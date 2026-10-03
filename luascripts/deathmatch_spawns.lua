-- deathmatch_spawns.lua
-- Spawn rules for configs/deathmatch.config, for the Legacy mod
-- (ET: Legacy), Lua 5.4.
--
-- Bots spawn around a random alive human. Where exactly:
--   - if the map has a squares file (deathmatch/<mapname>.txt, made with
--     deathmatch_squares.lua): inside one of its squares;
--   - otherwise: at a random spot in a ring around that human.
-- With CROWD_HUMANS or more humans playing, bots spawn like humans do
-- instead. While only one human is playing, bots that stray are dragged
-- back.
--
-- The regular map uses every square in the file, a map variant
-- (g_mapVariant) only the squares tagged with its name.
--
-- Humans respawn at a random spot in one of the map's squares (at their
-- normal spawn if the map has no squares file), with a respawn sound.
--
-- Everyone spawns with a SPAWN_SHIELD ms spawn shield and without hand
-- grenades.
-- A human playing alone also gets an ammo top-up on every spawn.
--
-- How many bots there are is up to deathmatch_bots.lua.

local modname = "deathmatch spawns"
local version = "3.0"

-- tuning ------------------------------------------------------------------
local MIN_DIST = 600    -- units; a standing player is 72 units tall
local MAX_DIST = 1800
local LEASH_DIST = 2400 -- wander past this and you get moved back
local LEASH_STEP = 50   -- ms between leash checks; one bot per check
local LEASH_REFRESH = 1000 -- ms between looking up who the leash applies to
local SPAWN_SHIELD = 1000 -- ms of invulnerability after spawning
local MAX_TRIES = 12    -- random spots tried before giving up
local CROWD_HUMANS = 5  -- from this many humans on, bots no longer spawn around one
local HEIGHT_TOLERANCE = 50 -- square spots: floor within this of the square's z
                            -- (keep equal to deathmatch_squares.lua)
-- Played where a human respawns. From the legacy mod pk3, so every client
-- has it without downloading anything.
local RESPAWN_SOUND = "sound/player/land_hurt.wav"

-- constants ---------------------------------------------------------------
local SVF_BOT = 8       -- bg_public.h
local CON_CONNECTED = 2
local GS_INTERMISSION = 3
local TEAM_AXIS = 1
local TEAM_ALLIES = 2
local JOIN_LIMBO_AFTER = 600 -- ms into a level from which the mod sends team joiners to
                             -- limbo (g_client.c: FRAMETIME * GAME_INIT_FRAMES)
local ENTITYNUM_NONE = 1023
local PW_INVULNERABLE = et.PW_INVULNERABLE or 1
local WP_GRENADE_LAUNCHER = et.WP_GRENADE_LAUNCHER or 4   -- axis hand grenade
local WP_GRENADE_PINEAPPLE = et.WP_GRENADE_PINEAPPLE or 9 -- allied hand grenade

local PLAYER_MINS = { -18, -18, -24 }
local PLAYER_MAXS = { 18, 18, 48 }

-- state -------------------------------------------------------------------
local maxclients = 64
local respawn_sound = nil -- sound index of RESPAWN_SOUND
local squares = {}      -- the spawn squares used on this level: { x1, y1, x2, y2, z }, x1 <= x2, y1 <= y2
local next_leash_check = 0
local next_leash_refresh = 0
local leash_bots = {}   -- client numbers of the bots, as of the last refresh
local leash_cursor = 0  -- index in leash_bots of the bot checked last
local lone_human = nil  -- client number of the only human on a team, or nil
local level_start = 0   -- level time at et_InitGame
local level_time = 0    -- level time of the last frame

-- helpers -----------------------------------------------------------------

local function is_bot(clientNum)
	local svFlags = et.gentity_get(clientNum, "r.svFlags")
	return svFlags ~= nil and (svFlags & SVF_BOT) == SVF_BOT
end

local function is_alive(clientNum)
	local health = et.gentity_get(clientNum, "health")
	return health ~= nil and health > 0
end

local function distance(a, b)
	local dx, dy, dz = a[1] - b[1], a[2] - b[2], a[3] - b[3]
	return math.sqrt(dx * dx + dy * dy + dz * dz)
end

-- Client numbers of the humans on a team, of the alive ones among them,
-- and of the connected bots.
local function list_clients()
	local humans, alive, bots = {}, {}, {}

	for i = 0, maxclients - 1 do
		if et.gentity_get(i, "pers.connected") == CON_CONNECTED then
			if is_bot(i) then
				bots[#bots + 1] = i
			else
				local team = et.gentity_get(i, "sess.sessionTeam")

				if team == TEAM_AXIS or team == TEAM_ALLIES then
					humans[#humans + 1] = i
					if is_alive(i) then alive[#alive + 1] = i end
				end
			end
		end
	end

	return humans, alive, bots
end

-- Drop a candidate position to the floor and confirm a player fits there.
-- One box trace does both: it stops at the floor, and a start/all-solid
-- result means the spot is inside geometry.
local function settle_on_ground(pos)
	local from = { pos[1], pos[2], pos[3] + 64 }
	local to = { pos[1], pos[2], pos[3] - 512 }

	local tr = et.trap_Trace(from, PLAYER_MINS, PLAYER_MAXS, to, ENTITYNUM_NONE, et.MASK_PLAYERSOLID)

	if type(tr) ~= "table" then return nil end
	if tr.startsolid == 1 or tr.startsolid == true then return nil end
	if tr.allsolid == 1 or tr.allsolid == true then return nil end
	if tr.fraction == nil or tr.fraction >= 1.0 then return nil end -- no floor below

	return tr.endpos
end

local function random_spot_around(origin)
	local angle = math.random() * 2 * math.pi
	local dist = MIN_DIST + math.random() * (MAX_DIST - MIN_DIST)

	return {
		origin[1] + math.cos(angle) * dist,
		origin[2] + math.sin(angle) * dist,
		origin[3],
	}
end

local function yaw_towards(from, to)
	return math.deg(math.atan(to[2] - from[2], to[1] - from[1]))
end

-- yaw is optional: without it the view direction is left alone.
local function teleport(clientNum, pos, yaw)
	et.gentity_set(clientNum, "ps.origin", pos)
	et.gentity_set(clientNum, "r.currentOrigin", pos)
	et.gentity_set(clientNum, "ps.velocity", { 0, 0, 0 })

	if yaw ~= nil then
		et.gentity_set(clientNum, "ps.viewangles", { 0, yaw, 0 })
	end

	et.trap_LinkEntity(clientNum)
end

-- spawn squares -----------------------------------------------------------
-- File format (see deathmatch_squares.lua): one square per line,
-- "x1 y1 x2 y2 z [variant ...]", '#' starts a comment. x1 y1 and x2 y2 are
-- two opposite corners, the sides run along the map's axes; z is a standing
-- player's origin. The words after z are the map variants that use the
-- square.

-- "x1 y1 x2 y2 z [variant ...]" -> square and its tags (lower case), or nil
-- if the text is malformed.
local function parse_square(text)
	local words = {}
	for word in text:gmatch("%S+") do
		words[#words + 1] = word
	end
	if #words < 5 then return nil end

	local xa, ya, xb, yb, z = tonumber(words[1]), tonumber(words[2]), tonumber(words[3]),
		tonumber(words[4]), tonumber(words[5])
	if xa == nil or ya == nil or xb == nil or yb == nil or z == nil then return nil end
	if xa == xb or ya == yb then return nil end

	local tags = {}
	for i = 6, #words do
		tags[string.lower(words[i])] = true
	end

	return {
		x1 = math.min(xa, xb), y1 = math.min(ya, yb),
		x2 = math.max(xa, xb), y2 = math.max(ya, yb),
		z = z,
	}, tags
end

-- Read the squares this level uses: all of the map's on the regular map,
-- the ones tagged with the variant on a map variant. The list stays empty
-- if there is no file.
local function load_squares()
	squares = {}
	local path = "deathmatch/" .. string.lower(et.trap_Cvar_Get("mapname")) .. ".txt"
	local variant = string.lower(et.trap_Cvar_Get("g_mapVariant") or "")

	local fd, len = et.trap_FS_FOpenFile(path, et.FS_READ)
	if len == nil or len < 0 then
		et.G_Print("deathmatch: no " .. path .. ", bots use the random ring\n")
		return
	end

	local data = (len > 0 and et.trap_FS_Read(fd, len)) or ""
	et.trap_FS_FCloseFile(fd)

	for raw in (data .. "\n"):gmatch("([^\n]*)\n") do
		local text = raw:gsub("#.*", "") -- drop the comment

		if text:match("%S") then -- skip blank lines
			local square, tags = parse_square(text)

			if square ~= nil then
				if variant == "" or tags[variant] then
					squares[#squares + 1] = square
				end
			else
				et.G_Print("deathmatch: " .. path .. " ignored line: " .. raw .. "\n")
			end
		end
	end

	et.G_Print("deathmatch: " .. #squares .. " spawn squares from " .. path ..
		(variant ~= "" and " for variant " .. variant or "") .. "\n")
end

-- One attempt at a random floor spot inside a square. Only x and y are
-- random; the floor must be within HEIGHT_TOLERANCE of the square's z.
-- nil if the attempt hit a wall, a drop, or someone standing there.
local function random_spot_in_square(square, ignoreEnt)
	local x = square.x1 + math.random() * (square.x2 - square.x1)
	local y = square.y1 + math.random() * (square.y2 - square.y1)
	local z = square.z

	local from = { x, y, z + HEIGHT_TOLERANCE }
	local to = { x, y, z - HEIGHT_TOLERANCE }
	local tr = et.trap_Trace(from, PLAYER_MINS, PLAYER_MAXS, to, ignoreEnt, et.MASK_PLAYERSOLID)

	if type(tr) ~= "table" then return nil end
	if tr.startsolid == 1 or tr.startsolid == true then return nil end
	if tr.allsolid == 1 or tr.allsolid == true then return nil end
	if tr.fraction == nil or tr.fraction >= 1.0 then return nil end -- no floor in range

	return tr.endpos
end

-- Distances from a position to the nearest and to the farthest point of a
-- square.
local function square_range(pos, square)
	local nx = math.max(square.x1, math.min(pos[1], square.x2))
	local ny = math.max(square.y1, math.min(pos[2], square.y2))
	local fx = (pos[1] - square.x1 > square.x2 - pos[1]) and square.x1 or square.x2
	local fy = (pos[2] - square.y1 > square.y2 - pos[2]) and square.y1 or square.y2

	return distance(pos, { nx, ny, square.z }), distance(pos, { fx, fy, square.z })
end

-- Squares that reach into the ring around target: some part of them is no
-- further than MAX_DIST and some part no closer than MIN_DIST.
local function squares_in_ring(target)
	local found = {}

	for _, square in ipairs(squares) do
		local near, far = square_range(target, square)
		if near <= MAX_DIST and far >= MIN_DIST then
			found[#found + 1] = square
		end
	end

	return found
end

-- Closest square with some part at least MIN_DIST from target, or nil.
local function nearest_square_outside_min(target)
	local best, best_dist = nil, math.huge

	for _, square in ipairs(squares) do
		local near, far = square_range(target, square)
		if far >= MIN_DIST and near < best_dist then
			best, best_dist = square, near
		end
	end

	return best
end

-- Random square from the list, bigger ones more often (weighted by area),
-- so spawns spread evenly over the ground the squares cover.
local function pick_by_area(list)
	local total = 0
	for _, square in ipairs(list) do
		total = total + (square.x2 - square.x1) * (square.y2 - square.y1)
	end

	local roll = math.random() * total
	for _, square in ipairs(list) do
		roll = roll - (square.x2 - square.x1) * (square.y2 - square.y1)
		if roll <= 0 then return square end
	end

	return list[#list] -- only reached through float rounding
end

-- choosing spots ----------------------------------------------------------

-- Random spot in the ring, dropped to the floor.
local function ring_spot(target)
	for _ = 1, MAX_TRIES do
		local pos = settle_on_ground(random_spot_around(target))
		if pos ~= nil then return pos end
	end

	return nil
end

-- Random spot in a square that reaches into the ring. If there is none, use
-- the closest square beyond it. A spot inside the ring is preferred; failing
-- that, one further out. Spots closer than MIN_DIST to the target are never
-- used, same as with the ring.
local function square_spot(clientNum, target)
	local candidates = squares_in_ring(target)

	if #candidates == 0 then
		local fallback = nearest_square_outside_min(target)
		if fallback == nil then return nil end
		candidates = { fallback }
	end

	local too_far = nil

	for _ = 1, MAX_TRIES do
		local spot = random_spot_in_square(pick_by_area(candidates), clientNum)
		local d = spot ~= nil and distance(spot, target) or 0

		if d >= MIN_DIST then
			if d <= MAX_DIST then return spot end
			too_far = too_far or spot
		end
	end

	return too_far
end

-- Where to put a bot for this target, or nil if nothing valid was found.
local function choose_spot(clientNum, target)
	if #squares > 0 then
		return square_spot(clientNum, target)
	end

	return ring_spot(target)
end

-- A random spot in any of the map's squares, wherever the players are, or
-- nil if the map has none or nothing valid was found.
local function map_spot(clientNum)
	if #squares == 0 then return nil end

	for _ = 1, MAX_TRIES do
		local spot = random_spot_in_square(pick_by_area(squares), clientNum)
		if spot ~= nil then return spot end
	end

	return nil
end

-- leash -------------------------------------------------------------------
-- Only while a single human is playing: a bot further than LEASH_DIST from
-- that human gets moved back.

-- Look up who the leash applies to: the bots, and the human if there is
-- exactly one on a team. Nobody at intermission.
local function refresh_leash()
	leash_bots, lone_human = {}, nil

	if tonumber(et.trap_Cvar_Get("gamestate")) == GS_INTERMISSION then return end

	local humans, _, bots = list_clients()
	if #humans ~= 1 then return end

	leash_bots, lone_human = bots, humans[1]
end

-- One bot is looked at per call, so the checks and teleports are spread
-- over frames instead of landing in one.
local function leash_next_bot()
	if lone_human == nil or #leash_bots == 0 then return end

	leash_cursor = leash_cursor % #leash_bots + 1
	local bot = leash_bots[leash_cursor]

	-- both are as of the last refresh, so check they still hold
	if et.gentity_get(bot, "pers.connected") ~= CON_CONNECTED
		or not is_bot(bot) or not is_alive(bot) then return end
	if et.gentity_get(lone_human, "pers.connected") ~= CON_CONNECTED
		or not is_alive(lone_human) then return end

	local target = et.gentity_get(lone_human, "ps.origin")
	local pos = et.gentity_get(bot, "ps.origin")
	if target == nil or pos == nil or distance(pos, target) <= LEASH_DIST then return end

	local spot = choose_spot(bot, target)

	-- Only move it somewhere inside the leash. A fallback square can be
	-- further away than that, and the bot would otherwise be teleported
	-- again on every check.
	if spot ~= nil and distance(spot, target) <= LEASH_DIST then
		teleport(bot, spot, yaw_towards(spot, target))
	end
end

-- callbacks ---------------------------------------------------------------

function et_InitGame(levelTime, randomSeed, restart)
	et.RegisterModname(modname .. " " .. version)
	math.randomseed(randomSeed)
	maxclients = tonumber(et.trap_Cvar_Get("sv_maxclients")) or 64
	respawn_sound = et.G_SoundIndex(RESPAWN_SOUND)
	next_leash_check = 0
	next_leash_refresh = 0
	leash_bots = {}
	leash_cursor = 0
	lone_human = nil
	level_start = levelTime
	level_time = levelTime
	load_squares()
end

function et_ClientSpawn(clientNum, revived, teamChange, restoreHealth)
    -- turn of spawnshield
    et.gentity_set(clientNum, "ps.powerups", PW_INVULNERABLE, 0)

	-- No hand grenades for anyone, bots included: there is no cvar for
	-- them, so take them away on every spawn.
	et.RemoveWeaponFromPlayer(clientNum, WP_GRENADE_LAUNCHER)
	et.RemoveWeaponFromPlayer(clientNum, WP_GRENADE_PINEAPPLE)

	if revived == 1 then return end

	local humans, alive = list_clients()

	if not is_bot(clientNum) then
		-- Joining a team or the spectators runs through here too, but it is
		-- not a respawn: a spectator isn't in the game, and someone joining
		-- a team mid-level goes to limbo and spawns for real afterwards.
		local team = et.gentity_get(clientNum, "sess.sessionTeam")

		if team ~= TEAM_AXIS and team ~= TEAM_ALLIES then return end
		if teamChange == 1 and level_time - level_start > JOIN_LIMBO_AFTER then return end

		-- Only while a single human is playing: one big ammo top-up per
		-- spawn instead of refilling on every shot.
		local weapon = (#humans == 1) and et.GetCurrentWeapon(clientNum) or nil

		if weapon ~= nil then
			et.AddWeaponToPlayer(clientNum, weapon, 999, 999, 0)
		end

		local spot = map_spot(clientNum)
		if spot ~= nil then teleport(clientNum, spot) end

		et.G_Sound(clientNum, respawn_sound) -- after the move, so it plays there

		return
	end

	if #humans >= CROWD_HUMANS then
		-- too many players to spawn around one of them
		local spot = map_spot(clientNum)
		if spot ~= nil then teleport(clientNum, spot) end
		return
	end

	if #alive == 0 then return end

	local target = et.gentity_get(alive[math.random(#alive)], "ps.origin")
	if target == nil then return end

	local spot = choose_spot(clientNum, target)
	if spot ~= nil then
		teleport(clientNum, spot, yaw_towards(spot, target))
	end
end

-- Leashes bots.
function et_RunFrame(levelTime)
	level_time = levelTime

	if levelTime >= next_leash_refresh then
		next_leash_refresh = levelTime + LEASH_REFRESH
		refresh_leash()
	end

	if levelTime >= next_leash_check then
		next_leash_check = levelTime + LEASH_STEP
		leash_next_bot()
	end
end
