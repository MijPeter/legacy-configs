-- deathmatch_bots.lua
-- Bot population and map rotation for configs/deathmatch.config, for the
-- Legacy mod (ET: Legacy), Lua 5.4.
--
-- Keeps the number of Omni-bot bots on what MAP_RULES asks for, writes the
-- map vote's player limits from the same table, and ends intermission as
-- soon as everyone has voted.
--
-- Players can vote the bots off with /callvote bots 0 (g_bots, needs the
-- server's qagame). They stay off while anyone is playing; once nobody is
-- on a team any more, they are turned back on.
--
-- Where bots and humans spawn is up to deathmatch_spawns.lua.

local modname = "deathmatch bots"
local version = "3.0"

-- per-map rules -----------------------------------------------------------
-- Keyed by map name, in lower case. A map variant is its own entry, under
-- the variant's name.
--   players = { min, max }  humans connected (spectators count too) for the
--                           map to be offered in the map vote; -1 = no limit.
--                           Maps without it are always offered.
--   bots = { [n] = count }  bots to keep while n humans are on a team. A
--                           number of humans that isn't listed uses the
--                           nearest lower entry; none lower means no bots.
--                           Maps without it use DEFAULT_BOTS.
local DEFAULT_BOTS = { [0] = 5, [1] = 5, [2] = 10, [3] = 10, [4] = 10, [5] = 8, [6] = 8, [7] = 6 }

-- Bots for small maps: max(0, 5 - humans).
local SMALL_BOTS = { [0] = 5, [1] = 4, [2] = 3, [3] = 2, [4] = 1, [5] = 0 }

-- Bots for the stage variants: max(0, 8 - 2 * humans).
local STAGE_BOTS = { [0] = 8, [1] = 6, [2] = 4, [3] = 2, [4] = 0 }

-- Below 10 players only the small maps and the stage variants are offered.
local FULL_MAP = { 10, -1 }

local MAP_RULES = {
	-- small maps and stage variants: always offered
	mp_sillyctf = { bots = SMALL_BOTS },
	te_valhalla = { bots = SMALL_BOTS },
	etl_adlernest_first_stage = { bots = STAGE_BOTS },
	etl_adlernest_second_stage = { bots = STAGE_BOTS },
	operation_first_stage = { bots = STAGE_BOTS },
	supply_last_stage = { bots = STAGE_BOTS },
	missile_first_stage = { bots = STAGE_BOTS },

	-- full maps: from 10 players (all but etl_adlernest and et_operation_b8 are
	-- also kept out of the vote by g_excludedMaps in deathmatch.config)
	etl_adlernest = { players = FULL_MAP },
	bremen_b3 = { players = FULL_MAP },
	et_operation_b8 = { players = FULL_MAP },
	missile_b3 = { players = FULL_MAP },
	radar = { players = FULL_MAP },
	supply = { players = FULL_MAP },
	sw_goldrush_te = { players = FULL_MAP },
}

-- tuning ------------------------------------------------------------------
local BOT_CHECK_INTERVAL = 1000 -- ms between bot count checks; one bot added per check
local BOT_ADD_TRIES = 10 -- adds in a row that change nothing before pausing
local BOT_ADD_PAUSE = 30000 -- ms to wait after that (Omni-bot off, or server full)
local BOT_TEAM = 1      -- "bot addbot" arguments: 1 = axis, so join allies
local BOT_CLASS = 1     -- 1 = soldier, the only class the config allows
local BOTS_DONT_SHOOT = true -- harmless targets that never shoot back
local DONT_SHOOT_REPEAT = 2000 -- ms to keep resending "bot dontshoot" after a bot joins

-- constants ---------------------------------------------------------------
local SVF_BOT = 8       -- bg_public.h
local CON_DISCONNECTED = 0
local CON_CONNECTED = 2
local GS_INTERMISSION = 3
local VOTE_LIMITS_PATH = "mapvoteplayerscount.cfg" -- read by the mod at map load
local VOTE_LIMITS_MAX_SIZE = 2046 -- the mod refuses the file beyond this
local TEAM_AXIS = 1
local TEAM_ALLIES = 2
local EF_VOTED = 0x4000 -- bg_public.h: has cast a map vote

-- state -------------------------------------------------------------------
local maxclients = 64
local map_bots = DEFAULT_BOTS -- this map's bots table: [humans] = count
local next_bot_check = 0
local failed_adds = 0   -- adds in a row after which the bot count didn't grow
local last_bot_count = 0
local dont_shoot_until = 0 -- resend "bot dontshoot" on each bot check up to this time
local intermission_ended = false -- "ref allready" already sent this intermission

-- helpers -----------------------------------------------------------------

local function is_bot(clientNum)
	local svFlags = et.gentity_get(clientNum, "r.svFlags")
	return svFlags ~= nil and (svFlags & SVF_BOT) == SVF_BOT
end

-- bot count ---------------------------------------------------------------

-- Bots wanted for this many active humans: the entry for the nearest
-- listed number at or below it.
local function wanted_bots(humans)
	local best_n, best = -1, 0

	for n, count in pairs(map_bots) do
		if n <= humans and n > best_n then
			best_n, best = n, count
		end
	end

	return best
end

-- Humans on a team, and the client numbers of all bots (connecting ones
-- included, so a bot that is still joining isn't added twice).
local function count_clients()
	local humans, bots = 0, {}

	for i = 0, maxclients - 1 do
		local connected = et.gentity_get(i, "pers.connected")

		if connected ~= nil and connected ~= CON_DISCONNECTED then
			if is_bot(i) then
				bots[#bots + 1] = i
			elseif connected == CON_CONNECTED then
				local team = et.gentity_get(i, "sess.sessionTeam")

				if team == TEAM_AXIS or team == TEAM_ALLIES then
					humans = humans + 1
				end
			end
		end
	end

	return humans, bots
end

-- Move the bot count towards what MAP_RULES asks for. Surplus bots are
-- dropped at once; missing ones are added one per check.
local function balance_bots(levelTime)
	local humans, bots = count_clients()
	local wanted = wanted_bots(humans)

	-- voted off: no bots while anyone plays, back on once nobody does
	if et.trap_Cvar_Get("g_bots") == "0" then
		if humans > 0 then
			wanted = 0
		else
			et.trap_Cvar_Set("g_bots", "1")
			et.trap_SendServerCommand(-1, 'cpm "^3Nobody is playing: bots are back on"')
		end
	end

	for i = #bots, wanted + 1, -1 do
		et.trap_DropClient(bots[i], "removed, fewer bots needed", 0)
	end

	local grew = #bots > last_bot_count
	last_bot_count = #bots

	-- "bot dontshoot" only flags the bots Omni-bot has at that moment, so it
	-- has to be sent again for every bot that joins. Repeated for a while,
	-- as a bot counted here may not be known to Omni-bot yet.
	if BOTS_DONT_SHOOT then
		if grew then dont_shoot_until = levelTime + DONT_SHOOT_REPEAT end

		if levelTime <= dont_shoot_until then
			et.trap_SendConsoleCommand(et.EXEC_APPEND, "bot dontshoot 1\n")
		end
	end

	if grew or #bots >= wanted then failed_adds = 0 end
	if #bots >= wanted then return end

	if failed_adds >= BOT_ADD_TRIES then
		et.G_Print("deathmatch: 'bot addbot' isn't adding bots (" .. #bots .. " of " ..
			wanted .. "), is Omni-bot running and is there a free slot?\n")
		failed_adds = 0
		next_bot_check = levelTime + BOT_ADD_PAUSE
		return
	end

	failed_adds = failed_adds + 1
	et.trap_SendConsoleCommand(et.EXEC_APPEND,
		string.format("bot addbot %d %d\n", BOT_TEAM, BOT_CLASS))
end

-- intermission ------------------------------------------------------------
-- With map voting the mod ignores ready-ups at intermission and waits out
-- g_intermissionTime. Voting for a map counts as being ready here: once
-- every human on a team has voted, move on to the next map.
local function end_intermission_if_ready()
	if intermission_ended then return end

	local humans = 0

	for i = 0, maxclients - 1 do
		if et.gentity_get(i, "pers.connected") == CON_CONNECTED and not is_bot(i) then
			local team = et.gentity_get(i, "sess.sessionTeam")

			if team == TEAM_AXIS or team == TEAM_ALLIES then
				local eFlags = et.gentity_get(i, "ps.eFlags") or 0

				if (eFlags & EF_VOTED) == 0 then return end
				humans = humans + 1
			end
		end
	end

	if humans == 0 then return end

	intermission_ended = true
	et.trap_SendConsoleCommand(et.EXEC_APPEND, "ref allready\n")
end

-- map vote limits ---------------------------------------------------------
-- The mod filters the map vote by player count itself, from
-- mapvoteplayerscount.cfg: one '"map" min max' per line. Write that file
-- from MAP_RULES so the rules stay in one place. The mod reads it at map
-- load, before this script runs, so a change applies from the next map.
local function write_vote_limits()
	local lines = {}

	for map, rules in pairs(MAP_RULES) do
		if rules.players ~= nil then
			lines[#lines + 1] = string.format('"%s" %d %d', map, rules.players[1], rules.players[2])
		end
	end

	table.sort(lines)
	table.insert(lines, 1, "// written by deathmatch_bots.lua from MAP_RULES, edit it there")
	local data = table.concat(lines, "\n") .. "\n"

	if #data > VOTE_LIMITS_MAX_SIZE then
		et.G_Print("deathmatch: WARNING " .. VOTE_LIMITS_PATH .. " would be " .. #data ..
			" bytes, the mod reads at most " .. VOTE_LIMITS_MAX_SIZE .. " - not written\n")
		return
	end

	local fd, len = et.trap_FS_FOpenFile(VOTE_LIMITS_PATH, et.FS_READ)
	if len ~= nil and len >= 0 then
		local current = (len > 0 and et.trap_FS_Read(fd, len)) or ""
		et.trap_FS_FCloseFile(fd)
		if current == data then return end
	end

	fd = et.trap_FS_FOpenFile(VOTE_LIMITS_PATH, et.FS_WRITE)
	if fd == nil or fd == 0 then
		et.G_Print("deathmatch: WARNING can't write " .. VOTE_LIMITS_PATH .. "\n")
		return
	end

	et.trap_FS_Write(data, #data, fd)
	et.trap_FS_FCloseFile(fd)
	et.G_Print("deathmatch: " .. VOTE_LIMITS_PATH .. " updated, applies from the next map\n")
end

-- This level's map key: the map variant being played, or else the map.
local function map_key()
	local variant = et.trap_Cvar_Get("g_mapVariant")
	if variant ~= nil and variant ~= "" then return string.lower(variant) end

	return string.lower(et.trap_Cvar_Get("mapname"))
end

-- callbacks ---------------------------------------------------------------

function et_InitGame(levelTime, randomSeed, restart)
	et.RegisterModname(modname .. " " .. version)
	maxclients = tonumber(et.trap_Cvar_Get("sv_maxclients")) or 64
	next_bot_check = 0
	failed_adds = 0
	last_bot_count = 0
	dont_shoot_until = 0
	intermission_ended = false

	local rules = MAP_RULES[map_key()]
	map_bots = (rules ~= nil and rules.bots) or DEFAULT_BOTS
	write_vote_limits()
end

-- Keeps the bot count on target, and ends intermission once everyone has
-- voted.
-- Tell each player how to vote the bots off (or back on): on joining, and
-- again on every map start, as each map begins every client anew. Only
-- when the server's qagame has the vote and it is allowed.
function et_ClientBegin(clientNum)
	if is_bot(clientNum) then return end
	if et.trap_Cvar_Get("vote_allow_bots") ~= "1" then return end

	local msg
	if et.trap_Cvar_Get("g_bots") == "0" then
		msg = "^3Bots are off. ^7/callvote bots 1 ^3turns them back on"
	else
		msg = "^3Too many bots? ^7/callvote bots 0 ^3turns them off while people play"
	end

	et.trap_SendServerCommand(clientNum, 'cpm "' .. msg .. '\n"')
end

function et_RunFrame(levelTime)
	if levelTime < next_bot_check then return end
	next_bot_check = levelTime + BOT_CHECK_INTERVAL

	if tonumber(et.trap_Cvar_Get("gamestate")) == GS_INTERMISSION then
		end_intermission_if_ready()
	else
		balance_bots(levelTime)
	end
end
