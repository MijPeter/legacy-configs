-- deathmatch_squares.lua
-- Development tool: author the spawn squares that deathmatch_spawns.lua will
-- use. Remove it from lua_modules once every map is done.
--
-- Squares file: <fs_homepath>/legacy/deathmatch/<mapname>.txt, one per map,
-- shared by the map and its variants.
-- One square per line: "x1 y1 x2 y2 z [variant ...]", optionally followed by
-- "# comment". x1 y1 and x2 y2 are two opposite corners; the sides run along
-- the map's axes. z is a standing player's origin, which is what /ppos
-- prints.
--
-- Variants: the regular map uses every square; a map variant (g_mapVariant)
-- uses only the squares tagged with its name. A square with no tags is for
-- the regular map only.
--
-- The squares near you are outlined, each as a box from the floor to head
-- height: green for the one you stand in, red for the others, yellow for
-- the one you are drawing. While playing a variant, squares it doesn't use
-- are blue.
--
--   /phelp                       list these commands
--   /ppos                        your current position
--   /pcorner [variant] [label]   stand in one corner and use it, walk to the
--                                opposite corner and use it again: adds the
--                                square, tagged with the variant if one is given
--   /pcancel                     forget the first corner
--   /pinfo                       the square you stand in, or the nearest one
--   /ptest                       teleport to a random spot in that square
--   /ptag <variant> [...]        tag the square you stand in with variants
--   /puntag <variant> [...]      remove those tags from it
--   /pdel                        remove the square you stand in
--   /pshow                       turn the outlines on or off, for you (off at first)
--   /preload                     re-read the file after editing it by hand
--
-- Barriers: invisible walls for a map variant's mapscript (func_fakebrush).
-- They aren't saved anywhere: each one is printed as a "create" block, to
-- your console and to the server's, to paste into the mapscript's
-- game_manager spawn. Copy it from the server console or etconsole.log: a
-- client's console can't show double quotes, so it shows ' instead. Barriers already in this level's mapscript are
-- outlined in magenta, the ones made this level in cyan.
--
--   /bcorner [height] [solid]    like /pcorner: stand in one corner, then in the
--                                opposite one. The barrier spans exactly between
--                                the two spots you stood on (at least
--                                BARRIER_MIN_THICKNESS thick), from the floor up to
--                                height (default 256) above the higher corner.
--                                Blocks players only, or shots too with "solid"
--   /bcancel                     forget the first corner
--   /btest                       turn this level's barriers on or off in game
--   /bundo                       drop the last barrier made this level
--   /blist                       print the barriers made this level again

local modname = "deathmatch squares"
local version = "dev"

-- tuning ------------------------------------------------------------------
local HEIGHT_TOLERANCE = 50 -- a spot's floor must be within this of its square's z
                            -- (keep equal to deathmatch_spawns.lua)
local MIN_SIDE = 32
local MAX_TRIES = 12        -- /ptest attempts before giving up
local CHECK_SAMPLES = 20    -- attempts used to rate a square after adding it
local DRAW_INTERVAL = 600   -- ms between redraws; an outline lasts cg_railTrailTime
                            -- on the client, 750 by default
local DRAW_DIST = 3000      -- squares further away than this are not outlined
local MAX_DRAWN = 8         -- outlines per player, nearest first

-- constants ---------------------------------------------------------------
local PLAYER_MINS = { -18, -18, -24 }
local PLAYER_MAXS = { 18, 18, 48 }
local SVF_BOT = 8             -- bg_public.h
local SVF_BROADCAST = 0x20    -- sent whether or not it is in view
local SVF_SINGLECLIENT = 0x800
local CON_CONNECTED = 2
local EV_RAILTRAIL = 60       -- bg_public.h, entity_event_t
local RAIL_BOX = 1            -- s.dmgFlags: outline the box between two corners
local COLOR_INSIDE = { 0, 255, 0 }
local COLOR_OTHER = { 255, 0, 0 }
local COLOR_PENDING = { 255, 255, 0 }
local COLOR_UNUSED = { 0, 128, 255 } -- not used by the variant being played
local COLOR_SCRIPT_BARRIER = { 255, 0, 255 } -- in this level's mapscript
local COLOR_NEW_BARRIER = { 0, 255, 255 }    -- made this level with /bcorner

local BARRIER_HEIGHT = 256 -- default height above the higher corner
local BARRIER_MIN_THICKNESS = 8 -- a side shorter than this is widened to it, around its middle
local MAX_BARRIERS_DRAWN = 8
local CONTENTS_SOLID = 1
local CONTENTS_PLAYERCLIP = 65536

-- state -------------------------------------------------------------------
local squares = {}      -- { x1, y1, x2, y2, z, tags, comment, line }, x1 <= x2 and y1 <= y2
local file_lines = {}   -- the file exactly as read, one entry per line
local squares_path = "" -- relative to <fs_homepath>/legacy/
local maxclients = 64
local next_draw = 0
local pending = {}      -- [clientNum] = position of the first corner
local shown = {}        -- [clientNum] = true once /pshow turned the outlines on
local variant = ""      -- map variant being played, lower case; "" for the regular map
local script_barriers = {} -- func_fakebrush boxes in this level's mapscript: { mins, maxs }
local new_barriers = {}    -- made this level: { mins, maxs, contents, ent }; ent while /btest has it on
local barriers_on = false  -- /btest state
local pending_barrier = {} -- [clientNum] = position of the first barrier corner

-- helpers -----------------------------------------------------------------

local function tell(clientNum, msg)
	msg = msg:gsub('"', "'") -- a double quote would end the print command early
	et.trap_SendServerCommand(clientNum, 'print "' .. msg .. '\n"')
end

local function is_bot(clientNum)
	local svFlags = et.gentity_get(clientNum, "r.svFlags")
	return svFlags ~= nil and (svFlags & SVF_BOT) == SVF_BOT
end

local function is_alive(clientNum)
	local health = et.gentity_get(clientNum, "health")
	return health ~= nil and health > 0
end

local function get_pos(clientNum)
	return et.gentity_get(clientNum, "ps.origin")
end

local function fmt_pos(pos)
	return string.format("%.0f %.0f %.0f", pos[1], pos[2], pos[3])
end

-- trap_Trace flags may come back as 0/1 or as booleans.
local function is_set(value)
	return value == 1 or value == true
end

local function teleport(clientNum, pos)
	et.gentity_set(clientNum, "ps.origin", pos)
	et.gentity_set(clientNum, "r.currentOrigin", pos)
	et.gentity_set(clientNum, "ps.velocity", { 0, 0, 0 })
	et.trap_LinkEntity(clientNum)
end

-- file --------------------------------------------------------------------

local function full_path()
	return et.trap_Cvar_Get("fs_homepath") .. "/" .. et.trap_Cvar_Get("fs_game") .. "/" .. squares_path
end

-- Lines of a file without their newlines; empty if the file doesn't exist.
local function read_lines(path)
	local fd, len = et.trap_FS_FOpenFile(path, et.FS_READ)
	if len == nil or len < 0 then return {} end

	local data = (len > 0 and et.trap_FS_Read(fd, len)) or ""
	et.trap_FS_FCloseFile(fd)

	if data ~= "" and data:sub(-1) ~= "\n" then
		data = data .. "\n"
	end

	local lines = {}
	for line in data:gmatch("([^\n]*)\n") do
		lines[#lines + 1] = line
	end

	return lines
end

local function write_lines(path, lines)
	local fd = et.trap_FS_FOpenFile(path, et.FS_WRITE)
	if fd == nil or fd == 0 then return false end

	local data = #lines > 0 and (table.concat(lines, "\n") .. "\n") or ""
	et.trap_FS_Write(data, #data, fd)
	et.trap_FS_FCloseFile(fd)

	return true
end

-- squares -----------------------------------------------------------------

-- Square between two opposite corners, in either order.
local function make_square(xa, ya, xb, yb, z)
	return {
		x1 = math.min(xa, xb), y1 = math.min(ya, yb),
		x2 = math.max(xa, xb), y2 = math.max(ya, yb),
		z = z,
	}
end

-- "x1 y1 x2 y2 z [variant ...]" -> square, or nil if the text is malformed.
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

	local square = make_square(xa, ya, xb, yb, z)
	square.tags = {}
	for i = 6, #words do
		square.tags[#square.tags + 1] = string.lower(words[i])
	end

	return square
end

-- One line of the file: "x1 y1 x2 y2 z", then its tags, plus " # comment"
-- if given.
local function format_square(square, comment)
	local line = string.format("%.0f %.0f %.0f %.0f %.0f",
		square.x1, square.y1, square.x2, square.y2, square.z)

	if square.tags ~= nil and #square.tags > 0 then
		line = line .. " " .. table.concat(square.tags, " ")
	end

	if comment ~= nil and comment ~= "" then
		line = line .. " # " .. comment
	end

	return line
end

local function has_tag(square, name)
	for _, tag in ipairs(square.tags) do
		if tag == name then return true end
	end

	return false
end

-- Whether the level being played spawns in this square.
local function is_used(square)
	return variant == "" or has_tag(square, variant)
end

local function describe(square)
	local tags = #square.tags > 0 and table.concat(square.tags, ", ") or "none, regular map only"

	return string.format("line %d, %.0f x %.0f at height %.0f, variants: %s",
		square.line, square.x2 - square.x1, square.y2 - square.y1, square.z, tags)
end

-- Whether maps/<name>.variant exists and is a variant of this map.
local function is_variant_of_map(name)
	local fd, len = et.trap_FS_FOpenFile("maps/" .. name .. ".variant", et.FS_READ)
	if len == nil or len < 0 then return false end

	local data = (len > 0 and et.trap_FS_Read(fd, len)) or ""
	et.trap_FS_FCloseFile(fd)

	local base = data:match("%S+")
	return base ~= nil and string.lower(base) == string.lower(et.trap_Cvar_Get("mapname"))
end

-- Re-read this map's file from disk into file_lines and squares.
local function load_squares()
	squares_path = "deathmatch/" .. string.lower(et.trap_Cvar_Get("mapname")) .. ".txt"
	file_lines = read_lines(squares_path)
	squares = {}

	for line_no, raw in ipairs(file_lines) do
		local text, comment = raw:match("^([^#]*)#?%s*(.-)%s*$")

		if text:match("%S") then -- skip blank lines
			local square = parse_square(text)

			if square ~= nil then
				square.line = line_no
				square.comment = comment
				squares[#squares + 1] = square
			else
				et.G_Print("deathmatch: " .. squares_path .. " line " .. line_no ..
					" ignored, expected: x1 y1 x2 y2 z [variant ...]\n")
			end
		end
	end
end

-- Write file_lines to disk, then re-read it so squares match the file.
local function save_squares()
	local ok = write_lines(squares_path, file_lines)
	load_squares()
	return ok
end

-- Distance from a position to the nearest point of a square; 0 inside it.
local function distance_to_square(pos, square)
	local dx = pos[1] - math.max(square.x1, math.min(pos[1], square.x2))
	local dy = pos[2] - math.max(square.y1, math.min(pos[2], square.y2))
	local dz = pos[3] - square.z
	return math.sqrt(dx * dx + dy * dy + dz * dz)
end

-- Inside = within the sides and within HEIGHT_TOLERANCE of z.
local function is_inside(pos, square)
	return pos[1] >= square.x1 and pos[1] <= square.x2
		and pos[2] >= square.y1 and pos[2] <= square.y2
		and math.abs(pos[3] - square.z) <= HEIGHT_TOLERANCE
end

-- The square you stand in; if several overlap, the smallest one.
local function square_at(pos)
	local best, best_area = nil, math.huge

	for _, square in ipairs(squares) do
		local area = (square.x2 - square.x1) * (square.y2 - square.y1)
		if is_inside(pos, square) and area < best_area then
			best, best_area = square, area
		end
	end

	return best
end

local function nearest_square(pos)
	local best, best_dist = nil, math.huge

	for _, square in ipairs(squares) do
		local d = distance_to_square(pos, square)
		if d < best_dist then
			best, best_dist = square, d
		end
	end

	return best, best_dist
end

-- traces ------------------------------------------------------------------

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
	if is_set(tr.startsolid) or is_set(tr.allsolid) then return nil end
	if tr.fraction == nil or tr.fraction >= 1.0 then return nil end -- no floor in range

	return tr.endpos
end

-- How many of CHECK_SAMPLES attempts find a valid spot.
local function rate_square(square, ignoreEnt)
	local found = 0

	for _ = 1, CHECK_SAMPLES do
		if random_spot_in_square(square, ignoreEnt) ~= nil then
			found = found + 1
		end
	end

	return found
end

-- True if the player stands upright on something, not jumping or falling.
local function standing_on_ground(clientNum, pos)
	local below = { pos[1], pos[2], pos[3] - 2 }
	local tr = et.trap_Trace(pos, PLAYER_MINS, PLAYER_MAXS, below, clientNum, et.MASK_PLAYERSOLID)

	if type(tr) ~= "table" then return false end
	if is_set(tr.startsolid) then return false end -- no room to stand upright here

	return tr.fraction ~= nil and tr.fraction < 1.0
end

-- outlines ----------------------------------------------------------------
-- Drawn with the mod's debug line effect, for one player only. The client
-- lets each outline fade after cg_railTrailTime, so they are sent again
-- every DRAW_INTERVAL.

-- Outline of a box between two opposite corners.
local function draw_box(clientNum, mins, maxs, color)
	local ent = et.G_TempEntity(mins, EV_RAILTRAIL)

	et.gentity_set(ent, "s.origin2", maxs)
	et.gentity_set(ent, "s.dmgFlags", RAIL_BOX)
	et.gentity_set(ent, "s.angles", color)
	et.gentity_set(ent, "s.effect1Time", -1) -- no id: the client draws new lines every time
	et.gentity_set(ent, "r.singleClient", clientNum)
	et.gentity_set(ent, "r.svFlags", SVF_BROADCAST | SVF_SINGLECLIENT)
end

-- Outline of a square, from the floor to a standing player's head.
local function draw_square(clientNum, square, color)
	draw_box(clientNum, { square.x1, square.y1, square.z + PLAYER_MINS[3] },
		{ square.x2, square.y2, square.z + PLAYER_MAXS[3] }, color)
end

-- Distance from a position to the nearest point of a box; 0 inside it.
local function distance_to_box(pos, mins, maxs)
	local d = 0
	for i = 1, 3 do
		local out = pos[i] - math.max(mins[i], math.min(pos[i], maxs[i]))
		d = d + out * out
	end
	return math.sqrt(d)
end

local function draw_barriers_for(clientNum, pos)
	local near = {}
	local function add(list, color)
		for _, b in ipairs(list) do
			local d = distance_to_box(pos, b.mins, b.maxs)
			if d <= DRAW_DIST then
				near[#near + 1] = { barrier = b, dist = d, color = color }
			end
		end
	end

	add(script_barriers, COLOR_SCRIPT_BARRIER)
	add(new_barriers, COLOR_NEW_BARRIER)
	table.sort(near, function(a, b) return a.dist < b.dist end)

	for i = 1, math.min(#near, MAX_BARRIERS_DRAWN) do
		draw_box(clientNum, near[i].barrier.mins, near[i].barrier.maxs, near[i].color)
	end
end

local function draw_for(clientNum)
	local pos = get_pos(clientNum)
	if pos == nil then return end

	local near = {}
	for _, square in ipairs(squares) do
		local d = distance_to_square(pos, square)
		if d <= DRAW_DIST then
			near[#near + 1] = { square = square, dist = d }
		end
	end

	table.sort(near, function(a, b) return a.dist < b.dist end)

	local inside = square_at(pos)
	for i = 1, math.min(#near, MAX_DRAWN) do
		local square = near[i].square
		local color = COLOR_OTHER

		if square == inside then
			color = COLOR_INSIDE
		elseif not is_used(square) then
			color = COLOR_UNUSED
		end

		draw_square(clientNum, square, color)
	end

	-- the square being drawn: from the first corner to where you stand now
	local corner = pending[clientNum]
	if corner ~= nil and corner[1] ~= pos[1] and corner[2] ~= pos[2] then
		draw_square(clientNum, make_square(corner[1], corner[2], pos[1], pos[2], corner[3]),
			COLOR_PENDING)
	end

	draw_barriers_for(clientNum, pos)
end

local function draw_all()
	for i = 0, maxclients - 1 do
		if shown[i] and et.gentity_get(i, "pers.connected") == CON_CONNECTED
			and not is_bot(i) then
			draw_for(i)
		end
	end
end

-- barriers ----------------------------------------------------------------

-- "x y z" -> { x, y, z }, or nil.
local function parse_vector(text)
	if text == nil then return nil end
	local x, y, z = text:match("^%s*(%S+)%s+(%S+)%s+(%S+)%s*$")
	x, y, z = tonumber(x), tonumber(y), tonumber(z)
	if x == nil or y == nil or z == nil then return nil end
	return { x, y, z }
end

-- Text of this level's mapscript, found the way the mod finds it: the
-- variant's own script, else the map's; in g_mapScriptDirectory, else maps/.
local function read_mapscript()
	local dir = et.trap_Cvar_Get("g_mapScriptDirectory")
	local names = { string.lower(et.trap_Cvar_Get("mapname")) }
	if variant ~= "" then table.insert(names, 1, variant) end

	for _, name in ipairs(names) do
		local paths = { "maps/" .. name .. ".script" }
		if dir ~= nil and dir ~= "" then table.insert(paths, 1, dir .. "/" .. name .. ".script") end

		for _, path in ipairs(paths) do
			local fd, len = et.trap_FS_FOpenFile(path, et.FS_READ)
			if len ~= nil and len > 0 then
				local data = et.trap_FS_Read(fd, len) or ""
				et.trap_FS_FCloseFile(fd)
				return data, path
			elseif len ~= nil and len >= 0 then
				et.trap_FS_FCloseFile(fd)
			end
		end
	end

	return nil
end

-- The func_fakebrush boxes the mapscript creates, for the outlines.
local function load_script_barriers()
	script_barriers = {}

	local data = read_mapscript()
	if data == nil then return end

	data = data:gsub("//[^\n]*", "") -- drop comments

	for block in data:gmatch("create%s*{(.-)}") do
		local classname = block:match('classname%s+"?([%w_]+)"?')

		if classname ~= nil and string.lower(classname) == "func_fakebrush" then
			local origin = parse_vector(block:match('origin%s+"([^"]*)"'))
			local mins = parse_vector(block:match('mins%s+"([^"]*)"'))
			local maxs = parse_vector(block:match('maxs%s+"([^"]*)"'))

			if origin ~= nil and mins ~= nil and maxs ~= nil then
				script_barriers[#script_barriers + 1] = {
					mins = { origin[1] + mins[1], origin[2] + mins[2], origin[3] + mins[3] },
					maxs = { origin[1] + maxs[1], origin[2] + maxs[2], origin[3] + maxs[3] },
				}
			end
		end
	end
end

-- The mapscript block for a barrier, one line per entry. The origin is its
-- lowest corner, so mins is 0 0 0.
local function barrier_block(b)
	return {
		"create",
		"{",
		'\tclassname "func_fakebrush"',
		string.format('\torigin "%.0f %.0f %.0f"', b.mins[1], b.mins[2], b.mins[3]),
		'\tmins "0 0 0"',
		string.format('\tmaxs "%.0f %.0f %.0f"',
			b.maxs[1] - b.mins[1], b.maxs[2] - b.mins[2], b.maxs[3] - b.mins[3]),
		"\tcontents " .. b.contents,
		"}",
	}
end

local function print_barrier(clientNum, b)
	for _, line in ipairs(barrier_block(b)) do
		tell(clientNum, "^7" .. line:gsub("\t", "    "))
		et.G_Print(line .. "\n")
	end
end

local function set_barrier_live(b, on)
	if on and b.ent == nil then
		local block = barrier_block(b)
		b.ent = et.G_CreateEntity(table.concat(block, " ", 3, #block - 1))
	elseif not on and b.ent ~= nil then
		et.G_FreeEntity(b.ent)
		b.ent = nil
	end
end

-- Clients whose box overlaps a barrier's: turning it on would trap them.
local function players_inside(b)
	local inside = {}

	for i = 0, maxclients - 1 do
		if et.gentity_get(i, "pers.connected") == CON_CONNECTED and is_alive(i) then
			local pos = get_pos(i)
			local overlaps = true

			for k = 1, 3 do
				if pos[k] + PLAYER_MAXS[k] <= b.mins[k] or pos[k] + PLAYER_MINS[k] >= b.maxs[k] then
					overlaps = false
				end
			end

			if overlaps then inside[#inside + 1] = i end
		end
	end

	return inside
end

-- commands ----------------------------------------------------------------

local function cmd_help(clientNum)
	tell(clientNum, "^3deathmatch squares (dev tool)")
	tell(clientNum, "^7/ppos                       ^3your current position")
	tell(clientNum, "^7/pcorner [variant] [label]  ^3use it in one corner, then in the opposite one: adds the square")
	tell(clientNum, "^7/pcancel                    ^3forget the first corner")
	tell(clientNum, "^7/pinfo                      ^3the square you stand in, or the nearest one")
	tell(clientNum, "^7/ptest                      ^3teleport to a random spot in that square")
	tell(clientNum, "^7/ptag <variant> [...]       ^3tag the square you stand in with variants")
	tell(clientNum, "^7/puntag <variant> [...]     ^3remove those tags from it")
	tell(clientNum, "^7/pdel                       ^3remove the square you stand in")
	tell(clientNum, "^7/pshow                      ^3turn the outlines on or off, for you (off at first)")
	tell(clientNum, "^7/preload                    ^3re-read the file after editing it by hand")
	tell(clientNum, "^3the regular map uses every square, a variant only the squares tagged with its name")
	tell(clientNum, "^3outlines: ^2green^3 you are inside, ^1red^3 others, ^3yellow being drawn" ..
		"^3, ^4blue^3 not used by this variant")
	tell(clientNum, "^7/bcorner [height] [solid]   ^3barrier for the mapscript: one corner, then the opposite one")
	tell(clientNum, "^7/bcancel /btest /bundo /blist ^3forget the corner, try them in game, drop the last, print again")
	tell(clientNum, "^3barrier outlines: ^6magenta^3 in the mapscript, ^5cyan^3 made this level")
	tell(clientNum, "^3playing: ^7" .. (variant ~= "" and variant or "regular map") ..
		"^3, file: ^7" .. full_path())
end

local function cmd_pos(clientNum)
	tell(clientNum, "^7position: ^3" .. fmt_pos(get_pos(clientNum)))
end

local function cmd_info(clientNum)
	local pos = get_pos(clientNum)
	local inside = square_at(pos)

	if inside ~= nil then
		tell(clientNum, "^2you are inside: ^7" .. describe(inside))
		return
	end

	local square, dist = nearest_square(pos)
	if square == nil then
		tell(clientNum, "^1no squares loaded for this map")
		return
	end

	tell(clientNum, string.format("^7nearest square: ^3%s^7, %.0f units away", describe(square), dist))
end

local function cmd_test(clientNum)
	if not is_alive(clientNum) then
		tell(clientNum, "^1can't teleport while dead")
		return
	end

	local pos = get_pos(clientNum)
	local square = square_at(pos) or nearest_square(pos)
	if square == nil then
		tell(clientNum, "^1no squares loaded for this map")
		return
	end

	for try = 1, MAX_TRIES do
		local spot = random_spot_in_square(square, clientNum)

		if spot ~= nil then
			teleport(clientNum, spot)
			tell(clientNum, "^2moved to ^7" .. fmt_pos(spot) .. "^2, square on line " ..
				square.line .. ", try " .. try)
			return
		end
	end

	tell(clientNum, "^1no valid spot in square on line " .. square.line ..
		" after " .. MAX_TRIES .. " tries")
end

local function cmd_corner(clientNum)
	local pos = get_pos(clientNum)
	if not is_alive(clientNum) or not standing_on_ground(clientNum, pos) then
		tell(clientNum, "^1stand upright on the floor to mark a corner")
		return
	end

	local first = pending[clientNum]
	if first == nil then
		pending[clientNum] = pos
		tell(clientNum, "^2first corner at ^7" .. fmt_pos(pos) ..
			"^2, now /pcorner in the opposite corner (/pcancel to drop it)")
		return
	end

	if math.abs(pos[1] - first[1]) < MIN_SIDE or math.abs(pos[2] - first[2]) < MIN_SIDE then
		tell(clientNum, "^1too small: each side must be at least " .. MIN_SIDE ..
			" units, move further along both axes")
		return
	end

	if math.abs(pos[3] - first[3]) > HEIGHT_TOLERANCE then
		tell(clientNum, string.format("^3the corners are %.0f units apart in height; " ..
			"the square uses the first corner's height", math.abs(pos[3] - first[3])))
	end

	-- a first argument that names a variant of this map tags the square,
	-- the rest is the label
	local tags = {}
	local first_word = 1
	local name = et.trap_Argc() > 1 and string.lower(et.trap_Argv(1)) or ""

	if name ~= "" and is_variant_of_map(name) then
		tags[1] = name
		first_word = 2
	end

	local words = {}
	for i = first_word, et.trap_Argc() - 1 do
		words[#words + 1] = et.trap_Argv(i)
	end

	local square = make_square(first[1], first[2], pos[1], pos[2], first[3])
	square.tags = tags

	load_squares() -- start from what is on disk right now
	file_lines[#file_lines + 1] = format_square(square, table.concat(words, " "))

	if not save_squares() then
		tell(clientNum, "^1could not write " .. full_path())
		return
	end

	pending[clientNum] = nil

	local added = squares[#squares] -- the appended line is the last square
	tell(clientNum, "^2added line " .. added.line .. ": ^7" .. file_lines[added.line])
	tell(clientNum, "^7for: ^3" .. (#added.tags > 0 and "regular map and " .. added.tags[1]
		or "regular map only"))
	tell(clientNum, "^7valid spots: ^3" .. rate_square(added, clientNum) .. "/" .. CHECK_SAMPLES)
end

-- /ptag and /puntag: add or remove variant tags on the square you stand in.
local function cmd_tag(clientNum, add)
	local names = {}
	for i = 1, et.trap_Argc() - 1 do
		names[#names + 1] = string.lower(et.trap_Argv(i))
	end

	if #names == 0 then
		tell(clientNum, "^1usage: /" .. (add and "ptag" or "puntag") .. " <variant> [...]")
		return
	end

	load_squares() -- start from what is on disk right now
	local square = square_at(get_pos(clientNum))
	if square == nil then
		tell(clientNum, "^1you are not standing in a square")
		return
	end

	for _, name in ipairs(names) do
		if add then
			if not is_variant_of_map(name) then
				tell(clientNum, "^3" .. name .. " is not a variant of this map " ..
					"(no maps/" .. name .. ".variant for it), tagged anyway")
			end

			if not has_tag(square, name) then
				square.tags[#square.tags + 1] = name
			end
		else
			for i = #square.tags, 1, -1 do
				if square.tags[i] == name then table.remove(square.tags, i) end
			end
		end
	end

	local line = square.line
	file_lines[line] = format_square(square, square.comment)

	if not save_squares() then
		tell(clientNum, "^1could not write " .. full_path())
		return
	end

	tell(clientNum, "^2line " .. line .. ": ^7" .. file_lines[line])
end

local function cmd_cancel(clientNum)
	if pending[clientNum] == nil then
		tell(clientNum, "^3no first corner to forget")
		return
	end

	pending[clientNum] = nil
	tell(clientNum, "^2first corner dropped")
end

local function cmd_del(clientNum)
	load_squares() -- start from what is on disk right now
	local square = square_at(get_pos(clientNum))
	if square == nil then
		tell(clientNum, "^1you are not standing in a square")
		return
	end

	local removed = table.remove(file_lines, square.line)

	if not save_squares() then
		tell(clientNum, "^1could not write " .. full_path())
		return
	end

	tell(clientNum, "^2removed line " .. square.line .. ": ^7" .. removed)
end

local function cmd_show(clientNum)
	shown[clientNum] = not shown[clientNum] or nil
	tell(clientNum, shown[clientNum] and "^2outlines on" or "^3outlines off")
end

local function cmd_reload(clientNum)
	load_squares()
	load_script_barriers()
	tell(clientNum, "^2" .. #squares .. " squares loaded from ^7" .. full_path())
end

local function cmd_bcorner(clientNum)
	local pos = get_pos(clientNum)
	if not is_alive(clientNum) or not standing_on_ground(clientNum, pos) then
		tell(clientNum, "^1stand upright on the floor to mark a corner")
		return
	end

	local first = pending_barrier[clientNum]
	if first == nil then
		pending_barrier[clientNum] = pos
		tell(clientNum, "^2first barrier corner at ^7" .. fmt_pos(pos) ..
			"^2, now /bcorner [height] [solid] in the opposite corner (/bcancel to drop it)")
		return
	end

	local height, contents = BARRIER_HEIGHT, CONTENTS_PLAYERCLIP
	for i = 1, et.trap_Argc() - 1 do
		local arg = string.lower(et.trap_Argv(i))
		if arg == "solid" then
			contents = CONTENTS_SOLID
		elseif tonumber(arg) ~= nil and tonumber(arg) > 0 then
			height = tonumber(arg)
		else
			tell(clientNum, "^1usage: /bcorner [height] [solid]")
			return
		end
	end

	-- exactly between the two spots, from the lower floor up
	local b = { mins = {}, maxs = {}, contents = contents }

	for k = 1, 2 do
		local lo, hi = math.min(first[k], pos[k]), math.max(first[k], pos[k])

		if hi - lo < BARRIER_MIN_THICKNESS then -- a line across a doorway: give it some thickness
			local mid = (lo + hi) / 2
			lo, hi = mid - BARRIER_MIN_THICKNESS / 2, mid + BARRIER_MIN_THICKNESS / 2
		end

		b.mins[k], b.maxs[k] = math.floor(lo + 0.5), math.floor(hi + 0.5)
	end

	b.mins[3] = math.floor(math.min(first[3], pos[3]) + PLAYER_MINS[3] + 0.5)
	b.maxs[3] = math.floor(math.max(first[3], pos[3]) + PLAYER_MINS[3] + height + 0.5)

	pending_barrier[clientNum] = nil
	new_barriers[#new_barriers + 1] = b

	tell(clientNum, "^2barrier " .. #new_barriers .. ", for the mapscript's game_manager spawn. " ..
		"Copy it from the server console or etconsole.log: quotes show as ' here")
	print_barrier(clientNum, b)

	if barriers_on then
		tell(clientNum, "^3step out of it and /btest twice to try it")
	end
end

local function cmd_bcancel(clientNum)
	if pending_barrier[clientNum] == nil then
		tell(clientNum, "^3no first barrier corner to forget")
		return
	end

	pending_barrier[clientNum] = nil
	tell(clientNum, "^2first barrier corner dropped")
end

local function cmd_btest(clientNum)
	if #new_barriers == 0 then
		tell(clientNum, "^3no barriers made this level, /bcorner makes one")
		return
	end

	barriers_on = not barriers_on

	if not barriers_on then
		for _, b in ipairs(new_barriers) do set_barrier_live(b, false) end
		tell(clientNum, "^2barriers off")
		return
	end

	local on = 0
	for n, b in ipairs(new_barriers) do
		if #players_inside(b) > 0 then
			tell(clientNum, "^3barrier " .. n .. " skipped: someone is standing in it")
		else
			set_barrier_live(b, true)
			if b.ent ~= nil then on = on + 1 end
		end
	end

	tell(clientNum, "^2" .. on .. " of " .. #new_barriers .. " barriers on, /btest again to turn them off")
end

local function cmd_bundo(clientNum)
	local b = table.remove(new_barriers)
	if b == nil then
		tell(clientNum, "^3no barriers made this level")
		return
	end

	set_barrier_live(b, false)
	tell(clientNum, "^2dropped barrier " .. (#new_barriers + 1))
end

local function cmd_blist(clientNum)
	if #new_barriers == 0 then
		tell(clientNum, "^3no barriers made this level")
		return
	end

	tell(clientNum, "^3copy them from the server console or etconsole.log: quotes show as ' here")
	for n, b in ipairs(new_barriers) do
		tell(clientNum, "^3barrier " .. n .. ":")
		print_barrier(clientNum, b)
	end
end

-- callbacks ---------------------------------------------------------------

function et_InitGame(levelTime, randomSeed, restart)
	et.RegisterModname(modname .. " " .. version)
	math.randomseed(randomSeed)
	maxclients = tonumber(et.trap_Cvar_Get("sv_maxclients")) or 64
	next_draw = 0
	pending = {}
	variant = string.lower(et.trap_Cvar_Get("g_mapVariant") or "")
	pending_barrier = {}
	new_barriers = {}
	barriers_on = false
	load_squares()
	load_script_barriers()
	et.G_Print("deathmatch: " .. #squares .. " squares from " .. full_path() .. "\n")
end

function et_ClientDisconnect(clientNum)
	pending[clientNum] = nil
	pending_barrier[clientNum] = nil
	shown[clientNum] = nil
end

function et_RunFrame(levelTime)
	if levelTime < next_draw then return end
	next_draw = levelTime + DRAW_INTERVAL

	draw_all()
end

function et_ClientCommand(clientNum, command)
	local cmd = string.lower(et.trap_Argv(0))

	if cmd == "phelp" then
		cmd_help(clientNum)
	elseif cmd == "ppos" then
		cmd_pos(clientNum)
	elseif cmd == "pcorner" then
		cmd_corner(clientNum)
	elseif cmd == "pcancel" then
		cmd_cancel(clientNum)
	elseif cmd == "pinfo" then
		cmd_info(clientNum)
	elseif cmd == "ptest" then
		cmd_test(clientNum)
	elseif cmd == "ptag" then
		cmd_tag(clientNum, true)
	elseif cmd == "puntag" then
		cmd_tag(clientNum, false)
	elseif cmd == "pdel" then
		cmd_del(clientNum)
	elseif cmd == "pshow" then
		cmd_show(clientNum)
	elseif cmd == "preload" then
		cmd_reload(clientNum)
	elseif cmd == "bcorner" then
		cmd_bcorner(clientNum)
	elseif cmd == "bcancel" then
		cmd_bcancel(clientNum)
	elseif cmd == "btest" then
		cmd_btest(clientNum)
	elseif cmd == "bundo" then
		cmd_bundo(clientNum)
	elseif cmd == "blist" then
		cmd_blist(clientNum)
	else
		return 0 -- not ours, let other modules and the mod handle it
	end

	return 1
end
