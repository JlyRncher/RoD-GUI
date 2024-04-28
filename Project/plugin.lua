-- RoD_UI - Realms of Despair User Interface
-- Author: Sepharoth
-- Version: 1.0
--
-- See the "Acknowledgements" section of the README file for credits.
-- Edited in Notepad++ using tabwidth=4
require "tprint"
-- msdp stuff, don't touch!
local using_msdp = false
local MSDP = 69
local msdp = {}

local using_msp = false
local MSP = 90

-- setup miniwindows
local background_win = "background_window_" .. GetPluginID()
local top_panel = "top_panel_" .. GetPluginID()
local logo_win = "zlogo_window_" .. GetPluginID()	-- starts with z to trick drawing order
local top_right_panel = "top_right_panel_" .. GetPluginID()
local left_panel = "left_panel_" .. GetPluginID()
local info_panel = "info_panel_" .. GetPluginID()
local bottom_panel = "bottom_panel_" .. GetPluginID()
local health_win = "health_bar_" .. GetPluginID()
local mana_win = "mana_bar_"  .. GetPluginID()
local movement_win = "movement_bar_"  .. GetPluginID()
local xp_win = "zexperience_window_" .. GetPluginID()	-- starts with z to trick drawing order
local opponent_win = "opponent_bar_"  .. GetPluginID()
local score_win = "score_window_" .. GetPluginID()
local affect_win = "affect_window_" .. GetPluginID()
local area_win = "area_window_" .. GetPluginID()
local eq_win = "eq_window_" .. GetPluginID()
local minimap_win = "minimap_window_" .. GetPluginID()
local console_win = "console_window_" .. GetPluginID()

-- setup buttons
local score_button = "score_button_" .. GetPluginID()
local affect_button = "affect_button_" .. GetPluginID()
local area_button = "area_button_" .. GetPluginID()
local repair_button = "repair_button_" .. GetPluginID()
local cancel_button = "cancel_button_" .. GetPluginID()

-- dimensions
local screen_width				-- GetInfo(281)
local screen_height				-- GetInfo(280)
local bar_width					-- for health/mana/blood/movement/xp/opp.
local bar_height				-- for health/mana/blood/movement/xp/opp.
local top_panel_height = 80		-- height of the top panel containing player bars
local left_panel_width = 70		-- width of the left panel containing buttons
local right_panel_width = 275 	-- width of the panels on the right side of the screen
local bottom_panel_height = 35	-- width of the panel containing the opponent bar
local logo_width = 485			-- width in pixels of the logo image
local opponent_width = logo_width-125	-- width of the opponent health bar
local min_width = 945 			-- 70 + 600 + 275
local min_height = 485 			-- 80 + 375 + 35

-- misc. variables
local version_ok = false		-- is the client version ok?
local timer_warning = 10 		-- warning level for spell affects, in rounds (gray)
local timer_critical = 3 		-- critical level for spell affects, in rounds (red)
local affects = {}				-- table containing player spell affects
local RoomExit					-- table containing room exits
local RoomType					-- table containing room type (0 = closed, 1 = open)
local ExitCount					-- number of exits leading out of the current room
local console_log = {}			-- contains messages about ui and other select events
local affect_scroll = 0 		-- used in affect window to control visible spells
local affect_scroll_bottom_max	-- the maximum allowed scrollable distance downward
local area_scroll = 0			-- used in the area window to control visible areas
local area_scroll_bottom_max	-- the maximum allowed scrollable distance downward
local repair_scroll = 0			-- used in the repair window to control visible areas
local repair_scroll_bottom_max	-- the maximum allowed scrollable distance downward
local is_loaded = false			-- set to true after the first initialization
local area_list					-- list of all area names parsed from directions.xml file
local filter_text = nil			-- text filter for area panel, if present we need to display things differently
local load_once = false			-- used to only load the avatar image one time
local START_ROOM = "Darkhaven Square"	-- basis room from which all directions are navigated (safety)
local EQ_AUTO_AC = true			-- toggle for whether we should automatically try and set MaxAC from an eqdb
local item_nodes				-- used for xml parsing
local eq = {}					-- table containg list of all scanned eq.
local sorted_damaged_eq = {}	-- sort eq table into an index table where items with highest # of hits are first
local scanned = false			-- so we only scan on the first connect and not subsequence connects
local repair_total = 0			-- the total cost of repairs
local repair_needed = 0			-- remaining cost needed to repair eq
local cancel_showing = false	-- is the "Cancel Action" button showing
local alt_affects_view = false	-- is the alternate affects view on?
local area_modifier = 0			-- used when player is config +NEWBIE to modify area list
local level
local areas_loaded = false

local info_windows = {score_win, affect_win, area_win, eq_win, xp_win} -- table containing all dynamically loaded windows
local current_window -- the current window set showing in the dynamic pane

-- path to asset directory
-- GetInfo(66) = MUSHclient base directory e.g. C:\Program Files (x86)\MUSHclient\
local asset_path = GetInfo(66) .. "worlds//plugins//rod_ui//"

-- predefined colours
local colourWhite = ColourNameToRGB("#ffffff")
local colourGreen = ColourNameToRGB("#00ff00")
local colourGold = ColourNameToRGB("#fdd017")
local colourBlack = ColourNameToRGB("#000000")
local colourRed = ColourNameToRGB("#ff0000")
local colourDarkGray = ColourNameToRGB("#080808")
local colourOrange = ColourNameToRGB("#ff6600")

-- NOTE: Always use colourDarkGray if you want to give a "black" effect to a window
-- or image in a miniwindow that has the transparent flag set (4). Using "real" black
-- in a miniwindow with a background colour of black and the transparent flag set will
-- show the contents behind the colour.

-- predefined fonts and their respective fallbacks in case preferred fonts are not installed
-- *nix users may need to make adjustments here if they do not have the mscorefonts installed
local fixed_width = "Consolas"		-- font used for items that require precise spacing (available from Vista onwards)
local fixed_width_fb = "Courier"
local bar_font = "Verdana" 			-- font for gauges and other non-stylized items
local bar_font_fb = "Arial"
local default_font = "Georgia" 		-- default font used for text in the ui
local default_font_fb = "Arial"

-- table containing all "important" spell affects
local i_affects = {"sanctuary",
	"greater sanctuary",
	"sacral divinity",
	"prophetic aura",
	"holy sanctity",
	"nadur dion",
	"major invocation",
	"indignation",
	"true sight",
	"glass eye",
	"elemental supremacy",
	"iceshield",
	"fireshield",
	"shockshield",
	"fly",
	"aqua breath",
	"inviola magicka"}
table.sort(i_affects) -- so we can use binary search

-- table containing spelldowns (not exhaustive)
local spelldowns = {"razorbait",
	"lethargy",
	"swordbait",
	"acidmist",
	"blazebane",
	"faerie fire",
	"ill fortune",
	"execrate",
	"kleshas",
	"blasphemy",
	"petrification",
	"chains of agony",
	"enervate",
	"mental anguish",
	"blindness",
	"poison",
	"curse",
	"weaken",
	"burden defense",
	"unravel defense",
	"salvation",
	"wisteria"}
table.sort(spelldowns) -- so we can use binary search

-- so the plugin doesn't freeze on initial load due to 15+ resizes in ~0.1 secs
AddTimer("init_delay", 0, 0, 2.0, "", timer_flag.Enabled + timer_flag.OneShot, "")

-- plugin hook
function OnPluginWorldOutputResized()
	if IsTimer("init_delay") ~= 0 then	-- if the timer DOESN'T exist
		do_resize()
		draw_panes()
		--Note(msdp["WORLD_TIME"]) -- test to see if it has been implemented yet!
	else end -- end
end -- if

-- plugin hook
function OnPluginDisconnect()
	DiscardQueue()	-- Forget about any commands we were processing (avoid sitebans!)
	-- reset the scroll positions
	affect_scroll = 0
	area_scroll = 0
	repair_scroll = 0
	WindowShow(opponent_win, false)
	WindowShow(cancel_button, false)
	cancel_showing = false
	areas_loaded = false
	check(WindowDrawImage(logo_win, "rod_logo_full", 0, 0, 0, 0, miniwin.image_transparent_copy))
	
	-- dump equipment max ac values into variables
	-- look into serialize instead?
	for k,v in pairs(eq) do
		SetVariable(encode(v.name), v.max_hits)
		--Note("Saved " .. v.name .. " with value: " .. v.max_hits)
	end -- for
	SaveState()
end -- function

-- plugin hook
function OnPluginInstall()
	Disconnect() -- force the client offline
	AddTimer("update_console_timer", 0, 0, 1.0, "", 0, "update_console")
	table.insert(console_log, "> Realms of Despair UI (v." .. string.format("%.1f", 
					GetPluginInfo(GetPluginID(), 19)) .. ") plugin by Sepharoth.")
	if tonumber(GetInfo(72)) < 4.43 then
		table.insert(console_log, "> MUSHclient version is >= 4.73: FAIL")
		ColourNote("red", "", "> Warning: Your client version is not compatible with this plugin. Please upgrade to the latest version.")
	elseif tonumber(GetInfo(72)) < 4.73 then
		table.insert(console_log, "> MUSHclient version is >= 4.73: FAIL")
		ColourNote("red", "", "> Warning: Plugin not designed to function on client version < 4.73. Some components may not work.")
	else
		table.insert(console_log, "> MUSHclient version is >= 4.73: OK")
		version_ok = true
		local file = io.open(asset_path .. "etc//directions.xml", "r")
		local directions = assert(file:read '*a', "DirectionsDB XML is corrupt.")
		file:close()

		local status = ImportXML(directions)	-- directions are loaded as temporary aliases
		if status >= 0 then
			table.insert(console_log, "> Directions database loaded.")
		else
			table.insert(console_log, "> Error (" .. status .. "): Directions database is corrupt.")
		end -- if
	end -- if
	
	if GetVariable("warnings") ~= "true" then
		SetVariable("warnings", "false")
		table.insert(console_log, "> Warnings are disabled.")
	else
		table.insert(console_log, "> Warnings are enabled.")
	end -- if
	
	if GetVariable("newbie") ~= "false" then
		SetVariable("newbie", "true")
		table.insert(console_log, "> Newbie mode enabled.")
	else
		table.insert(console_log, "> Newbie mode disabled.")
	end -- if
	
	-- make sure we have set fonts that actually exist on the system
	local found_fixed = false
	local found_default = false
	local found_bar = false
	for font in pairs(utils.getfontfamilies()) do
		if font == fixed_width then
			found_fixed = true
		elseif font == default_font then
			found_default = true
		elseif font == bar_font then
			found_bar = true
		else end -- if
	end -- for
	
	-- check to make sure fonts were found, if not then revert to fallback fonts
	if not found_fixed then
		fixed_width = fixed_width_fb
		table.insert(console_log, "> Using backup font for 'fixed width'.")
	else end -- if
	
	if not found_default then
		default_font = default_font_fb
		table.insert(console_log, "> Using backup font for 'default'.")
	else end -- if
	
	if not found_bar then
		bar_font = bar_font_fb
		table.insert(console_log, "> Using backup font for 'bar'.")
	else end -- if
	
	if GetGlobalOption("OpenWorldsMaximised") ~= 1 then
		  -- set the OpenWorldsMaximised option
		  db = sqlite3.open(GetInfo (82))  -- open preferences
		  db:exec 'UPDATE prefs SET value = 1 WHERE name = "OpenWorldsMaximised"'
		  db:close()  -- close

		  -- update the global preferences
		  utils.reload_global_prefs ()
	end -- if
	
	SetOption("enable_timers", true)	-- we need timers to be enabled
	SetOption("auto_repeat", true)		-- leave the last command typed on the input line
	ColourNote("#00ff00", "", "[GUI] ", "white", "", "Plugin installed. Reconnect to the world.")
end -- function

-- plugin hook
function OnPluginConnect()
	check_dimensions(GetInfo(281), GetInfo(280))
	create_layout()
end -- function

-- plugin hook
function OnPluginTelnetRequest(type, data)
	if type == MSDP and data == "WILL" then
		using_msdp = true
		return true
	elseif type == MSDP and data == "SENT_DO" then
		-- IAC SB MSDP response IAC SE
		local request_vars = "\255\250\69\1REPORT\2CHARACTER_NAME\2RACE\2CLASS\2HEALTH_MAX\2HEALTH\2MANA_MAX\2MANA\2MOVEMENT_MAX\2MOVEMENT\2EXPERIENCE_TNL\2EXPERIENCE\2BLOOD\2LEVEL\2HITROLL\2DAMROLL\2AC\2STR\2INT\2WIS\2DEX\2CON\2CHA\2LCK\2STR_PERM\2INT_PERM\2WIS_PERM\2DEX_PERM\2CON_PERM\2CHA_PERM\2LCK_PERM\2ALIGNMENT\2AFFECTS\2WIMPY\2PRACTICE\2MONEY\2ROOM_EXITS\2AREA_NAME\2ROOM_NAME\2WORLD_TIME\2OPPONENT_NAME\2OPPONENT_HEALTH\2OPPONENT_LEVEL\2\255\240"
		SendPkt(request_vars)
		return true
	elseif type == MSP and data == "WILL" then
		using_msp = true
		return true -- IAC DO MSP
	else -- another protocol
		return false
	end -- if
end -- function

-- plugin hook
function OnPluginTelnetSubnegotiation(type, data)
	if type == MSDP then
		endpos=string.len(data)
		for i=endpos,1,-1 do
			if string.byte(data,i) == 1 then
				variable = string.sub(data,i+1,endpos)
				StoreVariable(variable, value)
				endpos = i-1
			elseif string.byte(data,i) == 2 then
				value = string.sub(data,i+1,endpos)
				endpos = i-1
			end -- if
		end -- for

		--  redraw the map
		draw_minimap()
		-- redraw the energy bars
		draw_energy_bars()
		-- redraw the score
		draw_score()
		-- redraw affects
		draw_affects()
		-- draw world time
		draw_time()
		if not areas_loaded then
			draw_area_list()
		else end -- if
	elseif type == MSP then
		Note("Received MSP string.")	-- currently testing msp integration
	end -- if
end -- function

function draw_panes()
	--  redraw the map
	draw_minimap()
	-- redraw the energy bars
	draw_energy_bars()
	-- redraw the score
	draw_score()
	-- redraw affects
	draw_affects()
	-- draw time
	draw_time()
	-- redraw the area list
	draw_area_list()
	-- redraw the eq window
	draw_eq_window()
	-- general redraw, leftover from KaVir's script
	Redraw()
end -- function

-- recreate the layout to new screen dimensions
function do_resize()
	check_dimensions(GetInfo(281), GetInfo(280))
	create_layout()
end -- function

-- make sure the new dimensions meet the minimum requirements
function check_dimensions(width, height)
	if width < min_width then
		screen_width = min_width
	else
		screen_width = width
	end -- if
	if height < min_height then
		screen_height = min_height
	else
		screen_height = height
	end -- if
end -- function

-- this function is run after once the player has ENTERED the game (after login/motd seq.)
-- triggered on: "Welcome to Realms of Despair, ..."
function init_script()
	if GetVariable("eqAutoScan") == "true" then
		if scanned ~= true then
			scanned = true
			table.insert(console_log, "> EQscan is enabled. Forcing scan.")
			Execute("ui.eqscan")
		else
			table.insert(console_log, "> EQscan is enabled. Scan already performed.")
		end -- if
	else end -- if
end -- function

-- create/draw/show windows using current dimensions
function create_layout()
	-- set up TextRectangle
	left = left_panel_width
	top = top_panel_height	-- give space for the top panel
	right = screen_width - right_panel_width	-- give space for the right panel
	-- if right < tonumber(GetInfo(213) * 85) then	-- the minimum width!
		-- right = tonumber(GetInfo(213) * 85)
	-- else end -- if
	bottom = screen_height - bottom_panel_height -- give space for the bottom window

	-- avoid the plugin crashing if someone makes the window stupidly small
	if bottom < top then
		bottom = top
	end -- if

	TextRectangle(left+15,  		-- left
					top+15,   		-- top
					right,			-- width
					bottom-15,  	-- height
					0,  			-- BorderOffset, 
					colourWhite,   	-- BorderColour, 
					0,  			-- BorderWidth, 
					colourWhite,  	-- OutsideFillColour, 
					1) 				-- OutsideFillStyle (fine hatch)
	-- enforce the 90 column wrap
	-- we can't do anything about the user changing these options in the client itself
	SetOption("auto_wrap_window_width", false)
	SetOption("wrap", true)
	SetOption("wrap_column", 90)
			
	-- make a miniwindow under the text for background img
	check(WindowCreate (background_win,   	-- window ID
							left,           -- left
							top,            -- top
							right-left,		-- right
							bottom-bottom_panel_height,		-- depth
							5,            	-- center it (ignored anyway) 
							3,             	-- draw underneath (1) + absolute location (2)
							colourBlack))  	-- background colour
	
	check (WindowCreate (left_panel,   		-- window ID
						0,            		-- left
						top_panel_height,	-- top
						left_panel_width,
						bottom - bottom_panel_height,
						5,            		-- center it (ignored anyway) 
						7,             		-- draw underneath (1) + absolute location (2)
						colourBlack))  		-- background colour	
	
	check (WindowCreate (top_panel,   		-- window ID
						 0,         		-- left
						 0,           		-- top
						 right, 			-- width
						 top_panel_height,	-- depth
						 5,            		-- center it (ignored anyway) 
						 3,             	-- draw underneath (1) + absolute location (2)
						 colourBlack))  	-- background colour
	
	check (WindowCreate (top_right_panel,   -- window ID
						 right,         	-- left
						 0,            		-- top
						 right_panel_width, -- width
						 210,				-- depth
						 5,            		-- center it (ignored anyway) 
						 7,             	-- draw underneath (1) + absolute location (2)
						 colourBlack))  	-- background colour	
	
	check (WindowCreate (info_panel,   			-- window ID
						 right,         		-- left
						 210,           		-- top
						 right_panel_width, 	-- width
						 screen_height - 210,	-- depth
						 5,            			-- center it (ignored anyway) 
						 3,             		-- draw underneath (1) + absolute location (2)
						 colourBlack))  		-- background colour
	
	check (WindowCreate (bottom_panel,   						-- window ID
						 left_panel_width,         				-- left
						 screen_height - bottom_panel_height,	-- top
						 right-left_panel_width, 				-- width
						 bottom_panel_height,					-- depth
						 5,            							-- center it (ignored anyway) 
						 7,             						-- draw underneath (1) + absolute location (2)
						 colourBlack))  						-- background colour
	
	check(WindowCreate (minimap_win,   		-- window ID
							 right+62,		-- left
							 25,    		-- top
							 150,			-- width
							 150,        	-- depth
							 12,         	-- center it (ignored anyway) 
							 6, 			-- draw underneath (1) + absolute location (2)
							 colourBlack))	-- background colour	

	-- setup character status bars
	local next_bar = left_panel_width	-- where to position the beginning of the bar
	local bar_padding_top = 10	-- padding from the top, border height is 10
	local outer_padding = 10 -- so the health bars are in line with the text rectangle
	bar_width = (right - left_panel_width - (outer_padding*2))/3	-- get the width for the 3 bars
	bar_height = 25	-- how tall the health/mana/blood/movement/opponent bars will be
	
	check(WindowCreate (health_win,   					-- window ID
							next_bar,            		-- left
							screen_height - bottom_panel_height + bar_padding_top,            -- top
							bar_width,          		-- width
							bar_height,            		-- depth
							5,            				-- center it (ignored anyway) 
							6,             				-- draw underneath (1) + absolute location (2) + transparent (4)
							colourBlack))  -- background colour

	next_bar = next_bar + bar_width + outer_padding
	--make a miniwindow for mana
	check(WindowCreate (mana_win,   					-- window ID
							next_bar,            		-- left
							screen_height - bottom_panel_height + bar_padding_top,           	-- top
							bar_width,           		-- width
							bar_height,            		-- depth
							5,            				-- center it (ignored anyway) 
							6,             				-- draw underneath (1) + absolute location (2) + transparent (4)
							colourBlack))  -- background colour	
	
	next_bar = next_bar + bar_width + outer_padding
	--make a miniwindow for movement
	check (WindowCreate (movement_win,   				-- window ID
							next_bar,            		-- left
							screen_height - bottom_panel_height + bar_padding_top, 	-- top
							bar_width,           		-- width
							bar_height,		            -- depth
							5,            				-- center it (ignored anyway) 
							6,             				-- draw underneath (1) + absolute location (2) + transparent (4)
							colourBlack))  				-- background colour
	
	
	-- make a miniwindow for the opponent
	check (WindowCreate (opponent_win,   						-- window ID
							((screen_width-right_panel_width-(logo_width))/2)+55,            		-- left
							bar_padding_top+20, 	-- top
							opponent_width,			-- width
							bar_height+10,      	-- depth
							5,            			-- center it (ignored anyway) 
							6,             			-- draw underneath (1) + absolute location (2) + transparent (4)
							colourBlack))  			-- background colour
							
	check (WindowCreate (logo_win,   			-- window ID
						 (screen_width-right_panel_width-(logo_width))/2,  -- left
						 0,           			-- top
						 logo_width, 			-- width
						 top_panel_height-10,	-- depth
						 5,            			-- center it (ignored anyway) 
						 6,             		-- draw underneath (1) + absolute location (2)
						 colourBlack))  		-- background colour
	
	--make a miniwindow for xp
	check (WindowCreate (xp_win,		   			-- window ID
							right+25,            	-- left
							540,		           	-- top
							235,					-- width
							40,            			-- depth
							5,            			-- center it (ignored anyway) 
							6,             			-- draw underneath (1) + absolute location (2) + transparent (4)
							colourBlack))  			-- background colour

  -- score window
	check (WindowCreate (score_win,   				-- window ID
							right+10,       		-- left
							200+10,           		-- top
							right_panel_width, 		-- width
							screen_height - 210,	-- depth
							5,            			-- center it (ignored anyway) 
							6,             			-- draw underneath (1) + absolute location (2)
							colourBlack))  			-- background colour
	
	-- affects window
	WindowCreate(affect_win,
						right+10,
						200+10,
						right_panel_width,
						screen_height - 210,
						5,
						6,
						colourBlack)
						
	WindowAddHotspot(affect_win, "change_affect_view",  
                 190,
				 0,
				 215,
				 25,   						-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Order affects by importance",	-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
			  
	WindowAddHotspot(affect_win, "affect_scroll_up",  
                 210,
				 0,
				 235,
				 25,   						-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "",						-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	WindowAddHotspot(affect_win, "affect_scroll_down",  
                 235,
				 0,
				 260,
				 25,			   			-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "",						-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	-- we add a scrollwheel handler to this hotspot
	WindowAddHotspot(affect_win, "affect_scrollwheel",  
                 0,
				 30,
				 right_panel_width,
				 screen_height - 210,			-- rectangle
                 "",				-- mouseover 
                 "", 		-- cancelmouseover
                 "",				-- mousedown
                 "", 		-- cancelmousedown
                 "", 				-- mouseup
                 "",						-- tooltip text
                 miniwin.cursor_ns_arrow, 0)  	-- hand cursor
	WindowScrollwheelHandler(affect_win, "affect_scrollwheel", "scrollwheel")
	
	-- area list window
	WindowCreate(area_win,
						right+10,
						200+10,
						right_panel_width,
						screen_height - 210,
						5,
						6,
						colourBlack)
						
	-- repair window
	WindowCreate(eq_win,
						right+10,
						200+10,
						right_panel_width,
						screen_height - 210,
						5,
						6,
						colourBlack)
						
	WindowAddHotspot(eq_win, "scan_eq",  
                 165,
				 0,
				 290,
				 25,			   			-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Scan current equipment",		-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
	
	WindowAddHotspot(eq_win, "repair_eq",  
                 190,
				 0,
				 215,
				 25,			   			-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Repair equipment",		-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	WindowAddHotspot(eq_win, "repair_scroll_up",  
                 210,
				 0,
				 235,
				 25,   						-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "",						-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	WindowAddHotspot(eq_win, "repair_scroll_down",  
                 235,
				 0,
				 260,
				 25,			   			-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "",						-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	-- we add a scrollwheel handler to this hotspot
	WindowAddHotspot(eq_win, "zeq_scrollwheel",  
                 0,
				 30,
				 right_panel_width,
				 screen_height - 210,	-- rectangle
                 "",					-- mouseover 
                 "", 					-- cancelmouseover
                 "",					-- mousedown
                 "", 					-- cancelmousedown
                 "", 					-- mouseup
                 "",					-- tooltip text
                 miniwin.cursor_ns_arrow, 0)  	-- hand cursor
	WindowScrollwheelHandler(eq_win, "zeq_scrollwheel", "scrollwheel")
	
	-- buttons
	
	-- score button
	WindowCreate(score_button,
						5,
						90,
						50,
						50,
						12,
						6,
						colourBlack)
	
	WindowAddHotspot(score_button, "score",  
                 0, 0, 0, 0,   				-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Display character information",			-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
	
	-- affect button
	WindowCreate(affect_button,
						5,
						150,
						50,
						50,
						12,
						6,
						colourBlack)
	
	WindowAddHotspot(affect_button, "affects",  
                 0, 0, 0, 0,   				-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Display active spells",	-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor	
	
	-- area button
	WindowCreate(area_button,
						5,
						210,
						50,
						50,
						12,
						6,
						colourBlack)
	
	WindowAddHotspot(area_button, "area",  
                 0, 0, 0, 0,   				-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Display area list",		-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	-- repair button
	WindowCreate(repair_button,
						5,
						270,
						50,
						50,
						12,
						6,
						colourBlack)
	
	WindowAddHotspot(repair_button, "repair",  
                 0, 0, 0, 0,   				-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Display equipment list",		-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	-- cancel button
	WindowCreate(cancel_button,
						5,
						screen_height-60,
						50,
						50,
						12,
						6,
						colourBlack)
	
	WindowAddHotspot(cancel_button, "cancel",  
                 0, 0, 0, 0,   				-- rectangle
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "Cancel the current action",		-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
	
	check(WindowCreate (console_win,   	-- window ID
							right-400,      -- left
							top,            -- top
							400,			-- right
							200,			-- depth
							5,            	-- center it (ignored anyway) 
							6,             	-- draw underneath (1) + absolute location (2)
							colourBlack))  	-- background colour
				 
	if not is_loaded then 	-- do this section once per world open/plugin (re)install
		is_loaded = true	-- so we don't run this section again
		init_area_list() 	-- populate area_list table
		WindowFont(console_win, "console_font", fixed_width, 8, false, false, false, false)
		SetBackgroundImage(asset_path .. "background//brick.png", 13)	-- set the overall background image (drawn underneath everything else)
		-- background_win
		check(WindowLoadImage(background_win, "bg", asset_path .. "background//bg.png"))
		-- left_panel
		check(WindowLoadImage(left_panel, "border", asset_path .. "border//border_left.png"))
		-- top_panel
  		check(WindowLoadImage(top_panel, "ui_tile", asset_path .. "background//ui_tile.png"))
		check(WindowLoadImage(top_panel, "border", asset_path .. "border//border_top.png"))
		-- logo_win
		check(WindowLoadImage(logo_win, "rod_logo", asset_path .. "background//rod_logo.png"))
		check(WindowLoadImage(logo_win, "rod_logo_full", asset_path .. "background//rod_logo_full.png"))
		-- top_right_panel
		check(WindowLoadImage(top_right_panel, "border", asset_path .. "border//border_right.png"))
		check(WindowLoadImage(top_right_panel, "border_bottom", asset_path .. "border//border_bottom.png"))
		-- info_panel
  		check(WindowLoadImage(info_panel, "background", asset_path .. "background//ui_tile.png"))
		check(WindowLoadImage(info_panel, "border", asset_path .. "border//border_right.png"))
		-- bottom_panel
  		check(WindowLoadImage(bottom_panel, "ui_tile", asset_path .. "background//ui_tile.png"))
		check(WindowLoadImage(bottom_panel, "border", asset_path .. "border//border_bottom.png"))
		check(WindowLoadImage(bottom_panel, "separator", asset_path .. "border//separator.png"))
		-- bars
		-- health
		check(WindowLoadImage(health_win, "health_100", asset_path .. "bars//health//health_100.png"))
		check(WindowLoadImage(health_win, "health_90", asset_path .. "bars//health//health_90.png"))
		check(WindowLoadImage(health_win, "health_80", asset_path .. "bars//health//health_80.png"))
		check(WindowLoadImage(health_win, "health_70", asset_path .. "bars//health//health_70.png"))
		check(WindowLoadImage(health_win, "health_60", asset_path .. "bars//health//health_60.png"))
		check(WindowLoadImage(health_win, "health_50", asset_path .. "bars//health//health_50.png"))
		check(WindowLoadImage(health_win, "health_40", asset_path .. "bars//health//health_40.png"))
		check(WindowLoadImage(health_win, "health_30", asset_path .. "bars//health//health_30.png"))
		check(WindowLoadImage(health_win, "health_20", asset_path .. "bars//health//health_20.png"))
		check(WindowLoadImage(health_win, "health_10", asset_path .. "bars//health//health_10.png"))
		-- opponent_win
		check(WindowLoadImage(opponent_win, "health_100", asset_path .. "bars//health//health_100.png"))
		check(WindowLoadImage(opponent_win, "health_90", asset_path .. "bars//health//health_90.png"))
		check(WindowLoadImage(opponent_win, "health_80", asset_path .. "bars//health//health_80.png"))
		check(WindowLoadImage(opponent_win, "health_70", asset_path .. "bars//health//health_70.png"))
		check(WindowLoadImage(opponent_win, "health_60", asset_path .. "bars//health//health_60.png"))
		check(WindowLoadImage(opponent_win, "health_50", asset_path .. "bars//health//health_50.png"))
		check(WindowLoadImage(opponent_win, "health_40", asset_path .. "bars//health//health_40.png"))
		check(WindowLoadImage(opponent_win, "health_30", asset_path .. "bars//health//health_30.png"))
		check(WindowLoadImage(opponent_win, "health_20", asset_path .. "bars//health//health_20.png"))
		check(WindowLoadImage(opponent_win, "health_10", asset_path .. "bars//health//health_10.png"))
		-- mana
		check(WindowLoadImage(mana_win, "mana", asset_path .. "bars//mana.png"))
		-- blood
		check(WindowLoadImage(mana_win, "blood", asset_path .. "bars//blood.png"))
		-- xp
		check(WindowLoadImage(xp_win, "xp", asset_path .. "bars//xp.png"))
		-- movement win
		check(WindowLoadImage(movement_win, "movement", asset_path .. "bars//movement.png"))
		-- minimap_win
		check(WindowLoadImage(minimap_win, "minimap_border", asset_path .. "border//minimap_border.png"))
		check(WindowLoadImage(minimap_win, "terrain_city", asset_path .. "terrain//terrain_city.bmp"))
		check(WindowLoadImage(minimap_win, "terrain_dark", asset_path .. "terrain//terrain_dark.bmp"))
		-- score_win
		check(WindowLoadImage(score_win, "page", asset_path .. "background//score.png"))
		check(WindowLoadImage(score_win, "title_bar", asset_path .. "border//title_bar.png"))
		check(WindowLoadImage(score_win, "avatar_border", asset_path .. "border//avatar_border.png"))
		-- affect_win
		check(WindowLoadImage(affect_win, "scroll", asset_path .. "background//affect.png"))
		check(WindowLoadImage(affect_win, "eye", asset_path .. "icon//affect_view.png"))
		check(WindowLoadImage(affect_win, "eye_hover", asset_path .. "icon//affect_view_hover.png"))
		check(WindowLoadImage(affect_win, "eye_on", asset_path .. "icon//affect_view_on.png"))
		check(WindowLoadImage(affect_win, "eye_on_hover", asset_path .. "icon//affect_view_on_hover.png"))
		check(WindowLoadImage(affect_win, "arrow_up", asset_path .. "icon//arrow_up.png"))
		check(WindowLoadImage(affect_win, "arrow_down", asset_path .. "icon//arrow_down.png"))
		check(WindowLoadImage(affect_win, "arrow_up_hover", asset_path .. "icon//arrow_up_hover.png"))
		check(WindowLoadImage(affect_win, "arrow_down_hover", asset_path .. "icon//arrow_down_hover.png"))
		check(WindowLoadImage(affect_win, "title_bar", asset_path .. "border//title_bar.png"))
		-- area_win
		check(WindowLoadImage(area_win, "map", asset_path .. "background//area.png"))
		check(WindowLoadImage(area_win, "arrow_up", asset_path .. "icon//arrow_up.png"))
		check(WindowLoadImage(area_win, "arrow_up_hover", asset_path .. "icon//arrow_up_hover.png"))
		check(WindowLoadImage(area_win, "arrow_down", asset_path .. "icon//arrow_down.png"))
		check(WindowLoadImage(area_win, "arrow_down_hover", asset_path .. "icon//arrow_down_hover.png"))
		check(WindowLoadImage(area_win, "filter", asset_path .. "icon//filter.png"))
		check(WindowLoadImage(area_win, "filter_cancel", asset_path .. "icon//filter_cancel.png"))
		check(WindowLoadImage(area_win, "filter_hover", asset_path .. "icon//filter_hover.png"))
		check(WindowLoadImage(area_win, "filter_cancel_hover", asset_path .. "icon//filter_cancel_hover.png"))
		check(WindowLoadImage(area_win, "title_bar", asset_path .. "border//title_bar.png"))
		-- eq_win
		check(WindowLoadImage(eq_win, "bg", asset_path .. "background//repair.png"))
		check(WindowLoadImage(eq_win, "title_bar", asset_path .. "border//title_bar.png"))
		check(WindowLoadImage(eq_win, "arrow_up", asset_path .. "icon//arrow_up.png"))
		check(WindowLoadImage(eq_win, "arrow_up_hover", asset_path .. "icon//arrow_up_hover.png"))
		check(WindowLoadImage(eq_win, "arrow_down", asset_path .. "icon//arrow_down.png"))
		check(WindowLoadImage(eq_win, "arrow_down_hover", asset_path .. "icon//arrow_down_hover.png"))
		check(WindowLoadImage(eq_win, "hammer", asset_path .. "icon//hammer.png"))
		check(WindowLoadImage(eq_win, "hammer_hover", asset_path .. "icon//hammer_hover.png"))
		check(WindowLoadImage(eq_win, "eqscan", asset_path .. "icon//eqscan.png"))
		check(WindowLoadImage(eq_win, "eqscan_hover", asset_path .. "icon//eqscan_hover.png"))
		-- affect_button
		check(WindowLoadImage(affect_button, "button", asset_path .. "icon//affect.png"))
		check(WindowLoadImage(affect_button, "button_hover", asset_path .. "icon//affect_hover.png"))
		check(WindowLoadImage(affect_button, "button_pressed", asset_path .. "icon//affect_pressed.png"))
		-- score_button
		check(WindowLoadImage(score_button, "button", asset_path .. "icon//score.png"))
		check(WindowLoadImage(score_button, "button_hover", asset_path .. "icon//score_hover.png"))
		check(WindowLoadImage(score_button, "button_pressed", asset_path .. "icon//score_pressed.png"))
		-- area_button
		check(WindowLoadImage(area_button, "button", asset_path .. "icon//area.png"))
		check(WindowLoadImage(area_button, "button_hover", asset_path .. "icon//area_hover.png"))
		check(WindowLoadImage(area_button, "button_pressed", asset_path .. "icon//area_pressed.png"))
		-- repair_button
		check(WindowLoadImage(repair_button, "button", asset_path .. "icon//repair.png"))
		check(WindowLoadImage(repair_button, "button_hover", asset_path .. "icon//repair_hover.png"))
		check(WindowLoadImage(repair_button, "button_pressed", asset_path .. "icon//repair_pressed.png"))
		-- cancel_button
		check(WindowLoadImage(cancel_button, "button", asset_path .. "icon//cancel.png"))
		check(WindowLoadImage(cancel_button, "button_hover", asset_path .. "icon//cancel_hover.png"))
		check(WindowLoadImage(cancel_button, "button_pressed", asset_path .. "icon//cancel_pressed.png"))
	else end -- if
	
	-- draw loaded images to windows
	check(WindowDrawImage(background_win, "bg", 0, 0, 0, 0, miniwin.image_stretch))
	check(WindowDrawImage(left_panel, "border", 60, 0, 70, 0, miniwin.image_stretch))
	WindowImageOp (top_panel, miniwin.image_fill_rectangle, -- rectangle
              0, 0, 0, 0,                         -- Left, Top, Right, Bottom
              ColourNameToRGB("blue"), miniwin.pen_null, 1,   -- no pen
              ColourNameToRGB("cyan"), "ui_tile")
	check(WindowDrawImage(top_panel, "border", 0, 70, 0, 80, miniwin.image_stretch))
	check(WindowDrawImage(top_right_panel, "border", 0, 0, 10, 0, miniwin.image_stretch))
	check(WindowDrawImage(top_right_panel, "border_bottom", 10, 200, 0, 0, miniwin.image_stretch))
	WindowImageOp (info_panel, miniwin.image_fill_rectangle, -- rectangle
              0, 0, 0, 0,                         -- Left, Top, Right, Bottom
              ColourNameToRGB("blue"), miniwin.pen_null, 1,   -- no pen
              ColourNameToRGB("cyan"), "background")
	check(WindowDrawImage(info_panel, "border", 0, 0, 10, 0, miniwin.image_stretch))
	WindowImageOp (bottom_panel, miniwin.image_fill_rectangle, -- rectangle
              0, 0, 0, 0,                         -- Left, Top, Right, Bottom
              ColourNameToRGB("blue"), miniwin.pen_null, 1,   -- no pen
              ColourNameToRGB("cyan"), "ui_tile")
	check(WindowDrawImage(bottom_panel, "border", 0, 0, 0, 10, miniwin.image_stretch))
	check(WindowDrawImage(bottom_panel, "separator", bar_width, 10, bar_width+10, 0, miniwin.image_stretch))
	check(WindowDrawImage(bottom_panel, "separator", (bar_width*2)+10, 10, (bar_width*2)+20, 0, miniwin.image_stretch))
	check(WindowDrawImage(minimap_win, "minimap_border", 0, 0, 0, 0, miniwin.image_transparent_copy))
	check(WindowDrawImage(score_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	check(WindowDrawImage(affect_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	check(WindowDrawImage(area_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	check(WindowDrawImage(score_win, "title_bar", 0, 0, 275, 25, miniwin.image_copy))
	check(WindowDrawImage(repair_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	check(WindowDrawImage(cancel_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	check(WindowDrawImage(affect_win, "title_bar", 0, 0, 275, 25, miniwin.image_copy))
	-- draw panes that aren't done so automatically through subnegotiation
	draw_area_list()
	draw_eq_window()
	
	-- Show windows
	WindowShow(background_win, true)
	WindowShow(left_panel, true)
	WindowShow(top_panel, true)
	WindowShow(logo_win, true)
	WindowShow(top_right_panel, true)
	WindowShow(info_panel, true)
	WindowShow(bottom_panel, true)
	WindowShow(minimap_win, true)
	WindowShow(health_win, true)
	WindowShow(mana_win, true)
	WindowShow(movement_win, true)
	WindowShow(opponent_win, true)
	WindowShow(affect_button, true)
	WindowShow(score_button, true)
	WindowShow(area_button, true)
	WindowShow(repair_button, true)
	
	if current_window ~= nil then
		WindowShow(current_window, true) -- redisplay the current window
	else
		WindowShow(score_win, true)
	end -- if
	
	if GetVariable("console") == "true" then
		-- periodically display console updates
		EnableTimer("update_console_timer", true)
	else end -- if
end -- function


function draw_time()
	if msdp["WORLD_TIME"] ~= nil then
		local width = outlined_text(colourGold, background_win, format_time(msdp["WORLD_TIME"]), 9, 0, 10, 0, bar_font)
		WindowRectOp(background_win, miniwin.rect_fill, 0, 0, 0, 50, colourBlack)
		outlined_text (colourGold, background_win, format_time(msdp["WORLD_TIME"]), 9, WindowInfo(background_win, 3)-width-10, 5, 0, bar_font)
	else end -- if
end -- function

function format_time(time_var)
	if tonumber(time_var) == 12 then
		return string.gsub(string.format("%.02f", time_var), "%.", ":") .. " PM"
	elseif tonumber(time_var) > 12 then
		time_var = time_var - 12
		return string.gsub(string.format("%.02f", time_var), "%.", ":") .. " PM"
	elseif tonumber(time_var) == 0 then
		return "12:00 AM"
	else
		return string.gsub(string.format("%.02f", time_var), "%.", ":") .. " AM"
	end -- if
	
end -- function

  -- fill the three energy bars
function draw_energy_bars()
	-- HEALTH
	current_health = msdp["HEALTH"]
	max_health = msdp["HEALTH_MAX"]
	-- initialise with empty bars
	if current_health == nil then
		current_health = 0
		max_health = 0
	elseif current_health ~= nil and max_health ~= nil then
		type = "hp"
		draw_energy_bar(type, colour, colour2, health_win, current_health, max_health, bar_width, bar_height)
	end -- if

	class = msdp["CLASS"]
	if class == "Vampire" then
		-- BLOOD
		current_blood = msdp["BLOOD"]
		max_blood = msdp["LEVEL"]

		-- initialise with empty bars
		if current_blood == nil then
			current_blood = 0
			max_blood = 0
		elseif current_blood ~= nil and max_blood ~= nil then
			type = "bp"
			colour = ColourNameToRGB("#CC3300")
			colour2 = ColourNameToRGB("#CC0000")
			draw_energy_bar(type, colour, colour2, mana_win, current_blood, max_blood+10, bar_width, bar_height)
		end -- if
	else -- they're not a vampire
		-- MANA
		current_mana = msdp["MANA"]
		max_mana = msdp["MANA_MAX"]

		-- initialise with empty bars
		if current_mana == nil then
			current_mana = 0
			max_mana = 0
		elseif current_mana ~= nil and max_mana ~= nil then
			type = "mp"
			colour = ColourNameToRGB("#00FFFF")
			colour2 = ColourNameToRGB("#0033FF")
			draw_energy_bar(type, colour, colour2, mana_win, current_mana, max_mana, bar_width, bar_height)
		end -- if
	end -- if

	-- MOVEMENT
	current_movement = msdp["MOVEMENT"]
	max_movement = msdp["MOVEMENT_MAX"]

	-- initialise with empty bars
	if current_movement == nil then
		current_movement = 0
		max_movement = 0
	elseif current_movement ~= nil and max_movement ~= nil then
		type = "mv"
		colour = ColourNameToRGB("#FFFF00")
		colour2 = ColourNameToRGB("#FF6600")
		draw_energy_bar(type, colour, colour2, movement_win, current_movement, max_movement, bar_width, bar_height)
	end -- if

	-- EXP
	local xp = msdp["EXPERIENCE"]
	local xp_tnl = msdp["EXPERIENCE_TNL"]

	local level = msdp["LEVEL"] or 50
	if tonumber(level) < 50 then
		-- initialise with empty bars
		if xp == nil then
			current_xp = 0
			max_xp = 0
		else
			current_xp = xp
			max_xp = xp + xp_tnl
		end -- if

		if xp ~= nil and xp_tnl ~= nil then
			type = "XP"
			colour = 0xCC00CC
			colour2 = 0x330033
			draw_energy_bar(type, colour, colour2, xp_win, current_xp, max_xp, 235, 15, type)
			local ticks_at = 235 / 4
			for i = 1, 5 do
				WindowLine (xp_win, i * ticks_at, 0, i * ticks_at, 15, colourDarkGray, 0, 1)
			end -- for
			if current_window == score_win or current_window == nil then
				WindowShow(xp_win, true)
			else end -- if
		else end -- if
	else
		WindowShow(xp_win, false)
	end -- if

	-- check to see if we should draw the enemy bar
	local opponent_name = msdp["OPPONENT_NAME"]
	if opponent_name ~= "" and opponent_name ~= nil then
		local opponent_health = msdp["OPPONENT_HEALTH"]
		type = "hp"
		WindowRectOp(logo_win, miniwin.rect_fill, 0, 0, 0, 0, colourBlack)
		WindowGradient (opponent_win, 0, 0, 0, 0, colourBlack, colourBlack, 1)
		draw_energy_bar(type, colourWhite, colourWhite, opponent_win, opponent_health, 100, opponent_width, 35, opponent_name)
		check(WindowDrawImage(logo_win, "rod_logo", 0, 0, 0, 0, miniwin.image_transparent_copy))
	else
		WindowGradient(opponent_win, 0, 0, 0, 0, colourBlack, colourBlack, 1)
		check(WindowDrawImage(logo_win, "rod_logo_full", 0, 0, 0, 0, miniwin.image_transparent_copy))
	end -- if
end -- draw_energy_bars


-- fill the bar
function draw_energy_bar (type, colour, colour2, window, current_value, max_value, width, height, xarg)
	-- empty part of bar colour
	local not_filled = ColourNameToRGB("#010101")
	local not_filled2 = ColourNameToRGB("#888888")

	-- convert the strings to numbers
	current = tonumber(current_value)
	max = tonumber(max_value)

	-- Calculate health
	if current < 0 then
		current = 0
	else end -- if

	-- calculate the filled part
	if max > 0 then
		filled = current * width / max
	else -- avoid division by zero
		filled = 0
	end -- if

	-- redraw the bars
	if current >= 0 then
		if type == "hp" then
			local health_pct = tonumber(string.format("%.2f", (current_value / max_value)))
			if health_pct <= 0 then
				-- do nothing
			elseif health_pct <= 0.10 then
				check(WindowDrawImage(window, "health_10", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.20 then
				check(WindowDrawImage(window, "health_20", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.30 then
				check(WindowDrawImage(window, "health_30", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.40 then
				check(WindowDrawImage(window, "health_40", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.50 then
				check(WindowDrawImage(window, "health_50", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.60 then
				check(WindowDrawImage(window, "health_60", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.70 then
				check(WindowDrawImage(window, "health_70", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.80 then
				check(WindowDrawImage(window, "health_80", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 0.90 then
				check(WindowDrawImage(window, "health_90", 0, 0, filled, height, miniwin.image_stretch))
			elseif health_pct <= 1 or health_pct > 1 then
				check(WindowDrawImage(window, "health_100", 0, 0, filled, height, miniwin.image_stretch))
			else end -- if
			WindowGradient (window, filled, 0, width, height, not_filled, not_filled2, 2) -- max 'non-filled' hp
		elseif type == "mp" then
			check(WindowDrawImage(window, "mana", 0, 0, filled, height, miniwin.image_stretch))
			WindowGradient (window, filled, 0, width, height, not_filled, not_filled2, 2) -- max 'non-filled' hp
		elseif type == "bp" then
			check(WindowDrawImage(window, "blood", 0, 0, filled, height, miniwin.image_stretch))
			WindowGradient (window, filled, 0, width, height, not_filled, not_filled2, 2) -- max 'non-filled' hp
		elseif type == "mv" then
			check(WindowDrawImage(window, "movement", 0, 0, filled, height, miniwin.image_stretch))
			WindowGradient (window, filled, 0, width, height, not_filled, not_filled2, 2) -- max 'non-filled' hp
		elseif type == "XP" then
			check(WindowDrawImage(window, "xp", 0, 0, filled, height, miniwin.image_stretch))
			WindowGradient (window, filled, 0, width, height, not_filled, not_filled2, 2) -- max 'non-filled' hp
		end -- if
	else end -- if

	if xarg == nil then -- this is not for an opponent / xp
		-- write the information inside the bar. we use current_value instead of current because health can be negative
		local text = table.concat({current_value, " / ", max, " ", type}, "")
		outlined_text (colourGold, window, text,8 ,0 ,6, bar_width, bar_font) -- values on the right
	else -- draw opponent or xp bar
		if type == "XP" then
			-- this is now handled in the draw_score section
		elseif type == "hp" then
			local formatted_name = table.concat({xarg, " (Lv. ", msdp["OPPONENT_LEVEL"], ")"}, "")
			local text = table.concat({(current/max)*100, "%"}, "")
			outlined_text (colourGold, window, formatted_name, 8, 10, 10, 0, bar_font)  -- draw text on the left side of the bar
			
			outlined_text (colourGold, window, text, 8, opponent_width-45, 10, 0, bar_font) -- values on the right
		else end -- if
	end
end -- draw_energy_bar

function outlined_text (colour, window, text, size, x, y, centre_width, font)
	local use_font = font or default_font
	outlineColour = colourDarkGray

	-- write the information inside
	WindowFont(window,'f',use_font,size,1,0,0,0)

	if centre_width > 0 then
		width = WindowTextWidth (window, 'f', text)
		x = x + ((centre_width-width) / 2)
	end -- if

	-- smear black text around the location to create an outline, so that it's clearer to read
	WindowText(window,'f',text,x+1,y+1,0,0,outlineColour,0)
	WindowText(window,'f',text,x+1,y,0,0,outlineColour,0)
	WindowText(window,'f',text,x+1,y-1,0,0,outlineColour,0)
	WindowText(window,'f',text,x,y+1,y,0,outlineColour,0)
	WindowText(window,'f',text,x,y-1,y,0,outlineColour,0)
	WindowText(window,'f',text,x-1,y+1,0,0,outlineColour,0)
	WindowText(window,'f',text,x-1,y,0,0,outlineColour,0)
	WindowText(window,'f',text,x-1,y-1,0,0,outlineColour,0)

	-- display the text
	width = WindowText(window,'f',text,x,y,0,0,colour,0)

	return width
end -- outlined_text

function draw_score()
	if msdp["CHARACTER_NAME"] == nil or msdp["LEVEL"] == nil or 
		msdp["RACE"] == nil or msdp["CLASS"] == nil then
		return
	end -- if
	if not load_once then
		load_once = true
		load_avatar_img(msdp["CHARACTER_NAME"], msdp["CLASS"])
	else end -- if
	
	outlined_text(colourGold, score_win, "Character Information", 10, 5, 5, 0)
	
	-- draw the background image
	check(WindowDrawImage (score_win, "page", 0, 28, right_panel_width-10, 0, miniwin.image_stretch))

	x_offset = (right_panel_width)/2 + 5
	check(WindowDrawImage(score_win, "avatar", 15, 93, 135, 257, miniwin.image_stretch)) -- portraits should be 120x164 or be stretched
	check(WindowDrawImageAlpha(score_win, "avatar_border", 15, 93, 135, 257, 1.0))	-- border around portrait image
	y_offset = 43
	text_length = outlined_text (colourGold, score_win, msdp["CHARACTER_NAME"], 12, 5, y_offset, right_panel_width)

	y_offset = y_offset + 22
	text_line = 'Level '..msdp["LEVEL"]..' '..msdp["RACE"]..' '..msdp["CLASS"]
	outlined_text (colourGold, score_win, text_line, 10, 5, y_offset, right_panel_width)

	y_offset = y_offset + 40
	outlined_text (colourGold, score_win, "STR:", 8, x_offset, y_offset+1, 0)
	if msdp["STR"] ~= nil and msdp["STR_PERM"] ~= nil then
		outlined_text (colourWhite, score_win, format_stat(msdp["STR"])..' ('..format_stat(msdp["STR_PERM"])..')', 9, x_offset+38, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "INT:", 8, x_offset, y_offset+1, 0)
	if msdp["INT"] ~= nil and msdp["INT_PERM"] ~= nil then
		outlined_text (colourWhite, score_win, format_stat(msdp["INT"])..' ('..format_stat(msdp["INT_PERM"])..')', 9, x_offset+38, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "WIS:", 8, x_offset, y_offset+1, 0)
	if msdp["WIS"] ~= nil and msdp["WIS_PERM"] ~= nil then
		outlined_text (colourWhite, score_win, format_stat(msdp["WIS"])..' ('..format_stat(msdp["WIS_PERM"])..')', 9, x_offset+38, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "DEX:", 8, x_offset, y_offset+1, 0)
	if msdp["DEX"] ~= nil and msdp["DEX_PERM"] ~= nil then
		outlined_text (colourWhite, score_win, format_stat(msdp["DEX"])..' ('..format_stat(msdp["DEX_PERM"])..')', 9, x_offset+38, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "CON:", 8, x_offset, y_offset+1, 0)
	if msdp["CON"] ~= nil and msdp["CON_PERM"] ~= nil then
		outlined_text (colourWhite, score_win, format_stat(msdp["CON"])..' ('..format_stat(msdp["CON_PERM"])..')', 9, x_offset+38, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "CHA:", 8, x_offset, y_offset+1, 0)
	if msdp["CHA"] ~= nil and msdp["CHA_PERM"] ~= nil then
		outlined_text (colourWhite, score_win, format_stat(msdp["CHA"])..' ('..format_stat(msdp["CHA_PERM"])..')', 9, x_offset+38, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "LCK:", 8, x_offset, y_offset+1, 0)
	if msdp["LCK"] ~= nil and msdp["LCK_PERM"] ~= nil then
		outlined_text (colourWhite, score_win, format_stat(msdp["LCK"])..' ('..format_stat(msdp["LCK_PERM"])..')', 9, x_offset+38, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 42
	outlined_text (colourGold, score_win, "Hitroll:", 9, 15, y_offset, 0)
	if msdp["HITROLL"] ~= nil then
		outlined_text (colourWhite, score_win, msdp["HITROLL"], 9, 70, y_offset, 0, fixed_width)
	end -- if

	outlined_text (colourGold, score_win, "Damroll:", 9, x_offset, y_offset, 0)
	if msdp["DAMROLL"] ~= nil then
		outlined_text (colourWhite, score_win, msdp["DAMROLL"], 9, 65+x_offset, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "Armor:", 9, x_offset, y_offset, 0)
	if msdp["AC"] ~= nil then
		outlined_text (colourWhite, score_win, msdp["AC"], 9, 65+x_offset, y_offset, 0, fixed_width)
	end -- if

	outlined_text (colourGold, score_win, "Align: ", 9, 15, y_offset, 0)
	if msdp["ALIGNMENT"] ~= nil then
		outlined_text (colourWhite, score_win, msdp["ALIGNMENT"], 9, 70, y_offset, 0, fixed_width)
	end -- if

	y_offset = y_offset + 20
	outlined_text (colourGold, score_win, "Gold: ", 9, 15, y_offset, 0)
	if msdp["MONEY"] ~= nil then
		outlined_text (colourWhite, score_win, format_gold(msdp["MONEY"]), 9, 70, y_offset, 0, fixed_width)
	end -- if
	
	-- write out the xp text below the bar
	if tonumber(msdp["LEVEL"]) < 50 then
		local xp = msdp["EXPERIENCE"]
		local tnl = xp + msdp["EXPERIENCE_TNL"]
		local text = table.concat({format_gold(xp), " / ", format_gold(tnl), " xp"}, "")
		outlined_text (colourGold, score_win, text, 9, 0 , 350, 265, fixed_width)
	else end -- if
end -- draw_score

function format_gold(str)
	local length = string.len(str)
	if length <= 3 then
		f_str = str
	elseif length <= 6 then
		f_str = string.gsub(str, "(%d+)(%d%d%d)", "%1,%2")
	elseif length <= 9 then
		f_str = string.gsub(str, "(%d+)(%d%d%d)(%d%d%d)", "%1,%2,%3")
	elseif length <= 12 then
		f_str = string.gsub(str, "(%d+)(%d%d%d)(%d%d%d)(%d%d%d)", "%1,%2,%3,%4")
	end
	return f_str
end -- function

function format_stat(str)
	return string.format("%2s", str)
end -- function

-- attempt to load an avatar image for this character
-- avatar by name is highest priority, then by class and finally the default 'unknown' avatar
function load_avatar_img(name, class)
	local char_name = string.lower(name)
	local char_class = string.lower(class)
	if WindowLoadImage(score_win, "avatar", asset_path .. "portrait//characters//" .. char_name .. ".png") ~= eOK then
		if WindowLoadImage(score_win, "avatar", asset_path .. "portrait//classes//" .. char_class .. ".png") ~= eOK then
			check(WindowLoadImage(score_win, "avatar", asset_path .. "portrait//unknown.png"))
		else end -- if
	else end -- if
end -- function

function update_affects(data)
	local index = 0
	local startpos = 1
	local max = 0
	for i=1,string.len(data),1 do
		if string.byte(data,i) == 7 or i == string.len(data) then
			if string.byte(data,i) == 7 then
				endpos = 1
			else
				endpos = 0
			end -- if
			variable = string.sub(data,startpos,i-endpos)
			startpos = i+1
			pos1 = string.find(variable, ",")
			if pos1 ~= nil then
				index = index + 1
				local aff_name = string.sub(variable, 1, pos1-1)
				local aff_duration = string.sub(variable, pos1+1)

				if affects[index] ~= nil and affects[index].name == aff_name then
					affects[index].duration = aff_duration
				else
					local aff_type = 0
					if table.binsearch(i_affects, aff_name) ~= nil then
						aff_type = 1
					elseif table.binsearch(spelldowns, aff_name) ~= nil then
						aff_type = 2
					end -- if
					-- affects are stored inside the affects table, as (name, duration, type)
					affects[index] = {name=aff_name, 
										duration=aff_duration,
										type=aff_type}
				end -- if
			else end -- if
		end -- if
	end -- for
	-- discard affects that have expired but still exist in the table
	for i=index,#affects,1 do
		if affects[i+1] ~= nil then
			affects[i+1] = nil
		else
			break
		end -- if
	end -- for
	affect_scroll_bottom_max = (#affects * -21) + (bottom-210-84)	-- needs to change depending on the affect view
end -- function

function draw_affects()
	local aff_str = msdp["AFFECTS"]
	if not aff_str then return else end	-- don't bother if msdp isn't initialized
	update_affects(aff_str) -- update affects to the latest information from the mud
	padding = 10			
	-- draw the background image (clears the screen as well)
	check(WindowDrawImage (affect_win, "scroll", 0, 28, right_panel_width-10, screen_height-210, miniwin.image_stretch))
	if alt_affects_view == true then
		check(WindowDrawImage(affect_win, "eye_on", 190, 0, 0, 0, miniwin.image_copy))
	else
		check(WindowDrawImage(affect_win, "eye", 190, 0, 0, 0, miniwin.image_copy))
	end -- if
	if affect_scroll < 0 then
		check(WindowDrawImage(affect_win, "arrow_up", 215, 0, 0, 0, miniwin.image_transparent_copy))
	else
		check(WindowDrawImage(affect_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_transparent_copy))
	end -- if
	if affect_scroll > affect_scroll_bottom_max then
		check(WindowDrawImage(affect_win, "arrow_down", 240, 0, 0, 0, miniwin.image_transparent_copy))
	else
		check(WindowDrawImage(affect_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_transparent_copy))
	end -- if
	outlined_text(colourGold, affect_win, "Spell Affects", 10, 5, 5, 0)
	
	-- sort spell affects by shortest duration, so they are displayed at the top (do this no matter what the sort is)
	local sorted_affects = copy_table(affects)
	table.sort(sorted_affects, function(a,b) return tonumber(a.duration) < tonumber(b.duration) end)
	
	local y_offset
	local count = 0	-- need to subtract number of spells drawn up here from the area bottom scroll max
	if alt_affects_view == true then
		y_offset = 79
		for k,v in ipairs(sorted_affects) do
			if v.type == 1 then	-- if the affect is "important"
				sorted_affects[k] = nil
				draw_affect_line(v, y_offset)
				y_offset = y_offset + 21
				count = count + 1
			else end --if
		end -- for
		affect_scroll_bottom_max = (#affects * -21) + (bottom-210-84) -- - (21 * count) -- adapt bottom scroll
	else end -- if

	if not alt_affects_view then
		y_offset = 79 + affect_scroll	-- normal behaviour
	else
		y_offset = y_offset + affect_scroll -- include the y_offset generated by the priority spells
	end -- if
	for _,v in pairs(sorted_affects) do
		if y_offset >= (79+(21*count)) and y_offset <= bottom-162-84 then -- don't show spells that are outside our desired area
			draw_affect_line(v, y_offset)
		 else end -- if
		y_offset = y_offset + 21
	end -- for
	
	if #affects == 0 and count == 0 then
		outlined_text(colourGold, affect_win, "You are not affected by any spells.", 9, 0, WindowInfo(affect_win, 4)/2, right_panel_width-10)
	end -- if
end -- function

function draw_affect_line(t_val, y_offset)
	local duration = table.concat({"( ", string.format("%4s", t_val.duration), " )"}, "")
	local spell_name_color
	local spell_name_font
	if tonumber(t_val.duration) <= timer_warning and tonumber(t_val.duration) > timer_critical then
		spell_name_color = "gray"
		spell_name_font = warning_font
	elseif tonumber(t_val.duration) <= timer_critical then
		spell_name_color = "red"
		spell_name_font = critical_font
	else
		spell_name_color = "white"
		spell_name_font = default_font
	end -- if
	
	if t_val.type == 1 and alt_affects_view == true then	-- affect is important
		outlined_text(colourGold, affect_win, "*", 9, padding+10, y_offset+4, 0, fixed_width)
	else end -- if
	
	outlined_text(colourGold, affect_win, duration, 9, padding+25, y_offset+3.5, 0, fixed_width) -- padding+180
	
	if t_val.type == 2 then -- affect is a spelldown
		outlined_text(ColourNameToRGB("#FF00FF"), affect_win, trunc(t_val.name, 20), 9, padding+85, y_offset+4, 0)
	else
		outlined_text(ColourNameToRGB(spell_name_color), affect_win, trunc(t_val.name, 20), 9, padding+85, y_offset+4, 0)
	end -- if
end -- function

function init_rooms(data)
	index = 0
	startpos = 1
	max = 0
	for i=1,string.len(data),1 do
		if string.byte(data,i) == 7 or i == string.len(data) then
			if string.byte(data,i) == 7 then
				endpos = 1
			else
				endpos = 0
			end -- if
			variable = string.sub(data,startpos,i-endpos)
			startpos = i+1
			index = index + 1

			pos1 = string.find(variable, ",")
			if pos1 ~= nil then
				RoomExit[index] = string.sub(variable, 1, pos1-1)
				RoomType[index] = string.sub(variable, pos1+1)
				ExitCount = ExitCount + 1
			end -- if
		end -- if
	end -- for
end -- function


-- draw one room
function draw_room(x, y, type, in_room)
	terrain_image = "terrain_dark"
	if type == "O" then	-- the door is open or there is no door
		terrain_image = "terrain_city"
	end -- if

	if in_room then
		WindowCircleOp(minimap_win, 2, x-1, y-1, x+22, y+22, colourGreen, 0, 2, 0, 1)
	else
		WindowCircleOp(minimap_win, 2, x-1, y-1, x+22, y+22, colourGold, 0, 2, 0, 1)
	end -- if
	WindowCircleOp(minimap_win, 2, x-1, y-1, x+21, y+21, colourDarkGray, 0, 1, 0, 1)
	WindowDrawImage(minimap_win, terrain_image, x, y, x+20, y+20, 1)  -- draw the terrain
end -- draw_room


-- draw the minimap
function draw_minimap()
	data = msdp["ROOM_EXITS"]
	RoomExit = {}
	RoomType = {}
	ExitCount = 0
	local isUpDown = false
	if data ~= nil then
		init_rooms(data)
	end -- if
	
	mapCentre = 64
	-- clear the previous rooms
	WindowCircleOp (minimap_win, 1, 12, 12, 138, 138, 
                colourDarkGray, 0, 0,  -- no pen
                colourDarkGray, 0,  -- brush
                15, 15)
	local room_name = msdp["ROOM_NAME"]
	local area_name = msdp["AREA_NAME"]
	if area_name ~= nil and room_name ~= nil then
		-- clear the previous area/room name and redraw the current ones
		WindowRectOp(top_right_panel, miniwin.rect_fill, 11, 0, 0, 200, colourBlack)
		outlined_text(colourGold, top_right_panel, trunc(room_name,35), 9, 0, 5, right_panel_width)
		outlined_text(colourGold, top_right_panel, trunc(area_name,35), 9, 0, 180, right_panel_width)
	else end -- if

	-- draw any surrounding rooms
	if ExitCount > 0 then
		for i=1,ExitCount,1 do
			if RoomExit[i] == "north" then
				WindowLine(minimap_win, mapCentre+10, mapCentre-2, mapCentre+10, mapCentre-45, colourGold, 0, 1)
				draw_room(mapCentre, mapCentre-45, RoomType[i])
			elseif RoomExit[i] == "south" then
				WindowLine(minimap_win, mapCentre+10, mapCentre+18, mapCentre+10, mapCentre+43, colourGold, 0, 1)
				draw_room(mapCentre, mapCentre+45, RoomType[i])
			elseif RoomExit[i] == "east" then
				WindowLine(minimap_win, mapCentre+22, mapCentre+9, mapCentre+43, mapCentre+9, colourGold, 0, 1)
				draw_room(mapCentre+45, mapCentre, RoomType[i])
			elseif RoomExit[i] == "west" then
				WindowLine(minimap_win, mapCentre-3, mapCentre+9, mapCentre-25, mapCentre+9, colourGold, 0, 1)
				draw_room(mapCentre-45, mapCentre, RoomType[i])
			elseif RoomExit[i] == "northeast" then
				WindowLine(minimap_win, mapCentre+22, mapCentre-3, mapCentre+28, mapCentre-9, colourGold, 0, 1)
				draw_room(mapCentre+30, mapCentre-30, RoomType[i])
			elseif RoomExit[i] == "southeast" then
				WindowLine(minimap_win, mapCentre+22, mapCentre+22, mapCentre+28, mapCentre+28, colourGold, 0, 1)
				draw_room(mapCentre+30, mapCentre+30, RoomType[i])
			elseif RoomExit[i] == "northwest" then
				WindowLine(minimap_win, mapCentre-3, mapCentre-3, mapCentre-9, mapCentre-9, colourGold, 0, 1)
				draw_room(mapCentre-30, mapCentre-30, RoomType[i])
			elseif RoomExit[i] == "southwest" then
				WindowLine(minimap_win, mapCentre-3, mapCentre+22, mapCentre-9, mapCentre+28, colourGold, 0, 1)
				draw_room(mapCentre-30, mapCentre+30, RoomType[i])
			elseif RoomExit[i] == "up" then
				isUpDown = true
			elseif RoomExit[i] == "down" then
				isUpDown = true
			end -- if
		end -- for
	end -- if
	
	-- draw the current room (where the player is)
	draw_room (mapCentre, mapCentre, "O", true)
	if isUpDown == true then
		outlined_text(colourWhite, minimap_win, "*", 13, mapCentre+6, mapCentre+3, 0)
	else end -- if
end -- draw_minimap

function init_area_list()
	area_list = {}
	local index = 1
	for k,v in ipairs(GetAliasList()) do
		_, alname, almatch = GetAlias(v)
		-- check to see if alias a direction alias
		local alias_group = GetAliasInfo(alname, 16)
		if alias_group ~= nil then
			if string.find(alias_group, "directions") ~= nil then
				local lrange = split(alias_group, "_")[1]
				if lrange == nil then
					lrange = "0t65"	-- default range (all)
					Note("Found area without a recommended level range. Using default setting.")
				else end --if
				area_list[index] = table.concat({alname, almatch, lrange}, ":")
				index = index + 1
			else end -- if
		else end -- if
	end -- for
	table.sort(area_list)	-- order areas descending alphabetically
	--area_scroll_bottom_max = (#area_list * -20) + (bottom-200)	-- set the max bottom scroll limit
	draw_area_list()
end -- if

function draw_area_list()
	if msdp["LEVEL"] == nil and level == nil then return else end
	areas_loaded = true
	check(WindowDrawImage(area_win, "title_bar", 0, 0, 275, 25, miniwin.image_copy))
	WindowDeleteAllHotspots(area_win)	-- need to do this so the filter is accurate
	area_modifier = 0
	WindowAddHotspot(area_win, "filter",  
			 185,
			 0,
			 210,
			 25,
			 "mouseover",				-- mouseover 
			 "cancelmouseover", 		-- cancelmouseover
			 "mousedown",				-- mousedown
			 "cancelmousedown", 		-- cancelmousedown
			 "mouseup", 				-- mouseup
			 "Area search",				-- tooltip text
			 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	WindowAddHotspot(area_win, "area_scroll_up",  
			 210,
			 0,
			 235,
			 25,  
			 "mouseover",				-- mouseover 
			 "cancelmouseover", 		-- cancelmouseover
			 "mousedown",				-- mousedown
			 "cancelmousedown", 		-- cancelmousedown
			 "mouseup", 				-- mouseup
			 "",						-- tooltip text
			 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	WindowAddHotspot(area_win, "area_scroll_down",  
                 235,
				 0,
				 260,
				 25,
                 "mouseover",				-- mouseover 
                 "cancelmouseover", 		-- cancelmouseover
                 "mousedown",				-- mousedown
                 "cancelmousedown", 		-- cancelmousedown
                 "mouseup", 				-- mouseup
                 "",						-- tooltip text
                 miniwin.cursor_hand, 0)  	-- hand cursor
				 
	-- we add a scrollwheel handler to this hotspot
	WindowAddHotspot(area_win, "area_scrollwheel",  
                 0,
				 30,
				 right_panel_width,
				 screen_height - 210,			-- rectangle
                 "",				-- mouseover 
                 "", 		-- cancelmouseover
                 "",				-- mousedown
                 "", 		-- cancelmousedown
                 "", 				-- mouseup
                 "",						-- tooltip text
                 miniwin.cursor_ns_arrow, 0)  	-- hand cursor
	WindowScrollwheelHandler(area_win, "area_scrollwheel", "scrollwheel")
	
	check(WindowDrawImage (area_win, "map", -2, 28, right_panel_width-10, screen_height-210, miniwin.image_stretch))
	if filter_text ~= nil then
		check(WindowDrawImage(area_win, "filter_cancel", 190, 0, 0, 0, miniwin.image_transparent_copy))
	else
		check(WindowDrawImage(area_win, "filter", 190, 0, 0, 0, miniwin.image_transparent_copy))
	end -- if
	
	local y_offset = 35 + area_scroll
	local filtered_areas = 0
	for _, v in ipairs(area_list) do
		if y_offset >= 35 and y_offset <= bottom-200 then	-- the first comparison should be the same as the initial y_offset (35)
			local parts = split(v, ":")
			local alias_name = parts[0]
			local area_name = decode(alias_name)
			local directions = parts[1]
			local lrange = parts[2]
			
			if filter_text ~= nil then
				if string.find(string.lower(area_name), string.lower(filter_text)) ~= nil then
					y_offset = print_area_line(alias_name, area_name, y_offset, lrange)
					filtered_areas = filtered_areas + 1
				else end -- if
			else
				y_offset = print_area_line(alias_name, area_name, y_offset, lrange)
			end -- if
		else
			y_offset = y_offset + 20
		end -- if
	end -- for
	if filter_text ~= nil then
		outlined_text(colourGold, area_win, string.format("Area List (%d)", filtered_areas - area_modifier), 10, 5, 5, 0)
	else
		outlined_text(colourGold, area_win, string.format("Area List (%d)", #area_list - area_modifier), 10, 5, 5, 0)
	end -- if
	if filter_text ~= nil then
		area_scroll_bottom_max = ((filtered_areas-area_modifier) * -20) + (bottom-220)
		if filtered_areas == 0 then
			outlined_text(colourGold, area_win, "No areas match that criteria.", 10, 0, WindowInfo(area_win, 4)/2, right_panel_width-10)
		else end -- if
	else
		area_scroll_bottom_max = ((#area_list-area_modifier) * -20) + (bottom-220)
	end -- if
	if area_scroll < 0 then
		check(WindowDrawImage(area_win, "arrow_up", 215, 0, 0, 0, miniwin.image_transparent_copy))
	else
		check(WindowDrawImage(area_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_transparent_copy))
	end -- if
	if area_scroll > area_scroll_bottom_max then
		check(WindowDrawImage(area_win, "arrow_down", 240, 0, 0, 0, miniwin.image_transparent_copy))
	else
		check(WindowDrawImage(area_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_transparent_copy))
	end -- if
end -- function

function print_area_line(alias_name, area_name, y_offset, lrange)
	local range = split(lrange, "t")	-- t is the separator character (conforms to naming standards)
	local width
	if level == nil then
		level = msdp["LEVEL"]
	else end -- if
	if (tonumber(range[0]) - level) > 10 then
		-- if GetVariable("newbie") == "true" then	-- don't show areas out of the player's level range if configured
			--area_modifier = area_modifier + 1
			-- return y_offset
		-- else
			width = outlined_text(colourRed, area_win, trunc(area_name,35), 10, 10, y_offset, 0)
		--end -- if
	elseif (tonumber(range[0]) - level) > 5 then
		width = outlined_text(colourOrange, area_win, trunc(area_name,35), 10, 10, y_offset, 0)
	else
		width = outlined_text(colourWhite, area_win, trunc(area_name,35), 10, 10, y_offset, 0)
	end -- if
	local tooltip_text = string.format("Recommended Level Range: %s - %s", range[0], range[1])
	WindowAddHotspot(area_win, alias_name,
					 10,
					 y_offset,
					 width+10,
					 y_offset+16,				-- rectangle
					 "",						-- mouseover 
					 "", 						-- cancelmouseover
					 "",						-- mousedown
					 "", 						-- cancelmousedown
					 "goto_area", 				-- mouseup
					 tooltip_text,				-- tooltip text
					 miniwin.cursor_hand, 0)  	-- hand cursor
	return y_offset + 20
end -- function

-- Updated by Alex to remove dependence on the Repeat_Command plugin / stacking character
function goto_area(flags, hotspot_id)
	_, alname, almatch  = GetAlias(hotspot_id)
	if msdp["ROOM_NAME"] == START_ROOM then
		table.insert(console_log, "> Speedwalking to: " .. trunc(decode(alname) .. ".", 20, "~"))
		ColourNote("white", "", "\nYou start out on your journey to ",
					"#00ff00", "", decode(alname),
					"white", "", ".\n")
		WindowShow(cancel_button, true)
		showing_cancel = true
		SetVariable("old_delay", GetOption("speed_walk_delay"))	-- store the user's current setting
		SetOption("speed_walk_delay", 550)		-- so that speedwalk is treated like a queue and not send immediate
		Queue(EvaluateSpeedwalk(almatch), false)
		AddTimer("are_we_there_yet", 0, 0, 1, "", timer_flag.Enabled, "hide_cancel")
	else
		if GetVariable("newbie") == "true" then
			ColourNote("white", "", "\nA voice whispers, 'You should start your journey at Darkhaven Square.'\n")
		else
			ColourNote("white", "", "\nYou walk about in circles as the directions don't make any sense!\n")
		end -- if
	end -- if
end -- function

function hide_cancel()
	if GetQueue() == nil then
		DeleteTimer("are_we_there_yet")
		WindowShow(cancel_button, false)
		showing_cancel = false
		SetOption("speed_walk_delay", tonumber(GetVariable("old_delay")))	-- restore the user's old setting
	else end -- if
end -- function

function draw_eq_window()
	check(WindowDrawImage(eq_win, "title_bar", 0, 0, 275, 25, miniwin.image_copy))
	outlined_text(colourGold, eq_win, "Equipment", 10, 5, 5, 0)
	check(WindowDrawImage(eq_win, "bg", 0, 28, right_panel_width-10, 0, miniwin.image_stretch))
	sorted_damaged_eq = {}
	for k,v in pairs(eq) do
		table.insert(sorted_damaged_eq, v)
	end -- for
	table.sort(sorted_damaged_eq, function(a,b) return a.hits > b.hits end)
	repair_scroll_bottom_max = (#sorted_damaged_eq * -20) + (bottom-190)
	if repair_scroll < 0 then
		check(WindowDrawImage(eq_win, "arrow_up", 215, 0, 0, 0, miniwin.image_copy))
	else
		check(WindowDrawImage(eq_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
	end -- if
	if repair_scroll > repair_scroll_bottom_max then
		check(WindowDrawImage(eq_win, "arrow_down", 240, 0, 0, 0, miniwin.image_copy))
	else
		check(WindowDrawImage(eq_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
	end -- if
	if #sorted_damaged_eq == 0 then
		check(WindowDrawImage(eq_win, "hammer_hover", 190, 0, 0, 0, miniwin.image_copy))
	else
		check(WindowDrawImage(eq_win, "hammer", 190, 0, 0, 0, miniwin.image_copy))
	end -- if
	check(WindowDrawImage(eq_win, "eqscan", 165, 0, 0, 0, miniwin.image_copy))
	
	y_offset = 30 + repair_scroll
	for _,v in ipairs(sorted_damaged_eq) do
		if y_offset >= 30 and y_offset <= bottom-190 then
			outlined_text(colourGold, eq_win, table.concat({"<", v.hits, 
			"/", v.max_hits, ">"}, ""), 8, 10, y_offset, 0, fixed_width)
			local width
			if tonumber(v.max_hits) ~= nil then
				if tonumber(v.max_hits) - tonumber(v.hits) <= 0 then
					width = outlined_text(colourGreen, eq_win, trunc(v.name, 25), 8, 65, y_offset, 0)
				elseif tonumber(v.max_hits) - tonumber(v.hits) <= 3 and v.eq_type ~= "light" then
					width = outlined_text(colourRed, eq_win, trunc(v.name, 25), 8, 65, y_offset, 0)
				else
					width = outlined_text(colourWhite, eq_win, trunc(v.name, 30), 8, 65, y_offset, 0)
				end -- if
			else
				width = outlined_text(colourWhite, eq_win, trunc(v.name, 30), 8, 65, y_offset, 0)
			end -- if
		else end -- if
		
		WindowAddHotspot(eq_win, "eqwin:" .. encode(v.name),
							65,
							y_offset,
							65+width,
							y_offset+13,
							"",							-- mouseover 
							"", 						-- cancelmouseover
							"",							-- mousedown
							"", 						-- cancelmousedown
							"mouseup", 					-- mouseup
							"Set MaxAC for: " .. v.name,-- tooltip text
							miniwin.cursor_hand, 0)  	-- hand cursor)
		
		y_offset = y_offset + 20
	end -- for
	
	if #sorted_damaged_eq == 0 then
		outlined_text(colourGold, eq_win, "Click on the 'gears' icon.", 9, 0, WindowInfo(eq_win, 4)/2, right_panel_width-10)
	end -- if
end -- function

function draw_repair_totals()
	local text = table.concat({"You spent ", format_gold(repair_total), " gold coins repairing your equipment."}, "")
	local text2 = table.concat({"You need an additional ", format_gold(repair_needed), " gold coins to repair the rest of your equipment."}, "")
		ColourNote("gold", "", text)
		ColourNote("gray", "", text2)
end -- function

-- mouse event handlers
function mousedown(flags, hotspot_id)
	if hotspot_id == "score" then
		check(WindowDrawImage(score_button, "button_pressed", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "affects" then
		check(WindowDrawImage(affect_button, "button_pressed", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "area" then
		check(WindowDrawImage(area_button, "button_pressed", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "repair" then
		check(WindowDrawImage(repair_button, "button_pressed", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "cancel" then
		check(WindowDrawImage(cancel_button, "button_pressed", 0, 0, 0, 0, miniwin.image_copy))
	end
	Redraw()
end -- function

function mouseup(flags, hotspot_id)
	if hotspot_id == "score" then
		hide_info_windows()
		check(WindowDrawImage(score_button, "button", 0, 0, 0, 0, miniwin.image_copy))
		current_window = score_win
		WindowShow (score_win, true)
		WindowShow(xp_win, true)
	elseif hotspot_id == "affects" then
		hide_info_windows()
		check(WindowDrawImage(affect_button, "button", 0, 0, 0, 0, miniwin.image_copy))
		current_window = affect_win
		WindowShow(affect_win, true)
	elseif hotspot_id == "area" then
		hide_info_windows()
		check(WindowDrawImage(area_button, "button", 0, 0, 0, 0, miniwin.image_copy))
		current_window = area_win
		draw_area_list()
		WindowShow(area_win, true)
	elseif hotspot_id == "repair" then
		hide_info_windows()
		check(WindowDrawImage(repair_button, "button", 0, 0, 0, 0, miniwin.image_copy))
		current_window = eq_win
		WindowShow(eq_win, true)
	elseif hotspot_id == "change_affect_view" then
		if alt_affects_view then
			alt_affects_view = false
		else
			alt_affects_view = true
		end -- if
		draw_affects()
	elseif hotspot_id == "affect_scroll_down" then
		if affect_scroll > affect_scroll_bottom_max then
			affect_scroll = affect_scroll - 21
		else end -- if
		draw_affects()
	elseif hotspot_id == "affect_scroll_up" then
		if affect_scroll < 0 then
			affect_scroll = affect_scroll + 21
		else end -- if
		draw_affects()
	elseif hotspot_id == "area_scroll_down" then
		if area_scroll > area_scroll_bottom_max then
			area_scroll = area_scroll - 20
			draw_area_list()
		else end -- if
	elseif hotspot_id == "area_scroll_up" then
		if area_scroll < 0 then
			area_scroll = area_scroll + 20
			draw_area_list()
		else end -- if
	elseif hotspot_id == "repair_scroll_down" then
		if repair_scroll > repair_scroll_bottom_max then
			repair_scroll = repair_scroll - 20
		else end -- if
		draw_eq_window()
	elseif hotspot_id == "repair_scroll_up" then
		if repair_scroll < 0 then
			repair_scroll = repair_scroll + 20
		else end -- if
		draw_eq_window()
	elseif hotspot_id == "scan_eq" then
		Execute("ui.eqscan")
	elseif hotspot_id == "repair_eq" then
		if sorted_damaged_eq ~= nil then
			repair_total = 0
			repair_needed = 0
			Execute("remove all")
			Execute("repair all")
			Execute("wear all")
			DoAfterSpecial(2, "ui.eqscan", sendto.execute)
			DoAfterSpecial(3, "draw_repair_totals()", sendto.script)
		else end -- if
	elseif hotspot_id == "filter" then
		if filter_text == nil then
			filter_text = utils.inputbox("Search for areas containing:",   	-- prompt
										  "Area Search",   					-- window title
										  "",   							-- default answer
										  default_font, 10,					-- font
										  {box_width = 180,
										  box_height = 125, 
										  prompt_width = 170,
										  prompt_height = 15,
										  reply_width = 150,
										  reply_height = 20,
										  max_length = 40})
			if filter_text ~= nil then
				draw_area_list()
			else end -- if
		else
			filter_text = nil
			draw_area_list()
		end -- if
	elseif hotspot_id == "cancel" then
		DiscardQueue()
		hide_cancel()
		check(WindowDrawImage(cancel_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	elseif string.find(hotspot_id, "eqwin") ~= nil then
		local item_name = decode(split(hotspot_id, ":")[1])
		local item_ac = utils.inputbox(item_name,   			-- prompt
										  "Set MaxAC",   		-- window title
										  "",   				-- default answer
										  bar_font, 10,			-- font
										  {box_width = 180,
										  box_height = 125, 
										  prompt_width = 190,
										  prompt_height = 15,
										  reply_width = 150,
										  reply_height = 20,
										  max_length = 40})
		if item_ac ~= nil then
			if tonumber(item_ac) ~= nil then
				eq[item_name].max_hits = tonumber(item_ac)
				SetVariable(encode(eq[item_name].name), eq[item_name].max_hits)
				draw_eq_window()
			else
				ColourNote("red", "", "MaxAC must be a number or blank.")
			end -- if
		else end -- if
	end -- if
end -- function

function mouseover(flags, hotspot_id)
	if hotspot_id == "score" then
		check(WindowDrawImage(score_button, "button_hover", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "affects" then
		check(WindowDrawImage(affect_button, "button_hover", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "change_affect_view" then
		if alt_affects_view == true then
			check(WindowDrawImage(affect_win, "eye_on_hover", 190, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(affect_win, "eye_hover", 190, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "affect_scroll_up" then
		if affect_scroll == 0 then
			check(WindowDrawImage(affect_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(affect_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "affect_scroll_down" then
		if affect_scroll == affect_bottom_scroll_max then
			check(WindowDrawImage(affect_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(affect_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "area" then
		check(WindowDrawImage(area_button, "button_hover", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "filter" then
		if filter_text ~= nil then
			check(WindowDrawImage(area_win, "filter_cancel_hover", 190, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(area_win, "filter_hover", 190, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "area_scroll_up" then
		check(WindowDrawImage(area_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "area_scroll_down" then
		check(WindowDrawImage(area_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "repair" then
		check(WindowDrawImage(repair_button, "button_hover", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "repair_scroll_up" then
		check(WindowDrawImage(eq_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "repair_scroll_down" then
		check(WindowDrawImage(eq_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "repair_eq" then
		check(WindowDrawImage(eq_win, "hammer_hover", 190, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "scan_eq" then
		check(WindowDrawImage(eq_win, "eqscan_hover", 165, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "cancel" then
		check(WindowDrawImage(cancel_button, "button_hover", 0, 0, 0, 0, miniwin.image_copy))
	end
	Redraw()
end -- function

function cancelmouseover(flags, hotspot_id)
	if hotspot_id == "score" then
		check(WindowDrawImage(score_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "affects" then
		check(WindowDrawImage(affect_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "change_affect_view" then
		if alt_affects_view == true then
			check(WindowDrawImage(affect_win, "eye_on", 190, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(affect_win, "eye", 190, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "affect_scroll_up" then
		if affect_scroll == 0 then
			check(WindowDrawImage(affect_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(affect_win, "arrow_up", 215, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "affect_scroll_down" then
		if affect_scroll > affect_scroll_bottom_max then
			check(WindowDrawImage(affect_win, "arrow_down", 240, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(affect_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "area" then
		check(WindowDrawImage(area_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "filter" then
		if filter_text ~= nil then
			check(WindowDrawImage(area_win, "filter_cancel", 190, 0, 0, 0, miniwin.image_copy))
			draw_area_list()
		else
			check(WindowDrawImage(area_win, "filter", 190, 0, 0, 0, miniwin.image_copy))
			draw_area_list()
		end -- if
	elseif hotspot_id == "area_scroll_up" then
		if area_scroll == 0 then
			check(WindowDrawImage(area_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(area_win, "arrow_up", 215, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "area_scroll_down" then
		if area_scroll > area_scroll_bottom_max then
			check(WindowDrawImage(area_win, "arrow_down", 240, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(area_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
		end
	elseif hotspot_id == "repair" then
		check(WindowDrawImage(repair_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "repair_scroll_up" then
		if repair_scroll == 0 then
			check(WindowDrawImage(eq_win, "arrow_up_hover", 215, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(eq_win, "arrow_up", 215, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "repair_scroll_down" then
		if repair_scroll > repair_scroll_bottom_max then
			check(WindowDrawImage(eq_win, "arrow_down", 240, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(eq_win, "arrow_down_hover", 240, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "repair_eq" then
		if sorted_damaged_eq ~= nil then
			check(WindowDrawImage(eq_win, "hammer", 190, 0, 0, 0, miniwin.image_copy))
		else
			check(WindowDrawImage(eq_win, "hammer_hover", 190, 0, 0, 0, miniwin.image_copy))
		end -- if
	elseif hotspot_id == "scan_eq" then
		check(WindowDrawImage(eq_win, "eqscan", 165, 0, 0, 0, miniwin.image_copy))
	elseif hotspot_id == "cancel" then
		check(WindowDrawImage(cancel_button, "button", 0, 0, 0, 0, miniwin.image_copy))
	end
	Redraw()
end -- function

function scrollwheel(flags, hotspot_id)
	if bit.band(flags, 0x100) ~= 0 then
		if hotspot_id == "affect_scrollwheel" then
			if affect_scroll > affect_scroll_bottom_max then
				affect_scroll = affect_scroll - 21
				draw_affects()
				WindowShow(affect_win, true)
			else end -- if
		elseif hotspot_id == "area_scrollwheel" then
			if area_scroll > area_scroll_bottom_max then
				area_scroll = area_scroll - 20
				draw_area_list()
				WindowShow(area_win, true)
			else end -- if
		elseif hotspot_id == "zeq_scrollwheel" then
			if repair_scroll > repair_scroll_bottom_max then
				repair_scroll = repair_scroll - 20
				draw_eq_window()
				WindowShow(eq_win, true)
			else end -- if
		end -- if
	else
		if hotspot_id == "affect_scrollwheel" then
			if affect_scroll < 0 then
				affect_scroll = affect_scroll + 21
				draw_affects()
				WindowShow(affect_win, true)
			else end -- if
		elseif hotspot_id == "area_scrollwheel" then
			if area_scroll < 0 then
				area_scroll = area_scroll + 20
				draw_area_list()
				WindowShow(area_win, true)
			else end -- if
		elseif hotspot_id == "zeq_scrollwheel" then
			if repair_scroll < 0 then
				repair_scroll = repair_scroll + 20
				draw_eq_window()
				WindowShow(eq_win, true)
			else end -- if
		end -- if
	end -- if
end -- function

function hide_info_windows()
	for _, v in ipairs(info_windows) do
		WindowShow(v, false)
	end -- for
	affect_scroll = 0
	area_scroll = 0
	repair_scroll = 0
end -- function

function StoreVariable(MSDP_var, MSDP_val)
	if MSDP_var == "SERVER_ID" then
		SendPkt ("\255\250\69\1PLUGIN_ID\2Official Realms of Despair UI Plugin\255\240")
	else -- store the variable
		msdp[MSDP_var] = MSDP_val
	end -- if
end -- function StoreVariable

------------------------
-- Trigger Functions
------------------------

function update_damaged_eq(name, _, wildcards)
	if name == "eqDamaged" then
		if eq[wildcards[1]] ~= nil then
			eq[wildcards[1]].hits = eq[wildcards[1]].hits + 1
		else
			if GetVariable("warnings") == "true" then
				ColourNote("yellow", "black", "This piece of equipment has not been configured yet. Wear it and type 'ui.eqscan'.")
			else end -- if
		end -- if
	elseif name == "eqRepair" then
		-- on equipment repair, gold amount for repair = wildcards[1], item = wildcards[2]
		if eq[wildcards[2]] ~= nil then
			eq[wildcards[2]].hits = 0
			repair_total = repair_total + tonumber(wildcards[1])
		else
			if GetVariable("warnings") == "true" then
				ColourNote("red", "", "Warning: This item not included in repair count. (not set)")
			else end -- if
		end -- if
	elseif name == "eqScrap" then
		-- when a piece of equipment scraps, the MUD capitalizes the first letter of the item,
		-- which may be different from the real item name, so we need to compensate for this
		-- behaviour
		if eq[wildcards[1]] == nil then	-- real name is not capitalized (e.g obsidian boots)
			eq[decapitalize(wildcards[1])] = nil
		else	-- real name is capitalized already (e.g Crusade)
			eq[wildcards[1]] = nil
		end -- if
		table.insert(console_log, "> EQ scrapped (" .. wildcards[1] .. ")!")
	elseif name =="eqRepairNeeded" then
		repair_needed = repair_needed + wildcards[1]
	elseif name == "disableEqScanTriggers" then
		EnableTriggerGroup('eqautotrigger', false)
		draw_eq_window()
	end -- if
	draw_eq_window()
end -- function

-- name is always the eq slot
-- we need to call the strip function to get rid of tags like (Glowing), etc
function set_eq(name, _, wildcards)
	if name == "toggleEqAutoScan" then
		if wildcards[1] == "-" then
			SetVariable("eqAutoScan", "false")
			ColourNote("#00FF00", "black", "Configured -eqscan.")
		elseif wildcards[1] == "+" then
			SetVariable("eqAutoScan", "true")
			ColourNote("#00FF00", "black", "Configured +eqscan.")
		else
			ColourNote("#00FF00", "black", "Config -option or +option?")
		end -- if
		return
	elseif name == "doEqScan" then
		EnableTriggerGroup("eqautotrigger", true)
		eq = {}
		sorted_damaged_eq = {}
		Execute("eq")	-- so we only get slots with equipped items
		return
	else end -- if
	
	local piece = strip(wildcards[1])
	local ac_max = GetVariable(encode(piece))	-- load from the previous state if it exists
	if eq[piece] == nil then	-- if we don't already have the piece in the table
		if ac_max ~= nil and ac_max ~= "?" and ac_max ~= "-1" then	-- the ac max has been set
			eq[piece] = {name=piece, hits=0, max_hits=ac_max, eq_type=name}
		else	-- the ac max hasn't been set
			if name == "wield" or name == "dual_wield" or name == "lance" then
				eq[piece] = {name=piece, hits=0, max_hits=12, eq_type=name}
				return
			else end -- if
			if EQ_AUTO_AC == true then
				local lookup_ac = auto_detect_ac(piece)
				if lookup_ac ~= "-1" and lookup_ac ~= "?" then
					-- do nothing
				else
					table.insert(console_log, "> Item not found in database. (" .. trunc(piece, 20, "~") .. ")")
				end -- if
				eq[piece] = {name=piece, hits=0, max_hits=lookup_ac, eq_type=name}
			else
				eq[piece] = {name=piece, hits=0, max_hits="?", eq_type=name}
				table.insert(console_log, "> AC not set. (" .. trunc(piece, 20, "~") .. ").")
			end -- if
		end -- if
	else end -- if
end -- function

function delete_eq_vars()
	local count = 0
	for k,v in pairs(eq) do
		eq[k] = nil
		if GetVariable(encode(v.name)) ~= nil then
			DeleteVariable(encode(v.name))
			count = count + 1
		else end -- if
	end -- for
	table.insert(console_log, "> Cleared " .. count .. " stored MaxAC variables.")
end -- function

function set_eq_max_ac(name, _, wildcards)
	local piece = strip(wildcards[1])
	if eq[piece] ~= nil then	-- make sure that eqscan has been performed
		eq[piece].max_hits = wildcards[2]
		ColourNote("yellow", "black", "AC updated: ",
				"gray", "black", piece,
				"white", "black", string.format(" (%s)", wildcards[2]))
		SetVariable(encode(eq[piece].name), eq[piece].max_hits)
	else
		ColourNote("yellow", "black", "This piece of equipment has not been configured yet. Wear it and type 'ui.eqscan'.")
	end -- if
	draw_eq_window()
end -- function

-- extras

-- automatically scan eqacdb and set appropriate values
local load_once = false	-- don't read in the eqacdb more than once
function auto_detect_ac(eq_name)
	if load_once == false then
		load_once = true
		local file = io.open(asset_path .. "etc//eq_ac_db.xml", "r")
		if file ~= nil then
			item_nodes = assert(utils.xmlread(file:read '*a'), "EQACDB XML is corrupt.")
			file:close()
			table.insert(console_log, "> EQAC database loaded.")
		else
			EQ_AUTO_AC = false
			table.insert(console_log, "> Error loading EQAC database.")
			return "?"
		end -- if
	else end -- if
	
	local count = 1
	local max_node = item_nodes.nodes[2].nodes[count]
	-- ? means in the database but no value in ac field
	-- -1 means not found in database
	while max_node ~= nil do
		local name = item_nodes.nodes[2].nodes[count].nodes[1].content
		local ac = item_nodes.nodes[2].nodes[count].nodes[2].content
		if string.find(encode(eq_name), encode(name)) ~= nil then 	-- some of the words in the eqdb have been stripped
			if ac ~= nil and ac ~= "" then						-- such as "A" and "the"
				return ac
			else
				return "?"
			end -- if
		else
			count = count + 1
			max_node = item_nodes.nodes[2].nodes[count]
		end -- if
	end -- while
	return "-1"
end -- function

-- end extras

-- toggle warnings on/off
function toggle_warnings(name, _, wildcards)
	if wildcards[1] == "-" then
			SetVariable("warnings", "false")
			ColourNote("#00FF00", "black", "Configured -warnings.")
	elseif wildcards[1] == "+" then
		SetVariable("warnings", "true")
		ColourNote("#00FF00", "black", "Configured +warnings.")
	else
		ColourNote("#00FF00", "black", "Config -option or +option?")
	end -- if
end -- function

-- toggle newbie on/off
function toggle_newbie(name, _, wildcards)
	if wildcards[1] == "-" then
		SetVariable("newbie", "false")
		ColourNote("#00FF00", "black", "Configured -newbie.")
	elseif wildcards[1] == "+" then
		SetVariable("newbie", "true")
		ColourNote("#00FF00", "black", "Configured +newbie.")
	else
		ColourNote("#00FF00", "black", "Config -option or +option?")
	end -- if
	draw_area_list()
end -- function

-- turn the console on/off
function enable_console(name, line, wildcards)
	if wildcards[1] == "-" then
		SetVariable("console", "false")
		EnableTimer("update_console_timer", false)
		WindowShow(console_win, false)
		ColourNote("#00FF00", "black", "Configured -console.")
	elseif wildcards[1] == "+" then
		SetVariable("console", "true")
		EnableTimer("update_console_timer", true)
		ColourNote("#00FF00", "black", "Configured +console.")
	else
		ColourNote("#00FF00", "black", "Config -option or +option?")
	end -- if
end -- function

-- refresh/update the console
function update_console()
	WindowRectOp(console_win, miniwin.rect_fill, 0, 0, 0, 0, colourBlack)
	y_offset = 10
	if #console_log > 12 then
		repeat
			table.remove(console_log, 1)	-- limit the console to 12 items
		until #console_log == 12
	else end -- if
	for k,v in ipairs(console_log) do
		WindowText(console_win, 'console_font', v, 10, y_offset, 400, 200, colourWhite)
		y_offset = y_offset + 15
	end -- for
	WindowShow(console_win, true)
end -- function

-- remove all log items from the console
function clear_console()
	console_log = {}
	table.insert(console_log, "> Realms of Despair UI (v." .. string.format("%.1f", 
					GetPluginInfo(GetPluginID(), 19)) .. ") plugin by Sepharoth.")
end -- function

-- make seamless additions to the RoD 'config' menu.
function append_config()	
	local eqscan_sign
	local eqscan
	local eqscan_colour
	local console_sign
	local console
	local console_colour
	local warnings_sign
	local warnings
	local warnings_colour
	local newbie_sign
	local newbie
	local newbie_colour
	
	if GetVariable("eqAutoScan") == "true" then
		eqscan_sign = "[+] "
		eqscan = "EQSCAN     "
		eqscan_colour = "yellow"
	else
		eqscan_sign = "[-] "
		eqscan = "eqscan     "
		eqscan_colour = "silver"
	end -- if
	
	if GetVariable("console") == "true" then
		console_sign = "[+] "
		console = "CONSOLE    "
		console_colour = "yellow"
	else
		console_sign = "[-] "
		console = "console    "
		console_colour = "silver"
	end -- if
	
	if GetVariable("warnings") == "true" then
		warnings_sign = "[+] "
		warnings = "WARNINGS   "
		warnings_colour = "yellow"
	else
		warnings_sign = "[-] "
		warnings = "warnings   "
		warnings_colour = "silver"
	end -- if
	
	if GetVariable("newbie") == "true" then
		newbie_sign = "[+] "
		newbie = "NEWBIE   "
		newbie_colour = "yellow"
	else
		newbie_sign = "[-] "
		newbie = "newbie   "
		newbie_colour = "silver"
	end -- if
	
	ColourNote("green", "black", "\nUI:        ",
				"silver", "black", eqscan_sign,
				eqscan_colour, "black", eqscan,
				"silver", "black", console_sign,
				console_colour, "black", console,
				"silver", "black", warnings_sign,
				warnings_colour, "black", warnings,
				"silver", "black", newbie_sign,
				newbie_colour, "black", newbie)
end -- function

-- these should be made in to gui elements at some point, or at least added as
-- gui elements for a nicer effect
function note_dialog(name, line, wildcards)
	if name == "help" then
		Note("[UI] Command list")
		Note("> Additional options available in the 'config' menu.")
		Note("> ui.eqac <name> <#> - Assign the maximum armor level for a piece of equipment.")
		Note("> ui.eqclear - Delete all stored MaxAC variables.")
		Note("> ui.eqscan - Scan current EQ so that MaxAC variables can be set.")
		Note("> ui.resize - Force output window to resize to new screen dimensions.")
		Note("> ui.cls - Clear console output.")
	else end -- if
end -- if

------------------------
-- Lua Utility Functions
------------------------

function split(str, patt)
	vals = {}; valindex = 0; word = ""
	-- need to add a trailing separator to catch the last value.
	str = str .. patt
	for i = 1, string.len(str) do
	
		cha = string.sub(str, i, i)
		if cha ~= patt then
			word = word .. cha
		else
			if word ~= nil then
				vals[valindex] = word
				valindex = valindex + 1
				word = ""
			else
				-- in case we get a line with no data.
				break
			end
		end 
	end	
	return vals
end -- function

-- binary search
-- Avoid heap allocs for performance
local default_fcompval = function( value ) return value end
local fcompf = function( a,b ) return a < b end
local fcompr = function( a,b ) return a > b end
function table.binsearch( t,value,fcompval,reversed )
  -- Initialise functions
  local fcompval = fcompval or default_fcompval
  local fcomp = reversed and fcompr or fcompf
  --  Initialise numbers
  local iStart,iEnd,iMid = 1,#t,0
  -- Binary Search
  while iStart <= iEnd do
	 -- calculate middle
	 iMid = math.floor( (iStart+iEnd)/2 )
	 -- get compare value
	 local value2 = fcompval( t[iMid] )
	 -- get all values that match
	 if value == value2 then
		local tfound,num = { iMid,iMid },iMid - 1
		while value == fcompval( t[num] ) do
		   tfound[1],num = num,num - 1
		end
		num = iMid + 1
		while value == fcompval( t[num] ) do
		   tfound[2],num = num,num + 1
		end
		return tfound
	 -- keep searching
	 elseif fcomp( value,value2 ) then
		iEnd = iMid - 1
	 else
		iStart = iMid + 1
	 end
  end
end

function decapitalize(str)
	return (string.gsub(str, "(%w)(%w*)",
	function(FirstLetter, Rest)
		return string.lower(FirstLetter) .. Rest
	end)) -- function
end -- function

-- shorten a long string 'str' to 'length' (optionally) replacing
-- the truncated portion with 'repl'
function trunc(str, length, repl)
	if string.len(str) >= length then
		if not repl then
			return string.sub(str, 1, tonumber(length-3)) .. "..."
		else
			return string.sub(str, 1, tonumber(length-string.len(repl))) .. repl
		end -- if
	else
		return str
	end -- if
end -- function

-- used for removing flags like (Glowing) and (Humming) from item names
-- if the player forgets to exclude it
function strip(str)
	return string.gsub(str, "(%(.*%)) (.*)", "%2")
end -- function

-- translate a string into MUSHclient a compatible string
function encode(str)
	local encoded = str
	encoded = string.gsub(encoded, " ", "_")
	encoded = string.gsub(encoded, "'", "0")
	encoded = string.gsub(encoded, "/", "1")
	encoded = string.gsub(encoded, "-", "2")
	encoded = string.gsub(encoded, "%(", "3")
	encoded = string.gsub(encoded, "%)", "4")
	encoded = string.gsub(encoded, '"', "5")
	encoded = string.gsub(encoded, "&", "6")
	encoded = string.gsub(encoded, ",", "7")
	return encoded
end -- function

-- translate a string into it's real value
function decode(str)
	local decoded = str
	decoded = string.gsub(decoded, "_", " ")
	decoded = string.gsub(decoded, "0", "'")
	decoded = string.gsub(decoded, "1", "/")
	decoded = string.gsub(decoded, "2", "-")
	decoded = string.gsub(decoded, "3", "(")
	decoded = string.gsub(decoded, "4", ")")
	decoded = string.gsub(decoded, "5", '"')
	decoded = string.gsub(decoded, "6", "&")
	decoded = string.gsub(decoded, "7", ",")
	return decoded
end -- function

-- a very basic table copy function
function copy_table(t)
	local t_copy = {}
	
	for k,v in pairs(t) do
		t_copy[k] = v
	end -- for
	
	return t_copy
end -- function
