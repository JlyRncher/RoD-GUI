--[[

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Merged and debugged by Rick Lemons...

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

-- RoD_UI - Realms of Despair User Interface
-- Author: Sepharoth
-- Version: 1.0
--
-- See the "Acknowledgements" section of the README file for credits.
-- Edited in Notepad++ using tabwidth=4

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

LEARNING MAPPER

Author: Nick Gammon
Date:   24th January 2020

 PERMISSION TO DISTRIBUTE

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software
 and associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense,
 and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so,
 subject to the following conditions:

 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.


 LIMITATION OF LIABILITY

 The software is provided "as is", without warranty of any kind, express or implied,
 including but not limited to the warranties of merchantability, fitness for a particular
 purpose and noninfringement. In no event shall the authors or copyright holders be liable
 for any claim, damages or other liability, whether in an action of contract,
 tort or otherwise, arising from, out of or in connection with the software
 or the use or other dealings in the software.

 -------------------------------------------------------------------------

 EXPOSED FUNCTIONS

  set_line_type (linetype, contents) --> set this current line to be definitely linetype with option contents
  set_line_type_contents (linetype, contents)  --> sets the content for <linetype> to be <contents>
                                                   (for example, if you get a room name on a prompt line)
  set_not_line_type (linetype)       --> set this current line to be definitely not linetype (can call for multiple line types)
  set_area_name (name)               --> sets the name of the area you are in
  set_uid (uid)                      --> sets a string to be hashed as the UID for this room
  do_not_deduce_line_type (linetype) --> do not deduce (do Bayesian analysis) on this type of line - has to be set by set_line_type
  deduce_line_type (linetype)        --> deduce this line type (cancels do_not_deduce_line_type)
  get_last_line_type ()              --> get the previous line type as deduced or set by set_line_type
  get_this_line_type ()              --> get the current overridden line type (from set_line_type)
  set_config_option (name, value)    --> set a mapper configuration value of <name> to <value>
  get_config_option (name)           --> get the current configuration value of <name>
  get_corpus ()                      --> get the corpus (serialized table)
  get_stats ()                       --> get the training stats (serialized table)
  get_database ()                    --> get the mapper database (rooms table) (serialized table)
  get_config ()                      --> get the configuration options (serialized table)
  get_current_room ()                --> gets the current room's UID and room information (serialized table)
  set_room_extras (uid, extras)      --> sets extra information for the room (user-supplied)
                                          extras must be a string which serializes into a variable including a table
                                          eg. " { a = 42, b = 666, c = 'Kobold' } "


  eg. config = CallPlugin ("99c74b2685e425d3b6ed6a7d", "get_config")
               CallPlugin ("99c74b2685e425d3b6ed6a7d", "set_line_type", "exits")
               CallPlugin ("99c74b2685e425d3b6ed6a7d", "do_not_deduce_line_type", "exits")

  Note: The plugin ID is fixed as it is set in the Learning_Mapper.xml file near the top:
       id="99c74b2685e425d3b6ed6a7d"

--]]

UI_LUA_VERSION = 1.0 -- version must agree with plugin version


-- The probability (in the range 0.0 to 1.0) that a line has to meet to be considered a certain line type.
-- The higher, the stricter the requirement.
-- Default of 0.7 seems to work OK, but you could tweak that.

PROBABILITY_CUTOFF = 0.7


-- other modules needed by this plugin
require "mapper"
require "serialize"
require "copytable"
require "commas"
require "tprint"
require "pairsbykeys"


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
local mapper_win = "window_type_info_" .. GetPluginID ()
local learn_window = "learn_dialog_" .. GetPluginID ()

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
function OnPluginDisconnect()
	mapper.cancel_speedwalk ()
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
function OnPluginConnect()
	check_dimensions(GetInfo(281), GetInfo(280))
	create_layout()
	mapper.cancel_speedwalk ()
	set_from_room (nil)
	room_name = nil
	exits_str = nil
	description = nil
	set_last_direction_moved (nil)
	ignore_received = false
	override_line_type = nil
	override_line_contents = nil
	override_contents = { }
	line_is_not_line_type = { }
	set_current_room (nil)
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
					width = outlined_text(colourLightGray, eq_win, trunc(v.name, 25), 8, 65, y_offset, 0)
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

-- -----------------------------------------------------------------
-- Handlers for when a line-type changes
-- -----------------------------------------------------------------

description_styles = { }
exits_styles = { }
room_name_styles = { }

UNKNOWN_DUPLICATE_ROOM = string.rep ("F", 25)  -- dummy UID

DEBUGGING = true

function set_last_direction_moved (where)
  last_direction_moved = where
  DEBUG ("SET: last_direction_moved: " .. tostring (where))
end  -- set_last_direction_moved
function get_last_direction_moved ()
  DEBUG ("get: last_direction_moved: " .. tostring (last_direction_moved))
  return last_direction_moved
end  -- get_last_direction_moved
function set_from_room (where)
  from_room = where
  DEBUG ("SET: from_room: " .. fixuid (tostring (where)))
end  -- set_from_room
function get_from_room (f)
  if f then
    DEBUG ("get: from_room: " .. fixuid (tostring (from_room)) .. " (" .. f .. ")")
  else
    DEBUG ("get: from_room: " .. fixuid (tostring (from_room)))
  end -- if
  return from_room
end  -- get_from_room
function set_current_room (where)
  current_room = where
  DEBUG ("SET: current_room: " .. fixuid (tostring (where)))
end  -- set_current_room
function get_current_room_ (f)
  if f then
    DEBUG ("get: current_room: " .. fixuid (tostring (current_room)) .. " (" .. f .. ")")
  else
    DEBUG ("get: current_room: " .. fixuid (tostring (current_room)))
  end -- if
  return current_room
end  -- get_current_room_

-- -----------------------------------------------------------------
-- description
-- -----------------------------------------------------------------
function f_handle_description (saved_lines)

  if description and ignore_received then
    return
  end -- if

  -- if the description follows the exits, then ignore descriptions that don't follow exits
  if config.ACTIVATE_DESCRIPTION_AFTER_EXITS then
    if not exits_str then
      return
    end -- if
  end -- if

  -- if the description follows the room name, then ignore descriptions that don't follow the room name
  if config.ACTIVATE_DESCRIPTION_AFTER_ROOM_NAME then
    if not room_name then
      return
    end -- if
  end -- if

  local lines = { }
  description_styles = { }
  for _, line_info in ipairs (saved_lines) do
    table.insert (lines, line_info.line) -- get text of line
    table.insert (description_styles, line_info.styles [1])  -- remember first style run
  end -- for each line
  description = table.concat (lines, "\n")

  if config.WHEN_TO_DRAW_MAP == DRAW_MAP_ON_DESCRIPTION then
    process_new_room ()
  end -- if
end -- f_handle_description

-- -----------------------------------------------------------------
-- exits
-- -----------------------------------------------------------------
function f_handle_exits ()
  local lines = { }
  exits_styles = { }
  for _, line_info in ipairs (saved_lines) do
    table.insert (lines, line_info.line) -- get text of line
    table.insert (exits_styles, line_info.styles [1])  -- remember first style run
  end -- for each line
  exits_str = table.concat (lines, " "):lower ()

  if config.WHEN_TO_DRAW_MAP == DRAW_MAP_ON_EXITS then
    process_new_room ()
  end -- if
end -- f_handle_exits

-- -----------------------------------------------------------------
-- room name
-- -----------------------------------------------------------------
function f_handle_name ()
  local lines = { }
  room_name_styles = { }
  for _, line_info in ipairs (saved_lines) do
    table.insert (lines, line_info.line) -- get text of line
    table.insert (room_name_styles, line_info.styles [1])  -- remember first style run
  end -- for each line
  room_name = table.concat (lines, " ")

  -- a bit of a hack, but look for: Room name [N, S, W]
  if config.EXITS_ON_ROOM_NAME then
    local name, exits = string.match (room_name, "^([^%[]+)(%[.*%])%s*$")
    if name then
      room_name = name
      exits_str = exits:lower ()
    end -- if that sort of line found
  end -- if exits on room name wanted

  if config.WHEN_TO_DRAW_MAP == DRAW_MAP_ON_ROOM_NAME then
    process_new_room ()
  end -- if
end -- f_handle_name

-- -----------------------------------------------------------------
-- prompt
-- -----------------------------------------------------------------
function f_handle_prompt ()
  local lines = { }
  for _, line_info in ipairs (saved_lines) do
    table.insert (lines, line_info.line) -- get text of line
  end -- for each line
  prompt = table.concat (lines, " ")
  if config.WHEN_TO_DRAW_MAP == DRAW_MAP_ON_PROMPT then
    if override_contents ['description'] then
      description = override_contents ['description']
    end -- if
    if override_contents ['exits'] then
      exits_str = override_contents ['exits']:lower ()
    end -- if
    if override_contents ['room_name'] then
      room_name = override_contents ['room_name']
    end -- if
    if description and exits_str then
      process_new_room ()
    end -- if
  end -- if time to draw the map
end -- f_handle_prompt

-- -----------------------------------------------------------------
-- ignore this line type
-- -----------------------------------------------------------------
function f_handle_ignore ()
  ignore_received = true
end -- f_handle_ignore

-- -----------------------------------------------------------------
-- cannot move - cancel speedwalk
-- -----------------------------------------------------------------
function f_cannot_move ()
  mapper.cancel_speedwalk ()
  set_last_direction_moved (nil)  -- therefore we haven't moved anywhere
end -- f_cannot_move

-- -----------------------------------------------------------------
-- Handlers for getting the wanted value for a marker for the nominated line
-- -----------------------------------------------------------------

-- these are the types of lines we are trying to classify as a certain line IS or IS NOT that type
line_types = {
  room_name   = { short = "Room name",    handler = f_handle_name,        seq = 1 },
  description = { short = "Description",  handler = f_handle_description, seq = 2 },
  exits       = { short = "Exits",        handler = f_handle_exits,       seq = 3 },
  prompt      = { short = "Prompt",       handler = f_handle_prompt,      seq = 4 },
  ignore      = { short = "Ignore",       handler = f_handle_ignore,      seq = 5 },
  cannot_move = { short = "Can't move",   handler = f_cannot_move,        seq = 6 },
}  -- end of line_types table

function f_first_style_run_foreground (line)
  return { GetStyleInfo(line, 1, 14) or -1 }
end -- f_first_style_run_foreground

function f_show_colour (which, value)
  mapper.mapprint (string.format ("    %20s %5d %5d %7.2f", RGBColourToName (which), value.black, value.red, value.score))
end -- f_show_colour

function f_show_word (which, value)
  if #which > 20 then
    mapper.mapprint (string.format ("%s\n    %20s %5d %5d %7.2f", which, '', value.black, value.red, value.score))
  else
    mapper.mapprint (string.format ("    %20s %5d %5d %7.2f", which, value.black, value.red, value.score))
  end -- if
end -- f_show_colour

function f_first_word (line)
  if not GetLineInfo(line, 1) then
    return {}
  end -- no line available
  return { (string.match (GetLineInfo(line, 1), "^%s*(%a+)") or ""):lower () }
end -- f_first_word

function f_exact_line (line)
  if not GetLineInfo(line, 1) then
    return {}
  end -- no line available
  return { GetLineInfo(line, 1) }
end -- f_exact_line

function f_first_two_words (line)
  if not GetLineInfo(line, 1) then
    return {}
  end -- no line available
  return { (string.match (GetLineInfo(line, 1), "^%s*(%a+%s+%a+)") or ""):lower () }
end -- f_first_two_words

function f_first_three_words (line)
  if not GetLineInfo(line, 1) then
    return {}
  end -- no line available
  return { (string.match (GetLineInfo(line, 1), "^%s*(%a+%s+%a+%s+%a+)") or ""):lower () }
end -- f_first_three_words

function f_all_words (line)
  if not GetLineInfo(line, 1) then
    return {}
  end -- no line available
  local words = { }
  for w in string.gmatch (GetLineInfo(line, 1), "%a+") do
    table.insert (words, w:lower ())
  end -- for
  return words
end -- f_all_words

function f_first_character (line)
  if not GetLineInfo(line, 1) then
    return {}
  end -- no line available
  return { string.match (GetLineInfo(line, 1), "^.") or "" }
end -- f_first_character

-- -----------------------------------------------------------------
-- markers: things we are looking for, like colour of first style run
-- You could add others, for example:
--   * colour of the last style run
--   * number of words on the line
--   * number of style runs on the line
--  Whether that would help or not remains to be seen.

-- The functions above return the value(s) for the corresponding marker, for the nominated line.
-- -----------------------------------------------------------------
markers = {

  {
  desc = "Foreground colour of first style run",
  func = f_first_style_run_foreground,
  marker = "first_style_run_foreground",
  show = f_show_colour,
  accessing_function = pairs,
  },

  {
  desc = "First word in the line",
  func = f_first_word,
  marker = "first_word",
  show = f_show_word,
  accessing_function = pairsByKeys,

  },

 {
  desc = "First two words in the line",
  func = f_first_two_words,
  marker = "first_two_words",
  show = f_show_word,
  accessing_function = pairsByKeys,

  },

 {
  desc = "First three words in the line",
  func = f_first_three_words,
  marker = "first_three_words",
  show = f_show_word,
  accessing_function = pairsByKeys,

  },

  {
  desc = "All words in the line",
  func = f_all_words,
  marker = "all_words",
  show = f_show_word,
  accessing_function = pairsByKeys,

  },

 {
  desc = "Exact line",
  func = f_exact_line,
  marker = "exact_line",
  show = f_show_word,
  accessing_function = pairsByKeys,
  },

--[[

 {
  desc = "First character in the line",
  func = f_first_character,
  marker = "first_character",
  show = f_show_word,

  },

--]]

  } -- end of markers

inverse_markers = { }
for k, v in ipairs (markers) do
  inverse_markers [v.marker] = v
end -- for

local MAX_NAME_LENGTH = 60

-- when to update the map
DRAW_MAP_ON_ROOM_NAME = 1
DRAW_MAP_ON_DESCRIPTION = 2
DRAW_MAP_ON_EXITS = 3
DRAW_MAP_ON_PROMPT = 4


default_config = {
  -- assorted colours
  BACKGROUND_COLOUR       = { name = "Background",        colour =  ColourNameToRGB "lightseagreen", },
  ROOM_COLOUR             = { name = "Room",              colour =  ColourNameToRGB "cyan", },
  EXIT_COLOUR             = { name = "Exit",              colour =  ColourNameToRGB "darkgreen", },
  EXIT_COLOUR_UP_DOWN     = { name = "Exit up/down",      colour =  ColourNameToRGB "darkmagenta", },
  EXIT_COLOUR_IN_OUT      = { name = "Exit in/out",       colour =  ColourNameToRGB "#3775E8", },
  OUR_ROOM_COLOUR         = { name = "Our room",          colour =  ColourNameToRGB "black", },
  UNKNOWN_ROOM_COLOUR     = { name = "Unknown room",      colour =  ColourNameToRGB "#00CACA", },
  DIFFERENT_AREA_COLOUR   = { name = "Another area",      colour =  ColourNameToRGB "#009393", },
  SHOP_FILL_COLOUR        = { name = "Shop",              colour =  ColourNameToRGB "darkolivegreen", },
  TRAINER_FILL_COLOUR     = { name = "Trainer",           colour =  ColourNameToRGB "yellowgreen", },
  BANK_FILL_COLOUR        = { name = "Bank",              colour =  ColourNameToRGB "gold", },
  DUPLICATE_FILL_COLOUR   = { name = "Duplicate",         colour =  ColourNameToRGB "lightgoldenrodyellow", },
  BOOKMARK_FILL_COLOUR    = { name = "Notes",             colour =  ColourNameToRGB "lightskyblue", },
  MAPPER_NOTE_COLOUR      = { name = "Messages",          colour =  ColourNameToRGB "lightgreen" },

  ROOM_NAME_TEXT          = { name = "Room name text",    colour = ColourNameToRGB "#BEF3F1", },
  ROOM_NAME_FILL          = { name = "Room name fill",    colour = ColourNameToRGB "#105653", },
  ROOM_NAME_BORDER        = { name = "Room name box",     colour = ColourNameToRGB "black", },

  AREA_NAME_TEXT          = { name = "Area name text",    colour = ColourNameToRGB "#BEF3F1",},
  AREA_NAME_FILL          = { name = "Area name fill",    colour = ColourNameToRGB "#105653", },
  AREA_NAME_BORDER        = { name = "Area name box",     colour = ColourNameToRGB "black", },

  FONT = { name =  get_preferred_font {"Dina",  "Lucida Console",  "Fixedsys", "Courier", "Sylfaen",} ,
           size = 8
         } ,

  -- size of map window
  WINDOW = { width = 400, height = 400 },

  -- how far from where we are standing to draw (rooms)
  SCAN = { depth = 30 },

  -- speedwalk delay
  DELAY = { time = 0.3 },

  -- how many seconds to show "recent visit" lines (default 3 minutes)
  LAST_VISIT_TIME = { time = 60 * 3 },

  -- config for learning mapper

  STATUS_BACKGROUND_COLOUR  = "black",       -- the background colour of the status window
  STATUS_FRAME_COLOUR       = "#1B1B1B",     -- the frame colour of the status window
  STATUS_TEXT_COLOUR        = "lightgreen",   -- palegreen is more visible

  UID_SIZE = 4,  -- how many characters of the UID to show

  -- learning configuration
  WHEN_TO_DRAW_MAP = DRAW_MAP_ON_EXITS,        -- we need to have name/description/exits to draw the map
  ACTIVATE_DESCRIPTION_AFTER_EXITS = false,    -- descriptions are activated *after* an exit line (used for MUDs with exits then descriptions)
  ACTIVATE_DESCRIPTION_AFTER_ROOM_NAME = false,-- descriptions are activated *after* a room name line
  BLANK_LINE_TERMINATES_LINE_TYPE = false,     -- if true, a blank line terminates the previous line type
  ADD_NEWLINE_TO_PROMPT = false,               -- if true, attempts to add a newline to a prompt at the end of a packet
  SHOW_LEARNING_WINDOW = true,                 -- if true, show the learning status and training windows on startup
  EXITS_ON_ROOM_NAME = false,                  -- if true, exits are listed on the room name line (eg. Starter Inventory and Shops [E, U])
  INCLUDE_EXITS_IN_HASH = true,                -- if true, exits are included in the description hash (UID)
  INCLUDE_ROOM_NAME_IN_HASH = false,           -- if true, the room name is included in the description hash (UID)
  EXITS_IS_SINGLE_LINE = false,                -- if true, exits are assumed to be only a single line
  PROMPT_IS_SINGLE_LINE = true,                -- if true, prompts are assumed to be only a single line
  EXIT_LINES_START_WITH_DIRECTION = false,     -- if true, exit lines must start with a direction (north, south, etc.)
  SORT_EXITS = false,                          -- if true, exit lines are extracted into words and sorted, excluding any other characters on the line
  SAVE_LINE_INFORMATION = true,                -- if true, we save to the database the colour of the first style run for name/description/exits

  -- other stuff

  SHOW_INFO = false,              -- if true, information messages are displayed
  SHOW_WARNINGS = true,           -- if true, warning messages are displayed
  SHOW_ROOM_AND_EXITS = false,    -- if true, exact deduced room name and exits are shown (needs SHOW_INFO)

  }

-- -----------------------------------------------------------------
-- Handlers for validating configuration values (eg. colour, boolean)
-- -----------------------------------------------------------------

function config_validate_colour (which)
  local colour = ColourNameToRGB (which)
  if colour == -1 then
    mapper.maperror (string.format ('Colour name "%s" not a valid HTML colour name or code.', which))
    mapper.mapprint ("  You can use HTML colour codes such as '#ab34cd' or names such as 'green'.")
    mapper.mapprint ("  See the Colour Picker (Edit menu -> Colour Picker: Ctrl+Alt+P).")
    return nil, nil
  end -- if bad
  return which, colour
end -- config_validate_colour

function config_validate_uid_size (which)
  local size = tonumber (which)
  if not size then
    mapper.maperror ("Bad UID size: " .. which)
    return nil
  end -- if

  if size < 3 or size > 25 then
    mapper.maperror ("UID size must be in the range 3 to 25")
    return nil
  end -- if

  return size
end -- config_validate_uid_size

-- -----------------------------------------------------------------
-- when we draw the map (after what sort of line)
-- -----------------------------------------------------------------
local when_types = {
    ["room name"]   = DRAW_MAP_ON_ROOM_NAME,
    ["description"] = DRAW_MAP_ON_DESCRIPTION,
    ["exits"]       = DRAW_MAP_ON_EXITS,
    ["prompt"]      = DRAW_MAP_ON_PROMPT,
    } -- end of table

function config_validate_when_to_draw (which)
  local when = which:lower ()

  local w = when_types [when]
  if not w then
    mapper.maperror ("Unknown time to draw the map: " .. which)
    mapper.mapprint ("Valid times are:")
    local t = { }
    for k, v in ipairs (when_types) do
      table.insert (t, k)
    end
    mapper.mapprint ("    " .. table.concat (t, ", "))
    return nil
  end -- if type not found

  return w
end -- when_to_draw

function convert_when_to_draw_to_name (which)
  local when = "Unknown"
  for k, v in pairs (when_types) do
    if which == v then
      when = k
      break
    end -- if
  end -- for
  return when
end -- convert_when_to_draw_to_name

local bools = {
  yes = true,
  y = true,
  no = false,
  n = false
} -- end of bools

function config_validate_boolean (which)
  local which = which:lower ()
  local yesno = bools [which]
  if yesno == nil then
    mapper.maperror ("Invalid option: must be YES or NO")
    return
  end -- not in bools table
  return yesno
end -- config_validate_boolean

-- -----------------------------------------------------------------
-- Handlers for displaying configuration values (eg. colour, boolean)
-- -----------------------------------------------------------------

function config_display_colour (which)
  return which
end -- config_display_colour

function config_display_number (which)
  return tostring (which)
end -- config_display_number

function config_display_when_to_draw (which)
  return convert_when_to_draw_to_name (which)
end -- config_display_when_to_draw

function config_display_boolean (which)
  if which then
    return "Yes"
  else
    return "No"
  end -- if
end -- config_display_boolean

-- -----------------------------------------------------------------
-- Configuration options (ie. mapper config <option>) and their handlers and internal option name
-- -----------------------------------------------------------------

config_control = {
  { option = 'WHEN_TO_DRAW_MAP',                  name = 'when_to_draw',                     validate = config_validate_when_to_draw, show = config_display_when_to_draw },
  { option = 'ACTIVATE_DESCRIPTION_AFTER_EXITS',  name = 'activate_description_after_exits', validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'ACTIVATE_DESCRIPTION_AFTER_ROOM_NAME',  name = 'activate_description_after_room_name', validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'ADD_NEWLINE_TO_PROMPT',             name = 'add_newline_to_prompt',            validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'BLANK_LINE_TERMINATES_LINE_TYPE',   name = 'blank_line_terminates_line_type',  validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'EXITS_ON_ROOM_NAME',                name = 'exits_on_room_name',               validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'INCLUDE_EXITS_IN_HASH',             name = 'include_exits_in_hash',            validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'INCLUDE_ROOM_NAME_IN_HASH',         name = 'include_room_name_in_hash',        validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'EXITS_IS_SINGLE_LINE',              name = 'exits_is_single_line',             validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'PROMPT_IS_SINGLE_LINE',             name = 'prompt_is_single_line',            validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'EXIT_LINES_START_WITH_DIRECTION',   name = 'exit_lines_start_with_direction',  validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'SORT_EXITS',                        name = 'sort_exits',                       validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'STATUS_BACKGROUND_COLOUR',          name = 'status_background',                validate = config_validate_colour,       show = config_display_colour },
  { option = 'STATUS_FRAME_COLOUR',               name = 'status_border',                    validate = config_validate_colour,       show = config_display_colour },
  { option = 'STATUS_TEXT_COLOUR',                name = 'status_text',                      validate = config_validate_colour,       show = config_display_colour },
  { option = 'UID_SIZE',                          name = 'uid_size',                         validate = config_validate_uid_size,     show = config_display_number },
  { option = 'SAVE_LINE_INFORMATION',             name = 'save_line_info',                   validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'SHOW_INFO',                         name = 'show_info',                        validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'SHOW_WARNINGS',                     name = 'show_warnings',                    validate = config_validate_boolean,      show = config_display_boolean },
  { option = 'SHOW_ROOM_AND_EXITS',               name = 'show_room_and_exits',              validate = config_validate_boolean,      show = config_display_boolean },

}

-- make a table keyed on the name the user uses
config_control_names = { }
for k, v in ipairs (config_control) do
  config_control_names [v.name] = v
end -- for

-- -----------------------------------------------------------------
-- valid_direction - for detecting movement between rooms, and validating exit lines
-- -----------------------------------------------------------------

valid_direction = {
  n = "n",
  s = "s",
  e = "e",
  w = "w",
  u = "u",
  d = "d",
  ne = "ne",
  sw = "sw",
  nw = "nw",
  se = "se",
  north = "n",
  south = "s",
  east = "e",
  west = "w",
  up = "u",
  down = "d",
  northeast = "ne",
  northwest = "nw",
  southeast = "se",
  southwest = "sw",
  ['in'] = "in",
  out = "out",
  }  -- end of valid_direction

-- -----------------------------------------------------------------
-- inverse_direction - if we go north then the inverse direction is south, and so on.
-- -----------------------------------------------------------------

inverse_direction = {
  n = "s",
  s = "n",
  e = "w",
  w = "e",
  u = "d",
  d = "u",
  ne = "sw",
  sw = "ne",
  nw = "se",
  se = "nw",
  ['in'] = "out",
  out = "in",
  }  -- end of inverse_direction

-- -----------------------------------------------------------------
-- OnPluginDrawOutputWindow
--  Update our line information info
-- -----------------------------------------------------------------
function OnPluginDrawOutputWindow (firstline, offset, notused)

  -- don't bother if window not visible
  if not WindowInfo (mapper_win, 5) then
    return
  end -- if

  local background_colour = ColourNameToRGB (config.STATUS_BACKGROUND_COLOUR)
  local frame_colour = ColourNameToRGB (config.STATUS_FRAME_COLOUR)
  local text_colour = ColourNameToRGB (config.STATUS_TEXT_COLOUR)
  local main_height = GetInfo (280)
  local font_height = GetInfo (212)

  -- clear window
  WindowRectOp (mapper_win, miniwin.rect_fill, 0, 0, 0, 0, background_colour)

  -- frame it
  WindowRectOp(mapper_win, miniwin.rect_frame, 0, 0, 0, 0, frame_colour)

  -- allow for scrolling position
  local top =  (((firstline - 1) * font_height) - offset) - 2

  -- how many lines to draw

  local lastline = firstline + (main_height / font_height)

  for line = firstline, lastline do
    if line >= 1 and GetLineInfo (line, 1) then
      if GetLineInfo (line, 4) or GetLineInfo (line, 5) then
        -- note or input line, ignore it
      else
        local linetype, probability, x_offset
        local ded = deduced_line_types [GetLineInfo (line, 10)]
        if ded and ded.lt then
          if ded.ov then
            line_type_info = string.format ("<- %s (certain)", line_types [ded.lt].short)
          else
            line_type_info = string.format ("<- %s (%0.0f%%)", line_types [ded.lt].short, (ded.con or 0) * 100)
          end -- if overridden or not
          local x_offset = WindowText (mapper_win, font_id, line_type_info, 1, top, 0, 0, text_colour)
          if (not GetLineInfo (line, 3)) and (line >= lastline - 1) then
            x_offset = x_offset + WindowText (mapper_win, font_id, " (partial line)", 1 + x_offset, top, 0, 0, ColourNameToRGB ("darkgray"))
          end -- if
          if ded.draw then
            x_offset = x_offset + WindowText (mapper_win, font_id,
                      string.format (" (draw room %s)", fixuid (ded.uid)), 1 + x_offset, top, 0, 0, ColourNameToRGB ("darkgray"))
          end -- if
        end -- if in deduced_line_types table
      end -- if output line
      top = top + font_height
    end -- if line exists
  end -- for each line

end -- OnPluginDrawOutputWindow

-- -----------------------------------------------------------------
-- OnPluginWorldOutputResized
--  On world window resize, remake the miniwindow to fit the size correctly
-- -----------------------------------------------------------------
function OnPluginWorldOutputResized ()

	if IsTimer("init_delay") ~= 0 then	-- if the timer DOESN'T exist
		do_resize()
		draw_panes()
		--Note(msdp["WORLD_TIME"]) -- test to see if it has been implemented yet!
	else end -- end

  font_name = GetInfo (20) -- output window font
  font_size = GetOption "output_font_height"

  local output_width  = GetInfo (240)  -- average width of pixels per character
  local wrap_column   = GetOption ('wrap_column')
  local pixel_offset  = GetOption ('pixel_offset')

  -- make window so I can grab the font info
  WindowCreate (mapper_win,
                (output_width * wrap_column) + pixel_offset + 10, -- left
                0,  -- top
                400, -- width
                GetInfo (263),   -- world window client height
                miniwin.pos_top_left,   -- position (irrelevant)
                miniwin.create_absolute_location,   -- flags
                ColourNameToRGB (config.STATUS_BACKGROUND_COLOUR))   -- background colour

  -- add font
  WindowFont (mapper_win, font_id, font_name, font_size,
              false, false, false, false,  -- normal
              miniwin.font_charset_ansi, miniwin.font_family_any)

  -- find height of font for future calculations
  font_height = WindowFontInfo (mapper_win, font_id, 1)  -- height

  WindowSetZOrder(mapper_win, -5)

   if WindowInfo (learn_window, 5) then
     WindowShow (mapper_win)
   end -- if

end -- OnPluginWorldOutputResized

-- -----------------------------------------------------------------
-- INFO helper function for debugging the plugin (information messages)
-- -----------------------------------------------------------------
function INFO (...)
  if config.SHOW_INFO then
    ColourNote ("orange", "", table.concat ( { ... }, " "))
  end -- if
end -- INFO

-- -----------------------------------------------------------------
-- WARNING helper function for debugging the plugin (warning/error messages)
-- -----------------------------------------------------------------
function WARNING (...)
  if config.SHOW_WARNINGS then
    ColourNote ("red", "", table.concat ( { ... }, " "))
  end -- if
end -- WARNING

-- -----------------------------------------------------------------
-- DEBUG helper function for debugging the plugin
-- -----------------------------------------------------------------
function DEBUG (...)
  if DEBUGGING then
    ColourNote ("cornflowerblue", "", table.concat ( { ... }, " "))
  end -- if
end -- DEBUG


-- -----------------------------------------------------------------
-- corpus_reset - throw away the learned corpus
-- -----------------------------------------------------------------
function corpus_reset (empty)
  if empty then
    corpus = { }
    stats  = { }
  end -- if

  -- make sure each line type is in the corpus

  for k, v in pairs (line_types) do
    if not corpus [k] then
      corpus [k] = {}
    end -- not there yet

    if not stats [k] then
      stats [k] = { is = 0, isnot = 0 }
    end -- not there yet

    for k2, v2 in ipairs (markers) do
      if not corpus [k] [v2.marker] then  -- if that marker not there, add it
         corpus [k] [v2.marker] = { } -- table of values for this marker
      end -- marker not there yet

    end -- for each marker type
  end -- for each line type

end -- corpus_reset

LEARN_WINDOW_WIDTH = 300
LEARN_WINDOW_HEIGHT = 270
LEARN_BUTTON_WIDTH = 80
LEARN_BUTTON_HEIGHT = 30

hotspots = { }
button_down = false

-- -----------------------------------------------------------------
-- button_mouse_down - generic mouse-down handler
-- -----------------------------------------------------------------
function button_mouse_down (flags, hotspot_id)
  local hotspot_info = hotspots [hotspot_id]
  if not hotspot_info then
    WARNING ("No info found for hotspot", hotspot_id)
    return
  end

  -- no button state change if no selection
  if GetSelectionStartLine () == 0 then
    return
  end -- if

  button_down = true
  WindowRectOp (hotspot_info.window, miniwin.rect_draw_edge,
                hotspot_info.x1, hotspot_info.y1, hotspot_info.x2, hotspot_info.y2,
                miniwin.rect_edge_sunken,
                miniwin.rect_edge_at_all + miniwin.rect_option_fill_middle)  -- sunken, filled
  WindowText   (hotspot_info.window, hotspot_info.font, hotspot_info.text, hotspot_info.text_x + 1, hotspot_info.y1 + 8 + 1, 0, 0, ColourNameToRGB "black", true)
  Redraw ()

end -- button_mouse_down

-- -----------------------------------------------------------------
-- button_cancel_mouse_down - generic cancel-mouse-down handler
-- -----------------------------------------------------------------
function button_cancel_mouse_down (flags, hotspot_id)
  local hotspot_info = hotspots [hotspot_id]
  if not hotspot_info then
    WARNING ("No info found for hotspot", hotspot_id)
    return
  end

  button_down = false
  buttons_active = nil

  WindowRectOp (hotspot_info.window, miniwin.rect_draw_edge,
                hotspot_info.x1, hotspot_info.y1, hotspot_info.x2, hotspot_info.y2,
                miniwin.rect_edge_raised,
                miniwin.rect_edge_at_all + miniwin.rect_option_fill_middle)  -- raised, filled
  WindowText   (hotspot_info.window, hotspot_info.font, hotspot_info.text, hotspot_info.text_x, hotspot_info.y1 + 8, 0, 0, ColourNameToRGB "black", true)

  Redraw ()
end -- button_cancel_mouse_down

-- -----------------------------------------------------------------
-- button_mouse_up - generic mouse-up handler
-- -----------------------------------------------------------------
function button_mouse_up (flags, hotspot_id)
  local hotspot_info = hotspots [hotspot_id]
  if not hotspot_info then
    WARNING ("No info found for hotspot", hotspot_id)
    return
  end

  button_down = false
  buttons_active = nil

  -- call the handler
  hotspot_info.handler ()

  WindowRectOp (hotspot_info.window, miniwin.rect_draw_edge,
                hotspot_info.x1, hotspot_info.y1, hotspot_info.x2, hotspot_info.y2,
                miniwin.rect_edge_raised,
                miniwin.rect_edge_at_all + miniwin.rect_option_fill_middle)  -- raised, filled
  WindowText   (hotspot_info.window, hotspot_info.font, hotspot_info.text, hotspot_info.text_x, hotspot_info.y1 + 8, 0, 0, ColourNameToRGB "black", true)

  Redraw ()
end -- button_mouse_up

-- -----------------------------------------------------------------
-- make_button - make a button for the dialog window and remember its handler
-- -----------------------------------------------------------------
function make_button (window, font, x, y, text, tooltip, handler)

  WindowRectOp (window, miniwin.rect_draw_edge, x, y, x + LEARN_BUTTON_WIDTH, y + LEARN_BUTTON_HEIGHT,
            miniwin.rect_edge_raised,
            miniwin.rect_edge_at_all + miniwin.rect_option_fill_middle)  -- raised, filled

  local width = WindowTextWidth (window, font, text, true)
  local text_x = x + (LEARN_BUTTON_WIDTH - width) / 2

  WindowText   (window, font, text, text_x, y + 8, 0, 0, ColourNameToRGB "black", true)

  local hotspot_id = string.format ("HS_learn_%d,%d", x, y)
  -- remember handler function
  hotspots [hotspot_id] = { handler = handler,
                            window = window,
                            x1 = x, y1 = y,
                            x2 = x + LEARN_BUTTON_WIDTH, y2 = y + LEARN_BUTTON_HEIGHT,
                            font = font,
                            text = text,
                            text_x = text_x }

  WindowAddHotspot(window,
                  hotspot_id,
                   x, y, x + LEARN_BUTTON_WIDTH, y + LEARN_BUTTON_HEIGHT,
                   "",                          -- MouseOver
                   "",                          -- CancelMouseOver
                   "button_mouse_down",         -- MouseDown
                   "button_cancel_mouse_down",  -- CancelMouseDown
                   "button_mouse_up",           -- MouseUp
                   tooltip,                     -- tooltip text
                   miniwin.cursor_hand,         -- mouse cursor shape
                   0)                           -- flags


end -- make_button

-- -----------------------------------------------------------------
-- update_buttons - grey-out buttons if nothing selected
-- -----------------------------------------------------------------

buttons_active = nil


-- stuff for warning them to save their file
time_last_saved = os.time ()
time_last_warned = nil

TIME_BETWEEN_SAVES = 15 * 60    -- warn if they haven't saved for 30 minutes
TIME_BETWEEN_WARNINGS = 1 * 60  -- warn every 1 minute
ADDED_ROOMS_COUNT = 10          -- warn if they have added this many rooms

function update_buttons (name)

  -- to save memory, throw away info for lines more than 1000 further back in the buffer
  local this_line = GetLinesInBufferCount()         -- which line in the output buffer
  local line_number = GetLineInfo (this_line, 10)   -- which line this was overall
  local wanted_line_number = line_number - 1000     -- keep info for 1000 lines

  if line_number then
    for k in pairs (deduced_line_types) do
       if k < wanted_line_number then
         deduced_line_types [k] = nil
        end -- for
    end -- for
  end -- if we have any lines

  -- warn user if database not saved after adding rooms

  -- how long since the last save
  local time_since_save = os.difftime (os.time (), time_last_saved)

  -- if they have added a few rooms and not saved then warn them
  if rooms_added >= ADDED_ROOMS_COUNT and     -- added a few rooms
    time_since_save > TIME_BETWEEN_SAVES and  -- not saved for a while
    (time_last_warned == nil or os.difftime (os.time (), time_last_warned) >= TIME_BETWEEN_WARNINGS) then  -- warn quite often after that time elapsed
    mapper.maperror (string.format ("WARNING: You have added %d rooms, but have not saved your world file recently.", rooms_added))
    mapper.mapprint ("Recommended: Save your world file (Ctrl+S) which will also save the mapper database.")
    time_last_warned = os.time ()
  end -- if

  -- do nothing if button pressed
  if button_down then
    return
  end -- if

  local have_selection = GetSelectionStartLine () ~= 0

  -- do nothing if the state hasn't changed
  if have_selection == buttons_active then
    return
  end -- if

  buttons_active = have_selection

  for hotspot_id, hotspot_info in pairs (hotspots) do
    if string.match (hotspot_id, "^HS_learn_") then
      local wanted_colour = ColourNameToRGB "black"
      if not buttons_active then
        wanted_colour = ColourNameToRGB "silver"
      end -- if
      WindowText   (hotspot_info.window, hotspot_info.font, hotspot_info.text, hotspot_info.text_x, hotspot_info.y1 + 8, 0, 0, wanted_colour, true)
    end -- if a learning button
  end -- for

  Redraw ()

end -- update_buttons

-- -----------------------------------------------------------------
-- mouseup_close_configure - they hit the close box in the learning window
-- -----------------------------------------------------------------
function mouseup_close_configure  (flags, hotspot_id)
  WindowShow (learn_window, false)
  WindowShow (mapper_win, false)
  mapper.mapprint ('Type: "mapper learn" to show the training window again')
  config.SHOW_LEARNING_WINDOW = false
end -- mouseup_close_configure

-- -----------------------------------------------------------------
-- toggle_learn_window - toggle the window: called from "mapper learn"
-- -----------------------------------------------------------------
function toggle_learn_window (name, line, wildcards)
  if WindowInfo (learn_window, 5) then
    WindowShow (mapper_win, false)
    WindowShow (learn_window, false)
    config.SHOW_LEARNING_WINDOW = false
  else
    WindowShow (mapper_win, true)
    WindowShow (learn_window, true)
    config.SHOW_LEARNING_WINDOW = true
  end -- if
end -- toggle_learn_window

-- -----------------------------------------------------------------
-- Plugin Install
-- -----------------------------------------------------------------
function OnPluginInstall ()
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

  font_id = "f"

  -- this table has the counters
  corpus = { }

  -- stats
  stats = { }

  -- load corpus
  assert (loadstring (GetVariable ("corpus") or "")) ()
  -- load stats
  assert (loadstring (GetVariable ("stats") or "")) ()

  config = {}  -- in case not found

  -- get saved configuration
  assert (loadstring (GetVariable ("config") or "")) ()

  corpus_reset ()

  -- allow for additions to config
  for k, v in pairs (default_config) do
    config [k] = config [k] or v
  end -- for


  -- and rooms
  rooms = {}
  assert (loadstring (GetVariable ("rooms") or "")) ()

  -- fix up in case I bugger up the exits
  for uid, room in pairs (rooms) do
    if not room.exits then
      room.exits = { }
    end -- if
  end -- if

  -- and duplicate rooms
  duplicates = {}
  assert (loadstring (GetVariable ("duplicates") or "")) ()

  -- initialize mapper

  mapper.init {
              config = config,            -- our configuration table
              get_room = get_room,        -- get info about a room
              room_click = room_click,    -- called on RH click on room square
              show_other_areas = true,    -- show all areas
              show_help = OnHelp,         -- to show help
  }
  mapper.mapprint (string.format ("[%s version %0.1f]", GetPluginName(), GetPluginInfo (GetPluginID (), 19)))
  mapper.mapprint (string.format ("MUSHclient mapper installed, version %0.1f", mapper.VERSION))

  local rooms_count = 0
  local explored_exits_count = 0
  local unexplored_exits_count = 0

  for uid, room in pairs (rooms) do
    rooms_count = rooms_count + 1
    for dir, exit_uid in pairs (room.exits) do
      if exit_uid == '0' then
        unexplored_exits_count = unexplored_exits_count + 1
      else
        explored_exits_count = explored_exits_count + 1
      end -- if
    end -- for each exit
  end -- for each room

  mapper.mapprint (string.format (
        "Mapper database loaded: %d rooms, %d explored exits, %d unexplored exits.",
         rooms_count, explored_exits_count, unexplored_exits_count))

  OnPluginWorldOutputResized ()

 -- find where window was last time

  windowinfo = movewindow.install (learn_window, miniwin.pos_center_right)

  learnFontName = get_preferred_font {"Dina",  "Lucida Console",  "Fixedsys", "Courier", "Sylfaen",}
  learnFontId = "f"
  learnFontSize = 9

  WindowCreate (learn_window,
                 windowinfo.window_left,
                 windowinfo.window_top,
                 LEARN_WINDOW_WIDTH,
                 LEARN_WINDOW_HEIGHT,
                 windowinfo.window_mode,   -- top right
                 windowinfo.window_flags,
                 ColourNameToRGB "lightcyan")

  WindowFont (learn_window, learnFontId, learnFontName, learnFontSize,
              true, false, false, false,  -- bold
              miniwin.font_charset_ansi, miniwin.font_family_any)

  -- find height of font for future calculations
  learn_font_height = WindowFontInfo (learn_window, font_id, 1)  -- height

  -- let them move it around
  movewindow.add_drag_handler (learn_window, 0, 0, 0, learn_font_height + 5)
  WindowRectOp (learn_window, miniwin.rect_fill, 0, 0, 0, learn_font_height + 5, ColourNameToRGB "darkblue", 0)
  draw_3d_box  (learn_window, 0, 0, LEARN_WINDOW_WIDTH, LEARN_WINDOW_HEIGHT)
  DIALOG_TITLE = "Learn line type"
  local width = WindowTextWidth (learn_window, learnFontId, DIALOG_TITLE, true)
  local x = (LEARN_WINDOW_WIDTH - width) / 2
  WindowText   (learn_window, learnFontId, DIALOG_TITLE, x, 3, 0, 0, ColourNameToRGB "white", true)

 -- close box
  local box_size = learn_font_height - 2
  local GAP = 5
  local y = 3
  local x = 1

  WindowRectOp (learn_window,
                miniwin.rect_frame,
                x + LEARN_WINDOW_WIDTH - box_size - GAP * 2,
                y + 1,
                x + LEARN_WINDOW_WIDTH - GAP * 2,
                y + 1 + box_size,
                0x808080)
  WindowLine (learn_window,
              x + LEARN_WINDOW_WIDTH - box_size - GAP * 2 + 3,
              y + 4,
              x + LEARN_WINDOW_WIDTH - GAP * 2 - 3,
              y - 2 + box_size,
              0x808080,
              miniwin.pen_solid, 1)
  WindowLine (learn_window,
              x - 4 + LEARN_WINDOW_WIDTH - GAP * 2,
              y + 4,
              x - 1 + LEARN_WINDOW_WIDTH - box_size - GAP * 2 + 3,
              y - 2 + box_size,
              0x808080,
              miniwin.pen_solid, 1)

  -- close configuration hotspot
  WindowAddHotspot(learn_window, "close_learn_dialog",
                   x + LEARN_WINDOW_WIDTH - box_size - GAP * 2,
                   y + 1,
                   x + LEARN_WINDOW_WIDTH - GAP * 2,
                   y + 1 + box_size,   -- rectangle
                   "", "", "", "", "mouseup_close_configure",  -- mouseup
                   "Click to close",
                   miniwin.cursor_hand, 0)  -- hand cursor


  -- the buttons for learning
  local LABEL_LEFT = 10
  local YES_BUTTON_LEFT = 100
  local NO_BUTTON_LEFT = YES_BUTTON_LEFT + LEARN_BUTTON_WIDTH + 20

  -- get the line types into my preferred order
  local sorted_line_types = { }
  for type_name in pairs (line_types) do
    table.insert (sorted_line_types, type_name)
  end -- for
  table.sort (sorted_line_types, function (a, b) return line_types [a].seq < line_types [b].seq end)

  local y = learn_font_height + 10
  for _, type_name in ipairs (sorted_line_types) do
    local type_info = line_types [type_name]
    WindowText   (learn_window, learnFontId, type_info.short, LABEL_LEFT, y + 8, 0, 0, ColourNameToRGB "black", true)

    make_button (learn_window, learnFontId, YES_BUTTON_LEFT, y, "Yes", "Learn selection IS " .. type_info.short,
                  function () learn_line_type (type_name, true) end)
    make_button (learn_window, learnFontId, NO_BUTTON_LEFT,  y, "No",  "Learn selection is NOT " .. type_info.short,
                  function () learn_line_type (type_name, false) end)

    y = y + LEARN_BUTTON_HEIGHT + 10

  end -- for

  WindowShow (learn_window, config.SHOW_LEARNING_WINDOW)
  WindowShow (mapper_win, config.SHOW_LEARNING_WINDOW)

  time_last_saved = os.time ()
  rooms_added = 0

end -- OnPluginInstall

-- -----------------------------------------------------------------
-- OnPluginClose
-- -----------------------------------------------------------------
function OnPluginClose ()
  WindowShow (learn_window, false)
  WindowShow (mapper_win, false)
  mapper.hide ()  -- hide the map
end -- OnPluginClose

-- -----------------------------------------------------------------
-- Plugin Save State
-- -----------------------------------------------------------------
function OnPluginSaveState ()
  mapper.save_state ()
  SetVariable ("corpus", "corpus = " .. serialize.save_simple (corpus))
  SetVariable ("stats", "stats = " .. serialize.save_simple (stats))
  SetVariable ("config", "config = " .. serialize.save_simple (config))
  SetVariable ("rooms",  "rooms = "  .. serialize.save_simple (rooms))
  SetVariable ("duplicates",  "duplicates = "  .. serialize.save_simple (duplicates))
  movewindow.save_state (learn_window)

  time_last_saved = os.time ()
  rooms_added = 0

  mapper.mapprint ("Mapping database saved.")

end -- OnPluginSaveState

local C1 = 2   -- weightings
local C2 = 1
local weight = 1
local MAX_WEIGHT = 2.0

-- calculate the probability one word is red or black
function CalcProbability (red, black)
 local pResult = ( (black - red) * weight )
                 / (C1 * (black + red + C2) * MAX_WEIGHT)
  return 0.5 + pResult
end -- CalcProbability


-- -----------------------------------------------------------------
-- update_corpus
--  add one to red or black for a certain value, for a certain type of line, for a certain marker type
-- -----------------------------------------------------------------
function update_corpus (which, marker, value, black)
  local which_corpus = corpus [which] [marker]
  -- make new one for this value if necessary
  if not which_corpus [value] then
     which_corpus [value] = { red = 0, black = 0, score = 0 }
  end -- end of this value not there yet
  if black then
     which_corpus [value].black = which_corpus [value].black + 1
  else
     which_corpus [value].red = which_corpus [value].red + 1
  end -- if
  which_corpus [value].score = assert (CalcProbability (which_corpus [value].red, which_corpus [value].black))
end -- update_corpus


-- -----------------------------------------------------------------
-- learn_line_type
--  The user is training a line type. Update the corpus for each line type to show that this set of
--  markers is/isn't in it.
-- -----------------------------------------------------------------
function learn_line_type (which, black)

  start_line = GetSelectionStartLine ()
  end_line = GetSelectionEndLine ()

  if start_line == 0 then
     WARNING ("No line(s) selected - select one or more lines (or part lines)")
     return
  end -- if

  if black then
    stats [which].is = stats [which].is + 1
  else
    stats [which].isnot = stats [which].isnot + 1
  end -- if

  -- do all lines in the selection
  for line = start_line, end_line do
    -- process all the marker types, and add 1 to the red/black counter for that particular marker
    for k, v in ipairs (markers) do
      local values = v.func (line) -- call handler to get values
      for _, value in ipairs (values) do
        update_corpus (which, v.marker, value, black)
      end -- for each value

    end -- for each type of marker
  end -- for each line

  -- INFO (string.format ("Selection is from %d to %d", start_line, end_line))

  local s = ":"
  if not black then
    s = ": NOT"
  end -- if

  -- INFO ("Selected lines " .. s .. " " .. which)

  -- tprint (corpus)

  Pause (false)

end -- learn_line_type

--   See:
--     http://www.paulgraham.com/naivebayes.html
--   For a good explanation of the background, see:
--     http://www.mathpages.com/home/kmath267.htm.

-- -----------------------------------------------------------------
-- SetProbability
-- calculate the probability a bunch of markers are ham (black)
--  using an array of probabilities, get an overall one
-- -----------------------------------------------------------------
function SetProbability (probs)
  local n, inv = 1, 1
  local i = 0
  for k, v in pairs (probs) do
    n = n * v
    inv = inv * (1 - v)
    i = i + 1
  end
  return  n / (n + inv)
end -- SetProbability

-- DO NOT DEBUG TO THE OUTPUT WINDOW IN THIS FUNCTION!
-- -----------------------------------------------------------------
-- analyse_line
-- work out type of line by comparing its markers to the corpus
-- -----------------------------------------------------------------
function analyse_line (line)
  local result = {}
  local line_type_probs = {}
  local marker_values = { }

  if Trim (GetLineInfo (line, 1)) == "" then
    return nil
  end -- if blank line

  -- get the values first, they will stay the same for all line types
  for _, m in ipairs (markers) do
    marker_values [m.marker] = m.func (line) -- call handler to get values
  end -- for each type of marker

  for line_type, line_type_info in pairs (line_types) do
     -- don't if they don't want Bayesian deduction for this type
    if not do_not_deduce_linetypes [line_type] and not line_is_not_line_type [line_type] then
      local probs = { }
      for _, m in ipairs (markers) do
        marker_probs = { }  -- probability for this marker
        local values = marker_values [m.marker] -- get previously-retrieved values
        for _, value in ipairs (values) do
          local corpus_value = corpus [line_type] [m.marker] [value]
          if corpus_value then
            assert (type (corpus_value) == 'table', 'corpus_value not a table')
            --table.insert (probs, corpus_value.score)
            table.insert (marker_probs, corpus_value.score)
          end -- of having a value
        end -- for each value
        table.insert (probs, SetProbability (marker_probs))
      end -- for each type of marker
      local score = SetProbability (probs)
      table.insert (result, string.format ("%s: %3.2f", line_type_info.short, score))
      local first_word = (string.match (GetLineInfo(line, 1), "^%s*(%a+)") or ""):lower ()

      if line_type ~= 'exits' or
        (not config.EXIT_LINES_START_WITH_DIRECTION) or
        valid_direction [first_word] then
          table.insert (line_type_probs, { line_type = line_type, score = score } )
      end -- if
    end -- allowed to deduce this line type
  end -- for each line type
  table.sort (line_type_probs, function (a, b) return a.score > b.score end)
  if line_type_probs [1].score > PROBABILITY_CUTOFF then
    return line_type_probs [1].line_type, line_type_probs [1].score
  else
    return nil
  end -- if
end -- analyse_line

-- -----------------------------------------------------------------
-- fixuid
-- shorten a UID for display purposes
-- -----------------------------------------------------------------
function fixuid (uid)
  if not uid then
    return "NO_UID"
  end -- if nil
  return uid:sub (1, config.UID_SIZE)
end -- fixuid

function get_unique_styles (styles)
  local t = { }
  for k, v in ipairs (styles) do
    local s = string.format ("%d/%d/%d", v.textcolour, v.backcolour, v.style)
    if not t[s] then
      t [s] = v
    end -- if not there
  end -- for each supplied style

  local result = { }
  for k, v in pairs (t) do
    if v.textcolour == nil then
      tprint (v)
    end -- if
    table.insert (result, { fore = v.textcolour, back = v.backcolour, style = v.style } )
  end -- for each unique style
  return result
end -- get_unique_styles

-- -----------------------------------------------------------------
-- process_new_room
-- we have an exit line - work out where we are and what the exits are
-- -----------------------------------------------------------------
function process_new_room ()

  local from_room = get_from_room ("process_new_room")

  if override_contents ['description'] then
    description = override_contents ['description']
    description_styles = { }
  end -- if
  if override_contents ['exits'] then
    exits_str = override_contents ['exits']:lower ()
    exits_styles = { }
  end -- if
  if override_contents ['room_name'] then
    room_name = override_contents ['room_name']
    room_name_styles = { }
  end -- if

  if not description then
    if override_uid then
      description = "(none)"
    else
      WARNING "No description for this room"
      return
    end -- if
  end -- if no description

  if not exits_str then
    WARNING "No exits for this room"
    return
  end -- if no exits string

  if from_room and get_last_direction_moved () then
    local last_desc = "Unknown"
    if rooms [from_room] then
      desc = rooms [from_room].desc
    end -- if
    if last_desc == description then
      mapper.mapprint ("Warning: You have moved from a room to one with an identical description - the mapper may get confused.")
    end -- if

  end -- if moved from somewhere

  if config.SORT_EXITS then
    -- get all the exit words, exclude other crap, put them in a table, and sort it
    -- this is for MUDs that put markers after exit words to show if you have explored that way or not
    -- it is also to deal with MUDs that might sort the exits into different orders for some reason
    local t_exits = { }
    for exit in string.gmatch (exits_str, "%w+") do
      local ex = valid_direction [exit]
      if ex then
        table.insert (t_exits, ex)
      end -- if
    end -- for
    table.sort (t_exits)
    exits_str = table.concat (t_exits, " ")
  end -- if

  -- generate a "room ID" by hashing the room description and possibly the exits
  -- or, if supplied the override UID
  if override_uid then
    uid = utils.tohex (utils.md5 (override_uid))
  -- description / name / exits
  elseif config.INCLUDE_EXITS_IN_HASH and config.INCLUDE_ROOM_NAME_IN_HASH and room_name then
    uid = utils.tohex (utils.md5 (description .. exits_str .. room_name))
  -- description / exits
  elseif config.INCLUDE_EXITS_IN_HASH then
    uid = utils.tohex (utils.md5 (description .. exits_str))
  -- description / name
  elseif config.INCLUDE_ROOM_NAME_IN_HASH and room_name then
    uid = utils.tohex (utils.md5 (description .. room_name))
  else
  -- description only
    uid = utils.tohex (utils.md5 (description))
  end -- if

  uid = uid:sub (1, 25)
  local duplicate = nil

  current_room_hash = uid   -- in case of duplicate rooms

  -- is this a known duplicate room?
  if duplicates [current_room_hash] then
    INFO ("<<This is a duplicate room identified by hash " .. fixuid (uid) .. ">>")
    -- yes, so disregard the uid and work out where we came from

    if not (from_room and get_last_direction_moved ()) then
      -- make up some non-existent UID and give up
      uid = UNKNOWN_DUPLICATE_ROOM
      INFO ("Hit a duplicate room, but don't know where we came from, giving up.")
    else
      -- the UID is known to the room that led to this
      uid = rooms [from_room].exits [get_last_direction_moved ()]
      if not uid or uid == "0" then
        uid = UNKNOWN_DUPLICATE_ROOM
        INFO ("No exit known going " .. get_last_direction_moved ()  .. " from " .. fixuid (from_room))
      elseif duplicates [uid] then
        uid = UNKNOWN_DUPLICATE_ROOM
        INFO ("Hit a duplicate room, disregarding " .. get_last_direction_moved ()  .. " exit from " .. fixuid (from_room))
      end -- if
    end -- if we don't know where we came from

  end -- if

  if uid == UNKNOWN_DUPLICATE_ROOM and from_room and get_last_direction_moved () then
    INFO ("Entering unknown duplicate room - querying whether to make a new room here")
    local a, b, c = get_last_direction_moved (), fixuid (from_room), fixuid (current_room_hash)
    local answer = utils.msgbox (string.format ("Entering duplicate room %s, make new room leading %s from %s?",
                    fixuid (current_room_hash), get_last_direction_moved (), fixuid (from_room)),
            "Duplicate room", "yesno", "?", 1)
    INFO (string.format ("Response to query: Make a new room leading %s from %s to %s (duplicate)?: %s",
          a, b, c, answer))
    if answer == "yes" then
      uid = utils.tohex (utils.md5 (string.format ("%0.9f/%0.9f/%0.9f/%d",
                              math.random (), math.random (), math.random (), os.time ()))):sub (1, 25)
      rooms [from_room].exits [get_last_direction_moved ()] = uid
      INFO (string.format ("Adding new room with random UID (%s) leading %s from %s", fixuid (uid), get_last_direction_moved (), fixuid (from_room)))
      duplicate = current_room_hash
    end -- if

  end -- if

  if uid == UNKNOWN_DUPLICATE_ROOM then
    set_from_room (nil)
    from_room = nil  -- local copy
  end -- if we don't know where we are

  if config.SHOW_ROOM_AND_EXITS then
    INFO (string.format ("Description:\n'%s'\nExits: '%s'\nHash: %s", description, exits_str, fixuid (uid)))
  end -- if config.SHOW_ROOM_AND_EXITS

  if uid == UNKNOWN_DUPLICATE_ROOM then
    desc = "Unknown duplicate room"
    exits_str = ""
    room_name = "Unknown duplicate of " .. fixuid (current_room_hash)
  end -- if

  -- break up exits into individual directions
  local exits = {}

  -- for each word in the exits line, which happens to be an exit name (eg. "north") add to the table
  for exit in string.gmatch (exits_str, "%w+") do
    local ex = valid_direction [exit]
    if ex then
      exits [ex] = "0"  -- don't know where it goes yet
    end -- if
  end -- for


  -- add room to rooms table if not already known
  if not rooms [uid] then
    INFO ("Mapper adding room " .. fixuid (uid))
    rooms [uid] = {
        desc = description,
        exits = exits,
        area = area_name or WorldName (),
        name = room_name or fixuid (uid),
        duplicate = duplicate,   -- which UID, if any, this is a duplicate of
        } -- end of new room table

    if config.SAVE_LINE_INFORMATION then
      rooms [uid].styles = {
                           name   = get_unique_styles (room_name_styles),
                           exits  = get_unique_styles (exits_styles),
                           desc   = get_unique_styles (description_styles),
                           } -- end of styles
    end -- if

    rooms_added = rooms_added + 1
  else
    -- room there - add exits not known
    for dir in pairs (exits) do
      if not rooms [uid].exits [dir] then
        rooms [uid].exits [dir]  = "0"
        INFO ("Adding exit", dir)
      end -- if exit not there
    end -- for each exit we now about *now*

    -- remove exits that don't exist
    for dir in pairs (rooms [uid].exits) do
      if not exits [dir] then
        INFO ("Removing exit", dir)
        rooms [uid].exits [dir] = nil
      end -- if
    end -- for each exit in the existing room
  end -- if

  -- update room name if possible
  if room_name then
    rooms [uid].name = room_name
  end -- if

  INFO ("We are now in room " .. fixuid (uid))
  -- INFO ("Description: ", description)

  -- save so we know current room later on
  set_current_room (uid)

  -- show what we believe the current exits to be
  for dir, dest in pairs (rooms [uid].exits) do
    local probable = ''
    if dest == '0' then
      exit_uid = find_probable_room (uid, dir)
      if exit_uid then
        probable = ' (Probably ' .. fixuid (exit_uid) .. ')'
      end -- if
    end -- if
    INFO ("Exit: " .. dir .. " -> " .. fixuid (dest) .. probable)
  end -- for

  -- try to work out where previous room's exit led
  if get_last_direction_moved () and
     expected_exit ~= uid and
     from_room and uid ~= UNKNOWN_DUPLICATE_ROOM then
    fix_up_exit ()
  end -- exit was wrong

  -- warn them to explore nearby rooms
  if rooms [uid].duplicate then
    local unexplored = { }
    for dir, dest in pairs (rooms [uid].exits) do
      if dest == "0" then
        table.insert (unexplored, dir:upper ())
      end -- not explored
    end -- for each exit
    if #unexplored > 0 then
      local s = 's'
      local u = ' until none left'
      if #unexplored == 1 then
        s = ''
        u = ''
      end -- if
      mapper.mapprint ("Inside duplicated room. Please explore exit" .. s .. ": " ..
                      table.concat (unexplored, ", ") ..
                      " and then return here" .. u)
    end -- if
  end -- if

  -- call mapper to draw this room
  mapper.draw (uid)
  last_drawn_id = uid    -- in case they change the window size

  -- emergency fallback to stop lots of errors
  if not deduced_line_types [line_number] then
    deduced_line_types [line_number] = { }
  end -- if

  deduced_line_types [line_number].draw = true
  deduced_line_types [line_number].uid = get_current_room_ ("process_new_room")

  DEBUG "Finished processing new room"

  room_name = nil
  exits_str = nil
  description = nil
  set_last_direction_moved (nil)
  ignore_received = false
  override_line_type = nil
  override_line_contents = nil
  override_uid = nil
  line_is_not_line_type = { }
  override_contents = { }
  description_styles = { }
  exits_styles = { }
  room_name_styles = { }

end -- process_new_room


-- -----------------------------------------------------------------
-- mapper 'get_room' callback - it wants to know about room uid
-- -----------------------------------------------------------------

function get_room (uid)

  if not rooms [uid] then
   return nil
  end -- if

  local room = copytable.deep (rooms [uid])

  local texits = {}
  for dir,dest in pairs (room.exits) do
    table.insert (texits, dir .. " -> " .. fixuid (dest))
  end -- for
  table.sort (texits)

  -- get first sentence of description
  local desc = room.desc
  if desc:sub (1, #room.name) == room.name then
    desc = desc:sub (#room.name + 1)
  end -- if
  desc = Trim ((string.match (desc, "^[^.]+") or desc) .. ".")
  if room.name and not string.match (room.name, "^%x+$") then
    -- desc = room.name
  end -- if

  local textras = { }
  if room.Bank then
    table.insert (textras, "Bank")
  end -- if
  if room.Shop then
    table.insert (textras, "Shop")
  end -- if
  if room.Trainer then
    table.insert (textras, "Trainer")
  end -- if
  local extras = ""
  if #textras then
    extras = "\n" .. table.concat (textras, ", ")
  end -- if extras

  local notes = ""
  if room.notes then
    notes = "\nNotes: " .. room.notes
  end -- if notes

  room.hovermessage = string.format (
       "%s\tExits: %s\nRoom: %s%s\n%s\n%s",
        room.name or "unknown",
        table.concat (texits, ", "),
        fixuid (uid),
        extras,
        desc,
        notes
      )

  room.borderpenwidth = 1 -- default

  if uid == current_room then
    room.bordercolour = config.OUR_ROOM_COLOUR.colour
    room.borderpenwidth = 2
  end -- not in this area

  room.fillbrush = miniwin.brush_null -- no fill

  -- special room fill colours

  if room.notes and room.notes ~= "" then
    room.fillcolour = config.BOOKMARK_FILL_COLOUR.colour
    room.fillbrush = miniwin.brush_solid
  elseif room.Shop then
    room.fillcolour = config.SHOP_FILL_COLOUR.colour
    room.fillbrush = miniwin.brush_fine_pattern
  elseif room.Trainer then
    room.fillcolour = config.TRAINER_FILL_COLOUR.colour
    room.fillbrush = miniwin.brush_fine_pattern
  elseif room.Bank then
    room.fillcolour = config.BANK_FILL_COLOUR.colour
    room.fillbrush = miniwin.brush_fine_pattern
  end -- if

  if room.duplicate then
    room.fillcolour = config.DUPLICATE_FILL_COLOUR.colour
    room.fillbrush = miniwin.brush_fine_pattern
  end -- if

  return room
end -- get_room

-- -----------------------------------------------------------------
-- We have changed rooms - work out where the previous room led to
-- -----------------------------------------------------------------

function fix_up_exit ()

  local current_room = get_current_room_ ("fix_up_exit")
  local from_room = get_from_room ("fix_up_exit")
  local last_direction_moved = get_last_direction_moved ("fix_up_exit")

  -- where we were before
  local room = rooms [from_room]

  INFO ("Exit from " .. fixuid (from_room) .. " in the direction " .. last_direction_moved .. " was previously " .. (fixuid (room.exits [last_direction_moved]) or "nowhere"))
  -- leads to here

  if from_room == current_room then
    WARNING ("Declining to set the exit " .. last_direction_moved .. " from this room to be itself")
  else
    room.exits [last_direction_moved] = current_room
    INFO ("Exit from " .. fixuid (from_room) .. " in the direction " .. last_direction_moved .. " is now " .. fixuid (current_room))
  end -- if

  -- do inverse direction as a guess
  local inverse = inverse_direction [last_direction_moved]
  if inverse and current_room then
    if duplicates [rooms [current_room].exits [inverse]] then
      rooms [current_room].exits [inverse] = '0'
    end -- if
    if rooms [current_room].exits [inverse] == '0' then
      rooms [current_room].exits [inverse] = from_room
      INFO ("Added inverse direction from " .. fixuid (current_room) .. " in the direction " .. inverse .. " to be " .. fixuid (from_room))
    end -- if
  end -- of having an inverse


  -- clear for next time
  set_last_direction_moved (nil)
  set_from_room (nil)

end -- fix_up_exit

-- -----------------------------------------------------------------
-- try to detect when we send a movement command
-- -----------------------------------------------------------------

function OnPluginSent (sText)

  local current_room = get_current_room_ ("OnPluginSent")

  if valid_direction [sText] then
    set_last_direction_moved (valid_direction [sText])
    INFO ("current_room =", fixuid (current_room))
    INFO ("Just moving", get_last_direction_moved ())
    if current_room and rooms [current_room] then
      expected_exit = rooms [current_room].exits [get_last_direction_moved ()]
      if expected_exit then
        set_from_room (current_room)
      end -- if
    INFO ("Expected exit for this in direction " .. get_last_direction_moved () .. " is to room", fixuid (expected_exit))
    end -- if
  end -- if
end -- function

-- -----------------------------------------------------------------
-- Callback to show part of the room description/name/notes, used by map_find
-- -----------------------------------------------------------------

FIND_OFFSET = 33

function show_find_details (uid)
  local this_room = rooms [uid]
  local target = this_room.desc
  local label = "Description: "
  local st, en = string.find (target:lower (), wanted, 1, true)
  -- not in description, try the name
  if not st then
    target = this_room.name
    label = "Room name: "
    st, en = string.find (target:lower (), wanted, 1, true)
    if not st then
      target = this_room.notes
      label = "Notes: "
      if target then
        st, en = string.find (target:lower (), wanted, 1, true)
      end -- if any notes
    end -- not found in the name
  end -- can't find the wanted text anywhere, odd


  local first, last
  local first_dots = ""
  local last_dots = ""

  for i = 1, #target do

    -- find a space before the wanted match string, within the FIND_OFFSET range
    if not first and
       target:sub (i, i) == ' ' and
       i < st and
       st - i <= FIND_OFFSET then
      first = i
      first_dots = "... "
    end -- if

    -- find a space after the wanted match string, within the FIND_OFFSET range
    if not last and
      target:sub (i, i) == ' ' and
      i > en and
      i - en >= FIND_OFFSET then
      last = i
      last_dots = " ..."
    end -- if

  end -- for

  if not first then
    first = 1
  end -- if
  if not last then
    last = #target
  end -- if

  mapper.mapprint (label .. first_dots .. Trim (string.gsub (target:sub (first, last), "\n", " ")) .. last_dots)

end -- show_find_details

-- -----------------------------------------------------------------
-- Find a room
-- -----------------------------------------------------------------

function map_find (name, line, wildcards)

  local room_ids = {}
  local count = 0
  wanted = (wildcards [1]):lower ()     -- NOT local

  -- scan all rooms looking for a simple match
  for k, v in pairs (rooms) do
     local desc = v.desc:lower ()
     local name = v.name:lower ()
     local notes = ""
     if v.notes then
       notes = v.notes:lower ()
      end -- if notes
     if string.find (desc, wanted, 1, true) or
        string.find (name, wanted, 1, true) or
        string.find (notes, wanted, 1, true) then
       room_ids [k] = true
       count = count + 1
     end -- if
  end   -- finding room

  -- see if nearby
  mapper.find (
    function (uid)
      local room = room_ids [uid]
      if room then
        room_ids [uid] = nil
      end -- if
      return room, next (room_ids) == nil
    end,  -- function
    show_vnums,  -- show vnum?
    count,      -- how many to expect
    false,      -- don't auto-walk
    show_find_details -- callback function
    )

end -- map_find

-- -----------------------------------------------------------------
-- mapper_show_bookmarked_room - callback to show a bookmark
-- -----------------------------------------------------------------
function mapper_show_bookmarked_room (uid)
  local this_room = rooms [uid]
  mapper.mapprint (this_room.notes)
end -- mapper_show_bookarked_room

-- -----------------------------------------------------------------
-- Find bookmarked rooms
-- -----------------------------------------------------------------
function map_bookmarks (name, line, wildcards)

  local room_ids = {}
  local count = 0

  -- scan all rooms looking for a simple match
  for k, v in pairs (rooms) do
    if v.notes and v.notes ~= "" then
      room_ids [k] = true
      count = count + 1
    end -- if
  end   -- finding room

  -- find such places
  mapper.find (
    function (uid)
      local room = room_ids [uid]
      if room then
        room_ids [uid] = nil
      end -- if
      return room, next (rooms) == nil  -- room will be type of info (eg. shop)
    end,  -- function
    show_vnums,  -- show vnum?
    count,       -- how many to expect
    false,       -- don't auto-walk
    mapper_show_bookmarked_room  -- callback function to show the room bookmark
    )

end -- map_bookmarks

-- -----------------------------------------------------------------
-- Go to a room
-- -----------------------------------------------------------------

function map_goto (name, line, wildcards)

  if not mapper.check_we_can_find () then
    return
  end -- if

  local wanted = wildcards [1]

  if not string.match (wanted, "^%x+$") then
    mapper.mapprint ("Room IDs are hex strings (eg. FC758) - you can specify a partial string")
    return
  end -- if

  local goto_uid, room = find_room_partial_uid (wanted)
  if not goto_uid then
    return
  end -- if not found

  local current_room = get_current_room_ ("map_goto")
  if current_room and goto_uid == current_room then
    mapper.mapprint ("You are already in that room.")
    return
  end -- if

  -- find desired room
  mapper.find (
    function (uid)
      return uid == goto_uid, uid == goto_uid
    end,  -- function
    show_vnums,  -- show vnum?
    1,          -- how many to expect
    true        -- just walk there
    )

end -- map_goto

-- -----------------------------------------------------------------
-- line_received - called by a trigger on all lines
--   work out its line type, and then handle a line-type change
-- -----------------------------------------------------------------

last_deduced_type = nil
saved_lines = { }
deduced_line_types = { }

function line_received (name, line, wildcards, styles)

  -- these need to be global, for use later on
  this_line = GetLinesInBufferCount()         -- which line in the output buffer
  line_number = GetLineInfo (this_line, 10)   -- which line this was overall

  local deduced_type, probability

  -- see if a plugin has overriden the line type
  if override_line_type then
    deduced_type = override_line_type
    if override_line_contents then
      line = override_line_contents
    end -- if new contents wanted
  else
    if (not config.BLANK_LINE_TERMINATES_LINE_TYPE) and Trim (line) == "" then
      return
    end -- if empty line

    if config.BLANK_LINE_TERMINATES_LINE_TYPE and Trim (line) == "" then
      deduced_type = nil
    else
      deduced_type, probability = analyse_line (this_line)
    end -- if

  end -- if

  -- record for scrollback buffer
  if deduced_type then
    deduced_line_types [line_number] = {
        lt = deduced_type,  -- what type we assigned to it
        con = probability,  -- with what probability
        draw = false,       -- did we draw on this line?
        ov = override_line_type,  -- was it overridden?
        }
  end -- if not nil type

  -- INFO ("This line is", deduced_type, "last type was", last_deduced_type)

  if deduced_type ~= last_deduced_type then

    -- deal with previous line type
    -- INFO ("Now handling", last_deduced_type)

    if last_deduced_type then
      line_types [last_deduced_type].handler (saved_lines)  -- handle the line(s)
    end -- if we have a type

    last_deduced_type = deduced_type
    saved_lines = { }
  end -- if line type has changed


  table.insert (saved_lines, { line = line, styles = styles } )

  -- if exits are on a single line, then we can process them as soon as we get them
  if config.EXITS_IS_SINGLE_LINE and deduced_type == 'exits' then
      -- INFO ("Now handling", deduced_type)
      line_types.exits.handler (saved_lines)  -- handle the line
      saved_lines = { }
      last_deduced_type = nil
  end -- if

  -- if prompt are on a single line, then we can process it as soon as we get it
  if config.PROMPT_IS_SINGLE_LINE and deduced_type == 'prompt' then
      -- INFO ("Now handling", deduced_type)
      line_types.prompt.handler (saved_lines)  -- handle the line
      saved_lines = { }
      last_deduced_type = nil
  end -- if

  -- reset back ready for next line
  line_is_not_line_type = { }
  override_line_type = nil

end -- line_received

-- -----------------------------------------------------------------
-- corpus_info - show how many times we trained the corpus
-- -----------------------------------------------------------------

function corpus_info ()
  mapper.mapprint  (string.format ("%20s %5s %5s", "Line type", "is", "not"))
  mapper.mapprint  (string.format ("%20s %5s %5s", string.rep ("-", 15), string.rep ("-", 5), string.rep ("-", 5)))
  for k, v in pairs (stats) do
    mapper.mapprint  (string.format ("%20s %5d %5d", k, v.is, v.isnot))
  end -- for each line type
  mapper.mapprint ("There are " .. count_values (corpus) .. " entries in the corpus.")
end -- corpus_info

-- -----------------------------------------------------------------
-- OnHelp - show help
-- -----------------------------------------------------------------
function OnHelp ()
  local p = mapper.mapprint
	mapper.mapprint (string.format ("[MUSHclient mapper, version %0.1f]", mapper.VERSION))
  p (string.format ("[%s version %0.1f]", GetPluginName(), GetPluginInfo (GetPluginID (), 19)))
  p (string.rep ("-", 78))
	p (GetPluginInfo (GetPluginID (), 3))
  p (string.rep ("-", 78))

  -- Tell them where to get the latest mapper plugin
  local old_note_colour = GetNoteColourFore ()
  SetNoteColourFore(config.MAPPER_NOTE_COLOUR.colour)

  Tell ("Lastest mapper plugin: ")
  Hyperlink ("https://github.com/nickgammon/plugins/blob/master/Learning_Mapper.xml",
             "Learning_Mapper.xml", "Click to see latest plugin", "darkorange", "", true)
  Tell (" and ")
  Hyperlink ("https://github.com/nickgammon/plugins/blob/master/Learning_Mapper.lua",
             "Learning_Mapper.lua", "Click to see latest plugin", "darkorange", "", true)
  p ""
  p ('You need both files. RH-click the "Raw" button on those pages to download the files.')
  Tell ('Save them to the folder: ')
  ColourNote ("orange", "", GetPluginInfo (GetPluginID (), 20))
  p (string.rep ("-", 78))
  SetNoteColourFore (old_note_colour)

end

-- -----------------------------------------------------------------
-- map_where - where is the specified room? (by uid)
-- -----------------------------------------------------------------
function map_where (name, line, wildcards)

  if not mapper.check_we_can_find () then
    return
  end -- if

  local wanted = wildcards [1]:upper ()

  if not string.match (wanted, "^%x+$") then
    mapper.mapprint ("Room IDs are hex strings (eg. FC758) - you can specify a partial string")
    return
  end -- if

  local where_uid, room = find_room_partial_uid (wanted)
  if not where_uid then
    return
  end -- if not found

  local current_room = get_current_room_ ("map_where")

  if current_room and where_uid == current_room then
    mapper.mapprint ("You are already in that room.")
    return
  end -- if

  local paths = mapper.find_paths (current_room,
           function (uid)
            return uid == where_uid, uid == where_uid
            end)

  local uid, item = next (paths, nil) -- extract first (only) path

  -- nothing? room not found
  if not item then
    mapper.mapprint (string.format ("Room %s not found", wanted))
    return
  end -- if

  -- turn into speedwalk
  local path = mapper.build_speedwalk (item.path)

  -- display it
  mapper.mapprint (string.format ("Path to %s (%s) is: %s", wanted, rooms [where_uid].name, path))

end -- map_where

-- -----------------------------------------------------------------
-- OnPluginPacketReceived - try to add newlines to prompts if wanted
-- -----------------------------------------------------------------
function OnPluginPacketReceived (pkt)

  if not config.ADD_NEWLINE_TO_PROMPT then
    return pkt
  end -- if

  -- add a newline to the end of a packet if it appears to be a simple prompt
  -- (just a ">" sign at the end of a line optionally followed by one space)
  if GetInfo (104) then  -- if MXP enabled
    if string.match (pkt, "&gt; ?$") then
      return pkt .. "\n"
    end -- if
  else
    if string.match (pkt, "> ?$") then  -- > symbol at end of packet
      return pkt .. "\n"
    elseif string.match (pkt, "> ?\027%[0m ?$") then -- > symbol at end of packet followed by ESC [0m
      return pkt .. "\n"
    end -- if
  end -- if MXP or not

  return pkt
end -- OnPluginPacketReceived

-- -----------------------------------------------------------------
-- show_corpus - show all values in the corpus, printed nicely
-- -----------------------------------------------------------------
function show_corpus ()

  -- start with each line type (eg. exits, descriptions)
  for name, type_info in pairs (line_types) do
    mapper.mapprint (string.rep ("=", 72))
    mapper.mapprint (type_info.short)
    mapper.mapprint (string.rep ("=", 72))
    corpus_line_type = corpus [name]
    -- for each one show each marker type (eg. first word, all words, colour)
    for _, marker in ipairs (markers) do
      mapper.mapprint ("  " .. string.rep ("-", 70))
      mapper.mapprint ("  " .. marker.desc)
      mapper.mapprint ("  " .. string.rep ("-", 70))
      local f = marker.show
      local accessing_function  = marker.accessing_function  -- pairs for numbers or pairsByKeys for strings
      if f then
        mapper.mapprint (string.format ("    %20s %5s %5s %7s", "Value", "Yes", "No", "Score"))
        mapper.mapprint (string.format ("    %20s %5s %5s %7s", "-------", "---", "---", "-----"))
        -- for each marker show each value, along with its counts for and against, and its calculated score
        for k, v in accessing_function (corpus_line_type [marker.marker], function (a, b) return a:lower () < b:lower () end ) do
          f (k, v)
        end -- for each value
      end -- if function exists
    end -- for each marker type
  end -- for each line type

end -- show_corpus

-- -----------------------------------------------------------------
-- show_styles - show a set of style runs summary
-- -----------------------------------------------------------------
function show_styles (name, styles)
  local p = mapper.mapprint

  p ""
  p (string.format ("%s styles:", name))
  p (string.format ("%-20s %-20s %-30s %s", "Foreground", "Background", "Styles", "Count"))
  p (string.format ("%-20s %-20s %-30s %s", "----------", "----------", "------", "-----"))
  for k, v in pairs (styles) do
    local fore, back, style = string.match (k, "^(%d+)/(%d+)/(%d+)$")
    local t = { }
    if bit.band (style, 1) ~= 0 then
      table.insert (t, "bold")
    end
    if bit.band (style, 2) ~= 0 then
      table.insert (t, "underline")
    end
    if bit.band (style, 4) ~= 0 then
      table.insert (t, "italic")
    end

    p (string.format ("%-20s %-20s %-30s %5d", RGBColourToName (fore), RGBColourToName (back), table.concat (t, ","), v))
  end -- for

end -- show_styles


-- -----------------------------------------------------------------
-- mapper_analyse - analyse the map database
-- -----------------------------------------------------------------
function mapper_analyse (name, line, wildcards)
  local min_name_length = 1e20
  local max_name_length = 0
  local total_name_length = 0
  local room_count = 0
  local min_name = ""
  local max_name = ""
  local name_styles = { }
  local desc_styles = { }
  local exits_styles = { }

  local function get_styles (this_style, all)
    if this_style then
      for k, v in ipairs (this_style) do
        local s = string.format ("%d/%d/%d", v.fore, v.back, v.style)
        if all [s] then
          all [s] = all [s] + 1
        else
          all [s] = 1
        end -- if
      end -- for
    end -- if styles exits
  end -- get_styles

  for uid, room in pairs (rooms) do
    -- don't bother getting the length of hex uids - that doesn't prove much
    if not string.match (room.name, "^%x+$") then
      local len = #room.name
      room_count = room_count + 1
      min_name_length = math.min (min_name_length, len)
      max_name_length = math.max (max_name_length, len)
      if len == min_name_length then
        min_name = room.name
      end
      if len == max_name_length then
        max_name = room.name
      end
      total_name_length = total_name_length + len
      end -- if not a hex room name

    -- now get the colours
    if room.styles then
      get_styles (room.styles.name, name_styles)
      get_styles (room.styles.desc, desc_styles)
      get_styles (room.styles.exits, exits_styles)
    end -- if we have some styles

  end -- for each room

  local p = mapper.mapprint
  mapper.mapprint (string.rep ("-", 78))

  p (string.format ("%20s %4d (%s)", "Minimum room name length", min_name_length, min_name))
  p (string.format ("%20s %4d (%s)", "Maximum room name length", max_name_length, max_name))
  if room_count > 0 then  -- no divide by zero
    p (string.format ("%20s %4d",      "Average room name length", total_name_length / room_count))
  end -- if

  if not config.SAVE_LINE_INFORMATION then
    mapper.mapprint ("WARNING: Option 'save_line_info' is not set.")
  end -- if

  show_styles ("Room name",   name_styles)
  show_styles ("Description", desc_styles)
  show_styles ("Exits",       exits_styles)

  mapper.mapprint (string.rep ("-", 78))

end -- mapper_analyse

-- -----------------------------------------------------------------
-- mapper_delete - delete a room from the database
-- -----------------------------------------------------------------
function mapper_delete (name, line, wildcards)
  local uid = wildcards [1]
  if #uid < 4 then
    mapper.maperror ("UID length must be at least 4 characters for deleting rooms")
    return
  end -- if too short

  delete_uid, room = find_room_partial_uid (uid)
  if not delete_uid then
    return
  end -- if not found

  mapper_show (delete_uid)
  rooms [delete_uid] = nil  -- delete it
  mapper.mapprint ("Room", delete_uid, "deleted.")

  -- remove any exit references to this room
  for uid, room in pairs (rooms) do
    for dir, dest in pairs (room.exits) do
      if dest == delete_uid then
        mapper.mapprint (string.format ("Setting exit %s from room %s to be unknown",
                          dest, fixuid (uid)))
        room.exits [dir] = '0'
      end -- if that exit pointed to the deleted room
    end -- for each exit
  end -- for each room

  -- redraw map
  if last_drawn_id then
    mapper.draw (last_drawn_id)
  end -- if

end -- mapper_delete

-- -----------------------------------------------------------------
-- uid_hyperlink - displays (with no newline) a hyperlink to a UID
-- -----------------------------------------------------------------
function uid_hyperlink (uid)
  Hyperlink ("!!" .. GetPluginID () .. ":mapper_show(" .. uid .. ")",
            fixuid (uid), "Click to show room details for " .. fixuid (uid), RGBColourToName (config.MAPPER_NOTE_COLOUR.colour), "", false)
end -- uid_hyperlink

-- -----------------------------------------------------------------
-- list_rooms_table - displays a list of rooms from the supplied table of uid/room pairs
-- -----------------------------------------------------------------
function list_rooms_table (t)
  table.sort (t, function (a, b) return a.room.name:upper () < b.room.name:upper () end )

  for _, v in ipairs (t) do
    local room = v.room
    local uid = v.uid
    uid_hyperlink (uid)
    mapper.mapprint (" ", room.name)
  end -- for each room

  if #t == 0 then
    mapper.mapprint "No matches."
  else
    local s = ""
    if #t > 1 then
      s = "es"
    end -- if
    mapper.mapprint (string.format ("%d match%s.", #t, s))
  end -- if

end -- list_rooms_table

-- -----------------------------------------------------------------
-- find_orphans - finds all rooms nothing leads to
-- -----------------------------------------------------------------
function find_orphans ()
  local orphans = { }
  -- add all rooms to orphans table
  for uid, room in pairs (rooms) do
    orphans [uid] = room
  end -- for

  -- now eliminate rooms which others point to
  for uid, room in pairs (rooms) do
    for dir, exit_uid in pairs (room.exits) do
      if exit_uid ~= "0" then
        orphans [exit_uid] = nil  -- not an orphan
      end -- if
    end -- for each exit
  end -- for
  local t = { }
  for uid, room in pairs (orphans) do
    table.insert (t, { uid = uid, room = room })
  end -- for
  list_rooms_table (t)
end -- find_orphans

-- -----------------------------------------------------------------
-- find_connect - finds all rooms that this one eventually leads to
-- -----------------------------------------------------------------
function find_connect (uid, room)
  local found = {  }
  local unexplored = { [uid] = true }

  while next (unexplored) do
    local new_ones= { }
    for uid in pairs (unexplored) do
      if not found [uid] then
        local room = rooms [uid]
        if room then
          found [uid] = true
          unexplored [uid] = nil  -- remove from unexplored list
          for dir, exit_uid in pairs (room.exits) do
            if not found [exit_uid] and not unexplored [exit_uid] then
              table.insert (new_ones, exit_uid)
            end -- if not noticed yet
          end -- for
        else
          unexplored [uid] = nil  -- doesn't exist, remove from list
        end -- if room exists
      end -- if not yet found
    end -- for each unexplored room
    for _, uid in ipairs (new_ones) do
      unexplored [uid] = true
    end -- for
  end -- while still some to go

  local t = { }

  for uid in pairs (found) do
    table.insert (t, { uid = uid, room = rooms [uid] } )
  end -- for each found room

  list_rooms_table (t)
end -- find_connect

-- -----------------------------------------------------------------
-- colour_finder - generic finder for name/description/exits
--                 foreground or background colours
-- -----------------------------------------------------------------
function  colour_finder (wanted_colour, which_styles, fore_or_back)
  local colour, colourRGB = config_validate_colour (wanted_colour)
  if not colour then
    return
  end -- if
  mapper_list_finder (function (uid, room)
    if room [which_styles] then
      for _, style in ipairs (room [which_styles]) do
        if style [fore_or_back] == colourRGB then
          return true
        end -- if wanted colour
      end -- for each style
    end -- if any style
    return false
   end)
end -- colour_finder

-- -----------------------------------------------------------------
-- find_room_partial_uid - find a room by partial ID
-- if multiples found, advises what they are
-- if none, gives an error and returns nil
-- otherwise returns the UID and the room info for that room
-- -----------------------------------------------------------------
function find_room_partial_uid (which)
  local t = { }
  which = which:upper ()
  for uid, room in pairs (rooms) do
    if string.match (uid, "^" .. which) then
      table.insert (t, { uid = uid, room = room })
    end -- if a partial match
  end -- for
  if #t == 0 then
    mapper.maperror ("Room UID", which, "is not known.")
    return nil, nil
  end -- if

  if #t > 1 then
    mapper.maperror ("Multiple matches for UID", which .. ":")
    list_rooms_table (t)
    return nil, nil
  end -- if

  return t [1].uid, t [1].room
end -- find_room_partial_uid

-- -----------------------------------------------------------------
-- mapper_list_finder - generic finder which adds a room if f() returns true
-- -----------------------------------------------------------------
function mapper_list_finder (f)
  local t = { }

  for uid, room in pairs (rooms) do
    if not f or f (uid, room) then
      table.insert (t, { uid = uid, room = room } )
    end -- if room wanted
  end -- for

  list_rooms_table (t)
end -- mapper_list_finder

-- -----------------------------------------------------------------
-- mapper_list - show or search the map database
-- -----------------------------------------------------------------
function mapper_list (name, line, wildcards)
  local first_wildcard = Trim (wildcards [1]):lower ()
  local name     = string.match (first_wildcard, "^name%s+(.+)$")
  local desc     = string.match (first_wildcard, "^desc%s+(.+)$")
  local notes    = string.match (first_wildcard, "^notes?%s+(.+)$")
  local area     = string.match (first_wildcard, "^areas?%s+(.+)$")
  local any_notes= string.match (first_wildcard, "^notes?$")
  local orphans  = string.match (first_wildcard, "^orphans?$")
  local lead_to  = string.match (first_wildcard, "^dest%s+(%x+)$")
  local connect  = string.match (first_wildcard, "^connect%s+(%x+)$")
  local shops    = string.match (first_wildcard, "^shops?$")
  local banks    = string.match (first_wildcard, "^banks?$")
  local trainers = string.match (first_wildcard, "^trainers?$")
  local dups     = string.match (first_wildcard, "^duplicates?$")
  local colour_name_fore  = string.match (first_wildcard, "^colou?r%s+name%s+fore%s+(.*)$")
  local colour_name_back  = string.match (first_wildcard, "^colou?r%s+name%s+back%s+(.*)$")
  local colour_desc_fore  = string.match (first_wildcard, "^colou?r%s+desc%s+fore%s+(.*)$")
  local colour_desc_back  = string.match (first_wildcard, "^colou?r%s+desc%s+back%s+(.*)$")
  local colour_exits_fore = string.match (first_wildcard, "^colou?r%s+exits?%s+fore%s+(.*)$")
  local colour_exits_back = string.match (first_wildcard, "^colou?r%s+exits?%s+back%s+(.*)$")
  local p = mapper.mapprint

  -- no wildcard? list all rooms
  if first_wildcard == "" then
    p ("All rooms")
    mapper_list_finder ()

  -- wildcard consists of hex digits and spaces? must be a uid list
  elseif string.match (first_wildcard, "^[%x ]+$") then
    first_wildcard = first_wildcard:upper ()  -- UIDs are in upper case
    if not string.match (first_wildcard, ' ') then
      local uid, room = find_room_partial_uid (first_wildcard)
      if not uid then
        return
      end -- if not found

      mapper_show (uid)
    else
      -- hex strings? room uids
      mapper_list_finder (function (uid, room)
        for w in string.gmatch (first_wildcard, "%x+") do
          if string.match (uid, "^" .. w) then
            return true
          end -- if
        end -- for each uid they wanted
        return false
      end )  -- function
    end -- if more than one uid

  -- wildcard is: name xxx
  elseif name then
    p (string.format ('Rooms whose name match "%s"', name))
    mapper_list_finder (function (uid, room) return string.find (room.name:lower (), name, 1, true) end)

  -- wildcard is: desc xxx
  elseif desc then
    p (string.format ('Rooms whose description matches "%s"', desc))
    mapper_list_finder (function (uid, room) return string.find (room.desc:lower (), desc, 1, true) end)

  -- wildcard is: notes xxx
  elseif notes then
    p (string.format ('Rooms whose notes match "%s"', notes))
    mapper_list_finder (function (uid, room) return room.notes and string.find (room.notes:lower (), notes, 1, true) end)

  -- wildcard is: area xxx
  elseif area then
    p (string.format ('Rooms whose area matches "%s"', area))
    mapper_list_finder (function (uid, room) return room.area and string.find (room.area:lower (), area, 1, true) end)

  -- wildcard is: notes
  -- (show all rooms with notes)
  elseif any_notes then
    p ("Rooms with notes")
    mapper_list_finder (function (uid, room) return room.notes end)

  -- wildcard is: shops
  elseif shops then
    p ("Rooms with shops")
    mapper_list_finder (function (uid, room) return room.Shop end)

  -- wildcard is: trainers
  elseif trainers then
    p ("Rooms with trainers")
    mapper_list_finder (function (uid, room) return room.Trainer end)

  -- wildcard is: banks
  elseif banks then
    p ("Rooms with banks")
    mapper_list_finder (function (uid, room) return room.Bank end)
  elseif dups then
    p ("Duplicate rooms")
    for duplicate_uid in pairs (duplicates) do
      p (string.rep ("-", 10))
      p ("Marked duplicate: " .. fixuid (duplicate_uid))
      mapper_list_finder (function (uid, room) return room.duplicate == duplicate_uid end)
    end -- for

  -- find orphan rooms (rooms no other room leads to)
  elseif orphans then
    p ("Orphaned rooms")
    find_orphans ()

  -- find rooms which this one eventually connects to
  elseif connect then
    local connect_uid, room = find_room_partial_uid (connect)
    if not connect_uid then
      return
    end -- if not found
    p (string.format ('Rooms which can be reached from "%s" (%s)', connect, room.name))
    t = find_connect (connect_uid, room)

  -- find rooms which have an exit leading to this one
  elseif lead_to then
    local lead_to_uid, room = find_room_partial_uid (lead_to)
    if not lead_to_uid then
      return
    end -- if not found
    p (string.format ("Rooms which have an exit to %s:", lead_to))
    mapper_list_finder (function (uid, room)
      for dir, exit_uid in pairs (room.exits) do
        if exit_uid == lead_to_uid then
          return true
        end -- if exit leads to this room
      end -- for each exit
      return false
      end)  -- finding function

  -- colour finding
  elseif colour_name_fore then
    p (string.format ("Rooms who have a name foreground style of %s:", colour_name_fore))
    colour_finder (colour_name_fore, 'name_styles', 'fore')
  elseif colour_name_back then
    p (string.format ("Rooms who have a name background style of %s:", colour_name_back))
    colour_finder (colour_name_back, 'name_styles', 'back')
  elseif colour_desc_fore then
    p (string.format ("Rooms who have a description foreground style of %s:", colour_desc_fore))
    colour_finder (colour_desc_fore, 'desc_styles', 'fore')
  elseif colour_desc_back then
    p (string.format ("Rooms who have a description background style of %s:", colour_desc_back))
    colour_finder (colour_desc_back, 'desc_styles', 'back')
  elseif colour_exits_fore then
    p (string.format ("Rooms who have a exits foreground style of %s:", colour_exits_fore))
    colour_finder (colour_exits_fore, 'exits_styles', 'fore')
  elseif colour_exits_back then
    p (string.format ("Rooms who have a exits background style of %s:", colour_exits_back))
    colour_finder (colour_exits_back, 'exits_styles', 'back')

  else
    mapper.maperror ("Do not understand 'list' command:", first_wildcard)
    p ("Options are:")
    p ("  mapper list")
    p ("  mapper list uid ...")
    p ("  mapper list name <name>")
    p ("  mapper list desc <description>")
    p ("  mapper list note <note>")
    p ("  mapper list area <area>")
    p ("  mapper list notes")
    p ("  mapper list orphans")
    p ("  mapper list dest <uid>")
    p ("  mapper list connect <uid>")
    p ("  mapper list shop")
    p ("  mapper list trainer")
    p ("  mapper list bank")
    p ("  mapper list colour name  fore <colour>")
    p ("  mapper list colour name  back <colour>")
    p ("  mapper list colour desc  fore <colour>")
    p ("  mapper list colour desc  back <colour>")
    p ("  mapper list colour exits fore <colour>")
    p ("  mapper list colour exits back <colour>")
    return
  end -- if

end -- mapper_list

-- -----------------------------------------------------------------
-- mapper_show - show one room
-- -----------------------------------------------------------------
function mapper_show (uid)
  local room = rooms [uid]
  if not room then
    mapper.maperror ("Room", uid, "is not known.")
    return
  end -- if

  local old_note_colour = GetNoteColourFore ()
  SetNoteColourFore(config.MAPPER_NOTE_COLOUR.colour)

  Note (string.rep ("-", 78))
  Note (string.format ("Room:  %s -> %s.", fixuid (uid), room.name))
  if room.duplicate then
    Note (string.format ("(Duplicate of %s)", fixuid (room.duplicate)))
  end -- if a duplicate
  Note (string.rep ("-", 78))
  Note (room.desc)
  Note (string.rep ("-", 78))
  Tell ("Exits: ")
  for dir,dest in pairs (room.exits) do
    Tell (dir:upper () .. " -> ")
    if dest == "0" then
      Tell "(Not explored)"
    else
      local dest_room = rooms [dest]
      if dest_room then
        uid_hyperlink (dest)
        Tell (" (" .. dest_room.name .. ")")
      else
        Tell (fixuid (dest) .. " (unknown)")
      end -- if dest_room
    end -- if
    Tell " "
  end -- for
  Note "" -- finish line
  if room.notes then
    Note (string.rep ("-", 78))
    Note (room.notes)
  end -- of having notes
  if room.Trainer or room.Shop or room.Bank then
    Note (string.rep ("-", 78))
    local t = { }
    if room.Bank then
      table.insert (t, "Bank")
    end -- if
    if room.Shop then
      table.insert (t, "Shop")
    end -- if
    if room.Trainer then
      table.insert (t, "Trainer")
    end -- if
    Note (table.concat (t, ", "))
  end -- of having notes
  Note (string.rep ("-", 78))

  SetNoteColourFore (old_note_colour)
end -- mapper_show

-- -----------------------------------------------------------------
-- mapper_config - display or change configuration options
-- Format is: mapper config <name> <value>  <-- change option <name> to <value>
--            mapper config                 <-- show all options
--            mapper config <name>          <-- show setting for one option
-- -----------------------------------------------------------------
function mapper_config (name, line, wildcards)
  local name = Trim (wildcards.name:lower ())
  local value = Trim (wildcards.value)

  -- no config item - show all existing ones
  if name == "" then
    mapper.mapprint ("All mapper configuration options")
    mapper.mapprint (string.rep ("-", 60))
    mapper.mapprint ("")
    for k, v in ipairs (config_control) do
      mapper.mapprint (string.format ("mapper config %-40s %s", v.name, v.show (config [v.option])))
    end
    mapper.mapprint ("")
    mapper.mapprint (string.rep ("-", 60))
    mapper.mapprint ('Type "mapper help" for more information about the above options.')

    -- training counts
    local count = 0
    for k, v in pairs (stats) do
      count = count + v.is + v.isnot
    end -- for each line type
    mapper.mapprint (string.format ("%s: %s.", "Number of times line types trained", count))

    -- hints on corpus info
    mapper.mapprint ('Type "mapper corpus info" for more information about line training.')
    mapper.mapprint ('Type "mapper learn" to toggle the training windows.')
    return false
  end -- no item given

  -- config name given - look it up in the list
  local config_item = validate_option (name, 'mapper config')
  if not config_item then
    return false
  end -- if no such option

  -- no value given - display the current setting of this option
  if value == "" then
    mapper.mapprint ("Current value for " .. name .. ":")
    mapper.mapprint ("")
    mapper.mapprint (string.format ("mapper config %s %s", config_item.name, config_item.show (config [config_item.option])))
    mapper.mapprint ("")
    return false
  end -- no value given

  -- validate new option value
  local new_value = config_item.validate (value)
  if new_value == nil then    -- it might be false, so we have to test for nil
    mapper.maperror ("Configuration option not changed.")
    return false
  end -- bad value

  -- set the new value and confirm it was set
  config [config_item.option] = new_value
  mapper.mapprint ("Configuration option changed. New value is:")
  mapper.mapprint (string.format ("mapper config %s %s", config_item.name, config_item.show (config [config_item.option])))
  return true
end -- mapper_config

-- -----------------------------------------------------------------
-- count_rooms - count how many rooms are in the database
-- -----------------------------------------------------------------
function count_rooms ()
  local count = 0
  for k, v in pairs (rooms) do
    count = count + 1
  end -- for
  return count
end -- count_rooms

-- -----------------------------------------------------------------
-- mapper_export - writes the rooms table to a file
-- -----------------------------------------------------------------
function mapper_export (name, line, wildcards)
  local filter = { lua = "Lua files" }

  local filename = utils.filepicker ("Export mapper map database", "Map_database " .. WorldName () .. ".lua", "lua", filter, true)
  if not filename then
    return
  end -- if cancelled
  local f, err = io.open (filename, "w")
  if not f then
    mapper.maperror ("Cannot open " .. filename .. " for output: " .. err)
    return
  end -- if not open

  local status, err = f:write ("rooms = "  .. serialize.save_simple (rooms) .. "\n")
  if not status then
    mapper.maperror ("Cannot write database to " .. filename .. ": " .. err)
  end -- if cannot write
  f:close ()
  mapper.mapprint ("Database exported, " .. count_rooms () .. " rooms.")
end -- mapper_export

-- -----------------------------------------------------------------
-- set_window_width - sets the mapper window width
-- -----------------------------------------------------------------
function set_window_width (name, line, wildcards)
  local size = tonumber (wildcards [1])
  if not size then
    mapper.maperror ("Bad size: " .. size)
    return
  end -- if

  if size < 200 or size > 1000 then
    mapper.maperror ("Size must be in the range 200 to 1000 pixels")
    return
  end -- if

  config.WINDOW.width = size
  mapper.mapprint ("Map window width set to", size, "pixels")
  if last_drawn_id then
    mapper.draw (last_drawn_id)
  end -- if
end -- set_window_width

-- -----------------------------------------------------------------
-- set_window_height - sets the mapper window height
-- -----------------------------------------------------------------
function set_window_height (name, line, wildcards)
  local size = tonumber (wildcards [1])
  if not size then
    mapper.maperror ("Bad size: " .. size)
    return
  end -- if

  if size < 200 or size > 1000 then
    mapper.maperror ("Size must be in the range 200 to 1000 pixels")
    return
  end -- if

  config.WINDOW.height = size
  mapper.mapprint ("Map window height set to", size, "pixels")
  if last_drawn_id then
    mapper.draw (last_drawn_id)
  end -- if
end -- set_window_height

-- -----------------------------------------------------------------
-- mapper_import - imports the rooms table from a file
-- -----------------------------------------------------------------
function mapper_import (name, line, wildcards)

  if count_rooms () > 0 then
    mapper.maperror ("Mapper database is not empty (there are " .. count_rooms () .. " rooms in it)")
    mapper.maperror ("Before importing another database, clear this one out with: mapper reset database")
    return
  end -- if

  local filter = { lua = "Lua files" }

  local filename = utils.filepicker ("Import mapper map database", "Map_database " .. WorldName () .. ".lua", "lua", filter, false)
  if not filename then
    return
  end -- if cancelled
  local f, err = io.open (filename, "r")
  if not f then
    mapper.maperror ("Cannot open " .. filename .. " for input: " .. err)
    return
  end -- if not open

  local s, err = f:read ("*a")
  if not s then
    mapper.maperror ("Cannot read database from " .. filename .. ": " .. err)
  end -- if cannot write
  f:close ()

  -- make a sandbox so they can't put Lua functions into the import file

  local t = {} -- empty environment table
  f = assert (loadstring (s))
  setfenv (f, t)
  -- load it
  f ()

  -- move the rooms table into our rooms table
  rooms = t.rooms
  mapper.mapprint ("Database imported, " .. count_rooms () .. " rooms.")

end -- mapper_import


-- -----------------------------------------------------------------
-- count_values - count how many values are in the database
-- -----------------------------------------------------------------
function count_values (t, done)
  local count = count or 0
  done = done or {}
  for key, value in pairs (t) do
    if type (value) == "table" and not done [value] then
      done [value] = true
      count = count + count_values (value, done)
    elseif key == 'score' then
      count = count + 1
    end
  end
  return count
end -- count_values

-- -----------------------------------------------------------------
-- corpus_export - writes the corpus table to a file
-- -----------------------------------------------------------------
function corpus_export (name, line, wildcards)
  local filter = { lua = "Lua files" }

  local filename = utils.filepicker ("Export map corpus", "Map_corpus " .. WorldName () .. ".lua", "lua", filter, true)
  if not filename then
    return
  end -- if cancelled
  local f, err = io.open (filename, "w")
  if not f then
    corpus.maperror ("Cannot open " .. filename .. " for output: " .. err)
    return
  end -- if not open

  local status, err = f:write ("corpus = "  .. serialize.save_simple (corpus) .. "\n")
  if not status then
    mapper.maperror ("Cannot write corpus to " .. filename .. ": " .. err)
  end -- if cannot write
  f:close ()
  mapper.mapprint ("Corpus exported, " .. count_values (corpus) .. " entries.")
end -- corpus_export


-- -----------------------------------------------------------------
-- corpus_import - imports the corpus table from a file
-- -----------------------------------------------------------------
function corpus_import (name, line, wildcards)

  if count_values (corpus) > 0 then
    mapper.maperror ("Corpus is not empty (there are " .. count_values (corpus) .. " entries in it)")
    mapper.maperror ("Before importing another corpus, clear this one out with: mapper reset corpus")
    return
  end -- if

  local filter = { lua = "Lua files" }

  local filename = utils.filepicker ("Import map corpus", "Map_corpus " .. WorldName () .. ".lua", "lua", filter, false)
  if not filename then
    return
  end -- if cancelled
  local f, err = io.open (filename, "r")
  if not f then
    mapper.maperror ("Cannot open " .. filename .. " for input: " .. err)
    return
  end -- if not open

  local s, err = f:read ("*a")
  if not s then
    mapper.maperror ("Cannot read corpus from " .. filename .. ": " .. err)
  end -- if cannot write
  f:close ()

  -- make a sandbox so they can't put Lua functions into the import file

  local t = {} -- empty environment table
  f = assert (loadstring (s))
  setfenv (f, t)
  -- load it
  f ()

  -- move the corpus table into our corpus table
  corpus = t.corpus
  mapper.mapprint ("Corpus imported, " .. count_values (corpus) .. " entries.")

end -- corpus_import

-- -----------------------------------------------------------------
-- room_toggle_trainer /  room_toggle_shop / room_toggle_bank
-- menu handlers to toggle trainers, shops, banks
-- -----------------------------------------------------------------
function room_toggle_trainer (room, uid)
  room.Trainer = not room.Trainer
  mapper.mapprint ("Trainer here: " .. config_display_boolean (room.Trainer))
end -- room_toggle_trainer

function room_toggle_shop (room, uid)
  room.Shop = not room.Shop
  mapper.mapprint ("Shop here: " .. config_display_boolean (room.Shop))
end -- room_toggle_shop

function room_toggle_bank (room, uid)
  room.Bank = not room.Bank
  mapper.mapprint ("Bank here: " .. config_display_boolean (room.Bank))
end -- room_toggle_bank

-- -----------------------------------------------------------------
-- room_edit_bookmark - menu handler to add, edit or remove a note
-- -----------------------------------------------------------------
function room_edit_bookmark (room, uid)

  local notes = room.notes
  local found = room.notes and room.notes ~= ""


  if found then
    newnotes = utils.inputbox ("Modify room comment (clear it to delete it)", room.name, notes)
  else
    newnotes = utils.inputbox ("Enter room comment (creates a note for this room)", room.name, notes)
  end -- if

  if not newnotes then
    return
  end -- if cancelled

  if newnotes == "" then
    if not found then
      mapper.mapprint ("Nothing, note not saved.")
      return
    else
      mapper.mapprint ("Note for room", uid, "deleted. Was previously:", notes)
      rooms [uid].notes = nil
      return
    end -- if
  end -- if

  if notes == newnotes then
    return -- no change made
  end -- if

  if found then
     mapper.mapprint ("Note for room", uid, "changed to:", newnotes)
   else
     mapper.mapprint ("Note added to room", uid, ":", newnotes)
   end -- if

   rooms [uid].notes = newnotes

end -- room_edit_bookmark

-- -----------------------------------------------------------------
-- room_edit_area - menu handler to edit the room area
-- -----------------------------------------------------------------
function room_edit_area (room, uid)

  local area = room.area


  newarea = utils.inputbox ("Modify room area name", room.name, area)

  if not newarea then
    return
  end -- if cancelled

  if newarea == "" then
    mapper.mapprint ("Area not changed.")
    return
  end -- if

  if area == newarea then
    return -- no change made
  end -- if

   mapper.mapprint ("Area name for room", uid, "changed to:", newarea)

   rooms [uid].area = newarea

end -- room_edit_area


-- -----------------------------------------------------------------
-- room_delete_exit - menu handler to delete an exit
-- -----------------------------------------------------------------
function room_delete_exit (room, uid)

local available =  {
  n = "North",
  s = "South",
  e = "East",
  w = "West",
  u = "Up",
  d = "Down",
  ne = "Northeast",
  sw = "Southwest",
  nw = "Northwest",
  se = "Southeast",
  ['in'] = "In",
  out = "Out",
  }  -- end of available

  -- remove non-existent exits
  for k in pairs (available) do
    if room.exits [k] then
      available [k] = available [k] .. " --> " .. fixuid (room.exits [k])
    else
      available [k] = nil
    end -- if not a room exit
  end -- for

  if next (available) == nil then
    utils.msgbox ("There are no exits from this room.", "No exits!", "ok", "!", 1)
    return
  end -- not known

  local chosen_exit = utils.listbox ("Choose exit to delete", "Exits ...", available )
  if not chosen_exit then
    return
  end

  mapper.mapprint ("Deleted exit", available [chosen_exit], "from room", uid, "from mapper.")

  -- update in-memory table
  rooms [uid].exits [chosen_exit] = nil

  local current_room = get_current_room_ ("room_delete_exit")

  mapper.draw (current_room)
  last_drawn_id = current_room    -- in case they change the window size

end -- room_delete_exit

-- -----------------------------------------------------------------
-- room_show_description - menu handler to show the room description
-- -----------------------------------------------------------------
function room_show_description (room, uid)

  local font_name = GetInfo (20) -- output window font
  local font_size = GetOption "output_font_height"
  local output_width  = GetInfo (240)  -- average width of pixels per character
  local wrap_column   = GetOption ('wrap_column')
  local _, lines = string.gsub (room.desc, "\n", "x") -- count lines

  local font_height = WindowFontInfo (mapper_win, font_id, 1)  -- height

  utils.editbox ("", "Description of " .. room.name, string.gsub (room.desc, "\n", "\r\n"), font_name, font_size,
                { read_only = true,
                box_width  = output_width * wrap_column + 100,
                box_height  = font_height * (lines + 1) + 120,
                reply_width = output_width * wrap_column + 10,
                -- cancel_button_width = 1,
                prompt_height = 1,
                 } )

end -- room_show_description

-- -----------------------------------------------------------------
-- room_connect_exit - menu handler to connect an exit to another room
-- -----------------------------------------------------------------
function room_connect_exit  (room, uid, dir)
  -- find what room they want to connect to
  local response = utils.inputbox ("Enter UID of room which is " .. dir:upper () .. " of here", "Connect exit")
  if not response then
    return
  end -- cancelled

  -- get rid of spaces, make upper-case
  response = Trim (response):upper ()

  -- validate
  if not string.match (response, "^%x%x%x+$") then
    mapper.maperror ("Destination room UID must be a hexadecimal string")
    return
  end -- if

  -- check it exists
  dest_uid = find_room_partial_uid (response)

  if not dest_uid then
    return  -- doesn't exist
  end -- if

  if duplicates [dest_uid] then
    mapper.maperror ("Cannot connect to a room marked as a duplicate")
    return
  end -- if

  if uid == dest_uid then
    mapper.maperror ("Cannot connect to a room to itself")
    return
  end -- if

  room.exits [dir] = dest_uid

  INFO (string.format ("Exit %s from %s now connects to %s",
      dir:upper (), fixuid (uid), fixuid (dest_uid)))

  local inverse = inverse_direction [dir]
  if inverse then
    rooms [dest_uid].exits [inverse] = uid
    INFO ("Added inverse direction from " .. fixuid (dest_uid) .. " in the direction " .. inverse .. " to be " .. fixuid (uid))
  end -- of having an inverse


end -- room_connect_exit

function room_copy_uid (room, uid)
  SetClipboard (uid)
  mapper.mapprint (string.format ("UID %s (in full: %s) now on the clipboard", fixuid (uid), uid))
end -- room_copy_uid

-- -----------------------------------------------------------------
-- room_click - RH-click on a room
-- -----------------------------------------------------------------
function room_click (uid, flags)

  -- check we got room at all
  if not uid then
    return nil
  end -- if

  -- look it up
  local room = rooms [uid]

  if not room then
    return
  end -- if still not there

  local notes_desc = "Add note"
  if room.notes then
    notes_desc = "Edit note"
  end -- if

  local handlers = {
      { name = notes_desc, func = room_edit_bookmark} ,
      { name = "Edit area", func = room_edit_area } ,
      { name = "Show description", func = room_show_description} ,
      { name = "-", } ,
      { name = "Trainer", func = room_toggle_trainer, check_item = true} ,
      { name = "Shop",    func = room_toggle_shop,    check_item = true} ,
      { name = "Bank",    func = room_toggle_bank,    check_item = true} ,
      { name = "-", } ,
      { name = "Copy UID", func = room_copy_uid } ,
      { name = "-", } ,
      } -- handlers

  local count = 0
  for dir, dest in pairs (room.exits) do
    if dest == '0' then
      table.insert (handlers, { name = "Connect " .. dir:upper () .. " exit",
        func = function ()
          return room_connect_exit (room, uid, dir)
        end -- factory function
      } )
      count = count + 1
    end -- if not known
  end -- for
  if count > 0 then
    table.insert (handlers, { name = "-" })
  end --if we had any

  table.insert (handlers, { name = "Delete an exit", func = room_delete_exit} )

  local t, tf = {}, {}
  for _, v in pairs (handlers) do
    local name = v.name
    if v.check_item then
      if room [name] then
        name = "+" .. name
      end -- if
    end -- if need to add a checkmark
    table.insert (t, name)
    tf [v.name] = v.func
  end -- for

  local choice = WindowMenu (mapper.mapper_win,
                            WindowInfo (mapper.mapper_win, 14),
                            WindowInfo (mapper.mapper_win, 15),
                            table.concat (t, "|"))

  -- find their choice, if any (empty string if cancelled)
  local f = tf [choice]

  if f then
    f (room, uid)
    current_room = get_current_room_ ("room_click")
    mapper.draw (current_room)
    last_drawn_id = current_room    -- in case they change the window size
  end -- if handler found


end -- room_click

-- -----------------------------------------------------------------
-- Find a with a special attribute which f(room) will return true if it exists
-- -----------------------------------------------------------------

function map_find_special (f)

  local room_ids = {}
  local count = 0

  -- scan all rooms looking for a match
  for uid, room in pairs (rooms) do
     if f (room) then
       room_ids [uid] = true
       count = count + 1
     end -- if
  end   -- finding room

  -- see if nearby
  mapper.find (
    function (uid)
      local room = room_ids [uid]
      if room then
        room_ids [uid] = nil
      end -- if
      return room, next (room_ids) == nil
    end,  -- function
    show_vnums,  -- show vnum?
    count,      -- how many to expect
    false       -- don't auto-walk
    )

end -- map_find_special

-- -----------------------------------------------------------------
-- mapper_peek - draw the map as if you were at uid
-- -----------------------------------------------------------------
function mapper_peek (name, line, wildcards)
  local uid = wildcards [1]

  peek_uid, room = find_room_partial_uid (uid)
  if not peek_uid then
    return
  end -- if not found

  mapper.draw (peek_uid)
  last_drawn_id = peek_uid    -- in case they change the window size

end -- mapper_peek

-- -----------------------------------------------------------------
-- map_shops - find nearby shops
-- -----------------------------------------------------------------
function map_shops (name, line, wildcards)
  map_find_special (function (room) return room.Shop end)
end -- map_shops

-- -----------------------------------------------------------------
-- map_trainers - find nearby trainers
-- -----------------------------------------------------------------
function map_trainers (name, line, wildcards)
  map_find_special (function (room) return room.Trainer end)
end -- map_trainers


-- -----------------------------------------------------------------
-- map_banks - find nearby banks
-- -----------------------------------------------------------------
function map_banks (name, line, wildcards)
  map_find_special (function (room) return room.Bank end)
end -- map_banks

-- -----------------------------------------------------------------
-- mark_duplicate_room - mark the current room as a duplicate UID
-- -----------------------------------------------------------------
function mark_duplicate_room (name, line, wildcards)
  if not current_room_hash then
   mapper.maperror ("We don't know where we are, try LOOK")
   return
  end -- if

  if rooms [current_room_hash] then
    rooms [current_room_hash] = nil  -- delete it
    mapper.mapprint ("Room", current_room_hash, "deleted.")
  end -- if

  duplicates [current_room_hash] = true -- this is a duplicated room
  mapper.mapprint (string.format ("Room %s now marked as being a duplicated one", fixuid (current_room_hash)))
  set_current_room (nil)  -- throw away incorrect UID
  set_from_room (nil)
  set_last_direction_moved (nil)

  mapper.draw (UNKNOWN_DUPLICATE_ROOM)  -- draw with unknown room

end -- mark_duplicate_room

-- -----------------------------------------------------------------
-- mapper_integrity - integrity check of exits
-- -----------------------------------------------------------------
function mapper_integrity (name, line, wildcards)
  local p = mapper.mapprint
  local repair = Trim (wildcards [1]) == 'repair'

  p("Mapper integrity check")
  local t = { }  -- table of rooms that have connections
  for uid, room in pairs (rooms) do
    for dir, dest in pairs (room.exits) do
      if rooms [dest] then
        -- check for inverse exits
        local dest_room = rooms [dest]
        local inverse = inverse_direction [dir]
        if inverse then
          if dest_room.exits [inverse] ~= uid then
            p(string.format ("Room %s exit %s leads to %s, however room %s exit %s leads to %s",
                fixuid (uid), dir, fixuid (dest), fixuid (dest), inverse, fixuid (dest_room.exits [inverse])))
            if repair then
              dest_room.exits [inverse] = uid
              p (string.format ("Changed %s exit %s to be %s", fixuid (dest), inverse, fixuid (uid)))
            end -- repair
          end -- if

        end -- if inverse exists

        -- add to table for exits that lead to this room
        if not t [dest] then
         t [dest] = { }
        end -- if destination not in table
        local dest_room = t [dest]
        if not dest_room [dir] then
          dest_room [dir] = { }
        end -- if not one from this direction yet
        table.insert (dest_room [dir], uid)
      end -- of the exit existing
    end -- for each exit

    -- see if duplicate UID not recorded
    if duplicates [uid] and not room.duplicate then
      p ("Room " .. fixuid (uid) .. " in duplicates list but we don't know what it is a duplicate of.")
    end -- if

  end -- for each room

  for dest, exits in pairs (t) do
    for dir, from in pairs (exits) do
      if #from > 1 then
        p(string.format ("Problem with exit %s leading to %s",
                         dir:upper (), fixuid (dest)))
        for _, v in ipairs (from) do
          p(string.format ("Room %s leads there",
                          fixuid (v)))
        end -- for each one
      end -- if more than one leads here
    end -- for each direction
  end -- for each destination room

  p "Done."

end -- mapper_integrity


-- based on mapper.find_paths
-- the intention of this is to find a room which is probably the one we want
-- for example, a room directly north of where we are

function find_probable_room (uid, dir)

  local function make_particle (curr_loc, prev_path)
    local prev_path = prev_path or {}
    return {current_room=curr_loc, path=prev_path}
  end

  local depth = 0
  local explored_rooms, particles = {}, {}

  local relative_location = {
    n  = { x =  0, y = -1 },
    s  = { x =  0, y =  1 },
    e  = { x =  1, y =  0 },
    w  = { x = -1, y =  0 },
    ne = { x =  1, y = -1 },
    se = { x =  1, y =  1 },
    nw = { x = -1, y = -1 },
    sw = { x = -1, y =  1 },
  } -- end of relative_location

  local offsets = relative_location [dir]
  if not offsets then
    return false
  end -- if not a n/s/e/w/ne/sw/se/sw
  local x_offset, y_offset = offsets.x, offsets.y

  -- create particle for the initial room
  table.insert (particles, make_particle (uid))

  while #particles > 0 and depth < config.SCAN.depth do

    -- create a new generation of particles
    local new_generation = {}
    depth = depth + 1

    -- process each active particle
    for i, part in ipairs (particles) do

      if not rooms [part.current_room] then
        rooms [part.current_room] = get_room (part.current_room)
      end -- if not in memory yet

      -- if room doesn't exist, forget it
      if rooms [part.current_room] then

        -- get a list of exits from the current room
        exits = rooms [part.current_room].exits

        -- create one new particle for each exit
        for dir, dest in pairs(exits) do

          -- if we've been in this room before, drop it
          if not explored_rooms[dest] then
            explored_rooms[dest] = true
            rooms [dest] = get_room (dest)  -- make sure this room in table
            if rooms [dest] then
              new_path = copytable.deep (part.path)
              table.insert(new_path, { dir = dir, uid = dest } )

              -- see if this is the wanted room
              local x, y = 0, 0
              for _, v in ipairs (new_path) do
                local this_offset = relative_location [v.dir]
                if not this_offset then  -- can't handle up/down/in/out
                  -- DEBUG ("Can't handle " .. v.dir)
                  break
                end -- if
                x = x + this_offset.x
                y = y + this_offset.y
                --DEBUG (string.format ("UID: %s, looking for %d, %d, got %d, %d",
                --       fixuid (v.uid), x_offset, y_offset, x, y))
                -- see if we got where we want to go
                if x == x_offset and y == y_offset then
                  return v.uid
                end -- if found
              end -- for each direction

              -- make a new particle in the new room
              table.insert(new_generation, make_particle(dest, new_path))
            end -- if room exists
          end -- not explored this room

        end  -- for each exit

      end -- if room exists

    end  -- for each particle

    particles = new_generation
  end   -- while more particles

  return false
end -- find_probable_room



-- -----------------------------------------------------------------
-- validate_linetype and  validate_option
-- helper functions for validating line types and option names
-- -----------------------------------------------------------------

function validate_linetype (which, func_name)
  if not line_types [which] then
    mapper.maperror ("Invalid line type '" .. which .. "' given to '" .. func_name .. "'")
    mapper.mapprint ("  Line types are:")
    for k, v in pairs (line_types) do
      mapper.mapprint ("    " .. k)
    end
    return false
  end -- not valid
  return true
end -- validate_linetype

function validate_option (which, func_name)
  -- config name given - look it up in the list
  local config_item = config_control_names [which]
  if not config_item then
    mapper.maperror ("Invalid config item name '" .. which .. "' given to '" .. func_name .. "'")
    mapper.mapprint ("  Configuration items are:")
    for k, v in ipairs (config_control) do
      mapper.mapprint ("    " .. v.name)
    end
    return false
  end -- config item not found
  return config_item
end -- validate_option

-- =================================================================
-- EXPOSED FUNCTIONS FOR OTHER PLUGINS TO CALL
-- =================================================================

-- -----------------------------------------------------------------
-- set_line_type - the current line is of type: linetype
-- linetype is one of: description, exits, room_name, prompt, ignore
-- optional contents lets you change what the contents are (eg. from "You are standing in a field" to "in a field")
-- -----------------------------------------------------------------
override_line_type = nil
override_line_contents = nil
function set_line_type (linetype, contents)
  if not validate_linetype (linetype, 'set_line_type') then
    return nil
  end -- not valid
  override_line_type = linetype
  override_line_contents = contents
  this_line = GetLinesInBufferCount()         -- which line in the output buffer
  line_number = GetLineInfo (this_line, 10)   -- which line this was overall

  -- if line type not recorded for this line yet, record it
  if not deduced_line_types [line_number] then
    deduced_line_types [line_number] = {
        lt = override_line_type,  -- what type we assigned to it
        con = 100,  -- with what probability
        draw = false,       -- did we draw on this line?
        ov = override_line_type,  -- was it overridden? (yes)
        }
  end -- if

  return true
end -- set_line_type

-- -----------------------------------------------------------------
-- set_line_type_contents - set the contents of <linetype> to be <contents>
-- linetype is one of: description, exits, room_name, prompt, ignore
-- This lets you set something (like the room name) from another line (eg. the prompt)
-- -----------------------------------------------------------------
override_contents = { }
function set_line_type_contents (linetype, contents)
  if not validate_linetype (linetype, 'set_line_type_contents') then
    return nil
  end -- not valid
  override_contents [linetype] = contents
  return true
end -- set_line_type_contents

-- -----------------------------------------------------------------
-- set_not_line_type - the current line is NOT of type: linetype
-- linetype is one of: description, exits, room_name, prompt, ignore
-- -----------------------------------------------------------------
line_is_not_line_type = { }
function set_not_line_type (linetype)
  if not validate_linetype (linetype, 'set_not_line_type') then
    return nil
  end -- not valid
  line_is_not_line_type [linetype] = true
  return true
end -- set_not_line_type

-- -----------------------------------------------------------------
-- set_area_name - set the name of the current area (used at the bottom of the map)
-- -----------------------------------------------------------------
area_name = nil
function set_area_name (name)
  area_name = name
end -- set_area_name

-- -----------------------------------------------------------------
-- set_uid - set the uid for the current room
-- -----------------------------------------------------------------
override_uid = nil
function set_uid (uid)
  override_uid = uid
end -- set_uid

-- -----------------------------------------------------------------
-- do_not_deduce_line_type - do not use the Bayesian deduction on linetype
-- linetype is one of: description, exits, room_name, prompt, ignore

-- Used to make sure that lines which we have not explicitly set (eg. to an exit)
-- are never deduced to be an exit. Useful for making sure that set_line_type is
-- the only way we know a certain line is a certain type (eg. an exit line)
-- -----------------------------------------------------------------
do_not_deduce_linetypes = { }
function do_not_deduce_line_type (linetype)
  if not validate_linetype (linetype, 'do_not_deduce_line_type') then
    return nil
  end -- not valid
  do_not_deduce_linetypes [linetype] = true
  return true
end -- do_not_deduce_line_type

-- -----------------------------------------------------------------
-- deduce_line_type - use the Bayesian deduction on linetype
--   (undoes do_not_deduce_line_type for that type of line)
-- linetype is one of: description, exits, room_name, prompt, ignore
-- -----------------------------------------------------------------
function deduce_line_type (linetype)
  if not validate_linetype (linetype, 'deduce_line_type') then
    return nil
  end -- not valid
  do_not_deduce_linetypes [linetype] = nil
  return true
end -- do_not_deduce_line_type

-- -----------------------------------------------------------------
-- get the previous line type (deduced or not)
-- returns nil if no last deduced type
-- -----------------------------------------------------------------
function get_last_line_type ()
  return last_deduced_type
end -- get_last_line_type

-- -----------------------------------------------------------------
-- get the current overridden line type
-- returns nil if no last overridden type
-- -----------------------------------------------------------------
function get_this_line_type ()
  return override_line_type
end -- get_last_line_type

-- -----------------------------------------------------------------
-- set_config_option - set a configuration option
-- name: which option (eg. when_to_draw)
-- value: new setting (string) (eg. 'description')
-- equivalent in behaviour to: mapper config <name> <value>
-- returns nil if option name not given or invalid
-- returns true on success
-- -----------------------------------------------------------------
function set_config_option (name, value)
  if type (value) == 'boolean' then
    if value then
      value = 'yes'
    else
      value = 'no'
    end -- if
  end -- they supplied a boolean
  return mapper_config (name, 'mapper config whatever', { name = name or '', value = value or '' } )
end -- set_config_option

-- -----------------------------------------------------------------
-- get_config_option - get a configuration option
-- name: which option (eg. when_to_draw)
-- returns (string) (eg. 'description')
-- returns nil if option name not given or invalid
-- -----------------------------------------------------------------
function get_config_option (name)
  if not name or name == '' then
    mapper.mapprint ("No option name given to 'get_config_option'")
    return nil
  end -- if no name
  local config_item = validate_option (name, 'get_config_option')
  if not config_item then
    return nil
  end -- if not valid
  return config_item.show (config [config_item.option])
end -- get_config_option

-- -----------------------------------------------------------------
-- get_corpus - gets the corpus (serialized)
-- -----------------------------------------------------------------
function get_corpus ()
  return "corpus = " .. serialize.save_simple (corpus)
end -- get_corpus_count

-- -----------------------------------------------------------------
-- get_stats - gets the training stats (serialized)
-- -----------------------------------------------------------------
function get_stats ()
  return "stats = " .. serialize.save_simple (stats)
end -- get_stats

-- -----------------------------------------------------------------
-- get_database - gets the mapper database (rooms) (serialized)
-- -----------------------------------------------------------------
function get_database ()
  return "rooms = " .. serialize.save_simple (rooms)
end -- get_database

-- -----------------------------------------------------------------
-- get_config - gets the mapper database (rooms) (serialized)
-- -----------------------------------------------------------------
function get_config ()
  return "config = " .. serialize.save_simple (config)
end -- get_config

-- -----------------------------------------------------------------
-- get_current_room_ - gets the current room's data (serialized)
-- returns uid, room
-- -----------------------------------------------------------------
function get_current_room ()
  local current_room = get_current_room_ ("get_current_room")
  if not current_room or not rooms [current_room] then
    return nil
  end -- if
  return uid, "room = " .. serialize.save_simple (rooms [current_room])
end -- get_current_room

-- -----------------------------------------------------------------
-- set_room_extras - sets extra information for the nominated UID
-- returns true if UID exists, false if not
-- extras must be a serialized table. eg. "{a = 'nick', b = 666 }"
-- -----------------------------------------------------------------
function set_room_extras (uid, extras)
  if not uid  or not rooms [uid] or type (extras) ~= 'string' then
    return false
  end -- if

  -- make a sandbox so they can't put Lua functions into the import data
  local t = {} -- empty environment table
  f = assert (loadstring ('extras =  ' .. extras))
  setfenv (f, t)
  -- load it
  f ()

  -- move the rooms table into our rooms table
  rooms [uid].extras = t.extras
  return true
end -- set_room_extras

