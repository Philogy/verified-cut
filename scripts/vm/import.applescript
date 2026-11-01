-- import <file>: click Import..., type the path into the open panel (Cmd-Shift-G), open it.
on run argv
	tell application "VerifiedCut" to activate
	delay 0.5
	set b to byId(appWindow(), "import")
	tell application "System Events" to tell process "VerifiedCut"
		click b
		delay 1.5
		keystroke "g" using {command down, shift down}
		delay 1
		keystroke (item 1 of argv)
		delay 1
		key code 36
		delay 1
		key code 36
		delay 3
	end tell
end run
