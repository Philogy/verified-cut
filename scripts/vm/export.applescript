-- export <dir> <name>: click Export..., save as dir/name via the save panel.
on run argv
	tell application "VerifiedCut" to activate
	set b to byId(appWindow(), "export")
	tell application "System Events" to tell process "VerifiedCut"
		click b
		delay 1.5
		-- Typing into the name field is racy (the panel selects only the base name); set it via AX.
		set value of text field "Save As:" of splitter group 1 of window "Save" to (item 2 of argv)
		keystroke "g" using {command down, shift down}
		delay 1
		keystroke (item 1 of argv)
		key code 36
		delay 1
		key code 36
		delay 4
	end tell
end run
