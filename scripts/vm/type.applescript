-- type <row> <in|out> <sample>: type a sample number into that clip's In/Out field and press return.
on run argv
	set r to clipRow(item 1 of argv as integer)
	set f to byId(r, "clip." & (item 2 of argv) & ".value")
	tell application "System Events"
		set frontmost of process "VerifiedCut" to true
		set focused of f to true
		keystroke "a" using command down
		keystroke (item 3 of argv)
		key code 36
		delay 1.5
		return value of f
	end tell
end run
