on run argv
	set r to byId(appWindow(), "timeline.ruler")
	tell application "System Events"
		set {px, py} to position of r
	end tell
	do shell script "/opt/homebrew/bin/cliclick c:" & (px + (item 1 of argv as integer)) & "," & (py + 10)
	delay 1
	return idValue("transport.time")
end run
