-- drag <lane> <in|out> <dx>: drag that clip's trim handle dx points (negative = left) with cliclick.
on run argv
	set h to byId(clipLane(item 1 of argv as integer), "clip." & (item 2 of argv) & ".handle")
	tell application "System Events"
		set {px, py} to position of h
		set {w, hh} to size of h
	end tell
	set x to (px + w / 2) as integer
	set y to (py + hh / 2) as integer
	set dx to item 3 of argv as integer
	set steps to ""
	repeat with i from 1 to 10
		set steps to steps & " m:" & (x + dx * i / 10 as integer) & "," & y
	end repeat
	do shell script "/opt/homebrew/bin/cliclick -e 20 dd:" & x & "," & y & steps & " du:" & (x + dx) & "," & y
	delay 2
	tell application "System Events" to return value of my byId(my clipRow(item 1 of argv as integer), "clip." & (item 2 of argv) & ".value")
end run
