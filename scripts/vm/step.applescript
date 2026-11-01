-- step <row> <in|out> <n>: press that clip's stepper n times (negative = down).
-- Setting the slider value directly is ignored by SwiftUI, so this clicks the arrows.
on run argv
	set r to clipRow(item 1 of argv as integer)
	set which to item 2 of argv
	set n to item 3 of argv as integer
	set s to byId(r, "clip." & which & ".stepper")
	tell application "System Events"
		set b to button 1 of s
		if n < 0 then
			set b to button 2 of s
			set n to -n
		end if
		repeat n times
			click b
		end repeat
		delay 1.5
		return value of my byId(r, "clip." & which & ".value")
	end tell
end run
