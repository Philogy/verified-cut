-- List every accessibility identifier in the app window with its role.
on run
	set out to ""
	tell application "System Events"
		set es to entire contents of my appWindow()
		repeat with e in es
			set e to contents of e
			try
				set i to value of attribute "AXIdentifier" of e
				if i is not missing value and i is not "" then set out to out & i & " " & (role of e) & linefeed
			end try
		end repeat
	end tell
	return out
end run
