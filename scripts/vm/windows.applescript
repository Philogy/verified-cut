-- List every process that has windows, with the window names. Useful to spot system dialogs.
tell application "System Events"
	set out to ""
	repeat with p in (every process)
		try
			if (count of windows of p) > 0 then set out to out & name of p & ": " & (name of every window of p as text) & linefeed
		end try
	end repeat
	return out
end tell
