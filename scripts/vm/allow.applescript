-- Click "Allow" on the screen-recording consent dialog macOS shows to sshd-session.
tell application "System Events"
	if exists process "UserNotificationCenter" then
		tell process "UserNotificationCenter"
			if (count of windows) > 0 then click button "Allow" of window 1
		end tell
	end if
end tell
