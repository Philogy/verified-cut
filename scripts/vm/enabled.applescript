-- enabled <id>: whether the control with that accessibility identifier is enabled.
on run argv
	tell application "System Events" to return enabled of my byId(my appWindow(), item 1 of argv)
end run
