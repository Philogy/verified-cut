-- click <id> [row]: click the control with that accessibility identifier (inside clip row `row` if given).
on run argv
	if (count of argv) > 1 then
		set root to clipRow(item 2 of argv as integer)
	else
		set root to appWindow()
	end if
	set e to byId(root, item 1 of argv)
	tell application "System Events" to click e
	return
end run
