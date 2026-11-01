-- Print the plan summary, the status line and one line per clip row.
on run
	set out to "plan: " & idValue("plan.summary") & linefeed & "frames: " & idValue("timeline.frames") & linefeed & "status: " & idValue("status") & linefeed
	set n to count of allById(appWindow(), "clip.row")
	repeat with i from 1 to n
		set r to clipRow(i)
		set out to out & "clip " & i & ": "
		repeat with ident in {"clip.name", "clip.length", "clip.in.value", "clip.out.value"}
			tell application "System Events" to set out to out & (value of my byId(r, contents of ident)) & " | "
		end repeat
		set out to out & linefeed
	end repeat
	return out
end run
