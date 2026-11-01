-- Print the project format, total samples, the status line and one line per clip row.
on run
	set out to "format: " & idValue("project.format") & linefeed & "samples: " & idValue("timeline.samples") & linefeed & "status: " & idValue("status") & linefeed
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
