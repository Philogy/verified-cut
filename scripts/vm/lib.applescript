-- Prepended to each script by `osa` in vm.sh: look up the app's controls by accessibility identifier.

-- The first element under root (inclusive) whose AXIdentifier is ident.
on byId(root, ident)
	tell application "System Events"
		try
			if value of attribute "AXIdentifier" of root is ident then return root
		end try
		set es to entire contents of root
		repeat with e in es
			set e to contents of e
			try
				if value of attribute "AXIdentifier" of e is ident then return e
			end try
		end repeat
	end tell
	error "no element with identifier " & ident
end byId

on appWindow()
	tell application "System Events" to return window 1 of process "VerifiedCut"
end appWindow

-- Every element under root whose AXIdentifier is ident, in tree order.
on allById(root, ident)
	set found to {}
	tell application "System Events"
		set es to entire contents of root
		repeat with e in es
			set e to contents of e
			try
				if value of attribute "AXIdentifier" of e is ident then set end of found to e
			end try
		end repeat
	end tell
	return found
end allById

-- Lane header n (the clip's name, In/Out steppers, order buttons); row-level ids (clip.in.stepper, ...) repeat per lane.
on clipRow(n)
	return item n of allById(appWindow(), "clip.row")
end clipRow

-- Timeline lane n: the clip rectangle with its trim handles (clip.in.handle, clip.out.handle).
on clipLane(n)
	return item n of allById(appWindow(), "clip.lane")
end clipLane

-- SwiftUI drops empty Text views from the tree, so a missing element reads as "".
on idValue(ident)
	try
		set e to byId(appWindow(), ident)
	on error
		return ""
	end try
	tell application "System Events" to return value of e
end idValue

