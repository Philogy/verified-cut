#!/bin/sh
# Drive Verified Cut inside a local Tart macOS VM, so GUI tests keep running
# while the host screen is locked. See docs/tart-vm.md.
set -eu

VM=${VM:-vc-test}
IMAGE=ghcr.io/cirruslabs/macos-tahoe-base:latest
ROOT=$(cd "$(dirname "$0")/.." && pwd)
KEY=$HOME/.tart/vc-ssh/id_ed25519
# The repo is shared as "vc"; macOS guests automount shares here. The guest keeps
# seeing the old contents of files the host modifies after boot, so anything we
# rebuild or edit (binaries, scripts) is streamed over SSH into GBIN instead.
GROOT="/Volumes/My Shared Files/vc"
GAPP="/Users/admin/Applications/VerifiedCut.app"
GBIN="/Users/admin/vc-bin"

ssh_vm() {
	ssh -i "$KEY" -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null \
		-o LogLevel=ERROR "admin@$(tart ip "$VM")" "$@"
}

put() { # put <host file> <guest path>
	ssh_vm "mkdir -p '$(dirname "$2")' && cat > '$2.tmp' && mv '$2.tmp' '$2'" <"$1"
}

osa() { # osa <script> [args...]: run scripts/vm/<script>.applescript, with lib.applescript prepended, in the guest
	s=$1; shift
	cat "$ROOT/scripts/vm/lib.applescript" "$ROOT/scripts/vm/$s.applescript" >"${TMPDIR:-/tmp}/vm-$s.applescript"
	put "${TMPDIR:-/tmp}/vm-$s.applescript" "$GBIN/$s.applescript"
	ssh_vm "osascript '$GBIN/$s.applescript' $(printf "'%s' " "$@")"
}

cmd=${1:-help}; [ $# -gt 0 ] && shift
case $cmd in
create)
	tart clone "$IMAGE" "$VM"
	tart set "$VM" --cpu 6 --memory 12288
	;;
start)
	# caffeinate -s: host sleep would suspend the VM (locking is fine).
	# Start from a logged-in host session: Tart needs the login keychain unlocked.
	nohup caffeinate -s tart run --no-graphics --dir "vc:$ROOT" "$VM" \
		>"${TMPDIR:-/tmp}/tart-$VM.log" 2>&1 &
	tart ip --wait 120 "$VM" >/dev/null
	[ -f "$KEY" ] || { mkdir -p "$(dirname "$KEY")"; ssh-keygen -q -t ed25519 -N "" -C "$VM" -f "$KEY"; }
	pub=$(cat "$KEY.pub")
	# The guest agent may need a few seconds after the IP appears.
	for _ in 1 2 3 4 5 6 7 8 9 10; do
		tart exec "$VM" sh -c "mkdir -p ~/.ssh && chmod 700 ~/.ssh && (grep -qF '$pub' ~/.ssh/authorized_keys 2>/dev/null || echo '$pub' >> ~/.ssh/authorized_keys) && chmod 600 ~/.ssh/authorized_keys" && break
		sleep 3
	done
	echo "$VM up at $(tart ip "$VM")"
	;;
stop) tart stop "$VM" ;;
ssh) ssh_vm "$@" ;;
setup)
	# The NAT DNS proxy on 192.168.64.1 doesn't answer on this host; use public resolvers in the guest.
	ssh_vm 'sudo networksetup -setdnsservers Ethernet 1.1.1.1 8.8.8.8
		eval "$(/opt/homebrew/bin/brew shellenv)"
		HOMEBREW_NO_AUTO_UPDATE=1 brew install ffmpeg cliclick'
	;;
install)
	# Build on the host (the guest has no Lean), then wrap the SwiftPM binary in a minimal .app
	# in the guest so `open` launches it into the GUI session.
	# VERICUT_BIN=app/dev/vericut-stub installs the stub instead of building core/.
	if [ -n "${VERICUT_BIN:-}" ]; then bin=$VERICUT_BIN; else
		(cd "$ROOT/core" && lake build vericut)
		bin=$ROOT/core/.lake/build/bin/vericut
	fi
	(cd "$ROOT/app" && swift build -c release)
	put "$bin" "$GBIN/vericut"
	put "$(cd "$ROOT/app" && swift build -c release --show-bin-path)/VerifiedCut" "$GAPP/Contents/MacOS/VerifiedCut"
	put "$ROOT/scripts/ocr.swift" "$GBIN/ocr.swift"
	ssh_vm "chmod +x '$GBIN/vericut' '$GAPP/Contents/MacOS/VerifiedCut'
		cat > '$GAPP/Contents/Info.plist' <<EOF
<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<plist version=\"1.0\"><dict>
<key>CFBundleExecutable</key><string>VerifiedCut</string>
<key>CFBundleIdentifier</key><string>net.dumo.verifiedcut.vmtest</string>
<key>CFBundleName</key><string>VerifiedCut</string>
<key>CFBundlePackageType</key><string>APPL</string>
<key>NSHighResolutionCapable</key><true/>
</dict></plist>
EOF"
	;;
launch)
	# #filePath in VeriCut.swift points at the host checkout, so pass the binary explicitly.
	# Quit first: macOS restores the app at login without the variable, and open --env won't reach a running app.
	ssh_vm "osascript -e 'tell application \"VerifiedCut\" to quit' 2>/dev/null; sleep 1; open --env VERICUT_BIN='$GBIN/vericut' '$GAPP'"
	sleep 3
	osa allow >/dev/null
	;;
quit) ssh_vm 'osascript -e "tell application \"VerifiedCut\" to quit"' ;;
shot) # shot <host.png>: full-screen capture of the guest
	ssh_vm 'screencapture -x /tmp/vm-shot.png && cat /tmp/vm-shot.png' >"${1:-vm-shot.png}"
	;;
ocr) # ocr: capture the guest screen and print the recognised text
	ssh_vm "screencapture -x /tmp/vm-shot.png && swift '$GBIN/ocr.swift' /tmp/vm-shot.png 2>/dev/null"
	;;
record) # record <seconds> <host.mov>: screen video of the guest
	ssh_vm "rm -f /tmp/vm-rec.mov; screencapture -x -v -V $1 /tmp/vm-rec.mov && cat /tmp/vm-rec.mov" >"$2"
	;;
ax) ssh_vm "osascript -e 'tell application \"System Events\" to tell process \"VerifiedCut\" to get entire contents of window 1'" | tr ',' '\n' ;;
import | step | type | drag | rulerclick | value | enabled | export | status | click | ids | windows | allow) osa "$cmd" "$@" ;;
*)
	echo "usage: $0 create|start|stop|setup|install|launch|quit|ssh|shot F|ocr|record S F|ax|import F|step ROW in|out N|type ROW in|out SAMPLE|drag LANE in|out DX|export DIR NAME|status|click ID [ROW]|enabled ID|ids|windows|allow" >&2
	exit 2
	;;
esac
