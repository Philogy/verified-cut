# Driving the app in a Tart VM

A locked host screen blocks GUI automation (AX, `screencapture`, XCUITest). A
macOS VM has its own GUI session that stays logged in, so the app can be
driven there while the host is locked. Background: `research/headless-gui-testing.md`.
Everything goes through `scripts/vm.sh`.

## Setup (once)

```sh
brew trust --formula openai/tools/softnet   # tart's dependency; the cirruslabs tap formula is broken
brew install openai/tools/tart
scripts/vm.sh create    # clones ghcr.io/cirruslabs/macos-tahoe-base (26 GB download), 6 CPU, 12 GB RAM
scripts/vm.sh start
scripts/vm.sh setup     # guest DNS fix, brew install ffmpeg cliclick
```

Base image without Xcode: the guest has the Command Line Tools (`swift`), and
the app and `vericut` are built on the host anyway (the guest has no Lean).
The `-xcode` image is only needed for XCUITest.

## Daily use

```sh
scripts/vm.sh start            # from a logged-in host session (Tart needs the login keychain); lock afterwards
scripts/vm.sh install          # lake build + swift build on the host, copy the app into the guest
scripts/vm.sh launch
scripts/vm.sh import "/Volumes/My Shared Files/vc/samples/bbb_baseline.mp4"
scripts/vm.sh step 1 in 100    # clip 1, In stepper, 100 clicks up (out = Out, negative = down)
scripts/vm.sh drag 1 in 40     # drag clip 1's In handle 40 points right with cliclick; prints the new In frame
scripts/vm.sh rulerclick 300   # click the ruler 300 points from its left edge (seeks); prints the transport time
scripts/vm.sh value transport.time   # value of any control by accessibility id
scripts/vm.sh click clip.in.snap 1   # click any control by accessibility id (row-scoped ids take a row)
scripts/vm.sh export /tmp out.mp4
scripts/vm.sh status           # plan summary, frame total, status line, one line per clip
scripts/vm.sh ids              # every accessibility id in the window, with its role
scripts/vm.sh shot shot.png    # guest screenshot to the host
scripts/vm.sh ocr              # guest screenshot, printed as text (Vision)
scripts/vm.sh record 10 run.mov
scripts/vm.sh ax               # the window's accessibility tree
scripts/vm.sh windows          # all windows, to spot system dialogs
scripts/vm.sh ssh 'cmd'        # anything else; scripts/vm.sh stop to shut down
```

- SSH: user `admin` (password `admin`), key `~/.tart/vc-ssh/id_ed25519`, installed by `start` via `tart exec`.
- Shared dir: the repo, read-write, at `/Volumes/My Shared Files/vc` in the guest.
- `install` streams the app, `vericut` and `scripts/ocr.swift` over SSH into the guest
  (`~/Applications/VerifiedCut.app`, `~/vc-bin/`), and `osa` does the same with each
  AppleScript per call. The share can't be used for these (see limits).
- `launch` starts the app with `open --env VERICUT_BIN=~/vc-bin/vericut`, because
  `VeriCut.swift` looks for the binary at the host checkout path. It quits any running
  copy first, since macOS restores the app at guest login without that variable.
- The AppleScripts are in `scripts/vm/`. `osa` prepends `scripts/vm/lib.applescript`,
  whose `byId` finds controls by accessibility identifier (a walk of the window,
  about 2 s), so the scripts don't depend on the view hierarchy.

## Accessibility identifiers

Set with `.accessibilityIdentifier` in `app/Sources/VerifiedCut/`. Each clip has a lane
header (`clip.row`, left column) and a lane (`clip.lane`, on the time axis); the `clip.*`
ids repeat in each. `clipRow(n)` and `clipLane(n)` in `lib.applescript` find the n-th one.

| id | role | what |
|---|---|---|
| `import` | button | Import… |
| `export` | button | Export… |
| `transport.play` | button | play/pause (space) |
| `transport.time` | static text | "m:ss.ss / m:ss.ss", playhead / output duration |
| `timeline.frames` | static text | total output frames |
| `plan.summary` | static text | "Export plan: copy N …, re-encode M." (absent while empty) |
| `status` | static text | status line under the timeline |
| `preview.player` | group | the AVKit preview (play/scrub controls inside) |
| `clip.list` | group | the whole timeline editor |
| `timeline.zoom`, `timeline.fit` | slider, button | zoom (log scale), fit everything in view |
| `timeline.ruler` | group | time ruler; click or drag to seek |
| `timeline.playhead` | group | playhead line; value = its time |
| `clip.row` | group | lane header of one clip |
| `clip.name` | static text | file name |
| `clip.length` | static text | "N frames · m:ss.ss" |
| `clip.up`, `clip.down`, `clip.remove` | button | move earlier/later, remove |
| `clip.in.stepper`, `clip.out.stepper` | incrementor | In/Out stepper; button 1 = up, 2 = down |
| `clip.in.snap`, `clip.out.snap` | button | snap to nearest keyframe |
| `clip.in.value`, `clip.out.value` | static text | current In/Out frame |
| `clip.lane` | group | the clip's rectangle: whole source, trimmed parts faded |
| `clip.in.handle`, `clip.out.handle` | group | trim handles; drag (snaps to keyframes within 6 pt), or AX increment/decrement by one frame |
| `clip.keyframes` | group | keyframe ticks along the bottom of the lane |

## What was checked (macOS 26.6.2 guest on a 26.5.1 host, Oct 2026)

- Over plain SSH, no manual permission pass was needed: AX queries/clicks,
  keystrokes and `screencapture` (stills and `-v` video) all work. macOS shows a
  "com.apple.sshd-session … access your screen" dialog. Capture still works,
  and `launch` clicks Allow via AX (`scripts/vm/allow.applescript`).
- Import → trim → export through the open and save panels, driven by the ids above. `bbb_baseline.mp4` [100, 700)
  gives 572 copied / 28 re-encoded, the same as the README, and the 600-frame output decodes.
- Hardware VideoToolbox works in the guest: macOS 26 exposes a paravirtualized AVC
  encoder (`paravirtualized:com.apple.videotoolbox.videoencoder.ave.avc`,
  hardware-accelerated). `-allow_sw 0` succeeds, and 10 s of 1080p encodes in about 1 s.
  It is a different encoder ID from the host's, so bitstreams may differ from host exports.
- `tests/test_vericut.py` in the guest: 12/13 pass with libx264 and with
  `h264_videotoolbox`. `test_axioms` fails because it needs `lake` (run it on the host).

## Known limits

- Host sleep suspends the VM: `start` wraps it in `caffeinate -s`. Locking is fine.
- Not tested: an actual run with the host locked. The host stayed unlocked during setup.
- SSH runs `zsh` without Homebrew on `PATH`: use `/opt/homebrew/bin/ffmpeg` or
  `eval "$(/opt/homebrew/bin/brew shellenv)"`.
- The host's NAT DNS proxy (192.168.64.1) doesn't answer, so `setup` points the
  guest at 1.1.1.1/8.8.8.8.
- Guest screen is 1024×768 points (2048×1536 px) regardless of `tart set --display`.
- SwiftUI doesn't take AX value writes, so `step` clicks the stepper arrows and `drag` moves the real pointer.
- Files from the guest under `/tmp` aren't shared; export into the shared dir or copy
  them over `scripts/vm.sh ssh 'cat …' > file`.
- **The share goes stale for modified files.** A file the host edits after the VM boots
  keeps showing its old contents in the guest, even with the new size, so reads are
  truncated or corrupt. Same for symlinks SwiftPM recreates (`.build/release` gives
  `EINVAL`). Files created after boot, and files the guest writes, are fine. So the
  scripts stream changed files over SSH. To run `tests/` or anything else from the share
  after editing it, restart the VM (`stop`, `start`).
- Disk: about 33 GB (image cache and VM are APFS clones; `du` counts them twice).
  Remove with `tart delete vc-test` and `tart prune --entries caches`.
