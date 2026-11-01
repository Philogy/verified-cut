# Testing the Verified Cut GUI without the user's screen

Research only. Nothing was installed and no settings were changed. Written 2026-10-31.

## The problem

An agent should be able to drive `app/` (a SwiftUI app built with SwiftPM that calls the Lean CLI) end to end and record demo videos. That has to keep working while the user's Mac is locked. The previous session (TRANSCRIPT §16) found that a locked session (`CGSSessionScreenIsLocked = 1`) gives black screenshots and hides windows from Accessibility (AX). `caffeinate` only stops sleep. It doesn't unlock anything.

Facts about this machine:

- M5 Pro with 48 GB RAM and 564 GB free disk.
- **No Xcode.app is installed, only the Command Line Tools.** XCUITest and `xcodebuild test` need full Xcode, either on the host or in the VM.
- Tart, Lume and testvm are not installed.

## TL;DR

The host's GUI session can't be used while it is locked. Apple has no supported way to do that. Every option that works gives the app **a separate, always-unlocked GUI session**. In practice that means a local macOS VM with auto-login. The host can stay locked: locking only affects the host's GUI session, and the `tart run` process keeps running. Add screen-free snapshot and view-model tests for most of the coverage. Use the VM, or a GitHub macOS runner, for real end-to-end runs and demo recordings.

## 1. Local options

| Option | Works while host locked? | Setup | Cost | Video | Fidelity | Notes |
|---|---|---|---|---|---|---|
| XCUITest on host | **No** | Needs Xcode plus an Xcode project | free | Xcode 26 records UI tests | full | Apple DTS: no native way to run macOS XCUITest on a locked session. Fails with "Failed to activate application … Running Background" [1]. Over SSH it also needs the GUI-session context (LaunchAgent in `gui/<uid>`) [2] and keychain access [3]. |
| AX / System Events / cliclick on host | **No** | already working | free | `screencapture -v` | full | Same lock restriction (observed in §16). |
| Second user via Screen Sharing "log in as yourself" / virtual display | Unclear | low | free | in-session | full | Since 10.7, Screen Sharing can start a separate session as another user [4]. Tahoe "High Performance" mode offers 1–2 virtual displays, one session per Mac at a time [5]. Normally you connect from *another* machine; looping back to localhost isn't a documented workflow. Not verified while the console is locked. |
| Fast user switching (second user in background) | **No** | low | free | no | — | Background sessions keep running but are off-console. Capture and synthetic input fail, and at the login window SCK fails to initialize [6][7]. |
| Virtual display (BetterDisplay, `CGVirtualDisplay` private API, HDMI dummy) | **No** | low | BetterDisplay Pro is paid | yes | full | A virtual display belongs to the same WindowServer session, so it is not isolated [8]. No source shows capture working on one while locked. Known bugs: sleep freezes and SCK capturing the wrong virtual display [9][10]. A dummy plug only fixes "no display attached", not the lock. |
| ScreenCaptureKit / AVFoundation capture while locked | **No** | — | — | — | — | DTS: lock-screen UI applies "special case security restrictions". Observed behaviour is black frames [11]. |
| Keep the host unlocked (auto-login, no screensaver password, `caffeinate -d`) | n/a | trivial | free | yes | full | The only native option [1]. Security tradeoff: anyone at the machine gets the session. Not recommended for a laptop. |
| **Tart VM** (Virtualization.framework) | **Yes** | medium | free on personal machines (Fair Source; paid only for server fleets over 100 cores) [12] | yes, in guest | see §1a | `tart run --no-graphics [--vnc]`. Cirrus images ship with auto-login, user `admin`/`admin` [13][14]. macOS 15+ hosts need an unlocked login keychain to start VMs [13]. A locked screen doesn't lock the keychain, but a reboot or an SSH-only start does. Host sleep suspends the VM, so use `caffeinate -s`. `ghcr.io/cirruslabs/macos-tahoe-base` (~25 GB, Homebrew, no Xcode) and `-xcode` variants exist [14]. |
| testvm (Flavio Copes) | **Yes** (wraps Tart) | low | MIT | screenshots | same as Tart | Exactly this use case. Build on host, rsync the `.app` into the VM, `open` it, take screenshots and AX dumps over SSH, click with AppleScript and cliclick. Commands: `testvm open/shot/ui/click/type/key`. Needs 4 CPU, 8 GB, ~33 GB disk [15]. |
| Lume / Cua (trycua) | **Yes** in the VM | medium | MIT, Spaces FSL [16] | yes | same as Tart | Lume is another Virtualization.framework VM manager with a Cua macOS image and an agent UI. Cua Driver can drive apps in the background without stealing focus, using AX actions and per-PID CGEvent/SkyLight private calls. Its docs say nothing about a locked screen, so assume it doesn't work there; on the host it only solves focus-stealing [17]. Running it *inside* the VM is fine. |
| UTM / VirtualBuddy | Yes (VM) | medium | free | yes | same as Tart | VirtualBuddy 2.2 can preconfigure the account only with macOS 27 host and guest. Its automation is a URL scheme (open/boot/stop) [18]. Less scriptable than Tart for CI-style use. |
| Anka (Veertu) | Yes (VM) | medium | quote only, annual per host [19] | yes | same | Overkill for one developer. |

### 1a. Media fidelity inside a macOS VM

This matters for us because the exporter can use `h264_videotoolbox`.

- The public Virtualization.framework gives the guest a paravirtualized Metal GPU running on the host GPU. It reports a conservative feature set (about Apple GPU family 5) [20].
- **Hardware VideoToolbox encoding is not exposed by default.** The only route found is `avm`, which uses private entitlements (`com.apple.virtualization.avp.videotoolbox`, `…AppleM2ScalerDevice`) and probably needs SIP/AMFI changes. Without them, guest VideoToolbox falls back to software encoders [21]. I didn't find whether hardware *decode* is exposed. AVPlayer still plays, using a software decoder if needed [22].
- Conflicting data point: a diagnostic run on GitHub's `macos-26-arm64` runner (itself a VM) showed HEVC VideoToolbox hardware encoding working at about 6× realtime. Concurrent encodes contended, and parallel VP9 hardware decode failed with -12909 [23]. GitHub's virtualization stack may enable the media engine in a way a stock Tart VM doesn't. **Test it**: inside the VM, run `ffmpeg -f lavfi -i testsrc=d=1:s=1280x720 -c:v h264_videotoolbox -b:v 2M out.mp4`, and in Swift call `VTIsHardwareDecodeSupported(kCMVideoCodecType_H264)`.
- Consequence for Verified Cut: GUI flows and libx264 exports are fully testable in a VM. The `SMARTCUT_ENCODER=h264_videotoolbox` path may silently run a software VideoToolbox encoder there, which would give different bitstreams. Keep the hardware-encoder tests on the host (CLI only, no GUI needed, and they already pass while locked).

## 2. Rendering-level tests that need no screen at all

These run under plain `swift test`. They don't need Xcode or a GUI session, and they work while locked, over SSH and in CI.

- **View models / logic.** Move import/export/plan state into an `@Observable` model and test it with XCTest or Swift Testing. Examples: in/out points, snapping, the plan summary "copy 572 / re-encode 28", and Lean CLI invocation and error handling. This catches most bugs cheaply.
- **ViewInspector** (`nalexn/ViewInspector`, supports macOS, v0.10.6). It walks the SwiftUI view tree in tests, for example `try sut.inspect().find(button: "Export").tap()`. Add it to the test target only [24].
- **Snapshot tests** with pointfreeco `swift-snapshot-testing`: `assertSnapshot(of: NSHostingView(rootView: v), as: .image)` with an explicit size. Pitfall: the default renders inside an `NSWindow`, whose title-bar height differs between a real Mac and a headless VM. The fix is `bitmapImageRepForCachingDisplay` + `cacheDisplay` into a 1× rep [25].
- **Video is not snapshot-able.** `ImageRenderer` and `cacheDisplay` don't capture `AVPlayerLayer` content, so `VideoPlayer` comes out blank. That is from my knowledge; sources only covered the window issue [25]. Inject a stub frame view in tests: decode a known frame with `AVAssetImageGenerator` and show it as an `Image`.
- **Demo video without a screen.** You can render successive `NSHostingView` snapshots into an `AVAssetWriter`. This produces a *synthetic* demo with no real cursor, menus, open panel or live player. It's fine for docs, but it is not an end-to-end test. Real demos should be recorded in the VM (§1) or in CI (§3).

## 3. Cloud / CI macOS

| Service | GUI session | Locked-host issue | Cost (Oct 2026) | Video | Notes |
|---|---|---|---|---|---|
| **GitHub Actions** hosted macOS | yes, interactive session; XCUITest works [26] | n/a | $0.062/min standard; Free plan includes $12/mo ≈ 190 macOS min; `macos-26` GA 2026-02-26 [27] | `screencapture -v` works on 13/14 once `kTCCServiceScreenCapture` is inserted into TCC.db via `sudo sqlite3` (schema varies per OS); green videos on macOS 12 [26]. Untested on 15/26. | Runners are VMs (`VirtualMac2,1`). Hardware VT encoding seen on macos-26 (HEVC) [23]. Good for a nightly e2e run plus a recorded demo artifact. |
| Codemagic | yes | n/a | $0.095/min M2; 500 free macOS min/mo [28] | DIY | |
| Bitrise | yes | n/a | plan + credits ($99–218/mo) [28] | DIY | |
| Cirrus Runners / Cirrus CI | — | — | was $150/mo per runner; Cirrus joined OpenAI Apr 2026, Cirrus CI shut down 1 Jun 2026 (unconfirmed primary) [28] | — | Avoid. Tart itself remains (github.com/openai/tart). |
| AWS EC2 Mac (mac2-m2.metal) | via VNC/Screen Sharing after enabling | n/a | $0.878/h, 24 h minimum ≈ $21 [29] | yes | Bare metal, so real VideoToolbox. Heavy for occasional use. |
| Scaleway Mac mini M4 | via VNC | n/a | ~€0.22/h, 24 h minimum (snippets; pricing page 403) [29] | yes | Cheapest bare-metal option with real VideoToolbox. |
| MacStadium | via VNC | n/a | M4.S $149/mo (June 2026 increase) [28] | yes | Monthly dedicated machine. |

Licensing: the macOS SLA §2B(iii) allows **two extra macOS VMs per Apple machine**. The kernel enforces this: a third guest fails with VZErrorDomain Code 6. The permitted uses are development and testing, plus personal non-commercial use in the macOS 27 text [19][30]. One Tart VM for testing is well within the license.

## 4. Agent-oriented computer-use sandboxes

- **Cua / Lume** (trycua, MIT): Virtualization.framework VMs with a prebuilt macOS image, SDKs and an MCP server. Fits "agent drives a Mac GUI", but it duplicates what Tart + SSH + AX scripting already does here. The background driver relies on private APIs that may break on OS updates [16][17].
- **testvm**: the smallest thing that does the job. It is a shell wrapper over Tart [15].
- I found no hosted macOS computer-use service whose GUI fidelity beats a local VM. Hosted runners from §3 can be driven the same way over SSH.

## 5. Ranked recommendation

1. **Screen-free tests first** (cheap, always run, no Xcode). Extract the view model, test it, add ViewInspector and snapshot tests of the timeline and plan summary with a stubbed video frame. Run with `swift test` on the host, also when locked.
2. **Local Tart VM for e2e and demo videos** (works while the host is locked):
   ```sh
   brew install cirruslabs/cli/tart          # quick-start formula; some READMEs say openai/tools/tart
   tart clone ghcr.io/cirruslabs/macos-tahoe-base:latest vc-test
   tart set vc-test --cpu 6 --memory 12288
   caffeinate -s &                           # host sleep would suspend the VM; lock is fine
   tart run --no-graphics vc-test &          # or --vnc to watch; start from a logged-in host session (keychain)
   ssh admin@$(tart ip vc-test)              # admin/admin; install ssh key, brew install ffmpeg cliclick
   ```
   In the guest, once, through VNC: grant Accessibility and Screen Recording to `sshd-keygen-wrapper`/Terminal (or whichever binary drives it). Disable the screensaver lock. Keep auto-login, which Cirrus images enable. Then save the VM as a golden image with `tart clone vc-test vc-golden`.

   Agent loop: build `VerifiedCut.app` on the host (needs the planned `app/bundle.sh`), rsync it plus the Lean CLI and samples into the VM, `open` it, drive it with System Events/AX (`entire contents of window 1`) and cliclick, record with `screencapture -v` in the guest, copy the video back, and verify the output on the host with ffmpeg/AVFoundation. Or use `testvm` instead of hand-rolled scripts. **Caveat:** guest VideoToolbox is probably software-only, so run hardware-encoder checks on the host CLI.
3. **XCUITest, optional.** It needs full Xcode (not installed, ~several GB, also needed in the VM via a `-xcode` image) and a thin Xcode/XcodeGen project with a UI Testing Bundle, because SwiftPM has no UI-test target [31]. Xcode 26 records UI-test videos when the test plan sets Automatic Screen Capture to "On, and keep all" with format Video [32]. That gives demo recordings for free, but the AX scripting from step 2 already covers the flows. Only do this if assertions get complex.
4. **GitHub Actions `macos-26` nightly** as a second, cloud-hosted e2e and demo run, after pushing the repo. It's cheap (~$0.06/min) and screen recording needs the TCC.db insert. This needs the repo on GitHub, which hasn't been decided (`git init` is still pending).
5. **Not recommended:** keeping the host unlocked (security), virtual displays or dummy plugs (don't solve the lock), fast user switching, or paid bare-metal clouds (only worth it for real-hardware VideoToolbox tests in CI).

## Blockers / open questions

- Xcode isn't installed. That only blocks option 3.
- `app/bundle.sh` (a `.app` bundle) is probably needed so AX sees the window. This is still unverified with the screen unlocked (TRANSCRIPT open item 1).
- First-time TCC grants inside the VM need a human or VNC session once.
- Starting the VM requires an unlocked host login keychain on macOS 15+. Start it from the logged-in session before locking, not after a reboot.
- Unverified on this exact setup: macOS 26 guest behaviour under a locked host, hardware VideoToolbox in a Tart guest, and GitHub `screencapture -v` on macos-26.
- Disk: about 25–35 GB per VM image (564 GB free).

## Sources

1. Apple forums 840965, Mac UI tests on locked CI runner: https://developer.apple.com/forums/thread/840965
2. Apple forums 765060, SSH vs LaunchAgent GUI access: https://developer.apple.com/forums/thread/765060
3. Apple forums 713606, xcodebuild over SSH: https://developer.apple.com/forums/thread/713606
4. AppleInsider, Lion multi-user Screen Sharing: https://appleinsider.com/articles/11/03/31/mac_os_x_10_7_lion_to_introduce_multi_user_screen_sharing
5. Apple, Screen Sharing type options: https://support.apple.com/en-gb/guide/mac-help/mchl1883115d
6. Eclectic Light, fast user switching: https://eclecticlight.co/2023/03/22/fast-user-switching-how-it-works-and-when-to-use-it
7. MacPaw, detecting screen capture: https://macpaw.tech/research/is-mac-screen-captured
8. computer-use crate ISOLATION.md: https://docs.rs/crate/computer-use/0.2.0/source/docs/ISOLATION.md
9. BetterDisplay discussion 122: https://github.com/waydabber/BetterDisplay/discussions/122
10. Apple forums 786829, SCK virtual displays: https://developer.apple.com/forums/thread/786829
11. Apple forums 756908, lock-screen restrictions: https://developer.apple.com/forums/thread/756908
12. Tart licensing: https://tart.run/licensing/
13. Tart FAQ: https://tart.run/faq/
14. Tart quick start / image templates: https://tart.run/quick-start/ , https://github.com/cirruslabs/macos-image-templates
15. Flavio Copes, test Mac apps in a VM / testvm: https://flaviocopes.com/mac-test-vm/ , https://flaviocopes.com/testvm/
16. trycua/cua: https://github.com/trycua/cua
17. Cua no-foreground contract: https://cua.ai/docs/explanation/the-no-foreground-contract
18. VirtualBuddy 2.2: https://github.com/insidegui/VirtualBuddy/releases/tag/2.2
19. Anka licensing: https://docs.veertu.com/anka/licensing/ ; Apple forums 845455 (macOS 27 EULA): https://developer.apple.com/forums/thread/845455
20. Tart discussion 344 (GPU): https://github.com/openai/tart/discussions/344
21. catinthesack/avm: https://github.com/catinthesack/avm
22. Apple, RequireHardwareAcceleratedVideoEncoder: https://developer.apple.com/documentation/videotoolbox/kvtvideoencoderspecification_requirehardwareacceleratedvideoencoder
23. zvidlib PR 566 (VT on macos-26 runner): https://github.com/lsegal/zvidlib/pull/566
24. ViewInspector: https://github.com/nalexn/ViewInspector
25. Snapshot tests local vs CI: https://neura.market/directories/deepseek/blog/devto-3507904 ; swift-snapshot-testing PR 533: https://github.com/pointfreeco/swift-snapshot-testing/pull/533
26. runner-images #9047, #9529: https://github.com/actions/runner-images/issues/9047 , https://github.com/actions/runner-images/issues/9529
27. GitHub runner pricing / macOS 26 GA: https://docs.github.com/en/billing/reference/actions-runner-pricing , https://github.blog/changelog/2026-02-26-macos-26-is-now-generally-available-for-github-hosted-runners/
28. Codemagic: https://docs.codemagic.io/billing/pricing/ ; Bitrise: https://cicdcalculator.com/bitrise-pricing-mobile-ci ; Cirrus: https://cirrus-ci.org/pricing ; MacStadium: https://www.MacStadium.com/pricing
29. AWS mac2-m2.metal: https://instances.vantage.sh/aws/ec2/mac2-m2.metal ; Scaleway: https://scaleway.com/en/pricing/apple-silicon
30. Eclectic Light, how Apple limits VMs: https://eclecticlight.co/2022/08/04/virtualisation-on-apple-silicon-macs-8-how-apple-limits-vms/
31. Swift Forums, UI tests with Package.swift only: https://forums.swift.org/t/how-to-run-ui-tests-with-project-only-using-package-swift/69402
32. WWDC25 344 notes: https://wwdcnotes.com/documentation/wwdc25-344-record-replay-and-review-ui-automation-with-xcode/ ; Apple forums 768924: https://developer.apple.com/forums/thread/768924

Several figures come from search-result snippets rather than the vendor pages themselves: Scaleway and Bitrise pricing, Cirrus shutting down, and Tart's brew tap. Check those before relying on them.
