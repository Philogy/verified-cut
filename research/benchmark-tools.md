# What to benchmark vericut against

Our tool is **vericut** (was `smartcut`; renamed because
[skeskinen/smartcut](https://github.com/skeskinen/smartcut) already uses that name).
The script and results are in `bench/`.

## Recommendation

Compare against three baselines, and always show correctness next to time:

1. **ffmpeg full re-encode with vericut's encoder settings**
   (`h264_videotoolbox -q:v 75 -bf 0 -allow_sw 0`). This is the honest
   "what an ordinary editor does" baseline: same frames out, same hardware
   encoder, so the only difference is how much gets re-encoded.
2. **skeskinen/smartcut**: the closest open-source equivalent (frame-accurate
   smart cut, scriptable CLI, installs without sudo). Its re-encoder is software
   libx264, which we can't change from its CLI, so its time isn't encoder-matched.
3. **ffmpeg stream copy** as the lower bound on time. It can't produce the requested
   frames, and the correctness table shows that.

Skip LosslessCut and Avidemux for now (below).

## Candidates

### ffmpeg stream copy (`-c copy`, `-ss`/`-to`, concat `inpoint`/`outpoint`)
- Nothing is decoded with `-c copy`, so cuts can only land on packet boundaries,
  which for inter-frame codecs means keyframes.
- The concat demuxer docs say `inpoint` "works best with intra frame codecs, because
  for non-intra frame ones you will usually get extra packets before the actual In
  point". `outpoint` is exclusive on packet DTS
  ([ffmpeg-formats: concat](https://ffmpeg.org/ffmpeg-formats.html#concat-1)).
  Trac [#8464](https://trac.ffmpeg.org/ticket/8464) reports outpoint being off by one
  frame (closed invalid).
- **Measured** (bench, 4K Falcon 9, keyframes every 30): asking for 4,200 frames
  gives 4,255. The extra 55 = 25 + 7 + 23, exactly the frames between each `in`
  (1015, 4507, 8003) and the keyframe before it (990, 4500, 7980). Only 1 output
  frame is bit-identical to the frame it should be, min PSNR 14 dB. On bbb
  `[100,700)`: 636 frames instead of 600.

### ffmpeg full re-encode with matched settings
- vericut's `encodeRange` (`core/Main.lean`, `defaultArgs "h264_videotoolbox"`) uses
  `-c:v h264_videotoolbox -q:v 75 -bf 0 -allow_sw 0`. `-q:v` on VideoToolbox is
  Apple-Silicon only, 0-100 quality scale, added in ffmpeg 4.4
  ([ffmpeg-devel patch, 2021](https://ffmpeg.org/pipermail/ffmpeg-devel/2021-March/278019.html)).
  `-allow_sw 0` (default false) forbids a software fallback (`ffmpeg -h encoder=h264_videotoolbox`).
- Command used (per range: seek half a frame early, trim to the exact count, concat):
  ```
  ffmpeg -ss <in-0.5 frames> -i src.mp4 ... \
    -filter_complex "[0:v]trim=end_frame=<n0>,setpts=PTS-STARTPTS[v0];...[v0][v1][v2]concat=n=3:v=1:a=0[out]" \
    -map [out] -c:v h264_videotoolbox -q:v 75 -bf 0 -allow_sw 0 out.mp4
  ```
  Verified frame-accurate: 4,200 frames, correct duration.
- `-hwaccel videotoolbox` adds hardware decode. Software filters pull frames back to
  system memory, which limits the gain ([codetv.dev](https://codetv.dev/blog/hardware-acceleration-ffmpeg-apple-silicon)).
  Measured: no difference (55.3 s vs 55.4 s); the encoder is the bottleneck.

### skeskinen/smartcut (Python) — **included**
- MIT, `pip`/`pipx install smartcut`; re-encodes only around cut points, stream-copies
  the rest; claims frame accuracy for H.264/H.265/VP9/AV1; README says it is no longer
  actively maintained, updates go to a commercial product
  ([GitHub](https://github.com/skeskinen/smartcut), [PyPI](https://pypi.org/project/smartcut)).
  A fork exists ([selpats/smartcut](https://github.com/selpats/smartcut)), not evaluated.
- Installed 1.7 with `uv tool install smartcut` (`~/.local/bin/smartcut`, no sudo).
- From its source (`cut_video.py`, `media_utils.py`): the CLI hardcodes quality NORMAL =
  libx264 CRF 18, `x264-params sps-id=3`; no encoder option.
- **Measured**: one frame too many per range (4,203 for 3 ranges; 601 for bbb `[100,700)`;
  `--keep 10,20` on a test clip gives 10, so not simply inclusive ends). Exact matches
  stop after the first join (frame 1175) because everything later is shifted by one.

### LosslessCut — skipped
- Smart cut is labelled experimental ([GitHub](https://github.com/mifi/lossless-cut)).
  The CLI has no "cut and exit" command ([CLI docs](https://losslesscut.app/docs/cli));
  automation means a running Electron instance driven through `--http-api`
  (`POST /api/action/export`, `/api/await-event/export-complete`;
  [API docs](https://losslesscut.app/docs/api)). Cut points and the smart-cut setting
  would have to be set through the GUI/project file. Not headless; not worth it for a
  benchmark. Installable with `brew install --cask losslesscut` (not installed).

### Avidemux — skipped
- Has `--force-smart` ("smart copy mode with CQ=3 at next save") and `--begin/--end`
  ([man page](https://man.archlinux.org/man/avidemux.1.en)). But the Homebrew cask is
  **disabled** since 2026-09-01 (fails Gatekeeper; `brew info --cask avidemux`), the build is
  Intel-only (Rosetta), and the frame-accuracy of its CLI smart copy is undocumented.
  Would need a manual DMG install and Gatekeeper override.

### Others found, not pursued
- avcut, ExactCut Video Tools (VirtualDub cutlists; Windows), VideoReDo, Smart Cutter,
  TMPGEnc Smart Renderer (commercial, Windows); QuickTime Player (GUI only).
  ([ExactCut](https://github.com/CluelessCoder73/ExactCut-Video-Tools),
  [Smart Cutter](https://www.videohelp.com/tools/Smart-Cutter-Ps-Ts),
  [LosslessCut #372](https://github.com/mifi/lossless-cut/issues/372)).
