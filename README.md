# Verified Cut

A cuts-only video editor whose exporter is **proven** (Lean 4) to output exactly
the frames you selected, while re-encoding only the frames it has to.

Most editors re-encode every frame on export. A cut only *needs* re-encoding
where it breaks a frame's dependencies: from a mid-GOP cut point up to the next
keyframe. Everything else can be copied byte-for-byte: faster, and lossless.
"Smart cut" tools exist but are notoriously buggy. Here the planner and the
copy semantics are machine-checked, and the parts that can't be proven are
named and tested against ffmpeg.

```
core/     Lean 4 library + `vericut` CLI (spec, proofs, planner, MP4 demux/mux)
app/      SwiftUI macOS app (import, trim, preview, export) that calls the CLI
tests/    end-to-end tests: vericut vs ffmpeg as oracle, plus a proof audit
samples/  test clips (fetch_samples.sh recreates them)
```

## Quick start (macOS)

```sh
brew install ffmpeg               # oracle for tests, and the encoder bridge for boundary frames
cd core && lake build             # builds proofs + the vericut binary (Lean v4.33.0, no Mathlib)
cd .. && python3 tests/test_vericut.py
VERICUT_ENCODER=h264_videotoolbox python3 tests/test_vericut.py   # hardware encoder path
cd app && swift run               # or: open app/Package.swift in Xcode
```

CLI:

```sh
vericut probe clip.mp4                       # frame table (sizes, timestamps, keyframes) as JSON
vericut plan timeline.json                   # which frames will be copied / re-encoded
vericut export timeline.json out.mp4 --encoder h264_videotoolbox
# timeline.json: {"clips": [{"path": "a.mp4", "in": 100, "out": 700}]}   display frames, half-open
```

Example (Big Buck Bunny, cut [100, 700)): 572 frames copied, 28 re-encoded, ~0.2 s.

## What is proven

The model (`core/VeriCut/Spec/`) is a stream of packets in decode order. Each
packet has opaque bytes and references to earlier packets. A **codec** is *any*
function `(bytes, reference pictures) → picture`. Every theorem holds for every
codec. "Picture" means the decoder's whole state, i.e. its decoded picture
buffer. So in the MP4 bridge, a non-keyframe depends on the previous packet and
an IDR keyframe depends on nothing, which is the definition of IDR. That is
faithful even with B-frames and long-term references.

| Theorem (`core/VeriCut/Proofs/`) | Statement |
|---|---|
| `picture_extract`, `decode_extract` | Copying a dependency-closed packet set byte-for-byte yields exactly the source pictures. |
| `decode_concatStreams` | Concatenating self-contained streams decodes to the concatenation of their decodes. |
| `export_correct` | For any encoder meeting its contract, a valid plan's export decodes to the requested source pictures, exactly for copies and `approx`-close for re-encodes. |
| `export_exact` | A copy-only valid plan is lossless: equality, not approximation. |
| `copySet_copyable` | The reference planner's copy set is valid (sorted, in bounds, closed). |
| `copyable_maximal` | Any dependency-closed set of wanted frames is contained in it, so **no correct copy-based plan re-encodes fewer frames.** |
| `table_eq_copyable` | The fast O(n) memoized planner table equals the reference definition. |
| `plan_valid`, `plan_covers`, `plan_copy_copyable` | The implemented planner emits only valid copy segments, covers exactly the wanted frames, and copies only copyable frames. |
| `exportTimeline_correct` | The export loop the CLI actually runs (`Impl/Export.lean`, generic over a `MonadEncode` effect, run in `IO` with ffmpeg), run on the planner's plans with *any* encoder function meeting the per-job contract, decodes to the requested pictures of every clip in timeline order. |
| `toStream_wellFormed` | The MP4 bridge stream is well-formed when sample 0 is sync (which the CLI checks). |

`VeriCut/Examples.lean` instantiates the hypotheses on concrete streams,
shows the spec *rejects* a naive cut (`¬ CopySet gop2 [1,2,3,4]`), and has
`#guard` tests, including B-frames. `tests/` audits that every main theorem
uses only `propext`, `Classical.choice`, `Quot.sound` (no `sorry`).

## Trusted surface

Read these before trusting the theorems:

- **Spec definitions**: `Spec/Stream.lean` (`Packet`, `Codec`, `picture`, `decode`,
  `DepClosed`, `CopySet`, `extract`, `shift`, `concatStreams`), `Spec/Export.lean`
  (`Segment`, `Encoder`, `exportPlan`, `target`, `PlanValid`, `Job`, `JobContract`), `Spec/Planner.lean`
  (`wanted`, `copyable`).
- **Encoder contract** (`Encoder` / per-job `JobContract` in `Spec/Export.lean`): the re-encoder outputs
  a self-contained stream that decodes approx-close to its input. In practice
  this is ffmpeg calling VideoToolbox (`h264_videotoolbox`) or libx264. The CLI
  checks frame count, codec, no reordering, and a leading sync sample.
- **Bridge assumption** (`toStream` in `MP4/Parse.lean`): a sync sample resets
  the decoder. For H.264/HEVC, sync means listed in `stss` *and* holding an IDR
  picture; the parser reads the NAL headers to check. Open-GOP I-frames (which
  x264/ffmpeg list in `stss`) are not sync. For other codecs (ProRes) `stss` is
  trusted as is. The ffmpeg tests check it on every sample.
- **Unverified, tested code**: MP4 parsing (`MP4/Parse.lean`, differential-tested
  against ffprobe), MP4 writing (`MP4/Write.lean`), and in the CLI (`Main.lean`) the
  `IO` encode instance and the mux pass that turns the exporter's packet stream into
  sample descriptions, display slots and in-band parameter sets (see `docs/pipeline.md`).
- **Toolchain**: Lean 4.33.0 kernel and compiler. No Mathlib, no `native_decide`.

## Tests

`python3 tests/test_vericut.py` (16 tests, ~20 s) uses ffmpeg as the oracle:

- probe agrees with ffprobe on sizes, offsets, keyframes and display order of every sample,
  and its sync flags with the IDR NAL units ffmpeg's `trace_headers` sees;
- whole-clip and keyframe-aligned cuts: decoded frames and **compressed packets byte-identical**;
- intra-only (ProRes) cuts at any frame copy everything, losslessly;
- mid-GOP smart cuts (no B-frames, B-frames, real footage, single-GOP clip),
  in both parameter-set modes: every copied frame bit-identical to the source,
  every re-encoded frame above 35 dB PSNR;
- open GOP (generated `gop24_open.mp4`): cuts at and across non-IDR I-frames;
- multi-clip timelines; rejection of bad ranges, mismatched clips, `--strict`;
- proof audit: no `sorry`, no extra axioms.

A mutation check was run while building this: making the bridge claim every
frame is a keyframe causes the smart-cut tests to fail.

## Known limits / next steps

- **Video track only**: audio is dropped. Next: AAC with priming and edit lists.
- **Display order and timestamps** are produced by the muxer and tested, not yet
  proven. Next theorem: output pts strictly increasing and gap-free.
- **MP4 parse/serialize** round-trip theorem not yet stated. Today they're
  differential-tested only.
- **Re-encode needs H.264 (`avc1`)**. HEVC/ProRes clips are copy-only. ProRes is
  intra-only, so it never needs re-encoding.
- **Open GOP** sources are cut correctly but conservatively: only IDR frames start
  copy runs, so a cut after a non-IDR I-frame re-encodes up to the next IDR (with
  x264 `open-gop`, often the rest of the clip). Copying from such an I-frame, minus
  its leading B-frames, would need per-frame references in the bridge.
- Constant frame rate; all clips in one timeline share resolution, codec and frame rate.
- Source edit lists are ignored (frames are addressed by display rank of all samples).
- Whole input files are read into memory. Next: seek-based streaming copy.
- Parameter sets: default `--paramsets stsd` writes one sample description per
  distinct SPS/PPS (AVFoundation-native). `--paramsets inband` keeps one and
  prepends SPS/PPS at switches. Both pass with ffmpeg. **Check playback in
  QuickTime/AVFoundation on a Mac.** That hasn't been tested yet.
- Testing note: lossless x264 (`-qp 0`, High 4:4:4) as the boundary encoder makes
  ffmpeg's decoder drift on later copied GOPs (deterministic, about 1 LSB). Normal
  lossy encodes don't. The tests use lossy encodes and PSNR for re-encoded frames.
- Re-encoding fewer than a GOP per cut is an open auto-research target (see the I_PCM idea in the design notes).
