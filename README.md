# Verified Cut

An audio splicer with a FLAC encoder and decoder written in Lean 4, proven lossless.
For every PCM input FLAC can carry and every encoder setting, decoding what we encode gives
back exactly the input. An exported timeline decodes to exactly the requested sample ranges,
in order.

```
core/     Lean 4 library and the `vericut` CLI (spec, FLAC codec, WAV, proofs)
app/      SwiftUI macOS editor that calls the CLI
tests/    end-to-end tests against libFLAC (`flac`) and ffmpeg, plus an axiom audit
bench/    benchmark script, results and plot
docs/     CLI contract, pipeline with trust boundaries, Tart VM for GUI tests
```

## Build, test, run (macOS)

```sh
brew install flac ffmpeg          # flac: reference codec for tests; ffmpeg: the app's imports
cd core && lake build             # proofs and the vericut binary (Lean v4.33.0, no Mathlib)
cd .. && python3 tests/test_vericut.py
cd app && swift run               # the editor; uses ../core/.lake/build/bin/vericut ($VERICUT_BIN overrides)
```

`app/dev/vericut-stub` is an unverified ffmpeg stand-in, for app development only
(`app/dev/README.md`). CLI contract: `docs/cli.md`. Pipeline, file by file: `docs/pipeline.md`.

To listen to an export, use VLC or another player. QuickTime Player plays FLAC unreliably
(seeking lands at the wrong time, the tail may not play), with libFLAC's files as well as ours.
To use QuickTime, convert to ALAC: `afconvert -f m4af -d alac out.flac out.m4a`. Apple Music
can't import FLAC at all.

## What is proven

Spec, `core/VeriCut/Correctness.lean`:

```lean
theorem flac_roundTrip (st : Flac.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.encode st x) = .ok x                                    -- :17

theorem export_correct (st : Flac.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClips st format clips) = .ok (splice format clips)     -- :24
```

`Flac.encode` and `Flac.decode` are written to be read: a `Nat` bit writer, fixed predictors
only. The CLI runs the optimized codec in `core/VeriCut/Flac/Fast/` (LPC, 64-bit writer,
streaming, MD5). `core/VeriCut/CorrectnessFast.lean` ties it to the same spec `decode`, with
the same hypotheses:

```lean
theorem decodeFast_eq (d : ByteArray) : Flac.Fast.decodeFast d = Flac.decode d          -- :20

theorem flac_roundTrip_fast (st : Flac.Fast.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.Fast.encodeFast st x) = .ok x                                       -- :24

theorem export_correct_fast ... :   -- export_correct's hypotheses
    Flac.decode (exportClipsFast st format clips) = .ok (splice format clips)            -- :29
```

Definitions these mention: `core/VeriCut/Spec/Audio.lean` (`Format`, `Pcm`, `Pcm.Valid`,
`Clip`, `Clip.Valid`, `splice`) and the spec decoder in `core/VeriCut/Flac/` (`Parse.lean`
reads a stream, `Format.lean` gives its meaning). `Pcm.valid_of_validate` shows the CLI's
run-time check establishes `Pcm.Valid`. `Examples.lean` discharges every hypothesis on concrete
audio. All five theorems use only `propext`, `Classical.choice`, `Quot.sound`, checked with
`#guard_msgs` in the build.

## Trusted, not proven

- That our bitstream is standard FLAC (RFC 9639). The theorems are about our own decoder.
  That libFLAC and ffmpeg decode our files bit-exact, and that we decode theirs, is tested.
- The STREAMINFO MD5. It is computed (`Flac/Fast/Md5.lean`) and matches libFLAC's, but no
  theorem mentions it.
- WAV parsing and writing (`Wav.lean`), file IO, JSON, the CLI glue in `Main.lean`.
- ffmpeg, which the app uses to convert other formats to WAV on import.
- The Swift app, its preview playback and its waveforms.
- Lean's compiler and runtime.

## Speed and size

Against libFLAC 1.5.0 (`bench/RESULTS-audio.md`, data in `bench/flac-optimization.csv`, plot
`bench/flac-optimization.png`): within 0.3 % of libFLAC's size at every level, 10-17x slower to
encode, about 8x slower to decode. A 61-minute podcast at -5 encodes in 52.7 s with 3.5 GB peak
RSS.
