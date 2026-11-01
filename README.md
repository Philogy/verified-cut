# Verified Cut

An audio splicer with a FLAC encoder and decoder written in Lean 4 and **proven** lossless:
for every PCM input FLAC can carry and every encoder setting, decoding what we encode gives
back exactly the input. The export of a timeline decodes to exactly the requested sample
ranges, in order.

```
core/     Lean 4 library + `vericut` CLI (spec, FLAC codec, WAV, proofs)
app/      SwiftUI macOS editor that calls the CLI
tests/    end-to-end tests against libFLAC (`flac`) and ffmpeg, plus a proof audit
```

## Quick start (macOS)

```sh
brew install flac ffmpeg          # reference codec for tests; ffmpeg for the app's imports
cd core && lake build             # proofs + the vericut binary (Lean v4.33.0, no Mathlib)
cd .. && python3 tests/test_vericut.py
cd app && swift run               # the editor; uses ../core/.lake/build/bin/vericut ($VERICUT_BIN overrides)
```

`app/dev/vericut-stub` is an unverified ffmpeg stand-in for app development only (`app/dev/README.md`).

CLI contract: `docs/cli.md`.

## What is proven (`core/VeriCut/Correctness.lean`)

| Theorem | Statement |
|---|---|
| `flac_roundTrip` | `Pcm.Valid x → Flac.decode (Flac.encode st x) = .ok x`, for all settings `st`. |
| `export_correct` | For valid clips in one format, `Flac.decode (exportClips st format clips) = .ok (splice format clips)`. |

Definitions they mention: `Spec/Audio.lean` (`Pcm`, `Pcm.Valid`, `Clip`, `splice`) and the codec
in `Flac/` (`Format.lean` gives a stream's meaning, `Parse.lean` reads it). `Pcm.valid_of_validate`
shows the CLI's run-time check establishes `Pcm.Valid`. `Examples.lean` discharges every
hypothesis on concrete audio. Both theorems use only `propext`, `Classical.choice`, `Quot.sound`.

The encoder (`Flac/Encode.lean`) uses CONSTANT, VERBATIM and FIXED (order 0–4) subframes,
wasted bits, left/right/mid-side stereo and partitioned Rice coding. LPC is decoded but not yet
produced.

## Trusted, not proven

- That our bitstream is standard FLAC (RFC 9639). The theorem is about our own decoder; that libFLAC
  and ffmpeg decode our files bit-exact, and that we decode theirs, is tested.
- WAV parsing and writing, file IO, JSON, the CLI glue in `Main.lean`.
- Lean's compiler and runtime.
- ffmpeg, which the app uses to convert other formats to WAV on import.

Speed and size against `flac`/ffmpeg: `bench/RESULTS-audio.md` (not committed).
