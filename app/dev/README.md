# App development without the Lean CLI

`vericut-stub` answers the CLI contract below with ffmpeg doing the work, so the app
can run before (or without) a `lake build` of `core/`. Nothing it does is verified.

```sh
app/dev/make-test-audio.sh                      # synthetic clips in samples/synth/ (untracked)
VERICUT_BIN=$PWD/app/dev/vericut-stub swift run --package-path app
VERICUT_BIN=$PWD/app/dev/vericut-stub scripts/vm.sh install   # same, in the Tart VM
```

Needs `python3` (stdlib only) and ffmpeg (`$FFMPEG`, else Homebrew's).

## CLI contract the app relies on

JSON on stdout; on error a nonzero exit and a message on stderr, which the app shows.

| command | stdout |
|---|---|
| `vericut probe <file.wav\|file.flac>` | `{"sampleRate":int,"channels":int,"bitsPerSample":int,"samples":int,"format":"wav"\|"flac"}`, `samples` per channel |
| `vericut peaks <file> <buckets>` | `{"min":[...],"max":[...]}`, `buckets` floats each in [-1, 1], of the mono mix |
| `vericut export <timeline.json> <out.flac> [--level N]` | `{"samples":int,"bytes":int,"ms":int}` |

Timeline: `{"clips":[{"src":"path","in":int,"out":int}]}`, half-open sample ranges. All
sources share rate, channels and bit depth; the app guarantees it by converting on import.

## Import (outside the verified boundary)

The first clip sets the project format: its own if `vericut probe` reads it, else
44.1 kHz / 16-bit / stereo. A WAV or FLAC already in the project format is used as is.
Anything else (MP3, M4A, float WAV, another rate, channel count or bit depth) is
converted once by ffmpeg to an integer-PCM WAV in `~/Library/Caches/VerifiedCut/imports/`,
and the app and `vericut` only ever see that WAV. Converted clips show a ⟲ badge.

The app asks for `min(samples / 32, 100000)` peak buckets per file and only draws the
part of each waveform that is on screen. The stub needs about 3 s for an hour of audio.
