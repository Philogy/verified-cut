# Pipelines

Two audio pipelines, both Lean 4.33, core only, no Mathlib. Lossless is on `main` (`core/`,
`app/`). Lossy is on branch `lossy` (worktree `~/Documents/verified-cut-lossy`), a separate lake
project in `lossy/`, not merged. The untracked `lossy/` in the `main` checkout is an unfinished
merge attempt that was stopped; it is gitignored and not described here.

Legend: **proven** = covered by a headline theorem; **checked** = a run-time check that a lemma
turns into the theorem's hypothesis; **trusted** = outside the proofs.

## 1. Lossless (`main`)

```mermaid
flowchart LR
  pick[file picked in app] --> imp{probe ok and<br/>project format?}
  imp -- no --> ff[ffmpeg to WAV<br/>trusted]
  imp -- yes --> tl
  ff --> tl[timeline.json<br/>app, trusted]
  tl --> load[read WAV/FLAC<br/>Wav.parseFrames trusted<br/>decodeFast proven]
  load --> val[Pcm.validate<br/>checked]
  val --> splice[splice<br/>spec]
  splice --> enc[encodeFast<br/>proven]
  enc --> write[writeBinFile<br/>trusted]
  write --> out[(out.flac)]
  out -. Flac.decode, proven inverse .-> pcm[(same samples)]
```

The CLI runs the fast codec in `core/VeriCut/Flac/Fast/`. The spec codec in `core/VeriCut/Flac/`
(`encode`, `decode`) is written to be read and is what the theorems are stated over.

| stage | where | status |
|---|---|---|
| Import: WAV/FLAC in the project format is used as is, anything else goes through ffmpeg to a cached WAV | `app/Sources/VerifiedCut/Importer.swift:33` (`prepare`), `:44` (`convert`) | trusted. The timeline marks converted clips (`TimelineView.swift:177`) |
| Preview playback | `app/Sources/VerifiedCut/Model.swift:114` (`refresh`, AVMutableComposition) | trusted, preview only. Never feeds the export |
| Waveforms | `core/Main.lean:60` (`peaksBy`), `:91` (`peaks`) | trusted, display only. Tested against FLAC peaks |
| `probe`: header only, rejects what `export` can't encode, so the app converts it first | `core/Main.lean:45`; `Wav.header` `core/VeriCut/Wav.lean:57`; `Flac.probe` `Flac/Decode.lean:16` | trusted |
| CLI to app protocol | `docs/cli.md`; Swift side `app/Sources/VerifiedCut/VeriCut.swift:23` | trusted |
| Timeline parse, clip loading, range and format checks | `core/Main.lean:108` (`parseTimeline`), `:120` (`exportCmd`) | checked: ranges, equal formats, total < 2^36 |
| WAV sample parsing (format 1 and EXTENSIBLE, 8-bit unsigned) | `core/VeriCut/Wav.lean:65` (`parseFrames`), `:78` (`parse`) | **trusted**. Nothing proves the samples are what's in the file |
| Validity | `core/VeriCut/Export.lean:14` (`Pcm.isValid`), `:31` (`validate`); `Pcm.valid_of_validate` `Proofs/Splice.lean:80` | checked, then proven to imply `Pcm.Valid` |
| Splice | `core/VeriCut/Spec/Audio.lean` (`splice`, `Clip.samples`) | spec (part of the trusted surface) |
| Encode (CLI): plan each frame (block size, fixed predictor 0-4 or LPC, Rice partitions, stereo mode, wasted bits), write it, compute MD5 | `core/VeriCut/Flac/Fast/Encode.lean:223` (`encodeFast`), `:188` (`planFrame`), `:175` (`planSubframe`); LPC analysis `Flac/Fast/Lpc.lean` (Float, only proposes coefficients); `Flac/Fast/Md5.lean` | proven (round trip), except the MD5 value |
| Encode (spec): fixed predictors only, `Nat` bit writer | `core/VeriCut/Flac/Encode.lean:135` (`encode`); `Flac/Write.lean:72` (`writeStream`) | proven (round trip). Not run by the CLI |
| Decode (spec): parse bytes to `Stream`, its meaning is `Stream.samples` | `core/VeriCut/Flac/Decode.lean:8` (`decode`); `Flac/Parse.lean:189` (`streamP`); `Flac/Format.lean:156` (`Stream.samples`) | the reference all theorems are stated over |
| Decode (CLI): samples appended per frame, fused Rice reader | `core/VeriCut/Flac/Fast/Decode.lean:127` (`decodeFast`) | proven equal to `decode` on every input |
| CRC-8/16 | `core/VeriCut/Flac/Crc.lean`; checked on decode | proven (part of the round trip) |
| File write | `core/Main.lean:115` (`writeOut`) | trusted |
| `decode` command: FLAC to WAV | `core/Main.lean:179`, `Wav.write` `Wav.lean:89` | trusted |

### Theorems

`core/VeriCut/Correctness.lean`:

```lean
theorem flac_roundTrip (st : Flac.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.encode st x) = .ok x

theorem export_correct (st : Flac.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClips st format clips) = .ok (splice format clips)
```

`core/VeriCut/CorrectnessFast.lean`, for what the CLI runs, same hypotheses:

```lean
theorem decodeFast_eq (d : ByteArray) : Flac.Fast.decodeFast d = Flac.decode d

theorem flac_roundTrip_fast (st : Flac.Fast.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.Fast.encodeFast st x) = .ok x

theorem export_correct_fast (st : Flac.Fast.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClipsFast st format clips) = .ok (splice format clips)
```

Axioms: `propext`, `Classical.choice`, `Quot.sound` (checked with `#guard_msgs`).

They guarantee that for every encoder setting, our decoder gets back exactly the input samples
(and, for the export theorems, exactly the clips one after another). Encoder choices only affect
size.

They don't guarantee:
- That the bytes are standard FLAC. `Flac.decode` is our reading of RFC 9639. Agreement with
  libFLAC (`flac -d`, bit-exact) is tested in `tests/test_vericut.py`, not proven.
- That the STREAMINFO MD5 is right. It matches libFLAC's in tests.
- That the input samples are what's in the WAV file (`Wav.lean` is trusted), or what the user
  picked when ffmpeg converted it.
- Anything about the app, the preview, the waveforms, or the file landing on disk.

`Pcm.Valid` is part of the statement. Review it with `Format`, `Pcm`, `Clip`, `Clip.Valid` and
`splice`, all in `Spec/Audio.lean`.

## 2. Lossy (branch `lossy`, `lossy/`)

The output is a **standard `.flac` file**: lossyWAV-style. Samples are rounded to a coarser
grid, and FLAC's wasted-bits field then stores fewer bits per sample. There is no MP3 or AAC.
Any FLAC decoder plays the result. `flac -t` and ffmpeg accept it (`lossy/tests/run.py`).

```mermaid
flowchart LR
  wav[(in.wav)] --> parse[Wav.parse<br/>trusted]
  parse --> q[quantize q<br/>per 4096-sample block<br/>grid of 2^s, spec]
  q --> an[analyze<br/>wasted bits + fixed 0-4<br/>proven]
  an --> pack[frameBits / packInto<br/>proven]
  pack --> out[(out.flac)]
  out -. Lossy.decode, proven .-> y[(quantize q x)]
  y --> err[maxErr / sqErr<br/>spec]
```

| stage | where (`lossy/Lossy/...`) | status |
|---|---|---|
| WAV read/write | `Wav.lean:22` (`parse`, uses a `partial def findChunk`), `:43` (`render`) | trusted |
| Quantize: per block `f` of 4096 samples, `s = q - headroom(peak of block)`, round to the nearest multiple of `2^s`, clamped to the bit depth | `Spec/Quantize.lean:13` (`blockSize`), `:17` (`roundTo`), `:31` (`shift`), `:35` (`quantize`) | spec |
| Encode: per frame, round, find wasted bits, pick constant/verbatim/fixed 0–4, one Rice `k` per subframe, independent channels only | `Flac/Encode.lean:163` (`encodeFrame`), `:106` (`analyze`), `:97` (`wasted`), `:172` (`encode`) | proven |
| Decode: reads only this subset (no LPC, no stereo modes, no partitions), CRC not checked | `Flac/Decode.lean:105`, `:98` (`readStream`) | proven inverse |
| Error metrics | `Spec/Error.lean` (`diffs`, `maxErr`, `sqErr`) | spec |
| CLI `encode`/`decode`/`stats` | `lossy/Main.lean:15` | trusted. `stats` compares against `quantizeBlocks`, proven equal to `quantize` (`Proofs/Stream.lean:174`) |

### Theorems (`lossy/Lossy/Correctness.lean`)

```lean
theorem decode_encode_eq_quantize (q : Nat) (x : Pcm) (valid : x.Valid) :
    decode (encode q x) = some (quantize q x)

theorem lossless (x : Pcm) (valid : x.Valid) : decode (encode 0 x) = some x

theorem error_mono (x : Pcm) (valid : x.Valid) {q q' : Nat} (more : q ≤ q') :
    ∃ y y', decode (encode q x) = some y ∧ decode (encode q' x) = some y' ∧
      maxErr x y ≤ maxErr x y' ∧ sqErr x y ≤ sqErr x y'

theorem error_lt (x : Pcm) (valid : x.Valid) (q : Nat) :
    ∃ y, decode (encode q x) = some y ∧ maxErr x y < 2 ^ q
```

Same three standard axioms.

They **do** guarantee: the decoded signal is exactly `quantize q x`. `q = 0` is lossless. Raising
`q` never lowers the peak or squared error. No sample moves by `2^q` or more.

They **don't** guarantee:
- Perceptual quality. Error is in integer sample units with no psychoacoustics. SNR per block
  is roughly constant by construction, but that isn't stated.
- That size shrinks as `q` grows. Not stated, only measured.
- Standard FLAC conformance, same as lossless: tested, not proven.
- That the WAV reader is right.

## Lossy and lossless

The two were written in parallel and share no code: the lossy branch has its own `Pcm`
(per channel), bit layer, encoder and decoder. Main's encoder already emits wasted-bits
subframes, so lossy could become `encode (quantize q x)` on top of main's encoder, with the
round trip coming from `flac_roundTrip_fast`. That merge was started and stopped for time.
