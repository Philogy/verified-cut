# Pipelines

Two audio pipelines. Lossless is on `main` (`core/`, `app/`). Lossy lives on branch `lossy`
(worktree `~/Documents/verified-cut-lossy`) as its own lake project, `lossy/`. It is not merged.
Both are Lean 4.33, core only, no Mathlib.

Legend: **proven** = covered by a headline theorem; **checked** = a run-time check that a lemma
turns into the theorem's hypothesis; **trusted** = outside the proofs.

## 1. Lossless (`main`)

```mermaid
flowchart LR
  pick[file picked in app] --> imp{probe ok and<br/>project format?}
  imp -- no --> ff[ffmpeg to WAV<br/>trusted]
  imp -- yes --> tl
  ff --> tl[timeline.json<br/>app, trusted]
  tl --> load[read WAV/FLAC<br/>Wav.parseFrames trusted<br/>Flac.decode]
  load --> val[Pcm.validate<br/>checked]
  val --> splice[splice<br/>spec]
  splice --> enc[Flac.encode<br/>proven]
  enc --> write[writeBinFile<br/>trusted]
  write --> out[(out.flac)]
  out -. Flac.decode, proven inverse .-> pcm[(same samples)]
```

| stage | where | status |
|---|---|---|
| Import: native WAV/FLAC in the project format is used as is, anything else goes through ffmpeg to a cached WAV | `app/Sources/VerifiedCut/Importer.swift:33` (`prepare`), `:44` (`convert`) | trusted. The timeline marks converted clips (`TimelineView.swift:179`) |
| Preview playback | `app/Sources/VerifiedCut/Model.swift:114` (`refresh`, AVMutableComposition) | trusted, preview only. Never feeds the export |
| Waveforms | `core/Main.lean:56` (`peaksBy`), `:87` (`peaks`); WAV read straight from the bytes in Int64 (`:73`) | trusted, display only. Tested against FLAC peaks |
| `probe`: header only, rejects what `export` can't encode, so the app converts it first | `core/Main.lean:41`; `Wav.header` `core/VeriCut/Wav.lean:54`; `Flac.probe` `Flac/Decode.lean:16` | trusted |
| CLI to app protocol | `docs/cli.md`; Swift side `app/Sources/VerifiedCut/VeriCut.swift:23` | trusted |
| Timeline parse, clip loading, range and format checks | `core/Main.lean:104` (`parseTimeline`), `:116` (`exportCmd`) | checked: ranges, equal formats, total < 2^36 |
| WAV sample parsing (format 1 and EXTENSIBLE, 8-bit unsigned) | `core/VeriCut/Wav.lean:62` (`parseFrames`), `:75` (`parse`) | **trusted**. Nothing proves the samples are what's in the file |
| Validity | `core/VeriCut/Export.lean:14` (`Pcm.isValid`), `:31` (`validate`); `Pcm.valid_of_validate` `Proofs/Splice.lean:80` | checked, then proven to imply `Pcm.Valid` |
| Splice | `core/VeriCut/Spec/Audio.lean:44` (`splice`), `Clip.samples` `:40` | spec (part of the trusted surface) |
| Encode: plan a `Stream` (block size, fixed predictor 0–4, Rice partitions, stereo mode, wasted bits), then write it | `core/VeriCut/Flac/Encode.lean:135` (`encode`), `:111` (`planFrame`), `:98` (`planSubframe`); `Flac/Write.lean:72` (`writeStream`) | proven (round trip) |
| Decode: parse bytes to `Stream`, its meaning is `Stream.samples` | `core/VeriCut/Flac/Decode.lean:8`; `Flac/Parse.lean:189` (`streamP`); `Flac/Format.lean:156` (`Stream.samples`) | proven inverse of encode. Also reads LPC subframes, which the encoder never emits |
| CRC-8/16 | `core/VeriCut/Flac/Crc.lean`; checked on decode `Flac/Parse.lean:144,149` | proven (part of the round trip) |
| File write, STREAMINFO MD5 = 0 | `core/Main.lean:111` (`writeOut`) | trusted. `flac -t` warns about the MD5 |
| `decode` command: FLAC to WAV | `core/Main.lean:175`, `Wav.write` `Wav.lean:86` | trusted |

### Theorems (`core/VeriCut/Correctness.lean`)

```lean
theorem flac_roundTrip (st : Flac.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.encode st x) = .ok x

theorem export_correct (st : Flac.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClips st format clips) = .ok (splice format clips)
```

Axioms: `propext`, `Classical.choice`, `Quot.sound` (checked with `#guard_msgs`).

They **do** guarantee that for every encoder setting, our own decoder gets back exactly the input
samples (and, for `export_correct`, exactly the clips one after another). Encoder choices only
affect size.

They **don't** guarantee:
- That the bytes are standard FLAC. `Flac.decode` is our reading of RFC 9639. Agreement with
  libFLAC (`flac -d`, bit-exact) is tested in `tests/test_vericut.py`, not proven.
- That the input samples are what's in the WAV file (`Wav.lean` is trusted), or what the user
  picked when ffmpeg converted it.
- Anything about the app, the preview, the waveforms, or the file actually landing on disk.
- `Pcm.Valid` (`Spec/Audio.lean:25`) is part of the statement. Review it alongside `Format`,
  `Pcm`, `Clip`, `Clip.Valid` and `splice`. All of them are in `Spec/Audio.lean`.

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

## What lossless and lossy share

They were written in parallel and duplicate each other. Neither imports the other.

| piece | main `core/VeriCut/` | lossy `lossy/Lossy/` |
|---|---|---|
| PCM type | `Spec/Audio.lean:14`: `Pcm := {format : Format, samples : Array Int}` **interleaved**; `Valid` allows `length < 2^36` | `Spec/Pcm.lean`: `Pcm := {rate, bits, chans : List (Array Int)}` **per channel**; `Valid` allows `length < 2^32`; `lo`/`hi` helpers |
| Bit I/O | `Flac/Bits.lean`: `Writer` (ByteArray accumulator), `Parser` monad over ByteArray | `Bits.lean`: `List Bool` + `packInto`; `Reader.lean`: own reader monad |
| Stream model | `Flac/Format.lean`: `Stream`/`Frame`/`Subframe`/`Body` (constant, verbatim, fixed, lpc), `Channels` incl. side/mid; semantics `Stream.samples` | no separate model: `Sub` in `Flac/Encode.lean` (const, verbatim, fixed with one Rice `k`) |
| Encoder | `Flac/Encode.lean`: `Settings`/levels, block 1152 or 4096, Rice partitions, stereo decorrelation, **wasted bits** | `Flac/Encode.lean`: fixed block 4096, one Rice `k`, independent channels, **wasted bits** |
| Decoder | `Flac/Parse.lean` + `Decode.lean`: general (LPC, all channel modes, variable block sizes, metadata skipping) | `Flac/Decode.lean`: own subset only |
| CRC | `Flac/Crc.lean`, checked on decode | `Bits.lean:66` + `crc16Bytes`, not checked on decode |
| WAV | `Wav.lean`: format 1 + EXTENSIBLE, 4–32 bits incl. 8-bit unsigned, `parseFrames` for partial reads | `Wav.lean`: format 1 + EXTENSIBLE, 16/24/32-bit only, whole file |
| Spec-only, new | – | `Spec/Quantize.lean`, `Spec/Error.lean`, `Proofs/Round.lean`, `Proofs/Quantize.lean` |

**Main's encoder already emits wasted-bits subframes.** In `core/VeriCut/Flac/Encode.lean:98`,
`planSubframe` takes `trailingZeros` of the OR of the samples, capped at `bits - 1`. It checks at
run time that every sample is a multiple of `2^w`, and then codes `s / 2^w`. The format carries
`Subframe.wasted` (`Flac/Format.lean:46`), and `Subframe.samples` multiplies it back in (`:136`).
It is covered by `flac_roundTrip` (`Proofs/Subframe.lean:105`, `roundTrip_wasted`).

### Merge sketch

Define lossy on main as quantize-then-lossless:

```lean
def encodeLossy (st : Flac.Settings) (q : Nat) (x : Pcm) : ByteArray := Flac.encode st (quantize q x)

theorem decode_encodeLossy (st) (q) (x : Pcm) (valid : x.Valid) :
    Flac.decode (encodeLossy st q x) = .ok (quantize q x) :=
  flac_roundTrip st _ (quantize_valid valid)
```

What's left to prove is `quantize_valid`. It is short, because `roundTo_spec`
(`lossy/Lossy/Proofs/Round.lean:72`) already gives `OnGrid`: a multiple of `2^s` within
`lo bits … hi bits`. It also needs `quantize` to preserve format and length. `lossless`,
`error_mono` and `error_lt` carry over unchanged from `Proofs/Quantize.lean`. The lossy
encoder, decoder, bit layer, reader, CRC and stream proofs (`Flac/`, `Bits`, `Reader`,
`Proofs/{Analyze,Bits,Frame,Pack,Stream,Sub,Codec}`, about 1,000 lines) would be deleted.

Blockers. None of them is fundamental:
1. **Different `Pcm`.** `quantize`, `maxErr`, `sqErr` and their proofs are written over
   per-channel `chans : List (Array Int)` and `bits`. Main is interleaved with a `Format`. We
   either restate `quantize` over interleaved samples (sample `k` is channel `k % ch` of frame
   `k / ch`, block `(k / ch) / 4096`) and re-prove `Round`/`Quantize`, or add a
   proven-bijective conversion between the two representations.
2. **Block alignment affects size only, never correctness.** Quantization blocks are 4096
   samples. Main uses 4096 at levels 3–8 but 1152 at levels 0–2, so frames there straddle
   quantization blocks. Wasted bits then fall to the smaller of the two shifts and compression
   drops. The round trip still holds. Fix: when `q > 0`, force `blockSize = 4096`, or make the
   quantization block a parameter equal to `st.blockSize`.
3. **Stereo decorrelation.** Mid/side and left/side of two grid-aligned channels stay multiples
   of `2^s`, because the shift is shared across channels in a block. So wasted bits survive.
   Mid = `(l + r) / 2` can lose one bit of alignment, but the encoder already falls back to the
   cheapest option.
4. **Length bounds.** Lossy `Valid` uses `< 2^32` and main uses `< 2^36`. The quantize proofs
   don't depend on that bound, so restating them is mechanical.
5. Main's wasted-bits detection is checked, not proven. That's fine: only the round trip
   matters, and the round trip holds either way. Whether quantized input actually gets smaller
   is a benchmark question.
