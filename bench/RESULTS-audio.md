# vericut FLAC vs libFLAC 1.5.0 / ffmpeg

Current state (`95565b4`, the CLI's fast path): within 0.3 % of libFLAC's size at levels 0, 5
and 8, 10-17x slower to encode, about 8x slower to decode, 3.5 GB peak RSS on a 61-minute
podcast. Table at the end of step 9. Plots: `bench/flac-progress.png`, `bench/pareto-final.png`, animation `bench/pareto.gif`
(`uv run bench/plot_pareto.py`). Steps 2-8 below were first made in the spec codec
and moved to `Flac/Fast/` in step 9; the spec is unchanged since `8a7a9cd`.

## Starting point (`bce05d8`, Apple M5 Pro, single run, wall clock)

Build `bce05d8` (fixed predictors only, no LPC, no SIMD, single thread, unoptimized Lean).

| clip (44.1k/16/stereo) | tool | s | bytes | ratio vs WAV |
|---|---|---|---|---|
| piano 60.7 s | vericut -0 / -5 / -8 | 5.75 / 7.75 / 8.02 | 4,329,519 / 4,305,416 / 4,305,403 | 40.4 / 40.2 / 40.2 % |
| | flac -0 / -5 / -8 | 0.07 / 0.09 / 0.18 | 4,337,855 / 3,997,227 / 3,927,037 | 40.5 / 37.3 / 36.7 % |
| | ffmpeg default / level 0 | 0.13 / 0.11 | 4,024,915 / 4,340,758 | |
| forest ambience 33 s | vericut -0 / -5 / -8 | 3.17 / 3.19 / 3.22 | 3,011,369 / 1,502,195 / 1,501,968 | 51.7 / 25.8 / 25.8 % |
| | flac -0 / -5 / -8 | 0.05 / 0.06 / 0.09 | 3,019,766 / 1,093,498 / 1,081,272 | 51.9 / 18.8 / 18.6 % |
| | ffmpeg default / level 0 | 0.08 / 0.08 | 1,094,416 / 1,518,773 | |
| vine boom 4.4 s | vericut -0 / -5 / -8 | 0.44 / 0.68 / 0.63 | 251,013 / 244,989 / 245,004 | |
| | flac -0 / -5 / -8 | 0.02 / 0.03 / 0.03 | 258,404 / 236,171 / 235,094 | |
| podcast 61.2 min | vericut -5 | 324 (5.37 GB RSS) | 151,418,805 | 23.4 % |

At level 0 (same toolset as `flac -0`: fixed predictors) we match libFLAC's size, and are ~80× slower.
At -5/-8 libFLAC won by 7–30 % in size through LPC, which we didn't emit then (added in step 6).
Decode of piano (flac -5 input): 1.9 s vs flac ~0.05 s. Podcast output: `flac -d` md5 = source md5.
Throughput was ~8–11× realtime, linear in length; memory ~88 B per sample (boxed `Array Int`).


## Optimization log

Data: `bench/flac-optimization.csv`, one row per (commit, clip, tool, level), appended by
`bench/flac_bench.py`. Method: each encode and each decode runs 5 times (3 for the
baseline, 1 for the 61-min podcast) under `nice -n 5`; the CSV has the median wall time and
the peak RSS over all runs (from `wait4`). Decode times decode the tool's own output to WAV.
Every vericut output is checked with `flac -t` and decoded with `flac -d`, bit-exact against
the source WAV, before its row is written. `ratio` is output bytes / WAV bytes. The reference
rows (`commit = ref`) are libFLAC 1.5.0 and ffmpeg 8 at the same levels. Other jobs were
running on the machine at times, so treat differences under ~10 % as noise.

Clips: piano 60.7 s, forest ambience 33 s, Dwarkesh podcast 61.2 min; all 44.1 kHz 16-bit stereo.

The theorems (`flac_roundTrip`, `export_correct`) keep their statements at every step; the
proofs were updated alongside the code, no `sorry`, only the standard axioms.

### 1. Profile (`b508a0b`)

`sample` on a piano -5 encode: ~60 % planning (of which most in `predict`), ~30 % writing,
~10 % WAV parsing, and throughout, GMP and malloc. The cause in every hot spot was the same:
`2 ^ k` on `Nat`/`Int` (and `Nat` shifts), which Lean computes through GMP, allocating, even
for small `k`. The predictor divided by `2 ^ shift` per sample, the bit writer reduced its
accumulator modulo `2 ^ k` per write, WAV parsing divided by `2 ^ 0` per sample. The planner
also did redundant work: five residual arrays per channel to pick the fixed order, and one
pass over the residual per partition order.

### 2. Planner (`8d95b92`): piano -5 7.06 s -> 3.33 s

* Fixed order chosen from one pass of `Int64` sums of |residual| for orders 0-4 (libFLAC's
  method); only the chosen order's residual is materialized.
* Partition sums computed once at the finest order and merged pairwise for coarser ones.
* `predict` shifts instead of dividing by `2 ^ shift` (same value: arithmetic shift is floor
  division; the round-trip proof didn't change).

Only choices changed, so the proof needed new invariants for the choosers, nothing else.

### 3. Bit writer (`c58d6c2`): piano -5 3.33 s -> 0.76 s, forest -5 1.25 s -> 0.34 s

* `Writer` keeps pending bits in a `UInt64` (fewer than 8 between writes); a write of up to
  56 bits is a shift-add and at most 7 byte pushes. Its correctness is the old lemma
  `write_bits : (w.write k v).bits = w.bits ++ natBits k v`, re-proved for the new
  representation, so nothing above the bit layer noticed.
* A Rice code is one write (`q` zeros, a one, `k` bits) when it fits in 56 bits.
* CRC-8/16 table loops in `UInt32`; WAV reading and writing without per-sample powers.

Podcast -5: 305 s -> 34.7 s encode, 74 s -> 43.7 s decode, RSS still ~10 GB.

### 4. Decoder powers (`41816e5`): piano decode 1.03 s -> 0.42 s

`pow2 k` (`UInt64` shift, proved `= 2 ^ k`) for Rice values and signed reads, so decoding a
Rice code no longer allocates; the WAV writer goes through `Int64` bytes.

### 5. Streaming (`687147f`): RSS piano 223 MB -> 96 MB, podcast decode 43.7 s -> 15.2 s

* The decoder appends each frame's samples as it parses it (`streamSamplesP`), so no
  `Stream` of all frames (with their residual arrays) is held. Proved equal to
  `streamP` followed by `Stream.samples` for every input, not just encoder output.
* The encoder plans and writes one frame at a time (`encodeFrames`); `encode_body` proves the
  bytes equal writing the array of planned frames.

The podcast still peaked at ~5.3 GB here because the decoder preallocated its output with an
uncapped-then-clamped capacity that made it regrow; fixed in the next commit (capacity is not
observable, so the proof only needs `Array.emptyWithCapacity_eq`). What remains is the input:
`Pcm.samples : Array Int` is part of the theorem statement, so the whole input lives in memory
as 8 bytes per sample (1.3 GB for the podcast) next to the WAV bytes being parsed.

### 6. LPC (`05433ac`): piano -5 40.2 % -> 37.3 % of WAV, forest -5 25.8 % -> 18.6 %

libFLAC's method, in `Flac/Lpc.lean`: Tukey(0.5) window, autocorrelation, Levinson-Durbin for
every order up to 8 (12 at -7/-8), order chosen by expected residual bits, coefficients
quantized to libFLAC's precision for the block size with error feedback. Level 8 tries three
windows (Tukey 0.5, 0.1, 0.9) where libFLAC uses `subdivide_tukey(3)`. All of it is `Float` and
only proposes `(precision, shift, coefficients)`; `lpcBody` computes the residual in `Int` and
checks what the format needs (order 1-32, precision 1-15, shift 0-15, coefficients in range;
residual under 2^30 for other decoders), and the planner keeps whichever of verbatim, fixed and
LPC is smallest. The proof needed `Body.WF` for `.lpc` and its parser/writer round trip; the
decoder already implemented LPC. Float literals had to become top-level constants: inside a loop
`0.5` is `OfScientific.ofScientific`, parsed through GMP on every iteration.

Sizes now beat libFLAC slightly at -5 and -8 on both clips (piano -5 3,989,002 vs 3,997,227
bytes; forest -8 1,073,205 vs 1,081,272), at a cost in speed: piano -5 0.76 s -> 1.29 s.

### 7. Int64 residual, Rice estimate (`8b2fbe4`): piano -5 1.29 s -> 1.07 s

Residuals in `Int64` when nothing can overflow, with an `Int` fallback (proved equal); Rice
parameter from libFLAC's estimate, then +-1; zigzag sums in `UInt64`. Dead end on the way: the
first `Int64` version was 25 % *slower*. The guard compared against the literal `2 ^ 36`, and a
`Nat` literal of `2 ^ 32` or more compiles to `lean_cstr_to_nat("68719476736")`, parsed from a
string on every iteration. Moving it into a `@[noinline]` constant fixed it.

### 8. MD5 (`27cd261`), fused Rice reader (`e0ed3ec`)

STREAMINFO MD5 per RFC 1321 in `UInt32`, a chunk at a time; it matches libFLAC's digest and
costs about 1 %. `flac -t` no longer warns. The decoder reads a Rice partition in one loop that
allocates nothing per value: piano decode 0.41 s -> 0.31 s.

### 9. Spec restored, fast path separate (`95565b4`): same bytes, same speed

Steps 2-8 had edited the spec definitions (`Flac.encode`, `Flac.decode` and what they use) in
place. By request, the spec is back at `8a7a9cd` exactly (the simple `Nat` writer, fixed
predictors only, `Stream` then `Stream.samples`), and every speedup lives in `Flac/Fast/`:

* `decodeFast`, with `decodeFast_eq : decodeFast d = decode d` for every `d`;
* `encodeFast` (LPC, Rice estimate, `Int64` prediction, the 64-bit writer, streaming frames, MD5),
  with `flac_roundTrip_fast : decode (encodeFast st x) = .ok x` and `export_correct_fast`, stated
  over the spec's `decode` and with the same hypotheses as `flac_roundTrip`/`export_correct`.
  No extra hypotheses: bounds the fast code relies on (`Int64` sums) are checked at run time,
  with a fallback to the `Int` code, and that fallback is part of what is proved.

The CLI runs the fast path. Output is byte-identical to `e0ed3ec` on every clip at levels 0, 5
and 8, and timings match. From here on every commit is benchmarked at all levels 0-8 on piano
and forest against libFLAC 0-8 (for Pareto plots), and on the podcast at -5.

Where we stand against libFLAC (piano / forest, median wall time):

| level | vericut encode s | flac encode s | vericut bytes | flac bytes |
|---|---|---|---|---|
| -0 | 0.69 / 0.32 | 0.04 / 0.03 | 4,329,538 / 3,011,386 | 4,337,855 / 3,019,766 |
| -5 | 1.16 / 0.51 | 0.07 / 0.03 | 3,989,000 / 1,085,094 | 3,997,227 / 1,093,498 |
| -8 | 2.30 / 0.99 | 0.14 / 0.07 | 3,923,398 / 1,073,203 | 3,927,037 / 1,081,272 |

Decode: piano 0.33 s vs 0.04 s. Podcast -5: encode 52.7 s vs 3.3 s, decode 11.3 s vs 1.8 s, peak
RSS 3.5 GB vs 3 MB, 131,356,914 vs 131,359,912 bytes.

What remains and why:
* ~10-17x slower to encode, ~8x to decode. libFLAC is hand-tuned C with SIMD for
  autocorrelation, residuals and Rice sums. We have no SIMD; samples are `Array Int`, one boxed
  slot (8 bytes) per sample with a scalar/bignum check on every access, and each analysis step
  makes a fresh array. Parsing goes through a `Parser` monad of closures.
* Memory: `Pcm.samples : Array Int` appears in the theorem statements, so the whole input is
  held as `Array Int` (1.3 GB for the podcast), next to the WAV bytes and the output. libFLAC
  streams. Closing this needs a streaming encoder that is proved equal frame by frame.
* Size: we're within 0.3 % of libFLAC, and slightly smaller at every level shown, because we
  keep the cheapest of all candidates per subframe while libFLAC estimates.
