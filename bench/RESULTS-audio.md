# vericut FLAC vs libFLAC 1.5.0 / ffmpeg

## Starting point (`bce05d8`, M-series Mac, single run, wall clock)

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
At -5/-8 libFLAC wins by 7–30 % in size through LPC; we don't emit LPC yet.
Decode of piano (flac -5 input): 1.9 s vs flac ~0.05 s. Podcast output: `flac -d` md5 = source md5.
Throughput ~8–11× realtime, linear in length; memory ~88 B per sample (boxed `Array Int`).


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
