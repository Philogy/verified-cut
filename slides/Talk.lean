module
public import VersoSlides

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Verified Cut" =>


# Thesis

Formalization allows faster hands-free optimization.

* Write a spec that is simple enough to review: a `Nat` bit writer, fixed predictors only
* Let agents optimize the real codec freely
* The proof is the gate: a change lands only if the theorems still hold against the *unchanged* spec

# What We Built

* A lossless FLAC encoder and decoder, written and proven in Lean 4 (no Mathlib)
* An audio splicer on top: cut clips out of WAV files, export one FLAC
* `vericut` CLI plus a SwiftUI macOS editor that calls it
* Output checked against libFLAC 1.5.0 and ffmpeg: they decode ours, we decode theirs, bit-exact

# The Spec: Audio and Splicing

```code lean4
structure Pcm where
  format : Format
  samples : Array Int        -- sample c of frame i is samples[i * channels + c]

def Clip.samples (c : Clip) : Array Int :=
  c.src.samples.extract (c.start * c.src.format.channels) (c.stop * c.src.format.channels)

def splice (format : Format) (clips : List Clip) : Pcm :=
  ⟨format, (clips.map Clip.samples).foldl (· ++ ·) #[]⟩
```

`Pcm.Valid`: what FLAC can carry (1-8 channels, 4-32 bits, samples in range).

# What Is Proven

`core/VeriCut/Correctness.lean`

```code lean4
theorem flac_roundTrip (st : Flac.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.encode st x) = .ok x

theorem export_correct (st : Flac.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClips st format clips) = .ok (splice format clips)
```

Only `propext`, `Classical.choice`, `Quot.sound`; checked in CI with `lake comparator`.

# The Fast Path

The CLI runs `Flac/Fast/` (LPC, 64-bit bit writer, streaming, MD5), tied to the same spec `decode`:

```code lean4
theorem decodeFast_eq (d : ByteArray) : Flac.Fast.decodeFast d = Flac.decode d

theorem flac_roundTrip_fast (st : Flac.Fast.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.Fast.encodeFast st x) = .ok x

theorem export_correct_fast ... :   -- export_correct's hypotheses
    Flac.decode (exportClipsFast st format clips) = .ok (splice format clips)
```

No extra hypotheses: bounds the fast code relies on are checked at run time, with a proven fallback.

# Packed Samples: a Data Refinement

`Array Int` is 8-byte pointers to boxed values; `PackedPcm` keeps 4 bytes per sample in a `ByteArray`.

```code lean4
def PackedPcm.toSpec : PackedPcm → Pcm      -- abstraction function

theorem encodePacked_eq (st : Settings) (x : PackedPcm) :
    encodePacked st x = encodeFast st x.toSpec

theorem flac_roundTrip_packed (st : Flac.Fast.Settings) (p : PackedPcm) (valid : p.toSpec.Valid) :
    Flac.decode (encodePacked st p) = .ok p.toSpec
```

* Podcast -5: peak memory 3.41 GB → 2.11 GB, 64.1 s → 60.5 s, byte-identical
* Not yet proven: packed WAV parser agrees with the spec one; its run-time check implies `Valid`

# Trusted, Not Proven

* That our bitstream is standard FLAC (RFC 9639): the theorems are about our own decoder; libFLAC interop is tested
* The STREAMINFO MD5: computed, matches libFLAC, no theorem mentions it
* WAV parsing and writing, file IO, JSON, CLI glue
* ffmpeg (app imports), the Swift app and its preview
* Lean's compiler and runtime

# Optimization Log

Piano 60.7 s at -5, median wall time; podcast 61.2 min at -5. Spec unchanged throughout.

```html
<table>
<tr><th>step</th><th>commit</th><th>result</th></tr>
<tr><td>Baseline: GMP for every <code>2 ^ k</code></td><td><code>b508a0b</code></td><td>piano encode 7.06 s; podcast 305 s</td></tr>
<tr><td>Planner: one-pass fixed-order choice</td><td><code>8d95b92</code></td><td>piano 7.06 s → 3.33 s</td></tr>
<tr><td>Bit writer in <code>UInt64</code></td><td><code>c58d6c2</code></td><td>piano 3.33 s → 0.76 s; podcast 305 s → 34.7 s</td></tr>
<tr><td>Streaming encoder and decoder</td><td><code>687147f</code></td><td>piano RSS 223 MB → 96 MB</td></tr>
<tr><td>LPC (libFLAC's method)</td><td><code>05433ac</code></td><td>piano 40.2 % → 37.3 % of WAV; 0.76 s → 1.29 s</td></tr>
<tr><td><code>Int64</code> residuals, Rice estimate</td><td><code>8b2fbe4</code></td><td>piano 1.29 s → 1.07 s</td></tr>
<tr><td>Spec restored, fast path separate</td><td><code>95565b4</code></td><td>same bytes, same speed</td></tr>
<tr><td>Packed samples</td><td><code>41e5646</code></td><td>podcast RSS 3.41 GB → 2.11 GB</td></tr>
</table>
```

# Pareto Frontier Over the Commits

```html
<img style="display:block;margin:0 auto;width:92vw;max-width:none;max-height:none" src="pareto.gif" alt="Size/speed Pareto frontier of vericut levels -0..-8 per commit against libFLAC">
```

# Where We Stand

```html
<div class="two-col" style="grid-template-columns:3fr 2fr">
<img style="max-width:100%;max-height:62vh" src="pareto-final.png" alt="Final vericut frontier vs libFLAC">
<div>
<table>
<tr><th>-5, piano / forest</th><th>vericut</th><th>libFLAC</th></tr>
<tr><td>encode s</td><td>1.160 / 0.509</td><td>0.067 / 0.034</td></tr>
<tr><td>size, % of WAV</td><td>37.26 / 18.64</td><td>37.33 / 18.78</td></tr>
<tr><td>piano decode s</td><td>0.329</td><td>0.042</td></tr>
</table>
<p style="font-size:0.6em;color:#7c6f64">Table: commit 95565b4, median wall time.</p>
</div>
</div>
```

* Within 0.3 % of libFLAC's size, slightly smaller at -0/-5/-8: we keep the cheapest candidate per subframe
* 10-17x slower to encode, ~8x to decode: no SIMD, and the hot loops still read samples as boxed `Int`
