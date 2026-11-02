module
public import VersoSlides

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Vericut" =>

# What

* A lossless audio encoder and decoder, written and proven in Lean 4
* A thin GUI, in Swift acts as the interface
* Output checked against libFLAC 1.5.0 and ffmpeg

# Why

* Video & Audio editing software is notoriously performance constrained
* Lossless encoding good target for formalization and auto-research
* Test how vanilla Lean4 + auto-research compares against hardcore optimized codec libs

# Project Learnings I — Agents (while Smart) are Still Pretty Dumb

Opus 5.5 (medium) *not only* missed a trivial optimization, *but also*
repeatedly failed to implement when prompted.

*Possible Cause:* Top-level specification overly constrained the agent?

# Project Learnings II — Vanilla Lean4 still Lacks important Low-level Optimization Facilities

- `Array α` does *not* unbox small, fixed types such as `UInt32` and
  structures (as of `v4.36.0-rc1`)
- SIMD, and other hardware specific low-level primitives (e.g. Apple Silicon's
  ARM NEON) are not natively available
- workarounds possible but increase the TCB (`unsafe`, `implemented_by`, FFI)



# What Is Proven


```code lean4
theorem flac_roundTrip (st : Flac.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.encode st x) = .ok x

theorem export_correct (st : Flac.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClips st format clips) = .ok (splice format clips)
```


## + The Fast Path


```code lean4
theorem decodeFast_eq (d : ByteArray) : Flac.Fast.decodeFast d = Flac.decode d

theorem flac_roundTrip_fast (st : Flac.Fast.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.Fast.encodeFast st x) = .ok x

theorem export_correct_fast ... :   -- export_correct's hypotheses
    Flac.decode (exportClipsFast st format clips) = .ok (splice format clips)
```

No extra hypotheses: bounds the fast code relies on are checked at run time, with a proven fallback.

# Attempted But Scrapped

- Video encoding formalization
- lossy compression with formalized loss measurement


# Pareto Frontier Over the Commits

```html
<img class="img-plot" src="pareto.gif" alt="Size/speed Pareto frontier of vericut levels -0..-8 per commit against libFLAC">
```

# Where We Stand

```html
<div class="two-col" style="grid-template-columns:3fr 2fr">
<img style="max-width:100%;max-height:62vh" src="pareto-final.png" alt="Final vericut frontier vs libFLAC">
<div>
<img style="max-width:100%" src="vs-libflac.png" alt="vericut vs libFLAC at -5: encode time, size, decode time">
<p style="font-size:0.6em;color:#7c6f64">-5, commit 95565b4, median wall time.</p>
</div>
</div>
```

* Within 0.3 % of libFLAC's size, slightly smaller at -0/-5/-8: we keep the cheapest candidate per subframe
* 10-17x slower to encode, ~8x to decode: no SIMD, and the hot loops still read samples as boxed `Int`

# Low Hanging Fruit & Future Work

- Avoid big integer overhead by using fixed size types
- expose lower-level `SIMD` directives via simple `implemented_by` wrappers
- Handroll packed, aligned "Array" type
- Use faster program language (either eDSL or Rust + prover tooling)
