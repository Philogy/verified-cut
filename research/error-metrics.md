# What `approx` should be: error metrics and formal bounds

Research for `approx` in `core/SmartCut/Spec/Export.lean` (the `Encoder.faithful`
contract). All facts are from web sources (linked). Points the sources did not
confirm are marked *(unverified)*. My own inferences are marked *(inference)*.
Research date: 2026-10-31.

## TL;DR

- **Metrics you can compute exactly in Lean core**, using `Nat`/`Int`/`Rat` and
  comparisons only: SSE/MSE, PSNR thresholds (`PSNR ≥ P` is the same as
  `MSE ≤ MAX²/10^(P/10)`, so set the bound as a rational), max-abs error,
  SAD/SATD, block-wise MSE, and **SSIM with uniform 8×8 windows** (the
  x264/ffmpeg variant), which is a rational function of integer sums.
  Everything else needs transcendentals (log, exp, sqrt, cube roots, fractional
  powers), floats or IIR filters. Their reference implementation is in effect
  their definition.
- **Not reproducible bit-for-bit**: VMAF (SVM model, logs in VIF; float vs
  integer models differ), SSIMULACRA2 (independent ports agree only to about
  0.008 points), Butteraugli (results depend on the SIMD path), FLIP, CIEDE2000,
  XPSNR (`1/sqrt` weights in double).
- **No prior formal work fits this problem.** I found no verified video codec,
  no verified JPEG codec, no verified perceptual metric, and no formally
  guaranteed-PSNR encoder. What does exist: integer-exact transforms in
  H.264/HEVC, conformance specs (H.264.1/H.265.1), IDCT accuracy specs
  (IEEE 1180 / ISO 23002-1), verified lossless codecs (DEFLATE in Coq and Lean,
  QOI in Stainless), Halide rewrite and scheduling verification, and
  floating-point error tools (Gappa, Flocq, FPTaylor, Daisy). I found no
  "smart cut" correctness work at all, only bug reports.
- **Recommendation:** `approx` = a **per-plane frame-MSE bound plus a per-block
  MSE bound**, on the displayed frame, stated as exact rationals.
  **Check-then-accept** at runtime in Lean: try encodes from high to low QP,
  decode each, accept the first that passes, otherwise fail loudly. The
  `faithful` field then stops being a trusted claim about the encoder. It
  becomes a theorem about the checker, so no encoder-quality assumption remains.
  What stays trusted is that the ffmpeg decoder computes `Codec.step`, which is
  backed by H.264's normative bit-exact decoding, plus the "displayed frame"
  projection. SSIM/VMAF remain reported test numbers, not part of the spec.

---

## 1. Metrics

Notation: `x`, `y` are reference and test planes with N samples each, and
`MAX = 2^bitdepth − 1`.

| Metric | Definition (short) | Exact in ℚ? | Metric axioms | Reference impl. & determinism | Lean-core effort |
|---|---|---|---|---|---|
| **SSE / MSE** | Σ(x−y)², divided by N | **Yes** (Nat) | √SSE is the L² metric | Trivial. Exact in any integer implementation | ~20 lines |
| **PSNR** | 10·log10(MAX²/MSE) | Threshold form **yes** (`MSE ≤ MAX²·10^(−P/10)`, choose a rational) | Monotone in MSE, so not a metric itself | Pooling differs between tools, see below | Trivial in threshold form |
| **Per-plane / YUV-weighted PSNR** | JVET reports (6·PSNR_Y + PSNR_U + PSNR_V)/8, a mean of dB values. x264 pools SSE over the planes, which weights 4:1:1 by sample count in 4:2:0 [x264-devel][doom9] | Per-plane thresholds: yes. A 6:1:1 mean of dB values needs logs | n/a | JVET 6:1:1 taken from a summary of CTC, not checked against the CTC text *(unverified)* [mendevi CTC] | Trivial per plane |
| **Max-abs (L∞)** | max \|x−y\| | **Yes** | Metric | Exact | Trivial |
| **SAD / SATD** | Σ\|x−y\|, or Σ\|Hadamard(x−y)\| | **Yes** (integer Hadamard) | SAD is the L¹ metric | Encoder-internal, exact | Small |
| **Block-wise MSE / max** | MSE over k×k blocks, then the worst block | **Yes** | L² per block | Exact | Small |
| **SSIM (Wang 2004)** | [(2μxμy+C1)(2σxy+C2)]/[(μx²+μy²+C1)(σx²+σy²+C2)], C1=(0.01L)², C2=(0.03L)², 11×11 Gaussian window σ=1.5, mean over the map [Wang04][Wang SSIM page] | With a **Gaussian** window, no: irrational weights unless quantized. With **uniform 8×8 windows** (x264/ffmpeg: integer 4×4 sums, 8×8 windows, stride 4 [ffmpeg vf_ssim]), **yes**: means, variances and the formula are all rational. dB form needs log | Symmetric, S=1 iff x=y, but **no triangle inequality**. 1−S and √(1−S) are not metrics either. √(1−l) and √(1−cs) separately are [Brunet-Vrscay-Wang 2012] | ffmpeg's integer-sum path is near-exact, but the final step is float | Moderate (~100 lines, Rat) |
| **MS-SSIM** | 5 scales, exponents 0.0448/0.2856/0.3001/0.2363/0.1333 [Wang03 MS-SSIM] | **No** (fractional powers) | Not a metric | Float | Hard (needs fractional powers) |
| **VIF / VIFp** | Ratio of summed log2(1 + g²σ²/(σv²+σn²)) terms, a GSM/NSS model [Sheikh-Bovik 2006] | **No** (log2) | VIF(x,x)=1, can exceed 1, not a metric | Float | Hard |
| **VMAF** | VIF (4 scales) + DLM + motion, fused by an SVM regressor trained on MOS, 0–100 [Netflix blog via forasoft/paperswithcode] | **No** | Not a metric. Learned, gameable | libvmaf v3 has fixed-point features (`vmaf_v0.6.1`) and optional float (`vmaf_float_v0.6.1`). The two give close but different scores. No cross-platform bit-exactness claim found [libvmaf README][FAQ] | Impractical |
| **Butteraugli** | Per-pixel float diffmap. Score = max (L∞). The "3-norm" averages p=3, 6, 12 norms [libjxl butteraugli.h, metrics.cc] | **No** | Not a metric | Float. The SIMD path accumulates in double or float depending on the CPU, so results can differ | Impractical |
| **SSIMULACRA2** | XYB (cube root), 6 scales, SSIM + ringing + blur maps per channel, 1- and 4-norms, 108 tuned weights [cloudinary/ssimulacra2] | **No** | Not a metric | Defined by libjxl code (IIR Gaussian). The Vulkan port matches to ~0.008 points [Vship PR #32] | Impractical |
| **CIEDE2000 (ΔE00)** | CIELAB with atan2, cos, exp. **Discontinuous** at 180° hue differences [Sharma-Wu-Dalal 2005] | **No** | Not a metric (discontinuous, CIE restricts it to small differences) | Test data in the paper | Hard; also wrong tool for video |
| **FLIP** | CSF filtering in YCxCz, Hunt-adjusted Lab, HyAB distance, edge/point features [NVlabs/flip] (pipeline detail from memory, *unverified*) | **No** | Not a metric | Several implementations | Impractical |
| **XPSNR** | Block SSE weighted by 1/√(spatial+temporal activity), then PSNR [ffmpeg vf_xpsnr.c] | SSE and activity are integer; the weight is `1.0/sqrt` in double. **No** as specified; a rational version would be a new definition | Not a metric | ffmpeg filter | Moderate if redefined with `Nat.sqrt` |
| **CAMBI** | No-reference banding index: contrast steps at several scales, CSF-weighted, pooled. 0 = none, ~5 = slightly annoying [arXiv 2102.00079] | Not checked *(unverified)* | No-reference, so not a distance | In libvmaf | Out of scope (no-reference) |
| **Temporal / flicker** | E.g. difference of mean brightness or mean abs difference between adjacent frames [MSU BFM] | Yes (simple variants) | n/a | Ad hoc. ffmpeg has no flicker filter | Small |

### How codec designers actually use them

- **RDO**: the encoder minimises J = D + λR [Sullivan-Wiegand 1998]. In full
  mode decision D is **SSE**. HM uses λ = α·2^((QP−12)/3), α≈0.57. Fast intra
  pre-selection uses **SATD** (Hadamard) + λ·R_mode [arXiv 2203.01765,
  1907.02287]. Motion estimation using SAD/SATD + √λ·R_mv is from memory
  *(unverified)*.
- **Perceptual layers** sit on top of RDO. x264's psy-rd/psy-trellis and AQ
  lower PSNR/SSIM on purpose. `--tune psnr` sets aq-mode 0 and `--no-psy`;
  `--tune ssim` sets aq-mode 2 and `--no-psy` [x264 man page, base.c].
- **"Observability" = JND**: the visibility threshold set by luminance
  adaptation, contrast sensitivity, contrast masking and temporal masking.
  Codecs use pixel- or DCT-domain JND models (Watson's DCTune lineage) to shape
  quantisation [arXiv 2112.12284, Wu et al. survey]. JND points for video are
  measured per viewer (MCL-JCV dataset, satisfied-user-ratio curves) and
  predicted with VMAF + SVR [arXiv 1710.11090, 1807.00681]. A JND is a
  statistical property of viewers, not a function of two frames, so it can't
  be a spec. The "≈6 VMAF points per JND" rule of thumb is from secondary
  sources only *(unverified)*.
- **Quantisation error** *(standard theory, from the search summary)*: a
  uniform quantiser with step Δ has |e| ≤ Δ/2 in range, and MSE ≈ Δ²/12 is a
  high-resolution *approximation*, not a bound. Dead-zone rounding with offset
  f < ½ (the HM values f=1/3 intra, 1/6 inter are *unverified*) gives a
  worst-case coefficient error of (1−f)Δ. Qstep doubles every 6 QP. These are
  coefficient-domain bounds. A pixel bound would also need transform gain,
  prediction, clipping and deblocking, so a provable per-pixel bound for a real
  encoder isn't realistic.

## 2. Prior formal work

| Area | What exists | Relevance |
|---|---|---|
| **Decoder bit-exactness (specs)** | H.264 specifies its inverse transform exactly in integer add/shift, so encoder and decoder don't drift. HEVC's integer transforms use 16-bit stages and clip to the dynamic range [Budagavi JSTSP 2013][MPEG-IF h264_transform]. MPEG-1/2/4 only bounded the IDCT, so they drift [guru.multimedia.cx]. H.264.1/H.265.1 give conformance bitstreams. HEVC suites publish YUV MD5s, and decoded-picture-hash SEI carries MD5/CRC/checksum [ITU H.264.1, H.265.1][rusty_h265] | **This is what justifies modelling the decoder as a function `Codec.step`.** That H.264.1 itself mandates YUV MD5s is *unverified* |
| **IDCT accuracy specs** | IEEE 1180-1990 (withdrawn): ppe ≤ 1, pmse ≤ 0.06, omse ≤ 0.02, pme ≤ 0.015, ome ≤ 0.0015, zero in → zero out, tested on random blocks against a double-precision reference. ISO/IEC 23002-1 restates it, and 23002-2 gives a conforming fixed-point IDCT [M4IF, VDE preview, MPEG] | A *statistical* accuracy spec checked by testing, not proof. Shows the field's precedent: closeness is stated as MSE/peak thresholds |
| **Verified codecs / decoders** | Lossless only: DEFLATE in Coq [Senjak-Hofmann arXiv 1609.01220]; **lean-zip** (Lean 4, `inflate (deflateRaw d l) = .ok d`, >1,100 theorems, scope beyond round-trip *unverified*) [kim-em/lean-zip]; QOI in Stainless [Bucev 2022]; Narcissus (Coq, derived encoders/decoders) [arXiv 1803.04870]; EverParse (F*, TLS/ASN.1, no media formats) [project-everest]. Wuffs (PNG etc.) is memory-safe only, not functionally verified [Wuffs docs] | **Nothing found for JPEG, H.264, HEVC or any lossy codec.** I also found nothing formalising a lossy codec's error |
| **Verified image processing** | Halide's term rewriter checked with SMT + Coq: 4 wrong rules, 8 non-terminating ones found [Newcomb et al. OOPSLA 2020]. Verified scheduling via Coq rewrites [Liu et al. POPL 2022]. HaliVer (deductive verification of Halide pipelines, likely VerCors) [arXiv 2401.10778] | Correctness of pipelines (semantics preserved), not error metrics |
| **Floating-point error bounds** | Gappa (emits Coq proofs, straight-line code) [arXiv 0801.0523]; Flocq; VCFloat2 (Coq/CompCert) [Appel]; Ramananandro et al. CPP 2016, "certified error bounds for signal processing" [normalesup]; FPTaylor (HOL Light certificates), Daisy/Rosa, FPBench [fptalks.org]; verified certificate checker in Coq/HOL4 [arXiv 1707.02115] | Could in principle bound a float implementation of a metric. **I found no verified DCT/IDCT error bound or verified perceptual metric** (Capretta's exact FFT in Coq etc. are from memory, *unverified*) |
| **Guaranteed-quality coding** | Near-lossless L∞ coding (JPEG-LS/CALIC style: residuals quantised in a DPCM loop) guarantees \|e\| ≤ τ by construction, so PSNR ≥ 20·log10(MAX/τ). This work is published without machine-checked proofs [arXiv 2103.17015, 2002.03482]. Verified neural compressed sensing (bounds for NN reconstruction) [arXiv 2405.04260] | None formalised. **No formally guaranteed-PSNR encoder found** |
| **Perceptual metrics, formally** | Only the math above (Brunet-Vrscay-Wang on SSIM's metric properties; Sharma on ΔE00's discontinuity) | **No mechanised work found** |
| **Smart cut / lossless editing** | LosslessCut calls smart cut "very experimental" (duplicate segments, workarounds) [LosslessCut troubleshooting]. Avidemux copy mode skips segments and drops frames [avidemux forum]. ffmpeg has no "re-encode to next keyframe then copy" mode; it's requested on ffmpeg-devel 2024/2025 [ffmpeg-devel] | **No formal work found.** This project appears to be the first |
| **Encoder determinism** | No documentation found that VideoToolbox output is reproducible. Its output changes across OS versions [Apple forums 702891, 667629]. Comparing decoded-frame hashes (framemd5) is the robust check | Supports *checking decoded output* rather than trusting or replaying the encoder |

## 3. Recommendation for verified-cut

### What to put in `approx`

1. **Per-plane frame MSE bound** (Y, U, V separately), on the **displayed,
   cropped frame** extracted from `Pic` (`Pic` is the whole DPB). Use separate
   planes so chroma errors can't hide in a pooled number. This is the D that
   RDO minimises, it is reflexive and symmetric, and √SSE is a metric. It is
   exact in `Nat`.
2. **Per-block worst-case MSE bound** (e.g. 16×16 luma, 8×8 chroma), looser
   than the frame bound. *(inference)* A frame-average bound alone misses
   localised corruption. One fully garbage 16×16 block (error 128 per sample)
   in a 1080p frame adds only 256·128²/(1920·1080) ≈ **2.0** to the frame MSE,
   and that passes a 40 dB (MSE ≤ 6.5) bound. A block bound catches bad
   macroblocks and slice errors, which are exactly the smart-cut failure modes.
3. **Dimension, bit-depth and range equality** as part of `approx`. Colour-range
   or pixel-format bugs then show up as failures instead of passing silently
   *(inference: a limited/full range swap produces a large SSE, so the check
   catches it)*.
4. **Thresholds as rationals, chosen from PSNR**: MSE_max = MAX²·10^(−P/10). For
   8-bit: 35 dB→20.56, 38→10.31, **40→6.50**, 42→4.10, **45→2.06**, 50→0.65.
   Pick defaults by measuring VideoToolbox boundary frames on `samples/`.
   I found no source for typical VideoToolbox PSNR.
5. **No temporal term needed** *(inference)*: copied neighbours have error 0, so
   the per-frame bound already caps the quality "pop" at each copy/encode seam,
   and caps flicker across the re-encoded run.
6. **Not in the spec**: SSIM (only the uniform-window variant is rational, and
   it isn't a metric), MS-SSIM, VIF, VMAF, Butteraugli, SSIMULACRA2, FLIP,
   CIEDE2000, XPSNR. Report them in `tests/` as numbers (ffmpeg `ssim`,
   `libvmaf`, `xpsnr` filters). If a perceptual gate is ever wanted, uniform-8×8
   SSIM is the one that can be specified exactly in Lean.

### Provable / runtime-checked / trusted

| | |
|---|---|
| **Proved** | `approx` is reflexive (SSE x x = 0) and symmetric. `checkedEncode` returns `some s` only if `AllRel approx (decode c s) pics`, by construction. `export_correct` then needs no encoder-quality contract. The existing copy theorems are unchanged |
| **Runtime-checked (in Lean)** | Decode each candidate boundary segment (ffmpeg → rawvideo pipe), compute per-plane and per-block SSE in Lean, compare against the rational bounds. Retry at higher quality (VideoToolbox `-q:v` 0–100 is Apple Silicon only; then libx264 at lower CRF), then fail. `libx264 -qp 0` is lossless but forces High 4:4:4 Predictive, which poor decoders can't play and which won't match the copied stream's SPS, so don't use it as the fallback [x264-devel, ffmpeg-devel 2021] |
| **Trusted** | (a) The ffmpeg decoder (and the player's decoder) computes `Codec.step` on these bitstreams. This is the new trust the check adds, and it rests on H.264's normative bit-exact decoding plus conformance testing. (b) `display : Pic → Frame`, i.e. picking the output picture and cropping. (c) The raw-YUV I/O plumbing. **Encoder quality is no longer trusted.** |

### Lean sketch (core only; not typechecked)

```lean
/-- One 8-bit sample plane, row-major. -/
structure Plane where
  width  : Nat
  height : Nat
  data   : ByteArray

/-- The displayed, cropped picture of a decoder state. -/
structure Frame where
  y : Plane
  u : Plane
  v : Plane

def Plane.sse (a b : Plane) : Nat := Id.run do
  let mut acc := 0
  for i in [0:a.data.size] do
    let p := a.data[i]!.toNat
    let q := b.data[i]!.toNat
    let d := if p ≤ q then q - p else p - q
    acc := acc + d * d
  return acc

/-- SSE of the `k×k` block at block coordinates `(bx, bz)`; partial edge blocks included. -/
def Plane.blockSSE (a b : Plane) (k bx bz : Nat) : Nat := sorry -- same loop over the block

/-- Error budget as exact mean-squared-error bounds per sample. -/
structure Tolerance where
  lumaMSE        : Rat   -- e.g. 6503/1000 ≈ 40 dB
  chromaMSE      : Rat
  blockSize      : Nat   -- luma; chroma uses blockSize / 2
  lumaBlockMSE   : Rat
  chromaBlockMSE : Rat

def Plane.close (frameMSE blockMSE : Rat) (k : Nat) (a b : Plane) : Prop :=
  a.width = b.width ∧ a.height = b.height ∧ a.data.size = b.data.size ∧
  (a.sse b : Rat) ≤ frameMSE * a.data.size ∧
  ∀ bx < (a.width + k - 1) / k, ∀ bz < (a.height + k - 1) / k,
    (a.blockSSE b k bx bz : Rat) ≤ blockMSE * (k * k)

def Frame.close (t : Tolerance) (a b : Frame) : Prop :=
  a.y.close t.lumaMSE   t.lumaBlockMSE   t.blockSize       b.y ∧
  a.u.close t.chromaMSE t.chromaBlockMSE (t.blockSize / 2) b.u ∧
  a.v.close t.chromaMSE t.chromaBlockMSE (t.blockSize / 2) b.v

/-- `approx` for the Encoder contract: compare only what is displayed. -/
def approxBy (display : Pic → Frame) (t : Tolerance) (p q : Pic) : Prop :=
  Frame.close t (display p) (display q)
-- needs: `instance : Decidable (Frame.close t a b)` (bounded ∀ + Rat ≤),
-- `theorem approxBy_refl (h : 0 ≤ bounds) : approxBy d t p p`.

/-- Untrusted proposer, trusted check: the first candidate that decodes close enough. -/
def checkedEncode (c : Codec α Pic) (approx : Pic → Pic → Prop)
    [∀ p q, Decidable (approx p q)] (candidates : List Pic → List (Stream α))
    (pics : List Pic) : Option (Stream α) :=
  (candidates pics).find? fun s =>
    s.WellFormed' && decide (AllRel approx (decode c s) pics)  -- WellFormed' : Bool version

theorem checkedEncode_sound :
    checkedEncode c approx cands pics = some s → AllRel approx (decode c s) pics := sorry
```

Then `Encoder.faithful` stops being a field. Export returns `Option`/`Except`,
and `export_correct` becomes "if export succeeds, the result is close". In the
CLI, `decode c` is evaluated by running ffmpeg, which is assumption (a) above.
`AllRel` needs a `Decidable` instance (structural, easy). Performance
*(inference)*: a 1080p 4:2:0 frame is ~3.1 M samples, one pass of `ByteArray`
indexing, and only boundary frames (e.g. 28 per export) are checked.

## Sources

- libvmaf README / FAQ: https://github.com/Netflix/vmaf/blob/master/libvmaf/README.md, https://github.com/Netflix/vmaf/blob/master/resource/doc/faq.md ; fixed-point paper: https://proceedings.spiedigitallibrary.org/conference-proceedings-of-spie/11510/115100G/
- VMAF overview: https://www.forasoft.com/learn/video-quality/articles-vqm/vmaf-explained ; https://cs.paperswithcode.com/paper/toward-a-practical-perceptual-video-quality
- SSIM: https://www.cns.nyu.edu/pub/lcv/wang03-preprint.pdf ; https://ece.uwaterloo.ca/~z70wang/research/ssim/ ; MS-SSIM: https://www.cns.nyu.edu/pub/eero/wang03b.pdf
- SSIM math properties: https://ece.uwaterloo.ca/~z70wang/publications/TIP_SSIM_MathProperties.pdf
- ffmpeg SSIM: https://ffmpeg.org/doxygen/trunk/vf__ssim_8c_source.html ; XPSNR: https://ffmpeg.org/doxygen/8.0/vf__xpsnr_8c_source.html
- VIF: https://live.ece.utexas.edu/research/Quality/VIF.htm
- SSIMULACRA2: https://github.com/cloudinary/ssimulacra2 ; https://codeberg.org/Line-fr/Vship/pulls/32
- Butteraugli: https://raw.githubusercontent.com/libjxl/libjxl/main/lib/jxl/butteraugli/butteraugli.h ; https://raw.githubusercontent.com/libjxl/libjxl/main/lib/extras/metrics.cc
- CIEDE2000: https://hajim.rochester.edu/ece/sites/gsharma/ciede2000/
- FLIP: https://github.com/NVlabs/flip ; https://research.nvidia.com/publication/flip
- CAMBI: https://arxiv.org/pdf/2102.00079
- Flicker (MSU BFM): https://compression.ru/video/quality_measure/metric_plugins/bfm_en.htm
- PSNR pooling: https://mailman.videolan.org/pipermail/x264-devel/2004-August/000050.html ; https://forum.doom9.org/archive/index.php/t-144373.html ; https://mendevi.readthedocs.io/1.3.2/dataset/explore/ctc.html
- RDO: https://www.microsoft.com/en-us/research/?p=799324 ; https://arxiv.org/pdf/2203.01765 ; https://arxiv.org/pdf/1907.02287
- x264 tunes: https://dyn.manpages.debian.org/trixie/x264/x264.1.en.html ; https://github.com/mirror/x264/blob/master/common/base.c
- JND: https://arxiv.org/pdf/2112.12284 ; https://arxiv.org/pdf/1710.11090 ; https://ar5iv.arxiv.org/html/1807.00681
- Quantiser: https://hevc.hhi.fraunhofer.de/HM-doc/_t_com_tr_quant_8h_source.html
- Transforms / drift: https://eems.mit.edu/wp-content/uploads/2014/10/budagavi_jstsp_2013.pdf ; https://mpegif.org/files/h264_transform.pdf ; https://guru.multimedia.cx/the-mpeg124-and-h26123-idct/
- Conformance: https://www.itu.int/rec/T-REC-H.264.1-200503-S/en ; https://www.itu.int/rec/T-REC-H.265.1-201410-S ; https://docs.rs/crate/rusty_h265/0.6.0
- IDCT accuracy: https://mpegif.org/lists-sub/pipermail/mp4-tech/2003-January/001587.html ; https://www.vde-verlag.de/iec-normen/preview-pdf/info_isoiec23002-1{ed1.0}en.pdf ; https://mpeg.chiariglione.org/node/151
- Verified lossless codecs: https://arxiv.org/pdf/1609.01220 ; https://github.com/kim-em/lean-zip ; https://repositum.tuwien.at/bitstream/20.500.12708/81370/1/Bucev-2022-Formally%20Verified%20Quite%20OK%20Image%20Format-vor.pdf ; https://arxiv.org/pdf/1803.04870 ; https://project-everest.github.io/everparse/ ; https://skia.googlesource.com/external/github.com/google/wuffs/+show/HEAD/README.md
- Halide: https://2020.splashcon.org/details/splash-2020-oopsla/42/ ; https://people.csail.mit.edu/lamanda/assets/documents/LiuPOPL2022.pdf ; https://www.arxiv.org/pdf/2401.10778
- FP error tools: https://arxiv.org/pdf/0801.0523 ; https://arxiv.org/pdf/1707.02115 ; https://www.normalesup.org/~ramanana/research/2016cpp.pdf ; https://www.cs.princeton.edu/~appel/papers/vcfloat2.pdf ; https://fptalks.org/benchmarks.html
- Near-lossless L∞: https://arxiv.org/pdf/2103.17015 ; https://arxiv.org/pdf/2002.03482 ; verified NN sensing: https://arxiv.org/pdf/2405.04260
- Smart cut: https://github.com/mifi/lossless-cut/blob/master/docs/troubleshooting.md ; https://avidemux.org/smif/index.php?msg=94407 ; https://ffmpeg.org/pipermail/ffmpeg-devel/2025-July/346918.html
- VideoToolbox: https://developer.apple.com/forums/thread/702891 ; https://developer.apple.com/forums/thread/667629 ; https://ffmpeg.org/pipermail/ffmpeg-devel/2021-March/278019.html
