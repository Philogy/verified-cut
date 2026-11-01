import VeriCut.Proofs.Codes

/-!
Round trip of a subframe: what `writeSubframe` writes, `subframeP` reads back,
for the subframes the encoder makes (`Subframe.WF`).
-/

namespace VeriCut.Flac

open Parser

/-- Fits in `bits`-bit two's complement. -/
def InRange (bits : Nat) (v : Int) : Prop := -2 ^ (bits - 1) ≤ v ∧ v < 2 ^ (bits - 1)

structure Partition.WF (paramBits count : Nat) (p : Partition) : Prop where
  rice : ∃ k, p.coding = .rice k ∧ k < 2 ^ paramBits - 1
  size : p.values.size = count

def Residual.paramBits (r : Residual) : Nat := if r.wide then 5 else 4

structure Residual.WF (n warmup : Nat) (r : Residual) : Prop where
  order : r.order < 16
  divides : n % 2 ^ r.order = 0
  fitsWarmup : warmup ≤ n / 2 ^ r.order
  first : ∃ p rest, r.parts.toList = p :: rest ∧ p.WF r.paramBits (n / 2 ^ r.order - warmup) ∧
    (∀ q ∈ rest, q.WF r.paramBits (n / 2 ^ r.order)) ∧ rest.length = 2 ^ r.order - 1

def Body.WF (bits n : Nat) : Body → Prop
  | .constant v => InRange bits v
  | .verbatim s => s.size = n ∧ ∀ v ∈ s, InRange bits v
  | .fixed warmup r => warmup.size ≤ 4 ∧ warmup.size ≤ n ∧ (∀ v ∈ warmup, InRange bits v) ∧ r.WF n warmup.size
  | .lpc precision shift coefs warmup r =>
    1 ≤ precision ∧ precision ≤ 15 ∧ shift < 16 ∧ coefs.size = warmup.size ∧ 1 ≤ warmup.size ∧
      warmup.size ≤ 32 ∧ warmup.size ≤ n ∧ (∀ c ∈ coefs, InRange precision c) ∧
      (∀ v ∈ warmup, InRange bits v) ∧ r.WF n warmup.size

structure Subframe.WF (bits n : Nat) (sf : Subframe) : Prop where
  wasted : sf.wasted < bits
  body : sf.body.WF (bits - sf.wasted) n

theorem roundTrip_partition (paramBits count : Nat) (p : Partition) (h : p.WF paramBits count) :
    RoundTrip (writePartition paramBits · p) (partitionP paramBits count) p := by
  obtain ⟨⟨k, hk, hlt⟩, hsize⟩ := h
  unfold partitionP
  rt RoundTrip.readBits paramBits k (by omega)
  · rw [if_neg (by omega)]
    rt RoundTrip.many' (xs := p.values.toList) (fun v _ => roundTrip_rice k v) #[] (by simp [hsize])
    · exact RoundTrip.pure' (by cases p; simp_all)
    · intro w; rfl
  · intro w; simp [writePartition, hk, ← Array.foldl_toList]

theorem roundTrip_residual (n warmup : Nat) (r : Residual) (h : r.WF n warmup) :
    RoundTrip (writeResidual r) (residualP n warmup) r := by
  obtain ⟨hord, hdiv, hwarm, first, rest, hparts, hfirst, hrest, hlen⟩ := h
  unfold residualP
  rt RoundTrip.readBits 2 (if r.wide then 1 else 0) (by split <;> decide)
  rt RoundTrip.check (c := decide ((if r.wide then 1 else 0) < 2)) _ (by split <;> decide)
  rt RoundTrip.readBits 4 r.order (by omega)
  rt RoundTrip.check _ (by simp [hdiv, hwarm])
  have pb : (if (if r.wide then 1 else 0) = 1 then 5 else 4) = r.paramBits := by
    unfold Residual.paramBits; cases r.wide <;> rfl
  simp only [pb]
  rt roundTrip_partition _ _ first hfirst
  rt RoundTrip.many' (xs := rest) (fun q hq => roundTrip_partition _ _ q (hrest q hq)) #[first] hlen.symm
  · refine RoundTrip.pure' ?_
    cases r with
    | mk wide order parts =>
      have : parts = (first :: rest).toArray := by rw [← hparts, Array.toArray_toList]
      subst this
      cases wide <;> simp
  rt_rfl
  intro w
  simp only [writeResidual, Residual.paramBits, ← Array.foldl_toList, hparts, List.foldl_cons, id]

theorem roundTrip_samples (bits : Nat) (hb : 0 < bits) (s : Array Int) (h : ∀ v ∈ s, InRange bits v)
    (acc : Array Int) (count : Nat) (hc : count = s.size) :
    RoundTrip (writeSamples bits · s) (many (readSigned bits) count acc) (acc ++ s) := by
  have := RoundTrip.many' (xs := s.toList) (count := count) (step := (·.writeSigned bits ·))
    (fun v hv => RoundTrip.readSigned bits v (h v (by simpa using hv)) hb) acc (by simp [hc])
  exact RoundTrip.congr this (fun w => by simp [writeSamples, ← Array.foldl_toList]) rfl (by simp)

theorem roundTrip_body (bits n : Nat) (hb : 0 < bits) (b : Body) (h : b.WF bits n) :
    RoundTrip (writeBody bits · b) (bodyP bits n b.typeCode) b := by
  unfold bodyP
  cases b with
  | constant v =>
    simp only [Body.typeCode, if_true]
    rt RoundTrip.readSigned bits v h hb
    · exact RoundTrip.pure' rfl
    rt_rfl
  | verbatim s =>
    obtain ⟨hs, hr⟩ := h
    simp only [Body.typeCode, if_pos, if_neg (by decide : (1 : Nat) ≠ 0)]
    rt roundTrip_samples bits hb s hr #[] n hs.symm
    · exact RoundTrip.pure' (by simp)
    rt_rfl
  | fixed warmup r =>
    obtain ⟨h4, hn, hw, hr⟩ := h
    simp only [Body.typeCode, if_neg (by omega : 8 + warmup.size ≠ 0), if_neg (by omega : 8 + warmup.size ≠ 1),
      if_pos (by omega : 8 ≤ 8 + warmup.size ∧ 8 + warmup.size ≤ 12), Nat.add_sub_cancel_left]
    rt RoundTrip.check _ (by simpa using hn)
    rt roundTrip_samples bits hb warmup hw #[] warmup.size rfl
    rt roundTrip_residual n warmup.size r hr
    · exact RoundTrip.pure' (by simp)
    rt_rfl
  | lpc precision shift coefs warmup r =>
    obtain ⟨hp1, hp15, hsh, hcw, ho1, ho32, hn, hc, hw, hr⟩ := h
    simp only [Body.typeCode, if_neg (by omega : 31 + coefs.size ≠ 0), if_neg (by omega : 31 + coefs.size ≠ 1),
      if_neg (by omega : ¬(8 ≤ 31 + coefs.size ∧ 31 + coefs.size ≤ 12)), if_pos (by omega : 32 ≤ 31 + coefs.size),
      show 31 + coefs.size - 31 = coefs.size by omega]
    rt RoundTrip.check _ (by simpa using (show coefs.size ≤ n by omega))
    rt roundTrip_samples bits hb warmup hw #[] coefs.size hcw
    rt RoundTrip.readBits 4 (precision - 1) (by omega)
    rt RoundTrip.check _ (by simpa using (show precision - 1 < 15 by omega))
    rt RoundTrip.readSigned 5 (shift : Int) (by constructor <;> simp <;> omega) (by decide)
    rt RoundTrip.check _ (by simp)
    rt roundTrip_samples (precision - 1 + 1) (by omega) coefs
      (by rw [show precision - 1 + 1 = precision by omega]; exact hc) #[] coefs.size rfl
    rt roundTrip_residual n coefs.size r (hcw ▸ hr)
    · exact RoundTrip.pure' (by simp; omega)
    rt_rfl
    intro w
    simp only [writeBody, show precision - 1 + 1 = precision by omega, id]

theorem roundTrip_wasted (k : Nat) :
    RoundTrip (fun w => if k = 0 then w.write 1 0 else ((w.write 1 1).zeros (k - 1)).write 1 1) wastedP k := by
  unfold wastedP
  by_cases hk : k = 0
  · subst hk
    rt RoundTrip.readBits 1 0 (by decide)
    · exact RoundTrip.pure' rfl
    rt_rfl
  · rt RoundTrip.readBits 1 1 (by decide)
    · simp only [if_true]
      rt roundTrip_unary (k - 1)
      · exact RoundTrip.pure' (by omega)
      rt_rfl
    rt_rfl
    intro w; simp [hk]

theorem roundTrip_subframe (bits n : Nat) (sf : Subframe) (h : sf.WF bits n) :
    RoundTrip (writeSubframe bits · sf) (subframeP bits n) sf := by
  obtain ⟨hw, hb⟩ := h
  have htype : sf.body.typeCode < 2 ^ 6 := by
    cases hc : sf.body <;> rw [hc] at hb <;> simp [Body.typeCode, Body.WF] at hb ⊢ <;> omega
  unfold subframeP
  rt RoundTrip.readBits 1 0 (by decide)
  rt RoundTrip.check _ (by decide)
  rt RoundTrip.readBits 6 _ htype
  rt roundTrip_wasted sf.wasted
  rt RoundTrip.check _ (by simpa using hw)
  rt roundTrip_body (bits - sf.wasted) n (by omega) sf.body hb
  · exact RoundTrip.pure' rfl
  rt_rfl

end VeriCut.Flac
