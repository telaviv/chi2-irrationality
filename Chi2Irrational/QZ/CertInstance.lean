/-
# Dual certificates at `w = (a/q)²`: from checked data to a `DualCertZ (q/a)` (copy of `Cert/Instance.lean`)

`CDataZ` is `Cert/Instance.lean`'s `CData` plus the numerator `a`: the weight is `w = (a/q)²`, i.e. the rational point
`ζ = q/a`, and the log-weight enclosure is `lw = 2·[log a] − 2·[log q]` (`((tabIV tab a).smul 2).add
((tabIV tab q).smul (-2))`, matching `scripts/q2num/gen_cert_z.py`). `CDataZ.Valid` collects the decidable checks;
`toCertZ` builds the `DualCertZ (q/a)` and `Phi_le` bounds its exponent by the rational `PhiQ`.
-/
import Chi2Irrational.QZ.TheoremB
import Chi2Irrational.Cert.Instance

namespace Chi2Irr
namespace QZ

open Chi2Irr.Cert Chi2Irr.Interval IV Finset

/-- Raw certificate data at `w = (a/q)²`. -/
structure CDataZ where
  a : ℕ
  q : ℕ
  L : ℕ
  s : ℕ
  K : ℕ
  X : ℕ
  N : ℕ
  tab : List ℤ
  cs : List ℚ
  lam : ℚ
  Sks : List ℚ
  Elo : ℚ

namespace CDataZ

variable (d : CDataZ)

def c (j : ℕ) : ℚ := d.cs.getD j 0

def D (j : ℕ) : ℚ :=
  if j ≤ d.K then 2 * (d.c j - (if j = 0 then 0 else d.c (j - 1))) else if j = d.K + 1 then 1 else -1

def α (j : ℕ) : ℤ := if j ≤ d.K then ((j * d.s : ℕ) : ℤ) else if j = d.K + 1 then 0 else -(d.L : ℤ)

/-- The enclosure of `log w = 2 log a − 2 log q`. -/
def lw : IV := ((tabIV d.tab d.a).smul 2).add ((tabIV d.tab d.q).smul (-2))

def Sk (k : ℕ) : ℚ := d.Sks.getD k 0

def σQ : ℚ := (d.Sks.map (fun v => max (v - d.lam) 0)).sum

/-- The certified exponent. -/
def PhiQ : ℚ := -d.Elo + d.lam + 2 / d.L * d.σQ

/-- The cell checks on `[lo, lo + n)`. -/
def cellsOK (lo n : ℕ) : Bool :=
  (List.range' lo n).all (fun k => cellOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.Sk k))

def EOK : Bool := (EIV d.tab d.s d.L d.c d.K).loGe d.Elo

def tailOK : Bool :=
  (d.lw.add (ofRat (1 / (d.X : ℚ)))).hiLt 0 && ((tabIV d.tab d.X).add (d.lw.smul (d.X : ℚ))).hiLt d.lam

lemma cells_of (lo n : ℕ) (h : d.cellsOK lo n = true) (k : ℕ) (hk1 : lo ≤ k) (hk2 : k < lo + n) :
    cellOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.Sk k) = true := by
  unfold cellsOK at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'_1.mpr ⟨hk1, hk2⟩)

/-- The checks. -/
structure Valid : Prop where
  a1 : 1 ≤ d.a
  aq : d.a < d.q
  L1 : 1 ≤ d.L
  X1 : 1 ≤ d.X
  NX : d.N ≤ d.X
  Ks : d.K * d.s ≤ d.N * d.L
  len : d.cs.length = d.K
  slen : d.Sks.length = d.X * d.L
  crange : ∀ v ∈ d.cs, 0 ≤ v ∧ v ≤ 2
  mass : d.cs.sum * d.s = d.L
  tab : checkTab d.tab 1 = true
  cells : ∀ k < d.X * d.L, cellOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.Sk k) = true
  tail : d.tailOK = true
  E : d.EOK = true

variable {d}

lemma c_nonneg (hv : d.Valid) (j : ℕ) : 0 ≤ d.c j := by
  rcases getD_zero_or_mem d.cs j with h | h
  · unfold c; rw [h]
  · exact (hv.crange _ h).1

lemma c_le_two (hv : d.Valid) (j : ℕ) : d.c j ≤ 2 := by
  rcases getD_zero_or_mem d.cs j with h | h
  · unfold c; rw [h]; norm_num
  · exact (hv.crange _ h).2

lemma c_K (hv : d.Valid) : d.c d.K = 0 := by
  unfold c; exact List.getD_eq_default _ _ (by rw [hv.len])

/-- Two adjacent blocks of cell checks combine. -/
lemma cellsOK_append (lo n m : ℕ) (h1 : d.cellsOK lo n = true) (h2 : d.cellsOK (lo + n) m = true) :
    d.cellsOK lo (n + m) = true := by
  unfold cellsOK at *
  rw [List.all_eq_true] at *
  intro k hk
  rw [List.mem_range'_1] at hk
  rcases lt_or_ge k (lo + n) with h | h
  · exact h1 k (List.mem_range'_1.mpr ⟨hk.1, h⟩)
  · exact h2 k (List.mem_range'_1.mpr ⟨h, by omega⟩)

/-- The rational point `ζ = q/a` of the certificate is `> 1`. -/
lemma one_lt_zeta (hv : d.Valid) : 1 < (d.q : ℚ) / d.a := by
  have ha : (0 : ℚ) < d.a := by exact_mod_cast (by have := hv.a1; omega : 0 < d.a)
  rw [one_lt_div ha]; exact_mod_cast hv.aq
/-- The step density of the certificate. -/
noncomputable def μ (hv : d.Valid) : StepData where
  K := d.K
  a := fun j => ((j * d.s : ℕ) : ℝ) / d.L
  c := fun j => (d.c j : ℝ)
  a0 := by simp
  amono := fun j => div_le_div_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_right _ (Nat.le_succ j))
    (Nat.cast_nonneg _)
  c0 := fun j => by exact_mod_cast c_nonneg hv j
  c2 := fun j => by exact_mod_cast c_le_two hv j
  mass := by
    have hL : (0 : ℝ) < d.L := by exact_mod_cast (by have := hv.L1; omega : 0 < d.L)
    have e : ∀ j ∈ range d.K, (d.c j : ℝ) * ((((j + 1) * d.s : ℕ) : ℝ) / d.L - ((j * d.s : ℕ) : ℝ) / d.L) =
        (d.s : ℝ) / d.L * (d.c j : ℝ) := fun j _ => by push_cast; ring
    rw [sum_congr rfl e, ← mul_sum]
    have hs := sum_range_getD d.cs (fun v => (v : ℝ))
    rw [hv.len] at hs
    simp only [c]
    rw [hs]
    have hm : ((d.cs.sum * d.s : ℚ) : ℝ) = (d.L : ℝ) := by exact_mod_cast hv.mass
    push_cast at hm
    rw [show (List.map (fun v : ℚ => (v : ℝ)) d.cs) = List.map Rat.cast d.cs from rfl]
    field_simp
    linarith

lemma mem_lw (hv : d.Valid) : d.lw.mem (Real.log (WrZ ((d.q : ℚ) / d.a))) := by
  have := mem_add (mem_smul 2 (mem_tabIV hv.tab d.a)) (mem_smul (-2) (mem_tabIV hv.tab d.q))
  have ha : (0 : ℝ) < d.a := by exact_mod_cast (by have := hv.a1; omega : 0 < d.a)
  have hq : (0 : ℝ) < d.q := by exact_mod_cast (by have := hv.aq; omega : 0 < d.q)
  have e : WrZ ((d.q : ℚ) / d.a) = ((d.a : ℝ) / d.q) ^ 2 := by
    unfold WrZ wtZ; push_cast; field_simp
  unfold lw
  rw [e, Real.log_pow, Real.log_div ha.ne' hq.ne']
  push_cast at this ⊢
  convert this using 1; ring

/-- `2U + V` as a sum of `ψ`-terms. -/
lemma F_eq (hv : d.Valid) (x : ℝ) :
    2 * (μ hv).U x + Vf (WrZ ((d.q : ℚ) / d.a)) x =
      ∑ j ∈ range (d.K + 3), (d.D j : ℝ) * psiF (x - (d.α j : ℝ) / d.L) + x * Real.log (WrZ ((d.q : ℚ) / d.a)) := by
  have hL : (d.L : ℝ) ≠ 0 := by exact_mod_cast (by have := hv.L1; omega : d.L ≠ 0)
  have hU : 2 * (μ hv).U x = ∑ j ∈ range (d.K + 1), (d.D j : ℝ) * psiF (x - (d.α j : ℝ) / d.L) := by
    unfold StepData.U Uint
    simp only [μ]
    rw [mul_sum]
    have := abel_sum (fun j => 2 * (d.c j : ℝ)) (fun j => psiF (x - ((j * d.s : ℕ) : ℝ) / d.L)) d.K
      (by simp [c_K hv])
    rw [show ∑ j ∈ range d.K, 2 * ((d.c j : ℝ) * (psiF (x - ((j * d.s : ℕ) : ℝ) / d.L) -
        psiF (x - (((j + 1) * d.s : ℕ) : ℝ) / d.L))) = ∑ j ∈ range d.K, 2 * (d.c j : ℝ) *
        (psiF (x - ((j * d.s : ℕ) : ℝ) / d.L) - psiF (x - (((j + 1) * d.s : ℕ) : ℝ) / d.L)) from
      sum_congr rfl (fun j _ => by ring), this]
    refine sum_congr rfl (fun j hj => ?_)
    have hjK : j ≤ d.K := by have := mem_range.mp hj; omega
    simp only [D, α, ite_eq_left hjK]
    push_cast
    split_ifs <;> push_cast <;> ring
  rw [show d.K + 3 = d.K + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ← hU]
  have h1 : d.D (d.K + 1) = 1 := by simp [D]
  have h2 : d.α (d.K + 1) = 0 := by simp [α]
  have h3 : d.D (d.K + 1 + 1) = -1 := by simp [D]
  have h4 : d.α (d.K + 1 + 1) = -(d.L : ℤ) := by simp [α]
  rw [h1, h2, h3, h4]
  unfold Vf
  push_cast
  rw [show x - -(d.L : ℝ) / d.L = x + 1 by rw [neg_div, div_self hL]; ring,
    show x - 0 / (d.L : ℝ) = x by simp]
  ring

/-- **The `DualCertZ` of checked data.** -/
noncomputable def toCertZ (hv : d.Valid) : DualCertZ ((d.q : ℚ) / d.a) where
  μ := μ hv
  lam := d.lam
  L := d.L
  X := d.X
  N := d.N
  Sk := fun k => (d.Sk k : ℝ)
  hL := hv.L1
  hN := by
    show ((d.K * d.s : ℕ) : ℝ) / d.L ≤ d.N
    have hL : (0 : ℝ) < d.L := by exact_mod_cast (by have := hv.L1; omega : 0 < d.L)
    rw [div_le_iff₀ hL]
    exact_mod_cast hv.Ks
  hXN := hv.NX
  hX := hv.X1
  hF := by
    intro k hk x _ hx0 hx1
    have hL : 0 < d.L := by have := hv.L1; omega
    have := cellOK_sound hv.tab hL d.D d.α (mem_lw hv) (d.K + 3) (hv.cells k hk) hx0 hx1
    rw [F_eq hv]
    exact this
  htail1 := by
    have h := hv.tail
    simp only [tailOK, Bool.and_eq_true] at h
    have := lt_of_hiLt (IV.mem_add (mem_lw hv) (mem_ofRat (1 / (d.X : ℚ)))) h.1
    push_cast at this
    linarith
  htail2 := by
    have h := hv.tail
    simp only [tailOK, Bool.and_eq_true] at h
    have := lt_of_hiLt (IV.mem_add (mem_tabIV hv.tab d.X) (mem_smul (d.X : ℚ) (mem_lw hv))) h.2
    push_cast at this
    linarith

/-- **The certified exponent.** -/
theorem Phi_le (hv : d.Valid) : (toCertZ hv).Phi ≤ (d.PhiQ : ℝ) := by
  have hL : (0 : ℝ) < d.L := by exact_mod_cast (by have := hv.L1; omega : 0 < d.L)
  -- `E(μ) ≥ E_lo`
  have hE : (d.Elo : ℝ) ≤ (μ hv).E := by
    have hm := mem_EIV hv.tab d.s (by have := hv.L1; omega : 0 < d.L) d.c d.K
    have := ge_of_loGe hm hv.E
    exact this
  -- `σ = σQ`
  have hσ : (toCertZ hv).σ = (d.σQ : ℝ) := by
    show ∑ k ∈ range (d.X * d.L), max ((d.Sk k : ℝ) - d.lam) 0 = _
    rw [← hv.slen]
    have := sum_range_getD d.Sks (fun v => max ((v : ℝ) - d.lam) 0)
    simp only [Sk]
    rw [this]
    unfold σQ
    push_cast
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left (fun v _ => ?_))
    simp
  unfold DualCertW.Phi PhiQ
  rw [hσ]
  show -(μ hv).E + (d.lam : ℝ) + 2 / (d.L : ℝ) * (d.σQ : ℝ) ≤ _
  push_cast
  linarith

end CDataZ

end QZ
end Chi2Irr
