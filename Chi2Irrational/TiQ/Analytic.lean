/-
# Theorem B for the signed weight `w = −q⁻²` (RESULT §4, referee fix F6)

Copies, for the Ti machine (namespace `Chi2Irr.TiQ`), of
* the node expansion of `Analytic/Nodes.lean` (`nodeTerm`, `HT`, `LamMat_hasSum`, `tendsto_det_HT`,
  `abs_Delta_le_of`, `cN`, `HT_rankOne`, `abs_cN_le`, `abs_det_HT_le`) with weight `WT q = wT q = −1/q²` in place of
  `Wr q = 1/q²`;
* `abs_det_HT_le_dual` (`Analytic/Dual.lean`), `DualCert.det_bound` and `DualCert.analytic` (`Analytic/TheoremB.lean`).

The only change is in `abs_cNT_le`: the node coefficient is `(wT q)^s · φ(s)` or `(wT q)^s · φ′(s)`, and
`|(wT q)^s| = Wr q ^ s`, so `|cNT| ≤ bN q h s` with the **same** node weight `bN` (built from `Wr q = |wT q|`).
Hence `abs_det_HTT_le` has exactly the right-hand side of `abs_det_HT_le`, and everything after the slot bound
(the dual bound, the certificate) is reused by name from the χ₂ files: a `DualCert q` sees only `|w| = q⁻²`.
-/
import Chi2Irrational.TiQ.PoleExpansion
import Chi2Irrational.Analytic.TheoremB

namespace Chi2Irr
namespace TiQ

open Polynomial Finset Filter Topology Matrix

/-! ### The truncations -/

/-- The signed weight `w = −q⁻²` as a real. -/
noncomputable def WT (q : ℕ) : ℝ := ((wT q : ℚ) : ℝ)

lemma abs_WT (q : ℕ) : |WT q| = Wr q := by
  unfold WT Wr wT wt
  push_cast
  rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]

/-- The node term of `ΛT(u^n)` at `s = t + 1`. -/
noncomputable def nodeTermT (q h n t : ℕ) : ℝ :=
  WT q ^ (t + 1) * ((n : ℝ) * ((t : ℝ) + 1) ^ (n - 1) * phiR h ((t : ℝ) + 1) +
    ((t : ℝ) + 1) ^ n * deriv (phiR h) ((t : ℝ) + 1))

/-- The truncated matrix. -/
noncomputable def HTT (q h T : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∑ t ∈ range T, nodeTermT q h ((i : ℕ) + j) t

lemma LamMatT_hasSum {q : ℕ} (hq : 2 ≤ q) (h : ℕ) (i j : Fin h) :
    HasSum (fun t => nodeTermT q h ((i : ℕ) + j) t) (LamMatT q h i j) := by
  have hs := summable_Lam_summandT hq h ((X : ℚ[X]) ^ ((i : ℕ) + j))
  have hterm : ∀ t : ℕ, ((wT q : ℚ) : ℝ) ^ (t + 1) * deriv (fun u : ℝ =>
      aeval u ((X : ℚ[X]) ^ ((i : ℕ) + j)) * u / aeval u (Dpoly h)) ((t : ℝ) + 1) =
      nodeTermT q h ((i : ℕ) + j) t := by
    intro t
    rw [deriv_pow_phi h _ (by positivity)]
    unfold nodeTermT WT; ring
  have hs' := hs.congr hterm
  have hval : LamMatT q h i j = ∑' t, nodeTermT q h ((i : ℕ) + j) t := by
    unfold LamMatT LamT
    exact tsum_congr hterm
  rw [hval]
  exact hs'.hasSum

lemma tendsto_det_HTT {q : ℕ} (hq : 2 ≤ q) (h : ℕ) :
    Tendsto (fun T => (HTT q h T).det) atTop (𝓝 (LamMatT q h).det) := by
  have hmat : Tendsto (fun T => HTT q h T) atTop (𝓝 (LamMatT q h)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => (LamMatT_hasSum hq h i j).tendsto_sum_nat
  exact ((continuous_id.matrix_det).tendsto _).comp hmat

/-- A uniform bound on the truncations bounds `|Δ^Ti_h(Ti₂(1/q))|`. -/
theorem abs_DeltaT_le_of {q : ℕ} (hq : 2 ≤ q) (h : ℕ) {B : ℝ} (hB : ∀ T, |(HTT q h T).det| ≤ B) :
    |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)| ≤ B := by
  rw [aeval_ti2_DeltaT hq h]
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_det_HTT hq h)) hB

/-! ### Rank-one form -/

/-- The coefficient of a triple (signed weight). -/
noncomputable def cNT (q h : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  WT q ^ tnode k * (if (k.2 : ℕ) = 0 then deriv (phiR h) (tnode k) else phiR h (tnode k))

lemma HTT_rankOne (q h T : ℕ) :
    HTT q h T = Matrix.of fun i j => ∑ k : Fin T × Fin 3,
      cNT q h k * slotRow h (xslot k) i * slotRow h (yslot k) j := by
  ext i j
  simp only [HTT, Matrix.of_apply]
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun t => nodeTermT q h ((i : ℕ) + j) t) T]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.sum_univ_three]
  simp only [cNT, xslot, yslot, tnode, slotRow, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp only [show (0 : ℕ) ≠ 1 by norm_num, show (0 : ℕ) ≠ 2 by norm_num, show (1 : ℕ) ≠ 2 by norm_num,
    show (1 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
    decide_false, decide_true, ite_true, ite_false, Bool.false_eq_true]
  unfold nodeTermT
  push_cast
  rw [pow_deriv_split]
  ring

/-! ### The bound on the truncated determinant -/

/-- `|cNT| ≤ b(s)` with the χ₂ node weight `b(s) = Wr^s h φ(s)`, since `|wT q| = Wr q`. -/
lemma abs_cNT_le {q h T : ℕ} (hq : 2 ≤ q) (hh : 1 ≤ h) (k : Fin T × Fin 3) :
    |cNT q h k| ≤ bN q h (tnode k) := by
  have hs : (1 : ℝ) ≤ (tnode k : ℝ) := by unfold tnode; push_cast; linarith [(k.1 : ℕ).cast_nonneg (α := ℝ)]
  have hW := Wr_pos q hq
  have hphi := phiR_pos h (show (0 : ℝ) < tnode k by linarith)
  unfold cNT bN
  rw [abs_mul, abs_pow, abs_WT, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hW _).le
  split_ifs
  · exact abs_phi_deriv_le hh hs
  · rw [abs_of_pos hphi]
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith

/-- **The truncated determinant, slot form** (same right-hand side as `abs_det_HT_le`). -/
theorem abs_det_HTT_le {q h T : ℕ} (hq : 2 ≤ q) (hh : 2 ≤ h) :
    |(HTT q h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      ∑ f : Fin h → Fin T × Fin 3, (if Function.Injective (fun i => xslot (f i)) then
        (∏ i, bN q h (tnode (f i))) *
          ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 else 0) := by
  have hfac : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have hA := factorial_smul_det_sum_rankOne (R := ℝ) (cNT q h (T := T)) (fun k => slotRow h (xslot k))
    (fun k => slotRow h (yslot k))
  rw [← HTT_rankOne, Fintype.card_fin, nsmul_eq_mul] at hA
  have hdet : (HTT q h T).det = ((h.factorial : ℝ))⁻¹ * ∑ f : Fin h → Fin T × Fin 3,
      (∏ i, cNT q h (f i)) * (Matrix.of fun i j => slotRow h (xslot (f i)) j).det *
        (Matrix.of fun i j => slotRow h (yslot (f i)) j).det := by
    rw [← hA]; field_simp
  rw [hdet, abs_mul, abs_of_pos (inv_pos.mpr hfac), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hfac).le
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun f _ => ?_))
  split_ifs with hinj
  · rw [abs_mul, abs_mul, Finset.abs_prod]
    have hX := abs_det_slot_le hh (fun i => xslot (f i))
    have hY := abs_det_slot_le hh (fun i => yslot (f i))
    simp only [xslot, yslot] at hX hY
    have hc : ∏ i, |cNT q h (f i)| ≤ ∏ i, bN q h (tnode (f i)) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => abs_cNT_le hq (by omega) (f i))
    have hP : 0 ≤ ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) :=
      Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => pairFactor_nonneg _ _))
    have hK : 0 ≤ Kslot h := by unfold Kslot; positivity
    have hb : 0 ≤ ∏ i, bN q h (tnode (f i)) :=
      Finset.prod_nonneg (fun i _ => (bN_pos hq (by unfold tnode; omega) (by omega)).le)
    calc (∏ i, |cNT q h (f i)|) * |(Matrix.of fun i j => slotRow h (xslot (f i)) j).det| *
          |(Matrix.of fun i j => slotRow h (yslot (f i)) j).det|
        ≤ (∏ i, bN q h (tnode (f i))) * (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) *
            (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) := by
          gcongr
          · unfold Kslot; exact hX
          · unfold Kslot; exact hY
      _ = Kslot h ^ 2 * ((∏ i, bN q h (tnode (f i))) *
            ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2) := by
          simp_rw [Finset.prod_pow]; ring
  · -- two equal x-slots: the x-minor vanishes
    rw [Function.Injective] at hinj
    push_neg at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have h0 : (Matrix.of fun i j => slotRow h (xslot (f i)) j).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
    rw [h0]; simp

/-! ### The dual bound (copy of `abs_det_HT_le_dual`) -/

/-- **The dual bound on the truncated determinant** (Ti machine). -/
theorem abs_det_HTT_le_dual {q h T M : ℕ} (hq : 2 ≤ q) (hh : 2 ≤ h) (hTM : T < M) (m : ℕ → ℝ)
    (hmsum : ∑ s ∈ range M, m s = h) (lam : ℝ) (S0 : ℕ) :
    |(HTT q h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      (Real.exp (Cd h M m lam + 2 * ∑ s ∈ range (S0 + 1), max (gD q h M m lam s) 0) *
        (∑ k : Fin T × Fin 3, zf q h M m lam S0 k) ^ h) := by
  refine (abs_det_HTT_le hq hh).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg _))
  rw [Finset.sum_pow', Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun f _ => ?_)
  split_ifs with hinj
  · refine (pattern_le hq hh hTM m hmsum lam f hinj).trans ?_
    have hsplit := split_near_far (q := q) hTM m lam S0 f hinj
    have hz : ∏ i, zf q h M m lam S0 (f i) =
        Real.exp (∑ i, (if tnode (f i) ≤ S0 then 0 else gD q h M m lam (tnode (f i)))) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      unfold zf; split_ifs <;> simp
    rw [hz, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => by
      unfold zf; split_ifs
      · norm_num
      · exact (Real.exp_pos _).le))

/-! ### Theorem B from a dual certificate (copy of `DualCert.det_bound`, `DualCert.analytic`) -/

namespace DualCertT

variable {q : ℕ} (C : DualCert q)

/-- **The truncated determinants, uniformly in `T`** (Ti machine). -/
theorem det_bound (hq : 2 ≤ q) {h : ℕ} (hh : 2 ≤ h) (T : ℕ) :
    |(HTT q h T).det| ≤ Real.exp (C.Phi * (h : ℝ) ^ 2 + C.Rem h) := by
  have hh1 : 1 ≤ h := by omega
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  set M := T + C.N * h + 1 with hMdef
  have hM : C.N * h + 1 ≤ M := by omega
  have hTM : T < M := by omega
  have hmsum : ∑ s ∈ range M, C.μ.mref h s = h := by
    rw [sum_range_support hM (C.μ.mref h) (C.μ.mref_zero h) (fun n hn => C.μ.mref_supp hh1 (C.hS hh1) n hn)]
    exact C.μ.sum_mref_cells hh1 (C.hS hh1)
  have hdual := abs_det_HTT_le_dual hq hh hTM (C.μ.mref h) hmsum (h * C.lam + h * Real.log h) (C.X * h)
  -- the pieces
  have hfar := C.far_le hq (T := T) hh1
  have hnear := C.near_le hq hh1 hM
  have hCd := C.Cd_le hh1 hM
  have hK := log_Kslot_sq_le hh1
  have hZ := C.Zb_pos hh1
  have hKpos : 0 < Kslot h ^ 2 := by unfold Kslot; positivity
  have hfac1 : (1 : ℝ) ≤ h.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero h)
  have hfac : ((h.factorial : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hfac1
  have hzf0 : 0 ≤ ∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k :=
    Finset.sum_nonneg (fun k _ => by unfold zf; split_ifs <;> positivity)
  have hpow : (∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k) ^ h ≤
      C.Zb h ^ h := pow_le_pow_left₀ hzf0 hfar h
  refine hdual.trans ?_
  generalize hE1 : Cd h M (C.μ.mref h) (h * C.lam + h * Real.log h) +
    2 * ∑ s ∈ range (C.X * h + 1), max (gD q h M (C.μ.mref h) (h * C.lam + h * Real.log h) s) 0 = E1
  have hstep : ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 * (Real.exp E1 *
      (∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k) ^ h) ≤
      Real.exp (Real.log (Kslot h ^ 2) + E1 + h * Real.log (C.Zb h)) := by
    calc ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 * (Real.exp E1 *
          (∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k) ^ h)
        ≤ 1 * Kslot h ^ 2 * (Real.exp E1 * C.Zb h ^ h) := by gcongr
      _ = _ := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hKpos, Real.exp_nat_mul, Real.exp_log hZ]; ring
  refine hstep.trans (Real.exp_le_exp.mpr ?_)
  -- the exponent
  have hnear' : ∑ s ∈ range (C.X * h + 1), max (gD q h M (C.μ.mref h) (h * C.lam + h * Real.log h) s) 0 ≤
      (h * |2 * C.μ.U 0 - C.lam| + h * Real.log h + 2 * C.errB h) + h * (((h : ℝ) / C.L + 1) * C.σ) +
        (C.X * h : ℕ) * (Real.log h + Real.log ((C.X * h : ℕ) : ℝ) + 2 * C.errB h) := hnear
  have hL0 : (0 : ℝ) < C.L := by exact_mod_cast (by have := C.hL; omega : 0 < C.L)
  have eΦ : C.Phi * (h : ℝ) ^ 2 = (h : ℝ) ^ 2 * (C.lam - C.μ.E) + 2 * h * ((h : ℝ) / C.L * C.σ) := by
    unfold DualCert.Phi; field_simp; ring
  unfold DualCert.Rem
  rw [← hE1, eΦ]
  nlinarith

/-- **Theorem B for the Ti machine** (from a dual certificate for `|w| = q⁻²`). -/
theorem analytic (hq : 2 ≤ q) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)| ≤ Real.exp ((C.Phi + ε) * (h : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨a, b, c, hR⟩ := C.Rem_le
  filter_upwards [eventually_small a b c ε hε, eventually_ge_atTop 2] with h hsmall hh
  refine abs_DeltaT_le_of hq h (fun T => (det_bound C hq hh T).trans (Real.exp_le_exp.mpr ?_))
  have := hR h (by omega)
  nlinarith

end DualCertT

/-- **Theorem B for the signed weight** (RESULT §4): the stub `analytic_t` of `TiQ/Interface.lean`. -/
theorem analytic_t_proof {q : ℕ} (C : DualCert q) (hq : 2 ≤ q) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)| ≤ Real.exp ((C.Phi + ε) * (h : ℝ) ^ 2) :=
  DualCertT.analytic C hq

end TiQ
end Chi2Irr
