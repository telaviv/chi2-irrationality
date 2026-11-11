/-
# Theorem B at a real weight `W`, step 1: the node expansion (copy of `Analytic/Nodes.lean` from `Wr` on)

`Analytic/Nodes.lean` works with `W = Wr q = q⁻²`; everything there depends on `q` only through `W > 0`. Here the
same objects are built for a real weight `W` (`pilot_chi2_2q/RESULT.md` §1: the analytic part depends only on
`w ∈ (0, 1)`):
* `HTW W h T`: the truncation of `Λ(u^{i+j})` at weight `W`; `abs_det_HTW_le`: its slot-form bound;
* at `W = WrZ ζ` (`ζ > 1`): `abs_DeltaZ_le_of`, a uniform bound on `|det HTW|` bounds `|Δ_h(χ₂(1/ζ); ζ)|`.
The `q`-free parts (`phiR`, `deriv_pow_phi`, `abs_phi_deriv_le`, slots, `Kslot`, `pairFactor`) are reused.
-/
import Chi2Irrational.QZ.PoleExpansion
import Chi2Irrational.Analytic.Nodes

namespace Chi2Irr
namespace QZ

open Polynomial Finset Filter Topology Matrix

/-- The node term of `Λ(u^n)` at `s = t + 1`, weight `W`. -/
noncomputable def nodeTermW (W : ℝ) (h n t : ℕ) : ℝ :=
  W ^ (t + 1) * ((n : ℝ) * ((t : ℝ) + 1) ^ (n - 1) * phiR h ((t : ℝ) + 1) +
    ((t : ℝ) + 1) ^ n * deriv (phiR h) ((t : ℝ) + 1))

/-- The truncated matrix at weight `W`. -/
noncomputable def HTW (W : ℝ) (h T : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∑ t ∈ range T, nodeTermW W h ((i : ℕ) + j) t

lemma LamMatZ_hasSum {ζ : ℚ} (hζ : 1 < ζ) (h : ℕ) (i j : Fin h) :
    HasSum (fun t => nodeTermW (WrZ ζ) h ((i : ℕ) + j) t) (LamMatZ ζ h i j) := by
  have hs := summable_LamZ_summand hζ h ((X : ℚ[X]) ^ ((i : ℕ) + j))
  have hterm : ∀ t : ℕ, WrZ ζ ^ (t + 1) * deriv (fun u : ℝ =>
      aeval u ((X : ℚ[X]) ^ ((i : ℕ) + j)) * u / aeval u (Dpoly h)) ((t : ℝ) + 1) =
      nodeTermW (WrZ ζ) h ((i : ℕ) + j) t := by
    intro t
    rw [deriv_pow_phi h _ (by positivity)]
    unfold nodeTermW; ring
  have hs' := hs.congr hterm
  have hval : LamMatZ ζ h i j = ∑' t, nodeTermW (WrZ ζ) h ((i : ℕ) + j) t := by
    unfold LamMatZ LamZ
    exact tsum_congr hterm
  rw [hval]
  exact hs'.hasSum

lemma tendsto_det_HTW {ζ : ℚ} (hζ : 1 < ζ) (h : ℕ) :
    Tendsto (fun T => (HTW (WrZ ζ) h T).det) atTop (𝓝 (LamMatZ ζ h).det) := by
  have hmat : Tendsto (fun T => HTW (WrZ ζ) h T) atTop (𝓝 (LamMatZ ζ h)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => (LamMatZ_hasSum hζ h i j).tendsto_sum_nat
  exact ((continuous_id.matrix_det).tendsto _).comp hmat

/-- A uniform bound on the truncations bounds `|Δ_h(χ₂(1/ζ); ζ)|`. -/
theorem abs_DeltaZ_le_of {ζ : ℚ} (hζ : 1 < ζ) (h : ℕ) {B : ℝ} (hB : ∀ T, |(HTW (WrZ ζ) h T).det| ≤ B) :
    |aeval (chi2 (1 / (ζ : ℝ))) (DeltaZ ζ h)| ≤ B := by
  rw [aeval_chi2_DeltaZ hζ h]
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_det_HTW hζ h)) hB

/-! ### Rank-one form -/

/-- The coefficient of a triple at weight `W`. -/
noncomputable def cW (W : ℝ) (h : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  W ^ tnode k * (if (k.2 : ℕ) = 0 then deriv (phiR h) (tnode k) else phiR h (tnode k))

lemma HTW_rankOne (W : ℝ) (h T : ℕ) :
    HTW W h T = Matrix.of fun i j => ∑ k : Fin T × Fin 3,
      cW W h k * slotRow h (xslot k) i * slotRow h (yslot k) j := by
  ext i j
  simp only [HTW, Matrix.of_apply]
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun t => nodeTermW W h ((i : ℕ) + j) t) T]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.sum_univ_three]
  simp only [cW, xslot, yslot, tnode, slotRow, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp only [show (0 : ℕ) ≠ 1 by norm_num, show (0 : ℕ) ≠ 2 by norm_num, show (1 : ℕ) ≠ 2 by norm_num,
    show (1 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
    decide_false, decide_true, ite_true, ite_false, Bool.false_eq_true]
  unfold nodeTermW
  push_cast
  rw [pow_deriv_split]
  ring

/-! ### The bound on the truncated determinant -/

/-- The node weight `b(s) = W^s h φ(s)`. -/
noncomputable def bW (W : ℝ) (h s : ℕ) : ℝ := W ^ s * h * phiR h s

lemma abs_cW_le {W : ℝ} (hW : 0 < W) {h T : ℕ} (hh : 1 ≤ h) (k : Fin T × Fin 3) :
    |cW W h k| ≤ bW W h (tnode k) := by
  have hs : (1 : ℝ) ≤ (tnode k : ℝ) := by unfold tnode; push_cast; linarith [(k.1 : ℕ).cast_nonneg (α := ℝ)]
  have hphi := phiR_pos h (show (0 : ℝ) < tnode k by linarith)
  unfold cW bW
  rw [abs_mul, abs_of_pos (pow_pos hW _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hW _).le
  split_ifs
  · exact abs_phi_deriv_le hh hs
  · rw [abs_of_pos hphi]
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith

lemma bW_pos {W : ℝ} (hW : 0 < W) {h : ℕ} {s : ℕ} (hs : 1 ≤ s) (hh : 1 ≤ h) : 0 < bW W h s := by
  unfold bW
  have : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have := phiR_pos h (show (0 : ℝ) < s by assumption)
  positivity

/-- **The truncated determinant, slot form**, at weight `W > 0`. -/
theorem abs_det_HTW_le {W : ℝ} (hW : 0 < W) {h T : ℕ} (hh : 2 ≤ h) :
    |(HTW W h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      ∑ f : Fin h → Fin T × Fin 3, (if Function.Injective (fun i => xslot (f i)) then
        (∏ i, bW W h (tnode (f i))) *
          ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 else 0) := by
  have hfac : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have hA := factorial_smul_det_sum_rankOne (R := ℝ) (cW W h (T := T)) (fun k => slotRow h (xslot k))
    (fun k => slotRow h (yslot k))
  rw [← HTW_rankOne, Fintype.card_fin, nsmul_eq_mul] at hA
  have hdet : (HTW W h T).det = ((h.factorial : ℝ))⁻¹ * ∑ f : Fin h → Fin T × Fin 3,
      (∏ i, cW W h (f i)) * (Matrix.of fun i j => slotRow h (xslot (f i)) j).det *
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
    have hc : ∏ i, |cW W h (f i)| ≤ ∏ i, bW W h (tnode (f i)) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => abs_cW_le hW (by omega) (f i))
    have hP : 0 ≤ ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) :=
      Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => pairFactor_nonneg _ _))
    have hK : 0 ≤ Kslot h := by unfold Kslot; positivity
    have hb : 0 ≤ ∏ i, bW W h (tnode (f i)) :=
      Finset.prod_nonneg (fun i _ => (bW_pos hW (by unfold tnode; omega) (by omega)).le)
    calc (∏ i, |cW W h (f i)|) * |(Matrix.of fun i j => slotRow h (xslot (f i)) j).det| *
          |(Matrix.of fun i j => slotRow h (yslot (f i)) j).det|
        ≤ (∏ i, bW W h (tnode (f i))) * (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) *
            (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) := by
          gcongr
          · unfold Kslot; exact hX
          · unfold Kslot; exact hY
      _ = Kslot h ^ 2 * ((∏ i, bW W h (tnode (f i))) *
            ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2) := by
          simp_rw [Finset.prod_pow]; ring
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have h0 : (Matrix.of fun i j => slotRow h (xslot (f i)) j).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
    rw [h0]; simp

end QZ
end Chi2Irr
