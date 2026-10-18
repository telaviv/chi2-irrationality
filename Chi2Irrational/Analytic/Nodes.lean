/-
# Theorem B, step 1: the node expansion

With `W = q⁻²`, `D(u) = ∏_{k<h}(u + k + ½)`, `φ(u) = u/D(u)`:
* `HT T`: the truncation `Σ_{t<T} W^{t+1} [(i+j)(t+1)^{i+j−1} φ(t+1) + (t+1)^{i+j} φ′(t+1)]` of `Λ(u^{i+j})`;
* `abs_det_LamMat_le_of`: a uniform bound on `|det HT T|` bounds `|Δ_h(χ₂(1/q))|`;
* `HT_rankOne`: `HT T` is `Σ_{k} c_k x_k y_kᵀ` over slot triples `k = (t, τ)`, `τ ∈ {(val,val), (der,val), (val,der)}`;
* `abs_phi_deriv_le`: `|φ′(s)| ≤ h φ(s)` for `s ≥ 1`;
* `abs_det_HT_le`: `|det HT T| ≤ (h!)⁻¹ K² Σ_f [x-slots of f distinct] ∏_i b(s_i) ∏_{i<j} pf(s_i, s_j)²`,
  `b(s) = W^s h φ(s)`, `K = h^h (1 + 2/h)^{h²}`.
-/
import Chi2Irrational.PoleExpansion
import Chi2Irrational.Analytic.Andreief
import Chi2Irrational.Analytic.SlotDet

namespace Chi2Irr

open Polynomial Finset Filter Topology Matrix

/-- `D(u) = ∏_{k<h} (u + k + ½)` as a real function. -/
noncomputable def Dr (h : ℕ) (u : ℝ) : ℝ := aeval u (Dpoly h)

/-- `φ(u) = u/D(u)`. -/
noncomputable def phiR (h : ℕ) (u : ℝ) : ℝ := u / Dr h u

lemma Dr_pos (h : ℕ) {u : ℝ} (hu : 0 < u) : 0 < Dr h u := aeval_Dpoly_pos h hu

lemma Dr_eq_prod (h : ℕ) (u : ℝ) : Dr h u = ∏ k ∈ range h, (u - poleR k) := by
  unfold Dr
  rw [aeval_def, eval₂_eq_eval_map, map_Dpoly, Lagrange.eval_nodal]

lemma phiR_pos (h : ℕ) {u : ℝ} (hu : 0 < u) : 0 < phiR h u := div_pos hu (Dr_pos h hu)

/-- The derivative of `D`: `D′(u) = Σ_k ∏_{l≠k} (u − x_l)`. -/
lemma hasDerivAt_Dr (h : ℕ) (u : ℝ) :
    HasDerivAt (Dr h) (∑ k ∈ range h, ∏ l ∈ (range h).erase k, (u - poleR l)) u := by
  have := Polynomial.hasDerivAt_aeval (q := Dpoly h) u
  unfold Dr
  convert this using 1
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, map_Dpoly]
  unfold Lagrange.nodal
  rw [derivative_prod_finset, eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [eval_prod]

lemma sum_erase_prod_eq (h : ℕ) {u : ℝ} (hu : 0 < u) :
    ∑ k ∈ range h, ∏ l ∈ (range h).erase k, (u - poleR l) =
      Dr h u * ∑ k ∈ range h, 1 / (u - poleR k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hne : u - poleR k ≠ 0 := by have := poleR_neg k; intro e; linarith
  rw [Dr_eq_prod, ← Finset.mul_prod_erase _ _ hk]
  field_simp

lemma hasDerivAt_phiR (h : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (phiR h) (phiR h u * (1 / u - ∑ k ∈ range h, 1 / (u - poleR k))) u := by
  have hD := Dr_pos h hu
  have h1 := (hasDerivAt_id u).div (hasDerivAt_Dr h u) hD.ne'
  have h2 : HasDerivAt (phiR h) ((1 * Dr h u - id u * ∑ k ∈ range h,
      ∏ l ∈ (range h).erase k, (u - poleR l)) / Dr h u ^ 2) u := h1
  convert h2 using 1
  rw [sum_erase_prod_eq h hu]
  unfold phiR
  simp only [id]
  field_simp

lemma phiR_deriv_eq (h : ℕ) {u : ℝ} (hu : 0 < u) :
    deriv (phiR h) u = phiR h u * (1 / u - ∑ k ∈ range h, 1 / (u - poleR k)) :=
  (hasDerivAt_phiR h hu).deriv

/-- `|φ′(s)| ≤ h φ(s)` for `s ≥ 1`, `h ≥ 1`. -/
lemma abs_phi_deriv_le {h : ℕ} (hh : 1 ≤ h) {s : ℝ} (hs : 1 ≤ s) :
    |deriv (phiR h) s| ≤ h * phiR h s := by
  have hs0 : 0 < s := by linarith
  rw [phiR_deriv_eq h hs0, abs_mul, abs_of_pos (phiR_pos h hs0), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (phiR_pos h hs0).le
  have hA : 0 ≤ 1 / s := by positivity
  have hA1 : 1 / s ≤ 1 := by rw [div_le_one hs0]; exact hs
  have hterm : ∀ k ∈ range h, 0 ≤ 1 / (s - poleR k) ∧ 1 / (s - poleR k) ≤ 1 := by
    intro k _
    have hk := poleR_neg k
    have hk' : poleR k ≤ -(1 / 2) := by
      unfold poleR pole; push_cast
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      linarith
    constructor
    · have : 0 < s - poleR k := by linarith
      positivity
    · rw [div_le_one (by linarith)]; linarith
  have hB : 0 ≤ ∑ k ∈ range h, 1 / (s - poleR k) := Finset.sum_nonneg (fun k hk => (hterm k hk).1)
  have hB1 : ∑ k ∈ range h, 1 / (s - poleR k) ≤ h := by
    calc ∑ k ∈ range h, 1 / (s - poleR k) ≤ ∑ _k ∈ range h, (1 : ℝ) :=
          Finset.sum_le_sum (fun k hk => (hterm k hk).2)
      _ = h := by simp
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rw [abs_le]
  constructor <;> linarith

/-- The derivative of `u ↦ u^n φ(u)`. -/
lemma deriv_pow_phi (h n : ℕ) {s : ℝ} (hs : 0 < s) :
    deriv (fun u : ℝ => aeval u ((X : ℚ[X]) ^ n) * u / aeval u (Dpoly h)) s =
      (n : ℝ) * s ^ (n - 1) * phiR h s + s ^ n * deriv (phiR h) s := by
  have heq : (fun u : ℝ => aeval u ((X : ℚ[X]) ^ n) * u / aeval u (Dpoly h)) =
      fun u => u ^ n * phiR h u := by
    ext u; simp only [map_pow, aeval_X, phiR, Dr]; ring
  rw [heq]
  have h1 : HasDerivAt (fun u : ℝ => u ^ n) ((n : ℝ) * s ^ (n - 1)) s := hasDerivAt_pow n s
  exact (h1.mul (hasDerivAt_phiR h hs)).deriv.trans (by rw [(hasDerivAt_phiR h hs).deriv])

/-! ### The truncations -/

/-- The weight `W = q⁻²` as a real. -/
noncomputable def Wr (q : ℕ) : ℝ := ((wt q : ℚ) : ℝ)

/-- The node term of `Λ(u^n)` at `s = t + 1`. -/
noncomputable def nodeTerm (q h n t : ℕ) : ℝ :=
  Wr q ^ (t + 1) * ((n : ℝ) * ((t : ℝ) + 1) ^ (n - 1) * phiR h ((t : ℝ) + 1) +
    ((t : ℝ) + 1) ^ n * deriv (phiR h) ((t : ℝ) + 1))

/-- The truncated matrix. -/
noncomputable def HT (q h T : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∑ t ∈ range T, nodeTerm q h ((i : ℕ) + j) t

lemma LamMat_hasSum {q : ℕ} (hq : 2 ≤ q) (h : ℕ) (i j : Fin h) :
    HasSum (fun t => nodeTerm q h ((i : ℕ) + j) t) (LamMat q h i j) := by
  have hs := summable_Lam_summand hq h ((X : ℚ[X]) ^ ((i : ℕ) + j))
  have hterm : ∀ t : ℕ, ((wt q : ℚ) : ℝ) ^ (t + 1) * deriv (fun u : ℝ =>
      aeval u ((X : ℚ[X]) ^ ((i : ℕ) + j)) * u / aeval u (Dpoly h)) ((t : ℝ) + 1) =
      nodeTerm q h ((i : ℕ) + j) t := by
    intro t
    rw [deriv_pow_phi h _ (by positivity)]
    unfold nodeTerm Wr; ring
  have hs' := hs.congr hterm
  have hval : LamMat q h i j = ∑' t, nodeTerm q h ((i : ℕ) + j) t := by
    unfold LamMat Lam
    exact tsum_congr hterm
  rw [hval]
  exact hs'.hasSum

lemma tendsto_det_HT {q : ℕ} (hq : 2 ≤ q) (h : ℕ) :
    Tendsto (fun T => (HT q h T).det) atTop (𝓝 (LamMat q h).det) := by
  have hmat : Tendsto (fun T => HT q h T) atTop (𝓝 (LamMat q h)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => (LamMat_hasSum hq h i j).tendsto_sum_nat
  exact ((continuous_id.matrix_det).tendsto _).comp hmat

/-- A uniform bound on the truncations bounds `|Δ_h(χ₂(1/q))|`. -/
theorem abs_Delta_le_of {q : ℕ} (hq : 2 ≤ q) (h : ℕ) {B : ℝ} (hB : ∀ T, |(HT q h T).det| ≤ B) :
    |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ B := by
  rw [aeval_chi2_Delta hq h]
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_det_HT hq h)) hB

/-! ### Rank-one form -/

/-- The node of a triple `(t, τ)`. -/
def tnode {T : ℕ} (k : Fin T × Fin 3) : ℕ := (k.1 : ℕ) + 1

/-- The x-slot of a triple: derivative iff `τ = 1`. -/
def xslot {T : ℕ} (k : Fin T × Fin 3) : ℕ × Bool := (tnode k, decide ((k.2 : ℕ) = 1))

/-- The y-slot of a triple: derivative iff `τ = 2`. -/
def yslot {T : ℕ} (k : Fin T × Fin 3) : ℕ × Bool := (tnode k, decide ((k.2 : ℕ) = 2))

/-- The coefficient of a triple. -/
noncomputable def cN (q h : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  Wr q ^ tnode k * (if (k.2 : ℕ) = 0 then deriv (phiR h) (tnode k) else phiR h (tnode k))

lemma pow_deriv_split (s : ℝ) (i j : ℕ) :
    ((i : ℝ) + j) * s ^ (i + j - 1) =
      ((i : ℝ) * s ^ (i - 1)) * s ^ j + s ^ i * ((j : ℝ) * s ^ (j - 1)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have e1 : s ^ (i + j - 1) = s ^ (i - 1) * s ^ j := by rw [← pow_add]; congr 1; omega
  have e2 : s ^ (i + j - 1) = s ^ i * s ^ (j - 1) := by rw [← pow_add]; congr 1; omega
  rw [add_mul, show (i : ℝ) * s ^ (i + j - 1) = i * (s ^ (i - 1) * s ^ j) by rw [e1],
    show (j : ℝ) * s ^ (i + j - 1) = j * (s ^ i * s ^ (j - 1)) by rw [e2]]
  ring

lemma HT_rankOne (q h T : ℕ) :
    HT q h T = Matrix.of fun i j => ∑ k : Fin T × Fin 3,
      cN q h k * slotRow h (xslot k) i * slotRow h (yslot k) j := by
  ext i j
  simp only [HT, Matrix.of_apply]
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun t => nodeTerm q h ((i : ℕ) + j) t) T]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.sum_univ_three]
  simp only [cN, xslot, yslot, tnode, slotRow, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp only [show (0 : ℕ) ≠ 1 by norm_num, show (0 : ℕ) ≠ 2 by norm_num, show (1 : ℕ) ≠ 2 by norm_num,
    show (1 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
    decide_false, decide_true, ite_true, ite_false, Bool.false_eq_true]
  unfold nodeTerm
  push_cast
  rw [pow_deriv_split]
  ring

/-! ### The bound on the truncated determinant -/

/-- The slot-minor constant `h^h (1 + 2/h)^{h²}`. -/
noncomputable def Kslot (h : ℕ) : ℝ := (h : ℝ) ^ h * (1 + 2 / (h : ℝ)) ^ (h ^ 2)

/-- The node weight `b(s) = W^s h φ(s)`. -/
noncomputable def bN (q h s : ℕ) : ℝ := Wr q ^ s * h * phiR h s

lemma Wr_pos (q : ℕ) (hq : 2 ≤ q) : 0 < Wr q := by
  unfold Wr wt; push_cast
  have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  positivity

lemma abs_cN_le {q h T : ℕ} (hq : 2 ≤ q) (hh : 1 ≤ h) (k : Fin T × Fin 3) :
    |cN q h k| ≤ bN q h (tnode k) := by
  have hs : (1 : ℝ) ≤ (tnode k : ℝ) := by unfold tnode; push_cast; linarith [(k.1 : ℕ).cast_nonneg (α := ℝ)]
  have hW := Wr_pos q hq
  have hphi := phiR_pos h (show (0 : ℝ) < tnode k by linarith)
  unfold cN bN
  rw [abs_mul, abs_of_pos (pow_pos hW _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hW _).le
  split_ifs
  · exact abs_phi_deriv_le hh hs
  · rw [abs_of_pos hphi]
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith

lemma bN_pos {q h : ℕ} (hq : 2 ≤ q) {s : ℕ} (hs : 1 ≤ s) (hh : 1 ≤ h) : 0 < bN q h s := by
  unfold bN
  have : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have := phiR_pos h (show (0 : ℝ) < s by assumption)
  have := Wr_pos q hq
  positivity

/-- **The truncated determinant, slot form.** -/
theorem abs_det_HT_le {q h T : ℕ} (hq : 2 ≤ q) (hh : 2 ≤ h) :
    |(HT q h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      ∑ f : Fin h → Fin T × Fin 3, (if Function.Injective (fun i => xslot (f i)) then
        (∏ i, bN q h (tnode (f i))) *
          ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 else 0) := by
  have hfac : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have hA := factorial_smul_det_sum_rankOne (R := ℝ) (cN q h (T := T)) (fun k => slotRow h (xslot k))
    (fun k => slotRow h (yslot k))
  rw [← HT_rankOne, Fintype.card_fin, nsmul_eq_mul] at hA
  have hdet : (HT q h T).det = ((h.factorial : ℝ))⁻¹ * ∑ f : Fin h → Fin T × Fin 3,
      (∏ i, cN q h (f i)) * (Matrix.of fun i j => slotRow h (xslot (f i)) j).det *
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
    have hc : ∏ i, |cN q h (f i)| ≤ ∏ i, bN q h (tnode (f i)) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => abs_cN_le hq (by omega) (f i))
    have hP : 0 ≤ ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) :=
      Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => pairFactor_nonneg _ _))
    have hK : 0 ≤ Kslot h := by unfold Kslot; positivity
    have hb : 0 ≤ ∏ i, bN q h (tnode (f i)) :=
      Finset.prod_nonneg (fun i _ => (bN_pos hq (by unfold tnode; omega) (by omega)).le)
    calc (∏ i, |cN q h (f i)|) * |(Matrix.of fun i j => slotRow h (xslot (f i)) j).det| *
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

end Chi2Irr
