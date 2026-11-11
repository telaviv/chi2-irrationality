/-
# Lemma 10₁ (RESULT §3): the 2-adic bound on the coefficients of `Δ^Ti_h` at odd `q`

Copy of `Arith/TwoAdic.lean` (Gram identity, Leibniz bound) and `Q/TwoAdic.lean` (limit argument) for the Ti machine.
The machine-free pieces (`PN`, `det_PN`, `PN_entry`, `expand_fin`, `det_CoefM_monic`, `det_map_C`, `monic_prod_pole`,
`rPot`, `cPot`, `betaP`, `betaP_le`, `eventually_rem_le`) are reused by import.
* `LamLinT`, `LamPT`, `Gram2_eqT`, `DeltaT_eq_anchored`: `Δ^Ti_h = det (Λ_X(a_i b_j))` in the anchored basis;
* `twoAdic_DeltaT`: `‖[X^k] Δ^Ti_h‖₂ ≤ 2^{βp(h) + h (⌊log₂ h⌋ + 2)}` at odd `q ≥ 3`, from the entry bound
  `v₂ ≥ −(i+j+1−h)₊ − ⌊log₂ h⌋ − 2` (`V2_entryT`) with `ρ_i = 2^{rPot i + ⌊log₂ h⌋ + 2}`, `κ_j = 2^{cPot j}`;
* `twoAdic_odd_t_proof`: the ingredient `twoAdic_odd_t` of `TiQ/Interface.lean`, from `4 βp(h) ≤ h² + 2h`.
Departure from RESULT §3: `n₂ ≤ βp(h) + h(⌊log₂ h⌋ + 2) = h²/4 + O(h log h)` in place of `⌊h²/4⌋` (same constant
`¼ log 2`; the logarithmic loss comes from the weaker (L) entry bound of `TiQ/TwoAdicEntries.lean`).
-/
import Chi2Irrational.TiQ.TwoAdicEntries
import Chi2Irrational.Arith.TwoAdic
import Chi2Irrational.Arith.Assembly

namespace Chi2Irr
namespace TiQ

open Polynomial Finset Filter

/-! ### Linearity of `Λ_X` and the Gram identity for two families -/

/-- `Λ_r = A + r·B` (Ti machine) as a linear map. -/
noncomputable def LamLinT (q K : ℕ) (r : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (muLin (wT q)).comp ((divByMonicHom (Dpoly K)).comp (LinearMap.mulRight ℚ X)) +
    ∑ k ∈ range K, (4 * omega K k * SpartT q k - 4 * r * omega K k * poleW q k) •
      Polynomial.leval (pole k)

lemma LamLinT_apply (q K : ℕ) (r : ℚ) (g : ℚ[X]) : LamLinT q K r g = AfunT q K g + r * BfunT q K g := by
  unfold LamLinT AfunT BfunT
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, divByMonicHom_apply, muLin_apply]
  simp only [LinearMap.smul_apply, Polynomial.leval_apply, smul_eq_mul]
  rw [add_assoc]
  congr 1
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  ring

lemma AfunT_add' (q K : ℕ) (f g : ℚ[X]) : AfunT q K (f + g) = AfunT q K f + AfunT q K g := by
  have := (LamLinT q K 0).map_add f g
  simpa only [LamLinT_apply, zero_mul, add_zero] using this

lemma AfunT_smul' (q K : ℕ) (c : ℚ) (f : ℚ[X]) : AfunT q K (c • f) = c * AfunT q K f := by
  have := (LamLinT q K 0).map_smul c f
  simpa only [LamLinT_apply, zero_mul, add_zero, smul_eq_mul] using this

lemma BfunT_eq_LamLinT (q K : ℕ) (g : ℚ[X]) : BfunT q K g = LamLinT q K 1 g - LamLinT q K 0 g := by
  simp only [LamLinT_apply]; ring

lemma BfunT_add' (q K : ℕ) (f g : ℚ[X]) : BfunT q K (f + g) = BfunT q K f + BfunT q K g := by
  simp only [BfunT_eq_LamLinT, map_add]; ring

lemma BfunT_smul' (q K : ℕ) (c : ℚ) (f : ℚ[X]) : BfunT q K (c • f) = c * BfunT q K f := by
  simp only [BfunT_eq_LamLinT, map_smul, smul_eq_mul]; ring

/-- `Λ_X(g) = A(g) + X B(g)` (Ti machine) as a `ℚ`-linear map `ℚ[X] → ℚ[X]`. -/
noncomputable def LamPT (q K : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun g := C (AfunT q K g) + X * C (BfunT q K g)
  map_add' f g := by simp only [AfunT_add', BfunT_add', map_add]; ring
  map_smul' c f := by
    rw [AfunT_smul', BfunT_smul', RingHom.id_apply, smul_eq_C_mul, map_mul, map_mul]; ring

lemma LamPT_apply (q K : ℕ) (g : ℚ[X]) : LamPT q K g = C (AfunT q K g) + X * C (BfunT q K g) := rfl

/-- The monomial matrix `H_{de} = Λ_X(X^{d+e})`. -/
noncomputable def HPmT (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] := fun d e => LamPT q h (X ^ ((d : ℕ) + e))

lemma HPmT_eq (q h : ℕ) : HPmT q h = (X : ℚ[X]) • (BmatT q h).map C + (AmatT q h).map C := by
  ext d e
  simp only [HPmT, LamPT_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, AmatT,
    BmatT]
  ring_nf

theorem Gram2_eqT (q : ℕ) {h : ℕ} (a b : Fin h → ℚ[X]) (ha : ∀ i, (a i).natDegree < h)
    (hb : ∀ i, (b i).natDegree < h) :
    Matrix.of (fun i j => LamPT q h (a i * b j)) =
      (CoefM a).map C * HPmT q h * ((CoefM b).map C).transpose := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [expand_fin a ha i, expand_fin b hb j, sum_mul_sum]
  simp only [map_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  have : C (CoefM a i d) * X ^ (d : ℕ) * (C (CoefM b j e) * X ^ (e : ℕ)) =
      (CoefM a i d * CoefM b j e) • X ^ ((d : ℕ) + e) := by
    rw [smul_eq_C_mul, C_mul, pow_add]; ring
  rw [this, map_smul, smul_eq_C_mul, C_mul]
  simp only [HPmT]
  ring

/-- `Δ^Ti_h` is the determinant of the anchored Gram matrix. -/
theorem DeltaT_eq_anchored (q h : ℕ) :
    DeltaT q h = (Matrix.of (fun i j : Fin h => LamPT q h (aB i * bB h j))).det := by
  have hda : ∀ i : Fin h, (aB i).natDegree = i := fun i => by
    unfold aB; rw [natDegree_prod_pole, card_range]
  have hdb : ∀ j : Fin h, (bB h j).natDegree = j := fun j => by
    unfold bB; rw [natDegree_prod_pole, Nat.card_Ico]; have := j.isLt; omega
  rw [Gram2_eqT q (fun i => aB i) (fun j => bB h j) (fun i => by rw [hda]; exact i.isLt)
    (fun j => by rw [hdb]; exact j.isLt), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_map_C, det_map_C, det_CoefM_monic _ hda (fun i => monic_prod_pole _),
    det_CoefM_monic _ hdb (fun j => monic_prod_pole _), map_one, one_mul, mul_one, HPmT_eq]
  rfl

/-! ### The bound -/

/-- **Lemma 10₁.** Every coefficient of `Δ^Ti_h` has `‖·‖₂ ≤ 2^{βp(h) + h (⌊log₂ h⌋ + 2)}` at odd `q ≥ 3`. -/
theorem twoAdic_DeltaT {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (h k : ℕ) :
    padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (betaP h + h * (Nat.log 2 h + 2)) := by
  set L := Nat.log 2 h with hL
  set ρ : Fin h → ℚ := fun i => (2 : ℚ) ^ (rPot h i + L + 2) with hρ
  set κ : Fin h → ℚ := fun j => (2 : ℚ) ^ (cPot h j) with hκ
  have hentry : ∀ i j : Fin h, PN (ρ i * κ j) (LamPT q h (aB i * bB h j)) := by
    intro i j
    have hv := V2_entryT hq ho i.isLt j.isLt
    have hle : (2 : ℚ) ^ (-eTA1 h i j) ≤ ρ i * κ j := by
      have e : ρ i * κ j = (2 : ℚ) ^ (((rPot h i + L + 2 + cPot h j : ℕ) : ℤ)) := by
        rw [zpow_natCast, pow_add]
      rw [e]
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      have hπ : i + j + 1 - h ≤ rPot h i + cPot h j := by unfold rPot cPot; omega
      unfold eTA1
      push_cast
      omega
    rw [LamPT_apply]
    exact PN_entry (hv.1.trans hle) (hv.2.trans hle) (by positivity)
  have hdet : PN ((∏ i, ρ i) * ∏ i, κ i) (Matrix.of (fun i j : Fin h => LamPT q h (aB i * bB h j))).det :=
    det_PN _ ρ κ (fun i => by positivity) (fun j => by positivity) hentry
  rw [DeltaT_eq_anchored]
  refine (hdet k).trans (le_of_eq ?_)
  simp only [hρ, hκ]
  rw [prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, ← pow_add,
    Fin.sum_univ_eq_sum_range (fun i => rPot h i + L + 2) h, Fin.sum_univ_eq_sum_range (fun j => cPot h j) h]
  congr 1
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul]
  unfold betaP
  ring

/-- The size of the 2-adic exponent: `(βp(h) + h (⌊log₂ h⌋ + 2)) log 2 ≤ (¼ log 2 + ε) h²` eventually. -/
theorem eventually_n2_le_t : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    (((betaP h + h * (Nat.log 2 h + 2) : ℕ) : ℤ) : ℝ) * Real.log 2 ≤ (c2TiOdd + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [eventually_rem_le ε hε, eventually_ge_atTop 1] with h hrem hh
  set H : ℝ := (h : ℝ) with hH
  have hH1 : 1 ≤ H := by rw [hH]; exact_mod_cast hh
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hβ : 4 * (betaP h : ℝ) ≤ H ^ 2 + 2 * H := by
    have := betaP_le h; rw [hH]; exact_mod_cast this
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log H := by
    have hp := Nat.pow_log_le_self 2 (by omega : h ≠ 0)
    have : ((2 : ℝ) ^ Nat.log 2 h) ≤ H := by rw [hH]; exact_mod_cast hp
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) this
  have e1 : (betaP h : ℝ) * Real.log 2 ≤ (H ^ 2 + 2 * H) / 4 * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hl2.le
  have e2 : H * ((Nat.log 2 h : ℝ) * Real.log 2) ≤ H * Real.log H :=
    mul_le_mul_of_nonneg_left hL (by linarith)
  have e3 : H * Real.log 2 ≤ H := mul_le_of_le_one_right (by linarith) hl2'
  have e4 : 0 ≤ H * Real.log H := mul_nonneg (by linarith) hlH
  unfold c2TiOdd
  push_cast
  rw [← hH]
  nlinarith

/-- **Lemma 10₁** (the ingredient `twoAdic_odd_t` of `TiQ/Interface.lean`). -/
theorem twoAdic_odd_t_proof (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2TiOdd + ε) * (h : ℝ) ^ 2 :=
  ⟨fun h => ((betaP h + h * (Nat.log 2 h + 2) : ℕ) : ℤ),
    fun h k => by rw [zpow_natCast]; exact twoAdic_DeltaT hq ho h k, eventually_n2_le_t⟩

end TiQ
end Chi2Irr
