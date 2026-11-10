/-
# Lemma 10_e, step 3: the 2-adic size of a Vandermonde determinant with derivative rows

For points `z : Fin h → ℚ` and a set `U` of rows, let `R(z, U)` have rows `(z_i^j)_j` for `i ∉ U` and
`(j z_i^{j−1})_j` for `i ∈ U` (value rows and derivative rows; repeated points allowed, as for the confluent
nodes of `pilot_qeven/RESULT.md` §2, step 2). If `2^{−Λ} ≤ |z_i − z_j|₂` whenever `i ∈ U` and `z_j ≠ z_i`, then

  `|det R(z, U)|₂ ≤ ∏_{i<j, z_i ≠ z_j} |z_j − z_i|₂ · 2^{Λ·|U|}`     (`padicNorm_detR_le`).

Proof (RESULT §2 step 3, "each derivative lowers one difference factor containing its own variable"):
`det R(z, U) = eval_z (∂_U V)` with `V = ∏_{i<j}(X_j − X_i)` in `ℚ[X_0, …, X_{h−1}]`, because only row `a` involves
`X_a` (`det_Wm_insert`); by induction on `U`, `∂_U V` is a `ℤ`-combination of the products `∏_{p ∉ C} ℓ_p` over sets
`C` of pairs that are images of an injective choice `c : U → pairs` with `i ∈ c(i)` (`det_Wm_mem_span`); each such
product is bounded by evaluation (`padicNorm_eval_gen_le`), and the bound passes to the span by the ultrametric
inequality.
-/
import Mathlib

namespace Chi2Irr
namespace Q
namespace CoreDet

open MvPolynomial Finset

/-- Leibniz for finite products. -/
lemma deriv_prod {R : Type*} [CommRing R] [Algebra ℚ R] (D : Derivation ℚ R R) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, erase_insert ha, smul_eq_mul, smul_eq_mul,
      mul_sum, add_comm]
    congr 1
    refine sum_congr rfl (fun i hi => ?_)
    have hai : a ≠ i := fun e => ha (e ▸ hi)
    rw [erase_insert_of_ne hai, prod_insert (fun h' => ha (mem_of_mem_erase h'))]
    ring

lemma deriv_prod_eq_zero {R : Type*} [CommRing R] [Algebra ℚ R] (D : Derivation ℚ R R) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  rw [deriv_prod]
  exact sum_eq_zero (fun i hi => by rw [hf i hi, mul_zero])

variable {h : ℕ}

/-- The polynomial matrix: value rows `X_i^j`, derivative rows `j X_i^{j−1}` for `i ∈ U`. -/
noncomputable def Wm (U : Finset (Fin h)) : Matrix (Fin h) (Fin h) (MvPolynomial (Fin h) ℚ) :=
  Matrix.of fun i j => if i ∈ U then C ((j : ℕ) : ℚ) * X i ^ ((j : ℕ) - 1) else X i ^ (j : ℕ)

lemma pderiv_X_pow_self (i : Fin h) (n : ℕ) :
    pderiv i (X i ^ n : MvPolynomial (Fin h) ℚ) = C (n : ℚ) * X i ^ (n - 1) := by
  rw [Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, mul_one, nsmul_eq_mul, map_natCast]

lemma pderiv_X_pow_ne {a i : Fin h} (hai : i ≠ a) (n : ℕ) :
    pderiv a (X i ^ n : MvPolynomial (Fin h) ℚ) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_X_of_ne hai, smul_zero, smul_zero]

lemma pderiv_Wm_ne (U : Finset (Fin h)) {a i : Fin h} (hai : i ≠ a) (j : Fin h) : pderiv a (Wm U i j) = 0 := by
  unfold Wm
  rw [Matrix.of_apply]
  split_ifs
  · rw [Derivation.leibniz, pderiv_X_pow_ne hai, pderiv_C, smul_zero, smul_zero, add_zero]
  · exact pderiv_X_pow_ne hai _

/-- Differentiating the determinant in `X_a` turns row `a` into a derivative row. -/
lemma det_Wm_insert {U : Finset (Fin h)} {a : Fin h} (ha : a ∉ U) :
    (Wm (insert a U)).det = pderiv a (Wm U).det := by
  rw [Matrix.det_apply, Matrix.det_apply, map_sum]
  refine sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def, Units.smul_def, map_zsmul]
  congr 1
  set i₀ := σ.symm a with hi₀
  have hσ : σ i₀ = a := by rw [hi₀, Equiv.apply_symm_apply]
  rw [← mul_prod_erase univ _ (mem_univ i₀), ← mul_prod_erase univ _ (mem_univ i₀), Derivation.leibniz,
    deriv_prod_eq_zero _ _ _ (fun i hi => pderiv_Wm_ne U (fun e => (ne_of_mem_erase hi)
      (σ.injective (e.trans hσ.symm))) i), smul_zero, zero_add, smul_eq_mul, mul_comm]
  congr 1
  · refine prod_congr rfl (fun i hi => ?_)
    have hne : σ i ≠ a := fun e => (ne_of_mem_erase hi) (σ.injective (e.trans hσ.symm))
    unfold Wm
    simp only [Matrix.of_apply, mem_insert, hne, false_or]
  · rw [hσ]
    unfold Wm
    simp only [Matrix.of_apply, mem_insert_self, ite_true, ha, ite_false]
    exact (pderiv_X_pow_self a _).symm

/-! ### Pairs and generators -/

/-- The pairs `i < j`. -/
def Spr (h : ℕ) : Finset (Fin h × Fin h) := univ.filter (fun p => p.1 < p.2)

/-- The linear factor `X_j − X_i` of the pair `(i, j)`. -/
noncomputable def ell (p : Fin h × Fin h) : MvPolynomial (Fin h) ℚ := X p.2 - X p.1

/-- The product over the pairs outside `C`. -/
noncomputable def Fpr (C : Finset (Fin h × Fin h)) : MvPolynomial (Fin h) ℚ := ∏ p ∈ Spr h \ C, ell p

/-- `C` is the image of an injective choice of a pair containing `i`, for `i ∈ U`. -/
def Good (U : Finset (Fin h)) (C : Finset (Fin h × Fin h)) : Prop :=
  ∃ c : Fin h → Fin h × Fin h, (∀ i ∈ U, c i ∈ Spr h ∧ ((c i).1 = i ∨ (c i).2 = i)) ∧ Set.InjOn c U ∧
    C = U.image c

def Gens (U : Finset (Fin h)) : Set (MvPolynomial (Fin h) ℚ) := {F | ∃ C, Good U C ∧ F = Fpr C}

lemma det_Wm_empty : (Wm (∅ : Finset (Fin h))).det = Fpr ∅ := by
  have hW : Wm (∅ : Finset (Fin h)) = Matrix.vandermonde (fun i => X i) := by
    ext i j; simp [Wm, Matrix.vandermonde]
  rw [hW, Matrix.det_vandermonde]
  unfold Fpr Spr ell
  rw [sdiff_empty, prod_filter, Fintype.prod_prod_type]
  refine prod_congr rfl (fun i _ => ?_)
  rw [← prod_filter]
  congr 1
  ext j; simp

lemma pderiv_ell (a : Fin h) (p : Fin h × Fin h) :
    pderiv a (ell p) = (if p.2 = a then 1 else 0) - (if p.1 = a then 1 else 0) := by
  unfold ell
  rw [map_sub, pderiv_X, pderiv_X]
  simp only [Pi.single_apply]

lemma gen_step {U : Finset (Fin h)} {a : Fin h} (ha : a ∉ U) {C : Finset (Fin h × Fin h)} (hC : Good U C) :
    pderiv a (Fpr C) ∈ Submodule.span ℤ (Gens (insert a U)) := by
  obtain ⟨c, hc1, hc2, rfl⟩ := hC
  unfold Fpr
  rw [deriv_prod]
  refine Submodule.sum_mem _ (fun p hp => ?_)
  obtain ⟨hpS, hpC⟩ := mem_sdiff.mp hp
  have hlt : p.1 < p.2 := (mem_filter.mp hpS).2
  have hset : (Spr h \ U.image c).erase p = Spr h \ insert p (U.image c) := by
    ext x; simp only [mem_erase, mem_sdiff, mem_insert]; tauto
  rw [hset, pderiv_ell]
  by_cases hpa : p.2 = a ∨ p.1 = a
  · have hgood : Good (insert a U) (insert p (U.image c)) := by
      refine ⟨Function.update c a p, fun i hi => ?_, ?_, ?_⟩
      · rcases mem_insert.mp hi with rfl | hi'
        · rw [Function.update_self]; exact ⟨hpS, hpa.symm⟩
        · rw [Function.update_of_ne (by rintro rfl; exact ha hi')]; exact hc1 i hi'
      · intro i hi j hj hij
        have hi2 := mem_insert.mp (Finset.mem_coe.mp hi)
        have hj2 := mem_insert.mp (Finset.mem_coe.mp hj)
        rcases hi2 with rfl | hi' <;> rcases hj2 with rfl | hj'
        · rfl
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hj')] at hij
          have := mem_image_of_mem c hj'
          rw [← hij] at this
          exact absurd this hpC
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hi')] at hij
          have := mem_image_of_mem c hi'
          rw [hij] at this
          exact absurd this hpC
        · rw [Function.update_of_ne (by rintro rfl; exact ha hi'),
            Function.update_of_ne (by rintro rfl; exact ha hj')] at hij
          exact hc2 hi' hj' hij
      · rw [image_insert, Function.update_self]
        congr 1
        exact image_congr (fun i hi => (Function.update_of_ne (by rintro rfl; exact ha hi) _ _).symm)
    have hmem : Fpr (insert p (U.image c)) ∈ Gens (insert a U) := ⟨_, hgood, rfl⟩
    have hsp := Submodule.subset_span (R := ℤ) hmem
    unfold Fpr at hsp
    rcases hpa with h2 | h1
    · have h1 : p.1 ≠ a := fun e => by rw [e, ← h2] at hlt; exact lt_irrefl _ hlt
      simp only [h2, h1, ite_true, ite_false, sub_zero, mul_one]
      exact hsp
    · have h2 : p.2 ≠ a := fun e => by rw [e, ← h1] at hlt; exact lt_irrefl _ hlt
      simp only [h2, h1, ite_true, ite_false, zero_sub, mul_neg, mul_one]
      exact Submodule.neg_mem _ hsp
  · push Not at hpa
    simp only [hpa.1, hpa.2, ite_false, sub_zero, mul_zero]
    exact Submodule.zero_mem _

lemma pderiv_span {U : Finset (Fin h)} {a : Fin h} (ha : a ∉ U) {x : MvPolynomial (Fin h) ℚ}
    (hx : x ∈ Submodule.span ℤ (Gens U)) : pderiv a x ∈ Submodule.span ℤ (Gens (insert a U)) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨C, hC, rfl⟩ := hy; exact gen_step ha hC
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y w _ _ hy hw => rw [map_add]; exact Submodule.add_mem _ hy hw
  | smul n y _ hy => rw [map_zsmul]; exact Submodule.smul_mem _ n hy

lemma det_Wm_mem_span (U : Finset (Fin h)) : (Wm U).det ∈ Submodule.span ℤ (Gens U) := by
  induction U using Finset.induction_on with
  | empty =>
    rw [det_Wm_empty]
    exact Submodule.subset_span ⟨∅, ⟨fun i => (i, i), fun i hi => absurd hi (Finset.notMem_empty i),
      fun i hi => absurd hi (Finset.notMem_empty i), by rw [image_empty]⟩, rfl⟩
  | insert a U ha ih => rw [det_Wm_insert ha]; exact pderiv_span ha ih

/-! ### Evaluation -/

variable (z : Fin h → ℚ)

/-- The factor of the pair `p`: `|z_j − z_i|₂` if `z_i ≠ z_j`, else `1`. -/
noncomputable def gz (p : Fin h × Fin h) : ℚ := if z p.1 ≠ z p.2 then padicNorm 2 (z p.2 - z p.1) else 1

lemma gz_nonneg (p : Fin h × Fin h) : 0 ≤ gz z p := by
  unfold gz; split_ifs
  · exact padicNorm.nonneg _
  · exact zero_le_one

lemma padicNorm_prod_fin {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm 2 (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm 2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

variable {z}

lemma padicNorm_eval_gen_le {U : Finset (Fin h)} {Λ : ℕ}
    (hz : ∀ i ∈ U, ∀ j, z j ≠ z i → (2 : ℚ) ^ (-(Λ : ℤ)) ≤ padicNorm 2 (z i - z j))
    {C : Finset (Fin h × Fin h)} (hC : Good U C) :
    padicNorm 2 (eval z (Fpr C)) ≤ (∏ p ∈ Spr h, gz z p) * 2 ^ (Λ * U.card) := by
  have hR : 0 ≤ (∏ p ∈ Spr h, gz z p) * 2 ^ (Λ * U.card) :=
    mul_nonneg (prod_nonneg (fun p _ => gz_nonneg z p)) (by positivity)
  have he : eval z (Fpr C) = ∏ p ∈ Spr h \ C, (z p.2 - z p.1) := by
    unfold Fpr ell; rw [map_prod]; simp only [map_sub, eval_X]
  rw [he]
  by_cases hz0 : ∃ p ∈ Spr h \ C, z p.1 = z p.2
  · obtain ⟨p, hp, hpz⟩ := hz0
    rw [prod_eq_zero hp (by rw [hpz, sub_self]), padicNorm.zero]
    exact hR
  push Not at hz0
  obtain ⟨c, hc1, hc2, rfl⟩ := hC
  have hsub : U.image c ⊆ Spr h := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx; exact (hc1 i hi).1
  rw [padicNorm_prod_fin, prod_congr rfl (fun p hp => (show padicNorm 2 (z p.2 - z p.1) = gz z p by
    unfold gz; rw [ite_eq_left_iff.mpr (fun h => absurd (hz0 p hp) h)])), ← prod_sdiff hsub, mul_assoc]
  have hS : 0 ≤ ∏ p ∈ Spr h \ U.image c, gz z p := prod_nonneg (fun p _ => gz_nonneg z p)
  refine le_mul_of_one_le_right hS ?_
  rw [prod_image (fun x hx y hy e => hc2 hx hy e), pow_mul, ← prod_const, ← prod_mul_distrib]
  calc (1 : ℚ) = ∏ i ∈ U, (1 : ℚ) := by rw [prod_const_one]
    _ ≤ ∏ i ∈ U, (gz z (c i) * 2 ^ Λ) := by
      refine prod_le_prod₀ (fun _ _ => zero_le_one) (fun i hi => ?_)
      unfold gz
      split_ifs with hne
      · have key : (2 : ℚ) ^ (-(Λ : ℤ)) ≤ padicNorm 2 (z (c i).2 - z (c i).1) := by
          rcases (hc1 i hi).2 with h1 | h2
          · have e1 : z i = z (c i).1 := by rw [h1]
            have := hz i hi (c i).2 (fun e => hne (e1.symm.trans e.symm))
            rw [← e1, ← padicNorm.neg, neg_sub]; exact this
          · have e2 : z i = z (c i).2 := by rw [h2]
            have := hz i hi (c i).1 (fun e => hne (e.trans e2))
            rw [← e2]; exact this
        calc (1 : ℚ) = (2 : ℚ) ^ (-(Λ : ℤ)) * 2 ^ Λ := by
              rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
          _ ≤ _ := mul_le_mul_of_nonneg_right key (by positivity)
      · rw [one_mul]; exact one_le_pow₀ (by norm_num)

/-- **CoreDet.** -/
theorem padicNorm_detR_le (U : Finset (Fin h)) (Λ : ℕ)
    (hz : ∀ i ∈ U, ∀ j, z j ≠ z i → (2 : ℚ) ^ (-(Λ : ℤ)) ≤ padicNorm 2 (z i - z j)) :
    padicNorm 2 (Matrix.of fun i j : Fin h =>
        if i ∈ U then ((j : ℕ) : ℚ) * z i ^ ((j : ℕ) - 1) else z i ^ (j : ℕ)).det ≤
      (∏ p ∈ Spr h, gz z p) * 2 ^ (Λ * U.card) := by
  have hdet : (Matrix.of fun i j : Fin h =>
      if i ∈ U then ((j : ℕ) : ℚ) * z i ^ ((j : ℕ) - 1) else z i ^ (j : ℕ)).det = eval z (Wm U).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Wm]
    split_ifs <;> simp
  rw [hdet]
  have hR : 0 ≤ (∏ p ∈ Spr h, gz z p) * 2 ^ (Λ * U.card) :=
    mul_nonneg (prod_nonneg (fun p _ => gz_nonneg z p)) (by positivity)
  refine Submodule.span_induction (p := fun y _ => padicNorm 2 (eval z y) ≤
      (∏ p ∈ Spr h, gz z p) * 2 ^ (Λ * U.card)) ?_ ?_ ?_ ?_ (det_Wm_mem_span U)
  · intro y hy; obtain ⟨C, hC, rfl⟩ := hy; exact padicNorm_eval_gen_le hz hC
  · rw [map_zero, padicNorm.zero]; exact hR
  · intro y w _ _ hy hw; rw [map_add]; exact padicNorm.nonarchimedean.trans (max_le hy hw)
  · intro n y _ hy
    rw [map_zsmul, zsmul_eq_mul, padicNorm.mul]
    calc padicNorm 2 (n : ℚ) * padicNorm 2 (eval z y) ≤ 1 * padicNorm 2 (eval z y) :=
          mul_le_mul_of_nonneg_right (padicNorm.of_int n) (padicNorm.nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hy

end CoreDet
end Q
end Chi2Irr
