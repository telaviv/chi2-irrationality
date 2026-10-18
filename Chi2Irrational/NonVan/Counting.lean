/-
# Counting ℓ-close roots of a product (Lemma P, Step 4, general part)

For `P = ∏_{s∈T} (X − a_s)` and a point `t` with all `‖t − a_s‖_ℓ ≤ 1`, and a set `S ⊆ T` of roots with
`‖t − a_s‖ ≤ ℓ⁻¹`:
* `padicNorm_prod_le_of_close`: `‖P(t)‖ ≤ ℓ^{−#S}`;
* `eval_derivative_prod`: `P′(t) = Σ_{s∈T} ∏_{T∖s} (t − a)`;
* `padicNorm_deriv_le_of_close`: `‖P′(t)‖ ≤ ℓ^{−(#S−1)}`;
* `padicNorm_deriv_sub_le`: `‖P′(t) − Σ_{s∈S} ∏_{T∖s}(t − a)‖ ≤ ℓ^{−#S}`.
-/
import Chi2Irrational.NonVan.LAdic

namespace Chi2Irr

open Polynomial Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma padicNorm_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm ℓ (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

/-- A product with `#S` factors of norm `≤ ℓ⁻¹` and the rest of norm `≤ 1`. -/
lemma padicNorm_prod_le_of_close {ι : Type*} [DecidableEq ι] {T S : Finset ι} (hST : S ⊆ T)
    (f : ι → ℚ) (h1 : ∀ s ∈ T, padicNorm ℓ (f s) ≤ 1) (hS : ∀ s ∈ S, padicNorm ℓ (f s) ≤ (ℓ : ℚ)⁻¹) :
    padicNorm ℓ (∏ s ∈ T, f s) ≤ ((ℓ : ℚ)⁻¹) ^ S.card := by
  rw [padicNorm_prod, ← prod_sdiff hST]
  have hA : ∏ s ∈ T \ S, padicNorm ℓ (f s) ≤ 1 :=
    prod_le_one₀ (fun s _ => padicNorm.nonneg _) (fun s hs => h1 s (mem_sdiff.mp hs).1)
  have hB : ∏ s ∈ S, padicNorm ℓ (f s) ≤ ((ℓ : ℚ)⁻¹) ^ S.card := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun s _ => padicNorm.nonneg _) hS
  calc (∏ s ∈ T \ S, padicNorm ℓ (f s)) * ∏ s ∈ S, padicNorm ℓ (f s)
      ≤ 1 * ((ℓ : ℚ)⁻¹) ^ S.card :=
        mul_le_mul hA hB (prod_nonneg (fun s _ => padicNorm.nonneg _)) zero_le_one
    _ = _ := one_mul _

/-- `(∏ (X − a_s))′(t) = Σ_s ∏_{T∖s} (t − a)`. -/
lemma eval_derivative_prod {ι : Type*} [DecidableEq ι] (T : Finset ι) (a : ι → ℚ) (t : ℚ) :
    (derivative (∏ s ∈ T, (X - C (a s)))).eval t = ∑ s ∈ T, ∏ s' ∈ T.erase s, (t - a s') := by
  rw [derivative_prod_finset, eval_finsetSum]
  refine sum_congr rfl (fun s _ => ?_)
  simp [eval_prod]

lemma eval_prod_X_sub_C {ι : Type*} (T : Finset ι) (a : ι → ℚ) (t : ℚ) :
    (∏ s ∈ T, (X - C (a s))).eval t = ∏ s ∈ T, (t - a s) := by
  simp [eval_prod]

/-- `‖P′(t)‖ ≤ ℓ^{−(#S−1)}`. -/
lemma padicNorm_deriv_le_of_close {ι : Type*} [DecidableEq ι] {T S : Finset ι} (hST : S ⊆ T)
    (a : ι → ℚ) (t : ℚ) (h1 : ∀ s ∈ T, padicNorm ℓ (t - a s) ≤ 1)
    (hS : ∀ s ∈ S, padicNorm ℓ (t - a s) ≤ (ℓ : ℚ)⁻¹) :
    padicNorm ℓ ((derivative (∏ s ∈ T, (X - C (a s)))).eval t) ≤ ((ℓ : ℚ)⁻¹) ^ (S.card - 1) := by
  rw [eval_derivative_prod]
  refine padicNorm.sum_le' (fun s hs => ?_) (pow_nonneg ell_inv_pos.le _)
  have hsub : S.erase s ⊆ T.erase s := erase_subset_erase s hST
  have hb := padicNorm_prod_le_of_close hsub (fun s' => t - a s')
    (fun s' hs' => h1 s' (mem_of_mem_erase hs')) (fun s' hs' => hS s' (mem_of_mem_erase hs'))
  refine hb.trans (pow_le_pow_of_le_one ell_inv_pos.le ell_inv_le_one ?_)
  have := card_erase_le (s := S) (a := s)
  by_cases h : s ∈ S
  · rw [card_erase_of_mem h]
  · rw [erase_eq_of_notMem h]; omega

/-- `P′(t) ≡ Σ_{s∈S} ∏_{T∖s} (t − a)` modulo `ℓ^{#S}`. -/
lemma padicNorm_deriv_sub_le {ι : Type*} [DecidableEq ι] {T S : Finset ι} (hST : S ⊆ T)
    (a : ι → ℚ) (t : ℚ) (h1 : ∀ s ∈ T, padicNorm ℓ (t - a s) ≤ 1)
    (hS : ∀ s ∈ S, padicNorm ℓ (t - a s) ≤ (ℓ : ℚ)⁻¹) :
    padicNorm ℓ ((derivative (∏ s ∈ T, (X - C (a s)))).eval t -
      ∑ s ∈ S, ∏ s' ∈ T.erase s, (t - a s')) ≤ ((ℓ : ℚ)⁻¹) ^ S.card := by
  rw [eval_derivative_prod, ← sum_sdiff hST, add_sub_cancel_right]
  refine padicNorm.sum_le' (fun s hs => ?_) (pow_nonneg ell_inv_pos.le _)
  have hsT := mem_sdiff.mp hs
  have hsub : S ⊆ T.erase s := fun x hx => mem_erase.mpr ⟨fun e => hsT.2 (e ▸ hx), hST hx⟩
  exact padicNorm_prod_le_of_close hsub (fun s' => t - a s')
    (fun s' hs' => h1 s' (mem_of_mem_erase hs')) hS

end Chi2Irr
