/-
# Lemma P for Ti, Steps 1–2: the Lagrange-basis Gram matrix (any `K = h`)

Copy of the machine-dependent part of `NonVan/Gram.lean` for the Ti machine (`AfunT`, `BfunT`, `DeltaT`,
`wT`, `SpartT`, `poleW` of `TiQ/Machine.lean`). The generic part (`muLin`, `fpoly`, `Fpoly`, `gpoly`, `Qpoly`, `Cm`, …)
is reused from `NonVan/Gram.lean`.
* `LamLin q K r`: `Λ_r = AT + r·BT` as a `ℚ`-linear map.
* `det_gram`: `det (Λ_r(f_i f_j)) = (det C)² · Δ^Ti_h(r)`; `Delta_eval_ne_zero_of_det`.
* Entries: `Afun_offdiag`, `Afun_diag`, `Bfun_fpoly` for `AfunT`/`BfunT`.
-/
import Chi2Irrational.TiQ.Machine
import Chi2Irrational.NonVan.Gram

namespace Chi2Irr
namespace TiQ

open Polynomial Finset

/-- `Λ_r = AT + r·BT` as a linear map. -/
noncomputable def LamLin (q K : ℕ) (r : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (muLin (wT q)).comp ((divByMonicHom (Dpoly K)).comp (LinearMap.mulRight ℚ X)) +
    ∑ k ∈ range K, (4 * omega K k * SpartT q k - 4 * r * omega K k * poleW q k) •
      Polynomial.leval (pole k)

lemma LamLin_apply (q K : ℕ) (r : ℚ) (g : ℚ[X]) : LamLin q K r g = AfunT q K g + r * BfunT q K g := by
  unfold LamLin AfunT BfunT
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, divByMonicHom_apply, muLin_apply]
  simp only [LinearMap.smul_apply, Polynomial.leval_apply, smul_eq_mul]
  rw [add_assoc]
  congr 1
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  ring

/-! ### The functionals on `f_i f_j` -/

lemma Bfun_fpoly (q K i j : ℕ) (hi : i < K) :
    BfunT q K (fpoly K i * fpoly K j) =
      if i = j then -4 * pole i * dPrime K i * poleW q i else 0 := by
  unfold BfunT
  have := sum_fpoly_fpoly_eval K i j hi (fun k => omega K k * poleW q k)
  simp only [← mul_assoc] at this ⊢
  rw [this]
  split_ifs with h
  · unfold omega
    field_simp [dPrime_ne_zero K i]
  · ring

lemma Afun_offdiag (q K i j : ℕ) (hi : i < K) (hj : j < K) (hij : i ≠ j) :
    AfunT q K (fpoly K i * fpoly K j) = muPoly (wT q) (Fpoly K i j) := by
  unfold AfunT
  rw [fpoly_mul_fpoly_X hi hj hij, mul_divByMonic_cancel_left _ (monic_prod_of_monic _ _
    (fun _ _ => monic_X_sub_C _))]
  have := sum_fpoly_fpoly_eval K i j hi (fun k => omega K k * SpartT q k)
  simp only [← mul_assoc] at this ⊢
  rw [this, ite_eq_right hij, mul_zero, add_zero]

lemma Afun_diag (q K i : ℕ) (hi : i < K) :
    AfunT q K (fpoly K i * fpoly K i) =
      muPoly (wT q) (Qpoly K i) + 4 * pole i * dPrime K i * SpartT q i := by
  unfold AfunT
  rw [fpoly_sq_X_divByMonic hi]
  have := sum_fpoly_fpoly_eval K i i hi (fun k => omega K k * SpartT q k)
  simp only [← mul_assoc] at this ⊢
  rw [this]
  simp only [↓reduceIte]
  unfold omega
  field_simp [dPrime_ne_zero K i]

/-! ### The Gram identity -/

/-- `H(r) = AT + r BT`, entries `Λ_r(X^{d+e})`. -/
lemma Amat_add_smul_Bmat_apply (q h : ℕ) (r : ℚ) (d e : Fin h) :
    (AmatT q h + r • BmatT q h) d e = LamLin q h r (X ^ ((d : ℕ) + e)) := by
  rw [LamLin_apply]
  simp [AmatT, BmatT, Matrix.add_apply, Matrix.smul_apply]

/-- The Gram matrix of `Λ_r` in the basis `f_i`. -/
noncomputable def Gram (q h : ℕ) (r : ℚ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => LamLin q h r (fpoly h i * fpoly h j)

lemma Gram_eq (q h : ℕ) (r : ℚ) :
    Gram q h r = Cm h * (AmatT q h + r • BmatT q h) * (Cm h).transpose := by
  ext i j
  have expand : ∀ k : Fin h, fpoly h k = ∑ d : Fin h, C (Cm h k d) * X ^ (d : ℕ) := by
    intro k
    change fpoly h k = ∑ d : Fin h, C ((fpoly h k).coeff d) * X ^ (d : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun d => C ((fpoly h k).coeff d) * X ^ d) h]
    exact as_sum_range_C_mul_X_pow' _ (natDegree_fpoly_lt k.isLt)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Amat_add_smul_Bmat_apply]
  unfold Gram
  rw [expand i, expand j, sum_mul_sum]
  simp only [map_sum]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  have : C (Cm h i d) * X ^ (d : ℕ) * (C (Cm h j e) * X ^ (e : ℕ)) =
      (Cm h i d * Cm h j e) • X ^ ((d : ℕ) + e) := by
    rw [smul_eq_C_mul, C_mul, pow_add]; ring
  rw [this, map_smul, smul_eq_mul]
  ring

theorem det_gram (q h : ℕ) (r : ℚ) : (Gram q h r).det = (Cm h).det ^ 2 * (DeltaT q h).eval r := by
  rw [Gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, eval_DeltaT]
  ring

/-- **Step 1.** A nonzero rescaled Gram determinant forces `Δ^Ti_h(r) ≠ 0`. -/
theorem Delta_eval_ne_zero_of_det {q h : ℕ} {r : ℚ} (α β : Fin h → ℚ)
    (hdet : (Matrix.of fun i j => α i * Gram q h r i j * β j).det ≠ 0) : (DeltaT q h).eval r ≠ 0 := by
  have e : (Matrix.of fun i j => α i * Gram q h r i j * β j) =
      Matrix.diagonal α * Gram q h r * Matrix.diagonal β := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply]
  rw [e, Matrix.det_mul, Matrix.det_mul, det_gram] at hdet
  intro h0
  rw [h0, mul_zero, mul_zero, zero_mul] at hdet
  exact hdet rfl

end TiQ
end Chi2Irr
