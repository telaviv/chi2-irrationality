/-
# Lemma P, Steps 1–2: the Lagrange-basis Gram matrix (any `K = h`)

* `LamLin q K r`: the functional `Λ_r = A + r·B` as a `ℚ`-linear map.
* `fpoly h i = ∏_{m≠i} (X − x_m)` (Lagrange basis up to scaling), `Cm h` its coefficient matrix.
* `det_gram`: `det (Λ_r(f_i f_j)) = (det C)² · Δ_h(r)`; hence `Delta_eval_ne_zero_of_det`:
  if `det (α_i Λ_r(f_i f_j) β_j) ≠ 0` then `Δ_h(r) ≠ 0` (no value of `det C` is needed).
* Entries: `Afun`/`Bfun` on `f_i f_j` (`Afun_offdiag`, `Bfun_offdiag`, `Afun_diag`, `Bfun_diag`), with
  `Fpoly i j = X ∏_{m∉{i,j}} (X − x_m)` and `Qpoly i = (g_i − g_i(x_i))/(X − x_i)`, `g_i = X f_i`.
-/
import Chi2Irrational.Machine

namespace Chi2Irr

open Polynomial Finset

/-- `μ` as a linear map. -/
noncomputable def muLin (w : ℚ) : ℚ[X] →ₗ[ℚ] ℚ := Polynomial.lsum (fun d => LinearMap.mulRight ℚ (muMono w d))

lemma muLin_apply (w : ℚ) (R : ℚ[X]) : muLin w R = muPoly w R := by
  unfold muLin muPoly
  rw [Polynomial.lsum_apply]
  rfl

/-- `Λ_r = A + r·B` as a linear map. -/
noncomputable def LamLin (q K : ℕ) (r : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (muLin (wt q)).comp ((divByMonicHom (Dpoly K)).comp (LinearMap.mulRight ℚ X)) +
    ∑ k ∈ range K, (4 * omega K k * Spart q k - 4 * r * omega K k * (q : ℚ) ^ (2 * k + 1)) •
      Polynomial.leval (pole k)

lemma LamLin_apply (q K : ℕ) (r : ℚ) (g : ℚ[X]) : LamLin q K r g = Afun q K g + r * Bfun q K g := by
  unfold LamLin Afun Bfun
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, divByMonicHom_apply, muLin_apply]
  simp only [LinearMap.smul_apply, Polynomial.leval_apply, smul_eq_mul]
  rw [add_assoc]
  congr 1
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  ring

/-- The Lagrange basis polynomials `f_i = ∏_{m<K, m≠i} (X − x_m)`. -/
noncomputable def fpoly (K i : ℕ) : ℚ[X] := ∏ m ∈ (range K).erase i, (X - C (pole m))

lemma pole_injective : Function.Injective pole := by
  intro a b h
  unfold pole at h
  have : (a : ℚ) = b := by linarith
  exact_mod_cast this

lemma pole_sub_ne_zero {a b : ℕ} (h : a ≠ b) : pole a - pole b ≠ 0 :=
  sub_ne_zero.mpr (fun e => h (pole_injective e))

lemma dPrime_ne_zero (K k : ℕ) : dPrime K k ≠ 0 := by
  unfold dPrime
  exact prod_ne_zero_iff.mpr (fun m hm => pole_sub_ne_zero (ne_of_mem_erase hm).symm)

lemma natDegree_fpoly_lt {K i : ℕ} (hi : i < K) : (fpoly K i).natDegree < K := by
  unfold fpoly
  rw [natDegree_prod_of_monic _ _ (fun m _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
  rw [card_erase_of_mem (mem_range.mpr hi), card_range]
  omega

lemma eval_fpoly (K i k : ℕ) (hk : k < K) :
    (fpoly K i).eval (pole k) = if k = i then dPrime K i else 0 := by
  unfold fpoly dPrime
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  split_ifs with h
  · subst h; rfl
  · exact prod_eq_zero (mem_erase.mpr ⟨h, mem_range.mpr hk⟩) (sub_self _)

/-- `D = (X − x_i) f_i` for `i < K`. -/
lemma Dpoly_eq_mul_fpoly {K i : ℕ} (hi : i < K) : Dpoly K = (X - C (pole i)) * fpoly K i := by
  unfold Dpoly fpoly
  exact (mul_prod_erase (range K) (fun m => X - C (pole m)) (mem_range.mpr hi)).symm

/-- `F_ij = X ∏_{m ∉ {i, j}} (X − x_m)`. -/
noncomputable def Fpoly (K i j : ℕ) : ℚ[X] := X * ∏ m ∈ ((range K).erase i).erase j, (X - C (pole m))

/-- `f_i f_j X = D · F_ij` for `i ≠ j`. -/
lemma fpoly_mul_fpoly_X {K i j : ℕ} (hi : i < K) (hj : j < K) (hij : i ≠ j) :
    fpoly K i * fpoly K j * X = Dpoly K * Fpoly K i j := by
  have hj' : j ∈ (range K).erase i := mem_erase.mpr ⟨hij.symm, mem_range.mpr hj⟩
  have hi' : i ∈ (range K).erase j := mem_erase.mpr ⟨hij, mem_range.mpr hi⟩
  have e1 : fpoly K i = (X - C (pole j)) * ∏ m ∈ ((range K).erase i).erase j, (X - C (pole m)) := by
    unfold fpoly; exact (mul_prod_erase ((range K).erase i) (fun m => X - C (pole m)) hj').symm
  have e2 : fpoly K j = (X - C (pole i)) * ∏ m ∈ ((range K).erase i).erase j, (X - C (pole m)) := by
    unfold fpoly
    have := mul_prod_erase ((range K).erase j) (fun m => X - C (pole m)) hi'
    rw [erase_right_comm] at this
    exact this.symm
  rw [Dpoly_eq_mul_fpoly hi, e1, e2]
  unfold Fpoly
  ring

/-- `g_i = X f_i`. -/
noncomputable def gpoly (K i : ℕ) : ℚ[X] := X * fpoly K i

/-- `Q_i = (g_i − g_i(x_i)) / (X − x_i)`. -/
noncomputable def Qpoly (K i : ℕ) : ℚ[X] :=
  (gpoly K i - C ((gpoly K i).eval (pole i))) /ₘ (X - C (pole i))

lemma gpoly_eq (K i : ℕ) :
    gpoly K i = (X - C (pole i)) * Qpoly K i + C ((gpoly K i).eval (pole i)) := by
  unfold Qpoly
  have hroot : IsRoot (gpoly K i - C ((gpoly K i).eval (pole i))) (pole i) := by
    simp [IsRoot]
  rw [mul_divByMonic_eq_iff_isRoot.mpr hroot]
  ring

lemma eval_gpoly_pole (K i : ℕ) : (gpoly K i).eval (pole i) = pole i * dPrime K i := by
  unfold gpoly fpoly dPrime
  rw [eval_mul, eval_X, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

lemma natDegree_C_mul_fpoly_lt {K i : ℕ} (hi : i < K) (c : ℚ) :
    (C c * fpoly K i).degree < (Dpoly K).degree := by
  have hD : Dpoly K = (X - C (pole i)) * fpoly K i := Dpoly_eq_mul_fpoly hi
  have hf : fpoly K i ≠ 0 := prod_ne_zero_iff.mpr (fun m _ => X_sub_C_ne_zero _)
  have hD0 : Dpoly K ≠ 0 := by rw [hD]; exact mul_ne_zero (X_sub_C_ne_zero _) hf
  have hdeg : (Dpoly K).natDegree = (fpoly K i).natDegree + 1 := by
    rw [hD, natDegree_mul (X_sub_C_ne_zero _) hf, natDegree_X_sub_C]; ring
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [map_zero, zero_mul, degree_zero]
    exact bot_lt_iff_ne_bot.mpr (fun h => hD0 (degree_eq_bot.mp h))
  · rw [degree_C_mul hc, degree_eq_natDegree hf, degree_eq_natDegree hD0, hdeg]
    exact_mod_cast Nat.lt_succ_self _

/-- `f_i² X = D Q_i + g_i(x_i) f_i`, so `(f_i² X) div D = Q_i`. -/
lemma fpoly_sq_X_divByMonic {K i : ℕ} (hi : i < K) :
    (fpoly K i * fpoly K i * X) /ₘ Dpoly K = Qpoly K i := by
  have hmon : (Dpoly K).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have key : fpoly K i * fpoly K i * X =
      C ((gpoly K i).eval (pole i)) * fpoly K i + Dpoly K * Qpoly K i := by
    have h := gpoly_eq K i
    set G := (gpoly K i).eval (pole i) with hG
    have hg : gpoly K i = X * fpoly K i := rfl
    rw [hg] at h
    rw [Dpoly_eq_mul_fpoly hi]
    linear_combination (fpoly K i) * h
  exact (div_modByMonic_unique (Qpoly K i) (C ((gpoly K i).eval (pole i)) * fpoly K i) hmon
    ⟨key.symm ▸ by ring, natDegree_C_mul_fpoly_lt hi _⟩).1

/-! ### The functionals on `f_i f_j` -/

lemma sum_fpoly_fpoly_eval (K i j : ℕ) (hi : i < K) (c : ℕ → ℚ) :
    ∑ k ∈ range K, (fpoly K i * fpoly K j).eval (pole k) * c k =
      if i = j then dPrime K i * dPrime K i * c i else 0 := by
  rw [sum_eq_single i]
  · rw [eval_mul, eval_fpoly K i i hi, eval_fpoly K j i hi]
    split_ifs with h1 h2 <;> simp_all
  · intro k hk hki
    rw [eval_mul, eval_fpoly K i k (mem_range.mp hk), ite_eq_right hki, zero_mul, zero_mul]
  · intro h; exact absurd (mem_range.mpr hi) h

lemma Bfun_fpoly (q K i j : ℕ) (hi : i < K) :
    Bfun q K (fpoly K i * fpoly K j) =
      if i = j then -4 * pole i * dPrime K i * (q : ℚ) ^ (2 * i + 1) else 0 := by
  unfold Bfun
  have := sum_fpoly_fpoly_eval K i j hi (fun k => omega K k * (q : ℚ) ^ (2 * k + 1))
  simp only [← mul_assoc] at this ⊢
  rw [this]
  split_ifs with h
  · unfold omega
    field_simp [dPrime_ne_zero K i]
  · ring

lemma Afun_offdiag (q K i j : ℕ) (hi : i < K) (hj : j < K) (hij : i ≠ j) :
    Afun q K (fpoly K i * fpoly K j) = muPoly (wt q) (Fpoly K i j) := by
  unfold Afun
  rw [fpoly_mul_fpoly_X hi hj hij, mul_divByMonic_cancel_left _ (monic_prod_of_monic _ _
    (fun _ _ => monic_X_sub_C _))]
  have := sum_fpoly_fpoly_eval K i j hi (fun k => omega K k * Spart q k)
  simp only [← mul_assoc] at this ⊢
  rw [this, ite_eq_right hij, mul_zero, add_zero]

lemma Afun_diag (q K i : ℕ) (hi : i < K) :
    Afun q K (fpoly K i * fpoly K i) =
      muPoly (wt q) (Qpoly K i) + 4 * pole i * dPrime K i * Spart q i := by
  unfold Afun
  rw [fpoly_sq_X_divByMonic hi]
  have := sum_fpoly_fpoly_eval K i i hi (fun k => omega K k * Spart q k)
  simp only [← mul_assoc] at this ⊢
  rw [this]
  simp only [↓reduceIte]
  unfold omega
  field_simp [dPrime_ne_zero K i]

/-! ### The Gram identity -/

/-- The coefficient matrix of the `f_i` (`K = h`). -/
noncomputable def Cm (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i d => (fpoly h i).coeff d

/-- `H(r) = A + r B`, entries `Λ_r(X^{d+e})`. -/
lemma Amat_add_smul_Bmat_apply (q h : ℕ) (r : ℚ) (d e : Fin h) :
    (Amat q h + r • Bmat q h) d e = LamLin q h r (X ^ ((d : ℕ) + e)) := by
  rw [LamLin_apply]
  simp [Amat, Bmat, Matrix.add_apply, Matrix.smul_apply]

/-- The Gram matrix of `Λ_r` in the basis `f_i`. -/
noncomputable def Gram (q h : ℕ) (r : ℚ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => LamLin q h r (fpoly h i * fpoly h j)

lemma Gram_eq (q h : ℕ) (r : ℚ) : Gram q h r = Cm h * (Amat q h + r • Bmat q h) * (Cm h).transpose := by
  ext i j
  have expand : ∀ k : Fin h, fpoly h k = ∑ d : Fin h, C (Cm h k d) * X ^ (d : ℕ) := by
    intro k
    show fpoly h k = ∑ d : Fin h, C ((fpoly h k).coeff d) * X ^ (d : ℕ)
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

theorem det_gram (q h : ℕ) (r : ℚ) : (Gram q h r).det = (Cm h).det ^ 2 * (Delta q h).eval r := by
  rw [Gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, eval_Delta]
  ring

/-- **Step 1.** A nonzero rescaled Gram determinant forces `Δ_h(r) ≠ 0`. -/
theorem Delta_eval_ne_zero_of_det {q h : ℕ} {r : ℚ} (α β : Fin h → ℚ)
    (hdet : (Matrix.of fun i j => α i * Gram q h r i j * β j).det ≠ 0) : (Delta q h).eval r ≠ 0 := by
  have e : (Matrix.of fun i j => α i * Gram q h r i j * β j) =
      Matrix.diagonal α * Gram q h r * Matrix.diagonal β := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply]
  rw [e, Matrix.det_mul, Matrix.det_mul, det_gram] at hdet
  intro h0
  rw [h0, mul_zero, mul_zero, zero_mul] at hdet
  exact hdet rfl

end Chi2Irr
