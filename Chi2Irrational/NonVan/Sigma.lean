/-
# The progression sums σ(v, g) = Σ_{j≥0} v^j g(j)

For a polynomial `g` and `N > deg g`, `sigN N v g := Σ_{b<N} Δ^b g(0) · v^b/(1−v)^{b+1}` (a finite rational expression).
* `sigN_eq_tsum`: it equals `Σ_{j≥0} v^j g(j)` for `|v| < 1` (Newton series and `Σ_j C(j,b) v^j = v^b/(1−v)^{b+1}`);
* `padicNorm_sigN_le`: if `‖v‖_ℓ = ‖1 − v‖_ℓ = 1` and `‖g(j)‖_ℓ ≤ c` for all `j ∈ ℕ`, then `‖sigN N v g‖_ℓ ≤ c`;
* `sigN_sub`, `sigN_linear`: linearity and the value on linear polynomials.
-/
import Chi2Irrational.NonVan.LAdic

namespace Chi2Irr

open Polynomial Finset fwdDiff

/-- The Newton coefficient `Δ^b g(0)`. -/
noncomputable def newt (g : ℚ[X]) (b : ℕ) : ℚ := (fwdDiff (1 : ℚ))^[b] (fun x : ℚ => g.eval x) 0

/-- `σ_N(v, g) = Σ_{b<N} Δ^b g(0) v^b/(1−v)^{b+1}`. -/
noncomputable def sigN (N : ℕ) (v : ℚ) (g : ℚ[X]) : ℚ :=
  ∑ b ∈ range N, newt g b * v ^ b / (1 - v) ^ (b + 1)

lemma newt_eq_sum (g : ℚ[X]) (b : ℕ) :
    newt g b = ∑ k ∈ range (b + 1), ((-1 : ℚ) ^ (b - k) * b.choose k) * g.eval (k : ℚ) := by
  unfold newt
  rw [fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl (fun k _ => ?_)
  rw [zsmul_eq_mul, nsmul_eq_mul, zero_add, mul_one]
  push_cast
  ring

lemma newt_eq_zero {g : ℚ[X]} {b : ℕ} (hb : g.natDegree < b) : newt g b = 0 := by
  unfold newt
  rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hb]
  rfl

lemma newt_sub (g g' : ℚ[X]) (b : ℕ) : newt (g - g') b = newt g b - newt g' b := by
  simp only [newt_eq_sum, eval_sub, mul_sub, sum_sub_distrib]

lemma sigN_sub (N : ℕ) (v : ℚ) (g g' : ℚ[X]) : sigN N v (g - g') = sigN N v g - sigN N v g' := by
  unfold sigN
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun b _ => ?_)
  rw [newt_sub]
  ring

/-- Newton series: `g(j) = Σ_{b<N} C(j, b) Δ^b g(0)` for `N > deg g`. -/
lemma eval_eq_newton {g : ℚ[X]} {N : ℕ} (hN : g.natDegree < N) (j : ℕ) :
    g.eval (j : ℚ) = ∑ b ∈ range N, (j.choose b : ℚ) * newt g b := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℚ) (fun x : ℚ => g.eval x) j 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  rw [h]
  have e1 : ∑ k ∈ range (j + 1), (j.choose k : ℚ) * (fwdDiff (1 : ℚ))^[k] (fun x : ℚ => g.eval x) 0 =
      ∑ k ∈ range (j + 1 + N), (j.choose k : ℚ) * newt g k := by
    rw [← sum_subset (range_subset_range.mpr (Nat.le_add_right (j + 1) N))]
    · rfl
    · intro k _ hk
      rw [mem_range, not_lt] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have e2 : ∑ b ∈ range N, (j.choose b : ℚ) * newt g b =
      ∑ k ∈ range (j + 1 + N), (j.choose k : ℚ) * newt g k := by
    rw [← sum_subset (range_subset_range.mpr (Nat.le_add_left N (j + 1)))]
    intro k _ hk
    rw [mem_range, not_lt] at hk
    rw [newt_eq_zero (by omega), mul_zero]
  rw [e1, e2]

/-- `Σ_j C(j, b) v^j = v^b/(1−v)^{b+1}` for `|v| < 1`. -/
lemma hasSum_choose_geom {v : ℝ} (hv : |v| < 1) (b : ℕ) :
    HasSum (fun j : ℕ => (j.choose b : ℝ) * v ^ j) (v ^ b / (1 - v) ^ (b + 1)) := by
  have hv' : ‖v‖ < 1 := by rwa [Real.norm_eq_abs]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one b hv').mul_left (v ^ b)
  rw [← hasSum_nat_add_iff' b]
  have hzero : ∑ j ∈ range b, (j.choose b : ℝ) * v ^ j = 0 :=
    sum_eq_zero (fun j hj => by rw [Nat.choose_eq_zero_of_lt (mem_range.mp hj), Nat.cast_zero, zero_mul])
  rw [hzero, sub_zero]
  convert h using 1
  · ext n
    rw [pow_add]
    ring
  · ring

/-- **σ as a series.** -/
theorem sigN_eq_tsum {g : ℚ[X]} {N : ℕ} (hN : g.natDegree < N) {v : ℚ} (hv : |(v : ℝ)| < 1) :
    ((sigN N v g : ℚ) : ℝ) = ∑' j : ℕ, (v : ℝ) ^ j * ((g.eval (j : ℚ) : ℚ) : ℝ) := by
  have hterm : ∀ j : ℕ, (v : ℝ) ^ j * ((g.eval (j : ℚ) : ℚ) : ℝ) =
      ∑ b ∈ range N, (newt g b : ℝ) * ((j.choose b : ℝ) * (v : ℝ) ^ j) := by
    intro j
    rw [eval_eq_newton hN j]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl (fun b _ => by ring)
  rw [tsum_congr hterm]
  rw [Summable.tsum_finsetSum (fun b _ => ((hasSum_choose_geom hv b).summable.mul_left _))]
  unfold sigN
  push_cast
  refine sum_congr rfl (fun b _ => ?_)
  rw [tsum_mul_left, (hasSum_choose_geom hv b).tsum_eq]
  ring

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma padicNorm_newt_le {g : ℚ[X]} {c : ℚ} (hc : 0 ≤ c)
    (hg : ∀ j : ℕ, padicNorm ℓ (g.eval (j : ℚ)) ≤ c) (b : ℕ) : padicNorm ℓ (newt g b) ≤ c := by
  rw [newt_eq_sum]
  refine padicNorm.sum_le' (fun k _ => ?_) hc
  rw [padicNorm.mul]
  have h1 : padicNorm ℓ ((-1 : ℚ) ^ (b - k) * b.choose k) ≤ 1 := by
    have : ((-1 : ℚ) ^ (b - k) * b.choose k) = (((-1 : ℤ) ^ (b - k) * b.choose k : ℤ) : ℚ) := by
      push_cast; ring
    rw [this]
    exact padicNorm.of_int _
  calc padicNorm ℓ ((-1 : ℚ) ^ (b - k) * b.choose k) * padicNorm ℓ (g.eval (k : ℚ))
      ≤ 1 * c := mul_le_mul h1 (hg k) (padicNorm.nonneg _) zero_le_one
    _ = c := one_mul c

/-- **ℓ-adic bound for σ.** -/
theorem padicNorm_sigN_le {g : ℚ[X]} {N : ℕ} {v : ℚ} (hv : padicNorm ℓ v = 1)
    (hv1 : padicNorm ℓ (1 - v) = 1) {c : ℚ} (hc : 0 ≤ c)
    (hg : ∀ j : ℕ, padicNorm ℓ (g.eval (j : ℚ)) ≤ c) : padicNorm ℓ (sigN N v g) ≤ c := by
  unfold sigN
  refine padicNorm.sum_le' (fun b _ => ?_) hc
  rw [padicNorm.div, padicNorm.mul, padicNorm_pow, padicNorm_pow, hv, hv1, one_pow, one_pow,
    mul_one, div_one]
  exact padicNorm_newt_le hc hg b

/-- σ of a linear polynomial. -/
lemma sigN_linear {N : ℕ} (hN : 2 ≤ N) (c₀ c₁ v : ℚ) :
    sigN N v (C c₁ * X + C c₀) = c₀ / (1 - v) + c₁ * v / (1 - v) ^ 2 := by
  unfold sigN
  have hdeg : (C c₁ * X + C c₀).natDegree ≤ 1 := natDegree_linear_le
  rw [← sum_subset (range_subset_range.mpr hN)]
  · simp only [sum_range_succ, sum_range_zero, zero_add]
    have h0 : newt (C c₁ * X + C c₀) 0 = c₀ := by
      unfold newt; simp
    have h1 : newt (C c₁ * X + C c₀) 1 = c₁ := by
      unfold newt; simp [fwdDiff]
    rw [h0, h1]
    ring
  · intro b _ hb
    rw [mem_range, not_lt] at hb
    rw [newt_eq_zero (by omega), zero_mul, zero_div]

lemma newt_C_mul (c : ℚ) (g : ℚ[X]) (b : ℕ) : newt (C c * g) b = c * newt g b := by
  simp only [newt_eq_sum, eval_mul, eval_C, mul_sum]
  refine sum_congr rfl (fun k _ => by ring)

lemma sigN_C_mul (N : ℕ) (v c : ℚ) (g : ℚ[X]) : sigN N v (C c * g) = c * sigN N v g := by
  unfold sigN
  rw [mul_sum]
  refine sum_congr rfl (fun b _ => ?_)
  rw [newt_C_mul]
  ring

end Chi2Irr
