/-
# Lemma M, part 1: the binomial basis `Cb s`, forward differences of derivatives, and the matrix `Am`

* `Cb_pascal`: `Cb (s+1) (X + 1) = Cb (s+1) + Cb s`; hence `Δ (Cb (s+1))′ = (Cb s)′` on integers and
  `Δ^b (Cb s)′ (0) = (Cb (s − b))′(0) = (−1)^{s−b−1}/(s − b)` for `b < s`, `0` for `b ≥ s` (`fd_deriv_Cb`).
* `fd_deriv_intval` (RESULT §1 step 3 (A), "using v₂(x) ≤ x − 1"): for a polynomial `F` of degree `≤ d` that is
  integer-valued on `ℕ`, `‖Δ^b F′(0)‖₂ ≤ 2^{d − b}` (expand `F = Σ_s (Δ^s F(0)) Cb s`, `Δ^s F(0) ∈ ℤ`).
* `Am_eq`, `Am_bound` (RESULT §1 step 3 (C)): `A_{ni} = (−1)^n C_{i−n}(x_n)` for `n ≤ i` and `0` for `n > i`, so
  `‖A_{ni}‖₂ ≤ 2^{2(i−n)}`.
-/
import Chi2Irrational.TiQ.M.Defs

namespace Chi2Irr
namespace TiQ
namespace M

open Polynomial Finset
open scoped Nat

lemma fd_eq_sum (b : ℕ) (F : ℕ → ℚ) :
    fd b F = ∑ i ∈ range (b + 1), ((-1 : ℚ) ^ (b - i) * (b.choose i : ℚ)) * F i := by
  unfold fd
  rw [fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl (fun i _ => ?_)
  rw [zsmul_eq_mul]
  push_cast
  simp

/-- `fd` of polynomial values agrees with the forward difference of `P.eval` on `ℚ`. -/
lemma binom_fd_eval (P : ℚ[X]) (b : ℕ) :
    fd b (fun i => P.eval (i : ℚ)) = ((fwdDiff (1 : ℚ))^[b] (fun x => P.eval x)) 0 := by
  rw [fd_eq_sum, fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl (fun i _ => ?_)
  rw [zsmul_eq_mul]
  push_cast
  simp

lemma binom_fd_eval_eq_zero {P : ℚ[X]} {b : ℕ} (hb : P.natDegree < b) :
    fd b (fun i => P.eval (i : ℚ)) = 0 := by
  rw [binom_fd_eval, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hb]
  rfl

lemma Cb_natDegree (s : ℕ) : (Cb s).natDegree = s := by
  unfold Cb
  rw [natDegree_C_mul (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))),
    descPochhammer_natDegree]

lemma Cb_eval_nat (s n : ℕ) : (Cb s).eval (n : ℚ) = (n.choose s : ℚ) := by
  unfold Cb
  rw [eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div, div_eq_inv_mul]

lemma binom_eq_of_nat {p q : ℚ[X]} (h : ∀ n : ℕ, p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : ℚ)))
  · rintro _ ⟨n, rfl⟩; exact h n
  · exact Set.infinite_range_of_injective Nat.cast_injective

/-- Pascal's rule for the binomial polynomials. -/
lemma Cb_pascal (s : ℕ) : (Cb (s + 1)).comp (X + 1) = Cb (s + 1) + Cb s := by
  apply binom_eq_of_nat
  intro n
  rw [eval_comp, eval_add, eval_add, eval_X, eval_one, ← Nat.cast_succ, Cb_eval_nat, Cb_eval_nat,
    Cb_eval_nat, Nat.choose_succ_succ', Nat.cast_add]
  ring

lemma binom_deriv_pascal (s : ℕ) (t : ℚ) :
    (derivative (Cb (s + 1))).eval (t + 1) =
      (derivative (Cb (s + 1))).eval t + (derivative (Cb s)).eval t := by
  have h := congrArg (fun p => (derivative p).eval t) (Cb_pascal s)
  simp only [derivative_comp, derivative_add, derivative_X, derivative_one, add_zero, one_mul,
    eval_add, eval_comp, eval_X, eval_one] at h
  exact h

lemma binom_deriv_Cb_zero : derivative (Cb 0) = 0 := by
  simp [Cb]

lemma binom_fwdDiff_deriv (s : ℕ) :
    fwdDiff 1 (fun i : ℕ => (derivative (Cb s)).eval (i : ℚ)) =
      fun i : ℕ => (derivative (Cb (s - 1))).eval (i : ℚ) := by
  funext i
  rcases s with _ | s
  · simp [fwdDiff, binom_deriv_Cb_zero]
  · simp only [fwdDiff, Nat.cast_add, Nat.cast_one, binom_deriv_pascal, Nat.add_sub_cancel]
    ring

lemma binom_descP_eval_neg_one (n : ℕ) :
    (descPochhammer ℚ n).eval (-1) = (-1) ^ n * (n ! : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]; push_cast; ring

lemma binom_deriv_Cb_eval_zero (n : ℕ) :
    (derivative (Cb (n + 1))).eval 0 = (-1) ^ n / ((n + 1 : ℕ) : ℚ) := by
  unfold Cb
  rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, descPochhammer_succ_left,
    derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero, eval_comp,
    eval_sub, eval_X, eval_one, zero_sub, binom_descP_eval_neg_one, Nat.factorial_succ]
  have : (n ! : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- `Δ^b (Cb s)′ (0)`. -/
lemma fd_deriv_Cb (s b : ℕ) :
    fd b (fun i => (derivative (Cb s)).eval (i : ℚ)) =
      if b < s then (-1 : ℚ) ^ (s - 1 - b) / ((s - b : ℕ) : ℚ) else 0 := by
  induction b generalizing s with
  | zero =>
    simp only [fd, Function.iterate_zero, id_eq, Nat.cast_zero]
    rcases s with _ | s
    · simp [binom_deriv_Cb_zero]
    · rw [binom_deriv_Cb_eval_zero]; simp
  | succ b ih =>
    have e : fd (b + 1) (fun i => (derivative (Cb s)).eval (i : ℚ)) =
        fd b (fun i => (derivative (Cb (s - 1))).eval (i : ℚ)) := by
      unfold fd; rw [Function.iterate_succ_apply, binom_fwdDiff_deriv]
    rw [e, ih]
    split_ifs with h1 h2 h2
    · congr 2 <;> omega
    · exfalso; omega
    · exfalso; omega
    · rfl

lemma binom_fd_sum {ι : Type*} (S : Finset ι) (c : ι → ℚ) (g : ι → ℕ → ℚ) (b : ℕ) :
    fd b (fun i => ∑ s ∈ S, c s * g s i) = ∑ s ∈ S, c s * fd b (g s) := by
  simp only [fd_eq_sum, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun s _ => sum_congr rfl (fun i _ => by ring))

lemma binom_V2_neg_one_pow (m : ℕ) : V2 0 ((-1 : ℚ) ^ m) := by
  convert V2_pow (V2_neg V2_one) m using 1
  simp

lemma binom_fd_int {F : ℕ → ℚ} (hF : ∀ n, ∃ z : ℤ, F n = z) (b : ℕ) : V2 0 (fd b F) := by
  rw [fd_eq_sum]
  refine V2_sum _ _ (fun i _ => ?_)
  obtain ⟨z, hz⟩ := hF i
  rw [hz]
  have h1 := V2_mul (binom_V2_neg_one_pow (b - i)) (V2_natCast (b.choose i))
  have h2 := V2_mul h1 (V2_intCast z)
  simpa using h2

lemma binom_V2_inv_nat {n : ℕ} (hn : 0 < n) : V2 (-(n : ℤ)) (1 / (n : ℚ)) := by
  cases n with
  | zero => omega
  | succ m =>
    have h := V2_div_factorial (V2_natCast (m !)) (m + 1)
    have hm : (m ! : ℚ) ≠ 0 := by positivity
    have e : ((m ! : ℕ) : ℚ) / (((m + 1) ! : ℕ) : ℚ) = 1 / ((m + 1 : ℕ) : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; field_simp
    rw [← e]
    exact V2_mono (by have := vf_le (m + 1); omega) h

/-- Newton expansion of a polynomial in the binomial basis. -/
lemma binom_expand {F : ℚ[X]} {d : ℕ} (hd : F.natDegree ≤ d) :
    F = ∑ s ∈ range (d + 1), C (fd s (fun i => F.eval (i : ℚ))) * Cb s := by
  apply binom_eq_of_nat
  intro n
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, Cb_eval_nat]
  have hN := shift_eq_sum_fwdDiff_iter (1 : ℕ) (fun i : ℕ => F.eval (i : ℚ)) n 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at hN
  rw [hN]
  have h1 : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (fwdDiff 1)^[k] (fun i : ℕ => F.eval (i : ℚ)) 0 =
      ∑ k ∈ range (n + d + 1), (n.choose k : ℚ) * fd k (fun i : ℕ => F.eval (i : ℚ)) := by
    apply sum_subset
    · intro k hk; simp only [mem_range] at *; omega
    · intro k _ hk'
      simp only [mem_range, not_lt] at hk'
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : ∑ s ∈ range (d + 1), fd s (fun i : ℕ => F.eval (i : ℚ)) * (n.choose s : ℚ) =
      ∑ k ∈ range (n + d + 1), (n.choose k : ℚ) * fd k (fun i : ℕ => F.eval (i : ℚ)) := by
    rw [sum_subset (s₂ := range (n + d + 1)) ?_ ?_]
    · exact sum_congr rfl (fun k _ => mul_comm _ _)
    · intro k hk; simp only [mem_range] at *; omega
    · intro k _ hk'
      simp only [mem_range, not_lt] at hk'
      rw [binom_fd_eval_eq_zero (lt_of_le_of_lt hd (by omega)), zero_mul]
  rw [h1, h2]

/-- **The derivative bound** (RESULT §1 step 3 (A)). -/
lemma fd_deriv_intval {F : ℚ[X]} {d : ℕ} (hd : F.natDegree ≤ d)
    (hint : ∀ n : ℕ, ∃ z : ℤ, F.eval (n : ℚ) = z) (b : ℕ) :
    padicNorm 2 (fd b (fun i => (derivative F).eval (i : ℚ))) ≤ (2 : ℚ) ^ ((d : ℤ) - b) := by
  have hE := binom_expand hd
  have hD : ∀ x : ℚ, (derivative F).eval x = ∑ s ∈ range (d + 1),
      fd s (fun i => F.eval (i : ℚ)) * (derivative (Cb s)).eval x := by
    intro x
    conv_lhs => rw [hE]
    rw [derivative_sum, eval_finsetSum]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  have h1 : fd b (fun i => (derivative F).eval (i : ℚ)) = ∑ s ∈ range (d + 1),
      fd s (fun i => F.eval (i : ℚ)) * fd b (fun i => (derivative (Cb s)).eval (i : ℚ)) := by
    simp only [hD]
    exact binom_fd_sum _ _ (fun s i => (derivative (Cb s)).eval (i : ℚ)) b
  rw [h1]
  have key : V2 ((b : ℤ) - d) (∑ s ∈ range (d + 1),
      fd s (fun i => F.eval (i : ℚ)) * fd b (fun i => (derivative (Cb s)).eval (i : ℚ))) := by
    refine V2_sum _ _ (fun s hs => ?_)
    have hs' := mem_range.mp hs
    rw [fd_deriv_Cb]
    split_ifs with hbs
    · have hcs : V2 0 (fd s (fun i => F.eval (i : ℚ))) := binom_fd_int (fun n => hint n) s
      have h2 : V2 (-((s - b : ℕ) : ℤ)) ((-1 : ℚ) ^ (s - 1 - b) / ((s - b : ℕ) : ℚ)) := by
        rw [div_eq_mul_one_div]
        exact V2_mul' (binom_V2_neg_one_pow _) (binom_V2_inv_nat (by omega)) (by omega)
      exact V2_mul' hcs h2 (by omega)
    · rw [mul_zero]; exact V2_zero _
  unfold V2 at key
  convert key using 2
  ring

/-- Derivative values at the nodes of an integer-valued polynomial. -/
lemma deriv_intval_bound {F : ℚ[X]} {d : ℕ} (hd : F.natDegree ≤ d)
    (hint : ∀ n : ℕ, ∃ z : ℤ, F.eval (n : ℚ) = z) (i : ℕ) :
    padicNorm 2 ((derivative F).eval (i : ℚ)) ≤ (2 : ℚ) ^ (d : ℤ) := by
  set G := F.comp (X + C (i : ℚ)) with hG
  have hGd : G.natDegree ≤ d := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact hd
  have hGint : ∀ n : ℕ, ∃ z : ℤ, G.eval (n : ℚ) = z := by
    intro n
    obtain ⟨z, hz⟩ := hint (n + i)
    exact ⟨z, by rw [← hz, hG, eval_comp, eval_add, eval_X, eval_C, Nat.cast_add]⟩
  have h := fd_deriv_intval hGd hGint 0
  simp only [fd, Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero] at h
  rw [hG, derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul, eval_comp,
    eval_add, eval_X, eval_C, zero_add] at h
  exact h

lemma binom_descP_pole (s k : ℕ) : V2 (-(s : ℤ)) ((descPochhammer ℚ s).eval (pole k)) := by
  induction s with
  | zero => simpa using V2_one
  | succ s ih =>
    rw [descPochhammer_succ_eval]
    have e : pole k - (s : ℚ) = -(((2 * k + 2 * s + 1 : ℕ) : ℚ) / 2) := by
      unfold pole; push_cast; ring
    have h2 : V2 (-1) (pole k - (s : ℚ)) := by
      rw [e]
      have := V2_div_of_norm (V2_natCast (2 * k + 2 * s + 1)) padicNorm_two_self
      exact V2_neg (by simpa using this)
    exact V2_mul' ih h2 (by push_cast; omega)

/-- Values of `Cb s` at the poles: `‖C_s(x_k)‖₂ ≤ 2^{2s}`. -/
lemma Cb_pole_bound (s k : ℕ) : padicNorm 2 ((Cb s).eval (pole k)) ≤ (2 : ℚ) ^ (2 * (s : ℤ)) := by
  have h := V2_div_factorial (binom_descP_pole s k) s
  have e : (Cb s).eval (pole k) = (descPochhammer ℚ s).eval (pole k) / ((s ! : ℕ) : ℚ) := by
    unfold Cb; rw [eval_mul, eval_C, div_eq_inv_mul]
  rw [e]
  have h2 := V2_mono (show -(2 * (s : ℤ)) ≤ -(s : ℤ) - (vf s : ℤ) by have := vf_le s; omega) h
  unfold V2 at h2
  rwa [neg_neg] at h2

lemma binom_pole_succ (k : ℕ) : pole (k + 1) + 1 = pole k := by
  unfold pole; push_cast; ring

lemma binom_P_step (s k : ℕ) :
    (Cb (s + 1)).eval (pole (k + 1)) - (Cb (s + 1)).eval (pole k) = -(Cb s).eval (pole (k + 1)) := by
  have h := congrArg (fun p => p.eval (pole (k + 1))) (Cb_pascal s)
  simp only [eval_comp, eval_add, eval_X, eval_one, binom_pole_succ] at h
  rw [h]; ring

lemma binom_fd_P_le (i : ℕ) : ∀ n, n ≤ i → ∀ y : ℕ,
    (fwdDiff 1)^[n] (fun k : ℕ => (Cb i).eval (pole k)) y =
      (-1 : ℚ) ^ n * (Cb (i - n)).eval (pole (y + n)) := by
  intro n
  induction n with
  | zero => intro _ y; simp
  | succ n ih =>
    intro hn y
    rw [fd_succ, ih (by omega), ih (by omega)]
    have e : i - n = (i - (n + 1)) + 1 := by omega
    have h := binom_P_step (i - (n + 1)) (y + n)
    rw [← e] at h
    rw [show y + 1 + n = y + n + 1 by omega, show y + (n + 1) = y + n + 1 by omega, pow_succ]
    linear_combination (-1 : ℚ) ^ n * h

lemma binom_fd_P_gt (i m : ℕ) :
    (fwdDiff 1)^[i + 1 + m] (fun k : ℕ => (Cb i).eval (pole k)) = 0 := by
  induction m with
  | zero =>
    funext y
    rw [add_zero, fd_succ, binom_fd_P_le i i le_rfl, binom_fd_P_le i i le_rfl]
    simp [Cb]
  | succ m ih =>
    funext y
    rw [show i + 1 + (m + 1) = (i + 1 + m) + 1 by omega, fd_succ, ih]
    simp

lemma Am_zero {h : ℕ} {n i : Fin h} (hni : (i : ℕ) < n) : Am h n i = 0 := by
  simp only [Am, fd]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hni
  rw [hm, show (i : ℕ) + m + 1 = i + 1 + m by omega, binom_fd_P_gt]
  try rfl

/-- **Bound (C).** -/
lemma Am_bound (h : ℕ) (n i : Fin h) : padicNorm 2 (Am h n i) ≤ (2 : ℚ) ^ (2 * ((i : ℤ) - n)) := by
  by_cases hni : (i : ℕ) < n
  · rw [Am_zero hni, padicNorm.zero]; positivity
  · rw [not_lt] at hni
    have e : Am h n i = (-1 : ℚ) ^ (n : ℕ) * (Cb (i - n)).eval (pole (0 + n)) := by
      simp only [Am, fd]; exact binom_fd_P_le i n hni 0
    rw [e, padicNorm.mul]
    have h1 : padicNorm 2 ((-1 : ℚ) ^ (n : ℕ)) = 1 := by
      rcases neg_one_pow_eq_or ℚ (n : ℕ) with h' | h' <;> rw [h'] <;> simp
    rw [h1, one_mul]
    have h2 := Cb_pole_bound (i - n) (0 + n)
    rwa [Nat.cast_sub hni] at h2

end M
end TiQ
end Chi2Irr
