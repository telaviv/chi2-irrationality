/-
# The two series behind Lemma 1

* `powSum_eq_tsum`: the rational recurrence `powSum w n` equals `∑_{t≥1} t^n w^t` (`0 ≤ w < 1`).
* `pole_series`: `∑_{t≥1} w^t · (−1/(t − x_k)²) = −4 (q^{2k+1} χ₂(1/q) − S_k)` for `w = q⁻²`,
  i.e. `μ(1/(u − x_k)) = −4(q^{2k+1}χ − S_k)`.
-/
import Chi2Irrational.Defs
import Chi2Irrational.Machine

namespace Chi2Irr

open Finset

lemma summable_powW (n : ℕ) {W : ℝ} (h0 : 0 ≤ W) (h1 : W < 1) :
    Summable (fun t : ℕ => ((t : ℝ) + 1) ^ n * W ^ (t + 1)) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one n
    (r := W) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have := (summable_nat_add_iff 1).mpr hs
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- `(x+1)^(n+1) − x^(n+1) = ∑_{j≤n} C(n+1, j) (−1)^(n−j) (x+1)^j`. -/
lemma succ_pow_sub_pow (x : ℝ) (n : ℕ) :
    (x + 1) ^ (n + 1) - x ^ (n + 1) =
      ∑ j ∈ range (n + 1), ((n + 1).choose j : ℝ) * (-1) ^ (n - j) * (x + 1) ^ j := by
  have h := add_pow (x + 1) (-1 : ℝ) (n + 1)
  rw [show x + 1 + -1 = x by ring, sum_range_succ] at h
  rw [h]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  rw [sub_add_cancel_right, ← sum_neg_distrib]
  refine sum_congr rfl (fun j hj => ?_)
  have hj : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
  ring

/-- **Power sums.** `powSum w n = ∑_{t≥1} t^n w^t` for `0 ≤ w < 1`. -/
theorem powSum_eq_tsum {w : ℚ} (h0 : 0 ≤ w) (h1 : w < 1) (n : ℕ) :
    ((powSum w n : ℚ) : ℝ) = ∑' t : ℕ, ((t : ℝ) + 1) ^ n * (w : ℝ) ^ (t + 1) := by
  have hW0 : (0 : ℝ) ≤ w := by exact_mod_cast h0
  have hW1 : (w : ℝ) < 1 := by exact_mod_cast h1
  have hne : (1 : ℝ) - w ≠ 0 := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  cases n with
  | zero =>
    rw [powSum]
    push_cast
    simp only [pow_zero, one_mul, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hW0 hW1]
    field_simp
  | succ n =>
    rw [powSum]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j => ((n + 1).choose j : ℝ) * (-1) ^ (n - j) * ((powSum w j : ℚ) : ℝ)) (n + 1)]
    rw [div_eq_iff hne]
    set S := ∑' t : ℕ, ((t : ℝ) + 1) ^ (n + 1) * (w : ℝ) ^ (t + 1) with hS
    -- `w · S = ∑ t^{n+1} w^{t+1}` (shift by one; the `t = 0` term vanishes)
    set f : ℕ → ℝ := fun t => (t : ℝ) ^ (n + 1) * (w : ℝ) ^ (t + 1) with hf
    have hgshift : Summable (fun t : ℕ => f (t + 1)) := by
      have hc : ∀ t : ℕ, (w : ℝ) * (((t : ℝ) + 1) ^ (n + 1) * (w : ℝ) ^ (t + 1)) = f (t + 1) := by
        intro t
        simp only [hf]
        push_cast
        ring
      exact ((summable_powW (n + 1) hW0 hW1).mul_left (w : ℝ)).congr hc
    have hsum0 : Summable f := (summable_nat_add_iff 1).mp hgshift
    have hshift : (w : ℝ) * S = ∑' t : ℕ, f t := by
      rw [tsum_eq_zero_add' (f := f) hgshift]
      have hf0 : f 0 = 0 := by simp [hf]
      rw [hf0, zero_add, hS, ← tsum_mul_left]
      congr 1
      ext t
      simp only [hf]
      push_cast
      ring
    have hdiff : S * (1 - w) = ∑' t : ℕ,
        ∑ j ∈ range (n + 1), ((n + 1).choose j : ℝ) * (-1) ^ (n - j) *
          (((t : ℝ) + 1) ^ j * (w : ℝ) ^ (t + 1)) := by
      rw [mul_sub, mul_one, mul_comm S, hshift, hS,
        ← (summable_powW (n + 1) hW0 hW1).tsum_sub hsum0]
      congr 1
      ext t
      simp only [hf]
      rw [← sub_mul, succ_pow_sub_pow, sum_mul]
      refine sum_congr rfl (fun j _ => by ring)
    rw [hdiff, Summable.tsum_finsetSum (fun j _ =>
      (summable_powW j hW0 hW1).mul_left (((n + 1).choose j : ℝ) * (-1) ^ (n - j)))]
    refine sum_congr rfl (fun j hj => ?_)
    rw [tsum_mul_left, ih j (mem_range.mp hj)]

/-- **The pole series.** For `q ≥ 2`, `w = q⁻²`:
`∑_{t≥1} w^t · (−1/(t − x_k)²) = −4 (q^{2k+1} χ₂(1/q) − S_k)`. -/
theorem pole_series {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    ∑' t : ℕ, ((wt q : ℚ) : ℝ) ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2)) =
      -4 * ((q : ℝ) ^ (2 * k + 1) * chi2 (1 / (q : ℝ)) - (Spart q k : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hz : |1 / (q : ℝ)| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    rw [div_le_one hq0]
    exact_mod_cast (by omega : 1 ≤ q)
  set z : ℝ := 1 / (q : ℝ) with hzdef
  have hzq : (q : ℝ) * z = 1 := by rw [hzdef]; field_simp
  -- split χ₂ after the first `k + 1` terms
  have hsplit := (summable_chi2Term hz).sum_add_tsum_nat_add (k + 1)
  -- `q^{2k+1} · (first k+1 terms) = S_k`
  have hhead : (q : ℝ) ^ (2 * k + 1) * ∑ i ∈ range (k + 1), chi2Term z i = (Spart q k : ℝ) := by
    unfold Spart chi2Term
    push_cast
    rw [mul_sum]
    refine sum_congr rfl (fun j hj => ?_)
    have hj : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have : (q : ℝ) ^ (2 * k + 1) * z ^ (2 * j + 1) = (q : ℝ) ^ (2 * (k - j)) := by
      rw [show 2 * k + 1 = 2 * (k - j) + (2 * j + 1) by omega, pow_add, mul_assoc, ← mul_pow, hzq,
        one_pow, mul_one]
    rw [← this]
    ring
  -- the tail, term by term
  have htail : ∀ t : ℕ, (q : ℝ) ^ (2 * k + 1) * chi2Term z (t + (k + 1)) =
      ((wt q : ℚ) : ℝ) ^ (t + 1) * (1 / 4) * (1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2) := by
    intro t
    unfold chi2Term wt pole
    push_cast
    have hw : (1 / (q : ℝ) ^ 2) ^ (t + 1) = z ^ (2 * t + 2) := by
      rw [hzdef, ← one_div_pow, ← pow_mul]
      ring_nf
    rw [hw]
    have hpow : (q : ℝ) ^ (2 * k + 1) * z ^ (2 * (t + (k + 1)) + 1) = z ^ (2 * t + 2) := by
      rw [show 2 * (t + (k + 1)) + 1 = (2 * k + 1) + (2 * t + 2) by ring, pow_add z, ← mul_assoc,
        ← mul_pow, hzq, one_pow, one_mul]
    have hden : (2 * ((t : ℝ) + ((k : ℝ) + 1)) + 1) ^ 2 =
        4 * ((t : ℝ) + 1 - -((k : ℝ) + 1 / 2)) ^ 2 := by
      ring
    rw [mul_div_assoc', hpow, hden]
    have : ((t : ℝ) + 1 - -((k : ℝ) + 1 / 2)) ≠ 0 := by
      have : (0 : ℝ) ≤ t := t.cast_nonneg
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      intro h0
      linarith
    field_simp
  have hts : Summable (fun t => chi2Term z (t + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).mpr (summable_chi2Term hz)
  have key : (q : ℝ) ^ (2 * k + 1) * chi2 z - (Spart q k : ℝ) =
      ∑' t : ℕ, ((wt q : ℚ) : ℝ) ^ (t + 1) * (1 / 4) *
        (1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2) := by
    rw [chi2, ← hsplit, mul_add, hhead, add_sub_cancel_left, ← tsum_mul_left]
    exact tsum_congr htail
  rw [key, ← tsum_mul_left]
  refine tsum_congr (fun t => ?_)
  ring

end Chi2Irr
