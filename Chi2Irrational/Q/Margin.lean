/-
# Theorem Q: the margins `alphaCore q + c₂ + β < 0` (RESULT §2, §4.2)

Closed forms: with `log n = v₂(n) log 2 + log(oddPart n)`,
* odd `q`: `alphaCore + c2Odd + betaOdd = 133/60 − ½ log 2 + ¼ log(q² − 1) − ⅓ log q − 2.078 − ½ log(q/3)
  < 133/60 − 2.078 − ½ log 2 + ½ log 3 − ⅓ log q ≤ 133/60 − 2.078 − ½ log 2 + ⅙ log 3`, negative by `3⁵ < 2⁸`
  and `log 2 > 0.6931`;
* even `q`: `alphaCore + c2Even + betaEven = 133/60 + ½ log 2 + ¼ log(q² − 1) − ⅓ log q − 3.03 − ½ log(q/14)
  < 133/60 − 3.03 + ½ log 2 + ⅙ log 14 ≤ 133/60 − 3.03 + (7/6) log 2` (`14 < 16`), negative by `log 2 < 0.6932`.
Numerical check: `scripts/q/margin_check.py`.
-/
import Chi2Irrational.Q.Defs
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Chi2Irr
namespace Q

/-- `n = 2^{v₂(n)} · oddPart n`. -/
lemma two_pow_mul_oddPart (n : ℕ) : 2 ^ padicValNat 2 n * oddPart n = n :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

/-- `log n = v₂(n) log 2 + log(oddPart n)` for `n ≠ 0`. -/
lemma log_eq_padicVal_add_log_oddPart {n : ℕ} (hn : n ≠ 0) :
    Real.log n = (padicValNat 2 n : ℝ) * Real.log 2 + Real.log (oddPart n) := by
  have hmul := two_pow_mul_oddPart n
  have hodd : oddPart n ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; exact hn hmul.symm
  conv_lhs => rw [← hmul]
  push_cast
  rw [Real.log_mul (by positivity) (by exact_mod_cast hodd), Real.log_pow]

/-- `log(q² − 1) < 2 log q` for `q ≥ 2`. -/
lemma log_sq_sub_one_lt {q : ℕ} (hq : 2 ≤ q) :
    Real.log ((q ^ 2 - 1 : ℕ) : ℝ) < 2 * Real.log q := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  rw [Nat.cast_sub h1, show 2 * Real.log q = Real.log ((q : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
  push_cast
  apply Real.log_lt_log
  · have : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast hq4
    linarith
  · linarith

/-- **Margin at odd `q`** (RESULT §2). -/
theorem margin_odd_proof (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    alphaCore q + c2Odd q + betaOdd q < 0 := by
  have hv : padicValNat 2 q = 0 :=
    padicValNat.eq_zero_of_not_dvd (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr ho)
  have hoq : oddPart q = q := by simp [oddPart, hv]
  have hne : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have hL := log_eq_padicVal_add_log_oddPart hne
  have hlt := log_sq_sub_one_lt (q := q) (by omega)
  have hq3 : Real.log 3 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have h35 : 5 * Real.log 3 < 8 * Real.log 2 := by
    have := Real.log_lt_log (by norm_num) (show (3 : ℝ) ^ 5 < 2 ^ 8 by norm_num)
    rwa [Real.log_pow, Real.log_pow] at this
  have hdiv : Real.log ((q : ℝ) / 3) = Real.log q - Real.log 3 :=
    Real.log_div (by positivity) (by norm_num)
  have h2 := Real.log_two_gt_d9
  unfold alphaCore c2Odd betaOdd
  rw [hoq, hdiv]
  norm_num at h2 ⊢
  nlinarith

/-- **Margin at even `q ≥ 14`** (RESULT §4.2). -/
theorem margin_even_proof (q : ℕ) (hq : 14 ≤ q) (he : Even q) :
    alphaCore q + c2Even q + betaEven q < 0 := by
  have hne : q ^ 2 - 1 ≠ 0 := by
    have : 196 ≤ q ^ 2 := by nlinarith
    omega
  have hL := log_eq_padicVal_add_log_oddPart hne
  have hodd : padicValNat 2 (q ^ 2 - 1) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    obtain ⟨k, rfl⟩ := he
    refine ⟨2 * (k * k) - 1, ?_⟩
    have h4 : (k + k) ^ 2 = 4 * (k * k) := by ring
    have : 1 ≤ k * k := by nlinarith
    rw [h4]; omega
  have hQ := log_eq_padicVal_add_log_oddPart (n := q) (by omega)
  have hlt := log_sq_sub_one_lt (q := q) (by omega)
  have hq14 : Real.log 14 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have h14 : Real.log 14 < 4 * Real.log 2 := by
    have := Real.log_lt_log (by norm_num) (show (14 : ℝ) < 2 ^ 4 by norm_num)
    rwa [Real.log_pow] at this
  have hdiv : Real.log ((q : ℝ) / 14) = Real.log q - Real.log 14 :=
    Real.log_div (by positivity) (by norm_num)
  have h2 := Real.log_two_lt_d9
  rw [hodd] at hL
  unfold alphaCore c2Even betaEven
  rw [hdiv]
  norm_num at h2 hL ⊢
  nlinarith

end Q
end Chi2Irr
