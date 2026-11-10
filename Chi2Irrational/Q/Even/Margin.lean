/-
# Theorem Q₄: the margins `alphaCore q + c2EvenSharp q + PhiT q < 0` at `q = 6, 8, 10, 12`

Data: `(v₂ q, oddPart(q² − 1), oddPart q, cE(v₂ q)) = (1, 35, 3, 2/33), (3, 63, 1, −2/17), (1, 99, 5, 2/33),
(2, 143, 3, −1/21)`. Elementary log bounds (`log x ≤ x − 1` on ratios near `1`, and `log 2 < 0.6931471808`):
* `q = 6`: `log 35 ≤ log 36 − 1/36`, `log 9 ≤ log 8 + 1/8`; bound `−0.00904` (true margin `−0.00974`);
* `q = 8`: `log 63 < log 64`; bound `−0.238`;
* `q = 10`: `log 99 < log 100`, `log 5 ≤ log 4 + 1/4`; bound `−0.203`;
* `q = 12`: `log 143 < log 144`, `log 3 < log 4`; bound `−0.304`.
Numerical check: `scripts/q/margin_newQ_check.py` (Arb).
-/
import Chi2Irrational.Q.Even.Defs
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Chi2Irr
namespace Q

/-- `v₂(2^k m) = k` for odd `m`. -/
lemma padicValNat_two_pow_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) :
    padicValNat 2 (2 ^ k * m) = k := by
  rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero]

/-- `oddPart n = n` for odd `n`. -/
lemma oddPart_of_not_dvd {n : ℕ} (hn : ¬ 2 ∣ n) : oddPart n = n := by
  simp [oddPart, padicValNat.eq_zero_of_not_dvd hn]

/-- `log (a / b) ≤ a / b − 1` in the form `log a ≤ log b + a / b − 1`. -/
lemma log_le_log_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a ≤ Real.log b + (a / b - 1) := by
  have := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at this
  linarith

/-- **The margins** at `q = 6, 8, 10, 12`. -/
theorem margin_newQ_proof {q : ℕ} (hq : q ∈ newQ) :
    alphaCore q + c2EvenSharp q + (PhiT q : ℝ) < 0 := by
  simp only [newQ, Finset.mem_insert, Finset.mem_singleton] at hq
  have h2 := Real.log_two_lt_d9
  have h2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  rcases hq with rfl | rfl | rfl | rfl
  · -- q = 6
    have hv : padicValNat 2 6 = 1 := padicValNat_two_pow_mul_odd 1 3 (by norm_num) (by norm_num)
    have ho1 : oddPart (6 ^ 2 - 1) = 35 := oddPart_of_not_dvd (by norm_num)
    have ho2 : oddPart 6 = 3 := by simp [oddPart, hv]
    have h36 : Real.log 36 = 2 * Real.log 2 + 2 * Real.log 3 := by
      rw [show (36 : ℝ) = 4 * 9 by norm_num, Real.log_mul (by norm_num) (by norm_num), hl4, hl9]
    have hA := log_le_log_add (a := 35) (b := 36) (by norm_num) (by norm_num)
    have hB := log_le_log_add (a := 9) (b := 8) (by norm_num) (by norm_num)
    unfold alphaCore c2EvenSharp
    rw [ho1, ho2, hv, show PhiT 6 = -256 / 100 from rfl]
    simp only [cE]
    push_cast
    rw [h36] at hA
    rw [hl9, hl8] at hB
    norm_num at hA hB h2 ⊢
    linarith
  · -- q = 8
    have hv : padicValNat 2 8 = 3 := padicValNat_two_pow_mul_odd 3 1 (by norm_num) (by norm_num)
    have ho1 : oddPart (8 ^ 2 - 1) = 63 := oddPart_of_not_dvd (by norm_num)
    have ho2 : oddPart 8 = 1 := by simp [oddPart, hv]
    have hA : Real.log 63 < 6 * Real.log 2 := by
      rw [show 6 * Real.log 2 = Real.log ((2 : ℝ) ^ 6) by rw [Real.log_pow]; norm_num]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    unfold alphaCore c2EvenSharp
    rw [ho1, ho2, hv, show PhiT 8 = -272 / 100 from rfl]
    simp only [cE]
    push_cast
    norm_num at hA h2 ⊢
    linarith
  · -- q = 10
    have hv : padicValNat 2 10 = 1 := padicValNat_two_pow_mul_odd 1 5 (by norm_num) (by norm_num)
    have ho1 : oddPart (10 ^ 2 - 1) = 99 := oddPart_of_not_dvd (by norm_num)
    have ho2 : oddPart 10 = 5 := by simp [oddPart, hv]
    have hA : Real.log 99 < 2 * Real.log 2 + 2 * Real.log 5 := by
      rw [show 2 * Real.log 2 + 2 * Real.log 5 = Real.log ((2 : ℝ) ^ 2 * 5 ^ 2) by
        rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; norm_num]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    have hB := log_le_log_add (a := 5) (b := 4) (by norm_num) (by norm_num)
    unfold alphaCore c2EvenSharp
    rw [ho1, ho2, hv, show PhiT 10 = -285 / 100 from rfl]
    simp only [cE]
    push_cast
    rw [hl4] at hB
    norm_num at hA hB h2 ⊢
    linarith
  · -- q = 12
    have hv : padicValNat 2 12 = 2 := padicValNat_two_pow_mul_odd 2 3 (by norm_num) (by norm_num)
    have ho1 : oddPart (12 ^ 2 - 1) = 143 := oddPart_of_not_dvd (by norm_num)
    have ho2 : oddPart 12 = 3 := by simp [oddPart, hv]
    have hA : Real.log 143 < 4 * Real.log 2 + 2 * Real.log 3 := by
      rw [show 4 * Real.log 2 + 2 * Real.log 3 = Real.log ((2 : ℝ) ^ 4 * 3 ^ 2) by
        rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; norm_num]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    have hB : Real.log 3 < 2 * Real.log 2 := by
      rw [← hl4]; exact Real.log_lt_log (by norm_num) (by norm_num)
    unfold alphaCore c2EvenSharp
    rw [ho1, ho2, hv, show PhiT 12 = -295 / 100 from rfl]
    simp only [cE]
    push_cast
    norm_num at hA hB h2 ⊢
    linarith

end Q
end Chi2Irr
