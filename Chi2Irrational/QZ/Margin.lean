/-
# Theorem Q4′: the margin `alphaZ q + c2Num + betaZ q < 0` (`pilot_chi2_2q/RESULT.md` §4)

With `qB = 175`, `PhiB = −4.003` and `log(q² − 4) < 2 log q`:
`alphaZ q + c2Num + betaZ q < 133/60 + (4/3) log 2 + PhiB + ½ log qB − ⅓ log q ≤ 133/60 + (4/3) log 2 + PhiB + ⅙ log 175`
for `q ≥ 175`. Then `175^104 < 2^775` (so `log 175 < (775/104) log 2`) and `log 2 < 0.6931471808` give
`< 133/60 − 4.003 + (4/3 + 775/624)·0.6931471808 ≈ −0.00126`.
(RESULT's Arb margin at the paper's base `q = 173` is `−0.0008`; Lean's certificate format is weaker, so the base moves
to `q = 175` (certificate grid `L = 1200`).) Numerical check: `scripts/q2num/margin_check.py`.
-/
import Chi2Irrational.QZ.Defs
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Chi2Irr
namespace QZ

set_option exponentiation.threshold 2048 in
lemma log175_lt : 104 * Real.log 175 < 775 * Real.log 2 := by
  have hN : (175 : ℕ) ^ 104 < 2 ^ 775 := by norm_num
  have h : (175 : ℝ) ^ 104 < 2 ^ 775 := by exact_mod_cast hN
  have := Real.log_lt_log (by positivity) h
  rwa [Real.log_pow, Real.log_pow] at this

/-- **Margin** (the exact statement of `margin_z`, `QZ/Interface.lean`). -/
theorem margin_z_proof (q : ℕ) (hq : qB ≤ q) (_ho : Odd q) : alphaZ q + c2Num + betaZ q < 0 := by
  have hq' : (175 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  unfold alphaZ c2Num betaZ PhiB qB
  have h1 : Real.log ((q : ℝ) ^ 2 - 4) < 2 * Real.log q := by
    rw [show 2 * Real.log q = Real.log ((q : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_lt_log (by nlinarith) (by linarith)
  have h2 : Real.log ((q : ℝ) / 175) = Real.log q - Real.log 175 := Real.log_div hq0.ne' (by norm_num)
  have h3 : Real.log 175 ≤ Real.log q := Real.log_le_log (by norm_num) hq'
  have h4 := log175_lt
  have h5 := Real.log_two_lt_d9
  push_cast
  rw [h2]
  linarith

end QZ
end Chi2Irr
