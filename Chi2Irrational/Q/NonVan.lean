/-
# Nonvanishing for general `q` (Theorem Q, RESULT §3)

The three block determinants of `NonVan/BlockMat.lean`, as rational functions of `q` (for `q ≥ 2`; derived and checked
at `q = 3, …, 15` in `scripts/q/nonvan_closed.py`):
* `det M(S) = 8 q⁶ (9q² + 1) / (9 (q² − 1))`,
* `det M(L) = 8 q² (16200 q⁶ − 10575 q⁴ − 6352 q² + 905) / (2025 (q² − 1))`,
* `det M(D) = −q⁴ (16200 q⁶ − 51075 q⁴ + 28523 q² + 420) / (135 (q² − 1)²)`.
(Against RESULT §3 / `pilot_q/check_Bclosed.py`: `det M(S) = q³ B(S,3)`, `det M(L) = q³ B(L,3)`, `det M(D) = B(D,3)`.) The numerators are nonzero for every integer
`q ≥ 2`, so `nonvan_of` applies.
-/
import Chi2Irrational.Q.Defs
import Chi2Irrational.NonVan.NonVanQ

namespace Chi2Irr
namespace Q

open Polynomial Filter

lemma det_MS_q {q : ℕ} (hq : 2 ≤ q) :
    (MS q).det = ((72 * (q : ℤ) ^ 8 + 8 * (q : ℤ) ^ 6 : ℤ) : ℚ) / ((9 * (q ^ 2 - 1) : ℕ) : ℚ) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hx : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hx1 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (4 : ℚ) ≤ (q : ℚ) ^ 2 := by
      have : (2 : ℚ) ≤ q := by exact_mod_cast hq
      nlinarith
    linarith
  rw [Matrix.det_fin_three]
  simp [MS, crr, wt, Tq, Finset.sum_range_succ, Nat.cast_sub h1]
  field_simp
  ring

lemma det_ML_q {q : ℕ} (hq : 2 ≤ q) :
    (ML q).det = ((129600 * (q : ℤ) ^ 8 - 84600 * (q : ℤ) ^ 6 - 50816 * (q : ℤ) ^ 4 + 7240 * (q : ℤ) ^ 2 : ℤ) : ℚ) /
      ((2025 * (q ^ 2 - 1) : ℕ) : ℚ) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hx : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hx1 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (4 : ℚ) ≤ (q : ℚ) ^ 2 := by
      have : (2 : ℚ) ≤ q := by exact_mod_cast hq
      nlinarith
    linarith
  rw [Matrix.det_fin_three]
  simp [ML, crr, wt, Tq, Finset.sum_range_succ, Nat.cast_sub h1]
  field_simp
  ring

lemma det_MD_q {q : ℕ} (hq : 2 ≤ q) :
    (MD q).det = ((-16200 * (q : ℤ) ^ 10 + 51075 * (q : ℤ) ^ 8 - 28523 * (q : ℤ) ^ 6 - 420 * (q : ℤ) ^ 4 : ℤ) : ℚ) /
      ((135 * (q ^ 2 - 1) ^ 2 : ℕ) : ℚ) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hx : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hx1 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (4 : ℚ) ≤ (q : ℚ) ^ 2 := by
      have : (2 : ℚ) ≤ q := by exact_mod_cast hq
      nlinarith
    linarith
  rw [Matrix.det_fin_three]
  simp [MD, crr, wt, Tq, eD, Finset.sum_range_succ, Nat.cast_sub h1]
  field_simp
  ring

/-! ### The numerators are nonzero for `q ≥ 2` -/

lemma numS_ne {q : ℕ} (hq : 2 ≤ q) : (72 * (q : ℤ) ^ 8 + 8 * (q : ℤ) ^ 6 : ℤ) ≠ 0 := by
  have : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  positivity

lemma numL_ne {q : ℕ} (hq : 2 ≤ q) :
    (129600 * (q : ℤ) ^ 8 - 84600 * (q : ℤ) ^ 6 - 50816 * (q : ℤ) ^ 4 + 7240 * (q : ℤ) ^ 2 : ℤ) ≠ 0 := by
  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set y : ℤ := (q : ℤ) ^ 2 with hy
  have hy4 : 4 ≤ y := by rw [hy]; nlinarith
  have e : 129600 * (q : ℤ) ^ 8 - 84600 * (q : ℤ) ^ 6 - 50816 * (q : ℤ) ^ 4 + 7240 * (q : ℤ) ^ 2 =
      8 * y * (16200 * y ^ 3 - 10575 * y ^ 2 - 6352 * y + 905) := by rw [hy]; ring
  rw [e]
  have hpos : 0 < 16200 * y ^ 3 - 10575 * y ^ 2 - 6352 * y + 905 := by nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ y - 4) (by nlinarith : (0:ℤ) ≤ y ^ 2)]
  have : 0 < 8 * y * (16200 * y ^ 3 - 10575 * y ^ 2 - 6352 * y + 905) := by positivity
  exact this.ne'

lemma numD_ne {q : ℕ} (hq : 2 ≤ q) :
    (-16200 * (q : ℤ) ^ 10 + 51075 * (q : ℤ) ^ 8 - 28523 * (q : ℤ) ^ 6 - 420 * (q : ℤ) ^ 4 : ℤ) ≠ 0 := by
  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set y : ℤ := (q : ℤ) ^ 2 with hy
  have hy4 : 4 ≤ y := by rw [hy]; nlinarith
  have e : -16200 * (q : ℤ) ^ 10 + 51075 * (q : ℤ) ^ 8 - 28523 * (q : ℤ) ^ 6 - 420 * (q : ℤ) ^ 4 =
      -(y ^ 2 * (16200 * y ^ 3 - 51075 * y ^ 2 + 28523 * y + 420)) := by rw [hy]; ring
  rw [e, neg_ne_zero]
  have hpos : 0 < 16200 * y ^ 3 - 51075 * y ^ 2 + 28523 * y + 420 := by nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ y - 4) (by nlinarith : (0:ℤ) ≤ y ^ 2)]
  have : 0 < y ^ 2 * (16200 * y ^ 3 - 51075 * y ^ 2 + 28523 * y + 420) := by positivity
  exact this.ne'

/-- **Nonvanishing for general `q`** (RESULT §3): the exact statement of the stub `nonvan_q` of `Q/Interface.lean`. -/
theorem nonvan_q_proof (q : ℕ) (hq : 3 ≤ q) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, (Delta q h).eval ((a : ℚ) / b) ≠ 0 := by
  have hq2 : 2 ≤ q := by omega
  have h1 : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith)
  exact nonvan_of hq2 (det_MS_q hq2) (det_ML_q hq2) (det_MD_q hq2) (numS_ne hq2) (numL_ne hq2) (numD_ne hq2)
    (by positivity) (by positivity) (by positivity) a b hb

end Q
end Chi2Irr
