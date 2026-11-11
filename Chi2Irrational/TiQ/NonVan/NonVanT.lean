/-
# Nonvanishing for Theorem T (RESULT §5: Lemma P at `Q = −q²`)

Copy of `Q/NonVan.lean` for the Ti machine. The three block determinants of `TiQ/NonVan/BlockMat.lean`, as rational
functions of `q` (derived with sympy and checked exactly at `q = 2, …, 15` in `scripts/tiq/nonvan_blocks.py`):
* `det M(S) = −8 q⁶ (9q² − 1) / (9 (q² + 1))`,
* `det M(L) = −8 q² (16200 q⁶ + 10575 q⁴ − 6352 q² − 905) / (2025 (q² + 1))`,
* `det M(D) = q⁴ (16200 q⁶ + 51075 q⁴ + 28523 q² − 420) / (135 (q² + 1)²)`.
Each is exactly the χ₂ determinant of `Q/NonVan.lean` at `q ↦ iq` (`q² ↦ −q²`), i.e. `B(·,3)` at `Q = −q²` up to the
units of RESULT §5. In the variable `Q = −x`, `x = q²`: `P_L(Q) = −(16200x³ + 10575x² − 6352x − 905)` and
`P_D(Q) = −(16200x³ + 51075x² + 28523x − 420)`, both `< 0` for `x ≥ 1` (RESULT §5, F5). So the numerators are nonzero
for every integer `q ≥ 2` and `nonvan_of` applies.
-/
import Chi2Irrational.TiQ.NonVan.NonVanQ

namespace Chi2Irr
namespace TiQ

open Polynomial Filter

lemma det_MS_q {q : ℕ} (hq : 2 ≤ q) :
    (MS q).det = ((-72 * (q : ℤ) ^ 8 + 8 * (q : ℤ) ^ 6 : ℤ) : ℚ) / ((9 * (q ^ 2 + 1) : ℕ) : ℚ) := by
  have hx : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hx1 : (q : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  have hw : (1 : ℚ) - -1 / (q : ℚ) ^ 2 = ((q : ℚ) ^ 2 + 1) / (q : ℚ) ^ 2 := by field_simp; ring
  rw [Matrix.det_fin_three]
  simp [MS, crr, wT, TqT, Finset.sum_range_succ]
  simp only [hw]
  field_simp
  ring

lemma det_ML_q {q : ℕ} (hq : 2 ≤ q) :
    (ML q).det = ((-129600 * (q : ℤ) ^ 8 - 84600 * (q : ℤ) ^ 6 + 50816 * (q : ℤ) ^ 4 + 7240 * (q : ℤ) ^ 2 : ℤ) : ℚ) /
      ((2025 * (q ^ 2 + 1) : ℕ) : ℚ) := by
  have hx : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hx1 : (q : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  have hw : (1 : ℚ) - -1 / (q : ℚ) ^ 2 = ((q : ℚ) ^ 2 + 1) / (q : ℚ) ^ 2 := by field_simp; ring
  rw [Matrix.det_fin_three]
  simp [ML, crr, wT, TqT, Finset.sum_range_succ]
  simp only [hw]
  field_simp
  ring

lemma det_MD_q {q : ℕ} (hq : 2 ≤ q) :
    (MD q).det = ((16200 * (q : ℤ) ^ 10 + 51075 * (q : ℤ) ^ 8 + 28523 * (q : ℤ) ^ 6 - 420 * (q : ℤ) ^ 4 : ℤ) : ℚ) /
      ((135 * (q ^ 2 + 1) ^ 2 : ℕ) : ℚ) := by
  have hx : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hx1 : (q : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  have hw : (1 : ℚ) - -1 / (q : ℚ) ^ 2 = ((q : ℚ) ^ 2 + 1) / (q : ℚ) ^ 2 := by field_simp; ring
  rw [Matrix.det_fin_three]
  simp [MD, crr, wT, TqT, eD, Finset.sum_range_succ]
  simp only [hw]
  field_simp
  ring

/-! ### The numerators are nonzero for `q ≥ 2` -/

lemma numS_ne {q : ℕ} (hq : 2 ≤ q) : (-72 * (q : ℤ) ^ 8 + 8 * (q : ℤ) ^ 6 : ℤ) ≠ 0 := by
  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set y : ℤ := (q : ℤ) ^ 2 with hy
  have hy4 : 4 ≤ y := by rw [hy]; nlinarith
  have e : -72 * (q : ℤ) ^ 8 + 8 * (q : ℤ) ^ 6 = -(8 * y ^ 3 * (9 * y - 1)) := by rw [hy]; ring
  rw [e, neg_ne_zero]
  have : 0 < 8 * y ^ 3 * (9 * y - 1) := by
    have : 0 < 9 * y - 1 := by linarith
    positivity
  exact this.ne'

lemma numL_ne {q : ℕ} (hq : 2 ≤ q) :
    (-129600 * (q : ℤ) ^ 8 - 84600 * (q : ℤ) ^ 6 + 50816 * (q : ℤ) ^ 4 + 7240 * (q : ℤ) ^ 2 : ℤ) ≠ 0 := by
  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set y : ℤ := (q : ℤ) ^ 2 with hy
  have hy4 : 4 ≤ y := by rw [hy]; nlinarith
  have e : -129600 * (q : ℤ) ^ 8 - 84600 * (q : ℤ) ^ 6 + 50816 * (q : ℤ) ^ 4 + 7240 * (q : ℤ) ^ 2 =
      -(8 * y * (16200 * y ^ 3 + 10575 * y ^ 2 - 6352 * y - 905)) := by rw [hy]; ring
  rw [e, neg_ne_zero]
  have hpos : 0 < 16200 * y ^ 3 + 10575 * y ^ 2 - 6352 * y - 905 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ y - 4) (by nlinarith : (0:ℤ) ≤ y ^ 2)]
  have : 0 < 8 * y * (16200 * y ^ 3 + 10575 * y ^ 2 - 6352 * y - 905) := by positivity
  exact this.ne'

lemma numD_ne {q : ℕ} (hq : 2 ≤ q) :
    (16200 * (q : ℤ) ^ 10 + 51075 * (q : ℤ) ^ 8 + 28523 * (q : ℤ) ^ 6 - 420 * (q : ℤ) ^ 4 : ℤ) ≠ 0 := by
  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set y : ℤ := (q : ℤ) ^ 2 with hy
  have hy4 : 4 ≤ y := by rw [hy]; nlinarith
  have e : 16200 * (q : ℤ) ^ 10 + 51075 * (q : ℤ) ^ 8 + 28523 * (q : ℤ) ^ 6 - 420 * (q : ℤ) ^ 4 =
      y ^ 2 * (16200 * y ^ 3 + 51075 * y ^ 2 + 28523 * y - 420) := by rw [hy]; ring
  rw [e]
  have hpos : 0 < 16200 * y ^ 3 + 51075 * y ^ 2 + 28523 * y - 420 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ y - 4) (by nlinarith : (0:ℤ) ≤ y ^ 2)]
  have : 0 < y ^ 2 * (16200 * y ^ 3 + 51075 * y ^ 2 + 28523 * y - 420) := by positivity
  exact this.ne'

/-- **Nonvanishing for Theorem T** (RESULT §5): the exact statement of the stub `nonvan_t` of `TiQ/Interface.lean`. -/
theorem nonvan_t_proof (q : ℕ) (hq : 3 ≤ q) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, (DeltaT q h).eval ((a : ℚ) / b) ≠ 0 := by
  have hq2 : 2 ≤ q := by omega
  exact nonvan_of hq2 (det_MS_q hq2) (det_ML_q hq2) (det_MD_q hq2) (numS_ne hq2) (numL_ne hq2) (numD_ne hq2)
    (by positivity) (by positivity) (by positivity) a b hb

end TiQ
end Chi2Irr
