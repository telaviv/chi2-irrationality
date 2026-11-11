/-
# The endgame at a rational point `ζ` (copy of `MainCond.lean` for `DeltaZ ζ`)

`MachineBoundsZ ζ` packages the inputs about `Δ_h = DeltaZ ζ h` (denominator, analytic bound at `χ₂(1/ζ)`, margin,
nonvanishing); `irrational_of_boundsZ` turns them into `Irrational (chi2 (1/ζ))` via Lemma E
(`irrational_of_poly_approx`, `Criterion.lean`).
-/
import Chi2Irrational.Defs
import Chi2Irrational.Criterion
import Chi2Irrational.QZ.Machine

namespace Chi2Irr
namespace QZ

open Polynomial Filter Topology

/-- The inputs to the endgame for the `χ₂(1/ζ)` machine. -/
structure MachineBoundsZ (ζ : ℚ) where
  /-- a common denominator of the coefficients of `Δ_h` -/
  den : ℕ → ℚ
  den_pos : ∀ h, 0 < den h
  den_int : ∀ h k, ∃ z : ℤ, den h * (DeltaZ ζ h).coeff k = z
  /-- the arithmetic constant (per `h²`) -/
  α : ℝ
  /-- the analytic constant (per `h²`) -/
  β : ℝ
  margin : α + β < 0
  arith : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (α + ε) * (h : ℝ) ^ 2
  analytic : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / (ζ : ℝ))) (DeltaZ ζ h)| ≤ Real.exp ((β + ε) * (h : ℝ) ^ 2)
  nonvan : ∀ (a : ℤ) (b : ℕ), 0 < b → ∃ᶠ h : ℕ in atTop, (DeltaZ ζ h).eval ((a : ℚ) / b) ≠ 0

/-- **Main theorem at `ζ`, conditional form.** -/
theorem irrational_of_boundsZ {ζ : ℚ} (H : MachineBoundsZ ζ) : Irrational (chi2 (1 / (ζ : ℝ))) := by
  set c : ℝ := -(H.α + H.β) / 2 with hc_def
  have hc : 0 < c := by have := H.margin; rw [hc_def]; linarith
  have hε : 0 < c / 2 := by linarith
  refine irrational_of_poly_approx _ (DeltaZ ζ) (natDegree_DeltaZ_le ζ) H.den H.den_pos H.den_int c hc ?_
    H.nonvan
  filter_upwards [H.arith (c / 2) hε, H.analytic (c / 2) hε] with h ha hb
  have hd : (0 : ℝ) < ((H.den h : ℚ) : ℝ) := by exact_mod_cast H.den_pos h
  calc ((H.den h : ℚ) : ℝ) * |aeval (chi2 (1 / (ζ : ℝ))) (DeltaZ ζ h)|
      ≤ Real.exp ((H.α + c / 2) * (h : ℝ) ^ 2) * Real.exp ((H.β + c / 2) * (h : ℝ) ^ 2) := by
        gcongr
        rw [← Real.exp_log hd]
        exact Real.exp_le_exp.mpr ha
    _ = Real.exp (-c * (h : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        rw [hc_def]
        ring

end QZ
end Chi2Irr
