/-
# The main theorem for Ti₂, conditional on the analytic/arithmetic inputs

Copy of `MainCond.lean` with `ti2` and `DeltaT` in place of `chi2` and `Delta`.
-/
import Chi2Irrational.TiQ.Defs
import Chi2Irrational.TiQ.Machine
import Chi2Irrational.Criterion

namespace Chi2Irr
namespace TiQ

open Polynomial Filter Topology

/-- The inputs to the endgame for the `Ti₂(1/q)` machine. -/
structure MachineBoundsT (q : ℕ) where
  /-- a common denominator of the coefficients of `Δ^Ti_h` -/
  den : ℕ → ℚ
  den_pos : ∀ h, 0 < den h
  den_int : ∀ h k, ∃ z : ℤ, den h * (DeltaT q h).coeff k = z
  /-- the arithmetic constant (per `h²`) -/
  α : ℝ
  /-- the analytic constant (per `h²`) -/
  β : ℝ
  margin : α + β < 0
  arith : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (α + ε) * (h : ℝ) ^ 2
  analytic : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)| ≤ Real.exp ((β + ε) * (h : ℝ) ^ 2)
  nonvan : ∀ (a : ℤ) (b : ℕ), 0 < b → ∃ᶠ h : ℕ in atTop, (DeltaT q h).eval ((a : ℚ) / b) ≠ 0

/-- **Main theorem for Ti₂, conditional form.** -/
theorem irrational_of_boundsT {q : ℕ} (H : MachineBoundsT q) : Irrational (ti2 (1 / (q : ℝ))) := by
  set c : ℝ := -(H.α + H.β) / 2 with hc_def
  have hc : 0 < c := by have := H.margin; rw [hc_def]; linarith
  have hε : 0 < c / 2 := by linarith
  refine irrational_of_poly_approx _ (DeltaT q) (natDegree_DeltaT_le q) H.den H.den_pos H.den_int c hc ?_
    H.nonvan
  filter_upwards [H.arith (c / 2) hε, H.analytic (c / 2) hε] with h ha hb
  have hd : (0 : ℝ) < ((H.den h : ℚ) : ℝ) := by exact_mod_cast H.den_pos h
  calc ((H.den h : ℚ) : ℝ) * |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)|
      ≤ Real.exp ((H.α + c / 2) * (h : ℝ) ^ 2) * Real.exp ((H.β + c / 2) * (h : ℝ) ^ 2) := by
        gcongr
        rw [← Real.exp_log hd]
        exact Real.exp_le_exp.mpr ha
    _ = Real.exp (-c * (h : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        rw [hc_def]
        ring

end TiQ
end Chi2Irr
