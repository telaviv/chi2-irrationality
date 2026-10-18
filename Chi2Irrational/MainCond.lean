/-
# The main theorem, conditional on the three analytic/arithmetic inputs

`MachineBounds q` packages the three inputs about `Δ_h = Delta q h`:
* `den`: positive rationals with `den h • Δ_h ∈ ℤ[X]` and `log den h ≤ (α + ε) h²` eventually (the arithmetic
  bound: class bound, Lemmas 4′, 5, 9, 10 and the prime number theorem);
* `analytic`: `|Δ_h(χ₂(1/q))| ≤ exp((β + ε) h²)` eventually (Theorem B with a dual certificate);
* `margin`: `α + β < 0`;
* `nonvan`: for each `a/b`, `Δ_h(a/b) ≠ 0` for infinitely many `h` (Lemma P, along `h = 3ℓ`).
The fields are supplied for `q = 3, 5` in `Arith/Assembly.lean`.
`irrational_of_bounds` turns these into `Irrational (chi2 (1/q))` via Lemma E.
-/
import Chi2Irrational.Defs
import Chi2Irrational.Criterion
import Chi2Irrational.Machine

namespace Chi2Irr

open Polynomial Filter Topology

/-- The inputs to the endgame for the `χ₂(1/q)` machine. -/
structure MachineBounds (q : ℕ) where
  /-- a common denominator of the coefficients of `Δ_h` -/
  den : ℕ → ℚ
  den_pos : ∀ h, 0 < den h
  den_int : ∀ h k, ∃ z : ℤ, den h * (Delta q h).coeff k = z
  /-- the arithmetic constant (per `h²`) -/
  α : ℝ
  /-- the analytic constant (per `h²`) -/
  β : ℝ
  margin : α + β < 0
  arith : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (α + ε) * (h : ℝ) ^ 2
  analytic : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ Real.exp ((β + ε) * (h : ℝ) ^ 2)
  nonvan : ∀ (a : ℤ) (b : ℕ), 0 < b → ∃ᶠ h : ℕ in atTop, (Delta q h).eval ((a : ℚ) / b) ≠ 0

/-- **Main theorem, conditional form.** -/
theorem irrational_of_bounds {q : ℕ} (H : MachineBounds q) : Irrational (chi2 (1 / (q : ℝ))) := by
  set c : ℝ := -(H.α + H.β) / 2 with hc_def
  have hc : 0 < c := by have := H.margin; rw [hc_def]; linarith
  have hε : 0 < c / 2 := by linarith
  refine irrational_of_poly_approx _ (Delta q) (natDegree_Delta_le q) H.den H.den_pos H.den_int c hc ?_
    H.nonvan
  filter_upwards [H.arith (c / 2) hε, H.analytic (c / 2) hε] with h ha hb
  have hd : (0 : ℝ) < ((H.den h : ℚ) : ℝ) := by exact_mod_cast H.den_pos h
  calc ((H.den h : ℚ) : ℝ) * |aeval (chi2 (1 / (q : ℝ))) (Delta q h)|
      ≤ Real.exp ((H.α + c / 2) * (h : ℝ) ^ 2) * Real.exp ((H.β + c / 2) * (h : ℝ) ^ 2) := by
        gcongr
        rw [← Real.exp_log hd]
        exact Real.exp_le_exp.mpr ha
    _ = Real.exp (-c * (h : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        rw [hc_def]
        ring

end Chi2Irr
