/-
# Theorem T: Ti₂(1/q) ∉ ℚ for every integer q ≥ 6 — statement and constants

Source: `../handoff/log2log3/pilot_ti2q/RESULT.md` (Theorem T; one AI gate referee, `pilot_ti2q/referee/REFEREE_TI2Q.md`,
PASS WITH FIXES, fixes applied). Copy of the layout of `Q/Defs.lean` and `Q/Even/Defs.lean`.

`Ti₂(z) = Σ_{n ≥ 0} (−1)ⁿ z^{2n+1}/(2n+1)²` (inverse tangent integral). The machine is the Theorem Q machine with the
signed weight `w = −q⁻²` (`TiQ/Machine.lean`).

Constants (per `h²`), for `q ≥ 3` (RESULT §2, "Arithmetic constants"):
* `alphaCoreT q = 133/60 + ¼ log(odd part of q² + 1) − ⅓ log(odd part of q)`: generic odd primes (Theorem A), odd
  `p ∣ q² + 1` (Lemma 5 + Corollary 9.1, pole at `q² = −1`), odd `p ∣ q` (Lemma 4′(ii));
* `c2TiOdd = ¼ log 2` (Lemma 10₁, `ν = v₂(q² + 1) = 1`), for odd `q`;
* even `q`: `Q.c2EvenSharp q = (c(e) − e/3) log 2` (Lemma 10_e, `e = v₂(q)`, unchanged for Ti);
* analytic: one certificate at `q = 6` (Lean format, `L = 800`, RESULT §6 / §11 "Lean constants check") with
  `Φ ≤ PhiT6 = −2.5671`, moved to every `q ≥ 6` by the shift lemma: `betaT q = PhiT6 − ½ log(q/6)`.
  Departure from RESULT §0: RESULT uses the `q = 5`, `14` and other even certificates for `q ≥ 7`; with the Lean
  constants the single `q = 6` certificate covers all `q ≥ 6` (margins ≤ −0.0029 at `q = 6`, ≤ −0.098 for `q ≥ 7`).
-/
import Chi2Irrational.Q.Even.Defs

namespace Chi2Irr
namespace TiQ

/-- The `n`-th term of the inverse tangent integral `Ti₂`. -/
noncomputable def ti2Term (z : ℝ) (n : ℕ) : ℝ := (-1) ^ n * z ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2

/-- The inverse tangent integral `Ti₂(z) = Σ_{n ≥ 0} (−1)ⁿ z^{2n+1}/(2n+1)²`. -/
noncomputable def ti2 (z : ℝ) : ℝ := ∑' n : ℕ, ti2Term z n

lemma abs_ti2Term_eq (z : ℝ) (n : ℕ) : |ti2Term z n| = |chi2Term z n| := by
  unfold ti2Term chi2Term
  rw [mul_div_assoc, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The series defining `Ti₂(z)` converges absolutely for `|z| ≤ 1`, so `ti2 z` is its genuine sum. -/
lemma summable_ti2Term {z : ℝ} (hz : |z| ≤ 1) : Summable (ti2Term z) := by
  refine Summable.of_norm ?_
  simp only [Real.norm_eq_abs, abs_ti2Term_eq]
  exact (summable_chi2Term hz).abs

/-- **Theorem T**: `Ti₂(1/q)` is irrational for every integer `q ≥ 6`. -/
def TheoremT : Prop := ∀ q : ℕ, 6 ≤ q → Irrational (ti2 (1 / (q : ℝ)))

/-- The arithmetic constant without the prime `2`. -/
noncomputable def alphaCoreT (q : ℕ) : ℝ :=
  133 / 60 + Real.log (Q.oddPart (q ^ 2 + 1)) / 4 - Real.log (Q.oddPart q) / 3

/-- The 2-adic constant at odd `q` (Lemma 10₁, `ν = v₂(q² + 1) = 1`). -/
noncomputable def c2TiOdd : ℝ := Real.log 2 / 4

/-- The target exponent of the `q = 6` certificate (`L = 800`; certified `Φ = −2.5671799991…`). -/
def PhiT6 : ℚ := -25671 / 10000

/-- The analytic constant at `q ≥ 6`: the `q = 6` certificate, shifted. -/
noncomputable def betaT (q : ℕ) : ℝ := (PhiT6 : ℝ) - Real.log ((q : ℝ) / 6) / 2

end TiQ
end Chi2Irr
