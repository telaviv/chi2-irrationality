/-
# Theorem Q4′ (numerator 2): χ₂(2/q) for every odd q ≥ q₀ — statement and constants

Source: `../handoff/log2log3/pilot_chi2_2q/RESULT.md` (Theorem Q4, odd `q ≥ 173` on paper; one AI gate referee,
`pilot_chi2_2q/referee/REFEREE_CHI2_2Q.md`, PASS WITH FIXES). RESULT §1: the machine at `z = 2/q` is the `χ₂(1/q)`
machine at the rational point `ζ = q/2` (`QZ/Machine.lean`, `DeltaZ`).

Constants (per `h²`), for odd `q ≥ 5`:
* `alphaZ q = 133/60 + ¼ log(q² − 4) − ⅓ log q`: generic odd primes (Theorem A), odd `p ∣ q² − 4` (Lemma 5 +
  Corollary 9.1 at `ζ₀ = q/2 ∈ ℤ_(p)`, `v_p(ζ₀² − 1) = v_p(q² − 4)`), odd `p ∣ q` (Lemma 4′(ii), `v_p(ζ₀) = v_p(q)`);
  `q² − 4` and `q` are odd;
* `c2Num = (4/3) log 2`: Lemma 10″ (RESULT §2), the prime `2` with numerator `2`;
* `betaZ q = PhiB − ½ log(q/qB)`: Theorem B from a kernel-checked certificate at `w = 4/qB²` (`Φ ≤ PhiB`), moved to
  `w = 4/q²` by the shift lemma (gain `L/4 = ½ log(q/qB)`, `L = log(w_B/w) = 2 log(q/qB)`).
-/
import Chi2Irrational.QZ.Machine

namespace Chi2Irr
namespace QZ

/-- The rational point `ζ = q/2` (so `z = 1/ζ = 2/q`). -/
def zq (q : ℕ) : ℚ := (q : ℚ) / 2

/-- The arithmetic constant without the prime `2` (odd `q`). -/
noncomputable def alphaZ (q : ℕ) : ℝ := 133 / 60 + Real.log ((q : ℝ) ^ 2 - 4) / 4 - Real.log q / 3

/-- The 2-adic constant of Lemma 10″. -/
noncomputable def c2Num : ℝ := 4 / 3 * Real.log 2

/-- The base point of the certificate: `w = 4/qB²`. -/
def qB : ℕ := 175

/-- The certified exponent at the base point (a rational upper bound for the certificate's `Φ`). -/
def PhiB : ℚ := -4003 / 1000

/-- The analytic constant at `q ≥ qB`: the base certificate, shifted. -/
noncomputable def betaZ (q : ℕ) : ℝ := (PhiB : ℝ) - Real.log ((q : ℝ) / qB) / 2

end QZ
end Chi2Irr
