/-
# Theorem Q: χ₂(1/q) for every integer q ≥ 3 outside {4, 6, 8, 10, 12} — statement and constants

Source: `../handoff/log2log3/pilot_q/RESULT.md` (Theorem Q, odd q ≥ 3; Theorem Q_even, even q ≥ 14; one AI gate referee,
`pilot_q/referee/REFEREE_Q.md`, PASS WITH FIXES). The machine (`Machine.lean`, `PoleExpansion.lean`, `MainCond.lean`) and
Theorem B (`Analytic/TheoremB.lean`, given a `DualCert q`) are already generic in `q`; the files of `Chi2Irrational/Q/*`
supply the `q`-general ingredients, and `Q/Interface.lean` assembles them.

Constants (per `h²`), for `q ≥ 3`:
* `alphaCore q = 133/60 + ¼ log(odd part of q² − 1) − ⅓ log(odd part of q)`: generic odd primes (Theorem A), odd
  `p ∣ q² − 1` (Lemma 5 + Corollary 9.1), odd `p ∣ q` (Lemma 4′(ii), prime by prime);
* `c2Odd q = (ν − 2)/4 · log 2`, `ν = v₂(q² − 1) ≥ 3` (Lemma 10, general ν), for odd `q`;
* `c2Even q = (½ − v₂(q)/3) · log 2` (Lemma 10₀, which includes the 2-adic share of Lemma 4′), for even `q`;
* `betaOdd q = −2.078 − ½ log(q/3)`: Theorem B from the `q = 3` certificate (`Cert/Q3.lean`, `Φ < −2.078`) moved by the
  shift lemma (density cap 2, so the gain is `L/4 = ½ log(q/q₀)` with `L = log(w/w′) = 2 log(q/q₀)`);
* `betaEven q = −3.03 − ½ log(q/14)`: from a certificate at `q = 14` with `Φ ≤ −3.03` (the referee's float-free one gives
  `−3.0444`), moved by the shift lemma.
Margins with these constants (Arb, scratch scan to `q = 20000`): odd worst at `q = 3` (`−0.05425`), even worst at
`q = 14` (`−0.0282`); both margins decrease in `q`.
-/
import Chi2Irrational.MainCond

namespace Chi2Irr
namespace Q

/-- **Theorem Q** (with Q_even): `χ₂(1/q)` is irrational for every integer `q ≥ 3` outside `{4, 6, 8, 10, 12}`. -/
def TheoremQ : Prop :=
  ∀ q : ℕ, 3 ≤ q → q ∉ ({4, 6, 8, 10, 12} : Finset ℕ) → Irrational (chi2 (1 / (q : ℝ)))

/-- The odd part of `n` (`n / 2^{v₂(n)}`). -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ padicValNat 2 n

/-- The arithmetic constant without the prime `2`. -/
noncomputable def alphaCore (q : ℕ) : ℝ :=
  133 / 60 + Real.log (oddPart (q ^ 2 - 1)) / 4 - Real.log (oddPart q) / 3

/-- The 2-adic constant at odd `q` (Lemma 10, `ν = v₂(q² − 1)`). -/
noncomputable def c2Odd (q : ℕ) : ℝ := ((padicValNat 2 (q ^ 2 - 1) : ℝ) - 2) / 4 * Real.log 2

/-- The 2-adic constant at even `q` (Lemma 10₀). -/
noncomputable def c2Even (q : ℕ) : ℝ := (1 / 2 - (padicValNat 2 q : ℝ) / 3) * Real.log 2

/-- The analytic constant at odd `q`: the `q = 3` certificate, shifted. -/
noncomputable def betaOdd (q : ℕ) : ℝ := -2078 / 1000 - Real.log ((q : ℝ) / 3) / 2

/-- The analytic constant at even `q ≥ 14`: a `q = 14` certificate with `Φ ≤ −3.03`, shifted. -/
noncomputable def betaEven (q : ℕ) : ℝ := -303 / 100 - Real.log ((q : ℝ) / 14) / 2

end Q
end Chi2Irr
