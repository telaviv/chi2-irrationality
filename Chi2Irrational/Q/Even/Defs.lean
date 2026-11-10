/-
# Theorem Q₄: χ₂(1/q) for every integer q ≥ 3 except possibly q = 4 — statement and constants

Source: `../handoff/log2log3/pilot_qeven/RESULT.md` (Lemma 10_e; gate referee `pilot_qeven/referee/REFEREE_QEVEN.md`,
PASS WITH FIXES, no errors). It extends Theorem Q (`Q/Defs.lean`, `q ∉ {4, 6, 8, 10, 12}`) by q = 6, 8, 10, 12.

**Lemma 10_e** (weighted Gauss valuation `v_e(q) = e = v₂(q₀)` on Lemma 4′'s slot Cauchy–Binet expansion): at even `q₀`,
`n₂(Δ_h) ≤ −a(h)·e + c(e)·h² + O(h log h)` with `c(e) = (6 − 4e)/(3(3e + 8))` (`2/33` for `e = 1`, negative for `e ≥ 2`),
in place of Lemma 10₀'s `½`. So the even 2-adic constant becomes `c2EvenSharp q = (c(e) − e/3)·log 2`.

Analytic constants: direct certificates at `q = 6, 8, 10, 12` (Lean format, `Cert/Q{6,8,10,12}.lean`) with `Φ ≤ PhiT q`.
The targets `PhiT` are set a little above what the Lean generator reaches at `L = 200` for q = 8, 10, 12, and at a finer
grid for q = 6 (float-free certified values, `pilot_qeven/CERTS.md`: −2.570438, −2.741829, −2.869418, −2.971024).
Margins `alphaCore q + c2EvenSharp q + PhiT q` (scratch, Arb): −0.0097 (q = 6), −0.242 (8), −0.209 (10), −0.354 (12).
-/
import Chi2Irrational.Q.Defs

namespace Chi2Irr
namespace Q

/-- **Theorem Q₄**: `χ₂(1/q)` is irrational for every integer `q ≥ 3`, `q ≠ 4`. -/
def TheoremQ4 : Prop := ∀ q : ℕ, 3 ≤ q → q ≠ 4 → Irrational (chi2 (1 / (q : ℝ)))

/-- Lemma 10_e's constant `c(e) = (6 − 4e)/(3(3e + 8))`. -/
def cE (e : ℕ) : ℚ := (6 - 4 * (e : ℚ)) / (3 * (3 * (e : ℚ) + 8))

/-- The sharp even 2-adic constant `(c(e) − e/3) · log 2`, `e = v₂(q)`. -/
noncomputable def c2EvenSharp (q : ℕ) : ℝ :=
  (((cE (padicValNat 2 q) : ℚ) : ℝ) - (padicValNat 2 q : ℝ) / 3) * Real.log 2

/-- The target certified exponents at `q = 6, 8, 10, 12` (`0` elsewhere; unused). -/
def PhiT : ℕ → ℚ
  | 6 => -256 / 100
  | 8 => -272 / 100
  | 10 => -285 / 100
  | 12 => -295 / 100
  | _ => 0

/-- The four new traces. -/
def newQ : Finset ℕ := {6, 8, 10, 12}

end Q
end Chi2Irr
