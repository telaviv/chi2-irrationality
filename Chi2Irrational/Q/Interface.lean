/-
# Theorem Q: the ingredients and the assembly (`pilot_q/RESULT.md`)

The ingredients below are stated for general `q`; each is proved as `<name>_proof` in its own file under
`Chi2Irrational/Q/`. The assembly (`theoremQ`) feeds them to `MachineBounds q` and `irrational_of_bounds`.

| ingredient | RESULT | statement |
|---|---|---|
| `arith_q` | §1, §4 | from a 2-adic bound `(n₂, c₂)`: a denominator with `log den ≤ (alphaCore q + c₂ + ε) h²` |
| `twoAdic_odd` | §1 (Lemma 10, general ν) | odd `q`: a 2-adic bound with `c₂ = c2Odd q` |
| `twoAdic_even` | §4.1 (Lemma 10₀) | even `q`: a 2-adic bound with `c₂ = c2Even q` |
| `nonvan_q` | §3 (Lemma P along `h = 3ℓ`) | `Δ_h(a/b) ≠ 0` for infinitely many `h` |
| `analytic_odd` | §2 (shift lemma from `q = 3`) | `|Δ_h(χ₂(1/q))| ≤ exp((betaOdd q + δ + ε) h²)` eventually |
| `analytic_even` | §4.2 (certificate at `q = 14`, shifted) | `q ≥ 14`: the same with `betaEven q` |
| `margin_odd`, `margin_even` | §2, §4.2 | `alphaCore q + c₂ + β < 0` |
-/
import Chi2Irrational.Q.Defs
import Chi2Irrational.Q.Margin

namespace Chi2Irr
namespace Q

open Polynomial Filter

/-! ## The ingredients (stubs) -/

/-- **Arithmetic bound for general `q`** (RESULT §1, §4): given a 2-adic bound on the coefficients of `Δ_h` with limit
constant `c₂`, a common denominator of size `≤ (alphaCore q + c₂ + ε) h²` (odd primes: Theorem A, Lemma 5 + Corollary 9.1
for `p ∣ q² − 1`, Lemma 4′(ii) prime by prime for odd `p ∣ q`). -/
theorem arith_q (q : ℕ) (hq : 3 ≤ q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (c2 : ℝ)
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2) :
    ∃ den : ℕ → ℚ, (∀ h, 0 < den h) ∧ (∀ h k, ∃ z : ℤ, den h * (Delta q h).coeff k = z) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (alphaCore q + c2 + ε) * (h : ℝ) ^ 2 := by
  sorry

/-- **Lemma 10, general ν** (RESULT §1; CHI2_IRRATIONALITY §4.3): at odd `q`, `ν = v₂(q² − 1) ≥ 3`. -/
theorem twoAdic_odd (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2Odd q + ε) * (h : ℝ) ^ 2 := by
  sorry

/-- **Lemma 10₀** (RESULT §4.1): at even `q`, `n₂ ≤ −a(h) v₂(q) + ⌊h²/2⌋ − h`. -/
theorem twoAdic_even (q : ℕ) (hq : 3 ≤ q) (he : Even q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2Even q + ε) * (h : ℝ) ^ 2 := by
  sorry

/-- **Nonvanishing for general `q`** (RESULT §3): Lemma P along `h = 3ℓ` with the three block determinants as rational
functions of `q`, nonzero at every integer `q ≥ 2` (the route `nonvan_of` of `NonVan/NonVanQ.lean`). -/
theorem nonvan_q (q : ℕ) (hq : 3 ≤ q) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, (Delta q h).eval ((a : ℚ) / b) ≠ 0 := by
  sorry

/-- **Analytic bound at odd `q`** (RESULT §2): the `q = 3` certificate moved by the shift lemma. Stated for every
`q ≥ 3`. -/
theorem analytic_odd (q : ℕ) (hq : 3 ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ Real.exp ((betaOdd q + δ + ε) * (h : ℝ) ^ 2) := by
  sorry

/-- **Analytic bound at `q ≥ 14`** (RESULT §4.2): a certificate at `q = 14` with `Φ ≤ −3.03`, moved by the shift lemma. -/
theorem analytic_even (q : ℕ) (hq : 14 ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ Real.exp ((betaEven q + δ + ε) * (h : ℝ) ^ 2) := by
  sorry

/-- **Margin at odd `q`** (RESULT §2, closed form `0.3414 − ⅓ log q` with Lean's `Φ₃`). -/
theorem margin_odd (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) : alphaCore q + c2Odd q + betaOdd q < 0 :=
  margin_odd_proof q hq ho

/-- **Margin at even `q ≥ 14`** (RESULT §4.2). -/
theorem margin_even (q : ℕ) (hq : 14 ≤ q) (he : Even q) : alphaCore q + c2Even q + betaEven q < 0 :=
  margin_even_proof q hq he

/-! ## Assembly -/

/-- The endgame inputs from a 2-adic bound, an analytic constant and a margin. -/
theorem exists_bounds (q : ℕ) (hq : 3 ≤ q) (c2 β : ℝ) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h))
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2)
    (hM : alphaCore q + c2 + β < 0)
    (hA : ∀ δ > 0, ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
      |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ Real.exp ((β + δ + ε) * (h : ℝ) ^ 2)) :
    Nonempty (MachineBounds q) := by
  obtain ⟨den, hpos, hint, harith⟩ := arith_q q hq n2 hn2 c2 hc2
  set δ : ℝ := -(alphaCore q + c2 + β) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  exact ⟨{
    den := den
    den_pos := hpos
    den_int := hint
    α := alphaCore q + c2
    β := β + δ
    margin := by rw [hδ]; linarith
    arith := harith
    analytic := hA δ hδ0
    nonvan := nonvan_q q hq }⟩

/-- **Theorem Q.** -/
theorem theoremQ : TheoremQ := by
  intro q hq hE
  rcases Nat.even_or_odd q with he | ho
  · have h14 : 14 ≤ q := by
      obtain ⟨k, rfl⟩ := he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      omega
    obtain ⟨n2, hn2, hc2⟩ := twoAdic_even q hq he
    obtain ⟨H⟩ := exists_bounds q hq (c2Even q) (betaEven q) n2 hn2 hc2 (margin_even q h14 he)
      (fun δ hδ => analytic_even q h14 hδ)
    exact irrational_of_bounds H
  · obtain ⟨n2, hn2, hc2⟩ := twoAdic_odd q hq ho
    obtain ⟨H⟩ := exists_bounds q hq (c2Odd q) (betaOdd q) n2 hn2 hc2 (margin_odd q hq ho)
      (fun δ hδ => analytic_odd q hq hδ)
    exact irrational_of_bounds H

end Q
end Chi2Irr
