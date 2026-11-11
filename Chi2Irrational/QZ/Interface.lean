/-
# Theorem Q4′ (numerator 2): the ingredients and the assembly (`pilot_chi2_2q/RESULT.md`)

The machine is `DeltaZ (zq q)`, the `χ₂(1/q)` machine at `ζ = q/2` (RESULT §1). Each ingredient is proved as
`<name>_proof` in its own file under `Chi2Irrational/QZ/`.

| ingredient | RESULT | statement |
|---|---|---|
| `arith_z` | §1, §4 | from a 2-adic bound `(n₂, c₂)`: a denominator with `log den ≤ (alphaZ q + c₂ + ε) h²` |
| `twoAdic_num` | §2 (Lemma 10″) | odd `q`: a 2-adic bound with `c₂ = c2Num = (4/3) log 2` |
| `nonvan_z` | §5 (Lemma P at `ζ = q/2`, along `h = 3ℓ`) | `Δ_h(a/b) ≠ 0` for infinitely many `h` |
| `analytic_z` | §3 (certificate at `w = 4/qB²`, shift lemma) | `|Δ_h(χ₂(2/q))| ≤ exp((betaZ q + δ + ε) h²)` eventually |
| `margin_z` | §4 | `alphaZ q + c2Num + betaZ q < 0` for odd `q ≥ qB` |
-/
import Chi2Irrational.QZ.Defs
import Chi2Irrational.QZ.MainCond
import Chi2Irrational.QZ.Arith
import Chi2Irrational.QZ.NonVan
import Chi2Irrational.QZ.Margin
import Chi2Irrational.QZ.TwoAdic
import Chi2Irrational.QZ.Analytic

namespace Chi2Irr
namespace QZ

open Polynomial Filter

/-! ## The ingredients -/

/-- **Arithmetic bound at `ζ = q/2`** (RESULT §1, §4): given a 2-adic bound on the coefficients of `Δ_h` with limit
constant `c₂`, a common denominator of size `≤ (alphaZ q + c₂ + ε) h²` (odd primes: Theorem A, Lemma 5 + Corollary 9.1
for `p ∣ q² − 4`, Lemma 4′(ii) for `p ∣ q`). -/
theorem arith_z (q : ℕ) (hq : 5 ≤ q) (ho : Odd q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((DeltaZ (zq q) h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (c2 : ℝ)
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2) :
    ∃ den : ℕ → ℚ, (∀ h, 0 < den h) ∧ (∀ h k, ∃ z : ℤ, den h * (DeltaZ (zq q) h).coeff k = z) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (alphaZ q + c2 + ε) * (h : ℝ) ^ 2 :=
  arith_z_proof q hq ho n2 hn2 c2 hc2

/-- **Lemma 10″** (RESULT §2): at `ζ = q/2`, `q` odd, `n₂(Δ_h) ≤ (4/3) h² + O(h)`, stated in limit
form (the proof's `n2Z` satisfies `3 n₂(h) ≤ 4h² + 4h + 4`, `QZ/TwoAdic.lean`). -/
theorem twoAdic_num (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaZ (zq q) h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2Num + ε) * (h : ℝ) ^ 2 :=
  twoAdic_num_proof q hq ho

/-- **Nonvanishing at `ζ = q/2`** (RESULT §5): Lemma P along `h = 3ℓ`. -/
theorem nonvan_z (q : ℕ) (hq : 5 ≤ q) (ho : Odd q) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, (DeltaZ (zq q) h).eval ((a : ℚ) / b) ≠ 0 :=
  nonvan_z_proof q hq ho a b hb

/-- **Analytic bound at `ζ = q/2`** (RESULT §3): the certificate at `w = 4/qB²` moved by the shift lemma. -/
theorem analytic_z (q : ℕ) (hq : qB ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / ((zq q : ℚ) : ℝ))) (DeltaZ (zq q) h)| ≤ Real.exp ((betaZ q + δ + ε) * (h : ℝ) ^ 2) :=
  analytic_z_proof q hq hδ

/-- **Margin** (RESULT §4). -/
theorem margin_z (q : ℕ) (hq : qB ≤ q) (ho : Odd q) : alphaZ q + c2Num + betaZ q < 0 :=
  margin_z_proof q hq ho

/-! ## Assembly -/

lemma chi2_two_div (q : ℕ) : chi2 (2 / (q : ℝ)) = chi2 (1 / ((zq q : ℚ) : ℝ)) := by
  congr 1
  unfold zq
  push_cast
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have : (q : ℝ) ≠ 0 := by positivity
    field_simp

/-- **Theorem Q4′ (numerator 2).** `χ₂(2/q)` is irrational for every odd `q ≥ qB`. -/
theorem theoremQ4num : ∀ q : ℕ, Odd q → 175 ≤ q → Irrational (chi2 (2 / (q : ℝ))) := by
  intro q ho hq
  have hqB : qB ≤ q := hq
  have h5 : 5 ≤ q := by omega
  obtain ⟨n2, hn2, hc2⟩ := twoAdic_num q (by omega) ho
  obtain ⟨den, hpos, hint, harith⟩ := arith_z q h5 ho n2 hn2 c2Num hc2
  have hM := margin_z q hqB ho
  set δ : ℝ := -(alphaZ q + c2Num + betaZ q) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  rw [chi2_two_div]
  exact irrational_of_boundsZ {
    den := den
    den_pos := hpos
    den_int := hint
    α := alphaZ q + c2Num
    β := betaZ q + δ
    margin := by rw [hδ]; linarith
    arith := harith
    analytic := analytic_z q hqB hδ0
    nonvan := nonvan_z q h5 ho }

end QZ
end Chi2Irr
