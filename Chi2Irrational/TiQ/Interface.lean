/-
# Theorem T: the ingredients and the assembly (`pilot_ti2q/RESULT.md`)

Copy of the layout of `Q/Interface.lean` and `Q/Even/Interface.lean`. Each ingredient is proved as `<name>_proof` in
its own file under `Chi2Irrational/TiQ/`; the assembly (`theoremT`) feeds them to `MachineBoundsT q` and
`irrational_of_boundsT`.

| ingredient | RESULT | statement |
|---|---|---|
| `arith_t` | §2 (transfer + odd primes) | from a 2-adic bound `(n₂, c₂)`: a denominator with `log den ≤ (alphaCoreT q + c₂ + ε) h²` |
| `twoAdic_odd_t` | §3 (Lemma 10₁) | odd `q`: a 2-adic bound with `c₂ = ¼ log 2` |
| `twoAdic_even_t` | §2 (Lemma 10_e transferred) | even `q`: a 2-adic bound with `c₂ = c2EvenSharp q` |
| `nonvan_t` | §5 (Lemma P at `Q = −q²`) | `Δ^Ti_h(a/b) ≠ 0` for infinitely many `h` |
| `analytic_t` | §4 (Theorem B for signed `w`) | a `DualCert q` (it sees only `|w| = q⁻²`) bounds `|Δ^Ti_h(Ti₂(1/q))|` |
| `cert_t6` | §6, §11 | a `DualCert 6` with `Φ ≤ PhiT6` (`L = 800`) |
| `margin_t6`, `margin_t_odd`, `margin_t_even` | §6 | `alphaCoreT q + c₂ + β < 0` |
-/
import Chi2Irrational.TiQ.MainCond
import Chi2Irrational.Q.Shift
import Chi2Irrational.TiQ.Arith
import Chi2Irrational.TiQ.TwoAdicNu1
import Chi2Irrational.TiQ.TwoAdicEven

namespace Chi2Irr
namespace TiQ

open Polynomial Filter

/-! ## The ingredients -/

/-- **Arithmetic bound** (RESULT §2): given a 2-adic bound on the coefficients of `Δ^Ti_h` with limit constant `c₂`, a
common denominator of size `≤ (alphaCoreT q + c₂ + ε) h²`. Odd primes: Theorem A at `p ∤ q(q² + 1)`, Lemma 5 +
Corollary 9.1 at `p ∣ q² + 1`, Lemma 4′(ii) at `p ∣ q` (all transferred from the χ₂ machine coefficientwise). -/
theorem arith_t (q : ℕ) (hq : 3 ≤ q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (c2 : ℝ)
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2) :
    ∃ den : ℕ → ℚ, (∀ h, 0 < den h) ∧ (∀ h k, ∃ z : ℤ, den h * (DeltaT q h).coeff k = z) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (alphaCoreT q + c2 + ε) * (h : ℝ) ^ 2 := by
  exact arith_t_proof q hq n2 hn2 c2 hc2

/-- **Lemma 10₁** (RESULT §3): at odd `q`, `ν = v₂(q² + 1) = 1`, `n₂ ≤ ⌊h²/4⌋ + O(h log h)`. -/
theorem twoAdic_odd_t (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2TiOdd + ε) * (h : ℝ) ^ 2 := by
  exact twoAdic_odd_t_proof q hq ho

/-- **Lemma 10_e for Ti** (RESULT §2, table row "p = 2, even q"): the same bound as for χ₂. -/
theorem twoAdic_even_t (q : ℕ) (hq : 3 ≤ q) (he : Even q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (Q.c2EvenSharp q + ε) * (h : ℝ) ^ 2 := by
  exact twoAdic_even_t_proof q hq he

/-- **Nonvanishing** (RESULT §5): Lemma P along `h = 3ℓ` with the block constants at `Q = −q²`. -/
theorem nonvan_t (q : ℕ) (hq : 3 ≤ q) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, (DeltaT q h).eval ((a : ℚ) / b) ≠ 0 := by
  sorry

/-- **Theorem B for the signed weight** (RESULT §4): a dual certificate for `|w| = q⁻²` bounds the Ti machine. -/
theorem analytic_t {q : ℕ} (C : DualCert q) (hq : 2 ≤ q) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)| ≤ Real.exp ((C.Phi + ε) * (h : ℝ) ^ 2) := by
  sorry

/-- **The `q = 6` certificate** (`L = 800`). -/
theorem cert_t6 : ∃ C : DualCert 6, C.Phi ≤ (PhiT6 : ℝ) := by
  sorry

/-- **Margin at `q = 6`** (direct certificate). -/
theorem margin_t6 : alphaCoreT 6 + Q.c2EvenSharp 6 + (PhiT6 : ℝ) < 0 := by
  sorry

/-- **Margin at odd `q ≥ 7`** (the `q = 6` certificate, shifted). -/
theorem margin_t_odd (q : ℕ) (hq : 7 ≤ q) (ho : Odd q) : alphaCoreT q + c2TiOdd + betaT q < 0 := by
  sorry

/-- **Margin at even `q ≥ 8`** (the `q = 6` certificate, shifted). -/
theorem margin_t_even (q : ℕ) (hq : 8 ≤ q) (he : Even q) : alphaCoreT q + Q.c2EvenSharp q + betaT q < 0 := by
  sorry

/-! ## Assembly -/

/-- The endgame inputs from a 2-adic bound, an analytic constant and a margin. -/
theorem exists_boundsT (q : ℕ) (hq : 3 ≤ q) (c2 β : ℝ) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h))
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2)
    (hM : alphaCoreT q + c2 + β < 0)
    (hA : ∀ δ > 0, ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
      |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)| ≤ Real.exp ((β + δ + ε) * (h : ℝ) ^ 2)) :
    Nonempty (MachineBoundsT q) := by
  obtain ⟨den, hpos, hint, harith⟩ := arith_t q hq n2 hn2 c2 hc2
  set δ : ℝ := -(alphaCoreT q + c2 + β) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  exact ⟨{
    den := den
    den_pos := hpos
    den_int := hint
    α := alphaCoreT q + c2
    β := β + δ
    margin := by rw [hδ]; linarith
    arith := harith
    analytic := hA δ hδ0
    nonvan := nonvan_t q hq }⟩

/-- The `q = 6` certificate gives the analytic bound with `betaT q + δ` at every `q ≥ 6`. -/
theorem analytic_betaT (q : ℕ) (hq : 6 ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (ti2 (1 / (q : ℝ))) (DeltaT q h)| ≤ Real.exp ((betaT q + δ + ε) * (h : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨C, hC⟩ := cert_t6
  obtain ⟨C', hC'⟩ := Q.DualCert.shift C (by norm_num) q hq hδ
  filter_upwards [analytic_t C' (by omega) ε hε] with h hh
  refine hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
  have e : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [e] at hC'
  unfold betaT
  linarith

/-- **Theorem T.** `Ti₂(1/q) ∉ ℚ` for every integer `q ≥ 6`. -/
theorem theoremT : TheoremT := by
  intro q hq
  have h3 : 3 ≤ q := by omega
  rcases Nat.even_or_odd q with he | ho
  · obtain ⟨n2, hn2, hc2⟩ := twoAdic_even_t q h3 he
    rcases Nat.lt_or_ge q 8 with h8 | h8
    · -- `q = 6`: the direct certificate
      have h6 : q = 6 := by obtain ⟨k, rfl⟩ := he; omega
      subst h6
      obtain ⟨C, hC⟩ := cert_t6
      obtain ⟨H⟩ := exists_boundsT 6 h3 (Q.c2EvenSharp 6) (PhiT6 : ℝ) n2 hn2 hc2 margin_t6
        (fun δ hδ ε hε => by
          filter_upwards [analytic_t C (by norm_num) ε hε] with h hh
          refine hh.trans (Real.exp_le_exp.mpr ?_)
          have : (0 : ℝ) ≤ (h : ℝ) ^ 2 := by positivity
          nlinarith)
      exact irrational_of_boundsT H
    · obtain ⟨H⟩ := exists_boundsT q h3 (Q.c2EvenSharp q) (betaT q) n2 hn2 hc2 (margin_t_even q h8 he)
        (fun δ hδ => analytic_betaT q hq hδ)
      exact irrational_of_boundsT H
  · have h7 : 7 ≤ q := by obtain ⟨k, rfl⟩ := ho; omega
    obtain ⟨n2, hn2, hc2⟩ := twoAdic_odd_t q h3 ho
    obtain ⟨H⟩ := exists_boundsT q h3 c2TiOdd (betaT q) n2 hn2 hc2 (margin_t_odd q h7 ho)
      (fun δ hδ => analytic_betaT q hq hδ)
    exact irrational_of_boundsT H

end TiQ
end Chi2Irr
