/-
# Theorem Q₄: the new ingredients and the assembly

| ingredient | source | statement |
|---|---|---|
| `twoAdic_even_sharp` | `pilot_qeven/RESULT.md`, Lemma 10_e | even `q ≥ 3`: a 2-adic bound with `c₂ = c2EvenSharp q` |
| `cert_newQ` | `pilot_qeven/CERTS.md` | `q ∈ {6, 8, 10, 12}`: a `DualCert q` with `Φ ≤ PhiT q` |
| `margin_newQ` | `pilot_qeven/RESULT.md` §margins | `q ∈ {6, 8, 10, 12}`: `alphaCore q + c2EvenSharp q + PhiT q < 0` |
The rest is Theorem Q (`Q/Interface.lean`: `arith_q`, `nonvan_q`, `exists_bounds`, `theoremQ`).
-/
import Chi2Irrational.Q.Even.Defs
import Chi2Irrational.Q.Interface
import Chi2Irrational.Q.Even.Margin
import Chi2Irrational.Q.Even.Certs

namespace Chi2Irr
namespace Q

open Polynomial Filter

/-! ## The new ingredients (stubs) -/

/-- **Lemma 10_e** (`pilot_qeven/RESULT.md`): at even `q₀`, `e = v₂(q₀)`,
`n₂(Δ_h) ≤ −a(h)·e + c(e)·h² + O(h log h)`, `c(e) = (6 − 4e)/(3(3e + 8))`. -/
theorem twoAdic_even_sharp (q : ℕ) (hq : 3 ≤ q) (he : Even q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2EvenSharp q + ε) * (h : ℝ) ^ 2 := by
  sorry

/-- **Direct certificates** at `q = 6, 8, 10, 12`. -/
theorem cert_newQ {q : ℕ} (hq : q ∈ newQ) : ∃ C : DualCert q, C.Phi ≤ (PhiT q : ℝ) :=
  cert_newQ_proof hq

/-- **The margins** at `q = 6, 8, 10, 12`. -/
theorem margin_newQ {q : ℕ} (hq : q ∈ newQ) : alphaCore q + c2EvenSharp q + (PhiT q : ℝ) < 0 :=
  margin_newQ_proof hq

/-! ## Assembly -/

lemma three_le_of_newQ {q : ℕ} (hq : q ∈ newQ) : 3 ≤ q := by
  simp only [newQ, Finset.mem_insert, Finset.mem_singleton] at hq; omega

lemma even_of_newQ {q : ℕ} (hq : q ∈ newQ) : Even q := by
  simp only [newQ, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- `χ₂(1/q) ∉ ℚ` at `q = 6, 8, 10, 12`. -/
theorem irrational_newQ {q : ℕ} (hq : q ∈ newQ) : Irrational (chi2 (1 / (q : ℝ))) := by
  have h3 := three_le_of_newQ hq
  obtain ⟨n2, hn2, hc2⟩ := twoAdic_even_sharp q h3 (even_of_newQ hq)
  obtain ⟨C, hC⟩ := cert_newQ hq
  obtain ⟨H⟩ := exists_bounds q h3 (c2EvenSharp q) (PhiT q) n2 hn2 hc2 (margin_newQ hq) (fun δ hδ ε hε => by
    filter_upwards [C.analytic (by omega) ε hε] with h hh
    refine hh.trans (Real.exp_le_exp.mpr ?_)
    have : (0 : ℝ) ≤ (h : ℝ) ^ 2 := by positivity
    nlinarith)
  exact irrational_of_bounds H

/-- **Theorem Q₄.** -/
theorem theoremQ4 : TheoremQ4 := by
  intro q hq h4
  by_cases hn : q ∈ newQ
  · exact irrational_newQ hn
  · refine theoremQ q hq ?_
    intro hm
    simp only [newQ, Finset.mem_insert, Finset.mem_singleton] at hn hm
    omega

end Q
end Chi2Irr
