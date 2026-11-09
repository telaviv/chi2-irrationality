/-
# Theorem Q: the analytic bounds (RESULT §2, §4.2)

* `analytic_odd_proof`: the `q = 3` certificate (`Cert/Q3.lean`, `Φ ≤ PhiQ < −2.078`) moved to every `q ≥ 3` by the
  shift lemma (`Q/Shift.lean`), then Theorem B (`DualCert.analytic`);
* `analytic_even_proof`: the `q = 14` certificate (`Cert/Q14.lean`, `Φ ≤ PhiQ = −3.03724 < −3.03`) moved to every
  `q ≥ 14` the same way.
-/
import Chi2Irrational.Q.Defs
import Chi2Irrational.Q.Shift
import Chi2Irrational.Cert.Q3
import Chi2Irrational.Cert.Q14

namespace Chi2Irr
namespace Q

open Polynomial Filter

/-- A certificate at `q₀` with `Φ ≤ Φ₀` gives the analytic bound with `Φ₀ − ½ log(q/q₀) + δ` at every `q ≥ q₀`. -/
theorem analytic_of_cert {q₀ : ℕ} (C : DualCert q₀) (hq₀ : 2 ≤ q₀) {Φ₀ : ℝ} (hΦ : C.Phi ≤ Φ₀) (q : ℕ)
    (hq : q₀ ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
      |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤
        Real.exp ((Φ₀ - Real.log ((q : ℝ) / q₀) / 2 + δ + ε) * (h : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨C', hC'⟩ := DualCert.shift C (by omega) q hq hδ
  filter_upwards [C'.analytic (by omega) ε hε] with h hh
  refine hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
  linarith

/-- The `q = 3` certificate: `Φ ≤ −2.078`. -/
lemma phi_Q3 : (Cert.CData.toCert Cert.Q3.valid).Phi ≤ -2078 / 1000 := by
  have h1 := Cert.CData.Phi_le Cert.Q3.valid
  have h2 : (Cert.Q3.data.PhiQ : ℝ) ≤ -2078 / 1000 := by exact_mod_cast Cert.Q3.phiQ_le
  linarith

/-- **Analytic bound at odd `q`** (RESULT §2), stated for every `q ≥ 3`. -/
theorem analytic_odd_proof (q : ℕ) (hq : 3 ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ Real.exp ((betaOdd q + δ + ε) * (h : ℝ) ^ 2) := by
  have H := analytic_of_cert (q₀ := 3) (Cert.CData.toCert Cert.Q3.valid) (by norm_num) phi_Q3 q hq hδ
  have e : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [e] at H
  exact H

/-- **Analytic bound at `q ≥ 14`** (RESULT §4.2). -/
theorem analytic_even_proof (q : ℕ) (hq : 14 ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ Real.exp ((betaEven q + δ + ε) * (h : ℝ) ^ 2) := by
  have H := analytic_of_cert (q₀ := 14) (Cert.CData.toCert Cert.Q14.valid) (by norm_num) Cert.Q14.phi_le q hq hδ
  have e : ((14 : ℕ) : ℝ) = 14 := by norm_num
  rw [e] at H
  exact H

end Q
end Chi2Irr
