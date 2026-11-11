/-
# Theorem Q4′ (numerator 2): the analytic bound (`pilot_chi2_2q/RESULT.md` §3)

`analytic_z_proof`: the certificate at `w = 4/qB²` (`ζ_B = qB/2 = 177/2`, `QZ/CertQ177.lean`, `Φ ≤ PhiB = −4.005`)
moved to `ζ = q/2` for every `q ≥ qB` by the shift lemma (`QZ/Shift.lean`, gain `½ log(ζ/ζ_B) = ½ log(q/qB)`), then
Theorem B at `ζ` (`DualCertW.analyticZ`). This is the statement of the stub `analytic_z` in `QZ/Interface.lean`.
-/
import Chi2Irrational.QZ.Defs
import Chi2Irrational.QZ.Shift
import Chi2Irrational.QZ.CertQ177

namespace Chi2Irr
namespace QZ

open Polynomial Filter

lemma log_WrZ {ζ : ℚ} (hζ : 1 < ζ) : Real.log (WrZ ζ) = -2 * Real.log (ζ : ℝ) := by
  have h0 : (0 : ℝ) < ζ := by have : (1 : ℝ) < ζ := by exact_mod_cast hζ
                              linarith
  unfold WrZ wtZ
  push_cast
  rw [one_div, Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- A certificate at `ζ₀` with `Φ ≤ Φ₀` gives the analytic bound with `Φ₀ − ½ log(ζ/ζ₀) + δ` at every rational
`ζ ≥ ζ₀`. -/
theorem analytic_of_certZ {ζ₀ : ℚ} (hζ₀ : 1 < ζ₀) (C : DualCertZ ζ₀) {Φ₀ : ℝ} (hΦ : DualCertW.Phi C ≤ Φ₀)
    {ζ : ℚ} (hζ : ζ₀ ≤ ζ) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
      |aeval (chi2 (1 / (ζ : ℝ))) (DeltaZ ζ h)| ≤
        Real.exp ((Φ₀ - Real.log ((ζ : ℝ) / ζ₀) / 2 + δ + ε) * (h : ℝ) ^ 2) := by
  intro ε hε
  have hζ1 : 1 < ζ := lt_of_lt_of_le hζ₀ hζ
  have hW := WrZ_pos hζ1
  have h0 : (0 : ℝ) < ζ₀ := by have : (1 : ℝ) < ζ₀ := by exact_mod_cast hζ₀
                               linarith
  have hle : (ζ₀ : ℝ) ≤ ζ := by exact_mod_cast hζ
  have hWW : WrZ ζ ≤ WrZ ζ₀ := by
    unfold WrZ wtZ
    push_cast
    gcongr
  obtain ⟨C', hC'⟩ := DualCertW.shift C hW hWW hδ
  have hlog : (Real.log (WrZ ζ₀) - Real.log (WrZ ζ)) / 4 = Real.log ((ζ : ℝ) / ζ₀) / 2 := by
    rw [log_WrZ hζ₀, log_WrZ hζ1, Real.log_div (by linarith) h0.ne']
    ring
  filter_upwards [DualCertW.analyticZ hζ1 C' ε hε] with h hh
  refine hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
  linarith

/-- The base certificate sits at `ζ_B = zq qB = 177/2`. -/
lemma cert_zeta : ((Cert.Q177.data.q : ℚ) / Cert.Q177.data.a) = zq qB := by
  rw [show Cert.Q177.data.q = 177 from rfl, show Cert.Q177.data.a = 2 from rfl]
  norm_num [zq, qB]

/-- The base certificate: `Φ ≤ PhiB`. -/
lemma phi_Q177 : DualCertW.Phi (CDataZ.toCertZ Cert.Q177.valid) ≤ ((PhiB : ℚ) : ℝ) := by
  have h := Cert.Q177.phi_le
  have e : ((PhiB : ℚ) : ℝ) = -4005 / 1000 := by norm_num [PhiB]
  rw [e]
  exact h

/-- **Analytic bound at `ζ = q/2`** (RESULT §3): the statement of `analytic_z`. -/
theorem analytic_z_proof (q : ℕ) (hq : qB ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / ((zq q : ℚ) : ℝ))) (DeltaZ (zq q) h)| ≤ Real.exp ((betaZ q + δ + ε) * (h : ℝ) ^ 2) := by
  have hv := Cert.Q177.valid
  have hζ₀ : 1 < ((Cert.Q177.data.q : ℚ) / Cert.Q177.data.a) := CDataZ.one_lt_zeta hv
  have hle : ((Cert.Q177.data.q : ℚ) / Cert.Q177.data.a) ≤ zq q := by
    rw [cert_zeta]
    unfold zq
    have : (qB : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  have H := analytic_of_certZ hζ₀ (CDataZ.toCertZ hv) phi_Q177 hle hδ
  rw [cert_zeta] at H
  have hqB : (0 : ℝ) < qB := by norm_num [qB]
  have e : Real.log (((zq q : ℚ) : ℝ) / ((zq qB : ℚ) : ℝ)) = Real.log ((q : ℝ) / qB) := by
    congr 1
    unfold zq
    push_cast
    field_simp
  rw [e] at H
  exact H

end QZ
end Chi2Irr
