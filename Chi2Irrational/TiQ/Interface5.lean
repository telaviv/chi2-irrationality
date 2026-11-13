/-
# Theorem T₅: `Ti₂(1/q) ∉ ℚ` for every integer `q ≥ 5`

Source: `../handoff/log2log3/pilot_ti2_q5/RESULT.md` (Lemma M; one AI gate referee, PASS WITH FIXES). Theorem T
(`TiQ/Interface.lean`, `q ≥ 6`) is unchanged; this file adds `q = 5`:
* the 2-adic bound at odd `q` is Lemma M (`TiQ/M/Final.lean`), limit constant `⅛ log 2` in place of Lemma 10₁'s `¼ log 2`;
* the analytic bound is the signed Theorem B (`TiQ.analytic_t`) with a new Lean-format certificate at `q = 5`, grid
  `L = 200` (`Cert/{DataQ5L200,Q5L200}.lean`, `Φ ≤ PhiQ = −2.4435517… ≤ PhiT5 = −2.44`; the older `q = 5` certificate,
  `Φ ≤ −2.385`, is too coarse here);
* margin `alphaCoreT 5 + ⅛ log 2 + PhiT5 = −0.0319…` (Lean proves `< 0` with elementary logarithm bounds);
* the odd-prime bound (`arith_t`) and nonvanishing (`nonvan_t`) are those of Theorem T, stated for every `q ≥ 3`.
Departure from the source: RESULT uses the Arb certificate `Φ₅ ≤ −2.4516816` (margin `−0.0436`); Lean's certificate is
coarser (margin `−0.0319`). The written Lemma M uses a 2-adic `θ₂`; the formal proof uses a rational truncation
(`TiQ/M/Defs.lean`).
-/
import Chi2Irrational.TiQ.Interface
import Chi2Irrational.TiQ.M.Final
import Chi2Irrational.Cert.Q5L200

namespace Chi2Irr
namespace TiQ

open Polynomial Filter

/-- **Theorem T₅**: `Ti₂(1/q)` is irrational for every integer `q ≥ 5`. -/
def TheoremT5 : Prop := ∀ q : ℕ, 5 ≤ q → Irrational (ti2 (1 / (q : ℝ)))

/-- The target exponent of the `q = 5` certificate (`L = 200`; certified `Φ = −2.4435517…`). -/
def PhiT5 : ℚ := -244 / 100

/-- **The `q = 5` certificate** (`L = 200`). -/
theorem cert_t5 : ∃ C : DualCert 5, C.Phi ≤ (PhiT5 : ℝ) := by
  refine ⟨Cert.CData.toCert Cert.Q5L200.valid, ?_⟩
  have h := Cert.Q5L200.phi_le
  have e : ((PhiT5 : ℚ) : ℝ) = -244 / 100 := by rw [show PhiT5 = -244 / 100 from rfl]; push_cast; ring
  rw [e]
  exact h

/-- **Lemma M** at odd `q ≥ 3`: a 2-adic bound with `c₂ = ⅛ log 2`. -/
theorem twoAdic_odd_M (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (Real.log 2 / 8 + ε) * (h : ℝ) ^ 2 :=
  M.twoAdic_odd_M_proof q hq ho

/-- **Margin at `q = 5`**: `alphaCoreT 5 + ⅛ log 2 + PhiT5 < 0` (true value `−0.0319…`). -/
theorem margin_t5 : alphaCoreT 5 + Real.log 2 / 8 + (PhiT5 : ℝ) < 0 := by
  have h2 := Real.log_two_lt_d9
  have hv : padicValNat 2 26 = 1 := Q.padicValNat_two_pow_mul_odd 1 13 (by norm_num) (by norm_num)
  have ho1 : Q.oddPart (5 ^ 2 + 1) = 13 := by
    show Q.oddPart 26 = 13
    simp [Q.oddPart, hv]
  have ho2 : Q.oddPart 5 = 5 := Q.oddPart_of_not_dvd (by norm_num)
  -- `log 13 ≤ log 16 − 3/16` and `log 4 ≤ log 5 − 1/5`
  have h13 := Q.log_le_log_add (a := 13) (b := 16) (by norm_num) (by norm_num)
  have h5 := Q.log_le_log_add (a := 4) (b := 5) (by norm_num) (by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  unfold alphaCoreT
  rw [ho1, ho2, show PhiT5 = -244 / 100 from rfl]
  push_cast
  rw [h16] at h13
  rw [h4] at h5
  norm_num at h13 h5 h2 ⊢
  linarith

/-- **Theorem T₅.** `Ti₂(1/q) ∉ ℚ` for every integer `q ≥ 5`. -/
theorem theoremT5 : TheoremT5 := by
  intro q hq
  rcases Nat.lt_or_ge q 6 with h6 | h6
  · have h5 : q = 5 := by omega
    subst h5
    obtain ⟨n2, hn2, hc2⟩ := twoAdic_odd_M 5 (by norm_num) (by decide)
    obtain ⟨C, hC⟩ := cert_t5
    obtain ⟨H⟩ := exists_boundsT 5 (by norm_num) (Real.log 2 / 8) (PhiT5 : ℝ) n2 hn2 hc2 margin_t5
      (fun δ hδ ε hε => by
        filter_upwards [analytic_t C (by norm_num) ε hε] with h hh
        refine hh.trans (Real.exp_le_exp.mpr ?_)
        have : (0 : ℝ) ≤ (h : ℝ) ^ 2 := by positivity
        nlinarith)
    exact irrational_of_boundsT H
  · exact theoremT q h6

end TiQ
end Chi2Irr
