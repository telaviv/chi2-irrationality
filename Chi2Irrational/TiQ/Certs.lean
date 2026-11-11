/-
# Theorem T: the `q = 6` certificate (`L = 800`)

`cert_t6_proof` (stub `cert_t6` of `TiQ/Interface.lean`): the Lean-format dual certificate at `q = 6`, grid `L = 800`,
cells `s = 8` (`TiQ/Cert/{DataQ6L800,Q6L800}.lean`, data from `scripts/gen_cert.py 6 800 8 108 2 1`, every check by
`decide +kernel`), with `Φ ≤ PhiQ = −2.5671799991… ≤ PhiT6 = −2.5671`. `DualCert 6` depends on `q` only through
`|w| = 1/36`, so the same certificate serves the χ₂ and the Ti machines (RESULT §4).
-/
import Chi2Irrational.TiQ.Defs
import Chi2Irrational.TiQ.Cert.Q6L800

namespace Chi2Irr
namespace TiQ

/-- **The `q = 6` certificate**: the exact statement of `TiQ.cert_t6`. -/
theorem cert_t6_proof : ∃ C : DualCert 6, C.Phi ≤ (PhiT6 : ℝ) := by
  refine ⟨Cert.CData.toCert Cert.Q6L800.valid, ?_⟩
  have h := Cert.Q6L800.phi_le
  have e : ((PhiT6 : ℚ) : ℝ) = -25671 / 10000 := by rw [show PhiT6 = -25671 / 10000 from rfl]; push_cast; ring
  rw [e]
  exact h

end TiQ
end Chi2Irr
