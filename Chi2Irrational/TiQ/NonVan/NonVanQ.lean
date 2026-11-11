/-
# Nonvanishing for Ti from the three block determinants

Copy of `nonvan_of` in `NonVan/NonVanQ.lean` for the Ti machine: given `det M(S), det M(L), det M(D)` (of
`TiQ/NonVan/BlockMat.lean`) as nonzero fractions, every prime `ℓ` larger than all numerators, denominators, `q² + 1`
and `b` is good (`ℓ ∤ q(q²+1)`, `ℓ ∤ b`), and `lemmaP` gives `Δ^Ti_{3ℓ}(a/b) ≠ 0`. There are infinitely many such `ℓ`.
The generic `padicNorm_frac_eq_one` is reused.
-/
import Chi2Irrational.TiQ.NonVan.LemmaP
import Chi2Irrational.NonVan.NonVanQ

namespace Chi2Irr
namespace TiQ

open Polynomial Finset Filter

/-- The general step: given the three determinants as fractions, nonvanishing holds frequently. -/
theorem nonvan_of {q : ℕ} (hq : 2 ≤ q) {nS nL nD : ℤ} {dS dL dD : ℕ}
    (hS : (MS q).det = (nS : ℚ) / dS) (hL : (ML q).det = (nL : ℚ) / dL)
    (hD : (MD q).det = (nD : ℚ) / dD) (hS0 : nS ≠ 0) (hL0 : nL ≠ 0) (hD0 : nD ≠ 0)
    (hdS : 0 < dS) (hdL : 0 < dL) (hdD : 0 < dD) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h in atTop, (DeltaT q h).eval ((a : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N
  set L := N + nS.natAbs + nL.natAbs + nD.natAbs + dS + dL + dD + q ^ 2 + b + 7
  obtain ⟨ℓ, hℓL, hℓp⟩ := Nat.exists_infinite_primes L
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  have hℓq : ¬ ℓ ∣ q := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hℓq2 : ¬ ℓ ∣ q ^ 2 + 1 := fun h => by
    have := Nat.le_of_dvd (by omega) h; omega
  have g : Good q ℓ := ⟨hq, by omega, hℓq, hℓq2⟩
  refine ⟨3 * ℓ, by omega, ?_⟩
  refine lemmaP g ?_ ?_ ?_ a hb (fun h => by have := Nat.le_of_dvd hb h; omega)
  · rw [hS]; exact padicNorm_frac_eq_one hS0 (by omega) hdS (by omega)
  · rw [hL]; exact padicNorm_frac_eq_one hL0 (by omega) hdL (by omega)
  · rw [hD]; exact padicNorm_frac_eq_one hD0 (by omega) hdD (by omega)

end TiQ
end Chi2Irr
