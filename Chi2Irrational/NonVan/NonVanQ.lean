/-
# Nonvanishing for `q = 3` and `q = 5` (`MachineBounds.nonvan`)

The block determinants (exact, `norm_num`):
  q = 3: `det M(S) = 6642`, `det M(L) = 10896962/225`, `det M(D) = −5947389/80`;
  q = 5: `det M(S) = 3531250/27`, `det M(L) = 246357730/243`, `det M(D) = −6934894375/3888`.
For every prime `ℓ` larger than all
numerators, denominators, `q²` and `b`, `lemmaP` gives `Δ_{3ℓ}(a/b) ≠ 0`. There are infinitely many such `ℓ`, so:
`nonvan_three`, `nonvan_five`: `∀ a b, 0 < b → ∃ᶠ h in atTop, Δ_h(a/b) ≠ 0`.
No prime-gap theorem and no list of bad primes is needed.
-/
import Chi2Irrational.NonVan.LemmaP

namespace Chi2Irr

open Polynomial Finset Filter

lemma padicNorm_frac_eq_one {ℓ : ℕ} [Fact ℓ.Prime] {n : ℤ} {d : ℕ} (hn0 : n ≠ 0)
    (hn : n.natAbs < ℓ) (hd0 : 0 < d) (hd : d < ℓ) : padicNorm ℓ ((n : ℚ) / d) = 1 := by
  rw [padicNorm.div]
  have h1 : padicNorm ℓ (n : ℚ) = 1 := by
    refine padicNorm_intCast_eq_one ?_
    intro h
    have : ℓ ∣ n.natAbs := Int.natCast_dvd.mp h
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this
    omega
  have h2 : padicNorm ℓ (d : ℚ) = 1 := by
    refine padicNorm_natCast_eq_one ?_
    intro h; have := Nat.le_of_dvd hd0 h; omega
  rw [h1, h2, div_one]

/-- The general step: given the three determinants as fractions, nonvanishing holds frequently. -/
theorem nonvan_of {q : ℕ} (hq : 2 ≤ q) {nS nL nD : ℤ} {dS dL dD : ℕ}
    (hS : (MS q).det = (nS : ℚ) / dS) (hL : (ML q).det = (nL : ℚ) / dL)
    (hD : (MD q).det = (nD : ℚ) / dD) (hS0 : nS ≠ 0) (hL0 : nL ≠ 0) (hD0 : nD ≠ 0)
    (hdS : 0 < dS) (hdL : 0 < dL) (hdD : 0 < dD) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h in atTop, (Delta q h).eval ((a : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N
  set L := N + nS.natAbs + nL.natAbs + nD.natAbs + dS + dL + dD + q ^ 2 + b + 7
  obtain ⟨ℓ, hℓL, hℓp⟩ := Nat.exists_infinite_primes L
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  have hℓq : ¬ ℓ ∣ q := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hℓq2 : ¬ ℓ ∣ q ^ 2 - 1 := fun h => by
    have := Nat.le_of_dvd (by omega) h; omega
  have g : Good q ℓ := ⟨hq, by omega, hℓq, hℓq2⟩
  refine ⟨3 * ℓ, by omega, ?_⟩
  refine lemmaP g ?_ ?_ ?_ a hb (fun h => by have := Nat.le_of_dvd hb h; omega)
  · rw [hS]; exact padicNorm_frac_eq_one hS0 (by omega) hdS (by omega)
  · rw [hL]; exact padicNorm_frac_eq_one hL0 (by omega) hdL (by omega)
  · rw [hD]; exact padicNorm_frac_eq_one hD0 (by omega) hdD (by omega)

/-! ### The determinants -/

lemma det_MS_three : (MS 3).det = ((6642 : ℤ) : ℚ) / (1 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp [MS, crr, wt, Tq, Finset.sum_range_succ]
  norm_num

lemma det_ML_three : (ML 3).det = ((10896962 : ℤ) : ℚ) / (225 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp [ML, crr, wt, Tq, Finset.sum_range_succ]
  norm_num

lemma det_MD_three : (MD 3).det = ((-5947389 : ℤ) : ℚ) / (80 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp [MD, crr, wt, Tq, eD, Finset.sum_range_succ]
  norm_num

lemma det_MS_five : (MS 5).det = ((3531250 : ℤ) : ℚ) / (27 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp [MS, crr, wt, Tq, Finset.sum_range_succ]
  norm_num

lemma det_ML_five : (ML 5).det = ((246357730 : ℤ) : ℚ) / (243 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp [ML, crr, wt, Tq, Finset.sum_range_succ]
  norm_num

lemma det_MD_five : (MD 5).det = ((-6934894375 : ℤ) : ℚ) / (3888 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp [MD, crr, wt, Tq, eD, Finset.sum_range_succ]
  norm_num

/-- **Nonvanishing for `χ₂(1/3)`.** -/
theorem nonvan_three (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h in atTop, (Delta 3 h).eval ((a : ℚ) / b) ≠ 0 :=
  nonvan_of (by norm_num) det_MS_three det_ML_three det_MD_three (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) a b hb

/-- **Nonvanishing for `χ₂(1/5)`.** -/
theorem nonvan_five (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h in atTop, (Delta 5 h).eval ((a : ℚ) / b) ≠ 0 :=
  nonvan_of (by norm_num) det_MS_five det_ML_five det_MD_five (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) a b hb

end Chi2Irr
