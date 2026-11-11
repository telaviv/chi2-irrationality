/-
# Lemma 10_e for Ti (`pilot_ti2q/RESULT.md` §2, table row "p = 2, even q")

At even `q₀`, `q₀² + 1` is odd and the weighted-Gauss-valuation bound `WLe_DeltaP` of Lemma 10_e
(`Q/Even/TwoAdicSharp.lean`, a statement about the symbolic χ₂ determinant mapped to `ℚ⟦q⟧[X]`) transfers to `Δ^Ti`:
copy of step 4 (`padicNorm_Delta_of_WLe`) with the Ti clearing `clearET` of `TiQ/Free.lean`, whose coefficients are `±`
those of `clearE` (`padicNorm_coeff_clearET`). Step 5 (the limit) is copied verbatim.
-/
import Chi2Irrational.TiQ.Free
import Chi2Irrational.Q.Even.TwoAdicSharp

namespace Chi2Irr
namespace TiQ

open Finset Filter
open scoped Nat

lemma odd_sq_add_one {q : ℕ} (he : Even q) : ¬ 2 ∣ q ^ 2 + 1 := by
  obtain ⟨k, rfl⟩ := he
  intro h
  have : (k + k) ^ 2 + 1 = 2 * (2 * k ^ 2) + 1 := by ring
  rw [this] at h
  omega

lemma padicNorm_qsqT_unit' {p q : ℕ} [Fact p.Prime] (hp : ¬ p ∣ q ^ 2 + 1) :
    padicNorm p ((q : ℚ) ^ 2 + 1) = 1 := by
  rw [show (q : ℚ) ^ 2 + 1 = ((q ^ 2 + 1 : ℕ) : ℚ) by push_cast; ring, padicNorm.nat_eq_one_iff]; exact hp

/-- Step 4 for Ti: specialisation at an even `q₀` (`v₂(q₀) = e`). -/
theorem padicNorm_DeltaT_of_WLe {q e h : ℕ} (hq : 2 ≤ q) (hodd : ¬ 2 ∣ q ^ 2 + 1)
    (hqe : padicNorm 2 (q : ℚ) = (2 : ℚ) ^ (-(e : ℤ))) {B : ℚ} (hB : 0 ≤ B)
    (hW : Q.WLe e B ((DeltaF h).map psiP.toRingHom)) (k : ℕ) : padicNorm 2 ((DeltaT q h).coeff k) ≤ B := by
  set f := (DeltaF h).coeff k with hfdef
  have hE : EDeg (betaP h) f := EDeg_DeltaF h k
  have hpar : ∀ m, f.coeff m ≠ 0 → Even (m 0 + k) := parity_DeltaF h k
  set G := clearE (betaP h) f with hG
  set GT := clearET (betaP h) (twF k f) with hGT
  set v : Fin 2 → ℚ := ![(q : ℚ), 1 / ((q : ℚ) ^ 2 + 1)] with hvdef
  have hv : v 1 * (v 0 ^ 2 + 1) = 1 := by
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    field_simp [(qsq_add_one_pos q).ne']
  have hcl : MvPolynomial.aeval v GT = (v 0 ^ 2 + 1) ^ betaP h * MvPolynomial.aeval v (twF k f) :=
    aeval_clearET v hv (EDeg_twF hE k)
  have hpsi : psiP G = (PowerSeries.X ^ 2 - 1) ^ betaP h * psiP f := by
    unfold psiP
    refine aeval_clearE _ ?_ hE
    simpa using EP_mul
  have hWk : Q.WLeP e B (psiP f) := by
    have := hW k
    rwa [Polynomial.coeff_map] at this
  have hWG : Q.WLeP e B (psiP G) := by
    rw [hpsi]
    have := Q.WLeP_mul (by positivity) hB (Q.WLeP_pow zero_le_one (Q.WLeP_qsq_sub_one e) (betaP h)) hWk
    rwa [one_pow, one_mul] at this
  have hGb : padicNorm 2 (MvPolynomial.aeval v GT) ≤ B := by
    rw [aeval_eq_sum_support]
    refine padicNorm.sum_le' (fun m hm => ?_) hB
    have hm0 := MvPolynomial.mem_support_iff.mp hm
    have hm1 : m 1 = 0 := Nat.le_zero.mp (EDeg_clearET _ _ m hm0)
    rw [hm1, pow_zero, mul_one, Algebra.algebraMap_self, RingHom.id_apply, padicNorm.mul,
      padicNorm_pow (ℓ := 2)]
    have hGm : G.coeff m ≠ 0 := coeff_clearET_ne_zero hE hpar hm0
    have hc := hWG (m 0)
    rw [coeff_psiP_of_EDeg0 (EDeg_clearE _ _) m hGm] at hc
    rw [hGT, padicNorm_coeff_clearET k _ f hE hpar m, ← hG]
    have hv0 : v 0 = q := rfl
    rw [hv0, hqe, ← zpow_natCast, ← zpow_mul]
    calc padicNorm 2 (G.coeff m) * (2 : ℚ) ^ (-(e : ℤ) * (m 0 : ℕ))
        ≤ B * (2 : ℚ) ^ (e * m 0) * (2 : ℚ) ^ (-(e : ℤ) * (m 0 : ℕ)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = B := by
          rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
          push_cast; ring_nf; simp
  rw [coeff_DeltaT_eq hq]
  have hu : padicNorm 2 ((v 0 ^ 2 + 1) ^ betaP h) = 1 := by
    rw [padicNorm_pow (ℓ := 2)]
    have : v 0 = q := rfl
    rw [this, padicNorm_qsqT_unit' hodd, one_pow]
  have := congrArg (padicNorm 2) hcl
  rw [padicNorm.mul, hu, one_mul] at this
  rw [← this]
  exact hGb

/-! ### Step 5: the limit -/

lemma c2EvenSharp_eq' (q : ℕ) :
    Q.c2EvenSharp q = -(((padicValNat 2 q : ℝ) - 2 * ((padicValNat 2 q : ℝ) + 1) ^ 2 /
      (3 * padicValNat 2 q + 8))) * Real.log 2 := by
  unfold Q.c2EvenSharp Q.cE
  congr 1
  push_cast
  have : (3 * (padicValNat 2 q : ℝ) + 8) ≠ 0 := by positivity
  field_simp
  ring

/-- **Lemma 10_e for Ti**: the exact statement of `TiQ.twoAdic_even_t`. -/
theorem twoAdic_even_t_proof (q : ℕ) (hq : 3 ≤ q) (he : Even q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (Q.c2EvenSharp q + ε) * (h : ℝ) ^ 2 := by
  set e := padicValNat 2 q with he_def
  have hq0 : q ≠ 0 := by omega
  have he1 : 1 ≤ e := one_le_padicValNat_of_dvd hq0 (even_iff_two_dvd.mp he)
  have hqe : padicNorm 2 (q : ℚ) = (2 : ℚ) ^ (-(e : ℤ)) := by
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hq0), padicValRat.of_nat, Nat.cast_ofNat]
  refine ⟨Q.n2E e, fun h k => padicNorm_DeltaT_of_WLe (by omega) (odd_sq_add_one he) hqe
    (by positivity) (Q.WLe_DeltaP e he1 h) k, ?_⟩
  intro ε hε
  rw [c2EvenSharp_eq', ← he_def]
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 * (e : ℝ) + 10) / ε + 256 / ε ^ 2)
  refine eventually_atTop.2 ⟨N, fun h hh => ?_⟩
  have hhN : (N : ℝ) ≤ h := by exact_mod_cast hh
  have hε2 : 0 < ε ^ 2 := by positivity
  have hA : (3 * (e : ℝ) + 10) / ε ≤ h := by
    have : 0 ≤ 256 / ε ^ 2 := by positivity
    linarith
  have hB : 256 / ε ^ 2 ≤ h := by
    have : 0 ≤ (3 * (e : ℝ) + 10) / ε := by positivity
    linarith
  rw [div_le_iff₀ hε] at hA
  rw [div_le_iff₀ hε2] at hB
  have hh0 : (0 : ℝ) ≤ h := by positivity
  set t := Nat.log 2 h with ht
  -- `t² ≤ 4h`
  have htt : (t : ℝ) ^ 2 ≤ 4 * h := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [ht, h0]; simp
    · have h1 := Q.sq_add_le_two_pow t
      have h2 : 2 ^ t ≤ h := Nat.pow_log_le_self 2 (by omega)
      have h3 : t ^ 2 ≤ 4 * h := by
        have : 2 ^ (t + 2) = 4 * 2 ^ t := by ring
        omega
      exact_mod_cast h3
  have h4t : 4 * (t : ℝ) ≤ ε * h / 2 := by
    have hsq : (4 * (t : ℝ)) ^ 2 ≤ (ε * h / 2) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  -- `n₂ ≤ h − R(h)`
  have hceil : ((⌈Q.Rbd e h⌉ : ℤ) : ℝ) ≥ ((Q.Rbd e h : ℚ) : ℝ) := by
    have := Int.le_ceil (Q.Rbd e h)
    have h' : ((Q.Rbd e h : ℚ) : ℝ) ≤ (((⌈Q.Rbd e h⌉ : ℤ) : ℚ) : ℝ) := Rat.cast_le.mpr this
    rwa [Rat.cast_intCast] at h'
  have hR : ((Q.Rbd e h : ℚ) : ℝ) = ((e : ℝ) - 2 * ((e : ℝ) + 1) ^ 2 / (3 * e + 8)) * (h : ℝ) ^ 2 -
      h * (3 * (e : ℝ) / 2 + 4 * (t : ℝ) + 4) := by
    unfold Q.Rbd; push_cast; rfl
  have hn : (Q.n2E e h : ℝ) ≤ -((e : ℝ) - 2 * ((e : ℝ) + 1) ^ 2 / (3 * e + 8)) * (h : ℝ) ^ 2 +
      h * (3 * (e : ℝ) / 2 + 5 + 4 * (t : ℝ)) := by
    unfold Q.n2E; push_cast; rw [hR] at hceil; nlinarith
  set m := ((e : ℝ) - 2 * ((e : ℝ) + 1) ^ 2 / (3 * e + 8))
  have hsmall : h * (3 * (e : ℝ) / 2 + 5 + 4 * (t : ℝ)) ≤ ε * (h : ℝ) ^ 2 := by nlinarith
  have hpos : 0 ≤ h * (3 * (e : ℝ) / 2 + 5 + 4 * (t : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hn hL0.le]

end TiQ
end Chi2Irr
