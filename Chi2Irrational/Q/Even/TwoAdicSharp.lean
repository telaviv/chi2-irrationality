/-
# Lemma 10_e (`pilot_qeven/RESULT.md` §2): the sharp 2-adic bound at even `q`

`twoAdic_even_sharp_proof` (the exact statement of the stub `Q.twoAdic_even_sharp`, `Q/Even/Interface.lean`):
for even `q ≥ 3`, `e = v₂(q)`, every coefficient of `Δ_h = Delta q h` has `‖·‖₂ ≤ 2^{n₂(h)}` with
`n₂(h) = h − ⌈R(h)⌉`, `R(h) = m_e h² − h(3e/2 + 4⌊log₂ h⌋ + 4)`, `m_e = e − 2(e+1)²/(3e+8)`, so the limit constant is
`−m_e · log 2 = (c(e) − e/3) · log 2 = c2EvenSharp q`.

Chain (plan: `scripts/q/l10e_plan.md`):
1. `WLe_term_all`: every Andreief term of the truncated slot matrix `Mdec M h` (Lemma 4′, `Arith/QAdic.lean`) has
   `‖·‖_{v_e} ≤ 2^{−⌈R(h)⌉}` (`WLe_term` + `nu_ge`; terms with a repeated `X`- or `Y`-key vanish);
2. `WLe_det_Mdec`: Andreief (`factorial_smul_det_sum_rankOne`) and `|1/h!|₂ ≤ 2^h`;
3. `WLe_DeltaP`: `det HPser ≡ det Mdec` modulo `q^{2M}` (as in `ord_DeltaP`), for every `M`;
4. `padicNorm_Delta_of_WLe`: specialisation at `q₀` with `|q₀|₂ = 2^{−e}`, `q₀² − 1` odd (clearing `E` as in
   `padicNorm_Delta_clear`);
5. the limit.
-/
import Chi2Irrational.Q.Even.Defs
import Chi2Irrational.Q.Even.NuBound
import Chi2Irrational.Q.TwoAdicEven

namespace Chi2Irr
namespace Q

open Finset Filter
open scoped Nat

/-- The exponent `n₂(h) = h − ⌈R(h)⌉`. -/
noncomputable def n2E (e h : ℕ) : ℤ := h - ⌈Rbd e h⌉

/-! ### Step 1: each term -/

lemma WLe_term_all (e : ℕ) (he : 1 ≤ e) (M h : ℕ) (f : Fin h → SIdx M h) :
    WLe e ((2 : ℚ) ^ (-⌈Rbd e h⌉))
      ((∏ i, ccS M h (f i)) * (Matrix.of fun i j => xS M h (f i) j).det *
        (Matrix.of fun i j => yS M h (f i) j).det) := by
  by_cases hx : Function.Injective (fun i => skey (f i))
  · by_cases hy : Function.Injective (fun i => ykey (f i))
    · refine WLe_mono ?_ (WLe_term e (Nat.log 2 h + 1) (Nat.log 2 (univ.sup fun i => nodeM (f i))) f
        (hz_der f))
      have hc := Int.ceil_le.mpr (nu_ge f hx hy e he)
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    · obtain ⟨i, i', heq, hne⟩ := Function.not_injective_iff.mp hy
      have h0 : (Matrix.of fun i j => yS M h (f i) j).det = 0 :=
        Matrix.det_zero_of_row_eq hne (by funext j; simp only [Matrix.of_apply, yS_eq_of_ykey heq])
      rw [h0, mul_zero]; exact WLe_zero (by positivity)
  · obtain ⟨i, i', heq, hne⟩ := Function.not_injective_iff.mp hx
    have h0 : (Matrix.of fun i j => xS M h (f i) j).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by funext j; simp only [Matrix.of_apply, xS_eq_of_skey heq])
    rw [h0, mul_zero, zero_mul]; exact WLe_zero (by positivity)

/-! ### Step 2: the truncated determinant -/

lemma padicNorm_inv_factorial_le (h : ℕ) : padicNorm 2 ((h ! : ℚ))⁻¹ ≤ 2 ^ h := by
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one, padicNorm_factorial, one_div, ← zpow_neg, neg_neg,
    ← zpow_natCast]
  exact zpow_le_zpow_right₀ (by norm_num) (by have := vf_le h; omega)

lemma WLe_det_Mdec (e : ℕ) (he : 1 ≤ e) (M h : ℕ) : WLe e ((2 : ℚ) ^ (n2E e h)) (Mdec M h).det := by
  have hA := factorial_smul_det_sum_rankOne (ccS M h) (xS M h) (yS M h)
  rw [Fintype.card_fin] at hA
  have hsum : WLe e ((2 : ℚ) ^ (-⌈Rbd e h⌉)) (h ! • (Mdec M h).det) := by
    unfold Mdec; rw [hA]
    exact WLe_sum _ (by positivity) _ (fun f _ => WLe_term_all e he M h f)
  have hfac : ((h ! : ℚ))⁻¹ • (h ! • (Mdec M h).det) = (Mdec M h).det := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero h),
      one_smul]
  rw [← hfac, Algebra.smul_def]
  refine WLe_mono ?_ (WLe_smul _ hsum)
  unfold n2E
  rw [sub_eq_add_neg, zpow_add₀ two_ne_zero, zpow_natCast]
  exact mul_le_mul_of_nonneg_right (padicNorm_inv_factorial_le h) (by positivity)

/-! ### Step 3: truncation -/

lemma WLe_DeltaP (e : ℕ) (he : 1 ≤ e) (h : ℕ) :
    WLe e ((2 : ℚ) ^ (n2E e h)) ((DeltaF h).map psiP.toRingHom) := by
  intro j n
  set M := n + 1
  have hdet : (DeltaF h).map psiP.toRingHom = (HPser h).det := by
    unfold DeltaF HPser
    rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
    rfl
  have hdiff : (HPser h).det - (Mdec M h).det ∈ Jq (2 * M) := by
    rw [← Ideal.Quotient.eq, RingHom.map_det (Ideal.Quotient.mk _) (HPser h),
      RingHom.map_det (Ideal.Quotient.mk _) (Mdec M h)]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (HPm_sub_Mdec_mem M h i j)
  have hd := coeff_dvd_of_mem_Jq hdiff j
  have h0 := PowerSeries.X_pow_dvd_iff.mp hd n (by omega)
  rw [Polynomial.coeff_sub, map_sub, sub_eq_zero] at h0
  rw [hdet, h0]
  exact WLe_det_Mdec e he M h j n

/-! ### Step 4: specialisation at `q₀` -/

lemma WLeP_qsq_sub_one (e : ℕ) : WLeP e 1 ((PowerSeries.X : PowerSeries ℚ) ^ 2 - 1) := by
  have h1 := WLeP_C_mul_X_pow (e := e) 1 2
  rw [map_one, one_mul, padicNorm.one, one_mul] at h1
  have h2 : WLeP e 1 ((PowerSeries.X : PowerSeries ℚ) ^ 2) :=
    WLeP_mono (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) h1
  rw [sub_eq_add_neg]
  exact WLeP_add h2 (WLeP_neg WLeP_one)

theorem padicNorm_Delta_of_WLe {q e h : ℕ} (hq : 2 ≤ q) (hodd : ¬ 2 ∣ q ^ 2 - 1)
    (hqe : padicNorm 2 (q : ℚ) = (2 : ℚ) ^ (-(e : ℤ))) {B : ℚ} (hB : 0 ≤ B)
    (hW : WLe e B ((DeltaF h).map psiP.toRingHom)) (k : ℕ) : padicNorm 2 ((Delta q h).coeff k) ≤ B := by
  set G := clearE (betaP h) ((DeltaF h).coeff k) with hG
  set v : Fin 2 → ℚ := ![(q : ℚ), 1 / ((q : ℚ) ^ 2 - 1)] with hvdef
  have hv : v 1 * (v 0 ^ 2 - 1) = 1 := by
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    field_simp [qsq_ne_zero hq]
  have hcl : MvPolynomial.aeval v G = (v 0 ^ 2 - 1) ^ betaP h * MvPolynomial.aeval v ((DeltaF h).coeff k) :=
    aeval_clearE v hv (EDeg_DeltaF h k)
  have hpsi : psiP G = (PowerSeries.X ^ 2 - 1) ^ betaP h * psiP ((DeltaF h).coeff k) := by
    unfold psiP
    refine aeval_clearE _ ?_ (EDeg_DeltaF h k)
    simpa using EP_mul
  have hWk : WLeP e B (psiP ((DeltaF h).coeff k)) := by
    have := hW k
    rwa [Polynomial.coeff_map] at this
  have hWG : WLeP e B (psiP G) := by
    rw [hpsi]
    have := WLeP_mul (by positivity) hB (WLeP_pow zero_le_one (WLeP_qsq_sub_one e) (betaP h)) hWk
    rwa [one_pow, one_mul] at this
  have hGb : padicNorm 2 (MvPolynomial.aeval v G) ≤ B := by
    rw [aeval_eq_sum_support]
    refine padicNorm.sum_le' (fun m hm => ?_) hB
    have hm0 := MvPolynomial.mem_support_iff.mp hm
    have hm1 : m 1 = 0 := Nat.le_zero.mp (EDeg_clearE _ _ m hm0)
    rw [hm1, pow_zero, mul_one, Algebra.algebraMap_self, RingHom.id_apply, padicNorm.mul,
      padicNorm_pow (ℓ := 2)]
    have hc := hWG (m 0)
    rw [coeff_psiP_of_EDeg0 (EDeg_clearE _ _) m hm0] at hc
    have hv0 : v 0 = q := rfl
    rw [hv0, hqe, ← zpow_natCast, ← zpow_mul]
    calc padicNorm 2 (G.coeff m) * (2 : ℚ) ^ (-(e : ℤ) * (m 0 : ℕ))
        ≤ B * (2 : ℚ) ^ (e * m 0) * (2 : ℚ) ^ (-(e : ℤ) * (m 0 : ℕ)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = B := by
          rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
          push_cast; ring_nf; simp
  rw [coeff_Delta_eq hq]
  have hu : padicNorm 2 ((v 0 ^ 2 - 1) ^ betaP h) = 1 := by
    rw [padicNorm_pow (ℓ := 2)]
    have : v 0 = q := rfl
    rw [this, padicNorm_qsq_unit hq hodd, one_pow]
  have := congrArg (padicNorm 2) hcl
  rw [padicNorm.mul, hu, one_mul] at this
  rw [← this]
  exact hGb

/-! ### Step 5: the limit -/

lemma c2EvenSharp_eq (q : ℕ) :
    c2EvenSharp q = -(((padicValNat 2 q : ℝ) - 2 * ((padicValNat 2 q : ℝ) + 1) ^ 2 /
      (3 * padicValNat 2 q + 8))) * Real.log 2 := by
  unfold c2EvenSharp cE
  congr 1
  push_cast
  have : (3 * (padicValNat 2 q : ℝ) + 8) ≠ 0 := by positivity
  field_simp
  ring

/-- **Lemma 10_e**: the exact statement of `Q.twoAdic_even_sharp`. -/
theorem twoAdic_even_sharp_proof (q : ℕ) (hq : 3 ≤ q) (he : Even q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2EvenSharp q + ε) * (h : ℝ) ^ 2 := by
  set e := padicValNat 2 q with he_def
  have hq0 : q ≠ 0 := by omega
  have he1 : 1 ≤ e := one_le_padicValNat_of_dvd hq0 (even_iff_two_dvd.mp he)
  have hqe : padicNorm 2 (q : ℚ) = (2 : ℚ) ^ (-(e : ℤ)) := by
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hq0), padicValRat.of_nat, Nat.cast_ofNat]
  refine ⟨n2E e, fun h k => padicNorm_Delta_of_WLe (by omega) (not_two_dvd_qsq (by omega) he) hqe
    (by positivity) (WLe_DeltaP e he1 h) k, ?_⟩
  intro ε hε
  rw [c2EvenSharp_eq, ← he_def]
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
    · have h1 := sq_add_le_two_pow t
      have h2 : 2 ^ t ≤ h := Nat.pow_log_le_self 2 (by omega)
      have h3 : t ^ 2 ≤ 4 * h := by
        have : 2 ^ (t + 2) = 4 * 2 ^ t := by ring
        omega
      exact_mod_cast h3
  have h4t : 4 * (t : ℝ) ≤ ε * h / 2 := by
    have hsq : (4 * (t : ℝ)) ^ 2 ≤ (ε * h / 2) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  -- `n₂ ≤ h − R(h)`
  have hceil : ((⌈Rbd e h⌉ : ℤ) : ℝ) ≥ ((Rbd e h : ℚ) : ℝ) := by
    have := Int.le_ceil (Rbd e h)
    have h' : ((Rbd e h : ℚ) : ℝ) ≤ (((⌈Rbd e h⌉ : ℤ) : ℚ) : ℝ) := Rat.cast_le.mpr this
    rwa [Rat.cast_intCast] at h'
  have hR : ((Rbd e h : ℚ) : ℝ) = ((e : ℝ) - 2 * ((e : ℝ) + 1) ^ 2 / (3 * e + 8)) * (h : ℝ) ^ 2 -
      h * (3 * (e : ℝ) / 2 + 4 * (t : ℝ) + 4) := by
    unfold Rbd; push_cast; rfl
  have hn : (n2E e h : ℝ) ≤ -((e : ℝ) - 2 * ((e : ℝ) + 1) ^ 2 / (3 * e + 8)) * (h : ℝ) ^ 2 +
      h * (3 * (e : ℝ) / 2 + 5 + 4 * (t : ℝ)) := by
    unfold n2E; push_cast; rw [hR] at hceil; nlinarith
  set m := ((e : ℝ) - 2 * ((e : ℝ) + 1) ^ 2 / (3 * e + 8))
  have hsmall : h * (3 * (e : ℝ) / 2 + 5 + 4 * (t : ℝ)) ≤ ε * (h : ℝ) ^ 2 := by nlinarith
  have hpos : 0 ≤ h * (3 * (e : ℝ) / 2 + 5 + 4 * (t : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hn hL0.le]

end Q
end Chi2Irr
