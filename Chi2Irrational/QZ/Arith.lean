/-
# Theorem Q4′: the arithmetic bound at `ζ = q/2`, odd primes (`pilot_chi2_2q/RESULT.md` §1, §4)

Port of `Q/Arith.lean` from `Delta q` (integer `q`) to `DeltaZ (q/2)` (odd `q ≥ 5`). Every `p`-adic input is a Gauss-norm
bound on the symbolic machine `DeltaF h` over `ℚ[q, E]` (`Arith/*`), specialised at `v = (ζ, 1/(ζ² − 1))`
(`QZ.coeff_DeltaZ_eq`). For an odd prime `p`, `ζ = q/2` has `‖ζ‖_p = ‖q‖_p ≤ 1` and `‖ζ² − 1‖_p = ‖q² − 4‖_p`, so
(RESULT §1, "q₀ ∈ ℤ_(p)"):
* odd `p ∣ q(q² − 4)`: `‖c‖_p ≤ p^{2h·lev + v_p(q²−4)·βp(h)} · ‖q‖_p^{aQ h}` (Lemma 9 after clearing `E`, and Lemma 4′(ii));
* other odd `p`: `‖c‖_p ≤ p^{eGen h p}` (Theorem A).
`p = 2` is the hypothesis `‖c‖₂ ≤ 2^{n₂(h)}` (Lemma 10″, `twoAdic_num`). Denominator
`denz q n₂ h = 2^{n₂ h} · N / q^{aQ h}`, `N = ∏_{odd p ≤ 2h + q²} p^{eNz}`; its size is
`n₂ log 2 + (133/60 + ¼ log(q² − 4) − ⅓ log q + o(1)) h²` (`q` and `q² − 4` are odd).
-/
import Chi2Irrational.QZ.Defs
import Chi2Irrational.Q.Arith

namespace Chi2Irr
namespace QZ

open Finset Filter

/-! ### `ζ = q/2` at an odd prime -/

lemma padicNorm_two_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : padicNorm p (2 : ℚ) = 1 := by
  have := padicNorm_prime_nat (p := p) Nat.prime_two
  rw [ite_eq_right (fun h => hp2 h.symm)] at this
  exact_mod_cast this

lemma padicNorm_zq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (q : ℕ) : padicNorm p (zq q) = padicNorm p (q : ℚ) := by
  unfold zq; rw [padicNorm.div, padicNorm_two_odd hp2, div_one]

lemma one_lt_zq {q : ℕ} (hq : 3 ≤ q) : 1 < zq q := by
  unfold zq
  have : (3 : ℚ) ≤ q := by exact_mod_cast hq
  linarith

lemma zq_sq_sub_one {q : ℕ} (hq : 3 ≤ q) : zq q ^ 2 - 1 = ((q ^ 2 - 4 : ℕ) : ℚ) / 4 := by
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  unfold zq
  rw [Nat.cast_sub h4]; push_cast; ring

lemma qsq4_ne_zero {q : ℕ} (hq : 3 ≤ q) : q ^ 2 - 4 ≠ 0 := by
  have : 9 ≤ q ^ 2 := by nlinarith
  omega

lemma padicNorm_zq_sq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {q : ℕ} (hq : 3 ≤ q) :
    padicNorm p (zq q ^ 2 - 1) = padicNorm p ((q ^ 2 - 4 : ℕ) : ℚ) := by
  rw [zq_sq_sub_one hq, padicNorm.div]
  have : padicNorm p (4 : ℚ) = 1 := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, padicNorm_pow (ℓ := p), padicNorm_two_odd hp2, one_pow]
  rw [this, div_one]

/-! ### Per-prime bounds -/

/-- **Generic odd primes** at `ζ = q/2` (Theorem A). -/
theorem padicNorm_DeltaZ_gen {p q : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 3 ≤ q) (hpq : ¬ p ∣ q ^ 2 - 4)
    (h k : ℕ) : padicNorm p ((DeltaZ (zq q) h).coeff k) ≤ (p : ℚ) ^ eGen h p := by
  rw [coeff_DeltaZ_eq (one_lt_zq hq)]
  refine GLe_ev (GLeX_eGen hp2 h k) (by positivity) _ ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simpa [padicNorm_zq hp2] using padicNorm_nat_le_one p q
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [padicNorm.div, padicNorm_zq_sq hp2 hq, (padicNorm.nat_eq_one_iff _).mpr hpq, padicNorm.one, div_one]

/-- Clearing `E` at `ζ = q/2` (odd `p`). -/
lemma padicNorm_DeltaZ_clear {p q : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B : ℚ} (hB : 0 ≤ B) (hq : 3 ≤ q)
    (h k a : ℕ) (hf : GLe p B ((DeltaF h).coeff k))
    (ha : ∀ m, (clearE (betaP h) ((DeltaF h).coeff k)).coeff m ≠ 0 → a ≤ m 0) :
    padicNorm p ((q ^ 2 - 4 : ℕ) : ℚ) ^ betaP h * padicNorm p ((DeltaZ (zq q) h).coeff k) ≤
      B * padicNorm p (q : ℚ) ^ a := by
  set v : Fin 2 → ℚ := ![zq q, 1 / (zq q ^ 2 - 1)]
  have hv : v 1 * (v 0 ^ 2 - 1) = 1 := by
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    field_simp [zsq_sub_one_ne_zero (one_lt_zq hq)]
  have hcl := aeval_clearE v hv (EDeg_DeltaF h k)
  have hb := padicNorm_aeval_le_of_qdeg hB (GLe_clearE hB hf (betaP h)) (EDeg_clearE _ _) a ha v
    (by simpa [v, padicNorm_zq hp2] using padicNorm_nat_le_one p q)
  rw [hcl, padicNorm.mul, padicNorm_pow (ℓ := p)] at hb
  rw [coeff_DeltaZ_eq (one_lt_zq hq)]
  simpa [v, padicNorm_zq hp2, padicNorm_zq_sq hp2 hq] using hb

/-- The exponent of an odd prime `p` in the numerator. -/
noncomputable def eNz (q h p : ℕ) : ℕ :=
  if p ∣ q ∨ p ∣ q ^ 2 - 4 then 2 * h * lev h p + padicValNat p (q ^ 2 - 4) * betaP h else eGen h p

/-- **Odd primes** at `ζ = q/2`: Lemma 9 + Lemma 4′(ii) at the special primes, Theorem A elsewhere. -/
theorem padicNorm_DeltaZ_odd {q p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 3 ≤ q) (h k : ℕ) :
    padicNorm p ((DeltaZ (zq q) h).coeff k) ≤ (p : ℚ) ^ eNz q h p * padicNorm p ((q : ℚ) ^ aQ h) := by
  rw [padicNorm_pow (ℓ := p)]
  unfold eNz
  split_ifs with hs
  · have hcl := padicNorm_DeltaZ_clear hp2 (p := p) (by positivity) hq h k (aQ h) (lemma9_DeltaF hp2 h k)
      (fun m hm => qdeg_clearE_DeltaF h k m hm)
    have hu : padicNorm p ((q ^ 2 - 4 : ℕ) : ℚ) = ((p : ℚ) ^ padicValNat p (q ^ 2 - 4))⁻¹ := by
      rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast qsq4_ne_zero hq), padicValRat.of_nat, zpow_neg,
        zpow_natCast]
    rw [hu, inv_pow, ← pow_mul] at hcl
    have hpos : (0 : ℚ) < (p : ℚ) ^ (padicValNat p (q ^ 2 - 4) * betaP h) := by
      have := (Fact.out : p.Prime).pos; positivity
    rw [inv_mul_le_iff₀ hpos] at hcl
    rw [pow_add]
    calc padicNorm p ((DeltaZ (zq q) h).coeff k)
        ≤ (p : ℚ) ^ (padicValNat p (q ^ 2 - 4) * betaP h) *
            ((p : ℚ) ^ (2 * h * lev h p) * padicNorm p (q : ℚ) ^ aQ h) := hcl
      _ = _ := by ring
  · push Not at hs
    have hu : padicNorm p (q : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr hs.1
    rw [hu, one_pow, mul_one]
    exact padicNorm_DeltaZ_gen hp2 hq hs.2 h k

/-! ### The common denominator -/

/-- The odd primes that may occur. -/
def SPz (q h : ℕ) : Finset ℕ := (range (2 * h + q ^ 2 + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- The odd numerator. -/
noncomputable def Nz (q h : ℕ) : ℕ := ∏ p ∈ SPz q h, p ^ eNz q h p

/-- **The denominator** `2^{n₂ h} · N / q^{aQ h}`. -/
noncomputable def denz (q : ℕ) (n2 : ℕ → ℤ) (h : ℕ) : ℚ :=
  (2 : ℚ) ^ n2 h * (Nz q h : ℚ) / (q : ℚ) ^ aQ h

lemma eNz_eq_zero {q h p : ℕ} (hq : 3 ≤ q) (hbig : 2 * h + q ^ 2 + 1 ≤ p) : eNz q h p = 0 := by
  have hq2 : 9 ≤ q ^ 2 := by nlinarith
  have hqq : q < q ^ 2 := by nlinarith
  unfold eNz
  rw [ite_eq_right]
  · unfold eGen
    rw [ite_eq_left ⟨by nlinarith, by omega⟩]
    exact classBd_eq_zero (by omega)
  · rintro (hd | hd)
    · have := Nat.le_of_dvd (by omega) hd; omega
    · have := Nat.le_of_dvd (by omega) hd; omega

lemma padicNorm_Nz {q h p : ℕ} [Fact p.Prime] (hq : 3 ≤ q) :
    padicNorm p (Nz q h : ℚ) = if p = 2 then 1 else ((p : ℚ)⁻¹) ^ eNz q h p := by
  unfold Nz
  rw [Nat.cast_prod, padicNorm_prod']
  rw [prod_congr rfl (fun p' hp' => by
    rw [Nat.cast_pow, padicNorm_pow (ℓ := p), padicNorm_prime_nat (mem_filter.mp hp').2.1])]
  rw [prod_congr rfl (fun p' _ => (show (if p' = p then (p : ℚ)⁻¹ else 1) ^ eNz q h p' =
      if p' = p then ((p : ℚ)⁻¹) ^ eNz q h p else 1 by split_ifs with he <;> simp [he]))]
  rw [prod_ite_eq']
  split_ifs with hS h2 h2
  · exact absurd h2 (mem_filter.mp hS).2.2
  · rfl
  · rfl
  · have hbig : 2 * h + q ^ 2 + 1 ≤ p := by
      by_contra hc
      exact hS (mem_filter.mpr ⟨mem_range.mpr (by omega), Fact.out, h2⟩)
    rw [eNz_eq_zero hq hbig, pow_zero]

lemma denz_pos {q : ℕ} (hq : 3 ≤ q) (n2 : ℕ → ℤ) (h : ℕ) : 0 < denz q n2 h := by
  unfold denz Nz
  have : 0 < ∏ p ∈ SPz q h, p ^ eNz q h p := prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.1.pos _)
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  positivity

/-- **Integrality.** `denz · Δ_h ∈ ℤ[X]` at `ζ = q/2`, odd `q`. -/
theorem denz_int {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((DeltaZ (zq q) h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (h k : ℕ) :
    ∃ z : ℤ, denz q n2 h * (DeltaZ (zq q) h).coeff k = z := by
  refine exists_int_of_padicNorm_le _ (fun p hp => ?_)
  have := Fact.mk hp
  have hQ : ((q : ℚ) ^ aQ h) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show q ≠ 0 by omega))
  have hn : 0 < padicNorm p ((q : ℚ) ^ aQ h) := lt_of_le_of_ne (padicNorm.nonneg _)
    (fun h0 => hQ (padicNorm.zero_of_padicNorm_eq_zero h0.symm))
  unfold denz
  rw [padicNorm.mul, padicNorm.div, padicNorm.mul, padicNorm_Nz hq]
  by_cases h2 : p = 2
  · subst h2
    rw [ite_eq_left rfl]
    have hu : padicNorm 2 (q : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr (by have := Nat.odd_iff.mp ho; omega)
    rw [padicNorm_pow (ℓ := 2), hu, one_pow, div_one, mul_one, Q.padicNorm_two_zpow]
    calc (2 : ℚ) ^ (-n2 h) * padicNorm 2 ((DeltaZ (zq q) h).coeff k) ≤ (2 : ℚ) ^ (-n2 h) * (2 : ℚ) ^ (n2 h) :=
          mul_le_mul_of_nonneg_left (hn2 h k) (by positivity)
      _ = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  · rw [ite_eq_right h2, Q.padicNorm_odd_two_zpow h2, one_mul]
    have hc := padicNorm_DeltaZ_odd h2 hq h k
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
    calc ((p : ℚ)⁻¹) ^ eNz q h p / padicNorm p ((q : ℚ) ^ aQ h) * padicNorm p ((DeltaZ (zq q) h).coeff k)
        ≤ ((p : ℚ)⁻¹) ^ eNz q h p / padicNorm p ((q : ℚ) ^ aQ h) *
            ((p : ℚ) ^ eNz q h p * padicNorm p ((q : ℚ) ^ aQ h)) :=
          mul_le_mul_of_nonneg_left hc (div_nonneg (by positivity) hn.le)
      _ = 1 := by
          rw [inv_pow]
          field_simp

/-! ### The size of the denominator -/

/-- The special odd primes. -/
def TSz (q h : ℕ) : Finset ℕ := (SPz q h).filter (fun p => p ∣ q ∨ p ∣ q ^ 2 - 4)

lemma TSz_sub {q h : ℕ} (hq : 3 ≤ q) : TSz q h ⊆ range (q ^ 2 + 1) := by
  intro p hp
  have hq2 : 9 ≤ q ^ 2 := by nlinarith
  have hqq : q < q ^ 2 := by nlinarith
  rw [mem_range]
  rcases (mem_filter.mp hp).2 with hd | hd
  · have := Nat.le_of_dvd (by omega) hd; omega
  · have := Nat.le_of_dvd (by omega) hd; omega

lemma eNz_log_le {q h p : ℕ} :
    (eNz q h p : ℝ) * Real.log p ≤ (eGen h p : ℝ) * Real.log p +
      (if p ∣ q ∨ p ∣ q ^ 2 - 4 then
        2 * (h : ℝ) * lev h p * Real.log p + betaP h * ((padicValNat p (q ^ 2 - 4) : ℝ) * Real.log p)
       else 0) := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  unfold eNz
  split_ifs
  · have : 0 ≤ (eGen h p : ℝ) * Real.log p := by positivity
    push_cast; nlinarith
  · simp

/-- **The size of the denominator**, for `h ≥ 13`. -/
theorem log_denz_le {q : ℕ} (hq : 3 ≤ q) (n2 : ℕ → ℤ) {h : ℕ} (hh : 13 ≤ h) :
    Real.log ((denz q n2 h : ℚ) : ℝ) ≤ (n2 h : ℝ) * Real.log 2 +
      ∑ p ∈ F1 h, 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p +
        ∑ p ∈ F2 h, (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p +
        (Real.log (q ^ 2 - 4 : ℕ) / 4 - Real.log q / 3) * (h : ℝ) ^ 2 +
        ((q : ℝ) ^ 2 + 1 + Real.log (q ^ 2 - 4 : ℕ) + Real.log q) *
          (30 * h + 6 * h * Real.log h) := by
  set H : ℝ := (h : ℝ) with hH
  have hH1 : (13 : ℝ) ≤ H := by rw [hH]; exact_mod_cast hh
  have hq1 : q ^ 2 - 4 ≠ 0 := qsq4_ne_zero hq
  set L1 : ℝ := Real.log (q ^ 2 - 4 : ℕ) with hL1
  set L2 : ℝ := Real.log q with hL2
  have hL10 : 0 ≤ L1 := Real.log_natCast_nonneg _
  have hL20 : 0 ≤ L2 := Real.log_natCast_nonneg _
  have hNpos : 0 < Nz q h := prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.1.pos _)
  have hop : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hden : ((denz q n2 h : ℚ) : ℝ) = (2 : ℝ) ^ n2 h * (Nz q h : ℝ) / (q : ℝ) ^ aQ h := by
    unfold denz; push_cast; ring
  rw [hden, Real.log_div (by positivity) (pow_ne_zero _ hop.ne'), Real.log_mul (by positivity)
    (by exact_mod_cast hNpos.ne'), Real.log_zpow, Real.log_pow]
  have hlogN : Real.log (Nz q h) = ∑ p ∈ SPz q h, (eNz q h p : ℝ) * Real.log p := by
    unfold Nz
    push_cast
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (mem_filter.mp hp).2.1.ne_zero))]
    simp only [Real.log_pow]
  rw [hlogN, ← hL2]
  have hs : ∀ p ∈ SPz q h, p.Prime ∧ p ≠ 2 := fun p hp => (mem_filter.mp hp).2
  have hsplit : ∑ p ∈ SPz q h, (eNz q h p : ℝ) * Real.log p ≤
      ∑ p ∈ SPz q h, (eGen h p : ℝ) * Real.log p +
        (∑ p ∈ TSz q h, 2 * H * lev h p * Real.log p +
          betaP h * ∑ p ∈ TSz q h, (padicValNat p (q ^ 2 - 4) : ℝ) * Real.log p) := by
    refine (sum_le_sum (fun p hp => eNz_log_le (q := q) (h := h) (p := p))).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, mul_sum, ← sum_add_distrib]
    rfl
  have hgen := sum_eGen_le hh (SPz q h) hs
  have hlev : ∑ p ∈ TSz q h, 2 * H * lev h p * Real.log p ≤ ((q : ℝ) ^ 2 + 1) * (2 * H * (1 + Real.log H)) := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hb : ∀ p ∈ TSz q h, 2 * H * lev h p * Real.log p ≤ 2 * H * (1 + Real.log H) := fun p hp => by
      have hpp := (hs p (mem_filter.mp hp).1).1
      have := lev_mul_log_le hpp (by omega : 1 ≤ h)
      rw [Real.log_mul (by norm_num) (by rw [hH] at hH1; positivity)] at this
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [← hH] at this; linarith) (by positivity)
    have hc : ((TSz q h).card : ℝ) ≤ (q : ℝ) ^ 2 + 1 := by
      have := card_le_card (TSz_sub (h := h) hq)
      rw [card_range] at this
      exact_mod_cast this
    have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    calc ∑ p ∈ TSz q h, 2 * H * lev h p * Real.log p ≤ ∑ p ∈ TSz q h, 2 * H * (1 + Real.log H) := sum_le_sum hb
      _ = ((TSz q h).card : ℝ) * (2 * H * (1 + Real.log H)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  have hv := Q.sum_padicValNat_log_le hq1 (TSz q h) (fun p hp => hs p (mem_filter.mp hp).1)
  have hv' : ∑ p ∈ TSz q h, (padicValNat p (q ^ 2 - 4) : ℝ) * Real.log p ≤ L1 := by
    refine hv.trans (Real.log_le_log (by exact_mod_cast Q.oddPart_pos hq1) ?_)
    exact_mod_cast Nat.div_le_self _ _
  have hβ : 4 * (betaP h : ℝ) ≤ H ^ 2 + 2 * H := by
    have := betaP_le h; rw [hH]; exact_mod_cast this
  have hβL : (betaP h : ℝ) * ∑ p ∈ TSz q h, (padicValNat p (q ^ 2 - 4) : ℝ) * Real.log p ≤
      (H ^ 2 + 2 * H) / 4 * L1 :=
    (mul_le_mul_of_nonneg_left hv' (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hL10)
  have haQ := aQ_ge (h := h) (by omega)
  rw [← hH] at haQ
  have haQl : ((H ^ 2 - 7 * H - 2) / 3) * L2 ≤ (aQ h : ℝ) * L2 := mul_le_mul_of_nonneg_right haQ hL20
  have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ 2 + 1 := by positivity
  have hrem : ((q : ℝ) ^ 2 + 1) * (2 * H * (1 + Real.log H)) + 2 * H / 4 * L1 + (7 * H + 2) / 3 * L2 ≤
      ((q : ℝ) ^ 2 + 1 + L1 + L2) * (30 * H + 6 * H * Real.log H) := by
    have e1 : ((q : ℝ) ^ 2 + 1) * (2 * H * (1 + Real.log H)) ≤ ((q : ℝ) ^ 2 + 1) * (30 * H + 6 * H * Real.log H) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hq0
    have e2 : 2 * H / 4 * L1 ≤ L1 * (30 * H + 6 * H * Real.log H) := by
      have : 0 ≤ 6 * H * Real.log H := by positivity
      nlinarith
    have e3 : (7 * H + 2) / 3 * L2 ≤ L2 * (30 * H + 6 * H * Real.log H) := by
      have : 0 ≤ 6 * H * Real.log H := by positivity
      nlinarith
    nlinarith
  nlinarith

lemma log_qsq4_cast {q : ℕ} (hq : 3 ≤ q) : Real.log ((q ^ 2 - 4 : ℕ) : ℝ) = Real.log ((q : ℝ) ^ 2 - 4) := by
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  rw [Nat.cast_sub h4]; push_cast; rfl

/-- **The arithmetic bound at `ζ = q/2`** (the exact statement of `arith_z`, `QZ/Interface.lean`). -/
theorem arith_z_proof (q : ℕ) (hq : 5 ≤ q) (ho : Odd q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((DeltaZ (zq q) h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (c2 : ℝ)
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2) :
    ∃ den : ℕ → ℚ, (∀ h, 0 < den h) ∧ (∀ h k, ∃ z : ℤ, den h * (DeltaZ (zq q) h).coeff k = z) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (alphaZ q + c2 + ε) * (h : ℝ) ^ 2 := by
  have hq3 : 3 ≤ q := by omega
  refine ⟨denz q n2, denz_pos hq3 n2, denz_int hq3 ho n2 hn2, fun ε hε => ?_⟩
  set C : ℝ := (q : ℝ) ^ 2 + 1 + Real.log (q ^ 2 - 4 : ℕ) + Real.log q with hC
  have hC0 : 0 < C := by
    have := Real.log_natCast_nonneg (q ^ 2 - 4)
    have := Real.log_natCast_nonneg q
    positivity
  filter_upwards [hc2 (ε / 4) (by positivity), eventually_primeSum_lev_le (ε / 4) (by positivity),
    eventually_primeSum_phi1_le (ε / 4) (by positivity), eventually_rem_le (ε / 4 / C) (by positivity),
    eventually_ge_atTop 13] with h h0 h1 h2 h3 h4
  have := log_denz_le hq3 n2 h4
  unfold F1 F2 at this
  rw [← hC, log_qsq4_cast hq3] at this
  have h3' : C * (30 * (h : ℝ) + 6 * (h : ℝ) * Real.log h) ≤ ε / 4 * (h : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 hC0.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hC0.ne'] at this
  unfold alphaZ
  nlinarith

end QZ
end Chi2Irr
