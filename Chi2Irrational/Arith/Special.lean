/-
# Per-prime bounds for the coefficients of `Δ_h = Delta q₀ h`, and the common denominator

For a prime `q₀` (we use `q₀ = 3, 5`), every coefficient `c` of `Δ_h` satisfies, prime by prime:
* `p = 2`: `‖c‖₂ ≤ 2^{βp(h) + h(⌊log₂ h⌋ + 6)}` (Lemma 10, `twoAdic_Delta`);
* `p = q₀`: `‖c‖_{q₀} ≤ q₀^{2h·lev} · q₀^{−aQ(h)}` (Lemma 9 + Lemma 4′, via `clearE`);
* odd `p ∣ q₀² − 1`: `‖c‖_p ≤ p^{2h·lev + v_p(q₀²−1)·βp(h)}` (Lemma 9 after clearing `E`);
* other odd `p`: `‖c‖_p ≤ p^{eGen h p}`, the class bound when `2h < p²` and `2h ≤ 5p`, else Lemma 9.
`denQ q₀ h = N/q₀^{aQ h}` with `N = ∏_{p ≤ 2h + q₀²} p^{eN}`; `denQ_int`: `denQ · c ∈ ℤ`.
-/
import Chi2Irrational.Arith.QAdic
import Chi2Irrational.Arith.ClassBound
import Chi2Irrational.Arith.ClassCount
import Chi2Irrational.Arith.TwoAdic

namespace Chi2Irr

open Finset

lemma coeff_Delta_eq {q₀ : ℕ} (hq : 2 ≤ q₀) (h k : ℕ) :
    (Delta q₀ h).coeff k = MvPolynomial.aeval ![(q₀ : ℚ), 1 / ((q₀ : ℚ) ^ 2 - 1)] ((DeltaF h).coeff k) := by
  rw [← map_DeltaF hq, Polynomial.coeff_map]; rfl

/-- The exponent of a generic odd prime. -/
def eGen (h p : ℕ) : ℕ := if 2 * h < p * p ∧ 2 * h ≤ 5 * p then classBd h p else 2 * h * lev h p

lemma GLeX_eGen {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h : ℕ) : GLeX p ((p : ℚ) ^ eGen h p) (DeltaF h) := by
  unfold eGen
  split_ifs with hc
  · have := classBound_DeltaF hp2 hc.1
    rwa [zpow_natCast] at this
  · exact lemma9_DeltaF hp2 h

lemma qsq_cast {q₀ : ℕ} (hq : 2 ≤ q₀) : (q₀ : ℚ) ^ 2 - 1 = ((q₀ ^ 2 - 1 : ℕ) : ℚ) := by
  rw [Nat.cast_sub (by nlinarith : 1 ≤ q₀ ^ 2)]; push_cast; ring

lemma qsq_ne_zero {q₀ : ℕ} (hq : 2 ≤ q₀) : (q₀ : ℚ) ^ 2 - 1 ≠ 0 := by
  rw [qsq_cast hq, Nat.cast_ne_zero]; have : 4 ≤ q₀ ^ 2 := by nlinarith
  omega

lemma padicNorm_qsq_unit {p q₀ : ℕ} [Fact p.Prime] (hq : 2 ≤ q₀) (hp : ¬ p ∣ q₀ ^ 2 - 1) :
    padicNorm p ((q₀ : ℚ) ^ 2 - 1) = 1 := by
  rw [qsq_cast hq, padicNorm.nat_eq_one_iff]; exact hp

lemma padicNorm_nat_le_one (p n : ℕ) [Fact p.Prime] : padicNorm p (n : ℚ) ≤ 1 := padicNorm.of_nat n

/-- **Generic odd primes.** -/
theorem padicNorm_Delta_gen {p q₀ : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 2 ≤ q₀) (hpq : ¬ p ∣ q₀ ^ 2 - 1)
    (h k : ℕ) : padicNorm p ((Delta q₀ h).coeff k) ≤ (p : ℚ) ^ eGen h p := by
  rw [coeff_Delta_eq hq]
  refine GLe_ev (GLeX_eGen hp2 h k) (by positivity) _ ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simpa using padicNorm_nat_le_one p q₀
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [padicNorm.div, padicNorm_qsq_unit hq hpq, padicNorm.one, div_one]

/-- The common setup for primes where `E` must be cleared. -/
lemma padicNorm_Delta_clear {p q₀ : ℕ} [Fact p.Prime] {B : ℚ} (hB : 0 ≤ B) (hq : 2 ≤ q₀)
    (h k a : ℕ) (hf : GLe p B ((DeltaF h).coeff k))
    (ha : ∀ m, (clearE (betaP h) ((DeltaF h).coeff k)).coeff m ≠ 0 → a ≤ m 0) :
    padicNorm p ((q₀ : ℚ) ^ 2 - 1) ^ betaP h * padicNorm p ((Delta q₀ h).coeff k) ≤
      B * padicNorm p (q₀ : ℚ) ^ a := by
  set v : Fin 2 → ℚ := ![(q₀ : ℚ), 1 / ((q₀ : ℚ) ^ 2 - 1)]
  have hv : v 1 * (v 0 ^ 2 - 1) = 1 := by
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    field_simp [qsq_ne_zero hq]
  have hcl := aeval_clearE v hv (EDeg_DeltaF h k)
  have hb := padicNorm_aeval_le_of_qdeg hB (GLe_clearE hB hf (betaP h)) (EDeg_clearE _ _) a ha v
    (by simpa [v] using padicNorm_nat_le_one p q₀)
  rw [hcl, padicNorm.mul, padicNorm_pow (ℓ := p)] at hb
  rw [coeff_Delta_eq hq]
  simpa [v] using hb

lemma not_dvd_qsq_self {q₀ : ℕ} (hq : q₀.Prime) : ¬ q₀ ∣ q₀ ^ 2 - 1 := by
  intro hd
  have h1 : q₀ ∣ q₀ ^ 2 - 1 + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hq.pos)]; exact dvd_pow_self _ two_ne_zero
  exact hq.not_dvd_one ((Nat.dvd_add_right hd).mp h1)

/-- **`p = q₀`** (Lemma 4′ + Lemma 9). -/
theorem padicNorm_Delta_self {q₀ : ℕ} [hq0 : Fact q₀.Prime] (hq2 : q₀ ≠ 2) (h k : ℕ) :
    padicNorm q₀ ((Delta q₀ h).coeff k) ≤ (q₀ : ℚ) ^ (2 * h * lev h q₀) * ((q₀ : ℚ)⁻¹) ^ aQ h := by
  have hq : 2 ≤ q₀ := hq0.out.two_le
  have hcl := padicNorm_Delta_clear (p := q₀) (by positivity) hq h k (aQ h) (lemma9_DeltaF hq2 h k)
    (fun m hm => qdeg_clearE_DeltaF h k m hm)
  rwa [padicNorm_qsq_unit hq (not_dvd_qsq_self hq0.out), one_pow, one_mul,
    padicNorm.padicNorm_p_of_prime] at hcl

/-- **Odd `p ∣ q₀² − 1`** (Lemma 9 after clearing `E`). -/
theorem padicNorm_Delta_sq {p q₀ : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 2 ≤ q₀) (h k : ℕ) :
    padicNorm p ((Delta q₀ h).coeff k) ≤
      (p : ℚ) ^ (2 * h * lev h p) * (p : ℚ) ^ (padicValNat p (q₀ ^ 2 - 1) * betaP h) := by
  have hcl := padicNorm_Delta_clear (p := p) (by positivity) hq h k 0 (lemma9_DeltaF hp2 h k)
    (fun _ _ => Nat.zero_le _)
  have hu : padicNorm p ((q₀ : ℚ) ^ 2 - 1) = ((p : ℚ) ^ padicValNat p (q₀ ^ 2 - 1))⁻¹ := by
    rw [padicNorm.eq_zpow_of_nonzero (qsq_ne_zero hq), qsq_cast hq, padicValRat.of_nat, zpow_neg,
      zpow_natCast]
  rw [hu, inv_pow, ← pow_mul, pow_zero, mul_one] at hcl
  have hpos : (0 : ℚ) < (p : ℚ) ^ (padicValNat p (q₀ ^ 2 - 1) * betaP h) := by
    have := (Fact.out : p.Prime).pos; positivity
  rw [inv_mul_le_iff₀ hpos] at hcl
  linarith [mul_comm ((p : ℚ) ^ (padicValNat p (q₀ ^ 2 - 1) * betaP h)) ((p : ℚ) ^ (2 * h * lev h p))]


/-! ### The common denominator -/

/-- A rational with `‖x‖_p ≤ 1` at every prime is an integer. -/
lemma exists_int_of_padicNorm_le (x : ℚ) (hx : ∀ p : ℕ, p.Prime → padicNorm p x ≤ 1) : ∃ z : ℤ, x = z := by
  refine ⟨x.num, ?_⟩
  by_contra hne
  have hden : x.den ≠ 1 := fun h1 => hne (Rat.coe_int_num_of_den_eq_one h1).symm
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hden
  haveI := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ x.num := fun hn => by
    have h1 : p ∣ x.num.natAbs := Int.ofNat_dvd_left.mp hn
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 x.reduced) hpd)
  have h1 : padicNorm p (x.num : ℚ) = 1 := (padicNorm.int_eq_one_iff _).mpr hnum
  have h2 : padicNorm p (x.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff _).mpr hpd
  have h3 : 0 < padicNorm p (x.den : ℚ) := lt_of_le_of_ne (padicNorm.nonneg _) (fun h0 => by
    have := padicNorm.zero_of_padicNorm_eq_zero h0.symm
    exact x.den_nz (by exact_mod_cast this))
  have := hx p hp
  rw [← Rat.num_div_den x, padicNorm.div, h1, div_le_one h3] at this
  linarith

/-- The exponent of `p` in the numerator `N` of the denominator. -/
noncomputable def eN (q₀ h p : ℕ) : ℕ :=
  if p = 2 then betaP h + h * (Nat.log 2 h + 6)
  else if p = q₀ then 2 * h * lev h p
  else if p ∣ q₀ ^ 2 - 1 then 2 * h * lev h p + padicValNat p (q₀ ^ 2 - 1) * betaP h
  else eGen h p

/-- The primes that may occur. -/
def SP (q₀ h : ℕ) : Finset ℕ := (range (2 * h + q₀ ^ 2 + 1)).filter Nat.Prime

noncomputable def Nden (q₀ h : ℕ) : ℕ := ∏ p ∈ SP q₀ h, p ^ eN q₀ h p

/-- **The denominator** `N / q₀^{aQ h}`. -/
noncomputable def denQ (q₀ h : ℕ) : ℚ := (Nden q₀ h : ℚ) / (q₀ : ℚ) ^ aQ h

lemma eN_eq_zero {q₀ h p : ℕ} (hq : 2 ≤ q₀) (hp : p.Prime) (hS : p ∉ SP q₀ h) : eN q₀ h p = 0 := by
  have hbig : 2 * h + q₀ ^ 2 + 1 ≤ p := by
    by_contra hc; exact hS (mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩)
  have hq2 : 4 ≤ q₀ ^ 2 := by nlinarith
  have hqq : q₀ < q₀ ^ 2 := by nlinarith
  unfold eN
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (fun hd => by
    have := Nat.le_of_dvd (by omega) hd; omega)]
  unfold eGen
  rw [ite_eq_left ⟨by nlinarith, by omega⟩]
  exact classBd_eq_zero (by omega)

lemma padicNorm_prime_nat {p p' : ℕ} [Fact p.Prime] (hp' : p'.Prime) :
    padicNorm p (p' : ℚ) = if p' = p then (p : ℚ)⁻¹ else 1 := by
  split_ifs with he
  · subst he; exact padicNorm.padicNorm_p_of_prime
  · rw [padicNorm.nat_eq_one_iff]
    intro hd
    exact he ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp').mp hd).symm

lemma padicNorm_Nden {q₀ h p : ℕ} [Fact p.Prime] (hq : 2 ≤ q₀) :
    padicNorm p (Nden q₀ h : ℚ) = ((p : ℚ)⁻¹) ^ eN q₀ h p := by
  unfold Nden
  rw [Nat.cast_prod, padicNorm_prod']
  rw [prod_congr rfl (fun p' hp' => by
    rw [Nat.cast_pow, padicNorm_pow (ℓ := p), padicNorm_prime_nat (mem_filter.mp hp').2])]
  rw [prod_congr rfl (fun p' _ => (show (if p' = p then (p : ℚ)⁻¹ else 1) ^ eN q₀ h p' =
      if p' = p then ((p : ℚ)⁻¹) ^ eN q₀ h p else 1 by split_ifs with he <;> simp [he]))]
  rw [prod_ite_eq']
  split_ifs with hS
  · rfl
  · rw [eN_eq_zero hq (Fact.out) hS, pow_zero]

lemma odd_q₀ {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) : padicNorm 2 (q₀ : ℚ) = 1 := by
  rw [padicNorm.nat_eq_one_iff]; rcases hq with rfl | rfl <;> decide

/-- **The per-prime bound**, uniformly. -/
theorem padicNorm_Delta_eN {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) (p : ℕ) [hp : Fact p.Prime] (h k : ℕ) :
    padicNorm p ((Delta q₀ h).coeff k) ≤ (p : ℚ) ^ eN q₀ h p * padicNorm p ((q₀ : ℚ) ^ aQ h) := by
  have hq2 : 2 ≤ q₀ := by rcases hq with rfl | rfl <;> norm_num
  haveI hq0 : Fact q₀.Prime := ⟨by rcases hq with rfl | rfl <;> norm_num⟩
  have hqn2 : q₀ ≠ 2 := by omega
  have hunit : p ≠ q₀ → padicNorm p ((q₀ : ℚ) ^ aQ h) = 1 := fun hne => by
    rw [padicNorm_pow (ℓ := p), padicNorm_prime_nat hq0.out, ite_eq_right (Ne.symm hne), one_pow]
  unfold eN
  split_ifs with h2 hpq hd
  · subst h2
    rw [hunit (by omega), mul_one]
    exact twoAdic_Delta hq h k
  · subst hpq
    rw [padicNorm_pow (ℓ := p), padicNorm.padicNorm_p_of_prime]
    exact padicNorm_Delta_self hqn2 h k
  · rw [hunit hpq, mul_one, pow_add]
    exact padicNorm_Delta_sq h2 hq2 h k
  · rw [hunit hpq, mul_one]
    exact padicNorm_Delta_gen h2 hq2 hd h k

lemma denQ_pos {q₀ : ℕ} (hq : 2 ≤ q₀) (h : ℕ) : 0 < denQ q₀ h := by
  unfold denQ Nden
  have : 0 < ∏ p ∈ SP q₀ h, p ^ eN q₀ h p :=
    prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.pos _)
  have hq0 : (0 : ℚ) < q₀ := by exact_mod_cast (by omega : 0 < q₀)
  positivity

/-- **Integrality.** `denQ q₀ h · Δ_h ∈ ℤ[X]`. -/
theorem denQ_int {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) (h k : ℕ) :
    ∃ z : ℤ, denQ q₀ h * (Delta q₀ h).coeff k = z := by
  have hq2 : 2 ≤ q₀ := by rcases hq with rfl | rfl <;> norm_num
  refine exists_int_of_padicNorm_le _ (fun p hp => ?_)
  have := Fact.mk hp
  have hQ : ((q₀ : ℚ) ^ aQ h) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q₀ ≠ 0))
  have hn : 0 < padicNorm p ((q₀ : ℚ) ^ aQ h) := lt_of_le_of_ne (padicNorm.nonneg _)
    (fun h0 => hQ (padicNorm.zero_of_padicNorm_eq_zero h0.symm))
  have hc := padicNorm_Delta_eN hq p h k
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  unfold denQ
  rw [padicNorm.mul, padicNorm.div, padicNorm_Nden hq2]
  calc ((p : ℚ)⁻¹) ^ eN q₀ h p / padicNorm p ((q₀ : ℚ) ^ aQ h) * padicNorm p ((Delta q₀ h).coeff k)
      ≤ ((p : ℚ)⁻¹) ^ eN q₀ h p / padicNorm p ((q₀ : ℚ) ^ aQ h) *
          ((p : ℚ) ^ eN q₀ h p * padicNorm p ((q₀ : ℚ) ^ aQ h)) :=
        mul_le_mul_of_nonneg_left hc (div_nonneg (by positivity) hn.le)
    _ = 1 := by
        rw [inv_pow]
        field_simp

end Chi2Irr
