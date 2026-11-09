/-
# Theorem Q: the arithmetic bound for general `q ≥ 3` (`pilot_q/RESULT.md` §1, §4)

Generalises `Arith/Special.lean` + `Arith/Assembly.lean` (there `q₀ ∈ {3, 5}`, `q₀` prime) to every `q ≥ 3`.
Per prime, for a coefficient `c` of `Δ_h = Delta q h`:
* `p = 2`: `‖c‖₂ ≤ 2^{n₂(h)}`, the hypothesis (`n₂(h)` may be negative);
* odd `p ∣ q(q² − 1)`: `‖c‖_p ≤ p^{2h·lev + v_p(q²−1)·βp(h)} · ‖q‖_p^{aQ h}` (Lemma 9 after clearing `E`, and
  Lemma 4′(ii): every monomial of the cleared coefficient has `q`-degree `≥ aQ h`, so the gain `‖q‖_p^{aQ h}` is
  available at every odd `p ∣ q`, with multiplicity `v_p(q)`; for `p ∣ q² − 1` it is `1`);
* other odd `p`: `‖c‖_p ≤ p^{eGen h p}` (Theorem A; `padicNorm_Delta_gen`).
`denq q n₂ h = 2^{n₂ h} · N / oddPart(q)^{aQ h}`, `N = ∏_{odd p ≤ 2h + q²} p^{eNq}`. Size: the generic exponents give the
prime sums `F1`, `F2` (`133/60`); the finitely many special odd primes give `O(h log h)` from `2h·lev` (they are added on
top of `eGen`, which only over-counts), `βp · log oddPart(q² − 1) ≤ ¼ log oddPart(q² − 1) · h² + O(h)` and
`−aQ · log oddPart(q) ≤ −⅓ log oddPart(q) · h² + O(h)`.
-/
import Chi2Irrational.Q.Defs
import Chi2Irrational.Arith.Assembly

namespace Chi2Irr
namespace Q

open Finset Filter

/-! ### The odd part -/

lemma oddPart_mul (n : ℕ) : oddPart n * 2 ^ padicValNat 2 n = n :=
  Nat.div_mul_cancel pow_padicValNat_dvd

lemma oddPart_pos {n : ℕ} (hn : n ≠ 0) : 0 < oddPart n := by
  rcases Nat.eq_zero_or_pos (oddPart n) with h0 | h0
  · have := oddPart_mul n; rw [h0, zero_mul] at this; omega
  · exact h0

lemma not_two_dvd_oddPart {n : ℕ} (hn : n ≠ 0) : ¬ 2 ∣ oddPart n := by
  have := Nat.not_dvd_ordCompl Nat.prime_two hn
  rwa [Nat.factorization_def n Nat.prime_two] at this

lemma padicNorm_oddPart {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) :
    padicNorm p (oddPart n : ℚ) = padicNorm p (n : ℚ) := by
  conv_rhs => rw [← oddPart_mul n]
  rw [Nat.cast_mul, padicNorm.mul, Nat.cast_pow, padicNorm_pow (ℓ := p), padicNorm_prime_nat Nat.prime_two,
    ite_eq_right (Ne.symm hp2), one_pow, mul_one]

/-- The prime powers `p^{v_p(n)}`, `p ∈ T`, of distinct primes divide `n` jointly. -/
lemma prod_pow_padicValNat_dvd (n : ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∏ p ∈ T, p ^ padicValNat p n ∣ n := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha]
    have hpa := hT a (mem_insert_self a T)
    have ih' := ih (fun p hp => hT p (mem_insert_of_mem hp))
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ pow_padicValNat_dvd ih'
    refine Nat.Coprime.prod_right (fun p hp => ?_)
    have hpp := hT p (mem_insert_of_mem hp)
    have hne : a ≠ p := fun e => ha (e ▸ hp)
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hpa hpp).mpr hne)

lemma prod_pow_padicValNat_dvd_oddPart {n : ℕ} (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) :
    ∏ p ∈ T, p ^ padicValNat p n ∣ oddPart n := by
  have h2 : (2 : ℕ) ∉ T := fun h => (hT 2 h).2 rfl
  have := prod_pow_padicValNat_dvd n (insert 2 T) (fun p hp => by
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact (hT p hp).1)
  rw [prod_insert h2] at this
  conv_rhs at this => rw [← oddPart_mul n]
  rw [mul_comm] at this
  exact Nat.dvd_of_mul_dvd_mul_right (by positivity) this

lemma sum_padicValNat_log_le {n : ℕ} (hn : n ≠ 0) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) :
    ∑ p ∈ T, (padicValNat p n : ℝ) * Real.log p ≤ Real.log (oddPart n) := by
  have hd := prod_pow_padicValNat_dvd_oddPart (n := n) T hT
  have hpos : 0 < ∏ p ∈ T, p ^ padicValNat p n := prod_pos (fun p hp => pow_pos (hT p hp).1.pos _)
  have hle := Nat.le_of_dvd (oddPart_pos hn) hd
  have e : Real.log ((∏ p ∈ T, p ^ padicValNat p n : ℕ) : ℝ) = ∑ p ∈ T, (padicValNat p n : ℝ) * Real.log p := by
    push_cast
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (hT p hp).1.ne_zero))]
    simp only [Real.log_pow]
  rw [← e]
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

/-! ### Per-prime bounds -/

/-- The exponent of an odd prime `p` in the numerator. -/
noncomputable def eNq (q h p : ℕ) : ℕ :=
  if p ∣ q ∨ p ∣ q ^ 2 - 1 then 2 * h * lev h p + padicValNat p (q ^ 2 - 1) * betaP h else eGen h p

/-- **Odd primes**, uniformly in `q ≥ 2`: Lemma 9 + Lemma 4′(ii) at the special primes, Theorem A elsewhere. -/
theorem padicNorm_Delta_odd {q p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 2 ≤ q) (h k : ℕ) :
    padicNorm p ((Delta q h).coeff k) ≤ (p : ℚ) ^ eNq q h p * padicNorm p ((oddPart q : ℚ) ^ aQ h) := by
  rw [padicNorm_pow (ℓ := p), padicNorm_oddPart hp2]
  unfold eNq
  split_ifs with hs
  · have hcl := padicNorm_Delta_clear (p := p) (by positivity) hq h k (aQ h) (lemma9_DeltaF hp2 h k)
      (fun m hm => qdeg_clearE_DeltaF h k m hm)
    have hu : padicNorm p ((q : ℚ) ^ 2 - 1) = ((p : ℚ) ^ padicValNat p (q ^ 2 - 1))⁻¹ := by
      rw [padicNorm.eq_zpow_of_nonzero (qsq_ne_zero hq), qsq_cast hq, padicValRat.of_nat, zpow_neg,
        zpow_natCast]
    rw [hu, inv_pow, ← pow_mul] at hcl
    have hpos : (0 : ℚ) < (p : ℚ) ^ (padicValNat p (q ^ 2 - 1) * betaP h) := by
      have := (Fact.out : p.Prime).pos; positivity
    rw [inv_mul_le_iff₀ hpos] at hcl
    rw [pow_add]
    calc padicNorm p ((Delta q h).coeff k)
        ≤ (p : ℚ) ^ (padicValNat p (q ^ 2 - 1) * betaP h) *
            ((p : ℚ) ^ (2 * h * lev h p) * padicNorm p (q : ℚ) ^ aQ h) := hcl
      _ = _ := by ring
  · push Not at hs
    have hu : padicNorm p (q : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr hs.1
    rw [hu, one_pow, mul_one]
    exact padicNorm_Delta_gen hp2 hq hs.2 h k

/-! ### The common denominator -/

/-- The odd primes that may occur. -/
def SPq (q h : ℕ) : Finset ℕ := (range (2 * h + q ^ 2 + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- The odd numerator. -/
noncomputable def Nq (q h : ℕ) : ℕ := ∏ p ∈ SPq q h, p ^ eNq q h p

/-- **The denominator** `2^{n₂ h} · N / oddPart(q)^{aQ h}`. -/
noncomputable def denq (q : ℕ) (n2 : ℕ → ℤ) (h : ℕ) : ℚ :=
  (2 : ℚ) ^ n2 h * (Nq q h : ℚ) / (oddPart q : ℚ) ^ aQ h

lemma eNq_eq_zero {q h p : ℕ} (hq : 2 ≤ q) (hbig : 2 * h + q ^ 2 + 1 ≤ p) : eNq q h p = 0 := by
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hqq : q < q ^ 2 := by nlinarith
  unfold eNq
  rw [ite_eq_right]
  · unfold eGen
    rw [ite_eq_left ⟨by nlinarith, by omega⟩]
    exact classBd_eq_zero (by omega)
  · rintro (hd | hd)
    · have := Nat.le_of_dvd (by omega) hd; omega
    · have := Nat.le_of_dvd (by omega) hd; omega

lemma padicNorm_Nq {q h p : ℕ} [Fact p.Prime] (hq : 2 ≤ q) :
    padicNorm p (Nq q h : ℚ) = if p = 2 then 1 else ((p : ℚ)⁻¹) ^ eNq q h p := by
  unfold Nq
  rw [Nat.cast_prod, padicNorm_prod']
  rw [prod_congr rfl (fun p' hp' => by
    rw [Nat.cast_pow, padicNorm_pow (ℓ := p), padicNorm_prime_nat (mem_filter.mp hp').2.1])]
  rw [prod_congr rfl (fun p' _ => (show (if p' = p then (p : ℚ)⁻¹ else 1) ^ eNq q h p' =
      if p' = p then ((p : ℚ)⁻¹) ^ eNq q h p else 1 by split_ifs with he <;> simp [he]))]
  rw [prod_ite_eq']
  split_ifs with hS h2 h2
  · exact absurd h2 (mem_filter.mp hS).2.2
  · rfl
  · rfl
  · have hbig : 2 * h + q ^ 2 + 1 ≤ p := by
      by_contra hc
      exact hS (mem_filter.mpr ⟨mem_range.mpr (by omega), Fact.out, h2⟩)
    rw [eNq_eq_zero hq hbig, pow_zero]

lemma oddPart_ne_zero {q : ℕ} (hq : 2 ≤ q) : (oddPart q : ℚ) ≠ 0 := by
  exact_mod_cast (oddPart_pos (by omega)).ne'

lemma denq_pos {q : ℕ} (hq : 2 ≤ q) (n2 : ℕ → ℤ) (h : ℕ) : 0 < denq q n2 h := by
  unfold denq Nq
  have : 0 < ∏ p ∈ SPq q h, p ^ eNq q h p := prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.1.pos _)
  have hq0 : (0 : ℚ) < oddPart q := by exact_mod_cast oddPart_pos (by omega)
  positivity

lemma padicNorm_two_zpow (n : ℤ) : padicNorm 2 ((2 : ℚ) ^ n) = (2 : ℚ) ^ (-n) := by
  have h1 : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat.self (p := 2) one_lt_two
  rw [padicNorm.eq_zpow_of_nonzero (by positivity), padicValRat.zpow, h1]
  simp

lemma padicNorm_odd_two_zpow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (n : ℤ) : padicNorm p ((2 : ℚ) ^ n) = 1 := by
  rw [padicNorm.eq_zpow_of_nonzero (by positivity), padicValRat.zpow]
  have : padicValRat p 2 = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
  rw [this]; simp

/-- **Integrality.** `denq · Δ_h ∈ ℤ[X]`. -/
theorem denq_int {q : ℕ} (hq : 2 ≤ q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (h k : ℕ) :
    ∃ z : ℤ, denq q n2 h * (Delta q h).coeff k = z := by
  refine exists_int_of_padicNorm_le _ (fun p hp => ?_)
  have := Fact.mk hp
  have hQ : ((oddPart q : ℚ) ^ aQ h) ≠ 0 := pow_ne_zero _ (oddPart_ne_zero hq)
  have hn : 0 < padicNorm p ((oddPart q : ℚ) ^ aQ h) := lt_of_le_of_ne (padicNorm.nonneg _)
    (fun h0 => hQ (padicNorm.zero_of_padicNorm_eq_zero h0.symm))
  unfold denq
  rw [padicNorm.mul, padicNorm.div, padicNorm.mul, padicNorm_Nq hq]
  by_cases h2 : p = 2
  · subst h2
    rw [ite_eq_left rfl]
    have hu : padicNorm 2 (oddPart q : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr (not_two_dvd_oddPart (by omega))
    rw [padicNorm_pow (ℓ := 2), hu, one_pow, div_one, mul_one, padicNorm_two_zpow]
    calc (2 : ℚ) ^ (-n2 h) * padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (-n2 h) * (2 : ℚ) ^ (n2 h) :=
          mul_le_mul_of_nonneg_left (hn2 h k) (by positivity)
      _ = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  · rw [ite_eq_right h2, padicNorm_odd_two_zpow h2, one_mul]
    have hc := padicNorm_Delta_odd h2 hq h k
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
    calc ((p : ℚ)⁻¹) ^ eNq q h p / padicNorm p ((oddPart q : ℚ) ^ aQ h) * padicNorm p ((Delta q h).coeff k)
        ≤ ((p : ℚ)⁻¹) ^ eNq q h p / padicNorm p ((oddPart q : ℚ) ^ aQ h) *
            ((p : ℚ) ^ eNq q h p * padicNorm p ((oddPart q : ℚ) ^ aQ h)) :=
          mul_le_mul_of_nonneg_left hc (div_nonneg (by positivity) hn.le)
      _ = 1 := by
          rw [inv_pow]
          field_simp

/-! ### The size of the denominator -/

/-- The special odd primes. -/
def TS (q h : ℕ) : Finset ℕ := (SPq q h).filter (fun p => p ∣ q ∨ p ∣ q ^ 2 - 1)

lemma TS_sub {q h : ℕ} (hq : 2 ≤ q) : TS q h ⊆ range (q ^ 2 + 1) := by
  intro p hp
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hqq : q < q ^ 2 := by nlinarith
  rw [mem_range]
  rcases (mem_filter.mp hp).2 with hd | hd
  · have := Nat.le_of_dvd (by omega) hd; omega
  · have := Nat.le_of_dvd (by omega) hd; omega

lemma eNq_log_le {q h p : ℕ} :
    (eNq q h p : ℝ) * Real.log p ≤ (eGen h p : ℝ) * Real.log p +
      (if p ∣ q ∨ p ∣ q ^ 2 - 1 then
        2 * (h : ℝ) * lev h p * Real.log p + betaP h * ((padicValNat p (q ^ 2 - 1) : ℝ) * Real.log p)
       else 0) := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  unfold eNq
  split_ifs
  · have : 0 ≤ (eGen h p : ℝ) * Real.log p := by positivity
    push_cast; nlinarith
  · simp

/-- **The size of the denominator**, for `h ≥ 13`. -/
theorem log_denq_le {q : ℕ} (hq : 2 ≤ q) (n2 : ℕ → ℤ) {h : ℕ} (hh : 13 ≤ h) :
    Real.log ((denq q n2 h : ℚ) : ℝ) ≤ (n2 h : ℝ) * Real.log 2 +
      ∑ p ∈ F1 h, 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p +
        ∑ p ∈ F2 h, (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p +
        (Real.log (oddPart (q ^ 2 - 1)) / 4 - Real.log (oddPart q) / 3) * (h : ℝ) ^ 2 +
        ((q : ℝ) ^ 2 + 1 + Real.log (oddPart (q ^ 2 - 1)) + Real.log (oddPart q)) *
          (30 * h + 6 * h * Real.log h) := by
  set H : ℝ := (h : ℝ) with hH
  have hH1 : (13 : ℝ) ≤ H := by rw [hH]; exact_mod_cast hh
  have hq1 : q ^ 2 - 1 ≠ 0 := by have : 4 ≤ q ^ 2 := by nlinarith
                                 omega
  set L1 : ℝ := Real.log (oddPart (q ^ 2 - 1)) with hL1
  set L2 : ℝ := Real.log (oddPart q) with hL2
  have hL10 : 0 ≤ L1 := Real.log_natCast_nonneg _
  have hL20 : 0 ≤ L2 := Real.log_natCast_nonneg _
  -- `log denq = n₂ log 2 + Σ eNq log p − aQ log oddPart q`
  have hNpos : 0 < Nq q h := prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.1.pos _)
  have hop : (0 : ℝ) < oddPart q := by exact_mod_cast oddPart_pos (by omega)
  have hden : ((denq q n2 h : ℚ) : ℝ) = (2 : ℝ) ^ n2 h * (Nq q h : ℝ) / (oddPart q : ℝ) ^ aQ h := by
    unfold denq; push_cast; ring
  rw [hden, Real.log_div (by positivity) (pow_ne_zero _ hop.ne'), Real.log_mul (by positivity)
    (by exact_mod_cast hNpos.ne'), Real.log_zpow, Real.log_pow]
  have hlogN : Real.log (Nq q h) = ∑ p ∈ SPq q h, (eNq q h p : ℝ) * Real.log p := by
    unfold Nq
    push_cast
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (mem_filter.mp hp).2.1.ne_zero))]
    simp only [Real.log_pow]
  rw [hlogN, ← hL2]
  have hs : ∀ p ∈ SPq q h, p.Prime ∧ p ≠ 2 := fun p hp => (mem_filter.mp hp).2
  -- split off the special primes
  have hsplit : ∑ p ∈ SPq q h, (eNq q h p : ℝ) * Real.log p ≤
      ∑ p ∈ SPq q h, (eGen h p : ℝ) * Real.log p +
        (∑ p ∈ TS q h, 2 * H * lev h p * Real.log p +
          betaP h * ∑ p ∈ TS q h, (padicValNat p (q ^ 2 - 1) : ℝ) * Real.log p) := by
    refine (sum_le_sum (fun p hp => eNq_log_le (q := q) (h := h) (p := p))).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, mul_sum, ← sum_add_distrib]
    rfl
  have hgen := sum_eGen_le hh (SPq q h) hs
  -- the special primes: `2h·lev` terms
  have hlev : ∑ p ∈ TS q h, 2 * H * lev h p * Real.log p ≤ ((q : ℝ) ^ 2 + 1) * (2 * H * (1 + Real.log H)) := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hb : ∀ p ∈ TS q h, 2 * H * lev h p * Real.log p ≤ 2 * H * (1 + Real.log H) := fun p hp => by
      have hpp := (hs p (mem_filter.mp hp).1).1
      have := lev_mul_log_le hpp (by omega : 1 ≤ h)
      rw [Real.log_mul (by norm_num) (by rw [hH] at hH1; positivity)] at this
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [← hH] at this; linarith) (by positivity)
    have hc : ((TS q h).card : ℝ) ≤ (q : ℝ) ^ 2 + 1 := by
      have := card_le_card (TS_sub (h := h) hq)
      rw [card_range] at this
      exact_mod_cast this
    have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    calc ∑ p ∈ TS q h, 2 * H * lev h p * Real.log p ≤ ∑ p ∈ TS q h, 2 * H * (1 + Real.log H) := sum_le_sum hb
      _ = ((TS q h).card : ℝ) * (2 * H * (1 + Real.log H)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  -- the special primes: `v_p(q² − 1)·βp` terms
  have hv := sum_padicValNat_log_le hq1 (TS q h) (fun p hp => hs p (mem_filter.mp hp).1)
  rw [← hL1] at hv
  have hβ : 4 * (betaP h : ℝ) ≤ H ^ 2 + 2 * H := by
    have := betaP_le h; rw [hH]; exact_mod_cast this
  have hβL : (betaP h : ℝ) * ∑ p ∈ TS q h, (padicValNat p (q ^ 2 - 1) : ℝ) * Real.log p ≤
      (H ^ 2 + 2 * H) / 4 * L1 :=
    (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hL10)
  -- `aQ`
  have haQ := aQ_ge (h := h) (by omega)
  rw [← hH] at haQ
  have haQl : ((H ^ 2 - 7 * H - 2) / 3) * L2 ≤ (aQ h : ℝ) * L2 := mul_le_mul_of_nonneg_right haQ hL20
  -- remainder
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

/-- **The arithmetic bound for general `q`** (the exact statement of `arith_q`, `Q/Interface.lean`). -/
theorem arith_q_proof (q : ℕ) (hq : 3 ≤ q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (c2 : ℝ)
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2) :
    ∃ den : ℕ → ℚ, (∀ h, 0 < den h) ∧ (∀ h k, ∃ z : ℤ, den h * (Delta q h).coeff k = z) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (alphaCore q + c2 + ε) * (h : ℝ) ^ 2 := by
  have hq2 : 2 ≤ q := by omega
  refine ⟨denq q n2, denq_pos hq2 n2, denq_int hq2 n2 hn2, fun ε hε => ?_⟩
  set C : ℝ := (q : ℝ) ^ 2 + 1 + Real.log (oddPart (q ^ 2 - 1)) + Real.log (oddPart q) with hC
  have hC0 : 0 < C := by
    have := Real.log_natCast_nonneg (oddPart (q ^ 2 - 1))
    have := Real.log_natCast_nonneg (oddPart q)
    positivity
  filter_upwards [hc2 (ε / 4) (by positivity), eventually_primeSum_lev_le (ε / 4) (by positivity),
    eventually_primeSum_phi1_le (ε / 4) (by positivity), eventually_rem_le (ε / 4 / C) (by positivity),
    eventually_ge_atTop 13] with h h0 h1 h2 h3 h4
  have := log_denq_le hq2 n2 h4
  unfold F1 F2 at this
  rw [← hC] at this
  have h3' : C * (30 * (h : ℝ) + 6 * (h : ℝ) * Real.log h) ≤ ε / 4 * (h : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 hC0.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hC0.ne'] at this
  unfold alphaCore
  nlinarith

end Q
end Chi2Irr
