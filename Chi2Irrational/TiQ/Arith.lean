/-
# Theorem T: the arithmetic bound for `Δ^Ti_h` (`pilot_ti2q/RESULT.md` §2)

Copy of `Q/Arith.lean` (Theorem Q) with `q² + 1` in place of `q² − 1` and `DeltaT` in place of `Delta`. The per-prime
bounds come from the symbolic χ₂ determinant through the coefficient twist of `TiQ/Free.lean` (RESULT §2, referee fix F2:
every coefficient of the Ti determinant is `±` a coefficient of the χ₂ one):
* `p = 2`: the hypothesis `‖c‖₂ ≤ 2^{n₂(h)}`;
* odd `p ∣ q(q² + 1)`: `‖c‖_p ≤ p^{2h·lev + v_p(q²+1)·βp(h)} · ‖q‖_p^{aQ h}` (Lemma 9 after clearing `(q² + 1)^β`, Lemma 5,
  and Lemma 4′(ii) through `padicNorm_DeltaT_clear`);
* other odd `p`: `‖c‖_p ≤ p^{eGen h p}` (Theorem A; `padicNorm_DeltaT_gen`).
Size: as in `Q/Arith.lean`; the special primes now divide `q(q² + 1)`, so there are at most `q² + 2` of them.
-/
import Chi2Irrational.TiQ.Defs
import Chi2Irrational.TiQ.Free
import Chi2Irrational.Q.Arith

namespace Chi2Irr
namespace TiQ

open Finset Filter

/-! ### Per-prime bounds -/

lemma qsqT_cast (q : ℕ) : (q : ℚ) ^ 2 + 1 = ((q ^ 2 + 1 : ℕ) : ℚ) := by push_cast; ring

lemma padicNorm_qsqT_unit {p q : ℕ} [Fact p.Prime] (hp : ¬ p ∣ q ^ 2 + 1) : padicNorm p ((q : ℚ) ^ 2 + 1) = 1 := by
  rw [qsqT_cast, padicNorm.nat_eq_one_iff]; exact hp

/-- **Generic odd primes** (Theorem A, transferred). -/
theorem padicNorm_DeltaT_gen {p q₀ : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 2 ≤ q₀) (hpq : ¬ p ∣ q₀ ^ 2 + 1)
    (h k : ℕ) : padicNorm p ((DeltaT q₀ h).coeff k) ≤ (p : ℚ) ^ eGen h p := by
  rw [coeff_DeltaT_eq hq]
  refine GLe_ev (GLe_twF (GLeX_eGen hp2 h k) k) (by positivity) _ ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simpa using padicNorm_nat_le_one p q₀
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [padicNorm.div, padicNorm_qsqT_unit hpq, padicNorm.one, div_one]

/-- The exponent of an odd prime `p` in the numerator. -/
noncomputable def eNqT (q h p : ℕ) : ℕ :=
  if p ∣ q ∨ p ∣ q ^ 2 + 1 then 2 * h * lev h p + padicValNat p (q ^ 2 + 1) * betaP h else eGen h p

/-- **Odd primes**, uniformly in `q ≥ 2`: Lemma 9 + Lemma 5 + Lemma 4′(ii) at the special primes, Theorem A elsewhere. -/
theorem padicNorm_DeltaT_odd {q p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 2 ≤ q) (h k : ℕ) :
    padicNorm p ((DeltaT q h).coeff k) ≤ (p : ℚ) ^ eNqT q h p * padicNorm p ((Q.oddPart q : ℚ) ^ aQ h) := by
  rw [padicNorm_pow (ℓ := p), Q.padicNorm_oddPart hp2]
  unfold eNqT
  split_ifs with hs
  · have hcl := padicNorm_DeltaT_clear (p := p) (by positivity) hq h k (aQ h) (lemma9_DeltaF hp2 h k)
      (fun m hm => qdeg_clearE_DeltaF h k m hm)
    have hu : padicNorm p ((q : ℚ) ^ 2 + 1) = ((p : ℚ) ^ padicValNat p (q ^ 2 + 1))⁻¹ := by
      rw [padicNorm.eq_zpow_of_nonzero (qsq_add_one_pos q).ne', qsqT_cast, padicValRat.of_nat, zpow_neg,
        zpow_natCast]
    rw [hu, inv_pow, ← pow_mul] at hcl
    have hpos : (0 : ℚ) < (p : ℚ) ^ (padicValNat p (q ^ 2 + 1) * betaP h) := by
      have := (Fact.out : p.Prime).pos; positivity
    rw [inv_mul_le_iff₀ hpos] at hcl
    rw [pow_add]
    calc padicNorm p ((DeltaT q h).coeff k)
        ≤ (p : ℚ) ^ (padicValNat p (q ^ 2 + 1) * betaP h) *
            ((p : ℚ) ^ (2 * h * lev h p) * padicNorm p (q : ℚ) ^ aQ h) := hcl
      _ = _ := by ring
  · push_neg at hs
    have hu : padicNorm p (q : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr hs.1
    rw [hu, one_pow, mul_one]
    exact padicNorm_DeltaT_gen hp2 hq hs.2 h k

/-! ### The common denominator -/

/-- The odd primes that may occur. -/
def SPqT (q h : ℕ) : Finset ℕ := (range (2 * h + q ^ 2 + 2)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- The odd numerator. -/
noncomputable def NqT (q h : ℕ) : ℕ := ∏ p ∈ SPqT q h, p ^ eNqT q h p

/-- **The denominator** `2^{n₂ h} · N / oddPart(q)^{aQ h}`. -/
noncomputable def denqT (q : ℕ) (n2 : ℕ → ℤ) (h : ℕ) : ℚ :=
  (2 : ℚ) ^ n2 h * (NqT q h : ℚ) / (Q.oddPart q : ℚ) ^ aQ h

lemma eNqT_eq_zero {q h p : ℕ} (hq : 2 ≤ q) (hbig : 2 * h + q ^ 2 + 2 ≤ p) : eNqT q h p = 0 := by
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hqq : q < q ^ 2 := by nlinarith
  unfold eNqT
  rw [ite_eq_right]
  · unfold eGen
    rw [ite_eq_left ⟨by nlinarith, by omega⟩]
    exact classBd_eq_zero (by omega)
  · rintro (hd | hd)
    · have := Nat.le_of_dvd (by omega) hd; omega
    · have := Nat.le_of_dvd (by omega) hd; omega

lemma padicNorm_NqTT {q h p : ℕ} [Fact p.Prime] (hq : 2 ≤ q) :
    padicNorm p (NqT q h : ℚ) = if p = 2 then 1 else ((p : ℚ)⁻¹) ^ eNqT q h p := by
  unfold NqT
  rw [Nat.cast_prod, padicNorm_prod']
  rw [prod_congr rfl (fun p' hp' => by
    rw [Nat.cast_pow, padicNorm_pow (ℓ := p), padicNorm_prime_nat (mem_filter.mp hp').2.1])]
  rw [prod_congr rfl (fun p' _ => (show (if p' = p then (p : ℚ)⁻¹ else 1) ^ eNqT q h p' =
      if p' = p then ((p : ℚ)⁻¹) ^ eNqT q h p else 1 by split_ifs with he <;> simp [he]))]
  rw [prod_ite_eq']
  split_ifs with hS h2 h2
  · exact absurd h2 (mem_filter.mp hS).2.2
  · rfl
  · rfl
  · have hbig : 2 * h + q ^ 2 + 2 ≤ p := by
      by_contra hc
      exact hS (mem_filter.mpr ⟨mem_range.mpr (by omega), Fact.out, h2⟩)
    rw [eNqT_eq_zero hq hbig, pow_zero]

lemma Q.oddPart_ne_zero {q : ℕ} (hq : 2 ≤ q) : (Q.oddPart q : ℚ) ≠ 0 := by
  exact_mod_cast (Q.oddPart_pos (by omega)).ne'

lemma denqT_pos {q : ℕ} (hq : 2 ≤ q) (n2 : ℕ → ℤ) (h : ℕ) : 0 < denqT q n2 h := by
  unfold denqT NqT
  have : 0 < ∏ p ∈ SPqT q h, p ^ eNqT q h p := prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.1.pos _)
  have hq0 : (0 : ℚ) < Q.oddPart q := by exact_mod_cast Q.oddPart_pos (by omega)
  positivity

lemma Q.padicNorm_two_zpow (n : ℤ) : padicNorm 2 ((2 : ℚ) ^ n) = (2 : ℚ) ^ (-n) := by
  have h1 : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat.self (p := 2) one_lt_two
  rw [padicNorm.eq_zpow_of_nonzero (by positivity), padicValRat.zpow, h1]
  simp

lemma Q.padicNorm_odd_two_zpow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (n : ℤ) : padicNorm p ((2 : ℚ) ^ n) = 1 := by
  rw [padicNorm.eq_zpow_of_nonzero (by positivity), padicValRat.zpow]
  have : padicValRat p 2 = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
  rw [this]; simp

/-- **Integrality.** `denqT · Δ_h ∈ ℤ[X]`. -/
theorem denqT_int {q : ℕ} (hq : 2 ≤ q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (h k : ℕ) :
    ∃ z : ℤ, denqT q n2 h * (DeltaT q h).coeff k = z := by
  refine exists_int_of_padicNorm_le _ (fun p hp => ?_)
  have := Fact.mk hp
  have hQ : ((Q.oddPart q : ℚ) ^ aQ h) ≠ 0 := pow_ne_zero _ (Q.oddPart_ne_zero hq)
  have hn : 0 < padicNorm p ((Q.oddPart q : ℚ) ^ aQ h) := lt_of_le_of_ne (padicNorm.nonneg _)
    (fun h0 => hQ (padicNorm.zero_of_padicNorm_eq_zero h0.symm))
  unfold denqT
  rw [padicNorm.mul, padicNorm.div, padicNorm.mul, padicNorm_NqTT hq]
  by_cases h2 : p = 2
  · subst h2
    rw [ite_eq_left rfl]
    have hu : padicNorm 2 (Q.oddPart q : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr (Q.not_two_dvd_oddPart (by omega))
    rw [padicNorm_pow (ℓ := 2), hu, one_pow, div_one, mul_one, Q.padicNorm_two_zpow]
    calc (2 : ℚ) ^ (-n2 h) * padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (-n2 h) * (2 : ℚ) ^ (n2 h) :=
          mul_le_mul_of_nonneg_left (hn2 h k) (by positivity)
      _ = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  · rw [ite_eq_right h2, Q.padicNorm_odd_two_zpow h2, one_mul]
    have hc := padicNorm_DeltaT_odd h2 hq h k
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
    calc ((p : ℚ)⁻¹) ^ eNqT q h p / padicNorm p ((Q.oddPart q : ℚ) ^ aQ h) * padicNorm p ((DeltaT q h).coeff k)
        ≤ ((p : ℚ)⁻¹) ^ eNqT q h p / padicNorm p ((Q.oddPart q : ℚ) ^ aQ h) *
            ((p : ℚ) ^ eNqT q h p * padicNorm p ((Q.oddPart q : ℚ) ^ aQ h)) :=
          mul_le_mul_of_nonneg_left hc (div_nonneg (by positivity) hn.le)
      _ = 1 := by
          rw [inv_pow]
          field_simp

/-! ### The size of the denominator -/

/-- The special odd primes. -/
def TST (q h : ℕ) : Finset ℕ := (SPqT q h).filter (fun p => p ∣ q ∨ p ∣ q ^ 2 + 1)

lemma TST_sub {q h : ℕ} (hq : 2 ≤ q) : TST q h ⊆ range (q ^ 2 + 2) := by
  intro p hp
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hqq : q < q ^ 2 := by nlinarith
  rw [mem_range]
  rcases (mem_filter.mp hp).2 with hd | hd
  · have := Nat.le_of_dvd (by omega) hd; omega
  · have := Nat.le_of_dvd (by omega) hd; omega

lemma eNqT_log_le {q h p : ℕ} :
    (eNqT q h p : ℝ) * Real.log p ≤ (eGen h p : ℝ) * Real.log p +
      (if p ∣ q ∨ p ∣ q ^ 2 + 1 then
        2 * (h : ℝ) * lev h p * Real.log p + betaP h * ((padicValNat p (q ^ 2 + 1) : ℝ) * Real.log p)
       else 0) := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  unfold eNqT
  split_ifs
  · have : 0 ≤ (eGen h p : ℝ) * Real.log p := by positivity
    push_cast; nlinarith
  · simp

/-- **The size of the denominator**, for `h ≥ 13`. -/
theorem log_denqT_le {q : ℕ} (hq : 2 ≤ q) (n2 : ℕ → ℤ) {h : ℕ} (hh : 13 ≤ h) :
    Real.log ((denqT q n2 h : ℚ) : ℝ) ≤ (n2 h : ℝ) * Real.log 2 +
      ∑ p ∈ F1 h, 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p +
        ∑ p ∈ F2 h, (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p +
        (Real.log (Q.oddPart (q ^ 2 + 1)) / 4 - Real.log (Q.oddPart q) / 3) * (h : ℝ) ^ 2 +
        ((q : ℝ) ^ 2 + 2 + Real.log (Q.oddPart (q ^ 2 + 1)) + Real.log (Q.oddPart q)) *
          (30 * h + 6 * h * Real.log h) := by
  set H : ℝ := (h : ℝ) with hH
  have hH1 : (13 : ℝ) ≤ H := by rw [hH]; exact_mod_cast hh
  have hq1 : q ^ 2 + 1 ≠ 0 := by have : 4 ≤ q ^ 2 := by nlinarith
                                 omega
  set L1 : ℝ := Real.log (Q.oddPart (q ^ 2 + 1)) with hL1
  set L2 : ℝ := Real.log (Q.oddPart q) with hL2
  have hL10 : 0 ≤ L1 := Real.log_natCast_nonneg _
  have hL20 : 0 ≤ L2 := Real.log_natCast_nonneg _
  -- `log denqT = n₂ log 2 + Σ eNqT log p − aQ log Q.oddPart q`
  have hNpos : 0 < NqT q h := prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.1.pos _)
  have hop : (0 : ℝ) < Q.oddPart q := by exact_mod_cast Q.oddPart_pos (by omega)
  have hden : ((denqT q n2 h : ℚ) : ℝ) = (2 : ℝ) ^ n2 h * (NqT q h : ℝ) / (Q.oddPart q : ℝ) ^ aQ h := by
    unfold denqT; push_cast; ring
  rw [hden, Real.log_div (by positivity) (pow_ne_zero _ hop.ne'), Real.log_mul (by positivity)
    (by exact_mod_cast hNpos.ne'), Real.log_zpow, Real.log_pow]
  have hlogN : Real.log (NqT q h) = ∑ p ∈ SPqT q h, (eNqT q h p : ℝ) * Real.log p := by
    unfold NqT
    push_cast
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (mem_filter.mp hp).2.1.ne_zero))]
    simp only [Real.log_pow]
  rw [hlogN, ← hL2]
  have hs : ∀ p ∈ SPqT q h, p.Prime ∧ p ≠ 2 := fun p hp => (mem_filter.mp hp).2
  -- split off the special primes
  have hsplit : ∑ p ∈ SPqT q h, (eNqT q h p : ℝ) * Real.log p ≤
      ∑ p ∈ SPqT q h, (eGen h p : ℝ) * Real.log p +
        (∑ p ∈ TST q h, 2 * H * lev h p * Real.log p +
          betaP h * ∑ p ∈ TST q h, (padicValNat p (q ^ 2 + 1) : ℝ) * Real.log p) := by
    refine (sum_le_sum (fun p hp => eNqT_log_le (q := q) (h := h) (p := p))).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, mul_sum, ← sum_add_distrib]
    rfl
  have hgen := sum_eGen_le hh (SPqT q h) hs
  -- the special primes: `2h·lev` terms
  have hlev : ∑ p ∈ TST q h, 2 * H * lev h p * Real.log p ≤ ((q : ℝ) ^ 2 + 2) * (2 * H * (1 + Real.log H)) := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hb : ∀ p ∈ TST q h, 2 * H * lev h p * Real.log p ≤ 2 * H * (1 + Real.log H) := fun p hp => by
      have hpp := (hs p (mem_filter.mp hp).1).1
      have := lev_mul_log_le hpp (by omega : 1 ≤ h)
      rw [Real.log_mul (by norm_num) (by rw [hH] at hH1; positivity)] at this
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [← hH] at this; linarith) (by positivity)
    have hc : ((TST q h).card : ℝ) ≤ (q : ℝ) ^ 2 + 2 := by
      have := card_le_card (TST_sub (h := h) hq)
      rw [card_range] at this
      exact_mod_cast this
    have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    calc ∑ p ∈ TST q h, 2 * H * lev h p * Real.log p ≤ ∑ p ∈ TST q h, 2 * H * (1 + Real.log H) := sum_le_sum hb
      _ = ((TST q h).card : ℝ) * (2 * H * (1 + Real.log H)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  -- the special primes: `v_p(q² − 1)·βp` terms
  have hv := Q.sum_padicValNat_log_le hq1 (TST q h) (fun p hp => hs p (mem_filter.mp hp).1)
  rw [← hL1] at hv
  have hβ : 4 * (betaP h : ℝ) ≤ H ^ 2 + 2 * H := by
    have := betaP_le h; rw [hH]; exact_mod_cast this
  have hβL : (betaP h : ℝ) * ∑ p ∈ TST q h, (padicValNat p (q ^ 2 + 1) : ℝ) * Real.log p ≤
      (H ^ 2 + 2 * H) / 4 * L1 :=
    (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hL10)
  -- `aQ`
  have haQ := aQ_ge (h := h) (by omega)
  rw [← hH] at haQ
  have haQl : ((H ^ 2 - 7 * H - 2) / 3) * L2 ≤ (aQ h : ℝ) * L2 := mul_le_mul_of_nonneg_right haQ hL20
  -- remainder
  have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ 2 + 2 := by positivity
  have hrem : ((q : ℝ) ^ 2 + 2) * (2 * H * (1 + Real.log H)) + 2 * H / 4 * L1 + (7 * H + 2) / 3 * L2 ≤
      ((q : ℝ) ^ 2 + 2 + L1 + L2) * (30 * H + 6 * H * Real.log H) := by
    have e1 : ((q : ℝ) ^ 2 + 2) * (2 * H * (1 + Real.log H)) ≤ ((q : ℝ) ^ 2 + 2) * (30 * H + 6 * H * Real.log H) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hq0
    have e2 : 2 * H / 4 * L1 ≤ L1 * (30 * H + 6 * H * Real.log H) := by
      have : 0 ≤ 6 * H * Real.log H := by positivity
      nlinarith
    have e3 : (7 * H + 2) / 3 * L2 ≤ L2 * (30 * H + 6 * H * Real.log H) := by
      have : 0 ≤ 6 * H * Real.log H := by positivity
      nlinarith
    nlinarith
  nlinarith

/-- **The arithmetic bound for Ti** (the exact statement of `arith_t`, `TiQ/Interface.lean`). -/
theorem arith_t_proof (q : ℕ) (hq : 3 ≤ q) (n2 : ℕ → ℤ)
    (hn2 : ∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) (c2 : ℝ)
    (hc2 : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2 + ε) * (h : ℝ) ^ 2) :
    ∃ den : ℕ → ℚ, (∀ h, 0 < den h) ∧ (∀ h k, ∃ z : ℤ, den h * (DeltaT q h).coeff k = z) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log (den h) ≤ (alphaCoreT q + c2 + ε) * (h : ℝ) ^ 2 := by
  have hq2 : 2 ≤ q := by omega
  refine ⟨denqT q n2, denqT_pos hq2 n2, denqT_int hq2 n2 hn2, fun ε hε => ?_⟩
  set C : ℝ := (q : ℝ) ^ 2 + 2 + Real.log (Q.oddPart (q ^ 2 + 1)) + Real.log (Q.oddPart q) with hC
  have hC0 : 0 < C := by
    have := Real.log_natCast_nonneg (Q.oddPart (q ^ 2 + 1))
    have := Real.log_natCast_nonneg (Q.oddPart q)
    positivity
  filter_upwards [hc2 (ε / 4) (by positivity), eventually_primeSum_lev_le (ε / 4) (by positivity),
    eventually_primeSum_phi1_le (ε / 4) (by positivity), eventually_rem_le (ε / 4 / C) (by positivity),
    eventually_ge_atTop 13] with h h0 h1 h2 h3 h4
  have := log_denqT_le hq2 n2 h4
  unfold F1 F2 at this
  rw [← hC] at this
  have h3' : C * (30 * (h : ℝ) + 6 * (h : ℝ) * Real.log h) ≤ ε / 4 * (h : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 hC0.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hC0.ne'] at this
  unfold alphaCoreT
  nlinarith

end TiQ
end Chi2Irr
