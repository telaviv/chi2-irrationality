/-
# Assembly: the size of the denominator, the margins, and the main theorems

* `log_denQ_le`: for `h ≥ 13`,
  `log denQ ≤ Σ_{5p<2h} 2h·lev·log p + Σ_{2h≤5p, p<2h} h φ₁(p/h) log p + (α − 133/60) h² + 30h + 6h log h`,
  with `α = alphaQ q₀ = 133/60 + ¼ log 2 [+ ¼ log 3 if q₀ = 5] − ⅓ log q₀`.
* `arith_denQ`: with the PNT prime sums (`eventually_primeSum_lev_le`, `eventually_primeSum_phi1_le`),
  `log denQ ≤ (α + ε) h²` eventually.
* `margin_three`, `margin_five`: `α + β < 0` with `β = −2.078` (`q = 3`), `−2.385` (`q = 5`) from Theorem B.
* **`chi2_one_third_irrational`, `chi2_one_fifth_irrational`.**
-/
import Chi2Irrational.Arith.Special
import Chi2Irrational.Arith.PrimeSums
import Chi2Irrational.MainCond
import Chi2Irrational.Statement
import Chi2Irrational.Cert.Q3
import Chi2Irrational.Cert.Q5
import Chi2Irrational.NonVan.NonVanQ

namespace Chi2Irr

open Finset Filter

/-- The arithmetic constant. -/
noncomputable def alphaQ (q₀ : ℕ) : ℝ :=
  133 / 60 + Real.log 2 / 4 + (if q₀ = 5 then Real.log 3 / 4 else 0) - Real.log q₀ / 3

/-- Small primes (`5p < 2h`, Lemma 9) and large primes (`2h ≤ 5p < 10h`, the class bound). -/
def F1 (h : ℕ) : Finset ℕ := (range (2 * h)).filter (fun p => p.Prime ∧ 5 * p < 2 * h)
def F2 (h : ℕ) : Finset ℕ := (range (2 * h)).filter (fun p => p.Prime ∧ 2 * h ≤ 5 * p)

lemma eGen_log_le {h p : ℕ} (hh : 13 ≤ h) (hp : p.Prime) (hp2 : p ≠ 2) :
    (eGen h p : ℝ) * Real.log p ≤
      (if p ∈ F1 h then 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p else 0) +
        (if p ∈ F2 h then (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p else 0) := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rcases lt_or_ge (5 * p) (2 * h) with h5 | h5
  · have hm1 : p ∈ F1 h := mem_filter.mpr ⟨mem_range.mpr (by omega), hp, h5⟩
    have hm2 : p ∉ F2 h := fun hm => by have := (mem_filter.mp hm).2.2; omega
    rw [ite_eq_left hm1, ite_eq_right hm2, add_zero]
    unfold eGen
    rw [ite_eq_right (by omega)]
    push_cast; exact le_refl _
  · have hm1 : p ∉ F1 h := fun hm => by have := (mem_filter.mp hm).2.2; omega
    have hpp : 2 * h < p * p := by nlinarith [Nat.mul_le_mul h5 h5]
    rw [ite_eq_right hm1, zero_add]
    unfold eGen
    rw [ite_eq_left ⟨hpp, h5⟩]
    rcases lt_or_ge p (2 * h) with hp2h | hp2h
    · rw [ite_eq_left (show p ∈ F2 h from mem_filter.mpr ⟨mem_range.mpr hp2h, hp, h5⟩)]
      exact mul_le_mul_of_nonneg_right (classBd_le_phi1 hh hodd h5 hp2h) hlog
    · rw [classBd_eq_zero hp2h, ite_eq_right (fun hm => by have := mem_range.mp (mem_filter.mp hm).1; omega)]
      simp

/-- The generic odd primes contribute at most the two prime sums. -/
lemma sum_eGen_le {h : ℕ} (hh : 13 ≤ h) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2) :
    ∑ p ∈ s, (eGen h p : ℝ) * Real.log p ≤
      ∑ p ∈ F1 h, 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p +
        ∑ p ∈ F2 h, (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p := by
  have hl : ∀ p ∈ range (2 * h), 0 ≤ Real.log p := fun p _ => Real.log_natCast_nonneg p
  calc ∑ p ∈ s, (eGen h p : ℝ) * Real.log p
      ≤ ∑ p ∈ s, ((if p ∈ F1 h then 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p else 0) +
          (if p ∈ F2 h then (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p else 0)) :=
        sum_le_sum (fun p hp => eGen_log_le hh (hs p hp).1 (hs p hp).2)
    _ = ∑ p ∈ s ∩ F1 h, 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p +
          ∑ p ∈ s ∩ F2 h, (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p := by
        rw [sum_add_distrib, sum_ite_mem, sum_ite_mem]
    _ ≤ _ := add_le_add
        (sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => by
          have := Real.log_natCast_nonneg p; positivity))
        (sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => by
          have := Real.log_natCast_nonneg p; have := phi1_nonneg ((p : ℝ) / h); positivity))

lemma padicValNat_three_24 : padicValNat 3 (5 ^ 2 - 1) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [show 5 ^ 2 - 1 = 3 * 8 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- The exponent of an odd prime: generic part plus the special contributions. -/
lemma eN_le_odd {q₀ h p : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) (hp : p.Prime) (hp2 : p ≠ 2) :
    (eN q₀ h p : ℝ) ≤ eGen h p + (if p = q₀ then 2 * (h : ℝ) * lev h p else 0) +
      (if p = 3 then (if q₀ = 5 then 2 * (h : ℝ) * lev h p + betaP h else 0) else 0) := by
  have h0 : (0 : ℝ) ≤ (if p = 3 then (if q₀ = 5 then 2 * (h : ℝ) * lev h p + betaP h else 0) else 0) := by
    split_ifs <;> positivity
  have h1 : (0 : ℝ) ≤ eGen h p := Nat.cast_nonneg _
  unfold eN
  rw [ite_eq_right hp2]
  by_cases hpq : p = q₀
  · rw [ite_eq_left hpq, ite_eq_left hpq]; push_cast; linarith
  · rw [ite_eq_right hpq, ite_eq_right hpq, add_zero]
    by_cases hd : p ∣ q₀ ^ 2 - 1
    · rw [ite_eq_left hd]
      have h3 : q₀ = 5 ∧ p = 3 := by
        rcases hq with rfl | rfl
        · exfalso
          have := Nat.le_of_dvd (by norm_num) hd
          interval_cases p <;> revert hp hp2 hd <;> norm_num
        · refine ⟨rfl, ?_⟩
          have := Nat.le_of_dvd (by norm_num) hd
          interval_cases p <;> first | rfl | (exfalso; revert hp hp2 hd; norm_num)
      obtain ⟨rfl, rfl⟩ := h3
      rw [padicValNat_three_24, ite_eq_left rfl, ite_eq_left rfl]
      push_cast; linarith
    · rw [ite_eq_right hd]; linarith

lemma sum_ite_eq_le {s : Finset ℕ} {a : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    ∑ p ∈ s, (if p = a then c else 0) ≤ c := by
  rw [sum_ite_eq']; split_ifs <;> linarith

lemma aQ_ge {h : ℕ} (hh : 7 ≤ h) : ((h : ℝ) ^ 2 - 7 * h - 2) / 3 ≤ aQ h := by
  have hle : 6 * h ≤ h * (h - 1) := by
    have : 7 ≤ h - 1 + 1 := by omega
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ h)]
  have hn : h * (h - 1) - 6 * h ≤ 3 * aQ h + 2 := by
    unfold aQ
    generalize h * (h - 1) - 6 * h = t
    omega
  have hc : ((h * (h - 1) - 6 * h : ℕ) : ℝ) = (h : ℝ) ^ 2 - 7 * h := by
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ h)]; push_cast; ring
  have : ((h * (h - 1) - 6 * h : ℕ) : ℝ) ≤ 3 * (aQ h : ℝ) + 2 := by exact_mod_cast hn
  rw [hc] at this
  linarith

/-- **The size of the denominator**, for `h ≥ 13`. -/
theorem log_denQ_le {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) {h : ℕ} (hh : 13 ≤ h) :
    Real.log ((denQ q₀ h : ℚ) : ℝ) ≤
      ∑ p ∈ F1 h, 2 * (h : ℝ) * (lev h p : ℝ) * Real.log p +
        ∑ p ∈ F2 h, (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p +
        (alphaQ q₀ - 133 / 60) * (h : ℝ) ^ 2 + (30 * h + 6 * h * Real.log h) := by
  have hq2 : 2 ≤ q₀ := by rcases hq with rfl | rfl <;> norm_num
  have hqp : q₀.Prime := by rcases hq with rfl | rfl <;> norm_num
  set H : ℝ := (h : ℝ) with hH
  have hH1 : (13 : ℝ) ≤ H := by rw [hH]; exact_mod_cast hh
  -- `log denQ = Σ eN log p − aQ log q₀`
  have hNpos : 0 < Nden q₀ h := prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.pos _)
  have hden : ((denQ q₀ h : ℚ) : ℝ) = (Nden q₀ h : ℝ) / (q₀ : ℝ) ^ aQ h := by
    unfold denQ; push_cast; ring
  have hq0 : (0 : ℝ) < q₀ := by exact_mod_cast (by omega : 0 < q₀)
  rw [hden, Real.log_div (by exact_mod_cast hNpos.ne') (pow_ne_zero _ hq0.ne'), Real.log_pow]
  have hlogN : Real.log (Nden q₀ h) = ∑ p ∈ SP q₀ h, (eN q₀ h p : ℝ) * Real.log p := by
    unfold Nden
    push_cast
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (mem_filter.mp hp).2.ne_zero))]
    simp only [Real.log_pow]
  rw [hlogN]
  have h2S : 2 ∈ SP q₀ h := mem_filter.mpr ⟨mem_range.mpr (by nlinarith), Nat.prime_two⟩
  rw [← add_sum_erase _ _ h2S]
  have he2 : eN q₀ h 2 = betaP h + h * (Nat.log 2 h + 6) := by unfold eN; rw [ite_eq_left rfl]
  rw [he2]
  -- the odd primes
  set s := (SP q₀ h).erase 2
  have hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2 := fun p hp => ⟨(mem_filter.mp (mem_of_mem_erase hp)).2, ne_of_mem_erase hp⟩
  set A : ℝ := 2 * H * lev h q₀ * Real.log q₀
  set B : ℝ := if q₀ = 5 then (2 * H * lev h 3 + betaP h) * Real.log 3 else 0
  have hodd : ∑ p ∈ s, (eN q₀ h p : ℝ) * Real.log p ≤
      ∑ p ∈ s, (eGen h p : ℝ) * Real.log p + A + B := by
    have hA0 : 0 ≤ A := by have := Real.log_natCast_nonneg q₀; positivity
    have hB0 : 0 ≤ B := by
      simp only [B]; split_ifs
      · have := Real.log_natCast_nonneg 3; positivity
      · exact le_refl _
    calc ∑ p ∈ s, (eN q₀ h p : ℝ) * Real.log p
        ≤ ∑ p ∈ s, ((eGen h p : ℝ) * Real.log p + (if p = q₀ then A else 0) + (if p = 3 then B else 0)) := by
          refine sum_le_sum (fun p hp => ?_)
          have hl := Real.log_natCast_nonneg p
          have := mul_le_mul_of_nonneg_right (eN_le_odd (h := h) hq (hs p hp).1 (hs p hp).2) hl
          refine this.trans (le_of_eq ?_)
          simp only [A, B]
          split_ifs with h1 h2 h3 <;> (try subst h1) <;> (try subst h2) <;> (try simp_all) <;> ring
      _ ≤ ∑ p ∈ s, (eGen h p : ℝ) * Real.log p + A + B := by
          rw [sum_add_distrib, sum_add_distrib]
          linarith [sum_ite_eq_le (s := s) (a := q₀) hA0, sum_ite_eq_le (s := s) (a := 3) hB0]
  have hgen := sum_eGen_le hh s hs
  -- the remainder
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hl3' : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlq : 0 ≤ Real.log q₀ := Real.log_natCast_nonneg q₀
  have hlq' : Real.log q₀ ≤ 4 := by
    have := Real.log_le_sub_one_of_pos hq0
    have : (q₀ : ℝ) ≤ 5 := by rcases hq with rfl | rfl <;> norm_num
    linarith
  have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hβ : 4 * (betaP h : ℝ) ≤ H ^ 2 + 2 * H := by
    have := betaP_le h; rw [hH]; exact_mod_cast this
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log H := by
    have hp := Nat.pow_log_le_self 2 (by omega : h ≠ 0)
    have : ((2 : ℝ) ^ Nat.log 2 h) ≤ H := by rw [hH]; exact_mod_cast hp
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) this
  have hlev : ∀ r : ℕ, r.Prime → (lev h r : ℝ) * Real.log r ≤ Real.log 2 + Real.log H := fun r hr => by
    have := lev_mul_log_le hr (by omega : 1 ≤ h)
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    exact this
  have hA : A ≤ 2 * H * (Real.log 2 + Real.log H) := by
    simp only [A]; rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlev q₀ hqp) (by positivity)
  have haQ := aQ_ge (h := h) (by omega)
  have haQl : ((H ^ 2 - 7 * H - 2) / 3) * Real.log q₀ ≤ (aQ h : ℝ) * Real.log q₀ :=
    mul_le_mul_of_nonneg_right haQ hlq
  have h2t : ((betaP h + h * (Nat.log 2 h + 6) : ℕ) : ℝ) * Real.log 2 ≤
      (H ^ 2 + 2 * H) / 4 * Real.log 2 + H * Real.log H + 6 * H * Real.log 2 := by
    push_cast
    have e1 : (betaP h : ℝ) * Real.log 2 ≤ (H ^ 2 + 2 * H) / 4 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hl2.le
    have e2 : H * ((Nat.log 2 h : ℝ) * Real.log 2) ≤ H * Real.log H :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    rw [← hH]; nlinarith
  have hBb : B ≤ (if q₀ = 5 then Real.log 3 / 4 else 0) * H ^ 2 +
      (2 * H * (Real.log 2 + Real.log H) + H / 2 * Real.log 3) := by
    simp only [B]
    split_ifs
    · have e1 : 2 * H * lev h 3 * Real.log 3 ≤ 2 * H * (Real.log 2 + Real.log H) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlev 3 (by norm_num)) (by positivity)
      have e2 : (betaP h : ℝ) * Real.log 3 ≤ (H ^ 2 + 2 * H) / 4 * Real.log 3 :=
        mul_le_mul_of_nonneg_right (by linarith) hl3
      nlinarith
    · have : 0 ≤ 2 * H * (Real.log 2 + Real.log H) := by positivity
      nlinarith
  -- combine
  have hrem : 2 * H * (Real.log 2 + Real.log H) * 2 + H * Real.log H + (6 * H + H / 2) * Real.log 2 +
      H / 2 * Real.log 3 + (7 * H + 2) / 3 * Real.log q₀ ≤ 30 * H + 6 * H * Real.log H := by
    nlinarith
  unfold alphaQ
  have hdef : (if q₀ = 5 then Real.log 3 / 4 else 0) * H ^ 2 =
      (if q₀ = 5 then Real.log 3 / 4 else 0) * H ^ 2 := rfl
  nlinarith

/-- `30h + 6h log h = o(h²)`. -/
lemma eventually_rem_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop, 30 * (h : ℝ) + 6 * (h : ℝ) * Real.log h ≤ c * (h : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop ⌈(24 / c) ^ 2 + 60 / c + 1⌉₊] with h hh
  have hH : (24 / c) ^ 2 + 60 / c + 1 ≤ (h : ℝ) := Nat.ceil_le.mp hh
  set H : ℝ := (h : ℝ)
  have hc24 : 0 ≤ 24 / c := by positivity
  have hc60 : 0 ≤ 60 / c := by positivity
  have hH0 : 0 < H := by nlinarith
  set s := Real.sqrt H
  have hs2 : s ^ 2 = H := Real.sq_sqrt hH0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hH0
  have hs24 : 24 / c ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hcs : 24 ≤ c * s := by rwa [div_le_iff₀ hc, mul_comm] at hs24
  have hcH : 60 ≤ c * H := by
    have : 60 / c ≤ H := by nlinarith
    rwa [div_le_iff₀ hc, mul_comm] at this
  have hlog : Real.log H ≤ 2 * s := by
    have h1 := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log H = 2 * Real.log s := by rw [← hs2, Real.log_pow]; push_cast; ring
    linarith
  have h3 : 6 * H * Real.log H ≤ 12 * H * s := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ H * s / 2)]

/-- **The arithmetic bound.** -/
theorem arith_denQ {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) :
    ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Real.log ((denQ q₀ h : ℚ) : ℝ) ≤ (alphaQ q₀ + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [eventually_primeSum_lev_le (ε / 3) (by positivity),
    eventually_primeSum_phi1_le (ε / 3) (by positivity), eventually_rem_le (ε / 3) (by positivity),
    eventually_ge_atTop 13] with h h1 h2 h3 h4
  have := log_denQ_le hq h4
  unfold F1 F2 at this
  nlinarith

/-! ### The margins -/

lemma log_three_le : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h1
  norm_num at h1; linarith

lemma log_three_ge : Real.log 2 + 1 / 3 ≤ Real.log 3 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  rw [Real.log_div (by norm_num) (by norm_num)] at h1
  norm_num at h1; linarith

lemma log_five_ge : 2 * Real.log 2 + 1 / 5 ≤ Real.log 5 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h1
  norm_num at h1; linarith

theorem margin_three : alphaQ 3 + (-2078 / 1000) < 0 := by
  unfold alphaQ
  rw [ite_eq_right (by norm_num)]
  have := Real.log_two_gt_d9
  have := log_three_ge
  push_cast
  linarith

theorem margin_five : alphaQ 5 + (-2385 / 1000) < 0 := by
  unfold alphaQ
  rw [ite_eq_left rfl]
  have := Real.log_two_lt_d9
  have := log_three_le
  have := log_five_ge
  push_cast
  linarith

/-! ### The main theorems -/

/-- The bounds for `χ₂(1/3)`. -/
noncomputable def boundsThree : MachineBounds 3 where
  den := denQ 3
  den_pos := denQ_pos (by norm_num)
  den_int := denQ_int (Or.inl rfl)
  α := alphaQ 3
  β := -2078 / 1000
  margin := margin_three
  arith := arith_denQ (Or.inl rfl)
  analytic := Cert.Q3.analytic
  nonvan := nonvan_three

/-- The bounds for `χ₂(1/5)`. -/
noncomputable def boundsFive : MachineBounds 5 where
  den := denQ 5
  den_pos := denQ_pos (by norm_num)
  den_int := denQ_int (Or.inr rfl)
  α := alphaQ 5
  β := -2385 / 1000
  margin := margin_five
  arith := arith_denQ (Or.inr rfl)
  analytic := Cert.Q5.analytic
  nonvan := nonvan_five

/-- **Main Theorem.** `χ₂(1/3)` is irrational. -/
theorem chi2_one_third_irrational : Chi2OneThirdIrrational := by
  have := irrational_of_bounds boundsThree
  unfold Chi2OneThirdIrrational
  simpa using this

/-- **Main Theorem.** `χ₂(1/5)` is irrational. -/
theorem chi2_one_fifth_irrational : Chi2OneFifthIrrational := by
  have := irrational_of_bounds boundsFive
  unfold Chi2OneFifthIrrational
  simpa using this

end Chi2Irr
