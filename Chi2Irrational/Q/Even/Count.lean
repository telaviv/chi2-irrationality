/-
# Lemma 10_e, step 4: counting lemmas

* `cntL L a b = #{ℓ < L : 2^{ℓ+1} ∣ a − b}`, a lower bound for `v₂(a − b)` (`padicNorm_sub_le_cntL`).
* `sum_cntL_ge`: for `T` with fibres of `g` of size `≤ μ`,
  `Σ_{i,j∈T, g i ≠ g j} cntL L (g i) (g j) ≥ |T|²(1 − 2^{−L}) − μ L |T|`
  (pairs congruent mod `2^{ℓ+1}`: Cauchy–Schwarz over the residues, `sq_sum_le_card_mul_sum_sq`).
  For the nodes (`μ = 2`) and the poles (`μ = 1`) this is RESULT §2 step 4's `N(I, n₂)` and `SF(P)`,
  in ordered-pair form (`V(T)²`).
* `le_padicNorm_of_le`: `2^{−⌊log₂ M⌋} ≤ |n|₂` for `1 ≤ n ≤ M` (the derivative loss `λ_m`).
* `large_node`: `⌊log₂ M⌋·d ≤ e·max(0, 2M − h) + h(2⌊log₂ h⌋ + 1)` for `d ≤ h`, `e ≥ 1` (RESULT §2 step 5).
-/
import Mathlib

namespace Chi2Irr
namespace Q

open Finset

/-- `#{ℓ < L : 2^{ℓ+1} ∣ a − b}`. -/
def cntL (L a b : ℕ) : ℕ := ((range L).filter (fun l => (2 : ℤ) ^ (l + 1) ∣ (a : ℤ) - b)).card

lemma cntL_comm (L a b : ℕ) : cntL L a b = cntL L b a := by
  unfold cntL
  congr 1
  ext l
  simp only [mem_filter]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by rw [← dvd_neg, neg_sub]; exact h2⟩

lemma cntL_le_v2 {L a b : ℕ} (hab : a ≠ b) : cntL L a b ≤ padicValInt 2 ((a : ℤ) - b) := by
  have hne : (a : ℤ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  unfold cntL
  calc ((range L).filter (fun l => (2 : ℤ) ^ (l + 1) ∣ (a : ℤ) - b)).card
      ≤ (range (padicValInt 2 ((a : ℤ) - b))).card := by
        refine card_le_card (fun l hl => ?_)
        obtain ⟨_, hd⟩ := mem_filter.mp hl
        have := (padicValInt_dvd_iff (p := 2) (l + 1) ((a : ℤ) - b)).mp (by exact_mod_cast hd)
        rcases this with h0 | h1
        · exact absurd h0 hne
        · exact mem_range.mpr (by omega)
    _ = _ := card_range _

lemma padicNorm_sub_le_cntL {L a b : ℕ} (hab : a ≠ b) :
    padicNorm 2 ((a : ℚ) - b) ≤ (2 : ℚ) ^ (-(cntL L a b : ℤ)) := by
  have hne : (a : ℤ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  have e : ((a : ℚ) - b) = (((a : ℤ) - b : ℤ) : ℚ) := by push_cast; ring
  rw [e, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hne), padicValRat.of_int]
  push_cast
  exact zpow_le_zpow_right₀ (by norm_num) (by have := cntL_le_v2 (L := L) hab; omega)

/-! ### Pigeonhole -/

lemma sum_mod_sq_ge {α : Type*} (T : Finset α) (g : α → ℕ) (N : ℕ) (hN : 0 < N) :
    (T.card : ℚ) ^ 2 ≤ N * ∑ i ∈ T, ∑ j ∈ T, (if g i % N = g j % N then (1 : ℚ) else 0) := by
  set n : ℕ → ℚ := fun c => ∑ j ∈ T, (if g j % N = c then (1 : ℚ) else 0) with hn
  have h1 : ∑ i ∈ T, ∑ j ∈ T, (if g i % N = g j % N then (1 : ℚ) else 0) = ∑ i ∈ T, n (g i % N) := by
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
    simp only [eq_comm]
  have hmaps : ∀ i ∈ T, g i % N ∈ range N := fun i _ => mem_range.mpr (Nat.mod_lt _ hN)
  have h2 : ∑ i ∈ T, n (g i % N) = ∑ c ∈ range N, n c ^ 2 := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl (fun c _ => ?_)
    rw [sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2]), sum_const, nsmul_eq_mul, sq]
    congr 1
    rw [hn]; simp only [sum_boole]
  have h3 : ∑ c ∈ range N, n c = T.card := by
    rw [hn, sum_comm]
    simp only [sum_ite_eq, mem_range, Nat.mod_lt _ hN, ite_true, sum_const, nsmul_eq_mul, mul_one]
  have hcs := sq_sum_le_card_mul_sum_sq (s := range N) (f := n)
  rw [h3, card_range] at hcs
  rw [h1, h2]
  exact hcs

lemma geom_half (L : ℕ) : ∑ l ∈ range L, (1 : ℚ) / 2 ^ (l + 1) = 1 - 1 / 2 ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, ih, pow_succ]; field_simp; ring

/-- **The congruence count.** -/
theorem sum_cntL_ge {α : Type*} (T : Finset α) (g : α → ℕ) (μ L : ℕ)
    (hμ : ∀ i ∈ T, (T.filter (fun j => g j = g i)).card ≤ μ) :
    (T.card : ℚ) ^ 2 * (1 - 1 / 2 ^ L) - μ * L * T.card ≤
      ∑ i ∈ T, ∑ j ∈ T, ((if g i = g j then 0 else cntL L (g i) (g j) : ℕ) : ℚ) := by
  -- rewrite the right side as a sum over `ℓ`
  have hR : ∑ i ∈ T, ∑ j ∈ T, ((if g i = g j then 0 else cntL L (g i) (g j) : ℕ) : ℚ) =
      ∑ l ∈ range L, ∑ i ∈ T, ∑ j ∈ T,
        (if g i ≠ g j ∧ (2 : ℤ) ^ (l + 1) ∣ (g i : ℤ) - g j then (1 : ℚ) else 0) := by
    symm
    rw [Finset.sum_comm (s := range L) (t := T)]
    refine sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm (s := range L) (t := T)]
    refine sum_congr rfl (fun j _ => ?_)
    by_cases hij : g i = g j
    · simp [hij]
    · simp only [hij, ite_false, ne_eq, not_false_eq_true, true_and]
      rw [cntL, card_filter]; push_cast; rfl
  rw [hR]
  have hl : ∀ l ∈ range L, (T.card : ℚ) ^ 2 * (1 / 2 ^ (l + 1)) - μ * T.card ≤
      ∑ i ∈ T, ∑ j ∈ T, (if g i ≠ g j ∧ (2 : ℤ) ^ (l + 1) ∣ (g i : ℤ) - g j then (1 : ℚ) else 0) := by
    intro l _
    set N := 2 ^ (l + 1) with hN
    have hN0 : 0 < N := by positivity
    have hpig := sum_mod_sq_ge T g N hN0
    have hsplit : ∀ i ∈ T, ∀ j ∈ T, (if g i % N = g j % N then (1 : ℚ) else 0) ≤
        (if g i ≠ g j ∧ (2 : ℤ) ^ (l + 1) ∣ (g i : ℤ) - g j then (1 : ℚ) else 0) +
          (if g j = g i then (1 : ℚ) else 0) := by
      intro i _ j _
      by_cases hm : g i % N = g j % N
      · have hd : (2 : ℤ) ^ (l + 1) ∣ (g i : ℤ) - g j := by
          have := (Nat.modEq_iff_dvd (n := N) (a := g j) (b := g i)).mp hm.symm
          rw [hN] at this; exact_mod_cast this
        by_cases he : g j = g i
        · simp [he]
        · simp [hm, hd, Ne.symm he, he]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hm)]; positivity
    have hsum := sum_le_sum (fun i hi => sum_le_sum (fun j hj => hsplit i hi j hj))
    simp only [sum_add_distrib] at hsum
    have hdiag : ∑ i ∈ T, ∑ j ∈ T, (if g j = g i then (1 : ℚ) else 0) ≤ μ * T.card := by
      calc ∑ i ∈ T, ∑ j ∈ T, (if g j = g i then (1 : ℚ) else 0)
          ≤ ∑ i ∈ T, (μ : ℚ) := sum_le_sum (fun i hi => by
            rw [sum_boole]; exact_mod_cast hμ i hi)
        _ = μ * T.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
    have hN' : (N : ℚ) = 2 ^ (l + 1) := by rw [hN]; push_cast; rfl
    rw [hN'] at hpig
    have hpos : (0 : ℚ) < 2 ^ (l + 1) := by positivity
    have : (T.card : ℚ) ^ 2 * (1 / 2 ^ (l + 1)) ≤
        ∑ i ∈ T, ∑ j ∈ T, (if g i % N = g j % N then (1 : ℚ) else 0) := by
      rw [mul_one_div, div_le_iff₀ hpos, mul_comm]; exact hpig
    linarith
  have := sum_le_sum hl
  rw [sum_sub_distrib, ← mul_sum, geom_half, sum_const, card_range, nsmul_eq_mul] at this
  linarith

/-! ### Logarithms -/

lemma le_padicNorm_of_le {n M : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    (2 : ℚ) ^ (-(Nat.log 2 M : ℤ)) ≤ padicNorm 2 (n : ℚ) := by
  have hn0 : n ≠ 0 := by omega
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn0), padicValRat.of_nat]
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  have hd : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have hle : 2 ^ padicValNat 2 n ≤ M := (Nat.le_of_dvd (by omega) hd).trans hnM
  have := Nat.le_log_of_pow_le (by norm_num) hle
  omega

lemma log_sq_le (h : ℕ) : Nat.log 2 (h ^ 2) ≤ 2 * Nat.log 2 h + 1 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  have h1 : h < 2 ^ (Nat.log 2 h + 1) := Nat.lt_pow_succ_log_self (by norm_num) h
  have h2 : h ^ 2 < 2 ^ (2 * Nat.log 2 h + 2) := by
    calc h ^ 2 < (2 ^ (Nat.log 2 h + 1)) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
      _ = 2 ^ (2 * Nat.log 2 h + 2) := by rw [← pow_mul]; ring_nf
  have := Nat.log_lt_of_lt_pow (by positivity) h2
  omega

lemma sq_add_le_two_pow (n : ℕ) : n ^ 2 + n ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : 2 * n + 2 ≤ 2 ^ (n + 2) := by
      have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      have h4 : 2 ^ (n + 2) = 4 * 2 ^ n := by ring
      omega
    calc (n + 1) ^ 2 + (n + 1) = (n ^ 2 + n) + (2 * n + 2) := by ring
      _ ≤ 2 ^ (n + 2) + 2 ^ (n + 2) := add_le_add ih h1
      _ = 2 ^ (n + 1 + 2) := by ring

/-- **Large nodes.** -/
theorem large_node (e h M d : ℕ) (he : 1 ≤ e) (hd : d ≤ h) :
    ((Nat.log 2 M : ℕ) : ℤ) * d ≤ e * max 0 (2 * (M : ℤ) - h) + h * (2 * Nat.log 2 h + 1) := by
  have hmax : 0 ≤ max 0 (2 * (M : ℤ) - h) := le_max_left _ _
  have hmax2 : 2 * (M : ℤ) - h ≤ max 0 (2 * (M : ℤ) - h) := le_max_right _ _
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hemax : max 0 (2 * (M : ℤ) - h) ≤ e * max 0 (2 * (M : ℤ) - h) := by nlinarith
  have hd' : (d : ℤ) ≤ h := by exact_mod_cast hd
  set Λ := Nat.log 2 M with hΛ
  rcases le_or_gt M (h ^ 2) with hM | hM
  · have h1 : Λ ≤ 2 * Nat.log 2 h + 1 := (Nat.log_mono_right hM).trans (log_sq_le h)
    have h1' : (Λ : ℤ) ≤ 2 * Nat.log 2 h + 1 := by exact_mod_cast h1
    have h0 : (0 : ℤ) ≤ Λ := by positivity
    have hd0 : (0 : ℤ) ≤ d := by positivity
    nlinarith
  · have hM0 : M ≠ 0 := by intro h0; rw [h0] at hM; exact absurd hM (Nat.not_lt_zero _)
    have hpow : 2 ^ Λ ≤ M := Nat.pow_log_le_self 2 hM0
    rcases lt_or_ge Λ (2 * h) with hl | hl
    · have hl' : (Λ : ℤ) + 1 ≤ 2 * h := by exact_mod_cast hl
      have hM' : (h : ℤ) ^ 2 < M := by exact_mod_cast hM
      have h0 : (0 : ℤ) ≤ Λ := by positivity
      have hd0 : (0 : ℤ) ≤ d := by positivity
      have hh0 : (0 : ℤ) ≤ h := by positivity
      have key : (Λ : ℤ) * d ≤ 2 * (M : ℤ) - h := by
        rcases Nat.eq_zero_or_pos h with hz | hz
        · have : d = 0 := by omega
          subst this; simp; omega
        · have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast hz
          nlinarith
      have : (0 : ℤ) ≤ h * (2 * Nat.log 2 h + 1) := by positivity
      linarith
    · have h2 := sq_add_le_two_pow Λ
      have h3 : 2 * (h * Λ + h) ≤ Λ ^ 2 + Λ := by
        have : 2 * h ≤ Λ := hl
        nlinarith
      have h4 : 2 ^ (Λ + 2) = 4 * 2 ^ Λ := by ring
      have key : h * Λ + h ≤ 2 * M := by omega
      have key' : (Λ : ℤ) * d ≤ 2 * (M : ℤ) - h := by
        have hk : ((h * Λ + h : ℕ) : ℤ) ≤ ((2 * M : ℕ) : ℤ) := by exact_mod_cast key
        push_cast at hk
        have : (Λ : ℤ) * d ≤ Λ * h := mul_le_mul_of_nonneg_left hd' (by positivity)
        nlinarith
      have : (0 : ℤ) ≤ h * (2 * Nat.log 2 h + 1) := by positivity
      linarith

end Q
end Chi2Irr
