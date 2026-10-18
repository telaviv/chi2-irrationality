/-
# Lemma P along `K = 3ℓ`: setup

* `rt K m`: the roots of `F_ij` and `g_i`, i.e. `x_m` for `m < K` and `0` (the factor `u`) for `m = K`;
  `Fpoly_eq_prod`, `gpoly_eq_prod` write `F_ij`, `g_i` as products over `range (K+1)`.
* ℓ-adic size of `t − rt K m` for `t ∈ ℕ`: `≤ 1` always; `≤ ℓ⁻¹` iff `ℓ | 2t+2m+1` (`m < K`) or `ℓ | t` (`m = K`).
* Progressions: if `ℓ | 2t+2γ+1` (`γ < ℓ`), then `ℓ | 2t+2m+1 ↔ m % ℓ = γ`, and `ℓ | t ↔ γ = κ`, `κ = ℓ/2`.
* Classes: for `m < 3ℓ`, `m % ℓ = γ ↔ m ∈ {γ, γ+ℓ, γ+2ℓ}`.
-/
import Chi2Irrational.NonVan.Gram
import Chi2Irrational.NonVan.Counting

namespace Chi2Irr

open Polynomial Finset

/-- The extended roots: `x_m` for `m < K`, and `0` for `m ≥ K`. -/
noncomputable def rt (K m : ℕ) : ℚ := if m < K then pole m else 0

lemma rt_of_lt {K m : ℕ} (h : m < K) : rt K m = pole m := ite_eq_left h

lemma rt_self (K : ℕ) : rt K K = 0 := ite_eq_right (lt_irrefl K)

lemma prod_range_succ_erase_rt {K : ℕ} {s : Finset ℕ} (hs : s ⊆ range K) :
    ∏ m ∈ insert K s, (X - C (rt K m)) = X * ∏ m ∈ s, (X - C (pole m)) := by
  have hK : K ∉ s := fun h => lt_irrefl K (mem_range.mp (hs h))
  rw [prod_insert hK, rt_self, map_zero, sub_zero]
  congr 1
  exact prod_congr rfl (fun m hm => by rw [rt_of_lt (mem_range.mp (hs hm))])

lemma Fpoly_eq_prod {K i j : ℕ} (hi : i < K) (hj : j < K) :
    Fpoly K i j = ∏ m ∈ ((range (K + 1)).erase i).erase j, (X - C (rt K m)) := by
  rw [range_add_one, erase_insert_of_ne (Nat.ne_of_gt hi), erase_insert_of_ne (Nat.ne_of_gt hj),
    prod_range_succ_erase_rt (fun m hm => mem_of_mem_erase (mem_of_mem_erase hm))]
  rfl

lemma gpoly_eq_prod {K i : ℕ} (hi : i < K) :
    gpoly K i = ∏ m ∈ (range (K + 1)).erase i, (X - C (rt K m)) := by
  rw [range_add_one, erase_insert_of_ne (Nat.ne_of_gt hi),
    prod_range_succ_erase_rt (fun m hm => mem_of_mem_erase hm)]
  rfl

/-! ### ℓ-adic sizes of `t − rt K m` -/

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma two_not_dvd_of_ne (hℓ2 : ℓ ≠ 2) : ¬ ℓ ∣ 2 := by
  intro h
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp h)

lemma padicNorm_two (hℓ2 : ℓ ≠ 2) : padicNorm ℓ (2 : ℚ) = 1 := by
  have := padicNorm_natCast_eq_one (ℓ := ℓ) (two_not_dvd_of_ne hℓ2)
  simpa using this

lemma sub_pole_eq (t : ℚ) (m : ℕ) : t - pole m = ((2 * t + 2 * m + 1) : ℚ) / 2 := by
  unfold pole; ring

lemma padicNorm_sub_pole (hℓ2 : ℓ ≠ 2) (t m : ℕ) :
    padicNorm ℓ ((t : ℚ) - pole m) = padicNorm ℓ ((2 * t + 2 * m + 1 : ℕ) : ℚ) := by
  rw [sub_pole_eq, padicNorm.div, padicNorm_two hℓ2, div_one]
  push_cast; ring_nf

lemma padicNorm_sub_rt_le_one (hℓ2 : ℓ ≠ 2) (K t m : ℕ) : padicNorm ℓ ((t : ℚ) - rt K m) ≤ 1 := by
  unfold rt
  split_ifs
  · rw [padicNorm_sub_pole hℓ2]; exact padicNorm.of_nat _
  · rw [sub_zero]; exact padicNorm.of_nat _

lemma padicNorm_sub_rt_close {K t m : ℕ} (hℓ2 : ℓ ≠ 2) (hm : m < K) (hd : ℓ ∣ 2 * t + 2 * m + 1) :
    padicNorm ℓ ((t : ℚ) - rt K m) ≤ (ℓ : ℚ)⁻¹ := by
  rw [rt_of_lt hm, padicNorm_sub_pole hℓ2]
  exact padicNorm_le_inv_of_lt_one ((padicNorm.nat_lt_one_iff _).mpr hd)

lemma padicNorm_sub_rt_unit {K t m : ℕ} (hℓ2 : ℓ ≠ 2) (hm : m < K) (hd : ¬ ℓ ∣ 2 * t + 2 * m + 1) :
    padicNorm ℓ ((t : ℚ) - rt K m) = 1 := by
  rw [rt_of_lt hm, padicNorm_sub_pole hℓ2]
  exact padicNorm_natCast_eq_one hd

lemma padicNorm_sub_rt_self_close {K t : ℕ} (hd : ℓ ∣ t) :
    padicNorm ℓ ((t : ℚ) - rt K K) ≤ (ℓ : ℚ)⁻¹ := by
  rw [rt_self, sub_zero]
  exact padicNorm_le_inv_of_lt_one ((padicNorm.nat_lt_one_iff _).mpr hd)

/-! ### Progressions and classes -/

lemma odd_of_prime_ne_two (hℓ2 : ℓ ≠ 2) : ℓ % 2 = 1 :=
  Nat.odd_iff.mp (hℓ.out.odd_of_ne_two hℓ2)

/-- `κ = (ℓ − 1)/2`. -/
def kap (ℓ : ℕ) : ℕ := ℓ / 2

lemma two_kap_add_one (hℓ2 : ℓ ≠ 2) : 2 * kap ℓ + 1 = ℓ := by
  have := odd_of_prime_ne_two (hℓ := hℓ) hℓ2
  unfold kap; omega

/-- On the progression of `γ`, the close poles are exactly the class of `γ`. -/
lemma dvd_iff_mod_eq (hℓ2 : ℓ ≠ 2) {γ t : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1) (m : ℕ) :
    ℓ ∣ 2 * t + 2 * m + 1 ↔ m % ℓ = γ := by
  have hcop : Nat.Coprime ℓ 2 := (Nat.coprime_primes hℓ.out Nat.prime_two).mpr hℓ2
  constructor
  · intro hm
    have h1 : 2 * t + 2 * m + 1 ≡ 2 * t + 2 * γ + 1 [MOD ℓ] :=
      (Nat.modEq_zero_iff_dvd.mpr hm).trans (Nat.modEq_zero_iff_dvd.mpr ht).symm
    have h2 : 2 * m ≡ 2 * γ [MOD ℓ] := by
      have := Nat.ModEq.add_right_cancel' 1 h1
      rw [add_comm (2 * t), add_comm (2 * t)] at this
      exact Nat.ModEq.add_right_cancel' (2 * t) this
    have h3 : m ≡ γ [MOD ℓ] := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.coprime_comm] using hcop) h2
    rw [h3, Nat.mod_eq_of_lt hγ]
  · intro hm
    have h3 : m ≡ γ [MOD ℓ] := by
      unfold Nat.ModEq; rw [hm, Nat.mod_eq_of_lt hγ]
    have h1 : 2 * t + 2 * m + 1 ≡ 2 * t + 2 * γ + 1 [MOD ℓ] :=
      ((h3.mul_left 2).add_left (2 * t)).add_right 1
    exact (Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr ht)))

/-- On the progression of `γ`, `ℓ | t` iff `γ = κ`. -/
lemma dvd_t_iff (hℓ2 : ℓ ≠ 2) {γ t : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1) :
    ℓ ∣ t ↔ γ = kap ℓ := by
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  constructor
  · intro h
    have h1 : ℓ ∣ 2 * γ + 1 := by
      have := (Nat.dvd_add_right (dvd_mul_of_dvd_right h 2)).mp (by simpa [add_assoc] using ht)
      exact this
    obtain ⟨c, hc⟩ := h1
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    subst hc1
    omega
  · intro h
    subst h
    have h1 : ℓ ∣ 2 * t + ℓ := by have := ht; rwa [add_assoc, hk] at this
    have h2 : ℓ ∣ 2 * t := (Nat.dvd_add_left (dvd_refl ℓ)).mp h1
    exact (Nat.Prime.dvd_mul hℓ.out).mp h2 |>.resolve_left (two_not_dvd_of_ne hℓ2)

/-- The class `{γ, γ+ℓ, γ+2ℓ}` inside `[0, 3ℓ)`. -/
lemma mod_eq_iff_mem_cls {γ m : ℕ} (hγ : γ < ℓ) (hm : m < 3 * ℓ) :
    m % ℓ = γ ↔ m = γ ∨ m = γ + ℓ ∨ m = γ + 2 * ℓ := by
  have hℓpos : 0 < ℓ := hℓ.out.pos
  constructor
  · intro h
    have hq : m / ℓ < 3 := (Nat.div_lt_iff_lt_mul hℓpos).mpr (by linarith)
    have hdm := Nat.div_add_mod m ℓ
    interval_cases hk : m / ℓ <;> omega
  · rintro (rfl | rfl | rfl)
    · exact Nat.mod_eq_of_lt hγ
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hγ]
    · rw [show γ + 2 * ℓ = γ + ℓ * 2 by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hγ]

end Chi2Irr
