/-
# Lemma P along `K = 3ℓ`: the pole term mod `ℓ`

For `i = γ + ℓr` (`γ < ℓ`, `r < 3`, `ℓ ≥ 7`, `ℓ ∤ q`):
  `red(ℓ² S_i) = q̄^{2γ} q̄^{2r+1} red(T_n)`,  `T_n = Σ_{u<n} z^{2u+1}/(2u+1)²`, `z = 1/q`,
with `n = r` if `γ < κ` (type S) and `n = r + 1` otherwise (types D, L). Only the `j ≤ i` with `ℓ | 2j+1`,
i.e. `j = κ + ℓu`, survive in `ℓ² S_i = Σ_j q^{2(i−j)} ℓ²/(2j+1)²`, and `q̄^ℓ = q̄`.
-/
import Chi2Irrational.NonVan.Residues

namespace Chi2Irr

open Polynomial Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `T_n(q) = Σ_{u<n} z^{2u+1}/(2u+1)²`, `z = 1/q`. -/
def Tq (q n : ℕ) : ℚ := ∑ u ∈ range n, (1 / (q : ℚ)) ^ (2 * u + 1) / (2 * (u : ℚ) + 1) ^ 2

lemma dvd_two_mul_add_one_iff (hℓ2 : ℓ ≠ 2) (j : ℕ) : ℓ ∣ 2 * j + 1 ↔ j % ℓ = kap ℓ := by
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  have hκ : kap ℓ < ℓ := by omega
  have h0 : ℓ ∣ 2 * 0 + 2 * kap ℓ + 1 := by rw [mul_zero, zero_add, hk]
  have := dvd_iff_mod_eq hℓ2 hκ h0 j
  simpa using this

lemma pow_ell_mul (x : ZMod ℓ) (m : ℕ) : x ^ (ℓ * m) = x ^ m := by
  rw [pow_mul, ZMod.pow_card]

/-- The surviving indices of `ℓ² S_i`. -/
lemma filter_dvd_eq (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    (range (idx ℓ γ r + 1)).filter (fun j => ℓ ∣ 2 * j + 1) =
      (range (if γ < kap ℓ then r else r + 1)).image (fun u => idx ℓ (kap ℓ) u) := by
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  have hℓpos := hℓ.out.pos
  ext j
  rw [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hj, hd⟩
    have hmod := (dvd_two_mul_add_one_iff hℓ2 j).mp hd
    have hj3 : j < 3 * ℓ := lt_of_lt_of_le hj (by have := idx_lt hγ hr; omega)
    have hu : j / ℓ < 3 := div_lt_three hj3
    have hjd := Nat.mod_add_div j ℓ
    refine ⟨j / ℓ, mem_range.mpr ?_, ?_⟩
    · unfold idx at hj
      split_ifs with hs <;> interval_cases hq : j / ℓ <;> interval_cases r <;> omega
    · unfold idx; omega
  · rintro ⟨u, hu, rfl⟩
    have hu3 : u < 3 := by split_ifs at hu <;> rw [mem_range] at hu <;> omega
    refine ⟨?_, ?_⟩
    · unfold idx
      rw [mem_range] at hu
      split_ifs at hu with hs <;> interval_cases u <;> interval_cases r <;> omega
    · rw [dvd_two_mul_add_one_iff hℓ2]
      exact idx_mod (by omega)

theorem red_ell_sq_Spart (hℓ7 : 7 ≤ ℓ) {q : ℕ} (hℓq : ¬ ℓ ∣ q) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    (ℓ : ℚ) ^ 2 * Spart q (idx ℓ γ r) ∈ Zl ℓ ∧
    red ℓ ((ℓ : ℚ) ^ 2 * Spart q (idx ℓ γ r)) =
      (q : ZMod ℓ) ^ (2 * γ) * (q : ZMod ℓ) ^ (2 * r + 1) *
        red ℓ (Tq q (if γ < kap ℓ then r else r + 1)) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  have hℓpos := hℓ.out.pos
  set i := idx ℓ γ r
  have hi3 : i < 3 * ℓ := idx_lt hγ hr
  have hqn : padicNorm ℓ (q : ℚ) = 1 := padicNorm_natCast_q hℓq
  have hqmem : (q : ℚ) ∈ Zl ℓ := natCast_mem_Zl q
  -- the terms
  set f : ℕ → ℚ := fun j => (q : ℚ) ^ (2 * (i - j)) * ((ℓ : ℚ) ^ 2 / (2 * (j : ℚ) + 1) ^ 2)
  have hsum : (ℓ : ℚ) ^ 2 * Spart q i = ∑ j ∈ range (i + 1), f j := by
    unfold Spart; rw [mul_sum]
    refine sum_congr rfl (fun j _ => by simp only [f]; ring)
  -- `2j + 1` as a natural number
  have hcast : ∀ j : ℕ, (2 * (j : ℚ) + 1) = ((2 * j + 1 : ℕ) : ℚ) := fun j => by push_cast; ring
  -- non-surviving terms are `ℓ`-small, surviving ones integral
  have hsmall : ∀ j, ¬ ℓ ∣ 2 * j + 1 → padicNorm ℓ (f j) ≤ (ℓ : ℚ)⁻¹ := by
    intro j hj
    simp only [f]
    rw [padicNorm.mul, padicNorm_pow, hqn, one_pow, one_mul, padicNorm.div, padicNorm_ell_pow,
      hcast, padicNorm_pow, padicNorm_natCast_eq_one hj, one_pow, div_one]
    calc ((ℓ : ℚ)⁻¹) ^ 2 ≤ ((ℓ : ℚ)⁻¹) ^ 1 := inv_pow_anti (by norm_num)
      _ = _ := pow_one _
  -- surviving terms: `j = κ + ℓu`, `2j + 1 = ℓ(2u + 1)`
  have hsurv : ∀ u < 3, f (idx ℓ (kap ℓ) u) =
      (q : ℚ) ^ (2 * (i - idx ℓ (kap ℓ) u)) * (1 / (2 * (u : ℚ) + 1) ^ 2) := by
    intro u _
    simp only [f]
    congr 1
    have h2 : (2 * ((idx ℓ (kap ℓ) u : ℕ) : ℚ) + 1) = (ℓ : ℚ) * (2 * (u : ℚ) + 1) := by
      unfold idx; push_cast
      have : (2 * (kap ℓ : ℚ) + 1) = ℓ := by exact_mod_cast hk
      linear_combination this
    rw [h2]
    have : (2 * (u : ℚ) + 1) ≠ 0 := by positivity
    field_simp [ell_pos.ne']
  have hunit_u : ∀ u : ℕ, u < 3 → padicNorm ℓ ((2 * (u : ℚ) + 1) ^ 2) = 1 := by
    intro u hu
    rw [hcast, padicNorm_pow, padicNorm_natCast_eq_one, one_pow]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hf_mem : ∀ j ∈ range (i + 1), f j ∈ Zl ℓ := by
    intro j _
    by_cases hd : ℓ ∣ 2 * j + 1
    · have hmod := (dvd_two_mul_add_one_iff hℓ2 j).mp hd
      have hj3 : j < 3 * ℓ := by
        have := mem_range.mp ‹j ∈ range (i + 1)›; omega
      have hu : j / ℓ < 3 := div_lt_three hj3
      have hj : j = idx ℓ (kap ℓ) (j / ℓ) := by
        have := Nat.mod_add_div j ℓ; unfold idx; omega
      rw [hj, hsurv _ hu]
      refine mul_mem (pow_mem hqmem _) ?_
      rw [one_div]
      exact inv_mem_Zl (hunit_u _ hu)
    · exact (hsmall j hd).trans ell_inv_le_one
  refine ⟨by rw [hsum]; exact sum_mem hf_mem, ?_⟩
  rw [hsum, red_sum _ _ hf_mem]
  rw [← sum_filter_add_sum_filter_not (range (i + 1)) (fun j => ℓ ∣ 2 * j + 1)]
  have hzero : ∑ j ∈ (range (i + 1)).filter (fun j => ¬ ℓ ∣ 2 * j + 1), red ℓ (f j) = 0 := by
    refine sum_eq_zero (fun j hj => ?_)
    have hd := (mem_filter.mp hj).2
    exact (red_eq_zero_iff' ((hsmall j hd).trans ell_inv_le_one)).mpr (hsmall j hd)
  rw [hzero, add_zero, filter_dvd_eq hℓ2 hγ hr, sum_image (fun a _ b _ h => idx_injective h)]
  -- the target, termwise
  unfold Tq
  have hTmem : ∀ u ∈ range (if γ < kap ℓ then r else r + 1),
      (1 / (q : ℚ)) ^ (2 * u + 1) / (2 * (u : ℚ) + 1) ^ 2 ∈ Zl ℓ := by
    intro u hu
    have hu3 : u < 3 := by split_ifs at hu <;> rw [mem_range] at hu <;> omega
    rw [div_eq_mul_inv]
    refine mul_mem (pow_mem ?_ _) (inv_mem_Zl (hunit_u u hu3))
    rw [one_div]; exact inv_mem_Zl hqn
  rw [red_sum _ _ hTmem, mul_sum]
  refine sum_congr rfl (fun u hu => ?_)
  have hu3 : u < 3 := by split_ifs at hu <;> rw [mem_range] at hu <;> omega
  have hji : idx ℓ (kap ℓ) u ≤ i := by
    have := (mem_filter.mp ((filter_dvd_eq hℓ2 hγ hr).symm ▸ mem_image_of_mem _ hu)).1
    exact Nat.lt_succ_iff.mp (mem_range.mp this)
  -- `q̄^{2(i−j)} = q̄^{2γ} q̄^{2r+1} (q̄⁻¹)^{2u+1}`
  have hq0 : (q : ZMod ℓ) ≠ 0 := red_q_ne_zero hℓq
  have hexp : 2 * (i - idx ℓ (kap ℓ) u) + ℓ * (2 * u + 1) = 2 * γ + 1 + ℓ * (2 * r) := by
    have h1 : 2 * idx ℓ (kap ℓ) u + 1 = ℓ * (2 * u + 1) := by
      unfold idx; rw [show ℓ * (2 * u + 1) = ℓ + 2 * (ℓ * u) by ring]; omega
    have h2 : 2 * i + 1 = 2 * γ + 1 + ℓ * (2 * r) := by simp only [i]; unfold idx; ring
    omega
  have hpow : (q : ZMod ℓ) ^ (2 * (i - idx ℓ (kap ℓ) u)) * (q : ZMod ℓ) ^ (2 * u + 1) =
      (q : ZMod ℓ) ^ (2 * γ) * (q : ZMod ℓ) ^ (2 * r + 1) := by
    have := congrArg (fun e => (q : ZMod ℓ) ^ e) hexp
    simp only [pow_add, pow_ell_mul] at this
    rw [show (q : ZMod ℓ) ^ (2 * r + 1) = (q : ZMod ℓ) ^ (2 * r) * (q : ZMod ℓ) by rw [pow_succ]]
    linear_combination this
  have hred2 : red ℓ ((2 * (u : ℚ) + 1) ^ 2) = (2 * (u : ZMod ℓ) + 1) ^ 2 := by
    rw [hcast, red_pow (natCast_mem_Zl _), red_natCast]; push_cast; ring
  have hinvmem := inv_mem_Zl (hunit_u u hu3)
  have hqinv : (1 / (q : ℚ)) ∈ Zl ℓ := by rw [one_div]; exact inv_mem_Zl hqn
  have hLHS : red ℓ ((q : ℚ) ^ (2 * (i - idx ℓ (kap ℓ) u)) * (1 / (2 * (u : ℚ) + 1) ^ 2)) =
      (q : ZMod ℓ) ^ (2 * (i - idx ℓ (kap ℓ) u)) * ((2 * (u : ZMod ℓ) + 1) ^ 2)⁻¹ := by
    rw [one_div, red_mul (pow_mem hqmem _) hinvmem, red_pow hqmem, red_natCast,
      red_inv (hunit_u u hu3), hred2]
  have hRHS : red ℓ ((1 / (q : ℚ)) ^ (2 * u + 1) / (2 * (u : ℚ) + 1) ^ 2) =
      ((q : ZMod ℓ)⁻¹) ^ (2 * u + 1) * ((2 * (u : ZMod ℓ) + 1) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, red_mul (pow_mem hqinv _) hinvmem, red_pow hqinv, one_div, red_inv hqn,
      red_natCast, red_inv (hunit_u u hu3), hred2]
  rw [hsurv u hu3, hLHS, hRHS]
  have hu0 : (q : ZMod ℓ) ^ (2 * u + 1) ≠ 0 := pow_ne_zero _ hq0
  rw [inv_pow]
  have h2u : (2 * (u : ZMod ℓ) + 1) ^ 2 ≠ 0 := by
    intro h0
    have := red_ne_zero_of_norm_one (hunit_u u hu3)
    rw [hred2] at this
    exact this h0
  have hpow' : (q : ZMod ℓ) ^ (2 * (i - idx ℓ (kap ℓ) u)) =
      (q : ZMod ℓ) ^ (2 * γ) * (q : ZMod ℓ) ^ (2 * r + 1) * ((q : ZMod ℓ) ^ (2 * u + 1))⁻¹ := by
    rw [← hpow, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  rw [hpow']
  ring

end Chi2Irr
