/-
# Lemma P for Ti along `K = 3ℓ`: the pole term mod `ℓ`

Copy of `NonVan/PoleTerm.lean` for `SpartT q k = Σ_{j≤k} (−1)^{k−j} q^{2(k−j)}/(2j+1)²`. For `i = γ + ℓr`
(`γ < ℓ`, `r < 3`, `ℓ ≥ 7`, `ℓ ∤ q`):
  `red(ℓ² S♮_i) = (−1)^{κ+γ} q̄^{2γ} (−1)^r q̄^{2r+1} red(T♮_n)`,  `T♮_n = Σ_{u<n} (−1)^u z^{2u+1}/(2u+1)²`, `z = 1/q`,
with `n = r` if `γ < κ` (type S) and `n = r + 1` otherwise (types D, L). This is RESULT §5 (F4),
"ℓ² T♮(2i+1) ≡ χ₄(ℓ) T♮(M_i)": the surviving `j = κ + ℓu` carry the sign `(−1)^{i−j} = (−1)^{κ+γ+r+u}`
(`(−1)^κ = χ₄(ℓ)`). The generic lemmas `dvd_two_mul_add_one_iff`, `pow_ell_mul`, `filter_dvd_eq` are reused.
-/
import Chi2Irrational.TiQ.NonVan.ProgAdic
import Chi2Irrational.NonVan.PoleTerm

namespace Chi2Irr
namespace TiQ

open Polynomial Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `T♮_n(q) = Σ_{u<n} (−1)^u z^{2u+1}/(2u+1)²`, `z = 1/q`. -/
def TqT (q n : ℕ) : ℚ := ∑ u ∈ range n, (-1 : ℚ) ^ u * (1 / (q : ℚ)) ^ (2 * u + 1) / (2 * (u : ℚ) + 1) ^ 2

/-- Signs depend only on parity. -/
lemma neg_one_pow_eq_of_parity {R : Type*} [Monoid R] [HasDistribNeg R] {a b c d : ℕ}
    (h : a + 2 * b = c + 2 * d) : (-1 : R) ^ a = (-1 : R) ^ c := by
  calc (-1 : R) ^ a = (-1 : R) ^ a * ((-1 : R) ^ 2) ^ b := by simp
    _ = (-1 : R) ^ (a + 2 * b) := by rw [pow_add, pow_mul]
    _ = (-1 : R) ^ (c + 2 * d) := by rw [h]
    _ = (-1 : R) ^ c := by rw [pow_add, pow_mul]; simp

lemma red_neg_one_pow (n : ℕ) : red ℓ ((-1 : ℚ) ^ n) = (-1 : ZMod ℓ) ^ n := by
  rw [red_pow (neg_mem (one_mem _)), red_neg (one_mem _), red_one]

lemma neg_one_pow_mem (n : ℕ) : (-1 : ℚ) ^ n ∈ Zl ℓ := pow_mem (neg_mem (one_mem _)) n

theorem red_ell_sq_Spart (hℓ7 : 7 ≤ ℓ) {q : ℕ} (hℓq : ¬ ℓ ∣ q) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    (ℓ : ℚ) ^ 2 * SpartT q (idx ℓ γ r) ∈ Zl ℓ ∧
    red ℓ ((ℓ : ℚ) ^ 2 * SpartT q (idx ℓ γ r)) =
      (-1 : ZMod ℓ) ^ (kap ℓ + γ) * (q : ZMod ℓ) ^ (2 * γ) * ((-1 : ZMod ℓ) ^ r * (q : ZMod ℓ) ^ (2 * r + 1)) *
        red ℓ (TqT q (if γ < kap ℓ then r else r + 1)) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  have hℓpos := hℓ.out.pos
  set i := idx ℓ γ r
  have hi3 : i < 3 * ℓ := idx_lt hγ hr
  have hqn : padicNorm ℓ (q : ℚ) = 1 := padicNorm_natCast_q hℓq
  have hqmem : (q : ℚ) ∈ Zl ℓ := natCast_mem_Zl q
  -- the terms
  set f : ℕ → ℚ := fun j => (-1 : ℚ) ^ (i - j) * (q : ℚ) ^ (2 * (i - j)) * ((ℓ : ℚ) ^ 2 / (2 * (j : ℚ) + 1) ^ 2)
  have hsum : (ℓ : ℚ) ^ 2 * SpartT q i = ∑ j ∈ range (i + 1), f j := by
    unfold SpartT; rw [mul_sum]
    refine sum_congr rfl (fun j _ => by simp only [f]; ring)
  -- `2j + 1` as a natural number
  have hcast : ∀ j : ℕ, (2 * (j : ℚ) + 1) = ((2 * j + 1 : ℕ) : ℚ) := fun j => by push_cast; ring
  have hsgn : ∀ n : ℕ, padicNorm ℓ ((-1 : ℚ) ^ n) = 1 := fun n => by
    rw [padicNorm_pow, padicNorm.neg, padicNorm.one, one_pow]
  -- non-surviving terms are `ℓ`-small, surviving ones integral
  have hsmall : ∀ j, ¬ ℓ ∣ 2 * j + 1 → padicNorm ℓ (f j) ≤ (ℓ : ℚ)⁻¹ := by
    intro j hj
    simp only [f]
    rw [padicNorm.mul, padicNorm.mul, hsgn, one_mul, padicNorm_pow, hqn, one_pow, one_mul, padicNorm.div,
      padicNorm_ell_pow, hcast, padicNorm_pow, padicNorm_natCast_eq_one hj, one_pow, div_one]
    calc ((ℓ : ℚ)⁻¹) ^ 2 ≤ ((ℓ : ℚ)⁻¹) ^ 1 := inv_pow_anti (by norm_num)
      _ = _ := pow_one _
  -- surviving terms: `j = κ + ℓu`, `2j + 1 = ℓ(2u + 1)`
  have hsurv : ∀ u < 3, f (idx ℓ (kap ℓ) u) =
      (-1 : ℚ) ^ (i - idx ℓ (kap ℓ) u) * (q : ℚ) ^ (2 * (i - idx ℓ (kap ℓ) u)) *
        (1 / (2 * (u : ℚ) + 1) ^ 2) := by
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
      refine mul_mem (mul_mem (neg_one_pow_mem _) (pow_mem hqmem _)) ?_
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
  unfold TqT
  have hTmem : ∀ u ∈ range (if γ < kap ℓ then r else r + 1),
      (-1 : ℚ) ^ u * (1 / (q : ℚ)) ^ (2 * u + 1) / (2 * (u : ℚ) + 1) ^ 2 ∈ Zl ℓ := by
    intro u hu
    have hu3 : u < 3 := by split_ifs at hu <;> rw [mem_range] at hu <;> omega
    rw [div_eq_mul_inv]
    refine mul_mem (mul_mem (neg_one_pow_mem _) (pow_mem ?_ _)) (inv_mem_Zl (hunit_u u hu3))
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
  -- the sign: `(−1)^{i−j} = (−1)^{κ+γ+r+u}`
  have hsign : (-1 : ZMod ℓ) ^ (i - idx ℓ (kap ℓ) u) = (-1 : ZMod ℓ) ^ (kap ℓ + γ + r + u) := by
    refine neg_one_pow_eq_of_parity (b := idx ℓ (kap ℓ) u) (d := kap ℓ * r + kap ℓ * u) ?_
    have hℓr : ℓ * r = 2 * (kap ℓ * r) + r := by
      rw [show ℓ * r = (2 * kap ℓ + 1) * r by rw [hk]]; ring
    have hℓu : ℓ * u = 2 * (kap ℓ * u) + u := by
      rw [show ℓ * u = (2 * kap ℓ + 1) * u by rw [hk]]; ring
    have hi' : i = γ + ℓ * r := rfl
    have hj' : idx ℓ (kap ℓ) u = kap ℓ + ℓ * u := rfl
    omega
  have hred2 : red ℓ ((2 * (u : ℚ) + 1) ^ 2) = (2 * (u : ZMod ℓ) + 1) ^ 2 := by
    rw [hcast, red_pow (natCast_mem_Zl _), red_natCast]; push_cast; ring
  have hinvmem := inv_mem_Zl (hunit_u u hu3)
  have hqinv : (1 / (q : ℚ)) ∈ Zl ℓ := by rw [one_div]; exact inv_mem_Zl hqn
  have hLHS : red ℓ ((-1 : ℚ) ^ (i - idx ℓ (kap ℓ) u) * (q : ℚ) ^ (2 * (i - idx ℓ (kap ℓ) u)) *
      (1 / (2 * (u : ℚ) + 1) ^ 2)) =
      (-1 : ZMod ℓ) ^ (i - idx ℓ (kap ℓ) u) * (q : ZMod ℓ) ^ (2 * (i - idx ℓ (kap ℓ) u)) *
        ((2 * (u : ZMod ℓ) + 1) ^ 2)⁻¹ := by
    rw [one_div, red_mul (mul_mem (neg_one_pow_mem _) (pow_mem hqmem _)) hinvmem,
      red_mul (neg_one_pow_mem _) (pow_mem hqmem _), red_neg_one_pow, red_pow hqmem, red_natCast,
      red_inv (hunit_u u hu3), hred2]
  have hRHS : red ℓ ((-1 : ℚ) ^ u * (1 / (q : ℚ)) ^ (2 * u + 1) / (2 * (u : ℚ) + 1) ^ 2) =
      (-1 : ZMod ℓ) ^ u * ((q : ZMod ℓ)⁻¹) ^ (2 * u + 1) * ((2 * (u : ZMod ℓ) + 1) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, red_mul (mul_mem (neg_one_pow_mem _) (pow_mem hqinv _)) hinvmem,
      red_mul (neg_one_pow_mem _) (pow_mem hqinv _), red_neg_one_pow, red_pow hqinv, one_div, red_inv hqn,
      red_natCast, red_inv (hunit_u u hu3), hred2]
  rw [hsurv u hu3, hLHS, hRHS]
  have hu0 : (q : ZMod ℓ) ^ (2 * u + 1) ≠ 0 := pow_ne_zero _ hq0
  rw [inv_pow]
  have hpow' : (q : ZMod ℓ) ^ (2 * (i - idx ℓ (kap ℓ) u)) =
      (q : ZMod ℓ) ^ (2 * γ) * (q : ZMod ℓ) ^ (2 * r + 1) * ((q : ZMod ℓ) ^ (2 * u + 1))⁻¹ := by
    rw [← hpow, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  rw [hpow', hsign, pow_add, pow_add, pow_add]
  ring

end TiQ
end Chi2Irr
