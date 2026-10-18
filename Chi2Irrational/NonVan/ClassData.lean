/-
# Lemma P along `K = 3ℓ`: class data

Indices `idx γ r = γ + ℓ r` (`γ < ℓ`, `r < 3`); a class `{idx γ r, idx γ s, idx γ c}` with `{r, s, c} = {0, 1, 2}`.
* `closeSet ℓ γ`: the roots close to `t` on the progression of `γ` (the class of `γ`, plus `3ℓ` if `γ = κ`), its
  cardinality and the closeness of its members;
* `dPrime_split`: `D′(x_i) = (x_i − x_j)(x_i − x_c) ∏_{rest} (x_i − x_m)` with `‖∏_{rest}‖ = 1`;
  `x_{idx γ r} − x_{idx γ s} = ℓ (s − r)`; `‖D′(x_i)‖ = ℓ^{−2}`;
* `DD x h = (h − h(x))/(X − x)` (divided difference): product rule and the quadratic/cubic cases.
-/
import Chi2Irrational.NonVan.Setup
import Chi2Irrational.NonVan.ProgAdic

namespace Chi2Irr

open Polynomial Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma pole_eq (m : ℕ) : pole m = -(((2 * m + 1 : ℕ) : ℚ) / 2) := by
  unfold pole; push_cast; ring

lemma pole_mem_Zl (hℓ2 : ℓ ≠ 2) (m : ℕ) : pole m ∈ Zl ℓ := by
  rw [pole_eq, mem_Zl, padicNorm.neg, padicNorm.div, padicNorm_two hℓ2, div_one]
  exact padicNorm.of_nat _

lemma rt_mem_Zl (hℓ2 : ℓ ≠ 2) (K m : ℕ) : rt K m ∈ Zl ℓ := by
  unfold rt; split_ifs
  · exact pole_mem_Zl hℓ2 m
  · exact zero_mem _

lemma pole_sub_pole (a b : ℕ) : pole a - pole b = (b : ℚ) - a := by unfold pole; ring

/-- `ℓ ∤ m − i` (as integers) when `m`, `i` lie in different classes. -/
lemma padicNorm_pole_sub_of_mod_ne {a b : ℕ} (h : a % ℓ ≠ b % ℓ) : padicNorm ℓ (pole a - pole b) = 1 := by
  rw [pole_sub_pole]
  have : ((b : ℚ) - a) = (((b : ℤ) - a : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  refine padicNorm_intCast_eq_one ?_
  rw [← Nat.modEq_iff_dvd]
  exact fun e => h e

/-! ### Indices and classes -/

/-- `idx ℓ γ r = γ + ℓ r`. -/
def idx (ℓ γ r : ℕ) : ℕ := γ + ℓ * r

lemma idx_lt {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) : idx ℓ γ r < 3 * ℓ := by
  unfold idx; interval_cases r <;> omega

lemma idx_mod {γ r : ℕ} (hγ : γ < ℓ) : idx ℓ γ r % ℓ = γ := by
  unfold idx; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hγ]

lemma idx_injective {γ r s : ℕ} (h : idx ℓ γ r = idx ℓ γ s) : r = s := by
  unfold idx at h
  exact Nat.eq_of_mul_eq_mul_left hℓ.out.pos (by omega)

lemma idx_ne {γ r s : ℕ} (h : r ≠ s) : idx ℓ γ r ≠ idx ℓ γ s := fun e => h (idx_injective e)

lemma pole_idx_sub (γ r s : ℕ) : pole (idx ℓ γ r) - pole (idx ℓ γ s) = (ℓ : ℚ) * ((s : ℚ) - r) := by
  rw [pole_sub_pole]; unfold idx; push_cast; ring

/-- A permutation `(r, s, c)` of `(0, 1, 2)`. -/
structure Perm3 (r s c : ℕ) : Prop where
  hr : r < 3
  hs : s < 3
  hc : c < 3
  rs : r ≠ s
  rc : r ≠ c
  sc : s ≠ c

lemma Perm3.sum {r s c : ℕ} (p : Perm3 r s c) : r + s + c = 3 := by
  have := p.hr; have := p.hs; have := p.hc; have := p.rs; have := p.rc; have := p.sc; omega

/-- Every member of the class is one of `idx γ r`, `idx γ s`, `idx γ c`. -/
lemma mem_class_of_perm {γ r s c m : ℕ} (hγ : γ < ℓ) (p : Perm3 r s c) (hm : m < 3 * ℓ)
    (hmod : m % ℓ = γ) : m = idx ℓ γ r ∨ m = idx ℓ γ s ∨ m = idx ℓ γ c := by
  have h := (mod_eq_iff_mem_cls hγ hm).mp hmod
  have := p.hr; have := p.hs; have := p.hc; have := p.rs; have := p.rc; have := p.sc
  unfold idx
  interval_cases r <;> interval_cases s <;> interval_cases c <;> omega

/-- The rest of `[0, 3ℓ)` after removing a class. -/
def restSet (ℓ γ r s c : ℕ) : Finset ℕ :=
  (((range (3 * ℓ)).erase (idx ℓ γ r)).erase (idx ℓ γ s)).erase (idx ℓ γ c)

lemma mod_ne_of_mem_restSet {γ r s c m : ℕ} (hγ : γ < ℓ) (p : Perm3 r s c)
    (hm : m ∈ restSet ℓ γ r s c) : m % ℓ ≠ γ := by
  unfold restSet at hm
  simp only [mem_erase, mem_range] at hm
  intro hmod
  rcases mem_class_of_perm hγ p hm.2.2.2 hmod with h | h | h
  · exact hm.2.2.1 h
  · exact hm.2.1 h
  · exact hm.1 h

lemma restSet_subset (ℓ γ r s c : ℕ) : restSet ℓ γ r s c ⊆ range (3 * ℓ) :=
  fun m hm => mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase hm))

lemma padicNorm_restProd {γ r s c : ℕ} (hγ : γ < ℓ) (p : Perm3 r s c) :
    padicNorm ℓ (∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)) = 1 := by
  rw [padicNorm_prod]
  refine prod_eq_one (fun m hm => padicNorm_pole_sub_of_mod_ne ?_)
  rw [idx_mod hγ]
  exact (mod_ne_of_mem_restSet hγ p hm).symm

lemma restProd_ne_zero {γ r s c : ℕ} (hγ : γ < ℓ) (p : Perm3 r s c) :
    ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m) ≠ 0 := by
  intro h
  have := padicNorm_restProd (ℓ := ℓ) hγ p
  rw [h, padicNorm.zero] at this
  exact zero_ne_one this

/-- `D′(x_i) = (x_i − x_j)(x_i − x_c) ∏_{rest} (x_i − x_m)`. -/
lemma dPrime_split {γ r s c : ℕ} (hγ : γ < ℓ) (p : Perm3 r s c) :
    dPrime (3 * ℓ) (idx ℓ γ r) = (pole (idx ℓ γ r) - pole (idx ℓ γ s)) *
      (pole (idx ℓ γ r) - pole (idx ℓ γ c)) *
      ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m) := by
  unfold dPrime restSet
  have hj : idx ℓ γ s ∈ (range (3 * ℓ)).erase (idx ℓ γ r) :=
    mem_erase.mpr ⟨idx_ne p.rs.symm, mem_range.mpr (idx_lt hγ p.hs)⟩
  have hc : idx ℓ γ c ∈ ((range (3 * ℓ)).erase (idx ℓ γ r)).erase (idx ℓ γ s) :=
    mem_erase.mpr ⟨idx_ne p.sc.symm, mem_erase.mpr ⟨idx_ne p.rc.symm, mem_range.mpr (idx_lt hγ p.hc)⟩⟩
  rw [← mul_prod_erase _ (fun m => pole (idx ℓ γ r) - pole m) hj,
    ← mul_prod_erase _ (fun m => pole (idx ℓ γ r) - pole m) hc]
  ring

/-- `c′_r = (s − r)(c − r)`, so that `ℓ²/D′(x_i) = 1/(c′_r ∏_{rest})`. -/
def cpr (r s c : ℕ) : ℚ := ((s : ℚ) - r) * ((c : ℚ) - r)

lemma cpr_values {r s c : ℕ} (p : Perm3 r s c) :
    cpr r s c = if r = 1 then -1 else 2 := by
  have := p.hr; have := p.hs; have := p.hc; have := p.rs; have := p.rc; have := p.sc
  unfold cpr
  interval_cases r <;> interval_cases s <;> interval_cases c <;> norm_num at *

lemma padicNorm_cpr (hℓ2 : ℓ ≠ 2) {r s c : ℕ} (p : Perm3 r s c) : padicNorm ℓ (cpr r s c) = 1 := by
  rw [cpr_values p]
  split_ifs
  · rw [padicNorm.neg, padicNorm.one]
  · exact padicNorm_two hℓ2

lemma cpr_ne_zero (hℓ2 : ℓ ≠ 2) {r s c : ℕ} (p : Perm3 r s c) : cpr r s c ≠ 0 := by
  intro h; have := padicNorm_cpr hℓ2 p; rw [h, padicNorm.zero] at this; exact zero_ne_one this

lemma dPrime_eq {γ r s c : ℕ} (hγ : γ < ℓ) (p : Perm3 r s c) :
    dPrime (3 * ℓ) (idx ℓ γ r) = (ℓ : ℚ) ^ 2 * cpr r s c *
      ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m) := by
  rw [dPrime_split hγ p, pole_idx_sub, pole_idx_sub]
  unfold cpr; ring

lemma padicNorm_dPrime (hℓ2 : ℓ ≠ 2) {γ r s c : ℕ} (hγ : γ < ℓ) (p : Perm3 r s c) :
    padicNorm ℓ (dPrime (3 * ℓ) (idx ℓ γ r)) = ((ℓ : ℚ)⁻¹) ^ 2 := by
  rw [dPrime_eq hγ p, padicNorm.mul, padicNorm.mul, padicNorm_ell_pow, padicNorm_cpr hℓ2 p,
    padicNorm_restProd hγ p]
  ring

lemma dPrime_idx_ne_zero {γ r : ℕ} : dPrime (3 * ℓ) (idx ℓ γ r) ≠ 0 := dPrime_ne_zero _ _

/-! ### The close set -/

open Classical in
/-- The roots close to `t` on the progression of `γ`. -/
noncomputable def closeSet (ℓ γ : ℕ) : Finset ℕ :=
  (range (3 * ℓ)).filter (fun m => m % ℓ = γ) ∪ (if γ = kap ℓ then {3 * ℓ} else ∅)

lemma mem_closeSet {γ m : ℕ} :
    m ∈ closeSet ℓ γ ↔ (m < 3 * ℓ ∧ m % ℓ = γ) ∨ (γ = kap ℓ ∧ m = 3 * ℓ) := by
  unfold closeSet
  rw [mem_union, mem_filter, mem_range]
  split_ifs with h <;> simp [h]

lemma closeSet_subset (γ : ℕ) : closeSet ℓ γ ⊆ range (3 * ℓ + 1) := by
  intro m hm
  rw [mem_closeSet] at hm
  rw [mem_range]
  rcases hm with h | h <;> omega

lemma close_of_mem_closeSet (hℓ2 : ℓ ≠ 2) {γ t m : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1)
    (hm : m ∈ closeSet ℓ γ) : padicNorm ℓ ((t : ℚ) - rt (3 * ℓ) m) ≤ (ℓ : ℚ)⁻¹ := by
  rw [mem_closeSet] at hm
  rcases hm with ⟨hm, hmod⟩ | ⟨hk, rfl⟩
  · exact padicNorm_sub_rt_close hℓ2 hm ((dvd_iff_mod_eq hℓ2 hγ ht m).mpr hmod)
  · exact padicNorm_sub_rt_self_close ((dvd_t_iff hℓ2 hγ ht).mpr hk)

lemma mem_closeSet_of_lt {γ m : ℕ} (hm : m < 3 * ℓ) : m ∈ closeSet ℓ γ ↔ m % ℓ = γ := by
  rw [mem_closeSet]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h
    · omega
  · intro h; exact Or.inl ⟨hm, h⟩

lemma filter_class_eq {γ : ℕ} (hγ : γ < ℓ) :
    (range (3 * ℓ)).filter (fun m => m % ℓ = γ) = {idx ℓ γ 0, idx ℓ γ 1, idx ℓ γ 2} := by
  ext m
  rw [mem_filter, mem_range, mem_insert, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hm, hmod⟩
    have := (mod_eq_iff_mem_cls hγ hm).mp hmod
    unfold idx; omega
  · intro h
    have hm : m < 3 * ℓ := by
      rcases h with h | h | h <;> rw [h] <;> exact idx_lt hγ (by norm_num)
    refine ⟨hm, ?_⟩
    rcases h with h | h | h <;> rw [h] <;> exact idx_mod hγ

lemma card_filter_class {γ : ℕ} (hγ : γ < ℓ) :
    ((range (3 * ℓ)).filter (fun m => m % ℓ = γ)).card = 3 := by
  rw [filter_class_eq hγ, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · rw [mem_singleton]; exact idx_ne (by norm_num)
  · rw [mem_insert, mem_singleton, not_or]; exact ⟨idx_ne (by norm_num), idx_ne (by norm_num)⟩

lemma card_closeSet {γ : ℕ} (hγ : γ < ℓ) :
    (closeSet ℓ γ).card = 3 + (if γ = kap ℓ then 1 else 0) := by
  unfold closeSet
  rw [card_union_of_disjoint, card_filter_class hγ]
  · split_ifs <;> simp
  · rw [disjoint_left]
    intro m hm hm'
    rw [mem_filter, mem_range] at hm
    split_ifs at hm' with h
    · rw [mem_singleton] at hm'; omega
    · simp at hm'

/-! ### Divided differences -/

/-- `DD x h = (h − h(x)) / (X − x)`. -/
noncomputable def DD (x : ℚ) (h : ℚ[X]) : ℚ[X] := (h - C (h.eval x)) /ₘ (X - C x)

lemma X_sub_C_mul_DD (x : ℚ) (h : ℚ[X]) : (X - C x) * DD x h = h - C (h.eval x) := by
  unfold DD
  rw [mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot])]

lemma DD_eq_of_mul {x : ℚ} {h D : ℚ[X]} (H : (X - C x) * D = h - C (h.eval x)) : DD x h = D := by
  have := X_sub_C_mul_DD x h
  rw [← H] at this
  exact mul_left_cancel₀ (X_sub_C_ne_zero x) this

lemma DD_mul (x : ℚ) (P R : ℚ[X]) : DD x (P * R) = DD x P * R + C (P.eval x) * DD x R := by
  apply DD_eq_of_mul
  have hP := X_sub_C_mul_DD x P
  have hR := X_sub_C_mul_DD x R
  rw [eval_mul, C_mul]
  linear_combination R * hP + C (P.eval x) * hR

lemma DD_quad (x α β : ℚ) :
    DD x ((X - C α) * (X - C β)) = X + C (x - α - β) := by
  apply DD_eq_of_mul
  simp only [eval_mul, eval_sub, eval_X, eval_C, map_sub, map_mul]
  ring

lemma DD_cubic (x α β : ℚ) :
    DD x (X * ((X - C α) * (X - C β))) =
      X ^ 2 + C (x - α - β) * X + C (x ^ 2 - (α + β) * x + α * β) := by
  apply DD_eq_of_mul
  simp only [eval_mul, eval_sub, eval_X, eval_C, map_sub, map_mul, map_add, map_pow]
  ring

lemma Qpoly_eq_DD (K i : ℕ) : Qpoly K i = DD (pole i) (gpoly K i) := rfl

end Chi2Irr
