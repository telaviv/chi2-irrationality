/-
# Lemma P along `K = 3ℓ`: residues on the own progression

Class `γ`, `(r, s, c)` a permutation of `(0, 1, 2)`, `i = γ + ℓr`, `j = γ + ℓs`, third atom `γ + ℓc`, and `t` on the
progression of `γ`. With `c′_r = (s − r)(c − r)` (`cpr`):
* S/L (`γ ≠ κ`): `red(ν_ij F_ij′(t)) = red(ν_ii Q_i′(t)) = red(x_i / c′_r)`;
* D (`γ = κ`): `red(ν_ij F_ij′(t)) = red(((2t − x_c)/ℓ)/c′_r)`,
  `red(ν_ii Q_i′(t)) = red(((2t + x_i − x_j − x_c)/ℓ)/c′_r)`.
All four quantities are ℓ-integral.
-/
import Chi2Irrational.NonVan.EntryBounds

namespace Chi2Irr

open Polynomial Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

section
variable {γ r s c : ℕ}

lemma erase3_eq_insert (hγ : γ < ℓ) (p : Perm3 r s c) :
    (((range (3 * ℓ + 1)).erase (idx ℓ γ r)).erase (idx ℓ γ s)).erase (idx ℓ γ c) =
      insert (3 * ℓ) (restSet ℓ γ r s c) := by
  unfold restSet
  rw [range_add_one, erase_insert_of_ne (Nat.ne_of_gt (idx_lt hγ p.hr)),
    erase_insert_of_ne (Nat.ne_of_gt (idx_lt hγ p.hs)), erase_insert_of_ne (Nat.ne_of_gt (idx_lt hγ p.hc))]

lemma notMem_restSet_self (ℓ γ r s c : ℕ) : 3 * ℓ ∉ restSet ℓ γ r s c :=
  fun h => lt_irrefl _ (mem_range.mp (restSet_subset ℓ γ r s c h))

lemma prod_insert_rt (z : ℚ) (hγ : γ < ℓ) (p : Perm3 r s c) :
    ∏ m ∈ insert (3 * ℓ) (restSet ℓ γ r s c), (z - rt (3 * ℓ) m) =
      z * ∏ m ∈ restSet ℓ γ r s c, (z - pole m) := by
  rw [prod_insert (notMem_restSet_self ℓ γ r s c), rt_self, sub_zero]
  congr 1
  exact prod_congr rfl (fun m hm => by rw [rt_of_lt (mem_range.mp (restSet_subset ℓ γ r s c hm))])

lemma prod_insert_rt_X (hγ : γ < ℓ) (p : Perm3 r s c) :
    ∏ m ∈ insert (3 * ℓ) (restSet ℓ γ r s c), (X - C (rt (3 * ℓ) m)) =
      X * ∏ m ∈ restSet ℓ γ r s c, (X - C (pole m)) := by
  rw [prod_insert (notMem_restSet_self ℓ γ r s c), rt_self, map_zero, sub_zero]
  congr 1
  exact prod_congr rfl (fun m hm => by rw [rt_of_lt (mem_range.mp (restSet_subset ℓ γ r s c hm))])

variable (hℓ2 : ℓ ≠ 2) (hγ : γ < ℓ) (p : Perm3 r s c) {t : ℕ} (ht : ℓ ∣ 2 * t + 2 * γ + 1)
include hℓ2 hγ p ht

lemma close_member {a : ℕ} (ha : a < 3) : padicNorm ℓ ((t : ℚ) - pole (idx ℓ γ a)) ≤ (ℓ : ℚ)⁻¹ := by
  have h := close_of_mem_closeSet hℓ2 hγ ht
    ((mem_closeSet_of_lt (idx_lt hγ ha)).mpr (idx_mod (r := a) hγ))
  rwa [rt_of_lt (idx_lt hγ ha)] at h

lemma red_t_eq : red ℓ (t : ℚ) = red ℓ (pole (idx ℓ γ r)) := by
  refine red_eq_of_sub (natCast_mem_Zl t) (pole_mem_Zl hℓ2 _) ?_
  exact lt_of_le_of_lt (close_member hℓ2 hγ p ht p.hr) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt))

lemma red_restProd_t :
    red ℓ (∏ m ∈ restSet ℓ γ r s c, ((t : ℚ) - pole m)) =
      red ℓ (∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)) := by
  rw [red_prod _ _ (fun m _ => sub_mem (natCast_mem_Zl t) (pole_mem_Zl hℓ2 m)),
    red_prod _ _ (fun m _ => sub_mem (pole_mem_Zl hℓ2 _) (pole_mem_Zl hℓ2 m))]
  refine prod_congr rfl (fun m _ => ?_)
  rw [red_sub (natCast_mem_Zl t) (pole_mem_Zl hℓ2 m),
    red_sub (pole_mem_Zl hℓ2 _) (pole_mem_Zl hℓ2 m), red_t_eq hℓ2 hγ p ht]

lemma restProd_t_mem : ∏ m ∈ restSet ℓ γ r s c, ((t : ℚ) - pole m) ∈ Zl ℓ :=
  prod_mem (fun m _ => sub_mem (natCast_mem_Zl t) (pole_mem_Zl hℓ2 m))

/-- The common core: `red(A · ∏_rest(t − x_m) / (c′_r ∏_rest(x_i − x_m))) = red(A)/red(c′_r)`. -/
lemma red_core {A : ℚ} (hA : A ∈ Zl ℓ) :
    red ℓ (A * (∏ m ∈ restSet ℓ γ r s c, ((t : ℚ) - pole m)) /
      (cpr r s c * ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m))) =
      red ℓ (A / cpr r s c) := by
  have hB := padicNorm_restProd (ℓ := ℓ) hγ p
  have hcB : padicNorm ℓ (cpr r s c * ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)) = 1 := by
    rw [padicNorm.mul, padicNorm_cpr hℓ2 p, hB, one_mul]
  have hBmem : ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m) ∈ Zl ℓ := le_of_eq hB
  have hBne : red ℓ (∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)) ≠ 0 :=
    red_ne_zero_of_norm_one hB
  rw [red_div (mul_mem hA (restProd_t_mem hℓ2 hγ p ht)) hcB, red_div hA (padicNorm_cpr hℓ2 p),
    red_mul hA (restProd_t_mem hℓ2 hγ p ht), red_mul (le_of_eq (padicNorm_cpr hℓ2 p)) hBmem,
    red_restProd_t hℓ2 hγ p ht]
  field_simp

lemma nu_eq_SL (hk : γ ≠ kap ℓ) (b : ℕ) (hb : b < 3) :
    nu ℓ (idx ℓ γ r) (idx ℓ γ b) =
      1 / (cpr r s c * ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)) := by
  unfold nu
  rw [ite_eq_right (by rw [idx_mod hγ]; exact hk), dPrime_eq hγ p]
  have := ell_pos (ℓ := ℓ)
  have := cpr_ne_zero hℓ2 p
  have := restProd_ne_zero (ℓ := ℓ) hγ p
  field_simp

lemma nu_eq_D (hk : γ = kap ℓ) (b : ℕ) (hb : b < 3) :
    nu ℓ (idx ℓ γ r) (idx ℓ γ b) =
      1 / ((ℓ : ℚ) * (cpr r s c * ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m))) := by
  unfold nu
  rw [ite_eq_left (by rw [idx_mod hγ]; exact hk), dPrime_eq hγ p]
  have := ell_pos (ℓ := ℓ)
  have := cpr_ne_zero hℓ2 p
  have := restProd_ne_zero (ℓ := ℓ) hγ p
  field_simp

end

lemma derivative_DD_quad_mul (x α β : ℚ) (R : ℚ[X]) :
    derivative (DD x (((X - C α) * (X - C β)) * R)) =
      R + (X + C (x - α - β)) * derivative R +
        C (((X - C α) * (X - C β)).eval x) * derivative (DD x R) := by
  rw [DD_mul, DD_quad]
  simp only [derivative_add, derivative_mul, derivative_X, derivative_C, zero_mul, zero_add,
    one_mul, add_zero]

lemma derivative_DD_cubic_mul (x α β : ℚ) (R : ℚ[X]) :
    derivative (DD x ((X * ((X - C α) * (X - C β))) * R)) =
      (2 * X + C (x - α - β)) * R +
        (X ^ 2 + C (x - α - β) * X + C (x ^ 2 - (α + β) * x + α * β)) * derivative R +
        C (x * ((x - α) * (x - β))) * derivative (DD x R) := by
  rw [DD_mul, DD_cubic]
  simp only [eval_mul, eval_sub, eval_X, eval_C, derivative_add, derivative_mul, derivative_X,
    derivative_C, derivative_X_pow, zero_mul, zero_add, one_mul, add_zero, mul_one]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  have h2 : (C (2 : ℚ) : ℚ[X]) = 2 := by rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, map_natCast]; norm_num
  try rw [h2]
  try simp only [Nat.cast_ofNat, h2]
  ring

/-! ### Small-norm arithmetic -/

lemma pn_add_le {a b e : ℚ} (ha : padicNorm ℓ a ≤ e) (hb : padicNorm ℓ b ≤ e) : padicNorm ℓ (a + b) ≤ e :=
  padicNorm.nonarchimedean.trans (max_le ha hb)

lemma pn_sub_le {a b e : ℚ} (ha : padicNorm ℓ a ≤ e) (hb : padicNorm ℓ b ≤ e) : padicNorm ℓ (a - b) ≤ e :=
  padicNorm.sub.trans (max_le ha hb)

lemma pn_mul_le {a b e₁ e₂ : ℚ} (ha : padicNorm ℓ a ≤ e₁) (hb : padicNorm ℓ b ≤ e₂) (h₁ : 0 ≤ e₁) :
    padicNorm ℓ (a * b) ≤ e₁ * e₂ := by
  rw [padicNorm.mul]
  exact mul_le_mul ha hb (padicNorm.nonneg _) h₁

lemma pn_mul_le_left {a b e : ℚ} (ha : padicNorm ℓ a ≤ 1) (hb : padicNorm ℓ b ≤ e) :
    padicNorm ℓ (a * b) ≤ e := by
  have h0 : 0 ≤ e := (padicNorm.nonneg b).trans hb
  simpa using pn_mul_le ha hb zero_le_one

lemma pole_idx_kap (hℓ2 : ℓ ≠ 2) (a : ℕ) :
    pole (idx ℓ (kap ℓ) a) = -((ℓ : ℚ) * ((a : ℚ) + 1 / 2)) := by
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  have hkq : (2 * (kap ℓ : ℚ) + 1) = ℓ := by exact_mod_cast hk
  unfold pole idx; push_cast
  linear_combination (-1 / 2 : ℚ) * hkq

lemma half_add_mem (hℓ2 : ℓ ≠ 2) (n : ℕ) : ((n : ℚ) + 1 / 2) ∈ Zl ℓ := by
  have : ((n : ℚ) + 1 / 2) = ((2 * n + 1 : ℕ) : ℚ) / 2 := by push_cast; ring
  rw [this, mem_Zl, padicNorm.div, padicNorm_two hℓ2, div_one]
  exact padicNorm.of_nat _

lemma padicNorm_pole_idx_kap (hℓ2 : ℓ ≠ 2) (a : ℕ) :
    padicNorm ℓ (pole (idx ℓ (kap ℓ) a)) ≤ (ℓ : ℚ)⁻¹ := by
  rw [pole_idx_kap hℓ2, padicNorm.neg]
  exact (pn_mul_le (le_of_eq padicNorm_self) (half_add_mem hℓ2 a) ell_inv_pos.le).trans (by simp)

section
variable {γ r s c : ℕ}
variable (hℓ2 : ℓ ≠ 2) (hγ : γ < ℓ) (p : Perm3 r s c) {t : ℕ} (ht : ℓ ∣ 2 * t + 2 * γ + 1)
include hℓ2 hγ p ht

lemma t_small (hk : γ = kap ℓ) : padicNorm ℓ (t : ℚ) ≤ (ℓ : ℚ)⁻¹ :=
  padicNorm_le_inv_of_lt_one ((padicNorm.nat_lt_one_iff t).mpr ((dvd_t_iff hℓ2 hγ ht).mpr hk))

lemma t_eq_ell_mul (hk : γ = kap ℓ) : (t : ℚ) = (ℓ : ℚ) * ((t / ℓ : ℕ) : ℚ) := by
  have hd : ℓ ∣ t := (dvd_t_iff hℓ2 hγ ht).mpr hk
  exact_mod_cast (Nat.mul_div_cancel' hd).symm

/-- The set of roots of `F_ij` and its erasures. -/
lemma Tset_facts :
    let T := ((range (3 * ℓ + 1)).erase (idx ℓ γ r)).erase (idx ℓ γ s)
    idx ℓ γ c ∈ T ∧ 3 * ℓ ∈ T ∧ T.erase (idx ℓ γ c) = insert (3 * ℓ) (restSet ℓ γ r s c) ∧
      (T.erase (3 * ℓ)).erase (idx ℓ γ c) = restSet ℓ γ r s c := by
  intro T
  have hcT : idx ℓ γ c ∈ T := mem_erase.mpr ⟨idx_ne p.sc.symm, mem_erase.mpr ⟨idx_ne p.rc.symm,
    mem_range.mpr (by have := idx_lt hγ p.hc; omega)⟩⟩
  have hKT : 3 * ℓ ∈ T := mem_erase.mpr ⟨Nat.ne_of_gt (idx_lt hγ p.hs), mem_erase.mpr
    ⟨Nat.ne_of_gt (idx_lt hγ p.hr), mem_range.mpr (by omega)⟩⟩
  have h3 : T.erase (idx ℓ γ c) = insert (3 * ℓ) (restSet ℓ γ r s c) := erase3_eq_insert hγ p
  refine ⟨hcT, hKT, h3, ?_⟩
  rw [erase_right_comm, h3, erase_insert (notMem_restSet_self ℓ γ r s c)]

/-- **Residue, off-diagonal, types S and L.** -/
theorem resid_off_SL (hk : γ ≠ kap ℓ) :
    nu ℓ (idx ℓ γ r) (idx ℓ γ s) * (derivative (Fpoly (3 * ℓ) (idx ℓ γ r) (idx ℓ γ s))).eval (t : ℚ) ∈ Zl ℓ ∧
    red ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ s) *
      (derivative (Fpoly (3 * ℓ) (idx ℓ γ r) (idx ℓ γ s))).eval (t : ℚ)) =
      red ℓ (pole (idx ℓ γ r) / cpr r s c) := by
  have hi := idx_lt hγ p.hr
  have hj := idx_lt hγ p.hs
  have hmem := nuF_le_one hℓ2 hi hj (idx_ne p.rs) t
  refine ⟨hmem, ?_⟩
  obtain ⟨hcT, -, h3, -⟩ := Tset_facts hℓ2 hγ p ht
  have hdiff := padicNorm_deriv_sub_le (singleton_subset_iff.mpr hcT) (rt (3 * ℓ)) (t : ℚ)
    (fun m _ => padicNorm_sub_rt_le_one hℓ2 _ _ _)
    (fun m hm => by rw [mem_singleton.mp hm, rt_of_lt (idx_lt hγ p.hc)]; exact close_member hℓ2 hγ p ht p.hc)
  rw [sum_singleton, h3, prod_insert_rt _ hγ p, card_singleton, pow_one, ← Fpoly_eq_prod hi hj] at hdiff
  set A := ∏ m ∈ restSet ℓ γ r s c, ((t : ℚ) - pole m)
  set B := ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)
  have hnu := nu_eq_SL hℓ2 hγ p ht hk s p.hs
  have hnu1 : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ s)) = 1 := by
    rw [padicNorm_nu hℓ2 hi, ite_eq_right (by rw [idx_mod hγ]; exact hk)]
  have hmain_mem : nu ℓ (idx ℓ γ r) (idx ℓ γ s) * ((t : ℚ) * A) ∈ Zl ℓ :=
    mul_mem (le_of_eq hnu1) (mul_mem (natCast_mem_Zl t) (restProd_t_mem hℓ2 hγ p ht))
  have hclose : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ s) *
      (derivative (Fpoly (3 * ℓ) (idx ℓ γ r) (idx ℓ γ s))).eval (t : ℚ) -
      nu ℓ (idx ℓ γ r) (idx ℓ γ s) * ((t : ℚ) * A)) < 1 := by
    rw [← mul_sub, padicNorm.mul, hnu1, one_mul]
    exact lt_of_le_of_lt hdiff (inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt))
  rw [red_eq_of_sub hmem hmain_mem hclose, hnu,
    show 1 / (cpr r s c * B) * ((t : ℚ) * A) = (t : ℚ) * A / (cpr r s c * B) by ring,
    red_core hℓ2 hγ p ht (natCast_mem_Zl t), red_div (natCast_mem_Zl t) (padicNorm_cpr hℓ2 p),
    red_div (pole_mem_Zl hℓ2 _) (padicNorm_cpr hℓ2 p), red_t_eq hℓ2 hγ p ht]

/-- **Residue, off-diagonal, type D.** -/
theorem resid_off_D (hk : γ = kap ℓ) :
    nu ℓ (idx ℓ γ r) (idx ℓ γ s) * (derivative (Fpoly (3 * ℓ) (idx ℓ γ r) (idx ℓ γ s))).eval (t : ℚ) ∈ Zl ℓ ∧
    red ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ s) *
      (derivative (Fpoly (3 * ℓ) (idx ℓ γ r) (idx ℓ γ s))).eval (t : ℚ)) =
      red ℓ ((2 * (t : ℚ) - pole (idx ℓ γ c)) / ℓ / cpr r s c) := by
  have hi := idx_lt hγ p.hr
  have hj := idx_lt hγ p.hs
  have hmem := nuF_le_one hℓ2 hi hj (idx_ne p.rs) t
  refine ⟨hmem, ?_⟩
  obtain ⟨hcT, hKT, h3, h4⟩ := Tset_facts hℓ2 hγ p ht
  have hcK : idx ℓ γ c ≠ 3 * ℓ := Nat.ne_of_lt (idx_lt hγ p.hc)
  have hS : ({idx ℓ γ c, 3 * ℓ} : Finset ℕ) ⊆
      ((range (3 * ℓ + 1)).erase (idx ℓ γ r)).erase (idx ℓ γ s) :=
    insert_subset hcT (singleton_subset_iff.mpr hKT)
  have hdiff := padicNorm_deriv_sub_le hS (rt (3 * ℓ)) (t : ℚ)
    (fun m _ => padicNorm_sub_rt_le_one hℓ2 _ _ _)
    (fun m hm => by
      rcases mem_insert.mp hm with h | h
      · rw [h, rt_of_lt (idx_lt hγ p.hc)]; exact close_member hℓ2 hγ p ht p.hc
      · rw [mem_singleton.mp h]; exact padicNorm_sub_rt_self_close ((dvd_t_iff hℓ2 hγ ht).mpr hk))
  set A := ∏ m ∈ restSet ℓ γ r s c, ((t : ℚ) - pole m)
  set B := ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)
  have hKe : ∏ m ∈ (((range (3 * ℓ + 1)).erase (idx ℓ γ r)).erase (idx ℓ γ s)).erase (3 * ℓ),
      ((t : ℚ) - rt (3 * ℓ) m) = ((t : ℚ) - pole (idx ℓ γ c)) * A := by
    have hc' : idx ℓ γ c ∈
        (((range (3 * ℓ + 1)).erase (idx ℓ γ r)).erase (idx ℓ γ s)).erase (3 * ℓ) :=
      mem_erase.mpr ⟨hcK, hcT⟩
    rw [← mul_prod_erase _ _ hc', h4, rt_of_lt (idx_lt hγ p.hc)]
    congr 1
    exact prod_congr rfl (fun m hm => by rw [rt_of_lt (mem_range.mp (restSet_subset ℓ γ r s c hm))])
  rw [sum_pair hcK, h3, prod_insert_rt _ hγ p, hKe, card_pair hcK, ← Fpoly_eq_prod hi hj] at hdiff
  have hnu := nu_eq_D hℓ2 hγ p ht hk s p.hs
  have hnuN : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ s)) = ℓ := by
    rw [padicNorm_nu hℓ2 hi, ite_eq_left (by rw [idx_mod hγ]; exact hk)]
  set L := (2 * (t : ℚ) - pole (idx ℓ γ c)) / ℓ
  have hL : L ∈ Zl ℓ := by
    have e : L = 2 * ((t / ℓ : ℕ) : ℚ) + ((c : ℚ) + 1 / 2) := by
      simp only [L]
      rw [t_eq_ell_mul hℓ2 hγ p ht hk, hk, pole_idx_kap hℓ2]
      field_simp [ell_pos.ne']
      ring
    rw [e]
    exact add_mem (mul_mem (by exact_mod_cast natCast_mem_Zl 2) (natCast_mem_Zl _)) (half_add_mem hℓ2 c)
  have hval : nu ℓ (idx ℓ γ r) (idx ℓ γ s) * ((t : ℚ) * A + ((t : ℚ) - pole (idx ℓ γ c)) * A) =
      L * A / (cpr r s c * B) := by
    rw [hnu]; simp only [L]; field_simp [ell_pos.ne']; ring
  have hmain_mem : L * A / (cpr r s c * B) ∈ Zl ℓ := by
    rw [div_eq_mul_inv]
    refine mul_mem (mul_mem hL (restProd_t_mem hℓ2 hγ p ht)) (inv_mem_Zl ?_)
    rw [padicNorm.mul, padicNorm_cpr hℓ2 p, padicNorm_restProd hγ p, one_mul]
  have hclose : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ s) *
      (derivative (Fpoly (3 * ℓ) (idx ℓ γ r) (idx ℓ γ s))).eval (t : ℚ) -
        L * A / (cpr r s c * B)) < 1 := by
    rw [← hval, ← mul_sub, padicNorm.mul, hnuN]
    calc (ℓ : ℚ) * padicNorm ℓ _ ≤ (ℓ : ℚ) * ((ℓ : ℚ)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left hdiff ell_pos.le
      _ = (ℓ : ℚ)⁻¹ := by rw [ell_mul_inv_pow 1, pow_one]
      _ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt)
  rw [red_eq_of_sub hmem hmain_mem hclose, red_core hℓ2 hγ p ht hL]

/-- The split `g_i = (X − x_j)(X − x_c) · X · ∏_rest (X − x_m)`. -/
lemma gpoly_split :
    gpoly (3 * ℓ) (idx ℓ γ r) = ((X - C (pole (idx ℓ γ s))) * (X - C (pole (idx ℓ γ c)))) *
      (X * ∏ m ∈ restSet ℓ γ r s c, (X - C (pole m))) := by
  have hi := idx_lt hγ p.hr
  rw [gpoly_eq_prod hi]
  set U := (range (3 * ℓ + 1)).erase (idx ℓ γ r)
  have hjU : idx ℓ γ s ∈ U :=
    mem_erase.mpr ⟨idx_ne p.rs.symm, mem_range.mpr (by have := idx_lt hγ p.hs; omega)⟩
  have hcU : idx ℓ γ c ∈ U.erase (idx ℓ γ s) := mem_erase.mpr ⟨idx_ne p.sc.symm,
    mem_erase.mpr ⟨idx_ne p.rc.symm, mem_range.mpr (by have := idx_lt hγ p.hc; omega)⟩⟩
  rw [← mul_prod_erase _ _ hjU, ← mul_prod_erase _ _ hcU, erase3_eq_insert hγ p,
    prod_insert_rt_X hγ p, rt_of_lt (idx_lt hγ p.hs), rt_of_lt (idx_lt hγ p.hc)]
  ring

lemma zlPoly_restProd : ZlPoly ℓ (∏ m ∈ restSet ℓ γ r s c, (X - C (pole m))) :=
  zlPoly_prod _ _ (fun m _ => zlPoly_X_sub_C (pole_mem_Zl hℓ2 m))

lemma eval_deriv_mem {R : ℚ[X]} (hR : ZlPoly ℓ R) : (derivative R).eval (t : ℚ) ∈ Zl ℓ :=
  eval_mem_Zl (zlPoly_derivative hR) (natCast_mem_Zl t)

lemma eval_deriv_DD_mem {R : ℚ[X]} (hR : ZlPoly ℓ R) (x : ℚ) (hx : x ∈ Zl ℓ) :
    (derivative (DD x R)).eval (t : ℚ) ∈ Zl ℓ :=
  eval_mem_Zl (zlPoly_derivative (zlPoly_divDiff hR hx)) (natCast_mem_Zl t)

lemma pole_idx_sub_small (a b : ℕ) :
    padicNorm ℓ (pole (idx ℓ γ a) - pole (idx ℓ γ b)) ≤ (ℓ : ℚ)⁻¹ := by
  rw [pole_idx_sub, padicNorm.mul, padicNorm_self]
  have : ((b : ℚ) - a) = (((b : ℤ) - a : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  calc (ℓ : ℚ)⁻¹ * padicNorm ℓ (((b : ℤ) - a : ℤ) : ℚ) ≤ (ℓ : ℚ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (padicNorm.of_int _) ell_inv_pos.le
    _ = _ := mul_one _

/-- **Residue, diagonal, types S and L.** -/
theorem resid_diag_SL (hk : γ ≠ kap ℓ) :
    nu ℓ (idx ℓ γ r) (idx ℓ γ r) * (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) ∈ Zl ℓ ∧
    red ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ r) * (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ)) =
      red ℓ (pole (idx ℓ γ r) / cpr r s c) := by
  have hi := idx_lt hγ p.hr
  set x := pole (idx ℓ γ r)
  set xj := pole (idx ℓ γ s)
  set xc := pole (idx ℓ γ c)
  set R := X * ∏ m ∈ restSet ℓ γ r s c, (X - C (pole m))
  have hR : ZlPoly ℓ R := zlPoly_mul zlPoly_X (zlPoly_restProd hℓ2 hγ p ht)
  have hQ : derivative (Qpoly (3 * ℓ) (idx ℓ γ r)) =
      R + (X + C (x - xj - xc)) * derivative R +
        C (((X - C xj) * (X - C xc)).eval x) * derivative (DD x R) := by
    rw [Qpoly_eq_DD, gpoly_split hℓ2 hγ p ht, derivative_DD_quad_mul]
  set A := ∏ m ∈ restSet ℓ γ r s c, ((t : ℚ) - pole m)
  set B := ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)
  have hRt : R.eval (t : ℚ) = (t : ℚ) * A := by simp [R, A, eval_prod]
  have hk1 : padicNorm ℓ ((t : ℚ) + (x - xj - xc)) ≤ (ℓ : ℚ)⁻¹ := by
    have : (t : ℚ) + (x - xj - xc) = ((t : ℚ) - xj) + (x - xc) := by ring
    rw [this]
    exact pn_add_le (close_member hℓ2 hγ p ht p.hs) (pole_idx_sub_small hℓ2 hγ p ht r c)
  have hPx : padicNorm ℓ ((x - xj) * (x - xc)) ≤ (ℓ : ℚ)⁻¹ :=
    pn_mul_le_left ((pole_idx_sub_small hℓ2 hγ p ht r s).trans ell_inv_le_one)
      (pole_idx_sub_small hℓ2 hγ p ht r c)
  have hdiff : padicNorm ℓ ((derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) - (t : ℚ) * A) ≤
      (ℓ : ℚ)⁻¹ := by
    rw [hQ]
    simp only [eval_add, eval_mul, eval_X, eval_C, eval_sub]
    rw [hRt]
    have e : (t : ℚ) * A + ((t : ℚ) + (x - xj - xc)) * (derivative R).eval (t : ℚ) +
        ((x - xj) * (x - xc)) * (derivative (DD x R)).eval (t : ℚ) - (t : ℚ) * A =
        ((t : ℚ) + (x - xj - xc)) * (derivative R).eval (t : ℚ) +
        ((x - xj) * (x - xc)) * (derivative (DD x R)).eval (t : ℚ) := by ring
    rw [e]
    refine pn_add_le ?_ ?_
    · rw [mul_comm]; exact pn_mul_le_left (eval_deriv_mem hℓ2 hγ p ht hR) hk1
    · rw [mul_comm]
      exact pn_mul_le_left (eval_deriv_DD_mem hℓ2 hγ p ht hR x (pole_mem_Zl hℓ2 _)) hPx
  have hnu := nu_eq_SL hℓ2 hγ p ht hk r p.hr
  have hnu1 : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ r)) = 1 := by
    rw [padicNorm_nu hℓ2 hi, ite_eq_right (by rw [idx_mod hγ]; exact hk)]
  have hmain_mem : nu ℓ (idx ℓ γ r) (idx ℓ γ r) * ((t : ℚ) * A) ∈ Zl ℓ :=
    mul_mem (le_of_eq hnu1) (mul_mem (natCast_mem_Zl t) (restProd_t_mem hℓ2 hγ p ht))
  have hsmall : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ r) *
      (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) -
      nu ℓ (idx ℓ γ r) (idx ℓ γ r) * ((t : ℚ) * A)) ≤ (ℓ : ℚ)⁻¹ := by
    rw [← mul_sub, padicNorm.mul, hnu1, one_mul]; exact hdiff
  have hmem : nu ℓ (idx ℓ γ r) (idx ℓ γ r) *
      (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) ∈ Zl ℓ := by
    have := add_mem hmain_mem (show _ ∈ Zl ℓ from hsmall.trans ell_inv_le_one)
    rwa [add_sub_cancel] at this
  refine ⟨hmem, ?_⟩
  rw [red_eq_of_sub hmem hmain_mem
      (lt_of_le_of_lt hsmall (inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt))),
    hnu, show 1 / (cpr r s c * B) * ((t : ℚ) * A) = (t : ℚ) * A / (cpr r s c * B) by ring,
    red_core hℓ2 hγ p ht (natCast_mem_Zl t), red_div (natCast_mem_Zl t) (padicNorm_cpr hℓ2 p),
    red_div (pole_mem_Zl hℓ2 _) (padicNorm_cpr hℓ2 p), red_t_eq hℓ2 hγ p ht]

/-- **Residue, diagonal, type D.** -/
theorem resid_diag_D (hk : γ = kap ℓ) :
    nu ℓ (idx ℓ γ r) (idx ℓ γ r) * (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) ∈ Zl ℓ ∧
    red ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ r) * (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ)) =
      red ℓ ((2 * (t : ℚ) + pole (idx ℓ γ r) - pole (idx ℓ γ s) - pole (idx ℓ γ c)) / ℓ /
        cpr r s c) := by
  have hi := idx_lt hγ p.hr
  set x := pole (idx ℓ γ r)
  set xj := pole (idx ℓ γ s)
  set xc := pole (idx ℓ γ c)
  set R := ∏ m ∈ restSet ℓ γ r s c, (X - C (pole m))
  have hR : ZlPoly ℓ R := zlPoly_restProd hℓ2 hγ p ht
  set k := x - xj - xc
  set k₀ := x ^ 2 - (xj + xc) * x + xj * xc
  have hg : gpoly (3 * ℓ) (idx ℓ γ r) = (X * ((X - C xj) * (X - C xc))) * R := by
    rw [gpoly_split hℓ2 hγ p ht]; ring
  have hQ : derivative (Qpoly (3 * ℓ) (idx ℓ γ r)) =
      (2 * X + C k) * R + (X ^ 2 + C k * X + C k₀) * derivative R +
        C (x * ((x - xj) * (x - xc))) * derivative (DD x R) := by
    rw [Qpoly_eq_DD, hg, derivative_DD_cubic_mul]
  set A := ∏ m ∈ restSet ℓ γ r s c, ((t : ℚ) - pole m)
  set B := ∏ m ∈ restSet ℓ γ r s c, (pole (idx ℓ γ r) - pole m)
  have hRt : R.eval (t : ℚ) = A := by simp [R, A, eval_prod]
  have hts := t_small hℓ2 hγ p ht hk
  have hxs : ∀ a, padicNorm ℓ (pole (idx ℓ γ a)) ≤ (ℓ : ℚ)⁻¹ := fun a => by
    rw [hk]; exact padicNorm_pole_idx_kap hℓ2 a
  have hks : padicNorm ℓ k ≤ (ℓ : ℚ)⁻¹ := pn_sub_le (pn_sub_le (hxs r) (hxs s)) (hxs c)
  have hsq : ∀ {a b : ℚ}, padicNorm ℓ a ≤ (ℓ : ℚ)⁻¹ → padicNorm ℓ b ≤ (ℓ : ℚ)⁻¹ →
      padicNorm ℓ (a * b) ≤ ((ℓ : ℚ)⁻¹) ^ 2 := fun ha hb => by
    rw [sq]; exact pn_mul_le ha hb ell_inv_pos.le
  have hpoly : padicNorm ℓ ((t : ℚ) ^ 2 + k * t + k₀) ≤ ((ℓ : ℚ)⁻¹) ^ 2 := by
    simp only [k₀]
    refine pn_add_le (pn_add_le ?_ (hsq hks hts)) (pn_add_le (pn_sub_le ?_ ?_) (hsq (hxs s) (hxs c)))
    · rw [sq]; exact hsq hts hts
    · rw [sq]; exact hsq (hxs r) (hxs r)
    · exact hsq (pn_add_le (hxs s) (hxs c)) (hxs r)
  have hPx : padicNorm ℓ (x * ((x - xj) * (x - xc))) ≤ ((ℓ : ℚ)⁻¹) ^ 2 :=
    hsq (hxs r) (pn_mul_le_left ((pn_sub_le (hxs r) (hxs s)).trans ell_inv_le_one)
      (pn_sub_le (hxs r) (hxs c)))
  have hdiff : padicNorm ℓ ((derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) -
      (2 * (t : ℚ) + k) * A) ≤ ((ℓ : ℚ)⁻¹) ^ 2 := by
    rw [hQ]
    simp only [eval_add, eval_mul, eval_X, eval_C, eval_pow, eval_ofNat]
    rw [hRt]
    have e : (2 * (t : ℚ) + k) * A + ((t : ℚ) ^ 2 + k * t + k₀) * (derivative R).eval (t : ℚ) +
        (x * ((x - xj) * (x - xc))) * (derivative (DD x R)).eval (t : ℚ) - (2 * (t : ℚ) + k) * A =
        ((t : ℚ) ^ 2 + k * t + k₀) * (derivative R).eval (t : ℚ) +
        (x * ((x - xj) * (x - xc))) * (derivative (DD x R)).eval (t : ℚ) := by ring
    rw [e]
    refine pn_add_le ?_ ?_
    · rw [mul_comm]; exact pn_mul_le_left (eval_deriv_mem hℓ2 hγ p ht hR) hpoly
    · rw [mul_comm]
      exact pn_mul_le_left (eval_deriv_DD_mem hℓ2 hγ p ht hR x (pole_mem_Zl hℓ2 _)) hPx
  have hnu := nu_eq_D hℓ2 hγ p ht hk r p.hr
  have hnuN : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ r)) = ℓ := by
    rw [padicNorm_nu hℓ2 hi, ite_eq_left (by rw [idx_mod hγ]; exact hk)]
  set L := (2 * (t : ℚ) + x - xj - xc) / ℓ
  have hL : L ∈ Zl ℓ := by
    have e : L = 2 * ((t / ℓ : ℕ) : ℚ) - ((r : ℚ) + 1 / 2) + ((s : ℚ) + 1 / 2) +
        ((c : ℚ) + 1 / 2) := by
      simp only [L, x, xj, xc]
      rw [t_eq_ell_mul hℓ2 hγ p ht hk, hk, pole_idx_kap hℓ2, pole_idx_kap hℓ2, pole_idx_kap hℓ2]
      field_simp [ell_pos.ne']
      ring
    rw [e]
    exact add_mem (add_mem (sub_mem (mul_mem (by exact_mod_cast natCast_mem_Zl 2)
      (natCast_mem_Zl _)) (half_add_mem hℓ2 r)) (half_add_mem hℓ2 s)) (half_add_mem hℓ2 c)
  have hval : nu ℓ (idx ℓ γ r) (idx ℓ γ r) * ((2 * (t : ℚ) + k) * A) = L * A / (cpr r s c * B) := by
    rw [hnu]; simp only [L, k]; field_simp [ell_pos.ne']; ring
  have hmain_mem : L * A / (cpr r s c * B) ∈ Zl ℓ := by
    rw [div_eq_mul_inv]
    refine mul_mem (mul_mem hL (restProd_t_mem hℓ2 hγ p ht)) (inv_mem_Zl ?_)
    rw [padicNorm.mul, padicNorm_cpr hℓ2 p, padicNorm_restProd hγ p, one_mul]
  have hsmall : padicNorm ℓ (nu ℓ (idx ℓ γ r) (idx ℓ γ r) *
      (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) - L * A / (cpr r s c * B)) ≤
        (ℓ : ℚ)⁻¹ := by
    rw [← hval, ← mul_sub, padicNorm.mul, hnuN]
    calc (ℓ : ℚ) * padicNorm ℓ _ ≤ (ℓ : ℚ) * ((ℓ : ℚ)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left hdiff ell_pos.le
      _ = (ℓ : ℚ)⁻¹ := by rw [ell_mul_inv_pow 1, pow_one]
  have hmem : nu ℓ (idx ℓ γ r) (idx ℓ γ r) *
      (derivative (Qpoly (3 * ℓ) (idx ℓ γ r))).eval (t : ℚ) ∈ Zl ℓ := by
    have := add_mem hmain_mem (show _ ∈ Zl ℓ from hsmall.trans ell_inv_le_one)
    rwa [add_sub_cancel] at this
  refine ⟨hmem, ?_⟩
  rw [red_eq_of_sub hmem hmain_mem
      (lt_of_le_of_lt hsmall (inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt))),
    red_core hℓ2 hγ p ht hL]

end

end Chi2Irr
