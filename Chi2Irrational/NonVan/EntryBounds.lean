/-
# Lemma P along `K = 3ℓ`: pointwise bounds for the normalised entries

`ν_ij = ℓ^{2−δ_j}/D′(x_i)` (`nu`), `‖ν_ij‖ = ℓ^{δ_j}`. For every integer `t` (on the progression of some `γ`):
* `nuF_le_one`: `‖ν_ij F_ij′(t)‖ ≤ 1` (`i ≠ j`);
* `nuF_small_offclass`: `‖ν_ij F_ij′(t)‖ ≤ ℓ⁻¹` if `class j ≠ κ` and `class i ≠ class j`;
* `nuF_small_offprog`: `‖ν_ij F_ij′(t)‖ ≤ ℓ⁻¹` if `class i = class j ≠ γ`;
* `nuQ_small_offprog`: `‖ν_ii Q_i′(t)‖ ≤ ℓ⁻¹` if `class i ≠ γ`.
-/
import Chi2Irrational.NonVan.ClassData

namespace Chi2Irr

open Polynomial Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The normaliser `ν_ij = ℓ^{2−δ_j}/D′(x_i)` (`K = 3ℓ`). -/
noncomputable def nu (ℓ i j : ℕ) : ℚ :=
  (if j % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) / dPrime (3 * ℓ) i

lemma exists_perm {r : ℕ} (hr : r < 3) : ∃ s c, Perm3 r s c := by
  interval_cases r
  · exact ⟨1, 2, ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨0, 2, ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨0, 1, ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

lemma idx_mod_div {i : ℕ} : idx ℓ (i % ℓ) (i / ℓ) = i := by
  unfold idx; exact Nat.mod_add_div i ℓ

lemma div_lt_three {i : ℕ} (hi : i < 3 * ℓ) : i / ℓ < 3 :=
  (Nat.div_lt_iff_lt_mul hℓ.out.pos).mpr (by linarith)

lemma padicNorm_dPrime' (hℓ2 : ℓ ≠ 2) {i : ℕ} (hi : i < 3 * ℓ) :
    padicNorm ℓ (dPrime (3 * ℓ) i) = ((ℓ : ℚ)⁻¹) ^ 2 := by
  obtain ⟨s, c, p⟩ := exists_perm (div_lt_three hi)
  have := padicNorm_dPrime hℓ2 (Nat.mod_lt i hℓ.out.pos) p
  rwa [idx_mod_div] at this

lemma padicNorm_nu (hℓ2 : ℓ ≠ 2) {i : ℕ} (hi : i < 3 * ℓ) (j : ℕ) :
    padicNorm ℓ (nu ℓ i j) = if j % ℓ = kap ℓ then (ℓ : ℚ) else 1 := by
  unfold nu
  have hpos := ell_pos (ℓ := ℓ)
  rw [padicNorm.div, padicNorm_dPrime' hℓ2 hi]
  split_ifs
  · rw [padicNorm_self]; field_simp
  · rw [padicNorm_ell_pow]; field_simp

lemma padicNorm_nu_le (hℓ2 : ℓ ≠ 2) {i : ℕ} (hi : i < 3 * ℓ) (j : ℕ) :
    padicNorm ℓ (nu ℓ i j) ≤ ℓ := by
  rw [padicNorm_nu hℓ2 hi]
  split_ifs
  · exact le_refl _
  · exact_mod_cast hℓ.out.one_lt.le

/-- Every integer `t` lies on the progression of some class `γ`. -/
lemma exists_prog (hℓ2 : ℓ ≠ 2) (t : ℕ) : ∃ γ < ℓ, ℓ ∣ 2 * t + 2 * γ + 1 := by
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  have hℓpos := hℓ.out.pos
  set g' := kap ℓ + ℓ - t % ℓ
  refine ⟨g' % ℓ, Nat.mod_lt _ hℓpos, ?_⟩
  have h1 : 2 * t + 2 * g' + 1 = ℓ * (2 * (t / ℓ) + 3) := by
    have := Nat.mod_add_div t ℓ
    have := Nat.mod_lt t hℓpos
    simp only [g']
    zify [show t % ℓ ≤ kap ℓ + ℓ by omega] at *
    nlinarith
  have h2 : 2 * t + 2 * (g' % ℓ) + 1 + ℓ * (2 * (g' / ℓ)) = 2 * t + 2 * g' + 1 := by
    have := Nat.mod_add_div g' ℓ
    linarith
  have h3 : ℓ ∣ 2 * t + 2 * (g' % ℓ) + 1 + ℓ * (2 * (g' / ℓ)) := by
    rw [h2, h1]; exact dvd_mul_right _ _
  exact (Nat.dvd_add_left (dvd_mul_right ℓ _)).mp h3

/-! ### Card of the close roots of `F_ij` -/

lemma card_S_off {γ i j : ℕ} (hγ : γ < ℓ) (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) (hij : i ≠ j) :
    (((closeSet ℓ γ).erase i).erase j).card + (if i % ℓ = γ then 1 else 0) +
      (if j % ℓ = γ then 1 else 0) = 3 + (if γ = kap ℓ then 1 else 0) := by
  rw [← card_closeSet hγ]
  have hiC := mem_closeSet_of_lt (ℓ := ℓ) (γ := γ) hi
  have hjC := mem_closeSet_of_lt (ℓ := ℓ) (γ := γ) hj
  by_cases ha : i % ℓ = γ <;> by_cases hb : j % ℓ = γ
  · rw [ite_eq_left ha, ite_eq_left hb, card_erase_of_mem (mem_erase.mpr ⟨hij.symm, hjC.mpr hb⟩),
      card_erase_of_mem (hiC.mpr ha)]
    have : 2 ≤ (closeSet ℓ γ).card := by rw [card_closeSet hγ]; split_ifs <;> omega
    omega
  · rw [ite_eq_left ha, ite_eq_right hb, erase_eq_of_notMem (fun h => hb (hjC.mp (mem_of_mem_erase h))),
      card_erase_of_mem (hiC.mpr ha)]
    have : 1 ≤ (closeSet ℓ γ).card := by rw [card_closeSet hγ]; split_ifs <;> omega
    omega
  · rw [ite_eq_right ha, ite_eq_left hb, erase_eq_of_notMem (fun h => ha (hiC.mp h)),
      card_erase_of_mem (hjC.mpr hb)]
    have : 1 ≤ (closeSet ℓ γ).card := by rw [card_closeSet hγ]; split_ifs <;> omega
    omega
  · rw [ite_eq_right ha, ite_eq_right hb, erase_eq_of_notMem (fun h => ha (hiC.mp h)),
      erase_eq_of_notMem (fun h => hb (hjC.mp h))]
    simp

/-- `‖F_ij′(t)‖ ≤ ℓ^{−(#S−1)}`, `S` the close roots of `F_ij`. -/
lemma padicNorm_Fpoly_deriv_le (hℓ2 : ℓ ≠ 2) {γ i j t : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1)
    (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) :
    padicNorm ℓ ((derivative (Fpoly (3 * ℓ) i j)).eval (t : ℚ)) ≤
      ((ℓ : ℚ)⁻¹) ^ ((((closeSet ℓ γ).erase i).erase j).card - 1) := by
  rw [Fpoly_eq_prod hi hj]
  refine padicNorm_deriv_le_of_close ?_ _ _ (fun m _ => padicNorm_sub_rt_le_one hℓ2 _ _ _)
    (fun m hm => close_of_mem_closeSet hℓ2 hγ ht (mem_of_mem_erase (mem_of_mem_erase hm)))
  exact erase_subset_erase j (erase_subset_erase i (closeSet_subset γ))

lemma inv_pow_anti {a b : ℕ} (h : a ≤ b) : ((ℓ : ℚ)⁻¹) ^ b ≤ ((ℓ : ℚ)⁻¹) ^ a :=
  pow_le_pow_of_le_one ell_inv_pos.le ell_inv_le_one h

lemma ell_mul_inv_pow (n : ℕ) : (ℓ : ℚ) * ((ℓ : ℚ)⁻¹) ^ (n + 1) = ((ℓ : ℚ)⁻¹) ^ n := by
  rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ ell_pos.ne', one_mul]

/-- The basic estimate `‖ν F′(t)‖ ≤ ℓ^{δ_j} ℓ^{−(n−1)}`, in the form used below. -/
lemma nuF_le_pow (hℓ2 : ℓ ≠ 2) {γ i j t e : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1)
    (hi : i < 3 * ℓ) (hj : j < 3 * ℓ)
    (hcount : e + (if j % ℓ = kap ℓ then 1 else 0) + 1 ≤ (((closeSet ℓ γ).erase i).erase j).card) :
    padicNorm ℓ (nu ℓ i j * (derivative (Fpoly (3 * ℓ) i j)).eval (t : ℚ)) ≤ ((ℓ : ℚ)⁻¹) ^ e := by
  rw [padicNorm.mul, padicNorm_nu hℓ2 hi]
  have hF := padicNorm_Fpoly_deriv_le hℓ2 hγ ht hi hj
  have hF0 := padicNorm.nonneg (p := ℓ) ((derivative (Fpoly (3 * ℓ) i j)).eval (t : ℚ))
  split_ifs at hcount ⊢ with hb
  · calc (ℓ : ℚ) * padicNorm ℓ ((derivative (Fpoly (3 * ℓ) i j)).eval (t : ℚ))
        ≤ (ℓ : ℚ) * ((ℓ : ℚ)⁻¹) ^ (e + 1) := by
          refine mul_le_mul_of_nonneg_left (hF.trans (inv_pow_anti (by omega))) ell_pos.le
      _ = _ := ell_mul_inv_pow e
  · rw [one_mul]
    exact hF.trans (inv_pow_anti (by omega))

lemma nuF_le_one (hℓ2 : ℓ ≠ 2) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) (hij : i ≠ j) (t : ℕ) :
    padicNorm ℓ (nu ℓ i j * (derivative (Fpoly (3 * ℓ) i j)).eval (t : ℚ)) ≤ 1 := by
  obtain ⟨γ, hγ, ht⟩ := exists_prog (hℓ := hℓ) hℓ2 t
  have hc := card_S_off hγ hi hj hij
  have := nuF_le_pow (e := 0) hℓ2 hγ ht hi hj (by
    by_cases hb : j % ℓ = kap ℓ
    · rw [ite_eq_left hb]
      by_cases hgk : γ = kap ℓ
      · rw [ite_eq_left hgk] at hc
        have : j % ℓ = γ := by rw [hb, hgk]
        rw [ite_eq_left this] at hc
        split_ifs at hc <;> omega
      · rw [ite_eq_right hgk] at hc
        have : ¬ j % ℓ = γ := fun h => hgk (h ▸ hb)
        rw [ite_eq_right this] at hc
        split_ifs at hc <;> omega
    · rw [ite_eq_right hb]; split_ifs at hc <;> omega)
  simpa using this

lemma nuF_small_offclass (hℓ2 : ℓ ≠ 2) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ)
    (hb : j % ℓ ≠ kap ℓ) (hab : i % ℓ ≠ j % ℓ) (t : ℕ) :
    padicNorm ℓ (nu ℓ i j * (derivative (Fpoly (3 * ℓ) i j)).eval (t : ℚ)) ≤ (ℓ : ℚ)⁻¹ := by
  have hij : i ≠ j := fun h => hab (h ▸ rfl)
  obtain ⟨γ, hγ, ht⟩ := exists_prog (hℓ := hℓ) hℓ2 t
  have hc := card_S_off hγ hi hj hij
  have := nuF_le_pow (e := 1) hℓ2 hγ ht hi hj (by
    rw [ite_eq_right hb]
    by_cases ha : i % ℓ = γ
    · have : ¬ j % ℓ = γ := fun h => hab (ha.trans h.symm)
      rw [ite_eq_left ha, ite_eq_right this] at hc; split_ifs at hc <;> omega
    · rw [ite_eq_right ha] at hc; split_ifs at hc <;> omega)
  simpa using this

lemma nuF_small_offprog (hℓ2 : ℓ ≠ 2) {γ i j t : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1)
    (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) (hij : i ≠ j) (hab : i % ℓ = j % ℓ) (hag : i % ℓ ≠ γ) :
    padicNorm ℓ (nu ℓ i j * (derivative (Fpoly (3 * ℓ) i j)).eval (t : ℚ)) ≤ (ℓ : ℚ)⁻¹ := by
  have hc := card_S_off hγ hi hj hij
  have hbg : ¬ j % ℓ = γ := fun h => hag (hab.trans h)
  rw [ite_eq_right hag, ite_eq_right hbg] at hc
  have := nuF_le_pow (e := 1) hℓ2 hγ ht hi hj (by
    by_cases hb : j % ℓ = kap ℓ
    · rw [ite_eq_left hb]
      have : ¬ γ = kap ℓ := fun h => hbg (hb.trans h.symm)
      rw [ite_eq_right this] at hc; omega
    · rw [ite_eq_right hb]; split_ifs at hc <;> omega)
  simpa using this

/-! ### The diagonal off its own progression -/

lemma padicNorm_gpoly_bounds (hℓ2 : ℓ ≠ 2) {γ i t : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1)
    (hi : i < 3 * ℓ) (hag : i % ℓ ≠ γ) :
    padicNorm ℓ ((gpoly (3 * ℓ) i).eval (t : ℚ)) ≤ ((ℓ : ℚ)⁻¹) ^ 3 ∧
      padicNorm ℓ ((derivative (gpoly (3 * ℓ) i)).eval (t : ℚ)) ≤ ((ℓ : ℚ)⁻¹) ^ 2 := by
  have hiC : i ∉ closeSet ℓ γ := fun h => hag ((mem_closeSet_of_lt hi).mp h)
  have hsub : closeSet ℓ γ ⊆ (range (3 * ℓ + 1)).erase i :=
    fun m hm => mem_erase.mpr ⟨fun e => hiC (e ▸ hm), closeSet_subset γ hm⟩
  have hcard : 3 ≤ (closeSet ℓ γ).card := by rw [card_closeSet hγ]; omega
  have hclose := fun m (hm : m ∈ closeSet ℓ γ) => close_of_mem_closeSet hℓ2 hγ ht hm
  rw [gpoly_eq_prod hi]
  constructor
  · rw [eval_prod_X_sub_C]
    exact (padicNorm_prod_le_of_close hsub (fun m => (t : ℚ) - rt (3 * ℓ) m)
      (fun m _ => padicNorm_sub_rt_le_one hℓ2 _ _ _) hclose).trans (inv_pow_anti hcard)
  · exact (padicNorm_deriv_le_of_close hsub _ _ (fun m _ => padicNorm_sub_rt_le_one hℓ2 _ _ _)
      hclose).trans (inv_pow_anti (by omega))

lemma nuQ_small_offprog (hℓ2 : ℓ ≠ 2) {γ i t : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ + 1)
    (hi : i < 3 * ℓ) (hag : i % ℓ ≠ γ) :
    padicNorm ℓ (nu ℓ i i * (derivative (Qpoly (3 * ℓ) i)).eval (t : ℚ)) ≤ (ℓ : ℚ)⁻¹ := by
  obtain ⟨hg, hg'⟩ := padicNorm_gpoly_bounds hℓ2 hγ ht hi hag
  set x := pole i
  set g := gpoly (3 * ℓ) i
  set Q := Qpoly (3 * ℓ) i
  have hunit : padicNorm ℓ ((t : ℚ) - x) = 1 := by
    have := padicNorm_sub_rt_unit (K := 3 * ℓ) hℓ2 hi
      (fun h => hag ((dvd_iff_mod_eq hℓ2 hγ ht i).mp h))
    rwa [rt_of_lt hi] at this
  have hne : (t : ℚ) - x ≠ 0 := by
    intro h; rw [h, padicNorm.zero] at hunit; exact zero_ne_one hunit
  have hgx : padicNorm ℓ (g.eval x) ≤ ((ℓ : ℚ)⁻¹) ^ 2 := by
    rw [eval_gpoly_pole, padicNorm.mul, padicNorm_dPrime' hℓ2 hi]
    have := pole_mem_Zl (ℓ := ℓ) hℓ2 i
    calc padicNorm ℓ (pole i) * ((ℓ : ℚ)⁻¹) ^ 2 ≤ 1 * ((ℓ : ℚ)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right this (pow_nonneg ell_inv_pos.le 2)
      _ = _ := one_mul _
  have hdecomp := gpoly_eq (3 * ℓ) i
  have hval : g.eval (t : ℚ) = ((t : ℚ) - x) * Q.eval (t : ℚ) + g.eval x := by
    have := congrArg (eval (t : ℚ)) hdecomp
    simpa [eval_mul, eval_add] using this
  have hder : (derivative g).eval (t : ℚ) = Q.eval (t : ℚ) + ((t : ℚ) - x) * (derivative Q).eval (t : ℚ) := by
    have := congrArg (fun p => (derivative p).eval (t : ℚ)) hdecomp
    simpa [derivative_mul, eval_mul, eval_add] using this
  have hQ : padicNorm ℓ (Q.eval (t : ℚ)) ≤ ((ℓ : ℚ)⁻¹) ^ 2 := by
    have hQe : Q.eval (t : ℚ) = (g.eval (t : ℚ) - g.eval x) / ((t : ℚ) - x) := by
      rw [hval]; field_simp; ring
    rw [hQe, padicNorm.div, hunit, div_one]
    refine padicNorm.sub.trans (max_le (hg.trans (inv_pow_anti (by norm_num))) hgx)
  have hQ' : padicNorm ℓ ((derivative Q).eval (t : ℚ)) ≤ ((ℓ : ℚ)⁻¹) ^ 2 := by
    have hQe : (derivative Q).eval (t : ℚ) = ((derivative g).eval (t : ℚ) - Q.eval (t : ℚ)) / ((t : ℚ) - x) := by
      rw [hder]; field_simp; ring
    rw [hQe, padicNorm.div, hunit, div_one]
    exact padicNorm.sub.trans (max_le hg' hQ)
  rw [padicNorm.mul]
  calc padicNorm ℓ (nu ℓ i i) * padicNorm ℓ ((derivative Q).eval (t : ℚ))
      ≤ (ℓ : ℚ) * ((ℓ : ℚ)⁻¹) ^ 2 :=
        mul_le_mul (padicNorm_nu_le hℓ2 hi i) hQ' (padicNorm.nonneg _) ell_pos.le
    _ = (ℓ : ℚ)⁻¹ := by rw [ell_mul_inv_pow 1, pow_one]

end Chi2Irr
