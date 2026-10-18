/-
# Lemma P along `K = 3ℓ`: the blocks are `λ_γ · M̄(type)`

The ℓ-independent rational block matrices (`c_r = 1/c′_r = 1/2, −1, 1/2`, `w = q⁻²`, `T_n` as in `PoleTerm`):
  `M(S)_rs = c_r/(1−w) + [r=s] 4 q^{2r+1} T_r`,
  `M(L)_rs = w c_r/(1−w) + [r=s] 4 q^{2r+1} T_{r+1}`,
  `M(D)_rs = w (c_r e_rs/(1−w) + 2 c_r w/(1−w)²) + [r=s] (−4)(r+½) q^{2r+1} T_{r+1}`,
  `e_rs = 11/2 − 2r` (`r = s`), `(3 − r − s) + 5/2` (`r ≠ s`).
* `block_SL`: for `γ ≠ κ`, `red E0(γ+ℓr, γ+ℓs) = x̄_γ q̄^{2γ} · red M(S or L)_rs`;
* `block_D`: `red E0(κ+ℓr, κ+ℓs) = red M(D)_rs`.
-/
import Chi2Irrational.NonVan.Blocks

namespace Chi2Irr

open Polynomial Finset

/-- `c_r = 1/c′_r`. -/
def crr (r : ℕ) : ℚ := if r = 1 then -1 else 1 / 2

lemma inv_cpr {r s c : ℕ} (p : Perm3 r s c) : 1 / cpr r s c = crr r := by
  rw [cpr_values p]; unfold crr; split_ifs <;> norm_num

/-- `e_rs`. -/
def eD (r s : ℕ) : ℚ := if r = s then 11 / 2 - 2 * r else ((3 - r - s : ℕ) : ℚ) + 5 / 2

/-- The block matrix of type S. -/
def MS (q : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun r s =>
  crr r / (1 - wt q) + if r = s then 4 * (q : ℚ) ^ (2 * (r : ℕ) + 1) * Tq q r else 0

/-- The block matrix of type L. -/
def ML (q : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun r s =>
  wt q * crr r / (1 - wt q) + if r = s then 4 * (q : ℚ) ^ (2 * (r : ℕ) + 1) * Tq q (r + 1) else 0

/-- The block matrix of type D. -/
def MD (q : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun r s =>
  wt q * (crr r * eD r s / (1 - wt q) + crr r * 2 * wt q / (1 - wt q) ^ 2) +
    if r = s then -4 * ((r : ℚ) + 1 / 2) * (q : ℚ) ^ (2 * (r : ℕ) + 1) * Tq q (r + 1) else 0

variable {q ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### Integrality and reductions of the ingredients -/

lemma crr_mem (hℓ2 : ℓ ≠ 2) (r : ℕ) : crr r ∈ Zl ℓ := by
  unfold crr; split_ifs
  · exact neg_mem (one_mem _)
  · rw [one_div]; exact inv_mem_Zl (padicNorm_two hℓ2)

lemma padicNorm_one_sub_wt (g : Good q ℓ) : padicNorm ℓ (1 - wt q) = 1 := by
  refine padicNorm_eq_one_of_red_ne_zero (sub_mem (one_mem _) (wt_mem g.hℓq)) ?_
  rw [red_sub (one_mem _) (wt_mem g.hℓq), red_one]
  exact one_sub_red_wt_ne_zero (by have := g.hq; omega) g.hℓq g.hℓq2

lemma Tq_mem (g : Good q ℓ) {n : ℕ} (hn : n ≤ 3) : Tq q n ∈ Zl ℓ := by
  unfold Tq
  refine sum_mem (fun u hu => ?_)
  have hu3 : u < 3 := by have := mem_range.mp hu; omega
  have hqn : padicNorm ℓ (q : ℚ) = 1 := padicNorm_natCast_q g.hℓq
  have hunit : padicNorm ℓ ((2 * (u : ℚ) + 1) ^ 2) = 1 := by
    rw [show (2 * (u : ℚ) + 1) = ((2 * u + 1 : ℕ) : ℚ) by push_cast; ring, padicNorm_pow,
      padicNorm_natCast_eq_one, one_pow]
    intro hd; have := Nat.le_of_dvd (by omega) hd; have := g.h7; omega
  rw [div_eq_mul_inv]
  exact mul_mem (pow_mem (by rw [one_div]; exact inv_mem_Zl hqn) _) (inv_mem_Zl hunit)

lemma red_pole_idx (hℓ2 : ℓ ≠ 2) (γ r : ℕ) : red ℓ (pole (idx ℓ γ r)) = red ℓ (pole γ) := by
  refine red_eq_of_sub (pole_mem_Zl hℓ2 _) (pole_mem_Zl hℓ2 _) ?_
  rw [pole_sub_pole]
  unfold idx
  have : ((γ : ℕ) : ℚ) - ((γ + ℓ * r : ℕ) : ℚ) = (ℓ : ℚ) * (((0 : ℤ) - r : ℤ) : ℚ) := by push_cast; ring
  rw [this, padicNorm.mul, padicNorm_self]
  calc (ℓ : ℚ)⁻¹ * padicNorm ℓ (((0 : ℤ) - r : ℤ) : ℚ) ≤ (ℓ : ℚ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (padicNorm.of_int _) ell_inv_pos.le
    _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt)

lemma q_pow_two_kap (g : Good q ℓ) : (q : ZMod ℓ) ^ (2 * kap ℓ) = 1 := by
  have hk := two_kap_add_one (hℓ := hℓ) g.ne_two
  rw [show 2 * kap ℓ = ℓ - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one (red_q_ne_zero g.hℓq)

/-- Reduction of `c/(1 − w)` and `c/(1 − w)²`. -/
lemma red_div_one_sub_wt (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) :
    red ℓ (x / (1 - wt q)) = red ℓ x / (1 - red ℓ (wt q)) := by
  rw [red_div hx (padicNorm_one_sub_wt g), red_sub (one_mem _) (wt_mem g.hℓq), red_one]

lemma red_div_one_sub_wt_sq (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) :
    red ℓ (x / (1 - wt q) ^ 2) = red ℓ x / (1 - red ℓ (wt q)) ^ 2 := by
  have h2 : padicNorm ℓ ((1 - wt q) ^ 2) = 1 := by rw [padicNorm_pow, padicNorm_one_sub_wt g, one_pow]
  rw [red_div hx h2, red_pow (sub_mem (one_mem _) (wt_mem g.hℓq)),
    red_sub (one_mem _) (wt_mem g.hℓq), red_one]

lemma one_sub_wt_inv_mem (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) : x / (1 - wt q) ∈ Zl ℓ := by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem_Zl (padicNorm_one_sub_wt g))

lemma one_sub_wt_sq_inv_mem (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) : x / (1 - wt q) ^ 2 ∈ Zl ℓ := by
  rw [div_eq_mul_inv]
  refine mul_mem hx (inv_mem_Zl ?_)
  rw [padicNorm_pow, padicNorm_one_sub_wt g, one_pow]

lemma poleblock_mem (g : Good q ℓ) (r : ℕ) {n : ℕ} (hn : n ≤ 3) :
    4 * (q : ℚ) ^ (2 * r + 1) * Tq q n ∈ Zl ℓ :=
  mul_mem (mul_mem (by exact_mod_cast natCast_mem_Zl 4) (pow_mem (natCast_mem_Zl q) _)) (Tq_mem g hn)

lemma red_poleblock (g : Good q ℓ) (r : ℕ) {n : ℕ} (hn : n ≤ 3) :
    red ℓ (4 * (q : ℚ) ^ (2 * r + 1) * Tq q n) = 4 * (q : ZMod ℓ) ^ (2 * r + 1) * red ℓ (Tq q n) := by
  rw [red_mul (mul_mem (by exact_mod_cast natCast_mem_Zl 4) (pow_mem (natCast_mem_Zl q) _)) (Tq_mem g hn),
    red_mul (by exact_mod_cast natCast_mem_Zl 4) (pow_mem (natCast_mem_Zl q) _),
    red_pow (natCast_mem_Zl q), red_natCast]
  have := red_natCast (ℓ := ℓ) 4
  push_cast at this
  rw [this]

/-! ### The blocks -/

lemma perm_of_ne {r s : ℕ} (hr : r < 3) (hs : s < 3) (hrs : r ≠ s) : Perm3 r s (3 - r - s) :=
  ⟨hr, hs, by omega, hrs, by omega, by omega⟩

lemma pole_div_cpr {r s c : ℕ} (p : Perm3 r s c) (x : ℚ) : x / cpr r s c = x * crr r := by
  rw [← inv_cpr p, mul_one_div]

/-- The raw form of an S/L block entry. -/
lemma block_SL_raw (g : Good q ℓ) {γ : ℕ} (hγ : γ < ℓ) (hk : γ ≠ kap ℓ) {r s : ℕ} (hr : r < 3)
    (hs : s < 3) :
    red ℓ (E0 q ℓ (idx ℓ γ r) (idx ℓ γ s)) =
      (q : ZMod ℓ) ^ (2 * γ) * (if γ < kap ℓ then 1 else red ℓ (wt q)) *
          (red ℓ (pole γ) * red ℓ (crr r) / (1 - red ℓ (wt q))) +
        if r = s then 4 * red ℓ (pole γ) * (q : ZMod ℓ) ^ (2 * γ) * (q : ZMod ℓ) ^ (2 * r + 1) *
          red ℓ (Tq q (if γ < kap ℓ then r else r + 1)) else 0 := by
  have hℓ2 := g.ne_two
  have hi : idx ℓ γ r < 3 * ℓ := idx_lt hγ hr
  have hpowt := red_wt_pow_t0 g hγ
  have hmodi : idx ℓ γ r % ℓ = γ := idx_mod hγ
  have hcrr := crr_mem (ℓ := ℓ) hℓ2 r
  by_cases hrs : r = s
  · subst hrs
    obtain ⟨s', c, p⟩ := exists_perm hr
    have hc₀ : pole (idx ℓ γ r) / cpr r s' c ∈ Zl ℓ := by
      rw [pole_div_cpr p]; exact mul_mem (pole_mem_Zl hℓ2 _) hcrr
    have hser := series_const g hγ (nu ℓ (idx ℓ γ r) (idx ℓ γ r)) (Qpoly (3 * ℓ) (idx ℓ γ r)) hc₀
      (fun t => nuQ_le_one g hi t)
      (fun γ' t hγ' ht hne => nuQ_small_offprog hℓ2 hγ' ht hi (by rw [hmodi]; exact fun h => hne h.symm))
      (fun t ht => resid_diag_SL hℓ2 hγ p ht hk)
    obtain ⟨hSmem, hSred⟩ := red_ell_sq_Spart g.h7 g.hℓq hγ hr
    have hμmem : nu ℓ (idx ℓ γ r) (idx ℓ γ r) * muPoly (wt q) (Qpoly (3 * ℓ) (idx ℓ γ r)) ∈ Zl ℓ :=
      padicNorm_mul_muPoly_le g.hq g.hℓq g.hℓq2 _ _ zero_le_one (fun t _ => nuQ_le_one g hi t)
    have hpole : (if idx ℓ γ r % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) *
        (4 * pole (idx ℓ γ r) * Spart q (idx ℓ γ r)) =
        4 * pole (idx ℓ γ r) * ((ℓ : ℚ) ^ 2 * Spart q (idx ℓ γ r)) := by
      rw [ite_eq_right (by rw [hmodi]; exact hk)]; ring
    have h4 : (4 : ℚ) ∈ Zl ℓ := by exact_mod_cast natCast_mem_Zl 4
    have h4m : 4 * pole (idx ℓ γ r) ∈ Zl ℓ := mul_mem h4 (pole_mem_Zl hℓ2 _)
    rw [E0_diag_eq hi, red_add hμmem (poleTerm_mem g hi), hser, hpole, red_mul h4m hSmem,
      red_mul h4 (pole_mem_Zl hℓ2 _), hSred, pole_div_cpr p, red_mul (pole_mem_Zl hℓ2 _) hcrr,
      red_pole_idx hℓ2, hpowt, ite_eq_left rfl]
    have := red_natCast (ℓ := ℓ) 4
    push_cast at this
    rw [this]
    ring
  · have p := perm_of_ne hr hs hrs
    have hj : idx ℓ γ s < 3 * ℓ := idx_lt hγ hs
    have hij : idx ℓ γ r ≠ idx ℓ γ s := idx_ne hrs
    have hc₀ : pole (idx ℓ γ r) / cpr r s (3 - r - s) ∈ Zl ℓ := by
      rw [pole_div_cpr p]; exact mul_mem (pole_mem_Zl hℓ2 _) hcrr
    have hser := series_const g hγ (nu ℓ (idx ℓ γ r) (idx ℓ γ s))
      (Fpoly (3 * ℓ) (idx ℓ γ r) (idx ℓ γ s)) hc₀
      (fun t => nuF_le_one hℓ2 hi hj hij t)
      (fun γ' t hγ' ht hne => nuF_small_offprog hℓ2 hγ' ht hi hj hij
        (by rw [hmodi, idx_mod hγ]) (by rw [hmodi]; exact fun h => hne h.symm))
      (fun t ht => resid_off_SL hℓ2 hγ p ht hk)
    rw [E0_offdiag_eq hi hj hij, hser, pole_div_cpr p, red_mul (pole_mem_Zl hℓ2 _) hcrr,
      red_pole_idx hℓ2, hpowt, ite_eq_right hrs, add_zero]
    try ring

/-- **The S/L blocks.** `red E0(γ+ℓr, γ+ℓs) = x̄_γ q̄^{2γ} · red M(type)_rs`. -/
theorem block_SL (g : Good q ℓ) {γ : ℕ} (hγ : γ < ℓ) (hk : γ ≠ kap ℓ) (r s : Fin 3) :
    red ℓ (E0 q ℓ (idx ℓ γ r) (idx ℓ γ s)) =
      red ℓ (pole γ) * (q : ZMod ℓ) ^ (2 * γ) *
        red ℓ ((if γ < kap ℓ then MS q else ML q) r s) := by
  have hℓ2 := g.ne_two
  have hr := r.isLt
  have hs := s.isLt
  rw [block_SL_raw g hγ hk hr hs]
  have hcrr := crr_mem (ℓ := ℓ) hℓ2 r
  have hw := wt_mem (ℓ := ℓ) g.hℓq
  by_cases hS : γ < kap ℓ
  · simp only [ite_eq_left hS, MS]
    have hA := one_sub_wt_inv_mem g hcrr
    by_cases hrs : r = s
    · subst hrs
      simp only [↓reduceIte]
      rw [red_add hA (poleblock_mem g r (n := (r : ℕ)) (by omega)), red_div_one_sub_wt g hcrr,
        red_poleblock g r (n := (r : ℕ)) (by omega)]
      ring
    · have hrs' : (r : ℕ) ≠ s := fun h => hrs (Fin.ext h)
      simp only [ite_eq_right hrs, ite_eq_right hrs', add_zero]
      rw [red_div_one_sub_wt g hcrr]
      ring
  · simp only [ite_eq_right hS, ML]
    have hwc : wt q * crr r ∈ Zl ℓ := mul_mem hw hcrr
    have hA := one_sub_wt_inv_mem g hwc
    by_cases hrs : r = s
    · subst hrs
      simp only [↓reduceIte]
      rw [red_add hA (poleblock_mem g r (n := (r : ℕ) + 1) (by omega)), red_div_one_sub_wt g hwc,
        red_mul hw hcrr, red_poleblock g r (n := (r : ℕ) + 1) (by omega)]
      ring
    · have hrs' : (r : ℕ) ≠ s := fun h => hrs (Fin.ext h)
      simp only [ite_eq_right hrs, ite_eq_right hrs', add_zero]
      rw [red_div_one_sub_wt g hwc, red_mul hw hcrr]
      ring

lemma t0_kap (hℓ2 : ℓ ≠ 2) : t0 ℓ (kap ℓ) = ℓ := by
  unfold t0; simp

lemma eD_mem (hℓ2 : ℓ ≠ 2) (r s : ℕ) : eD r s ∈ Zl ℓ := by
  have h52 : (5 / 2 : ℚ) ∈ Zl ℓ := by
    rw [div_eq_mul_inv]
    exact mul_mem (by exact_mod_cast natCast_mem_Zl 5) (inv_mem_Zl (padicNorm_two hℓ2))
  unfold eD; split_ifs
  · have : (11 / 2 - 2 * (r : ℚ)) = 11 / 2 - ((2 * r : ℕ) : ℚ) := by push_cast; ring
    rw [this]
    refine sub_mem ?_ (natCast_mem_Zl _)
    rw [div_eq_mul_inv]
    exact mul_mem (by exact_mod_cast natCast_mem_Zl 11) (inv_mem_Zl (padicNorm_two hℓ2))
  · exact add_mem (natCast_mem_Zl _) h52

lemma cast_t0_add (hℓ2 : ℓ ≠ 2) (j : ℕ) :
    (((t0 ℓ (kap ℓ) + ℓ * j : ℕ)) : ℚ) = (ℓ : ℚ) * (1 + j) := by
  rw [t0_kap hℓ2]; push_cast; ring

/-- **The D block.** `red E0(κ+ℓr, κ+ℓs) = red M(D)_rs`. -/
theorem block_D (g : Good q ℓ) (r s : Fin 3) :
    red ℓ (E0 q ℓ (idx ℓ (kap ℓ) r) (idx ℓ (kap ℓ) s)) = red ℓ (MD q r s) := by
  have hℓ2 := g.ne_two
  have hk2 := two_kap_add_one (hℓ := hℓ) hℓ2
  have hγ : kap ℓ < ℓ := by omega
  have hr := r.isLt
  have hs := s.isLt
  have hi : idx ℓ (kap ℓ) r < 3 * ℓ := idx_lt hγ hr
  have hmodi : idx ℓ (kap ℓ) r % ℓ = kap ℓ := idx_mod hγ
  have hpowt := red_wt_pow_t0 g hγ
  rw [ite_eq_right (lt_irrefl _), q_pow_two_kap g, one_mul] at hpowt
  have hcrr := crr_mem (ℓ := ℓ) hℓ2 r
  have hw := wt_mem (ℓ := ℓ) g.hℓq
  have h2 : (2 : ℚ) ∈ Zl ℓ := by exact_mod_cast natCast_mem_Zl 2
  have hc₀ : eD r s * crr r ∈ Zl ℓ := mul_mem (eD_mem hℓ2 r s) hcrr
  have hc₁ : 2 * crr r ∈ Zl ℓ := mul_mem h2 hcrr
  -- the series part of `M(D)`
  have hMser : red ℓ (wt q * (crr r * eD r s / (1 - wt q) + crr r * 2 * wt q / (1 - wt q) ^ 2)) =
      red ℓ (wt q) * (red ℓ (eD r s * crr r) / (1 - red ℓ (wt q)) +
        red ℓ (2 * crr r) * red ℓ (wt q) / (1 - red ℓ (wt q)) ^ 2) := by
    have hA := one_sub_wt_inv_mem g (mul_mem hcrr (eD_mem hℓ2 r s))
    have hB := one_sub_wt_sq_inv_mem g (mul_mem (mul_mem hcrr h2) hw)
    rw [red_mul hw (add_mem hA hB), red_add hA hB, red_div_one_sub_wt g (mul_mem hcrr (eD_mem hℓ2 r s)),
      red_div_one_sub_wt_sq g (mul_mem (mul_mem hcrr h2) hw), red_mul (mul_mem hcrr h2) hw,
      red_mul hcrr (eD_mem hℓ2 r s), red_mul hcrr h2, red_mul (eD_mem hℓ2 r s) hcrr, red_mul h2 hcrr]
    ring
  by_cases hrs : (r : ℕ) = s
  · have hrs' : r = s := Fin.ext hrs
    subst hrs'
    obtain ⟨s', c, p⟩ := exists_perm hr
    have hsum := p.sum
    have hser := series_lin g hγ (nu ℓ (idx ℓ (kap ℓ) r) (idx ℓ (kap ℓ) r))
      (Qpoly (3 * ℓ) (idx ℓ (kap ℓ) r)) hc₀ hc₁
      (fun t => nuQ_le_one g hi t)
      (fun γ' t hγ' ht hne => nuQ_small_offprog hℓ2 hγ' ht hi (by rw [hmodi]; exact fun h => hne h.symm))
      (fun j => by
        obtain ⟨hm, hred⟩ := resid_diag_D hℓ2 hγ p (t0_dvd hℓ2 hγ j) rfl
        refine ⟨hm, ?_⟩
        rw [hred]
        congr 1
        rw [cast_t0_add hℓ2, pole_idx_kap hℓ2, pole_idx_kap hℓ2, pole_idx_kap hℓ2, pole_div_cpr p]
        unfold eD
        rw [ite_eq_left rfl]
        have hsc : (s' : ℚ) + c = 3 - r := by
          have : ((r + s' + c : ℕ) : ℚ) = 3 := by rw [hsum]; norm_num
          push_cast at this; linarith
        field_simp [ell_pos.ne']
        linear_combination (2 * crr r) * hsc)
    obtain ⟨hSmem, hSred⟩ := red_ell_sq_Spart g.h7 g.hℓq hγ hr
    rw [ite_eq_right (lt_irrefl _), q_pow_two_kap g, one_mul] at hSred
    have hμmem : nu ℓ (idx ℓ (kap ℓ) r) (idx ℓ (kap ℓ) r) *
        muPoly (wt q) (Qpoly (3 * ℓ) (idx ℓ (kap ℓ) r)) ∈ Zl ℓ :=
      padicNorm_mul_muPoly_le g.hq g.hℓq g.hℓq2 _ _ zero_le_one (fun t _ => nuQ_le_one g hi t)
    have hhalf := half_add_mem (ℓ := ℓ) hℓ2 r
    have hpole : (if idx ℓ (kap ℓ) r % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) *
        (4 * pole (idx ℓ (kap ℓ) r) * Spart q (idx ℓ (kap ℓ) r)) =
        (-4 * ((r : ℚ) + 1 / 2)) * ((ℓ : ℚ) ^ 2 * Spart q (idx ℓ (kap ℓ) r)) := by
      rw [ite_eq_left hmodi, pole_idx_kap hℓ2]; ring
    have h4 : (-4 * ((r : ℚ) + 1 / 2)) ∈ Zl ℓ :=
      mul_mem (neg_mem (by exact_mod_cast natCast_mem_Zl 4)) hhalf
    rw [E0_diag_eq hi, red_add hμmem (poleTerm_mem g hi), hser, hpole, red_mul h4 hSmem, hSred,
      hpowt]
    -- the right-hand side
    unfold MD
    simp only [↓reduceIte]
    have hTm := Tq_mem g (n := (r : ℕ) + 1) (by omega)
    have hpb : -4 * ((r : ℚ) + 1 / 2) * (q : ℚ) ^ (2 * (r : ℕ) + 1) * Tq q ((r : ℕ) + 1) ∈ Zl ℓ :=
      mul_mem (mul_mem h4 (pow_mem (natCast_mem_Zl q) _)) hTm
    have hA := one_sub_wt_inv_mem g (mul_mem hcrr (eD_mem hℓ2 r r))
    have hB := one_sub_wt_sq_inv_mem g (mul_mem (mul_mem hcrr h2) hw)
    rw [red_add (mul_mem hw (add_mem hA hB)) hpb, hMser,
      red_mul (mul_mem h4 (pow_mem (natCast_mem_Zl q) _)) hTm, red_mul h4 (pow_mem (natCast_mem_Zl q) _),
      red_pow (natCast_mem_Zl q), red_natCast]
    ring
  · have p := perm_of_ne hr hs hrs
    have hj : idx ℓ (kap ℓ) s < 3 * ℓ := idx_lt hγ hs
    have hij : idx ℓ (kap ℓ) r ≠ idx ℓ (kap ℓ) s := idx_ne hrs
    have hser := series_lin g hγ (nu ℓ (idx ℓ (kap ℓ) r) (idx ℓ (kap ℓ) s))
      (Fpoly (3 * ℓ) (idx ℓ (kap ℓ) r) (idx ℓ (kap ℓ) s)) hc₀ hc₁
      (fun t => nuF_le_one hℓ2 hi hj hij t)
      (fun γ' t hγ' ht hne => nuF_small_offprog hℓ2 hγ' ht hi hj hij
        (by rw [hmodi, idx_mod hγ]) (by rw [hmodi]; exact fun h => hne h.symm))
      (fun j => by
        obtain ⟨hm, hred⟩ := resid_off_D hℓ2 hγ p (t0_dvd hℓ2 hγ j) rfl
        refine ⟨hm, ?_⟩
        rw [hred]
        congr 1
        rw [cast_t0_add hℓ2, pole_idx_kap hℓ2, pole_div_cpr p]
        unfold eD
        rw [ite_eq_right hrs]
        have hc : ((3 - r - s : ℕ) : ℚ) = (3 - r - s : ℕ) := rfl
        field_simp [ell_pos.ne']
        ring)
    rw [E0_offdiag_eq hi hj hij, hser, hpowt]
    unfold MD
    have hrs2 : r ≠ s := fun h => hrs (congrArg Fin.val h)
    simp only [ite_eq_right hrs2, add_zero]
    rw [hMser]

end Chi2Irr
