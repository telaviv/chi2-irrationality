/-
# Lemma P for Ti along `K = 3ℓ`: the blocks are `λ_γ · M̄(type)`

Copy of `NonVan/BlockMat.lean` for the Ti machine. The ℓ-independent rational block matrices
(`c_r = 1/2, −1, 1/2`, `w = −q⁻²`, `T♮_n` as in `TiQ/NonVan/PoleTerm`):
  `M(S)_rs = c_r/(1−w) + [r=s] 4 (−1)^r q^{2r+1} T♮_r`,
  `M(L)_rs = w c_r/(1−w) + [r=s] 4 (−1)^r q^{2r+1} T♮_{r+1}`,
  `M(D)_rs = w (c_r e_rs/(1−w) + 2 c_r w/(1−w)²) + [r=s] (−4)(r+½) (−1)^r q^{2r+1} T♮_{r+1}`,
  `e_rs = 11/2 − 2r` (`r = s`), `(3 − r − s) + 5/2` (`r ≠ s`).
* `block_SL`: for `γ ≠ κ`, `red E0(γ+ℓr, γ+ℓs) = x̄_γ (−1)^{κ+γ} q̄^{2γ} · red M(S or L)_rs`;
* `block_D`: `red E0(κ+ℓr, κ+ℓs) = red M(D)_rs`.
These are RESULT §5 (F4): the S and L blocks pick up the unit `χ₄(ℓ)(−1)^γ = (−1)^{κ+γ}`, and in the D block the two
signs cancel. Checked against exact data (`scripts/tiq/nonvan_blocks.py`: the reduced `E0` blocks at
`q ∈ {3, 4, 6, 7}`, `ℓ ∈ {7, 11}`, 0 mismatches). The generic `crr`, `eD`, `inv_cpr`, `perm_of_ne`, `pole_div_cpr`,
`crr_mem`, `eD_mem`, `red_pole_idx`, `t0_kap`, `cast_t0_add` are reused.
-/
import Chi2Irrational.TiQ.NonVan.Blocks
import Chi2Irrational.NonVan.BlockMat

namespace Chi2Irr
namespace TiQ

open Polynomial Finset

/-- The block matrix of type S. -/
def MS (q : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun r s =>
  crr r / (1 - wT q) + if r = s then 4 * (-1 : ℚ) ^ (r : ℕ) * (q : ℚ) ^ (2 * (r : ℕ) + 1) * TqT q r else 0

/-- The block matrix of type L. -/
def ML (q : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun r s =>
  wT q * crr r / (1 - wT q) +
    if r = s then 4 * (-1 : ℚ) ^ (r : ℕ) * (q : ℚ) ^ (2 * (r : ℕ) + 1) * TqT q (r + 1) else 0

/-- The block matrix of type D. -/
def MD (q : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun r s =>
  wT q * (crr r * eD r s / (1 - wT q) + crr r * 2 * wT q / (1 - wT q) ^ 2) +
    if r = s then -4 * ((r : ℚ) + 1 / 2) * (-1 : ℚ) ^ (r : ℕ) * (q : ℚ) ^ (2 * (r : ℕ) + 1) * TqT q (r + 1)
    else 0

variable {q ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### Integrality and reductions of the ingredients -/

lemma padicNorm_one_sub_wt (g : Good q ℓ) : padicNorm ℓ (1 - wT q) = 1 := by
  refine padicNorm_eq_one_of_red_ne_zero (sub_mem (one_mem _) (wt_mem g.hℓq)) ?_
  rw [red_sub (one_mem _) (wt_mem g.hℓq), red_one]
  exact one_sub_red_wt_ne_zero g.hℓq g.hℓq2

lemma Tq_mem (g : Good q ℓ) {n : ℕ} (hn : n ≤ 3) : TqT q n ∈ Zl ℓ := by
  unfold TqT
  refine sum_mem (fun u hu => ?_)
  have hu3 : u < 3 := by have := mem_range.mp hu; omega
  have hqn : padicNorm ℓ (q : ℚ) = 1 := padicNorm_natCast_q g.hℓq
  have hunit : padicNorm ℓ ((2 * (u : ℚ) + 1) ^ 2) = 1 := by
    rw [show (2 * (u : ℚ) + 1) = ((2 * u + 1 : ℕ) : ℚ) by push_cast; ring, padicNorm_pow,
      padicNorm_natCast_eq_one, one_pow]
    intro hd; have := Nat.le_of_dvd (by omega) hd; have := g.h7; omega
  rw [div_eq_mul_inv]
  exact mul_mem (mul_mem (neg_one_pow_mem _) (pow_mem (by rw [one_div]; exact inv_mem_Zl hqn) _))
    (inv_mem_Zl hunit)

lemma q_pow_two_kap (g : Good q ℓ) : (q : ZMod ℓ) ^ (2 * kap ℓ) = 1 := by
  have hk := two_kap_add_one (hℓ := hℓ) g.ne_two
  rw [show 2 * kap ℓ = ℓ - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one (red_q_ne_zero g.hℓq)

lemma neg_one_pow_kap_add_kap : (-1 : ZMod ℓ) ^ (kap ℓ + kap ℓ) = 1 := by
  rw [← two_mul, pow_mul]; simp

/-- Reduction of `c/(1 − w)` and `c/(1 − w)²`. -/
lemma red_div_one_sub_wt (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) :
    red ℓ (x / (1 - wT q)) = red ℓ x / (1 - red ℓ (wT q)) := by
  rw [red_div hx (padicNorm_one_sub_wt g), red_sub (one_mem _) (wt_mem g.hℓq), red_one]

lemma red_div_one_sub_wt_sq (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) :
    red ℓ (x / (1 - wT q) ^ 2) = red ℓ x / (1 - red ℓ (wT q)) ^ 2 := by
  have h2 : padicNorm ℓ ((1 - wT q) ^ 2) = 1 := by rw [padicNorm_pow, padicNorm_one_sub_wt g, one_pow]
  rw [red_div hx h2, red_pow (sub_mem (one_mem _) (wt_mem g.hℓq)),
    red_sub (one_mem _) (wt_mem g.hℓq), red_one]

lemma one_sub_wt_inv_mem (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) : x / (1 - wT q) ∈ Zl ℓ := by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem_Zl (padicNorm_one_sub_wt g))

lemma one_sub_wt_sq_inv_mem (g : Good q ℓ) {x : ℚ} (hx : x ∈ Zl ℓ) : x / (1 - wT q) ^ 2 ∈ Zl ℓ := by
  rw [div_eq_mul_inv]
  refine mul_mem hx (inv_mem_Zl ?_)
  rw [padicNorm_pow, padicNorm_one_sub_wt g, one_pow]

lemma poleblock_mem (g : Good q ℓ) (r : ℕ) {n : ℕ} (hn : n ≤ 3) :
    4 * (-1 : ℚ) ^ r * (q : ℚ) ^ (2 * r + 1) * TqT q n ∈ Zl ℓ :=
  mul_mem (mul_mem (mul_mem (by exact_mod_cast natCast_mem_Zl 4) (neg_one_pow_mem _))
    (pow_mem (natCast_mem_Zl q) _)) (Tq_mem g hn)

lemma red_poleblock (g : Good q ℓ) (r : ℕ) {n : ℕ} (hn : n ≤ 3) :
    red ℓ (4 * (-1 : ℚ) ^ r * (q : ℚ) ^ (2 * r + 1) * TqT q n) =
      4 * (-1 : ZMod ℓ) ^ r * (q : ZMod ℓ) ^ (2 * r + 1) * red ℓ (TqT q n) := by
  have h4 : (4 : ℚ) ∈ Zl ℓ := by exact_mod_cast natCast_mem_Zl 4
  rw [red_mul (mul_mem (mul_mem h4 (neg_one_pow_mem _)) (pow_mem (natCast_mem_Zl q) _)) (Tq_mem g hn),
    red_mul (mul_mem h4 (neg_one_pow_mem _)) (pow_mem (natCast_mem_Zl q) _),
    red_mul h4 (neg_one_pow_mem _), red_neg_one_pow, red_pow (natCast_mem_Zl q), red_natCast]
  have := red_natCast (ℓ := ℓ) 4
  push_cast at this
  rw [this]

/-! ### The blocks -/

/-- The raw form of an S/L block entry. -/
lemma block_SL_raw (g : Good q ℓ) {γ : ℕ} (hγ : γ < ℓ) (hk : γ ≠ kap ℓ) {r s : ℕ} (hr : r < 3)
    (hs : s < 3) :
    red ℓ (E0 q ℓ (idx ℓ γ r) (idx ℓ γ s)) =
      (-1 : ZMod ℓ) ^ (kap ℓ + γ) * (q : ZMod ℓ) ^ (2 * γ) * (if γ < kap ℓ then 1 else red ℓ (wT q)) *
          (red ℓ (pole γ) * red ℓ (crr r) / (1 - red ℓ (wT q))) +
        if r = s then 4 * red ℓ (pole γ) * ((-1 : ZMod ℓ) ^ (kap ℓ + γ) * (q : ZMod ℓ) ^ (2 * γ) *
          ((-1 : ZMod ℓ) ^ r * (q : ZMod ℓ) ^ (2 * r + 1)) *
          red ℓ (TqT q (if γ < kap ℓ then r else r + 1))) else 0 := by
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
    have hμmem : nu ℓ (idx ℓ γ r) (idx ℓ γ r) * muPoly (wT q) (Qpoly (3 * ℓ) (idx ℓ γ r)) ∈ Zl ℓ :=
      padicNorm_mul_muPoly_le g.hq g.hℓq g.hℓq2 _ _ zero_le_one (fun t _ => nuQ_le_one g hi t)
    have hpole : (if idx ℓ γ r % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) *
        (4 * pole (idx ℓ γ r) * SpartT q (idx ℓ γ r)) =
        4 * pole (idx ℓ γ r) * ((ℓ : ℚ) ^ 2 * SpartT q (idx ℓ γ r)) := by
      rw [ite_eq_right (by rw [hmodi]; exact hk)]; ring
    have h4 : (4 : ℚ) ∈ Zl ℓ := by exact_mod_cast natCast_mem_Zl 4
    have h4m : 4 * pole (idx ℓ γ r) ∈ Zl ℓ := mul_mem h4 (pole_mem_Zl hℓ2 _)
    rw [E0_diag_eq hi, red_add hμmem (poleTerm_mem g hi), hser, hpole, red_mul h4m hSmem,
      red_mul h4 (pole_mem_Zl hℓ2 _), hSred, pole_div_cpr p, red_mul (pole_mem_Zl hℓ2 _) hcrr,
      red_pole_idx hℓ2, hpowt, ite_eq_left rfl]
    have := red_natCast (ℓ := ℓ) 4
    push_cast at this
    rw [this]
    try ring
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

/-- **The S/L blocks.** `red E0(γ+ℓr, γ+ℓs) = x̄_γ (−1)^{κ+γ} q̄^{2γ} · red M(type)_rs`. -/
theorem block_SL (g : Good q ℓ) {γ : ℕ} (hγ : γ < ℓ) (hk : γ ≠ kap ℓ) (r s : Fin 3) :
    red ℓ (E0 q ℓ (idx ℓ γ r) (idx ℓ γ s)) =
      red ℓ (pole γ) * (-1 : ZMod ℓ) ^ (kap ℓ + γ) * (q : ZMod ℓ) ^ (2 * γ) *
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
    have hwc : wT q * crr r ∈ Zl ℓ := mul_mem hw hcrr
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
  rw [ite_eq_right (lt_irrefl _), q_pow_two_kap g, neg_one_pow_kap_add_kap] at hpowt
  simp only [one_mul] at hpowt
  have hcrr := crr_mem (ℓ := ℓ) hℓ2 r
  have hw := wt_mem (ℓ := ℓ) g.hℓq
  have h2 : (2 : ℚ) ∈ Zl ℓ := by exact_mod_cast natCast_mem_Zl 2
  have hc₀ : eD r s * crr r ∈ Zl ℓ := mul_mem (eD_mem hℓ2 r s) hcrr
  have hc₁ : 2 * crr r ∈ Zl ℓ := mul_mem h2 hcrr
  -- the series part of `M(D)`
  have hMser : red ℓ (wT q * (crr r * eD r s / (1 - wT q) + crr r * 2 * wT q / (1 - wT q) ^ 2)) =
      red ℓ (wT q) * (red ℓ (eD r s * crr r) / (1 - red ℓ (wT q)) +
        red ℓ (2 * crr r) * red ℓ (wT q) / (1 - red ℓ (wT q)) ^ 2) := by
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
    rw [ite_eq_right (lt_irrefl _), q_pow_two_kap g, neg_one_pow_kap_add_kap] at hSred
    simp only [one_mul] at hSred
    have hμmem : nu ℓ (idx ℓ (kap ℓ) r) (idx ℓ (kap ℓ) r) *
        muPoly (wT q) (Qpoly (3 * ℓ) (idx ℓ (kap ℓ) r)) ∈ Zl ℓ :=
      padicNorm_mul_muPoly_le g.hq g.hℓq g.hℓq2 _ _ zero_le_one (fun t _ => nuQ_le_one g hi t)
    have hhalf := half_add_mem (ℓ := ℓ) hℓ2 r
    have hpole : (if idx ℓ (kap ℓ) r % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) *
        (4 * pole (idx ℓ (kap ℓ) r) * SpartT q (idx ℓ (kap ℓ) r)) =
        (-4 * ((r : ℚ) + 1 / 2)) * ((ℓ : ℚ) ^ 2 * SpartT q (idx ℓ (kap ℓ) r)) := by
      rw [ite_eq_left hmodi, pole_idx_kap hℓ2]; ring
    have h4 : (-4 * ((r : ℚ) + 1 / 2)) ∈ Zl ℓ :=
      mul_mem (neg_mem (by exact_mod_cast natCast_mem_Zl 4)) hhalf
    rw [E0_diag_eq hi, red_add hμmem (poleTerm_mem g hi), hser, hpole, red_mul h4 hSmem, hSred,
      hpowt]
    -- the right-hand side
    unfold MD
    simp only [↓reduceIte]
    have hTm := Tq_mem g (n := (r : ℕ) + 1) (by omega)
    have h4s : -4 * ((r : ℚ) + 1 / 2) * (-1 : ℚ) ^ (r : ℕ) ∈ Zl ℓ := mul_mem h4 (neg_one_pow_mem _)
    have hpb : -4 * ((r : ℚ) + 1 / 2) * (-1 : ℚ) ^ (r : ℕ) * (q : ℚ) ^ (2 * (r : ℕ) + 1) *
        TqT q ((r : ℕ) + 1) ∈ Zl ℓ :=
      mul_mem (mul_mem h4s (pow_mem (natCast_mem_Zl q) _)) hTm
    have hA := one_sub_wt_inv_mem g (mul_mem hcrr (eD_mem hℓ2 r r))
    have hB := one_sub_wt_sq_inv_mem g (mul_mem (mul_mem hcrr h2) hw)
    rw [red_add (mul_mem hw (add_mem hA hB)) hpb, hMser,
      red_mul (mul_mem h4s (pow_mem (natCast_mem_Zl q) _)) hTm,
      red_mul h4s (pow_mem (natCast_mem_Zl q) _), red_mul h4 (neg_one_pow_mem _), red_neg_one_pow,
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

end TiQ
end Chi2Irr
