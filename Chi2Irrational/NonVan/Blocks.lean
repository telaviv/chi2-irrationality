/-
# Lemma P along `K = 3ℓ`: the normalised entries `E0_ij = ν_ij A(f_i f_j)`

Under `Good q ℓ` (`q ≥ 2`, `ℓ ≥ 7` prime, `ℓ ∤ q(q²−1)`):
* `E0_mem`: every `E0_ij` is ℓ-integral;
* `E0_offclass`: `red E0_ij = 0` if `class i ≠ class j` and `class j ≠ κ`;
* `E0_series_SL`, `E0_series_D`: the series part of an entry of the block of `γ` (from `red_mul_muPoly` and the
  residues), with `t₀(γ)` the least `t ≥ 1` on the progression of `γ`.
-/
import Chi2Irrational.NonVan.PoleTerm

namespace Chi2Irr

open Polynomial Finset

/-- Standing hypotheses on `(q, ℓ)`. -/
structure Good (q ℓ : ℕ) : Prop where
  hq : 2 ≤ q
  h7 : 7 ≤ ℓ
  hℓq : ¬ ℓ ∣ q
  hℓq2 : ¬ ℓ ∣ q ^ 2 - 1

variable {q ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma Good.ne_two (g : Good q ℓ) : ℓ ≠ 2 := by have := g.h7; omega

/-- The normalised entry `E0_ij = ν_ij A(f_i f_j)` for `K = 3ℓ`. -/
noncomputable def E0 (q ℓ i j : ℕ) : ℚ :=
  nu ℓ i j * Afun q (3 * ℓ) (fpoly (3 * ℓ) i * fpoly (3 * ℓ) j)

/-- The least `t ≥ 1` on the progression of `γ`. -/
def t0 (ℓ γ : ℕ) : ℕ := if γ < kap ℓ then kap ℓ - γ else if γ = kap ℓ then ℓ else kap ℓ + ℓ - γ

lemma t0_facts (hℓ2 : ℓ ≠ 2) {γ : ℕ} (hγ : γ < ℓ) :
    1 ≤ t0 ℓ γ ∧ t0 ℓ γ ≤ ℓ ∧
      2 * t0 ℓ γ + 2 * γ + 1 = ℓ * (if γ < kap ℓ then 1 else 3) := by
  have hk := two_kap_add_one (hℓ := hℓ) hℓ2
  unfold t0
  split_ifs <;> omega

lemma t0_dvd (hℓ2 : ℓ ≠ 2) {γ : ℕ} (hγ : γ < ℓ) (j : ℕ) :
    ℓ ∣ 2 * (t0 ℓ γ + ℓ * j) + 2 * γ + 1 := by
  obtain ⟨-, -, h⟩ := t0_facts (hℓ := hℓ) hℓ2 hγ
  have : 2 * (t0 ℓ γ + ℓ * j) + 2 * γ + 1 = ℓ * ((if γ < kap ℓ then 1 else 3) + 2 * j) := by
    split_ifs at h ⊢ <;> linarith
  rw [this]; exact dvd_mul_right _ _

/-- Points with the same residue as `t₀(γ)` are exactly those on the progression of `γ`. -/
lemma prog_of_mod_ne (hℓ2 : ℓ ≠ 2) {γ γ' t : ℕ} (hγ : γ < ℓ) (ht : ℓ ∣ 2 * t + 2 * γ' + 1)
    (hmod : t % ℓ ≠ t0 ℓ γ % ℓ) : γ' ≠ γ := by
  rintro rfl
  apply hmod
  have hcop : Nat.Coprime ℓ 2 := (Nat.coprime_primes hℓ.out Nat.prime_two).mpr hℓ2
  have h0 := t0_dvd (hℓ := hℓ) hℓ2 hγ 0
  rw [mul_zero, add_zero] at h0
  have h1 : 2 * t + 2 * γ' + 1 ≡ 2 * t0 ℓ γ' + 2 * γ' + 1 [MOD ℓ] :=
    (Nat.modEq_zero_iff_dvd.mpr ht).trans (Nat.modEq_zero_iff_dvd.mpr h0).symm
  have h2 : 2 * t ≡ 2 * t0 ℓ γ' [MOD ℓ] :=
    Nat.ModEq.add_right_cancel' (2 * γ') (Nat.ModEq.add_right_cancel' 1 h1)
  exact Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.coprime_comm] using hcop) h2

/-- `w̄^{t₀(γ)} = q̄^{2γ} ε̄` with `ε = 1` (type S) or `w` (types D, L). -/
lemma red_wt_pow_t0 (g : Good q ℓ) {γ : ℕ} (hγ : γ < ℓ) :
    red ℓ (wt q) ^ t0 ℓ γ =
      (q : ZMod ℓ) ^ (2 * γ) * (if γ < kap ℓ then 1 else red ℓ (wt q)) := by
  have hℓ2 := g.ne_two
  obtain ⟨-, -, h⟩ := t0_facts (hℓ := hℓ) hℓ2 hγ
  have hq0 : (q : ZMod ℓ) ≠ 0 := red_q_ne_zero g.hℓq
  have hpow : (q : ZMod ℓ) ^ (2 * t0 ℓ γ) * (q : ZMod ℓ) ^ (2 * γ + 1) =
      (q : ZMod ℓ) ^ (if γ < kap ℓ then 1 else 3) := by
    rw [← pow_add, show 2 * t0 ℓ γ + (2 * γ + 1) = 2 * t0 ℓ γ + 2 * γ + 1 by ring, h, pow_ell_mul]
  rw [red_wt g.hℓq, inv_pow, ← pow_mul]
  have hA : (q : ZMod ℓ) ^ (2 * t0 ℓ γ) ≠ 0 := pow_ne_zero _ hq0
  split_ifs at hpow ⊢ with hs
  · have key : (q : ZMod ℓ) ^ (2 * t0 ℓ γ) * (q : ZMod ℓ) ^ (2 * γ) = 1 := by
      refine mul_right_cancel₀ hq0 ?_
      rw [one_mul, mul_assoc, ← pow_succ, hpow, pow_one]
    rw [mul_one]
    exact (eq_inv_of_mul_eq_one_right key).symm
  · have key : (q : ZMod ℓ) ^ (2 * t0 ℓ γ) * (q : ZMod ℓ) ^ (2 * γ) = (q : ZMod ℓ) ^ 2 := by
      refine mul_right_cancel₀ hq0 ?_
      rw [mul_assoc, ← pow_succ, hpow, ← pow_succ]
    have h2 : (q : ZMod ℓ) ^ 2 ≠ 0 := pow_ne_zero _ hq0
    rw [eq_comm, mul_inv_eq_iff_eq_mul₀ h2, ← key]
    field_simp

/-! ### Integrality and the off-class zeros -/

lemma E0_offdiag_eq {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) (hij : i ≠ j) :
    E0 q ℓ i j = nu ℓ i j * muPoly (wt q) (Fpoly (3 * ℓ) i j) := by
  unfold E0; rw [Afun_offdiag q _ i j hi hj hij]

lemma E0_diag_eq {i : ℕ} (hi : i < 3 * ℓ) :
    E0 q ℓ i i = nu ℓ i i * muPoly (wt q) (Qpoly (3 * ℓ) i) +
      (if i % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) * (4 * pole i * Spart q i) := by
  unfold E0
  rw [Afun_diag q _ i hi, mul_add]
  congr 1
  unfold nu
  have := dPrime_ne_zero (3 * ℓ) i
  field_simp

lemma E0_offdiag_mem (g : Good q ℓ) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) (hij : i ≠ j) :
    E0 q ℓ i j ∈ Zl ℓ := by
  rw [E0_offdiag_eq hi hj hij]
  exact padicNorm_mul_muPoly_le g.hq g.hℓq g.hℓq2 _ _ zero_le_one
    (fun t _ => nuF_le_one g.ne_two hi hj hij t)

lemma E0_offclass (g : Good q ℓ) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ)
    (hb : j % ℓ ≠ kap ℓ) (hab : i % ℓ ≠ j % ℓ) : red ℓ (E0 q ℓ i j) = 0 := by
  have hij : i ≠ j := fun h => hab (h ▸ rfl)
  rw [E0_offdiag_eq hi hj hij]
  have h := padicNorm_mul_muPoly_le g.hq g.hℓq g.hℓq2 (nu ℓ i j) (Fpoly (3 * ℓ) i j)
    ell_inv_pos.le (fun t _ => nuF_small_offclass g.ne_two hi hj hb hab t)
  exact (red_eq_zero_iff' (h.trans ell_inv_le_one)).mpr h

/-- Pointwise integrality of `ν_ii Q_i′(t)`. -/
lemma nuQ_le_one (g : Good q ℓ) {i : ℕ} (hi : i < 3 * ℓ) (t : ℕ) :
    padicNorm ℓ (nu ℓ i i * (derivative (Qpoly (3 * ℓ) i)).eval (t : ℚ)) ≤ 1 := by
  have hℓ2 := g.ne_two
  obtain ⟨γ', hγ', ht⟩ := exists_prog (hℓ := hℓ) hℓ2 t
  by_cases hag : i % ℓ = γ'
  · obtain ⟨s, c, p⟩ := exists_perm (div_lt_three hi)
    have hii : idx ℓ γ' (i / ℓ) = i := by rw [← hag]; exact idx_mod_div
    by_cases hk : γ' = kap ℓ
    · have := (resid_diag_D hℓ2 hγ' p ht hk).1
      rwa [hii] at this
    · have := (resid_diag_SL hℓ2 hγ' p ht hk).1
      rwa [hii] at this
  · exact (nuQ_small_offprog hℓ2 hγ' ht hi hag).trans ell_inv_le_one

lemma pole_div_ell_mem (hℓ2 : ℓ ≠ 2) {i : ℕ} (hi : i < 3 * ℓ) (hk : i % ℓ = kap ℓ) :
    pole i / ℓ ∈ Zl ℓ := by
  have hii : idx ℓ (kap ℓ) (i / ℓ) = i := by rw [← hk]; exact idx_mod_div
  rw [← hii, pole_idx_kap hℓ2]
  have : -((ℓ : ℚ) * (((i / ℓ : ℕ) : ℚ) + 1 / 2)) / ℓ = -(((i / ℓ : ℕ) : ℚ) + 1 / 2) := by
    field_simp [ell_pos.ne']
  rw [this]
  exact neg_mem (half_add_mem hℓ2 _)

lemma poleTerm_mem (g : Good q ℓ) {i : ℕ} (hi : i < 3 * ℓ) :
    (if i % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) * (4 * pole i * Spart q i) ∈ Zl ℓ := by
  have hℓ2 := g.ne_two
  have hii : idx ℓ (i % ℓ) (i / ℓ) = i := idx_mod_div
  have hS := (red_ell_sq_Spart g.h7 g.hℓq (Nat.mod_lt i hℓ.out.pos) (div_lt_three hi)).1
  rw [hii] at hS
  have h4 : (4 : ℚ) ∈ Zl ℓ := by exact_mod_cast natCast_mem_Zl 4
  split_ifs with hk
  · have e : (ℓ : ℚ) * (4 * pole i * Spart q i) = 4 * (pole i / ℓ) * ((ℓ : ℚ) ^ 2 * Spart q i) := by
      field_simp [ell_pos.ne']
    rw [e]
    exact mul_mem (mul_mem h4 (pole_div_ell_mem hℓ2 hi hk)) hS
  · have e : (ℓ : ℚ) ^ 2 * (4 * pole i * Spart q i) = 4 * pole i * ((ℓ : ℚ) ^ 2 * Spart q i) := by ring
    rw [e]
    exact mul_mem (mul_mem h4 (pole_mem_Zl hℓ2 i)) hS

lemma E0_diag_mem (g : Good q ℓ) {i : ℕ} (hi : i < 3 * ℓ) : E0 q ℓ i i ∈ Zl ℓ := by
  rw [E0_diag_eq hi]
  refine add_mem ?_ (poleTerm_mem g hi)
  exact padicNorm_mul_muPoly_le g.hq g.hℓq g.hℓq2 _ _ zero_le_one (fun t _ => nuQ_le_one g hi t)

lemma E0_mem (g : Good q ℓ) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) : E0 q ℓ i j ∈ Zl ℓ := by
  by_cases hij : i = j
  · subst hij; exact E0_diag_mem g hi
  · exact E0_offdiag_mem g hi hj hij

/-! ### The series part of a block entry -/

/-- From residues on the own progression to the series part (`c₁ = 0`, types S and L). -/
lemma series_const (g : Good q ℓ) {γ : ℕ} (hγ : γ < ℓ) (ν : ℚ) (G : ℚ[X]) {c₀ : ℚ}
    (hc₀ : c₀ ∈ Zl ℓ)
    (hint : ∀ t : ℕ, padicNorm ℓ (ν * (derivative G).eval (t : ℚ)) ≤ 1)
    (hoff : ∀ γ' t : ℕ, γ' < ℓ → ℓ ∣ 2 * t + 2 * γ' + 1 → γ' ≠ γ →
      padicNorm ℓ (ν * (derivative G).eval (t : ℚ)) ≤ (ℓ : ℚ)⁻¹)
    (hres : ∀ t : ℕ, ℓ ∣ 2 * t + 2 * γ + 1 → ν * (derivative G).eval (t : ℚ) ∈ Zl ℓ ∧
      red ℓ (ν * (derivative G).eval (t : ℚ)) = red ℓ c₀) :
    red ℓ (ν * muPoly (wt q) G) = red ℓ (wt q) ^ t0 ℓ γ * (red ℓ c₀ / (1 - red ℓ (wt q))) := by
  have hℓ2 := g.ne_two
  obtain ⟨h1, h2, -⟩ := t0_facts (hℓ := hℓ) hℓ2 hγ
  rw [red_mul_muPoly g.hq g.hℓq g.hℓq2 ν G h1 h2 hc₀ (zero_mem _) (fun t _ => hint t)
    (fun t _ hmod => by
      obtain ⟨γ', hγ', ht⟩ := exists_prog (hℓ := hℓ) hℓ2 t
      exact hoff γ' t hγ' ht (prog_of_mod_ne hℓ2 hγ ht hmod))
    (fun j => by
      obtain ⟨hm, hr⟩ := hres _ (t0_dvd hℓ2 hγ j)
      rw [zero_mul, add_zero]
      exact (red_eq_zero_iff' (sub_mem hm hc₀)).mp (by rw [red_sub hm hc₀, hr, sub_self])),
    red_zero, zero_mul, zero_div, add_zero]

/-- The same with a linear residue `c₀ + c₁ j` (type D). -/
lemma series_lin (g : Good q ℓ) {γ : ℕ} (hγ : γ < ℓ) (ν : ℚ) (G : ℚ[X]) {c₀ c₁ : ℚ}
    (hc₀ : c₀ ∈ Zl ℓ) (hc₁ : c₁ ∈ Zl ℓ)
    (hint : ∀ t : ℕ, padicNorm ℓ (ν * (derivative G).eval (t : ℚ)) ≤ 1)
    (hoff : ∀ γ' t : ℕ, γ' < ℓ → ℓ ∣ 2 * t + 2 * γ' + 1 → γ' ≠ γ →
      padicNorm ℓ (ν * (derivative G).eval (t : ℚ)) ≤ (ℓ : ℚ)⁻¹)
    (hres : ∀ j : ℕ, ν * (derivative G).eval (((t0 ℓ γ + ℓ * j : ℕ)) : ℚ) ∈ Zl ℓ ∧
      red ℓ (ν * (derivative G).eval (((t0 ℓ γ + ℓ * j : ℕ)) : ℚ)) = red ℓ (c₀ + c₁ * j)) :
    red ℓ (ν * muPoly (wt q) G) = red ℓ (wt q) ^ t0 ℓ γ *
      (red ℓ c₀ / (1 - red ℓ (wt q)) + red ℓ c₁ * red ℓ (wt q) / (1 - red ℓ (wt q)) ^ 2) := by
  have hℓ2 := g.ne_two
  obtain ⟨h1, h2, -⟩ := t0_facts (hℓ := hℓ) hℓ2 hγ
  exact red_mul_muPoly g.hq g.hℓq g.hℓq2 ν G h1 h2 hc₀ hc₁ (fun t _ => hint t)
    (fun t _ hmod => by
      obtain ⟨γ', hγ', ht⟩ := exists_prog (hℓ := hℓ) hℓ2 t
      exact hoff γ' t hγ' ht (prog_of_mod_ne hℓ2 hγ ht hmod))
    (fun j => by
      obtain ⟨hm, hr⟩ := hres j
      have hcm : c₀ + c₁ * j ∈ Zl ℓ := add_mem hc₀ (mul_mem hc₁ (natCast_mem_Zl j))
      exact (red_eq_zero_iff' (sub_mem hm hcm)).mp (by rw [red_sub hm hcm, hr, sub_self]))

end Chi2Irr
