/-
# Lemma P for Ti along `h = 3ℓ`

Copy of `NonVan/LemmaP.lean` for the Ti machine. `lemmaP`: if `Good q ℓ` (`ℓ ∤ q(q²+1)`, `ℓ ≥ 7`) and the three
ℓ-independent block determinants `det M(S), det M(L), det M(D)` of `TiQ/NonVan/BlockMat.lean` are ℓ-units, then
`Δ^Ti_{3ℓ}(a/b) ≠ 0` for every `a/b` with `ℓ ∤ b`.

Proof as for χ₂: the rescaled Gram matrix `ν_ij Λ_{a/b}(f_i f_j)` is ℓ-integral with the same reduction as `E0`
(the `X`-part is `ℓ`-small); `red E0` is block upper triangular for the key `bkey`, and its diagonal blocks are
`λ_γ M̄(S/L)` with the unit `λ_γ = x̄_γ (−1)^{κ+γ} q̄^{2γ}` and `M̄(D)`. The generic `bkey`, `bkey_eq_iff`, `bkey_le`,
`classEquiv`, `red_det_ne_zero`, `red_pole_ne_zero` are reused.
-/
import Chi2Irrational.TiQ.NonVan.BlockMat
import Chi2Irrational.NonVan.LemmaP

namespace Chi2Irr
namespace TiQ

open Polynomial Finset

variable {q ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The reduced matrix `red E0`. -/
noncomputable def Ebar (q ℓ : ℕ) [Fact ℓ.Prime] : Matrix (Fin (3 * ℓ)) (Fin (3 * ℓ)) (ZMod ℓ) :=
  fun i j => red ℓ (E0 q ℓ i j)

lemma Ebar_blockTriangular (g : Good q ℓ) :
    (Ebar q ℓ).BlockTriangular (fun i : Fin (3 * ℓ) => bkey ℓ i) := by
  intro i j hij
  have hℓ2 := g.ne_two
  have hjk : (j : ℕ) % ℓ ≠ kap ℓ := by
    intro h
    have : bkey ℓ j = ℓ := by unfold bkey; rw [ite_eq_left h]
    have := bkey_le (ℓ := ℓ) i
    simp only at hij
    omega
  have hab : (i : ℕ) % ℓ ≠ (j : ℕ) % ℓ := by
    intro h
    have := (bkey_eq_iff hℓ2 i j).mpr h
    simp only at hij
    omega
  show red ℓ (E0 q ℓ i j) = 0
  exact E0_offclass g i.isLt j.isLt hjk hab

lemma M_mem_SL (g : Good q ℓ) (r s : Fin 3) : MS q r s ∈ Zl ℓ ∧ ML q r s ∈ Zl ℓ := by
  have hℓ2 := g.ne_two
  have hr := r.isLt
  constructor
  · unfold MS
    refine add_mem (one_sub_wt_inv_mem g (crr_mem hℓ2 r)) ?_
    split_ifs
    · exact poleblock_mem g r (by omega)
    · exact zero_mem _
  · unfold ML
    refine add_mem (one_sub_wt_inv_mem g (mul_mem (wt_mem g.hℓq) (crr_mem hℓ2 r))) ?_
    split_ifs
    · exact poleblock_mem g r (by omega)
    · exact zero_mem _

lemma M_mem_D (g : Good q ℓ) (r s : Fin 3) : MD q r s ∈ Zl ℓ := by
  have hℓ2 := g.ne_two
  have hr := r.isLt
  have h2 : (2 : ℚ) ∈ Zl ℓ := by exact_mod_cast natCast_mem_Zl 2
  unfold MD
  refine add_mem (mul_mem (wt_mem g.hℓq) (add_mem (one_sub_wt_inv_mem g (mul_mem (crr_mem hℓ2 r)
    (eD_mem hℓ2 r s))) (one_sub_wt_sq_inv_mem g (mul_mem (mul_mem (crr_mem hℓ2 r) h2)
    (wt_mem g.hℓq))))) ?_
  split_ifs
  · exact mul_mem (mul_mem (mul_mem (mul_mem (neg_mem (by exact_mod_cast natCast_mem_Zl 4))
      (half_add_mem hℓ2 r)) (neg_one_pow_mem _)) (pow_mem (natCast_mem_Zl q) _)) (Tq_mem g (by omega))
  · exact zero_mem _

/-- **The reduced determinant is a unit.** -/
theorem det_Ebar_ne_zero (g : Good q ℓ) (hS : padicNorm ℓ (MS q).det = 1)
    (hL : padicNorm ℓ (ML q).det = 1) (hD : padicNorm ℓ (MD q).det = 1) :
    (Ebar q ℓ).det ≠ 0 := by
  have hℓ2 := g.ne_two
  rw [(Ebar_blockTriangular g).det]
  refine prod_ne_zero_iff.mpr (fun k hk => ?_)
  obtain ⟨i₀, -, rfl⟩ := mem_image.mp hk
  set γ := (i₀ : ℕ) % ℓ
  have hγ : γ < ℓ := Nat.mod_lt _ hℓ.out.pos
  have hkey : bkey ℓ (i₀ : ℕ) = bkey ℓ γ := by
    rw [bkey_eq_iff hℓ2, Nat.mod_eq_of_lt hγ]
  have hblock : ((Ebar q ℓ).toSquareBlock (fun i : Fin (3 * ℓ) => bkey ℓ i) (bkey ℓ (i₀ : ℕ))).det =
      (Matrix.of fun r s : Fin 3 => red ℓ (E0 q ℓ (idx ℓ γ r) (idx ℓ γ s))).det := by
    rw [hkey, ← Matrix.det_submatrix_equiv_self (classEquiv (ℓ := ℓ) hℓ2 hγ)]
    congr 1
  rw [hblock]
  by_cases hk : γ = kap ℓ
  · have e2 : (Matrix.of fun r s : Fin 3 => red ℓ (E0 q ℓ (idx ℓ γ r) (idx ℓ γ s))) =
        (MD q).map (red ℓ) := by
      ext r s
      simp only [Matrix.of_apply, Matrix.map_apply]
      rw [hk]; exact block_D g r s
    rw [e2]
    exact red_det_ne_zero (M_mem_D g) hD
  · set lamγ := red ℓ (pole γ) * (-1 : ZMod ℓ) ^ (kap ℓ + γ) * (q : ZMod ℓ) ^ (2 * γ)
    have hlam : lamγ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (red_pole_ne_zero hℓ2 hγ hk) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
        (pow_ne_zero _ (red_q_ne_zero g.hℓq))
    have e2 : (Matrix.of fun r s : Fin 3 => red ℓ (E0 q ℓ (idx ℓ γ r) (idx ℓ γ s))) =
        lamγ • ((if γ < kap ℓ then MS q else ML q).map (red ℓ)) := by
      ext r s
      simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact block_SL g hγ hk r s
    rw [e2, Matrix.det_smul, Fintype.card_fin]
    refine mul_ne_zero (pow_ne_zero _ hlam) ?_
    split_ifs
    · exact red_det_ne_zero (fun r s => (M_mem_SL g r s).1) hS
    · exact red_det_ne_zero (fun r s => (M_mem_SL g r s).2) hL

/-! ### From `E0` to the rescaled Gram matrix at `a/b` -/

lemma poleW_mem (q i : ℕ) : poleW q i ∈ Zl ℓ := by
  unfold poleW; exact mul_mem (neg_one_pow_mem _) (pow_mem (natCast_mem_Zl q) _)

lemma nu_Bfun_small (g : Good q ℓ) {i j : ℕ} (hi : i < 3 * ℓ) :
    padicNorm ℓ (nu ℓ i j * BfunT q (3 * ℓ) (fpoly (3 * ℓ) i * fpoly (3 * ℓ) j)) ≤ (ℓ : ℚ)⁻¹ := by
  have hℓ2 := g.ne_two
  rw [Bfun_fpoly q _ i j hi]
  split_ifs with hij
  · subst hij
    have e : nu ℓ i i * (-4 * pole i * dPrime (3 * ℓ) i * poleW q i) =
        (if i % ℓ = kap ℓ then (ℓ : ℚ) else (ℓ : ℚ) ^ 2) * (-4 * pole i * poleW q i) := by
      unfold nu
      have := dPrime_ne_zero (3 * ℓ) i
      field_simp
    rw [e]
    have hq4 : padicNorm ℓ (-4 * poleW q i) ≤ 1 :=
      mul_mem (neg_mem (by exact_mod_cast natCast_mem_Zl 4)) (poleW_mem q i)
    split_ifs with hk
    · -- `ℓ · x_i` with `ℓ | x_i`
      have hx := (pole_div_ell_mem hℓ2 hi hk)
      have e2 : (ℓ : ℚ) * (-4 * pole i * poleW q i) =
          (ℓ : ℚ) ^ 2 * ((pole i / ℓ) * (-4 * poleW q i)) := by
        field_simp [ell_pos.ne']
      rw [e2, padicNorm.mul, padicNorm_ell_pow]
      calc ((ℓ : ℚ)⁻¹) ^ 2 * padicNorm ℓ (pole i / ℓ * (-4 * poleW q i))
          ≤ ((ℓ : ℚ)⁻¹) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (mul_mem hx hq4) (pow_nonneg ell_inv_pos.le _)
        _ ≤ (ℓ : ℚ)⁻¹ := by rw [mul_one]; exact (inv_pow_anti (by norm_num)).trans (le_of_eq (pow_one _))
    · have e2 : (ℓ : ℚ) ^ 2 * (-4 * pole i * poleW q i) =
          (ℓ : ℚ) ^ 2 * (pole i * (-4 * poleW q i)) := by ring
      rw [e2, padicNorm.mul, padicNorm_ell_pow]
      calc ((ℓ : ℚ)⁻¹) ^ 2 * padicNorm ℓ (pole i * (-4 * poleW q i))
          ≤ ((ℓ : ℚ)⁻¹) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (mul_mem (pole_mem_Zl hℓ2 i) hq4) (pow_nonneg ell_inv_pos.le _)
        _ ≤ (ℓ : ℚ)⁻¹ := by rw [mul_one]; exact (inv_pow_anti (by norm_num)).trans (le_of_eq (pow_one _))
  · rw [mul_zero, padicNorm.zero]; exact ell_inv_pos.le

/-- **Lemma P for Ti (along `h = 3ℓ`).** -/
theorem lemmaP (g : Good q ℓ) (hS : padicNorm ℓ (MS q).det = 1)
    (hL : padicNorm ℓ (ML q).det = 1) (hD : padicNorm ℓ (MD q).det = 1)
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hℓb : ¬ ℓ ∣ b) :
    (DeltaT q (3 * ℓ)).eval ((a : ℚ) / b) ≠ 0 := by
  have hℓ2 := g.ne_two
  set r₀ : ℚ := (a : ℚ) / b
  have hr₀ : r₀ ∈ Zl ℓ := by
    simp only [r₀]
    rw [div_eq_mul_inv]
    exact mul_mem (intCast_mem_Zl a) (inv_mem_Zl (padicNorm_natCast_eq_one hℓb))
  set α : Fin (3 * ℓ) → ℚ := fun i => (ℓ : ℚ) ^ 2 / dPrime (3 * ℓ) i
  set β : Fin (3 * ℓ) → ℚ := fun j => if (j : ℕ) % ℓ = kap ℓ then (ℓ : ℚ)⁻¹ else 1
  apply Delta_eval_ne_zero_of_det α β
  set N := Matrix.of fun i j : Fin (3 * ℓ) => α i * Gram q (3 * ℓ) r₀ i j * β j
  have hN : ∀ i j : Fin (3 * ℓ), N i j = E0 q ℓ i j +
      r₀ * (nu ℓ i j * BfunT q (3 * ℓ) (fpoly (3 * ℓ) i * fpoly (3 * ℓ) j)) := by
    intro i j
    simp only [N, Matrix.of_apply, α, β, Gram, LamLin_apply, E0]
    have hαβ : (ℓ : ℚ) ^ 2 / dPrime (3 * ℓ) i * (if (j : ℕ) % ℓ = kap ℓ then (ℓ : ℚ)⁻¹ else 1) =
        nu ℓ i j := by
      unfold nu
      split_ifs <;> field_simp [ell_pos.ne']
    rw [← hαβ]
    ring
  have hsmallB : ∀ i j : Fin (3 * ℓ),
      padicNorm ℓ (r₀ * (nu ℓ i j * BfunT q (3 * ℓ) (fpoly (3 * ℓ) i * fpoly (3 * ℓ) j))) ≤ (ℓ : ℚ)⁻¹ :=
    fun i j => pn_mul_le_left hr₀ (nu_Bfun_small g i.isLt)
  have hNmem : ∀ i j, N i j ∈ Zl ℓ := fun i j => by
    rw [hN]; exact add_mem (E0_mem g i.isLt j.isLt) ((hsmallB i j).trans ell_inv_le_one)
  have hNred : N.map (red ℓ) = Ebar q ℓ := by
    ext i j
    simp only [Matrix.map_apply, Ebar]
    refine red_eq_of_sub (hNmem i j) (E0_mem g i.isLt j.isLt) ?_
    rw [hN, add_sub_cancel_left]
    exact lt_of_le_of_lt (hsmallB i j) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt))
  intro h0
  have := red_det N hNmem
  rw [h0, red_zero, hNred] at this
  exact det_Ebar_ne_zero g hS hL hD this.symm

end TiQ
end Chi2Irr
