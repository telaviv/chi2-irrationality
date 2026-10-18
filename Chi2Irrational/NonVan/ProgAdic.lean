/-
# ℓ-adic consequences of the progression split

For `ℓ ∤ q(q²−1)` and `w = q⁻²`:
* `padicNorm_wt`, `red_wt`, `padicNorm_one_sub_wt_pow`: `w`, `1 − w^ℓ` are ℓ-units, `w̄^ℓ = w̄`.
* `padicNorm_mul_muPoly_le`: if `‖ν F′(t)‖ ≤ c` for all integers `t ≥ 1`, then `‖ν μ(F)‖ ≤ c`.
* `red_mul_muPoly`: if moreover `‖ν F′(t)‖ ≤ ℓ⁻¹` off one progression `t ≡ t₀ (mod ℓ)`, and on it
  `ν F′(t₀ + ℓj) ≡ c₀ + c₁ j (mod ℓ)`, then `red(ν μ(F)) = w̄^{t₀}(c̄₀/(1−w̄) + c̄₁ w̄/(1−w̄)²)`.
-/
import Chi2Irrational.NonVan.Progression

namespace Chi2Irr

open Polynomial Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma padicNorm_eq_one_of_red_ne_zero {x : ℚ} (hx : x ∈ Zl ℓ) (h : red ℓ x ≠ 0) :
    padicNorm ℓ x = 1 := by
  rw [Ne, red_eq_zero_iff hx, not_lt] at h
  exact le_antisymm hx h

lemma padicNorm_natCast_q {q : ℕ} (hℓq : ¬ ℓ ∣ q) : padicNorm ℓ (q : ℚ) = 1 :=
  padicNorm_natCast_eq_one hℓq

lemma padicNorm_wt {q : ℕ} (hℓq : ¬ ℓ ∣ q) : padicNorm ℓ (wt q) = 1 := by
  unfold wt
  rw [padicNorm.div, padicNorm.one, padicNorm_pow, padicNorm_natCast_q hℓq]
  norm_num

lemma wt_mem {q : ℕ} (hℓq : ¬ ℓ ∣ q) : wt q ∈ Zl ℓ := le_of_eq (padicNorm_wt hℓq)

lemma red_wt {q : ℕ} (hℓq : ¬ ℓ ∣ q) : red ℓ (wt q) = ((q : ZMod ℓ) ^ 2)⁻¹ := by
  unfold wt
  have hq2 : padicNorm ℓ ((q : ℚ) ^ 2) = 1 := by rw [padicNorm_pow, padicNorm_natCast_q hℓq]; norm_num
  rw [red_div (one_mem _) hq2, red_one, red_pow (natCast_mem_Zl q), red_natCast, one_div]

lemma red_q_ne_zero {q : ℕ} (hℓq : ¬ ℓ ∣ q) : (q : ZMod ℓ) ≠ 0 := by
  rwa [Ne, ZMod.natCast_eq_zero_iff]

lemma red_wt_ne_zero {q : ℕ} (hℓq : ¬ ℓ ∣ q) : red ℓ (wt q) ≠ 0 := by
  rw [red_wt hℓq]
  exact inv_ne_zero (pow_ne_zero 2 (red_q_ne_zero hℓq))

lemma one_sub_red_wt_ne_zero {q : ℕ} (hq : 1 ≤ q) (hℓq : ¬ ℓ ∣ q) (hℓq2 : ¬ ℓ ∣ q ^ 2 - 1) :
    1 - red ℓ (wt q) ≠ 0 := by
  rw [red_wt hℓq, sub_ne_zero]
  intro h
  have h2 : (q : ZMod ℓ) ^ 2 = 1 := by
    have := congrArg (·⁻¹) h
    simpa using this.symm
  apply hℓq2
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rw [h2, sub_self]

lemma red_wt_pow_ell {q : ℕ} : red ℓ (wt q) ^ ℓ = red ℓ (wt q) := ZMod.pow_card _

lemma padicNorm_wt_pow {q : ℕ} (hℓq : ¬ ℓ ∣ q) (n : ℕ) : padicNorm ℓ (wt q ^ n) = 1 := by
  rw [padicNorm_pow, padicNorm_wt hℓq, one_pow]

lemma red_one_sub_wt_pow {q : ℕ} (hℓq : ¬ ℓ ∣ q) :
    red ℓ (1 - wt q ^ ℓ) = 1 - red ℓ (wt q) := by
  rw [red_sub (one_mem _) (pow_mem (wt_mem hℓq) ℓ), red_one, red_pow (wt_mem hℓq), red_wt_pow_ell]

lemma padicNorm_one_sub_wt_pow {q : ℕ} (hq : 1 ≤ q) (hℓq : ¬ ℓ ∣ q) (hℓq2 : ¬ ℓ ∣ q ^ 2 - 1) :
    padicNorm ℓ (1 - wt q ^ ℓ) = 1 := by
  refine padicNorm_eq_one_of_red_ne_zero (sub_mem (one_mem _) (pow_mem (wt_mem hℓq) ℓ)) ?_
  rw [red_one_sub_wt_pow hℓq]
  exact one_sub_red_wt_ne_zero hq hℓq hℓq2

/-- The progression terms `ν · F′(ρ + 1 + ℓ j)`. -/
lemma eval_progTerm (ν : ℚ) (F : ℚ[X]) (ρ L j : ℕ) :
    (C ν * (derivative F).comp (C ((ρ : ℚ) + 1) + C (L : ℚ) * X)).eval (j : ℚ) =
      ν * (derivative F).eval (((ρ + 1 + L * j : ℕ)) : ℚ) := by
  rw [eval_mul, eval_C, eval_comp]
  simp only [eval_add, eval_C, eval_mul, eval_X]
  push_cast
  ring_nf

lemma muPoly_split' {q : ℕ} (hq : 2 ≤ q) (ν : ℚ) (F : ℚ[X]) {N : ℕ} (hN : F.natDegree < N) :
    ν * muPoly (wt q) F = ∑ ρ ∈ range ℓ, wt q ^ (ρ + 1) *
      sigN N (wt q ^ ℓ) (C ν * (derivative F).comp (C ((ρ : ℚ) + 1) + C (ℓ : ℚ) * X)) := by
  rw [muPoly_split hq hℓ.out.pos F hN, mul_sum]
  refine sum_congr rfl (fun ρ _ => ?_)
  rw [sigN_C_mul]
  ring

/-- **Integrality / smallness of `ν μ(F)`.** -/
theorem padicNorm_mul_muPoly_le {q : ℕ} (hq : 2 ≤ q) (hℓq : ¬ ℓ ∣ q) (hℓq2 : ¬ ℓ ∣ q ^ 2 - 1)
    (ν : ℚ) (F : ℚ[X]) {c : ℚ} (hc : 0 ≤ c)
    (h : ∀ t : ℕ, 1 ≤ t → padicNorm ℓ (ν * (derivative F).eval (t : ℚ)) ≤ c) :
    padicNorm ℓ (ν * muPoly (wt q) F) ≤ c := by
  rw [muPoly_split' (ℓ := ℓ) hq ν F (Nat.lt_succ_self _)]
  refine padicNorm.sum_le' (fun ρ _ => ?_) hc
  rw [padicNorm.mul, padicNorm_wt_pow hℓq, one_mul]
  refine padicNorm_sigN_le (padicNorm_wt_pow hℓq ℓ)
    (padicNorm_one_sub_wt_pow (by omega) hℓq hℓq2) hc (fun j => ?_)
  rw [eval_progTerm]
  exact h _ (by omega)

lemma mod_ne_of_ne {ρ t₀ : ℕ} (hρ : ρ < ℓ) (h1 : 1 ≤ t₀) (h2 : t₀ ≤ ℓ) (hne : ρ ≠ t₀ - 1) (j : ℕ) :
    (ρ + 1 + ℓ * j) % ℓ ≠ t₀ % ℓ := by
  have hℓpos : 0 < ℓ := hℓ.out.pos
  rw [show ρ + 1 + ℓ * j = (ρ + 1) + ℓ * j from rfl, Nat.add_mul_mod_self_left]
  intro h
  rcases Nat.lt_or_ge (ρ + 1) ℓ with h3 | h3
  · rcases Nat.lt_or_ge t₀ ℓ with h4 | h4
    · rw [Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] at h; omega
    · have : t₀ = ℓ := le_antisymm h2 h4
      subst this
      rw [Nat.mod_eq_of_lt h3, Nat.mod_self] at h; omega
  · have : ρ + 1 = ℓ := by omega
    rw [this, Nat.mod_self] at h
    rcases Nat.lt_or_ge t₀ ℓ with h4 | h4
    · rw [Nat.mod_eq_of_lt h4] at h; omega
    · omega

/-- **Residue of `ν μ(F)` from its own progression.** -/
theorem red_mul_muPoly {q : ℕ} (hq : 2 ≤ q) (hℓq : ¬ ℓ ∣ q) (hℓq2 : ¬ ℓ ∣ q ^ 2 - 1)
    (ν : ℚ) (F : ℚ[X]) {t₀ : ℕ} (ht₁ : 1 ≤ t₀) (htℓ : t₀ ≤ ℓ) {c₀ c₁ : ℚ}
    (hc₀ : c₀ ∈ Zl ℓ) (hc₁ : c₁ ∈ Zl ℓ)
    (hint : ∀ t : ℕ, 1 ≤ t → padicNorm ℓ (ν * (derivative F).eval (t : ℚ)) ≤ 1)
    (hoff : ∀ t : ℕ, 1 ≤ t → t % ℓ ≠ t₀ % ℓ →
      padicNorm ℓ (ν * (derivative F).eval (t : ℚ)) ≤ (ℓ : ℚ)⁻¹)
    (hon : ∀ j : ℕ, padicNorm ℓ (ν * (derivative F).eval (((t₀ + ℓ * j : ℕ)) : ℚ) -
      (c₀ + c₁ * j)) ≤ (ℓ : ℚ)⁻¹) :
    red ℓ (ν * muPoly (wt q) F) = red ℓ (wt q) ^ t₀ *
      (red ℓ c₀ / (1 - red ℓ (wt q)) + red ℓ c₁ * red ℓ (wt q) / (1 - red ℓ (wt q)) ^ 2) := by
  set N := F.natDegree + 2
  have hN : F.natDegree < N := by omega
  have hN2 : 2 ≤ N := by omega
  set v := wt q ^ ℓ with hv
  set G : ℕ → ℚ[X] := fun ρ => C ν * (derivative F).comp (C ((ρ : ℚ) + 1) + C (ℓ : ℚ) * X)
  have hvn : padicNorm ℓ v = 1 := padicNorm_wt_pow hℓq ℓ
  have hv1 : padicNorm ℓ (1 - v) = 1 := padicNorm_one_sub_wt_pow (by omega) hℓq hℓq2
  have hterm_mem : ∀ ρ ∈ range ℓ, wt q ^ (ρ + 1) * sigN N v (G ρ) ∈ Zl ℓ := by
    intro ρ _
    refine mul_mem (pow_mem (wt_mem hℓq) _) ?_
    exact padicNorm_sigN_le hvn hv1 zero_le_one (fun j => by
      simp only [G]; rw [eval_progTerm]; exact hint _ (by omega))
  rw [muPoly_split' (ℓ := ℓ) hq ν F hN, red_sum _ _ hterm_mem]
  rw [sum_eq_single (t₀ - 1)]
  · -- the own progression
    have hρ : ((t₀ - 1 : ℕ) : ℚ) + 1 = t₀ := by
      rw [Nat.cast_sub ht₁]; push_cast; ring
    set L : ℚ[X] := C c₁ * X + C c₀
    have hsplit : sigN N v (G (t₀ - 1)) = sigN N v L + sigN N v (G (t₀ - 1) - L) := by
      rw [sigN_sub]; ring
    have hsmall : padicNorm ℓ (sigN N v (G (t₀ - 1) - L)) ≤ (ℓ : ℚ)⁻¹ := by
      refine padicNorm_sigN_le hvn hv1 ell_inv_pos.le (fun j => ?_)
      simp only [G, L, eval_sub]
      rw [eval_progTerm]
      simp only [eval_add, eval_mul, eval_C, eval_X]
      have := hon j
      rwa [show t₀ - 1 + 1 + ℓ * j = t₀ + ℓ * j by omega, show c₁ * (j : ℚ) + c₀ = c₀ + c₁ * j by ring]
    have hlin := sigN_linear hN2 c₀ c₁ v
    have hsm_mem : sigN N v (G (t₀ - 1) - L) ∈ Zl ℓ := hsmall.trans ell_inv_le_one
    have h1v : 1 - v ∈ Zl ℓ := le_of_eq hv1
    have hsq : padicNorm ℓ ((1 - v) ^ 2) = 1 := by rw [padicNorm_pow, hv1, one_pow]
    have hA : c₀ / (1 - v) ∈ Zl ℓ := by
      rw [div_eq_mul_inv]; exact mul_mem hc₀ (inv_mem_Zl hv1)
    have hB : c₁ * v / (1 - v) ^ 2 ∈ Zl ℓ := by
      rw [div_eq_mul_inv]; exact mul_mem (mul_mem hc₁ (le_of_eq hvn)) (inv_mem_Zl hsq)
    have hLmem : sigN N v L ∈ Zl ℓ := by rw [hlin]; exact add_mem hA hB
    rw [hsplit, red_mul (pow_mem (wt_mem hℓq) _) (add_mem hLmem hsm_mem),
      red_add hLmem hsm_mem, (red_eq_zero_iff' hsm_mem).mpr hsmall, add_zero, hlin,
      red_add hA hB, red_div hc₀ hv1, red_div (mul_mem hc₁ (le_of_eq hvn)) hsq,
      red_mul hc₁ (le_of_eq hvn), red_pow h1v, red_one_sub_wt_pow hℓq, hv, red_pow (wt_mem hℓq) ℓ,
      red_wt_pow_ell, red_pow (wt_mem hℓq) (t₀ - 1 + 1), Nat.sub_add_cancel ht₁]
  · intro ρ hρ hne
    have hsm : padicNorm ℓ (wt q ^ (ρ + 1) * sigN N v (G ρ)) ≤ (ℓ : ℚ)⁻¹ := by
      rw [padicNorm.mul, padicNorm_wt_pow hℓq, one_mul]
      refine padicNorm_sigN_le hvn hv1 ell_inv_pos.le (fun j => ?_)
      simp only [G]
      rw [eval_progTerm]
      exact hoff _ (by omega) (mod_ne_of_ne (mem_range.mp hρ) ht₁ htℓ hne j)
    exact (red_eq_zero_iff' (hsm.trans ell_inv_le_one)).mpr hsm
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

end Chi2Irr
