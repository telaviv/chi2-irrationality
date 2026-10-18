/-
# The progression split of μ (Lemma P, Step 3)

`muPoly_split`: for `L ≥ 1`,
  `μ(F) = Σ_{ρ<L} w^{ρ+1} · σ(w^L, j ↦ F′(ρ + 1 + L j))`
as rational numbers, where `σ = sigN (deg F + 1)`. With `padicNorm_sigN_le` this gives the ℓ-adic control of `μ(F)`
progression by progression (`padicNorm_muPoly_le`).
-/
import Chi2Irrational.NonVan.Sigma
import Chi2Irrational.PoleExpansion

namespace Chi2Irr

open Polynomial Finset

/-- Split a convergent series over `ℕ` by residues mod `L`. -/
lemma tsum_split_mod {f : ℕ → ℝ} (hf : Summable f) {L : ℕ} (hL : 0 < L) :
    ∑' t, f t = ∑ ρ ∈ range L, ∑' j : ℕ, f (ρ + L * j) := by
  have hdecomp : ∀ t, f t = ∑ ρ ∈ range L, Set.indicator {t : ℕ | t % L = ρ} f t := by
    intro t
    rw [sum_eq_single (t % L)]
    · simp
    · intro ρ _ hρ
      rw [Set.indicator_of_notMem]
      simpa [eq_comm] using hρ
    · intro h
      exact absurd (mem_range.mpr (Nat.mod_lt t hL)) h
  rw [tsum_congr hdecomp, Summable.tsum_finsetSum (fun ρ _ => hf.indicator _)]
  refine sum_congr rfl (fun ρ hρ => ?_)
  have hρL : ρ < L := mem_range.mp hρ
  have hinj : Function.Injective (fun j : ℕ => ρ + L * j) := by
    intro a b hab
    simp only at hab
    exact Nat.eq_of_mul_eq_mul_left hL (by omega)
  rw [← hinj.tsum_eq]
  · refine tsum_congr (fun j => ?_)
    rw [Set.indicator_of_mem]
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρL]
  · intro t ht
    rw [Function.mem_support] at ht
    have : t % L = ρ := by
      by_contra hne
      exact ht (Set.indicator_of_notMem (show t ∉ {t : ℕ | t % L = ρ} from hne) f)
    exact ⟨t / L, by simp only; rw [← this]; exact Nat.mod_add_div t L⟩

lemma natDegree_comp_linear_lt (F : ℚ[X]) (a b : ℚ) :
    ((derivative F).comp (C a + C b * X)).natDegree < F.natDegree + 1 := by
  have h1 := natDegree_comp_le (p := derivative F) (q := C a + C b * X)
  have h2 : (C a + C b * X).natDegree ≤ 1 := by
    rw [add_comm]; exact natDegree_linear_le
  have h3 : (derivative F).natDegree ≤ F.natDegree := natDegree_derivative_le F |>.trans (Nat.sub_le _ _)
  calc ((derivative F).comp (C a + C b * X)).natDegree
      ≤ (derivative F).natDegree * (C a + C b * X).natDegree := h1
    _ ≤ F.natDegree * 1 := Nat.mul_le_mul h3 h2
    _ < F.natDegree + 1 := by omega

/-- **Progression split of μ.** -/
theorem muPoly_split {q : ℕ} (hq : 2 ≤ q) {L : ℕ} (hL : 0 < L) (F : ℚ[X]) {N : ℕ}
    (hN : F.natDegree < N) :
    muPoly (wt q) F = ∑ ρ ∈ range L, wt q ^ (ρ + 1) *
      sigN N (wt q ^ L) ((derivative F).comp (C ((ρ : ℚ) + 1) + C (L : ℚ) * X)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [muPoly_eq_tsum hq F]
  have hW0 := wt_nonneg q
  have hW1 := wt_lt_one hq
  have hsum : Summable (fun t : ℕ => ((wt q : ℚ) : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative F)) := by
    have := (muPoly_eq_tsum hq F)
    -- summability as in `muPoly_eq_tsum`: a finite sum of `t^n w^t`
    have hder : ∀ x : ℝ, aeval x (derivative F) =
        ∑ n ∈ (derivative F).support, (((derivative F).coeff n : ℚ) : ℝ) * x ^ n := by
      intro x
      rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
      rw [← sum_subset (s₁ := (derivative F).support) (s₂ := range ((derivative F).natDegree + 1))]
      · refine sum_congr rfl (fun n _ => ?_)
        rw [Algebra.smul_def, eq_ratCast]
      · intro n hn; exact mem_range.mpr (Nat.lt_succ_of_le (le_natDegree_of_mem_supp n hn))
      · intro n _ hn
        rw [notMem_support_iff.mp hn, zero_smul]
    simp_rw [hder, mul_sum]
    refine summable_sum (fun n _ => ?_)
    refine ((summable_powW n hW0 hW1).mul_left ((((derivative F).coeff n : ℚ) : ℝ))).congr (fun t => ?_)
    ring
  rw [tsum_split_mod hsum hL]
  push_cast
  refine sum_congr rfl (fun ρ _ => ?_)
  have hv : |(((wt q ^ L : ℚ)) : ℝ)| < 1 := by
    push_cast
    rw [abs_of_nonneg (pow_nonneg hW0 L)]
    exact pow_lt_one₀ hW0 hW1 hL.ne'
  rw [sigN_eq_tsum ((natDegree_comp_linear_lt F _ _).trans_le (Nat.succ_le_of_lt hN)) hv,
    ← tsum_mul_left]
  refine tsum_congr (fun j => ?_)
  rw [eval_comp]
  simp only [eval_add, eval_C, eval_mul, eval_X]
  have hx : ((ρ : ℝ) + (L : ℝ) * (j : ℝ) + 1) = ((((ρ : ℚ) + 1 + (L : ℚ) * (j : ℚ) : ℚ)) : ℝ) := by
    push_cast; ring
  rw [hx, aeval_ratCast]
  push_cast
  ring

end Chi2Irr
