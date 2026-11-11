/-
# The progression split of μ for the signed weight `w = −q⁻²` (Lemma P, Step 3)

Copy of `NonVan/Progression.lean` (and of `muMono_eq_tsum`, `muPoly_eq_tsum` from `PoleExpansion.lean`) for
`wT q = −1/q²`: the series are absolutely convergent since `|w| < 1` (`abs_wT_lt_one`, `powSum_eq_tsum'`), which
replaces `0 ≤ w < 1`. The generic lemmas `tsum_split_mod`, `natDegree_comp_linear_lt` are reused.

`muPoly_split`: for `L ≥ 1`, `μ(F) = Σ_{ρ<L} w^{ρ+1} · σ(w^L, j ↦ F′(ρ + 1 + L j))`.
-/
import Chi2Irrational.NonVan.Progression
import Chi2Irrational.TiQ.PoleSeries

namespace Chi2Irr
namespace TiQ

open Polynomial Finset

/-- `μ(u^n)` as a series, for `|w| < 1`. -/
lemma muMono_eq_tsum {w : ℚ} (h1 : |w| < 1) (n : ℕ) :
    ((muMono w n : ℚ) : ℝ) = ∑' t : ℕ, (w : ℝ) ^ (t + 1) * ((n : ℝ) * ((t : ℝ) + 1) ^ (n - 1)) := by
  cases n with
  | zero => simp [muMono]
  | succ d =>
    simp only [muMono, Nat.add_sub_cancel]
    push_cast
    rw [powSum_eq_tsum' h1, ← tsum_mul_left]
    congr 1
    ext t
    ring

lemma abs_wT_real_lt_one {q : ℕ} (hq : 2 ≤ q) : |((wT q : ℚ) : ℝ)| < 1 := by
  rw [← Rat.cast_abs]; exact_mod_cast abs_wT_lt_one hq

/-- `μ(R) = ∑_{t≥1} w^t R′(t)` for a polynomial `R`, `w = −q⁻²`. -/
lemma muPoly_eq_tsum {q : ℕ} (hq : 2 ≤ q) (R : ℚ[X]) :
    ((muPoly (wT q) R : ℚ) : ℝ) =
      ∑' t : ℕ, ((wT q : ℚ) : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) := by
  have h1 : |wT q| < 1 := abs_wT_lt_one hq
  have hder : ∀ x : ℝ, aeval x (derivative R) =
      ∑ n ∈ R.support, ((R.coeff n : ℚ) : ℝ) * ((n : ℝ) * x ^ (n - 1)) := by
    intro x
    rw [derivative_apply, Polynomial.sum_def, map_sum]
    refine sum_congr rfl (fun n _ => ?_)
    rw [map_mul, aeval_C, map_pow, aeval_X]
    push_cast
    simp [eq_ratCast]
    ring
  simp_rw [hder, mul_sum]
  rw [Summable.tsum_finsetSum (fun n _ => ?_)]
  · unfold muPoly
    rw [Polynomial.sum_def]
    push_cast
    refine sum_congr rfl (fun n _ => ?_)
    rw [muMono_eq_tsum h1, ← tsum_mul_left]
    congr 1
    ext t
    ring
  · cases n with
    | zero => simp
    | succ d =>
      refine ((summable_powW' d (abs_wT_real_lt_one hq)).mul_left
        (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- **Progression split of μ** (`w = −q⁻²`). -/
theorem muPoly_split {q : ℕ} (hq : 2 ≤ q) {L : ℕ} (hL : 0 < L) (F : ℚ[X]) {N : ℕ}
    (hN : F.natDegree < N) :
    muPoly (wT q) F = ∑ ρ ∈ range L, wT q ^ (ρ + 1) *
      sigN N (wT q ^ L) ((derivative F).comp (C ((ρ : ℚ) + 1) + C (L : ℚ) * X)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [muPoly_eq_tsum hq F]
  have hW1 := abs_wT_real_lt_one hq
  have hsum : Summable (fun t : ℕ => ((wT q : ℚ) : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative F)) := by
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
    refine ((summable_powW' n hW1).mul_left ((((derivative F).coeff n : ℚ) : ℝ))).congr (fun t => ?_)
    ring
  rw [tsum_split_mod hsum hL]
  push_cast
  refine sum_congr rfl (fun ρ _ => ?_)
  have hv : |(((wT q ^ L : ℚ)) : ℝ)| < 1 := by
    push_cast
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) hW1 hL.ne'
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

end TiQ
end Chi2Irr
