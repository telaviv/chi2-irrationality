/-
# Lemma 1 for the Ti machine: the pole expansion at the signed weight `w = −q⁻²`

Copy of `PoleExpansion.lean` (namespace `Chi2Irr.TiQ`): `ΛT(g) := ∑_{t≥1} w^t (g(u)·u/D(u))′|_{u=t}` with
`w = wT q = −1/q²` equals `AT(g) + Ti₂(1/q)·BT(g)` (`Lam_eqT`), hence
`Δ^Ti_h(Ti₂(1/q)) = det(ΛT(u^{i+j}))_{i,j<h}` (`aeval_ti2_DeltaT`).

Changes from the χ₂ file: summability uses `|w| < 1` (`summable_powW'`, `powSum_eq_tsum'` of `TiQ/PoleSeries.lean`)
and the pole series is `pole_seriesT`. The machine-free lemmas (`partialFrac`, `deriv_gphi`, `poleR`, …) are reused
from `PoleExpansion.lean`.
-/
import Chi2Irrational.TiQ.PoleSeries
import Chi2Irrational.PoleExpansion

namespace Chi2Irr
namespace TiQ

open Polynomial Finset Filter Topology

/-- The real moment functional `ΛT(g) = ∑_{t≥1} w^t (g u / D)′(t)`, `w = −q⁻²`, `K` poles. -/
noncomputable def LamT (q K : ℕ) (g : ℚ[X]) : ℝ :=
  ∑' t : ℕ, ((wT q : ℚ) : ℝ) ^ (t + 1) *
    deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1)

lemma abs_wT_real_lt_one {q : ℕ} (hq : 2 ≤ q) : |((wT q : ℚ) : ℝ)| < 1 := by
  rw [← Rat.cast_abs]; exact_mod_cast abs_wT_lt_one hq

lemma summable_geomW' {W : ℝ} (h1 : |W| < 1) : Summable (fun t : ℕ => |W| ^ (t + 1)) := by
  have h1' : |(|W|)| < 1 := by rwa [abs_abs]
  simpa using summable_powW' 0 h1'

lemma summable_pole_termT {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    Summable (fun t : ℕ => ((wT q : ℚ) : ℝ) ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
  have hW1 := abs_wT_real_lt_one hq
  refine Summable.of_norm_bounded (summable_geomW' hW1) (fun t => ?_)
  have hk := poleR_neg k
  have h1 : (1 : ℝ) ≤ ((t : ℝ) + 1) - poleR k := by
    have : (0 : ℝ) ≤ t := t.cast_nonneg
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_pow]
  have : |1 / (((t : ℝ) + 1) - poleR k) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    nlinarith
  have hWt := pow_nonneg (abs_nonneg ((wT q : ℚ) : ℝ)) (t + 1)
  calc |((wT q : ℚ) : ℝ)| ^ (t + 1) * |1 / (((t : ℝ) + 1) - poleR k) ^ 2|
      ≤ |((wT q : ℚ) : ℝ)| ^ (t + 1) * 1 := by gcongr
    _ = _ := mul_one _

/-- `μ(u^n)` as a series (`|w| < 1`). -/
lemma muMono_eq_tsum' {w : ℚ} (h1 : |w| < 1) (n : ℕ) :
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

lemma aeval_derivative_eq (R : ℚ[X]) (x : ℝ) : aeval x (derivative R) =
    ∑ n ∈ R.support, ((R.coeff n : ℚ) : ℝ) * ((n : ℝ) * x ^ (n - 1)) := by
  rw [derivative_apply, Polynomial.sum_def, map_sum]
  refine sum_congr rfl (fun n _ => ?_)
  rw [map_mul, aeval_C, map_pow, aeval_X]
  push_cast
  simp [eq_ratCast]
  ring

lemma summable_muPoly_termT {q : ℕ} (hq : 2 ≤ q) (R : ℚ[X]) :
    Summable (fun t : ℕ => ((wT q : ℚ) : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R)) := by
  have hW1 := abs_wT_real_lt_one hq
  simp_rw [aeval_derivative_eq, mul_sum]
  refine summable_sum (fun n _ => ?_)
  cases n with
  | zero => simp
  | succ d =>
    refine ((summable_powW' d hW1).mul_left
      (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- `μ(R) = ∑_{t≥1} w^t R′(t)` for a polynomial `R`, `w = −q⁻²`. -/
lemma muPoly_eq_tsumT {q : ℕ} (hq : 2 ≤ q) (R : ℚ[X]) :
    ((muPoly (wT q) R : ℚ) : ℝ) =
      ∑' t : ℕ, ((wT q : ℚ) : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) := by
  have h1 := abs_wT_lt_one hq
  have hW1 := abs_wT_real_lt_one hq
  simp_rw [aeval_derivative_eq, mul_sum]
  rw [Summable.tsum_finsetSum (fun n _ => ?_)]
  · unfold muPoly
    rw [Polynomial.sum_def]
    push_cast
    refine sum_congr rfl (fun n _ => ?_)
    rw [muMono_eq_tsum' h1, ← tsum_mul_left]
    congr 1
    ext t
    ring
  · cases n with
    | zero => simp
    | succ d =>
      refine ((summable_powW' d hW1).mul_left
        (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

lemma Lam_termT (q K : ℕ) (g : ℚ[X]) (t : ℕ) :
    ((wT q : ℚ) : ℝ) ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1) =
      ((wT q : ℚ) : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative ((g * X) /ₘ Dpoly K)) +
        ∑ k ∈ range K, (((g.eval (pole k) * omega K k : ℚ)) : ℝ) *
          (((wT q : ℚ) : ℝ) ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
  rw [deriv_gphi K g (by positivity), mul_add, mul_sum]
  refine congrArg _ (sum_congr rfl (fun k _ => by ring))

/-- **Lemma 1 for Ti (pole expansion).** `ΛT(g) = AT(g) + Ti₂(1/q) BT(g)`. -/
theorem Lam_eqT {q : ℕ} (hq : 2 ≤ q) (K : ℕ) (g : ℚ[X]) :
    LamT q K g = (AfunT q K g : ℝ) + ti2 (1 / (q : ℝ)) * (BfunT q K g : ℝ) := by
  unfold LamT
  set W : ℝ := ((wT q : ℚ) : ℝ)
  set R := (g * X) /ₘ Dpoly K
  set c : ℕ → ℝ := fun k => (((g.eval (pole k) * omega K k : ℚ)) : ℝ) with hc
  have hsR := summable_muPoly_termT hq R
  have hsP : ∀ k ∈ range K, Summable (fun t : ℕ =>
      c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2)))) :=
    fun k _ => (summable_pole_termT hq k).mul_left (c k)
  rw [tsum_congr (Lam_termT q K g), hsR.tsum_add (summable_sum hsP), Summable.tsum_finsetSum hsP,
    ← muPoly_eq_tsumT hq R]
  have hpk : ∀ k ∈ range K, ∑' t : ℕ, c k * (W ^ (t + 1) *
      (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) =
      c k * (-4 * ((poleW q k : ℝ) * ti2 (1 / (q : ℝ)) - (SpartT q k : ℝ))) := by
    intro k _
    rw [tsum_mul_left]
    congr 1
    exact pole_seriesT hq k
  rw [sum_congr rfl hpk]
  unfold AfunT BfunT
  push_cast
  simp only [hc]
  push_cast
  rw [mul_sum, mul_sum, mul_sum]
  rw [add_assoc]
  congr 1
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  ring

/-- The series defining `ΛT(g)` converges. -/
lemma summable_Lam_summandT {q : ℕ} (hq : 2 ≤ q) (K : ℕ) (g : ℚ[X]) :
    Summable (fun t : ℕ => ((wT q : ℚ) : ℝ) ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1)) := by
  have hsP : ∀ k ∈ range K, Summable (fun t : ℕ =>
      (((g.eval (pole k) * omega K k : ℚ)) : ℝ) *
        (((wT q : ℚ) : ℝ) ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2)))) :=
    fun k _ => (summable_pole_termT hq k).mul_left _
  exact ((summable_muPoly_termT hq _).add (summable_sum hsP)).congr
    (fun t => (Lam_termT q K g t).symm)

/-- The Hankel matrix of `ΛT` (real), `K = h`. -/
noncomputable def LamMatT (q h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => LamT q h (X ^ ((i : ℕ) + j))

/-- `Δ^Ti_h(Ti₂(1/q)) = det(ΛT(u^{i+j}))`. -/
theorem aeval_ti2_DeltaT {q : ℕ} (hq : 2 ≤ q) (h : ℕ) :
    aeval (ti2 (1 / (q : ℝ))) (DeltaT q h) = (LamMatT q h).det := by
  unfold DeltaT
  rw [AlgHom.map_det]
  · congr 1
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, aeval_X, aeval_C, LamMatT, Lam_eqT hq, AmatT, BmatT, eq_ratCast]
    ring

end TiQ
end Chi2Irr
