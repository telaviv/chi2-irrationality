/-
# Lemma 1 at a rational point `ζ > 1` (copy of `PoleSeries.lean`, `PoleExpansion.lean` for `DeltaZ ζ`)

With `W = ζ⁻²` (`wtZ ζ`):
* `pole_seriesZ`: `∑_{t≥1} W^t · (−1/(t − x_k)²) = −4 (ζ^{2k+1} χ₂(1/ζ) − S_k(ζ))`;
* `LamZ ζ K g = ∑_{t≥1} W^t (g u / D)′(t)` and `LamZ_eq`: `LamZ ζ K g = A(g) + χ₂(1/ζ) B(g)` (`AfunZ`, `BfunZ`);
* `aeval_chi2_DeltaZ`: `Δ_h(χ₂(1/ζ); ζ) = det(LamZ ζ h (u^{i+j}))`.

The `q`-free lemmas of the originals (`powSum_eq_tsum`, `partialFrac`, `deriv_gphi`, `muMono_eq_tsum`,
`summable_powW`, `summable_geomW`, …) are reused.
-/
import Chi2Irrational.PoleExpansion
import Chi2Irrational.QZ.Machine

namespace Chi2Irr
namespace QZ

open Polynomial Finset Filter Topology

/-- The weight `W = ζ⁻²` as a real. -/
noncomputable def WrZ (ζ : ℚ) : ℝ := ((wtZ ζ : ℚ) : ℝ)

lemma WrZ_pos {ζ : ℚ} (hζ : 1 < ζ) : 0 < WrZ ζ := by
  unfold WrZ; exact_mod_cast wtZ_pos hζ

lemma WrZ_lt_one {ζ : ℚ} (hζ : 1 < ζ) : WrZ ζ < 1 := by
  unfold WrZ; exact_mod_cast wtZ_lt_one hζ

/-- **The pole series at `ζ`.** -/
theorem pole_seriesZ {ζ : ℚ} (hζ : 1 < ζ) (k : ℕ) :
    ∑' t : ℕ, WrZ ζ ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2)) =
      -4 * ((ζ : ℝ) ^ (2 * k + 1) * chi2 (1 / (ζ : ℝ)) - (SpartZ ζ k : ℝ)) := by
  have hq1 : (1 : ℝ) < ζ := by exact_mod_cast hζ
  have hq0 : (0 : ℝ) < ζ := by linarith
  have hz : |1 / (ζ : ℝ)| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    rw [div_le_one hq0]
    exact hq1.le
  set z : ℝ := 1 / (ζ : ℝ) with hzdef
  have hzq : (ζ : ℝ) * z = 1 := by rw [hzdef]; field_simp
  have hsplit := (summable_chi2Term hz).sum_add_tsum_nat_add (k + 1)
  have hhead : (ζ : ℝ) ^ (2 * k + 1) * ∑ i ∈ range (k + 1), chi2Term z i = (SpartZ ζ k : ℝ) := by
    unfold SpartZ chi2Term
    push_cast
    rw [mul_sum]
    refine sum_congr rfl (fun j hj => ?_)
    have hj : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have : (ζ : ℝ) ^ (2 * k + 1) * z ^ (2 * j + 1) = (ζ : ℝ) ^ (2 * (k - j)) := by
      rw [show 2 * k + 1 = 2 * (k - j) + (2 * j + 1) by omega, pow_add, mul_assoc, ← mul_pow, hzq,
        one_pow, mul_one]
    rw [← this]
    ring
  have htail : ∀ t : ℕ, (ζ : ℝ) ^ (2 * k + 1) * chi2Term z (t + (k + 1)) =
      WrZ ζ ^ (t + 1) * (1 / 4) * (1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2) := by
    intro t
    unfold chi2Term WrZ wtZ pole
    push_cast
    have hw : (1 / (ζ : ℝ) ^ 2) ^ (t + 1) = z ^ (2 * t + 2) := by
      rw [hzdef, ← one_div_pow, ← pow_mul]
      ring_nf
    rw [hw]
    have hpow : (ζ : ℝ) ^ (2 * k + 1) * z ^ (2 * (t + (k + 1)) + 1) = z ^ (2 * t + 2) := by
      rw [show 2 * (t + (k + 1)) + 1 = (2 * k + 1) + (2 * t + 2) by ring, pow_add z, ← mul_assoc,
        ← mul_pow, hzq, one_pow, one_mul]
    have hden : (2 * ((t : ℝ) + ((k : ℝ) + 1)) + 1) ^ 2 =
        4 * ((t : ℝ) + 1 - -((k : ℝ) + 1 / 2)) ^ 2 := by
      ring
    rw [mul_div_assoc', hpow, hden]
    have : ((t : ℝ) + 1 - -((k : ℝ) + 1 / 2)) ≠ 0 := by
      have : (0 : ℝ) ≤ t := t.cast_nonneg
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      intro h0
      linarith
    field_simp
  have key : (ζ : ℝ) ^ (2 * k + 1) * chi2 z - (SpartZ ζ k : ℝ) =
      ∑' t : ℕ, WrZ ζ ^ (t + 1) * (1 / 4) * (1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2) := by
    rw [chi2, ← hsplit, mul_add, hhead, add_sub_cancel_left, ← tsum_mul_left]
    exact tsum_congr htail
  rw [key, ← tsum_mul_left]
  refine tsum_congr (fun t => ?_)
  ring

/-- The real moment functional at `ζ`: `Λ(g) = ∑_{t≥1} W^t (g u / D)′(t)`, `W = ζ⁻²`, `K` poles. -/
noncomputable def LamZ (ζ : ℚ) (K : ℕ) (g : ℚ[X]) : ℝ :=
  ∑' t : ℕ, WrZ ζ ^ (t + 1) * deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1)

lemma summable_pole_termZ {ζ : ℚ} (hζ : 1 < ζ) (k : ℕ) :
    Summable (fun t : ℕ => WrZ ζ ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
  have hW0 := (WrZ_pos hζ).le
  refine Summable.of_norm_bounded (summable_geomW hW0 (WrZ_lt_one hζ)) (fun t => ?_)
  have hk := poleR_neg k
  have h1 : (1 : ℝ) ≤ ((t : ℝ) + 1) - poleR k := by
    have : (0 : ℝ) ≤ t := t.cast_nonneg
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hW0 _)]
  have : |1 / (((t : ℝ) + 1) - poleR k) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    nlinarith
  have hWt := pow_nonneg hW0 (t + 1)
  calc WrZ ζ ^ (t + 1) * |1 / (((t : ℝ) + 1) - poleR k) ^ 2|
      ≤ WrZ ζ ^ (t + 1) * 1 := by gcongr
    _ = _ := mul_one _

lemma aeval_derivative_eq (R : ℚ[X]) (x : ℝ) : aeval x (derivative R) =
    ∑ n ∈ R.support, ((R.coeff n : ℚ) : ℝ) * ((n : ℝ) * x ^ (n - 1)) := by
  rw [derivative_apply, Polynomial.sum_def, map_sum]
  refine sum_congr rfl (fun n _ => ?_)
  rw [map_mul, aeval_C, map_pow, aeval_X]
  push_cast
  simp [eq_ratCast]
  ring

lemma summable_derivR {W : ℝ} (hW0 : 0 ≤ W) (hW1 : W < 1) (R : ℚ[X]) :
    Summable (fun t : ℕ => W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R)) := by
  simp_rw [aeval_derivative_eq, mul_sum]
  refine summable_sum (fun n _ => ?_)
  cases n with
  | zero => simp
  | succ d =>
    refine ((summable_powW d hW0 hW1).mul_left
      (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- `μ(R) = ∑_{t≥1} w^t R′(t)` for a polynomial `R`, any rational `w ∈ [0, 1)`. -/
lemma muPoly_eq_tsum' {w : ℚ} (h0 : 0 ≤ w) (h1 : w < 1) (R : ℚ[X]) :
    ((muPoly w R : ℚ) : ℝ) = ∑' t : ℕ, (w : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) := by
  have hW0 : (0 : ℝ) ≤ w := by exact_mod_cast h0
  have hW1 : (w : ℝ) < 1 := by exact_mod_cast h1
  simp_rw [aeval_derivative_eq, mul_sum]
  rw [Summable.tsum_finsetSum (fun n _ => ?_)]
  · unfold muPoly
    rw [Polynomial.sum_def]
    push_cast
    refine sum_congr rfl (fun n _ => ?_)
    rw [muMono_eq_tsum h0 h1, ← tsum_mul_left]
    congr 1
    ext t
    ring
  · cases n with
    | zero => simp
    | succ d =>
      refine ((summable_powW d hW0 hW1).mul_left
        (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- **Lemma 1 at `ζ` (pole expansion).** `Λ(g) = A(g) + χ₂(1/ζ) B(g)`. -/
theorem LamZ_eq {ζ : ℚ} (hζ : 1 < ζ) (K : ℕ) (g : ℚ[X]) :
    LamZ ζ K g = (AfunZ ζ K g : ℝ) + chi2 (1 / (ζ : ℝ)) * (BfunZ ζ K g : ℝ) := by
  unfold LamZ
  have hW0 := (WrZ_pos hζ).le
  have hW1 := WrZ_lt_one hζ
  set W : ℝ := WrZ ζ with hWdef
  set R := (g * X) /ₘ Dpoly K
  set c : ℕ → ℝ := fun k => (((g.eval (pole k) * omega K k : ℚ)) : ℝ) with hc
  have hterm : ∀ t : ℕ, W ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1) =
      W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) +
        ∑ k ∈ range K, c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
    intro t
    rw [deriv_gphi K g (by positivity), mul_add, mul_sum]
    refine congrArg _ (sum_congr rfl (fun k _ => by simp only [hc]; ring))
  have hsR := summable_derivR hW0 hW1 R
  have hsP : ∀ k ∈ range K, Summable (fun t : ℕ =>
      c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2)))) :=
    fun k _ => (summable_pole_termZ hζ k).mul_left (c k)
  have hmu : ((muPoly (wtZ ζ) R : ℚ) : ℝ) =
      ∑' t : ℕ, W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) :=
    muPoly_eq_tsum' (wtZ_pos hζ).le (wtZ_lt_one hζ) R
  rw [tsum_congr hterm, hsR.tsum_add (summable_sum hsP), Summable.tsum_finsetSum hsP, ← hmu]
  have hpk : ∀ k ∈ range K, ∑' t : ℕ, c k * (W ^ (t + 1) *
      (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) =
      c k * (-4 * ((ζ : ℝ) ^ (2 * k + 1) * chi2 (1 / (ζ : ℝ)) - (SpartZ ζ k : ℝ))) := by
    intro k _
    rw [tsum_mul_left]
    congr 1
    exact pole_seriesZ hζ k
  rw [sum_congr rfl hpk]
  unfold AfunZ BfunZ
  push_cast
  simp only [hc]
  push_cast
  rw [mul_sum, mul_sum, mul_sum]
  rw [add_assoc]
  congr 1
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  ring

/-- The series defining `Λ(g)` converges. -/
lemma summable_LamZ_summand {ζ : ℚ} (hζ : 1 < ζ) (K : ℕ) (g : ℚ[X]) :
    Summable (fun t : ℕ => WrZ ζ ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1)) := by
  have hW0 := (WrZ_pos hζ).le
  have hW1 := WrZ_lt_one hζ
  set W : ℝ := WrZ ζ
  set R := (g * X) /ₘ Dpoly K
  set c : ℕ → ℝ := fun k => (((g.eval (pole k) * omega K k : ℚ)) : ℝ) with hc
  have hterm : ∀ t : ℕ, W ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1) =
      W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) +
        ∑ k ∈ range K, c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
    intro t
    rw [deriv_gphi K g (by positivity), mul_add, mul_sum]
    refine congrArg _ (sum_congr rfl (fun k _ => by simp only [hc]; ring))
  have hsP : ∀ k ∈ range K, Summable (fun t : ℕ =>
      c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2)))) :=
    fun k _ => (summable_pole_termZ hζ k).mul_left (c k)
  exact ((summable_derivR hW0 hW1 R).add (summable_sum hsP)).congr (fun t => (hterm t).symm)

/-- The Hankel matrix of `Λ` at `ζ` (real), `K = h`. -/
noncomputable def LamMatZ (ζ : ℚ) (h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => LamZ ζ h (X ^ ((i : ℕ) + j))

/-- `Δ_h(χ₂(1/ζ); ζ) = det(Λ(u^{i+j}))`. -/
theorem aeval_chi2_DeltaZ {ζ : ℚ} (hζ : 1 < ζ) (h : ℕ) :
    aeval (chi2 (1 / (ζ : ℝ))) (DeltaZ ζ h) = (LamMatZ ζ h).det := by
  unfold DeltaZ
  rw [AlgHom.map_det]
  · congr 1
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, aeval_X, aeval_C, LamMatZ, LamZ_eq hζ, AmatZ, BmatZ, eq_ratCast]
    ring

end QZ
end Chi2Irr
