/-
# Lemma 1: the pole expansion

`Λ(g) := ∑_{t≥1} w^t (g(u)·u/D(u))′|_{u=t}` (the real moment functional of the machine) equals
`A(g) + χ₂(1/q)·B(g)` with the rational functionals `Afun`, `Bfun` of `Machine.lean`.
Hence `Δ_h(χ₂(1/q)) = det(Λ(u^{i+j}))_{i,j<h}` (`aeval_chi2_Delta`).

Proof: partial fractions `g u/D = R + ∑_k g(x_k) ω_k/(u − x_k)` (Lagrange interpolation of the remainder),
differentiate termwise, and sum with `powSum_eq_tsum` and `pole_series`.
-/
import Chi2Irrational.PoleSeries
import Chi2Irrational.Criterion

namespace Chi2Irr

open Polynomial Finset Filter Topology

/-- The real moment functional `Λ(g) = ∑_{t≥1} w^t (g u / D)′(t)`, `w = q⁻²`, `K` poles. -/
noncomputable def Lam (q K : ℕ) (g : ℚ[X]) : ℝ :=
  ∑' t : ℕ, ((wt q : ℚ) : ℝ) ^ (t + 1) *
    deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1)

/-- Partial fractions over a field, from the first barycentric form of Lagrange interpolation. -/
lemma eval_eq_nodal_mul {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → F) (hvs : Set.InjOn v s) (P : F[X]) {u : F} (hu : ∀ i ∈ s, u ≠ v i) :
    P.eval u = (Lagrange.nodal s v).eval u * ((P /ₘ Lagrange.nodal s v).eval u +
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (u - v i)⁻¹ * P.eval (v i)) := by
  set N := Lagrange.nodal s v with hNdef
  have hN : N.Monic := Lagrange.nodal_monic
  have hdecomp := modByMonic_add_div P N
  have hdeg : (P %ₘ N).degree < #s := by
    rw [← Lagrange.degree_nodal (s := s) (v := v)]
    exact degree_modByMonic_lt P hN
  have hr := Lagrange.eq_interpolate hvs hdeg
  have hnode : ∀ i ∈ s, (P %ₘ N).eval (v i) = P.eval (v i) := by
    intro i hi
    conv_rhs => rw [← hdecomp]
    rw [eval_add, eval_mul, hNdef, Lagrange.eval_nodal_at_node hi, zero_mul, add_zero]
  conv_lhs => rw [← hdecomp]
  rw [eval_add, eval_mul, hr, Lagrange.eval_interpolate_not_at_node _ hu]
  have hsum : ∑ i ∈ s, Lagrange.nodalWeight s v i * (u - v i)⁻¹ *
      (fun i => (P %ₘ N).eval (v i)) i =
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (u - v i)⁻¹ * P.eval (v i) :=
    sum_congr rfl (fun i hi => by simp only [hnode i hi])
  rw [hsum]
  ring

/-- The real nodes `x_k`. -/
noncomputable def poleR (k : ℕ) : ℝ := ((pole k : ℚ) : ℝ)

lemma poleR_neg (k : ℕ) : poleR k < 0 := by
  unfold poleR pole
  push_cast
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  linarith

lemma poleR_injective : Function.Injective poleR := by
  intro a b hab
  unfold poleR pole at hab
  push_cast at hab
  exact_mod_cast (by linarith : (a : ℝ) = b)

lemma map_Dpoly (K : ℕ) : (Dpoly K).map (algebraMap ℚ ℝ) = Lagrange.nodal (range K) poleR := by
  unfold Dpoly Lagrange.nodal poleR
  rw [Polynomial.map_prod]
  refine prod_congr rfl (fun _ _ => ?_)
  rw [Polynomial.map_sub, map_X, map_C]
  rfl

lemma Dpoly_monic (K : ℕ) : (Dpoly K).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

lemma nodalWeight_eq (K k : ℕ) :
    Lagrange.nodalWeight (range K) poleR k = (((dPrime K k : ℚ) : ℝ))⁻¹ := by
  unfold Lagrange.nodalWeight dPrime poleR
  rw [prod_inv_distrib]
  push_cast
  rfl

lemma aeval_Dpoly_pos (K : ℕ) {u : ℝ} (hu : 0 < u) : 0 < aeval u (Dpoly K) := by
  rw [aeval_def, eval₂_eq_eval_map, map_Dpoly, Lagrange.eval_nodal]
  exact prod_pos (fun k _ => by have := poleR_neg k; linarith)

/-- **Partial fractions for the machine.** For `u > 0`:
`g(u) u / D(u) = R(u) + ∑_k g(x_k) ω_k / (u − x_k)`, `R = (g X) div D`. -/
lemma partialFrac (K : ℕ) (g : ℚ[X]) {u : ℝ} (hu : 0 < u) :
    aeval u g * u / aeval u (Dpoly K) = aeval u ((g * X) /ₘ Dpoly K) +
      ∑ k ∈ range K, (((g.eval (pole k) * omega K k : ℚ)) : ℝ) * (u - poleR k)⁻¹ := by
  have hD := aeval_Dpoly_pos K hu
  set P : ℝ[X] := (g * X).map (algebraMap ℚ ℝ)
  have hu' : ∀ k ∈ range K, u ≠ poleR k := fun k _ => by have := poleR_neg k; intro h; linarith
  have key := eval_eq_nodal_mul (range K) poleR poleR_injective.injOn P hu'
  have hPu : P.eval u = aeval u g * u := by
    simp [P, eval_map, ← aeval_def]
  have hND : (Lagrange.nodal (range K) poleR).eval u = aeval u (Dpoly K) := by
    rw [← map_Dpoly, eval_map, ← aeval_def]
  have hdiv : (P /ₘ Lagrange.nodal (range K) poleR).eval u = aeval u ((g * X) /ₘ Dpoly K) := by
    rw [← map_Dpoly, ← map_divByMonic _ (Dpoly_monic K), eval_map, ← aeval_def]
  rw [hPu, hND, hdiv] at key
  rw [key, mul_div_cancel_left₀ _ hD.ne']
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  rw [nodalWeight_eq]
  have hPk : P.eval (poleR k) = ((g.eval (pole k) : ℚ) : ℝ) * poleR k := by
    simp only [P, eval_map, poleR]
    rw [← aeval_def, aeval_ratCast, eval_mul, eval_X]
    push_cast
    rfl
  rw [hPk]
  unfold omega
  push_cast
  unfold poleR
  ring

/-- The derivative of `g u / D` at `t > 0`. -/
lemma deriv_gphi (K : ℕ) (g : ℚ[X]) {t : ℝ} (ht : 0 < t) :
    deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) t =
      aeval t (derivative ((g * X) /ₘ Dpoly K)) +
        ∑ k ∈ range K, (((g.eval (pole k) * omega K k : ℚ)) : ℝ) * (-(1 / (t - poleR k) ^ 2)) := by
  have heq : (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) =ᶠ[𝓝 t]
      (fun u : ℝ => aeval u ((g * X) /ₘ Dpoly K) +
        ∑ k ∈ range K, (((g.eval (pole k) * omega K k : ℚ)) : ℝ) * (u - poleR k)⁻¹) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact partialFrac K g hu
  rw [heq.deriv_eq]
  have hne : ∀ k, t - poleR k ≠ 0 := fun k => by have := poleR_neg k; intro h; linarith
  have hsum : HasDerivAt (fun u : ℝ => ∑ k ∈ range K,
      (((g.eval (pole k) * omega K k : ℚ)) : ℝ) * (u - poleR k)⁻¹)
      (∑ k ∈ range K, (((g.eval (pole k) * omega K k : ℚ)) : ℝ) * (-(1 / (t - poleR k) ^ 2))) t := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have h1 : HasDerivAt (fun u : ℝ => (u - poleR k)⁻¹) (-(1 : ℝ) / (t - poleR k) ^ 2) t :=
      ((hasDerivAt_id t).sub_const (poleR k)).inv (hne k)
    have h2 := h1.const_mul ((((g.eval (pole k) * omega K k : ℚ)) : ℝ))
    convert h2 using 2
    ring
  exact ((Polynomial.hasDerivAt_aeval _ t).add hsum).deriv

lemma summable_geomW {W : ℝ} (h0 : 0 ≤ W) (h1 : W < 1) : Summable (fun t : ℕ => W ^ (t + 1)) := by
  simpa using summable_powW 0 h0 h1

lemma wt_nonneg (q : ℕ) : (0 : ℝ) ≤ ((wt q : ℚ) : ℝ) := by
  unfold wt; push_cast; positivity

lemma wt_lt_one {q : ℕ} (hq : 2 ≤ q) : ((wt q : ℚ) : ℝ) < 1 := by
  unfold wt
  push_cast
  have : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  rw [div_lt_one (by positivity)]
  linarith

lemma summable_pole_term {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    Summable (fun t : ℕ => ((wt q : ℚ) : ℝ) ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
  refine Summable.of_norm_bounded (summable_geomW (wt_nonneg q) (wt_lt_one hq)) (fun t => ?_)
  have hk := poleR_neg k
  have h1 : (1 : ℝ) ≤ ((t : ℝ) + 1) - poleR k := by
    have : (0 : ℝ) ≤ t := t.cast_nonneg
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg (wt_nonneg q) _)]
  have : |1 / (((t : ℝ) + 1) - poleR k) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    nlinarith
  have hWt := pow_nonneg (wt_nonneg q) (t + 1)
  calc ((wt q : ℚ) : ℝ) ^ (t + 1) * |1 / (((t : ℝ) + 1) - poleR k) ^ 2|
      ≤ ((wt q : ℚ) : ℝ) ^ (t + 1) * 1 := by gcongr
    _ = _ := mul_one _

/-- `μ(u^n)` as a series. -/
lemma muMono_eq_tsum {w : ℚ} (h0 : 0 ≤ w) (h1 : w < 1) (n : ℕ) :
    ((muMono w n : ℚ) : ℝ) = ∑' t : ℕ, (w : ℝ) ^ (t + 1) * ((n : ℝ) * ((t : ℝ) + 1) ^ (n - 1)) := by
  cases n with
  | zero => simp [muMono]
  | succ d =>
    simp only [muMono, Nat.add_sub_cancel]
    push_cast
    rw [powSum_eq_tsum h0 h1, ← tsum_mul_left]
    congr 1
    ext t
    ring

/-- `μ(R) = ∑_{t≥1} w^t R′(t)` for a polynomial `R`. -/
lemma muPoly_eq_tsum {q : ℕ} (hq : 2 ≤ q) (R : ℚ[X]) :
    ((muPoly (wt q) R : ℚ) : ℝ) =
      ∑' t : ℕ, ((wt q : ℚ) : ℝ) ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) := by
  have h0 : (0 : ℚ) ≤ wt q := by unfold wt; positivity
  have h1 : wt q < 1 := by exact_mod_cast wt_lt_one hq
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
    rw [muMono_eq_tsum h0 h1, ← tsum_mul_left]
    congr 1
    ext t
    ring
  · cases n with
    | zero => simp
    | succ d =>
      refine ((summable_powW d (wt_nonneg q) (wt_lt_one hq)).mul_left
        (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- **Lemma 1 (pole expansion).** `Λ(g) = A(g) + χ₂(1/q) B(g)`. -/
theorem Lam_eq {q : ℕ} (hq : 2 ≤ q) (K : ℕ) (g : ℚ[X]) :
    Lam q K g = (Afun q K g : ℝ) + chi2 (1 / (q : ℝ)) * (Bfun q K g : ℝ) := by
  unfold Lam
  have hW0 := wt_nonneg q
  have hW1 := wt_lt_one hq
  set W : ℝ := ((wt q : ℚ) : ℝ)
  set R := (g * X) /ₘ Dpoly K
  set c : ℕ → ℝ := fun k => (((g.eval (pole k) * omega K k : ℚ)) : ℝ) with hc
  have hterm : ∀ t : ℕ, W ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1) =
      W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) +
        ∑ k ∈ range K, c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
    intro t
    rw [deriv_gphi K g (by positivity), mul_add, mul_sum]
    refine congrArg _ (sum_congr rfl (fun k _ => by simp only [hc]; ring))
  have hsR : Summable (fun t : ℕ => W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R)) := by
    by_contra hns
    have h := muPoly_eq_tsum hq R
    -- summability is part of the finite-sum argument; re-derive it directly
    apply hns
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
    refine summable_sum (fun n _ => ?_)
    cases n with
    | zero => simp
    | succ d =>
      refine ((summable_powW d hW0 hW1).mul_left
        (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have hsP : ∀ k ∈ range K, Summable (fun t : ℕ =>
      c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2)))) :=
    fun k _ => (summable_pole_term hq k).mul_left (c k)
  rw [tsum_congr hterm, hsR.tsum_add (summable_sum hsP), Summable.tsum_finsetSum hsP,
    ← muPoly_eq_tsum hq R]
  have hpk : ∀ k ∈ range K, ∑' t : ℕ, c k * (W ^ (t + 1) *
      (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) =
      c k * (-4 * ((q : ℝ) ^ (2 * k + 1) * chi2 (1 / (q : ℝ)) - (Spart q k : ℝ))) := by
    intro k _
    rw [tsum_mul_left]
    congr 1
    exact pole_series hq k
  rw [sum_congr rfl hpk]
  unfold Afun Bfun
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
lemma summable_Lam_summand {q : ℕ} (hq : 2 ≤ q) (K : ℕ) (g : ℚ[X]) :
    Summable (fun t : ℕ => ((wt q : ℚ) : ℝ) ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1)) := by
  have hW0 := wt_nonneg q
  have hW1 := wt_lt_one hq
  set W : ℝ := ((wt q : ℚ) : ℝ)
  set R := (g * X) /ₘ Dpoly K
  set c : ℕ → ℝ := fun k => (((g.eval (pole k) * omega K k : ℚ)) : ℝ) with hc
  have hterm : ∀ t : ℕ, W ^ (t + 1) *
      deriv (fun u : ℝ => aeval u g * u / aeval u (Dpoly K)) ((t : ℝ) + 1) =
      W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R) +
        ∑ k ∈ range K, c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2))) := by
    intro t
    rw [deriv_gphi K g (by positivity), mul_add, mul_sum]
    refine congrArg _ (sum_congr rfl (fun k _ => by simp only [hc]; ring))
  have hsR : Summable (fun t : ℕ => W ^ (t + 1) * aeval ((t : ℝ) + 1) (derivative R)) := by
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
    refine summable_sum (fun n _ => ?_)
    cases n with
    | zero => simp
    | succ d =>
      refine ((summable_powW d hW0 hW1).mul_left
        (((R.coeff (d + 1) : ℚ) : ℝ) * ((d : ℝ) + 1))).congr (fun t => ?_)
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have hsP : ∀ k ∈ range K, Summable (fun t : ℕ =>
      c k * (W ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - poleR k) ^ 2)))) :=
    fun k _ => (summable_pole_term hq k).mul_left (c k)
  exact (hsR.add (summable_sum hsP)).congr (fun t => (hterm t).symm)

/-- The Hankel matrix of `Λ` (real), `K = h`. -/
noncomputable def LamMat (q h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => Lam q h (X ^ ((i : ℕ) + j))

/-- `Δ_h(χ₂(1/q)) = det(Λ(u^{i+j}))`. -/
theorem aeval_chi2_Delta {q : ℕ} (hq : 2 ≤ q) (h : ℕ) :
    aeval (chi2 (1 / (q : ℝ))) (Delta q h) = (LamMat q h).det := by
  unfold Delta
  rw [AlgHom.map_det]
  · congr 1
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, aeval_X, aeval_C, LamMat, Lam_eq hq, Amat, Bmat, eq_ratCast]
    ring

end Chi2Irr
