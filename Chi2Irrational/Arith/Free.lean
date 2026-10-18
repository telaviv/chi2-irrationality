/-
# The symbolic machine over the free ring `ℚ[q, E]`

`FR = MvPolynomial (Fin 2) ℚ` with `q = X 0` and `E = X 1` (`E` stands for `1/(q²−1)`; no relation is imposed).
* `dCoef n b = Δ^b[x^n](0) = Σ_{k≤b} (−1)^{b−k} C(b,k) k^n` (Newton coefficients);
* `OmegaF b = Ω_b`: `Ω_0 = E`, `Ω_b = q² E^{b+1}` (`= Σ_{t≥1} C(t,b) w^t` once `E = 1/(q²−1)`, `w = q⁻²`);
* `muF R = Σ_d R_d · Σ_{b<d} d · Δ^b[x^{d−1}](0) · Ω_b` (`μ` in Newton form), `AfunF`, `BfunF`, `DeltaF`;
* `evQ q₀ : FR →ₐ[ℚ] ℚ` (`q ↦ q₀`, `E ↦ 1/(q₀²−1)`) maps the symbolic machine to `Machine.lean`'s:
  `map_DeltaF : (DeltaF h).map (evQ q₀) = Delta q₀ h` (via `powSum w n = Σ_b Δ^b[x^n](0) Ω_b(w)`, from the series).
-/
import Chi2Irrational.PoleExpansion

namespace Chi2Irr

open Polynomial Finset

/-- The free ring `ℚ[q, E]`. -/
abbrev FR := MvPolynomial (Fin 2) ℚ

/-- `q`. -/
noncomputable def qF : FR := MvPolynomial.X 0

/-- `E` (stands for `1/(q² − 1)`). -/
noncomputable def EF : FR := MvPolynomial.X 1

/-- `Ω_0 = E`, `Ω_b = q² E^{b+1}`. -/
noncomputable def OmegaF (b : ℕ) : FR := if b = 0 then EF else qF ^ 2 * EF ^ (b + 1)

/-- Newton coefficients `Δ^b[x^n](0)` (integers). -/
def dCoef (n b : ℕ) : ℤ := ∑ k ∈ range (b + 1), (-1 : ℤ) ^ (b - k) * (b.choose k : ℤ) * (k : ℤ) ^ n

/-- `μ(u^d) = Σ_{b<d} d Δ^b[x^{d−1}](0) Ω_b`. -/
noncomputable def muMonoF (d : ℕ) : FR :=
  ∑ b ∈ range d, MvPolynomial.C ((d : ℚ) * (dCoef (d - 1) b : ℚ)) * OmegaF b

/-- `μ` on polynomials, as a `ℚ`-linear map. -/
noncomputable def muLinF : ℚ[X] →ₗ[ℚ] FR :=
  Polynomial.lsum (fun d => (LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (muMonoF d))

noncomputable def muF (R : ℚ[X]) : FR := muLinF R

lemma muF_eq_sum (R : ℚ[X]) : muF R = R.sum (fun d c => c • muMonoF d) := by
  simp [muF, muLinF, Polynomial.lsum_apply]

/-- `S_k(q) = Σ_{j≤k} q^{2(k−j)}/(2j+1)²`. -/
noncomputable def SpartF (k : ℕ) : FR :=
  ∑ j ∈ range (k + 1), qF ^ (2 * (k - j)) * MvPolynomial.C (1 / (2 * (j : ℚ) + 1) ^ 2)

/-- The functional `A` over `FR`. -/
noncomputable def AfunF (K : ℕ) (g : ℚ[X]) : FR :=
  muF ((g * X) /ₘ Dpoly K) +
    4 * ∑ k ∈ range K, MvPolynomial.C (g.eval (pole k) * omega K k) * SpartF k

/-- The functional `B` over `FR`. -/
noncomputable def BfunF (K : ℕ) (g : ℚ[X]) : FR :=
  -4 * ∑ k ∈ range K, MvPolynomial.C (g.eval (pole k) * omega K k) * qF ^ (2 * k + 1)

noncomputable def AmatF (h : ℕ) : Matrix (Fin h) (Fin h) FR := fun i j => AfunF h (X ^ ((i : ℕ) + j))

noncomputable def BmatF (h : ℕ) : Matrix (Fin h) (Fin h) FR := fun i j => BfunF h (X ^ ((i : ℕ) + j))

/-- `Δ_h` over the free ring. -/
noncomputable def DeltaF (h : ℕ) : FR[X] :=
  ((X : FR[X]) • (BmatF h).map C + (AmatF h).map C).det

/-! ### Specialization at an integer `q₀` -/

/-- `q ↦ q₀`, `E ↦ 1/(q₀² − 1)`. -/
noncomputable def evQ (q₀ : ℕ) : FR →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval ![(q₀ : ℚ), 1 / ((q₀ : ℚ) ^ 2 - 1)]

lemma evQ_q (q₀ : ℕ) : evQ q₀ qF = q₀ := by simp [evQ, qF]

lemma evQ_E (q₀ : ℕ) : evQ q₀ EF = 1 / ((q₀ : ℚ) ^ 2 - 1) := by simp [evQ, EF]

lemma evQ_C (q₀ : ℕ) (r : ℚ) : evQ q₀ (MvPolynomial.C r) = r := by simp [evQ]

/-! ### Newton's formula and `μ` at `q₀` -/

lemma dCoef_eq_fwdDiff {R : Type*} [CommRing R] (n b : ℕ) :
    ((fwdDiff (1 : R))^[b] (fun x : R => x ^ n)) 0 = ((dCoef n b : ℤ) : R) := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold dCoef
  push_cast
  refine sum_congr rfl (fun k _ => ?_)
  rw [zsmul_eq_mul]
  push_cast
  simp

lemma dCoef_eq_zero {n b : ℕ} (h : n < b) : dCoef n b = 0 := by
  have := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) (n := b) h) 0
  rw [dCoef_eq_fwdDiff] at this
  simpa using this

/-- Newton: `t^n = Σ_{b≤n} C(t, b) Δ^b[x^n](0)`. -/
lemma newton_pow {R : Type*} [CommRing R] (n t : ℕ) :
    ((t : R)) ^ n = ∑ b ∈ range (n + 1), ((t.choose b : ℕ) : R) * ((dCoef n b : ℤ) : R) := by
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : R)) (fun x : R => x ^ n) t 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  rw [h]
  have hsub1 : range (t + 1) ⊆ range (t + n + 2) := range_subset_range.mpr (by omega)
  have hsub2 : range (n + 1) ⊆ range (t + n + 2) := range_subset_range.mpr (by omega)
  have e : ∀ k ∈ range (t + 1), ((t.choose k : ℕ) : R) * ((fwdDiff (1 : R))^[k] (fun x => x ^ n)) 0 =
      ((t.choose k : ℕ) : R) * ((dCoef n k : ℤ) : R) := fun k _ => by rw [dCoef_eq_fwdDiff]
  rw [Finset.sum_congr rfl e]
  calc ∑ k ∈ range (t + 1), ((t.choose k : ℕ) : R) * ((dCoef n k : ℤ) : R)
      = ∑ k ∈ range (t + n + 2), ((t.choose k : ℕ) : R) * ((dCoef n k : ℤ) : R) :=
        Finset.sum_subset hsub1 (fun k hk hk' => by
          simp only [mem_range] at hk hk'
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
    _ = _ := (Finset.sum_subset hsub2 (fun k hk hk' => by
          simp only [mem_range] at hk hk'
          rw [dCoef_eq_zero (by omega)]; simp)).symm

/-- `Ω_b(w) = Σ_{t≥1} C(t, b) w^t` in closed form. -/
noncomputable def OmR (w : ℝ) (b : ℕ) : ℝ := if b = 0 then w / (1 - w) else w ^ b / (1 - w) ^ (b + 1)

lemma hasSum_choose_shift {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) (b : ℕ) :
    HasSum (fun t : ℕ => ((t + 1).choose b : ℝ) * w ^ (t + 1)) (OmR w b) := by
  have hn : ‖w‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  unfold OmR
  split_ifs with hb
  · subst hb
    have := (hasSum_geometric_of_lt_one h0 h1).mul_left w
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    convert this using 1
    · ext t; ring
    · field_simp
  · -- shift by `b`: the terms with `t + 1 < b` vanish
    have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) b hn).mul_left (w ^ b)
    have hf : HasSum (fun s : ℕ => (s.choose b : ℝ) * w ^ s) (w ^ b / (1 - w) ^ (b + 1)) := by
      rw [← hasSum_nat_add_iff' b]
      have hz : ∑ i ∈ range b, (i.choose b : ℝ) * w ^ i = 0 :=
        Finset.sum_eq_zero (fun i hi => by rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]; simp)
      rw [hz, sub_zero]
      convert hs using 1
      · ext n; rw [pow_add]; ring
      · ring
    have := (hasSum_nat_add_iff' 1).mpr hf
    have hz : ∑ i ∈ range 1, (i.choose b : ℝ) * w ^ i = 0 := by
      simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)]
    rw [hz, sub_zero] at this
    exact this

/-- `Σ_{t≥1} t^n w^t = Σ_{b≤n} Δ^b[x^n](0) Ω_b(w)`. -/
lemma powSum_newton {w : ℚ} (h0 : 0 ≤ w) (h1 : w < 1) (n : ℕ) :
    ((powSum w n : ℚ) : ℝ) = ∑ b ∈ range (n + 1), ((dCoef n b : ℤ) : ℝ) * OmR w b := by
  have hW0 : (0 : ℝ) ≤ w := by exact_mod_cast h0
  have hW1 : (w : ℝ) < 1 := by exact_mod_cast h1
  rw [powSum_eq_tsum h0 h1]
  have hterm : ∀ t : ℕ, ((t : ℝ) + 1) ^ n * (w : ℝ) ^ (t + 1) =
      ∑ b ∈ range (n + 1), ((dCoef n b : ℤ) : ℝ) * (((t + 1).choose b : ℝ) * (w : ℝ) ^ (t + 1)) := by
    intro t
    have := newton_pow (R := ℝ) n (t + 1)
    push_cast at this
    rw [this, Finset.sum_mul]
    exact sum_congr rfl (fun b _ => by ring)
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun b _ => ((hasSum_choose_shift hW0 hW1 b).mul_left _).summable)]
  exact sum_congr rfl (fun b _ => by rw [tsum_mul_left, (hasSum_choose_shift hW0 hW1 b).tsum_eq])

lemma evQ_OmegaF {q₀ : ℕ} (hq : 2 ≤ q₀) (b : ℕ) :
    ((evQ q₀ (OmegaF b) : ℚ) : ℝ) = OmR ((wt q₀ : ℚ) : ℝ) b := by
  have hq' : (2 : ℝ) ≤ q₀ := by exact_mod_cast hq
  have h1 : (q₀ : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (q₀ : ℝ) ≠ 0 := by positivity
  unfold OmegaF OmR wt
  split_ifs with hb
  · rw [evQ_E]; push_cast; field_simp
  · rw [map_mul, map_pow, map_pow, evQ_q, evQ_E]
    push_cast
    have h3 : (1 : ℝ) - 1 / (q₀ : ℝ) ^ 2 = ((q₀ : ℝ) ^ 2 - 1) / (q₀ : ℝ) ^ 2 := by field_simp
    rw [h3]
    simp only [one_pow, div_pow]
    field_simp
    ring

lemma evQ_muMonoF {q₀ : ℕ} (hq : 2 ≤ q₀) (d : ℕ) : evQ q₀ (muMonoF d) = muMono (wt q₀) d := by
  have h0 : (0 : ℚ) ≤ wt q₀ := by unfold wt; positivity
  have h1 : wt q₀ < 1 := by exact_mod_cast wt_lt_one hq
  apply Rat.cast_injective (α := ℝ)
  cases d with
  | zero => simp [muMonoF, muMono]
  | succ n =>
    simp only [muMonoF, muMono, Nat.add_sub_cancel, map_sum, map_mul, evQ_C]
    push_cast
    rw [powSum_newton h0 h1, Finset.mul_sum]
    refine sum_congr rfl (fun b _ => ?_)
    rw [evQ_OmegaF hq]
    ring

lemma evQ_muF {q₀ : ℕ} (hq : 2 ≤ q₀) (R : ℚ[X]) : evQ q₀ (muF R) = muPoly (wt q₀) R := by
  rw [muF_eq_sum, muPoly, Polynomial.sum_def, Polynomial.sum_def, map_sum]
  refine sum_congr rfl (fun d _ => ?_)
  rw [map_smul, evQ_muMonoF hq, smul_eq_mul]

lemma evQ_SpartF (q₀ k : ℕ) : evQ q₀ (SpartF k) = Spart q₀ k := by
  simp only [SpartF, Spart, map_sum, map_mul, map_pow, evQ_q, evQ_C]
  exact sum_congr rfl (fun j _ => by ring)

lemma evQ_AfunF {q₀ : ℕ} (hq : 2 ≤ q₀) (K : ℕ) (g : ℚ[X]) : evQ q₀ (AfunF K g) = Afun q₀ K g := by
  simp only [AfunF, Afun, map_add, map_mul, map_sum, evQ_C, evQ_muF hq, evQ_SpartF, map_ofNat]

lemma evQ_BfunF (q₀ K : ℕ) (g : ℚ[X]) : evQ q₀ (BfunF K g) = Bfun q₀ K g := by
  simp only [BfunF, Bfun, map_mul, map_sum, map_neg, map_pow, evQ_C, evQ_q, map_ofNat]

/-- **The symbolic machine specializes to `Machine.lean`'s.** -/
theorem map_DeltaF {q₀ : ℕ} (hq : 2 ≤ q₀) (h : ℕ) : (DeltaF h).map (evQ q₀) = Delta q₀ h := by
  unfold DeltaF Delta
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, AmatF, BmatF, Amat, Bmat]
  erw [evQ_AfunF hq, evQ_BfunF]

end Chi2Irr
