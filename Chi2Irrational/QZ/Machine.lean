/-
# The χ₂ Hankel machine at a rational point `ζ` (`pilot_chi2_2q/RESULT.md` §1)

`Machine.lean` builds `Δ_h` for an integer `q`. Here the same machine is built at a rational `ζ` with `z = 1/ζ`
(for Theorem Q4′, `ζ = q/2`, `z = 2/q`): `w = ζ⁻²`, `S_k(ζ) = Σ_{j≤k} ζ^{2(k−j)}/(2j+1)²`,
`A(g) = μ((g u) div D) + 4 Σ_k g(x_k) ω_k S_k(ζ)`, `B(g) = −4 Σ_k g(x_k) ω_k ζ^{2k+1}`,
`Δ_h(X; ζ) = det (A(u^{i+j}) + X B(u^{i+j}))_{i,j<h}`. The poles, `D`, `ω_k`, `powSum`, `muMono`, `muPoly` are those of
`Machine.lean` (they do not depend on `q`).

* `DeltaZ_natCast`: at an integer `ζ = q` this is `Machine.lean`'s `Delta q h` (definitionally).
* `map_DeltaF_Z`: the symbolic machine `DeltaF h` over `FR = ℚ[q, E]` (`Arith/Free.lean`) specialises to `DeltaZ ζ h`
  under `q ↦ ζ`, `E ↦ 1/(ζ² − 1)`, for every rational `ζ > 1`. All `p`-adic bounds of `Arith/*` are Gauss-norm bounds on
  `DeltaF`, so they transfer to `DeltaZ ζ` through this identity (RESULT §1: "statements in ℚ[ζ, X] followed by a
  specialisation").
-/
import Chi2Irrational.Arith.Free

namespace Chi2Irr
namespace QZ

open Polynomial Finset

/-- `S_k(ζ) = ∑_{j≤k} ζ^{2(k−j)}/(2j+1)²`. -/
def SpartZ (ζ : ℚ) (k : ℕ) : ℚ := ∑ j ∈ Finset.range (k + 1), ζ ^ (2 * (k - j)) / (2 * (j : ℚ) + 1) ^ 2

/-- The weight `w = ζ⁻²`. -/
def wtZ (ζ : ℚ) : ℚ := 1 / ζ ^ 2

/-- The functional `A` at `ζ`. -/
noncomputable def AfunZ (ζ : ℚ) (K : ℕ) (g : ℚ[X]) : ℚ :=
  muPoly (wtZ ζ) ((g * X) /ₘ Dpoly K) +
    4 * ∑ k ∈ Finset.range K, g.eval (pole k) * omega K k * SpartZ ζ k

/-- The functional `B` at `ζ`. -/
noncomputable def BfunZ (ζ : ℚ) (K : ℕ) (g : ℚ[X]) : ℚ :=
  -4 * ∑ k ∈ Finset.range K, g.eval (pole k) * omega K k * ζ ^ (2 * k + 1)

/-- The Hankel matrix of `A` with `K = h`. -/
noncomputable def AmatZ (ζ : ℚ) (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i j => AfunZ ζ h (X ^ ((i : ℕ) + j))

/-- The Hankel matrix of `B` with `K = h`. -/
noncomputable def BmatZ (ζ : ℚ) (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i j => BfunZ ζ h (X ^ ((i : ℕ) + j))

/-- `Δ_h(X; ζ) = det(A_h + X B_h)`. -/
noncomputable def DeltaZ (ζ : ℚ) (h : ℕ) : ℚ[X] :=
  ((X : ℚ[X]) • (BmatZ ζ h).map C + (AmatZ ζ h).map C).det

/-- At an integer point the machine is `Machine.lean`'s. -/
lemma DeltaZ_natCast (q h : ℕ) : DeltaZ (q : ℚ) h = Delta q h := rfl

lemma natDegree_DeltaZ_le (ζ : ℚ) (h : ℕ) : (DeltaZ ζ h).natDegree ≤ h := by
  have := natDegree_det_X_add_C_le (BmatZ ζ h) (AmatZ ζ h)
  simpa [DeltaZ] using this

/-- Evaluating `Δ_h(·; ζ)` at a rational `r` gives `det(A_h + r B_h)`. -/
lemma eval_DeltaZ (ζ : ℚ) (h : ℕ) (r : ℚ) : (DeltaZ ζ h).eval r = (AmatZ ζ h + r • BmatZ ζ h).det := by
  unfold DeltaZ
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  ring

/-! ### Basic facts on `w = ζ⁻²` -/

lemma wtZ_pos {ζ : ℚ} (hζ : 1 < ζ) : 0 < wtZ ζ := by unfold wtZ; have : 0 < ζ := by linarith
                                                     positivity

lemma wtZ_lt_one {ζ : ℚ} (hζ : 1 < ζ) : wtZ ζ < 1 := by
  unfold wtZ
  have h1 : 1 < ζ ^ 2 := by nlinarith
  rw [div_lt_one (by linarith)]; exact h1

lemma zsq_sub_one_ne_zero {ζ : ℚ} (hζ : 1 < ζ) : ζ ^ 2 - 1 ≠ 0 := by
  have : 1 < ζ ^ 2 := by nlinarith
  linarith

/-! ### Specialisation of the symbolic machine at `ζ` -/

/-- `q ↦ ζ`, `E ↦ 1/(ζ² − 1)`. -/
noncomputable def evZ (ζ : ℚ) : FR →ₐ[ℚ] ℚ := MvPolynomial.aeval ![ζ, 1 / (ζ ^ 2 - 1)]

lemma evZ_q (ζ : ℚ) : evZ ζ qF = ζ := by simp [evZ, qF]

lemma evZ_E (ζ : ℚ) : evZ ζ EF = 1 / (ζ ^ 2 - 1) := by simp [evZ, EF]

lemma evZ_C (ζ : ℚ) (r : ℚ) : evZ ζ (MvPolynomial.C r) = r := by simp [evZ]

lemma evZ_OmegaF {ζ : ℚ} (hζ : 1 < ζ) (b : ℕ) :
    ((evZ ζ (OmegaF b) : ℚ) : ℝ) = OmR ((wtZ ζ : ℚ) : ℝ) b := by
  have hz1 : (1 : ℝ) < (ζ : ℝ) := by exact_mod_cast hζ
  have h1 : (ζ : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (ζ : ℝ) ≠ 0 := by positivity
  unfold OmegaF OmR wtZ
  split_ifs with hb
  · rw [evZ_E]; push_cast; field_simp
  · rw [map_mul, map_pow, map_pow, evZ_q, evZ_E]
    push_cast
    have h3 : (1 : ℝ) - 1 / (ζ : ℝ) ^ 2 = ((ζ : ℝ) ^ 2 - 1) / (ζ : ℝ) ^ 2 := by field_simp
    rw [h3]
    simp only [one_pow, div_pow]
    field_simp
    ring

lemma evZ_muMonoF {ζ : ℚ} (hζ : 1 < ζ) (d : ℕ) : evZ ζ (muMonoF d) = muMono (wtZ ζ) d := by
  have h0 : (0 : ℚ) ≤ wtZ ζ := (wtZ_pos hζ).le
  have h1 : wtZ ζ < 1 := wtZ_lt_one hζ
  apply Rat.cast_injective (α := ℝ)
  cases d with
  | zero => simp [muMonoF, muMono]
  | succ n =>
    simp only [muMonoF, muMono, Nat.add_sub_cancel, map_sum, map_mul, evZ_C]
    push_cast
    rw [powSum_newton h0 h1, Finset.mul_sum]
    refine sum_congr rfl (fun b _ => ?_)
    rw [evZ_OmegaF hζ]
    ring

lemma evZ_muF {ζ : ℚ} (hζ : 1 < ζ) (R : ℚ[X]) : evZ ζ (muF R) = muPoly (wtZ ζ) R := by
  rw [muF_eq_sum, muPoly, Polynomial.sum_def, Polynomial.sum_def, map_sum]
  refine sum_congr rfl (fun d _ => ?_)
  rw [map_smul, evZ_muMonoF hζ, smul_eq_mul]

lemma evZ_SpartF (ζ : ℚ) (k : ℕ) : evZ ζ (SpartF k) = SpartZ ζ k := by
  simp only [SpartF, SpartZ, map_sum, map_mul, map_pow, evZ_q, evZ_C]
  exact sum_congr rfl (fun j _ => by ring)

lemma evZ_AfunF {ζ : ℚ} (hζ : 1 < ζ) (K : ℕ) (g : ℚ[X]) : evZ ζ (AfunF K g) = AfunZ ζ K g := by
  simp only [AfunF, AfunZ, map_add, map_mul, map_sum, evZ_C, evZ_muF hζ, evZ_SpartF, map_ofNat]

lemma evZ_BfunF (ζ : ℚ) (K : ℕ) (g : ℚ[X]) : evZ ζ (BfunF K g) = BfunZ ζ K g := by
  simp only [BfunF, BfunZ, map_mul, map_sum, map_neg, map_pow, evZ_C, evZ_q, map_ofNat]

/-- **The symbolic machine specialises to `DeltaZ ζ`** for every rational `ζ > 1`. -/
theorem map_DeltaF_Z {ζ : ℚ} (hζ : 1 < ζ) (h : ℕ) : (DeltaF h).map (evZ ζ) = DeltaZ ζ h := by
  unfold DeltaF DeltaZ
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, AmatF, BmatF, AmatZ, BmatZ]
  erw [evZ_AfunF hζ, evZ_BfunF]

lemma coeff_DeltaZ_eq {ζ : ℚ} (hζ : 1 < ζ) (h k : ℕ) :
    (DeltaZ ζ h).coeff k = MvPolynomial.aeval ![ζ, 1 / (ζ ^ 2 - 1)] ((DeltaF h).coeff k) := by
  rw [← map_DeltaF_Z hζ, Polynomial.coeff_map]; rfl

end QZ
end Chi2Irr
