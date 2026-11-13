/-
# Lemma M, part 2: the Mahler Gram matrix and the block matrix (RESULT §1 step 2)

* `DeltaT_eq_Cb`: `Δ^Ti_h = (Π_{i<h} i!)² · det(Λ_X(Cb i · Cb j))` (Gram identity in the binomial basis; `Cb i` has leading
  coefficient `1/i!`).
* `BfunT_Cb`: `B(Cb i · Cb j) = (Aᵀ O A)_{ij}` (Newton's forward formula for `k ↦ C_i(x_k)` at `k < h`).
* `HM_eq`: `Λ_X(Cb i · Cb j) = Em(θ) + (X − θ)·(Aᵀ O A)` as polynomials in `X`, for any rational `θ`.
* `det_block`: for matrices over a commutative ring, the `3 × 3` block matrix
  `N = [[E, Aᵀ, 0], [0, 1, −Y·O], [−A, 0, 1]]` has `det N = det(E + Y · Aᵀ O A)` (Schur complement).
-/
import Chi2Irrational.TiQ.M.Binom

namespace Chi2Irr
namespace TiQ
namespace M

open Polynomial Finset

/-- The Mahler Gram matrix `Λ_X(Cb i · Cb j)`. -/
noncomputable def HM (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] := Matrix.of fun i j => LamPT q h (Cb i * Cb j)

lemma gram_det_CoefM_Cb (h : ℕ) :
    (CoefM (fun i : Fin h => Cb i)).det = ∏ i ∈ range h, ((i.factorial : ℕ) : ℚ)⁻¹ := by
  have hM : CoefM (fun i : Fin h => Cb i) =
      Matrix.diagonal (fun i : Fin h => (((i : ℕ).factorial : ℕ) : ℚ)⁻¹) *
        CoefM (fun i : Fin h => descPochhammer ℚ (i : ℕ)) := by
    ext i d
    simp [CoefM, Cb, Matrix.diagonal_mul, coeff_C_mul]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal,
    det_CoefM_monic _ (fun i => descPochhammer_natDegree ℚ _) (fun i => monic_descPochhammer ℚ _), mul_one]
  exact Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ)⁻¹) h

lemma gram_newton (i : ℕ) {h k : ℕ} (hk : k < h) :
    (Cb i).eval (pole k) = ∑ n ∈ range h, ((k.choose n : ℕ) : ℚ) * fd n (fun k => (Cb i).eval (pole k)) := by
  have hN := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) (fun k : ℕ => (Cb i).eval (pole k)) k 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at hN
  rw [hN]
  refine sum_subset (fun n hn => mem_range.2 (lt_of_lt_of_le (mem_range.1 hn) hk)) ?_
  intro n _ hn
  rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]
  simp

theorem DeltaT_eq_Cb (q h : ℕ) :
    DeltaT q h = C ((∏ i ∈ range h, ((i.factorial : ℕ) : ℚ)) ^ 2) * (HM q h).det := by
  have hdeg : ∀ i : Fin h, (Cb i).natDegree < h := fun i => by rw [Cb_natDegree]; exact i.isLt
  have hG := Gram2_eqT q (fun i : Fin h => Cb i) (fun i => Cb i) hdeg hdeg
  have hHM : HM q h = Matrix.of (fun i j : Fin h => LamPT q h (Cb i * Cb j)) := rfl
  rw [hHM, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_map_C, gram_det_CoefM_Cb, HPmT_eq]
  have hP : (∏ i ∈ range h, ((i.factorial : ℕ) : ℚ)) * ∏ i ∈ range h, ((i.factorial : ℕ) : ℚ)⁻¹ = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun i _ => mul_inv_cancel₀ (by positivity)
  have e : ∀ (P Q : ℚ) (D : ℚ[X]), C (P ^ 2) * (C Q * D * C Q) = C ((P * Q) ^ 2) * D := by
    intro P Q D; simp only [map_pow, map_mul]; ring
  rw [e, hP]
  simp [DeltaT]

theorem BfunT_Cb (q h : ℕ) (i j : Fin h) :
    BfunT q h (Cb i * Cb j) = ((Am h).transpose * Om q h * Am h) i j := by
  have key : ∀ k ∈ range h, ∀ i : Fin h,
      (Cb i).eval (pole k) = ∑ n : Fin h, ((k.choose n : ℕ) : ℚ) * Am h n i := by
    intro k hk i
    rw [gram_newton i (mem_range.1 hk)]
    exact (Fin.sum_univ_eq_sum_range
      (fun n => ((k.choose n : ℕ) : ℚ) * fd n (fun k => (Cb i).eval (pole k))) h).symm
  unfold BfunT
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Om]
  rw [mul_sum, sum_congr rfl (fun k hk => by rw [eval_mul, key k hk i, key k hk j])]
  simp only [sum_mul, mul_sum, betaK]
  rw [sum_comm]
  refine sum_congr rfl fun n' _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun n _ => sum_congr rfl fun k _ => by ring

theorem HM_eq (q h : ℕ) (θ : ℚ) :
    HM q h = (Emt q h θ).map C + (X - C θ) • ((Am h).transpose * Om q h * Am h).map C := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, ← BfunT_Cb]
  simp only [HM, Matrix.of_apply, LamPT_apply, Emt, smul_eq_mul, map_add, map_mul]
  ring_nf

/-- The `3 × 3` block matrix of the Leibniz bound. -/
def Nblk {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (E A O : Matrix ι ι R) (Y : R) :
    Matrix (ι ⊕ (ι ⊕ ι)) (ι ⊕ (ι ⊕ ι)) R :=
  Matrix.fromBlocks E (Matrix.fromCols A.transpose 0) (Matrix.fromRows 0 (-A))
    (Matrix.fromBlocks 1 (-(Y • O)) 0 1)

theorem det_block {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (E A O : Matrix ι ι R) (Y : R) :
    (Nblk E A O Y).det = (E + Y • (A.transpose * O * A)).det := by
  let Dm : Matrix (ι ⊕ ι) (ι ⊕ ι) R := Matrix.fromBlocks 1 (-(Y • O)) 0 1
  let Di : Matrix (ι ⊕ ι) (ι ⊕ ι) R := Matrix.fromBlocks 1 (Y • O) 0 1
  have h1 : Di * Dm = 1 := by
    simp [Di, Dm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have h2 : Dm * Di = 1 := by
    simp [Di, Dm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  let _ : Invertible Dm := ⟨Di, h1, h2⟩
  have hN : Nblk E A O Y = Matrix.fromBlocks E (Matrix.fromCols A.transpose 0) (Matrix.fromRows 0 (-A)) Dm := rfl
  have hdet : Dm.det = 1 := by simp [Dm]
  rw [hN, Matrix.det_fromBlocks₂₂, hdet, one_mul, show ⅟Dm = Di from rfl]
  congr 1
  simp only [Di, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp [Matrix.mul_assoc]

end M
end TiQ
end Chi2Irr
