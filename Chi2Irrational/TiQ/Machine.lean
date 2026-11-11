/-
# The Ti₂ machine: the Theorem Q machine at the signed weight `w = −q⁻²`

Copy of `Machine.lean` (namespace `Chi2Irr.TiQ`), with (RESULT §1):
* `wT q = −1/q²` in place of `wt q = 1/q²`;
* `SpartT q k = Σ_{j≤k} (−1)^{k−j} q^{2(k−j)}/(2j+1)²` (`= (−1)^k q^{2k+1} T♮(2k+1)`, the χ₄-twisted partial sum
  `T♮(M) = Σ_{s odd ≤ M} χ₄(s) q^{−s}/s²`) in place of `Spart`;
* the pole weight `(−1)^k q^{2k+1}` in place of `q^{2k+1}` in `B`.
The generic pieces `pole`, `Dpoly`, `dPrime`, `omega`, `powSum`, `muMono`, `muPoly` of `Machine.lean` are reused.
`TiQ/PoleExpansion.lean` shows `AT(g) + Ti₂(1/q) BT(g) = Σ_{t≥1} w^t (g u / D)′(t)`.
-/
import Chi2Irrational.Machine

namespace Chi2Irr
namespace TiQ

open Polynomial

/-- The signed weight `w = −q⁻²`. -/
def wT (q : ℕ) : ℚ := -1 / (q : ℚ) ^ 2

/-- `S♮_k(q) = Σ_{j≤k} (−1)^{k−j} q^{2(k−j)}/(2j+1)² = (−1)^k q^{2k+1} T♮(2k+1)`. -/
def SpartT (q k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - j) * (q : ℚ) ^ (2 * (k - j)) / (2 * (j : ℚ) + 1) ^ 2

/-- The pole weight `(−1)^k q^{2k+1}`. -/
def poleW (q k : ℕ) : ℚ := (-1 : ℚ) ^ k * (q : ℚ) ^ (2 * k + 1)

/-- The functional `A` (the `X⁰` part of `Λ_X`). -/
noncomputable def AfunT (q K : ℕ) (g : ℚ[X]) : ℚ :=
  muPoly (wT q) ((g * X) /ₘ Dpoly K) +
    4 * ∑ k ∈ Finset.range K, g.eval (pole k) * omega K k * SpartT q k

/-- The functional `B` (the `X¹` part of `Λ_X`). -/
noncomputable def BfunT (q K : ℕ) (g : ℚ[X]) : ℚ :=
  -4 * ∑ k ∈ Finset.range K, g.eval (pole k) * omega K k * poleW q k

/-- The Hankel matrix of `A` with `K = h`. -/
noncomputable def AmatT (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i j => AfunT q h (X ^ ((i : ℕ) + j))

/-- The Hankel matrix of `B` with `K = h`. -/
noncomputable def BmatT (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i j => BfunT q h (X ^ ((i : ℕ) + j))

/-- `Δ^Ti_h(X) = det(A_h + X B_h)`. -/
noncomputable def DeltaT (q h : ℕ) : ℚ[X] :=
  ((X : ℚ[X]) • (BmatT q h).map C + (AmatT q h).map C).det

lemma natDegree_DeltaT_le (q h : ℕ) : (DeltaT q h).natDegree ≤ h := by
  have := natDegree_det_X_add_C_le (BmatT q h) (AmatT q h)
  simpa [DeltaT] using this

/-- Evaluating `Δ^Ti_h` at a rational `r` gives `det(A_h + r B_h)`. -/
lemma eval_DeltaT (q h : ℕ) (r : ℚ) : (DeltaT q h).eval r = (AmatT q h + r • BmatT q h).det := by
  unfold DeltaT
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  ring

end TiQ
end Chi2Irr
