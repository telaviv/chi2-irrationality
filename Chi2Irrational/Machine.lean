/-
# The zero-free, unshifted χ₂ Hankel machine

For an integer `q ≥ 2` (we use `q = 3, 5`), `w = q⁻²` and `K = h` poles `x_k = −(k + ½)`, `k < K`:
* `D(u) = ∏_{k<K} (u − x_k)`, `D′(x_k) = ∏_{m≠k} (x_k − x_m)`, `ω_k = x_k / D′(x_k)`;
* `S_k(q) = ∑_{j≤k} q^{2(k−j)}/(2j+1)²` (= `q^{2k+1} T(2k+1)`);
* `μ(u^d) = d ∑_{t≥1} t^{d−1} w^t` (rational, via the recurrence `powSum`), extended linearly to `μ` on `ℚ[X]`;
* `A(g) = μ((g u) div D) + 4 ∑_k g(x_k) ω_k S_k`, `B(g) = −4 ∑_k g(x_k) ω_k q^{2k+1}`;
* `Δ_h(X) = det (A(u^{i+j}) + X B(u^{i+j}))_{i,j<h} ∈ ℚ[X]`.

Lemma 1 (`PoleExpansion.lean`) shows `A(g) + χ₂(1/q) B(g) = ∑_{t≥1} w^t (g u / D)′(t)`.
-/
import Mathlib

namespace Chi2Irr

open Polynomial

/-- The poles `x_k = −(k + ½)`. -/
def pole (k : ℕ) : ℚ := -((k : ℚ) + 1 / 2)

/-- `D(u) = ∏_{k<K} (u − x_k)`. -/
noncomputable def Dpoly (K : ℕ) : ℚ[X] := ∏ k ∈ Finset.range K, (X - C (pole k))

/-- `D′(x_k) = ∏_{m<K, m≠k} (x_k − x_m)`. -/
def dPrime (K k : ℕ) : ℚ := ∏ m ∈ (Finset.range K).erase k, (pole k - pole m)

/-- The residue weight `ω_k = x_k / D′(x_k)` of `u/D(u)` at `x_k`. -/
def omega (K k : ℕ) : ℚ := pole k / dPrime K k

/-- `S_k(q) = ∑_{j≤k} q^{2(k−j)}/(2j+1)² = q^{2k+1} T(2k+1)`. -/
def Spart (q k : ℕ) : ℚ := ∑ j ∈ Finset.range (k + 1), (q : ℚ) ^ (2 * (k - j)) / (2 * (j : ℚ) + 1) ^ 2

/-- The weight `w = q⁻²`. -/
def wt (q : ℕ) : ℚ := 1 / (q : ℚ) ^ 2

/-- `powSum w n = ∑_{t≥1} t^n w^t`, via `s₀ = w/(1−w)` and
`(1 − w) s_{n+1} = ∑_{j≤n} C(n+1, j) (−1)^{n−j} s_j`. -/
def powSum (w : ℚ) : ℕ → ℚ
  | 0 => w / (1 - w)
  | n + 1 => (∑ j : Fin (n + 1), ((n + 1).choose j : ℚ) * (-1) ^ (n - (j : ℕ)) * powSum w j) / (1 - w)
termination_by n => n
decreasing_by exact j.isLt

/-- `μ(u^d) = ∑_{t≥1} w^t (u^d)′(t) = d · powSum w (d − 1)`. -/
def muMono (w : ℚ) : ℕ → ℚ
  | 0 => 0
  | d + 1 => ((d : ℚ) + 1) * powSum w d

/-- `μ` on polynomials, by linearity. -/
noncomputable def muPoly (w : ℚ) (R : ℚ[X]) : ℚ := R.sum (fun d c => c * muMono w d)

/-- The functional `A` (the `X⁰` part of `Λ_X`). -/
noncomputable def Afun (q K : ℕ) (g : ℚ[X]) : ℚ :=
  muPoly (wt q) ((g * X) /ₘ Dpoly K) +
    4 * ∑ k ∈ Finset.range K, g.eval (pole k) * omega K k * Spart q k

/-- The functional `B` (the `X¹` part of `Λ_X`). -/
noncomputable def Bfun (q K : ℕ) (g : ℚ[X]) : ℚ :=
  -4 * ∑ k ∈ Finset.range K, g.eval (pole k) * omega K k * (q : ℚ) ^ (2 * k + 1)

/-- The Hankel matrix of `A` with `K = h`. -/
noncomputable def Amat (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i j => Afun q h (X ^ ((i : ℕ) + j))

/-- The Hankel matrix of `B` with `K = h`. -/
noncomputable def Bmat (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i j => Bfun q h (X ^ ((i : ℕ) + j))

/-- `Δ_h(X) = det(A_h + X B_h)`. -/
noncomputable def Delta (q h : ℕ) : ℚ[X] :=
  ((X : ℚ[X]) • (Bmat q h).map C + (Amat q h).map C).det

lemma natDegree_Delta_le (q h : ℕ) : (Delta q h).natDegree ≤ h := by
  have := natDegree_det_X_add_C_le (Bmat q h) (Amat q h)
  simpa [Delta] using this

/-- Evaluating `Δ_h` at a rational `r` gives `det(A_h + r B_h)`. -/
lemma eval_Delta (q h : ℕ) (r : ℚ) : (Delta q h).eval r = (Amat q h + r • Bmat q h).det := by
  unfold Delta
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  ring

end Chi2Irr
