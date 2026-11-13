/-
# Lemma M (Ti₂ at odd `q`, `ν = v₂(q² + 1) = 1`): definitions

Source: `../handoff/log2log3/pilot_ti2_q5/RESULT.md` (Lemma M, one AI gate referee, PASS WITH FIXES). Lemma M bounds the
2-adic size of the coefficients of `Δ^Ti_h` at odd `q` by `n₂(h) ≤ h²/8 + O(h log h)` (Lemma 10₁ had `h²/4`).

The written proof uses a 2-adic number `θ₂` and the 2-adic functional `𝕄(G) = Σ_b Ω_b Δ^b G′(0)`. The formal proof is
rational throughout:
* `MB q B F = Σ_{b<B} Ω_b Δ^b F(0)` is `𝕄` truncated at `B` (applied to derivative values `F = G′`);
* `theta q h = (4 − MB q (Bt h) (fk 0)) / (4q)` is a rational stand-in for `θ₂` (RESULT §1 step 1, with `𝕄` truncated);
* the Mahler (binomial) basis `Cb s = X(X−1)⋯(X−s+1)/s!` replaces the monomials (RESULT §1 step 2):
  `Λ_X(Cb i · Cb j) = Em + (X − θ)·(Aᵀ O A)` with `Em = A + θ·B` on `Cb i · Cb j`, `Am n i = Δ^n_k Cb_i(x_k)|_{k=0}` and
  `Om n n′ = Σ_k β_k C(k,n) C(k,n′)`;
* instead of the 2h-row Cauchy–Binet of RESULT §1 step 4, one Leibniz bound with row/column potentials on a
  `3h × 3h` block matrix whose determinant is `det(Em + (X − θ) AᵀOA)` (`TiQ/M/Gram.lean`, `TiQ/M/Final.lean`); its
  tropical value equals RESULT's subset bound exactly (checked for h ≤ 48).
-/
import Chi2Irrational.TiQ.TwoAdicNu1
import Mathlib.Algebra.Group.ForwardDiff

namespace Chi2Irr
namespace TiQ
namespace M

open Polynomial Finset

/-- The binomial polynomial `C_s = X(X−1)⋯(X−s+1)/s!`. -/
noncomputable def Cb (s : ℕ) : ℚ[X] := C ((s.factorial : ℚ)⁻¹) * descPochhammer ℚ s

/-- `Δ^b F(0)` for `F : ℕ → ℚ` (forward difference with step `1`). -/
def fd (b : ℕ) (F : ℕ → ℚ) : ℚ := (fwdDiff 1)^[b] F 0

/-- The truncated Mahler functional `MB q B F = Σ_{b<B} Ω_b(w) Δ^b F(0)`, `w = −q⁻²`. -/
noncomputable def MB (q B : ℕ) (F : ℕ → ℚ) : ℚ := ∑ b ∈ range B, OmQ (wT q) b * fd b F

/-- Derivative values of `1/(u − x_k)` at the nodes: `f_k′(i) = −1/(i − x_k)²`. -/
def fk (k : ℕ) (i : ℕ) : ℚ := -1 / ((i : ℚ) - pole k) ^ 2

/-- The truncation level. -/
def Bt (h : ℕ) : ℕ := 16 * h + 16

/-- The rational stand-in for `θ₂`. -/
noncomputable def theta (q h : ℕ) : ℚ := (4 - MB q (Bt h) (fk 0)) / (4 * (q : ℚ))

/-- `Em = A + θ·B` on the products of the binomial basis. -/
noncomputable def Emt (q h : ℕ) (θ : ℚ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => AfunT q h (Cb i * Cb j) + θ * BfunT q h (Cb i * Cb j)

/-- `Em` at `θ = theta q h`. -/
noncomputable def Em (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ := Emt q h (theta q h)

/-- `A_{ni} = Δ^n_k [C_i(x_k)]|_{k=0}`. -/
noncomputable def Am (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun n i => fd n (fun k => (Cb i).eval (pole k))

/-- The pole weights of `B`: `B(g) = Σ_k β_k g(x_k)`. -/
def betaK (q h k : ℕ) : ℚ := -4 * omega h k * poleW q k

/-- `O_{nn′} = Σ_{k<h} β_k C(k,n) C(k,n′)`. -/
def Om (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun n n' => ∑ k ∈ range h, betaK q h k * ((k.choose n : ℕ) : ℚ) * ((k.choose n' : ℕ) : ℚ)

end M
end TiQ
end Chi2Irr
