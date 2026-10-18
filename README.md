# χ₂(1/3) and χ₂(1/5) are irrational: a Lean 4 proof

This repository contains a complete, machine-checked proof in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the following theorem.

> **Theorem.** Let χ₂(z) = Σ_{n≥0} z^{2n+1}/(2n+1)² be Legendre's chi function. Then χ₂(1/3) and χ₂(1/5) are
> irrational.

Equivalently, χ₂(z) = ½(Li₂(z) − Li₂(−z)). The two numbers are χ₂(1/3) = 0.33762317823243597996… and
χ₂(1/5) = 0.20090195660862019582….

In Lean:

```lean
-- Chi2Irrational/Defs.lean, Chi2Irrational/Statement.lean
noncomputable def chi2Term (z : ℝ) (n : ℕ) : ℝ := z ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2
noncomputable def chi2 (z : ℝ) : ℝ := ∑' n : ℕ, chi2Term z n
def Chi2OneThirdIrrational : Prop := Irrational (chi2 (1 / 3))
def Chi2OneFifthIrrational : Prop := Irrational (chi2 (1 / 5))

-- Chi2Irrational/Arith/Assembly.lean
theorem Chi2Irr.chi2_one_third_irrational : Chi2OneThirdIrrational
theorem Chi2Irr.chi2_one_fifth_irrational : Chi2OneFifthIrrational
```

```
'Chi2Irr.chi2_one_third_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_fifth_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof uses only Lean's three standard axioms. There is no `sorry`, no added `axiom` and no `native_decide`: every
numerical certificate is evaluated by the Lean kernel. See [TRUST.md](TRUST.md).

## Context

We know of no earlier proof that χ₂(1/q) is irrational for any small integer q.

- **Large q.** χ₂(1/q) = (1/q)(1 + ¼Φ(1/q², 2, ½)) is a single Lerch value. Irrationality for all sufficiently large q
  follows from Hata (J. Math. Pures Appl. 69, 1990) and from the explicit criteria of David, Hirata-Kohno and Kawashima
  (Acta Arith. 206, 2022). By our evaluation, those criteria need q in the thousands.
- **Separate dilogarithm values do not suffice.** Li₂(−1/5) ∉ ℚ is due to Hata (Trans. AMS 336, 1993), and
  Li₂(1/5) ∉ ℚ was proved recently (Prellberg, arXiv:2609.06895; S. Liu's Lean repository
  [Li2Rational](https://github.com/siqiliu-tsinghua/Li2Rational); both
  unrefereed). Neither implies anything about the difference ½(Li₂(1/5) − Li₂(−1/5)) = χ₂(1/5).
- **Identities do not suffice.** For example, Landen's identity gives χ₂(1/3) + χ₂(1/2) = π²/8 − ½ log 2 · log 3,
  and both χ₂(1/2) and log 2 · log 3 are open.

Our search covered the web, arXiv and recent Lean repositories, but not MathSciNet or zbMATH. Please tell us if you know
of prior work.

## Outline of the proof

Fix q ∈ {3, 5} and put w = q⁻². For each h ≥ 1 take the h poles x_k = −(k + ½), k < h, put D(u) = Π_{k<h}(u − x_k),
and consider the functional

    Λ(g) = Σ_{t≥1} w^t · (g(u) · u / D(u))′ |_{u=t}      (g ∈ ℚ[u]).

Its Hankel determinant Δ_h(X) = det(A(u^{i+j}) + X·B(u^{i+j}))_{i,j<h} is a polynomial of degree ≤ h with rational
coefficients (`Machine.lean`). Five steps prove the theorem.

1. **Pole expansion (Lemma 1).**
   - Λ(g) = A(g) + χ₂(1/q)·B(g) with explicit rational functionals A and B, so Δ_h(χ₂(1/q)) = det(Λ(u^{i+j})).
   - Proof: partial fractions, then summing the series.
   - Files: `PoleSeries.lean`, `PoleExpansion.lean`.
2. **Arithmetic: a common denominator (the arithmetic bound).** There are positive rationals den_h with
   den_h·Δ_h ∈ ℤ[X] and log den_h ≤ (α + ε)h² eventually, where

       α = 133/60 + ¼ log 2 [+ ¼ log 3 if q = 5] − ⅓ log q   (α = 2.0237… for q = 3, 2.1281… for q = 5).

   The machine is first built over the free ring ℚ[q, E], with E standing for 1/(q² − 1) (`Arith/Free.lean`). Δ_h is
   then bounded prime by prime:
   - **Odd p ≥ 2h/5, the class bound.** A basis adapted to the residue classes mod p, together with an explicit count
     (Lemma 8A), gives exponent ≤ h·φ₁(p/h) for a piecewise-linear φ₁ with ∫φ₁ = 17/12. Files: `Arith/ClassBound.lean`,
     `Arith/ClassCount.lean`.
   - **Odd p < 2h/5 (Lemma 9).** A Lagrange-basis Gauss-norm bound gives exponent ≤ 2h·#{e : p^e < 2h}. File:
     `Arith/Lemma9.lean`.
   - **The prime sums.** With the prime number theorem, the two bounds above contribute 17/12 + 4/5 = 133/60 per h².
     Files: `Arith/PrimeSums.lean`, `PNT/`.
   - **p = q (Lemma 4′, a gain).** In ℚ⟦q⟧ the functional reflects to μ(R) = −Σ_m q^{2m} R′(−m). A slot decomposition
     plus the Andreief identity show that q^{⌊(h² − 7h)/3⌋} divides Δ_h. File: `Arith/QAdic.lean`.
   - **p | q² − 1, i.e. p = 3 when q = 5 (Lemma 5).** Δ_h has degree ≤ (h² + 2h)/4 in E. File: `Arith/PoleOrder.lean`.
   - **p = 2 (Lemma 10).** An anchored basis and forward-difference valuations give exponent
     ≤ (h² + 2h)/4 + h(log₂ h + 6). Files: `Arith/TwoAdic*.lean`.
   - **Assembly.** The bounds are combined in `Arith/Special.lean` and `Arith/Assembly.lean`.
3. **Analytic bound (Theorem B).** |Δ_h(χ₂(1/q))| ≤ exp((Φ + ε)h²) eventually, where Φ is read off a dual certificate:
   a step density μ on [0, N] together with cell bounds for its potential.
   - **The bound.** Expand the truncated Hankel matrix as a sum of rank-one terms (Andreief) and bound the resulting
     minors with value and derivative rows. A discrete weak-duality inequality (a Pólya-type lattice energy inequality)
     then compares the log-gas energy of the nodes with the energy of μ. Files: `Analytic/`.
   - **The certificates.** They give Φ ≤ −2.078 for q = 3 and Φ ≤ −2.385 for q = 5. Their data is checked by
     `decide +kernel` using rational interval arithmetic and a kernel-verified table of logarithms. Files: `Cert/`,
     `Interval/`.
4. **Nonvanishing (Lemma P).** For every rational a/b, Δ_h(a/b) ≠ 0 for infinitely many h.
   - Take h = 3ℓ with ℓ a large prime. In a basis adapted to the classes mod ℓ, the Gram matrix reduced mod ℓ is block
     upper triangular.
   - Its diagonal blocks are invertible mod ℓ as soon as ℓ does not divide three fixed rational block determinants.
     These are computed exactly by `norm_num` (`NonVan/NonVanQ.lean`).
   - Since there are infinitely many primes, no prime-gap theorem is needed. Files: `NonVan/`.
5. **Conclusion (Lemma E).**
   - α + Φ < 0: about −0.055 for q = 3 and −0.257 for q = 5 (`margin_three`, `margin_five`).
   - So den_h·Δ_h(χ₂(1/q)) → 0 faster than any b^{−h}. If χ₂(1/q) = a/b, then b^h·den_h·Δ_h(a/b) would be a
     nonzero integer for infinitely many h and would tend to 0: a contradiction.
   - Files: `Criterion.lean`, `MainCond.lean`, `Arith/Assembly.lean`.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and Mathlib (v4.35.0) are pinned in
`lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get          # download prebuilt Mathlib
lake build                  # about 10 minutes on a desktop once Mathlib is cached
lake env lean Axioms.lean   # print the axioms of the main theorems and their ingredients
```

The certificate data can be regenerated with `scripts/gen_cert.py` (Python with numpy, scipy and mpmath). The output is
byte-identical to the committed `Cert/DataQ3.lean` and `Cert/DataQ5.lean`; the commands are in the script's docstring.

## Repository layout

Paths are relative to `Chi2Irrational/`.

| path | content |
|---|---|
| `Defs.lean`, `Statement.lean` | χ₂ and the two target statements |
| `Machine.lean` | the functionals A, B and the polynomial Δ_h(X); deg Δ_h ≤ h |
| `PoleSeries.lean`, `PoleExpansion.lean` | Lemma 1: Λ = A + χ₂(1/q)·B |
| `Criterion.lean`, `MainCond.lean` | Lemma E and the conditional main theorem `irrational_of_bounds` |
| `Arith/` | the arithmetic bound: free ring, Gauss norms, class bound, Lemmas 4′, 5, 9, 10, the denominator, final assembly |
| `PNT/` | prime number theorem (θ(x) ~ x) and prime sums with step weights |
| `Analytic/` | Theorem B: node expansion, slot determinants, lattice energy inequality, discretization |
| `Interval/`, `Cert/` | rational interval arithmetic, log enclosures, and the two kernel-checked dual certificates |
| `NonVan/` | Lemma P: ℓ-adic reduction, progressions, class blocks, nonvanishing for q = 3, 5 |
| `../scripts/gen_cert.py` | generator for the certificate data (untrusted; see TRUST.md) |
| `../Axioms.lean` | axiom audit |

Every Lean file starts with a docstring saying what it proves and how.

## Status and caveats

- The Lean kernel has checked the proof. **No human expert has yet reviewed the mathematics or the Lean code.** The
  statement definitions (see TRUST.md) are short and worth reading.
- The construction, the proofs, the certificate programs and the Lean formalisation were produced largely by AI models
  (Claude, Anthropic), working under the direction of the author. Apart from the Lean kernel check, all verification so
  far has been done by AI systems.
- The margin for q = 3 is thin (α + Φ ≈ −0.055 per h²). It is certified, not estimated.

## Acknowledgements

- `PNT/` and `Interval/` are ported from [beta-irrationality](https://github.com/telaviv/beta-irrationality), the
  author's Lean proof that one of β(4), β(6), …, β(36) is irrational.
- `PNT/Port/` comes originally from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (A. Kontorovich, T. Tao et al.), via [domino14/zeta5](https://github.com/domino14/zeta5), under the Apache License
  2.0 (see `PNT/Port/LICENSE`).
- The Hankel-determinant approach follows Q. Tang's Lean proof that Li₂(1/2) is irrational
  ([dtq1997/li2-half-irrationality](https://github.com/dtq1997/li2-half-irrationality)). The analytic part uses ideas
  from logarithmic potential theory (Saff–Totik, *Logarithmic Potentials with External Fields*).

## License

Apache License 2.0 (see [LICENSE](LICENSE)). `Chi2Irrational/PNT/Port/` is derived from PrimeNumberTheoremAnd, also
Apache-2.0; its own `LICENSE` file and the provenance notes in its file headers are kept.
