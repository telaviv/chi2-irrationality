# χ₂(1/q) is irrational for every integer q ≥ 3 except possibly q = 4: a Lean 4 proof

This repository contains a complete, machine-checked proof in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the following theorems. Here χ₂(z) = Σ_{n≥0}
z^{2n+1}/(2n+1)² = ½(Li₂(z) − Li₂(−z)) is Legendre's chi function.

> **Theorem Q₄.** For every integer q ≥ 3 with q ≠ 4, the number χ₂(1/q) is irrational.

> **Theorem Q.** For every integer q ≥ 3 with q ∉ {4, 6, 8, 10, 12}, the number χ₂(1/q) is irrational.

> **Theorem (q = 3, 5).** χ₂(1/3) = 0.33762317823243597996… and χ₂(1/5) = 0.20090195660862019582… are irrational.

> **Theorem Q4′ (numerator 2).** For every odd integer q ≥ 175, the number χ₂(2/q) is irrational.
> (`Chi2Irr.QZ.theoremQ4num`, files `Chi2Irrational/QZ/*`.)

Theorem Q4′ is separate from the chain below. Its machine is the χ₂(1/q) machine read at the rational point ζ = q/2.
The paper proof gives q ≥ 173; Lean's certificate format is coarser, so the base certificate sits at w = 4/175²
(Φ ≤ −4.0033; q = 173 would need Φ(4/173²) < −3.99971). Departures from the paper proof
(`../handoff/log2log3/pilot_chi2_2q/RESULT.md`, all declared in the files): weaker 2-adic entry bounds in Lemma 10″
(same constant 4/3), the base at q = 175, and Lemma P transferred ℓ-adically from an integer q′ ≡ q/2 (mod ℓ^M)
instead of being re-read at rational ζ. Fidelity report: `FIDELITY_REFEREE_Q2NUM.md`.

Theorem Q₄ is the main result. Each theorem in this list contains the next one, and each is kept as its own Lean
theorem:
- the case q = 3, 5 was the first result of this repository and keeps its own proof;
- Theorem Q covers every odd q ≥ 3 and every even q ≥ 14;
- Theorem Q₄ adds q = 6, 8, 10, 12, using a sharper 2-adic bound for even q (Lemma 10_e, step 6 below), and reuses the
  proof of Theorem Q for every other q.

q = 4 is open: by our computations the margin is positive there (+0.090), even with Lemma 10_e and the best analytic
constant we have. q = 2, i.e. χ₂(1/2), is also open (the construction fails there). q = 1 gives χ₂(1) = π²/8, which is
classical and not part of the statement.

In Lean:

```lean
-- Chi2Irrational/Defs.lean
noncomputable def chi2Term (z : ℝ) (n : ℕ) : ℝ := z ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2
noncomputable def chi2 (z : ℝ) : ℝ := ∑' n : ℕ, chi2Term z n

-- Chi2Irrational/Q/Even/Defs.lean, Chi2Irrational/Q/Even/Interface.lean
def Chi2Irr.Q.TheoremQ4 : Prop := ∀ q : ℕ, 3 ≤ q → q ≠ 4 → Irrational (chi2 (1 / (q : ℝ)))
theorem Chi2Irr.Q.theoremQ4 : Chi2Irr.Q.TheoremQ4

-- Chi2Irrational/Q/Defs.lean, Chi2Irrational/Q/Interface.lean
def Chi2Irr.Q.TheoremQ : Prop :=
  ∀ q : ℕ, 3 ≤ q → q ∉ ({4, 6, 8, 10, 12} : Finset ℕ) → Irrational (chi2 (1 / (q : ℝ)))
theorem Chi2Irr.Q.theoremQ : Chi2Irr.Q.TheoremQ

-- Chi2Irrational/Statement.lean, Chi2Irrational/Arith/Assembly.lean
def Chi2OneThirdIrrational : Prop := Irrational (chi2 (1 / 3))
def Chi2OneFifthIrrational : Prop := Irrational (chi2 (1 / 5))
theorem Chi2Irr.chi2_one_third_irrational : Chi2OneThirdIrrational
theorem Chi2Irr.chi2_one_fifth_irrational : Chi2OneFifthIrrational
```

```
'Chi2Irr.Q.theoremQ4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.Q.theoremQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_third_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_fifth_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof uses only Lean's three standard axioms. There is no `sorry`, no added `axiom` and no `native_decide`: every
numerical certificate is evaluated by the Lean kernel. See [TRUST.md](TRUST.md).

The paper "χ₂(1/3) and χ₂(1/5) are irrational" is [`paper/chi2-irrationality.pdf`](paper/chi2-irrationality.pdf)
(source `paper/main.tex`). It proves the case q = 3, 5 in full and describes the formalisation of Theorems Q and Q₄,
whose written proofs are not part of it.

## Context

We know of no earlier proof that χ₂(1/q) is irrational for any small integer q.

- **Large q.** χ₂(1/q) = (4q)⁻¹Φ(1/q², 2, ½) is a single value of Lerch's transcendent (a shift-½ dilogarithm at
  1/q²). Irrationality for all sufficiently large q follows from Hata (J. Math. Pures Appl. 69, 1990) and from the
  explicit criteria of David, Hirata-Kohno and Kawashima (Acta Arith. 206, 2022); by our evaluation the latter need
  q ≥ 2949. So Theorem Q₄ is new for 3 ≤ q < 2949 **unless Hata's method reaches lower**: we have not read Hata 1990
  and have not determined his explicit range for the shift ½. Hata's headline application (Li₂(1/Q) ∉ ℚ for Q ≥ 12)
  is for the easier shift 0, so q = 3 (Q = q² = 9) is presumably outside his range; whether q = 5 (Q = 25) or larger
  q are within it is open to us (heuristically q = 5 is not).
- **Separate dilogarithm values do not suffice.** Li₂(−1/5) ∉ ℚ is due to Hata (Trans. AMS 336, 1993), and
  Li₂(1/5) ∉ ℚ was proved recently (Prellberg, arXiv:2609.06895; S. Liu's Lean repository
  [Li2Rational](https://github.com/siqiliu-tsinghua/Li2Rational); both
  unrefereed). Neither implies anything about the difference ½(Li₂(1/5) − Li₂(−1/5)) = χ₂(1/5).
- **Identities do not suffice.** For example, Landen's identity gives χ₂(1/3) + χ₂(1/2) = π²/8 − ½ log 2 · log 3,
  and both χ₂(1/2) and log 2 · log 3 are open.

Our search covered the web, arXiv and recent Lean repositories, but not MathSciNet or zbMATH. Please tell us if you know
of prior work.

## Outline of the proof

Fix an integer q ≥ 2 and put w = q⁻². Steps 1–5 describe the proof for q ∈ {3, 5}; step 6 describes what changes for
general q (Theorems Q and Q₄). For each h ≥ 1 take the h poles x_k = −(k + ½), k < h, put D(u) = Π_{k<h}(u − x_k), and consider
the functional

    Λ(g) = Σ_{t≥1} w^t · (g(u) · u / D(u))′ |_{u=t}      (g ∈ ℚ[u]).

Its Hankel determinant Δ_h(X) = det(A(u^{i+j}) + X·B(u^{i+j}))_{i,j<h} is a polynomial of degree ≤ h with rational
coefficients (`Machine.lean`). The machine, step 1, Theorem B (step 3) and Lemma E (step 5) are formalised for general q.

1. **Pole expansion (Lemma 1).**
   - Λ(g) = A(g) + χ₂(1/q)·B(g) with explicit rational functionals A and B, so Δ_h(χ₂(1/q)) = det(Λ(u^{i+j})).
   - Proof: partial fractions, then summing the series.
   - Files: `PoleSeries.lean`, `PoleExpansion.lean`.
2. **Arithmetic: a common denominator (the arithmetic bound).** There are positive rationals den_h with
   den_h·Δ_h ∈ ℤ[X] and log den_h ≤ (α + ε)h² eventually, where

       α = 133/60 + ¼ log 2 [+ ¼ log 3 if q = 5] − ⅓ log q   (α = 2.0237… for q = 3, 2.1281… for q = 5).

   (For general q, α is given in step 6.) The machine is first built over the free ring ℚ[q, E], with E standing for
   1/(q² − 1) (`Arith/Free.lean`). Δ_h is then bounded prime by prime:
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
   - **The certificates.** They give Φ ≤ −2.078 for q = 3 and Φ ≤ −2.385 for q = 5 (and, for step 6, Φ ≤ −3.03 for
     q = 14 and Φ ≤ −2.56, −2.72, −2.85, −2.95 for q = 6, 8, 10, 12). Their data is checked by `decide +kernel` using rational interval arithmetic and a
     kernel-verified table of logarithms. Files: `Cert/`, `Interval/`.
4. **Nonvanishing (Lemma P).** For every rational a/b, Δ_h(a/b) ≠ 0 for infinitely many h.
   - Take h = 3ℓ with ℓ a large prime. In a basis adapted to the classes mod ℓ, the Gram matrix reduced mod ℓ is block
     upper triangular.
   - Its diagonal blocks are invertible mod ℓ as soon as ℓ does not divide three fixed rational block determinants.
     For q = 3, 5 these are computed exactly by `norm_num` (`NonVan/NonVanQ.lean`); for general q they are rational
     functions of q (step 6).
   - Since there are infinitely many primes, no prime-gap theorem is needed. Files: `NonVan/`.
5. **Conclusion (Lemma E).**
   - α + Φ < 0: about −0.055 for q = 3 and −0.257 for q = 5 (`margin_three`, `margin_five`).
   - So den_h·Δ_h(χ₂(1/q)) → 0 faster than any b^{−h}. If χ₂(1/q) = a/b, then b^h·den_h·Δ_h(a/b) would be a
     nonzero integer for infinitely many h and would tend to 0: a contradiction.
   - Files: `Criterion.lean`, `MainCond.lean`, `Arith/Assembly.lean`.
6. **General q (Theorems Q and Q₄), files `Q/`.** For Theorem Q, statement and constants are in `Q/Defs.lean` and the
   assembly is in `Q/Interface.lean`; for Theorem Q₄ they are in `Q/Even/Defs.lean` and `Q/Even/Interface.lean`.
   - **Odd primes (`Q/Arith.lean`).** For every q ≥ 3 the odd primes cost at most `alphaCore q` per h², where

         alphaCore q = 133/60 + ¼ log(oddPart(q² − 1)) − ⅓ log(oddPart(q)).

     The generic primes give 133/60 as in step 2. An odd p | q² − 1 costs ¼ v_p(q² − 1) log p (Lemma 5 and Lemma 9).
     An odd p | q gives the gain −⅓ v_p(q) log p: Lemma 4′ says that every monomial of a cleared coefficient has
     q-degree ≥ a_h, and this is used prime by prime.
   - **p = 2, odd q (`Q/TwoAdicEntries.lean`, `Q/TwoAdic.lean`).** Lemma 10 at general ν = v₂(q² − 1) ≥ 3: the cost
     is c2Odd q = (ν − 2)/4 · log 2.
   - **p = 2, even q (`Q/TwoAdicEven.lean`, Lemma 10₀).** A Gauss bound in the anchored basis gives 2-adic exponent
     ≤ 2⌊h/2⌋(⌊h/2⌋ + 1) − v₂(q)·a_h ≤ h²/2 + h − v₂(q)·a_h, so the cost is c2Even q = (½ − v₂(q)/3) · log 2. This
     includes the 2-adic share of the gain of Lemma 4′. Theorem Q uses this bound.
   - **p = 2, even q, sharp (`Q/Even/TwoAdicSharp.lean`, Lemma 10_e; used for Theorem Q₄).** Let e = v₂(q). The
     weighted Gauss valuation v_e(Σ c_{n,j} qⁿXʲ) = inf(v₂(c_{n,j}) + e·n) on ℚ⟦q⟧[X] bounds the 2-adic size of Δ_h
     at q (`Q/Even/WNorm.lean`). Bounding v_e of every term of Lemma 4′'s slot expansion gives the 2-adic exponent
     ≤ −e·a_h + c(e)·h² + O(h log h), with c(e) = (6 − 4e)/(3(3e + 8)) (2/33, −1/21, −2/17 for e = 1, 2, 3) in place
     of ½. The cost is c2EvenSharp q = (c(e) − e/3) · log 2.
   - **Arithmetic constant.** alphaCore q + c₂ is, for odd q, α(q) = 133/60 − ½ log 2 + ¼ log(q² − 1) − ⅓ log q
     (α(3) = 2.0237…, α(5) = 2.1281…, as in step 2), and for even q, α(q) = 133/60 + ½ log 2 + ¼ log(q² − 1) − ⅓ log q
     with Lemma 10₀, or α_e(q) = 133/60 + c(e) log 2 + ¼ log(q² − 1) − ⅓ log q with Lemma 10_e.
   - **Analytic constant (`Q/Shift.lean`, `Q/Analytic.lean`).** The shift lemma `DualCert.shift` turns a dual
     certificate at q₀ into one at any q ≥ q₀, with Φ decreased by ½ log(q/q₀) − δ for any δ > 0 (the functional
     depends on q only through w = q⁻²). Odd q use the q = 3 certificate: β = −2.078 − ½ log(q/3). Even q ≥ 14 use a
     new certificate at q = 14 (`Cert/Q14.lean`, exact exponent PhiQ = −3.0372394…, used as Φ ≤ −3.03):
     β = −3.03 − ½ log(q/14). For Theorem Q₄, q = 6, 8, 10, 12 use direct certificates at q itself, with no shift
     (`Cert/Q6.lean`, …, `Cert/Q12.lean`, combined in `Q/Even/Certs.lean`). Their exact exponents are
     PhiQ = −2.5635463…, −2.7264892…, −2.8528812…, −2.9535971…, used as Φ ≤ −2.56, −2.72, −2.85, −2.95.
   - **Nonvanishing (`Q/NonVan.lean`).** The three block determinants of step 4, in closed form in q:
     det M(S) = 8q⁶(9q² + 1)/(9(q² − 1)), det M(L) = 8q²(16200q⁶ − 10575q⁴ − 6352q² + 905)/(2025(q² − 1)),
     det M(D) = −q⁴(16200q⁶ − 51075q⁴ + 28523q² + 420)/(135(q² − 1)²). The numerators are nonzero at every integer
     q ≥ 2.
   - **Margins (`Q/Margin.lean`), by closed forms valid for all q.** For odd q ≥ 3, α(q) + β ≤ 133/60 − 2.078 − ½ log 2
     + ⅙ log 3 < −0.023. For even q ≥ 14, α(q) + β ≤ 133/60 − 3.03 + (7/6) log 2 < −0.0046. The true margins decrease
     in q (numerically); the worst are −0.0543 at q = 3 and −0.0282 at q = 14 (`scripts/q/margin_check.py`). With Lemma 10₀ the even
     margin is positive for q ≤ 12 (numerically +0.0045 at q = 12 even with the best analytic constant), which is why
     Theorem Q excludes the even values below 14.
   - **Margins for Theorem Q₄ (`Q/Even/Margin.lean`).** With Lemma 10_e and the direct certificates,
     alphaCore q + c2EvenSharp q + PhiT q = −0.0097, −0.2422, −0.2101, −0.3539 for q = 6, 8, 10, 12
     (`scripts/q/margin_newQ_check.py`, Arb). Lean proves the weaker bounds −0.00904, −0.238, −0.203, −0.304 with
     elementary logarithm bounds. At q = 4 the margin stays positive, so q = 4 is excluded.

   The sources are two written proofs, one for Theorem Q and one for Lemma 10_e and q = 6, 8, 10, 12. Each was read by
   one AI gate referee (PASS WITH FIXES), and neither is part of this repository. Lean departs from them as follows;
   none of the departures loses anything claimed:
   - for odd q, Lean uses the existing q = 3 certificate (Φ ≤ −2.078) instead of the written proof's sharper
     Φ₃ = −2.0987, and shifts every odd q from q = 3;
   - for even q, Lean uses its own kernel-checked q = 14 certificate (Φ ≤ −3.03) instead of the written proof's
     certificates (Φ ≤ −3.0444 and −3.0498), so the q = 14 margin is −0.0282 instead of −0.0426;
   - the even 2-adic exponent is h²/2 + O(h) rather than the written proof's ⌊h²/2⌋ − h, with the same limit; and the
     shift lemma is discretised (a Riemann-sum loss, absorbed into δ);
   - for Lemma 10_e, Lean counts through the existing Andreief expansion of Lemma 4′'s truncated slot matrix, together
     with a 2-adic bound for Vandermonde determinants with derivative rows (`Q/Even/CoreDet.lean`), instead of the
     written proof's confluent Cauchy–Binet formula. Its O(h log h) terms are cruder, and the leading constant c(e) is
     the same (helpers `Q/Even/Terms.lean`, `Count.lean`, `NuBound.lean`);
   - for q = 6, 8, 10, 12, Lean's certificates are weaker than the written proof's (Φ ≤ −2.5704, −2.7418, −2.8694,
     −2.9710), so the margins are −0.0097, −0.2422, −0.2101, −0.3539 instead of −0.0202, −0.2641, −0.2295, −0.3750.

Formalised: everything above, for every q in Theorem Q₄, including the general-ν form of Lemma 10 (the written proof
recorded one half of it as proved on paper only at ν ≠ 3) and Lemma 10_e. Not formalised: explicit thresholds (an
effective h₀). q = 4 is open.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and Mathlib (v4.35.0) are pinned in
`lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get                 # download prebuilt Mathlib
LEAN_NUM_THREADS=4 lake build      # 9139 jobs
lake env lean Axioms.lean          # print the axioms of the main theorems and their ingredients
```

Before Theorem Q was added, a clean build took about 10 minutes on a desktop once Mathlib was cached. The kernel checks
of the certificates added since then take 233 s (q = 14, `Cert/Q14.lean`), 502 s (q = 6), 191 s (q = 8), 170 s
(q = 10) and 171 s (q = 12), about 21 minutes in all; the full build has not been re-timed.
The thread limit follows the author's larger Lean repositories, where a build at Lake's default concurrency once ran out
of memory on Windows.

The certificate data can be regenerated with `scripts/gen_cert.py` (Python with numpy, scipy and mpmath). The output is
byte-identical to the committed `Cert/DataQ3.lean`, `Cert/DataQ5.lean`, `Cert/DataQ14.lean` and
`Cert/DataQ6.lean`, …, `Cert/DataQ12.lean`; the commands are in TRUST.md (for q = 3, 5 also in the script's
docstring). The checks made while porting to general q (denominators, 2-adic bounds, the shift lemma, the block
determinants, Lemma 10_e, the margins) are in `scripts/q/`.

## Repository layout

Paths are relative to `Chi2Irrational/`.

| path | content |
|---|---|
| `Defs.lean`, `Statement.lean` | χ₂ and the two target statements for q = 3, 5 |
| `Machine.lean` | the functionals A, B and the polynomial Δ_h(X); deg Δ_h ≤ h |
| `PoleSeries.lean`, `PoleExpansion.lean` | Lemma 1: Λ = A + χ₂(1/q)·B |
| `Criterion.lean`, `MainCond.lean` | Lemma E and the conditional main theorem `irrational_of_bounds` |
| `Arith/` | the arithmetic bound: free ring, Gauss norms, class bound, Lemmas 4′, 5, 9, 10, the denominator, final assembly (q = 3, 5) |
| `PNT/` | prime number theorem (θ(x) ~ x) and prime sums with step weights |
| `Analytic/` | Theorem B: node expansion, slot determinants, lattice energy inequality, discretization |
| `Interval/`, `Cert/` | rational interval arithmetic, log enclosures, and the seven kernel-checked dual certificates (q = 3, 5, 14 and q = 6, 8, 10, 12) |
| `NonVan/` | Lemma P: ℓ-adic reduction, progressions, class blocks, nonvanishing for q = 3, 5 and the generic route `nonvan_of` |
| `Q/` | Theorem Q: `Defs` (statement, constants), `Arith` (odd primes for general q), `TwoAdicEntries`, `TwoAdic` (Lemma 10 at general ν), `TwoAdicEven` (Lemma 10₀), `Shift` (shift lemma), `Analytic`, `NonVan` (block determinants in closed form), `Margin`, `Interface` (assembly) |
| `Q/Even/` | Theorem Q₄: `Defs` (statement, constants), `WNorm`, `Terms`, `CoreDet`, `Count`, `NuBound`, `TwoAdicSharp` (Lemma 10_e), `Certs` (q = 6, 8, 10, 12), `Margin`, `Interface` (assembly) |
| `../scripts/gen_cert.py` | generator for the certificate data (untrusted; see TRUST.md) |
| `../scripts/q/` | checks made for Theorems Q and Q₄; `referee/` and `referee_q4/` hold the fidelity referees' independent recomputations |
| `../scripts/axioms_q.txt`, `../scripts/leanchecker_q.log` | axiom output and per-module `leanchecker` results for the build with Theorem Q |
| `../scripts/axioms_q4.txt`, `../scripts/leanchecker_q4.log` | the same for the build with Theorem Q₄ |
| `../Axioms.lean` | axiom audit |
| `../FIDELITY_REFEREE_Q.md` | AI referee report on the fidelity of the statement of Theorem Q |
| `../FIDELITY_REFEREE_Q4.md` | AI referee report on the fidelity of the statement of Theorem Q₄ |

Every Lean file starts with a docstring saying what it proves and how. The files under `Q/` cite `RESULT §n` (or
`pilot_q/RESULT.md`), the working proof note of Theorem Q, and `CHI2_IRRATIONALITY §n`, the working proof note for
q = 3, 5. The files under `Q/Even/` cite `pilot_qeven/RESULT.md`, the working proof note of Lemma 10_e and of
q = 6, 8, 10, 12. These notes belong to the development history and are not part of this repository.

## Status and caveats

- The Lean kernel has checked the proof. **No human expert has yet reviewed the mathematics or the Lean code.** The
  statement definitions (see TRUST.md) are short and worth reading.
- The construction, the proofs, the certificate programs and the Lean formalisation were produced largely by AI models
  (Claude, Anthropic), working under the direction of the author. Apart from the Lean kernel check, all verification so
  far has been done by AI systems.
- The margins are thin: α + Φ ≈ −0.055 per h² for q = 3, −0.0282 for q = 14, and −0.0097 for q = 6, the thinnest in
  the repository (Lean proves it as ≤ −0.00904). They are certified, not estimated.

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
