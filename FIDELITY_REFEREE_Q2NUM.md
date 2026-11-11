# Fidelity referee report: Theorem Q4′ (`Chi2Irr.QZ.theoremQ4num`), χ₂(2/q) for odd q ≥ 175

Referee: independent AI fidelity referee (Claude), 2026-11-10. Worktree `lean_chi2_wt/q2num`, branch `theorem-q2num`,
HEAD `9853b60` ("Theorem Q4': base moved to qB = 175 …", 23:48:40). `git status` is clean. I did not build anything and
edited no Lean file. I read the axiom output `scripts/q2num/runs/axioms_q2num.txt` (mtime 23:48:24). That is after the
last `.lean` edit (`QZ/Analytic.lean`, 23:41:42) and after the second, successful build pass in
`scripts/q2num/runs/full_build.txt`, so it belongs to the committed tree.

Scope: the new files `Chi2Irrational/QZ/*.lean` (18 files, 3158 lines), the nine new lines of `Axioms.lean`, and the
root import `Chi2Irrational.lean` l. 70. The integer-q machinery they reuse (`Arith/*`, `NonVan/*`, `Analytic/*`,
`Cert/*`, `Q/*`) was audited in `FIDELITY_REFEREE_Q.md` and `FIDELITY_REFEREE_Q4.md`. I did not re-audit it here.

Paper: `handoff/log2log3/pilot_chi2_2q/RESULT.md` ("RESULT"), which states Theorem Q4: χ₂(2/q) ∉ ℚ for every odd
q ≥ 173, at [Proof sketch]. Gate referee: `pilot_chi2_2q/referee/REFEREE_CHI2_2Q.md` (PASS WITH FIXES).

**Verdict: PASS WITH REMARKS.** The Lean statement says exactly what RESULT claims, with q₀ = 175 in place of 173:

```lean
theorem theoremQ4num : ∀ q : ℕ, Odd q → 175 ≤ q → Irrational (chi2 (2 / (q : ℝ)))
```

* There are no hidden hypotheses, no custom axioms and no trusted code. `#print axioms Chi2Irr.QZ.theoremQ4num` gives
  `[propext, Classical.choice, Quot.sound]`.
* The only value RESULT claims that Lean does not cover is q = 173. The source files disclose this (`QZ/Defs.lean`
  l. 4, `QZ/Margin.lean` l. 8–9).
* Every constant matches RESULT, and the margin and certificate exponent match my independent recomputation.
* Lean departs from RESULT in three places, and each is sound and disclosed:
  - weaker entry bounds in Lemma 10″;
  - a coarser certificate at a different base (q_B = 175, not 173);
  - an ℓ-adic transfer from an integer q′ in place of RESULT §5's re-reading of Lemma P at rational ζ. The transfer is
    the stronger argument: it removes gap G3 of RESULT for the Lean statement.

**No code or statement change is required.**
* Required (documentation): README.md, TRUST.md and `paper/main.tex` do not mention Q4′ at all (R1). The handoff
  RESULT.md still says "Q4 is not in Lean" (R2).
* Optional: four stale or slightly inaccurate docstrings (S1–S4).

---

## 1. The final statement (`QZ/Interface.lean` l. 71–91): faithful

* **Quantifiers.** `∀ q : ℕ, Odd q → 175 ≤ q`. `Odd` is Mathlib's `Odd` on ℕ. RESULT l. 64 says "every odd q ≥ 173".
  Even q are not claimed, as in RESULT (for even q, 2/q = 1/(q/2) is Theorem Q's business). There are no instance
  arguments or side hypotheses.
* **The number.** `2 / (q : ℝ)` is real division after the explicit ℕ → ℝ cast, so it is the real number 2/q ∈ (0, 2/175].
* **`Irrational`** is Mathlib's (`x ∉ Set.range (Rat.cast)`).
* **`chi2`** (`Defs.lean` l. 11–14): `chi2 z = ∑' n, z^(2n+1)/(2n+1)²`. This is Legendre's χ₂(z) = Σ_{n≥0}
  z^{2n+1}/(2n+1)², as in RESULT and README l. 4–5.
  - `summable_chi2Term` (l. 31–35) proves absolute summability for |z| ≤ 1, so the `tsum` is the genuine sum and not
    Lean's junk value 0. Here |2/q| ≤ 2/175 < 1.
  - The statement does not route through `zq`, `DeltaZ`, `alphaZ` or any other project definition. Its dependency cone
    is `chi2`, `chi2Term`, `tsum`, `Odd`, `Irrational` and casts, the same as `TheoremQ4` minus `≠ 4`.
* **q₀ = 175 against the paper's 173.** The docstring (l. 71) says "every odd `q ≥ qB`", with `qB = 175`
  (`QZ/Defs.lean` l. 31); the statement writes the literal 175. Disclosure:
  - `QZ/Defs.lean` l. 4: "odd `q ≥ 173` on paper";
  - `QZ/Margin.lean` l. 8–9: "Lean's certificate format is weaker, so the base moves to `q = 175`";
  - commit message of `9853b60`; `Axioms.lean` l. 54 comment ("for odd q ≥ 175").

  It is **not** disclosed in README/TRUST/paper, because Q4′ is absent from them entirely (R1).
* **Bridge** `chi2_two_div` (l. 62–69): `chi2 (2/q) = chi2 (1/((q/2 : ℚ) : ℝ))`. This is correct for all q, including
  q = 0, where both sides are `chi2 0`.
* **Name.** RESULT calls the theorem "Theorem Q4". The repository already has `Chi2Irr.Q.theoremQ4` (χ₂(1/q), q ≠ 4).
  Lean's "Q4′" / `theoremQ4num` avoids the clash. RESULT and any paper text should adopt the same name (R2).

## 2. The machine `DeltaZ` (`QZ/Machine.lean`): the χ₂(1/q) machine at ζ = q/2

* **Definitions** (l. 24–46) are `Machine.lean`'s (l. 32–70) with `(q : ℚ)` replaced by `ζ : ℚ`:
  - `SpartZ ζ k = Σ_{j≤k} ζ^{2(k−j)}/(2j+1)²` and `wtZ ζ = 1/ζ²`;
  - `AfunZ` = μ((g·u) div D) + 4 Σ_k g(x_k) ω_k S_k(ζ), and `BfunZ` = −4 Σ_k g(x_k) ω_k ζ^{2k+1};
  - `DeltaZ ζ h = det(X·B_h + A_h)`.

  The pole part of Λ_X is therefore −4 Σ g(x_k) ω_k (ζ^{2k+1} X − S_k(ζ)), which is RESULT §1 l. 93. The weight is
  w = ζ⁻² = 4/q², as in RESULT §1 l. 106. Poles, D, ω_k, `powSum`, `muMono`, `muPoly` are the q-free originals.
* **`DeltaZ_natCast`** (l. 49) holds by `rfl`. At an integer ζ the machine *is* `Delta q h`, definitionally. This is the
  strongest possible confirmation that it is "the same machine read at ζ".
* **Lemma 1 at ζ** (`QZ/PoleExpansion.lean` l. 30). `pole_seriesZ` is Σ_{t≥1} W^t·(−1/(t − x_k)²) =
  −4(ζ^{2k+1} χ₂(1/ζ) − S_k(ζ)). I re-derived it by hand: 1/(t − x_k)² = 4/(2(t+k)+1)², and re-indexing n = t + k gives
  the tail of χ₂(1/ζ) times ζ^{2k+1}. `aeval_chi2_DeltaZ` (l. 220) then ties `DeltaZ ζ` evaluated at `chi2 (1/ζ)` to the
  real moment determinant. That is the link "χ₂(2/q) ↔ the machine" of RESULT §9 step 1.
* **`map_DeltaF_Z`** (l. 136). The statement is `(DeltaF h).map (evZ ζ) = DeltaZ ζ h`, with
  `evZ ζ = aeval ![ζ, 1/(ζ² − 1)]` (l. 82): q ↦ ζ, E ↦ 1/(ζ² − 1). This is the free-ring machine of `Arith/Free.lean`
  (l. 21–63) under the same substitution that `evQ` (l. 69) uses at integers.
  - The proof matches entries. `evZ_OmegaF` sends `OmegaF b` to `OmR (ζ⁻²) b`, that is w/(1−w) = 1/(ζ²−1) at b = 0 and
    w^b/(1−w)^{b+1} = ζ²/(ζ²−1)^{b+1} at b ≥ 1. `evZ_muMonoF` goes through `powSum_newton`.
  - **Hypothesis `1 < ζ`.** It is not vacuous, and it is right. `powSum_newton` is proved analytically, as Σ t^n w^t
    for 0 ≤ w < 1, which needs w = ζ⁻² ∈ (0, 1). At ζ = q/2 with q ≥ 3 it holds (`one_lt_zq`, `QZ/Arith.lean` l. 32).
    The identity is false or undefined at ζ = ±1, where E has a pole.
  - `coeff_DeltaZ_eq` (l. 146) is the coefficient form that every p-adic transfer uses. It is exactly RESULT §1's
    "statements in ℚ[ζ, X] followed by a specialisation".
* Side remark on the paper, not on Lean: RESULT §1 l. 94 writes "Ω_b = ζ²/(ζ²−1)^{b+1}" without "b ≥ 1". Ω₀ = 1/(ζ²−1),
  as RESULT §2 l. 119 and the gate referee F3 say, and as Lean has.

## 3. The endgame (`QZ/MainCond.lean`, `Criterion.lean`): sound, and no field can cheat

* `MachineBoundsZ ζ` (l. 18–31) has the same shape as `MainCond.lean`'s structure, and `irrational_of_boundsZ`
  (l. 34–52) feeds Lemma E (`Criterion.lean` l. 54) with c = −(α + β)/2.
* **Lemma E is sound for an arbitrary polynomial family.** It needs only:
  - deg P_h ≤ h;
  - `den h · P_h ∈ ℤ[X]` with `den h > 0`;
  - `den h · |P_h(ξ)| ≤ exp(−c h²)` eventually;
  - for every a/b, P_h(a/b) ≠ 0 infinitely often.

  The proof (l. 61–85) is the standard one: N = b^h·den·P_h(a/b) is a nonzero integer, yet |N| < 1.
* So the structure cannot be satisfied trivially. `den` must clear denominators of the actual `DeltaZ ζ h` (`den_int`).
  `analytic` must bound the actual `aeval (chi2 (1/ζ)) (DeltaZ ζ h)`. `nonvan` is about the same `DeltaZ ζ h`. α and β
  are free reals, but they are tied together by `margin` and by `arith` / `analytic`.
* The conclusion does not depend on whether `DeltaZ` is "the right machine". Any family satisfying the fields would
  prove irrationality of `chi2 (1/ζ)`. The fidelity of the machine matters only for whether the Lean proof *follows
  RESULT*, and §2 confirms that it does.
* **Wiring** (`Interface.lean` l. 72–91):
  - α = `alphaZ q + c2Num`, β = `betaZ q + δ`, δ = −(margin)/2 > 0;
  - `arith_z` is fed the n₂ and c₂ = `c2Num` from `twoAdic_num`;
  - `analytic_z` uses q ≥ qB, and `nonvan_z` uses q ≥ 5.

  Every ingredient is used with the same `DeltaZ (zq q)`.

## 4. Ingredients and constants

### 4.1 Constants (`QZ/Defs.lean` l. 21–37)

| Lean | value | RESULT |
|---|---|---|
| `zq q` | q/2 ∈ ℚ | ζ = q/2 (§1) |
| `alphaZ q` | 133/60 + ¼ log(q²−4) − ⅓ log q | α(q) minus the 2-adic term (§4 l. 200) ✓ |
| `c2Num` | (4/3)·log 2 | Lemma 10″, §2 l. 148 ✓ |
| `qB` | 175 | base 173 on paper (disclosed, §1 above) |
| `PhiB` | −4003/1000 | certificate value; paper's 175 bases: −3.9948 / −4.0052 / −4.0007 (§3 table) |
| `betaZ q` | PhiB − ½ log(q/qB) | shift lemma, Φ_b − ½ log(q/q_b) (§3 l. 167–168) ✓ |

### 4.2 Margin (`QZ/Margin.lean`)

* The statement of `margin_z_proof` (l. 25) is exactly `margin_z`. The proof combines:
  - log(q²−4) < 2 log q;
  - −⅓ log q + ½ log 175 ≤ ⅙ log 175 for q ≥ 175;
  - `log175_lt`, i.e. 175¹⁰⁴ < 2⁷⁷⁵ (l. 17–22, which I checked in Python);
  - `Real.log_two_lt_d9`.
* The closed-form bound 133/60 − 4.003 + (4/3 + 775/624)·0.6931471808 = −0.0012572 matches the header (l. 7,
  "≈ −0.00126").
* My float recomputation of `alphaZ q + c2Num + betaZ q`:

  | q | margin (Lean constants) |
  |---|---|
  | 175 | −0.0013721 (= `margin_check.out`) |
  | 177 | −0.0051593 |
  | 199 | −0.0442043 |
  | 1001 | −0.58266 |
  | 10⁶ | −2.8849 |

  The margin decreases like −⅓ log q, as RESULT §4 says.
* **Why not 173.** With the paper's own base at 173, margin(173) < 0 needs Φ(4/173²) < −3.99971. RESULT's Arb value is
  −4.00053, but Lean's certificate format at L = 1200 reaches only about −4.0033 + ½ log(175/173) ≈ −3.9976 there. So
  175 is the honest Lean threshold. The margin at 175 (−0.00137) is thin but proved with elementary bounds, so the
  thinness is not a fidelity issue.

### 4.3 Lemma 10″ (`QZ/TwoAdicEntries.lean`, `QZ/TwoAdic.lean`): faithful, with weaker entry bounds (disclosed)

* **Exported statement** (`twoAdic_num`, `Interface.lean` l. 41–44): ∃ n₂ with ‖coeff_k Δ_h(·; q/2)‖₂ ≤ 2^{n₂(h)} for
  all h, k, and n₂(h)·log 2 ≤ (c2Num + ε)h² eventually. This is RESULT §2's "n₂ ≤ (4/3)h² + O(h)", in the o(h²) limit
  form that `arith_z` consumes. n₂ upper-bounds −v₂ of every coefficient, as in RESULT.
* **Basis.** `DeltaZ_eq_anchored` (l. 98) uses RESULT's anchored basis a_i = Π_{l<i}(u − x_l),
  b_j = Π_{h−j ≤ m < h}(u − x_m) (`aB`, `bB`), with K = h. The determinant identity is unitriangular.
* **Departures from RESULT §2.** Both are declared in the header (l. 8–12), and both are weaker, never stronger:
  - **(L)** π = i+j+1−h ≥ 1: Lean proves v₂(A) ≥ −π (`V2_A_LZ`, l. 187) and B = 0 (`BfunZ_L`). RESULT has 3 − π
    (corrected after gate F1). The pre-correction duals were checked against 1 − π. Lean's cost π is one more even
    than that.
  - **(U)** N = h−1−i−j ≥ 0: Lean proves v₂(A), v₂(B) ≥ −2i − 3N (`V2_A_UZ`, `V2_B_UZ`) by the naive Δ^N expansion
    (v₂(N!) ≤ N, v₂(x_k S_k) ≥ −2k − 1, v₂(x_k ζ^{2k+1}) = −2k − 2). RESULT has −2i − 3N + s₂(N) via Chu–Vandermonde.
    RESULT's own assignment (l. 139) already drops s₂(N) (c ≤ 3h − 3 − i − 3j = 2i + 3N). So for (U), Lean uses exactly
    the cost RESULT's dual is checked against.
* **Potentials** (`TwoAdic.lean` l. 21–31):
  - U_i = −i or i − a and V_j = 3h − 3j or j + 1 − h + a, with a = ⌈4h/3⌉. These discretise RESULT's u(x) = −x or
    x − 4/3 and v(y) = 3 − 3y or y + 1/3. The extra +1 in V absorbs the weaker (L) bound.
  - `cZ_le_pot` checks c(i,j) ≤ U_i + V_j exactly, in the discrete setting, as RESULT l. 144 asks.
  - `n2Z_eq` and `three_n2Z_le` give the explicit 3n₂ ≤ 4h² + 4h + 4. That is the "explicit O(h) constant" RESULT
    l. 146 says a Lean port needs.
* The 4/3 survives the weaker entries, as RESULT l. 121 predicts. `scripts/q2num/twoadic_z_check.txt` independently
  shows n₂ = closed form, exact −v₂ ≤ n₂, and 0 entry violations for q = 3, 5, … and h ≤ 12. I spot-read this file and
  did not re-run it.
* Docstring nit (S3): `V2_muPolyZ` (l. 170) says "H ∈ ℤ[X]". `IS n R` means v₂(coeff_d R) ≥ d − n, i.e. H is 2-integral
  (ℤ₍₂₎[X]). This is harmless.

### 4.4 Odd primes (`QZ/Arith.lean`): faithful

* p-adic facts at ζ = q/2 for odd p:
  - ‖ζ‖_p = ‖q‖_p (`padicNorm_zq`, l. 29);
  - ‖ζ² − 1‖_p = ‖q² − 4‖_p (`padicNorm_zq_sq`, l. 46).

  These are RESULT §1's "q₀ ∈ ℤ_(p)" and "v_p(ζ₀² − 1) = v_p(q² − 4)" (gate F3).
* `eNz` (l. 84):
  - p ∣ q(q² − 4): 2h·lev + v_p(q²−4)·β(h), with the ‖q‖_p^{aQ h} factor kept in the denominator. This is Lemma 9 after
    clearing E (Lemma 5 + Cor. 9.1) and Lemma 4′(ii).
  - otherwise: `eGen` (Theorem A).

  This is RESULT §1 l. 100–104.
* `denz = 2^{n₂}·N/q^{aQ h}` (l. 121).
  - `denz_int`: at p = 2 it uses only the hypothesis n₂ and ‖q‖₂ = 1 (q odd). At odd p it uses the bound above.
  - `log_denz_le` and `arith_z_proof` give log den ≤ (alphaZ q + c₂ + ε)h².
  - β(h) ≤ (h² + 2h)/4 gives ¼ log(q²−4), and aQ(h) ≥ (h² − 7h − 2)/3 gives −⅓ log q. Each special-prime class is
    counted once: the factor ‖q‖_p^{aQ} sits in the denominator, and `oddPart(q²−4) = q²−4` because q is odd.

### 4.5 Analytic bound and certificate: faithful

* **Theorem B at real weight** (`QZ/TheoremB.lean`).
  - `DualCertW W` (l. 20–33) is `Analytic/TheoremB.lean`'s `DualCert q` with `Wr q` replaced by a real `W`. Its fields
    are the step density μ, λ, L, X, N, the cell bounds S_k, and the cell inequality 2U(x) + V_W(x) ≤ S_k on each cell
    of [0, X], plus two tail conditions.
  - Φ = −E(μ) + λ + (2/L) Σ_k (S_k − λ)₊ (l. 44) is RESULT's and `Cert/Instance.lean`'s.
  - `analyticZ` (l. 395) concludes |aeval (chi2 (1/ζ)) (DeltaZ ζ h)| ≤ exp((Φ + ε)h²) eventually, with W = ζ⁻².
  - The route is `abs_DeltaZ_le_of` (`Nodes.lean` l. 51, truncations HTW → the real moment determinant) plus
    `det_bound`, the same as the integer original. The certificate depends on q only through W, which is RESULT §1
    l. 106.
* **Shift** (`QZ/Shift.lean` l. 19). From C at W₀ and 0 < W ≤ W₀ it builds C′ at W with
  Φ(C′) ≤ Φ(C) − (log W₀ − log W)/4 + δ. This is pilot_q's construction (λ′ = λ − ℓ/2, grid refined by 2r).
  `analytic_of_certZ` (`Analytic.lean` l. 28) turns it into −½ log(ζ/ζ₀), with log W = −2 log ζ (`log_WrZ`). At
  ζ = q/2, ζ₀ = qB/2 this is −½ log(q/qB) (l. 75–80), exactly `betaZ`.
* **The certificate is at ζ_B = 175/2, i.e. w = 4/175².**
  - `CertDataQ175.lean` l. 22–24: `a := 2`, `q := 175`.
  - `cert_zeta` (`Analytic.lean` l. 51) proves `data.q / data.a = zq qB` by `rfl` and `norm_num`.
  - `toCertZ` produces a `DualCertZ (q/a)`, i.e. a `DualCertW (WrZ (175/2))` with `WrZ (175/2) = (2/175)²`.
* **`lw` encloses log w** (`CertInstance.lean` l. 128): `lw = 2·tabIV tab a − 2·tabIV tab q`. `mem_lw` (l. 224) is a
  *theorem*: `lw.mem (log (WrZ (q/a)))`, through `WrZ (q/a) = (a/q)²` and `mem_tabIV` under `checkTab` (kernel-checked).
  So the enclosure is proved, not trusted. As a sanity check I confirmed that tab[1], tab[174] enclose log 2, log 175 to
  2⁻³⁹, and that log w = 2 log(2/175) = −8.9433.
* **`Valid`** (l. 153–167) has every field that `toCertZ` needs.
  - `aq : a < q` gives ζ > 1 (`one_lt_zeta`), which Theorem B and the shift need.
  - `mass : Σc·s = L` and `crange : 0 ≤ c ≤ 2` make μ admissible.
  - `cells` covers all X·L = 1200 cells, and `tail` is htail1/htail2 in interval form.

  `CertQ175.lean` proves each field by `decide +kernel` (33 calls) or `decide`. `cells_of` / `cellsOK_append` combine
  the 24 blocks of 50 cells into [0, 1200) correctly (`comb4_0`, l. 100 ff.; `valid.cells`, l. 128–129).
* **Exponent.** I recomputed PhiQ exactly from `CertDataQ175.lean` with Python `Fraction`: 1200 cell bounds, 70 heights
  (Σc·12 = 1200 ✓), log table 4804. The result is **PhiQ = −4.0033242421 ≤ −4.003** ✓, matching the header (l. 5) and
  `runs/gen_q175.log` (−2401994545239721/600000000000000).
  - `phiQ_le` (l. 134) and `phi_le` (l. 137) are used by `phi_Q175` (`Analytic.lean` l. 56) with `PhiB = −4003/1000`.
  - −E_lo = 2.153111 against RESULT's −E ≈ 2.15307 at 175. The two are different μ (Lean: 70 steps of width 1/100 on
    [0, 0.7]), and `E ≥ E_lo` is kernel-checked (`EOK`). Lean's Φ (−4.0033) lies between RESULT's 150-cell (−3.9948)
    and 300-cell (−4.0052) values at 175.
  - The tail at X = 1: log 1 + log w − λ = −8.943 + 7.797 < 0 ✓.

### 4.6 Nonvanishing (`QZ/NonVan.lean`): a faithful, and stronger, substitute for RESULT §5

RESULT §5 re-reads Lemma P's ~3000-line ℓ-adic proof with ζ₀ = q/2 ∈ ℤ_(ℓ)^× in place of an integer. That is gap G3,
"confirmed in reading" by the gate referee. Lean does not re-read the proof. It **transfers** the integer theorem:

1. **`lemmaP_norm`** (l. 44). This is the refereed integer `lemmaP` with its exact output: the rescaled Gram determinant
   is an ℓ-adic unit, ‖KP ℓ · Δ_{3ℓ}(a/b; q′)‖_ℓ = 1. The proof reuses `det_Ebar_ne_zero` and `det_gram` from
   `NonVan/*`. The normaliser `KP ℓ` (l. 30) is built only from `dPrime`, `kap ℓ = ℓ/2` and `Cm (3ℓ)`, the coefficient
   matrix of `fpoly`. None of these depends on q (checked: `NonVan/Gram.lean` l. 194, `NonVan/Setup.lean` l. 90). So the
   docstring's "independent of the integer q′" is true.
2. **Continuity** (l. 92–145). Every coefficient of Δ_h at both points is the image of the same `(DeltaF h).coeff k`,
   whose Gauss norm is ≤ ℓ^{2h·lev} (`lemma9_DeltaF`). Both evaluation vectors are ℓ-integral, and the points are
   ℓ^{−M}-close. Hence |Δ_h(r; q/2) − Δ_h(r; q′)|_ℓ ≤ ℓ^{2h·lev − M}.
3. **Choice of q′** (l. 222–238). M = 2h·lev + |v_ℓ(KP)| + 1 is fixed before q′. Then q′ = q(ℓ^M + 1)/2, so
   2q′ − q = q·ℓ^M. There is no circularity, because KP does not depend on q′.
4. **Lemma P's hypotheses at q′.**
   - `Good q′ ℓ` (`NonVan/Blocks.lean` l. 17–21) needs q′ ≥ 2, ℓ ≥ 7, ℓ ∤ q′, ℓ ∤ q′² − 1. These follow from ℓ ∤ q and
     ℓ ∤ q² − 4, because 2q′ ≡ q.
   - The three block determinants are ℓ-units. `Q.det_MS_q`, `det_ML_q`, `det_MD_q` (`Q/NonVan.lean` l. 20–51) give
     them as integer polynomials over 9(q′²−1), 2025(q′²−1), 135(q′²−1)². Multiplying the numerator by 2⁸ (2¹⁰ for D)
     and using x = 2q′ ≡ y = q mod ℓ reduces it to `nS q`, `nL q`, `nD q`.
5. **The integers `nS`, `nL`, `nD`** (l. 150–156). I recomputed them by hand from the q′-numerators:
   - 2⁸(72q′⁸ + 8q′⁶) = 72x⁸ + 32x⁶;
   - 2⁸(129600q′⁸ − 84600q′⁶ − 50816q′⁴ + 7240q′²) = 129600x⁸ − 338400x⁶ − 813056x⁴ + 463360x²;
   - 2¹⁰(−16200q′¹⁰ + 51075q′⁸ − 28523q′⁶ − 420q′⁴) = −16200x¹⁰ + 204300x⁸ − 456368x⁶ − 26880x⁴.

   These agree with RESULT §5:
   - nS = 8q⁶(9q² + 4), i.e. ζ and 9ζ² + 1 at ζ = q/2, which is B(S,3)'s prime set.
   - The cubic factors of nL/q² and nD/q⁴ in y = q² have their real roots at ζ = √y/2 ∈ {0.996, 0.350} and
     {1.556, 0.864}. That is RESULT's "all real roots in |ζ| < 1.56" (referee: 1.556).

   `nS_ne`, `nL_ne`, `nD_ne` prove that they are nonzero for q ≥ 5. Hence ℓ > |n·| avoids them, and **the integer
   conditions are justified**.
6. **Assembly** (l. 204–412). ℓ is any prime > N₀ + |nS| + |nL| + |nD| + q² + b + 2026. This is a cofinite set of primes,
   so it avoids RESULT's Bad(q/2): primes dividing 2q(q²−4), the three B-constants, and b, with ℓ ≥ 7. Lemma E is then
   used along h = 3ℓ, exactly as RESULT §5 l. 261–264 and gate F4 require.

The transfer is a rigorous argument for the same conclusion. It replaces gap G3's "proof read at rational ζ" with an
argument that uses only the integer Lemma P, which is already in Lean. The header (l. 1–16) describes it accurately.

## 5. Trust surface

* **Grep.** I searched `QZ/*.lean`, `Chi2Irrational.lean` and `Axioms.lean`, whole words, for: `sorry`, `admit`,
  `axiom`, `native_decide`, `implemented_by`, `extern`, `opaque`, `unsafe`, `ofReduceBool`, `partial`, `debug`,
  `skipKernelTC`, `run_cmd`, `#eval`, `elab`, `macro`, `instance`, `attribute`. There are **no hits**, and no `@[…]`
  attributes in `QZ/`.
* **Options.** There are exactly two `set_option`s:
  - `maxRecDepth 38432 in` on the log-table literal (`CertDataQ175.lean` l. 11);
  - `exponentiation.threshold 2048 in` on `log175_lt` (`Margin.lean` l. 17), which lets `norm_num` evaluate 175¹⁰⁴.

  Both are elaborator limits and do not affect the kernel. `lakefile.toml` has only linter options and
  `maxSynthPendingDepth`.
* **Kernel checks.** The certificate is checked by `decide +kernel` (33 calls in `CertQ175.lean`). The build log
  records 10697 s for that module.
* **Imports.** `Chi2Irrational.lean` l. 70 imports `Chi2Irrational.QZ.Interface`. The QZ-internal imports reach all 18
  `QZ/` files, so there is no orphan.
* **Axioms.** `scripts/q2num/runs/axioms_q2num.txt` has 50 lines, one for each `#print axioms` in `Axioms.lean`. All
  50 are `[propext, Classical.choice, Quot.sound]`, and there is no `sorryAx`. The nine new lines are:

  ```
  'Chi2Irr.QZ.theoremQ4num' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.map_DeltaF_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.irrational_of_boundsZ' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.arith_z' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.twoAdic_num' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.nonvan_z' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.lemmaP_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.analytic_z' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Chi2Irr.QZ.margin_z' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
* **Build log.** `full_build.txt` shows that the first pass failed in `QZ/Analytic.lean` (stale `PhiB` literal). The
  second pass built `Analytic` and `Interface` with "Build completed successfully (9157 jobs)". `QZ.Margin` is marked ⚠
  (a linter warning, text not recorded).
* **Not done.** No `leanchecker` replay exists yet for the QZ modules (S5).

## 6. Findings

### Required (documentation only; no Lean change)

**R1. README.md, TRUST.md and `paper/main.tex` do not mention Theorem Q4′.** (Severity: documentation, required before
release.)
* README l. 1–11 lists only Q₄, Q and q = 3, 5. Add Q4′ with the statement written out, its q₀ = 175 against the
  paper's 173, and the reason for the difference: Lean's certificate is coarser, and 173 would need Φ(4/173²) < −3.99971.
* README / TRUST axiom blocks (README l. ~48, TRUST l. 5–15) list 41 declarations. There are now 50; cite
  `scripts/q2num/runs/axioms_q2num.txt`.
* TRUST l. 18: add `QZ/CertQ175.lean` to the `decide +kernel` list, and note the two elaborator-only `set_option`s.
* TRUST: add a `QZ/Interface.lean` row (`theoremQ4num`), mark `zq`, `alphaZ`, `c2Num`, `qB`, `PhiB`, `betaZ` as
  internal, and add the generator line `gen_cert_z.py 2 175 1200 12 70 1 1`, PhiQ = −4.0033242, and the 10697 s kernel
  time.
* TRUST: update the module count (now 109: the 91 of Q₄ plus the 18 `QZ` files), and record the QZ leanchecker replay
  once it is run (S5).
* Paper: add Q4′, or at least a pointer to `theoremQ4num`. Name it Q4′ to avoid the clash with Theorem Q₄ (χ₂(1/q),
  q ≠ 4).
* List the three declared departures from RESULT:
  - weaker (L)/(U) entry bounds;
  - the base at 175 with L = 1200, X = 1;
  - the ℓ-adic transfer from an integer q′ in place of the rational-ζ reading of Lemma P.

**R2. Handoff (outside this repository).**
* `pilot_chi2_2q/RESULT.md` l. 53–54, l. 66–67 ("Q4 is not in Lean") and §9 ("Lean plan (do not start)") are
  outdated. Point them to `Chi2Irr.QZ.theoremQ4num` (q ≥ 175, standard axioms).
* The G3 entry can record that, for the Lean statement, the rational-ζ reading is replaced by the ℓ-adic transfer of
  §4.6.
* Rename "Theorem Q4" to "Q4′", or add a note, to avoid the clash with `Chi2Irr.Q.theoremQ4`.
* `lean_chi2/CLAUDE.md` should mention Q4′.

### Suggestions (optional docstring fixes; no statement change)

* **S1.** `QZ/Analytic.lean` l. 6: "This is the statement of the stub `analytic_z`". It is no longer a stub. Write
  "the statement of `analytic_z`".
* **S2.** `QZ/Shift.lean` l. 7 cites `DualCertZ.shift`, which does not exist. The declaration is `DualCertW.shift`, and
  the ζ-form is `analytic_of_certZ` in `QZ/Analytic.lean`.
* **S3.** `QZ/TwoAdicEntries.lean` l. 170: "H ∈ ℤ[X]" should read "H 2-integral (ℤ₍₂₎[X])", to match `IS`.
* **S4.** `QZ/Interface.lean` l. 40: the `twoAdic_num` docstring gives "(4/3)h² + O(h)", but the statement is the limit
  form. Add "(stated in limit form; the proof's `n2Z` satisfies 3n₂ ≤ 4h² + 4h + 4)". This is the same remark as S4 of
  `FIDELITY_REFEREE_Q4.md`.
* **S5.** Run `leanchecker` on the 18 `QZ` modules (TRUST's loop), and commit the log next to `axioms_q2num.txt`.
* **S6.** Record the ⚠ text from `QZ.Margin` in the build log, or fix the warning (probably the unused `_ho`, which is
  harmless).
* **S7.** Optional, as S6 of the Q4 report: regenerate `CertDataQ175.lean` with `gen_cert_z.py` and confirm it is
  byte-identical before README/TRUST claim reproducibility.

## Checks performed

* **Read in full:** `QZ/Interface`, `Defs`, `MainCond`, `Margin`, `Machine`, `Arith`, `TwoAdic`, `TwoAdicEntries`,
  `NonVan`, `Analytic`, `CertInstance`, `CertQ175`; root `Defs.lean`, `Machine.lean`, `Criterion.lean`; `Axioms.lean`.
* **Read in part:**
  - `QZ/TheoremB` (structure, Φ, `analyticZ`), `QZ/Shift` (statement and construction), `QZ/PoleExpansion` (header,
    `WrZ`, `pole_seriesZ`), `QZ/Nodes` and `QZ/Dual` (declarations), `CertDataQ175` (record, truncated lists);
  - `Arith/Free.lean` (declarations, `evQ`), `Q/NonVan.lean` l. 20–51, `NonVan/Blocks.lean` l. 17–21, and the
    definitions of `IS`, `V2`, `PN`, `lev`, `eGen`, `betaP`, `aQ`, `Cm`, `kap`.
* **Notes:** RESULT.md (all of it); the verdict table and bottom line of `REFEREE_CHI2_2Q.md`.
* **Documentation:** README.md, TRUST.md and `paper/main.tex`, grepped for Q4′ (absent).
* **Searches and git:**
  - grep for unsafe constructs and options;
  - the QZ import closure;
  - `git status`, `git log`, `git show --stat HEAD`, file timestamps;
  - `full_build.txt`, `gen_q175.log`, `defs_check.out`, `twoadic_z_check.txt` (spot-read).
* **Recomputation** (scratch script, not committed):
  - an exact `Fraction` recomputation of PhiQ, the mass and the list lengths from `CertDataQ175.lean`;
  - log-table enclosures of log 2 and log 175;
  - float margins at q = 173, 175, 177, 199, 1001, 10⁶;
  - the Φ needed for a base at 173;
  - 175¹⁰⁴ < 2⁷⁷⁵;
  - the roots of the nL and nD cubics;
  - a hand derivation of nS, nL, nD from the q′-numerators, and of the dual-potential identities.

Not done: building (as instructed), a leanchecker replay, regenerating the certificate data, and checking proofs (that
is the kernel's job).
