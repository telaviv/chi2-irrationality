# Fidelity referee report: Theorem Q (`Chi2Irr.Q.theoremQ`)

Referee: independent AI fidelity referee (Claude), 2026-11-09. Branch `theorem-q`, HEAD `b5d8fb6` ("Theorem Q complete in
Lean …", committed 13:47:54 while this review ran; it adds `import Chi2Irrational.Q.Interface` to `Chi2Irrational.lean`
and the nine Q lines to `Axioms.lean`). After that commit the working tree equals HEAD for every `.lean` file; the only
untracked files are `scripts/axioms_q.txt`, `scripts/leanchecker_q.log` and this referee's `scripts/q/referee/`. I did not
build anything. I read the axiom output that the running build wrote to `scripts/axioms_q.txt`.
Scope: what is new for Theorem Q. The generic machine, Lemma E, Theorem B and the q = 3, 5 ingredients were already
in the published q = 3, 5 development and were not re-audited.

**Verdict: PASS WITH FIXES.** The Lean statement `TheoremQ` is exactly the paper's combined claim (RESULT §0: Theorem Q,
every odd q ≥ 3, together with Theorem Q_even, every even q ≥ 14). That is, χ₂(1/q) ∉ ℚ for every integer q ≥ 3 except
possibly q ∈ {4, 6, 8, 10, 12}. The exception set is the same. There are no hidden hypotheses, no custom axioms and no
trusted code, and `#print axioms Chi2Irr.Q.theoremQ` gives `[propext, Classical.choice, Quot.sound]`. My independent
interval recomputation confirms every margin. **All required fixes are documentation**: README.md, TRUST.md and
`paper/main.tex` still describe only q = 3, 5 (R1–R3).

---

## 1. Statement fidelity: faithful

`Chi2Irrational/Q/Defs.lean` l. 27–28:

```lean
def TheoremQ : Prop :=
  ∀ q : ℕ, 3 ≤ q → q ∉ ({4, 6, 8, 10, 12} : Finset ℕ) → Irrational (chi2 (1 / (q : ℝ)))
```

* **Quantifiers.** `q : ℕ` with `3 ≤ q` and `q ∉ {4, 6, 8, 10, 12}`. That set is {odd q ≥ 3} ∪ {even q ≥ 14}, which is
  RESULT §0 l. 11–16 ("every odd q ≥ 3"; "every even q ≥ 14"; "every integer q ≥ 3 except possibly
  q ∈ {4, 6, 8, 10, 12}"). q = 1, 2 are not claimed, and are not covered. There are no instance arguments and no
  side hypotheses. `theoremQ` (`Q/Interface.lean` l. 104–118) splits on `Nat.even_or_odd`. In the even branch it
  derives `14 ≤ q` from `hE` by `omega` (l. 107–110), so the odd and even ingredients are used on exactly the hypotheses
  of the theorem.
* **The point.** `1 / (q : ℝ)` is real division after the ℕ → ℝ cast. It is not ℕ division, which would give 0 (the cast
  is explicit). The same expression `chi2 (1 / (q : ℝ))` appears in `MachineBounds.analytic` (`MainCond.lean` l. 34),
  and `irrational_of_bounds` (l. 38) concludes `Irrational (chi2 (1 / (q : ℝ)))` syntactically. So the endgame is about
  the stated number, with no rewriting.
* **The function.** `chi2Term z n := z ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2` and `chi2 z := ∑' n : ℕ, chi2Term z n`
  (`Chi2Irrational/Defs.lean` l. 11, 14). This is Legendre's χ₂(z) = Σ_{n≥0} z^{2n+1}/(2n+1)², unchanged from the
  q = 3, 5 development.
* **Summability.** `summable_chi2Term : |z| ≤ 1 → Summable (chi2Term z)` (`Defs.lean` l. 31–35). It is used where the
  pole expansion splits the series (`PoleSeries.lean` l. 105, 142), and that feeds Theorem B's bound on
  `aeval (chi2 (1/q)) (Delta q h)` at |1/q| ≤ 1/3. The statement could not be vacuous through a junk `tsum` anyway:
  in this Mathlib `∑'` is `tsum f (unconditional _)`, and it is 0 for a non-summable f
  (`Topology/Algebra/InfiniteSum/Defs.lean` l. 143–148). 0 is rational, so `Irrational (chi2 x)` itself forces
  summability at x.
* **Vacuity.** None. The hypotheses hold for infinitely many q, and `Irrational` is Mathlib's.

## 2. Wiring and trusted base: clean

* **Interface.** `theoremQ : TheoremQ` (`Q/Interface.lean` l. 104). Every ingredient is a one-line call to a `_proof`
  theorem:
  - `arith_q` → `arith_q_proof` (l. 40);
  - `twoAdic_odd` → `twoAdic_odd_proof` (l. 46);
  - `twoAdic_even` → `twoAdic_even_proof` (l. 52);
  - `nonvan_q` → `nonvan_q_proof` (l. 58);
  - `analytic_odd` → `analytic_odd_proof` (l. 64);
  - `analytic_even` → `analytic_even_proof` (l. 69);
  - `margin_odd` → `margin_odd_proof` (l. 73);
  - `margin_even` → `margin_even_proof` (l. 77).

  `exists_bounds` (l. 82–101) builds `MachineBounds q` from these, with α = `alphaCore q + c₂` and β = β + δ, where
  δ = −(margin)/2 > 0.
* **Grep of `Chi2Irrational/` and `Chi2Irrational.lean`.** I searched for the whole words `sorry`, `axiom`, `admit`,
  `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `ofReduceBool`, `skipKernelTC`, `debug` and
  `partial`. The only hits are the English word "partial" in two comments (`Arith/QAdic.lean` l. 297,
  `PoleExpansion.lean` l. 8).
  - Under `Q/`, `Cert/Q14.lean` and `Cert/DataQ14.lean` there is no `run_cmd`, `#eval`, `elab`, `macro`, `set_option`,
    `instance` or `attribute`.
  - The q = 14 certificate is checked by `decide +kernel` (17 occurrences in `Cert/Q14.lean`).
  - `lakefile.toml` sets only linter options and `maxSynthPendingDepth`. Neither affects the kernel.
* **Import closure.** I computed it in Python from `Chi2Irrational.lean`, which imports `Chi2Irrational.Q.Interface`
  at l. 68 (committed in `b5d8fb6`). It reaches all 73 modules under `Chi2Irrational/`, including all 10 under `Q/` and
  `Cert/Q14`, `Cert/DataQ14`. No module is orphaned. `defaultTargets = ["Chi2Irrational"]`, so `lake build` now builds
  Q.
* **Dependency cone of the statement:** `chi2`, `chi2Term` (project), and Mathlib's `Irrational`, `tsum`, `Finset`
  literal membership, the ℕ → ℝ cast and real division. None of `alphaCore`, `oddPart`, `c2Odd`, `c2Even`, `betaOdd`,
  `betaEven`, `Delta`, `DualCert`, `MachineBounds` is in it. All of them are internal: a wrong one can only make the
  proof fail.

## 3. Constants and margins: recomputed independently, all negative

Script: `scripts/q/referee/margin_q_referee.py` (output `margin_q_referee.out`). It shares no code with
`scripts/q/margin_check.py`. It uses mpmath `iv` at 200 bits and transcribes `Q/Defs.lean` l. 31–47 literally:
alphaCore = 133/60 + ¼ log oddPart(q²−1) − ⅓ log oddPart(q); c2Odd = (v₂(q²−1) − 2)/4·log 2;
c2Even = (½ − v₂(q)/3)·log 2; betaOdd = −2.078 − ½ log(q/3); betaEven = −3.03 − ½ log(q/14).

* **Odd 3 ≤ q ≤ 5001** (2500 values): every interval is < 0. The worst is q = 3 with **≤ −0.0542506**, matching the
  Defs docstring (−0.05425).
* **Even 14 ≤ q ≤ 5000** (2494 values): every interval is < 0. The worst is q = 14 with **≤ −0.0281956**, matching
  −0.0282. The same formula at q = 12 gives +0.0227, so q = 12 is correctly excluded. Its exclusion is not an artefact
  of `TheoremQ`, which excludes it explicitly anyway.
* For all q, Lean proves the margins by closed forms (`Q/Margin.lean` l. 45–97). I evaluated both constants:
  - odd: 133/60 − 2.078 − ½ log 2 + ⅙ log 3 = −0.0248;
  - even: 133/60 − 3.03 + (7/6) log 2 = −0.00466.

  Both are negative, consistent with the scan.
* **Match with the paper's formulas.** Lean's alphaCore + c₂ equals the paper's α(q) = 133/60 − ½ log 2 + ¼ log(q²−1) −
  ⅓ log q (odd, RESULT §1). It also equals α_even(q) = 133/60 + ½ log 2 + ¼ log(q²−1) − ⅓ log q (even, RESULT §4.2).
  The maximum difference over both ranges is 2·10⁻⁵⁹, which is interval width. The identity holds exactly because
  log(q²−1) = v₂·log 2 + log oddPart, and the v₂ terms cancel against c₂. I reproduce α(3) = 2.0237494,
  α(5) = 2.1281272 and α_even(14) = 3.0018044 as in RESULT. With the paper's Φ₃ = −2.0987404387 I reproduce the q = 3
  margin −0.074991 and the closed-form constant 0.320658782. With Lean's −2.078 that constant is 0.341399, which
  matches the "0.3414" in the `margin_odd` docstring and RESULT §7.2(d).
* **Certificates, recomputed exactly** (python Fractions from the Lean data files, using PhiQ = −Elo + λ +
  (2/L)Σ_k(S_k − λ)₊ as in `Cert/Instance.lean` l. 78–81):
  - `DataQ3`: q = 3, L = 100, 300 cells, PhiQ = −2.0783260426 ≤ −2.078.
  - `DataQ14`: q = 14, L = 200, 400 cells, **PhiQ = −3.0372394261 ≤ −3.03**, as its docstring claims.

  `analytic_even_proof` (`Q/Analytic.lean` l. 45–50) uses exactly this certificate: `Cert.CData.toCert Cert.Q14.valid`
  with `Cert.Q14.phi_le : Phi ≤ −303/100` (`Cert/Q14.lean` l. 67–73, from `phiQ_le` by `decide +kernel`), shifted from
  q₀ = 14. `analytic_odd_proof` (l. 37–42) uses `Cert.Q3.valid` with `phi_Q3 : Phi ≤ −2078/1000`, shifted from q₀ = 3.

## 4. Departures from the paper (declared, harmless)

* **Φ₃.** Lean uses −2.078 (the kernel-checked `Cert/Q3.lean`) instead of the paper's −2.0987404387. The q = 3 margin
  becomes −0.0543 instead of −0.0750. Lean shifts every odd q from the q = 3 base. RESULT's table uses the q = 5 base
  for q ≥ 5, but the closed form uses Φ₃ too, so nothing that is claimed is lost.
* **q = 14.** Lean has its own certificate (`scripts/gen_cert.py 14 200 4 40 2 1`, Φ ≤ −3.03724, used as ≤ −3.03). The
  paper rests q = 14 on the referee's float-free certificate (Φ ≤ −3.0444074), with the pilot's e29 run at −3.0498.
  Lean's value is weaker but kernel-checked, so the float caveat (R4-5) does not arise. The q = 14 margin is −0.0282
  instead of −0.0426.
* **Shift lemma.** It is discretised (`Q/Shift.lean` header): the Riemann sum costs ℓ/(4m), which is absorbed by δ.
  This is declared in the file and has no effect on the constants.
* **Lemma 4′(ii)** is applied prime by prime to the odd part of q. The 2-adic share of the q-adic gain sits in c2Even
  (Lemma 10₀). RESULT §4.1 does the same. The general-ν Lemma 10 (L) half, which RESULT §1 calls paper-only, is now
  Lean-proved inside `twoAdic_odd_proof`. That makes Lean *stronger* than the RESULT caveat.

## 5. Mathlib definitions relied on (v4.35.0)

`Irrational x := x ∉ Set.range ((↑) : ℚ → ℝ)` (`NumberTheory/Real/Irrational.lean` l. 34–35). `tsum` (with the
summation filter `unconditional`, `Topology/Algebra/InfiniteSum/Defs.lean` l. 143) is the unconditional sum, or 0. The
statement also uses `Finset` insert/singleton notation with decidable ℕ membership, `Nat.cast : ℕ → ℝ` and real `HDiv`.
The internal constants use `Real.log`, `padicValNat` and ℕ division, but these are not in the statement.

## 6. Axioms

`scripts/axioms_q.txt` (written 13:47 by `lake env lean Axioms.lean` on the build of the current tree) has 37 lines,
all of them `[propext, Classical.choice, Quot.sound]`. This includes:

```
'Chi2Irr.Q.theoremQ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the same for `arith_q`, `twoAdic_odd`, `twoAdic_even`, `nonvan_q`, `analytic_odd`, `analytic_even`, `margin_odd`,
`margin_even`, and the 28 earlier entries. There is no `sorryAx`. `scripts/leanchecker_q.log` had 7 lines, all rc=0
(Analytic modules), when I looked. The replay was still running and had not yet reached `Q/`.

## 7. Findings

### Required fixes (documentation pass)

**R1. README.md** still describes only q = 3, 5:
* l. 1 (title), l. 3–7 (Theorem box), l. 9–10;
* l. 12–29: the Lean block and axiom lines. Add `Chi2Irr.Q.TheoremQ` written out and `theoremQ` with its axiom line;
* l. 56 ("Fix q ∈ {3, 5}");
* l. 71 (α only for q = 3, 5): add alphaCore + c₂ and the two closed forms;
* l. 93 (certificates): add q = 14 with Φ ≤ −3.03 and the shift lemma;
* l. 103 (margins): add odd q ≥ 3, worst q = 3 at −0.0543, and even q ≥ 14, worst q = 14 at −0.0282, both by closed
  forms;
* l. 115 (build time): the q = 14 kernel check alone is about 233 s according to CLAUDE.md;
* l. 119–120: the byte-identical regeneration claim lists only DataQ3 and DataQ5. Add DataQ14 and its command;
* l. 126–138 (layout): no `Q/` row, no `Cert/Q14`, and l. 136 says "nonvanishing for q = 3, 5". `Q/NonVan.lean` has
  the closed forms in q;
* l. 149 (thin margin): add q = 14 even at −0.0282.

Also state the exception set {4, 6, 8, 10, 12}, and say that q = 2 is open.

**R2. TRUST.md:**
* l. 5–10: the axiom block. There are now 37 entries; add `Chi2Irr.Q.theoremQ`.
* l. 15–19: add `Cert/Q14.lean` to the `decide +kernel` list. The "six block determinants … `norm_num`" item should also
  mention that `Q/NonVan.lean` computes them as rational functions of q.
* l. 24, 31: "61 project modules". There are now 73. The replay covers the Q modules only once `leanchecker_q.log`
  finishes; record that result.
* l. 41–44: the statements table. Add a `Chi2Irrational/Q/Defs.lean` row with `TheoremQ` written out (l. 27–28). Add
  a note that `summable_chi2Term` covers |1/q| ≤ 1/3, and that `alphaCore`, `c2Odd`, `c2Even`, `betaOdd`, `betaEven`,
  `oddPart` are internal.
* l. 48: "The main theorems … `Arith/Assembly.lean`". Add `Q/Interface.lean`.
* l. 53–59: "Two Lean files". There are now three. Add the `Cert/DataQ14.lean` row (log table size, 40 cells, generator
  `python scripts/gen_cert.py 14 200 4 40 2 1 …`).
* l. 62–63, 74, 77–78: add q = 14 (PhiQ < −3.03).
* l. 82–83: build time.

**R3. Paper `paper/main.tex`** (the q = 3, 5 paper). One sentence is now false. The rest is scope that should say what
the repository now contains.
* **l. 1282–1287** (§ "Other values of q"): "We expect the method to prove χ₂(1/q) ∉ ℚ for every q ≥ 3 … We have not
  carried this out." This is false now. Theorem Q is carried out and kernel-checked, except for {4, 6, 8, 10, 12}, so
  "every q ≥ 3" also needs the even-q caveat (Lemma 10₀, q = 4 fails even with ideal arithmetic). Replace it with a
  statement of Theorem Q, its Lean name and the two closed-form margins.
* l. 58–69 (abstract) and l. 186–197 ("two dual certificates", "six block determinants"): these describe the formalised
  content as q = 3, 5 only. At least add a sentence that the repository also proves Theorem Q.
* l. 1151–1157: "61 Lean files … about 18,000 lines". It is now 73 files and about 19,600 lines.
* l. 1160–1184: the statement and axiom quote.
* l. 1187–1215: Table `tab:lean`. Add the Q rows (`Q/Defs`, `Q/Interface`, `Q/Shift`, `Q/Arith`, `Q/TwoAdic*`,
  `Q/NonVan`, `Q/Margin`, `Cert/Q14`).
* l. 1238–1248: "both data files". There are now three.
* l. 1251–1252: cost.
* l. 1258: "61 project modules".

If the author prefers to keep the paper about q = 3, 5 only, then at minimum l. 1282–1287 must be corrected and a
pointer to the `theorem-q` formalisation added.

### Suggestions (not required)

* **S1.** Commit `scripts/axioms_q.txt` now, and `scripts/leanchecker_q.log` once all 73 modules report rc=0. Both are
  untracked.
* **S2.** `Q/Interface.lean` l. 30: the section is headed "The ingredients (stubs)", but they are not stubs any more.
  Rename it as was done for V, e.g. "(each proved as `<name>_proof`)".
* **S3.** `Q/Defs.lean` l. 16–17: it reads as if the Lean certificate is the referee's (−3.0444). Say "Lean's own
  certificate `Cert/Q14.lean` gives PhiQ = −3.03724; the referee's float-free one gives −3.0444".
* **S4.** Handoff, not part of this repository: `handoff/log2log3/pilot_q/RESULT.md` l. 4 ("Not in Lean for any
  q ∉ {3, 5}"), l. 19, l. 38–39 (the general-ν (L) half is now Lean-proved), l. 192 and the §7.2 plan at l. 203 are
  outdated.
* **S5.** `Interface.lean` l. 71's "closed form 0.3414 − ⅓ log q" is the bound before q ≥ 3 is used. `Margin.lean`'s
  final constant is −0.0248. A cross-reference would help readers.

## Checks performed

* I read in full: `Q/Defs.lean`, `Q/Interface.lean`, `Q/Analytic.lean`, `Q/Margin.lean`, `Cert/Q14.lean`, `Cert/Q3.lean`,
  `MainCond.lean`, `Defs.lean`, and the `DataQ14.lean` header and record.
* I read in part: the `Q/Shift.lean` header and statement, the `Q/NonVan.lean` header, `Cert/Instance.lean` l. 60–90,
  and `Criterion.lean` l. 54–60.
* RESULT.md (all of it). README.md, TRUST.md, CLAUDE.md. paper/main.tex l. 55–70, 184–220, 335–342, 1148–1300.
* Grep for unsafe constructs and options. Import closure in Python. `git log`, `git status`, `git show HEAD --stat`,
  `git diff HEAD`.
* Mathlib source of `Irrational` and `tsum`.
* Independent interval recomputation of both margin families, and exact recomputation of PhiQ for q = 3 and q = 14.
* `scripts/axioms_q.txt` read.

Not done: building (as instructed), and the leanchecker replay (still running).
