# Fidelity referee report: Theorem Q₄ (`Chi2Irr.Q.theoremQ4`)

Referee: independent AI fidelity referee (Claude), 2026-11-09. Branch `theorem-qeven`, HEAD `bc9d040` ("Theorem Q4
complete in Lean …", 18:33:49). `git diff HEAD` is empty for every tracked file. The untracked files are
`scripts/axioms_q4.txt`, `scripts/leanchecker_q4.log` and this referee's `scripts/q/referee_q4/`. I did not build
anything. I read the axiom output that the build wrote to `scripts/axioms_q4.txt` (18:33:40). That is after the last
edits to `.lean` files (18:30:42) and 9 s before the commit, so it belongs to the committed tree.

Scope: what is new for Q₄. That is `Q/Even/*` and `Cert/{Q,DataQ}{6,8,10,12}.lean`, and how they are wired into
Theorem Q. Theorem Q itself was audited in `FIDELITY_REFEREE_Q.md` (PASS WITH FIXES) and was not re-audited.

**Verdict: PASS WITH FIXES.** The Lean statement `TheoremQ4` is exactly the headline of `pilot_qeven/RESULT.md`
(l. 10, l. 33): χ₂(1/q) ∉ ℚ for every integer q ≥ 3 except possibly q = 4.
* There are no hidden hypotheses, no custom axioms and no trusted code.
* `#print axioms Chi2Irr.Q.theoremQ4` gives `[propext, Classical.choice, Quot.sound]`.
* The constants `cE` and `c2EvenSharp` are RESULT's c(e) and (c(e) − e/3)·log 2.
* `twoAdic_even_sharp` is Lemma 10_e for the same Δ_h as Theorem Q. The 2-adic share −a(h)·e is counted once.
* My independent interval recomputation confirms all four margins and all four certificate exponents.

**All required fixes are documentation.** README.md, TRUST.md and `paper/main.tex` still say that q = 6, 8, 10, 12 are
open and that only Theorem Q is formalised (R1–R3). In the paper, two passages are now false (l. 1305–1307 and
l. 1392–1393).

---

## 1. Statement and constants (`Q/Even/Defs.lean`): faithful

* **`TheoremQ4`** (l. 22):

  ```lean
  def TheoremQ4 : Prop := ∀ q : ℕ, 3 ≤ q → q ≠ 4 → Irrational (chi2 (1 / (q : ℝ)))
  ```

  The quantifier is over `q : ℕ` with `3 ≤ q`. The only exception is `q ≠ 4`, the same as RESULT l. 10 and l. 33.
  q = 1, 2 are neither claimed nor covered, as in RESULT. There are no instance arguments or side hypotheses.
  `1 / (q : ℝ)` is real division after the explicit ℕ → ℝ cast. It is the same expression as in `TheoremQ`
  (`Q/Defs.lean` l. 28), whose cast, `chi2`/`tsum` and summability were audited in `FIDELITY_REFEREE_Q.md` §1. The
  dependency cone of the statement is the same as for `TheoremQ`, minus the Finset literal. None of `cE`,
  `c2EvenSharp`, `PhiT`, `newQ`, `DualCert` or `Delta` occurs in it.
* **`cE`** (l. 25): `(6 − 4e)/(3(3e + 8))` over ℚ. This is RESULT l. 16 literally. My script gives cE(1, 2, 3) =
  2/33, −1/21, −2/17, as in RESULT l. 18.
* **`c2EvenSharp`** (l. 28–29): `(cE(v₂ q) − v₂(q)/3) · log 2`, with `v₂ = padicValNat 2`. This is RESULT §0 l. 23–24
  ("`(c(e) − e/3)·log 2`, e = v₂(q)"). Adding `alphaCore q` (`Q/Defs.lean` l. 34–35) gives RESULT's
  α_e(q) = 133/60 + ¼ log(q² − 1) − ⅓ log q + c(e) log 2 (l. 25). My script finds a difference of at most 2·10⁻⁷⁶ at
  q = 6, 8, 10, 12, which is the interval width. The identity is exact, because q² − 1 is odd and
  −⅓ log q = −⅓ log oddPart(q) − (e/3) log 2.
* **`PhiT`** (l. 32–37): −2.56, −2.72, −2.85, −2.95 at q = 6, 8, 10, 12, and 0 elsewhere. The 0 is used only under
  `q ∈ newQ`, so it is harmless.
* **`newQ`** (l. 40): `{6, 8, 10, 12}`.

## 2. Wiring and trusted base (`Q/Even/Interface.lean`): clean

* `theoremQ4 : TheoremQ4` (l. 61–68). If `q ∈ newQ`, it uses `irrational_newQ`. Otherwise it calls `theoremQ q hq _`,
  and `omega` derives `q ∉ {4, 6, 8, 10, 12}` from `q ≠ 4` and `q ∉ newQ`. So for every q ∉ {4, 6, 8, 10, 12} the
  proof reuses Theorem Q (`Q/Interface.lean` l. 104), as RESULT l. 32–33 says ("With Theorem Q this gives").
* The three new ingredients are one-line calls to `_proof` theorems:
  - `twoAdic_even_sharp` → `twoAdic_even_sharp_proof` (l. 26–29; `Q/Even/TwoAdicSharp.lean` l. 168);
  - `cert_newQ` → `cert_newQ_proof` (l. 32–33; `Q/Even/Certs.lean` l. 19);
  - `margin_newQ` → `margin_newQ_proof` (l. 36–37; `Q/Even/Margin.lean` l. 36).
* `irrational_newQ` (l. 49–58) feeds them into Theorem Q's `exists_bounds` (`Q/Interface.lean` l. 82). The inputs are
  c₂ = `c2EvenSharp q` and β = `PhiT q`. The analytic bound comes from `C.analytic`, a certificate taken directly at q
  with no shift. The step `Φ ≤ PhiT q ≤ PhiT q + δ` is handled by `nlinarith`. The other inputs are the remaining
  Theorem Q ingredients (`arith_q`, `nonvan_q`), and the result goes to `irrational_of_bounds`.
* **Grep** of `Chi2Irrational/` and `Chi2Irrational.lean`, whole words: `sorry`, `axiom`, `admit`, `native_decide`,
  `implemented_by`, `extern`, `unsafe`, `opaque`, `ofReduceBool`, `skipKernelTC`, `debug`, `partial`.
  - The only hits are the two English uses of "partial" in comments (`Arith/QAdic.lean` l. 297,
    `PoleExpansion.lean` l. 8), as before.
  - In `Q/Even/` and the eight new `Cert/` files there is no `run_cmd`, `#eval`, `elab`, `macro`, `instance`,
    `attribute` or `@[…]`.
  - The only option is `set_option maxRecDepth 19232 in` on the log-table literal of `Cert/DataQ6.lean` l. 11.
    It is an elaborator recursion limit and does not affect the kernel.
  - Each certificate is checked by `decide +kernel`: 23 calls in `Cert/Q6.lean`, 15 in each of Q8, Q10 and Q12.
  - `lakefile.toml` is unchanged (linter options, `maxSynthPendingDepth`).
* **Imports.** `Chi2Irrational.lean` l. 69 imports `Chi2Irrational.Q.Even.Interface` (added in `bc9d040`). I computed
  the import closure in Python: it reaches all 91 modules under `Chi2Irrational/`, with no orphan.

## 3. Margins and certificates: recomputed independently

The script is `scripts/q/referee_q4/margin_q4_referee.py`, with output `margin_q4_referee.out`. It uses mpmath `iv` at
256 bits and shares no code with `scripts/q/margin_newQ_check.py`. It transcribes the Lean definitions literally.

| q | e | oddPart(q²−1) | oddPart(q) | cE | `alphaCore + c2EvenSharp + PhiT` (Lean constants) | Lean's proved bound (`Margin.lean` doc) | RESULT margin with pilot Φ (reproduced) |
|---|---|---|---|---|---|---|---|
| 6 | 1 | 35 | 3 | 2/33 | **−0.0097406** | −0.00904 | −0.0201782 |
| 8 | 3 | 63 | 1 | −2/17 | **−0.2422436** | −0.238 | −0.2640729 |
| 10 | 1 | 99 | 5 | 2/33 | **−0.2100728** | −0.203 | −0.2294905 |
| 12 | 2 | 143 | 3 | −1/21 | **−0.3539314** | −0.304 | −0.3749556 |

* All four intervals are negative. The last column reproduces RESULT §0 l. 42–45 to 7 digits, and q = 4 gives
  +0.0897627 (fails), as in RESULT l. 41.
* The q = 6 margin with Lean's constants is thin. A negative margin needs PhiT(6) < −2.5502594, and Lean uses −2.56.
  `Margin.lean` proves the margin with elementary log bounds (bound −0.00904), so the thinness is not a fidelity issue.
* **Certificates.** I recomputed PhiQ = −Elo + λ + (2/L) Σ_k (S_k − λ)₊ (`Cert/Instance.lean` l. 78–81) exactly, with
  Python `Fraction`, from the data files:

  | file | L | #S_k | log table | cells K | PhiQ (exact) | ≤ PhiT | slack |
  |---|---|---|---|---|---|---|---|
  | `DataQ6` | 400 | 800 | 2404 | 54 | −2.5635463721 | ≤ −2.56 ✓ | 0.0035 |
  | `DataQ8` | 200 | 400 | 1204 | 50 | −2.7264892317 | ≤ −2.72 ✓ | 0.0065 |
  | `DataQ10` | 200 | 400 | 1204 | 46 | −2.8528812698 | ≤ −2.85 ✓ | 0.0029 |
  | `DataQ12` | 200 | 400 | 1204 | 46 | −2.9535971042 | ≤ −2.95 ✓ | 0.0036 |

  These equal the generator values in the brief: −2.5635464 (rounded), −2.7264892, −2.8528813, −2.9535971.
* `Cert/Q{6,8,10,12}.lean` each prove `phiQ_le : data.PhiQ ≤ PhiT` by `decide +kernel` (Q6 l. 100; Q8, Q10, Q12
  l. 68). They then prove `phi_le : (toCert valid).Phi ≤ PhiT` (Q6 l. 103; others l. 71).
* `Q/Even/Certs.lean` l. 22–25 uses exactly `Cert.Q6.phi_le`, …, `Cert.Q12.phi_le`, with `norm_num [PhiT]` matching
  the literals.
* Every Lean PhiQ is weaker than the float-free certified Φ of RESULT / CERTS.md, by 0.004 to 0.017 (q = 12: −2.9536
  vs −2.9710). That is declared in `Q/Even/Defs.lean` l. 11–13, and nothing claimed is lost.

## 4. Lemma 10_e statement (`Q/Even/TwoAdicSharp.lean` l. 168–170, re-exported in `Interface.lean` l. 26–28)

```lean
theorem twoAdic_even_sharp (q : ℕ) (hq : 3 ≤ q) (he : Even q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2EvenSharp q + ε) * (h : ℝ) ^ 2
```

* **Normalisation of Δ_h.** The theorem uses `Delta q h`, the same polynomial that Theorem Q's `twoAdic_even`
  (`Q/Interface.lean` l. 49–51) and `arith_q` (l. 35–36) use. Its form is identical to `twoAdic_even`, with `c2Even`
  replaced by `c2EvenSharp`. That is RESULT's interface (§0 l. 22–24: "Lemma 10_e replaces Lemma 10₀'s ½ … nothing
  else changes") and REFEREE_QEVEN #8 (same Δ_h as defines F_h). The first conjunct makes n₂(h) an upper bound for
  −v₂ of every coefficient, i.e. for RESULT's n₂ = −v₂(Δ_h(q₀)).
* **Leading constant.** RESULT gives n₂ + e·a(h) ≤ c(e)h² + O(h log h), with a(h) = h²/3 + O(h). So the limit
  constant is (c(e) − e/3) per h², i.e. `c2EvenSharp q` in log-2 units.
  - The proof's explicit n₂ (`n2E e h = h − ⌈R(h)⌉`, with R(h) = m_e h² − h(3e/2 + 4⌊log₂ h⌋ + 4) and
    m_e = e − 2(e+1)²/(3e+8)) is an O(h log h) form, as in RESULT step 6–7.
  - `c2EvenSharp_eq` (l. 157–165) proves −m_e·log 2 = c2EvenSharp q, and I re-derived the identity
    e/3 − m_e = (6 − 4e)/(3(3e+8)) by hand.
  - The exported statement is the weaker o(h²) ε-form, which is all the chain uses.
* **The −a(h)·e share is counted once.** The 2-adic part of q appears only in `c2EvenSharp` (as −e/3). `alphaCore` uses
  `oddPart q` (Lemma 4′(ii) only at odd p) and `oddPart(q² − 1) = q² − 1`, which is odd. This matches RESULT l. 26–28.
* **Specialisation at q₀.** `padicNorm_Delta_of_WLe` (l. 107–153) is step 1 of RESULT. Its hypotheses are
  |q₀|₂ = 2^{−e} and q₀² − 1 odd, and it clears (q² − 1)^β as RESULT l. 93–95 does.
* **Proof route.** The Lean proof routes the count through Andreief on the truncated slot matrix `Mdec` of Lemma 4′
  (`Terms.lean`, `CoreDet.lean`, `Count.lean`, `NuBound.lean`), not the confluent Cauchy–Binet formula of RESULT
  step 2. It is the same slot expansion in different coordinates, and it is declared in the file headers.

## 5. Axioms

`scripts/axioms_q4.txt` has 41 lines, one for each `#print axioms` in `Axioms.lean`. All 41 are
`[propext, Classical.choice, Quot.sound]`, and there is no `sorryAx`. The new lines are:

```
'Chi2Irr.Q.theoremQ4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.Q.twoAdic_even_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.Q.cert_newQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.Q.margin_newQ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/leanchecker_q4.log` had 1 line when I looked (`Chi2Irrational.Analytic.Andreief rc=0`). The replay of the
91 modules was still running.

## 6. Findings

### Required fixes (documentation)

**R1. README.md** still presents Theorem Q as the main result, with q = 6, 8, 10, 12 open.
* l. 1 (title "except possibly 4, 6, 8, 10, 12"), l. 7 (Theorem box), l. 11–15: "The five even values
  q = 4, 6, 8, 10, 12 are open". State Theorem Q₄ and keep Theorem Q as the intermediate result.
* l. 24–27 and l. 36–40: add `Chi2Irr.Q.TheoremQ4` written out (`Q/Even/Defs.lean` l. 22), `theoremQ4`, and its axiom
  line.
* l. 46–47: "describes the formalisation of Theorem Q". Add Q₄.
* l. 56: "Theorem Q is new for 3 ≤ q < 2949". This now applies to Q₄.
* l. 110–111: certificates. Add q = 6, 8, 10, 12 (Φ ≤ −2.56, −2.72, −2.85, −2.95; used directly, no shift).
* l. 125–166, step 6:
  - add a Lemma 10_e bullet (`Q/Even/`, c₂ = (c(e) − e/3)·log 2, c(e) = (6 − 4e)/(3(3e+8)));
  - l. 151–153 ("which is why the even values below 14 are excluded") and l. 164–166 ("the even values q ≤ 12 are
    open") are now false;
  - add the four margins (−0.0097, −0.242, −0.210, −0.354).
* l. 175 ("9121 jobs") and l. 179–180 (build time): the four new kernel checks are not timed.
* l. 184–186: the byte-identical regeneration claim lists only DataQ3, 5, 14. Add DataQ6, 8, 10, 12 only after
  checking that the claim holds for them; I did not regenerate them.
* l. 202 ("three kernel-checked dual certificates (q = 3, 5, 14)"): there are now seven. l. 204: no `Q/Even/` row.
  l. 207: add `axioms_q4.txt` and `leanchecker_q4.log`. l. 209: add this report.
* l. 222: "−0.0282 for q = 14, the worst even case". The worst even case is now q = 6 at −0.0097, the thinnest
  margin in the repository.

**R2. TRUST.md**
* l. 5–13: add the `theoremQ4` axiom line. There are now 41 declarations, not 37, with output in
  `scripts/axioms_q4.txt`.
* l. 17–18: add `Cert/Q6`, `Q8`, `Q10`, `Q12.lean` to the `decide +kernel` list. Optionally note the elaborator-only
  `set_option maxRecDepth` in `DataQ6.lean`.
* l. 27–29: there are now 91 modules, not 73. Record the result of `leanchecker_q4.log` when it finishes.
* l. 49–53: add a `Q/Even/Defs.lean` row with `TheoremQ4` written out, proved in `Q/Even/Interface.lean`.
* l. 59–62: add `Q/Even/Interface.lean`. Mark `cE`, `c2EvenSharp`, `PhiT`, `newQ` as internal.
* l. 66 ("Three Lean files"), l. 69–73, l. 76–77 ("all three files"): add four rows, with generators `gen_cert.py 6 400
  8 54 2 2` (log table 2404, 54 cells, 800 cell bounds), `8 200 4 50 2 1`, `10 200 4 46 2 1`, `12 200 4 46 2 1` (log
  table 1204 each). Re-confirm the byte-for-byte claim.
* l. 88–93: add PhiQ = −2.5635464, −2.7264892, −2.8528813, −2.9535971 (each < PhiT).
* l. 95–96: add that q = 6, 8, 10, 12 use direct certificates, not shifted.
* l. 100–108: add the Lemma 10_e gate referee (`pilot_qeven/referee/REFEREE_QEVEN.md`, PASS WITH FIXES) and this
  fidelity report.
* l. 112–114: cost and job count.

**R3. `paper/main.tex`**
* **l. 1305–1307 (false now):** "For even q ≤ 12 … the margin is positive. A sharper 2-adic bound might reach
  q = 6, 8, 10, 12". Lean now proves exactly that, with Lemma 10_e. Replace this with the statement of Q₄. Keep the
  sentence that q = 4 fails for this machine (RESULT l. 52: it would need c(2) < −0.177).
* **l. 1392–1393 (false now):** "The even values q ≤ 12 remain open". Also l. 1386–1387 (c₂ = ½ for even q) and
  l. 1389–1391 (Theorem Q as the final result).
* l. 70 (abstract) and l. 194–196: "q ∉ {4, 6, 8, 10, 12}". Change to q ≠ 4, or add Q₄.
* l. 1158–1160: "73 Lean files … 19,600 lines … other 12". It is now 91 files and about 22,000 lines (`wc`: 21,966).
* l. 1187–1191: add `theoremQ4`. There are now 41 declarations, not 37.
* l. 1247–1303 (§ General q): add Q₄ after Theorem Q, with the Lemma 10_e bullet and the four direct certificates.
* l. 1312–1328, Table `tab:leanQ`: add rows for `Q/Even/Defs`, `Q/Even/Interface` (`theoremQ4`),
  `Q/Even/TwoAdicSharp` (+ `WNorm`, `Terms`, `CoreDet`, `Count`, `NuBound`), `Q/Even/Certs`, `Cert/Q6–Q12` and
  `Q/Even/Margin`.
* l. 1331–1342: "all three data files". There are now seven.
* l. 1347–1348: cost.
* l. 1359–1360: "all 73 project modules". Update when the q4 replay finishes.

If the author keeps the paper about q = 3, 5 plus Theorem Q only, at minimum l. 1305–1307 and l. 1392–1393 must be
corrected, and a pointer to `theoremQ4` must be added.

### Suggestions (not required)

* **S1.** Commit `scripts/axioms_q4.txt` now, and `scripts/leanchecker_q4.log` once all 91 modules report rc=0. Also
  commit `scripts/q/referee_q4/`.
* **S2.** `Q/Even/Defs.lean` l. 14: q = 10 is listed as "−0.209". The value is −0.2101 (rounds to −0.210). The other
  three are right.
* **S3.** `Q/Even/Certs.lean` l. 6: "−2.5635463" truncates −2.56354637. Write −2.5635464, as `Cert/Q6.lean` and the
  generator log effectively do.
* **S4.** `Q/Even/Interface.lean` l. 24–25: the docstring gives the O(h log h) form, while the theorem states the o(h²)
  limit form. Add "(stated in limit form; the proof's `n2E` is the O(h log h) form)".
* **S5.** Handoff (outside this repository):
  - `pilot_qeven/RESULT.md` l. 4 ("not in Lean") and §7 item 3 are outdated.
  - `pilot_q/RESULT.md` l. 4 and l. 13 (exceptions {2, 4, …, 12}) should point to Q₄.
  - `lean_chi2/CLAUDE.md` mentions only Theorem Q.
* **S6.** Optional: regenerate DataQ6, 8, 10, 12 with `scripts/gen_cert.py` and confirm they are byte-identical before
  adding them to the README/TRUST claim (see R1, R2).

## Checks performed

* **Read in full:** `Q/Even/Defs.lean`, `Interface.lean`, `Certs.lean`, `Margin.lean`, `TwoAdicSharp.lean`;
  `Cert/Q6.lean`, `Q8.lean`, `Q10.lean`, `Q12.lean`; `Q/Defs.lean`, `Q/Interface.lean`.
* **Read in part:** the headers of `WNorm`, `CoreDet`, `Count`, `Terms`, `NuBound`; the headers and records of
  `DataQ6`–`DataQ12`; `Cert/Instance.lean` l. 50–100.
* **Notes:** `pilot_qeven/RESULT.md` (all of it); the verdict of `REFEREE_QEVEN.md`.
* **Documentation:** README.md, TRUST.md, `paper/main.tex` l. 55–72, 110–120, 186–200, 1150–1200, 1240–1415.
* **Searches and git:** grep for unsafe constructs and options; import closure in Python; `git log`, `git status`,
  `git show HEAD`, file timestamps.
* **Recomputation:** an independent interval recomputation of the four margins and of RESULT's margins, and an exact
  recomputation of PhiQ for q = 6, 8, 10, 12.
* **Axioms:** `scripts/axioms_q4.txt` read.

Not done: building (as instructed), the leanchecker replay (still running), regenerating the data files, and checking
the proof of Lemma 10_e (out of scope).
