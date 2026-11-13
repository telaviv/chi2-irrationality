# Gate referee T5: Theorem B extended to q ≥ 5 (Lemma M, q = 5 certificate), changed sections of paper_q/main.tex

* **Date:** 2026-11-13
* **Referee:** a fresh AI gate referee (Claude), adversarial, with no earlier involvement in Lemma M or this paper. No human read.
* **Scope:** only the sections changed in `git diff HEAD -- paper_q/main.tex`. These are the abstract, Theorem B, the
  novelty paragraph (HATA-2), the §1.3 bullet, the constants table, Theorem 7.x and Table 2, §10.3 (Lemma M, its proof and
  remark), the proof of Theorem B and the remark after it, the Ti₂ bullet of §12, §13 (statement, axioms, commit,
  Table 6 rows, departures, build and replay) and the disclosure. The rest of the paper was read only where the
  changed text cites it: §2 (data, eq:newton, eq:Omega, Lemma 2.2, eq:gram), Lemma 4.1 (Leibniz), Lemma 9.2 (fdseq),
  Lemma 10.1 (10₁), Prop. 10.4 (nonvanishing, case B).
* **Read:** `pilot_ti2_q5/RESULT.md` and `referee/REFEREE_Q5.md`; Lean at cef469e:
  `TiQ/M/{Defs,Binom,Gram,BoundB,Trunc,BoundA,Final}.lean` (statements and the proofs of `boundA` and `bA_tail_V2`, plus
  the definitions `rP`, `cP`, `SM`, `n2M`, `two_SM_le`), `TiQ/Interface5.lean` (in full), `Cert/{DataQ5L200,Q5L200}.lean`;
  `FIDELITY_REFEREE_T5.md`; `scripts/axioms_t5.txt`; the end of `NOVELTY_CHECK.md`; the header of `REFEREE.md`.
* **Ran.** Scripts are in the session scratchpad. No `lake build` was run, and no repository file other than this one
  was written.
  1. `lemM.py` (python-flint, exact): an independent machine (Λ_X from Lemma 2.2 and eq:newton, Δ^Ti_h(X) by
     interpolation). For q ∈ {3,5,7,9,15} and h ≤ 16 it checked:
     - the Step 1 identity B(C_iC_j) = (AᵀOA)_ij;
     - the Step 2 closed form A_ni = (−1)ⁿC_{i−n}(x_n), against the Newton definition;
     - the Step 3 closed form of β_k;
     - bounds (A), (B), (C), the Step 4 error and |θ|₂.
     It also checked Lemma M's bound n₂ ≤ S_h − 2Σv₂(i!) against the exact −min_k v₂([X^k]Δ^Ti_h) at
     q ∈ {3,5} with h ≤ 32 (and q = 7, 9, 15 at smaller h).
  2. `potentials.py`: the Step 6 sum S_h for h ≤ 20000, the closed formula, and the 9h²/4 + 13 bound.
  3. `trop.py` (scipy optimal assignment): the tropical value of the Leibniz bound for N, h ≤ 48 (Remark after Lemma M).
  4. mpmath, 40 digits: the q = 5, q = 3 margins; the formal q = 5 margin from the bounds used in `margin_t5`.
  5. Python Fractions: Φ_Q from `DataQ5L200.lean` (λ, E_lo, 400 values S_k), and the parameters L, s, K, X, N and the
     table length.
  6. `python paper_q/check_lean_names.py cef469e`: 225 tokens, 0 problems. `git rev-parse cef469e`; the file count at
     cef469e; the axiom file at cef469e.
  7. A copy of main.tex and references.bib built in the scratchpad with `build.sh`. There are no undefined references
     and 13 overfull boxes; one of them is new (finding 9).

## Verdict: PASS WITH FIXES

There is no ERROR. The mathematics of Lemma M as written is correct: every step checks by hand, and every intermediate
inequality holds on exact data with nonnegative slack. The q = 5 margin and the certificate numbers recompute. The
Lean section is accurate, with one stale number. Two MAJOR findings need fixing before release:
* a false quantitative comparison in the §1.3 bullet;
* an inaccurate review-status claim in the disclosure.

Neither affects any proof.

## Findings

1. **MAJOR, l. 236–238 (§1.3 bullet).** The bullet says the anchored-basis entry bounds "cost ¼ log 2, which is
   ½ log 2 more than for χ₂(1/q)". As a statement about the prime-2 cost this is false. For χ₂(1/q) at odd q, Lemma 10
   costs (ν−2)/4·log 2, which is also ¼ log 2 at q = 3, 5 (ν = 3).
   - The ½ log 2 is the difference in the **total** arithmetic constant. For χ₂, the 2-part 2^ν of q²−1 is removed
     from c_odd and only (ν−2)/4 is paid back, a net −½ log 2. For Ti₂, the 2-part of q²+1 is 2, and that is removed
     and paid back exactly. Compare eq:alphaodd with eq:alphaTi, and the sentence after eq:alphaTi.
   - The old bullet ("so Ti₂(1/q) pays ½ log 2 more than χ₂(1/q)") was correct.
   - *Fix:* "for Ti₂ at odd q, ν = v₂(q²+1) = 1, so the 2-part of q²+1 saves only ¼ log 2 and Ti₂(1/q) pays ½ log 2
     more in total than χ₂(1/q) (entry bounds in the anchored basis cost ¼ log 2); a change to the binomial basis
     halves the cost of the prime 2 to ⅛ log 2 (Lemma M), which brings q = 5 within reach (q = 3 stays out)".

2. **MAJOR, l. 2010–2013 (disclosure).** The disclosure lists Lemma M among the written proofs that "were checked by
   the Lean kernel and by the whole-paper referee only". The whole-paper referee (`REFEREE.md`, 2026-11-12, commit
   7a2780c) predates Lemma M and never saw it.
   - Lemma M's written proof (the Lean route) has been checked only by the Lean kernel and by this changed-sections
     gate referee.
   - Its source proof (θ₂, Cauchy–Binet) had one gate referee (`REFEREE_Q5.md`).
   - *Fix:* take Lemma M out of that parenthesis and add a sentence such as: "Lemma M (added after the whole-paper
     review) follows the formal proof; as written it was checked by the Lean kernel and by one AI referee of the changed
     sections; its source proof was checked by one AI gate referee." The new ingredients listed earlier in that
     paragraph should also mention Lemma M.

3. **MINOR (stale number), l. 1802.** "It has 138 Lean files under Chi2Irrational/". At cef469e there are **148**
   (`git ls-tree -r cef469e Chi2Irrational | grep -c .lean`; 138 was the count at 7a2780c). The ten new files are
   TiQ/M/* (7), Interface5, DataQ5L200 and Q5L200. *Fix:* 148.

4. **MINOR, l. 1519–1520 and 1598 (Lemma M statement).** The statement uses n₂(h) for an undefined bound. Elsewhere
   the symbol is the true exponent: "Exact computations give n₂(h) ≈ h²/8" (l. 1515), the Remark (l. 1598), and §1.3
   "n₂ ≥ h² − h". *Fix:* define it in the statement, e.g. "Then n₂(h) := −min_k v₂([X^k]Δ^Ti_h) ≤ h²/8 + O(h log h)",
   or name the proved bound n_M(h) := S_h − 2Σ_{i<h}v₂(i!).

5. **MINOR (notation clashes in §10.3).** Several symbols are reused with different meanings:
   - θ is redefined as a rational number (l. 1528), although §1.4 says "elsewhere θ is the target number" and Lemma 2.2
     uses θ = Ti₂(1/q). Step 1 then mixes the two (Λ_X = A + XB, with E built from the new θ).
   - B is both the functional B(g) and the integer B = 16h+16; both appear in Steps 1 and 4.
   - A is both the functional (in E_ij) and the matrix A_ni.
   - N is the 3h×3h matrix, N′ = h−1 is set in Step 3, and in Step 5 (N/P)′ uses N′ for a derivative. These clash
     directly.
   - P is a polynomial (Step 5) and the integer ⌊h/4⌋ (Step 6).
   - Q is q² (Step 3) and −β (Step 6).
   - S is a polynomial and S_h is a sum.
   - Step 6 indexes E-rows by j.

   *Fix:* write θ̃ (or θ_B) for the rational θ, 𝔅 or B₀ for 16h+16, and n_E or similar for N. Rename the Step 6
   integers P, Q, P′ (e.g. a, c, a′) and the Step 3 N′ (e.g. K = h−1). Index E-rows by i.

6. **MINOR, l. 1530, 1595–1597, 1951–1953 ("the source").** "The source" is never identified for the reader. *Fix:*
   "our working notes" (the disclosure already uses this phrase), or cite the RESULT document.

7. **MINOR, l. 1951–1953 (departures).** "With the source's sharper bound (A) the two give the same bound". This is
   true of the **tropical value** of the Leibniz bound for N: recomputed for h ≤ 48, it equals
   2Σs₂(j) + max_m m(h+1−2m) exactly. It is not true of the potentials of Step 6, which with the sharper (A) (γ − 1)
   give the source's bound + 1 (h = 8, 16, 32, 48: 35/34, 101/100, 297/296, 557/556).
   - *Fix:* "with the source's sharper bound (A) the tropical value of this Leibniz bound equals the source's bound".
   - Also, this item records a difference between the paper and its source, not between Lean and the paper. It could
     say so ("The formal proof is Steps 1–6 exactly; they differ from the working notes in …").

8. **MINOR, l. 1513 (opening of §10.3).** "With Lemma 10₁ the margin at q = 5 is +0.043". That figure uses the
   ball-arithmetic certificate Φ ≤ −2.4516816. With the paper's own q = 5 certificate (Φ ≤ −2.44) it is +0.0547.
   *Fix:* add "(with the ball-arithmetic certificate of the Remark after the proof of Theorem B; +0.055 with
   Φ ≤ −2.44)". Alternatively, say only "is positive".

9. **MINOR (typesetting), l. 1527–1529.** The display defining 𝕄_B, f_k, θ overflows by 13.6 pt (new overfull box).
   *Fix:* split it into two lines.

10. **MINOR, l. 1039 and 1081.** The label "1/5² (finer)" is unexplained. At the q = 6 row "(finer)" means L = 800 as
    against L = 400, but there is no coarser q = 5 row. *Fix:* drop "(finer)", or explain it as "finer than the q = 5
    certificate of [Chi2Paper], Φ ≤ −2.385".

11. **MINOR, l. 1551 (Step 3).** "a combination of" should be "an integer combination of" (coefficients 2s+1 and s+1);
    integrality is what the valuation bound needs.

12. **MINOR, l. 1580–1582 (Step 5, tail).** The tail step says the numerator's derivative at an integer t has
    |·|₂ ≤ 2^{2h}, with no reason given. The only non-integral factor is g′(t). *Fix:* add "(the derivative bound
    just proved, with b = 0, applied to g(t+·))". This is the Lean `deriv_intval_bound` with d = 2h.

13. **MINOR, l. 1906 (Table 6).** `TiQ.M.fd_deriv_intval` is the integer-valued derivative bound used in Step 5, but
    the table files it under "Steps 1–2". *Fix:* move it to the "Steps 3–5" row.

14. **MINOR, l. 1777–1779 (§12).** The phrase "Neither is within reach of the 2-adic arithmetic" is unclear, and for
    q = 4 nothing in the text supports it: the old text's "for q = 3, 4 even ideal ingredients do not seem to suffice"
    was narrowed to q = 3. *Fix:* say "Improving the 2-adic bound cannot close either gap: …", or restore the q = 4
    statement with its reason.

15. **MINOR, l. 1990–1991.** "the two new certificates" now reads as if it were all of them. The q = 5 certificate is
    a third, covered by the next sentence. *Fix:* "the two certificates of Theorems B (q ≥ 6) and C".

## What I checked and recomputed

**Lemma M, step by step (by hand, then exact data):**
* *Notation.* μ(R) = 𝕄_B(R′) for deg R ≤ B (Δ^bR′ = 0 for b ≥ deg R). θ = (4 − 𝕄_B(f₀))/(4q) is the truncation of
  the source's θ₂ = 1/q − 𝕄(f₀)/(4q).
* *Step 1.* det C = Π1/i!, so Δ = (Πi!)²·det(Λ_X(C_iC_j)). Newton's formula on k < h. β_k and B(C_iC_j) = (AᵀOA)_ij:
  exact match for every (q, h) tested. Λ_X = E + (X−θ)AᵀOA. Block determinant: the lower-right 2h×2h block
  [[1, −(X−θ)O], [0, 1]] has determinant 1, and its Schur complement is E + (X−θ)AᵀOA. Correct.
* *Step 2.* Pascal at u = x_{k+1} gives Δ_kC_i(x_k) = −C_{i−1}(x_{k+1}), hence A_ni = (−1)ⁿC_{i−n}(x_n), and 0 for
  n > i. This matches the Newton definition exactly. Also v₂C_s(x_k) = −s − v₂(s!) ≥ −2s. Minimum slack of (C): 0.
* *Step 3.* D′(x_k) and β_k = (2q/N′!)C(N′,k)(2k+1)Q^k: exact. (2k+1)C(k,s) = (2s+1)C(k,s) + 2(s+1)C(k,s+1). Both
  binomial sums have v₂ ≥ N′−s, so v₂T_s ≥ 1−s. The product C(k,n)C(k,n′) is an integer combination of C(k,s) with
  s ≤ n+n′. Minimum slack of (B): 1 to 4.
* *Step 4.* Shift f_{k+1}(t) = f_k(t+1). Ω_{b−1} = (w⁻¹−1)Ω_b for b ≥ 2 and Ω₀ = (w⁻¹−1)Ω₁ − 1. Re-deriving gives
  𝕄_B(f_{k+1}) = w⁻¹𝕄_B(f_k) − f_k(1) + (w⁻¹−1)Ω_BΔ^Bf_k(0), which is the printed recursion
  (w⁻¹ = −q², −f_k(1) = 4/(2k+3)²).
  - D_{k+1} = −q²D_k + 4/(2k+3)², and D₀ = 𝕄_B(f₀).
  - The forcing has v₂ ≥ 1 − (B+1) + B + 2 + v₂(B!) ≥ 8h+10, so the claimed 2^{−(8h+8)} holds with room. Exact:
    min v₂(D_k − 𝕄_B(f_k)) = 17h + 16 or more (e.g. 272 at h = 16, against 136 required).
  - v₂(𝕄_B(f₀)) ≥ 1 termwise, and v₂(θ) = −1 in every case tested.
* *Step 5.*
  - Decomposition: E_ij = μ(R_g) + Σg(x_k)ω_kD_k.
  - Error terms: 2^{2i+2j+h−8h−8} ≤ 2^{i+j+2−h} because i+j ≤ 6h+10.
  - Partial fractions give 𝕄_B(F) with F = (gu/D)′; deg R_g ≤ h−1 ≤ B.
  - With D = 2^{−h}P(2u), PS = 1 − T^MV^M, and the polynomial part Σ2^{h+m}σ_m u^{m+1}g, the derivative bound
    |Δ^bG′(0)|₂ ≤ 2^{d−b} holds: C_r′(0) = (−1)^{r−1}/r, and 2^{v₂(r)} ≤ r ≤ 2^r.
  - Tail: 2^{h−M} ≤ 2^{i+j+1−h−b} needs M ≥ B + 2h − 2; M = B + 2h + 1 is enough. Lean's route
    (G·U^M with U = TV) is equivalent.
  - Minimum slack of (A): 1 everywhere tested. Lean's (A) is one weaker than the source's (slack 0 there), as the
    paper says.
* *Step 6.* Every block's entry inequality was checked against the row and column exponents:
  - E/E uses α + γ = 2 − h;
  - Aᵀ and −A use (2i+β) + (−2n−β);
  - the identity blocks use max(2n+β, n) − 2n − β ≥ 0;
  - the O block uses n + n′, with |θO|₂ ≤ 2·2^{n+n′−1}.

  Lemma 4.1 applies verbatim to a 3h×3h matrix over ℚ[X]. 2S_h equals the closed formula **exactly** for every
  h ≤ 2000 (it is the Lean `two_SM_le` with −4hQ = 4hβ). The formula is ≤ 9h²/4 + 13 for every h ≤ 20000; the excess
  over 9h²/4 is linear in h with negative slope in each residue class mod 4, and its maximum is +2 at h = 4. With
  2Σv₂(i!) ≥ h² − O(h log h) this gives n₂ ≤ h²/8 + O(h log h). For example, (bound − h²/8)/(h log₂h) = 1.04 at
  h = 1000.
* *Lemma M against the exact determinants, (q, h): exact n₂ ≤ bound.*

  | (q, h) | exact n₂ | bound |
  |---|---|---|
  | (5, 16) | 28 | 107 |
  | (5, 24) | 65 | 191 |
  | (5, 32) | 120 | 307 |
  | (3, 32) | 116 | 307 |
  | (9, 12) | 15 | 67 |

  There were no violations. The exact values match RESULT's 28, 65, 120.
* *Remark.* With bound (A) sharpened to 2^{i+j+1−h}, the tropical (optimal-assignment) value equals the source bound
  2Σs₂(j) + max_m m(h+1−2m) for every h ≤ 48 (e.g. 100 at h = 16, 556 at h = 48). With the paper's (A) it is larger by
  about h/4 (104, 568). "Weaker by O(h)" is correct.

**Margins and certificate:**
* q = 5: 133/60 + ¼log13 − ⅓log5 + ⅛log2 − 2.44 = −0.0319319… With the exact Φ_Q it is −0.0354836; with the Arb
  Φ = −2.4516816 it is −0.0436135 (the Remark's −0.0436). With Lemma 10₁ and the Arb Φ it is +0.04303 (the "+0.043").
* Formal margin: the bounds in `margin_t5` give −0.0192 (§13's −0.019).
* q = 3 with Lemma M (Arb Φ₃ = −2.0987404): +0.24073, matching "+0.241". The q = 4 figure +0.121 is unchanged and was
  not recomputed (it does not involve Lemma M).
* Certificate `DataQ5L200`: q = 5, L = 200, s = 2 (width 1/100), K = 115, X = 2 (400 cells), N = 2, |tab| = 1204,
  |S_k| = 400. Φ_Q = −E_lo + λ + (2/L)Σ(S_k−λ)₊ = −2.44355175557…, matching Table 2's −2.4435517….
  `phiQ_le : PhiQ ≤ −244/100` by `decide +kernel`.
* Proof of Theorem B: for q = 5 it uses Lemma M, the W = 1/25 certificate, Theorem 6.2 with |w|, and Prop. 10.4
  (stated for q ≥ 3). For q ≥ 6 it is unchanged.

**Consistency:**
* "q ≥ 6" for Theorem B: the remaining occurrences are l. 1038 (the q = 6 certificate), l. 1645 (the q ≥ 6 branch),
  and l. 1829 and 1911 (`theoremT`). All are correct. Abstract, Theorem B, novelty, constants table and §12 now say
  q ≥ 5, q = 5 or q ≤ 4 consistently.
* Novelty "5 ≤ q ≤ 2948": consistent with the DHK threshold 2949 and with the unchanged Hata caveat ("if that threshold
  is below q"). It matches the `NOVELTY_CHECK.md` addendum (q = 5 CLEAR, same caveat) and HATA_TODO row HATA-2.
* Lean:
  - cef469e = cef469ef846a2a3967d2d441e331254bd82898e2.
  - `TheoremT5` in `TiQ/Interface5.lean` reads exactly as displayed. `theoremT5` dispatches q = 5 to Lemma M with
    `cert_t5`, and q ≥ 6 to `theoremT`, as §13 says.
  - `scripts/axioms_t5.txt` at cef469e has 72 `depends on axioms` lines, all [propext, Classical.choice, Quot.sound],
    including theoremQ4, theoremT5 and theoremQ4num. It records 9196 jobs.
  - All 225 Lean tokens exist (name check).
  - The 461 s kernel time agrees with TRUST.md; it was not re-measured.
  - The departures item is honest: rational θ, block matrix, (A) one weaker, Lemma M formal only at q = 5.
  - The replay status is honest: the new modules are stated as not replayed.

**Style:** no bracket labels ([Proved] etc.) in main.tex. The lemma label "[Lemma M]" follows the house style
("[Lemma 10₁]").

## Author's response (2026-11-13)

All fifteen findings were applied to `main.tex`.

1. §1.3 bullet rewritten as proposed: the ½ log 2 is the total difference; the anchored entry bounds cost ¼ log 2;
   Lemma M halves the prime-2 cost to ⅛ log 2.
2. Disclosure: Lemma M taken out of the "whole-paper referee" parenthesis. A new sentence says it was added after the
   whole-paper review, follows the formal proof, and was checked by the Lean kernel and this changed-sections referee;
   its source proof had one gate referee. Lemma M is now listed among the new ingredients ("the case of Ti₂ including
   Lemma M").
3. 138 → 148 Lean files.
4. The lemma now defines n₂(h) := −min_k v₂([X^k]Δ^Ti_h). The opening paragraph no longer uses n₂ before the definition.
5. Notation in §10.3: θ̃ for the rational θ (with a sentence saying it is not the target); B₀ = 16h+16 and 𝕄 without
   subscript; matrices 𝒜, 𝒪, 𝒩 (the functionals A, B keep their names); K = h−1 in Step 3; Y for the polynomial S;
   (F₁/F₂)′ for the quotient derivative; Step 6 integers p, r, p′; E-rows indexed by i; bounds named by matrix
   ("the entries of E / 𝒪 / 𝒜") instead of (A)/(B)/(C).
6. "the source" → "our working notes" throughout §10.3 and the departures list.
7. Departures item rewritten: tropical value of the Leibniz bound equals the notes' bound; marked as a difference from the
   working notes, not from the Lean.
8. Opening of §10.3: "is positive (+0.055 with the paper's certificate Φ ≤ −2.44, +0.043 with the ball-arithmetic certificate)".
9. The 𝕄/f_k/θ̃ display is split in two; the 13.6 pt overfull box is gone (largest remaining overfull box 10.0 pt, l. 1393,
   pre-existing).
10. "(finer)" dropped from both q = 5 rows.
11. "an integer combination of … (with coefficients 2s+1 and s+1)".
12. Tail step: the factor u^{M+1}V(2u)^M has integer coefficients, g(t) ∈ ℤ, and |g′(t)|₂ ≤ 2^{i+j} ≤ 2^{2h} by the
    derivative bound with b = 0 applied to g(t+·).
13. `TiQ.M.fd_deriv_intval` moved to the Steps 3–5 row of the Lean table.
14. §12: "Improving the 2-adic bound cannot close either gap": at q = 3 removing the prime 2 altogether (⅛ log 2 ≈ 0.087)
    leaves +0.154; at q = 4 c(2) would have to fall far below the exact values, as for χ₂(1/4).
15. "the two certificates of Theorems B (q ≥ 6) and C".

Checks after the fixes: PDF 46 pages, 0 LaTeX errors, no undefined references; `check_lean_names.py cef469e`: 226 tokens,
0 problems; `scripts/axioms_t5.txt`: 72 declarations, all [propext, Classical.choice, Quot.sound].
