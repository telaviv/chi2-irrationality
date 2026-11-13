# Referee report: "Irrationality of χ₂(1/q), Ti₂(1/q) and χ₂(2/q)" (paper_q/main.tex)

* **Date:** 2026-11-12
* **Referee:** a fresh AI (Claude Opus) whole-paper referee, adversarial; no earlier involvement with this paper.
* **Read:** all of `paper_q/main.tex` (1895 lines), `references.bib` (entries cited in §1), `HATA_TODO.md`,
  `NOVELTY_CHECK.md`; for comparison `paper/main.tex` (published q = 3, 5 paper: disclosure, Lemma 5.3, §11.4);
  sources `pilot_chi2_2q/RESULT.md` and `NOVELTY.md`, `pilot_ti2q/RESULT.md` §0–9, `HATA.md`, `NOVELTY.md`, `LIT_NOTES.md`,
  `pilot_qeven/RESULT.md` §0–2, `pilot_q/RESULT.md` §5 (novelty) and `pilot_q/hata/RESULT.md` §0; the verdict lines of the four
  `FIDELITY_REFEREE_*.md`; Bahçıvan `paper.txt` (Thm 4.1, Thm 5.1, Cor. 6.2); `NOVELTY_SWEEP_2026-11-11.md` (Bahçıvan and arXiv
  coverage).
* **Lean read (commit 7a2780c; `git diff 7a2780c HEAD -- Chi2Irrational` is empty, and 7a2780c is on origin/main):**
  `Defs.lean`, `TiQ/Defs.lean`, `Q/Defs.lean`, `Q/Even/{Defs,Interface,Margin,TwoAdicSharp,CoreDet,Count,NuBound}.lean`,
  `Q/{TwoAdic,TwoAdicEven,Shift,Margin,Analytic}.lean`, `TiQ/{Free,TwoAdicNu1,Margin,Analytic}.lean`,
  `QZ/{Interface,NonVan}.lean`, `Analytic/Andreief.lean`, `Cert/Core.lean`, `Interval/Log.lean`, and all certificate data files.
* **Ran (scripts in the session scratchpad; no Lean build):**
  1. `python paper_q/check_lean_names.py`: 179 tokens, 0 problems.
  2. sympy: all six block determinants of Prop. 7.2 and §10.3 (χ₂ and Ti₂ matrices, entries exactly as printed in l. 1090–1095
     and l. 1511–1513) equal the printed closed forms (difference simplifies to 0); real roots of P_L, P_D.
  3. Lemma 10″: c(i,j) ≤ U_i + V_j for all i, j < h, ΣU + ΣV = 4hm − 3m² + 2m, and 3n₂ ≤ 4h² + 4h + 4, for every h < 400.
     0 violations.
  4. Lemma 3.4 (class count): cb(h,d) by the definition against hφ₁(d/h) (− 3/2 when d ≤ (2h−1)/3), all odd d < 4h,
     2 ≤ h < 200. 0 mismatches.
  5. mpmath (30 digits): every margin in §8–§11, Remark 9.x, Remark 10.x, Remark 11.6, §12, the DHK thresholds.
  6. Φ_ℚ = −E_lo + λ + (2/L)Σ(S_k − λ)₊, the mass Σc_j·s/L, the height cap and the dyadic denominators, recomputed exactly
     from the eight Lean data files.
  7. Leibniz/Andreief, the reflection and recombination formulas, Lemma 10_e's minimisation, the twist signs, the shift lemma,
     Lemma 10 / 10₁ entry bounds, Prop. 11.2, Lemma P Step 5 (types S, L, D), the Ti sign bookkeeping and the q′ transfer:
     checked by hand line by line.

## Verdict: **PASS WITH FIXES**

I found no mathematical error. Every lemma I checked is correct as written, and every number I recomputed agrees with the
paper and with the Lean data. Two passages are misleading (MAJOR): the novelty sentence of the abstract, and the claim that
"the written proof reaches q = 173". The rest are minor. All fixes are textual; no proof has to change.

## Findings

### 1. MAJOR: the abstract's novelty claim omits the Hata caveat, and the paper withholds its own estimate of Hata's threshold
* **Location:** l. 76–78 (HATA-3); also l. 164–170 (HATA-2) and l. 142–143 (HATA-1).
* **Problem:**
  - The abstract says that below DHK's range "they are new as far as we know". It gives no sign that Hata (JMPA 1990) may
    cover Theorems A and B down to an unknown threshold. The body states that caveat (l. 166–169), so the abstract claims more
    than the body.
  - The paper also says only "We do not know its threshold for the shift ½" (l. 142). The project's own sources say more:
    - `pilot_q/hata/RESULT.md` §0 reconstructs Hata's method (calibrated exactly to Hata's E₂ = 11.837…) and estimates
      q₀ ≈ 55 (exact denominators) to 85 (plain denominators) for χ₂(1/q) at Q = +q².
    - `pilot_q/RESULT.md` §5 concludes that Theorem A is "robustly new only at q = 3" and that "nothing we have read excludes
      Hata 1990 covering every q ≥ 4".
  - For Theorem B, Hata's thresholds are better at negative Q (Q ≤ −8 against Q ≥ 12), so the Q = −q² case is no better known.
  - So a reader who sees "new for 6 ≤ q ≤ 2948" in the abstract and the introduction gets a range that, by the authors' own
    estimate, may shrink to roughly q ≲ 85 or less.
* **Fix:**
  - (a) In the abstract, change the sentence to something like: "For large q the statements follow from the criteria of
    David, Hirata-Kohno and Kawashima; for Theorems A and B, a 1990 criterion of Hata that we could not consult may also apply
    from an unknown threshold on."
  - (b) In the Novelty paragraph or the HATA-1 bullet, add one sentence: a heuristic reconstruction of Hata's method (not a
    citation) suggests a threshold near q ≈ 55–85 for χ₂(1/q), and says nothing about Q = −q². So the genuinely new range of
    Theorems A and B may be much shorter than 6 ≤ q ≤ 2948.
  - (c) Theorem C is unaffected (numerator 4), and the paper already says so. Keep that.
  - Update HATA_TODO to record the new sentence.

### 2. MAJOR: "the written proof reaches q = 173" rests on computations that are neither in the paper nor in the formalisation
* **Location:** l. 114–115, Remark 11.6 (l. 1645–1651), l. 1835–1836; it is in tension with l. 243–246 and l. 1079–1080.
* **Problem:**
  - The q = 173 base needs a dual certificate at W = 4/173². Neither certificate is in the paper: Table 6.2 lists only
    4/175², and no data, code or verification method is given. Neither is in the formalisation. The sources show they are Arb
    computations (`q4_cert.py`, and the gate referee's `ref_cert.py`), with a [Computer-assisted: Arb] label.
  - Line 243–246 says the written proof is self-contained except for certificates "proved by evaluation in the Lean kernel".
    The 173 certificates are not covered by that sentence.
  - Line 1080 says the ball-arithmetic certificates are "used only in the remarks". Yet Remark 11.6 uses them to claim a proof.
* **Fix:** do one of the following.
  - (a) Downgrade the claim. For example: "Two independent ball-arithmetic computations (not included here and not
    formalised) give Φ ≤ −4.0005336 and Φ ≤ −4.0004556 at W = 4/173². With them the argument would reach q = 173."
    Drop "The written proof of Theorem C reaches q = 173" from l. 114 and l. 1835.
  - (b) Or archive the two certificate programs and their outputs (Arb endpoints) in the repository, cite them, and describe
    the verification method in one paragraph as a computer-assisted step. Then amend l. 243–246 and l. 1080 to match.

### 3. MINOR: a stale claim of a "different nonvanishing argument for Theorem C"
* **Location:** l. 239–241.
* **Problem:** The list of departures in §13.6 has no such item. In fact Prop. 11.3 is now exactly the Lean route:
  `QZ.lemmaP_norm` plus ℓ-adic continuity from q′ = q(ℓ^M+1)/2, as the `QZ/NonVan.lean` docstring confirms. The only
  difference is the explicit size bound on ℓ in `nonvan_z_proof`, which is immaterial.
* **Fix:** delete "and a different nonvanishing argument for Theorem C" (or replace it with "an explicit choice of ℓ").

### 4. MINOR: the replay placeholder, and the state of the replay
* **Location:** l. 1867 (`%%REPLAY%%`).
* **Problem:**
  - The placeholder is invisible in the PDF.
  - The current state is partial. `scripts/leanchecker_q.log` and `leanchecker_q4.log` are committed at 7a2780c.
    `scripts/leanchecker_qz_tiq.log` (untracked, in progress) lists the QZ/ and TiQ/ modules and explicitly *skips* the
    `decide +kernel` certificate modules (e.g. `QZ/CertQ175.lean`).
* **Fix:** replace the placeholder with an exact statement of what was replayed, including which certificate modules were
  skipped. If the replay is not finished, keep the published paper's wording ("we have not done so" for the remaining modules).

### 5. MINOR: the cited axiom output is not in the cited commit
* **Location:** l. 1733–1734.
* **Problem:**
  - `scripts/axioms_paper_q.txt` is untracked: it is not in 7a2780c and not public.
  - It has 61 entries, all `[propext, Classical.choice, Quot.sound]`, which matches the paper. But the file has no header
    naming the commit or the date; its only extra lines are the `time` output.
* **Fix:** commit the file with a header line (commit hash, date, command). Or cite the committed audit from 54a3d5b
  (61 entries) instead.

### 6. MINOR: the single-Li₂ citations are over-attributed, and Hata 1993 is cited secondhand without saying so
* **Location:** l. 146–149.
* **Problem:**
  - "[Hata 1993] proved Li₂(1/q) ∉ ℚ for some real rational points" is garbled. It is also secondhand: per `HATA.md` §3 the
    paper was blocked by a bot check, and the reported content is q ≥ 7 or q ≤ −5.
  - "Li₂(1/n) ∉ ℚ for every integer n ≠ 0 [Zhang, Liu, Prellberg, Tang]" holds only for Zhang. Per the bib entries:
    - Tang proves Li₂(1/2);
    - Prellberg proves Li₂ at −1/4, 1/5, −1/3;
    - Liu proves Li₂(±1/k) and Li₂(±p/k) above thresholds.
* **Fix:** write "for every integer n ≠ 0 [Zhang], after special cases [Tang (1/2), Prellberg, Liu]". For Hata 1993 write
  "reportedly for integers q ≥ 7 and q ≤ −5 (we could not consult it)".

### 7. MINOR: the abstract's "the three cases differ only at the prime 2 … and in the certificates" is inaccurate
* **Location:** l. 73–74.
* **Problem:** The three cases also differ in the nonvanishing step and in the odd primes:
  - the nonvanishing step needs the χ₄ sign analysis of Prop. 10.3 and the ℓ-adic transfer of Prop. 11.3;
  - for the odd primes of case (B), the coefficient twist of Prop. 4.9 is needed.
* **Fix:** "The three cases differ at the prime 2, where each needs its own lemma, in the certificates, and in the transfer
  of the nonvanishing lemma."

### 8. MINOR: numerical and heuristic statements are written as facts
* **Location:**
  - l. 1607–1608: "For an odd prime numerator the analogous price is exactly log of that prime per h²; the extra ⅓ log 2 …
    comes from the half-integer poles."
  - l. 1672–1676: "this machine cannot reach odd q below about 87".
* **Problem:**
  - The first claim comes from runs at numerator 3 (`pilot_chi2_2q/RESULT.md` §2.3, "measured"). Only the lower bound
    follows from the leading coefficient; "exactly" is numerical, and the attribution to the poles is heuristic.
  - The second claim assumes that 133/60 is sharp and uses C(W) numerics. §12's preamble says "numerical unless stated
    otherwise", but "cannot" reads as a theorem.
* **Fix:** add "numerically" or "we observed" to both. For l. 1675 write "numerically, with these ingredients, …".

### 9. MINOR: the e = 0 remark after Lemma 10_e
* **Location:** l. 1428–1429.
* **Problem:** "The same count with e = 0 … gives the cost ¼ log 2". But Step 5 absorbs the derivative loss h⌊log₂ M_f⌋
  into the price term e(2M_f − h)₊, which needs e ≥ 1. With e = 0 the count is uniform in M only after restricting to
  q-degrees ≤ deg cl_β f = O(h²), and then log M = O(log h).
* **Fix:** say this in half a sentence, or cite the source's e-free version (bound on cl_β f, a polynomial).

### 10. MINOR: the scope of "Every step of the written proof is formalised"
* **Location:** l. 1693.
* **Problem:** Not formalised: Prop. 11.2 (the floor), Remark 11.6 (q = 173), Remark 5.x (C(W)), and all of §12. None of these
  is needed for Theorems A–C.
* **Fix:** "Every step of the proofs of Theorems A–C is formalised …".

### 11. MINOR: "equals" should be "is at most"
* **Location:** l. 1450.
* **Problem:** The values −0.0097, −0.2422, −0.2101, −0.3539 are computed with the rounded Φ ≤ −2.56, … These are upper
  bounds for the margin (I recomputed −0.009741, −0.242244, −0.210073, −0.353931).
* **Fix:** write "is at most".

### 12. MINOR: the disclosure overstates what the gate referees saw
* **Location:** l. 1880–1883.
* **Problem:** The gate referees checked the working-note proofs. Several written proofs here follow different routes, mostly
  the Lean ones:
  - Lemma 10_e uses Andreief on the truncated slot matrix plus the derivative-row minor bound; the refereed note used a
    confluent Cauchy–Binet expansion;
  - Prop. 11.3 uses the q′-transfer; the refereed note read Lemma P at a rational ζ;
  - Lemma 10″ uses the simpler (U) bound;
  - Theorem 5.2 at w < 0 was only a paper sketch in `pilot_ti2q/RESULT.md` §4.

  These routes are kernel-checked in Lean, but as written proofs they have been read only by this whole-paper referee.
* **Fix:** add one clause, for example: "Several written proofs here follow the formal proofs rather than the refereed working
  notes (Lemma 10_e, Proposition 11.3, Lemma 10″); these were checked by the Lean kernel and by the whole-paper referee."

### 13. MINOR: the claim about DHK's proof should be hedged
* **Location:** l. 132–133.
* **Problem:** "Their proof as written supports only the weaker form …" asserts that a refereed theorem is stronger than its
  proof. It is based on one AI reading of the arXiv source (`REFEREE_CHI2_2Q.md` F6).
* **Fix:**
  - write "As far as we can see, the last step of their proof gives only …";
  - consider writing to the authors;
  - since Theorem C is for odd q, note that both thresholds are the first odd integers above 11,793.2 and 23,586.4
    (I recomputed both).

### 14. MINOR: notation overloads that cost the reader time
* **Location and problem:**
  - **ℓ:** reserved for primes (l. 256), but it is log(W/W′) in the shift lemma (l. 992–1011) and in §8's remark.
  - **ψ:** the ring homomorphism ℛ → ℚ[[q]] (l. 681, §8) and u log|u| − u (l. 789).
  - **μ:** the functional (l. 292) and the step density (l. 796).
  - **L:** the grid (Def. 5.1), ⌊log₂ h⌋ (l. 1244), and Hata's L(α,k;x).
  - **c:** c_k (pole data), c_r (block constants), c(e), c(i,j) (Lemma 10″), c_2.
  - **δ:** the far-node decay rate and the shift tolerance.
* **Fix:** rename the shift parameter (e.g. τ := log(W/W′)) and the power-series map (e.g. ψ_q or ι). The rest is
  optional.

### 15. MINOR: small points
* l. 1402: "M_f ≥ 1 is the largest node". If no node slot or only node 0 occurs, set Λ = 0. This is trivial but worth a word.
* Lemma 8.2(i) (l. 1271–1272): the bound k − 1 − ⌊log₂ k⌋ ≤ v₂(k!) is used for k = 0, where ⌊log₂ 0⌋ is undefined. Treat
  k = 0 separately (that term has v₂ ≥ 2m − 2).
* The build log has 12 overfull boxes.
* `NOVELTY_CHECK.md` (outside the paper) still contains `ARXIV_SECTION_PLACEHOLDER` and `ARXIV_DEPENDENT_VERDICTS`. The arXiv
  coverage claimed at l. 171 is supported by the 11-11 sweep, but the 11-12 file should be completed or should point to it.

## Checked and found correct (what I recomputed)

* **§2.**
  - Lemma 2.1, all three cases, including (−1)^t = (−1)^k χ₄(s) and S_k^Ti(y) = S_k(iy).
  - Ω_b and its y-form.
  - Lemma 2.2.
  - eq:lerch: all three Lerch identities, including the signs and the factors q/4, −q/4, q/8.
* **§3.** Prop. 3.1 and Thm. 3.2 (c = −(α+β)/2).
* **§4.**
  - Lemma 4.1/4.2 (Lemma 9) and Prop. 4.3: the residue valuation and β(a,b) ≥ ½(β(a,a)+β(b,b)).
  - Lemma 4.4, exact (script 4); ∫φ₁ = 17/12, and 4/5 + 17/12 = 133/60.
  - Thm. 4.5: the h ≥ 13 condition, and the 16/(5M) upper-sum error.
  - Prop. 4.9, the twist: the parity argument, and τ = (−1)^{m₁+j+(m₀+j)/2}.
  - The remark after (4.x): coefficients of cl⁻(f^Ti) and cl(f) agree up to the factor (−1)^{j+β} i^{j+n}, hence ±.
* **§5.**
  - β_h = ⌊h²/4⌋ (both parities).
  - Lemma 5.1.
  - Lemma 5.2:
    - ψ(Ω_b) coefficients and Newton's backward formula;
    - the reflection (5.x);
    - the recombination: I re-derived the pole part 4Σc′_k(S_k + q^{2k+1}χ₂(q)), so the result is −4(X+χ₂(q))Σc′_k q^{2k+1};
    - Σ_m q^{2m}/(2k+1−2m)² = S_k + q^{2k+1}χ₂(q);
    - the price map: injective, 2·image ≤ 3·price + 6;
    - Andreief (x-keys distinct, h! a unit).
  - Thm. 5.3:
    - the three cases p | q, p | Y, p ∤ qY (in case (C), v_p(q/2) = v_p(q));
    - d^odd;
    - the asymptotics.
* **§6, Theorem 6.2 (size).**
  - Lemma 6.3: the roots-of-unity identity needs h ≥ 2.
  - Lemma 6.4 (Pólya): the convexity of f, including Δ²f(0) = 0 and Δ²f(M−1) = log(M/(M−1)).
  - Lemma 6.5 (dual): the expansion in ν = n − m, and Σν² ≤ 8h.
  - Lemma 6.6 (i)–(iii): the deficit 2(1 − (d−1)log(d/(d−1))) ≤ 2/d, and log(d+1) ≤ log d + 1/d.
  - The near/far split and the (3S₀ + 3Σe^g)^h count.
  - The far bound: 1 − x log(1+1/x) ≤ 1/(x+1) ≤ log(1+1/x).
  - Remark: E(ρ − μ) ≤ 0 gives Φ ≥ C(W).
  - |φ′/φ| ≤ h for s ≥ 1, so the theorem sees only |w|.
* **Shift lemma.** (ii): the tail term decreases by (X − ½)ℓ. The new Φ′ ≤ Φ − ℓ/4 + ℓ/(4m), using
  Σ_{k′}(1 − k′/m)₊ = (m+1)/2. The mean ≥ ¼ remark. The Lean `Q.DualCert.shift` docstring is the same discretised
  construction.
* **Table 6.2.** Exact from the Lean data:
  - Φ_ℚ = −2.0783260, −3.0372394, −2.5635464, −2.7264892, −2.8528813, −2.9535971, −2.5671800, −4.0033242;
  - L, s, K, X, N and the log-table lengths (804, 1204, 2404, 1204, 1204, 1204, 4804, 4804) all match;
  - mass exactly 1, c_j ≤ 2, dyadic denominators ≤ 2¹⁶;
  - K·s ≤ N·L in every row;
  - log 2 is enclosed to width 2⁻¹⁰⁰ (`Interval/Log.lean`).
* **§7, Lemma P.**
  - The c_r values; D′(x_i) = ℓ² c_r⁻¹ U_i.
  - The off-diagonal valuations N_γ − 1 − δ_j and the block upper-triangular shape (D class last).
  - Step 5:
    - types S and L: Q[P](t) ≡ 0, ℓ² | P(x_i), so Q_i′(t) ≡ x_i U_i;
    - type D: 2t − x_c = ℓ(2y + c − ½), Q[P]′ = ℓ(2y + 5/2 − 2r), e_{rs}, and the sum w(e/(1−w) + 2w/(1−w)²).
  - K_ℓ is q-free.
  - Prop. 7.2: all three closed forms (sympy, script 2); positivity for Q ≥ 4 and negativity for Q ≤ −1.
* **§8.**
  - Lemma 8.2: Δ^k g(0) = (−2)^k k! H_k/P_k via g = −∂_s(1/(s+2l)); (i) and (ii).
  - Lemma 8.1 (general ν):
    - (L) via uP = 2^{−π}H(2u) and the Stirling numbers;
    - (U) via Δ^N[l T(l)](0) = NΔ^{N−1}[T(·+1)](0);
    - the assembly, with exponent 0 after the Σ(i+1) + Σj − h² cancellation;
    - Lean `Q.twoAdic_Delta` has exactly (ν−2)β_h + h(⌊log₂h⌋ + 6).
  - (8.x): ¼ log odd(q²−1) + (ν−2)/4 log 2 = ¼ log(q²−1) − ½ log 2.
  - Lemma 8.3 (10₀): the entry norms 2^{|i+j+1−h|}, and 2Σ|i − (h−1)/2| = ⌊h²/2⌋.
  - Lemma 8.4 (10_e):
    - Step 3: valuations of φ, φ′, 4ω_k;
    - Step 4: the ∂_U V argument (each factor is removed at most once, so c is injective); I compared it with Lean `CoreDet`;
    - Step 5: prices, including the (2M_f − h)₊ term; Cauchy–Schwarz counts; −2IP; derivative absorption for e ≥ 1;
    - f_e = (3e/2 + 4)x² − (2e+2)x + e, x* = (2e+2)/(3e+8), min = m_e, and −m_e = c(e) − e/3;
    - c(1), c(2), c(3);
    - the explicit Lean bound matches l. 1830 (`Rbd`, `n2E`).
  - Margins of §8.4: −0.023805, −0.025917 / −0.003662, −0.009741, −0.242244, −0.210073, −0.353931. q = 6 needs
    Φ < −2.550259.
* **§10.**
  - Lemma 10.1 (10₁): v₂(Ω_b) = −(b+1); (L) ≥ −π; (U) ≥ s₂(N) ≥ 1. The departure n₂ ≤ β_h + h(⌊log₂h⌋ + 2) matches
    `TiQ.twoAdic_DeltaT`.
  - (10.x) and the difference ½ log 2 + ¼ log((q²+1)/(q²−1)).
  - Cor. 10.2.
  - Prop. 10.3: I re-derived the S/L block factor χ₄(ℓ)(−1)^γ x̄_γ q̄^{2γ}, the D-block cancellation, and
    det M^Ti_S = −8q⁶(9q²−1)/(9(q²+1)). The Ti matrices are M at q̃ = iq, so the determinants are the printed forms at
    Q = −q² (sympy).
  - Margins: q = 6 gives −0.002948 (−0.006286 with −2.5704376; +0.1283 with c = ¼); q = 7 gives −0.097988 + δ; q = 8 gives
    −0.101686 + δ.
* **§11.**
  - Lemma 11.1 (10″):
    - v₂(Ω_b) = 2b (b ≥ 1) and 2 (b = 0);
    - the (U) bound −2i − 3N;
    - the potential inequality and the sum formula, exact for h < 400 (script 3);
    - ∫(u + v) = −7/18 + 31/18 = 4/3.
  - Prop. 11.2: [X^h]Δ_h = ±4^h ζ^{h²} Πx_k, with v₂ = h − h².
  - Prop. 11.3:
    - q′ is an integer and 2q′ ≡ q (mod ℓ^M);
    - 64P_L(q²/4) and 64P_D(q²/4) are integers;
    - the hypotheses of Lemma P at q′;
    - the continuity estimate via Lemma 9 with lev(ℓ) = 1;
    - K_ℓ is independent of M.
  - Margin: −0.001339 with 2 log q (−0.001372 exact), and 175¹⁰⁴ < 2⁷⁷⁵ gives < −0.0012. Remark 11.6: −0.000822 and −0.000744
    with exact log(q² − 4), matching the source.
* **§12.** χ₂(1/4): +0.0898, and the needed c(2) < −0.1771. Ti q = 3, 5: α_Ti = 2.426109, 2.494711. Ti q = 4: +0.1211.
  The q = 5 constant 0.18792. The rest match `pilot_ti2q` §6 and `pilot_chi2_2q` §4.
* **Introduction.**
  - DHK at ±q⁻²: q > 2948.30, so q ≥ 2949.
  - Bahçıvan described correctly: Thm 5.1 is density one for Ti_s, ℜLi_s, Li_s(−·), χ; Cor. 6.2 gives
    dim span{1, Ti₂(n), π ln n} = 3, which implies Ti₂(1/n) ∉ ℚ on that set; the method is DHK at 1/(qs) for large q
    (Thm 4.1), and the set is not explicit.
  - Ti₂(n) = Ti₂(1/n) + (π/2)log n, and ℜχ₂(n) = π²/4 − χ₂(1/n).
* **Hata marks.**
  - HATA-1/2/3 in main.tex match the three rows of HATA_TODO.md.
  - Hata 1990 is described honestly as unread and secondhand in the body.
  - No other sentence depends on Hata 1990. The Hata 1993 sentence is secondhand too; see finding 6.
* **§13 (Lean).**
  - Statements: `chi2Term`/`chi2`, `ti2Term`/`ti2`, `TheoremQ4`, `TheoremT` and `theoremQ4num` are verbatim as displayed;
    `TheoremQ` excludes {4, 6, 8, 10, 12}.
  - Files: 138 files; 61 axiom entries, all standard; no sorry, native_decide, implemented_by or axiom found by grep.
  - Versions: lean-toolchain v4.35.0, Mathlib v4.35.0; 9186 jobs (commit message of 54a3d5b); 10,697 s for the 175
    certificate.
  - I checked the meaning of 16 declarations against the paper's tables:
    - `Q.theoremQ4`, which branches on `newQ`;
    - `TiQ.theoremT`, `QZ.theoremQ4num`;
    - `Q.twoAdic_Delta`, `Q.twoAdic_even_proof` (Ebd ≤ (h² + 2h)/2), `Q.twoAdic_even_sharp_proof`,
      `Q.CoreDet.padicNorm_detR_le`, `Q.sum_cntL_ge`/`large_node`;
    - `TiQ.twoAdic_odd_t_proof`, `TiQ.parity_DeltaF`, `TiQ.map_DeltaFT`, `TiQ.coeff_clearET_twF`, `TiQ.abs_WT`;
    - `Q.DualCert.shift`, `factorial_smul_det_sum_rankOne`, `QZ.lemmaP_norm`/`nonvan_z_proof`.
  - The margins (`Q.margin_odd` with base 3 and 3⁵ < 2⁸; Q/Even/Margin −0.00904; TiQ/Margin −0.0025, −0.095, −0.10;
    QZ/Margin −0.00126) match §13.6.
* **Style.** The author is "Shawn Krisman"; no bracket labels; χ₂/Ti₂ notation is consistent. The AI disclosure is
  consistent with, and more detailed than, the published paper's. The PDF builds with no undefined references.

---

## Author's response and fixes applied (2026-11-12)

All findings were accepted; no proof changed.

| # | fix |
|---|---|
| 1 | Abstract (HATA-3) now says that for Theorems A and B a 1990 criterion of Hata, not consulted, applies from an unknown threshold. HATA-1 adds the heuristic reconstruction (q ≈ 55–85 for χ₂(1/q), an estimate, nothing for Q = −q²); HATA-2 says the genuinely new range of Theorem A may be much shorter (q ≲ 85 or less), with no estimate for B. HATA_TODO.md and README updated. |
| 2 | Option (a): "the written proof reaches q = 173" removed from §1.1 and §13.6. Remark 11.6 now says the two Arb computations are not included and not formalised, and that the paper does not claim q = 173. §13.6 lists Prop. 11.2, the remarks and §12 as not formalised. |
| 3 | Stale "different nonvanishing argument for Theorem C" removed from §1.4. |
| 4 | Replay paragraph filled in after the leanchecker run finished, naming the skipped certificate modules (see §13.7). |
| 5 | `scripts/axioms_paper_q.txt` now has a header (command, date, tree, worktree note) and is committed with the paper; §13.3 says it was added after 7a2780c. |
| 6 | Li₂ citations: Zhang for all n ≠ 0, "after special cases" Tang, Prellberg, Liu; Hata 1993 "reportedly … q ≥ 7 and q ≤ −5 (we could not consult this paper either)". |
| 7 | Abstract: the cases differ "at the prime 2, … in the certificates, and in how the nonvanishing lemma is transferred". |
| 8 | Numerator-3 statement marked as observed numerically, pole attribution as "presumably"; §12 "does not reach … numerically and assuming 133/60 is the true generic constant". |
| 9 | The e = 0 remark now says the count is applied to the polynomial cl_β f (q-degree O(h²)), and that it is not used. |
| 10 | §13.1: "Every step of the proofs of Theorems A–C is formalised". |
| 11 | "equals" → "is at most" for the four margins. |
| 12 | Disclosure: written proofs that follow the formal route (Lemma 10_e, Lemma 10″, Prop. 11.3, Thm. 6.2 at w < 0) were checked as written proofs only by the kernel and this referee. |
| 13 | DHK: "As far as we can see, the last step of their proof gives only …"; the odd-q remark (11,793.2 and 23,586.4) added. Writing to the authors is left to the owner. |
| 14 | Shift parameter renamed τ; the power-series homomorphism renamed ψ_q (the analytic ψ keeps its name). Other overloads left as they are. |
| 15 | Λ = 0, M_f = 1 when no comparison node exists; k = 0 treated separately in Lemma 8.2(i); NOVELTY_CHECK.md completed by its search agent (arXiv section). Overfull boxes: the large ones were fixed before the referee; the remaining ones are under 12 pt. |
