# Novelty check for paper_q, 2026-11-12

This updates `handoff/lit/NOVELTY_SWEEP_2026-11-11.md` (the 11-11 sweep) for the three theorems of `paper_q`:

* **A.** χ₂(1/q) ∉ ℚ for every integer q ≥ 3, q ≠ 4.
* **B.** Ti₂(1/q) ∉ ℚ for every integer q ≥ 6.
* **C.** χ₂(2/q) ∉ ℚ for every odd q ≥ 175.

Novelty ranges, given DHK, Acta Arith. 206 (2022) Thm 2.1 (already cited):
* A: 3 ≤ q < 2949;
* B: 6 ≤ q ≤ 2948;
* C: 175 ≤ q < 11,795, using DHK's printed criterion.

Everything fetched was treated as data. No downloaded code was run, and no personal name was used as a query. The only names
queried were those of cited authors (Hata; David, Hirata-Kohno, Kawashima). The author's own repositories
(telaviv/chi2-irrationality, telaviv/chi2-quadratic-units-irrationality) did turn up, and are ignored as prior art. Raw
outputs stay in the session scratchpad and are not kept.

## 0. Coverage

| source | tool | queries | notes |
|---|---|---|---|
| GitHub repositories | `gh search repos` (authenticated) | 25 queries × 2 match modes (name/description, README) = 50 calls, plus 10 calls restricted to `created:>2026-11-08` | no date filter on the 50; we checked dates by hand |
| GitHub code | `gh search code` (authenticated, legacy index, default branches) | 24 queries (.lean, .md, .tex) | the index is sparse for new repositories (see the 11-11 sweep, §A, caveat) |
| GitHub, targeted | `gh api` | READMEs of 9 candidate repositories; commit logs and repository lists of the Li₂ authors (ryzfsu, siqiliu-tsinghua, dtq1997); listing of the openai/math preprint folders | |
| Zenodo | REST API `records?q=…&sort=mostrecent&size=25` (Python urllib) | 32 queries; record and version API for 4 records | |
| arXiv | export API `search_query=…&sortBy=submittedDate` | 19 queries | see §3 for the rate-limit history |
| Palomar registry | `data.palomar-registry.org/recent.json` | 200 entries, from 2026-08-19 to 2026-11-13 | keyword filter |

**Not covered:** MathSciNet, zbMATH (except the Hata 1990 record already in references.bib), Google Scholar,
Semantic Scholar citation lists of Hata 1990 and DHK 2022, Lean Zulip, MathOverflow. **Hata, J. Math. Pures Appl. 69
(1990) is still unread** (see `HATA_TODO.md`); no source found today states its threshold for the shift ½.

## 1. GitHub

### 1a. Repository search (2026-11-12)

The count gives hits for name/description, then for README (`--match readme`). 100 means "at least 100".

| query | hits (name/desc; README) | relevant items | verdict |
|---|---|---|---|
| "Legendre chi" | 0; 2 | ours only | none |
| "legendre chi" irrational | 0; 1 | ours only | none |
| chi2 irrational | 2; 9 | ours; the rest are statistics (χ² tests) | none |
| chi2 irrationality | 2; 9 | same | none |
| "inverse tangent integral" | 0; 5 | randogelist/Catalans-Constant (2026-10-25): G = Ti₂(1), conditional, "unconditional irrationality is not claimed" | none |
| Ti2 irrational | 0; 2 | daandobber/krabton ("TI2" synthesizer); ours | none |
| Ti2 irrationality | 0; 2 | same | none |
| Lerch irrational | 0; 4 | nothing on Lerch irrationality | none |
| Lerch irrationality | 0; 4 | same | none |
| dilogarithm irrational | 6; 13 | ryzfsu/li2-* (Li₂ at 1/2, 1/3, 1/4, −1/2, 1/n); siqiliu-tsinghua/Li2Rational; dtq1997/li2-half-irrationality: all already cited or known | known |
| dilogarithm irrationality | 6; 13 | same | known |
| dilogarithm Lean | 1; 17 | karlesmarin/formalizations (dilogarithm identities, Rogers five-term; no irrationality); yuanzhu-lab/LeanPolyLog (16 polylog integral identities; no irrationality) | none |
| Li2 irrational | 7; 7 | the Li₂ repositories above | known |
| Li2 irrationality | 7; 7 | same | known |
| polylogarithm irrational | 1; 14 | ryzfsu/li3-* (trilogarithm); no χ₂/Ti₂ | none |
| polylogarithm irrationality | 1; 14 | same | none |
| arctan dilogarithm | 0; 6 | none on irrationality | none |
| polylogarithm "linear independence" | 0; 4 | none relevant | none |
| Hurwitz-Lerch | 2; 15 | bjbraams/lean-DLMF (definitions); none on irrationality | none |
| "Legendre chi function" | 0; 2 | ours | none |
| "Lerch transcendent" | 2; error | none relevant | none |
| chi_2 irrational | 2; 9 | jonhanke/elementary-number-theory-lean (2026-11-09): Dirichlet L-values L(1−k,χ), L(k,χ) by Gauss sums; matched on "χ"; no χ₂ | none |
| dilogarithm | 15; 96 | long-mathematics/quantum-polylogarithms-finite-dilogarithms (2026-10-01; quantum dilogarithms); izaidi/rm-reciprocity (quantum dilogarithm, 2026-10-06); no irrationality of χ₂/Ti₂ | none |
| polylogarithm Lean | 3; 23 | LeanPolyLog; SampLib; none relevant | none |
| irrationality Lean | 49; 100 | the odd-zeta, β, ζ₂, log, Catalan, π-measure repositories already in the 11-11 sweep; ryzfsu/small-height-lacunary-irrationality-exponent (2026-11-08; lacunary series) | none |

**Created after 2026-11-08** (`created:>2026-11-08`, both match modes): irrational, irrationality, dilogarithm,
polylogarithm, Lean. Hits: 4 and 43 for irrational, 1 and 43 for irrationality, 0 and 0 for dilogarithm, 1 and 2 for
polylogarithm, about 50 and 50 for Lean. None concerns χ₂, Ti₂, Li₂ or Lerch values. The nearest are
DiegoMarquesMath/Erdos-Mahler and Alex-lop/erdos-197-kronecker, which are unrelated.

**Li₂ authors, rechecked (gh api).**
* ryzfsu (R. Zhang): no new Li₂/χ₂ repository since 2026-10-15. The newer repositories (10-24 to 11-08) are on Goldbach,
  abc, equal radicals and lacunary series. The last commits to li2-integer-reciprocals-irrationality are 11-03
  (licence) and 11-05 ("Record comparator pass"). The theorem is unchanged: `li2_inv_irrational (n : ℤ) (hn : n ≠ 0)`.
* siqiliu-tsinghua: Li2Rational (2026-09-29) is unchanged; the later repositories are unrelated.
* dtq1997: nothing after li2-half-irrationality (09-28) and zeta2-zeta3-linear-independence (09-30).

### 1b. Code search (2026-11-12)

| ext | query | hits | relevant items | verdict |
|---|---|---|---|---|
| lean | chi2 Irrational | 12 | the-omega-institute/automath, nickgou-nuke/info-geometry-lean (`Omega/Zeta.lean` etc.; χ² unrelated) | none |
| lean | ti2 Irrational | 1 | siddhartha-gadgil/PlasmaLean (plasma physics) | none |
| lean | Ti2 Irrational | 1 | same (the first attempt was a network error; retried) | none |
| lean | inverseTangentIntegral | 0 | — | none |
| lean | legendreChi | 0 | — | none |
| lean | legendre_chi | 0 | — | none |
| lean | "Legendre chi" | 0 | — | none |
| lean | "χ₂" Irrational | 9 | AxiomMath/CFSG, AxiomMath/Stacks, TauCeti, … (χ₂ as a character name) | none |
| lean | "Ti₂" Irrational | 0 | — | none |
| lean | chi_two Irrational | 2 | AxiomMath/CFSG, FractalDevTeam/Principia-Fractalis | none |
| lean | Lerch Irrational | 21 | openai/math `lean/OAI.lean` (index file), lean-DLMF, SymLean, … | none |
| lean | dilog Irrational | 36 | marozols/SIC-existence (35), lean-DLMF | none |
| lean | Li2 Irrational | 29 | LeanPool `Zeta32/*` (Tang's 1, ζ(2), ζ(3)), automath | none (known) |
| lean | arctan Irrational "(2 * n + 1) ^ 2" | 7 | gamayos/finite-ring-space `Epi.lean` | none |
| lean | "inverse tangent integral" | 0 | — | none |
| md | "Legendre chi" irrational | 2 | tamnd/wikipedia-math (Wikipedia dump), roberthparry/MARS (CAS docs) | none |
| md | "inverse tangent integral" irrational | 7 | tamnd/wikipedia-math (6), alkahest-cas (CAS docs) | none |
| md | "Ti_2" irrational | 33 | noise (case law, textbooks, wiki dumps) | none |
| md | "chi_2" irrational dilogarithm | 0 | — | none |
| tex | "Legendre chi" irrational | 0 | — | none |
| tex | "inverse tangent integral" irrational | 2 | AlexenderSokolov/cross-theory-formal-database, source 206539 = N. Bhandari, "Positive rational series for reciprocal powers of Catalan's constant and Dirichlet beta values" (no irrationality claim for G); VladimirReshetnikov/ProveIt `Analysis/Polylogarithms/docs/reports/report-1.tex` (Ti₃ and Li₃((1+i)/2) closed forms) | none |
| tex | "\chi_2" irrational | 53 | ProveIt polylog manuscript (joint-coefficient asymptotics; χ₁−χ₂ are local symbols), openai/math (Margulis–Platonov palettes), arXiv-source mirrors (unrelated) | none |
| tex | Lerch irrational "linear forms" | 6 | none relevant | none |
| tex | "Ti_2" irrational | 4 | ProveIt `05-gamma.tex` (Ti₂ on the imaginary line, Gauss multiplication; no irrationality claim); cross-theory sources 206539, 210066 (GR), 183203 (Floquet) | none |

We fetched the ProveIt and cross-theory files and grepped them (no code run). None states an irrationality result for χ₂
or Ti₂ at any argument.

### 1c. Other GitHub checks

* openai/math: 751 preprint folders; the last commit is 2026-10-30. The only special-value folders are Catalan
  (09-24) and the irrationality exponent of π (09-24). Nothing on χ₂, Ti₂, Li₂ or Lerch.
* Palomar registry `recent.json`: 200 entries (08-19 to 11-13). Keyword hits: Siegel's L(1,χ) (11-12), lacunary
  series (11-10), a hyperspace result, Padovan. None relevant.

## 2. Zenodo (2026-11-12)

Unquoted multi-word queries match as OR on Zenodo (e.g. `chi2 irrationality` returned 1997 noise hits), so the queries
were re-run with quoted phrases and AND. Both runs are listed.

| query | hits | relevant items (title, author, created, id) | verdict |
|---|---|---|---|
| "Legendre chi" | 1 | P. Emmerson, "Swapping Two Operations: the double series 1/(n²−l²) …", 2026-10-08, 23182952. Uses χ₂ for a summation limit; no irrationality claim | none |
| "Legendre's chi" | 1 | **Bahçıvan, "Irrationality of ℜLiₛ, Tiₛ, and Related Functions at Almost All Positive Integers", 2026-11-08, 24047688** (re-found) | known; no overlap (§5) |
| "Legendre chi function" | 1 | Emmerson (above) | none |
| "Legendre" AND "chi function" | 1 | Emmerson (above) | none |
| "inverse tangent integral" | 4 | T. Krause, 24115988 (11-10; spanning trees and real quadratic fields) and 23805527 (10-30; Catalan, L(2,χ₋₃), lattice entropy); Y_Lily, 23418298 (closed form of an integral); Na, 22888210. No irrationality claims for Ti₂(1/q) | none |
| "inverse tangent integral" AND irrational* | 0 | — | none |
| "inverse tangent" AND irrational* | 0 | — | none |
| "arctangent integral" | 1 | Z. Ahmed, "A Golden Arctangent Integral", 2026-09-29, 23045013 (closed form) | none |
| "chi_2" AND irrational* | 8 | noise (physics, health) | none |
| "Ti_2" AND irrational* | 0 | — | none |
| "χ₂" | 1231 | noise (χ² statistics); nothing mathematical after 11-08 | none |
| "Ti₂" | 14316 | noise (titanium) | none |
| "Ti_s" | 601 | noise | none |
| "chi_2(1/3)" | 0 | — | none |
| "Li_2(1/q)" | 0 | — | none |
| dilogarithm AND irrationality | 10 | Zhang: Li₂(1/4) (09-13, 22737651; 10-08, 23247747), Li₂(−1/2) (23247749), Li₂(1/3) (23247755), Li₂(1/2) (23329843), Li₂(1/n) v2 (10-19, 23482367); Tan–Zhang, "Uniform cubic bounds for irrational values of the dilogarithm" (10-08, 23247332 = arXiv:2611.01066); **Anonymous, "Legendre-square determinants for dilogarithmic values", 2026-09-28, 23021891** (new to our notes, see below) | known / see below |
| dilogarithm AND irrational | 10 | same Zhang and Tan–Zhang records | known |
| Li_2 AND irrationality | 3 | noise | none |
| Lerch AND irrationality | 7 | S. Liu, Lerch-transcendent series papers (Jan–Mar 2026; series representations, no irrationality theorem at 1/q) | none |
| Lerch AND irrational | 7 | same, plus H.-J. Lim (10-23, noise) | none |
| "Lerch function" AND irrational* | 0 | — | none |
| polylogarithm AND "linear independence" | 0 | (the unquoted run: 145 hits, noise: Hylleraas integrals, cotangent-polylog integrals) | none |
| polylogarithm AND irrationality | 2 | Zhang, Li₃(1/n) for large n (10-13, 23329358); Krause (blackbody constants) | none |
| polylogarithms AND "linear forms" | 0 | — | none |
| "generalized polylogarithm" AND irrational* | 0 | — | none |
| arctan AND dilogarithm AND irrational* | 0 | — | none |
| "Hata" AND dilogarithm | 4 | Zhang records (cite Hata 1993) | known |
| "David" AND "Hirata-Kohno" AND Kawashima | 1 | Bahçıvan 24047688 | known |
| title:irrationality | 158 | newest math items: Kilani (2-adic ζ, 10-10; ζ₃(5), 10-07), Zhang Li₂(1/4) | none |
| title:irrational | 261 | Tan–Zhang; Kilani ζ₂(7); nothing after 11-03 in mathematics | none |
| dilogarithm AND Lean | 4 | C. Marín Muñoz (dilogarithm identities, quantum speed limits; 10-26, 23671607); Abel's five-term relation (06-13) | none |
| polylogarithm AND "linear independence" AND Lean | 0 | — | none |

**Zenodo records created after 2026-11-08 with any bearing:** none. Bahçıvan (11-08) is the newest relevant record.

**Version checks (records API):**
* Bahçıvan, concept 24047687: one version only (24047688, v1.0, 2026-11-08). No update.
* Zhang, concept 23296411: v1 = 23296412 (10-11), v2 = 23482367 (10-19, with Lean archive); latest is v2, metadata
  last updated 11-03. Abstract: "Li_2(1/n) is irrational for every nonzero integer n."

**New to our notes: Zenodo 23021891** (Anonymous, "Legendre-square determinants for dilogarithmic values", 2026-09-28,
v1.3).
* Claim: 1, Li₂(1/d), Li₂(−1/(d−1)) are linearly independent over ℚ for every integer d ≥ 3.
* Status: AI-produced (OpenAI Codex, with "user-supplied Anthropic Claude notes"); not refereed; no Lean; "no priority
  claim is made"; it does not prove Li₂(1/2) ∉ ℚ.
* Bearing: none on A–C. By Landen, Li₂(1/d) + Li₂(−1/(d−1)) = −½ log²(1 − 1/d), so this pair is not the pair
  Li₂(±1/q) whose difference is 2χ₂(1/q). It is one more single-Li₂ result (Li₂(1/d) ∉ ℚ for d ≥ 3), subsumed by
  Zhang's Li₂(1/n).

## 3. arXiv (2026-11-12)

The API rate-limited us hard today (HTTP 429/503). We ran the 19 queries in three passes, with pauses of 3.5 s, 25 s and
90 s between calls. Two queries never returned: `abs:Lerch AND abs:irrational` and `all:"inverse tangent integral"`.
They are covered in part by `abs:Lerch AND abs:irrationality` and `abs:"inverse tangent integral"`. The index reaches
November 2026: the 11-11 sweep saw arXiv:2611.11404, dated 8 Nov.

"New" means submitted on or after 2026-10-01.

| query | hits | relevant items (title, author, submitted, id) | verdict |
|---|---|---|---|
| abs:"Legendre chi" | 7 | Greenwell 2608.06591 (random triangles); González Layja 2603.21079; Dattoli–Ricci 2603.12164 (Le Roy, Lerch and Legendre chi functions, integral transforms); Kobayashi 2021; Schmidt 2016; Cvijović 2009 (×2). All are representations or evaluations; none proves irrationality. Nothing new | none |
| all:"Legendre chi" | 7 | same | none |
| abs:"inverse tangent integral" | 5 | Vlachopulos 2605.01830 (generalised Ti and Catalan); González Layja 2603.21079, 2601.20027; Batır–Dasireddy 2510.00870; Nicholson 2404.10805. All are evaluations; nothing new | none |
| all:"inverse tangent integral" | — | failed (429/503, three passes) | not run |
| abs:"inverse tangent" AND abs:irrational | 0 | — | none |
| abs:arctangent AND abs:irrationality | 0 | — | none |
| abs:Lerch AND abs:irrational | — | failed (429/503, three passes) | not run |
| abs:Lerch AND abs:irrationality | 2 | Straub 1407.5119; Bel 0705.1430 (p-adic Hurwitz) | none |
| abs:"Lerch function" AND abs:independence | 4 | DHK 1912.03811, 2010.09167, 2202.13931 (cited); Bel 2007 | known |
| abs:dilogarithm AND abs:irrational | 5 | **Tan–Zhang 2611.01066 (31 Oct; new, already known and cited)**; Radchenko–Wheeler 2609.21892 (finite quantum dilogarithms); Radchenko–Zagier 2012.15805; two unrelated | known |
| abs:dilogarithm AND abs:irrationality | 1 | Tan–Zhang 2611.01066 | known |
| abs:dilogarithms AND abs:irrationality | 1 | Tan–Zhang 2611.01066 | known |
| abs:polylogarithm AND abs:"linear independence" | 13 | **Mistiaen 2610.09774 (7 Oct; new; already in our notes, `schanuel/four_exp/strong4/pilot_U/novelty/NOVELTY.md` (g))**; Kawashima 2605.17756 (May; in our notes); Kawashima 2511.10057; DHK ×3; Fischler 2109.10136; Fischler–Rivoal 1701.09051; positive-characteristic papers | known |
| abs:polylogarithms AND abs:"linear independence" | 13 | same | known |
| abs:"generalized polylogarithm" AND abs:irrational | 1 | Kniehl et al. 2009 (QED) | none |
| abs:"generalized polylogarithms" AND abs:"linear independence" | 1 | DHK 2202.13931 (cited) | known |
| abs:polylogarithms AND abs:"linear forms" AND abs:irrational | 0 | — | none |
| abs:"Catalan" AND abs:dilogarithm AND abs:irrational | 0 | — | none |
| abs:"Hirata-Kohno" | 2 | Binyamini–Salant 2609.24148 (zero estimates; name in abstract); Tengely 2007 | none |
| abs:"Pade approximants" AND abs:polylogarithm | 0 | — | none |

**The two Oct–Nov 2026 items:**
* **Tan–Zhang, arXiv:2611.01066 (= Zenodo 23247332):** single Li₂ values, already cited.
* **Mistiaen, arXiv:2610.09774 (7 Oct), "Linear independence of values of polylogarithms with periodic coefficients,
  outside the disk of convergence".**
  * χ₂ (coefficients periodic mod 2) and Ti₂ (mod 4) are polylogarithms with periodic coefficients, so this is the
    closest new paper in kind.
  * Per our earlier read of the abstract and §1, its results are lower bounds ≫ s/log s for
    dim Span(L(f, i, z₀) : i ≤ s), asymptotic in the weight s. They say nothing at weight 2 or at a single value.
  * Not refereed; human author; no Lean. **No overlap.** Optional related-work citation.

## 4. Verdicts

No item found today states irrationality of χ₂(1/q), Ti₂(1/q) or χ₂(2/q) for any explicit q. Nothing found
supersedes DHK's ranges. The only open point is the one already recorded (`HATA_TODO.md`, the `% HATA-n` comments in
main.tex): Hata 1990 is unread. These are one-point Lerch values with shift ½:
* χ₂(1/q) involves Φ(1/q², 2, ½);
* Ti₂(1/q) involves Φ(−1/q², 2, ½), and the secondhand description says Q < 0 is allowed;
* χ₂(2/q) involves Φ(4/q², 2, ½).

So a small threshold in Hata 1990 could cover part of each range. Today's searches found no secondary source that quotes
that threshold.

* **A (χ₂(1/q), q ≥ 3, q ≠ 4): CLEAR** for 3 ≤ q < 2949 against GitHub (repositories and code), Zenodo, arXiv and
  Palomar as of 2026-11-12. **NEEDS READ** (standing, unchanged): Hata 1990, shift ½, at 1/q².
* **B (Ti₂(1/q), q ≥ 6): CLEAR** for 6 ≤ q ≤ 2948 on the same sources. Bahçıvan covers Ti₂(n) at integers on a
  density-one set, a different number with no explicit range. **NEEDS READ** (standing): Hata 1990 at −1/q².
* **C (χ₂(2/q), odd q ≥ 175): CLEAR** for 175 ≤ q < 11,795 on the same sources. **NEEDS READ** (standing): Hata 1990
  at 4/q², if his theorem allows non-reciprocal rational points.

Not verified here: whether DHK's printed criterion can be sharpened by hand below 2949 or 11,795. This is a statement
about DHK, not a search question; the paper already discusses it.

## 5. Bahçıvan and Zhang, re-found

* **Bahçıvan, Zenodo 24047688 (2026-11-08): re-found** (Zenodo "Legendre's chi"; DHK names). Still v1.0, with no
  later version and no other record by the same method. Its abstract confirms the scope:
  * "F(n) is irrational for almost all positive integers n", for F = Ti_s, Li_s(−x), ℜLi_s, Legendre's χ at integer
    arguments, via DHK at small rational points and reciprocity;
  * no explicit threshold. Ti₂(n) and ℜχ₂(n) are different numbers from Ti₂(1/q) and χ₂(1/q), and the density-one
    statement says nothing about any single small q.
  * No Lean; not refereed. It is not superseded.
* **Zhang, Zenodo 23296411 (concept; v2 = 23482367, 2026-10-19): re-found** (Zenodo dilogarithm queries; GitHub
  ryzfsu/li2-integer-reciprocals-irrationality).
  * Li₂(1/n) ∉ ℚ for all n ≠ 0; Lean, standard axioms, comparator pass recorded 11-05; not refereed.
  * No newer version, and no χ₂ or Ti₂ follow-up by the same author on GitHub or Zenodo.
  * It does not imply A–C: χ₂(1/q) = ½(Li₂(1/q) − Li₂(−1/q)) needs the joint independence of 1, Li₂(1/q), Li₂(−1/q),
    or at least that the difference is irrational.
* **Nothing newer supersedes either.** The only new-to-us related item is Zenodo 23021891 (09-28, §2), which is older
  than both and weaker than Zhang.

## Addendum 2026-11-13: Theorem B at q = 5 (Ti₂(1/5) ∉ ℚ)

Theorem B now covers q ≥ 5 (Lemma M, `Chi2Irr.TiQ.theoremT5`). A quick check for the new value, on top of the q ≥ 6 sweep
above:
* GitHub (gh CLI, 2026-11-13): repository searches `"inverse tangent integral" irrational`, `Ti2 irrational 1/5`,
  `"Ti_2(1/5)"`, `arctan dilogarithm irrational`: 0 hits each. Code searches `"ti2" Irrational lean`, `"Ti₂(1/5)"`,
  `"inverse tangent integral" irrational`: 0 hits; `ti2Term`: two unrelated hits. Caveat: the code index does not yet
  contain our own recent files (control `theoremQ4num`: 0 hits), so code search may miss very recent repositories.
* Zenodo (API, most recent): `"inverse tangent integral"`, `"Ti_2" irrational`, `arctangent dilogarithm irrationality`:
  no irrationality result for Ti₂ at any point (hits are identities, closed forms, unrelated topics).
* arXiv (API): `all:"inverse tangent integral"`: newest is Vlachopulos 2605.01830 (identities, already in our notes);
  `irrationality AND "inverse tangent"`: 0 hits.
* DHK 2022 Thm 2.1 needs q ≥ 2949; Bahçıvan's density-one result decides no individual q. Hata 1990 is still unread
  (HATA_TODO.md); its threshold at Q = −q² would have to be ≤ 25 to cover q = 5.

Verdict for q = 5: **CLEAR** (no prior or concurrent result found), with the same Hata caveat as for 6 ≤ q ≤ 2948.
