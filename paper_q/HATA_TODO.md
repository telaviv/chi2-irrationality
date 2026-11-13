# HATA_TODO: what to change if Hata 1990 is read

Source not consulted: M. Hata, "On the linear independence of the values of polylogarithmic functions",
J. Math. Pures Appl. (9) 69 (1990), no. 2, 133–173, MR1067449, Zbl 0712.11040 (bib key `Hata1990`).

Everything the paper says about it is secondhand: F. Beukers' zbMATH review, and citations in DHK (arXiv:1912.03811,
arXiv:2202.13931). Secondhand content: linear independence measures for 1 and L(α_j, k_j; 1/Q), rational shifts α_j,
integers |Q| > Q₀ with explicit Q₀; negative Q allowed; stated application Li₂(1/Q) ∉ ℚ for Q ≥ 12 or Q ≤ −8.

What to compute from the paper: Hata's threshold Q₀ for the shift α = ½, depth k ≤ 2 (the system 1, L(½,1;x), L(½,2;x)
at x = 1/Q), at **Q = q² (χ₂(1/q)) and at Q = −q² (Ti₂(1/q))**, and whether the theorem allows a point α/β with
numerator α ≠ 1 (χ₂(2/q) is at x = 4/q²). Relations used: χ₂(1/q) = (q/4)L(½,2;q⁻²), Ti₂(1/q) = −(q/4)L(½,2;−q⁻²),
χ₂(2/q) = (q/8)L(½,2;4q⁻²) (`main.tex`, eq. `eq:lerch`).

Background estimate (not a citation; quoted in the paper as a heuristic since the referee fix of 2026-11-12): a
reconstruction of Hata's method at shift ½ and Q = +q² (`handoff/log2log3/pilot_q/hata/RESULT.md`) suggests q₀ ≈ 55–85
for χ₂(1/q); it says nothing about Q = −q², where his unshifted thresholds are better (Q ≤ −8 against Q ≥ 12).

Also secondhand: Hata, Trans. AMS 336 (1993) (bib `Hata1993`), "reportedly Li₂(1/q) ∉ ℚ for q ≥ 7 and q ≤ −5"; the paper
says it was not consulted (§1.2, bullet "Single dilogarithm values"). It does not affect any novelty range.

## Marked spots in `main.tex` (search for `% HATA-`)

| tag | where | current text (gist) | if Hata's threshold is q_H (and q_H' for Q = −q²) |
|---|---|---|---|
| HATA-3 | abstract, sentences after "…transferred." | "For large q the three statements follow from … DHK; for the first two, a 1990 criterion of Hata, which we could not consult, also applies from a threshold unknown to us. Below these ranges the results are new as far as we know." | State the thresholds: "follow from the criteria of DHK and, for the first two, of Hata (from q ≥ q_H, q_H')". If q_H ≤ 6, Theorem A has nothing new beyond q = 3, 5 and the sentence must say which theorems are new. |
| HATA-1 | §1.2 Context, bullet "Hata's criterion" | secondhand description; "We have not been able to consult this paper"; "We do not know its threshold for the shift ½, at either sign of Q"; the heuristic reconstruction "q ≈ 55–85 for χ₂(1/q)" (estimate, not a citation); "Theorem C lies outside the theorem as it is reviewed" | Replace by a first-hand statement with theorem number and the evaluated thresholds q_H (χ₂(1/q)) and q_H' (Ti₂(1/q)); drop the heuristic estimate (or compare it with the real value); state explicitly whether numerators α ≠ 1 are covered (Theorem C). Delete "We have not been able to consult". |
| HATA-2 | §1.2, paragraph "Novelty." | new ranges: A: 6 ≤ q ≤ 2948 (q = 3, 5 in Chi2Paper); B: 6 ≤ q ≤ 2948; C: 175 ≤ q < 11,795; "subject to the threshold of Hata, which we could not check"; "the range that is genuinely new for Theorem A may be much shorter … perhaps q ≲ 85 or less; for Theorem B we have no estimate"; "Theorem C does not depend on Hata in this way" | New ranges: A: 6 ≤ q < min(2949, q_H) (and say whether q = 3, 5 were already covered); B: 6 ≤ q < min(2949, q_H'); C unchanged unless Hata covers numerator 4 (then 175 ≤ q < min(11,795, its threshold)). Remove the "subject to" and "may be much shorter" sentences. |

Also check, outside the paper:
* `README.md` §"Context" and the paper_q entry (novelty ranges, the sentence "we have not read Hata 1990").
* `paper_q/references.bib`, entry `Hata1990`: add the theorem number used, and remove "the paper itself was NOT read".
* `paper_q/NOVELTY_CHECK.md`: record the read.

No proof in the paper depends on Hata 1990; only the novelty wording does.
