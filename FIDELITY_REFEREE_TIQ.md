**Verdict: PASS WITH NOTES.** `Chi2Irr.TiQ.theoremT : TheoremT` states exactly Theorem T of
`handoff/log2log3/pilot_ti2q/RESULT.md`: Ti₂(1/q) ∉ ℚ for every integer q ≥ 6. The definitions are faithful and add no
hidden hypotheses. The notes are about process (uncommitted files, no recorded axiom audit for `theoremT`) and stale
wording in the docs. None of them changes what the theorem means.

# Fidelity referee report: Theorem T (`Chi2Irr.TiQ.theoremT`)

Referee: independent AI fidelity referee (Claude), 2026-11-10. Branch `theorem-tiq`, worktree
`lean_chi2_wt/tiq`, HEAD `9190742` plus uncommitted changes (see N1). I only read files: I did not run `lake build`
and edited nothing except this report. I checked the statement, definitions and constants. The proofs are left to the kernel.

## Q1. `ti2` is the source's Ti₂

* `TiQ/Defs.lean:26`: `ti2Term z n = (-1)^n * z^(2n+1) / (2n+1)^2`. Lean parses this as `((-1)^n · z^(2n+1)) / (2n+1)²`. Index
  from n = 0, sign (−1)ⁿ, odd exponent 2n+1, squared odd denominator. This matches RESULT line 12,
  Σ_{n≥0} (−1)ⁿ z^{2n+1}/(2n+1)², the standard inverse tangent integral (= Im Li₂(iz)). **OK.**
* `TiQ/Defs.lean:29`: `ti2 z = ∑' n, ti2Term z n`. A `tsum` would silently be 0 for a non-summable series. That cannot
  happen here: `summable_ti2Term` (`Defs.lean:36`) proves absolute summability for |z| ≤ 1 (|ti2Term| = |chi2Term|,
  `Defs.lean:31`), and 1/q ≤ 1 for q ≥ 6. So `ti2 (1/q)` is the true sum. **OK.**
* `(q : ℝ)` with `q : ℕ` and `1 / (q : ℝ)` is the real number 1/q. There is no truncated ℕ division, because the cast comes
  first. **OK.**
* `Irrational` is Mathlib's (`x ∉ range (Rat.cast)`). Grep finds no local `def`/`notation`/`abbrev Irrational`
  in `Chi2Irrational/`. **OK.**
* An independent check, `scripts/tiq/check_defs.py:72`, evaluates Ti₂ from the defining series with mpmath `nsum` and checks
  A + Ti₂·B against Σ wᵗ(gu/D)′(t). The errors are ≤ 1.5·10⁻³⁶ (`check_defs.txt`, "ALL OK").

## Q2. `TheoremT` is exactly the claim

* `TiQ/Defs.lean:42`: `∀ q : ℕ, 6 ≤ q → Irrational (ti2 (1 / (q : ℝ)))`. The range is q ≥ 6 with no exclusions and no
  other hypotheses. This is RESULT §0 line 16 verbatim. Negative q are not claimed, as in the source (they follow by oddness
  of Ti₂ anyway). **OK.**
* `TiQ/Interface.lean:121`: `theorem theoremT : TheoremT`. The case split is even q = 6 (direct certificate), even q ≥ 8 and
  odd q ≥ 7 (shifted q = 6 certificate). Together these cover every q ≥ 6 (`omega` derives q = 6 from even, q < 8, q ≥ 6,
  and q ≥ 7 from odd, q ≥ 6). **OK.**
* `TheoremT` does not involve the machine (`DeltaT` etc.). So the meaning of the theorem depends only on `ti2`,
  `Irrational` and the q range. A defect in the machine definitions could make the proof fail, but it could not change what
  is proved.
* Endgame: `irrational_of_boundsT` (`TiQ/MainCond.lean:32`) feeds `irrational_of_poly_approx` (`Criterion.lean:54`,
  Lemma E). That lemma concludes `Irrational ξ` from the denominator, smallness and nonvanishing data. `MachineBoundsT`
  (`MainCond.lean:16–29`) is a structure of proved data, not an assumption: `theoremT` builds it (`exists_boundsT`,
  `Interface.lean:86`). **OK.**

## Q3. Constants

* `alphaCoreT q = 133/60 + ¼ log oddPart(q²+1) − ⅓ log oddPart(q)` (`Defs.lean:45`), with `Q.oddPart n = n / 2^{v₂ n}`
  (`Q/Defs.lean`).
  - Odd q: v₂(q²+1) = 1 and oddPart q = q. So alphaCoreT + `c2TiOdd` (= ¼ log 2, `Defs.lean:49`) = 133/60 + ¼ log(q²+1) − ⅓ log q.
    This is α_Ti (RESULT §2 line 91). **OK.**
  - Even q, e = v₂(q): q²+1 is odd, and −⅓ log oddPart q = −⅓ log q + (e/3) log 2. `Q.c2EvenSharp q = (c(e) − e/3) log 2`
    (`Q/Even/Defs.lean`), with `Q.cE e = (6 − 4e)/(3(3e+8))`. The sum is 133/60 + ¼ log(q²+1) − ⅓ log q + c(e) log 2, which is
    RESULT line 93. `cE` matches c(e) exactly. **OK.**
* `PhiT6 = −25671/10000` (`Defs.lean:52`). The certificate (`TiQ/Cert/Q6L800.lean:167`, `phiQ_le` by `decide +kernel`)
  gives Φ ≤ PhiQ = −2.5671799991… ≤ −2.5671. This is the Lean-format L = 800 certificate of RESULT §6 line 233 / §11
  (−2.567180). `cert_t6_proof` (`TiQ/Certs.lean`) has type `∃ C : DualCert 6, …`, so the q = 6 identity is enforced by type.
  **OK.**
* `betaT q = PhiT6 − ½ log(q/6)` (`Defs.lean:55`) is the shift lemma with base b = 6.
* My recomputation of the margins by hand: q = 6: 2.56416 − 2.5671 = −0.00295; q = 7: −0.0981; q = 8: −0.2254;
  q = 10: −0.1776; q = 14: −0.2910. These agree with `scripts/tiq/margin_check.txt` (worst −0.002948 at q = 6) and with the
  header claim (`Defs.lean:18`: ≤ −0.0029 at q = 6, ≤ −0.098 for q ≥ 7). Closed form: odd margin = 0.54545 + ¼log(1+q⁻²) − ⅓log q,
  and the even margin adds at most c(1) log 2 = 0.0420. Both decrease in q. The Lean margins are proved (`Margin.lean:55,73,107`).

**The documented departure** (`Defs.lean:15–18`): one q = 6 certificate, shifted to every q ≥ 7, in place of RESULT §0's
q = 5 / 8 / 10 / 12 / 14 bases.
* It is sound in principle. `DualCert q` depends on q only through `Wr q = q⁻²` (`Analytic/TheoremB.lean:21–35`). The
  shift lemma `Q.DualCert.shift` (`Q/Shift.lean:86`) is parity-blind: for 1 ≤ q₀ ≤ q it gives Φ(C′) ≤ Φ(C) − ½ log(q/q₀) + δ.
  This is RESULT §4 line 153 ("b ≤ q, any parity"). §11 (line 404–405) already proposes the q = 6 L = 800 certificate for
  q = 7.
* `analytic_betaT` (`Interface.lean:108`) uses it with q₀ = 6 and absorbs δ into the endgame's slack. The statement is
  correct.
* The trade-off: in Lean, odd q ≥ 7 no longer rests on the refereed q = 5 certificate but on the kernel-checked q = 6 one.
  That is a gain in trust, not a loss.

## Q4. The Ti machine (`TiQ/Machine.lean`) against RESULT §1

* `wT q = −1/q²` (`Machine.lean:20`): w = −q⁻². **OK.**
* `SpartT q k = Σ_{j≤k} (−1)^{k−j} q^{2(k−j)}/(2j+1)²` (`Machine.lean:23`). With χ₄(2j+1) = (−1)ʲ,
  (−1)ᵏq^{2k+1}T♮(2k+1) = Σ_j (−1)^{k+j} q^{2(k−j)}/(2j+1)², and (−1)^{k+j} = (−1)^{k−j}. So it matches RESULT line 39/48.
  The ℕ subtraction k − j is safe because j ≤ k. **OK.**
* `poleW q k = (−1)ᵏ q^{2k+1}` (`Machine.lean:27`) in `BfunT`: the pole weight of RESULT line 39. **OK.**
* I re-derived it by hand: μ(1/(u−x_k)) = −4Σ_t wᵗ/(2t+2k+1)². With s = 2t+2k+1, (−1)ᵗ = (−1)ᵏχ₄(s), which gives
  −4(−1)ᵏq^{2k+1}(Ti₂ − T♮(2k+1)), as RESULT line 39–40 states. The signs of A (+4Σ…SpartT) and B (−4Σ…poleW) are the χ₂
  pattern (`Machine.lean` base) with the twisted pieces. **OK.**
* Kernel link: `Lam_eqT` (`TiQ/PoleExpansion.lean:121`) proves ΛT(g) = AfunT + ti2(1/q)·BfunT, with ΛT the series
  Σ wᵗ(gu/D)′(t), and `aeval_ti2_DeltaT` (line 168) proves it at the determinant level. So the machine is tied to `ti2`
  itself by a proof, not only by agreement of names.
* Scripts:
  - `check_defs.txt`: the Lean definitions equal the pilot Ti machine and P_h(−q², qX) entrywise at q ∈ {5,6,7,8},
    h ∈ {1,2,3,5,8};
  - `check_twist.txt`: the twisted and Q-form entries and Δ agree (ti and chi) at q ∈ {2,3,5,6}, h ≤ 12;
  - the Lemma 1 float check is reported under Q1.
* Signed Theorem B (`TiQ/Analytic.lean`): the header (lines 1–15) and `abs_WT` (line 28) show that the only change is
  |wTᵗ| = Wr qᵗ. This matches RESULT §4's argument (F6).

## Q5. Other checks

* **No escape hatches.** Grep over `Chi2Irrational/**/*.lean` finds no `sorry`, `axiom`, `native_decide`, `implemented_by`,
  `@[extern]`, `opaque` or `admit`. The certificates use `decide +kernel`, which adds no axioms. The recorded audits
  (`scripts/tiq/axioms_{analytic,nonvan,twoadic_odd}.txt`) show the standard three axioms for those ingredients.
* **N1 (process, important).** The proof is complete only in the working tree. Committed HEAD `9190742` still has
  `sorry` in `Interface.lean` for `nonvan_t`, `analytic_t`, `cert_t6` and the three margins (see `git diff`). `TiQ/Cert/`,
  `TiQ/Certs.lean`, `scripts/tiq/gen_cert_proof_t6.py`, `margin_check.*` and `build_cert_t6.txt` are untracked, and
  `Axioms.lean` and `Chi2Irrational.lean` are modified. Before anyone cites `theoremT`, commit these and run a clean build.
* **N2 (process).** There is no recorded output of `#print axioms Chi2Irr.TiQ.theoremT`. It is newly listed in the
  uncommitted `Axioms.lean`. The same holds for `arith_t`, `twoAdic_even_t`, `cert_t6` and the margins. Run
  `lake env lean Axioms.lean` and save the output. `build_cert_t6.txt` shows only that `DataQ6L800` built.
* **N3 (docstring).** `twoAdic_odd_t`'s docstring (`Interface.lean:45`) says "n₂ ≤ ⌊h²/4⌋ + O(h log h)". RESULT §3 has
  n₂ ≤ ⌊h²/4⌋ exactly. The Lean statement is the asymptotic form with c₂ = ¼ log 2, which is weaker than the paper lemma but
  all the endgame needs. This is cosmetic.
* **N4 (stale source wording).** RESULT's status lines no longer match the Lean work:
  - the header (lines 4, 8–9, "Not in Lean"; Theorem B "Lean only for w > 0") and §10 / §11 ("not started") predate this
    port;
  - once N1/N2 are done, Theorem B for signed w is Lean-proved (`analytic_t_proof`), and the G4 / q = 6 dependence on the
    pilot certificate is replaced by the kernel-checked L = 800 certificate;
  - update the per-thread docs (not HANDOFF).
* **N5 (scope).** Like the base χ₂ files, `nonvan_t`, `arith_t` and `twoAdic_*` are stated for q ≥ 3 and `analytic_t` for
  q ≥ 2. They are more general than needed and are used only at q ≥ 6. This is harmless.
