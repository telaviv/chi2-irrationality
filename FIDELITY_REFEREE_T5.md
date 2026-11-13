# Fidelity referee: Theorem T₅ (`Chi2Irr.TiQ.theoremT5`, Ti₂(1/q) ∉ ℚ for q ≥ 5)

**Verdict: PASS WITH FIXES.** The fixes are to documentation only. The statement is faithful. The proof uses Lemma M,
the new q = 5 certificate and Theorem T's ingredients at q = 5, and `theoremT` for q ≥ 6. The certificate exponent and
the margin recompute exactly. There are no escape hatches. Three docstring or README/TRUST statements are stale or
inaccurate (§6, §7).

AI referee (Claude, 2026-11-13); independent Python (Fractions, mpmath, scipy) and `lake env lean` on a check file. No
human read. No file other than this one was edited; nothing was built or committed.

## 1. Statement

- `Interface5.lean:26` `TheoremT5 : Prop := ∀ q : ℕ, 5 ≤ q → Irrational (ti2 (1 / (q : ℝ)))`. `#print` (with
  `pp.fullNames`) shows `∀ (q : ℕ), 5 ≤ q → Irrational (Chi2Irr.TiQ.ti2 (1 / ↑q))`. Here `↑q : ℝ` and `/` is real
  division. `Irrational` is Mathlib's (`fun x => x ∉ Set.range Rat.cast`). A check file confirms
  `example : ∀ q : ℕ, 5 ≤ q → ti2 (1 / (q : ℝ)) ∉ Set.range ((↑) : ℚ → ℝ) := theoremT5`.
- `ti2` and `ti2Term` (`TiQ/Defs.lean`, unchanged) are `ti2 z = ∑' n, (−1)^n z^(2n+1)/(2n+1)²`, the inverse tangent
  integral. For q ≥ 5, |1/q| ≤ 1/5 ≤ 1, so `summable_ti2Term` applies and the `tsum` is the genuine sum.
- The statement has no extra hypotheses: the only binder is `5 ≤ q`. `#print axioms theoremT5` gives
  `[propext, Classical.choice, Quot.sound]` (rerun here).

## 2. Proof structure (`Interface5.lean:69–83`)

- **q ≥ 6:** the proof is `exact theoremT q h6` (line 83). `theoremT` (`TiQ/Interface.lean`) is unchanged; `git diff
  HEAD --stat` shows edits only to `Axioms.lean`, `Chi2Irrational.lean` (one import), `README.md` and `TRUST.md`.
- **q = 5** (via `omega`, then `subst`):
  - the 2-adic bound is `twoAdic_odd_M 5` (Lemma M);
  - the analytic bound is `cert_t5` (data `Cert.Q5L200`) fed to the existing signed Theorem B `analytic_t`;
  - the arithmetic bound and nonvanishing come through `exists_boundsT 5 … (Real.log 2 / 8) (PhiT5 : ℝ) … margin_t5`,
    which calls the existing `arith_t` and `nonvan_t` (both stated for q ≥ 3);
  - the conclusion is `irrational_of_boundsT`.

  This is the same assembly pattern as the q = 6 branch of `theoremT`.
- The δ-slack lambda is identical to the q = 6 branch: `exp((Φ+ε)h²) ≤ exp((PhiT5+δ+ε)h²)` via `nlinarith`.

## 3. Lemma M ↔ `arith_t`; constants

- `twoAdic_odd_M` (`Interface5.lean:40`) is stated in namespace `TiQ`. With `pp.fullNames` its hypothesis reads
  `padicNorm 2 ((Chi2Irr.TiQ.DeltaT q h).coeff k) ≤ 2 ^ n2 h`, the exact form of `arith_t`'s `hn2`. There is only one
  `DeltaT` (`TiQ/Machine.lean:45`). The asymptotic clause has the same shape as `arith_t`'s `hc2`, with
  `c2 = Real.log 2 / 8`. Lean unifies the two in `exists_boundsT`, so they are the same `DeltaT` by typechecking.
- `M.twoAdic_odd_M_proof` (`M/Final.lean`) supplies `n2M` and `eventually_n2M_le`. The chain from the definition to the
  bound, `DeltaT_eq_Cb` → `HM_eq` → `det_block` → `det_PNz` → `Nblk_entry`, is in `twoAdic_DeltaT_M` (`Final.lean:191`).
- Source agreement:
  - `theta = (4 − MB)/(4q) = 1/q − MB/(4q)` is RESULT's θ₂ = 1/q − 𝕄(f₀)/(4q), with 𝕄 truncated at `Bt h = 16h+16`;
  - `fk k i = −1/(i − pole k)² = −4/(2i+2k+1)²` with `pole k = −(k+½)`, which is RESULT's f_k′;
  - `betaK = −4ω_k(−1)^k q^{2k+1}` matches RESULT's β_k;
  - `OmQ` matches RESULT's Ω_b.
- Constants, recomputed with mpmath at 30 digits:
  - `alphaCoreT 5 = 133/60 + ¼ log 13 − ⅓ log 5 = 2.3214247019`;
  - margin `alphaCoreT 5 + ⅛ log 2 + PhiT5 = −0.0319319` with `PhiT5 = −2.44`;
  - with the exact `PhiQ` the margin is −0.0354837;
  - with the source's Arb Φ₅ = −2.4516816 it is −0.0436135, which matches RESULT and REFEREE_Q5;
  - with Lemma 10₁'s ¼ log 2 it would be +0.0430 (fails), as RESULT states.
- Declared departure: Lean's certificate gives Φ ≤ −2.4435518, against the source's −2.4516816. The margins −0.0319 and
  −0.0436 are stated in `Interface5.lean`, the README and TRUST. They match.
- `margin_t5` uses `log 13 ≤ 4 log 2 − 3/16`, `2 log 2 ≤ log 5 − 1/5` and `log 2 < 0.6931471808`. These give
  −0.01918 < 0 (recomputed), which is sound.

## 4. Certificate `Cert/DataQ5L200.lean` (independent Python, `fractions.Fraction`)

- Parameters: `q = 5, L = 200, s = 2, K = 115, X = 2, N = 2`, which match `gen_cert.py 5 200 2 115 2 2`.
- Lengths: `|cs| = 115 = K`, `|Sks| = 400 = X·L`, `|tab| = 1204`.
- Mass: `Σ cs · s = 200 = L`, exact.
- Heights: `0 ≤ c ≤ 2`, all dyadic with denominator ≤ 2¹⁶, nonincreasing.
- Size constraints: `K·s = 230 ≤ N·L = 400`, and `N ≤ X`.
- Exponent: `λ = −4.651915863`, `E_lo = −1.768954624163`, `σ = Σ(S_k − λ)₊ = 43.940948326212` (100 positive cells).
  **`PhiQ = −E_lo + λ + (2/L)σ = −15272198472343/6250000000000 = −2.44355175557488`**, which matches the docstring and
  TRUST (`−2.4435517556…`). `PhiQ ≤ −244/100` holds with slack 0.00355.
- Log table: every entry satisfies `t ≤ 2⁴⁰ log(i+1) ≤ t+2` (mpmath, 40 digits; 0 failures).
- Tail checks: `−2 log 5 + ½ = −2.72 < 0`, and `log 2 + 2(−2 log 5) = −5.74 < λ`.
- Not recomputed: the cell bounds `S_k` and `E_lo`. They are kernel-checked by `decide +kernel` (`Q5L200.lean`) against
  the pre-existing, previously refereed `CData.Valid` / `Phi_le` (`Cert/Instance.lean`, unchanged).

## 5. Escape hatches

- Grep over `TiQ/M/*.lean`, `TiQ/Interface5.lean`, `Cert/Q5L200.lean` and `Cert/DataQ5L200.lean` for `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `admit`, `opaque`, `extern`, `unsafe` and `set_option`: **no matches**.
- The certificate uses `decide +kernel` (a kernel reduction with no `Lean.ofReduceBool`), the same as the earlier
  certificates.
- `scripts/axioms_t5.txt`: 72 declarations, all `[propext, Classical.choice, Quot.sound]`. This matches the 72
  `#print axioms` lines in `Axioms.lean` (61 old + 11 new).
- All oleans are newer than their sources (BoundA source 00:51, olean 00:56). `lake env lean` re-elaborated
  `M/Trunc.lean`, `M/Final.lean` and `Interface5.lean` cleanly. The only diagnostic is the warning at
  `Trunc.lean:202:29` (unused `hq`, see §6).

## 6. Docstrings vs the formal route

The docstrings state these departures honestly:
- a rational `theta` with a truncated Mahler functional, instead of the 2-adic θ₂ (`M/Defs.lean`, `Interface5.lean`);
- a Leibniz bound with row/column potentials on the 3h×3h block matrix, instead of RESULT's 2h-row Cauchy–Binet
  (`Defs.lean`, `Final.lean`, README);
- the coarser certificate.

The `Gram.lean`, `Binom.lean`, `BoundB.lean` and `Trunc.lean` docstrings match their statements: `DeltaT_eq_Cb`,
`HM_eq`, `det_block`, `Am_bound` = (C), `Om_bound` = (B) `v₂ ≥ 1 − n − n′`, and `err_bound` `v₂ ≥ 8h+8`.

Findings:
- **F1 (fix, `M/Defs.lean:15–16`).** The docstring says the block matrix's "tropical value equals RESULT's subset bound
  exactly (checked for h ≤ 48)". This is true only with **RESULT's** entry bound (A), `2^{i+j+1−h}`. It is false with
  Lean's own (A), `2^{i+j+2−h}`, and false for the potential sum `n2M` that Lean actually proves. Recomputed by optimal
  assignment (scipy `linear_sum_assignment`), all after subtracting 2Σv₂(i!):

  | h | tropical value, RESULT's (A) | tropical value, Lean's (A) | Lean's `n2M` | RESULT's bound 2Σs₂(j) + max_m m(h+1−2m) |
  |---|---|---|---|---|
  | 16 | 100 | 104 | 107 | 100 |
  | 48 | 556 | 568 | 571 | 556 |

  `n2M − RESULT ≈ h/4 + 3`; for example h = 1000 gives 135367 vs 135114. All of this is O(h), so the constant ⅛ is
  unaffected. Suggested wording: "with RESULT's entry bound (A) its tropical value equals RESULT's subset bound (checked
  h ≤ 48); Lean's (A) is one weaker per entry and its potentials are not tight, so `n2M` exceeds RESULT's bound by
  O(h) (≈ h/4)".
- **F2 (note, `M/BoundA.lean:432`, `Final.lean` docstring).** `boundA` proves `v₂(Em_ij) ≥ h − 2 − i − j`. RESULT (A)
  is `v₂ ≥ K − 1 − j − j′ = h − 1 − i − j`, so Lean's bound is one weaker. The loss comes from the term
  `‖Ω_b‖ = 2^{b+1}` and is harmless (O(h) in `n2M`). It is visible in the `BoundA.lean` docstring but is not flagged as
  a departure; suggest one clause in `Final.lean` and the README.
- **F3 (note, `Trunc.lean:202`).** `theta_bound`'s hypothesis `hq : 3 ≤ q` is unused (linter warning). This is
  harmless: dropping it would only generalise the lemma. Optionally rename it to `_hq`.
- **F4 (note, `Interface5.lean` header).** "Lean's certificate is coarser (margin −0.0319)": −0.0319 is the margin with
  the rounded `PhiT5 = −2.44`. The certificate's exact `PhiQ` gives −0.0355. Optionally say "(−0.0319 with
  `PhiT5 = −2.44`)".

## 7. Documentation fixes needed (README.md / TRUST.md)

1. **README:39–40**, in the Theorem T section: "this is why q = 3, 5 are out of reach" is now stale. Suggested wording:
   "… out of reach with Lemma 10₁; q = 5 is Theorem T₅ (Lemma M, ⅛ log 2); q = 3 still fails (margin +0.24 with
   Lemma M, RESULT table)".
2. **README:335**: the row "axiom output of the current tree (61 declarations)" should point to
   `scripts/axioms_t5.txt` (72 declarations). Add a row for `FIDELITY_REFEREE_T5.md` next to the TIQ/Q2NUM referee
   row (README:339). README:343 should also cite `pilot_ti2_q5/RESULT.md` for `TiQ/M/` and `Interface5.lean`.
3. **README:355**: the Ti₂(1/5) margin entry should follow the pattern of the other entries, e.g. "−0.0436 for Ti₂(1/5)
   (Lean's constants: −0.0319; Lean proves < 0, via ≤ −0.019)".
4. **TRUST:20–21**: "each of the 61 declarations in `Axioms.lean`" should be 72. The current-tree axiom output is now
   `scripts/axioms_t5.txt`, run 2026-11-13; keep `axioms_paper_q.txt` as an earlier run.
5. **TRUST:27–31 and 40–42**: add `Cert/Q5L200.lean` (data `Cert/DataQ5L200.lean`) to the list of certificates proved
   by `decide +kernel`, noting that it sets no options.
6. **TRUST "Environment replay"**: state that the new modules (`TiQ/M/*`, `TiQ/Interface5.lean`,
   `Cert/{DataQ5L200,Q5L200}.lean`) have **not** been replayed with `leanchecker`. Only `lake build`'s kernel check
   covers them.
7. **TRUST:92–99**:
   - add "In `TheoremT5`, |1/q| ≤ 1/5 and `summable_ti2Term` applies";
   - add `TiQ/Interface5.lean` to the list of files that state main theorems;
   - add `PhiT5`, `n2M`, `theta`, `MB` (`TiQ/M/Defs.lean`) to the internal definitions that need not be trusted.
8. Optional: `lean_chi2/CLAUDE.md` has no Theorem T₅ entry.

## What I recomputed

- Statement, `#print`s and axioms via `lake env lean` on a scratch check file (21 s).
- `PhiQ` exactly with Python Fractions, mass, height range and dyadicity, lengths, `K·s ≤ N·L`, all 1204 log-table
  enclosures, and the tail checks.
- Margins (mpmath): −0.0319319 (Lean constants), −0.0354837 (exact `PhiQ`), −0.0436135 (source), +0.0430 (¼ log 2), and
  Lean's elementary-bound value −0.01918.
- `n2M(h)` vs RESULT's bound, and tropical values of the block matrix with Lean's (A) and with RESULT's (A), for
  h ≤ 48 (F1).
- Re-elaboration of `M/Trunc.lean`, `M/Final.lean` and `Interface5.lean`; olean timestamps vs sources; `git status` and
  `git diff`.
