# What you have to trust

The written proofs are in two papers: `paper/` (q = 3, 5; published, unchanged) and `paper_q/` (Theorems Q₄, T and Q4′
as Theorems A, B and C; its §13 maps every step to a Lean declaration of commit `7a2780c`).

## Axioms

`lake env lean Axioms.lean` prints, for the main theorems and each of their main ingredients,

```
'Chi2Irr.Q.theoremQ4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.TiQ.theoremT5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.TiQ.theoremT' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.QZ.theoremQ4num' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.Q.theoremQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_third_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_fifth_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the same list for each of the 72 declarations in `Axioms.lean`. The output of the current tree, with Theorem T₅
(run 2026-11-13), is `scripts/axioms_t5.txt`. The output for commit `7a2780c` (61 declarations, run 2026-11-12) is
`scripts/axioms_paper_q.txt`; it was produced in a worktree at commit `54a3d5b`, whose tree is
identical to that of `7a2780c`, because this checkout's `.lake` holds an older build. Earlier runs:
`scripts/q2num/runs/axioms_q2num.txt` (50 declarations, with Theorem Q4′), `scripts/axioms_q4.txt` (41, with
Theorem Q₄), `scripts/axioms_q.txt` (37, with Theorem Q). These are Lean's three standard axioms, the same ones Mathlib uses. The project contains no
`sorry`, no `axiom` declaration, no `native_decide` and no `implemented_by`, so nothing relies on the compiler. Every
proof is checked by the kernel:
- the dual certificates of Theorem B are decidable statements about rational data, proved by `decide +kernel`
  (`Cert/Q3.lean`, `Cert/Q5.lean`, for Theorem Q `Cert/Q14.lean`, and for Theorem Q₄ `Cert/Q6.lean`, `Cert/Q8.lean`,
  `Cert/Q10.lean`, `Cert/Q12.lean`, and for Theorem Q4′ `QZ/CertQ175.lean`, data `QZ/CertDataQ175.lean` from
  `scripts/q2num/gen_cert_z.py 2 175 1200 12 70 1 1`, PhiQ = −4.0033242, kernel checks 10697 s wall). The only option set in these files is `set_option maxRecDepth` on the log-table
  literal of `Cert/DataQ6.lean` (and of `QZ/CertDataQ175.lean`), an elaborator recursion limit that does not affect the
  kernel; `QZ/Margin.lean` sets `exponentiation.threshold` so that `norm_num` evaluates `175^104 < 2^775`;
- the dyadic enclosure of `log 2` used by the log table is proved by `decide +kernel` from Mathlib's series bound
  (`Interval/Log.lean`);
- the six block determinants of Lemma P for q = 3, 5 are evaluated exactly by `norm_num` (`NonVan/NonVanQ.lean`); for
  Theorem Q, `Q/NonVan.lean` computes the three block determinants as rational functions of q and proves their
  numerators nonzero for every integer q ≥ 2; for Theorem T, `TiQ/NonVan/NonVanT.lean` does the same for the Ti blocks
  (the χ₂ determinants at q² ↦ −q²); for Theorem Q4′, `QZ/NonVan.lean` evaluates them at ζ = q/2 (integers `nS`, `nL`,
  `nD`, nonzero for q ≥ 5);
- Theorem T's certificate (`TiQ/Cert/Q6L800.lean` and `TiQ/Cert/Q6L800Cells{A,B,C,D}.lean`, data
  `TiQ/Cert/DataQ6L800.lean`) and Theorem Q4′'s certificate (`QZ/CertQ175.lean`, data `QZ/CertDataQ175.lean`) are proved
  by `decide +kernel` in the same way; `TiQ/Cert/DataQ6L800.lean` sets `maxRecDepth` on its literals; so is Theorem T₅'s
  certificate (`Cert/Q5L200.lean`, data `Cert/DataQ5L200.lean`, no options set);

## Environment replay

**Theorem T₅ (2026-11-13).** The new modules (`TiQ/M/*`, `TiQ/Interface5.lean`, `Cert/{DataQ5L200,Q5L200}.lean`) have
**not** been replayed with `leanchecker`; they are checked by the kernel during `lake build` (9196 jobs, 2026-11-13).

**Theorems T and Q4′ (2026-11-12), partial.** The modules under `QZ/` and `TiQ/` were replayed with the command below,
on the tree of commit `7a2780c` (in the worktree at `54a3d5b`, identical tree): 40 modules pass, 0 fail (3189 s,
`scripts/leanchecker_qz_tiq.log`). **Not yet replayed:** the seven modules containing the `decide +kernel` proofs of
the two new certificates (`QZ/CertQ175.lean`, `TiQ/Certs.lean`, `TiQ/Cert/Q6L800.lean`, `TiQ/Cert/Q6L800Cells{A,B,C,D}.lean`),
since each replay repeats hours of kernel evaluation; they are checked by the kernel during `lake build`.

**Theorem Q₄ (2026-11-09).** After the files for even q were added (91 modules), every module was replayed again with
the command below (`scripts/leanchecker_q4.log`): all 91 modules pass (3611 s ≈ 60 min).

**Theorem Q (2026-11-09).** After the files for general q were added (73 modules), every module was replayed again with
the command below.
All 73 modules pass (2443 s ≈ 41 min; `scripts/leanchecker_q.log`).

The record for q = 3, 5 follows. `lake build` checks each declaration in the kernel as it is added. To avoid trusting
the elaborator's handling of the stored environment, every declaration of the 61 project modules of that version was
also replayed through the kernel with `leanchecker`, the lean4checker tool shipped with the Lean toolchain:

```sh
for m in $(find Chi2Irrational -name "*.lean" | sed 's/\.lean$//; s#/#.#g'); do lake env leanchecker "$m"; done
```

All 61 modules pass (about two hours on the author's machine). Each module is replayed against the compiled environment
of its imports, so Mathlib itself is not re-checked; that would need `leanchecker --fresh`, which we have not run.
Running `leanchecker` on the root module `Chi2Irrational`, which has no declarations of its own, fails on Windows while
loading Mathlib `.olean` files (a different file on each attempt, all present on disk), which we attribute to resource
limits rather than to a kernel error.

## The statements

The kernel checks the proof. It cannot check that the statements mean what we claim, so read these definitions yourself:

| file | definition |
|---|---|
| `Chi2Irrational/Defs.lean` | `chi2Term z n := z^(2n+1) / (2n+1)²` and `chi2 z := ∑' n, chi2Term z n`, with `summable_chi2Term` for `|z| ≤ 1`. The `tsum` is therefore the genuine sum of the series. |
| `Chi2Irrational/Statement.lean` | `Chi2OneThirdIrrational := Irrational (chi2 (1/3))`, `Chi2OneFifthIrrational := Irrational (chi2 (1/5))` |
| `Chi2Irrational/Q/Defs.lean` | `Q.TheoremQ := ∀ q : ℕ, 3 ≤ q → q ∉ ({4, 6, 8, 10, 12} : Finset ℕ) → Irrational (chi2 (1 / (q : ℝ)))` (proved as `Q.theoremQ` in `Q/Interface.lean`) |
| `Chi2Irrational/Q/Even/Defs.lean` | `Q.TheoremQ4 := ∀ q : ℕ, 3 ≤ q → q ≠ 4 → Irrational (chi2 (1 / (q : ℝ)))` (proved as `Q.theoremQ4` in `Q/Even/Interface.lean`) |
| `Chi2Irrational/TiQ/Defs.lean` | `TiQ.ti2Term z n := (−1)^n · z^(2n+1) / (2n+1)²`, `TiQ.ti2 z := ∑' n, ti2Term z n` (`summable_ti2Term` for `|z| ≤ 1`), and `TiQ.TheoremT := ∀ q : ℕ, 6 ≤ q → Irrational (ti2 (1 / (q : ℝ)))` (proved as `TiQ.theoremT` in `TiQ/Interface.lean`) |
| `Chi2Irrational/TiQ/Interface5.lean` | `TiQ.TheoremT5 := ∀ q : ℕ, 5 ≤ q → Irrational (ti2 (1 / (q : ℝ)))` (proved as `TiQ.theoremT5`; same `ti2` as Theorem T) |
| `Chi2Irrational/QZ/Interface.lean` | `QZ.theoremQ4num : ∀ q : ℕ, Odd q → 175 ≤ q → Irrational (chi2 (2 / (q : ℝ)))` (statement written in the theorem itself; `Odd` is Mathlib's) |

`Irrational` is Mathlib's (`x ∉ Set.range ((↑) : ℚ → ℝ)`). In `TheoremQ` and `TheoremQ4`, `1 / (q : ℝ)` is real division after the cast
ℕ → ℝ, and |1/q| ≤ 1/3, so `summable_chi2Term` applies and `chi2` is again the genuine sum of the series (in any case a
non-summable `tsum` is 0, which is rational).

In `TheoremT`, |1/q| ≤ 1/6 and `summable_ti2Term` applies; in `theoremQ4num`, `2 / (q : ℝ)` is real division and
|2/q| ≤ 2/175.

The main theorems are stated about these definitions directly (`Arith/Assembly.lean` for q = 3, 5, `Q/Interface.lean`
for Theorem Q, `Q/Even/Interface.lean` for Theorem Q₄, `TiQ/Interface.lean` for Theorem T, `QZ/Interface.lean` for
Theorem Q4′). Everything in between (the machines Δ_h, `DeltaT`, `DeltaZ`, the denominators, the certificates, for
Theorem Q the constants `oddPart`, `alphaCore`, `c2Odd`, `c2Even`, `betaOdd`, `betaEven` of `Q/Defs.lean`, for Theorem Q₄
the constants `cE`, `c2EvenSharp`, `PhiT` and the set `newQ` of `Q/Even/Defs.lean`, for Theorem T `alphaCoreT`, `c2TiOdd`,
`PhiT6`, `betaT` of `TiQ/Defs.lean`, for Theorem Q4′ `alphaZ`, `c2Num`, `qB`, `PhiB`, `betaZ` of `QZ/Defs.lean`, and for Theorem T₅ `PhiT5` and everything in
`TiQ/M/` (`Cb`, `fd`, `MB`, `theta`, `Em`, `Am`, `Om`, the potentials `rP`, `cP`)) is
internal to the proof and does not need to be trusted: a wrong internal definition could make the proof fail, not make a statement weaker.

## Generated files

Ten Lean files contain literal data produced by a script. The scripts and their output are **untrusted inputs**: every
number is re-checked by the kernel, so a wrong value makes the build fail; it cannot make a false theorem true.

| data | Lean file | generator |
|---|---|---|
| dual certificate for q = 3 (log table of 804 entries, 30 density cells, cell bounds) | `Cert/DataQ3.lean` | `python scripts/gen_cert.py 3 100 5 30 3 2 Chi2Irrational/Cert/DataQ3.lean Q3` |
| dual certificate for q = 5 (log table of 244 entries, 23 density cells, cell bounds) | `Cert/DataQ5.lean` | `python scripts/gen_cert.py 5 40 2 23 2 2 Chi2Irrational/Cert/DataQ5.lean Q5` |
| dual certificate for q = 14 (log table of 1204 entries, 40 density cells, 400 cell bounds) | `Cert/DataQ14.lean` | `python scripts/gen_cert.py 14 200 4 40 2 1 Chi2Irrational/Cert/DataQ14.lean Q14` |
| dual certificate for q = 6 (log table of 2404 entries, 54 density cells, 800 cell bounds) | `Cert/DataQ6.lean` | `python scripts/gen_cert.py 6 400 8 54 2 2 Chi2Irrational/Cert/DataQ6.lean Q6` |
| dual certificate for q = 8 (log table of 1204 entries, 50 density cells, 400 cell bounds) | `Cert/DataQ8.lean` | `python scripts/gen_cert.py 8 200 4 50 2 1 Chi2Irrational/Cert/DataQ8.lean Q8` |
| dual certificate for q = 10 (log table of 1204 entries, 46 density cells, 400 cell bounds) | `Cert/DataQ10.lean` | `python scripts/gen_cert.py 10 200 4 46 2 1 Chi2Irrational/Cert/DataQ10.lean Q10` |
| dual certificate for q = 12 (log table of 1204 entries, 46 density cells, 400 cell bounds) | `Cert/DataQ12.lean` | `python scripts/gen_cert.py 12 200 4 46 2 1 Chi2Irrational/Cert/DataQ12.lean Q12` |
| Theorem T: dual certificate for q = 6, L = 800 (log table of 4804 entries, 108 density cells, 1600 cell bounds) | `TiQ/Cert/DataQ6L800.lean` | `scripts/gen_cert.py 6 800 8 108 2 2` (header of the file); the proof files are split by `scripts/tiq/gen_cert_proof_t6.py` |
| Theorem T₅: dual certificate for q = 5, L = 200 (log table of 1204 entries, 115 density cells, 400 cell bounds) | `Cert/DataQ5L200.lean` | `python scripts/gen_cert.py 5 200 2 115 2 2 Chi2Irrational/Cert/DataQ5L200.lean Q5L200` |
| Theorem Q4′: dual certificate at w = (2/175)² (log table of 4804 entries, 70 density cells, 1200 cell bounds) | `QZ/CertDataQ175.lean` | `scripts/q2num/gen_cert_z.py 2 175 1200 12 70 1 1`; proof file by `scripts/q2num/gen_cert_proof_z.py` |

The scripts optimise a step density in floating point, round it to dyadic rationals, and then replicate the Lean
interval arithmetic exactly in Python fractions, so that every kernel check passes. Re-running `gen_cert.py` reproduces
the first seven files byte for byte (re-checked for q = 6, 8, 10, 12 on 2026-11-09); the reproducibility of the last two
has not been re-checked.

## How a certificate is checked

`Cert/Instance.lean` defines the raw certificate `CData` and a Boolean predicate `CData.Valid` collecting every check:
- each entry of the log table against a series enclosure of `log`;
- the mass and range of the step density;
- for every grid cell, an interval upper bound of `2U^μ(x) + V(x)` below the stated `S_k`;
- a lower enclosure of the energy `E(μ)`;
- the tail conditions.

`Cert/Q3.lean`, `Cert/Q5.lean`, `Cert/Q14.lean` and `Cert/Q6.lean`, …, `Cert/Q12.lean` prove `Valid` by
`decide +kernel`. The soundness lemmas then turn it
into a `DualCert`, to which Theorem B (`Analytic/TheoremB.lean`) applies. The certified exponent is the exact rational
`PhiQ = −E_lo + λ + (2/L) Σ_k (S_k − λ)₊`:
- `PhiQ < −2.078` for q = 3;
- `PhiQ < −2.385` for q = 5;
- `PhiQ = −3.0372394… < −3.03` for q = 14;
- `PhiQ = −2.5635463… < −2.56` for q = 6, `−2.7264892… < −2.72` for q = 8, `−2.8528812… < −2.85` for q = 10 and
  `−2.9535971… < −2.95` for q = 12;
- `PhiQ = −2.5671799991… ≤ −2.5671` for Theorem T's certificate at q = 6 (`TiQ/Cert/Q6L800.lean`, `phiQ_le`);
- `PhiQ = −2.4435517556… ≤ −2.44` for Theorem T₅'s certificate at q = 5, L = 200 (`Cert/Q5L200.lean`; kernel check 461 s);
- `PhiQ = −4.0033242421… ≤ −4.003` for Theorem Q4′'s certificate at w = (2/175)² (`QZ/CertInstance.lean` defines
  `CDataZ`, with log w = 2 log 2 − 2 log 175; `QZ/CertQ175.lean` checks it).

For Theorem Q the q = 3 and q = 14 certificates are moved to every odd q ≥ 3 and every even q ≥ 14 by the shift lemma
(`Q/Shift.lean`), which is proved, not computed. For Theorem Q₄ the certificates at q = 6, 8, 10, 12 are used directly
at their own q, with no shift. For Theorem T the q = 6 certificate is used at q = 6 and shifted to every q ≥ 7; a
`DualCert q` sees only |w| = q⁻², so it applies to the signed weight w = −q⁻² (`TiQ/Analytic.lean`, `abs_WT`). For
Theorem Q4′ the certificate at q = 175 is shifted to every odd q ≥ 175 at real weight (`QZ/Shift.lean`).

## Who checked what

The construction, the written proofs, the paper and this formalisation were produced largely by AI models (Claude,
Anthropic), working under the direction of the author. The written
proof of Theorem Q was read by one AI gate referee (PASS WITH FIXES, fixes applied). The fidelity of the Lean statement
of Theorem Q was checked by an independent AI referee, `FIDELITY_REFEREE_Q.md` (PASS WITH FIXES; the fixes were
documentation only, in this file, the README and the paper, applied). It checked that `TheoremQ` is exactly the claimed
statement with the same exception set, found no hidden hypotheses, custom axioms or trusted code, recomputed both margin
families in interval arithmetic for 3 ≤ q ≤ 5001 by code that shares nothing with the project's scripts
(`scripts/q/referee/`), and recomputed the q = 3 and q = 14 certificate exponents exactly from the data files.

For Theorem Q₄, the written proof of Lemma 10_e and of the cases q = 6, 8, 10, 12 was read by one AI gate referee
(PASS WITH FIXES, no errors; fixes applied), who re-certified the analytic constants with independent code. The
fidelity of the Lean statement of Theorem Q₄ was checked by an independent AI referee, `FIDELITY_REFEREE_Q4.md` (PASS
WITH FIXES; documentation only, applied). It checked that `TheoremQ4` is exactly the claimed statement, with q = 4 the
only exception, that the constants `cE` and `c2EvenSharp` are those of the written proof, that Lemma 10_e is stated for
the same Δ_h as Theorem Q and counts the 2-adic share of the gain once, and that there are no hidden hypotheses, custom
axioms or trusted code. It recomputed the four margins in interval arithmetic and the four certificate exponents exactly
from the data files, by code that shares nothing with the project's scripts (`scripts/q/referee_q4/`).

For Theorem T, the written proof (`pilot_ti2q/RESULT.md`) was read by one AI gate referee (PASS WITH FIXES, fixes
applied), with independent code. The fidelity of the Lean statement was checked by an independent AI referee,
`FIDELITY_REFEREE_TIQ.md` (PASS WITH NOTES). It checked that `ti2` is the inverse tangent integral and its `tsum` is
genuine, that `TheoremT` is exactly "Ti₂(1/q) ∉ ℚ for every q ≥ 6" with no hidden hypotheses, that the constants match
the written proof, that the Ti machine is tied to `ti2` by a proof (`Lam_eqT`, `aeval_ti2_DeltaT`), and that there are
no escape hatches. Its process notes (uncommitted files and no recorded axiom audit at the time) were resolved before the
merge: the axiom audit is `scripts/tiq/axioms_full.txt` and, for the current tree, `scripts/axioms_paper_q.txt`.

For Theorem Q4′, the written proof (`pilot_chi2_2q/RESULT.md`) was read by one AI gate referee (PASS WITH FIXES, fixes
applied), who also produced an independent certificate of the q = 173 base. The fidelity of the Lean statement was
checked by an independent AI referee, `FIDELITY_REFEREE_Q2NUM.md` (PASS WITH REMARKS; no code change). It checked the
statement and the bridge `chi2_two_div`, that `DeltaZ` is the χ₂(1/q) machine at ζ = q/2 (`DeltaZ_natCast` holds by
`rfl`), that the constants match the written proof with base 175 in place of 173, and recomputed the margin and the
certificate exponent.

For Theorem T₅, the written proof of Lemma M (`pilot_ti2_q5/RESULT.md`) was read by one AI gate referee (PASS WITH FIXES,
fixes applied), with independent code. The Lean route differs (rational θ, one Leibniz bound with potentials on a block
matrix in place of the 2h-row Cauchy–Binet); its fidelity was checked by an independent AI referee,
`FIDELITY_REFEREE_T5.md` (PASS WITH FIXES; documentation only, applied), who recomputed the q = 5 certificate exponent
exactly and the margin. Lemma M as formalised has not been read by a human.

The paper `paper_q/` was reviewed as a whole by one further AI referee (`paper_q/REFEREE.md`).

Apart from the Lean kernel check, **no human has reviewed the mathematics or the Lean code**.

## Cost

With Mathlib cached, `lake build` took about 10 minutes on a desktop (8 minutes on the author's machine) before Theorem Q
was added. `LEAN_NUM_THREADS=4 lake build` of the current version runs 9186 jobs. The kernel checks of the
certificates for general q take 233 s (q = 14, `Cert/Q14.lean`), 502 s (q = 6), 191 s (q = 8), 170 s (q = 10) and
171 s (q = 12); Theorem Q4′'s certificate (`QZ/CertQ175.lean`) took 10697 s wall on a shared machine, and Theorem T's
certificate (`TiQ/Cert/*`) takes several hours. The full build has not been re-timed.
