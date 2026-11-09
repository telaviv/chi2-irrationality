# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the main theorems and each of their main ingredients,

```
'Chi2Irr.Q.theoremQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_third_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_fifth_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the same list for each of the 37 declarations in `Axioms.lean` (the output of the run with Theorem Q is
`scripts/axioms_q.txt`). These are Lean's three standard axioms, the same ones Mathlib uses. The project contains no
`sorry`, no `axiom` declaration, no `native_decide` and no `implemented_by`, so nothing relies on the compiler. Every
proof is checked by the kernel:
- the dual certificates of Theorem B are decidable statements about rational data, proved by `decide +kernel`
  (`Cert/Q3.lean`, `Cert/Q5.lean`, and for Theorem Q `Cert/Q14.lean`);
- the dyadic enclosure of `log 2` used by the log table is proved by `decide +kernel` from Mathlib's series bound
  (`Interval/Log.lean`);
- the six block determinants of Lemma P for q = 3, 5 are evaluated exactly by `norm_num` (`NonVan/NonVanQ.lean`); for
  Theorem Q, `Q/NonVan.lean` computes the three block determinants as rational functions of q and proves their
  numerators nonzero for every integer q ≥ 2.

## Environment replay

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

`Irrational` is Mathlib's (`x ∉ Set.range ((↑) : ℚ → ℝ)`). In `TheoremQ`, `1 / (q : ℝ)` is real division after the cast
ℕ → ℝ, and |1/q| ≤ 1/3, so `summable_chi2Term` applies and `chi2` is again the genuine sum of the series (in any case a
non-summable `tsum` is 0, which is rational).

The main theorems are stated about these definitions directly (`Arith/Assembly.lean` for q = 3, 5, `Q/Interface.lean`
for Theorem Q). Everything in between (the machine Δ_h, the denominators, the certificates, and for Theorem Q the
constants `oddPart`, `alphaCore`, `c2Odd`, `c2Even`, `betaOdd`, `betaEven` of `Q/Defs.lean`) is internal to the proof and
does not need to be trusted: a wrong internal definition could make the proof fail, not make a statement weaker.

## Generated files

Three Lean files contain literal data produced by a script. The script and its output are **untrusted inputs**: every
number is re-checked by the kernel, so a wrong value makes the build fail; it cannot make a false theorem true.

| data | Lean file | generator |
|---|---|---|
| dual certificate for q = 3 (log table of 804 entries, 30 density cells, cell bounds) | `Cert/DataQ3.lean` | `python scripts/gen_cert.py 3 100 5 30 3 2 Chi2Irrational/Cert/DataQ3.lean Q3` |
| dual certificate for q = 5 (log table of 244 entries, 23 density cells, cell bounds) | `Cert/DataQ5.lean` | `python scripts/gen_cert.py 5 40 2 23 2 2 Chi2Irrational/Cert/DataQ5.lean Q5` |
| dual certificate for q = 14 (log table of 1204 entries, 40 density cells, 400 cell bounds) | `Cert/DataQ14.lean` | `python scripts/gen_cert.py 14 200 4 40 2 1 Chi2Irrational/Cert/DataQ14.lean Q14` |

The script optimises a step density in floating point, rounds it to dyadic rationals, and then replicates the Lean
interval arithmetic exactly in Python fractions, so that every kernel check passes. Re-running it reproduces all three
files byte for byte.

## How a certificate is checked

`Cert/Instance.lean` defines the raw certificate `CData` and a Boolean predicate `CData.Valid` collecting every check:
- each entry of the log table against a series enclosure of `log`;
- the mass and range of the step density;
- for every grid cell, an interval upper bound of `2U^μ(x) + V(x)` below the stated `S_k`;
- a lower enclosure of the energy `E(μ)`;
- the tail conditions.

`Cert/Q3.lean`, `Cert/Q5.lean` and `Cert/Q14.lean` prove `Valid` by `decide +kernel`. The soundness lemmas then turn it
into a `DualCert`, to which Theorem B (`Analytic/TheoremB.lean`) applies. The certified exponent is the exact rational
`PhiQ = −E_lo + λ + (2/L) Σ_k (S_k − λ)₊`:
- `PhiQ < −2.078` for q = 3;
- `PhiQ < −2.385` for q = 5;
- `PhiQ = −3.0372394… < −3.03` for q = 14.

For Theorem Q the q = 3 and q = 14 certificates are moved to every odd q ≥ 3 and every even q ≥ 14 by the shift lemma
(`Q/Shift.lean`), which is proved, not computed.

## Who checked what

The construction, the written proofs, the paper and this formalisation were produced largely by AI models (Claude,
Anthropic), working under the direction of the author. The written
proof of Theorem Q was read by one AI gate referee (PASS WITH FIXES, fixes applied). The fidelity of the Lean statement
of Theorem Q was checked by an independent AI referee, `FIDELITY_REFEREE_Q.md` (PASS WITH FIXES; the fixes were
documentation only, in this file, the README and the paper, applied). It checked that `TheoremQ` is exactly the claimed
statement with the same exception set, found no hidden hypotheses, custom axioms or trusted code, recomputed both margin
families in interval arithmetic for 3 ≤ q ≤ 5001 by code that shares nothing with the project's scripts
(`scripts/q/referee/`), and recomputed the q = 3 and q = 14 certificate exponents exactly from the data files. Apart from
the Lean kernel check, **no human has reviewed the mathematics or the Lean code**.

## Cost

With Mathlib cached, `lake build` took about 10 minutes on a desktop (8 minutes on the author's machine) before Theorem Q
was added. `LEAN_NUM_THREADS=4 lake build` of the current version runs 9121 jobs; the kernel check of the q = 14
certificate (`Cert/Q14.lean`) alone takes 233 s. The full build has not been re-timed.
