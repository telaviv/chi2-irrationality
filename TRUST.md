# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the two main theorems and each of their main ingredients,

```
'Chi2Irr.chi2_one_third_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2Irr.chi2_one_fifth_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms, the same ones Mathlib uses. The project contains no `sorry`, no `axiom`
declaration, no `native_decide` and no `implemented_by`, so nothing relies on the compiler. Every proof is checked by
the kernel:
- the dual certificates of Theorem B are decidable statements about rational data, proved by `decide +kernel`
  (`Cert/Q3.lean`, `Cert/Q5.lean`);
- the dyadic enclosure of `log 2` used by the log table is proved by `decide +kernel` from Mathlib's series bound
  (`Interval/Log.lean`);
- the six block determinants of Lemma P are evaluated exactly by `norm_num` (`NonVan/NonVanQ.lean`).

## The statement

The kernel checks the proof. It cannot check that the statement means what we claim, so read these definitions yourself:

| file | definition |
|---|---|
| `Chi2Irrational/Defs.lean` | `chi2Term z n := z^(2n+1) / (2n+1)²` and `chi2 z := ∑' n, chi2Term z n`, with `summable_chi2Term` for `|z| ≤ 1`. The `tsum` is therefore the genuine sum of the series. |
| `Chi2Irrational/Statement.lean` | `Chi2OneThirdIrrational := Irrational (chi2 (1/3))`, `Chi2OneFifthIrrational := Irrational (chi2 (1/5))` |

`Irrational` is Mathlib's (`x ∉ Set.range ((↑) : ℚ → ℝ)`).

The main theorems are stated about these definitions directly (`Arith/Assembly.lean`). Everything in between (the
machine Δ_h, the denominators, the certificates) is internal to the proof and does not need to be trusted.

## Generated files

Two Lean files contain literal data produced by a script. The script and its output are **untrusted inputs**: every
number is re-checked by the kernel, so a wrong value makes the build fail; it cannot make a false theorem true.

| data | Lean file | generator |
|---|---|---|
| dual certificate for q = 3 (log table of 804 entries, 30 density cells, cell bounds) | `Cert/DataQ3.lean` | `python scripts/gen_cert.py 3 100 5 30 3 2 Chi2Irrational/Cert/DataQ3.lean Q3` |
| dual certificate for q = 5 (log table of 244 entries, 23 density cells, cell bounds) | `Cert/DataQ5.lean` | `python scripts/gen_cert.py 5 40 2 23 2 2 Chi2Irrational/Cert/DataQ5.lean Q5` |

The script optimises a step density in floating point, rounds it to dyadic rationals, and then replicates the Lean
interval arithmetic exactly in Python fractions, so that every kernel check passes. Re-running it reproduces both files
byte for byte.

## How a certificate is checked

`Cert/Instance.lean` defines the raw certificate `CData` and a Boolean predicate `CData.Valid` collecting every check:
- each entry of the log table against a series enclosure of `log`;
- the mass and range of the step density;
- for every grid cell, an interval upper bound of `2U^μ(x) + V(x)` below the stated `S_k`;
- a lower enclosure of the energy `E(μ)`;
- the tail conditions.

`Cert/Q3.lean` and `Cert/Q5.lean` prove `Valid` by `decide +kernel`. The soundness lemmas then turn it into a
`DualCert`, to which Theorem B (`Analytic/TheoremB.lean`) applies. The certified exponent is the exact rational
`PhiQ = −E_lo + λ + (2/L) Σ_k (S_k − λ)₊`:
- `PhiQ < −2.078` for q = 3;
- `PhiQ < −2.385` for q = 5.

## Cost

With Mathlib cached, `lake build` takes about 10 minutes on a desktop (8 minutes on the
author's machine).
