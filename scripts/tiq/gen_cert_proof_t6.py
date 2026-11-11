"""Theorem T: write `Chi2Irrational/TiQ/Cert/Q6L800.lean` (kernel checks of `DataQ6L800.data`, q = 6, L = 800).
Runs `scripts/q/gen_cert_proof.py`'s generator text with the output path and names changed (the original writes
`Chi2Irrational/Cert/Q{q}.lean`, which must not be touched).
Usage: python scripts/tiq/gen_cert_proof_t6.py
"""
import sys
src = open("scripts/q/gen_cert_proof.py", encoding="utf-8").read()
last = src.rstrip("\n").split("\n")[-1]
assert last.startswith('open(f"Chi2Irrational/Cert/Q{q}.lean"'), last
src = src.rstrip(chr(10))[: -len(last)] + "RESULT_TEXT = chr(10).join(o)" + chr(10)
sys.argv = ["gen", "6", "1600", "50", "25671", "10000",
            "6 800 8 108 2 1 Chi2Irrational/TiQ/Cert/DataQ6L800.lean Q6L800", "-2.5671799991"]
g = {}
exec(compile(src, "gen_cert_proof.py", "exec"), g)
txt = g["RESULT_TEXT"]
for a, b in [("import Chi2Irrational.Cert.DataQ6", "import Chi2Irrational.TiQ.Cert.DataQ6L800"),
             ("Chi2Irr.Cert.Q6", "Chi2Irr.Cert.Q6L800"), ("`DataQ6.data`", "`DataQ6L800.data`"),
             ("for q = 6: kernel checks", "for q = 6, L = 800 (Theorem T): kernel checks"),
             ("`|Δ_h(χ₂(1/6))| ≤ exp((Φ + ε) h²)` eventually", "`|Δ^Ti_h(Ti₂(1/6))| ≤ exp((Φ + ε) h²)` eventually (`TiQ.analytic_t`)"),
             ("scripts/q/gen_cert_proof.py", "scripts/tiq/gen_cert_proof_t6.py")]:
    txt = txt.replace(a, b)
open("Chi2Irrational/TiQ/Cert/Q6L800.lean", "w", encoding="utf-8", newline="\n").write(txt)
