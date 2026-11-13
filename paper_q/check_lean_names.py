"""Check that every Lean declaration and file cited in paper_q/main.tex exists at the cited commit.

Usage (from lean_chi2/):  python paper_q/check_lean_names.py [commit]
For each \\lean{...} token in main.tex:
  * a token with '/' (a path; `\\slash{}` in the source) must be a file or folder under Chi2Irrational/ (or the repo root);
  * a dotted or underscore identifier must be declared (theorem/lemma/def/structure/...) in Chi2Irrational/ at the
    commit, inside a matching namespace (the dotted prefix must equal the tail of the enclosing namespace plus any
    dotted part of the declared name).
Tokens that are not Lean names (axiom names, tactic names, hashes, shell words) are listed in SKIP.
"""
import re, subprocess, sys

COMMIT = sys.argv[1] if len(sys.argv) > 1 else "7a2780c"
tex = open("paper_q/main.tex", encoding="utf-8").read()
toks = re.findall(r"\\lean\{((?:[^{}]|\{[^{}]*\})*)\}", tex)

def clean(t):
    t = t.replace("\\slash{}", "/").replace("\\_", "_").replace("\\textunderscore", "_")
    return t.strip()

SKIP = {"propext", "Classical.choice", "Quot.sound", "sorry", "native_decide", "implemented_by", "decide +kernel",
        "main", "7a2780c", "7a2780c73c5d84fc41e3ea49f56dabf7e13b0235", "lake env lean Axioms.lean", "leanchecker",
        "lean4checker", "tsum", "Irrational x", "Irrational", "Odd", "chi2 z", "ti2 z", "zeta5", "DualCert",
        "scripts/axioms_paper_q.txt", "scripts/gen_cert.py", "scripts/q2num/gen_cert_z.py"}

files = subprocess.run(["git", "ls-tree", "-r", "--name-only", COMMIT], capture_output=True, text=True,
                       encoding="utf-8").stdout.split("\n")
fileset = set(files)
dirs = {"/".join(f.split("/")[:i]) for f in files for i in range(1, f.count("/") + 1)}

# collect declarations with their namespaces
decls = {}  # short name -> list of full names
for f in files:
    if not (f.startswith("Chi2Irrational") and f.endswith(".lean")):
        continue
    src = subprocess.run(["git", "show", f"{COMMIT}:{f}"], capture_output=True, text=True, encoding="utf-8").stdout
    ns = []
    for line in src.split("\n"):
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r"^end\s+(\S+)", line)
        if m and ns:
            ns.pop(); continue
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
                     r"(theorem|lemma|def|structure|abbrev|instance|inductive)\s+([^\s(:{\[]+)", line)
        if m:
            name = m.group(2)
            full = ".".join(ns + [name])
            decls.setdefault(name.split(".")[-1], []).append((full, f))

bad = []
checked = 0
for t in toks:
    c = clean(t)
    if c in SKIP or not c:
        continue
    if "/" in c or c.endswith(".lean"):
        path = c.rstrip("/")
        cands = [path, "Chi2Irrational/" + path, "Chi2Irrational/" + path + ".lean", path + ".lean"]
        if not any(x in fileset or x in dirs for x in cands):
            bad.append(("file", c))
        checked += 1
        continue
    if not re.fullmatch(r"[A-Za-z0-9_.']+", c):
        continue
    if c == "Chi2Irr":
        continue
    if re.fullmatch(r"[A-Z][A-Za-z0-9]*", c) and ("Chi2Irrational/" + c + ".lean") in fileset:
        checked += 1
        continue
    if "." not in c and "_" not in c and not c[0].isupper():
        continue
    short = c.split(".")[-1]
    hits = decls.get(short, [])
    want = "Chi2Irr." + c
    ok = any(full == want or full == c for full, _ in hits)
    checked += 1
    if not ok:
        bad.append(("decl", c, [h[0] for h in hits][:4]))

print(f"commit {COMMIT}: checked {checked} tokens, {len(bad)} problems")
for b in bad:
    print("  ", b)
