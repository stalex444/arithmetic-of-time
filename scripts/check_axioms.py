#!/usr/bin/env python3
"""Axiom audit: verify every theorem/lemma in the repository depends only on
{propext, Classical.choice, Quot.sound} — the claim the README's Rigor note
makes — and that no `sorry` or `native_decide` appears anywhere.

A green `lake build` alone certifies compilation, not the axiom footprint; a
custom axiom or a native_decide would still build green. This script closes
that gap, in CI and locally:

  python3 scripts/check_axioms.py

It (1) greps the sources for sorry/native_decide/axiom declarations,
(2) enumerates every theorem/lemma by parsing the sources (the same regex
family as the private tooling), (3) generates AxiomAudit.lean containing one
`#print axioms` per declaration, (4) elaborates it with `lake env lean`, and
(5) fails unless every declaration's reported axioms are within the allowed
set. Exit 0 = the Rigor note is true of this commit.
"""
import os
import re
import subprocess
import sys

os.chdir(os.path.dirname(os.path.abspath(__file__)) + "/..")

# Every module except Challenge (which states the compared theorems with
# `sorry`, by the registry's challenge format); Solution is included.
MODULES = ["Solution", "Irreducibility", "FieldNorm", "Settling",
           "SettlingReplica", "ConstantChain", "AlgebraicIntegers",
           "MechanicalWord", "PisotBoundary", "Chirality", "OriginDefect",
           "PdtIrreducible", "PdtSalemFamily", "PdtPisotBoundary",
           "PdtRulerMinpoly", "PdtChirality", "PdtFourTickThreshold",
           "PdtArrowRate", "PdtCommitment", "PdtNormFloor", "PdtMirrorTensor",
           "PdtRhoQChirality", "PdtCharpolyTensor", "PdtSignature",
           "PdtSignatureRho", "PdtTraceLink", "PdtTraceSignature",
           "PdtTraceCompositum", "PdtJointClock", "PdtJointClockIrreducible",
           "PdtRecordBoundary", "PdtQuarticSeparation",
           "PdtQuarticWindowDynamics", "PdtCubicQuarticBridge", "Sturmian",
           "BetaIrrational", "PdtMahler", "PdtMahlerBox", "PdtMahlerMain",
           "PdtMahlerTheta", "PdtMahlerWindow", "SlowestClock",
           "Supplement"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([^\s:({\[]+)")
NS = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
NS_END = re.compile(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_'.]*)")
BANNED_SRC = re.compile(r"^\s*(axiom\s|.*\bnative_decide\b|.*\bsorry\b)")


def blank_comments(text):
    """Replace the contents of comments (nested block comments and line
    comments) by spaces, keeping newlines, so that prose in a docstring that
    happens to begin with the word `theorem` is not parsed as a declaration."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def decls_of(path):
    stack, names, private = [], [], set()
    raw = open(path, encoding="utf-8").read()
    for ln in raw.split("\n"):
        if BANNED_SRC.match(ln) and "-- audit-ok" not in ln:
            print(f"BANNED CONSTRUCT in {path}: {ln.strip()[:100]}")
            sys.exit(1)
    for ln in blank_comments(raw).split("\n"):
        m = NS.match(ln)
        if m:
            stack.append(m.group(1))
            continue
        m = NS_END.match(ln)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = DECL.match(ln)
        if m:
            full = ".".join(stack + [m.group(2)]) if stack else m.group(2)
            if "private" in ln.split(m.group(1))[0]:
                private.add(full)
            else:
                names.append(full)
    return [n for n in names if n not in private]


def main():
    all_decls = []
    for mod in MODULES:
        path = f"{mod}.lean"
        if not os.path.exists(path):
            print(f"MISSING MODULE: {path}")
            return 1
        all_decls += decls_of(path)
    print(f"auditing {len(all_decls)} theorems/lemmas across {len(MODULES)} modules")

    with open("AxiomAudit.lean", "w", encoding="utf-8") as f:
        for mod in MODULES:
            f.write(f"import {mod}\n")
        f.write("\n")
        for d in all_decls:
            f.write(f"#print axioms {d}\n")

    r = subprocess.run(["lake", "env", "lean", "AxiomAudit.lean"],
                       capture_output=True, text=True)
    out = r.stdout + r.stderr
    os.remove("AxiomAudit.lean")
    if r.returncode != 0:
        print("AUDIT FILE FAILED TO ELABORATE:\n" + out[-3000:])
        return 1

    checked = bad = 0
    for line in out.split("\n"):
        # names may contain primes (`foo'`), so the name group is greedy and
        # the line is anchored at both ends
        m = re.match(r"^'(.+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", line.strip())
        if not m:
            continue
        checked += 1
        axs = {a.strip() for a in (m.group(3) or "").split(",") if a.strip()}
        extra = axs - ALLOWED
        if extra:
            bad += 1
            print(f"  VIOLATION {m.group(1)}: {sorted(extra)}")
    print(f"checked {checked} declarations; violations: {bad}")
    if checked < len(all_decls):
        print(f"COVERAGE GAP: {len(all_decls)} declared but only {checked} reported — failing.")
        return 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
