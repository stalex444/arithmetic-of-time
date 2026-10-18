# The Arithmetic of Time — paper, version 2

`arithmetic-of-time.tex` is the LaTeX source of the companion paper and
`arithmetic-of-time.pdf` the compiled paper (50 pages). The source is
self-contained (amsart, `thebibliography`, `figure.png` alongside); compile
with any standard distribution,

```
pdflatex arithmetic-of-time.tex
pdflatex arithmetic-of-time.tex   # second pass for cross-references
```

or `tectonic arithmetic-of-time.tex`.

The paper states what the repository proves, at its honest tier:
*kernel-verified* results carry their Lean declaration names, classical
results are *cited*, computations are labeled *computed*, and the
identification of this arithmetic with time is stated once, in Section 1, and
kept distinct from the theorems. Appendix A gives the tier of every claim.
Every declaration name in the paper exists in the Lean sources of the commit
cited for it: this repository's names in its version-2 sources, a sibling
entry's names at the commit given in the bibliography. Appendix B lists the
three compared theorems of `../comparator.json` (the registered record of
PALOMAR-2026-08-19-000006 at `c48eb12`, unchanged), the five theorems
registered separately as PALOMAR-2026-10-18-000019 (proved here in
`../Supplement.lean`, not compared here), and the other results of version 2,
which are public and not compared.

## Principal changes from version 1 (15 August 2026)

- **New results.** Section 8: on at most three letters the Padovan
  substitution and its mirror are the only substitutions whose incidence
  matrix has the least Pisot eigenvalue, and both are chiral; Siegel's bound
  is proved in degree at most three (not new). Section 9.2: the exact
  orientation threshold, four letters. Section 10: the forced rate and the one
  bit. Section 11: the twelve-letter substitution for `ρQ` and its chirality.
  Section 12: the chiral history in Lorentzian signature, cited from a
  registered sibling entry. Remark 6.10: the distinguished slope `β` is
  irrational (`Time.beta_irrational`).
- **Facts that moved.** Irreversibility is located in the handedness of the
  settled word, not in the contraction, whose inverse is equally exact; the
  text that placed it in the contraction is corrected. Statements that the
  irrationality of `β` and Siegel's theorem in low degree are unformalized are
  updated. The Lean pin is now `leanprover/lean4:v4.35.0-rc2` with Mathlib
  `065356127b1d`. The diffraction scaling table is taken at the word's own
  peak `p = β`; the peaks at `1 + β` and `2 + 2β` belong to the integer gap
  lattice.
- **Added.** The identification paragraph in Section 1, the literature on
  the arrow of time and on handedness, Appendices A–C; the bibliography now has 60
  entries. Sections 5–7 are reordered (chain, word, spectral).
