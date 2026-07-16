# The Arithmetic of Time — paper source

`arithmetic-of-time.tex` is the LaTeX source of the companion paper. It is
self-contained (amsart, `thebibliography`, `figure.png` alongside): compile
with any standard distribution,

```
pdflatex arithmetic-of-time.tex
pdflatex arithmetic-of-time.tex   # second pass for cross-references
```

or upload the two files in this folder to Overleaf.

The paper states exactly what the repository proves, at its honest tier:
*kernel-verified* results carry their Lean declaration names, classical
results are *cited*, and the diffraction picture is labeled *computed*.
Every declaration name appearing in the paper exists in the Lean sources at
the commit that ships alongside it.
