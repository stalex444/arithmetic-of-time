"""Diffraction of the mechanical word — numerical companion to MechanicalWord.lean.

Computes the structure factor S(k) = |sum_j e^{i k x_j}|^2 / N for three point
sets at identical density beta:

  crystal  : the periodic lattice  x_n = n / beta
  word     : the mechanical (Sturmian) word m(n) = floor((n+1)beta) - floor(n beta),
             laid out as positions via cumulative gap sums
  gas      : a Poisson process of the same density

The mechanical word shows sharp Bragg peaks at the incommensurate module
m + n*beta — positions forbidden to any periodic crystal and absent in the
gas — and the intensity of the crystal-forbidden peak grows proportionally
to N (a genuine Bragg peak; the gas stays O(1)).

This is computation, not proof. The underlying fact — a mechanical word is a
cut-and-project (regular model) set, and regular model sets have pure-point
diffraction — is a theorem of the literature (Hof 1995; Schlottmann 2000;
Baake & Grimm, *Aperiodic Order*, CUP 2013).

Run:  python3 diffraction.py        (requires numpy)
"""

import numpy as np

beta = 0.4367860016          # an irrational slope; any irrational works
sp = 1.0 / beta              # mean spacing: identical density for all three sets
rng = np.random.default_rng(0)


def sets(N):
    xc = np.arange(N) * sp                          # crystal
    xg = np.cumsum(rng.exponential(sp, N))          # gas (Poisson)
    kk = np.arange(N + 1)
    g = 1.0 + np.diff(np.floor(kk * beta))          # gaps from the mechanical word
    g *= sp / g.mean()
    xq = np.cumsum(g)[:N]                           # the word, as positions
    return xc, xg, xq


def S(x, k):
    """Structure factor |sum e^{ikx}|^2 / N."""
    return abs(np.exp(1j * k * x).sum()) ** 2 / len(x)


if __name__ == "__main__":
    N = 200000
    xc, xg, xq = sets(N)

    # reciprocal positions p = m + n*beta   (physical wavenumber k = 2*pi*beta*p)
    pos = sorted({round(m + n * beta, 6) for m in range(4) for n in range(-3, 4)
                  if 0.05 < m + n * beta < 3.2})
    print(f"N = {N},  beta = {beta}")
    print(f"{'k/u = m+nb':>11} | {'crystal':>9} | {'word':>9} | {'gas':>6} |")
    print("-" * 55)
    rows = []
    for p in pos:
        k = 2 * np.pi * beta * p
        c, q, g = S(xc, k), S(xq, k), S(xg, k)
        rows.append((p, c, q, g))
        tag = "integer" if abs(p - round(p)) < 1e-6 else "INCOMMENSURATE"
        print(f"{p:>11.4f} | {c:>9.0f} | {q:>9.0f} | {g:>6.2f} | {tag}")

    # N-scaling at the strongest crystal-forbidden (incommensurate) peak
    inc = sorted([(q, p) for p, c, q, g in rows if abs(p - round(p)) > 1e-6],
                 reverse=True)
    _, pbest = inc[0]
    kb = 2 * np.pi * beta * pbest
    print(f"\nN-scaling at k/u = {pbest:.4f} (a peak the crystal cannot have):")
    print(f"{'N':>8} | {'crystal':>8} | {'word':>10} | {'gas':>6}")
    for Nn in [25000, 100000, 400000]:
        c, g, q = sets(Nn)
        print(f"{Nn:>8} | {S(c, kb):>8.1f} | {S(q, kb):>10.1f} | {S(g, kb):>6.2f}")
    print("Bragg: the word's peak grows ~ N. Gas: O(1). Crystal: nothing there.")
