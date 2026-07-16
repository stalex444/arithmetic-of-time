"""Render figure.png — three-panel diffraction comparison (crystal / mechanical
word / gas) with an N-scaling inset. Requires numpy + matplotlib.

Run:  python3 make_figure.py
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

from diffraction import beta, sets, S

N = 200000
xc, xg, xq = sets(N)
pos = sorted({round(m + n * beta, 6) for m in range(4) for n in range(-3, 4)
              if 0.05 < m + n * beta < 3.2})
Sc = np.array([S(xc, 2*np.pi*beta*p)/N for p in pos])
Sq = np.array([S(xq, 2*np.pi*beta*p)/N for p in pos])
Sg = np.array([S(xg, 2*np.pi*beta*p)/N for p in pos])

# N-scaling at the crystal-forbidden incommensurate peak 1 + beta
kb = 2*np.pi*beta*(1+beta)
Ns = [10000, 30000, 100000, 300000, 1000000]
qN, gN = [], []
for Nn in Ns:
    c, g, q = sets(Nn)
    qN.append(S(q, kb)); gN.append(S(g, kb))

fig = plt.figure(figsize=(7.6, 8.0))
gs = fig.add_gridspec(3, 1, hspace=0.42, top=0.905, bottom=0.24, left=0.11, right=0.97)
pos = np.array(pos)
panels = [("Crystal — periodic lattice", Sc, "#2a6fdb", "peaks only at integers"),
          ("Mechanical (Sturmian) word — slope β", Sq, "#d1552a", ""),
          ("Gas — Poisson point set", Sg, "#8a8a8a", "flat floor, no peaks")]
for i, (ttl, Sv, col, note) in enumerate(panels):
    ax = fig.add_subplot(gs[i])
    ax.vlines(pos, 0, Sv, color=col, lw=1.8)
    ax.axhline(0, color='#cccccc', lw=0.6)
    ax.set_ylim(0, 1.08); ax.set_xlim(0, 3.15)
    ax.set_title(ttl, fontsize=11, loc='left', pad=4)
    ax.text(0.985, 0.86, note, transform=ax.transAxes, ha='right', va='top',
            fontsize=8.5, color='#555')
    ax.set_ylabel("$S(k)/N$", fontsize=9)
    if i < 2: ax.set_xticklabels([])
    ax.tick_params(labelsize=8)
    for s_ in ('top', 'right'): ax.spines[s_].set_visible(False)
fig.axes[-1].set_xlabel(r"reciprocal position   $k\,/\,2\pi\beta$", fontsize=10)

# inset: N-scaling in the word panel
axm = fig.axes[1]
ins = axm.inset_axes([0.50, 0.50, 0.36, 0.44])
ins.loglog(Ns, qN, 'o-', color="#d1552a", ms=3.5, lw=1.3, label="word")
ins.loglog(Ns, gN, 's-', color="#8a8a8a", ms=3, lw=1.0, label="gas")
ins.loglog(Ns, [qN[0]*n/Ns[0] for n in Ns], '--', color="#999", lw=0.9)
ins.set_title(r"peak at $1{+}\beta$ vs $N$", fontsize=7.5, pad=2)
ins.tick_params(labelsize=6.5); ins.legend(fontsize=6, loc='upper left', frameon=False)
ins.text(0.5, 0.05, r"$\propto N$ = Bragg", transform=ins.transAxes, fontsize=6,
         color="#666", ha='center')

fig.suptitle("Diffraction of the mechanical word: quasicrystalline order",
             fontsize=13, y=0.965)
cap = ("Structure factor of three point sets at identical density $\\beta = 0.4368$ (any irrational slope behaves "
       "the same). The mechanical word $m(n)=\\lfloor(n{+}1)\\beta\\rfloor-\\lfloor n\\beta\\rfloor$ has a pure-point "
       "spectrum — sharp Bragg peaks at the incommensurate module $m+n\\beta$, forbidden to the crystal and absent "
       "in the gas. Inset: the incommensurate peak grows $\\propto N$, a genuine Bragg peak. A mechanical word is a "
       "regular model set, so pure-point diffraction is a theorem (Hof 1995; Baake–Grimm 2013); this figure is the "
       "computation, not the proof.")
fig.text(0.5, 0.155, cap, ha='center', va='top', fontsize=7.8, wrap=True, linespacing=1.5)

fig.savefig("figure.png", dpi=300)
print("saved: figure.png")
print("word peak intensities S/N at incommensurate positions:",
      [f"{p:.3f}:{s:.2f}" for p, s in zip(pos, Sq)
       if abs(p - round(p)) > 1e-6 and s > 0.05])
