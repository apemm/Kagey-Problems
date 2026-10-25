# Captions for the current merged Paper C

The manuscript currently includes the three figures below: the complete-graph envelope
(Figure 1), the composition simplex (Figure 2) and the worked 4-cycle (Figure 3). All captions
are transcribed from the current manuscript sources, using stable labels rather than figure or
theorem numbers. All three figures have white backgrounds. The cycle-hull figure
(`fig:cycles`) was cut on October 24, 2026 (audit 20), and its asset is listed at the end.

## The composition simplex (`fig:simplex`)

Source: `../sec_model.tex`. Asset: `fig_simplex.pdf`. Generator: `make_simplex_figure.py`.

```latex
\caption{The exact law of the composition for the path $1-2-3$ (rate $1$ on
each edge, uniform start, $N=90$) on the simplex of visit fractions, with the
faces drawn apart. The triangle holds the compositions with three states, each
band those with two, and each disk a vertex. The color is the probability
relative to the mode, the thin lines are spaced by a factor of ten, and the
rings mark the modes. The mode is (a) at an end of the path, (b) on a pair of
neighbors and (c) inside. The dashed band $\{1,3\}$ has probability zero}
```


## The worked 4-cycle (TikZ) (`fig:C4worked`)

Source: `../sec_firstorder.tex`. Drawn directly in the manuscript with TikZ; no external figure file.

```latex
\caption{The 4-cycle. (a) The exponents $\Phi_\tau(F)=\tau\lambda_F+\lvert
F\rvert-1$ of the four kinds of faces against $\tau$, and their lower envelope
(bold). The mode sits on the face whose line is lowest, namely a vertex for
$\tau<1$, an adjacent pair for $1<\tau<2$ and the whole cycle for $\tau>2$. The
dashed line of the arc of three states is never lowest. (b) The same faces as points
$(\lambda_F,\lvert F\rvert-1)$, with the lower-left boundary of their convex
hull. The gray numbers are minus the slopes of its edges, the values of $\tau$
where the winner changes (Theorem~\ref{thm:hull}). The arc (open) lies above
the boundary.}
```


## Cycle hull and finite-size modes (`fig:cycles`), not included

Asset: `fig_cycles.pdf`. Generator: `make_figures.py`. Cut from `../sec_firstorder.tex` on
October 24, 2026 (audit 20), since the 4-cycle figure shows the same hull. Its last caption was

```latex
\caption{(a) The points $(\lambda_F,\lvert F\rvert-1)$ of the arcs of the 6-cycle $C_6$ and of $C_6$ itself,
with the lower-left boundary of their hull. The numbers beside the edges are the switch values
$\tau_i$ of Theorem~\ref{thm:hull}. The winners (filled) are the arcs of one to four states and
$C_6$, and the arc of five states (open) never wins. (b) The support size of the exact mode on
$C_5$ with the uniform start, against $T$, at $N=40$ and $N=72$. The mode skips the arc of four
states. The triangles mark the first-order switch points $\tau_i\log N$ with $\tau_i=1$,
$1+\sqrt2$ and $2+\sqrt2$.}
```


## Complete graph without a field (`fig:complete-envelope`)

Source: `../sec_intro.tex`. Asset: `fig_complete_envelope.pdf`. Generator: `make_complete_envelope.py`.

Included after Theorem C in the introduction. Exact current inclusion block:

```latex
\begin{figure}[t]
\centering
\includegraphics[width=0.62\textwidth]{fig_complete_envelope}
\caption{Support selection on the complete graph with four states, unit rates
and uniform start, in the window $T=\log N-\frac12\log\log N+t$.
Thin lines are limiting log face maxima relative to a vertex,
and the bold curve is their upper envelope. The winner jumps from one state
to all four at $t=a_4$. The scores are derived in Section~\ref{sec:complete},
and the marked tie concerns the limit, not a finite-$N$ equality}
\label{fig:complete-envelope}
\end{figure}
```

Change of October 24, 2026: the figure had a second panel, (b), with the weak field
$\xi_i=-(i-1)^2$, which let every size win in turn. The weak field was cut from the paper
(the proposition of Section 5.6 and Section 7.4), and the panel and its sentence in the
caption with it. The figure now has the single panel that was (a).

### Complete-graph source, reproduction, and interpretation

`fig_complete_envelope.pdf` is entirely vector. `fig_complete_envelope.png` is its preview, and
`fig_complete_envelope.json` records the constants, the crossing and the checks.
Run `python -B make_complete_envelope.py` from this directory (or give its absolute path).
It uses NumPy and Matplotlib, with no TeX installation, SciPy, simulation or DP required.
It writes only in this directory and does not load or regenerate computational data.

The scores are the lines $\ell_k(t)=(k-1)t+\log D_k$ of `cor:paperB` and
`thm:simplex-crossing`(ii), where $D_1=1$ and $D_k=k^{k+1/2}(4\pi)^{-(k-1)/2}$. The envelope
jumps from size 1 to size 4 at $a_4=-0.8139294182\ldots$ (`cor:simplex-modes`). The tie
marker does not assert a finite-$N$ tie.

Print and accessibility: native width 280 PDF points, included at 0.62 of the text width,
8.5-point base labels, embedded TrueType fonts, distinct solid, dashed, dotted and dash-dot
candidate lines, a black envelope, a labeled tie marker and a numeric winner strip. The answer
does not depend on recognizing colors. The previews in `qa/` are of the earlier two-panel
version.

Suggested text alternative: On the complete graph with four states and a uniform start,
the limiting upper envelope selects size one and then size four, with the jump at
approximately -0.814.

## Start-law asset, not included

`fig_window.pdf` and `.png` illustrate the start-law example on $K_3$ with start
$(1/2,1/2,0)$ (formerly `ex:K3-start`). That example was cut from the paper on October 24,
2026, with the rest of Section 7.3, so this asset belongs to no current statement. The
analytic panel's endpoints are $a_2=\frac12\log(\pi/8)$ and
$t_{\rm ef}=\frac12\log(32\pi/243)$, with width $\log(16/(9\sqrt3))\simeq0.026058$.

The right panel uses cached numerical estimates from `../data/figdata_window.json`.
The generator uses a truncated run expansion and continuous numerical optimization for the
full-face maximum, so the figure does not itself establish certified exact lattice maxima.

Historical planar/sticky captions have been removed from this current-paper caption file.
No archived figure asset has been altered here.
