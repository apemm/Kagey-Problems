# Captions for the current merged Paper C

The manuscript currently includes the four figures below. All captions are transcribed
from the current manuscript sources, using stable labels rather than figure or theorem
numbers. The complete-graph inclusion and its final caption were added by the manuscript
owner; this file records that included version. All four figures have white backgrounds.

## The composition simplex (`fig:simplex`)

Source: `../sec_model.tex`. Asset: `fig_simplex.pdf`. Generator: `make_simplex_figure.py`.

```latex
\caption{The exact law of the composition for the path $1-2-3$ (rate $1$ on
each edge, uniform start, $N=90$), on the simplex of visit fractions. The
faces are drawn apart. The triangle holds the compositions that use all three
states, each band holds the compositions that use two states, and each disk is
the composition that spends all $N$ steps in one state. The color is the probability
of a composition relative to the mode, the thin lines are spaced by a factor
of ten, and the rings mark the modes. (a) For small $T$ the mode is at an end
of the path. (b) Then it sits on a band, that is, on a pair of neighbors.
(c) Then it is inside. The dashed band is the pair $\{1,3\}$, which the chain
cannot use without visiting $2$, so it has probability zero. Here $\lambda_F$
is $1$ for an end, $(3-\sqrt5)/2$ for a pair of neighbors and $0$ for all
three states, so to first order the mode moves at $\tau=(1+\sqrt5)/2$ and at
$\tau=(3+\sqrt5)/2$, that is, at $T=7.3$ and $T=11.8$. At $N=90$ it moves
near $T=4.9$ and $T=8.5$. Corrections of this size are the subject of
Section~\ref{sec:secondorder}.}
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


## Cycle hull and finite-size modes (`fig:cycles`)

Source: `../sec_firstorder.tex`. Asset: `fig_cycles.pdf`. Generator: `make_figures.py`.

```latex
\caption{(a) The points $(\lambda_F,\lvert F\rvert-1)$ of the arcs of the 6-cycle $C_6$ and of $C_6$ itself,
with the lower-left boundary of their hull. The numbers beside the edges are the switch values
$\tau_i$ of Theorem~\ref{thm:hull}. The winners (filled) are the arcs of one to four states and
$C_6$, and the arc of five states (open) never wins. (b) The support size of the exact mode on
$C_5$ with the uniform start, against $T$, at $N=40$ and $N=72$. The mode skips the arc of four
states. The triangles mark the first-order switch points $\tau_i\log N$ with $\tau_i=1$,
$1+\sqrt2$ and $2+\sqrt2$.}
```


## Complete graph: no field versus a weak field (`fig:complete-envelope`)

Source: `../sec_intro.tex`. Asset: `fig_complete_envelope.pdf`. Generator: `make_complete_envelope.py`.

Included immediately after Theorem A in the introduction. Exact current inclusion block:

```latex
\begin{figure}[H]
\centering
\includegraphics[width=\textwidth]{fig_complete_envelope}
\caption{Support selection on the complete graph with four states, unit rates
and uniform start, in the window $T=\log N-\frac12\log\log N+t$.
Thin lines are limiting log face maxima relative to an untilted vertex,
and the bold curve is their upper envelope.
(a) Without a field the winner jumps from one state to all four.
(b) Weighting a composition by $e^{\langle\xi,n\rangle/N}$, with
$\xi_i=-(i-1)^2$, lets every size win in turn. The scores and marked
crossings are derived in Section~\ref{sec:complete}. Field weights are
unnormalized, and marked ties concern the limit, not finite-$N$ equalities.}
\label{fig:complete-envelope}
\end{figure}
```

### Complete-graph source, reproduction, and interpretation

`fig_complete_envelope.pdf` is entirely vector. `fig_complete_envelope.png` is its preview;
`fig_complete_envelope.json` records constants, crossings, and scientific checks.
Run `python -B make_complete_envelope.py` from this directory (or give its absolute path).
It uses NumPy and Matplotlib, with no TeX installation, SciPy, simulation, or DP required.
It writes solely in this directory and does not load or regenerate computational data.

The scores are exactly the affine functions in `eq:weakfield-lines`:
$\ell_k(t)=(k-1)t+\log D_k+k^{-1}\sum_{i=1}^k\xi_i$,
where $D_1=1$ and $D_k=k^{k+1/2}(4\pi)^{-(k-1)/2}$.
For the displayed field, the exact limiting crossings are
$t_k=\log D_k-\log D_{k+1}+(4k-1)/6$.
Their rounded values are $(0.032644,0.319904,0.705664)$; the no-field transition is
$a_4=-0.8139294182\ldots$. The PDF's tie markers do not assert finite-$N$ ties.

Both panels use the uniform start. A nonuniform start instead contributes
$\log(\mu(S)/|S|)$ to the score of a support $S$, up to a common additive constant
(`cor:start-modes`); the field contributes $|S|^{-1}\sum_{i\in S}\xi_i$
(`cor:weakfield-phases`). These are different perturbations.

Print/accessibility: native width 400 PDF points (approximately the current EJP text width),
8.5-point base labels, embedded TrueType fonts, distinct solid/dashed/dotted/dash-dot candidate
lines, black envelope, labeled tie markers, and numeric winner strips. The answer does not
depend on recognizing colors. PDF render and grayscale/bilevel print previews are in `qa/`.
The math-script glyphs in subscripts are naturally smaller than the base labels.

Suggested text alternative: On the complete graph with four states and a uniform start,
the limiting upper envelope selects sizes one and four when the field is zero. With field
values zero, minus one, minus four and minus nine, it selects the nested supports of sizes
one, two, three and four, with limiting transition coordinates approximately 0.032644,
0.319904 and 0.705664.

## Existing start-law asset, not currently included

`fig_window.pdf` and `.png` still illustrate the current start-law example
`ex:K3-start`, with start $(1/2,1/2,0)$ on $K_3$. The analytic panel's endpoints are
$a_2=\frac12\log(\pi/8)$ and $t_{\rm ef}=\frac12\log(32\pi/243)$, with width
$\log(16/(9\sqrt3))\simeq0.026058$. This is a start-law effect, with no field.
It belongs to the merged complete-graph discussion.

The right panel uses cached numerical estimates from `../data/figdata_window.json`.
The generator uses a truncated run expansion and continuous numerical optimization for the
full-face maximum; the figure does not itself establish certified exact lattice maxima.
If this asset is added later, its numerical caption needs that distinction. The complete-graph
comparison now included is sufficient; no second new figure is recommended.

Historical planar/sticky captions have been removed from this current-paper caption file.
No archived figure asset has been altered here.
