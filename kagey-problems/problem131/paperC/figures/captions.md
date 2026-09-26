# Captions for the Paper C figures

Each caption is written in LaTeX and can be pasted into `\caption{...}`. The figures are made by
`make_figures.py` in this folder. Paper C uses `fig_cycles` and `fig_planar` as Figures 2 and 3. Figure 1 is the program figure
`program_C.pdf` in `../../figures/`, with its caption in `../../figures/program_captions.md`.

## Figure 2, `fig_cycles` (label `fig:cycles`, Section 3)

(a) The points $(\lambda_F,\lvert F\rvert-1)$ of the arcs of the 6-cycle and of $C_6$,
with the lower-left boundary of their hull. The numbers beside the edges are the switch values
$\tau_i$ of Theorem~\ref{thm:hull}. The winners (filled) are the arcs of $1$ to $4$ states and
$C_6$, and the arc of $5$ states (open) never wins. (b) The support size of the exact mode on
$C_5$ with the uniform start, against $T$, at $N=40$ and $N=72$. The mode skips the arc of $4$
states. The triangles mark the first-order switch points $\tau_i\log N$ with $\tau_i=1$,
$1+\sqrt2$ and $2+\sqrt2$ (Table~\ref{tab:outcomes}).

## Figure 3, `fig_planar` (label `fig:planar`, Section 6)

(a) The exact crossing of the planar walk with $(r,s)=(0.1,1)$, written as $sT^*_N-z_N$, for
$N=40,80,\dots,10240$. Here $z_N=N(1-p_N)$ is the crossing of Paper~A. The dashed curve is
$-\log2+\log2/(2L)$ from Theorem~\ref{thm:planar-rev}(c), and the dotted line is its limit $-\log2$.
(b) The zero-turn share $2S_N(u^*_N)$ of the origin mass at the crossing. It tends to $1$ for $s>2r$
and to $0$ for $s<2r$ (Theorem~\ref{thm:planar-first}), and to $2\sqrt2/(\sqrt2+\sqrt5)=0.7749$ at
the switch $s=2r$ (Remark~\ref{rem:planar-turns}). For $(r,s)=(1,0)$ there are no reversals and the
share is $0$ for every $N$. The pair $(0.3,1)$ was computed up to $N=640$.

## No longer used in Paper C

The files `fig_window` and `fig_sticky` stay in this folder, but Paper C no longer includes them.
`fig_window` may move to Paper B. Their last captions follow, without cross-references.

`fig_window`. (a) The lines $\ell_F(t)$ of the tie window on $K_3$ with the start
$(\frac12,\frac12,0)$. The vertex $\{3\}$ has no start mass and is not admissible. The upper envelope
is bold, and the edge window $(-0.4674,-0.4413)$ is shaded. (b) The ends $t_{ve}$ and $t_{ef}$ of the
window at $N=10^6,10^8,\dots,10^{20}$, computed from the exact face maxima, against $(\log L)/L$. The
stars are the limits from (a). The dotted curve solves
$T+\frac12\log T=L+\frac12\log\frac\pi8+\frac1{8T}$ for the left end. At $N=10^{20}$ the window is
$(-0.43825,-0.41345)$.

`fig_sticky`. The probability $\Prob_\omega(D)$ that a random sticky kernel on $3$ states with
uniform base weights has a direct jump, against the concentration $\omega$. The open circles are
Monte Carlo estimates with $10^6$ draws, and their error bars of one standard error are smaller than
the circles. The filled squares are quadrature values for $\omega\ge100$. The dotted line is the
limit $\frac14$ as $\omega\to0$, and the dashed line is the asymptote $3\sqrt3/(8\pi\omega)$.
