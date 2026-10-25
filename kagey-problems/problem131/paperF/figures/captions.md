# Captions

## atlas.pdf (`make_atlas_figure.py`)

Caption in the paper (sec_intro.tex):

(a) The law $P_N(k)$ for $N=5000$, run lengths with $f(n)\propto n^{-5/2}$ for both signs and a fresh plus start, on a logarithmic scale, with the four pieces of Theorems~\ref{thm:bulk} and~\ref{thm:bigjump}. The two ends of the horizontal axis are stretched.
(b) The position $j^*_N$ of the interior minimum near the plus end against $N$, on logarithmic axes, with the law of Theorem~\ref{thm:antimode} and the refined prediction with $C(j)$ from Theorem~\ref{thm:second-order}.
Section~\ref{sec:verify} describes the computations.

Full description (for Section 7):

The zeta law $f_\pm(n)=n^{-5/2}/\zeta(5/2)$ for both signs ($\alpha_\plus=\alpha_\minus=1.5$, $p=1/2$), fresh plus start.
(a) The exact law $P_N(k)$ at $N=5000$ (thick grey, computed by the run recursion described in Section~\ref{sec:verify}, from the identities of Section~\ref{sec:identities}, with relative error below $3\cdot10^{-9}$) and its four pieces, each drawn on its zone and the adjacent junction band.
The bulk profile $B_N^{-1}h_N((k-pN)/B_N)$, with $h_N$ obtained by numerical inversion of its characteristic function, is drawn on $|k-pN|\le4B_N$ ($B_N=74.1$).
The big-jump kernel $G^{(\plus)}_N$ of~\eqref{eq:G} and its mirror at the minus end are drawn on $|k-pN|\ge3B_N$, $\min(k,N-k)\ge B_N$.
The boundary kernels $T_\plus(N)u_\minus(N-k)$ and $T_\minus(N)u_\plus(k)$ are drawn on $1\le\min(k,N-k)\le2B_N$, and the dot is the atom $P_N(N)=T_\plus(N)$. The minus atom $P_N(0)$ vanishes for a fresh plus start.
The light bands are the junctions, each of width $B_N$.
The horizontal scale is linear on each of $[0,250]$, $[250,4750]$ and $[4750,5000]$, with the two end stretches enlarged (dotted lines), which causes the kinks of the curves at $k=250$ and $k=4750$.
The maximal relative errors on the zones $|k-pN|\le3B_N$, $\{|k-pN|\ge4B_N,\ \min(k,N-k)\ge2B_N\}$ and $1\le\min(k,N-k)\le B_N$ are $0.071$, $0.38$ and $0.094$, and the atom is exact.
(b) Both axes logarithmic. The antimode $j^*_N$, the minimizer of $P_N$ over $[pN,N]$ read from the plus end, for $N=600,1200,2400,4000,8000$ (circles, each certified to be separated from the value at every other point of $[pN,N]$ by more than the numerical error), the law $T_\minus^{-1}(2\alpha_\plus s/N)$ of Theorem~\ref{thm:antimode}(a) with $T_\minus$ extended to real arguments by the Hurwitz zeta function (dashed), and the refined prediction $\arg\min_j[u_\minus(j)+C(j)/N]$ of Theorem~\ref{thm:antimode}(a), with $C(j)$ from~\eqref{eq:Cj} (steps).
