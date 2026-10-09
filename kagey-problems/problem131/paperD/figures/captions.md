# Figure captions for Paper D

Figure 1 is the program figure `program_D.pdf` in the `figures` folder of Problem 131, that is
`../../figures/program_D.pdf` from here. It is made by `../../figures/make_program_figure.py`, not
here, and the paper includes the shared file directly with
`\includegraphics[width=0.8\textwidth]{../figures/program_D}` (the path is relative to `paperD`), so
there is no copy in this folder. It is in the introduction with label `fig:program` and the caption
"The crossing on each model's switching scale against $L=\log N$ (a), and the heavy-tailed exponent $e(\alpha)=1-\alpha+1/\alpha$ of this paper for a stationary start (b). The scale is $T$ for Papers~A to~C, $x=N\varepsilon$ for the elephant walk (drawn through the root $g_N$ of Theorem~\ref{thm:erw-crossing}), and the expected number $H_N-1$ of switches at the fixed-start crossing $c=1$ for the aging walk. The curves of this paper are in bold, and a version of this figure also appears in Paper~C."

Figures 2 and 3 are made by `make_figures.py` in this folder. Each is 6.4 in wide. Figure 2 is
included with `\includegraphics[width=\textwidth]{figures/shape}` and Figure 3 at its natural size with
`\includegraphics{figures/heavy}`. The script also makes `crossing.pdf`, a figure of the elephant
crossing that the paper no longer prints (Table 1 has its numbers).

## Figure 2, `shape.pdf`, label `fig:shape`, in Section 3.2 before Theorem 3.5

The elephant walk at its crossing. (a) The law $P_N$ at $N=3200$ and its crossing $x=11.5468$, divided by the end $E_N$. The center equals the end, and the law rises from each end to a mode and falls to the center. The inset shows the last 60 bins, with dots at bins $N$, $N-1$ and $N-2$. The end is below its neighbor, and the modes are 25 steps from each end (dashed). (b) The law of $M_N$, scaled as $xf_N(m)$, against $\lambda_m=(m-x\log x)/x$, with the Landau density $f_L$. The dotted line is its mode $\lambda_0$. (c) The tail $P_N(N-m)$ divided by $x/(2m^2)$. The dashed line is the limit 1 of Theorem~\ref{thm:profile}, and the dotted curves are the heuristic correction $1+x(2\log m+2\gamma-3)/m$ for $2x\log x\le m\le N/x$. The rise of the $N=3200$ curve near $m=N/2$ is the mirror term $f_N(N-m)$. At $N=10^6$ we use $x=g_N=22.4407$.

## Figure 3, `heavy.pdf`, label `fig:heavy`, in Section 4 before Corollary 4.5

Alternating runs with a stationary start. (a) $R_N/(C(\alpha)N^{e(\alpha)})$ for even $N$ from 100 to $10^5$, with the entries of Table~\ref{tab:heavy} as dots. (b) $R_N$ for $\alpha=1.5,1.55,1.58,1.59$ below $\varphi$. Each curve crosses 1 once on $10\le N\le3\cdot10^4$, at $N^*(\alpha)$ (circles).
