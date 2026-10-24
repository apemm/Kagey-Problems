# Numbers and computational material removed from the proof sections

This file collects, word for word, every numerical statement that the 2026-10-24 revision
removed from Sections 1 to 7 of problem131_levy.tex, with its parameters, so that
Section 8 (sec_verify.tex) can report it. In the paper each removed passage is replaced
by the sentence "Section~\ref{sec:verify} reports the check." (or, for the figure, by
"Section~\ref{sec:verify} describes the computations.").

Labels that changed in the revision and that sec_verify.tex must follow:
- `lem:final-explicit` no longer exists. Its explicit identity is now `prop:final-run`,
  display `eq:final-explicit`, in sec_setting.tex.
- The recursion `eq:AB-recursion` and the cost count are no longer in the paper. They are
  reproduced in Section 5 below so that sec_verify.tex can state them (we suggest the names
  a_t(k), b_t(k), since A_N and B_N are the plus count and the bulk scale).
- `tab:antimode` is no longer defined in sec_shape.tex. The table is reproduced in Section 4
  below and should be placed in sec_verify.tex with that label.
- `prop:uniform-second` is now `thm:second-order`(b).
- `sec:second-order` still exists (the C(j)/j values were in that subsection).

All computations use the zeta law f(n)=n^{-5/2}/zeta(5/2) for both signs
(alpha_+ = alpha_- = 3/2, p = 1/2, mu = 1.947372, s = 3.894745) and a fresh plus start,
unless stated otherwise.

## 1. Figure 1 caption (old sec_intro.tex lines 46-57), removed details

The old caption read, verbatim:

```latex
\begin{figure}[t]
\centering
\includegraphics[width=\textwidth]{atlas}
\caption{(a) The law $P_N(k)$ for $N=5000$, run lengths with
$f(n)\propto n^{-5/2}$ for both signs, and a fresh plus start, on a
logarithmic scale, with the four pieces of Theorems~\ref{thm:bulk}
and~\ref{thm:bigjump} drawn separately. The horizontal axis is linear on
$[250,4750]$ and stretched on the last $250$ bins at each end, which makes
the two kinks. The shaded bands have width $B_N=74$ and mark the junctions
between the pieces. (b) The position $j^*_N$ of the interior minimum of
$P_N$ near the plus end against $N$, with the law
$T_\minus(j^*_N)\sim2\alpha_\plus s/N$ of Theorem~\ref{thm:antimode} and the
finite-$N$ prediction $\arg\min_j[u_\minus(j)+C(j)/N]$ of
Theorem~\ref{thm:second-order}. Section~\ref{sec:verify} describes the
computations.}
\label{fig:atlas}
\end{figure}
```

Removed details (the new caption keeps only the pieces and points to Section 8):
- "The horizontal axis is linear on $[250,4750]$ and stretched on the last $250$ bins at each
  end, which makes the two kinks."
- "The shaded bands have width $B_N=74$ and mark the junctions between the pieces."
  (atlas_pieces.json gives B_N = 74.1098.)
- Panel (b): "with the law $T_\minus(j^*_N)\sim2\alpha_\plus s/N$ of Theorem~\ref{thm:antimode} and the
  finite-$N$ prediction $\arg\min_j[u_\minus(j)+C(j)/N]$". The consistency audit (L6) notes that the
  argmin statement is Theorem~\ref{thm:antimode}(a), with $C(j)$ from Theorem~\ref{thm:second-order}.
- New in the caption: panel (b) has logarithmic axes. figures/captions.md has the full caption.

## 2. Remark rem:no-single-formula (old sec_bigjump.tex lines 752-757)

# Numbers removed from sec_bigjump.tex (Remark rem:no-single-formula)

Context: b_{+,N}=B_N, (LR), k = ceil(pN + K B_N) with K fixed; the limit of B_N G_N(k) is
alpha_+ (1-p)^{alpha_+} K^{-alpha_+-1}.

Verbatim removed text:

"For equal laws with $\alpha_\pm=1.5$ the ratio $h_N(K)/(\alpha_\plus(1-p)^{\alpha_\plus}K^{-\alpha_\plus-1})$
is $0.31$, $1.68$ and $1.09$ at $K=1$, $4$ and $16$. For the zeta law
$f_\sgn(n)=n^{-5/2}/\zeta(5/2)$ the exact ratio $P_N(k)/G_N(k)$ at these $K$ is
$0.354$, $1.482$ and $1.036$ at $N=1200$, and $0.337$, $1.538$ and $1.059$ at
$N=3000$. These move toward the limits, and at $N=3000$ they are still $7$ to $8$
percent off at $K=1$ and $K=4$."

Notes from the audits: referee recomputed the limit ratios as 0.3126, 1.6774, 1.0934 at K=1,4,16
(symmetric 3/2-stable density); "7 to 8 percent" corresponds to 7.8% and 8.3%. The exact ratios at
N=1200 and N=3000 have no data file in data/ (consistency audit M7).


## 3. After Corollary cor:stationary (old sec_preparation.tex lines 729-732)

# Numbers removed from sec_preparation.tex (after Corollary cor:stationary)

Original text, verbatim (it followed the reading of the three terms of kappa^st_+):

"We checked the corollary against the exact law for
the zeta law with $\alpha_\pm=\frac32$. At $N=2400$ the ratio of $P_N(N-j)/T_\plus(N)$ to
$\kappa^{\mathrm{st}}_\plus(j)$ is $1.0007$, $1.0031$ and $1.0098$ at $j=1$, $2$ and $5$, and
each deviation is about half of its value at $N=1200$."

Parameters: zeta law f_sgn(n)=n^{-5/2}/zeta(5/2) for both signs, stationary preparation
nu_sgn=T_sgn/s, kappa^st_+(j)=(2/s)(1+mu_+ u_-(j)), N=2400 (and N=1200 for the halving claim).
The replacement sentence in the paper: "Section~\ref{sec:verify} reports a check of part (c) against the exact law."


## 4. Section 6 (old sec_shape.tex): C(j)/j, the second-order renewal check, Table 1

# Numbers removed from sec_shape.tex (verbatim), for the verification section

## 1. After Theorem thm:second-order (old lines 433-437)

Context sentence kept in the paper: "The convergence of $C(j)/j$ is slow, since
$C(j)/j-2\alpha_\plus s/\mu_\minus^2$ is of the order of $jT_\minus(j)$ by~\eqref{eq:second-renewal} below."

Removed text:

For the zeta
law $f_\sgn(n)=n^{-5/2}/\zeta(5/2)$ on both sides the limit is $3.0811$, while
$C(j)/j$ equals $4.968$, $4.430$, $4.041$, $3.762$, $3.563$, $3.422$, $3.323$ at
$j=5,10,20,40,80,160,320$.

(Parameters: alpha_+ = alpha_- = 3/2, mu = 1.947372, s = 3.894745; limit 2 alpha_+ s/mu_-^2.)

## 2. After the second-order renewal theorem eq:second-renewal (old lines 500-502)

For the zeta law
$f_\minus(n)=n^{-5/2}/\zeta(5/2)$ the ratio of the two sides
of~\eqref{eq:second-renewal} is $0.978$, $0.994$ and $0.999$ at $j=40$, $160$
and $640$.

## 3. After the proof of Theorem thm:antimode (old lines 675-700), with Table tab:antimode

Removed paragraph (its first sentence is kept in the paper in shortened form):

The leading law $T_\minus(j^*_N)\sim2\alpha_\plus s/N$ is approached slowly,
because $C(j)/j$ converges slowly. The minimizer of $u_\minus(j)+C(j)/N$ is the
better prediction at moderate $N$. Table~\ref{tab:antimode} compares the two
with the exact law for the zeta law $f_\sgn(n)=n^{-5/2}/\zeta(5/2)$ on both
sides, computed by the recursion of Proposition~\ref{prop:final-run} in double
precision.

(Note: the recursion of the old Proposition prop:final-run, eq:AB-recursion, has been removed from
sec_setting; the lead editor records it separately. The new prop:final-run is the explicit form.)

Removed table:

```latex
\begin{table}[ht]
\centering\small
\begin{tabular}{@{}rrrrr@{}}
\toprule
$N$ & observed $j^*_N$ & refined $i_N$ & leading $\ell_N$ & $NT_\minus(j^*_N)/(2\alpha_\plus s)$\\
\midrule
600 & 7 & 7 & 10 & 1.534\\
1200 & 11 & 12 & 15 & 1.498\\
2400 & 19 & 20 & 23 & 1.282\\
4000 & 27 & 28 & 32 & 1.247\\
8000 & 44 & 45 & 50 & 1.186\\
\bottomrule
\end{tabular}
\caption{The antimode for the zeta law with $\alpha_\plus=\alpha_\minus=3/2$ and a
fresh plus start. The observed $j^*_N$ minimizes $P_N(N-j)$ over
$0\le j\le N/2$, the refined $i_N$ minimizes $u_\minus(j)+C(j)/N$, and the
leading $\ell_N$ is the smallest $j$ with $T_\minus(j)<2\alpha_\plus s/N$.}
\label{tab:antimode}
\end{table}
```

Note for the verification section: the caption's range $0\le j\le N/2$ equals the range
$0\le j\le(1-p)N$ of Theorem~\ref{thm:antimode} because $p=1/2$ for two equal laws. The
symbol $\ell_N$ clashes with $\ell=(v-p)/(1-p)$ of the infinite density; consider renaming it.
The certified list in the placeholder stopped at $N=4000$; the table and data include $N=8000$.


## 5. The run recursion and its cost (old Proposition prop:final-run, sec_setting.tex lines 420-497)

The old text, verbatim. In the revised paper the final-run identity is stated only in the
explicit form `eq:final-explicit`; A_t(k) equals rho^{(+)}_{t-k}(k) of `eq:rho-rep`.

```latex
The next identity isolates the final run. For a fresh plus start let
$A_t(k)$ be the probability that a plus run starts at slot $t+1$ and the first
$t$ slots contain exactly $k$ plus slots, and $B_t(k)$ the probability that a
minus run starts at slot $t+1$ and the first $t$ slots contain exactly $k$ plus
slots, with $A_0(0)=1$ and $B_0(0)=0$.

\begin{proposition}[the final-run identity]\label{prop:final-run}
For a fresh plus start and $0\le j\le N$,
\[
 P_N(N-j)=\sum_{t=j}^{N-1}A_t(t-j)\,T_\plus(N-t)+\sum_{m=1}^{j}B_{N-m}(N-j)\,T_\minus(m).
\]
The first sum is the event that the final run is a plus run, which then
starts after the $j$-th minus slot, and the second is the event that the final
run is a minus run of length $m\le j$. Moreover, with $A_t(k)=B_t(k)=0$ for $k<0$,
the functions $A$ and $B$ satisfy, for $t\ge1$ and $0\le k\le t$,
\begin{equation}\label{eq:AB-recursion}
 B_t(k)=\sum_{\ell=1}^{t}A_{t-\ell}(k-\ell)\,f_\plus(\ell),\qquad
 A_t(k)=\sum_{\ell=1}^{t}B_{t-\ell}(k)\,f_\minus(\ell).
\end{equation}
So a plus run of length $\ell$ that starts at slot $t+1$ turns $A_t(k)$ into a
contribution to $B_{t+\ell}(k+\ell)$, and a minus run of length $\ell$ turns $B_t(k)$
into a contribution to $A_{t+\ell}(k)$. Together with the identity above, this
computes the whole row $P_N(0),\dots,P_N(N)$ exactly in $O(N^3)$ arithmetic
operations.
\end{proposition}

\begin{proof}
We condition on the start of the final run, which is the run that contains slot $N$.
We use the run lengths and partial sums of the proof of
Proposition~\ref{prop:fresh-identity}. For $i\ge1$ let $E^\plus_i(t,k)$ be the event that
the $i$-th plus run starts at slot $t+1$ and the first $t$ slots contain exactly $k$
plus slots. The $i$-th plus run starts at slot $S^\plus_{i-1}+S^\minus_{i-1}+1$, and the
slots before it contain $S^\plus_{i-1}$ plus slots. So $E^\plus_i(t,k)$ is determined by
$X^\plus_1,\dots,X^\plus_{i-1}$ and $X^\minus_1,\dots,X^\minus_{i-1}$, and it is
independent of $X^\plus_i$. In the same way let $E^\minus_i(t,k)$ be the event that the
$i$-th minus run starts at slot $t+1$ and the first $t$ slots contain exactly $k$ plus
slots. It is determined by $X^\plus_1,\dots,X^\plus_i$ and
$X^\minus_1,\dots,X^\minus_{i-1}$, and it is independent of $X^\minus_i$. The events
$E^\plus_i(t,k)$ with $i\ge1$ are disjoint and their union is the event in the
definition of $A_t(k)$, so $A_t(k)=\sum_i\Prob(E^\plus_i(t,k))$. Likewise
$B_t(k)=\sum_i\Prob(E^\minus_i(t,k))$.

The final run starts at slot $t+1$ for exactly one $t\in\{0,\dots,N-1\}$. Suppose it is
the $i$-th plus run. It contains slot $N$ exactly when $X^\plus_i\ge N-t$, and then its
last $N-t$ slots up to slot $N$ are plus slots. So if the first $t$ slots contain $k$
plus slots, then $A_N=k+N-t$, and $A_N=N-j$ means $k=t-j$. This needs $t\ge j$. By
independence, the event that $A_N=N-j$ and the final run is a plus run starting at
slot $t+1$ has probability
\[
 \sum_{i\ge1}\Prob\bigl(E^\plus_i(t,t-j)\bigr)\,T_\plus(N-t)=A_t(t-j)\,T_\plus(N-t).
\]
Now suppose the final run is the $i$-th minus run and put $m=N-t$. It contains slot $N$
exactly when $X^\minus_i\ge m$. Then the slots $t+1,\dots,N$ are minus slots, so
$A_N=N-j$ means that the first $t$ slots contain $N-j$ plus slots. Since $N-j\le t$,
this needs $m\le j$. In the same way this case has probability
$B_{N-m}(N-j)\,T_\minus(m)$. Summing over the disjoint cases gives the identity. (For
$j=0$ the second sum is empty and only $t=0$ contributes, since a plus run that starts
at slot $t+1\ge2$ follows a minus slot. So $P_N(N)=T_\plus(N)$, as in
Proposition~\ref{prop:fresh-identity}.)

For the recursion let $t\ge1$. The runs alternate, so a minus run starts at slot $t+1$
exactly when slot $t$ is the last slot of a plus run. That plus run starts at slot
$t-\ell+1$ for exactly one $\ell\in\{1,\dots,t\}$, and it has length $\ell$. Its $\ell$
slots are plus slots, so the first $t$ slots contain $k$ plus slots exactly when the
first $t-\ell$ slots contain $k-\ell$. So $E^\minus_i(t,k)$ is the disjoint union over
$\ell$ of the events $E^\plus_i(t-\ell,k-\ell)\cap\{X^\plus_i=\ell\}$. By independence,
$\Prob(E^\minus_i(t,k))=\sum_{\ell=1}^t\Prob(E^\plus_i(t-\ell,k-\ell))f_\plus(\ell)$,
and summing over $i$ gives the first part of \eqref{eq:AB-recursion}. In the same way a
plus run starts at slot $t+1\ge2$ exactly when slot $t$ is the last slot of a minus run.
So $E^\plus_1(t,k)$ is empty, and for $i\ge2$ the event $E^\plus_i(t,k)$ is the disjoint
union over $\ell$ of $E^\minus_{i-1}(t-\ell,k)\cap\{X^\minus_{i-1}=\ell\}$, since minus
slots do not change the plus count. Summing over $i$ gives the second part.

For the cost, the recursion computes $A_t(k)$ and $B_t(k)$ for $0\le k\le t\le N-1$,
which are $O(N^2)$ numbers, each a sum of at most $N$ terms. This takes $O(N^3)$
operations. Then each $P_N(N-j)$ is a sum of at most $N$ terms, which takes $O(N^2)$
operations for the whole row.
\end{proof}

\begin{lemma}[the counting lemma]\label{lem:counting}
Fix $j\ge0$ and $N>j$. On the event $\{A_N=N-j\}$ there are exactly $j$ minus
slots among the first $N$ slots. Hence at most $j+1$ plus runs meet the first $N$
slots (at most $j$ if the first run is a minus run), and at least one of them has at
least $(N-j)/(j+1)$ slots among the first $N$. For a fresh start of either sign and
every $L\ge1$, the probability that $A_N=N-j$ and two plus runs that meet the first
$N$ slots have length at least $L$ is at most
\[
 \binom{j+1}2T_\plus(L)^2\le(j+1)^2T_\plus(L)^2 .
\]
\end{lemma}

\begin{proof}
On $\{A_N=N-j\}$ the first $N$ slots contain $N-(N-j)=j$ minus slots and $N-j\ge1$
plus slots. Let $r\ge1$ be the number of plus runs that meet the first $N$ slots. The
runs alternate, so between two consecutive such plus runs lies a minus run, and all
its slots come before slot $N$. So there are at least $r-1$ minus slots among the
first $N$, and $r\le j+1$. If the first run is a minus run, it also comes before every
plus run and has at least one slot among the first $N$, so $r\le j$. The $N-j$ plus
slots are shared among $r\le j+1$ runs, so by the pigeonhole principle one of these
runs has at least $(N-j)/(j+1)$ of them.

For the bound, take a fresh start of either sign. Then the plus runs have lengths
$X^\plus_1,X^\plus_2,\dots$ in order, and these are independent copies of $X_\plus$.
The plus runs that meet the first $N$ slots are the first $r$ of them. On the event in
the lemma $r\le j+1$, so there are indices $1\le a<b\le j+1$ with $X^\plus_a\ge L$ and
$X^\plus_b\ge L$. By the union bound and independence, the probability is at most
\[
 \sum_{1\le a<b\le j+1}\Prob(X^\plus_a\ge L)\,\Prob(X^\plus_b\ge L)=\binom{j+1}2T_\plus(L)^2 ,
\]
and $\binom{j+1}2\le(j+1)^2$. Here the length of a run is its whole length. The event
in which only the slots among the first $N$ are counted is smaller, so the bound holds
for it too.
\end{proof}
```
