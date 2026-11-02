"""Second prose-only trim; all proof and mathematical environments are fixed."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "kagey-problems/problem131/paperD"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def protected(text):
    names = "definition|theorem|lemma|proposition|corollary|proof|remark|figure|table|equation|align|gather"
    blocks = [m.group(0) for m in re.finditer(r"\\begin\{("+names+r")\*?\}.*?\\end\{\1\*?\}", text, re.S)]
    return blocks + re.findall(r"\\\[.*?\\\]", text, re.S)


CHANGES = {
"sec_erw_crossing.tex": [
(r"""So to first order the walk flips once, at some step $t+1$, and then
runs as P\'olya's urn from $t$ balls of one color and one of the other. As
$N\to\infty$ the final fraction of the color that started with one ball tends
in law to a Beta$(1,t)$ variable, whose density at $\frac12$ is $t2^{1-t}$, and $\sum_tt2^{1-t}=4$ explains the constant
$4/(N+2)$. Since $w_t\le2t2^{-t}$, only an early flip counts in this
first-order term.""",
r"""To first order, one flip at step $t+1$ starts P\'olya's urn with $t$
balls of one color and one of the other. As $N\to\infty$, the latter
fraction tends to Beta$(1,t)$, with density $t2^{1-t}$ at $\frac12$.
Thus $\sum_tt2^{1-t}=4$ explains $4/(N+2)$, and $w_t\le2t2^{-t}$
restricts this term to early flips."""),
(r"""The proof is in Appendix~\ref{app:erw}. After the first flip, $M$ at time $s$
is P\'olya's urn with $\alpha s$ extra balls of each color, where
$\alpha=\varepsilon/(1-2\varepsilon)$ (Lemma~\ref{lem:A-polya}). They pull the
minority fraction toward $\frac12$. For (a) we drop them. For (b) we compare
$M$ with an urn with $\kappa(s+10)$ extra balls, where
$\kappa=2\varepsilon/(1-4\varepsilon)$. One step of $M$ at time $s$
multiplies the hitting probability of this urn by a factor of at most about
$e^{\kappa/s}$, and the product of these factors is about
$e^{\kappa H_N}\approx N^{2\varepsilon}$.""",
r"""Appendix~\ref{app:erw} represents $M$ at time $s$, after its first flip,
as P\'olya's urn with $\alpha s$ extra balls of each color, where
$\alpha=\varepsilon/(1-2\varepsilon)$ (Lemma~\ref{lem:A-polya}). These pull
the minority fraction toward $\frac12$; dropping them gives (a).
For (b), use an urn with $\kappa(s+10)$ extra balls, where
$\kappa=2\varepsilon/(1-4\varepsilon)$. Each step multiplies its hitting
probability by at most about $e^{\kappa/s}$, whose product is about
$e^{\kappa H_N}\approx N^{2\varepsilon}$."""),
],
"sec_erw_shape.tex": [
(r"""For $k_0\ge1$ let $(M^{[k_0]}_k)_{k\ge k_0}$ be the Markov chain with
$M^{[k_0]}_{k_0}=0$ and the transition probabilities $r_k(b)$ of $M$. It is
the count of disagreeing steps for a walk whose first $k_0$ steps are forced
to agree. So $M^{[1]}$ has the law of $M$. We write $Y_d=M^{[1]}_d$, and
$Z^{(j)}_t=M^{[j-1]}_t$ for $j\ge2$ and $t\ge j-1$. In a random recursive tree
on $[N]=\{1,\dots,N\}$, vertex $k+1$ is joined to a uniform vertex of $[k]$,
independently for $k=1,\dots,N-1$. We write $\mathcal T_v$ for the subtree of
$v$, that is, $v$ and its descendants, and we call it the family of $v$.""",
r"""For $k_0\ge1$, the chain $(M^{[k_0]}_k)_{k\ge k_0}$ starts at
$M^{[k_0]}_{k_0}=0$ with transitions $r_k(b)$. It counts disagreeing
steps when the first $k_0$ steps are forced to agree; $M^{[1]}$ has the
law of $M$. Put $Y_d=M^{[1]}_d$ and $Z^{(j)}_t=M^{[j-1]}_t$ for
$j\ge2$, $t\ge j-1$. In a random recursive tree on $[N]=\{1,\dots,N\}$,
vertex $k+1$ joins a uniform vertex of $[k]$, independently for
$k=1,\dots,N-1$. The family $\mathcal T_v$ comprises $v$ and its descendants."""),
(r"""So a single flip at $v$ turns every step of its family
(Figure~\ref{fig:family}). For $k\ge v$, if $\mathcal T_v$ contains $s$ of the
vertices in $[k]$, then $k+1$ joins $\mathcal T_v$ with probability $s/k$.
This is the urn of Lemma~\ref{lem:urn}, so $\lvert\mathcal T_v\rvert$ has the
law $\beta_v$ and mean $N/v$, and on average there are $N/(d(d+1))$ families
of size $d$. If $v$ is the only marked vertex, the odd vertices are those of
$\mathcal T_v$. Two or more marks have probability $O(\varepsilon^2)$ at fixed
$N$, and no mark gives $M_N=0$. So at fixed $N$ the part of $f_N(m)$ of first
order in $\varepsilon$ is exactly $\varepsilon\sum_v\beta_v(m)=x/(m(m+1))$ for
$1\le m\le N-1$, which is the formula of~\cite[Eq.~(10)]{bhs2023} with one cell at the
start. It is also proved in Lean
for the chain $M$ (Section~\ref{sec:verify}).""",
r"""A single flip at $v$ turns its family (Figure~\ref{fig:family}). For
$k\ge v$, a family $\mathcal T_v$ containing $s$ vertices of $[k]$
gains vertex $k+1$ with probability $s/k$. Lemma~\ref{lem:urn} gives
$\lvert\mathcal T_v\rvert$ law $\beta_v$, mean $N/v$, and an average
$N/(d(d+1))$ families of size $d$. If $v$ alone is marked,
$\mathcal T_v$ is the odd set. At fixed $N$, multiple marks have
probability $O(\varepsilon^2)$ and no mark gives $M_N=0$. Thus the
first-order part of $f_N(m)$ in $\varepsilon$ is
$\varepsilon\sum_v\beta_v(m)=x/(m(m+1))$ for $1\le m\le N-1$:
\cite[Eq.~(10)]{bhs2023} with one initial cell, also proved in Lean
for $M$ (Section~\ref{sec:verify})."""),
(r"""Here $\operatorname{TV}(P,Q)=\frac12\sum_k|P(k)-Q(k)|$. Thus the same
bound holds for each mass and each event. Also
$\delta_\Sigma=O(x^2\log^2N/N)$. Appendix~\ref{app:bulk-cp} proves the
bound by coupling marks with Poisson variables and revealing the tree's
parents one at a time. Changing one parent affects family sizes only
along two paths to the root, whose depths have second moments of order
$\log^2N$.""",
r"""Here $\operatorname{TV}(P,Q)=\frac12\sum_k|P(k)-Q(k)|$, so the bound
holds for every mass and event, and $\delta_\Sigma=O(x^2\log^2N/N)$.
Appendix~\ref{app:bulk-cp} couples marks with Poisson variables and
reveals parents successively. Changing one parent affects family sizes
along only two root paths, whose depth second moments have order $\log^2N$."""),
(r"""The next theorem is the step that turns one sign into a whole convex
stretch. Its idea is short. A sign change from negative to positive at
$a_0<a_1$, together with its mirror image, gives the signs $-,+,+,-$ at
$a_0<a_1<N-a_1<N-a_0$. A negative second difference in between would add a
fifth alternating sign, which Theorem~\ref{thm:five-blocks} forbids. A zero
in between is subtler. We follow it back in time through \eqref{eq:D-rec},
whose coefficients are positive, so a zero has two zero parents unless its
parents have opposite signs, and opposite signs would again give five
alternating signs. Going back to $t=5$ forces $s_3=s_4=0$, which
Lemma~\ref{lem:level-one} rules out.""",
r"""A negative-to-positive change at $a_0<a_1$ and its reflection give
$-,+,+,-$ at $a_0<a_1<N-a_1<N-a_0$. A negative second difference
between them would give the fifth alternating sign forbidden by
Theorem~\ref{thm:five-blocks}. For a zero, trace \eqref{eq:D-rec}
backwards: positivity of its coefficients forces two zero parents,
unless the parents have opposite signs, again giving five alternating
signs. Reaching $t=5$ forces $s_3=s_4=0$, contrary to
Lemma~\ref{lem:level-one}. This proves a whole convex stretch."""),
(r"""The finite endpoint-dip certificates in Proposition~\ref{prop:dip-hyp}
remain inputs. Neither corollary needs a mode-location or convex-window
estimate. The height bound gives a window at every even length, although it may
consist only of the center. Heuristically the window is much wider. Near the
crossing, Theorem~\ref{thm:landau}(b) and Corollary~\ref{cor:mode-location} give
$M=P_N(r)=\frac{f_L(\lambda_{\mathrm L})}{2x}(1+o(1))$, so with $m^*=r$ we get
$B=m^*+\bigl(2/f_L(\lambda_{\mathrm L})+o(1)\bigr)x$. Since
$f_L(\lambda_{\mathrm L})\approx0.1807$, this is about $m^*+11x$, far below $h$
for large $N$. At $N=4000$ the computed $B-m^*$ is about $9.9x$. We do not
compute the $o(1)$, and the constants of Theorem~\ref{thm:landau} are far from
sharp, so this is not a bound. A stronger, prescribed window is studied in
\arxivonly{Section}{or:window}.""",
r"""Both corollaries use the finite endpoint-dip certificates of
Proposition~\ref{prop:dip-hyp}, but no mode-location or convex-window
estimate. The height bound supplies a window at every even length,
possibly just the center. Heuristically, Theorem~\ref{thm:landau}(b) and
Corollary~\ref{cor:mode-location} give
$M=P_N(r)=\frac{f_L(\lambda_{\mathrm L})}{2x}(1+o(1))$, hence, with $m^*=r$,
$B=m^*+\bigl(2/f_L(\lambda_{\mathrm L})+o(1)\bigr)x$. Since
$f_L(\lambda_{\mathrm L})\approx0.1807$, this is about $m^*+11x$, far below
$h$ for large $N$; at $N=4000$, computed $B-m^*$ is about $9.9x$.
This is not a bound: the $o(1)$ is unevaluated and the constants of
Theorem~\ref{thm:landau} are not sharp. For a stronger prescribed window,
see \arxivonly{Section}{or:window}."""),
(r"""The center of a walk with an even number of steps is reached from the two central values
one step earlier, and from each of them with the same probability. So the two central values of
an odd $N$ are the center of $N+1$ up to the factor $1-c/N$, and what we know about the crossing
for even $N$ carries over. We show in \arxivonly{Proposition}{prop:odd-more} that the crossing for
odd $N$ satisfies Theorem~\ref{thm:erw-crossing}, that $P_N(0)<P_N(1)$ at the crossing for odd
$N\ge1689$, and that the convexity window of \arxivonly{Section}{or:window} holds at the crossing
for every large odd $N$.""",
r"""The two central values at odd $N$ reach the center at $N+1$ with equal
probabilities, giving the factor $1-c/N$. By
\arxivonly{Proposition}{prop:odd-more}, their crossing satisfies
Theorem~\ref{thm:erw-crossing}; $P_N(0)<P_N(1)$ there for odd
$N\ge1689$, and the convexity window of \arxivonly{Section}{or:window}
holds at every sufficiently large odd $N$."""),
],
}

result, pending = {}, {}
for name,replacements in CHANGES.items():
    path = PAPER/name
    before = path.read_text(encoding="utf-8")
    after = before
    for old,new in replacements:
        require(after.count(old)==1, f"Expected one paragraph in {name}: {old[:60]}")
        after = after.replace(old,new)
    require(protected(before)==protected(after), f"Protected block changed in {name}")
    inline = lambda s: set(re.findall(r"(?<!\\)\$(?!\$)(.*?)(?<!\\)\$",s,re.S))
    missing = inline(before)-inline(after)
    require(not missing, f"Distinct inline formula removed in {name}: {missing}")
    result[name] = {"words_before":len(before.split()), "words_after":len(after.split()),
        "words_removed":len(before.split())-len(after.split()),
        "protected_blocks":len(protected(before)),"protected_blocks_unchanged":True,
        "all_distinct_inline_formulae_preserved":True,
        "sha256_before":hashlib.sha256(before.encode()).hexdigest(),
        "sha256_after":hashlib.sha256(after.encode()).hexdigest()}
    pending[path] = after
for path,after in pending.items():
    path.write_text(after,encoding="utf-8")
Path(__file__).with_name("trim_second_output.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
