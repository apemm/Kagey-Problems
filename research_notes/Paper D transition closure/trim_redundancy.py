"""Prose-only cuts, with exact preservation checks for mathematical blocks."""
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
    blocks = re.findall(r"\\begin\{("+names+r")\*?\}.*?\\end\{\1\*?\}", text, re.S)
    # Full matches, including the exact environment contents.
    blocks = [m.group(0) for m in re.finditer(r"\\begin\{("+names+r")\*?\}.*?\\end\{\1\*?\}", text, re.S)]
    blocks += re.findall(r"\\\[.*?\\\]", text, re.S)
    return blocks


CHANGES = {
"sec_erw_crossing.tex": [
(r"""We reduce the elephant walk to a counting chain and prove that the crossing is
unique. We then compute the center to first order in $\varepsilon$, bound it
from both sides, and locate the crossing.

""", ""),
(r"""A flip is what the introduction called a reversal. Given the first step, all that
matters is how many steps disagree with it. So let $M_t$ be the number of
$i\le t$ with $X_i\ne X_1$, and put""",
r"""A flip is the reversal of the introduction. Let $M_t$ count the
$i\le t$ with $X_i\ne X_1$, and put"""),
(r"""We need some more notation. Let $V_s(b)$ be the chance of ending at the
center from state $b$ at time $s$. We define it by the backward recursion""",
r"""Define the hitting probability $V_s(b)$ from state $b$ at time $s$ by"""),
(r"""The first-order coefficient in part (b) below is known. With both switching
probabilities equal to $\varepsilon$ and one sensitive cell at the start, the
number of resistant cells in the reversible fluctuation assay of Bokes,
Hlubinov\'a and Singh~\cite[Section~2 and Eq.~(1)]{bhs2023} is our chain $M$.
They condition on the first switch and use P\'olya's urn, as we do, and their
first-order formula~\cite[Eqs.~(6)--(10)]{bhs2023} gives
$\varepsilon N/(m(m+1))$ as the part of $f_N(m)$ of first order in
$\varepsilon$, which is $\frac{4\varepsilon}{N+2}$ at
$m=h$. We include the short proof because the decomposition (a) and the
weights (c) are what the uniform bounds of Theorem~\ref{thm:erw-bounds} and
Appendix~\ref{app:erw} start from.""",
r"""The first-order coefficient in (b) is known. With equal switching
probabilities $\varepsilon$ and one initial sensitive cell, the resistant-cell
count of Bokes, Hlubinov\'a and Singh~\cite[Section~2 and Eq.~(1)]{bhs2023}
is $M$. Their first-switch and P\'olya-urn argument gives
$\varepsilon N/(m(m+1))$ as the first-order part of $f_N(m)$
\cite[Eqs.~(6)--(10)]{bhs2023}, hence $\frac{4\varepsilon}{N+2}$ at $m=h$.
We retain the proof because (a) and (c) underpin the uniform bounds of
Theorem~\ref{thm:erw-bounds} and Appendix~\ref{app:erw}."""),
(r"""This subsection bounds the center from both sides. The bounds give the crossing in the next
subsection.

""", ""),
(r"""We prove three refinements in \arxivonly{Section}{sec:erw-second}. A
lower bound for $C_N$ matches Theorem~\ref{thm:erw-bounds}(b) up to a
factor $1+O(\varepsilon)$. One more term of the crossing shows that
$x_N<g_N$ for large $N$. A comparison with the crossing value $z_N$ of $T$
for the persistent walk shows that $x_N-(2z_N-\log(2\pi))$ is $c_*/\log N$
to first order, with $c_*=\frac12\log(2\pi)-\frac14$.""",
r"""In \arxivonly{Section}{sec:erw-second}, a lower bound for $C_N$ matches
Theorem~\ref{thm:erw-bounds}(b) up to $1+O(\varepsilon)$, and a further
crossing term gives $x_N<g_N$ for large $N$. If $z_N$ is the crossing value
of $T$ for the persistent walk, then $x_N-(2z_N-\log(2\pi))$ is
$c_*/\log N$ to first order, with $c_*=\frac12\log(2\pi)-\frac14$."""),
],
"sec_erw_shape.tex": [
(r"""We now look at the whole law $P_N$ near the crossing. In this section and in
Appendices~\ref{app:shape} and~\ref{app:bulk}, a statement that says
``Assume~\eqref{eq:H}'' assumes""",
r"""In this section and Appendices~\ref{app:shape} and~\ref{app:bulk},
``Assume~\eqref{eq:H}'' means"""),
(r"""So the first flip turns its whole family except the steps of that
family that flip back, and the rest of the tree is a walk whose first $j-1$
steps agree with $X_1$. Only the law of each pair $(Y_d,Z^{(j)}_{N-d})$
enters the lemma. So from now on $(Y_d)_{d\ge1}$ is a copy of the chain
$M^{[1]}$, and $(Z^{(j)}_t)_{t\ge j-1}$ is a copy of $M^{[j-1]}$, independent
of $Y$ and of $(V,\lvert\mathcal T_V\rvert)$.""",
r"""Only the law of each pair $(Y_d,Z^{(j)}_{N-d})$ enters the lemma.
Henceforth $(Y_d)_{d\ge1}$ is a copy of $M^{[1]}$, and
$(Z^{(j)}_t)_{t\ge j-1}$ is a copy of $M^{[j-1]}$, independent of $Y$
and $(V,\lvert\mathcal T_V\rvert)$. The latter walk starts with $j-1$
steps agreeing with $X_1$."""),
(r"""This is shown at the start of the proof of Theorem~1.1
of~\cite{glrs2025}, for every $N$ and every memory parameter
$p=1-\varepsilon\in[0,1]$, for the position $N-2M_N$ given $X_1=+1$. The lemma is also proved in Lean
(Section~\ref{sec:verify}). So
$f_N$ is nondecreasing on $\{0,\dots,m_h\}$ and nonincreasing on
$\{m_h,\dots,N\}$. With a fair first step, $P_N$ mixes $f_N$ and its mirror
image. When the mode of $f_N$ is far from the center, the mixture can have
two humps, one near each end.""",
r"""The proof of~\cite[Theorem~1.1]{glrs2025} treats every $N$ and
$p=1-\varepsilon\in[0,1]$, for $N-2M_N$ given $X_1=+1$; a Lean proof
is recorded in Section~\ref{sec:verify}. Thus $f_N$ is nondecreasing on
$\{0,\dots,m_h\}$ and nonincreasing on $\{m_h,\dots,N\}$. Its fair
mixture $P_N$ can have two humps when the mode of $f_N$ is far from the center."""),
(r"""We first say heuristically why the end should fall below its neighbor once
$x>2$ (Figure~\ref{fig:shape}(a), inset). Given
$X_1=+1$, the end needs no flip at all. Its neighbor, the value $N-1$, needs one flip
that is never copied. A flip at step $j$ is never copied with probability
about $j/N$. Summing $\varepsilon j/N$ over $j$ gives a factor of about $x/2$
in favor of the neighbor.""",
r"""The heuristic threshold is $x>2$ (Figure~\ref{fig:shape}(a), inset).
Given $X_1=+1$, the end needs no flip, whereas $N-1$ needs one flip
that is never copied. A flip at step $j$ is never copied with probability
about $j/N$; summing $\varepsilon j/N$ over $j$ gives the factor $x/2$."""),
(r"""The CP law and its Landau limit are known (Section~\ref{sec:prior}).
We give an explicit total variation bound for the CP approximation to the
elephant law, and an explicit local rate for the law with jump sizes
truncated at $N-1$. Numerical values of $f_L$ and its mode are standard
(see K\"olbig and Schorr~\cite{ks1984}).
Lemma~\ref{lem:landau-mode} adds a certified enclosure.""",
r"""The CP law and Landau limit are known (Section~\ref{sec:prior}). We give
explicit total variation and local bounds, the latter with jumps truncated
at $N-1$. K\"olbig and Schorr~\cite{ks1984} compute $f_L$ and its mode;
Lemma~\ref{lem:landau-mode} adds a certified enclosure."""),
(r"""The families of size up to about $x$ add up to nearly $x\log x$, and the few
families of size of order $x$ give fluctuations of order $x$. So we center
$M_N$ at $x\log x$ and divide by $x$, which gives the coordinate $\lambda_m$
and the Landau density $f_L$ of Section~\ref{sec:results}. It is a stable
density with index one. We show in
Appendix~\ref{app:bulk} that $e^B$ is the characteristic function of a
probability law of class $L$, so that $f_L$ is a unimodal probability
density by~\cite{yamazato1978}.""",
r"""Families of size up to $x$ contribute nearly $x\log x$; those of order
$x$ give fluctuations of order $x$. Centering $M_N$ at $x\log x$ and
dividing by $x$ gives $\lambda_m$ and the index-one stable density $f_L$.
Appendix~\ref{app:bulk} shows that $e^B$ is the characteristic function
of a law of class $L$, so $f_L$ is unimodal by~\cite{yamazato1978}."""),
(r"""Near the crossing the number of disagreeing steps is about
$x\log x$, with fluctuations of order $x$ that follow the Landau law, point by
point (Figure~\ref{fig:shape}(b)). Both conditions of (c) hold at the crossing, by
Theorem~\ref{thm:erw-crossing}. For the untruncated law the weak limit in (c) is
Pakes' theorem~\cite[p.~993]{pakes1993}, and Bertoin proves the analogue for the
vertices cut off from the root of a random recursive tree in another
regime~\cite[Proposition~1]{bertoin2014ejp}. So (c) is new only through the
transfer to the walk. We know of no earlier form of (a) and (b).""",
r"""At the crossing, the disagreement count is about $x\log x$, with
Landau fluctuations of order $x$ (Figure~\ref{fig:shape}(b));
Theorem~\ref{thm:erw-crossing} supplies both conditions of (c).
For the untruncated law, (c) is Pakes' theorem~\cite[p.~993]{pakes1993}.
Bertoin proves an analogue for vertices cut from a random recursive
tree's root in another regime~\cite[Proposition~1]{bertoin2014ejp}.
Thus (c) is new only in its transfer to the walk; we know no earlier
form of (a) or (b)."""),
(r"""Trinas and Valle~\cite[(2.2)]{tv2026} write \eqref{eq:P-rec} for the mass
function of the position, which is the forward equation of the counting
chain of Lemma~\ref{lem:erw-reduction}, and they use it for a local limit
theorem in the superdiffusive regime. In~\cite[(4.10)]{tv2026} they write
the analogue of~\eqref{eq:D-rec} for differences of higher order, and they
use it at a fixed memory parameter in a certified study of log-concavity. We use
\eqref{eq:D-rec} for signs.
The coefficients in \eqref{eq:D-rec} are positive when $2\le a\le t-1$. So the
second difference moves like a mass that is partly killed, and its sign can
change only through what enters at the two edges. The next lemma is the
elementary form of the variation diminishing property that we need.""",
r"""Trinas and Valle~\cite[(2.2)]{tv2026} use \eqref{eq:P-rec}, the forward
equation of Lemma~\ref{lem:erw-reduction}, for a superdiffusive local
limit theorem. Their higher-difference recurrence~\cite[(4.10)]{tv2026}
supports a certified fixed-memory study of log-concavity. We use
\eqref{eq:D-rec} for signs: its coefficients are positive for
$2\le a\le t-1$, so sign changes enter only through the two edges.
The next lemma gives the required variation diminishing property."""),
],
}

result = {}
pending = {}
for name, replacements in CHANGES.items():
    path = PAPER/name
    before = path.read_text(encoding="utf-8")
    after = before
    for old,new in replacements:
        require(after.count(old)==1, f"Expected one paragraph match in {name}: {old[:60]}")
        after = after.replace(old,new)
    require(protected(before)==protected(after), f"Protected mathematical block changed: {name}")
    inline = lambda s: set(re.findall(r"(?<!\\)\$(?!\$)(.*?)(?<!\\)\$",s,re.S))
    missing = inline(before)-inline(after)
    require(not missing, f"Unique inline formula removed in {name}: {missing}")
    count = lambda s: len(s.split())
    result[name] = {"words_before":count(before),"words_after":count(after),
      "words_removed":count(before)-count(after),"protected_blocks":len(protected(before)),
      "protected_blocks_unchanged":True,"all_distinct_inline_formulae_preserved":True,
      "sha256_before":hashlib.sha256(before.encode()).hexdigest(),
      "sha256_after":hashlib.sha256(after.encode()).hexdigest()}
    pending[path] = after
for path,after in pending.items():
    path.write_text(after,encoding="utf-8")
Path(__file__).with_name("trim_output.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
