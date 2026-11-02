"""Integrate the reviewed proof fragments without editing the disclosure."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'kagey-problems/problem131/paperD'
NOTES = ROOT / 'research_notes/Paper D transition and modes'
main = PAPER / 'problem131_memory.tex'
source = main.read_text(encoding='utf-8')
disclosure = source.split(r'\section*{A note on the use of AI}', 1)[1].split(
    r'\section*{Statements and Declarations}', 1)[0]

app = PAPER / 'app_modes.tex'
text = app.read_text(encoding='utf-8')
if r'\label{prop:all-bias-modes}' not in text:
    fragment = (NOTES / 'biased_modes_proof.tex').read_text(encoding='utf-8')
    fragment = fragment[fragment.index(r'\begin{proposition}'):]
    fragment = fragment.split('% The following is the short limit transfer.')[0].rstrip()
    text += '\n\n\\subsection{First differences for a biased start}\n\n' + fragment + '\n'
text = text.replace(
    'The densities of $\\mathcal L_a$ and\n$\\mathcal L^\\circ_a$ extend to entire functions. In particular, neither\ndensity is constant on an interval of positive length.',
    'For every $q\\in[0,1]$, the density of the limit with first-step bias $q$\nextends to an entire function and is not constant on an interval of\npositive length.')
text = text.replace(
    'The fair-start characteristic function is\n$\\operatorname{Re}\\phi_a(t)$ for real $t$ and obeys the same bound.\nBoth densities are integrable with integral one, so neither is constant\non $\\mathbb R$. The identity theorem excludes a constant interval.',
    'At initial bias $q$, the characteristic function is\n$q\\phi_a(t)+(1-q)\\phi_a(-t)$ and obeys the same bound by the triangle\ninequality. Each resulting density is integrable with integral one, so\nit is not constant on $\\mathbb R$. The identity theorem excludes a\nconstant interval.')
app.write_text(text, encoding='utf-8', newline='\n')

section = PAPER / 'sec_bulk_applications.tex'
text = section.read_text(encoding='utf-8')
text = text.replace(
    'This is weak convergence. Trinas and Valle find',
    'Theorem~\\ref{thm:near-one-profile} below upgrades this convergence to a\nuniform density approximation and total variation convergence. Trinas and Valle find')
text = text.replace(
    'The conjecture for $q\\ne\\frac12$ remains open. For $q\\ne\\frac12$ the\nfinite law $qf_N(N-k)+(1-q)f_N(k)$ is not symmetric, and we have no analogue\nof Theorem~\\ref{thm:five-blocks} for it.',
    'The full bias-dependent phase classification remains open. The next\nresult gives an at-most-two-mode bound for every bias. It uses first\ndifferences: the symmetric curvature bound need not persist under bias.')
if r'\label{thm:biased-limit-modes}' not in text:
    text += r'''

\subsection{Arbitrary initial bias}

Write $h_a$ for the density of $\mathcal L_a$ and
$g_{a,q}(x)=q h_a(x)+(1-q)h_a(-x)$ for initial bias
$\Prob(X_1=1)=q$. Thus $g_{a,1/2}=g_a$.

\begin{theorem}[at most two modes for every bias]\label{thm:biased-limit-modes}
For every $a\in(1/2,1)$ and $q\in[0,1]$, the density $g_{a,q}$ has at
most two local maxima. At finite time, for every $0<\varepsilon<1$ and
$N\ge1$, the count law has at most two modal plateaus, including its
endpoints.
\end{theorem}

\begin{proof}
Proposition~\ref{prop:all-bias-modes} proves the finite assertion and,
more precisely, excludes two successive strict valleys. The local
limit theorem of Trinas and Valle~\cite[Theorem~3.1]{tv2026} gives
\[
 \frac{N^a}{2}P_N\!\left(\left\lfloor
             \frac{N+N^a x}{2}\right\rfloor\right)\longrightarrow g_{a,q}(x)
 \qquad(x\in\mathbb R).
\]
The lattice point has the correct parity and differs from $x$ after
scaling by less than $2N^{-a}$. Continuity therefore justifies this
form of the local limit, including the span-two factor.
Lemma~\ref{lem:analytic-density} excludes constant intervals for every
bias. If $x<y<z$ were local maxima, there would be
$x<u<y<v<z$ with
\[
 g_{a,q}(u)<\min\{g_{a,q}(x),g_{a,q}(y)\},\qquad
 g_{a,q}(v)<\min\{g_{a,q}(y),g_{a,q}(z)\}.
\]
For each pair choose a point below the smaller local maximum in its
one-sided maximizing neighbourhood. The absence of a constant
interval makes that decrease strict. The five lattice indices are
ordered for all large $N$, and the local limit preserves the four
strict inequalities. This contradicts
Proposition~\ref{prop:all-bias-modes}.
\end{proof}

This bounds the number of modes without classifying the biases for
which both occur. In particular, it does not prove that the set of
bimodal biases is an interval centred at $1/2$, as conjectured
in~\cite[Remark~2.1(b)]{glrs2025}.

\subsection{Uniform profiles as memory tends to one}

'''
    profile = (NOTES / 'near_one_profile_proof.tex').read_text(encoding='utf-8')
    profile = profile[profile.index(r'\begin{theorem}'):]
    profile = profile.split('% Exact two-mode claims')[0].rstrip()
    text += profile + '\n'
section.write_text(text, encoding='utf-8', newline='\n')

after = main.read_text(encoding='utf-8').split(r'\section*{A note on the use of AI}', 1)[1].split(
    r'\section*{Statements and Declarations}', 1)[0]
if after != disclosure:
    raise RuntimeError('The disclosure changed')
print('Proof fragments integrated; disclosure unchanged.')
