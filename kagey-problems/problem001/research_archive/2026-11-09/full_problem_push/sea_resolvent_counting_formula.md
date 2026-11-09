# An exact sea-resolvent formula and recurrence

9 November 2026. The eventual counting sequence has an unconditional
rational formula using at most \(q_h+1\) sea resolvents in each summand.
This makes its recurrence depend on ordinary sea matrices, without
putting all \(2^{q_h}\) used-label subsets into the denominator.
It does not settle the dominant pole or its order.

Fix \(h\ge4\), and write \(q=q_h=\lfloor h^2/4\rfloor\).
For an unordered balanced row partition \(\pi\), let \(E_\pi\) be
its \(q\) double labels. Let \(e_\pi(m)\) count valid words whose
double columns are exactly these labels, each used once, and whose
other columns are singletons.

## 1. Matrices with exact finite ends

Use the finite history automaton from
[all_width_counting_formula.md](all_width_counting_formula.md),
with memory \(L=2W_h\), alphabet consisting of the \(h\) singleton
letters and the labels in \(E_\pi\), and final virtual pair set
\(E_\pi\). Empty columns are excluded. The transition tests use
actual contained rectangles. Initial short histories and acceptance
of every terminal history handle the two ends exactly.

Let \(A_0\) be the matrix of singleton transitions, and let \(A_e\)
be the matrix of transitions appending label \(e\). Let \(u\)
select the empty history, and let \(v\) be one at every terminal
history. Define
\[
R(z)=(I-zA_0)^{-1}.
\tag{1}
\]
All these matrices depend on \(\pi\), even when the notation omits it.
They are finite integer matrices. History states may contain earlier
double letters; no used-label subset is attached to a state.

The exact formula is
\[
\boxed{\displaystyle
\sum_{m\ge0}e_\pi(m)z^m
 =
 z^q\sum_{\sigma\in\operatorname{Sym}(E_\pi)}
 uR(z)A_{\sigma(1)}R(z)\cdots
 A_{\sigma(q)}R(z)v.}
\tag{2}
\]

To prove (2), expand each resolvent as
\(R(z)=\sum_{j\ge0}z^jA_0^j\). A term chooses a chronological
order for the \(q\) distinct doubles and the lengths of the
\(q+1\) singleton runs before, between, and after them.
These choices partition every accepted word uniquely.
No separation between doubles is imposed: runs of length zero
are included, and the history retains all recent doubles.
The exact local tests and complete final pair set identify precisely
the valid equality words, as in the all-width formula.

Equivalently, introduce commuting markers \(x_e\) and take the
squarefree coefficient of
\[
u\left(I-zA_0-z\sum_e x_eA_e\right)^{-1}v.
\]
Its resolvent expansion gives (2). This is a finite algebraic
identity, not an asymptotic expansion.

## 2. Only the sea contributes to the denominator

Let \(T_\pi\) be the restriction of \(A_0\) to histories of length
exactly \(L\) that contain only singleton letters. These states
are closed under singleton transitions.

Every other state is transient under \(A_0\). Short histories
reach length \(L\) after at most \(L\) transitions. A history
containing a double loses all its double letters after at most
\(L\) singleton transitions. Such a history cannot occur on a
directed singleton cycle. After ordering the transient and pure
sea states, the transient diagonal block is nilpotent. Therefore
\[
\det(I-zA_0)=\det(I-zT_\pi)=:D_\pi(z).
\tag{3}
\]
In particular \(D_\pi(z)\in\mathbb Z[z]\) and \(D_\pi(0)=1\).
The adjugate formula for \(R\), followed by (2), gives
\[
\sum_m e_\pi(m)z^m
  =\frac{P_\pi(z)}{D_\pi(z)^{q+1}}
\qquad\text{for some }P_\pi(z)\in\mathbb Z[z].
\tag{4}
\]
Cancellation can make the reduced denominator smaller.
The formula keeps exact finite ends. Replacing \(u,R,v\) by
unjustified normalized sea boundary vectors would not preserve
the numerator.

## 3. The optimum count has an integer recurrence

Write \(e_h(m)=\sum_\pi e_\pi(m)\). Every equality board has one
unique unordered balanced partition, so this sum has no duplicate
boards. The all-height construction gives a finite \(M_h\) such
that \(a_h(m)=e_h(m)\) for every \(m\ge M_h\).

Thus there is a polynomial \(F_h(z)\in\mathbb Z[z]\), consisting
of the finitely many earlier coefficient corrections, such that
\[
\sum_{m\ge0}a_h(m)z^m
 =
 F_h(z)+\sum_\pi
 \frac{P_\pi(z)}{D_\pi(z)^{q+1}}.
\tag{5}
\]
Any convention for the finitely many widths below four can be
included in \(F_h\).

Let
\[
D_h(z)=\mathop{\operatorname{lcm}}_\pi
              D_\pi(z)^{q+1}
       =1+d_1z+\cdots+d_sz^s,
\tag{6}
\]
where the least common multiple is normalized to constant term
one. Then, for every sufficiently large \(m\),
\[
\boxed{\displaystyle
a_h(m)+d_1a_h(m-1)+\cdots+d_sa_h(m-s)=0.}
\tag{7}
\]
The coefficients are integers and effectively computable.
If \(N_\pi\) is the number of pure sea histories in this
presentation, then
\[
s\le(q+1)\sum_\pi N_\pi.
\tag{8}
\]
One can reduce this bound using actual determinant degrees,
coincident characteristic factors, and cancellations.

## 4. Scope

Equations (2), (5), and (7) are unconditional general counting
formulas. They also show directly that every nonzero exponential
base comes from an ordinary singleton-sea eigenvalue. The marker
coordinates create no new exponential base.

They do not say which sea component dominates, whether the
dominant base is independent of the width residue, or whether
the leading polynomial has degree exactly \(q\). Those questions
remain the structural work needed to simplify the exact answer.
The sharper geometric pole-order bound and the general
residue-class asymptotic are proved in
[hereditary_marked_bridges.md](hereditary_marked_bridges.md) and
[unconditional_residue_asymptotics.md](unconditional_residue_asymptotics.md).
