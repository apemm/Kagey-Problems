# A fixed logarithm-of-logarithm threshold bound

9 November 2026. The weighted pair estimate in
[safe_triangle_pair_first_moment.md](safe_triangle_pair_first_moment.md)
needs only its first and second class-weight moments. This removes the
epsilon from the exponent of the main logarithm, at the cost of an
unspecified absolute power of the second logarithm.

**Theorem.** There are absolute constants \(C_0,C_1>0\) such that
\[
m_0(h)\le C_0 h^2(1+\log h)^2
                 (1+\log\log(3h))^{C_1}
\qquad(h\ge4).
\tag{1}
\]
The construction has constant tails, so equality holds at every width
at least the displayed bound. The constant \(C_1\) is not optimized.
This strengthens the \(2+\varepsilon\) logarithmic exponent, but does
not prove an absolute quadratic threshold.

## 1. The two moments

Keep the oriented profiles, harmless three-black triangles, exceptional
rows, and complete forbidden-support classification of the cited proof.
Write
\[
Q=\lfloor h^2/4\rfloor,\quad
\Lambda=1+\log h,\quad
\ell=1+\log\log(3h).
\]
For a profile with sea rows \(S\), put
\[
v(e)=1+\sum_{r\in e,\ s\in S}\tau(|r-s|).
\]
Use dyadic classes \(\mathcal C_w=\{e:w/2<v(e)\le w\}\), of size
\(n_w\). The divisor moments at exponents one and two give
\[
\sum_e v(e)\ll Q\Lambda,\qquad
\sum_e v(e)^2\ll Q\Lambda^3.
\tag{2}
\]
Thus, for one absolute \(C\),
\[
n_w\le C Q M(w),\qquad
M(w)=\min\{1,\ C\Lambda/w,\ C\Lambda^3/w^2\}.
\tag{3}
\]

The weighted pair proof applies at \(s=2\). Indeed its arithmetic
functions remain submultiplicative with subpower growth. Henriot's
upper bound then has prime exponent
\(\beta(2)=2^2-1=3\). Its distinct-root requirements and exceptional
row slices are unchanged. Consequently, for each \(e\in\mathcal C_w\),
\[
\sum_{f\in\mathcal C_w\setminus\{e\}}G_{e,f}
\ll Q\ell^{C_2}(\Lambda^2+w\Lambda)M(w)
       +h^{1+o(1)}
=:B(w),
\tag{4}
\]
with an absolute exponent \(C_2\). This follows by taking the minimum
of the unweighted bound and the bounds with class weights \(v(f)\)
and \(v(f)^2\). All constants are fixed.

## 2. Sum the pair budgets

For dyadic \(w\), split at constant multiples of \(\Lambda\) and
\(\Lambda^2\). Equation (3) gives
\[
\sum_w M(w)\ll 1+\log\Lambda\ll\ell.
\tag{5}
\]
For the weighted sum, the three ranges give respectively
\[
\begin{aligned}
\sum_{w\le\Lambda}wM(w)&\ll\Lambda,\\
\sum_{\Lambda<w\le\Lambda^2}wM(w)&\ll\Lambda(1+\log\Lambda),\\
\sum_{w>\Lambda^2}wM(w)&\ll\Lambda.
\end{aligned}
\tag{6}
\]
The middle range has \(O(1+\log\Lambda)\) dyadic classes and each
term is \(O(\Lambda)\). The outer sums are geometric. Enlarging
the split points by fixed constants has no effect. Hence
\[
\sum_w wM(w)\ll\Lambda\ell,\qquad
\sum_w B(w)\ll Q\Lambda^2\ell^{C_2+1}.
\tag{7}
\]
There are \(O(\log h)\) nonempty classes, so the uniform subpower
remainders sum to \(h^{1+o(1)}\), absorbed in (7).

## 3. Higher-arity budgets and ends

The established second-moment estimate for three- and four-label
supports has
\[
A(w)=\Lambda^4\ell^{C_3}+w\Lambda^{3/2}.
\]
It includes the restored six-cell collisions of harmless triangles.
The local-lemma placement length for a class is
\[
N_w\ll B(w)+\sqrt{n_wQ}\sqrt{A(w)}+n_w+1.
\tag{8}
\]

For completeness, (2) and (3) imply
\[
\sum_w\sqrt{n_w}\ll\sqrt{Q\ell}.
\tag{9}
\]
For \(w\le\Lambda\), use Cauchy--Schwarz and
\(\sum_w n_w\le Q\). For larger \(w\), use
\(n_w\ll Q\Lambda/w\) and sum a geometric series.
Also the same three ranges as (6) give
\[
\sum_w\sqrt{w n_w}
\ll \sqrt Q\sum_w\sqrt{wM(w)}
\ll \sqrt{Q\Lambda}\,\ell.
\tag{10}
\]
The middle range contributes \(O(\sqrt\Lambda)\) per dyadic class.
Equations (9) and (10) show that
\[
\begin{aligned}
\sum_w\sqrt{n_wQ}\sqrt{A(w)}
&\ll Q\left(
  \Lambda^2\ell^{C_3/2+1/2}
  +\Lambda^{5/4}\ell\right)\\
&\ll Q\Lambda^2\ell^{C_4}
\end{aligned}
\tag{11}
\]
for an absolute \(C_4\). Summing (8), then summing the constant
number of profile families, gives the same bound for the interiors.
The \(O(\log h)\) filled collars cost \(O(h^2\log h)\), and the
exceptional labels cost \(O(h^2)\). Both are absorbed in (1).
The verified constant-tail transitions supply all larger widths.
Finally, the finitely many heights below the profile construction's
range are absorbed by increasing \(C_0\).

## 4. Consequence for simultaneous counting

The argument of
[joint_height_width_counting.md](joint_height_width_counting.md)
now gives
\[
\frac{a_h(m)^{1/m}}h\longrightarrow\frac12
\quad\text{if}\quad
h\longrightarrow\infty,\qquad
\frac{m}{h^2(1+\log h)^3
             (1+\log\log(3h))^{C_1}}\longrightarrow\infty.
\tag{12}
\]
The extra main logarithm pays for the deterministic construction's
reserved columns. No stronger conclusion at widths comparable to
the threshold is asserted.
