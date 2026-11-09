# Polylogarithmic separation for dense short packets

9 November 2026. Averaging the diagonal-completion factorization removes the maximum-divisor loss from the packet incidence bound. Packet separation can therefore be a fixed power of \(\log h\), and packet widths can reach \(h/\log^3h\). Summable packet activities require an explicit lower bound on their internal error density.

Fix a protected pair \((c_0,X)\), its fixed final pair set, and normalized-support partition functions. Put \(\Lambda=1+\log h\), \(g_h=\Lambda^{10}\), and
\[
 \ell_{\max}=\lfloor h/\Lambda^3\rfloor.
\]
For intervals \(I_i\) of lengths \(\ell_i\le\ell_{\max}\), require their expansions by \(g_h\ell_i\) on both sides to be disjoint. Choose arbitrary \(S_i\subseteq I_i\), and put \(S=\bigcup_iS_i\). End collars of length \(L=Ch^2\) are understood.

**Relative packet claim.** For sufficiently large h,
\[
 Z_{X,S}(m)\le Z_X(m)
 \exp\left[-c\sum_i|S_i|\log^2(h/\ell_i)\right]
\tag{1}
\]
with absolute c. No internal density hypothesis is needed for this fixed-description estimate.

For the union over packet descriptions, fix any constant \(B_0>0\), and impose
\[
 |S_i|\ge \max(1,\lceil\ell_i/\Lambda^{B_0}\rceil).
\tag{2}
\]
Then its entropy is at most
\[
 \rho_X(h)\bigl(1+\exp[-c_{B_0}\log^2h]\bigr).
\tag{3}
\]
The complete proof passed [independent review](polylog_packet_independent_audit.md) and a [second audit](polylog_packets_independent_audit.md).

## 1. Average the diagonal kernel over a distance interval

All actual kernel distances satisfy \(1\le d\le L=Ch^2\). In interval and dyadic estimates, restrict \(1\le D\le L\) and truncate the selected distance set at L when necessary. This only decreases the sums, and ensures every logarithm of a norm or factorization scale is \(O(\Lambda)\).

Fix a black point P and let its completion column have distance d. In the diagonal case write the fixed diagonal as \((d,v)\) and the alternate one as \((z,w)\), with \(z>0\). All four columns are distinct. The case z=d is degenerate or axis-aligned and is excluded.

Put \(t=z-d\). Then
\[
 (v-w)(v+w)=t(2d+t)\ne0.
\tag{4}
\]
The vertical differences have magnitude less than h, so
\[
 0<|t|\le C\min(h,h^2/d).
\tag{5}
\]
The bound by h follows directly from
\(|z-d|\le\sqrt{d^2+h^2}-d\) when z>d, and
\(d-z\le\min(d,h^2/d)\) when z<d.

For each d,t, signed factor pairs in (4) give at most
\(C\tau(|t|)\tau(2d+t)\) possibilities. The admissible condition z>0 implies \(2d+t=d+z>0\).

Consider d in \([D,D+\ell]\), with \(\ell\le D\), and write
\[
 M=\max(h,D),\qquad T=C\min(h,h^2/D).
\]
A uniform divisor-hyperbola estimate gives
\[
 \sum_{\substack{D\le d<D+\ell\\d+t>0}}\tau(2d+t)
 \le C\ell\Lambda+C\sqrt M.
\tag{6}
\]
Indeed, divisibility by a fixes at most \(2\ell/a+1\) values of d, and only \(a\le C\sqrt M\) need be considered. The admissible d form a subinterval.

Using \(\sum_{n\le T}\tau(n)\le CT\log(2T)\), and dividing by \(h^2\) for the two residual row probabilities, yields
\[
 \sum_{D\le d<D+\ell}K_{\rm diag}(d)
 \le C\left[
 \frac{\ell\Lambda^2}{\max(h,D)}
 +\frac{\Lambda}{\sqrt{\max(h,D)}}\right].
\tag{7}
\]
Here the kernel also bounds raw incident event mass after summing the fixed black row. This replaces a maximum-divisor bound by an interval average.

## 2. Diagonal incidence on a sparse distance set

Suppose a set of relevant root distances in a dyadic interval \([D,2D]\) has cardinality at most \(CD/g\). Cauchy–Schwarz and
\[
 \sum_{n\le Y}\tau(n)^2\le CY(1+\log Y)^3
\tag{8}
\]
give, for every t,
\[
 \sum_{\substack{d\ \mathrm{selected}\\d+t>0}}\tau(2d+t)
 \le C\sqrt{\frac{D\max(h,D)}g}\,\Lambda^{3/2}.
\]
The elementary inequality \(\tau(n)^2\le d_4(n)\), followed by the divisor hyperbola, proves (8).

Sum over t as in Section 1. The conditional diagonal mass on this dyadic distance scale is at most
\[
 \frac{C\Lambda^{5/2}}{\sqrt g}
 \begin{cases}
 \sqrt{D/h},&D\le h,\\
 1,&D>h.
 \end{cases}
\tag{9}
\]
Summing the \(D\le h\) scales is geometric; there are \(O(\Lambda)\) remaining scales up to L. Thus the total is
\[
 O(\Lambda^{7/2}/\sqrt g).
\tag{10}
\]
The analogous side-kernel estimate, using Cauchy–Schwarz directly on \(\tau(d)/d\), is \(O(\Lambda^{5/2}/\sqrt g)\).

If the distance-set cardinality is instead at most \(CA\Lambda D/g\), multiply these bounds by \(O(\sqrt{A\Lambda})\).

## 3. Apply the estimates to packet geometry

For packet i use a buffer of radius
\[
 B_i=A\ell_i\Lambda
\]
and primitive cutoff \(R_i=\lfloor h/(1000B_i)\rfloor\), as in the far-black construction. Since \(\ell_i\le h/\Lambda^3\),
\[
 \log R_i\ge\tfrac12\log(h/\ell_i)
\]
for sufficiently large h. Delete all events whose black columns enter any packet buffer.

At a free black point, at most one expanded packet is near. Its side-kernel mass is \(C/A+o(1)\), by interval hyperbola summation. Its diagonal mass, by (7), is
\[
 O(\ell_i\Lambda^2/h+\Lambda/\sqrt h)=o(1).
\tag{11}
\]

For all far packets, the disjoint expanded intervals imply that the root columns in a distance annulus \([D,2D]\) number at most \(CD/g_h\). To see this, their central half-expansions have disjoint lengths comparable to \(g_h\ell_i\) and all lie in an annulus of length \(O(D)\). Equations (9)--(10) then give total far diagonal mass
\[
 O(\Lambda^{7/2}/\Lambda^5)=o(1),
\]
and the side mass is smaller. This controls both raw incidence and one-fixed-cell conditional extensions.

At a root in its own packet, every other packet is far. Their smaller buffers contain at most \(CA\Lambda D/g_h\) columns in an annulus. The last sentence of Section 2 bounds the mean removed by all other buffers by
\[
 O(\sqrt A\,\Lambda^4/\sqrt{g_h})
 =O(\sqrt A/\Lambda)=o(1).
\tag{12}
\]
The own buffer was excluded by construction. Each root consequently retains mean at least \(c\log^2(h/\ell_i)\).

## 4. Exact conditional comparison

Two fixed black cells have \(O(h)\) possible completion points across the whole strip. Their total two-assignment conditional mass is \(O(1)\). Three black corners determine their unique completion.

Mark the new roots by a fixed small probability. The one-cell estimates, the two-cell bound, and the usual protected-bulk extension estimates give the joint local lemma and the exact conditional lower-probability estimate for each marked root.

Retain old bulk certificates whose required black columns avoid S. Avoid those first, then the marked roots. Restore old bulk deleted at S at cost \(\exp(C|S|\Lambda^4/h)\), and include the alphabet-size ratio \(\exp(C|S|/h)\).

The smallest new penalty is of order \(\log^2\Lambda\), because \(h/\ell_i\ge\Lambda^3\). It absorbs both restoration costs. This proves (1).

## 5. Sum internally dense packets

Fix \(B_0>0\). For a packet of length ell, set
\[
 s=\log(h/\ell),\qquad
 q_{\min}=\max(1,\lceil\ell/\Lambda^{B_0}\rceil).
\]
Its nonempty activity under (2) is bounded by
\[
 a_\ell\le
 \sum_{q\ge q_{\min}}\binom{\ell}{q}e^{-cq s^2}.
\]
For such q,
\[
 \log(e\ell/q)\le1+B_0\log\Lambda.
\]
Since \(s\ge3\log\Lambda\), this binomial entropy is at most \(cs^2/2\) for large h. Hence
\[
 a_\ell\le2e^{-(c/2)q_{\min}s^2}.
\tag{13}
\]

Uniformly over \(\ell\le h/\Lambda^3\),
\[
 q_{\min}\log^2(h/\ell)\ge c_{B_0}\log^2h.
\tag{14}
\]
For \(\ell\le\Lambda^{B_0}\), this follows from
\(\log(h/\ell)\sim\log h\). Above that scale, the function
\(\ell\log^2(h/\ell)\) is increasing for \(\ell<h/e^2\), so its minimum occurs at the lower endpoint.

Summing (13) over all polynomially many lengths gives
\[
 \sum_{\ell\le\ell_{\max}}a_\ell
 \le e^{-c'_{B_0}\log^2h}.
\]
Allowing a packet to start at every column overcounts the valid descriptions and proves (3).

The density condition in (2) is essential to this activity argument. The fixed-description relative bound (1) does not require it. Arbitrary densely interacting packets and macroscopic phase profiles remain unresolved.

