# The linear P palette works at every fixed horizontal scale

9 November 2026. Fix a positive integer \(s\). Replace the within-block
horizontal coordinate \(2(a-1)\) by \(s(a-1)\), where \(a\) is the odd row
of a parity label. The resulting global vertical-rival graph still has
chromatic number \(O_s(h)\).

Define
\[
D_s(u)=\#\{d\in2\mathbb Z\setminus\{0\}:
              (u+d)^2+s^2d^2=L^2,\quad 1\le L\le h-1\}.
\]
The proof of global_P_linear_coloring.md applies with this replacement.
Here are the three required arithmetic checks.

First, the right triangle has legs \(s|d|\) and \(|u+d|\). The first leg
is even and the second odd. Each triangle has at most four signed
preimages \((u,d)\). Hence
\[
\sum_{\substack{|u|\le h-1\\u\ {\rm odd}}}D_s(u)=O(h\log h).
\]
This bound is independent of \(s\).

Second, put \(A=s^2+1\). Completing the square gives
\[
(Ad+u)^2-A L^2=-s^2u^2.
\]
The integer \(A\) is nonsquare. Dividing a solution by the greatest common
divisor of its two coordinates produces a primitive norm equation with
norm \(N=-s^2u^2/g^2\), where \(g\mid s|u|\). Its second coordinate is
invertible modulo \(|N|\), so it determines a root of
\[
r^2\equiv A\pmod {|N|}.
\]
For fixed \(A\), this congruence has at most \(C_s\tau(|N|)\) roots.
At primes not dividing \(2A\), there are at most two roots per prime
power. The root counts at the finitely many remaining primes have
bounded factors depending only on \(A\).

Two primitive solutions in the same root class have an integral
norm-one quotient in \(\mathbb Z[\sqrt A]\). Positive quotients greater
than one exceed two, by comparing them with their reciprocal conjugates.
The positive real solution coordinates have size between \(1/(C_sh)\)
and \(C_sh\). Thus each root class contributes \(O_s(\log h)\) solutions.
The divisor estimate now gives
\[
\max_uD_s(u)=h^{o(1)}.
\]
This argument uses only the discreteness of integer norm-one quotients,
not a fundamental-unit formula.

Finally, a fixed other odd row \(a'\ne a\) blocks at most
\[
2\tau\bigl(s^2(a'-a)^2\bigr)=h^{o(1)}
\]
vertices within the odd-row-\(a\) clique. The factorization is
\[
\bigl(L-(a'-b)\bigr)\bigl(L+(a'-b)\bigr)=s^2(a'-a)^2.
\]

These are exactly the total-mass, maximum-blocker, and blocker-frequency
hypotheses used in the palette and Hall argument. Its band sum therefore
gives \(O_s(h)\) colors. Choose an integer block separation
\(P>(s+1)(h-1)\), and place each label at
\[
x(a,b)=s(a-1)+P c(a,b).
\]
Different blocks cannot have an in-strip vertical rival. The total width
is \(O_s(h^2)\).

This is a fixed-scale extension of the P-only theorem. It supplies neither
the other rectangle exclusions nor the singleton sea. In particular, the
choice \(s=4\) gives within-block double gaps of eight without proving a
complete gap-eight construction.
