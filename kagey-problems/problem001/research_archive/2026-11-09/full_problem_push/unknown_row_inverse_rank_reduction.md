# A finite-rank reduction for the remaining aggregate inverse problem

9 November 2026. The constant-column-phase inverse and the protected-row inverse are proved in the linked notes. This note records an exact algebraic reduction for the case in which both the row coloring and the column phase are arbitrary. The required robust integration step remains open.

Let
\[
 W(x,y)=1+c(y)+t(x)\pmod2,
\]
so \(W=1\) means that the row color agrees with the column phase. For one primitive direction \((a,b)\), use rotated coordinates
\[
 G_{ij}=W(x_0+ai-bj,\ y_0+bi+aj).
\]
Put \(D=a^2+b^2\). Whenever the indicated entries lie in the index square,
\[
 \begin{aligned}
 G_{i+sb,j+sa}+G_{ij}
 &=c(y+sD)+c(y),\\
 G_{i+sa,j-sb}+G_{ij}
 &=t(x+sD)+t(x).
 \end{aligned}
\tag{1}
\]
Thus the two orthogonal shifts isolate derivatives of the two original one-dimensional words.

If \(G\) differs from an \(\mathbb F_2\)-rank-\(r\) matrix in at most \(E\) entries, each matrix on the left of (1), on its rectangular overlap, differs from a rank-at-most-\(2r\) matrix in at most \(2E\) entries. This holds for every permitted \(s\), not only for \(s=1\).

Induced-three-corner removal makes \(G\) close to a union of bicliques. Retaining components with both sides at least \(dK\) gives rank \(O(1/d)\), but deleting the other components costs \(O(dK^2)\). This is the main quantitative difficulty: a fixed-rank repair lemma whose error tends to zero for fixed \(r\) cannot automatically be applied with error \(d\) and rank \(r\asymp1/d\). Its conditioning constants may grow faster than \(1/d\). The successful constant-phase proof avoids this issue by comparing the full biclique union and deleting small components only after the translation action is identified.

## An arithmetic fact for a possible period argument

For odd positive \(a,b\), define the four integers
\[
 \begin{aligned}
 F_{00}&=ab(a^2+b^2),\\
 F_{10}&=(a+2)b((a+2)^2+b^2),\\
 F_{01}&=a(b+2)(a^2+(b+2)^2),\\
 F_{11}&=(a+2)(b+2)((a+2)^2+(b+2)^2).
 \end{aligned}
\]
Then
\[
 \gcd(F_{00},F_{10},F_{01},F_{11})\mid10.
\tag{2}
\]
Each integer has exactly one factor of two, since its two linear factors are odd and its norm is \(2\bmod8\).

Suppose an odd prime \(p\) divides all four integers. If \(p\) divides none of \(a,a+2,b,b+2\), it divides all four norms. Subtracting adjacent norms gives \(a=b=-1\bmod p\), and then a norm is \(2\bmod p\), a contradiction.

By symmetry, suppose \(p\mid a\). It cannot also divide either \(b\) or \(b+2\): the remaining opposite corner would have norm \(8\bmod p\). Thus \(b,b+2\) are units. The two norms in the other row must vanish, so subtraction gives \(b=-1\bmod p\). Since \(a+2=2\bmod p\), this forces \(p=5\).

Finally, \(25\) cannot divide all four integers. The first-row products would force \(25\mid a\), since their other factors are units modulo five. The other two norms would force \(b=-1\bmod25\). Either norm would then equal \(5\bmod25\), a contradiction. The same argument applies if the divisible linear factor was \(a+2\), \(b\), or \(b+2\). This proves (2).

Consequently, if a future uniform argument supplied approximate periods dividing \(C\,ab(a^2+b^2)\), with the same fixed \(C\) for four neighboring good directions, their common period would divide \(10C\). The lcm of the four direction-dependent factors is at most
\[
 a(a+2)b(b+2)
 (a^2+b^2)((a+2)^2+b^2)
 (a^2+(b+2)^2)((a+2)^2+(b+2)^2)
 =O(R^{12}).
\]
Choosing comparable directions below \(h^{1/32}\) would keep that lcm \(o(h)\), as required by the Chinese-remainder comparison.

These observations identify a possible next step. They do not establish that approximate derivative periods integrate without error accumulation, nor that the rank truncation above is quantitatively adequate.
