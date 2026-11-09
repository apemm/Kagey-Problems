# Reflection stability near parity and a calibration for the remaining case

9 November 2026. The proposed lower bound
\[
 V_A\ge c p^2,
\]
where p counts adjacent pairs in a balanced row block A, remains unproved.
Such a bound would combine with Section 3 of
`approximate_reflection_closure.md` to give global parity distance
\(O(V_A/h+\sqrt{V_A}+1)\), hence \(O(\sqrt{Mh}+M+1)\) when
\(V_A\le Mh\).

Any universal constant c in this particular inequality is at most \(1/8\).
For height \(h=4n\), take
\[
 A=[1,n]\cup[3n+1,4n].
\]
This is balanced and has \(p=2n-2\). A reflection centered at
\(a\in[1,n]\) cannot reach the other A interval: its reflected points are
at most \(2a-1\le2n-1\). Its mismatched endpoint pairs therefore number
\(\max(0,2a-n-1)\). By reflection of the whole strip,
\[
 V_A=2\sum_{a=1}^n\max(0,2a-n-1)
     =2\left\lfloor\frac{n^2}{4}\right\rfloor.
\]
Consequently \(V_A/p^2\to1/8\). This family is a constraint on a possible
lower-bound constant, not a counterexample to the existence of such a bound.

`reflection_stability_probe.py` enumerates every balanced block at heights
8 through 20, computes the reflection count by direct endpoint comparison,
and records the smallest ratios \(V_A/p^2\) and
\(V_A/(|A_{\rm even}||A_{\rm odd}|)\). The exact output is
`reflection_stability_probe.json`. These finite data do not establish a
uniform inequality.

A possible injection would relate adjacent A pairs to adjacent complementary
pairs. Balance makes their counts differ by at most two. However, midpoint
pairing can land in the complementary block, and repeated reflection can
leave the finite strip. No boundary-uniform charging argument resolving
these cases is supplied here.

## A linear bound in the minority-parity regime

There is a direct bound when the balanced block is already moderately close
to a parity class. Let \(h=2n\), \(|A|=n\), and
\[
 m=\min(|A\cap2\mathbb Z|,|A\setminus2\mathbb Z|).
\]
Then
\[
 \boxed{V_A\ge2m\left(\left\lfloor\frac n2\right\rfloor-2m\right).}
 \tag{1}
\]
In particular, if \(n\ge4\) and \(m\le n/8\), the distance r from A to its
nearer parity class satisfies
\[
 \boxed{r=2m\le16V_A/h.}
 \tag{2}
\]
Thus \(V_A\le Mh\) gives \(r\le16M\) in this regime.

Assume first that the majority of A lies on odd rows. Exactly m odd rows are
missing from A, and exactly m even rows have been inserted.

For each missing odd row \(u=2j-1\), choose an odd endpoint
\(v=2i-1\) with \(i=j\pmod2\). Its midpoint \(i+j-1\) is odd.
There are at least \(\lfloor n/2\rfloor\) choices of i. At most m choices
have \(v\notin A\), and at most m have a midpoint outside A, because the
midpoint is an injective function of i. Every remaining choice gives one
reflection violation centered in A. Distinct missing endpoints give
distinct violations, since a mismatched pair has exactly one endpoint
outside A. This supplies
\(m(\lfloor n/2\rfloor-2m)\) violations with odd endpoints.

For each inserted even row \(u=2j\), choose an even endpoint \(v=2i\)
with i opposite in parity to j. The midpoint \(i+j\) is odd. Again at least
\(\lfloor n/2\rfloor\) choices are available; at most m have \(v\in A\),
and at most m have a missing midpoint. The remaining choices give the same
lower count of violations with even endpoints. These are disjoint from the
first family. Every midpoint lies between its endpoints, so there is no
boundary loss.

If A has an even-row majority, interchange odd and even in the two arguments.
The same index-parity counts apply. This proves (1). Finally,
\[
 V_A\ge m(n/2-1)\ge mn/4
\]
under the hypotheses of (2), which proves that conclusion.

The remaining balanced even-height regime is
\(n/8<m\le n/2\). The argument does not prove a positive uniform bound
there, and no such general interval bound is claimed in this note.
