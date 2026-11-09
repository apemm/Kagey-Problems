# A dilute parity-defect bound retaining the bulk pressure

9 November 2026. This is a first Peierls-type estimate toward unrestricted parity entropy. It treats flipped columns separated by more than twice the support memory. Dense clusters and long domain walls are not covered. Independent review checked the rooted geometry, overlap bounds, thinning argument, and profile sum.

Let \(L=2W_h=O(h^2)\). Let \(r_{\rm O}(h)\) denote the all-odd protected-phase entropy, and let \(\mu_{\rm O}(h)\) be its exact minimal four/six support mean from [crossed_codegree_and_avoidance.md](crossed_codegree_and_avoidance.md). Let \(r_{\rm dil}(h)\) be the entropy of valid parity seas in which any two even-row letters are separated by more than \(2L\).

**Theorem.** There is an absolute \(c>0\) such that, for every fixed \(\varepsilon>0\),
\[
 \log r_{\rm dil}(h)
 \le \log r_{\rm O}(h)
      +O_\varepsilon(h^{-2+\varepsilon})
      +\exp[-c(\log h)^2].
\tag{1}
\]
Thus isolated parity defects do not alter the first-order protected-phase pressure. This does not yet compare the full ordinary-parity component with the quadratic partition.

## 1. Three-variable events at a flipped column

Fix a set \(S\) of \(n\) columns, separated by more than \(2L\), and prescribe even rows at S and odd rows elsewhere. Initially keep S at distance at least L from the two ends of a finite word.

For each \(j\in S\), take every tilted rectangle with four distinct columns whose four corner rows are odd and one corner W lies in column j. Require its other three corners to be black. The fourth corner W is necessarily white because the selected row in column j is even, and the parity pair set gives its singleton axis rival. Each such condition is therefore a forbidden event on only three row variables.

All variables of this event lie within distance L of j. Hence none is another flipped column, and event families belonging to different j have disjoint variable sets.

Let \(\nu_j\) be the mean number of these events. The all-odd fixed-corner degree from [six_support_leading_pressure.md](six_support_leading_pressure.md) gives
\[
 \nu_j\sim \frac{20}{3\pi^2}(\log h)^2.
\tag{2}
\]
Indeed their number is four times the phase-compatible rectangle count per translation, asymptotic to \(5h^3\log^2h/(6\pi^2)\), and each event has probability \((2/h)^3(1+O(1/h))\).

The three black cells determine their rectangle and completion uniquely, so these events have no multiplicity.

## 2. Their dependency and overlap costs are bounded

For a fixed free column x, there are \(O(h^3)\) three-cell events rooted at j that use x: choose the black point in column x and the completion point in column j in \(h^2\) ways, then use the \(O(h)\) two-corner rectangle bound. Thus the sum of their probabilities incident with any column is \(O(1)\).

For a fixed black point P, there are \(O(h^2)\) events rooted at j containing P. Therefore pairs sharing exactly one assignment have total joint weight
\[
 O\bigl((h^3\log^2h)\,h^2\,h^{-5}\bigr)
 =O(\log^2h).
\]
For two fixed black points in different columns, there are only \(O(1)\) rooted events: the completion lies in the specified column j and on one of the perpendicular lines or Thales circles determined by the two points. A vertical perpendicular line is at the column of one of those black points, hence cannot coincide with column j. This leaves at most constantly many intersections. Pairs sharing two assignments contribute only \(O(\log^2h/h)\).

Consequently the total joint overlap weight within one rooted family is \(O(\log^2h)\). Families rooted at different flipped columns are independent.

## 3. Retain the ordinary four/six events away from S

Retain every all-odd minimal four/six event whose black support avoids S. These events remain forbidden in the prescribed mixed-parity word. Their mean is
\[
 m\mu_{\rm O}(h)-O_\varepsilon(nh^{-1+\varepsilon})+O_h(1),
\tag{3}
\]
because the incident bulk probability at any column is \(O_\varepsilon(h^{-1+\varepsilon})\).

Their bulk overlap weight is \(O_\varepsilon(mh^{-2+\varepsilon})\). The joint overlap weight between the rooted three-cell events and the retained bulk events is
\[
 O_\varepsilon(nh^{-1+\varepsilon}).
\tag{4}
\]
To see this, fix a rooted three-event and r of its assignments. A size-s bulk support through those r points has \(O_\varepsilon(h^{s-r-1+\varepsilon})\) choices by the extension table, and the joint probability is \(O(h^{-(s+3-r)})\). There are \(O(h^3\log^2h)\) rooted events per flipped column. Sum over the finitely many possibilities \(s\in\{4,6\}\) and \(1\le r\le3\).

## 4. Thin only the rooted singleton events

Independently retain each rooted three-event indicator with a fixed probability \(\theta>0\), using an auxiliary Bernoulli marker. Keep all bulk indicators unchanged. Avoiding the original events implies avoiding this thinned family, so an upper bound for the latter is valid for the original word.

The shared-variable graph, with the independent markers included, is a strong dependency graph. Its neighbor probability sum is \(O(\theta)+o(1)\). Its total mean is at least
\[
 m\mu_{\rm O}(h)
 +\theta c_0 n\log^2h
 -O_\varepsilon(nh^{-1+\varepsilon})-O_h(1),
\]
for some absolute \(c_0>0\). Its joint overlap weight is at most
\[
 C\theta^2n\log^2h
 +O_\varepsilon(\theta nh^{-1+\varepsilon})
 +O_\varepsilon(mh^{-2+\varepsilon}).
\]

Apply the same arbitrary-indicator Suen inequality used in the protected-phase expansion. Choose \(\theta\) as a sufficiently small absolute constant. The quadratic overlap term is then at most half the rooted-event mean, after the bounded factor \(e^{2\delta}\) is included. For large h, the other terms involving n are also smaller than a fixed multiple of \(n\log^2h\). Thus
\[
 \Pr(\text{word valid}\mid\text{prescribed parity profile }S)
 \le
 \exp\!\left[
 -m\mu_{\rm O}(h)-c n\log^2h
 +O_\varepsilon(mh^{-2+\varepsilon})+O_h(1)
 \right].
\tag{5}
\]

This retains the ordinary bulk pressure. Applying a standalone upper bound only to the singleton events would not have been enough for comparison with \(r_{\rm O}\).

## 5. Sum over separated defects

Put \(k=\lceil h/2\rceil\). The product-space size for the profile S is at most \(k^m\), since there are no more even rows than odd rows. Sum (5) over separated sets S; dropping the separation condition only enlarges the upper bound:
\[
 \sum_S e^{-c|S|\log^2h}
 \le(1+e^{-c\log^2h})^m.
\]
The bounded end strips affect only a factor depending on h. Therefore
\[
 \log r_{\rm dil}(h)
 \le \log k-\mu_{\rm O}(h)
       +O_\varepsilon(h^{-2+\varepsilon})
       +e^{-c\log^2h}.
\]
The protected-phase expansion identifies the first two terms with
\(\log r_{\rm O}(h)+O_\varepsilon(h^{-2+\varepsilon})\), proving (1).

The same method applies to isolated flips from a checkerboard or quadratic protected class, with its corresponding row partition and bulk mean. In those cases, a flipped column can have one more available row than its unflipped class. The resulting factor \(\exp[O(n/h)]\) is absorbed by the defect penalty. For the ordinary parity problem, the unresolved profiles are those with interacting defect clusters. Controlling those clusters is necessary before replacing \(r_{\rm dil}\) by the full sea entropy.

