# Independent audit of interval reflection stability

9 November 2026. The theorem in [Reflection interval stability](reflection_interval_stability.md) passes an independent proof audit. It establishes an absolute, nonnumerical constant \(C\) such that
\[
 \min_{P\text{ a physical parity class}}|A\triangle P|
 \le C V(A)/h
\]
for every balanced \(A\subseteq[1,h]\), \(h\ge8\). Here \(V(A)\) counts an in-set reflection center and an in-set endpoint whose reflected endpoint is outside \(A\).

The two imported statements were checked in their sources. The uniform arithmetic removal statement is Theorem 1 of [Kráľ–Serra–Vena](https://arxiv.org/html/0804.4847). Theorem 13 of [Bollobás–Leader–Tiba](https://api.repository.cam.ac.uk/server/api/core/bitstreams/c0df9132-de28-4a03-b7d3-50bb078d3bf7/content) gives the precise asymmetric integer inverse theorem used: sumset excess at most the smaller cardinality minus three yields common-step progression hulls with at most that excess many holes.

The following points are essential to the application.

* The index sets \(E=\{i:2i\in A\}\) and \(F=[1,\lfloor h/2\rfloor]\setminus E\) are complementary. A solution \(x+y\in A\), \(x\in E,y\in F\), gives exactly an allowed reflection violation with physical endpoints \(2x,2y\). The embedding in a cyclic group of order \(4h+1\) introduces no modular solutions.
* After removal, \(S=E'+F'\) has size \(n+o(n)\), and its excess over \(|E'|+|F'|-1\) is \(o(n)\). In the mixed regime both summands have positive limiting density, so the inverse theorem applies. The two trimmed progression hulls cover all but \(o(n)\) points of \([1,n]\); their common step is therefore one or two.
* Step two makes \(S\), and then \(A^c\), close to a physical parity class. Step one makes \(E,F\) close to complementary endpoint intervals and \(S\) close to a central interval of length \(n\). The latter forces \(|E|=n/2+o(n)\), but also makes \(E\) close to the two outer quarter-intervals. Their symmetric difference from either endpoint half-interval has size \(n/2+o(n)\). Thus neither step supports a sequence remaining a positive distance from parity.
* The odd-height estimate uses missing majority-parity points \(t\) and inserted minority-parity points \(m\), with \(|t-m|\le1\). Its lower bound
  \[
  V(A)\ge (t+m)\bigl(\lfloor\lfloor h/2\rfloor/2\rfloor-(t+m)-1\bigr)
  \]
  follows from two disjoint endpoint-parity families. All their midpoints lie between their endpoints, so no boundary correction is missing.
* Qualitative closeness combined with this explicit near-parity estimate gives the asserted linear inequality. The remaining finite heights are legitimate: zero violations imply a full residue class by the minimum-gap reflection argument, and balance forces ordinary parity for \(h\ge8\).

This audit establishes the stated existence result, not an explicit usable value of \(C\). It needs no periodic extension or assumption on the number of parity changes.
