# The canonical component carries the linear sea entropy

Research note, 9 November 2026. This improves the canonical bound
\(\lambda_*(h)\ge(1-o(1))h/(4\log h)\) of
`odd_graph_entropy_square/sea_entropy_progress.md`, section 3, to the same
linear bound proved there for the whole parity sea shift.

**Theorem.** For every fixed \(0<\epsilon<1\) there is \(C_\epsilon\) such that,
for all sufficiently large \(h\),
\[
 \lambda_*(h)\ge\left\lceil\frac h2\right\rceil
 \exp\!\left(-C_\epsilon h^{-1+\epsilon}\right)
 \ge\frac h2-O_\epsilon(h^\epsilon).
\]
Consequently
\[
 \frac h2-O_\epsilon(h^\epsilon)\le\lambda_*(h)\le\rho_h\le h .
\]
The canonical component \(C_*\), into which every double inserts, has entropy of
the same order as the whole sea shift, and its known lower bound now equals the
best known lower bound for \(\rho_h\).

The new ingredient is a buffer. The earlier argument placed the free core
directly against the constant tails, so every core letter had to come from the
prime-row pool to kill two-pin events. Here the prime pool is used only in two
buffers of length \(L\). The buffers separate every core cell from every tail
cell by more than the span of any forbidden pattern, so core cells never meet a
pinned event and can use every odd row.

## 1. Setting and inputs

Fix the parity partition. Put \(W=1+\lfloor(h-1)^2/4\rfloor\) and \(L=2W\).
Every letter used below is an odd row. The inputs are:

1. **Covering family** (section 1 of `sea_entropy_progress.md`). If every black
   row is odd, a bi-infinite sea is valid exactly when it avoids four families of
   forbidden patterns: hidden tilted rectangles, horizontal axis rivals, mixed
   side/diagonal configurations (four specified black cells each), and
   one-corner intersections of two tilted rectangles (six specified cells).
   Singleton rivals and vertical rivals are impossible by parity.
2. **Span.** A tilted rectangle with sides \(\alpha(u,v)\), \(\beta(-v,u)\) has
   vertical span \(\alpha|v|+\beta|u|\le h-1\) and horizontal span
   \(\alpha|u|+\beta|v|\). The two horizontal terms have product
   \((\alpha|v|)(\beta|u|)\le((h-1)/2)^2\), and two positive integers with
   product at most \(P\) have sum at most \(1+P\). So the horizontal span is at
   most \(W\). Every pattern in the covering family is the union of the corners
   of at most two rectangles that share at least one corner column, so its
   specified columns lie in an interval of length at most \(2W=L\).
3. **Counts** (sections 2 and 3.2 of `sea_entropy_progress.md`). With
   \(B_4=O_\epsilon(h^{3+\epsilon})\) and \(B_6=O_\epsilon(h^{5+\epsilon})\)
   normalized unpinned patterns, and pinned counts with cells in a constant
   row-1 tail:

   | Family | Pins | Free columns | Count |
   |---|---:|---:|---:|
   | Four-cell | 1 | 3 | \(O_\epsilon(h^{2+\epsilon})\) |
   | Four-cell | 2 | 2 | 0 when both free rows lie in \(A_h\) |
   | Six-cell | 1 | 5 | \(O_\epsilon(h^{4+\epsilon})\) |
   | Six-cell | 2 | 4 | \(O_\epsilon(h^{3+\epsilon})\) |

   Here \(A_h=\{1+2p:\ p\le(h-1)/2\ \text{prime},\ p\equiv3\pmod4\}\), with
   \(k_h=|A_h|\sim h/(4\log h)\). The two-pin exclusion is the arithmetic lemma
   of section 3.1 there. Pinned events have at most two pins, as recorded there.
   The pinned counts are counts of geometric patterns; the alphabet enters only
   through probabilities and the two-pin exclusion.

## 2. The construction

Let \(k=\lceil h/2\rceil\) and let \(O_h\) be the set of odd rows, so
\(|O_h|=k\). For a core length \(m\ge1\), consider bi-infinite words
\[
 1^\infty\,T\,w\,T'\,1^\infty,
 \qquad |T|=|T'|=L,\quad T,T'\in A_h^{L},\quad w\in O_h^{m}.
\]
Call the \(m+2L\) letters of \(T w T'\) free, and the tail letters pinned.

**Separation.** Any forbidden pattern containing a pinned cell and a core cell
has two specified columns at distance at least \(L+1\). By the span bound this
is impossible. Likewise no pattern meets both tails. Hence every event
containing a pin has all its free cells in one buffer, where every letter lies in
\(A_h\).

**Event classes.** Choose the free letters independently and uniformly, from
\(A_h\) in the buffers and from \(O_h\) in the core. Each translate of a
covering pattern whose specified cells consistent with the pinned letters
defines a bad event on its free columns. Its probability is the product of
\(1/|A_c|\) over its free columns \(c\), and hence at most \(k_h^{-t}\) if it
has \(t\) free columns.

* Unpinned events, with free cells anywhere in \(TwT'\): through any free
  column there are at most \(4B_4\) four-cell and \(6B_6\) six-cell events.
* Pinned events: their free cells lie in a buffer, and the table bounds them.
  Two-pin four-cell events do not occur, since both free rows lie in \(A_h\).

**Pressure.** For every free column \(c\), the total probability of the events
through \(c\) is at most
\[
 4B_4k_h^{-4}+6B_6k_h^{-6}
 +3\,O_\epsilon(h^{2+\epsilon})k_h^{-3}
 +5\,O_\epsilon(h^{4+\epsilon})k_h^{-5}
 +4\,O_\epsilon(h^{3+\epsilon})k_h^{-4}
 =O_\epsilon\!\left(h^{-1+\epsilon}(\log h)^6\right).
\]
Only the worst alphabet size \(k_h\) is used, which overcounts core events.

**Local lemma.** Two events are dependent only if they share a free column;
pinned cells are constants. Give event \(E\) weight \(x_E=2\Pr(E)\). An event
has at most six free columns, so the weight of its neighbours is at most
\(12\) times the column pressure, which is below \(1/2\) for large \(h\). As in
section 2 of `sea_entropy_progress.md`, the elementary bound
\(\prod(1-x_j)\ge1-\sum x_j\) verifies the criterion, and the product form of
the local lemma gives
\[
 \Pr(\text{no bad event})\ge\prod_E(1-x_E)
 \ge\exp\Big(-4\sum_E\Pr(E)\Big)
 \ge\exp\!\left(-C_\epsilon(m+2L)h^{-1+\epsilon}(\log h)^6\right).
\]
The last step sums the column pressure over the \(m+2L\) free columns.

**Validity and the component.** A word avoiding all bad events has only odd
letters and avoids the covering family, so it is a valid bi-infinite sea. Its
windows are allowed states, and reading \(TwT'1^L\) from the state \(1^L\) is a
closed walk of length \(n=m+3L\) at \(1^L\). Every such walk lies in \(C_*\).
Distinct words give distinct walks. Therefore
\[
 \#\{\text{closed walks of length }m+3L\text{ at }1^L\}
 \ge k^m k_h^{2L}\exp\!\left(-C_\epsilon(m+2L)h^{-1+\epsilon}(\log h)^6\right).
\]
For fixed \(h\), the number of closed walks of length \(n\) at a vertex of
\(C_*\) is at most \(c_h n^{d_h}\lambda_*^n\). Taking \(n\)-th roots and letting
\(m\to\infty\),
\[
 \lambda_*(h)\ge k\exp\!\left(-C_\epsilon h^{-1+\epsilon}(\log h)^6\right).
\]
Absorbing the logarithms into a smaller \(\epsilon\) proves the theorem. \(\square\)

## 3. Self-audit

* **Completeness of the covering family needs odd letters only.** Row 1, every
  row of \(A_h\), and every row of \(O_h\) are odd.
* **Span of mixed and six-cell patterns.** Two rectangles sharing a corner have
  a common column, and each spans at most \(W\) columns, so the union spans at
  most \(2W\). The buffer has \(L=2W\) columns, so a pinned cell and a core cell
  are at least \(L+1\) apart. This is strict, as required.
* **Two-pin exclusion.** Section 3.1 of `sea_entropy_progress.md` needs both
  free rows of the form \(1+2s\), \(1+2t\) with distinct primes
  \(s,t\equiv3\pmod4\). Both free cells of a pinned event lie in one buffer, so
  this holds. The degenerate case \(s=t\) is excluded there by \(t>s\).
* **Row-1 cells in the core.** The core alphabet contains row 1. Events with
  row-1 core cells are unpinned events and are already in \(B_4\) and \(B_6\).
  The pin count of a pattern refers only to tail cells.
* **Heterogeneous alphabets.** The local lemma needs only that the free letters
  are independent and that each event is determined by its free columns. Mixed
  alphabets change probabilities, never dependency sets.
* **Common white corners outside the free region.** Events are specified by
  their required black cells only. Common corners need not be white, as stated
  in section 1 of `sea_entropy_progress.md`.

## 4. Consequences and limits

1. **Any local-lemma entropy bound transfers.** The argument uses nothing about
   the core alphabet except its pressure. Any odd-row alphabet whose unpinned
   pressure is \(o(1)\) gives the same lower bound for \(\lambda_*\) as for
   \(\rho_h\). The buffers cost nothing in the growth rate.
2. **Dominance to first order is now an upper-bound problem.** Since
   \(\lambda_*\ge h/2-O(h^\epsilon)\), the growth base \(R\) of
   \(b_{\rm par}(m)\) in Proposition 1.3 of `dominance_attempt.md` satisfies
   \(h/2-O(h^\epsilon)\le\lambda_*\le R\le\rho_h\le h\). Any upper bound
   \(\rho_h\le(1/2+o(1))h\) would give \(\lambda_*\sim R\sim\rho_h\sim h/2\),
   fixing the growth base of the parity counting formula to first order without
   proving exact dominance.
3. **Mixed-parity words are the open part.** Words using both parities face
   three-cell singleton-rival events (Lemma 3.1 of `dominance_attempt.md`).
   About \(h^{3+o(1)}\) right-angle patterns meet a column, each with
   probability about \(h^{-3}\) for a uniform letter, so a uniform word over all
   rows sees \(h^{o(1)}\) forced-parity violations per column. This heuristic
   leaves room for \(\rho_h/h\) anywhere in \([1/2,1)\). No upper bound below
   \(h\) is proved.
4. **Exact dominance is unchanged.** The theorem does not exclude a recurrent
   component outside \(C_*\) with root above \(\lambda_*\). It shows only that
   such a component would have root above \(h/2-O(h^\epsilon)\). A component
   using one parity on all but a vanishing density of columns could still lie
   in the window between \(\lambda_*\) and \(\lceil h/2\rceil\); only a component
   with root above \(\lceil h/2\rceil\) is forced to use both parities on a
   positive density of columns.
