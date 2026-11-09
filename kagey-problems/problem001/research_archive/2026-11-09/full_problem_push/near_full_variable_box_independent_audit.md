# Audit of near-full Cartesian-box stability

9 November 2026. The proof in `near_full_variable_box_stability.md` passes
independent review. The interval reflection-stability theorem is used in
its already audited form; no stronger quantitative version is required.

The following points were checked explicitly.

* In the light-color branch, summing \(n_s(k)\le2M\) over at most
  \(\lfloor(h-1)/2\rfloor\) shifts gives \(V(B_s)\le Mh\). The cited
  reflection theorem applies at every height at least eight, so it needs
  no additional asymptotic threshold.
* In the heavy/heavy branch, both intermediate positions in the two-step
  phase argument lie between \(x\) and \(x+p\). Thus period \(p\) and the
  complement shift \(a_0\) hold for every stated finite index.
* For the equal-vertical-increment rectangles, each corner column \(j\)
  satisfies \(j+p\le m\). The bound
  \(1+\max(5h/4,10)+(2h-2)<4h+20\) leaves room for both placements.
* The loss \(8M\) is correct. There are eight fixed corner-column
  incidences across the two complementary placements. At each incidence,
  the row is an injective function of the vertical translation. At most
  \(M\) relevant rows are omitted there. This count remains valid when the
  placement with three matches depends on the translation, or when some
  physical columns occur in both placements.
* The shift-four/shift-six comparison has at least one good starting row.
  The induction to distance \(h-R\) uses at least \(R=32M+16>3D\)
  starting rows at its last step, with \(D=8M\). The discarded long
  distances contribute less than \(R^2/2\), and the minority estimate
  comfortably gives the stated \(100M\) bound.
* For the small templates in the final phase argument, the admissible
  vertical translations form an interval of length at least \(h-4\).
  Pairing translations at distance one or two gives more than the stated
  \(h/2-4\) three-match contexts. The union bounds \(4KM\) and \(4M\)
  therefore leave a surviving context under the displayed hypothesis.
* On a five-column interval, the first phase relation gives
  \(d_x=d_{x+2}\) and \(d_{x+1}=d_{x+3}\), while the second gives
  \(d_x+d_{x+3}=\kappa\). Hence consecutive differences alternate with
  increment \(\kappa\). Overlapping five-column intervals cover every
  difference, including those at both endpoints. The exact phase formula
  therefore holds on the entire finite word.

The scope statement is necessary and correct: this is a theorem about a
Cartesian box in which every choice avoids the two specified rivals. It
does not show that an arbitrary high-entropy component contains such a box,
and it does not prove general component dominance.
