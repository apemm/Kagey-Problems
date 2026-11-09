# Independent audit of near-full row-class box stability

9 November 2026. The theorem and the finite-width obstruction in [Near-full variable box stability](near_full_variable_box_stability.md) pass an independent analytical audit.

The theorem assumes a balanced row partition, at most \(M\) omissions from the selected block in each column, height \(h\ge C(M+1)\), and width \(m\ge4h+20\). Its hypothesis applies to every word in the Cartesian box. Under this hypothesis the row partition is within \(O(M)\) rows of an ordinary or quadratic law, and the column phase satisfies the corresponding law exactly. This does not classify arbitrary high-entropy components.

The key steps check as follows.

* A reflection distance with more than \(2M\) bad centers forbids two equal phases of the corresponding color. The middle alphabet has another available row, so both displayed vertical corners can be made white. The two heavy colors yield a period \(p=a_0+b_0\) and a phase-complementing shift \(a_0\) on the stated finite domain.
* For even \(a\), side vectors \((a/2,a)\) and \((-2a,a)\) are orthogonal. Their four column coordinates are distinct, with span \(5a/2\). All their complemented contexts fit inside width \(4h+20\), because \(p\le2h-2\). The separate \(a=3\) geometry supplies shift six. At most \(8M\) vertical placements are lost over the two contexts.
* Three shift-four identities and two shift-six identities fit a common domain and force the shift-four constant to vanish. Induction controls every multiple of four away from the last \(R=32M+16\) rows. Composing shift six with a multiple of four adds at most another \(8M\) errors. The resulting count of differing same-parity row pairs is at most \(20Mh\), yielding at most \(100M\) exceptional rows.
* After obtaining the row approximation, the two small four-column rectangle templates eliminate every erroneous phase XOR by a surviving vertical translation. The constants \(h/2-4\) and \(4(K+1)M\) give the claimed margin. On each five-column interval the identities force the phase increments, including at the two ends; neighboring intervals propagate the same law.
* The light-color branch uses the independently checked interval reflection-stability theorem. The \(M=0\) case is covered by the exact finite full-box theorem.

The additional fixed-width example is also valid for its stated two-rival scope. In a width-\(m\) right triangle, the product of the nonzero vertical legs is at most \((m-1)^2\). A triple meeting both retained row regions violates this bound. If only its completion crosses the row-color switch, each leg exceeds the omitted-band width \(R\), again violating the bound. For a vertical alternative diagonal spanning the two regions, \(0<L-v<1\) excludes integral length; within one region the vertical expansion is less than \(R\). Exactly \(R\) rows are omitted from the selected balanced block, while the row coloring remains a linear distance from all protected laws as height grows.

No further defect was found in the constants or finite-boundary indices.
