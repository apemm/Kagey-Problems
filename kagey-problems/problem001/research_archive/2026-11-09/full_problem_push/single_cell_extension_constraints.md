# Exact one-point extensions of an identifying set

9 November 2026. Let \(B\) be an identifying set of black points on a grid with both dimensions at least four. Write \(\mathcal P_B=\{R\setminus B:R\text{ is a rectangle}\}\). For a white point \(p\), the enlarged set \(B\cup\{p\}\) is invalid exactly when one of the following conditions holds:

1. Some rectangle has presentation \(\{p\}\).
2. There are presentations \(P,Q\in\mathcal P_B\) with \(P=Q\cup\{p\}\) and \(1\le|Q|\le2\).

The first condition makes a hidden rectangle, which is forbidden on these grids. The second condition makes the two presentations equal after adding \(p\).

For the converse, two rectangles that both contain \(p\) cannot acquire equal presentations for the first time: adding \(p\) back to those presentations would make their original presentations equal. A new collision therefore consists of one rectangle containing \(p\) and one not containing it. Their old presentations differ exactly by \(p\). The smaller presentation cannot have three or more points, since two distinct rectangles cannot share three vertices. If it is empty, the larger presentation is \(\{p\}\), which is covered by the first condition. This proves the characterization.

Consequently, exact unary extension restrictions can be computed by storing the presentations of weak rectangles, those with at least two black corners, and scanning all rectangles with at least one black corner. Only presentations of sizes one, two, and three need inspection. There is no need to compare every pair of rectangles.

`single_cell_extension_constraints.py` implements this test independently of the lazy SAT clauses. On the verified height-15 scaffold with 56 double slots and empty sea columns, it finds **at least ten individually permissible rows in every sea column, including at least five odd rows**. The computation takes 0.89 seconds. Its data are in `constant_sea_h15_cadical195_seed17_empty_unary.json`.

These row domains describe individually valid additions. Simultaneous choices can still collide, so nonempty domains do not prove that a full sea filling exists.
