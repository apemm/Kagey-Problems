# Exact coloring certificates for an actual CRT chain

9 November 2026. The graph on vertices 0 through 149 used in the rational 4/3 CRT-chain probe requires at least six colors. This conclusion has an independent standard-library proof check and an actual-strip geometric realization. It does not prove that the infinite graph has unbounded chromatic number.

## 1. Arithmetic graph and coloring formulas

Vertices i,j are joined exactly when at least one of

    25[2(j−i)]² ± 6*375*[2(j−i)] + 375²

is an integer square. Independent direct square tests, without importing the probe's divisor enumeration, give 1,289 edges. The coloring variables are C*i+c+1. The independently reconstructed formulas impose exactly one color at each vertex, distinct colors on adjacent vertices, and fix the clique {0,23,68,133} to four distinct colors. This last restriction loses no coloring: a permutation of color names always puts a proper coloring into that form, for every C≥4.

The four-color formula has 600 variables and 6,210 clauses. Ignoring deletion lines, its four proof additions are

    −484;   −43 or 574;   574;   the empty clause.

For each addition, negating that clause and performing unit propagation against the original formula and preceding additions reaches a contradiction. The respective propagation counts are 210, 231, 204 and 248. Keeping clauses that the producer deleted is sound here because every retained clause is an original clause or an already proved consequence.

The five-color formula has 750 variables and 8,099 clauses. All 2,305 nondeletion additions likewise pass reverse unit propagation, ending with the empty clause. Thus the lower bound is six colors, rather than just five. No SAT-solver library is imported by either independent checker.

The reduced 32-vertex graph has 100 edges. Its 628-clause four-color formula passes all 26 proof additions, and its supplied five-color assignment is checked directly on every edge. This smaller graph is therefore exactly five-chromatic.

## 2. Actual strip embedding

Use t=18,375, k_j=98j, and the 150 labels

    a_j=9,409+294j,   b_j=a_j+18,375.

The independent checker chooses

    h=80,998,   p=2,024,977,   q=2,025,029,

verifies primality by exact trial division, and checks p,q>25h. For each label it computes the unique center x_j in [0,98pq) with

    98|x_j,   3x_j=4a_j mod p,   3x_j=4b_j mod q.

It then verifies x_j−x_0=392j as an equality of integers, without wraparound. Every one of the 1,289 edges has an odd integral diagonal length and an opposite-parity vertical completion pair inside [1,h]. The complete parity family supplies the corresponding axis-rival owner column.

The check verifies more than the four points of each diagonal: for each common white point (x,y), its necessary CRT congruence for an inserted endpoint of parity y fails. It is consequently white even in the full complete-parity scaffold. The axis owner differs from the common white column and both diagonal columns. Equal midpoint sums, equal diagonal norms, four distinct corners, and the symmetric difference of the tilted and axis rectangles are checked exactly. These are actual vertical presentation collisions, not just rational norm identities without containment.

## 3. Saved audit trail and scope

The independent sources are [verify_crt_chain_nonfourcolorable.py](verify_crt_chain_nonfourcolorable.py) and [verify_crt_chain_color_proof.py](verify_crt_chain_color_proof.py). The first checks the full geometry and the four-addition proof. The second accepts the color count and either the full or reduced vertex set. All arithmetic uses exact integers.

Outputs are [crt_chain_nonfourcolorable_independent_check.json](crt_chain_nonfourcolorable_independent_check.json), [crt_chain_t375_n150_5color_independent_check.json](crt_chain_t375_n150_5color_independent_check.json), and [crt_chain_small_4color_independent_check.json](crt_chain_small_4color_independent_check.json). They record source/proof hashes and propagation traces, and the first records every in-strip rival.

This certifies a six-color lower bound for an actual finite P-chain graph and hence for the countable Cayley graph in the preceding reduction. It says nothing yet about a finite uniform upper bound for that countable graph, and a coloring of the P graph alone does not eliminate mixed collisions or construct the singleton filling.
