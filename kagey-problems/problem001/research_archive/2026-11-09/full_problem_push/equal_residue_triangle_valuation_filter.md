# A finite-level filter for equal-residue triangles

9 November 2026. A stronger column congruence removes the opposite-parity
label-root triangles in a substantial part of the all-zero profile
family. This is a local exclusion lemma, not a complete placement or
threshold improvement.

Fix two residues \(\alpha,\beta\pmod {49}\) with
\(\alpha\equiv\beta\pmod7\) but
\(\alpha\not\equiv\beta\pmod {49}\). Every assigned label
has its odd endpoint congruent to \(\alpha\) and its even endpoint
congruent to \(\beta\). Choose odd \(L\) satisfying
\[
 L\equiv\alpha\pmod7,\qquad
 L\not\equiv\alpha,\beta\pmod {49}.
\tag{1}
\]
Such a choice exists in \([1,98]\): the seven odd representatives
of the fixed modulo-seven class cover all seven possible residues
modulo 49, and at most two are excluded. Use an all-zero period-49
profile with this low row, with the usual bulk and margin hypotheses.
The original finite-profile existence proof permits this fixed
enlargement of the set of lower rows.

Place all assigned label columns in \(343\mathbb Z\). Consider
a prospective tilted right angle at one label point of row \(a\),
with a point of the opposite physical parity from another label at
row \(c\), and a sea point of row \(s\). Translate the root
column to zero and write the other column offsets as \(\Delta,x\).
Orthogonality requires
\[
 \Delta x=-(c-a)(s-a).
\tag{2}
\]
The two selected endpoints come from different fixed residue classes,
so \(v_7(c-a)=1\), regardless of which endpoint is the root.

For \(s=L\), (1) gives \(v_7(s-a)=1\). The right side of
(2) has valuation exactly two. The left side has valuation at least
three, since \(343\mid\Delta\); a low binary sea column is a
unit modulo seven. This is impossible.

For \(s=H\), the profile has \(H-L\not\equiv0\pmod7\),
so the right side has valuation one, again impossible. For a filler
row \(s=F_j\), its normalized row residue is three, distinct from
the inserted residue zero. The right side again has valuation one,
whereas the sea column is now divisible by seven and the left side
has valuation at least four. Thus every sea-level case is excluded.

The conclusion concerns exactly the opposite-parity, two-label
triangles rooted at a label. Same-parity triangles retain their
separate safe-completion analysis. Triangles on three labels and other
mixed supports are not covered.

The column restriction has constant density, and the residue classes
here form a constant number of blocks. However, it leaves unoccupied
holes in phase zero of the period-49 profile. The horizontal
full-occupation lemma therefore cannot be invoked. Labels whose two
endpoints are equal modulo 49 also remain outside this lemma. These
two limitations prevent an immediate improvement to the all-height
threshold.
