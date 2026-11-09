# Odd-row components at heights seven and eight

9 November 2026. These computations concern the restricted alphabet
\(\{1,3,5,7\}\) and the full ordinary-parity pair set at the stated physical
height. They do not classify the unrestricted height-eight sea.

| Physical height | Reachable states | Unique recurrent component | Certified Perron interval |
|---|---:|---:|---|
| 7 | 2,835,767 | 2,794,328 | [2.771037, 2.771038] |
| 8 | 2,463,157 | 2,421,827 | [2.715792, 2.715793] |

Every other component is a transient singleton. All four constant-row
states belong to the recurrent component, which is therefore primitive.
The input compiler first generates all forbidden patterns at the physical
height, then restricts their letters to the odd alphabet. The binary graph
header's height field is four, the alphabet size, rather than the physical
height. The input metadata preserves both quantities.

Independent graph traversal verifies the SCC certificates. Independent
integer Collatz inequalities verify the two Perron intervals. The files are
sea_packed_h7_odd.scc_verified.json,
sea_packed_h8_odd.scc_verified.json,
sea_packed_h7_odd.perron.31337.verified.json, and
sea_packed_h8_odd.perron.30581.verified.json.

## A protected prefix can force a parity change

At physical height seven, the singleton word
\[
 (3,5,3,5,5,3,7,3)
\]
is valid in the normalized full-parity sea. Its only admissible next row is
six. In particular, none of the four protected odd letters can follow it.
Its full-sea residual state lies in the canonical recurrent component.

The coordinate certificate in protected_dead_prefix_h7.json gives, for
each proposed odd next letter, two distinct rectangles with the same white
presentation. An independent equal-diagonal generator checks the prefix
and all four obstructions inside a width-49 strip, with twenty white
columns on either side. It examines 28,451 rectangles. The prefix itself
has no presentation collision there.

This distinguishes two statements. Every recurrent odd-row component
reaches the constant states at these two heights. A finite odd-row prefix
need not have an odd-row continuation. A bridge argument for arbitrary
prefixes must account for this obstruction.

The height-nine odd-row graph was not completed: a capped exploration
reached 6,009,519 states after processing 1,810,000. It supplies no SCC
classification or spectral certificate.
