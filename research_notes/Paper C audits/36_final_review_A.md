# 36 Final review A (abstract and introduction)

Files touched: abstract in problem131_chains.tex and problem131_chains_sn.tex, and sec_intro.tex. Statements were compared read-only with Theorems thm:layer, thm:layer-counts, thm:first, thm:crossing and prop:layer-cubic.

## Abstract (both files)
1. Old: "For irreducible faces the crossing is unique for $T\le\varepsilon N$"
   New: "For two irreducible faces the crossing is unique for large $N$ in $1\le T\le\varepsilon N$"
   Reason: Theorem B(ii) concerns a pair and gives exactly one root only for large N.
2. Old: "The counts obey a lattice form with extra error $T^2/N$."
   New: "... extra error $T^2/N$ for $T\le\varepsilon_1\sqrt N$."
   Reason: thm:layer-counts needs $T\le\varepsilon_1N^{1/2}$.
3. Old: "Donsker and Varadhan functional of the chain $I+(T/N)Q$ at $n/N$"
   New: "Donsker and Varadhan functional at $n/N$"
   Reason: the chain was named in the first sentence. Needed to keep the journal abstract under 250 words (now about 248 with math counted as one word).

## Abstract (problem131_chains.tex only)
4. Old: "each face crosses a vertex exactly once"
   New: "each face of at least 2 states crosses a vertex exactly once"
   Reason: a vertex does not cross itself (Theorem C(i) has 2 <= k).

Note: the _sn abstract has never contained the complete-graph sentence. I did not add it because the 250 word cap leaves no room. So the two abstracts are identical except for that last sentence.

## sec_intro.tex
5. Old: "a local limit theorem for the count vector on each face, ... Up to $O(1)$,"
   New: "... on each face that satisfies the condition (H) below, ... On compact subsets of the open face, up to $O(1)$,"
   Reason: Theorem A needs (H) and a compact set of the open face for the first display.
6. Old: "so the Bessel forms hold for the counts as well."
   New: "so the Bessel forms hold for the counts with $T^2/N$ added to the error."
   Reason: thm:layer-counts(c) adds $T^2/N$ to each error bound.

No trim was made in sec_intro.tex. No repeated sentence was found that adds nothing.
