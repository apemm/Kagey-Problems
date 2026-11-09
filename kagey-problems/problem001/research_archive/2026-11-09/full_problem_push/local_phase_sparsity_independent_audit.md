# Independent audit of uniform local phase sparsity

9 November 2026. [uniform_local_phase_sparsity.md](uniform_local_phase_sparsity.md) passes review, including uniformity for 1/h<=epsilon<=epsilon_0 and comparison with the exact protected partition function.

For the family U=(4ka,4 eta kb), V=(-4lb,4 eta la), a fixed black cell and a fixed completion column leave O(hR²) shapes. In the side roles the horizontal displacement fixes one scale and the other scale has O(h/a) or O(h/b) possibilities. In the opposite-corner role, ka-lb=d and coprimality give a one-parameter progression with O(h/max(a²,b²)+1) terms. The fixed black row then determines the completion row. There is no extra factor h.

The family has Theta(h² log²R) shapes per eligible completion row. The excluded equality ka=lb contributes O(h log R), which is lower order uniformly for R<=h^(1/4). It is important to exclude this equality: otherwise the opposite black corner lies in the flipped completion column. All remaining black columns are distinct, and increments divisible by four preserve every protected row/phase rule.

Every relevant column interval has length O(hR), hence contains O(epsilon hR) errors. For mean deletion, summing the fixed-black-row count over the h possible rows and multiplying by h^(-3) costs O(R²/h) per deleted black column. The total absolute mean loss is O(epsilon R³). The same bound controls raw column incidence and one-fixed-assignment conditional extensions. Two fixed black cells and a completion column give O(1) possible completions, yielding O(epsilon R) conditional mass. The completion locus cannot be a vertical line unless a black side is horizontal, which this tilted family excludes.

With R=floor(epsilon^(-1/4)), both conditional quantities are uniformly small after choosing epsilon_0. The retained mean per error column is at least c log²R. The inequalities R<=h^(1/4) and h/R>=h^(3/4) make all integer-rounding losses uniform in epsilon. Distinct three-cell assignments have distinct completions after deduplication.

Old bulk whose required black columns avoid S has exactly its former joint product law. Common-corner colors need not be prescribed. The conditional lower-probability argument therefore gives a genuine extra root penalty after avoiding this retained bulk. Restoring deleted old bulk costs O(|S|log⁴h/h), and alphabet-size changes cost O(|S|/h). These are uniformly absorbed because log R is bounded below by a fixed positive constant. This proves the exact ratio rather than a comparison with an approximate bulk exponential.

Summing over every error set is a valid upper bound on the locally sparse family. Finite end errors can be removed in fixed-height collars and compared using protected partition-function bounds; this does not require every individual prefix to extend. Phase periods can be preserved by enlarging the collars by at most three columns.

Taking epsilon_h=exp(-A sqrt(log h)) lies in the uniform range for large h. Its activity is h^(-cA²), so sufficiently large fixed A preserves the full leading protected pressure. This conclusion allows arbitrary local clustering subject to the h-window cap. It does not show that all competitive profiles satisfy that cap, and does not establish unrestricted component dominance.

## Protected domains with the same local sparsity cap

The extension [locally_sparse_errors_in_protected_domains.md](locally_sparse_errors_in_protected_domains.md) also passes review. For fixed B, rescaled wall supports at scale h/log^B h have marked mean at least c_B h/log^(3B+1)h. This deliberately conservative bound suffices. A prescribed completion or black column has bounded marked incident mass; deleting all error columns in the local wall window therefore loses at most C epsilon_h h, which is negligible compared with this wall mean.

Guard neighborhoods have radius O(hR_h), where R_h=epsilon_h^(-1/4). Their error count is O(epsilon_h hR_h) per wall, and describing the assigned error sets costs O(epsilon_h hR_h log(1/epsilon_h)). Both are smaller than the rescaled wall mean by every fixed logarithmic factor. Overlap of guard neighborhoods causes no difficulty: assign each error to a nearby wall, and overcount the resulting choices. Active-root black neighborhoods are disjoint from wall-root black neighborhoods after fixing the guard constant sufficiently large.

At wall density at most K_B log^(3B+5)h/h², the truncated bulk cut loss is O(h^(-1-delta)log^(3B+9)h) per column. Guard bulk deletion and description costs are also lower order than log⁴h/h. The active-error activity h^(-cA²) is lower order for sufficiently large fixed A. Avoiding the retained bulk before rooted events preserves coefficient one on its mean.

Above that wall density, the absolute marked-wall estimate absorbs both wall-location entropy and guard descriptions. Choosing K_B large makes this branch smaller than the protected reference. Thus the low/high density split and the delta-last limit yield the claimed equality of leading pressure. The theorem permits domains as short as h divided by any fixed power of log h, while retaining the uniform local error cap. It still does not classify arbitrary competitive phase profiles.
