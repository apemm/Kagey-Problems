# Independent audit of the separable CRT spacing obstruction

9 November 2026. The theorem in [continuation_separable_crt_p_obstruction.md](continuation_separable_crt_p_obstruction.md) is correct for canonical representatives in one common CRT period. It proves an actual occupied-width lower bound of Omega(h^(5/2)) for this family, including either fixed odd-row residue modulo four. It does not prove a lower bound for arbitrary identifying boards.

## 1. The short difference is an equality of integers

Write the selected ordinary image representatives as F(j_2)=F(j_1)+d<N. Let b=2j_2+2 be central, and take the labels (a,2j_1+2) and (a+2d,b). Their odd indices and their F images both differ by d. Thus their canonical CRT indices differ by either d or d-pN.

There is a direct upper bound on the first representative:

    z_1 <= (p-1)N+F(j_1) < pN-d.

The second possibility is therefore excluded, and z_2=z_1+d. This argument requires no alternate sign choice to avoid a wrap. It also works when p is not prime: coprimality with N and p>h suffice for the proof below.

## 2. Rows, residue classes, and the actual presentation collision

Put v=4d^2-1 and L=4d^2+1. Choose a=b+v or a=b-v. The selected black diagonal has horizontal displacement 4d and vertical displacement of magnitude v, so its squared length is L^2.

In the plus case, its vertical alternative diagonal has rows

    b-1, b+4d^2.

In the minus case, those rows are

    b-4d^2, b+1.

All selected label rows, including a+2d, and these white-candidate rows lie in [1,h] for large h. Indeed, b lies in [h/3,2h/3], while 4d^2+2d<=h/25+sqrt(h)/5 for d<=sqrt(h)/10.

For the mod-four split, require d even. The two choices of a have opposite odd residues modulo four, and a+2d has the same residue as a. The odd white-candidate row is a-4d^2 in the plus case and a+4d^2 in the minus case. Hence its owner label is present in the same retained odd residue family, rather than only elsewhere in a complete unsplit construction.

The midpoint column is 4(z_1+d/2). Its odd-row CRT index is i_a+d/2 modulo p. The white odd row has index i_a-2d^2 or i_a+2d^2. Their difference is nonzero and has magnitude at most 2d^2+d/2<h<p. Therefore the odd candidate point is genuinely white in the full retained scaffold. The owner column is not the midpoint. The same congruence check, with index differences 2d^2 and 2d^2 plus or minus d, separates the owner from both diagonal columns.

The tilted rectangle and the axis rectangle using this owner have exactly the same presentation. Their symmetric difference consists of the two original black diagonal points and the two owner points. Thus any later filling preserves the collision. The argument does not require the other common candidate point to remain white.

Without the mod-four split one can use arbitrary positive d. If d is odd, the midpoint column is not divisible by four and contains no inserted point. The even-d argument already suffices for the claimed lower bound in both settings.

## 3. Spacing and occupied span

Let D=floor(sqrt(h)/10), and let M be the number of central even rows. Then M>=h/6-O(1). If the placement avoids the displayed collision, the F images in each parity class must be separated by more than D. Consequently

    M <= 2+2N/D,
    N >= (M-2)D/2 = Omega(h^(3/2)).

This is an ordinary spacing estimate in [0,N), with the two image-parity classes treated separately. It uses the injection only to ensure distinct image representatives and labels.

The width conclusion is stronger than saying that the nominal period pN is large. Fix one even row. Its Theta(h) retained odd endpoints have distinct columns, all congruent to 4F(j) modulo 4N. Their occupied span is at least 4N times one less than their number. This gives Omega(hN)=Omega(h^(5/2)), regardless of how much larger p is than h.

The collision proof applies to canonical representatives and to a common translation of the resulting placement. Arbitrary label-dependent additions of pN are outside its scope. A bounded lift depending only on the even row can be handled by first selecting a common lift class among the central even rows; the resulting constant can depend on the number of lift values. No corresponding assertion about arbitrary odd-row-dependent lifts is needed here.

## 4. Consequence for the proposed construction

The obstruction allows every injection F, so an even-row isometry, permutation, or other global refinement cannot remove it while N=O(h). Splitting the odd rows into their two mod-four classes does not help. Filler choices cannot repair the already black symmetric difference.

A complete quadratic-width construction must therefore change at least one of these features: the separable single map F, the canonical common-period representatives, or the retained full odd/even label family. The theorem does not exclude coordinated label-dependent lifts or other coordinate maps.
