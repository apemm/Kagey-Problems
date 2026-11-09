# Every high even insertion fails in the full alternating sea

9 November 2026. Consider the infinite horizontal-strip background with row one black in odd
columns and row two black in even columns. Replace the point in column zero
by a parity double whose even row is \(b\). If \(b\ge8\), the resulting
configuration has a horizontal axis rival, independently of the odd partner.

Put \(n=(b-2)/2\ge3\). Every integer \(n\ge3\) is a leg of a nondegenerate
integer right triangle. For odd \(n\), use
\[
n^2+\bigl((n^2-1)/2\bigr)^2
=\bigl((n^2+1)/2\bigr)^2.
\]
For even \(n\ge4\), use
\[
n^2+\bigl(n^2/4-1\bigr)^2
=\bigl(n^2/4+1\bigr)^2.
\]
Doubling either triangle gives positive even integers \(x,L\) such that
\[
x^2+(b-2)^2=L^2.
\]
Use the black diagonal \(\{(0,b),(x,2)\}\). Its horizontal alternative has
endpoint columns \((x-L)/2,(x+L)/2\) and row \((b+2)/2\). This row is
strictly between two and \(b\), so both endpoints are white. Their columns
differ by the even integer \(L\), and hence have the same parity. The two
retained background points in those columns lie on the same row, one or two,
and supply a distinct axis rectangle with the same white presentation.

Neither horizontal endpoint is column zero, since that would require
\(L=x\), contrary to \(b>2\). The collision is therefore unaffected by the
odd central point. All its rows fit whenever \(h\ge b\). On a finite board,
the same obstruction applies whenever its displayed horizontal frame fits.

For example, \(b=8\) gives \(x=8,L=10\) and white pair
\(\{(-1,5),(9,5)\}\), whose axis rival uses two row-one sea points.
For \(b=10\), use \(x=6,L=10\) and white pair
\(\{(-2,6),(8,6)\}\), whose rival uses two row-two points.

Thus the full alternating sea has a dense family of bad even endpoints.
It cannot replace the punctured low-two background with only a sparse set of
exceptional labels.
