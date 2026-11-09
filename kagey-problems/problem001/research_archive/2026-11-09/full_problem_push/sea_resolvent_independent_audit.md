# Independent audit of the sea-resolvent counting formula

9 November 2026. sea_resolvent_counting_formula.md passes independent
review. Its exact generating function, denominator reduction, and
eventual integer recurrence have the stated unconditional scope.

The chronological permutation of the distinct double labels and the
\(q+1\) intervening singleton-run lengths specify each word uniquely.
Zero run lengths correctly include adjacent doubles. Expanding each
\((I-zA_0)^{-1}\) as its formal power series therefore proves the
matrix identity coefficient by coefficient, without a convergence or
asymptotic assumption. There is no need to attach used-label subsets
to the history for this identity: the chosen permutation already
requires each label exactly once.

The matrices must remain the finite-end history matrices from the
all-width formula. In particular, their tests use actual contained
rectangles and the complete final pair set. The markers ensure that
every pair in that final set really appears in the completed word.
Initial short histories and acceptance of every terminal history
retain the finite-boundary numerator. Replacing these by normalized
support-language boundary vectors would not be justified.

For \(h\ge4\), a word containing all \(q=\lfloor h^2/4\rfloor\)
labels has width at least four. Thus the no-hidden theorem used by
the underlying transition test applies to every nonzero coefficient
in this equality-word series. Shorter prefixes may be rejected for
containing a hidden rectangle because no valid completed word in
this series could retain it.

Under singleton transitions, every short history reaches full length,
and every double letter is flushed out in at most \(L\) steps.
Consequently the complementary block to the full-length singleton
histories is nilpotent. Singleton histories are closed under these
transitions. Block triangularity gives
\[
 \det(I-zA_0)=\det(I-zT_\pi).
\]
Unreachable or internally inadmissible presentation states do not
create a hidden recurrence issue: any singleton cycle is a genuine
bi-infinite path whose local tests repeat, while purely transient
states contribute determinant factor one.

The adjugate formula gives denominator \(D_\pi\) for each
resolvent entry, hence \(D_\pi^{q+1}\) for each summand and for
their permutation sum. Every equality board has a unique unordered
balanced partition because its complete bipartite row graph is
connected. Summing partitions therefore introduces no multiplicity.

Each \(D_\pi\) is an integer polynomial with constant term one.
Its normalized polynomial least common multiple is consequently
also integral with constant term one, by Gauss's lemma. After
multiplication by that common denominator, the finitely many
pre-threshold corrections leave a polynomial numerator. Comparing
coefficients gives the stated eventual integer recurrence and
degree bound.

The formula introduces no nonzero exponential base beyond the
fixed-final-pair-set singleton-sea eigenvalues. It does not identify
the dominant component, remove possible residue dependence, or
force polynomial degree \(q\).
