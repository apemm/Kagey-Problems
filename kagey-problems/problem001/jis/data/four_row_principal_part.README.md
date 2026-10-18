# Four-row dominant principal part: decimal preservation

`four_row_principal_part.txt` is the unmodified 725-byte numerical output recovered on
2026-10-17 from the output of the
script that computed the principal part for Corollary "four-row growth".
Its SHA-256 is
`65050cab2d92ebb7f1038e2d5ec750edc47f1120158cfb1909ab5e6306c28462`.
It was copied without replacing a preexisting file.

For the exact `P4/Q4` in `four_row_recurrence.json` at commit
`6064e85c2ff728980ba2f96fff576284e839d90d`, let `r` be the positive dominant pole,
`rho = 1/r`, and let `H(z) = P4(z)(1-z/r)^5/Q4(z)`, extended analytically at `r`.
Then

```
c_j = (-r)^(5-j) H^(5-j)(r)/(5-j)!,       1 <= j <= 5,
B(m) = sum(j=1..5, c_j binomial(m+j-1,j-1)),
a_4(m) = rho^m B(m) + O((1000/341)^m).
```

The five `c_j` are coefficients in this **binomial basis**, not coefficients of
ordinary powers `m^j` (nor of `m^(j-1)`). In particular the leading coefficient
of the degree-four polynomial `B` is `c_5/24`, approximately
`0.0000816109707754112490336898789612`.

The preserved file contains rounded decimals and diagnostics, not exact algebraic
numbers, a full interval certificate, or an explicit uniform remainder constant.
The equal-looking printed lower and upper endpoints are rounded to the same
30 significant digits; they do not assert a zero-width interval. The `c_j` have
about 16 significant digits. Finite scaled-error samples do not bound the
big-O constant for all widths, and these rounded decimals should not be used to
generate exact integer sequence terms.

The original `principal_part.py` was preserved only in
`research_notes/Problem 001 final submission review/math_coefficients_20261017_6064e85_91c7/principal_part_original.py`.
Its SHA-256 is
`eb8667ed868c93471cebdc1476eb094d8102e5fad6604ea4cb30c0755da348a1`.
It accepts a JSON input path; the recovered output itself does not record the
historical input hash or invocation. The present audit independently checked all
five printed values, correctly rounded at their final displayed place, against
the exact current `P4/Q4`, using factorwise deflation and 4000-bit outward interval
arithmetic with a unique-root rational bracket narrower than `2^-900`. See
`research_notes/Problem 001 final submission review/01_math_and_coefficients.md`
and that audit subfolder's `check_revision.py` and `checks.json`.

The working-tree recurrence file SHA-256 is
`45100f715803f873c7dc9019119f9c9d91dd09d073c4358bbc22f1436711071e`;
the Git blob SHA-256 is
`3c88c73bd9b0d5c304171e254bb325378a30b787d5653142c664fe2a22f34fbc`.
The difference is CRLF/LF line endings; normalized contents agree with the pinned
commit. These checks retain ordinary Python/SymPy/mpmath execution trust and are
not a Lean proof or a rerun of the automaton-equivalence/recurrence certificates.
