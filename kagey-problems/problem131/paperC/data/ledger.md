# Problem 131 Paper C ledger

Predictions were written down before the computation that tests them. Each prediction has a kill
condition, and the outcome is recorded below it without changes, also when it refutes the
prediction. The entries are kept in one file per topic, and each file starts by listing the few
computations that were run before it existed.

- [ledger_C1.md](ledger_C1.md) covers the exact law in transition-count form, the order of the
  winning faces on a star and a path, the star with a rare centre, and the non-reversible cell NR3
  (Sections 2 and 3). Entries L1 to L6 and L3'.
- [ledger_C2.md](ledger_C2.md) covers complete graphs, the cycle cascade, 2 triangles, the paw and
  the house, and the census of small graphs (Section 5). Entries 0 to 11, and an erratum that
  records the checks of the path P_4 and of C_6 at N = 40.
- [ledger_C3.md](ledger_C3.md) covers the planar walk, corner against origin (Section 7 and
  Appendix D). Entries C3-P1 to C3-P8.
- [ledger_C4.md](ledger_C4.md) covers sticky priors and the Fisher information of the endpoint
  (Sections 6 and 8, Appendices C and E). Entries C4-F1 to C4-F7, C4-S1 to C4-S5, C4-G1 and
  C4-R1 to C4-R3.
- [ledger_C5.md](ledger_C5.md) covers the local law, the constants K_F, the crossings, the window
  on K_3 and the directed 3-cycle (Section 4 and Appendices A and B). Entries P0 to P10, P3', P6',
  P8(b'), R1 and R2.

Some predictions were refuted. In C1 these are L3(b) and L3(d), whose tolerances left out
corrections of order N^(-1/2) and N^(-1/4). In C2 they are P1.5 (a symmetry clause that fails by
parity), Q2.1 and Q2.4 (a boundary mode of the 2 triangles when h is large), H3 at N = 40, A9.1
at N = 300 and 1000, and S1 (consecutive winners can be disjoint). In C3 one tau band of C3-P2
and one of C3-P6 were written down wrongly. In C4 they are C4-F1, C4-F2, part of C4-F3, the
wording of C4-S1(a) (it missed a 3-way tie) and the precision part of C4-S2. In C5 they are P2,
P3, P6 and P8(b), where a fit or a tolerance was chosen badly. In each case a corrected test on
new cells was registered before it was run. None of them concerns a statement that the paper
calls a theorem. The path P_4 in the erratum of C2 shows that at finite N the order of the phases
can differ from first order, and the paper says so as a numerical remark.

The output of the check scripts (`verify_all.py`) is in `verify_output.txt`.
