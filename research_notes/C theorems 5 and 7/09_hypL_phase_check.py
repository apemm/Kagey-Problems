"""Finite-difference check of Lemma 4.1(d) of 09_hypL_complex_laplace.md.

At the complex critical point zeta'(beta, z) of the torus phase Phi_z, the phase on the rotated torus
Psi(phi) = Phi_z(zeta' e^{i phi}) has zero phi-gradient and phi-Hessian -J with
J = Z_c grad^2 Phi_z(zeta') Z_c, Z_c = diag zeta'. The script compares central differences in phi
(step 1e-4, truncation error of order 1e-8) with the closed form used in 09_hypL_check.py.

Run from this folder:  py -I 09_hypL_phase_check.py > 09_hypL_phase_output.txt
"""
import importlib
import sys
from math import pi

import numpy as np

sys.path.insert(0, ".")
m = importlib.import_module("09_hypL_check")

for name, (Q, mu), beta in [("4-cycle", m.chain_cycle4(), np.array([0.5, 0.3, 0.2])),
                            ("K4", m.chain_k4(), np.array([0.4, 0.35, 0.25]))]:
    fd = m.facet_data(Q, mu, [0, 1, 2], 3)
    for z in [0.1j, 0.1 * np.exp(3j * pi / 4), -0.05, 0.2 * np.exp(1j * pi / 3)]:
        rc = m.rate_and_constant(fd, beta, z)
        A, d, muz, ez = m.weights(fd, z)
        zc, Phi, Jm, bval, gval = m.torus_critical_point(A, muz, ez, beta, rc['theta'][1:])

        def Psi(phi):
            zp = zc * np.exp(1j * np.asarray(phi))
            g, _, _, _ = m.torus_funcs(A, muz, ez, zp)
            return beta[0] * g + beta[1:] @ zp

        h = 1e-4
        Hfd = np.zeros((2, 2), complex)
        grad = np.zeros(2, complex)
        for j in range(2):
            ej = np.zeros(2)
            ej[j] = 1
            grad[j] = (Psi(h * ej) - Psi(-h * ej)) / (2 * h)
            for k in range(2):
                ek = np.zeros(2)
                ek[k] = 1
                Hfd[j, k] = (Psi(h * ej + h * ek) - Psi(h * ej - h * ek) - Psi(-h * ej + h * ek)
                             + Psi(-h * ej - h * ek)) / (4 * h * h)
        print(f"{name:8s} z = {str(np.round(z, 4)):>20}: |grad_phi Psi(0)| = {abs(grad).max():.2e},   "
              f"|(-Hess_phi Psi(0)) - J| / |J| = {abs(-Hfd - Jm).max() / abs(Jm).max():.2e},   "
              f"J = {np.round(Jm, 5).tolist()}")
