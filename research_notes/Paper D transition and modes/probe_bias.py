"""Exploratory finite-row bias tests, with exact curvature counterexamples.

Floating-point mode counts are diagnostics, not certificates. Every open sign
cell in q is sampled; local roundoff and absolute underflow guards are applied.
"""

from fractions import Fraction
import json
import time

import numpy as np


def row_step(row, a, n):
    eps = (1 - a) / 2
    up = eps + a * np.arange(n + 1) / n
    out = np.zeros(n + 2)
    out[:-1] += row * (1 - up)
    out[1:] += row * up
    return out


def exact_row(a, q, n):
    eps = (1 - a) / 2
    row = [1 - q, q]
    for t in range(1, n):
        out = [Fraction(0) for _ in range(t + 2)]
        for k, value in enumerate(row):
            up = eps + a * Fraction(k, t)
            out[k] += value * (1 - up)
            out[k + 1] += value * up
        row = out
    return row


def sign_blocks(values):
    signs = np.sign(values[values != 0]).astype(int)
    if not len(signs):
        return []
    return signs[np.r_[True, signs[1:] != signs[:-1]]].tolist()


def mode_probe():
    memories = list(np.linspace(0.01, 0.99, 50)) + [0.985, 0.995, 0.999, 0.9999]
    times = {2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 40, 60, 80, 100, 150,
             200, 300, 500, 750, 1000, 1500, 2000, 3000, 4000}
    count, worst, disconnected = 0, None, []
    for a in memories:
        row = np.array([0.0, 1.0])
        for n in range(1, max(times) + 1):
            if n in times:
                derivative = np.diff(np.r_[0.0, row, 0.0])
                reflected = -derivative[::-1]
                denominator = derivative - reflected
                active = denominator != 0
                roots = -reflected[active] / denominator[active]
                roots = np.unique(np.r_[0.0, roots[(roots > 0) & (roots < 1)], 1.0])
                qs = np.r_[0.0, (roots[1:] + roots[:-1]) / 2, 1.0]
                bimodal_cells = []
                for q in qs:
                    mixture = q * row + (1 - q) * row[::-1]
                    values = q * derivative + (1 - q) * reflected
                    extended = np.r_[0.0, mixture, 0.0]
                    local = np.maximum(extended[:-1], extended[1:])
                    values[np.abs(values) <= np.maximum(1e-12 * local, 1e-280)] = 0
                    blocks = sign_blocks(values)
                    modes = sum(x == 1 and y == -1 for x, y in zip(blocks, blocks[1:]))
                    count += 1
                    if worst is None or modes > worst[0]:
                        worst = [modes, float(a), float(q), blocks, n]
                    if modes > 2:
                        return {"q_cells": count, "worst": worst, "counterexample": worst}
                    bimodal_cells.append(modes == 2)
                indices = np.flatnonzero(bimodal_cells)
                if len(indices) and not all(bimodal_cells[indices[0]:indices[-1] + 1]):
                    disconnected.append([float(a), n])
            if n < max(times):
                row = row_step(row, a, n)
    return {"q_cells": count, "worst": worst, "counterexample": [],
            "disconnected_bimodal_bias_sets_diagnostics": disconnected,
            "guard": "max(1e-12 * adjacent local mass, 1e-280)"}


def curvature_counterexamples():
    a, q, n = Fraction(24, 25), Fraction(1, 1200), 80
    row = exact_row(a, q, n)
    places = [1, 2, 74, 75, 77]
    values = [row[k - 1] - 2 * row[k] + row[k + 1] for k in places]
    assert [v > 0 for v in values] == [False, True, False, True, False]
    temporal_places = [2, 7, 11, 25, 85]
    temporal_values = []
    for t in temporal_places:
        row = exact_row(Fraction(9, 10), Fraction(199, 200), t)
        temporal_values.append(row[0] - 2 * row[1] + row[2])
    assert [v > 0 for v in temporal_values] == [True, False, True, False, True]
    return {
        "spatial": {"a": str(a), "q": str(q), "n": n, "places": places,
                    "values": [float(v) for v in values], "exact_signs_verified": True},
        "temporal": {"a": "9/10", "q": "199/200", "times": temporal_places,
                     "values": [float(v) for v in temporal_values], "exact_signs_verified": True},
    }


if __name__ == "__main__":
    start = time.perf_counter()
    result = {"curvature_counterexamples": curvature_counterexamples(), "modes": mode_probe()}
    result["seconds"] = time.perf_counter() - start
    print(json.dumps(result, indent=2))
