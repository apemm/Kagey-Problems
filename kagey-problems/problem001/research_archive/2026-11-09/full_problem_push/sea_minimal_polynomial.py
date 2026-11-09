"""Minimize the exact sea DFA and seek a certified integer annihilator."""
from __future__ import annotations
import argparse
from array import array
import importlib.util
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "2026-11-08" / "dominance_bridge" / "sea_sparse_automaton.py"
spec = importlib.util.spec_from_file_location("sea_sparse_original", SOURCE)
sea = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sea)


def minimize(trans, h):
    n = len(trans) // h
    classes = [0] * n
    while True:
        lookup, refined, representatives = {}, [], []
        for i in range(n):
            key = tuple(classes[t] if t >= 0 else -1 for t in trans[i*h:(i+1)*h])
            if key not in lookup:
                lookup[key] = len(lookup)
                representatives.append(i)
            refined.append(lookup[key])
        if refined == classes:
            break
        classes = refined
    quotient = [[classes[t] if t >= 0 else -1 for t in trans[i*h:(i+1)*h]]
                for i in representatives]
    return quotient, classes[0]


def bm(sequence, prime):
    c, b, length, age, last = [1], [1], 0, 1, 1
    for n, value in enumerate(sequence):
        discrepancy = value
        for i in range(1, length + 1):
            if i < len(c):
                discrepancy += c[i] * sequence[n-i]
        discrepancy %= prime
        if not discrepancy:
            age += 1
            continue
        saved = c[:]
        ratio = discrepancy * pow(last, prime - 2, prime) % prime
        if len(c) < len(b) + age:
            c.extend([0] * (len(b) + age - len(c)))
        for j, value in enumerate(b):
            c[j+age] = (c[j+age] - ratio * value) % prime
        if 2 * length <= n:
            length = n + 1 - length
            b, last, age = saved, discrepancy, 1
        else:
            age += 1
    c.extend([0] * (length + 1 - len(c)))
    return c[:length+1]


def sequence(rows, start, count, prime):
    vector = [1] * len(rows) + [0]
    out = []
    for _ in range(count):
        out.append(vector[start])
        vector = [sum(vector[t] for t in row) % prime for row in rows] + [0]
    return out


def exact_certificate(rows, coefficients):
    vector = [1] * len(rows) + [0]
    for coefficient in coefficients[1:]:
        vector = [sum(vector[t] for t in row) + coefficient for row in rows] + [0]
    return all(value == 0 for value in vector)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("height", type=int)
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    started = time.monotonic()
    patterns, stats = sea.forbidden_patterns(args.height, started + args.seconds)
    transition, nres = sea.build_residuals(patterns, args.height)
    states, trans, complete, bfs = sea.build_graph(
        transition, args.height, started + args.seconds, 100000, 512)
    assert complete, bfs
    rows, start = minimize(trans, args.height)
    result = {"height": args.height, "original_states": len(states),
              "minimal_states": len(rows), "geometry": stats, "residuals": nres}
    print(json.dumps(result), flush=True)
    residue, modulus = None, 1
    # All are known primes. More can be added if the integer certificate needs them.
    for prime in [1000000007, 1000000009, 998244353, 1004535809, 469762049,
                  985661441, 943718401, 935329793]:
        seq = sequence(rows, start, 2 * len(rows) + 8, prime)
        coeff = bm(seq, prime)
        print(json.dumps({"prime": prime, "degree": len(coeff)-1}), flush=True)
        if residue is None:
            residue = coeff
        elif len(residue) != len(coeff):
            raise ValueError("Modular degrees disagree; do not reconstruct blindly")
        else:
            inverse = pow(modulus % prime, prime - 2, prime)
            residue = [a + modulus * ((b-a) * inverse % prime)
                       for a, b in zip(residue, coeff)]
        modulus *= prime
        candidate = [a if 2*a <= modulus else a-modulus for a in residue]
        if exact_certificate(rows, candidate):
            degree = len(candidate) - 1
            vector = [1] * len(rows) + [0]
            initial = []
            for _ in range(degree):
                initial.append(vector[start])
                vector = [sum(vector[t] for t in row) for row in rows] + [0]
            numerator = [
                sum(candidate[i] * initial[j-i] for i in range(j+1))
                for j in range(degree)
            ]
            denominator = candidate[:]
            while len(numerator) > 1 and numerator[-1] == 0:
                numerator.pop()
            while len(denominator) > 1 and denominator[-1] == 0:
                denominator.pop()
            result.update({"integer_annihilator_verified": True,
                           "descending_coefficients": candidate,
                           "degree": degree,
                           "gf_numerator_ascending": numerator,
                           "gf_denominator_ascending": denominator,
                           "initial_counts": initial,
                           "reconstruction_modulus": modulus})
            break
    else:
        result["integer_annihilator_verified"] = False
    result["seconds"] = time.monotonic() - started
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("descending_coefficients", "gf_numerator_ascending",
                                   "gf_denominator_ascending", "initial_counts")}), flush=True)


if __name__ == "__main__":
    main()
