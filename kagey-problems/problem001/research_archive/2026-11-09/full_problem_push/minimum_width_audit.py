"""Exact finite audit of the minimum-width conjecture, using integer arithmetic."""
from math import isqrt
from pathlib import Path
import json
import time


HERE = Path(__file__).resolve().parent


def three_variable(n):
    best = n
    witness = (n - 1, 1, 1)
    for y in range(2, n):
        x = (n - 1) // y
        z = n - x * y
        value = x + y * z
        if value < best:
            best, witness = value, (x, y, z)
    return best, witness


def full_rectangle(n, initial):
    best = initial
    witness = None
    for b in range(1, n // 2 + 1):
        d = n - b
        product = b * d
        if 4 * product > best * best:
            break
        for a in range(1, isqrt(product) + 1):
            if product % a:
                continue
            c = product // a
            value = a + c
            if value <= best:
                best, witness = value, (a, b, c, d)
    assert witness is not None
    a, b, c, d = witness
    assert a * c == b * d and b + d == n and a + c == best
    return best, witness


def independent_a228286(n):
    best = n
    witness = None
    for x in range(1, n):
        for y in range(1, (n - 1) // x + 1):
            z = n - x * y
            value = x + y * z
            if value < best:
                best, witness = value, (x, y, z)
    return best, witness


def main():
    started = time.monotonic()
    counterexamples = []
    for n in range(2, 656):
        restricted, restricted_witness = three_variable(n)
        unrestricted, rectangle_witness = full_rectangle(n, restricted)
        if unrestricted < restricted:
            counterexamples.append({
                "height_span": n,
                "minimum_width": unrestricted,
                "rectangle_a_b_c_d": rectangle_witness,
                "A228286": restricted,
                "A228286_x_y_z": restricted_witness,
            })
    checked = independent_a228286(655)
    assert checked[0] == three_variable(655)[0]
    out = {
        "heights_exhausted": [2, 655],
        "scope": "height and width are coordinate spans, not numbers of grid points",
        "counterexamples": counterexamples,
        "independent_A228286_655": checked,
        "elapsed_seconds": time.monotonic() - started,
    }
    (HERE / "minimum_width_audit.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out), flush=True)


if __name__ == "__main__":
    main()
