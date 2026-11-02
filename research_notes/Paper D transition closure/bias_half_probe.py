"""Exact rational stress-test of dominant-half unimodality and reflection dominance."""
from fractions import Fraction as F
from pathlib import Path
import json
import time


def require(ok, message):
    if not ok:
        raise ValueError(message)


def run():
    start = time.perf_counter()
    memories = [F(-9, 10), F(-1, 2), F(0), F(1, 5), F(1, 2), F(7, 10), F(9, 10), F(99, 100)]
    biases = [F(1, 2), F(3, 5), F(4, 5), F(99, 100), F(1)]
    cases = 0
    for a in memories:
        eps = (1-a)/2
        for q in biases:
            row = [1-q, q]
            last_edge_negative = False
            for n in range(1, 65):
                require(all(row[k] >= row[n-k] for k in range((n+1)//2, n+1)),
                        f"reflection dominance failed at {(a, q, n)}")
                ds = [row[k+1]-row[k] for k in range(n)]
                seen_negative = False
                for k in range(n//2, n):
                    require(not (seen_negative and ds[k] > 0),
                            f"right half valley at {(a,q,n,k)}")
                    seen_negative |= ds[k] < 0
                edge = ds[-1]
                require(not (last_edge_negative and edge > 0),
                        f"right boundary regains positive sign at {(a,q,n)}")
                last_edge_negative |= edge < 0
                cases += 1
                out = [F(0)]*(n+2)
                for k,v in enumerate(row):
                    r = eps+a*F(k,n)
                    out[k] += (1-r)*v
                    out[k+1] += r*v
                row = out
    return {"arithmetic":"exact fractions", "cases":cases,
            "memories":list(map(str, memories)), "biases":list(map(str,biases)),
            "largest_time":64, "all_checks_passed":True,
            "scope":"Actual finite rows, reflection dominance, dominant-half no valley, temporal outer-edge sign. Not a limiting-shape certificate.",
            "seconds":time.perf_counter()-start}


if __name__ == "__main__":
    result = run()
    text = json.dumps(result,indent=2)+"\n"
    print(text)
    Path(__file__).with_name("bias_half_probe_output.json").write_text(text)
