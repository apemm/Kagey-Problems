"""Finite checks of the candidate absolute primitive-direction coefficient.

This is numerical evidence, not an asymptotic certificate.
"""
from pathlib import Path
from math import gcd, log, pi
from functools import lru_cache
import json
import time
import numpy as np

HERE = Path(__file__).resolve().parent
began = time.monotonic()
heights = [128, 256, 512, 1024, 2048, 4096]
hmax = max(heights)
amax = int(hmax/log(hmax))
limit = hmax*hmax + amax*amax
spf = np.zeros(limit+1, dtype=np.int32)
for p in range(2, int(limit**.5)+1):
    if spf[p] == 0:
        block = spf[p*p::p]
        block[block == 0] = p

@lru_cache(maxsize=None)
def coefficient(n):
    product = 1.0
    while n > 1:
        p = int(spf[n]) or n
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if p % 4 == 1:
            product *= 1 + e*(p-1)/(p+1)
        else:
            assert p == 2
    return 4*product/pi

cq, cw = 1.0, .5
for p in range(3, min(limit, 1000000)+1, 2):
    if spf[p] != 0:
        continue
    if p % 4 == 1:
        cq *= 1-4/(p+1)**2
        cw *= 1-(3*p+1)/(p*p*(p+3))
    else:
        cw *= 1-1/(p*p)
predicted = cq*cw/(3*pi*pi)
records = []
for h in heights:
    sums = {"OO":0.0, "OE":0.0, "EO":0.0}
    counts = dict.fromkeys(sums, 0)
    cutoff = log(h)
    for b in range(1, h+1):
        weight_b = log(h/b)/b
        for a in range(1, int(b/cutoff)+1):
            if gcd(a,b) != 1:
                continue
            kind = ("O" if a % 2 else "E") + ("O" if b % 2 else "E")
            sums[kind] += coefficient(a*a+b*b)*weight_b/a
            counts[kind] += 1
    norm = {key:value/log(h)**4 for key,value in sums.items()}
    item = dict(height=h, weights=sums, normalized=norm, counts=counts,
                ratios_to_OO={key:value/sums["OO"] for key,value in sums.items()})
    records.append(item)
    print(json.dumps(item), flush=True)
result = dict(status="NUMERICAL_ONLY", predicted_each=predicted,
              product_Cq=cq, product_cw=cw,
              predicted_mixed_ordinary=8*cq*cw/(9*pi*pi),
              records=records, seconds=time.monotonic()-began)
(HERE/"primitive_absolute_coefficient_checks.json").write_text(
    json.dumps(result, indent=2)+"\n", encoding="utf-8")
print(json.dumps({key:value for key,value in result.items() if key!="records"}))

