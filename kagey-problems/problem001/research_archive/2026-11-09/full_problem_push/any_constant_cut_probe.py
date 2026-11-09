"""Exact bounded search for periodic seas with no direct constant future."""
from itertools import product
from pathlib import Path
import argparse
import json
import time
from constant_cut_probe import quotient, minimize, sea, HERE


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('height', type=int)
    parser.add_argument('--maxperiod', type=int, default=4)
    parser.add_argument('--seconds', type=float, default=180)
    args = parser.parse_args()
    started = time.monotonic()
    h = args.height
    patterns, geometry = sea.forbidden_patterns(h, started + args.seconds)
    records = []
    for p in range(1, args.maxperiod + 1):
        full = []
        cuts = [[] for _ in range(h + 1)]
        for support in patterns:
            for shift in range(p):
                projected = quotient(((x+shift, r) for x, r in support), p)
                if projected is not None:
                    full.append(projected)
            for shift in range(-support[-1][0], 0):
                targets = {r for x, r in support if x+shift >= 0}
                if len(targets) != 1:
                    continue
                target = next(iter(targets))
                projected = quotient(((x+shift, r) for x, r in support if x+shift < 0), p)
                if projected is not None:
                    cuts[target].append(projected)
        full = minimize(full)
        cuts = [minimize(c) for c in cuts]
        accepted = 0
        bad = []
        tested = 0
        complete = True
        for word in product(range(1, h+1), repeat=p):
            tested += 1
            if tested % 1000 == 0 and time.monotonic()-started > args.seconds:
                complete = False
                break
            if any(all(word[i] == r for i, r in c) for c in full):
                continue
            accepted += 1
            allowed = [(r, phase) for r in range(1, h+1) for phase in range(p)
                       if not any(all(word[(i+phase) % p] == y for i, y in c)
                                  for c in cuts[r])]
            if not allowed:
                bad.append(word)
        result = {'period':p, 'tested':tested, 'accepted':accepted,
                  'no_constant_cut':len(bad), 'first_examples':bad[:20],
                  'complete':complete}
        records.append(result)
        print(json.dumps(result), flush=True)
        if bad or not complete:
            break
    output = {'height':h, 'maxperiod':args.maxperiod, 'geometry':geometry,
              'records':records, 'seconds':time.monotonic()-started}
    (HERE / f'any_constant_cut_h{h}_p{args.maxperiod}.json').write_text(
        json.dumps(output, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
