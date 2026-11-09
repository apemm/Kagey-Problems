"""Build the complete proven 7x9/19-point candidate family and tilted templates."""
from itertools import combinations, product
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
PROBLEM = HERE.parents[2]
sys.path.insert(0, str(PROBLEM))
from solver.enumerate import rectangles


def reflected(mask):
    return sum(1 << (6-r) for r in range(7) if mask & (1 << r))


def main():
    patterns = set()
    for triple in combinations(range(7), 3):
        outside = [r for r in range(7) if r not in triple]
        for second in outside[1:]:
            left = (outside[0], second)
            right = tuple(r for r in outside if r not in left)
            edges = [(x,y) for x in left for y in right]
            for colors in product(triple, repeat=4):
                attach = dict(zip(outside, colors))
                if any(attach[x] == attach[y] for x,y in edges):
                    continue
                columns = [triple] + edges + [(x,attach[x]) for x in outside]
                masks = tuple(sorted(sum(1 << r for r in c) for c in columns))
                assert len(set(masks)) == 9
                patterns.add(masks)
    assert len(patterns) == 1890
    canonical = sorted(p for p in patterns if p <= tuple(sorted(map(reflected,p))))
    templates = [[] for _ in range(9)]
    all_rectangles = rectangles(7,9)
    for rectangle in all_rectangles:
        if len({x for x,y in rectangle}) == 2 and len({y for x,y in rectangle}) == 2:
            continue
        points = sorted((x-1,y-1) for x,y in rectangle)
        templates[max(x for x,y in points)].append([v for p in points for v in p])
    out = {"rows":7,"columns":9,"black_points":19,
           "all_axis_patterns":len(patterns),
           "vertical_reflection_representatives":len(canonical),
           "rectangles":len(all_rectangles),
           "tilted_rectangles":sum(map(len,templates)),
           "patterns":canonical,"templates_by_last_column":templates}
    (HERE/'seven_nine_search_data.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ('patterns','templates_by_last_column')}))


if __name__ == '__main__':
    main()
