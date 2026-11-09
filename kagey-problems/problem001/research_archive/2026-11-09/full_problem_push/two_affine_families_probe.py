"""Exact 2-SAT test of constant-even-row versus constant-offset blocks.

This tests only vertical rivals within blocks. It is not a full-board test.
Rows use one-based coordinates. Type 0 assigns (a,b) to its b block;
type 1 assigns it to its a-b block.
"""
import argparse
from collections import defaultdict, deque
import json
from math import isqrt
from pathlib import Path


def p_rival(a, b, dx, h):
    square = dx * dx + (a - b) ** 2
    length = isqrt(square)
    if length * length != square:
        return None
    if (a + b - length) % 2 or a + b - length < 2 or a + b + length > 2 * h:
        return None
    return [length, (a + b - length) // 2, (a + b + length) // 2]


def solve(h, group_kinds=('even', 'offset'), scale=2):
    labels = [(a, b) for a in range(1, h + 1, 2) for b in range(2, h + 1, 2)]
    n = len(labels)
    graph, reverse = [[] for _ in range(2*n)], [[] for _ in range(2*n)]
    clauses = []
    for kind in range(2):
        groups = defaultdict(list)
        for i, (a, b) in enumerate(labels):
            key = {'even':b, 'offset':a-b, 'sum':a+b}[group_kinds[kind]]
            groups[key].append(i)
        for ids in groups.values():
            for j, first in enumerate(ids):
                a, b = labels[first]
                for second in ids[j+1:]:
                    c, d = labels[second]
                    dx = scale*(a-c)
                    cert = p_rival(a, d, dx, h)
                    order = [first, second]
                    if cert is None:
                        cert = p_rival(c, b, dx, h)
                        order = [second, first]
                    if cert is None:
                        continue
                    x, y = 2*first + kind, 2*second + kind
                    ci = len(clauses)
                    clauses.append({'kind': kind, 'labels': [first, second], 'ordered_labels': order, 'certificate': cert})
                    for src, dst in [(x^1, y), (y^1, x)]:
                        graph[src].append((dst, ci))
                        reverse[dst].append(src)
    seen, finish = [False]*(2*n), []
    for root in range(2*n):
        if seen[root]:
            continue
        seen[root] = True
        stack = [(root, 0)]
        while stack:
            v, j = stack[-1]
            if j == len(graph[v]):
                finish.append(v)
                stack.pop()
                continue
            stack[-1] = (v, j+1)
            w = graph[v][j][0]
            if not seen[w]:
                seen[w] = True
                stack.append((w, 0))
    component, count = [-1]*(2*n), 0
    for root in reversed(finish):
        if component[root] >= 0:
            continue
        component[root] = count
        stack = [root]
        while stack:
            v = stack.pop()
            for w in reverse[v]:
                if component[w] < 0:
                    component[w] = count
                    stack.append(w)
        count += 1
    bad = next((i for i in range(n) if component[2*i] == component[2*i+1]), None)
    result = {'height': h, 'group_kinds':list(group_kinds), 'scale':scale,
              'labels_count': n, 'clauses_count': len(clauses), 'satisfiable': bad is None}
    if bad is None:
        assignment = [int(component[2*i] > component[2*i+1]) for i in range(n)]
        assert all(not (assignment[i] == assignment[j] == cl['kind']) for cl in clauses for i, j in [cl['labels']])
        result['type1_count'] = sum(assignment)
        return result

    def path(src, dst):
        predecessor = {src: None}
        queue = deque([src])
        while dst not in predecessor:
            v = queue.popleft()
            for w, ci in graph[v]:
                if component[w] == component[src] and w not in predecessor:
                    predecessor[w] = (v, ci)
                    queue.append(w)
        steps, cur = [], dst
        while cur != src:
            prev, ci = predecessor[cur]
            cl = clauses[ci]
            steps.append({'from_label': labels[prev//2], 'from_type': 1-(prev%2),
                          'to_label': labels[cur//2], 'to_type': 1-(cur%2),
                          'forbidden_type': cl['kind'],
                          'ordered_labels': [labels[i] for i in cl['ordered_labels']],
                          'certificate': cl['certificate']})
            cur = prev
        return list(reversed(steps))

    result['contradictory_label'] = labels[bad]
    result['paths'] = [path(2*bad, 2*bad+1), path(2*bad+1, 2*bad)]
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('heights', nargs='+', type=int)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--groups', nargs=2, choices=['even','offset','sum'], default=['even','offset'])
    parser.add_argument('--scale',type=int,default=2)
    args = parser.parse_args()
    results = []
    for h in args.heights:
        result = solve(h,tuple(args.groups),args.scale)
        results.append(result)
        print(json.dumps({k: v for k, v in result.items() if k != 'paths'}), flush=True)
        if not result['satisfiable']:
            break
    if args.output:
        args.output.write_text(json.dumps(results, indent=2) + '\n')
