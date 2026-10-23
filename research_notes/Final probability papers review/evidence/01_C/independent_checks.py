"""Small exact checks for the independent Paper C mathematical audit.

Standard library only. No manuscript imports, Lean, Lake, or numerical sweeps.
Run from the repository root; outputs JSON next to this file.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def inverse(a):
    n = len(a)
    z = [[F(x) for x in row] + [F(i == j) for j in range(n)]
         for i, row in enumerate(a)]
    for j in range(n):
        p = next(i for i in range(j, n) if z[i][j])
        z[j], z[p] = z[p], z[j]
        t = z[j][j]
        z[j] = [x / t for x in z[j]]
        for i in range(n):
            if i != j:
                t = z[i][j]
                z[i] = [x - t*y for x, y in zip(z[i], z[j])]
    return [row[n:] for row in z]


def det(a):
    n = len(a)
    if n == 1:
        return a[0][0]
    return sum((-1)**j*a[0][j]*det([row[:j]+row[j+1:] for row in a[1:]])
               for j in range(n))


def covariance_check(g):
    n = len(g)
    # Solve pi^T G=0, sum(pi)=1 independently of tree formulas.
    a = [[F(g[j][i]) for j in range(n)] for i in range(n-1)] + [[F(1)]*n]
    ai = inverse(a)
    pi = [row[-1] for row in ai]
    z = inverse([[pi[j]-g[i][j] for j in range(n)] for i in range(n)])
    z = [[z[i][j]-pi[j] for j in range(n)] for i in range(n)]
    gamma = [[pi[i]*z[i][j]+pi[j]*z[j][i] for j in range(n)] for i in range(n)]
    sigma_det = det([row[1:] for row in gamma[1:]])
    flow = [[pi[i]*g[i][j] if i != j else F(0) for j in range(n)] for i in range(n)]
    # Explicit rooted trees, independent of any determinant tree implementation.
    trees = []
    for root in range(n):
        nonroot = [i for i in range(n) if i != root]
        total = F(0)
        for parents in product(range(n), repeat=n-1):
            parent = dict(zip(nonroot, parents))
            valid = True
            for i in nonroot:
                seen = set()
                j = i
                while j != root:
                    if j in seen:
                        valid = False
                        break
                    seen.add(j)
                    j = parent[j]
                if not valid:
                    break
            if valid:
                weight = F(1)
                for i in nonroot:
                    weight *= flow[i][parent[i]]
                total += weight
        trees.append(total)
    assert len(set(trees)) == 1
    if n == 2:
        undirected = flow[0][1]+flow[1][0]
    else:
        a, b, c = (flow[0][1]+flow[1][0], flow[0][2]+flow[2][0],
                   flow[1][2]+flow[2][1])
        undirected = a*b+a*c+b*c
    pp = F(1)
    for x in pi:
        pp *= x
    tree_det = pp**2*undirected/trees[0]**2
    assert sigma_det == tree_det
    return {'pi': list(map(str, pi)), 'det_sigma_direct': str(sigma_det),
            'det_sigma_trees': str(tree_det), 'directed_tree_by_root': list(map(str, trees))}


def compositions(g, mu, h, n):
    d = len(g)
    p = [[F(i == j)+h*g[i][j] for j in range(d)] for i in range(d)]
    cur = defaultdict(F)
    for i in range(d):
        counts = tuple(int(j == i) for j in range(d))
        cur[(counts, i)] += mu[i]
    for _ in range(n-1):
        nxt = defaultdict(F)
        for (counts, i), weight in cur.items():
            for j in range(d):
                if p[i][j]:
                    cc = list(counts)
                    cc[j] += 1
                    nxt[(tuple(cc), j)] += weight*p[i][j]
        cur = nxt
    out = defaultdict(F)
    for (counts, _), weight in cur.items():
        out[counts] += weight
    assert sum(out.values()) == 1
    return out


results = {}
branch = [[-2, 1, 1], [0, 0, 0], [0, 0, 0]]
probs = compositions(branch, [F(1), F(0), F(0)], F(1, 10), 9)
assert probs[(3, 3, 3)] == 0
results['branching_counterexample_to_unrestricted_rate_prose'] = {
    'N': 9, 'h': '1/10', 'composition': [3, 3, 3],
    'exact_probability': str(probs[(3, 3, 3)]), 'variational_I_at_alpha': '2/3',
    'reason': 'A path that reaches state 2 or 3 is absorbed there and cannot visit the other.'}

cycle = [[-3, 3, 0], [0, -1, 1], [1, 0, -1]]
probs = compositions(cycle, [F(1), F(0), F(0)], F(1, 20), 9)
support_max = {}
support_arg = {}
for counts, mass in probs.items():
    if not mass:
        continue
    support = tuple(i+1 for i, x in enumerate(counts) if x)
    if support not in support_max or mass > support_max[support]:
        support_max[support] = mass
        support_arg[support] = counts
assert set(support_max) == {(1,), (1, 2), (1, 2, 3)}
assert support_arg[(1, 2)] == (1, 8, 0)
assert support_max[(1, 2)] == F(3, 20)*F(19, 20)**7
results['directed_cycle_exact_small_check'] = {
    'N': 9, 'h': '1/20', 'positive_supports': [list(s) for s in support_max],
    'pair_mode': list(support_arg[(1, 2)]), 'pair_maximum': str(support_max[(1, 2)])}

results['covariances'] = {
    'asymmetric_pair_rates_2_3': covariance_check([[-2, 2], [3, -3]]),
    'directed_cycle_rates_3_1_1': covariance_check(cycle),
    'nonreversible_three_state': covariance_check([[-3, 2, 1], [1, -4, 3], [4, 2, -6]])}
assert results['covariances']['asymmetric_pair_rates_2_3']['det_sigma_direct'] == '12/125'
assert results['covariances']['directed_cycle_rates_3_1_1']['det_sigma_direct'] == '27/2401'

# Independent one-dimensional torus calculation for symmetric rates a=1.
# At alpha=(1/2,1/2): Psi=cos(phi), chi=mu1*exp(i phi)
# +(mu1+mu2)+mu2*exp(-i phi). Thus c(alpha*)=-1/8,
# gamma=(mu2-mu1)/(mu1+mu2), Sigma=1/4.
results['symmetric_pair_start_dependence_next_coefficient'] = []
for mu1, mu2 in [(F(1, 2), F(1, 2)), (F(1), F(0)), (F(3, 4), F(1, 4))]:
    gamma = (mu2-mu1)/(mu1+mu2)
    c_face = -F(1, 8)+gamma**2/F(8)
    assert c_face == -mu1*mu2/(2*(mu1+mu2)**2)
    results['symmetric_pair_start_dependence_next_coefficient'].append({
        'mu': [str(mu1), str(mu2)], 'gamma': str(gamma), 'c_face': str(c_face)})

out = Path(__file__).with_name('independent_checks.json')
out.write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8')
print(json.dumps(results, indent=2))
