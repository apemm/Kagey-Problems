# Exhaustive verification for Kagey Problem 137 (tree of A226247/A226248)
import sys, time

MAX = 41          # BFS ranks 0..MAX
CFCHECK = 32      # exhaustive continued-fraction formula checks through this rank

t0 = time.time()
rank_of = {(0, 1): 0}
order = [(0, 1)]
frontier = [(0, 1)]
counts = [1]
tag_of = {}       # 'f' or 'g' = last map applied (red/blue)
fails = []

def gmap(p, q):
    return (-q, p) if p > 0 else (q, -p)

for n in range(MAX):
    newf = []
    seen = set()
    for (p, q) in frontier:
        c1 = (p + q, q)
        if c1 not in rank_of:
            if c1 in seen:
                fails.append(('WAVE-COLLISION-f', n + 1, c1))
            else:
                seen.add(c1); newf.append(c1); tag_of[c1] = 'f'
        if p:
            c2 = gmap(p, q)
            if c2 not in rank_of:
                if c2 in seen:
                    fails.append(('WAVE-COLLISION-g', n + 1, c2))
                else:
                    seen.add(c2); newf.append(c2); tag_of[c2] = 'g'
    for c in newf:
        rank_of[c] = n + 1
    frontier = newf
    order.extend(frontier)
    counts.append(len(frontier))
    print("rank %d: %d vertices, cum %d, %.1fs" % (n + 1, len(frontier), len(order), time.time() - t0), flush=True)

# ---- check 1: recurrence a(n) = a(n-1) + a(n-3) for 4 <= n <= MAX ----
rec_ok = all(counts[n] == counts[n - 1] + counts[n - 3] for n in range(4, MAX + 1))
rec_fail_at_3 = (counts[3] != counts[2] + counts[0])  # should be True (recurrence fails at n=3)

# ---- check 2: sign <-> tag (blue iff negative) ----
sign_ok = True
for c, t in tag_of.items():
    if (t == 'f') != (c[0] > 0):
        sign_ok = False; fails.append(('SIGN', c, t)); break

# ---- check 3: structural claims at every vertex ----
struct_fails = 0
for (p, q), n in rank_of.items():
    if n == 0:
        continue
    if p > 0:
        if rank_of.get((p - q, q)) != n - 1:
            struct_fails += 1; fails.append(('PARENT-POS', (p, q), n))
        if n + 1 <= MAX:
            if rank_of.get((p + q, q)) != n + 1:
                struct_fails += 1; fails.append(('CHILD-F-POS', (p, q), n))
            if rank_of.get(gmap(p, q)) != n + 1:
                struct_fails += 1; fails.append(('CHILD-G-POS', (p, q), n))
    else:
        if rank_of.get(gmap(p, q)) != n - 1:
            struct_fails += 1; fails.append(('PARENT-NEG', (p, q), n))
        if -q < p:
            if n + 1 <= MAX and rank_of.get((p + q, q)) != n + 1:
                struct_fails += 1; fails.append(('CHILD-F-B0', (p, q), n))
        elif p == -q:
            if rank_of.get((0, 1)) != n - 2:
                struct_fails += 1; fails.append(('MINUS1', (p, q), n))
        else:
            if rank_of.get((p + q, q)) != n - 3:
                struct_fails += 1; fails.append(('UNCLE-3', (p, q), n))

# ---- check 4: negative-CF formula d(x) = sum(c_i) + k - 1 for x>0; d(x)=1+d(-1/x) for x<0 ----
def D_negcf(p, q):
    s = 0; k = 0
    while True:
        c = -((-p) // q)   # ceil(p/q)
        s += c; k += 1
        r = c * q - p
        if r == 0:
            return s + k - 1
        p, q = q, r

cf_fails = 0
for (p, q), n in rank_of.items():
    if n > CFCHECK or n == 0:
        continue
    if p > 0:
        if D_negcf(p, q) != n:
            cf_fails += 1; fails.append(('NEGCF', (p, q), n))
    else:
        pp, qq = gmap(p, q)
        if 1 + D_negcf(pp, qq) != n:
            cf_fails += 1; fails.append(('NEGCF-NEG', (p, q), n))

# ---- check 5: regular-CF formula (odd-length-r form): d = sum(even-idx) + 3*sum(odd-idx) - 2 ----
def D_regcf(p, q):
    a = []
    while q:
        a.append(p // q)
        p, q = q, p - (p // q) * q
    if len(a) % 2 == 1:            # want an even number of digits (last index r odd)
        if a[-1] >= 2:
            a[-1] -= 1; a.append(1)
        else:                      # a == [1], i.e. x = 1: odd-r form is [0; 1]
            a = [0, 1]
    ev = sum(a[i] for i in range(0, len(a), 2))
    od = sum(a[i] for i in range(1, len(a), 2))
    return ev + 3 * od - 2

reg_fails = 0
for (p, q), n in rank_of.items():
    if n > CFCHECK or n == 0:
        continue
    if p > 0:
        if D_regcf(p, q) != n:
            reg_fails += 1; fails.append(('REGCF', (p, q), n, D_regcf(p, q)))
    else:
        pp, qq = gmap(p, q)
        if 1 + D_regcf(pp, qq) != n:
            reg_fails += 1; fails.append(('REGCF-NEG', (p, q), n))

# ---- check 6: class automaton (r+, r-, b0, b1) transitions ----
def cls(p, q):
    if p > q: return 0        # x > 1
    if p > 0: return 1        # 0 < x <= 1
    if -q < p: return 2       # -1 < x < 0
    return 3                  # x <= -1

by_rank = [[0, 0, 0, 0] for _ in range(MAX + 1)]
for (p, q), n in rank_of.items():
    if n >= 1:
        by_rank[n][cls(p, q)] += 1
auto_ok = True
for n in range(1, MAX):
    v = by_rank[n]; w = by_rank[n + 1]
    if not (w[0] == v[0] + v[1] and w[1] == v[2] and w[2] == v[0] and w[3] == v[1]):
        auto_ok = False; fails.append(('AUTOMATON', n))

# ---- check 7: OEIS A226247/A226248 term-by-term including order ----
A226247 = [1,1,1,1,1,2,1,3,2,1,4,3,2,1,1,5,4,3,2,2,3,1,6,5,4,3,3,5,2,5,3,1,7,6,5,4,4,7,3,8,5,2,7,5,3,1,1,8,7,6,5,5,9,4,11,7,3,11,8,5,2,2,9,7,5,3,3,4,1,9,8,7,6,6,11,5,14,9,4,15,11,7,3,3]
A226248 = [0,1,2,-1,3,-1,4,-1,1,5,-1,2,3,-2,6,-1,3,5,-3,5,-2,7,-1,4,7,-4,8,-3,7,-2,1,8,-1,5,9,-5,11,-4,11,-3,2,9,-2,3,4,-3,9,-1,6,11,-6,14,-5,15,-4,3,14,-3,5,7,-5,11,-2,5,8,-5,7,-3,10,-1,7,13,-7]
oeis_ok = True
for i in range(min(len(A226247), len(A226248))):
    p, q = order[i]
    if q != A226247[i] or p != A226248[i]:
        oeis_ok = False; fails.append(('OEIS', i, order[i], (A226248[i], A226247[i])))
        break

# ---- check 8: counts match A097333 shifted: a(n) = A097333(n-1) ----
A097333 = [1,2,2,3,5,7,10,15,22,32,47,69,101,148,217,318,466,683,1001,1467,2150,3151,4618,6768,9919,14537,21305,31224,45761,67066,98290,144051,211117,309407,453458,664575,973982,1427440,2092015,3065997,4493437,6585452]
a97_ok = all(counts[n] == A097333[n - 1] for n in range(1, min(MAX + 1, len(A097333) + 1)))

print("=" * 70)
print("counts a(0..%d): %s" % (MAX, counts))
print("recurrence a(n)=a(n-1)+a(n-3) for 4<=n<=%d : %s" % (MAX, "PASS" if rec_ok else "FAIL"))
print("recurrence correctly fails at n=3 (a(3)=%d vs a(2)+a(0)=%d): %s" % (counts[3], counts[2] + counts[0], "PASS" if rec_fail_at_3 else "FAIL"))
print("blue<->negative (tag g iff x<0), all %d vertices: %s" % (len(tag_of), "PASS" if sign_ok else "FAIL"))
print("structure (parents/children/uncle-3), all vertices: %s (%d fails)" % ("PASS" if struct_fails == 0 else "FAIL", struct_fails))
print("neg-CF distance formula, all vertices rank<=%d: %s (%d fails)" % (CFCHECK, "PASS" if cf_fails == 0 else "FAIL", cf_fails))
print("reg-CF distance formula (odd-r form), rank<=%d: %s (%d fails)" % (CFCHECK, "PASS" if reg_fails == 0 else "FAIL", reg_fails))
print("4-class automaton transitions: %s" % ("PASS" if auto_ok else "FAIL"))
print("OEIS A226247/A226248 first %d terms incl. order: %s" % (len(A226247), "PASS" if oeis_ok else "FAIL"))
print("counts match A097333 shift: %s" % ("PASS" if a97_ok else "FAIL"))
print("total anomalies: %d" % len(fails))
for x in fails[:20]:
    print("  FAIL:", x)
print("class counts (r+, r-, b0, b1) by rank:")
for n in range(1, min(16, MAX + 1)):
    v = by_rank[n]
    print("  n=%2d: %s  total %d" % (n, v, sum(v)))
print("total time %.1fs" % (time.time() - t0))

# ---- dump data for the writeup ----
import json
tree = []   # (num, den, rank, tag, parent_num, parent_den) for ranks 0..8
for (p, q), n in rank_of.items():
    if n <= 8:
        if n == 0:
            tree.append((p, q, n, 'root', None, None))
        elif p > 0:
            tree.append((p, q, n, 'f', p - q, q))
        else:
            pp, qq = gmap(p, q)
            tree.append((p, q, n, 'g', pp, qq))
with open('treedata.json', 'w') as fh:
    json.dump({'counts': counts, 'classes': by_rank, 'tree': tree}, fh)
print("dumped treedata.json")
