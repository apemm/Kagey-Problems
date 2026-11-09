"""Lazy-constraint (counterexample-guided) SAT search for structured boards.

Layout: W_h pad columns of row PL, then the q_h doubles of K_{odd,even} at spacing s (one per slot,
order free), s - 1 singleton columns between consecutive doubles, then W_h pad columns of row PR.
Sea-cell domains depend on MODE:
  free  every sea cell may use any row
  bdry  every sea cell in {1, h}
  hyb   gaps within TR of either end: any row; middle gaps "1, x, h" with x in {1, h} (s = 4 only)
The solver starts with only the structural constraints. Each candidate board is checked exactly
(fastcheck.violations, which is sound and complete for boards whose doubles are distinct pairs of a
triangle-free graph and which contain every pair of F). Every violation found is turned into a no-good
clause on the at most 8 cells it involves, and the solver is called again. The no-goods are exact (any
board agreeing on those cells has the same violation), so UNSAT is a proof that no board of this layout
exists, and SAT returns a board that passes the full checker; it is then re-verified with verify_narrow.
Memory stays small because only violated constraints are ever added.
Usage: python cegar_board.py h s MODE TR PL PR CAP_SECONDS [seed]"""
import sys, json, time, random
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from fastcheck import shapes, rival


def check(h, cols):
    """Same tests as fastcheck.violations, but each tilt-tilt violation also returns its partner."""
    m = len(cols); B = [frozenset(c) for c in cols]
    F = {frozenset(c) for c in cols if len(c) == 2}
    seen = {}; det = []
    for sh in shapes(h):
        span = max(dx for dx, _ in sh)
        for x0 in range(0, m - span):
            cs = [(x0 + dx, r) for dx, r in sh]
            k = [r in B[x] for x, r in cs]
            if sum(k) < 2:
                continue
            Pw = frozenset(c for c, kk in zip(cs, k) if not kk)
            if not Pw:
                det.append(('hidden', cs, [], None))
            elif Pw in seen:
                det.append(('tilt-tilt', cs, sorted(Pw), seen[Pw]))
            else:
                seen[Pw] = cs
                if rival(Pw, B, F):
                    det.append(('rival', cs, sorted(Pw), None))
    return len(det), det


def main():
    h, s = int(sys.argv[1]), int(sys.argv[2]); mode = sys.argv[3]; TR = int(sys.argv[4])
    PL, PR, cap = int(sys.argv[5]), int(sys.argv[6]), float(sys.argv[7])
    seed = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    import os
    W = int(os.environ.get('PADW', 1 + (h - 1) ** 2 // 4))
    ORDER = json.loads(os.environ['ORDER']) if os.environ.get('ORDER') else None
    SYM = os.environ.get('SYM') == '1'
    QUIET = os.environ.get('QUIET') == '1'
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    q = len(E); rows = range(1, h + 1)
    pool = IDPool(); cl = []
    P = {(j, e): pool.id(('P', j, e)) for j in range(q) for e in E}
    for j in range(q):
        cl += CardEnc.equals([P[j, e] for e in E], 1, vpool=pool, encoding=EncType.seqcounter).clauses
    for e in E:
        cl += CardEnc.equals([P[j, e] for j in range(q)], 1, vpool=pool, encoding=EncType.seqcounter).clauses
    if ORDER:
        for j, e in enumerate(ORDER):
            cl.append([P[j, tuple(sorted(e))]])
    RULE = os.environ.get('RULE')
    if RULE and RULE.startswith('mod4'):
        # slot-residue rule: tau = 2 vertices at even slots (residue by w), odd slots hold the other
        # edges with even-row class fixed by the slot mod 4 (interior slots only)
        j0 = int(RULE.split(':')[1]) if ':' in RULE else 0
        def v2(n):
            c = 0
            while n % 2 == 0:
                n //= 2; c += 1
            return c
        def tauw(e):
            o = e[0] if e[0] % 2 else e[1]
            if o in (1, h):
                return None
            if o % 4 == 1:
                t = v2(o - 1); u = (o - 1) >> t; w = u % 4
            else:
                t = v2(h - o); u = (h - o) >> t; w = (-u) % 4
            return (t, w)
        RTR = int(os.environ.get('RULE_TR', TR)); lo, hi = RTR, q - 1 - RTR
        for j in range(lo, hi + 1):
            for e in E:
                ev = e[0] if e[0] % 2 == 0 else e[1]
                tw = tauw(e)
                hot = tw is not None and tw[0] == 2
                rj = (j - j0) % 4
                ok = True
                if rj % 2 == 1:
                    ok = (not hot) and (ev % 4 == (0 if rj == 1 else 2))
                elif hot:
                    ok = (rj == 0) == (tw[1] == 1)
                if not ok:
                    cl.append([-P[j, e]])
    if SYM:
        sig = lambda e: tuple(sorted((h + 1 - e[0], h + 1 - e[1])))
        for j in range(q):
            for e in E:
                cl.append([-P[j, e], P[q - 1 - j, sig(e)]])
    ncol = 2 * W + q + (q - 1) * (s - 1)
    kind = {}          # column -> ('pad', row) | ('dbl', j) | ('sea', gap, pos)
    x = 0
    for _ in range(W):
        kind[x] = ('pad', PL); x += 1
    for j in range(q):
        kind[x] = ('dbl', j); x += 1
        if j < q - 1:
            for i in range(s - 1):
                kind[x] = ('sea', j, i); x += 1
    for _ in range(W):
        kind[x] = ('pad', PR); x += 1
    assert x == ncol

    def domain(g, i):
        if mode == 'free':
            return list(rows)
        if mode == 'bdry':
            return [1, h]
        if g < TR or g >= q - 1 - TR:
            return list(rows)
        if SYM and g == (q - 2) // 2 and i == 1:
            return [(h + 1) // 2]
        return [[1], [1, h], [h]][i]
    cell = {}          # (x, r) -> var, or True/False constant
    for x, k in kind.items():
        if k[0] == 'pad':
            for r in rows:
                cell[x, r] = (r == k[1])
        elif k[0] == 'dbl':
            j = k[1]
            for r in rows:
                v = pool.id(('D', j, r)); cell[x, r] = v
                inc = [P[j, e] for e in E if r in e]
                cl.append([-v] + inc)
                for p in inc:
                    cl.append([v, -p])
        else:
            dom = domain(k[1], k[2])
            vs = []
            for r in rows:
                if r in dom:
                    v = pool.id(('S', x, r)); cell[x, r] = v; vs.append(v)
                else:
                    cell[x, r] = False
            cl += CardEnc.equals(vs, 1, vpool=pool, encoding=EncType.pairwise).clauses

    if SYM:
        for x0 in range(ncol):
            y0 = ncol - 1 - x0
            for r in rows:
                a, b = cell[x0, r], cell[y0, h + 1 - r]
                if a in (True, False) or b in (True, False):
                    if a in (True, False) and b in (True, False):
                        assert a == b, 'pads not half-turn symmetric'
                    elif a in (True, False):
                        cl.append([b] if a else [-b])
                    else:
                        cl.append([a] if b else [-a])
                else:
                    cl.append([-a, b]); cl.append([a, -b])
    def nogood(black_cells, white_cells):
        """Clause: not (all black_cells black and all white_cells white)."""
        c = []
        for xr in black_cells:
            v = cell[xr]
            if v is True:
                continue
            if v is False:
                return None          # already impossible, clause trivially true
            c.append(-v)
        for xr in white_cells:
            v = cell[xr]
            if v is False:
                continue
            if v is True:
                return None
            c.append(v)
        return c

    rng = random.Random(seed)
    S = Solver(name='cadical153', bootstrap_with=cl)
    if os.environ.get('PHASE'):
        # warm start: prefer the order and sea cells of a stored board (same layout)
        pb = json.load(open(os.environ['PHASE']))
        ph = []
        for j, e in enumerate(pb['order']):
            ph.append(P[j, tuple(sorted(e))])
        for x, k in kind.items():
            if k[0] == 'sea':
                for r in pb['cols'][x]:
                    v = cell[x, r]
                    if v not in (True, False):
                        ph.append(v)
        S.set_phases(ph)
        print('phases set', len(ph), flush=True)
    t0 = time.time(); it = 0; added = 0
    while True:
        it += 1
        if time.time() - t0 > cap:
            print('UNRESOLVED at cap after', it, 'iterations,', added, 'no-goods', flush=True); return
        if not S.solve():
            print('UNSAT after', it, 'iterations,', added, 'no-goods,', round(time.time() - t0), 's', flush=True)
            return
        M = set(l for l in S.get_model() if l > 0)
        cols = []
        for x in range(ncol):
            cols.append({r for r in rows if (cell[x, r] is True) or (cell[x, r] not in (True, False) and cell[x, r] in M)})
        nbad, det = check(h, cols)
        if (not QUIET and it % 10 == 1) or nbad == 0:
            print('iter', it, 'violations', nbad, 'no-goods', added, 'time', round(time.time() - t0), flush=True)
        if nbad == 0:
            order = [next(e for e in E if P[j, e] in M) for j in range(q)]
            word = ','.join('.'.join(str(r) for r in sorted(c)) for c in cols)
            out = 'cegar_h%d_s%d_%s_t%d_%d%d.json' % (h, s, mode, TR, PL, PR)
            json.dump({'h': h, 's': s, 'mode': mode, 'TR': TR, 'pads': [PL, PR], 'W': W, 'w': ncol,
                       'core_width': ncol - 2 * W, 'cols': [sorted(c) for c in cols], 'order': order},
                      open(out, 'w'))
            print('FOUND width', ncol, 'core', ncol - 2 * W, 'order', order, '->', out, flush=True); return
        B = [frozenset(c) for c in cols]
        seenP = {}
        for v, cs, Pw, partner in det:
            blk = [c for c in cs if c not in set(Pw)]
            wht = list(Pw)
            if v == 'hidden':
                c = nogood(cs, [])
            elif v == 'tilt-tilt':
                # the other rectangle with the same presentation: recover it from the earlier ones
                other = partner
                ob = [c for c in other if c not in set(Pw)]
                c = nogood(sorted(set(blk) | set(ob)), wht)
            else:  # rival with an axis-aligned rectangle
                Pw = sorted(Pw)
                if len(Pw) == 1:
                    (px, pr), = Pw
                    ss = [t for t in B[px] if t != pr and (t - pr) % 2]
                    c = nogood(blk + [(px, ss[0])], wht)
                else:
                    (px, pr), (pz, ps) = Pw
                    if px == pz:
                        c = nogood(blk, wht)
                    elif pr == ps:
                        t = min(B[px] & B[pz])
                        c = nogood(blk + [(px, t), (pz, t)], wht)
                    else:
                        c = nogood(blk + [(px, ps), (pz, pr)], wht)
            if c is None:
                continue
            if not c:
                print('UNSAT: a violation independent of all variables (pads alone)', flush=True); return
            S.add_clause(c); added += 1
            seenP[frozenset(Pw)] = cs


def find_other(h, cols, cs, Pw):
    """Find a different rectangle (2+ black corners) with white set Pw."""
    from fastcheck import shapes
    m = len(cols); Pw = set(Pw)
    for sh in shapes(h):
        span = max(dx for dx, _ in sh)
        for x0 in range(0, m - span):
            cc = [(x0 + dx, r) for dx, r in sh]
            if cc == cs or sorted(cc) == sorted(cs):
                continue
            wh = {c for c in cc if c[1] not in cols[c[0]]}
            if wh == Pw and len(wh) <= 2:
                return cc
    raise RuntimeError('no partner found')


if __name__ == '__main__':
    main()
