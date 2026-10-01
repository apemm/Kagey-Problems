"""Draw the figures of notes.tex as TikZ files in figs/.

Every blackout drawn here is checked against the definition first, with the rectangle list of
verify_narrow.py (rectangles from equal diagonals with a common midpoint). Coordinates follow
the conventions of PROBLEM.md: (i, j) is column i, row j, and (1, 1) is the top-left point.

Run from this folder: python make_figures.py
"""
import os
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from verify_narrow import collision, four_row_upper_candidates, no_short_cycles, rectangles  # noqa: E402

FIGS = os.path.join(HERE, 'figs')
UNIT = 0.7           # cm between neighbouring grid points
TEXTWIDTH = 16.0     # cm available on the page (we stay below this)


# ---------------------------------------------------------------- grid helpers (1-based)

def bit(p, m):
    i, j = p
    return 1 << ((j - 1) * m + (i - 1))


def to_mask(points, m):
    return sum(bit(p, m) for p in set(points))


def to_points(mask, n, m):
    return sorted((i, j) for j in range(1, n + 1) for i in range(1, m + 1) if mask & bit((i, j), m))


def all_rects(n, m):
    return [to_points(r, n, m) for r in rectangles(n, m)]


def is_valid(n, m, black):
    return collision(rectangles(n, m), to_mask(black, m)) is None


def confused_pair(n, m, black):
    pair = collision(rectangles(n, m), to_mask(black, m))
    return None if pair is None else [to_points(r, n, m) for r in pair]


def axis_ok(n, m, black):
    return no_short_cycles(n, m, to_mask(black, m))


def from_picture(rows):
    """Rows top to bottom, '#' = blacked out."""
    return {(i + 1, j + 1) for j, row in enumerate(rows) for i, ch in enumerate(row) if ch == '#'}


def ordered(corners):
    """The 4 corners in order around the rectangle."""
    cx = sum(p[0] for p in corners) / 4
    cy = sum(p[1] for p in corners) / 4
    from math import atan2
    return sorted(corners, key=lambda p: atan2(p[1] - cy, p[0] - cx))


# ---------------------------------------------------------------- the picture builder

COLORS = {'A': 'rectA', 'B': 'rectB', 'C': 'rectC'}


class Pic:
    """A TikZ picture in grid units; x to the right, row j drawn at y = -j."""

    def __init__(self, scale=1.0):
        self.scale = scale
        self.cmds = []
        self.xmin = self.ymin = 1e9
        self.xmax = self.ymax = -1e9

    def _box(self, x, y, pad=0.0):
        self.xmin = min(self.xmin, x - pad)
        self.xmax = max(self.xmax, x + pad)
        self.ymin = min(self.ymin, y - pad)
        self.ymax = max(self.ymax, y + pad)

    def add(self, cmd):
        self.cmds.append(cmd)

    def width(self):
        return (self.xmax - self.xmin) * UNIT

    # grid of points
    def grid(self, n, m, black=(), ox=0, labels=True, grey=(), hidden=(), shade=(),
             lines=True, small=False):
        black, grey, hidden = set(black), set(grey), set(hidden)
        r = 0.17 if not small else 0.13
        if shade:
            for (i, j) in shade:
                self.add(rf'\fill[keptcol] ({ox + i - 0.42},{-j - 0.42}) rectangle ({ox + i + 0.42},{-j + 0.42});')
        if lines:
            self.add(rf'\draw[gridcol] ({ox + 1},-1) grid ({ox + m},{-n});')
        for j in range(1, n + 1):
            for i in range(1, m + 1):
                x, y = ox + i, -j
                if (i, j) in hidden:
                    self.add(rf'\draw[hidcol,line width=0.5pt] ({x},{y}) circle ({r * 0.55});')
                elif (i, j) in grey:
                    self.add(rf'\fill[pencol] ({x},{y}) circle ({r});')
                elif (i, j) in black:
                    self.add(rf'\fill[black] ({x},{y}) circle ({r});')
                else:
                    self.add(rf'\filldraw[fill=white,draw=keptline,line width=0.6pt] ({x},{y}) circle ({r});')
                self._box(x, y, 0.4)
        if labels:
            for i in range(1, m + 1):
                self.add(rf'\node[lab] at ({ox + i},-0.35) {{{i}}};')
            for j in range(1, n + 1):
                self.add(rf'\node[lab] at ({ox + 0.35},{-j}) {{{j}}};')
            self._box(ox + 0.25, -0.25)

    def rect(self, corners, color='rectA', ox=0, dashed=False, width=1.6, fill=False):
        pts = ordered(corners)
        path = ' -- '.join(f'({ox + i},{-j})' for i, j in pts) + ' -- cycle'
        style = f'draw={color},line width={width}pt,line join=round'
        if dashed:
            style += ',dash pattern=on 3pt off 2pt'
        if fill:
            self.add(rf'\fill[{color},opacity=0.12] {path};')
        self.add(rf'\draw[{style}] {path};')

    def ring(self, p, color='rectA', ox=0, radius=0.3):
        i, j = p
        self.add(rf'\draw[{color},line width=1.1pt] ({ox + i},{-j}) circle ({radius});')

    def seg(self, a, b, color='black', ox=0, width=1.0, dashed=False, extra=''):
        style = f'draw={color},line width={width}pt'
        if dashed:
            style += ',dash pattern=on 2.5pt off 2pt'
        if extra:
            style += ',' + extra
        self.add(rf'\draw[{style}] ({ox + a[0]},{-a[1]}) -- ({ox + b[0]},{-b[1]});')

    def text(self, x, y, s, style='capt'):
        self.add(rf'\node[{style}] at ({x},{y}) {{{s}}};')
        self._box(x, y)

    def caption(self, x, s, y=None, w=None):
        """A label under a panel; w (grid units) is the width it may wrap to."""
        y = self.ymin - 0.35 if y is None else y
        if w is None:
            self.add(rf'\node[capt,anchor=north] at ({x},{y}) {{{s}}};')
        else:
            tw = w * UNIT * self.scale
            self.add(rf'\node[capt,anchor=north,text width={tw:.2f}cm,align=center] at ({x},{y}) {{{s}}};')
        self._box(x, y - 0.6)

    # a graph with given vertex positions (grid units)
    def graph(self, pos, edges, ox=0, oy=0, hi=(), pend=(), size=0.62):
        for (u, v) in edges:
            key = frozenset((u, v))
            if key in {frozenset(e) for e in hi}:
                style = 'draw=cyccol,line width=2pt'
            elif key in {frozenset(e) for e in pend}:
                style = 'draw=pencol,line width=1.3pt,dash pattern=on 3pt off 2pt'
            else:
                style = 'draw=black!75,line width=0.9pt'
            (x1, y1), (x2, y2) = pos[u], pos[v]
            self.add(rf'\draw[{style}] ({ox + x1},{oy + y1}) -- ({ox + x2},{oy + y2});')
        for v, (x, y) in pos.items():
            kind = 'rowv' if v[0] == 'r' else 'colv'
            label = f'${v[0]}_{{{v[1:]}}}$'
            self.add(rf'\node[{kind}] at ({ox + x},{oy + y}) {{{label}}};')
            self._box(ox + x, oy + y, size / 2 + 0.05)

    def tex(self):
        u = UNIT * self.scale
        body = '\n  '.join(self.cmds)
        return (f'\\begin{{tikzpicture}}[x={u:.3f}cm,y={u:.3f}cm,baseline=(current bounding box.north)]\n'
                f'  {body}\n\\end{{tikzpicture}}\n')


def save(name, pic):
    w = pic.width() * pic.scale
    assert w < TEXTWIDTH, (name, w)
    with open(os.path.join(FIGS, name + '.tex'), 'w') as f:
        f.write(f'% generated by make_figures.py; width about {w:.1f} cm\n')
        f.write(pic.tex())
    print(f'{name:22s} {w:5.1f} cm')


def bipartite_layout(n, m, gap=1.6, x0=0.0, y0=-1.0, step=1.0):
    """Rows on the left, columns on the right, both centred vertically."""
    pos = {}
    top = max(n, m)
    for j in range(1, n + 1):
        pos[f'r{j}'] = (x0, y0 - (j - 1) * step - (top - n) * step / 2)
    for i in range(1, m + 1):
        pos[f'c{i}'] = (x0 + gap, y0 - (i - 1) * step - (top - m) * step / 2)
    return pos


def incidence_edges(black):
    return [(f'r{j}', f'c{i}') for i, j in sorted(black)]


def cycle_layout(names, cx, cy, radius, start=90):
    from math import cos, sin, radians
    k = len(names)
    return {v: (cx + radius * cos(radians(start - 360 * t / k)), cy + radius * sin(radians(start - 360 * t / k)))
            for t, v in enumerate(names)}


# ---------------------------------------------------------------- the figures
# Panel layout: a grid with m columns occupies x in [0.4, m + 0.4]; captions wrap to the panel.

def fig_game():
    n, m = 3, 4
    black = {(i, 1) for i in range(1, m + 1)} | {(1, 2), (1, 3)}
    assert is_valid(n, m, black)
    diamond = [(2, 2), (3, 1), (4, 2), (3, 3)]
    p = Pic(0.9)
    gap = m + 1.6
    capy = -3.7
    p.grid(n, m, (), ox=0)
    p.ring((3, 2), 'rectB', radius=0.3)
    p.caption(2.5, '(a) the point $(3,2)$ is ringed', y=capy, w=gap - 0.4)
    p.grid(n, m, black, ox=gap)
    p.caption(gap + 2.5, '(b) our blackout', y=capy, w=gap - 0.4)
    p.grid(n, m, black, ox=2 * gap)
    p.rect(diamond, 'rectA', ox=2 * gap, dashed=True)
    p.caption(2 * gap + 2.5, '(c) the rectangle', y=capy, w=gap - 0.4)
    vis = [q for q in diamond if q not in black]
    everything = {(i, j) for i in range(1, m + 1) for j in range(1, n + 1)}
    p.grid(n, m, (), ox=3 * gap, hidden=everything - set(vis))
    for q in vis:
        p.ring(q, 'rectA', ox=3 * gap)
    p.caption(3 * gap + 2.5, '(d) what we are shown', y=capy, w=gap - 0.4)
    save('game', p)


def fig_rects():
    n = m = 4
    p = Pic(0.85)
    gap = m + 1.8
    shapes = [
        ([(1, 1), (3, 1), (3, 2), (1, 2)], '(a) axis-aligned'),
        ([(1, 2), (2, 1), (3, 2), (2, 3)], '(b) a tilted square'),
        ([(1, 2), (2, 1), (4, 3), (3, 4)], '(c) tilted, sides $1:2$'),
        ([(1, 1), (3, 1), (4, 3), (2, 3)], '(d) not a rectangle'),
    ]
    rect_sets = [set(r) for r in all_rects(n, m)]
    for k, (shape, cap) in enumerate(shapes):
        assert (set(shape) in rect_sets) == (k < 3)
        ox = k * gap
        p.grid(n, m, (), ox=ox)
        p.rect(shape, 'rectA' if k < 3 else 'rectB', ox=ox, fill=True)
        if k >= 2:
            a, b, c, d = ordered(shape)
            p.seg(a, c, 'black!60', ox=ox, width=0.7, dashed=True)
            p.seg(b, d, 'black!60', ox=ox, width=0.7, dashed=True)
        p.caption(ox + 2.5, cap, y=-4.7, w=gap - 0.3)
    save('rects', p)


def fig_strip_rects():
    n, m = 2, 3
    p = Pic()
    gap = m + 2.0
    for k, (a, b) in enumerate([(1, 2), (1, 3), (2, 3)]):
        ox = k * gap
        p.grid(n, m, (), ox=ox)
        p.rect([(a, 1), (b, 1), (b, 2), (a, 2)], 'rectA', ox=ox, fill=True)
        p.caption(ox + 2, f'$R_{{{a},{b}}}$', y=-2.7)
    save('strip_rects', p)


def fig_two_blackouts():
    n, m = 2, 3
    good = {(1, 2), (2, 2), (3, 1), (3, 2)}
    bad = {(1, 1), (1, 2), (2, 1), (2, 2)}
    assert is_valid(n, m, good) and not is_valid(n, m, bad)
    p = Pic()
    p.grid(n, m, good, ox=0)
    p.caption(2, '(a) valid', y=-2.7)
    ox = m + 3.5
    p.grid(n, m, bad, ox=ox)
    p.rect([(1, 1), (3, 1), (3, 2), (1, 2)], 'rectA', ox=ox, width=1.4)
    p.rect([(2, 1), (3, 1), (3, 2), (2, 2)], 'rectB', ox=ox, dashed=True, width=1.4)
    for q in [(3, 1), (3, 2)]:
        p.ring(q, 'black!70', ox=ox, radius=0.32)
    p.caption(ox + 2, '(b) not valid', y=-2.7)
    save('two_blackouts', p)


def fig_difference():
    n, m = 2, 4
    p = Pic()
    r1 = [(1, 1), (2, 1), (2, 2), (1, 2)]
    r2 = [(1, 1), (3, 1), (3, 2), (1, 2)]
    r3 = [(3, 1), (4, 1), (4, 2), (3, 2)]
    p.grid(n, m, (), ox=0, shade=set(r1) ^ set(r2))
    p.rect(r1, 'rectA', width=1.4)
    p.rect(r2, 'rectB', dashed=True, width=1.4)
    p.caption(2.5, r'(a) $R_{1,2}$ and $R_{1,3}$', y=-2.7)
    ox = m + 3.0
    p.grid(n, m, (), ox=ox, shade=set(r1) ^ set(r3))
    p.rect(r1, 'rectA', ox=ox, width=1.4)
    p.rect(r3, 'rectB', ox=ox, dashed=True, width=1.4)
    p.caption(ox + 2.5, r'(b) $R_{1,2}$ and $R_{3,4}$', y=-2.7)
    save('difference', p)


def fig_strip():
    n, m = 2, 6
    black = {(1, 1), (2, 2), (3, 2), (4, 1), (4, 2), (5, 1), (6, 2)}
    assert is_valid(n, m, black) and len(black) == m + 1
    p = Pic()
    p.add(r'\fill[keptcol] (3.6,-0.6) rectangle (4.4,-2.4);')
    p.grid(n, m, black, ox=0)
    save('strip_max', p)
    # the 12 maximum blackouts of the 2 x 3 strip, grouped by the fully black column
    n, m = 2, 3
    pts = [(i, j) for j in (1, 2) for i in (1, 2, 3)]
    found = [set(S) for S in combinations(pts, 4) if is_valid(n, m, S)]
    assert len(found) == 12
    groups = {c: sorted((S for S in found if {(c, 1), (c, 2)} <= S), key=sorted) for c in (1, 2, 3)}
    assert all(len(g) == 4 for g in groups.values())
    q = Pic(0.8)
    for g, c in enumerate((1, 2, 3)):
        for k, S in enumerate(groups[c]):
            ox = g * 10.0 + (k % 2) * 4.4
            oy = -(k // 2) * 2.8
            q.add(rf'\begin{{scope}}[yshift={oy * UNIT * q.scale:.3f}cm]')
            q.grid(n, m, S, ox=ox, labels=False, lines=False)
            q.add(r'\end{scope}')
            q._box(ox + 1, oy - 2.4)
        q.caption(g * 10.0 + 4.2, f'column {c} black', y=-5.4)
    save('strip_all', q)


def fig_incidence():
    n, m = 3, 4
    black = {(1, 1), (2, 1), (3, 1), (4, 1), (1, 2), (1, 3)}
    assert is_valid(n, m, black)
    p = Pic()
    p.grid(n, m, black, ox=0)
    p.caption(2.5, '(a) the blackout', y=-4.3)
    pos = bipartite_layout(n, m, gap=2.6, x0=m + 3.0, y0=-0.6, step=1.1)
    p.graph(pos, incidence_edges(black))
    p.caption(m + 4.3, '(b) its graph $G_S$', y=-4.3)
    save('incidence', p)


def fig_c4():
    n, m = 2, 3
    black = {(1, 1), (1, 2), (2, 1), (2, 2)}
    p = Pic()
    p.grid(n, m, black, ox=0)
    p.rect([(1, 1), (3, 1), (3, 2), (1, 2)], 'rectA', width=1.4)
    p.rect([(2, 1), (3, 1), (3, 2), (2, 2)], 'rectB', dashed=True, width=1.4)
    p.caption(2, '(a) a black 4-cycle', y=-3.1)
    pos = {'r1': (m + 3.0, -0.8), 'c1': (m + 4.8, -0.8), 'r2': (m + 4.8, -2.4), 'c2': (m + 3.0, -2.4),
           'c3': (m + 6.6, -1.6)}
    edges = incidence_edges(black)
    p.graph(pos, edges, hi=edges)
    p.caption(m + 4.8, '(b) $G_S$', y=-3.1)
    save('c4', p)


def fig_c6():
    n, m = 3, 3
    black = {(1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (3, 1)}
    r1 = [(1, 1), (2, 1), (2, 2), (1, 2)]
    r2 = [(2, 1), (3, 1), (3, 3), (2, 3)]
    assert [q for q in r1 if q not in black] == [q for q in r2 if q not in black] == [(2, 1)]
    p = Pic()
    p.grid(n, m, black, ox=0)
    p.rect(r1, 'rectA', width=1.4)
    p.rect(r2, 'rectB', dashed=True, width=1.4)
    p.ring((2, 1), 'black!70', radius=0.32)
    p.caption(2, '(a) a black 6-cycle', y=-4.2)
    pos = cycle_layout(['r1', 'c1', 'r2', 'c2', 'r3', 'c3'], m + 4.4, -2.0, 1.5)
    edges = incidence_edges(black)
    p.graph(pos, edges, hi=edges)
    p.caption(m + 4.4, '(b) $G_S$', y=-4.2)
    save('c6', p)


def fig_threecorners():
    n, m = 4, 5
    pp, q, r = (1, 2), (2, 1), (4, 3)
    u = (pp[0] - q[0], pp[1] - q[1])
    v = (r[0] - q[0], r[1] - q[1])
    assert u[0] * v[0] + u[1] * v[1] == 0          # right angle at q
    fourth = (pp[0] + r[0] - q[0], pp[1] + r[1] - q[1])
    assert fourth == (3, 4) and set([pp, q, r, fourth]) in [set(x) for x in all_rects(n, m)]
    p = Pic()
    p.grid(n, m, (), ox=0, labels=False)
    p.rect([pp, q, r, fourth], 'rectA', dashed=True, width=1.0)
    p.seg(q, pp, 'rectA', width=1.6)
    p.seg(q, r, 'rectA', width=1.6)
    for z in (pp, q, r):
        p.ring(z, 'rectA', radius=0.3)
    from math import hypot
    t = 0.32
    a = (q[0] + t * u[0] / hypot(*u), q[1] + t * u[1] / hypot(*u))
    c = (q[0] + t * v[0] / hypot(*v), q[1] + t * v[1] / hypot(*v))
    b = (a[0] + c[0] - q[0], a[1] + c[1] - q[1])
    p.add(rf'\draw[black!70,line width=0.6pt] ({a[0]:.3f},{-a[1]:.3f}) -- ({b[0]:.3f},{-b[1]:.3f}) -- ({c[0]:.3f},{-c[1]:.3f});')
    p.text(0.3, -2.0, '$p$', 'tiny')
    p.text(2.0, -0.4, '$q$', 'tiny')
    p.text(4.45, -3.35, '$r$', 'tiny')
    p.text(3.0, -4.55, '$p+r-q$', 'tiny')
    save('threecorners', p)


def fig_rowbound():
    n, m = 5, 4
    good = {(1, 1), (1, 3), (1, 5), (2, 2), (2, 3), (3, 4), (4, 4), (4, 5)}
    bad = {(1, 1), (1, 3), (1, 5), (2, 2), (2, 3), (3, 4), (4, 2), (4, 5)}
    assert axis_ok(n, m, good) and not axis_ok(n, m, bad)
    colc = {1: 'rectA', 2: 'rectB', 3: 'black', 4: 'rectC'}
    p = Pic(0.85)
    panel = m + 1.2          # grid panel width
    hgap = 3.6               # graph panel width
    xs = [0, panel, panel + hgap + 1.6, 2 * panel + hgap + 1.6]
    for ox, S in ((xs[0], good), (xs[2], bad)):
        p.grid(n, m, S, ox=ox)
        for i in range(1, m + 1):
            col = sorted(j for (a, j) in S if a == i)
            if len(col) >= 2:
                p.add(rf'\draw[{colc[i]},line width=4pt,opacity=0.25,line cap=round] ({ox + i},{-col[0]}) -- ({ox + i},{-col[-1]});')
    for ox, S in ((xs[1], good), (xs[3], bad)):
        pos = {f'r{j}': (ox + 0.9 + (0.0 if j % 2 else 1.4), -j) for j in range(1, n + 1)}
        for i in range(1, m + 1):
            col = sorted(j for (a, j) in S if a == i)
            for a, b in zip(col, col[1:]):
                (x1, y1), (x2, y2) = pos[f'r{a}'], pos[f'r{b}']
                p.add(rf'\draw[{colc[i]},line width=1.6pt] ({x1},{y1}) -- ({x2},{y2});')
        for v, (x, y) in pos.items():
            p.add(rf'\node[rowv] at ({x},{y}) {{$r_{{{v[1:]}}}$}};')
            p._box(x, y, 0.45)
    caps = ['(a) a blackout', '(b) its graph $H$', '(c) another blackout', '(d) its $H$ has a triangle']
    centres = [xs[0] + 2.5, xs[1] + 1.6, xs[2] + 2.5, xs[3] + 1.6]
    widths = [panel - 0.3, hgap - 0.3, panel - 0.3, hgap - 0.3]
    for x, c, w in zip(centres, caps, widths):
        p.caption(x, c, y=-5.7, w=w)
    save('rowbound', p)


def fig_mantel():
    p = Pic()
    pos3 = {'r1': (0, -1), 'r2': (1.6, -1), 'r3': (0.8, -2.5)}
    p.graph(pos3, [('r1', 'r3'), ('r2', 'r3')])
    p.caption(0.8, '$n=3$: 2 edges', y=-3.2, w=3.2)
    pos4 = {'r1': (4.6, -1), 'r2': (6.2, -1), 'r3': (6.2, -2.5), 'r4': (4.6, -2.5)}
    p.graph(pos4, [('r1', 'r2'), ('r2', 'r3'), ('r3', 'r4'), ('r4', 'r1')])
    p.caption(5.4, '$n=4$: 4 edges', y=-3.2, w=3.2)
    pos5 = {'r1': (9.4, -1), 'r2': (11.0, -1), 'r3': (8.8, -2.5), 'r4': (10.2, -2.5), 'r5': (11.6, -2.5)}
    p.graph(pos5, [(a, b) for a in ('r1', 'r2') for b in ('r3', 'r4', 'r5')])
    p.caption(10.2, '$n=5$: 6 edges', y=-3.2, w=3.2)
    save('mantel', p)


def fig_tilted():
    rect_sets = {frozenset(r) for r in all_rects(4, 4)}
    shapes = [
        ('$D(1,1)$', [(1, 2), (2, 1), (3, 2), (2, 3)]),
        ('$A_1$', [(1, 3), (2, 4), (3, 1), (4, 2)]),
        ('$B_1$', [(1, 3), (3, 4), (2, 1), (4, 2)]),
        ('$C_1$', [(1, 2), (2, 4), (3, 1), (4, 3)]),
        ('$E_1$', [(1, 2), (3, 4), (2, 1), (4, 3)]),
    ]
    tilted = [r for r in rect_sets if len({i for i, _ in r}) > 2 or len({j for _, j in r}) > 2]
    assert all(frozenset(sh) in rect_sets for _, sh in shapes)
    p = Pic(0.85)
    gap = 4 + 1.3
    for k, (name, sh) in enumerate(shapes):
        ox = k * gap
        p.grid(4, 4, (), ox=ox, labels=(k == 0))
        p.rect(sh, 'rectA', ox=ox, fill=True, width=1.4)
        p.ring(min(sh), 'rectB', ox=ox, radius=0.3)
        p.caption(ox + 2.5, name, y=-4.6)
    save('tilted', p)
    return len(tilted)


def fig_three():
    n, m = 3, 6
    black = {(i, 1) for i in range(1, m + 1)} | {(1, 2), (1, 3)}
    assert is_valid(n, m, black)
    d1 = [(1, 2), (2, 1), (3, 2), (2, 3)]
    d3 = [(3, 2), (4, 1), (5, 2), (4, 3)]
    p = Pic(0.95)
    p.grid(n, m, black, ox=0)
    p.rect(d1, 'rectA', width=1.4)
    p.rect(d3, 'rectB', dashed=True, width=1.4)
    p.caption(3.5, '(a) row 1 and column 1, with $D(1,1)$ and $D(3,1)$', y=-4.6, w=m + 0.8)
    x0 = m + 2.4
    pos = {'r1': (x0 + 3.0, -0.6)}
    for i in range(1, m + 1):
        pos[f'c{i}'] = (x0 + (i - 1) * 1.2, -2.1)
    pos['r2'] = (x0 - 0.7, -3.6)
    pos['r3'] = (x0 + 0.7, -3.6)
    p.graph(pos, incidence_edges(black))
    p.caption(x0 + 3.0, '(b) $G_S$ is a tree', y=-4.6, w=6.5)
    save('three', p)


def four_construction(m):
    return {(i, 1) for i in range(2, m)} | {(m - 1, 2), (m, 2), (1, 3), (2, 3), (1, 4), (m, 4)}


def fig_four():
    n, m = 4, 7
    black = four_construction(m)
    assert is_valid(n, m, black) and len(black) == m + 4
    p = Pic(0.9)
    p.grid(n, m, black, ox=0)
    cyc = [(2, 1), (6, 1), (6, 2), (7, 2), (7, 4), (1, 4), (1, 3), (2, 3)]
    path = ' -- '.join(f'({i},{-j})' for i, j in cyc) + ' -- cycle'
    p.add(rf'\draw[cyccol,line width=1.8pt,line join=round,opacity=0.85] {path};')
    p.grid(n, m, black, ox=0, labels=False, lines=False)
    p.caption(4, '(a) the blackout, $m=7$', y=-5.4, w=m)
    order = ['r1', 'c2', 'r3', 'c1', 'r4', 'c7', 'r2', 'c6']
    cx, cy = m + 5.4, -3.0
    pos = cycle_layout(order, cx, cy, 1.9, start=112.5)
    rx, ry = pos['r1']
    pos['c3'] = (rx - 2.3, ry + 0.9)
    pos['c4'] = (rx - 1.2, ry + 1.3)
    pos['c5'] = (rx - 0.1, ry + 1.5)
    edges = incidence_edges(black)
    cyc_edges = list(zip(order, order[1:] + order[:1]))
    pend = [('r1', 'c3'), ('r1', 'c4'), ('r1', 'c5')]
    p.graph(pos, edges, hi=cyc_edges, pend=pend)
    p.caption(cx, '(b) $G_S$', y=-5.4)
    save('four', p)


def fig_four_tilted():
    n, m = 4, 7
    black = four_construction(m)
    p = Pic(0.75)
    panels = [
        ([[(1, 2), (2, 1), (3, 2), (2, 3)]], '(a) $D(1,1)$'),
        ([[(1, 3), (2, 4), (3, 1), (4, 2)], [(1, 3), (3, 4), (2, 1), (4, 2)]], '(b) $A_1$ and $B_1$'),
        ([[(4, 3), (5, 4), (6, 1), (7, 2)], [(4, 3), (6, 4), (5, 1), (7, 2)]], '(c) $A_4$ and $B_4$'),
    ]
    gap = m + 1.5
    for k, (rs, cap) in enumerate(panels):
        ox = k * gap
        p.grid(n, m, black, ox=ox, labels=(k == 0))
        for t, r in enumerate(rs):
            col = 'rectA' if t == 0 else 'rectB'
            p.rect(r, col, ox=ox, dashed=(t == 1), width=1.3)
            for q in r:
                if q not in black:
                    p.ring(q, col, ox=ox, radius=0.3 + 0.08 * t)
        p.caption(ox + 4, cap, y=-4.7)
    save('four_tilted', p)


def fig_four_cases():
    p = Pic(0.85)
    cycles = [[1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4]]
    for k, c in enumerate(cycles):
        ox = k * 2.9
        sq = [(ox, -1.0), (ox + 1.6, -1.0), (ox + 1.6, -2.6), (ox, -2.6)]
        pos = {f'r{c[t]}': sq[t] for t in range(4)}
        p.graph(pos, [(f'r{c[t]}', f'r{c[(t + 1) % 4]}') for t in range(4)])
    p.caption(3.7, '(a) the 3 possible graphs $H$', y=-4.7, w=8.0)
    cands = sorted(four_row_upper_candidates(4))
    cand = to_points(cands[0], 4, 4)
    pair = confused_pair(4, 4, cand)
    assert pair is not None and all(set(r) <= set(cand) for r in pair)   # both fully black
    ox = 9.6
    p.grid(4, 4, cand, ox=ox)
    p.rect(pair[0], 'rectA', ox=ox, width=1.4)
    p.rect(pair[1], 'rectB', ox=ox, dashed=True, width=1.4)
    p.caption(ox + 2.5, '(b) a candidate with 8 points', y=-4.7, w=5.0)
    cross = {(i, 1) for i in range(1, 5)} | {(1, j) for j in range(1, 5)}
    assert is_valid(4, 4, cross) and len(cross) == 7
    ox2 = ox + 6.0
    p.grid(4, 4, cross, ox=ox2)
    p.caption(ox2 + 2.5, '(c) valid with 7 points', y=-4.7, w=5.0)
    save('four_cases', p)
    return cand, pair


def fig_bfs():
    p = Pic(0.85)
    xs = {0: [4.0], 1: [1.5, 4.0, 6.5], 2: [1.5, 4.0, 6.5], 3: [1.5, 4.0, 6.5], 4: [6.5]}
    nodes = {}
    for lvl, row in xs.items():
        for t, x in enumerate(row):
            nodes[lvl, t] = (x, -1 - 1.3 * lvl)
    edges = [((0, 0), (1, t)) for t in range(3)] + [((1, t), (2, t)) for t in range(3)] + \
            [((2, t), (3, t)) for t in range(3)] + [((3, 2), (4, 0))]
    for a, b in edges:
        (x1, y1), (x2, y2) = nodes[a], nodes[b]
        p.add(rf'\draw[black!75,line width=0.9pt] ({x1},{y1}) -- ({x2},{y2});')
    for (lvl, t), (x, y) in nodes.items():
        fill = 'black' if lvl % 2 == 0 else 'white'
        p.add(rf'\filldraw[fill={fill},draw=black,line width=0.7pt] ({x},{y}) circle (0.2);')
        p._box(x, y, 0.4)
    p.text(4.55, -0.8, '$x$', 'tiny')
    counts = ['1 vertex', 'at least 3', 'at least 3', 'at least 3', 'at least 1']
    for lvl in range(5):
        y = -1 - 1.3 * lvl
        p.add(rf'\node[tiny,anchor=west] at (8.3,{y}) {{$D_{lvl}$: {counts[lvl]}}};')
        p._box(12.0, y)
    save('bfs', p)


FIVE = ['..###', '..#..', '.##..', '##...', '#...#']


def fig_fivefive():
    n = m = 5
    black = from_picture(FIVE)
    assert is_valid(n, m, black) and len(black) == 10
    kept = {(i, j) for i in range(1, 6) for j in range(1, 6)} - black
    p = Pic()
    p.grid(n, m, black, ox=0, shade=kept, grey={(4, 1), (3, 2)})
    cyc = [(3, 1), (5, 1), (5, 5), (1, 5), (1, 4), (2, 4), (2, 3), (3, 3)]
    path = ' -- '.join(f'({i},{-j})' for i, j in cyc) + ' -- cycle'
    p.add(rf'\draw[cyccol,line width=1.8pt,line join=round,opacity=0.85] {path};')
    p.grid(n, m, black, ox=0, labels=False, lines=False, grey={(4, 1), (3, 2)})
    p.caption(3, '(a) the blackout', y=-6.0)
    order = ['r1', 'c5', 'r5', 'c1', 'r4', 'c2', 'r3', 'c3']
    cx, cy = m + 5.4, -3.1
    pos = cycle_layout(order, cx, cy, 2.0, start=112.5)
    pos['c4'] = (pos['r1'][0] + 0.2, pos['r1'][1] + 1.3)
    pos['r2'] = (pos['c3'][0] - 1.4, pos['c3'][1] + 0.4)
    edges = incidence_edges(black)
    cyc_edges = list(zip(order, order[1:] + order[:1]))
    p.graph(pos, edges, hi=cyc_edges, pend=[('r1', 'c4'), ('r2', 'c3')])
    p.caption(cx, '(b) $G_S$', y=-6.0)
    save('fivefive', p)


def square_images(black, n):
    maps = [lambda i, j: (i, j), lambda i, j: (n + 1 - j, i), lambda i, j: (n + 1 - i, n + 1 - j),
            lambda i, j: (j, n + 1 - i), lambda i, j: (n + 1 - i, j), lambda i, j: (i, n + 1 - j),
            lambda i, j: (j, i), lambda i, j: (n + 1 - j, n + 1 - i)]
    return [{f(i, j) for i, j in black} for f in maps]


def fig_orbit():
    black = from_picture(FIVE)
    imgs = square_images(black, 5)
    assert len({frozenset(S) for S in imgs}) == 8 and all(is_valid(5, 5, S) for S in imgs)
    names = ['as in Figure~\\ref{fig:fivefive}', 'turned $90^\\circ$', 'turned $180^\\circ$', 'turned $270^\\circ$',
             'flipped left to right', 'flipped top to bottom', 'flipped in $i=j$', 'flipped in $i+j=6$']
    p = Pic(0.6)
    gap = 7.6
    for k, S in enumerate(imgs):
        ox = (k % 4) * gap
        oy = -(k // 4) * 8.4
        p.add(rf'\begin{{scope}}[yshift={oy * UNIT * p.scale:.3f}cm]')
        p.grid(5, 5, S, ox=ox, labels=False, lines=False)
        p.caption(ox + 3, names[k], y=-5.6, w=gap - 0.4)
        p.add(r'\end{scope}')
        p._box(ox + 3, oy - 6.8)
    save('orbit', p)


def fig_tencycle():
    n = m = 5
    from itertools import permutations
    found = None
    ident = (1, 2, 3, 4, 5)
    for perm in permutations(range(1, 6)):
        if any(perm[t] == ident[t] for t in range(5)):
            continue
        S = {(ident[t], t + 1) for t in range(5)} | {(perm[t], t + 1) for t in range(5)}
        if axis_ok(n, m, S) and not is_valid(n, m, S):
            pair = confused_pair(n, m, S)
            if any(len({i for i, _ in r}) > 2 for r in pair):
                found = (S, pair)
                break
    S, pair = found
    p = Pic()
    p.grid(n, m, S, ox=0)
    p.rect(pair[0], 'rectA', width=1.4)
    p.rect(pair[1], 'rectB', dashed=True, width=1.4)
    for q in pair[0]:
        if q not in S:
            p.ring(q, 'black!70', radius=0.33)
    save('tencycle', p)
    return S, pair


STAIRS = {
    (5, 6): ['##....', '.##...', '..###.', '....##', '#....#'],
    (6, 6): ['###...', '..###.', '....##', '#....#', '.....#', '.....#'],
    (6, 7): ['####...', '...###.', '.....##', '......#', '......#', '#.....#'],
}


def fig_stairs():
    p = Pic(0.72)
    ox = 0
    for (n, m), pic in STAIRS.items():
        black = from_picture(pic)
        assert len(black) == n + m and is_valid(n, m, black)
        p.grid(n, m, black, ox=ox, labels=False)
        p.caption(ox + (m + 1) / 2, f'${n}\\times{m}$, {n + m} points', y=-6.7)
        ox += m + 2.2
    save('stairs', p)


def fig_excess():
    """The value of each computed grid; shaded cells beat n+m-1."""
    values = {(2, m): m + 1 for m in range(3, 8)}
    values[(2, 2)] = 4
    values.update({(3, m): m + 2 for m in range(3, 11)})
    values.update({(4, 4): 7, (4, 5): 8, (4, 6): 10, (4, 7): 11, (4, 8): 12,
                   (5, 5): 10, (5, 6): 11, (5, 7): 12, (6, 6): 12})
    proved = {k for k in values if k[0] <= 4 or k == (5, 5)}
    p = Pic(0.85)
    s = 1.5
    for (n, m), v in values.items():
        x, y = (m - 2) * s, -(n - 2) * s
        col = 'white' if v - (n + m - 1) <= 0 else 'excesscol'
        p.add(rf'\filldraw[fill={col},draw=black!40] ({x - s / 2},{y - s / 2}) rectangle ({x + s / 2},{y + s / 2});')
        p.add(rf'\node[font=\footnotesize] at ({x},{y + 0.1}) {{{v}}};')
        if (n, m) in proved:
            p.add(rf'\node[font=\tiny,black!60] at ({x + 0.45},{y - 0.45}) {{p}};')
        p._box(x, y, s / 2)
    for m in range(2, 11):
        p.text((m - 2) * s, s * 1.0, f'${m}$', 'tiny')
    for n in range(2, 7):
        p.text(-s * 0.95, -(n - 2) * s, f'${n}$', 'tiny')
    p.text(-s * 0.95, s * 1.0, r'$n\backslash m$', 'tiny')
    save('excess', p)


def main():
    os.makedirs(FIGS, exist_ok=True)
    fig_game()
    fig_rects()
    fig_strip_rects()
    fig_two_blackouts()
    fig_difference()
    fig_strip()
    fig_incidence()
    fig_c4()
    fig_c6()
    fig_threecorners()
    fig_rowbound()
    fig_mantel()
    print('tilted rectangles on 4 x 4:', fig_tilted())
    fig_three()
    fig_four()
    fig_four_tilted()
    cand, pair = fig_four_cases()
    print('4x4 candidate:', cand, 'confused:', pair)
    fig_bfs()
    fig_fivefive()
    fig_orbit()
    S, pair = fig_tencycle()
    print('10-cycle:', sorted(S), 'confused:', pair)
    fig_stairs()
    fig_excess()


if __name__ == '__main__':
    main()
