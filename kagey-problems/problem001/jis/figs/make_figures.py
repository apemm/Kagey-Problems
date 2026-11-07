"""Draw the grid figures of the paper as TikZ files, in the style of Kagey's figure for Problem 001.

The style follows the figure on peterkagey.com/problems/001: grid lines are thin and dashed,
every grid point is a large circle with a black outline, a visible (white) point is filled
white, a blacked-out point is filled gray and crossed out, a point we are shown is filled
yellow, and rectangles are thick blue or red outlines drawn under the points.

Every blackout drawn here is first checked against the definition with the rectangle list of
verify_narrow.py. Coordinates are one-based (column, row) with (1,1) the top-left point.

Run from this folder: python make_figures.py [output folder]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, '..', '..')))
from verify_narrow import collision, rectangles  # noqa: E402

# Kagey's figure: points 2 cm apart, circles of radius 0.6 cm, circle outlines 1.2 pt,
# rectangles 5.67 pt, grid lines 0.8 pt dashed 3 pt on 3 pt. We scale all of it with the spacing.
KAGEY_SPACING_CM = 2.0


def widths(spacing_cm):
    k = spacing_cm / KAGEY_SPACING_CM
    return {
        'radius': 0.3,                      # in units of the spacing
        'outline': 1.2 * k,                 # pt
        'rect': 5.67 * k,                   # pt
        'grid': 0.8 * k,                    # pt
        'dash': 3.0 * k,                    # pt
        'cross': 0.212,                     # half-length of a cross arm, in units of the spacing
    }


def mask(points, m):
    return sum(1 << ((j - 1) * m + (i - 1)) for i, j in set(points))


def check_valid(h, m, black, expect=True):
    ok = collision(rectangles(h, m), mask(black, m)) is None
    assert ok == expect, (h, m, sorted(black))


def is_rectangle(corners):
    pts = list(corners)
    assert len(set(pts)) == 4
    cx = sum(p[0] for p in pts) / 4
    cy = sum(p[1] for p in pts) / 4
    d = sorted((p[0] - cx) ** 2 + (p[1] - cy) ** 2 for p in pts)
    assert abs(d[0] - d[3]) < 1e-9, corners
    # A quadrilateral whose diagonals bisect each other and have equal length is a rectangle.
    for a in pts:
        b = (2 * cx - a[0], 2 * cy - a[1])
        assert b in pts, corners
    return True


def picture(h, m, black, spacing, shown=(), rects=(), drawn=None, labels=True, shift=0.0,
            caption=None):
    """TikZ commands for one panel. black: blacked-out points. shown: points filled yellow.
    rects: list of (color, corners in order around the rectangle). drawn: if given, only these
    points get circles (the rest of the grid shows only its dashed lines)."""
    w = widths(spacing)
    out = []
    out.append(f'  \\begin{{scope}}[xshift={shift:.3f}cm]')
    style = f'black,line width={w["grid"]:.2f}pt,dash pattern=on {w["dash"]:.2f}pt off {w["dash"]:.2f}pt'
    lines = [f'(1,-{j}) -- ({m},-{j})' for j in range(1, h + 1)]
    lines += [f'({i},-1) -- ({i},-{h})' for i in range(1, m + 1)]
    out.append(f'    \\draw[{style}] ' + ' '.join(lines) + ';')
    for color, corners in rects:
        path = ' -- '.join(f'({x},-{y})' for x, y in corners)
        out.append(f'    \\draw[{color},line width={w["rect"]:.2f}pt,line join=round] {path} -- cycle;')
    pts = [(i, j) for j in range(1, h + 1) for i in range(1, m + 1)]
    if drawn is not None:
        pts = [p for p in pts if p in set(drawn)]
    r = w['radius']
    c = w['cross']
    for (i, j) in pts:
        if (i, j) in set(black):
            out.append(f'    \\filldraw[fill=kgray,draw=black,line width={w["outline"]:.2f}pt] '
                       f'({i},-{j}) circle ({r});')
            out.append(f'    \\draw[black,line width={w["outline"]:.2f}pt] ({i - c:.3f},-{j - c:.3f}) -- '
                       f'({i + c:.3f},-{j + c:.3f}) ({i - c:.3f},-{j + c:.3f}) -- ({i + c:.3f},-{j - c:.3f});')
        else:
            fill = 'kyellow' if (i, j) in set(shown) else 'white'
            out.append(f'    \\filldraw[fill={fill},draw=black,line width={w["outline"]:.2f}pt] '
                       f'({i},-{j}) circle ({r});')
    if labels:
        for i in range(1, m + 1):
            out.append(f'    \\node[lab] at ({i},-0.45) {{{i}}};')
        for j in range(1, h + 1):
            out.append(f'    \\node[lab] at (0.45,-{j}) {{{j}}};')
    if caption:
        out.append(f'    \\node[capt,anchor=north] at ({(m + 1) / 2:.2f},-{h + 0.45:.2f}) {{{caption}}};')
    out.append('  \\end{scope}')
    return out


def tikz(spacing, body):
    return ([f'\\begin{{tikzpicture}}[x={spacing}cm,y={spacing}cm,baseline=(current bounding box.north)]']
            + body + ['\\end{tikzpicture}'])


OUT = sys.argv[1] if len(sys.argv) > 1 else HERE


def write(name, lines):
    with open(os.path.join(OUT, name), 'w', encoding='ascii', newline='\n') as fh:
        fh.write('\n'.join(lines) + '\n')


def game():
    """Figure 1: one round on the 3 x 4 grid."""
    h, m = 3, 4
    black = {(i, 1) for i in range(1, m + 1)} | {(1, 2), (1, 3)}
    check_valid(h, m, black)
    square = [(2, 2), (3, 1), (4, 2), (3, 3)]
    is_rectangle(square)
    visible = [p for p in square if p not in black]
    assert sorted(visible) == [(2, 2), (3, 3), (4, 2)]
    s = 0.9
    gap = (m + 1.2)
    body = []
    body += picture(h, m, set(), s, shown={(3, 2)}, caption='(a) the point $(3,2)$', shift=0)
    body += picture(h, m, black, s, caption='(b) our blackout', shift=gap * s)
    body += picture(h, m, black, s, rects=[('kred', square)], caption='(c) the rectangle',
                    shift=2 * gap * s)
    body += picture(h, m, set(), s, shown=set(visible), drawn=visible,
                    caption='(d) what we are shown', shift=3 * gap * s)
    write('game.tex', tikz(s, body))


def boards():
    """Figure 2: the 5 x 13 test board of S_8 and the blackout S_16 of the 6 x 16 grid."""
    s8 = {(1, 1), (1, 4), (2, 4), (2, 5), (3, 2), (3, 5), (4, 5), (5, 5), (6, 3), (6, 4),
          (7, 2), (7, 3), (8, 1), (8, 2)}
    board13 = s8 | {(8 + i, 1) for i in range(1, 6)}
    check_valid(5, 8, s8)
    check_valid(5, 13, board13)
    s16 = {(1, 3), (1, 6), (2, 1), (2, 4), (3, 2), (3, 5), (4, 6), (5, 6), (6, 1), (6, 6), (7, 6),
           (8, 6), (9, 5), (9, 6), (10, 4), (10, 5), (11, 4), (12, 4), (13, 4), (14, 3), (14, 4),
           (15, 2), (15, 3), (16, 1), (16, 2)}
    assert len(s16) == 16 + 9
    check_valid(6, 16, s16)
    s = 0.68
    write('board13.tex', tikz(s, picture(5, 13, board13, s, caption='(a)')))
    write('board16.tex', tikz(s, picture(6, 16, s16, s, caption='(b)')))


def tilted():
    """Figure: the diamond D(1,1) and the templates A_1, B_1, C_1, E_1 of the 4 x m grid, each
    in a 4 x 4 window, with the leftmost corner shown yellow."""
    shapes = [('$D(1,1)$', [(1, 2), (2, 1), (3, 2), (2, 3)]),
              ('$\\kA_1$', [(1, 3), (2, 4), (4, 2), (3, 1)]),
              ('$\\kB_1$', [(1, 3), (3, 4), (4, 2), (2, 1)]),
              ('$\\kC_1$', [(1, 2), (2, 4), (4, 3), (3, 1)]),
              ('$\\kE_1$', [(1, 2), (3, 4), (4, 3), (2, 1)])]
    rows = {'$\\kA_1$': '3412', '$\\kB_1$': '3142', '$\\kC_1$': '2413', '$\\kE_1$': '2143'}
    rects4 = {frozenset(r) for r in [frozenset((i % 4 + 1, i // 4 + 1) for i in range(16) if r >> i & 1)
                                     for r in rectangles(4, 4)]}
    for name, sh in shapes:
        is_rectangle(sh)
        assert frozenset(sh) in rects4, name
        if name in rows:      # corner rows read left to right, as in the definition
            assert ''.join(str(y) for _, y in sorted(sh)) == rows[name], name
    s = 0.5
    gap = 4 + 1.4
    body = []
    for k, (name, sh) in enumerate(shapes):
        body += picture(4, 4, set(), s, shown={min(sh)}, rects=[('kred', sh)], labels=(k == 0),
                        caption=name, shift=k * gap * s)
    write('tilted.tex', tikz(s, body))


def four():
    """Figure: the four-row construction for m = 7, its eight-cycle, and the weak rectangle A_1."""
    h, m = 4, 7
    black = {(i, 1) for i in range(2, m)} | {(m - 1, 2), (m, 2), (1, 3), (2, 3), (1, 4), (m, 4)}
    assert len(black) == m + 4
    check_valid(h, m, black)
    cyc = [(2, 1), (6, 1), (6, 2), (7, 2), (7, 4), (1, 4), (1, 3), (2, 3)]
    assert all(p in black for p in cyc)
    a1 = [(1, 3), (2, 4), (4, 2), (3, 1)]
    is_rectangle(a1)
    shown = {p for p in a1 if p not in black}
    assert shown == {(2, 4), (4, 2)}
    s = 0.62
    gap = m + 1.2
    body = picture(h, m, black, s, rects=[('kblue', cyc)], caption='(a) the cycle of $G_S$')
    body += picture(h, m, black, s, shown=shown, rects=[('kred', a1)],
                    caption='(b) $\\kA_1$ shows two points', shift=gap * s)
    write('four.tex', tikz(s, body))


def diamond():
    """Figure: the diamond test on three rows. (a) The valid word aAbCc. (b) In bAbCc the diamond
    D(1,1) and the axis-aligned rectangle on columns 2, 4 and rows 2, 3 both show only (2,3)."""
    letters = {'a': [1], 'b': [2], 'c': [3], 'A': [1, 2], 'C': [2, 3]}

    def word(w):
        return {(i + 1, r) for i, ch in enumerate(w) for r in letters[ch]}

    ok, bad = word('aAbCc'), word('bAbCc')
    check_valid(3, 5, ok)
    check_valid(3, 5, bad, expect=False)
    d = [(1, 2), (2, 1), (3, 2), (2, 3)]
    rival = [(2, 2), (4, 2), (4, 3), (2, 3)]
    is_rectangle(d)
    is_rectangle(rival)
    assert {p for p in d if p not in bad} == {(2, 3)} == {p for p in rival if p not in bad}
    s = 0.62
    gap = 5 + 1.6
    body = picture(3, 5, ok, s, rects=[('kred', d)], shown={p for p in d if p not in ok},
                   caption='(a) $aAbCc$ is valid')
    body += picture(3, 5, bad, s, rects=[('kblue', rival), ('kred', d)], shown={(2, 3)},
                    caption='(b) $bAbCc$ fails', shift=gap * s)
    write('diamond.tex', tikz(s, body))


if __name__ == '__main__':
    game()
    boards()
    tilted()
    four()
    diamond()
    print('figures written and checked')
