"""A dark figure style in the spirit of 3Blue1Brown's animations.

Black background, white text, and the colors of the manim palette (Grant
Sanderson's animation library). The figure scripts draw as usual, in black on
white, and call `finish(fig)` before saving. That call flips every gray, black
or white artist to its mirror image on the gray scale and leaves colored
artists alone. Set `DARK = False` to get the figures on a white background.
"""
import matplotlib.colors as mcolors
from matplotlib.colors import LinearSegmentedColormap

DARK = True

BLUE = "#58C4DD"
BLUE_E = "#1C758A"
TEAL = "#5CD0B3"
GREEN = "#83C167"
YELLOW = "#FFFF00"
GOLD = "#F0AC5F"
RED = "#FC6255"
MAROON = "#C55F73"
PURPLE = "#9A72AC"

# For a family of curves, from the first curve (YELLOW) to the last (PURPLE).
LINES = LinearSegmentedColormap.from_list("manim_lines", [PURPLE, BLUE, TEAL, GREEN, YELLOW])
# For heat maps, from nothing (black) to the most (yellow).
HEAT = LinearSegmentedColormap.from_list("manim_heat", ["#000000", BLUE_E, BLUE, YELLOW])
# A few curves that must be told apart.
DISTINCT = [YELLOW, BLUE, RED, GREEN, PURPLE, GOLD, TEAL, MAROON]


def shades(n, lo=0.0, hi=1.0):
    """n colors for a family of curves."""
    if n == 1:
        return [LINES(hi)]
    return [LINES(hi + (lo - hi) * i / (n - 1)) for i in range(n)]


def _flip(c):
    """Mirror an achromatic color on the gray scale. Other colors are kept."""
    try:
        r, g, b, a = mcolors.to_rgba(c)
    except (ValueError, TypeError):
        return None
    if max(r, g, b) - min(r, g, b) > 0.02:
        return None
    return (1 - r, 1 - g, 1 - b, a)


def _flip_array(colors):
    out, changed = [], False
    for c in colors:
        f = _flip(c)
        out.append(f if f is not None else tuple(c))
        changed = changed or f is not None
    return out if changed else None


def finish(fig):
    """Turn a figure drawn in black on white into white on black."""
    if not DARK:
        return fig
    from matplotlib.axes import Axes
    from matplotlib.figure import Figure
    from matplotlib.lines import Line2D
    for art in fig.findobj():
        if isinstance(art, (Figure, Axes)):
            continue                          # their background patch is visited on its own
        mapped = getattr(art, "get_array", lambda: None)() is not None
        pairs = [("get_color", "set_color"),
                 ("get_markerfacecolor", "set_markerfacecolor"),
                 ("get_markeredgecolor", "set_markeredgecolor"),
                 ("get_facecolor", "set_facecolor"),
                 ("get_edgecolor", "set_edgecolor")]
        for getter, setter in pairs:
            if not (hasattr(art, getter) and hasattr(art, setter)):
                continue
            if mapped and getter in ("get_facecolor", "get_edgecolor"):
                continue                      # colors that come from a color map
            if isinstance(art, Line2D):
                # a marker color left on "auto" follows the line color
                if getter == "get_markerfacecolor" and isinstance(art._markerfacecolor, str)                         and art._markerfacecolor == "auto":
                    continue
                if getter == "get_markeredgecolor" and isinstance(art._markeredgecolor, str)                         and art._markeredgecolor == "auto":
                    continue
            if getter == "get_edgecolor" and isinstance(getattr(art, "_edgecolors", None), str):
                continue                      # "face" follows the face color
            if getter == "get_edgecolor" and isinstance(getattr(art, "_original_edgecolor", None), str)                     and art._original_edgecolor in ("face", "none"):
                continue
            try:
                c = getattr(art, getter)()
            except Exception:
                continue
            if isinstance(c, str) and c in ("none", "None", "face", "auto"):
                continue
            try:
                if hasattr(c, "ndim") and c.ndim == 2:
                    new = _flip_array(c)
                else:
                    new = _flip(c)
                if new is not None:
                    getattr(art, setter)(new)
            except Exception:
                pass
    return fig
