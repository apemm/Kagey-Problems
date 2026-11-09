"""Test escape moves on one explicit modular family, without graph enumeration."""
from pathlib import Path
import sys
import json
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "counting_followup"))
from dominance_compatibility import compatibility, allowed, placements


def obstruction(h, word, origin):
    seen = {}
    def shifted(rect):
        return [(x - origin, r) for x, r in rect]
    for rect in sorted(placements(h, len(word)), key=lambda r: max(x for x, _ in r)):
        white = tuple(sorted((x, r) for x, r in rect if word[x] != r))
        if len(white) > 2:
            continue
        cause = None
        if not white:
            cause = "hidden"
        elif white in seen:
            return {"type": "tilted collision", "rectangles": [
                shifted(seen[white]), shifted(rect)], "white": shifted(white)}
        elif len(white) == 1:
            x, r = white[0]
            if (r - word[x]) % 2:
                cause = "singleton axis rival"
        else:
            (x, r), (z, s) = white
            if x == z and (r - s) % 2:
                cause = "vertical axis rival"
            elif r == s and word[x] == word[z]:
                cause = "horizontal axis rival"
            elif x != z and r != s and word[x] == s and word[z] == r:
                cause = "oblique axis rival"
        if cause:
            return {"type": cause, "rectangles": [shifted(rect)],
                    "white": shifted(white)}
        seen[white] = rect
    return None


def main():
    out = []
    # The arithmetic proof covers every prime with (2/p)=-1. This finite
    # calculation only supplies an explicit counterexample to a proposed
    # direct-padding lemma, not a height-by-height graph survey.
    for h in (11,):
        started = time.monotonic()
        L = 2 * (1 + (h - 1)**2 // 4)
        parity = set(range(1, h + 1, 2))
        base = tuple(1 + x % h for x in range(h + L))
        assert allowed(compatibility(h, base), parity)
        phases = []
        for phase in range(h):
            history = tuple(1 + (x + phase) % h for x in range(-L, 0))
            choices = [r for r in range(1, h + 1)
                       if allowed(compatibility(h, history + (r,)), parity)]
            constant_exits = [r for r in range(1, h + 1)
                              if allowed(compatibility(h, history + (r,) * L), parity)]
            phases.append({"phase": phase, "one_step_choices": choices,
                           "constant_exits": constant_exits})
        result = {"prime": h, "memory": L, "phases": phases,
                  "elapsed_seconds": time.monotonic() - started}
        phase = 7
        history = tuple(1 + (x + phase) % h for x in range(-L, 0))
        result["phase_seven_constant_exit_obstructions"] = {
            r: obstruction(h, history + (r,) * L, L)
            for r in range(1, h + 1)
        }
        assert all(result["phase_seven_constant_exit_obstructions"].values())
        out.append(result)
        print(json.dumps(result), flush=True)
    (HERE / "periodic_lattice_probe.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
