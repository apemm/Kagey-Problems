"""Reading the hypnograms of the Sleep-EDF telemetry study.

The files are the 44 files ST*-Hypnogram.edf of the Sleep-EDF Database Expanded
(PhysioNet, version 1.0.0, Open Data Commons Attribution License v1.0), in the
folder data_sleep_edf next to this script, with their SHA256 sums. They hold
only the scored sleep stages, as runs (start, length, stage) in seconds.

We read them as sequences of 30 second epochs on three states,
    0 = awake (W, and movement time), 1 = non-REM (stages 1 to 4), 2 = REM,
and cut each night into windows of a fixed number of epochs.
"""
import re
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
DATA = HERE / "data_sleep_edf"
EPOCH = 30
STATE = {"Sleep stage W": 0, "Movement time": 0,
         "Sleep stage 1": 1, "Sleep stage 2": 1, "Sleep stage 3": 1, "Sleep stage 4": 1,
         "Sleep stage R": 2}
NAMES = ("awake", "non-REM", "REM")
TAL = re.compile(rb"\+(\d+(?:\.\d+)?)\x15(\d+(?:\.\d+)?)\x14([^\x14\x00]*)\x14")


def read_night(path):
    """The epochs of one night as an integer array, with -1 where the stage is not scored."""
    raw = path.read_bytes()
    header_bytes = int(raw[184:192])
    out = []
    for onset, length, label in TAL.findall(raw[header_bytes:]):
        onset, length, label = float(onset), float(length), label.decode("ascii", "replace")
        assert onset % EPOCH == 0 and length % EPOCH == 0 and onset >= len(out) * EPOCH, path.name
        out.extend([-1] * (int(onset // EPOCH) - len(out)))      # a gap in the scoring
        out.extend([STATE.get(label, -1)] * int(length // EPOCH))
    return np.array(out, dtype=int)


def nights():
    files = sorted(DATA.glob("ST*-Hypnogram.edf"))
    return [(f.name[:7], read_night(f)) for f in files]


def windows(n_epochs, trim_wake=True):
    """Windows of n_epochs epochs, with the night they come from.
    With trim_wake the long waking stretches before the first sleep and after
    the last sleep are cut off first."""
    out = []
    for name, x in nights():
        if trim_wake:
            asleep = np.flatnonzero(x > 0)
            x = x[asleep[0]:asleep[-1] + 1]
        for k in range(len(x) // n_epochs):
            w = x[k * n_epochs:(k + 1) * n_epochs]
            if (w >= 0).all():
                out.append((name, w))
    return out


if __name__ == "__main__":
    ns = nights()
    lens = [len(x) for _, x in ns]
    print("nights:", len(ns), " epochs per night: min %d, median %d, max %d" % (min(lens), np.median(lens), max(lens)))
    allx = np.concatenate([x for _, x in ns])
    print("unscored epochs:", int((allx < 0).sum()))
    print("share of time:", {NAMES[k]: round(float((allx == k).mean()), 3) for k in range(3)})
    for n in (40, 60):
        ws = windows(n)
        print("windows of %d epochs after trimming: %d" % (n, len(ws)))
