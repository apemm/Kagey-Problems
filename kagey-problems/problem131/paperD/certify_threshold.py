"""Certificate for the unimodal to bimodal threshold of the fair-start limit law.

Theorem thm:threshold (Section 4.2) with the lemmas of Appendix app:threshold.
Put z- = 1838418790980431/2748779069440000 and z+ = 45960469774511/68719476736000.
The certificate proves
  * f_a''(0) < 0 for every a in (1/2, z-]   (modes 'scaled' and 'zero'),
  * f_a''(0) > 0 for every a in [z+, 839/1250]   (mode 'zero'),
  * the Hankel test of Lemma lem:thr-hankel fails for every a in [1341/2000, 1)
    (mode 'hankel'),
and that every zero of f''(0) in (1/2, 839/1250] lies in (z-, z+).

The sign of f_a''(0) on an interval I = [a0 - w, a0 + w] comes from the uniform
enclosure f_a''(0) in G(a - a0) +- eta of threshold_taylor.TaylorModel, which
the script splits into pieces where it has one sign. An interval is accepted
when every piece has a sign, and otherwise it is halved. In mode 'zero' one
undecided piece is allowed in the whole cover. Mode 'scaled' works with
X = L/sigma (Lemma lem:thr-scaled), which reaches a = 1/2.

Usage (from any folder; every run uses exact rationals for LO and HI):
  python -I -B certify_threshold.py scaled LO HI         certifies f'' < 0 on [LO, HI]
  python -I -B certify_threshold.py zero LO HI [RHO]     one sign change in [LO, HI]
  python -I -B certify_threshold.py cover LO HI SIGN [RHO]
  python -I -B certify_threshold.py hankel LO            Hankel test on [LO, 1]
  python -I -B certify_threshold.py full                 the whole certificate (9 runs in
                                                         parallel), then 'check'
  python -I -B certify_threshold.py check                checks the stored records in data/
  python -I -B certify_threshold.py quick                a few minutes: 'check' and 3 short
                                                         runs compared with the records
Add --out FILE to write the output also to FILE, after a header line with the sha256
of this script and its 3 helper modules and the software versions. The last line of
such a file is the exit status. 'full' writes data/threshold_*.txt in this way. The
run of October 25, 2026 was
  python -I -B certify_threshold.py full --out data/certify_threshold_output.txt
Exit status 1 on any failure. Needs python-flint and mpmath.
"""
import datetime
import hashlib
import math
import platform
import re
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE))
sys.dont_write_bytecode = True
from threshold_pointwise import ERW  # noqa: E402
from threshold_taylor import TaylorModel, sign_cover  # noqa: E402

SOURCES = ('certify_threshold.py', 'threshold_taylor.py', 'threshold_pointwise.py',
           'threshold_hankel.py')
Z_LO = Fraction(1838418790980431, 2748779069440000)
Z_HI = Fraction(45960469774511, 68719476736000)
SCALED_RANGES = [('0.50', '0.53'), ('0.53', '0.56'), ('0.56', '0.60'), ('0.60', '0.63'),
                 ('0.63', '0.65'), ('0.65', '0.66'), ('0.66', '0.668')]
RUNS = ([('scaled_%s_%s' % r, ['scaled', r[0], r[1]]) for r in SCALED_RANGES]
        + [('zero_0.668_0.6712', ['zero', '0.668', '0.6712', '1/100']),
           ('hankel_0.6705_1', ['hankel', '0.6705'])])

T2_LADDER = [Fraction(1, 2), Fraction(1), Fraction(2), Fraction(3), Fraction(4),
             Fraction(6), Fraction(8), Fraction(10), Fraction(12), Fraction(16),
             Fraction(20), Fraction(24)]
B_CACHE = {}


def header():
    import flint
    import mpmath
    parts = ['%s sha256=%s' % (n, hashlib.sha256((BASE / n).read_bytes()).hexdigest())
             for n in SOURCES]
    return ('# ' + ' '.join(parts) + ' python=%s python-flint=%s mpmath=%s date=%s'
            % (platform.python_version(), flint.__version__, mpmath.__version__,
               datetime.date.today().isoformat()))


def b_estimate(a):
    key = round(float(a), 3)
    if key not in B_CACHE:
        B_CACHE[key] = float(ERW("%.3f" % key, N=120, prec=300).B.mid())
    return B_CACHE[key]


def params(a0, w, q, T2):
    a = float(a0) - float(w / q)
    B = 1.45 * b_estimate(a0)            # room for the square enclosure
    T3 = 2 ** (float(a0 + w)) * float(T2)
    peak = (B * T3) ** (1 / a)
    N = 300
    while N * math.log(B * T3) + 14 * math.log(N) - math.lgamma(1 + a * N) > -200:
        N += 100
    prec = int(1.45 * peak + 1100)
    return N, prec


SCALED = [False]
RHO_CAP = [Fraction(1, 25)]


def try_interval(a0, w, q, T2):
    if SCALED[0]:
        a = float(a0) - float(w / q)
        T3 = 2 ** float(a0 + w) * float(T2)
        B = 2.8
        peak = (B * T3) ** (1 / a)
        N = 600
        while N * math.log(B * T3) + 14 * math.log(N) - math.lgamma(1 + a * N) > -200:
            N += 100
        prec = int(1.45 * peak + 1100)
    else:
        N, prec = params(a0, w, q, T2)
    tm = TaylorModel(a0, w, q=q, N=N, prec=prec, scaled=SCALED[0])
    d = tm.certify(T2, Fraction(1, 32))
    if not d["boot"]:
        return None, d, N, prec
    cover = sign_cover(d["G"], d["eta"], a0, w)
    return cover, d, N, prec


def max_w(a0):
    """Largest half-width allowed at a0: the disc must stay in Re z > 1/2."""
    if SCALED[0]:
        return Fraction(1, 8), Fraction(1, 400)
    room = a0 - Fraction(1, 2)
    q = Fraction(1, 8) if room < Fraction(1, 50) else Fraction(1, 32)
    rho = min(RHO_CAP[0], room * Fraction(9, 10))
    return q, rho * q


def run(lo, hi, mode, want, log, allow_zero, start_t2=None):
    a0 = (lo + hi) / 2
    w = (hi - lo) / 2
    q, wmax = max_w(lo)
    if w > wmax:
        mid = (lo + hi) / 2
        return (run(lo, mid, mode, want, log, allow_zero, start_t2)
                and run(mid, hi, mode, want, log, allow_zero, start_t2))
    if start_t2 is None and SCALED[0]:
        fa = float(a0)
        start_t2 = 3 if fa < 0.56 else 4 if fa < 0.6 else 5 if fa < 0.63 else 6 if fa < 0.655 else 7
    if start_t2 is None:
        fa = float(a0)
        start_t2 = 0 if fa < 0.53 else 1 if fa < 0.58 else 2 if fa < 0.64 else 3 if fa < 0.665 else 4
    for i in range(start_t2, len(T2_LADDER)):
        T2 = T2_LADDER[i]
        try:
            cover, d, N, prec = try_interval(a0, w, q, T2)
        except (ValueError, AssertionError) as exc:
            print("  skip a0=%.10f T2=%s: %s" % (a0, T2, exc), flush=True)
            continue
        if cover is None:
            continue
        signs = [s for (_, _, s) in cover]
        line = ("[%.14f, %.14f] T2=%s N=%d prec=%d K=%d q=%s eta=%s G0=%s"
                % (lo, hi, T2, N, prec, d["K"], q, d["eta"].str(3), d["G"][0].str(6)))
        if mode == "cover" and all(s == want for s in signs):
            log.append((lo, hi, want, line))
            print("ok  " + line, flush=True)
            return True
        if mode == "zero" and 0 not in signs and len(set(signs)) == 1:
            log.append((lo, hi, signs[0], line))
            print("ok  " + line, flush=True)
            return True
        if mode == "zero" and allow_zero[0] and signs.count(0) == 1:
            # a single undecided piece, with - to its left and + to its right
            k = signs.index(0)
            if all(s == -1 for s in signs[:k]) and all(s == 1 for s in signs[k + 1:]):
                zlo, zhi = cover[k][0], cover[k][1]
                if zhi - zlo < Fraction(1, 10 ** 12):
                    allow_zero[0] = False
                    log.append((lo, hi, 0, line + "  zero piece [%s, %s]" % (zlo, zhi)))
                    print("ok* " + line + "  undecided piece [%.16f, %.16f]"
                          % (zlo, zhi), flush=True)
                    return True
        # an undecided part: more tail accuracy may settle it, else split
        if 0 not in signs:
            break
    if w < Fraction(1, 10 ** 9):
        print("FAIL [%.14f, %.14f]" % (lo, hi), flush=True)
        return False
    mid = (lo + hi) / 2
    return (run(lo, mid, mode, want, log, allow_zero)
            and run(mid, hi, mode, want, log, allow_zero))


def interval_main(argv):
    """Modes scaled, zero and cover. Returns the exit status."""
    mode = argv[0]
    if mode == "scaled":
        SCALED[0] = True
        mode = "cover"
        argv = argv[:3] + ["-1"] + argv[3:]
    lo, hi = Fraction(argv[1]), Fraction(argv[2])
    want = int(argv[3]) if mode == "cover" else 0
    extra = argv[4:] if mode == "cover" else argv[3:]
    if extra:
        RHO_CAP[0] = Fraction(extra[0])
    t0 = time.time()
    log = []
    allow_zero = [mode == "zero"]
    ok = run(lo, hi, mode, want, log, allow_zero)
    log.sort()
    covered = all(log[i][1] == log[i + 1][0] for i in range(len(log) - 1))
    covered = bool(covered and log and log[0][0] == lo and log[-1][1] == hi)
    print("intervals: %d  contiguous cover of [%s, %s]: %s" % (len(log), lo, hi, covered))
    if mode == "zero":
        zl = [x for x in log if x[2] == 0]
        print("zero piece:", zl[0][3].split("zero piece")[-1] if zl else "none")
    print("elapsed %.1f s" % (time.time() - t0))
    return 0 if (ok and covered) else 1


def hankel_main(argv):
    import threshold_hankel
    return 0 if threshold_hankel.run(Fraction(argv[1])) else 1


class Tee:
    def __init__(self, stream, fh):
        self.stream, self.fh = stream, fh

    def write(self, s):
        self.stream.write(s)
        self.fh.write(s)

    def flush(self):
        self.stream.flush()
        self.fh.flush()


def single(argv, out):
    """One run, optionally recorded in the file out."""
    main = {'hankel': hankel_main, 'full': lambda a: full(), 'check': lambda a: check(),
            'quick': lambda a: quick()}.get(argv[0], interval_main)
    if out is None:
        return main(argv)
    with open(out, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(header() + '\n')
        fh.write('# command: certify_threshold.py %s\n' % ' '.join(argv))
        old = sys.stdout
        sys.stdout = Tee(old, fh)
        try:
            status = main(argv)
        finally:
            sys.stdout = old
        fh.write('exit %d\n' % status)
    return status


def read_record(name):
    path = BASE / 'data' / ('threshold_%s.txt' % name)
    if not path.exists():
        return None, 'missing %s' % path.name
    lines = path.read_text(encoding='utf-8').splitlines()
    return lines, path.name


def check():
    """Check the stored records: hashes, exit status and the cover of (1/2, 1)."""
    want = header().split(' python=')[0]
    fails = []
    recs = {}
    for name, argv in RUNS:
        lines, label = read_record(name)
        if lines is None:
            fails.append(label)
            continue
        recs[name] = lines
        if lines[0].split(' python=')[0] != want:
            fails.append('%s: sha256 of the scripts differs from the header' % label)
        if lines[-1] != 'exit 0':
            fails.append('%s: last line is %r' % (label, lines[-1]))
    if fails:
        for f in fails:
            print('FAIL ' + f)
        return 1
    # the scaled runs and the zero run must chain from 1/2 to 839/1250
    chain = []
    for name, argv in RUNS[:-1]:
        m = [re.search(r'contiguous cover of \[(\S+), (\S+)\]: True', s) for s in recs[name]]
        m = [x for x in m if x]
        if len(m) != 1:
            fails.append('%s: no contiguous cover line' % name)
            continue
        chain.append((Fraction(m[0].group(1)), Fraction(m[0].group(2))))
    ok_chain = (not fails and chain[0][0] == Fraction(1, 2)
                and all(chain[i][1] == chain[i + 1][0] for i in range(len(chain) - 1)))
    top = chain[-1][1] if chain else None
    print('f\'\' < 0 runs (scaled) and the zero run chain from 1/2 to %s: %s' % (top, ok_chain))
    zl = [s for s in recs['zero_0.668_0.6712'] if s.startswith('zero piece:')]
    zm = re.search(r'\[(\S+), (\S+)\]', zl[0]) if zl else None
    ok_zero = bool(zm) and Fraction(zm.group(1)) == Z_LO and Fraction(zm.group(2)) == Z_HI
    print('undecided piece of the zero run is [z-, z+] = [%s, %s]: %s' % (Z_LO, Z_HI, ok_zero))
    hk = [s for s in recs['hankel_0.6705_1'] if s.startswith('boxes:')]
    hm = re.search(r'covered \[(\S+), (\S+)\]: yes', hk[0]) if hk else None
    ok_hankel = bool(hm) and Fraction(hm.group(2)) == 1 and Fraction(hm.group(1)) <= top
    print('Hankel test fails on [%s, 1], which overlaps [z+, %s]: %s'
          % (hm.group(1) if hm else '?', top, ok_hankel))
    ok = ok_chain and ok_zero and ok_hankel and not fails
    if ok:
        print('certified: case (a) for a in (1/2, z-], case (b) for a in [z+, 1), '
              'z+ - z- = %.2e' % float(Z_HI - Z_LO))
    for f in fails:
        print('FAIL ' + f)
    return 0 if ok else 1


def full():
    t0 = time.time()
    procs = []
    for name, argv in RUNS:
        out = BASE / 'data' / ('threshold_%s.txt' % name)
        cmd = [sys.executable, '-I', '-B', str(BASE / 'certify_threshold.py')] + argv + ['--out', str(out)]
        procs.append((name, subprocess.Popen(cmd, cwd=BASE, stdout=subprocess.DEVNULL)))
    status = 0
    for name, p in procs:
        rc = p.wait()
        print('%-22s exit %d  (%.0f s since start)' % (name, rc, time.time() - t0), flush=True)
        status |= rc
    print('all runs done in %.0f s' % (time.time() - t0), flush=True)
    return status | check()


def quick():
    """The record check and 3 short runs, each compared with its stored line."""
    t0 = time.time()
    status = check()
    probes = [('scaled', ['scaled', '0.5', '0.50375'], 'scaled_0.50_0.53',
               '[0.50000000000000, 0.50375000000000]'),
              ('cover', ['cover', '0.6704', '0.6708', '1', '1/100'], 'zero_0.668_0.6712',
               '[0.67040000000000, 0.67080000000000]')]
    import io
    for label, argv, rec, key in probes:
        buf = io.StringIO()
        old = sys.stdout
        sys.stdout = buf
        try:
            SCALED[0] = False
            RHO_CAP[0] = Fraction(1, 25)
            rc = interval_main(argv)
        finally:
            sys.stdout = old
        new = [s for s in buf.getvalue().splitlines() if s.startswith('ok')]
        lines, _ = read_record(rec)
        stored = [s for s in (lines or []) if s.startswith('ok') and key in s]
        same = (rc == 0 and len(new) == 1 and len(stored) == 1
                and new[0].split(' T2=')[1] == stored[0].split(' T2=')[1].split('  undecided')[0])
        print('rerun %s %s: %s' % (' '.join(argv[1:]), 'matches the record' if same else 'DIFFERS', new[0] if new else '(no line)'))
        status |= 0 if same else 1
    import threshold_hankel
    buf = io.StringIO()
    old = sys.stdout
    sys.stdout = buf
    try:
        ok = threshold_hankel.run(Fraction(7, 10))
    finally:
        sys.stdout = old
    nbox = len([s for s in buf.getvalue().splitlines() if s.startswith('a in')])
    print('Hankel test on [7/10, 1]: %s (%d boxes)' % ('certified' if ok else 'FAILED', nbox))
    status |= 0 if ok else 1
    print('quick run %s (%.0f s)' % ('passed' if status == 0 else 'FAILED', time.time() - t0))
    return status


def main():
    argv = sys.argv[1:]
    out = None
    if '--out' in argv:
        i = argv.index('--out')
        out = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if not argv:
        print(__doc__)
        return 2
    if argv[0] in ('scaled', 'zero', 'cover', 'hankel', 'full', 'check', 'quick'):
        return single(argv, out)
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main())
