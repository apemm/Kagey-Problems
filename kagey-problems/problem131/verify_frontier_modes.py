"""Checks for multidimensional superlevel geometry and weak-field modal phases.

Run with python -B verify_frontier_modes.py. Uses only the standard library.
The large-N refresh series is evaluated with 65-digit Decimal arithmetic and
a wider cutoff check; this is numerical evidence, not interval certification.
Finite-N global modes are independently computed by a word-state dynamic program.
"""
from decimal import Decimal, localcontext
from math import ceil, exp, floor, gamma, log, pi, sqrt
from pathlib import Path
import json

from verify_simplex_threshold import positive_coefficients, log_ratio_from_coeff


def a_k(k):
    return log(4*pi)/2 - (k+0.5)*log(k)/(k-1)


def lattice_counts():
    """Independent covolume checks in dimensions one and two."""
    rows = []
    B = 1.3
    for k in (2, 3):
        radius = sqrt(4*B/k**2)
        target = pi**((k-1)/2)/gamma(1+(k-1)/2)/sqrt(k)*radius**(k-1)
        for mesh_inverse in (100, 1000, 10000):
            Q = radius**2*mesh_inverse**2
            if k == 2:
                edge = ceil(sqrt(Q/2))-1
                count = 2*edge+1
            else:
                count = 0
                for x in range(-ceil(sqrt(2*Q/3)), ceil(sqrt(2*Q/3))+1):
                    discriminant = 2*Q-3*x*x
                    if discriminant <= 0:
                        continue
                    lo = (-x-sqrt(discriminant))/2
                    hi = (-x+sqrt(discriminant))/2
                    count += max(0, ceil(hi)-floor(lo)-1)
            value = count/mesh_inverse**(k-1)
            assert abs(value-target) < 6/mesh_inverse
            rows.append({"k": k, "inverse_mesh": mesh_inverse,
                         "scaled_lattice_count": value,
                         "predicted_volume": target, "error": value-target})
    return rows


def profile_checks():
    rows = []
    with localcontext() as ctx:
        ctx.prec = 65
        pi_d = Decimal("3.1415926535897932384626433832795028841971693993751058209749445923")
        for k in (2, 3, 4):
            ak = (4*pi_d).ln()/2-(Decimal(k)+Decimal("0.5"))*Decimal(k).ln()/(k-1)
            for n in (10**4, 10**8, 10**16):
                L = Decimal(n).ln()
                t = Decimal("0.2")
                # A nonzero tangent-space deviation; sum y_i = 0 exactly.
                target_y = [Decimal("0.2")] + [-Decimal("0.2")/(k-1)]*(k-1)
                counts = [int(Decimal(n)/k + y*Decimal(n)/L.sqrt()) for y in target_y[:-1]]
                counts.append(n-sum(counts))
                y = [(Decimal(ni)/n-Decimal(1)/k)*L.sqrt() for ni in counts]
                cutoff = min(n, ceil(3*k*(log(n)+1))+60)
                coeff = positive_coefficients(n, k, cutoff, counts)
                z = L-L.ln()/2+t
                actual = log_ratio_from_coeff(n, k, coeff, z)
                predicted = (k-1)*(t-ak)-Decimal(k*k)/4*sum(yi*yi for yi in y)
                # Test an arbitrary fixed field on this support as well.
                fields = [Decimal(i)/3 for i in range(k)]
                tilted = actual + sum(h*Decimal(ni)/n for h, ni in zip(fields, counts))-max(fields)
                tilted_prediction = predicted+sum(fields)/k-max(fields)
                cutoff_error = None
                if n == 10**16:
                    wider = positive_coefficients(n, k, cutoff+35, counts)
                    cutoff_error = abs(log_ratio_from_coeff(n, k, wider, z)-actual)
                    assert cutoff_error < Decimal("1e-25")
                    assert abs(actual-predicted) < Decimal("0.2")
                    assert abs(tilted-tilted_prediction) < Decimal("0.2")
                rows.append({"k": k, "N": n, "counts": counts,
                             "actual_scaled_deviation": [str(yi) for yi in y],
                             "untilted_log_ratio": str(actual),
                             "untilted_profile_error": str(actual-predicted),
                             "tilted_profile_error": str(tilted-tilted_prediction),
                             "wider_cutoff_difference": str(cutoff_error)})
    return rows


def word_state_ratios(n, d, u):
    """All exact word sums evaluated in floating point by an independent DP.

    Every initial color has weight one, a repeat has weight one, and a
    change has weight u; the resulting bin weights are ratios to a vertex.
    """
    states = {}
    for i in range(d):
        counts = tuple(int(i == j) for j in range(d))
        last = [0.0]*d
        last[i] = 1.0
        states[counts] = last
    for _ in range(1, n):
        new = {}
        for counts, last in states.items():
            total = sum(last)
            for j in range(d):
                next_counts = list(counts)
                next_counts[j] += 1
                key = tuple(next_counts)
                values = new.setdefault(key, [0.0]*d)
                values[j] += u*total+(1-u)*last[j]
        states = new
    return {counts: sum(last) for counts, last in states.items()}


def finite_modal_checks():
    rows = []
    fields = (0.0, 0.0, -6.0)
    assert 6 > 6*(a_k(2)-a_k(3))
    for n in (30, 60, 120):
        for t, predicted_support_size in ((-1.0, 1), (0.0, 2), (3.0, 3)):
            u = (log(n)-log(log(n))/2+t)/n
            values = word_state_ratios(n, 3, u)
            tilted = {counts: value*exp(sum(h*ni/n for h, ni in zip(fields, counts)))
                      for counts, value in values.items()}
            maximum = max(tilted.values())
            modes = [counts for counts, value in tilted.items()
                     if abs(value-maximum) <= 1e-12*maximum]
            sizes = sorted({sum(ni > 0 for ni in counts) for counts in modes})
            # This check is finite and does not infer the asymptotic theorem.
            if n >= 60:
                assert sizes == [predicted_support_size], (n, t, modes)
            if predicted_support_size == 2 and n >= 60:
                assert all(counts[2] == 0 for counts in modes)
            rows.append({"N": n, "t": t, "fields": fields,
                         "u": u, "global_modes": modes,
                         "maximum_untilted_vertex_units": maximum,
                         "observed_support_sizes": sizes,
                         "limiting_winning_support_size": predicted_support_size})
    # Pointwise field tilt can move a full-support maximum away from exact balance.
    # The theorem intentionally gives scaled convergence, not exact balanced modes.
    return rows


def face_realizations():
    rows = []
    for d in range(3, 9):
        for k in range(2, d):
            t = a_k(k)+0.04 if k == 2 else (a_k(k)+a_k(k-1))/2
            base = (k-1)*(t-a_k(k))
            H = 1+max([0.0]+[j*((j-1)*(t-a_k(j))-base)/(j-k)
                                  for j in range(k+1, d+1)])
            scores = [0.0]+[(j-1)*(t-a_k(j))-H*max(j-k, 0)/j
                            for j in range(2, d+1)]
            assert scores[k-1] > max(score for j, score in enumerate(scores, 1) if j != k)
            rows.append({"d": d, "realized_support_size": k, "t": t,
                         "negative_field_strength": H, "top_support_scores": scores})
    return rows


def full_hierarchy_checks():
    """Check all score lines, including nonadjacent rivals, in every phase."""
    rows = []
    for d in range(3, 11):
        for H in (0.76, 1.0, 2.0):
            c = [0.0]+[(k+0.5)*log(k)-(k-1)*log(4*pi)/2
                       for k in range(2, d+1)]
            transitions = [c[k-1]-c[k]+H*(4*k-1)/6 for k in range(1, d)]
            assert all(a < b for a, b in zip(transitions, transitions[1:]))
            fields = [-H*(i-1)**2 for i in range(1, d+1)]
            for k in range(1, d+1):
                t = (transitions[0]-1 if k == 1 else
                     transitions[-1]+1 if k == d else
                     (transitions[k-2]+transitions[k-1])/2)
                scores = [c[j-1]+(j-1)*t+sum(fields[:j])/j
                          for j in range(1, d+1)]
                margin = scores[k-1]-max(score for j, score in enumerate(scores, 1) if j != k)
                assert margin > 0
                rows.append({"d": d, "field_strength": H,
                             "winning_support_size": k, "sample_t": t,
                             "score_margin_over_all_other_sizes": margin,
                             "transition_parameters": transitions})
    return rows


if __name__ == "__main__":
    result = {"status": "passed",
              "numerical_scope": "65-digit Decimal refresh series; wider cutoff comparison; not interval-certified. Finite modal DP uses double precision.",
              "lattice_volume_checks": lattice_counts(),
              "profile_checks": profile_checks(),
              "finite_modal_checks": finite_modal_checks(),
              "proper_face_realizations": face_realizations(),
              "full_hierarchy_checks": full_hierarchy_checks()}
    path = Path(__file__).resolve().parent / "data" / "frontier-modes-verification.json"
    path.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "lattice_checks": len(result["lattice_volume_checks"]),
                      "profile_checks": len(result["profile_checks"]),
                      "independent_global_mode_checks": len(result["finite_modal_checks"]),
                      "proper_face_realizations": len(result["proper_face_realizations"]),
                      "full_hierarchy_phase_checks": len(result["full_hierarchy_checks"]),
                      "output": str(path)}, indent=2))
