"""Exact finite-field and row-choice checks for filled_mod7_profile_cover.md."""
from collections import Counter
from itertools import combinations, product
import json
from math import isqrt
from pathlib import Path

LOW,HIGH = (3,5,6),(1,2,4)


def mixed_rows(points):
    out = []
    for first,second in combinations(range(4),2):
        other = [i for i in range(4) if i not in (first,second)]
        A,B,C,D = [points[i] for i in (first,second,*other)]
        ux,uy = B[0]-A[0],B[1]-A[1]
        vx,vy = D[0]-C[0],D[1]-C[1]
        tx,ty = C[0]+D[0]-A[0]-B[0],C[1]+D[1]-A[1]-B[1]
        if (ux*ux+uy*uy-vx*vx-vy*vy)%7 == 0 and (ux*tx+uy*ty)%7 == 0:
            out.append((tuple(sorted((A[2],B[2]))),tuple(sorted((C[2],D[2])))))
    return out


def modular_checks():
    report = {}
    for r in (0,5):
        found = Counter()
        for s,t in product((0,1),repeat=2):
            for x,z in product(LOW if s==0 else HIGH,LOW if t==0 else HIGH):
                points = [(0,r,'r'),(0,3,'F'),(x,s,'L' if s==0 else 'H'),(z,t,'L' if t==0 else 'H')]
                found.update(mixed_rows(points))
        expected = {(('F','H'),('H','r')),(('H','L'),('F','r'))} if r==0 else set()
        assert set(found) == expected, (r,found)
        for s in (0,1):
            for x in (LOW if s==0 else HIGH):
                assert not mixed_rows([(0,r,'r'),(0,3,'F1'),(0,3,'F2'),(x,s,'B')])
        assert not mixed_rows([(0,r,'r'),(0,3,'F1'),(0,3,'F2'),(0,3,'F3')])
        angles = set()
        for s in (0,1):
            for x in (LOW if s==0 else HIGH):
                points = [(0,r,'r'),(0,3,'F'),(x,s,'L' if s==0 else 'H')]
                for center in range(3):
                    A = points[center]
                    B,C = [points[i] for i in range(3) if i!=center]
                    dot = (B[0]-A[0])*(C[0]-A[0])+(B[1]-A[1])*(C[1]-A[1])
                    if dot%7 == 0:
                        angles.add((A[2],tuple(sorted((B[2],C[2])))))
        expected_angles = {('r',('F','L')),('H',('F','r'))} if r==0 else set()
        assert angles == expected_angles,(r,angles)
        report[str(r)] = {'one_filler_mixed_types':[{'side':a,'diagonal':b,'count':n} for (a,b),n in sorted(found.items())],
                          'two_or_three_filler_mixed_types':0,
                          'one_filler_angle_types':sorted(angles)}
    # Arbitrary high replacements at holes: the remaining central-side
    # mixed case with a single actual filler (residue3) has no solution.
    collar_checks = 0
    for side_level in (0,1):
        for x in (LOW if side_level==0 else (*HIGH,0)):
            for z,w in product(LOW,(*HIGH,0)):
                collar_checks += 1
                assert not (x*(z+w-x)%7 == 3*(1-3)%7 and
                            ((w-z)**2+1-x*x-(side_level-3)**2)%7 == 0)
    report['collar_central_side_cases_checked'] = collar_checks
    return report


def square(n):
    return n>=0 and isqrt(n)**2 == n


def profiles(h):
    chosen = {}
    rejected_h = rejected_f = 0
    for L in range(1,15):
        for g in range(1,7):
            candidates = [H for H in range(h-195,h+1) if (H-L)%7==g and (H-L)%2]
            assert len(candidates)==14
            H = None
            for candidate in candidates:
                if any(square(j*(candidate-L+j)) for j in range(1,L)):
                    rejected_h += 1
                else:
                    H = candidate
                    break
            assert H is not None
            candidates_f = [F for F in range(1000,3744) if (F-L)%7==3*g%7 and (F-L)%2==0]
            assert len(candidates_f)==196
            F = None
            for candidate in candidates_f:
                if any(square(j*(H-candidate+j)) for j in range(1,h-H+1)):
                    rejected_f += 1
                else:
                    F = candidate
                    break
            assert F is not None
            assert F-L > 2*max(L-1,h-H) and H-F > 2*max(L-1,h-H)
            assert 5000 > F+2*(h-H) and h-5000+F < H-L+2
            chosen[L,g] = (H,F)
    for a,b in product(range(7),repeat=2):
        assert any((a-L)%7 in (0,5*g%7) and (b-L)%7 in (0,5*g%7) for L,g in chosen)
    return {'height':h,'profiles':len(chosen),'residue_pairs_covered':49,
            'rejected_high_candidates':rejected_h,'rejected_filler_candidates':rejected_f,
            'minimum_filler':min(F for H,F in chosen.values()),
            'maximum_filler':max(F for H,F in chosen.values())}


if __name__ == '__main__':
    result = {'status':'PASS','modular':modular_checks(),
              'row_choices':[profiles(10**10+i) for i in range(28)]}
    path = Path(__file__).with_name('filled_mod7_profile_checks.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','modular_cases':result['modular'],
                      'height_cases':len(result['row_choices']),
                      'total_profiles':sum(x['profiles'] for x in result['row_choices'])}))
