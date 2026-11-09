"""Independent point-vector checks for the nearby-prime scaffold lemmas.

The finite checks supplement the proof; they do not assert identifying
scaffolds. In particular vertical rivals may occur and are reported.
"""
from collections import defaultdict
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def twin_above(n):
    p = n + 1 + (n % 2)
    while not (prime(p) and prime(p+2)):
        p += 2
    return p, p+2


def direction(x, y):
    g = gcd(x, y)
    x, y = x//g, y//g
    return (x, y) if x > 0 or (x == 0 and y > 0) else (-x, -y)


def check(h):
    p, q = twin_above(500*h)
    delta = q-p
    assert p > 100*(delta*delta+1)*h
    points = []
    for a in range(1, h+1, 2):
        for b in range(2, h+1, 2):
            x = 2*q*a-2*p*b
            points += [(x, a, a-b, a, b), (x, b, a-b, a, b)]
    assert len(set((x,y) for x,y,*_ in points)) == len(points)
    columns = {p[0] for p in points}
    assert len(columns) == (h//2)*((h+1)//2)
    angles_checked = 0
    for first in points:
        seen = set()
        for second in points:
            dx, dy = second[0]-first[0], second[1]-first[1]
            if dx == 0 or dy == 0:
                continue
            unit = direction(dx,dy)
            assert direction(-dy,dx) not in seen, (h, first, second, 'tilted right angle')
            seen.add(unit)
            angles_checked += 1

    pairs = defaultdict(list)
    p_count = 0
    first_p = None
    for i,j in combinations(range(len(points)),2):
        a,b = points[i],points[j]
        dx,dy = b[0]-a[0],b[1]-a[1]
        norm = dx*dx+dy*dy
        pairs[norm].append((i,j,dx,dy))
        length = isqrt(norm)
        if dx and (a[1]-b[1])%2 and length*length == norm:
            low,high = a[1]+b[1]-length,a[1]+b[1]+length
            if low%2 == 0 and low >= 2 and high <= 2*h:
                assert a[2] == b[2]
                p_count += 1
                if first_p is None:
                    first_p = {'black': [list(a[:2]),list(b[:2])], 'length':length,
                               'offset':a[2], 'white_rows':[low//2,high//2]}

    mixed_count = vertical_count = 0
    candidate_pairs = 0
    black = {(p[0],p[1]) for p in points}
    for group in pairs.values():
        for side in group:
            i,j,ux,uy = side
            for diagonal in group:
                A,B = points[i],points[j]
                k,l,vx,vy = diagonal
                if len({i,j,k,l}) < 4 or ux*vy == uy*vx:
                    continue
                C,E = points[k],points[l]
                tx,ty = C[0]+E[0]-A[0]-B[0],C[1]+E[1]-A[1]-B[1]
                candidate_pairs += 1
                if (tx == ty == 0) or ux*tx+uy*ty:
                    continue
                numerators = [(C[0]+E[0]+sgn*ux,C[1]+E[1]+sgn*uy) for sgn in [-1,1]]
                if any(x%2 or y%2 or y<2 or y>2*h for x,y in numerators):
                    continue
                whites = [(x//2,y//2) for x,y in numerators]
                assert not any(z in black for z in whites)
                if ux == 0:
                    vertical_count += 1
                    continue
                assert A[2] == B[2] and C[2] == E[2] and A[2] != C[2]
                assert (A[1]-B[1])%2 and (C[1]-E[1])%2
                mixed_count += 1
                # Orient each pair from the even endpoint to the odd one.
                if A[1]%2:
                    A,B = B,A
                if C[1]%2:
                    C,E = E,C
                u,v = A[2],C[2]
                d,e = B[3]-A[3],E[3]-C[3]
                S = C[3]+E[3]-A[3]-B[3]
                K = 4*delta*delta+1
                assert K*d*d+2*d*u+u*u == K*e*e+2*e*v+v*v
                assert (K*d+u)*S == (d+u-8*delta*p*d)*(v-u)
    return {'height':h,'p':p,'q':q,'gap':delta,'points':len(points),
            'directed_vectors_checked':angles_checked,
            'equal_norm_pair_candidates':candidate_pairs,
            'vertical_rival_black_diagonals':p_count,'first_vertical_rival':first_p,
            'mixed_vertical_side_cases':vertical_count,'remaining_mixed_cases':mixed_count,
            'status':'PASS'}


def remaining_mixed_certificate():
    m,A = 1200,1000049
    p,q = m*A-1,m*A+1
    h = A+64*m-28
    assert prime(p) and prime(q) and p > 500*h
    labels = [(A+64*m-30,64*m+4),(A+64*m-28,64*m+6),
              (A-26,4),(A-28,2)]
    origin = 2*q*labels[0][0]-2*p*labels[0][1]
    columns = [2*q*a-2*p*b-origin for a,b in labels]
    T = 8*m*(A-32)
    assert columns == [0,8,T+8,T]
    black = {(x,y) for x,pair in zip(columns,labels) for y in pair}
    assert all(1 <= y <= h for x,y in black)
    side = [(0,64*m+4),(8,h)]
    diagonal = [(T+8,4),(T,A-28)]
    whites = [(T,4),(T+8,A-28)]
    assert not (set(whites) & black)
    ux,uy = 8,A-32
    vx,vy = -8,A-32
    assert ux*ux+uy*uy == vx*vx+vy*vy
    assert ux*T-uy*64*m == 0
    assert ux*vy-uy*vx != 0
    # Exhaust every possible opposite-parity vertical rival of these labels.
    p_checks = 0
    for (x,y),(X,Y) in combinations(sorted(black),2):
        if x == X or (y-Y)%2 == 0:
            continue
        square = (x-X)**2+(y-Y)**2
        length = isqrt(square)
        low,high = y+Y-length,y+Y+length
        assert not (length*length == square and low%2 == 0 and low >= 2 and high <= 2*h)
        p_checks += 1
    return {'status':'PASS','height':h,'m':m,'A':A,'p':p,'q':q,
            'labels':labels,'columns_after_translation':columns,
            'side_rectangle':side+whites,'diagonal_rectangle':diagonal+whites,
            'common_white_pair':whites,'opposite_parity_pairs_checked':p_checks}


if __name__ == '__main__':
    results = []
    for height in [4,8,12,16,20,24,28]:
        result = check(height)
        results.append(result)
        print(json.dumps({k:v for k,v in result.items() if k != 'first_vertical_rival'}),flush=True)
    path = Path(__file__).with_name('nearby_prime_scaffold_checks.json')
    certificate = remaining_mixed_certificate()
    path.write_text(json.dumps({'status':'PASS','cases':results,
                               'remaining_mixed_certificate':certificate},indent=2)+'\n')
    print(json.dumps({'remaining_mixed_certificate':'PASS','height':certificate['height']}))
