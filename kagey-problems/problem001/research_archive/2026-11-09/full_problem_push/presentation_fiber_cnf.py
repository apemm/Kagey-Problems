"""Linear-size exact presentation-injectivity CNF, with optional unique auxiliaries."""
from collections import defaultdict
from itertools import combinations


def set_bits(mask):
    while mask:
        bit=mask&-mask
        yield bit
        mask-=bit


def encode(rectangles,points,no_hidden=False,parsimonious=False):
    """Point p is variable p+1; rectangle masks use the same point indices.

    no_hidden is valid only when a separate theorem excludes every hidden
    rectangle. In particular it is valid for rectangular integer grids with
    both dimensions at least four. The default permits one hidden rectangle.
    """
    rects=list(rectangles);clauses=[];top=points
    pairs={};pair_groups=defaultdict(list);point_groups=defaultdict(list);hidden=[]
    def fresh():
        nonlocal top
        top+=1;return top
    def conjunction(mask):
        flag=fresh();variables=[b.bit_length() for b in set_bits(mask)]
        clauses.append([-v for v in variables]+[flag])
        if parsimonious:clauses.extend([-flag,v] for v in variables)
        return flag
    def at_most_one(variables):
        k=len(variables)
        if k<2:return
        prefix=[fresh() for _ in range(k-1)]
        for i in range(k-1):clauses.append([-variables[i],prefix[i]])
        for i in range(1,k-1):clauses.append([-prefix[i-1],prefix[i]])
        for i in range(1,k):clauses.append([-variables[i],-prefix[i-1]])
        if parsimonious:
            clauses.append([-prefix[0],variables[0]])
            for i in range(1,k-1):clauses.append([-prefix[i],prefix[i-1],variables[i]])
    for R in rects:
        assert R.bit_count()==4 and R.bit_length()<=points
        corners=list(set_bits(R))
        for a,b in combinations(corners,2):
            P=a|b;Q=R^P
            if Q not in pairs:pairs[Q]=conjunction(Q)
            pair_groups[P].append(pairs[Q])
        for p in corners:point_groups[p].append(conjunction(R^p))
        if no_hidden:clauses.append([-p.bit_length() for p in corners])
        else:hidden.append(conjunction(R))
    for group in pair_groups.values():at_most_one(group)
    for group in point_groups.values():at_most_one(group)
    at_most_one(hidden)
    M=len(rects)
    variable_bound=(20 if no_hidden else 22)*M
    clause_bound=(75 if no_hidden else 83)*M if parsimonious else (41 if no_hidden else 44)*M
    assert top-points<=variable_bound and len(clauses)<=clause_bound
    return clauses,top,{'rectangles':M,'point_variables':points,'auxiliary_variables':top-points,
                        'clauses':len(clauses),'pair_flags':len(pairs),
                        'no_hidden':no_hidden,'parsimonious':parsimonious}
