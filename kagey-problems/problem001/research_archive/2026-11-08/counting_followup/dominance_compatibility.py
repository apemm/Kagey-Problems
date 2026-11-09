"""Exact finite/periodic sea-word compatibility with row bipartitions.

Standard library only. Rows are 1..h. A word's constraint graph records exactly
the partition-dependent singleton and vertical-pair axis rivals. Other failures
are checked independently of the partition. This is the zero-hidden sea shift.
"""
import itertools
import json
from functools import lru_cache
from fractions import Fraction


@lru_cache(None)
def placements(h, n):
    out = []
    for b in range(1, h):
        for d in range(1, h-b):
            for a in range(1, b*d+1):
                if b*d % a:
                    continue
                c = b*d//a
                if a+c >= n:
                    continue
                for r in range(b+1, h-d+1):
                    sh = ((0,r), (a,r-b), (c,r+d), (a+c,r-b+d))
                    for x0 in range(n-a-c):
                        out.append(tuple((x0+x,y) for x,y in sh))
    return tuple(out)


def compatibility(h, word):
    edges = set()
    seen = set()
    for rect in placements(h, len(word)):
        white = tuple(sorted((x,r) for x,r in rect if word[x] != r))
        if len(white) > 2:
            continue
        if not white:
            return None
        if white in seen:
            return None
        seen.add(white)
        if len(white) == 1:
            x,r = white[0]
            edges.add(tuple(sorted((r,word[x]))))
        else:
            (x,r),(z,s) = white
            if x == z:
                edges.add(tuple(sorted((r,s))))
            elif r == s:
                if word[x] == word[z]:
                    return None
            elif word[x] == s and word[z] == r:
                return None
    return edges


def allowed(edges, block):
    return edges is not None and all((r in block) == (s in block) for r,s in edges)


def periodic_graph(h, period):
    W = 1+(h-1)**2//4
    length = len(period)+2*W
    return compatibility(h, tuple(period[j%len(period)] for j in range(length)))


def strongly_connected(adjacency):
    n=len(adjacency)
    reverse=[[] for _ in range(n)]
    for i,row in enumerate(adjacency):
        for j in row:
            reverse[j].append(i)
    visited=set()
    order=[]
    for start in range(n):
        if start in visited:
            continue
        visited.add(start)
        stack=[(start,0)]
        while stack:
            u,k=stack[-1]
            if k==len(adjacency[u]):
                order.append(u)
                stack.pop()
                continue
            v=adjacency[u][k]
            stack[-1]=(u,k+1)
            if v not in visited:
                visited.add(v)
                stack.append((v,0))
    used=set()
    components=[]
    for start in reversed(order):
        if start in used:
            continue
        component=[]
        stack=[start]
        used.add(start)
        while stack:
            u=stack.pop()
            component.append(u)
            for v in reverse[u]:
                if v not in used:
                    used.add(v)
                    stack.append(v)
        components.append(component)
    return components


def collatz_bounds(adjacency, component, iterations=160):
    local={u:i for i,u in enumerate(component)}
    rows=[[local[v] for v in adjacency[u] if v in local] for u in component]
    vector=[1]*len(rows)
    # M+I is primitive on every irreducible component, including periodic ones.
    for _ in range(iterations):
        vector=[vector[i]+sum(vector[j] for j in row) for i,row in enumerate(rows)]
    product=[vector[i]+sum(vector[j] for j in row) for i,row in enumerate(rows)]
    ratios=[Fraction(a,b)-1 for a,b in zip(product,vector)]
    return min(ratios),max(ratios)


def graph_analysis(h,block):
    W=1+(h-1)**2//4
    memory=2*W
    states=[()]
    for _ in range(memory):
        states=[w+(a,) for w in states for a in range(1,h+1)
                if allowed(compatibility(h,w+(a,)),block)]
    index={w:i for i,w in enumerate(states)}
    adjacency=[[] for _ in states]
    for i,w in enumerate(states):
        for a in range(1,h+1):
            word=w+(a,)
            if allowed(compatibility(h,word),block):
                adjacency[i].append(index[word[1:]])
    comps=strongly_connected(adjacency)
    cyclic=[c for c in comps if len(c)>1 or c[0] in adjacency[c[0]]]
    data=[]
    for comp in cyclic:
        lo,hi=collatz_bounds(adjacency,comp)
        constants=[r for r in range(1,h+1) if index.get((r,)*memory) in comp]
        data.append({'states':len(comp),'constant_rows':constants,
                     'rho_lower':float(lo),'rho_upper':float(hi),
                     'lower_fraction':str(lo),'upper_fraction':str(hi)})
    return {'block':sorted(block),'states':len(states),'edges':sum(map(len,adjacency)),
            'scc_sizes':sorted(map(len,comps),reverse=True),'cyclic_components':data}


def symbol_map_checks():
    permutation=(1,3,2,4)
    checked=0
    for word in itertools.product(range(1,5),repeat=7):
        if allowed(compatibility(4,word),{1,2}):
            image=tuple(permutation[r-1] for r in word)
            assert allowed(compatibility(4,image),{1,3})
            checked+=1
    remaining=list(itertools.permutations(range(1,5)))
    witnesses=[]
    for n in range(1,5):
        cache={w:allowed(periodic_graph(4,w),{1,3})
               for w in itertools.product(range(1,5),repeat=n)}
        for word in itertools.product(range(1,5),repeat=n):
            if not allowed(periodic_graph(4,word),{1,4}):
                continue
            for p in remaining[:]:
                image=tuple(p[r-1] for r in word)
                if not cache[image]:
                    witnesses.append({'permutation':p,'period':word,'image_period':image})
                    remaining.remove(p)
    assert not remaining
    return {'block_12_embedding':{'permutation':permutation,'checked_length':7,
                                  'checked_allowed_words':checked},
            'block_14_all_symbol_permutations_fail':witnesses}


def main():
    h = 4
    parity = frozenset((1,3))
    others = (frozenset((1,2)), frozenset((1,4)))
    answers = {}
    for n in range(1,9):
        for word in itertools.product(range(1,h+1), repeat=n):
            graph = periodic_graph(h,word)
            if graph is None:
                continue
            p = allowed(graph,parity)
            for other in others:
                t = allowed(graph,other)
                direction = 'parity_only' if p and not t else 'other_only' if t and not p else None
                if direction:
                    name = ''.join(map(str,sorted(other)))+'_'+direction
                    if name not in answers:
                        answers[name] = {'period':word,'constraint_edges':sorted(graph),'other_block':sorted(other)}
        if len(answers) == 4:
            break
    graphs=[graph_analysis(h,b) for b in (parity,*others)]
    enclosures=((3351996777310,3351996777311),(2931999526203,2931999526204),
                (2856932081641,2856932081642))
    for graph,(left,right) in zip(graphs,enclosures):
        lo=max(Fraction(c['lower_fraction']) for c in graph['cyclic_components'])
        hi=max(Fraction(c['upper_fraction']) for c in graph['cyclic_components'])
        assert Fraction(left,10**12)<lo<=hi<Fraction(right,10**12)
    parity_lower=max(Fraction(c['lower_fraction']) for c in graphs[0]['cyclic_components'])
    other_upper=max(Fraction(c['upper_fraction']) for g in graphs[1:] for c in g['cyclic_components'])
    assert parity_lower>other_upper
    print(json.dumps({'height':h,'periodic_incomparability':answers,'graphs':graphs,
                      'symbol_map_checks':symbol_map_checks(),
                      'strict_parity_dominance_certified':True},indent=2))


if __name__ == '__main__':
    main()
