"""Exact finite checks of the periodic-orientation impossibility construction."""
from math import lcm
from pathlib import Path
import json

from verify_period_eight_obstruction import rectangle

HERE=Path(__file__).resolve().parent


def check_period(period):
    odd=period;k=0
    while odd%2==0:odd//=2;k+=1
    A=1
    for a in range(1,8*period,2):A=lcm(A,a)
    C=A*odd;T=C;u=1+8*T+20*T*T;F=u+2*T
    two=2**(k+2)
    first=pow(F,-1,two)
    L=first+two*((pow(2*F,-1,C)-first)*pow(two,-1,C)%C)
    assert L>0 and L%2
    N=2*F*L-1;h=N+2
    assert N%C==0 and N%(2**(k+3))==1 and h%8==3
    graph=[set() for _ in range(period)]
    span=0
    for a in range(1,8*period,2):
        assert N%a==0
        b=N//a;span=max(span,a+b)
        assert b%odd==0 and a*b%(2**(k+3))==1
        i=a//8;j=(b//8)%period
        graph[i].add(j);graph[j].add(i)
        assert (a+b)%4==2
    reached={0};stack=[0]
    while stack:
        i=stack.pop()
        for j in graph[i]-reached:reached.add(j);stack.append(j)
    assert len(reached)==period
    assert span<=h-1 and (span+7)//8<(h+1)//2
    B1=(0,1+2*u*L);B2=(u*L,1)
    B3=((1+8*T)*L,1);B4=((8*T+20*T*T)*L,h)
    W=(4*T*L,1+2*(u+T)*L);Z=((u+4*T)*L,1+2*T*L)
    assert rectangle({B1,B2,W,Z}) and rectangle({B3,B4,W,Z})
    assert (20*T*T-1)**2+4*F*F==5*u*u
    assert B2[0]%2 and B3[0]%2 and B4[0]%8==4
    assert W[0]%8==4 and Z[0]%2
    assert all(1<r<h for x,r in (W,Z))
    assert (Z[0]+7)//8<(h-1)//2
    return {'period':period,'height_bits':h.bit_length(),'graph_vertices':len(reached)}


def main():
    results=[check_period(p) for p in range(1,65)]
    out={'status':'PASS','periods_checked':len(results),'results':results}
    (HERE/'periodic_orientation_obstruction_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','periods_checked':len(results),
                      'maximum_height_bits':max(r['height_bits'] for r in results)}))


if __name__=='__main__':main()
