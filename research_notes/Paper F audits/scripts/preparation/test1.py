import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from bl import *
from atlas_copy import occupation
N=60; J=5
f,T,mu=zeta_law(1.5,N+5)
E=boundary(N,J,f,T,f,T,'+')
P=occupation(N,f,T,f,T)
print('fresh+ vs atlas', max(abs(E[m][N]-P[N-m])/P[N-m] for m in range(J+1)))
# fresh minus via symmetry: F^-_N(N-m) for equal laws = F^+_N(m) (count of plus = m when minus count N-m)
Em=boundary(N,J,f,T,f,T,'-')
print('fresh- vs atlas(sym)', max(abs(Em[m][N]-P[m])/P[m] for m in range(1,J+1)), Em[0][N])
# closed forms fresh plus
def conv(a,b,n): return sum(a[i]*b[n-i] for i in range(1,n))
fT=lambda n: conv(f,T,n)
P1=f[1]*fT(N-1)+f[N-1]
ffT=lambda n: sum(f[a]*f[b]*T[n-a-b] for a in range(1,n) for b in range(1,n-a))
ff=lambda n: conv(f,f,n)
P2=f[2]*fT(N-2)+f[1]**2*ffT(N-2)+f[1]*ff(N-2)+f[N-2]*T[2]
print('closed P(N-1)',P1,E[1][N],' P(N-2)',P2,E[2][N])
