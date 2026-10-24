import sympy as sp
NMAX=6
fp=[0]+list(sp.symbols('a1:%d'%(NMAX+1)))
fm=[0]+list(sp.symbols('b1:%d'%(NMAX+1)))
tp7,tm7=sp.symbols('tp7 tm7')
def F(sig,n):
    if n<=0 or n>NMAX: return sp.Integer(0) if n<=0 else None
    return (fp if sig>0 else fm)[n]
def T(sig,n):
    if n<=0: return sp.Integer(0)
    tail = tp7 if sig>0 else tm7
    return sum(((fp if sig>0 else fm)[m] for m in range(n,NMAX+1)), sp.Integer(0))+tail
def comps(n):
    if n==0: yield []; return
    for a in range(1,n+1):
        for c in comps(n-a): yield [a]+c
def brute(N):
    P=[sp.Integer(0)]*(N+1)
    for c in comps(N):
        pr=sp.Integer(1); sig=1; k=0
        for i,l in enumerate(c):
            s=1 if i%2==0 else -1
            pr*= T(s,l) if i==len(c)-1 else F(s,l)
            if s>0: k+=l
        P[k]+=pr
    return [sp.expand(x) for x in P]
def conv(a,b,n):
    return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(n+1)]
def upow(sig,r,n):
    base=[sp.Integer(0)]+[F(sig,m) for m in range(1,n+1)]
    u=[sp.Integer(1)]+[sp.Integer(0)]*n
    for _ in range(r): u=conv(u,base,n)
    return u
def explicit(N):
    P=[None]*(N+1)
    U={(s,r):upow(s,r,N) for s in (1,-1) for r in range(N+2)}
    for j in range(0,N):
        tot=sp.Integer(0)
        for r in range(0,j+1):
            tot+=U[(-1,r)][j]*sum(U[(1,r)][k]*T(1,N-j-k) for k in range(0,N-j))
        for m in range(1,j+1):
            for r in range(0,j-m+1):
                tot+=T(-1,m)*U[(-1,r)][j-m]*U[(1,r+1)][N-j]
        P[N-j]=sp.expand(tot)
    return P
def recursion(N):
    A={(0,0):sp.Integer(1)}; B={(0,0):sp.Integer(0)}
    def g(D,t,k): return D.get((t,k),sp.Integer(0)) if k>=0 else sp.Integer(0)
    for t in range(1,N):
        for k in range(0,t+1):
            B[(t,k)]=sum(g(A,t-l,k-l)*F(1,l) for l in range(1,t+1))
            A[(t,k)]=sum(g(B,t-l,k)*F(-1,l) for l in range(1,t+1))
    P=[None]*(N+1)
    for j in range(0,N+1):
        tot=sum(g(A,t,t-j)*T(1,N-t) for t in range(j,N))
        tot+=sum(g(B,N-m,N-j)*T(-1,m) for m in range(1,j+1))
        P[N-j]=sp.expand(tot)
    return P
def fresh_identity(N):
    out={}
    for k in range(1,N):
        l=N-k; tot=sp.Integer(0)
        for m in range(1,N+1):
            um=upow(-1,m,N); up=upow(1,m,N)
            qp=conv(upow(1,m,N),[sp.Integer(0)]+[T(1,i) for i in range(1,N+1)],N) # q_{m+1}=T*u_m
            qm=conv(upow(-1,m-1,N),[sp.Integer(0)]+[T(-1,i) for i in range(1,N+1)],N)
            tot+=um[l]*qp[k]+up[k]*qm[l]
        out[k]=sp.expand(tot)
    return out
ok=True
for N in range(1,NMAX+1):
    b=brute(N); e=explicit(N); r=recursion(N); fi=fresh_identity(N)
    for j in range(0,N):
        if sp.expand(b[N-j]-e[N-j])!=0: ok=False; print('explicit mismatch',N,j)
    for k in range(0,N+1):
        if sp.expand(b[k]-r[k])!=0: ok=False; print('recursion mismatch',N,k)
    for k in range(1,N):
        if sp.expand(b[k]-fi[k])!=0: ok=False; print('fresh mismatch',N,k)
    # total mass check: sum P = 1 when tails consistent: substitute numeric law
    # closed forms
    if N>=3:
        c1 = fm[1]*sum(fp[a]*T(1,N-1-a) for a in range(1,N-1)) + fp[N-1]*T(-1,1)
        if sp.expand(b[N-1]-c1)!=0: ok=False; print('P(N-1) closed form mismatch',N)
    if N>=4:
        c2 = fm[2]*sum(fp[a]*T(1,N-2-a) for a in range(1,N-2)) \
           + fm[1]**2*sum(fp[a]*fp[bb]*T(1,N-2-a-bb) for a in range(1,N) for bb in range(1,N) if N-2-a-bb>=1) \
           + fp[N-2]*T(-1,2) + fm[1]*T(-1,1)*sum(fp[a]*fp[N-2-a] for a in range(1,N-2))
        if sp.expand(b[N-2]-c2)!=0: ok=False; print('P(N-2) closed form mismatch',N)
    print('N',N,'done')
print('ALL OK' if ok else 'FAIL')
print('P_6(5)=',b[5] if N==6 else '')
