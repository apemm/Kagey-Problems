import numpy as np, itertools
np.set_printoptions(precision=4, suppress=True)
# 4-state generator with a rank-one cut X={0,1}, Y={2,3}
p=np.array([1.,2.]); q=np.array([1.,3.]); u=np.array([2.,1.]); v=np.array([1.,1.])
Q=np.zeros((4,4))
Q[0,1]=0.7; Q[1,0]=1.3; Q[2,3]=0.4; Q[3,2]=2.0
Q[np.ix_([0,1],[2,3])]=np.outer(p,q); Q[np.ix_([2,3],[0,1])]=np.outer(u,v)
np.fill_diagonal(Q,0); np.fill_diagonal(Q,-Q.sum(1))
A=-Q
M=A[np.ix_([0,1],[0,1])]; Nn=A[np.ix_([2,3],[2,3])]
# cut-transpose with signs chosen so the result stays a Z-matrix
Ap=np.zeros((4,4)); Ap[np.ix_([0,1],[0,1])]=M; Ap[np.ix_([2,3],[2,3])]=Nn.T
Ap[np.ix_([0,1],[2,3])]=-np.outer(p,u); Ap[np.ix_([2,3],[0,1])]=-np.outer(q,v)
def minors(B): return {S: np.linalg.det(B[np.ix_(S,S)]) for r in range(1,5) for S in itertools.combinations(range(4),r)}
mA, mAp = minors(A), minors(Ap)
print("max |minor difference| =", max(abs(mA[S]-mAp[S]) for S in mA))
print("det A =", np.linalg.det(A), " det A' =", np.linalg.det(Ap))
w,V=np.linalg.eig(Ap); i=np.argmin(abs(w)); h=np.real(V[:,i]); h=h/h[np.argmax(abs(h))]
print("null vector of A' (positive?):", h)
D=np.diag(1/h); Qp=-(D@Ap@np.linalg.inv(D))
print("row sums of normalized Q' :", Qp.sum(1))
print("off-diagonal min of Q' :", (Qp-np.diag(np.diag(Qp))).min())
# time reversal of Q
w2,V2=np.linalg.eig(Q.T); j=np.argmin(abs(w2)); pi=np.real(V2[:,j]); pi=pi/pi.sum()
Qstar=np.diag(1/pi)@Q.T@np.diag(pi)
print("||Q'-Q|| =", np.abs(Qp-Q).max(), "  ||Q'-Q*|| =", np.abs(Qp-Qstar).max())
print("Q =\n",Q,"\nQ' =\n",Qp)
# irreducibility of Q': reachability
R=(Qp>1e-12)|np.eye(4,dtype=bool)
for _ in range(4): R=R|(R.astype(int)@R.astype(int)>0)
print("Q' irreducible:", R.all())
