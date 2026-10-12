import gzip, itertools, sys
from fractions import Fraction
from math import gcd
from functools import reduce
import sympy

def lcm(a,b): return a*b//gcd(a,b)

ws=[]
with gzip.open(sys.argv[1] if len(sys.argv)>1 else 'w5.ip.gz','rt') as f:
    for line in f:
        p=line.split()
        d=int(p[0]); w=list(map(int,p[1:6]))
        ws.append((d,w))
print(len(ws))

def structures(d,w):
    n=5
    P=[]
    for i in range(n):
        opts=[]
        if d%w[i]==0: opts.append((i,d//w[i]))
        for j in range(n):
            if j!=i and (d-w[j])%w[i]==0 and (d-w[j])//w[i]>=2:
                opts.append((j,(d-w[j])//w[i]))
        P.append(opts)
    for choice in itertools.product(*P):
        tgt=[c[0] for i,c in enumerate(choice) if c[0]!=i]
        if len(tgt)!=len(set(tgt)): continue
        yield choice

res={}
count=0
for (d,w) in ws:
    for ch in structures(d,w):
        A=sympy.zeros(5,5)
        for i,(j,a) in enumerate(ch):
            A[i,i]+=a
            if j!=i: A[i,j]+=1
        if A.det()==0: continue
        qT=(A.T).LUsolve(sympy.ones(5,1))
        dT=reduce(lcm,[sympy.fraction(x)[1] for x in qT])
        count+=1
        res.setdefault(int(dT),[]).append((d,tuple(w),ch))
print('invertible structures',count,'distinct dT',len(res))
import pickle
pickle.dump(res,open('inv.pkl','wb'))
