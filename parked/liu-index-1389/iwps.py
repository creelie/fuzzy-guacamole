import sys
import re
from math import gcd
from functools import reduce
def canonical(a):
    q=sum(a); n=len(a)-1
    for k in range(2,q-1):
        age=k-sum((ai*k)//q for ai in a)
        if age==n: return False
    return True
def wellformed(a):
    for i in range(len(a)):
        if reduce(gcd,a[:i]+a[i+1:])!=1: return False
    return True
S={}
for line in open(sys.argv[1] if len(sys.argv)>1 else 'results.txt'):
    m=re.match(r'h=(\d+) -> \[([\d,]+)\]',line.strip())
    if m: S[int(m.group(1))]=list(map(int,m.group(2).split(',')))
# small h brute force
def small(q):
    for a1 in range(q,0,-1):
      for a2 in range(min(a1,q-a1),0,-1):
        for a3 in range(min(a2,q-a1-a2),0,-1):
          for a4 in range(min(a3,q-a1-a2-a3),0,-1):
            a5=q-a1-a2-a3-a4
            if a5<1 or a5>a4: continue
            t=[a1,a2,a3,a4,a5]
            if wellformed(t) and canonical(t): return t
    return None
for q in range(5,100):
    t=small(q)
    if t: S[q]=t
    else: print('missing small',q)
for q in range(1,5): S[q]=None
import pickle; pickle.dump(S,open('iwps.pkl','wb'))
print(len(S))
# verify listed tuples
bad=[h for h,t in S.items() if t and h>=100 and not (sum(t)==h and wellformed(t) and canonical(t))]
print('bad',bad)
