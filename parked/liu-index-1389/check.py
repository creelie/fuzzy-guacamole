import pickle, sympy
res=pickle.load(open('inv.pkl','rb')); S=pickle.load(open('iwps.pkl','rb'))
D=sorted(res)
print('D not in Iwps:',[x for x in D if x not in S])
hits={}
for x in D:
    for dv in sympy.divisors(x):
        if dv not in S: hits.setdefault(dv,[]).append(x)
print('divisors not in Iwps:',sorted(hits.items())[:50])
print(max(D))
