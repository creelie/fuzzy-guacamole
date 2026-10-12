# Split the (t1,t2) streams into units (t1, t2, lo, hi) of at most CAP k-values.
import sys, glob, json
Q = 1389
def boxes(t1, t2):
    out = []
    for t3 in range(t2 + 1):
        for t4 in range(t3 + 1):
            if 2*(1+8*t1) + (1+8*t2) + (1+8*t3) + (1+8*t4) <= Q:
                out.append((t3, t4))
    return out
def units(dirn, cap):
    res = []
    for fn in sorted(glob.glob(dirn + "/t1_*.txt")):
        for line in open(fn):
            v = list(map(int, line.split())); t1, t2, dg = v[0], v[1], v[3:]
            bx = boxes(t1, t2); i = 0; per = {}
            for (t3, t4) in bx:
                n = dg[i]; per.setdefault(t3, []).append(dg[i:i+1+n]); i += 1 + n
            assert i == len(dg)
            t3s = list(range(t2 + 1)); lo = 0; cur = []; cnt = 0
            for t3 in t3s:
                seg = per.get(t3, []); c = sum(len(s) - 1 for s in seg)
                if cur and cnt + c > cap:
                    res.append((t1, t2, lo, t3, [d for s in cur for d in s])); lo = t3; cur = []; cnt = 0
                cur += seg; cnt += c
            res.append((t1, t2, lo, t2 + 1, [d for s in cur for d in s]))
    return res
def num(dg):
    x = 0
    for d in reversed(dg): x = x * 2048 + d
    return x
if __name__ == "__main__":
    u = units(sys.argv[1], int(sys.argv[2]))
    print(len(u))
    from collections import Counter
    c = Counter()
    for (t1, t2, lo, hi, dg) in u: c[t1] += len(dg)
    print(sorted(c.items(), key=lambda x: -x[1])[:10])
