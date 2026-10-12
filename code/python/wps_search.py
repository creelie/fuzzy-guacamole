"""Exhaustive search for well-formed weighted projective 4-spaces
P(a1,...,a5) with canonical singularities and Fano index q = a1+...+a5.

Kasprzyk's criterion: P(a) is canonical iff age(k) != 4 for every k in
[2, q-2], where age(k) = k - sum_i floor(k*a_i/q).  The tuples
a1 >= ... >= a5 >= 1 are generated in numpy blocks; for each block the
values k = 2, 3, ... are tried until every tuple has a witness k.

Usage: python3 wps_search.py q [processes]
"""
import sys
import numpy as np
from multiprocessing import Pool

BLOCK = 1 << 21


def tuples_for_a1(q, a1):
    """All (a2, a3, a4, a5) with a1 >= a2 >= a3 >= a4 >= a5 >= 1 and sum q - a1."""
    rest = q - a1
    out = []
    for a2 in range(min(a1, rest - 3), 0, -1):
        r2 = rest - a2
        if 4 * a2 < rest:
            break
        a3 = np.arange(1, min(a2, r2 - 2) + 1)
        a3 = a3[3 * a3 >= r2]
        if a3.size == 0:
            continue
        r3 = r2 - a3
        # a4 runs over ceil(r3/2) .. min(a3, r3-1)
        lo = (r3 + 1) // 2
        hi = np.minimum(a3, r3 - 1)
        cnt = np.maximum(hi - lo + 1, 0)
        if cnt.sum() == 0:
            continue
        rep_a3 = np.repeat(a3, cnt)
        rep_r3 = np.repeat(r3, cnt)
        start = np.repeat(lo, cnt)
        offs = np.arange(cnt.sum()) - np.repeat(np.cumsum(cnt) - cnt, cnt)
        a4 = start + offs
        a5 = rep_r3 - a4
        out.append(np.stack([np.full(a4.size, a2), rep_a3, a4, a5]))
    if not out:
        return np.zeros((4, 0), dtype=np.int64)
    return np.concatenate(out, axis=1).astype(np.int64)


def wellformed(A):
    """A has shape (5, n); True where every four of the five weights are coprime."""
    ok = np.ones(A.shape[1], dtype=bool)
    for i in range(5):
        g = np.zeros(A.shape[1], dtype=np.int64)
        for j in range(5):
            if j != i:
                g = np.gcd(g, A[j])
        ok &= (g == 1)
    return ok


def canonical_in_block(q, A):
    """Return the columns of A (shape (5, n)) that pass Kasprzyk's criterion."""
    idx = np.arange(A.shape[1])
    for k in range(2, q - 1):
        if idx.size == 0:
            break
        s = (k * A[:, idx] // q).sum(axis=0)
        idx = idx[k - s != 4]
    return A[:, idx]


def work(args):
    q, a1 = args
    T = tuples_for_a1(q, a1)
    n = T.shape[1]
    if n == 0:
        return 0, 0, []
    A = np.vstack([np.full(n, a1, dtype=np.int64), T])
    wf = wellformed(A)
    A = A[:, wf]
    canon = []
    for s in range(0, A.shape[1], BLOCK):
        C = canonical_in_block(q, A[:, s:s + BLOCK])
        canon.extend(tuple(int(x) for x in C[:, j]) for j in range(C.shape[1]))
    return n, int(wf.sum()), canon


def main():
    q = int(sys.argv[1])
    procs = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    jobs = [(q, a1) for a1 in range(q - 4, 0, -1) if 5 * a1 >= q]
    tuples = wellf = 0
    canon = []
    with Pool(procs) as pool:
        for n, w, c in pool.imap_unordered(work, jobs, chunksize=1):
            tuples += n
            wellf += w
            canon.extend(c)
    for t in sorted(canon):
        print("canonical", *t)
    print(f"q={q} tuples={tuples} wellformed={wellf} canonical={len(canon)}")


if __name__ == "__main__":
    main()
