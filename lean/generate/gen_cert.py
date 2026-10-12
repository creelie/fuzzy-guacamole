# Write the certificate modules LiuIndex/Cert/Txx.lean and LiuIndex/Cert/All.lean
# from the witness streams produced by gen6.c.
#   python3 gen_cert.py <streams-dir> <out-dir> [cap]
import os, sys
from collections import OrderedDict
from mkunits import units, num

Q = 1389

def main():
    sdir, odir = sys.argv[1], sys.argv[2]
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 1500
    us = units(sdir, cap)
    by_t1 = OrderedDict()
    for (t1, t2, lo, hi, dg) in us:
        by_t1.setdefault(t1, OrderedDict()).setdefault(t2, []).append((lo, hi, dg))
    t1s = sorted(by_t1)
    assert t1s == list(range(len(t1s)))
    T = len(t1s)
    assert Q < 2 * (1 + 8 * T) + 3 and not Q < 2 * (1 + 8 * (T - 1)) + 3
    os.makedirs(odir, exist_ok=True)
    for t1 in t1s:
        rows = by_t1[t1]
        t2s = sorted(rows)
        n = len(t2s)
        assert t2s == list(range(n)) and n <= t1 + 1
        L = []
        L.append("import LiuIndex.Check.Sound\n")
        L.append("/-! Certificate for the boxes with first corner index `t1 = %d`. -/\n" % t1)
        L.append("namespace LiuCert\nopen LiuCheck\nset_option Elab.async false\n")
        for t2 in t2s:
            segs = rows[t2]
            assert segs[0][0] == 0 and segs[-1][1] == t2 + 1
            for a, b in zip(segs, segs[1:]):
                assert a[1] == b[0]
            for (lo, hi, dg) in segs:
                L.append("theorem u_%d_%d_%d : run12 %d %d %d %d 0x%x = true := by decide +kernel"
                         % (t1, t2, lo, t1, t2, lo, hi, num(dg)))
            term = "unit_sound %d %d %d %d _ u_%d_%d_%d" % ((t1, t2) + segs[0][:2] + (t1, t2, segs[0][0]))
            for (lo, hi, dg) in segs[1:]:
                term = "rng_join (%s) (unit_sound %d %d %d %d _ u_%d_%d_%d)" % (term, t1, t2, lo, hi, t1, t2, lo)
            L.append("theorem q_%d_%d : Q %d %d := Q_of_rng (%s)\n" % (t1, t2, t1, t2, term))
        chain = "Q_lt_zero %d" % t1
        for t2 in t2s:
            chain = "Q_lt_succ (n := %d) (%s) q_%d_%d" % (t2, chain, t1, t2)
        if n == t1 + 1:
            L.append("theorem r_%d : R %d := R_of_full (t1 := %d) (%s)\n" % (t1, t1, t1, chain))
        else:
            assert Q < 2 * (1 + 8 * t1) + (1 + 8 * n) + 2
            L.append("theorem r_%d : R %d := R_of_cut (t1 := %d) (n := %d) (%s) (by decide)\n"
                     % (t1, t1, t1, n, chain))
        L.append("end LiuCert\n")
        with open(os.path.join(odir, "T%02d.lean" % t1), "w") as f:
            f.write("\n".join(L))
    A = []
    for t1 in t1s:
        A.append("import LiuIndex.Cert.T%02d" % t1)
    A.append("")
    A.append("/-! Assembly of the certificate: every box passes. -/")
    A.append("namespace LiuCert\nopen LiuCheck\n")
    chain = "R_lt_zero"
    for t1 in t1s:
        chain = "R_lt_succ (n := %d) (%s) r_%d" % (t1, chain, t1)
    A.append("theorem R_below : ∀ t1, t1 < %d → R t1 := %s\n" % (T, chain))
    A.append("theorem R_all : ∀ t1, R t1 := by")
    A.append("  intro t1")
    A.append("  by_cases h : t1 < %d" % T)
    A.append("  · exact R_below t1 h")
    A.append("  · exact R_vac (by simp only [q]; omega)\n")
    A.append("/-- Every sorted 4-tuple `a4 ≤ a3 ≤ a2 ≤ a1` with `2 a1 + a2 + a3 + a4 ≤ 1389` has a")
    A.append("witness `k`. -/")
    A.append("theorem witness (a1 a2 a3 a4 : Nat) (h4 : 1 ≤ a4) (h34 : a4 ≤ a3) (h23 : a3 ≤ a2)")
    A.append("    (h12 : a2 ≤ a1) (h0 : 2 * a1 + a2 + a3 + a4 ≤ 1389) :")
    A.append("    ∃ k, 2 ≤ k ∧ k ≤ 1387 ∧ 1 ≤ k * a1 % 1389 ∧ 1 ≤ k * a2 % 1389 ∧ 1 ≤ k * a3 % 1389 ∧")
    A.append("      1 ≤ k * a4 % 1389 ∧ k * a1 % 1389 + k * a2 % 1389 + k * a3 % 1389 + k * a4 % 1389 ≤ 1388 :=")
    A.append("  cover R_all a1 a2 a3 a4 h4 h34 h23 h12 h0\n")
    A.append("end LiuCert")
    with open(os.path.join(odir, "All.lean"), "w") as f:
        f.write("\n".join(A) + "\n")
    print("units", len(us), "files", T)

main()
