// Exhaustive search for well-formed weighted projective 4-spaces
// P(a1,...,a5) with canonical singularities and Fano index q = a1+...+a5.
//
// Canonicity is tested with Kasprzyk's criterion in its symmetric form:
// P(a) is NOT canonical iff there is k in [2, q-2] such that no a_i*k is
// divisible by q and the residues (a_i*k mod q) add up to exactly q
// (that is, age(k) = 1, equivalently age(q-k) = 4).  The residues are
// updated incrementally, so this program shares no arithmetic with the
// floor-division implementations in C, Python and Julia.
//
// Usage: wps_search q [threads]
#include <cstdio>
#include <cstdlib>
#include <thread>
#include <vector>
#include <mutex>
#include <atomic>
#include <algorithm>
#include <numeric>

static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }

int main(int argc, char** argv) {
  if (argc < 2) { std::fprintf(stderr, "usage: %s q [threads]\n", argv[0]); return 2; }
  const long q = std::atol(argv[1]);
  const int T = argc > 2 ? std::atoi(argv[2]) : (int)std::max(1u, std::thread::hardware_concurrency());
  std::atomic<long> next(1);
  std::mutex mu;
  long tuples = 0, wellformed = 0;
  std::vector<std::vector<long>> canonical;
  auto work = [&]() {
    long lt = 0, lw = 0;
    std::vector<std::vector<long>> lc;
    for (;;) {
      long a5 = next.fetch_add(1);           // smallest weight
      if (5 * a5 > q) break;
      for (long a4 = a5; a5 + 4 * a4 <= q; a4++)
        for (long a3 = a4; a5 + a4 + 3 * a3 <= q; a3++)
          for (long a2 = a3; a5 + a4 + a3 + 2 * a2 <= q; a2++) {
            long a1 = q - a5 - a4 - a3 - a2;   // a1 >= a2 by the loop bound
            lt++;
            long a[5] = {a1, a2, a3, a4, a5};
            long pre[6], suf[6];
            pre[0] = 0; for (int i = 0; i < 5; i++) pre[i + 1] = gcdl(pre[i], a[i]);
            suf[5] = 0; for (int i = 4; i >= 0; i--) suf[i] = gcdl(suf[i + 1], a[i]);
            bool wf = true;
            for (int i = 0; i < 5; i++) if (gcdl(pre[i], suf[i + 1]) != 1) { wf = false; break; }
            if (!wf) continue;
            lw++;
            long r[5];
            for (int i = 0; i < 5; i++) r[i] = a[i] % q;   // residues for k = 1
            bool canon = true;
            for (long k = 2; k <= q - 2; k++) {
              long s = 0; bool zero = false;
              for (int i = 0; i < 5; i++) {
                r[i] += a[i]; if (r[i] >= q) r[i] -= q;
                s += r[i]; zero |= (r[i] == 0);
              }
              if (!zero && s == q) { canon = false; break; }
            }
            if (canon) lc.push_back({a1, a2, a3, a4, a5});
          }
    }
    std::lock_guard<std::mutex> g(mu);
    tuples += lt; wellformed += lw;
    for (auto& v : lc) canonical.push_back(v);
  };
  std::vector<std::thread> th;
  for (int t = 0; t < T; t++) th.emplace_back(work);
  for (auto& t : th) t.join();
  std::sort(canonical.begin(), canonical.end());
  for (auto& v : canonical) std::printf("canonical %ld %ld %ld %ld %ld\n", v[0], v[1], v[2], v[3], v[4]);
  std::printf("q=%ld tuples=%ld wellformed=%ld canonical=%zu\n", q, tuples, wellformed, canonical.size());
  return 0;
}
