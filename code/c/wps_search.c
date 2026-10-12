/* Exhaustive search for well-formed weighted projective 4-spaces
 * P(a1,...,a5) with canonical singularities and Fano index q = a1+...+a5.
 *
 * Kasprzyk's criterion: P(a) is canonical iff age(k) != 4 for every
 * k in [2, q-2], where age(k) = k - sum_i floor(k*a_i/q).
 * Tuples are enumerated with a1 >= a2 >= a3 >= a4 >= a5 >= 1.
 *
 * Build: gcc -O2 -fopenmp wps_search.c -o wps_search
 * Usage: ./wps_search q
 */
#include <stdio.h>
#include <stdlib.h>

static long gcd(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s q\n", argv[0]); return 2; }
  long q = atol(argv[1]);
  long tuples = 0, wellformed = 0, canonical = 0;
#pragma omp parallel for schedule(dynamic, 1) reduction(+ : tuples, wellformed, canonical)
  for (long a1 = q - 4; a1 >= 1; a1--) {
    for (long a2 = a1; a2 >= 1; a2--) {
      long r2 = q - a1 - a2;
      if (r2 < 3) continue;
      if (4 * a2 < q - a1) break;
      for (long a3 = (a2 < r2 - 2 ? a2 : r2 - 2); a3 >= 1; a3--) {
        long r3 = r2 - a3;
        if (3 * a3 < r2) break;
        for (long a4 = (a3 < r3 - 1 ? a3 : r3 - 1); a4 >= 1; a4--) {
          long a5 = r3 - a4;
          if (a5 > a4) break;
          tuples++;
          long a[5] = {a1, a2, a3, a4, a5};
          int ok = 1;
          for (int i = 0; i < 5 && ok; i++) {
            long G = 0;
            for (int j = 0; j < 5; j++) if (j != i) G = gcd(G, a[j]);
            if (G != 1) ok = 0;
          }
          if (!ok) continue;
          wellformed++;
          for (long k = 2; k <= q - 2; k++) {
            long s = 0;
            for (int i = 0; i < 5; i++) s += (k * a[i]) / q;
            if (k - s == 4) { ok = 0; break; }
          }
          if (ok) {
            canonical++;
#pragma omp critical
            printf("canonical %ld %ld %ld %ld %ld\n", a1, a2, a3, a4, a5);
          }
        }
      }
    }
  }
  printf("q=%ld tuples=%ld wellformed=%ld canonical=%ld\n", q, tuples, wellformed, canonical);
  return 0;
}
