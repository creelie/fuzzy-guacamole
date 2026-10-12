# Parked: a candidate counterexample to Liu's index conjecture in dimension 4

Status: parked, not released. Nothing here is Lean-verified. The arithmetic
facts below are checked by exhaustive computer search, and the geometric
steps rest on cited theorems.

## The conjecture

H. Liu, *On Fano indices of weighted projective spaces*, arXiv:2608.03434
(v3, 7 Oct 2026), Conjecture 4.2:
I_{n,wps} = I_{n,term} = I_{n,loc} for every n >= 2.

- I_{n,wps}: the Fano indices of n-dimensional well-formed weighted projective
  spaces with canonical singularities, together with {1, ..., n}.
- I_{n,term}: the indices of n-dimensional terminal Calabi-Yau varieties.
- I_{n,loc}: the indices of n-dimensional log canonical singularities. Read
  literally this includes klt quotient singularities, whose indices are
  unbounded, so the intended reading is "lc, not klt".

## The candidate: index 1389

1. Let F = x0^77 x1 + x1^67 x2 + x2^7 x0 + x3^3 + x4^2, an invertible
   polynomial of degree 78 with weights (1, 1, 11, 26, 39). These weights add
   up to 78, so X = {F = 0} in P(1,1,11,26,39) is a quasi-smooth Calabi-Yau
   threefold with K_X ~ 0 and canonical singularities.
   - Quasi-smoothness: on the critical locus, x0*dF/dx0, x1*dF/dx1 and
     x2*dF/dx2 give a linear system for the three loop monomials whose
     determinant is 77*67*7 + 1 = 36114, which is nonzero.
2. The diagonal symmetry group G_F modulo the trivially acting subgroup J is
   cyclic of order 2778.
   - The determinant character maps G_F/J isomorphically onto mu_2778. Its
     image has order 2778, the degree of the transpose polynomial
     x0^77 x2 + x1^67 x0 + x2^7 x1 + x3^3 + x4^2, which has weights
     (31, 41, 391, 926, 1389).
   - So the subgroup mu_1389 acts on H^{3,0}(X) faithfully.
3. Index 1389 is realised in I_{4,term}. Take a mu_1389-equivariant
   terminalisation Z of X (Esser-Totaro-Wang, "Calabi-Yau varieties of large index", arXiv:2209.04597, the proposition on equivariant terminalisations), an elliptic curve
   E, and a point p of order 1389 on E. Then (Z x E)/mu_1389 is a terminal
   Calabi-Yau 4-fold of index 1389, by the argument of the corollary constructing terminal Calabi-Yau varieties of large index in the same paper.
4. Index 1389 is also realised in I_{4,loc}.
   - The subgroup of order 1389 of the loop part of G_F acts on the cone
     {F = 0} in C^5 freely in codimension one.
   - The quotient is therefore an lc, non-klt 4-dimensional singularity of
     index 1389.
5. 1389 is not in I_{4,wps}.
   - `search.c` enumerates all 1,301,769,806 sorted 5-tuples with sum 1389.
     None is well-formed and canonical under Kasprzyk's age criterion.
   - This agrees with Liu's published list (Zenodo 10.5281/zenodo.21806548).

Among all 27,865 invertible Calabi-Yau polynomials in five variables
(`inv.py`, run on the Kreuzer-Skarke list `w5.ip.gz`), 1389 is the only
divisor of a transpose degree that lies outside I_{4,wps} (`check.py`).

## Why parked

The project bar requires a famous problem and a complete Lean formalisation
of the main theorem. Liu's conjecture is recent and not of that stature.
Mathlib cannot yet express terminal Calabi-Yau varieties. Proving
1389 notin I_{4,wps} in the Lean kernel would need a certificate of
roughly 10^8 cases.

## Files

| File | Purpose |
|---|---|
| `inv.py` | Enumerates invertible CY polynomials in five variables and computes the transpose degrees |
| `iwps.py` | Loads Liu's list and confirms that every h < 100 is in I_{4,wps} |
| `check.py` | Lists the transpose-degree divisors that lie outside I_{4,wps} |
| `search.c` | Exhaustive search for canonical well-formed 5-tuples with a given sum; run `gcc -O3 -fopenmp search.c -o search && ./search 1389` |
