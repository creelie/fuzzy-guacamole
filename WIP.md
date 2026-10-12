# Work in progress (paused, not released)

Counterexample to Liu's index conjecture (arXiv:2608.03434, Conjecture 4.2) in dimension 4:
1389 lies in I_{4,term} and I_{4,loc} but not in I_{4,wps}.

## Done
- `code/`: exhaustive search over all sorted 5-tuples with sum 1389 in C, C++, Julia and Python.
  All four report `q=1389 tuples=1301769806 wellformed=874763737 canonical=0` (`results/full_*.out`).
  Control: q = 1383 finds the canonical tuple (674, 461, 195, 35, 18) (`results/control_q1383_c.out`).
- `lean/Scratch/Liu1389.lean` compiles against Mathlib v4.34.1 with only the axioms
  propext, Classical.choice, Quot.sound (`lean/Scratch/Ax.lean` prints them): weights, weighted
  homogeneity, well-formedness, quasi-smoothness, invariance under g, the order-1389 character
  and the fixed locus of g^k.

## Not done
- `lean/Scratch/T3.lean` (agreement of the two forms of Kasprzyk's test) still ends in `sorry`.
- Non-membership 1389 notin I_{4,wps} is checked by the four programs, not in the Lean kernel.
- Paper (amsart, Proceedings of the AMS), journal-details file, `run_all.sh`, README, release.
