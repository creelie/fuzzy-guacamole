**A counterexample to Liu's conjecture on Fano indices in dimension four**, by Deep Bhattacharjee.

H. Liu ([arXiv:2608.03434](https://arxiv.org/abs/2608.03434), Conjecture 4.2) conjectured that, in each dimension n ≥ 2, the Fano indices of canonical weighted projective n-spaces (with 1, …, n), the indices of terminal Calabi–Yau n-folds and the indices of n-dimensional log canonical singularities form the same set. The paper shows that this fails for n = 4:

**Theorem.** 1389 ∈ I_{4,term} ∩ I_{4,loc} and 1389 ∉ I_{4,wps}.

| Step | Content |
|---|---|
| Lemmas 2.1–2.3 | F = x0^77 x1 + x1^67 x2 + x2^7 x0 + x3^3 + x4^2 in P(1,1,11,26,39) is quasi-smooth of degree 78; g = diag(ζ, ζ^1312, ζ^992, 1, 1) preserves F, det g has order 1389, and g multiplies the 3-form of X = {F = 0} by det g |
| Proposition 3.1 | (Z × E)/μ_1389, with Z → X an equivariant terminalization, is a terminal Calabi–Yau fourfold of index 1389 |
| Lemma 4.1, Proposition 4.2 | the cone {F = 0} is log canonical and not klt; its quotient by μ_1389 is a log canonical, non-klt singularity of index 1389 |
| Lemma 5.1, Proposition 5.2, Theorem 5.3 | every a ∈ Z_{>0}^5 with sum 1389 has age_a(k) = 4 for some k ∈ [2, 1387], so no well-formed P(a) of Fano index 1389 is canonical (Kasprzyk's criterion) |

Lean 4 with Mathlib proves 1389 ∉ I_{4,wps} (`LiuIndex.not_mem_Iwps4`, with Kasprzyk's criterion as the definition) and the algebraic lemmas on F and g; every theorem depends only on the axioms propext, Classical.choice and Quot.sound. The finite part is a certificate of 4,022 units, each proved by `decide +kernel`, so the kernel evaluates the checker; `native_decide` is not used. The geometric steps (Kasprzyk's criterion, weighted hypersurfaces, equivariant terminalization, singularities) rest on the cited literature and are proved by hand in the paper. Independent checks: exhaustive searches over all 1,301,769,806 partitions of 1389 into five parts in C, C++, Julia and Python.

Files:
- `dist/liu-index-1389.pdf`: the paper
- `dist/liu-index-1389-anonymous.pdf`: the anonymized version for double-anonymous review
- `dist/liu-index-1389-tex.zip`: LaTeX source (`main.tex`)
- `dist/liu-index-1389-arxiv.tar.gz`: the same source, ready for arXiv
- `dist/MasterLiuIndexConjectureZip.zip`: every file of the repository with the four files above

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
