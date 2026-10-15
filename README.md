# A counterexample to Liu's conjecture on Fano indices in dimension four

Authors: Deep Bhattacharjee (corresponding author; ORCID 0000-0003-0466-750X;
itsdeep@live.com, d.bhattacharjee@erl-forschung.de) and Ushashi Bhattacharya
(ORCID 0009-0002-2254-3914; rai.bhattacharya.in@gmail.com).

The paper: [`preprintLiuFanoIndexConjecture/LiuFanoIndexConjecture.pdf`](preprintLiuFanoIndexConjecture/LiuFanoIndexConjecture.pdf).
Everything in one file: [`MasterLiuFanoIndexConjecture_masterzipfinal2.zip`](https://github.com/creelie/fuzzy-guacamole/raw/main/MasterLiuFanoIndexConjecture_masterzipfinal2.zip).

H. Liu (*On Fano indices of weighted projective spaces*,
[arXiv:2608.03434v3](https://arxiv.org/abs/2608.03434), Conjecture 4.2)
conjectured that, in each dimension n ≥ 2, three sets of integers coincide:

- I_{n,wps}: the Fano indices of n-dimensional well-formed weighted projective
  spaces with canonical singularities, together with 1, ..., n;
- I_{n,term}: the indices of n-dimensional terminal Calabi-Yau varieties;
- I_{n,loc}: the indices of n-dimensional log canonical singularities.

Liu proves this for n ≤ 3. This repository shows that it fails for n = 4.

**Theorem.** 1389 ∈ I_{4,term} ∩ I_{4,loc} and 1389 ∉ I_{4,wps}.

- Let F = x0^77 x1 + x1^67 x2 + x2^7 x0 + x3^3 + x4^2, weighted homogeneous of
  degree 78 for the weights (1, 1, 11, 26, 39), and let
  g = diag(ζ, ζ^1312, ζ^992, 1, 1) with ζ a primitive 1389th root of unity.
  Then F(gx) = F(x), det g = ζ^2305 has order 1389, and g^k fixes only points
  with x0 = x1 = x2 = 0 for 0 < k < 1389.
- **1389 ∈ I_{4,term}.** The quasi-smooth Calabi-Yau threefold
  X = {F = 0} ⊂ P(1,1,11,26,39) has K_X ~ 0, and g multiplies its
  holomorphic 3-form by det g. With a G-equivariant terminalization Z → X
  (Esser-Totaro-Wang, Prop. 2.2) and an elliptic curve E with a point p of
  order 1389, S = (Z × E)/μ_1389, acting by (z, e) ↦ (gz, e + p), is a terminal
  Calabi-Yau fourfold of index 1389.
- **1389 ∈ I_{4,loc}.** The cone C = {F = 0} ⊂ C^5 is log canonical and not
  klt (proved in the paper by a weighted blow-up), μ_1389 acts on C freely in
  codimension one, and C/μ_1389 is a four-dimensional log canonical, non-klt
  singularity of index 1389.
- **1389 ∉ I_{4,wps}.** Every a ∈ Z_{>0}^5 with a_0 + ... + a_4 = 1389 has
  age_a(k) = 4 for some k ∈ {2, ..., 1387}, so no well-formed P(a) of Fano
  index 1389 is canonical by Kasprzyk's criterion (arXiv:1304.3029,
  Prop. 2.5). This agrees with Liu's computer list (Zenodo
  [10.5281/zenodo.21806548](https://doi.org/10.5281/zenodo.21806548)), in which
  1389 is absent.

Read literally, I_{4,loc} contains every positive integer (C^4/μ_m with
weights (1,1,1,m−2) is klt of index m), so the conjecture is meant for log
canonical singularities that are not klt; the singularity above is not klt,
so the theorem refutes both readings.

## What is checked by Lean

The Lean 4 project in `lean/` (Lean v4.34.1, Mathlib v4.34.1) proves, with no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`:

```lean
-- I_{4,wps}, with Kasprzyk's criterion as the definition of "canonical"
def Iwps4 : Set ℕ :=
  {q | 1 ≤ q ∧ q ≤ 4} ∪
    {q | ∃ a : Fin 5 → ℕ, (∀ i, 0 < a i) ∧ WellFormed a ∧ ∑ i, a i = q ∧ KasprzykCanonical a}

theorem LiuIndex.exists_age_four (a : Fin 5 → ℕ) (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1389) :
    ∃ k, 2 ≤ k ∧ k ≤ 1387 ∧ age a k = 4
theorem LiuIndex.not_mem_Iwps4 : 1389 ∉ Iwps4

-- the algebra of F and g (Lemmas 2.1 and 2.2 of the paper)
theorem Liu1389.F_isWeightedHomogeneous : IsWeightedHomogeneous w F 78
theorem Liu1389.quasiSmooth (x : Fin 5 → ℂ) (h : ∀ i, eval x (pderiv i F) = 0) : x = 0
theorem Liu1389.F_invariant (ζ : ℂ) (hζ : ζ ^ 1389 = 1) (x : Fin 5 → ℂ) :
    eval (g ζ x) F = eval x F
theorem Liu1389.det_isPrimitiveRoot (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 1389) :
    IsPrimitiveRoot (ζ * ζ ^ 1312 * ζ ^ 992) 1389
theorem Liu1389.fixed_of_pow (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 1389) (k : ℕ) (hk0 : 0 < k)
    (hk : k < 1389) (x : Fin 5 → ℂ) (hx : (g ζ)^[k] x = x) : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0
```

`not_mem_Iwps4` rests on a certificate: the sorted 4-tuples
a4 ≤ a3 ≤ a2 ≤ a1 with 2a1 + a2 + a3 + a4 ≤ 1389 are covered by 368,253 boxes
of 8^4 points, each with a list of values k (2,624,293 in all). A checker
written in core Lean packs the 4096 points of a box into 17-bit lanes of one
natural number, and Lean proves that a box that passes has the required
witnesses (`LiuIndex/Check/Sound.lean`). The certificate is split into 4,022
theorems `run12 ... = true`, each proved by `decide +kernel`, so the Lean
kernel evaluates the checker itself; nothing compiled is trusted, and
`native_decide` is not used. The full build takes about 15 minutes on four
cores.

Not formalized, because Mathlib has no weighted projective spaces,
discrepancies or terminalizations: Kasprzyk's criterion (used as the
definition), the facts on weighted hypersurfaces (Iano-Fletcher), the
equivariant terminalization of Esser-Totaro-Wang, and the singularity theory
of Sections 2 to 4 of the paper, which is proved there by hand.

## Contents

| Path | Contents |
|---|---|
| `preprintLiuFanoIndexConjecture/` | the paper as a PDF, the only file in the folder |
| `paper/` | LaTeX source (`main.tex`, `amsart`), the figures as PNG and the compiled `main.pdf` |
| `figures/` | TikZ sources of the three schematic figures and `make_figures.sh`, which writes them to `paper/figures/` |
| `lean/LiuIndex/Algebra.lean` | F, g and their properties (Mathlib) |
| `lean/LiuIndex/Age.lean` | ages, Kasprzyk's criterion, `Iwps4`, the reduction to sorted 4-tuples (Mathlib) |
| `lean/LiuIndex/Check/` | the packed-lane checker and its soundness proof (core Lean) |
| `lean/LiuIndex/Cert/` | the certificate, 87 generated modules `T00` to `T86` and their assembly `All.lean` |
| `lean/LiuIndex/Main.lean` | `exists_age_four`, `not_kasprzykCanonical`, `not_mem_Iwps4` |
| `lean/Axioms.lean` | prints the axioms of the main theorems |
| `lean/generate/` | the certificate generator (`gen6.c`, `mkunits.py`, `gen_cert.py`, `gen_defs.py`) and `regenerate.sh`, which rebuilds the certificate from scratch and compares it with the committed files |
| `code/` | exhaustive search over all 1,301,769,806 partitions of 1389 into five parts, in C (`c/`), C++ (`cpp/`), Julia (`julia/`) and Python (`python/`) |
| `results/` | outputs of the four searches (`canonical=0` at q = 1389) and the control q = 1383, which finds the canonical P(674, 461, 195, 35, 18) |
| `scripts/run_all.sh` | regenerates the certificate, builds the Lean project, checks the axioms and runs all searches |
| `scripts/build_paper.sh` | builds the files in `dist/`, the preprint folder and the master zip |
| `journal/JOURNAL.md` | target journal (Proceedings of the AMS), format rules and AI policy |
| `dist/` | `LiuFanoIndexConjecture_final2.pdf`, the anonymized `_final2-anonymous.pdf` for review, the LaTeX source zip `_final2-tex.zip` (with the figures as PNG) and the arXiv tarball `_final2-arxiv.tar.gz` |
| `MasterLiuFanoIndexConjecture_masterzipfinal2.zip` | every file of the repository with `dist/` and the preprint folder |
| `.github/workflows/` | `verify.yml` (the Lean kernel check, the four searches and the paper on every pull request) and `release.yml` (runs the checks and publishes a release) |

## Running the checks

```sh
bash scripts/run_all.sh              # everything
SKIP_LEAN=1 bash scripts/run_all.sh  # the four searches only
bash lean/generate/regenerate.sh     # certificate only
cd lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

Tools: elan (the toolchain is pinned in `lean/lean-toolchain`), gcc with
OpenMP, g++ (C++17), Julia, Python 3 with NumPy, and pdflatex for the paper.

## Archive

Zenodo, all versions: [10.5281/zenodo.23319498](https://doi.org/10.5281/zenodo.23319498);
release v1.0.0: [10.5281/zenodo.23319499](https://doi.org/10.5281/zenodo.23319499).
Release v2.0.0 (two authors, figures, the declarations of the journal and the
preprint folder) gets its DOI when it is published.

## License

MIT (see `LICENSE`).
