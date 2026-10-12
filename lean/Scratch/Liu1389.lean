import Mathlib

/-!
# The finite algebra behind index 1389

`F = x₀⁷⁷x₁ + x₁⁶⁷x₂ + x₂⁷x₀ + x₃³ + x₄²` is weighted homogeneous of degree 78
for the weights `(1, 1, 11, 26, 39)`, whose sum is 78. This file proves:

* `F_isWeightedHomogeneous`, `weights_sum`: the Calabi–Yau degree condition.
* `wellFormed_P`, `wellFormed_X`: the gcd conditions for well-formedness of
  `ℙ(1,1,11,26,39)` and of the hypersurface `X₇₈`.
* `quasiSmooth`: the partial derivatives of `F` vanish simultaneously only at `0`.
* `F_invariant`: `g = diag(ζ, ζ¹³¹², ζ⁹⁹², 1, 1)` preserves `F` when `ζ¹³⁸⁹ = 1`.
* `det_isPrimitiveRoot`: for a primitive 1389th root of unity `ζ`, `det g` is again
  a primitive 1389th root of unity.
* `fixed_of_pow`: for `0 < k < 1389`, every fixed point of `gᵏ` in `ℂ⁵` has
  `x₀ = x₁ = x₂ = 0`.
-/

open MvPolynomial

namespace Liu1389

/-- The weights of `ℙ(1,1,11,26,39)`. -/
def w : Fin 5 → ℕ := ![1, 1, 11, 26, 39]

/-- The invertible polynomial of degree 78. -/
noncomputable def F : MvPolynomial (Fin 5) ℂ :=
  X 0 ^ 77 * X 1 + X 1 ^ 67 * X 2 + X 2 ^ 7 * X 0 + X 3 ^ 3 + X 4 ^ 2

theorem weights_sum : ∑ i, w i = 78 := by
  simp [w, Fin.sum_univ_five]

theorem F_isWeightedHomogeneous : IsWeightedHomogeneous w F 78 := by
  have hX : ∀ i, IsWeightedHomogeneous w (X i : MvPolynomial (Fin 5) ℂ) (w i) :=
    fun i => isWeightedHomogeneous_X ℂ w i
  have h1 : IsWeightedHomogeneous w (X 0 ^ 77 * X 1 : MvPolynomial (Fin 5) ℂ) 78 := by
    have := ((hX 0).pow 77).mul (hX 1)
    simpa [w] using this
  have h2 : IsWeightedHomogeneous w (X 1 ^ 67 * X 2 : MvPolynomial (Fin 5) ℂ) 78 := by
    have := ((hX 1).pow 67).mul (hX 2)
    simpa [w] using this
  have h3 : IsWeightedHomogeneous w (X 2 ^ 7 * X 0 : MvPolynomial (Fin 5) ℂ) 78 := by
    have := ((hX 2).pow 7).mul (hX 0)
    simpa [w] using this
  have h4 : IsWeightedHomogeneous w (X 3 ^ 3 : MvPolynomial (Fin 5) ℂ) 78 := by
    have := (hX 3).pow 3
    simpa [w] using this
  have h5 : IsWeightedHomogeneous w (X 4 ^ 2 : MvPolynomial (Fin 5) ℂ) 78 := by
    have := (hX 4).pow 2
    simpa [w] using this
  exact (((h1.add h2).add h3).add h4).add h5

/-- `ℙ(w)` is well formed: any four of the five weights are coprime. -/
theorem wellFormed_P : ∀ i : Fin 5,
    (Finset.univ.erase i).gcd w = 1 := by
  decide

/-- `X₇₈ ⊂ ℙ(w)` is well formed: any three of the weights are coprime, so their
gcd divides the degree 78. -/
theorem wellFormed_X : ∀ i j : Fin 5, i ≠ j →
    ((Finset.univ.erase i).erase j).gcd w = 1 := by
  decide

/-- The singular locus of the affine cone `{F = 0} ⊂ ℂ⁵` is the origin. -/
theorem quasiSmooth (x : Fin 5 → ℂ) (h : ∀ i, eval x (pderiv i F) = 0) : x = 0 := by
  have e0 := h 0
  have e1 := h 1
  have e2 := h 2
  have e3 := h 3
  have e4 := h 4
  simp [F] at e0 e1 e2 e3 e4
  have h3 : x 3 = 0 := e3
  have h4 : x 4 = 0 := e4
  have hm : (36114 : ℂ) * (x 2 ^ 7 * x 0) = 0 := by
    linear_combination x 0 * e0 - 77 * x 1 * e1 + 5159 * x 2 * e2
  have hm' : x 2 ^ 7 * x 0 = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · norm_num at h
    · exact h
  have h012 : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
    rcases mul_eq_zero.mp hm' with h | h
    · have hx2 : x 2 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h
      have hx0 : x 0 = 0 := by
        have : x 0 ^ 77 = 0 := by linear_combination e1 - 67 * x 1 ^ 66 * hx2
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hx1 : x 1 = 0 := by
        have : x 1 ^ 67 = 0 := by linear_combination e2 - 7 * x 0 * x 2 ^ 5 * hx2
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      exact ⟨hx0, hx1, hx2⟩
    · have hx0 : x 0 = 0 := h
      have hx2 : x 2 = 0 := by
        have : x 2 ^ 7 = 0 := by linear_combination e0 - 77 * x 0 ^ 75 * x 1 * hx0
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hx1 : x 1 = 0 := by
        have : x 1 ^ 67 = 0 := by linear_combination e2 - 7 * x 2 ^ 6 * hx0
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      exact ⟨hx0, hx1, hx2⟩
  funext i
  fin_cases i
  · exact h012.1
  · exact h012.2.1
  · exact h012.2.2
  · exact h3
  · exact h4

/-- The diagonal symmetry `g = diag(ζ, ζ¹³¹², ζ⁹⁹², 1, 1)`. -/
def g (ζ : ℂ) (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![ζ * x 0, ζ ^ 1312 * x 1, ζ ^ 992 * x 2, x 3, x 4]

theorem F_invariant (ζ : ℂ) (hζ : ζ ^ 1389 = 1) (x : Fin 5 → ℂ) :
    eval (g ζ x) F = eval x F := by
  simp [F, g]
  have a : (ζ * x 0) ^ 77 * (ζ ^ 1312 * x 1) = ζ ^ 1389 * (x 0 ^ 77 * x 1) := by ring
  have b : (ζ ^ 1312 * x 1) ^ 67 * (ζ ^ 992 * x 2) = (ζ ^ 1389) ^ 64 * (x 1 ^ 67 * x 2) := by
    ring
  have c : (ζ ^ 992 * x 2) ^ 7 * (ζ * x 0) = (ζ ^ 1389) ^ 5 * (x 2 ^ 7 * x 0) := by ring
  rw [a, b, c, hζ]
  ring

/-- `det g = ζ · ζ¹³¹² · ζ⁹⁹² = ζ²³⁰⁵`, and `gcd(2305, 1389) = 1`. -/
theorem det_isPrimitiveRoot (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 1389) :
    IsPrimitiveRoot (ζ * ζ ^ 1312 * ζ ^ 992) 1389 := by
  have : ζ * ζ ^ 1312 * ζ ^ 992 = ζ ^ 2305 := by ring
  rw [this]
  exact hζ.pow_of_coprime 2305 (by norm_num)

/-- A primitive 1389th root of unity exists in `ℂ`. -/
theorem exists_primitive : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 1389)) 1389 :=
  Complex.isPrimitiveRoot_exp 1389 (by norm_num)

/-- The `k`-th power of `g`. -/
def gpow (ζ : ℂ) (k : ℕ) (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![ζ ^ k * x 0, ζ ^ (1312 * k) * x 1, ζ ^ (992 * k) * x 2, x 3, x 4]

theorem gpow_eq_iterate (ζ : ℂ) (k : ℕ) : gpow ζ k = (g ζ)^[k] := by
  induction k with
  | zero =>
    funext x i
    fin_cases i <;> simp [gpow]
  | succ k ih =>
    rw [Function.iterate_succ', ← ih]
    funext x i
    fin_cases i <;> simp [gpow, g] <;> ring

/-- For `0 < k < 1389`, a fixed point of `gᵏ` has `x₀ = x₁ = x₂ = 0`; so the fixed
locus of every nontrivial element of `⟨g⟩` on the cone `{F = 0}` is the curve
`{x₀ = x₁ = x₂ = 0, x₃³ + x₄² = 0}`, of codimension 3 in the cone. -/
theorem fixed_of_pow (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 1389) (k : ℕ) (hk0 : 0 < k)
    (hk : k < 1389) (x : Fin 5 → ℂ) (hx : (g ζ)^[k] x = x) :
    x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
  rw [← gpow_eq_iterate] at hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  simp only [gpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  have notdvd : ¬ 1389 ∣ k := fun h => absurd (Nat.le_of_dvd hk0 h) (by omega)
  have key : ∀ (m : ℕ), Nat.Coprime m 1389 → ∀ y : ℂ, ζ ^ (m * k) * y = y → y = 0 := by
    intro m hm y hy
    by_contra hy0
    have : ζ ^ (m * k) = 1 := by
      have := congrArg (· / y) hy
      simpa [hy0] using this
    have hd : 1389 ∣ m * k := hζ.dvd_of_pow_eq_one _ this
    exact notdvd ((Nat.Coprime.symm hm).dvd_of_dvd_mul_left hd)
  refine ⟨key 1 (by norm_num) (x 0) (by simpa using h0), key 1312 (by norm_num) (x 1) h1,
    key 992 (by norm_num) (x 2) h2⟩

end Liu1389
