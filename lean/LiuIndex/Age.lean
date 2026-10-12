import Mathlib

/-!
# Ages of weighted projective 4-spaces

For positive weights `a : Fin 5 → ℕ` with `q = ∑ aᵢ`, the age of `k` is
`k - ∑ ⌊k aᵢ / q⌋`, the sum of the fractional parts of `k aᵢ / q`. By Kasprzyk's
criterion [Kasprzyk, *Classifying terminal weighted projective space*, Prop. 2.5], a
well-formed `ℙ(a)` has canonical singularities if and only if every `k ∈ [2, q - 2]` has age
in `{1, 2, 3}`.

This file reduces the claim "every `a` with `∑ aᵢ = 1389` has some `k ∈ [2, 1387]` of
age `4`" to a statement about sorted 4-tuples (`exists_age_four_of_sorted`), which the
certificate proves.
-/

namespace LiuIndex

/-- The age of `k` for the weights `a`. -/
def age (a : Fin 5 → ℕ) (k : ℕ) : ℕ := k - ∑ i, k * a i / ∑ j, a j

/-- Kasprzyk's criterion for canonical singularities of `ℙ(a)`. -/
def KasprzykCanonical (a : Fin 5 → ℕ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ (∑ i, a i) - 2 → 1 ≤ age a k ∧ age a k ≤ 3

/-- `ℙ(a)` is well formed: any four of the five weights are coprime. -/
def WellFormed (a : Fin 5 → ℕ) : Prop := ∀ i, (Finset.univ.erase i).gcd a = 1

/-- The Fano indices of 4-dimensional well-formed weighted projective spaces with canonical
singularities, together with `1, …, 4`. -/
def Iwps4 : Set ℕ :=
  {q | 1 ≤ q ∧ q ≤ 4} ∪
    {q | ∃ a : Fin 5 → ℕ, (∀ i, 0 < a i) ∧ WellFormed a ∧ ∑ i, a i = q ∧ KasprzykCanonical a}

theorem age_perm (a : Fin 5 → ℕ) (σ : Equiv.Perm (Fin 5)) (k : ℕ) :
    age (a ∘ σ) k = age a k := by
  simp only [age, Function.comp_apply]
  rw [Equiv.sum_comp σ a, Equiv.sum_comp σ (fun i => k * a i / ∑ j, a j)]

/-- A witness on four of the weights gives age `4` at `1389 - k`. -/
theorem age_eq_four (a : Fin 5 → ℕ) (hs : ∑ i, a i = 1389) (k : ℕ) (hk : k ≤ 1389)
    (h0 : 1 ≤ k * a 0 % 1389) (h1 : 1 ≤ k * a 1 % 1389) (h2 : 1 ≤ k * a 2 % 1389)
    (h3 : 1 ≤ k * a 3 % 1389)
    (hsum : k * a 0 % 1389 + k * a 1 % 1389 + k * a 2 % 1389 + k * a 3 % 1389 ≤ 1388) :
    age a (1389 - k) = 4 := by
  unfold age
  rw [hs, Fin.sum_univ_five]
  rw [Fin.sum_univ_five] at hs
  have hx : ∀ i, k * a i + (1389 - k) * a i = 1389 * a i := by
    intro i; rw [← Nat.add_mul, Nat.add_sub_cancel' hk]
  have e0 := hx 0; have e1 := hx 1; have e2 := hx 2; have e3 := hx 3; have e4 := hx 4
  have hk0 : k * a 0 + k * a 1 + k * a 2 + k * a 3 + k * a 4 = 1389 * k := by
    rw [← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, hs, Nat.mul_comm]
  clear hx
  generalize k * a 0 = x0 at *
  generalize k * a 1 = x1 at *
  generalize k * a 2 = x2 at *
  generalize k * a 3 = x3 at *
  generalize k * a 4 = x4 at *
  generalize (1389 - k) * a 0 = y0 at *
  generalize (1389 - k) * a 1 = y1 at *
  generalize (1389 - k) * a 2 = y2 at *
  generalize (1389 - k) * a 3 = y3 at *
  generalize (1389 - k) * a 4 = y4 at *
  have dx0 := Nat.div_add_mod x0 1389; have mx0 := Nat.mod_lt x0 (show 1389 > 0 by decide)
  have dx1 := Nat.div_add_mod x1 1389; have mx1 := Nat.mod_lt x1 (show 1389 > 0 by decide)
  have dx2 := Nat.div_add_mod x2 1389; have mx2 := Nat.mod_lt x2 (show 1389 > 0 by decide)
  have dx3 := Nat.div_add_mod x3 1389; have mx3 := Nat.mod_lt x3 (show 1389 > 0 by decide)
  have dx4 := Nat.div_add_mod x4 1389; have mx4 := Nat.mod_lt x4 (show 1389 > 0 by decide)
  have dy0 := Nat.div_add_mod y0 1389; have my0 := Nat.mod_lt y0 (show 1389 > 0 by decide)
  have dy1 := Nat.div_add_mod y1 1389; have my1 := Nat.mod_lt y1 (show 1389 > 0 by decide)
  have dy2 := Nat.div_add_mod y2 1389; have my2 := Nat.mod_lt y2 (show 1389 > 0 by decide)
  have dy3 := Nat.div_add_mod y3 1389; have my3 := Nat.mod_lt y3 (show 1389 > 0 by decide)
  have dy4 := Nat.div_add_mod y4 1389; have my4 := Nat.mod_lt y4 (show 1389 > 0 by decide)
  generalize x0 / 1389 = u0 at *; generalize x0 % 1389 = r0 at *
  generalize x1 / 1389 = u1 at *; generalize x1 % 1389 = r1 at *
  generalize x2 / 1389 = u2 at *; generalize x2 % 1389 = r2 at *
  generalize x3 / 1389 = u3 at *; generalize x3 % 1389 = r3 at *
  generalize x4 / 1389 = u4 at *; generalize x4 % 1389 = r4 at *
  generalize y0 / 1389 = v0 at *; generalize y0 % 1389 = s0 at *
  generalize y1 / 1389 = v1 at *; generalize y1 % 1389 = s1 at *
  generalize y2 / 1389 = v2 at *; generalize y2 % 1389 = s2 at *
  generalize y3 / 1389 = v3 at *; generalize y3 % 1389 = s3 at *
  generalize y4 / 1389 = v4 at *; generalize y4 % 1389 = s4 at *
  subst dx0 dx1 dx2 dx3 dx4 dy0 dy1 dy2 dy3 dy4
  omega

/-- If every sorted 4-tuple `a₄ ≤ a₃ ≤ a₂ ≤ a₁` with `2a₁ + a₂ + a₃ + a₄ ≤ 1389` has a witness,
then every 5-tuple of positive weights with sum `1389` has some `k ∈ [2, 1387]` of age `4`. -/
theorem exists_age_four_of_sorted
    (W : ∀ a1 a2 a3 a4 : ℕ, 1 ≤ a4 → a4 ≤ a3 → a3 ≤ a2 → a2 ≤ a1 →
      2 * a1 + a2 + a3 + a4 ≤ 1389 →
      ∃ k, 2 ≤ k ∧ k ≤ 1387 ∧ 1 ≤ k * a1 % 1389 ∧ 1 ≤ k * a2 % 1389 ∧ 1 ≤ k * a3 % 1389 ∧
        1 ≤ k * a4 % 1389 ∧ k * a1 % 1389 + k * a2 % 1389 + k * a3 % 1389 + k * a4 % 1389 ≤ 1388)
    (a : Fin 5 → ℕ) (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1389) :
    ∃ k, 2 ≤ k ∧ k ≤ 1387 ∧ age a k = 4 := by
  have hm : Monotone (a ∘ Tuple.sort a) := Tuple.monotone_sort a
  have hcs : ∑ i, (a ∘ Tuple.sort a) i = 1389 := by
    simp only [Function.comp_apply]; rw [Equiv.sum_comp (Tuple.sort a) a]; exact hs
  generalize hc : a ∘ Tuple.sort a = c at hm hcs
  have h01 : c 0 ≤ c 1 := hm (by decide)
  have h12 : c 1 ≤ c 2 := hm (by decide)
  have h23 : c 2 ≤ c 3 := hm (by decide)
  have h34 : c 3 ≤ c 4 := hm (by decide)
  have hpos : 1 ≤ c 0 := by rw [← hc]; exact ha _
  have hcs' := hcs
  rw [Fin.sum_univ_five] at hcs'
  obtain ⟨k, hk2, hk, r3, r2, r1, r0, rs⟩ := W (c 3) (c 2) (c 1) (c 0) hpos h01 h12 h23 (by omega)
  refine ⟨1389 - k, by omega, by omega, ?_⟩
  rw [← age_perm a (Tuple.sort a), hc]
  exact age_eq_four c hcs k (by omega) r0 r1 r2 r3 (by omega)

/-- With the hypothesis of `exists_age_four_of_sorted`, `1389 ∉ Iwps4`. -/
theorem not_mem_Iwps4_of_sorted
    (W : ∀ a1 a2 a3 a4 : ℕ, 1 ≤ a4 → a4 ≤ a3 → a3 ≤ a2 → a2 ≤ a1 →
      2 * a1 + a2 + a3 + a4 ≤ 1389 →
      ∃ k, 2 ≤ k ∧ k ≤ 1387 ∧ 1 ≤ k * a1 % 1389 ∧ 1 ≤ k * a2 % 1389 ∧ 1 ≤ k * a3 % 1389 ∧
        1 ≤ k * a4 % 1389 ∧ k * a1 % 1389 + k * a2 % 1389 + k * a3 % 1389 + k * a4 % 1389 ≤ 1388) :
    1389 ∉ Iwps4 := by
  rintro (⟨_, h⟩ | ⟨a, ha, _, hs, hcan⟩)
  · omega
  · obtain ⟨k, hk2, hk, h4⟩ := exists_age_four_of_sorted W a ha hs
    have := (hcan k hk2 (by rw [hs]; exact hk)).2
    omega

end LiuIndex
