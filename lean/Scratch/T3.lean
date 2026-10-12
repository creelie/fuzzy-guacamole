import Mathlib

/-- Age of `k` for weights summing to 1389, in the floor form. -/
def age (a : Fin 5 → ℕ) (k : ℕ) : ℕ := k - ∑ i, k * a i / 1389

theorem age_eq_four_iff (a : Fin 5 → ℕ) (hs : ∑ i, a i = 1389) (k : ℕ) (hk : k ≤ 1389) :
    age a k = 4 ↔
      (∀ i, (1389 - k) * a i % 1389 ≠ 0) ∧ ∑ i, (1389 - k) * a i % 1389 = 1389 := by
  simp only [age, Fin.sum_univ_five, Fin.forall_fin_succ, Fin.forall_fin_zero_pi] at *
  simp only [Fin.sum_univ_five] at hs
  have hx : ∀ i, k * a i + (1389 - k) * a i = 1389 * a i := by
    intro i; rw [← Nat.add_mul, Nat.add_sub_cancel' hk]
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3; have h4 := hx 4
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
  sorry
