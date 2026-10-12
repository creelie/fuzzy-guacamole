import LiuIndex.Age
import LiuIndex.Cert.All

/-!
# `1389 ∉ I_{4,wps}`

No 5-tuple of positive integers with sum `1389` passes Kasprzyk's criterion for canonical
singularities: every such tuple has some `k ∈ [2, 1387]` of age `4`. The sorted 4-tuple
statement `LiuCert.witness` is proved by the kernel-checked certificate in `LiuIndex.Cert`.
-/

namespace LiuIndex

/-- Every 5-tuple of positive weights with sum `1389` has some `k ∈ [2, 1387]` of age `4`. -/
theorem exists_age_four (a : Fin 5 → ℕ) (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1389) :
    ∃ k, 2 ≤ k ∧ k ≤ 1387 ∧ age a k = 4 :=
  exists_age_four_of_sorted LiuCert.witness a ha hs

/-- No weighted projective 4-space of Fano index `1389` passes Kasprzyk's criterion. -/
theorem not_kasprzykCanonical (a : Fin 5 → ℕ) (ha : ∀ i, 0 < a i) (hs : ∑ i, a i = 1389) :
    ¬ KasprzykCanonical a := by
  intro hcan
  obtain ⟨k, hk2, hk, h4⟩ := exists_age_four a ha hs
  have := (hcan k hk2 (by rw [hs]; exact hk)).2
  omega

/-- `1389 ∉ I_{4,wps}`. -/
theorem not_mem_Iwps4 : 1389 ∉ Iwps4 :=
  not_mem_Iwps4_of_sorted LiuCert.witness

end LiuIndex
