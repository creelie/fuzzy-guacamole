/-
Soundness of the kernel checker in `LiuIndex.Check.Defs`: if every certificate unit
passes, every tuple `a1 ≥ a2 ≥ a3 ≥ a4 ≥ 1` with `2 a1 + a2 + a3 + a4 ≤ 1389` has a
`k ∈ [2, 1387]` with all residues `k a_i mod 1389` positive and summing to at most 1388.
Core Lean only.
-/
import LiuIndex.Check.Defs

namespace LiuCheck

def lane (X j : Nat) : Nat := X / 2 ^ (w * j) % 2 ^ w

theorem pk_zero (f : Nat → Nat) : pk f 0 = 0 := rfl
theorem pk_succ (f : Nat → Nat) (n : Nat) : pk f (n + 1) = pk f n + f n * 2 ^ (w * n) := rfl

theorem pk_congr {f g : Nat → Nat} {n : Nat} (h : ∀ j < n, f j = g j) : pk f n = pk g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pk_succ, pk_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem pk_add (f g : Nat → Nat) (n : Nat) : pk f n + pk g n = pk (fun j => f j + g j) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pk_succ, pk_succ, pk_succ, ← ih, Nat.add_mul]; omega

theorem pk_mul (c : Nat) (f : Nat → Nat) (n : Nat) : c * pk f n = pk (fun j => c * f j) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pk_succ, pk_succ, Nat.mul_add, ih, Nat.mul_assoc]

theorem pk_sub {f g : Nat → Nat} {n : Nat} (h : ∀ j < n, g j ≤ f j) :
    pk f n - pk g n = pk (fun j => f j - g j) n := by
  have : pk (fun j => f j - g j) n + pk g n = pk f n := by
    rw [pk_add]; exact pk_congr (fun j hj => Nat.sub_add_cancel (h j hj))
  omega

theorem pow_w_pos (j : Nat) : 0 < 2 ^ (w * j) := Nat.two_pow_pos _

theorem pk_lt {f : Nat → Nat} {n : Nat} (h : ∀ j < n, f j < 2 ^ w) : pk f n < 2 ^ (w * n) := by
  induction n with
  | zero => simp [pk_zero]
  | succ n ih =>
    rw [pk_succ]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 : f n + 1 ≤ 2 ^ w := h n (by omega)
    have e : 2 ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [e]
    have := Nat.mul_le_mul_right (2 ^ (w * n)) h2
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

theorem lane_pk {f : Nat → Nat} {n : Nat} (h : ∀ j < n, f j < 2 ^ w) {j : Nat} (hj : j < n) :
    lane (pk f n) j = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold lane
    rw [pk_succ]
    have hA := pk_lt (fun i hi => h i (by omega) : ∀ i < n, f i < 2 ^ w)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · -- f n * 2^(w n) = (f n * 2^(w (n - j))) * 2^(w j)
      have e : f n * 2 ^ (w * n) = (f n * 2 ^ (w * (n - j - 1)) * 2 ^ w) * 2 ^ (w * j) := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
        congr 2
        simp only [w]; omega
      rw [e, Nat.add_mul_div_right _ _ (pow_w_pos j), Nat.add_mul_mod_self_right]
      exact ih (fun i hi => h i (by omega)) hj
    · subst hj
      rw [Nat.add_mul_div_right _ _ (pow_w_pos j), Nat.div_eq_of_lt hA, Nat.zero_add]
      exact Nat.mod_eq_of_lt (h j (by omega))

end LiuCheck

namespace LiuCheck

theorem lane_and (X Y j : Nat) : lane (X &&& Y) j = lane X j &&& lane Y j := by
  unfold lane
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  cases decide (i < w) <;> simp

theorem lane_or (X Y j : Nat) : lane (X ||| Y) j = lane X j ||| lane Y j := by
  unfold lane
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_or]
  cases decide (i < w) <;> simp

theorem lane_shiftRight_mod_two (Y s j : Nat) (hs : s < w) :
    lane (Y >>> s) j % 2 = lane Y j / 2 ^ s % 2 := by
  have h1 : ∀ x : Nat, x % 2 = if x.testBit 0 then 1 else 0 := by
    intro x; rw [Nat.testBit_eq_decide_div_mod_eq]; simp only [Nat.pow_zero, Nat.div_one]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  have h2 : ∀ x : Nat, x / 2 ^ s % 2 = if x.testBit s then 1 else 0 := by
    intro x; rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ s) with h | h <;> simp [h]
  rw [h1, h2]
  unfold lane
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_shiftRight]
  have : (decide (0 < w)) = true := by decide
  have h3 : decide (s < w) = true := by simp [hs]
  rw [this, h3]; simp only [Bool.true_and, Nat.zero_add]

theorem pk_lane {X n : Nat} (h : X < 2 ^ (w * n)) : pk (lane X) n = X := by
  induction n generalizing X with
  | zero => simp [pk_zero] at *; omega
  | succ n ih =>
    rw [pk_succ]
    have hm : X % 2 ^ (w * n) < 2 ^ (w * n) := Nat.mod_lt _ (pow_w_pos n)
    have e1 : pk (lane X) n = pk (lane (X % 2 ^ (w * n))) n := by
      apply pk_congr; intro j hj
      unfold lane
      have e : 2 ^ (w * n) = 2 ^ (w * j) * 2 ^ (w * (n - j)) := by
        rw [← Nat.pow_add]; congr 1; simp only [w]; omega
      rw [e, Nat.mod_mul_right_div_self]
      have hd : 2 ^ w ∣ 2 ^ (w * (n - j)) := Nat.pow_dvd_pow 2 (by simp only [w]; omega)
      rw [Nat.mod_mod_of_dvd _ hd]
    rw [e1, ih hm]
    have e2 : 2 ^ (w * (n + 1)) = 2 ^ (w * n) * 2 ^ w := by
      rw [Nat.mul_succ, Nat.pow_add]
    have hq : X / 2 ^ (w * n) < 2 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (pow_w_pos n), Nat.mul_comm, ← e2]; exact h
    have hl : lane X n = X / 2 ^ (w * n) := by unfold lane; exact Nat.mod_eq_of_lt hq
    rw [hl]
    have := Nat.mod_add_div X (2 ^ (w * n))
    rw [Nat.mul_comm (2 ^ (w * n))] at this; omega

theorem and_lt {X Y n : Nat} (h : Y < 2 ^ n) : X &&& Y < 2 ^ n := Nat.and_lt_two_pow X h
theorem or_lt {X Y n : Nat} (h1 : X < 2 ^ n) (h2 : Y < 2 ^ n) : X ||| Y < 2 ^ n :=
  Nat.or_lt_two_pow h1 h2

end LiuCheck

namespace LiuCheck

theorem Ones_eq : Ones = pk (fun _ => 1) L := by decide +kernel
theorem D1_eq : D1 = pk (dig 0) L := by decide +kernel
theorem D2_eq : D2 = pk (dig 1) L := by decide +kernel
theorem D3_eq : D3 = pk (dig 2) L := by decide +kernel
theorem D4_eq : D4 = pk (dig 3) L := by decide +kernel
theorem Dsum_eq : Dsum = pk (fun l => dig 0 l + dig 1 l + dig 2 l + dig 3 l) L := by decide +kernel
theorem DD_eq : DD = pk (fun l => 2 * dig 0 l + dig 1 l + dig 2 l + dig 3 l) L := by decide +kernel

theorem SM_small : ∀ i < 4, ∀ δ < 8, SM i δ = pk (fun l => if δ ≤ dig i l then 1 else 0) L := by
  decide +kernel

theorem dig_lt (i l : Nat) : dig i l < 8 := Nat.mod_lt _ (by decide)

theorem pk_zero_fun (n : Nat) : pk (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pk_succ, ih]; simp

theorem SM_spec (i δ : Nat) (hi : i < 4) :
    SM i δ = pk (fun l => if δ ≤ dig i l then 1 else 0) L := by
  by_cases hδ : δ < 8
  · exact SM_small i hi δ hδ
  · have hz : pk (fun l => if δ ≤ dig i l then 1 else 0) L = 0 := by
      refine (pk_congr (g := fun _ => 0) (fun j _ => ?_)).trans (pk_zero_fun L)
      have := dig_lt i j
      simp only [show ¬ δ ≤ dig i j by omega, ite_false]
    rw [hz]
    have hb : Nat.ble 8 δ = true := Nat.ble_eq.mpr (by omega)
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl
    · show SM0 δ = 0; unfold SM0; rw [hb]; rfl
    · show SM1 δ = 0; unfold SM1; rw [hb]; rfl
    · show SM2 δ = 0; unfold SM2; rw [hb]; rfl
    · show SM3 δ = 0; unfold SM3; rw [hb]; rfl

theorem flr_min (i k c : Nat) (hi : i < 4) (hk : 0 < k) (_hc : c < q) :
    ∀ J, flr i k c J = pk (fun l => min J ((c + k * dig i l) / q)) L := by
  intro J
  induction J with
  | zero => simp only [flr, Nat.zero_min]; exact (pk_zero_fun L).symm
  | succ J ih =>
    show flr i k c J + SM i (((J + 1) * q - c + k - 1) / k) = _
    rw [ih, SM_spec i _ hi, pk_add]
    apply pk_congr; intro l _
    have key : ((J + 1) * q - c + k - 1) / k ≤ dig i l ↔ (J + 1) * q ≤ c + k * dig i l := by
      rw [Nat.div_le_iff_le_mul_add_pred hk]
      generalize k * dig i l = m
      simp only [q] at *; omega
    by_cases h : (J + 1) * q ≤ c + k * dig i l
    · rw [ite_eq_left (key.mpr h)]
      have : J + 1 ≤ (c + k * dig i l) / q := (Nat.le_div_iff_mul_le (by decide)).mpr h
      omega
    · rw [ite_eq_right (fun h' => h (key.mp h'))]
      have : (c + k * dig i l) / q < J + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
      omega

theorem flr_spec (i k c : Nat) (hi : i < 4) (hk : 0 < k) (hc : c < q) :
    flr i k c (Jof k c) = pk (fun l => (c + k * dig i l) / q) L := by
  rw [flr_min i k c hi hk hc]
  apply pk_congr; intro l _
  have : (c + k * dig i l) / q ≤ Jof k c := by
    unfold Jof; apply Nat.div_le_div_right
    have := dig_lt i l
    have : k * dig i l ≤ k * (B - 1) := Nat.mul_le_mul_left _ (by simp only [B]; omega)
    omega
  omega

end LiuCheck

namespace LiuCheck

theorem Ones_lt : Ones < 2 ^ (w * L) := by
  rw [Ones_eq]; exact pk_lt (fun _ _ => by decide)

theorem lane_Ones {l : Nat} (hl : l < L) : lane Ones l = 1 := by
  rw [Ones_eq]; exact lane_pk (fun _ _ => by decide) hl

/-- Bit `s` of every lane, as `0`/`1`. -/
theorem lane_flag (Y s l : Nat) (hs : s < w) (hl : l < L) :
    lane ((Y >>> s) &&& Ones) l = lane Y l / 2 ^ s % 2 := by
  rw [lane_and, lane_Ones hl, Nat.and_one_is_mod, lane_shiftRight_mod_two Y s l hs]

theorem flag_lt (Y s : Nat) : (Y >>> s) &&& Ones < 2 ^ (w * L) := and_lt Ones_lt

theorem flag_le (Y s l : Nat) (hs : s < w) (hl : l < L) : lane ((Y >>> s) &&& Ones) l ≤ 1 := by
  rw [lane_flag Y s l hs hl]; omega

theorem rr_lemma (k x d : Nat) :
    ((k * x + q - 1) % q + k * d) % q = (k * (x + d) + q - 1) % q := by
  rw [Nat.mod_add_mod, Nat.mul_add]; congr 1; simp only [q]; omega

def Xv (x1 x2 x3 x4 k : Nat) : Nat :=
  (cOf k x1 + cOf k x2 + cOf k x3 + cOf k x4 + 4 + 2 ^ 16 - q) * Ones + k * Dsum -
    q * (flr 0 k (cOf k x1) (Jof k (cOf k x1)) + flr 1 k (cOf k x2) (Jof k (cOf k x2)) +
      flr 2 k (cOf k x3) (Jof k (cOf k x3)) + flr 3 k (cOf k x4) (Jof k (cOf k x4)))

theorem goodVec_eq (x1 x2 x3 x4 k : Nat) :
    goodVec x1 x2 x3 x4 k = Ones - ((Xv x1 x2 x3 x4 k >>> 16) &&& Ones) := rfl

theorem lane_notflag (Y s l : Nat) (hs : s < w) (hl : l < L) :
    lane (Ones - ((Y >>> s) &&& Ones)) l = 1 - lane Y l / 2 ^ s % 2 := by
  have h1 := lane_flag Y s l hs hl
  have h2 := flag_lt Y s
  have h3 := fun j (hj : j < L) => flag_le Y s j hs hj
  generalize (Y >>> s) &&& Ones = Z at *
  rw [← pk_lane h2, Ones_eq, pk_sub h3, lane_pk _ hl, h1]
  intro j _; exact Nat.lt_of_le_of_lt (Nat.sub_le 1 _) (by decide)

/-- The value in lane `l` of `Xv`. -/
theorem lane_Xv (x1 x2 x3 x4 k l : Nat) (hk : 0 < k) (hl : l < L) :
    lane (Xv x1 x2 x3 x4 k) l = 2 ^ 16 - q + 4 + (k * (x1 + dig 0 l) + q - 1) % q +
      (k * (x2 + dig 1 l) + q - 1) % q + (k * (x3 + dig 2 l) + q - 1) % q +
      (k * (x4 + dig 3 l) + q - 1) % q := by
  have hc : ∀ x, cOf k x < q := fun x => Nat.mod_lt _ (by decide)
  have e : ∀ c d, c + k * d = q * ((c + k * d) / q) + (c + k * d) % q := fun c d =>
    (Nat.div_add_mod _ _).symm
  unfold Xv
  rw [flr_spec 0 k _ (by decide) hk (hc x1), flr_spec 1 k _ (by decide) hk (hc x2),
    flr_spec 2 k _ (by decide) hk (hc x3), flr_spec 3 k _ (by decide) hk (hc x4),
    pk_add, pk_add, pk_add, Ones_eq, Dsum_eq, pk_mul, pk_mul, pk_mul, pk_add]
  have hcx := hc x1; have hcx2 := hc x2; have hcx3 := hc x3; have hcx4 := hc x4
  rw [pk_sub, lane_pk _ hl]
  · rw [← rr_lemma k x1, ← rr_lemma k x2, ← rr_lemma k x3, ← rr_lemma k x4]
    unfold cOf at *
    have := e ((k * x1 + q - 1) % q) (dig 0 l); have := e ((k * x2 + q - 1) % q) (dig 1 l)
    have := e ((k * x3 + q - 1) % q) (dig 2 l); have := e ((k * x4 + q - 1) % q) (dig 3 l)
    simp only [Nat.mul_add, Nat.mul_one] at *
    generalize k * dig 0 l = m1 at *; generalize k * dig 1 l = m2 at *
    generalize k * dig 2 l = m3 at *; generalize k * dig 3 l = m4 at *
    simp only [q] at *; omega
  · intro j _
    unfold cOf at *
    have := e ((k * x1 + q - 1) % q) (dig 0 j); have := e ((k * x2 + q - 1) % q) (dig 1 j)
    have := e ((k * x3 + q - 1) % q) (dig 2 j); have := e ((k * x4 + q - 1) % q) (dig 3 j)
    have := Nat.mod_lt ((k * x1 + q - 1) % q + k * dig 0 j) (show 0 < q by decide)
    have := Nat.mod_lt ((k * x2 + q - 1) % q + k * dig 1 j) (show 0 < q by decide)
    have := Nat.mod_lt ((k * x3 + q - 1) % q + k * dig 2 j) (show 0 < q by decide)
    have := Nat.mod_lt ((k * x4 + q - 1) % q + k * dig 3 j) (show 0 < q by decide)
    simp only [Nat.mul_add, Nat.mul_one] at *
    generalize k * dig 0 j = m1 at *; generalize k * dig 1 j = m2 at *
    generalize k * dig 2 j = m3 at *; generalize k * dig 3 j = m4 at *
    simp only [q, w] at *; omega
  · intro j _
    unfold cOf at *
    have := e ((k * x1 + q - 1) % q) (dig 0 j); have := e ((k * x2 + q - 1) % q) (dig 1 j)
    have := e ((k * x3 + q - 1) % q) (dig 2 j); have := e ((k * x4 + q - 1) % q) (dig 3 j)
    simp only [Nat.mul_add, Nat.mul_one] at *
    generalize k * dig 0 j = m1 at *; generalize k * dig 1 j = m2 at *
    generalize k * dig 2 j = m3 at *; generalize k * dig 3 j = m4 at *
    simp only [q] at *; omega

end LiuCheck

namespace LiuCheck

theorem lane_goodVec_le (x1 x2 x3 x4 k l : Nat) (hl : l < L) :
    lane (goodVec x1 x2 x3 x4 k) l ≤ 1 := by
  rw [goodVec_eq, lane_notflag _ 16 l (by decide) hl]; omega

theorem lane_goodVec (x1 x2 x3 x4 k l : Nat) (hk : 0 < k) (hl : l < L)
    (h : lane (goodVec x1 x2 x3 x4 k) l = 1) :
    (k * (x1 + dig 0 l) + q - 1) % q + (k * (x2 + dig 1 l) + q - 1) % q +
      (k * (x3 + dig 2 l) + q - 1) % q + (k * (x4 + dig 3 l) + q - 1) % q + 4 ≤ q - 1 := by
  rw [goodVec_eq, lane_notflag _ 16 l (by decide) hl, lane_Xv _ _ _ _ _ _ hk hl] at h
  simp only [q] at *; omega

theorem goodVec_lt (x1 x2 x3 x4 k : Nat) : goodVec x1 x2 x3 x4 k < 2 ^ (w * L) := by
  rw [goodVec_eq]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) Ones_lt

theorem lane_hiFlag (Y l : Nat) (hl : l < L) : lane (hiFlag Y) l = lane Y l / 2 ^ 15 % 2 :=
  lane_flag Y 15 l (by decide) hl

theorem lane_sorted_flag (c : Nat) (A Bv : Nat → Nat) (Pa Pb l : Nat) (hl : l < L)
    (hA : Pa = pk A L) (hB : Pb = pk Bv L) (hAb : ∀ j < L, A j < 8) (hBb : ∀ j < L, Bv j < 8)
    (hc : 8 ≤ c) (hc2 : c + 8 < 2 ^ 16) (hs : 2 ^ 15 + Bv l ≤ c + A l) :
    lane (hiFlag (c * Ones + Pa - Pb)) l = 1 := by
  have := hAb l hl; have := hBb l hl
  rw [lane_hiFlag _ _ hl, hA, hB, Ones_eq, pk_mul, pk_add, pk_sub, lane_pk _ hl]
  · simp only [Nat.mul_one]; omega
  · intro j hj; have := hAb j hj; have := hBb j hj; simp only [Nat.mul_one, w]; omega
  · intro j hj; have := hBb j hj; simp only [Nat.mul_one]; omega

theorem and_one_one {a b : Nat} (ha : a = 1) (hb : b = 1) : a &&& b = 1 := by subst ha hb; rfl

theorem lane_validVec (x1 x2 x3 x4 l : Nat) (hl : l < L) (h1 : x1 ≤ q) (h2 : x2 ≤ q)
    (h3 : x3 ≤ q) (h4 : x4 ≤ q)
    (s1 : x2 + dig 1 l ≤ x1 + dig 0 l) (s2 : x3 + dig 2 l ≤ x2 + dig 1 l)
    (s3 : x4 + dig 3 l ≤ x3 + dig 2 l)
    (s4 : 2 * (x1 + dig 0 l) + (x2 + dig 1 l) + (x3 + dig 2 l) + (x4 + dig 3 l) ≤ q) :
    lane (validVec x1 x2 x3 x4) l = 1 := by
  have d0 := dig_lt 0 l; have d1 := dig_lt 1 l; have d2 := dig_lt 2 l; have d3 := dig_lt 3 l
  unfold validVec
  rw [lane_and, lane_and, lane_and]
  refine and_one_one (and_one_one (and_one_one ?_ ?_) ?_) ?_
  · exact lane_sorted_flag _ _ _ _ _ l hl D1_eq D2_eq (fun j _ => dig_lt 0 j) (fun j _ => dig_lt 1 j)
      (by simp only [q] at *; omega) (by simp only [q] at *; omega) (by simp only [q] at *; omega)
  · exact lane_sorted_flag _ _ _ _ _ l hl D2_eq D3_eq (fun j _ => dig_lt 1 j) (fun j _ => dig_lt 2 j)
      (by simp only [q] at *; omega) (by simp only [q] at *; omega) (by simp only [q] at *; omega)
  · exact lane_sorted_flag _ _ _ _ _ l hl D3_eq D4_eq (fun j _ => dig_lt 2 j) (fun j _ => dig_lt 3 j)
      (by simp only [q] at *; omega) (by simp only [q] at *; omega) (by simp only [q] at *; omega)
  · rw [lane_hiFlag _ _ hl, DD_eq, Ones_eq, pk_mul, pk_sub, lane_pk _ hl]
    · simp only [Nat.mul_one, q] at *; omega
    · intro j hj
      have := dig_lt 0 j; have := dig_lt 1 j; have := dig_lt 2 j; have := dig_lt 3 j
      simp only [Nat.mul_one, q, w] at *; omega
    · intro j hj
      have := dig_lt 0 j; have := dig_lt 1 j; have := dig_lt 2 j; have := dig_lt 3 j
      simp only [Nat.mul_one, q] at *; omega

theorem or_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

theorem or_eq_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (h : a ||| b = 1) : a = 1 ∨ b = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp_all

theorem covOf_lt (x1 x2 x3 x4 : Nat) (ks : List Nat) : covOf x1 x2 x3 x4 ks < 2 ^ (w * L) := by
  induction ks with
  | nil => exact Nat.two_pow_pos _
  | cons k ks ih => exact or_lt (goodVec_lt _ _ _ _ _) ih

theorem lane_covOf_le (x1 x2 x3 x4 : Nat) (ks : List Nat) (l : Nat) (hl : l < L) :
    lane (covOf x1 x2 x3 x4 ks) l ≤ 1 := by
  induction ks with
  | nil => simp [covOf, lane]
  | cons k ks ih =>
    simp only [covOf]; rw [lane_or]; exact or_le_one (lane_goodVec_le _ _ _ _ _ _ hl) ih

theorem covOf_one (x1 x2 x3 x4 : Nat) (ks : List Nat) (l : Nat) (hl : l < L)
    (h : lane (covOf x1 x2 x3 x4 ks) l = 1) : ∃ k ∈ ks, lane (goodVec x1 x2 x3 x4 k) l = 1 := by
  induction ks with
  | nil => simp [covOf, lane] at h
  | cons k ks ih =>
    simp only [covOf] at h; rw [lane_or] at h
    rcases or_eq_one (lane_goodVec_le _ _ _ _ _ _ hl) (lane_covOf_le _ _ _ _ _ _ hl) h with h | h
    · exact ⟨k, List.mem_cons_self .., h⟩
    · obtain ⟨k', hk', h'⟩ := ih h; exact ⟨k', List.mem_cons_of_mem _ hk', h'⟩

theorem boxOK_sound (x1 x2 x3 x4 : Nat) (ks : List Nat) (hb : boxOK x1 x2 x3 x4 ks = true)
    (l : Nat) (hl : l < L) (hv : lane (validVec x1 x2 x3 x4) l = 1) :
    ∃ k ∈ ks, kOK k = true ∧ lane (goodVec x1 x2 x3 x4 k) l = 1 := by
  simp only [boxOK, Bool.and_eq_true, List.all_eq_true] at hb
  obtain ⟨hk, h0⟩ := hb
  have h0 := congrArg (fun X => lane X l) (Nat.eq_of_beq_eq_true h0)
  simp only [lane_and, hv] at h0
  have hc := lane_covOf_le x1 x2 x3 x4 ks l hl
  have hs : lane (Ones - covOf x1 x2 x3 x4 ks) l = 1 - lane (covOf x1 x2 x3 x4 ks) l := by
    have h2 := covOf_lt x1 x2 x3 x4 ks
    have h3 := fun j (hj : j < L) => lane_covOf_le x1 x2 x3 x4 ks j hj
    generalize covOf x1 x2 x3 x4 ks = Z at *
    conv => lhs; rw [← pk_lane h2, Ones_eq, pk_sub h3]
    rw [lane_pk _ hl]
    intro j _; exact Nat.lt_of_le_of_lt (Nat.sub_le 1 _) (by decide)
  rw [hs] at h0
  have h1 : lane (covOf x1 x2 x3 x4 ks) l = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · rw [h] at h0; simp [lane] at h0
    · exact h
  obtain ⟨k, hkm, hk'⟩ := covOf_one x1 x2 x3 x4 ks l hl h1
  exact ⟨k, hkm, hk k hkm, hk'⟩

end LiuCheck

namespace LiuCheck

/-- Every box `(t1, t2, t3, t4)` with `t4 ≤ t3` passing the corner filter has a valid `k`-list. -/
def P (t1 t2 t3 : Nat) : Prop :=
  ∀ t4, t4 ≤ t3 → 2 * (1 + 8 * t1) + (1 + 8 * t2) + (1 + 8 * t3) + (1 + 8 * t4) ≤ q →
    ∃ ks, boxOK (1 + 8 * t1) (1 + 8 * t2) (1 + 8 * t3) (1 + 8 * t4) ks = true

def Q (t1 t2 : Nat) : Prop := ∀ t3, t3 ≤ t2 → P t1 t2 t3

def R (t1 : Nat) : Prop := ∀ t2, t2 ≤ t1 → Q t1 t2

theorem runBoxes_sound (t1 t2 : Nat) (ps : List (Nat × Nat)) (s : Nat)
    (h : runBoxes t1 t2 ps s = true) :
    ∀ p ∈ ps, ∃ ks, boxOK (1 + 8 * t1) (1 + 8 * t2) (1 + 8 * p.1) (1 + 8 * p.2) ks = true := by
  induction ps generalizing s with
  | nil => intro p hp; cases hp
  | cons p ps ih =>
    simp only [runBoxes, Bool.and_eq_true] at h
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact ⟨_, h.1⟩
    · exact ih _ h.2 p' hp'

theorem mem_boxesOf (t1 t2 lo hi t3 t4 : Nat) (h1 : lo ≤ t3) (h2 : t3 < hi) (h3 : t4 ≤ t3)
    (h4 : 2 * (1 + 8 * t1) + (1 + 8 * t2) + (1 + 8 * t3) + (1 + 8 * t4) ≤ q) :
    (t3, t4) ∈ boxesOf t1 t2 lo hi := by
  simp only [boxesOf, List.mem_filter, List.mem_flatMap, List.mem_range', List.mem_map,
    List.mem_range, Prod.mk.injEq]
  refine ⟨⟨t3, ⟨t3 - lo, by omega, by omega⟩, t4, by omega, rfl, rfl⟩, ?_⟩
  exact Nat.ble_eq.mpr h4

theorem unit_sound (t1 t2 lo hi s : Nat) (h : run12 t1 t2 lo hi s = true) :
    ∀ t3, lo ≤ t3 → t3 < hi → P t1 t2 t3 := by
  intro t3 h1 h2 t4 h3 h4
  exact runBoxes_sound t1 t2 _ s h (t3, t4) (mem_boxesOf t1 t2 lo hi t3 t4 h1 h2 h3 h4)

theorem rng_join {t1 t2 a b c : Nat} (h1 : ∀ t3, a ≤ t3 → t3 < b → P t1 t2 t3)
    (h2 : ∀ t3, b ≤ t3 → t3 < c → P t1 t2 t3) : ∀ t3, a ≤ t3 → t3 < c → P t1 t2 t3 := by
  intro t3 ha hc
  by_cases hb : t3 < b
  · exact h1 t3 ha hb
  · exact h2 t3 (by omega) hc

theorem Q_of_rng {t1 t2 : Nat} (h : ∀ t3, 0 ≤ t3 → t3 < t2 + 1 → P t1 t2 t3) : Q t1 t2 :=
  fun t3 h3 => h t3 (Nat.zero_le _) (by omega)

theorem Q_vac {t1 t2 : Nat} (h : q < 2 * (1 + 8 * t1) + (1 + 8 * t2) + 2) : Q t1 t2 := by
  intro t3 _ t4 _ h4; simp only [q] at *; omega

theorem Q_lt_zero (t1 : Nat) : ∀ t2, t2 < 0 → Q t1 t2 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem Q_lt_succ {t1 n : Nat} (h : ∀ t2, t2 < n → Q t1 t2) (h' : Q t1 n) :
    ∀ t2, t2 < n + 1 → Q t1 t2 := by
  intro t2 h2
  by_cases hn : t2 < n
  · exact h t2 hn
  · have : t2 = n := by omega
    subst this; exact h'

theorem R_of_full {t1 : Nat} (h : ∀ t2, t2 < t1 + 1 → Q t1 t2) : R t1 :=
  fun t2 h2 => h t2 (by omega)

theorem R_of_cut {t1 n : Nat} (h : ∀ t2, t2 < n → Q t1 t2)
    (hv : q < 2 * (1 + 8 * t1) + (1 + 8 * n) + 2) : R t1 := by
  intro t2 _
  by_cases hn : t2 < n
  · exact h t2 hn
  · exact Q_vac (by simp only [q] at *; omega)

theorem R_vac {t1 : Nat} (h : q < 2 * (1 + 8 * t1) + 3) : R t1 :=
  fun t2 _ => Q_vac (by simp only [q] at *; omega)

theorem R_lt_zero : ∀ t1, t1 < 0 → R t1 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem R_lt_succ {n : Nat} (h : ∀ t1, t1 < n → R t1) (h' : R n) : ∀ t1, t1 < n + 1 → R t1 := by
  intro t1 h1
  by_cases hn : t1 < n
  · exact h t1 hn
  · have : t1 = n := by omega
    subst this; exact h'

theorem kOK_bounds {k : Nat} (h : kOK k = true) : 2 ≤ k ∧ k ≤ q - 2 := by
  simp only [kOK, Bool.and_eq_true, Nat.ble_eq] at h; exact h

theorem res_of_rr (u : Nat) (hu : 1 ≤ u) (h : (u + q - 1) % q + 4 ≤ q - 1) :
    1 ≤ u % q ∧ u % q = (u + q - 1) % q + 1 := by
  simp only [q] at *; omega

theorem dig_vals (d1 d2 d3 d4 : Nat) (h1 : d1 < 8) (h2 : d2 < 8) (h3 : d3 < 8) (h4 : d4 < 8) :
    dig 0 (d1 + 8 * d2 + 64 * d3 + 512 * d4) = d1 ∧ dig 1 (d1 + 8 * d2 + 64 * d3 + 512 * d4) = d2 ∧
    dig 2 (d1 + 8 * d2 + 64 * d3 + 512 * d4) = d3 ∧ dig 3 (d1 + 8 * d2 + 64 * d3 + 512 * d4) = d4 := by
  simp only [dig, B]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Nat.pow_zero, Nat.pow_succ, Nat.one_mul] <;> omega

/-- The covering statement, from the certificate. -/
theorem cover (hall : ∀ t1, R t1) (a1 a2 a3 a4 : Nat) (h4 : 1 ≤ a4) (h34 : a4 ≤ a3)
    (h23 : a3 ≤ a2) (h12 : a2 ≤ a1) (h0 : 2 * a1 + a2 + a3 + a4 ≤ q) :
    ∃ k, 2 ≤ k ∧ k ≤ q - 2 ∧ 1 ≤ k * a1 % q ∧ 1 ≤ k * a2 % q ∧ 1 ≤ k * a3 % q ∧
      1 ≤ k * a4 % q ∧ k * a1 % q + k * a2 % q + k * a3 % q + k * a4 % q ≤ q - 1 := by
  have hd := dig_vals ((a1 - 1) % 8) ((a2 - 1) % 8) ((a3 - 1) % 8) ((a4 - 1) % 8)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))
  generalize hl : (a1 - 1) % 8 + 8 * ((a2 - 1) % 8) + 64 * ((a3 - 1) % 8) + 512 * ((a4 - 1) % 8) = l
    at hd
  obtain ⟨e1, e2, e3, e4⟩ := hd
  have hlL : l < L := by simp only [L]; omega
  have hP := hall ((a1 - 1) / 8) ((a2 - 1) / 8) (by omega) ((a3 - 1) / 8) (by omega)
    ((a4 - 1) / 8) (by omega) (by simp only [q] at *; omega)
  obtain ⟨ks, hks⟩ := hP
  generalize hX1 : 1 + 8 * ((a1 - 1) / 8) = X1 at hks
  generalize hX2 : 1 + 8 * ((a2 - 1) / 8) = X2 at hks
  generalize hX3 : 1 + 8 * ((a3 - 1) / 8) = X3 at hks
  generalize hX4 : 1 + 8 * ((a4 - 1) / 8) = X4 at hks
  have ea1 : X1 + dig 0 l = a1 := by rw [e1]; omega
  have ea2 : X2 + dig 1 l = a2 := by rw [e2]; omega
  have ea3 : X3 + dig 2 l = a3 := by rw [e3]; omega
  have ea4 : X4 + dig 3 l = a4 := by rw [e4]; omega
  clear e1 e2 e3 e4 hX1 hX2 hX3 hX4 hl
  have hv : lane (validVec X1 X2 X3 X4) l = 1 :=
    lane_validVec X1 X2 X3 X4 l hlL (by simp only [q] at *; omega) (by simp only [q] at *; omega)
      (by simp only [q] at *; omega) (by simp only [q] at *; omega)
      (by omega) (by omega) (by omega) (by rw [ea1, ea2, ea3, ea4]; exact h0)
  obtain ⟨k, _, hk, hg⟩ := boxOK_sound X1 X2 X3 X4 ks hks l hlL hv
  obtain ⟨hk2, hkq⟩ := kOK_bounds hk
  have hs := lane_goodVec X1 X2 X3 X4 k l (by omega) hlL hg
  rw [ea1, ea2, ea3, ea4] at hs
  have p1 : 1 ≤ k * a1 := Nat.mul_pos (by omega) (by omega)
  have p2 : 1 ≤ k * a2 := Nat.mul_pos (by omega) (by omega)
  have p3 : 1 ≤ k * a3 := Nat.mul_pos (by omega) (by omega)
  have p4 : 1 ≤ k * a4 := Nat.mul_pos (by omega) h4
  have r1 := res_of_rr (k * a1) p1 (by omega)
  have r2 := res_of_rr (k * a2) p2 (by omega)
  have r3 := res_of_rr (k * a3) p3 (by omega)
  have r4 := res_of_rr (k * a4) p4 (by omega)
  refine ⟨k, hk2, hkq, r1.1, r2.1, r3.1, r4.1, ?_⟩
  omega

end LiuCheck
