import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 3`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_3_0_0 : run12 3 0 0 1 0x1001 = true := by decide +kernel
theorem q_3_0 : Q 3 0 := Q_of_rng (unit_sound 3 0 0 1 _ u_3_0_0)

theorem u_3_1_0 : run12 3 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_3_1 : Q 3 1 := Q_of_rng (unit_sound 3 1 0 2 _ u_3_1_0)

theorem u_3_2_0 : run12 3 2 0 3 0x4004010010040040100100400401001 = true := by decide +kernel
theorem q_3_2 : Q 3 2 := Q_of_rng (unit_sound 3 2 0 3 _ u_3_2_0)

theorem u_3_3_0 : run12 3 3 0 4 0x40040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_3_3 : Q 3 3 := Q_of_rng (unit_sound 3 3 0 4 _ u_3_3_0)

theorem r_3 : R 3 := R_of_full (t1 := 3) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 3) q_3_0) q_3_1) q_3_2) q_3_3)

end LiuCert
