import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 4`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_4_0_0 : run12 4 0 0 1 0x1001 = true := by decide +kernel
theorem q_4_0 : Q 4 0 := Q_of_rng (unit_sound 4 0 0 1 _ u_4_0_0)

theorem u_4_1_0 : run12 4 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_4_1 : Q 4 1 := Q_of_rng (unit_sound 4 1 0 2 _ u_4_1_0)

theorem u_4_2_0 : run12 4 2 0 3 0x4004010010040040100100400401001 = true := by decide +kernel
theorem q_4_2 : Q 4 2 := Q_of_rng (unit_sound 4 2 0 3 _ u_4_2_0)

theorem u_4_3_0 : run12 4 3 0 4 0x40040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_4_3 : Q 4 3 := Q_of_rng (unit_sound 4 3 0 4 _ u_4_3_0)

theorem u_4_4_0 : run12 4 4 0 5 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_4_4 : Q 4 4 := Q_of_rng (unit_sound 4 4 0 5 _ u_4_4_0)

theorem r_4 : R 4 := R_of_full (t1 := 4) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 4) q_4_0) q_4_1) q_4_2) q_4_3) q_4_4)

end LiuCert
