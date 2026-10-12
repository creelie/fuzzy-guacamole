import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 5`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_5_0_0 : run12 5 0 0 1 0x1001 = true := by decide +kernel
theorem q_5_0 : Q 5 0 := Q_of_rng (unit_sound 5 0 0 1 _ u_5_0_0)

theorem u_5_1_0 : run12 5 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_5_1 : Q 5 1 := Q_of_rng (unit_sound 5 1 0 2 _ u_5_1_0)

theorem u_5_2_0 : run12 5 2 0 3 0x4004010010040040100100400401001 = true := by decide +kernel
theorem q_5_2 : Q 5 2 := Q_of_rng (unit_sound 5 2 0 3 _ u_5_2_0)

theorem u_5_3_0 : run12 5 3 0 4 0x40040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_5_3 : Q 5 3 := Q_of_rng (unit_sound 5 3 0 4 _ u_5_3_0)

theorem u_5_4_0 : run12 5 4 0 5 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_5_4 : Q 5 4 := Q_of_rng (unit_sound 5 4 0 5 _ u_5_4_0)

theorem u_5_5_0 : run12 5 5 0 6 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_5_5 : Q 5 5 := Q_of_rng (unit_sound 5 5 0 6 _ u_5_5_0)

theorem r_5 : R 5 := R_of_full (t1 := 5) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 5) q_5_0) q_5_1) q_5_2) q_5_3) q_5_4) q_5_5)

end LiuCert
