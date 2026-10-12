import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 6`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_6_0_0 : run12 6 0 0 1 0x1001 = true := by decide +kernel
theorem q_6_0 : Q 6 0 := Q_of_rng (unit_sound 6 0 0 1 _ u_6_0_0)

theorem u_6_1_0 : run12 6 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_6_1 : Q 6 1 := Q_of_rng (unit_sound 6 1 0 2 _ u_6_1_0)

theorem u_6_2_0 : run12 6 2 0 3 0x4004010010040040100100400401001 = true := by decide +kernel
theorem q_6_2 : Q 6 2 := Q_of_rng (unit_sound 6 2 0 3 _ u_6_2_0)

theorem u_6_3_0 : run12 6 3 0 4 0x40040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_6_3 : Q 6 3 := Q_of_rng (unit_sound 6 3 0 4 _ u_6_3_0)

theorem u_6_4_0 : run12 6 4 0 5 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_6_4 : Q 6 4 := Q_of_rng (unit_sound 6 4 0 5 _ u_6_4_0)

theorem u_6_5_0 : run12 6 5 0 6 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_6_5 : Q 6 5 := Q_of_rng (unit_sound 6 5 0 6 _ u_6_5_0)

theorem u_6_6_0 : run12 6 6 0 7 0x40040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_6_6 : Q 6 6 := Q_of_rng (unit_sound 6 6 0 7 _ u_6_6_0)

theorem r_6 : R 6 := R_of_full (t1 := 6) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 6) q_6_0) q_6_1) q_6_2) q_6_3) q_6_4) q_6_5) q_6_6)

end LiuCert
