import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 7`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_7_0_0 : run12 7 0 0 1 0x1001 = true := by decide +kernel
theorem q_7_0 : Q 7 0 := Q_of_rng (unit_sound 7 0 0 1 _ u_7_0_0)

theorem u_7_1_0 : run12 7 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_7_1 : Q 7 1 := Q_of_rng (unit_sound 7 1 0 2 _ u_7_1_0)

theorem u_7_2_0 : run12 7 2 0 3 0x4004010010040040100100400401001 = true := by decide +kernel
theorem q_7_2 : Q 7 2 := Q_of_rng (unit_sound 7 2 0 3 _ u_7_2_0)

theorem u_7_3_0 : run12 7 3 0 4 0x40040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_7_3 : Q 7 3 := Q_of_rng (unit_sound 7 3 0 4 _ u_7_3_0)

theorem u_7_4_0 : run12 7 4 0 5 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_7_4 : Q 7 4 := Q_of_rng (unit_sound 7 4 0 5 _ u_7_4_0)

theorem u_7_5_0 : run12 7 5 0 6 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_7_5 : Q 7 5 := Q_of_rng (unit_sound 7 5 0 6 _ u_7_5_0)

theorem u_7_6_0 : run12 7 6 0 7 0x40040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_7_6 : Q 7 6 := Q_of_rng (unit_sound 7 6 0 7 _ u_7_6_0)

theorem u_7_7_0 : run12 7 7 0 8 0x4004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_7_7 : Q 7 7 := Q_of_rng (unit_sound 7 7 0 8 _ u_7_7_0)

theorem r_7 : R 7 := R_of_full (t1 := 7) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 7) q_7_0) q_7_1) q_7_2) q_7_3) q_7_4) q_7_5) q_7_6) q_7_7)

end LiuCert
