import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 8`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_8_0_0 : run12 8 0 0 1 0x1001 = true := by decide +kernel
theorem q_8_0 : Q 8 0 := Q_of_rng (unit_sound 8 0 0 1 _ u_8_0_0)

theorem u_8_1_0 : run12 8 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_8_1 : Q 8 1 := Q_of_rng (unit_sound 8 1 0 2 _ u_8_1_0)

theorem u_8_2_0 : run12 8 2 0 3 0x4004010010040040100100400401001 = true := by decide +kernel
theorem q_8_2 : Q 8 2 := Q_of_rng (unit_sound 8 2 0 3 _ u_8_2_0)

theorem u_8_3_0 : run12 8 3 0 4 0x40040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_8_3 : Q 8 3 := Q_of_rng (unit_sound 8 3 0 4 _ u_8_3_0)

theorem u_8_4_0 : run12 8 4 0 5 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_8_4 : Q 8 4 := Q_of_rng (unit_sound 8 4 0 5 _ u_8_4_0)

theorem u_8_5_0 : run12 8 5 0 6 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_8_5 : Q 8 5 := Q_of_rng (unit_sound 8 5 0 6 _ u_8_5_0)

theorem u_8_6_0 : run12 8 6 0 7 0x40040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_8_6 : Q 8 6 := Q_of_rng (unit_sound 8 6 0 7 _ u_8_6_0)

theorem u_8_7_0 : run12 8 7 0 8 0x4004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_8_7 : Q 8 7 := Q_of_rng (unit_sound 8 7 0 8 _ u_8_7_0)

theorem u_8_8_0 : run12 8 8 0 9 0x100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001004004010010040040100100400401001 = true := by decide +kernel
theorem q_8_8 : Q 8 8 := Q_of_rng (unit_sound 8 8 0 9 _ u_8_8_0)

theorem r_8 : R 8 := R_of_full (t1 := 8) (Q_lt_succ (n := 8) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 8) q_8_0) q_8_1) q_8_2) q_8_3) q_8_4) q_8_5) q_8_6) q_8_7) q_8_8)

end LiuCert
