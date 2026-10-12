import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 81`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_81_0_0 : run12 81 0 0 1 0x1001 = true := by decide +kernel
theorem q_81_0 : Q 81 0 := Q_of_rng (unit_sound 81 0 0 1 _ u_81_0_0)

theorem u_81_1_0 : run12 81 1 0 2 0x180100600401001 = true := by decide +kernel
theorem q_81_1 : Q 81 1 := Q_of_rng (unit_sound 81 1 0 2 _ u_81_1_0)

theorem u_81_2_0 : run12 81 2 0 3 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_81_2 : Q 81 2 := Q_of_rng (unit_sound 81 2 0 3 _ u_81_2_0)

theorem u_81_3_0 : run12 81 3 0 4 0x60040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_81_3 : Q 81 3 := Q_of_rng (unit_sound 81 3 0 4 _ u_81_3_0)

theorem u_81_4_0 : run12 81 4 0 5 0x600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_81_4 : Q 81 4 := Q_of_rng (unit_sound 81 4 0 5 _ u_81_4_0)

theorem u_81_5_0 : run12 81 5 0 6 0x180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_81_5 : Q 81 5 := Q_of_rng (unit_sound 81 5 0 6 _ u_81_5_0)

theorem u_81_6_0 : run12 81 6 0 7 0x6004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_81_6 : Q 81 6 := Q_of_rng (unit_sound 81 6 0 7 _ u_81_6_0)

theorem u_81_7_0 : run12 81 7 0 8 0x180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_81_7 : Q 81 7 := Q_of_rng (unit_sound 81 7 0 8 _ u_81_7_0)

theorem u_81_8_0 : run12 81 8 0 9 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_81_8 : Q 81 8 := Q_of_rng (unit_sound 81 8 0 9 _ u_81_8_0)

theorem u_81_9_0 : run12 81 9 0 10 0x60040180100600401801 = true := by decide +kernel
theorem q_81_9 : Q 81 9 := Q_of_rng (unit_sound 81 9 0 10 _ u_81_9_0)

theorem u_81_10_0 : run12 81 10 0 11 0x600401801 = true := by decide +kernel
theorem q_81_10 : Q 81 10 := Q_of_rng (unit_sound 81 10 0 11 _ u_81_10_0)

theorem u_81_11_0 : run12 81 11 0 12 0x1801 = true := by decide +kernel
theorem q_81_11 : Q 81 11 := Q_of_rng (unit_sound 81 11 0 12 _ u_81_11_0)

theorem r_81 : R 81 := R_of_cut (t1 := 81) (n := 12) (Q_lt_succ (n := 11) (Q_lt_succ (n := 10) (Q_lt_succ (n := 9) (Q_lt_succ (n := 8) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 81) q_81_0) q_81_1) q_81_2) q_81_3) q_81_4) q_81_5) q_81_6) q_81_7) q_81_8) q_81_9) q_81_10) q_81_11) (by decide)

end LiuCert
