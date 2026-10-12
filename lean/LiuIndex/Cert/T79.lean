import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 79`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_79_0_0 : run12 79 0 0 1 0x1001 = true := by decide +kernel
theorem q_79_0 : Q 79 0 := Q_of_rng (unit_sound 79 0 0 1 _ u_79_0_0)

theorem u_79_1_0 : run12 79 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_79_1 : Q 79 1 := Q_of_rng (unit_sound 79 1 0 2 _ u_79_1_0)

theorem u_79_2_0 : run12 79 2 0 3 0x6004018010060040180100400401001 = true := by decide +kernel
theorem q_79_2 : Q 79 2 := Q_of_rng (unit_sound 79 2 0 3 _ u_79_2_0)

theorem u_79_3_0 : run12 79 3 0 4 0x60040180100600401801006004018010060040180100600401001 = true := by decide +kernel
theorem q_79_3 : Q 79 3 := Q_of_rng (unit_sound 79 3 0 4 _ u_79_3_0)

theorem u_79_4_0 : run12 79 4 0 5 0x180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_4 : Q 79 4 := Q_of_rng (unit_sound 79 4 0 5 _ u_79_4_0)

theorem u_79_5_0 : run12 79 5 0 6 0x180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_5 : Q 79 5 := Q_of_rng (unit_sound 79 5 0 6 _ u_79_5_0)

theorem u_79_6_0 : run12 79 6 0 7 0x6004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_6 : Q 79 6 := Q_of_rng (unit_sound 79 6 0 7 _ u_79_6_0)

theorem u_79_7_0 : run12 79 7 0 8 0x6004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_7 : Q 79 7 := Q_of_rng (unit_sound 79 7 0 8 _ u_79_7_0)

theorem u_79_8_0 : run12 79 8 0 9 0x600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_8 : Q 79 8 := Q_of_rng (unit_sound 79 8 0 9 _ u_79_8_0)

theorem u_79_9_0 : run12 79 9 0 10 0x60040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_9 : Q 79 9 := Q_of_rng (unit_sound 79 9 0 10 _ u_79_9_0)

theorem u_79_10_0 : run12 79 10 0 11 0x6004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_10 : Q 79 10 := Q_of_rng (unit_sound 79 10 0 11 _ u_79_10_0)

theorem u_79_11_0 : run12 79 11 0 12 0x180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_79_11 : Q 79 11 := Q_of_rng (unit_sound 79 11 0 12 _ u_79_11_0)

theorem u_79_12_0 : run12 79 12 0 13 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_79_12 : Q 79 12 := Q_of_rng (unit_sound 79 12 0 13 _ u_79_12_0)

theorem u_79_13_0 : run12 79 13 0 14 0x60040180100600401801 = true := by decide +kernel
theorem q_79_13 : Q 79 13 := Q_of_rng (unit_sound 79 13 0 14 _ u_79_13_0)

theorem u_79_14_0 : run12 79 14 0 15 0x600401801 = true := by decide +kernel
theorem q_79_14 : Q 79 14 := Q_of_rng (unit_sound 79 14 0 15 _ u_79_14_0)

theorem u_79_15_0 : run12 79 15 0 16 0x1801 = true := by decide +kernel
theorem q_79_15 : Q 79 15 := Q_of_rng (unit_sound 79 15 0 16 _ u_79_15_0)

theorem r_79 : R 79 := R_of_cut (t1 := 79) (n := 16) (Q_lt_succ (n := 15) (Q_lt_succ (n := 14) (Q_lt_succ (n := 13) (Q_lt_succ (n := 12) (Q_lt_succ (n := 11) (Q_lt_succ (n := 10) (Q_lt_succ (n := 9) (Q_lt_succ (n := 8) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 79) q_79_0) q_79_1) q_79_2) q_79_3) q_79_4) q_79_5) q_79_6) q_79_7) q_79_8) q_79_9) q_79_10) q_79_11) q_79_12) q_79_13) q_79_14) q_79_15) (by decide)

end LiuCert
