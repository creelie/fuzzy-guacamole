import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 78`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_78_0_0 : run12 78 0 0 1 0x1001 = true := by decide +kernel
theorem q_78_0 : Q 78 0 := Q_of_rng (unit_sound 78 0 0 1 _ u_78_0_0)

theorem u_78_1_0 : run12 78 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_78_1 : Q 78 1 := Q_of_rng (unit_sound 78 1 0 2 _ u_78_1_0)

theorem u_78_2_0 : run12 78 2 0 3 0x6004018010040040100100400401001 = true := by decide +kernel
theorem q_78_2 : Q 78 2 := Q_of_rng (unit_sound 78 2 0 3 _ u_78_2_0)

theorem u_78_3_0 : run12 78 3 0 4 0x60040180100600401801006004018010060040180100400401001 = true := by decide +kernel
theorem q_78_3 : Q 78 3 := Q_of_rng (unit_sound 78 3 0 4 _ u_78_3_0)

theorem u_78_4_0 : run12 78 4 0 5 0x180100600401801006004018010060040180100600401801006004018010060040180100600401001 = true := by decide +kernel
theorem q_78_4 : Q 78 4 := Q_of_rng (unit_sound 78 4 0 5 _ u_78_4_0)

theorem u_78_5_0 : run12 78 5 0 6 0x180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_5 : Q 78 5 := Q_of_rng (unit_sound 78 5 0 6 _ u_78_5_0)

theorem u_78_6_0 : run12 78 6 0 7 0x180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_6 : Q 78 6 := Q_of_rng (unit_sound 78 6 0 7 _ u_78_6_0)

theorem u_78_7_0 : run12 78 7 0 8 0x6004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_7 : Q 78 7 := Q_of_rng (unit_sound 78 7 0 8 _ u_78_7_0)

theorem u_78_8_0 : run12 78 8 0 9 0x18010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_8 : Q 78 8 := Q_of_rng (unit_sound 78 8 0 9 _ u_78_8_0)

theorem u_78_9_0 : run12 78 9 0 10 0x1801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_9 : Q 78 9 := Q_of_rng (unit_sound 78 9 0 10 _ u_78_9_0)

theorem u_78_10_0 : run12 78 10 0 11 0x600401801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_10 : Q 78 10 := Q_of_rng (unit_sound 78 10 0 11 _ u_78_10_0)

theorem u_78_11_0 : run12 78 11 0 12 0x60040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_11 : Q 78 11 := Q_of_rng (unit_sound 78 11 0 12 _ u_78_11_0)

theorem u_78_12_0 : run12 78 12 0 13 0x6004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_12 : Q 78 12 := Q_of_rng (unit_sound 78 12 0 13 _ u_78_12_0)

theorem u_78_13_0 : run12 78 13 0 14 0x180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_78_13 : Q 78 13 := Q_of_rng (unit_sound 78 13 0 14 _ u_78_13_0)

theorem u_78_14_0 : run12 78 14 0 15 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_78_14 : Q 78 14 := Q_of_rng (unit_sound 78 14 0 15 _ u_78_14_0)

theorem u_78_15_0 : run12 78 15 0 16 0x60040180100600401801 = true := by decide +kernel
theorem q_78_15 : Q 78 15 := Q_of_rng (unit_sound 78 15 0 16 _ u_78_15_0)

theorem u_78_16_0 : run12 78 16 0 17 0x600401801 = true := by decide +kernel
theorem q_78_16 : Q 78 16 := Q_of_rng (unit_sound 78 16 0 17 _ u_78_16_0)

theorem u_78_17_0 : run12 78 17 0 18 0x1801 = true := by decide +kernel
theorem q_78_17 : Q 78 17 := Q_of_rng (unit_sound 78 17 0 18 _ u_78_17_0)

theorem r_78 : R 78 := R_of_cut (t1 := 78) (n := 18) (Q_lt_succ (n := 17) (Q_lt_succ (n := 16) (Q_lt_succ (n := 15) (Q_lt_succ (n := 14) (Q_lt_succ (n := 13) (Q_lt_succ (n := 12) (Q_lt_succ (n := 11) (Q_lt_succ (n := 10) (Q_lt_succ (n := 9) (Q_lt_succ (n := 8) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 78) q_78_0) q_78_1) q_78_2) q_78_3) q_78_4) q_78_5) q_78_6) q_78_7) q_78_8) q_78_9) q_78_10) q_78_11) q_78_12) q_78_13) q_78_14) q_78_15) q_78_16) q_78_17) (by decide)

end LiuCert
