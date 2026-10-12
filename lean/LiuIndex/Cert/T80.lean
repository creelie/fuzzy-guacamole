import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 80`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_80_0_0 : run12 80 0 0 1 0x1001 = true := by decide +kernel
theorem q_80_0 : Q 80 0 := Q_of_rng (unit_sound 80 0 0 1 _ u_80_0_0)

theorem u_80_1_0 : run12 80 1 0 2 0x180100400401001 = true := by decide +kernel
theorem q_80_1 : Q 80 1 := Q_of_rng (unit_sound 80 1 0 2 _ u_80_1_0)

theorem u_80_2_0 : run12 80 2 0 3 0x6004018010060040180100600401001 = true := by decide +kernel
theorem q_80_2 : Q 80 2 := Q_of_rng (unit_sound 80 2 0 3 _ u_80_2_0)

theorem u_80_3_0 : run12 80 3 0 4 0x60040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_80_3 : Q 80 3 := Q_of_rng (unit_sound 80 3 0 4 _ u_80_3_0)

theorem u_80_4_0 : run12 80 4 0 5 0x180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_80_4 : Q 80 4 := Q_of_rng (unit_sound 80 4 0 5 _ u_80_4_0)

theorem u_80_5_0 : run12 80 5 0 6 0x1801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_80_5 : Q 80 5 := Q_of_rng (unit_sound 80 5 0 6 _ u_80_5_0)

theorem u_80_6_0 : run12 80 6 0 7 0x1801006004018010060040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_80_6 : Q 80 6 := Q_of_rng (unit_sound 80 6 0 7 _ u_80_6_0)

theorem u_80_7_0 : run12 80 7 0 8 0x60040180100600401801006004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_80_7 : Q 80 7 := Q_of_rng (unit_sound 80 7 0 8 _ u_80_7_0)

theorem u_80_8_0 : run12 80 8 0 9 0x6004018010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_80_8 : Q 80 8 := Q_of_rng (unit_sound 80 8 0 9 _ u_80_8_0)

theorem u_80_9_0 : run12 80 9 0 10 0x180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_80_9 : Q 80 9 := Q_of_rng (unit_sound 80 9 0 10 _ u_80_9_0)

theorem u_80_10_0 : run12 80 10 0 11 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_80_10 : Q 80 10 := Q_of_rng (unit_sound 80 10 0 11 _ u_80_10_0)

theorem u_80_11_0 : run12 80 11 0 12 0x60040180100600401801 = true := by decide +kernel
theorem q_80_11 : Q 80 11 := Q_of_rng (unit_sound 80 11 0 12 _ u_80_11_0)

theorem u_80_12_0 : run12 80 12 0 13 0x600401801 = true := by decide +kernel
theorem q_80_12 : Q 80 12 := Q_of_rng (unit_sound 80 12 0 13 _ u_80_12_0)

theorem u_80_13_0 : run12 80 13 0 14 0x1801 = true := by decide +kernel
theorem q_80_13 : Q 80 13 := Q_of_rng (unit_sound 80 13 0 14 _ u_80_13_0)

theorem r_80 : R 80 := R_of_cut (t1 := 80) (n := 14) (Q_lt_succ (n := 13) (Q_lt_succ (n := 12) (Q_lt_succ (n := 11) (Q_lt_succ (n := 10) (Q_lt_succ (n := 9) (Q_lt_succ (n := 8) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 80) q_80_0) q_80_1) q_80_2) q_80_3) q_80_4) q_80_5) q_80_6) q_80_7) q_80_8) q_80_9) q_80_10) q_80_11) q_80_12) q_80_13) (by decide)

end LiuCert
