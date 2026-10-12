import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 82`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_82_0_0 : run12 82 0 0 1 0x1001 = true := by decide +kernel
theorem q_82_0 : Q 82 0 := Q_of_rng (unit_sound 82 0 0 1 _ u_82_0_0)

theorem u_82_1_0 : run12 82 1 0 2 0x180100600401801 = true := by decide +kernel
theorem q_82_1 : Q 82 1 := Q_of_rng (unit_sound 82 1 0 2 _ u_82_1_0)

theorem u_82_2_0 : run12 82 2 0 3 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_82_2 : Q 82 2 := Q_of_rng (unit_sound 82 2 0 3 _ u_82_2_0)

theorem u_82_3_0 : run12 82 3 0 4 0x60040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_82_3 : Q 82 3 := Q_of_rng (unit_sound 82 3 0 4 _ u_82_3_0)

theorem u_82_4_0 : run12 82 4 0 5 0x18010060040180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_82_4 : Q 82 4 := Q_of_rng (unit_sound 82 4 0 5 _ u_82_4_0)

theorem u_82_5_0 : run12 82 5 0 6 0x180100600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_82_5 : Q 82 5 := Q_of_rng (unit_sound 82 5 0 6 _ u_82_5_0)

theorem u_82_6_0 : run12 82 6 0 7 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_82_6 : Q 82 6 := Q_of_rng (unit_sound 82 6 0 7 _ u_82_6_0)

theorem u_82_7_0 : run12 82 7 0 8 0x60040180100600401801 = true := by decide +kernel
theorem q_82_7 : Q 82 7 := Q_of_rng (unit_sound 82 7 0 8 _ u_82_7_0)

theorem u_82_8_0 : run12 82 8 0 9 0x600401801 = true := by decide +kernel
theorem q_82_8 : Q 82 8 := Q_of_rng (unit_sound 82 8 0 9 _ u_82_8_0)

theorem u_82_9_0 : run12 82 9 0 10 0x1801 = true := by decide +kernel
theorem q_82_9 : Q 82 9 := Q_of_rng (unit_sound 82 9 0 10 _ u_82_9_0)

theorem r_82 : R 82 := R_of_cut (t1 := 82) (n := 10) (Q_lt_succ (n := 9) (Q_lt_succ (n := 8) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 82) q_82_0) q_82_1) q_82_2) q_82_3) q_82_4) q_82_5) q_82_6) q_82_7) q_82_8) q_82_9) (by decide)

end LiuCert
