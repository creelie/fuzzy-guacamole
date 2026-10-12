import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 83`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_83_0_0 : run12 83 0 0 1 0x1801 = true := by decide +kernel
theorem q_83_0 : Q 83 0 := Q_of_rng (unit_sound 83 0 0 1 _ u_83_0_0)

theorem u_83_1_0 : run12 83 1 0 2 0x180100600401801 = true := by decide +kernel
theorem q_83_1 : Q 83 1 := Q_of_rng (unit_sound 83 1 0 2 _ u_83_1_0)

theorem u_83_2_0 : run12 83 2 0 3 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_83_2 : Q 83 2 := Q_of_rng (unit_sound 83 2 0 3 _ u_83_2_0)

theorem u_83_3_0 : run12 83 3 0 4 0x600401801006004018010060040180100600401801 = true := by decide +kernel
theorem q_83_3 : Q 83 3 := Q_of_rng (unit_sound 83 3 0 4 _ u_83_3_0)

theorem u_83_4_0 : run12 83 4 0 5 0x6004018010060040180100600401801 = true := by decide +kernel
theorem q_83_4 : Q 83 4 := Q_of_rng (unit_sound 83 4 0 5 _ u_83_4_0)

theorem u_83_5_0 : run12 83 5 0 6 0x60040180100600401801 = true := by decide +kernel
theorem q_83_5 : Q 83 5 := Q_of_rng (unit_sound 83 5 0 6 _ u_83_5_0)

theorem u_83_6_0 : run12 83 6 0 7 0x600401801 = true := by decide +kernel
theorem q_83_6 : Q 83 6 := Q_of_rng (unit_sound 83 6 0 7 _ u_83_6_0)

theorem u_83_7_0 : run12 83 7 0 8 0x1801 = true := by decide +kernel
theorem q_83_7 : Q 83 7 := Q_of_rng (unit_sound 83 7 0 8 _ u_83_7_0)

theorem r_83 : R 83 := R_of_cut (t1 := 83) (n := 8) (Q_lt_succ (n := 7) (Q_lt_succ (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 83) q_83_0) q_83_1) q_83_2) q_83_3) q_83_4) q_83_5) q_83_6) q_83_7) (by decide)

end LiuCert
