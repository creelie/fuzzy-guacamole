import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 84`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_84_0_0 : run12 84 0 0 1 0x1801 = true := by decide +kernel
theorem q_84_0 : Q 84 0 := Q_of_rng (unit_sound 84 0 0 1 _ u_84_0_0)

theorem u_84_1_0 : run12 84 1 0 2 0x180100600401801 = true := by decide +kernel
theorem q_84_1 : Q 84 1 := Q_of_rng (unit_sound 84 1 0 2 _ u_84_1_0)

theorem u_84_2_0 : run12 84 2 0 3 0x18010060040180100600401801 = true := by decide +kernel
theorem q_84_2 : Q 84 2 := Q_of_rng (unit_sound 84 2 0 3 _ u_84_2_0)

theorem u_84_3_0 : run12 84 3 0 4 0x60040180100600401801 = true := by decide +kernel
theorem q_84_3 : Q 84 3 := Q_of_rng (unit_sound 84 3 0 4 _ u_84_3_0)

theorem u_84_4_0 : run12 84 4 0 5 0x600401801 = true := by decide +kernel
theorem q_84_4 : Q 84 4 := Q_of_rng (unit_sound 84 4 0 5 _ u_84_4_0)

theorem u_84_5_0 : run12 84 5 0 6 0x1801 = true := by decide +kernel
theorem q_84_5 : Q 84 5 := Q_of_rng (unit_sound 84 5 0 6 _ u_84_5_0)

theorem r_84 : R 84 := R_of_cut (t1 := 84) (n := 6) (Q_lt_succ (n := 5) (Q_lt_succ (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 84) q_84_0) q_84_1) q_84_2) q_84_3) q_84_4) q_84_5) (by decide)

end LiuCert
