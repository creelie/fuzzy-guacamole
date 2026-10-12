import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 85`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_85_0_0 : run12 85 0 0 1 0x1801 = true := by decide +kernel
theorem q_85_0 : Q 85 0 := Q_of_rng (unit_sound 85 0 0 1 _ u_85_0_0)

theorem u_85_1_0 : run12 85 1 0 2 0x180100600401801 = true := by decide +kernel
theorem q_85_1 : Q 85 1 := Q_of_rng (unit_sound 85 1 0 2 _ u_85_1_0)

theorem u_85_2_0 : run12 85 2 0 3 0x600401801 = true := by decide +kernel
theorem q_85_2 : Q 85 2 := Q_of_rng (unit_sound 85 2 0 3 _ u_85_2_0)

theorem u_85_3_0 : run12 85 3 0 4 0x1801 = true := by decide +kernel
theorem q_85_3 : Q 85 3 := Q_of_rng (unit_sound 85 3 0 4 _ u_85_3_0)

theorem r_85 : R 85 := R_of_cut (t1 := 85) (n := 4) (Q_lt_succ (n := 3) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 85) q_85_0) q_85_1) q_85_2) q_85_3) (by decide)

end LiuCert
