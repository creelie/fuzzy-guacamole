import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 2`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_2_0_0 : run12 2 0 0 1 0x1001 = true := by decide +kernel
theorem q_2_0 : Q 2 0 := Q_of_rng (unit_sound 2 0 0 1 _ u_2_0_0)

theorem u_2_1_0 : run12 2 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_2_1 : Q 2 1 := Q_of_rng (unit_sound 2 1 0 2 _ u_2_1_0)

theorem u_2_2_0 : run12 2 2 0 3 0x4004010010040040100100400401001 = true := by decide +kernel
theorem q_2_2 : Q 2 2 := Q_of_rng (unit_sound 2 2 0 3 _ u_2_2_0)

theorem r_2 : R 2 := R_of_full (t1 := 2) (Q_lt_succ (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 2) q_2_0) q_2_1) q_2_2)

end LiuCert
