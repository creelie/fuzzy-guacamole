import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 1`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_1_0_0 : run12 1 0 0 1 0x1001 = true := by decide +kernel
theorem q_1_0 : Q 1 0 := Q_of_rng (unit_sound 1 0 0 1 _ u_1_0_0)

theorem u_1_1_0 : run12 1 1 0 2 0x100100400401001 = true := by decide +kernel
theorem q_1_1 : Q 1 1 := Q_of_rng (unit_sound 1 1 0 2 _ u_1_1_0)

theorem r_1 : R 1 := R_of_full (t1 := 1) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 1) q_1_0) q_1_1)

end LiuCert
