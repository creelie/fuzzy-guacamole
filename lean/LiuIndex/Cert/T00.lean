import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 0`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_0_0_0 : run12 0 0 0 1 0x1001 = true := by decide +kernel
theorem q_0_0 : Q 0 0 := Q_of_rng (unit_sound 0 0 0 1 _ u_0_0_0)

theorem r_0 : R 0 := R_of_full (t1 := 0) (Q_lt_succ (n := 0) (Q_lt_zero 0) q_0_0)

end LiuCert
