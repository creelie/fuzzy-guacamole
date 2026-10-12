import LiuIndex.Check.Sound

/-! Certificate for the boxes with first corner index `t1 = 86`. -/

namespace LiuCert
open LiuCheck
set_option Elab.async false

theorem u_86_0_0 : run12 86 0 0 1 0x1801 = true := by decide +kernel
theorem q_86_0 : Q 86 0 := Q_of_rng (unit_sound 86 0 0 1 _ u_86_0_0)

theorem u_86_1_0 : run12 86 1 0 2 0x1801 = true := by decide +kernel
theorem q_86_1 : Q 86 1 := Q_of_rng (unit_sound 86 1 0 2 _ u_86_1_0)

theorem r_86 : R 86 := R_of_cut (t1 := 86) (n := 2) (Q_lt_succ (n := 1) (Q_lt_succ (n := 0) (Q_lt_zero 86) q_86_0) q_86_1) (by decide)

end LiuCert
