import LiuIndex.Cert.T00
import LiuIndex.Cert.T01
import LiuIndex.Cert.T02
import LiuIndex.Cert.T03
import LiuIndex.Cert.T04
import LiuIndex.Cert.T05
import LiuIndex.Cert.T06
import LiuIndex.Cert.T07
import LiuIndex.Cert.T08
import LiuIndex.Cert.T09
import LiuIndex.Cert.T10
import LiuIndex.Cert.T11
import LiuIndex.Cert.T12
import LiuIndex.Cert.T13
import LiuIndex.Cert.T14
import LiuIndex.Cert.T15
import LiuIndex.Cert.T16
import LiuIndex.Cert.T17
import LiuIndex.Cert.T18
import LiuIndex.Cert.T19
import LiuIndex.Cert.T20
import LiuIndex.Cert.T21
import LiuIndex.Cert.T22
import LiuIndex.Cert.T23
import LiuIndex.Cert.T24
import LiuIndex.Cert.T25
import LiuIndex.Cert.T26
import LiuIndex.Cert.T27
import LiuIndex.Cert.T28
import LiuIndex.Cert.T29
import LiuIndex.Cert.T30
import LiuIndex.Cert.T31
import LiuIndex.Cert.T32
import LiuIndex.Cert.T33
import LiuIndex.Cert.T34
import LiuIndex.Cert.T35
import LiuIndex.Cert.T36
import LiuIndex.Cert.T37
import LiuIndex.Cert.T38
import LiuIndex.Cert.T39
import LiuIndex.Cert.T40
import LiuIndex.Cert.T41
import LiuIndex.Cert.T42
import LiuIndex.Cert.T43
import LiuIndex.Cert.T44
import LiuIndex.Cert.T45
import LiuIndex.Cert.T46
import LiuIndex.Cert.T47
import LiuIndex.Cert.T48
import LiuIndex.Cert.T49
import LiuIndex.Cert.T50
import LiuIndex.Cert.T51
import LiuIndex.Cert.T52
import LiuIndex.Cert.T53
import LiuIndex.Cert.T54
import LiuIndex.Cert.T55
import LiuIndex.Cert.T56
import LiuIndex.Cert.T57
import LiuIndex.Cert.T58
import LiuIndex.Cert.T59
import LiuIndex.Cert.T60
import LiuIndex.Cert.T61
import LiuIndex.Cert.T62
import LiuIndex.Cert.T63
import LiuIndex.Cert.T64
import LiuIndex.Cert.T65
import LiuIndex.Cert.T66
import LiuIndex.Cert.T67
import LiuIndex.Cert.T68
import LiuIndex.Cert.T69
import LiuIndex.Cert.T70
import LiuIndex.Cert.T71
import LiuIndex.Cert.T72
import LiuIndex.Cert.T73
import LiuIndex.Cert.T74
import LiuIndex.Cert.T75
import LiuIndex.Cert.T76
import LiuIndex.Cert.T77
import LiuIndex.Cert.T78
import LiuIndex.Cert.T79
import LiuIndex.Cert.T80
import LiuIndex.Cert.T81
import LiuIndex.Cert.T82
import LiuIndex.Cert.T83
import LiuIndex.Cert.T84
import LiuIndex.Cert.T85
import LiuIndex.Cert.T86

/-! Assembly of the certificate: every box passes. -/
namespace LiuCert
open LiuCheck

theorem R_below : ∀ t1, t1 < 87 → R t1 := R_lt_succ (n := 86) (R_lt_succ (n := 85) (R_lt_succ (n := 84) (R_lt_succ (n := 83) (R_lt_succ (n := 82) (R_lt_succ (n := 81) (R_lt_succ (n := 80) (R_lt_succ (n := 79) (R_lt_succ (n := 78) (R_lt_succ (n := 77) (R_lt_succ (n := 76) (R_lt_succ (n := 75) (R_lt_succ (n := 74) (R_lt_succ (n := 73) (R_lt_succ (n := 72) (R_lt_succ (n := 71) (R_lt_succ (n := 70) (R_lt_succ (n := 69) (R_lt_succ (n := 68) (R_lt_succ (n := 67) (R_lt_succ (n := 66) (R_lt_succ (n := 65) (R_lt_succ (n := 64) (R_lt_succ (n := 63) (R_lt_succ (n := 62) (R_lt_succ (n := 61) (R_lt_succ (n := 60) (R_lt_succ (n := 59) (R_lt_succ (n := 58) (R_lt_succ (n := 57) (R_lt_succ (n := 56) (R_lt_succ (n := 55) (R_lt_succ (n := 54) (R_lt_succ (n := 53) (R_lt_succ (n := 52) (R_lt_succ (n := 51) (R_lt_succ (n := 50) (R_lt_succ (n := 49) (R_lt_succ (n := 48) (R_lt_succ (n := 47) (R_lt_succ (n := 46) (R_lt_succ (n := 45) (R_lt_succ (n := 44) (R_lt_succ (n := 43) (R_lt_succ (n := 42) (R_lt_succ (n := 41) (R_lt_succ (n := 40) (R_lt_succ (n := 39) (R_lt_succ (n := 38) (R_lt_succ (n := 37) (R_lt_succ (n := 36) (R_lt_succ (n := 35) (R_lt_succ (n := 34) (R_lt_succ (n := 33) (R_lt_succ (n := 32) (R_lt_succ (n := 31) (R_lt_succ (n := 30) (R_lt_succ (n := 29) (R_lt_succ (n := 28) (R_lt_succ (n := 27) (R_lt_succ (n := 26) (R_lt_succ (n := 25) (R_lt_succ (n := 24) (R_lt_succ (n := 23) (R_lt_succ (n := 22) (R_lt_succ (n := 21) (R_lt_succ (n := 20) (R_lt_succ (n := 19) (R_lt_succ (n := 18) (R_lt_succ (n := 17) (R_lt_succ (n := 16) (R_lt_succ (n := 15) (R_lt_succ (n := 14) (R_lt_succ (n := 13) (R_lt_succ (n := 12) (R_lt_succ (n := 11) (R_lt_succ (n := 10) (R_lt_succ (n := 9) (R_lt_succ (n := 8) (R_lt_succ (n := 7) (R_lt_succ (n := 6) (R_lt_succ (n := 5) (R_lt_succ (n := 4) (R_lt_succ (n := 3) (R_lt_succ (n := 2) (R_lt_succ (n := 1) (R_lt_succ (n := 0) (R_lt_zero) r_0) r_1) r_2) r_3) r_4) r_5) r_6) r_7) r_8) r_9) r_10) r_11) r_12) r_13) r_14) r_15) r_16) r_17) r_18) r_19) r_20) r_21) r_22) r_23) r_24) r_25) r_26) r_27) r_28) r_29) r_30) r_31) r_32) r_33) r_34) r_35) r_36) r_37) r_38) r_39) r_40) r_41) r_42) r_43) r_44) r_45) r_46) r_47) r_48) r_49) r_50) r_51) r_52) r_53) r_54) r_55) r_56) r_57) r_58) r_59) r_60) r_61) r_62) r_63) r_64) r_65) r_66) r_67) r_68) r_69) r_70) r_71) r_72) r_73) r_74) r_75) r_76) r_77) r_78) r_79) r_80) r_81) r_82) r_83) r_84) r_85) r_86

theorem R_all : ∀ t1, R t1 := by
  intro t1
  by_cases h : t1 < 87
  · exact R_below t1 h
  · exact R_vac (by simp only [q]; omega)

/-- Every sorted 4-tuple `a4 ≤ a3 ≤ a2 ≤ a1` with `2 a1 + a2 + a3 + a4 ≤ 1389` has a
witness `k`. -/
theorem witness (a1 a2 a3 a4 : Nat) (h4 : 1 ≤ a4) (h34 : a4 ≤ a3) (h23 : a3 ≤ a2)
    (h12 : a2 ≤ a1) (h0 : 2 * a1 + a2 + a3 + a4 ≤ 1389) :
    ∃ k, 2 ≤ k ∧ k ≤ 1387 ∧ 1 ≤ k * a1 % 1389 ∧ 1 ≤ k * a2 % 1389 ∧ 1 ≤ k * a3 % 1389 ∧
      1 ≤ k * a4 % 1389 ∧ k * a1 % 1389 + k * a2 % 1389 + k * a3 % 1389 + k * a4 % 1389 ≤ 1388 :=
  cover R_all a1 a2 a3 a4 h4 h34 h23 h12 h0

end LiuCert
