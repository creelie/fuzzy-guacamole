# Writes LiuIndex/Check/Defs.lean: the kernel checker (core Lean only) and its packed constants.
import sys
q, B, w = 1389, 8, 17
L = B**4
def dig(i, l): return l // B**i % B
def pk(f): 
    x = 0
    for l in range(L): x |= f(l) << (w*l)
    return x
def lit(x): return "0x%x" % x
out = []
P = out.append
P("""/-
Kernel checker for the non-membership 1389 ∉ I_{4,wps}.
Core Lean only, so that the certificate modules build without Mathlib.
A box is a 8×8×8×8 block of tuples (a1,a2,a3,a4), a_i = x_i + d_i with
x_i = 1 + 8 t_i and 0 ≤ d_i < 8. Lane ℓ = d1 + 8 d2 + 64 d3 + 512 d4 of a
packed vector holds a 17-bit value.
-/
namespace LiuCheck

def q : Nat := 1389
def B : Nat := 8
def L : Nat := 4096
def w : Nat := 17

/-- `pk f n` packs the values `f 0, …, f (n-1)` into lanes of width `w`. -/
def pk (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j ih => ih + f j * 2 ^ (w * j)) n

/-- Digit `i` of a lane index (the offset `d_{i+1}`). -/
def dig (i l : Nat) : Nat := l / B ^ i % B
""")
P("def Ones : Nat := " + lit(pk(lambda l: 1)))
for i in range(4):
    P("def D%d : Nat := " % (i+1) + lit(pk(lambda l, i=i: dig(i, l))))
P("def Dsum : Nat := " + lit(pk(lambda l: sum(dig(i, l) for i in range(4)))))
P("def DD : Nat := " + lit(pk(lambda l: 2*dig(0, l) + dig(1, l) + dig(2, l) + dig(3, l))))
for i in range(4):
    for d in range(1, B):
        P("def SM%d_%d : Nat := " % (i, d) + lit(pk(lambda l, i=i, d=d: 1 if dig(i, l) >= d else 0)))
P("")
# selection of a step mask; δ ≥ 8 gives 0, δ = 0 gives Ones
for i in range(4):
    s = "def SM%d (δ : Nat) : Nat :=\n  " % i
    s += "bif Nat.ble 8 δ then 0 else bif Nat.beq δ 0 then Ones else "
    for d in range(1, B):
        s += "bif Nat.beq δ %d then SM%d_%d else " % (d, i, d)
    s += "0"
    P(s)
P("""def SM (i δ : Nat) : Nat :=
  bif Nat.beq i 0 then SM0 δ else bif Nat.beq i 1 then SM1 δ else
  bif Nat.beq i 2 then SM2 δ else bif Nat.beq i 3 then SM3 δ else 0

/-- Shifted residue offset of a box corner: `(k x - 1) mod q`. -/
def cOf (k x : Nat) : Nat := (k * x + q - 1) % q
/-- Number of multiples of `q` crossed along an edge of the box. -/
def Jof (k c : Nat) : Nat := (c + k * (B - 1)) / q

/-- Lane ℓ: `(c + k * dig i ℓ) / q`, as a sum of step masks. -/
def flr (i k c J : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => ih + SM i (((j + 1) * q - c + k - 1) / k)) J

/-- Lane ℓ is `1` iff `∑ ((k a_i - 1) mod q + 1) ≤ q - 1` at the tuple of lane ℓ. -/
def goodVec (x1 x2 x3 x4 k : Nat) : Nat :=
  let c1 := cOf k x1
  let c2 := cOf k x2
  let c3 := cOf k x3
  let c4 := cOf k x4
  let F := flr 0 k c1 (Jof k c1) + flr 1 k c2 (Jof k c2) + flr 2 k c3 (Jof k c3) +
    flr 3 k c4 (Jof k c4)
  let X := (c1 + c2 + c3 + c4 + 4 + 2 ^ 16 - q) * Ones + k * Dsum - q * F
  Ones - ((X >>> 16) &&& Ones)

/-- Bit 15 of every lane, moved to bit 0. -/
def hiFlag (Y : Nat) : Nat := (Y >>> 15) &&& Ones

/-- Lane ℓ is `1` iff the tuple of lane ℓ satisfies `a0 ≥ a1 ≥ a2 ≥ a3 ≥ a4`. -/
def validVec (x1 x2 x3 x4 : Nat) : Nat :=
  hiFlag ((2 ^ 15 + x1 - x2) * Ones + D1 - D2) &&&
  hiFlag ((2 ^ 15 + x2 - x3) * Ones + D2 - D3) &&&
  hiFlag ((2 ^ 15 + x3 - x4) * Ones + D3 - D4) &&&
  hiFlag ((2 ^ 15 + q - (2 * x1 + x2 + x3 + x4)) * Ones - DD)

def kOK (k : Nat) : Bool := Nat.ble 2 k && Nat.ble k (q - 2)

def covOf (x1 x2 x3 x4 : Nat) : List Nat → Nat
  | [] => 0
  | k :: ks => goodVec x1 x2 x3 x4 k ||| covOf x1 x2 x3 x4 ks

/-- Every sorted tuple of the box is covered by one of the listed `k`. -/
def boxOK (x1 x2 x3 x4 : Nat) (ks : List Nat) : Bool :=
  ks.all kOK && Nat.beq (validVec x1 x2 x3 x4 &&& (Ones - covOf x1 x2 x3 x4 ks)) 0

/-- Read `n` base-2048 digits from the stream `s`. -/
def takeKs : Nat → Nat → List Nat × Nat
  | 0, s => ([], s)
  | n + 1, s => let r := takeKs n (s / 2048); (s % 2048 :: r.1, r.2)

/-- The boxes `(t3, t4)` with `lo ≤ t3 < hi` checked for a pair `(t1, t2)`. -/
def boxesOf (t1 t2 lo hi : Nat) : List (Nat × Nat) :=
  ((List.range' lo (hi - lo)).flatMap fun t3 => (List.range (t3 + 1)).map fun t4 => (t3, t4)).filter
    fun p => Nat.ble (2 * (1 + 8 * t1) + (1 + 8 * t2) + (1 + 8 * p.1) + (1 + 8 * p.2)) q

/-- Check the boxes in order; each takes a count and that many `k` from the stream. -/
def runBoxes (t1 t2 : Nat) : List (Nat × Nat) → Nat → Bool
  | [], _ => true
  | p :: ps, s =>
    let r := takeKs (s % 2048) (s / 2048)
    boxOK (1 + 8 * t1) (1 + 8 * t2) (1 + 8 * p.1) (1 + 8 * p.2) r.1 && runBoxes t1 t2 ps r.2

def run12 (t1 t2 lo hi s : Nat) : Bool := runBoxes t1 t2 (boxesOf t1 t2 lo hi) s

end LiuCheck
""")
open(sys.argv[1], "w").write("\n".join(out))
