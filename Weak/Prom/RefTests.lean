/-
Weak/Prom: **the plan's §5 litmus rows as tests of the reference** (definitions only; the verdict theorems are in
`Weak/Prom/RefLitmus.lean`).

Sources: plan rev 7 §5, Table S §19.1 (text verdicts), §20 (fixed against `litmus-tests-riscv` @ `08728edc`, path
`tests/non-mixed-size/…` unless noted), §21 (row 26).  Where §20 names a repository test, the code is the
repository's (registers `xN` as written there); manual tests use the manual's ABI names (`mm-explanatory.adoc`
figure, line cited).  Locations: `x = 0x1000`, `y = 0x2000`, `z = 0x3000`, `a = 0x4000`, `b = 0x5000`,
`c = 0x6000`, `d = 0x7000` (the oracle's parser assigns the same addresses to the same names).  Initial memory 0
unless stated.  Branch/jump targets are absolute instruction indices within the hart.

ABI register numbers: t0 5, t1 6, t2 7, s0 8, s1 9, a0 10, a1 11, a2 12, a3 13, a4 14, a5 15, s2 18, s4 20, t3 28,
t4 29.
-/
import Weak.Prom.RefCheck

namespace Weak.Prom.Ref.Lit

open Weak.Prom.Ref

/-! ## The DSL -/

def X : Nat := 0x1000
def Y : Nat := 0x2000
def Z : Nat := 0x3000
def A : Nat := 0x4000
def B : Nat := 0x5000
def C : Nat := 0x6000
def D : Nat := 0x7000

def lw (rd rs1 : Nat) (off : Nat := 0) : Instr := .load 4 true rd rs1 off
def ld (rd rs1 : Nat) (off : Nat := 0) : Instr := .load 8 true rd rs1 off
def lh (rd rs1 : Nat) (off : Nat := 0) : Instr := .load 2 true rd rs1 off
def sw (rs2 rs1 : Nat) (off : Nat := 0) : Instr := .store 4 rs2 rs1 off
def sd (rs2 rs1 : Nat) (off : Nat := 0) : Instr := .store 8 rs2 rs1 off
def sh (rs2 rs1 : Nat) (off : Nat := 0) : Instr := .store 2 rs2 rs1 off
def sb (rs2 rs1 : Nat) (off : Nat := 0) : Instr := .store 1 rs2 rs1 off
def ori (rd rs1 imm : Nat) : Instr := .alui .or rd rs1 imm
def andi (rd rs1 imm : Nat) : Instr := .alui .and rd rs1 imm
def addi (rd rs1 imm : Nat) : Instr := .alui .add rd rs1 imm
def li (rd v : Nat) : Instr := .alui .add rd 0 v
def xor (rd rs1 rs2 : Nat) : Instr := .alu .xor rd rs1 rs2
def add (rd rs1 rs2 : Nat) : Instr := .alu .add rd rs1 rs2
def bne (rs1 rs2 tgt : Nat) : Instr := .br .ne rs1 rs2 tgt
def beq (rs1 rs2 tgt : Nat) : Instr := .br .eq rs1 rs2 tgt
def fence (pr pw sr sw : Bool) : Instr := .fence ⟨pr, pw, false, false, sr, sw, false, false⟩
def fRWRW : Instr := fence true true true true
def fRR : Instr := fence true false true false
def fRRW : Instr := fence true false true true
def fWW : Instr := fence false true false true
def fRWW : Instr := fence true true false true
def amoswapW (aq rl : Bool) (rd rs2 rs1 : Nat) : Instr := .amo .swap 4 aq rl rd rs2 rs1
def amoaddW (aq rl : Bool) (rd rs2 rs1 : Nat) : Instr := .amo .add 4 aq rl rd rs2 rs1
def amoorW (aq rl : Bool) (rd rs2 rs1 : Nat) : Instr := .amo .or 4 aq rl rd rs2 rs1
def lrW (rd rs1 : Nat) : Instr := .lr 4 false false rd rs1
def lrD (rd rs1 : Nat) : Instr := .lr 8 false false rd rs1
def scW (rd rs2 rs1 : Nat) (rl : Bool := false) : Instr := .sc 4 false rl rd rs2 rs1
def scD (rd rs2 rs1 : Nat) : Instr := .sc 8 false false rd rs2 rs1

/-- `n`-byte little-endian initial value `v` at `a`. -/
def ini (a v : Nat) (n : Nat := 8) : List (Nat × Nat) := (byteList v n).mapIdx (fun k b => (a + k, b))

def r (h reg v : Nat) : OC := .reg h reg v
def m4 (a v : Nat) : OC := .mem a 4 v
def ands : List OC → OC
  | [] => .tt
  | [p] => p
  | p :: ps => .and p (ands ps)

def mk (harts : List (List Instr)) (regs0 : List (List (Nat × Nat))) (img : List (Nat × Nat)) (cond : OC) :
    Test := ⟨harts, regs0, img, [], cond⟩

/-! ## Rows 1–6: the LB family -/

/-- Row 1, repo `BASIC_2_THREAD/LB`. ALLOWED. -/
def lb : Test := mk [[lw 5 6, sw 7 8], [lw 5 6, sw 7 8]]
  [[(6, X), (7, 1), (8, Y)], [(6, Y), (7, 1), (8, X)]] [] (ands [r 0 5 1, r 1 5 1])

/-- Row 2, LB+data+data (no repository counterpart, §20). FORBIDDEN. -/
def lbdd : Test := mk [[lw 5 6, sw 5 8], [lw 5 6, sw 5 8]]
  [[(6, X), (8, Y)], [(6, Y), (8, X)]] [] (ands [r 0 5 1, r 1 5 1])

/-- Row 3 = repo `BASIC_2_THREAD/LB+datas` (fake dependency `xor; ori`). FORBIDDEN. -/
def lbDatas : Test := mk [[lw 5 6, xor 7 5 5, ori 7 7 1, sw 7 8], [lw 5 6, xor 7 5 5, ori 7 7 1, sw 7 8]]
  [[(6, X), (8, Y)], [(6, Y), (8, X)]] [] (ands [r 0 5 1, r 1 5 1])

/-- Row 4, repo `BASIC_2_THREAD/LB+ctrls` (`bne` to the next instruction). FORBIDDEN. -/
def lbCtrls : Test := mk [[lw 5 6, bne 5 0 2, sw 7 8], [lw 5 6, bne 5 0 2, sw 7 8]]
  [[(6, X), (7, 1), (8, Y)], [(6, Y), (7, 1), (8, X)]] [] (ands [r 0 5 1, r 1 5 1])

/-- Row 4′, the `beq` (fall-through when the value is 1) variant §20 asks for (FC-4). FORBIDDEN. -/
def lbCtrlsBeq : Test := mk [[lw 5 6, beq 5 0 2, sw 7 8], [lw 5 6, beq 5 0 2, sw 7 8]]
  [[(6, X), (7, 1), (8, Y)], [(6, Y), (7, 1), (8, X)]] [] (ands [r 0 5 1, r 1 5 1])

/-- Row 5, manual `litmus_lb_lrsc` (mm-explanatory.adoc:932–948): init `0(s0)=1`, `0(s2)=1`;
H0 `ld a0,0(s0); lr a1,0(s1); sc a2,a0,0(s1); sd a2,0(s2)` ‖ H1 `ld a3,0(s2); sd a3,0(s0)`; doubleword LR/SC.
FORBIDDEN (a0=0, a3=0). -/
def lbLrsc : Test := mk [[ld 10 8, lrD 11 9, scD 12 10 9, sd 12 18], [ld 13 18, sd 13 8]]
  [[(8, X), (9, Y), (18, Z)], [(8, X), (18, Z)]] (ini X 1 ++ ini Z 1) (ands [r 0 10 0, r 1 13 0])

/-- Row 6, OOTA-42 (Promising'17): row 2's code. FORBIDDEN (a0=a1=42). -/
def oota42 : Test := { lbdd with cond := ands [r 0 5 42, r 1 5 42] }

/-! ## Rows 7–11b: MP -/

/-- Row 7, repo `BASIC_2_THREAD/MP`. ALLOWED. -/
def mp : Test := mk [[sw 5 6, sw 5 7], [lw 5 6, lw 7 8]]
  [[(5, 1), (6, X), (7, Y)], [(6, Y), (8, X)]] [] (ands [r 1 5 1, r 1 7 0])

/-- Row 8 = repo `SAFE/MP+fence.w.w+fence.r.rw` (§20: the repo has no `fence r,r` variant). FORBIDDEN. -/
def mpFF : Test := mk [[sw 5 6, fWW, sw 5 7], [lw 5 6, fRRW, lw 7 8]]
  [[(5, 1), (6, X), (7, Y)], [(6, Y), (8, X)]] [] (ands [r 1 5 1, r 1 7 0])

/-- Row 8′, the plan's `fence r,r` reader. FORBIDDEN. -/
def mpFFrr : Test := mk [[sw 5 6, fWW, sw 5 7], [lw 5 6, fRR, lw 7 8]]
  [[(5, 1), (6, X), (7, Y)], [(6, Y), (8, X)]] [] (ands [r 1 5 1, r 1 7 0])

/-- Row 9 = repo `SAFE/MP+fence.w.w+addr` (`xor x7,x5,x5; add x10,x9,x7; lw x8,0(x10)`). FORBIDDEN. -/
def mpFAddr : Test := mk [[sw 5 6, fWW, sw 5 7], [lw 5 6, xor 7 5 5, add 10 9 7, lw 8 10]]
  [[(5, 1), (6, X), (7, Y)], [(6, Y), (9, X)]] [] (ands [r 1 5 1, r 1 8 0])

/-- Row 10, MP+amo.rl+amo.aq: H0 `li t1,1; sw t1,(x); amoswap.w.rl x0,t1,(y)` ‖ H1 `amoswap.w.aq a0,x0,(y);
lw a1,(x)`. FORBIDDEN (a0=1, a1=0). -/
def mpAmoRlAq : Test := mk [[li 6 1, sw 6 8, amoswapW false true 0 6 9], [amoswapW true false 10 0 9, lw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 10 1, r 1 11 0])

/-- Row 11, MP+fence.rw.w-amo+amo-fence.r.rw: H0 `li t,1; sw t,(x); fence rw,w; amoswap.w x0,t,(y)` ‖
H1 `li t2,2; amoswap.w a0,t2,(y); fence r,rw; lw a1,(x)`. FORBIDDEN (a0=1, a1=0). -/
def mpFAmo : Test :=
  mk [[li 5 1, sw 5 8, fRWW, amoswapW false false 0 5 9], [li 7 2, amoswapW false false 10 7 9, fRRW, lw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 10 1, r 1 11 0])

/-- Row 11b, AMO-store-part+fence.r.rw: H0 `li t,1; amoswap.w a0,t,(y); fence r,rw; li t3,2; sw t3,(z)` ‖
H1 `lw b0,(z); fence r,r; lw b1,(y)`. FORBIDDEN (b0=2, b1=0). -/
def amoStorePart : Test :=
  mk [[li 5 1, amoswapW false false 10 5 9, fRRW, li 28 2, sw 28 18], [lw 10 18, fRR, lw 11 9]]
  [[(9, Y), (18, Z)], [(9, Y), (18, Z)]] [] (ands [r 1 10 2, r 1 11 0])

/-! ## Rows 12–20: SB and the manual's store-buffer and pipeline tests -/

/-- Row 12, repo `BASIC_2_THREAD/SB`. ALLOWED. -/
def sbT : Test := mk [[sw 5 6, lw 7 8], [sw 5 6, lw 7 8]]
  [[(5, 1), (6, X), (8, Y)], [(5, 1), (6, Y), (8, X)]] [] (ands [r 0 7 0, r 1 7 0])

/-- Row 13, repo `BASIC_2_THREAD/SB+fence.rw.rws`. FORBIDDEN. -/
def sbFF : Test := mk [[sw 5 6, fRWRW, lw 7 8], [sw 5 6, fRWRW, lw 7 8]]
  [[(5, 1), (6, X), (8, Y)], [(5, 1), (6, Y), (8, X)]] [] (ands [r 0 7 0, r 1 7 0])

/-- Row 14 = repo `HAND/SB+rfi-fence.r.rs` (manual `litms_sb_forward`, mm-explanatory.adoc:243–257). ALLOWED. -/
def sbFwd : Test := mk [[ori 5 0 1, sw 5 6, lw 7 6, fRR, lw 8 9], [ori 5 0 1, sw 5 6, lw 7 6, fRR, lw 8 9]]
  [[(6, X), (9, Y)], [(6, Y), (9, X)]] [] (ands [r 0 7 1, r 0 8 0, r 1 7 1, r 1 8 0])

/-- Row 15 = repo `HAND/PPOCA` (manual `litmus_ppoca` has a loop; the repo's is loop-free). ALLOWED. -/
def ppoca : Test :=
  mk [[sd 5 6, fWW, sd 5 7], [ld 5 6, bne 5 0 2, sd 7 8, ld 9 8, xor 10 9 9, add 13 12 10, ld 11 13]]
  [[(5, 1), (6, X), (7, Y)], [(6, Y), (7, 1), (8, Z), (12, X)]] [] (ands [r 1 5 1, r 1 9 1, r 1 11 0])

/-- Row 16, manual `litmus_datarfi` (mm-explanatory.adoc:993–1009): H0 `li t1,1; sw t1,0(s0); fence w,w;
sw t1,0(s1)` ‖ H1 `lw a0,0(s1); sw a0,0(s2); lw a1,0(s2); xor a2,a1,a1; add s0,s0,a2; lw a3,0(s0)`.
FORBIDDEN (a0=1, a3=0). -/
def datarfi : Test :=
  mk [[li 6 1, sw 6 8, fWW, sw 6 9], [lw 10 9, sw 10 18, lw 11 18, xor 12 11 11, add 8 8 12, lw 13 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y), (18, Z)]] [] (ands [r 1 10 1, r 1 13 0])

/-- Row 17, manual `litmus_datacoirfi` (mm-explanatory.adoc:1027–1044): H1 adds `sw t1,0(s2)` after the data
store. ALLOWED (a0=1, a3=0). -/
def datacoirfi : Test :=
  mk [[li 6 1, sw 6 8, fWW, sw 6 9],
      [li 6 1, lw 10 9, sw 10 18, sw 6 18, lw 11 18, xor 12 11 11, add 8 8 12, lw 13 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y), (18, Z)]] [] (ands [r 1 10 1, r 1 13 0])

/-- Row 17r = repo `HAND/MP+fence.w.w+data-wsi-rfi-addr`. ALLOWED. -/
def datacoirfiR : Test :=
  mk [[ori 5 0 1, sw 5 6, fWW, ori 7 0 1, sw 7 8],
      [lw 5 6, andi 7 5 128, ori 7 7 1, sw 7 8, ori 9 0 2, sw 9 8, lw 10 8, andi 11 10 128, add 14 13 11,
        lw 12 14]]
  [[(6, X), (8, Y)], [(6, Y), (8, Z), (13, X)]] [] (ands [.mem Z 4 2, r 1 5 1, r 1 10 2, r 1 12 0])

/-- Row 18, manual `litmus:addrdatarfi_no` (mm-explanatory.adoc:1069–1084): H0 `lw a0,0(s0); fence rw,rw;
sw s2,0(s1)` ‖ H1 `li t1,1; lw a1,0(s1); lw a2,0(a1); sw t1,0(s0)`; `s2 = t := z`. FORBIDDEN (a0=1, a1=t). -/
def addrpo : Test := mk [[lw 10 8, fRWRW, sw 18 9], [li 6 1, lw 11 9, lw 12 11, sw 6 8]]
  [[(8, X), (9, Y), (18, Z)], [(8, X), (9, Y)]] [] (ands [r 0 10 1, r 1 11 Z])

/-- Row 18r = repo `HAND/LB+fence.r.rw+addr-po`. FORBIDDEN. -/
def addrpoR : Test :=
  mk [[lw 5 6, fRRW, ori 7 0 1, sw 7 8], [lw 5 6, xor 7 5 5, add 10 9 7, lw 8 10, ori 11 0 1, sw 11 12]]
  [[(6, X), (8, Y)], [(6, Y), (9, Z), (12, X)]] [] (ands [r 0 5 1, r 1 5 1])

/-- Row 19, manual `frirfi` (mm-explanatory.adoc:505–521). ALLOWED (a0=1, a1=2, a2=0). -/
def frirfi : Test :=
  mk [[li 6 1, sw 6 8, fWW, sw 6 9], [li 7 2, lw 10 9, sw 7 9, lw 11 9, xor 28 11 11, add 8 8 28, lw 12 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 10 1, r 1 11 2, r 1 12 0])

/-- Row 20 = repo `HAND/RSW` (manual `litmus-rsw` with `fence rw,rw`). ALLOWED. -/
def rsw : Test :=
  mk [[ori 5 0 1, sw 5 6, fRWRW, ori 7 0 1, sw 7 8],
      [lw 5 6, xor 7 5 5, add 10 9 7, lw 8 10, lw 11 9, xor 12 11 11, add 15 14 12, lw 13 15]]
  [[(6, X), (8, Y)], [(6, Y), (9, Z), (14, X)]] [] (ands [r 1 5 1, r 1 13 0])

/-! ## Rows 21–25 -/

/-- Row 21, repo `BASIC_2_THREAD/2+2W`. ALLOWED. -/
def w22 : Test := mk [[sw 5 6, sw 7 8], [sw 5 6, sw 7 8]]
  [[(5, 2), (6, X), (7, 1), (8, Y)], [(5, 2), (6, Y), (7, 1), (8, X)]] [] (ands [m4 X 2, m4 Y 2])

/-- Row 21′, repo `SAFE/2+2W+fence.w.ws`. FORBIDDEN. -/
def w22F : Test := mk [[sw 5 6, fWW, sw 7 8], [sw 5 6, fWW, sw 7 8]]
  [[(5, 2), (6, X), (7, 1), (8, Y)], [(5, 2), (6, Y), (7, 1), (8, X)]] [] (ands [m4 X 2, m4 Y 2])

/-- Row 22 CoWW, repo `CO/CoWW` (`exists (not (x=2))`). FORBIDDEN. -/
def coWW : Test := mk [[sw 5 6, sw 7 6]] [[(5, 1), (6, X), (7, 2)]] [] (.not (m4 X 2))

/-- Row 22 CoWR0, repo `CO/CoWR0` (`exists (not (0:x7=1 /\ x=1))`). FORBIDDEN. -/
def coWR0 : Test := mk [[sw 5 6, lw 7 6]] [[(5, 1), (6, X)]] [] (.not (ands [r 0 7 1, m4 X 1]))

/-- Row 22 CoWR, repo `HAND/CoWR` (`~exists (x=1 /\ 0:x7=2)`, doublewords). FORBIDDEN. -/
def coWR : Test := mk [[sd 5 6, ld 7 6], [sd 5 6]] [[(5, 1), (6, X)], [(5, 2), (6, X)]] []
  (ands [.mem X 8 1, r 0 7 2])

/-- Row 22 CoRW1, repo `CO/CoRW1`. FORBIDDEN. -/
def coRW1 : Test := mk [[lw 5 6, sw 7 6]] [[(6, X), (7, 1)]] [] (.not (ands [r 0 5 0, m4 X 1]))

/-- Row 22 CoRW2, repo `CO/CoRW2`. FORBIDDEN. -/
def coRW2 : Test := mk [[sw 5 6], [lw 5 6, sw 7 6]] [[(5, 1), (6, X)], [(6, X), (7, 2)]] []
  (.not (.or (.and (r 1 5 0) (.or (m4 X 2) (m4 X 1))) (.and (r 1 5 1) (m4 X 2))))

/-- Row 22 CoRR, repo `CO/CoRR`. FORBIDDEN. -/
def coRR : Test := mk [[sw 5 6], [lw 5 6, lw 7 6]] [[(5, 1), (6, X)], [(6, X)]] []
  (.not (.and (m4 X 1) (.or (.and (r 1 5 0) (.or (r 1 7 0) (r 1 7 1))) (.and (r 1 5 1) (r 1 7 1)))))

/-- Row 22 CoRR2 (SLR §2.3, four harts): `x:=1 ‖ x:=2 ‖ a:=x; b:=x ‖ c:=x; d:=x`, outcome a=1,b=2,c=2,d=1.
FORBIDDEN. -/
def coRR2 : Test := mk [[li 5 1, sw 5 6], [li 5 2, sw 5 6], [lw 10 6, lw 11 6], [lw 10 6, lw 11 6]]
  [[(6, X)], [(6, X)], [(6, X)], [(6, X)]] [] (ands [r 2 10 1, r 2 11 2, r 3 10 2, r 3 11 1])

/-- Row 23, Par-Inc: `amoadd.w _,1,(x)` ‖ same. FORBIDDEN (final x=1). -/
def parInc : Test := mk [[li 5 1, amoaddW false false 10 5 6], [li 5 1, amoaddW false false 10 5 6]]
  [[(6, X)], [(6, X)]] [] (m4 X 1)

/-- Row 24, repo `SAFE/ISA2+fence.rw.rws`. FORBIDDEN. -/
def isa2F : Test := mk [[sw 5 6, fRWRW, sw 5 7], [lw 5 6, fRWRW, sw 7 8], [lw 5 6, fRWRW, lw 7 8]]
  [[(5, 1), (6, X), (7, Y)], [(6, Y), (7, 1), (8, Z)], [(6, Z), (8, X)]] [] (ands [r 1 5 1, r 2 5 1, r 2 7 0])

/-- Row 24, plain ISA2 (repo `SF_THESIS/BASIC/ISA2`, no model result). ALLOWED (text verdict). -/
def isa2 : Test := mk [[sw 5 6, sw 5 7], [lw 5 6, sw 7 8], [lw 5 6, lw 7 8]]
  [[(5, 1), (6, X), (7, Y)], [(6, Y), (7, 1), (8, Z)], [(6, Z), (8, X)]] [] (ands [r 1 5 1, r 2 5 1, r 2 7 0])

/-- Row 24, repo `SAFE/WRC+fence.rw.rws`. FORBIDDEN. -/
def wrcF : Test := mk [[sw 5 6], [lw 5 6, fRWRW, sw 7 8], [lw 5 6, fRWRW, lw 7 8]]
  [[(5, 1), (6, X)], [(6, X), (7, 1), (8, Y)], [(6, Y), (8, X)]] [] (ands [r 1 5 1, r 2 5 1, r 2 7 0])

/-- Row 24, plain WRC (repo `SF_THESIS/BASIC/WRC`, no model result). ALLOWED (text verdict). -/
def wrc : Test := mk [[sw 5 6], [lw 5 6, sw 7 8], [lw 5 6, lw 7 8]]
  [[(5, 1), (6, X)], [(6, X), (7, 1), (8, Y)], [(6, Y), (8, X)]] [] (ands [r 1 5 1, r 2 5 1, r 2 7 0])

/-- Row 25, repo `SAFE/IRIW+ctrlfenceis` (ctrl + fence.i order no loads). ALLOWED. -/
def iriwCtrlFi : Test :=
  mk [[sw 5 6], [lw 5 6, bne 5 0 2, .fencei, lw 7 8], [sw 5 6], [lw 5 6, bne 5 0 2, .fencei, lw 7 8]]
  [[(5, 1), (6, X)], [(6, X), (8, Y)], [(5, 1), (6, Y)], [(6, Y), (8, X)]] []
  (ands [r 1 5 1, r 1 7 0, r 3 5 1, r 3 7 0])

/-- Row 25, plain IRIW (no repository test). ALLOWED (text verdict). -/
def iriw : Test :=
  mk [[sw 5 6], [lw 5 6, lw 7 8], [sw 5 6], [lw 5 6, lw 7 8]]
  [[(5, 1), (6, X)], [(6, X), (8, Y)], [(5, 1), (6, Y)], [(6, Y), (8, X)]] []
  (ands [r 1 5 1, r 1 7 0, r 3 5 1, r 3 7 0])

/-- Row 25, repo `SAFE/IRIW+fence.r.rws`. FORBIDDEN. -/
def iriwF : Test :=
  mk [[sw 5 6], [lw 5 6, fRRW, lw 7 8], [sw 5 6], [lw 5 6, fRRW, lw 7 8]]
  [[(5, 1), (6, X)], [(6, X), (8, Y)], [(5, 1), (6, Y)], [(6, Y), (8, X)]] []
  (ands [r 1 5 1, r 1 7 0, r 3 5 1, r 3 7 0])

/-! ## Rows 28–37, 41 -/

/-- Row 28, MP+amo-data+fence.r.r: H0 `li t2,2; amoswap.w a0,t2,(x); addi t,a0,5; sw t,(y)` ‖
H1 `lw a1,(y); fence r,r; lw a2,(x)`. FORBIDDEN (a1=5, a2=0). -/
def mpAmoData : Test := mk [[li 7 2, amoswapW false false 10 7 8, addi 5 10 5, sw 5 9], [lw 11 9, fRR, lw 12 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 11 5, r 1 12 0])

/-- Row 28c, MP+amo-ctrl+fence.r.r: H0 `li t,2; amoswap.w a0,t,(x); bnez a0,L; L: li t1,1; sw t1,(y)`.
FORBIDDEN (a1=1, a2=0). -/
def mpAmoCtrl : Test :=
  mk [[li 5 2, amoswapW false false 10 5 8, bne 10 0 3, li 6 1, sw 6 9], [lw 11 9, fRR, lw 12 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 11 1, r 1 12 0])

/-- Row 29, LB+amo-po: H0 `li t,2; amoswap.w a0,t,(x); li t1,1; sw t1,(y)` ‖ H1 `lw a1,(y); sw a1,(x)`.
ALLOWED (a1=1, a0=1). -/
def lbAmoPo : Test := mk [[li 5 2, amoswapW false false 10 5 8, li 6 1, sw 6 9], [lw 11 9, sw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 11 1, r 0 10 1])

/-- Row 30, LB+amo-ad: init x=1. H0 `lw a0,(y); li t,0x41; amoswap.w x0,t,(x)` ‖ H1 `lw a1,(x); sw a1,(y)`.
ALLOWED (a0=a1=0x41). -/
def lbAmoAd : Test := mk [[lw 10 9, li 5 0x41, amoswapW false false 0 5 8], [lw 11 8, sw 11 9]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] (ini X 1 4) (ands [r 0 10 0x41, r 1 11 0x41])

/-- Row 31, LR;SC: `lr.w a0,(x); sc.w a1,a2,(x)`. ALLOWED (a1=0). -/
def lrsc : Test := mk [[lrW 10 8, scW 11 12 8]] [[(8, X), (12, 7)]] [] (r 0 11 0)

/-- Row 31b, LR;ld;SC: `lr.w a0,(x); ld t,(y); sc.w a1,a2,(x)`. ALLOWED (a1=0). -/
def lrldsc : Test := mk [[lrW 10 8, ld 5 9, scW 11 12 8]] [[(8, X), (9, Y), (12, 7)]] [] (r 0 11 0)

/-- Row 32 (= 26j), mixed-size SCA: A `sb 1,(x)` ‖ B `sh 0x0202,(x)` ‖ C `lh a0,(x)`.
FORBIDDEN (a0=0x0201 ∧ final byte x = 0x02). -/
def mixSca : Test := mk [[sb 5 8], [sh 5 8], [lh 10 8]] [[(5, 1), (8, X)], [(5, 0x0202), (8, X)], [(8, X)]] []
  (ands [r 2 10 0x0201, .mem X 1 2])

/-- Rows 35a–d, manual `litmus_lrsdsc` (mm-explanatory.adoc:396–409). ALLOWED (t3=0). -/
def lrsdsc_a : Test := mk [[lrD 10 8, sd 6 8, scD 28 7 8]] [[(8, X), (6, 1), (7, 2)]] [] (r 0 28 0)
def lrsdsc_b : Test := mk [[lrD 10 8, sw 6 8 4, scD 28 7 8]] [[(8, X), (6, 1), (7, 2)]] [] (r 0 28 0)
def lrsdsc_c : Test := mk [[lrW 10 8, sw 6 8 4, scW 28 7 8]] [[(8, X), (6, 1), (7, 2)]] [] (r 0 28 0)
def lrsdsc_d : Test := mk [[lrW 10 8, sw 6 8 4, addi 8 8 8, scW 28 7 8]] [[(8, X), (6, 1), (7, 2)]] [] (r 0 28 0)

/-- Row 36, LR;AMO;SC: `lr.w a0,(x); li t4,1; amoadd.w t0,t4,(y); sc.w a1,a2,(x)`. ALLOWED (a1=0). -/
def lrAmoSc : Test := mk [[lrW 10 8, li 29 1, amoaddW false false 5 29 9, scW 11 12 8]]
  [[(8, X), (9, Y), (12, 7)]] [] (r 0 11 0)

/-- Row 37, LR;SC-fail;SC: `lr.w a0,(x); sc.w a1,a2,(x); sc.w a3,a4,(x)`. FORBIDDEN (a1=1 ∧ a3=0). -/
def lrScSc : Test := mk [[lrW 10 8, scW 11 12 8, scW 13 14 8]] [[(8, X), (12, 7), (14, 9)]] []
  (ands [r 0 11 1, r 0 13 0])

/-- Row 41, LB+misa (M-mode, no CSR is written): H0 `ld a0,(x); csrr a0,misa; sd a0,(y)` ‖ H1 `ld a1,(y);
sd a1,(x)`; `misa = M`. ALLOWED (both loads = M). -/
def misaV : Nat := 0x101105
def lbMisa : Test := mk [[ld 10 8, .csrr 10 misaV, sd 10 9], [ld 11 9, sd 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 0 10 misaV, r 1 11 misaV])

/-! ## Rows 52–61 (Table S §19.1, new rows) -/

/-- Row 52, write subsumption (mm-explanatory.adoc:1724–1755): H0 `li t1,3; li t2,1; sw t1,0(s0); fence w,w;
sw t2,0(s1)` ‖ H1 `li t3,2; lw a0,0(s1); sw a0,0(s0); sw t3,0(s0)`. FORBIDDEN (a0=1 ∧ final (s0)=3). -/
def wsub : Test := mk [[li 6 3, li 7 1, sw 6 8, fWW, sw 7 9], [li 28 2, lw 10 9, sw 10 8, sw 28 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 10 1, m4 X 3])

/-- Row 53, ARM-weak (Promising'17, three harts). FORBIDDEN (a0=1). -/
def armWeak : Test := mk [[lw 10 8, li 5 1, sw 5 8], [lw 11 8, sw 11 9], [lw 12 9, sw 12 8]]
  [[(8, X)], [(8, X), (9, Y)], [(8, X), (9, Y)]] [] (r 0 10 1)

/-- Row 54, LBa (Promising'17): H0 `amoor.w.aq a0,x0,(x); li t,1; sw t,(y)` ‖ H1 `lw b,(y); sw b,(x)`.
FORBIDDEN (a0=1). -/
def lbAcq : Test := mk [[amoorW true false 10 0 8, li 5 1, sw 5 9], [lw 11 9, sw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (r 0 10 1)

/-- Row 55, LBr (Promising'17): H0 `lw a0,(x); li t,1; amoswap.w.rl x0,t,(y)` ‖ H1 `lw b,(y); sw b,(x)`.
FORBIDDEN (a0=1). -/
def lbRel : Test := mk [[lw 10 8, li 5 1, amoswapW false true 0 5 9], [lw 11 9, sw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (r 0 10 1)

/-- Row 56, Upd-Stuck (Promising'17): H0 `lw a,(x); li t1,1; amoadd.w b,t1,(z); addi t,b,1; sw t,(y)` ‖
H1 `lw r,(y); sw r,(x); li t1,1; amoadd.w x0,t1,(z)`. ALLOWED (a=1 ∧ b=0). -/
def updStuck : Test :=
  mk [[lw 10 8, li 6 1, amoaddW false false 11 6 18, addi 5 11 1, sw 5 9],
      [lw 12 9, sw 12 8, li 6 1, amoaddW false false 0 6 18]]
  [[(8, X), (9, Y), (18, Z)], [(8, X), (9, Y), (18, Z)]] [] (ands [r 0 10 1, r 0 11 0])

/-- Row 57, COH (Promising'17): `sw 1,(x); lw a,(x)` ‖ `sw 2,(x); lw b,(x)`. FORBIDDEN (a=2 ∧ b=1). -/
def coh : Test := mk [[li 5 1, sw 5 8, lw 10 8], [li 5 2, sw 5 8, lw 10 8]] [[(8, X)], [(8, X)]] []
  (ands [r 0 10 2, r 1 10 1])

/-- Row 58, SEQ (XMM): H0 `lw a,(x); li t,1; beq a,t,L; sw t,(x); L: lw u,(x); sw u,(y)` ‖ H1 `lw v,(y);
sw v,(x)`. FORBIDDEN (a=1). -/
def seqT : Test := mk [[lw 10 8, li 5 1, beq 10 5 4, sw 5 8, lw 11 8, sw 11 9], [lw 12 9, sw 12 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (r 0 10 1)

/-- Row 59, LBfd (XMM/Promising'17): H0 `lw a,(x); bnez a,L1; li t,1; sw t,(y); j L2; L1: li t,1; sw t,(y);
L2:` ‖ H1 `lw b,(y); sw b,(x)`. FORBIDDEN (a=b=1). -/
def lbfd : Test :=
  mk [[lw 10 8, bne 10 0 5, li 5 1, sw 5 9, .jmp 7, li 5 1, sw 5 9], [lw 11 9, sw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 0 10 1, r 1 11 1])

/-- Row 60, RNG (SLR): H0 `lw a,(x); addi t,a,1; sw t,(y)` ‖ H1 `lw b,(y); sw b,(x)`. FORBIDDEN (a≠0). -/
def rng : Test := mk [[lw 10 8, addi 5 10 1, sw 5 9], [lw 11 9, sw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (.not (r 0 10 0))

/-- Row 61, Disjoint-Lists (SLR): `ld r1,(a); sd a,0(r1)` ‖ `ld r2,(b); sd b,0(r2)`; init `[a] = c`,
`[b] = d` (disjoint cells). FORBIDDEN (r1=&b ∧ r2=&a). -/
def disjLists : Test := mk [[ld 10 8, sd 8 10], [ld 11 9, sd 9 11]] [[(8, A)], [(9, B)]] (ini A C ++ ini B D)
  (ands [r 0 10 B, r 1 11 A])

/-! ## Row 26: the mixed-size tests (Table S §21) -/

/-- 26a, repo `SF_THESIS/HAND/MP+sis`. FORBIDDEN. -/
def mix26a : Test := mk [[sh 2 1], [lh 2 1]] [[(1, X), (2, 0x1110)], [(1, X)]] [] (r 1 2 0x1100)

/-- 26b, repo `SF_THESIS/HAND/MP+fence.rw.rw+si`. FORBIDDEN. -/
def mix26b : Test := mk [[sb 1 4, fRWRW, sb 2 4 1], [lh 2 4]] [[(4, X), (1, 0x10), (2, 0x11)], [(4, X)]] []
  (r 1 2 0x1100)

/-- 26c, repo `SF_THESIS/HAND/WRR+2W+sis`. FORBIDDEN. -/
def mix26c : Test := mk [[sb 2 1], [lh 2 1, lh 3 1], [sh 2 1]] [[(1, X), (2, 0x20)], [(1, X)], [(1, X), (2, 0x1110)]]
  [] (ands [.mem X 2 0x1120, r 1 2 0x0020, r 1 3 0x1120])

/-- 26d, repo `SF_THESIS/HAND/MIX1`: `sw 0x13121110,0(x); sb 0x22,2(x); lw a0,0(x)`. ALLOWED (a0=0x13221110),
and the only outcome. -/
def mix26d : Test := mk [[sw 2 1, sb 3 1 2, lw 4 1]] [[(1, X), (2, 0x13121110), (3, 0x22)]] [] (r 0 4 0x13221110)
def mix26dNot : Test := { mix26d with cond := .not (r 0 4 0x13221110) }

/-- 26e, manual rsw1 (mm-explanatory.adoc:1782–1795). ALLOWED. -/
def mix26e : Test :=
  mk [[lw 10 8, fRWRW, sw 6 9],
      [lw 11 9, amoswapW false true 12 6 18, ld 13 18, lw 14 18 4, xor 15 14 14, add 8 8 15, sw 6 8]]
  [[(8, X), (9, Y), (6, 1)], [(8, X), (9, Y), (18, Z), (6, 1)]] []
  (ands [r 0 10 1, r 1 11 1, r 1 12 0, r 1 13 1, r 1 14 0])

/-- 26f, manual rsw2 (mm-explanatory.adoc:1798–1809). ALLOWED. -/
def mix26f : Test :=
  mk [[lw 10 8, fRWRW, sw 6 9], [ld 11 9, lw 12 9 4, xor 13 12 12, add 8 8 13, sw 6 8]]
  [[(8, X), (9, Y), (6, 1)], [(8, X), (9, Y), (6, 1)]] [] (ands [r 0 10 1, r 1 11 1, r 1 12 0])

/-- 26g, manual rsw3 (mm-explanatory.adoc:1812–1824). ALLOWED. -/
def mix26g : Test :=
  mk [[lw 10 8, fRWRW, sw 6 9], [sw 6 9 4, ld 11 9, lw 12 9 4, xor 13 12 12, add 8 8 13, sw 6 8]]
  [[(8, X), (9, Y), (6, 1)], [(8, X), (9, Y), (6, 1)]] [] (ands [r 0 10 1, r 1 11 0x100000001, r 1 12 1])

/-- 26h, repo `mixed-size/HAND/LR-SC-mixed1` (`~exists`). FORBIDDEN. -/
def mix26h : Test :=
  mk [[lrD 5 6, ori 7 0 1, scW 8 7 6], [lrD 5 6, ori 7 0 1, addi 9 6 4, scW 8 7 9]] [[(6, X)], [(6, X)]] []
  (ands [.mem X 8 0x100000001, r 0 5 0, r 0 8 0, r 1 5 0, r 1 8 0])

/-- 26i, repo `mixed-size/HAND/LR-SC-mixed2` (`~exists`). FORBIDDEN. -/
def mix26i : Test :=
  mk [[lrD 5 6, ori 7 0 1, sw 7 6, scW 8 7 9 true], [lrD 5 6, ori 7 0 1, sw 7 6 4, scW 8 7 9 true]]
  [[(6, X), (9, Y)], [(6, X), (9, Z)]] []
  (ands [.mem X 8 0x100000001, m4 Y 1, m4 Z 1, r 0 5 0, r 0 8 0, r 1 5 0, r 1 8 0])

/-! ## Non-vacuity: every test has SOME execution (the FORBIDDEN verdicts are not vacuous) -/

def anyOutcome (T : Test) : Test := { T with cond := .tt }

end Weak.Prom.Ref.Lit
