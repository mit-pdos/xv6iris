/-
Weak: **THE WHOLE-SEGMENT WPd of Theorem 2** — hart `i`'s inlined allocpid inside xv6's REAL
`allocproc`, `allocproc + 0x38 .. + 0x9a` (the terminal `c.sw a5,24(s1)`), as ONE positional CPS
WPd at the joint instance Ixv6 (`AxSpinX2.xG L GT nm` / `xv6Pol GT`), interrupts off
(`ctrlOkSW`), warm TLB, on the row family of `AxSpinT2a` — and the PRIVATE STORE FLOW
`FstMPriv` that discharges `wpdAllocpidCs`'s `Opid` premise (Q-T2-4).  Theorem 2 design
(`notes/weak-lb-thm2-design.md`) §C.3, §D row `AxSpinApA`.  NEW Lean file (no Rocq source).

## What this file proves

§1 `FstMPriv L GT nm HL Hcons i pa n` — `FstM (dokAtP pa n) i (fun _ _ => True)`: a store of
   hart `i` to its OWN private bytes `pa .. pa + n` (`priv L _ i`) is `fxPrivWrite`'s flow (writer
   = owner, WOK), given the row fact `rowWle row pa n`.  (AxSpinE5's `FstSlot` for any width.)
§2 the two instructions after `jal release` (+ 0x98 `c.li a5,1`, + 0x9a `c.sw a5,24(s1)`):
   `ap98`/`ap9a`, their `TokC` decodes (`AxSpinApA.tkc98/tkc9a`, kernel-walk decode as
   AxSpinAp3/Ap5) and `textOkB` facts from the NEW text premise `AxSpinApA.tailText`.
§3–5 layout numbers (`AxSpinApA.Lay`, `AxSpinApA.nums`), `ofInt` address arithmetic (the slot
   addresses every callee computes from `sp = S`: `AxSpinApA.aA24 … aMm0`), and THE WRITES OF THE
   FAMILY `AxSpinApA.segWr`: every write of a row in `allocFull` is a stack spill, a cpu-field
   store, the lock word (spins / releasing store), `lk->cpu` (acquire's / release's store), the
   nextpid store or one of `p`'s fields — BY POSITION.  Consequences: `npOnly` (Ap9's `Hone`),
   `npBefore` (Ap9's `Hpo`), `lkBetween` (Rl4b's `nolk`), `clbBetween` (Rl4b's no lk->cpu write
   between acquire's store and release's holding read), `wle4`, `privNe`.
§6 the hypothesis bundle `AxSpinApA.Hyp L GT σi T i q S p` (row family, pins, layout, the
   translation premise `AxSpinApA.MapOk`, the eight text premises, `textFixed`) and the premise
   bundles of the callees from it (`AxSpinApA.slot`/`fld`/`dat`, `alldjOf`/`slotsDisjOf`).
§7 THE PIECES, composed by continuation:
   `AxSpinApA.segRel` — + 0x94 `jal release` (XxReg) → `wpdRelease` (Rl4b; ret = + 0x98) →
     `c.li` (XxReg) → `c.sw` (`XxStF` with `FstMPriv 4` at `p + 24`) → row end `t2Len q`;
   `AxSpinApA.segCs` — from acquire's return (+ 0x44, row `t2KBd q`): `wpdAllocpidCs` (Ap9) with
     anchor `e := (i, t2KA q)` (`e ∈ lobp (i, t2KBd q)` by `AxSpinRl2.lobpAcq`, ppo rule 5 =
     `acqGob`) and `Opid := FstMPriv 4` at `p + 48`, then `segRel`;
   **`wpdAllocpidSeg`** — + 0x38 `auipc a0`, + 0x3c `addi a0` (`a0 = &pid_lock`), + 0x40 `jal
     acquire` (XxReg ×3) → `AxSpinAq2.wpdAcquire` (ret = + 0x44) → `segCs`.  Continuation
     `AxSpinApA.KSeg` at the row end (`PC = allocproc + 0x9c`): ∃ w, `a3 = sext32 w`,
     `pidOf = some (wbytes 4 w)`, the TLB, and the annotations `(i, t2KBd q) ↦ₐ ⌜npSrc …⌝`,
     `(i, t2KBd q + 65) ↦ₐ FRAG nm w` (minted at nextpid's write inside `wpdAllocpidCs`).
§8 PAST THE ROW END: `AxSpinApA.wpdEndAnn` / `wpdEnd2` — at a position `≥ LEN` every program
   state's WPd holds for any post that follows from owned annotations (Löb over the admin steps
   and wires; `annotAgreeBig` + `AxSpinProt7.readbackBig` at the post).
§9 **`wpdAllocpidSegS`** — `wpdAllocpidSeg` closed by §8: `WPd {{ AxSpinApA.t2PostS }}` from
   + 0x38; `AxSpinApA.wpdAllocpidSegE` from `entryOk`; `AxSpinApA.hypXv6` (the `Hyp` at the real
   layout `xlayXv6` from `T2LayHyp`); the joint twin `AxSpinApA.t2JointS` (`t2PhiS`, `t2ConclS`).

## The `a3` conjunct (FINDING; see `PROGRESS-AxSpinApA.md`)

`AxSpinT2a.t2Post` asks, at EVERY non-mid state the WPd reaches at the row end, `a3 = sext32 w`.
Past the terminal store the hart keeps executing allocproc (+ 0x9c `jal kalloc`, kalloc's
`c.addi sp`, then `c.sdsp ra` whose write has no row item), and `wpdMPreStepDef`'s row-end clause
demands the post at each of those states.  Register-only steps past the row end need an
`XxReg` at `k = LEN` (the engine's `XBk` takes `k < L`), and the stuck `c.sdsp` needs a
"write at the row end" certificate arm (`AxCert.Cert` / `EvA` have a read-end arm `cEnd` only).
Neither exists, so `t2Post` cannot be closed here.  This file delivers (a) the `a3` fact at the
row-end BOUNDARY inside the CPS continuation `KSeg` of `wpdAllocpidSeg` (exact, unweakened), and
(b) the closed WPd for the state-independent part `t2PostS` (pid = `p->pid`'s data, `npSrc`,
`FRAG`) with its joint step.  `t2Post`/`t2Joint` of AxSpinT2a are untouched.

## Pins and premises (honesty notes, Q20' Option V)

* The ROW (`allocFull`, AxSpinT2a) fixes A's control flow and addresses on the normal path.
* PINS: all of `AllocPins`, which now also carries every Option V pin the callees take beyond
  T2a's original list (fields ADDED to `AxSpinT2a.AllocPins`, names kept): `poS1` / `hdS1`
  (push_off's / holding's s1 reload on acquire's call = `&pid_lock`, AxSpinAq2's extra pins),
  `aqS1` / `rlS1` (acquire's / release's s1 reload returns its own s1 spill — so `s1 = p` for
  the `p->pid` and `p->state` bases), `rhCpu` (holding's lk->cpu read on release's call = this
  cpu, the VALUE form AxSpinRl4b's `Hvcpu` needs; T2a's `rhArm` is the semantic form), `rhS1`
  (holding's s1 reload on release's call, Rl4b's `Hvs1`).  T2a's `hdArm` is bridged to
  AxSpinAq2's `hres` form by `AxSpinT2a.hresZero` + `mycpuRetHart`.  All pins concern hart `i`'s
  OWN reads (its private reloads, its own cpu fields, its own nextpid read); none constrains
  another hart.  The theorem proves nothing about a graph whose pinned values differ.
* TRANSLATION / TLB (HAD, design §A.5): `AxSpinApA.MapOk` (the page table maps every aligned 4- /
  8-byte word of the data ranges — stack window, cpu fields, `pid_lock`..`lk->cpu`, nextpid,
  `proc[]` — to itself, load / store / AMO), `AxSpinApA.Warm` (warm TLB on `t2Touch`).
* LAYOUT: `AxSpinApA.Lay` = T2LayHyp's per-hart facts + `S % 16 = 0` (allocproc's frame is
  16-aligned; NOT in `T2LayHyp` — the capstone must add it); `L.xlLk`/`L.xlNp`, `priv`, text.
* TEXT: `acquireText`, `mycpuText`, `pushOffText`, `holdingText`, `popOffText`, `releaseText`,
  `allocpidText` (satisfiable, AxSpinTextCerts) and the NEW `AxSpinApA.tailText` (2 halfwords at
  + 0x98 / + 0x9a; satisfiable on the kernel image like `allocpidTextOf`, not certified here).
* Dropped (affine): release's `notheld` deposit, the reload / `RLfact` annotations.
* Ownership is load-bearing for the DATA: the claim (`locked`, `RNp` from `RPid`), the minted
  issued fragment, the nextpid read's source (`npSrc`), the lk->cpu handle, the private slots.

## Deviations from the design

1. The terminal store is `c.sw a5,24(s1)` at + 0x9a (after `c.li a5,1` at + 0x98), as T2a
   found; the run ends after + 0x9a.
2. The `a3` conjunct of the post (above): `wpdAllocpidSeg` is stated in CPS (a3 at the row-end
   boundary); the closed form is over `t2PostS`.
3. No `XxReg ×3` after the critical section: `wpdAllocpidCs` already executes + 0x8c / + 0x90;
   only `jal release` (+ 0x94) remains (inside `segRel`).
4. `FstMPriv` takes the row premise `rowWle row pa n` (a store flow must bound the store's
   width); the family supplies it (`AxSpinApA.wle4`).

**Reused** (by name): `XxReg` (AxSpinE6), `XxStF` (AxSpinAp8), `AxSpinAq2.wpdAcquire`/`KAcq`,
`wpdAllocpidCs`, `wpdRelease` (Rl4b), `fxPrivWrite`/`HGX`/`naWfEmpty` (AxSpinX2/E5),
`allocFull`/`allocItem`/`allocAcquire`/`allocRelease`/`allocBody`/`allocSpinRmw`/`allocCpuVals`/
`allocCpuWin`/`allocRelZ4`/`allocRelWinC`/`allocW8`/`allocNoRmw8`/`allocNoRmwn`/`allocRmw`/
`AxSpinT2a.jalrRets`/`mycpuRetHart`/`hresZero`/`cpuZAddr`/`scanVaNat`/`privIff`/`hartLt`/`symV`
/`fragNe`, `t2TouchText`/`Np`/`Scan`/`Stk` (AxSpinT2a), `AxSpinRl2.lobpAcq`/`lobpCpuSt`/
`lobpCpuLd`, `gwbIdent`/`lblRow`/`lblOfRow` (AxSpinE5), `certAuipc`/`certAddi` (AxSpinE7),
`certJAL` (AxSymCtl2), `atok38/3c/40/94` + `rfFAp38/3c/40/94` (AxSpinAp6), `tokC` (AxSpinAp),
`stepRegs`/`stepRegs0`/`gbCtrl`/`gbPc`/`gbTlb`/`retxRefl`/`AxSpinE8.ldResStBytes8` (AxSpinE8),
`wpdAnnotEntail` (AxSpinH5), `annotAgreeBig` (AxWp), `AxSpinProt7.readbackBig`,
`AxSpinWit.gconstEq`/`shSkip`, `AxSpinRow.lbAdminWdata`, `postLiftingTrue`,
`AxSpinJ2.bigSepLTriple`.

**Lean-only declarations** (new short names grepped absent from the tree): `FstMPriv`, `ap98`,
`ap9a`, `wpdAllocpidSeg`, `wpdAllocpidSegS`; everything else `AxSpinApA.*` (+ 4 local macros).
-/
import Weak.AxSpinT2a
import Weak.AxSpinAq2
import Weak.AxSpinRl4b
import Weak.AxSpinAp6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The private store flow `FstMPriv` (Q-T2-4 / Q18c) -/

section priv
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- THE PRIVATE STORE FLOW of `n` bytes at `pa` (hart `i`'s private bytes, `fxPrivWrite`): the
flow resource `AxSpinAp9.wpdAllocpidCs` takes as `Opid` for the `p->pid` store, and the terminal
`p->state` store's.  Row premise: every row write of hart `i` at base `pa` is at most `n` bytes
wide (`rowWle`). -/
theorem FstMPriv (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (pa : Int) (n : Nat)
    (Hpriv : ∀ j : Nat, j < n → priv L (pa + (j : Int)) i)
    (Hwn : rowWle (AxOpsem.grow (gtAdGd GT) i) pa n) :
    ⊢ @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i
        (fun _ _ => iprop(True)) := by
  unfold FstM
  iintro %GD %ls %k %data %base %n' %Hc #Hg _ %Hgd %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨Hb, -⟩, lb, rl, Hlb, Hid⟩ := Hd
  rw [Hb] at Hid
  have Hisw : gisW (gtAdGd GT).gdG (i, k) = true := by
    unfold gisW
    rw [lblOfRow _ _ _ _ Hlb]
    cases lb <;> simp [aident, aidentWr] at Hid ⊢ <;> rfl
  have Hsg : ∀ a v, gwritesByte (gtAdGd GT).gdG (i, k) a v → priv L a (i, k).1 := by
    intro a v Hw
    obtain ⟨rl', b, m, j, Hid', Hj, rfl⟩ := gwbIdent _ _ _ _ _ (lblOfRow _ _ _ _ Hlb) Hw
    rw [Hid] at Hid'
    simp only [Option.some.injEq, Prod.mk.injEq] at Hid'
    obtain ⟨rfl, rfl, rfl⟩ := Hid'
    have Hm := Hwn k lb rl data.length Hlb Hid
    exact Hpriv j (by omega)
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply (fxPrivWrite L GT nm HL Hcons (i, k) Hisw Hsg)
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(True)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · itrivial

end priv

/-! # 2. The two instructions after release: `c.li a5,1` (+ 0x98), `c.sw a5,24(s1)` (+ 0x9a) -/

/-- `allocproc + 0x98`: `c.li a5,1` (0x4785). -/
def ap98 : instruction := .ITYPE (sign_extend (m := 12) (1#6), zreg, .Regidx 15#5, .ADDI)
/-- `allocproc + 0x9a`: `c.sw a5,24(s1)` (0xcc9c, `p->state = USED`). -/
def ap9a : instruction := .STORE (24#12, .Regidx 15#5, .Regidx 9#5, 4)

/-- The text facts of the two instructions after `jal release` (not in `allocpidText`, whose
copy ends at + 0x94). -/
def AxSpinApA.tailText (σi : ExecSt) (T : PTree) : Prop :=
  textAtS σi T (pca 0x98) (AxSpinE7.hw 0x4785) ∧ textAtS σi T (pca 0x9a) (AxSpinE7.hw 0xcc9c)

/-- (Rocq `tkc`, as AxSpinAp3/Ap5) the four `TokC` conjuncts. -/
local macro "ax_spin_apa_tkc" h:term:max i0:term:max hex:term:max : tactic =>
  `(tactic| (
    show TokC $h _
    unfold TokC
    refine ⟨$i0, ?_, ?_, True.intro, $hex⟩
    · unfold ext_decode_compressed encdec_compressed_backwards
      simp (config := { decide := true }) only [↓reduceIte]
      rff_auto
    · intro s hm
      refine execOfRunRead drefMisa _ s _ true ?_ (by ax_epi_ledger_krfl)
      intro r v hv
      unfold drefMisa at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
      subst hv
      exact hm))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxSpinApA.tkc98 : TokC (AxSpinE7.hw 0x4785) ap98 := by
  ax_spin_apa_tkc (0x4785#16) (.C_LI (1#6, .Regidx 15#5)) (execExecuteCLI _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxSpinApA.tkc9a : TokC (AxSpinE7.hw 0xcc9c) ap9a := by
  ax_spin_apa_tkc (0xcc9c#16) (.C_SW (6#5, .Cregidx 1#3, .Cregidx 7#3)) (fun _ => rfl)

theorem AxSpinApA.atok98 (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (H : AxSpinApA.tailText σi T) : textOkB σi T satp0 (pca 0x98) true ap98 :=
  tokC σi T satp0 _ _ _ H.1 AxSpinApA.tkc98

theorem AxSpinApA.atok9a (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (H : AxSpinApA.tailText σi T) : textOkB σi T satp0 (pca 0x9a) true ap9a :=
  tokC σi T satp0 _ _ _ H.2 AxSpinApA.tkc9a

theorem AxSpinApA.rfFAp98 : rfF (execute ap98) := rfFOfRf0 _ (rf0Addi _ _ _)

/-! # 3. Layout numbers and addresses -/

/-- The layout facts of hart `i`'s run: a hart id, allocproc's frame base `S` inside `stack0`
(16-aligned, room for the 80-byte callee window), the proc slot `p` a `proc[]` entry. -/
structure AxSpinApA.Lay (i : Agent) (S p : Int) : Prop where
  hi : i < NCPU
  sLo : (KernelSyms.«stack0» : Int) + 80 ≤ S
  sHi : S ≤ (KernelSyms.«stack0» : Int) + 0x8000
  sAl : S % 16 = 0
  pSlot : ∃ m : Nat, m < 64 ∧ p = (KernelSyms.«proc» : Int) + 376 * (m : Int)

/-- (Lean-only) the numbers `omega` needs. -/
theorem AxSpinApA.nums {i : Agent} {S p : Int} (H : AxSpinApA.Lay i S p) :
    0x8000a470 ≤ S ∧ S ≤ 0x80012420 ∧ S % 16 = 0 ∧
    0x80012530 ≤ cpuZ i ∧ cpuZ i ≤ 0x80012530 + 896 ∧
    0x80012930 ≤ p ∧ p + 376 ≤ 0x80012930 + 376 * 64 ∧ (p - 0x80012930) % 8 = 0 ∧
    AxSpinT2a.zLk = 0x80012500 ∧ AxSpinT2a.zNp = 0x8000a384 ∧ cpuZ i % 8 = 0 := by
  obtain ⟨-, -, v3, v4, v5, -, -, -⟩ := AxSpinT2a.symV
  obtain ⟨m, hm, hp⟩ := H.pSlot
  have hS1 := H.sLo
  have hS2 := H.sHi
  rw [v5] at hS1 hS2
  rw [v3] at hp
  have hc : cpuZ i = 0x80012530 + 128 * ((cpuOf i).val : Int) := by
    unfold cpuZ; rw [v4]
  have hcv : (cpuOf i).val < 8 := (cpuOf i).isLt
  refine ⟨by omega, by omega, H.sAl, by omega, by omega, by omega, by omega, by omega, rfl, rfl,
    by omega⟩

/-- (Lean-only) a sum of `ofInt`s. -/
theorem AxSpinApA.vaEq (a d e : Int) (c : BitVec 64) (h : c = BitVec.ofInt 64 d)
    (he : a + d = e) : BitVec.ofInt 64 a + c = BitVec.ofInt 64 e := by
  rw [h, ← BitVec.ofInt_add, he]

theorem AxSpinApA.paZOf (a : Int) (h0 : 0 ≤ a) (h1 : a < 2 ^ 64) :
    paZ (BitVec.ofInt 64 a) = a := by
  unfold paZ
  rw [BitVec.toNat_ofInt]
  have : a % (2 ^ 64 : Nat) = a := Int.emod_eq_of_lt h0 (by simpa using h1)
  rw [this]
  exact Int.toNat_of_nonneg h0

theorem AxSpinApA.toNatOf (a : Int) (h0 : 0 ≤ a) (h1 : a < 2 ^ 64) :
    ((BitVec.ofInt 64 a).toNat : Int) = a := AxSpinApA.paZOf a h0 h1

theorem AxSpinApA.spoOf (a : Int) : spo (BitVec.ofInt 64 a) = BitVec.ofInt 64 (a - 32) :=
  AxSpinApA.vaEq a (-32) _ _ (by decide) (by omega)

theorem AxSpinApA.sp1OfOf (a : Int) :
    AxSpinE8.sp1Of (BitVec.ofInt 64 a) = BitVec.ofInt 64 (a - 16) :=
  AxSpinApA.vaEq a (-16) _ _ (by decide) (by omega)

theorem AxSpinApA.imm24Of : sign_extend (m := 64) AxSpinPO3.imm24 = BitVec.ofInt 64 24 := by
  decide
theorem AxSpinApA.imm16Of : sign_extend (m := 64) AxSpinPO3.imm16 = BitVec.ofInt 64 16 := by
  decide
theorem AxSpinApA.imm8Of : sign_extend (m := 64) AxSpinPO3.imm8 = BitVec.ofInt 64 8 := by
  decide
theorem AxSpinApA.himm24Of : sign_extend (m := 64) AxSpinHd8.imm24 = BitVec.ofInt 64 24 := by
  decide
theorem AxSpinApA.himm16Of : sign_extend (m := 64) AxSpinHd8.imm16 = BitVec.ofInt 64 16 := by
  decide
theorem AxSpinApA.himm8Of : sign_extend (m := 64) AxSpinHd8.imm8 = BitVec.ofInt 64 8 := by
  decide
theorem AxSpinApA.immRaOf : sign_extend (m := 64) AxSpinE8.immRa = BitVec.ofInt 64 8 := by
  decide
theorem AxSpinApA.immS0Of : sign_extend (m := 64) AxSpinE8.immS0 = BitVec.ofInt 64 0 := by
  decide
theorem AxSpinApA.i120Of : sign_extend (m := 64) i120 = BitVec.ofInt 64 120 := by decide
theorem AxSpinApA.i124Of : sign_extend (m := 64) i124 = BitVec.ofInt 64 124 := by decide
theorem AxSpinApA.i16Of : sign_extend (m := 64) (16#12) = BitVec.ofInt 64 16 := by decide
theorem AxSpinApA.i0Of : sign_extend (m := 64) (0#12) = BitVec.ofInt 64 0 := by decide
theorem AxSpinApA.i48Of : sign_extend (m := 64) (48#12) = BitVec.ofInt 64 48 := by decide
theorem AxSpinApA.i24Of : sign_extend (m := 64) (24#12) = BitVec.ofInt 64 24 := by decide

/-- `&pid_lock` as the `ofInt` the slot lemmas use. -/
theorem AxSpinApA.lkOf : BitVec.ofNat 64 KernelSyms.«pid_lock» = BitVec.ofInt 64 AxSpinT2a.zLk := by
  decide

/-- `a0` after allocproc + 0x38 / + 0x3c: `&pid_lock`. -/
theorem AxSpinApA.a0Entry :
    pca 0x38 + auipcOff 17#20 + sign_extend (m := 64) 0x956#12 =
      BitVec.ofNat 64 KernelSyms.«pid_lock» := by decide

/-- `&cpus[cpuOf i]` as an `ofInt`. -/
theorem AxSpinApA.cpuOfInt (i : Agent) : cpuAddr (cpuOf i) = BitVec.ofInt 64 (cpuZ i) := by
  have h := AxSpinT2a.cpuZAddr i
  apply BitVec.eq_of_toNat_eq
  have h0 : 0 ≤ cpuZ i := by rw [← h]; omega
  have h1 : cpuZ i < 2 ^ 64 := by rw [← h]; have := (cpuAddr (cpuOf i)).isLt; omega
  have := AxSpinApA.toNatOf (cpuZ i) h0 h1
  omega

/-- `mycpu()`'s result at `tp = hartId (cpuOf i)`. -/
theorem AxSpinApA.myOf (i : Agent) :
    AxSpinE8.mycpuRet (hartId (cpuOf i)) = BitVec.ofInt 64 (cpuZ i) := by
  rw [AxSpinT2a.mycpuRetHart, AxSpinApA.cpuOfInt]

/-! # 4. The writes of the row family, by position -/

/-- (Lean-only) the (base, width) of a segment item that writes. -/
def AxSpinApA.xWm : Rxitem → Option (Int × Nat)
  | .it (.RS pa n) => some (pa, n)
  | .RSc pa n _ => some (pa, n)
  | .RM _ _ pa n => some (pa, n)
  | _ => none

theorem AxSpinApA.xWmOf (x : Rxitem) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    xshape x lb → aidentWr (aident lb) = some (rl, b, m) → AxSpinApA.xWm x = some (b, m) := by
  intro Hs Hw
  cases x with
  | it it =>
    cases it with
    | RF n' => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hw; cases Hw
    | RP pb n' => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RL pb n' => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RS pb n' =>
      obtain ⟨vw, cls, rfl, Hl⟩ := Hs
      simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
      obtain ⟨_, rfl, rfl⟩ := Hw
      rw [Hl]
      rfl
  | RB pr pw sr sw => rw [Hs] at Hw; cases Hw
  | RSc pb n' cls =>
    obtain ⟨vw, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, rfl, rfl⟩ := Hw
    rw [Hl]
    rfl
  | RM aq rl' pb n' =>
    rw [Hs] at Hw
    simp only [aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, rfl, rfl⟩ := Hw
    rfl

theorem AxSpinApA.appCase {α : Type} {l1 l2 : List α} {k : Nat} {x : α}
    (h : (l1 ++ l2)[k]? = some x) :
    (k < l1.length ∧ l1[k]? = some x) ∨ (l1.length ≤ k ∧ l2[k - l1.length]? = some x) := by
  by_cases hk : k < l1.length
  · rw [List.getElem?_append_left hk] at h
    exact .inl ⟨hk, h⟩
  · rw [List.getElem?_append_right (by omega)] at h
    exact .inr ⟨by omega, h⟩

/-- (Lean-only) an item of a mapped `Ritem` list that writes is one of its `RS` items. -/
theorem AxSpinApA.mapW {l : List Ritem} {k : Nat} {x : Rxitem} {b : Int} {m : Nat}
    (h : (l.map Rxitem.it)[k]? = some x) (hw : AxSpinApA.xWm x = some (b, m)) :
    Ritem.RS b m ∈ l := by
  rw [List.getElem?_map] at h
  obtain ⟨it, Hit, rfl⟩ := Option.map_eq_some_iff.1 h
  have Hm := List.mem_of_getElem? Hit
  cases it with
  | RS pa n =>
    simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact Hm
  | _ => simp [AxSpinApA.xWm] at hw

theorem AxSpinApA.itRS {it : Ritem} {b : Int} {m : Nat}
    (h : AxSpinApA.xWm (.it it) = some (b, m)) : it = .RS b m := by
  cases it with
  | RS pa n =>
    simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | _ => simp [AxSpinApA.xWm] at h

theorem AxSpinApA.aqTailW {pmra pms0 pcl pra ps0 ps1 b : Int} {j m : Nat}
    (h : (aqTail pmra pms0 pcl pra ps0 ps1)[j]? = some (Ritem.RS b m)) :
    (j = 4 ∧ b = pcl ∧ m = 8) ∨ ((b = pmra ∨ b = pms0) ∧ m = 8) := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [aqTail, mycSh] at h <;> omega

theorem AxSpinApA.bodyW {pnp ppid b : Int} {j m : Nat}
    (h : (apBodySh pnp ppid)[j]? = some (Ritem.RS b m)) :
    (j = 65 ∧ b = pnp ∧ m = 4) ∨ (j = 66 ∧ b = ppid ∧ m = 4) := by
  unfold apBodySh at h
  cases j with
  | zero => simp at h
  | succ j =>
    rw [List.getElem?_cons_succ] at h
    rcases AxSpinApA.appCase h with ⟨h6, H6⟩ | ⟨h6, H6⟩
    · rw [List.getElem?_map] at H6
      obtain ⟨jj, -, H⟩ := Option.map_eq_some_iff.1 H6
      cases H
    · rw [List.length_map, List.length_range] at h6 H6
      rcases (show j - 64 = 0 ∨ j - 64 = 1 by
        have := (List.getElem?_eq_some_iff.1 H6).1; simp at this; omega) with hj | hj <;>
        rw [hj] at H6 <;> simp at H6 <;> omega

theorem AxSpinApA.get3 {α : Type} {a b c x : α} {j : Nat} (h : [a, b, c][j]? = some x) :
    (j = 0 ∧ x = a) ∨ (j = 1 ∧ x = b) ∨ (j = 2 ∧ x = c) := by
  rcases j with _ | _ | _ | j <;> simp at h
  · exact .inl ⟨rfl, h.symm⟩
  · exact .inr (.inl ⟨rfl, h.symm⟩)
  · exact .inr (.inr ⟨rfl, h.symm⟩)

/-- THE WRITES OF THE ROW FAMILY: every write of a row in `allocFull` is a stack-window spill
(8 bytes), a cpu-field store (4), the lock word (the spins and the releasing store), `lk->cpu`
(acquire's / release's store), the nextpid store, or one of `p`'s two fields. -/
def AxSpinApA.WrAt (q : T2Prm) (i : Agent) (S p : Int) (k : Nat) (b : Int) (m : Nat) : Prop :=
  (m = 8 ∧ S - 80 ≤ b ∧ b + 8 ≤ S) ∨
  (m = 4 ∧ (b = cpuZ i + 120 ∨ b = cpuZ i + 124)) ∨
  (m = 4 ∧ b = AxSpinT2a.zLk ∧ ((t2KSp q ≤ k ∧ k ≤ t2KA q) ∨ k = relKw (t2KRl q))) ∨
  (m = 8 ∧ b = AxSpinT2a.zLk + 16 ∧ (k = t2KMy q + 4 ∨ k = relKc (t2KRl q))) ∨
  (m = 4 ∧ b = AxSpinT2a.zNp ∧ k = t2KBd q + 65) ∨
  (m = 4 ∧ (b = p + 48 ∨ b = p + 24))

section wr
variable {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}

theorem AxSpinApA.segWr (HF : allocFull row q i S p) (k : Nat) (lb : Lbl) (rl : Bool) (b : Int)
    (m : Nat) :
    row[k]? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    AxSpinApA.WrAt q i S p k b m := by
  intro Hk Hw
  obtain ⟨x, Hx, Hs⟩ := allocItem HF k lb Hk
  have Hxw := AxSpinApA.xWmOf x lb rl b m Hs Hw
  unfold AxSpinApA.WrAt
  unfold allocSeg at Hx
  rcases AxSpinApA.appCase Hx with ⟨h0, H⟩ | ⟨h0, H⟩
  · -- acquire's spills
    have := AxSpinApA.mapW H Hxw
    refine Or.inl ?_
    clear Hx H Hk Hs Hxw HF
    simp only [aqHead, List.mem_cons, List.not_mem_nil, or_false, Ritem.RS.injEq] at this
    omega
  rw [List.length_map, AxSpinT2a.aqHeadLen] at h0 H
  rcases AxSpinApA.appCase H with ⟨h1, H⟩ | ⟨h1, H⟩
  · -- push_off
    have := AxSpinApA.mapW H Hxw
    have hs : (m = 8 ∧ S - 80 ≤ b ∧ b + 8 ≤ S) ∨
        (m = 4 ∧ (b = cpuZ i + 120 ∨ b = cpuZ i + 124)) := by
      clear Hx H Hk Hs Hxw h0 h1 HF
      cases hb : q.b <;>
        simp only [hb, poSh, poHead, poInt, poTail, mycSh, ↓reduceIte, Bool.false_eq_true,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          reduceCtorEq, Ritem.RS.injEq, false_or] at this <;>
        omega
    rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  rw [List.length_map, AxSpinT2a.poShLen] at h1 H
  rcases AxSpinApA.appCase H with ⟨h2, H⟩ | ⟨h2, H⟩
  · -- holding
    have := AxSpinApA.mapW H Hxw
    refine Or.inl ?_
    clear Hx H Hk Hs Hxw h0 h1 h2 HF
    cases hb : q.hb <;>
      simp only [hb, holdShB, mycSh, ↓reduceIte, Bool.false_eq_true,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, Ritem.RS.injEq, false_or] at this <;>
      omega
  rw [List.length_map, holdShBLen] at h2 H
  rcases AxSpinApA.appCase H with ⟨h3, H⟩ | ⟨h3, H⟩
  · -- the spins
    rw [List.length_replicate] at h3
    rw [List.getElem?_replicate, if_pos h3] at H
    cases H
    simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq] at Hxw
    obtain ⟨rfl, rfl⟩ := Hxw
    have e1 : t2KSp q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb := by
      simp only [t2KSp, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;> simp
    have e2 : t2KA q = t2KSp q + q.n := rfl
    refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inl ⟨?_, ?_⟩⟩))
    · rw [e1]; omega
    · rw [e2, e1]; omega
  rw [List.length_replicate] at h3 H
  rcases AxSpinApA.appCase H with ⟨h4, H⟩ | ⟨h4, H⟩
  · -- acquire's tail
    rw [List.length_map, aqTailLen] at h4
    rw [List.getElem?_map] at H
    obtain ⟨it, Hit, rfl⟩ := Option.map_eq_some_iff.1 H
    rw [AxSpinApA.itRS Hxw] at Hit
    have hk : t2KMy q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb + (q.n + 1) := by
      simp only [t2KMy, aqKm, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;> simp <;> omega
    rcases AxSpinApA.aqTailW Hit with ⟨hj, rfl, rfl⟩ | ⟨hb, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inl (by omega)⟩)))
    · exact Or.inl ⟨rfl, by omega, by omega⟩
  rw [List.length_map, aqTailLen] at h4 H
  rcases AxSpinApA.appCase H with ⟨h5, H⟩ | ⟨h5, H⟩
  · -- the critical-section body
    rw [List.length_map, AxSpinAp7.apBodyShLen] at h5
    rw [List.getElem?_map] at H
    obtain ⟨it, Hit, rfl⟩ := Option.map_eq_some_iff.1 H
    rw [AxSpinApA.itRS Hxw] at Hit
    have hk : t2KBd q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb + (q.n + 1) + 8 := by
      simp only [t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;> simp <;>
        omega
    rcases AxSpinApA.bodyW Hit with ⟨hj, rfl, rfl⟩ | ⟨hj, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, .inl rfl⟩))))
  rw [List.length_map, AxSpinAp7.apBodyShLen] at h5 H
  have hkr : t2KRl q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb + (q.n + 1) + 8 + 67 := by
    simp only [t2KRl, t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;>
      simp <;> omega
  rcases AxSpinApA.appCase H with ⟨h6, H⟩ | ⟨h6, H⟩
  · -- release
    unfold relSh at H
    rcases AxSpinApA.appCase H with ⟨h7, H⟩ | ⟨h7, H⟩
    · have := AxSpinApA.mapW H Hxw
      refine Or.inl ?_
      clear Hx H Hk Hs Hxw HF
      simp only [relHead, List.mem_cons, List.not_mem_nil, or_false, Ritem.RS.injEq] at this
      omega
    rw [List.length_map] at h7 H
    rcases AxSpinApA.appCase H with ⟨h8, H⟩ | ⟨h8, H⟩
    · have := AxSpinApA.mapW H Hxw
      refine Or.inl ?_
      clear Hx H Hk Hs Hxw HF
      simp only [holdShB, mycSh, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, Ritem.RS.injEq, false_or] at this
      omega
    rw [List.length_map, holdShBLen] at h8 H
    rcases AxSpinApA.appCase H with ⟨h9, H⟩ | ⟨h9, H⟩
    · have hl : (relHead (S - 8) (S - 16) (S - 24)).length = 3 := rfl
      have hh : holdLen true = 12 := rfl
      rcases AxSpinApA.get3 H with ⟨hj, rfl⟩ | ⟨hj, rfl⟩ | ⟨hj, rfl⟩ <;>
        simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at Hxw
      · obtain ⟨rfl, rfl⟩ := Hxw
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inr (by simp only [relKc]; omega)⟩)))
      · obtain ⟨rfl, rfl⟩ := Hxw
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inr (by simp only [relKw]; omega)⟩))
    rcases AxSpinApA.appCase H with ⟨h10, H⟩ | ⟨h10, H⟩
    · have := AxSpinApA.mapW H Hxw
      have hs : (m = 8 ∧ S - 80 ≤ b ∧ b + 8 ≤ S) ∨
          (m = 4 ∧ (b = cpuZ i + 120 ∨ b = cpuZ i + 124)) := by
        clear Hx H Hk Hs Hxw HF
        cases hc : q.c <;>
          simp only [hc, ppSh, ppHead, ppMid, ppTail, mycSh, ↓reduceIte, Bool.false_eq_true,
            List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            reduceCtorEq, Ritem.RS.injEq, false_or] at this <;>
          omega
      rcases hs with hs | hs
      · exact Or.inl hs
      · exact Or.inr (Or.inl hs)
    · have := AxSpinApA.mapW H Hxw
      simp [relTail] at this
  · -- the terminal store
    have Hlt : k < t2Len q := by
      rw [← HF.2.1]; exact (List.getElem?_eq_some_iff.1 Hk).1
    rw [relShLen] at h6 H
    have hTl : t2Len q = t2KRl q + relLen q.c + 1 := by rw [t2Len, AxSpinT2a.kTEq]
    rw [show k - 3 - (17 + (if q.b then 5 else 0)) - holdLen q.hb - (q.n + 1) - 8 - 67 -
      relLen q.c = 0 by omega] at H
    simp only [List.getElem?_cons_zero, Option.some.injEq] at H
    subst H
    simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq] at Hxw
    obtain ⟨rfl, rfl⟩ := Hxw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, .inr rfl⟩))))

end wr

/-! # 5. Consequences: the windows, widths and the layout gaps the callees ask for -/

/-- (Lean-only) a byte written by a row event is inside the event's (base, width). -/
theorem AxSpinApA.gwbRow (GD : Gdexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG e a v → ∃ lb rl b m t, (AxOpsem.grow GD e.1)[e.2]? = some lb ∧
      aidentWr (aident lb) = some (rl, b, m) ∧ t < m ∧ a = b + (t : Int) := by
  intro Hw
  obtain ⟨l, -, -, -, Hl, -⟩ := id Hw
  obtain ⟨rl, b, m, t, Hid, Ht, Ha⟩ := gwbIdent _ _ _ _ _ Hl Hw
  exact ⟨l, rl, b, m, t, lblRow GD e.1 e.2 l Hl, Hid, Ht, Ha⟩

section win
variable {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
variable (HF : allocFull row q i S p) (Hlay : AxSpinApA.Lay i S p)
include HF Hlay

/-- (Lean-only) the position facts `omega` needs. -/
theorem AxSpinApA.posFacts :
    t2KSp q ≤ t2KA q ∧ t2KA q + 1 = t2KMy q ∧ t2KBd q = t2KMy q + 8 ∧
    t2KRl q = t2KBd q + 67 ∧ t2KRh q = t2KRl q + 3 ∧ relKc (t2KRl q) = t2KRl q + 15 ∧
    relKw (t2KRl q) = t2KRl q + 17 := by
  refine ⟨Nat.le_add_right _ _, AxSpinT2a.kAEq q, rfl, rfl, rfl, rfl, rfl⟩

/-- Ap9's `Hone`: the only row write at base `nextpid` is the body's store. -/
theorem AxSpinApA.npOnly (k' : Nat) (lb : Lbl) (rl : Bool) (m : Nat) :
    row[k']? = some lb → aidentWr (aident lb) = some (rl, AxSpinT2a.zNp, m) →
    k' = t2KBd q + 65 := by
  intro Hk Hw
  have N := AxSpinApA.nums Hlay
  rcases AxSpinApA.segWr HF k' lb rl _ m Hk Hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
    ⟨-, -, h⟩ | ⟨-, h⟩
  all_goals first | exact h | omega

/-- No row write before the body touches nextpid's bytes. -/
theorem AxSpinApA.npBefore (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    k' < t2KBd q → row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    dj b m AxSpinT2a.zNp 4 := by
  intro hk Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApA.posFacts HF Hlay
  unfold dj
  rcases AxSpinApA.segWr HF k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

/-- No row write strictly between the claim and release's holding touches the lock byte. -/
theorem AxSpinApA.lkBetween (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    t2KA q < k' → k' < t2KRh q → row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    dj b m AxSpinT2a.zLk 1 := by
  intro hk1 hk2 Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApA.posFacts HF Hlay
  unfold dj
  rcases AxSpinApA.segWr HF k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

/-- No row write strictly between acquire's lk->cpu store and release's lk->cpu read touches
`lk->cpu`. -/
theorem AxSpinApA.clbBetween (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    t2KMy q + 4 < k' → k' < t2KRh q + 4 → row[k']? = some lb →
    aidentWr (aident lb) = some (rl, b, m) → dj b m (AxSpinT2a.zLk + 16) 8 := by
  intro hk1 hk2 Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApA.posFacts HF Hlay
  unfold dj
  rcases AxSpinApA.segWr HF k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

/-- The 4-byte private fields are written 4 bytes at a time. -/
theorem AxSpinApA.wle4 (b : Int)
    (hb : b = cpuZ i + 120 ∨ b = cpuZ i + 124 ∨ b = p + 48 ∨ b = p + 24) : rowWle row b 4 := by
  intro k' lb rl m Hk Hw
  have N := AxSpinApA.nums Hlay
  rcases AxSpinApA.segWr HF k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

/-- hart `i`'s private ranges miss the lock word's base (AxSpinT2a's `Hpz`). -/
theorem AxSpinApA.privNe : ∀ a, AxSpinT2a.privZ S p i a → a ≠ AxSpinT2a.zLk := by
  intro a ha
  have N := AxSpinApA.nums Hlay
  unfold AxSpinT2a.privZ at ha
  omega

end win

/-! # 6. The hypothesis bundle and the premise bundles of the callees -/

/-- The DATA ranges hart `i`'s segment touches (stack window, its cpu fields, `pid_lock` and
`lk->cpu`, nextpid, the whole `proc[]` array: `p`'s fields and the scan). -/
def AxSpinApA.Rng (i : Agent) (S p a : Int) (w : Nat) : Prop :=
  (S - 80 ≤ a ∧ a + w ≤ S) ∨ (cpuZ i + 120 ≤ a ∧ a + w ≤ cpuZ i + 128) ∨
  (AxSpinT2a.zLk ≤ a ∧ a + w ≤ AxSpinT2a.zLk + 24) ∨
  (AxSpinT2a.zNp ≤ a ∧ a + w ≤ AxSpinT2a.zNp + 4) ∨
  ((KernelSyms.«proc» : Int) ≤ a ∧ a + w ≤ (KernelSyms.«proc» : Int) + 376 * 64)

/-- THE TRANSLATION PREMISE (HAD, design §A.5): the page table maps every aligned 4- / 8-byte
word of the data ranges to itself, readable, writable and AMO-able (the kernel direct map,
VA = PA). -/
def AxSpinApA.MapOk (σi : ExecSt) (T : PTree) (i : Agent) (S p : Int) : Prop :=
  ∀ (acc : MemoryAccessType mem_payload) (a : Int) (w : Nat),
    (acc = .Load .Data ∨ acc = .Store .Data ∨ acc = accAmo true) → (w = 4 ∨ w = 8) →
    a % (w : Int) = 0 → AxSpinApA.Rng i S p a w →
    dataAtS σi T acc (BitVec.ofInt 64 a) w (BitVec.ofInt 64 a)

/-- WARM TLB on every page the segment touches. -/
def AxSpinApA.Warm (rs : RegFile) (i : Agent) (S p : Int) : Prop :=
  ∀ va, t2Touch i S p va → hitW rs va

theorem AxSpinApA.warmTlb (rs rs' : RegFile) (i : Agent) (S p : Int) :
    rs' .tlb = rs .tlb → AxSpinApA.Warm rs i S p → AxSpinApA.Warm rs' i S p :=
  fun Ht H va hv => hitWAgree rs rs' va Ht (H va hv)

/-- THE HYPOTHESES of the segment WPd (one hart `i`, control parameters `q`, frame `S`, slot
`p`): the row family, the pins, the layout, the translation, the text. -/
structure AxSpinApA.Hyp (L : Xlay) (GT : GdexecT) (σi : ExecSt) (T : PTree) (i : Agent)
    (q : T2Prm) (S p : Int) : Prop where
  full : allocFull (AxOpsem.grow (gtAdGd GT) i) q i S p
  pins : AllocPins (gtAdGd GT) i q
  lay : AxSpinApA.Lay i S p
  hLk : L.xlLk = AxSpinT2a.zLk
  hNp : L.xlNp = AxSpinT2a.zNp
  hpriv : ∀ a, AxSpinT2a.privZ S p i a → priv L a i
  ntx : ∀ a, ¬ AxSpinT2a.textZ a → ¬ L.xlText a
  map : AxSpinApA.MapOk σi T i S p
  txa : acquireText σi T
  txm : mycpuText σi T
  txp : pushOffText σi T
  txh : holdingText σi T
  txq : popOffText σi T
  txr : releaseText σi T
  txc : allocpidText σi T
  txt : AxSpinApA.tailText σi T
  fix : textFixed (gtAdGd GT) i (imgS σi)

section bundles
variable {L : Xlay} {GT : GdexecT} {σi : ExecSt} {T : PTree} {i : Agent} {q : T2Prm} {S p : Int}
variable (H : AxSpinApA.Hyp L GT σi T i q S p)
include H

theorem AxSpinApA.ntxOf (a : Int) (h : 0x80007000 ≤ a) : ¬ L.xlText a := by
  refine H.ntx a ?_
  unfold AxSpinT2a.textZ
  obtain ⟨-, -, -, -, -, -, v7, v8⟩ := AxSpinT2a.symV
  rw [v8]
  omega

theorem AxSpinApA.dat (acc : MemoryAccessType mem_payload)
    (hacc : acc = .Load .Data ∨ acc = .Store .Data ∨ acc = accAmo true) (a : Int) (w : Nat)
    (hw : w = 4 ∨ w = 8) (hal : a % (w : Int) = 0) (hr : AxSpinApA.Rng i S p a w) :
    dataAtS σi T acc (BitVec.ofInt 64 a) w (BitVec.ofInt 64 a) :=
  H.map acc a w hacc hw hal hr

theorem AxSpinApA.hitStk (rs : RegFile) (hw : AxSpinApA.Warm rs i S p) (a : Int)
    (h1 : S - 80 ≤ a) (h2 : a < S) : hitW rs (BitVec.ofInt 64 a) := by
  have N := AxSpinApA.nums H.lay
  refine hw _ (t2TouchStk i S p _ ?_ ?_) <;> rw [AxSpinApA.toNatOf a (by omega) (by omega)] <;>
    omega

theorem AxSpinApA.slot (rs : RegFile) (hw : AxSpinApA.Warm rs i S p) (d : Int) (h1 : 8 ≤ d)
    (h2 : d ≤ 80) (h3 : d % 8 = 0) :
    AxSpinPO1.slot8 σi T L i rs (BitVec.ofInt 64 (S - d)) (BitVec.ofInt 64 (S - d)) := by
  have N := AxSpinApA.nums H.lay
  have hz := AxSpinApA.paZOf (S - d) (by omega) (by omega)
  refine ⟨AxSpinApA.dat H _ (.inr (.inl rfl)) _ 8 (.inr rfl) (by omega) (.inl ⟨by omega, by omega⟩),
    AxSpinApA.dat H _ (.inl rfl) _ 8 (.inr rfl) (by omega) (.inl ⟨by omega, by omega⟩),
    AxSpinApA.hitStk H rs hw _ (by omega) (by omega), ?_, ?_⟩
  · intro j hj
    rw [hz]
    exact H.hpriv _ (.inl ⟨by omega, by omega⟩)
  · rw [hz]
    exact AxSpinApA.ntxOf H _ (by omega)

theorem AxSpinApA.fld (rs : RegFile) (hw : AxSpinApA.Warm rs i S p) (c : Int)
    (hc : c = 120 ∨ c = 124) :
    fld4 σi T L i rs (BitVec.ofInt 64 (cpuZ i + c)) (BitVec.ofInt 64 (cpuZ i + c)) := by
  have N := AxSpinApA.nums H.lay
  have hz := AxSpinApA.paZOf (cpuZ i + c) (by omega) (by omega)
  refine ⟨AxSpinApA.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega)
      (.inr (.inl ⟨by omega, by omega⟩)),
    AxSpinApA.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega) (.inr (.inl ⟨by omega, by omega⟩)),
    hw _ ?_, ?_, ?_⟩
  · refine .inr (.inr (.inr (.inl ?_)))
    rw [AxSpinApA.toNatOf _ (by omega) (by omega)]
    omega
  · intro j hj
    rw [hz]
    exact H.hpriv _ (.inr (.inr (.inr ⟨by omega, by omega⟩)))
  · rw [hz]
    exact AxSpinApA.ntxOf H _ (by omega)

end bundles

/-! ## The slot addresses the callees compute -/

section addrs
variable (S : Int)

/-- (Lean-only) `spo` / `sp1Of` arithmetic, `simp`-normal. -/
local macro "ax_spin_apa_va" : tactic =>
  `(tactic| (simp only [AxSpinApA.spoOf, AxSpinApA.sp1OfOf, AxSpinApA.imm24Of,
               AxSpinApA.imm16Of, AxSpinApA.imm8Of, AxSpinApA.himm24Of, AxSpinApA.himm16Of,
               AxSpinApA.himm8Of, AxSpinApA.immRaOf, AxSpinApA.immS0Of, ← BitVec.ofInt_add]
             congr 1
             omega))

theorem AxSpinApA.aA24 : spo (BitVec.ofInt 64 S) + sign_extend (m := 64) AxSpinPO3.imm24 =
    BitVec.ofInt 64 (S - 8) := by ax_spin_apa_va
theorem AxSpinApA.aA16 : spo (BitVec.ofInt 64 S) + sign_extend (m := 64) AxSpinPO3.imm16 =
    BitVec.ofInt 64 (S - 16) := by ax_spin_apa_va
theorem AxSpinApA.aA8 : spo (BitVec.ofInt 64 S) + sign_extend (m := 64) AxSpinPO3.imm8 =
    BitVec.ofInt 64 (S - 24) := by ax_spin_apa_va
theorem AxSpinApA.aQ24 : spo (spo (BitVec.ofInt 64 S)) + sign_extend (m := 64) AxSpinPO3.imm24 =
    BitVec.ofInt 64 (S - 40) := by ax_spin_apa_va
theorem AxSpinApA.aQ16 : spo (spo (BitVec.ofInt 64 S)) + sign_extend (m := 64) AxSpinPO3.imm16 =
    BitVec.ofInt 64 (S - 48) := by ax_spin_apa_va
theorem AxSpinApA.aQ8 : spo (spo (BitVec.ofInt 64 S)) + sign_extend (m := 64) AxSpinPO3.imm8 =
    BitVec.ofInt 64 (S - 56) := by ax_spin_apa_va
theorem AxSpinApA.aH24 : spo (spo (BitVec.ofInt 64 S)) + sign_extend (m := 64) AxSpinHd8.imm24 =
    BitVec.ofInt 64 (S - 40) := by ax_spin_apa_va
theorem AxSpinApA.aH16 : spo (spo (BitVec.ofInt 64 S)) + sign_extend (m := 64) AxSpinHd8.imm16 =
    BitVec.ofInt 64 (S - 48) := by ax_spin_apa_va
theorem AxSpinApA.aH8 : spo (spo (BitVec.ofInt 64 S)) + sign_extend (m := 64) AxSpinHd8.imm8 =
    BitVec.ofInt 64 (S - 56) := by ax_spin_apa_va
theorem AxSpinApA.aQm8 : AxSpinE8.sp1Of (spo (spo (BitVec.ofInt 64 S))) +
    sign_extend (m := 64) AxSpinE8.immRa = BitVec.ofInt 64 (S - 72) := by ax_spin_apa_va
theorem AxSpinApA.aQm0 : AxSpinE8.sp1Of (spo (spo (BitVec.ofInt 64 S))) +
    sign_extend (m := 64) AxSpinE8.immS0 = BitVec.ofInt 64 (S - 80) := by ax_spin_apa_va
theorem AxSpinApA.aM8 : AxSpinE8.sp1Of (spo (BitVec.ofInt 64 S)) +
    sign_extend (m := 64) AxSpinE8.immRa = BitVec.ofInt 64 (S - 40) := by ax_spin_apa_va
theorem AxSpinApA.aM0 : AxSpinE8.sp1Of (spo (BitVec.ofInt 64 S)) +
    sign_extend (m := 64) AxSpinE8.immS0 = BitVec.ofInt 64 (S - 48) := by ax_spin_apa_va
theorem AxSpinApA.aMm8 : AxSpinE8.sp1Of (AxSpinE8.sp1Of (spo (BitVec.ofInt 64 S))) +
    sign_extend (m := 64) AxSpinE8.immRa = BitVec.ofInt 64 (S - 56) := by ax_spin_apa_va
theorem AxSpinApA.aMm0 : AxSpinE8.sp1Of (AxSpinE8.sp1Of (spo (BitVec.ofInt 64 S))) +
    sign_extend (m := 64) AxSpinE8.immS0 = BitVec.ofInt 64 (S - 64) := by ax_spin_apa_va

end addrs

/-- (Lean-only) `alldj` from pairwise disjointness. -/
theorem AxSpinApA.alldjOf (l : List (Int × Nat))
    (H : l.Pairwise (fun x y => dj x.1 x.2 y.1 y.2)) : alldj l := by
  intro j1 j2 x y h1 h2 hne
  obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hj2, rfl⟩ := List.getElem?_eq_some_iff.1 h2
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact List.pairwise_iff_getElem.1 H j1 j2 hj1 hj2 h
  · exact djSym _ _ _ _ (List.pairwise_iff_getElem.1 H j2 j1 hj2 hj1 h)

/-- (Lean-only) `slotsDisj` from pairwise disjointness. -/
theorem AxSpinApA.slotsDisjOf (l : List Int) (H : l.Pairwise disj8) : slotsDisj l := by
  intro j1 j2 a b hne h1 h2
  obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hj2, rfl⟩ := List.getElem?_eq_some_iff.1 h2
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact List.pairwise_iff_getElem.1 H j1 j2 hj1 hj2 h
  · have := List.pairwise_iff_getElem.1 H j2 j1 hj2 hj1 h
    unfold disj8 at this ⊢
    omega

/-! # 7. The pieces of the segment -/

theorem AxSpinApA.lk0 :
    BitVec.ofNat 64 KernelSyms.«pid_lock» + sign_extend (m := 64) (0#12) =
      BitVec.ofInt 64 AxSpinT2a.zLk := by decide
theorem AxSpinApA.lk16 :
    BitVec.ofNat 64 KernelSyms.«pid_lock» + sign_extend (m := 64) (16#12) =
      BitVec.ofInt 64 (AxSpinT2a.zLk + 16) := by decide

theorem AxSpinApA.hitTxt {i : Agent} {S p : Int} (rs : RegFile) (hw : AxSpinApA.Warm rs i S p)
    (va : BitVec 64) (h1 : 0x80000000 ≤ va.toNat) (h2 : va.toNat < 0x80002000) : hitW rs va :=
  hw va (t2TouchText i S p va h1 h2)

theorem AxSpinApA.hitLk {i : Agent} {S p : Int} (rs : RegFile) (hw : AxSpinApA.Warm rs i S p)
    (c : Int) (h1 : 0 ≤ c) (h2 : c < 24) : hitW rs (BitVec.ofInt 64 (AxSpinT2a.zLk + c)) := by
  refine hw _ (.inr (.inr (.inl ?_)))
  have hz : AxSpinT2a.zLk = 0x80012500 := rfl
  rw [AxSpinApA.toNatOf _ (by omega) (by omega)]
  omega

/-- (Lean-only) `P ⊢ P ∗ True`. -/
theorem AxSpinApA.sepTrue {GF : BundledGFunctors} (P : IProp GF) : P ⊢ iprop(P ∗ True) := by
  iintro HP
  isplitl [HP]
  · iexact HP
  · itrivial

theorem AxSpinApA.npOf : vaNp = BitVec.ofInt 64 AxSpinT2a.zNp := by decide

theorem AxSpinApA.scanOf (j : Nat) (hj : j < 64) :
    AxSpinAp9.scanVa j = BitVec.ofInt 64 (AxSpinAp7.scanAddr j) := by
  apply BitVec.eq_of_toNat_eq
  have h := AxSpinT2a.scanVaNat j hj
  have hp : (KernelSyms.«proc» : Int) = 0x80012930 := rfl
  have hsa : AxSpinAp7.scanAddr j = 0x80012930 + 376 * (j : Int) + 48 := by
    unfold AxSpinAp7.scanAddr; rw [hp]
  have h2 := AxSpinApA.toNatOf (AxSpinAp7.scanAddr j) (by omega) (by omega)
  omega


/-- (Lean-only) a row write is a memory event. -/
theorem AxSpinApA.wrMem (lb : Lbl) (x : Bool × Int × Nat) :
    aidentWr (aident lb) = some x → lbIsMem lb = true := by
  cases lb <;> simp [aident, aidentWr, lbIsMem, lbIsR, lbIsW]


section seg
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- `wpdAnnotEntail` (AxSpinH5) at Ixv6, in the `wpdM` form of the positional leaves. -/
theorem AxSpinApA.annotEntailX (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent)
    (Ψ : Athread → IProp GF) (s : Athread) (e : Geid) (P Q : IProp GF) (HPQ : P ⊢ Q) :
    ⊢ AxAnnot.annotOwn e P -∗
      (AxAnnot.annotOwn e Q -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ :=
  wpdAnnotEntail (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 L) nm i Ψ s e P Q
    HPQ

variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_apa_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-- (Lean-only) `paZ (ofInt a) = a` everywhere, side conditions by `omega`. -/
local macro "ax_spin_apa_pz" : tactic =>
  `(tactic| simp (disch := omega) only [AxSpinApA.paZOf])

/-- (Lean-only) pairwise disjointness of concrete ranges. -/
local macro "ax_spin_apa_dj" : tactic =>
  `(tactic| (simp [List.pairwise_cons, dj, disj8] <;> omega))

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn HΨmid in
/-- THE RELEASE PIECE: from `jal release` (allocproc + 0x94, row position `t2KRl q`) through
release (`wpdRelease`), `c.li a5,1` and the terminal private store `c.sw a5,24(s1)`
(`p->state`, `FstMPriv 4`) to the row end `t2Len q`, `PC = allocproc + 0x9c`, `a3` kept. -/
theorem AxSpinApA.segRel (q : T2Prm) (S p : Int) (H : AxSpinApA.Hyp L GT σi T i q S p)
    (rsR : RegFile) (ibR : Ibch) (cls : WmClass) :
    ctrlOkSW T satp0 rsR → rsR .PC = pca 0x94 → AxSpinApA.Warm rsR i S p →
    gprVal rsR 2#5 = BitVec.ofInt 64 S → gprVal rsR 4#5 = hartId (cpuOf i) →
    gprVal rsR 9#5 = BitVec.ofInt 64 p →
    gprVal rsR 10#5 = BitVec.ofNat 64 KernelSyms.«pid_lock» →
    (AxOpsem.grow (gtAdGd GT) i)[t2KMy q + 4]? = some (.LStore false (L.xlLk + 16)
      (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i)))) cls) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, t2KA q) (locked nm.xnReg L.xlLk i (i, t2KA q)) -∗
      AxAnnot.annotOwn (GF := GF) (i, t2KMy q + 4)
        iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, t2KMy q + 4)
          (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i))))) -∗
      AxAnnot.annotOwn (i, t2KBd q + 65)
        (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, t2KBd q + 65)) -∗
      (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x9c ∧ rs' .tlb = rsR .tlb ∧
          gprVal rs' 13#5 = gprVal rsR 13#5⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', t2Len q⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsR none ibR, t2KRl q⟩ Ψ := by
  intro Hc HPC Hw E2 E4 E9 E10 Hkw
  have HF := H.full
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := AxSpinApA.nums H.lay
  obtain ⟨P1, P2, P3, P4, P5, P6, P7⟩ := AxSpinApA.posFacts HF H.lay
  have hproc : (KernelSyms.«proc» : Int) = 0x80012930 := rfl
  have hlen : (AxOpsem.grow (gtAdGd GT) i).length = t2Len q := HF.2.1
  have hTl : t2Len q = t2KRl q + relLen q.c + 1 := by rw [t2Len, AxSpinT2a.kTEq]
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix Ψ HΨmid
  have XS := XxStF L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix Ψ HΨmid
  have HP := H.pins
  -- the claim's label
  obtain ⟨tA, rvsA, HrmA, -⟩ := allocSpinRmw HF q.n (Nat.le_refl _)
  have HrmA' : (AxOpsem.grow (gtAdGd GT) i)[t2KA q]? =
      some (Lbl.LRmw true false L.xlLk [tA, tA, tA, tA] rvsA AxSpinX4.o4 .WCexcl) := by
    rw [H.hLk]; exact HrmA
  iintro #Hil HLK HW HNp K
  iapply (AxSpinApA.annotEntailX L GT nm i Ψ _ (i, t2KA q) _ _ (AxSpinApA.sepTrue _)) $$ HLK
  iintro HLK
  -- ---- + 0x94: jal ra,release (t2KRl) ----
  have Hcj : CertC (ctrlOkSW T satp0) rsR (pca 0x94) false ap94 (some (AxSpinHdB.prl 0))
      (some (1#5, BitVec.addInt (pca 0x94) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rsR (pca 0x94)
      false 2093274#21 1#5 (by decide)
    rw [show pca 0x94 + sign_extend (m := 64) 2093274#21 = AxSpinHdB.prl 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (pca 0x94) (incr false)) =
      some (1#5, BitVec.addInt (pca 0x94) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rsR (t2KRl q) (pca 0x94) false ap94 (some (AxSpinHdB.prl 0))
    (some (1#5, BitVec.addInt (pca 0x94) (incr false)))
    (retxRefl cpu rsR (t2KRl q) ibR) Hc HPC (AxSpinApA.hitTxt rsR Hw _ (by decide) (by decide))
    (atok94 σi T satp0 H.txc) (AxSpinE8.owOkSome 1#5 _ (by decide)) rfFAp94 Hcj
    (by rw [hlen]; omega))
  iintro %rsJ %ibJ %HGJ
  have HFJ := stepRegs T satp0 _ rsR _ _ _ _ _ rsJ (fun _ => rfl) HGJ
  have HPCJ : rsJ .PC = AxSpinHdB.prl 0 := by rw [gbPc T satp0 _ _ _ _ _ _ HGJ]; rfl
  have HtlJ : rsJ .tlb = rsR .tlb := gbTlb T satp0 _ _ _ _ _ _ HGJ
  have HcJ := gbCtrl T satp0 _ _ _ _ _ _ HGJ
  have HwJ := AxSpinApA.warmTlb rsR rsJ i S p HtlJ Hw
  have EJ2 : gprVal rsJ AxSpinE8.r2 = BitVec.ofInt 64 S := by
    rw [HFJ]; ax_spin_apa_zsimp; exact E2
  have EJ4 : gprVal rsJ AxSpinE8.r4 = hartId (cpuOf i) := by
    rw [HFJ]; ax_spin_apa_zsimp; exact E4
  have EJ9 : gprVal rsJ AxSpinHd8.r9 = BitVec.ofInt 64 p := by
    rw [HFJ]; ax_spin_apa_zsimp; exact E9
  have EJ10 : gprVal rsJ AxSpinE8.r10 = BitVec.ofNat 64 KernelSyms.«pid_lock» := by
    rw [HFJ]; ax_spin_apa_zsimp; exact E10
  have EJ13 : gprVal rsJ 13#5 = gprVal rsR 13#5 := by
    rw [HFJ]; ax_spin_apa_zsimp
  -- the holding read's label (for `CpuWin (i, relKh + 4)`)
  obtain ⟨lbH, HlbH, HsH⟩ := (allocRelease HF).1 7 (.it (.RL (AxSpinT2a.zLk + 16) 8)) rfl
  obtain ⟨aqH, HidH⟩ := HsH
  obtain ⟨tsH, vsH, HlH, HvsH⟩ : ∃ ts vs, lbH = .LLoad aqH (AxSpinT2a.zLk + 16) ts vs ∧
      vs.length = 8 := by
    cases lbH with
    | LLoad a b ts vs =>
      simp only [aident, AidentT.IRead.injEq] at HidH
      obtain ⟨rfl, rfl, h⟩ := HidH
      exact ⟨ts, vs, rfl, h⟩
    | _ => simp [aident] at HidH
  subst HlH
  -- the nextpid store's label
  obtain ⟨lbS, HlbS, vwS, clsS, HlS, -⟩ := (allocBody HF).1 65 (.RS AxSpinT2a.zNp 4) rfl
  iapply (wpdRelease L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix H.txm H.txh H.txq
    H.txr Ψ HΨmid (t2KRl q) q.c rsJ ibJ (pca 0x98)
    (BitVec.ofInt 64 (S - 8)) (BitVec.ofInt 64 (S - 16)) (BitVec.ofInt 64 (S - 24))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
    (BitVec.ofInt 64 (AxSpinT2a.zLk + 16)) (BitVec.ofInt 64 (AxSpinT2a.zLk + 16))
    (BitVec.ofInt 64 AxSpinT2a.zLk) (BitVec.ofInt 64 AxSpinT2a.zLk)
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 64))
    (BitVec.ofInt 64 (cpuZ i + 120)) (BitVec.ofInt 64 (cpuZ i + 124))
    AxSpinT2a.zLk (t2KA q) (t2KMy q + 4) (t2KBd q + 65)
    (AxSpinE8.mycpuRet (hartId (cpuOf i))) cls iprop(True) iprop(True)
    [tA, tA, tA, tA] rvsA AxSpinX4.o4 .WCexcl
    (by ax_spin_apa_pz; exact allocRelease HF) (allocW8 HF)
    (allocNoRmw8 HF _) (allocNoRmw8 HF _) (allocNoRmw8 HF _) (allocNoRmw8 HF _)
    (allocNoRmw8 HF _) (allocNoRmw8 HF _) (allocNoRmw8 HF _) (allocNoRmw8 HF _)
    (allocNoRmw8 HF _) (allocNoRmw8 HF _) (allocNoRmw8 HF _) (allocNoRmw8 HF _)
    (allocNoRmw8 HF _)
    (by ax_spin_apa_pz; exact AxSpinApA.wle4 HF H.lay _ (.inl rfl))
    (allocNoRmwn HF _ 4 (.inl (by ax_spin_apa_pz; omega)))
    (allocNoRmwn HF _ 4 (.inl (by ax_spin_apa_pz; omega)))
    HcJ HPCJ (AxSpinApA.hitTxt rsJ HwJ _ (by decide) (by decide))
    (AxSpinApA.hitTxt rsJ HwJ _ (by decide) (by decide))
    (by rw [EJ2, AxSpinApA.aA24]; exact AxSpinApA.slot H rsJ HwJ 8 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aA16]; exact AxSpinApA.slot H rsJ HwJ 16 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aA8]; exact AxSpinApA.slot H rsJ HwJ 24 (by omega) (by omega) (by omega))
    (by ax_spin_apa_pz; apply AxSpinApA.alldjOf; ax_spin_apa_dj)
    (by ax_spin_apa_pz; simp only [relWr]; ax_spin_apa_dj)
    (by rw [EJ2, AxSpinApA.aH24]; exact AxSpinApA.slot H rsJ HwJ 40 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aH16]; exact AxSpinApA.slot H rsJ HwJ 48 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aH8]; exact AxSpinApA.slot H rsJ HwJ 56 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aQm8]; exact AxSpinApA.slot H rsJ HwJ 72 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aQm0]; exact AxSpinApA.slot H rsJ HwJ 80 (by omega) (by omega) (by omega))
    (by ax_spin_apa_pz; apply AxSpinApA.slotsDisjOf; ax_spin_apa_dj)
    (by rw [EJ2, AxSpinApA.aM8]; exact AxSpinApA.slot H rsJ HwJ 40 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aM0]; exact AxSpinApA.slot H rsJ HwJ 48 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aMm8]; exact AxSpinApA.slot H rsJ HwJ 56 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aMm0]; exact AxSpinApA.slot H rsJ HwJ 64 (by omega) (by omega) (by omega))
    (by rw [EJ4, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i120Of rfl]
        exact AxSpinApA.fld H rsJ HwJ 120 (.inl rfl))
    (by rw [EJ4, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i124Of rfl]
        exact AxSpinApA.fld H rsJ HwJ 124 (.inr rfl))
    (by ax_spin_apa_pz; apply AxSpinApA.alldjOf; ax_spin_apa_dj)
    (by rw [EJ10, AxSpinApA.lk0, show AxSpinT2a.zLk = AxSpinT2a.zLk + 0 by omega]
        exact AxSpinApA.hitLk rsJ HwJ 0 (by omega) (by omega))
    (by rw [EJ10, AxSpinApA.lk16]; exact AxSpinApA.hitLk rsJ HwJ 16 (by omega) (by omega))
    (by rw [EJ10, AxSpinApA.lk0]
        exact AxSpinApA.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by ax_spin_apa_pz; exact AxSpinApA.ntxOf H _ (by omega))
    (by rw [EJ10, AxSpinApA.lk0]
        exact AxSpinApA.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [H.hLk]; ax_spin_apa_pz)
    (by rw [EJ10, AxSpinApA.lk16]
        exact AxSpinApA.dat H _ (.inl rfl) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [H.hLk]; ax_spin_apa_pz)
    (by ax_spin_apa_pz; exact AxSpinApA.ntxOf H _ (by omega))
    (by rw [EJ10, AxSpinApA.lk16]
        exact AxSpinApA.dat H _ (.inr (.inl rfl)) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [H.hLk]; ax_spin_apa_pz)
    HrmA' (by simp only [relKh]; omega)
    (by
      intro w v Hwb Hpo1 Hpo2
      obtain ⟨lb, rl, b, m, t, Hlb, Hid, Ht, Ha⟩ := AxSpinApA.gwbRow _ w _ _ Hwb
      obtain ⟨hw1, hw2, -, -⟩ := Hpo1
      obtain ⟨-, hw3, -, -⟩ := Hpo2
      simp only at hw1 hw2 hw3
      rw [← hw1] at Hlb
      have := AxSpinApA.lkBetween HF H.lay w.2 lb rl b m hw2 hw3 Hlb Hid
      rw [H.hLk] at Ha
      unfold dj at this
      omega)
    Hkw (by simp only [relKh]; omega)
    (by
      intro w a v Ha Hwb Hpo1 Hpo2
      obtain ⟨lb, rl, b, m, t, Hlb, Hid, Ht, Hab⟩ := AxSpinApA.gwbRow _ w _ _ Hwb
      obtain ⟨hw1, hw2, -, -⟩ := Hpo1
      obtain ⟨-, hw3, -, -⟩ := Hpo2
      simp only at hw1 hw2 hw3
      rw [← hw1] at Hlb
      have := AxSpinApA.clbBetween HF H.lay w.2 lb rl b m hw2 hw3 Hlb Hid
      unfold clb at Ha
      rw [inClr, H.hLk] at Ha
      unfold dj at this
      omega)
    (allocCpuWin L GT i q S p _ HF H.hLk (by
      intro k lb rl m hk Hlb Hid
      obtain ⟨vw, cls', rfl, Hv⟩ := allocCpuVals HF k lb rl m Hlb (by rw [← H.hLk]; exact Hid)
      refine AxSpinRl2.lobpCpuSt GT Hcons (L.xlLk + 16) i _ k _ vw cls cls' Hkw
        (List.ne_nil_of_length_pos (by rw [wbytesLength]; omega)) (by rw [H.hLk]; exact Hlb)
        ?_ hk
      rcases Hv with rfl | rfl
      · exact List.ne_nil_of_length_pos (by rw [cvxLength]; omega)
      · exact List.ne_nil_of_length_pos (by simp)))
    (allocCpuWin L GT i q S p _ HF H.hLk (by
      intro k lb rl m hk Hlb Hid
      obtain ⟨vw, cls', rfl, Hv⟩ := allocCpuVals HF k lb rl m Hlb (by rw [← H.hLk]; exact Hid)
      refine AxSpinRl2.lobpCpuLd GT Hcons (L.xlLk + 16) i _ k aqH tsH vsH vw cls'
        (by rw [H.hLk]; exact HlbH) (List.ne_nil_of_length_pos (by omega))
        (by rw [H.hLk]; exact Hlb) ?_ (by simp only [relKh] at hk ⊢; omega)
      rcases Hv with rfl | rfl
      · exact List.ne_nil_of_length_pos (by rw [cvxLength]; omega)
      · exact List.ne_nil_of_length_pos (by simp)))
    (by rw [H.hLk]; exact allocRelZ4 HF)
    (allocRelWinC (AxSpinApA.privNe HF H.lay) HF L H.hLk)
    (by omega) ⟨lbS, HlbS, by rw [HlS]; rfl⟩
    HP.rhRets.1 HP.rhRets.2
    (by rw [EJ4, AxSpinT2a.mycpuRetHart]; exact HP.rhCpu)
    (by rw [EJ10]; exact HP.rhS1)
    HP.ppMy HP.ppGe HP.ppArm HP.ppInt HP.ppRet HP.rlRet AxSpinT2a.jalrRets.2.2.2.2.2.2)
    $$ Hil HLK HW HNp
  iintro %vra %vs0 %vs1 %rs1 %ib1 %Hf - - - -
  obtain ⟨Hc1, HPC1, Htl1, -, -, -, -, -, -, -, E91, Hkeep1, -, -, Hgd2, -, -, Hgv2⟩ := Hf
  have Evs1 : vs1 = stBytes 8 (BitVec.ofInt 64 p) := by
    have h := HP.rlS1
    rw [show t2KRr q = relKr (t2KRl q) q.c from rfl, Hgv2, Hgd2, EJ9] at h
    exact Option.some.inj h
  rw [Evs1, AxSpinE8.ldResStBytes8] at E91
  have E131 : gprVal rs1 13#5 = gprVal rsR 13#5 :=
    (Hkeep1 13#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      EJ13
  have Htl1' : rs1 .tlb = rsR .tlb := Htl1.trans HtlJ
  have Hw1 := AxSpinApA.warmTlb rsR rs1 i S p Htl1' Hw
  -- ---- + 0x98: c.li a5,1 (t2KT) ----
  iapply (XR _ rs1 (relKe (t2KRl q) q.c) (pca 0x98) true ap98 none _
    (retxRefl cpu rs1 (relKe (t2KRl q) q.c) ib1) Hc1 HPC1 (AxSpinApA.hitTxt rs1 Hw1 _ (by decide) (by decide))
    (AxSpinApA.atok98 σi T satp0 H.txt) (AxSpinE8.owOkSome 15#5 _ (by decide)) AxSpinApA.rfFAp98
    (certAddi _ rs1 (pca 0x98) true (zero_extend (m := 5) 0b00#2) 15#5
      (sign_extend (m := 12) (1#6)) (by decide)) (by rw [hlen]; exact AxSpinT2a.kTLen q))
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 (fun _ => rfl) HG2
  have HPC2 : rs2 .PC = pca 0x9a := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rsR .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1'
  have Hw2 := AxSpinApA.warmTlb rsR rs2 i S p Htl2 Hw
  have E92 : gprVal rs2 9#5 = BitVec.ofInt 64 p := by rw [HF2]; ax_spin_apa_zsimp; exact E91
  have E132 : gprVal rs2 13#5 = gprVal rsR 13#5 := by rw [HF2]; ax_spin_apa_zsimp; exact E131
  have Eva : gprVal rs2 9#5 + sign_extend (m := 64) 24#12 = BitVec.ofInt 64 (p + 24) := by
    rw [E92]; exact AxSpinApA.vaEq _ _ _ _ AxSpinApA.i24Of rfl
  ihave Fp := FstMPriv (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ (BitVec.ofInt 64 (p + 24))) 4
    (by
      intro j hj
      rw [AxSpinApA.paZOf (p + 24) (by omega) (by omega)]
      exact H.hpriv _ (.inr (.inl ⟨by omega, by omega⟩)))
    (by
      rw [AxSpinApA.paZOf (p + 24) (by omega) (by omega)]
      exact AxSpinApA.wle4 HF H.lay _ (.inr (.inr (.inr rfl))))
  -- ---- + 0x9a: c.sw a5,24(s1) — THE TERMINAL PRIVATE STORE (t2KT) ----
  iapply (XS _ rs2 (relKe (t2KRl q) q.c) (pca 0x9a) true 24#12 15#5 9#5 4
    (gprVal rs2 9#5 + sign_extend (m := 64) 24#12) (BitVec.ofInt 64 (p + 24))
    (fun _ _ => iprop(True))
    (retxRefl cpu rs2 (relKe (t2KRl q) q.c) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (AxSpinApA.hitTxt rs2 Hw2 _ (by decide) (by decide))
    (AxSpinApA.atok9a σi T satp0 H.txt) AxSpinAp9.vw4 (by decide) (by decide) rfl
    (by rw [Eva]
        exact AxSpinApA.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inr
          (.inr ⟨by omega, by omega⟩)))))
    (by rw [Eva]
        refine Hw2 _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl ?_)))))))
        rw [AxSpinApA.toNatOf _ (by omega) (by omega)]
        omega)
    (by rw [hlen]; exact Nat.le_refl _))
    $$ Fp
  iintro %rs3 %ib3 %HG3 %- -
  rw [show relKe (t2KRl q) q.c + 1 = t2Len q from rfl]
  iapply K $$ %rs3 %ib3
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG3, ?_, (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2, ?_⟩
  · rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  · rw [stepRegs0 T satp0 _ rs2 _ _ _ rs3 (fun _ => rfl) HG3]; exact E132

/-- THE SEGMENT'S CONTINUATION at the row end `t2Len q` (`PC = allocproc + 0x9c`): the issued pid
`w` is in `a3` (`sext32 w`) and is the `p->pid` store's data; the nextpid read's source fact and
the minted exclusive fragment are the two annotations; the TLB is the entry TLB. -/
def AxSpinApA.KSeg (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64)
    (i : Agent) (cpu : CPU) (Ψ : Athread → IProp GF) (q : T2Prm) (rs0 : RegFile) : IProp GF :=
  iprop(∀ (w : BitVec 32) (rs' : RegFile) (ib' : Ibch),
    ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x9c ∧ rs' .tlb = rs0 .tlb ∧
      gprVal rs' 13#5 = AxSpinT2a.sext32 w ∧
      pidOf (gtAdGd GT) i q = some (WeakInterpProj.wbytes 4 w)⌝ -∗
    AxAnnot.annotOwn (GF := GF) (i, t2KBd q)
      iprop(⌜npSrc (gtAdGd GT).gdG L (i, t2KBd q) (i, t2KA q)⌝) -∗
    AxAnnot.annotOwn (i, t2KBd q + 65) (FRAG nm w) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', t2Len q⟩ Ψ)

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn HΨmid in
/-- THE CRITICAL-SECTION PIECE: from acquire's return (allocproc + 0x44, row position
`t2KBd q`) through `wpdAllocpidCs` (anchor = the claim `(i, t2KA q)`, lob-before the nextpid
read by ppo rule 5; `Opid := FstMPriv 4` at `p->pid`) and `AxSpinApA.segRel` to the row end. -/
theorem AxSpinApA.segCs (q : T2Prm) (S p : Int) (H : AxSpinApA.Hyp L GT σi T i q S p)
    (rs0 rsC : RegFile) (ibC : Ibch) (cls : WmClass) :
    ctrlOkSW T satp0 rsC → rsC .PC = pca 0x44 → rsC .tlb = rs0 .tlb →
    AxSpinApA.Warm rsC i S p →
    gprVal rsC 2#5 = BitVec.ofInt 64 S → gprVal rsC 4#5 = hartId (cpuOf i) →
    gprVal rsC 9#5 = BitVec.ofInt 64 p →
    (AxOpsem.grow (gtAdGd GT) i)[t2KMy q + 4]? = some (.LStore false (L.xlLk + 16)
      (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i)))) cls) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, t2KA q) (locked nm.xnReg L.xlLk i (i, t2KA q)) -∗
      AxAnnot.annotOwn (i, t2KA q) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, t2KA q)) -∗
      AxAnnot.annotOwn (GF := GF) (i, t2KMy q + 4)
        iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, t2KMy q + 4)
          (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i))))) -∗
      AxSpinApA.KSeg (hlc := hlc) L GT nm T satp0 i cpu Ψ q rs0 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsC none ibC, t2KBd q⟩ Ψ := by
  intro Hc HPC Htl Hw E2 E4 E9 Hkw
  have HF := H.full
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := AxSpinApA.nums H.lay
  obtain ⟨P1, P2, P3, P4, P5, P6, P7⟩ := AxSpinApA.posFacts HF H.lay
  have hproc : (KernelSyms.«proc» : Int) = 0x80012930 := rfl
  have HP := H.pins
  -- the claim and the read labels
  obtain ⟨tA, rvsA, HrmA, -⟩ := allocSpinRmw HF q.n (Nat.le_refl _)
  obtain ⟨lbR, HlbR, aqR, HidR⟩ := (allocBody HF).1 0 (.RL AxSpinT2a.zNp 4) rfl
  rw [Nat.add_zero] at HlbR
  have HmR : lbIsMem lbR = true := by
    cases lbR with
    | LLoad => rfl
    | _ => simp [aident] at HidR
  have He : (i, t2KA q) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, t2KBd q) :=
    AxSpinRl2.lobpAcq GT Hcons i (t2KA q) (t2KBd q) _ lbR AxSpinT2a.zLk 4 HrmA rfl HlbR HmR
      (by omega)
  have Eva : gprVal rsC 9#5 + sign_extend (m := 64) 48#12 = BitVec.ofInt 64 (p + 48) := by
    rw [E9]; exact AxSpinApA.vaEq _ _ _ _ AxSpinApA.i48Of rfl
  ihave Fp := FstMPriv (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ (BitVec.ofInt 64 (p + 48)))
    4
    (by
      intro j hj
      rw [AxSpinApA.paZOf (p + 48) (by omega) (by omega)]
      exact H.hpriv _ (.inr (.inr (.inl ⟨by omega, by omega⟩))))
    (by
      rw [AxSpinApA.paZOf (p + 48) (by omega) (by omega)]
      exact AxSpinApA.wle4 HF H.lay _ (.inr (.inr (.inl rfl))))
  unfold AxSpinApA.KSeg
  iintro #Hil HLK HRN HW K
  iapply (wpdAllocpidCs L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix H.txc Ψ HΨmid
    (t2KBd q) rsC ibC vaNp (BitVec.ofInt 64 (p + 48)) AxSpinAp9.scanVa (i, t2KA q)
    (fun _ _ => iprop(True))
    (by rw [AxSpinApA.npOf]; ax_spin_apa_pz; exact allocBody HF)
    (allocBodyLen HF)
    (by
      rw [AxSpinApA.npOf]
      ax_spin_apa_pz
      exact AxSpinApA.npOnly HF H.lay)
    (by
      intro w a v' Ha Hwb Hpo
      exfalso
      obtain ⟨lb, rl, b, m, t, Hlb, Hid, Ht, Hab⟩ := AxSpinApA.gwbRow _ w _ _ Hwb
      obtain ⟨hw1, hw2, -, -⟩ := Hpo
      simp only at hw1 hw2
      rw [hw1] at Hlb
      have := AxSpinApA.npBefore HF H.lay w.2 lb rl b m hw2 Hlb Hid
      unfold npb at Ha
      rw [inClr, H.hNp] at Ha
      unfold dj at this
      omega)
    HP.npNowrap HP.npNcoll Hc HPC (AxSpinApA.hitTxt rsC Hw _ (by decide) (by decide))
    (by rw [AxSpinApA.npOf, H.hNp]; ax_spin_apa_pz)
    (by rw [AxSpinApA.npOf]; ax_spin_apa_pz; exact AxSpinApA.ntxOf H _ (by omega))
    (by rw [AxSpinApA.npOf]
        exact AxSpinApA.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))
    (by rw [AxSpinApA.npOf]
        exact AxSpinApA.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))
    (Hw _ (t2TouchNp i S p))
    (by
      intro j hj
      rw [AxSpinApA.scanOf j hj]
      have hsa : AxSpinAp7.scanAddr j = 0x80012930 + 376 * (j : Int) + 48 := by
        unfold AxSpinAp7.scanAddr; rw [hproc]
      refine ⟨AxSpinApA.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))),
        AxSpinApA.paZOf _ (by omega) (by omega), ?_⟩
      rw [← AxSpinApA.scanOf j hj]
      exact Hw _ (t2TouchScan i S p j hj))
    (by rw [Eva]
        exact AxSpinApA.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))))
    (by rw [Eva]
        refine Hw _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr ?_)))))))
        rw [AxSpinApA.toNatOf _ (by omega) (by omega)]
        omega)
    He) $$ HRN Fp
  iintro %vs %rs1 %ib1 %Hf Hsrc HRN65 HFR -
  obtain ⟨Hc1, HPC1, Htl1, -, -, E131, -, -, E101, -, -, Hkeep1, -, Hgd66⟩ := Hf
  have Hw1 := AxSpinApA.warmTlb rsC rs1 i S p Htl1 Hw
  rw [show t2KBd q + 67 = t2KRl q from rfl]
  iapply (AxSpinApA.segRel L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Ψ HΨmid q S p H
    rs1 ib1 cls Hc1 HPC1 Hw1
    ((Hkeep1 2#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E2)
    ((Hkeep1 4#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E4)
    ((Hkeep1 9#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E9)
    E101 Hkw) $$ Hil HLK HW HRN65
  iintro %rs2 %ib2 %Hf2
  obtain ⟨Hc2, HPC2, Htl2, E132⟩ := Hf2
  iapply K $$ %(wordOfBytes 4 vs) %rs2 %ib2 [] Hsrc HFR
  ipureintro
  refine ⟨Hc2, HPC2, Htl2.trans (Htl1.trans Htl), ?_, Hgd66⟩
  rw [E132, E131]
  rfl

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn HΨmid in
/-- **THE WHOLE-SEGMENT WPd** (Theorem 2 design §C.3): hart `i`'s inlined allocpid inside
`allocproc`, from `allocproc + 0x38` (row position 0; `sp = S`, `s1 = p`, `tp = hartId (cpuOf
i)`, interrupts off, warm TLB) through `auipc/addi a0 = &pid_lock`, `jal acquire`
(`AxSpinAq2.wpdAcquire`, return to + 0x44), the critical section (`wpdAllocpidCs`), `jal release`
(`wpdRelease`, return to + 0x98), `c.li a5,1` and the terminal private store `c.sw a5,24(s1)`
(+ 0x9a) to the row end `t2Len q` (`AxSpinApA.KSeg`: `a3 = sext32 w`, `pidOf = wbytes 4 w`, the
`npSrc` and `FRAG nm w` annotations), on any row of the family (`AxSpinApA.Hyp`: `allocFull`,
the Option V / Q18b pins `AllocPins`, the layout, the translation, the text). -/
theorem wpdAllocpidSeg (q : T2Prm) (S p : Int) (H : AxSpinApA.Hyp L GT σi T i q S p)
    (rs0 : RegFile) (ib0 : Ibch) :
    ctrlOkSW T satp0 rs0 → rs0 .PC = pca 0x38 → AxSpinApA.Warm rs0 i S p →
    gprVal rs0 2#5 = BitVec.ofInt 64 S → gprVal rs0 4#5 = hartId (cpuOf i) →
    gprVal rs0 9#5 = BitVec.ofInt 64 p →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinApA.KSeg (hlc := hlc) L GT nm T satp0 i cpu Ψ q rs0 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, 0⟩ Ψ := by
  intro Hc HPC Hw E2 E4 E9
  have HF := H.full
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := AxSpinApA.nums H.lay
  obtain ⟨P1, P2, P3, P4, P5, P6, P7⟩ := AxSpinApA.posFacts HF H.lay
  have hlen : (AxOpsem.grow (gtAdGd GT) i).length = t2Len q := HF.2.1
  have hl0 : 0 < (AxOpsem.grow (gtAdGd GT) i).length := by rw [hlen]; unfold t2Len; omega
  have HP := H.pins
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix Ψ HΨmid
  obtain ⟨tA, rvsA, HrmA, -⟩ := allocSpinRmw HF q.n (Nat.le_refl _)
  iintro #Hil Hnh K
  -- ---- + 0x38: auipc a0,0x11 (row 0) ----
  iapply (XR _ rs0 0 (pca 0x38) false ap38 none (some (10#5, pca 0x38 + auipcOff 17#20))
    (retxRefl cpu rs0 0 ib0) Hc HPC (AxSpinApA.hitTxt rs0 Hw _ (by decide) (by decide))
    (atok38 σi T satp0 H.txc) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFAp38
    (certAuipc _ rs0 (pca 0x38) false 10#5 17#20 (by decide)) hl0)
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pca 0x3c := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- ---- + 0x3c: addi a0,a0,-1706 (a0 = &pid_lock) ----
  have Hc2 : CertC (ctrlOkSW T satp0) rs1 (pca 0x3c) false ap3c none
      (some (10#5, BitVec.ofNat 64 KernelSyms.«pid_lock»)) := by
    have h := certAddi (ctrlOkSW T satp0) rs1 (pca 0x3c) false 10#5 10#5 0x956#12 (by decide)
    simp only [HF1] at h
    ax_spin_apa_zsimp at h
    rw [AxSpinApA.a0Entry] at h
    exact h
  iapply (XR _ rs1 0 (pca 0x3c) false ap3c none _
    (retxRefl cpu rs1 0 ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (AxSpinApA.hitTxt rs1 (AxSpinApA.warmTlb rs0 rs1 i S p Htl1 Hw) _ (by decide) (by decide))
    (atok3c σi T satp0 H.txc) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFAp3c Hc2 hl0)
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = pca 0x40 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  -- ---- + 0x40: jal ra,acquire ----
  have Hcj : CertC (ctrlOkSW T satp0) rs2 (pca 0x40) false ap40 (some (AxSpinHdB.pac 0))
      (some (1#5, BitVec.addInt (pca 0x40) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs2 (pca 0x40)
      false 2093222#21 1#5 (by decide)
    rw [show pca 0x40 + sign_extend (m := 64) 2093222#21 = AxSpinHdB.pac 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (pca 0x40) (incr false)) =
      some (1#5, BitVec.addInt (pca 0x40) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs2 0 (pca 0x40) false ap40 (some (AxSpinHdB.pac 0))
    (some (1#5, BitVec.addInt (pca 0x40) (incr false)))
    (retxRefl cpu rs2 0 ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (AxSpinApA.hitTxt rs2 (AxSpinApA.warmTlb rs0 rs2 i S p Htl2 Hw) _ (by decide) (by decide))
    (atok40 σi T satp0 H.txc) (AxSpinE8.owOkSome 1#5 _ (by decide)) rfFAp40 Hcj hl0)
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = AxSpinHdB.pac 0 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; rfl
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  have Hc3 := gbCtrl T satp0 _ _ _ _ _ _ HG3
  have Hw3 := AxSpinApA.warmTlb rs0 rs3 i S p Htl3 Hw
  have E32 : gprVal rs3 AxSpinE8.r2 = BitVec.ofInt 64 S := by
    rw [HF3]; ax_spin_apa_zsimp; exact E2
  have E34 : gprVal rs3 AxSpinE8.r4 = hartId (cpuOf i) := by
    rw [HF3]; ax_spin_apa_zsimp; exact E4
  have E39 : gprVal rs3 9#5 = BitVec.ofInt 64 p := by
    rw [HF3]; ax_spin_apa_zsimp; exact E9
  have E310 : gprVal rs3 AxSpinE8.r10 = BitVec.ofNat 64 KernelSyms.«pid_lock» := by
    rw [HF3]; ax_spin_apa_zsimp
  -- ---- acquire (rows 0 .. t2KMy q + 8) ----
  iapply (AxSpinAq2.wpdAcquire L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix H.txa
    H.txm H.txp H.txh Ψ HΨmid 0 q.b q.hb q.n rs3 ib3 (pca 0x44)
    (BitVec.ofInt 64 (S - 8)) (BitVec.ofInt 64 (S - 16)) (BitVec.ofInt 64 (S - 24))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
    (BitVec.ofInt 64 (cpuZ i + 120)) (BitVec.ofInt 64 (cpuZ i + 124))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48))
    (BitVec.ofInt 64 (AxSpinT2a.zLk + 16)) (BitVec.ofInt 64 AxSpinT2a.zLk)
    (by rw [H.hLk]; ax_spin_apa_pz; exact allocAcquire HF)
    (by rw [H.hLk]; exact allocSpinRmw HF) HF.2.2.2.1 (allocW8 HF)
    (fun _ _ => allocNoRmw8 HF _)
    (by ax_spin_apa_pz; exact AxSpinApA.wle4 HF H.lay _ (.inl rfl))
    (allocNoRmwn HF _ 4 (.inl (by ax_spin_apa_pz; omega)))
    (by ax_spin_apa_pz; exact AxSpinApA.wle4 HF H.lay _ (.inr (.inl rfl)))
    (by
      intro k' lb aq rl m Hlb Hid
      obtain ⟨-, rfl⟩ := allocRmw HF k' lb aq rl _ m Hlb Hid
      omega)
    (allocCpuWin L GT i q S p _ HF H.hLk (by
      intro k lb rl m hk Hlb Hid
      exact AxSpinRl2.lobpAcq GT Hcons i (t2KA q) k _ lb AxSpinT2a.zLk 4 HrmA rfl Hlb
        (AxSpinApA.wrMem lb _ Hid) hk))
    Hc3 HPC3 (AxSpinApA.hitTxt rs3 Hw3 _ (by decide) (by decide))
    (AxSpinApA.hitTxt rs3 Hw3 _ (by decide) (by decide))
    (by rw [H.hLk]; ax_spin_apa_pz)
    (by ax_spin_apa_pz; exact AxSpinApA.ntxOf H _ (by omega))
    (by rw [E310, AxSpinApA.lkOf]
        exact AxSpinApA.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lkOf]
        exact AxSpinApA.dat H _ (.inr (.inr rfl)) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lkOf, show AxSpinT2a.zLk = AxSpinT2a.zLk + 0 by omega]
        exact AxSpinApA.hitLk rs3 Hw3 0 (by omega) (by omega))
    (by rw [H.hLk]; ax_spin_apa_pz)
    (by ax_spin_apa_pz; exact AxSpinApA.ntxOf H _ (by omega))
    (by rw [E310, AxSpinApA.lk16]
        exact AxSpinApA.dat H _ (.inl rfl) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lk16]
        exact AxSpinApA.dat H _ (.inr (.inl rfl)) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lk16]; exact AxSpinApA.hitLk rs3 Hw3 16 (by omega) (by omega))
    (by rw [E32, AxSpinApA.aA24]; exact AxSpinApA.slot H rs3 Hw3 8 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aA16]; exact AxSpinApA.slot H rs3 Hw3 16 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aA8]; exact AxSpinApA.slot H rs3 Hw3 24 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQ24]; exact AxSpinApA.slot H rs3 Hw3 40 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQ16]; exact AxSpinApA.slot H rs3 Hw3 48 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQ8]; exact AxSpinApA.slot H rs3 Hw3 56 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm8]; exact AxSpinApA.slot H rs3 Hw3 72 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm0]; exact AxSpinApA.slot H rs3 Hw3 80 (by omega) (by omega) (by omega))
    (by rw [E34, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i120Of rfl]
        exact AxSpinApA.fld H rs3 Hw3 120 (.inl rfl))
    (by rw [E34, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i124Of rfl]
        exact AxSpinApA.fld H rs3 Hw3 124 (.inr rfl))
    (by rw [E32, AxSpinApA.aH24]; exact AxSpinApA.slot H rs3 Hw3 40 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aH16]; exact AxSpinApA.slot H rs3 Hw3 48 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aH8]; exact AxSpinApA.slot H rs3 Hw3 56 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm8]; exact AxSpinApA.slot H rs3 Hw3 72 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm0]; exact AxSpinApA.slot H rs3 Hw3 80 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aM8]; exact AxSpinApA.slot H rs3 Hw3 40 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aM0]; exact AxSpinApA.slot H rs3 Hw3 48 (by omega) (by omega) (by omega))
    (by ax_spin_apa_pz; apply AxSpinApA.alldjOf; ax_spin_apa_dj)
    (by ax_spin_apa_pz; apply AxSpinApA.slotsDisjOf; ax_spin_apa_dj)
    (by ax_spin_apa_pz; unfold dj; omega)
    (by ax_spin_apa_pz; unfold dj; omega) (by ax_spin_apa_pz; unfold dj; omega)
    (by ax_spin_apa_pz; unfold dj; omega)
    (by
      rw [H.hLk]
      ax_spin_apa_pz
      simp only [AxSpinAq2.djOut, List.mem_cons, List.not_mem_nil, _root_.or_false,
        forall_eq_or_imp, forall_eq, dj]
      omega)
    HP.poMy1 HP.poArm HP.poMy2 HP.poMy3 HP.poRet (by rw [E310]; exact HP.poS1)
    (by
      intro hb
      obtain ⟨h7, h9⟩ := HP.hdRets hb
      refine ⟨h7, h9, by rw [E310]; exact HP.hdS1 hb, ?_⟩
      intro vcpu Hv
      rw [E34, AxSpinT2a.mycpuRetHart]
      exact (AxSpinT2a.hresZero _ _).2 (HP.hdArm hb vcpu Hv))
    HP.aqMy HP.aqRet AxSpinT2a.jalrRets.2.2.2.1) $$ Hil Hnh
  unfold AxSpinAq2.KAcq
  rw [E34, show aqKA 0 q.b q.hb q.n = t2KA q from rfl, show aqKm 0 q.b q.hb q.n = t2KMy q from rfl]
  iintro %vra' %vs0' %vs1' %rsC %ibC %Ht HLK HNp HDep - - -
  obtain ⟨HcC, HPCC, HtlC, EspC, -, -, -, -, -, -, Es1C, HkeepC, -, -, Hgd2, -, -, Hlb4, -, -,
    Hgv7⟩ := Ht
  obtain ⟨cls, Hlb4⟩ := Hlb4
  have Evs1 : vs1' = stBytes 8 (BitVec.ofInt 64 p) := by
    have h := HP.aqS1
    rw [Hgv7, show ((i, 2) : Geid) = (i, 0 + 2) from rfl, Hgd2, E39] at h
    exact Option.some.inj h
  rw [Evs1, AxSpinE8.ldResStBytes8] at Es1C
  rw [show t2KMy q + 8 = t2KBd q from rfl]
  iapply (AxSpinApA.segCs L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Ψ HΨmid q S p H
    rs0 rsC ibC cls HcC HPCC (HtlC.trans Htl3) (AxSpinApA.warmTlb rs0 rsC i S p (HtlC.trans Htl3) Hw)
    (EspC.trans E32)
    ((HkeepC 4#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E34)
    Es1C Hlb4) $$ Hil HLK HNp HDep K

end seg

/-! # 8. Past the row end: closing a state-independent post -/

/-- (Lean-only; as `AxAllHarts.astepProgRowEndShape'`, not imported here) past the row end, a
program step is administrative and keeps the position. -/
theorem AxSpinApA.rowEndShape (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread)
    (Hnone : row[s.atK]? = none) :
    AxOpsem.astepProg row s l s' → lbAdmin true l ∧ s'.atK = s.atK := by
  intro h
  cases h with
  | AStepAdmin p k d l p' d' hadm hst => exact ⟨hadm, rfl⟩
  | AStepWrite p k d l lb p' d' hlk _ _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone
  | AStepFence p k d l lb p' d' hlk _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone


section rowend
open Iris.Std.PartialMap
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- PAST THE ROW END, an annotation readback: from position `k0 ≥ LEN` every program state's
WPd holds for a STATE-INDEPENDENT post `P` that follows from owned annotations of hart `i`
(the hart may keep running register-only / administrative steps; no row item is left).  The
generic form of `AxSpinU2.shHltReadbackP` (which needs a halted node) and of
`AxAllHarts.wpdIdle` (post `True`). -/
theorem AxSpinApA.wpdEndAnn (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (m : Mea GF)
    (Hm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i) (Φ : Athread → IProp GF)
    (HRQ : ∀ s, ([∗map] R ∈ m, R) ⊢ Φ s) :
    ⊢ ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗ ∀ pr : Pexv6,
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have Hnone : (AxOpsem.grow (gtAdGd GT) i)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ pr : Pexv6, ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
    iloeb as IH
    iintro %pr Hp
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT)
      rvwmoCatConsistent .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (AxSpinX2.xG L GT nm) _ i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := (AxSpinWit.gconstEq (gtAdGd GT) Xv6N Unit (protXv6 L) nm GD') $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk'⟩ := AxSpinApA.rowEndShape _ _ l s' Hnone Hst
      rw [AxSpinRow.lbAdminWdata l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p' Hp
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p' Hp
    · iintro %-
      unfold postLifting
      iintro %na Hna
      ihave ⟨%Hdomi, #Hw⟩ := annotAgreeBig na m $$ Hna Hp
      imodintro
      isplitl [Hna]
      · iexact Hna
      iintro Hbig
      ihave HR := AxSpinProt7.readbackBig na m i Hdomi Hm $$ Hbig Hw
      inext
      imodintro
      iapply (HRQ _) $$ HR
  iintro Hp %pr
  iapply H $$ %pr Hp

/-- `AxSpinApA.wpdEndAnn` for two annotations at distinct events of hart `i`. -/
theorem AxSpinApA.wpdEnd2 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (e1 e2 : Geid) (h1 : e1.1 = i)
    (h2 : e2.1 = i) (hne : e1 ≠ e2) (P1 P2 : IProp GF) (Φ : Athread → IProp GF)
    (HRQ : ∀ s, iprop(P2 ∗ P1) ⊢ Φ s) :
    ⊢ AxAnnot.annotOwn e1 P1 -∗ AxAnnot.annotOwn e2 P2 -∗ ∀ pr : Pexv6,
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have hn1 : get? (∅ : Mea GF) e1 = none := lookupEmpty
  have hn2 : get? (insert (∅ : Mea GF) e1 P1) e2 = none := by
    rw [lookupInsertNe hne]; exact lookupEmpty
  have Hm : ∀ e, e ∈ (FiniteMap.dom_set (insert (insert (∅ : Mea GF) e1 P1) e2 P2) : GSet Geid) →
      e.1 = i := by
    intro e he
    rw [domInsert, domInsert, domEmpty] at he
    rcases elemOfUnion.1 he with h | h
    · rw [elemOfSingleton.1 h]; exact h2
    · rcases elemOfUnion.1 h with h | h
      · rw [elemOfSingleton.1 h]; exact h1
      · exact absurd h (fun h' => (elemOfEmpty (S := GSet Geid)).1 h')
  have HR : ∀ s, ([∗map] R ∈ insert (insert (∅ : Mea GF) e1 P1) e2 P2, R) ⊢ Φ s := by
    intro s
    iintro Hb
    icases (BigSepM.bigSepM_insert hn2).1 $$ Hb with ⟨H2, Hb⟩
    icases (BigSepM.bigSepM_insert hn1).1 $$ Hb with ⟨H1, -⟩
    iapply (HRQ s)
    isplitl [H2]
    · iexact H2
    · iexact H1
  iintro A1 A2
  iapply (AxSpinApA.wpdEndAnn L GT nm i k0 Hend _ Hm Φ HR)
  iapply (BigSepM.bigSepM_insert hn2).2
  isplitl [A2]
  · iexact A2
  iapply (BigSepM.bigSepM_insert hn1).2
  isplitl [A1]
  · iexact A1
  iapply BigSepM.bigSepM_empty.2
  itrivial

end rowend

/-! # 9. THE SEGMENT WITH ITS POST: the state-independent part of `t2Post` -/

/-- THE POST THAT CAN BE CLOSED PAST THE ROW END: `t2Post` without its `a3` conjunct (see the
header, "The `a3` conjunct"): at a non-mid state, an issued pid `w` that is the `p->pid` store's
data, the nextpid read's source fact, and the exclusive fragment. -/
def AxSpinApA.t2PostS {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (GD : Gdexec) (L : Xlay)
    (nm : Xv6N) (i : Agent) (q : T2Prm) (s : Athread) : IProp GF :=
  iprop(⌜¬ midState s⌝ -∗ ∃ w : BitVec 32,
    ⌜pidOf GD i q = some (WeakInterpProj.wbytes 4 w) ∧
      npSrc GD.gdG L (i, t2KBd q) (i, t2KA q)⌝ ∗ FRAG nm w)

section segS
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)

/-- The mid-instruction states' post is free (the `¬ midState` guard). -/
theorem AxSpinApA.postSMid (q : T2Prm) :
    ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) (AxSpinApA.t2PostS (gtAdGd GT) L nm i q) i s := by
  intro s Hm _
  refine @postLiftingTrue GF (AxSpinX2.xG L GT nm) _ _ i s ?_
  unfold AxSpinApA.t2PostS
  iintro - %Hn
  exact absurd Hm Hn

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn in
/-- **THE SEGMENT WPd WITH ITS POST** — `wpdAllocpidSeg` closed past the row end by the
annotation readback (`AxSpinApA.wpdEnd2`): from allocproc + 0x38, `WPd {{ t2PostS }}`. -/
theorem wpdAllocpidSegS (q : T2Prm) (S p : Int) (H : AxSpinApA.Hyp L GT σi T i q S p)
    (rs0 : RegFile) (ib0 : Ibch) :
    ctrlOkSW T satp0 rs0 → rs0 .PC = pca 0x38 → AxSpinApA.Warm rs0 i S p →
    gprVal rs0 2#5 = BitVec.ofInt 64 S → gprVal rs0 4#5 = hartId (cpuOf i) →
    gprVal rs0 9#5 = BitVec.ofInt 64 p →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, 0⟩ (AxSpinApA.t2PostS (gtAdGd GT) L nm i q) := by
  intro Hc HPC Hw E2 E4 E9
  have hlen : (AxOpsem.grow (gtAdGd GT) i).length = t2Len q := H.full.2.1
  iintro #Hil Hnh
  iapply (wpdAllocpidSeg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu
    (AxSpinApA.t2PostS (gtAdGd GT) L nm i q) (AxSpinApA.postSMid L GT nm i q) q S p H rs0 ib0
    Hc HPC Hw E2 E4 E9) $$ Hil Hnh
  unfold AxSpinApA.KSeg
  iintro %w %rs' %ib' %Hf HS HFr
  obtain ⟨-, -, -, -, Hpid⟩ := Hf
  ihave W := (AxSpinApA.wpdEnd2 L GT nm i (t2Len q) (by rw [hlen]; exact Nat.le_refl _) (i, t2KBd q) (i, t2KBd q + 65)
    rfl rfl (by intro h; have := congrArg Prod.snd h; simp at this)
    iprop(⌜npSrc (gtAdGd GT).gdG L (i, t2KBd q) (i, t2KA q)⌝) (FRAG nm w)
    (AxSpinApA.t2PostS (gtAdGd GT) L nm i q)
    (by
      intro s
      unfold AxSpinApA.t2PostS
      iintro ⟨HF, %Hsrc⟩ -
      iexists w
      isplitr
      · ipureintro
        exact ⟨Hpid, Hsrc⟩
      · iexact HF)) $$ HS HFr
  iapply W

end segS

/-! ## The joint step for `t2PostS` (the `a3`-free twin of `AxSpinT2a.t2Joint`) -/

/-- (the `a3`-free twin of `t2Phi`) A, B: `t2PostS`; anyone else: `True`. -/
def AxSpinApA.t2PhiS (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) :
    InvGS_gen .hasNoLC AxSpinX7.xv6GF → AxannotGS AxSpinX7.xv6GF → Xv6N → Agent → Athread →
      IProp AxSpinX7.xv6GF :=
  fun _ _ nm i s =>
    if i = A then AxSpinApA.t2PostS GD L nm A qA s
    else if i = B then AxSpinApA.t2PostS GD L nm B qB s else iprop(True)

/-- (the `a3`-free twin of `t2Concl`) -/
def AxSpinApA.t2ConclS (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) : Prop :=
  ∃ wA wB : BitVec 32,
    pidOf GD A qA = some (WeakInterpProj.wbytes 4 wA) ∧
    pidOf GD B qB = some (WeakInterpProj.wbytes 4 wB) ∧
    npSrc GD.gdG L (A, t2KBd qA) (A, t2KA qA) ∧ npSrc GD.gdG L (B, t2KBd qB) (B, t2KA qB) ∧
    wA ≠ wB

/-- (the `a3`-free twin of `t2Joint`) the three posts at non-mid final states give
`t2ConclS`, by issued-fragment exclusivity (`AxSpinT2a.fragNe`). -/
theorem AxSpinApA.t2JointS (GD : Gdexec) (L : Xlay) (A B C : Agent) (qA qB : T2Prm)
    (sN : Agent → Athread) (hAB : A ≠ B) (hmA : ¬ midState (sN A)) (hmB : ¬ midState (sN B))
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) :
    ⊢ ([∗list] i ∈ [A, B, C], AxSpinApA.t2PhiS GD L A B qA qB Hinv Hann nm i (sN i)) ==∗
      ⌜AxSpinApA.t2ConclS GD L A B qA qB⌝ := by
  have Htri : ([∗list] i ∈ [A, B, C], AxSpinApA.t2PhiS GD L A B qA qB Hinv Hann nm i (sN i)) ⊢
      AxSpinApA.t2PostS (GF := AxSpinX7.xv6GF) GD L nm A qA (sN A) ∗
        AxSpinApA.t2PostS (GF := AxSpinX7.xv6GF) GD L nm B qB (sN B) := by
    refine (AxSpinJ2.bigSepLTriple A B C _).1.trans ?_
    have hA : AxSpinApA.t2PhiS GD L A B qA qB Hinv Hann nm A (sN A) =
        AxSpinApA.t2PostS GD L nm A qA (sN A) := by simp [AxSpinApA.t2PhiS]
    have hB : AxSpinApA.t2PhiS GD L A B qA qB Hinv Hann nm B (sN B) =
        AxSpinApA.t2PostS GD L nm B qB (sN B) := by simp [AxSpinApA.t2PhiS, Ne.symm hAB]
    rw [hA, hB]
    exact sep_mono .rfl sep_elim_left
  iintro HI
  ihave HI := Htri $$ HI
  icases HI with ⟨HPA, HPB⟩
  unfold AxSpinApA.t2PostS
  ihave HPA := HPA $$ %hmA
  ihave HPB := HPB $$ %hmB
  icases HPA with ⟨%wA, %HwA, FA⟩
  icases HPB with ⟨%wB, %HwB, FB⟩
  ihave %Hne := (AxSpinT2a.fragNe (GF := AxSpinX7.xv6GF) nm wA wB) $$ [FA FB]
  · isplitl [FA]
    · iexact FA
    · iexact FB
  imodintro
  ipureintro
  exact ⟨wA, wB, HwA.1, HwB.1, HwA.2, HwB.2, Hne⟩

/-! ## For the capstone: the hypotheses at the real layout, the entry condition -/

/-- `AxSpinApA.Hyp` at the real layout `xlayXv6` (AxSpinT2a §5): the layout fields come from
`T2LayHyp` (plus the 16-alignment of allocproc's frame, which `T2LayHyp` does not state). -/
theorem AxSpinApA.hypXv6 (A B C : Agent) (Sf pf : Agent → Int) (ptp : Int → Prop)
    (HLay : T2LayHyp A B C Sf pf ptp) (GT : GdexecT) (σi : ExecSt) (T : PTree) (i : Agent)
    (q : T2Prm) (hi : i = A ∨ i = B ∨ i = C) (hal : Sf i % 16 = 0)
    (HF : allocFull (AxOpsem.grow (gtAdGd GT) i) q i (Sf i) (pf i))
    (HP : AllocPins (gtAdGd GT) i q) (Hmap : AxSpinApA.MapOk σi T i (Sf i) (pf i))
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    (Hfix : textFixed (gtAdGd GT) i (imgS σi)) :
    AxSpinApA.Hyp (xlayXv6 A B C Sf pf ptp) GT σi T i q (Sf i) (pf i) where
  full := HF
  pins := HP
  lay := ⟨AxSpinT2a.hartLt A B C Sf pf ptp HLay i hi, (HLay.stk i hi).1, (HLay.stk i hi).2, hal,
    HLay.slot i hi⟩
  hLk := rfl
  hNp := rfl
  hpriv := fun a ha => (AxSpinT2a.privIff A B C Sf pf ptp a i).2 ⟨hi, ha⟩
  ntx := fun _ h => h
  map := Hmap
  txa := Htxa
  txm := Htxm
  txp := Htxp
  txh := Htxh
  txq := Htxq
  txr := Htxr
  txc := Htxc
  txt := Htxt
  fix := Hfix

section segE
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- `wpdAllocpidSegS` from AxSpinT2a's `entryOk` (the capstone's `Hentry`). -/
theorem AxSpinApA.wpdAllocpidSegE (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) (i : Agent) (q : T2Prm)
    (S p : Int) (H : AxSpinApA.Hyp L GT σi T i q S p) (s : Athread) :
    entryOk T satp0 i S p s →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s
        (AxSpinApA.t2PostS (gtAdGd GT) L nm i q) := by
  rintro ⟨rs, ib, rfl, Hc, HPC, E2, E9, E4, Hw⟩
  exact wpdAllocpidSegS L GT nm HL Hcons σi T satp0 hmode hasid hppn i (cpuOf i) q S p H rs ib
    Hc HPC Hw E2 E4 E9

end segE

end Weak
