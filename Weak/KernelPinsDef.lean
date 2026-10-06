/-
Weak: **the static pin checker** -- a decidable re-check of one witness per LOAD site of the
kernel image (the definition side of the pin table `Weak/KernelPins.lean`).

Rocq: `iris/KernelPinsDef.v` @ xxvzwolszwmp (1cc222280).

Rocq header (verbatim, Rocq vocabulary):

    KernelPinsDef.v -- THE STATIC PIN CHECKER: a decidable re-check of one
    witness per LOAD site of the kernel image.

    HAND-WRITTEN, and the formal object of the effort.  tools/gen_pins.py is
    the untrusted witness GENERATOR (it does the CFG search); this file is what
    says the witnesses are true of the image.  The generated table and its two
    reflection lemmas live in iris/KernelPins.v -- the same split as
    KernelSitesDef.v / KernelSites.v, one level up in ambition.

    ---------------------------------------------------------------------
    WHAT THE PIN IS FOR (route-b design 4g / 4g.1).

    [l2_claim]'s only kernel content is: every cross-hart read that the row
    does not PIN before the hart's next write must be a [prot_read].  A read
    is pinned on its row when the row's own items order it before the write --
    [gacq_po] (the read is an acquire), [gfence_covers] (a fence between them),
    or [gd_deps] (address / data / control provenance into the write, DEC-4..7)
    -- or when it reads a byte no other hart writes (the hart's own stack, its
    per-cpu slot).  That is a VALUE-INDEPENDENT property of the binary, and
    this file decides it.

    So the seven witness classes below are not an ad-hoc taxonomy: [PCtrl] is
    ppo rule 11, [PDep] is rules 9/10 (through [deps_addr]/[deps_vsrc], with
    DEC-4's load-result provenance doing the transitive work), [PFence] is the
    fence rule, and [PStack]/[PPerCpu] are the no-other-writer cases.  [PCall]
    and [PResidue] certify NOTHING -- they are the audited residue, and the
    audit is tools/pins.md.

    ---------------------------------------------------------------------
    THE ROLE DECODER IS WeakDeps', NOT A SECOND ONE.

    Every operand question below goes through [WeakDeps.deps_of_bits] and its
    projections ([deps_ctrl], [deps_addr], [deps_vsrc], [deps_rd], [deps_rd2]).
    That is deliberate and it is the whole reason the check is worth anything:
    the same function decides which registers an instruction reads and writes
    HERE and in the emission ([WeakEvLang]'s [erw_of], the [LInstr]/[LLoad]/
    [LStore] labels), so a pin certified here transfers to the row's items with
    no second correspondence to prove.  KernelSitesDef's bitmask classifiers
    are used only where WeakDeps has no opinion -- [w_is_fence], which is
    [ORnone] as far as roles go -- and for the image bytes themselves
    ([kw], [w_size], [text_pcs]).

    ---------------------------------------------------------------------
    WHAT IS RE-CHECKED HERE AND WHAT IS TRUSTED TO PYTHON.  Honestly:

    * RE-CHECKED (slice 1): the witness event happens, at the pc the witness
      names, on the FALL-THROUGH path out of the load, with no intervening
      unpinned store, and with the taint arithmetic ([taint_step], over
      [deps_rd]/[deps_rd2]) that makes "the branch tests the loaded value" /
      "the store is fed by it" precise.

    * RE-CHECKED (slice 2), and this is what slice 1 trusted to Python:
      - CONTROL FLOW IS DECODED, not inferred from roles.  [kflow_of] reads
        every transfer out of the word: the conditional branches (both
        widths), [jal]/[c.j], the direct call, [ret], and every indirect
        transfer.  Slice 1 read control flow off [WeakDeps]' roles, and
        [c.j] HAS NO ROLE — so its straight-line walk stepped past an
        unconditional compressed jump.  (No slice-1 witness actually crossed
        one, checked against the image; but the checker would have taken it.)
      - THE FALL-THROUGH WALK FOLLOWS AND DESCENDS.  [fwalk] follows a
        direct jump and DESCENDS INTO A DIRECT CALL, keeping a return stack
        of depth [pin_depth]; a [ret] pops it.  So a witness may name a pc
        INSIDE a callee, and the checker walks there rather than trusting a
        summary table.  Deeper calls and indirect calls stop the walk
        ([PCall], the audited residue).
      - BOTH BRANCH ARMS.  [pdfs] is a fuel-bounded depth-first search with
        a visited set over the SAME [pstep]: every conditional branch
        contributes both successors, and it succeeds only when EVERY path
        out of the load reaches a pin before a store the load's value does
        not feed.  Every certifying witness carries it.  This is exactly
        the [all_paths] column of tools/pins.md, promoted from a Python
        fact to a [vm_compute] one.

    * THE ONE NEW ASSUMPTION, AND IT IS IN THE WITNESS.  A callee's first
      act is to spill to its own frame, so descending into a call is
      worthless unless a store through [sp] is not treated as the
      publication the pin is about.  Each of [PCtrl]/[PFence]/[PDep]
      therefore carries an [own : bool]: [false] means the check skipped NO
      store and rests on nothing beyond the image; [true] means it skipped
      stores whose base register is [sp], i.e. it rests on the exact dual of
      the [PStack] LOAD class ("[sp] addresses the hart's own frame").  The
      census splits the two, and at this revision only a small minority need
      [own = true].

    * STILL TRUSTED TO PYTHON: that the flat walk [text_pcs] covers every
      real instruction (KernelSitesDef 6.6 item 4), and that the bitmask
      classification agrees with the Sail decoder (item 1).  Note
      [pins_cover] is stated over [text_pcs], i.e. over the SUPERSET — at
      this revision no flat-walk position outside the real instruction
      stream decodes as a load at all.

    * AND THE IMMEDIATE DECODERS BELOW ([imm_b]/[imm_j]/[imm_cb]/[imm_cj])
      ARE NEW SURFACE.  Nothing in the tree relates them to the Sail
      decoder's own immediates; what does check them is tools/gen_pins.py's
      [audit_targets], which compares every computed target in the image
      against the target objdump printed (1688 agreeing, 0 disagreeing at
      this revision, reported in tools/pins.md), plus the [Example]s at the
      bottom of this file.  A wrong immediate here can only make the walk
      visit the wrong stretch, which is a checker soundness question, not a
      model one — recorded as the slice's residual trust item.

In this tree the generator is `tools/gen_weak_pins.py` (the Lean retarget of Rocq's
`tools/gen_pins.py`; it prints the census and the target audit instead of writing `pins.md`, and
`--json` writes Rocq's `pins.json`).  At this tree's revision its target audit reads 1788
agreeing, 0 disagreeing; no flat-walk position outside the real instruction stream decodes as a
load (the generator's `--check` fails if one does).

**Deviations from Rocq.**

1. THE IMAGE.  The checker runs over this tree's kernel (`Xv6/KernelImage.lean`, xv6-riscv
   b72cbac1; `KernelSitesDef` deviation 1), not the Rocq weak line's (9dd28f5e).  Every definition
   is the Rocq one; the EXAMPLES name this image's pcs:
   * `pinFirst`: this kernel's `forkret` reads `first.1` with a plain UNFENCED `lw` at
     `forkret+0x18` (Rocq: `forkret+0x1c`, fence at `+0x1e`), so the Rocq `PFence` witness has no
     counterpart; the site is CONTROL-pinned instead, by the `beqz` at `forkret+0x1c`, and
     `pinFirst` states that.  Added `pinFirstNotFence`: the Rocq-shaped `PFence` witness at
     `forkret+0x1c` is rejected.
   * `pinFilereadThroughCallee`: Rocq's `fileread+0x36` is this image's `fileread+0x42`
     (`ld a0,24(s1)`, the load immediately before `jal readi`); the pin is still the `beqz` at
     `readi+0x2`, with `own = false`.
   * every other example keeps its Rocq pcs (`main+0x16/0x18/0x1e`, `fileclose+0x2e/0x40`,
     `kexec+0x11c/0x12c`, `release+0x1a`, `acquire+0x0c`), each re-checked on this image.
2. TYPES.  Addresses are `Int` (Rocq `Z`); words and fields are `Nat` (`KernelSitesDef`
   deviation 3), so `zsext` takes a `Nat` field and returns an `Int`, and `imm_*` take the `Nat`
   word; `kword` is `BitVec.ofNat 32 (kw pc)` (Rocq `Z_to_bv 32 (kw pc)`); register names `wreg`
   are `Nat`; `Z.shiftl x k` ↦ `x <<< k`, `Z.shiftl 1 n` ↦ `2 ^ n`, `Z.testbit` ↦ `Nat.testBit`,
   `Z.land w 3` ↦ `w &&& 3`; `Nat.eqb` ↦ `Nat.beq`, `Nat.ltb` ↦ `Nat.blt`, `Z.eqb` ↦ `==`,
   `<?`/`<=?` ↦ `decide`; `existsb` ↦ `List.any`; `length` ↦ `List.length`.
3. `Z.to_nat 2/64/400` ↦ the literals (Lean `Nat` literals are binary, so the Rocq workaround is
   moot).  The record `pstate`/`PSt` is the structure `PState` with constructor `PSt`.
4. `vm_cast_no_check (eq_refl b)` ↦ `decide +kernel`; the Rocq `Example`s are named theorems; the
   `Print Assumptions` audit lines are not reproduced (the lint bans new axioms).
5. The Rocq `pin` type is `KernelPinsDef.Pin` (file-qualified: `pin` is also an `AxSymMem3`
   name); its constructors and `kflow`'s keep their Rocq spelling.

**Drift:** none (dependencies are `WeakDeps`, `WeakMem.Dsrc` and `KernelSitesDef`, all weak-line
ports).

**Name map** (Rocq → Lean): `kword`→`kword`, `krole`→`krole`, `role_is_load/store/branch`→
`roleIsLoad/Store/Branch`, `taint_mem`→`taintMem`, `taint_del`→`taintDel`,
`dsrc_tainted`→`dsrcTainted`, `srcs_tainted`→`srcsTainted`, `taint_upd1`→`taintUpd1`,
`taint_step`→`taintStep`, `zsext`→`zsext`, `imm_b/j/cb/cj`→`immB/J/Cb/Cj`, `kflow`→`Kflow`
(constructors `FLnone`…`FLind` unchanged), `kflow_of`→`kflowOf`, `pstate`→`PState` (`PSt`,
`ps_pc/ps_t/ps_rs`→`psPc/psT/psRs`), `listn_eqb`→`listnEqb`, `listz_eqb`→`listzEqb`,
`pstate_eqb`→`pstateEqb`, `pin_depth`→`pinDepth`, `stack_store`→`stackStore`, `pstep`→`pstep`,
`fwalk`→`fwalk`, `pdfs`→`pdfs`, `walk_to`→`walkTo`, `pin`→`KernelPinsDef.Pin` (constructors
unchanged), `pin_fuel`→`pinFuel`, `pdfs_fuel`→`pdfsFuel`, `load_rd`→`loadRd`, `pin_t0`→`pinT0`,
`pin_start`→`pinStart`, `all_paths_pinned`→`allPathsPinned`, `pinnedb`→`pinnedb`,
`pin_certifies`→`pinCertifies`, `pin_owned`→`pinOwned`, `pin_started`→`pinStarted`,
`pin_first`→`pinFirst`, `pin_fileclose_not_dep`→`pinFilecloseNotDep`,
`pin_fileclose_not_ctrl`→`pinFilecloseNotCtrl`, `pin_fileclose_not_dep_own`→
`pinFilecloseNotDepOwn`, `pin_fileread_through_callee`→`pinFilereadThroughCallee`,
`pin_kexec_fallthrough_still_ok`→`pinKexecFallthroughStillOk`,
`pin_kexec_not_all_paths`→`pinKexecNotAllPaths`, `pin_kexec_dep_rejected`→`pinKexecDepRejected`,
`pin_not_a_load`→`pinNotALoad`, `kflow_main_spin`→`kflowMainSpin`,
`kflow_acquire_call`→`kflowAcquireCall`.  Added: `pinFirstNotFence` (deviation 1).

**Not ported:** none.

**Statements checked** (by hand against Rocq): every definition and all thirteen examples (two
restated at this image's pcs, deviation 1).
-/
import Weak.WeakDeps
import Weak.KernelSitesDef

namespace Weak

open MachCSL

/-! ## 1. The image, as ROLES -/

/-- The 4-byte fetch window at `pc` as the `BitVec 32` the announce carries.  For a compressed
instruction the high half is the NEXT instruction's bytes -- harmless, because `depsOfBits`
dispatches on bits `[1:0]` and every compressed arm reads only bits `[15:0]`. -/
def kword (pc : Int) : BitVec 32 := BitVec.ofNat 32 (kw pc)

def krole (pc : Int) : OpRoles := depsOfBits (kword pc)

def roleIsLoad (r : OpRoles) : Bool :=
  match r with
  | .ORload _ _ => true
  | _ => false

/-- A STORE for pin purposes is anything that publishes a value to memory: the plain stores and
the AMOs.  (An `ORload` from opcode 47 is `lr`, which publishes nothing; the image has none.) -/
def roleIsStore (r : OpRoles) : Bool :=
  match r with
  | .ORstore _ _ | .ORamo _ _ _ => true
  | _ => false

def roleIsBranch (r : OpRoles) : Bool :=
  match r with
  | .ORbranch _ _ => true
  | _ => false

/-! ## 2. Taint: which registers carry the loaded value

A taint set is a list of register names.  Duplicates are allowed -- membership is all anyone
asks -- so the update needs no normalisation. -/

def taintMem (r : Nat) : List Nat → Bool
  | [] => false
  | x :: q => Nat.beq x r || taintMem r q

def taintDel (r : Nat) : List Nat → List Nat
  | [] => []
  | x :: q => if Nat.beq x r then taintDel r q else x :: taintDel r q

/-- `DLdRes` is the load-reservation source, never a register, so it never carries the taint of
a NAMED register. -/
def dsrcTainted (t : List Nat) (s : Dsrc) : Bool :=
  match s with
  | .DReg r => taintMem r t
  | .DLdRes => false

def srcsTainted (t : List Nat) (l : List Dsrc) : Bool :=
  l.any (dsrcTainted t)

/-- One destination's effect: a write from a tainted source TAINTS it, any other write KILLS
it.  This is PARM's `step_assign` read as a two-point lattice -- exactly `depsRd`'s
(destination, sources) pair, which is why the load's own address provenance (DEC-4: `rd`
inherits `DLdRes :: depsAddr`) propagates for free.  DUPLICATE-FREE: the DFS's visited set
compares taints syntactically, so the update must be idempotent or a loop never closes. -/
def taintUpd1 (t : List Nat) (d : Option (Nat × List Dsrc)) : List Nat :=
  match d with
  | none => t
  | some (rd, srcs) =>
      if srcsTainted t srcs
      then (if taintMem rd t then t else rd :: t)
      else taintDel rd t

def taintStep (t : List Nat) (pc : Int) : List Nat :=
  let r := krole pc
  taintUpd1 (taintUpd1 t (depsRd r)) (depsRd2 r)

/-! ## 3. CONTROL FLOW, DECODED -/

/-- Sign-extend the low `n` bits of a nonnegative field (deviation 2). -/
def zsext (v n : Nat) : Int :=
  if v.testBit (n - 1) then (v : Int) - ((2 ^ n : Nat) : Int) else (v : Int)

/-! The four PC-relative immediate formats the image uses.  `wfield` is KernelSitesDef's own bit
extractor, so nothing here re-implements the masking. -/

/-- B-type: beq/bne/blt/bge/... -/
def immB (w : Nat) : Int :=
  zsext ((wfield w 31 31 <<< 12) + (wfield w 7 7 <<< 11)
         + (wfield w 30 25 <<< 5) + (wfield w 11 8 <<< 1)) 13

/-- J-type: jal -/
def immJ (w : Nat) : Int :=
  zsext ((wfield w 31 31 <<< 20) + (wfield w 19 12 <<< 12)
         + (wfield w 20 20 <<< 11) + (wfield w 30 21 <<< 1)) 21

/-- CB-type: c.beqz / c.bnez -/
def immCb (w : Nat) : Int :=
  zsext ((wfield w 12 12 <<< 8) + (wfield w 6 5 <<< 6)
         + (wfield w 2 2 <<< 5) + (wfield w 11 10 <<< 3)
         + (wfield w 4 3 <<< 1)) 9

/-- CJ-type: c.j -/
def immCj (w : Nat) : Int :=
  zsext ((wfield w 12 12 <<< 11) + (wfield w 8 8 <<< 10)
         + (wfield w 10 9 <<< 8) + (wfield w 6 6 <<< 7)
         + (wfield w 7 7 <<< 6) + (wfield w 2 2 <<< 5)
         + (wfield w 11 11 <<< 4) + (wfield w 5 3 <<< 1)) 12

/-- WHERE CONTROL GOES after the instruction at a pc.  This does NOT go through `WeakDeps`' roles,
and that is the point: `c.j` is `ORnone` as far as roles go, so a role-driven walk steps straight
past an unconditional jump.  Every transfer of the image is enumerated here.

`FLnone` is "falls through to the next word"; it is the answer for every instruction that is not
a transfer, including `wfi` and `sfence.vma`.  `FLind` -- an indirect jump, an indirect call,
`sret`/`mret`, `ecall`, `ebreak` -- STOPS every walk below, because the checker cannot say where
it lands. -/
inductive Kflow where
  | FLnone
  /-- conditional; `tgt` is the TAKEN arm -/
  | FLbranch (tgt : Int)
  /-- jal x0 / c.j -/
  | FLjump (tgt : Int)
  /-- jal rd, rd ≠ x0 -/
  | FLcall (tgt : Int)
  /-- jalr x0, 0(ra) / c.jr ra -/
  | FLret
  /-- anything else that redirects the pc -/
  | FLind
  deriving DecidableEq, Repr

open Kflow in
def kflowOf (pc : Int) : Kflow :=
  let w := kw pc
  if wIsRvc w then
    let q := w &&& 3
    let f3 := wfield w 15 13
    if Nat.beq q 1 && Nat.beq f3 5 then FLjump (pc + immCj w)
    else if Nat.beq q 1 && (Nat.beq f3 6 || Nat.beq f3 7) then FLbranch (pc + immCb w)
    else if Nat.beq q 2 && Nat.beq f3 4 && Nat.beq (wfield w 6 2) 0 then
      let rd := wfield w 11 7
      if Nat.beq (wfield w 12 12) 0
      then (if Nat.beq rd 1 then FLret                -- c.jr ra = ret
            else if Nat.beq rd 0 then FLnone          -- reserved
            else FLind)                               -- c.jr rd
      else (if Nat.beq rd 0 then FLnone               -- c.ebreak
            else FLind)                               -- c.jalr rd
    else FLnone
  else
    let op := wOp w
    if Nat.beq op 99 then FLbranch (pc + immB w)
    else if Nat.beq op 111 then
      (if Nat.beq (wfield w 11 7) 0 then FLjump (pc + immJ w) else FLcall (pc + immJ w))
    else if Nat.beq op 103 then
      (if Nat.beq (wfield w 11 7) 0 && Nat.beq (wfield w 19 15) 1 && Nat.beq (wfield w 31 20) 0
       then FLret else FLind)
    else if Nat.beq op 115 && Nat.beq (wF3 w) 0 then
      (if Nat.beq (wfield w 31 20) 0x105 || Nat.beq (wfield w 31 25) 0x09
       then FLnone                                    -- wfi, sfence.vma
       else FLind)                                    -- ecall/ebreak/x-ret
    else FLnone

/-! ## 4. ONE STEP OF THE WALK, and the two walks built on it -/

/-- A walk state: where we are, which registers carry the loaded value, and the RETURN STACK of
the calls we descended into (innermost first). -/
structure PState where
  PSt ::
  psPc : Int
  psT : List Nat
  psRs : List Int

def listnEqb : List Nat → List Nat → Bool
  | [], [] => true
  | x :: a', y :: b' => Nat.beq x y && listnEqb a' b'
  | _, _ => false

def listzEqb : List Int → List Int → Bool
  | [], [] => true
  | x :: a', y :: b' => (x == y) && listzEqb a' b'
  | _, _ => false

def pstateEqb (a b : PState) : Bool :=
  (a.psPc == b.psPc) && listnEqb a.psT b.psT && listzEqb a.psRs b.psRs

/-- HOW MANY CALL LEVELS ARE INLINED.  `2` at this revision: one level is not enough (the
interesting pins sit past a helper's own call to `acquire`/`myproc`), three buys almost nothing.
A call past this depth is `PCall`, the audited residue. -/
def pinDepth : Nat := 2

/-- A store through `sp` -- the hart's OWN FRAME.  Skipped only when the witness's `own` bit says
so; see the header. -/
def stackStore (r : OpRoles) : Bool :=
  match r with
  | .ORstore rs1 _ => rs1 == 2
  | _ => false

open PState in
/-- `pstep own s`:
* `some []` -- `s` IS a pin: a fence, a branch on the tainted value, or a store the tainted value
  feeds.  The path ENDS here, successfully.
* `some l` -- the successors (`l` has two elements at a conditional branch: fall-through, then
  taken).
* `none` -- the path FAILS: a store the load's value does not feed (and that the `own` bit does
  not excuse), an indirect transfer, a return with an empty stack, a call past `pinDepth`, or a
  pc outside the text. -/
def pstep (own : Bool) (s : PState) : Option (List PState) :=
  let pc := s.psPc
  let t := s.psT
  let rs := s.psRs
  if decide (pc < textLo) || decide (textHi ≤ pc) then none
  else
    let w := kw pc
    let r := krole pc
    if wIsFence w then some []
    else if roleIsStore r then
      (if srcsTainted t (depsAddr r) || srcsTainted t (depsVsrc r)
       then some []
       else if own && stackStore r
       then some [PSt (pc + wSize w) (taintStep t pc) rs]
       else none)
    else
      match kflowOf pc with
      | .FLbranch tgt =>
          if srcsTainted t (depsCtrl r) then some []
          else some [PSt (pc + wSize w) (taintStep t pc) rs,
                     PSt tgt (taintStep t pc) rs]
      | .FLjump tgt => some [PSt tgt t rs]
      | .FLcall tgt =>
          if Nat.blt rs.length pinDepth
          then some [PSt tgt (taintStep t pc) ((pc + wSize w) :: rs)]
          else none
      | .FLret =>
          (match rs with
           | [] => none
           | a :: rs' => some [PSt a t rs'])
      | .FLind => none
      | .FLnone => some [PSt (pc + wSize w) (taintStep t pc) rs]

/-- THE FALL-THROUGH WALK to the pc a witness names: the FIRST successor at every step, i.e. the
not-taken arm of a conditional branch -- but jumps are followed and direct calls descended into,
so the stretch it crosses is a genuine execution path with a genuine call stack.  `none` if the
fuel runs out, if the path fails, or if a PIN is reached before `stop` (in which case the witness
names the wrong pc). -/
def fwalk : Nat → Bool → Int → PState → Option (List Nat)
  | 0, _, _, _ => none
  | f + 1, own, stop, s =>
      if s.psPc == stop then some s.psT
      else match pstep own s with
        | some (s' :: _) => fwalk f own stop s'
        | _ => none

/-- ALL PATHS.  A depth-first search with a visited set; `true` only when every path out of the
start state ends in a pin.  Revisiting a state is sound to skip: the future is a function of the
state, so a cycle is an infinite path that never stores, on which the claim is vacuous. -/
def pdfs : Nat → Bool → List PState → List PState → Bool
  | 0, _, _, _ => false
  | f + 1, own, seen, work =>
      match work with
      | [] => true
      | s :: w' =>
          if seen.any (pstateEqb s) then pdfs f own seen w'
          else match pstep own s with
            | none => false
            | some ns => pdfs f own (s :: seen) (ns ++ w')

/-- `walkTo` survives for `PPerCpu` alone: that witness re-checks a STRAIGHT-LINE stretch INSIDE
one function, from the `tp` write to the load, and neither call descent nor branch arms have
anything to add. -/
def walkTo : Nat → Bool → Int → Int → List Nat → Option (List Nat)
  | 0, _, _, _, _ => none
  | f + 1, nost, a, stop, t =>
      if a == stop then some t
      else if decide (stop < a) then none
      else if nost && roleIsStore (krole a) then none
      else walkTo f nost (a + wSize (kw a)) stop (taintStep t a)

/-! ## 5. The witnesses -/

/-- The seven witness classes (file-qualified: `pin` is also an `AxSymMem3` name). -/
inductive KernelPinsDef.Pin where
  /-- the base register IS `sp` -/
  | PStack
  /-- the base is `tp`-derived, from `pc0` -/
  | PPerCpu (pc0 : Int)
  /-- a branch at `pc'` tests the loaded value -/
  | PCtrl (pc' : Int) (own : Bool)
  /-- a fence at `pc'` -/
  | PFence (pc' : Int) (own : Bool)
  /-- the store at `pc'` is fed by the load -/
  | PDep (pc' : Int) (own : Bool)
  /-- RESIDUE: a call the walk cannot enter -/
  | PCall (pc' : Int)
  /-- RESIDUE: nothing pins it -/
  | PResidue
  deriving DecidableEq, Repr

open KernelPinsDef

/-- Fuel for the fall-through walk, and for the DFS's total number of state pops. -/
def pinFuel : Nat := 64
def pdfsFuel : Nat := 400

def loadRd (pc : Int) : Option Nat :=
  match depsRd (krole pc) with
  | some (rd, _) => some rd
  | none => none

/-- The start state of both walks: the instruction AFTER the load, the load's destination
register tainted, an empty return stack. -/
def pinT0 (pc : Int) : List Nat :=
  match loadRd pc with
  | some rd => [rd]
  | none => []

def pinStart (pc : Int) : PState :=
  PState.PSt (pc + wSize (kw pc)) (pinT0 pc) []

def allPathsPinned (own : Bool) (pc : Int) : Bool :=
  pdfs pdfsFuel own [] [pinStart pc]

/-- `pinnedb fuel pc w` -- does witness `w` hold at load site `pc`?

Every arm starts from `roleIsLoad`, so a witness at a pc that is not a load is rejected outright
rather than vacuously accepted.  Every CERTIFYING arm ends in `allPathsPinned`, so no witness
certifies on the strength of the fall-through path alone.

* `PStack`: `depsAddr` is the ONE place a base register is read as such.
* `PPerCpu pc0`: the instruction at `pc0` writes a register from `tp` (= x4), and that register's
  taint reaches the load's base register at `pc`.  This is the `mv/slli/auipc/add` per-cpu idiom,
  re-checked rather than pattern-matched: any address chain out of `tp` passes.
* `PCall _ | PResidue`: THE AUDITED RESIDUE.  These certify nothing beyond "this pc is a load";
  the claim about them lives in the generator's census, not here.  They are in the table so that
  `pinsCover` can be exhaustive -- a site cannot escape the census by having no witness. -/
def pinnedb (fuel : Nat) (pc : Int) (w : Pin) : Bool :=
  roleIsLoad (krole pc) &&
  match w with
  | .PStack =>
      (match depsAddr (krole pc) with
       | [.DReg r] => Nat.beq r 2
       | _ => false)
  | .PPerCpu pc0 =>
      decide (pc0 < pc) &&
      (match depsRd (krole pc0) with
       | some (r0, srcs0) =>
           srcsTainted [4] srcs0 &&
           (match walkTo fuel false (pc0 + wSize (kw pc0)) pc [r0] with
            | some t => srcsTainted t (depsAddr (krole pc))
            | none => false)
       | none => false)
  | .PCtrl pc' own =>
      (match fwalk fuel own pc' (pinStart pc) with
       | some t =>
           roleIsBranch (krole pc')
           && srcsTainted t (depsCtrl (krole pc'))
           && allPathsPinned own pc
       | none => false)
  | .PFence pc' own =>
      (match fwalk fuel own pc' (pinStart pc) with
       | some _ => wIsFence (kw pc') && allPathsPinned own pc
       | none => false)
  | .PDep pc' own =>
      (match fwalk fuel own pc' (pinStart pc) with
       | some t =>
           roleIsStore (krole pc')
           && (srcsTainted t (depsAddr (krole pc'))
               || srcsTainted t (depsVsrc (krole pc')))
           && allPathsPinned own pc
       | none => false)
  | .PCall _ | .PResidue => true

/-- The classes that CERTIFY something, as a predicate on a witness.  A consumer that wants
"this site is pinned" -- rather than "this site was audited" -- filters the table by this. -/
def pinCertifies (w : Pin) : Bool :=
  match w with
  | .PStack | .PPerCpu _ | .PCtrl _ _ | .PFence _ _ | .PDep _ _ => true
  | .PCall _ | .PResidue => false

/-- ... and the ones that lean on the sp-frame assumption.  Counting these is how the census
reports the trust delta of slice 2. -/
def pinOwned (w : Pin) : Bool :=
  match w with
  | .PCtrl _ own | .PFence _ own | .PDep _ own => own
  | _ => false

/-! ## 6. Sanity: the checker is not vacuous, and it does not over-accept -/

/-- The racy publication flag of KernelSitesDef is FENCE-pinned; the witness names the very
`fence r,rw` that file enumerates, and the pin holds on EVERY path out of the load, not just the
fall-through one. -/
theorem pinStarted :
    pinnedb pinFuel ((KernelSyms.«main» : Int) + 0x16)
      (.PFence ((KernelSyms.«main» : Int) + 0x18) false) = true := by decide +kernel

/-- `forkret`'s `first.1` read (deviation 1): in this image a plain, unfenced `lw` at
`forkret+0x18`, CONTROL-pinned by the `beqz` at `forkret+0x1c` on every path. -/
theorem pinFirst :
    pinnedb pinFuel ((KernelSyms.«forkret» : Int) + 0x18)
      (.PCtrl ((KernelSyms.«forkret» : Int) + 0x1c) false) = true := by decide +kernel

/-- ... and there is no fence to name: the Rocq-shaped `PFence` witness is rejected (added,
deviation 1). -/
theorem pinFirstNotFence :
    pinnedb pinFuel ((KernelSyms.«forkret» : Int) + 0x18)
      (.PFence ((KernelSyms.«forkret» : Int) + 0x1c) false) = false := by decide +kernel

/-- AND THE NEGATIVE DIRECTION, which is what makes the census mean anything: the residue is not
residue for want of trying.  `fileclose+0x2e` reads `f->ref` under `ftable.lock` and the next
store is `ftable`'s own, fed by nothing the load produced -- so NO witness pc between the two is
acceptable.  (Its real justification is the lock, i.e. route-b 4g(A)'s `WProt` port convention,
which is not an image property at all.) -/
theorem pinFilecloseNotDep :
    pinnedb pinFuel ((KernelSyms.«fileclose» : Int) + 0x2e)
      (.PDep ((KernelSyms.«fileclose» : Int) + 0x40) false) = false := by decide +kernel

theorem pinFilecloseNotCtrl :
    pinnedb pinFuel ((KernelSyms.«fileclose» : Int) + 0x2e)
      (.PCtrl ((KernelSyms.«fileclose» : Int) + 0x40) false) = false := by decide +kernel

/-- ... and not even with the sp-frame assumption switched on. -/
theorem pinFilecloseNotDepOwn :
    pinnedb pinFuel ((KernelSyms.«fileclose» : Int) + 0x2e)
      (.PDep ((KernelSyms.«fileclose» : Int) + 0x40) true) = false := by decide +kernel

/-- THE CALL DESCENT IS REAL, AND IT COSTS NO ASSUMPTION.  `fileread+0x42` (Rocq `+0x36`,
deviation 1) loads a field of the open file and the next thing the hart does is CALL `readi`;
the pin is the `beqz` at `readi+0x2` -- INSIDE the callee -- and the witness carries
`own = false`, i.e. no store was skipped to get there. -/
theorem pinFilereadThroughCallee :
    pinnedb pinFuel ((KernelSyms.«fileread» : Int) + 0x42)
      (.PCtrl ((KernelSyms.«readi» : Int) + 0x2) false) = true := by decide +kernel

/-- THE ALL-PATHS CHECK IS REAL TOO.  `kexec+0x11c`'s next store on the FALL-THROUGH path is fed
by the loaded value, but some OTHER path out of the load reaches a store that is not, so `pdfs`
rejects it and the site is in the audited residue.  The three facts below separate the two
checks: the fall-through walk still succeeds, the DFS does not. -/
theorem pinKexecFallthroughStillOk :
    (match fwalk pinFuel false ((KernelSyms.«kexec» : Int) + 0x12c)
            (pinStart ((KernelSyms.«kexec» : Int) + 0x11c)) with
     | some t =>
         roleIsStore (krole ((KernelSyms.«kexec» : Int) + 0x12c))
         && (srcsTainted t (depsAddr (krole ((KernelSyms.«kexec» : Int) + 0x12c)))
             || srcsTainted t (depsVsrc (krole ((KernelSyms.«kexec» : Int) + 0x12c))))
     | none => false) = true := by decide +kernel

theorem pinKexecNotAllPaths :
    allPathsPinned false ((KernelSyms.«kexec» : Int) + 0x11c) = false := by decide +kernel

theorem pinKexecDepRejected :
    pinnedb pinFuel ((KernelSyms.«kexec» : Int) + 0x11c)
      (.PDep ((KernelSyms.«kexec» : Int) + 0x12c) false) = false := by decide +kernel

/-- A witness at a pc that is not a load is rejected, not vacuously accepted: `release+0x1a` is
the release STORE. -/
theorem pinNotALoad :
    pinnedb pinFuel ((KernelSyms.«release» : Int) + 0x1a) .PResidue = false := by decide +kernel

/-! THE IMMEDIATE DECODERS, spot-checked against the disassembly.  These are the one piece of NEW
decoding surface slice 2 adds (see the header); the whole-image cross-check against objdump lives
in tools/gen_weak_pins.py. -/

/-- `main+0x1e`: `beqz a5, main+0x16` -- the `started` spin loop, a BACKWARD conditional branch,
i.e. a negative CB immediate. -/
theorem kflowMainSpin :
    kflowOf ((KernelSyms.«main» : Int) + 0x1e) = .FLbranch ((KernelSyms.«main» : Int) + 0x16) := by
  decide +kernel

/-- `acquire`'s entry: `jal ra, push_off` -- a direct CALL, J-type. -/
theorem kflowAcquireCall :
    kflowOf ((KernelSyms.«acquire» : Int) + 0x0c) = .FLcall (KernelSyms.«push_off» : Int) := by
  decide +kernel

end Weak
