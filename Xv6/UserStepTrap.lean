/-
**The cycle's arms, over the user frames** (lane U3-L; Rocq
`UserStepFull.u_step_post`'s per-arm obligations, discharged by UserTrap's
towers; `UserActiveClass`'s arm routing).

The cycle rule (`UCycleSwp.swp_ucTryStep_U`) asks, per step, the arm
obligation `ucArmOb RF BF Q R st`: a landing `s2` with `Q st s2`, and for the
four TRAPPING arms the handler as a `swp` obligation landing on `s2`.  Here
every arm is discharged at the user frames, with `Q := ustQ` (UserStepLand)
and no rider (`ustR`):

* `ust_swp_exec_trap` -- the execute-trap handler for ANY payload-free
  delegable cause (`exception_handler User exc pc >>= set_next_pc`), from
  UTrap's cause-generic tower (`swp_exception_delegatee_U`,
  `swp_trap_handler_U`).  UTrap's `swp_exec_trap_U` is the
  `make_sync_exception` instance; the ECALL payload is not of that form.
* `ust_trapArm` -- the common core: the frame opened into UTrap's cells
  (`uf_trapCells`), a tower run, the frame closed at `ustTrapS` (a
  `UstTrapped` landing).
* `ust_armOb_interrupt` / `_fetchFail` / `_illegal` / `_trap` -- the four
  trapping arms; `ust_armOb_exec` -- every execute outcome `UstResOk`
  admits (retire, wait entry, trap, illegal).
-/
import Xv6.UserStepClose

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open Sail LeanRV64D LeanRV64D.Functions

set_option linter.unusedSectionVars false

section arms
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- The arm rider: nothing (the closers need no per-arm resource). -/
def ustR : Step → UWSt → IProp GF := fun _ _ => iprop(emp)

set_option maxHeartbeats 4000000 in
/-- **The execute-trap arm, any cause** (Rocq `swp_exec_trap_u` at a general
`sync_exception`): delegated to Supervisor, the cause-generic tower with the
exception's own `tval` payload, then `nextPC := stvec`. -/
theorem ust_swp_exec_trap (cpu : CPU) (exc : sync_exception) (hext : exc.ext = none)
    (pc0 npc ms sc stv sep h md : BitVec 64) (hdir : stvecDirect h) (dqs dqd : DFrac)
    (hdel : md.getLsbD (exceptionType_bits_forwards exc.trap).toNat = true) (Φ : Unit → IProp GF) :
    hwConfig cpu ∗
    Register.cur_privilege ↦ᵣ[cpu] Privilege.User ∗ Register.mstatus ↦ᵣ[cpu] ms ∗
    Register.scause ↦ᵣ[cpu] sc ∗ Register.stval ↦ᵣ[cpu] stv ∗ Register.sepc ↦ᵣ[cpu] sep ∗
    Register.stvec ↦ᵣ[cpu]{dqs} h ∗ Register.medeleg ↦ᵣ[cpu]{dqd} md ∗ Register.nextPC ↦ᵣ[cpu] npc ∗
    ▷ (Register.cur_privilege ↦ᵣ[cpu] Privilege.Supervisor -∗ Register.mstatus ↦ᵣ[cpu] utrapMs 0#1 ms -∗
        Register.scause ↦ᵣ[cpu] utrapScause (.Exception exc.trap) sc -∗
        Register.stval ↦ᵣ[cpu] tval exc.excinfo -∗
        Register.sepc ↦ᵣ[cpu] pc0 -∗ Register.stvec ↦ᵣ[cpu]{dqs} h -∗ Register.medeleg ↦ᵣ[cpu]{dqd} md -∗
        Register.nextPC ↦ᵣ[cpu] h -∗ Φ ())
    ⊢ swp cpu (exception_handler Privilege.User exc pc0 >>= set_next_pc) Φ := by
  obtain ⟨ex, info, ext⟩ := exc
  dsimp only at hext hdel ⊢
  subst hext
  iintro ⟨#Hhw, Hp, Hms, Hsc, Hstv, Hsep, Hstvec, Hmd, Hnpc, HΦ⟩
  iapply swp_bind
  unfold exception_handler
  dsimp only
  iapply swp_bind
  iapply swp_exception_delegatee_U cpu ex md dqd hdel
  iframe Hhw Hmd
  inext
  iintro Hmd
  generalize hT : trap_handler = T
  swp_run 10
  subst hT
  iapply swp_trap_handler_U cpu (.Exception ex) pc0 info ms sc stv sep h hdir dqs
  iframe Hhw Hp Hms Hsc Hstv Hsep Hstvec
  inext
  iintro Hp Hms Hsc Hstv Hsep Hstvec
  iapply swp_set_next_pc_U cpu h npc
  iframe Hnpc
  inext
  iintro Hnpc
  iapply HΦ $$ Hp Hms Hsc Hstv Hsep Hstvec Hmd Hnpc

variable (cpu : CPU) (C : UCfg) (P : UPtd) (t0 : PTree) (mm0 : BMap)

/-- The tower shape every trapping arm has at a user state `sX`: the cells
the frame opens into, the delivered values back. -/
abbrev UstTower (sX : UWSt) (m : SailM Unit) (sc' stv' sep' : BitVec 64) : Prop :=
  ∀ Φ : Unit → IProp GF,
    hwConfig cpu ∗ Register.cur_privilege ↦ᵣ[cpu] Privilege.User ∗
    Register.mstatus ↦ᵣ[cpu] sX.file .mstatus ∗ Register.scause ↦ᵣ[cpu] sX.file .scause ∗
    Register.stval ↦ᵣ[cpu] sX.file .stval ∗ Register.sepc ↦ᵣ[cpu] sX.file .sepc ∗
    Register.stvec ↦ᵣ[cpu]{C.dqc} C.stvec ∗ Register.medeleg ↦ᵣ[cpu]{C.dqc} C.medeleg ∗
    Register.PC ↦ᵣ[cpu] sX.file .PC ∗ Register.nextPC ↦ᵣ[cpu] sX.file .nextPC ∗
    ▷ (Register.cur_privilege ↦ᵣ[cpu] Privilege.Supervisor -∗
        Register.mstatus ↦ᵣ[cpu] utrapMs 0#1 (sX.file .mstatus) -∗
        Register.scause ↦ᵣ[cpu] sc' -∗ Register.stval ↦ᵣ[cpu] stv' -∗ Register.sepc ↦ᵣ[cpu] sep' -∗
        Register.stvec ↦ᵣ[cpu]{C.dqc} C.stvec -∗ Register.medeleg ↦ᵣ[cpu]{C.dqc} C.medeleg -∗
        Register.PC ↦ᵣ[cpu] sX.file .PC -∗ Register.nextPC ↦ᵣ[cpu] C.stvec -∗ Φ ())
    ⊢ swp cpu m Φ

set_option maxRecDepth 10000 in
/-- **The trapping arm, generic** (Rocq's four trap closers' shared half): a
tower run from a user machine `sX` lands on `ustTrapS sX …`, which is a
trapped machine, with the frames. -/
theorem ust_trapArm (sX : UWSt) (hl : UstLand C P t0 mm0 sX) (st : Step) (m : SailM Unit)
    (sc' stv' sep' : BitVec 64) (htow : UstTower (GF := GF) cpu C sX m sc' stv' sep')
    (hb : ∀ s2, ucArmBody (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) (ustR (GF := GF)) st s2 =
      swp cpu m (fun _ => iprop(⌜s2.file .hart_state = .HART_ACTIVE ()⌝ ∗
        uFr (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) s2 ∗ ustR st s2)))
    (hq : ∀ s2, UstTrapped C P t0 mm0 s2 → ustQ C P t0 mm0 st s2) :
    hwConfig (GF := GF) cpu ∗ uFr (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) sX ⊢
      ucArmOb (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) (ustQ C P t0 mm0) ustR st := by
  have ht := ustTrapped_trapS hl sc' stv' sep'
  unfold ucArmOb
  iintro ⟨#Hhw, Hfr⟩
  iexists ustTrapS sX (utrapMs 0#1 (sX.file .mstatus)) sc' stv' sep' C.stvec
  rw [hb]
  isplitr
  · ipureintro; exact hq _ ht
  unfold uFr
  icases Hfr with ⟨HF, HB, Hc, Hr⟩
  icases uf_trapCells cpu C P sX.file hl.cfg $$ HF with ⟨Hp, Hms, Hsc, Hstv, Hsep, Hstvec, Hmd, Hpc, Hnpc, Hcl⟩
  rw [hl.priv]
  iapply htow _
  iframe Hhw Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc
  inext
  iintro Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc
  ihave HF := Hcl $$ %Privilege.Supervisor %(utrapMs 0#1 (sX.file .mstatus)) %sc' %stv' %sep' %C.stvec
    Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc
  rw [ustTrapS_mm, ustTrapS_rv, ustTrapS_file]
  unfold ustR
  isplitr
  · ipureintro; exact ht.act
  iframe

/-- **The interrupt arm** (Rocq `swp_handle_interrupt_u`): the dispatch
picked `(i, Supervisor)`. -/
theorem ust_armOb_interrupt (sX : UWSt) (hl : UstLand C P t0 mm0 sX) (i : InterruptType) :
    hwConfig (GF := GF) cpu ∗ uFr (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) sX ⊢
      ucArmOb (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) (ustQ C P t0 mm0) ustR
        (Step.Step_Pending_Interrupt (i, Privilege.Supervisor)) :=
  ust_trapArm cpu C P t0 mm0 sX hl _ (handle_interrupt i Privilege.Supervisor) (sCause i) 0#64 (sX.file .PC)
    (fun Φ => by
      iintro ⟨#Hhw, Hp, Hms, Hsc, Hstv, Hsep, Hstvec, Hmd, Hpc, Hnpc, HΦ⟩
      iapply swp_handle_interrupt_U cpu i (sX.file .PC) (sX.file .nextPC) (sX.file .mstatus) (sX.file .scause)
        (sX.file .stval) (sX.file .sepc) C.stvec C.tvd C.dqc (DFrac.own 1)
      iframe Hhw Hp Hms Hsc Hstv Hsep Hstvec Hpc Hnpc
      inext
      iintro Hp Hms Hsc Hstv Hsep Hstvec Hpc Hnpc
      iapply HΦ $$ Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc)
    (fun _ => rfl) (fun _ h => h)

/-- **The fetch-fault arm** (Rocq `swp_handle_exception_u` at the fault). -/
theorem ust_armOb_fetchFail (sX : UWSt) (hl : UstLand C P t0 mm0 sX) (e : ExceptionType) (a : BitVec 64)
    (he : userExc e = true) :
    hwConfig (GF := GF) cpu ∗ uFr (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) sX ⊢
      ucArmOb (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) (ustQ C P t0 mm0) ustR
        (Step.Step_Fetch_Failure (virtaddr.Virtaddr a, e)) :=
  ust_trapArm cpu C P t0 mm0 sX hl _ (handle_exception a e) (utrapScause (.Exception e) (sX.file .scause))
    (tval (xtval_exception_value e a)) (sX.file .PC)
    (fun Φ => by
      iintro ⟨#Hhw, Hp, Hms, Hsc, Hstv, Hsep, Hstvec, Hmd, Hpc, Hnpc, HΦ⟩
      iapply swp_handle_exception_U cpu e a (sX.file .PC) (sX.file .nextPC) (sX.file .mstatus)
        (sX.file .scause) (sX.file .stval) (sX.file .sepc) C.stvec C.medeleg C.tvd C.dqc C.dqc (DFrac.own 1)
        (C.del e he)
      iframe Hhw Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc
      inext
      iintro Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc
      iapply HΦ $$ Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc)
    (fun _ => rfl) (fun _ h => h)

/-- **The illegal-instruction arm**. -/
theorem ust_armOb_illegal (sX : UWSt) (hl : UstLand C P t0 mm0 sX) (ib : BitVec 32) :
    hwConfig (GF := GF) cpu ∗ uFr (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) sX ⊢
      ucArmOb (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) (ustQ C P t0 mm0) ustR
        (Step.Step_Execute (.Illegal_Instruction (), ib)) :=
  ust_trapArm cpu C P t0 mm0 sX hl _ (handle_exception (zero_extend (m := 64) ib) (.E_Illegal_Instr ()))
    (utrapScause (.Exception (.E_Illegal_Instr ())) (sX.file .scause))
    (tval (xtval_exception_value (.E_Illegal_Instr ()) (zero_extend (m := 64) ib))) (sX.file .PC)
    (fun Φ => by
      iintro ⟨#Hhw, Hp, Hms, Hsc, Hstv, Hsep, Hstvec, Hmd, Hpc, Hnpc, HΦ⟩
      iapply swp_handle_exception_U cpu (.E_Illegal_Instr ()) (zero_extend (m := 64) ib) (sX.file .PC)
        (sX.file .nextPC) (sX.file .mstatus) (sX.file .scause) (sX.file .stval) (sX.file .sepc) C.stvec
        C.medeleg C.tvd C.dqc C.dqc (DFrac.own 1) (C.del _ rfl)
      iframe Hhw Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc
      inext
      iintro Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc
      iapply HΦ $$ Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc)
    (fun _ => rfl) (fun _ h => h)

/-- **The execute-trap arm** (a `Trap` at User of a payload-free delegable
cause). -/
theorem ust_armOb_trap (sX : UWSt) (hl : UstLand C P t0 mm0 sX) (exc : sync_exception) (pc0 : BitVec 64)
    (ib : BitVec 32) (hext : exc.ext = none) (he : userExc exc.trap = true) :
    hwConfig (GF := GF) cpu ∗ uFr (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) sX ⊢
      ucArmOb (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) (ustQ C P t0 mm0) ustR
        (Step.Step_Execute (.Trap (Privilege.User, exc, pc0), ib)) :=
  ust_trapArm cpu C P t0 mm0 sX hl _ (exception_handler Privilege.User exc pc0 >>= set_next_pc)
    (utrapScause (.Exception exc.trap) (sX.file .scause)) (tval exc.excinfo) pc0
    (fun Φ => by
      iintro ⟨#Hhw, Hp, Hms, Hsc, Hstv, Hsep, Hstvec, Hmd, Hpc, Hnpc, HΦ⟩
      iapply ust_swp_exec_trap cpu exc hext pc0 (sX.file .nextPC) (sX.file .mstatus) (sX.file .scause)
        (sX.file .stval) (sX.file .sepc) C.stvec C.medeleg C.tvd C.dqc C.dqc (C.del _ he)
      iframe Hhw Hp Hms Hsc Hstv Hsep Hstvec Hmd Hnpc
      inext
      iintro Hp Hms Hsc Hstv Hsep Hstvec Hmd Hnpc
      iapply HΦ $$ Hp Hms Hsc Hstv Hsep Hstvec Hmd Hpc Hnpc)
    (fun _ => rfl) (fun _ h => h)

/-- **Every admissible execute outcome's arm** (Rocq `UserActiveClass`'s
per-result routing): retire and wait entry hand the frames over; a trap or
an illegal instruction runs its tower. -/
theorem ust_armOb_exec (res : ExecutionResult) (s' : UWSt) (ib : BitVec 32)
    (h : UstResOk C P t0 mm0 res s') :
    hwConfig (GF := GF) cpu ∗ uFr (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) s' ⊢
      ucArmOb (ufRegF cpu C) (ubFrame curCtx (ubUAddrs P t0)) (ustQ C P t0 mm0) ustR
        (Step.Step_Execute (res, ib)) := by
  cases res with
  | Retire_Success u =>
    cases u
    have hl : UstLand C P t0 mm0 s' := h
    dsimp only [ucArmOb, ucArmBody, ustR]
    iintro ⟨-, Hfr⟩
    iexists s'
    isplitr
    · ipureintro; exact hl
    isplitr
    · ipureintro; exact hl.act
    iframe
  | Enter_Wait wr =>
    dsimp only [ucArmOb, ucArmBody, ustR]
    iintro ⟨-, Hfr⟩
    iexists s'
    isplitr
    · ipureintro; exact h
    iframe
  | Trap x =>
    obtain ⟨p, exc, pc0⟩ := x
    obtain ⟨hl, hp, hext, he⟩ := h
    subst hp
    exact ust_armOb_trap cpu C P t0 mm0 s' hl exc pc0 ib hext he
  | Illegal_Instruction u =>
    cases u
    exact ust_armOb_illegal cpu C P t0 mm0 s' h ib
  | _ => exact False.elim h

end arms

end Xv6
