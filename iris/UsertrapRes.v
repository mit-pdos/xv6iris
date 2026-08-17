(* UsertrapRes.v -- [usertrap_res] DEFINED: the kernel-side bundle
   [SpecUsertrap.v] abstracts.  Definitional layer only -- Spec files and
   below, never a whole-function proof -- so the phases of ProofUsertrap can
   each open it without depending on one another.

   [SpecUsertrap.v]'s boundary is "machine state in, machine state out, plus
   [R pt ksp]".  This file says what R is.  It splits three ways:

     [ut_trap]  -- the TRAP-SIDE pieces: everything [IntrDefs.sie_cap] and
                   [IntrDefs.sconf] need that is not the mstatus cell the
                   boundary hands over raw, the per-cpu bundle, and the four
                   loose ghost fractions the excursion through user mode
                   parks (see below).  This is what Phase A assembles.
     [ut_env]   -- the UNION OF THE FIVE CONES' environments (syscall,
                   devintr, vmfault, printk-general, kexit), which usertrap
                   only ever hands over.  Most of it is [syscall_env]'s union
                   already -- kexit's list IS sys_exit's -- so the real
                   content is what syscall does not need: devintr's device
                   caps, vmfault's kalloc side, and printk-general's pr lock.
     [ut_res]   -- the two above, existentially closed over every ghost name
                   and over the process record, keyed on (pt, ksp) because
                   those are the only two the TRAMPOLINE knows.

   WHY THE GHOST FRACTIONS ARE LOOSE HERE.  [sie_gname] is split 1/2 (in
   [sconf]) + 1/4 (in [intr_res]) + 1/8 ([sie_arm]) + 1/8 ([intr_count]).
   At usertrap's entry there IS no [intr_res] -- stvec points at the
   trampoline, no kernel handler is installed -- so that quarter is dangling,
   which is prepare_return's safety argument arriving intact.  And [sconf]
   cannot survive the [sret] either (it ties the SIE half to the LIVE
   mstatus, and the sret sets SIE := SPIE = 1 in user mode), so its half is
   loose too, at 'b"0" -- the value it had when prepare_return left and the
   value the trap restores by clearing SIE.  Same for the sret mirror: R
   holds BOTH halves, which is what makes the pair UPDATABLE across the sret
   that changes SPP/SPIE.  So the whole excursion moves no ghost, and the
   only fraction still bundled is [intr_count]'s, inside [cpu_own].

   THE STACK BUDGET is inside R rather than on the boundary for the same
   reason [av] is: the trampoline has no business knowing usertrap's frame
   depth.  [ut_res] carries [K_usertrap <= av] as a pure conjunct. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile HartTp WpGpr.
Require Import SmodeCore.
Require Import KernelDataInv MstatusBits.
Require Import MinstretInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.   (* csp_rs1 -- sie_cap's stack key *)
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import KptShare.   (* [tlb_res_pt] -- the parked residue drops it *)
Require Import ProcPtOwn.  (* [proc_pt] / [ud_norm] -- the bare residue drops those *)
Require Import SchedCtx.
Require Import KallocInv KvmSpec.
Require Import IcacheEscrow IrefSlots InodeRegion.
Require Import WaitInv.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import UserPtTree.
Require Import SpecProcinit.
Require Import SpecFileclose.
Require Import SpecDevintr.
Require Import SpecPrintk.
Require Import SpecSyscall.
Require Import SpecKernelvec.   (* the two kernelvec trap-vector facts *)
Require Import SpecUsertrap.   (* USERTRAP_RES -- the fit is checked at the foot *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.

(* usertrap's own 32-byte frame is 4 slots; below it the deepest callee is
   syscall (whose own deepest table entry is sys_exit over kexit).  Written
   as an expression for the reason SpecSyscall.v writes K_syscall as one: a
   change to kexit's budget must not silently leave this one behind.  The
   others are all smaller and subsumed -- devintr 40, vmfault 38,
   printk-general 38, yield 20, killed/setkilled 14, prepare_return 12,
   myproc 10, and kexit itself 74 (which syscall's 82 already covers).

   AND [kv_frame_slots] ON TOP OF THAT, WHICH IS NOT AN OVERESTIMATE.  The
   [csrsi sstatus,2] at +0x9e RE-ENABLES INTERRUPTS before the [jal syscall],
   and an enabled arm's carve is [trap_res true + avail]
   ([IntrDefs.sie_cap]) -- so the leaf that performs the flip
   ([WpSconfCsr.wp_csrsi_sstatus_x0_enable_s_sconf]) is stated at pre index
   [trap_res true + n] and post index [n].  In other words the 78 slots
   kernelvec would need for a NESTED trap have to come out of usertrap's own
   budget at that instruction, exactly as scheduler()'s single real
   [intr_on] pays for them out of its.  Only the syscall arm needs it, but a
   function has one budget.  The other four arms never re-enable, so they
   fit in [4 + K_syscall] and nothing there notices. *)
Notation K_usertrap := ((4 + kv_frame_slots + K_syscall)%nat) (only parsing).
Section UsertrapRes.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* ------------------------------------------------------------------- *)
  (* THE TRAP SIDE.  What Phase A turns into [sie_cap_gpr] + [cpu_own] +   *)
  (* [trap_csrs] once the boundary's raw cells are added to it.            *)
  (* ------------------------------------------------------------------- *)
  (* [ksp] is the kernel stack TOP, which is what uservec loaded into sp
     out of the trapframe's kernel_sp word -- so [stack_own ksp av] is
     exactly [sie_cap]'s carve at [m !!! sp = ksp], which is the boundary's
     own premise.  [trap_res false = 0], so no reserve is owed: the disabled
     index is not holding an enabled arm's window. *)
  Definition ut_stack (ksp : mword 64) (av : nat) : iProp Σ :=
    stack_own (KTR := kt) ksp (trap_res false + av)%nat.

  (* [sconf] MINUS the mstatus cell AND the privilege cell is
     [IntrDefs.sconf_priv_closer], which lives beside [sconf_at] because it
     is [sconf_at]'s idiom with one more cell -- and it is a CLOSER rather
     than a restatement of the bundle's internals so that re-spelling
     hw_config / minstret / the mie and menvcfg pin blocks is not a second
     place for five pure side conditions to drift. *)

  (* THE FOUR LOOSE GHOSTS -- see the header.  Values are PINNED, not
     existential: [usertrap_entry_ms] pins SPP = 0 / SPIE = 1 / SIE = 0, and
     an existential here would only have to be identified with those pins
     again at the first agreement. *)
  Definition ut_ghosts : iProp Σ :=
    (ghost_var sie_gname (1/2) ('b"0" : mword 1) ∗
     ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
     sret_bits ('b"0" : mword 1) ('b"1" : mword 1) ∗
     sret_bits ('b"0" : mword 1) ('b"1" : mword 1))%I.

  Definition ut_trap (pj : mword 64) (ksp : mword 64) (av : nat)
      (lks : gset string) : iProp Σ :=
    (ut_stack ksp av ∗
     (* the translation slot, in its KPT arm: THE KERNEL PAGE TABLE, on the
        SHARED tier ([KptShare.tlb_res_pt] inside), which is the whole point
        of SpecUsertrap.v's restatement *)
     strans_inv ∗
     sie_arm kt false pj ∗
     kpt_on cpu_id ∗
     (* NOT [IntrDefs.sconf_priv_closer]: [mie]/[mideleg]/[menvcfg] are
        [user_cfg]'s cells too (uservec/userret/user-mode hold them the
        whole time usertrap ISN'T running), so [ut_trap] cannot claim them
        permanently the way the closer would -- [wp_usertrap_body] borrows
        them as loose cells for the call instead (see SpecUsertrap.v) and
        [ut_trap_open]/the exit epilogue assemble/release [sconf] from
        those, not from a parked closer. *)
     ut_ghosts ∗
     cpu_own 0%nat false pj false lks ∗
     (* the running claim.  It is what [SpecYield] / [SpecKexit] want as
        [cpu_claim_ext false pj], and the trap is where it comes from. *)
     cpu_claim pj)%I.

  (* ------------------------------------------------------------------- *)
  (* THE PARKED FORM: [ut_trap] WITHOUT THE TRANSLATION SLOT.             *)
  (*                                                                      *)
  (* [ut_trap] owns [satp] -- its [strans_inv] is pinned to the KPT arm by *)
  (* the [kpt_on cpu_id] beside it, and that arm IS                        *)
  (* [tlb_res_pt], whose [satp ↦ᵣ] is full.  That is correct for the state *)
  (* usertrap RUNS in, and WRONG for anything parked across user           *)
  (* execution: while the user runs, [UptTree.utlb_inv_pt] owns [satp] (at *)
  (* the USER root), so a residue also holding [strans_inv] makes the pair *)
  (* contradictory -- [strans_inv ∗ kpt_on cpu_id ∗                        *)
  (* utlb_inv_pt _ _ _ ⊢ False] is provable, which silently turns any      *)
  (* consumer holding both into a vacuous lemma.                          *)
  (*                                                                      *)
  (* So the parked form drops [strans_inv] and keeps the one-shot's own    *)
  (* [strans_kpt] auth loose beside the client's persistent [kpt_on]: the  *)
  (* auth is at fraction 1, so holding it IS "nobody is using the          *)
  (* translation slot right now" (a second copy is unsatisfiable).         *)
  (* uservec's exit switch produces the [tlb_res_pt] that                  *)
  (* completes it ([ut_trap_tlb_close]); userret's entry switch takes it   *)
  (* back out ([ut_trap_tlb_open]).                                       *)
  Definition ut_trap_parked (pj : mword 64) (ksp : mword 64) (av : nat)
      (lks : gset string) : iProp Σ :=
    (ut_stack ksp av ∗
     sie_arm kt false pj ∗
     strans_kpt ∗ kpt_on cpu_id ∗
     ut_ghosts ∗
     cpu_own 0%nat false pj false lks ∗
     cpu_claim pj)%I.

  Lemma ut_trap_tlb_close (pj ksp : mword 64) (av : nat)
      (lks : gset string) (kroot : mword 44) :
    ut_trap_parked pj ksp av lks -∗ tlb_res_pt kroot -∗ ut_trap pj ksp av lks.
  Proof.
    iIntros "(Hstk & Harm & Hb1 & #Hb2 & Hgh & Hcpu & Hclm) Hkres".
    rewrite /ut_trap. iFrame "Hstk Harm Hb2 Hgh Hcpu Hclm".
    iApply (strans_inv_intro kroot with "Hb1 Hkres").
  Qed.

  Lemma ut_trap_tlb_open (pj ksp : mword 64) (av : nat)
      (lks : gset string) :
    ut_trap pj ksp av lks -∗
    ∃ kroot : mword 44, tlb_res_pt kroot ∗ ut_trap_parked pj ksp av lks.
  Proof.
    iIntros "(Hstk & Hstr & Harm & #Hbit & Hgh & Hcpu & Hclm)".
    (* the receipt BESIDE the slot pins the slot's arm: at Bare the shot's
       lower bound and the pending half conflict, so only KPT survives. *)
    iDestruct "Hstr" as "[(Hb0 & _ & _) | (Hb1 & Hkpt)]".
    { iDestruct (kpt_on_pending_False with "Hbit Hb0") as %[]. }
    iDestruct "Hkpt" as (kroot) "Hkres".
    iExists kroot. iFrame "Hkres". rewrite /ut_trap_parked.
    iFrame "Hstk Harm Hb1 Hbit Hgh Hcpu Hclm".
  Qed.

  (* NOT IN THE BUNDLE: [intr_handler_spec kernelvec], the contract the
     [csrw stvec] at +0x1e installs.  It is DERIVABLE from what [ut_env]
     already carries -- [SpecKernelvec]'s [kernelvec_handler_spec] takes
     hw_config, minstret_inv, kernel_text and [devintr_caps], and the first two
     are persistent conjuncts of the [sconf] this bundle assembles.  So asking
     for it here would be asking R's builder for something it can compute, and
     the cost of not asking is one more functor argument on ProofUsertrap
     (KERNELVEC, a PROVEN module).  Named here because the derivation lives one
     layer up: this file may not mention a module parameter. *)

  (* ---- THE ENTRY ASSEMBLY (Phase A) --------------------------------- *)
  (* The boundary's raw machine state plus [ut_trap] IS the kernel cone's
     entry state.  No instruction is involved, which is the point: if this
     lemma holds then SpecUsertrap's restated boundary is the right one, and
     everything after +0x1e is ordinary kernel-cone work.

     WHAT COMES OUT LOOSE is exactly what usertrap still has to fold.  The
     dangling SIE quarter, the KPT receipt and the sret mirror are three of
     [trap_csrs]'s six members; the [csrw stvec, kernelvec] at +0x1e turns
     them -- plus the boundary's stvec cell and the handler contract -- into
     the bundle.  The three trap CSR CELLS stay on the boundary rather than
     coming out here because usertrap READS them (scause three times, sepc
     once, stval twice) before ever folding them away. *)
  Lemma ut_trap_open (pj ksp : mword 64) (av : nat)
      (m : regfile) (ms : mword 64) (mie_v mdv0 menvcfg0 : mword 64)
      (lks : gset string) :
    sconf_ms_facts ms ->
    eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ->
    eq_vec (_get_Mstatus_SPP ms) ('b"1") = false ->
    _get_Mstatus_SPIE ms = ('b"1" : mword 1) ->
    m !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx Rtp = cid_word ->
    (* the three [sconf] pins, borrowed loose (see [ut_trap]'s comment) *)
    mie_v = MIE_S ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    gpr_file m -∗
    ut_trap pj ksp av lks -∗
      sie_cap_gpr kt m av false pj ∗
      cpu_own 0%nat false pj false lks ∗
      cpu_claim pj ∗
      ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
      kpt_on cpu_id ∗
      sret_bits ('b"0" : mword 1) ('b"1" : mword 1).
  Proof.
    intros Hmsf Hsie Hspp Hspie Hsp Htp Hmiev Hmask Hmenvv.
    subst mie_v.
    apply mword1_zero_of_ne_one in Hsie.
    apply mword1_zero_of_ne_one in Hspp.
    iIntros "#Hhw #Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Hgpr Ht".
    (* THE RECEIPT IS PERSISTENT, and taking it intuitionistically is what
       lets this assembly supply the capability's tier witness for real
       ([strans_ktier_wit_intro] below) instead of re-conjuring a KT0 one:
       [ut_trap] carries [kpt_on cpu_id] at every tier, so the bundle it
       builds attests the access right whatever the hart's regime is. *)
    iDestruct "Ht" as "(Hstk & Hstr & Harm & #Hkpt & Hgh & Hcpu & Hclm)".
    iDestruct "Hgh" as "(Hhalf & Hq & Htie & Htrav)".
    (* A named [iFrame] here still makes the tactic hunt these five atoms
       through the WHOLE goal, including the [sie_cap_gpr] conjunct that is
       about to be unfolded below -- and [sie_cap_gpr] is transparent and
       wraps [gpr_file], a [big_sepM] over the entire register file, so every
       failed match against it pays a real unfold.  [iSplitR] pays nothing
       extra: the goal is already a literal top-level [sie_cap_gpr ∗ (...)],
       so peeling it off costs one syntactic step, and the five atoms then
       get framed into a goal that no longer mentions [sie_cap_gpr] at all.
       The first branch is left open (empty in the bracket) so the rest of
       this proof, which is entirely about the [sie_cap_gpr] side, is
       unchanged. *)
    iSplitR "Hcpu Hclm Hq Htrav"; [ | iFrame "Hcpu Hclm Hq Hkpt Htrav" ].
    rewrite /sie_cap_gpr. iFrame "Hhs".
    iSplitL "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
    { rewrite /sconf. iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hhalf Htie".
      { iExists ms. rewrite /sret_tie Hsie Hspp Hspie.
        iFrame "Hms Hhalf Htie". iPureIntro. exact Hmsf. }
      iSplitL "Hmie Hmdl".
      { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmask. }
      iExists menvcfg0. iFrame "Hmenv". subst menvcfg0.
      iPureIntro. split; [| split; [| split; [| split]]]; vm_compute; reflexivity. }
    rewrite /sie_cap /ut_stack Hsp.
    iFrame "Hstk Hstr Harm".
    iSplitR; [ iApply (strans_ktier_wit_intro with "Hkpt") |].
    rewrite (tp_pin_id m Htp). iExact "Hgpr".
  Qed.

  (* ---- THE EXIT FACTS ARE DERIVABLE, NOT ARRANGED (Phase D) ---------- *)
  (* [SpecUsertrap.usertrap_ret_ms] is the boundary's promise that the mstatus
     usertrap returns is sret-ready.  usertrap does not have to ESTABLISH it:
     every conjunct is already a consequence of the bundle prepare_return
     hands back, read off two ghost agreements and [sconf_ms_facts] --

       SIE = 0     : the loose quarter (prepare_return's DANGLING one, the
                     fraction that forbids re-enabling interrupts before the
                     sret) agrees with [sconf]'s half, which is tied to the
                     LIVE mstatus;
       SPP, SPIE   : the travelling sret mirror agrees with [sconf]'s tie, so
                     SPP = User and SPIE = 1, and [sret_ms2_SPP] turns the
                     first into [sret_newpriv ms = User];
       the rest    : MPRV / SXL / MXR / TSR / TVM verbatim from
                     [sconf_ms_facts], and FS / VS from its Off pins.

     So the two ghost fractions the excursion parks are not bookkeeping -- they
     are what MAKES the return legal, and this lemma is where that is cashed. *)
  Lemma ut_exit_ms_ok (ms : mword 64) :
    sconf_msown ms -∗
    sret_bits ('b"0" : mword 1) ('b"1" : mword 1) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    ⌜ usertrap_ret_ms ms ⌝.
  Proof.
    iIntros "(Hms & Hhalf & Htie & %Hmsf) Htrav Hq".
    rewrite /sret_tie.
    iDestruct (sret_bits_agree _ _ _ _ with "Htie Htrav") as %[Hspp Hspie].
    iDestruct (ghost_var_agree with "Hhalf Hq") as %Hsie.
    destruct Hmsf as (Hmprv & Hsxl & Hmxr & Htsr & _ & Hfs & Hvs & _ & _ & Htvm).
    iPureIntro. rewrite /usertrap_ret_ms. split_and!.
    - rewrite Hsie. vm_compute. reflexivity.
    - exact Hmprv.
    - exact Hsxl.
    - exact Htvm.
    - exact Hmxr.
    - exact Htsr.
    - rewrite Hfs. vm_compute. reflexivity.
    - rewrite Hvs. vm_compute. reflexivity.
    - unfold sret_newpriv. rewrite sret_ms2_SPP Hspp. vm_compute. reflexivity.
  Qed.

  (* ---- THE FOLD AT +0x1e, WHICH IS WHAT THE C COMMENT SAYS -----------

         // send interrupts and exceptions to kerneltrap(),
         // since we're now in the kernel.
         w_stvec((uint64)kernelvec);

     [ut_trap_open] hands out three of [trap_csrs]' six members loose -- the
     DANGLING SIE quarter, the KPT receipt and the sret mirror -- because at
     entry no kernel handler is installed, and an [intr_res] at TRAMPOLINE
     would be FALSE: uservec's contract is not [intr_handler_spec], since it
     never returns to the interrupted pc.  This is the step that makes it true
     again, and it is the exact inverse of what prepare_return's [csrci] does
     on the way out.

     THE ORDER IS FORCED, which is the theorem hiding in the C comment:
     nothing before this instruction may set SIE = 1, because
     [sie_ghost_flip] needs all three fractions and the quarter is not inside
     an [intr_res] to be found in.  xv6 writes stvec first and enables
     interrupts (the [csrsi] at +0xa2) only on the syscall arm, long after. *)
  Lemma ut_trap_csrs_fold (ep sc st : mword 64) :
    sepc ↦ᵣ ep -∗
    scause ↦ᵣ sc -∗
    stval ↦ᵣ st -∗
    sret_bits ('b"0" : mword 1) ('b"1" : mword 1) -∗
    stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    kpt_on cpu_id -∗
    intr_handler_spec kt (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    trap_csrs kt.
  Proof.
    iIntros "Hep Hsc Hst Hsret Hstv Hq Hkpt #Hih".
    iApply (trap_csrs_of_raw with "[Hep Hsc Hst Hsret] [Hq Hstv] Hkpt").
    - rewrite /trap_csrs_raw.
      iSplitL "Hep"; [iExists ep; iExact "Hep" |].
      iSplitL "Hsc"; [iExists sc; iExact "Hsc" |].
      iSplitL "Hst"; [iExists st; iExact "Hst" |].
      iExists ('b"0" : mword 1), ('b"1" : mword 1). iExact "Hsret".
    - iApply (intr_res_intro (mword_of_int KernelSyms.kernelvec : mword 64)
                ('b"0" : mword 1) kernelvec_tv_direct kernelvec_stvec_base
                with "Hq Hstv [Hih]").
      iApply bi.later_intro. iExact "Hih".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE FIVE CONES' ENVIRONMENTS.  usertrap hands these over and, except  *)
  (* on the kexit paths, takes them back; nothing here is read by usertrap *)
  (* itself.                                                              *)
  (* ------------------------------------------------------------------- *)
  (* WHAT THE NAMES ARE SHARED BY -- this is the content of the union, and
     the reason it is one bundle rather than five:
       [un_u] (uart) is devintr's uartintr, printk-general's console, and
             kexit's [dev_inv];
       [un_v] (disk) and [un_k] (the virtio lock) are devintr's disk interrupt
             and kexit's begin_op/end_op cone;
       [un_s]  is the proc array, shared by killed / setkilled / yield /
             devintr's tick_keeper / kexit;
       [un_kl]/[un_ka] are kexit's kalloc pieces AND vmfault's [kalloc_env];
       [un_f]  is the open-file table, shared by syscall and kexit.
     Getting those identifications right is what makes the bundle coherent;
     five independently-named piles would be satisfiable by nobody.

     AND THEY ARE A RECORD, not a parameter list.  [SpecKexit.v] spells its
     thirty-odd names out because it is ONE contract; usertrap's walk is six
     block lemmas that each hand the whole pile to the next, and a
     thirty-argument list restated a dozen times is where a wrong
     identification hides.  [fclose_names] is the precedent -- and the
     equation SpecKexit takes as a premise ([fn = MkFCloseNames ...]) becomes
     the DEFINITION [un_fn] below, so the coherence cannot be got wrong
     rather than merely being checked. *)
  Record ut_names : Type := MkUtNames {
    un_ft : gname;                    (* ftable.lock                        *)
    un_f  : gname;                    (* the open-file table                *)
    un_w  : gname;                    (* wait_lock                          *)
    un_s  : list gname;               (* the proc array's per-slot locks     *)
    un_j  : nat;                      (* the running process's slot          *)
    un_l  : gname;
    un_u  : uart_names;
    un_v  : disk_names;
    un_k  : gname;                    (* virtio_disk.lock                   *)
    un_pd : mword 64;
    un_pav : mword 64;
    un_pu : mword 64;
    un_tk : gname;                    (* the ticks lock                     *)
    un_pr : gname;                    (* the pr lock (printk-general)        *)
    un_bn : bio_names;
    un_lg : log_names;
    un_fs : fs_names;
    un_cov : gset Z;
    un_logstart : Z;
    un_dev : mword 32;
    un_ip  : mword 64;                (* the initproc pointer's value        *)
    un_dqi : dfrac;
    un_kl  : gname;                   (* kmem.lock                          *)
    un_ka  : gname * gname;
    un_i   : gname;                   (* the inode region's ghost            *)
    un_cn  : ic_names;
    un_tl  : gname;                   (* itable.lock                        *)
    un_bmapstart : Z;
    un_inodestart : Z;
    un_nib : nat;
    un_size : Z;
    un_dqb : dfrac;
    un_dqs : dfrac;
    un_us  : gset Z;
    un_ks  : mword 64;                (* the kernel stack's BASE             *)
    un_pid : mword 32;
  }.

  (* the running process's [struct proc] address, and the fileclose
     environment index -- DERIVED, see the note above. *)
  Definition un_pj (N : ut_names) : mword 64 := proc_addr (un_j N).

  Definition un_fn (N : ut_names) : fclose_names :=
    MkFCloseNames (un_s N) (un_j N) (un_l N) (un_kl N) (un_ka N)
      (un_u N) (un_v N) (un_k N) (un_pd N) (un_pav N) (un_pu N)
      (un_bn N) (un_lg N) (un_fs N) (un_cov N) (un_logstart N) (un_dev N)
      (un_pid N) (DfracOwn (1/4))
      (un_i N) (un_cn N) (un_tl N) (un_bmapstart N) (un_inodestart N)
      (un_nib N) (un_size N) (un_dqb N) (un_dqs N).

  (* THE ONE FIELD A SYSCALL CALL CAN MOVE.  [SpecSyscall.wp_syscall_sconf_body]
     hands [fileclose_bm (un_fn N) (un_us N)] to the dispatch table (see its
     header) and gets back [fileclose_bm (un_fn N) us'] for a possibly SMALLER
     [us'] -- [SYSCLOSE]'s own postcondition re-indexes it the same way.  No
     other field of [ut_names] moves across that call, so this is the only
     update function this record needs. *)
  Definition upd_us (N : ut_names) (us : gset Z) : ut_names :=
    MkUtNames (un_ft N) (un_f N) (un_w N) (un_s N) (un_j N) (un_l N)
      (un_u N) (un_v N) (un_k N) (un_pd N) (un_pav N) (un_pu N)
      (un_tk N) (un_pr N) (un_bn N) (un_lg N) (un_fs N) (un_cov N)
      (un_logstart N) (un_dev N) (un_ip N) (un_dqi N) (un_kl N) (un_ka N)
      (un_i N) (un_cn N) (un_tl N) (un_bmapstart N) (un_inodestart N)
      (un_nib N) (un_size N) (un_dqb N) (un_dqs N) us (un_ks N) (un_pid N).

  Lemma un_fn_upd_us (N : ut_names) (us : gset Z) : un_fn (upd_us N us) = un_fn N.
  Proof. reflexivity. Qed.

  Lemma upd_us_id (N : ut_names) : upd_us N (un_us N) = N.
  Proof. destruct N; reflexivity. Qed.

  (* the pure side conditions every callee below usertrap shares.  Bundled
     for the same reason the names are: each block lemma needs all four and
     none of them is about the block. *)
  Definition ut_wf (N : ut_names) : Prop :=
    (un_j N < NPROC)%nat /\
    un_s N !! un_j N = Some (un_l N) /\
    length (un_s N) = NPROC /\
    log_geom_ok (un_cov N) (un_logstart N).

  (* ------------------------------------------------------------------- *)
  (* THE ONE MEMBER THAT IS PER-HART, IN ITS HART-GENERIC FORM.            *)
  (* ------------------------------------------------------------------- *)
  (* [SpecDevintr.devintr_caps] is genuinely hart-indexed -- [TimerCap.
     timer_cap] holds THIS hart's mcounteren and stimecmp, and
     [SpecClockintr.tick_keeper]'s left disjunct is [tick_hart = false],
     which is a statement about THIS hart.  usertrap cannot carry it in that
     form: everything on the syscall arm from the [csrsi] at +0x9e onwards
     runs at [b = true], where every step may resume on a different hart, and
     the environment is FRAMED across those steps rather than re-delivered by
     a leaf.  [IntrDefs]' three transport lemmas do not help -- they work
     because their propositions are [emp] at [true], which this one is not.

     So the bundle carries the [∀ h] form, exactly as [SpecPanic.
     panic_env] carries panic's credentials for the same reason (a function
     that PARKS does not return on the hart it entered on).  It is
     persistent, hence free to hand to devintr at whatever hart the call
     happens on ([devintr_caps_any_at]), and it is satisfiable: of
     [devintr_caps]' nine members seven are hart-free outright, [timer_cap] is
     available at every hart because the boot chain mints one PER HART out of
     timerinit's own [mcounteren] / [stimecmp] cells ([BootChain], via
     [TimerCap.timer_cap_intro]), and [tick_keeper]'s REAL arm --
     which the boot hart brings up -- is hart-free too.  What it rules out is
     satisfying the tick keeper with the left disjunct, and that is right: a
     process can migrate onto hart 0. *)
  Definition devintr_caps_any (γu : uart_names) (γv : disk_names)
      (γdk γtl : gname) (γs : list gname)
      (pd pav pu : mword 64) : iProp Σ :=
    (□ ∀ h : CPU,
        devintr_caps (kt := kt) (CID := h) γu γv γdk γtl γs pd pav pu)%I.

  Global Instance devintr_caps_any_persistent γu γv γdk γtl γs pd pav pu :
    Persistent (devintr_caps_any γu γv γdk γtl γs pd pav pu).
  Proof. rewrite /devintr_caps_any. apply _. Qed.

  Lemma devintr_caps_any_at (h : CPU) (γu : uart_names) (γv : disk_names)
      (γdk γtl : gname) (γs : list gname) (pd pav pu : mword 64) :
    devintr_caps_any γu γv γdk γtl γs pd pav pu -∗
    devintr_caps (kt := kt) (CID := h) γu γv γdk γtl γs pd pav pu.
  Proof.
    iIntros "#H". rewrite /devintr_caps_any.
    iPoseProof (bi.forall_elim h with "H") as "H2". iExact "H2".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE BUNDLE SPLITS BY PERSISTENCE, and that is not cosmetic.            *)
  (* ------------------------------------------------------------------- *)
  (* Eighteen of the twenty-five members are PERSISTENT -- every lock, every
     invariant, every agreement -- and the walk leans on it in a way a flat
     [∗] would hide: [killed] is called TWICE and takes [procs_inv] both
     times without giving it back, [prepare_return] takes [is_kstack] and
     does not return it, [vmfault] takes [kalloc_env] and does not return it.
     None of those calls could be made from a bundle that had to be rebuilt
     afterwards.  So the split is the statement of why they are callable, and
     it makes every block lemma's environment handling two lines
     ([iDestruct "Henv" as "[#Hcaps Hown]"] and the mirror) instead of a
     twenty-five-way destructure and rebuild. *)
  Definition ut_caps (N : ut_names) : iProp Σ :=
    (procs_inv (kt := kt) (un_s N) ∗
     kernel_data ∗
     is_kstack (un_pj N) (un_ks N) ∗
     devintr_caps_any (un_u N) (un_v N) (un_k N) (un_tk N) (un_s N)
       (un_pd N) (un_pav N) (un_pu N) ∗
     printk_env (un_pr N) (un_u N) (un_v N) ∗
     is_lock (un_w N) wait_lock_addr "wait_lock"%string wait_res ∗
     is_ftable (un_ft N) (un_f N) ∗
     is_lock (un_kl N) (mword_of_int KernelSyms.kmem) "kmem"%string
       (kmem_res (un_ka N) (mword_of_int (KernelSyms.kmem + 24))) ∗
     is_lock (un_k N) d_lock "virtio_disk"%string
       (disk_res (un_v N) (un_pd N) (un_pav N) (un_pu N)) ∗
     bio_ctx (un_bn N) (fs_view (un_fs N) (un_v N) (un_dev N) (un_cov N)) ∗
     log_ctx (un_lg N) (un_bn N) (un_fs N) (un_cov N) (un_logstart N) (un_dev N) ∗
     fs_crash_seam (un_cov N) (un_logstart N) ∗
     gen_cert ∗
     dev_inv (un_u N) (un_v N) ∗
     disk_geom (un_v N) (un_pd N) (un_pav N) (un_pu N) ∗
     kalloc_avail (un_ka N) None ∗
     fileclose_ic_env (un_fn N))%I.

  Global Instance ut_caps_persistent N : Persistent (ut_caps N).
  Proof. rewrite /ut_caps. apply _. Qed.

  (* vmfault's and the kalloc cone's bundle, assembled out of three
     persistent members of [ut_caps] rather than carried separately. *)
  Lemma ut_caps_kalloc (N : ut_names) :
    ut_caps N -∗ kalloc_env (un_kl N) None.
  Proof.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & #Hkm & _ & _ & _ & _ & _ & _ & _ & #Hav & _)".
    iExists (un_ka N). iFrame "Hkm Hav".
  Qed.

  (* the EXCLUSIVE remainder: what a callee can consume and must give back --
     plus [proc_priv], which every callee gives back at a MOVED record, which
     is why [V] is a parameter of this half and not of [ut_caps]. *)
  Definition ut_own (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) : iProp Σ :=
    (bslots (un_bn N) 3 ∗
     fileclose_bm (un_fn N) (un_us N) ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{un_dqi N} (un_ip N) ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     (* THE PROCESS BLOCK.  The one owner of the user page table and of the
        trapframe page (at the VA tier) -- which is why SpecUsertrap.v's
        boundary hands over neither. *)
     proc_priv (un_f N) (un_pj N) (un_pid N) V ∗
     (* everything the twenty-two syscall table entries consume, abstractly *)
     Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N))%I.

  Definition ut_env (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) : iProp Σ :=
    (ut_caps N ∗ ut_own Rsys N V)%I.

  (* the process block and the syscall environment, borrowed together and
     handed back at a moved record: syscall wants both, prepare_return and
     vmfault only the first. *)
  Lemma ut_own_priv (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ) (N : ut_names)
      (V : pprivate) :
    ut_own Rsys N V -∗
    proc_priv (un_f N) (un_pj N) (un_pid N) V ∗
    Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N) ∗
    (∀ V' : pprivate,
       proc_priv (un_f N) (un_pj N) (un_pid N) V' -∗
       Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N) -∗ ut_own Rsys N V').
  Proof.
    iIntros "(Hb & Hbm & Hip & Hfd & Hir & Hpv & Hsy)".
    iFrame "Hpv Hsy". iIntros (V') "Hpv Hsy".
    rewrite /ut_own. iFrame "Hb Hbm Hip Hfd Hir Hpv Hsy".
  Qed.

  (* [ut_own]'s SEVEN raw conjuncts, straight back into [ut_own (upd_us N
     us)] -- the rebuild [ProofUsertrapSys.v]'s syscall block needs after
     [wp_syscall_sconf]'s crossing hands the six unmoved pieces back plus a
     (possibly smaller) [fileclose_bm] set.  A DEDICATED lemma, proved here
     against a SEVEN-hypothesis context, rather than an inline
     [rewrite /ut_own /N2 ...; iFrame.] at the call site: the same shape
     with the caller's own ~100-hypothesis proof state behind it makes
     [iFrame]'s search degenerate (durable-notes.md's "failing tactic looks
     like a hang" family -- this one is a slow, not a failing, tactic, but
     the fix is the same: keep the reconstruction in a small lemma). *)
  Lemma ut_own_rebuild_us (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ) (N : ut_names)
      (V : pprivate) (us : gset Z) :
    bslots (un_bn N) 3 -∗
    fileclose_bm (un_fn N) us -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{un_dqi N} (un_ip N) -∗
    fd_slots FDSPARE -∗
    iref_slots IREFSPARE -∗
    proc_priv (un_f N) (un_pj N) (un_pid N) V -∗
    Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N) -∗
    ut_own Rsys (upd_us N us) V.
  Proof.
    rewrite /ut_own.
    assert (un_bn (upd_us N us) = un_bn N) as -> by reflexivity.
    assert (un_fn (upd_us N us) = un_fn N) as -> by reflexivity.
    assert (un_dqi (upd_us N us) = un_dqi N) as -> by reflexivity.
    assert (un_ip (upd_us N us) = un_ip N) as -> by reflexivity.
    assert (un_f (upd_us N us) = un_f N) as -> by reflexivity.
    assert (un_pj (upd_us N us) = un_pj N) as -> by reflexivity.
    assert (un_pid (upd_us N us) = un_pid N) as -> by reflexivity.
    iIntros "Hb Hbm Hip Hfd Hir Hpv Hsy".
    iFrame "Hb Hbm Hip Hfd Hir Hpv Hsy".
  Qed.

  (* THE TRAPFRAME BORROW, at the [proc_priv] level.  [proc_fields] /
     [proc_pt_at] / [cwd_ref] / [p_pid] are all functions of [pprivate]
     fields [upd_tf] does not touch (see [upd_tf]'s own header comment), so
     the closer reassembles at whatever NEW content [ws'] the caller hands
     back, no rewriting needed beyond unfolding [upd_tf] itself. *)
  Lemma proc_priv_tf_open (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗
    ∃ ws : list (mword 64), tf_page (ud_tfp (pv_upt V)) ws ∗
      (∀ ws' : list (mword 64), tf_page (ud_tfp (pv_upt V)) ws' -∗
         proc_priv γf pa pid (upd_tf V ws')).
  Proof.
    rewrite /proc_priv /proc_priv_core.
    iIntros "((%Ha & %Hb & Hpid & Hpf & Hpt & Htf & Hcwd) & Hof)".
    iExists (pv_tf V). iFrame "Htf".
    iIntros (ws') "Htf'".
    (* [iFrame]/[cbn] both hang trying to match hypotheses against the
       OPAQUE [upd_tf V ws'] inside the goal (the opening [rewrite]
       does not reach under this closer's [∀ ws'] binder).  Name each
       projection's equality EXPLICITLY instead -- one [reflexivity] per
       field, each instant since it is a single iota step -- and
       [rewrite] them in by NAME, a directed search rather than a blind
       match. *)
    (* [pv_name] is NOT in this list: [proc_fields] takes the WHOLE
       record (not one of its projections) as its argument, so
       [pv_name (upd_tf V ws')] never appears as a direct subterm of the
       goal at all -- [proc_fields]'s own OUTPUT is what needs equating
       (Heq7), not one more of its inputs.  [proc_pt_at]/[cwd_ref]/
       [proc_ofiles] all take a PROJECTION directly, so Heq2/Heq4/Heq3
       reach them; [proc_fields] was the one outlier, and it is what
       [iFrame] was hanging trying to match without a hint. *)
    assert (Heq1 : pv_sz (upd_tf V ws') = pv_sz V) by reflexivity.
    assert (Heq2 : pv_upt (upd_tf V ws') = pv_upt V) by reflexivity.
    assert (Heq3 : pv_ofile (upd_tf V ws') = pv_ofile V) by reflexivity.
    assert (Heq4 : pv_cwd (upd_tf V ws') = pv_cwd V) by reflexivity.
    assert (Heq6 : pv_tf (upd_tf V ws') = ws') by reflexivity.
    assert (Heq7 : proc_fields pa (DfracOwn 1) (upd_tf V ws')
                   = proc_fields pa (DfracOwn 1) V) by reflexivity.
    rewrite /proc_priv /proc_priv_core Heq1 Heq2 Heq3 Heq4 Heq6 Heq7.
    (* Even with the goal now fully reduced to the target shape, [iFrame]
       hangs -- its typeclass-based [Frame] search is apparently
       pathological in this section's large ambient instance context,
       independent of matching. Bypass it: plain [iSplitL]/[iExact] are
       structural (no typeclass search at all). *)
    iSplitL "Hpid Hpf Hpt Htf' Hcwd".
    - iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hpid"; [iExact "Hpid"|].
      iSplitL "Hpf"; [iExact "Hpf"|].
      iSplitL "Hpt"; [iExact "Hpt"|].
      iSplitL "Htf'"; [iExact "Htf'"|].
      iExact "Hcwd".
    - iExact "Hof".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [usertrap_res] itself.                                              *)
  (* ------------------------------------------------------------------- *)
  Definition ut_res (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) : iProp Σ :=
    (∃ (N : ut_names) (V : pprivate) (av : nat),
       (* THE PROCESS RUNNING IS THE ONE WHOSE TABLE THE TRAMPOLINE PARKED.
          This equation is the whole reason R is keyed on [pt]: it is what
          lets userret install [MAKE_SATP(p->pagetable)] and know it is the
          table uservec came out of. *)
       ⌜ pv_upt V = pt ⌝ ∗
       (* ...and the stack the trapframe's kernel_sp word named *)
       ⌜ add_vec (un_ks N) (mword_of_int 4096) = ksp ⌝ ∗
       ⌜ ut_wf N ⌝ ∗
       ⌜ (K_usertrap <= av)%nat ⌝ ∗
       (* the trampoline hands over a hart that holds NO kernel lock, so the
          held set here is the literal [∅] rather than an existential *)
       ut_trap (un_pj N) ksp av ∅ ∗
       ut_env Rsys N V)%I.

  (* [ut_res]'s parked twin -- see [ut_trap_parked]'s header.  This is what
     survives user execution (no [satp]); [ut_res] itself is what usertrap
     consumes. *)
  Definition ut_res_parked (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) : iProp Σ :=
    (∃ (N : ut_names) (V : pprivate) (av : nat),
       ⌜ pv_upt V = pt ⌝ ∗
       ⌜ add_vec (un_ks N) (mword_of_int 4096) = ksp ⌝ ∗
       ⌜ ut_wf N ⌝ ∗
       ⌜ (K_usertrap <= av)%nat ⌝ ∗
       ut_trap_parked (un_pj N) ksp av ∅ ∗
       ut_env Rsys N V)%I.

  (* THE TRANSLATION BORROW, lifted to the residue.  [_close] is uservec's
     move (its exit switch just produced [tlb_res_pt kroot]); [_open] is
     userret's (its entry switch is about to consume it). *)
  Lemma ut_res_tlb_close (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    ut_res_parked Rsys pt ksp -∗ tlb_res_pt kroot -∗ ut_res Rsys pt ksp.
  Proof.
    iIntros "H Hkres".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & Henv)".
    iDestruct (ut_trap_tlb_close with "Htrap Hkres") as "Htrap".
    iExists N, V, av. iFrame "Htrap Henv".
    iPureIntro. split; [| split; [| split]]; assumption.
  Qed.

  Lemma ut_res_tlb_open (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) :
    ut_res Rsys pt ksp -∗
    ∃ kroot : mword 44, tlb_res_pt kroot ∗ ut_res_parked Rsys pt ksp.
  Proof.
    iIntros "H".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & Henv)".
    iDestruct (ut_trap_tlb_open with "Htrap") as (kroot) "[Hkres Htrap]".
    iExists kroot. iFrame "Hkres".
    iExists N, V, av. iFrame "Htrap Henv".
    iPureIntro. split; [| split; [| split]]; assumption.
  Qed.

  (* THE TRAPFRAME BORROW, lifted to [usertrap_res] -- the concrete proof
     of [SpecUsertrap.USERTRAP_RES.usertrap_res_tf_open].  Opens via
     [ut_own_priv] + [proc_priv_tf_open]; the closer moves [V] to
     [upd_tf V ws'] (its [pv_upt] is unchanged, so [pt] is unaffected). *)
  Lemma ut_res_tf_open (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    (forall ws : list (mword 64), length ws = TFWORDS -> tf_kernel_words_ok kroot ksp ws) ->
    ut_res_parked Rsys pt ksp -∗
    ∃ ws : list (mword 64), ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗ tf_page (ud_tfp pt) ws ∗
      (∀ ws' : list (mword 64), tf_page (ud_tfp pt) ws' -∗ ut_res_parked Rsys pt ksp).
  Proof.
    iIntros (Hgap) "H".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & Henv)".
    iDestruct "Henv" as "[Hcaps Hown]".
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    iDestruct (proc_priv_tf_open with "Hpv") as (ws) "[Htf Hclose]".
    rewrite Hupt.
    iDestruct (tf_page_length with "Htf") as %Hlen.
    iExists ws. iSplitR; [iPureIntro; exact (Hgap ws Hlen) |]. iFrame "Htf".
    iIntros (ws') "Htf'".
    iDestruct ("Hclose" $! ws' with "Htf'") as "Hpv'".
    iDestruct ("Hownback" $! (upd_tf V ws') with "Hpv' Hsy") as "Hown'".
    iExists N, (upd_tf V ws'), av.
    iFrame "Htrap Hcaps Hown'".
    iPureIntro. split; [| split; [| split]].
    - rewrite /upd_tf. exact Hupt.
    - exact Hksp.
    - exact Hwf.
    - exact Hav.
  Qed.

  (* =================================================================== *)
  (* THE BARE RESIDUE: the parked form WITHOUT THE USER ADDRESS SPACE.    *)
  (*                                                                      *)
  (* [ut_trap_parked] already dropped the translation SLOT (satp).  That  *)
  (* was one of FOUR overlaps with the user tier, not the only one: the   *)
  (* residue also carries [proc_priv], hence [proc_pt_at], hence          *)
  (* [proc_pt] -- the user page-table tree at [ptree_own 2 (DfracOwn 1)]  *)
  (* AND the user data pages -- and [UserPtTree.user_pt_inv] carries      *)
  (* exactly those same two.  A precondition naming both is therefore     *)
  (* unsatisfiable and the lemma taking it is vacuous.                    *)
  (*                                                                      *)
  (* THE BARE FORM IS WHAT PARKS ACROSS USER EXECUTION.  What it keeps is *)
  (* everything the kernel genuinely still owns while user code runs: the *)
  (* stack, the ghosts, the cpu claim, the whole capability environment,  *)
  (* the [struct proc] cells (INCLUDING [p->pagetable]/[p->trapframe],    *)
  (* which merely name the table) and the trapframe page itself (physical *)
  (* tier, U = 0 leaf -- user mode cannot reach it).                      *)
  (*                                                                      *)
  (* The two borrows compose in one order and back:                       *)
  (*   bare --[_pt_close]--> parked --[_tlb_close]--> ut_res              *)
  (* uservec's exit switch produces both pieces at once (it converts the  *)
  (* user table to a [pt_frame] and writes the kernel root into satp);    *)
  (* userret's entry switch consumes both.  See                           *)
  (* claude-notes/projects/uservec.md.                                    *)
  (* =================================================================== *)
  Definition ut_own_nopt (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) : iProp Σ :=
    (bslots (un_bn N) 3 ∗
     fileclose_bm (un_fn N) (un_us N) ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{un_dqi N} (un_ip N) ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     proc_priv_nopt (un_f N) (un_pj N) (un_pid N) V ∗
     Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N))%I.

  Definition ut_env_nopt (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) : iProp Σ :=
    (ut_caps N ∗ ut_own_nopt Rsys N V)%I.

  Lemma ut_own_pt_close (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) :
    ut_own_nopt Rsys N V -∗ proc_pt (pv_upt V) -∗ ut_own Rsys N V.
  Proof.
    rewrite /ut_own /ut_own_nopt proc_priv_split_pt.
    iIntros "(Hb & Hbm & Hip & Hfd & Hir & Hpv & Hsy) Hpt".
    iFrame "Hb Hbm Hip Hfd Hir Hpv Hpt Hsy".
  Qed.

  Lemma ut_own_pt_open (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) :
    ut_own Rsys N V -∗ ut_own_nopt Rsys N V ∗ proc_pt (pv_upt V).
  Proof.
    rewrite /ut_own /ut_own_nopt proc_priv_split_pt.
    iIntros "(Hb & Hbm & Hip & Hfd & Hir & (Hpv & Hpt) & Hsy)".
    iFrame "Hb Hbm Hip Hfd Hir Hpv Hpt Hsy".
  Qed.

  (* the borrow accessor, at the reduced environment -- [ut_own_priv]'s twin *)
  Lemma ut_own_nopt_priv (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ) (N : ut_names)
      (V : pprivate) :
    ut_own_nopt Rsys N V -∗
    proc_priv_nopt (un_f N) (un_pj N) (un_pid N) V ∗
    Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N) ∗
    (∀ V' : pprivate,
       proc_priv_nopt (un_f N) (un_pj N) (un_pid N) V' -∗
       Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N) -∗ ut_own_nopt Rsys N V').
  Proof.
    iIntros "(Hb & Hbm & Hip & Hfd & Hir & Hpv & Hsy)".
    iFrame "Hpv Hsy". iIntros (V') "Hpv Hsy".
    rewrite /ut_own_nopt. iFrame "Hb Hbm Hip Hfd Hir Hpv Hsy".
  Qed.

  (* the descriptor's derived footprint field is invisible to the reduced
     environment -- see [ProcInv.proc_priv_nopt_upt_irrel] *)
  Lemma ut_own_nopt_upt_irrel (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) (Q : uptd) :
    ud_root (pv_upt V) = ud_root Q ->
    ud_tfp (pv_upt V) = ud_tfp Q ->
    ud_um (pv_upt V) = ud_um Q ->
    ut_own_nopt Rsys N V ⊣⊢ ut_own_nopt Rsys N (upd_upt V Q).
  Proof.
    intros Hr Ht Hu.
    rewrite /ut_own_nopt (proc_priv_nopt_upt_irrel _ _ _ V Q Hr Ht Hu).
    reflexivity.
  Qed.

  Definition ut_res_bare (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) : iProp Σ :=
    (∃ (N : ut_names) (V : pprivate) (av : nat),
       ⌜ pv_upt V = pt ⌝ ∗
       ⌜ add_vec (un_ks N) (mword_of_int 4096) = ksp ⌝ ∗
       ⌜ ut_wf N ⌝ ∗
       ⌜ (K_usertrap <= av)%nat ⌝ ∗
       ut_trap_parked (un_pj N) ksp av ∅ ∗
       ut_env_nopt Rsys N V)%I.

  Lemma ut_res_pt_close (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) :
    ut_res_bare Rsys pt ksp -∗ proc_pt pt -∗ ut_res_parked Rsys pt ksp.
  Proof.
    iIntros "H Hpt".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & (Hcaps & Hown))".
    subst pt.
    iDestruct (ut_own_pt_close with "Hown Hpt") as "Hown".
    iExists N, V, av. rewrite /ut_env. iFrame "Htrap Hcaps Hown".
    iPureIntro. split; [reflexivity | split; [| split]]; assumption.
  Qed.

  Lemma ut_res_pt_open (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) :
    ut_res_parked Rsys pt ksp -∗ proc_pt pt ∗ ut_res_bare Rsys pt ksp.
  Proof.
    iIntros "H".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & (Hcaps & Hown))".
    subst pt.
    iDestruct (ut_own_pt_open with "Hown") as "(Hown & Hpt)".
    iFrame "Hpt".
    iExists N, V, av. rewrite /ut_env_nopt. iFrame "Htrap Hcaps Hown".
    iPureIntro. split; [reflexivity | split; [| split]]; assumption.
  Qed.

  (* RENORMALISING THE DESCRIPTOR.  The bare residue reads [pt] only through
     [ud_root]/[ud_tfp]/[ud_um] (its [proc_pt] is gone, and that was the
     only conjunct whose partner on the user side names [ud_data]), so it
     may be re-keyed on [ud_norm pt] for free.  This is what lets the trap
     loop hand the user tier a descriptor whose [udata_cov] holds by
     construction -- see [ProcPtOwn.user_pt_inv_close]. *)
  Lemma ut_res_bare_norm (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) :
    ut_res_bare Rsys pt ksp -∗ ut_res_bare Rsys (ud_norm pt) ksp.
  Proof.
    iIntros "H".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & (Hcaps & Hown))".
    subst pt.
    rewrite (ut_own_nopt_upt_irrel Rsys N V (ud_norm (pv_upt V))
               eq_refl eq_refl eq_refl).
    iExists N, (upd_upt V (ud_norm (pv_upt V))), av.
    rewrite /ut_env_nopt. iFrame "Htrap Hcaps Hown".
    iPureIntro. split; [reflexivity | split; [| split]]; assumption.
  Qed.

  (* THE TRAPFRAME BORROW at the BARE residue.  This is the form uservec's
     save/restore walks open: the trapframe page never leaves the residue
     (physical tier, unreachable from user mode), so it is available in
     exactly the window where the address space is not. *)
  Lemma ut_res_bare_tf_open (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    (forall ws : list (mword 64), length ws = TFWORDS -> tf_kernel_words_ok kroot ksp ws) ->
    ut_res_bare Rsys pt ksp -∗
    ∃ ws : list (mword 64), ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗ tf_page (ud_tfp pt) ws ∗
      (∀ ws' : list (mword 64), tf_page (ud_tfp pt) ws' -∗ ut_res_bare Rsys pt ksp).
  Proof.
    iIntros (Hgap) "H".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & (Hcaps & Hown))".
    iDestruct (ut_own_nopt_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    iDestruct (proc_priv_nopt_tf_open with "Hpv") as (ws) "[Htf Hclose]".
    rewrite Hupt.
    iDestruct (tf_page_length with "Htf") as %Hlen.
    iExists ws. iSplitR; [iPureIntro; exact (Hgap ws Hlen) |]. iFrame "Htf".
    iIntros (ws') "Htf'".
    iDestruct ("Hclose" $! ws' with "Htf'") as "Hpv'".
    iDestruct ("Hownback" $! (upd_tf V ws') with "Hpv' Hsy") as "Hown'".
    iExists N, (upd_tf V ws'), av.
    rewrite /ut_env_nopt. iFrame "Htrap Hcaps Hown'".
    iPureIntro. split; [| split; [| split]].
    - rewrite /upd_tf. exact Hupt.
    - exact Hksp.
    - exact Hwf.
    - exact Hav.
  Qed.

  (* THE PER-HART CSRs.  [hart_csrs] rides in [cpu_priv], hence in the
     [cpu_own 0 false pj false ∅] this residue's [ut_trap_parked] carries --
     so the bare form, the one that parks across user execution, is exactly
     where the trampoline and the trap loop reach it: uservec borrows
     [sscratch] across its save walk, and the loop hands [medeleg] and the
     two state-enable pins to [UserExec.user_cfg] for the user phase, keeping
     the closer wand as the parked remainder.  Open/close, not a tier of its
     own: nothing needs a name for "the residue minus its CSRs". *)
  Lemma ut_res_bare_csrs_open (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) :
    ut_res_bare Rsys pt ksp -∗
    hart_csrs ∗ (hart_csrs -∗ ut_res_bare Rsys pt ksp).
  Proof.
    iIntros "H".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & Henv)".
    iDestruct "Htrap" as "(Hstk & Harm & Hb1 & Hb2 & Hgh & Hcpu & Hclm)".
    iDestruct (cpu_own_csrs_open with "Hcpu") as "[Hcsrs Hback]".
    iFrame "Hcsrs". iIntros "Hcsrs".
    iDestruct ("Hback" with "Hcsrs") as "Hcpu".
    iExists N, V, av. rewrite /ut_trap_parked.
    iFrame "Hstk Harm Hb1 Hb2 Hgh Hcpu Hclm Henv".
    iPureIntro. split; [| split; [| split]]; assumption.
  Qed.

  (* BOTH AT ONCE, and uservec needs exactly that: its save walk holds the
     trapframe page open across +0x0c..+0x7a while its [csrw sscratch,a0] at
     +0x00 and the [csrr] at +0x76 hold the [sscratch] cell, and the two
     borrows therefore overlap.  Each single accessor consumes the whole
     residue, so neither can be applied to the other's remainder -- a sealed
     bundle's simultaneous borrows have to come out of ONE opener. *)
  Lemma ut_res_bare_tf_csrs_open (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    (forall ws : list (mword 64), length ws = TFWORDS -> tf_kernel_words_ok kroot ksp ws) ->
    ut_res_bare Rsys pt ksp -∗
    ∃ ws : list (mword 64), ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗
      tf_page (ud_tfp pt) ws ∗ hart_csrs ∗
      (∀ ws' : list (mword 64),
         tf_page (ud_tfp pt) ws' -∗ hart_csrs -∗ ut_res_bare Rsys pt ksp).
  Proof.
    iIntros (Hgap) "H".
    iDestruct "H" as (N V av) "(%Hupt & %Hksp & %Hwf & %Hav & Htrap & (Hcaps & Hown))".
    (* the CSRs, out of the trap bundle's own [cpu_own] *)
    iDestruct "Htrap" as "(Hstk & Harm & Hb1 & Hb2 & Hgh & Hcpu & Hclm)".
    iDestruct (cpu_own_csrs_open with "Hcpu") as "[Hcsrs Hcback]".
    (* ... and the trapframe page, out of the process block *)
    iDestruct (ut_own_nopt_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    iDestruct (proc_priv_nopt_tf_open with "Hpv") as (ws) "[Htf Hclose]".
    rewrite Hupt.
    iDestruct (tf_page_length with "Htf") as %Hlen.
    iExists ws. iSplitR; [iPureIntro; exact (Hgap ws Hlen) |].
    iFrame "Htf Hcsrs".
    iIntros (ws') "Htf' Hcsrs'".
    iDestruct ("Hclose" $! ws' with "Htf'") as "Hpv'".
    iDestruct ("Hownback" $! (upd_tf V ws') with "Hpv' Hsy") as "Hown'".
    iDestruct ("Hcback" with "Hcsrs'") as "Hcpu".
    iExists N, (upd_tf V ws'), av.
    rewrite /ut_env_nopt /ut_trap_parked.
    iFrame "Hstk Harm Hb1 Hb2 Hgh Hcpu Hclm Hcaps Hown'".
    iPureIntro. split; [| split; [| split]].
    - rewrite /upd_tf. exact Hupt.
    - exact Hksp.
    - exact Hwf.
    - exact Hav.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE WALK'S OWN VOCABULARY -- what the block lemmas of ProofUsertrap  *)
  (* hand one another.  Definitional, so the phases do not depend on each *)
  (* other's proofs.                                                      *)
  (* ------------------------------------------------------------------- *)

  (* THE SAVED FRAME.  The [c.addi sp,sp,-32] at +0x00 frees four slots and
     +0x02..+0x08 fill them with ra / s0 / s1 / s2, in that order at
     [pa_stk sp0 1..4].  ra is in here even though it is not callee-saved:
     the epilogue's [c.ldsp ra,24(sp)] is what makes the [ret] land on the
     boundary's [ret_pc (m !!! ra)]. *)
  Definition ut_frame (sp0 : mword 64) (vra vs0 vs1 vs2 : mword 64) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ vra ∗ pa_stk sp0 2 ↦₈ vs0 ∗
     pa_stk sp0 3 ↦₈ vs1 ∗ pa_stk sp0 4 ↦₈ vs2)%I.

  (* CALLEE-SAVED MINUS THE FOUR THE FRAME HOLDS.  [CalleeSaved.callee_saved
     m0 m] is FALSE at every point inside usertrap -- s1 holds [p] and s2
     holds [which_dev] from +0x26 on -- so what travels through the walk is
     this weaker relation, and the epilogue's four loads turn it back into
     the real thing.  sp is excluded too: it is [pa_stk sp0 4] until +0xc4. *)
  Definition ut_cs (m0 m : regfile) : Prop :=
    forall c : mword 5, is_cs_idx c = true ->
      Regidx c <> Regidx csp_rs1 ->
      Regidx c <> Regidx (mword_of_int 8 : mword 5) ->
      Regidx c <> Regidx (mword_of_int 9 : mword 5) ->
      Regidx c <> Regidx (mword_of_int 18 : mword 5) ->
      m !!! Regidx c = m0 !!! Regidx c.

  Lemma ut_cs_refl (m0 : regfile) : ut_cs m0 m0.
  Proof. intros c _ _ _ _ _. reflexivity. Qed.

  Lemma ut_cs_trans (m0 m1 m2 : regfile) :
    ut_cs m0 m1 -> ut_cs m1 m2 -> ut_cs m0 m2.
  Proof.
    intros H1 H2 c Hc H H0 H3 H4.
    rewrite (H2 c Hc H H0 H3 H4). exact (H1 c Hc H H0 H3 H4).
  Qed.

  Lemma ut_cs_of_callee_saved (m0 m : regfile) : callee_saved m0 m -> ut_cs m0 m.
  Proof. intros Hcs c Hc _ _ _ _. exact (callee_saved_lookup Hcs c Hc). Qed.

  Lemma ut_cs_insert (k : mword 5) (v : mword 64) (m0 m : regfile) :
    is_cs_idx k = false -> ut_cs m0 m -> ut_cs m0 (<[Regidx k := v]> m).
  Proof.
    intros Hk H c Hc H1 H2 H3 H4. rewrite upd_ne.
    - exact (H c Hc H1 H2 H3 H4).
    - apply not_eq_sym, (is_cs_idx_true_neq _ _ Hk). exact Hc.
  Qed.

  (* ...and the twin for the FOUR the frame holds.  A write to sp / s0 / s1 /
     s2 is invisible to [ut_cs] by construction -- those are the registers it
     says nothing about -- so it needs no [is_cs_idx] side condition, only
     that the destination IS one of them. *)
  Lemma ut_cs_insert4 (k : mword 5) (v : mword 64) (m0 m : regfile) :
    (Regidx k = Regidx csp_rs1 \/ Regidx k = Regidx (mword_of_int 8 : mword 5) \/
     Regidx k = Regidx (mword_of_int 9 : mword 5) \/
     Regidx k = Regidx (mword_of_int 18 : mword 5)) ->
    ut_cs m0 m -> ut_cs m0 (<[Regidx k := v]> m).
  Proof.
    intros Hk H c Hc H1 H2 H3 H4. rewrite upd_ne;
      [ exact (H c Hc H1 H2 H3 H4) | ].
    destruct Hk as [-> | [-> | [-> | ->]]]; congruence.
  Qed.

  (* THE EPILOGUE'S PAYOFF: [ut_cs] plus the four restored registers IS
     [callee_saved].  This is where the frame stops being bookkeeping. *)
  Lemma ut_cs_to_callee_saved (m0 m : regfile) :
    ut_cs m0 m ->
    m !!! Regidx csp_rs1 = m0 !!! Regidx csp_rs1 ->
    m !!! Regidx (mword_of_int 8 : mword 5) = m0 !!! Regidx (mword_of_int 8 : mword 5) ->
    m !!! Regidx (mword_of_int 9 : mword 5) = m0 !!! Regidx (mword_of_int 9 : mword 5) ->
    m !!! Regidx (mword_of_int 18 : mword 5) = m0 !!! Regidx (mword_of_int 18 : mword 5) ->
    callee_saved m0 m.
  Proof.
    intros H Hsp Hs0 Hs1 Hs2. unfold callee_saved. repeat apply conj;
      [ exact Hsp | exact Hs0 | exact Hs1 | exact Hs2 | .. ];
      (apply H; [ vm_compute; reflexivity
                | vm_compute; discriminate | vm_compute; discriminate
                | vm_compute; discriminate | vm_compute; discriminate ]).
  Qed.

  (* p->trapframe->epc EXISTS -- prepare_return's [pv_tf V !! tf_epc_idx =
     Some epc] premise, read off the page's own length invariant rather than
     asked of usertrap's caller. *)
  Lemma ut_epc_exists (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗
    ⌜ ∃ ep : mword 64, pv_tf V !! tf_epc_idx = Some ep ⌝.
  Proof.
    iIntros "Hpv".
    iDestruct (proc_priv_tf with "Hpv") as "(_ & Htfp & _)".
    rewrite /tf_page. iDestruct "Htfp" as "(%Hlen & _ & _)".
    iPureIntro. apply lookup_lt_is_Some_2. rewrite Hlen.
    unfold TFWORDS, tf_epc_idx. lia.
  Qed.

  (* the record eta a [proc_priv_copy] round trip that changed nothing needs,
     the [upd_tf_id] of the descriptor field. *)
  Lemma upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
  Proof. by destruct V. Qed.

  (* THE TRAP CSRs, RAW -- what usertrap holds between the [csrw stvec] at
     +0x1e and whichever later point on its path first wants the folded
     bundle.  It cannot fold at +0x1e, because it READS scause three times,
     sepc once and stval twice afterwards, and [trap_csrs] buries all three
     under existentials.  [ut_trap_csrs_fold] above is the fold; the three
     values are pinned here because the reads' results are what the dispatch
     branches on. *)
  Definition ut_csrs_raw (ep sc st : mword 64) : iProp Σ :=
    (sepc ↦ᵣ ep ∗ scause ↦ᵣ sc ∗ stval ↦ᵣ st ∗
     stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) ∗
     ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
     sret_bits ('b"0" : mword 1) ('b"1" : mword 1) ∗
     kpt_on cpu_id)%I.

  Lemma ut_csrs_raw_fold (ep sc st : mword 64) :
    ut_csrs_raw ep sc st -∗
    intr_handler_spec kt (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    trap_csrs kt.
  Proof.
    iIntros "(Hep & Hsc & Hst & Hstv & Hq & Hsret & Hkpt) #Hih".
    iApply (ut_trap_csrs_fold ep sc st with "Hep Hsc Hst Hsret Hstv Hq Hkpt Hih").
  Qed.

  (* EVERYTHING ELSE A BLOCK CARRIES, at its own SIE index: the per-cpu
     bundle, the two arm complements, and the five cones' environment.  At
     [b = false] the complements are the real trap-CSR set and the real
     claim; at [b = true] both are [emp] because the enabled arm owns them.
     That is what makes the tail blocks index-generic, which they have to be:
     +0xa6 is reached at [true] from the syscall arm and at [false] from the
     other four. *)
  Definition ut_hold (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) (b : bool) (lks : gset string) : iProp Σ :=
    (cpu_own 0%nat b (un_pj N) b lks ∗
     trap_csrs_ext kt b ∗
     cpu_claim_ext b (un_pj N) ∗
     ut_env Rsys N V)%I.

  (* the index arithmetic, once.  [nx] is a block's own stack index and [av]
     the entry budget; the four frame slots are spent and, on the syscall
     arm, [kv_frame_slots] more sit in the enabled arm's reserve.  Either way
     what is left covers every callee, because [K_usertrap] was chosen so:
     see its definition. *)
  Lemma ut_nx_bound (b : bool) (av nx : nat) :
    (K_usertrap <= av)%nat -> (trap_res b + nx)%nat = (av - 4)%nat ->
    (K_syscall <= nx)%nat.
  Proof.
    unfold trap_res. destruct b; lia.
  Qed.

  (* ...and the STRONGER bound the [csrsi] at +0x9e needs, which is available
     only on the arm that reaches it.  There the block's index is still the
     disabled one, so nothing has been spent on a reserve yet and the whole
     [kv_frame_slots + K_syscall] is in hand -- which is exactly what
     [wp_csrsi_sstatus_x0_enable_s_sconf]'s pre index [trap_res true + n]
     demands, and why [K_usertrap] carries the summand at all. *)
  Lemma ut_nx_bound_off (av nx : nat) :
    (K_usertrap <= av)%nat -> (trap_res false + nx)%nat = (av - 4)%nat ->
    (kv_frame_slots + K_syscall <= nx)%nat.
  Proof. unfold trap_res. lia. Qed.

  (* WHAT THE FLIP AT +0x9e TAKES OUT OF THE PER-CPU BUNDLE.  The enabling
     leaf wants the counting token and the cells SEPARATELY (at the enabled
     base both live inside [sie_arm]), and at the disabled index
     [cpu_own 0 false pj C false] IS the two of them beside the caller's own
     frame.  ProofScheduler's [sc_flip_pre] is the same lemma at [C = emp];
     this one is [C]-generic because usertrap's frame is a parameter. *)
  Lemma ut_flip_pre (pj : mword 64) (lks : gset string) :
    cpu_own 0%nat false pj false lks -∗
    intr_count 0 false ∗ cpu_priv 0 true pj lks.
  Proof.
    rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells.
    iIntros "(((_ & Hn & Hi & Hp) & Hl) & Hc)".
    iFrame "Hc Hn Hi Hp Hl". iPureIntro. vm_compute. reflexivity.
  Qed.

End UsertrapRes.

(* ---------------------------------------------------------------------- *)
(* THE TRANSPORT, outside the section so both harts are free arguments --   *)
(* [IntrDefs]' three transports' idiom exactly.                            *)
(*                                                                         *)
(* [ut_hold] is hart-indexed and the walk FRAMES it across steps that can   *)
(* move the hart, so it needs one.  It has one for the same two-halves      *)
(* reason its three components do: at [b = true] every hart-indexed member  *)
(* is [emp] or a pure fact ([cpu_own]'s payload is inside [sie_arm],        *)
(* [trap_csrs_ext true] and [cpu_claim_ext true] are [emp]) and [ut_env] is *)
(* hart-FREE by construction -- which is exactly what [devintr_caps_any]    *)
(* and [SpecSyscall]'s hart-free [syscall_env] are for.  At [b = false] no  *)
(* trap can have been taken and [wp_next]'s conditional equality pins the   *)
(* hart.  Chain the per-step equalities with [wp_next_chain] and apply this *)
(* once per crossing.                                                      *)
(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* THE BOUNDARY'S [j] AND [usertrap_res]'s ARE NOT TIED, AND AT [true] IT   *)
(* DOES NOT MATTER.                                                        *)
(*                                                                         *)
(* [SpecUsertrap.wp_usertrap_body] takes a slot index [j] and states its    *)
(* crossing at [wp_next true (proc_addr j)], while [ut_res] existentially   *)
(* packages its OWN [ut_names] and therefore its own [un_j].  Nothing ties  *)
(* the two -- and nothing needs to, because at index [true] a crossing's    *)
(* guard is [true = false \/ p = zero_reg -> …], whose antecedent is FALSE  *)
(* for any real process: the [wp_next] does not depend on [p] at all there. *)
(* So the walk runs entirely at [un_pj N] (which is where [ut_trap]'s       *)
(* [sie_cap_gpr] / [cpu_own] / [cpu_claim] live, and those DO care) and the *)
(* entry block swaps the boundary's crossing over with this one line.       *)
(*                                                                         *)
(* The alternative -- keying [ut_res] on [j] as well as on [(pt, ksp)] --   *)
(* was rejected for the reason the key is [(pt, ksp)] in the first place:   *)
(* those are the only two things the TRAMPOLINE knows.                      *)
(* ---------------------------------------------------------------------- *)
Lemma wp_next_true_swap `{!riscvGS Σ} `{GEN : GenId} `{CID0 : CpuId}
    (p q : mword 64) (K : forall CID : CpuId, iProp Σ) :
  p <> zero_reg ->
  wp_next true p K -∗ wp_next true q K.
Proof.
  intros Hp. iIntros "H" (CIDx Hs). iApply "H". iPureIntro.
  intros [Hb | Hz]; [discriminate Hb | exfalso; exact (Hp Hz)].
Qed.

Lemma ut_hold_transport
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ} `{GEN : GenId}
    (CID0 CID1 : CpuId) (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
    (N : ut_names) (V : pprivate) (b : bool) (lks : gset string) :
  (b = false \/ un_pj N = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
  ut_hold (CID := CID0) Rsys N V b lks -∗ ut_hold (CID := CID1) Rsys N V b lks.
Proof.
  intros Heq. rewrite /ut_hold. iIntros "(Hcpu & Hcsrs & Hclm & Henv)".
 iDestruct (cpu_own_transport CID0 CID1 0%nat b (un_pj N) b  Heq
               with "Hcpu") as "$".
  iDestruct (trap_csrs_ext_transport CID0 CID1 b (un_pj N) Heq
               with "Hcsrs") as "$".
  iDestruct (cpu_claim_ext_transport CID0 CID1 b (un_pj N) Heq
               with "Hclm") as "$".
  iExact "Henv".
Qed.

(* ---------------------------------------------------------------------- *)
(* THE FIT, CHECKED HERE.                                                  *)
(*                                                                         *)
(* [SpecUsertrap.USERTRAP] declares [usertrap_res] as a PARAMETER, so its   *)
(* type has to be the one its instantiation has -- and the instantiation's  *)
(* instance list is not the boundary's, it is the union of the five cones'. *)
(* Nothing checks that until ProofUsertrap seals the module, which is a     *)
(* long way from here and a bad place to discover a missing class.  This    *)
(* functor is that check and nothing else: its one definition is written    *)
(* with the module type's binder list VERBATIM, so it fails to compile the  *)
(* moment [ut_res] needs a class [USERTRAP] does not offer (or offers one   *)
(* it does not need, which is just as worth knowing).                      *)
(*                                                                         *)
(* [syscall_env] is why it is a functor: that one member of the union is    *)
(* itself still abstract (SpecSyscall's contract is ASSUMED), so the        *)
(* definition can only be written under a SYSCALL.                         *)
(* ---------------------------------------------------------------------- *)
Module UtResFits (SY : SYSCALL) <: USERTRAP_RES.

  Definition usertrap_res
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res SY.syscall_env.

  Definition usertrap_res_parked
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res_parked SY.syscall_env.

  Lemma usertrap_res_tlb_close
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    usertrap_res_parked pt ksp -∗ tlb_res_pt kroot -∗ usertrap_res pt ksp.
  Proof. exact (ut_res_tlb_close SY.syscall_env pt ksp kroot). Qed.

  Lemma usertrap_res_tlb_open
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res pt ksp -∗
    ∃ kroot : mword 44, tlb_res_pt kroot ∗ usertrap_res_parked pt ksp.
  Proof. exact (ut_res_tlb_open SY.syscall_env pt ksp). Qed.

  Definition usertrap_res_bare
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res_bare SY.syscall_env.

  Lemma usertrap_res_pt_close
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗ proc_pt pt -∗ usertrap_res_parked pt ksp.
  Proof. exact (ut_res_pt_close SY.syscall_env pt ksp). Qed.

  Lemma usertrap_res_pt_open
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_parked pt ksp -∗ proc_pt pt ∗ usertrap_res_bare pt ksp.
  Proof. exact (ut_res_pt_open SY.syscall_env pt ksp). Qed.

  Lemma usertrap_res_bare_norm
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗ usertrap_res_bare (ud_norm pt) ksp.
  Proof. exact (ut_res_bare_norm SY.syscall_env pt ksp). Qed.

  Lemma usertrap_res_tf_open
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    (forall ws : list (mword 64), length ws = TFWORDS -> tf_kernel_words_ok kroot ksp ws) ->
    usertrap_res_bare pt ksp -∗
    ∃ ws : list (mword 64), ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗ tf_page (ud_tfp pt) ws ∗
      (∀ ws' : list (mword 64), tf_page (ud_tfp pt) ws' -∗ usertrap_res_bare pt ksp).
  Proof. exact (ut_res_bare_tf_open SY.syscall_env pt ksp kroot). Qed.

  Lemma usertrap_res_csrs_open
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗
    hart_csrs ∗ (hart_csrs -∗ usertrap_res_bare pt ksp).
  Proof. exact (ut_res_bare_csrs_open SY.syscall_env pt ksp). Qed.

  Lemma usertrap_res_tf_csrs_open
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    (forall ws : list (mword 64), length ws = TFWORDS -> tf_kernel_words_ok kroot ksp ws) ->
      usertrap_res_bare pt ksp -∗
      ∃ ws : list (mword 64), ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗
        tf_page (ud_tfp pt) ws ∗ hart_csrs ∗
        (∀ ws' : list (mword 64),
           tf_page (ud_tfp pt) ws' -∗ hart_csrs -∗ usertrap_res_bare pt ksp).
  Proof. exact (ut_res_bare_tf_csrs_open SY.syscall_env pt ksp kroot). Qed.

End UtResFits.
