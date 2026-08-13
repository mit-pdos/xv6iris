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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpGpr.
Require Import SmodeCore.
Require Import KernelText KernelDataInv MstatusBits.
Require Import IntrDefs.
Require Import WpLock.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.   (* csp_rs1 -- sie_cap's stack key *)
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv.
Require Import ProcInv.
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
Require Import SpecPanic.
Require Import SpecProcinit.
Require Import SpecFileclose.
Require Import SpecDevintr.
Require Import SpecPrintkGen.
Require Import SpecSyscall.
Require Import SpecKexit.
Require Import SpecKernelvec.   (* the two kernelvec trap-vector facts *)
Require Import SpecUsertrap.   (* USERTRAP_RES -- the fit is checked at the foot *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
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
Definition K_usertrap : nat := (4 + kv_frame_slots + K_syscall)%nat.

Section UsertrapRes.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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
    stack_own ksp (trap_res false + av)%nat.

  (* [sconf] MINUS the mstatus cell AND the privilege cell, as a CLOSER
     rather than as a restatement of the bundle's internals: re-spelling
     hw_config / minstret / the mie and menvcfg pin blocks here would be a
     second place for five pure side conditions to drift.  This is
     [IntrDefs.sconf_at]'s idiom with one more cell handed out --
     [sconf_at] exposes only mstatus, and the trampoline needs
     [cur_privilege] too (userret's [sret] writes it).

     BELONGS BESIDE [sconf_at] IN IntrDefs.v and is here only because
     IntrDefs is at the bottom of the tree and editing it costs a near-total
     rebuild; hoist it the next time something else has to touch that file. *)
  Definition ut_sconf_closer : iProp Σ :=
    (∀ ms' : mword 64,
       cur_privilege ↦ᵣ Supervisor -∗ sconf_msown ms' -∗ sconf)%I.

  (* the opener that makes it faithful: if this proof breaks, the closer above
     is no longer "the rest of sconf". *)
  Lemma ut_sconf_open :
    sconf -∗ ∃ ms : mword 64,
      ut_sconf_closer ∗ cur_privilege ↦ᵣ Supervisor ∗ sconf_msown ms.
  Proof.
    iIntros "(#Hhw & #Hminv & Hpriv & Hmsx & Hmie & Hmenv)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Htie & %Hmsf)".
    iExists ms. iSplitR "Hpriv Hms Hhalf Htie".
    { rewrite /ut_sconf_closer. iIntros (ms') "Hpriv' Hown'".
      iDestruct "Hown'" as "(Hms' & Hhalf' & Htie' & %Hmsf')".
      iFrame "Hhw Hminv Hpriv' Hmie Hmenv".
      iExists ms'. iFrame "Hms' Hhalf' Htie'". iPureIntro. exact Hmsf'. }
    iFrame "Hpriv". rewrite /sconf_msown. iFrame "Hms Hhalf Htie".
    iPureIntro. exact Hmsf.
  Qed.

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
      (C : iProp Σ) : iProp Σ :=
    (ut_stack ksp av ∗
     (* the translation slot, in its KPT arm: THE KERNEL PAGE TABLE, on the
        SHARED tier ([KptShare.tlb_res_pt] inside), which is the whole point
        of SpecUsertrap.v's restatement *)
     strans_inv ∗
     sie_arm false pj ∗
     strans_bit strans_bit_kpt ∗
     ut_sconf_closer ∗
     ut_ghosts ∗
     cpu_own 0%nat false pj C false ∗
     (* the running claim.  It is what [SpecYield] / [SpecKexit] want as
        [cpu_claim_ext false pj], and the trap is where it comes from. *)
     cpu_claim pj)%I.

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
  Lemma ut_trap_open (pj ksp : mword 64) (av : nat) (C : iProp Σ)
      (m : regfile) (ms : mword 64) :
    sconf_ms_facts ms ->
    eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ->
    eq_vec (_get_Mstatus_SPP ms) ('b"1") = false ->
    _get_Mstatus_SPIE ms = ('b"1" : mword 1) ->
    m !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx Rtp = cid_word ->
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms -∗
    gpr_file m -∗
    ut_trap pj ksp av C -∗
      sie_cap_gpr m av false pj ∗
      cpu_own 0%nat false pj C false ∗
      cpu_claim pj ∗
      ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
      strans_bit strans_bit_kpt ∗
      sret_bits ('b"0" : mword 1) ('b"1" : mword 1).
  Proof.
    intros Hmsf Hsie Hspp Hspie Hsp Htp.
    apply mword1_zero_of_ne_one in Hsie.
    apply mword1_zero_of_ne_one in Hspp.
    iIntros "Hhs Hpriv Hms Hgpr Ht".
    iDestruct "Ht" as "(Hstk & Hstr & Harm & Hkpt & Hcl & Hgh & Hcpu & Hclm)".
    iDestruct "Hgh" as "(Hhalf & Hq & Htie & Htrav)".
    iFrame "Hcpu Hclm Hq Hkpt Htrav".
    rewrite /sie_cap_gpr. iFrame "Hhs".
    iSplitL "Hpriv Hms Hhalf Htie Hcl".
    { iApply ("Hcl" $! ms with "Hpriv [Hms Hhalf Htie]").
      rewrite /sconf_msown /sret_tie Hsie Hspp Hspie.
      iFrame "Hms Hhalf Htie". iPureIntro. exact Hmsf. }
    rewrite /sie_cap /ut_stack Hsp.
    iFrame "Hstk Hstr Harm".
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
    strans_bit strans_bit_kpt -∗
    intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    trap_csrs.
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
     panic_wp_any] carries panic's contract for the same reason (a function
     that PARKS does not return on the hart it entered on).  It is
     persistent, hence free to hand to devintr at whatever hart the call
     happens on ([devintr_caps_any_at]), and it is satisfiable: of
     [devintr_caps]' eight members six are hart-free outright, [timer_cap] is
     available at every hart from [SpecBootDevCaps.boot_dev_caps] (whose
     interface quantifies over the hart), and [tick_keeper]'s REAL arm --
     which the boot hart brings up -- is hart-free too.  What it rules out is
     satisfying the tick keeper with the left disjunct, and that is right: a
     process can migrate onto hart 0. *)
  Definition devintr_caps_any (γu : uart_names) (γv : disk_names)
      (γdk γtl : gname) (γs : list gname)
      (pd pav pu : mword 64) : iProp Σ :=
    (□ ∀ h : CPU,
        devintr_caps (CID := h) γu γv γdk γtl γs pd pav pu)%I.

  Global Instance devintr_caps_any_persistent γu γv γdk γtl γs pd pav pu :
    Persistent (devintr_caps_any γu γv γdk γtl γs pd pav pu).
  Proof. rewrite /devintr_caps_any. apply _. Qed.

  Lemma devintr_caps_any_at (h : CPU) (γu : uart_names) (γv : disk_names)
      (γdk γtl : gname) (γs : list gname) (pd pav pu : mword 64) :
    devintr_caps_any γu γv γdk γtl γs pd pav pu -∗
    devintr_caps (CID := h) γu γv γdk γtl γs pd pav pu.
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
    (procs_inv (un_s N) ∗
     panic_wp_any ∗
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
    iIntros "(_ & #Hp & _ & _ & _ & _ & _ & _ & #Hkm & _ & _ & _ & _ & _ & _ & _ & #Hav & _)".
    iExists (un_ka N). iFrame "Hkm Hav Hp".
  Qed.

  (* the EXCLUSIVE remainder: what a callee can consume and must give back --
     plus [proc_priv], which every callee gives back at a MOVED record, which
     is why [V] is a parameter of this half and not of [ut_caps]. *)
  Definition ut_own (Rsys : gname -> mword 64 -> iProp Σ)
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
     Rsys (un_f N) (un_pj N))%I.

  Definition ut_env (Rsys : gname -> mword 64 -> iProp Σ)
      (N : ut_names) (V : pprivate) : iProp Σ :=
    (ut_caps N ∗ ut_own Rsys N V)%I.

  (* the process block and the syscall environment, borrowed together and
     handed back at a moved record: syscall wants both, prepare_return and
     vmfault only the first. *)
  Lemma ut_own_priv (Rsys : gname -> mword 64 -> iProp Σ) (N : ut_names)
      (V : pprivate) :
    ut_own Rsys N V -∗
    proc_priv (un_f N) (un_pj N) (un_pid N) V ∗
    Rsys (un_f N) (un_pj N) ∗
    (∀ V' : pprivate,
       proc_priv (un_f N) (un_pj N) (un_pid N) V' -∗
       Rsys (un_f N) (un_pj N) -∗ ut_own Rsys N V').
  Proof.
    iIntros "(Hb & Hbm & Hip & Hfd & Hir & Hpv & Hsy)".
    iFrame "Hpv Hsy". iIntros (V') "Hpv Hsy".
    rewrite /ut_own. iFrame "Hb Hbm Hip Hfd Hir Hpv Hsy".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [usertrap_res] itself.                                              *)
  (* ------------------------------------------------------------------- *)
  Definition ut_res (Rsys : gname -> mword 64 -> iProp Σ)
      (pt : uptd) (ksp : mword 64) : iProp Σ :=
    (∃ (N : ut_names) (V : pprivate) (av : nat) (C : iProp Σ),
       (* THE PROCESS RUNNING IS THE ONE WHOSE TABLE THE TRAMPOLINE PARKED.
          This equation is the whole reason R is keyed on [pt]: it is what
          lets userret install [MAKE_SATP(p->pagetable)] and know it is the
          table uservec came out of. *)
       ⌜ pv_upt V = pt ⌝ ∗
       (* ...and the stack the trapframe's kernel_sp word named *)
       ⌜ add_vec (un_ks N) (mword_of_int 4096) = ksp ⌝ ∗
       ⌜ ut_wf N ⌝ ∗
       ⌜ (K_usertrap <= av)%nat ⌝ ∗
       ut_trap (un_pj N) ksp av C ∗
       ut_env Rsys N V)%I.

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
     strans_bit strans_bit_kpt)%I.

  Lemma ut_csrs_raw_fold (ep sc st : mword 64) :
    ut_csrs_raw ep sc st -∗
    intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    trap_csrs.
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
  Definition ut_hold (Rsys : gname -> mword 64 -> iProp Σ)
      (N : ut_names) (V : pprivate) (C : iProp Σ) (b : bool) : iProp Σ :=
    (cpu_own 0%nat b (un_pj N) C b ∗
     trap_csrs_ext b ∗
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
    unfold K_usertrap, trap_res, kv_frame_slots. destruct b; lia.
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
  Proof. unfold K_usertrap, trap_res, kv_frame_slots. lia. Qed.

  (* WHAT THE FLIP AT +0x9e TAKES OUT OF THE PER-CPU BUNDLE.  The enabling
     leaf wants the counting token and the cells SEPARATELY (at the enabled
     base both live inside [sie_arm]), and at the disabled index
     [cpu_own 0 false pj C false] IS the two of them beside the caller's own
     frame.  ProofScheduler's [sc_flip_pre] is the same lemma at [C = emp];
     this one is [C]-generic because usertrap's frame is a parameter. *)
  Lemma ut_flip_pre (pj : mword 64) (C : iProp Σ) :
    cpu_own 0%nat false pj C false -∗
    intr_count 0 false ∗ cpu_cells 0 true pj ∗ C.
  Proof.
    rewrite cpu_own_off /cpu_hart /cpu_cells.
    iIntros "(((_ & Hn & Hi & Hp) & Hc) & HC)".
    iFrame "Hc HC Hn Hi Hp". iPureIntro. vm_compute. reflexivity.
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
      !kallocG Σ, !irefslotG Σ, !iregG Σ} `{GEN : GenId}
    (CID0 CID1 : CpuId) (Rsys : gname -> mword 64 -> iProp Σ)
    (N : ut_names) (V : pprivate) (C : iProp Σ) (b : bool) :
  (b = false \/ un_pj N = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
  ut_hold (CID := CID0) Rsys N V C b -∗ ut_hold (CID := CID1) Rsys N V C b.
Proof.
  intros Heq. rewrite /ut_hold. iIntros "(Hcpu & Hcsrs & Hclm & Henv)".
  iDestruct (cpu_own_transport CID0 CID1 0%nat b (un_pj N) C b Heq
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
        !kallocG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res SY.syscall_env.

End UtResFits.
