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
Require Import StackOwn.
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
    un_tx : gname;                    (* the uart tx lock                   *)
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

  Definition ut_env (Rsys : gname -> mword 64 -> iProp Σ)
      (N : ut_names) (V : pprivate) : iProp Σ :=
    (* ---- persistent, so free to carry ---- *)
    (procs_inv (un_s N) ∗
     panic_wp_any ∗
     kernel_data ∗
     is_kstack (un_pj N) (un_ks N) ∗
     devintr_caps (un_u N) (un_v N) (un_tx N) (un_k N) (un_tk N) (un_s N)
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
     (* ---- exclusive ---- *)
     kalloc_avail (un_ka N) None ∗
     bslots (un_bn N) 3 ∗
     fileclose_ic_env (un_fn N) ∗
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

End UsertrapRes.

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
