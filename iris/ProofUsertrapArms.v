(* ProofUsertrapArms.v -- usertrap's THREE CHEAP ARMS, the ones that never
   leave the interrupts-off index.

     +0x56   printk("usertrap(): unexpected scause ...", ...);
             printk("            sepc=... stval=...", ...);
             setkilled(p);  goto +0xa6                        <- ut_56
     +0xd0   if (vmfault(p->pagetable, p->sz, r_stval(), scause==13))
               goto +0xa6; else goto +0x56                    <- ut_d0
     +0xea   if (killed(p)) kexit(-1); else goto +0xfc        <- ut_e8

   WHY THESE THREE ARE ONE FILE, AND WHY THEY ARE CHEAP.  All three are
   reached only from the scause dispatch, i.e. at [b = false] -- the trap
   cleared SIE and nothing on any of these paths re-enables it (only the
   syscall arm's [csrsi sstatus,2] does).  At [b = false] EVERY [wp_next]
   collapses with [WpNext.wp_next_off_intro] at the hart the block was
   entered on, including the ones handed back by the four callees (printk,
   setkilled, vmfault, killed).  So there is not one hart crossing in this
   file: no [cpu_own_transport], no [trap_csrs_ext_transport], no
   [wp_next_retarget], and -- the thing that actually costs time elsewhere --
   not a single [(CID := ...)] annotation.  Contrast ProofUsertrapTail, whose
   [ut_ret]/[ut_a6]/[ut_fa] are index-GENERIC and therefore pay for a hart
   epoch per call (its §5 / claude-notes/projects/usertrap.md finding 5).
   Hence the statements below take the literal [false] where the tail's take a
   parameter [b], and instantiate the tail's blocks at [b := false].

   THE TRAP CSRs ARE READ OUT OF THE FOLDED BUNDLE, not carried raw.  At
   [b = false] [IntrDefs.trap_csrs_ext false] IS [trap_csrs], and [trap_csrs]
   holds sepc / scause / stval under existentials beside the [intr_res] the
   [csrw stvec] at +0x1e built.  +0x56 reads all three and +0xd0 reads two, so
   both blocks open the bundle, name the values, and close it again at the same
   values ([ua_hold_off] / [ua_hold_on]).  That is why these blocks' premise
   list is [ut_a6]'s VERBATIM -- they need no [ut_csrs_raw] and, with it, no
   [intr_handler_spec kernelvec] and no KERNELVEC functor argument.  (The raw
   form is still what the walk carries from +0x1e to the dispatch, where the
   three values must be PINNED because the branches read them; here they are
   only passed to printk / vmfault and their identity is irrelevant.)

   printk IS THE ASSUMED GENERAL PATH, TAKEN AS A HYPOTHESIS.  [PRINTK_GEN]'s
   only instance is [LinkPrintk]'s [Axiom], so instantiating the functor
   here would carry that axiom into usertrap's [Print Assumptions] and, through
   the trampoline, into everybody's.  [SpecPrintk.printk_gen_contract] is
   the [Prop] twin of [SpecPanic.panic_wp_any] for exactly this reason, so
   [ut_56] takes it as an ordinary [->] premise and pushes the obligation up.
   ProofProcdumpLoop.v and ProofBalloc.v are the two worked call sites.  The
   vararg obligation is free: every conversion in both format strings is
   [%lx]/[%d], i.e. [PkANum], and [pk_desc_res _ PkANum = True]
   ([UsertrapAux.ut_fmt{1,2}_descs_res]).

   VMFAULT IS THE ONE CALLEE THAT MOVES THE PROCESS RECORD, and it is taken
   over the SAME accessor copyin/copyout use ([ProcInv.proc_priv_copy]): it
   hands out [p_sz], [p_pagetable] and [proc_pt] and takes them back at a
   descriptor that only GREW ([uptd_ext_sz]).  Since the psz bump only
   [proc_pt] actually crosses the call -- vmfault takes the size as an
   argument now, so the two CELLS are read at +0xde / +0xe0 and handed
   straight back.  Its [kalloc_env] comes from
   [UsertrapRes.ut_caps_kalloc] and is PERSISTENT at [None], so vmfault
   consuming it costs nothing.  On the success arm the record moves, so
   [ut_a6]'s [ud_tfp (pv_upt V') = ud_tfp pt] has to be re-established -- and
   [uptd_insert] keeps [ud_tfp] by construction, so it is a projection rather
   than an obligation.  [VMFAULT] also still asks for a RAW-map tp entry
   ([mm !!! Rtp = cid_word]) that its own proof has not shed; as in
   ProofCopyout.v the pinned map [tp_pin M] has it for free ([HartTp.rget_tp])
   and swapping [sie_cap_gpr]'s map argument for the pin changes nothing
   observable ([ua_pin_sie_cap_gpr]). *)
From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec.
Require Import PageGeom.
Require Import RegFile HartTp WpNext CpuOwn.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import WpGprCsrwA.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfCsr WpSconfBtype.
Require Import WpSmodeIntr.        (* [wp_cli_s_sconf] *)
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import KallocInv KvmSpec.
Require Import BioInv DiskPtsto WpUart FsBlocks LogInv FsCrash.
Require Import IrefSlots InodeRegion.
Require Import FdSlots ProcInv.
Require Import SchedCtx PanicStub.
Require Import FileInvDefs.
Require Import CodeUsertrap.
Require Import SpecKilled SpecSetkilled SpecKexit SpecYield SpecPrepareReturn.
Require Import SpecVmfault.
Require Import SpecPrintk.
Require Import SpecSyscall SpecSysExit.
Require Import SpecUsertrap UsertrapRes.
Require Import ProofUsertrapParts.
Require Import UsertrapAux.
Require Import ProofUsertrapTail.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

Module UtArms (PR : PREPARE_RETURN) (KI : KILLED) (KE : KEXIT) (YI : YIELD)
              (SK : SETKILLED) (VM : VMFAULT).

(* the tail's three blocks, at this file's callee instances: +0x56 and +0xd0
   both end in [ut_a6], +0xd0's failure arm in [ut_56], and +0xe8's two arms
   in [ut_fa] and [ut_kexit]. *)
Module T := UtTail PR KI KE YI.

(* register indices and the two scripts, at MODULE level, for the reason
   ProofUsertrapTail records: an [Ltac] defined inside a section is discharged
   over its variables and unusable in the next one, and a [Notation] inside a
   section disappears with it. *)
Notation Rra := (mword_of_int 1  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Ltac pcw := apply bv_eq; vm_compute; reflexivity.


Section UtArmsCommon.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* [ut_hold] AT THE LITERAL [false], BOTH WAYS.                          *)
  (* ==================================================================== *)
  (* [trap_csrs_ext false] is [trap_csrs] and [cpu_claim_ext false p] is
     [cpu_claim p] -- by iota, so both directions are one [iExact].  They are
     lemmas rather than an inline [rewrite /trap_csrs_ext] because the
     proofmode's [IntoSep] search is keyed on the head of the hypothesis, and
     [trap_csrs_ext false] is not syntactically a [∗]: destructuring it
     directly is a coin flip on whether resolution unfolds the definition. *)
  Lemma ua_hold_off (N : ut_names) (V : pprivate) (C : iProp Σ) (lks : gset string) :
    ut_hold Rsys N V C false lks -∗
      cpu_own 0%nat false (un_pj N) C false lks ∗ trap_csrs ∗
      cpu_claim (un_pj N) ∗ ut_env Rsys N V.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma ua_hold_on (N : ut_names) (V : pprivate) (C : iProp Σ) (lks : gset string) :
    cpu_own 0%nat false (un_pj N) C false lks -∗ trap_csrs -∗
    cpu_claim (un_pj N) -∗ ut_env Rsys N V -∗
    ut_hold Rsys N V C false lks.
  Proof.
    iIntros "Hcpu Hcsrs Hclm Henv". rewrite /ut_hold.
    iSplitL "Hcpu"; [iExact "Hcpu"|].
    iSplitL "Hcsrs"; [iExact "Hcsrs"|].
    iSplitL "Hclm"; [iExact "Hclm"|].
    iExact "Henv".
  Qed.

  (* ==================================================================== *)
  (* THE tp PIN, three ways -- what [VMFAULT]'s un-shed raw-map premise      *)
  (* costs its callers.  ProofCopyout.v pays exactly the same three.        *)
  (* ==================================================================== *)
  Lemma ua_pin_sie_cap_gpr (M : regfile) (avail : nat) (bb : bool)
      (pp : mword 64) :
    sie_cap_gpr (tp_pin M) avail bb pp = sie_cap_gpr M avail bb pp.
  Proof.
    unfold sie_cap_gpr, sie_cap.
    rewrite (tp_pin_id (tp_pin M) (rget_tp M)).
    rewrite (tp_pin_sp M).
    reflexivity.
  Qed.

  Lemma ua_pin_lookup (M : regfile) (k : mword 5) :
    Regidx k <> Regidx Rtp -> tp_pin M !!! Regidx k = M !!! Regidx k.
  Proof. intro H. rewrite /tp_pin. apply upd_ne. exact H. Qed.

  Lemma ua_pin_cs (m0 M : regfile) : ut_cs m0 M -> ut_cs m0 (tp_pin M).
  Proof.
    intro H. rewrite /tp_pin.
    apply ut_cs_insert; [vm_compute; reflexivity | exact H].
  Qed.

End UtArmsCommon.


Section Ut56.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* +0x56 .. +0x82: THE UNEXPECTED-SCAUSE ARM.                            *)
  (* ==================================================================== *)
  (*   printk("usertrap(): unexpected scause 0x%lx pid=%d\n", scause, p->pid)
       printk("            sepc=0x%lx stval=0x%lx\n", sepc, stval)
       setkilled(p);  j +0xa6

     Reached from the dispatch's fall-through and, on the vmfault failure arm,
     from [ut_d0]'s [c.j] at +0xe6.  [p->pid] is a FRACTIONAL read of the pid
     cell through [ProcInv.proc_priv_pid] -- the same quarter
     SpecAcquiresleep / SpecHoldingsleep take -- given straight back, so the
     process record does not move and [ut_a6] is applied at the SAME [V]. *)
  Lemma ut_56 (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (C : iProp Σ)
      (mie_v menvcfg0 : mword 64) (lks : gset string) :
    printk_gen_contract (un_pr N) (un_u N) (un_v N) ->
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res false + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0x56)) -∗
    sie_cap_gpr m nx false (un_pj N) -∗
    ut_hold Rsys N V C false lks -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpk Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv.
    pose proof (ut_nx_bound false av nx Hav Hnx) as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hcont".
    iDestruct (ua_hold_off Rsys N V C with "Hhold") as
      "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    (* depth 0 forces the held set empty, so the printk / killed / setkilled
       order premises need no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    (* the four persistent members this block needs, read WITHOUT consuming
       [Hcaps] (durable-notes: destructuring an intuitionistic hypothesis
       eats the name, and the exit hands [ut_env] back). *)
    iAssert (procs_inv (un_s N)) with "[]" as "#Hpi".
    { iDestruct "Hcaps" as "($ & _)". }
    iAssert (panic_wp_any) with "[]" as "#Hpa".
    { iDestruct "Hcaps" as "(_ & $ & _)". }
    iAssert (kernel_data) with "[]" as "#Hkd".
    { iDestruct "Hcaps" as "(_ & _ & $ & _)". }
    iAssert (printk_env (un_pr N) (un_u N) (un_v N)) with "[]" as "#Hpenv".
    { iDestruct "Hcaps" as "(_ & _ & _ & _ & _ & $ & _)". }
    iPoseProof (panic_wp_any_at CID with "Hpa") as "#Hpw".
    iPoseProof (ut_fmt1_str with "Hkd") as "#Hf1".
    iPoseProof (ut_fmt2_str with "Hkd") as "#Hf2".
    (* the three trap CSR cells, named *)
    iDestruct "Hcsrs" as "(Hsepc & Hscause & Hstval & Hsret & Hres & Hkpt)".
    iDestruct "Hsepc" as (ep) "Hsepc".
    iDestruct "Hscause" as (sc) "Hscause".
    iDestruct "Hstval" as (st) "Hstval".
    (* the pid quarter, out of the process block *)
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    iDestruct (proc_priv_pid with "Hpv") as "(Hpid & Hpidback)".
    iPoseProof (uti_056 with "Htext") as "Hi56".
    iPoseProof (uti_05a with "Htext") as "Hi5a".
    iPoseProof (uti_05c with "Htext") as "Hi5c".
    iPoseProof (uti_060 with "Htext") as "Hi60".
    iPoseProof (uti_064 with "Htext") as "Hi64".
    iPoseProof (uti_068 with "Htext") as "Hi68".
    iPoseProof (uti_06c with "Htext") as "Hi6c".
    iPoseProof (uti_070 with "Htext") as "Hi70".
    iPoseProof (uti_074 with "Htext") as "Hi74".
    iPoseProof (uti_078 with "Htext") as "Hi78".
    iPoseProof (uti_07c with "Htext") as "Hi7c".
    iPoseProof (uti_07e with "Htext") as "Hi7e".
    iPoseProof (uti_082 with "Htext") as "Hi82".
    (* ---- +0x56: csrr a1,scause ---- *)
    iApply (wp_csrr_scause_s_sconf (mword_of_int (UT + 0x56)) Ra1 m nx
              (DfracOwn 1) sc ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hscause Hpc Hi56 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hscause Hpc".
    set (M1 := <[Regidx Ra1 := regval_into_reg sc]> m).
    change (<[Regidx Ra1 := regval_into_reg sc]> m) with M1.
    assert (Hp5a : add_vec_int (mword_of_int (UT + 0x56) : mword 64) 4
                   = mword_of_int (UT + 0x5a)) by pcw.
    iEval (rewrite Hp5a) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    (* ---- +0x5a: lw a2,48(s1) -- p->pid ---- *)
    assert (Haddrpid : add_vec (rget M1 Rs1)
                         (sign_extend' 64 (mword_of_int 48 : mword 12))
                       = p_pid (un_pj N))
      by (rgne; rewrite HM1s1; reflexivity).
    iEval (rewrite -Haddrpid) in "Hpid".
    iApply (wp_clw_s_sconf (mword_of_int (UT + 0x5a)) Ra2 Rs1
              (mword_of_int 48 : mword 12) M1 nx (un_pid N) false
              (dqm := DfracOwn (1/4))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a Hpid [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpid".
    iEval (rewrite Haddrpid) in "Hpid".
    iDestruct ("Hpidback" with "Hpid") as "Hpv".
    set (M2 := <[Regidx Ra2 := regval_into_reg
                   (sign_extend' 64 (un_pid N))]> M1).
    change (<[Regidx Ra2 := regval_into_reg
               (sign_extend' 64 (un_pid N))]> M1) with M2.
    assert (Hp5c : add_vec_int (mword_of_int (UT + 0x5a) : mword 64) 2
                   = mword_of_int (UT + 0x5c)) by pcw.
    iEval (rewrite Hp5c) in "Hpc".
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    assert (HM2s1 : M2 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M2 upd_ne; [exact HM1s1 | reg_neq]).
    assert (HcsM2 : ut_cs m0 M2)
      by (rewrite /M2; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsM1]).
    (* ---- +0x5c .. +0x60: a0 := ut_fmt1_p ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (UT + 0x5c)) Ra0
              (mword_of_int 5 : mword 20) M2 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M3 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (mword_of_int (UT + 0x5c) : mword 64)
                      (auipc_off (mword_of_int 5 : mword 20)))]> M2).
    change (<[Regidx Ra0 := regval_into_reg
               (add_vec (mword_of_int (UT + 0x5c) : mword 64)
                  (auipc_off (mword_of_int 5 : mword 20)))]> M2) with M3.
    assert (Hp60 : add_vec_int (mword_of_int (UT + 0x5c) : mword 64) 4
                   = mword_of_int (UT + 0x60)) by pcw.
    iEval (rewrite Hp60) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (UT + 0x60)) Ra0 Ra0
              (mword_of_int 3262 : mword 12) M3 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (rget M3 Ra0)
                      (sign_extend' 64 (mword_of_int 3262 : mword 12)))]> M3).
    change (<[Regidx Ra0 := regval_into_reg
               (add_vec (rget M3 Ra0)
                  (sign_extend' 64 (mword_of_int 3262 : mword 12)))]> M3) with M4.
    assert (Hp64 : add_vec_int (mword_of_int (UT + 0x60) : mword 64) 4
                   = mword_of_int (UT + 0x64)) by pcw.
    iEval (rewrite Hp64) in "Hpc".
    assert (HM4a0 : M4 !!! Regidx Ra0 = ut_fmt1_p).
    { rewrite /M4 upd_eq. rewrite (rget_ne (CID := CID) M3 Ra0 ltac:(reg_neq)).
      rewrite /M3 upd_eq. unfold ut_fmt1_p, ut_fmt1_a. pcw. }
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk ksp 4).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      exact HM2sp. }
    assert (HM4s1 : M4 !!! Regidx Rs1 = un_pj N).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      exact HM2s1. }
    assert (HcsM4 : ut_cs m0 M4).
    { rewrite /M4 /M3.
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity | exact HcsM2]. }
    (* ---- +0x64: jal printk (call one) ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0x64)) Rra
              (mword_of_int 2088712 : mword 21) M4 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi64 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0x64) : mword 64) 4)]> M4).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0x64) : mword 64) 4)]> M4)
      with M5.
    assert (Hpk1 : add_vec (mword_of_int (UT + 0x64) : mword 64)
                     (sign_extend' 64 (mword_of_int 2088712 : mword 21))
                   = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Hpk1) in "Hpc".
    assert (HM5a0 : M5 !!! Regidx Ra0 = ut_fmt1_p)
      by (rewrite /M5 upd_ne; [exact HM4a0 | reg_neq]).
    assert (HM5ra : M5 !!! Regidx Rra = mword_of_int (UT + 0x68))
      by (rewrite /M5 upd_eq; pcw).
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M5 upd_ne; [exact HM4sp | reg_neq]).
    assert (HM5s1 : M5 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M5 upd_ne; [exact HM4s1 | reg_neq]).
    assert (HcsM5 : ut_cs m0 M5)
      by (rewrite /M5; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsM4]).
    iApply (Hpk CID M5 nx false (un_pj N) C DfracDiscarded ut_fmt1
              ut_fmt1_descs false lks ltac:(lia) ut_fmt1_len ut_fmt1_nonul
              ut_fmt1_kinds ut_fmt1_ndescs
              with "Hcg Htext Hkd Hpc Hpw Hcpu Hpenv [Hf1] []").
    all: try lkbelow.
    { rewrite HM5a0. iExact "Hf1". }
    { iApply ut_fmt1_descs_res. }
    iApply wp_next_off_intro. iIntros (P1) "Hcg Hpc %HcsP1 Hcpu _ _".
    destruct HcsP1 as [HcsP1 HraP1].
    assert (Hret68 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (UT + 0x68))
      by (rewrite HM5ra; pcw).
    iEval (rewrite Hret68) in "Hpc".
    assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup HcsP1 csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HM5sp).
    assert (HP1s1 : P1 !!! Regidx Rs1 = un_pj N)
      by (rewrite (callee_saved_lookup HcsP1 Rs1
                     ltac:(vm_compute; reflexivity)); exact HM5s1).
    assert (HcsP1' : ut_cs m0 P1)
      by exact (ut_cs_trans m0 M5 P1 HcsM5 (ut_cs_of_callee_saved _ _ HcsP1)).
    (* ---- +0x68: csrr a1,sepc ---- *)
    iApply (wp_csrr_sepc_s_sconf (mword_of_int (UT + 0x68)) Ra1 P1 nx
              (DfracOwn 1) ep ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hsepc Hpc Hi68 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hsepc Hpc".
    set (M6 := <[Regidx Ra1 := regval_into_reg (mepc_val ep)]> P1).
    change (<[Regidx Ra1 := regval_into_reg (mepc_val ep)]> P1) with M6.
    assert (Hp6c : add_vec_int (mword_of_int (UT + 0x68) : mword 64) 4
                   = mword_of_int (UT + 0x6c)) by pcw.
    iEval (rewrite Hp6c) in "Hpc".
    (* ---- +0x6c: csrr a2,stval ---- *)
    iApply (wp_csrr_stval_s_sconf (mword_of_int (UT + 0x6c)) Ra2 M6 nx
              (DfracOwn 1) st ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hstval Hpc Hi6c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hstval Hpc".
    set (M7 := <[Regidx Ra2 := regval_into_reg st]> M6).
    change (<[Regidx Ra2 := regval_into_reg st]> M6) with M7.
    assert (Hp70 : add_vec_int (mword_of_int (UT + 0x6c) : mword 64) 4
                   = mword_of_int (UT + 0x70)) by pcw.
    iEval (rewrite Hp70) in "Hpc".
    (* ---- +0x70 .. +0x74: a0 := ut_fmt2_p ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (UT + 0x70)) Ra0
              (mword_of_int 5 : mword 20) M7 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M8 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (mword_of_int (UT + 0x70) : mword 64)
                      (auipc_off (mword_of_int 5 : mword 20)))]> M7).
    change (<[Regidx Ra0 := regval_into_reg
               (add_vec (mword_of_int (UT + 0x70) : mword 64)
                  (auipc_off (mword_of_int 5 : mword 20)))]> M7) with M8.
    assert (Hp74 : add_vec_int (mword_of_int (UT + 0x70) : mword 64) 4
                   = mword_of_int (UT + 0x74)) by pcw.
    iEval (rewrite Hp74) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (UT + 0x74)) Ra0 Ra0
              (mword_of_int 3290 : mword 12) M8 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M9 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (rget M8 Ra0)
                      (sign_extend' 64 (mword_of_int 3290 : mword 12)))]> M8).
    change (<[Regidx Ra0 := regval_into_reg
               (add_vec (rget M8 Ra0)
                  (sign_extend' 64 (mword_of_int 3290 : mword 12)))]> M8) with M9.
    assert (Hp78 : add_vec_int (mword_of_int (UT + 0x74) : mword 64) 4
                   = mword_of_int (UT + 0x78)) by pcw.
    iEval (rewrite Hp78) in "Hpc".
    assert (HM9a0 : M9 !!! Regidx Ra0 = ut_fmt2_p).
    { rewrite /M9 upd_eq. rewrite (rget_ne (CID := CID) M8 Ra0 ltac:(reg_neq)).
      rewrite /M8 upd_eq. unfold ut_fmt2_p, ut_fmt2_a. pcw. }
    (* ---- +0x78: jal printk (call two) ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0x78)) Rra
              (mword_of_int 2088692 : mword 21) M9 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi78 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (MA := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0x78) : mword 64) 4)]> M9).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0x78) : mword 64) 4)]> M9)
      with MA.
    assert (Hpk2 : add_vec (mword_of_int (UT + 0x78) : mword 64)
                     (sign_extend' 64 (mword_of_int 2088692 : mword 21))
                   = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Hpk2) in "Hpc".
    assert (HMAa0 : MA !!! Regidx Ra0 = ut_fmt2_p)
      by (rewrite /MA upd_ne; [exact HM9a0 | reg_neq]).
    assert (HMAra : MA !!! Regidx Rra = mword_of_int (UT + 0x7c))
      by (rewrite /MA upd_eq; pcw).
    assert (HMAsp : MA !!! Regidx csp_rs1 = pa_stk ksp 4).
    { rewrite /MA upd_ne; [| reg_neq]. rewrite /M9 upd_ne; [| reg_neq].
      rewrite /M8 upd_ne; [| reg_neq]. rewrite /M7 upd_ne; [| reg_neq].
      rewrite /M6 upd_ne; [| reg_neq]. exact HP1sp. }
    assert (HMAs1 : MA !!! Regidx Rs1 = un_pj N).
    { rewrite /MA upd_ne; [| reg_neq]. rewrite /M9 upd_ne; [| reg_neq].
      rewrite /M8 upd_ne; [| reg_neq]. rewrite /M7 upd_ne; [| reg_neq].
      rewrite /M6 upd_ne; [| reg_neq]. exact HP1s1. }
    assert (HcsMA : ut_cs m0 MA).
    { rewrite /MA /M9 /M8 /M7 /M6.
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity | exact HcsP1']. }
    iApply (Hpk CID MA nx false (un_pj N) C DfracDiscarded ut_fmt2
              ut_fmt2_descs false lks ltac:(lia) ut_fmt2_len ut_fmt2_nonul
              ut_fmt2_kinds ut_fmt2_ndescs
              with "Hcg Htext Hkd Hpc Hpw Hcpu Hpenv [Hf2] []").
    all: try lkbelow.
    { rewrite HMAa0. iExact "Hf2". }
    { iApply ut_fmt2_descs_res. }
    iApply wp_next_off_intro. iIntros (P2) "Hcg Hpc %HcsP2 Hcpu _ _".
    destruct HcsP2 as [HcsP2 HraP2].
    assert (Hret7c : ret_pc (MA !!! Regidx Rra) = mword_of_int (UT + 0x7c))
      by (rewrite HMAra; pcw).
    iEval (rewrite Hret7c) in "Hpc".
    assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup HcsP2 csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HMAsp).
    assert (HP2s1 : P2 !!! Regidx Rs1 = un_pj N)
      by (rewrite (callee_saved_lookup HcsP2 Rs1
                     ltac:(vm_compute; reflexivity)); exact HMAs1).
    assert (HcsP2' : ut_cs m0 P2)
      by exact (ut_cs_trans m0 MA P2 HcsMA (ut_cs_of_callee_saved _ _ HcsP2)).
    (* ---- +0x7c: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (UT + 0x7c)) Ra0 Rs1 P2 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (MB := <[Regidx Ra0 := regval_into_reg
                   (add_vec zero_reg (rget P2 Rs1))]> P2).
    change (<[Regidx Ra0 := regval_into_reg
               (add_vec zero_reg (rget P2 Rs1))]> P2) with MB.
    assert (Hp7e : add_vec_int (mword_of_int (UT + 0x7c) : mword 64) 2
                   = mword_of_int (UT + 0x7e)) by pcw.
    iEval (rewrite Hp7e) in "Hpc".
    assert (HMBa0 : MB !!! Regidx Ra0 = proc_addr (un_j N)).
    { rewrite /MB upd_eq. rewrite (rget_ne (CID := CID) P2 Rs1 ltac:(reg_neq)).
      rewrite HP2s1 add_vec_zero_l. reflexivity. }
    assert (HMBsp : MB !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /MB upd_ne; [exact HP2sp | reg_neq]).
    assert (HMBs1 : MB !!! Regidx Rs1 = un_pj N)
      by (rewrite /MB upd_ne; [exact HP2s1 | reg_neq]).
    assert (HcsMB : ut_cs m0 MB)
      by (rewrite /MB; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsP2']).
    (* ---- +0x7e: jal setkilled ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0x7e)) Rra
              (mword_of_int 2095876 : mword 21) MB nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi7e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (MC := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0x7e) : mword 64) 4)]> MB).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0x7e) : mword 64) 4)]> MB)
      with MC.
    assert (Hsk : add_vec (mword_of_int (UT + 0x7e) : mword 64)
                    (sign_extend' 64 (mword_of_int 2095876 : mword 21))
                  = mword_of_int KernelSyms.setkilled) by pcw.
    iEval (rewrite Hsk) in "Hpc".
    assert (HMCa0 : MC !!! Regidx Ra0 = proc_addr (un_j N))
      by (rewrite /MC upd_ne; [exact HMBa0 | reg_neq]).
    assert (HMCra : MC !!! Regidx Rra = mword_of_int (UT + 0x82))
      by (rewrite /MC upd_eq; pcw).
    assert (HMCsp : MC !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /MC upd_ne; [exact HMBsp | reg_neq]).
    assert (HMCs1 : MC !!! Regidx Rs1 = un_pj N)
      by (rewrite /MC upd_ne; [exact HMBs1 | reg_neq]).
    assert (HcsMC : ut_cs m0 MC)
      by (rewrite /MC; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsMB]).
    iApply (SK.wp_setkilled_sconf (un_s N) (un_j N) (un_l N) MC nx 0%nat false
              (un_pj N) C false lks HMCa0 Hj Hjl ltac:(vm_compute; reflexivity)
              ltac:(lia) with "Hcg Hcpu Htext Hpc Hpi Hpa [-]").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (S1) "%HcsS1 Hcg Hcpu Hpc".
    assert (Hret82 : ret_pc (MC !!! Regidx Rra) = mword_of_int (UT + 0x82))
      by (rewrite HMCra; pcw).
    iEval (rewrite Hret82) in "Hpc".
    assert (HS1sp : S1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup HcsS1 csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HMCsp).
    assert (HS1s1 : S1 !!! Regidx Rs1 = un_pj N)
      by (rewrite (callee_saved_lookup HcsS1 Rs1
                     ltac:(vm_compute; reflexivity)); exact HMCs1).
    assert (HcsS1' : ut_cs m0 S1)
      by exact (ut_cs_trans m0 MC S1 HcsMC (ut_cs_of_callee_saved _ _ HcsS1)).
    (* ---- +0x82: c.j +0xa6 ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (UT + 0x82))
              (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")))
              S1 nx false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi82 [-]").
    iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
    assert (Hpa6 : add_vec (mword_of_int (UT + 0x82) : mword 64)
                     (sign_extend' 64 (sign_extend' 21
                        (concat_vec (mword_of_int 18 : mword 11) ('b"0"))))
                   = mword_of_int (UT + 0xa6)) by pcw.
    iEval (rewrite Hpa6) in "Hpc".
    (* ---- the bundle back together, and on to +0xa6 ---- *)
    iDestruct ("Hownback" $! V with "Hpv Hsy") as "Hown".
    iApply (T.ut_a6 Rsys N V pt ksp m0 S1 av nx C false
              mie_v menvcfg0 lks
              Hwf' Hav Hnx Htfpe Hksp Hm0sp HS1sp HS1s1 HcsS1'
              Hmiev Hmenvv
              with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
    all: try lkbelow.
    iApply (ua_hold_on Rsys N V C with "Hcpu [-Hclm Hown] Hclm [-]").
    - rewrite /trap_csrs.
      iSplitL "Hsepc"; [iExists ep; iExact "Hsepc"|].
      iSplitL "Hscause"; [iExists sc; iExact "Hscause"|].
      iSplitL "Hstval"; [iExists st; iExact "Hstval"|].
      iSplitL "Hsret"; [iExact "Hsret"|].
      iSplitL "Hres"; [iExact "Hres"|]. iExact "Hkpt".
    - rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End Ut56.


Section UtD0.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* +0xd0 .. +0xe8: THE VMFAULT ARM.                                      *)
  (* ==================================================================== *)
  (*   vmfault(p->pagetable, p->sz, r_stval(), (r_scause() == 13) ? 1 : 0)
       bnez a0 -> +0xa6   else   j +0x56

     THE psz BUMP MADE THIS BLOCK SIMPLER, WHICH IS THE POINT OF THE BUMP.
     vmfault no longer conflates the table it is handed with the running
     process's, so it takes the size as an ARGUMENT and no longer reads
     [p->sz] or [p->pagetable] itself: both cells left its contract, and with
     them both dfracs.  The cost is one instruction here -- the [ld a1,72(s1)]
     at +0xde -- and the gain is that the two cells never leave this block.
     It still opens [ProcInv.proc_priv_copy], because it has to READ them.

     The [addi a3,a3,-13] / [seqz a3,a3] pair is the ternary, and vmfault does
     not read a3 in any way this contract can see -- [SpecVmfault] takes the
     table, the size and the fault address (out of a2) -- so the read flag is
     stepped and never mentioned again.  The BRANCH is what the disjunction in
     vmfault's post decides: the left arm returns 0 and leaves [proc_pt P]
     alone, so the [bnez] falls through and the code joins the
     unexpected-scause arm; the right arm returns the backed page, so it is
     taken and the code joins +0xa6 -- with the process record MOVED. *)
  Lemma ut_d0 (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (C : iProp Σ)
      (mie_v menvcfg0 : mword 64) (lks : gset string) :
    printk_gen_contract (un_pr N) (un_u N) (un_v N) ->
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res false + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xd0)) -∗
    sie_cap_gpr m nx false (un_pj N) -∗
    ut_hold Rsys N V C false lks -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpk Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv.
    pose proof (ut_nx_bound false av nx Hav Hnx) as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hcont".
    iDestruct (ua_hold_off Rsys N V C with "Hhold") as
      "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    (* depth 0 forces the held set empty, so the printk / killed / setkilled
       order premises need no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    iAssert (kalloc_env (un_kl N) None) with "[]" as "#Hkenv".
    { iApply (ut_caps_kalloc N with "Hcaps"). }
    iDestruct "Hcsrs" as "(Hsepc & Hscause & Hstval & Hsret & Hres & Hkpt)".
    iDestruct "Hscause" as (sc) "Hscause".
    iDestruct "Hstval" as (st) "Hstval".
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hsy & Hownback)".
    iDestruct (proc_priv_sz_bound with "Hpv") as %Hszb.
    iDestruct (proc_priv_copy with "Hpv") as "(Hsz & Hpgt & Hppt & Hpvback)".
    iPoseProof (uti_0d0 with "Htext") as "Hid0".
    iPoseProof (uti_0d4 with "Htext") as "Hid4".
    iPoseProof (uti_0d8 with "Htext") as "Hid8".
    iPoseProof (uti_0da with "Htext") as "Hida".
    iPoseProof (uti_0de with "Htext") as "Hide".
    iPoseProof (uti_0e0 with "Htext") as "Hie0".
    iPoseProof (uti_0e2 with "Htext") as "Hie2".
    iPoseProof (uti_0e6 with "Htext") as "Hie6".
    (* ---- +0xd0: csrr a2,stval ---- *)
    iApply (wp_csrr_stval_s_sconf (mword_of_int (UT + 0xd0)) Ra2 m nx
              (DfracOwn 1) st ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hstval Hpc Hid0 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hstval Hpc".
    set (M1 := <[Regidx Ra2 := regval_into_reg st]> m).
    change (<[Regidx Ra2 := regval_into_reg st]> m) with M1.
    assert (Hpd4 : add_vec_int (mword_of_int (UT + 0xd0) : mword 64) 4
                   = mword_of_int (UT + 0xd4)) by pcw.
    iEval (rewrite Hpd4) in "Hpc".
    (* ---- +0xd4: csrr a3,scause ---- *)
    iApply (wp_csrr_scause_s_sconf (mword_of_int (UT + 0xd4)) Ra3 M1 nx
              (DfracOwn 1) sc ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hscause Hpc Hid4 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hscause Hpc".
    set (M2 := <[Regidx Ra3 := regval_into_reg sc]> M1).
    change (<[Regidx Ra3 := regval_into_reg sc]> M1) with M2.
    assert (Hpd8 : add_vec_int (mword_of_int (UT + 0xd4) : mword 64) 4
                   = mword_of_int (UT + 0xd8)) by pcw.
    iEval (rewrite Hpd8) in "Hpc".
    (* ---- +0xd8: c.addi a3,a3,-13 ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (UT + 0xd8)) Ra3
              (mword_of_int 51 : mword 6) M2 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hid8 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M3 := <[Regidx Ra3 := regval_into_reg
                   (add_vec (rget M2 Ra3)
                      (sign_extend' 64
                         (sign_extend' 12 (mword_of_int 51 : mword 6))))]> M2).
    change (<[Regidx Ra3 := regval_into_reg
               (add_vec (rget M2 Ra3)
                  (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 51 : mword 6))))]> M2)
      with M3.
    assert (Hpda : add_vec_int (mword_of_int (UT + 0xd8) : mword 64) 2
                   = mword_of_int (UT + 0xda)) by pcw.
    iEval (rewrite Hpda) in "Hpc".
    (* ---- +0xda: seqz a3,a3 (sltiu a3,a3,1) ---- *)
    iApply (wp_sltiu_s_sconf (mword_of_int (UT + 0xda)) Ra3 Ra3
              (mword_of_int 1 : mword 12)
              (zero_extend' 64 (bool_to_bit
                 (zopz0zI_u (rget M3 Ra3)
                    (sign_extend' 64 (mword_of_int 1 : mword 12)))))
              M3 nx false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hida [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M4 := <[Regidx Ra3 := regval_into_reg
                   (zero_extend' 64 (bool_to_bit
                      (zopz0zI_u (rget M3 Ra3)
                         (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> M3).
    change (<[Regidx Ra3 := regval_into_reg
               (zero_extend' 64 (bool_to_bit
                  (zopz0zI_u (rget M3 Ra3)
                     (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> M3)
      with M4.
    assert (Hpde : add_vec_int (mword_of_int (UT + 0xda) : mword 64) 4
                   = mword_of_int (UT + 0xde)) by pcw.
    iEval (rewrite Hpde) in "Hpc".
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk ksp 4).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [| reg_neq].
      exact Hmsp. }
    assert (HM4s1 : M4 !!! Regidx Rs1 = un_pj N).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [| reg_neq].
      exact Hms1. }
    assert (HM4a2 : M4 !!! Regidx Ra2 = st).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_eq. reflexivity. }
    assert (HcsM4 : ut_cs m0 M4).
    { rewrite /M4 /M3 /M2 /M1.
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]. }
    (* ---- +0xde: ld a1,72(s1) -- p->sz, vmfault's psz argument ---- *)
    (* THE ONE INSTRUCTION THE psz BUMP ADDED.  vmfault no longer reads
       [p->sz] itself, so it no longer takes the cell -- the caller reads it
       and passes the value.  The cell therefore never leaves this block:
       [proc_priv_copy] hands it out, the [c.ld] reads it, and [Hpvback]
       takes it straight back below. *)
    assert (Haddrsz : add_vec (rget M4 Rs1)
                        (sign_extend' 64 (mword_of_int 72 : mword 12))
                      = p_sz (un_pj N))
      by (rgne; rewrite HM4s1; reflexivity).
    iEval (rewrite -Haddrsz) in "Hsz".
    iApply (wp_cld_s_sconf (mword_of_int (UT + 0xde)) Ra1 Rs1
              (mword_of_int 72 : mword 12) M4 nx (pv_sz V) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hide Hsz [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hsz".
    iEval (rewrite Haddrsz) in "Hsz".
    set (M5 := <[Regidx Ra1 := regval_into_reg (pv_sz V)]> M4).
    change (<[Regidx Ra1 := regval_into_reg (pv_sz V)]> M4) with M5.
    assert (Hpe0 : add_vec_int (mword_of_int (UT + 0xde) : mword 64) 2
                   = mword_of_int (UT + 0xe0)) by pcw.
    iEval (rewrite Hpe0) in "Hpc".
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M5 upd_ne; [exact HM4sp | reg_neq]).
    assert (HM5s1 : M5 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M5 upd_ne; [exact HM4s1 | reg_neq]).
    assert (HM5a2 : M5 !!! Regidx Ra2 = st)
      by (rewrite /M5 upd_ne; [exact HM4a2 | reg_neq]).
    assert (HcsM5 : ut_cs m0 M5)
      by (rewrite /M5; apply ut_cs_insert;
          [vm_compute; reflexivity | exact HcsM4]).
    (* ---- +0xe0: ld a0,80(s1) -- p->pagetable ---- *)
    assert (Haddrpg : add_vec (rget M5 Rs1)
                        (sign_extend' 64 (mword_of_int 80 : mword 12))
                      = p_pagetable (un_pj N))
      by (rgne; rewrite HM5s1; reflexivity).
    iEval (rewrite -Haddrpg) in "Hpgt".
    iApply (wp_cld_s_sconf (mword_of_int (UT + 0xe0)) Ra0 Rs1
              (mword_of_int 80 : mword 12) M5 nx
              (page_base (ud_root (pv_upt V))) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie0 Hpgt [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpgt".
    iEval (rewrite Haddrpg) in "Hpgt".
    set (M6 := <[Regidx Ra0 := regval_into_reg
                   (page_base (ud_root (pv_upt V)))]> M5).
    change (<[Regidx Ra0 := regval_into_reg
               (page_base (ud_root (pv_upt V)))]> M5) with M6.
    assert (Hpe2 : add_vec_int (mword_of_int (UT + 0xe0) : mword 64) 2
                   = mword_of_int (UT + 0xe2)) by pcw.
    iEval (rewrite Hpe2) in "Hpc".
    (* ---- +0xe2: jal vmfault ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0xe2)) Rra
              (mword_of_int 2092576 : mword 21) M6 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hie2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M7 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0xe2) : mword 64) 4)]> M6).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0xe2) : mword 64) 4)]> M6)
      with M7.
    assert (Hvf : add_vec (mword_of_int (UT + 0xe2) : mword 64)
                    (sign_extend' 64 (mword_of_int 2092576 : mword 21))
                  = mword_of_int KernelSyms.vmfault) by pcw.
    iEval (rewrite Hvf) in "Hpc".
    assert (HM7a0 : M7 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
    { rewrite /M7 upd_ne; [| reg_neq]. rewrite /M6 upd_eq. reflexivity. }
    assert (HM7a1 : M7 !!! Regidx Ra1 = pv_sz V).
    { rewrite /M7 upd_ne; [| reg_neq]. rewrite /M6 upd_ne; [| reg_neq].
      rewrite /M5 upd_eq. reflexivity. }
    assert (HM7a2 : M7 !!! Regidx Ra2 = st).
    { rewrite /M7 upd_ne; [| reg_neq]. rewrite /M6 upd_ne; [| reg_neq].
      exact HM5a2. }
    assert (HM7ra : M7 !!! Regidx Rra = mword_of_int (UT + 0xe6))
      by (rewrite /M7 upd_eq; pcw).
    assert (HM7sp : M7 !!! Regidx csp_rs1 = pa_stk ksp 4).
    { rewrite /M7 upd_ne; [| reg_neq]. rewrite /M6 upd_ne; [| reg_neq].
      exact HM5sp. }
    assert (HM7s1 : M7 !!! Regidx Rs1 = un_pj N).
    { rewrite /M7 upd_ne; [| reg_neq]. rewrite /M6 upd_ne; [| reg_neq].
      exact HM5s1. }
    assert (HcsM7 : ut_cs m0 M7).
    { rewrite /M7 /M6.
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity | exact HcsM5]. }
    (* THE PIN, which is all [VMFAULT]'s un-shed raw-map premise costs -- the
       one premise the psz bump did NOT shed. *)
    assert (HP7a0 : tp_pin M7 !!! Regidx Ra0
                    = page_base (ud_root (pv_upt V)))
      by (rewrite (ua_pin_lookup M7 Ra0 ltac:(reg_neq)); exact HM7a0).
    assert (HP7a1 : tp_pin M7 !!! Regidx Ra1 = pv_sz V)
      by (rewrite (ua_pin_lookup M7 Ra1 ltac:(reg_neq)); exact HM7a1).
    assert (HP7a2 : tp_pin M7 !!! Regidx Ra2 = st)
      by (rewrite (ua_pin_lookup M7 Ra2 ltac:(reg_neq)); exact HM7a2).
    assert (HP7ra : tp_pin M7 !!! Regidx Rra = mword_of_int (UT + 0xe6))
      by (rewrite (ua_pin_lookup M7 Rra ltac:(reg_neq)); exact HM7ra).
    assert (HP7sp : tp_pin M7 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (ua_pin_lookup M7 csp_rs1 ltac:(reg_neq)); exact HM7sp).
    assert (HP7s1 : tp_pin M7 !!! Regidx Rs1 = un_pj N)
      by (rewrite (ua_pin_lookup M7 Rs1 ltac:(reg_neq)); exact HM7s1).
    assert (HcsP7 : ut_cs m0 (tp_pin M7)) by exact (ua_pin_cs m0 M7 HcsM7).
    iEval (rewrite <- (ua_pin_sie_cap_gpr M7 nx false (un_pj N))) in "Hcg".
    iApply (VM.wp_vmfault_sconf (un_kl N) (tp_pin M7) (pv_upt V) (pv_sz V) nx
              0%nat false (un_pj N) C false lks
              ltac:(lia) (rget_tp M7) HP7a0 HP7a1 Hszb
              ltac:(vm_compute; reflexivity)
              with "Hcg Hcpu Htext Hpc Hppt Hkenv [-]").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mr) "Hcg Hcpu Hpc %Hvfcs Hvfpay".
    assert (Hrete6 : ret_pc (tp_pin M7 !!! Regidx Rra)
                     = mword_of_int (UT + 0xe6))
      by (rewrite HP7ra; pcw).
    iEval (rewrite Hrete6) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup Hvfcs csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HP7sp).
    assert (Hmrs1 : mr !!! Regidx Rs1 = un_pj N)
      by (rewrite (callee_saved_lookup Hvfcs Rs1
                     ltac:(vm_compute; reflexivity)); exact HP7s1).
    assert (Hcsmr : ut_cs m0 mr)
      by exact (ut_cs_trans m0 (tp_pin M7) mr HcsP7
                  (ut_cs_of_callee_saved _ _ Hvfcs)).
    (* the trap CSR bundle, closed: nothing below reads a cell. *)
    iAssert (trap_csrs) with "[Hsepc Hscause Hstval Hsret Hres Hkpt]"
      as "Hcsrs".
    { rewrite /trap_csrs.
      iSplitL "Hsepc"; [iExact "Hsepc"|].
      iSplitL "Hscause"; [iExists sc; iExact "Hscause"|].
      iSplitL "Hstval"; [iExists st; iExact "Hstval"|].
      iSplitL "Hsret"; [iExact "Hsret"|].
      iSplitL "Hres"; [iExact "Hres"|]. iExact "Hkpt". }
    iDestruct "Hvfpay" as "[(%Hvz & Hppt) | Hvs]".
    - (* ---- vmfault declined: the [bnez] falls through, then c.j +0x56 ---- *)
      iPoseProof (uti_0e8 with "Htext") as "Hie8".
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (UT + 0xe6))
                (mword_of_int 224 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mr nx false ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hvz; vm_compute; reflexivity)
                with "Hcg Hpc Hie6 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpe8 : add_vec_int (mword_of_int (UT + 0xe6) : mword 64) 2
                     = mword_of_int (UT + 0xe8)) by pcw.
      iEval (rewrite Hpe8) in "Hpc".
      iApply (wp_cj_s_sconf (mword_of_int (UT + 0xe8))
                (sign_extend' 21
                   (concat_vec (mword_of_int 1975 : mword 11) ('b"0")))
                mr nx false ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hie8 [-]").
      iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
      assert (Hp56 : add_vec (mword_of_int (UT + 0xe8) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1975 : mword 11) ('b"0"))))
                     = mword_of_int (UT + 0x56)) by pcw.
      iEval (rewrite Hp56) in "Hpc".
      iDestruct ("Hpvback" $! (pv_upt V) ltac:(apply uptd_ext_sz_refl)
                   with "Hsz Hpgt Hppt") as "Hpv".
      rewrite upd_upt_id.
      iDestruct ("Hownback" $! V with "Hpv Hsy") as "Hown".
      iApply (ut_56 Rsys N V pt ksp m0 mr av nx C
                mie_v menvcfg0 lks
                Hpk Hwf' Hav Hnx Htfpe Hksp Hm0sp Hmrsp Hmrs1 Hcsmr
                Hmiev Hmenvv
                with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
      iApply (ua_hold_on Rsys N V C with "Hcpu Hcsrs Hclm [-]").
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
    - (* ---- vmfault backed a page: the [bnez] is taken, to +0xa6 ---- *)
      iDestruct "Hvs" as (r) "(%Hra0 & %Hrpv & %Hszlt & %Hunone & Hppt)".
      assert (Hrnz : mr !!! Regidx Ra0 <> zero_reg).
      { rewrite Hra0. intro Hc. apply (page_valid_ne_null r Hrpv).
        rewrite Hc. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (UT + 0xe6))
                (mword_of_int 224 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mr nx false ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rgne; unfold neq_vec;
                      rewrite (proj2 (eq_vec_false_iff _ _) Hrnz); reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hie6 [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpa6 : add_vec (mword_of_int (UT + 0xe6) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 224 : mword 8) ('b"0"))))
                     = mword_of_int (UT + 0xa6)) by pcw.
      iEval (rewrite Hpa6) in "Hpc".
      (* THE DESCRIPTOR GREW, so the record moves -- and [uptd_insert] keeps
         [ud_tfp], so [ut_a6]'s premise is a projection. *)
      set (Pd := uptd_insert (pv_upt V)
                   (svpn_of (and_vec (tp_pin M7 !!! Regidx Ra2)
                               (mword_of_int (-4096)))) r).
      change (uptd_insert (pv_upt V)
                (svpn_of (and_vec (tp_pin M7 !!! Regidx Ra2)
                            (mword_of_int (-4096)))) r) with Pd.
      assert (Hextd : uptd_ext_sz (pv_sz V) (pv_upt V) Pd).
      { rewrite /Pd. apply uptd_ext_sz_insert; [exact Hunone |].
        apply svpn_of_pgd_below.
        - rewrite -uint_unsigned. exact Hszb.
        - rewrite -!uint_unsigned. exact Hszlt. }
      iDestruct ("Hpvback" $! Pd Hextd with "Hsz Hpgt Hppt") as "Hpv".
      set (V' := upd_upt V Pd).
      change (upd_upt V Pd) with V'.
      assert (HV'tfp : ud_tfp (pv_upt V') = ud_tfp pt).
      { rewrite /V' /Pd. exact Htfpe. }
      iDestruct ("Hownback" $! V' with "Hpv Hsy") as "Hown".
      iApply (T.ut_a6 Rsys N V' pt ksp m0 mr av nx C false
                mie_v menvcfg0 lks
                Hwf' Hav Hnx HV'tfp Hksp Hm0sp Hmrsp Hmrs1 Hcsmr
                Hmiev Hmenvv
                with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
      all: try lkbelow.
      iApply (ua_hold_on Rsys N V' C with "Hcpu Hcsrs Hclm [-]").
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtD0.


Section UtE8.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (Rsys : gname -> mword 64 -> iProp Σ).

  (* ==================================================================== *)
  (* +0xea .. +0xf2: THE DEVICE ARM'S killed CHECK.                        *)
  (* ==================================================================== *)
  (*   if (killed(p)) kexit(-1);
       -- beqz taken -> +0xfc (which_dev == 2 ? yield), else j +0xf6

     +0xf6 is INSIDE the kexit tail +0xa6's own killed arm falls into
     ([c.li a0,-1; jal kexit]), which is why this block steps those two
     itself rather than jumping into the middle of [ut_a6]: a block lemma is
     entered at its own pc, and +0xf4's [c.li s2,0] -- the only instruction
     that separates the two entries -- is dead in the resource sense anyway
     (kexit never returns).  No premise about s2 is needed here either; it
     was set from devintr's return value at +0x3e and [ut_fa] only branches
     on it. *)
  Lemma ut_e8 (N : ut_names) (V : pprivate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (C : iProp Σ)
      (mie_v menvcfg0 : mword 64) (lks : gset string) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (trap_res false + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt V) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xea)) -∗
    sie_cap_gpr m nx false (un_pj N) -∗
    ut_hold Rsys N V C false lks -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwf Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv.
    pose proof (ut_nx_bound false av nx Hav Hnx) as Hks.
    unfold K_syscall, K_sys_exit, K_kexit in Hks.
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hcont".
    iDestruct (ua_hold_off Rsys N V C with "Hhold") as
      "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    (* depth 0 forces the held set empty, so the printk / killed / setkilled
       order premises need no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    iAssert (procs_inv (un_s N)) with "[]" as "#Hpi".
    { iDestruct "Hcaps" as "($ & _)". }
    iAssert (panic_wp_any) with "[]" as "#Hpa".
    { iDestruct "Hcaps" as "(_ & $ & _)". }
    iPoseProof (uti_0ea with "Htext") as "Hiea".
    iPoseProof (uti_0ec with "Htext") as "Hiec".
    iPoseProof (uti_0f0 with "Htext") as "Hif0".
    (* ---- +0xea: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (UT + 0xea)) Ra0 Rs1 m nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiea [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget m Rs1))]> m).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget m Rs1))]> m)
      with M1.
    assert (Hpec : add_vec_int (mword_of_int (UT + 0xea) : mword 64) 2
                   = mword_of_int (UT + 0xec)) by pcw.
    iEval (rewrite Hpec) in "Hpc".
    assert (HM1a0 : M1 !!! Regidx Ra0 = proc_addr (un_j N)).
    { rewrite /M1 upd_eq. rewrite (rget_ne (CID := CID) m Rs1 ltac:(reg_neq)).
      rewrite Hms1 add_vec_zero_l. reflexivity. }
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    (* ---- +0xec: jal killed ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0xec)) Rra
              (mword_of_int 2095802 : mword 21) M1 nx false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiec [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0xec) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0xec) : mword 64) 4)]> M1)
      with M2.
    assert (Hkilled : add_vec (mword_of_int (UT + 0xec) : mword 64)
                        (sign_extend' 64 (mword_of_int 2095802 : mword 21))
                      = mword_of_int KernelSyms.killed) by pcw.
    iEval (rewrite Hkilled) in "Hpc".
    assert (HM2a0 : M2 !!! Regidx Ra0 = proc_addr (un_j N))
      by (rewrite /M2 upd_ne; [exact HM1a0 | reg_neq]).
    assert (HM2ra : M2 !!! Regidx Rra = mword_of_int (UT + 0xf0))
      by (rewrite /M2 upd_eq; pcw).
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    assert (HM2s1 : M2 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M2 upd_ne; [exact HM1s1 | reg_neq]).
    assert (HcsM2 : ut_cs m0 M2)
      by (rewrite /M2; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsM1]).
    iApply (KI.wp_killed_sconf (un_s N) (un_j N) (un_l N) M2 nx 0%nat false
              (un_pj N) C false lks HM2a0 Hj Hjl ltac:(vm_compute; reflexivity)
              ltac:(lia) with "Hcg Hcpu Htext Hpc Hpi Hpa [-]").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mf kl) "[%Hcskl %Hkla0] Hcg Hcpu Hpc".
    assert (Hretee : ret_pc (M2 !!! Regidx Rra) = mword_of_int (UT + 0xf0))
      by (rewrite HM2ra; pcw).
    iEval (rewrite Hretee) in "Hpc".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite (callee_saved_lookup Hcskl csp_rs1
                     ltac:(vm_compute; reflexivity)); exact HM2sp).
    assert (Hmfs1 : mf !!! Regidx Rs1 = un_pj N)
      by (rewrite (callee_saved_lookup Hcskl Rs1
                     ltac:(vm_compute; reflexivity)); exact HM2s1).
    assert (Hcsmf : ut_cs m0 mf)
      by exact (ut_cs_trans m0 M2 mf HcsM2 (ut_cs_of_callee_saved _ _ Hcskl)).
    assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
      by (vm_compute; reflexivity).
    assert (Hrgmf : rget (CID := CID) mf Ra0 = sign_extend' 64 kl)
      by (rgne; exact Hkla0).
    (* ---- +0xf0: c.beqz a0 ---- *)
    destruct (eq_vec (sign_extend' 64 kl) (zero_reg : mword 64)) eqn:Hz.
    - (* NOT killed: the branch is taken, to +0xfc. *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (UT + 0xf0))
                (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx false Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hif0 [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpfc : add_vec (mword_of_int (UT + 0xf0) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 6 : mword 8) ('b"0"))))
                     = mword_of_int (UT + 0xfc)) by pcw.
      iEval (rewrite Hpfc) in "Hpc".
      iApply (T.ut_fa Rsys N V pt ksp m0 mf av nx C false
                mie_v menvcfg0 lks
                Hwf' Hav Hnx Htfpe Hksp Hm0sp Hmfsp Hmfs1 Hcsmf
                Hmiev Hmenvv
                with "Htext Hpc Hcg [-Hframe Hcont] Hframe Hcont").
      iApply (ua_hold_on Rsys N V C with "Hcpu Hcsrs Hclm [-]").
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
    - (* KILLED: fall through to +0xf2's [c.j +0xf6], then kexit(-1). *)
      iPoseProof (uti_0f2 with "Htext") as "Hif2".
      iPoseProof (uti_0f6 with "Htext") as "Hif6".
      iPoseProof (uti_0f8 with "Htext") as "Hif8".
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (UT + 0xf0))
                (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx false Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hz)
                with "Hcg Hpc Hif0 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpf2 : add_vec_int (mword_of_int (UT + 0xf0) : mword 64) 2
                     = mword_of_int (UT + 0xf2)) by pcw.
      iEval (rewrite Hpf2) in "Hpc".
      (* +0xf2 c.j +0xf6 *)
      iApply (wp_cj_s_sconf (mword_of_int (UT + 0xf2))
                (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")))
                mf nx false ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hif2 [-]").
      iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
      assert (Hpf6 : add_vec (mword_of_int (UT + 0xf2) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 2 : mword 11) ('b"0"))))
                     = mword_of_int (UT + 0xf6)) by pcw.
      iEval (rewrite Hpf6) in "Hpc".
      (* +0xf6 c.li a0,-1 *)
      iApply (wp_cli_s_sconf (mword_of_int (UT + 0xf6)) Ra0
                (mword_of_int 63 : mword 6)
                (add_vec zero_reg (sign_extend' 64
                   (sign_extend' 12 (mword_of_int 63 : mword 6))))
                mf nx false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hif6 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (K1 := <[Regidx Ra0 := regval_into_reg
                     (add_vec zero_reg (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))))]> mf).
      change (<[Regidx Ra0 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))]> mf)
        with K1.
      assert (Hpf8 : add_vec_int (mword_of_int (UT + 0xf6) : mword 64) 2
                     = mword_of_int (UT + 0xf8)) by pcw.
      iEval (rewrite Hpf8) in "Hpc".
      (* +0xf8 jal kexit *)
      iApply (wp_jal_s_sconf (mword_of_int (UT + 0xf8)) Rra
                (mword_of_int 2095486 : mword 21) K1 nx false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif8 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hkex : add_vec (mword_of_int (UT + 0xf8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095486 : mword 21))
                     = mword_of_int KernelSyms.kexit) by pcw.
      iEval (rewrite Hkex) in "Hpc".
      iApply (T.ut_kexit Rsys N V
                (<[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0xf8) : mword 64) 4)]> K1)
                nx C false lks Hwf' ltac:(unfold K_kexit; lia) ltac:(lkbelow)
                with "Htext Hpc Hcg [-]").
      iApply (ua_hold_on Rsys N V C with "Hcpu Hcsrs Hclm [-]").
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtE8.

End UtArms.
