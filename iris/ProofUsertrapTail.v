(* ProofUsertrapTail.v -- usertrap's TAIL: the three blocks every arm ends
   in, plus the exit disassembly.

     +0xa6   if (killed(p)) { which_dev = 0; kexit(-1); }        <- ut_a6
     +0xae   prepare_return();
             uint64 satp = MAKE_SATP(p->pagetable);
             <epilogue>; return satp;                            <- ut_ret
     +0xfc   if (which_dev == 2) yield();  goto +0xae             <- ut_fa

   WHY THIS IS THE FIRST FILE OF THE WALK, and why it is index-GENERIC.
   +0xa6 is reached at [b = true] from the syscall arm (whose [csrsi
   sstatus,2] at +0x9e re-enabled interrupts) and at [b = false] from the
   devintr / vmfault / unexpected-scause arms.  Every callee it reaches is
   already index-generic -- killed, kexit, prepare_return, yield -- so the
   three blocks are proved ONCE over a parameter [b], and the four arms above
   instantiate them.  That is also why [UsertrapRes.ut_hold] exists: at
   [b = true] the trap-CSR set and the running claim live inside [sie_arm]
   and the caller brings [emp], at [b = false] it brings them itself, and
   [trap_csrs_ext] / [cpu_claim_ext] are exactly that difference.

   THE ONE THING THE TAIL HAS TO GET RIGHT IS THE EXIT, and it is not the
   epilogue's four loads.  It is that the machine state prepare_return hands
   back re-assembles [SpecUsertrap]'s boundary: the sret-ready mstatus is
   DERIVED, not arranged ([UsertrapRes.ut_exit_ms_ok]), from the loose SIE
   quarter's agreement with [sconf]'s half and the travelling sret mirror's
   with [sconf]'s tie -- so the two ghost fractions the excursion through user
   mode parks are what makes the return legal.  See UsertrapRes.v's header.

   [mf] IS [tp_pin] OF THE FINAL MAP, which is the cheapest way to meet the
   boundary's [mf !!! tp = cid_word]: usertrap may have MIGRATED, so the tp
   SLOT of the map it has been threading still holds the entry hart's id
   while [gpr_file] holds the pinned one.  Handing over [tp_pin M] makes the
   two agree by construction ([HartTp.tp_pin_id]), and tp is deliberately not
   one of [CalleeSaved.callee_saved]'s thirteen, so nothing else moves. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import PageGeom.
Require Import RegFile HartTp WpNext CpuOwn.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import InstrBytes.
Require Import KernelText KernelRvcDecode.
Require Import WpGprCsrwA.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.        (* [wp_cli_s_sconf] *)
Require Import WpKvminithart.      (* [kvi_satp_word] and its three facts *)
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import WpUart LogInv.
Require Import Xv6Cameras.
Require Import SpecFileclose.
Require Import IrefSlots.
Require Import FdSlots ProcInv.
Require Import SchedCtx.
Require Import SlotGen.   (* [pid_reg] / [qeighth] -- the tie killed() is read at *)
Require Import FileInvDefs.
Require Import CodeUsertrap.
Require Import SpecKilled SpecKexit SpecYield SpecPrepareReturn.
Require Import SpecUsertrap UsertrapRes.
Require Import UsysMemOk.     (* [usys_num] / [uecall_scause] -- the row's guard *)
Require Import SpecSysRead.   (* [sys_rw_count] -- the read's count *)
Require Import UexecRet.      (* [uslot] -- the resume slot the row is stated at *)
Require Import UexecExecInst. (* [spost_at_read_why] -- the receipt's reason *)
Require Import UexecSlot TfUser.   (* [tf_resume_pc] / [ret_pc_idem] / [tf_ueq_epc] *)
Require Import UexecSG.            (* [sfam] -- the deposit's families, which
                                      the syscall channel's out row is at *)
Require Import UserPerm.   (* [perm_of] -- the exec row's entry permission map *)
Require Import ProofUsertrapParts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Require Import TsoCtx.
Require Import ChildTok.  (* [child_tok] -- fork's answer, relayed *)
Local Open Scope Z_scope.
Set Printing Depth 40.

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Module UtTail (PR : PREPARE_RETURN) (KI : KILLED) (KE : KEXIT) (YI : YIELD).

(* register indices and the two scripts, at MODULE level: an [Ltac] defined
   inside a section is discharged over its variables and unusable in the next
   one, and a [Notation] inside a section disappears with it. *)
Notation Rra := (mword_of_int 1  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Ltac pcw := apply bv_eq; vm_compute; reflexivity.


Section ProofUsertrapTail.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  (* the syscall environment, an ordinary hart-free parameter here: the tail
     never touches it, it only hands it on.  See SpecSyscall's note. *)
  Context (Rsys : gname -> mword 64 -> fclose_names -> iProp Σ).


  (* ==================================================================== *)
  (* THE RESIDUE WITHOUT THE INCARNATION'S MARKER (design/pipe.md, “The    *)
  (* exit path”).  A process that kills ITSELF spends the marker founding  *)
  (* <p->lock>'s killed row on its SPENT arm ([SpecSetkilled]'s owed       *)
  (* side), and walks the rest of the trap -- the jump to +0xa6, the       *)
  (* killed check, kexit -- on the block that is left.  kexit is stated at *)
  (* that block anyway ([SpecKexit], [ProcInv.proc_priv_unmarked]), so     *)
  (* every row from setkilled on is stated here and the two shapes differ  *)
  (* by exactly one conjunct.                                             *)
  (* ==================================================================== *)
  Definition ut_own_nm (N : ut_names) (U : ustate) (sts : list fdstate)
      (cs : gset gname) (pid : mword 32) : iProp Σ :=
    (bslots 3 ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{un_dqi N} (un_ip N) ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     proc_priv_unmarked (un_f N) (un_pj N) pid U ∗
     fd_frags (pv_fdg (us_V U)) sts ∗
     ch_frag (pv_chg (us_V U)) (un_pj N) cs ∗
     Rsys (un_f N) (un_pj N) (un_fn N pid))%I.

  Lemma ut_own_unmark (N : ut_names) (U : ustate) (sts : list fdstate)
      (cs : gset gname) (pid : mword 32) :
    ut_own Rsys N U sts cs pid ⊣⊢
    ut_own_nm N U sts cs pid ∗ ChildTok.taken_at (pv_gen (us_V U)).
  Proof using .
    rewrite /ut_own /ut_own_nm (proc_priv_unmark (un_f N) (un_pj N) pid U).
    (* BUILD the bundle rather than framing it: conjunct [E] is
       [proc_priv_unmarked], whose core ends in a 4096-element big-op, so a
       bare [iFrame] searches that goal once per conjunct (2.6s + 1.7s).
       Every row is in hand, so the goal's own order closes it. *)
    iSplit.
    - iIntros "(A & B & C & D & [E Ht] & F & G & H)".
      iSplitR "Ht"; [| iExact "Ht"].
      iSplitL "A"; [iExact "A" |].
      iSplitL "B"; [iExact "B" |].
      iSplitL "C"; [iExact "C" |].
      iSplitL "D"; [iExact "D" |].
      iSplitL "E"; [iExact "E" |].
      iSplitL "F"; [iExact "F" |].
      iSplitL "G"; [iExact "G" | iExact "H"].
    - iIntros "[(A & B & C & D & E & F & G & H) Ht]".
      iSplitL "A"; [iExact "A" |].
      iSplitL "B"; [iExact "B" |].
      iSplitL "C"; [iExact "C" |].
      iSplitL "D"; [iExact "D" |].
      iSplitL "E Ht"; [iSplitL "E"; [iExact "E" | iExact "Ht"] |].
      iSplitL "F"; [iExact "F" |].
      iSplitL "G"; [iExact "G" | iExact "H"].
  Qed.

  Definition ut_hold_nm (N : ut_names) (U : ustate) (b : bool)
      (lks : gset string) (sts : list fdstate) (cs : gset gname)
      (pid : mword 32) : iProp Σ :=
    (cpu_own 0%nat b (un_pj N) b lks ∗
     trap_csrs_ext KT1 b ∗
     cpu_claim_ext b (un_pj N) ∗
     (ut_caps N ∗ ut_own_nm N U sts cs pid))%I.

  (* the live slot's pid is nonzero -- the marker-less block still says so,
     out of the incarnation's two quarters ([SlotGen.gen_halves_at_nz]) *)
  Lemma ut_pid_nz_nm (γf : gname) (pa : mword 64) (pid : mword 32) (U : ustate) :
    proc_priv_unmarked γf pa pid U -∗ ⌜bv_unsigned pid <> 0⌝.
  Proof using . iIntros "(_ & _ & _ & _ & _ & Hgh)". iApply (gen_halves_at_nz with "Hgh"). Qed.

  (* ...and the block out of the marker-less residue, [UsertrapRes.ut_own_priv]
     one conjunct in *)
  Lemma ut_own_nm_priv (N : ut_names) (U : ustate) (sts : list fdstate)
      (cs : gset gname) (pid : mword 32) :
    ut_own_nm N U sts cs pid -∗
    proc_priv_unmarked (un_f N) (un_pj N) pid U ∗
    fd_frags (pv_fdg (us_V U)) sts ∗
    ch_frag (pv_chg (us_V U)) (un_pj N) cs ∗
    Rsys (un_f N) (un_pj N) (un_fn N pid) ∗
    (∀ (U' : ustate) (sts' : list fdstate) (cs' : gset gname),
       proc_priv_unmarked (un_f N) (un_pj N) pid U' -∗
       fd_frags (pv_fdg (us_V U')) sts' -∗
       ch_frag (pv_chg (us_V U')) (un_pj N) cs' -∗
       Rsys (un_f N) (un_pj N) (un_fn N pid) -∗ ut_own_nm N U' sts' cs' pid).
  Proof using .
    iIntros "(Hb & Hip & Hfd & Hir & Hpv & Hfr & Hch & Hsy)".
    iFrame "Hpv Hfr Hch Hsy". iIntros (U' sts' cs') "Hpv Hfr Hch Hsy".
    rewrite /ut_own_nm. iFrame "Hb Hip Hfd Hir Hpv Hfr Hch Hsy".
  Qed.

  (* the quarter of [p->pid] and the registration eighth, out of the
     marker-less block at once -- [ProcInv.proc_priv_pid_reg]'s reading one
     conjunct in.  The two pieces live in different conjuncts (the pid cell
     in [proc_priv_nocwd], the eighth in the incarnation's two quarters), so
     both come out with one closer. *)
  Lemma ut_priv_nm_pid_reg (γf : gname) (pa : mword 64) (pid : mword 32)
      (U : ustate) :
    proc_priv_unmarked γf pa pid U -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)) ∗
    (p_pid pa ↦₄{DfracOwn (1/4)} pid -∗
     pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)) -∗
     proc_priv_unmarked γf pa pid U).
  Proof using .
    iIntros "(Hn & Hc & Hf & Hgq & Hxs & Hgh)".
    iDestruct (proc_priv_nocwd_pid with "Hn") as "[Hq Hnb]".
    iDestruct (gen_halves_at_reg with "Hgh") as "[Hr Hgb]".
    iFrame "Hq Hr". iIntros "Hq Hr".
    iDestruct ("Hnb" with "Hq") as "Hn". iDestruct ("Hgb" with "Hr") as "Hgh".
    rewrite /proc_priv_unmarked.
    iSplitL "Hn"; [iExact "Hn" |].
    iSplitL "Hc"; [iExact "Hc" |].
    iSplitL "Hf"; [iExact "Hf" |].
    iSplitL "Hgq"; [iExact "Hgq" |].
    iSplitL "Hxs"; [iExact "Hxs" | iExact "Hgh"].
  Qed.

  Lemma ut_hold_unmark (N : ut_names) (U : ustate) (b : bool)
      (lks : gset string) (sts : list fdstate) (cs : gset gname)
      (pid : mword 32) :
    ut_hold Rsys N U b lks sts cs pid ⊣⊢
    ut_hold_nm N U b lks sts cs pid ∗ ChildTok.taken_at (pv_gen (us_V U)).
  Proof using .
    rewrite /ut_hold /ut_hold_nm /ut_env (ut_own_unmark N U sts cs pid).
    (* built, not framed, for [ut_own_unmark]'s reason one tier up *)
    iSplit.
    - iIntros "(A & B & C & [#D [E Ht]])".
      iSplitR "Ht"; [| iExact "Ht"].
      iSplitL "A"; [iExact "A" |].
      iSplitL "B"; [iExact "B" |].
      iSplitL "C"; [iExact "C" |].
      iSplitR; [iExact "D" | iExact "E"].
    - iIntros "[(A & B & C & [#D E]) Ht]".
      iSplitL "A"; [iExact "A" |].
      iSplitL "B"; [iExact "B" |].
      iSplitL "C"; [iExact "C" |].
      iSplitR; [iExact "D" |].
      iSplitL "E"; [iExact "E" | iExact "Ht"].
  Qed.

  (* ==================================================================== *)
  (* THE kexit(-1) DEAD END.                                              *)
  (* ==================================================================== *)
  (* usertrap reaches it from three places (+0xca on the syscall arm, +0xf6
     from the devintr arm's killed check -- through the [j +0xf6] at +0xf2 --
     and +0xf4's fall-through from +0xa6), and each time it spends the WHOLE
     bundle: kexit has no
     continuation, so [ut_hold]'s trap-CSR set, running claim, per-cpu bundle
     and environment all go with the dying process.  [Rsys] is the one member
     kexit does not want, and dropping it is right -- the syscalls' footprint
     belongs to a process that is going to run one. *)
  (* THE KILL STATUS, READ OFF THE REGISTER THE [c.li a0,-1] WROTE.  All
     three call sites reach [jal kexit] through that instruction, and
     [SpecKexit.kexit_status] reads exactly a0 -- so this is the one fact
     that ties the payload the process deposited at -1 to the status kexit
     stores into [p->xstate]. *)
  Lemma ut_kexit_status_neg1 (m : regfile) (v : mword 64) :
    m !!! Regidx (mword_of_int 10 : mword 5) = v ->
    xstate_of v = -1 ->
    kexit_status m = -1.
  Proof using . intros H1 H2. unfold kexit_status. rewrite H1. exact H2. Qed.

  Lemma ut_kexit (N : ut_names) (U : ustate) (m : regfile) (nx : nat)
      (b : bool) (lks : gset string) (sts : list fdstate) (cs : gset gname) (pid : mword 32)
      (* THE DYING PROCESS'S PAYLOAD, at the predicate the trap route
         carries it at ([UexecSG.sexit_pay] of the deposit's families). *)
      (Q : Z -> iProp Σ) :
    ut_wf N ->
    (K_kexit <= nx)%nat ->
    (* THE STATUS IS -1 AT ALL THREE CALL SITES: each is reached through a
       [c.li a0,-1], and [SpecKexit.kexit_status] reads that very word.  So
       what the payload is owed at is the KILL status, which is what the
       process's deposit paid ([UexecRet.upay_at]). *)
    kexit_status m = -1 ->
    (* kexit's own cone bottoms out at "ftable" (1) -- the fileclose loop --
       and every deeper lock it reaches (itable/log/wait_lock/proc) follows
       by [locks_below_mono] inside its own contract, so this is the ONE
       premise the tail owes it. *)
    locks_below lks "log" ->
    kernel_text -∗
    pc_is (mword_of_int KernelSyms.kexit) -∗
    sie_cap_gpr KT1 m nx b (un_pj N) -∗
    (* THE DYING THREAD'S STACK CLOSER, straight through.  This dead end adds
       no frame of its own -- it is a [jal] and nothing else -- so kexit's
       premise is this one verbatim.  Its three call sites build it from
       [ut_caps]' [is_kstack] and usertrap's own frame; see
       [ProcDefs.kstack_closer_top]. *)
    kstack_closer (un_pj N) (m !!! Regidx csp_rs1) (trap_res b + nx)%nat -∗
    (* ...AND THE PAYMENT THIS DEAD END SPENDS.  The process handed its
       payload over when it trapped ([SpecUsertrap.ut_pay_in]); nothing it
       does can pay now -- its continuation is never delivered -- so what
       kexit parks in the ZOMBIE escrow is what came in with the trap. *)
    (* ...AND IT IS NOT [Q (-1)] ANY MORE (lane SELF-KILL, P6).  Nothing
       the process handed over at the trap pays a KILL: what it deposited
       is the payment for the death IT could predict, and a process torn
       down by another hart predicted nothing.  What pays is the deposit
       the KILLER made, in <p->lock>'s killed row -- and kexit is the one
       party that can take it out ([SpecKexit]'s second payment
       disjunct).  All this dead end brings is the incarnation's kill
       ONE-SHOT, which [killed()] handed back at the nonzero flag that got
       execution here, and which is what refutes the row's zero arm. *)
    my_pay (pv_gen (us_V U)) Q -∗
    (* ...AND WHO PAYS THE TEAR-DOWN (design/pipe.md, "The exit path").
       kexit closes every descriptor, and a pipe row's LAST close steps that
       pipe's exact ghost state -- so the closes have a price, and so does
       the death itself.  Both come from the caller's killed check, and they
       come together, as one of two packages:

       LEFT, a kill by a THIRD PARTY.  <p->lock>'s killed row's paid arm
       carries the killer's TAINT, which the check read out of it with the
       block's own marker ([SchedCtx.kill_paid_shot_tear] -- the marker is
       what refutes the spent arm, i.e. what says this row was not founded
       by a self-kill).  The taint pays every close
       ([SpecFileclose.fileclose_cpays_taint]) and the marker is what kexit
       TRADES for the row's payload at the park.

       RIGHT, a SELF-KILL.  The process paid for its own death when it
       trapped: the closes are the exit number's bundle row
       ([UexecExecInst.sbundle_at_exit_elim] off the deposit) and the
       payload is [ChildTok.kill_owed]'s, agreed against the block's own
       [my_pay].  Its marker is already spent -- the fault arm gave it to
       setkilled, which founded the row on the SPENT arm -- so kexit takes
       the LEFT side of its own payment and owes no marker at all. *)
    ((ChildTok.kill_shot (pv_gen (us_V U)) ∗ ChildTok.taken_at (pv_gen (us_V U))
      ∗ app_taint)
     ∨ (fileclose_cpays sts ∗ Q (-1))) -∗
    ut_hold_nm N U b lks sts cs pid -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hwf Hnx Hst Hbelow. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hcl #Hmyp Htear (Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    (* THE TWO ROWS, OFF THE ONE PACKAGE, and read HERE so both arms of the
       caller's price are settled in one place: the taint pays the closes
       and its marker takes kexit's tear-down side; the self-kill's exit row
       pays the closes and its payload takes kexit's LEFT side, at the
       status this dead end stores ([Hst], -1 at all three call sites). *)
    iAssert (fileclose_cpays sts ∗
             (Q (kexit_status m)
              ∨ (⌜kexit_status m = -1⌝ ∗ ChildTok.kill_shot (pv_gen (us_V U))
                 ∗ ChildTok.taken_at (pv_gen (us_V U)))))%I
      with "[Htear]" as "[Hcpays Hpay]".
    { iDestruct "Htear" as "[(#Hs & Ht & #Hc) | [Hcp HQ]]".
      - iSplitR; [ iApply (fileclose_cpays_taint with "Hc") | ].
        iRight. iSplitR; [ iPureIntro; exact Hst | ]. iFrame "Hs Ht".
      - iFrame "Hcp". iLeft. rewrite Hst. iExact "HQ". }
    iDestruct "Hcaps" as "(#Hpi & #Hkd & #Hks & #Hdi & #Hpk & #Hw & #Hft
                           & #Hkm & #Hdk & #Hbio & #Hlog & #Hseam & #Hgc & #Hdev
                           & #Hgeom & #Hav & #Hfsr & #Hpw & #Hig & %Hdqi)".
    iDestruct "Hown" as "(Hbs & Hip & Hfd & Hir & Hpv & Hufr & Hrow & _)".
    (* WHO <INIT> IS, joined for kexit's reparent (lane TRAP-ROWS-3/4,
       T4(b)): the residue's cell is the DISCARDED one and the ghost half
       rides the capability record. *)
    iEval (rewrite Hdqi) in "Hip".
    iDestruct "Hip" as "#Hip".
    iAssert (WaitInv.init_ident (un_ip N)) as "#Hid".
    { iApply (WaitInv.init_ident_at_of_gen with "Hip Hig"). }
    iPoseProof (SpecPrintk.printk_env_panic with "Hpk") as "#Hpe".
    iApply (KE.wp_kexit_sconf (un_ft N) (un_f N) (un_w N) (un_s N) (un_j N) (un_l N)
 (un_pd N) (un_pav N) (un_pu N)

              (un_ip N) (un_dqi N)


              None (un_fn N pid) m nx b b _ pid (upd_usM U _) sts cs Q eq_refl Hj Hjl Hnx Hlg Hbelow
              with "Hcg Hcl Hcpu Hcsrs Hclm Htext Hkd Hpc Hpi Hpe Hw Hft Hkm Hav
                    Hbio Hlog Hseam Hgc Hdev Hgeom Hdk Hbs Hfsr Hip Hid Hfd Hir Hpv Hufr Hcpays Hrow
                    Hmyp Hpay").
    all: try lkbelow.
  Qed.


End ProofUsertrapTail.

Section UtRet2.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (Rsys : gname -> mword 64 -> fclose_names -> iProp Σ).

  (* ==================================================================== *)
  (* +0xb2 .. +0xc6: MAKE_SATP, the epilogue, THE EXIT.                    *)
  (* ==================================================================== *)
  (* ITS OWN SECTION, WHICH IS THE POINT.  prepare_return's post is a
     [wp_next b p] crossing, so everything from +0xb2 on runs on a hart that
     may not be the one usertrap was entered on -- and [CpuId] is a CLASS, so
     a leaf applied inside the caller's section resolves its hart by INSTANCE
     RESOLUTION and picks the section variable, not the hypothesis's hart.
     Annotating every leaf with [(CID := ...)] works and is what the tier does
     for one or two steps; for a fifteen-instruction stretch the honest move is
     durable-notes' "the chaining lemma needs its OWN section": stated here,
     the ambient [CID] IS the post-crossing hart and not one annotation is
     needed.  [ut_ret] below applies it at [(CID := CIDp)]. *)
  Lemma ut_ret2 (N : ut_names) (U0 U : ustate) (pt : uptd) (ksp : mword 64)
      (m0 mf : regfile) (av nx : nat) (b : bool)
      (uepc : mword 64) (vb : mword 1)
      (mie_v menvcfg0 epw scw : mword 64) (lks : gset string)
      (* TWO DESCRIPTOR INDICES, and the difference is the point: [sts0] is
         what usertrap was ENTERED at -- the index the caller's post is
         stated against -- and [sts] is what this tail is parking.  They
         differ on exactly one arm. *)
      (sts0 sts : list fdstate) (gn : gname) (cs cs2 : gset gname)
      (pid : mword 32)
      (* the deposit's families, relayed with the syscall channel's row *)
      (fdep : sfam) (Wk : UexecSlot.uvis) :
    ut_wf N ->
    (* THE GENERATION THE WALK KEPT: the post is stated at the ENTRY record
       and this tail parks the one it was handed.  No arm re-incarnates the
       slot, so the two name one generation, and the caller -- which built
       the second record out of the first -- is the party that says so
       ([SpecUsertrap.ut_gen_kept]).  The payment this tail carries is
       keyed by it too. *)
    ut_gen_kept U0 U ->
    (* the round's descriptor half, as this tail's caller certifies it.  The
       fault and timer arms pass one list twice and prove it by
       [reflexivity]; the syscall arm may have moved them, and its cause IS
       the ecall, so its proof is vacuous. *)
    ut_fd_kept scw sts0 sts ->
    (* ...and the children set's, on the same terms: every entry but fork
       keeps it, and fork's move is the kernel's answer, not a pure row
       ([SpecUsertrap.ut_ch_kept]). *)
    ut_ch_kept scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) cs cs2 ->
    (* ...and the ECALL's half, the row the syscall table states.  Relayed
       exactly like [ut_fd_kept]: the tail re-closes the residue with the
       fragments it borrowed, so whether the round moved the states -- and
       how -- is its caller's statement to make.  The row reads the syscall
       number and its argument off the trapframe usertrap was ENTERED at,
       and the return value out of the one being
       parked -- the ENTRY record is [U0], which these tails already carry
       for [ut_wf]. *)
    ut_fd_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) sts0 sts ->
    (* ...and pipe's join, off the same two records and the same pair of
       images: these tails move neither, so it rides across exactly as the
       descriptor row does. *)
    ut_pipe_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U))
                  (us_M U0) (us_M U) sts0 sts ->
    (* ...and getpid's answer, off the same two records: these tails move
       neither the number nor the a0 word, so it rides across exactly as
       the descriptor and pipe rows do ([SpecUsertrap.ut_ret_pid]). *)
    ut_ret_pid scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) pid ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt (us_V U)) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    mf !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    mf !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 mf ->
    (* [mie]/[menvcfg] -- each a unique architectural constant -- are pinned
       and threaded through the whole call (see UsertrapRes.v's [ut_trap]
       header comment); [mideleg]'s value is NOT (see [usertrap_post]'s
       comment) and is discovered fresh from [sconf] below, not threaded
       as a parameter here. *)
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    (* THE ROUND, COMPLETE (milestone J1a): prepare_return has already run,
       so [U] is the resume record and this is what [usertrap_post] says. *)
    ut_round epw scw U0 U ->
    (* ...and the epc word the [csrw sepc] restored IS the resume trapframe's
       own -- prepare_return writes the four KERNEL words and skips index 3. *)
    pv_tf (us_V U) !!! tf_epc_idx = uepc ->
    (* ...AND WHAT A RESUME PROVES, relayed to the post (lane TRAP-ROWS,
       T2(iii)): +0xa6's [killed] check refuted the read's shot, and this
       tail only carries the conclusion -- [SpecUsertrap.ut_live_out]. *)
    ut_live_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs2 ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xb2)) -∗
    (* ---- exactly what prepare_return handed back ---- *)
    sie_cap_gpr KT1 mf (trap_res b + nx)%nat false (un_pj N) -∗
    cpu_own 0%nat false (un_pj N) false lks -∗
    cpu_claim (un_pj N) -∗
    sepc ↦ᵣ mepc_val uepc -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    sret_bits ('b"0" : mword 1) ('b"1" : mword 1) -∗
    stvec ↦ᵣ uservec_tvec -∗
    ghost_var sie_gname (1/4) vb -∗
    kpt_on cpu_id -∗
    (* the four kernel words prepare_return just wrote, as the residue
       states them -- see [UsertrapRes.ut_tfk] *)
    ut_tfk ksp (us_V U) -∗
    ut_env Rsys N U sts cs2 pid -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    (* THE EXEC CHANNEL'S ANSWER, relayed exactly like the descriptor rows:
       this tail moves nothing the row reads -- [SpecUsertrap.ut_exec_out] *)
    ut_exec_out fdep scw (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) (us_M U0)
      (perm_of (ud_um (pv_upt (us_V U0))) (uint (pv_sz (us_V U0))))
      (uint (pv_sz (us_V U0))) (pv_lazy (us_V U0)) (pv_secc (us_V U0)) U sts0 sts gn cs pid -∗
    (* ...and FORK'S, relayed the same way -- [SpecUsertrap.ut_fork_out] *)
    ut_fork_out fdep scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 -∗
    (* ...and WAIT'S, beside it -- [SpecUsertrap.ut_wait_out] *)
    ut_wait_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (us_M U0) (us_M U)
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 gn pid -∗
    (* ...AND THE UNTAKEN CONTINUATION (lane TRAP-ROWS, T3) *)
    ut_kill_out scw Wk -∗
    (* ...and the syscall channel's, relayed the same way: this tail moves
       nothing the row reads, and the a0 word it is read at is the one of
       the record it parks, at the resume view it parks it at --
       [SpecUsertrap.ut_sys_out] *)
    (∀ n : Z,
       ut_sys_out n fdep scw (pv_tf (us_V U0)) U0 sts0 gn cs pid
         (pv_tf (us_V U) !!! tf_arg_idx 0) (us_M U) sts (pv_cwi (us_V U)) cs2) -∗
    (* THE PAY FACT, CARRIED.  The process handed its knowledge over when
       it trapped ([SpecUsertrap.ut_pay_in]); NOTHING travels beside it any
       more (lane SELF-KILL, P6b) -- a kill is paid for by the KILLER, into
       <p->lock>'s own killed row.  The fact is at the ENTRY record's
       generation, which is the one every arm of this walk keeps
       ([SpecUsertrap.ut_gen_kept]), so the arms below carry it at the
       record they hold and the conversion at each hop is by the update's
       own definition. *)
    my_pay (pv_gen (us_V U)) (sexit_pay fdep) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0 U0 sts0 gn cs pid epw scw fdep Wk) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hwf Hgenk Hfdk Hchk Hfde Hpipe Hpidr Hav Hnx Htfpe Hksp Hm0sp Hmfsp Hmfs1 Hcs Hmiev Hmenvv Hrd Hepcw Hlive.
    (* the budget, in numbers [lia] can see -- every one of these is a
       [Definition] and the index arithmetic below is what needs them *)
    pose proof Hav as Hav'.
    
    destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hcpu Hclm Hsepc Hscause Hstval Hsret Hstvec Hq4
             Hkptr #Htfk [#Hcaps Hown] Hframe Hxo Hfo Hwo Hko Hso #Hmyp Hcont".
    (* the boundary hands the trap resource back at the literal [∅] that
       [ut_res] pins -- depth 0 forces the held set empty, so this is a
       re-spelling, not an obligation. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    (* THE QUARTER'S VALUE IS NOT A DEGREE OF FREEDOM.  prepare_return leaves
       it existential because it never reads it; the arm it also hands back is
       at [false], and [sie_arm_half_agree] reads the live SIE off that index,
       so the half / quarter agreement pins [vb = 'b"0"] -- which is what
       [ut_exit_ms_ok] needs and what makes the return legal. *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (sconf_priv_open with "Hsc") as (msf) "(Hcl & Hpriv & Hmsown)".
    iDestruct "Hmsown" as "(Hms & Hhalf & Htie & %Hmsf)".
    iDestruct "Hcap" as "(Hstk & Hstr & Harm & Hctx & #Htc & #Hwit)".
    iDestruct (sie_arm_half_agree false (un_pj N) msf with "Hhalf Harm") as %Hsie0.
    iDestruct (ghost_var_agree with "Hhalf Hq4") as %Hvb.
    rewrite Hsie0 in Hvb. rewrite -Hvb.
    iDestruct (sret_bits_agree _ _ _ _ with "Htie Hsret") as %[Hspp Hspie].
    iAssert (sconf_msown msf) with "[Hms Hhalf Htie]" as "Hmsown".
    { rewrite /sconf_msown. iSplitL "Hms"; [iExact "Hms"|].
      iSplitL "Hhalf"; [iExact "Hhalf"|].
      iSplitL "Htie"; [iExact "Htie"|]. iPureIntro. exact Hmsf. }
    iDestruct (ut_exit_ms_ok msf with "Hmsown Hsret Hq4") as %Hretms.
    iDestruct "Hmsown" as "(Hms & Hhalf & Htie & _)".
    rewrite /sret_tie Hspp Hspie.
    rewrite Hsie0.
    (* the pieces back into a bundle for the walk *)
    iAssert (sconf) with "[Hcl Hpriv Hms Hhalf Htie]" as "Hsc".
    { iApply ("Hcl" $! msf with "Hpriv [Hms Hhalf Htie]").
      rewrite /sconf_msown /sret_tie Hsie0 Hspp Hspie.
      iSplitL "Hms"; [iExact "Hms"|]. iSplitL "Hhalf"; [iExact "Hhalf"|].
      iSplitL "Htie"; [iExact "Htie"|]. iPureIntro. exact Hmsf. }
    iAssert (sie_cap_gpr KT1 mf (trap_res b + nx)%nat false (un_pj N))
      with "[Hhs Hsc Hstk Hstr Harm Hctx Hfile]" as "Hcg".
    { rewrite /sie_cap_gpr /sie_cap.
      iSplitL "Hhs"; [iExact "Hhs"|]. iSplitL "Hsc"; [iExact "Hsc"|].
      iSplitR "Hfile"; [| iExact "Hfile"].
      iSplitL "Hstk"; [iExact "Hstk"|]. iSplitL "Hstr"; [iExact "Hstr"|].
      iSplitL "Harm"; [iExact "Harm"|].
      iSplitL "Hctx"; [iExact "Hctx"|].
      iSplitR; [iExact "Htc"|]. iExact "Hwit". }
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hufr & Hch & Hsy & Hownback)".
    (* [ut_caps] is NOT destructured here: +0xb2..+0xc6 calls nothing, so no
       member of it is needed, and destructuring an intuitionistic hypothesis
       CONSUMES the name -- which the exit needs to hand [ut_env] back. *)
    (* ---- +0xb2 .. +0xba: MAKE_SATP(p->pagetable) ---- *)
    iDestruct (proc_priv_copy with "Hpv") as "(Hsz & Hpgt & Hppt & Hpvback)".
    iDestruct (proc_ptm_wf with "Hppt") as %Hptwf.
    assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
      by (vm_compute; reflexivity).
    assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
      by (vm_compute; reflexivity).
    assert (Haddrpg : add_vec (rget mf Rs1)
                        (sign_extend' 64 (mword_of_int 80 : mword 12))
                      = p_pagetable (un_pj N))
      by (rgne; rewrite Hmfs1; reflexivity).
    iEval (rewrite -Haddrpg) in "Hpgt".
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (UT + 0xb2)) Ra0 Rs1
              (mword_of_int 80 : mword 12) mf (trap_res b + nx)%nat
              (page_base (ud_root (pv_upt (us_V U)))) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hpgt [-]").
    { iApply (uti_0b2 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpgt".
    set (S0 := <[Regidx Ra0 := regval_into_reg
                   (page_base (ud_root (pv_upt (us_V U))))]> mf).
    change (<[Regidx Ra0 := regval_into_reg
               (page_base (ud_root (pv_upt (us_V U))))]> mf) with S0.
    assert (Hpb4 : add_vec_int (mword_of_int (UT + 0xb2) : mword 64) 2
                   = mword_of_int (UT + 0xb4)) by pcw.
    iEval (rewrite Hpb4) in "Hpc".
    (* ---- +0xb4: srli a0,a0,0xc ---- *)
    iApply (wp_csrli_s_sconf (mword_of_int (UT + 0xb4)) (Cregidx (mword_of_int 2))
              Ra0 (mword_of_int 12 : mword 6) S0 (trap_res b + nx)%nat false
              Hc2 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iEval (rewrite -Hc2). iApply (uti_0b4 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S1 := <[Regidx Ra0 := regval_into_reg
                   (shift_bits_right (rget S0 Ra0)
                      (subrange_vec_dec (mword_of_int 12 : mword 6)
                         (Z.sub log2_xlen 1) 0))]> S0).
    change (<[Regidx Ra0 := regval_into_reg
               (shift_bits_right (rget S0 Ra0)
                  (subrange_vec_dec (mword_of_int 12 : mword 6)
                     (Z.sub log2_xlen 1) 0))]> S0) with S1.
    assert (Hpb6 : add_vec_int (mword_of_int (UT + 0xb4) : mword 64) 2
                   = mword_of_int (UT + 0xb6)) by pcw.
    iEval (rewrite Hpb6) in "Hpc".
    (* ---- +0xb6: li a5,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (UT + 0xb6)) Ra5 (mword_of_int 63 : mword 6)
              (add_vec zero_reg (sign_extend' 64
                 (sign_extend' 12 (mword_of_int 63 : mword 6))))
              S1 (trap_res b + nx)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc [] [-]").
    { iApply (uti_0b6 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S2 := <[Regidx Ra5 := regval_into_reg
                   (add_vec zero_reg (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S1).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec zero_reg (sign_extend' 64
                  (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S1) with S2.
    assert (Hpb8 : add_vec_int (mword_of_int (UT + 0xb6) : mword 64) 2
                   = mword_of_int (UT + 0xb8)) by pcw.
    iEval (rewrite Hpb8) in "Hpc".
    (* ---- +0xb8: slli a5,a5,0x3f ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int (UT + 0xb8)) (Regidx Ra5) Ra5
              (mword_of_int 63 : mword 6) S2 (trap_res b + nx)%nat false
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (uti_0b8 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S3 := <[Regidx Ra5 := regval_into_reg
                   (shift_bits_left (rget S2 Ra5)
                      (subrange_vec_dec (mword_of_int 63 : mword 6)
                         (Z.sub log2_xlen 1) 0))]> S2).
    change (<[Regidx Ra5 := regval_into_reg
               (shift_bits_left (rget S2 Ra5)
                  (subrange_vec_dec (mword_of_int 63 : mword 6)
                     (Z.sub log2_xlen 1) 0))]> S2) with S3.
    assert (Hpba : add_vec_int (mword_of_int (UT + 0xb8) : mword 64) 2
                   = mword_of_int (UT + 0xba)) by pcw.
    iEval (rewrite Hpba) in "Hpc".
    (* ---- +0xba: or a0,a0,a5 -- THE WORD IS kvminithart's ----
       The same five instructions as kvminithart's MAKE_SATP over a different
       register pair, and [WpKvminithart.kvi_satp_word] is register-free, so
       its three field facts ([kvi_satp_mode] / [_asid] / [_ppn]) serve
       verbatim -- which is the whole of [satp_rooted]. *)
    assert (Hor : or_vec (rget S3 Ra0) (rget S3 Ra5)
                  = kvi_satp_word (ud_root (pv_upt (us_V U)))).
    { assert (HS3a0 : rget S3 Ra0
                = shift_bits_right
                    (zero_extend' 64 (concat_vec (ud_root (pv_upt (us_V U)))
                                        (zeros' 12 : mword 12)))
                    (subrange_vec_dec (mword_of_int 12 : mword 6)
                       (Z.sub log2_xlen 1) 0)).
      { rgne. rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
        rewrite /S1 upd_eq. rgne. rewrite /S0 upd_eq. reflexivity. }
      assert (HS3a5 : rget S3 Ra5
                = shift_bits_left
                    (add_vec zero_reg (sign_extend' 64
                       (sign_extend' 12 (mword_of_int 63 : mword 6))))
                    (subrange_vec_dec (mword_of_int 63 : mword 6)
                       (Z.sub log2_xlen 1) 0)).
      { rgne. rewrite /S3 upd_eq. rgne. rewrite /S2 upd_eq. reflexivity. }
      rewrite HS3a0 HS3a5. unfold kvi_satp_word. reflexivity. }
    iApply (wp_cor_s_sconf (mword_of_int (UT + 0xba)) Ra0 Ra0 Ra5
              (kvi_satp_word (ud_root (pv_upt (us_V U)))) S3 (trap_res b + nx)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) Hor
              with "Hcg Hpc [] [-]").
    { iEval (rewrite -Hc2 -Hc7). iApply (uti_0ba with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (S4 := <[Regidx Ra0 := regval_into_reg
                   (kvi_satp_word (ud_root (pv_upt (us_V U))))]> S3).
    change (<[Regidx Ra0 := regval_into_reg
               (kvi_satp_word (ud_root (pv_upt (us_V U))))]> S3) with S4.
    assert (Hpbc : add_vec_int (mword_of_int (UT + 0xba) : mword 64) 2
                   = mword_of_int (UT + 0xbc)) by pcw.
    iEval (rewrite Hpbc) in "Hpc".
    (* the cell back in the block's own spelling -- the load left it in the
       leaf's [add_vec (rget ...) imm] form *)
    iEval (rewrite Haddrpg) in "Hpgt".
    iDestruct ("Hpvback" $! (pv_upt (us_V U)) (us_M U) ltac:(apply uptd_ext_sz_refl)
                 with "Hsz Hpgt Hppt") as "Hpv".
    rewrite us_upt_id upd_usM_id.
    (* ---- +0xbc .. +0xc2: the four restores ---- *)
    iDestruct "Hframe" as "(Hbra & Hbs0 & Hbs1 & Hbs2)".
    assert (HS4sp : S4 !!! Regidx csp_rs1 = pa_stk ksp 4).
    { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
      rewrite /S0 upd_ne; [| reg_neq]. exact Hmfsp. }
    assert (Hp1 : add_vec (S4 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk ksp 1).
    { rewrite HS4sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp1) in "Hbra".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xbc)) (mword_of_int 3 : mword 6)
              Rra S4 (trap_res b + nx)%nat (m0 !!! Regidx Rra) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hbra [-]").
    { iApply (uti_0bc with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbra".
    set (S5 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> S4).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> S4) with S5.
    assert (Hpbe : add_vec_int (mword_of_int (UT + 0xbc) : mword 64) 2
                   = mword_of_int (UT + 0xbe)) by pcw.
    iEval (rewrite Hpbe) in "Hpc".
    assert (HS5sp : S5 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S5 upd_ne; [exact HS4sp | reg_neq]).
    assert (Hp2 : add_vec (S5 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk ksp 2).
    { rewrite HS5sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp2) in "Hbs0".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xbe)) (mword_of_int 2 : mword 6)
              Rs0 S5 (trap_res b + nx)%nat (m0 !!! Regidx Rs0) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hbs0 [-]").
    { iApply (uti_0be with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs0".
    set (S6 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> S5).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> S5) with S6.
    assert (Hpc0 : add_vec_int (mword_of_int (UT + 0xbe) : mword 64) 2
                   = mword_of_int (UT + 0xc0)) by pcw.
    iEval (rewrite Hpc0) in "Hpc".
    assert (HS6sp : S6 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S6 upd_ne; [exact HS5sp | reg_neq]).
    assert (Hp3 : add_vec (S6 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk ksp 3).
    { rewrite HS6sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp3) in "Hbs1".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xc0)) (mword_of_int 1 : mword 6)
              Rs1 S6 (trap_res b + nx)%nat (m0 !!! Regidx Rs1) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hbs1 [-]").
    { iApply (uti_0c0 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs1".
    set (S7 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> S6).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> S6) with S7.
    assert (Hpc2 : add_vec_int (mword_of_int (UT + 0xc0) : mword 64) 2
                   = mword_of_int (UT + 0xc2)) by pcw.
    iEval (rewrite Hpc2) in "Hpc".
    assert (HS7sp : S7 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S7 upd_ne; [exact HS6sp | reg_neq]).
    assert (Hp4 : add_vec (S7 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk ksp 4).
    { rewrite HS7sp. apply stk_frm. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hp4) in "Hbs2".
    iApply (wp_cldsp_s_sconf (mword_of_int (UT + 0xc2)) (mword_of_int 0 : mword 6)
              Rs2 S7 (trap_res b + nx)%nat (m0 !!! Regidx Rs2) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hbs2 [-]").
    { iApply (uti_0c2 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs2".
    set (S8 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> S7).
    change (<[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> S7) with S8.
    assert (Hpc4 : add_vec_int (mword_of_int (UT + 0xc2) : mword 64) 2
                   = mword_of_int (UT + 0xc4)) by pcw.
    iEval (rewrite Hpc4) in "Hpc".
    (* ---- +0xc4: c.addi16sp sp,32 -- the frame traded back ---- *)
    assert (HS8sp : S8 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /S8 upd_ne; [exact HS7sp | reg_neq]).
    assert (Hwv : add_vec (S8 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = ksp) by (rewrite HS8sp; apply stk_pop_32).
    assert (Hpop : S8 !!! Regidx csp_rs1
                   = pa_stk (add_vec (S8 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HS8sp; reflexivity).
    (* each load handed its word back in the LEAF's address spelling; put the
       four back in [pa_stk]'s so they re-assemble into the frame *)
    iEval (rewrite Hp1) in "Hbra".
    iEval (rewrite Hp2) in "Hbs0".
    iEval (rewrite Hp3) in "Hbs1".
    iEval (rewrite Hp4) in "Hbs2".
    iAssert (stack_own (KTR := KT1) ksp 4) with "[Hbra Hbs0 Hbs1 Hbs2]" as "Hfr".
    { iApply (stack_own_4_intro (KTR := KT1) ksp with "Hbra Hbs0 Hbs1 Hbs2"). }
    iEval (rewrite -Hwv) in "Hfr".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (UT + 0xc4))
              (mword_of_int 2 : mword 6) S8 (trap_res b + nx)%nat 4 false Hpop
              with "Hcg Hpc [] Hfr [-]").
    { iApply (uti_0c4 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hwv) in "Hcg".
    set (S9 := <[Regidx csp_rs1 := regval_into_reg ksp]> S8).
    change (<[Regidx csp_rs1 := regval_into_reg ksp]> S8) with S9.
    assert (Havn : ((trap_res b + nx) + 4)%nat = av) by lia.
    iEval (rewrite Havn) in "Hcg".
    assert (Hpc6 : add_vec_int (mword_of_int (UT + 0xc4) : mword 64) 2
                   = mword_of_int (UT + 0xc6)) by pcw.
    iEval (rewrite Hpc6) in "Hpc".
    (* ---- +0xc6: c.jr ra ---- *)
    assert (HS9ra : rget S9 Rra = m0 !!! Regidx Rra).
    { rgne. rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
      rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_ne; [| reg_neq].
      rewrite /S5 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (UT + 0xc6)) Rra S9 av false
              ltac:(vm_compute; discriminate) with "Hcg Hpc [] [-]").
    { iApply (uti_0c6 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HS9ra) in "Hpc".
    (* ================================================================== *)
    (*  THE EXIT: the payload back into the boundary's pieces.             *)
    (* ================================================================== *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    (* [sconf] is destructured DIRECTLY here -- not via [sconf_priv_open],
       whose closer would re-park [mie]/[mideleg]/[menvcfg] rather than
       hand them out loose (see [ut_trap]'s header comment).  [hw_config]/
       [minstret_inv] ride at the head, at THIS (the resuming) hart -- kept,
       not discarded, since [usertrap_post] hands them back (see its
       comment). *)
    iDestruct "Hsc" as "(#Hhw & #Hmin & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (msg) "Hmsown".
    iDestruct (ut_exit_ms_ok msg with "Hmsown Hsret Hq4") as %Hretms2.
    iDestruct "Hmsown" as "(Hms & Hhalf & Htie & %Hmsg)".
    iDestruct (sret_bits_agree _ _ _ _ with "Htie Hsret") as %[Hspp2 Hspie2].
    iDestruct (ghost_var_agree with "Hhalf Hq4") as %Hsie2.
    rewrite /sret_tie Hspp2 Hspie2.
    rewrite Hsie2.
    (* [mie]/[menvcfg]: each pinned to its unique constant, so the exit
       value provably equals what [ut_trap_open] was handed at entry.
       [mideleg]: a fresh witness, handed to [Hcont] as-is (see
       [usertrap_post]'s comment). *)
    iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmaskx)".
    subst mie_v.
    iDestruct "Hmenvx" as (menvcfg0') "(Hmenv & _ & _ & _ & _ & %Hmeq)".
    subst menvcfg0' menvcfg0.
    (* [mf'] IS [tp_pin S9]: usertrap may have MIGRATED, so the tp SLOT of the
       map it threaded still holds the ENTRY hart's id while [gpr_file] holds
       the pinned one.  Handing over the pinned map makes the boundary's
       [mf !!! tp = cid_word] hold by construction, and tp is deliberately not
       one of [callee_saved]'s thirteen. *)
    assert (HcsS9 : ut_cs m0 S9).
    { rewrite /S9 /S8 /S7 /S6 /S5 /S4 /S3 /S2 /S1 /S0.
      apply ut_cs_insert4; [by left |].
      apply ut_cs_insert4; [by right; right; right |].
      apply ut_cs_insert4; [by right; right; left |].
      apply ut_cs_insert4; [by right; left |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      apply ut_cs_insert; [vm_compute; reflexivity |].
      exact Hcs. }
    assert (HcsF : callee_saved m0 S9).
    { apply (ut_cs_to_callee_saved m0 S9 HcsS9).
      - rewrite /S9 upd_eq Hm0sp. reflexivity.
      - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
        rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_eq. reflexivity.
      - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
        rewrite /S7 upd_eq. reflexivity.
      - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_eq. reflexivity. }
    assert (HcsP : callee_saved m0 (tp_pin S9)).
    { rewrite /tp_pin.
      apply (callee_saved_insert_r Rtp _ m0 S9 ltac:(vm_compute; reflexivity) HcsF). }
    assert (Htpid : tp_pin S9 !!! Regidx Rtp = cid_word)
      by (rewrite /tp_pin upd_eq; reflexivity).
    assert (Hmfa0 : tp_pin S9 !!! Regidx Ra0
                    = kvi_satp_word (ud_root (pv_upt (us_V U)))).
    { rewrite /tp_pin upd_ne; [| reg_neq]. rewrite /S9 upd_ne; [| reg_neq].
      rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
      rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
      rewrite /S4 upd_eq. reflexivity. }
    destruct Hptwf as (Hmapwf & Haccwf & _ & _ & _).
    iDestruct "Hscause" as (scv) "Hscause".
    iDestruct "Hstval" as (stv) "Hstval".
    iSpecialize ("Hcont" $! CID with "[%]"); [intros _; reflexivity|].
    iDestruct ("Hownback" $! U sts cs2 with "Hpv Hufr Hch Hsy") as "Hown".
    iAssert (⌜ut_live_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
                (pv_tf (us_V U) !!! tf_arg_idx 0) cs2⌝)%I as "Hlv";
      [ iPureIntro; exact Hlive | ].
    iApply ("Hcont" $! (pv_upt (us_V U)) (tp_pin S9) msg
              (kvi_satp_word (ud_root (pv_upt (us_V U)))) (mepc_val uepc) scv stv mdv0 U
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hhs Hpriv Hms Hscause Hstval Hsepc [Hstvec] Hpc [Hfile]
                    Hmie Hmdl Hmenv Hhw Hmin [-Hxo Hfo Hwo Hlv Hko Hso]
                    Hxo Hfo Hwo Hlv Hko Hso").
    - reflexivity.
    - exact Hrd.
    - (* [ut_fd_kept], straight off the premise: this tail re-closes the
         residue with the SAME fragments it borrowed, so what it parks is
         what its caller handed it, and whether THAT moved the states is
         the caller's statement to make. *)
      exact Hfdk.
    - (* ...and the children set's row, likewise its caller's statement *)
      exact Hchk.
    - (* ...AND THE GENERATION'S, straight off the premise: this tail parks
         the record it was handed and re-incarnates nothing, and whether
         THAT record kept the entry's generation is its caller's statement
         ([SpecUsertrap.ut_gen_kept]). *)
      exact Hgenk.
    - (* ...and [ut_fd_ecall], the same way *)
      exact Hfde.
    - (* ...and pipe's join, likewise untouched by this tail *)
      exact Hpipe.
    - (* ...and getpid's answer, likewise: the tail stores no a0 word *)
      exact Hpidr.
    - (* [ret_pc (mepc_val uepc) = tf_resume_pc (pv_tf (us_V U))]: [mepc_val]
         IS [ret_pc], which is idempotent, and the epc word is [uepc]. *)
      unfold tf_resume_pc, tf_w. rewrite Hepcw. exact (ret_pc_idem uepc).
    - exact Hmaskx.
    - exact Htfpe.
    - exact Haccwf.
    - exact Hmapwf.
    - exact Hretms2.
    - exact Hmsg.
    - exact HcsP.
    - exact Htpid.
    - exact Hmfa0.
    - split_and!; [exact (kvi_satp_mode _) | exact (kvi_satp_asid _)
                  | exact (kvi_satp_ppn _)].
    - rewrite /uservec_tvec. iExact "Hstvec".
    - (* the boundary asks for [gpr_file mf] and [mf] IS [tp_pin S9], so this
         is what [sie_cap_gpr] was holding all along -- no [tp_pin_id] step. *)
      iExact "Hfile".
    - (* [ut_res] rebuilt at the exit hart *)
      iExists N, av.
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; exact Hksp|].
      iSplitR; [iPureIntro; exact (conj Hj (conj Hjl (conj Hlen Hlg)))|].
      iSplitR; [iPureIntro; exact Hav|].
      iSplitR; [iExact "Htfk"|].
      iSplitR; [iExact "Htc"|].
      (* the mstatus and privilege CELLS, and now [mie]/[mideleg]/[menvcfg]
         too, are NOT in [ut_trap]: they go to the boundary raw (above). *)
      iSplitL "Hcap Hhalf Htie Hq4 Hkptr Hsret Hcpu Hclm".
      + rewrite /ut_trap /ut_stack /ut_ghosts.
        iDestruct "Hcap" as "(Hstk & Hstr & Harm & Hctx & _)".
        iSplitL "Hstk". { rewrite /S9 upd_eq. iExact "Hstk". }
        iSplitL "Hstr". { iExact "Hstr". }
        iSplitL "Harm". { iExact "Harm". }
        iSplitL "Hctx". { iExact "Hctx". }
        iSplitL "Hkptr". { iExact "Hkptr". }
        iSplitL "Hhalf Hq4 Htie Hsret".
        { iSplitL "Hhalf". { iExact "Hhalf". }
          iSplitL "Hq4". { iExact "Hq4". }
          iSplitL "Htie". { iExact "Htie". }
          iExact "Hsret". }
        iSplitL "Hcpu". { iEval (rewrite Hlkempty) in "Hcpu". iExact "Hcpu". }
        iExact "Hclm".
      + rewrite /ut_env. iSplitR; [iExact "Hcaps"|]. iExact "Hown".
  Qed.

End UtRet2.

Section UtRet.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (Rsys : gname -> mword 64 -> fclose_names -> iProp Σ).

  (* ==================================================================== *)
  (* +0xae: jal prepare_return, then the second half at ITS hart.          *)
  (* ==================================================================== *)
  Lemma ut_ret (N : ut_names) (U0 U : ustate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (b : bool)
      (mie_v menvcfg0 epw scw : mword 64) (lks : gset string)
      (* TWO DESCRIPTOR INDICES, and the difference is the point: [sts0] is
         what usertrap was ENTERED at -- the index the caller's post is
         stated against -- and [sts] is what this tail is parking.  They
         differ on exactly one arm. *)
      (sts0 sts : list fdstate) (gn : gname) (cs cs2 : gset gname)
      (pid : mword 32)
      (* the deposit's families, relayed with the syscall channel's row *)
      (fdep : sfam) (Wk : UexecSlot.uvis) :
    ut_wf N ->
    (* THE GENERATION THE WALK KEPT: the post is stated at the ENTRY record
       and this tail parks the one it was handed.  No arm re-incarnates the
       slot, so the two name one generation, and the caller -- which built
       the second record out of the first -- is the party that says so
       ([SpecUsertrap.ut_gen_kept]).  The payment this tail carries is
       keyed by it too. *)
    ut_gen_kept U0 U ->
    (* the round's descriptor half, as this tail's caller certifies it.  The
       fault and timer arms pass one list twice and prove it by
       [reflexivity]; the syscall arm may have moved them, and its cause IS
       the ecall, so its proof is vacuous. *)
    ut_fd_kept scw sts0 sts ->
    (* ...and the children set's, on the same terms: every entry but fork
       keeps it, and fork's move is the kernel's answer, not a pure row
       ([SpecUsertrap.ut_ch_kept]). *)
    ut_ch_kept scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) cs cs2 ->
    (* ...and the ECALL's half, the row the syscall table states.  Relayed
       exactly like [ut_fd_kept]: the tail re-closes the residue with the
       fragments it borrowed, so whether the round moved the states -- and
       how -- is its caller's statement to make.  The row reads the syscall
       number and its argument off the trapframe usertrap was ENTERED at,
       and the return value out of the one being
       parked -- the ENTRY record is [U0], which these tails already carry
       for [ut_wf]. *)
    ut_fd_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) sts0 sts ->
    (* ...and pipe's join, off the same two records and the same pair of
       images: these tails move neither, so it rides across exactly as the
       descriptor row does. *)
    ut_pipe_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U))
                  (us_M U0) (us_M U) sts0 sts ->
    (* ...and getpid's answer, off the same two records: these tails move
       neither the number nor the a0 word, so it rides across exactly as
       the descriptor and pipe rows do ([SpecUsertrap.ut_ret_pid]). *)
    ut_ret_pid scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) pid ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt (us_V U)) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    (* THE ROUND SO FAR (milestone J1a) -- see [SpecUsertrap.ut_round]. *)
    ut_round epw scw U0 U ->
    (* ...AND WHAT A RESUME PROVES, relayed to the post (lane TRAP-ROWS,
       T2(iii)): +0xa6's [killed] check refuted the read's shot, and this
       tail only carries the conclusion -- [SpecUsertrap.ut_live_out]. *)
    ut_live_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs2 ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xae)) -∗
    sie_cap_gpr KT1 m nx b (un_pj N) -∗
    ut_hold Rsys N U b lks sts cs2 pid -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    (* THE EXEC CHANNEL'S ANSWER, relayed exactly like the descriptor rows:
       this tail moves nothing the row reads -- [SpecUsertrap.ut_exec_out] *)
    ut_exec_out fdep scw (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) (us_M U0)
      (perm_of (ud_um (pv_upt (us_V U0))) (uint (pv_sz (us_V U0))))
      (uint (pv_sz (us_V U0))) (pv_lazy (us_V U0)) (pv_secc (us_V U0)) U sts0 sts gn cs pid -∗
    (* ...and FORK'S, relayed the same way -- [SpecUsertrap.ut_fork_out] *)
    ut_fork_out fdep scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 -∗
    (* ...and WAIT'S, beside it -- [SpecUsertrap.ut_wait_out] *)
    ut_wait_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (us_M U0) (us_M U)
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 gn pid -∗
    (* ...AND THE UNTAKEN CONTINUATION (lane TRAP-ROWS, T3) *)
    ut_kill_out scw Wk -∗
    (* ...and the syscall channel's, relayed the same way: this tail moves
       nothing the row reads, and the a0 word it is read at is the one of
       the record it parks, at the resume view it parks it at --
       [SpecUsertrap.ut_sys_out] *)
    (∀ n : Z,
       ut_sys_out n fdep scw (pv_tf (us_V U0)) U0 sts0 gn cs pid
         (pv_tf (us_V U) !!! tf_arg_idx 0) (us_M U) sts (pv_cwi (us_V U)) cs2) -∗
    (* THE PAY FACT, CARRIED.  The process handed its knowledge over when
       it trapped ([SpecUsertrap.ut_pay_in]); NOTHING travels beside it any
       more (lane SELF-KILL, P6b) -- a kill is paid for by the KILLER, into
       <p->lock>'s own killed row.  The fact is at the ENTRY record's
       generation, which is the one every arm of this walk keeps
       ([SpecUsertrap.ut_gen_kept]), so the arms below carry it at the
       record they hold and the conversion at each hop is by the update's
       own definition. *)
    my_pay (pv_gen (us_V U)) (sexit_pay fdep) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0 U0 sts0 gn cs pid epw scw fdep Wk) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hwf Hgenk Hfdk Hchk Hfde Hpipe Hpidr Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv Hrd Hlive.
    pose proof (ut_nx_bound b av nx Hav Hnx) as Hks.
    
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hxo Hfo Hwo Hko Hso #Hmyp Hcont".
    iDestruct "Hhold" as "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    iDestruct (ut_own_priv with "Hown") as "(Hpv & Hufr & Hch & Hsy & Hownback)".
    iDestruct (ut_epc_exists with "Hpv") as %Hepcx.
    iDestruct (ut_tf_length with "Hpv") as %Htflen.
    destruct Hepcx as [uepc Hepc].
    iAssert (is_kstack (un_pj N) (un_ks N)) with "[]" as "#Hkst".
    { iDestruct "Hcaps" as "(_ & _ & #H & _)". iExact "H". }
    (* ---- +0xae: jal prepare_return ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (UT + 0xae)) Rra
              (mword_of_int 2096642 : mword 21) m nx b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc [] [-]").
    { iApply (uti_0ae with "Htext"). }
    iIntros (CID1 Hk1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0xae) : mword 64) 4)]> m).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0xae) : mword 64) 4)]> m) with M1.
    assert (Hentry : add_vec (mword_of_int (UT + 0xae) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096642 : mword 21))
                     = mword_of_int KernelSyms.prepare_return) by pcw.
    iEval (rewrite Hentry) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HM1ra : M1 !!! Regidx Rra = mword_of_int (UT + 0xb2))
      by (rewrite /M1 upd_eq; pcw).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    iDestruct (cpu_own_transport CID CID1 0%nat b (un_pj N) b
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iDestruct (trap_csrs_ext_transport CID CID1 b (un_pj N)
                 ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
    iApply (PR.wp_prepare_return_sconf (un_f N) (un_ks N) pid U
              M1 nx (un_pj N) uepc b lks ltac:(lia) Hepc
              with "Hcg Hcpu Hcsrs Htext Hpc Hkst Hpv [-]").
    iIntros (CIDp Hkp mf ksat kroot vb)
      "%Hcspr %Hmode %Hasid %Hppn #Hkinv Hcg Hcpu Hclmpay Hsepc Hscause Hstval
       Hsret Hstvec Hq4 Hkptr Hpv Hpc".
    assert (Hpc0b2 : ret_pc (M1 !!! Regidx Rra) = mword_of_int (UT + 0xb2))
      by (rewrite HM1ra; pcw).
    iEval (rewrite Hpc0b2) in "Hpc".
    (* THE CLAIM, REJOINED -- [IntrDefs.cpu_claim_ext_split] is the seam: at
       [b = false] we kept our own and prepare_return's payout is [emp], at
       [b = true] the arm owned it and the [intr_off] has just handed it over. *)
    iDestruct (cpu_claim_ext_transport CID CIDp b (un_pj N)
                 ltac:(wp_next_chain) with "Hclm") as "Hclm".
    iAssert (cpu_claim (CID := CIDp) (un_pj N)) with "[Hclmpay Hclm]" as "Hclm".
    { rewrite -(cpu_claim_ext_split (CID := CIDp) b (un_pj N)).
      iSplitL "Hclmpay"; [iExact "Hclmpay" | iExact "Hclm"]. }
    iDestruct (wp_next_retarget CID CIDp true (un_pj N) _
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    set (Vr := upd_tf (us_V U) (prepare_return_tf (pv_tf (us_V U)) ksat
                           (add_vec (un_ks N) (mword_of_int 4096)) (cid_word (CID := CIDp)))).
    change (upd_tf (us_V U) (prepare_return_tf (pv_tf (us_V U)) ksat
              (add_vec (un_ks N) (mword_of_int 4096)) (cid_word (CID := CIDp)))) with Vr.
    assert (HVrupt : pv_upt Vr = pv_upt (us_V U)) by (rewrite /Vr; destruct (us_V U); reflexivity).
    (* THE KERNEL WORDS, sealed: [Vr]'s trapframe is [prepare_return_tf] of
       the old one, whose four inserts are exactly [tf_kernel_words_ok] at
       the root the satp read returned, at THIS hart. *)
    iDestruct (ut_tfk_intro (CID := CIDp) (add_vec (un_ks N) (mword_of_int 4096)) Vr kroot
                 (prepare_return_tf_kernel_words_ok (CID := CIDp) (pv_tf (us_V U)) ksat
                    (add_vec (un_ks N) (mword_of_int 4096)) kroot Htflen Hmode Hasid Hppn)
                 with "Hkinv") as "#Htfk".
    iEval (rewrite Hksp) in "Htfk".
    iDestruct ("Hownback" $! (MkUstate Vr (us_M U)) sts cs2 with "Hpv Hufr Hch Hsy") as "Hown".
    (* THE ROUND ACROSS prepare_return: the four KERNEL words it re-armed are
       exactly what [TfUser.tf_ueq] is blind to, and it moves neither the
       descriptor nor the size nor the image. *)
    assert (HVrsz : pv_sz Vr = pv_sz (us_V U))
      by (rewrite /Vr; destruct (us_V U); reflexivity).
    assert (HVrtf : pv_tf Vr = prepare_return_tf (pv_tf (us_V U)) ksat
                      (add_vec (un_ks N) (mword_of_int 4096)) (cid_word (CID := CIDp)))
      by (rewrite /Vr; destruct (us_V U); reflexivity).
    assert (Hrdr : ut_round epw scw U0 (MkUstate Vr (us_M U))).
    { refine (ut_round_ueq epw scw U0 U (MkUstate Vr (us_M U)) _ _ eq_refl _ _ _ _
                Hrd).
      - cbn [us_V]. rewrite HVrtf. apply prepare_return_tf_ueq.
      - cbn [us_V]. rewrite HVrupt HVrsz. reflexivity.
      - cbn [us_V]. exact HVrsz.
      - cbn [us_V]. rewrite /Vr; destruct (us_V U); reflexivity.
      (* the lazy bit: prepare_return writes trapframe words and no block
         field ([ProcDefs.pv_lazy]) -- lane LAZY-FLAG *)
      - cbn [us_V]. rewrite /Vr; destruct (us_V U); reflexivity.
      (* ...nor the mask *)
      - cbn [us_V]. rewrite /Vr; destruct (us_V U); reflexivity. }
    (* ...and the cwd's inum, which prepare_return's four stores leave alone *)
    assert (HVrcwi : pv_cwi (us_V (MkUstate Vr (us_M U))) = pv_cwi (us_V U))
      by (cbn [us_V]; rewrite /Vr; destruct (us_V U); reflexivity).
    (* ...and the exec row across the same re-arming ([ut_exec_out_ueq]):
       the entry frame is untouched and the parked record moves in the four
       kernel words only *)
    assert (HVru : tf_ueq (pv_tf (us_V U)) (pv_tf (us_V (MkUstate Vr (us_M U))))).
    { cbn [us_V]. rewrite HVrtf. apply prepare_return_tf_ueq. }
    assert (HVrpi : perm_of (ud_um (pv_upt (us_V (MkUstate Vr (us_M U)))))
                      (uint (pv_sz (us_V (MkUstate Vr (us_M U)))))
                    = perm_of (ud_um (pv_upt (us_V U))) (uint (pv_sz (us_V U)))).
    { cbn [us_V]. rewrite HVrupt HVrsz. reflexivity. }
    iDestruct (ut_exec_out_ueq fdep scw _ _ _ _ _ _ _ U (MkUstate Vr (us_M U))
                 sts0 sts gn cs pid
                 (tf_ueq_refl _) HVru eq_refl HVrpi HVrsz HVrcwi
                 (* the lazy bit across the re-arming: prepare_return writes
                    no block field (lane LAZY-FLAG) *)
                 ltac:(cbn [us_V]; rewrite /Vr; destruct (us_V U); reflexivity)
                 with "Hxo") as "Hxo".
    (* ...and the syscall channel's row across the same re-arming.  It reads
       the parked frame at a0 alone, which is what [tf_ueq] is blind to --
       the same word the descriptor row below crosses by. *)
    assert (Hsoarg : pv_tf (us_V U) !!! tf_arg_idx 0
                     = pv_tf (us_V (MkUstate Vr (us_M U))) !!! tf_arg_idx 0)
      by exact (tf_ueq_arg _ _ 0 ltac:(lia) HVru).
    iEval (rewrite Hsoarg) in "Hso".
    (* ...and fork's, read at that same word *)
    iEval (rewrite Hsoarg) in "Hfo".
    (* ...and wait's, beside it *)
    iEval (rewrite Hsoarg) in "Hwo".
    (* ...and at the cwd inum of that same record, which the row also reads
       and which prepare_return leaves alone ([HVrcwi]) *)
    iEval (rewrite -HVrcwi) in "Hso".
    (* THE DESCRIPTOR ROW ACROSS prepare_return.  The row reads the parked
       trapframe at a0 alone, and prepare_return re-arms the four KERNEL
       words -- which is exactly what [tf_ueq] is blind to -- so it crosses
       by [TfUser.tf_ueq_arg], the argument-word twin of the [tf_ueq_epc]
       the round above crosses by. *)
    assert (Hfder : ut_fd_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0))
                      (pv_tf (us_V (MkUstate Vr (us_M U)))) sts0 sts).
    { refine (ut_fd_ecall_out scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) _
                sts0 sts _ Hfde).
      cbn [us_V]. rewrite HVrtf.
      exact (tf_ueq_arg _ _ 0 ltac:(lia) (prepare_return_tf_ueq _ _ _ _)). }
    (* ...and pipe's join across the same re-arming, by the same word: the
       image half is untouched here ([us_M] rides through the [Vr] swap
       unchanged), so only the a0 reading has to move. *)
    assert (Hpiper : ut_pipe_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0))
                       (pv_tf (us_V (MkUstate Vr (us_M U))))
                       (us_M U0) (us_M (MkUstate Vr (us_M U))) sts0 sts).
    { refine (ut_pipe_ecall_out scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) _
                _ _ sts0 sts _ Hpipe).
      cbn [us_V]. rewrite HVrtf.
      exact (tf_ueq_arg _ _ 0 ltac:(lia) (prepare_return_tf_ueq _ _ _ _)). }
    (* ...and getpid's answer across the same re-arming, off the same word:
       prepare_return re-arms the four KERNEL words and a0 is not one of
       them ([SpecUsertrap.ut_ret_pid_out]). *)
    assert (Hpidrr : ut_ret_pid scw (pv_secc (us_V U0)) (pv_tf (us_V U0))
                       (pv_tf (us_V (MkUstate Vr (us_M U)))) pid).
    { refine (ut_ret_pid_out scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) _ _ _ Hpidr).
      cbn [us_V]. rewrite HVrtf.
      exact (tf_ueq_arg _ _ 0 ltac:(lia) (prepare_return_tf_ueq _ _ _ _)). }
    assert (Hepcw : pv_tf (us_V (MkUstate Vr (us_M U))) !!! tf_epc_idx = uepc).
    { cbn [us_V]. rewrite HVrtf.
      rewrite <- (tf_ueq_epc _ _ (prepare_return_tf_ueq (pv_tf (us_V U)) ksat
                    (add_vec (un_ks N) (mword_of_int 4096)) (cid_word (CID := CIDp)))).
      apply list_lookup_total_correct. exact Hepc. }
    iApply (ut_ret2 (CID := CIDp) Rsys N U0 (MkUstate Vr _) pt ksp m0 mf av nx b uepc vb
              mie_v menvcfg0 epw scw lks sts0 sts gn cs cs2 pid fdep Wk
              Hwf' ltac:(cbn [us_V]; exact Hgenk) Hfdk Hchk Hfder Hpiper Hpidrr Hav Hnx ltac:(rewrite HVrupt; exact Htfpe) Hksp Hm0sp
              ltac:(rewrite (callee_saved_lookup Hcspr csp_rs1
                              ltac:(vm_compute; reflexivity)); exact HM1sp)
              ltac:(rewrite (callee_saved_lookup Hcspr Rs1
                              ltac:(vm_compute; reflexivity)); exact HM1s1)
              ltac:(exact (ut_cs_trans m0 M1 mf HcsM1
                             (ut_cs_of_callee_saved _ _ Hcspr)))
              Hmiev Hmenvv Hrdr Hepcw ltac:(rewrite <- Hsoarg; exact Hlive)
              with "Htext Hpc Hcg Hcpu Hclm Hsepc Hscause Hstval Hsret Hstvec
                    Hq4 Hkptr Htfk [Hown] Hframe Hxo Hfo Hwo Hko Hso Hmyp Hcont").
    rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtRet.

Section UtA6.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (Rsys : gname -> mword 64 -> fclose_names -> iProp Σ).

  (* ==================================================================== *)
  (* +0xa6:  if (killed(p)) { which_dev = 0; kexit(-1); }                  *)
  (* ==================================================================== *)
  (* The rejoin every arm reaches, at [b = true] from the syscall arm and at
     [b = false] from the other three.  [which_dev = 0] before the kexit is
     dead code in the resource sense -- kexit never returns -- so the [c.li
     s2,0] is stepped and its value never read again. *)
  (* THE BRANCH'S OWN READING OF THE FLAG (lane TRAP-ROWS, T3).  The
     [c.bnez a0] at +0xac tests the SIGN-EXTENDED word [killed()] returned;
     its FALL-THROUGH says that word is zero, and [RiscvExtras.trunc32_sext64]
     brings that back to the 32-bit cell the row is stated at. *)
  Local Lemma ut_kl_zero_of_branch (kl : mword 32) :
    neq_vec (sign_extend' 64 kl) (zero_reg : mword 64) = false ->
    kl = (mword_of_int 0 : mword 32).
  Proof using .
    unfold neq_vec. rewrite negb_false_iff. intro H.
    apply eq_vec_true_iff in H.
    apply (f_equal trunc32) in H. rewrite trunc32_sext64 in H.
    rewrite H. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ut_a6 (N : ut_names) (U0 U : ustate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (b : bool)
      (mie_v menvcfg0 epw scw : mword 64) (lks : gset string)
      (* TWO DESCRIPTOR INDICES, and the difference is the point: [sts0] is
         what usertrap was ENTERED at -- the index the caller's post is
         stated against -- and [sts] is what this tail is parking.  They
         differ on exactly one arm. *)
      (sts0 sts : list fdstate) (gn : gname) (cs cs2 : gset gname)
      (pid : mword 32)
      (* the deposit's families, relayed with the syscall channel's row *)
      (fdep : sfam) (Wk : UexecSlot.uvis) :
    ut_wf N ->
    (* THE GENERATION THE WALK KEPT: the post is stated at the ENTRY record
       and this tail parks the one it was handed.  No arm re-incarnates the
       slot, so the two name one generation, and the caller -- which built
       the second record out of the first -- is the party that says so
       ([SpecUsertrap.ut_gen_kept]).  The payment this tail carries is
       keyed by it too. *)
    ut_gen_kept U0 U ->
    (* the round's descriptor half, as this tail's caller certifies it.  The
       fault and timer arms pass one list twice and prove it by
       [reflexivity]; the syscall arm may have moved them, and its cause IS
       the ecall, so its proof is vacuous. *)
    ut_fd_kept scw sts0 sts ->
    (* ...and the children set's, on the same terms: every entry but fork
       keeps it, and fork's move is the kernel's answer, not a pure row
       ([SpecUsertrap.ut_ch_kept]). *)
    ut_ch_kept scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) cs cs2 ->
    (* ...and the ECALL's half, the row the syscall table states.  Relayed
       exactly like [ut_fd_kept]: the tail re-closes the residue with the
       fragments it borrowed, so whether the round moved the states -- and
       how -- is its caller's statement to make.  The row reads the syscall
       number and its argument off the trapframe usertrap was ENTERED at,
       and the return value out of the one being
       parked -- the ENTRY record is [U0], which these tails already carry
       for [ut_wf]. *)
    ut_fd_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) sts0 sts ->
    (* ...and pipe's join, off the same two records and the same pair of
       images: these tails move neither, so it rides across exactly as the
       descriptor row does. *)
    ut_pipe_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U))
                  (us_M U0) (us_M U) sts0 sts ->
    (* ...and getpid's answer, off the same two records: these tails move
       neither the number nor the a0 word, so it rides across exactly as
       the descriptor and pipe rows do ([SpecUsertrap.ut_ret_pid]). *)
    ut_ret_pid scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) pid ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt (us_V U)) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    (* THE ROUND SO FAR (milestone J1a) -- see [SpecUsertrap.ut_round]. *)
    ut_round epw scw U0 U ->
    (* the block's whole cone bottoms out at "ftable" (1), via the killed
       branch's [ut_kexit]; killed itself (rank "proc" = 11) follows by
       [locks_below_mono].  The not-killed branch (ut_ret / prepare_return)
       touches no lock at all. *)
    (* THE KEY'S GENERATION IS THE BLOCK'S, at the ecall cause (lane
       TRAP-ROWS, T2(ii)).  The syscall channel's answer is keyed at [gn]
       and <p->lock>'s killed row at [pv_gen (us_V U)]; refuting the read's
       one-shot against the row needs the two to be one, and the party that
       says so is the dispatcher.  GUARDED ON THE CAUSE, because the two
       fault arms that also end here have no such equation and no read
       either. *)
    (scw = uecall_scause -> gn = pv_gen (us_V U)) ->
    locks_below lks "log" ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xa6)) -∗
    sie_cap_gpr KT1 m nx b (un_pj N) -∗
    (* THE RESIDUE, AND WHO WOULD PAY A TEAR-DOWN AT THIS CHECK
       (design/pipe.md, "The exit path").  LEFT, the ordinary route: the
       block still carries the incarnation's marker, which is what lets the
       check read the KILLER's taint out of <p->lock>'s killed row
       ([SchedCtx.kill_paid_shot_tear] -- the marker refutes the SPENT arm,
       i.e. says this row was not founded by a self-kill) and what kexit
       trades for the row's payload; if the process resumes it simply goes
       back into the block.  RIGHT, after a SELF-KILL on the way here (the
       unexpected-cause arm's setkilled, at the deposit's untainted side):
       the marker is spent, the one-shot is already fired -- which is what
       refutes the not-killed branch below -- and the closes and the payload
       are the trap's own deposit (the exit bundle row and
       [ChildTok.kill_owed]'s payload). *)
    (ut_hold Rsys N U b lks sts cs2 pid
     ∨ (ut_hold_nm Rsys N U b lks sts cs2 pid
        ∗ ChildTok.kill_shot (pv_gen (us_V U)) ∗ fileclose_cpays sts
        ∗ sexit_pay fdep (-1))) -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    (* THE EXEC CHANNEL'S ANSWER, relayed exactly like the descriptor rows:
       this tail moves nothing the row reads -- [SpecUsertrap.ut_exec_out] *)
    ut_exec_out fdep scw (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) (us_M U0)
      (perm_of (ud_um (pv_upt (us_V U0))) (uint (pv_sz (us_V U0))))
      (uint (pv_sz (us_V U0))) (pv_lazy (us_V U0)) (pv_secc (us_V U0)) U sts0 sts gn cs pid -∗
    (* ...and FORK'S, relayed the same way -- [SpecUsertrap.ut_fork_out] *)
    ut_fork_out fdep scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 -∗
    (* ...and WAIT'S, beside it -- [SpecUsertrap.ut_wait_out] *)
    ut_wait_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (us_M U0) (us_M U)
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 gn pid -∗
    (* ...AND THE UNTAKEN CONTINUATION, OR THE FACT THAT THERE IS NO RESUME
       (lane TRAP-ROWS, T3).  This arm is the second [killed()] check, so it
       is the one place the two can be told apart: the shot refutes the
       not-killed branch against the row ([SchedCtx.kill_paid_shot_nz]) and
       the slot is what the resume owes -- [SpecUsertrap.ut_resume_in]. *)
    ut_resume_in scw Wk (pv_gen (us_V U)) -∗
    (* ...and the syscall channel's, relayed the same way: this tail moves
       nothing the row reads, and the a0 word it is read at is the one of
       the record it parks, at the resume view it parks it at --
       [SpecUsertrap.ut_sys_out] *)
    (∀ n : Z,
       ut_sys_out n fdep scw (pv_tf (us_V U0)) U0 sts0 gn cs pid
         (pv_tf (us_V U) !!! tf_arg_idx 0) (us_M U) sts (pv_cwi (us_V U)) cs2) -∗
    (* THE PAY FACT, CARRIED.  The process handed its knowledge over when
       it trapped ([SpecUsertrap.ut_pay_in]); NOTHING travels beside it any
       more (lane SELF-KILL, P6b) -- a kill is paid for by the KILLER, into
       <p->lock>'s own killed row.  The fact is at the ENTRY record's
       generation, which is the one every arm of this walk keeps
       ([SpecUsertrap.ut_gen_kept]), so the arms below carry it at the
       record they hold and the conversion at each hop is by the update's
       own definition. *)
    my_pay (pv_gen (us_V U)) (sexit_pay fdep) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0 U0 sts0 gn cs pid epw scw fdep Wk) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hwf Hgenk Hfdk Hchk Hfde Hpipe Hpidr Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv Hrd Hgna Hbelow.
    pose proof (ut_nx_bound b av nx Hav Hnx) as Hks.
    
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold0 Hframe Hxo Hfo Hwo Hres Hso #Hmyp Hcont".
    (* the residue and the tear-down's price, split apart once *)
    iAssert (ut_hold_nm Rsys N U b lks sts cs2 pid ∗
             (ChildTok.taken_at (pv_gen (us_V U))
              ∨ (ChildTok.kill_shot (pv_gen (us_V U)) ∗ fileclose_cpays sts
                 ∗ sexit_pay fdep (-1))))%I
      with "[Hhold0]" as "[Hhold Htear]".
    { iDestruct "Hhold0" as "[Hh | (Hh & #Hs & Hcp & HQd)]".
      - iDestruct (bi.equiv_entails_1_1 _ _
                     (ut_hold_unmark Rsys N U b lks sts cs2 pid) with "Hh")
          as "[$ Ht]". iLeft. iExact "Ht".
      - iFrame "Hh". iRight. iFrame "Hs Hcp HQd". }
    iDestruct "Hhold" as "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    iAssert (procs_inv (un_s N)) with "[]" as "#Hpi".
    { iDestruct "Hcaps" as "($ & _)". }
    (* ---- +0xa6: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (UT + 0xa6)) Ra0 Rs1 m nx b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [-]").
    { iApply (uti_0a6 with "Htext"). }
    iIntros (CID1 Hk1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget m Rs1))]> m).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget m Rs1))]> m)
      with M1.
    assert (Hppa8 : add_vec_int (mword_of_int (UT + 0xa6) : mword 64) 2
                    = mword_of_int (UT + 0xa8)) by pcw.
    iEval (rewrite Hppa8) in "Hpc".
    assert (HM1a0 : M1 !!! Regidx Ra0 = proc_addr (un_j N)).
    { rewrite /M1 upd_eq. rewrite (rget_ne (CID := CID) m Rs1
        ltac:(intro Hbad; injection Hbad as Hb2; vm_compute in Hb2; congruence)).
      rewrite Hms1 add_vec_zero_l. reflexivity. }
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    (* ---- +0xa8: jal killed ---- *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (UT + 0xa8)) Rra
              (mword_of_int 2095854 : mword 21) M1 nx b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc [] [-]").
    { iApply (uti_0a8 with "Htext"). }
    iIntros (CID2 Hk2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UT + 0xa8) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (UT + 0xa8) : mword 64) 4)]> M1) with M2.
    assert (Hkilled : add_vec (mword_of_int (UT + 0xa8) : mword 64)
                        (sign_extend' 64 (mword_of_int 2095854 : mword 21))
                      = mword_of_int KernelSyms.killed) by pcw.
    iEval (rewrite Hkilled) in "Hpc".
    assert (HM2a0 : M2 !!! Regidx Ra0 = proc_addr (un_j N))
      by (rewrite /M2 upd_ne; [exact HM1a0 | reg_neq]).
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    assert (HM2s1 : M2 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M2 upd_ne; [exact HM1s1 | reg_neq]).
    assert (HM2ra : M2 !!! Regidx Rra = mword_of_int (UT + 0xac))
      by (rewrite /M2 upd_eq; pcw).
    assert (HcsM2 : ut_cs m0 M2)
      by (rewrite /M2; apply ut_cs_insert; [vm_compute; reflexivity | exact HcsM1]).
    iDestruct (cpu_own_transport CID CID2 0%nat b (un_pj N) b
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    (* WHAT THIS READ IS FOR, AND THE TIE IT IS MADE AT (lane SELF-KILL,
       P6).  A nonzero flag means the incarnation's kill ONE-SHOT has been
       fired, and that fact -- persistent, and about a GENERATION -- is
       what [kexit] needs two critical sections later to take the killer's
       deposit out of the row.  <p->lock>'s payload names its generation
       only existentially, so the identification is made HERE, out of the
       dying process's OWN block: the quarter of [p->pid] says the row's
       cell is this slot's, and the registration eighth says the row's
       generation is this incarnation's ([ProcInv.proc_priv_pid_reg]).
       Both come straight back, because the two agreements are pure. *)
    iDestruct (ut_own_nm_priv with "Hown") as "(Hpv & Hufr & Hch & Hsy & Hownback)".
    (* the live slot's pid is nonzero -- the block says so, and it is what
       keeps [SchedCtx.kill_paid]'s free arm out of the reading (T3) *)
    iDestruct (ut_pid_nz_nm with "Hpv") as "%Hpidnz".
    iDestruct (ut_priv_nm_pid_reg with "Hpv") as "(Hqp & Hrg & Hpvback)".
    (* THE ACCESSOR CARRIES THE RESUME ROW INTO THE CRITICAL SECTION (lane
       TRAP-ROWS, T3).  The refutation can only happen HERE: at a zero flag
       the row holds the UNFIRED one-shot, and that is the one moment the
       shot can be contradicted -- [ChildTok.kill_pend] is linear and goes
       straight back, so no refuter can be carried out of the section.  So
       the accessor consumes [Hres] and hands back, under the zero-flag
       guard, the slot the resume owes. *)
    (* THE READ'S REASON, HOISTED OFF THE SYSCALL CHANNEL ONCE (lane
       TRAP-ROWS, T2(ii)).  Both of the receipt's -1 disjuncts are
       persistent, so the channel goes back untouched; the row's guard pins
       the number, so the rebuild is the same wand at the same [n].  The
       three readings the guard is stated at are the ENTRY frame's, and the
       prologue's one epc word is not one of them. *)
    assert (Ha0e : (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                     !!! tf_arg_idx 0
                   = pv_tf (us_V U0) !!! tf_arg_idx 0)
      by (rewrite list_lookup_total_insert_ne;
          [ reflexivity | unfold tf_epc_idx, tf_arg_idx; lia ]).
    assert (Ha2e : (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                     !!! tf_arg_idx 2
                   = pv_tf (us_V U0) !!! tf_arg_idx 2)
      by (rewrite list_lookup_total_insert_ne;
          [ reflexivity | unfold tf_epc_idx, tf_arg_idx; lia ]).
    assert (Hnume : usys_num (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                    = usys_num (pv_tf (us_V U0)))
      by apply usys_num_epc.
    iAssert ((□ (⌜ut_live_read_g scw (pv_secc (us_V U0))
                    (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
                    (pv_tf (us_V U) !!! tf_arg_idx 0)⌝ -∗
                 (⌜(sys_rw_count (pv_tf (us_V U0) !!! tf_arg_idx 2) < 0)%Z⌝
                  ∨ ChildTok.kill_shot (pv_gen (us_V U))))) ∗
             (∀ n : Z,
                ut_sys_out n fdep scw (pv_tf (us_V U0)) U0 sts0 gn cs pid
                  (pv_tf (us_V U) !!! tf_arg_idx 0) (us_M U) sts
                  (pv_cwi (us_V U)) cs2))%I
      with "[Hso]" as "(#Hrwhy & Hso)".
    { destruct (decide (ut_live_read_g scw (pv_secc (us_V U0))
                          (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
                          (pv_tf (us_V U) !!! tf_arg_idx 0))) as [Hgr | Hgr].
      - pose proof Hgr as Hgr2.
        destruct Hgr2 as (Hge & Hgn & Hgc & (rb & Hgfd) & Hgm1).
        rewrite Hnume in Hgn. rewrite Ha0e in Hgfd.
        iDestruct ("Hso" $! USYS_read with "[%]") as "Hsp".
        { split_and!; [ exact Hge | exact Hgn
                      | unfold USYS_read, USYS_exit; lia
                      | unfold USYS_read, USYS_fork; lia ]. }
        iDestruct (spost_at_read_why uslot fdep (uvis_of U0 sts0 gn cs pid) rb
                     (pv_tf (us_V U) !!! tf_arg_idx 0) (us_M U) sts
                     (pv_cwi (us_V U)) cs2 Hgfd Hgm1 with "Hsp")
          as "(#Hwhy & Hsp)".
        iEval (rewrite (Hgna Hge)) in "Hwhy".
        iSplitR.
        + iModIntro. iIntros "_". iExact "Hwhy".
        + iIntros (n) "%Hg2". destruct Hg2 as (_ & Hn2 & _ & _).
          assert (Hn5 : n = USYS_read) by (rewrite <- Hn2; exact Hgn).
          rewrite Hn5. iExact "Hsp".
      - iSplitR.
        + iModIntro. iIntros "%Hc". exfalso. exact (Hgr Hc).
        + iExact "Hso". }
    (* WAIT'S REASON, HOISTED OFF THE ANSWER THE SAME WAY (lane TRAP-ROWS-3,
       T4(c)).  At a -1 return the reaping arm is refuted by the reaped
       pid's own range ([SlotGen.gen_halves_at], spent in
       [UserChildren.wait_ans_m1]) and what is left is the failing arm,
       which is wholly PERSISTENT -- so the channel is rebuilt from its
       own reason and goes back untouched. *)
    iAssert ((□ (⌜ut_live_wait_g scw (pv_secc (us_V U0))
                    (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                    (pv_tf (us_V U) !!! tf_arg_idx 0)⌝ -∗
                 ⌜cs2 = cs⌝ ∗ wait_why cs (pv_gen (us_V U)) true)) ∗
             ut_wait_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
               (us_M U0) (us_M U)
               (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 gn pid)%I
      with "[Hwo]" as "(#Hwwhy & Hwo)".
    { destruct (decide (ut_live_wait_g scw (pv_secc (us_V U0))
                          (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                          (pv_tf (us_V U) !!! tf_arg_idx 0))) as [Hgw | Hgw].
      - pose proof Hgw as Hgw2.
        destruct Hgw2 as (Hge & Hgn & Hga0 & Hgm1).
        assert (Hnull : bool_decide ((<[tf_epc_idx := ret_pc epw]>
                                        (pv_tf (us_V U0))) !!! tf_arg_idx 0
                                     = (zero_reg : mword 64)) = true)
          by (apply bool_decide_eq_true_2; exact (zero_reg_of_uint _ Hga0)).
        iDestruct ("Hwo" with "[%]") as "Hw"; [ exact (conj Hge Hgn) | ].
        rewrite Hnull.
        iDestruct "Hw" as (rv xw) "[%Hr [%Hwr Ha]]".
        assert (Hsm1 : (sign_extend' 64 rv : mword 64)
                       = (mword_of_int (-1) : mword 64))
          by (rewrite <- Hr; exact Hgm1).
        iDestruct (wait_ans_m1 rv (xstate_val xw) cs cs2 gn true pid Hsm1 with "Ha")
          as "[%Hf #Hwhy]".
        destruct Hf as (Hrm & Hcse).
        iEval (rewrite (Hgna Hge)) in "Hwhy".
        iSplitR.
        + iModIntro. iIntros "_". iSplitR; [ iPureIntro; exact Hcse | ].
          iExact "Hwhy".
        + iIntros "_". rewrite Hnull. iExists rv, xw.
          iSplitR; [ iPureIntro; exact Hr | ].
          iSplitR; [ iPureIntro; exact Hwr | ].
          rewrite Hrm Hcse. iApply wait_ans_neg.
          iEval (rewrite <- (Hgna Hge)) in "Hwhy". iExact "Hwhy".
      - iSplitR.
        + iModIntro. iIntros "%Hc". exfalso. exact (Hgw Hc).
        + iExact "Hwo". }
    iAssert (∀ (pidr klr : mword 32),
               p_pid (proc_addr (un_j N)) ↦₄{DfracOwn (1/4)} pidr -∗
               SchedCtx.kill_paid pidr klr -∗
               p_pid (proc_addr (un_j N)) ↦₄{DfracOwn (1/4)} pidr ∗
               SchedCtx.kill_paid pidr klr ∗
               ((⌜klr = (mword_of_int 0 : mword 32)⌝
                 ∨ ChildTok.kill_shot (pv_gen (us_V U))) ∗
                (⌜klr = (mword_of_int 0 : mword 32)⌝ -∗
                   ut_kill_out scw Wk) ∗
                p_pid (un_pj N) ↦₄{DfracOwn (1/4)} pid ∗
                pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)) ∗
                (* ...AND WHAT THE ZERO FLAG PROVES ABOUT THE READ (lane
                   TRAP-ROWS, T2(iii)) *)
                (⌜klr = (mword_of_int 0 : mword 32)⌝ -∗
                   ⌜ut_live_out scw (pv_secc (us_V U0))
                      (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
                      (pv_tf (us_V U) !!! tf_arg_idx 0) cs2⌝) ∗
                  (* ...AND WHO WOULD PAY A TEAR-DOWN, read INSIDE the
                     critical section because that is where the row is
                     (design/pipe.md, "The exit path").  LEFT: the block's
                     own marker went in and came back, and with it the
                     KILLER's taint out of the row's paid arm -- which is
                     the package kexit takes, and at a zero flag the marker
                     simply goes back into the block.  RIGHT: a self-kill
                     happened on the way here, so there is no marker, the
                     flag cannot be zero, and the closes and the payload are
                     the trap's own deposit. *)
                  (((⌜klr = (mword_of_int 0 : mword 32)⌝
                     ∨ (ChildTok.kill_shot (pv_gen (us_V U)) ∗ app_taint))
                    ∗ ChildTok.taken_at (pv_gen (us_V U)))
                   ∨ (⌜klr <> (mword_of_int 0 : mword 32)⌝
                      ∗ ChildTok.kill_shot (pv_gen (us_V U))
                      ∗ fileclose_cpays sts ∗ sexit_pay fdep (-1)))))%I
      with "[Hqp Hrg Hres Htear]" as "Hkacc".
    { iIntros (pidr klr) "Hq Hr".
      iDestruct (ctx_word4_pointsto_agree with "Hq Hqp") as %->.
      (* THE ROW IS READ ONCE, BY WHICHEVER ROUTE GOT HERE.  With the
         marker, [kill_paid_shot_tear] proves the row was paid by a THIRD
         PARTY (the marker refutes the spent arm) and hands the taint out;
         after a self-kill there is no marker, but the one-shot is already
         in hand and refutes the zero flag outright. *)
      iAssert (SchedCtx.kill_paid pid klr ∗
               pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)) ∗
               (⌜klr = (mword_of_int 0 : mword 32)⌝
                ∨ ChildTok.kill_shot (pv_gen (us_V U))) ∗
                  (* ...AND WHO WOULD PAY A TEAR-DOWN, read INSIDE the
                     critical section because that is where the row is
                     (design/pipe.md, "The exit path").  LEFT: the block's
                     own marker went in and came back, and with it the
                     KILLER's taint out of the row's paid arm -- which is
                     the package kexit takes, and at a zero flag the marker
                     simply goes back into the block.  RIGHT: a self-kill
                     happened on the way here, so there is no marker, the
                     flag cannot be zero, and the closes and the payload are
                     the trap's own deposit. *)
                  (((⌜klr = (mword_of_int 0 : mword 32)⌝
                     ∨ (ChildTok.kill_shot (pv_gen (us_V U)) ∗ app_taint))
                    ∗ ChildTok.taken_at (pv_gen (us_V U)))
                   ∨ (⌜klr <> (mword_of_int 0 : mword 32)⌝
                      ∗ ChildTok.kill_shot (pv_gen (us_V U))
                      ∗ fileclose_cpays sts ∗ sexit_pay fdep (-1))))%I
        with "[Hr Hrg Htear]" as "(Hr & Hrg & Hs & Htear)".
      { iDestruct "Htear" as "[Htk | (#Hsh & Hcp & HQd)]".
        - iDestruct (SchedCtx.kill_paid_shot_tear pid klr (DfracOwn qeighth)
                       (pv_gen (us_V U)) with "Hr Hrg Htk")
            as "(Hr & Hrg & Htk & #Hs)".
          iFrame "Hr Hrg". iSplitR; [ | iLeft; iFrame "Hs Htk" ].
          iDestruct "Hs" as "[%Hz | [#Hsh _]]";
            [ iLeft; by iPureIntro | iRight; iExact "Hsh" ].
        - iDestruct (SchedCtx.kill_paid_shot_nz pid klr (DfracOwn qeighth)
                       (pv_gen (us_V U)) Hpidnz with "Hr Hrg Hsh")
            as "(Hr & Hrg & %Hne)".
          iFrame "Hr Hrg". iSplitR; [ iRight; iExact "Hsh" | ].
          iRight. iSplitR; [ by iPureIntro | ]. iFrame "Hsh Hcp HQd". }
      destruct (decide (klr = (mword_of_int 0 : mword 32))) as [Hkz | Hknz].
      - (* the flag is ZERO: the row's own [kill_pend] refutes a shot, so
           what [Hres] is carrying can only be the slot -- AND the read's
           own one-shot is refuted the same way, which is what makes its -1
           arm unreachable (lane TRAP-ROWS, T2(ii)). *)
        iAssert (⌜~ ut_live_read_g scw (pv_secc (us_V U0))
                     (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
                     (pv_tf (us_V U) !!! tf_arg_idx 0)⌝ ∗
                 SchedCtx.kill_paid pid klr ∗
                 pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)))%I
          with "[Hr Hrg]" as "(%Hnr & Hr & Hrg)".
        { destruct (decide (ut_live_read_g scw (pv_secc (us_V U0))
                              (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                              sts0 (pv_tf (us_V U) !!! tf_arg_idx 0)))
            as [Hgr | Hgr].
          - pose proof Hgr as Hgr2.
            destruct Hgr2 as (_ & _ & Hgc & _ & _).
            iDestruct ("Hrwhy" with "[%]") as "[%Hlt | #Hsh]"; [ exact Hgr | | ].
            + exfalso. rewrite Ha2e in Hgc. lia.
            + iDestruct (SchedCtx.kill_paid_shot_nz pid klr (DfracOwn qeighth)
                           (pv_gen (us_V U)) Hpidnz with "Hr Hrg Hsh")
                as "(Hr & Hrg & %Hne)". destruct (Hne Hkz).
          - iFrame "Hr Hrg". iPureIntro. exact Hgr. }
        (* ...AND THE SAME REFUTATION FOR THE WAIT CLAUSE (lane
           TRAP-ROWS-3, T4(c)).  At a null status pointer the failing arm's
           reason has three disjuncts; the guard kills the first, this
           zero flag kills the shot, and what is left is the caller's own
           children column at [∅] -- which the reap-nothing arm did not
           move. *)
        iAssert (⌜ut_live_wait_g scw (pv_secc (us_V U0))
                     (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                     (pv_tf (us_V U) !!! tf_arg_idx 0) ->
                   cs2 = (∅ : gset gname)⌝ ∗
                 SchedCtx.kill_paid pid klr ∗
                 pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)))%I
          with "[Hr Hrg]" as "(%Hnw & Hr & Hrg)".
        { destruct (decide (ut_live_wait_g scw (pv_secc (us_V U0))
                              (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
                              (pv_tf (us_V U) !!! tf_arg_idx 0)))
            as [Hgw | Hgw].
          - iDestruct ("Hwwhy" with "[%]") as "[%Hcse Hwhy]"; [ exact Hgw | ].
            rewrite /wait_why.
            iDestruct "Hwhy" as "[%Hbf | [%Hemp | #Hsh]]".
            + exfalso. discriminate Hbf.
            + iFrame "Hr Hrg". iPureIntro. intros _. rewrite Hcse. exact Hemp.
            + iDestruct (SchedCtx.kill_paid_shot_nz pid klr (DfracOwn qeighth)
                           (pv_gen (us_V U)) Hpidnz with "Hr Hrg Hsh")
                as "(Hr & Hrg & %Hne)". destruct (Hne Hkz).
          - iFrame "Hr Hrg". iPureIntro. intro Hc. exfalso. exact (Hgw Hc). }
        rewrite /ut_resume_in /ut_kill_out.
        destruct (decide (scw = UsysMemOk.uecall_scause)) as [_ | _].
        + iFrame "Hq Hr Hs Hqp Hrg Htear". iSplitR; [ by iIntros "_" | ].
          iIntros "_". iPureIntro. exact (ut_live_out_of _ _ _ _ _ Hnr Hnw).
        + iDestruct "Hres" as "[Hslot | #Hsh]".
          * iFrame "Hq Hr Hs Hqp Hrg Htear". iSplitL "Hslot".
            { iIntros "_". iExact "Hslot". }
            iIntros "_". iPureIntro. exact (ut_live_out_of _ _ _ _ _ Hnr Hnw).
          * iDestruct (SchedCtx.kill_paid_shot_nz pid klr (DfracOwn qeighth)
                         (pv_gen (us_V U)) Hpidnz with "Hr Hrg Hsh")
              as "(_ & _ & %Hne)". exfalso. exact (Hne Hkz).
      - (* the flag is NONZERO: this call takes the kexit branch and the
           resume row is never read. *)
        iFrame "Hq Hr Hs Hqp Hrg Htear". iSplitR.
        + iIntros "%Hkz". exfalso. exact (Hknz Hkz).
        + iIntros "%Hkz". exfalso. exact (Hknz Hkz). }
    iApply (KI.wp_killed_sconf (CID := CID2) (un_s N) (un_j N) (un_l N)
              M2 nx 0%nat b (un_pj N) b lks
              (fun (klv : mword 32) =>
                 ((⌜klv = (mword_of_int 0 : mword 32)⌝
                   ∨ ChildTok.kill_shot (pv_gen (us_V U))) ∗
                  (⌜klv = (mword_of_int 0 : mword 32)⌝ -∗
                     ut_kill_out scw Wk) ∗
                  p_pid (un_pj N) ↦₄{DfracOwn (1/4)} pid ∗
                  pid_reg pid (DfracOwn qeighth) (pv_gen (us_V U)) ∗
                  (⌜klv = (mword_of_int 0 : mword 32)⌝ -∗
                     ⌜ut_live_out scw (pv_secc (us_V U0))
                        (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
                        (pv_tf (us_V U) !!! tf_arg_idx 0) cs2⌝) ∗
                  (((⌜klv = (mword_of_int 0 : mword 32)⌝
                     ∨ (ChildTok.kill_shot (pv_gen (us_V U)) ∗ app_taint))
                    ∗ ChildTok.taken_at (pv_gen (us_V U)))
                   ∨ (⌜klv <> (mword_of_int 0 : mword 32)⌝
                      ∗ ChildTok.kill_shot (pv_gen (us_V U))
                      ∗ fileclose_cpays sts ∗ sexit_pay fdep (-1))))%I)
              HM2a0 Hj Hjl ltac:(vm_compute; reflexivity) ltac:(lia)
              ltac:(lkbelow)
              with "Hkacc Hcg Hcpu Htext Hpc Hpi [-]").
    all: try lkbelow.
    iIntros (CID3 Hk3 mf kl)
      "[%Hcskl %Hkla0] (#Hkw & Hkores & Hqp & Hrg & Hlvres & Htear) Hcg Hcpu Hpc".
    iDestruct ("Hpvback" with "Hqp Hrg") as "Hpv".
    iDestruct ("Hownback" $! U sts cs2 with "Hpv Hufr Hch Hsy") as "Hown".
    assert (Hretac : ret_pc (M2 !!! Regidx Rra) = mword_of_int (UT + 0xac))
      by (rewrite HM2ra; pcw).
    iEval (rewrite Hretac) in "Hpc".
    (* the two arm complements and the exit, moved to killed's resuming hart *)
    iDestruct (trap_csrs_ext_transport CID CID3 b (un_pj N)
                 ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
    iDestruct (cpu_claim_ext_transport CID CID3 b (un_pj N)
                 ltac:(wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_retarget CID CID3 true (un_pj N) _
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
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
    assert (Hrgmf : rget (CID := CID3) mf Ra0 = sign_extend' 64 kl).
    { rewrite (rget_ne (CID := CID3) mf Ra0
        ltac:(intro Hbad; injection Hbad as Hb2; vm_compute in Hb2; congruence)).
      exact Hkla0. }
    (* ---- +0xac: c.bnez a0 ---- *)
    destruct (neq_vec (sign_extend' 64 kl) (zero_reg : mword 64)) eqn:Hnz.
    - (* KILLED: [which_dev = 0; kexit(-1)] -- a dead end. *)
      iApply (wp_cbnez_taken_s_sconf (CID := CID3) (mword_of_int (UT + 0xac))
                (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx b Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hnz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (uti_0ac with "Htext"). }
      iApply bi.later_intro. iIntros (CID4 Hk4) "Hcg Hpc".
      assert (Hpf4 : add_vec (mword_of_int (UT + 0xac) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 36 : mword 8) ('b"0"))))
                     = mword_of_int (UT + 0xf4)) by pcw.
      iEval (rewrite Hpf4) in "Hpc".
      (* +0xf4 c.li s2,0 *)
      iApply (wp_cli_s_sconf (CID := CID4) (mword_of_int (UT + 0xf4)) Rs2
                (mword_of_int 0 : mword 6)
                (add_vec zero_reg (sign_extend' 64
                   (sign_extend' 12 (mword_of_int 0 : mword 6))))
                mf nx b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc [] [-]").
      { iApply (uti_0f4 with "Htext"). }
      iIntros (CID5 Hk5) "Hcg Hpc".
      set (K1 := <[Regidx Rs2 := regval_into_reg
                     (add_vec zero_reg (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 0 : mword 6))))]> mf).
      change (<[Regidx Rs2 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 0 : mword 6))))]> mf) with K1.
      assert (Hpf6 : add_vec_int (mword_of_int (UT + 0xf4) : mword 64) 2
                     = mword_of_int (UT + 0xf6)) by pcw.
      iEval (rewrite Hpf6) in "Hpc".
      (* +0xf6 c.li a0,-1 *)
      iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (UT + 0xf6)) Ra0
                (mword_of_int 63 : mword 6)
                (add_vec zero_reg (sign_extend' 64
                   (sign_extend' 12 (mword_of_int 63 : mword 6))))
                K1 nx b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc [] [-]").
      { iApply (uti_0f6 with "Htext"). }
      iIntros (CID6 Hk6) "Hcg Hpc".
      set (K2 := <[Regidx Ra0 := regval_into_reg
                     (add_vec zero_reg (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))))]> K1).
      change (<[Regidx Ra0 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))]> K1) with K2.
      assert (Hpf8 : add_vec_int (mword_of_int (UT + 0xf6) : mword 64) 2
                     = mword_of_int (UT + 0xf8)) by pcw.
      iEval (rewrite Hpf8) in "Hpc".
      (* +0xf8 jal kexit *)
      iApply (wp_jal_s_sconf (CID := CID6) (mword_of_int (UT + 0xf8)) Rra
                (mword_of_int 2095464 : mword 21) K2 nx b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc [] [-]").
      { iApply (uti_0f8 with "Htext"). }
      iIntros (CID7 Hk7) "Hcg Hpc".
      assert (Hkex : add_vec (mword_of_int (UT + 0xf8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095464 : mword 21))
                     = mword_of_int KernelSyms.kexit) by pcw.
      iEval (rewrite Hkex) in "Hpc".
      iDestruct (cpu_own_transport CID3 CID7 0%nat b (un_pj N) b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID3 CID7 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID3 CID7 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      (* ---- THE DYING THREAD'S STACK CLOSER, BUILT HERE.  usertrap was
         entered with sp AT THE PAGE TOP ([Hksp]), which is the one point in
         a trap round where the closer is free ([ProcDefs.kstack_closer_top]:
         nothing is owed above the top).  Wrapping usertrap's own frame
         around it re-anchors it at the sp the walk is running on -- and that
         frame is dead, because kexit does not return. ---- *)
      assert (HKsp : (<[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (UT + 0xf8) : mword 64) 4)]> K2)
                       !!! Regidx csp_rs1 = pa_stk ksp 4).
      { rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /K2 upd_ne; [| vm_compute; discriminate].
        rewrite /K1 upd_ne; [exact Hmfsp | vm_compute; discriminate]. }
      iAssert (is_kstack (un_pj N) (un_ks N)) as "#Hkstk".
      { iDestruct "Hcaps" as "(_ & _ & $ & _)". }
      iDestruct (ut_frame_stack with "Hframe") as "Hfr".
      iDestruct (kstack_closer_top (un_pj N) (un_ks N) av
                   ltac:(unfold KSTACK_AV; lia) with "Hkstk") as "Hkcl".
      iEval (rewrite Hksp) in "Hkcl".
      iDestruct (kstack_closer_frame (un_pj N) ksp av 4 ltac:(lia)
                   with "Hkcl Hfr") as "Hkcl4".
      iEval (rewrite -Hnx -HKsp) in "Hkcl4".
      (* THE TAIL'S KILLED ARM IS PAID AT -1, out of the payment the
         process deposited when it trapped.  This check is reached from
         EVERY arm of usertrap -- the syscall's, the device's and the
         unexpected-cause one -- which is why the row is owed at every
         cause ([SpecUsertrap.ut_pay_in]).
         ...AND THE DEPOSIT IS A WAND FROM THE KILL CREDENTIAL (lane
         KILL-PAY, K4(a)), which is what [killed] just handed back beside
         its NONZERO answer: this arm is the one where the flag is not
         zero, so [SpecKilled]'s left arm is refuted and the right one is
         the credential. *)
      assert (Hknz : kl <> (mword_of_int 0 : mword 32)).
      { intro Hz0. rewrite Hz0 in Hnz. vm_compute in Hnz. discriminate Hnz. }
      iAssert (ChildTok.kill_shot (pv_gen (us_V U)))%I with "[]" as "#Hshot".
      { iDestruct "Hkw" as "[%Hz0 | $]". exfalso; exact (Hknz Hz0). }
      iApply (ut_kexit (CID := CID7) Rsys N U
                (<[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0xf8) : mword 64) 4)]> K2)
                nx b lks sts cs2 pid (sexit_pay fdep) Hwf' ltac:(lia)
                ltac:(eapply ut_kexit_status_neg1;
                      [ rewrite upd_ne;
                        [ subst K2; apply upd_eq | vm_compute; discriminate ]
                      | vm_compute; reflexivity ])
                ltac:(lkbelow)
                with "Htext Hpc Hcg Hkcl4 Hmyp [Htear] [-]").
      (* THE TEAR-DOWN'S PRICE, at the flag this branch read (design/pipe.md,
         "The exit path").  The flag is NONZERO, so the row's zero arm is
         refuted and what is left is the pair the check brought out: the
         KILLER's taint beside the block's marker, or -- after a self-kill
         on the way here -- the trap's own closes and payload. *)
      { iDestruct "Htear" as "[[Hs Htk] | (_ & #Hsh & Hcp & HQd)]".
        - iLeft. iDestruct "Hs" as "[%Hz | [#Hsh2 #Hc]]";
            [ exfalso; exact (Hknz Hz) | ]. iFrame "Hsh2 Htk Hc".
        - iRight. iFrame "Hcp HQd". }
      rewrite /ut_hold_nm. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      iSplitR; [iExact "Hcaps" | iExact "Hown"].
    - (* NOT killed: fall through to +0xae. *)
      (* THE MARKER GOES BACK INTO THE BLOCK.  The flag is zero, so the
         self-kill arm of the tear-down row is refuted -- a self-kill has
         already fired the one-shot -- and what is left is the marker this
         check lent the row and got back (design/pipe.md, "The exit
         path"). *)
      iDestruct "Htear" as "[[_ Htk] | (%Hne & _)]";
        [ | exfalso; exact (Hne (ut_kl_zero_of_branch kl Hnz)) ].
      iAssert (ut_own Rsys N U sts cs2 pid) with "[Hown Htk]" as "Hown".
      { iApply (bi.equiv_entails_1_2 _ _ (ut_own_unmark Rsys N U sts cs2 pid)).
        iFrame "Hown Htk". }
      (* ...AND THE RESUME ROW IS CASHED HERE (lane TRAP-ROWS, T3): the
         flag is zero, which is the guard the accessor's answer is under. *)
      iDestruct ("Hkores" with "[%]") as "Hko";
        [ exact (ut_kl_zero_of_branch kl Hnz) | ].
      (* ...AND THE READ'S ROW WITH IT (lane TRAP-ROWS, T2(iii)) *)
      iDestruct ("Hlvres" with "[%]") as "%Hlivea6";
        [ exact (ut_kl_zero_of_branch kl Hnz) | ].
      iApply (wp_cbnez_fall_s_sconf (CID := CID3) (mword_of_int (UT + 0xac))
                (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mf nx b Hc2 ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrgmf; exact Hnz)
                with "Hcg Hpc [] [-]").
      { iApply (uti_0ac with "Htext"). }
      iIntros (CID4 Hk4) "Hcg Hpc".
      assert (Hpae : add_vec_int (mword_of_int (UT + 0xac) : mword 64) 2
                     = mword_of_int (UT + 0xae)) by pcw.
      iEval (rewrite Hpae) in "Hpc".
      iDestruct (cpu_own_transport CID3 CID4 0%nat b (un_pj N) b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID3 CID4 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID3 CID4 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iDestruct (wp_next_retarget CID3 CID4 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ut_ret (CID := CID4) Rsys N U0 U pt ksp m0 mf av nx b
                mie_v menvcfg0 epw scw lks sts0 sts gn cs cs2 pid fdep Wk
                Hwf' ltac:(exact Hgenk) Hfdk Hchk Hfde Hpipe Hpidr Hav Hnx Htfpe Hksp Hm0sp Hmfsp Hmfs1 Hcsmf
                Hmiev Hmenvv Hrd Hlivea6
                with "Htext Hpc Hcg [-Hframe Hxo Hfo Hwo Hko Hso Hcont] Hframe Hxo Hfo Hwo Hko Hso
                      Hmyp Hcont").
      rewrite /ut_hold. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtA6.

Section UtFa.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (Rsys : gname -> mword 64 -> fclose_names -> iProp Σ).

  (* ==================================================================== *)
  (* +0xfc:  if (which_dev == 2) yield();   then +0xae                     *)
  (* ==================================================================== *)
  (* The timer arm's park.  It needs NO premise about [s2]: the block only
     branches on it, and both branches land on [ut_ret].  yield is the one
     callee here that takes the trap-CSR set and the running claim and gives
     them BACK -- it parks and resumes, so its crossing is real and everything
     has to be re-anchored on the far side. *)
  Lemma ut_fa (N : ut_names) (U0 U : ustate) (pt : uptd) (ksp : mword 64)
      (m0 m : regfile) (av nx : nat) (b : bool)
      (mie_v menvcfg0 epw scw : mword 64) (lks : gset string)
      (* TWO DESCRIPTOR INDICES, and the difference is the point: [sts0] is
         what usertrap was ENTERED at -- the index the caller's post is
         stated against -- and [sts] is what this tail is parking.  They
         differ on exactly one arm. *)
      (sts0 sts : list fdstate) (gn : gname) (cs cs2 : gset gname)
      (pid : mword 32)
      (* the deposit's families, relayed with the syscall channel's row *)
      (fdep : sfam) (Wk : UexecSlot.uvis) :
    ut_wf N ->
    (* THE GENERATION THE WALK KEPT: the post is stated at the ENTRY record
       and this tail parks the one it was handed.  No arm re-incarnates the
       slot, so the two name one generation, and the caller -- which built
       the second record out of the first -- is the party that says so
       ([SpecUsertrap.ut_gen_kept]).  The payment this tail carries is
       keyed by it too. *)
    ut_gen_kept U0 U ->
    (* the round's descriptor half, as this tail's caller certifies it.  The
       fault and timer arms pass one list twice and prove it by
       [reflexivity]; the syscall arm may have moved them, and its cause IS
       the ecall, so its proof is vacuous. *)
    ut_fd_kept scw sts0 sts ->
    (* ...and the children set's, on the same terms: every entry but fork
       keeps it, and fork's move is the kernel's answer, not a pure row
       ([SpecUsertrap.ut_ch_kept]). *)
    ut_ch_kept scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) cs cs2 ->
    (* ...and the ECALL's half, the row the syscall table states.  Relayed
       exactly like [ut_fd_kept]: the tail re-closes the residue with the
       fragments it borrowed, so whether the round moved the states -- and
       how -- is its caller's statement to make.  The row reads the syscall
       number and its argument off the trapframe usertrap was ENTERED at,
       and the return value out of the one being
       parked -- the ENTRY record is [U0], which these tails already carry
       for [ut_wf]. *)
    ut_fd_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) sts0 sts ->
    (* ...and pipe's join, off the same two records and the same pair of
       images: these tails move neither, so it rides across exactly as the
       descriptor row does. *)
    ut_pipe_ecall scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U))
                  (us_M U0) (us_M U) sts0 sts ->
    (* ...and getpid's answer, off the same two records: these tails move
       neither the number nor the a0 word, so it rides across exactly as
       the descriptor and pipe rows do ([SpecUsertrap.ut_ret_pid]). *)
    ut_ret_pid scw (pv_secc (us_V U0)) (pv_tf (us_V U0)) (pv_tf (us_V U)) pid ->
    (K_usertrap <= av)%nat ->
    (trap_res b + nx)%nat = (av - 4)%nat ->
    ud_tfp (pv_upt (us_V U)) = ud_tfp pt ->
    add_vec (un_ks N) (mword_of_int 4096) = ksp ->
    m0 !!! Regidx csp_rs1 = ksp ->
    m !!! Regidx csp_rs1 = pa_stk ksp 4 ->
    m !!! Regidx Rs1 = un_pj N ->
    ut_cs m0 m ->
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    (* THE ROUND SO FAR (milestone J1a) -- see [SpecUsertrap.ut_round]. *)
    ut_round epw scw U0 U ->
    (* ...AND WHAT A RESUME PROVES, relayed to the post (lane TRAP-ROWS,
       T2(iii)): +0xa6's [killed] check refuted the read's shot, and this
       tail only carries the conclusion -- [SpecUsertrap.ut_live_out]. *)
    ut_live_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) sts0
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs2 ->
    kernel_text -∗
    pc_is (mword_of_int (UT + 0xfc)) -∗
    sie_cap_gpr KT1 m nx b (un_pj N) -∗
    ut_hold Rsys N U b lks sts cs2 pid -∗
    ut_frame ksp (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0)
                 (m0 !!! Regidx Rs1) (m0 !!! Regidx Rs2) -∗
    (* THE EXEC CHANNEL'S ANSWER, relayed exactly like the descriptor rows:
       this tail moves nothing the row reads -- [SpecUsertrap.ut_exec_out] *)
    ut_exec_out fdep scw (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0))) (us_M U0)
      (perm_of (ud_um (pv_upt (us_V U0))) (uint (pv_sz (us_V U0))))
      (uint (pv_sz (us_V U0))) (pv_lazy (us_V U0)) (pv_secc (us_V U0)) U sts0 sts gn cs pid -∗
    (* ...and FORK'S, relayed the same way -- [SpecUsertrap.ut_fork_out] *)
    ut_fork_out fdep scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 -∗
    (* ...and WAIT'S, beside it -- [SpecUsertrap.ut_wait_out] *)
    ut_wait_out scw (pv_secc (us_V U0)) (<[tf_epc_idx := ret_pc epw]> (pv_tf (us_V U0)))
      (us_M U0) (us_M U)
      (pv_tf (us_V U) !!! tf_arg_idx 0) cs cs2 gn pid -∗
    (* ...AND THE UNTAKEN CONTINUATION (lane TRAP-ROWS, T3) *)
    ut_kill_out scw Wk -∗
    (* ...and the syscall channel's, relayed the same way: this tail moves
       nothing the row reads, and the a0 word it is read at is the one of
       the record it parks, at the resume view it parks it at --
       [SpecUsertrap.ut_sys_out] *)
    (∀ n : Z,
       ut_sys_out n fdep scw (pv_tf (us_V U0)) U0 sts0 gn cs pid
         (pv_tf (us_V U) !!! tf_arg_idx 0) (us_M U) sts (pv_cwi (us_V U)) cs2) -∗
    (* THE PAY FACT, CARRIED.  The process handed its knowledge over when
       it trapped ([SpecUsertrap.ut_pay_in]); NOTHING travels beside it any
       more (lane SELF-KILL, P6b) -- a kill is paid for by the KILLER, into
       <p->lock>'s own killed row.  The fact is at the ENTRY record's
       generation, which is the one every arm of this walk keeps
       ([SpecUsertrap.ut_gen_kept]), so the arms below carry it at the
       record they hold and the conversion at each hop is by the update's
       own definition. *)
    my_pay (pv_gen (us_V U)) (sexit_pay fdep) -∗
    wp_next true (un_pj N)
      (fun CID' => usertrap_post (CID := CID') (ut_res (CID := CID') Rsys) pt ksp m0
                     mie_v menvcfg0 U0 sts0 gn cs pid epw scw fdep Wk) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hwf Hgenk Hfdk Hchk Hfde Hpipe Hpidr Hav Hnx Htfpe Hksp Hm0sp Hmsp Hms1 Hcs Hmiev Hmenvv Hrd Hlive.
    pose proof (ut_nx_bound b av nx Hav Hnx) as Hks.
    
    pose proof Hwf as Hwf'. destruct Hwf as (Hj & Hjl & Hlen & Hlg).
    iIntros "#Htext Hpc Hcg Hhold Hframe Hxo Hfo Hwo Hko Hso #Hmyp Hcont".
    iDestruct "Hhold" as "(Hcpu & Hcsrs & Hclm & [#Hcaps Hown])".
    (* depth 0 forces the held set empty, which is what lets the yield arm
       hand [cpu_own ... ∅] to a contract that pins [∅] (SpecYield.v). *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    iAssert (procs_inv (un_s N)) with "[]" as "#Hpi".
    { iDestruct "Hcaps" as "($ & _)". }
    (* ---- +0xfc: c.li a5,2 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (UT + 0xfc)) Ra5 (mword_of_int 2 : mword 6)
              (add_vec zero_reg (sign_extend' 64
                 (sign_extend' 12 (mword_of_int 2 : mword 6))))
              m nx b ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc [] [-]").
    { iApply (uti_0fc with "Htext"). }
    iIntros (CID1 Hk1) "Hcg Hpc".
    set (M1 := <[Regidx Ra5 := regval_into_reg
                   (add_vec zero_reg (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 2 : mword 6))))]> m).
    change (<[Regidx Ra5 := regval_into_reg
               (add_vec zero_reg (sign_extend' 64
                  (sign_extend' 12 (mword_of_int 2 : mword 6))))]> m) with M1.
    assert (Hpfe : add_vec_int (mword_of_int (UT + 0xfc) : mword 64) 2
                   = mword_of_int (UT + 0xfe)) by pcw.
    iEval (rewrite Hpfe) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 4)
      by (rewrite /M1 upd_ne; [exact Hmsp | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = un_pj N)
      by (rewrite /M1 upd_ne; [exact Hms1 | reg_neq]).
    assert (HcsM1 : ut_cs m0 M1)
      by (rewrite /M1; apply ut_cs_insert; [vm_compute; reflexivity | exact Hcs]).
    (* ---- +0xfe: bne s2,a5 -> +0xae ---- *)
    destruct (neq_vec (rget (CID := CID1) M1 Rs2)
                      (rget (CID := CID1) M1 Ra5)) eqn:Hne.
    - (* which_dev <> 2: straight to +0xae *)
      iApply (wp_bne_taken_s_sconf (CID := CID1) (mword_of_int (UT + 0xfe))
                (mword_of_int 8112 : mword 13) Ra5 Rs2 M1 nx b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hne ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (uti_0fe with "Htext"). }
      iApply bi.later_intro. iIntros (CID2 Hk2) "Hcg Hpc".
      assert (Hpae : add_vec (mword_of_int (UT + 0xfe) : mword 64)
                       (sign_extend' 64 (mword_of_int 8112 : mword 13))
                     = mword_of_int (UT + 0xae)) by pcw.
      iEval (rewrite Hpae) in "Hpc".
      iDestruct (cpu_own_transport CID CID2 0%nat b (un_pj N) b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID CID2 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID CID2 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iDestruct (wp_next_retarget CID CID2 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ut_ret (CID := CID2) Rsys N U0 U pt ksp m0 M1 av nx b
                mie_v menvcfg0 epw scw lks sts0 sts gn cs cs2 pid fdep Wk
                Hwf' ltac:(exact Hgenk) Hfdk Hchk Hfde Hpipe Hpidr Hav Hnx Htfpe Hksp Hm0sp HM1sp HM1s1 HcsM1
                Hmiev Hmenvv Hrd Hlive
                with "Htext Hpc Hcg [-Hframe Hxo Hfo Hwo Hko Hso Hcont] Hframe Hxo Hfo Hwo Hko Hso
                      Hmyp Hcont").
      rewrite /ut_hold. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
    - (* which_dev == 2: yield(), then +0xae *)
      iApply (wp_bne_fall_s_sconf (CID := CID1) (mword_of_int (UT + 0xfe))
                (mword_of_int 8112 : mword 13) Ra5 Rs2 M1 nx b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hne with "Hcg Hpc [] [-]").
      { iApply (uti_0fe with "Htext"). }
      iIntros (CID2 Hk2) "Hcg Hpc".
      assert (Hp102 : add_vec_int (mword_of_int (UT + 0xfe) : mword 64) 4
                      = mword_of_int (UT + 0x102)) by pcw.
      iEval (rewrite Hp102) in "Hpc".
      (* +0x102 jal yield *)
      iApply (wp_jal_s_sconf (CID := CID2) (mword_of_int (UT + 0x102)) Rra
                (mword_of_int 2095114 : mword 21) M1 nx b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc [] [-]").
      { iApply (uti_102 with "Htext"). }
      iIntros (CID3 Hk3) "Hcg Hpc".
      set (M2 := <[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (UT + 0x102) : mword 64) 4)]> M1).
      change (<[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (UT + 0x102) : mword 64) 4)]> M1)
        with M2.
      assert (Hyield : add_vec (mword_of_int (UT + 0x102) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095114 : mword 21))
                       = mword_of_int KernelSyms.yield) by pcw.
      iEval (rewrite Hyield) in "Hpc".
      assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
      assert (HM2s1 : M2 !!! Regidx Rs1 = un_pj N)
        by (rewrite /M2 upd_ne; [exact HM1s1 | reg_neq]).
      assert (HM2ra : M2 !!! Regidx Rra = mword_of_int (UT + 0x106))
        by (rewrite /M2 upd_eq; pcw).
      assert (HcsM2 : ut_cs m0 M2)
        by (rewrite /M2; apply ut_cs_insert;
            [vm_compute; reflexivity | exact HcsM1]).
      iDestruct (cpu_own_transport CID CID3 0%nat b (un_pj N) b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID CID3 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID CID3 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iEval (rewrite Hlkempty) in "Hcpu".
      iApply (YI.wp_yield_sconf (CID := CID3) (un_s N) (un_j N) (un_l N)
                M2 nx b Hj Hjl ltac:(lia)
                with "Hcg Hcpu Htext Hpc Hpi Hcsrs Hclm [-]").
      iIntros (CID4 Hk4 mf) "%Hcsy Hcg Hcpu Hpc Hcsrs Hclm".
      assert (Hret106 : ret_pc (M2 !!! Regidx Rra) = mword_of_int (UT + 0x106))
        by (rewrite HM2ra; pcw).
      iEval (rewrite Hret106) in "Hpc".
      iDestruct (wp_next_retarget CID CID4 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* +0x106 c.j +0xae *)
      iApply (wp_cj_s_sconf (CID := CID4) (mword_of_int (UT + 0x106))
                (sign_extend' 21 (concat_vec (mword_of_int 2004 : mword 11) ('b"0")))
                mf nx b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [-]").
      { iApply (uti_106 with "Htext"). }
      iIntros (CID5 Hk5). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hpae2 : add_vec (mword_of_int (UT + 0x106) : mword 64)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 2004 : mword 11) ('b"0"))))
                      = mword_of_int (UT + 0xae)) by pcw.
      iEval (rewrite Hpae2) in "Hpc".
      assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 4)
        by (rewrite (callee_saved_lookup Hcsy csp_rs1
                       ltac:(vm_compute; reflexivity)); exact HM2sp).
      assert (Hmfs1 : mf !!! Regidx Rs1 = un_pj N)
        by (rewrite (callee_saved_lookup Hcsy Rs1
                       ltac:(vm_compute; reflexivity)); exact HM2s1).
      assert (Hcsmf : ut_cs m0 mf)
        by exact (ut_cs_trans m0 M2 mf HcsM2 (ut_cs_of_callee_saved _ _ Hcsy)).
      iDestruct (cpu_own_transport CID4 CID5 0%nat b (un_pj N) b
                   ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iDestruct (trap_csrs_ext_transport CID4 CID5 b (un_pj N)
                   ltac:(wp_next_chain) with "Hcsrs") as "Hcsrs".
      iDestruct (cpu_claim_ext_transport CID4 CID5 b (un_pj N)
                   ltac:(wp_next_chain) with "Hclm") as "Hclm".
      iDestruct (wp_next_retarget CID4 CID5 true (un_pj N) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ut_ret (CID := CID5) Rsys N U0 U pt ksp m0 mf av nx b
                mie_v menvcfg0 epw scw lks sts0 sts gn cs cs2 pid fdep Wk
                Hwf' ltac:(exact Hgenk) Hfdk Hchk Hfde Hpipe Hpidr Hav Hnx Htfpe Hksp Hm0sp Hmfsp Hmfs1 Hcsmf
                Hmiev Hmenvv Hrd Hlive
                with "Htext Hpc Hcg [-Hframe Hxo Hfo Hwo Hko Hso Hcont] Hframe Hxo Hfo Hwo Hko Hso
                      Hmyp Hcont").
      (* the yield arm came back at the literal [∅]; [lks = ∅] at depth 0
         makes that the set [ut_hold] names. *)
      rewrite /ut_hold Hlkempty. iSplitL "Hcpu"; [iExact "Hcpu"|].
      iSplitL "Hcsrs"; [iExact "Hcsrs"|].
      iSplitL "Hclm"; [iExact "Hclm"|].
      rewrite /ut_env. iSplitR; [iExact "Hcaps" | iExact "Hown"].
  Qed.

End UtFa.

End UtTail.
