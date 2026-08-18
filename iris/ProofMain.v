(* ProofMain.v -- the whole-function WP for xv6's main(), BOOT-HART arm.

     volatile static int started = 0;
     void main() {
       if (cpuid() == 0) {
         consoleinit(); printkinit();
         printk("\n"); printk("xv6 kernel is booting\n"); printk("\n");
         kinit(); kvminit(); kvminithart(); procinit();
         trapinit(); trapinithart(); plicinit(); plicinithart();
         binit(); iinit(); fileinit(); virtio_disk_init(); userinit();
         __atomic_thread_fence(__ATOMIC_SEQ_CST);
         started = 1;
       } else { ... }
       scheduler();
     }

   A sealed functor over the eighteen callee interfaces plus KERNELVEC (whose
   handler contract is what turns trapinithart's [stvec ↦ᵣ kernelvec] into the
   [intr_res] scheduler wants).  main NEVER RETURNS, so there is no
   epilogue, no [callee_saved] obligation and no register to restore -- the only
   register fact the proof threads across the sixteen calls is
   [tp = cid_word], which every callee in the kalloc/lock cone requires.

   STRUCTURE.  One [Local Lemma] per call block, each concluding at the next
   offset, chained by [wp_main_boot_sconf]:

     mn_boot_entry  0x00 -> 0x42   frame push, jal cpuid, beqz TAKEN
     mn_grp_printk  0x42 -> 0x6e   consoleinit printkinit printk x3
                                   + the [pr] newlock and the printk_env
                                     assembly
     mn_grp_kvm     0x6e -> 0x7e   kinit kvminit kvminithart procinit
                                   + kalloc_env, THE TABLE PUBLICATION
                                     (persist root, kvm_M_mint,
                                      kpt_inv_alloc), procs_inv_alloc
     mn_grp_trap    0x7e -> 0x8e   trapinit trapinithart plicinit plicinithart
                                   + intr_inv_alloc_off
     mn_grp_fs      0x8e -> 0xa2   binit iinit fileinit virtio_disk_init
                                     userinit
                                   + disk_res_boot, the vdisk newlock
     mn_grp_started 0xa2 -> (join) fence, started = 1, j 0x3e, jal scheduler

   Everything a group does not touch stays in the caller's context: the group
   lemmas' conclusion is a bare [WP Loop {{Φ}}], so the top-level proof keeps
   [trap_csrs], [started_inv], the deposit wand and the persistent ambient
   facts across all of them.  Resources nothing consumes (the cons/tx_lock/
   tickslock/bcache/itable/ftable [lk_fresh]s, binit/iinit's outputs,
   userinit's [initproc] cell, the leftover pages, the frame slots) are simply
   DROPPED -- Iris is affine. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List Ascii String.
From stdpp Require Import gmap list list_numbers finite bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import RiscvFetchExec MinstretInv MemAccessGen.
Require Import SmodeCore RegFile HartTp WpNext WpMmodeLeafBase InstrBytes.
Require Import StackOwn.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import WpLock.
Require Import KallocInv KvmSpec PageGeom.
(* the shared kernel page table: main's OWN publication assembly spends
   [kpt_unset] + [kmap_auth kmap_M0] here ([WpKvminithart.kvm_M_mint],
   [KptShare.kpt_inv_alloc], [KvmMap.kvm_bridge]) and the deposit wand
   carries the resulting [kpt_inv] / 65 claims / persistent root cell *)
Require Import KptGhost KptShare KptExecMap KvmMap.
(* K1 of the KSTACK campaign: the boot-arm mint of the 64 kernel stacks *)
Require Import KstackOwn.
Require Import PtreeType.
Require Import WpKvminithart.
Require Import ProcGeom CpuOwn SchedCtx FdSlots.
Require Import FileInvDefs.
Require Import BcacheInv SleepLock.
Require Import DevModel VirtioModel DiskPtsto WpUart.
Require Import VirtioQueue VirtioProto DiskInv DiskBoot.
Require Import PrintkFmt.
Require Import StartedInv.
Require Import SpecCpuid SpecConsoleinit SpecPrintkinit SpecPrintk.
Require Import SpecKinit SpecKvminit SpecKvminithart SpecProcinit.
Require Import SpecTrapinit SpecTrapinithart SpecPlicinit SpecPlicinithart.
Require Import SpecBinit SpecIinit SpecFileinit SpecVirtioDiskInit.
Require Import SpecUserinit SpecScheduler SpecKernelvec SpecFreerange.
Require Import SpecDevintr SpecClockintr TicksInv.
Require Import KMap.
Require Import UartTxInv.
Require Import ConsoleInv SpecConsoleintr.
Require Import SpecMain.
Require Import CodeMain.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.
Local Strategy 1000 [pa_stk].

(* ===================================================================== *)
(* The two format strings main passes to printk, and the addresses the     *)
(* auipc/addi pairs resolve to.  Both live in .rodata just above etext.    *)
(* Hoisted as NAMED pure lemmas (never inline [ltac:] arguments to         *)
(* [kernel_data_string] -- claude-notes/optimization.md).                  *)
(* ===================================================================== *)
Definition mn_nl : string := String (Ascii.ascii_of_nat 10) EmptyString.
Definition mn_boot : string := ("xv6 kernel is booting" ++ mn_nl)%string.
Definition mn_nl_addr : Z := 0x80007078.
Definition mn_boot_addr : Z := 0x80007080.

Lemma mn_nl_bytes : forall j b, cstring_bytes mn_nl !! j = Some b ->
  KernelData.kernel_data !! (mn_nl_addr + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 2 (destruct j as [|j];
        [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma mn_boot_bytes : forall j b, cstring_bytes mn_boot !! j = Some b ->
  KernelData.kernel_data !! (mn_boot_addr + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 23 (destruct j as [|j];
         [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma mn_nl_fmt : pk_kinds mn_nl = [] /\ nonul mn_nl = true /\
                  (Z.of_nat (String.length mn_nl) < 2147483645)%Z.
Proof. split_and!; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Lemma mn_boot_fmt : pk_kinds mn_boot = [] /\ nonul mn_boot = true /\
                    (Z.of_nat (String.length mn_boot) < 2147483645)%Z.
Proof. split_and!; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

(* clean-context (mword-free) nat arithmetic, so [lia] never sees a bv *)
(* the third conjunct is the SCHEDULER's, and it is what [K_main] is sized by:
   the loop-head enable funds [kv_frame_slots] out of what main hands it. *)
Lemma mn_bounds (K : nat) : (K_main <= K)%nat ->
  (2 <= K)%nat /\ (K_userinit <= K - 2)%nat /\ (kv_frame_slots + 20 <= K - 2)%nat.
Proof. lia. Qed.

(* ===================================================================== *)
Module MainProof
  (Cpuid : CPUID) (Consoleinit : CONSOLEINIT) (Printkinit : PRINTKINIT)
  (PrintkGen : PRINTK_GEN) (Kinit : KINIT) (Kvminit : KVMINIT)
  (Kvminithart : KVMINITHART) (Procinit : PROCINIT) (Trapinit : TRAPINIT)
  (Trapinithart : TRAPINITHART) (Plicinit : PLICINIT)
  (Plicinithart : PLICINITHART) (Binit : BINIT) (Iinit : IINIT)
  (Fileinit : FILEINIT) (VirtioDiskInit : VIRTIODISKINIT)
  (Userinit : USERINIT) (Scheduler : SCHEDULER) (Kernelvec : KERNELVEC)
  : MAIN.

Section ProofMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* [hw_config] + [minstret_inv], both persistent, out of the ambient
     bundle -- what [Kernelvec.kernelvec_handler_spec] consumes. *)
  Local Lemma mn_dup_hw {kt : ktier} m avail b p :
    sie_cap_gpr kt m avail b p -∗ hw_config ∗ minstret_inv ∗ sie_cap_gpr kt m avail b p.
  Proof.
    iIntros "Hcg".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hsie & Hgpr)".
    iEval (rewrite /sconf) in "Hsc".
    iDestruct "Hsc" as "(#Hhw & #Hmin & Hrest)".
    iSplitR; [iExact "Hhw"|]. iSplitR; [iExact "Hmin"|].
    iApply (sie_cap_gpr_join with "Hhs [Hrest] Hsie Hgpr").
    rewrite /sconf. iSplitR; [iExact "Hhw"|].
    iSplitR; [iExact "Hmin" | iExact "Hrest"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [VirtioDiskInit]'s contract still carries a RAW-MAP tp premise       *)
  (* ([m !!! Regidx Rtp = cid_word]) that the rest of the sweep has shed, *)
  (* and [SpecMain] hands main no tp fact about its entry map -- so there *)
  (* is nothing left to thread to it.  It is satisfiable regardless: the  *)
  (* PINNED map trivially has it ([rget_tp]), and re-pointing the bundle  *)
  (* at [tp_pin m] changes nothing observable, since [tp_pin] is          *)
  (* idempotent and never touches sp.  Same move ProofCopyin /            *)
  (* ProofCopyout make for vmfault's identical leftover premise.          *)
  (* ------------------------------------------------------------------ *)
  Local Lemma mn_pin_sie_cap_gpr {kt : ktier} (M : regfile) (avail : nat) (bb : bool)
      (pp : mword 64) :
    sie_cap_gpr kt M avail bb pp -∗ sie_cap_gpr kt (tp_pin M) avail bb pp.
  Proof.
    rewrite /sie_cap_gpr /sie_cap (tp_pin_sp M).
    assert (Htp2 : tp_pin (tp_pin M) = tp_pin M)
      by (apply tp_pin_id; exact (rget_tp M)).
    rewrite Htp2. iIntros "$".
  Qed.

  Local Lemma mn_tp_pin_ne (M : regfile) (k : mword 5) :
    Regidx k <> Regidx Rtp -> tp_pin M !!! Regidx k = M !!! Regidx k.
  Proof. exact (rget_ne M k). Qed.

  (* =================================================================== *)
  (* 0x00 .. 0x14 -- the frame push, [jal cpuid], and the [beqz a0] that  *)
  (* the boot premise [cid_word = 0] makes TAKEN into the boot arm.       *)
  (* =================================================================== *)
  Local Lemma mn_boot_entry 
      (m : regfile) (K : nat) (p0 : mword 64) :
    cid_word = (zero_reg : mword 64) ->
    (K_main <= K)%nat ->
    sie_cap_gpr KT0 m K false p0 -∗ kernel_text -∗
    pc_is (mword_of_int KernelSyms.main : mword 64) -∗
    ( ∀ m1 : regfile,
        sie_cap_gpr KT0 m1 (K - 2)%nat false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0x42) : mword 64) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hcid HK.
    pose proof (mn_bounds K HK) as (Hc2 & Hn50 & Hnsched).
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (mni_00 with "Htext") as "Hi00".
    iPoseProof (mni_02 with "Htext") as "Hi02".
    iPoseProof (mni_04 with "Htext") as "Hi04".
    iPoseProof (mni_06 with "Htext") as "Hi06".
    iPoseProof (mni_08 with "Htext") as "Hi08".
    iPoseProof (mni_0c with "Htext") as "Hi0c".
    iPoseProof (mni_10 with "Htext") as "Hi10".
    iPoseProof (mni_14 with "Htext") as "Hi14".
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
              = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (m !!! Regidx csp_rs1)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
              (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
              = pa_stk (m !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (m !!! Regidx csp_rs1)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
              (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
              = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x00 addi sp,sp,-16 *)
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.main) (mword_of_int 48 : mword 6)
              m K 2 false Hc2 Hpush with "Hcg Hpc Hi00").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    pose (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    iEval (rewrite (stack_own_slots (KTR := KT0)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (m !!! Regidx csp_rs1)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
      by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.main : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.main + 0x02)) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 5) W1 (K - 2)%nat v1 false
              with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.main + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.main + 0x04)) (mword_of_int 0 : mword 6)
              (mword_of_int 8 : mword 5) W1 (K - 2)%nat v2 false
              with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.main + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 addi s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.main + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat false ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.main + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 jal cpuid *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x08)) (mword_of_int 1 : mword 5)
              (mword_of_int 2670 : mword 21) W2 (K - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi08").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (W3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x08) : mword 64) 4)]> W2).
    assert (Htgtcp : add_vec (mword_of_int (KernelSyms.main + 0x08) : mword 64)
              (sign_extend' 64 (mword_of_int 2670 : mword 21))
              = (mword_of_int KernelSyms.cpuid : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtcp) in "Hpc".
    iApply (Cpuid.wp_cpuid_sconf KT0 W3 (K - 2)%nat p0 ltac:(lia) with "Hcg Htext Hpc").
    iIntros (m4) "Hcg Hpc %Hcp".
    destruct Hcp as (Hcpcs & Hcpa0).
    assert (Hretcp : ret_pc (W3 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x0c) : mword 64)).
    { rewrite /W3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretcp) in "Hpc".
    (* cpuid() returns [cpuid_ret (rget W3 tp)] = this hart's id, and on the
       boot hart that is 0 -- so the [beqz] below is TAKEN. *)
    assert (Hm4a0 : m4 !!! Regidx (mword_of_int 10 : mword 5) = (zero_reg : mword 64)).
    { rewrite Hcpa0 (rget_tp W3) cpuid_ret_cid. exact Hcid. }
    (* +0x0c auipc a4,0x9 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.main + 0x0c)) (mword_of_int 14 : mword 5)
              (mword_of_int 9 : mword 20) m4 (K - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (W5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.main + 0x0c) : mword 64)
           (auipc_off (mword_of_int 9 : mword 20)))]> m4).
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.main + 0x0c) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 addi a4,a4,1094 : a4 := &started (unused on the boot arm) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.main + 0x10)) (mword_of_int 14 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 1128 : mword 12) W5 (K - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (W6 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec (rget W5 (mword_of_int 14 : mword 5))
           (sign_extend' 64 (mword_of_int 1128 : mword 12)))]> W5).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.main + 0x10) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    assert (HW6a0 : eq_vec (rget W6 (mword_of_int 10 : mword 5)) zero_reg = true).
    { rgne. rewrite /W6 upd_ne; [| reg_neq]. rewrite /W5 upd_ne; [| reg_neq].
      rewrite Hm4a0. vm_compute. reflexivity. }
    (* +0x14 beqz a0,+0x2e -- TAKEN, into the boot arm at 0x42 *)
    iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.main + 0x14))
              (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 2))
              (mword_of_int 10 : mword 5) W6 (K - 2)%nat false
              creg_c2 ltac:(vm_compute; discriminate) HW6a0
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi14").
    iApply wp_next_off_intro.
    iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgtb : add_vec (mword_of_int (KernelSyms.main + 0x14) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 23 : mword 8) ('b"0"))))
              = (mword_of_int (KernelSyms.main + 0x42) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtb) in "Hpc".
    iApply ("Hcont" $! W6 with "Hcg Hpc").
  Qed.

  (* =================================================================== *)
  (* 0x42 .. 0x6a -- consoleinit(); printkinit(); printk x3, and the TWO   *)
  (* ghost steps in between: the [pr] lock -- which now protects NOTHING   *)
  (* ([SpecPrintk.pr_res] is [emp]; d80e61c5 moved the transmitter to   *)
  (* [tx_lock], which uartputc_sync takes for itself) -- and [printk_env]. *)
  (* The panic-flag invariant is gone with the flags themselves.           *)
  (* =================================================================== *)
  Local Lemma mn_grp_printk 
      (γd : uart_names) (γv : disk_names)
      (m : regfile) (n : nat) (p0 : mword 64) (l0 : list (bv 8)) (b0 : bool) :
    (K_userinit <= n)%nat ->
    sie_cap_gpr KT0 m n false p0 -∗
    kernel_text -∗ kernel_data -∗ dev_inv γd γv -∗
    pc_is (mword_of_int (KernelSyms.main + 0x42) : mword 64) -∗
    cpu_ctx_free -∗
    cpu_own 0 false p0 false ∅ -∗
    lk_raw (mword_of_int KernelSyms.cons) -∗
    (* the transmit spinlock's three raw fields, on their way to uartinit *)
    lk_raw (mword_of_int KernelSyms.tx_lock) -∗
    lk_raw (mword_of_int KernelSyms.pr) -∗
    (∃ r w : mword 64, devsw_console_read ↦₈ r ∗ devsw_console_write ↦₈ w) -∗
    (* the console RING, which this group locks up behind cons.lock *)
    cons_res -∗
    uart_tx_own γd l0 -∗ uart_sent γd l0 -∗ uart_out_lb γd l0 -∗
    uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
    ( ∀ (γpr : gname) (m' : regfile),
        sie_cap_gpr KT0 m' n false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0x6e) : mword 64) -∗
        cpu_ctx_free -∗
        cpu_own 0 false p0 false ∅ -∗
        printk_env γpr γd γv -∗
        console_caps γd -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn.
    iIntros "Hcg #Htext #Hkdata #Hdev Hpc Hfree Hcpu Hlcons Hltx Hlpr".
    iIntros "Hdevsw Hring Htx Hsent Hlb Hdlab Hcont".
    iPoseProof (dev_inv_uart with "Hdev") as "#Huinv".
    iPoseProof (mni_42 with "Htext") as "Hi42".
    iPoseProof (mni_46 with "Htext") as "Hi46".
    iPoseProof (mni_4a with "Htext") as "Hi4a".
    iPoseProof (mni_4e with "Htext") as "Hi4e".
    iPoseProof (mni_52 with "Htext") as "Hi52".
    iPoseProof (mni_56 with "Htext") as "Hi56".
    iPoseProof (mni_5a with "Htext") as "Hi5a".
    iPoseProof (mni_5e with "Htext") as "Hi5e".
    iPoseProof (mni_62 with "Htext") as "Hi62".
    iPoseProof (mni_66 with "Htext") as "Hi66".
    iPoseProof (mni_6a with "Htext") as "Hi6a".
    iPoseProof (kernel_data_string mn_nl_addr mn_nl
                  (mword_of_int mn_nl_addr) eq_refl
                  ltac:(unfold text_end, mn_nl_addr; lia) mn_nl_bytes
                  with "Hkdata") as "#Hsnl".
    iPoseProof (kernel_data_string mn_boot_addr mn_boot
                  (mword_of_int mn_boot_addr) eq_refl
                  ltac:(unfold text_end, mn_boot_addr; lia) mn_boot_bytes
                  with "Hkdata") as "#Hsbt".
    pose proof mn_nl_fmt as (Hknl & Hnnl & Hlnl).
    pose proof mn_boot_fmt as (Hkbt & Hnbt & Hlbt).
    iDestruct "Hlcons" as (vcl vcn vcc) "(Hcw & Hcn & Hcc)".
    (* [Hltx] is NOT unpacked: it goes to consoleinit whole, and comes back
       whole as [lk_fresh]. *)
    iDestruct "Hlpr" as (vpl vpn vpc) "(Hpw & Hpn & Hpc2)".
    iDestruct "Hdevsw" as (dr0 dw0) "(Hdr & Hdw)".
    (* ---- +0x42 jal consoleinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x42)) (mword_of_int 1 : mword 5)
              (mword_of_int 2094518 : mword 21) m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi42").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (C0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x42) : mword 64) 4)]> m).
    assert (Htgtci : add_vec (mword_of_int (KernelSyms.main + 0x42) : mword 64)
              (sign_extend' 64 (mword_of_int 2094518 : mword 21))
              = (mword_of_int KernelSyms.consoleinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtci) in "Hpc".
    (* BOTH CONSOLE LOCKS ARE BROUGHT UP HERE.  consoleinit runs
       [initlock(&cons.lock,"cons")] itself and, through uartinit,
       [initlock(&tx_lock,"uart")] -- so [Hlcons]'s three fields come back as
       [Hclw]/[Hclnm]/[Hclcpu] and [Hltx]'s as [Hlkfresh], and those are
       exactly [WpLock.newlock]'s premises.  The two [newlock]s are taken
       twenty lines below, once [printkinit] has returned; together they are
       [SpecConsoleintr.console_caps]. *)
    iApply (Consoleinit.wp_consoleinit_sconf γd C0 n l0 b0
              vcl vcn vcc dr0 dw0 p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Huinv Htx Hlb Hsent Hdlab
                    Hcw Hcn Hcc Hltx Hdr Hdw").
    iIntros (mc) "Hcg Hpc %Hcsci Htx Hsent #Hdoff Hclw #Hclnm Hclcpu Hlkfresh _ _".
    assert (Hretci : ret_pc (C0 !!! Regidx (mword_of_int 1 : mword 5) : mword 64)
                     = (mword_of_int (KernelSyms.main + 0x46) : mword 64)).
    { rewrite /C0 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretci) in "Hpc".
    (* ---- +0x46 jal printkinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x46)) (mword_of_int 1 : mword 5)
              (mword_of_int 2095576 : mword 21) mc n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi46").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (C1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x46) : mword 64) 4)]> mc).
    assert (Htgtpi : add_vec (mword_of_int (KernelSyms.main + 0x46) : mword 64)
              (sign_extend' 64 (mword_of_int 2095576 : mword 21))
              = (mword_of_int KernelSyms.printkinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpi) in "Hpc".
    iApply (Printkinit.wp_printkinit_sconf C1 n vpl vpn vpc false p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Hpw Hpn Hpc2").
    iApply wp_next_off_intro.
    iIntros (mp) "Hcg Hpc %Hcspi Hprw #Hprnm Hprcpu".
    assert (Hretpi : ret_pc (C1 !!! Regidx (mword_of_int 1 : mword 5) : mword 64)
                     = (mword_of_int (KernelSyms.main + 0x4a) : mword 64)).
    { rewrite /C1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretpi) in "Hpc".
    (* ---- the ghost steps: three [newlock]s and [printk_env] ----

       PR.LOCK'S [newlock] IS PAID FOR WITH NOTHING.  [SpecPrintk.pr_res]
       is [emp]: d80e61c5 put uartputc_sync's THR write under [tx_lock], so
       the transmitter belongs to [UartTxInv.tx_res] and pr.lock is left
       serializing format walks, which has no separation-logic content.  That
       is what frees the [uart_tx_own] this block hands to tx_lock's
       [newlock] instead. *)
    iApply fupd_wp.
    (* promote once, so both [console_caps] and [printk_env] below can reuse
       the same persistent witness instead of re-deriving it. *)
    iDestruct "Hsent" as "#Hsent".
    iPoseProof (uart_sent_sub_nil γd l0 with "Hsent") as "#Hsub0".
    iMod (newlock ⊤ (mword_of_int KernelSyms.pr) "pr"%string (pr_res γd)
            with "Hprnm Hprw Hprcpu []") as (γpr) "#Hprlk".
    { rewrite /pr_res. done. }
    (* ---- THE OTHER TWO [newlock]s, and this is the point of the group.
       consoleinit has just run [initlock] on cons.lock and, through uartinit,
       on tx_lock; both come back as [WpLock.newlock]'s raw material, and both
       RESOURCES are in hand -- the ring out of [main_globals_raw], the
       transmitter token [Htx] straight back from consoleinit (d80e61c5 left
       [pr_res] empty, so nothing else wants it).  Together the two are
       [SpecConsoleintr.console_caps], which the kernelvec handler contract
       closes over ([SpecDevintr.devintr_caps]) because devintr -> uartintr ->
       consoleintr takes both locks.  Nothing consumed it before consoleintr
       was proven, which is why the two steps sat here un-taken. ---- *)
    iDestruct "Hlkfresh" as "(Htxw & #Htxnm & Htxcpu)".
    iMod (newlock ⊤ UartTxInv.a_tx_lock "uart"%string (tx_res γd)
            with "Htxnm Htxw Htxcpu [Htx]") as (γtx) "#Htxinv".
    { iApply (tx_res_intro γd l0 with "Htx"). }
    (* [is_txlock]'s two halves are exactly [Htxinv]/[Hdoff] -- the same pair
       [console_caps] below folds inline -- so mint it once here and feed
       both consumers (LinkPrintk.v needs the witness to invoke the real
       [SpecPrintk.wp_printk_sconf]). *)
    iPoseProof (is_txlock_intro γtx γd with "Htxinv Hdoff") as "#Htxl".
    iAssert (printk_env γpr γd γv) as "#Hpenv".
    { rewrite /printk_env /pr_lock. iSplitR; [iExact "Hprlk"|].
      iSplitR; [iExact "Hdoff" |].
      iSplitR; [iExact "Hdev" |].
      iSplitR; [iExists γtx; iExact "Htxl" | iExact "Hsub0"]. }
    iMod (newlock ⊤ a_cons "cons"%string cons_res
            with "Hclnm Hclw Hclcpu Hring") as (γcl) "#Hconslk".
    iAssert (console_caps γd) as "#Hccaps".
    { rewrite /console_caps. iExists γtx, γcl.
      iSplitR; [iExact "Htxl" |].
      iSplitR; [iExact "Hconslk" |].
      iExact "Hsub0". }
    iModIntro.
    (* ---- +0x4a auipc a0,0x6 / +0x4e addi a0,a0,476 : a0 := &"\n" ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.main + 0x4a)) (mword_of_int 10 : mword 5)
              (mword_of_int 6 : mword 20) mp n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (A1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.main + 0x4a) : mword 64)
           (auipc_off (mword_of_int 6 : mword 20)))]> mp).
    assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.main + 0x4a) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4e) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.main + 0x4e)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 510 : mword 12) A1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (A2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (rget A1 (mword_of_int 10 : mword 5))
           (sign_extend' 64 (mword_of_int 510 : mword 12)))]> A1).
    assert (HA2a0 : A2 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int mn_nl_addr : mword 64)).
    { rewrite /A2 upd_eq. rgne. rewrite /A1 upd_eq /mn_nl_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.main + 0x4e) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp52) in "Hpc".
    (* ---- +0x52 jal printk ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x52)) (mword_of_int 1 : mword 5)
              (mword_of_int 2094720 : mword 21) A2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi52").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (A3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x52) : mword 64) 4)]> A2).
    assert (Htgtpk : add_vec (mword_of_int (KernelSyms.main + 0x52) : mword 64)
              (sign_extend' 64 (mword_of_int 2094720 : mword 21))
              = (mword_of_int KernelSyms.printk : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpk) in "Hpc".
    assert (HA3a0 : A3 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int mn_nl_addr : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]).
    iApply (PrintkGen.wp_printk_gen_sconf KT0 γpr γd γv A3 n false p0
              mn_nl [] false ∅ ltac:(lia) Hlnl Hnnl ltac:(rewrite Hknl; reflexivity)
              ltac:(cbn [length]; lia) (locks_below_empty "pr")
              with "Hcg Htext Hkdata Hpc Hcpu Hpenv [] [//]").
    all: try lkbelow.
    { rewrite HA3a0. iExact "Hsnl". }
    iApply wp_next_off_intro.
    iIntros (mk1) "Hcg Hpc %Hcsk1 Hcpu _ _".
    assert (Hretpk1 : ret_pc (A3 !!! Regidx (mword_of_int 1 : mword 5))
                      = (mword_of_int (KernelSyms.main + 0x56) : mword 64)).
    { rewrite /A3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretpk1) in "Hpc".
    destruct Hcsk1 as (Hcsk1 & _).
    (* ---- +0x56 / +0x5a : a0 := &"xv6 kernel is booting\n" ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.main + 0x56)) (mword_of_int 10 : mword 5)
              (mword_of_int 6 : mword 20) mk1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.main + 0x56) : mword 64)
           (auipc_off (mword_of_int 6 : mword 20)))]> mk1).
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.main + 0x56) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.main + 0x5a)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 506 : mword 12) B1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (B2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (rget B1 (mword_of_int 10 : mword 5))
           (sign_extend' 64 (mword_of_int 506 : mword 12)))]> B1).
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int mn_boot_addr : mword 64)).
    { rewrite /B2 upd_eq. rgne. rewrite /B1 upd_eq /mn_boot_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.main + 0x5a) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x5e)) (mword_of_int 1 : mword 5)
              (mword_of_int 2094708 : mword 21) B2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (B3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x5e) : mword 64) 4)]> B2).
    assert (Htgtpk2 : add_vec (mword_of_int (KernelSyms.main + 0x5e) : mword 64)
              (sign_extend' 64 (mword_of_int 2094708 : mword 21))
              = (mword_of_int KernelSyms.printk : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpk2) in "Hpc".
    assert (HB3a0 : B3 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int mn_boot_addr : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a0 | reg_neq]).
    iApply (PrintkGen.wp_printk_gen_sconf KT0 γpr γd γv B3 n false p0
              mn_boot [] false ∅ ltac:(lia) Hlbt Hnbt ltac:(rewrite Hkbt; reflexivity)
              ltac:(cbn [length]; lia) (locks_below_empty "pr")
              with "Hcg Htext Hkdata Hpc Hcpu Hpenv [] [//]").
    all: try lkbelow.
    { rewrite HB3a0. iExact "Hsbt". }
    iApply wp_next_off_intro.
    iIntros (mk2) "Hcg Hpc %Hcsk2 Hcpu _ _".
    assert (Hretpk2 : ret_pc (B3 !!! Regidx (mword_of_int 1 : mword 5))
                      = (mword_of_int (KernelSyms.main + 0x62) : mword 64)).
    { rewrite /B3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretpk2) in "Hpc".
    destruct Hcsk2 as (Hcsk2 & _).
    (* ---- +0x62 / +0x66 / +0x6a : the third printk("\n") ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.main + 0x62)) (mword_of_int 10 : mword 5)
              (mword_of_int 6 : mword 20) mk2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (D1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.main + 0x62) : mword 64)
           (auipc_off (mword_of_int 6 : mword 20)))]> mk2).
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.main + 0x62) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.main + 0x66)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 486 : mword 12) D1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (D2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (rget D1 (mword_of_int 10 : mword 5))
           (sign_extend' 64 (mword_of_int 486 : mword 12)))]> D1).
    assert (HD2a0 : D2 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int mn_nl_addr : mword 64)).
    { rewrite /D2 upd_eq. rgne. rewrite /D1 upd_eq /mn_nl_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.main + 0x66) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x6a)) (mword_of_int 1 : mword 5)
              (mword_of_int 2094696 : mword 21) D2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi6a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (D3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x6a) : mword 64) 4)]> D2).
    assert (Htgtpk3 : add_vec (mword_of_int (KernelSyms.main + 0x6a) : mword 64)
              (sign_extend' 64 (mword_of_int 2094696 : mword 21))
              = (mword_of_int KernelSyms.printk : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpk3) in "Hpc".
    assert (HD3a0 : D3 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int mn_nl_addr : mword 64))
      by (rewrite /D3 upd_ne; [exact HD2a0 | reg_neq]).
    iApply (PrintkGen.wp_printk_gen_sconf KT0 γpr γd γv D3 n false p0
              mn_nl [] false ∅ ltac:(lia) Hlnl Hnnl ltac:(rewrite Hknl; reflexivity)
              ltac:(cbn [length]; lia) (locks_below_empty "pr")
              with "Hcg Htext Hkdata Hpc Hcpu Hpenv [] [//]").
    all: try lkbelow.
    { rewrite HD3a0. iExact "Hsnl". }
    iApply wp_next_off_intro.
    iIntros (mk3) "Hcg Hpc %Hcsk3 Hcpu _ _".
    assert (Hretpk3 : ret_pc (D3 !!! Regidx (mword_of_int 1 : mword 5))
                      = (mword_of_int (KernelSyms.main + 0x6e) : mword 64)).
    { rewrite /D3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretpk3) in "Hpc".
    destruct Hcsk3 as (Hcsk3 & _).
    iApply ("Hcont" $! γpr mk3 with "Hcg Hpc Hfree Hcpu Hpenv Hccaps").
  Qed.

  (* =================================================================== *)
  (* 0x6e .. 0x7a -- kinit(); kvminit(); kvminithart(); procinit(), with   *)
  (* the [kalloc_env] and [procs_inv] assemblies, and -- between kvminit    *)
  (* and kvminithart -- THE TABLE PUBLICATION: the one-way door that        *)
  (* persists the root cell, mints the 65 kernel-mapping claims out of the  *)
  (* [kmap_auth kmap_M0] boot token, and allocates the shared [kpt_inv] out *)
  (* of kvminit's exclusive tree + the [kpt_unset] one-shot.  It lives HERE *)
  (* (boot-hart-only, once) so that kvminithart's own contract is           *)
  (* hart-generic: it takes only the persistent [kpt_inv] + root cell.      *)
  (* =================================================================== *)
  Local Lemma mn_grp_kvm 
      (m : regfile) (n : nat) (p0 : mword 64)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) :
    (K_userinit <= n)%nat ->
    phystop = (mword_of_int 0x88000000 : mword 64) ->
    (* [kmem_lo] IS the dumped `end` symbol -- see [SpecMain]'s premise *)
    s1entry = add_vec (and_vec (add_vec (mword_of_int kmem_lo : mword 64)
                        (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv ->
    prun phystop s1entry ps ->
    (K_kvmmake + 64 + 3 < length ps)%nat ->
    sie_cap_gpr KT0 m n false p0 -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.main + 0x6e) : mword 64) -∗
    cpu_ctx_free -∗
    cpu_own 0 false p0 false ∅ -∗
    lk_raw (mword_of_int KernelSyms.kmem) -∗
    (mword_of_int (KernelSyms.kmem + 24) : mword 64) ↦₈ (mword_of_int 0 : mword 64) -∗
    ([∗ list] p ∈ ps, page_own p) -∗
    (∃ kpt0 : mword 64,
       (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈ kpt0) -∗
    strans_pending -∗ tlb ↦ᵣ tlbvec0 -∗ kpt_unset -∗
    kmap_auth kmap_M0 -∗
    lk_raw pid_lock_addr -∗ lk_raw wait_lock_addr -∗
    ([∗ list] i ∈ seq 0 NPROC, proc_raw (proc_addr i)) -∗
    ([∗ list] i ∈ seq 0 NPROC,
       (∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗ proc_pub (proc_addr i)) -∗
    fd_slots (NPROC * (NOFILE + FDSPARE)) -∗
    iref_slots (NPROC * (1 + IREFSPARE)) -∗
    ([∗ list] i ∈ seq 0 NPROC, hart_full i (0%fin : CPU)) -∗
    ([∗ list] i ∈ seq 0 NPROC, pstate_full i UNUSED) -∗
    ( ∀ (γa : gname) (γs : list gname) (m' : regfile)
        (root : mword 44) (pas : nat -> mword 44),
        sie_cap_gpr KT1 m' n false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0x7e) : mword 64) -∗
        cpu_ctx_free -∗
        cpu_own 0 false p0 false ∅ -∗
        kalloc_env γa (avail_sub (Some (length ps)) K_kvmmake) -∗
        procs_inv γs -∗
        (* the KPT receipt kvminithart minted, on its way to [trap_csrs] *)
        kpt_on cpu_id -∗
        (∃ v : mword 64, stvec ↦ᵣ v) -∗
        (* what kvminithart published about the kernel page table: all four
           PERSISTENT, and exactly what the [started] deposit carries *)
        kpt_inv root -∗
        (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈□
          (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) -∗
        kmap_at tramp_vpn tramp_ppn KP_rx -∗
        ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hphystop Hs1 Hprun Hlen.
    subst phystop s1entry.
    iIntros "Hcg #Htext #Hkdata Hpc Hfree Hcpu Hlkmem Hkmem24 Hpages Hkpt".
    iIntros "Hsbit Htlb Hunset Hkauth Hlpid Hlwait Hprocs Hppub Hfds Hirs Hparks Hpst Hcont".
    iPoseProof (mni_6e with "Htext") as "Hi6e".
    iPoseProof (mni_72 with "Htext") as "Hi72".
    iPoseProof (mni_76 with "Htext") as "Hi76".
    iPoseProof (mni_7a with "Htext") as "Hi7a".
    iDestruct "Hlkmem" as (vkl vkn vkc) "(Hkw & Hkn & Hkc)".
    iDestruct "Hkpt" as (kpt0) "Hkpt".
    (* ---- +0x6e jal kinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x6e)) (mword_of_int 1 : mword 5)
              (mword_of_int 2096142 : mword 21) m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi6e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (V1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x6e) : mword 64) 4)]> m).
    assert (Htgtki : add_vec (mword_of_int (KernelSyms.main + 0x6e) : mword 64)
              (sign_extend' 64 (mword_of_int 2096142 : mword 21))
              = (mword_of_int KernelSyms.kinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtki) in "Hpc".
    iApply (Kinit.wp_kinit_sconf V1 ps n 0%nat false p0 vkl vkn vkc
              false ∅ ltac:(lia) eq_refl Hprun (locks_below_empty _)
              with "Hcg Hcpu Htext Hkdata Hpc Hkw Hkn Hkc Hkmem24 Hpages").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (γl γk mki) "Hcg Hcpu Hpc %Hcski #Hkmem Havail".
    assert (Hretki : ret_pc (V1 !!! Regidx (mword_of_int 1 : mword 5) : mword 64)
                     = (mword_of_int (KernelSyms.main + 0x72) : mword 64)).
    { rewrite /V1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretki) in "Hpc".
    (* ---- ASSEMBLY 1: kalloc_env out of + kalloc_avail ---- *)
    iAssert (kalloc_env γl (Some (length ps))) with "[Havail]" as "Hkenv".
    { rewrite /kalloc_env. iExists γk. iSplitR; [iExact "Hkmem"|].
      iExact "Havail". }
    (* ---- +0x72 jal kvminit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x72)) (mword_of_int 1 : mword 5)
              (mword_of_int 718 : mword 21) mki n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi72").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (V2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x72) : mword 64) 4)]> mki).
    assert (Htgtkv : add_vec (mword_of_int (KernelSyms.main + 0x72) : mword 64)
              (sign_extend' 64 (mword_of_int 718 : mword 21))
              = (mword_of_int KernelSyms.kvminit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtkv) in "Hpc".
    iApply (Kvminit.wp_kvminit_sconf γl V2 0%nat n false p0
              (Some (length ps)) kpt0 false ∅ eq_refl ltac:(lia)
              ltac:(exists (length ps); split; [reflexivity | lia])
              with "Hcg Hcpu Htext Hpc Hkpt Hkenv").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mkv t pas) "Hcg Hcpu Hpc Htree Hkpt %Hrep %Hnodes Hkenv %Hcskv %Hpasok Hkstacks".
    assert (Hretkv : ret_pc (V2 !!! Regidx (mword_of_int 1))
                     = (mword_of_int (KernelSyms.main + 0x76) : mword 64)).
    { rewrite /V2 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretkv) in "Hpc".
    (* ---- THE PUBLICATION: the one-way door that shares the kernel table.
       Persist the root cell kvminit wrote, mint the 65 claims out of the
       boot auth, and allocate [kpt_inv] out of kvminit's exclusive tree +
       the one-shot -- so kvminithart below (and on every secondary hart)
       needs only the persistent [kpt_inv] + root cell. ---- *)
    iApply fupd_wp.
    iMod (word_pointsto_persist with "Hkpt") as "#Hkptp".
    iMod (kvm_M_mint pas with "Hkauth") as "(Hauth & #Htramp & #Hkstx)".
    (* ---- K1 -- THE MINT (claude-notes/projects/sp-migration.md).  The 64
       claims just minted, against the 64 identity-mapped pages kvminit
       handed out, ARE the 64 process kernel stacks owned at their KSTACK
       virtual addresses -- at KT1, the tree's first real KT1 facts.  This
       is the one point in the tree where both halves are in hand.
       The bank travels to the [procs_inv] assembly below, where each slot's
       page is carved to [KSTACK_AV] and deposited in its dormant block
       ([SpecProcinit.procs_inv_alloc]) -- so a process's kernel stack comes
       from HERE for the rest of the system's life. ---- *)
    iDestruct (kstack_bank_intro pas Hpasok with "Hkstx Hkstacks") as "Hbank".
    iMod (kpt_inv_alloc (pt_base t) t (kvm_M pas) ⊤
            (kvm_bridge pas t (pt_base t) Hpasok eq_refl Hrep)
            with "Htree Hauth Hunset") as "[#Hkinv #Hlbt]".
    iModIntro.
    (* ---- +0x76 jal kvminithart ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x76)) (mword_of_int 1 : mword 5)
              (mword_of_int 62 : mword 21) mkv n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi76").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (V3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x76) : mword 64) 4)]> mkv).
    assert (Htgtkh : add_vec (mword_of_int (KernelSyms.main + 0x76) : mword 64)
              (sign_extend' 64 (mword_of_int 62 : mword 21))
              = (mword_of_int KernelSyms.kvminithart : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtkh) in "Hpc".
    iApply (Kvminithart.wp_kvminithart_sconf V3 0%nat n (pt_base t) tlbvec0 p0
              eq_refl ltac:(lia)
              with "Hcg Hsbit Htext Hpc Htlb Hkptp Hkinv").
    (* kvminithart's KPT RECEIPT, kept rather than dropped: it is a member of
       [trap_csrs] now (IntrDefs §6b -- interrupts enabled implies the kernel
       table is installed), so the boot chain must carry it to the fold in
       [wp_main_boot_sconf].  Named [Hkptr] -- [Hkpt] in this lemma is the
       [kernel_pagetable] CELL, a different thing. *)
    iIntros (mkh) "Hcg Hpc %Hcskh #Hkptr Hstvec".
    (* ---- THE BOOT SEAM: kvminithart has installed the kernel table, so
       this hart's regime moves KT0 -> KT1.  [sie_cap_gpr_ktier_up] carries
       the capability across, weakening its (static, boot-stack) frame
       through [StackOwn.stack_ktier_mono] and re-minting the tier witness
       from the receipt.  Everything below this line is post-boot. ---- *)
    iDestruct (sie_cap_gpr_ktier_up KT0 KT1 with "Hcg Hkptr") as "Hcg".
    assert (Hretkh : ret_pc (V3 !!! Regidx (mword_of_int 1))
                     = (mword_of_int (KernelSyms.main + 0x7a) : mword 64)).
    { rewrite /V3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretkh) in "Hpc".
    (* ---- +0x7a jal procinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x7a)) (mword_of_int 1 : mword 5)
              (mword_of_int 2374 : mword 21) mkh n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi7a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (V4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x7a) : mword 64) 4)]> mkh).
    assert (Htgtpr : add_vec (mword_of_int (KernelSyms.main + 0x7a) : mword 64)
              (sign_extend' 64 (mword_of_int 2374 : mword 21))
              = (mword_of_int KernelSyms.procinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpr) in "Hpc".
    iApply (Procinit.wp_procinit_sconf V4 n false p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Hlpid Hlwait Hprocs Hfds Hirs").
    iApply wp_next_off_intro.
    iIntros (mpr) "Hcg Hpc %Hcspr _ _ Hready".
    assert (Hretpr : ret_pc (V4 !!! Regidx (mword_of_int 1 : mword 5) : mword 64)
                     = (mword_of_int (KernelSyms.main + 0x7e) : mword 64)).
    { rewrite /V4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretpr) in "Hpc".
    (* ---- ASSEMBLY 2: the 64 proc locks -> procs_inv ---- *)
    iApply fupd_wp.
    iDestruct (big_sepL_sep_2
                 (fun _ i => proc_ready i)
                 (fun _ i => ((∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
                              proc_pub (proc_addr i))%I)
                 (seq 0 NPROC) with "Hready Hppub") as "Hin".
    iDestruct (big_sepL_sep_2
                 (fun _ i => (proc_ready i ∗
                              ((∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
                               proc_pub (proc_addr i)))%I)
                 (fun _ i => hart_full i (0%fin : CPU))
                 (seq 0 NPROC) with "Hin Hparks") as "Hin".
    iDestruct (big_sepL_sep_2
                 (fun _ i => ((proc_ready i ∗
                               ((∃ ch : mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
                                proc_pub (proc_addr i))) ∗ hart_full i (0%fin : CPU))%I)
                 (fun _ i => pstate_full i UNUSED)
                 (seq 0 NPROC) with "Hin Hpst") as "Hin".
    iMod (procs_inv_alloc ⊤ with "Hin Hbank") as (γs) "#Hpinv".
    iModIntro.
    iApply ("Hcont" $! γl γs mpr (pt_base t) pas
              with "Hcg Hpc Hfree Hcpu Hkenv Hpinv Hkptr Hstvec Hkinv Hkptp Htramp Hkstx").
  Qed.

  (* =================================================================== *)
  (* 0x7e .. 0x8a -- trapinit(); trapinithart(); plicinit();              *)
  (* plicinithart(), plus [intr_inv_alloc_off] over kernelvec.            *)
  (* =================================================================== *)
  Local Lemma mn_grp_trap 
      (γd : uart_names) (γv : disk_names) (m : regfile) (n : nat)
      (p0 : mword 64) :
    (K_userinit <= n)%nat ->
    cid_word = (zero_reg : mword 64) ->
    sie_cap_gpr KT1 m n false p0 -∗
    kernel_text -∗ kernel_data -∗ dev_inv γd γv -∗
    pc_is (mword_of_int (KernelSyms.main + 0x7e) : mword 64) -∗
    lk_raw (mword_of_int KernelSyms.tickslock) -∗
    (* the tick counter, so this group can bring tickslock UP: trapinit
       initialises the lock's words and this is the resource it protects. *)
    (∃ t : mword 32, a_ticks ↦₄ t) -∗
    (∃ v : mword 64, stvec ↦ᵣ v) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    (* IT HANDS OUT THE WRITTEN CELL AND THE GHOST QUARTER, NOT [intr_res],
       and that is an ORDERING fact about main rather than a preference: the
       handler contract closes over [devintr_caps] (SpecKernelvec.v), whose
       disk lock does not exist until virtio_disk_init -- three groups further
       on.  So the two pieces ride raw to the chain's tail, which is where
       [intr_res] is folded and where [trap_csrs_raw] was already waiting to
       be completed. *)
    ( ∀ (m' : regfile) (γtl : gname),
        sie_cap_gpr KT1 m' n false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0x8e) : mword 64) -∗
        is_tickslock γtl -∗
        stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) -∗
        ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hcid.
    (* [cid_word] is a [Definition] over [cpu_id]; naming the delta-expanded
       form once is what lets [rget_tp]'s output be rewritten below. *)
    assert (Hcidz : cid_word_of cpu_id = (zero_reg : mword 64)) by exact Hcid.
    iIntros "Hcg #Htext #Hkdata #Hdev Hpc Hltick Hticks Hstvec Hq Hcont".
    iPoseProof (dev_inv_plic with "Hdev") as "#Hpinv".
    iPoseProof (mni_7e with "Htext") as "Hi7e".
    iPoseProof (mni_82 with "Htext") as "Hi82".
    iPoseProof (mni_86 with "Htext") as "Hi86".
    iPoseProof (mni_8a with "Htext") as "Hi8a".
    iDestruct "Hltick" as (vtl vtn vtc) "(Htw & Htn & Htc)".
    (* ---- +0x7e jal trapinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x7e)) (mword_of_int 1 : mword 5)
              (mword_of_int 5480 : mword 21) m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi7e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (T1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x7e) : mword 64) 4)]> m).
    assert (Htgtti : add_vec (mword_of_int (KernelSyms.main + 0x7e) : mword 64)
              (sign_extend' 64 (mword_of_int 5480 : mword 21))
              = (mword_of_int KernelSyms.trapinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtti) in "Hpc".
    iApply (Trapinit.wp_trapinit_sconf T1 n vtl vtn vtc false p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Htw Htn Htc").
    iApply wp_next_off_intro.
    iIntros (mt) "Hcg Hpc %Hcsti Htw2 #Htn2 Htc2".
    (* ---- tickslock comes UP here: trapinit left its words initialised, and
           the resource it protects is the [ticks] counter.  This is what the
           handler contract's [tick_keeper] conjunct wants from the TICK hart
           (hart 0); a secondary discharges it by its left arm instead. ---- *)
    iDestruct "Hticks" as (t0) "Hticks".
    (* a fupd in front of a [WP (Loop)] goal: the tree's idiom is to peel it
       with [fupd_wp] first (ProofIupdate.v records the same). *)
    iApply fupd_wp.
    iMod (newlock ⊤ (mword_of_int KernelSyms.tickslock : mword 64) "time"%string
            ticks_res with "Htn2 Htw2 Htc2 [Hticks]") as (γtl) "#Htl".
    { iApply (ticks_res_intro t0 with "Hticks"). }
    iModIntro.
    assert (Hretti : ret_pc (T1 !!! Regidx (mword_of_int 1 : mword 5) : mword 64)
                     = (mword_of_int (KernelSyms.main + 0x82) : mword 64)).
    { rewrite /T1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretti) in "Hpc".
    (* ---- +0x82 jal trapinithart ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x82)) (mword_of_int 1 : mword 5)
              (mword_of_int 5512 : mword 21) mt n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi82").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (T2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x82) : mword 64) 4)]> mt).
    assert (Htgtth : add_vec (mword_of_int (KernelSyms.main + 0x82) : mword 64)
              (sign_extend' 64 (mword_of_int 5512 : mword 21))
              = (mword_of_int KernelSyms.trapinithart : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtth) in "Hpc".
    iDestruct "Hstvec" as (tv0) "Hstvec".
    iApply (Trapinithart.wp_trapinithart_sconf T2 n tv0 p0 ltac:(lia)
              with "Hcg Htext Hpc Hstvec").
    iIntros (mth) "Hcg Hpc %Hcsth Hstvec".
    assert (Hretth : ret_pc (T2 !!! Regidx (mword_of_int 1))
                     = (mword_of_int (KernelSyms.main + 0x86) : mword 64)).
    { rewrite /T2 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretth) in "Hpc".
    (* trapinithart has written kernelvec into stvec; the cell and the SIE
       ghost's spare quarter ride on to the chain's tail, where the handler
       contract's credentials are finally all in hand. *)
    (* ---- +0x86 jal plicinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x86)) (mword_of_int 1 : mword 5)
              (mword_of_int 18136 : mword 21) mth n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi86").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (T3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x86) : mword 64) 4)]> mth).
    assert (Htgtpl : add_vec (mword_of_int (KernelSyms.main + 0x86) : mword 64)
              (sign_extend' 64 (mword_of_int 18136 : mword 21))
              = (mword_of_int KernelSyms.plicinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpl) in "Hpc".
    iApply (Plicinit.wp_plicinit_sconf T3 n p0 ltac:(lia)
              with "Hcg Htext Hpc Hpinv").
    iApply wp_next_off_intro.
    iIntros (mpl) "Hcg Hpc %Hcspl".
    destruct Hcspl as (Hcspl & _).
    assert (Hretpl : ret_pc (T3 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x8a) : mword 64)).
    { rewrite /T3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretpl) in "Hpc".
    (* ---- +0x8a jal plicinithart ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x8a)) (mword_of_int 1 : mword 5)
              (mword_of_int 18158 : mword 21) mpl n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi8a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (T4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x8a) : mword 64) 4)]> mpl).
    assert (Htgtph : add_vec (mword_of_int (KernelSyms.main + 0x8a) : mword 64)
              (sign_extend' 64 (mword_of_int 18158 : mword 21))
              = (mword_of_int KernelSyms.plicinithart : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtph) in "Hpc".
    (* plicinithart indexes the PLIC banks by [rget _ tp], which IS this
       hart's id -- no map-side tp fact to thread. *)
    assert (Hdc : (bv_unsigned (rget T4 (mword_of_int 4 : mword 5))
                   < Z.of_nat dev_ncpu)%Z).
    { rewrite (rget_tp T4) Hcidz. vm_compute. reflexivity. }
    iApply (Plicinithart.wp_plicinithart_sconf γd γv T4 n p0 Hdc ltac:(lia)
              with "Hcg Htext Hpc Hdev").
    iIntros (mph) "Hcg Hpc %Hcsph".
    destruct Hcsph as (Hcsph & _).
    assert (Hretph : ret_pc (T4 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x8e) : mword 64)).
    { rewrite /T4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretph) in "Hpc".
    iApply ("Hcont" $! mph γtl with "Hcg Hpc Htl Hstvec Hq").
  Qed.

  (* =================================================================== *)
  (* 0x8e .. 0x9e -- binit(); iinit(); fileinit(); virtio_disk_init();     *)
  (* userinit(), plus [DiskBoot.disk_res_boot] and the vdisk [newlock].    *)
  (* =================================================================== *)
  Local Lemma mn_grp_fs 
      (γa : gname) (γs : list gname) (γv : disk_names) (γd : uart_names)
      (m : regfile) (n : nat) (p0 : mword 64)
      (ps : list (mword 64)) (c0 : virtio_cfg) (free0 : nat -> bv 8) :
    (K_userinit <= n)%nat ->
    (K_kvmmake + 64 + 3 < length ps)%nat ->
    virtio_live c0 = false ->
    sie_cap_gpr KT1 m n false p0 -∗
    kernel_text -∗ kernel_data -∗ dev_inv γd γv -∗
    pc_is (mword_of_int (KernelSyms.main + 0x8e) : mword 64) -∗
    cpu_ctx_free -∗
    cpu_own 0 false p0 false ∅ -∗
    procs_inv γs -∗
    kalloc_env γa (avail_sub (Some (length ps)) K_kvmmake) -∗
    lk_raw bcache_addr -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_raw (buf_lock (bnode k))) -∗
    ([∗ list] k ∈ seq 0 NBUF, blink_raw (bnode k)) -∗
    blink_raw bhead -∗
    lk_raw itable_addr -∗
    ([∗ list] i ∈ seq 0 NINODE, sl_raw (inode_lock i)) -∗
    lk_raw (mword_of_int KernelSyms.ftable) -∗
    lk_raw disk_lock -∗
    (∃ pd pav pu : mword 64,
       disk_desc ↦₈ pd ∗ disk_avail ↦₈ pav ∗ disk_used ↦₈ pu) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ free0 j) -∗
    d_used_idx ↦₂ wrap16 0%nat -∗
    ([∗ list] i ∈ seq 0 8, disk_slot_raw i) -∗
    ghost_map_auth (dn_claim γv) 1 (∅ : gmap nat dclaim) -∗
    disk_done_lb γv 0%nat -∗
    disk_cfg_is γv (DfracOwn (1/2)) c0 -∗
    (∃ v0 : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v0) -∗
    ( ∀ (γk : gname) (pd pav pu : mword 64) (m' : regfile),
        sie_cap_gpr KT1 m' n false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0xa2) : mword 64) -∗
        cpu_ctx_free -∗
        cpu_own 0 false p0 false ∅ -∗
        is_lock γk d_lock "virtio_disk"%string (disk_res γv pd pav pu) -∗
        disk_geom γv pd pav pu -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hlen Hlive.
    iIntros "Hcg #Htext #Hkdata #Hdev Hpc Hfree Hcpu #Hpinv Hkenv".
    iIntros "Hlbc Hbufl Hbufn Hbhead Hlit Hinl Hlft Hldisk".
    iIntros "Hdiskptr Hdiskfree Hdusedidx Hdslots Hclaim #Hdone Hcfg Hinitproc Hcont".
    iPoseProof (dev_inv_disk with "Hdev") as "#Hdinv".
    iPoseProof (mni_8e with "Htext") as "Hi8e".
    iPoseProof (mni_92 with "Htext") as "Hi92".
    iPoseProof (mni_96 with "Htext") as "Hi96".
    iPoseProof (mni_9a with "Htext") as "Hi9a".
    iPoseProof (mni_9e with "Htext") as "Hi9e".
    iDestruct "Hlbc" as (vbl vbn vbc) "(Hbw & Hbn & Hbc)".
    iDestruct "Hlit" as (vil vin vic) "(Hiw & Hin & Hic)".
    iDestruct "Hlft" as (vfl vfn vfc) "(Hfw & Hfn & Hfc)".
    iDestruct "Hldisk" as (vdl vdn vdc) "(Hdw & Hdn & Hdc)".
    iDestruct "Hdiskptr" as (pd0 pav0 pu0) "(Hdd0 & Hda0 & Hdu0)".
    iDestruct "Hinitproc" as (iv0) "Hinitproc".
    (* the two allocator-budget facts, in the closed form the callees ask for *)
    assert (Hnb3 : exists nb, avail_sub (Some (length ps)) K_kvmmake = Some nb
                              /\ (3 <= nb)%nat).
    { exists (length ps - K_kvmmake)%nat. split; [apply avail_sub_Some | lia]. }
    assert (Hnb8 : exists nb,
              avail_sub (avail_sub (Some (length ps)) K_kvmmake) 3 = Some nb
              /\ (userinit_pages <= nb)%nat).
    { exists (length ps - K_kvmmake - 3)%nat.
      rewrite !avail_sub_Some. split; [reflexivity | unfold userinit_pages; lia]. }
    (* ---- +0x8e jal binit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x8e)) (mword_of_int 1 : mword 5)
              (mword_of_int 7194 : mword 21) m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi8e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (F1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x8e) : mword 64) 4)]> m).
    assert (Htgtbi : add_vec (mword_of_int (KernelSyms.main + 0x8e) : mword 64)
              (sign_extend' 64 (mword_of_int 7194 : mword 21))
              = (mword_of_int KernelSyms.binit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbi) in "Hpc".
    iApply (Binit.wp_binit_sconf F1 n vbl vbn vbc false p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Hbw Hbn Hbc Hbufl Hbufn Hbhead").
    iApply wp_next_off_intro.
    iIntros (mbi) "Hcg Hpc %Hcsbi _ _ _ _ _".
    assert (Hretbi : ret_pc (F1 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x92) : mword 64)).
    { rewrite /F1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretbi) in "Hpc".
    (* ---- +0x92 jal iinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x92)) (mword_of_int 1 : mword 5)
              (mword_of_int 8556 : mword 21) mbi n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi92").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (F2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x92) : mword 64) 4)]> mbi).
    assert (Htgtii : add_vec (mword_of_int (KernelSyms.main + 0x92) : mword 64)
              (sign_extend' 64 (mword_of_int 8556 : mword 21))
              = (mword_of_int KernelSyms.iinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtii) in "Hpc".
    iApply (Iinit.wp_iinit_sconf F2 n vil vin vic false p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Hiw Hin Hic Hinl").
    iApply wp_next_off_intro.
    iIntros (mii) "Hcg Hpc %Hcsii _ _ _ _".
    assert (Hretii : ret_pc (F2 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x96) : mword 64)).
    { rewrite /F2 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretii) in "Hpc".
    (* ---- +0x96 jal fileinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x96)) (mword_of_int 1 : mword 5)
              (mword_of_int 12612 : mword 21) mii n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi96").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (F3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x96) : mword 64) 4)]> mii).
    assert (Htgtfi : add_vec (mword_of_int (KernelSyms.main + 0x96) : mword 64)
              (sign_extend' 64 (mword_of_int 12612 : mword 21))
              = (mword_of_int KernelSyms.fileinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtfi) in "Hpc".
    iApply (Fileinit.wp_fileinit_sconf F3 n vfl vfn vfc false p0 ltac:(lia)
              with "Hcg Htext Hkdata Hpc Hfw Hfn Hfc").
    iApply wp_next_off_intro.
    iIntros (mfi) "Hcg Hpc %Hcsfi _ _ _".
    assert (Hretfi : ret_pc (F3 !!! Regidx (mword_of_int 1 : mword 5) : mword 64)
                     = (mword_of_int (KernelSyms.main + 0x9a) : mword 64)).
    { rewrite /F3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretfi) in "Hpc".
    (* ---- +0x9a jal virtio_disk_init ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x9a)) (mword_of_int 1 : mword 5)
              (mword_of_int 18382 : mword 21) mfi n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi9a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (F4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x9a) : mword 64) 4)]> mfi).
    assert (Htgtvd : add_vec (mword_of_int (KernelSyms.main + 0x9a) : mword 64)
              (sign_extend' 64 (mword_of_int 18382 : mword 21))
              = (mword_of_int KernelSyms.virtio_disk_init : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtvd) in "Hpc".
    (* the pinned-map re-point [mn_pin_sie_cap_gpr] exists for: virtio_disk_init
       is the ONE callee left demanding a raw-map tp fact. *)
    iDestruct (mn_pin_sie_cap_gpr with "Hcg") as "Hcg".
    iApply (VirtioDiskInit.wp_virtio_disk_init_sconf γv γa (tp_pin F4) n false p0
              (avail_sub (Some (length ps)) K_kvmmake) c0
              vdl vdn vdc pd0 pav0 pu0 free0 ∅ ltac:(lia)
              Hnb3 (rget_tp F4) Hlive
              with "Hcg Hcpu Htext Hkdata Hpc Hkenv Hdinv Hcfg
                    Hdw Hdn Hdc Hdd0 Hda0 Hdu0 Hdiskfree").
    all: try lkbelow.
    rewrite /vdi_post.
    iIntros (mvd pd pav pu) "Hcg Hcpu Hpc %Hcsvd %Hpvd %Hpva %Hpvu Hkenv".
    iIntros "Hpub #Hdcfg Hdescpg Havpg Hdd Hda Hdu Hdfree Hdlkw Hdlnm Hdcpu".
    assert (Hretvd : ret_pc (tp_pin F4 !!! Regidx (mword_of_int 1 : mword 5) : mword 64)
                     = (mword_of_int (KernelSyms.main + 0x9e) : mword 64)).
    { rewrite (mn_tp_pin_ne F4 (mword_of_int 1 : mword 5) ltac:(reg_neq)).
      rewrite /F4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretvd) in "Hpc".
    (* ---- ASSEMBLY 3: the disk's geometry, its lock resource, and the lock. *)
    assert (Hal : virtio_pages_aligned (virtio_init_cfg pd pav pu))
      by (apply init_cfg_pages_aligned_of_valid; assumption).
    assert (Hedd : disk_desc = (d_desc_ptr : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Heda : disk_avail = (d_avail_ptr : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hedu : disk_used = (d_used_ptr : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Heldk : disk_lock = (d_lock : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hedd) in "Hdd".
    iEval (rewrite Heda) in "Hda".
    iEval (rewrite Hedu) in "Hdu".
    iEval (rewrite Heldk) in "Hdlkw".
    iEval (rewrite Heldk) in "Hdlnm".
    iEval (rewrite Heldk) in "Hdcpu".
    iApply fupd_wp.
    iMod (word_pointsto_persist with "Hdd") as "#Hddp".
    iMod (word_pointsto_persist with "Hda") as "#Hdap".
    iMod (word_pointsto_persist with "Hdu") as "#Hdup".
    iAssert (disk_geom γv pd pav pu) as "#Hgeom".
    { rewrite /disk_geom.
      iSplitR; [iExact "Hddp"|]. iSplitR; [iExact "Hdap"|].
      iSplitR; [iExact "Hdup"|]. iSplitR; [iPureIntro; exact Hal|].
      iSplitR; [iExact "Hdcfg"|].
      iSplitR; [iPureIntro; intros j Hj;
                apply page_in_range_addr_is_kdata; [exact Hpvd | exact Hj]|].
      iSplitR; [iPureIntro; intros j Hj;
                apply page_in_range_addr_is_kdata; [exact Hpva | exact Hj]|].
      iPureIntro; intros j Hj;
        apply page_in_range_addr_is_kdata; [exact Hpvu | exact Hj]. }
    iPoseProof (disk_res_boot γv pd pav pu Hal
                  with "Hpub Hdescpg Havpg Hdfree Hdusedidx Hdslots Hdone Hclaim")
      as "HRdisk".
    iMod (newlock ⊤ d_lock "virtio_disk"%string (disk_res γv pd pav pu)
            with "Hdlnm Hdlkw Hdcpu HRdisk") as (γk) "#Hdlock".
    iModIntro.
    (* ---- +0x9e jal userinit ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x9e)) (mword_of_int 1 : mword 5)
              (mword_of_int 3294 : mword 21) mvd n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi9e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (F5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x9e) : mword 64) 4)]> mvd).
    assert (Htgtui : add_vec (mword_of_int (KernelSyms.main + 0x9e) : mword 64)
              (sign_extend' 64 (mword_of_int 3294 : mword 21))
              = (mword_of_int KernelSyms.userinit : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtui) in "Hpc".
    iApply (Userinit.wp_userinit_sconf γa γs F5 n false p0
              (avail_sub (avail_sub (Some (length ps)) K_kvmmake) 3) iv0 false ∅
              ltac:(lia) Hnb8
              with "Hcg Htext Hkdata Hpc Hcpu Hpinv Hkenv Hinitproc").
    iApply wp_next_off_intro.
    iIntros (mui) "Hcg Hpc %Hcsui Hcpu _ _".
    destruct Hcsui as (Hcsui & _).
    assert (Hretui : ret_pc (F5 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0xa2) : mword 64)).
    { rewrite /F5 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretui) in "Hpc".
    iApply ("Hcont" $! γk pd pav pu mui with "Hcg Hpc Hfree Hcpu Hdlock Hgeom").
  Qed.

  (* =================================================================== *)
  (* 0xa2 .. 0xb0 then the join at 0x3e -- the release fence, the         *)
  (* [started = 1] deposit, and [jal scheduler] (which never returns).    *)
  (* =================================================================== *)
  Local Lemma mn_grp_started 
      (γpr γk γa : gname) (γs : list gname)
      (γd : uart_names) (γv : disk_names)
      (m : regfile) (n : nat) (p0 : mword 64) (pd pav pu : mword 64)
      (root : mword 44) (pas : nat -> mword 44)
      (P : iProp Σ) `{!Persistent P} :
    (* the scheduler this block tail-calls enables interrupts at its loop head
       and must fund [kv_frame_slots] there; see [SpecScheduler]. *)
    (kv_frame_slots + 20 <= n)%nat ->
    p0 = zero_reg ->
    sie_cap_gpr KT1 m n false p0 -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.main + 0xa2) : mword 64) -∗
    cpu_ctx_free -∗
    cpu_own 0 false p0 false ∅ -∗
    trap_csrs KT1 -∗
    started_inv P -∗
    □ (∀ (γpr' : gname) (γs' : list gname) (γk' : gname) (pd' pav' pu' : mword 64)
         (root' : mword 44) (pas' : nat -> mword 44),
         printk_env γpr' γd γv -∗
         procs_inv γs' -∗
         console_caps γd -∗
         is_lock γk' d_lock "virtio_disk"%string (disk_res γv pd' pav' pu') -∗
         disk_geom γv pd' pav' pu' -∗
         kpt_inv root' -∗
         (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈□
           (zero_extend' 64 (concat_vec root' (zeros' 12 : mword 12))) -∗
         kmap_at tramp_vpn tramp_ppn KP_rx -∗
         ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas' i) KP_rw) -∗
         P) -∗
    printk_env γpr γd γv -∗
    procs_inv γs -∗
    console_caps γd -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γv pd pav pu) -∗
    disk_geom γv pd pav pu -∗
    kpt_inv root -∗
    (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈□
      (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hp0.
    iIntros "Hcg #Htext Hpc Hfree Hcpu Htcsr #Hsinv #Hwand".
    iIntros "#Hpenv #Hpinv #Hccaps #Hdlock #Hgeom #Hkinv #Hkptp #Htramp #Hkstx".
    iPoseProof (mni_a2 with "Htext") as "Hia2".
    iPoseProof (mni_a6 with "Htext") as "Hia6".
    iPoseProof (mni_aa with "Htext") as "Hiaa".
    iPoseProof (mni_ac with "Htext") as "Hiac".
    iPoseProof (mni_b0 with "Htext") as "Hib0".
    iPoseProof (mni_b2 with "Htext") as "Hib2".
    iPoseProof (mni_3e with "Htext") as "Hi3e".
    (* the deposit itself: everything main built, through the □-wand *)
    iAssert P as "#HP".
    { iApply ("Hwand" $! γpr γs γk pd pav pu root pas
                with "Hpenv Hpinv Hccaps Hdlock Hgeom Hkinv Hkptp Htramp Hkstx"). }
    (* The release sequence.  Note the shape: the address is materialized
       BEFORE the barrier and the store is the compressed [c.sw], so the
       fence separates the whole deposit from the store alone -- and it is
       [rw,w], not [rw,rw]: nothing after it reads. *)
    (* ---- +0xa2 auipc a5,0x9 : start materializing &started ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.main + 0xa2)) (mword_of_int 15 : mword 5)
              (mword_of_int 9 : mword 20) m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia2").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (S1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.main + 0xa2) : mword 64)
           (auipc_off (mword_of_int 9 : mword 20)))]> m).
    assert (Hpa6 : add_vec_int (mword_of_int (KernelSyms.main + 0xa2) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa6) in "Hpc".
    (* ---- +0xa6 addi a5,a5,944 : a5 := &started ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.main + 0xa6)) (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 978 : mword 12) S1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia6").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (S2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (rget S1 (mword_of_int 15 : mword 5))
           (sign_extend' 64 (mword_of_int 978 : mword 12)))]> S1).
    assert (Hpaa : add_vec_int (mword_of_int (KernelSyms.main + 0xa6) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpaa) in "Hpc".
    (* ---- +0xaa li a4,1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.main + 0xaa)) (mword_of_int 14 : mword 5)
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) S2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hiaa").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (S3 := <[Regidx (mword_of_int 14 : mword 5) :=
        regval_into_reg (mword_of_int 1 : mword 64)]> S2).
    assert (Hpac : add_vec_int (mword_of_int (KernelSyms.main + 0xaa) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac) in "Hpc".
    (* ---- +0xac fence rw,w : the release barrier ---- *)
    iApply (wp_fence_gen_s_sconf (mword_of_int (KernelSyms.main + 0xac))
              (mword_of_int 0 : mword 4) (mword_of_int 3 : mword 4)
              (mword_of_int 1 : mword 4) (Regidx (mword_of_int 0))
              (Regidx (mword_of_int 0)) S3 n false with "Hcg Hpc Hiac").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpb0 : add_vec_int (mword_of_int (KernelSyms.main + 0xac) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpb0) in "Hpc".
    assert (Hsa : add_vec (rget S3 (mword_of_int 15 : mword 5))
                    (sign_extend' 64 (mword_of_int 0 : mword 12)) = started_addr).
    { rgne. rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_eq. rgne.
      rewrite /S1 upd_eq /started_addr. apply bv_eq; vm_compute; reflexivity. }
    assert (HS3a4 : rget S3 (mword_of_int 14 : mword 5)
                    = (mword_of_int 1 : mword 64)).
    { rgne. rewrite /S3 upd_eq. reflexivity. }
    assert (Hsvst : trunc32 (rget S3 (mword_of_int 14 : mword 5)) = started_set).
    { rewrite HS3a4 /trunc32 /started_set. apply bv_eq; vm_compute; reflexivity. }
    (* ---- +0xb0 sw a4,0(a5) : started = 1, paying [P] into the escrow ---- *)
    (* THE ADDRESS CLAIM the per-node store asks for (WpSconfMem.wordw_claim):
       per node the access TRANSLATES before it writes, so the window's
       mapping is needed BEFORE the atomic update is opened.  The claim is
       persistent and says nothing about the VALUE, so one peek-open of the
       started invariant delivers it and puts the body straight back. *)
    iApply fupd_wp.
    iMod (inv_acc ⊤ startedN with "Hsinv") as "[Hbody Hclose]"; [ solve_ndisj | ].
    iDestruct "Hbody" as (vpk) "[>Hword Hrest]".
    iDestruct (wordw_claim_of (KTR := KT0) 4 started_addr (DfracOwn 1) vpk
                 ltac:(lia) with "Hword") as "#Hstcl".
    iMod ("Hclose" with "[Hword Hrest]") as "_".
    { iNext. iExists vpk. iFrame "Hword Hrest". }
    iModIntro.
    iApply (wp_store_s_sconf_au (kt := KT1) (ktd := KT0) 4 true (mword_of_int (KernelSyms.main + 0xb0))
              (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 12) S3 n
              (trunc32 (rget S3 (mword_of_int 14 : mword 5))) True%I
              ((⊤ ∖ ↑minstretN) ∖ ↑startedN) false
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity) exec_write_ram_plain_4
              (store_ext_4 (rget S3 (mword_of_int 14 : mword 5)))
              ltac:(solve_ndisj) with "Hcg Hpc Hib0 [] [HP]").
    { rewrite Hsa. iExact "Hstcl". }
    { rewrite Hsa Hsvst.
      iApply (started_inv_store_au (⊤ ∖ ↑minstretN) P ltac:(solve_ndisj)
                with "Hsinv HP"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    iEval (change (if true then 2%Z else 4%Z) with 2%Z) in "Hpc".
    assert (Hpb2 : add_vec_int (mword_of_int (KernelSyms.main + 0xb0) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpb2) in "Hpc".
    (* ---- +0xb2 j 0x3e : back to the join the secondary arm also reaches ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.main + 0xb2))
              (sign_extend' 21 (concat_vec (mword_of_int 1990 : mword 11) ('b"0")))
              S3 n false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hib2").
    iApply wp_next_off_intro.
    iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgtj : add_vec (mword_of_int (KernelSyms.main + 0xb2) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 1990 : mword 11) ('b"0"))))
              = (mword_of_int (KernelSyms.main + 0x3e) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtj) in "Hpc".
    (* ---- +0x3e jal scheduler : main's exit; scheduler never returns ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x3e)) (mword_of_int 1 : mword 5)
              (mword_of_int 3818 : mword 21) S3 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (SS := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x3e) : mword 64) 4)]> S3).
    assert (Htgtsc : add_vec (mword_of_int (KernelSyms.main + 0x3e) : mword 64)
              (sign_extend' 64 (mword_of_int 3818 : mword 21))
              = (mword_of_int KernelSyms.scheduler : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtsc) in "Hpc".
    iApply (Scheduler.wp_scheduler_sconf γs SS n p0 Hp0 ltac:(lia)
              with "Hcg Hfree Hcpu Htext Hpc Hpinv Htcsr").
  Qed.

  (* =================================================================== *)
  (* THE CONTRACT.                                                        *)
  (* =================================================================== *)
  Lemma wp_main_boot_sconf 
      (m : regfile) (K : nat) (p0 : mword 64)
      (ps : list (mword 64)) (s1entry phystop : mword 64)
      (γd : uart_names) (γv : disk_names)
      (l0 : list (bv 8)) (b0 : bool) (c0 : virtio_cfg)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (P : iProp Σ) `{!Persistent P}
    : wp_main_boot_sconf_body m K p0 ps s1entry phystop
        γd γv l0 b0 c0 tlbvec0 P.
  Proof.
    cbv beta delta [wp_main_boot_sconf_body].
    intros pcE Hcid HK Hphystop Hs1 Hprun Hlen Hlive Hp0.
    pose proof (mn_bounds K HK) as (Hc2 & Hn50 & Hnsched).
    iIntros "Hcg Hfree Hcpu Hq #Htext #Hkdata Hpc #Hsinv #Hwand Hlocks Hglobals".
    iIntros "Hparks Hpst".
    iIntros "#Hdev Htx Hsent Hlb Hdlab Hcfg Hclaim #Hdone #Htimc Hhart Hunset Hkauth Hpages".
    iDestruct "Hlocks" as "(Hlcons & Hltx & Hlpr & Hlkmem & Hlpid & Hlwait &
                            Hltick & Hlbc & Hlit & Hlft & Hldisk)".
    (* THE [tx_busy] CELL IS GONE from the bundle: ae96fd0 deleted the flag, so
       there is no such symbol and nothing to carve (BootShared.v skips the
       word, which is now [tx_chan], and nobody owns it).  [Hltx] is still
       carried, and is the ordinary [lk_raw] spinlock shape (three cells over
       24 bytes): uartinit's [initlock(&tx_lock,"uart")] consumes it and
       consoleinit returns [lk_fresh].  What the flag was being carried FOR is
       still gone -- uartintr takes no lock, so [is_txlock] left
       [devintr_caps] entirely -- and the [newlock] step
       that would turn that [lk_fresh] into [is_txlock] is not taken here; see
       [mn_grp_printk].
       [Hient] -- the fifty itable entries' cells -- is still carried and
       DROPPED here: its only consumer is [IcacheBoot.icache_boot], whose other
       input (the stocked inode pool) needs the fs BLOCK layer wired into main.
       See claude-notes/projects/fs-icache.md, C7 owed (ii). *)
    iDestruct "Hglobals" as "(Hdevsw & Hkmem24 & Hkpt & Hprocs & Hppub &
                             Hfds & Hirs & Hinitproc & Hticks & Hbufl & Hbufn & Hbhead & Hinl &
                             Hient & Hdiskptr & Hdiskfree & Hdusedidx & Hdslots & Hring)".
    iDestruct "Hhart" as "(Hsbit & Htlb & Htcsr)".
    iDestruct "Hdiskfree" as (free0) "Hdiskfree".
    (* --- 0x00 .. 0x14 : prologue, cpuid, the taken branch --- *)
    iApply (mn_boot_entry m K p0 Hcid HK with "Hcg Htext Hpc").
    iIntros (m1) "Hcg Hpc".
    (* --- 0x42 .. 0x6a : console / printk --- *)
    iApply (mn_grp_printk γd γv m1 (K - 2)%nat p0 l0 b0 Hn50
              with "Hcg Htext Hkdata Hdev Hpc Hfree Hcpu Hlcons Hltx Hlpr
                    Hdevsw Hring Htx Hsent Hlb Hdlab").
    iIntros (γpr m2) "Hcg Hpc Hfree Hcpu #Hpenv #Hccaps".
    (* --- 0x6e .. 0x7a : kinit / kvminit / kvminithart / procinit --- *)
    iApply (mn_grp_kvm m2 (K - 2)%nat p0 ps s1entry phystop tlbvec0
              Hn50 Hphystop Hs1 Hprun Hlen
              with "Hcg Htext Hkdata Hpc Hfree Hcpu Hlkmem Hkmem24 Hpages Hkpt
                    Hsbit Htlb Hunset Hkauth Hlpid Hlwait Hprocs Hppub Hfds Hirs
                    Hparks Hpst").
    iIntros (γa γs m3 root pas)
      "Hcg Hpc Hfree Hcpu Hkenv #Hpinv Hkpt Hstvec #Hkinv #Hkptp #Htramp #Hkstx".
    (* --- 0x7e .. 0x8a : trap / plic, and the interrupt invariant --- *)
    iApply (mn_grp_trap γd γv m3 (K - 2)%nat p0 Hn50 Hcid
              with "Hcg Htext Hkdata Hdev Hpc Hltick Hticks Hstvec Hq").
    iIntros (m4 γtl) "Hcg Hpc #Htl Hstvec Hq".
    (* --- 0x8e .. 0x9e : binit / iinit / fileinit / virtio_disk_init /
           userinit, and the disk lock --- *)
    iApply (mn_grp_fs γa γs γv γd m4 (K - 2)%nat p0 ps c0 free0
              Hn50 Hlen Hlive
              with "Hcg Htext Hkdata Hdev Hpc Hfree Hcpu Hpinv Hkenv Hlbc Hbufl
                    Hbufn Hbhead Hlit Hinl Hlft Hldisk Hdiskptr Hdiskfree
                    Hdusedidx Hdslots Hclaim Hdone Hcfg Hinitproc").
    iIntros (γk pd pav pu m5) "Hcg Hpc Hfree Hcpu #Hdlock #Hgeom".
    (* ---- THE INSTALLED-HANDLER RESOURCE, folded HERE and not earlier: the
           handler contract closes over [devintr_caps], and its disk lock and
           geometry are exactly what the group above just produced.  ALL SEVEN
           members are now in hand and NONE is assumed: [dev_inv], [procs_inv],
           the disk lock and geometry from the group above,
           [timer_cap] handed in by the boot chain (which mints it out of the
           two cells timerinit wrote), and the tick keeper below. ---- *)
    iDestruct (procs_inv_len with "Hpinv") as %Hnproc.
    (* THE TICK KEEPER IS NOT ASSUMED: hart 0 IS the tick hart
       ([tick_hart] is [cpuid() == 0]), so it owes the real arm -- the lock
       trapinit's group brought up, plus [procs_inv]. *)
    iAssert (tick_keeper γtl γs) as "#Htick".
    { iRight. iFrame "Htl Hpinv". }
    iAssert (devintr_caps γd γv γk γtl γs pd pav pu) as "#Hcaps".
    { rewrite /devintr_caps.
      iFrame "Hdev Hccaps Hgeom Hdlock Htimc Htick Hpinv". }
    iDestruct (mn_dup_hw with "Hcg") as "(#Hhw & #Hmin & Hcg)".
    iPoseProof (Kernelvec.kernelvec_handler_spec γd γv γk γtl γs pd pav pu
                  Hnproc with "Hhw Hmin Htext Hcaps") as "#Hkvs".
    iDestruct (intr_res_intro (mword_of_int KernelSyms.kernelvec : mword 64) _
                 kernelvec_tv_direct kernelvec_stvec_base with "Hq Hstvec []")
      as "Hintr".
    { iApply bi.later_intro. iExact "Hkvs". }
    (* --- 0xa2 .. the join : the deposit and the scheduler --- *)
    iApply (mn_grp_started γpr γk γa γs γd γv m5 (K - 2)%nat p0 pd pav pu
              root pas P ltac:(lia) Hp0
              with "Hcg Htext Hpc Hfree Hcpu [Htcsr Hintr Hkpt] Hsinv Hwand Hpenv
                    Hpinv Hccaps Hdlock Hgeom Hkinv Hkptp Htramp Hkstx").
    (* fold the boot cells and the freshly built handler resource into the
       [trap_csrs] the scheduler consumes. *)
    iApply (trap_csrs_of_raw with "Htcsr Hintr Hkpt").
  Qed.

End ProofMain.
End MainProof.
