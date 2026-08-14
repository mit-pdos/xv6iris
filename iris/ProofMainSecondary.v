(* ProofMainSecondary.v -- the whole-function WP for xv6's main(), SECONDARY-
   HART arm.

     void main() {
       if (cpuid() == 0) { ... } else {
         while (started == 0) ;
         __atomic_thread_fence(__ATOMIC_SEQ_CST);
         printk("hart %d starting\n", cpuid());
         kvminithart(); trapinithart(); plicinithart();
       }
       scheduler();
     }

   A sealed functor over the seven callee interfaces this arm actually uses
   (cpuid, printk-general, kvminithart, trapinithart, plicinithart, scheduler,
   and KERNELVEC -- whose handler contract is what turns trapinithart's
   [stvec ↦ᵣ kernelvec] into the [intr_res] scheduler wants).  main
   never returns, so there is no epilogue and no [callee_saved] obligation --
   and since [tp] is PINNED to the hart (HartTp.v) there is no register fact
   left to thread across the calls at all: every callee that used to demand
   [tp = cid_word] now reads [rget _ Rtp] and gets [cid_word] by construction.

   STRUCTURE.  One [Local Lemma] per block, each concluding at the next offset
   (the last one diverges), chained by [wp_main_secondary_sconf]:

     ms_entry           0x00 -> 0x16   frame push, jal cpuid, beqz FALL
     ms_spin            0x16 -> 0x20   the iLöb spin loop on [started]
                                       + the acquire fence, which is where
                                         the [▷] comes off the deposit
     ms_printk          0x20 -> 0x32   jal cpuid; printk("hart %d starting\n")
     ms_inithart_sched  0x32 -> (join) kvminithart trapinithart plicinithart
                                       + intr_inv_alloc_off, then jal scheduler

   Everything a block does not touch stays in the caller's context: each
   lemma's conclusion is a bare [WP Loop {{Φ}}]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List Ascii String.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import RiscvFetchExec MinstretInv.
Require Import SmodeCore RegFile HartTp WpNext WpMmodeLeafBase InstrBytes.
Require Import StackOwn.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpLock.
Require Import KallocInv.
Require Import PanicStub.
Require Import KptShare.
Require Import CpuOwn SchedCtx FdSlots.
Require Import FileInvDefs.
Require Import DevModel DiskPtsto WpUart.
Require Import PrintkFmt.
Require Import PanicStub StartedInv.
Require Import SpecCpuid SpecPrintk.
Require Import SpecKvminithart SpecTrapinithart SpecPlicinithart.
Require Import SpecScheduler SpecKernelvec.
Require Import SpecDevintr SpecClockintr DiskInv TimerCap.
Require Import SpecConsoleintr.
Require Import SpecMainSecondary.
Require Import CodeMain.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.
Local Strategy 1000 [pa_stk].

(* ===================================================================== *)
(* The one format string the secondary arm passes to printk, and the      *)
(* address its auipc/addi pair resolves to (.rodata, just above etext).    *)
(* ===================================================================== *)
Definition ms_nl : string := String (Ascii.ascii_of_nat 10) EmptyString.
Definition ms_hart : string := ("hart %d starting" ++ ms_nl)%string.
Definition ms_hart_addr : Z := 0x80007098.

Lemma ms_hart_bytes : forall j b, cstring_bytes ms_hart !! j = Some b ->
  KernelData.kernel_data !! (ms_hart_addr + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 18 (destruct j as [|j];
         [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma ms_hart_fmt : pk_kinds ms_hart = [PkNum] /\ nonul ms_hart = true /\
                    (Z.of_nat (String.length ms_hart) < 2147483645)%Z.
Proof. split_and!; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

(* clean-context (mword-free) nat arithmetic, so [lia] never sees a bv *)
(* the last conjunct is the SCHEDULER's, and it is what [K_main_secondary] is
   sized by: the loop-head enable funds [kv_frame_slots] out of what the arm
   hands it. *)
Lemma ms_bounds (K : nat) : (K_main_secondary <= K)%nat ->
  (2 <= K)%nat /\ (48 <= K - 2)%nat /\ (kv_frame_slots + 20 <= K - 2)%nat.
Proof. unfold K_main_secondary, kv_frame_slots. lia. Qed.

(* ===================================================================== *)
Module MainSecondaryProof
  (Cpuid : CPUID) (PrintkGen : PRINTK_GEN) (Kvminithart : KVMINITHART)
  (Trapinithart : TRAPINITHART) (Plicinithart : PLICINITHART)
  (Scheduler : SCHEDULER) (Kernelvec : KERNELVEC)
  : MAIN_SECONDARY.

Section ProofMainSecondary.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* [hw_config] + [minstret_inv], both persistent, out of the ambient
     bundle -- what [Kernelvec.kernelvec_handler_spec] consumes. *)
  Local Lemma ms_dup_hw m avail b p :
    sie_cap_gpr m avail b p -∗ hw_config ∗ minstret_inv ∗ sie_cap_gpr m avail b p.
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

  (* =================================================================== *)
  (* 0x00 .. 0x14 -- the frame push, [jal cpuid], and the [beqz a0] that  *)
  (* the secondary premise [cid_word <> 0] makes FALL THROUGH into the    *)
  (* spin loop at 0x16.  It also names [a4 = &started], materialized once *)
  (* by the auipc/addi pair at 0x0c/0x10 and reused by the loop.          *)
  (* =================================================================== *)
  Local Lemma ms_entry 
      (m : regfile) (K : nat) (p0 : mword 64) :
    cid_word <> (zero_reg : mword 64) ->
    (K_main_secondary <= K)%nat ->
    sie_cap_gpr m K false p0 -∗ kernel_text -∗
    pc_is (mword_of_int KernelSyms.main : mword 64) -∗
    ( ∀ m1 : regfile,
        sie_cap_gpr m1 (K - 2)%nat false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0x16) : mword 64) -∗
        ⌜ add_vec (rget m1 (mword_of_int 14 : mword 5))
            (sign_extend' 64 (mword_of_int 0 : mword 12)) = started_addr ⌝ -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hcid HK.
    pose proof (ms_bounds K HK) as (Hc2 & Hn38 & Hn20).
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
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
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
    iApply (Cpuid.wp_cpuid_sconf W3 (K - 2)%nat p0 ltac:(lia) with "Hcg Htext Hpc").
    iIntros (m4) "Hcg Hpc %Hcp".
    destruct Hcp as (Hcpcs & Hcpa0).
    assert (Hretcp : ret_pc (W3 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x0c) : mword 64)).
    { rewrite /W3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretcp) in "Hpc".
    (* cpuid() returns [cpuid_ret (rget W3 tp)], and tp IS this hart's id -- no
       detour through the map's (now unobservable) tp slot. *)
    assert (Hm4a0 : m4 !!! Regidx (mword_of_int 10 : mword 5) = cid_word).
    { rewrite Hcpa0 (rget_tp W3). exact cpuid_ret_cid. }
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
    (* +0x10 addi a4,a4,1094 : a4 := &started, which the spin loop reads *)
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
    assert (HW6a0 : eq_vec (rget W6 (mword_of_int 10 : mword 5)) zero_reg = false).
    { rgne. rewrite /W6 upd_ne; [| reg_neq]. rewrite /W5 upd_ne; [| reg_neq].
      rewrite Hm4a0. exact (proj2 (eq_vec_false_iff _ _) Hcid). }
    assert (HW6a4 : add_vec (rget W6 (mword_of_int 14 : mword 5))
                      (sign_extend' 64 (mword_of_int 0 : mword 12)) = started_addr).
    { rgne. rewrite /W6 upd_eq. rgne. rewrite /W5 upd_eq /started_addr.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x14 beqz a0,+0x2e -- FALLS THROUGH, into the spin loop at 0x16 *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.main + 0x14))
              (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 2))
              (mword_of_int 10 : mword 5) W6 (K - 2)%nat false
              creg_c2 ltac:(vm_compute; discriminate) HW6a0
              with "Hcg Hpc Hi14").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.main + 0x14) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    iApply ("Hcont" $! W6 with "Hcg Hpc"). iPureIntro. exact HW6a4.
  Qed.

  (* =================================================================== *)
  (* 0x16 .. 0x1e -- [while (started == 0) ;] with the acquire fence.     *)
  (* =================================================================== *)
  Local Lemma ms_spin
      (γd : uart_names) (γv : disk_names) (m : regfile) (n : nat)
      (p0 : mword 64) :
    add_vec (rget m (mword_of_int 14 : mword 5))
        (sign_extend' 64 (mword_of_int 0 : mword 12)) = started_addr ->
    sie_cap_gpr m n false p0 -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.main + 0x16) : mword 64) -∗
    started_inv (main_deposit γd γv) -∗
    ( ∀ m' : regfile,
        sie_cap_gpr m' n false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0x20) : mword 64) -∗
        main_deposit γd γv -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha4.
    iIntros "Hcg #Htext Hpc #Hsinv Hcont".
    iLöb as "IH" forall (m Ha4).
    iPoseProof (mni_16 with "Htext") as "Hi16".
    iPoseProof (mni_18 with "Htext") as "Hi18".
    iPoseProof (mni_1c with "Htext") as "Hi1c".
    iPoseProof (mni_1e with "Htext") as "Hi1e".
    (* ---- +0x16 c.lw a5,0(a4) : the spin load, under the invariant ---- *)
    iApply (wp_load_s_sconf_au 4 true false (mword_of_int (KernelSyms.main + 0x16))
              (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (mword_of_int 0 : mword 12) m n
              (fun v => sign_extend' 64 v)
              (fun v => (▷ (⌜v = started_clear⌝ ∨ main_deposit γd γv))%I)
              ((⊤ ∖ ↑minstretN) ∖ ↑startedN) false
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity) exec_read_ram_plain_4 data2_ext_4
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(solve_ndisj) with "Hcg Hpc Hi16 []").
    { rewrite Ha4.
      iApply (started_inv_load_au (⊤ ∖ ↑minstretN) (main_deposit γd γv)
                ltac:(solve_ndisj) with "Hsinv"). }
    iIntros (v).
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc HPsi".
    pose (M1 := <[Regidx (mword_of_int 15 : mword 5) :=
        regval_into_reg (sign_extend' 64 (v : mword 32))]> m).
    iEval (change (if true then 2%Z else 4%Z) with 2%Z) in "Hpc".
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.main + 0x16) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* ---- +0x18 fence r,rw : THE ACQUIRE BARRIER.  9dd28f5 moved it INSIDE
           the loop, so it now runs on every iteration rather than once on the
           way out -- but it is still the one step whose continuation is under
           a [▷], which is what turns the invariant's [▷ deposit] into the
           deposit.  Stripping here rather than on the exit path is harmless:
           the iteration that goes around again just drops the payload. ---- *)
    iApply (wp_fence_gen_later_s_sconf (mword_of_int (KernelSyms.main + 0x18))
              (mword_of_int 0 : mword 4) (mword_of_int 2 : mword 4)
              (mword_of_int 3 : mword 4) (Regidx (mword_of_int 0))
              (Regidx (mword_of_int 0)) M1 n false with "Hcg Hpc Hi18").
    iApply wp_next_off_intro.
    iNext.
    iIntros "Hcg Hpc".
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.main + 0x18) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    (* ---- +0x1c c.addiw a5,0 : sext.w a5 ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.main + 0x1c)) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 6) M1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (M2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (rget M1 (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> M1).
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.main + 0x1c) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    assert (HM2a5 : rget M2 (mword_of_int 15 : mword 5)
              = sign_extend' 64 (subrange_vec_dec
                   (add_vec (sign_extend' 64 (v : mword 32))
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)).
    { rgne. rewrite /M2 upd_eq. rgne. rewrite /M1 upd_eq. reflexivity. }
    assert (HM2a4 : add_vec (rget M2 (mword_of_int 14 : mword 5))
                      (sign_extend' 64 (mword_of_int 0 : mword 12)) = started_addr).
    { rgne. rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [| reg_neq].
      rewrite -Ha4. rgne. reflexivity. }
    (* ---- +0x1e c.beqz a5,-8 : back to the load while [started] is 0.  The
           back edge is 8 now, not 4: the fence is inside the loop. ---- *)
    destruct (eq_vec (rget M2 (mword_of_int 15 : mword 5)) zero_reg) eqn:Hbz.
    - (* still zero: around the loop again, and the payload is dropped *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.main + 0x1e))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 7))
                (mword_of_int 15 : mword 5) M2 n false
                creg_c7 ltac:(vm_compute; discriminate) Hbz
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1e").
      iApply wp_next_off_intro.
      iNext. iIntros "Hcg Hpc".
      assert (Htgtl : add_vec (mword_of_int (KernelSyms.main + 0x1e) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                = (mword_of_int (KernelSyms.main + 0x16) : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtl) in "Hpc".
      iApply ("IH" $! M2 with "[%] Hcg Hpc Hcont").
      { exact HM2a4. }
    - (* [started] is set: fall through, carrying the deposit the fence at
         +0x18 already brought out from under its [▷] *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.main + 0x1e))
                (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 7))
                (mword_of_int 15 : mword 5) M2 n false
                creg_c7 ltac:(vm_compute; discriminate) Hbz
                with "Hcg Hpc Hi1e").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.main + 0x1e) : mword 64) 2
                     = mword_of_int (KernelSyms.main + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp20) in "Hpc".
      iDestruct "HPsi" as "[%Hv0 | #Hdep]".
      + (* the word read as 0 contradicts the branch having fallen through *)
        exfalso. rewrite HM2a5 Hv0 in Hbz. vm_compute in Hbz. discriminate.
      + iApply ("Hcont" $! M2 with "Hcg Hpc Hdep").
  Qed.

  (* =================================================================== *)
  (* 0x20 .. 0x2e -- [printk("hart %d starting\n", cpuid())].             *)
  (* =================================================================== *)
  Local Lemma ms_printk (γpr : gname) 
      (γd : uart_names) (γv : disk_names)
      (m : regfile) (n : nat) (p0 : mword 64) :
    (48 <= n)%nat ->
    sie_cap_gpr m n false p0 -∗ kernel_text -∗ kernel_data -∗ panic_wp -∗
    pc_is (mword_of_int (KernelSyms.main + 0x20) : mword 64) -∗
    cpu_own 0 false p0 cpu_ctx_free false -∗
    printk_env γpr γd γv -∗
    ( ∀ m' : regfile,
        sie_cap_gpr m' n false p0 -∗
        pc_is (mword_of_int (KernelSyms.main + 0x32) : mword 64) -∗
        cpu_own 0 false p0 cpu_ctx_free false -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn.
    iIntros "Hcg #Htext #Hkdata #Hpanic Hpc Hcpu #Hpenv Hcont".
    iPoseProof (mni_20 with "Htext") as "Hi20".
    iPoseProof (mni_24 with "Htext") as "Hi24".
    iPoseProof (mni_26 with "Htext") as "Hi26".
    iPoseProof (mni_2a with "Htext") as "Hi2a".
    iPoseProof (mni_2e with "Htext") as "Hi2e".
    iPoseProof (kernel_data_string ms_hart_addr ms_hart
                  (mword_of_int ms_hart_addr) eq_refl
                  ltac:(unfold text_end, ms_hart_addr; lia) ms_hart_bytes
                  with "Hkdata") as "#Hfmt".
    pose proof ms_hart_fmt as (Hkh & Hnh & Hlh).
    (* ---- +0x20 jal cpuid ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x20)) (mword_of_int 1 : mword 5)
              (mword_of_int 2646 : mword 21) m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi20").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (P1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x20) : mword 64) 4)]> m).
    assert (Htgtcp : add_vec (mword_of_int (KernelSyms.main + 0x20) : mword 64)
              (sign_extend' 64 (mword_of_int 2646 : mword 21))
              = (mword_of_int KernelSyms.cpuid : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtcp) in "Hpc".
    iApply (Cpuid.wp_cpuid_sconf P1 n p0 ltac:(lia) with "Hcg Htext Hpc").
    iIntros (m1) "Hcg Hpc %Hcp".
    destruct Hcp as (Hcpcs & Hcpa0).
    assert (Hretcp : ret_pc (P1 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x24) : mword 64)).
    { rewrite /P1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretcp) in "Hpc".
    (* ---- +0x24 c.mv a1,a0 : the vararg is this hart's id ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.main + 0x24)) (mword_of_int 11 : mword 5)
              (mword_of_int 10 : mword 5) m1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (P2 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec zero_reg (rget m1 (mword_of_int 10 : mword 5)))]> m1).
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.main + 0x24) : mword 64) 2
                   = mword_of_int (KernelSyms.main + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* ---- +0x26 / +0x2a : a0 := &"hart %d starting\n" ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.main + 0x26)) (mword_of_int 10 : mword 5)
              (mword_of_int 6 : mword 20) P2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (P3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.main + 0x26) : mword 64)
           (auipc_off (mword_of_int 6 : mword 20)))]> P2).
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.main + 0x26) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.main + 0x2a)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 578 : mword 12) P3 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (P4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (rget P3 (mword_of_int 10 : mword 5))
           (sign_extend' 64 (mword_of_int 578 : mword 12)))]> P3).
    assert (HP4a0 : P4 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int ms_hart_addr : mword 64)).
    { rewrite /P4 upd_eq. rgne. rewrite /P3 upd_eq /ms_hart_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.main + 0x2a) : mword 64) 4
                   = mword_of_int (KernelSyms.main + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    (* ---- +0x2e jal printk ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x2e)) (mword_of_int 1 : mword 5)
              (mword_of_int 2094756 : mword 21) P4 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi2e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (P5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x2e) : mword 64) 4)]> P4).
    assert (Htgtpk : add_vec (mword_of_int (KernelSyms.main + 0x2e) : mword 64)
              (sign_extend' 64 (mword_of_int 2094756 : mword 21))
              = (mword_of_int KernelSyms.printk : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpk) in "Hpc".
    assert (HP5a0 : P5 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int ms_hart_addr : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4a0 | reg_neq]).
    iApply (PrintkGen.wp_printk_gen_sconf γpr γd γv P5 n false p0 cpu_ctx_free
              ms_hart [PkANum] false ltac:(lia) Hlh Hnh ltac:(rewrite Hkh; reflexivity)
              ltac:(cbn [length]; lia)
              with "Hcg Htext Hkdata Hpc Hpanic Hcpu Hpenv [] []").
    { rewrite HP5a0. iExact "Hfmt". }
    { simpl. iSplit; done. }
    iApply wp_next_off_intro.
    iIntros (mf) "Hcg Hpc %Hcs Hcpu _ _".
    destruct Hcs as (Hcs & _).
    assert (Hretpk : ret_pc (P5 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x32) : mword 64)).
    { rewrite /P5 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretpk) in "Hpc".
    iApply ("Hcont" $! mf with "Hcg Hpc Hcpu").
  Qed.

  (* =================================================================== *)
  (* 0x32 .. 0x3a then the join at 0x3e -- kvminithart(); trapinithart(); *)
  (* plicinithart(), the [intr_inv_alloc_off] assembly over kernelvec,    *)
  (* and [jal scheduler], which never returns.                            *)
  (* =================================================================== *)
  Local Lemma ms_inithart_sched 
      (γd : uart_names) (γv : disk_names) (γs : list gname) (γk : gname)
      (pd pav pu : mword 64)
      (m : regfile) (n : nat) (p0 : mword 64)
      (root : mword 44) (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) :
    (* the scheduler this block tail-calls enables interrupts at its loop head
       and must fund [kv_frame_slots] there; see [SpecScheduler]. *)
    (kv_frame_slots + 20 <= n)%nat ->
    (bv_unsigned cid_word < Z.of_nat dev_ncpu)%Z ->
    (* NOT hart 0, which is what makes [tick_keeper]'s cheap arm available:
       [tick_hart] is [cpuid() == 0] and a secondary never keeps time. *)
    cid_word <> (zero_reg : mword 64) ->
    p0 = zero_reg ->
    sie_cap_gpr m n false p0 -∗ kernel_text -∗ panic_wp_any -∗
    pc_is (mword_of_int (KernelSyms.main + 0x32) : mword 64) -∗
    cpu_own 0 false p0 cpu_ctx_free false -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    strans_bit strans_bit_bare -∗ tlb ↦ᵣ tlbvec0 -∗ trap_csrs_raw -∗
    kpt_inv root -∗
    (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈□
      (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) -∗
    dev_inv γd γv -∗
    procs_inv γs -∗
    (* THE LAST THREE [devintr_caps] MEMBERS, out of the [started] deposit: the
       handler contract this block folds into [intr_res] closes over the whole
       credential, and the console's two lock credentials, the disk lock and
       the geometry are the pieces that are not this hart's to make.
       Persistent, so they simply ride in. *)
    console_caps γd -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γv pd pav pu) -∗
    disk_geom γv pd pav pu -∗
    (* this hart's timer capability, allocated in the boot chain *)
    timer_cap -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hdc Hcidne Hp0.
    iIntros "Hcg #Htext #Hpanic Hpc Hcpu Hq Hsbit Htlb Htcsr #Hkinv #Hkptp #Hdev #Hpinv #Hccaps #Hdlock #Hgeom #Htimc".
    iPoseProof (mni_32 with "Htext") as "Hi32".
    iPoseProof (mni_36 with "Htext") as "Hi36".
    iPoseProof (mni_3a with "Htext") as "Hi3a".
    iPoseProof (mni_3e with "Htext") as "Hi3e".
    (* ---- +0x32 jal kvminithart ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x32)) (mword_of_int 1 : mword 5)
              (mword_of_int 130 : mword 21) m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi32").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (Q1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x32) : mword 64) 4)]> m).
    assert (Htgtkh : add_vec (mword_of_int (KernelSyms.main + 0x32) : mword 64)
              (sign_extend' 64 (mword_of_int 130 : mword 21))
              = (mword_of_int KernelSyms.kvminithart : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtkh) in "Hpc".
    iApply (Kvminithart.wp_kvminithart_sconf Q1 0%nat n root tlbvec0 p0
              eq_refl ltac:(lia)
              with "Hcg Hsbit Htext Hpc Htlb Hkptp Hkinv").
    (* the KPT receipt is kept, not dropped -- see ProofMain.v's twin. *)
    iIntros (mkh) "Hcg Hpc %Hcskh Hkpt Hstvec".
    assert (Hretkh : ret_pc (Q1 !!! Regidx (mword_of_int 1))
                     = (mword_of_int (KernelSyms.main + 0x36) : mword 64)).
    { rewrite /Q1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretkh) in "Hpc".
    (* ---- +0x36 jal trapinithart ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x36)) (mword_of_int 1 : mword 5)
              (mword_of_int 5588 : mword 21) mkh n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi36").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (Q2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x36) : mword 64) 4)]> mkh).
    assert (Htgtth : add_vec (mword_of_int (KernelSyms.main + 0x36) : mword 64)
              (sign_extend' 64 (mword_of_int 5588 : mword 21))
              = (mword_of_int KernelSyms.trapinithart : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtth) in "Hpc".
    iDestruct "Hstvec" as (tv0) "Hstvec".
    iApply (Trapinithart.wp_trapinithart_sconf Q2 n tv0 p0 ltac:(lia)
              with "Hcg Htext Hpc Hstvec").
    iIntros (mth) "Hcg Hpc %Hcsth Hstvec".
    assert (Hretth : ret_pc (Q2 !!! Regidx (mword_of_int 1))
                     = (mword_of_int (KernelSyms.main + 0x3a) : mword 64)).
    { rewrite /Q2 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretth) in "Hpc".
    (* ---- THIS HART'S installed-handler resource: kernelvec is in stvec, so
           the contract is available and the SIE ghost's spare quarter joins
           the cell to make [intr_res].  Was an [inv_alloc] under an
           [fupd_wp]. ---- *)
    iDestruct (ms_dup_hw with "Hcg") as "(#Hhw & #Hmin & Hcg)".
    (* the handler contract's credentials: all seven in hand, none assumed.
       [timer_cap] rides in from the boot chain, which mints one per hart. *)
    iDestruct (procs_inv_len with "Hpinv") as %Hnproc.
    (* THE TICK KEEPER IS NOT ASSUMED HERE EITHER, and on a secondary it is
       free: [tick_hart] is [cpuid() == 0] and this arm's premise is
       [cid_word <> zero_reg], so the left disjunct closes it and the ghost
       name is irrelevant (reuse the disk lock's). *)
    iAssert (tick_keeper γk γs) as "#Htick".
    { iLeft. iPureIntro. rewrite /tick_hart.
      apply eq_vec_false_iff. exact Hcidne. }
    iAssert (devintr_caps γd γv γk γk γs pd pav pu) as "#Hcaps".
    { rewrite /devintr_caps.
      iFrame "Hdev Hccaps Hgeom Hdlock Htimc Htick Hpinv Hpanic". }
    iPoseProof (Kernelvec.kernelvec_handler_spec γd γv γk γk γs pd pav pu
                  Hnproc with "Hhw Hmin Htext Hcaps") as "#Hkvs".
    iDestruct (intr_res_intro (mword_of_int KernelSyms.kernelvec : mword 64) _
                 kernelvec_tv_direct kernelvec_stvec_base with "Hq Hstvec []")
      as "Hintr".
    { iApply bi.later_intro. iExact "Hkvs". }
    (* ---- +0x3a jal plicinithart ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x3a)) (mword_of_int 1 : mword 5)
              (mword_of_int 18222 : mword 21) mth n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (Q3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x3a) : mword 64) 4)]> mth).
    assert (Htgtph : add_vec (mword_of_int (KernelSyms.main + 0x3a) : mword 64)
              (sign_extend' 64 (mword_of_int 18222 : mword 21))
              = (mword_of_int KernelSyms.plicinithart : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtph) in "Hpc".
    (* plicinithart indexes the PLIC banks by [rget _ tp], which IS this
       hart's id -- no map-side tp fact to thread. *)
    assert (Hdc3 : (bv_unsigned (rget Q3 (mword_of_int 4 : mword 5))
                    < Z.of_nat dev_ncpu)%Z).
    { rewrite (rget_tp Q3). exact Hdc. }
    iApply (Plicinithart.wp_plicinithart_sconf γd γv Q3 n p0 Hdc3 ltac:(lia)
              with "Hcg Htext Hpc Hdev").
    iIntros (mph) "Hcg Hpc %Hcsph".
    destruct Hcsph as (Hcsph & _).
    assert (Hretph : ret_pc (Q3 !!! Regidx (mword_of_int 1 : mword 5))
                     = (mword_of_int (KernelSyms.main + 0x3e) : mword 64)).
    { rewrite /Q3 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretph) in "Hpc".
    (* ---- +0x3e jal scheduler : main's exit; scheduler never returns ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.main + 0x3e)) (mword_of_int 1 : mword 5)
              (mword_of_int 3818 : mword 21) mph n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    pose (Q4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.main + 0x3e) : mword 64) 4)]> mph).
    assert (Htgtsc : add_vec (mword_of_int (KernelSyms.main + 0x3e) : mword 64)
              (sign_extend' 64 (mword_of_int 3818 : mword 21))
              = (mword_of_int KernelSyms.scheduler : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtsc) in "Hpc".
    (* fold the boot cells and the handler resource built at +0x36 into the
       [trap_csrs] the scheduler consumes. *)
    iApply (Scheduler.wp_scheduler_sconf γs Q4 n p0 Hp0 ltac:(lia)
              with "Hcg Hcpu Htext Hpc Hpinv Hpanic [Htcsr Hintr Hkpt]").
    iApply (trap_csrs_of_raw with "Htcsr Hintr Hkpt").
  Qed.

  (* =================================================================== *)
  (* THE CONTRACT.                                                        *)
  (* =================================================================== *)
  Lemma wp_main_secondary_sconf 
      (m : regfile) (K : nat) (p0 : mword 64)
      (γd : uart_names) (γv : disk_names)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
    : wp_main_secondary_sconf_body m K p0 γd γv tlbvec0.
  (* [kallocG]/[fileG] are in [MAIN_SECONDARY]'s signature but this arm's proof
     never touches them, so the section would not generalize over them. *)
  Proof using All.
    cbv beta delta [wp_main_secondary_sconf_body].
    intros pcE Hcid Hdc HK Hp0.
    pose proof (ms_bounds K HK) as (Hc2 & Hn38 & Hn20).
    iIntros "Hcg Hcpu Hq #Htext #Hkdata Hpc #Hpany #Hsinv #Htimc Hhart".
    (* printk wants the ambient form; the scheduler join wants the generic one
       (its acquire does), so keep both. *)
    iPoseProof (panic_wp_any_at cpu_id with "Hpany") as "#Hpanic".
    iDestruct "Hhart" as "(Hsbit & Htlb & Htcsr)".
    iApply (ms_entry m K p0 Hcid HK with "Hcg Htext Hpc").
    iIntros (m1) "Hcg Hpc %Ha4".
    iApply (ms_spin γd γv m1 (K - 2)%nat p0 Ha4 with "Hcg Htext Hpc Hsinv").
    iIntros (m2) "Hcg Hpc #Hdep".
    iDestruct "Hdep" as (γpr γk γs pd pav pu root pas)
      "(#Hpenv & #Hpinv & #Hccaps & #Hdlock & #Hgeom & #Hkinv & #Hkptp & #Htramp & #Hkstx)".
    iPoseProof "Hpenv" as "Hpenv2".
    iDestruct "Hpenv2" as "(_ & _ & #Hdev & _ & _)".
    iApply (ms_printk γpr γd γv m2 (K - 2)%nat p0 Hn38
              with "Hcg Htext Hkdata Hpanic Hpc Hcpu Hpenv").
    iIntros (m3) "Hcg Hpc Hcpu".
    iApply (ms_inithart_sched γd γv γs γk pd pav pu m3 (K - 2)%nat p0 root tlbvec0
              Hn20 Hdc Hcid Hp0
              with "Hcg Htext Hpany Hpc Hcpu Hq Hsbit Htlb Htcsr Hkinv Hkptp Hdev Hpinv
                    Hccaps Hdlock Hgeom Htimc").
  Qed.

End ProofMainSecondary.
End MainSecondaryProof.
