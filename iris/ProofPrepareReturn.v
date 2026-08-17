(* ProofPrepareReturn.v -- the whole-function WP for xv6's prepare_return().

     void prepare_return(void) {
       struct proc *p = myproc();
       intr_off();
       w_stvec(TRAMPOLINE + (uservec - trampoline));
       p->trapframe->kernel_satp   = r_satp();
       p->trapframe->kernel_sp     = p->kstack + PGSIZE;
       p->trapframe->kernel_trap   = (uint64)usertrap;
       p->trapframe->kernel_hartid = r_tp();
       unsigned long x = r_sstatus();
       x &= ~SSTATUS_SPP;
       x |=  SSTATUS_SPIE;
       w_sstatus(x);
       w_sepc(p->trapframe->epc);
     }

   Forty-two instructions, a 16-byte frame, one call.  The contract is
   SpecPrepareReturn.v and the pure obligations are ProofPrepareReturnParts.v.

   THE ONE STRUCTURAL IDEA: THE FUNCTION CHANGES INDEX AT +0x0c, AND
   EVERYTHING IT NEEDS COMES OUT OF THAT FLIP.  The prologue and the call run
   at [b = true], so each step rebinds the hart; from the [csrci] onward the
   index is [false] and every step is [wp_next_off_intro].  The flip is also
   the function's supply line:

     - [trap_csrs] -- the four trap-scratch cells, [intr_res] (which owns the
       stvec cell), and the KPT receipt.  The [csrw stvec] at +0x2c is legal
       only because of the first; the [csrr satp] at +0x32 only because of
       the last.  Neither cell is a premise of this contract.
     - [cpu_priv_pay true p] + [intr_count 0 false] -- which, with the [C]
       the entry [cpu_own] carried, REASSEMBLE [cpu_own 0 false p C false].
       That is the whole per-cpu bundle and it is why the post names it once.
     - the reserve [trap_res true] moving from the arm into usable stack.

   TWO THINGS WORTH KNOWING BEFORE READING THE WALK.

   * THE ADDI IMMEDIATES AT +0x1c AND +0x24 ARE NEGATIVE.  0xB98 and 0xB90
     have bit 11 set, so they sign-extend to -1128 and -1136; both AUIPC/ADDI
     pairs land on 0x80006000 and the [c.sub] at +0x28 yields ZERO.  Read as
     positive they give an address 0x1000 too high and a confusing failure.

   * THE [c.mv a4,tp] AT +0x50 IS LEGAL ONLY BECAUSE THE FLIP ALREADY
     HAPPENED.  [src_ok b rs] forbids a tp read at [b = true] -- the value is
     the hart id and a migration would invalidate it -- so this instruction
     could not be proved before +0x0c.  gcc's ordering happens to be the only
     one that works. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import PageGeom.
Require Import RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpGprCsrwCommon.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfCsr.
Require Import IntrDefs.
Require Import HartTp WpNext CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import UserPtTree ProcPtOwn.
Require Import KptTree.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import CodePrepareReturn.
Require Import SpecMyproc.
Require Import SpecPrepareReturn.
Require Import WpIntrOff.
Require Import ProofPrepareReturnParts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* the push_off depth myproc's contract bounds; [lia] cannot evaluate the
   power, so it is [vm_compute]d once here rather than inline (the
   inline-[ltac:] trap, optimization.md). *)
Lemma prr_n0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.

Module PrepareReturnProof (Myproc : MYPROC) : PREPARE_RETURN.

Section ProofPrepareReturn.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

  (* the page's own length invariant, read off without consuming it *)
  Local Lemma prr_tf_len (tfp : mword 44) (ws : list (mword 64)) :
    tf_page tfp ws -∗ ⌜length ws = TFWORDS⌝.
  Proof. rewrite /tf_page. iIntros "(%Hlen & _ & _)". done. Qed.

  (* the trapframe page's own [page_valid], read off [proc_priv] without
     consuming it -- [proc_pt_wf]'s last conjunct, the same projection
     [ProofKforkParts.proc_priv_tfp_valid] takes.  A PURE-goal [iDestruct]
     does not spend the resource, so [Hpv] is still whole for
     [proc_priv_tf_upd] right afterward. *)
  Local Lemma prr_tfp_valid (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜page_valid (page_base (ud_tfp (pv_upt V)))⌝.
  Proof.
    iIntros "[(_ & _ & _ & _ & Hpt & _) _]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(_ & _ & Hptt)".
    iDestruct (proc_pt_wf_get with "Hptt") as "%Hwf".
    iPureIntro. exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
  Qed.

  (* [pt_node_claim tfp] is built INLINE at its one call site below, not as a
     standalone lemma: [sie_cap_gpr]/[hw_config] are HART-INDEXED (every
     [↦ᵣ] inside [hw_config] is per-hart), so a fresh lemma stated against
     this section's own [CID] would pin the WRONG hart once the WP walk has
     rebound it via intervening [wp_next] steps -- see durable-notes.md's
     "hart trap" (the [iSpecialize: cannot instantiate] failure whose two
     sides print identically).  Built from resources already threaded
     through the walk at that point: [hw_config] peels off [Hcg]
     persistently (no loss -- [IntrDefs.sie_cap_gpr_dup_hw_config]), and
     [page_valid (page_base tfp)] is [prr_tfp_valid] above.  The mem-tier
     convenience wrappers ([ProcInv.tf_page_word_mem]/[_upd_mem]) are what
     prepare_return's four kernel-word writes and one epc read actually need
     (their addresses are VA-tier loads/stores through the kernel identity
     map), per [ProcInv.v]'s header on [tf_page_word_mem]. *)

  Lemma wp_prepare_return_sconf (γf : gname) (ks : mword 64) (pid : mword 32)
      (V : pprivate) (m : regfile) (av : nat) (p : mword 64)
      (epc : mword 64) (b : bool) (lks : gset string)
    : wp_prepare_return_sconf_body kt γf ks pid V m av p epc b lks.
  Proof.
    cbv beta delta [wp_prepare_return_sconf_body].
    intros pcE ret_tgt Hav Hepc.
    
    set (ra_idx := (mword_of_int 1  : mword 5)).
    set (s0_idx := (mword_of_int 8  : mword 5)).
    set (tp_idx := (mword_of_int 4  : mword 5)).
    set (a0_idx := (mword_of_int 10 : mword 5)).
    set (a3_idx := (mword_of_int 13 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx ra_idx).
    set (s00 := m !!! Regidx s0_idx).
    iIntros "Hcg Hcpu Hext #Htext Hpc #Hks Hpv Hcont".
    iPoseProof (prr_00 with "Htext") as "Hi00".
    iPoseProof (prr_02 with "Htext") as "Hi02".
    iPoseProof (prr_04 with "Htext") as "Hi04".
    iPoseProof (prr_06 with "Htext") as "Hi06".
    iPoseProof (prr_08 with "Htext") as "Hi08".
    iPoseProof (prr_0c with "Htext") as "Hi0c".
    iPoseProof (prr_10 with "Htext") as "Hi10".
    iPoseProof (prr_14 with "Htext") as "Hi14".
    iPoseProof (prr_16 with "Htext") as "Hi16".
    iPoseProof (prr_18 with "Htext") as "Hi18".
    iPoseProof (prr_1c with "Htext") as "Hi1c".
    iPoseProof (prr_20 with "Htext") as "Hi20".
    iPoseProof (prr_24 with "Htext") as "Hi24".
    iPoseProof (prr_28 with "Htext") as "Hi28".
    iPoseProof (prr_2a with "Htext") as "Hi2a".
    iPoseProof (prr_2c with "Htext") as "Hi2c".
    iPoseProof (prr_30 with "Htext") as "Hi30".
    iPoseProof (prr_32 with "Htext") as "Hi32".
    iPoseProof (prr_36 with "Htext") as "Hi36".
    iPoseProof (prr_38 with "Htext") as "Hi38".
    iPoseProof (prr_3a with "Htext") as "Hi3a".
    iPoseProof (prr_3c with "Htext") as "Hi3c".
    iPoseProof (prr_3e with "Htext") as "Hi3e".
    iPoseProof (prr_40 with "Htext") as "Hi40".
    iPoseProof (prr_42 with "Htext") as "Hi42".
    iPoseProof (prr_44 with "Htext") as "Hi44".
    iPoseProof (prr_48 with "Htext") as "Hi48".
    iPoseProof (prr_4c with "Htext") as "Hi4c".
    iPoseProof (prr_4e with "Htext") as "Hi4e".
    iPoseProof (prr_50 with "Htext") as "Hi50".
    iPoseProof (prr_52 with "Htext") as "Hi52".
    iPoseProof (prr_54 with "Htext") as "Hi54".
    iPoseProof (prr_58 with "Htext") as "Hi58".
    iPoseProof (prr_5c with "Htext") as "Hi5c".
    iPoseProof (prr_60 with "Htext") as "Hi60".
    iPoseProof (prr_64 with "Htext") as "Hi64".
    iPoseProof (prr_66 with "Htext") as "Hi66".
    iPoseProof (prr_68 with "Htext") as "Hi68".
    iPoseProof (prr_6c with "Htext") as "Hi6c".
    iPoseProof (prr_6e with "Htext") as "Hi6e".
    iPoseProof (prr_70 with "Htext") as "Hi70".
    iPoseProof (prr_72 with "Htext") as "Hi72".
    (* =============================================================== *)
    (*  +0x00 .. +0x06: the 16-byte frame, at [b = true].               *)
    (* =============================================================== *)
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hpush : add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                    = pa_stk sp0 2)
      by (apply (stk_push sp0 _ 2); pcw).
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m av 2 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (m !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with M1.
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PRR + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /M1 upd_eq; exact Hpush).
    iDestruct (stack_own_2_elim with "Hframe") as (vra vs0) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (PRR + 0x02)) (mword_of_int 1 : mword 6)
              ra_idx M1 (av - 2)%nat vra b with "Hcg Hpc Hi02 Hbra").
    iIntros (CID2 Hk2) "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (PRR + 0x02) : mword 64) 2
                    = mword_of_int (PRR + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (PRR + 0x04)) (mword_of_int 0 : mword 6)
              s0_idx M1 (av - 2)%nat vs0 b with "Hcg Hpc Hi04 Hbs0").
    iIntros (CID3 Hk3) "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (PRR + 0x04) : mword 64) 2
                    = mword_of_int (PRR + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (PRR + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 4 : mword 8) s0_idx M1 (av - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hk4) "Hcg Hpc".
    set (M2 := <[Regidx s0_idx := regval_into_reg
                   (add_vec (M1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> M1).
    change (<[Regidx s0_idx := regval_into_reg
               (add_vec (M1 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> M1) with M2.
    assert (Hpp08 : add_vec_int (mword_of_int (PRR + 0x06) : mword 64) 2
                    = mword_of_int (PRR + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    (* =============================================================== *)
    (*  +0x08: jal ra,myproc -- a0 = p.                                 *)
    (* =============================================================== *)
    iApply (wp_jal_s_sconf (mword_of_int (PRR + 0x08)) ra_idx
              (mword_of_int 2094204 : mword 21) M2 (av - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hk5) "Hcg Hpc".
    set (M3 := <[Regidx ra_idx := regval_into_reg
                   (add_vec_int (mword_of_int (PRR + 0x08) : mword 64) 4)]> M2).
    change (<[Regidx ra_idx := regval_into_reg
               (add_vec_int (mword_of_int (PRR + 0x08) : mword 64) 4)]> M2) with M3.
    assert (HM3sp : M3 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /M3 upd_ne; [exact HM2sp | reg_neq]).
    assert (HM3ra : M3 !!! Regidx ra_idx = mword_of_int (PRR + 0x0c))
      by (rewrite /M3 upd_eq; pcw).
    assert (Hentry : add_vec (mword_of_int (PRR + 0x08) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094204 : mword 21))
                     = mword_of_int KernelSyms.myproc) by pcw.
    iEval (rewrite Hentry) in "Hpc".
    iDestruct (cpu_own_transport CID CID5 0%nat b p b
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf kt M3 (av - 2)%nat 0%nat b p b lks
              prr_n0 ltac:(lia) with "Hcg Hcpu Htext Hpc").
    iIntros (CID6 Hk6 msq A) "%Hmsq Hcg Hcpu Hpc %HcsA".
    destruct HcsA as [HcsA HAa0].
    assert (Hpc0c : ret_pc (M3 !!! Regidx ra_idx) = mword_of_int (PRR + 0x0c))
      by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc0c) in "Hpc".
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM3sp).
    (* =============================================================== *)
    (*  +0x0c: csrci sstatus,2 -- intr_off().  From here [b = false].   *)
    (* =============================================================== *)
    (* AT EITHER ENTRY INDEX, through the composite leaf: at [b = true] a
       real flip that pays the bundle out of [sie_arm true p], at
       [b = false] a write of a bit that is already clear, with the caller's
       own [trap_csrs_ext false] standing in for the payout.  Its post is
       index-free, so everything below this line is proved ONCE. *)
    iDestruct (trap_csrs_ext_transport CID CID6 b p
                 ltac:(wp_next_chain) with "Hext") as "Hext".
    iApply (wp_intr_off_lvl0_s_sconf (mword_of_int (PRR + 0x0c)) b p A
              (av - 2)%nat with "Hcg Hcpu Hext Hpc Hi0c").
    (* THE BINDER INDEX IS THE ENTRY ONE.  The leaf's continuation is
       [wp_next b p] at the instruction's OWN index, and at [b = true] an
       interrupt can be taken ON this very instruction, so the hart may have
       moved.  Every step AFTER this one is at [false] and introduces with
       [wp_next_off_intro]; this one alone rebinds. *)
    iIntros (CID7 Hk7 ms0) "%Hms0f Hcg Hcpu Hcsrs Hclm Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (PRR + 0x0c) : mword 64) 4
                    = mword_of_int (PRR + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* what the intr_off left in hand: the trap-scratch cells, [intr_res],
       the receipt *)
    iDestruct (trap_csrs_to_raw with "Hcsrs") as "(Hraw & Hintr & Hkptr)".
    iDestruct "Hraw" as "(Hsepc & Hscause & Hstval & Hsret)".
    iDestruct "Hsepc" as (sepc0) "Hsepc".
    iDestruct "Hsret" as (vspp vspie) "Hsret".
    (* [intr_res] is the INSTALLED-HANDLER resource: the vector cell, the SIE
       quarter, and the handler's spec under a later.  The spec is DROPPED
       here and that is the point -- after the [csrw stvec] below this hart
       has no kernel handler installed, so re-claiming it would be false.
       What survives is the cell (to be overwritten) and the quarter, which
       the post hands back dangling: with it loose, [sie_ghost_flip] cannot
       assemble and interrupts cannot come back on before the sret. *)
    rewrite /intr_res.
    iDestruct "Hintr" as (tv0 vb) "(%Htvmode & %Htvbase & Hq4 & Hstvec & _)".
    (* =============================================================== *)
    (*  +0x10 .. +0x2c: the stvec computation and its write.            *)
    (* =============================================================== *)
    (* ---- +0x10: lui a4,0x4000 ---- *)
    iApply (wp_lui_s_sconf (mword_of_int (PRR + 0x10)) a4_idx
              (mword_of_int 16384 : mword 20) (mword_of_int 0x4000000 : mword 64)
              A (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) prr_lui_a4
              with "Hcg Hpc Hi10").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T1 := <[Regidx a4_idx := regval_into_reg (mword_of_int 0x4000000 : mword 64)]> A).
    change (<[Regidx a4_idx := regval_into_reg (mword_of_int 0x4000000 : mword 64)]> A) with T1.
    assert (Hpp14 : add_vec_int (mword_of_int (PRR + 0x10) : mword 64) 4
                    = mword_of_int (PRR + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    assert (HT1a4 : rget T1 a4_idx = (mword_of_int 0x4000000 : mword 64))
      by (rgne; rewrite /T1 upd_eq; reflexivity).
    (* ---- +0x14: c.addi a4,a4,-1 ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (PRR + 0x14)) a4_idx (mword_of_int 63 : mword 6)
              T1 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi14").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HT1a4 prr_addi_a4) in "Hcg".
    set (T2 := <[Regidx a4_idx := regval_into_reg (mword_of_int 0x3FFFFFF : mword 64)]> T1).
    change (<[Regidx a4_idx := regval_into_reg (mword_of_int 0x3FFFFFF : mword 64)]> T1) with T2.
    assert (Hpp16 : add_vec_int (mword_of_int (PRR + 0x14) : mword 64) 2
                    = mword_of_int (PRR + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    assert (HT2a4 : rget T2 a4_idx = (mword_of_int 0x3FFFFFF : mword 64))
      by (rgne; rewrite /T2 upd_eq; reflexivity).
    (* ---- +0x16: c.slli a4,a4,12 ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int (PRR + 0x16)) (Regidx a4_idx) a4_idx
              (mword_of_int 12 : mword 6) T2 (trap_res b + (av - 2))%nat false
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HT2a4 prr_slli_a4) in "Hcg".
    set (T3 := <[Regidx a4_idx := regval_into_reg uservec_tvec]> T2).
    change (<[Regidx a4_idx := regval_into_reg uservec_tvec]> T2) with T3.
    assert (Hpp18 : add_vec_int (mword_of_int (PRR + 0x16) : mword 64) 2
                    = mword_of_int (PRR + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    (* ---- +0x18: auipc a5,0x4 ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PRR + 0x18)) a5_idx (mword_of_int 4 : mword 20)
              T3 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi18").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T4 := <[Regidx a5_idx := regval_into_reg
                   (add_vec (mword_of_int (PRR + 0x18) : mword 64)
                      (auipc_off (mword_of_int 4 : mword 20)))]> T3).
    change (<[Regidx a5_idx := regval_into_reg
               (add_vec (mword_of_int (PRR + 0x18) : mword 64)
                  (auipc_off (mword_of_int 4 : mword 20)))]> T3) with T4.
    assert (Hpp1c : add_vec_int (mword_of_int (PRR + 0x18) : mword 64) 4
                    = mword_of_int (PRR + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: addi a5,a5,-1128 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (PRR + 0x1c)) a5_idx a5_idx
              (mword_of_int 2962 : mword 12) T4 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne; rewrite /T4 upd_eq prr_uservec_addr) in "Hcg".
    set (T5 := <[Regidx a5_idx := regval_into_reg
                   (mword_of_int KernelSyms.uservec : mword 64)]> T4).
    change (<[Regidx a5_idx := regval_into_reg
               (mword_of_int KernelSyms.uservec : mword 64)]> T4) with T5.
    assert (Hpp20 : add_vec_int (mword_of_int (PRR + 0x1c) : mword 64) 4
                    = mword_of_int (PRR + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- +0x20: auipc a3,0x4 ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PRR + 0x20)) a3_idx (mword_of_int 4 : mword 20)
              T5 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi20").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T6 := <[Regidx a3_idx := regval_into_reg
                   (add_vec (mword_of_int (PRR + 0x20) : mword 64)
                      (auipc_off (mword_of_int 4 : mword 20)))]> T5).
    change (<[Regidx a3_idx := regval_into_reg
               (add_vec (mword_of_int (PRR + 0x20) : mword 64)
                  (auipc_off (mword_of_int 4 : mword 20)))]> T5) with T6.
    assert (Hpp24 : add_vec_int (mword_of_int (PRR + 0x20) : mword 64) 4
                    = mword_of_int (PRR + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ---- +0x24: addi a3,a3,-1136 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (PRR + 0x24)) a3_idx a3_idx
              (mword_of_int 2954 : mword 12) T6 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi24").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne; rewrite /T6 upd_eq prr_trampoline_addr) in "Hcg".
    set (T7 := <[Regidx a3_idx := regval_into_reg
                   (mword_of_int KernelSyms.trampoline : mword 64)]> T6).
    change (<[Regidx a3_idx := regval_into_reg
               (mword_of_int KernelSyms.trampoline : mword 64)]> T6) with T7.
    assert (Hpp28 : add_vec_int (mword_of_int (PRR + 0x24) : mword 64) 4
                    = mword_of_int (PRR + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    assert (HT7a5 : rget T7 a5_idx = (mword_of_int KernelSyms.uservec : mword 64)).
    { rgne. rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_eq. reflexivity. }
    assert (HT7a3 : rget T7 a3_idx = (mword_of_int KernelSyms.trampoline : mword 64))
      by (rgne; rewrite /T7 upd_eq; reflexivity).
    assert (HT7a4 : rget T7 a4_idx = uservec_tvec).
    { rgne. rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. reflexivity. }
    (* ---- +0x28: c.sub a5,a5,a3 -- and the difference is ZERO ---- *)
    iApply (wp_csub_wval_s_sconf (mword_of_int (PRR + 0x28)) a5_idx a5_idx a3_idx
              (mword_of_int 0 : mword 64) T7 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HT7a5 HT7a3; exact prr_uservec_off_zero)
              with "Hcg Hpc Hi28").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T8 := <[Regidx a5_idx := regval_into_reg (mword_of_int 0 : mword 64)]> T7).
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 0 : mword 64)]> T7) with T8.
    assert (Hpp2a : add_vec_int (mword_of_int (PRR + 0x28) : mword 64) 2
                    = mword_of_int (PRR + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    assert (HT8a5 : rget T8 a5_idx = (mword_of_int 0 : mword 64))
      by (rgne; rewrite /T8 upd_eq; reflexivity).
    assert (HT8a4 : rget T8 a4_idx = uservec_tvec)
      by (rgne; rewrite /T8 upd_ne; [rewrite -HT7a4; rgne; reflexivity | reg_neq]).
    (* ---- +0x2a: c.add a5,a5,a4 ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (PRR + 0x2a)) a5_idx a4_idx
              T8 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi2a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HT8a5 HT8a4 prr_tvec_val) in "Hcg".
    set (T9 := <[Regidx a5_idx := regval_into_reg uservec_tvec]> T8).
    change (<[Regidx a5_idx := regval_into_reg uservec_tvec]> T8) with T9.
    assert (Hpp2c : add_vec_int (mword_of_int (PRR + 0x2a) : mword 64) 2
                    = mword_of_int (PRR + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    assert (HT9a5 : rget T9 a5_idx = uservec_tvec)
      by (rgne; rewrite /T9 upd_eq; reflexivity).
    (* ---- +0x2c: csrw stvec,a5 ---- *)
    iApply (wp_csrw_stvec_s_sconf (mword_of_int (PRR + 0x2c)) a5_idx
              T9 (trap_res b + (av - 2))%nat tv0 uservec_tvec
              ltac:(vm_compute; discriminate) HT9a5 prr_tvec_mode
              with "Hcg Hstvec Hpc Hi2c").
    iApply wp_next_off_intro. iIntros "Hcg Hstvec Hpc".
    assert (Hpp30 : add_vec_int (mword_of_int (PRR + 0x2c) : mword 64) 4
                    = mword_of_int (PRR + 0x30)) by pcw.
    iEval (rewrite Hpp30) in "Hpc".
    (* =============================================================== *)
    (*  +0x30 .. +0x52: the four KERNEL slots.                          *)
    (* =============================================================== *)
    iDestruct (prr_tfp_valid with "Hpv") as %Hpv_valid.
    iDestruct (proc_priv_tf_upd with "Hpv") as "(Htfc & Htfp & Hclose)".
    iDestruct (prr_tf_len with "Htfp") as %Hlen.
    (* one name for the trapframe page, folded into the three resources the
       accessor just handed out (and thus into every [Un] built below). *)
    set (tfp := ud_tfp (pv_upt V)).
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iPoseProof (pt_node_claim_from_static tfp Hpv_valid with "Hkmapb") as "#Hptc".
    assert (Hi0 : (tf_ksatp_idx < length (pv_tf V))%nat)
      by (rewrite Hlen; unfold TFWORDS, tf_ksatp_idx; lia).
    assert (Hi1 : (tf_ksp_idx < length (pv_tf V))%nat)
      by (rewrite Hlen; unfold TFWORDS, tf_ksp_idx; lia).
    assert (Hi2 : (tf_ktrap_idx < length (pv_tf V))%nat)
      by (rewrite Hlen; unfold TFWORDS, tf_ktrap_idx; lia).
    assert (Hi4 : (tf_khartid_idx < length (pv_tf V))%nat)
      by (rewrite Hlen; unfold TFWORDS, tf_khartid_idx; lia).
    destruct (lookup_lt_is_Some_2 (pv_tf V) tf_ksatp_idx Hi0) as [w0 Hw0].
    (* ---- +0x30: c.ld a5,88(a0) -- a5 = p->trapframe ---- *)
    assert (HT9a0 : rget T9 a0_idx = p).
    { rgne. rewrite /T9 upd_ne; [| reg_neq]. rewrite /T8 upd_ne; [| reg_neq].
      rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact HAa0. }
    iEval (rewrite -(prr_p_trapframe p) -HT9a0) in "Htfc".
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (PRR + 0x30)) a5_idx a0_idx
              (mword_of_int 88 : mword 12) T9 (trap_res b + (av - 2))%nat
              (page_base tfp) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 Htfc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Htfc".
    iEval (rewrite HT9a0 (prr_p_trapframe p)) in "Htfc".
    set (U1 := <[Regidx a5_idx := regval_into_reg (page_base tfp)]> T9).
    change (<[Regidx a5_idx := regval_into_reg (page_base tfp)]> T9) with U1.
    assert (Hpp32 : add_vec_int (mword_of_int (PRR + 0x30) : mword 64) 2
                    = mword_of_int (PRR + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* ---- +0x32: csrr a4,satp -- THE READ THE KPT RECEIPT UNLOCKS.
       The cell is NOT threaded: it lives inside the bundle's own
       [strans_inv], so the leaf takes the receipt and borrows it internally
       ([wp_csrr_satp_kpt_s_sconf]).  The value comes back existentially with
       its three [satp_rooted] facts -- which is exactly what the post owes
       for [kernel_satp]. ---- *)
    iApply (wp_csrr_satp_kpt_s_sconf (mword_of_int (PRR + 0x32)) a4_idx
              U1 (trap_res b + (av - 2))%nat
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hkptr Hpc Hi32").
    iApply wp_next_off_intro.
    iIntros (ksat root) "%Hmode %Hasid %Hppn Hcg Hkptr Hpc".
    set (U2 := <[Regidx a4_idx := regval_into_reg ksat]> U1).
    change (<[Regidx a4_idx := regval_into_reg ksat]> U1) with U2.
    (* +0x32 is a BASE instruction, not compressed: pc advances by 4. *)
    assert (Hpp36 : add_vec_int (mword_of_int (PRR + 0x32) : mword 64) 4
                    = mword_of_int (PRR + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    (* ---- +0x36: c.sd a4,0(a5) -- trapframe->kernel_satp ---- *)
    assert (HU2a5 : rget U2 a5_idx = page_base tfp).
    { rgne. rewrite /U2 upd_ne; [| reg_neq]. rewrite /U1 upd_eq. reflexivity. }
    assert (HU2a4 : rget U2 a4_idx = ksat)
      by (rgne; rewrite /U2 upd_eq; reflexivity).
    assert (HU2a0 : rget U2 a0_idx = p).
    { rgne. rewrite /U2 upd_ne; [| reg_neq]. rewrite /U1 upd_ne; [| reg_neq].
      rewrite -HT9a0. rgne. reflexivity. }
    iDestruct (tf_page_word_upd_mem tfp (pv_tf V) tf_ksatp_idx w0 ltac:(vm_compute; lia) Hw0
                 with "Hptc Htfp")
      as "(Hcell & Hback)".
    iEval (rewrite -(prr_tf_addr_00 tfp) -HU2a5) in "Hcell".
    iApply (wp_csd_s_sconf (mword_of_int (PRR + 0x36)) a4_idx a5_idx
              (mword_of_int 0 : mword 12) U2 (trap_res b + (av - 2))%nat w0 false
              with "Hcg Hpc Hi36 Hcell").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite HU2a4 HU2a5 (prr_tf_addr_00 tfp)) in "Hcell".
    iDestruct ("Hback" $! ksat with "Hcell") as "Htfp".
    assert (Hpp38 : add_vec_int (mword_of_int (PRR + 0x36) : mword 64) 2
                    = mword_of_int (PRR + 0x38)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    (* ---- +0x38: c.ld a4,88(a0) -- a4 = p->trapframe ---- *)
    iEval (rewrite -(prr_p_trapframe p) -HU2a0) in "Htfc".
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (PRR + 0x38)) a4_idx a0_idx
              (mword_of_int 88 : mword 12) U2 (trap_res b + (av - 2))%nat
              (page_base tfp) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38 Htfc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Htfc".
    iEval (rewrite HU2a0 (prr_p_trapframe p)) in "Htfc".
    set (U3 := <[Regidx a4_idx := regval_into_reg (page_base tfp)]> U2).
    change (<[Regidx a4_idx := regval_into_reg (page_base tfp)]> U2) with U3.
    assert (Hpp3a : add_vec_int (mword_of_int (PRR + 0x38) : mword 64) 2
                    = mword_of_int (PRR + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    assert (HU3a0 : rget U3 a0_idx = p)
      by (rgne; rewrite /U3 upd_ne; [rewrite -HU2a0; rgne; reflexivity | reg_neq]).
    (* ---- +0x3a: c.ld a5,64(a0) -- a5 = p->kstack.  [is_kstack] is
       PERSISTENT (the field is write-once, set at procinit), so the load
       borrows a copy and the original stays in the intuitionistic context. ---- *)
    iPoseProof "Hks" as "Hksb".
    iEval (rewrite /is_kstack -(prr_p_kstack p) -HU3a0) in "Hksb".
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (PRR + 0x3a)) a5_idx a0_idx
              (mword_of_int 64 : mword 12) U3 (trap_res b + (av - 2))%nat
              ks false (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a Hksb").
    iApply wp_next_off_intro. iIntros "Hcg Hpc _".
    set (U4 := <[Regidx a5_idx := regval_into_reg ks]> U3).
    change (<[Regidx a5_idx := regval_into_reg ks]> U3) with U4.
    assert (Hpp3c : add_vec_int (mword_of_int (PRR + 0x3a) : mword 64) 2
                    = mword_of_int (PRR + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ---- +0x3c: c.lui a3,0x1 -- PGSIZE ---- *)
    iApply (wp_clui_s_sconf (mword_of_int (PRR + 0x3c)) a3_idx
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              U4 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) prr_lui_pgsize
              with "Hcg Hpc Hi3c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (U5 := <[Regidx a3_idx := regval_into_reg (mword_of_int 4096 : mword 64)]> U4).
    change (<[Regidx a3_idx := regval_into_reg (mword_of_int 4096 : mword 64)]> U4) with U5.
    assert (Hpp3e : add_vec_int (mword_of_int (PRR + 0x3c) : mword 64) 2
                    = mword_of_int (PRR + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HU5a5 : rget U5 a5_idx = ks).
    { rgne. rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_eq. reflexivity. }
    assert (HU5a3 : rget U5 a3_idx = (mword_of_int 4096 : mword 64))
      by (rgne; rewrite /U5 upd_eq; reflexivity).
    (* ---- +0x3e: c.add a5,a5,a3 -- kernel_sp = p->kstack + PGSIZE ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (PRR + 0x3e)) a5_idx a3_idx
              U5 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi3e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HU5a5 HU5a3) in "Hcg".
    set (U6 := <[Regidx a5_idx := regval_into_reg
                   (add_vec ks (mword_of_int 4096))]> U5).
    change (<[Regidx a5_idx := regval_into_reg
               (add_vec ks (mword_of_int 4096))]> U5) with U6.
    assert (Hpp40 : add_vec_int (mword_of_int (PRR + 0x3e) : mword 64) 2
                    = mword_of_int (PRR + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* ---- +0x40: c.sd a5,8(a4) -- trapframe->kernel_sp ---- *)
    assert (HU6a5 : rget U6 a5_idx = add_vec ks (mword_of_int 4096))
      by (rgne; rewrite /U6 upd_eq; reflexivity).
    assert (HU6a4 : rget U6 a4_idx = page_base tfp).
    { rgne. rewrite /U6 upd_ne; [| reg_neq]. rewrite /U5 upd_ne; [| reg_neq].
      rewrite /U4 upd_ne; [| reg_neq]. rewrite /U3 upd_eq. reflexivity. }
    assert (Hlen1 : length (<[tf_ksatp_idx := ksat]> (pv_tf V)) = TFWORDS)
      by (rewrite length_insert; exact Hlen).
    assert (Hj1 : (tf_ksp_idx < length (<[tf_ksatp_idx := ksat]> (pv_tf V)))%nat)
      by (rewrite Hlen1; unfold TFWORDS, tf_ksp_idx; lia).
    destruct (lookup_lt_is_Some_2 _ _ Hj1) as [w1 Hw1].
    iDestruct (tf_page_word_upd_mem tfp _ tf_ksp_idx w1 ltac:(vm_compute; lia) Hw1
                 with "Hptc Htfp") as "(Hcell & Hback)".
    iEval (rewrite -(prr_tf_addr_08 tfp) -HU6a4) in "Hcell".
    iApply (wp_csd_s_sconf (mword_of_int (PRR + 0x40)) a5_idx a4_idx
              (mword_of_int 8 : mword 12) U6 (trap_res b + (av - 2))%nat w1 false
              with "Hcg Hpc Hi40 Hcell").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite HU6a5 HU6a4 (prr_tf_addr_08 tfp)) in "Hcell".
    iDestruct ("Hback" $! (add_vec ks (mword_of_int 4096)) with "Hcell") as "Htfp".
    assert (Hpp42 : add_vec_int (mword_of_int (PRR + 0x40) : mword 64) 2
                    = mword_of_int (PRR + 0x42)) by pcw.
    iEval (rewrite Hpp42) in "Hpc".
    (* ---- +0x42: c.ld a5,88(a0) -- a5 = p->trapframe (again) ---- *)
    assert (HU6a0 : rget U6 a0_idx = p).
    { rgne. rewrite /U6 upd_ne; [| reg_neq]. rewrite /U5 upd_ne; [| reg_neq].
      rewrite /U4 upd_ne; [| reg_neq]. rewrite -HU3a0. rgne. reflexivity. }
    iEval (rewrite -(prr_p_trapframe p) -HU6a0) in "Htfc".
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (PRR + 0x42)) a5_idx a0_idx
              (mword_of_int 88 : mword 12) U6 (trap_res b + (av - 2))%nat
              (page_base tfp) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 Htfc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Htfc".
    iEval (rewrite HU6a0 (prr_p_trapframe p)) in "Htfc".
    set (U7 := <[Regidx a5_idx := regval_into_reg (page_base tfp)]> U6).
    change (<[Regidx a5_idx := regval_into_reg (page_base tfp)]> U6) with U7.
    assert (Hpp44 : add_vec_int (mword_of_int (PRR + 0x42) : mword 64) 2
                    = mword_of_int (PRR + 0x44)) by pcw.
    iEval (rewrite Hpp44) in "Hpc".
    (* ---- +0x44: auipc a4,0x0 ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PRR + 0x44)) a4_idx (mword_of_int 0 : mword 20)
              U7 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi44").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (U8 := <[Regidx a4_idx := regval_into_reg
                   (add_vec (mword_of_int (PRR + 0x44) : mword 64)
                      (auipc_off (mword_of_int 0 : mword 20)))]> U7).
    change (<[Regidx a4_idx := regval_into_reg
               (add_vec (mword_of_int (PRR + 0x44) : mword 64)
                  (auipc_off (mword_of_int 0 : mword 20)))]> U7) with U8.
    assert (Hpp48 : add_vec_int (mword_of_int (PRR + 0x44) : mword 64) 4
                    = mword_of_int (PRR + 0x48)) by pcw.
    iEval (rewrite Hpp48) in "Hpc".
    (* ---- +0x48: addi a4,a4,252 -- and 0x44 + 252 = 0x140 = usertrap ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (PRR + 0x48)) a4_idx a4_idx
              (mword_of_int 252 : mword 12) U8 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi48").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne; rewrite /U8 upd_eq prr_usertrap_addr) in "Hcg".
    set (U9 := <[Regidx a4_idx := regval_into_reg
                   (mword_of_int KernelSyms.usertrap : mword 64)]> U8).
    change (<[Regidx a4_idx := regval_into_reg
               (mword_of_int KernelSyms.usertrap : mword 64)]> U8) with U9.
    assert (Hpp4c : add_vec_int (mword_of_int (PRR + 0x48) : mword 64) 4
                    = mword_of_int (PRR + 0x4c)) by pcw.
    iEval (rewrite Hpp4c) in "Hpc".
    (* ---- +0x4c: c.sd a4,16(a5) -- trapframe->kernel_trap ---- *)
    assert (HU9a4 : rget U9 a4_idx = (mword_of_int KernelSyms.usertrap : mword 64))
      by (rgne; rewrite /U9 upd_eq; reflexivity).
    assert (HU9a5 : rget U9 a5_idx = page_base tfp).
    { rgne. rewrite /U9 upd_ne; [| reg_neq]. rewrite /U8 upd_ne; [| reg_neq].
      rewrite /U7 upd_eq. reflexivity. }
    assert (Hlen2 : length (<[tf_ksp_idx := add_vec ks (mword_of_int 4096)]>
                             (<[tf_ksatp_idx := ksat]> (pv_tf V))) = TFWORDS)
      by (rewrite length_insert; exact Hlen1).
    assert (Hj2 : (tf_ktrap_idx < length
                     (<[tf_ksp_idx := add_vec ks (mword_of_int 4096)]>
                       (<[tf_ksatp_idx := ksat]> (pv_tf V))))%nat)
      by (rewrite Hlen2; unfold TFWORDS, tf_ktrap_idx; lia).
    destruct (lookup_lt_is_Some_2 _ _ Hj2) as [w2 Hw2].
    iDestruct (tf_page_word_upd_mem tfp _ tf_ktrap_idx w2 ltac:(vm_compute; lia) Hw2
                 with "Hptc Htfp") as "(Hcell & Hback)".
    iEval (rewrite -(prr_tf_addr_16 tfp) -HU9a5) in "Hcell".
    iApply (wp_csd_s_sconf (mword_of_int (PRR + 0x4c)) a4_idx a5_idx
              (mword_of_int 16 : mword 12) U9 (trap_res b + (av - 2))%nat w2 false
              with "Hcg Hpc Hi4c Hcell").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite HU9a4 HU9a5 (prr_tf_addr_16 tfp)) in "Hcell".
    iDestruct ("Hback" $! (mword_of_int KernelSyms.usertrap : mword 64) with "Hcell")
      as "Htfp".
    assert (Hpp4e : add_vec_int (mword_of_int (PRR + 0x4c) : mword 64) 2
                    = mword_of_int (PRR + 0x4e)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    (* ---- +0x4e: c.ld a5,88(a0) -- a5 = p->trapframe (third time) ---- *)
    assert (HU9a0 : rget U9 a0_idx = p).
    { rgne. rewrite /U9 upd_ne; [| reg_neq]. rewrite /U8 upd_ne; [| reg_neq].
      rewrite /U7 upd_ne; [| reg_neq]. rewrite -HU6a0. rgne. reflexivity. }
    iEval (rewrite -(prr_p_trapframe p) -HU9a0) in "Htfc".
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (PRR + 0x4e)) a5_idx a0_idx
              (mword_of_int 88 : mword 12) U9 (trap_res b + (av - 2))%nat
              (page_base tfp) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e Htfc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Htfc".
    iEval (rewrite HU9a0 (prr_p_trapframe p)) in "Htfc".
    set (U10 := <[Regidx a5_idx := regval_into_reg (page_base tfp)]> U9).
    change (<[Regidx a5_idx := regval_into_reg (page_base tfp)]> U9) with U10.
    assert (Hpp50 : add_vec_int (mword_of_int (PRR + 0x4e) : mword 64) 2
                    = mword_of_int (PRR + 0x50)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ---- +0x50: c.mv a4,tp -- THE tp READ.  Legal only at [b = false]:
       [src_ok true tp] is false, so this instruction could not have been
       proved anywhere before the +0x0c flip. ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (PRR + 0x50)) a4_idx tp_idx
              U10 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi50").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite /tp_idx rget_tp add_vec_zero_l) in "Hcg".
    set (U11 := <[Regidx a4_idx := regval_into_reg cid_word]> U10).
    change (<[Regidx a4_idx := regval_into_reg (cid_word_of cpu_id)]> U10) with U11.
    assert (Hpp52 : add_vec_int (mword_of_int (PRR + 0x50) : mword 64) 2
                    = mword_of_int (PRR + 0x52)) by pcw.
    iEval (rewrite Hpp52) in "Hpc".
    (* ---- +0x52: c.sd a4,32(a5) -- trapframe->kernel_hartid ---- *)
    assert (HU11a4 : rget U11 a4_idx = cid_word)
      by (rgne; rewrite /U11 upd_eq; reflexivity).
    assert (HU11a5 : rget U11 a5_idx = page_base tfp).
    { rgne. rewrite /U11 upd_ne; [| reg_neq]. rewrite /U10 upd_eq. reflexivity. }
    assert (Hlen3 : length (<[tf_ktrap_idx := (mword_of_int KernelSyms.usertrap : mword 64)]>
                             (<[tf_ksp_idx := add_vec ks (mword_of_int 4096)]>
                               (<[tf_ksatp_idx := ksat]> (pv_tf V)))) = TFWORDS)
      by (rewrite length_insert; exact Hlen2).
    assert (Hj4 : (tf_khartid_idx < length
                     (<[tf_ktrap_idx := (mword_of_int KernelSyms.usertrap : mword 64)]>
                       (<[tf_ksp_idx := add_vec ks (mword_of_int 4096)]>
                         (<[tf_ksatp_idx := ksat]> (pv_tf V)))))%nat)
      by (rewrite Hlen3; unfold TFWORDS, tf_khartid_idx; lia).
    destruct (lookup_lt_is_Some_2 _ _ Hj4) as [w4 Hw4].
    iDestruct (tf_page_word_upd_mem tfp _ tf_khartid_idx w4 ltac:(vm_compute; lia) Hw4
                 with "Hptc Htfp")
      as "(Hcell & Hback)".
    iEval (rewrite -(prr_tf_addr_32 tfp) -HU11a5) in "Hcell".
    iApply (wp_csd_s_sconf (mword_of_int (PRR + 0x52)) a4_idx a5_idx
              (mword_of_int 32 : mword 12) U11 (trap_res b + (av - 2))%nat w4 false
              with "Hcg Hpc Hi52 Hcell").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite HU11a4 HU11a5 (prr_tf_addr_32 tfp)) in "Hcell".
    iDestruct ("Hback" $! cid_word with "Hcell") as "Htfp".
    assert (Hpp54 : add_vec_int (mword_of_int (PRR + 0x52) : mword 64) 2
                    = mword_of_int (PRR + 0x54)) by pcw.
    iEval (rewrite Hpp54) in "Hpc".
    (* =============================================================== *)
    (*  +0x54 .. +0x60: the sstatus read-modify-write.                  *)
    (* =============================================================== *)
    (* THE READ HANDS THE BUNDLE BACK IN PIECES, because it NAMES the mstatus
       it read ([sconf_at ms1] rather than [sconf]) -- which is exactly what
       the three ALU/CSR steps below need, since every premise of the write is
       a fact about a field of THIS [ms1].  Re-folding is four lines and the
       [ms1] stays visible in the context. *)
    iApply (wp_csrr_sstatus_s_sconf (mword_of_int (PRR + 0x54)) a5_idx
              U11 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54").
    iApply wp_next_off_intro.
    iIntros (ms1) "%Hms1f Hhs Hsc Htr Hpc Hfile Harm".
    set (U12 := <[Regidx a5_idx := regval_into_reg (sstatus_read ms1)]> U11).
    change (<[Regidx a5_idx := regval_into_reg (sstatus_read ms1)]> U11) with U12.
    iDestruct "Harm" as "(Hstk & %Hsie1 & Harm & #Hwit)".
    iAssert (sie_cap kt U12 (trap_res b + (av - 2))%nat false p)
      with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Htr Harm Hwit". }
    iDestruct (sconf_at_close with "Hsc") as "Hsc".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    assert (Hsie1' : _get_Mstatus_SIE ms1 = ('b"0" : mword 1))
      by (rewrite Hsie1; reflexivity).
    assert (Hpp58 : add_vec_int (mword_of_int (PRR + 0x54) : mword 64) 4
                    = mword_of_int (PRR + 0x58)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    (* ---- +0x58: andi a5,a5,-1128... no: -257, i.e. ~SSTATUS_SPP ---- *)
    assert (HU12a5 : rget U12 a5_idx = sstatus_read ms1)
      by (rgne; rewrite /U12 upd_eq; reflexivity).
    iApply (wp_andi_s_sconf (mword_of_int (PRR + 0x58)) a5_idx a5_idx
              (mword_of_int 3839 : mword 12)
              (bv_and (sstatus_read ms1) prr_and_mask)
              U12 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HU12a5; exact (prr_andi_step (sstatus_read ms1)))
              with "Hcg Hpc Hi58").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (U13 := <[Regidx a5_idx := regval_into_reg
                   (bv_and (sstatus_read ms1) prr_and_mask)]> U12).
    change (<[Regidx a5_idx := regval_into_reg
               (bv_and (sstatus_read ms1) prr_and_mask)]> U12) with U13.
    assert (Hpp5c : add_vec_int (mword_of_int (PRR + 0x58) : mword 64) 4
                    = mword_of_int (PRR + 0x5c)) by pcw.
    iEval (rewrite Hpp5c) in "Hpc".
    (* ---- +0x5c: ori a5,a5,32 -- SSTATUS_SPIE ---- *)
    assert (HU13a5 : rget U13 a5_idx = bv_and (sstatus_read ms1) prr_and_mask)
      by (rgne; rewrite /U13 upd_eq; reflexivity).
    iApply (wp_ori_s_sconf (mword_of_int (PRR + 0x5c)) a5_idx a5_idx
              (mword_of_int 32 : mword 12) (prr_sst (sstatus_read ms1))
              U13 (trap_res b + (av - 2))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HU13a5; exact (prr_ori_step (sstatus_read ms1)))
              with "Hcg Hpc Hi5c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (U14 := <[Regidx a5_idx := regval_into_reg
                   (prr_sst (sstatus_read ms1))]> U13).
    change (<[Regidx a5_idx := regval_into_reg
               (prr_sst (sstatus_read ms1))]> U13) with U14.
    assert (Hpp60 : add_vec_int (mword_of_int (PRR + 0x5c) : mword 64) 4
                    = mword_of_int (PRR + 0x60)) by pcw.
    iEval (rewrite Hpp60) in "Hpc".
    (* ---- +0x60: csrw sstatus,a5.  THE WRITE TAKES THE WORD ABSTRACTLY and
       asks only about its fields, so the whole-word identity between
       [prr_sst (sstatus_read ms1)] and the mstatus that comes back is never
       needed -- five field lemmas from Parts §2 are the entire obligation. ---- *)
    assert (HU14a5 : rget U14 a5_idx = prr_sst (sstatus_read ms1))
      by (rgne; rewrite /U14 upd_eq; reflexivity).
    assert (HW_sie : _get_Sstatus_SIE (prr_sst (sstatus_read ms1)) = sie_bit false).
    { change (sie_bit false) with ('b"0" : mword 1).
      apply prr_w_sie; assumption. }
    assert (HW_mxr : _get_Sstatus_MXR (prr_sst (sstatus_read ms1)) = ('b"0" : mword 1))
      by (apply prr_w_mxr; assumption).
    assert (HW_fs : _get_Sstatus_FS (prr_sst (sstatus_read ms1)) = extStatus_map_forwards Off)
      by (apply prr_w_fs; assumption).
    assert (HW_vs : _get_Sstatus_VS (prr_sst (sstatus_read ms1)) = extStatus_map_forwards Off)
      by (apply prr_w_vs; assumption).
    assert (HW_xs : _get_Sstatus_XS (prr_sst (sstatus_read ms1)) = extStatus_map_forwards Off)
      by (apply prr_w_xs; assumption).
    iApply (wp_csrw_sstatus_val_s_sconf (mword_of_int (PRR + 0x60)) a5_idx
              U14 (trap_res b + (av - 2))%nat (prr_sst (sstatus_read ms1)) vspp vspie
              ltac:(vm_compute; discriminate) HU14a5
              HW_sie HW_mxr HW_fs HW_vs HW_xs
              with "Hcg Hsret Hpc Hi60").
    iApply wp_next_off_intro.
    iIntros (msf) "%Hf_sie %Hf_spp %Hf_spie Hcgat Hsret Hpc".
    iDestruct (sie_cap_gpr_at_close with "Hcgat") as "Hcg".
    (* SPP := 0, SPIE := 1 -- the two bits the whole function exists to move. *)
    assert (Hspp : _get_Mstatus_SPP msf = ('b"0" : mword 1))
      by (rewrite Hf_spp; apply prr_sst_spp).
    assert (Hspie : _get_Mstatus_SPIE msf = ('b"1" : mword 1))
      by (rewrite Hf_spie; apply prr_sst_spie).
    iEval (rewrite Hspp Hspie) in "Hsret".
    assert (Hpp64 : add_vec_int (mword_of_int (PRR + 0x60) : mword 64) 4
                    = mword_of_int (PRR + 0x64)) by pcw.
    iEval (rewrite Hpp64) in "Hpc".
    (* =============================================================== *)
    (*  +0x64 .. +0x68: sepc := p->trapframe->epc.                      *)
    (* =============================================================== *)
    assert (HU14a0 : rget U14 a0_idx = p).
    { rgne. rewrite /U14 upd_ne; [| reg_neq]. rewrite /U13 upd_ne; [| reg_neq].
      rewrite /U12 upd_ne; [| reg_neq]. rewrite /U11 upd_ne; [| reg_neq].
      rewrite /U10 upd_ne; [| reg_neq]. rewrite -HU9a0. rgne. reflexivity. }
    iEval (rewrite -(prr_p_trapframe p) -HU14a0) in "Htfc".
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (PRR + 0x64)) a5_idx a0_idx
              (mword_of_int 88 : mword 12) U14 (trap_res b + (av - 2))%nat
              (page_base tfp) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 Htfc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Htfc".
    iEval (rewrite HU14a0 (prr_p_trapframe p)) in "Htfc".
    set (U15 := <[Regidx a5_idx := regval_into_reg (page_base tfp)]> U14).
    change (<[Regidx a5_idx := regval_into_reg (page_base tfp)]> U14) with U15.
    assert (Hpp66 : add_vec_int (mword_of_int (PRR + 0x64) : mword 64) 2
                    = mword_of_int (PRR + 0x66)) by pcw.
    iEval (rewrite Hpp66) in "Hpc".
    (* ---- +0x66: c.ld a5,24(a5) -- the epc slot, which the four stores above
       left ALONE (they touched 0, 1, 2 and 4), so its word is still the [epc]
       the contract's premise names. ---- *)
    assert (HU15a5 : rget U15 a5_idx = page_base tfp)
      by (rgne; rewrite /U15 upd_eq; reflexivity).
    assert (Hepc4 : (<[tf_khartid_idx := cid_word]>
                      (<[tf_ktrap_idx := (mword_of_int KernelSyms.usertrap : mword 64)]>
                        (<[tf_ksp_idx := add_vec ks (mword_of_int 4096)]>
                          (<[tf_ksatp_idx := ksat]> (pv_tf V)))))
                    !! tf_epc_idx = Some epc).
    { rewrite !list_lookup_insert_ne;
        try (unfold tf_khartid_idx, tf_ktrap_idx, tf_ksp_idx, tf_ksatp_idx,
                    tf_epc_idx; lia).
      exact Hepc. }
    iDestruct (tf_page_word_mem tfp _ tf_epc_idx epc ltac:(vm_compute; lia) Hepc4
                 with "Hptc Htfp") as "(Hcell & Hback)".
    iEval (rewrite -(prr_tf_addr_24 tfp) -HU15a5) in "Hcell".
    iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (PRR + 0x66)) a5_idx a5_idx
              (mword_of_int 24 : mword 12) U15 (trap_res b + (av - 2))%nat
              epc false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 Hcell").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite HU15a5 (prr_tf_addr_24 tfp)) in "Hcell".
    iDestruct ("Hback" with "Hcell") as "Htfp".
    set (U16 := <[Regidx a5_idx := regval_into_reg epc]> U15).
    change (<[Regidx a5_idx := regval_into_reg epc]> U15) with U16.
    assert (Hpp68 : add_vec_int (mword_of_int (PRR + 0x66) : mword 64) 2
                    = mword_of_int (PRR + 0x68)) by pcw.
    iEval (rewrite Hpp68) in "Hpc".
    (* ---- +0x68: csrw sepc,a5 ---- *)
    assert (HU16a5 : rget U16 a5_idx = epc)
      by (rgne; rewrite /U16 upd_eq; reflexivity).
    iApply (wp_csrw_sepc_s_sconf (mword_of_int (PRR + 0x68)) a5_idx
              U16 (trap_res b + (av - 2))%nat sepc0 epc
              ltac:(vm_compute; discriminate) HU16a5
              with "Hcg Hsepc Hpc Hi68").
    iApply wp_next_off_intro. iIntros "Hcg Hsepc Hpc".
    assert (Hpp6c : add_vec_int (mword_of_int (PRR + 0x68) : mword 64) 4
                    = mword_of_int (PRR + 0x6c)) by pcw.
    iEval (rewrite Hpp6c) in "Hpc".
    (* =============================================================== *)
    (*  +0x6c .. +0x72: the epilogue.                                   *)
    (* =============================================================== *)
    assert (HU16sp : U16 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /U16 /U15 /U14 /U13 /U12 /U11 /U10 /U9 /U8 /U7 /U6 /U5 /U4 /U3
              /U2 /U1 /T9 /T8 /T7 /T6 /T5 /T4 /T3 /T2 /T1.
      rewrite !upd_ne; try reg_neq. exact HAsp. }
    assert (Haddr1 : add_vec (M1 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                     = add_vec (U16 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (rewrite HM1sp HU16sp; reflexivity).
    (* THE HART ANNOTATION MATTERS HERE, and only here.  "Hbra" was minted by
       the +0x02 store, back at [b = true], so its stored value is spelled
       [rget] at THAT step's hart -- while everything since +0x0c is at the
       rebound one.  [rget_ne] is hart-generic away from tp, so a
       ∀-quantified restatement rewrites at whichever instance "Hbra" carries;
       a fact stated at the ambient hart would simply fail to match. *)
    assert (Hra0 : forall H : CpuId, rget (CID := H) M1 ra_idx = ra0).
    { intros H. rewrite (rget_ne (CID := H)); [| reg_neq].
      rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite Hra0 Haddr1) in "Hbra".
    (* ---- +0x6c: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PRR + 0x6c)) (mword_of_int 1 : mword 6)
              ra_idx U16 (trap_res b + (av - 2))%nat ra0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c Hbra").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbra".
    set (U17 := <[Regidx ra_idx := regval_into_reg ra0]> U16).
    change (<[Regidx ra_idx := regval_into_reg ra0]> U16) with U17.
    assert (Hpp6e : add_vec_int (mword_of_int (PRR + 0x6c) : mword 64) 2
                    = mword_of_int (PRR + 0x6e)) by pcw.
    iEval (rewrite Hpp6e) in "Hpc".
    assert (HU17sp : U17 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /U17 upd_ne; [exact HU16sp | reg_neq]).
    assert (Haddr0 : add_vec (M1 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                     = add_vec (U17 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))
      by (rewrite HM1sp HU17sp; reflexivity).
    assert (Hs000 : forall H : CpuId, rget (CID := H) M1 s0_idx = s00).
    { intros H. rewrite (rget_ne (CID := H)); [| reg_neq].
      rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite Hs000 Haddr0) in "Hbs0".
    (* ---- +0x6e: c.ldsp s0,0(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PRR + 0x6e)) (mword_of_int 0 : mword 6)
              s0_idx U17 (trap_res b + (av - 2))%nat s00 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e Hbs0").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs0".
    set (U18 := <[Regidx s0_idx := regval_into_reg s00]> U17).
    change (<[Regidx s0_idx := regval_into_reg s00]> U17) with U18.
    assert (Hpp70 : add_vec_int (mword_of_int (PRR + 0x6e) : mword 64) 2
                    = mword_of_int (PRR + 0x70)) by pcw.
    iEval (rewrite Hpp70) in "Hpc".
    (* ---- +0x70: c.addi16sp sp,16 -- the frame traded back ---- *)
    assert (HU18sp : U18 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /U18 upd_ne; [exact HU17sp | reg_neq]).
    assert (Hwv : add_vec (U18 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0)
      by (rewrite HU18sp; apply stk_pop_16).
    assert (Hpop : U18 !!! Regidx csp_rs1
                   = pa_stk (add_vec (U18 !!! Regidx csp_rs1)
                               (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv HU18sp; reflexivity).
    assert (Hpb1 : add_vec (U16 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1) by (rewrite -Haddr1; exact Hpa1).
    assert (Hpb0 : add_vec (U17 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2) by (rewrite -Haddr0; exact Hpa2).
    iEval (rewrite Hpb1) in "Hbra".
    iEval (rewrite Hpb0) in "Hbs0".
    iAssert (stack_own (KTR := kt) sp0 2) with "[Hbra Hbs0]" as "Hframe".
    { iApply (stack_own_2_intro (KTR := kt) with "Hbra Hbs0"). }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (PRR + 0x70)) (mword_of_int 16 : mword 6)
              U18 (trap_res b + (av - 2))%nat 2 false Hpop
              with "Hcg Hpc Hi70 Hframe").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hwv) in "Hcg".
    set (U19 := <[Regidx csp_rs1 := regval_into_reg sp0]> U18).
    change (<[Regidx csp_rs1 := regval_into_reg sp0]> U18) with U19.
    assert (Havn : ((trap_res b + (av - 2)) + 2)%nat = (trap_res b + av)%nat) by lia.
    iEval (rewrite Havn) in "Hcg".
    assert (Hpp72 : add_vec_int (mword_of_int (PRR + 0x70) : mword 64) 2
                    = mword_of_int (PRR + 0x72)) by pcw.
    iEval (rewrite Hpp72) in "Hpc".
    (* ---- +0x72: c.jr ra ---- *)
    assert (HU19ra : rget U19 ra_idx = ra0).
    { rgne. rewrite /U19 upd_ne; [| reg_neq]. rewrite /U18 upd_ne; [| reg_neq].
      rewrite /U17 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (PRR + 0x72)) ra_idx
              U19 (trap_res b + av)%nat false
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi72").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HU19ra) in "Hpc".
    (* =============================================================== *)
    (*  THE POST.                                                       *)
    (* =============================================================== *)
    (* WHAT prepare_return LEFT ALONE.  Everything above A is a write to a3,
       a4, a5 or ra -- all caller-saved -- so the whole tower is transparent
       to [callee_saved]; only sp and s0, which the prologue SAVED and the
       epilogue RESTORED, need their own conjuncts, and myproc's own
       [callee_saved] carries the rest across the call. *)
    assert (HcsA17 : callee_saved A U17).
    { rewrite /U17 /U16 /U15 /U14 /U13 /U12 /U11 /U10 /U9 /U8 /U7 /U6 /U5 /U4
              /U3 /U2 /U1 /T9 /T8 /T7 /T6 /T5 /T4 /T3 /T2 /T1.
      repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]).
      apply callee_saved_refl. }
    assert (Hcsother : forall c : mword 5, is_cs_idx c = true ->
              Regidx c <> Regidx csp_rs1 -> Regidx c <> Regidx s0_idx ->
              Regidx c <> Regidx ra_idx ->
              U19 !!! Regidx c = m !!! Regidx c).
    { intros c Hc Hcsp Hcs0 Hcra.
      rewrite /U19 upd_ne; [| exact Hcsp].
      rewrite /U18 upd_ne; [| exact Hcs0].
      rewrite (callee_saved_lookup HcsA17 c Hc) (callee_saved_lookup HcsA c Hc).
      rewrite /M3 upd_ne; [| exact Hcra].
      rewrite /M2 upd_ne; [| exact Hcs0].
      rewrite /M1 upd_ne; [| exact Hcsp].
      reflexivity. }
    assert (Hcs : callee_saved m U19).
    { unfold callee_saved. repeat apply conj;
        try (apply Hcsother; [vm_compute; reflexivity | reg_neq | reg_neq | reg_neq]).
      - rewrite /U19 upd_eq. reflexivity.
      - rewrite /U19 upd_ne; [| reg_neq]. rewrite /U18 upd_eq. reflexivity. }
    iDestruct ("Hclose" $! (prepare_return_tf (pv_tf V) ksat
                              (add_vec ks (mword_of_int 4096)) cid_word)
                 with "Htfc Htfp") as "Hpv".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! U19 ksat root vb with "[%] [%] [%] [%] Hcg Hcpu Hclm Hsepc
              Hscause Hstval Hsret Hstvec Hq4 Hkptr Hpv Hpc").
    - exact Hcs.
    - exact Hmode.
    - exact Hasid.
    - exact Hppn.
  Qed.

End ProofPrepareReturn.

End PrepareReturnProof.
