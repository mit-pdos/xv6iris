(* ProofSysClose.v -- whole-function WP for sys_close(), the first proof in
   which a [FileInv.file_ref] LEAVES a process's fd table.

     uint64 sys_close(void) {
       int fd; struct file *f;
       if (argfd(0, &fd, &f) < 0) return -1;
       myproc()->ofile[fd] = 0;
       fileclose(f);
       return 0;
     }

   Twenty-four instructions (KernelInstrs @ 0x80004d12; the listing is in
   CodeSysClose.v).  Three things here are new relative to the earlier
   syscall proofs, and they are what the file is about:

   * TWO STACK LOCALS, one of them a 4-byte [int] at the UPPER HALF of a
     frame slot ([&fd] = s0-20).  [InstrBytes.word_pointsto_split4] carves
     slot 3 into its two words for the duration of the argfd call and
     [word_pointsto_join4] puts it back for the epilogue's [c.addi16sp];
     [StackOwn.stack_own_sp_bounds] is what discharges argfd's two "the
     out-parameter is not null" premises -- an owned frame's addresses are
     canonical, so an sp below 8 would put the next slot at ~2^64.

   * AN OFILE INDEX COMPUTED AT RUNTIME.  [slli a5,3 / addi a5,208 / add
     a0,a0,a5] is [p_ofile p fd] for a SYMBOLIC fd; [ProcGeom.ofile_slli3]
     does the shift once over a symbolic [z] rather than casing on the
     sixteen descriptors (the argraw lesson --
     claude-notes/projects/proc-struct-resources.md).

   * A JOIN.  The [blt] failure arm branches to +0x3a, which is also where
     the success arm falls through, so the epilogue is ONE lemma ([sc_tail])
     parameterized by the value the arm left in a5 -- not two copies. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs HartTp WpNext WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import KallocInv.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecMyproc SpecArgfd SpecIput SpecFileclose.
Require Import IrefSlots InodeRegion.
Require Import SpecSysClose.
Require Import CodeSysClose.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.
Local Open Scope Z_scope.

(* a failing tactic in a whole-function WP over [proc_priv] otherwise spends
   tens of minutes formatting the goal (durable-notes) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure arithmetic: the frame, the two local addresses, the ofile index. *)
(* ===================================================================== *)


(* ...and [c.addi4spn s0,sp,32] takes it straight back: s0 IS the entry sp *)
Lemma sc_s0_entry (X : mword 64) :
  add_vec (pa_stk X 4) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))) = X.
Proof.
  rewrite <- stk_push_32. apply frame_cancel.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi a2,s0,-32] : &f, the whole of frame slot 4 *)
Lemma sc_addr_f (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)) = pa_stk X 4.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi a1,s0,-20] : &fd, the UPPER WORD of frame slot 3 *)
Lemma sc_addr_fd (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfec : mword 12)) = pa_add (pa_stk X 3) 4.
Proof.
  unfold pa_add, pa_stk. rewrite avi_assoc.
  unfold add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* ...which is also 12 bytes above the frame base, the form the non-null
   argument needs ([StackOwn.stack_off_nonzero] is anchored at sp). *)
Lemma sc_addr_fd_base (X : mword 64) :
  pa_add (pa_stk X 3) 4 = add_vec_int (pa_stk X 4) 12.
Proof.
  unfold pa_add, pa_stk. rewrite !avi_assoc. f_equal; lia.
Qed.

(* [sc_slli3] / [sc_addi208] moved to ProcGeom.v as [ofile_slli3] /
   [ofile_addi208]: argfd indexes [p->ofile[fd]] with the same three
   instructions, so the arithmetic is shared, not sys_close's. *)

Module SysCloseProof (Argfd : ARGFD) (Myproc : MYPROC) (Fileclose : FILECLOSE) : SYSCLOSE.

Section ProofSysClose.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* the frame's sp is sound: read the bound out of the ambient capability's
     own stack carve (the conclusion is pure, so the bundle survives). *)
  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  (* THE CARVE THIS READS IS ARM-DEPENDENT, hence the [0 < k] premise.
     [IntrDefs.sie_cap] owns [trap_res bb + k] slots, and [trap_res false] is
     NOTHING -- so at the interrupts-off arm the ONLY slots underwriting an sp
     bound are the caller's own [k], and a zero-slot carve says nothing about
     sp at all.  (Under the old arm-blind reserve the 78 reserved slots
     covered it at either arm, which is why this used to need no premise.
     The premise is local to this helper: every call site sits inside the
     capstone, whose [<fn>_stack <= av] premise is already unfolded, so it is
     a [lia].) *)
  Lemma sc_sp_bounds `{CID0 : CpuId} (m : regfile) (k : nat)
      (b : bool) (pp : mword 64) :
    (0 < k)%nat ->
    sie_cap_gpr kt m k b pp -∗
    ⌜(8 <= uint (m !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds (KTR := kt) _ (trap_res b + k)%nat with "Hstk").
    destruct b; unfold trap_res; lia.
  Qed.

  (* =================================================================== *)
  (*  The shared tail at +0x3a: [c.mv a0,a5] and the epilogue.            *)
  (* =================================================================== *)
  (* BOTH arms land here -- the failure arm by the [blt], the success arm by
     falling out of [c.li a5,0] -- so it is proved once, over the value [rv]
     the arm left in a5. *)
  (* A DECOMPOSED helper (porting guide): its own fresh `{CID0} binder -- it
     is entered at a MIGRATED hart -- its own [(b : bool)] and [(pp : mword
     64)] (sie_cap_gpr's explicit process pointer), and its continuation
     wrapped in [wp_next].  It does NOT carry [cpu_own]: the epilogue never
     touches it, so the caller transports it afterwards. *)
  Lemma sc_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 : mword 64) (w3 w4 : bv 64) (b : bool) (pp : mword 64) :
    (4 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx (mword_of_int 1 : mword 5) = ra0 ->
    m !!! Regidx (mword_of_int 8 : mword 5) = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    Mt !!! Regidx (mword_of_int 15 : mword 5) = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> (mword_of_int 8 : mword 5) -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr kt Mt (av - 4)%nat b pp -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_close + 0x3a) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    wp_next (CID0 := CID0) b pp (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx (mword_of_int 10 : mword 5) = rv⌝ -∗
        sie_cap_gpr kt mf av b pp -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hmtsp Hmt15 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hcont".
    iPoseProof (sci_3a with "Htext") as "Hi3a".
    iPoseProof (sci_3c with "Htext") as "Hi3c".
    iPoseProof (sci_3e with "Htext") as "Hi3e".
    iPoseProof (sci_40 with "Htext") as "Hi40".
    iPoseProof (sci_42 with "Htext") as "Hi42".
    (* ---- +0x3a: c.mv a0,a5 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_close + 0x3a))
              (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5) Mt (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (T1 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (add_vec zero_reg (rget Mt (mword_of_int 15 : mword 5)))]> Mt).
    change (<[Regidx (mword_of_int 10 : mword 5)
              := regval_into_reg (add_vec zero_reg (rget Mt (mword_of_int 15 : mword 5)))]> Mt) with T1.
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx (mword_of_int 10 : mword 5) = rv).
    { rewrite /T1 upd_eq. rgne. rewrite Hmt15. apply add_vec_zero_l. }
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x3c: c.ldsp ra,24(sp) ---- *)
    assert (Hpa1 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_close + 0x3c))
              (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5) T1 (av - 4)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c Hb1").
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0]> T1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0]> T1) with T2.
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x3e: c.ldsp s0,16(sp) ---- *)
    assert (Hpa2 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_close + 0x3e))
              (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5) T2 (av - 4)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e Hb2").
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T3 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00]> T2).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00]> T2) with T3.
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x40: c.addi16sp sp,32 (frame pop) ---- *)
    assert (Hwv : add_vec (T3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HT3sp. rewrite <- stk_push_32. apply frame_cancel.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpop : T3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HT3sp).
    (* rebundle the four slots *)
    iDestruct (stack_own_4_intro sp0 ra0 s00 w3 w4 with "Hb1 Hb2 Hb3 Hb4") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_close + 0x40))
              (mword_of_int 2 : mword 6) T3 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi40 Hframe").
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    set (T4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T3 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T3).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T3 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T3) with T4.
    (* ---- +0x42: c.ret ---- *)
    assert (HT4ra : T4 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_close + 0x42))
              (mword_of_int 1 : mword 5) T4 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi42").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne; rewrite HT4ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT4sp : T4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T4 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT4s0 : T4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. symmetry; exact Hs00. }
    assert (HT4a0 : T4 !!! Regidx (mword_of_int 10 : mword 5) = rv).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      exact HT1a0. }
    assert (Hthr4 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
              T4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T4 with "[%] Hcg Hpc").
    split; [| exact HT4a0].
    unfold callee_saved.
    split; [exact HT4sp|].
    split; [exact HT4s0|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr4; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE.                                                       *)
  (* =================================================================== *)
  Lemma wp_sys_close_sconf  (γl γf : gname)
      (fn : fclose_names) (on : option nat) (us : gset Z)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string)
    : wp_sys_close_sconf_body kt γl γf fn on us m av n eb p v pid V b lks.
  Proof.
    cbv beta delta [wp_sys_close_sconf_body].
    intros pcE ret_tgt Harg Hn Hav Hbelow.
    
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx (mword_of_int 1 : mword 5)).
    set (s00 := m !!! Regidx (mword_of_int 8 : mword 5)).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    iIntros "Hcg Hcpu Hextc Hextm #Htext #Hdata Hpc #Hftab #Hpe Hpriv Hpenv
              Hfenv Hcont".
    (* [b] AND [eb] ARE DERIVABLY EQUAL HERE, and the derivation is available
       because fileclose's FS bundle carries [⌜n = 0⌝]: sys_close has no
       acquire of its own, so it runs at push_off level 0 throughout, and at
       level 0 [CpuOwn.cpu_own_eb_agree] reads [eb = b] straight off
       [cpu_own].  Do NOT [subst] either name -- [b] is spelled by name in a
       hundred leaf-instruction arguments below, and the failure surfaces far
       away ("The variable b was not found").  [Hb] is used ONLY at the
       [trap_csrs_ext]/[cpu_claim_ext] transports, to turn their [eb]-guard
       into the [b]-guard the per-instruction chain facts are stated over. *)
    iAssert (⌜(n = 0)%nat⌝)%I as %Hn0.
    { iEval (rewrite /fileclose_fs_env /fileclose_fs_env_nopid) in "Hfenv".
      iDestruct "Hfenv" as "[(%Hz & _) _]". iPureIntro. exact Hz. }
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbm.
    assert (Hb : eb = b) by (rewrite -Hbm Hn0; reflexivity).
    clear Hbm.
    iPoseProof (sci_00 with "Htext") as "Hi00".
    iPoseProof (sci_02 with "Htext") as "Hi02".
    iPoseProof (sci_04 with "Htext") as "Hi04".
    iPoseProof (sci_06 with "Htext") as "Hi06".
    iPoseProof (sci_08 with "Htext") as "Hi08".
    iPoseProof (sci_0c with "Htext") as "Hi0c".
    iPoseProof (sci_10 with "Htext") as "Hi10".
    iPoseProof (sci_12 with "Htext") as "Hi12".
    iPoseProof (sci_16 with "Htext") as "Hi16".
    iPoseProof (sci_18 with "Htext") as "Hi18".
    iPoseProof (sci_1c with "Htext") as "Hi1c".
    iPoseProof (sci_20 with "Htext") as "Hi20".
    iPoseProof (sci_24 with "Htext") as "Hi24".
    iPoseProof (sci_26 with "Htext") as "Hi26".
    iPoseProof (sci_2a with "Htext") as "Hi2a".
    iPoseProof (sci_2c with "Htext") as "Hi2c".
    iPoseProof (sci_30 with "Htext") as "Hi30".
    iPoseProof (sci_34 with "Htext") as "Hi34".
    iPoseProof (sci_38 with "Htext") as "Hi38".
    (* ---- +0x00: c.addi sp,-32 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b
              ltac:(lia) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_close + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    (* the four frame slots *)
    iDestruct (stack_own_4_elim with "Hframe") as (v1 v2 w3 w4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    (* ---- +0x02: c.sdsp ra,24(sp) ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_close + 0x02))
              (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5) M1 (av - 4)%nat v1 b
              with "Hcg Hpc Hi02 Hs1").
    iIntros (CID2 Hs2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,16(sp) ---- *)
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_close + 0x04))
              (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5) M1 (av - 4)%nat v2 b
              with "Hcg Hpc Hi04 Hs2").
    iIntros (CID3 Hs3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* name the two saved values.  The stores' post spells the written value
       via [rget] (the leaf is generic over its source register), so the
       bridge is quantified over the hart -- ra/s0 are never tp. *)
    assert (HM1ra : forall CID' : CpuId, rget (CID := CID') M1 (mword_of_int 1 : mword 5) = ra0).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM1s0 : forall CID' : CpuId, rget (CID := CID') M1 (mword_of_int 8 : mword 5) = s00).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite Hpa1 HM1ra) in "Hs1".
    iEval (rewrite Hpa2 HM1s0) in "Hs2".
    (* ---- +0x06: c.addi4spn s0,sp,32 -- s0 := the entry sp ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_close + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with M2.
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (HM2s0 : M2 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /M2 upd_eq HM1sp. apply sc_s0_entry. }
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    (* ---- +0x08: addi a2,s0,-32 -- a2 := &f ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_close + 0x08))
              (mword_of_int 12 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfe0 : mword 12)
              M2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
                  (add_vec (rget M2 (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)))]> M2).
    change (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg
              (add_vec (rget M2 (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)))]> M2) with M3.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x08) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_close + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HM3a2 : M3 !!! Regidx (mword_of_int 12 : mword 5) = pa_stk sp0 4).
    { rewrite /M3 upd_eq. rgne. rewrite HM2s0. apply sc_addr_f. }
    assert (HM3s0 : M3 !!! Regidx (mword_of_int 8 : mword 5) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | reg_neq]).
    (* ---- +0x0c: addi a1,s0,-20 -- a1 := &fd ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_close + 0x0c))
              (mword_of_int 11 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfec : mword 12)
              M3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (M4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
                  (add_vec (rget M3 (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfec : mword 12)))]> M3).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
              (add_vec (rget M3 (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfec : mword 12)))]> M3) with M4.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x0c) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_close + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    assert (HM4a1 : M4 !!! Regidx (mword_of_int 11 : mword 5) = pa_add (pa_stk sp0 3) 4).
    { rewrite /M4 upd_eq. rgne. rewrite HM3s0. apply sc_addr_fd. }
    (* ---- +0x10: c.li a0,0 -- the argument index ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_close + 0x10))
              (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M4 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (M5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> M4).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> M4) with M5.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- +0x12: jal ra,argfd ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_close + 0x12))
              (mword_of_int 1 : mword 5) (mword_of_int 2096404 : mword 21) M5 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (M6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_close + 0x12) : mword 64) 4)]> M5).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_close + 0x12) : mword 64) 4)]> M5) with M6.
    assert (Hjafd : add_vec (mword_of_int (KernelSyms.sys_close + 0x12) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096404 : mword 21)) = mword_of_int KernelSyms.argfd)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjafd) in "Hpc".
    (* the register facts argfd's contract reads *)
    assert (HM6a0 : M6 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat 0)).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate]. rewrite /M5 upd_eq. reflexivity. }
    assert (HM6a1 : M6 !!! Regidx (mword_of_int 11 : mword 5) = pa_add (pa_stk sp0 3) 4).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate]. exact HM4a1. }
    assert (HM6a2 : M6 !!! Regidx (mword_of_int 12 : mword 5) = pa_stk sp0 4).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate]. exact HM3a2. }
    assert (HM6s0 : M6 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate]. exact HM3s0. }
    assert (HM6sp : M6 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_ne; [| vm_compute; discriminate]. exact HM2sp. }
    assert (HM6ra : M6 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.sys_close + 0x12) : mword 64) 4)
      by (rewrite /M6 upd_eq; reflexivity).
    (* the two out-parameters are not null: the frame's own geometry *)
    (* the helper's [0 < k] premise, from the capstone's own stack budget.
       Named rather than [ltac:(lia)]-inline: at that position [k] is still
       an unresolved evar, and [lia] answers "Cannot find witness". *)
    assert (Hkpos : (0 < (av - 4)%nat)%nat) by lia.
    iDestruct (sc_sp_bounds _ _ _ _ Hkpos with "Hcg") as %Hspb.
    rewrite HM6sp in Hspb.
    assert (Hnzf : M6 !!! Regidx (mword_of_int 12 : mword 5) <> (zero_reg : mword 64)).
    { rewrite HM6a2. by apply sp_bounds_nonzero. }
    assert (Hnzfd : M6 !!! Regidx (mword_of_int 11 : mword 5) <> (zero_reg : mword 64)).
    { rewrite HM6a1 sc_addr_fd_base. apply stack_off_nonzero; [exact Hspb | lia]. }
    (* carve the [int fd] cell out of the upper half of frame slot 3 *)
    iDestruct (word_pointsto_aligned_p with "Hs3") as %Hal3.
    iDestruct (word_pointsto_split4 with "Hs3") as "[Hs3lo Hs3hi]".
    iEval (rewrite -HM6a1) in "Hs3hi".
    iEval (rewrite -HM6a2) in "Hs4".
    (* ---- argfd(0, &fd, &f) ---- *)
    iDestruct (cpu_own_transport CID CID8 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argfd.wp_argfd_sconf kt γf M6 (av - 4)%nat n eb p 0%nat v
              pid V (word_hi w3) w4 b lks
              ltac:(unfold NARG; lia) HM6a0 Harg Hnzf Hn
              ltac:(lia)
              with "Hcg Hcpu Htext Hdata Hpc Hpriv [Hs3hi] Hs4").
    { (* sys_close DOES want the descriptor index, so its [pfd] is a real
         stack address -- [ofd_out]'s non-null case *)
      iApply (ofd_out_intro _ _ Hnzfd with "Hs3hi"). }
    iIntros (CID9 Hs9 A) "%HcsA Hcg Hcpu Hpc Hpriv Hpost".
    assert (Hpc16 : ret_pc (M6 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sys_close + 0x16))
      by (rewrite HM6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- +0x16: c.li a5,-1 (the error return, precomputed) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_close + 0x16))
              (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) A (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (A7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> A).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> A) with A7.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x16) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_close + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    assert (HA7a0 : A7 !!! Regidx (mword_of_int 10 : mword 5) = A !!! Regidx (mword_of_int 10 : mword 5))
      by (rewrite /A7 upd_ne; [reflexivity | reg_neq]).
    assert (HA7a5 : A7 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (-1) : mword 64))
      by (rewrite /A7 upd_eq; reflexivity).
    (* callee-saved registers ride through argfd unchanged *)
    assert (HA7sp : A7 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /A7 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)). exact HM6sp. }
    assert (HA7s0 : A7 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /A7 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA (mword_of_int 8) ltac:(vm_compute; reflexivity)). exact HM6s0. }
    (* the residual threading fact both arms hand to [sc_tail] *)
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> (mword_of_int 8 : mword 5) -> A7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> mword_of_int 12)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A7 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /M6 upd_ne; [| congruence].
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- +0x18: blt a0,x0 -- the two arms ---- *)
    rewrite /argfd_post. iDestruct "Hpost" as "[Hfail | Hsucc]".
    - (* ================= FAILURE: argfd returned -1 ================= *)
      iDestruct "Hfail" as "([%Hr %Hnone] & Hfdcell & Hfcell)".
      iDestruct (ofd_out_elim _ _ Hnzfd with "Hfdcell") as "Hfdcell".
      assert (HA7a0' : A7 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (-1) : mword 64))
        by (rewrite HA7a0; exact Hr).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_close + 0x18))
                (mword_of_int 34 : mword 13) (mword_of_int 10 : mword 5) A7 (av - 4)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA7a0'; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi18").
      iNext. iIntros (CID11 Hs11) "Hcg Hpc".
      assert (Hbtgt : add_vec (mword_of_int (KernelSyms.sys_close + 0x18) : mword 64)
                        (sign_extend' 64 (mword_of_int 34 : mword 13))
                      = mword_of_int (KernelSyms.sys_close + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbtgt) in "Hpc".
      (* nothing was written: rejoin the two halves of frame slot 3 *)
      iEval (rewrite HM6a1) in "Hfdcell".
      iEval (rewrite HM6a2) in "Hfcell".
      iDestruct (word_pointsto_join4 _ _ _ _ Hal3 with "Hs3lo Hfdcell") as "Hs3".
      iApply (sc_tail (CID0 := CID11) m A7 av (mword_of_int (-1) : mword 64) sp0 ra0 s00 _ w4 b p
                ltac:(lia) eq_refl eq_refl eq_refl HA7sp HA7a5 HthrA
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hfcell").
      iIntros (CID12 Hs12 mf) "[%Hcsf %Hmfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CID9 CID12 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      (* [Hextc]/[Hextm] never moved: argfd does not mention them, so they
         rode along in the frame at the ENTRY hart.  ONE WIDE HOP from there,
         spanning argfd's own guard fact and every leaf step since. *)
      iDestruct (trap_csrs_ext_transport CID CID12 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CID12 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hextc Hextm Hpc [Hpriv] [Hpenv] [Hfenv]");
        [exact Hcsf| | |].
      { rewrite /sys_close_post. iLeft. iFrame "Hpriv". iPureIntro.
        split; [exact Hmfa0 | exact Hnone]. }
      (* no fileclose ran on this path, so both bundles are as they came in *)
      { by iExists on. }
      { by iExists us. }
    - (* ================= SUCCESS: fd names a live file ================= *)
      iDestruct "Hsucc" as (fd fv) "([%Hr %Hsome] & Hfdcell & Hfcell)".
      iDestruct (ofd_out_elim _ _ Hnzfd with "Hfdcell") as "Hfdcell".
      pose proof (arg_fd_lookup v (pv_ofile V) fd fv Hsome) as (Hfdlt & Hlk & Hfvnz & Hsext).
      assert (HA7a0' : A7 !!! Regidx (mword_of_int 10 : mword 5) = (zero_reg : mword 64))
        by (rewrite HA7a0; exact Hr).
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_close + 0x18))
                (mword_of_int 34 : mword 13) (mword_of_int 10 : mword 5) A7 (av - 4)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA7a0'; vm_compute; reflexivity)
                with "Hcg Hpc Hi18").
      iIntros (CID11 Hs11) "Hcg Hpc".
      assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x18) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_close + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      (* ---- +0x1c: jal ra,myproc ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_close + 0x1c))
                (mword_of_int 1 : mword 5) (mword_of_int 2083628 : mword 21) A7 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1c").
      iIntros (CID12 Hs12) "Hcg Hpc".
      set (B := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                   (add_vec_int (mword_of_int (KernelSyms.sys_close + 0x1c) : mword 64) 4)]> A7).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.sys_close + 0x1c) : mword 64) 4)]> A7) with B.
      assert (Hjmp : add_vec (mword_of_int (KernelSyms.sys_close + 0x1c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2083628 : mword 21)) = mword_of_int KernelSyms.myproc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmp) in "Hpc".
      assert (HBra : B !!! Regidx (mword_of_int 1 : mword 5)
                     = add_vec_int (mword_of_int (KernelSyms.sys_close + 0x1c) : mword 64) 4)
        by (rewrite /B upd_eq; reflexivity).
      iDestruct (cpu_own_transport CID9 CID12 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (Myproc.wp_myproc_sconf kt B (av - 4)%nat n eb p b lks
                Hn ltac:(lia)
                with "Hcg Hcpu Htext Hpc").
      iIntros (CID13 Hs13 ms P) "%Hms Hcg Hcpu Hpc %HcsP".
      destruct HcsP as [HcsP HPa0].
      assert (Hpc20 : ret_pc (B !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.sys_close + 0x20))
        by (rewrite HBra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc20) in "Hpc".
      assert (HPs0 : P !!! Regidx (mword_of_int 8 : mword 5) = sp0).
      { rewrite (callee_saved_lookup HcsP (mword_of_int 8) ltac:(vm_compute; reflexivity)).
        rewrite /B upd_ne; [| vm_compute; discriminate]. exact HA7s0. }
      assert (HPsp : P !!! Regidx csp_rs1 = pa_stk sp0 4).
      { rewrite (callee_saved_lookup HcsP csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /B upd_ne; [| vm_compute; discriminate]. exact HA7sp. }
      (* ---- +0x20: lw a5,-20(s0) -- reload fd.  The load leaf spells its
         address through [rget], so the bridge is quantified over the hart
         (s0 is never tp) and is built BEFORE the [iApply]. ---- *)
      assert (Haddrfd : forall CID' : CpuId,
                add_vec (rget (CID := CID') P (mword_of_int 8 : mword 5))
                        (sign_extend' 64 (mword_of_int 0xfec : mword 12)) = pa_add (pa_stk sp0 3) 4).
      { intros CID'; rgne. rewrite HPs0. apply sc_addr_fd. }
      iEval (rewrite HM6a1) in "Hfdcell".
      iEval (rewrite -(Haddrfd CID13)) in "Hfdcell".
      iApply (wp_lw_s_sconf (CID := CID13) (mword_of_int (KernelSyms.sys_close + 0x20))
                (mword_of_int 15 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfec : mword 12)
                P (av - 4)%nat (trunc32 v) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi20 Hfdcell").
      iIntros (CID14 Hs14) "Hcg Hpc Hfdcell".
      iEval (rewrite (Haddrfd CID13)) in "Hfdcell".
      set (C1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (trunc32 v))]> P).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (trunc32 v))]> P) with C1.
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x20) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_close + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      assert (HC1a5 : C1 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int (Z.of_nat fd))
        by (rewrite /C1 upd_eq; exact Hsext).
      (* ---- +0x24: c.slli a5,a5,3 ---- *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.sys_close + 0x24))
                (Regidx (mword_of_int 15 : mword 5)) (mword_of_int 15 : mword 5) (mword_of_int 3 : mword 6)
                C1 (av - 4)%nat b
                eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24").
      iIntros (CID15 Hs15) "Hcg Hpc".
      set (C2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
                    (shift_bits_left (rget C1 (mword_of_int 15 : mword 5))
                       (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> C1).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
                (shift_bits_left (rget C1 (mword_of_int 15 : mword 5))
                   (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> C1) with C2.
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x24) : mword 64) 2
                      = mword_of_int (KernelSyms.sys_close + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      assert (Hfdb : (Z.of_nat fd < 16)%Z) by (unfold NOFILE in Hfdlt; lia).
      assert (HC2a5 : C2 !!! Regidx (mword_of_int 15 : mword 5)
                      = mword_of_int (Z.of_nat fd * 8)).
      { rewrite /C2 upd_eq. rgne. rewrite HC1a5. apply ofile_slli3; lia. }
      (* ---- +0x26: addi a5,a5,208 ---- *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_close + 0x26))
                (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 208 : mword 12)
                C2 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26").
      iIntros (CID16 Hs16) "Hcg Hpc".
      set (C3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
                    (add_vec (rget C2 (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> C2).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
                (add_vec (rget C2 (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> C2) with C3.
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x26) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_close + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      assert (HC3a5 : C3 !!! Regidx (mword_of_int 15 : mword 5)
                      = mword_of_int (208 + 8 * Z.of_nat fd)).
      { rewrite /C3 upd_eq. rgne. rewrite HC2a5.
        rewrite (ofile_addi208 (Z.of_nat fd * 8) ltac:(lia) ltac:(lia)).
        assert (Harith : (208 + Z.of_nat fd * 8)%Z = (208 + 8 * Z.of_nat fd)%Z) by lia.
        rewrite Harith. reflexivity. }
      assert (HC3a0 : C3 !!! Regidx (mword_of_int 10 : mword 5) = p).
      { rewrite /C3 upd_ne; [| reg_neq].
        rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_ne; [| reg_neq]. exact HPa0. }
      (* ---- +0x2a: c.add a0,a0,a5 -- a0 := &p->ofile[fd] ---- *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sys_close + 0x2a))
                (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5) C3 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a").
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (C4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
                    (add_vec (rget C3 (mword_of_int 10 : mword 5)) (rget C3 (mword_of_int 15 : mword 5)))]> C3).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
                (add_vec (rget C3 (mword_of_int 10 : mword 5)) (rget C3 (mword_of_int 15 : mword 5)))]> C3) with C4.
      assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x2a) : mword 64) 2
                      = mword_of_int (KernelSyms.sys_close + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      assert (HC4a0 : C4 !!! Regidx (mword_of_int 10 : mword 5) = p_ofile p fd).
      { rewrite /C4 upd_eq. rgne. rgne. rewrite HC3a0 HC3a5. reflexivity. }
      (* borrow the descriptor out of [proc_priv] *)
      iDestruct (proc_priv_ofile γf p pid V fd fv Hlk with "Hpriv") as "[Hslot Hback]".
      iDestruct "Hslot" as "[Hcell [[%Hz _] | Href]]"; [by exfalso; apply Hfvnz|].
      iDestruct "Href" as (k q Cf) "[[%Hfv %Hklt] Href]".
      (* ---- +0x2c: sd x0,0(a0) -- p->ofile[fd] = 0 ---- *)
      assert (Haddrof : forall CID' : CpuId,
                add_vec (rget (CID := CID') C4 (mword_of_int 10 : mword 5))
                        (sign_extend' 64 (mword_of_int 0 : mword 12)) = p_ofile p fd).
      { intros CID'; rgne. rewrite HC4a0. apply addv_sext0. }
      iEval (rewrite -(Haddrof CID17)) in "Hcell".
      iApply (wp_sd_zero_s_sconf (CID := CID17) (mword_of_int (KernelSyms.sys_close + 0x2c))
                (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 12) C4 (av - 4)%nat fv b
                with "Hcg Hpc Hi2c Hcell").
      iIntros (CID18 Hs18) "Hcg Hpc Hcell".
      iEval (rewrite (Haddrof CID17)) in "Hcell".
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x2c) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_close + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      (* ---- +0x30: ld a0,-32(s0) -- a0 := f ---- *)
      assert (HC4s0 : C4 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
      { rewrite /C4 upd_ne; [| reg_neq].
        rewrite /C3 upd_ne; [| reg_neq].
        rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_ne; [| reg_neq]. exact HPs0. }
      assert (Haddrf : forall CID' : CpuId,
                add_vec (rget (CID := CID') C4 (mword_of_int 8 : mword 5))
                        (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)) = pa_stk sp0 4).
      { intros CID'; rgne. rewrite HC4s0. apply sc_addr_f. }
      iEval (rewrite HM6a2) in "Hfcell".
      iEval (rewrite -(Haddrf CID18)) in "Hfcell".
      iApply (wp_ld_s_sconf (CID := CID18) (mword_of_int (KernelSyms.sys_close + 0x30))
                (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfe0 : mword 12)
                C4 (av - 4)%nat fv b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi30 Hfcell").
      iIntros (CID19 Hs19) "Hcg Hpc Hfcell".
      iEval (rewrite (Haddrf CID18)) in "Hfcell".
      set (C5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg fv]> C4).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg fv]> C4) with C5.
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x30) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_close + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      (* ---- +0x34: jal ra,fileclose ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_close + 0x34))
                (mword_of_int 1 : mword 5) (mword_of_int 2093836 : mword 21) C5 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi34").
      iIntros (CID20 Hs20) "Hcg Hpc".
      set (D := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                   (add_vec_int (mword_of_int (KernelSyms.sys_close + 0x34) : mword 64) 4)]> C5).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.sys_close + 0x34) : mword 64) 4)]> C5) with D.
      assert (Hjfc : add_vec (mword_of_int (KernelSyms.sys_close + 0x34) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093836 : mword 21)) = mword_of_int KernelSyms.fileclose)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjfc) in "Hpc".
      assert (HDra : D !!! Regidx (mword_of_int 1 : mword 5)
                     = add_vec_int (mword_of_int (KernelSyms.sys_close + 0x34) : mword 64) 4)
        by (rewrite /D upd_eq; reflexivity).
      assert (HDa0 : D !!! Regidx (mword_of_int 10 : mword 5) = fnode k).
      { rewrite /D upd_ne; [| reg_neq].
        rewrite /C5 upd_eq. exact Hfv. }
      iDestruct (cpu_own_transport CID13 CID20 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      (* the complement is fileclose's, and it has not moved since entry --
         neither argfd nor myproc mentions it, so it rode along in the frame
         at the ENTRY hart.  ONE WIDE HOP from there, spanning both calls'
         guard facts and every leaf step. *)
      iDestruct (trap_csrs_ext_transport CID CID20 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CID20 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      (* the descriptor's type is not visible here -- [ofile_slot] quantifies
         the content -- so hand fileclose whichever bundle it asks for and
         keep the other ([fileclose_env_split]). *)
      iDestruct (fileclose_env_frame fn on us n eb p Cf with "Hpenv Hfenv")
        as "[Hfcenv Hfcback]".
      iApply (Fileclose.wp_fileclose_sconf kt γl γf k q Cf fn on us D n eb p (av - 4)%nat b lks
                ltac:(lia) Hn HDa0
                Hbelow
                with "Hcg Hcpu Hextc Hextm Htext Hdata Hpc Hftab Hpe Href Hfcenv").
      all: try lkbelow.
      iIntros (CID21 Hs21 R) "Hcg Hcpu Hextc Hextm Hpc %HcsR Hfdslot Hout".
      iDestruct ("Hfcback" with "Hout") as "[Hpenv Hfenv]".
      assert (Hpc38 : ret_pc (D !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.sys_close + 0x38))
        by (rewrite HDra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc38) in "Hpc".
      (* ---- +0x38: c.li a5,0 (the success return) ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_close + 0x38))
                (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
                (zero_reg : mword 64) R (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi38").
      iIntros (CID22 Hs22) "Hcg Hpc".
      set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (zero_reg : mword 64)]> R).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (zero_reg : mword 64)]> R) with R8.
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.sys_close + 0x38) : mword 64) 2
                      = mword_of_int (KernelSyms.sys_close + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* the descriptor is empty now, and it owns the unit fileclose returned *)
      iDestruct ("Hback" $! (zero_reg : mword 64) with "[Hcell Hfdslot]") as "Hpriv".
      { rewrite /ofile_slot. iFrame "Hcell". iLeft. by iFrame "Hfdslot". }
      (* rejoin frame slot 3 *)
      iDestruct (word_pointsto_join4 _ _ _ _ Hal3 with "Hs3lo Hfdcell") as "Hs3".
      (* the epilogue's register facts *)
      assert (HR8a5 : R8 !!! Regidx (mword_of_int 15 : mword 5) = (zero_reg : mword 64))
        by (rewrite /R8 upd_eq; reflexivity).
      assert (HR8sp : R8 !!! Regidx csp_rs1 = pa_stk sp0 4).
      { rewrite /R8 upd_ne; [| reg_neq].
        rewrite (callee_saved_lookup HcsR csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /D upd_ne; [| reg_neq].
        rewrite /C5 upd_ne; [| reg_neq].
        rewrite /C4 upd_ne; [| reg_neq].
        rewrite /C3 upd_ne; [| reg_neq].
        rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_ne; [| reg_neq]. exact HPsp. }
      assert (HthrR : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> (mword_of_int 8 : mword 5) -> R8 !!! Regidx r = m !!! Regidx r).
      { intros r Hcs Ncsp N8.
        assert (N15 : r <> mword_of_int 15)
          by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
        rewrite /R8 upd_ne; [| congruence].
        rewrite (callee_saved_lookup HcsR r Hcs).
        rewrite /D upd_ne; [| congruence].
        rewrite /C5 upd_ne; [| congruence].
        rewrite /C4 upd_ne; [| congruence].
        rewrite /C3 upd_ne; [| congruence].
        rewrite /C2 upd_ne; [| congruence].
        rewrite /C1 upd_ne; [| congruence].
        rewrite (callee_saved_lookup HcsP r Hcs).
        rewrite /B upd_ne; [| congruence].
        apply HthrA; assumption. }
      iApply (sc_tail (CID0 := CID22) m R8 av (zero_reg : mword 64) sp0 ra0 s00 _ fv b p
                ltac:(lia) eq_refl eq_refl eq_refl HR8sp HR8a5 HthrR
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hfcell").
      iIntros (CID23 Hs23 mf) "[%Hcsf %Hmfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CID21 CID23 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      (* fileclose gave the complement back re-indexed at its own return hart
         [CID21], so this hop starts THERE -- it does not have to span
         fileclose's crossing, which is the literal [true] and would carry no
         chain fact at [b = false]. *)
      iDestruct (trap_csrs_ext_transport CID21 CID23 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID21 CID23 eb p
                   ltac:(rewrite Hb; wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Hcont" $! CID23 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hextc Hextm Hpc [Hpriv] Hpenv Hfenv");
        [exact Hcsf|].
      rewrite /sys_close_post. iRight. iExists fd, fv. iFrame "Hpriv". iPureIntro.
      split; [exact Hmfa0 | exact Hsome].
  Qed.

End ProofSysClose.

End SysCloseProof.
