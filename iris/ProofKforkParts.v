(* ProofKforkParts.v -- the pieces kfork's capstone shares, proved once here
   so [ProofKfork.v] is only the function's own control flow.

   kfork's frame is 8 slots ([addi sp,sp,-64]), the same layout fileclose
   uses:

     pa_stk sp0 1 = 56(sp)  saved ra      pa_stk sp0 5 = 24(sp)  saved s3
     pa_stk sp0 2 = 48(sp)  saved s0      pa_stk sp0 6 = 16(sp)  saved s4
     pa_stk sp0 3 = 40(sp)  saved s1      pa_stk sp0 7 =  8(sp)  saved s5
     pa_stk sp0 4 = 32(sp)  saved s2      pa_stk sp0 8 =  0(sp)  unused

   and s2/s3/s4 are LAZILY spilled -- s4 only after allocproc has found a
   slot (+0x1a), s2/s3 only after uvmcopy has succeeded (+0x30/+0x32) -- so
   the epilogue restores ra/s0/s1/s5 ONLY and [callee_saved] for the other
   three is a PREMISE about the incoming map, exactly the shape
   claude-notes/completed/fileclose.md records.

   What is here:

   * [kfk_frm1] .. [kfk_frm7] -- the slot arithmetic (identical to
     fileclose's, restated rather than imported: importing
     ProofFilecloseParts.v would drag the whole fileclose decode layer, and
     these are four-line facts).

   * [kfk_epi] -- the epilogue at +0xfc ([c.mv a0,s1] and the four restores),
     which ALL THREE exits reach.

   * The resource-level bridges kfork needs and [ProcInv.v] does not yet
     have.  They live here rather than in ProcInv.v so that landing kfork
     does not rebuild the whole tree; each is a candidate to be lifted the
     next time someone is in that file for another reason.
     - [kfk_um_below_child] -- what makes [np->sz = p->sz] legal: the
       child's map after uvmcopy is still bounded by the size it inherits.
     - [kfk_tf_disp] / [kfk_tf_step] / [kfk_tf_inj] -- the address
       arithmetic of the four-words-per-iteration trapframe copy, and its
       [bne a5,a3] exit test.
     - [tf_page_word_upd] -- the WRITE twin of [ProcInv.tf_page_word]: the
       trapframe copy STORES into the child's page, and the read accessor's
       wand rebuilds at the value it lent out.
     - [proc_priv_tfp_valid] -- [page_valid] of the trapframe page, read off
       [ProcPtOwn.proc_pt_wf] rather than taken as a premise.
     - [kfk_pname_bytes] / [kfk_bytes_pname] -- [ProcInv.pname_cells] as the
       [seq]-indexed byte big-op [SpecSafestrcpy.v] states its buffers over.
     - [kfk_of_priv] -- a freshly-allocated child's [proc_priv] taken apart
       into [SpecFreeproc]'s three pieces, which is what the uvmcopy-failure
       tail hands freeproc.  Both address-space slots are [Some] there, the
       one case allocproc's own two tails never exercise. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs.
Require Import PageGeom PageFields.
Require Import ProcGeom.
Require Import PtBuild.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import SwtchCtx.
Require Import ProcInv.
Require Import KallocInv.
Require Import SpecFreeproc.
Require Import CodeKfork.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Notation KF := KernelSyms.kfork (only parsing).

(* ------------------------------------------------------------------ *)
(*  The frame slots this function's prologue and epilogue touch.        *)
(* ------------------------------------------------------------------ *)
Lemma kfk_frm1 (X : mword 64) :          (* 56(sp) : saved ra *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kfk_frm2 (X : mword 64) :          (* 48(sp) : saved s0 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kfk_frm3 (X : mword 64) :          (* 40(sp) : saved s1 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kfk_frm4 (X : mword 64) :          (* 32(sp) : saved s2 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kfk_frm5 (X : mword 64) :          (* 24(sp) : saved s3 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kfk_frm6 (X : mword 64) :          (* 16(sp) : saved s4 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kfk_frm7 (X : mword 64) :          (*  8(sp) : saved s5 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
  = pa_stk X 7.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kfk_frame_back (K : nat) : (8 <= K)%nat -> ((K - 8) + 8)%nat = K.
Proof. lia. Qed.

(* ------------------------------------------------------------------ *)
(*  THE CHILD'S MAP IS STILL BELOW THE SIZE IT INHERITS.                *)
(*                                                                      *)
(*  [np->sz = p->sz] is the store that makes the child's private block   *)
(*  claim [um_below (pv_sz Vp) (ud_um P')], and nothing in uvmcopy's own  *)
(*  postcondition says so directly -- it reports where the new map came   *)
(*  from, not what it is bounded by.  The argument is the obvious one and *)
(*  it needs all three of uvmcopy's clauses: a vpn OUTSIDE the run reads   *)
(*  back off [Pnew], which allocproc left EMPTY; a vpn inside the run is   *)
(*  mapped only where the PARENT mapped it, and the parent's block already *)
(*  says every such vpn is below [sz].                                     *)
(* ------------------------------------------------------------------ *)
Lemma kfk_vpn_run_elem (vpn0 vpn : mword 27) (k : nat) :
  vpn ∈ vpn_run vpn0 k -> exists i, (i < k)%nat /\ vpn = vpn_at vpn0 i.
Proof.
  rewrite /vpn_run. intro Hin.
  apply elem_of_list_to_set in Hin.
  apply elem_of_list_fmap in Hin as (i & -> & Hi).
  apply elem_of_seq in Hi. exists i. split; [lia | reflexivity].
Qed.

Lemma kfk_um_below_child (sz : mword 64) (vpn0 : mword 27) (Pold Pnew P' : uptd) :
  ud_um Pnew = ∅ ->
  um_below sz (ud_um Pold) ->
  (forall vpn, vpn ∉ vpn_run vpn0 (uvm_np sz) ->
     ud_um P' !! vpn = ud_um Pnew !! vpn) ->
  (forall i, (i < uvm_np sz)%nat ->
     match ud_um Pold !! vpn_at vpn0 i with
     | None => ud_um P' !! vpn_at vpn0 i = ud_um Pnew !! vpn_at vpn0 i
     | Some _ => exists w' : mword 64, ud_um P' !! vpn_at vpn0 i = Some w'
     end) ->
  um_below sz (ud_um P').
Proof.
  intros Hempty Hold Hout Hin vpn w Hl.
  destruct (decide (vpn ∈ vpn_run vpn0 (uvm_np sz))) as [Hmem | Hnot].
  - destruct (kfk_vpn_run_elem vpn0 vpn (uvm_np sz) Hmem) as (i & Hi & ->).
    specialize (Hin i Hi).
    destruct (ud_um Pold !! vpn_at vpn0 i) as [w0 |] eqn:Hp.
    + exact (Hold _ _ Hp).
    + rewrite Hin Hempty lookup_empty in Hl. discriminate.
  - rewrite (Hout vpn Hnot) Hempty lookup_empty in Hl. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  THE TRAPFRAME COPY'S ADDRESS ARITHMETIC.                            *)
(*                                                                      *)
(*  The loop walks the SOURCE pointer a5 and the DESTINATION pointer a4  *)
(*  in lockstep, four words at a time, and each iteration reaches its    *)
(*  four words through the 12-bit displacements 0/8/16/24.  So every     *)
(*  address in the body is [a_tf_word tfp (4*k + j)], and the bump at    *)
(*  +0x5a/+0x5e is [a_tf_word tfp (4*(S k))].                            *)
(* ------------------------------------------------------------------ *)
Lemma kfk_avi (v : mword 64) (d : Z) :
  (sign_extend' 64 (mword_of_int d : mword 12) : mword 64) = (mword_of_int d : mword 64) ->
  add_vec v (sign_extend' 64 (mword_of_int d : mword 12)) = add_vec_int v d.
Proof. intro H. by rewrite H. Qed.

Lemma kfk_tf_disp (tfp : mword 44) (k j : nat) (d : Z) :
  d = 8 * Z.of_nat j ->
  (sign_extend' 64 (mword_of_int d : mword 12) : mword 64) = (mword_of_int d : mword 64) ->
  add_vec (a_tf_word tfp (4 * k)) (sign_extend' 64 (mword_of_int d : mword 12))
  = a_tf_word tfp (4 * k + j).
Proof.
  intros Hd Hs. rewrite (kfk_avi _ d Hs).
  rewrite /a_tf_word /pa_add avi_assoc. f_equal. lia.
Qed.

Lemma kfk_tf_step (tfp : mword 44) (k : nat) :
  (sign_extend' 64 (mword_of_int 32 : mword 12) : mword 64) = (mword_of_int 32 : mword 64) ->
  add_vec (a_tf_word tfp (4 * k)) (sign_extend' 64 (mword_of_int 32 : mword 12))
  = a_tf_word tfp (4 * S k).
Proof.
  intro Hs. rewrite (kfk_avi _ 32 Hs).
  rewrite /a_tf_word /pa_add avi_assoc. f_equal. lia.
Qed.

(* The [bne a5,a3] exit test.  The two addresses are offsets into ONE page,
   and a page is 4096-aligned and well below the top of RAM, so distinct
   offsets are distinct addresses -- there is no wraparound to worry about,
   which is exactly what [page_valid] buys. *)
Lemma kfk_tf_inj (tfp : mword 44) (i j : nat) :
  page_valid (page_base tfp) ->
  (8 * i < 4096)%nat -> (8 * j < 4096)%nat ->
  a_tf_word tfp i = a_tf_word tfp j -> i = j.
Proof.
  intros [_ [Hlo Hhi]] Hi Hj Heq.
  rewrite /a_tf_word /pa_add in Heq.
  pose proof (bv_unsigned_in_range 64 (page_base tfp)) as [Hnn _].
  rewrite uint_unsigned in Hhi.
  assert (Hbnd : (bv_unsigned (page_base tfp) < 2281701376)%Z)
    by (unfold kmem_hi in Hhi; exact Hhi).
  assert (Hii : (0 <= Z.of_nat (8 * i))%Z) by lia.
  assert (Hjj : (0 <= Z.of_nat (8 * j))%Z) by lia.
  assert (Hif : (bv_unsigned (page_base tfp) + Z.of_nat (8 * i) < 18446744073709551616)%Z) by lia.
  assert (Hjf : (bv_unsigned (page_base tfp) + Z.of_nat (8 * j) < 18446744073709551616)%Z) by lia.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (pa_add_unsigned _ _ Hii Hif) (pa_add_unsigned _ _ Hjj Hjf) in Heq.
  lia.
Qed.

Section ProofKforkParts.
  Context `{!riscvGS Σ, !sieG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne :=
    first [ congruence
          | apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption] ].

  (* =================================================================== *)
  (*  +0xfc .. +0x108 -- THE EPILOGUE.  All three exits reach it.         *)
  (*                                                                      *)
  (*    c.mv a0,s1 ; c.ldsp ra,56 ; c.ldsp s0,48 ; c.ldsp s1,40 ;         *)
  (*    c.ldsp s5,8 ; c.addi16sp sp,64 ; c.jr ra                          *)
  (*                                                                      *)
  (*  s2/s3/s4 are NOT restored here: they are spilled lazily, so on the   *)
  (*  allocproc-failure path they were never written and on the uvmcopy    *)
  (*  path only s4 was (its own tail reloads it).  Their [callee_saved]    *)
  (*  conjuncts therefore come out of [Hthr], the premise about the map    *)
  (*  this block is entered with.                                         *)
  (* =================================================================== *)
  Lemma kfk_epi `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s50 rv : mword 64) (w4 w5 w6 w8 : mword 64)
      (p : mword 64) (b : bool) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    Mt !!! Regidx Rs1 = rv ->
    (* every callee-saved register except sp/s0/s1/s5 already agrees with the
       entry map -- the four this block restores are the only ones it may
       have lost. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0xfc) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) s50 -∗
    word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hs50 Hmtsp Hmts1 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hcont".
    iPoseProof (kfk_0fc with "Htext") as "Hi0fc".
    iPoseProof (kfk_0fe with "Htext") as "Hi0fe".
    iPoseProof (kfk_100 with "Htext") as "Hi100".
    iPoseProof (kfk_102 with "Htext") as "Hi102".
    iPoseProof (kfk_104 with "Htext") as "Hi104".
    iPoseProof (kfk_106 with "Htext") as "Hi106".
    iPoseProof (kfk_108 with "Htext") as "Hi108".
    (* ---- +0xfc: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KF + 0xfc)) Ra0 Rs1 Mt (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0fc [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (rget Mt Rs1))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget Mt Rs1))]> Mt)
      with T0.
    assert (HT0a0 : T0 !!! Regidx Ra0 = rv).
    { rewrite /T0 upd_eq. rewrite add_vec_zero_l. exact Hmts1. }
    assert (HT0sp : T0 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T0 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hpp0fe : add_vec_int (mword_of_int (KF + 0xfc) : mword 64) 2
                     = mword_of_int (KF + 0xfe)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0fe) in "Hpc".
    (* ---- +0xfe: c.ldsp ra,56(sp) ---- *)
    assert (Hpa1 : add_vec (T0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                   = pa_stk sp0 1) by (rewrite HT0sp; apply kfk_frm1).
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0xfe)) (mword_of_int 7 : mword 6) Rra
              T0 (K - 8)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0fe Hb1 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> T0).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T1 upd_ne; [exact HT0sp | vm_compute; discriminate]).
    assert (Hpp100 : add_vec_int (mword_of_int (KF + 0xfe) : mword 64) 2
                     = mword_of_int (KF + 0x100)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp100) in "Hpc".
    (* ---- +0x100: c.ldsp s0,48(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                   = pa_stk sp0 2) by (rewrite HT1sp; apply kfk_frm2).
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0x100)) (mword_of_int 6 : mword 6) Rs0
              T1 (K - 8)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi100 Hb2 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (Hpp102 : add_vec_int (mword_of_int (KF + 0x100) : mword 64) 2
                     = mword_of_int (KF + 0x102)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp102) in "Hpc".
    (* ---- +0x102: c.ldsp s1,40(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                   = pa_stk sp0 3) by (rewrite HT2sp; apply kfk_frm3).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0x102)) (mword_of_int 5 : mword 6) Rs1
              T2 (K - 8)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi102 Hb3 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (Hpp104 : add_vec_int (mword_of_int (KF + 0x102) : mword 64) 2
                     = mword_of_int (KF + 0x104)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp104) in "Hpc".
    (* ---- +0x104: c.ldsp s5,8(sp) ---- *)
    assert (Hpa7 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 7) by (rewrite HT3sp; apply kfk_frm7).
    iEval (rewrite -Hpa7) in "Hb7".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0x104)) (mword_of_int 1 : mword 6) Rs5
              T3 (K - 8)%nat s50 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi104 Hb7 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hb7". iEval (rewrite Hpa7) in "Hb7".
    set (T4 := <[Regidx Rs5 := regval_into_reg s50]> T3).
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    assert (Hpp106 : add_vec_int (mword_of_int (KF + 0x104) : mword 64) 2
                     = mword_of_int (KF + 0x106)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp106) in "Hpc".
    (* ---- +0x106: c.addi16sp sp,64 -- the frame goes back ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0)
      by (rewrite HT4sp; apply stk_pop_64).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8)
      by (rewrite Hwv; exact HT4sp).
    iAssert (stack_own sp0 8) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      iSplitL "Hb7"; [iExists _; iExact "Hb7"|].
      iSplitL "Hb8"; [iExists _; iExact "Hb8"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KF + 0x106)) (mword_of_int 4 : mword 6)
              T4 (K - 8)%nat 8 b Hpop with "Hcg Hpc Hi106 Hframe [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hnk : ((K - 8) + 8)%nat = K) by exact (kfk_frame_back K HK).
    iEval (rewrite Hnk) in "Hcg".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> T4) with T5.
    assert (Hpp108 : add_vec_int (mword_of_int (KF + 0x106) : mword 64) 2
                     = mword_of_int (KF + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp108) in "Hpc".
    (* ---- +0x108: c.jr ra ---- *)
    assert (HT5ra : T5 !!! Regidx Rra = ra0).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1; apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (KF + 0x108)) Rra T5 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi108 [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HT5ra) in "Hpc".
    iSpecialize ("Hcont" $! CID7 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! T5 with "[%] Hcg Hpc").
    assert (Hrest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                      r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> r <> Rra -> r <> Ra0 ->
                      T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns5 Nra Na0.
      rewrite /T5 upd_ne; [| regne].
      rewrite /T4 upd_ne; [| regne].
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [| regne].
      rewrite /T0 upd_ne; [| regne].
      exact (Hthr r Hr Nsp Ns0 Ns1 Ns5). }
    assert (HT5a0 : T5 !!! Regidx Ra0 = rv).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [| vm_compute; discriminate].
      exact HT0a0. }
    split; [| exact HT5a0].
    (* the thirteen conjuncts are sp, s0, s1, s2 .. s11 -- so the four this
       block restores are goals 1, 2, 3 and 7, and the other nine come
       straight out of [Hrest]. *)
    rewrite /callee_saved. split_and!.
    4-6, 8-13: apply Hrest; vm_compute; first [reflexivity | discriminate].
    - rewrite /T5 upd_eq Hwv Hsp0. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq Hs00. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq Hs10. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_eq Hs50. reflexivity.
  Qed.

End ProofKforkParts.

(* =================================================================== *)
(*  THE RESOURCE-LEVEL BRIDGES.                                         *)
(* =================================================================== *)
Section KforkRes.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.
  Context `{GEN : GenId}.

  (* ---- the WRITE twin of [ProcInv.tf_page_word] ------------------- *)
  (* The read accessor rebuilds the page at the value it lent out, which
     is right for argraw and wrong for a COPY: the child's trapframe words
     are stored, not read back.  Same one-line [big_sepL_insert_acc]
     proof, with the wand quantified over the new value. *)
  Lemma tf_page_word_upd (tfp : mword 44) (ws : list (mword 64))
      (i : nat) (w : mword 64) :
    ws !! i = Some w ->
    tf_page tfp ws -∗
    a_tf_word tfp i ↦₈ w ∗
    (∀ w' : mword 64, a_tf_word tfp i ↦₈ w' -∗ tf_page tfp (<[i := w']> ws)).
  Proof.
    rewrite /tf_page /tf_words. iIntros (Hi) "(%Hlen & Hws & Htail)".
    iDestruct (big_sepL_insert_acc _ _ i w Hi with "Hws") as "[$ Hback]".
    iIntros (w') "Hc". iDestruct ("Hback" $! w' with "Hc") as "Hws".
    iSplitR; [iPureIntro; by rewrite length_insert|].
    iFrame "Hws Htail".
  Qed.

  (* ---- the WRITE twin of [ProcInv.proc_priv_tf] --------------------- *)
  (* [proc_priv_tf]'s wand rebuilds the block at the CONTENTS it lent out,
     which is right for a syscall-argument read and useless for a copy: the
     child's trapframe is 36 words of new data by the time the loop is done.
     This lends the same two things and takes back a DIFFERENT [ws'].

     It hands the [p_trapframe] cell out WHOLE rather than at the quarter
     [proc_priv_tf] splits off, for two reasons: the [ld a5,88(s4)] at +0x66
     wants a fraction and does not care which, and [ProcInv]'s
     [word_split14] / [word_join14] are [Local], so a quarter cannot be
     split here at all.  No length side condition is needed on the way back:
     [tf_page] carries [length ws = TFWORDS] itself. *)
  Lemma proc_priv_tf_upd (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) ∗
    tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
    (∀ ws' : list (mword 64),
       p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) -∗
       tf_page (ud_tfp (pv_upt V)) ws' -∗
       proc_priv γf pa pid (upd_pt V (pv_upt V) ws')).
  Proof.
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc) Ho]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iFrame "Htfc Htfp".
    iIntros (ws') "Htfc Htfp".
    rewrite /proc_priv /proc_priv_core /proc_pt_at.
    cbn [upd_pt pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho"; [| iFrame "Ho"].
    iSplitR; [iPureIntro; exact Hszb|].
    iSplitR; [iPureIntro; exact Hbel|].
    iFrame "Hpid Hf Hpg Htfc Hptt Htfp Hc".
  Qed.

  (* [upd_pt] at the SAME descriptor and the SAME contents is the identity --
     the record eta the two accessors above need to close a round trip that
     changed nothing. *)
  Lemma upd_pt_id (V : pprivate) :
    upd_pt V (pv_upt V) (pv_tf V) = V.
  Proof. by destruct V. Qed.

  (* The trapframe page is a kalloc page, and the fact is a projection of the
     block rather than a premise on it: [ProcPtOwn.proc_pt_wf]'s last
     conjunct.  The trapframe-copy loop's exit test needs it (see
     [kfk_tf_inj]) and so does [SpecFreeproc.fp_tf]. *)
  Lemma proc_priv_tfp_valid (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜page_valid (page_base (ud_tfp (pv_upt V)))⌝.
  Proof.
    iIntros "[(_ & _ & _ & _ & Hpt & _) _]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(_ & _ & Hptt)".
    iDestruct (proc_pt_wf_get with "Hptt") as "%Hwf".
    iPureIntro. exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
  Qed.

  (* ---- p->name as the byte big-op safestrcpy states its buffers over ---- *)
  Definition kfk_name_base (pa : mword 64) : mword 64 :=
    add_vec pa (mword_of_int 344).

  Lemma kfk_name_addr (pa : mword 64) (i : nat) :
    pa_add (kfk_name_base pa) i = p_name pa i.
  Proof.
    rewrite /kfk_name_base /p_name /pa_add.
    change (add_vec pa (mword_of_int 344)) with (add_vec_int pa 344).
    rewrite avi_assoc.
    reflexivity.
  Qed.

  (* re-indexing a [big_sepL] over a list by the FUNCTION that computes its
     elements -- what turns [pname_cells]' element-indexed big-op into
     [SpecSafestrcpy]'s [seq]-indexed one. *)
  Lemma kfk_list_of_fn {A : Type} (l : list A) (f : nat -> A) :
    (forall i, (i < length l)%nat -> l !! i = Some (f i)) ->
    l = f <$> seq 0 (length l).
  Proof.
    intro Hf. apply list_eq. intro i.
    rewrite list_lookup_fmap.
    destruct (decide (i < length l)%nat) as [Hi | Hi].
    - rewrite (lookup_seq_lt 0 (length l) i Hi) /=. exact (Hf i Hi).
    - rewrite (lookup_ge_None_2 l i ltac:(lia)).
      rewrite (lookup_seq_ge 0 (length l) i ltac:(lia)). reflexivity.
  Qed.

  Lemma kfk_pname_bytes (pa : mword 64) (dq : dfrac) (bs : list (bv 8))
      (f : nat -> bv 8) :
    (forall i, (i < length bs)%nat -> bs !! i = Some (f i)) ->
    pname_cells pa dq bs ⊣⊢
    ([∗ list] j ∈ seq 0 (length bs), pa_add (kfk_name_base pa) j ↦ₘ{dq} f j).
  Proof.
    intro Hf. rewrite /pname_cells.
    rewrite {1}(kfk_list_of_fn bs f Hf).
    rewrite big_sepL_fmap.
    apply big_sepL_proper. intros k x Hkx.
    apply lookup_seq in Hkx as [-> _].
    by rewrite kfk_name_addr.
  Qed.

  Lemma kfk_bytes_pname (pa : mword 64) (dq : dfrac) (n : nat) (h : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 n, pa_add (kfk_name_base pa) j ↦ₘ{dq} h j) -∗
    pname_cells pa dq (h <$> seq 0 n).
  Proof.
    iIntros "H". rewrite /pname_cells big_sepL_fmap.
    iApply (big_sepL_impl with "H"). iIntros "!>" (k x Hkx) "Hc".
    apply lookup_seq in Hkx as [-> _]. by rewrite kfk_name_addr.
  Qed.

  Lemma kfk_name_len (n : nat) (h : nat -> bv 8) :
    length (h <$> seq 0 n) = n.
  Proof. by rewrite length_fmap length_seq. Qed.

End KforkRes.

(* =================================================================== *)
(*  WHAT THE uvmcopy-FAILURE TAIL HANDS freeproc.                       *)
(*                                                                      *)
(*  allocproc returns the child as an assembled [ProcInv.proc_priv] with *)
(*  its allowance and its raw context beside it; freeproc wants          *)
(*  [SpecFreeproc]'s THREE pieces, whose two address-space slots are     *)
(*  independently optional.  At this point the child has a LIVE page      *)
(*  table and a LIVE trapframe page (uvmcopy rolled its own work back but *)
(*  neither cell was ever cleared), so both slots are [Some] -- which is  *)
(*  the one case allocproc's own two tails never exercise.                *)
(*                                                                      *)
(*  Everything here is a repackaging.  The two facts that are NOT already *)
(*  spelled in [proc_priv] are [um_below] / [uint sz <= uvm_maxsz] (its   *)
(*  first two conjuncts) and [page_valid] of the trapframe page, which is *)
(*  [proc_pt_wf]'s last conjunct -- see [proc_priv_tfp_valid].            *)
(* =================================================================== *)
Section KforkFreeproc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma kfk_of_priv (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    pv_ofile V = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd V = (zero_reg : mword 64) ->
    proc_priv γf pa pid V -∗
    fd_slots FDSPARE -∗
    own_ctx (p_context pa) -∗
    SpecFreeproc.fp_rest pa V pid ∗
    SpecFreeproc.fp_pt pa (pv_sz V) (Some (pv_upt V)) ∗
    SpecFreeproc.fp_tf pa (Some (ud_tfp (pv_upt V), pv_tf V)).
  Proof.
    intros Hof Hcwd.
    iIntros "Hpv Hsp Hctx".
    iDestruct (proc_priv_tfp_valid with "Hpv") as "%Hpv".
    iDestruct "Hpv" as "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & _) Ho]".
    iDestruct (proc_ofiles_null_split γf pa (pv_ofile V) Hof with "Ho")
      as "[Hcells Hunits]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    rewrite /SpecFreeproc.fp_rest /SpecFreeproc.fp_pt /SpecFreeproc.fp_tf.
    cbn [fst snd].
    iSplitR "Hpg Hptt Htfc Htfp".
    { iSplitR; [iPureIntro; split_and!; [exact Hof | exact Hcwd | exact Hszb]|].
      iFrame "Hpid Hf Hcells Hunits Hsp Hctx". }
    iSplitL "Hpg Hptt".
    { iFrame "Hpg Hptt". iPureIntro. split; [exact Hbel | exact Hszb]. }
    iFrame "Htfc Htfp". iPureIntro. exact Hpv.
  Qed.

End KforkFreeproc.
