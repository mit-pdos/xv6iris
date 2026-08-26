(* ProofBinit.v -- the whole-function WP for xv6's binit() over the
   SIE-agnostic sconf world.

     void binit(void) {
       initlock(&bcache.lock, "bcache");
       bcache.head.prev = bcache.head.next = &bcache.head;
       for (b = bcache.buf; b < bcache.buf + NBUF; b++) {
         b->next = bcache.head.next;  b->prev = &bcache.head;
         initsleeplock(&b->lock, "buffer");
         bcache.head.next->prev = b;  bcache.head.next = b;
       }
     }

   Three parts: the initlock-wrapper prologue (6-slot frame, ra/s0..s4 saved,
   two auipc/addi argument pairs, jal initlock), the two stores that make the
   head sentinel an empty cycle, and then a BOUNDED loop that both initializes a
   buffer's sleeplock and splices it into the list -- proved, like freerange's
   loop over kfree, by ordinary Coq fuel induction on the buffers left, NOT
   iLoeb (the packaged sconf leaves strip the step's later, so a later-guarded
   IH could never be applied).

   The list work is entirely in [BcacheInv.bcache_lru_splice]: it hands the body
   the only two cells the splice touches outside the new buffer -- the head's
   next field and the prev field of whatever the head currently points at (both
   holding [bhead] on entry) -- plus a wand that takes the four updated cells
   back.  So the loop never reasons about the list's shape, and the fact that
   the "head.next->prev" store lands on the head itself in the first iteration
   and on the previous buffer afterwards needs no case split here.

   EXPLICIT-CPUID: binit merely THREADS the SIE state (never flips it), so
   every plain instruction's [wp_next] index is the same [b] the bundle
   carries, and neither [biepi] nor the loop needs to case-split on it. Both
   [biepi] (the epilogue) and the fuel-induction loop are DECOMPOSED helpers
   applied at a hart a caller's own leaf steps may have migrated to, so each
   gets its OWN fresh [CpuId] binder (shadowing what a section [Context] would
   give) instead of sharing one rigid section-wide hart -- the section below
   therefore does NOT fix an ambient [CID], mirroring ProofIinit.v (the
   structurally closest ported example: same initlock-prologue-then-bounded-
   initsleeplock-loop shape). binit calls neither push_off/pop_off nor
   initlock/initsleeplock ever return a [cpu_own] -- their [SpecInitlock.v] /
   [SpecInitsleeplock.v] contracts don't mention it -- so this file needs no
   [cpu_own_transport] calls at all. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock SleepLock.
Require Import ArrCursor BcacheInv.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecInitlock SpecInitsleeplock.
Require Import CodeBinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecBinit.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Require TsoCtxShim.   (* BcacheInv's link cells ([blink_raw]/[bcache_lru]) are
                         still the RAW word tower: every store/load of one
                         crosses the ctx seam here. *)
Local Open Scope Z_scope.
Import Defs.

Module BinitProof (Initlock : INITLOCK) (Initsleeplock : INITSLEEPLOCK) : BINIT.

Section ProofBinit.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  (* NOTE: no shared [Context `{GEN : GenId} `{CID : CpuId}] here -- [biepi] and the loop
     below apply each other (and are applied by [wp_binit_sconf]) at a hart a
     [wp_next] crossing may have migrated to, so each needs its OWN implicit
     per-lemma [CID] binder; see the file header and ProofIinit.v. *)


  (* the four register indices the loop keeps live besides s0/s1 *)
  Notation s2i := (mword_of_int 18 : mword 5).
  Notation s3i := (mword_of_int 19 : mword 5).
  Notation s4i := (mword_of_int 20 : mword 5).

  (* the base the head sentinel's two link fields are addressed off: gcc keeps
     bcache+0x8000 in a5/s2 and reaches head.prev/head.next at +688/+696. *)
  Definition hbase : mword 64 := mword_of_int (KernelSyms.bcache + 32768).

  Lemma hbase_prev : add_vec hbase (sign_extend' 64 (mword_of_int 688 : mword 12)) = bprev bhead.
  Proof.
    unfold hbase, bprev, bhead, bnode, acur, buf_base, buf_stride, NBUF, KernelSyms.bcache.
    apply bv_eq; vm_compute; reflexivity.
  Qed.
  Lemma hbase_next : add_vec hbase (sign_extend' 64 (mword_of_int 696 : mword 12)) = bnext bhead.
  Proof.
    unfold hbase, bnext, bhead, bnode, acur, buf_base, buf_stride, NBUF, KernelSyms.bcache.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* ================================================================= *)
  (*  The epilogue (+0x76..+0x84): restore ra/s0/s1/s2/s3/s4, give the   *)
  (*  6-slot frame back, ret.  Payload-free: the caller's postcondition   *)
  (*  resources ride in the framed [-].  Its own fresh [CID0] binder      *)
  (*  (shadowing any ambient hart) is the "decomposed helper" rule --     *)
  (*  worked example ProofFreerange.frepi / ProofIinit.iiepi.             *)
  (* ================================================================= *)
  Lemma biepi `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx} (m Me : regfile) (K : nat) (b : bool) (pcur : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
    (6 <= K)%nat ->
    Me !!! Regidx csp_rs1 = spr ->
    (forall c : mword 5, is_cs_idx c = true ->
       c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> s4i -> c <> csp_rs1 ->
       Me !!! Regidx c = m !!! Regidx c) ->
    kernel_text -∗
    sie_cap_gpr KT1 Me (K - 6) b pcur -∗
    pc_is (mword_of_int (KernelSyms.binit + 0x76)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx s2i : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx s3i : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx s4i : mword 64) -∗
    wp_next b pcur (fun (CID : CpuId) =>
      ∀ mr,
      sie_cap_gpr KT1 mr K b pcur -∗
      pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt HK6 HMesp HMecs.
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iIntros "#Htext Hcg Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hcont".
    (* +0x76 c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.binit + 0x76)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              Me (K - 6)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc1]").
    { iApply (bii_76 with "Htext"). }
    { iEval (rewrite HMesp Hb1). iExact "Hc1". }
    iIntros (CID1 Hs1) "Hcg Hpc Hc1".
    iEval (rewrite HMesp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> Me).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact HMesp | vm_compute; discriminate]).
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.binit + 0x76) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp78) in "Hpc".
    (* +0x78 c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.binit + 0x78)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 6)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc2]").
    { iApply (bii_78 with "Htext"). }
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc2".
    iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.binit + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7a) in "Hpc".
    (* +0x7a c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.binit + 0x7a)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 6)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc3]").
    { iApply (bii_7a with "Htext"). }
    { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc3".
    iEval (rewrite HE2sp Hb3) in "Hc3".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3 upd_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.binit + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    (* +0x7c c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.binit + 0x7c)) (mword_of_int 2 : mword 6) s2i
              E3 (K - 6)%nat (m !!! Regidx s2i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc4]").
    { iApply (bii_7c with "Htext"). }
    { iEval (rewrite HE3sp Hb4). iExact "Hc4". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc4".
    iEval (rewrite HE3sp Hb4) in "Hc4".
    set (E4 := <[Regidx s2i := regval_into_reg (m !!! Regidx s2i)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spr) by (rewrite /E4 upd_ne; [exact HE3sp | vm_compute; discriminate]).
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.binit + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* +0x7e c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.binit + 0x7e)) (mword_of_int 1 : mword 6) s3i
              E4 (K - 6)%nat (m !!! Regidx s3i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc5]").
    { iApply (bii_7e with "Htext"). }
    { iEval (rewrite HE4sp Hb5). iExact "Hc5". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc5".
    iEval (rewrite HE4sp Hb5) in "Hc5".
    set (E5 := <[Regidx s3i := regval_into_reg (m !!! Regidx s3i)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spr) by (rewrite /E5 upd_ne; [exact HE4sp | vm_compute; discriminate]).
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.binit + 0x7e) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp80) in "Hpc".
    (* +0x80 c.ldsp s4,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.binit + 0x80)) (mword_of_int 0 : mword 6) s4i
              E5 (K - 6)%nat (m !!! Regidx s4i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc6]").
    { iApply (bii_80 with "Htext"). }
    { iEval (rewrite HE5sp Hb6). iExact "Hc6". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc6".
    iEval (rewrite HE5sp Hb6) in "Hc6".
    set (E6 := <[Regidx s4i := regval_into_reg (m !!! Regidx s4i)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spr) by (rewrite /E6 upd_ne; [exact HE5sp | vm_compute; discriminate]).
    assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.binit + 0x80) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp82) in "Hpc".
    (* +0x82 c.addi16sp sp,48 -- the frame trade back (pop 6) *)
    set (E7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6).
    assert (HE7sp : E7 !!! Regidx csp_rs1 = sp0).
    { rewrite /E7 upd_eq. rewrite HE6sp.
      unfold spr. rewrite pa_stk_off2.
      replace (mword_of_int (bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)) : mword 64) + uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)) : mword 64))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      change (add_vec sp0 (mword_of_int 0)) with (add_vec_int sp0 0). apply avi0. }
    assert (Hup : E6 !!! Regidx csp_rs1 = pa_stk (E7 !!! Regidx csp_rs1) 6).
    { rewrite HE6sp HE7sp Hspr6. reflexivity. }
    assert (Hwv : add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite -HE7sp /E7 upd_eq. reflexivity. }
    assert (Hpop : E6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv Hup HE7sp. reflexivity. }
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6]" as "Hframe6".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hc1"; [iExists _; iExact "Hc1"|].
      iSplitL "Hc2"; [iExists _; iExact "Hc2"|].
      iSplitL "Hc3"; [iExists _; iExact "Hc3"|].
      iSplitL "Hc4"; [iExists _; iExact "Hc4"|].
      iSplitL "Hc5"; [iExists _; iExact "Hc5"|].
      iSplitL "Hc6"; [iExists _; iExact "Hc6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe6".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.binit + 0x82)) (mword_of_int 3 : mword 6) E6 (K - 6)%nat 6 b Hpop
              with "Hcg Hpc [] Hframe6").
    { iApply (bii_82 with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6) with E7.
    assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.binit + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp84) in "Hpc".
    (* +0x84 c.ret *)
    assert (HE7ra : E7 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.binit + 0x84)) (mword_of_int 1 : mword 5) E7 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (bii_84 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (E7 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE7ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E7 with "Hcg Hpc [%]").
    (* callee_saved m E7 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> s4i -> c <> csp_rs1 ->
              E7 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 N20 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
      rewrite /E7 upd_ne; [| congruence].
      rewrite /E6 upd_ne; [| congruence].
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      apply HMecs; assumption. }
    assert (Hcs_s0 : E7 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_eq; reflexivity. }
    assert (Hcs_s1 : E7 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_eq; reflexivity. }
    assert (Hcs_s2 : E7 !!! Regidx s2i = m !!! Regidx s2i).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_eq; reflexivity. }
    assert (Hcs_s3 : E7 !!! Regidx s3i = m !!! Regidx s3i).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_eq; reflexivity. }
    assert (Hcs_s4 : E7 !!! Regidx s4i = m !!! Regidx s4i).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_eq; reflexivity. }
    unfold callee_saved.
    split. { exact HE7sp. }
    split. { exact Hcs_s0. }
    split. { exact Hcs_s1. }
    split. { exact Hcs_s2. }
    split. { exact Hcs_s3. }
    split. { exact Hcs_s4. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* ================================================================= *)
  (*  binit's whole-function WP.                                        *)
  (* ================================================================= *)
  Lemma wp_binit_sconf `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (m : regfile) (K : nat)
      (vlock : mword 32) (vname vcpu : mword 64) (b : bool) (pcur : mword 64)
    : wp_binit_sconf_body m K vlock vname vcpu b pcur.
  Proof.
    cbv beta delta [wp_binit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    pose (name_bcache := (mword_of_int bcache_name_str : mword 64)).
    pose (name_buffer := (mword_of_int buffer_name_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hlock Hname Hcpu Hraws Hlinks Hhlink Hcont".
    (* ---- the three string literals, read out of the data image ---- *)
    assert (Hbcache : forall j bt, cstring_bytes "bcache"%string !! j = Some bt ->
                       KernelData.kernel_data !! (bcache_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 7 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string bcache_name_str "bcache"%string name_bcache eq_refl ltac:(unfold text_end, bcache_name_str; lia)
                                                                                       ltac:(vm_compute; discriminate) Hbcache
                  with "Hkdata") as "#Hstr_bcache".
    assert (Hbuffer : forall j bt, cstring_bytes "buffer"%string !! j = Some bt ->
                       KernelData.kernel_data !! (buffer_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 7 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string buffer_name_str "buffer"%string name_buffer eq_refl ltac:(unfold text_end, buffer_name_str; lia)
                                                                                       ltac:(vm_compute; discriminate) Hbuffer
                  with "Hkdata") as "#Hstr_buffer".
    assert (Hslstr : forall j bt, cstring_bytes "sleep lock"%string !! j = Some bt ->
                      KernelData.kernel_data !! (0x80007568 + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 11 (destruct j as [|j];
             [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string 0x80007568 "sleep lock"%string sl_str_addr eq_refl ltac:(unfold text_end; lia)
                                                                                      ltac:(vm_compute; discriminate) Hslstr
                  with "Hkdata") as "#Hstr_sl".
    (* ---- the frame geometry ---- *)
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE: 6-slot frame push + save ra/s0/s1/s2/s3/s4 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hpush : add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) = pa_stk sp0 6)
      by (exact Hspr6).
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 b ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (bii_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vra0) "Hc1". iDestruct "S2" as (vs00) "Hc2".
    iDestruct "S3" as (vs10) "Hc3". iDestruct "S4" as (vs20) "Hc4".
    iDestruct "S5" as (vs30) "Hc5". iDestruct "S6" as (vs40) "Hc6".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* the saved values are the ORIGINAL ra/s0/s1/s2/s3/s4 *)
    assert (Hra_v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0_v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1_v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2_v : R1 !!! Regidx s2i = m !!! Regidx s2i)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs3_v : R1 !!! Regidx s3i = m !!! Regidx s3i)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs4_v : R1 !!! Regidx s4i = m !!! Regidx s4i)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.binit + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 6)%nat vra0 b with "Hcg Hpc [] [Hc1]").
    { iApply (bii_02 with "Htext"). }
    { iEval (rewrite HspR1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    iEval (rgne) in "Hc1". iEval (rewrite HspR1 Hb1 Hra_v) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.binit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.binit + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat vs00 b with "Hcg Hpc [] [Hc2]").
    { iApply (bii_04 with "Htext"). }
    { iEval (rewrite HspR1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    iEval (rgne) in "Hc2". iEval (rewrite HspR1 Hb2 Hs0_v) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.binit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.binit + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 6)%nat vs10 b with "Hcg Hpc [] [Hc3]").
    { iApply (bii_06 with "Htext"). }
    { iEval (rewrite HspR1 Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc3".
    iEval (rgne) in "Hc3". iEval (rewrite HspR1 Hb3 Hs1_v) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.binit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.binit + 0x08)) (mword_of_int 2 : mword 6) s2i
              R1 (K - 6)%nat vs20 b with "Hcg Hpc [] [Hc4]").
    { iApply (bii_08 with "Htext"). }
    { iEval (rewrite HspR1 Hb4). iExact "Hc4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc4".
    iEval (rgne) in "Hc4". iEval (rewrite HspR1 Hb4 Hs2_v) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.binit + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.binit + 0x0a)) (mword_of_int 1 : mword 6) s3i
              R1 (K - 6)%nat vs30 b with "Hcg Hpc [] [Hc5]").
    { iApply (bii_0a with "Htext"). }
    { iEval (rewrite HspR1 Hb5). iExact "Hc5". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc5".
    iEval (rgne) in "Hc5". iEval (rewrite HspR1 Hb5 Hs3_v) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.binit + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp s4,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.binit + 0x0c)) (mword_of_int 0 : mword 6) s4i
              R1 (K - 6)%nat vs40 b with "Hcg Hpc [] [Hc6]").
    { iApply (bii_0c with "Htext"). }
    { iEval (rewrite HspR1 Hb6). iExact "Hc6". }
    iIntros (CID7 Hs7) "Hcg Hpc Hc6".
    iEval (rgne) in "Hc6". iEval (rewrite HspR1 Hb6 Hs4_v) in "Hc6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.binit + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.binit + 0x0e)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_0e with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.binit + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== a1 := &"bcache", a0 := &bcache (0x10..0x1c) ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.binit + 0x10)) (mword_of_int 11 : mword 5) (mword_of_int 5 : mword 20)
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_10 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.binit + 0x10) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> R2).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.binit + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x14)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 2232 : mword 12)
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_14 with "Htext"). }
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 2232 : mword 12)))]> R3).
    assert (HR4a1 : R4 !!! Regidx (mword_of_int 11 : mword 5) = name_bcache).
    { rewrite /R4 upd_eq. rewrite /R3 upd_eq. unfold name_bcache, bcache_name_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.binit + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.binit + 0x18)) (mword_of_int 10 : mword 5) (mword_of_int 21 : mword 20)
              R4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_18 with "Htext"). }
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (R5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.binit + 0x18) : mword 64) (auipc_off (mword_of_int 21 : mword 20)))]> R4).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.binit + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 1792 : mword 12)
              R5 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_1c with "Htext"). }
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1792 : mword 12)))]> R5).
    assert (HR6a0 : R6 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R6 upd_eq. rewrite /R5 upd_eq. unfold lk, bcache_addr, KernelSyms.bcache.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HR6a1 : R6 !!! Regidx (mword_of_int 11 : mword 5) = name_bcache).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4a1 | vm_compute; discriminate]. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]. }
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.binit + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ===== jal initlock ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.binit + 0x20)) (mword_of_int 1 : mword 5) (mword_of_int 2089010 : mword 21)
              R6 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (bii_20 with "Htext"). }
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (R7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.binit + 0x20) : mword 64) 4)]> R6).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.binit + 0x20) : mword 64) (sign_extend' 64 (mword_of_int 2089010 : mword 21)) = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HR7a0 : R7 !!! Regidx (mword_of_int 10 : mword 5) = lk)
      by (rewrite /R7 upd_ne; [exact HR6a0 | vm_compute; discriminate]).
    assert (HR7a1 : R7 !!! Regidx (mword_of_int 11 : mword 5) = name_bcache)
      by (rewrite /R7 upd_ne; [exact HR6a1 | vm_compute; discriminate]).
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr)
      by (rewrite /R7 upd_ne; [exact HR6sp | vm_compute; discriminate]).
    assert (HR7ra : R7 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.binit + 0x24)).
    { rewrite /R7 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HR7cs : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 -> R7 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    iApply (Initlock.wp_initlock_sconf KT1 R7 vlock vname vcpu "bcache"%string (K - 6) b pcur
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HR7a1). iExact "Hstr_bcache". }
    { iEval (rewrite HR7a0). iExact "Hlock". }
    { iEval (rewrite HR7a0). iExact "Hname". }
    { iEval (rewrite HR7a0). iExact "Hcpu". }
    iIntros (CID14 Hs14 mil) "Hcg Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HR7a0) in "Hlock".
    iEval (rewrite HR7a0 HR7a1) in "Hlname".
    iMod (lock_name_intro with "Hstr_bcache Hlname") as "#Hlnm".
    iEval (rewrite HR7a0) in "Hcpu".
    assert (Hpcil : ret_pc (R7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.binit + 0x24)).
    { rewrite HR7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full.
    assert (Hilsp : mil !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hilcs_full csp_rs1 ltac:(vm_compute; reflexivity)); exact HR7sp).
    assert (Hilcs' : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 -> mil !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      rewrite (callee_saved_lookup Hilcs_full c Hc). apply HR7cs; assumption. }
    (* ===== the head sentinel: a5 := head-field base, a4 := &head ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.binit + 0x24)) (mword_of_int 15 : mword 5) (mword_of_int 29 : mword 20)
              mil (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_24 with "Htext"). }
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (T1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.binit + 0x24) : mword 64) (auipc_off (mword_of_int 29 : mword 20)))]> mil).
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.binit + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x28)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1780 : mword 12)
              T1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_28 with "Htext"). }
    iIntros (CID16 Hs16) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (T1 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1780 : mword 12)))]> T1).
    assert (HT2a5 : T2 !!! Regidx (mword_of_int 15 : mword 5) = hbase).
    { rewrite /T2 upd_eq. rewrite /T1 upd_eq. unfold hbase, KernelSyms.bcache.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.binit + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.binit + 0x2c)) (mword_of_int 14 : mword 5) (mword_of_int 30 : mword 20)
              T2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_2c with "Htext"). }
    iIntros (CID17 Hs17) "Hcg Hpc".
    set (T3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.binit + 0x2c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> T2).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.binit + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x30)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 2388 : mword 12)
              T3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_30 with "Htext"). }
    iIntros (CID18 Hs18) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (T3 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 2388 : mword 12)))]> T3).
    assert (HT4a4 : T4 !!! Regidx (mword_of_int 14 : mword 5) = bhead).
    { rewrite /T4 upd_eq. rewrite /T3 upd_eq.
      unfold bhead, bnode, acur, buf_base, buf_stride, NBUF, KernelSyms.bcache.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HT4a5 : T4 !!! Regidx (mword_of_int 15 : mword 5) = hbase).
    { rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [exact HT2a5 | vm_compute; discriminate]. }
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.binit + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 sd a4,688(a5) : bcache.head.prev := &bcache.head *)
    iDestruct "Hhlink" as "[Hhp Hhn]".
    iDestruct "Hhp" as (vhp) "Hhp". iDestruct "Hhn" as (vhn) "Hhn".
    (* [blink_raw] is BcacheInv's RAW word tower: cross into the ctx world
       for the two stores and cross back for [bcache_lru_nil]. *)
    iDestruct (TsoCtxShim.ctx_word_of_mem with "Hhp") as "Hhp".
    iDestruct (TsoCtxShim.ctx_word_of_mem with "Hhn") as "Hhn".
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x34)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 688 : mword 12)
              T4 (K - 6)%nat vhp b with "Hcg Hpc [] [Hhp]").
    { iApply (bii_34 with "Htext"). }
    { iEval (rgne). iEval (rewrite HT4a5 hbase_prev). iExact "Hhp". }
    iIntros (CID19 Hs19) "Hcg Hpc Hhp".
    iEval (rgne; rgne) in "Hhp". iEval (rewrite HT4a5 hbase_prev HT4a4) in "Hhp".
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.binit + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 sd a4,696(a5) : bcache.head.next := &bcache.head *)
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x38)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 696 : mword 12)
              T4 (K - 6)%nat vhn b with "Hcg Hpc [] [Hhn]").
    { iApply (bii_38 with "Htext"). }
    { iEval (rgne). iEval (rewrite HT4a5 hbase_next). iExact "Hhn". }
    iIntros (CID20 Hs20) "Hcg Hpc Hhn".
    iEval (rgne; rgne) in "Hhn". iEval (rewrite HT4a5 hbase_next HT4a4) in "Hhn".
    (* back across the ctx seam: [bcache_lru] is BcacheInv's RAW word tower *)
    iDestruct (TsoCtxShim.ctx_word_to_mem with "Hhn") as "Hhn".
    iDestruct (TsoCtxShim.ctx_word_to_mem with "Hhp") as "Hhp".
    iPoseProof (bcache_lru_nil bhead with "Hhn Hhp") as "Hlru".
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.binit + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== loop setup: s1 := &buf[0], s2 := a5, s3 := a4, s4 := &"buffer" ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.binit + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 21 : mword 20)
              T4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_3c with "Htext"). }
    iIntros (CID21 Hs21) "Hcg Hpc".
    set (T5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.binit + 0x3c) : mword 64) (auipc_off (mword_of_int 21 : mword 20)))]> T4).
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.binit + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x40)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1780 : mword 12)
              T5 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_40 with "Htext"). }
    iIntros (CID22 Hs22) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (T5 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1780 : mword 12)))]> T5).
    assert (HT6s1 : T6 !!! Regidx (mword_of_int 9 : mword 5) = bnode 0).
    { rewrite /T6 upd_eq. rewrite /T5 upd_eq.
      unfold bnode, acur, buf_base, buf_stride, KernelSyms.bcache.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HT6a5 : T6 !!! Regidx (mword_of_int 15 : mword 5) = hbase).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [exact HT4a5 | vm_compute; discriminate]. }
    assert (HT6a4 : T6 !!! Regidx (mword_of_int 14 : mword 5) = bhead).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [exact HT4a4 | vm_compute; discriminate]. }
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.binit + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 c.mv s2,a5 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.binit + 0x44)) s2i (mword_of_int 15 : mword 5)
              T6 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_44 with "Htext"). }
    iIntros (CID23 Hs23) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T7 := <[Regidx s2i := regval_into_reg (add_vec zero_reg (T6 !!! Regidx (mword_of_int 15 : mword 5)))]> T6).
    assert (HT7s2 : T7 !!! Regidx s2i = hbase).
    { rewrite /T7 upd_eq. rewrite HT6a5. apply add_vec_zero_l. }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.binit + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* +0x46 c.mv s3,a4 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.binit + 0x46)) s3i (mword_of_int 14 : mword 5)
              T7 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_46 with "Htext"). }
    iIntros (CID24 Hs24) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T8 := <[Regidx s3i := regval_into_reg (add_vec zero_reg (T7 !!! Regidx (mword_of_int 14 : mword 5)))]> T7).
    assert (HT7a4 : T7 !!! Regidx (mword_of_int 14 : mword 5) = bhead)
      by (rewrite /T7 upd_ne; [exact HT6a4 | vm_compute; discriminate]).
    assert (HT8s3 : T8 !!! Regidx s3i = bhead).
    { rewrite /T8 upd_eq. rewrite HT7a4. apply add_vec_zero_l. }
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.binit + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 auipc s4,0x5 / +0x4c addi s4,s4,-1888 : s4 := &"buffer" *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.binit + 0x48)) s4i (mword_of_int 5 : mword 20)
              T8 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_48 with "Htext"). }
    iIntros (CID25 Hs25) "Hcg Hpc".
    set (T9 := <[Regidx s4i := regval_into_reg (add_vec (mword_of_int (KernelSyms.binit + 0x48) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> T8).
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.binit + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x4c)) s4i s4i (mword_of_int 2184 : mword 12)
              T9 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bii_4c with "Htext"). }
    iIntros (CID26 Hs26) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (TA := <[Regidx s4i := regval_into_reg (add_vec (T9 !!! Regidx s4i) (sign_extend' 64 (mword_of_int 2184 : mword 12)))]> T9).
    assert (HTAs4 : TA !!! Regidx s4i = name_buffer).
    { rewrite /TA upd_eq. rewrite /T9 upd_eq. unfold name_buffer, buffer_name_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HTAs1 : TA !!! Regidx (mword_of_int 9 : mword 5) = bnode 0).
    { rewrite /TA upd_ne; [| vm_compute; discriminate].
      rewrite /T9 upd_ne; [| vm_compute; discriminate].
      rewrite /T8 upd_ne; [| vm_compute; discriminate].
      rewrite /T7 upd_ne; [exact HT6s1 | vm_compute; discriminate]. }
    assert (HTAs2 : TA !!! Regidx s2i = hbase).
    { rewrite /TA upd_ne; [| vm_compute; discriminate].
      rewrite /T9 upd_ne; [| vm_compute; discriminate].
      rewrite /T8 upd_ne; [exact HT7s2 | vm_compute; discriminate]. }
    assert (HTAs3 : TA !!! Regidx s3i = bhead).
    { rewrite /TA upd_ne; [| vm_compute; discriminate].
      rewrite /T9 upd_ne; [exact HT8s3 | vm_compute; discriminate]. }
    assert (HTAsp : TA !!! Regidx csp_rs1 = spr).
    { rewrite /TA upd_ne; [| vm_compute; discriminate].
      rewrite /T9 upd_ne; [| vm_compute; discriminate].
      rewrite /T8 upd_ne; [| vm_compute; discriminate].
      rewrite /T7 upd_ne; [| vm_compute; discriminate].
      rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact Hilsp | vm_compute; discriminate]. }
    assert (HTAcs : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> s4i -> c <> csp_rs1 ->
              TA !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 N20 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na4.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na5.
      rewrite /TA upd_ne; [| congruence].
      rewrite /T9 upd_ne; [| congruence].
      rewrite /T8 upd_ne; [| congruence].
      rewrite /T7 upd_ne; [| congruence].
      rewrite /T6 upd_ne; [| congruence].
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hilcs'; assumption. }
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.binit + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* fold the lock's returned cells into the shape the loop hands on --
       [wp_next]-wrapped: the ORIGINAL "Hcont" (wp_binit_sconf's own) is
       generic in [b] and its wp_next stays deferred until the loop's exit
       arm resolves it (ProofIinit.wp_iinit_sconf's "Hpost" is the worked
       example for this exact shape). *)
    iAssert (wp_next (CID0 := CID) b pcur (fun (CID' : CpuId) =>
              ∀ mr,
              sie_cap_gpr KT1 mr K b pcur -∗ pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
              ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
              bcache_lru bhead (blist 0 NBUF) -∗
              WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hlock Hcpu]" as "Hpost".
    { iIntros (CID' Hs' mr) "Hcg Hpc %Hcs Hfresh Hlru".
      iSpecialize ("Hcont" $! CID' with "[%]"); [exact Hs'|].
      iApply ("Hcont" $! mr with "Hcg Hpc [//] Hlock Hlnm Hcpu Hfresh Hlru"). }
    (* the loop-setup instructions have each moved the hart; re-anchor
       [Hpost] to the loop's own entry hart [CID26] before entering it. *)
    assert (Hshift0 : b = false \/ pcur = zero_reg -> (CID26 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift0 with "Hpost") as "Hpost".
    (* ================================================================= *)
    (* THE LOOP.  Fuel induction on the number of buffers left.  [CID0]   *)
    (* rides the SAME [forall] as the other per-iteration state so         *)
    (* [iInduction] auto-generalizes it (the "decomposed proof" recipe --  *)
    (* worked example: ProofFreerange.wp_freerange_sconf's "Hloop").       *)
    (* ================================================================= *)
    iAssert (∀ (fuel : nat) `(CID0 : CpuId) (j : nat) (M : regfile) (l L : list (mword 64)),
      ⌜(NBUF - j <= fuel)%nat⌝ -∗
      ⌜(j < NBUF)%nat⌝ -∗
      ⌜ L = (blist j (NBUF - j) ++ l)%list ⌝ -∗
      ⌜ M !!! Regidx (mword_of_int 9 : mword 5) = bnode j
        /\ M !!! Regidx s2i = hbase
        /\ M !!! Regidx s3i = bhead
        /\ M !!! Regidx s4i = name_buffer
        /\ M !!! Regidx csp_rs1 = spr
        /\ (forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> s4i -> c <> csp_rs1 ->
              M !!! Regidx c = m !!! Regidx c) ⌝ -∗
      sie_cap_gpr KT1 M (K - 6) b pcur -∗
      pc_is (mword_of_int (KernelSyms.binit + 0x50)) -∗
      ([∗ list] k ∈ seq 0 j, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
      ([∗ list] k ∈ seq j (NBUF - j), sl_raw (buf_lock (bnode k))) -∗
      ([∗ list] k ∈ seq j (NBUF - j), blink_raw (bnode k)) -∗
      bcache_lru bhead l -∗
      (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
      (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
      (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
      (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx s2i : mword 64) -∗
      (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx s3i : mword 64) -∗
      (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx s4i : mword 64) -∗
      wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
        ∀ mr, sie_cap_gpr KT1 mr K b pcur -∗ pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
        ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
        bcache_lru bhead L -∗
        WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang))%I
      with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CID0 j M l L) "%Hlen %Hj %HL %Hinv Hcg Hpc Hdone Hraw Hlnk Hlru Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hpost".
        exfalso. lia. }
      iIntros (CID0 j M l L) "%Hlen %Hj %HL %Hinv Hcg Hpc Hdone Hraw Hlnk Hlru Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hpost".
      destruct Hinv as (HMs1 & HMs2 & HMs3 & HMs4 & HMsp & HMcs).
      (* peel the head raw sleeplock and link pair off the remaining lists *)
      assert (Hsplit : (NBUF - j)%nat = S (NBUF - S j)) by lia.
      iEval (rewrite Hsplit) in "Hraw". iEval (cbn [seq]) in "Hraw".
      iDestruct "Hraw" as "[Hraw0 Hraw]".
      iEval (rewrite Hsplit) in "Hlnk". iEval (cbn [seq]) in "Hlnk".
      iDestruct "Hlnk" as "[Hlnk0 Hlnk]".
      iDestruct "Hlnk0" as "[Hbp Hbn]".
      iDestruct "Hbp" as (vbp) "Hbp". iDestruct "Hbn" as (vbn) "Hbn".
      (* the four link cells cross into the ctx world for the splice's four
         accesses and cross back for [Hclose] (BcacheInv is RAW) *)
      iDestruct (TsoCtxShim.ctx_word_of_mem with "Hbp") as "Hbp".
      iDestruct (TsoCtxShim.ctx_word_of_mem with "Hbn") as "Hbn".
      iDestruct "Hraw0" as (vlocked vlk vpid vlkname vcpu' vname') "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6p)".
      (* open the list: the head's next cell and the prev cell of whatever it
         points at, plus the wand that closes over the new node *)
      iPoseProof (bcache_lru_splice bhead l with "Hlru") as "(Hhn & Hhp & Hclose)".
      iDestruct (TsoCtxShim.ctx_word_of_mem with "Hhn") as "Hhn".
      iDestruct (TsoCtxShim.ctx_word_of_mem with "Hhp") as "Hhp".
      (* +0x50 ld a5,696(s2) : a5 := bcache.head.next *)
      iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x50)) (mword_of_int 15 : mword 5) s2i (mword_of_int 696 : mword 12)
                M (K - 6)%nat (List.hd bhead l) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hhn]").
      { iApply (bii_50 with "Htext"). }
      { iEval (rgne). iEval (rewrite HMs2 hbase_next). iExact "Hhn". }
      iIntros (CIDm1 Hsm1) "Hcg Hpc Hhn".
      iEval (rgne) in "Hhn". iEval (rewrite HMs2 hbase_next) in "Hhn".
      set (M1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (List.hd bhead l)]> M).
      assert (HM1a5 : M1 !!! Regidx (mword_of_int 15 : mword 5) = List.hd bhead l)
        by (rewrite /M1 upd_eq; reflexivity).
      assert (HM1s1 : M1 !!! Regidx (mword_of_int 9 : mword 5) = bnode j)
        by (rewrite /M1 upd_ne; [exact HMs1 | vm_compute; discriminate]).
      assert (HM1s3 : M1 !!! Regidx s3i = bhead)
        by (rewrite /M1 upd_ne; [exact HMs3 | vm_compute; discriminate]).
      assert (HM1s4 : M1 !!! Regidx s4i = name_buffer)
        by (rewrite /M1 upd_ne; [exact HMs4 | vm_compute; discriminate]).
      assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.binit + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 c.sd a5,80(s1) : b->next := bcache.head.next *)
      iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x54)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 80 : mword 12)
                M1 (K - 6)%nat vbn b with "Hcg Hpc [] [Hbn]").
      { iApply (bii_54 with "Htext"). }
      { iEval (rgne). iEval (rewrite HM1s1). iExact "Hbn". }
      iIntros (CIDm2 Hsm2) "Hcg Hpc Hbn".
      iEval (rgne; rgne) in "Hbn". iEval (rewrite HM1s1 HM1a5) in "Hbn".
      assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.binit + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56) in "Hpc".
      (* +0x56 sd s3,72(s1) : b->prev := &bcache.head *)
      iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x56)) s3i (mword_of_int 9 : mword 5) (mword_of_int 72 : mword 12)
                M1 (K - 6)%nat vbp b with "Hcg Hpc [] [Hbp]").
      { iApply (bii_56 with "Htext"). }
      { iEval (rgne). iEval (rewrite HM1s1). iExact "Hbp". }
      iIntros (CIDm3 Hsm3) "Hcg Hpc Hbp".
      iEval (rgne; rgne) in "Hbp". iEval (rewrite HM1s1 HM1s3) in "Hbp".
      assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.binit + 0x56) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5a) in "Hpc".
      (* +0x5a c.mv a1,s4 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.binit + 0x5a)) (mword_of_int 11 : mword 5) s4i
                M1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (bii_5a with "Htext"). }
      iIntros (CIDm4 Hsm4) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (M2 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M1 !!! Regidx s4i))]> M1).
      assert (HM2a1 : M2 !!! Regidx (mword_of_int 11 : mword 5) = name_buffer).
      { rewrite /M2 upd_eq. rewrite HM1s4. apply add_vec_zero_l. }
      assert (HM2s1 : M2 !!! Regidx (mword_of_int 9 : mword 5) = bnode j)
        by (rewrite /M2 upd_ne; [exact HM1s1 | vm_compute; discriminate]).
      assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.binit + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5c) in "Hpc".
      (* +0x5c addi a0,s1,16 : a0 := &b->lock *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x5c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 16 : mword 12)
                M2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (bii_5c with "Htext"). }
      iIntros (CIDm5 Hsm5) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (M3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (M2 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)))]> M2).
      assert (HM3a0 : M3 !!! Regidx (mword_of_int 10 : mword 5) = buf_lock (bnode j)).
      { rewrite /M3 upd_eq. rewrite HM2s1. reflexivity. }
      assert (HM3a1 : M3 !!! Regidx (mword_of_int 11 : mword 5) = name_buffer)
        by (rewrite /M3 upd_ne; [exact HM2a1 | vm_compute; discriminate]).
      assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.binit + 0x5c) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp60) in "Hpc".
      (* +0x60 jal ra,initsleeplock *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.binit + 0x60)) (mword_of_int 1 : mword 5) (mword_of_int 5134 : mword 21)
                M3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (bii_60 with "Htext"). }
      iIntros (CIDm6 Hsm6) "Hcg Hpc".
      set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.binit + 0x60) : mword 64) 4)]> M3).
      assert (Htgtisl : add_vec (mword_of_int (KernelSyms.binit + 0x60) : mword 64) (sign_extend' 64 (mword_of_int 5134 : mword 21)) = mword_of_int KernelSyms.initsleeplock)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtisl) in "Hpc".
      assert (HM4a0 : M4 !!! Regidx (mword_of_int 10 : mword 5) = buf_lock (bnode j))
        by (rewrite /M4 upd_ne; [exact HM3a0 | vm_compute; discriminate]).
      assert (HM4a1 : M4 !!! Regidx (mword_of_int 11 : mword 5) = name_buffer)
        by (rewrite /M4 upd_ne; [exact HM3a1 | vm_compute; discriminate]).
      assert (HM4s1 : M4 !!! Regidx (mword_of_int 9 : mword 5) = bnode j).
      { rewrite /M4 upd_ne; [| vm_compute; discriminate].
        rewrite /M3 upd_ne; [exact HM2s1 | vm_compute; discriminate]. }
      assert (HM4s2 : M4 !!! Regidx s2i = hbase).
      { rewrite /M4 upd_ne; [| vm_compute; discriminate].
        rewrite /M3 upd_ne; [| vm_compute; discriminate].
        rewrite /M2 upd_ne; [| vm_compute; discriminate].
        rewrite /M1 upd_ne; [exact HMs2 | vm_compute; discriminate]. }
      assert (HM4s3 : M4 !!! Regidx s3i = bhead).
      { rewrite /M4 upd_ne; [| vm_compute; discriminate].
        rewrite /M3 upd_ne; [| vm_compute; discriminate].
        rewrite /M2 upd_ne; [exact HM1s3 | vm_compute; discriminate]. }
      assert (HM4s4 : M4 !!! Regidx s4i = name_buffer).
      { rewrite /M4 upd_ne; [| vm_compute; discriminate].
        rewrite /M3 upd_ne; [| vm_compute; discriminate].
        rewrite /M2 upd_ne; [exact HM1s4 | vm_compute; discriminate]. }
      assert (HM4sp : M4 !!! Regidx csp_rs1 = spr).
      { rewrite /M4 upd_ne; [| vm_compute; discriminate].
        rewrite /M3 upd_ne; [| vm_compute; discriminate].
        rewrite /M2 upd_ne; [| vm_compute; discriminate].
        rewrite /M1 upd_ne; [exact HMsp | vm_compute; discriminate]. }
      assert (HM4cs : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> s4i -> c <> csp_rs1 ->
                M4 !!! Regidx c = m !!! Regidx c).
      { intros c Hc N8 N9 N18 N19 N20 Nsp.
        pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
        pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
        pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
        pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na5.
        rewrite /M4 upd_ne; [| congruence].
        rewrite /M3 upd_ne; [| congruence].
        rewrite /M2 upd_ne; [| congruence].
        rewrite /M1 upd_ne; [| congruence].
        apply HMcs; assumption. }
      assert (HM4ra : M4 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.binit + 0x64)).
      { rewrite /M4 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      (* ---- initsleeplock(&b->lock, "buffer") ---- *)
      iApply (Initsleeplock.wp_initsleeplock_sconf M4 "buffer"%string
                vlocked vlk vpid vlkname vcpu' vname' (K - 6) b pcur
                ltac:(lia)
                with "Hcg Htext Hpc Hstr_sl [] [Hf1] [Hf2] [Hf3] [Hf4] [Hf5] [Hf6p]").
      { iEval (rewrite HM4a1). iExact "Hstr_buffer". }
      { iEval (rewrite HM4a0). iExact "Hf1". }
      { iEval (rewrite HM4a0). iExact "Hf2". }
      { iEval (rewrite HM4a0). iExact "Hf3". }
      { iEval (rewrite HM4a0). iExact "Hf4". }
      { iEval (rewrite HM4a0). iExact "Hf5". }
      { iEval (rewrite HM4a0). iExact "Hf6p". }
      iIntros (CIDm7 Hsm7 msl) "Hcg Hpc %Hslcs Hg1 Hg2 Hg3 Hg4 Hg5 Hg6".
      iEval (rewrite HM4a0) in "Hg1". iEval (rewrite HM4a0) in "Hg2".
      iEval (rewrite HM4a0) in "Hg3". iEval (rewrite HM4a0) in "Hg4".
      iEval (rewrite HM4a0) in "Hg5". iEval (rewrite HM4a0) in "Hg6".
      assert (Hpcsl : ret_pc (M4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.binit + 0x64)).
      { rewrite HM4ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpcsl) in "Hpc".
      iAssert (sl_fresh (buf_lock (bnode j)) "buffer"%string) with "[Hg1 Hg2 Hg3 Hg4 Hg5 Hg6]" as "Hfr".
      { rewrite /sl_fresh. iFrame "Hg1 Hg2 Hg3 Hg4 Hg5 Hg6". }
      iAssert ([∗ list] k ∈ seq 0 (S j), sl_fresh (buf_lock (bnode k)) "buffer"%string)%I
        with "[Hdone Hfr]" as "Hdone".
      { rewrite seq_S. rewrite big_sepL_app. iFrame "Hdone".
        rewrite Nat.add_0_l. cbn [seq]. by iFrame "Hfr". }
      pose proof Hslcs as Hslcs_full.
      assert (Hslsp : msl !!! Regidx csp_rs1 = spr)
        by (rewrite (callee_saved_lookup Hslcs_full csp_rs1 ltac:(vm_compute; reflexivity)); exact HM4sp).
      assert (Hsls1 : msl !!! Regidx (mword_of_int 9 : mword 5) = bnode j)
        by (rewrite (callee_saved_lookup Hslcs_full (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)); exact HM4s1).
      assert (Hsls2 : msl !!! Regidx s2i = hbase)
        by (rewrite (callee_saved_lookup Hslcs_full s2i ltac:(vm_compute; reflexivity)); exact HM4s2).
      assert (Hsls3 : msl !!! Regidx s3i = bhead)
        by (rewrite (callee_saved_lookup Hslcs_full s3i ltac:(vm_compute; reflexivity)); exact HM4s3).
      assert (Hsls4 : msl !!! Regidx s4i = name_buffer)
        by (rewrite (callee_saved_lookup Hslcs_full s4i ltac:(vm_compute; reflexivity)); exact HM4s4).
      assert (Hslcs' : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> s4i -> c <> csp_rs1 ->
                msl !!! Regidx c = m !!! Regidx c).
      { intros c Hc N8 N9 N18 N19 N20 Nsp.
        rewrite (callee_saved_lookup Hslcs_full c Hc). apply HM4cs; assumption. }
      (* +0x64 ld a5,696(s2) : re-read bcache.head.next (unchanged) *)
      iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x64)) (mword_of_int 15 : mword 5) s2i (mword_of_int 696 : mword 12)
                msl (K - 6)%nat (List.hd bhead l) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hhn]").
      { iApply (bii_64 with "Htext"). }
      { iEval (rgne). iEval (rewrite Hsls2 hbase_next). iExact "Hhn". }
      iIntros (CIDm8 Hsm8) "Hcg Hpc Hhn".
      iEval (rgne) in "Hhn". iEval (rewrite Hsls2 hbase_next) in "Hhn".
      set (N1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (List.hd bhead l)]> msl).
      assert (HN1a5 : N1 !!! Regidx (mword_of_int 15 : mword 5) = List.hd bhead l)
        by (rewrite /N1 upd_eq; reflexivity).
      assert (HN1s1 : N1 !!! Regidx (mword_of_int 9 : mword 5) = bnode j)
        by (rewrite /N1 upd_ne; [exact Hsls1 | vm_compute; discriminate]).
      assert (HN1s2 : N1 !!! Regidx s2i = hbase)
        by (rewrite /N1 upd_ne; [exact Hsls2 | vm_compute; discriminate]).
      assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.binit + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp68) in "Hpc".
      (* +0x68 c.sd s1,72(a5) : bcache.head.next->prev := b *)
      iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x68)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 72 : mword 12)
                N1 (K - 6)%nat bhead b with "Hcg Hpc [] [Hhp]").
      { iApply (bii_68 with "Htext"). }
      { iEval (rgne). iEval (rewrite HN1a5). iExact "Hhp". }
      iIntros (CIDm9 Hsm9) "Hcg Hpc Hhp".
      iEval (rgne; rgne) in "Hhp". iEval (rewrite HN1a5 HN1s1) in "Hhp".
      assert (Hpp6a : add_vec_int (mword_of_int (KernelSyms.binit + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.binit + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp6a) in "Hpc".
      (* +0x6a sd s1,696(s2) : bcache.head.next := b *)
      iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.binit + 0x6a)) (mword_of_int 9 : mword 5) s2i (mword_of_int 696 : mword 12)
                N1 (K - 6)%nat (List.hd bhead l) b with "Hcg Hpc [] [Hhn]").
      { iApply (bii_6a with "Htext"). }
      { iEval (rgne). iEval (rewrite HN1s2 hbase_next). iExact "Hhn". }
      iIntros (CIDm10 Hsm10) "Hcg Hpc Hhn".
      iEval (rgne; rgne) in "Hhn". iEval (rewrite HN1s2 hbase_next HN1s1) in "Hhn".
      (* the splice is complete: close the list over the new node *)
      iDestruct (TsoCtxShim.ctx_word_to_mem with "Hhn") as "Hhn".
      iDestruct (TsoCtxShim.ctx_word_to_mem with "Hhp") as "Hhp".
      iDestruct (TsoCtxShim.ctx_word_to_mem with "Hbn") as "Hbn".
      iDestruct (TsoCtxShim.ctx_word_to_mem with "Hbp") as "Hbp".
      iPoseProof ("Hclose" $! (bnode j) with "Hhn Hhp Hbn Hbp") as "Hlru".
      assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.binit + 0x6a) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp6e) in "Hpc".
      (* +0x6e addi s1,s1,1112 -- bump the cursor to buffer j+1 *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.binit + 0x6e)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1112 : mword 12)
                N1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (bii_6e with "Htext"). }
      iIntros (CIDm11 Hsm11) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (N2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (N1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1112 : mword 12)))]> N1).
      assert (HN2s1 : N2 !!! Regidx (mword_of_int 9 : mword 5) = bnode (S j)).
      { rewrite /N2 upd_eq. rewrite HN1s1. unfold bnode.
        apply (acur_step buf_base buf_stride j).
        unfold buf_stride. apply bv_eq; vm_compute; reflexivity. }
      assert (HN2s2 : N2 !!! Regidx s2i = hbase)
        by (rewrite /N2 upd_ne; [exact HN1s2 | vm_compute; discriminate]).
      assert (HN2s3 : N2 !!! Regidx s3i = bhead).
      { rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [exact Hsls3 | vm_compute; discriminate]. }
      assert (HN2s4 : N2 !!! Regidx s4i = name_buffer).
      { rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [exact Hsls4 | vm_compute; discriminate]. }
      assert (HN2sp : N2 !!! Regidx csp_rs1 = spr).
      { rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_ne; [exact Hslsp | vm_compute; discriminate]. }
      assert (HN2cs : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> s4i -> c <> csp_rs1 ->
                N2 !!! Regidx c = m !!! Regidx c).
      { intros c Hc N8 N9 N18 N19 N20 Nsp.
        pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na5.
        rewrite /N2 upd_ne; [| congruence].
        rewrite /N1 upd_ne; [| congruence].
        apply Hslcs'; assumption. }
      assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.binit + 0x6e) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp72) in "Hpc".
      (* +0x72 bne s1,s3 -- back edge unless the cursor reached the head *)
      assert (Hcmp : neq_vec (N2 !!! Regidx (mword_of_int 9 : mword 5)) (N2 !!! Regidx s3i)
                     = negb (Nat.eqb (S j) NBUF)).
      { rewrite HN2s1 HN2s3. unfold bhead, bnode.
        apply (acur_neq buf_base buf_stride (S j) NBUF
                 buf_base_nonneg buf_stride_pos buf_end_fits).
        lia. }
      (* [decide], NOT [Nat.eqb_spec]: destructing the reflect would abstract
         [S j =? NBUF] out of [Hcmp] too. *)
      destruct (decide (S j = NBUF)) as [Hend | Hne].
      - (* the last buffer: bne FALLS -> straight into the epilogue *)
        assert (Hfall : neq_vec (N2 !!! Regidx (mword_of_int 9 : mword 5)) (N2 !!! Regidx s3i) = false).
        { rewrite Hcmp. rewrite (proj2 (Nat.eqb_eq (S j) NBUF) Hend). reflexivity. }
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.binit + 0x72)) (mword_of_int 8158 : mword 13) s3i (mword_of_int 9 : mword 5)
                  N2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hfall
                  with "Hcg Hpc []").
        { iApply (bii_72 with "Htext"). }
        iIntros (CIDexit Hsexit) "Hcg Hpc".
        assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.binit + 0x72) : mword 64) 4 = mword_of_int (KernelSyms.binit + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp76) in "Hpc".
        (* both remaining lists are empty, the accumulator is the full one, and
           the list we hold is exactly [L] *)
        assert (Hnone : (NBUF - S j)%nat = 0%nat) by lia.
        iEval (rewrite Hnone) in "Hraw". iEval (cbn [seq]) in "Hraw".
        iEval (rewrite Hnone) in "Hlnk". iEval (cbn [seq]) in "Hlnk".
        iEval (rewrite Hend) in "Hdone".
        assert (HLfin : L = (bnode j :: l)%list).
        { rewrite HL. rewrite Hsplit Hnone. unfold blist. cbn [seq map rev app].
          reflexivity. }
        iEval (rewrite -HLfin) in "Hlru".
        assert (Hshiftexit : b = false \/ pcur = zero_reg -> (CIDexit : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hshiftexit with "Hpost") as "Hpost".
        iApply (biepi (CID0 := CIDexit) m N2 K b pcur ltac:(lia) HN2sp HN2cs
                  with "Htext Hcg Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hc6").
        iIntros (CIDy Hsy mr) "Hcg Hpc %Hcs".
        iSpecialize ("Hpost" $! CIDy with "[%]"); [wp_next_chain|].
        iApply ("Hpost" $! mr with "Hcg Hpc [//] Hdone Hlru").
      - (* more buffers: bne TAKEN -> back edge to +0x50 at cursor S j *)
        assert (Htgt50 : add_vec (mword_of_int (KernelSyms.binit + 0x72) : mword 64) (sign_extend' 64 (mword_of_int 8158 : mword 13)) = mword_of_int (KernelSyms.binit + 0x50))
          by (apply bv_eq; vm_compute; reflexivity).
        assert (Htaken : neq_vec (N2 !!! Regidx (mword_of_int 9 : mword 5)) (N2 !!! Regidx s3i) = true).
        { rewrite Hcmp. rewrite (proj2 (Nat.eqb_neq (S j) NBUF) Hne). reflexivity. }
        iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.binit + 0x72)) (mword_of_int 8158 : mword 13) s3i (mword_of_int 9 : mword 5)
                  N2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Htaken
                  ltac:(rewrite Htgt50; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (bii_72 with "Htext"). }
        iNext. iIntros (CIDtaken Hstaken) "Hcg Hpc".
        iEval (rewrite Htgt50) in "Hpc".
        assert (Hshiftrec : b = false \/ pcur = zero_reg -> (CIDtaken : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hshiftrec with "Hpost") as "Hpost".
        iApply ("IHf" $! CIDtaken (S j) N2 (bnode j :: l)%list L
                  with "[] [] [] [] Hcg Hpc Hdone Hraw Hlnk Hlru Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hpost").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. rewrite HL Hsplit blist_step.
          rewrite <- app_assoc. reflexivity. }
        { iPureIntro. split; [exact HN2s1|]. split; [exact HN2s2|].
          split; [exact HN2s3|]. split; [exact HN2s4|].
          split; [exact HN2sp|]. exact HN2cs. } }
    (* enter the loop at cursor 0 with NBUF units of fuel *)
    iApply ("Hloop" $! NBUF CID26 0%nat TA [] (blist 0 NBUF)
              with "[] [] [] [] Hcg Hpc [] [Hraws] [Hlinks] Hlru Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hpost").
    { iPureIntro. lia. }
    { iPureIntro. unfold NBUF; lia. }
    { iPureIntro. rewrite Nat.sub_0_r. rewrite app_nil_r. reflexivity. }
    { iPureIntro. split; [exact HTAs1|]. split; [exact HTAs2|].
      split; [exact HTAs3|]. split; [exact HTAs4|].
      split; [exact HTAsp|]. exact HTAcs. }
    { cbn [seq]. done. }
    { rewrite Nat.sub_0_r. iExact "Hraws". }
    { rewrite Nat.sub_0_r. iExact "Hlinks". }
  Qed.

End ProofBinit.

End BinitProof.
