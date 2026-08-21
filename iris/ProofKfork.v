(* ProofKfork.v -- the whole-function proof of xv6's kfork (kernel/proc.c),
   over the contract in [SpecKfork.v].

   IN PROGRESS, but ADMIT-FREE and AXIOM-FREE: what is proved here today is
   the bottom of the control flow -- the two straight-line stretches that
   reach the shared epilogue -- and NOT the whole-function theorem, so
   [tools/proof_coverage.py] still reads kfork as unproven and there is no
   [LinkKfork.v].  [ProofKforkParts.v] holds the epilogue itself and the
   resource-level bridges; claude-notes/projects/proc-struct-resources.md
   (S11) has the ordered worklist for the rest.

   THE FUNCTION, block by block, with the register assignment gcc chose:

     s5 = p (the parent, myproc()'s result)   s4 = np (the child)
     s1 = the return value / the parent's &ofile[i] cursor
     s2 = the child's &ofile[i] cursor        s3 = &p->ofile[NOFILE] (= &p->cwd)

     +0x000 .. +0x016   prologue, myproc, allocproc, the "no slot" test
     +0x01a .. +0x02c   s4 := np, uvmcopy(p->pagetable, np->pagetable, p->sz)
     +0x030 .. +0x046   np->sz = p->sz; set up the trapframe copy
     +0x04a .. +0x062   the trapframe copy loop (4 words / iteration, 9 turns)
     +0x066 .. +0x07a   np->trapframe->a0 = 0; the fd cursors; enter the scan
     +0x07c .. +0x08c   THE uvmcopy-FAILURE TAIL (freeproc, release, -1)
     +0x08e .. +0x0a2   the ROTATED filedup scan
     +0x0a4 .. +0x0bc   idup(p->cwd); safestrcpy(np->name, p->name, 16)
     +0x0be .. +0x0f4   pid = np->pid; release; wait_lock; RUNNABLE; release
     +0x0f6 .. +0x0fa   the three lazy reloads
     +0x0fc .. +0x108   THE SHARED EPILOGUE ([ProofKforkParts.kfk_epi])
     +0x10a .. +0x10c   THE allocproc-FAILURE TAIL (-1) *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import ProofKforkParts.
Require Import CodeKfork.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

Section ProofKfork.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* THE FRAME, as every exit sees it.  Slots 4/5/6 (s2/s3/s4) are lazily
     spilled, so which of them holds a saved register and which holds junk
     depends on the path; every exit therefore takes them EXISTENTIALLY and
     the epilogue never reads them.  Slot 8 is the unused padding word. *)
  Definition kfk_frame (sp0 ra0 s00 s10 s50 : mword 64) : iProp Σ :=
    (word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     (∃ w4, word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) w4) ∗
     (∃ w5, word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5) ∗
     (∃ w6, word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6) ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) s50 ∗
     (∃ w8, word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8))%I.

  (* ... AND THE SAME FRAME WITH THE LAZY SLOTS PINNED.                   *)
  (*                                                                      *)
  (* [kfk_frame] is right for the allocproc-failure exit, which reaches the *)
  (* epilogue having written none of s2/s3/s4 -- there is nothing to say    *)
  (* about slots 4/5/6 and the epilogue never reads them.  It is WRONG for  *)
  (* the two uvmcopy-side exits: by then s4 (and on the success path s2 and *)
  (* s3) HAVE been spilled, and the blocks that reload them need to know    *)
  (* WHICH value they will get back -- [ProofKforkB1.kfk_exit_uvmcopy]      *)
  (* wants slot 6 at [m !!! Regidx Rs4], [kfk_tail_succ] wants all three at *)
  (* the caller's s2/s3/s4.  An existential slot cannot supply that, so the *)
  (* two mid-function continuations carry this form and weaken to           *)
  (* [kfk_frame] only at the exit that does not care.                       *)
  Definition kfk_frame_at (sp0 ra0 s00 s10 s50 w4 w5 w6 : mword 64) : iProp Σ :=
    (word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) w4 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) s50 ∗
     (∃ w8, word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8))%I.

  Lemma kfk_frame_at_weaken (sp0 ra0 s00 s10 s50 w4 w5 w6 : mword 64) :
    kfk_frame_at sp0 ra0 s00 s10 s50 w4 w5 w6 -∗ kfk_frame sp0 ra0 s00 s10 s50.
  Proof.
    rewrite /kfk_frame_at /kfk_frame.
    iIntros "(Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7 & Hb8)".
    iFrame "Hb1 Hb2 Hb3 Hb7 Hb8".
    iSplitL "Hb4"; [iExists w4; iExact "Hb4"|].
    iSplitL "Hb5"; [iExists w5; iExact "Hb5"|].
    iExists w6; iExact "Hb6".
  Qed.

  (* The epilogue, restated over [kfk_frame] so the three exits agree on one
     shape.  It is [ProofKforkParts.kfk_epi] with the three lazy slots
     existentially quantified. *)
  Lemma kfk_epi_frame `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s50 rv : mword 64) (p : mword 64) (b : bool) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    Mt !!! Regidx Rs1 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0xfc) : mword 64) -∗
    kfk_frame sp0 ra0 s00 s10 s50 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hs50 Hmtsp Hmts1 Hthr.
    iIntros "Hcg #Htext Hpc (Hb1 & Hb2 & Hb3 & (%w4 & Hb4) & (%w5 & Hb5) &
                             (%w6 & Hb6) & Hb7 & (%w8 & Hb8)) Hcont".
    iApply (kfk_epi m Mt K sp0 ra0 s00 s10 s50 rv w4 w5 w6 w8 p b
              HK Hsp0 Hra0 Hs00 Hs10 Hs50 Hmtsp Hmts1 Hthr
              with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hcont").
  Qed.

  (* =================================================================== *)
  (*  +0x10a: THE allocproc-FAILURE TAIL.                                 *)
  (*                                                                      *)
  (*    c.li s1,-1 ; c.j +0xfc                                            *)
  (*                                                                      *)
  (*  It jumps PAST the three lazy reloads, and that is exactly right:    *)
  (*  neither s2 nor s3 nor s4 has been written on this path, so the      *)
  (*  caller's values are still sitting in the physical registers and     *)
  (*  [callee_saved] for them comes out of [Hthr] untouched.              *)
  (* =================================================================== *)
  Lemma kfk_exit_alloc `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s50 : mword 64) (p : mword 64) (b : bool) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x10a) : mword 64) -∗
    kfk_frame sp0 ra0 s00 s10 s50 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hs50 Hmtsp Hthr.
    iIntros "Hcg #Htext Hpc Hframe Hcont".
    iPoseProof (kfk_10a with "Htext") as "Hi10a".
    iPoseProof (kfk_10c with "Htext") as "Hi10c".
    (* ---- +0x10a: c.li s1,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KF + 0x10a)) Rs1
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              Mt (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi10a").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (T1 := <[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> Mt).
    change (<[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> Mt)
      with T1.
    assert (Hpp10c : add_vec_int (mword_of_int (KF + 0x10a) : mword 64) 2
                     = mword_of_int (KF + 0x10c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10c) in "Hpc".
    (* ---- +0x10c: c.j +0xfc ---- *)
    assert (Htgt : add_vec (mword_of_int (KF + 0x10c) : mword 64)
                     (sign_extend' 64 (sign_extend' 21
                        (concat_vec (mword_of_int 2040 : mword 11) ('b"0"))))
                   = mword_of_int (KF + 0xfc))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KF + 0x10c))
              (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")))
              T1 (K - 8)%nat b
              ltac:(rewrite Htgt; vm_compute; reflexivity)
              with "Hcg Hpc Hi10c").
    iIntros (CID2 Hs2). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgt) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (HT1s1 : T1 !!! Regidx Rs1 = (mword_of_int (-1) : mword 64))
      by (rewrite /T1; apply upd_eq).
    assert (HT1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> T1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns5.
      rewrite /T1 upd_ne; [| regne]. exact (Hthr r Hr Nsp Ns0 Ns1 Ns5). }
    iApply (kfk_epi_frame (CID0 := CID2) m T1 K sp0 ra0 s00 s10 s50
              (mword_of_int (-1) : mword 64) p b
              HK Hsp0 Hra0 Hs00 Hs10 Hs50 HT1sp HT1s1 HT1thr
              with "Hcg Htext Hpc Hframe").
    iIntros (CID3 Hs3 mf) "%Hpost Hcg Hpc".
    iSpecialize ("Hcont" $! CID3 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hpc"). exact Hpost.
  Qed.

  (* =================================================================== *)
  (*  +0xf6 .. +0xfa: THE THREE LAZY RELOADS, on the success path only.   *)
  (*                                                                      *)
  (*    c.ldsp s2,32(sp) ; c.ldsp s3,24(sp) ; c.ldsp s4,16(sp)            *)
  (*                                                                      *)
  (*  and then FALLS INTO the epilogue.  This is the only path that spills *)
  (*  all three, so it is the only one that reloads them; the two failure  *)
  (*  tails jump over this block entirely.                                *)
  (* =================================================================== *)
  Lemma kfk_tail_succ `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s50 rv w8 : mword 64) (p : mword 64) (b : bool) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs5 = s50 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    Mt !!! Regidx Rs1 = rv ->
    (* s2/s3/s4 are NOT among the registers this premise covers: they hold
       the loop's cursors here and come back off the frame below. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0xf6) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) (m !!! Regidx Rs3) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) (m !!! Regidx Rs4) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) s50 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hs50 Hmtsp Hmts1 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hcont".
    iPoseProof (kfk_0f6 with "Htext") as "Hi0f6".
    iPoseProof (kfk_0f8 with "Htext") as "Hi0f8".
    iPoseProof (kfk_0fa with "Htext") as "Hi0fa".
    (* ---- +0xf6: c.ldsp s2,32(sp) ---- *)
    assert (Hpa4 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                   = pa_stk sp0 4) by (rewrite Hmtsp; apply kfk_frm4).
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0xf6)) (mword_of_int 4 : mword 6) Rs2
              Mt (K - 8)%nat (m !!! Regidx Rs2) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0f6 Hb4").
    iIntros (CID1 Hc1) "Hcg Hpc Hb4". iEval (rewrite Hpa4) in "Hb4".
    set (U1 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> Mt).
    assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /U1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hpp0f8 : add_vec_int (mword_of_int (KF + 0xf6) : mword 64) 2
                     = mword_of_int (KF + 0xf8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0f8) in "Hpc".
    (* ---- +0xf8: c.ldsp s3,24(sp) ---- *)
    assert (Hpa5 : add_vec (U1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk sp0 5) by (rewrite HU1sp; apply kfk_frm5).
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0xf8)) (mword_of_int 3 : mword 6) Rs3
              U1 (K - 8)%nat (m !!! Regidx Rs3) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0f8 Hb5").
    iIntros (CID2 Hc2) "Hcg Hpc Hb5". iEval (rewrite Hpa5) in "Hb5".
    set (U2 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> U1).
    assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /U2 upd_ne; [exact HU1sp | vm_compute; discriminate]).
    assert (Hpp0fa : add_vec_int (mword_of_int (KF + 0xf8) : mword 64) 2
                     = mword_of_int (KF + 0xfa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0fa) in "Hpc".
    (* ---- +0xfa: c.ldsp s4,16(sp) ---- *)
    assert (Hpa6 : add_vec (U2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite HU2sp; apply kfk_frm6).
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int (KF + 0xfa)) (mword_of_int 2 : mword 6) Rs4
              U2 (K - 8)%nat (m !!! Regidx Rs4) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0fa Hb6").
    iIntros (CID3 Hc3) "Hcg Hpc Hb6". iEval (rewrite Hpa6) in "Hb6".
    set (U3 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> U2).
    assert (Hpp0fc : add_vec_int (mword_of_int (KF + 0xfa) : mword 64) 2
                     = mword_of_int (KF + 0xfc)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0fc) in "Hpc".
    (* ---- fall into the epilogue ---- *)
    assert (HU3sp : U3 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /U3 upd_ne; [exact HU2sp | vm_compute; discriminate]).
    assert (HU3s1 : U3 !!! Regidx Rs1 = rv).
    { rewrite /U3 upd_ne; [| vm_compute; discriminate].
      rewrite /U2 upd_ne; [| vm_compute; discriminate].
      rewrite /U1 upd_ne; [exact Hmts1 | vm_compute; discriminate]. }
    assert (HU3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs5 -> U3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns5.
      destruct (decide (r = Rs4)) as [-> | N4]; [rewrite /U3; apply upd_eq |].
      rewrite /U3 upd_ne; [| congruence].
      destruct (decide (r = Rs3)) as [-> | N3]; [rewrite /U2; apply upd_eq |].
      rewrite /U2 upd_ne; [| congruence].
      destruct (decide (r = Rs2)) as [-> | N2]; [rewrite /U1; apply upd_eq |].
      rewrite /U1 upd_ne; [| congruence].
      exact (Hthr r Hr Nsp Ns0 Ns1 N2 N3 N4 Ns5). }
    iApply (kfk_epi (CID0 := CID3) m U3 K sp0 ra0 s00 s10 s50 rv
              (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4) w8 p b
              HK Hsp0 Hra0 Hs00 Hs10 Hs50 HU3sp HU3s1 HU3thr
              with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8").
    iIntros (CID4 Hc4 mf) "%Hpost Hcg Hpc".
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hpc"). exact Hpost.
  Qed.

End ProofKfork.
