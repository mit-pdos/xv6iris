(* ProofFilealloc.v -- filealloc over the SIE-agnostic sconf world.

     acquire(&ftable.lock)
       -> scan ftable.file[0..NFILE) for the first entry with ref == 0
       -> FOUND: f->ref = 1; release; return f
       -> FULL : release; return 0

   Two things carry the proof.

   The SCAN is a fuel induction on the number of entries left (NOT an iLob:
   the loop is bounded).  Its invariant is one line of ghost state -- every
   entry the cursor has passed is in the authority's domain -- and the branch
   at each step is decided by [FileInv]'s two [fref_word_{zero,nonzero}]
   lemmas, which is exactly where "the physical [ref] test and the ghost state
   agree" is discharged.  The cursor itself is [ArrCursor.acur] at stride 40,
   so the [addi s1,s1,40] bump is [acur_step] and the [bne s1,a4] test is
   [acur_neq]; no bitvector arithmetic appears in the loop.

   The scan only READS entries, and only their [ref] cells, so nothing about
   the table changes until the found entry is taken: the NFILE-way big-sep is
   borrowed and returned unchanged by [ftable_slots_acc] at every step, and
   the authority map is literally loop-invariant.  That is the mechanized form
   of "filealloc may look at every core's files because [ref] lives under the
   lock and nothing else does".

   The two arms rejoin at +0x52, so the epilogue is factored as an [iAssert]ed
   continuation ([Hepi]) taken before the split -- it owns the four frame
   slots and the caller's [Hcont], and each arm hands it the returned register
   and the matching [filealloc_post] disjunct.

   EXPLICIT-CPUID NOTE: from acquire's return through both arms' [release]
   calls, execution runs at the LITERAL [false] SIE state acquire hands back
   (the cursor setup, the whole scan, and the found/full bodies up to their
   own [release] call), so every step there is [rewrite wp_next_off] with no
   hart threading.  [Hepi] is entered AFTER release, at whichever hart
   release's own (generic) exit index lands on -- since it is applied from
   TWO different post-release call sites, it is asserted as a properly
   hart-GENERIC proposition (an explicit [∀ CID0, …], the [iAssert] analogue
   of "a helper lemma needs its own fresh binder", worked example
   ProofConsputc.wp_consputc_epi) rather than pinned to the section's own
   ambient [CID].  Both the pre-acquire prologue and [Hepi]'s own six-step
   tail need ONE [cpu_own_transport] each; release's derived exit index is
   absorbed by [sie_b_agree]'s [Houtb], read once at function entry, exactly
   as in ProofFiledup.v / ProofBunpin.v. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import ArrCursor.
Require Import FdSlots FileInv CodeFilealloc.
Require Import WpLock.
Require Import WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SpecAcquire SpecRelease.
Require Import SpecFilealloc.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Module FileallocProof (Acquire : ACQUIRE) (Release : RELEASE) : FILEALLOC.

Section ProofFilealloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* register indices, named once *)
  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rtp  := (mword_of_int 4 : mword 5).

  (* Peeling an [upd_ne] over an abstract callee-saved index [c]: either the
     written register is [c]-excluded by an explicit hypothesis (congruence),
     or it is not callee-saved at all, and then [is_cs_idx c = true] separates
     them.  a0/a4/a5/ra are the latter kind. *)
  Local Ltac regne := reg_ne_side.

  (* [b] (from [sie_cap_gpr]'s arm) and [n],[eb] (from [cpu_own]'s count) are
     two independent presentations of the same SIE state; see
     ProofFiledup.v's identical helper for the full comment. *)
  Local Lemma sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool) (p : mword 64) (C : iProp Σ) (lks : gset nat) :
    sie_cap_gpr m K0 b p -∗ cpu_own n eb p C b lks -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "[%Hb _]". destruct Hb as [-> ->]. done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[[_ Hint] _]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm) & _)".
      iDestruct (ghost_var_agree with "Harm Hint") as %Heq.
      destruct eb; [ exfalso | done ].
      apply (f_equal (@bv_unsigned _)) in Heq. vm_compute in Heq. discriminate.
  Qed.

  (* ---- THE BLOCK CONTINUATIONS, NAMED (RULE ONE, claude-notes/
     optimization.md): [wp_filealloc_sconf] states two large [iAssert]s
     ([Hepi], the shared epilogue, and [Hloop], the fuel-indexed scan) whose
     bodies are spelled out inline; every proofmode step in the ~600-line
     proof that follows re-embeds them, so naming the bodies here turns each
     live hypothesis into a small constant application in the context.

     Only [Hepi] folds.  [fa_epi_body] stays TRANSPARENT ON PURPOSE (never
     [Typeclasses Opaque]) so the later [iApply ("Hepi" $! ..)] use sites
     keep unifying through it without any extra [rewrite /..], and the
     [{ .. }] proof script at its original [iAssert] site is UNCHANGED
     byte-for-byte -- only the stated type moved out.

     [Hloop] (the scan) does NOT fold, matching ProofPiperead.v's [WXP]/
     [CLOOP] negative (lines ~432-457 there): the whole scan runs at the
     PINNED index [false] with no [wp_next] wrapper (file header), and a
     [Definition fa_loop_body ... (fuel j : nat) : iProp Σ := (∀ M, ...)%I]
     folded the same way as [fa_epi_body] MEASURED broke the first leaf
     instruction lemma inside the induction: [iApply (wp_clw_s_sconf ...
     with "Hcg Hpc Hi26 Hcell")] failed at the very first [iInduction]
     branch with

       Error: Tactic failure: iSpecialize: cannot instantiate
       (sie_cap_gpr M (trap_res b + (K - 4)) false ?p -∗ ... -∗
        wp_next false ?p (λ CID0 : CpuId, ...) -∗ WP Loop)%I
       with (sie_cap_gpr M (trap_res b + (K - 4)) false p).

     -- the leaf's implicit process pointer [p] no longer unifies once it
     is reached only through the folded body instead of appearing unfolded
     in the surrounding statement, exactly [ProofPiperead]'s
     "cannot instantiate ... false ?p" signature.  Per the file's fallback
     rule, [Hloop] is left as its original inline [iAssert] below. *)

  (* [fa_epi_body]: the shared epilogue at [+0x52..+0x5c].  [CID0] is an
     explicit trailing parameter (mirroring ProofDirlookup's [dl_tail_body]
     / its [CIDt]) rather than folded inside the body, because [Hepi] is a
     genuinely hart-GENERIC proposition -- entered from TWO different
     post-release call sites at two different concrete harts, so there is
     no ambient [CID0] to fix it at (worked example
     ProofConsputc.wp_consputc_epi; file header for the full reason [Hepi]
     is stated this way and takes its own [wp_next]-shaped continuation
     rather than invoking [Hcont] directly). *)
  Definition fa_epi_body
      (γf : gname) (m : regfile) (spr : mword 64) (K : nat) (b : bool)
      (p : mword 64) (C : iProp Σ) (n : nat) (eb : bool) (ret_tgt : mword 64)
      (CID0 : CpuId) (lks : gset nat) : iProp Σ :=
    (∀ (mj : regfile) (res : mword 64),
        ⌜ mj !!! Regidx csp_rs1 = spr
          /\ mj !!! Regidx Rs1 = res
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 9 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                mj !!! Regidx c = m !!! Regidx c) ⌝ -∗
        sie_cap_gpr (CID := CID0) mj (K - 4)%nat b p -∗
        pc_is (CID := CID0) (mword_of_int (KernelSyms.filealloc + 0x52)) -∗
        cpu_own (CID := CID0) n eb p C b lks -∗
        filealloc_post γf res -∗
        wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
          ∀ mfin,
          sie_cap_gpr mfin K b p -∗
          cpu_own n eb p C b lks -∗
          pc_is ret_tgt -∗
          ⌜ callee_saved m mfin ⌝ -∗
          filealloc_post γf (mfin !!! Regidx Ra0) -∗
          WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang))%I.

  Lemma wp_filealloc_sconf
      (γl γf : gname) (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool) (lks : gset nat)
    : wp_filealloc_sconf_body γl γf m n eb p C K b lks.
  Proof.
    cbv beta delta [wp_filealloc_sconf_body].
    intros pcE ret_tgt HK HnZ.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hlock #Hpanic Hfdslot Hcont".
    iDestruct (sie_b_agree m n K eb b p C lks with "Hcg Hcnt") as %Houtb.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (fai_00 with "Htext") as "Hi00".
    iPoseProof (fai_02 with "Htext") as "Hi02".
    iPoseProof (fai_04 with "Htext") as "Hi04".
    iPoseProof (fai_06 with "Htext") as "Hi06".
    iPoseProof (fai_08 with "Htext") as "Hi08".
    iPoseProof (fai_0a with "Htext") as "Hi0a".
    iPoseProof (fai_0e with "Htext") as "Hi0e".
    iPoseProof (fai_12 with "Htext") as "Hi12".
    (* ===== PROLOGUE (generic [b]): 4-slot frame + ra/s0/s1 saves + s0 := sp+32 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.filealloc + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 Hr24").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.filealloc + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 Hr16").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.filealloc + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 Hr8").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.filealloc + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a auipc a0,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.filealloc + 0x0a)) Ra0 (mword_of_int 0x1e : mword 20)
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.filealloc + 0x0a) : mword 64)
                     (auipc_off (mword_of_int 0x1e : mword 20)))]> R2).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x0a) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e addi a0,a0,1182  (a0 := &ftable) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.filealloc + 0x0e)) Ra0 Ra0 (mword_of_int 0x488 : mword 12)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1160 : mword 12)))]> R3).
    assert (HR4a0 : R4 !!! Regidx Ra0 = ftable_addr).
    { rewrite /R4 upd_eq /R3 upd_eq. rewrite /ftable_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.filealloc + 0x12)) Rra (mword_of_int 0x1fcb7a : mword 21)
              R4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi12").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.filealloc + 0x12) : mword 64) 4)]> R4).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.filealloc + 0x12) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1fcb7a : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx Ra0 = ftable_addr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate]. exact HR4a0. }
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.filealloc + 0x12) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    (* [Hcnt] was introduced at the entry hart; eight plain instructions have
       moved us to CID8. *)
    iDestruct (cpu_own_transport CID CID8 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf γl "ftable"%string (ftable_res γf) mA
              n eb p C (K - 4)%nat b
              HnZ ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlock] Hpanic").
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc16 : ret_pc (mA !!! Regidx Rra) = mword_of_int (KernelSyms.filealloc + 0x16)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc16) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    (* the ftable's ghost state, opened for the whole critical section *)
    iDestruct "HRres" as (Mg) "(Hauth & Hfdauth & %Hdom & Hslots)".
    iPoseProof (fai_16 with "Htext") as "Hi16".
    iPoseProof (fai_1a with "Htext") as "Hi1a".
    iPoseProof (fai_1e with "Htext") as "Hi1e".
    iPoseProof (fai_22 with "Htext") as "Hi22".
    (* ===== the critical section (literal [false], no hart threading), ===== *)
    (* ===== s1 := &ftable.file[0] ; a4 := one past the last entry     ===== *)
    (* +0x16 auipc s1,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.filealloc + 0x16)) Rs1 (mword_of_int 0x1e : mword 20)
              macq (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R6 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.filealloc + 0x16) : mword 64)
                     (auipc_off (mword_of_int 0x1e : mword 20)))]> macq).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a addi s1,s1,1194 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.filealloc + 0x1a)) Rs1 Rs1 (mword_of_int 0x494 : mword 12)
              R6 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R7 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (R6 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 1172 : mword 12)))]> R6).
    assert (HR7s1 : R7 !!! Regidx Rs1 = fnode 0).
    { rewrite /R7 upd_eq /R6 upd_eq. rewrite /fnode /acur /file_base /file_stride.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e auipc a4,0x1f *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.filealloc + 0x1e)) Ra4 (mword_of_int 0x1f : mword 20)
              R7 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R8 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.filealloc + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 0x1f : mword 20)))]> R7).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 addi a4,a4,1090 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.filealloc + 0x22)) Ra4 Ra4 (mword_of_int 0x42c : mword 12)
              R8 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R9 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (R8 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 1068 : mword 12)))]> R8).
    assert (HR9a4 : R9 !!! Regidx Ra4 = fnode NFILE).
    { rewrite /R9 upd_eq /R8 upd_eq. rewrite /fnode /acur /file_base /file_stride /NFILE.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HR9s1 : R9 !!! Regidx Rs1 = fnode 0).
    { rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate]. exact HR7s1. }
    assert (HR9thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                       R9 !!! Regidx c = macq !!! Regidx c).
    { intros c Hcs Hne.
      rewrite /R9 upd_ne; [| regne].
      rewrite /R8 upd_ne; [| regne].
      rewrite /R7 upd_ne; [| regne].
      rewrite /R6 upd_ne; [reflexivity | regne]. }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* ================================================================= *)
    (*  THE EPILOGUE (+0x52 .. +0x5c), entered AFTER release at whichever   *)
    (*  hart release's own [wp_next] lands on -- hence a properly hart-     *)
    (*  GENERIC assertion (fresh [CID0]), applied from both arms below.     *)
    (* ================================================================= *)
    iPoseProof (fai_52 with "Htext") as "Hi52".
    iPoseProof (fai_54 with "Htext") as "Hi54".
    iPoseProof (fai_56 with "Htext") as "Hi56".
    iPoseProof (fai_58 with "Htext") as "Hi58".
    iPoseProof (fai_5a with "Htext") as "Hi5a".
    iPoseProof (fai_5c with "Htext") as "Hi5c".
    (* [Hepi] does NOT invoke the OUTER [Hcont] itself: [CID0] is a truly
       arbitrary hart from [Hepi]'s own point of view (it is proved once,
       generically), so [wp_next_chain] could only ever relate its own
       six internal steps back to [CID0] -- never all the way back to the
       function's entry hart, which [Hepi] has no way to know about.  So
       [Hepi] instead takes its OWN wp_next-shaped continuation as an
       argument (mirroring ProofConsputc.wp_consputc_epi exactly) and
       closes THAT via [wp_next_chain] relative to [CID0]; the CALLER,
       at each concrete call site, is the one who both knows the full
       chain back to entry and holds the real [Hcont]. *)
    iAssert (∀ (CID0 : CpuId), fa_epi_body γf m spr K b p C n eb ret_tgt CID0 lks)%I
      with "[Hr24 Hr16 Hr8 Hg4]" as "Hepi".
    { iIntros (CID0 mj res) "(%Hjsp & %Hjs1 & %Hjthr) Hcg Hpc Hcnt Hpost Kont".
      (* +0x52 c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.filealloc + 0x52)) Ra0 Rs1
                mj (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi52").
      iIntros (CIDe1 Hse1) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (P1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mj !!! Regidx Rs1))]> mj).
      assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
        by (rewrite /P1 upd_ne; [exact Hjsp | vm_compute; discriminate]).
      assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
      iEval (rewrite HspR1) in "Hr8".  iEval (rewrite HspR1) in "Hg4".
      (* +0x54 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.filealloc + 0x54)) (mword_of_int 3 : mword 6) Rra
                P1 (K - 4)%nat (R1 !!! Regidx Rra) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi54 [Hr24]").
      { iEval (rewrite HP1sp). iExact "Hr24". }
      iIntros (CIDe2 Hse2) "Hcg Hpc Hr24".
      iEval (rewrite HP1sp) in "Hr24".
      set (P2 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> P1).
      assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
        by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
      assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56) in "Hpc".
      (* +0x56 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.filealloc + 0x56)) (mword_of_int 2 : mword 6) Rs0
                P2 (K - 4)%nat (R1 !!! Regidx Rs0) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi56 [Hr16]").
      { iEval (rewrite HP2sp). iExact "Hr16". }
      iIntros (CIDe3 Hse3) "Hcg Hpc Hr16".
      iEval (rewrite HP2sp) in "Hr16".
      set (P3 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P2).
      assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
        by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
      assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x58))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp58) in "Hpc".
      (* +0x58 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.filealloc + 0x58)) (mword_of_int 1 : mword 6) Rs1
                P3 (K - 4)%nat (R1 !!! Regidx Rs1) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi58 [Hr8]").
      { iEval (rewrite HP3sp). iExact "Hr8". }
      iIntros (CIDe4 Hse4) "Hcg Hpc Hr8".
      iEval (rewrite HP3sp) in "Hr8".
      set (P4 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P3).
      assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
        by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
      assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x5a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5a) in "Hpc".
      (* +0x5a c.addi16sp sp,32 -- the frame trade back *)
      set (P5 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (P4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
      assert (Hwv : add_vec (P4 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HP4sp. unfold spr, sp0. apply frame_cancel_32. }
      assert (Hpop : P4 !!! Regidx csp_rs1
                     = pa_stk (add_vec (P4 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HP4sp. unfold spr, sp0, pa_stk, add_vec_int.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
        iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
        iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
        iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.filealloc + 0x5a)) (mword_of_int 2 : mword 6)
                P4 (K - 4)%nat 4 b Hpop with "Hcg Hpc Hi5a Hframe4").
      iIntros (CIDe5 Hse5) "Hcg Hpc".
      assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (P4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4) with P5.
      assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x5c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5c) in "Hpc".
      (* +0x5c c.ret *)
      assert (HP5ra : P5 !!! Regidx Rra = m !!! Regidx Rra).
      { rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /P2 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HP5a0 : P5 !!! Regidx Ra0 = res).
      { rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /P2 upd_ne; [| vm_compute; discriminate].
        rewrite /P1 upd_eq. rewrite Hjs1. apply add_vec_zero_l. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.filealloc + 0x5c)) Rra P5 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi5c").
      iIntros (CIDe6 Hse6) "Hcg Hpc".
      assert (Hretf : ret_pc (P5 !!! Regidx Rra) = ret_tgt) by (rewrite HP5ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      (* [cpu_own] was handed to us at [CID0]; six more plain instructions
         have moved us to [CIDe6]. *)
      iDestruct (cpu_own_transport CID0 CIDe6 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Kont" $! CIDe6 with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Kont" $! P5 with "Hcg Hcnt Hpc [%] [Hpost]").
      2:{ rewrite HP5a0. iExact "Hpost". }
      { (* callee_saved m P5 *)
        assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
                  c <> mword_of_int 1 -> c <> mword_of_int 10 ->
                  P5 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N1 N10.
          rewrite /P5 upd_ne; [| regne].
          rewrite /P4 upd_ne; [| regne].
          rewrite /P3 upd_ne; [| regne].
          rewrite /P2 upd_ne; [| regne].
          rewrite /P1 upd_ne; [| regne].
          apply Hjthr; assumption. }
        unfold callee_saved.
        assert (Hc2 : P5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
        { rewrite /P5 upd_eq. rewrite HP4sp. unfold regval_into_reg, spr, sp0.
          apply frame_cancel_32. }
        assert (Hc8 : P5 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
        { rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        assert (Hc9 : P5 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
        { rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        repeat split;
          first [ exact Hc2 | exact Hc8 | exact Hc9
                | apply Hthread; vm_compute; first [reflexivity | discriminate] ]. } }
    (* ================================================================= *)
    (*  THE SCAN.  Fuel induction on the number of entries left, entirely  *)
    (*  at the LITERAL [false] SIE state -- no hart threading anywhere.    *)
    (* ================================================================= *)
    iPoseProof (fai_26 with "Htext") as "Hi26".
    iPoseProof (fai_28 with "Htext") as "Hi28".
    iPoseProof (fai_2a with "Htext") as "Hi2a".
    iPoseProof (fai_2e with "Htext") as "Hi2e".
    set (Cfound := (∀ (i : nat) (Mi : regfile),
        ⌜ (i < NFILE)%nat /\ Mg !! i = None
          /\ Mi !!! Regidx Rs1 = fnode i
          /\ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                Mi !!! Regidx c = macq !!! Regidx c) ⌝ -∗
        sie_cap_gpr Mi (trap_res b + (K - 4))%nat false p -∗
        pc_is (mword_of_int (KernelSyms.filealloc + 0x42)) -∗
        ([∗ list] k ∈ seq 0 NFILE, fslot γf Mg k) -∗
        WP (Loop : expr riscv_lang))%I).
    set (Cfull := (∀ (Mf : regfile),
        ⌜ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
             Mf !!! Regidx c = macq !!! Regidx c) ⌝ -∗
        sie_cap_gpr Mf (trap_res b + (K - 4))%nat false p -∗
        pc_is (mword_of_int (KernelSyms.filealloc + 0x32)) -∗
        ([∗ list] k ∈ seq 0 NFILE, fslot γf Mg k) -∗
        WP (Loop : expr riscv_lang))%I).
    iAssert (∀ (fuel j : nat) (M : regfile),
        ⌜ (NFILE - j <= fuel)%nat ⌝ -∗
        ⌜ (j < NFILE)%nat ⌝ -∗
        ⌜ M !!! Regidx Rs1 = fnode j
          /\ M !!! Regidx Ra4 = fnode NFILE
          /\ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                M !!! Regidx c = macq !!! Regidx c) ⌝ -∗
        sie_cap_gpr M (trap_res b + (K - 4))%nat false p -∗
        pc_is (mword_of_int (KernelSyms.filealloc + 0x26)) -∗
        ([∗ list] k ∈ seq 0 NFILE, fslot γf Mg k) -∗
        (* the two exits are conjoined, NOT separated: exactly one is taken,
           so they must SHARE the ambient resources (lock token, cpu_own,
           the authority, the epilogue) rather than split them. *)
        (Cfound ∧ Cfull) -∗
        WP (Loop : expr riscv_lang))%I
      with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IH] "IH";
        iIntros (j M) "%Hfuel %Hj (%Hcurs1 & %Ha4 & %Hthr) Hcg Hpc Hslots Hexit".
      { exfalso. lia. }
      (* --- +0x26 c.lw a5,4(s1) : read this entry's ref field --- *)
      iDestruct (ftable_slots_acc γf Mg j ltac:(lia) with "Hslots") as "[Hslot Hback]".
      assert (Hpa : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                    = a_fref j).
      { rewrite (rget_ne M Rs1 ltac:(vm_compute; discriminate)) Hcurs1. reflexivity. }
      destruct (Mg !! j) as [[qt cnt]|] eqn:HMj.
      - (* ---- entry IS in use: ref reads nonzero, keep scanning ---- *)
        iEval (rewrite /fslot HMj) in "Hslot".
        iDestruct "Hslot" as "(%Hcnt & Hcell & Hrest & Hfd)".
        iEval (rewrite -Hpa) in "Hcell".
        iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.filealloc + 0x26)) Ra5 Rs1 (mword_of_int 4 : mword 12)
                  M (trap_res b + (K - 4))%nat (mword_of_int (Z.pos cnt) : mword 32) false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi26 Hcell").
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
        iEval (rewrite Hpa) in "Hcell".
        iDestruct ("Hback" $! Mg with "[%] [Hcell Hrest Hfd]") as "Hslots".
        { intros k _. reflexivity. }
        { rewrite /fslot HMj. iFrame "Hcell Hrest Hfd". iPureIntro. exact Hcnt. }
        set (M1 := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))]> M).
        assert (HM1a5 : M1 !!! Regidx Ra5
                        = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
          by (rewrite /M1; apply upd_eq).
        assert (HM1s1 : M1 !!! Regidx Rs1 = fnode j)
          by (rewrite /M1 upd_ne; [exact Hcurs1 | vm_compute; discriminate]).
        assert (HM1a4 : M1 !!! Regidx Ra4 = fnode NFILE)
          by (rewrite /M1 upd_ne; [exact Ha4 | vm_compute; discriminate]).
        assert (HM1thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                           M1 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs Hne. rewrite /M1 upd_ne; [apply Hthr; assumption |].
          intro Hc. injection Hc as Hc'. subst c. vm_compute in Hcs. discriminate. }
        assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp28) in "Hpc".
        (* +0x28 c.beqz a5 -- NOT taken *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.filealloc + 0x28)) (mword_of_int 13 : mword 8)
                  (Cregidx (mword_of_int 7)) Ra5 M1 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HM1a5; apply fref_word_nonzero;
                        assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity);
                        rewrite E31; lia)
                  with "Hcg Hpc Hi28").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x2a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2a) in "Hpc".
        (* +0x2a addi s1,s1,40 -- the cursor bump *)
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.filealloc + 0x2a)) Rs1 Rs1 (mword_of_int 0x28 : mword 12)
                  M1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi2a").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (M2 := <[Regidx Rs1 := regval_into_reg
                      (add_vec (M1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0x28 : mword 12)))]> M1).
        assert (HM2s1 : M2 !!! Regidx Rs1 = fnode (S j)).
        { rewrite /M2 upd_eq HM1s1. rewrite /fnode.
          apply (acur_step file_base file_stride j).
          rewrite /file_stride. apply bv_eq; vm_compute; reflexivity. }
        assert (HM2a4 : M2 !!! Regidx Ra4 = fnode NFILE)
          by (rewrite /M2 upd_ne; [exact HM1a4 | vm_compute; discriminate]).
        assert (HM2thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                           M2 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs Hne. rewrite /M2 upd_ne; [apply HM1thr; assumption | regne]. }
        assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x2e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2e) in "Hpc".
        (* +0x2e bne s1,a4 -- back edge unless the cursor hit the end *)
        assert (Hcmp : neq_vec (rget M2 Rs1) (rget M2 Ra4)
                       = negb (Nat.eqb (S j) NFILE)).
        { rewrite (rget_ne M2 Rs1 ltac:(vm_compute; discriminate))
                  (rget_ne M2 Ra4 ltac:(vm_compute; discriminate))
                  HM2s1 HM2a4. rewrite /fnode.
          apply acur_neq;
            [exact file_base_nonneg | exact file_stride_pos | exact file_end_fits | lia]. }
        destruct (decide (S j = NFILE)) as [Hend | Hne].
        + (* the table is full: fall through to +0x32 *)
          iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.filealloc + 0x2e)) (mword_of_int 8184 : mword 13)
                    Ra4 Rs1 M2 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp; rewrite (proj2 (Nat.eqb_eq _ _) Hend); reflexivity)
                    with "Hcg Hpc Hi2e").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x32))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp32) in "Hpc".
          iDestruct "Hexit" as "[_ Hfull]".
          iApply ("Hfull" $! M2 with "[%] Hcg Hpc Hslots"). exact HM2thr.
        + (* keep going: the branch is taken back to +0x26 *)
          iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.filealloc + 0x2e)) (mword_of_int 8184 : mword 13)
                    Ra4 Rs1 M2 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp;
                          rewrite (proj2 (Nat.eqb_neq _ _) Hne); reflexivity)
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi2e").
          iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
          assert (Htgtb : add_vec (mword_of_int (KernelSyms.filealloc + 0x2e) : mword 64)
                            (sign_extend' 64 (mword_of_int 8184 : mword 13))
                          = mword_of_int (KernelSyms.filealloc + 0x26))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgtb) in "Hpc".
          (* [done] here searched the whole accumulated hypothesis context
             for this three-way conjunction (~8.85 s, the file's hottest
             line) instead of just using the three facts already proven by
             name -- [HM2s1]/[HM2a4]/[HM2thr] are exactly [IH]'s premise. *)
          iApply ("IH" $! (S j) M2 with "[%] [%] [%] Hcg Hpc Hslots Hexit");
            [lia | lia | exact (conj HM2s1 (conj HM2a4 HM2thr))].
      - (* ---- entry is FREE: ref reads zero, take the branch to +0x42 ---- *)
        iEval (rewrite /fslot HMj) in "Hslot".
        iDestruct "Hslot" as "[Hcell Hfree]".
        iEval (rewrite -Hpa) in "Hcell".
        iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.filealloc + 0x26)) Ra5 Rs1 (mword_of_int 4 : mword 12)
                  M (trap_res b + (K - 4))%nat (mword_of_int 0 : mword 32) false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi26 Hcell").
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
        iEval (rewrite Hpa) in "Hcell".
        iDestruct ("Hback" $! Mg with "[%] [Hcell Hfree]") as "Hslots".
        { intros k _. reflexivity. }
        { rewrite /fslot HMj. iFrame "Hcell Hfree". }
        set (M1 := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 32))]> M).
        assert (HM1a5 : M1 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int 0 : mword 32))
          by (rewrite /M1; apply upd_eq).
        assert (HM1s1 : M1 !!! Regidx Rs1 = fnode j)
          by (rewrite /M1 upd_ne; [exact Hcurs1 | vm_compute; discriminate]).
        assert (HM1thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                           M1 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs Hne. rewrite /M1 upd_ne; [apply Hthr; assumption |].
          intro Hc. injection Hc as Hc'. subst c. vm_compute in Hcs. discriminate. }
        assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp28) in "Hpc".
        (* +0x28 c.beqz a5 -- TAKEN *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.filealloc + 0x28)) (mword_of_int 13 : mword 8)
                  (Cregidx (mword_of_int 7)) Ra5 M1 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HM1a5; exact fref_word_zero)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi28").
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Htgtz : add_vec (mword_of_int (KernelSyms.filealloc + 0x28) : mword 64)
                          (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 13 : mword 8) ('b"0"))))
                        = mword_of_int (KernelSyms.filealloc + 0x42))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtz) in "Hpc".
        iDestruct "Hexit" as "[Hfound _]".
        iApply ("Hfound" $! j M1 with "[%] Hcg Hpc Hslots").
        split; [lia|]. split; [exact HMj|]. split; [exact HM1s1 | exact HM1thr]. }
    (* enter the loop at entry 0 with NFILE units of fuel *)
    iApply ("Hloop" $! NFILE 0%nat R9 with "[%] [%] [%] Hcg Hpc Hslots").
    { lia. }
    { rewrite /NFILE. lia. }
    { split; [exact HR9s1|]. split; [exact HR9a4 | exact HR9thr]. }
    rewrite /Cfound /Cfull. iSplit.
    (* ================================================================= *)
    (*  FOUND arm: f->ref = 1, release, return f.                         *)
    (* ================================================================= *)
    { iIntros (i Mi) "(%Hi & %HMgi & %Mis1 & %Mithr) Hcg Hpc Hslots".
      iPoseProof (fai_42 with "Htext") as "Hi42".
      iPoseProof (fai_44 with "Htext") as "Hi44".
      iPoseProof (fai_46 with "Htext") as "Hi46".
      iPoseProof (fai_4a with "Htext") as "Hi4a".
      iPoseProof (fai_4e with "Htext") as "Hi4e".
      iDestruct (ftable_slots_acc γf Mg i ltac:(lia) with "Hslots") as "[Hslot Hback]".
      iEval (rewrite /fslot HMgi) in "Hslot".
      iDestruct "Hslot" as "[Hcell Hfree]".
      iDestruct "Hfree" as (Cf) "(%HCtype & Hfields & Hfpay)".
      (* +0x42 c.li a5,1 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.filealloc + 0x42)) Ra5 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) Mi (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi42").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (F1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> Mi).
      assert (HF1s1 : F1 !!! Regidx Rs1 = fnode i)
        by (rewrite /F1 upd_ne; [exact Mis1 | vm_compute; discriminate]).
      assert (Hpa : add_vec (F1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                    = a_fref i) by (rewrite HF1s1; reflexivity).
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.sw a5,4(s1) : f->ref = 1 *)
      iEval (rewrite -Hpa) in "Hcell".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.filealloc + 0x44)) Ra5 Rs1 (mword_of_int 4 : mword 12)
                F1 (trap_res b + (K - 4))%nat (mword_of_int 0 : mword 32) false
                with "Hcg Hpc Hi44 Hcell").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
      iEval (rewrite Hpa) in "Hcell".
      assert (Hstv : trunc32 (rget F1 Ra5) = (mword_of_int (Z.pos 1) : mword 32)).
      { rewrite (rget_ne F1 Ra5 ltac:(vm_compute; discriminate)).
        rewrite /F1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hstv) in "Hcell".
      (* the ghost step: the slot enters the authority at (1,1) *)
      iMod (file_alloc_step γf Mg i Cf HMgi with "Hauth Hfields Hfpay") as "[Hauth Href]".
      iDestruct ("Hback" $! (<[i := (1%Qp, 1%positive)]> Mg) with "[%] [Hcell Hfdslot]") as "Hslots".
      { intros k Hk. rewrite lookup_insert_ne; [reflexivity | regne]. }
      { rewrite /fslot lookup_insert. rewrite file_rest_full.
        iFrame "Hcell". rewrite /fd_slot /=. iFrame "Hfdslot". iPureIntro.
        assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
        rewrite E31. lia. }
      iAssert (ftable_res γf) with "[Hauth Hfdauth Hslots]" as "HRres".
      { iExists (<[i := (1%Qp, 1%positive)]> Mg). iFrame "Hauth Hfdauth Hslots".
        iPureIntro. intros k Hk.
        destruct (decide (k = i)) as [->|Hne]; [lia|].
        apply Hdom. by rewrite lookup_insert_ne in Hk. }
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 auipc a0,0x1e ; +0x4a addi a0,a0,1122  (a0 := &ftable) *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.filealloc + 0x46)) Ra0 (mword_of_int 0x1e : mword 20)
                F1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi46").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (F2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.filealloc + 0x46) : mword 64)
                       (auipc_off (mword_of_int 0x1e : mword 20)))]> F1).
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.filealloc + 0x4a)) Ra0 Ra0 (mword_of_int 0x44c : mword 12)
                F2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (F3 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (F2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1100 : mword 12)))]> F2).
      assert (HF3a0 : F3 !!! Regidx Ra0 = ftable_addr).
      { rewrite /F3 upd_eq /F2 upd_eq. rewrite /ftable_addr.
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x4a) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4e) in "Hpc".
      (* +0x4e jal ra,release *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.filealloc + 0x4e)) Rra (mword_of_int 0x1fcbc6 : mword 21)
                F3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4e").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (F4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.filealloc + 0x4e) : mword 64) 4)]> F3).
      assert (Htgtrel : add_vec (mword_of_int (KernelSyms.filealloc + 0x4e) : mword 64)
                          (sign_extend' 64 (mword_of_int 0x1fcbc6 : mword 21))
                        = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtrel) in "Hpc".
      assert (HF4a0 : F4 !!! Regidx Ra0 = ftable_addr)
        by (rewrite /F4 upd_ne; [exact HF3a0 | vm_compute; discriminate]).
      assert (HF4thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                         F4 !!! Regidx c = macq !!! Regidx c).
      { intros c Hcs Hne.
        rewrite /F4 upd_ne; [| regne].
        rewrite /F3 upd_ne; [| regne].
        rewrite /F2 upd_ne; [| regne].
        rewrite /F1 upd_ne; [apply Mithr; assumption |].
        intro Hc. injection Hc as Hc'. subst c. vm_compute in Hcs. discriminate. }
      assert (HF4sp : F4 !!! Regidx csp_rs1 = spr)
        by (rewrite (HF4thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hmsp).
      assert (HF4s1 : F4 !!! Regidx Rs1 = fnode i).
      { rewrite /F4 upd_ne; [| vm_compute; discriminate].
        rewrite /F3 upd_ne; [| vm_compute; discriminate].
        rewrite /F2 upd_ne; [| vm_compute; discriminate]. exact HF1s1. }
      assert (HF4ra : F4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.filealloc + 0x4e) : mword 64) 4)
        by (rewrite /F4; apply upd_eq).
      (* ===== +0x4e lands us in release; absorb its derived exit index via
         [Houtb]. ===== *)
      (* the acquire handed the window index out as [trap_res b + N]; release
         wants it as [trap_res outb + N] with [outb = match n with O => eb
         | S _ => false end].  Those are the same bool -- [cpu_own] forces
         it -- so this is a pure re-spelling, and it is what makes the
         acquire/release pair compose back to [N]. *)
      iEval (rewrite Houtb) in "Hcg".
      iApply (Release.wp_release_sconf γl ftable_addr "ftable"%string (ftable_res γf) F4
                n eb p C (K - 4)%nat
                ltac:(rewrite HF4a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
      { iExact "Hlock". }
      iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
      iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
      rewrite <- Houtb in Hsr.
      pose proof Hrelpins as Hrelpins_cs.
      assert (Hpc52 : ret_pc (F4 !!! Regidx Rra) = mword_of_int (KernelSyms.filealloc + 0x52)).
      { rewrite HF4ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc52) in "Hpc".
      iApply ("Hepi" $! CIDr mr (fnode i) with "[%] Hcg Hpc Hcnt [Href]").
      { split.
        { rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HF4sp. }
        split.
        { rewrite (callee_saved_lookup Hrelpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HF4s1. }
        intros c Hcs N9 N2 N8.
        rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
        rewrite (HF4thr c Hcs N9).
        rewrite (callee_saved_lookup Hacqpins_cs c Hcs).
        rewrite /mA upd_ne; [| regne].
        rewrite /R4 upd_ne; [| regne].
        rewrite /R3 upd_ne; [| regne].
        rewrite /R2 upd_ne; [| regne].
        rewrite /R1 upd_ne; [reflexivity | regne]. }
      { rewrite /filealloc_post. iRight. iExists i, Cf. iFrame "Href".
        iPureIntro. split; [lia|]. split; [reflexivity | exact HCtype]. }
      (* [Hepi] handed back its own [wp_next]-shaped obligation, relative to
         CIDr; NOW (with the FULL chain -- Hs1..Hs8, Hsacq, the acquire-to-
         release hop, Hsr, and Hepi's own internal steps -- all in scope) is
         where the real outer [Hcont] gets closed. *)
      iIntros (CIDfin Hsfin mfin) "Hcg Hcnt Hpc %Hfin Hpost".
      iSpecialize ("Hcont" $! CIDfin with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mfin with "Hcg Hcnt Hpc [%] Hpost").
      exact Hfin. }
    (* ================================================================= *)
    (*  FULL arm: release, return 0.                                      *)
    (* ================================================================= *)
    { iIntros (Mf) "%Mfthr Hcg Hpc Hslots".
      iPoseProof (fai_32 with "Htext") as "Hi32".
      iPoseProof (fai_36 with "Htext") as "Hi36".
      iPoseProof (fai_3a with "Htext") as "Hi3a".
      iPoseProof (fai_3e with "Htext") as "Hi3e".
      iPoseProof (fai_40 with "Htext") as "Hi40".
      iAssert (ftable_res γf) with "[Hauth Hfdauth Hslots]" as "HRres".
      { iExists Mg. iFrame "Hauth Hfdauth Hslots". iPureIntro. exact Hdom. }
      (* +0x32 auipc a0,0x1e ; +0x36 addi a0,a0,1120 *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.filealloc + 0x32)) Ra0 (mword_of_int 0x1e : mword 20)
                Mf (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi32").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (G1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.filealloc + 0x32) : mword 64)
                       (auipc_off (mword_of_int 0x1e : mword 20)))]> Mf).
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.filealloc + 0x36)) Ra0 Ra0 (mword_of_int 0x460 : mword 12)
                G1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (G2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (G1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1120 : mword 12)))]> G1).
      assert (HG2a0 : G2 !!! Regidx Ra0 = ftable_addr).
      { rewrite /G2 upd_eq /G1 upd_eq. rewrite /ftable_addr.
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.filealloc + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a jal ra,release *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.filealloc + 0x3a)) Rra (mword_of_int 0x1fcbda : mword 21)
                G2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (G3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.filealloc + 0x3a) : mword 64) 4)]> G2).
      assert (Htgtrel : add_vec (mword_of_int (KernelSyms.filealloc + 0x3a) : mword 64)
                          (sign_extend' 64 (mword_of_int 0x1fcbda : mword 21))
                        = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtrel) in "Hpc".
      assert (HG3a0 : G3 !!! Regidx Ra0 = ftable_addr)
        by (rewrite /G3 upd_ne; [exact HG2a0 | vm_compute; discriminate]).
      assert (HG3thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                         G3 !!! Regidx c = macq !!! Regidx c).
      { intros c Hcs Hne.
        rewrite /G3 upd_ne; [| regne].
        rewrite /G2 upd_ne; [| regne].
        rewrite /G1 upd_ne; [apply Mfthr; assumption | regne]. }
      assert (HG3ra : G3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.filealloc + 0x3a) : mword 64) 4)
        by (rewrite /G3; apply upd_eq).
      (* the acquire handed the window index out as [trap_res b + N]; release
         wants it as [trap_res outb + N] with [outb = match n with O => eb
         | S _ => false end].  Those are the same bool -- [cpu_own] forces
         it -- so this is a pure re-spelling, and it is what makes the
         acquire/release pair compose back to [N]. *)
      iEval (rewrite Houtb) in "Hcg".
      iApply (Release.wp_release_sconf γl ftable_addr "ftable"%string (ftable_res γf) G3
                n eb p C (K - 4)%nat
                ltac:(rewrite HG3a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
      { iExact "Hlock". }
      iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
      iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
      rewrite <- Houtb in Hsr.
      pose proof Hrelpins as Hrelpins_cs.
      assert (Hpc3e : ret_pc (G3 !!! Regidx Rra) = mword_of_int (KernelSyms.filealloc + 0x3e)).
      { rewrite HG3ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc3e) in "Hpc".
      (* +0x3e c.li s1,0 -- past release, GENERIC [b] again (via [Houtb]) *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.filealloc + 0x3e)) Rs1 (mword_of_int 0 : mword 6)
                (zero_reg : mword 64) mr (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi3e").
      iIntros (CIDg1 Hsg1) "Hcg Hpc".
      set (G4 := <[Regidx Rs1 := regval_into_reg (zero_reg : mword 64)]> mr).
      assert (HG4s1 : G4 !!! Regidx Rs1 = (zero_reg : mword 64))
        by (rewrite /G4; apply upd_eq).
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.filealloc + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.filealloc + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* +0x40 c.j +0x52 *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.filealloc + 0x40))
                (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")))
                G4 (K - 4)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi40").
      iIntros (CIDg2 Hsg2). iNext. iIntros "Hcg Hpc".
      assert (Htgtj : add_vec (mword_of_int (KernelSyms.filealloc + 0x40) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.filealloc + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtj) in "Hpc".
      (* two more plain instructions since release handed [cpu_own] back at
         [CIDr]. *)
      iDestruct (cpu_own_transport CIDr CIDg2 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("Hepi" $! CIDg2 G4 (zero_reg : mword 64) with "[%] Hcg Hpc Hcnt [Hfdslot]").
      { split.
        { rewrite /G4 upd_ne; [| vm_compute; discriminate].
          rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite (HG3thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
          exact Hmsp. }
        split; [exact HG4s1|].
        intros c Hcs N9 N2 N8.
        rewrite /G4 upd_ne; [| regne].
        rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
        rewrite (HG3thr c Hcs N9).
        rewrite (callee_saved_lookup Hacqpins_cs c Hcs).
        rewrite /mA upd_ne; [| regne].
        rewrite /R4 upd_ne; [| regne].
        rewrite /R3 upd_ne; [| regne].
        rewrite /R2 upd_ne; [| regne].
        rewrite /R1 upd_ne; [reflexivity | regne]. }
      { rewrite /filealloc_post. iLeft. iSplitR; [done|].
        (* the scan created no reference, so the unit the caller supplied is
           still untouched -- it goes straight back out. *)
        iExact "Hfdslot". }
      iIntros (CIDfin Hsfin mfin) "Hcg Hcnt Hpc %Hfin Hpost".
      iSpecialize ("Hcont" $! CIDfin with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mfin with "Hcg Hcnt Hpc [%] Hpost").
      exact Hfin. }
  Qed.

End ProofFilealloc.

End FileallocProof.
