(* ProofFiledup.v -- filedup over the SIE-agnostic sconf world.

     acquire(&ftable.lock); if (f->ref < 1) panic; f->ref++; release; return f

   Straight-line, so the whole proof is about two things the ghost state has
   to supply, both under the lock:

   * the [f->ref < 1] arm is DEAD.  The caller's [file_ref] is a fragment of
     the authority, so [fref_tok_lookup] puts slot k in the domain with a
     [positive] count, and [fref_word_spos] turns that into "the sign-extended
     load is signed-positive", which is exactly what [bge x0,a5] tests.  The
     panic tail is never reached and this file proves no [instr] fact for it.

   * the [f->ref++] cannot overflow.  That is NOT a fact about the table --
     no unconditional increment preserves a finite bound -- it comes from the
     caller's [fd_slot]: the table holds one fd slot per outstanding
     reference, the supply is fixed at FDSLOTS, so adding the caller's slot
     to the ones already there gives [Pos.to_nat n + 1 <= FDSLOTS] by auth
     validity alone ([fd_slots_no_overflow]).  Both the [c.addiw] arithmetic
     and the invariant's re-established bound come from that one fact.

   The reference split itself is [file_dup_step]: the duplicate's fraction
   comes out of the caller's, each side leaving with q/2, so the invariant's
   leftover [file_rest k qt] is untouched -- which is why the slot closes
   back up at the same [qt] with only its count and its fd slots changed. *)
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
Require Import WpAuipc.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import FdSlots FileInv WpFiledupDecode.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecAcquire SpecRelease.
Require Import SpecFiledup.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Module FiledupProof (Acquire : ACQUIRE) (Release : RELEASE) : FILEDUP.

Section ProofFiledup.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ}.
  Context `{CID : CpuId}.

  Notation FD := KernelSyms.filedup.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rtp  := (mword_of_int 4 : mword 5).

  Local Ltac regne :=
    first [ congruence
          | apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption] ].

  Lemma wp_filedup_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl γf : gname) (k : nat) (q : Qp) (Cf : fcontent)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat)
    : wp_filedup_sconf_body γ Φ γl γf k q Cf m n eb p C K.
  Proof.
    cbv beta delta [wp_filedup_sconf_body].
    intros pcE ret_tgt HK Htp Hnoffpos Ha0.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hlock #Hpanic Hfdslot Href Hcont".
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (fdi_00 with "Htext") as "Hi00".
    iPoseProof (fdi_02 with "Htext") as "Hi02".
    iPoseProof (fdi_04 with "Htext") as "Hi04".
    iPoseProof (fdi_06 with "Htext") as "Hi06".
    iPoseProof (fdi_08 with "Htext") as "Hi08".
    iPoseProof (fdi_0a with "Htext") as "Hi0a".
    iPoseProof (fdi_0c with "Htext") as "Hi0c".
    iPoseProof (fdi_10 with "Htext") as "Hi10".
    iPoseProof (fdi_14 with "Htext") as "Hi14".
    (* ===== PROLOGUE ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE (mword_of_int 32 : mword 6) m K 4
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
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
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FD + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (FD + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (FD + 0x02) : mword 64) 2 = mword_of_int (FD + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (FD + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (FD + 0x04) : mword 64) 2 = mword_of_int (FD + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (FD + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (FD + 0x06) : mword 64) 2 = mword_of_int (FD + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (FD + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (FD + 0x08) : mword 64) 2 = mword_of_int (FD + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 : the cursor register takes the argument *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (FD + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = fnode k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (FD + 0x0a) : mword 64) 2 = mword_of_int (FD + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c/+0x10 a0 := &ftable *)
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (FD + 0x0c)) Ra0 (mword_of_int 0x1e : mword 20)
              R3 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (FD + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 0x1e : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (FD + 0x0c) : mword 64) 4 = mword_of_int (FD + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (FD + 0x10)) Ra0 Ra0 (mword_of_int 0x43e : mword 12)
              R4 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x43e : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = ftable_addr).
    { rewrite /R5 upd_eq /R4 upd_eq. rewrite /ftable_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (FD + 0x10) : mword 64) 4 = mword_of_int (FD + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (FD + 0x14)) Rra (mword_of_int 0x1fcbde : mword 21)
              R5 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FD + 0x14) : mword 64) 4)]> R5).
    assert (Htgtacq : add_vec (mword_of_int (FD + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1fcbde : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAtp : mA !!! Regidx Rtp = m !!! Regidx Rtp).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HmAa0 : mA !!! Regidx Ra0 = ftable_addr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate]. exact HR5a0. }
    assert (HmAs1 : mA !!! Regidx Rs1 = fnode k).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HR3s1. }
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (FD + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    iApply (Acquire.wp_acquire_sconf γ Φ γl "ftable"%string (ftable_res γf) mA
              n eb p C (K - 4)%nat
              ltac:(etransitivity; [exact HmAtp | exact Htp])
              Hnoffpos ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlock] Hpanic [-]").
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra) = mword_of_int (FD + 0x18)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (Hmtp : macq !!! Regidx Rtp = m !!! Regidx Rtp)
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 4) ltac:(vm_compute; reflexivity)); exact HmAtp).
    assert (Hms1 : macq !!! Regidx Rs1 = fnode k)
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmAs1).
    (* ===== the critical section ===== *)
    iDestruct "HRres" as (Mg) "(Hauth & Hfdauth & %Hdom & Hslots)".
    (* the caller's reference names a live slot *)
    iDestruct "Href" as "[Hrtok Hrfields]".
    iDestruct (fref_tok_lookup with "Hauth Hrtok") as %(qt & cnt & HMk & _ & _).
    assert (Hk : (k < NFILE)%nat) by (apply Hdom; rewrite HMk; eauto).
    iDestruct (ftable_slots_acc Mg k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /fslot HMk) in "Hslot".
    iDestruct "Hslot" as "(%Hcnt & Hcell & Hrest & Hfd)".
    (* the fd-slot conservation law: the caller's slot plus the ones the table
       already holds for this file are within the fixed supply, so the count
       is safely below what an int holds -- BEFORE and AFTER the increment. *)
    iDestruct (fd_slots_combine with "Hfd Hfdslot") as "Hfd".
    assert (Hsucc : (Pos.to_nat cnt + 1)%nat = Pos.to_nat (Pos.succ cnt))
      by (rewrite Pos2Nat.inj_succ; lia).
    iEval (rewrite Hsucc) in "Hfd".
    iDestruct (fd_slots_no_overflow with "Hfdauth Hfd") as %[Hno _].
    iPoseProof (fdi_18 with "Htext") as "Hi18".
    iPoseProof (fdi_1a with "Htext") as "Hi1a".
    iPoseProof (fdi_1e with "Htext") as "Hi1e".
    iPoseProof (fdi_20 with "Htext") as "Hi20".
    iPoseProof (fdi_22 with "Htext") as "Hi22".
    iPoseProof (fdi_26 with "Htext") as "Hi26".
    iPoseProof (fdi_2a with "Htext") as "Hi2a".
    (* +0x18 c.lw a5,4(s1) *)
    assert (Hpa : add_vec (macq !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                  = a_fref k) by (rewrite Hms1; reflexivity).
    iEval (rewrite -Hpa) in "Hcell".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (FD + 0x18)) Ra5 Rs1 (mword_of_int 4 : mword 12)
              macq (K - 4)%nat (mword_of_int (Z.pos cnt) : mword 32)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi18 Hcell [-]").
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa) in "Hcell".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))]> macq).
    assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /D1; apply upd_eq).
    assert (HD1s1 : D1 !!! Regidx Rs1 = fnode k)
      by (rewrite /D1 upd_ne; [exact Hms1 | vm_compute; discriminate]).
    assert (Hpp1a : add_vec_int (mword_of_int (FD + 0x18) : mword 64) 2 = mword_of_int (FD + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a bge x0,a5 -- the panic arm, NOT taken *)
    iApply (wp_bge_x0_fall_s_sconf γ Φ (mword_of_int (FD + 0x1a)) (mword_of_int 32 : mword 13)
              Ra5 D1 (K - 4)%nat ltac:(vm_compute; discriminate)
              ltac:(rewrite HD1a5; apply fref_word_spos; exact Hcnt)
              with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc".
    assert (Hpp1e : add_vec_int (mword_of_int (FD + 0x1a) : mword 64) 4 = mword_of_int (FD + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.addiw a5,a5,1 *)
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (FD + 0x1e)) Ra5 (mword_of_int 1 : mword 6)
              D1 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (D1 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D1).
    assert (HD2s1 : D2 !!! Regidx Rs1 = fnode k)
      by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
    assert (Hpp20 : add_vec_int (mword_of_int (FD + 0x1e) : mword 64) 2 = mword_of_int (FD + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.sw a5,4(s1) : f->ref = ref+1 *)
    assert (Hpa2 : add_vec (D2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                   = a_fref k) by (rewrite HD2s1; reflexivity).
    iEval (rewrite -Hpa2) in "Hcell".
    iApply (wp_csw_s_sconf γ Φ (mword_of_int (FD + 0x20)) Ra5 Rs1 (mword_of_int 4 : mword 12)
              D2 (K - 4)%nat (mword_of_int (Z.pos cnt) : mword 32)
              with "Hcg Hpc Hi20 Hcell [-]").
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa2) in "Hcell".
    (* the stored word IS the successor count -- the [c.addiw] arithmetic *)
    assert (Hstv : trunc32 (D2 !!! Regidx Ra5) = (mword_of_int (Z.pos (Pos.succ cnt)) : mword 32)).
    { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5.
      rewrite (moi32_storeval_succ (Z.pos cnt) ltac:(lia)
                 ltac:(pose proof Hno as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
      f_equal. rewrite Pos2Z.inj_succ. lia. }
    iEval (rewrite Hstv) in "Hcell".
    (* the ghost step: one more reference, the caller's fraction halved *)
    iMod (file_dup_step γf Mg k q Cf qt cnt HMk with "Hauth [Hrtok Hrfields]") as "(Hauth & Href1 & Href2)".
    { rewrite /file_ref /fref_tok. iFrame "Hrtok Hrfields". }
    iDestruct ("Hback" $! (<[k := (qt, Pos.succ cnt)]> Mg) with "[%] [Hcell Hrest Hfd]") as "Hslots".
    { intros j Hj. rewrite lookup_insert_ne; [reflexivity | congruence]. }
    { rewrite /fslot lookup_insert. iFrame "Hcell Hrest Hfd". iPureIntro. exact Hno. }
    iAssert (ftable_res γf) with "[Hauth Hfdauth Hslots]" as "HRres".
    { iExists (<[k := (qt, Pos.succ cnt)]> Mg). iFrame "Hauth Hfdauth Hslots".
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
      apply Hdom. by rewrite lookup_insert_ne in Hj. }
    assert (Hpp22 : add_vec_int (mword_of_int (FD + 0x20) : mword 64) 2 = mword_of_int (FD + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22/+0x26 a0 := &ftable ; +0x2a jal release *)
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (FD + 0x22)) Ra0 (mword_of_int 0x1e : mword 20)
              D2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi22 [-]").
    iIntros "Hcg Hpc".
    set (D3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (FD + 0x22) : mword 64)
                     (auipc_off (mword_of_int 0x1e : mword 20)))]> D2).
    assert (Hpp26 : add_vec_int (mword_of_int (FD + 0x22) : mword 64) 4 = mword_of_int (FD + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (FD + 0x26)) Ra0 Ra0 (mword_of_int 0x428 : mword 12)
              D3 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26 [-]").
    iIntros "Hcg Hpc".
    set (D4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (D3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0x428 : mword 12)))]> D3).
    assert (HD4a0 : D4 !!! Regidx Ra0 = ftable_addr).
    { rewrite /D4 upd_eq /D3 upd_eq. rewrite /ftable_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp2a : add_vec_int (mword_of_int (FD + 0x26) : mword 64) 4 = mword_of_int (FD + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (FD + 0x2a)) Rra (mword_of_int 0x1fcc50 : mword 21)
              D4 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi2a [-]").
    iIntros "Hcg Hpc".
    set (D5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FD + 0x2a) : mword 64) 4)]> D4).
    assert (Htgtrel : add_vec (mword_of_int (FD + 0x2a) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1fcc50 : mword 21))
                      = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HD5a0 : D5 !!! Regidx Ra0 = ftable_addr)
      by (rewrite /D5 upd_ne; [exact HD4a0 | vm_compute; discriminate]).
    assert (HD5thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                       D5 !!! Regidx c = macq !!! Regidx c).
    { intros c Hcs Hne.
      rewrite /D5 upd_ne; [| regne].
      rewrite /D4 upd_ne; [| regne].
      rewrite /D3 upd_ne; [| regne].
      rewrite /D2 upd_ne; [| regne].
      rewrite /D1 upd_ne; [reflexivity | regne]. }
    assert (HD5sp : D5 !!! Regidx csp_rs1 = spr)
      by (rewrite (HD5thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hmsp).
    assert (HD5tp : D5 !!! Regidx Rtp = m !!! Regidx Rtp)
      by (rewrite (HD5thr (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hmtp).
    assert (HD5s1 : D5 !!! Regidx Rs1 = fnode k).
    { rewrite /D5 upd_ne; [| vm_compute; discriminate].
      rewrite /D4 upd_ne; [| vm_compute; discriminate].
      rewrite /D3 upd_ne; [| vm_compute; discriminate]. exact HD2s1. }
    assert (HD5ra : D5 !!! Regidx Rra = add_vec_int (mword_of_int (FD + 0x2a) : mword 64) 4)
      by (rewrite /D5; apply upd_eq).
    iApply (Release.wp_release_sconf γ Φ γl ftable_addr "ftable"%string (ftable_res γf) D5
              n eb p C (K - 4)%nat
              ltac:(rewrite HD5a0; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HD5tp; exact Htp)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay [-]").
    { iExact "Hlock". }
    iIntros (mr) "Hcg Hpc %Hrelpins Hcnt".
    assert (Hpc2e : ret_pc (D5 !!! Regidx Rra) = mword_of_int (FD + 0x2e)).
    { rewrite HD5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc2e) in "Hpc".
    pose proof Hrelpins as Hrelpins_cs.
    (* ===== EPILOGUE ===== *)
    iPoseProof (fdi_2e with "Htext") as "Hi2e".
    iPoseProof (fdi_30 with "Htext") as "Hi30".
    iPoseProof (fdi_32 with "Htext") as "Hi32".
    iPoseProof (fdi_34 with "Htext") as "Hi34".
    iPoseProof (fdi_36 with "Htext") as "Hi36".
    iPoseProof (fdi_38 with "Htext") as "Hi38".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HD5sp).
    assert (Hmrs1 : mr !!! Regidx Rs1 = fnode k)
      by (rewrite (callee_saved_lookup Hrelpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HD5s1).
    (* +0x2e c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (FD + 0x2e)) Ra0 Rs1
              mr (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2e [-]").
    iIntros "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Rs1))]> mr).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact Hmrsp | vm_compute; discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (FD + 0x2e) : mword 64) 2 = mword_of_int (FD + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
    iEval (rewrite HspR1) in "Hr8".  iEval (rewrite HspR1) in "Hg4".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (FD + 0x30)) (mword_of_int 3 : mword 6) Rra
              P1 (K - 4)%nat (R1 !!! Regidx Rra)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi30 [Hr24] [-]").
    { iEval (rewrite HP1sp). iExact "Hr24". }
    iIntros "Hcg Hpc Hr24".
    iEval (rewrite HP1sp) in "Hr24".
    set (P2 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp32 : add_vec_int (mword_of_int (FD + 0x30) : mword 64) 2 = mword_of_int (FD + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (FD + 0x32)) (mword_of_int 2 : mword 6) Rs0
              P2 (K - 4)%nat (R1 !!! Regidx Rs0)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi32 [Hr16] [-]").
    { iEval (rewrite HP2sp). iExact "Hr16". }
    iIntros "Hcg Hpc Hr16".
    iEval (rewrite HP2sp) in "Hr16".
    set (P3 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp34 : add_vec_int (mword_of_int (FD + 0x32) : mword 64) 2 = mword_of_int (FD + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (FD + 0x34)) (mword_of_int 1 : mword 6) Rs1
              P3 (K - 4)%nat (R1 !!! Regidx Rs1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi34 [Hr8] [-]").
    { iEval (rewrite HP3sp). iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    iEval (rewrite HP3sp) in "Hr8".
    set (P4 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hpp36 : add_vec_int (mword_of_int (FD + 0x34) : mword 64) 2 = mword_of_int (FD + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
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
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (FD + 0x36)) (mword_of_int 2 : mword 6)
              P4 (K - 4)%nat 4 Hpop with "Hcg Hpc Hi36 Hframe4 [-]").
    iIntros "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P4 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4) with P5.
    assert (Hpp38 : add_vec_int (mword_of_int (FD + 0x36) : mword 64) 2 = mword_of_int (FD + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    assert (HP5ra : P5 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HP5a0 : P5 !!! Regidx Ra0 = fnode k).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. rewrite Hmrs1. apply add_vec_zero_l. }
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (FD + 0x38)) Rra P5 K
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi38 [-]").
    iIntros "Hcg Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra) = ret_tgt) by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! P5 with "Hcg Hcnt Hpc [%] Href1 Href2").
    (* callee_saved m P5, and a0 = f *)
    split; [| exact HP5a0].
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
      rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
      rewrite (HD5thr c Hcs N9).
      rewrite (callee_saved_lookup Hacqpins_cs c Hcs).
      rewrite /mA upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
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
    assert (Hc4 : P5 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5))
      by (apply Hthread; vm_compute; first [reflexivity | discriminate]).
    repeat split;
      first [ exact Hc2 | exact Hc4 | exact Hc8 | exact Hc9
            | apply Hthread; vm_compute; first [reflexivity | discriminate] ].
  Qed.

End ProofFiledup.

End FiledupProof.
