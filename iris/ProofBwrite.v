(* ProofBwrite.v -- bwrite over the SIE-agnostic sconf world.

     void bwrite(struct buf *b) {
       if (!holdingsleep(&b->lock)) panic("bwrite");
       virtio_disk_rw(b, 1);
     }

   Straight-line, so the whole proof is about three things:

   * the panic arm is DEAD.  [bio_locked] carries the sleeplock's exclusive
     token AND the pid cell the holder wrote, and the caller's own [p_pid]
     cell agrees with it, so holdingsleep's HOLDER variant returns 1 and the
     [c.beqz a0] at +0x12 falls through.  This file proves no [instr] fact for
     the tail at +0x26.

   * the WRITE flag.  [c.li a1,1] makes rw's [wr] -- which its spec spells as
     [negb (eq_vec (m !!! a1) zero_reg)] -- literally [true], so rw's exchange
     is the write case: [disk_block] leaves holding the BUFFER's bytes and the
     buffer comes back unchanged.  That is exactly bwrite's postcondition.

   * rw's [addr_is_kdata] premise on [b->data].  [b] is [bnode k] for
     k < NBUF, i.e. an element of bio.c's static [bcache] object at
     0x80018190, which lies well above [text_end] and well below PHYSTOP --
     [bw_data_kdata] below is that one arithmetic fact.

   The buffer's [valid] cell and its half of [dev] are untouched by both
   callees, so they are simply framed across the two calls and [bio_locked]
   is rebuilt from them plus the token/pid holdingsleep hands back and the
   [buf_own] rw returns. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpLock SleepLock.
Require Import WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import ByteCursor ArrCursor.
Require Import DiskPtsto DiskInv.
Require Import BufOwn BcacheInv BioInv.
Require Import SpecPanic.
Require Import SpecHoldingsleep SpecVirtioDiskRw.
Require Import SpecBwrite.
Require Import WpBwriteDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  The one arithmetic fact: every buffer's data area is kernel DATA.      *)
(*                                                                        *)
(*  [bcache] is a .bss object at 0x80018190; buffer k's base is            *)
(*  [buf_base + 1112*k] with buf_base = bcache+24 and k < NBUF = 30, so    *)
(*  the whole object sits inside [text_end, ram_base+ram_size) and the     *)
(*  address arithmetic never wraps.                                       *)
(* ===================================================================== *)

Lemma bw_wrap64_z (a : Z) : bv_wrap 64 a = (a `mod` 18446744073709551616)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. reflexivity. Qed.

Lemma bw_bnode_unsigned (k : nat) : (k < NBUF)%nat ->
  bv_unsigned (bnode k) = buf_base + buf_stride * Z.of_nat k.
Proof.
  intro Hk. unfold bnode.
  apply (acur_unsigned buf_base buf_stride k NBUF
           buf_base_nonneg buf_stride_pos buf_end_fits).
  lia.
Qed.

Lemma bw_kdata_z (b j : Z) :
  (2147512320 <= b)%Z -> (0 <= j)%Z -> (b + j < 2281701376)%Z ->
  (2147512320 <= ((b `mod` 18446744073709551616) + j) `mod` 18446744073709551616
     < 2281701376)%Z.
Proof.
  intros H1 H2 H3.
  rewrite (Z.mod_small b); [| lia].
  rewrite Z.mod_small; lia.
Qed.

Lemma bw_data_kdata (k j : nat) : (k < NBUF)%nat -> (j < 1024)%nat ->
  addr_is_kdata (pa_add (b_data (bnode k)) j).
Proof.
  intros Hk Hj. unfold addr_is_kdata, b_data, text_end, ram_base, ram_size.
  rewrite RiscvExtras.uint_unsigned.
  rewrite !ByteCursor.pa_add_unsigned.
  rewrite !bw_wrap64_z.
  rewrite (bw_bnode_unsigned k Hk).
  change (0x80007000)%Z with 2147512320%Z.
  change (0x80000000 + 0x8000000)%Z with 2281701376%Z.
  apply bw_kdata_z.
  - unfold buf_base, buf_stride, KernelSyms.bcache.
    pose proof (Nat2Z.is_nonneg k). lia.
  - exact (Nat2Z.is_nonneg j).
  - unfold NBUF in Hk. unfold buf_base, buf_stride, KernelSyms.bcache.
    assert (Hkz : (Z.of_nat k <= 29)%Z) by lia.
    assert (Hjz : (Z.of_nat j <= 1023)%Z) by lia.
    lia.
Qed.

(* the [wr] flag rw's spec computes from a1: [li a1,1] makes it [true]. *)
Lemma bw_wr_true (v : SailStdpp.Values.mword 64) (l1 l2 : list (bv 8)) :
  v = (mword_of_int 1 : mword 64) ->
  (if negb (eq_vec v (zero_reg : mword 64)) then l1 else l2) = l1.
Proof.
  intros ->.
  replace (eq_vec (mword_of_int 1 : mword 64) (zero_reg : mword 64)) with false
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* ===================================================================== *)

Module BwriteProof (HSL : HOLDINGSLEEP) (RW : VIRTIODISKRW) : BWRITE.

Section ProofBwrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{CID : CpuId}.

  Notation BW := KernelSyms.bwrite.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).

  (* the [upd_ne] side goal is [lookup-key <> update-key]; try the two
     [is_cs_idx] readings first and leave [congruence] (the slow closer --
     claude-notes/optimization.md) for the callee-saved writes. *)
  Local Ltac regne :=
    first [ apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
          | congruence ].

  Lemma wp_bwrite_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (k : nat)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (bs bs_disk : list (bv 8))
    : wp_bwrite_sconf_body γ Φ γs j γl γu γd γk pd pav pu bn k
                           pidv dev bno dq m K eb C bs bs_disk.
  Proof.
    cbv beta delta [wp_bwrite_sconf_body].
    intros pcE pj ret_tgt HK Hbno Htp Hj Hgl Hk Ha0.
    unfold K_bwrite in HK.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt Hpay #Htext Hpc #Hpanic #Hbio Hppid Hprocs Hoctx Hvc Hdev Hgeom Hdlock Hlocked Hdisk Hcont".
    iDestruct "Hlocked" as "(%Hk2 & Hstok & Hpid & Hvalid & Hbdev & Hbuf)".
    iDestruct (bio_ctx_buf bn k Hk with "Hbio") as "[#Hslk _]".
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (bwi_00 with "Htext") as "Hi00".
    iPoseProof (bwi_02 with "Htext") as "Hi02".
    iPoseProof (bwi_04 with "Htext") as "Hi04".
    iPoseProof (bwi_06 with "Htext") as "Hi06".
    iPoseProof (bwi_08 with "Htext") as "Hi08".
    iPoseProof (bwi_0a with "Htext") as "Hi0a".
    iPoseProof (bwi_0c with "Htext") as "Hi0c".
    iPoseProof (bwi_0e with "Htext") as "Hi0e".
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
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (BW + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (BW + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (BW + 0x02) : mword 64) 2 = mword_of_int (BW + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (BW + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (BW + 0x04) : mword 64) 2 = mword_of_int (BW + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (BW + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (BW + 0x06) : mword 64) 2 = mword_of_int (BW + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (BW + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (BW + 0x08) : mword 64) 2 = mword_of_int (BW + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 : the buffer pointer is saved *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (BW + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = bnode k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (BW + 0x0a) : mword 64) 2 = mword_of_int (BW + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.addi a0,a0,16 : a0 := &b->lock *)
    iApply (wp_caddi_s_sconf γ Φ (mword_of_int (BW + 0x0c)) Ra0 (mword_of_int 16 : mword 6)
              R3 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R3 !!! Regidx Ra0)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R3).
    assert (HR3a0 : R3 !!! Regidx Ra0 = bnode k).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate]. exact Ha0. }
    assert (Hlk16 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
                    = sign_extend' 64 (mword_of_int 16 : mword 12))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HR4a0 : R4 !!! Regidx Ra0 = buf_lock (bnode k)).
    { rewrite /R4 upd_eq. rewrite HR3a0. unfold regval_into_reg, buf_lock.
      rewrite Hlk16. reflexivity. }
    assert (Hpp0e : add_vec_int (mword_of_int (BW + 0x0c) : mword 64) 2 = mword_of_int (BW + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e jal ra,holdingsleep ===== *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (BW + 0x0e)) Rra (mword_of_int 0x1330 : mword 21)
              R4 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (BW + 0x0e) : mword 64) 4)]> R4).
    assert (Htgthsl : add_vec (mword_of_int (BW + 0x0e) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1330 : mword 21))
                      = mword_of_int KernelSyms.holdingsleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgthsl) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAtp : mA !!! Regidx Rtp = cid_word).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Htp | vm_compute; discriminate]. }
    assert (HmAa0 : mA !!! Regidx Ra0 = buf_lock (bnode k)).
    { rewrite /mA upd_ne; [| vm_compute; discriminate]. exact HR4a0. }
    assert (HmAs1 : mA !!! Regidx Rs1 = bnode k).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HR3s1. }
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (BW + 0x0e) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    assert (HKhsl : (16 <= K - 4)%nat) by lia.
    iApply (HSL.wp_holdingsleep_sconf γ Φ (fst (bn_slk bn k)) (snd (bn_slk bn k))
              "buffer"%string (bown bn k) mA pj pidv (K - 4)%nat eb C HmAtp HKhsl
              with "Hcg Hcnt Htext Hpc [] Hstok [Hpid] Hpanic Hppid [-]").
    { iEval (rewrite HmAa0). iExact "Hslk". }
    { iEval (rewrite HmAa0). iExact "Hpid". }
    iIntros (mH) "%Hhs Hcg Hcnt Hpc Hstok Hpid Hppid".
    destruct Hhs as [Hcs1 Hha0].
    iEval (rewrite HmAa0) in "Hpid".
    assert (Hpc12 : ret_pc (mA !!! Regidx Rra) = mword_of_int (BW + 0x12)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc12) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmHsp : mH !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (HmHtp : mH !!! Regidx Rtp = cid_word)
      by (rewrite (callee_saved_lookup Hcs1_cs (mword_of_int 4) ltac:(vm_compute; reflexivity)); exact HmAtp).
    assert (HmHs1 : mH !!! Regidx Rs1 = bnode k)
      by (rewrite (callee_saved_lookup Hcs1_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmAs1).
    (* ===== +0x12 c.beqz a0 : a0 = 1, the panic arm is dead ===== *)
    iPoseProof (bwi_12 with "Htext") as "Hi12".
    iPoseProof (bwi_14 with "Htext") as "Hi14".
    iPoseProof (bwi_16 with "Htext") as "Hi16".
    iPoseProof (bwi_18 with "Htext") as "Hi18".
    assert (Hbeqz : eq_vec (mH !!! Regidx Ra0) zero_reg = false)
      by (rewrite Hha0; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (BW + 0x12)) (mword_of_int 10 : mword 8)
              (Cregidx (mword_of_int 2)) Ra0 mH (K - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hbeqz
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (BW + 0x12) : mword 64) 2 = mword_of_int (BW + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.li a1,1 : the WRITE flag *)
    assert (Hli1 : add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
                   = (mword_of_int 1 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (BW + 0x14)) Ra1 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) mH (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hli1
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx Ra1 := regval_into_reg (mword_of_int 1 : mword 64)]> mH).
    assert (HD1s1 : D1 !!! Regidx Rs1 = bnode k)
      by (rewrite /D1 upd_ne; [exact HmHs1 | vm_compute; discriminate]).
    assert (Hpp16 : add_vec_int (mword_of_int (BW + 0x14) : mword 64) 2 = mword_of_int (BW + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv a0,s1 : a0 := b *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (BW + 0x16)) Ra0 Rs1
              D1 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    set (D2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D1 !!! Regidx Rs1))]> D1).
    assert (Hpp18 : add_vec_int (mword_of_int (BW + 0x16) : mword 64) 2 = mword_of_int (BW + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* ===== +0x18 jal ra,virtio_disk_rw ===== *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (BW + 0x18)) Rra (mword_of_int 0x2b2c : mword 21)
              D2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi18 [-]").
    iIntros "Hcg Hpc".
    set (D3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (BW + 0x18) : mword 64) 4)]> D2).
    assert (Htgtrw : add_vec (mword_of_int (BW + 0x18) : mword 64)
                       (sign_extend' 64 (mword_of_int 0x2b2c : mword 21))
                     = mword_of_int KernelSyms.virtio_disk_rw)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrw) in "Hpc".
    assert (HD3a0 : D3 !!! Regidx Ra0 = bnode k).
    { rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1s1. apply add_vec_zero_l. }
    assert (HD3a1 : D3 !!! Regidx Ra1 = (mword_of_int 1 : mword 64)).
    { rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [| vm_compute; discriminate].
      rewrite /D1 upd_eq. reflexivity. }
    assert (HD3thr : forall c : mword 5, is_cs_idx c = true ->
                       D3 !!! Regidx c = mH !!! Regidx c).
    { intros c Hcs.
      rewrite /D3 upd_ne; [| regne].
      rewrite /D2 upd_ne; [| regne].
      rewrite /D1 upd_ne; [reflexivity | regne]. }
    assert (HD3sp : D3 !!! Regidx csp_rs1 = spr)
      by (rewrite (HD3thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HmHsp).
    assert (HD3tp : D3 !!! Regidx Rtp = cid_word)
      by (rewrite (HD3thr (mword_of_int 4) ltac:(vm_compute; reflexivity)); exact HmHtp).
    assert (HD3ra : D3 !!! Regidx Rra = add_vec_int (mword_of_int (BW + 0x18) : mword 64) 4)
      by (rewrite /D3; apply upd_eq).
    assert (Hkdata : forall kk : nat, (kk < 1024)%nat ->
              addr_is_kdata (pa_add (b_data (D3 !!! Regidx Ra0)) kk)).
    { intros kk Hkk. rewrite HD3a0. exact (bw_data_kdata k kk Hk Hkk). }
    assert (HKrw : (K_virtio_disk_rw <= K - 4)%nat)
      by (unfold K_virtio_disk_rw; lia).
    iApply (RW.wp_virtio_disk_rw_sconf γ Φ γs j γl γu γd γk pd pav pu D3
              (K - 4)%nat eb C bno (mword_of_int 0 : mword 32) bs bs_disk
              HKrw Hbno Hkdata HD3tp Hj Hgl
              with "Hcg Hcnt Hpay Htext Hpc Hpanic Hprocs Hoctx Hvc Hdev Hgeom Hdlock [Hbuf] Hdisk [-]").
    { iEval (rewrite HD3a0). iExact "Hbuf". }
    iIntros (mR) "%Hcs2 Hcg Hcnt Hpay Hpc Hoctx Hvc Hbuf Hdisk".
    iEval (rewrite (bw_wr_true _ bs bs_disk HD3a1)) in "Hbuf".
    iEval (rewrite (bw_wr_true _ bs bs_disk HD3a1)) in "Hdisk".
    iEval (rewrite HD3a0) in "Hbuf".
    assert (Hpc1c : ret_pc (D3 !!! Regidx Rra) = mword_of_int (BW + 0x1c)).
    { rewrite HD3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc1c) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    (* ===== EPILOGUE ===== *)
    iPoseProof (bwi_1c with "Htext") as "Hi1c".
    iPoseProof (bwi_1e with "Htext") as "Hi1e".
    iPoseProof (bwi_20 with "Htext") as "Hi20".
    iPoseProof (bwi_22 with "Htext") as "Hi22".
    iPoseProof (bwi_24 with "Htext") as "Hi24".
    assert (HmRsp : mR !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HD3sp).
    iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
    iEval (rewrite HspR1) in "Hr8".  iEval (rewrite HspR1) in "Hg4".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (BW + 0x1c)) (mword_of_int 3 : mword 6) Rra
              mR (K - 4)%nat (R1 !!! Regidx Rra)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c [Hr24] [-]").
    { iEval (rewrite HmRsp). iExact "Hr24". }
    iIntros "Hcg Hpc Hr24".
    iEval (rewrite HmRsp) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> mR).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact HmRsp | vm_compute; discriminate]).
    assert (Hpp1e : add_vec_int (mword_of_int (BW + 0x1c) : mword 64) 2 = mword_of_int (BW + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (BW + 0x1e)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (R1 !!! Regidx Rs0)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [Hr16] [-]").
    { iEval (rewrite HP1sp). iExact "Hr16". }
    iIntros "Hcg Hpc Hr16".
    iEval (rewrite HP1sp) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp20 : add_vec_int (mword_of_int (BW + 0x1e) : mword 64) 2 = mword_of_int (BW + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (BW + 0x20)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (R1 !!! Regidx Rs1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 [Hr8] [-]").
    { iEval (rewrite HP2sp). iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    iEval (rewrite HP2sp) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp22 : add_vec_int (mword_of_int (BW + 0x20) : mword 64) 2 = mword_of_int (BW + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HP3sp. unfold spr, sp0. apply frame_cancel_32. }
    assert (Hpop : P3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP3sp. unfold spr, sp0, pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (BW + 0x22)) (mword_of_int 2 : mword 6)
              P3 (K - 4)%nat 4 Hpop with "Hcg Hpc Hi22 Hframe4 [-]").
    iIntros "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P3 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3) with P4.
    assert (Hpp24 : add_vec_int (mword_of_int (BW + 0x22) : mword 64) 2 = mword_of_int (BW + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    assert (HP4ra : P4 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (BW + 0x24)) Rra P4 K
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi24 [-]").
    iIntros "Hcg Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra) = ret_tgt) by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! P4 with "[%] Hcg Hcnt Hpay Hpc Hoctx Hvc Hppid [Hstok Hpid Hvalid Hbdev Hbuf] Hdisk").
    { (* callee_saved m P4 *)
      assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
                P4 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9.
        rewrite /P4 upd_ne; [| regne].
        rewrite /P3 upd_ne; [| regne].
        rewrite /P2 upd_ne; [| regne].
        rewrite /P1 upd_ne; [| regne].
        rewrite (callee_saved_lookup Hcs2_cs c Hcs).
        rewrite (HD3thr c Hcs).
        rewrite (callee_saved_lookup Hcs1_cs c Hcs).
        rewrite /mA upd_ne; [| regne].
        rewrite /R4 upd_ne; [| regne].
        rewrite /R3 upd_ne; [| regne].
        rewrite /R2 upd_ne; [| regne].
        rewrite /R1 upd_ne; [reflexivity | regne]. }
      unfold callee_saved.
      assert (Hc2 : P4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
      { rewrite /P4 upd_eq. rewrite HP3sp. unfold regval_into_reg, spr, sp0.
        apply frame_cancel_32. }
      assert (Hc8 : P4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /P2 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      assert (Hc9 : P4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      assert (Hc4 : P4 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5))
        by (apply Hthread; vm_compute; first [reflexivity | discriminate]).
      repeat split;
        first [ exact Hc2 | exact Hc4 | exact Hc8 | exact Hc9
              | apply Hthread; vm_compute; first [reflexivity | discriminate] ]. }
    (* the handle, rebuilt: valid and the dev half were framed across both
       calls, the token and pid came back from holdingsleep, the bundle from
       virtio_disk_rw. *)
    rewrite /bio_locked /bpa.
    iSplitR; [by iPureIntro|].
    iFrame "Hstok Hpid Hvalid Hbdev Hbuf".
  Qed.

End ProofBwrite.

End BwriteProof.
