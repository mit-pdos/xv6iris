(* ProofInitlog.v -- initlog over the SIE-agnostic sconf world: THE LOG
   LAYER'S CONSTRUCTOR, in its clean-image (stage-2) form.

     void initlog(int dev, struct superblock *sb) {
       initlock(&log.lock, "log");
       log.start = sb->logstart;
       log.dev   = dev;
       recover_from_log();            // INLINED, and read_head with it
     }

   THE SHAPE OF THE PROOF.  Straight line: five calls (initlock, bread,
   brelse, install_trans, write_head), four stores into [struct log], one
   load out of the buffer's header word, and ONE branch -- the [blez] at
   +0x40, which the clean-image premise [hdr_n bs_hdr = 0] makes TAKEN, so
   the header-copy do-while at +0x44..+0x5a is dead code and never appears
   in the proof at all.

   * DELAYED SEALING.  The "log" spinlock's resource ([LogInv.log_res])
     does not exist at the initlock call: it holds the very [lh] cells that
     install_trans and write_head are handed a few instructions later, and
     it is indexed by a [log_names] record whose first field IS the lock's
     own ghost name.  So the proof uses [WpLock.newlock_delayed]: the gname
     is chosen right after initlock returns (together with the ledger's, via
     [LogInv.log_ledger_alloc]), and the wand it hands back is spent at the
     very END, once [log_res] has been assembled out of everything initlog
     was given.  This is [SpecProcinit.procs_inv_alloc]'s trick applied to a
     single lock.

   * THE FROZEN CELLS ARE PERSISTED BEFORE THE FIRST CALLEE.  log.start and
     log.dev are written at +0x2c / +0x30 and then discarded to
     [DfracDiscarded] ([RiscvPtsto.word4_pointsto_persist]) on the spot --
     which is exactly [LogInv.log_frozen], the context both committer-only
     helpers take (they run with no lock held, and at their call sites there
     is no lock yet).

   * THE HEADER WORD IS READ THROUGH A FOUR-BYTE BRIDGE.  The [c.lw a2,88(a0)]
     at +0x3a reads [buf->data + 0], i.e. the first little-endian word of the
     block -- which is [LogInv.hdr_n] by definition.  [il_hdr_acc] borrows
     that word out of [buf_own]'s byte list and gives it back unchanged (the
     buffer is never written here), so the handle brelse gets is the one
     bread returned, byte for byte.  With [hdr_n bs_hdr = 0] the loaded word
     is 0, which is what kills the copy loop and what makes the
     [install_trans(1)] call legal (its stage-2 premise is
     [recovering = false \/ n = 0]).

   * SLOT ACCOUNTING.  34 = 1 + 33 in, one unit to bread and back from
     brelse, two to install_trans and 2 + |W| = 2 back, one to write_head and
     back: 34 out, split 32 (the batch's pool at n = 0) + 2 (the caller's
     working pair).

   HART-GENERIC PROTOCOL.  Every callee returns through [wp_next b pj (fun
   CID => ...)], so the caller's own continuation is re-anchored at each
   crossing with [WpSconfVc.wp_next_shift] and the [cpu_own] with
   [CpuOwn.cpu_own_transport]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import KernelDataInv.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfVc.
Require Import WpSmodeIntr.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import FdSlots.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import CodeInitlog.
Require Import SpecInitlock.
Require Import SpecBread SpecBrelse.
Require Import SpecInstallTrans SpecWriteHead.
Require Import SpecInitlog.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure vocabulary.  All of it over plain [Z]/[nat] or closed words, so   *)
(*  no solver ever runs inside the WP context.                            *)
(* ===================================================================== *)

(* ---- the header's [n] field as a WORD: the first little-endian 32-bit
   word of the block, which is what [c.lw a2,88(a0)] loads. ---- *)
Definition il_hdrw (bs : list (bv 8)) : SailStdpp.Values.mword 32 :=
  Z_to_bv 32 (hdr_n bs).

Lemma il_hdrw_zero (bs : list (bv 8)) :
  hdr_n bs = 0 -> il_hdrw bs = (mword_of_int 0 : SailStdpp.Values.mword 32).
Proof.
  intro H. rewrite /il_hdrw H. apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the alignment of the buffer's first data word: [bcache]'s geometry,
   then [ByteBuf.bb_align_z] (ProofWriteHead's [wh_align4] at q = 0) ---- *)
Lemma il_align_arith (kk : Z) :
  0 <= kk -> kk < 30 ->
  (2147582376 + 1112 * kk + 88) `mod` 4 = 0
  /\ 0 <= 2147582376 + 1112 * kk + 88
  /\ 2147582376 + 1112 * kk + 88 < 18446744073709551616.
Proof.
  intros H1 H2. split_and!; [| lia | lia].
  replace (2147582376 + 1112 * kk + 88)
    with ((536895616 + 278 * kk) * 4) by lia.
  apply Z_mod_mult.
Qed.

Lemma il_align4 (k : nat) : (k < NBUF)%nat ->
  is_aligned_paddr (Physaddr (b_data (bnode k))) 4 = true.
Proof.
  intros Hk.
  unfold b_data.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite RiscvExtras.uint_unsigned.
  rewrite ByteCursor.pa_add_unsigned.
  rewrite (bnode_unsigned k Hk).
  unfold buf_base, buf_stride, KernelSyms.bcache.
  destruct (il_align_arith (Z.of_nat k)
              ltac:(lia) ltac:(unfold NBUF in Hk; lia))
    as (Hm & Hlo & Hhi).
  replace (0x80018190 + 24 + 1112 * Z.of_nat k + Z.of_nat 88)
    with (2147582376 + 1112 * Z.of_nat k + 88) by lia.
  apply bb_align_z; assumption.
Qed.

(* ---- the sign-extended immediates initlog forms ---- *)
Lemma il_s20 : sign_extend' 64 (mword_of_int 20 : SailStdpp.Values.mword 12)
               = (mword_of_int 20 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s24 : sign_extend' 64 (mword_of_int 24 : SailStdpp.Values.mword 12)
               = (mword_of_int 24 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s36 : sign_extend' 64 (mword_of_int 36 : SailStdpp.Values.mword 12)
               = (mword_of_int 36 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s44 : sign_extend' 64 (mword_of_int 44 : SailStdpp.Values.mword 12)
               = (mword_of_int 44 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s88 : sign_extend' 64 (mword_of_int 88 : SailStdpp.Values.mword 12)
               = (mword_of_int 88 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- the [struct log] cell addresses the code forms ---- *)
Lemma il_l_start : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 24 : SailStdpp.Values.mword 64) = l_start.
Proof. reflexivity. Qed.
Lemma il_l_dev : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 36 : SailStdpp.Values.mword 64) = l_dev.
Proof. reflexivity. Qed.
Lemma il_l_lhn : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 44 : SailStdpp.Values.mword 64) = lh_n_pa.
Proof. reflexivity. Qed.

Lemma il_hdr_addr (a : SailStdpp.Values.mword 64) :
  add_vec a (mword_of_int 88 : SailStdpp.Values.mword 64) = b_data a.
Proof. reflexivity. Qed.

(* ===================================================================== *)

Module InitlogProof (Initlock : INITLOCK) (Bread : BREAD) (Brelse : BRELSE)
                    (InstallTrans : INSTALL_TRANS) (WriteHead : WRITE_HEAD)
  : INITLOG.


Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac ilidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section InitlogDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.

  (* BORROW the block's first word out of its byte list, and give it back.
     The window vocabulary is ByteBuf's ([bb_bytes_of_list] to trade the
     list for a named window, [bb_word4_acc] to borrow the aligned cell at
     offset 0); all this lemma adds is that the word there IS [il_hdrw].
     initlog never WRITES the buffer, so the give-back is at the same word,
     and [ByteBuf.bb_set_mk] -- writing back what was read changes nothing --
     is what says the handle brelse gets is bread's, byte for byte. *)
  Lemma il_hdr_acc (a : Arch.pa) (bs : list (bv 8)) :
    (4 <= length bs)%nat ->
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x) -∗
    a ↦₄ il_hdrw bs ∗
    (a ↦₄ il_hdrw bs -∗ ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x)).
  Proof.
    intros Hlen Hal.
    assert (Ha0 : pa_add a 0%nat = a) by apply RiscvExtras.pa_add_0.
    assert (Hmk : bb_mk (fun j => bs !!! j) 0%nat = il_hdrw bs).
    { rewrite /bb_mk /il_hdrw /hdr_n.
      destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in Hlen;
        try (exfalso; lia).
      reflexivity. }
    rewrite (bb_bytes_of_list a bs).
    iIntros "Hw".
    iDestruct (bb_word4_acc a (length bs) 0%nat (length bs - 4)%nat
                 (fun j => bs !!! j) ltac:(lia)
                 ltac:(rewrite Ha0; exact Hal) with "Hw") as "[Hc Hback]".
    rewrite Ha0 Hmk.
    iSplitL "Hc"; [iExact "Hc"|].
    iIntros "Hc".
    iDestruct ("Hback" $! (il_hdrw bs) with "Hc") as "Hw".
    (* the opening rewrite already put the give-back's window in [bb_bytes]
       form too, so only the unfolding is left here *)
    rewrite /bb_bytes.
    iApply (big_sepL_mono with "Hw"). intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite -Hmk (bb_set_mk (fun j => bs !!! j) 0%nat i). reflexivity.
  Qed.

  (* an EMPTY indexed big-op is [emp]; naming it keeps the call sites free
     of bracketed spec-pattern goals *)
  Lemma il_bigL_nil {A : Type} (Psi : nat -> A -> iProp Σ) :
    ⊢ ([∗ list] i ↦ x ∈ ([] : list A), Psi i x).
  Proof. first [ done | rewrite big_sepL_nil; done ]. Qed.

  (* the client's own [fsblock] half against the handle's machinery half
     pins the bytes bread returned -- for either payload polarity *)
  Lemma il_pay_agree (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32) (z : Z)
      (bs bsl bsd : list (bv 8)) (d : bool) :
    uint bno = z ->
    fsblock γfs z bs -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd d -∗ ⌜bsl = bs⌝.
  Proof.
    intros <-. rewrite /bio_pay /fs_view /=. destruct d.
    - iIntros "Hc [Hm _]". iApply (fsblock_mdirty_agree with "Hc Hm").
    - iIntros "Hc [Hm _]". iApply (fsblock_mclean_agree with "Hc Hm").
  Qed.

End InitlogDefs.

(* ===================================================================== *)

Section ProofInitlog.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_initlog_sconf (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (sb : mword 64)
      (bs_hdr : list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (vlock : mword 32) (vname vcpu : mword 64)
      (v_start v_dev v_nc v_n : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_initlog_sconf_body Φ γs j γl γu γd γk pd pav pu bn γfs
                            cov logstart dev sb bs_hdr L D
                            vlock vname vcpu v_start v_dev v_nc v_n
                            pidv dq dqs m K eb C b.
  Proof.
    cbv beta delta [wp_initlog_sconf_body].
    intros pcE pj ret_tgt c_name c_cpu HK Hgeom Hj Hgl Heb Hhdr0 Hma0 Hma1.
    destruct Hgeom as [Hcovok Hlogsub].
    subst eb.
    unfold K_initlog in HK.
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hpanic #Hbio #Hseam #Hcert Hmirf
              Hppid #Hprocs #Hscheds
              Hpark #Hdevi #Hdgeom #Hdlock Hsbf Hlock Hname Hcpu
              Hstc Hdevc Hout Hcmt Hnc Hncell Hblk HLauth HDauth Hcovf Hfsb
              Hslotsfs Hslots Hcont".
    (* ---- the header block is covered, and its number is a small int ---- *)
    assert (Hhdrcov : logstart ∈ cov).
    { apply Hlogsub. rewrite /log_region_set.
      apply elem_of_union_r. apply elem_of_singleton. reflexivity. }
    destruct (Hcovok logstart Hhdrcov) as [Hls0 Hls1].
    assert (Huint : uint (mword_of_int logstart : mword 32) = logstart).
    { rewrite bb_uint32. apply moi32_small.
      change (2 ^ 32)%Z with 4294967296%Z.
      change (2 ^ 31)%Z with 2147483648%Z in Hls1. lia. }
    assert (Hbnolt : (uint (mword_of_int logstart : mword 32) < 2147483648)%Z).
    { rewrite Huint. change (2 ^ 31)%Z with 2147483648%Z in Hls1. lia. }
    assert (Hcovin : uint (mword_of_int logstart : mword 32)
                     ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite Huint; exact Hhdrcov).
    (* ---- the "log" string literal, out of the data image ---- *)
    assert (Hlogs : forall jj bt, cstring_bytes "log"%string !! jj = Some bt ->
                     KernelData.kernel_data !! (log_name_str + Z.of_nat jj)%Z
                     = Some bt).
    { intros jj bt Hjj.
      do 4 (destruct jj as [|jj];
            [vm_compute in Hjj; injection Hjj as <-; vm_compute; reflexivity |]);
      vm_compute in Hjj; discriminate. }
    iPoseProof (kernel_data_string log_name_str "log"%string
                  (mword_of_int log_name_str : mword 64) eq_refl
                  ltac:(unfold text_end, log_name_str; lia) Hlogs
                  with "Hkdata") as "#Hstr".
    (* ---- the frame geometry (6 slots; ra@40 s0@32 s1@24 s2@16 s3@8) ---- *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (ili_00 with "Htext") as "Hi00".
    iPoseProof (ili_02 with "Htext") as "Hi02".
    iPoseProof (ili_04 with "Htext") as "Hi04".
    iPoseProof (ili_06 with "Htext") as "Hi06".
    iPoseProof (ili_08 with "Htext") as "Hi08".
    iPoseProof (ili_0a with "Htext") as "Hi0a".
    iPoseProof (ili_0c with "Htext") as "Hi0c".
    iPoseProof (ili_0e with "Htext") as "Hi0e".
    iPoseProof (ili_10 with "Htext") as "Hi10".
    iPoseProof (ili_12 with "Htext") as "Hi12".
    iPoseProof (ili_16 with "Htext") as "Hi16".
    iPoseProof (ili_1a with "Htext") as "Hi1a".
    iPoseProof (ili_1e with "Htext") as "Hi1e".
    iPoseProof (ili_22 with "Htext") as "Hi22".
    iPoseProof (ili_24 with "Htext") as "Hi24".
    (* ===== PROLOGUE ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    iApply (wp_caddi16sp_push_s_sconf Φ pcE (mword_of_int 61 : mword 6) m K 6 b
              ltac:(lia) Hspr6 with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vra0) "Hc1". iDestruct "S2" as (vs00) "Hc2".
    iDestruct "S3" as (vs10) "Hc3". iDestruct "S4" as (vs20) "Hc4".
    iDestruct "S5" as (vs30) "Hc5". iDestruct "S6" as (vs60) "Hc6".
    assert (Hra_v : R1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0_v : R1 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1_v : R1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2_v : R1 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs3_v : R1 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1a0 : R1 !!! Regidx Ra0 = sign_extend' 64 dev).
    { rewrite /R1 upd_ne; [exact Hma0 | vm_compute; discriminate]. }
    assert (HR1a1 : R1 !!! Regidx Ra1 = sb).
    { rewrite /R1 upd_ne; [exact Hma1 | vm_compute; discriminate]. }
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.initlog + 0x02))
      by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat vra0 b with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    iEval (rgne) in "Hc1". iEval (rewrite HspR1 Hb1 Hra_v) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat vs00 b with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    iEval (rgne) in "Hc2". iEval (rewrite HspR1 Hb2 Hs0_v) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6)%nat vs10 b with "Hcg Hpc Hi06 [Hc3] [-]").
    { iEval (rewrite HspR1 Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc3".
    iEval (rgne) in "Hc3". iEval (rewrite HspR1 Hb3 Hs1_v) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,16(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat vs20 b with "Hcg Hpc Hi08 [Hc4] [-]").
    { iEval (rewrite HspR1 Hb4). iExact "Hc4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc4".
    iEval (rgne) in "Hc4". iEval (rewrite HspR1 Hb4 Hs2_v) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,8(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (K - 6)%nat vs30 b with "Hcg Hpc Hi0a [Hc5] [-]").
    { iEval (rewrite HspR1 Hb5). iExact "Hc5". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc5".
    iEval (rgne) in "Hc5". iEval (rewrite HspR1 Hb5 Hs3_v) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x0c)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x0e)) Rs1 Ra0
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR2a0 : R2 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /R2 upd_ne; [exact HR1a0 | vm_compute; discriminate]).
    assert (HR3s1 : R3 !!! Regidx Rs1 = sign_extend' 64 dev).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a0. apply add_vec_zero_l. }
    assert (HR3a1 : R3 !!! Regidx Ra1 = sb).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HR1a1 | vm_compute; discriminate]. }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.mv s3,a1 *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x10)) Rs3 Ra1
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R4 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R3 Ra1))]> R3).
    assert (HR4s3 : R4 !!! Regidx Rs3 = sb).
    { rewrite /R4 upd_eq. rgne. rewrite HR3a1. apply add_vec_zero_l. }
    assert (HR4s1 : R4 !!! Regidx Rs1 = sign_extend' 64 dev)
      by (rewrite /R4 upd_ne; [exact HR3s1 | vm_compute; discriminate]).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 auipc s2,0x1e *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x12)) Rs2 (mword_of_int 30 : mword 20)
              R4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (R5 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.initlog + 0x12) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R4).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 addi s2,s2,1966 : s2 := &log *)
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x16)) Rs2 Rs2
              (mword_of_int 1946 : mword 12) R5 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (R6 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (rget R5 Rs2)
                     (sign_extend' 64 (mword_of_int 1946 : mword 12)))]> R5).
    assert (HR6s2 : R6 !!! Regidx Rs2 = log_addr).
    { rewrite /R6 upd_eq. rgne. rewrite /R5 upd_eq /log_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x16) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a auipc a1,0x4 *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x1a)) Ra1 (mword_of_int 4 : mword 20)
              R6 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (R7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.initlog + 0x1a) : mword 64)
                     (auipc_off (mword_of_int 4 : mword 20)))]> R6).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x1a) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e addi a1,a1,-1658 : a1 := "log" *)
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x1e)) Ra1 Ra1
              (mword_of_int 2418 : mword 12) R7 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (R8 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget R7 Ra1)
                     (sign_extend' 64 (mword_of_int 2418 : mword 12)))]> R7).
    assert (HR8a1 : R8 !!! Regidx Ra1 = (mword_of_int log_name_str : mword 64)).
    { rewrite /R8 upd_eq. rgne. rewrite /R7 upd_eq /log_name_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HR8s2 : R8 !!! Regidx Rs2 = log_addr).
    { rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [exact HR6s2 | vm_compute; discriminate]. }
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x1e) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.mv a0,s2 *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x22)) Ra0 Rs2
              R8 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [-]").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (R9 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R8 Rs2))]> R8).
    assert (HR9a0 : R9 !!! Regidx Ra0 = log_addr).
    { rewrite /R9 upd_eq. rgne. rewrite HR8s2. apply add_vec_zero_l. }
    assert (HR9a1 : R9 !!! Regidx Ra1 = (mword_of_int log_name_str : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8a1 | vm_compute; discriminate]).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 jal ra,initlock ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x24)) Rra
              (mword_of_int 2084856 : mword 21) R9 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi24 [-]").
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (RA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x24) : mword 64) 4)]> R9).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.initlog + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084856 : mword 21))
                     = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HRAa0 : RA !!! Regidx Ra0 = log_addr)
      by (rewrite /RA upd_ne; [exact HR9a0 | vm_compute; discriminate]).
    assert (HRAa1 : RA !!! Regidx Ra1 = (mword_of_int log_name_str : mword 64))
      by (rewrite /RA upd_ne; [exact HR9a1 | vm_compute; discriminate]).
    assert (HRAra : RA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x24) : mword 64) 4)
      by (rewrite /RA; apply upd_eq).
    assert (HRAsp : RA !!! Regidx csp_rs1 = spr).
    { rewrite /RA upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]. }
    assert (HRAcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              RA !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /RA upd_ne; [| regne]. rewrite /R9 upd_ne; [| regne].
      rewrite /R8 upd_ne; [| regne]. rewrite /R7 upd_ne; [| regne].
      rewrite /R6 upd_ne; [| regne]. rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne]. rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HRAs1 : RA !!! Regidx Rs1 = sign_extend' 64 dev).
    { rewrite /RA upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [exact HR4s1 | vm_compute; discriminate]. }
    assert (HRAs2 : RA !!! Regidx Rs2 = log_addr)
      by (rewrite /RA upd_ne; [| vm_compute; discriminate];
          rewrite /R9 upd_ne; [exact HR8s2 | vm_compute; discriminate]).
    assert (HRAs3 : RA !!! Regidx Rs3 = sb).
    { rewrite /RA upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4s3 | vm_compute; discriminate]. }
    iApply (Initlock.wp_initlock_sconf Φ RA vlock vname vcpu "log"%string
              (K - 6)%nat b pj ltac:(lia)
              with "Hcg Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HRAa1). iExact "Hstr". }
    { iEval (rewrite HRAa0). iExact "Hlock". }
    { iEval (rewrite HRAa0). iExact "Hname". }
    { iEval (rewrite HRAa0). iExact "Hcpu". }
    iIntros (CID16 Hs16 mil) "Hcg Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HRAa0) in "Hlock".
    iEval (rewrite HRAa0 HRAa1) in "Hlname".
    iEval (rewrite HRAa0) in "Hcpu".
    assert (Hpcil : ret_pc (RA !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x28)).
    { rewrite HRAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full.
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hilcs_full csp_rs1 ltac:(vm_compute; reflexivity));
          exact HRAsp).
    assert (Hmils1 : mil !!! Regidx Rs1 = sign_extend' 64 dev)
      by (rewrite (callee_saved_lookup Hilcs_full Rs1 ltac:(vm_compute; reflexivity));
          exact HRAs1).
    assert (Hmils2 : mil !!! Regidx Rs2 = log_addr)
      by (rewrite (callee_saved_lookup Hilcs_full Rs2 ltac:(vm_compute; reflexivity));
          exact HRAs2).
    assert (Hmils3 : mil !!! Regidx Rs3 = sb)
      by (rewrite (callee_saved_lookup Hilcs_full Rs3 ltac:(vm_compute; reflexivity));
          exact HRAs3).
    assert (Hmilcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mil !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hilcs_full c Hcs).
      exact (HRAcs c Hcs N2 N8 N9 N18 N19). }
    (* ===== THE DELAYED SEAL: pick the lock's gname and the ledger's now,
       and keep the wand that will take [log_res] at the very end. ===== *)
    iApply fupd_wp.
    iMod (lock_name_intro with "Hstr Hlname") as "#Hlnm".
    iMod (log_ledger_alloc) as (γops) "Hops".
    iMod (newlock_delayed ⊤ log_addr "log"%string with "Hlnm Hlock Hcpu")
      as (γlk) "Hmk".
    iModIntro.
    (* ===== +0x28 lw a1,20(s3) : a1 := sb->logstart ===== *)
    iPoseProof (ili_28 with "Htext") as "Hi28".
    iPoseProof (ili_2c with "Htext") as "Hi2c".
    iPoseProof (ili_30 with "Htext") as "Hi30".
    iPoseProof (ili_34 with "Htext") as "Hi34".
    iPoseProof (ili_36 with "Htext") as "Hi36".
    assert (Hsbad : add_vec (rget mil Rs3)
                      (sign_extend' 64 (mword_of_int 20 : mword 12))
                    = pa_add sb 20%nat).
    { rgne. rewrite Hmils3 il_s20. reflexivity. }
    iEval (rewrite -Hsbad) in "Hsbf".
    iApply (wp_lw_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x28)) Ra1 Rs3
              (mword_of_int 20 : mword 12) mil (K - 6)%nat
              (mword_of_int logstart : mword 32) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 Hsbf [-]").
    iIntros (CID17 Hs17) "Hcg Hpc Hsbf".
    iEval (rewrite Hsbad) in "Hsbf".
    set (T1 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int logstart : mword 32))]> mil).
    assert (HT1a1 : T1 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /T1; apply upd_eq).
    assert (HT1s1 : T1 !!! Regidx Rs1 = sign_extend' 64 dev)
      by (rewrite /T1 upd_ne; [exact Hmils1 | vm_compute; discriminate]).
    assert (HT1s2 : T1 !!! Regidx Rs2 = log_addr)
      by (rewrite /T1 upd_ne; [exact Hmils2 | vm_compute; discriminate]).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = spr)
      by (rewrite /T1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
    assert (HT1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              T1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /T1 upd_ne; [| regne]. exact (Hmilcs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x28) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* ===== +0x2c sw a1,24(s2) : log.start := sb->logstart ===== *)
    assert (Hstad : add_vec (rget T1 Rs2)
                      (sign_extend' 64 (mword_of_int 24 : mword 12)) = l_start).
    { rgne. rewrite HT1s2 il_s24. apply il_l_start. }
    iEval (rewrite -Hstad) in "Hstc".
    iApply (wp_sw_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x2c)) Ra1 Rs2
              (mword_of_int 24 : mword 12) T1 (K - 6)%nat v_start b
              with "Hcg Hpc Hi2c Hstc [-]").
    iIntros (CID18 Hs18) "Hcg Hpc Hstc".
    iEval (rewrite Hstad) in "Hstc".
    assert (Hsv1 : trunc32 (rget T1 Ra1) = (mword_of_int logstart : mword 32)).
    { rgne. rewrite HT1a1. apply trunc32_sext64. }
    iEval (rewrite Hsv1) in "Hstc".
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x2c) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* ===== +0x30 sw s1,36(s2) : log.dev := dev ===== *)
    assert (Hdvad : add_vec (rget T1 Rs2)
                      (sign_extend' 64 (mword_of_int 36 : mword 12)) = l_dev).
    { rgne. rewrite HT1s2 il_s36. apply il_l_dev. }
    iEval (rewrite -Hdvad) in "Hdevc".
    iApply (wp_sw_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x30)) Rs1 Rs2
              (mword_of_int 36 : mword 12) T1 (K - 6)%nat v_dev b
              with "Hcg Hpc Hi30 Hdevc [-]").
    iIntros (CID19 Hs19) "Hcg Hpc Hdevc".
    iEval (rewrite Hdvad) in "Hdevc".
    assert (Hsv2 : trunc32 (rget T1 Rs1) = dev).
    { rgne. rewrite HT1s1. apply trunc32_sext64. }
    iEval (rewrite Hsv2) in "Hdevc".
    (* ---- FREEZE: the two cells go persistent, giving [log_frozen] ---- *)
    iMod (word4_pointsto_persist with "Hstc") as "#Hstp".
    iMod (word4_pointsto_persist with "Hdevc") as "#Hdvp".
    iAssert (log_frozen logstart dev) as "#Hfroz".
    { rewrite /log_frozen. iSplitL; [iExact "Hdvp" | iExact "Hstp"]. }
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x30) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* ===== +0x34 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x34)) Ra0 Rs1
              T1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [-]").
    iIntros (CID20 Hs20) "Hcg Hpc".
    set (T2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget T1 Rs1))]> T1).
    assert (HT2a0 : T2 !!! Regidx Ra0 = sign_extend' 64 dev).
    { rewrite /T2 upd_eq. rgne. rewrite HT1s1. apply add_vec_zero_l. }
    assert (HT2a1 : T2 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /T2 upd_ne; [exact HT1a1 | vm_compute; discriminate]).
    assert (HT2s2 : T2 !!! Regidx Rs2 = log_addr)
      by (rewrite /T2 upd_ne; [exact HT1s2 | vm_compute; discriminate]).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = spr)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (HT2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              T2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /T2 upd_ne; [| regne]. exact (HT1cs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* ===== +0x36 jal ra,bread ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x36)) Rra
              (mword_of_int 2092962 : mword 21) T2 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi36 [-]").
    iIntros (CID21 Hs21) "Hcg Hpc".
    set (T3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x36) : mword 64) 4)]> T2).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.initlog + 0x36) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092962 : mword 21))
                     = mword_of_int KernelSyms.bread)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HT3a0 : T3 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /T3 upd_ne; [exact HT2a0 | vm_compute; discriminate]).
    assert (HT3a1 : T3 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /T3 upd_ne; [exact HT2a1 | vm_compute; discriminate]).
    assert (HT3s2 : T3 !!! Regidx Rs2 = log_addr)
      by (rewrite /T3 upd_ne; [exact HT2s2 | vm_compute; discriminate]).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = spr)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (HT3ra : T3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x36) : mword 64) 4)
      by (rewrite /T3; apply upd_eq).
    assert (HT3cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              T3 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /T3 upd_ne; [| regne]. exact (HT2cs c Hcs N2 N8 N9 N18 N19). }
    (* one slot unit for the bread; the rest stay put *)
    assert (Hsplit1 : ((LOGBLOCKS + 2) + 2)%nat = (1 + 33)%nat)
      by (unfold LOGBLOCKS; lia).
    iEval (rewrite Hsplit1 bslots_op) in "Hslots".
    iDestruct "Hslots" as "[Hs1u Hslots]".
    iDestruct (cpu_own_transport CID CID21 0 true pj C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID21) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 6)%nat) by (unfold K_bread; lia).
    iApply (Bread.wp_bread_sconf Φ γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev (mword_of_int logstart : mword 32) dq
              T3 (K - 6)%nat true C b
              HKbr Hbnolt eq_refl Hcovin eq_refl Hj Hgl HT3a0 HT3a1 eq_refl
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hscheds Hpark
                    Hdevi Hdgeom Hdlock Hs1u [-]").
    iIntros (CID22 Hs22 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hpc Hpark Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc3a : ret_pc (T3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x3a)).
    { rewrite HT3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc3a) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs2 : mB !!! Regidx Rs2 = log_addr)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HT3s2).
    assert (HmBsp : mB !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HT3sp).
    assert (HmBcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mB !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HT3cs c Hcs N2 N8 N9 N18 N19). }
    (* ---- the handle: its bytes ARE the header block's logical content ---- *)
    rewrite /bio_locked /bio_held.
    iDestruct "Hheld" as
      "(%HA & %HB & %HC & Hslk & Hpid & Hvalid & Hbdev & Hbown & Hdisk & Hpay)".
    assert (Huintl : uint (mword_of_int logstart : mword 32)
                     = log_hdr_bno logstart)
      by (rewrite /log_hdr_bno; exact Huint).
    iDestruct (il_pay_agree bn γfs γd dev cov kk dev
                 (mword_of_int logstart : mword 32) (log_hdr_bno logstart)
                 bs_hdr bs0 bsd0 d0 Huintl with "Hfsb Hpay") as %->.
    rewrite /buf_own /bpa.
    iDestruct "Hbown" as "(Hbno & Hbdsk & %Hlen & Hby)".
    assert (Hal : is_aligned_paddr (Physaddr (b_data (bnode kk))) 4 = true)
      by (apply il_align4; exact HA).
    assert (Hlen4 : (4 <= length bs_hdr)%nat) by (rewrite Hlen; lia).
    iDestruct (il_hdr_acc (b_data (bnode kk)) bs_hdr Hlen4 Hal with "Hby")
      as "[Hword Hback]".
    (* ===== +0x3a c.lw a2,88(a0) : a2 := lh->n ( = 0 ) ===== *)
    iPoseProof (ili_3a with "Htext") as "Hi3a".
    iPoseProof (ili_3c with "Htext") as "Hi3c".
    iPoseProof (ili_40 with "Htext") as "Hi40".
    iPoseProof (ili_5e with "Htext") as "Hi5e".
    assert (Hhaddr : add_vec (rget mB Ra0)
                       (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = b_data (bnode kk)).
    { rgne. rewrite HmBa0 il_s88. apply il_hdr_addr. }
    iEval (rewrite (il_hdrw_zero bs_hdr Hhdr0)) in "Hword".
    iEval (rewrite -Hhaddr) in "Hword".
    iApply (wp_clw_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x3a)) Ra2 Ra0
              (mword_of_int 88 : mword 12) mB (K - 6)%nat
              (mword_of_int 0 : mword 32) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a Hword [-]").
    iIntros (CID23 Hs23) "Hcg Hpc Hword".
    iEval (rewrite Hhaddr) in "Hword".
    iEval (rewrite -(il_hdrw_zero bs_hdr Hhdr0)) in "Hword".
    iDestruct ("Hback" with "Hword") as "Hby".
    set (B1 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 0 : mword 32))]> mB).
    assert (HB1a2 : B1 !!! Regidx Ra2
                    = sign_extend' 64 (mword_of_int 0 : mword 32))
      by (rewrite /B1; apply upd_eq).
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HmBa0 | vm_compute; discriminate]).
    assert (HB1s2 : B1 !!! Regidx Rs2 = log_addr)
      by (rewrite /B1 upd_ne; [exact HmBs2 | vm_compute; discriminate]).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = spr)
      by (rewrite /B1 upd_ne; [exact HmBsp | vm_compute; discriminate]).
    assert (HB1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              B1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /B1 upd_ne; [| regne]. exact (HmBcs c Hcs N2 N8 N9 N18 N19). }
    (* rebuild the handle: the buffer was only READ *)
    iAssert (bio_locked bn (fs_view γfs γd dev cov) kk pidv dev
               (mword_of_int logstart : mword 32) bs_hdr bsd0 d0)
      with "[Hslk Hpid Hvalid Hbdev Hbno Hbdsk Hby Hdisk Hpay]" as "Hheld".
    { rewrite /bio_locked /bio_held /buf_own /bpa.
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hslk"; [iExact "Hslk"|]. iSplitL "Hpid"; [iExact "Hpid"|].
      iSplitL "Hvalid"; [iExact "Hvalid"|]. iSplitL "Hbdev"; [iExact "Hbdev"|].
      iSplitR "Hdisk Hpay".
      { iSplitL "Hbno"; [iExact "Hbno"|]. iSplitL "Hbdsk"; [iExact "Hbdsk"|].
        iSplitR; [iPureIntro; exact Hlen|]. iExact "Hby". }
      iSplitL "Hdisk"; [iExact "Hdisk"|]. iExact "Hpay". }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c sw a2,44(s2) : log.lh.n := 0 ===== *)
    assert (Hlhad : add_vec (rget B1 Rs2)
                      (sign_extend' 64 (mword_of_int 44 : mword 12)) = lh_n_pa).
    { rgne. rewrite HB1s2 il_s44. apply il_l_lhn. }
    iEval (rewrite -Hlhad) in "Hncell".
    iApply (wp_sw_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x3c)) Ra2 Rs2
              (mword_of_int 44 : mword 12) B1 (K - 6)%nat v_n b
              with "Hcg Hpc Hi3c Hncell [-]").
    iIntros (CID24 Hs24) "Hcg Hpc Hncell".
    iEval (rewrite Hlhad) in "Hncell".
    assert (Hsv3 : trunc32 (rget B1 Ra2) = (mword_of_int 0 : mword 32)).
    { rgne. rewrite HB1a2. apply trunc32_sext64. }
    iEval (rewrite Hsv3) in "Hncell".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x3c) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 blez a2 -> +0x5e : TAKEN (n = 0), the copy loop is dead ===== *)
    assert (Hcmp : zopz0zKzJ_s (zero_reg : mword 64) (rget B1 Ra2) = true).
    { rgne. rewrite HB1a2. vm_compute. reflexivity. }
    iApply (wp_bge_x0_taken_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x40))
              (mword_of_int 30 : mword 13) Ra2 B1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) Hcmp ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi40 [-]").
    iNext. iIntros (CID25 Hs25) "Hcg Hpc".
    assert (Htgt5e : add_vec (mword_of_int (KernelSyms.initlog + 0x40) : mword 64)
                       (sign_extend' 64 (mword_of_int 30 : mword 13))
                     = mword_of_int (KernelSyms.initlog + 0x5e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt5e) in "Hpc".
    (* ===== +0x5e jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x5e)) Rra
              (mword_of_int 2093186 : mword 21) B1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5e [-]").
    iIntros (CID26 Hs26) "Hcg Hpc".
    set (B2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64) 4)]> B1).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093186 : mword 21))
                     = mword_of_int KernelSyms.brelse)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HB2a0 : B2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1a0 | vm_compute; discriminate]).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spr)
      by (rewrite /B2 upd_ne; [exact HB1sp | vm_compute; discriminate]).
    assert (HB2ra : B2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64) 4)
      by (rewrite /B2; apply upd_eq).
    assert (HB2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              B2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /B2 upd_ne; [| regne]. exact (HB1cs c Hcs N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID22 CID26 0 true pj C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID21) (CIDb := CID26) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 6)%nat) by (unfold K_brelse; lia).
    iApply (Brelse.wp_brelse_sconf Φ γs bn (fs_view γfs γd dev cov) kk pidv dev
              (mword_of_int logstart : mword 32) dq B2 (K - 6)%nat true pj C
              bs_hdr bsd0 d0 b HKbl HA HB2a0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hheld [-]").
    iIntros (CID27 Hs27 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hs1u".
    assert (Hpc62 : ret_pc (B2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x62)).
    { rewrite HB2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc62) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRsp : mR !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HB2sp).
    assert (HmRcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mR !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HB2cs c Hcs N2 N8 N9 N18 N19). }
    (* ===== +0x62 c.li a0,1 ===== *)
    iPoseProof (ili_62 with "Htext") as "Hi62".
    iPoseProof (ili_64 with "Htext") as "Hi64".
    iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x62)) Ra0
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              mR (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi62 [-]").
    iIntros (CID28 Hs28) "Hcg Hpc".
    set (C1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> mR).
    assert (HC1a0 : C1 !!! Regidx Ra0 = (mword_of_int 1 : mword 64))
      by (rewrite /C1; apply upd_eq).
    assert (HC1sp : C1 !!! Regidx csp_rs1 = spr)
      by (rewrite /C1 upd_ne; [exact HmRsp | vm_compute; discriminate]).
    assert (HC1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              C1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /C1 upd_ne; [| regne]. exact (HmRcs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x62) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* ===== +0x64 jal ra,install_trans ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x64)) Rra
              (mword_of_int 2096848 : mword 21) C1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi64 [-]").
    iIntros (CID29 Hs29) "Hcg Hpc".
    set (C2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x64) : mword 64) 4)]> C1).
    assert (Htgtit : add_vec (mword_of_int (KernelSyms.initlog + 0x64) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096848 : mword 21))
                     = mword_of_int KernelSyms.install_trans)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtit) in "Hpc".
    assert (HC2a0 : C2 !!! Regidx Ra0 = (mword_of_int 1 : mword 64))
      by (rewrite /C2 upd_ne; [exact HC1a0 | vm_compute; discriminate]).
    assert (HC2sp : C2 !!! Regidx csp_rs1 = spr)
      by (rewrite /C2 upd_ne; [exact HC1sp | vm_compute; discriminate]).
    assert (HC2ra : C2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x64) : mword 64) 4)
      by (rewrite /C2; apply upd_eq).
    assert (HC2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              C2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /C2 upd_ne; [| regne]. exact (HC1cs c Hcs N2 N8 N9 N18 N19). }
    (* the two units install_trans wants: the one brelse just returned plus
       one out of the 33 still parked *)
    assert (Hsplit2 : 33%nat = (1 + 32)%nat) by lia.
    iEval (rewrite Hsplit2 bslots_op) in "Hslots".
    iDestruct "Hslots" as "[Hs2u Hpool]".
    iAssert (bslots bn 2) with "[Hs1u Hs2u]" as "Hs2".
    { rewrite (_ : 2%nat = (1 + 1)%nat); [| lia]. rewrite bslots_op.
      iSplitL "Hs1u"; [iExact "Hs1u" | iExact "Hs2u"]. }
    iAssert (lh_n_pa ↦₄ (mword_of_int (Z.of_nat 0%nat) : mword 32))%I
      with "[Hncell]" as "Hncell"; [iExact "Hncell"|].
    iDestruct (cpu_own_transport CID27 CID29 0 true pj C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID26) (CIDb := CID29) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKit : (K_install_trans <= K - 6)%nat)
      by (unfold K_install_trans; lia).
    (* the empty batch's pure shape, as NAMED facts: a tactic in an argument
       position whose expected type is still an evar diverges
       (claude-notes/durable-notes.md) *)
    assert (Hgeomok : log_geom_ok cov logstart) by (split; assumption).
    assert (Hshape0 : (0%nat = length ([] : list (mword 32))
                       /\ (0 <= LOGBLOCKS)%nat)).
    { split; [reflexivity | unfold LOGBLOCKS; lia]. }
    assert (Hnodup0 : NoDup (map uint ([] : list (mword 32)))).
    { constructor. }
    assert (Hwcov0 : forall w : mword 32, w ∈ ([] : list (mword 32)) ->
              uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)).
    { intros w Hw. exfalso. exact (not_elem_of_nil w Hw). }
    assert (Hrec0 : (true = false \/ 0%nat = 0%nat)) by (right; reflexivity).
    assert (Hlw0 : forall (i : nat) (w : SailStdpp.Values.mword 32),
              ([] : list (mword 32)) !! i = Some w ->
              L !! uint w = Some ((fun _ : nat => ([] : list (bv 8))) i)).
    { intros i w Hi. rewrite lookup_nil in Hi. discriminate. }
    iAssert ([∗ list] i ↦ w ∈ ([] : list (mword 32)), lh_block i ↦₄ w)%I
      as "Hnil1"; [iApply il_bigL_nil|].
    iAssert ([∗ list] i ↦ w ∈ ([] : list (mword 32)),
               fsblock γfs (log_slot_bno logstart i) [] ∗
               (uint w) ↪[fs_dirty γfs]{#(1/2)} true)%I
      as "Hnil2"; [iApply il_bigL_nil|].
    iApply (InstallTrans.wp_install_trans_sconf Φ γs j γl γu γd γk pd pav pu bn γfs
              cov logstart dev true 0%nat ([] : list (mword 32))
              (fun _ : nat => ([] : list (bv 8))) L D pidv dq
              C2 (K - 6)%nat true C b True%I
              HKit Hgeomok Hj Hgl eq_refl
              Hrec0 HC2a0 Hshape0 Hnodup0 Hwcov0 Hlw0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hfroz Hppid Hprocs Hscheds
                    Hpark Hdevi Hdgeom Hdlock Hncell Hnil1 HLauth HDauth
                    Hnil2 Hs2 [] [] [-]").
    (* THE EMPTY WRITE SET's per-entry permits: this call installs NOTHING
       (the on-disk header is clean, which is initlog's precondition), so the
       generator is vacuous -- there is no entry to look up -- and the
       threaded resource is [True]. *)
    { iModIntro. iIntros (i w bs') "%Hi _ _". rewrite lookup_nil in Hi.
      discriminate. }
    { done. }
    iIntros (CID30 Hs30 mI) "%Hcs3 Hcg Hcnt Hpc Hpark Hppid
                             Hncell _ HLauth HDauth _ Hs2 _".
    assert (Hpc68 : ret_pc (C2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x68)).
    { rewrite HC2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc68) in "Hpc".
    pose proof Hcs3 as Hcs3_cs.
    assert (HmIsp : mI !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs3_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HC2sp).
    assert (HmIcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mI !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs3_cs c Hcs).
      exact (HC2cs c Hcs N2 N8 N9 N18 N19). }
    iAssert (ghost_map_auth (fs_dirty γfs) 1 D) with "[HDauth]" as "HDauth";
      [iExact "HDauth"|].
    iAssert (bslots bn 2) with "[Hs2]" as "Hs2"; [iExact "Hs2"|].
    (* ===== +0x68 auipc a5,0x1e / +0x6c sw zero,1924(a5) : log.lh.n := 0 ===== *)
    iPoseProof (ili_68 with "Htext") as "Hi68".
    iPoseProof (ili_6c with "Htext") as "Hi6c".
    iPoseProof (ili_70 with "Htext") as "Hi70".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x68)) Ra5
              (mword_of_int 30 : mword 20) mI (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68 [-]").
    iIntros (CID31 Hs31) "Hcg Hpc".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.initlog + 0x68) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> mI).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spr)
      by (rewrite /D1 upd_ne; [exact HmIsp | vm_compute; discriminate]).
    assert (HD1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              D1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /D1 upd_ne; [| regne]. exact (HmIcs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x68) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x6c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6c) in "Hpc".
    assert (Hlhad2 : add_vec (rget D1 Ra5)
                       (sign_extend' 64 (mword_of_int 1904 : mword 12)) = lh_n_pa).
    { rgne. rewrite /D1 upd_eq /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
      apply bv_eq; vm_compute; reflexivity. }
    iAssert (lh_n_pa ↦₄ (mword_of_int 0 : mword 32))%I with "[Hncell]" as "Hncell";
      [iExact "Hncell"|].
    iEval (rewrite -Hlhad2) in "Hncell".
    iApply (wp_sw_zero_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x6c)) Ra5
              (mword_of_int 1904 : mword 12) D1 (K - 6)%nat
              (mword_of_int 0 : mword 32) b
              with "Hcg Hpc Hi6c Hncell [-]").
    iIntros (CID32 Hs32) "Hcg Hpc Hncell".
    iEval (rewrite Hlhad2) in "Hncell".
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x6c) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    (* ===== +0x70 jal ra,write_head ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x70)) Rra
              (mword_of_int 2096742 : mword 21) D1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi70 [-]").
    iIntros (CID33 Hs33) "Hcg Hpc".
    set (D2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x70) : mword 64) 4)]> D1).
    assert (Htgtwh : add_vec (mword_of_int (KernelSyms.initlog + 0x70) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096742 : mword 21))
                     = mword_of_int KernelSyms.write_head)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwh) in "Hpc".
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spr)
      by (rewrite /D2 upd_ne; [exact HD1sp | vm_compute; discriminate]).
    assert (HD2ra : D2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x70) : mword 64) 4)
      by (rewrite /D2; apply upd_eq).
    assert (HD2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              D2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /D2 upd_ne; [| regne]. exact (HD1cs c Hcs N2 N8 N9 N18 N19). }
    (* one unit for write_head's bread *)
    iEval (rewrite (_ : 2%nat = (1 + 1)%nat); [| lia]) in "Hs2".
    iEval (rewrite bslots_op) in "Hs2".
    iDestruct "Hs2" as "[Hs1u Hs1v]".
    iAssert (lh_n_pa ↦₄ (mword_of_int (Z.of_nat 0%nat) : mword 32))%I
      with "[Hncell]" as "Hncell"; [iExact "Hncell"|].
    iDestruct (cpu_own_transport CID30 CID33 0 true pj C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID29) (CIDb := CID33) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKwh : (K_write_head <= K - 6)%nat) by (unfold K_write_head; lia).
    iAssert ([∗ list] i ↦ w ∈ ([] : list (mword 32)), lh_block i ↦₄ w)%I
      as "Hnil3"; [iApply il_bigL_nil|].
    iApply (WriteHead.wp_write_head_sconf Φ γs j γl γu γd γk pd pav pu bn γfs
              cov logstart dev 0%nat ([] : list (mword 32)) L pidv dq
              D2 (K - 6)%nat true C b
              (log_mirror_at (0%nat, []) ∗ swap_lb (S gen_id))%I
              HKwh Hgeomok Hj Hgl eq_refl Hshape0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hfroz Hppid Hprocs Hscheds
                    Hpark Hdevi Hdgeom Hdlock Hncell Hnil3 HLauth [Hfsb]
                    Hs1u [Hmirf] [-]").
    { iExists bs_hdr. iExact "Hfsb". }
    (* THE SWAP, riding this write (phase C2b/D1 stage 3): the era takes
       custody of the crash record at the image the write produces.  The
       WHOLE mirror variable goes into the closure -- the swap sets it to the
       post-write picture, splits it there, keeps one half in the arm and
       returns the other (with its clean header, read off the write itself)
       together with the swap receipt. *)
    { iIntros (bs' Hlen' Hhn' Hdec').
      iDestruct "Hcert" as "(_ & Hstc & Hregc)".
      iApply (fs_swap_permit cov logstart bs' ltac:(exact Hlen')
                ltac:(rewrite Hhn'; reflexivity)
                with "Hseam Hregc Hstc Hmirf"). }
    iIntros (CID34 Hs34 mW bs') "%Hcs4 Hcg Hcnt Hpc Hpark Hppid
                                 Hncell _ HLauth Hfsb %Hhn %Hhdec Hs1u HQ".
    assert (Hpc74 : ret_pc (D2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x74)).
    { rewrite HD2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc74) in "Hpc".
    pose proof Hcs4 as Hcs4_cs.
    assert (HmWsp : mW !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs4_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HD2sp).
    assert (HmWcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mW !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs4_cs c Hcs).
      exact (HD2cs c Hcs N2 N8 N9 N18 N19). }
    (* ===== EPILOGUE ===== *)
    iPoseProof (ili_74 with "Htext") as "Hi74".
    iPoseProof (ili_76 with "Htext") as "Hi76".
    iPoseProof (ili_78 with "Htext") as "Hi78".
    iPoseProof (ili_7a with "Htext") as "Hi7a".
    iPoseProof (ili_7c with "Htext") as "Hi7c".
    iPoseProof (ili_7e with "Htext") as "Hi7e".
    iPoseProof (ili_80 with "Htext") as "Hi80".
    (* +0x74 c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x74)) (mword_of_int 5 : mword 6) Rra
              mW (K - 6)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74 [Hc1] [-]").
    { iEval (rewrite HmWsp Hb1). iExact "Hc1". }
    iIntros (CID35 Hs35) "Hcg Hpc Hc1".
    iEval (rewrite HmWsp Hb1) in "Hc1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mW).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact HmWsp | vm_compute; discriminate]).
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x74) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x76))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x76)) (mword_of_int 4 : mword 6) Rs0
              P1 (K - 6)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi76 [Hc2] [-]").
    { iEval (rewrite HP1sp Hb2). iExact "Hc2". }
    iIntros (CID36 Hs36) "Hcg Hpc Hc2".
    iEval (rewrite HP1sp Hb2) in "Hc2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x76) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp78) in "Hpc".
    (* +0x78 c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x78)) (mword_of_int 3 : mword 6) Rs1
              P2 (K - 6)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [Hc3] [-]").
    { iEval (rewrite HP2sp Hb3). iExact "Hc3". }
    iIntros (CID37 Hs37) "Hcg Hpc Hc3".
    iEval (rewrite HP2sp Hb3) in "Hc3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x78) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x7a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7a) in "Hpc".
    (* +0x7a c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x7a)) (mword_of_int 2 : mword 6) Rs2
              P3 (K - 6)%nat (m !!! Regidx Rs2 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [Hc4] [-]").
    { iEval (rewrite HP3sp Hb4). iExact "Hc4". }
    iIntros (CID38 Hs38) "Hcg Hpc Hc4".
    iEval (rewrite HP3sp Hb4) in "Hc4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x7a) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    (* +0x7c c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x7c)) (mword_of_int 1 : mword 6) Rs3
              P4 (K - 6)%nat (m !!! Regidx Rs3 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c [Hc5] [-]").
    { iEval (rewrite HP4sp Hb5). iExact "Hc5". }
    iIntros (CID39 Hs39) "Hcg Hpc Hc5".
    iEval (rewrite HP4sp Hb5) in "Hc5".
    set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
    assert (HP5sp : P5 !!! Regidx csp_rs1 = spr)
      by (rewrite /P5 upd_ne; [exact HP4sp | vm_compute; discriminate]).
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x7c) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x7e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* +0x7e c.addi16sp sp,48 : pop the frame *)
    assert (Hwv : add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))
                  = sp0).
    { rewrite HP5sp. unfold spr, sp0. apply frame_cancel_48. }
    assert (Hpop : (P5 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HP5sp. exact Hspr6. }
    iAssert (stack_own sp0 6) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6]" as "Hframe6".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc1"; [iExists _; iExact "Hc1"|].
      iSplitL "Hc2"; [iExists _; iExact "Hc2"|].
      iSplitL "Hc3"; [iExists _; iExact "Hc3"|].
      iSplitL "Hc4"; [iExists _; iExact "Hc4"|].
      iSplitL "Hc5"; [iExists _; iExact "Hc5"|].
      iSplitL "Hc6"; [iExists _; iExact "Hc6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe6".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x7e))
              (mword_of_int 3 : mword 6) P5 (K - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi7e Hframe6 [-]").
    iIntros (CID40 Hs40) "Hcg Hpc".
    set (P6 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P5).
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x7e) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x80))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp80) in "Hpc".
    (* +0x80 c.ret *)
    assert (HP6ra : P6 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.initlog + 0x80)) Rra P6 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi80 [-]").
    iIntros (CID41 Hs41) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P6 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP6ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CALLEE-SAVED LEDGER ===== *)
    assert (Csp : P6 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite /P6 upd_eq. exact Hwv. }
    assert (Cs0 : P6 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P6 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs2 : P6 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_eq. reflexivity. }
    assert (Cs3 : P6 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_eq. reflexivity. }
    assert (Hfin : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              P6 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P6 upd_ne; [| regne]. rewrite /P5 upd_ne; [| regne].
      rewrite /P4 upd_ne; [| regne]. rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne]. rewrite /P1 upd_ne; [| regne].
      exact (HmWcs c Hcs N2 N8 N9 N18 N19). }
    assert (Cs4 : P6 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs5 : P6 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs6 : P6 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs7 : P6 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs8 : P6 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs9 : P6 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs10 : P6 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs11 : P6 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    (* ===== THE CONSTRUCTOR'S GHOST STEP: assemble [log_res], seal the
       lock, and hand out [log_ctx]. ===== *)
    assert (Hbd : forall z : Z,
              bool_decide (z ∈ map uint ([] : list (SailStdpp.Values.mword 32)))
              = false).
    { intro z. apply bool_decide_eq_false_2. apply not_elem_of_nil. }
    iApply fupd_wp.
    (* ---- THE SWAP'S RECEIPT, off the write's permit (stage 3) ----
       Both halves are timeless, so the [▷] the permit channel puts on them
       strips inside this update: the era's mirror half goes into the batch
       and the swap lower bound into [log_ctx]. *)
    iMod "HQ" as "[Hmirc #Hswlb]".
    iAssert (log_mirror_clean) with "[Hmirc]" as "Hmirc";
      [rewrite /log_mirror_clean; iExact "Hmirc"|].
    iAssert (log_batch bn γfs cov logstart 0%nat ∅)
      with "[Hncell Hblk HLauth HDauth Hcovf Hfsb Hslotsfs Hpool Hmirc]" as "Hbatch".
    { rewrite /log_batch.
      iExists ([] : list (mword 32)), (<[log_hdr_bno logstart := bs']> L), D.
      iSplitR; [iPureIntro; split; [reflexivity | unfold LOGBLOCKS; lia]|].
      (* the fresh batch has logged nothing: LB = list_to_set [] = empty *)
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; constructor|].
      iSplitR; [iPureIntro; exact Hwcov0|].
      iSplitL "Hncell"; [iExact "Hncell"|].
      iSplitR; [iApply il_bigL_nil|].
      iSplitL "Hblk"; [iExact "Hblk"|].
      iSplitL "HLauth"; [iExact "HLauth"|].
      iSplitL "HDauth"; [iExact "HDauth"|].
      iSplitL "Hcovf".
      { iApply (big_sepS_mono with "Hcovf"). intros z Hz. rewrite (Hbd z). done. }
      iSplitL "Hfsb"; [iExists bs'; iExact "Hfsb"|].
      iSplitL "Hslotsfs"; [iExact "Hslotsfs"|].
      iSplitL "Hpool"; [iExact "Hpool"|].
      iExact "Hmirc". }
    iAssert (log_res (MkLogNames γlk γops) bn γfs cov logstart)
      with "[Hout Hcmt Hnc Hops Hbatch]" as "Hres".
    { rewrite /log_res.
      iExists 0%nat, false, v_nc, (∅ : gmap nat op_entry).
      iSplitL "Hout"; [iExact "Hout"|].
      iSplitL "Hcmt"; [iExact "Hcmt"|].
      iSplitL "Hnc"; [iExact "Hnc"|].
      iSplitL "Hops"; [iExact "Hops"|].
      iSplitR; [iPureIntro; apply map_size_empty|].
      iSplitR; [iPureIntro; intros i e Hi; rewrite lookup_empty in Hi; discriminate|].
      iSplitR; [iPureIntro; lia|].
      iSplitR; [iPureIntro; discriminate|].
      iExists 0%nat, ∅.
      iSplitR; [iPureIntro; rewrite op_sum_empty; unfold LOGBLOCKS; lia|].
      iSplitR; [iPureIntro; intros i e Hi; rewrite lookup_empty in Hi; discriminate|].
      iExact "Hbatch". }
    iMod ("Hmk" $! (log_res (MkLogNames γlk γops) bn γfs cov logstart)
            with "Hres") as "#Hislk".
    iAssert (∃ γ : log_names, log_ctx γ bn γfs cov logstart dev)%I as "#Hctx".
    { iExists (MkLogNames γlk γops). rewrite /log_ctx.
      iSplitR; [iExact "Hislk"|].
      iSplitR; [iExact "Hdvp"|].
      iSplitR; [iExact "Hstp" | iExact "Hswlb"]. }
    iModIntro.
    (* the two units the caller gets back *)
    iAssert (bslots bn 2) with "[Hs1u Hs1v]" as "Hs2".
    { rewrite (_ : 2%nat = (1 + 1)%nat); [| lia]. rewrite bslots_op.
      iSplitL "Hs1u"; [iExact "Hs1u" | iExact "Hs1v"]. }
    iDestruct (cpu_own_transport CID34 CID41 0 true pj C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID41 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P6 with "[%] Hcg Hcnt Hpc Hpark Hppid Hsbf Hs2 Hctx").
    { unfold callee_saved. repeat split; assumption. }
  Qed.

End ProofInitlog.

End InitlogProof.
