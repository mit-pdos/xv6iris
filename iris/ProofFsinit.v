(* ProofFsinit.v -- fsinit over the SIE-agnostic sconf world.  THE LAST
   FUNCTION OF fs.c.

     void fsinit(int dev) {
       struct buf *bp;
       bp = bread(dev, 1);                 // readsb(dev, &sb), INLINED
       memmove(&sb, bp->data, sizeof(sb));
       brelse(bp);
       if(sb.magic != FSMAGIC) panic("invalid file system");
       initlog(dev, &sb);
       ireclaim(dev);
     }

   THE SHAPE OF THE PROOF.  fsinit is STRAIGHT-LINE -- no loop, no join,
   one live exit -- so there are only two blocks:

     [fsi_epilogue]  +0x58 .. +0x62  pop ra/s0/s1/s2, pop the 4-slot frame,
                                     return, discharge the contract.
     [wp_fsinit_sconf] +0x00 .. +0x54  the push, the four calls
                                     (bread / memmove / brelse, then initlog
                                     and ireclaim) and the magic test.

   THE ONE GENUINELY NEW PIECE IS THE memmove's BYTE -> WORD BRIDGE.  Before
   +0x26 the 32 bytes at [&sb] are raw .bss ([sb_old]); the memmove writes
   the bread'd buffer's first 32 bytes over them, and the contract's
   [take 32 bs_sb = sb_image ...] premise says what those bytes ARE.
   [fsi_img] reads the image back as eight little-endian words (it is
   literally [BlockWords.ind_bytes] at an eight-entry list, so
   [ind_bytes_lookup] does all the work), [ByteBuf.bb_chunk] regroups the
   32-byte window into eight four-byte records, and [fsi_word4] folds each
   record into the [↦₄] cell the rest of the tree takes as a premise.  FOUR
   of the eight ARE the addresses BitmapInv.v and InodeInv.v already name --
   SpecFsinit's [sb_size_addr] / [sb_ninodes_addr] / [sb_inodestart_addr] /
   [sb_bmapstart_addr] prove that by [reflexivity] -- so the cells born here
   are handed to initlog (its [sb + 20] fsc_logst fraction) and to ireclaim
   (ninodes / inodestart / bmapstart) without a single re-anchoring step.

   THE PANIC ARM AT +0x40 IS DEAD, and it is a REAL panic (not one of the
   [printk] arms balloc and ialloc have), so a contract that promises to
   return has to refute it: [bv_unsigned v_magic = FSMAGIC] is what does,
   against the [lui a5,0x10203 / addi a5,a5,64] literal at +0x38/+0x3c.
   The panic credentials still ride for the callees' own arms, so no PANIC functor
   is instantiated here or in LinkFsinit.v.

   THIRTY-FIVE BUFFER SLOTS, AND THE ONE HELD BACK.  The contract enters with
   [bslots ((LOGBLOCKS + 2) + 2 + 1)] = 35.  ONE is split off for the
   bread at +0x10 and returned by the brelse at +0x2c; the other 34 go to
   initlog, which seals 32 into [log_state]'s pool and returns 2; the held
   one rejoins them to make the 3 ireclaim wants.  See SpecFsinit.v's header
   and the N5d ledger's finding 1.                                        *)
From Stdlib Require Import Eqdep_dec ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list list_numbers functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers dfrac.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
(* [fs_sb] -- the record block 1 decodes to (durable-disk lane C-3a).
   EARLY, because this file's later imports own the names it shadows. *)
Require Import FsImg.
Require Import InstrBytes.
Require Import KernelText.
Require Import KernelRvcDecode.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import CpuOwn.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import DiskPtsto.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import BlockWords.
Require Import BitmapInv.
Require Import DinodeSlot.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import CodeFsinit.
Require Import SpecBread SpecBrelse SpecMemmove.
Require Import SpecInitlog SpecIreclaim.
Require Import BioDefs.   (* [hdr_dec], for the general initlog premises *)
Require Import LogDefs.
Require Import SpecPrintk.
Require Import SpecFsinit.
(* the commit's law and its FS-side discharge (durable-disk C-8) *)
Require Import InodeRegion.
Require Import FsCollect.
Require Import SbPark.
Require Import LogSnapLaw.
Require Import FsCollectAll.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  MODULE                                                                *)
(* ===================================================================== *)
Module FsinitProof (BR : BREAD) (MM : MEMMOVE) (BL : BRELSE)
                   (IL : INITLOG) (IR : IRECLAIM) : FSINIT.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac fsiidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  PURE: the superblock image, read back as eight little-endian words.   *)
(*                                                                        *)
(*  [sb_image] IS [BlockWords.ind_bytes] at an eight-entry list -- the     *)
(*  only difference is the trailing [++ []] the Fixpoint leaves -- so the  *)
(*  whole byte->word reading is [ind_bytes_lookup] and nothing else.       *)
(* ===================================================================== *)

Local Lemma fsi_image_ind (w0 w1 w2 w3 w4 w5 w6 w7 : mword 32) :
  sb_image w0 w1 w2 w3 w4 w5 w6 w7
  = ind_bytes [w0; w1; w2; w3; w4; w5; w6; w7].
Proof.
  rewrite /sb_image. cbn [ind_bytes]. rewrite app_nil_r. reflexivity.
Qed.

Local Lemma fsi_img (w0 w1 w2 w3 w4 w5 w6 w7 : mword 32) (i jj : nat) :
  (i < 8)%nat -> (jj < 4)%nat ->
  sb_image w0 w1 w2 w3 w4 w5 w6 w7 !!! (4 * i + jj)%nat
  = nth_byte ([w0; w1; w2; w3; w4; w5; w6; w7] !!! i) jj.
Proof.
  intros Hi Hjj. rewrite fsi_image_ind.
  apply list_lookup_total_correct.
  apply ind_bytes_lookup; [cbn [length]; lia | exact Hjj].
Qed.

(* the prefix equation, pointwise: [take 32 bs] and [bs] agree below 32 *)
Local Lemma fsi_take_total (l : list (bv 8)) (n k : nat) :
  (k < n)%nat -> take n l !!! k = l !!! k.
Proof.
  intros Hk. rewrite !list_lookup_total_alt.
  rewrite lookup_take; [reflexivity | exact Hk].
Qed.

(* [neq_vec] on a value against itself -- the +0x40 refutation's last step *)
Local Lemma fsi_neq_self (x : mword 64) : neq_vec x x = false.
Proof.
  unfold neq_vec. rewrite (proj2 (eq_vec_true_iff x x) eq_refl). reflexivity.
Qed.

(* ===================================================================== *)
(*  The frame, the two register-threading invariants, the continuation.   *)
(* ===================================================================== *)

(* fsinit's frame is FOUR slots, pushed with a plain [c.addi sp,sp,-32] at
   +0x00 and popped with a [c.addi16sp sp,32] at +0x60 -- so [stk_push_32]
   on the way in and [stk_pop_32] on the way out. *)
Definition fsi_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4.

Definition fsi_thr4 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Section FsinitDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
            ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ}.

  (* ra@24 s0@16 s1@8 s2@0 off the pushed sp, i.e. slots 1..4 off the entry *)
  Definition fsi_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64))%I.

  (* THE CONTINUATION, named so the proofmode does not re-traverse it at
     every split (claude-notes/optimization.md).  It is the contract's post,
     verbatim. *)
  Definition fsi_cont `{GEN : GenId} `{CID0 : CpuId}
      (bn : bio_names)
      (bmapstart inodestart ninodes size : Z)
      (dev : mword 32)
      (v_magic v_size v_nblocks v_nlog : mword 32)
      (pidv : mword 32) (dq : dfrac) (j : nat)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr j) pidv Vpr -∗
        sb_magic ↦₄ v_magic -∗
        BitmapInv.sb_size ↦₄ v_size -∗
        sb_nblocks ↦₄ v_nblocks -∗
        InodeInv.sb_ninodes ↦₄ (mword_of_int ninodes : mword 32) -∗
        sb_nlog ↦₄ v_nlog -∗
        sb_logstart ↦₄ (mword_of_int fsc_logst : mword 32) -∗
        InodeInv.sb_inodestart ↦₄ (mword_of_int inodestart : mword 32) -∗
        BitmapInv.sb_bmapstart ↦₄ (mword_of_int bmapstart : mword 32) -∗
        (* block 1's run does NOT come back (durable-disk lane C-3a): it is
           spent into [initlog]'s [SbPark] park and rides out inside the
           [log_ctx] below. *)
        log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst dev -∗
        bslots 3 -∗
        iref_slot -∗
        ireg_boot -∗
        WP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------ *)
  (* THE BUFFER'S DATA BYTES, out of the handle and back.  [ds_held_L]'s *)
  (* twin for the raw window: the whole of what fsinit's memmove wants.  *)
  (* ------------------------------------------------------------------ *)
  Lemma fsi_data_acc (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dv bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dv bno bs bsl bsd d -∗
      ⌜length bs = 1024%nat⌝ ∗
      bb_bytes (b_data (bpa k)) (length bs) (fun jj => bs !!! jj) ∗
      (bb_bytes (b_data (bpa k)) (length bs) (fun jj => bs !!! jj) -∗
       bio_held bn V k pidv dv bno bs bsl bsd d).
  Proof.
    rewrite /bio_held.
    iIntros "(%A & %B & %C & H1 & H3 & H4 & Hbo & H5 & H6)".
    rewrite /buf_own.
    iDestruct "Hbo" as "(Hb & Hdk & %Hlen & Hbytes)".
    iEval (rewrite (bb_bytes_of_list (b_data (bpa k)) bs)) in "Hbytes".
    iSplitR; [done |]. iFrame "Hbytes". iIntros "Hbytes".
    iEval (rewrite -(bb_bytes_of_list (b_data (bpa k)) bs)) in "Hbytes".
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iFrame "H1 H3 H4 H5 H6 Hb Hdk Hbytes". done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ONE 4-BYTE CELL out of four raw bytes.  The inverse of              *)
  (* [RiscvPtsto.word4_pointsto_bytes]: the alignment is a premise (the   *)
  (* bytes do not carry it) and the naming function is read at [o + jj].  *)
  (* ------------------------------------------------------------------ *)
  Lemma fsi_word4 (a : mword 64) (o : nat) (w : mword 32) (f : nat -> bv 8) :
    is_aligned_paddr (Physaddr (pa_add a o)) 4 = true ->
    (forall jj, (jj < 4)%nat -> f (o + jj)%nat = nth_byte w jj) ->
    ([∗ list] jj ∈ seq 0 4, pa_add (pa_add a o) jj ↦ₘ f (o + jj)%nat) -∗
    pa_add a o ↦₄ w.
  Proof.
    intros Hal Hf. iIntros "H". rewrite /word4_pointsto.
    iSplitR; [done |].
    iApply (big_sepL_mono with "H"). intros i x Hj.
    apply lookup_seq in Hj as [-> Hlt].
    rewrite (Hf (0 + i)%nat ltac:(lia)). done.
  Qed.

End FsinitDefs.

(* ===================================================================== *)
(*  +0x58 .. +0x62 : THE ONLY EXIT.  restore the four, pop, return.       *)
(* ===================================================================== *)
Section FsinitEpilogue.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
            ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ}.

  Local Lemma fsi_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names)
      (bmapstart inodestart ninodes size : Z)
      (dev : mword 32)
      (v_magic v_size v_nblocks v_nlog : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_fsinit <= K)%nat ->
    fsi_sp m M ->
    fsi_thr4 m M ->
    sie_cap_gpr KT1 M (K - 4)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.fsinit + 0x58) : mword 64) -∗
    fsi_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_magic ↦₄ v_magic -∗
    BitmapInv.sb_size ↦₄ v_size -∗
    sb_nblocks ↦₄ v_nblocks -∗
    InodeInv.sb_ninodes ↦₄ (mword_of_int ninodes : mword 32) -∗
    sb_nlog ↦₄ v_nlog -∗
    sb_logstart ↦₄ (mword_of_int fsc_logst : mword 32) -∗
    InodeInv.sb_inodestart ↦₄ (mword_of_int inodestart : mword 32) -∗
    BitmapInv.sb_bmapstart ↦₄ (mword_of_int bmapstart : mword 32) -∗
    log_ctx icfg_log bn fsc_fs fsc_cov fsc_logst dev -∗
    bslots 3 -∗
    iref_slot -∗
    ireg_boot -∗
    fsi_cont (CID0 := CID0) bn bmapstart inodestart ninodes
             size dev v_magic v_size v_nblocks v_nlog pidv dq j
             m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hthr.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc Hframe Hppid Hmg Hsz Hnb Hni Hnl Hls Hist
              Hbms Hlctx Hsl Hiref Hboot Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    rewrite /fsi_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4)".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0x58 c.ldsp ra,24(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x58))
              (mword_of_int 3 : mword 6) Rra
              M (K - 4)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (fsi_58 with "Htext"). }
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : fsi_sp m P1)
      by (rewrite /fsi_sp /P1 upd_ne; [exact Hsp | nz]).
    assert (HP1thr : fsi_thr4 m P1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ===== +0x5a c.ldsp s0,16(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x5a))
              (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf2]").
    { iApply (fsi_5a with "Htext"). }
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : fsi_sp m P2)
      by (rewrite /fsi_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : fsi_thr4 m P2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9 N18). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x5c)) by pcw.
    iEval (rewrite Hpp5c) in "Hpc".
    (* ===== +0x5c c.ldsp s1,8(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x5c))
              (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (fsi_5c with "Htext"). }
    { iEval (rewrite HP2sp -Hsp Hc3). iExact "Hf3". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -Hsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : fsi_sp m P3)
      by (rewrite /fsi_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : fsi_thr4 m P3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9 N18). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x5c) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x5e)) by pcw.
    iEval (rewrite Hpp5e) in "Hpc".
    (* ===== +0x5e c.ldsp s2,0(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x5e))
              (mword_of_int 0 : mword 6) Rs2
              P3 (K - 4)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (fsi_5e with "Htext"). }
    { iEval (rewrite HP3sp -Hsp Hc4). iExact "Hf4". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf4".
    iEval (rewrite HP3sp -Hsp Hc4) in "Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : fsi_sp m P4)
      by (rewrite /fsi_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : fsi_thr4 m P4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N18). }
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x5e) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x60)) by pcw.
    iEval (rewrite Hpp60) in "Hpc".
    (* ===== +0x60 c.addi16sp sp,32 : the 4-slot pop ===== *)
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP4sp. apply stk_pop_32. }
    assert (Hpop : (P4 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HP4sp).
    iDestruct (stack_own_4_intro (m !!! Regidx csp_rs1 : mword 64)
                 (m !!! Regidx Rra : mword 64) (m !!! Regidx Rs0 : mword 64)
                 (m !!! Regidx Rs1 : mword 64) (m !!! Regidx Rs2 : mword 64)
                 with "Hf1 Hf2 Hf3 Hf4") as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.fsinit + 0x60))
              (mword_of_int 2 : mword 6) P4 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (fsi_60 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x60) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x62)) by pcw.
    iEval (rewrite Hpp62) in "Hpc".
    (* ===== +0x62 c.ret ===== *)
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.fsinit + 0x62)) Rra P5 K b
              ltac:(nz) with "Hcg Hpc []").
    { iApply (fsi_62 with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P5 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P5 upd_eq; exact Hwv).
    assert (Cs2 : P5 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_eq. reflexivity. }
    assert (Cs1 : P5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs0 : P5 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Hfin : fsi_thr4 m P5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P5 upd_ne; [| regne]. exact (HP4thr c Hcs N2 N8 N9 N18). }
    assert (Cs3 : P5 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs4 : P5 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs5 : P5 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs6 : P5 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs7 : P5 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs8 : P5 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs9 : P5 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs10 : P5 !!! Regidx (mword_of_int 26 : mword 5)
                   = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Cs11 : P5 !!! Regidx (mword_of_int 27 : mword 5)
                   = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; fsiidx).
    assert (Hcs : callee_saved m P5)
      by (unfold callee_saved; split_and!; assumption).
   iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr j) b
                ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
   iDestruct (trap_csrs_ext_transport CID0 CID6 eb (proc_addr j)
                ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
   iDestruct (cpu_claim_ext_transport CID0 CID6 eb (proc_addr j)
                ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    rewrite /fsi_cont.
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P5 with "[%] Hcg Hcnt Hextc Hclmc Hpc Hppid Hmg Hsz Hnb Hni
                                  Hnl Hls Hist Hbms Hlctx Hsl Hiref
                                  Hboot");
      [exact Hcs].
  Qed.

End FsinitEpilogue.

(* ===================================================================== *)
(*  +0x00 .. +0x54 : the push, the four calls, and the magic test.        *)
(* ===================================================================== *)
Section FsinitMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
            ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ}.

  Lemma wp_fsinit_sconf `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γi : gname)
      (gtl : gname)
      (γpr : gname)
      (bmapstart inodestart : Z)
      (ninodes : Z) (nib : nat) (size : Z)
      (dev : mword 32)
      (v_magic v_size v_nblocks v_ninodes v_nlog
       v_logstart v_inodestart v_bmapstart : mword 32)
      (bs_sb : list (bv 8))
      (sb_old : nat -> bv 8)
      (bs_hdr : list (bv 8))
      (Xv : Z -> list (bv 8))
      (Mbrn : log_mirror)
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (vlock : mword 32) (vname vcpu : mword 64)
      (v_start v_dev v_nc v_n : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
      (sbrec : fs_sb) :
      wp_fsinit_sconf_body γs j γl γu γd γk pd pav pu bn γi gtl γpr
                           bmapstart inodestart ninodes nib size
                           dev
                           v_magic v_size v_nblocks v_ninodes v_nlog
                           v_logstart v_inodestart v_bmapstart bs_sb sb_old
                           bs_hdr Xv Mbrn L D vlock vname vcpu v_start v_dev v_nc v_n
                           pidv dq m K eb b lks Vpr sbrec.
  Proof.
    cbv beta delta [wp_fsinit_sconf_body].
    intros pcE pj ret_tgt HK Hgeom H1cov H1log Himg Hsbparse Hsbok
           Hcgeom Hbmq Hszq
           Hmagic Hvni Hvis Hvbs Hvls
           Hn1 Hnnib Hn31 Hdevc Hnibc Hdevr Hnib0 Hist0 Hblk Hsize Hbm0 Hbmcov
           Hbmlog Hcovb Hhdrbnd Hhdrnd Hhdrok Hxvslot HLmir Hpk Hj Hgl Ha0 Hbelow.
    subst v_ninodes. subst v_inodestart. subst v_bmapstart.
    subst v_logstart.
    pose proof HK as HK'. 
    (* ---- the image, pointwise, below 32 ---- *)
    assert (Hfimg : forall jj, (jj < 32)%nat ->
              bs_sb !!! jj
              = sb_image v_magic v_size v_nblocks (mword_of_int ninodes)
                  v_nlog (mword_of_int fsc_logst) (mword_of_int inodestart)
                  (mword_of_int bmapstart) !!! jj).
    { intros jj Hjj. rewrite -Himg. symmetry.
      apply (fsi_take_total bs_sb 32 jj Hjj). }
    (* ---- the block number bread is called with ---- *)
    set (bno := (mword_of_int 1 : mword 32)).
    assert (Hbnou : uint bno = 1) by (vm_compute; reflexivity).
    assert (Hbnolt : (uint bno < 2147483648)%Z) by (rewrite Hbnou; lia).
    assert (Hbnocov : uint bno ∈ bv_cov (fs_view fsc_fs γd dev fsc_cov))
      by (rewrite Hbnou; exact H1cov).
    iIntros "Hcg Hcnt Hextc Hclmc #Htext #Hkdata Hpc #Hpenv #Hbio #Hseam #Hgen
              Hmirror Hlfree #Hbinv Hfsb Hxo Hsbold #Hireg Hboot #Hitb2 #Hitbl #Hesc #Hslks #Hbm
              Hlock0 Hlname Hlcpu Hlstart Hldev Hlout Hlcmt Hlnc Hlhn Hlhblk
              HauthL HauthD Hdirty Hhdr Hlslots Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl Hiref Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    iPoseProof (printk_env_panic with "Hpenv") as "#Hpanenv".
    (* THE BYTE VIEW'S ROW, off the bitmap invariant fsinit already holds
       (durable-disk 1c-flip): initlog needs it at the NAMED home set, to
       put into [LogInv.log_ctx]; block 1's own read needs the home-set-free
       form. *)
    iPoseProof (bitmap_inv_bytes_at with "Hbm") as "#Hbrow".
    (* THE FILE SYSTEM'S LAW, MINUS BLOCK 1'S PARK (durable-disk C-8).  It
       is assembled out of the four invariants fsinit already holds, read at
       the record block 1 DECODES to rather than at the config numbers --
       the three ties above are that bridge.  The park itself is initlog's
       own, minted in the same ghost step as the log lock's seal, so what
       goes down to [initlog] is the WAND and initlog composes the two.
       Nothing else about the file system crosses into the WAL. *)
    assert (Hcgeom' : col_geom sbrec (FsImg.sb_inodestart sbrec) nib
                        (fs_home_set fsc_cov fsc_logst))
      by (rewrite (cg_ist Hcgeom); exact Hcgeom).
    iAssert (ireg_reg γi fsc_fs (FsImg.sb_inodestart sbrec) nib) as "#Hireg'".
    { rewrite (cg_ist Hcgeom). iExact "Hireg". }
    iAssert (bitmap_reg fsc_fs (FsImg.sb_bmapstart sbrec) fsc_cov fsc_logst
               (FsImg.sb_size sbrec)) as "#Hbm'".
    { rewrite Hbmq Hszq. iExact "Hbm". }
    iPoseProof (is_itable2_pool with "Hitb2") as "#Hpoolinv".
    iAssert (□ (sb_park fsc_fs sbrec -∗ snap_law icfg_log fsc_fs fsc_cov fsc_logst))%I
      as "#Hlawf".
    { iModIntro. iIntros "#Hpark".
      iApply (fs_snap_law_build icfg_log fsc_ic fsc_fs γi fsc_cov fsc_logst nib sbrec
                eq_refl Hcgeom'
                with "Hireg' Hbm' Hesc Hpoolinv Hpark"). }
    iAssert (fsi_cont (CID0 := CID) bn bmapstart inodestart
               ninodes size dev v_magic v_size v_nblocks v_nlog
               pidv dq j m K eb b lks Vpr)%I with "[Hcont]" as "Hcont";
      [rewrite /fsi_cont; iExact "Hcont" |].
    (* ===== +0x00 c.addi sp,sp,-32 : the 4-slot frame ===== *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) (stk_push_32 (m !!! Regidx csp_rs1 : mword 64))
              with "Hcg Hpc []").
    { iApply (fsi_00 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HM1sp : fsi_sp m M1)
      by (rewrite /fsi_sp /M1 upd_eq; apply stk_push_32).
    assert (HM1thr : fsi_thr4 m M1).
    { intros c Hcs N2 N8 N9 N18. rewrite /M1 upd_ne; [reflexivity | regne]. }
    assert (HM1a0 : M1 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /M1 upd_ne; [exact Ha0 | nz]).
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(T1 & T2 & T3 & T4 & _)".
    iDestruct "T1" as (w1) "Hf1".   iDestruct "T2" as (w2) "Hf2".
    iDestruct "T3" as (w3) "Hf3".   iDestruct "T4" as (w4) "Hf4".
    assert (Hb1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1".   iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3".   iEval (rewrite -Hb4) in "Hf4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x2)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 .. +0x08 : the four saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x2))
              (mword_of_int 3 : mword 6) Rra
              M1 (K - 4)%nat w1 b with "Hcg Hpc [] Hf1").
    { iApply (fsi_02 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x2) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x4)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x4))
              (mword_of_int 2 : mword 6) Rs0
              M1 (K - 4)%nat w2 b with "Hcg Hpc [] Hf2").
    { iApply (fsi_04 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x4) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x6)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x6))
              (mword_of_int 1 : mword 6) Rs1
              M1 (K - 4)%nat w3 b with "Hcg Hpc [] Hf3").
    { iApply (fsi_06 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x6) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x8)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fsinit + 0x8))
              (mword_of_int 0 : mword 6) Rs2
              M1 (K - 4)%nat w4 b with "Hcg Hpc [] Hf4").
    { iApply (fsi_08 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc Hf4".
    iEval (rewrite Hb1; rgne; rewrite HM1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HM1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HM1s1) in "Hf3".
    iEval (rewrite Hb4; rgne; rewrite HM1s2) in "Hf4".
    iAssert (fsi_frame m) with "[Hf1 Hf2 Hf3 Hf4]" as "Hframe".
    { rewrite /fsi_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" | iExact "Hf4"]. }
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x8) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0xa)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== +0x0a c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.fsinit + 0xa))
              (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 M1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fsi_0a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    assert (HM2sp : fsi_sp m M2)
      by (rewrite /fsi_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : fsi_thr4 m M2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /M2 upd_ne; [| regne]. exact (HM1thr c Hcs N2 N8 N9 N18). }
    assert (HM2a0 : M2 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.fsinit + 0xa) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0xc)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.mv s2,a0 : s2 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fsinit + 0xc)) Rs2 Ra0
              M2 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_0c with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M2 Ra0))]> M2).
    assert (HM3s2 : M3 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64)).
    { rewrite /M3 upd_eq. rgne. rewrite HM2a0. apply add_vec_zero_l. }
    assert (HM3a0 : M3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2a0 | nz]).
    assert (HM3sp : fsi_sp m M3)
      by (rewrite /fsi_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3thr : fsi_thr4 m M3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /M3 upd_ne; [| regne]. exact (HM2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.fsinit + 0xc) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0xe)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.li a1,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.fsinit + 0xe)) Ra1
              (mword_of_int 1 : mword 6) (sign_extend' 64 bno : mword 64)
              M3 (K - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (fsi_0e with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (M4 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 bno : mword 64)]> M3).
    assert (HM4a1 : M4 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4a0 : M4 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3a0 | nz]).
    assert (HM4s2 : M4 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s2 | nz]).
    assert (HM4sp : fsi_sp m M4)
      by (rewrite /fsi_sp /M4 upd_ne; [exact HM3sp | nz]).
    assert (HM4thr : fsi_thr4 m M4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /M4 upd_ne; [| regne]. exact (HM3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0xe) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fsinit + 0x10)) Rra
              (mword_of_int 2094620 : mword 21) M4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fsi_10 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fsinit + 0x10) : mword 64) 4)]> M4).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.fsinit + 0x10) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094620 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HM5a0 : M5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a0 | nz]).
    assert (HM5a1 : M5 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a1 | nz]).
    assert (HM5s2 : M5 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s2 | nz]).
    assert (HM5sp : fsi_sp m M5)
      by (rewrite /fsi_sp /M5 upd_ne; [exact HM4sp | nz]).
    assert (HM5thr : fsi_thr4 m M5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /M5 upd_ne; [| regne]. exact (HM4thr c Hcs N2 N8 N9 N18). }
    assert (HM5ra : M5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fsinit + 0x10) : mword 64) 4)
      by (rewrite /M5; apply upd_eq).
    iDestruct (iu_slots_split ((LOGBLOCKS + 2) + 2)%nat 1%nat with "Hsl")
      as "[Hsl34 Hsl1]".
    iDestruct (cpu_own_transport CID CID9 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID9 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID9 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID9) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view fsc_fs γd dev fsc_cov) pidv dev bno dq
              M5 (K - 4)%nat eb b lks Vpr
              ltac:(lia) Hbnolt eq_refl Hbnocov eq_refl Hj Hgl
              HM5a0 HM5a1
              (* bread's bound is "bcache"(4); fsinit's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hclmc Htext Hkdata Hpc Hpanenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    iIntros (CID10 Hq10 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hextc Hclmc Hpc Hppid Hheld".
    destruct Hfacts as [Hcsb HmBa0].
    assert (Hpc14 : ret_pc (M5 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.fsinit + 0x14))
      by (rewrite HM5ra; pcw).
    iEval (rewrite Hpc14) in "Hpc".
    pose proof Hcsb as Hcsb_cs.
    assert (HmBs2 : mB !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsb_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HM5s2).
    assert (HmBsp : fsi_sp m mB).
    { rewrite /fsi_sp
        (callee_saved_lookup Hcsb_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM5sp. }
    assert (HmBthr : fsi_thr4 m mB).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcsb_cs c Hcs).
      exact (HM5thr c Hcs N2 N8 N9 N18). }
    (* ---- THE BYTES bread RETURNED ARE THE IMAGE'S BLOCK 1 ---- *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk.
    iDestruct (ds_held_L with "Hheld") as "[HpL Hheldback]".
    iEval (rewrite Hbnou) in "HpL".
    iApply fupd_wp.
    (* RECOVERY HAS NOT RUN YET (durable-disk lane E-except): [readsb] is at
       +0x26 and [initlog] at +0x4e, so what fsinit holds is the WAL's
       EXCEPTION HANDLE, not the seal.  Block 1 is outside the exception
       set -- it is outside the on-disk header's write set at all
       ([FsCrash.hdr_wf]'s block-1 row, lane E-blk1) -- so the crossing is
       the [b ∉ X] form. *)
    assert (Hb1nin : (1 : Z) ∉ (list_to_set (hdr_dec bs_hdr).2 : gset Z)).
    { rewrite elem_of_list_to_set. intros Hc.
      destruct (Hhdrok 1 Hc) as (_ & _ & Hne). apply Hne. reflexivity. }
    iMod (fs_bytes_agree_exc ⊤ (fs_bytes fsc_fs) (fs_cache fsc_fs) (fs_exc fsc_fs)
            (fs_home_set fsc_cov fsc_logst) Xv (list_to_set (hdr_dec bs_hdr).2)
            1 bs_sb bs0 logN_top Hb1nin
            with "Hbinv [$Hxo] Hfsb HpL")
      as "(%Hbs0 & Hxo & Hfsb & HpL)".
    iModIntro.
    iEval (rewrite -Hbnou) in "HpL".
    iDestruct ("Hheldback" with "HpL") as "Hheld".
    subst bs0.
    (* ---- the buffer's data window, and its first 32 bytes ---- *)
    iDestruct (fsi_data_acc with "Hheld") as "(%Hlenb & Hdata & Hdataback)".
    iEval (rewrite Hlenb /bb_bytes) in "Hdata".
    iEval (change 1024%nat with (32 + 992)%nat) in "Hdata".
    iEval (rewrite (bb_split (b_data (bpa kk)) 32 992 (fun jj => bs_sb !!! jj)))
      in "Hdata".
    iDestruct "Hdata" as "[Hsrc Hrest]".
    (* ===== +0x14 c.mv s1,a0 : s1 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fsinit + 0x14)) Rs1 Ra0
              mB (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_14 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (N1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HN1s1 : N1 !!! Regidx Rs1 = bnode kk).
    { rewrite /N1 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HN1a0 : N1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /N1 upd_ne; [exact HmBa0 | nz]).
    assert (HN1s2 : N1 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /N1 upd_ne; [exact HmBs2 | nz]).
    assert (HN1sp : fsi_sp m N1)
      by (rewrite /fsi_sp /N1 upd_ne; [exact HmBsp | nz]).
    assert (HN1thr : fsi_thr4 m N1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /N1 upd_ne; [| regne]. exact (HmBthr c Hcs N2 N8 N9 N18). }
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 li a2,32 : sizeof(struct superblock) ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.fsinit + 0x16)) Ra2
              (mword_of_int 32 : mword 12)
              (mword_of_int (Z.of_nat 32%nat) : mword 64)
              N1 (K - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (fsi_16 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (N2 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 32%nat) : mword 64)]> N1).
    assert (HN2a2 : N2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 32%nat) : mword 64))
      by (rewrite /N2; apply upd_eq).
    assert (HN2a0 : N2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /N2 upd_ne; [exact HN1a0 | nz]).
    assert (HN2s1 : N2 !!! Regidx Rs1 = bnode kk)
      by (rewrite /N2 upd_ne; [exact HN1s1 | nz]).
    assert (HN2s2 : N2 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1s2 | nz]).
    assert (HN2sp : fsi_sp m N2)
      by (rewrite /fsi_sp /N2 upd_ne; [exact HN1sp | nz]).
    assert (HN2thr : fsi_thr4 m N2).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /N2 upd_ne; [| regne]. exact (HN1thr c Hcs N2' N8 N9 N18). }
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x16) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a addi a1,a0,88 : a1 := bp->data ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.fsinit + 0x1a)) Ra1 Ra0
              (mword_of_int 88 : mword 12) N2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_1a with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (N3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget N2 Ra0)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> N2).
    assert (HN3a1 : N3 !!! Regidx Ra1 = b_data (bpa kk)).
    { rewrite /N3 upd_eq. rgne. rewrite HN2a0. apply iu_data_addr. }
    assert (HN3a2 : N3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 32%nat) : mword 64))
      by (rewrite /N3 upd_ne; [exact HN2a2 | nz]).
    assert (HN3a0 : N3 !!! Regidx Ra0 = bnode kk)
      by (rewrite /N3 upd_ne; [exact HN2a0 | nz]).
    assert (HN3s1 : N3 !!! Regidx Rs1 = bnode kk)
      by (rewrite /N3 upd_ne; [exact HN2s1 | nz]).
    assert (HN3s2 : N3 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /N3 upd_ne; [exact HN2s2 | nz]).
    assert (HN3sp : fsi_sp m N3)
      by (rewrite /fsi_sp /N3 upd_ne; [exact HN2sp | nz]).
    assert (HN3thr : fsi_thr4 m N3).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /N3 upd_ne; [| regne]. exact (HN2thr c Hcs N2' N8 N9 N18). }
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x1a) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x1e)) by pcw.
    iEval (rewrite Hpp1e) in "Hpc".
    (* ===== +0x1e auipc a0,0x1d ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.fsinit + 0x1e)) Ra0
              (mword_of_int 29 : mword 20) N3 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_1e with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.fsinit + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> N3).
    assert (HN4a0 : N4 !!! Regidx Ra0
                    = add_vec (mword_of_int (KernelSyms.fsinit + 0x1e) : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /N4; apply upd_eq).
    assert (HN4a1 : N4 !!! Regidx Ra1 = b_data (bpa kk))
      by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
    assert (HN4a2 : N4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 32%nat) : mword 64))
      by (rewrite /N4 upd_ne; [exact HN3a2 | nz]).
    assert (HN4s1 : N4 !!! Regidx Rs1 = bnode kk)
      by (rewrite /N4 upd_ne; [exact HN3s1 | nz]).
    assert (HN4s2 : N4 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /N4 upd_ne; [exact HN3s2 | nz]).
    assert (HN4sp : fsi_sp m N4)
      by (rewrite /fsi_sp /N4 upd_ne; [exact HN3sp | nz]).
    assert (HN4thr : fsi_thr4 m N4).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /N4 upd_ne; [| regne]. exact (HN3thr c Hcs N2' N8 N9 N18). }
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x1e) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 addi a0,a0,950 : a0 := &sb ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.fsinit + 0x22)) Ra0 Ra0
              (mword_of_int 864 : mword 12) N4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_22 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (N5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget N4 Ra0)
                     (sign_extend' 64 (mword_of_int 864 : mword 12)))]> N4).
    assert (HN5a0 : N5 !!! Regidx Ra0 = sb_base).
    { rewrite /N5 upd_eq. rgne. rewrite HN4a0. rewrite /sb_base. pcw. }
    assert (HN5a1 : N5 !!! Regidx Ra1 = b_data (bpa kk))
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (HN5a2 : N5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 32%nat) : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4a2 | nz]).
    assert (HN5s1 : N5 !!! Regidx Rs1 = bnode kk)
      by (rewrite /N5 upd_ne; [exact HN4s1 | nz]).
    assert (HN5s2 : N5 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4s2 | nz]).
    assert (HN5sp : fsi_sp m N5)
      by (rewrite /fsi_sp /N5 upd_ne; [exact HN4sp | nz]).
    assert (HN5thr : fsi_thr4 m N5).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /N5 upd_ne; [| regne]. exact (HN4thr c Hcs N2' N8 N9 N18). }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x22) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 jal ra,memmove : WHERE THE EIGHT CELLS ARE BORN ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fsinit + 0x26)) Rra
              (mword_of_int 2086770 : mword 21) N5 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fsi_26 with "Htext"). }
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (N6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fsinit + 0x26) : mword 64) 4)]> N5).
    assert (Htgtmm : add_vec (mword_of_int (KernelSyms.fsinit + 0x26) : mword 64)
                       (sign_extend' 64 (mword_of_int 2086770 : mword 21))
                     = mword_of_int KernelSyms.memmove) by pcw.
    iEval (rewrite Htgtmm) in "Hpc".
    assert (HN6a0 : N6 !!! Regidx Ra0 = sb_base)
      by (rewrite /N6 upd_ne; [exact HN5a0 | nz]).
    assert (HN6a1 : N6 !!! Regidx Ra1 = b_data (bpa kk))
      by (rewrite /N6 upd_ne; [exact HN5a1 | nz]).
    assert (HN6a2 : N6 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 32%nat) : mword 64))
      by (rewrite /N6 upd_ne; [exact HN5a2 | nz]).
    assert (HN6s1 : N6 !!! Regidx Rs1 = bnode kk)
      by (rewrite /N6 upd_ne; [exact HN5s1 | nz]).
    assert (HN6s2 : N6 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /N6 upd_ne; [exact HN5s2 | nz]).
    assert (HN6sp : fsi_sp m N6)
      by (rewrite /fsi_sp /N6 upd_ne; [exact HN5sp | nz]).
    assert (HN6ra : N6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fsinit + 0x26) : mword 64) 4)
      by (rewrite /N6; apply upd_eq).
    assert (HN6thr : fsi_thr4 m N6).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /N6 upd_ne; [| regne]. exact (HN5thr c Hcs N2' N8 N9 N18). }
    iEval (rewrite -HN6a1) in "Hsrc".
    iEval (rewrite -HN6a0) in "Hsbold".
    iApply (MM.wp_memmove_sconf KT1 KT0 KT0 N6 (K - 4)%nat 32%nat
              (fun jj => bs_sb !!! jj) sb_old (DfracOwn 1) b (proc_addr j)
              ltac:(lia) ltac:(vm_compute; reflexivity) HN6a2
              with "Hcg Htext Hpc Hsrc Hsbold").
    iIntros (CID17 Hq17 mM) "Hcg Hpc Hsrc Hdst %Hmma0 %Hcsmm".
    assert (Hpc2a : ret_pc (N6 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.fsinit + 0x2a))
      by (rewrite HN6ra; pcw).
    iEval (rewrite Hpc2a) in "Hpc".
    iEval (rewrite HN6a1) in "Hsrc".
    iEval (rewrite HN6a0) in "Hdst".
    pose proof Hcsmm as Hcsmm_cs.
    assert (HmMs1 : mM !!! Regidx Rs1 = bnode kk)
      by (rewrite (callee_saved_lookup Hcsmm_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HN6s1).
    assert (HmMs2 : mM !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsmm_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HN6s2).
    assert (HmMsp : fsi_sp m mM).
    { rewrite /fsi_sp
        (callee_saved_lookup Hcsmm_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HN6sp. }
    assert (HmMthr : fsi_thr4 m mM).
    { intros c Hcs N2' N8 N9 N18.
      rewrite (callee_saved_lookup Hcsmm_cs c Hcs).
      exact (HN6thr c Hcs N2' N8 N9 N18). }
    (* ---- the buffer's window is unchanged: rejoin and give it back ---- *)
    iAssert (bb_bytes (b_data (bpa kk)) (length bs_sb) (fun jj => bs_sb !!! jj))
      with "[Hsrc Hrest]" as "Hdata".
    { rewrite Hlenb /bb_bytes.
      iEval (change 1024%nat with (32 + 992)%nat).
      rewrite (bb_split (b_data (bpa kk)) 32 992 (fun jj => bs_sb !!! jj)).
      iSplitL "Hsrc"; [iExact "Hsrc" | iExact "Hrest"]. }
    iDestruct ("Hdataback" with "Hdata") as "Hheld".
    (* ================================================================= *)
    (*  THE BRIDGE: 32 raw bytes at [&sb] become the eight typed cells.   *)
    (* ================================================================= *)
    iDestruct (bb_chunk 4 8 sb_base (fun jj => bs_sb !!! jj) with "Hdst")
      as "Hdst".
    iEval (cbn [seq]) in "Hdst".
    iDestruct "Hdst" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & _)".
    iDestruct (fsi_word4 sb_base (0 * 4)%nat v_magic (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (0 * 4 + jj)%nat with (4 * 0 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 0 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 0%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W0") as "Hmg".
    iDestruct (fsi_word4 sb_base (1 * 4)%nat v_size (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (1 * 4 + jj)%nat with (4 * 1 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 1 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 1%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W1") as "Hsz".
    iDestruct (fsi_word4 sb_base (2 * 4)%nat v_nblocks (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (2 * 4 + jj)%nat with (4 * 2 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 2 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 2%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W2") as "Hnb".
    iDestruct (fsi_word4 sb_base (3 * 4)%nat (mword_of_int ninodes : mword 32)
                 (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (3 * 4 + jj)%nat with (4 * 3 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 3 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 3%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W3") as "Hni".
    iDestruct (fsi_word4 sb_base (4 * 4)%nat v_nlog (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (4 * 4 + jj)%nat with (4 * 4 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 4 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 4%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W4") as "Hnl".
    iDestruct (fsi_word4 sb_base (5 * 4)%nat (mword_of_int fsc_logst : mword 32)
                 (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (5 * 4 + jj)%nat with (4 * 5 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 5 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 5%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W5") as "Hls".
    iDestruct (fsi_word4 sb_base (6 * 4)%nat (mword_of_int inodestart : mword 32)
                 (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (6 * 4 + jj)%nat with (4 * 6 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 6 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 6%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W6") as "Hist".
    iDestruct (fsi_word4 sb_base (7 * 4)%nat (mword_of_int bmapstart : mword 32)
                 (fun jj => bs_sb !!! jj)
                 ltac:(vm_compute; reflexivity)
                 ltac:(intros jj Hjj;
                       replace (7 * 4 + jj)%nat with (4 * 7 + jj)%nat by lia;
                       rewrite (Hfimg (4 * 7 + jj)%nat ltac:(lia));
                       rewrite (fsi_img _ _ _ _ _ _ _ _ 7%nat jj
                                  ltac:(lia) Hjj); reflexivity)
                 with "W7") as "Hbms".
    (* the four addresses the rest of the tree already names *)
    iEval (change (pa_add sb_base (0 * 4)%nat) with sb_magic) in "Hmg".
    iEval (rewrite -(sb_size_addr)) in "Hsz".
    iEval (change (pa_add sb_base (2 * 4)%nat) with sb_nblocks) in "Hnb".
    iEval (rewrite -(sb_ninodes_addr)) in "Hni".
    iEval (change (pa_add sb_base (4 * 4)%nat) with sb_nlog) in "Hnl".
    iEval (change (pa_add sb_base (5 * 4)%nat) with sb_logstart) in "Hls".
    iEval (rewrite -(sb_inodestart_addr)) in "Hist".
    iEval (rewrite -(sb_bmapstart_addr)) in "Hbms".
    (* ===== +0x2a c.mv a0,s1 : a0 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fsinit + 0x2a)) Ra0 Rs1
              mM (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_2a with "Htext"). }
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (Q0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mM Rs1))]> mM).
    assert (HQ0a0 : Q0 !!! Regidx Ra0 = bnode kk).
    { rewrite /Q0 upd_eq. rgne. rewrite HmMs1. apply add_vec_zero_l. }
    assert (HQ0s2 : Q0 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q0 upd_ne; [exact HmMs2 | nz]).
    assert (HQ0sp : fsi_sp m Q0)
      by (rewrite /fsi_sp /Q0 upd_ne; [exact HmMsp | nz]).
    assert (HQ0thr : fsi_thr4 m Q0).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q0 upd_ne; [| regne]. exact (HmMthr c Hcs N2' N8 N9 N18). }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    (* ===== +0x2c jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fsinit + 0x2c)) Rra
              (mword_of_int 2094856 : mword 21) Q0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fsi_2c with "Htext"). }
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (Q1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fsinit + 0x2c) : mword 64) 4)]> Q0).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.fsinit + 0x2c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094856 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HQ1a0 : Q1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /Q1 upd_ne; [exact HQ0a0 | nz]).
    assert (HQ1s2 : Q1 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q1 upd_ne; [exact HQ0s2 | nz]).
    assert (HQ1sp : fsi_sp m Q1)
      by (rewrite /fsi_sp /Q1 upd_ne; [exact HQ0sp | nz]).
    assert (HQ1ra : Q1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fsinit + 0x2c) : mword 64) 4)
      by (rewrite /Q1; apply upd_eq).
    assert (HQ1thr : fsi_thr4 m Q1).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q1 upd_ne; [| regne]. exact (HQ0thr c Hcs N2' N8 N9 N18). }
    iDestruct (cpu_own_transport CID10 CID19 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID10 CID19 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID10 CID19 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID9) (CIDb := CID19) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (BL.wp_brelse_sconf γs bn (fs_view fsc_fs γd dev fsc_cov) kk
              pidv dev bno dq Q1 (K - 4)%nat eb (proc_addr j)
              bs_sb bsd0 d0 b lks Vpr
              ltac:(lia) Hkk HQ1a0
              (* brelse's bound is "bcache"(4); fsinit's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs [Hheld]").
    all: try lkbelow.
    { rewrite /bio_locked. iExact "Hheld". }
    iIntros (CID20 Hq20 mR) "%Hcsbl Hcg Hcnt Hpc Hppid Hslot".
    assert (Hpc30 : ret_pc (Q1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.fsinit + 0x30))
      by (rewrite HQ1ra; pcw).
    iEval (rewrite Hpc30) in "Hpc".
    pose proof Hcsbl as Hcsbl_cs.
    assert (HmRs2 : mR !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsbl_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HQ1s2).
    assert (HmRsp : fsi_sp m mR).
    { rewrite /fsi_sp
        (callee_saved_lookup Hcsbl_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQ1sp. }
    assert (HmRthr : fsi_thr4 m mR).
    { intros c Hcs N2' N8 N9 N18.
      rewrite (callee_saved_lookup Hcsbl_cs c Hcs).
      exact (HQ1thr c Hcs N2' N8 N9 N18). }
    (* ===== +0x30 auipc a4,0x1d ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.fsinit + 0x30)) Ra4
              (mword_of_int 29 : mword 20) mR (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_30 with "Htext"). }
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (Q2 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.fsinit + 0x30) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> mR).
    assert (HQ2a4 : Q2 !!! Regidx Ra4
                    = add_vec (mword_of_int (KernelSyms.fsinit + 0x30) : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /Q2; apply upd_eq).
    assert (HQ2s2 : Q2 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q2 upd_ne; [exact HmRs2 | nz]).
    assert (HQ2sp : fsi_sp m Q2)
      by (rewrite /fsi_sp /Q2 upd_ne; [exact HmRsp | nz]).
    assert (HQ2thr : fsi_thr4 m Q2).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q2 upd_ne; [| regne]. exact (HmRthr c Hcs N2' N8 N9 N18). }
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x30) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x34)) by pcw.
    iEval (rewrite Hpp34) in "Hpc".
    (* ===== +0x34 lw a4,932(a4) : a4 := sb.magic ===== *)
    assert (Hmgadr : add_vec (rget Q2 Ra4)
                       (sign_extend' 64 (mword_of_int 846 : mword 12))
                     = sb_magic).
    { rgne. rewrite HQ2a4. rewrite /sb_magic /sb_base /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hmgadr) in "Hmg".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.fsinit + 0x34)) Ra4 Ra4
              (mword_of_int 846 : mword 12) Q2 (K - 4)%nat v_magic b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmg").
    { iApply (fsi_34 with "Htext"). }
    iIntros (CID22 Hq22) "Hcg Hpc Hmg".
    iEval (rewrite Hmgadr) in "Hmg".
    set (Q3 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 v_magic)]> Q2).
    assert (HQ3a4 : Q3 !!! Regidx Ra4 = (mword_of_int 0x10203040 : mword 64)).
    { rewrite /Q3 upd_eq. rewrite (ds_sext_small v_magic ltac:(rewrite Hmagic;
        unfold FSMAGIC; lia)). rewrite Hmagic. unfold FSMAGIC. reflexivity. }
    assert (HQ3s2 : Q3 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2s2 | nz]).
    assert (HQ3sp : fsi_sp m Q3)
      by (rewrite /fsi_sp /Q3 upd_ne; [exact HQ2sp | nz]).
    assert (HQ3thr : fsi_thr4 m Q3).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q3 upd_ne; [| regne]. exact (HQ2thr c Hcs N2' N8 N9 N18). }
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x34) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x38)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    (* ===== +0x38 lui a5,0x10203 ===== *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.fsinit + 0x38)) Ra5
              (mword_of_int 66051 : mword 20)
              (luival (mword_of_int 66051 : mword 20))
              Q3 (K - 4)%nat b ltac:(nz) ltac:(rdok) eq_refl
              with "Hcg Hpc []").
    { iApply (fsi_38 with "Htext"). }
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (Q4 := <[Regidx Ra5 := regval_into_reg
                  (luival (mword_of_int 66051 : mword 20))]> Q3).
    assert (HQ4a5 : Q4 !!! Regidx Ra5 = luival (mword_of_int 66051 : mword 20))
      by (rewrite /Q4; apply upd_eq).
    assert (HQ4a4 : Q4 !!! Regidx Ra4 = (mword_of_int 0x10203040 : mword 64))
      by (rewrite /Q4 upd_ne; [exact HQ3a4 | nz]).
    assert (HQ4s2 : Q4 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q4 upd_ne; [exact HQ3s2 | nz]).
    assert (HQ4sp : fsi_sp m Q4)
      by (rewrite /fsi_sp /Q4 upd_ne; [exact HQ3sp | nz]).
    assert (HQ4thr : fsi_thr4 m Q4).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q4 upd_ne; [| regne]. exact (HQ3thr c Hcs N2' N8 N9 N18). }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x38) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c addi a5,a5,64 : a5 := FSMAGIC ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.fsinit + 0x3c)) Ra5 Ra5
              (mword_of_int 64 : mword 12) Q4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_3c with "Htext"). }
    iIntros (CID24 Hq24) "Hcg Hpc".
    set (Q5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget Q4 Ra5)
                     (sign_extend' 64 (mword_of_int 64 : mword 12)))]> Q4).
    assert (HQ5a5 : Q5 !!! Regidx Ra5 = (mword_of_int 0x10203040 : mword 64)).
    { rewrite /Q5 upd_eq. rgne. rewrite HQ4a5. pcw. }
    assert (HQ5a4 : Q5 !!! Regidx Ra4 = (mword_of_int 0x10203040 : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4a4 | nz]).
    assert (HQ5s2 : Q5 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4s2 | nz]).
    assert (HQ5sp : fsi_sp m Q5)
      by (rewrite /fsi_sp /Q5 upd_ne; [exact HQ4sp | nz]).
    assert (HQ5thr : fsi_thr4 m Q5).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q5 upd_ne; [| regne]. exact (HQ4thr c Hcs N2' N8 N9 N18). }
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x3c) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 bne a4,a5 : THE PANIC ARM, REFUTED BY THE IMAGE ===== *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.fsinit + 0x40))
              (mword_of_int 36 : mword 13) Ra5 Ra4 Q5 (K - 4)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HQ5a4 HQ5a5; apply fsi_neq_self)
              with "Hcg Hpc []").
    { iApply (fsi_40 with "Htext"). }
    iIntros (CID25 Hq25) "Hcg Hpc".
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x40) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x44)) by pcw.
    iEval (rewrite Hpp44) in "Hpc".
    (* ===== +0x44 auipc a1,0x1d ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.fsinit + 0x44)) Ra1
              (mword_of_int 29 : mword 20) Q5 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_44 with "Htext"). }
    iIntros (CID26 Hq26) "Hcg Hpc".
    set (Q6 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.fsinit + 0x44) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> Q5).
    assert (HQ6a1 : Q6 !!! Regidx Ra1
                    = add_vec (mword_of_int (KernelSyms.fsinit + 0x44) : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /Q6; apply upd_eq).
    assert (HQ6s2 : Q6 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q6 upd_ne; [exact HQ5s2 | nz]).
    assert (HQ6sp : fsi_sp m Q6)
      by (rewrite /fsi_sp /Q6 upd_ne; [exact HQ5sp | nz]).
    assert (HQ6thr : fsi_thr4 m Q6).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q6 upd_ne; [| regne]. exact (HQ5thr c Hcs N2' N8 N9 N18). }
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x44) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x48)) by pcw.
    iEval (rewrite Hpp48) in "Hpc".
    (* ===== +0x48 addi a1,a1,912 : a1 := &sb ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.fsinit + 0x48)) Ra1 Ra1
              (mword_of_int 826 : mword 12) Q6 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_48 with "Htext"). }
    iIntros (CID27 Hq27) "Hcg Hpc".
    set (Q7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget Q6 Ra1)
                     (sign_extend' 64 (mword_of_int 826 : mword 12)))]> Q6).
    assert (HQ7a1 : Q7 !!! Regidx Ra1 = sb_base).
    { rewrite /Q7 upd_eq. rgne. rewrite HQ6a1. rewrite /sb_base. pcw. }
    assert (HQ7s2 : Q7 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q7 upd_ne; [exact HQ6s2 | nz]).
    assert (HQ7sp : fsi_sp m Q7)
      by (rewrite /fsi_sp /Q7 upd_ne; [exact HQ6sp | nz]).
    assert (HQ7thr : fsi_thr4 m Q7).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q7 upd_ne; [| regne]. exact (HQ6thr c Hcs N2' N8 N9 N18). }
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x48) : mword 64) 4
                    = mword_of_int (KernelSyms.fsinit + 0x4c)) by pcw.
    iEval (rewrite Hpp4c) in "Hpc".
    (* ===== +0x4c c.mv a0,s2 : a0 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fsinit + 0x4c)) Ra0 Rs2
              Q7 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_4c with "Htext"). }
    iIntros (CID28 Hq28) "Hcg Hpc".
    set (Q8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget Q7 Rs2))]> Q7).
    assert (HQ8a0 : Q8 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /Q8 upd_eq. rgne. rewrite HQ7s2. apply add_vec_zero_l. }
    assert (HQ8a1 : Q8 !!! Regidx Ra1 = sb_base)
      by (rewrite /Q8 upd_ne; [exact HQ7a1 | nz]).
    assert (HQ8s2 : Q8 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q8 upd_ne; [exact HQ7s2 | nz]).
    assert (HQ8sp : fsi_sp m Q8)
      by (rewrite /fsi_sp /Q8 upd_ne; [exact HQ7sp | nz]).
    assert (HQ8thr : fsi_thr4 m Q8).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q8 upd_ne; [| regne]. exact (HQ7thr c Hcs N2' N8 N9 N18). }
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x4c) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x4e)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    (* ===== +0x4e jal ra,initlog : THE LOG LAYER IS BUILT HERE ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fsinit + 0x4e)) Rra
              (mword_of_int 1630 : mword 21) Q8 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fsi_4e with "Htext"). }
    iIntros (CID29 Hq29) "Hcg Hpc".
    set (Q9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fsinit + 0x4e) : mword 64) 4)]> Q8).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.fsinit + 0x4e) : mword 64)
                       (sign_extend' 64 (mword_of_int 1630 : mword 21))
                     = mword_of_int KernelSyms.initlog) by pcw.
    iEval (rewrite Htgtil) in "Hpc".
    assert (HQ9a0 : Q9 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q9 upd_ne; [exact HQ8a0 | nz]).
    assert (HQ9a1 : Q9 !!! Regidx Ra1 = sb_base)
      by (rewrite /Q9 upd_ne; [exact HQ8a1 | nz]).
    assert (HQ9s2 : Q9 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Q9 upd_ne; [exact HQ8s2 | nz]).
    assert (HQ9sp : fsi_sp m Q9)
      by (rewrite /fsi_sp /Q9 upd_ne; [exact HQ8sp | nz]).
    assert (HQ9ra : Q9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fsinit + 0x4e) : mword 64) 4)
      by (rewrite /Q9; apply upd_eq).
    assert (HQ9thr : fsi_thr4 m Q9).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /Q9 upd_ne; [| regne]. exact (HQ8thr c Hcs N2' N8 N9 N18). }
    iDestruct (cpu_own_transport CID20 CID29 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID19 CID29 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID19 CID29 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID19) (CIDb := CID29) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* the boot dirty map is [false] on the covered range: the pure form
       the general initlog contract consumes (durable-disk stage D1) *)
    iDestruct (initlog_dirty_all_false fsc_fs D fsc_cov with "HauthD Hdirty")
      as "(%HDall & HauthD & Hdirty)".
    iApply (IL.wp_initlog_sconf γs j γl γu γd γk pd pav pu bn icfg_log fsc_fs γpr
              fsc_cov fsc_logst dev sb_base bs_hdr Xv
              Mbrn L D
              vlock vname vcpu v_start v_dev v_nc v_n
              pidv dq (DfracOwn 1) Q9 (K - 4)%nat eb b lks Vpr
              bs_sb sbrec
              ltac:(lia) Hgeom Hj Hgl
              Hhdrbnd Hhdrnd
              ltac:(intros b0 Hb0; destruct (Hhdrok b0 Hb0) as (Hc & Hl & _);
                    exact (conj Hc Hl))
              Hpk
              HQ9a0 HQ9a1 HDall HLmir
              (* initlog's bound is "bcache"(4); fsinit's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              (* block 1's two pure facts, straight from the contract
                 (durable-disk lane C-3a) *)
              Hsbok Hsbparse Hxvslot
              with "Hcg Hcnt Hextc Hclmc Htext Hkdata Hpc Hpanenv Hbio Hseam
                    Hpenv Hgen Hmirror
                    Hlfree
                    Hppid Hprocs Hdevi Hdgeom Hdlock Hls Hlock0 Hlname Hlcpu
                    Hlstart Hldev Hlout Hlcmt Hlnc Hlhn Hlhblk Hbinv Hxo HauthL HauthD
                    Hdirty Hhdr Hlslots Hsl34 Hfsb Hlawf").
    all: try lkbelow.
    iIntros (CID30 Hq30 mI) "%Hcsil Hcg Hcnt Hextc Hclmc Hpc Hppid Hls Hsl2 Hlctx".
    (* RECOVERY IS DONE (durable-disk lane E-except): [initlog] has sealed
       the byte view's exception set into [LogInv.log_ctx], so the region
       and the bitmap can be upgraded from their PowerOn forms to the ones
       every consumer above takes. *)
    iPoseProof (log_ctx_seal with "Hlctx") as "#Hbseal".
    iDestruct (ireg_inv_of with "Hireg Hbseal") as "#HiregS".
    iDestruct (bitmap_inv_of with "Hbm Hbseal") as "#HbmS".
    assert (Hpc52 : ret_pc (Q9 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.fsinit + 0x52))
      by (rewrite HQ9ra; pcw).
    iEval (rewrite Hpc52) in "Hpc".
    pose proof Hcsil as Hcsil_cs.
    assert (HmIs2 : mI !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsil_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HQ9s2).
    assert (HmIsp : fsi_sp m mI).
    { rewrite /fsi_sp
        (callee_saved_lookup Hcsil_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQ9sp. }
    assert (HmIthr : fsi_thr4 m mI).
    { intros c Hcs N2' N8 N9 N18.
      rewrite (callee_saved_lookup Hcsil_cs c Hcs).
      exact (HQ9thr c Hcs N2' N8 N9 N18). }
    (* the held-back slot rejoins initlog's two: THREE for ireclaim *)
    iDestruct (iu_slots_join 2%nat 1%nat with "Hsl2 Hslot") as "Hsl3".
    iEval (change (2 + 1)%nat with 3%nat) in "Hsl3".
    (* ===== +0x52 c.mv a0,s2 : a0 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fsinit + 0x52)) Ra0 Rs2
              mI (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsi_52 with "Htext"). }
    iIntros (CID31 Hq31) "Hcg Hpc".
    set (R0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mI Rs2))]> mI).
    assert (HR0a0 : R0 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R0 upd_eq. rgne. rewrite HmIs2. apply add_vec_zero_l. }
    assert (HR0sp : fsi_sp m R0)
      by (rewrite /fsi_sp /R0 upd_ne; [exact HmIsp | nz]).
    assert (HR0thr : fsi_thr4 m R0).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /R0 upd_ne; [| regne]. exact (HmIthr c Hcs N2' N8 N9 N18). }
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.fsinit + 0x52) : mword 64) 2
                    = mword_of_int (KernelSyms.fsinit + 0x54)) by pcw.
    iEval (rewrite Hpp54) in "Hpc".
    (* ===== +0x54 jal ra,ireclaim ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fsinit + 0x54)) Rra
              (mword_of_int 2096868 : mword 21) R0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fsi_54 with "Htext"). }
    iIntros (CID32 Hq32) "Hcg Hpc".
    set (R1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fsinit + 0x54) : mword 64) 4)]> R0).
    assert (Htgtir : add_vec (mword_of_int (KernelSyms.fsinit + 0x54) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096868 : mword 21))
                     = mword_of_int KernelSyms.ireclaim) by pcw.
    iEval (rewrite Htgtir) in "Hpc".
    assert (HR1a0 : R1 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R1 upd_ne; [exact HR0a0 | nz]).
    assert (HR1sp : fsi_sp m R1)
      by (rewrite /fsi_sp /R1 upd_ne; [exact HR0sp | nz]).
    assert (HR1ra : R1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fsinit + 0x54) : mword 64) 4)
      by (rewrite /R1; apply upd_eq).
    assert (HR1thr : fsi_thr4 m R1).
    { intros c Hcs N2' N8 N9 N18.
      rewrite /R1 upd_ne; [| regne]. exact (HR0thr c Hcs N2' N8 N9 N18). }
    (* [log_ctx] is PERSISTENT, and it has to be: ireclaim consumes it at
       +0x54 and the contract hands it to the caller afterwards.  No
       existential to open any more -- initlog built the layer at
       [icfg_log], the name the era fupd minted. *)
    iDestruct "Hlctx" as "#Hlctx".
    iDestruct (cpu_own_transport CID30 CID32 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID30 CID32 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID30 CID32 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID29) (CIDb := CID32) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (IR.wp_ireclaim_sconf γs j γl γu γd γk pd pav pu bn
              icfg_log γi gtl γpr bmapstart inodestart
              ninodes nib size dev pidv dq (DfracOwn 1) (DfracOwn 1)
              (DfracOwn 1) R1 (K - 4)%nat eb b lks Vpr
              ltac:(lia) Hgeom Hist0 Hblk Hsize Hbm0
              Hbmcov Hbmlog Hcovb Hn1 Hnnib Hn31 Hpk Hj Hgl HR1a0
              Hbelow eq_refl
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hkdata Hpenv Hbio Hlctx Hseam
                    Hgen Hni Hist Hbms HiregS Hboot Hitb2 Hitbl Hesc Hslks HbmS Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hsl3 Hiref").
    all: try lkbelow.
    iIntros (CID33 Hq33 mf) "%Hcsir Hcg Hcnt Hextc Hclmc Hpc Hni Hist Hbms Hppid
                             Hsl3 Hiref Hboot".
    assert (Hpc58 : ret_pc (R1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.fsinit + 0x58))
      by (rewrite HR1ra; pcw).
    iEval (rewrite Hpc58) in "Hpc".
    pose proof Hcsir as Hcsir_cs.
    assert (Hmfsp : fsi_sp m mf).
    { rewrite /fsi_sp
        (callee_saved_lookup Hcsir_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR1sp. }
    assert (Hmfthr : fsi_thr4 m mf).
    { intros c Hcs N2' N8 N9 N18.
      rewrite (callee_saved_lookup Hcsir_cs c Hcs).
      exact (HR1thr c Hcs N2' N8 N9 N18). }
    iApply (fsi_epilogue (CID0 := CID33) j bn bmapstart
              inodestart ninodes size dev v_magic v_size v_nblocks
              v_nlog pidv dq m mf K eb b lks Vpr HK Hmfsp Hmfthr
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hframe Hppid Hmg Hsz Hnb Hni Hnl Hls
                    Hist Hbms Hlctx Hsl3 Hiref Hboot [Hcont]").
    { iApply (wp_next_shift (b := true) (CIDa := CID32) (CIDb := CID33)
                ltac:(wp_next_chain) with "Hcont"). }
  Qed.

End FsinitMain.

End FsinitProof.
