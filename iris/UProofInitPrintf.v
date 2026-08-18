(* UProofInitPrintf.v -- init's PRINTF CONE: [vprintf] on a %-free format
   string, and [printf] on top of it.
   (claude-notes/projects/user-init.md; the contracts are USpecInit.v.)

   This is the first verified xv6 printf.  The scope is exactly the class
   of format strings init passes -- [init_lit]: NUL-terminated, no NUL
   inside, and NO '%' -- so [vprintf]'s state machine never leaves state 0
   and the whole [printint]/[printptr]/`%'-dispatch half of the function
   is unreachable.  What remains is one loop, one byte at a time, through
   [putc] and [write].

   THE LOOP IS BOUNDED (by the string's length), so it is ordinary Rocq
   induction on a strict nat measure and needs no [|>] from any leaf --
   the rule from user-echo.md.  init's UNBOUNDED loops are in main.

   The bookkeeping that dominates the proof is vprintf's TEN spilled
   registers (ra, s0..s8 -- gcc saves every callee-saved register it uses
   in the loop): each is stored in the prologue, must survive [putc]'s
   frame writes below sp, and is reloaded in the epilogue.  [vp_frame]
   bundles the ten, and it survives everything the loop does because
   [putc]'s window is [sp0-128, sp0-96) and the frame is [sp0-96, sp0). *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo
               UmodeInitIo UmodeFetch.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeInit USpecInit UProofInitLib.
Require User.InitSyms User.InitInstrs User.InitData.
Local Open Scope Z_scope.
Import Defs.
Import ListNotations.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 Helpers.                                                            *)
(* ===================================================================== *)

(* HOIST CANDIDATE (UmodeArith.v): x0 as a SOURCE reads as the identity. *)
Lemma add_vec_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  assert (Hz : (zero_reg : mword 64) = mword_of_int 0)
    by (apply bv_eq; vm_compute; reflexivity).
  transitivity (mword_of_int (0 + bv_unsigned x) : mword 64).
  - rewrite Hz. rewrite <- moi_add. f_equal. symmetry. apply moi_of_unsigned.
  - rewrite Z.add_0_l. apply moi_of_unsigned.
Qed.

Lemma zero_reg_moi : (zero_reg : mword 64) = mword_of_int 0.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the byte a [lbu] result carries, at the image's own spelling *)
Lemma nth_byte_moi8 (b : bv 8) :
  nth_byte (mword_of_int (bv_unsigned b) : mword 64) 0 = b.
Proof.
  pose proof (bv_unsigned_in_range _ b) as Hr.
  assert (E8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E8 in Hr.
  assert (Hms : bv_unsigned (mword_of_int (bv_unsigned b) : mword 64)
                = bv_unsigned b) by (apply moi_small; unfold Z64; lia).
  apply bv_eq. rewrite nth_byte_unsigned. rewrite Hms.
  replace (Z.of_N (8 * N.of_nat 0)) with 0 by (vm_compute; reflexivity).
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. apply Z.mod_small. lia.
Qed.

(* image invariants carried across a write that misses the image *)
Lemma init_img_only (M M' : gmap Z (bv 8)) (a n : Z) :
  8192 <= a -> uM_only M M' a n -> init_img_sub M -> init_img_sub M'.
Proof.
  intros Ha Ho [Ht Hd]. split.
  - refine (uM_only_img InitInstrs.init_bytes M M' a n _ Ho Ht).
    intros kk bb Hkb. pose proof (init_bytes_key_lt kk bb Hkb). lia.
  - refine (uM_only_img InitData.init_data M M' a n _ Ho Hd).
    intros kk bb Hkb. pose proof (init_data_key_lt kk bb Hkb). lia.
Qed.

Lemma init_lit_only (M M' : gmap Z (bv 8)) (a n s : Z) (bs : list (bv 8)) :
  4096 <= a -> uM_only M M' a n -> init_lit M s bs -> init_lit M' s bs.
Proof.
  intros Ha [_ E] [Hne [Hb Hn] Hnz Hpc Hlo Hhi]. constructor; try assumption.
  split.
  - intros j c Hj. pose proof (lookup_lt_Some bs j c Hj) as Hjl.
    rewrite (E (s + Z.of_nat j) ltac:(left; lia)). exact (Hb j c Hj).
  - rewrite (E (s + Z.of_nat (length bs)) ltac:(left; lia)). exact Hn.
Qed.

(* ===================================================================== *)
(* §1 [vp_frame] -- vprintf's ten spilled words.                          *)
(* ===================================================================== *)

Definition vp_frame (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) : Prop :=
  uM_bytes M (uint sp0 - 96 + 88) 8 (m !!! Regidx (mword_of_int 1 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 80) 8 (m !!! Regidx (mword_of_int 8 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 72) 8 (m !!! Regidx (mword_of_int 9 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 64) 8 (m !!! Regidx (mword_of_int 18 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 56) 8 (m !!! Regidx (mword_of_int 19 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 48) 8 (m !!! Regidx (mword_of_int 20 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 40) 8 (m !!! Regidx (mword_of_int 21 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 32) 8 (m !!! Regidx (mword_of_int 22 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 24) 8 (m !!! Regidx (mword_of_int 23 : mword 5)) /\
  uM_bytes M (uint sp0 - 96 + 16) 8 (m !!! Regidx (mword_of_int 24 : mword 5)).

(* the frame is ABOVE everything the callee writes, so it survives *)
Lemma vp_frame_only (M M' : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64)
    (a n : Z) :
  uM_only M M' a n -> a + n <= uint sp0 - 96 ->
  vp_frame M m sp0 -> vp_frame M' m sp0.
Proof.
  intros Ho Hn (H88 & H80 & H72 & H64 & H56 & H48 & H40 & H32 & H24 & H16).
  assert (K : forall (d : Z) (w : mword 64), 0 <= d ->
            uM_bytes M (uint sp0 - 96 + d) 8 w ->
            uM_bytes M' (uint sp0 - 96 + d) 8 w).
  { intros d w Hd Hb.
    exact (uM_bytes_only M M' (uint sp0 - 96 + d) a n 8 w Ho
             ltac:(right; lia) Hb). }
  split_and!; (apply K; [ lia | assumption ]).
Qed.


(* The callee-saved registers vprintf does NOT touch -- gp, tp, s9, s10,
   s11.  Everything else in the callee-saved set (sp, s0, s1, s2..s8) it
   spills in the prologue and reloads in the epilogue, so an intermediate
   register file agrees with the entry file exactly off those ten. *)
Definition vp_rest (mx m : regfile) : Prop :=
  forall r : mword 5, ucallee_saved_idx r = true ->
    Regidx r <> Regidx (mword_of_int 2 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 8 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 9 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 18 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 19 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 20 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 21 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 22 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 23 : mword 5) ->
    Regidx r <> Regidx (mword_of_int 24 : mword 5) ->
    mx !!! Regidx r = m !!! Regidx r.

(* ===================================================================== *)
(* §2 The proofs.                                                         *)
(* ===================================================================== *)

Section UProofInitPrintf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).
  Context (W : Z -> list (bv 8) -> iProp Σ).

  Local Notation Pinit := (xv6_init_protocol C pt Q W).

  (* ------------------------------------------------------------------- *)
  (* §2a vprintf's EPILOGUE, 0x6fc .. 0x712: reload the ten spilled       *)
  (* words, drop the frame, return.  It is the join point of both exits   *)
  (* (the empty-string arm at 0x4e4 does not spill s2..s8 and leaves at   *)
  (* 0x70a instead -- not reachable here, since [init_lit] strings are    *)
  (* non-empty).                                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma init_vprintf_epi (CIDp : CpuId) (Mx : gmap Z (bv 8)) (mx m : regfile)
      (sp0 : mword 64) :
    init_layout pt ->
    init_text_sub Mx ->
    uv_stack pt Mx sp0 96 ->
    vp_frame Mx m sp0 ->
    m !!! Regidx sp_idx = sp0 ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    mx !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64) ->
    vp_rest mx m ->
    uv_cap_gpr (CID := CIDp) C pt Pinit Mx mx -∗
    pc_is (CID := CIDp) (mword_of_int 0x6fc) -∗
    (∀ (CID : CpuId) (m' : regfile),
       ⌜ucallee_saved m m'⌝ -∗
       uv_cap_gpr (CID := CID) C pt Pinit Mx m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Htext Hst96 Hvf Hspm Hret2 Hsp_mx Hcs.
    destruct Hvf as (Hf88 & Hf80 & Hf72 & Hf64 & Hf56 & Hf48 & Hf40 & Hf32 &
                     Hf24 & Hf16).
    pose proof (us_lo _ _ _ _ Hst96) as Hlo.
    pose proof (us_canon _ _ _ _ Hst96) as Hhi.
    change (2 ^ 38) with 274877906944 in Hhi.
    iIntros "Hcg Hpc Hcont".

    (* ---- 0x6fc  c.ldsp s2,64(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDp Pinit Mx mx sp0 (mword_of_int 0x6fc)
              (mword_of_int 8 : mword 6) (mword_of_int 18 : mword 5) 96 64
              (m !!! Regidx (mword_of_int 18 : mword 5))
              (ui_init_6fc pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_mx
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 64) _ Hf64))
              with "Hcg Hpc").
    iIntros (L1) "Hcg Hpc".
    set (n1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> mx).
    assert (Hsp_n1 : n1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne mx (Regidx (mword_of_int 18 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_mx).
    assert (E6fc : add_vec_int (mword_of_int 0x6fc : mword 64) 2
                   = mword_of_int 0x6fe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E6fc) in "Hpc".

    (* ---- 0x6fe  c.ldsp s3,56(sp) ---- *)
    iApply (wp_uv_frame_load C pt L1 Pinit Mx n1 sp0 (mword_of_int 0x6fe)
              (mword_of_int 7 : mword 6) (mword_of_int 19 : mword 5) 96 56
              (m !!! Regidx (mword_of_int 19 : mword 5))
              (ui_init_6fe pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 56) _ Hf56))
              with "Hcg Hpc").
    iIntros (L2) "Hcg Hpc".
    set (n2 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> n1).
    assert (Hsp_n2 : n2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n1 (Regidx (mword_of_int 19 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n1).
    assert (E6fe : add_vec_int (mword_of_int 0x6fe : mword 64) 2
                   = mword_of_int 0x700)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E6fe) in "Hpc".

    (* ---- 0x700  c.ldsp s4,48(sp) ---- *)
    iApply (wp_uv_frame_load C pt L2 Pinit Mx n2 sp0 (mword_of_int 0x700)
              (mword_of_int 6 : mword 6) (mword_of_int 20 : mword 5) 96 48
              (m !!! Regidx (mword_of_int 20 : mword 5))
              (ui_init_700 pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 48) _ Hf48))
              with "Hcg Hpc").
    iIntros (L3) "Hcg Hpc".
    set (n3 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 20 : mword 5))]> n2).
    assert (Hsp_n3 : n3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n2 (Regidx (mword_of_int 20 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n2).
    assert (E700 : add_vec_int (mword_of_int 0x700 : mword 64) 2
                   = mword_of_int 0x702)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E700) in "Hpc".

    (* ---- 0x702  c.ldsp s5,40(sp) ---- *)
    iApply (wp_uv_frame_load C pt L3 Pinit Mx n3 sp0 (mword_of_int 0x702)
              (mword_of_int 5 : mword 6) (mword_of_int 21 : mword 5) 96 40
              (m !!! Regidx (mword_of_int 21 : mword 5))
              (ui_init_702 pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 40) _ Hf40))
              with "Hcg Hpc").
    iIntros (L4) "Hcg Hpc".
    set (n4 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 21 : mword 5))]> n3).
    assert (Hsp_n4 : n4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n3 (Regidx (mword_of_int 21 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n3).
    assert (E702 : add_vec_int (mword_of_int 0x702 : mword 64) 2
                   = mword_of_int 0x704)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E702) in "Hpc".

    (* ---- 0x704  c.ldsp s6,32(sp) ---- *)
    iApply (wp_uv_frame_load C pt L4 Pinit Mx n4 sp0 (mword_of_int 0x704)
              (mword_of_int 4 : mword 6) (mword_of_int 22 : mword 5) 96 32
              (m !!! Regidx (mword_of_int 22 : mword 5))
              (ui_init_704 pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 32) _ Hf32))
              with "Hcg Hpc").
    iIntros (L5) "Hcg Hpc".
    set (n5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 22 : mword 5))]> n4).
    assert (Hsp_n5 : n5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n4 (Regidx (mword_of_int 22 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n4).
    assert (E704 : add_vec_int (mword_of_int 0x704 : mword 64) 2
                   = mword_of_int 0x706)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E704) in "Hpc".

    (* ---- 0x706  c.ldsp s7,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt L5 Pinit Mx n5 sp0 (mword_of_int 0x706)
              (mword_of_int 3 : mword 6) (mword_of_int 23 : mword 5) 96 24
              (m !!! Regidx (mword_of_int 23 : mword 5))
              (ui_init_706 pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 24) _ Hf24))
              with "Hcg Hpc").
    iIntros (L6) "Hcg Hpc".
    set (n6 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 23 : mword 5))]> n5).
    assert (Hsp_n6 : n6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n5 (Regidx (mword_of_int 23 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n5).
    assert (E706 : add_vec_int (mword_of_int 0x706 : mword 64) 2
                   = mword_of_int 0x708)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E706) in "Hpc".

    (* ---- 0x708  c.ldsp s8,16(sp) ---- *)
    iApply (wp_uv_frame_load C pt L6 Pinit Mx n6 sp0 (mword_of_int 0x708)
              (mword_of_int 2 : mword 6) (mword_of_int 24 : mword 5) 96 16
              (m !!! Regidx (mword_of_int 24 : mword 5))
              (ui_init_708 pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n6
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 16) _ Hf16))
              with "Hcg Hpc").
    iIntros (L7) "Hcg Hpc".
    set (n7 := <[Regidx (mword_of_int 24 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 24 : mword 5))]> n6).
    assert (Hsp_n7 : n7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n6 (Regidx (mword_of_int 24 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n6).
    assert (E708 : add_vec_int (mword_of_int 0x708 : mword 64) 2
                   = mword_of_int 0x70a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E708) in "Hpc".

    (* ---- 0x70a  c.ldsp ra,88(sp) ---- *)
    iApply (wp_uv_frame_load C pt L7 Pinit Mx n7 sp0 (mword_of_int 0x70a)
              (mword_of_int 11 : mword 6) (mword_of_int 1 : mword 5) 96 88
              (m !!! Regidx (mword_of_int 1 : mword 5))
              (ui_init_70a pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n7
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 88) _ Hf88))
              with "Hcg Hpc").
    iIntros (L8) "Hcg Hpc".
    set (n8 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> n7).
    assert (Hsp_n8 : n8 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n7).
    assert (E70a : add_vec_int (mword_of_int 0x70a : mword 64) 2
                   = mword_of_int 0x70c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E70a) in "Hpc".

    (* ---- 0x70c  c.ldsp s0,80(sp) ---- *)
    iApply (wp_uv_frame_load C pt L8 Pinit Mx n8 sp0 (mword_of_int 0x70c)
              (mword_of_int 10 : mword 6) (mword_of_int 8 : mword 5) 96 80
              (m !!! Regidx (mword_of_int 8 : mword 5))
              (ui_init_70c pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 80) _ Hf80))
              with "Hcg Hpc").
    iIntros (L9) "Hcg Hpc".
    set (n9 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> n8).
    assert (Hsp_n9 : n9 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n8).
    assert (E70c : add_vec_int (mword_of_int 0x70c : mword 64) 2
                   = mword_of_int 0x70e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E70c) in "Hpc".

    (* ---- 0x70e  c.ldsp s1,72(sp) ---- *)
    iApply (wp_uv_frame_load C pt L9 Pinit Mx n9 sp0 (mword_of_int 0x70e)
              (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 5) 96 72
              (m !!! Regidx (mword_of_int 9 : mword 5))
              (ui_init_70e pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hst96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp_n9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Mx (uint sp0 - 96 + 72) _ Hf72))
              with "Hcg Hpc").
    iIntros (L10) "Hcg Hpc".
    set (n10 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> n9).
    assert (Hsp_n10 : n10 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hsp_n9).
    assert (E70e : add_vec_int (mword_of_int 0x70e : mword 64) 2
                   = mword_of_int 0x710)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E70e) in "Hpc".

    (* ---- 0x710  c.addi16sp sp,sp,96 ---- *)
    assert (Hw710 : (mword_of_int (uint sp0) : mword 64)
                    = add_vec (n10 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))
                      : mword 64) = mword_of_int 96)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp_n10. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Pinit Mx n10 (mword_of_int 0x710)
              (mword_of_int 6 : mword 6) (mword_of_int (uint sp0))
              (ui_init_710 pt Mx (ilay_text pt Hlay) Htext) Hw710
              with "Hcg Hpc").
    iIntros (LA) "Hcg Hpc".
    set (n11 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> n10).
    assert (E710 : add_vec_int (mword_of_int 0x710 : mword 64) 2
                   = mword_of_int 0x712)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E710) in "Hpc".

    (* ---- 0x712  c.jr ra ---- *)
    assert (Hra11 : n11 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { refine (eq_trans (upd_ne n10 (Regidx csp_rs1) (Regidx ra_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5))
                          (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5))
                          (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) _).
      exact (upd_eq n7 (Regidx ra_idx) (regval_into_reg (m !!! Regidx ra_idx))). }
    iApply (wp_uv_cjr C pt Pinit Mx n11 (mword_of_int 0x712)
              ra_idx (m !!! Regidx ra_idx)
              (ui_init_712 pt Mx (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra11; unfold ret_pc; symmetry;
                    exact (update_bit0_zero_of_aligned2 _ Hret2))
              with "Hcg Hpc").
    iIntros (LB) "Hcg Hpc".
    iApply ("Hcont" $! LB n11 with "[] Hcg Hpc").
    iPureIntro.
      intros r Hr.
      assert (Hne : forall k : Z,
                ucallee_saved_idx (mword_of_int k : mword 5) = false ->
                Regidx r <> Regidx (mword_of_int k : mword 5)).
      { intros k Hk Heq. injection Heq as Heq'.
        rewrite Heq' in Hr. rewrite Hk in Hr. discriminate. }
      destruct (decide (r = (mword_of_int 2 : mword 5))) as [ -> | Hd2 ].
      { transitivity (mword_of_int (uint sp0) : mword 64).
        - exact (upd_eq n10 (Regidx csp_rs1)
                   (regval_into_reg (mword_of_int (uint sp0) : mword 64))).
        - rewrite <- Hspm. exact (moi_of_uint _). }
      destruct (decide (r = (mword_of_int 9 : mword 5))) as [ -> | Hd9 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n9 (Regidx (mword_of_int 9 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5)))). }
      destruct (decide (r = (mword_of_int 8 : mword 5))) as [ -> | Hd8 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 8 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 8 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n8 (Regidx (mword_of_int 8 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5)))). }
      destruct (decide (r = (mword_of_int 24 : mword 5))) as [ -> | Hd24 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 24 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 24 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 24 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 24 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n6 (Regidx (mword_of_int 24 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 24 : mword 5)))). }
      destruct (decide (r = (mword_of_int 23 : mword 5))) as [ -> | Hd23 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n6 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n5 (Regidx (mword_of_int 23 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 23 : mword 5)))). }
      destruct (decide (r = (mword_of_int 22 : mword 5))) as [ -> | Hd22 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n6 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n4 (Regidx (mword_of_int 22 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 22 : mword 5)))). }
      destruct (decide (r = (mword_of_int 21 : mword 5))) as [ -> | Hd21 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n6 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n4 (Regidx (mword_of_int 22 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n3 (Regidx (mword_of_int 21 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 21 : mword 5)))). }
      destruct (decide (r = (mword_of_int 20 : mword 5))) as [ -> | Hd20 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n6 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n4 (Regidx (mword_of_int 22 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n3 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n2 (Regidx (mword_of_int 20 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 20 : mword 5)))). }
      destruct (decide (r = (mword_of_int 19 : mword 5))) as [ -> | Hd19 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n6 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n4 (Regidx (mword_of_int 22 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n3 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n2 (Regidx (mword_of_int 20 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq n1 (Regidx (mword_of_int 19 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5)))). }
      destruct (decide (r = (mword_of_int 18 : mword 5))) as [ -> | Hd18 ].
      { refine (eq_trans (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n6 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n4 (Regidx (mword_of_int 22 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n3 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n2 (Regidx (mword_of_int 20 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne n1 (Regidx (mword_of_int 19 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq mx (Regidx (mword_of_int 18 : mword 5)) (regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5)))). }
      rewrite (upd_ne n10 (Regidx (mword_of_int 2 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd2; injection He; auto)).
      rewrite (upd_ne n9 (Regidx (mword_of_int 9 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd9; injection He; auto)).
      rewrite (upd_ne n8 (Regidx (mword_of_int 8 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd8; injection He; auto)).
      rewrite (upd_ne n7 (Regidx (mword_of_int 1 : mword 5)) (Regidx r) _ (Hne 1 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne n6 (Regidx (mword_of_int 24 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd24; injection He; auto)).
      rewrite (upd_ne n5 (Regidx (mword_of_int 23 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd23; injection He; auto)).
      rewrite (upd_ne n4 (Regidx (mword_of_int 22 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd22; injection He; auto)).
      rewrite (upd_ne n3 (Regidx (mword_of_int 21 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd21; injection He; auto)).
      rewrite (upd_ne n2 (Regidx (mword_of_int 20 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd20; injection He; auto)).
      rewrite (upd_ne n1 (Regidx (mword_of_int 19 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd19; injection He; auto)).
      rewrite (upd_ne mx (Regidx (mword_of_int 18 : mword 5)) (Regidx r) _ ltac:(intro He; apply Hd18; injection He; auto)).
      assert (Hn2 : Regidx r <> Regidx (mword_of_int 2 : mword 5))
        by (intro He; apply Hd2; injection He; auto).
      assert (Hn8 : Regidx r <> Regidx (mword_of_int 8 : mword 5))
        by (intro He; apply Hd8; injection He; auto).
      assert (Hn9 : Regidx r <> Regidx (mword_of_int 9 : mword 5))
        by (intro He; apply Hd9; injection He; auto).
      assert (Hn18 : Regidx r <> Regidx (mword_of_int 18 : mword 5))
        by (intro He; apply Hd18; injection He; auto).
      assert (Hn19 : Regidx r <> Regidx (mword_of_int 19 : mword 5))
        by (intro He; apply Hd19; injection He; auto).
      assert (Hn20 : Regidx r <> Regidx (mword_of_int 20 : mword 5))
        by (intro He; apply Hd20; injection He; auto).
      assert (Hn21 : Regidx r <> Regidx (mword_of_int 21 : mword 5))
        by (intro He; apply Hd21; injection He; auto).
      assert (Hn22 : Regidx r <> Regidx (mword_of_int 22 : mword 5))
        by (intro He; apply Hd22; injection He; auto).
      assert (Hn23 : Regidx r <> Regidx (mword_of_int 23 : mword 5))
        by (intro He; apply Hd23; injection He; auto).
      assert (Hn24 : Regidx r <> Regidx (mword_of_int 24 : mword 5))
        by (intro He; apply Hd24; injection He; auto).
      exact (Hcs r Hr Hn2 Hn8 Hn9 Hn18 Hn19 Hn20 Hn21 Hn22 Hn23 Hn24).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2b THE FORMAT LOOP at 0x52c.  One turn per byte of [bs].            *)
  (*                                                                      *)
  (*   52c sext.w a5,s1     530 bnez s3,..  (state is always 0)           *)
  (*   534 bne a5,s5,50c    (the byte is never '%', so ALWAYS taken)      *)
  (*   50c mv a1,s1  50e mv a0,s6  510 jal putc  514 j 51a                *)
  (*   51a addiw a5,s2,1  51e mv s2,a5  520 mv a4,a5  522 add a5,a5,s4    *)
  (*   524 lbu s1,0(a5)   528 beqz s1,6fc  (taken exactly at the NUL)     *)
  (*                                                                      *)
  (* BOUNDED by [length bs], so plain Rocq induction on a STRICT nat       *)
  (* measure -- no [iLoeb], no [|>] (user-echo.md's rule).                 *)
  (* ------------------------------------------------------------------- *)
  Lemma init_vprintf_loop (k : nat) (sp0 : mword 64) (Mp : gmap Z (bv 8))
      (m : regfile) (s : Z) (bs : list (bv 8)) :
    init_layout pt ->
    init_img_sub Mp ->
    uv_stack pt Mp sp0 128 ->
    init_lit Mp s bs ->
    8192 <= uint sp0 - 128 ->
    m !!! Regidx sp_idx = sp0 ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    vp_frame Mp m sp0 ->
    forall (CIDp : CpuId) (i : nat) (b : bv 8)
           (Mi : gmap Z (bv 8)) (mi : regfile),
      (length bs - i < k)%nat ->
      (i < length bs)%nat ->
      bs !! i = Some b ->
      uM_only Mp Mi (uint sp0 - 128) 32 ->
      mi !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64) ->
      mi !!! Regidx (mword_of_int 9 : mword 5)
        = (mword_of_int (bv_unsigned b) : mword 64) ->
      mi !!! Regidx (mword_of_int 18 : mword 5)
        = (mword_of_int (Z.of_nat i) : mword 64) ->
      mi !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 0 : mword 64) ->
      mi !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int s : mword 64) ->
      mi !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 37 : mword 64) ->
      mi !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx a0_idx ->
      vp_rest mi m ->
      uv_cap_gpr (CID := CIDp) C pt Pinit Mi mi -∗
      init_wobs W (uint (m !!! Regidx a0_idx)) bs -∗
      pc_is (CID := CIDp) (mword_of_int 0x52c) -∗
      (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
         ⌜ucallee_saved m m'⌝ -∗
         ⌜uM_only Mp M' (uint sp0 - 128) 32⌝ -∗
         uv_cap_gpr (CID := CID) C pt Pinit M' m' -∗
         pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Himgp Hstp Hlitp Hfr Hspm Hret2 Hvfp.
    pose proof (us_lo _ _ _ _ Hstp) as Hlo.
    pose proof (us_canon _ _ _ _ Hstp) as Hhi.
    change (2 ^ 38) with 274877906944 in Hhi.
    pose proof (il_lo _ _ _ Hlitp) as Hslo.
    pose proof (il_hi _ _ _ Hlitp) as Hshi.
    induction k as [ | k' IH ];
      intros CIDp i b Mi mi Hk Hi Hbi Honly Hspi Hs1i Hs2i Hs3i Hs4i Hs5i Hs6i Hcs.
    { exfalso. lia. }
    (* ---- the byte's own facts ---- *)
    pose proof (il_nz _ _ _ Hlitp i b Hbi) as Hbnz.
    pose proof (il_nopc _ _ _ Hlitp i b Hbi) as Hbpc.
    pose proof (bv_unsigned_in_range _ b) as Hbr.
    assert (E8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite E8 in Hbr.
    assert (Hbu0 : bv_unsigned b <> 0).
    { intro Hz. apply Hbnz. apply bv_eq. rewrite Hz. vm_compute. reflexivity. }
    assert (Hbu37 : bv_unsigned b <> 37).
    { intro Hz. apply Hbpc. apply bv_eq. rewrite Hz. vm_compute. reflexivity. }
    (* ---- the image at [Mi] ---- *)
    assert (Himgi : init_img_sub Mi)
      by exact (init_img_only Mp Mi (uint sp0 - 128) 32 ltac:(lia) Honly Himgp).
    assert (Hsti : uv_stack pt Mi sp0 128)
      by exact (uM_only_stack pt Mp Mi sp0 128 (uint sp0 - 128) 32 Honly Hstp).
    assert (Hliti : init_lit Mi s bs)
      by exact (init_lit_only Mp Mi (uint sp0 - 128) 32 s bs ltac:(lia) Honly Hlitp).
    destruct (uv_stack_split pt Mi sp0 128 96 32 eq_refl ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hsti) as (Hs96i & Hs32i).
    assert (Espb : add_vec_int sp0 (- 96) = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (uv_stack_sp_moi pt Mi sp0 96 Hs96i).
    rewrite Espb in Hs32i.
    assert (Husp : uint (mword_of_int (uint sp0 - 96) : mword 64) = uint sp0 - 96)
      by (apply uint_moi; unfold Z64; lia).
    iIntros "Hcg #Hwobs Hpc Hcont".

    (* ---- 0x52c  sext.w a5,s1  (addiw a5,s1,0) ---- *)
    assert (Hw52c : (mword_of_int (bv_unsigned b) : mword 64)
                    = sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (mi !!! Regidx (mword_of_int 9 : mword 5))
                              (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)).
    { rewrite Hs1i.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc.
      rewrite (moi_addw (bv_unsigned b) 0 ltac:(unfold Z31; lia)).
      f_equal. lia. }
    iApply (wp_uv_addiw C pt Pinit Mi mi (mword_of_int 0x52c)
              (mword_of_int 0 : mword 12) (mword_of_int 9 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int (bv_unsigned b))
              (ui_init_52c pt Mi (ilay_text pt Hlay) (init_img_text Mi Himgi))
              ltac:(vm_compute; discriminate) Hw52c
              with "Hcg Hpc").
    iIntros (J1) "Hcg Hpc".
    set (q1 := <[Regidx (mword_of_int 15 : mword 5)
                 := regval_into_reg (mword_of_int (bv_unsigned b) : mword 64)]> mi).
    assert (E52c : add_vec_int (mword_of_int 0x52c : mword 64) 4
                   = mword_of_int 0x530)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E52c) in "Hpc".
    assert (Hq1a5 : q1 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (bv_unsigned b) : mword 64)).
    { exact (upd_eq mi (Regidx (mword_of_int 15 : mword 5)) (regval_into_reg (mword_of_int (bv_unsigned b) : mword 64))). }
    assert (Hq1s1 : q1 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int (bv_unsigned b) : mword 64)).
    { refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs1i. }
    assert (Hq1s3 : q1 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 0 : mword 64)).
    { refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs3i. }
    assert (Hq1s5 : q1 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 37 : mword 64)).
    { refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs5i. }
    assert (Hq1s6 : q1 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx a0_idx).
    { refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs6i. }

    (* ---- 0x530  bnez s3,516   (state is 0: NOT taken) ---- *)
    assert (Ht530 : false = uv_btaken BNE
                              (q1 !!! Regidx (mword_of_int 19 : mword 5)) zero_reg).
    { cbn [uv_btaken]. rewrite Hq1s3. rewrite zero_reg_moi.
      rewrite (moi_neq_vec 0 0 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      reflexivity. }
    iApply (wp_uv_btype0 C pt Pinit Mi q1 (mword_of_int 0x530)
              (mword_of_int 8166 : mword 13) (mword_of_int 19 : mword 5) BNE
              false (mword_of_int 0x516)
              (ui_init_530 pt Mi (ilay_text pt Hlay) (init_img_text Mi Himgi))
              Ht530 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hx; discriminate)
              with "Hcg Hpc").
    iIntros (J2) "Hcg Hpc".
    assert (E530 : add_vec_int (mword_of_int 0x530 : mword 64) 4
                   = mword_of_int 0x534)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E530) in "Hpc".

    (* ---- 0x534  bne a5,s5,50c   (the byte is never '%': ALWAYS taken) ---- *)
    assert (Ht534 : true = uv_btaken BNE
                             (q1 !!! Regidx (mword_of_int 15 : mword 5))
                             (q1 !!! Regidx (mword_of_int 21 : mword 5))).
    { cbn [uv_btaken]. rewrite Hq1a5. rewrite Hq1s5.
      rewrite (moi_neq_vec (bv_unsigned b) 37 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hbu37. }
    iApply (wp_uv_btype C pt Pinit Mi q1 (mword_of_int 0x534)
              (mword_of_int 8152 : mword 13) (mword_of_int 21 : mword 5)
              (mword_of_int 15 : mword 5) BNE true (mword_of_int 0x50c)
              (ui_init_534 pt Mi (ilay_text pt Hlay) (init_img_text Mi Himgi))
              Ht534 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hx; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (J3) "Hcg Hpc".

    (* ---- 0x50c  mv a1,s1 ---- *)
    iApply (wp_uv_cmv C pt Pinit Mi q1 (mword_of_int 0x50c)
              (mword_of_int 11 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int (bv_unsigned b))
              (ui_init_50c pt Mi (ilay_text pt Hlay) (init_img_text Mi Himgi))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hq1s1; reflexivity)
              with "Hcg Hpc").
    iIntros (J4) "Hcg Hpc".
    set (q2 := <[Regidx (mword_of_int 11 : mword 5)
                 := regval_into_reg (mword_of_int (bv_unsigned b) : mword 64)]> q1).
    assert (E50c : add_vec_int (mword_of_int 0x50c : mword 64) 2
                   = mword_of_int 0x50e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E50c) in "Hpc".

    (* ---- 0x50e  mv a0,s6 ---- *)
    assert (Hq2s6 : q2 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx a0_idx)
      by exact (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5))
                            (Regidx (mword_of_int 22 : mword 5)) _
                            ltac:(vm_compute; discriminate)) Hq1s6).
    iApply (wp_uv_cmv C pt Pinit Mi q2 (mword_of_int 0x50e)
              (mword_of_int 10 : mword 5) (mword_of_int 22 : mword 5)
              (m !!! Regidx a0_idx)
              (ui_init_50e pt Mi (ilay_text pt Hlay) (init_img_text Mi Himgi))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hq2s6; reflexivity)
              with "Hcg Hpc").
    iIntros (J5) "Hcg Hpc".
    set (q3 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (m !!! Regidx a0_idx)]> q2).
    assert (E50e : add_vec_int (mword_of_int 0x50e : mword 64) 2
                   = mword_of_int 0x510)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E50e) in "Hpc".

    (* ---- 0x510  jal putc ---- *)
    iApply (wp_uv_jal C pt Pinit Mi q3 (mword_of_int 0x510)
              (mword_of_int 2096906 : mword 21) ra_idx
              (mword_of_int 0x41a) (mword_of_int 0x514)
              (ui_init_510 pt Mi (ilay_text pt Hlay) (init_img_text Mi Himgi))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (J6) "Hcg Hpc".
    set (q4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x514 : mword 64)]> q3).
    iEval (change (mword_of_int 0x41a : mword 64)
             with (mword_of_int InitSyms.putc : mword 64)) in "Hpc".
    assert (Hq4a1 : q4 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int (bv_unsigned b) : mword 64)).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 11 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 11 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_eq q1 (Regidx (mword_of_int 11 : mword 5)) (regval_into_reg (mword_of_int (bv_unsigned b) : mword 64))). }
    assert (Hq4a0 : q4 !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx a0_idx).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 10 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_eq q2 (Regidx (mword_of_int 10 : mword 5)) (regval_into_reg (m !!! Regidx a0_idx))). }
    assert (Hq4ra : q4 !!! Regidx (mword_of_int 1 : mword 5) = (mword_of_int 0x514 : mword 64)).
    { exact (upd_eq q3 (Regidx (mword_of_int 1 : mword 5)) (regval_into_reg (mword_of_int 0x514 : mword 64))). }
    assert (Hq4sp : q4 !!! Regidx (mword_of_int 2 : mword 5) = (mword_of_int (uint sp0 - 96) : mword 64)).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hspi. }
    assert (Hq4s1 : q4 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int (bv_unsigned b) : mword 64)).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs1i. }
    assert (Hq4s2 : q4 !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (Z.of_nat i) : mword 64)).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs2i. }
    assert (Hq4s3 : q4 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 0 : mword 64)).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs3i. }
    assert (Hq4s4 : q4 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int s : mword 64)).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs4i. }
    assert (Hq4s5 : q4 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 37 : mword 64)).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs5i. }
    assert (Hq4s6 : q4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx a0_idx).
    { refine (eq_trans (upd_ne q3 (Regidx (mword_of_int 1 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact Hs6i. }

    (* ---- putc(fd, byte) ---- *)
    assert (Hbin : b ∈ bs) by (apply elem_of_list_lookup; exists i; exact Hbi).
    iDestruct ("Hwobs" $! b with "[]") as "Hw"; [ iPureIntro; exact Hbin | ].
    iApply (wp_init_putc C pt Q W J6 Mi q4 (mword_of_int (uint sp0 - 96)) b
              Hlay (init_img_text Mi Himgi) Hq4sp Hs32i
              ltac:(unfold init_frame_ok; rewrite Husp; lia)
              ltac:(rewrite Hq4a1; exact (nth_byte_moi8 b))
              ltac:(rewrite Hq4ra; vm_compute; reflexivity)
              with "Hcg [Hw] Hpc [Hcont]").
    { rewrite Hq4a0. iExact "Hw". }
    iIntros (J7 mo Mo) "%Hcso %Hoo Hcg Hpc".
    rewrite Husp in Hoo.
    iEval (rewrite Hq4ra) in "Hpc".
    (* the image after putc *)
    assert (Hoacc : uM_only Mp Mo (uint sp0 - 128) 32)
      by exact (uM_only_trans Mp Mi Mo (uint sp0 - 128) 32 Honly
                  ltac:(replace (uint sp0 - 96 - 32) with (uint sp0 - 128) in Hoo
                          by lia; exact Hoo)).
    assert (Himgo : init_img_sub Mo)
      by exact (init_img_only Mp Mo (uint sp0 - 128) 32 ltac:(lia) Hoacc Himgp).
    assert (Hsto : uv_stack pt Mo sp0 128)
      by exact (uM_only_stack pt Mp Mo sp0 128 (uint sp0 - 128) 32 Hoacc Hstp).
    assert (Hlito : init_lit Mo s bs)
      by exact (init_lit_only Mp Mo (uint sp0 - 128) 32 s bs ltac:(lia) Hoacc Hlitp).
    (* the registers putc preserved *)
    assert (Hosp : mo !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (Hcso (mword_of_int 2 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hq4sp).
    assert (Hos1 : mo !!! Regidx (mword_of_int 9 : mword 5)
                   = (mword_of_int (bv_unsigned b) : mword 64))
      by exact (eq_trans (Hcso (mword_of_int 9 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hq4s1).
    assert (Hos2 : mo !!! Regidx (mword_of_int 18 : mword 5)
                   = (mword_of_int (Z.of_nat i) : mword 64))
      by exact (eq_trans (Hcso (mword_of_int 18 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hq4s2).
    assert (Hos3 : mo !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 0 : mword 64))
      by exact (eq_trans (Hcso (mword_of_int 19 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hq4s3).
    assert (Hos4 : mo !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int s : mword 64))
      by exact (eq_trans (Hcso (mword_of_int 20 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hq4s4).
    assert (Hos5 : mo !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 37 : mword 64))
      by exact (eq_trans (Hcso (mword_of_int 21 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hq4s5).
    assert (Hos6 : mo !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx a0_idx)
      by exact (eq_trans (Hcso (mword_of_int 22 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hq4s6).
    (* ... and the rest of the callee-saved set, still equal to the entry file *)
    assert (Hcso2 : vp_rest mo m).
    { intros r Hr Hg2 Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24.
      assert (Hne : forall kz : Z,
                ucallee_saved_idx (mword_of_int kz : mword 5) = false ->
                Regidx r <> Regidx (mword_of_int kz : mword 5)).
      { intros kz Hkz Heq. injection Heq as Heq'.
        rewrite Heq' in Hr. rewrite Hkz in Hr. discriminate. }
      rewrite (Hcso r Hr).
      rewrite (upd_ne q3 (Regidx ra_idx) (Regidx r) _
                 (Hne 1 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne q2 (Regidx (mword_of_int 10 : mword 5)) (Regidx r) _
                 (Hne 10 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne q1 (Regidx (mword_of_int 11 : mword 5)) (Regidx r) _
                 (Hne 11 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne mi (Regidx (mword_of_int 15 : mword 5)) (Regidx r) _
                 (Hne 15 ltac:(vm_compute; reflexivity))).
      exact (Hcs r Hr Hg2 Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24). }

    (* ---- 0x514  j 51a ---- *)
    iApply (wp_uv_cj C pt Pinit Mo mo (mword_of_int 0x514)
              (mword_of_int 3 : mword 11) (mword_of_int 0x51a)
              (ui_init_514 pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (J8) "Hcg Hpc".

    (* ---- 0x51a  addiw a5,s2,1 ---- *)
    assert (Hilen : (i < length bs)%nat) by exact Hi.
    assert (Hi31 : 0 <= Z.of_nat i + 1 < Z31).
    { pose proof (il_hi _ _ _ Hlitp). unfold Z31. lia. }
    assert (Hw51a : (mword_of_int (Z.of_nat i + 1) : mword 64)
                    = sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (mo !!! Regidx (mword_of_int 18 : mword 5))
                              (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)).
    { rewrite Hos2.
      assert (Hc : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                   = mword_of_int 1) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. rewrite (moi_addw (Z.of_nat i) 1 Hi31). reflexivity. }
    iApply (wp_uv_addiw C pt Pinit Mo mo (mword_of_int 0x51a)
              (mword_of_int 1 : mword 12) (mword_of_int 18 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int (Z.of_nat i + 1))
              (ui_init_51a pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
              ltac:(vm_compute; discriminate) Hw51a
              with "Hcg Hpc").
    iIntros (J9) "Hcg Hpc".
    set (q5 := <[Regidx (mword_of_int 15 : mword 5)
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64)]> mo).
    assert (E51a : add_vec_int (mword_of_int 0x51a : mword 64) 4
                   = mword_of_int 0x51e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E51a) in "Hpc".

    (* ---- 0x51e  mv s2,a5 ---- *)
    assert (Hq5a5 : q5 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int (Z.of_nat i + 1) : mword 64))
      by exact (upd_eq mo (Regidx (mword_of_int 15 : mword 5)) _).
    iApply (wp_uv_cmv C pt Pinit Mo q5 (mword_of_int 0x51e)
              (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int (Z.of_nat i + 1))
              (ui_init_51e pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hq5a5; reflexivity)
              with "Hcg Hpc").
    iIntros (JA) "Hcg Hpc".
    set (q6 := <[Regidx (mword_of_int 18 : mword 5)
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64)]> q5).
    assert (E51e : add_vec_int (mword_of_int 0x51e : mword 64) 2
                   = mword_of_int 0x520)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E51e) in "Hpc".

    (* ---- 0x520  mv a4,a5 ---- *)
    assert (Hq6a5 : q6 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int (Z.of_nat i + 1) : mword 64))
      by exact (eq_trans (upd_ne q5 (Regidx (mword_of_int 18 : mword 5))
                            (Regidx (mword_of_int 15 : mword 5)) _
                            ltac:(vm_compute; discriminate)) Hq5a5).
    iApply (wp_uv_cmv C pt Pinit Mo q6 (mword_of_int 0x520)
              (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int (Z.of_nat i + 1))
              (ui_init_520 pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hq6a5; reflexivity)
              with "Hcg Hpc").
    iIntros (JB) "Hcg Hpc".
    set (q7 := <[Regidx (mword_of_int 14 : mword 5)
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64)]> q6).
    assert (E520 : add_vec_int (mword_of_int 0x520 : mword 64) 2
                   = mword_of_int 0x522)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E520) in "Hpc".

    (* ---- 0x522  add a5,a5,s4 ---- *)
    assert (Hq7a5 : q7 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int (Z.of_nat i + 1) : mword 64))
      by exact (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5))
                            (Regidx (mword_of_int 15 : mword 5)) _
                            ltac:(vm_compute; discriminate)) Hq6a5).
    assert (Hq7s4 : q7 !!! Regidx (mword_of_int 20 : mword 5)
                    = (mword_of_int s : mword 64)).
    { refine (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5))
                          (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q5 (Regidx (mword_of_int 18 : mword 5))
                          (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mo (Regidx (mword_of_int 15 : mword 5))
                          (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hos4. }
    iApply (wp_uv_cadd C pt Pinit Mo q7 (mword_of_int 0x522)
              (mword_of_int 15 : mword 5) (mword_of_int 20 : mword 5)
              (mword_of_int (Z.of_nat i + 1 + s))
              (ui_init_522 pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hq7a5; rewrite Hq7s4; rewrite moi_add; reflexivity)
              with "Hcg Hpc").
    iIntros (JC) "Hcg Hpc".
    set (q8 := <[Regidx (mword_of_int 15 : mword 5)
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1 + s) : mword 64)]> q7).
    assert (E522 : add_vec_int (mword_of_int 0x522 : mword 64) 2
                   = mword_of_int 0x524)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E522) in "Hpc".

    (* ---- 0x524  lbu s1,0(a5)   -- the NEXT byte ---- *)
    assert (Hq8a5 : q8 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int (Z.of_nat i + 1 + s) : mword 64))
      by exact (upd_eq q7 (Regidx (mword_of_int 15 : mword 5)) _).
    (* the byte at [s + i + 1]: either the next character or the NUL *)
    destruct (il_at _ _ _ Hlito) as (Hatb & Hatn).
    assert (Hnb : exists bn : bv 8,
              Mo !! (s + Z.of_nat i + 1) = Some bn /\
              (forall x : bv 8, bs !! (S i) = Some x -> bn = x) /\
              (bs !! (S i) = None -> bn = ubyte0)).
    { destruct (bs !! (S i)) as [ x | ] eqn:Hx.
      - exists x. split_and!.
        + replace (s + Z.of_nat i + 1) with (s + Z.of_nat (S i)) by lia.
          exact (Hatb (S i) x Hx).
        + intros y Hy. injection Hy as Hy'. exact Hy'.
        + intro Hc. discriminate.
      - assert (Hlen : length bs = S i).
        { pose proof (lookup_ge_None_1 bs (S i) Hx). lia. }
        exists ubyte0. split_and!.
        + replace (s + Z.of_nat i + 1) with (s + Z.of_nat (length bs)) by lia.
          exact Hatn.
        + intros y Hy. discriminate.
        + intro Hc. reflexivity. }
    destruct Hnb as (bn & Hbn & Hbnsome & Hbnnone).
    assert (Hva524 : (mword_of_int (Z.of_nat i + 1 + s) : mword 64)
                     = add_vec (q8 !!! Regidx (mword_of_int 15 : mword 5))
                         (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hq8a5.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. rewrite moi_add. f_equal. lia. }
    assert (Hbnlen : Z.of_nat i + 1 <= Z.of_nat (length bs)) by lia.
    assert (Hua : uint (mword_of_int (Z.of_nat i + 1 + s) : mword 64)
                  = s + Z.of_nat i + 1).
    { rewrite (uint_moi (Z.of_nat i + 1 + s) ltac:(unfold Z64; lia)). lia. }
    destruct (init_text_layout_load pt (Z.of_nat i + 1 + s) (ilay_text pt Hlay)
                ltac:(lia)) as (wld & Hwld & Hwok).
    iApply (wp_uv_lbu C pt Pinit Mo q8 (mword_of_int 0x524)
              (mword_of_int 0 : mword 12) (mword_of_int 15 : mword 5)
              (mword_of_int 9 : mword 5) wld
              (mword_of_int (Z.of_nat i + 1 + s)) (zero_extend' 64 (bn : mword 8)) (bn : mword 8)
              (ui_init_524 pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
              ltac:(vm_compute; discriminate) Hva524 Hwld Hwok
              ltac:(apply uva_canon_small; rewrite <- uint_unsigned; rewrite Hua; lia)
              ltac:(rewrite Hua; exact Hbn) eq_refl
              with "Hcg Hpc").
    iIntros (JD) "Hcg Hpc".
    set (q9 := <[Regidx (mword_of_int 9 : mword 5)
                 := regval_into_reg (zero_extend' 64 (bn : mword 8) : mword 64)]> q8).
    assert (E524 : add_vec_int (mword_of_int 0x524 : mword 64) 4
                   = mword_of_int 0x528)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E524) in "Hpc".
    assert (Hq9s1 : q9 !!! Regidx (mword_of_int 9 : mword 5)
                    = (mword_of_int (bv_unsigned bn) : mword 64)).
    { rewrite (upd_eq q8 (Regidx (mword_of_int 9 : mword 5))
                 (regval_into_reg (zero_extend' 64 (bn : mword 8) : mword 64))).
      exact (zext8_moi bn). }
    pose proof (bv_unsigned_in_range _ bn) as Hbnr. rewrite E8 in Hbnr.
    assert (Hq9sp : q9 !!! Regidx (mword_of_int 2 : mword 5) = (mword_of_int (uint sp0 - 96) : mword 64)).
    { refine (eq_trans (upd_ne q8 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q7 (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q5 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mo (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hosp. }
    assert (Hq9s2 : q9 !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (Z.of_nat (S i)) : mword 64)).
    { refine (eq_trans (upd_ne q8 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q7 (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      rewrite (upd_eq q5 (Regidx (mword_of_int 18 : mword 5))
                 (regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64))).
      replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia. reflexivity. }
    assert (Hq9s3 : q9 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 0 : mword 64)).
    { refine (eq_trans (upd_ne q8 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q7 (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q5 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mo (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hos3. }
    assert (Hq9s4 : q9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int s : mword 64)).
    { refine (eq_trans (upd_ne q8 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q7 (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q5 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mo (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hos4. }
    assert (Hq9s5 : q9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 37 : mword 64)).
    { refine (eq_trans (upd_ne q8 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q7 (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q5 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mo (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hos5. }
    assert (Hq9s6 : q9 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx a0_idx).
    { refine (eq_trans (upd_ne q8 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q7 (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q6 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne q5 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne mo (Regidx (mword_of_int 15 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hos6. }
    assert (Hq9cs : vp_rest q9 m).
    { intros r Hr Hg2 Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24.
      assert (Hne : forall kz : Z,
                ucallee_saved_idx (mword_of_int kz : mword 5) = false ->
                Regidx r <> Regidx (mword_of_int kz : mword 5)).
      { intros kz Hkz Heq. injection Heq as Heq'.
        rewrite Heq' in Hr. rewrite Hkz in Hr. discriminate. }
      rewrite (upd_ne q8 (Regidx (mword_of_int 9 : mword 5)) (Regidx r) _ Hg9).
      rewrite (upd_ne q7 (Regidx (mword_of_int 15 : mword 5)) (Regidx r) _
                 (Hne 15 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne q6 (Regidx (mword_of_int 14 : mword 5)) (Regidx r) _
                 (Hne 14 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne q5 (Regidx (mword_of_int 18 : mword 5)) (Regidx r) _ Hg18).
      rewrite (upd_ne mo (Regidx (mword_of_int 15 : mword 5)) (Regidx r) _
                 (Hne 15 ltac:(vm_compute; reflexivity))).
      exact (Hcso2 r Hr Hg2 Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24). }

    (* ---- 0x528  beqz s1,6fc  -- taken exactly at the NUL ---- *)
    destruct (decide (S i < length bs)%nat) as [ Hnext | Hend ].
    - (* another character: NOT taken; back to 0x52c through the IH *)
      destruct (lookup_lt_is_Some_2 bs (S i) Hnext) as (bx & Hbx).
      assert (Hbneq : bn = bx) by exact (Hbnsome bx Hbx).
      assert (Hbxnz : bx <> ubyte0) by exact (il_nz _ _ _ Hlitp (S i) bx Hbx).
      assert (Hbnu0 : bv_unsigned bn <> 0).
      { rewrite Hbneq. intro Hz. apply Hbxnz. apply bv_eq. rewrite Hz.
        vm_compute. reflexivity. }
      assert (Ht528 : false = uv_btaken BEQ
                                (q9 !!! Regidx (mword_of_int 9 : mword 5)) zero_reg).
      { cbn [uv_btaken]. rewrite Hq9s1. rewrite zero_reg_moi.
        rewrite (moi_eq_vec (bv_unsigned bn) 0 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact Hbnu0. }
      iApply (wp_uv_btype0 C pt Pinit Mo q9 (mword_of_int 0x528)
                (mword_of_int 468 : mword 13) (mword_of_int 9 : mword 5) BEQ
                false (mword_of_int 0x6fc)
                (ui_init_528 pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
                Ht528 ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hx; discriminate)
                with "Hcg Hpc").
      iIntros (JE) "Hcg Hpc".
      assert (E528 : add_vec_int (mword_of_int 0x528 : mword 64) 4
                     = mword_of_int 0x52c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E528) in "Hpc".
      iApply (IH JE (S i) bn Mo q9 ltac:(lia) Hnext
                ltac:(rewrite Hbneq; exact Hbx) Hoacc
                Hq9sp Hq9s1 Hq9s2 Hq9s3 Hq9s4 Hq9s5 Hq9s6 Hq9cs
                with "Hcg Hwobs Hpc Hcont").

    - (* the NUL: TAKEN, to the epilogue *)
      assert (Hlen : length bs = S i).
      { pose proof (lookup_lt_Some bs i b Hbi). lia. }
      assert (Hbnn : bs !! (S i) = None)
        by (apply lookup_ge_None_2; lia).
      assert (Hbn0 : bn = ubyte0) by exact (Hbnnone Hbnn).
      assert (Ht528 : true = uv_btaken BEQ
                               (q9 !!! Regidx (mword_of_int 9 : mword 5)) zero_reg).
      { cbn [uv_btaken]. rewrite Hq9s1. rewrite zero_reg_moi.
        rewrite (moi_eq_vec (bv_unsigned bn) 0 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_eq. rewrite Hbn0. vm_compute. reflexivity. }
      iApply (wp_uv_btype0 C pt Pinit Mo q9 (mword_of_int 0x528)
                (mword_of_int 468 : mword 13) (mword_of_int 9 : mword 5) BEQ
                true (mword_of_int 0x6fc)
                (ui_init_528 pt Mo (ilay_text pt Hlay) (init_img_text Mo Himgo))
                Ht528 ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hx; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (JE) "Hcg Hpc".
      destruct (uv_stack_split pt Mo sp0 128 96 32 eq_refl ltac:(lia)
                  ltac:(reflexivity) ltac:(lia) Hsto) as (Hs96o & _).
      iApply (init_vprintf_epi JE Mo q9 m sp0
                Hlay (init_img_text Mo Himgo) Hs96o
                (vp_frame_only Mp Mo m sp0 (uint sp0 - 128) 32 Hoacc
                   ltac:(lia) Hvfp)
                Hspm Hret2 Hq9sp Hq9cs
                with "Hcg Hpc [Hcont]").
      iIntros (JF m'') "%Hcs'' Hcg Hpc".
      iApply ("Hcont" $! JF m'' Mo with "[] [] Hcg Hpc").
      + iPureIntro. exact Hcs''.
      + iPureIntro. exact Hoacc.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2c vprintf itself: the prologue, the first [lbu], and the loop.      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_init_vprintf (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s : Z) (bs : list (bv 8)) :
    wp_init_vprintf_body (CID := CIDp) C pt Q W M m sp0 s bs.
  Proof.
    intros Hlay Himg Hsp Hst Hfr Hfmt Hlit Hret2.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hhi.
    unfold init_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhi.
    pose proof (il_lo _ _ _ Hlit) as Hslo.
    pose proof (il_hi _ _ _ Hlit) as Hshi.
    pose proof (il_ne _ _ _ Hlit) as Hbsne.
    assert (Hbslen : (0 < length bs)%nat)
      by (destruct bs; [ exfalso; exact (Hbsne eq_refl) | cbn; lia ]).
    destruct (lookup_lt_is_Some_2 bs 0 Hbslen) as (b0 & Hb0).
    destruct (uv_stack_split pt M sp0 128 96 32 eq_refl ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hs96 & _).
    assert (Hsp' : m !!! Regidx csp_rs1 = (mword_of_int (uint sp0) : mword 64))
      by (rewrite moi_of_uint; exact Hsp).
    iIntros "Hcg #Hwobs Hpc Hcont".
    iEval (change (mword_of_int InitSyms.vprintf : mword 64)
             with (mword_of_int 0x4d6 : mword 64)) in "Hpc".

    (* ---- 0x4d6  c.addi16sp sp,sp,-96 ---- *)
    assert (Hw4d6 : (mword_of_int (uint sp0 - 96) : mword 64)
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))
                      : mword 64) = mword_of_int (-96))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp'. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Pinit M m (mword_of_int 0x4d6)
              (mword_of_int 58 : mword 6) (mword_of_int (uint sp0 - 96))
              (ui_init_4d6 pt M (ilay_text pt Hlay) (init_img_text M Himg)) Hw4d6
              with "Hcg Hpc").
    iIntros (K1) "Hcg Hpc".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 96) : mword 64)]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (mword_of_int (uint sp0 - 96) : mword 64))).
    assert (E4d6 : add_vec_int (mword_of_int 0x4d6 : mword 64) 2
                   = mword_of_int 0x4d8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4d6) in "Hpc".
    assert (Hr1 : m1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 1 : mword 5)) _ ltac:(vm_compute; discriminate)). }
    assert (Hr8 : m1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 8 : mword 5)) _ ltac:(vm_compute; discriminate)). }
    assert (Hr9 : m1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _ ltac:(vm_compute; discriminate)). }

    (* ---- 0x4d8  c.sdsp ra,88(sp) ---- *)
    iApply (wp_uv_frame_store C pt K1 Pinit M m1 sp0 (mword_of_int 0x4d8)
              (mword_of_int 11 : mword 6) (mword_of_int 1 : mword 5) 96 88
              (ui_init_4d8 pt M (ilay_text pt Hlay) (init_img_text M Himg)) Hs96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K2) "Hcg Hpc".
    iEval (rewrite Hr1) in "Hcg".
    set (M1 := uM_store8 M (uint sp0 - 96 + 88) (m !!! Regidx (mword_of_int 1 : mword 5))).
    assert (Ho1 : uM_only M M1 (uint sp0 - 96) 96)
      by (rewrite /M1; apply uM_only_store8; lia).
    assert (Hot1 : uM_only M M1 (uint sp0 - 96 + 88) 8)
      by (rewrite /M1; apply uM_only_store8; lia).
    assert (Hacc1 : uM_only M M1 (uint sp0 - 96) 96) by exact Ho1.
    assert (Ht1 : init_img_sub M1)
      by exact (init_img_only M M1 (uint sp0 - 96) 96 ltac:(lia) Ho1 Himg).
    assert (Hs1 : uv_stack pt M1 sp0 96)
      by exact (uM_only_stack pt M M1 sp0 96 (uint sp0 - 96) 96 Ho1 Hs96).
    assert (E4d8 : add_vec_int (mword_of_int 0x4d8 : mword 64) 2
                   = mword_of_int 0x4da)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4d8) in "Hpc".

    (* ---- 0x4da  c.sdsp s0,80(sp) ---- *)
    iApply (wp_uv_frame_store C pt K2 Pinit M1 m1 sp0 (mword_of_int 0x4da)
              (mword_of_int 10 : mword 6) (mword_of_int 8 : mword 5) 96 80
              (ui_init_4da pt M1 (ilay_text pt Hlay) (init_img_text M1 Ht1)) Hs1
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K3) "Hcg Hpc".
    iEval (rewrite Hr8) in "Hcg".
    set (M2 := uM_store8 M1 (uint sp0 - 96 + 80) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Ho2 : uM_only M1 M2 (uint sp0 - 96) 96)
      by (rewrite /M2; apply uM_only_store8; lia).
    assert (Hot2 : uM_only M1 M2 (uint sp0 - 96 + 80) 8)
      by (rewrite /M2; apply uM_only_store8; lia).
    assert (Hacc2 : uM_only M M2 (uint sp0 - 96) 96) by exact (uM_only_trans M M1 M2 (uint sp0 - 96) 96 Hacc1 Ho2).
    assert (Ht2 : init_img_sub M2)
      by exact (init_img_only M1 M2 (uint sp0 - 96) 96 ltac:(lia) Ho2 Ht1).
    assert (Hs2 : uv_stack pt M2 sp0 96)
      by exact (uM_only_stack pt M1 M2 sp0 96 (uint sp0 - 96) 96 Ho2 Hs1).
    assert (E4da : add_vec_int (mword_of_int 0x4da : mword 64) 2
                   = mword_of_int 0x4dc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4da) in "Hpc".

    (* ---- 0x4dc  c.sdsp s1,72(sp) ---- *)
    iApply (wp_uv_frame_store C pt K3 Pinit M2 m1 sp0 (mword_of_int 0x4dc)
              (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 5) 96 72
              (ui_init_4dc pt M2 (ilay_text pt Hlay) (init_img_text M2 Ht2)) Hs2
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K4) "Hcg Hpc".
    iEval (rewrite Hr9) in "Hcg".
    set (M3 := uM_store8 M2 (uint sp0 - 96 + 72) (m !!! Regidx (mword_of_int 9 : mword 5))).
    assert (Ho3 : uM_only M2 M3 (uint sp0 - 96) 96)
      by (rewrite /M3; apply uM_only_store8; lia).
    assert (Hot3 : uM_only M2 M3 (uint sp0 - 96 + 72) 8)
      by (rewrite /M3; apply uM_only_store8; lia).
    assert (Hacc3 : uM_only M M3 (uint sp0 - 96) 96) by exact (uM_only_trans M M2 M3 (uint sp0 - 96) 96 Hacc2 Ho3).
    assert (Ht3 : init_img_sub M3)
      by exact (init_img_only M2 M3 (uint sp0 - 96) 96 ltac:(lia) Ho3 Ht2).
    assert (Hs3 : uv_stack pt M3 sp0 96)
      by exact (uM_only_stack pt M2 M3 sp0 96 (uint sp0 - 96) 96 Ho3 Hs2).
    assert (E4dc : add_vec_int (mword_of_int 0x4dc : mword 64) 2
                   = mword_of_int 0x4de)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4dc) in "Hpc".

    (* ---- 0x4de  c.addi4spn s0,sp,96 ---- *)
    assert (Hw4de : (mword_of_int (uint sp0) : mword 64)
                    = add_vec (m1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8)))).
    { assert (Hcst : (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                      : mword 64) = mword_of_int 96)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp1. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Pinit M3 m1 (mword_of_int 0x4de)
              (mword_of_int 0 : mword 3) (mword_of_int 24 : mword 8)
              (mword_of_int 8 : mword 5) (mword_of_int (uint sp0))
              (ui_init_4de pt M3 (ilay_text pt Hlay) (init_img_text M3 Ht3))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw4de
              with "Hcg Hpc").
    iIntros (K5) "Hcg Hpc".
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (E4de : add_vec_int (mword_of_int 0x4de : mword 64) 2
                   = mword_of_int 0x4e0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4de) in "Hpc".

    (* ---- 0x4e0  lbu s1,0(a1)  -- the first byte of the format string ---- *)
    assert (Hlit3 : init_lit M3 s bs)
      by exact (init_lit_only M M3 (uint sp0 - 96) 96 s bs ltac:(lia) Hacc3 Hlit).
    destruct (il_at _ _ _ Hlit3) as (Hatb3 & Hatn3).
    assert (Hb0m : M3 !! s = Some b0)
      by (replace s with (s + Z.of_nat 0) by lia; exact (Hatb3 0%nat b0 Hb0)).
    assert (Hm2a1 : m2 !!! Regidx a1_idx = (mword_of_int s : mword 64)).
    { refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5))
                          (Regidx a1_idx) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m (Regidx csp_rs1)
                          (Regidx a1_idx) _ ltac:(vm_compute; discriminate)) _).
      exact Hfmt. }
    assert (Hva4e0 : (mword_of_int s : mword 64)
                     = add_vec (m2 !!! Regidx a1_idx)
                         (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hm2a1.
      assert (Hcst : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                     = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite moi_add. f_equal. lia. }
    assert (Hus : uint (mword_of_int s : mword 64) = s)
      by (apply uint_moi; unfold Z64; lia).
    destruct (init_text_layout_load pt s (ilay_text pt Hlay) ltac:(lia))
      as (wld0 & Hwld0 & Hwok0).
    iApply (wp_uv_lbu C pt Pinit M3 m2 (mword_of_int 0x4e0)
              (mword_of_int 0 : mword 12) (mword_of_int 11 : mword 5)
              (mword_of_int 9 : mword 5) wld0
              (mword_of_int s) (zero_extend' 64 (b0 : mword 8)) (b0 : mword 8)
              (ui_init_4e0 pt M3 (ilay_text pt Hlay) (init_img_text M3 Ht3))
              ltac:(vm_compute; discriminate) Hva4e0 Hwld0 Hwok0
              ltac:(apply uva_canon_small; rewrite <- uint_unsigned; rewrite Hus; lia)
              ltac:(rewrite Hus; exact Hb0m) eq_refl
              with "Hcg Hpc").
    iIntros (K6) "Hcg Hpc".
    set (m3 := <[Regidx (mword_of_int 9 : mword 5)
                 := regval_into_reg (zero_extend' 64 (b0 : mword 8) : mword 64)]> m2).
    assert (E4e0 : add_vec_int (mword_of_int 0x4e0 : mword 64) 4
                   = mword_of_int 0x4e4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4e0) in "Hpc".

    (* ---- 0x4e4  beqz s1,70a  -- the string is non-empty: NOT taken ---- *)
    pose proof (bv_unsigned_in_range _ b0) as Hb0r.
    assert (E8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite E8 in Hb0r.
    assert (Hb0nz : b0 <> ubyte0) by exact (il_nz _ _ _ Hlit 0%nat b0 Hb0).
    assert (Hb0u : bv_unsigned b0 <> 0).
    { intro Hz. apply Hb0nz. apply bv_eq. rewrite Hz. vm_compute. reflexivity. }
    assert (Hm3s1 : m3 !!! Regidx (mword_of_int 9 : mword 5)
                    = (mword_of_int (bv_unsigned b0) : mword 64)).
    { rewrite (upd_eq m2 (Regidx (mword_of_int 9 : mword 5))
                 (regval_into_reg (zero_extend' 64 (b0 : mword 8) : mword 64))).
      exact (zext8_moi b0). }
    assert (Ht4e4 : false = uv_btaken BEQ
                              (m3 !!! Regidx (mword_of_int 9 : mword 5)) zero_reg).
    { cbn [uv_btaken]. rewrite Hm3s1. rewrite zero_reg_moi.
      rewrite (moi_eq_vec (bv_unsigned b0) 0 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. exact Hb0u. }
    iApply (wp_uv_btype0 C pt Pinit M3 m3 (mword_of_int 0x4e4)
              (mword_of_int 550 : mword 13) (mword_of_int 9 : mword 5) BEQ
              false (mword_of_int 0x70a)
              (ui_init_4e4 pt M3 (ilay_text pt Hlay) (init_img_text M3 Ht3))
              Ht4e4 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hx; discriminate)
              with "Hcg Hpc").
    iIntros (K7) "Hcg Hpc".
    assert (E4e4 : add_vec_int (mword_of_int 0x4e4 : mword 64) 4
                   = mword_of_int 0x4e8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4e4) in "Hpc".
    assert (Hsp3 : m3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5))
                          (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5))
                          (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) _).
      exact Hsp1. }
    assert (Hr18 : m3 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr19 : m3 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr20 : m3 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr21 : m3 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr22 : m3 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr23 : m3 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 23 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr24 : m3 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 24 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 24 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 24 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr10 : m3 !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 10 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 10 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 10 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr11 : m3 !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 11 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 11 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 11 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }
    assert (Hr12 : m3 !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5)).
    { refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 12 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 12 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx (mword_of_int 12 : mword 5)) _
                        ltac:(vm_compute; discriminate)). }

    (* ---- 0x4e8  c.sdsp s2,64(sp) ---- *)
    iApply (wp_uv_frame_store C pt K7 Pinit M3 m3 sp0 (mword_of_int 0x4e8)
              (mword_of_int 8 : mword 6) (mword_of_int 18 : mword 5) 96 64
              (ui_init_4e8 pt M3 (ilay_text pt Hlay) (init_img_text M3 Ht3)) Hs3
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K8) "Hcg Hpc".
    iEval (rewrite Hr18) in "Hcg".
    set (M4 := uM_store8 M3 (uint sp0 - 96 + 64) (m !!! Regidx (mword_of_int 18 : mword 5))).
    assert (Ho4 : uM_only M3 M4 (uint sp0 - 96) 96)
      by (rewrite /M4; apply uM_only_store8; lia).
    assert (Hot4 : uM_only M3 M4 (uint sp0 - 96 + 64) 8)
      by (rewrite /M4; apply uM_only_store8; lia).
    assert (Hacc4 : uM_only M M4 (uint sp0 - 96) 96) by exact (uM_only_trans M M3 M4 (uint sp0 - 96) 96 Hacc3 Ho4).
    assert (Ht4 : init_img_sub M4)
      by exact (init_img_only M3 M4 (uint sp0 - 96) 96 ltac:(lia) Ho4 Ht3).
    assert (Hs4 : uv_stack pt M4 sp0 96)
      by exact (uM_only_stack pt M3 M4 sp0 96 (uint sp0 - 96) 96 Ho4 Hs3).
    assert (E4e8 : add_vec_int (mword_of_int 0x4e8 : mword 64) 2
                   = mword_of_int 0x4ea)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4e8) in "Hpc".

    (* ---- 0x4ea  c.sdsp s3,56(sp) ---- *)
    iApply (wp_uv_frame_store C pt K8 Pinit M4 m3 sp0 (mword_of_int 0x4ea)
              (mword_of_int 7 : mword 6) (mword_of_int 19 : mword 5) 96 56
              (ui_init_4ea pt M4 (ilay_text pt Hlay) (init_img_text M4 Ht4)) Hs4
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K9) "Hcg Hpc".
    iEval (rewrite Hr19) in "Hcg".
    set (M5 := uM_store8 M4 (uint sp0 - 96 + 56) (m !!! Regidx (mword_of_int 19 : mword 5))).
    assert (Ho5 : uM_only M4 M5 (uint sp0 - 96) 96)
      by (rewrite /M5; apply uM_only_store8; lia).
    assert (Hot5 : uM_only M4 M5 (uint sp0 - 96 + 56) 8)
      by (rewrite /M5; apply uM_only_store8; lia).
    assert (Hacc5 : uM_only M M5 (uint sp0 - 96) 96) by exact (uM_only_trans M M4 M5 (uint sp0 - 96) 96 Hacc4 Ho5).
    assert (Ht5 : init_img_sub M5)
      by exact (init_img_only M4 M5 (uint sp0 - 96) 96 ltac:(lia) Ho5 Ht4).
    assert (Hs5 : uv_stack pt M5 sp0 96)
      by exact (uM_only_stack pt M4 M5 sp0 96 (uint sp0 - 96) 96 Ho5 Hs4).
    assert (E4ea : add_vec_int (mword_of_int 0x4ea : mword 64) 2
                   = mword_of_int 0x4ec)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4ea) in "Hpc".

    (* ---- 0x4ec  c.sdsp s4,48(sp) ---- *)
    iApply (wp_uv_frame_store C pt K9 Pinit M5 m3 sp0 (mword_of_int 0x4ec)
              (mword_of_int 6 : mword 6) (mword_of_int 20 : mword 5) 96 48
              (ui_init_4ec pt M5 (ilay_text pt Hlay) (init_img_text M5 Ht5)) Hs5
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K10) "Hcg Hpc".
    iEval (rewrite Hr20) in "Hcg".
    set (M6 := uM_store8 M5 (uint sp0 - 96 + 48) (m !!! Regidx (mword_of_int 20 : mword 5))).
    assert (Ho6 : uM_only M5 M6 (uint sp0 - 96) 96)
      by (rewrite /M6; apply uM_only_store8; lia).
    assert (Hot6 : uM_only M5 M6 (uint sp0 - 96 + 48) 8)
      by (rewrite /M6; apply uM_only_store8; lia).
    assert (Hacc6 : uM_only M M6 (uint sp0 - 96) 96) by exact (uM_only_trans M M5 M6 (uint sp0 - 96) 96 Hacc5 Ho6).
    assert (Ht6 : init_img_sub M6)
      by exact (init_img_only M5 M6 (uint sp0 - 96) 96 ltac:(lia) Ho6 Ht5).
    assert (Hs6 : uv_stack pt M6 sp0 96)
      by exact (uM_only_stack pt M5 M6 sp0 96 (uint sp0 - 96) 96 Ho6 Hs5).
    assert (E4ec : add_vec_int (mword_of_int 0x4ec : mword 64) 2
                   = mword_of_int 0x4ee)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4ec) in "Hpc".

    (* ---- 0x4ee  c.sdsp s5,40(sp) ---- *)
    iApply (wp_uv_frame_store C pt K10 Pinit M6 m3 sp0 (mword_of_int 0x4ee)
              (mword_of_int 5 : mword 6) (mword_of_int 21 : mword 5) 96 40
              (ui_init_4ee pt M6 (ilay_text pt Hlay) (init_img_text M6 Ht6)) Hs6
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K11) "Hcg Hpc".
    iEval (rewrite Hr21) in "Hcg".
    set (M7 := uM_store8 M6 (uint sp0 - 96 + 40) (m !!! Regidx (mword_of_int 21 : mword 5))).
    assert (Ho7 : uM_only M6 M7 (uint sp0 - 96) 96)
      by (rewrite /M7; apply uM_only_store8; lia).
    assert (Hot7 : uM_only M6 M7 (uint sp0 - 96 + 40) 8)
      by (rewrite /M7; apply uM_only_store8; lia).
    assert (Hacc7 : uM_only M M7 (uint sp0 - 96) 96) by exact (uM_only_trans M M6 M7 (uint sp0 - 96) 96 Hacc6 Ho7).
    assert (Ht7 : init_img_sub M7)
      by exact (init_img_only M6 M7 (uint sp0 - 96) 96 ltac:(lia) Ho7 Ht6).
    assert (Hs7 : uv_stack pt M7 sp0 96)
      by exact (uM_only_stack pt M6 M7 sp0 96 (uint sp0 - 96) 96 Ho7 Hs6).
    assert (E4ee : add_vec_int (mword_of_int 0x4ee : mword 64) 2
                   = mword_of_int 0x4f0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4ee) in "Hpc".

    (* ---- 0x4f0  c.sdsp s6,32(sp) ---- *)
    iApply (wp_uv_frame_store C pt K11 Pinit M7 m3 sp0 (mword_of_int 0x4f0)
              (mword_of_int 4 : mword 6) (mword_of_int 22 : mword 5) 96 32
              (ui_init_4f0 pt M7 (ilay_text pt Hlay) (init_img_text M7 Ht7)) Hs7
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K12) "Hcg Hpc".
    iEval (rewrite Hr22) in "Hcg".
    set (M8 := uM_store8 M7 (uint sp0 - 96 + 32) (m !!! Regidx (mword_of_int 22 : mword 5))).
    assert (Ho8 : uM_only M7 M8 (uint sp0 - 96) 96)
      by (rewrite /M8; apply uM_only_store8; lia).
    assert (Hot8 : uM_only M7 M8 (uint sp0 - 96 + 32) 8)
      by (rewrite /M8; apply uM_only_store8; lia).
    assert (Hacc8 : uM_only M M8 (uint sp0 - 96) 96) by exact (uM_only_trans M M7 M8 (uint sp0 - 96) 96 Hacc7 Ho8).
    assert (Ht8 : init_img_sub M8)
      by exact (init_img_only M7 M8 (uint sp0 - 96) 96 ltac:(lia) Ho8 Ht7).
    assert (Hs8 : uv_stack pt M8 sp0 96)
      by exact (uM_only_stack pt M7 M8 sp0 96 (uint sp0 - 96) 96 Ho8 Hs7).
    assert (E4f0 : add_vec_int (mword_of_int 0x4f0 : mword 64) 2
                   = mword_of_int 0x4f2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4f0) in "Hpc".

    (* ---- 0x4f2  c.sdsp s7,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt K12 Pinit M8 m3 sp0 (mword_of_int 0x4f2)
              (mword_of_int 3 : mword 6) (mword_of_int 23 : mword 5) 96 24
              (ui_init_4f2 pt M8 (ilay_text pt Hlay) (init_img_text M8 Ht8)) Hs8
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K13) "Hcg Hpc".
    iEval (rewrite Hr23) in "Hcg".
    set (M9 := uM_store8 M8 (uint sp0 - 96 + 24) (m !!! Regidx (mword_of_int 23 : mword 5))).
    assert (Ho9 : uM_only M8 M9 (uint sp0 - 96) 96)
      by (rewrite /M9; apply uM_only_store8; lia).
    assert (Hot9 : uM_only M8 M9 (uint sp0 - 96 + 24) 8)
      by (rewrite /M9; apply uM_only_store8; lia).
    assert (Hacc9 : uM_only M M9 (uint sp0 - 96) 96) by exact (uM_only_trans M M8 M9 (uint sp0 - 96) 96 Hacc8 Ho9).
    assert (Ht9 : init_img_sub M9)
      by exact (init_img_only M8 M9 (uint sp0 - 96) 96 ltac:(lia) Ho9 Ht8).
    assert (Hs9 : uv_stack pt M9 sp0 96)
      by exact (uM_only_stack pt M8 M9 sp0 96 (uint sp0 - 96) 96 Ho9 Hs8).
    assert (E4f2 : add_vec_int (mword_of_int 0x4f2 : mword 64) 2
                   = mword_of_int 0x4f4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4f2) in "Hpc".

    (* ---- 0x4f4  c.sdsp s8,16(sp) ---- *)
    iApply (wp_uv_frame_store C pt K13 Pinit M9 m3 sp0 (mword_of_int 0x4f4)
              (mword_of_int 2 : mword 6) (mword_of_int 24 : mword 5) 96 16
              (ui_init_4f4 pt M9 (ilay_text pt Hlay) (init_img_text M9 Ht9)) Hs9
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K14) "Hcg Hpc".
    iEval (rewrite Hr24) in "Hcg".
    set (M10 := uM_store8 M9 (uint sp0 - 96 + 16) (m !!! Regidx (mword_of_int 24 : mword 5))).
    assert (Ho10 : uM_only M9 M10 (uint sp0 - 96) 96)
      by (rewrite /M10; apply uM_only_store8; lia).
    assert (Hot10 : uM_only M9 M10 (uint sp0 - 96 + 16) 8)
      by (rewrite /M10; apply uM_only_store8; lia).
    assert (Hacc10 : uM_only M M10 (uint sp0 - 96) 96) by exact (uM_only_trans M M9 M10 (uint sp0 - 96) 96 Hacc9 Ho10).
    assert (Ht10 : init_img_sub M10)
      by exact (init_img_only M9 M10 (uint sp0 - 96) 96 ltac:(lia) Ho10 Ht9).
    assert (Hs10 : uv_stack pt M10 sp0 96)
      by exact (uM_only_stack pt M9 M10 sp0 96 (uint sp0 - 96) 96 Ho10 Hs9).
    assert (E4f4 : add_vec_int (mword_of_int 0x4f4 : mword 64) 2
                   = mword_of_int 0x4f6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4f4) in "Hpc".
    assert (Hf88 : uM_bytes M10 (uint sp0 - 96 + 88) 8 (m !!! Regidx (mword_of_int 1 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 88) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 88) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only M7 M8 (uint sp0 - 96 + 88) (uint sp0 - 96 + 32) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only M6 M7 (uint sp0 - 96 + 88) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot7 | lia | ].
      apply (uM_bytes_only M5 M6 (uint sp0 - 96 + 88) (uint sp0 - 96 + 48) 8 8);
        [ exact Hot6 | lia | ].
      apply (uM_bytes_only M4 M5 (uint sp0 - 96 + 88) (uint sp0 - 96 + 56) 8 8);
        [ exact Hot5 | lia | ].
      apply (uM_bytes_only M3 M4 (uint sp0 - 96 + 88) (uint sp0 - 96 + 64) 8 8);
        [ exact Hot4 | lia | ].
      apply (uM_bytes_only M2 M3 (uint sp0 - 96 + 88) (uint sp0 - 96 + 72) 8 8);
        [ exact Hot3 | lia | ].
      apply (uM_bytes_only M1 M2 (uint sp0 - 96 + 88) (uint sp0 - 96 + 80) 8 8);
        [ exact Hot2 | lia | ].
      rewrite /M1. exact (uM_store8_bytes M (uint sp0 - 96 + 88) _). }
    assert (Hf80 : uM_bytes M10 (uint sp0 - 96 + 80) 8 (m !!! Regidx (mword_of_int 8 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 80) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 80) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only M7 M8 (uint sp0 - 96 + 80) (uint sp0 - 96 + 32) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only M6 M7 (uint sp0 - 96 + 80) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot7 | lia | ].
      apply (uM_bytes_only M5 M6 (uint sp0 - 96 + 80) (uint sp0 - 96 + 48) 8 8);
        [ exact Hot6 | lia | ].
      apply (uM_bytes_only M4 M5 (uint sp0 - 96 + 80) (uint sp0 - 96 + 56) 8 8);
        [ exact Hot5 | lia | ].
      apply (uM_bytes_only M3 M4 (uint sp0 - 96 + 80) (uint sp0 - 96 + 64) 8 8);
        [ exact Hot4 | lia | ].
      apply (uM_bytes_only M2 M3 (uint sp0 - 96 + 80) (uint sp0 - 96 + 72) 8 8);
        [ exact Hot3 | lia | ].
      rewrite /M2. exact (uM_store8_bytes M1 (uint sp0 - 96 + 80) _). }
    assert (Hf72 : uM_bytes M10 (uint sp0 - 96 + 72) 8 (m !!! Regidx (mword_of_int 9 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 72) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 72) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only M7 M8 (uint sp0 - 96 + 72) (uint sp0 - 96 + 32) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only M6 M7 (uint sp0 - 96 + 72) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot7 | lia | ].
      apply (uM_bytes_only M5 M6 (uint sp0 - 96 + 72) (uint sp0 - 96 + 48) 8 8);
        [ exact Hot6 | lia | ].
      apply (uM_bytes_only M4 M5 (uint sp0 - 96 + 72) (uint sp0 - 96 + 56) 8 8);
        [ exact Hot5 | lia | ].
      apply (uM_bytes_only M3 M4 (uint sp0 - 96 + 72) (uint sp0 - 96 + 64) 8 8);
        [ exact Hot4 | lia | ].
      rewrite /M3. exact (uM_store8_bytes M2 (uint sp0 - 96 + 72) _). }
    assert (Hf64 : uM_bytes M10 (uint sp0 - 96 + 64) 8 (m !!! Regidx (mword_of_int 18 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 64) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 64) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only M7 M8 (uint sp0 - 96 + 64) (uint sp0 - 96 + 32) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only M6 M7 (uint sp0 - 96 + 64) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot7 | lia | ].
      apply (uM_bytes_only M5 M6 (uint sp0 - 96 + 64) (uint sp0 - 96 + 48) 8 8);
        [ exact Hot6 | lia | ].
      apply (uM_bytes_only M4 M5 (uint sp0 - 96 + 64) (uint sp0 - 96 + 56) 8 8);
        [ exact Hot5 | lia | ].
      rewrite /M4. exact (uM_store8_bytes M3 (uint sp0 - 96 + 64) _). }
    assert (Hf56 : uM_bytes M10 (uint sp0 - 96 + 56) 8 (m !!! Regidx (mword_of_int 19 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 56) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 56) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only M7 M8 (uint sp0 - 96 + 56) (uint sp0 - 96 + 32) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only M6 M7 (uint sp0 - 96 + 56) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot7 | lia | ].
      apply (uM_bytes_only M5 M6 (uint sp0 - 96 + 56) (uint sp0 - 96 + 48) 8 8);
        [ exact Hot6 | lia | ].
      rewrite /M5. exact (uM_store8_bytes M4 (uint sp0 - 96 + 56) _). }
    assert (Hf48 : uM_bytes M10 (uint sp0 - 96 + 48) 8 (m !!! Regidx (mword_of_int 20 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 48) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 48) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only M7 M8 (uint sp0 - 96 + 48) (uint sp0 - 96 + 32) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only M6 M7 (uint sp0 - 96 + 48) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot7 | lia | ].
      rewrite /M6. exact (uM_store8_bytes M5 (uint sp0 - 96 + 48) _). }
    assert (Hf40 : uM_bytes M10 (uint sp0 - 96 + 40) 8 (m !!! Regidx (mword_of_int 21 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 40) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 40) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only M7 M8 (uint sp0 - 96 + 40) (uint sp0 - 96 + 32) 8 8);
        [ exact Hot8 | lia | ].
      rewrite /M7. exact (uM_store8_bytes M6 (uint sp0 - 96 + 40) _). }
    assert (Hf32 : uM_bytes M10 (uint sp0 - 96 + 32) 8 (m !!! Regidx (mword_of_int 22 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 32) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only M8 M9 (uint sp0 - 96 + 32) (uint sp0 - 96 + 24) 8 8);
        [ exact Hot9 | lia | ].
      rewrite /M8. exact (uM_store8_bytes M7 (uint sp0 - 96 + 32) _). }
    assert (Hf24 : uM_bytes M10 (uint sp0 - 96 + 24) 8 (m !!! Regidx (mword_of_int 23 : mword 5))).
    { apply (uM_bytes_only M9 M10 (uint sp0 - 96 + 24) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot10 | lia | ].
      rewrite /M9. exact (uM_store8_bytes M8 (uint sp0 - 96 + 24) _). }
    assert (Hf16 : uM_bytes M10 (uint sp0 - 96 + 16) 8 (m !!! Regidx (mword_of_int 24 : mword 5))).
    { rewrite /M10. exact (uM_store8_bytes M9 (uint sp0 - 96 + 16) _). }

    (* ---- 0x4f6  mv s6,a0 ---- *)
    iApply (wp_uv_cmv C pt Pinit M10 m3 (mword_of_int 0x4f6)
              (mword_of_int 22 : mword 5) (mword_of_int 10 : mword 5)
              (m !!! Regidx a0_idx)
              (ui_init_4f6 pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hr10; reflexivity)
              with "Hcg Hpc").
    iIntros (K15) "Hcg Hpc".
    set (m4 := <[Regidx (mword_of_int 22 : mword 5)
                 := regval_into_reg (m !!! Regidx a0_idx)]> m3).
    assert (E4f6 : add_vec_int (mword_of_int 0x4f6 : mword 64) 2
                   = mword_of_int 0x4f8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4f6) in "Hpc".

    (* ---- 0x4f8  mv s4,a1 ---- *)
    assert (Hm4a1 : m4 !!! Regidx a1_idx = (mword_of_int s : mword 64))
      by exact (eq_trans (upd_ne m3 (Regidx (mword_of_int 22 : mword 5))
                            (Regidx a1_idx) _ ltac:(vm_compute; discriminate))
                         (eq_trans Hr11 Hfmt)).
    iApply (wp_uv_cmv C pt Pinit M10 m4 (mword_of_int 0x4f8)
              (mword_of_int 20 : mword 5) (mword_of_int 11 : mword 5)
              (mword_of_int s)
              (ui_init_4f8 pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hm4a1; reflexivity)
              with "Hcg Hpc").
    iIntros (K16) "Hcg Hpc".
    set (m5 := <[Regidx (mword_of_int 20 : mword 5)
                 := regval_into_reg (mword_of_int s : mword 64)]> m4).
    assert (E4f8 : add_vec_int (mword_of_int 0x4f8 : mword 64) 2
                   = mword_of_int 0x4fa)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4f8) in "Hpc".

    (* ---- 0x4fa  mv s7,a2   (the va_list; never dereferenced here) ---- *)
    assert (Hm5a2 : m5 !!! Regidx a2_idx = m !!! Regidx a2_idx).
    { refine (eq_trans (upd_ne m4 (Regidx (mword_of_int 20 : mword 5))
                          (Regidx a2_idx) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m3 (Regidx (mword_of_int 22 : mword 5))
                          (Regidx a2_idx) _ ltac:(vm_compute; discriminate)) _).
      exact Hr12. }
    iApply (wp_uv_cmv C pt Pinit M10 m5 (mword_of_int 0x4fa)
              (mword_of_int 23 : mword 5) (mword_of_int 12 : mword 5)
              (m !!! Regidx a2_idx)
              (ui_init_4fa pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hm5a2; reflexivity)
              with "Hcg Hpc").
    iIntros (K17) "Hcg Hpc".
    set (m6 := <[Regidx (mword_of_int 23 : mword 5)
                 := regval_into_reg (m !!! Regidx a2_idx)]> m5).
    assert (E4fa : add_vec_int (mword_of_int 0x4fa : mword 64) 2
                   = mword_of_int 0x4fc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4fa) in "Hpc".

    (* ---- 0x4fc  li s3,0 ---- *)
    iApply (wp_uv_cli C pt Pinit M10 m6 (mword_of_int 0x4fc)
              (mword_of_int 0 : mword 6) (mword_of_int 19 : mword 5)
              (mword_of_int 0)
              (ui_init_4fc pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K18) "Hcg Hpc".
    set (m7 := <[Regidx (mword_of_int 19 : mword 5)
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m6).
    assert (E4fc : add_vec_int (mword_of_int 0x4fc : mword 64) 2
                   = mword_of_int 0x4fe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4fc) in "Hpc".

    (* ---- 0x4fe  li s2,0 ---- *)
    iApply (wp_uv_cli C pt Pinit M10 m7 (mword_of_int 0x4fe)
              (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              (mword_of_int 0)
              (ui_init_4fe pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K19) "Hcg Hpc".
    set (m8 := <[Regidx (mword_of_int 18 : mword 5)
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m7).
    assert (E4fe : add_vec_int (mword_of_int 0x4fe : mword 64) 2
                   = mword_of_int 0x500)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4fe) in "Hpc".

    (* ---- 0x500  li a4,0 ---- *)
    iApply (wp_uv_cli C pt Pinit M10 m8 (mword_of_int 0x500)
              (mword_of_int 0 : mword 6) (mword_of_int 14 : mword 5)
              (mword_of_int 0)
              (ui_init_500 pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K20) "Hcg Hpc".
    set (m9 := <[Regidx (mword_of_int 14 : mword 5)
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m8).
    assert (E500 : add_vec_int (mword_of_int 0x500 : mword 64) 2
                   = mword_of_int 0x502)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E500) in "Hpc".

    (* ---- 0x502  li s5,37   ('%') ---- *)
    iApply (wp_uv_li C pt Pinit M10 m9 (mword_of_int 0x502)
              (mword_of_int 37 : mword 12) (mword_of_int 21 : mword 5)
              (mword_of_int 37)
              (ui_init_502 pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K21) "Hcg Hpc".
    set (m10 := <[Regidx (mword_of_int 21 : mword 5)
                  := regval_into_reg (mword_of_int 37 : mword 64)]> m9).
    assert (E502 : add_vec_int (mword_of_int 0x502 : mword 64) 4
                   = mword_of_int 0x506)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E502) in "Hpc".

    (* ---- 0x506  li s8,100   ('d') ---- *)
    iApply (wp_uv_li C pt Pinit M10 m10 (mword_of_int 0x506)
              (mword_of_int 100 : mword 12) (mword_of_int 24 : mword 5)
              (mword_of_int 100)
              (ui_init_506 pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K22) "Hcg Hpc".
    set (m11 := <[Regidx (mword_of_int 24 : mword 5)
                  := regval_into_reg (mword_of_int 100 : mword 64)]> m10).
    assert (E506 : add_vec_int (mword_of_int 0x506 : mword 64) 4
                   = mword_of_int 0x50a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E506) in "Hpc".

    (* ---- 0x50a  j 52c ---- *)
    iApply (wp_uv_cj C pt Pinit M10 m11 (mword_of_int 0x50a)
              (mword_of_int 17 : mword 11) (mword_of_int 0x52c)
              (ui_init_50a pt M10 (ilay_text pt Hlay) (init_img_text M10 Ht10))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K23) "Hcg Hpc".
    assert (Hm11sp : m11 !!! Regidx (mword_of_int 2 : mword 5) = (mword_of_int (uint sp0 - 96) : mword 64)).
    { refine (eq_trans (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m9 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m8 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m7 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m6 (Regidx (mword_of_int 19 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m4 (Regidx (mword_of_int 20 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m3 (Regidx (mword_of_int 22 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 2 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m (Regidx csp_rs1)
                 (regval_into_reg (mword_of_int (uint sp0 - 96) : mword 64))). }
    assert (Hm11s1 : m11 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int (bv_unsigned b0) : mword 64)).
    { refine (eq_trans (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m9 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m8 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m7 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m6 (Regidx (mword_of_int 19 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m4 (Regidx (mword_of_int 20 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m3 (Regidx (mword_of_int 22 : mword 5)) (Regidx (mword_of_int 9 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      rewrite (upd_eq m2 (Regidx (mword_of_int 9 : mword 5))
                 (regval_into_reg (zero_extend' 64 (b0 : mword 8) : mword 64))).
      exact (zext8_moi b0). }
    assert (Hm11s2 : m11 !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int (Z.of_nat 0) : mword 64)).
    { refine (eq_trans (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m9 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m8 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 18 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m7 (Regidx (mword_of_int 18 : mword 5)) (regval_into_reg (mword_of_int 0 : mword 64))). }
    assert (Hm11s3 : m11 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 0 : mword 64)).
    { refine (eq_trans (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m9 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m8 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m7 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 19 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m6 (Regidx (mword_of_int 19 : mword 5)) (regval_into_reg (mword_of_int 0 : mword 64))). }
    assert (Hm11s4 : m11 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int s : mword 64)).
    { refine (eq_trans (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m9 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m8 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m7 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m6 (Regidx (mword_of_int 19 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 20 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m4 (Regidx (mword_of_int 20 : mword 5)) (regval_into_reg (mword_of_int s : mword 64))). }
    assert (Hm11s5 : m11 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 37 : mword 64)).
    { refine (eq_trans (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 21 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m9 (Regidx (mword_of_int 21 : mword 5)) (regval_into_reg (mword_of_int 37 : mword 64))). }
    assert (Hm11s6 : m11 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx a0_idx).
    { refine (eq_trans (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m9 (Regidx (mword_of_int 21 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m8 (Regidx (mword_of_int 14 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m7 (Regidx (mword_of_int 18 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m6 (Regidx (mword_of_int 19 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m5 (Regidx (mword_of_int 23 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m4 (Regidx (mword_of_int 20 : mword 5)) (Regidx (mword_of_int 22 : mword 5)) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m3 (Regidx (mword_of_int 22 : mword 5)) (regval_into_reg (m !!! Regidx a0_idx))). }
    assert (Hm11cs : vp_rest m11 m).
    { intros r Hr Hn2 Hn8 Hn9 Hn18 Hn19 Hn20 Hn21 Hn22 Hn23 Hn24.
      assert (Hne : forall kz : Z,
                ucallee_saved_idx (mword_of_int kz : mword 5) = false ->
                Regidx r <> Regidx (mword_of_int kz : mword 5)).
      { intros kz Hkz Heq. injection Heq as Heq'.
        rewrite Heq' in Hr. rewrite Hkz in Hr. discriminate. }
      rewrite (upd_ne m10 (Regidx (mword_of_int 24 : mword 5)) (Regidx r) _ Hn24).
      rewrite (upd_ne m9 (Regidx (mword_of_int 21 : mword 5)) (Regidx r) _ Hn21).
      rewrite (upd_ne m8 (Regidx (mword_of_int 14 : mword 5)) (Regidx r) _ (Hne 14 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne m7 (Regidx (mword_of_int 18 : mword 5)) (Regidx r) _ Hn18).
      rewrite (upd_ne m6 (Regidx (mword_of_int 19 : mword 5)) (Regidx r) _ Hn19).
      rewrite (upd_ne m5 (Regidx (mword_of_int 23 : mword 5)) (Regidx r) _ Hn23).
      rewrite (upd_ne m4 (Regidx (mword_of_int 20 : mword 5)) (Regidx r) _ Hn20).
      rewrite (upd_ne m3 (Regidx (mword_of_int 22 : mword 5)) (Regidx r) _ Hn22).
      rewrite (upd_ne m2 (Regidx (mword_of_int 9 : mword 5)) (Regidx r) _ Hn9).
      rewrite (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx r) _ Hn8).
      rewrite (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx r) _ Hn2).
      reflexivity. }
    (* ---- the loop ---- *)
    assert (Hst10 : uv_stack pt M10 sp0 128)
      by exact (uM_only_stack pt M M10 sp0 128 (uint sp0 - 128) 128
                  (uM_only_widen M M10 (uint sp0 - 96) 96 (uint sp0 - 128) 128
                     Hacc10 ltac:(lia) ltac:(lia)) Hst).
    assert (Hlit10 : init_lit M10 s bs)
      by exact (init_lit_only M M10 (uint sp0 - 96) 96 s bs ltac:(lia) Hacc10 Hlit).
    iApply (init_vprintf_loop (S (length bs)) sp0 M10 m s bs
              Hlay Ht10 Hst10 Hlit10 ltac:(lia) Hsp Hret2
              ltac:(split_and!; assumption)
              K23 0%nat b0 M10 m11
              ltac:(cbn; lia) Hbslen Hb0
              (uM_only_refl M10 (uint sp0 - 128) 32)
              Hm11sp Hm11s1 Hm11s2 Hm11s3 Hm11s4 Hm11s5 Hm11s6 Hm11cs
              with "Hcg Hwobs Hpc [Hcont]").
    iIntros (KZ mz Mz) "%Hcsz %Hoz Hcg Hpc".
    iApply ("Hcont" $! KZ mz Mz with "[] [] Hcg Hpc").
    - iPureIntro. exact Hcsz.
    - iPureIntro.
      refine (uM_only_trans M M10 Mz (uint sp0 - 128) 128
                (uM_only_widen M M10 (uint sp0 - 96) 96 (uint sp0 - 128) 128
                   Hacc10 ltac:(lia) ltac:(lia))
                (uM_only_widen M10 Mz (uint sp0 - 128) 32 (uint sp0 - 128) 128
                   Hoz ltac:(lia) ltac:(lia))).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2d printf(fmt, ...) -- spill a0..a7 into the varargs save area,      *)
  (* build [ap], and call vprintf(1, fmt, ap).  Nothing reads the saved    *)
  (* arguments on a %-free format string, so the nine stores are pure      *)
  (* frame writes.                                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_init_printf (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s : Z) (bs : list (bv 8)) :
    wp_init_printf_body (CID := CIDp) C pt Q W M m sp0 s bs.
  Proof.
    intros Hlay Himg Hsp Hst Hfr Hfmt Hlit Hret2.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hhi.
    unfold init_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhi.
    destruct (uv_stack_split pt M sp0 224 96 128 eq_refl ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hs96 & Hs128).
    assert (Espb : add_vec_int sp0 (- 96) = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (uv_stack_sp_moi pt M sp0 96 Hs96).
    rewrite Espb in Hs128.
    assert (Husp : uint (mword_of_int (uint sp0 - 96) : mword 64) = uint sp0 - 96)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hsp' : m !!! Regidx csp_rs1 = (mword_of_int (uint sp0) : mword 64))
      by (rewrite moi_of_uint; exact Hsp).
    (* the store immediates, once each *)
    assert (Hi8 : (sign_extend' 64
                (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 5) ('b"000")))
                : mword 64) = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hi16 : (sign_extend' 64
                (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")))
                : mword 64) = mword_of_int 16)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hi24 : (sign_extend' 64
                (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 5) ('b"000")))
                : mword 64) = mword_of_int 24)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hi32 : (sign_extend' 64
                (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))
                : mword 64) = mword_of_int 32)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hi40 : (sign_extend' 64
                (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 5) ('b"000")))
                : mword 64) = mword_of_int 40)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hb48 : (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64)
                    = mword_of_int (48))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hb56 : (sign_extend' 64 (mword_of_int 56 : mword 12) : mword 64)
                    = mword_of_int (56))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hb4072 : (sign_extend' 64 (mword_of_int 4072 : mword 12) : mword 64)
                    = mword_of_int (-24))
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros "Hcg #Hwobs Hpc Hcont".
    iEval (change (mword_of_int InitSyms.printf : mword 64)
             with (mword_of_int 0x7c0 : mword 64)) in "Hpc".

    (* ---- 0x7c0  c.addi16sp sp,sp,-96 ---- *)
    assert (Hw7c0 : (mword_of_int (uint sp0 - 96) : mword 64)
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))
                      : mword 64) = mword_of_int (-96))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp'. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Pinit M m (mword_of_int 0x7c0)
              (mword_of_int 58 : mword 6) (mword_of_int (uint sp0 - 96))
              (ui_init_7c0 pt M (ilay_text pt Hlay) (init_img_text M Himg)) Hw7c0
              with "Hcg Hpc").
    iIntros (P1) "Hcg Hpc".
    set (p1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 96) : mword 64)]> m).
    assert (Hspp1 : p1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (mword_of_int (uint sp0 - 96) : mword 64))).
    assert (Hp1ra : p1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hp1s0 : p1 !!! Regidx (mword_of_int 8 : mword 5)
                    = m !!! Regidx (mword_of_int 8 : mword 5))
      by exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 8 : mword 5)) _
                  ltac:(vm_compute; discriminate)).
    assert (E7c0 : add_vec_int (mword_of_int 0x7c0 : mword 64) 2
                   = mword_of_int 0x7c2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7c0) in "Hpc".

    (* ---- 0x7c2  c.sdsp ra,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt P1 Pinit M p1 sp0 (mword_of_int 0x7c2)
              (mword_of_int 3 : mword 6) ra_idx 96 24
              (ui_init_7c2 pt M (ilay_text pt Hlay) (init_img_text M Himg)) Hs96
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hspp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (P2) "Hcg Hpc".
    iEval (rewrite Hp1ra) in "Hcg".
    set (N1 := uM_store8 M (uint sp0 - 96 + 24) (m !!! Regidx ra_idx)).
    assert (Ho1 : uM_only M N1 (uint sp0 - 96) 96)
      by (rewrite /N1; apply uM_only_store8; lia).
    assert (Hot1 : uM_only M N1 (uint sp0 - 96 + 24) 8)
      by (rewrite /N1; apply uM_only_store8; lia).
    assert (Hacc1 : uM_only M N1 (uint sp0 - 96) 96) by exact Ho1.
    assert (Ht1 : init_img_sub N1)
      by exact (init_img_only M N1 (uint sp0 - 96) 96 ltac:(lia) Ho1 Himg).
    assert (Hs1 : uv_stack pt N1 sp0 96)
      by exact (uM_only_stack pt M N1 sp0 96 (uint sp0 - 96) 96 Ho1 Hs96).
    assert (E7c2 : add_vec_int (mword_of_int 0x7c2 : mword 64) 2
                   = mword_of_int 0x7c4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7c2) in "Hpc".

    (* ---- 0x7c4  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uv_frame_store C pt P2 Pinit N1 p1 sp0 (mword_of_int 0x7c4)
              (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5) 96 16
              (ui_init_7c4 pt N1 (ilay_text pt Hlay) (init_img_text N1 Ht1)) Hs1
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hspp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (P3) "Hcg Hpc".
    iEval (rewrite Hp1s0) in "Hcg".
    set (N2 := uM_store8 N1 (uint sp0 - 96 + 16)
                 (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Ho2 : uM_only N1 N2 (uint sp0 - 96) 96)
      by (rewrite /N2; apply uM_only_store8; lia).
    assert (Hot2 : uM_only N1 N2 (uint sp0 - 96 + 16) 8)
      by (rewrite /N2; apply uM_only_store8; lia).
    assert (Hacc2 : uM_only M N2 (uint sp0 - 96) 96)
      by exact (uM_only_trans M N1 N2 (uint sp0 - 96) 96 Hacc1 Ho2).
    assert (Ht2 : init_img_sub N2)
      by exact (init_img_only N1 N2 (uint sp0 - 96) 96 ltac:(lia) Ho2 Ht1).
    assert (Hs2 : uv_stack pt N2 sp0 96)
      by exact (uM_only_stack pt N1 N2 sp0 96 (uint sp0 - 96) 96 Ho2 Hs1).
    assert (E7c4 : add_vec_int (mword_of_int 0x7c4 : mword 64) 2
                   = mword_of_int 0x7c6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7c4) in "Hpc".

    (* ---- 0x7c6  c.addi4spn s0,sp,32 ---- *)
    assert (Hw7c6 : (mword_of_int (uint sp0 - 64) : mword 64)
                    = add_vec (p1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { assert (Hcst : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                      : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hspp1. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Pinit N2 p1 (mword_of_int 0x7c6)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8)
              (mword_of_int 8 : mword 5) (mword_of_int (uint sp0 - 64))
              (ui_init_7c6 pt N2 (ilay_text pt Hlay) (init_img_text N2 Ht2))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw7c6
              with "Hcg Hpc").
    iIntros (P4) "Hcg Hpc".
    set (p2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64)]> p1).
    assert (Hs0p2 : p2 !!! Regidx (mword_of_int 8 : mword 5)
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (upd_eq p1 (Regidx (mword_of_int 8 : mword 5))
                  (regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64))).
    assert (E7c6 : add_vec_int (mword_of_int 0x7c6 : mword 64) 2
                   = mword_of_int 0x7c8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7c6) in "Hpc".
    assert (Hp2r11 : p2 !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5)).
    { refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 11 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 11 : mword 5)) _
               ltac:(vm_compute; discriminate)). }
    assert (Hp2r12 : p2 !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5)).
    { refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 12 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 12 : mword 5)) _
               ltac:(vm_compute; discriminate)). }
    assert (Hp2r13 : p2 !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5)).
    { refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 13 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 13 : mword 5)) _
               ltac:(vm_compute; discriminate)). }
    assert (Hp2r14 : p2 !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5)).
    { refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 14 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 14 : mword 5)) _
               ltac:(vm_compute; discriminate)). }
    assert (Hp2r15 : p2 !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5)).
    { refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 15 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 15 : mword 5)) _
               ltac:(vm_compute; discriminate)). }
    assert (Hp2r16 : p2 !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5)).
    { refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 16 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 16 : mword 5)) _
               ltac:(vm_compute; discriminate)). }
    assert (Hp2r17 : p2 !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5)).
    { refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx (mword_of_int 17 : mword 5)) _
                        ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 17 : mword 5)) _
               ltac:(vm_compute; discriminate)). }

    (* ---- 0x7c8 ---- *)
    destruct (uv_stack_slot_moi pt N2 sp0 96 40
                (mword_of_int (uint sp0 - 96 + 40)) Hs2 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu3 & (wst3 & Hl3 & Hok3 & _) & Hcan3 & Hpg3 &
          Hal3 & Hby3).
    iApply (wp_uv_csd C pt Pinit N2 p2 (mword_of_int 0x7c8)
              (mword_of_int 1 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 3 : mword 3) (mword_of_int 8 : mword 5)
              (mword_of_int 11 : mword 5) wst3
              (mword_of_int (uint sp0 - 96 + 40)) (m !!! Regidx a1_idx)
              (ui_init_7c8 pt N2 (ilay_text pt Hlay) (init_img_text N2 Ht2))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0p2; rewrite Hi8; rewrite moi_add;
                    f_equal; lia)
              ltac:(rewrite Hp2r11; reflexivity)
              Hl3 Hok3 Hcan3 Hpg3 Hal3 Hby3
              with "Hcg Hpc").
    iIntros (P5) "Hcg Hpc".
    iEval (rewrite Hu3) in "Hcg".
    set (N3 := uM_store8 N2 (uint sp0 - 96 + 40) (m !!! Regidx a1_idx)).
    assert (Ho3 : uM_only N2 N3 (uint sp0 - 96) 96)
      by (rewrite /N3; apply uM_only_store8; lia).
    assert (Hot3 : uM_only N2 N3 (uint sp0 - 96 + 40) 8)
      by (rewrite /N3; apply uM_only_store8; lia).
    assert (Hacc3 : uM_only M N3 (uint sp0 - 96) 96) by exact (uM_only_trans M N2 N3 (uint sp0 - 96) 96 Hacc2 Ho3).
    assert (Ht3 : init_img_sub N3)
      by exact (init_img_only N2 N3 (uint sp0 - 96) 96 ltac:(lia) Ho3 Ht2).
    assert (Hs3 : uv_stack pt N3 sp0 96)
      by exact (uM_only_stack pt N2 N3 sp0 96 (uint sp0 - 96) 96 Ho3 Hs2).
    assert (E7c8 : add_vec_int (mword_of_int 0x7c8 : mword 64) 2
                   = mword_of_int 0x7ca)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7c8) in "Hpc".

    (* ---- 0x7ca ---- *)
    destruct (uv_stack_slot_moi pt N3 sp0 96 48
                (mword_of_int (uint sp0 - 96 + 48)) Hs3 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu4 & (wst4 & Hl4 & Hok4 & _) & Hcan4 & Hpg4 &
          Hal4 & Hby4).
    iApply (wp_uv_csd C pt Pinit N3 p2 (mword_of_int 0x7ca)
              (mword_of_int 2 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 4 : mword 3) (mword_of_int 8 : mword 5)
              (mword_of_int 12 : mword 5) wst4
              (mword_of_int (uint sp0 - 96 + 48)) (m !!! Regidx a2_idx)
              (ui_init_7ca pt N3 (ilay_text pt Hlay) (init_img_text N3 Ht3))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0p2; rewrite Hi16; rewrite moi_add;
                    f_equal; lia)
              ltac:(rewrite Hp2r12; reflexivity)
              Hl4 Hok4 Hcan4 Hpg4 Hal4 Hby4
              with "Hcg Hpc").
    iIntros (P6) "Hcg Hpc".
    iEval (rewrite Hu4) in "Hcg".
    set (N4 := uM_store8 N3 (uint sp0 - 96 + 48) (m !!! Regidx a2_idx)).
    assert (Ho4 : uM_only N3 N4 (uint sp0 - 96) 96)
      by (rewrite /N4; apply uM_only_store8; lia).
    assert (Hot4 : uM_only N3 N4 (uint sp0 - 96 + 48) 8)
      by (rewrite /N4; apply uM_only_store8; lia).
    assert (Hacc4 : uM_only M N4 (uint sp0 - 96) 96) by exact (uM_only_trans M N3 N4 (uint sp0 - 96) 96 Hacc3 Ho4).
    assert (Ht4 : init_img_sub N4)
      by exact (init_img_only N3 N4 (uint sp0 - 96) 96 ltac:(lia) Ho4 Ht3).
    assert (Hs4 : uv_stack pt N4 sp0 96)
      by exact (uM_only_stack pt N3 N4 sp0 96 (uint sp0 - 96) 96 Ho4 Hs3).
    assert (E7ca : add_vec_int (mword_of_int 0x7ca : mword 64) 2
                   = mword_of_int 0x7cc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7ca) in "Hpc".

    (* ---- 0x7cc ---- *)
    destruct (uv_stack_slot_moi pt N4 sp0 96 56
                (mword_of_int (uint sp0 - 96 + 56)) Hs4 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu5 & (wst5 & Hl5 & Hok5 & _) & Hcan5 & Hpg5 &
          Hal5 & Hby5).
    iApply (wp_uv_csd C pt Pinit N4 p2 (mword_of_int 0x7cc)
              (mword_of_int 3 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 5 : mword 3) (mword_of_int 8 : mword 5)
              (mword_of_int 13 : mword 5) wst5
              (mword_of_int (uint sp0 - 96 + 56)) (m !!! Regidx (mword_of_int 13 : mword 5))
              (ui_init_7cc pt N4 (ilay_text pt Hlay) (init_img_text N4 Ht4))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0p2; rewrite Hi24; rewrite moi_add;
                    f_equal; lia)
              ltac:(rewrite Hp2r13; reflexivity)
              Hl5 Hok5 Hcan5 Hpg5 Hal5 Hby5
              with "Hcg Hpc").
    iIntros (P7) "Hcg Hpc".
    iEval (rewrite Hu5) in "Hcg".
    set (N5 := uM_store8 N4 (uint sp0 - 96 + 56) (m !!! Regidx (mword_of_int 13 : mword 5))).
    assert (Ho5 : uM_only N4 N5 (uint sp0 - 96) 96)
      by (rewrite /N5; apply uM_only_store8; lia).
    assert (Hot5 : uM_only N4 N5 (uint sp0 - 96 + 56) 8)
      by (rewrite /N5; apply uM_only_store8; lia).
    assert (Hacc5 : uM_only M N5 (uint sp0 - 96) 96) by exact (uM_only_trans M N4 N5 (uint sp0 - 96) 96 Hacc4 Ho5).
    assert (Ht5 : init_img_sub N5)
      by exact (init_img_only N4 N5 (uint sp0 - 96) 96 ltac:(lia) Ho5 Ht4).
    assert (Hs5 : uv_stack pt N5 sp0 96)
      by exact (uM_only_stack pt N4 N5 sp0 96 (uint sp0 - 96) 96 Ho5 Hs4).
    assert (E7cc : add_vec_int (mword_of_int 0x7cc : mword 64) 2
                   = mword_of_int 0x7ce)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7cc) in "Hpc".

    (* ---- 0x7ce ---- *)
    destruct (uv_stack_slot_moi pt N5 sp0 96 64
                (mword_of_int (uint sp0 - 96 + 64)) Hs5 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu6 & (wst6 & Hl6 & Hok6 & _) & Hcan6 & Hpg6 &
          Hal6 & Hby6).
    iApply (wp_uv_csd C pt Pinit N5 p2 (mword_of_int 0x7ce)
              (mword_of_int 4 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 6 : mword 3) (mword_of_int 8 : mword 5)
              (mword_of_int 14 : mword 5) wst6
              (mword_of_int (uint sp0 - 96 + 64)) (m !!! Regidx (mword_of_int 14 : mword 5))
              (ui_init_7ce pt N5 (ilay_text pt Hlay) (init_img_text N5 Ht5))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0p2; rewrite Hi32; rewrite moi_add;
                    f_equal; lia)
              ltac:(rewrite Hp2r14; reflexivity)
              Hl6 Hok6 Hcan6 Hpg6 Hal6 Hby6
              with "Hcg Hpc").
    iIntros (P8) "Hcg Hpc".
    iEval (rewrite Hu6) in "Hcg".
    set (N6 := uM_store8 N5 (uint sp0 - 96 + 64) (m !!! Regidx (mword_of_int 14 : mword 5))).
    assert (Ho6 : uM_only N5 N6 (uint sp0 - 96) 96)
      by (rewrite /N6; apply uM_only_store8; lia).
    assert (Hot6 : uM_only N5 N6 (uint sp0 - 96 + 64) 8)
      by (rewrite /N6; apply uM_only_store8; lia).
    assert (Hacc6 : uM_only M N6 (uint sp0 - 96) 96) by exact (uM_only_trans M N5 N6 (uint sp0 - 96) 96 Hacc5 Ho6).
    assert (Ht6 : init_img_sub N6)
      by exact (init_img_only N5 N6 (uint sp0 - 96) 96 ltac:(lia) Ho6 Ht5).
    assert (Hs6 : uv_stack pt N6 sp0 96)
      by exact (uM_only_stack pt N5 N6 sp0 96 (uint sp0 - 96) 96 Ho6 Hs5).
    assert (E7ce : add_vec_int (mword_of_int 0x7ce : mword 64) 2
                   = mword_of_int 0x7d0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7ce) in "Hpc".

    (* ---- 0x7d0 ---- *)
    destruct (uv_stack_slot_moi pt N6 sp0 96 72
                (mword_of_int (uint sp0 - 96 + 72)) Hs6 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu7 & (wst7 & Hl7 & Hok7 & _) & Hcan7 & Hpg7 &
          Hal7 & Hby7).
    iApply (wp_uv_csd C pt Pinit N6 p2 (mword_of_int 0x7d0)
              (mword_of_int 5 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 7 : mword 3) (mword_of_int 8 : mword 5)
              (mword_of_int 15 : mword 5) wst7
              (mword_of_int (uint sp0 - 96 + 72)) (m !!! Regidx (mword_of_int 15 : mword 5))
              (ui_init_7d0 pt N6 (ilay_text pt Hlay) (init_img_text N6 Ht6))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0p2; rewrite Hi40; rewrite moi_add;
                    f_equal; lia)
              ltac:(rewrite Hp2r15; reflexivity)
              Hl7 Hok7 Hcan7 Hpg7 Hal7 Hby7
              with "Hcg Hpc").
    iIntros (P9) "Hcg Hpc".
    iEval (rewrite Hu7) in "Hcg".
    set (N7 := uM_store8 N6 (uint sp0 - 96 + 72) (m !!! Regidx (mword_of_int 15 : mword 5))).
    assert (Ho7 : uM_only N6 N7 (uint sp0 - 96) 96)
      by (rewrite /N7; apply uM_only_store8; lia).
    assert (Hot7 : uM_only N6 N7 (uint sp0 - 96 + 72) 8)
      by (rewrite /N7; apply uM_only_store8; lia).
    assert (Hacc7 : uM_only M N7 (uint sp0 - 96) 96) by exact (uM_only_trans M N6 N7 (uint sp0 - 96) 96 Hacc6 Ho7).
    assert (Ht7 : init_img_sub N7)
      by exact (init_img_only N6 N7 (uint sp0 - 96) 96 ltac:(lia) Ho7 Ht6).
    assert (Hs7 : uv_stack pt N7 sp0 96)
      by exact (uM_only_stack pt N6 N7 sp0 96 (uint sp0 - 96) 96 Ho7 Hs6).
    assert (E7d0 : add_vec_int (mword_of_int 0x7d0 : mword 64) 2
                   = mword_of_int 0x7d2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7d0) in "Hpc".

    (* ---- 0x7d2 ---- *)
    destruct (uv_stack_slot_moi pt N7 sp0 96 80
                (mword_of_int (uint sp0 - 96 + 80)) Hs7 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu8 & (wst8 & Hl8 & Hok8 & _) & Hcan8 & Hpg8 &
          Hal8 & Hby8).
    iApply (wp_uv_sd C pt Pinit N7 p2 (mword_of_int 0x7d2)
              (mword_of_int 48 : mword 12) (mword_of_int 8 : mword 5)
              (mword_of_int 16 : mword 5) wst8
              (mword_of_int (uint sp0 - 96 + 80)) (m !!! Regidx (mword_of_int 16 : mword 5))
              (ui_init_7d2 pt N7 (ilay_text pt Hlay) (init_img_text N7 Ht7))
              ltac:(rewrite Hs0p2; rewrite Hb48; rewrite moi_add;
                    f_equal; lia)
              ltac:(rewrite Hp2r16; reflexivity)
              Hl8 Hok8 Hcan8 Hpg8 Hal8 Hby8
              with "Hcg Hpc").
    iIntros (P10) "Hcg Hpc".
    iEval (rewrite Hu8) in "Hcg".
    set (N8 := uM_store8 N7 (uint sp0 - 96 + 80) (m !!! Regidx (mword_of_int 16 : mword 5))).
    assert (Ho8 : uM_only N7 N8 (uint sp0 - 96) 96)
      by (rewrite /N8; apply uM_only_store8; lia).
    assert (Hot8 : uM_only N7 N8 (uint sp0 - 96 + 80) 8)
      by (rewrite /N8; apply uM_only_store8; lia).
    assert (Hacc8 : uM_only M N8 (uint sp0 - 96) 96) by exact (uM_only_trans M N7 N8 (uint sp0 - 96) 96 Hacc7 Ho8).
    assert (Ht8 : init_img_sub N8)
      by exact (init_img_only N7 N8 (uint sp0 - 96) 96 ltac:(lia) Ho8 Ht7).
    assert (Hs8 : uv_stack pt N8 sp0 96)
      by exact (uM_only_stack pt N7 N8 sp0 96 (uint sp0 - 96) 96 Ho8 Hs7).
    assert (E7d2 : add_vec_int (mword_of_int 0x7d2 : mword 64) 4
                   = mword_of_int 0x7d6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7d2) in "Hpc".

    (* ---- 0x7d6 ---- *)
    destruct (uv_stack_slot_moi pt N8 sp0 96 88
                (mword_of_int (uint sp0 - 96 + 88)) Hs8 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu9 & (wst9 & Hl9 & Hok9 & _) & Hcan9 & Hpg9 &
          Hal9 & Hby9).
    iApply (wp_uv_sd C pt Pinit N8 p2 (mword_of_int 0x7d6)
              (mword_of_int 56 : mword 12) (mword_of_int 8 : mword 5)
              (mword_of_int 17 : mword 5) wst9
              (mword_of_int (uint sp0 - 96 + 88)) (m !!! Regidx (mword_of_int 17 : mword 5))
              (ui_init_7d6 pt N8 (ilay_text pt Hlay) (init_img_text N8 Ht8))
              ltac:(rewrite Hs0p2; rewrite Hb56; rewrite moi_add;
                    f_equal; lia)
              ltac:(rewrite Hp2r17; reflexivity)
              Hl9 Hok9 Hcan9 Hpg9 Hal9 Hby9
              with "Hcg Hpc").
    iIntros (P11) "Hcg Hpc".
    iEval (rewrite Hu9) in "Hcg".
    set (N9 := uM_store8 N8 (uint sp0 - 96 + 88) (m !!! Regidx (mword_of_int 17 : mword 5))).
    assert (Ho9 : uM_only N8 N9 (uint sp0 - 96) 96)
      by (rewrite /N9; apply uM_only_store8; lia).
    assert (Hot9 : uM_only N8 N9 (uint sp0 - 96 + 88) 8)
      by (rewrite /N9; apply uM_only_store8; lia).
    assert (Hacc9 : uM_only M N9 (uint sp0 - 96) 96) by exact (uM_only_trans M N8 N9 (uint sp0 - 96) 96 Hacc8 Ho9).
    assert (Ht9 : init_img_sub N9)
      by exact (init_img_only N8 N9 (uint sp0 - 96) 96 ltac:(lia) Ho9 Ht8).
    assert (Hs9 : uv_stack pt N9 sp0 96)
      by exact (uM_only_stack pt N8 N9 sp0 96 (uint sp0 - 96) 96 Ho9 Hs8).
    assert (E7d6 : add_vec_int (mword_of_int 0x7d6 : mword 64) 4
                   = mword_of_int 0x7da)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7d6) in "Hpc".

    (* ---- 0x7da  addi a2,s0,8   (va_start) ---- *)
    assert (Hw7da : (mword_of_int (uint sp0 - 56) : mword 64)
                    = add_vec (p2 !!! Regidx (mword_of_int 8 : mword 5))
                        (sign_extend' 64 (mword_of_int 8 : mword 12))).
    { assert (Hcst : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                     = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hs0p2. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Pinit N9 p2 (mword_of_int 0x7da)
              (mword_of_int 8 : mword 12) (mword_of_int 8 : mword 5)
              (mword_of_int 12 : mword 5) (mword_of_int (uint sp0 - 56))
              (ui_init_7da pt N9 (ilay_text pt Hlay) (init_img_text N9 Ht9))
              ltac:(vm_compute; discriminate) Hw7da
              with "Hcg Hpc").
    iIntros (P12) "Hcg Hpc".
    set (p3 := <[Regidx (mword_of_int 12 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0 - 56) : mword 64)]> p2).
    assert (Hs0p3 : p3 !!! Regidx (mword_of_int 8 : mword 5)
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (eq_trans (upd_ne p2 (Regidx (mword_of_int 12 : mword 5))
                            (Regidx (mword_of_int 8 : mword 5)) _
                            ltac:(vm_compute; discriminate)) Hs0p2).
    assert (Hp3r12 : p3 !!! Regidx (mword_of_int 12 : mword 5)
                     = (mword_of_int (uint sp0 - 56) : mword 64))
      by exact (upd_eq p2 (Regidx (mword_of_int 12 : mword 5)) _).
    assert (E7da : add_vec_int (mword_of_int 0x7da : mword 64) 4
                   = mword_of_int 0x7de)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7da) in "Hpc".

    (* ---- 0x7de  sd a2,-24(s0) ---- *)
    destruct (uv_stack_slot_moi pt N9 sp0 96 8
                (mword_of_int (uint sp0 - 96 + 8)) Hs9 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) eq_refl)
      as (Hu10 & (wst10 & Hl10 & Hok10 & _) & Hcan10 & Hpg10 & Hal10 & Hby10).
    iApply (wp_uv_sd C pt Pinit N9 p3 (mword_of_int 0x7de)
              (mword_of_int 4072 : mword 12) (mword_of_int 8 : mword 5)
              (mword_of_int 12 : mword 5) wst10
              (mword_of_int (uint sp0 - 96 + 8))
              (mword_of_int (uint sp0 - 56))
              (ui_init_7de pt N9 (ilay_text pt Hlay) (init_img_text N9 Ht9))
              ltac:(rewrite Hs0p3; rewrite Hb4072; rewrite moi_add; f_equal; lia)
              ltac:(rewrite Hp3r12; reflexivity)
              Hl10 Hok10 Hcan10 Hpg10 Hal10 Hby10
              with "Hcg Hpc").
    iIntros (P13) "Hcg Hpc".
    iEval (rewrite Hu10) in "Hcg".
    set (N10 := uM_store8 N9 (uint sp0 - 96 + 8) (mword_of_int (uint sp0 - 56))).
    assert (Ho10 : uM_only N9 N10 (uint sp0 - 96) 96)
      by (rewrite /N10; apply uM_only_store8; lia).
    assert (Hot10 : uM_only N9 N10 (uint sp0 - 96 + 8) 8)
      by (rewrite /N10; apply uM_only_store8; lia).
    assert (Hacc10 : uM_only M N10 (uint sp0 - 96) 96)
      by exact (uM_only_trans M N9 N10 (uint sp0 - 96) 96 Hacc9 Ho10).
    assert (Ht10 : init_img_sub N10)
      by exact (init_img_only N9 N10 (uint sp0 - 96) 96 ltac:(lia) Ho10 Ht9).
    assert (Hs10 : uv_stack pt N10 sp0 96)
      by exact (uM_only_stack pt N9 N10 sp0 96 (uint sp0 - 96) 96 Ho10 Hs9).
    assert (E7de : add_vec_int (mword_of_int 0x7de : mword 64) 4
                   = mword_of_int 0x7e2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7de) in "Hpc".

    (* ---- 0x7e2  mv a1,a0 ---- *)
    assert (Hp3a0 : p3 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { refine (eq_trans (upd_ne p2 (Regidx (mword_of_int 12 : mword 5))
                          (Regidx a0_idx) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5))
                          (Regidx a0_idx) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m (Regidx csp_rs1)
                          (Regidx a0_idx) _ ltac:(vm_compute; discriminate)) _).
      exact Hfmt. }
    iApply (wp_uv_cmv C pt Pinit N10 p3 (mword_of_int 0x7e2)
              (mword_of_int 11 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int s)
              (ui_init_7e2 pt N10 (ilay_text pt Hlay) (init_img_text N10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite add_vec_zero_l; rewrite Hp3a0; reflexivity)
              with "Hcg Hpc").
    iIntros (P14) "Hcg Hpc".
    set (p4 := <[Regidx (mword_of_int 11 : mword 5)
                 := regval_into_reg (mword_of_int s : mword 64)]> p3).
    assert (E7e2 : add_vec_int (mword_of_int 0x7e2 : mword 64) 2
                   = mword_of_int 0x7e4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7e2) in "Hpc".

    (* ---- 0x7e4  li a0,1   (fd 1) ---- *)
    iApply (wp_uv_cli C pt Pinit N10 p4 (mword_of_int 0x7e4)
              (mword_of_int 1 : mword 6) (mword_of_int 10 : mword 5)
              (mword_of_int 1)
              (ui_init_7e4 pt N10 (ilay_text pt Hlay) (init_img_text N10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (P15) "Hcg Hpc".
    set (p5 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (mword_of_int 1 : mword 64)]> p4).
    assert (E7e4 : add_vec_int (mword_of_int 0x7e4 : mword 64) 2
                   = mword_of_int 0x7e6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7e4) in "Hpc".

    (* ---- 0x7e6  jal vprintf ---- *)
    iApply (wp_uv_jal C pt Pinit N10 p5 (mword_of_int 0x7e6)
              (mword_of_int 2096368 : mword 21) ra_idx
              (mword_of_int 0x4d6) (mword_of_int 0x7ea)
              (ui_init_7e6 pt N10 (ilay_text pt Hlay) (init_img_text N10 Ht10))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (P16) "Hcg Hpc".
    set (p6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x7ea : mword 64)]> p5).
    iEval (change (mword_of_int 0x4d6 : mword 64)
             with (mword_of_int InitSyms.vprintf : mword 64)) in "Hpc".

    (* ---- vprintf(1, fmt, ap) ---- *)
    assert (Hp6sp : p6 !!! Regidx sp_idx = (mword_of_int (uint sp0 - 96) : mword 64)).
    { refine (eq_trans (upd_ne p5 (Regidx ra_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne p4 (Regidx (mword_of_int 10 : mword 5))
                          (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne p3 (Regidx (mword_of_int 11 : mword 5))
                          (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne p2 (Regidx (mword_of_int 12 : mword 5))
                          (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5))
                          (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) _).
      exact Hspp1. }
    assert (Hp6a1 : p6 !!! Regidx a1_idx = (mword_of_int s : mword 64)).
    { refine (eq_trans (upd_ne p5 (Regidx ra_idx) (Regidx a1_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne p4 (Regidx (mword_of_int 10 : mword 5))
                          (Regidx a1_idx) _ ltac:(vm_compute; discriminate)) _).
      exact (upd_eq p3 (Regidx (mword_of_int 11 : mword 5))
               (regval_into_reg (mword_of_int s : mword 64))). }
    assert (Hp6a0 : p6 !!! Regidx a0_idx = (mword_of_int 1 : mword 64))
      by exact (eq_trans (upd_ne p5 (Regidx ra_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate))
                         (upd_eq p4 (Regidx (mword_of_int 10 : mword 5))
                            (regval_into_reg (mword_of_int 1 : mword 64)))).
    assert (Hp6ra : p6 !!! Regidx ra_idx = (mword_of_int 0x7ea : mword 64))
      by exact (upd_eq p5 (Regidx ra_idx) _).
    assert (Hs128' : uv_stack pt N10 (mword_of_int (uint sp0 - 96)) 128)
      by exact (uM_only_stack pt M N10 (mword_of_int (uint sp0 - 96)) 128
                  (uint sp0 - 96) 96
                  (uM_only_widen M N10 (uint sp0 - 96) 96 (uint sp0 - 96) 96
                     Hacc10 ltac:(lia) ltac:(lia)) Hs128).
    assert (Hlit10 : init_lit N10 s bs)
      by exact (init_lit_only M N10 (uint sp0 - 96) 96 s bs ltac:(lia) Hacc10 Hlit).
    iApply (wp_init_vprintf P16 N10 p6 (mword_of_int (uint sp0 - 96)) s bs
              Hlay Ht10 Hp6sp Hs128'
              ltac:(unfold init_frame_ok; rewrite Husp; lia)
              Hp6a1 Hlit10
              ltac:(rewrite Hp6ra; vm_compute; reflexivity)
              with "Hcg [] Hpc [Hcont]").
    { rewrite Hp6a0. rewrite (uint_moi 1 ltac:(unfold Z64; lia)). iExact "Hwobs". }
    iIntros (P17 pv Nv) "%Hcsv %Hov0 Hcg Hpc".
    rewrite Husp in Hov0.
    assert (Hov : uM_only N10 Nv (uint sp0 - 224) 128)
      by (replace (uint sp0 - 224) with (uint sp0 - 96 - 128) by lia; exact Hov0).
    iEval (rewrite Hp6ra) in "Hpc".
    assert (Hfra : uM_bytes Nv (uint sp0 - 96 + 24) 8 (m !!! Regidx ra_idx)).
    { apply (uM_bytes_only N10 Nv (uint sp0 - 96 + 24) (uint sp0 - 224) 128 8);
        [ exact Hov | lia | ].
      apply (uM_bytes_only N9 N10 (uint sp0 - 96 + 24) (uint sp0 - 96 + 8) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only N8 N9 (uint sp0 - 96 + 24) (uint sp0 - 96 + 88) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only N7 N8 (uint sp0 - 96 + 24) (uint sp0 - 96 + 80) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only N6 N7 (uint sp0 - 96 + 24) (uint sp0 - 96 + 72) 8 8);
        [ exact Hot7 | lia | ].
      apply (uM_bytes_only N5 N6 (uint sp0 - 96 + 24) (uint sp0 - 96 + 64) 8 8);
        [ exact Hot6 | lia | ].
      apply (uM_bytes_only N4 N5 (uint sp0 - 96 + 24) (uint sp0 - 96 + 56) 8 8);
        [ exact Hot5 | lia | ].
      apply (uM_bytes_only N3 N4 (uint sp0 - 96 + 24) (uint sp0 - 96 + 48) 8 8);
        [ exact Hot4 | lia | ].
      apply (uM_bytes_only N2 N3 (uint sp0 - 96 + 24) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot3 | lia | ].
      apply (uM_bytes_only N1 N2 (uint sp0 - 96 + 24) (uint sp0 - 96 + 16) 8 8);
        [ exact Hot2 | lia | ].
      rewrite /N1. exact (uM_store8_bytes M (uint sp0 - 96 + 24) _). }
    assert (Hfs0 : uM_bytes Nv (uint sp0 - 96 + 16) 8 (m !!! Regidx (mword_of_int 8 : mword 5))).
    { apply (uM_bytes_only N10 Nv (uint sp0 - 96 + 16) (uint sp0 - 224) 128 8);
        [ exact Hov | lia | ].
      apply (uM_bytes_only N9 N10 (uint sp0 - 96 + 16) (uint sp0 - 96 + 8) 8 8);
        [ exact Hot10 | lia | ].
      apply (uM_bytes_only N8 N9 (uint sp0 - 96 + 16) (uint sp0 - 96 + 88) 8 8);
        [ exact Hot9 | lia | ].
      apply (uM_bytes_only N7 N8 (uint sp0 - 96 + 16) (uint sp0 - 96 + 80) 8 8);
        [ exact Hot8 | lia | ].
      apply (uM_bytes_only N6 N7 (uint sp0 - 96 + 16) (uint sp0 - 96 + 72) 8 8);
        [ exact Hot7 | lia | ].
      apply (uM_bytes_only N5 N6 (uint sp0 - 96 + 16) (uint sp0 - 96 + 64) 8 8);
        [ exact Hot6 | lia | ].
      apply (uM_bytes_only N4 N5 (uint sp0 - 96 + 16) (uint sp0 - 96 + 56) 8 8);
        [ exact Hot5 | lia | ].
      apply (uM_bytes_only N3 N4 (uint sp0 - 96 + 16) (uint sp0 - 96 + 48) 8 8);
        [ exact Hot4 | lia | ].
      apply (uM_bytes_only N2 N3 (uint sp0 - 96 + 16) (uint sp0 - 96 + 40) 8 8);
        [ exact Hot3 | lia | ].
      rewrite /N2. exact (uM_store8_bytes N1 (uint sp0 - 96 + 16) _). }
    assert (Hpvsp : pv !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (Hcsv (mword_of_int 2 : mword 5)
                            ltac:(vm_compute; reflexivity)) Hp6sp).
    assert (Htv : init_img_sub Nv)
      by exact (init_img_only N10 Nv (uint sp0 - 224) 128 ltac:(lia) Hov Ht10).
    assert (Hsv : uv_stack pt Nv sp0 96)
      by exact (uM_only_stack pt N10 Nv sp0 96 (uint sp0 - 224) 128 Hov Hs10).

    (* ---- 0x7ea  c.ldsp ra,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt P17 Pinit Nv pv sp0 (mword_of_int 0x7ea)
              (mword_of_int 3 : mword 6) ra_idx 96 24 (m !!! Regidx ra_idx)
              (ui_init_7ea pt Nv (ilay_text pt Hlay) (init_img_text Nv Htv))
              ltac:(vm_compute; discriminate) Hsv
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hpvsp
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Nv (uint sp0 - 96 + 24) _ Hfra))
              with "Hcg Hpc").
    iIntros (P18) "Hcg Hpc".
    set (r1 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> pv).
    assert (Hr1sp : r1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne pv (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hpvsp).
    assert (E7ea : add_vec_int (mword_of_int 0x7ea : mword 64) 2
                   = mword_of_int 0x7ec)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7ea) in "Hpc".

    (* ---- 0x7ec  c.ldsp s0,16(sp) ---- *)
    iApply (wp_uv_frame_load C pt P18 Pinit Nv r1 sp0 (mword_of_int 0x7ec)
              (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5) 96 16
              (m !!! Regidx (mword_of_int 8 : mword 5))
              (ui_init_7ec pt Nv (ilay_text pt Hlay) (init_img_text Nv Htv))
              ltac:(vm_compute; discriminate) Hsv
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hr1sp
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 Nv (uint sp0 - 96 + 16) _ Hfs0))
              with "Hcg Hpc").
    iIntros (P19) "Hcg Hpc".
    set (r2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> r1).
    assert (Hr2sp : r2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (eq_trans (upd_ne r1 (Regidx (mword_of_int 8 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate)) Hr1sp).
    assert (E7ec : add_vec_int (mword_of_int 0x7ec : mword 64) 2
                   = mword_of_int 0x7ee)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7ec) in "Hpc".

    (* ---- 0x7ee  c.addi16sp sp,sp,96 ---- *)
    assert (Hw7ee : (mword_of_int (uint sp0) : mword 64)
                    = add_vec (r2 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))
                      : mword 64) = mword_of_int 96)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hr2sp. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Pinit Nv r2 (mword_of_int 0x7ee)
              (mword_of_int 6 : mword 6) (mword_of_int (uint sp0))
              (ui_init_7ee pt Nv (ilay_text pt Hlay) (init_img_text Nv Htv)) Hw7ee
              with "Hcg Hpc").
    iIntros (P20) "Hcg Hpc".
    set (r3 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> r2).
    assert (E7ee : add_vec_int (mword_of_int 0x7ee : mword 64) 2
                   = mword_of_int 0x7f0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7ee) in "Hpc".

    (* ---- 0x7f0  c.jr ra ---- *)
    assert (Hr3ra : r3 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { refine (eq_trans (upd_ne r2 (Regidx csp_rs1) (Regidx ra_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne r1 (Regidx (mword_of_int 8 : mword 5))
                          (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) _).
      exact (upd_eq pv (Regidx ra_idx) (regval_into_reg (m !!! Regidx ra_idx))). }
    iApply (wp_uv_cjr C pt Pinit Nv r3 (mword_of_int 0x7f0)
              ra_idx (m !!! Regidx ra_idx)
              (ui_init_7f0 pt Nv (ilay_text pt Hlay) (init_img_text Nv Htv))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hr3ra; unfold ret_pc; symmetry;
                    exact (update_bit0_zero_of_aligned2 _ Hret2))
              with "Hcg Hpc").
    iIntros (P21) "Hcg Hpc".
    iApply ("Hcont" $! P21 r3 Nv with "[] [] Hcg Hpc").
    - iPureIntro. intros r Hr.
      assert (Hne : forall kz : Z,
                ucallee_saved_idx (mword_of_int kz : mword 5) = false ->
                Regidx r <> Regidx (mword_of_int kz : mword 5)).
      { intros kz Hkz Heq. injection Heq as Heq'.
        rewrite Heq' in Hr. rewrite Hkz in Hr. discriminate. }
      destruct (decide (r = (mword_of_int 2 : mword 5))) as [ -> | Hd2 ].
      { transitivity (mword_of_int (uint sp0) : mword 64).
        - exact (upd_eq r2 (Regidx csp_rs1)
                   (regval_into_reg (mword_of_int (uint sp0) : mword 64))).
        - rewrite <- Hsp. exact (moi_of_uint _). }
      destruct (decide (r = (mword_of_int 8 : mword 5))) as [ -> | Hd8 ].
      { refine (eq_trans (upd_ne r2 (Regidx csp_rs1)
                            (Regidx (mword_of_int 8 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq r1 (Regidx (mword_of_int 8 : mword 5))
                 (regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5)))). }
      assert (Hn2 : Regidx r <> Regidx (mword_of_int 2 : mword 5))
        by (intro He; apply Hd2; injection He; auto).
      assert (Hn8 : Regidx r <> Regidx (mword_of_int 8 : mword 5))
        by (intro He; apply Hd8; injection He; auto).
      rewrite (upd_ne r2 (Regidx csp_rs1) (Regidx r) _ Hn2).
      rewrite (upd_ne r1 (Regidx (mword_of_int 8 : mword 5)) (Regidx r) _ Hn8).
      rewrite (upd_ne pv (Regidx ra_idx) (Regidx r) _
                 (Hne 1 ltac:(vm_compute; reflexivity))).
      rewrite (Hcsv r Hr).
      rewrite (upd_ne p5 (Regidx ra_idx) (Regidx r) _
                 (Hne 1 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne p4 (Regidx (mword_of_int 10 : mword 5)) (Regidx r) _
                 (Hne 10 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne p3 (Regidx (mword_of_int 11 : mword 5)) (Regidx r) _
                 (Hne 11 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne p2 (Regidx (mword_of_int 12 : mword 5)) (Regidx r) _
                 (Hne 12 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne p1 (Regidx (mword_of_int 8 : mword 5)) (Regidx r) _ Hn8).
      exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hn2).
    - iPureIntro.
      refine (uM_only_trans M N10 Nv (uint sp0 - 224) 224
                (uM_only_widen M N10 (uint sp0 - 96) 96 (uint sp0 - 224) 224
                   Hacc10 ltac:(lia) ltac:(lia))
                (uM_only_widen N10 Nv (uint sp0 - 224) 128 (uint sp0 - 224) 224
                   Hov ltac:(lia) ltac:(lia))).
  Qed.

End UProofInitPrintf.
