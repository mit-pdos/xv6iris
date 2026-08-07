(* UProofSync.v -- the VERIFIED-EXECUTION proofs of the four functions of
   the `sync` user program (claude-notes/projects/user-verified.md).  Each
   lemma discharges one contract of USpecSync.v, in dependency order:

     wp_sync_exit_stub   exit  @0x2c8   c.li a7,2;  ecall            (diverges)
     wp_sync_sync_stub   sync  @0x368   c.li a7,22; ecall; c.jr ra   (returns)
     wp_sync_main        main  @0x0     prologue; jal sync; li a0,0; jal exit
     wp_sync_start       start @0x12    prologue; jal main; (jal exit is dead)

   Every instruction is one application of a leaf from WpUmodeLeaf.v (or the
   store leaf of WpUmodeStore.v), fed the matching [ui_sync_<off>] fact from
   UCodeSync.v.  Every leaf continuation re-binds the hart ([∀ CID]): a user
   process can be preempted at any instruction and resumed on another hart. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import AlignBits UserBits.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeSyscall UmodeFetch.
Require Import WpUmodeStep WpUmodeLeaf WpUmodeStore.
Require Import UCodeSync USpecSync.
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 Pure arithmetic helpers.                                            *)
(*                                                                        *)
(* Everything here is stated over PLAIN [Z] variables (or over a single    *)
(* [mword] with the bitvector reading taken immediately), because [lia]    *)
(* is unusable on a goal mentioning [bv_unsigned] under this file's        *)
(* import set (durable-notes: the [bitvector.tactics] zify hook).          *)
(* ===================================================================== *)

(* a 16-aligned page offset leaves at least 4080-r room: this is what makes *)
(* both stack slots' 4-byte/8-byte windows sit on ONE page.                 *)
Lemma z_mod4096_of_mod16 (V r : Z) :
  0 <= V -> 0 <= r < 16 -> V mod 16 = r -> V mod 4096 <= 4080 + r.
Proof.
  intros HV Hr Hm.
  assert (Hd : (16 | 4096)) by (exists 256; reflexivity).
  pose proof (Znumtheory.Zmod_div_mod 16 4096 V ltac:(lia) ltac:(lia) Hd) as Hq.
  pose proof (Z.mod_pos_bound V 4096 ltac:(lia)) as Hb.
  pose proof (Z.div_mod (V mod 4096) 16 ltac:(lia)) as Hdm.
  rewrite <- Hq in Hdm. rewrite Hm in Hdm. lia.
Qed.

(* Sv39 canonicality of any address below 2^38 (the [uv_frame16] bound). *)
Lemma z_canon_small (V : Z) :
  0 <= V < 274877906944 ->
  V = (((V mod 549755813888 + 274877906944) mod 549755813888) - 274877906944)
        mod 18446744073709551616.
Proof.
  intro HV.
  rewrite (Z.mod_small V 549755813888 ltac:(lia)).
  rewrite (Z.mod_small (V + 274877906944) 549755813888 ltac:(lia)).
  replace (V + 274877906944 - 274877906944) with V by lia.
  rewrite (Z.mod_small V 18446744073709551616 ltac:(lia)). reflexivity.
Qed.

Lemma uva_canon_small (a : mword 64) :
  bv_unsigned a < 274877906944 -> uva_canon a.
Proof.
  intro Hlt.
  pose proof (proj1 (bv_unsigned_in_range _ a)) as Hlo.
  apply uva_canon_unsigned.
  unfold bv_swrap, bv_wrap.
  assert (E39 : bv_modulus 39 = 549755813888) by (vm_compute; reflexivity).
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Eh39 : bv_half_modulus 39 = 274877906944) by (vm_compute; reflexivity).
  rewrite E39 E64 Eh39.
  exact (z_canon_small (bv_unsigned a) (conj Hlo Hlt)).
Qed.

(* a NEGATIVE 64-bit displacement, as unsigned arithmetic (the [add_vec_int]
   twin of UserBits' [uint_add_vec_int_small]) *)
Lemma uv_avi_neg (a : mword 64) (d : Z) :
  0 <= d -> d <= bv_unsigned a ->
  bv_unsigned (add_vec_int a (- d)) = bv_unsigned a - d.
Proof.
  intros Hd Hle.
  unfold add_vec_int.
  rewrite add_vec64_unsigned moi64_unsigned.
  unfold bv_wrap.
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite E64.
  rewrite Zplus_mod_idemp_r.
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ a) as Hr. rewrite E64 in Hr. lia.
Qed.

Lemma z_mod8_of_mod16 (V r : Z) :
  0 <= V -> (r = 0 \/ r = 8) -> V mod 16 = r -> V mod 8 = 0.
Proof.
  intros HV Hr Hm.
  assert (Hd : (8 | 16)) by (exists 2; reflexivity).
  rewrite (Znumtheory.Zmod_div_mod 8 16 V ltac:(lia) ltac:(lia) Hd).
  rewrite Hm. destruct Hr as [ -> | -> ]; reflexivity.
Qed.

(* THE pure-Z package behind every stack-slot side condition: with sp0
   16-aligned, the slot at sp0-16+d (d = 0 or 8) is 8-aligned, sits inside
   one page, and leaves the whole 8-byte window on that page. *)
Lemma frame_slot_arith (U d : Z) :
  0 <= U -> 4096 + 16 <= U -> U mod 16 = 0 -> (d = 0 \/ d = 8) ->
  (U - 16 + d) mod 4096 <= 4080 + d /\
  (U - 16 + d) mod 8 = 0 /\
  (U - 16) mod 4096 + d < 4096.
Proof.
  intros HU0 HUlo HU16 Hd.
  assert (Hdr : (U - 16 + d) mod 16 = d).
  { replace (U - 16 + d) with (U + (d - 16)) by lia.
    rewrite Zplus_mod. rewrite HU16. destruct Hd as [ -> | -> ]; reflexivity. }
  assert (Hz : (U - 16) mod 16 = 0).
  { replace (U - 16) with (U + (0 - 16)) by lia.
    rewrite Zplus_mod. rewrite HU16. reflexivity. }
  split_and!.
  - apply (z_mod4096_of_mod16 (U - 16 + d) d); [ lia | destruct Hd; lia | exact Hdr ].
  - apply (z_mod8_of_mod16 (U - 16 + d) d); [ lia | exact Hd | exact Hdr ].
  - pose proof (z_mod4096_of_mod16 (U - 16) 0 ltac:(lia) ltac:(lia) Hz). lia.
Qed.

(* a 64-bit fit bound, mword-free (so [lia] never meets a [bv_unsigned]) *)
Lemma z_fit64 (A d : Z) :
  0 <= A < 18446744073709551616 -> 16 <= A -> 0 <= d <= 8 ->
  A - 16 + d < 18446744073709551616.
Proof. lia. Qed.

Lemma z_canon_slot (A d C : Z) : A < C -> 16 <= A -> 0 <= d <= 8 -> A - 16 + d < C.
Proof. lia. Qed.

(* the address of the slot at sp0-16+d, as unsigned arithmetic *)
Lemma uv_slot_unsigned (sp0 : mword 64) (d : Z) :
  16 <= bv_unsigned sp0 -> 0 <= d <= 8 ->
  bv_unsigned (add_vec_int (add_vec_int sp0 (-16)) d) = bv_unsigned sp0 - 16 + d.
Proof.
  intros Hlo Hd.
  pose proof (bv_unsigned_in_range _ sp0) as Hrng.
  assert (Em64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Em64 in Hrng.
  pose proof (uv_avi_neg sp0 16 ltac:(lia) Hlo) as H1.
  rewrite (uint_add_vec_int_small (add_vec_int sp0 (-16)) d ltac:(lia)
             ltac:(rewrite H1; exact (z_fit64 _ d Hrng Hlo Hd))).
  rewrite H1. reflexivity.
Qed.

(* ===================================================================== *)
(* §1 The image is only ever written ABOVE the text.                      *)
(* ===================================================================== *)

Lemma list_key_lt {A : Type} (L : list (Z * A)) (B k : Z) (b : A) :
  forallb (fun kv => Z.ltb (fst kv) B) L = true -> In (k, b) L -> k < B.
Proof.
  induction L as [ | x xs IH ]; cbn [forallb In]; [ tauto | ].
  intros HF [ Hx | Hin ].
  - apply andb_prop in HF as [ H1 _ ]. subst x. cbn in H1.
    apply Z.ltb_lt in H1. exact H1.
  - apply andb_prop in HF as [ _ H2 ]. exact (IH H2 Hin).
Qed.

(* every byte of the dumped text sits on page 0 (the image is 0x0..0x8c0) *)
Lemma sync_bytes_key_lt (k : Z) (b : bv 8) :
  SyncInstrs.sync_bytes !! k = Some b -> k < 4096.
Proof.
  intro Hk.
  apply elem_of_list_to_map_2 in Hk.
  apply elem_of_list_In in Hk.
  refine (list_key_lt _ 4096 k b _ Hk).
  vm_compute. reflexivity.
Qed.

(* an 8-byte store ABOVE the text preserves the text inclusion *)
Lemma sync_text_sub_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sync_text_sub M -> 4096 <= a -> sync_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sync_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

(* ===================================================================== *)
(* §1b The two stack slots of a 16-byte frame, as store-leaf premises.     *)
(*                                                                        *)
(* [wp_uv_csdsp] wants, for its target va: the page mapped store-          *)
(* permitting, canonicality, 8-alignment, the whole 8-byte window on one   *)
(* page, and the bytes present in the image.  A [uv_frame16] window gives  *)
(* all five for the slot at [sp0-16+d] with d = 0 (the s0 slot) and d = 8  *)
(* (the ra slot) -- one lemma, both call sites, both prologues.            *)
(* ===================================================================== *)

Lemma frame_slot_facts (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64) (d : Z) :
  uv_frame16 pt M sp0 -> (d = 0 \/ d = 8) ->
  let tgt := add_vec_int (add_vec_int sp0 (-16)) d in
  uint tgt = uint sp0 - 16 + d /\
  (exists w_st : mword 64,
     ud_um pt !! svpn_of tgt = Some w_st /\ uleaf_ok (Store Data) w_st) /\
  uva_canon tgt /\
  Z.rem (uint tgt) 4096 <= 4088 /\
  is_aligned_vaddr (Virtaddr tgt) 8 = true /\
  (forall j : nat, (j < 8)%nat ->
     exists b : bv 8, M !! (uint tgt + Z.of_nat j) = Some b).
Proof.
  intros [Hfb Hfl Hfal Hflo Hfcanon] Hd tgt.
  pose proof (bv_unsigned_in_range _ sp0) as Hrng.
  assert (Em64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Em64 in Hrng.
  rewrite !uint_unsigned in Hfb Hfal Hflo Hfcanon.
  rewrite Z.rem_mod_nonneg in Hfal; [ | exact (proj1 Hrng) | lia ].
  assert (Hd08 : 0 <= d <= 8) by (destruct Hd; lia).
  assert (Hlo16 : 16 <= bv_unsigned sp0) by lia.
  (* the address of the slot *)
  assert (Htu : bv_unsigned tgt = bv_unsigned sp0 - 16 + d)
    by (unfold tgt; exact (uv_slot_unsigned sp0 d Hlo16 Hd08)).
  destruct (frame_slot_arith (bv_unsigned sp0) d (proj1 Hrng) Hflo Hfal Hd)
    as (Apg & Aal & Awin).
  (* the leaf: the slot is on the same page as sp0-16 *)
  pose proof (uv_avi_neg sp0 16 ltac:(lia) Hlo16) as Hsp1u.
  assert (Hleaf : svpn_of tgt = svpn_of (add_vec_int sp0 (-16))).
  { unfold tgt.
    apply (usvpn_window (add_vec_int sp0 (-16)) d ltac:(lia)).
    rewrite Hsp1u. exact Awin. }
  split_and!.
  - rewrite !uint_unsigned. exact Htu.
  - destruct Hfl as (w & Hw & Hok). exists w. rewrite Hleaf. split; assumption.
  - apply uva_canon_small. rewrite Htu.
    exact (z_canon_slot _ d 274877906944 Hfcanon Hlo16 Hd08).
  - rewrite uint_unsigned Htu.
    rewrite Z.rem_mod_nonneg; [ | lia | lia ]. lia.
  - unfold is_aligned_vaddr. apply Z.eqb_eq.
    rewrite uint_unsigned Htu.
    rewrite Z.rem_mod_nonneg; [ exact Aal | lia | lia ].
  - intros j Hj. rewrite uint_unsigned Htu.
    destruct Hd as [ -> | -> ].
    + destruct (Hfb j ltac:(lia)) as (b & Hb). exists b.
      replace (bv_unsigned sp0 - 16 + 0 + Z.of_nat j)
        with (bv_unsigned sp0 - 16 + Z.of_nat j) by lia.
      exact Hb.
    + destruct (Hfb (8 + j)%nat ltac:(lia)) as (b & Hb). exists b.
      replace (bv_unsigned sp0 - 16 + 8 + Z.of_nat j)
        with (bv_unsigned sp0 - 16 + Z.of_nat (8 + j)%nat)
        by (rewrite Nat2Z.inj_add; lia).
      exact Hb.
Qed.

(* ===================================================================== *)
(* §2 The four function proofs.                                           *)
(* ===================================================================== *)

Section UProofSync.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  Local Notation Ψxv6 := (xv6_sys_protocol C pt).

  (* ------------------------------------------------------------------- *)
  (* exit @0x2c8: c.li a7,2; ecall.  The ecall's protocol payload is the   *)
  (* [UsysNoRet] arm ([emp]) -- the syscall never comes back, so the WP is *)
  (* absorbed and there is nothing after it.                               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sync_exit_stub (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (Φ : mval -> iProp Σ) :
    wp_exit_stub_body (CID := CIDp) C pt M m Φ.
  Proof.
    intros Hlay Htext.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    iIntros "Hcg Hpc".
    iEval (rewrite Hsexit) in "Hpc".
    (* 0x2c8  c.li a7,2 *)
    assert (Hw2 : (mword_of_int 2 : mword 64)
                  = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Ψxv6 M m (mword_of_int 0x2c8)
              (mword_of_int 2 : mword 6) a7_idx (mword_of_int 2 : mword 64) Φ
              (ui_sync_2c8 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hw2
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx a7_idx := regval_into_reg (mword_of_int 2 : mword 64)]> m).
    assert (Epc : add_vec_int (mword_of_int 0x2c8 : mword 64) 2 = mword_of_int 0x2ca)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Epc) in "Hpc".
    (* 0x2ca  ecall *)
    assert (Ha7 : uint (m1 !!! Regidx a7_idx) = 2)
      by (rewrite /m1; reg_lookup).
    iApply (wp_uv_ecall C pt Ψxv6 M m1 (mword_of_int 0x2ca) Φ
              (ui_sync_2ca pt M Hlay Htext) with "Hcg Hpc").
    rewrite /xv6_sys_protocol /usys_protocol_of.
    rewrite Ha7.
    change (xv6_sys_sem 2) with UsysNoRet.
    cbn [usys_arm]. done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sync @0x368: c.li a7,22; ecall; c.jr ra.  The ecall's payload is the  *)
  (* [UsysPureRet] arm, whose resume continuation comes back at pc+4 with  *)
  (* a0 set to an arbitrary value on an arbitrary hart; the c.jr then      *)
  (* returns to the caller's ra (2-aligned, so [ret_pc] is the identity).  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sync_sync_stub (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (Φ : mval -> iProp Σ) :
    wp_sync_stub_body (CID := CIDp) C pt M m Φ.
  Proof.
    intros Hlay Htext Hret2.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hssync) in "Hpc".
    (* the capability is persistent: keep a copy for the post-syscall repack *)
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgpr)".
    iAssert (uv_cap_gpr C pt Ψxv6 M m) with "[Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    (* 0x368  c.li a7,22 *)
    assert (Hw22 : (mword_of_int 22 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 22 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Ψxv6 M m (mword_of_int 0x368)
              (mword_of_int 22 : mword 6) a7_idx (mword_of_int 22 : mword 64) Φ
              (ui_sync_368 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hw22
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    (* the leaf's [regval_into_reg] wrapper is the identity: normalize the
       stored value NOW, before any further insert is stacked on it *)
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int 22 : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m)
      by reflexivity.
    iEval (rewrite Hnorm) in "Hcg".
    set (m1 := <[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m).
    assert (Epc1 : add_vec_int (mword_of_int 0x368 : mword 64) 2 = mword_of_int 0x36a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Epc1) in "Hpc".
    (* 0x36a  ecall -- SYS_sync, the returning arm *)
    assert (Ha7 : uint (m1 !!! Regidx a7_idx) = 22) by (rewrite /m1; reg_lookup).
    iApply (wp_uv_ecall C pt Ψxv6 M m1 (mword_of_int 0x36a) Φ
              (ui_sync_36a pt M Hlay Htext) with "Hcg Hpc").
    rewrite /xv6_sys_protocol /usys_protocol_of.
    rewrite Ha7.
    change (xv6_sys_sem 22) with UsysPureRet.
    cbn [usys_arm].
    iIntros (CID2 ret) "Hrun".
    assert (Epc2 : add_vec_int (mword_of_int 0x36a : mword 64) 4 = mword_of_int 0x36e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Epc2) in "Hrun".
    iDestruct (uv_run_cap_gpr (CID := CID2) C pt Ψxv6 M
                 (<[Regidx a0_idx := ret]> m1) (mword_of_int 0x36e)
                 with "Hcap Hrun") as "[Hcg Hpc]".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* 0x36e  c.jr ra -- neither insert touches ra *)
    assert (Hra2 : m2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx ra_idx).
    { exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx (mword_of_int 1 : mword 5)) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 1 : mword 5))
                  (mword_of_int 22) ltac:(vm_compute; discriminate))). }
    assert (Htgt : (m !!! Regidx ra_idx)
                   = ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))).
    { rewrite Hra2. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Ψxv6 M m2 (mword_of_int 0x36e)
              (mword_of_int 1 : mword 5) (m !!! Regidx ra_idx) Φ
              (ui_sync_36e pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Htgt
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* main @0x0: the gcc prologue (c.addi sp,-16; c.sdsp ra,8(sp);         *)
  (* c.sdsp s0,0(sp); c.addi4spn s0,sp,16), jal sync, c.li a0,0, jal      *)
  (* exit.  DIVERGES -- exit's ecall never returns, so the epilogue at     *)
  (* 0x12.. is dead code and gets no [uinstr] fact.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sync_main (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (Φ : mval -> iProp Σ) :
    wp_sync_main_body (CID := CIDp) C pt M m sp0 Φ.
  Proof.
    intros Hlay Htext Hsp Hfr.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    (* the two 8-byte stack slots, with every store-leaf side condition *)
    destruct (frame_slot_facts pt M sp0 8 Hfr (or_intror eq_refl))
      as (Hu8 & (w8 & Hl8 & Hok8) & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (frame_slot_facts pt M sp0 0 Hfr (or_introl eq_refl))
      as (Hu0 & (w0 & Hl0 & Hok0) & Hcanon0 & Hpg0 & Hal0 & Hb0).
    pose proof Hfr as Hfrc. destruct Hfrc as [ _ _ _ Hflo _ ].
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-16)) 8) = uint sp0 - 8)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-16)) 0) = uint sp0 - 16)
      by (rewrite Hu0; lia).
    iIntros "Hcg Hpc".
    iEval (rewrite Hsmain) in "Hpc".
    (* ---- 0x00  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : add_vec_int sp0 (-16)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uv_caddi C pt Ψxv6 M m (mword_of_int 0x00)
              (mword_of_int 48 : mword 6) sp_idx (add_vec_int sp0 (-16)) Φ
              (ui_sync_00 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (E00 : add_vec_int (mword_of_int 0x00 : mword 64) 2 = mword_of_int 0x02)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E00) in "Hpc".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    (* ---- 0x02  c.sdsp ra,8(sp) ---- *)
    assert (Htg8 : add_vec_int (add_vec_int sp0 (-16)) 8
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hwra : m !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx ra_idx)
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uv_csdsp C pt Ψxv6 M m1 (mword_of_int 0x02)
              (mword_of_int 1 : mword 6) ra_idx
              w8 (add_vec_int (add_vec_int sp0 (-16)) 8) (m !!! Regidx ra_idx) Φ
              (ui_sync_02 pt M Hlay Htext)
              Htg8 Hwra Hl8 Hok8 Hcanon8 Hpg8 Hal8 Hb8
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Hu8') in "Hcg".
    set (M2 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext2 : sync_text_sub M2)
      by (unfold M2; apply sync_text_sub_store8; [ exact Htext | lia ]).
    assert (E02 : add_vec_int (mword_of_int 0x02 : mword 64) 2 = mword_of_int 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E02) in "Hpc".
    (* ---- 0x04  c.sdsp s0,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 0) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb).
      exact (uM_store8_is_Some M (uint sp0 - 8) (m !!! Regidx ra_idx) _
               (mk_is_Some _ _ Hb)). }
    assert (Htg0 : add_vec_int (add_vec_int sp0 (-16)) 0
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : m !!! Regidx (mword_of_int 8 : mword 5)
                   = m1 !!! Regidx (mword_of_int 8 : mword 5))
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx (mword_of_int 8 : mword 5))
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uv_csdsp C pt Ψxv6 M2 m1 (mword_of_int 0x04)
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              w0 (add_vec_int (add_vec_int sp0 (-16)) 0)
              (m !!! Regidx (mword_of_int 8 : mword 5)) Φ
              (ui_sync_04 pt M2 Hlay Htext2)
              Htg0 Hws0 Hl0 Hok0 Hcanon0 Hpg0 Hal0 Hb0'
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite Hu0') in "Hcg".
    set (M3 := uM_store8 M2 (uint sp0 - 16) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Htext3 : sync_text_sub M3)
      by (unfold M3; apply sync_text_sub_store8; [ exact Htext2 | lia ]).
    assert (E04 : add_vec_int (mword_of_int 0x04 : mword 64) 2 = mword_of_int 0x06)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E04) in "Hpc".
    (* ---- 0x06  c.addi4spn s0,sp,16 (s0 is never read again in main) ---- *)
    assert (Hw16 : add_vec_int (add_vec_int sp0 (-16)) 16
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uv_caddi4spn C pt Ψxv6 M3 m1 (mword_of_int 0x06)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-16)) 16) Φ
              (ui_sync_06 pt M3 Hlay Htext3)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> m1).
    assert (E06 : add_vec_int (mword_of_int 0x06 : mword 64) 2 = mword_of_int 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E06) in "Hpc".
    (* ---- 0x08  jal ra,0x368 <sync> ---- *)
    assert (Htj : (mword_of_int SyncSyms.sync : mword 64)
                  = add_vec (mword_of_int 0x08)
                      (sign_extend' 64 (mword_of_int 864 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x0c : mword 64)
                  = add_vec_int (mword_of_int 0x08 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Ψxv6 M3 m2 (mword_of_int 0x08)
              (mword_of_int 864 : mword 21) ra_idx
              (mword_of_int SyncSyms.sync) (mword_of_int 0x0c) Φ
              (ui_sync_08 pt M3 Hlay Htext3)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x0c : mword 64)]> m2).
    (* ---- the call: sync() ---- *)
    assert (Hra3 : m3 !!! Regidx ra_idx = mword_of_int 0x0c)
      by exact (upd_eq m2 (Regidx ra_idx) (regval_into_reg (mword_of_int 0x0c : mword 64))).
    assert (Hret2 : is_aligned_vaddr (Virtaddr (m3 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra3; vm_compute; reflexivity).
    iApply (wp_sync_sync_stub CID5 M3 m3 Φ Hlay Htext3 Hret2 with "Hcg Hpc").
    iIntros (CID6 ret) "Hcg Hpc".
    set (m4 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m3)).
    iEval (rewrite Hra3) in "Hpc".
    (* ---- 0x0c  c.li a0,0 ---- *)
    assert (Hw0 : (mword_of_int 0 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Ψxv6 M3 m4 (mword_of_int 0x0c)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64) Φ
              (ui_sync_0c pt M3 Hlay Htext3)
              ltac:(vm_compute; discriminate) Hw0
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (m5 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m4).
    assert (E0c : add_vec_int (mword_of_int 0x0c : mword 64) 2 = mword_of_int 0x0e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0c) in "Hpc".
    (* ---- 0x0e  jal ra,0x2c8 <exit> -- diverges ---- *)
    assert (Htj2 : (mword_of_int SyncSyms.exit : mword 64)
                   = add_vec (mword_of_int 0x0e)
                       (sign_extend' 64 (mword_of_int 698 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj2 : (mword_of_int 0x12 : mword 64)
                   = add_vec_int (mword_of_int 0x0e : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Ψxv6 M3 m5 (mword_of_int 0x0e)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int SyncSyms.exit) (mword_of_int 0x12) Φ
              (ui_sync_0e pt M3 Hlay Htext3)
              ltac:(vm_compute; discriminate) Htj2 Hwj2
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    iApply (wp_sync_exit_stub CID8 M3 _ Φ Hlay Htext3 with "Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* start @0x12 -- the ELF entry: the same prologue at the 2-mod-4        *)
  (* parity, then jal main.  main DIVERGES, so the jal exit at 0x1e is     *)
  (* dead code: it is never decoded and needs no fact.                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sync_start (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (Φ : mval -> iProp Σ) :
    wp_sync_start_body (CID := CIDp) C pt M m sp0 Φ.
  Proof.
    intros Hlay Htext Hsp Hfr Hfr'.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    destruct (frame_slot_facts pt M sp0 8 Hfr (or_intror eq_refl))
      as (Hu8 & (w8 & Hl8 & Hok8) & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (frame_slot_facts pt M sp0 0 Hfr (or_introl eq_refl))
      as (Hu0 & (w0 & Hl0 & Hok0) & Hcanon0 & Hpg0 & Hal0 & Hb0).
    pose proof Hfr as Hfrc. destruct Hfrc as [ _ _ _ Hflo _ ].
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-16)) 8) = uint sp0 - 8)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-16)) 0) = uint sp0 - 16)
      by (rewrite Hu0; lia).
    iIntros "Hcg Hpc".
    iEval (rewrite Hsstart) in "Hpc".
    (* ---- 0x12  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : add_vec_int sp0 (-16)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uv_caddi C pt Ψxv6 M m (mword_of_int 0x12)
              (mword_of_int 48 : mword 6) sp_idx (add_vec_int sp0 (-16)) Φ
              (ui_sync_12 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 2 = mword_of_int 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E12) in "Hpc".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    (* ---- 0x14  c.sdsp ra,8(sp) ---- *)
    assert (Htg8 : add_vec_int (add_vec_int sp0 (-16)) 8
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hwra : m !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx ra_idx)
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uv_csdsp C pt Ψxv6 M m1 (mword_of_int 0x14)
              (mword_of_int 1 : mword 6) ra_idx
              w8 (add_vec_int (add_vec_int sp0 (-16)) 8) (m !!! Regidx ra_idx) Φ
              (ui_sync_14 pt M Hlay Htext)
              Htg8 Hwra Hl8 Hok8 Hcanon8 Hpg8 Hal8 Hb8
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Hu8') in "Hcg".
    set (M2 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext2 : sync_text_sub M2)
      by (unfold M2; apply sync_text_sub_store8; [ exact Htext | lia ]).
    assert (Hdom2 : forall a : Z, is_Some (M !! a) -> is_Some (M2 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M _ _ a Ha)).
    assert (E14 : add_vec_int (mword_of_int 0x14 : mword 64) 2 = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E14) in "Hpc".
    (* ---- 0x16  c.sdsp s0,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 0) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb).
      exact (Hdom2 _ (mk_is_Some _ _ Hb)). }
    assert (Htg0 : add_vec_int (add_vec_int sp0 (-16)) 0
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : m !!! Regidx (mword_of_int 8 : mword 5)
                   = m1 !!! Regidx (mword_of_int 8 : mword 5))
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx (mword_of_int 8 : mword 5))
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uv_csdsp C pt Ψxv6 M2 m1 (mword_of_int 0x16)
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              w0 (add_vec_int (add_vec_int sp0 (-16)) 0)
              (m !!! Regidx (mword_of_int 8 : mword 5)) Φ
              (ui_sync_16 pt M2 Hlay Htext2)
              Htg0 Hws0 Hl0 Hok0 Hcanon0 Hpg0 Hal0 Hb0'
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite Hu0') in "Hcg".
    set (M3 := uM_store8 M2 (uint sp0 - 16) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Htext3 : sync_text_sub M3)
      by (unfold M3; apply sync_text_sub_store8; [ exact Htext2 | lia ]).
    assert (Hdom3 : forall a : Z, is_Some (M2 !! a) -> is_Some (M3 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M2 _ _ a Ha)).
    assert (E16 : add_vec_int (mword_of_int 0x16 : mword 64) 2 = mword_of_int 0x18)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E16) in "Hpc".
    (* ---- 0x18  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : add_vec_int (add_vec_int sp0 (-16)) 16
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uv_caddi4spn C pt Ψxv6 M3 m1 (mword_of_int 0x18)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-16)) 16) Φ
              (ui_sync_18 pt M3 Hlay Htext3)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> m1).
    assert (E18 : add_vec_int (mword_of_int 0x18 : mword 64) 2 = mword_of_int 0x1a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E18) in "Hpc".
    (* ---- 0x1a  jal ra,0x0 <main> ---- *)
    assert (Htj : (mword_of_int SyncSyms.main : mword 64)
                  = add_vec (mword_of_int 0x1a)
                      (sign_extend' 64 (mword_of_int 2097126 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x1e : mword 64)
                  = add_vec_int (mword_of_int 0x1a : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Ψxv6 M3 m2 (mword_of_int 0x1a)
              (mword_of_int 2097126 : mword 21) ra_idx
              (mword_of_int SyncSyms.main) (mword_of_int 0x1e) Φ
              (ui_sync_1a pt M3 Hlay Htext3)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x1e : mword 64)]> m2).
    (* ---- the call: main() -- diverges, so the jal exit at 0x1e is dead ---- *)
    assert (Hsp3 : m3 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
    { exact (eq_trans
               (upd_ne m2 (Regidx ra_idx) (Regidx sp_idx)
                  (regval_into_reg (mword_of_int 0x1e : mword 64))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx sp_idx)
                     (regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16))
                     ltac:(vm_compute; discriminate))
                  (upd_eq m (Regidx sp_idx)
                     (regval_into_reg (add_vec_int sp0 (-16)))))). }
    assert (Hfr3 : uv_frame16 pt M3 (add_vec_int sp0 (-16)))
      by exact (uv_frame16_dom pt M2 M3 _ Hdom3
                  (uv_frame16_dom pt M M2 _ Hdom2 Hfr')).
    iApply (wp_sync_main CID5 M3 m3 (add_vec_int sp0 (-16)) Φ
              Hlay Htext3 Hsp3 Hfr3 with "Hcg Hpc").
  Qed.

End UProofSync.
