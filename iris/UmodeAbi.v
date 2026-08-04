(* UmodeAbi.v -- program-GENERIC user-space ABI vocabulary for the verified
   user-execution tier (claude-notes/projects/user-verified.md): the RISC-V
   ABI register indices contracts speak about, image inclusion, and the
   standard stack-frame window a gcc prologue needs.  Nothing here is about
   any particular program -- per-program facts live in UCode<Prog>.v /
   Spec<Prog>Prog.v. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import UserPtTree.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 ABI register indices.  (a7_idx, the syscall-number register, lives   *)
(* in UmodeCap.v because [uv_sys_wp] itself dispatches on it.)             *)
(* ===================================================================== *)

Definition ra_idx : mword 5 := mword_of_int 1.
Definition sp_idx : mword 5 := mword_of_int 2.
Definition a0_idx : mword 5 := mword_of_int 10.

(* ===================================================================== *)
(* §2 Image inclusion: program bytes [img] (a dumped [<prog>_bytes] /      *)
(* [<prog>_data]) present verbatim in a process image [M].                 *)
(* ===================================================================== *)

Definition uimg_sub (img M : gmap Z (bv 8)) : Prop :=
  forall (a : Z) (b : bv 8), img !! a = Some b -> M !! a = Some b.

Lemma uimg_sub_lookup (img M : gmap Z (bv 8)) (a : Z) (b : bv 8) :
  uimg_sub img M -> img !! a = Some b -> M !! a = Some b.
Proof. intros Hs Hl. exact (Hs a b Hl). Qed.

(* ===================================================================== *)
(* §3 The stack-frame window.  A 16-byte frame below [sp0]: bytes present  *)
(* in the image, on a store-permitting mapped page, 16-aligned (so the     *)
(* whole window sits on one page).  There is NO interrupt-headroom         *)
(* reservation -- user traps run on the KERNEL stack, so unlike the        *)
(* kernel's [sie_cap] there is no carve and no [avail] accounting.         *)
(* ===================================================================== *)

Record uv_frame16 (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64) : Prop := {
  fr_bytes : forall j : nat, (j < 16)%nat ->
               exists b : bv 8, M !! (uint sp0 - 16 + Z.of_nat j) = Some b;
  fr_leaf  : exists w : mword 64,
               ud_um pt !! svpn_of (add_vec_int sp0 (-16)) = Some w /\
               uleaf_ok (Store Data) w;
  fr_al    : Z.rem (uint sp0) 16 = 0;
  fr_lo    : 4096 + 16 <= uint sp0;      (* below the frame is not page 0 *)
  fr_canon : uint sp0 < 2 ^ 38           (* Sv39-canonical, no wrap *)
}.

(* a dom-preserving image update keeps every frame window *)
Lemma uv_frame16_dom (pt : uptd) (M M' : gmap Z (bv 8)) (sp0 : mword 64) :
  (forall a : Z, is_Some (M !! a) -> is_Some (M' !! a)) ->
  uv_frame16 pt M sp0 -> uv_frame16 pt M' sp0.
Proof.
  intros Hdom [Hb Hl Hal Hlo Hc]. constructor; try assumption.
  intros j Hj. destruct (Hb j Hj) as [b HMb].
  destruct (Hdom (uint sp0 - 16 + Z.of_nat j) (ex_intro _ b HMb)) as [b' Hb'].
  eauto.
Qed.
