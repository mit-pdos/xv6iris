(* ProofVirtioDiskRwF.v -- virtio_disk_rw, phase P6 (+0x1d2 .. +0x234), the
   whole-function composition, and the sealed functor.

     0x1d2 lw   s2,-96(s0)      s2 = idx[0] = the chain head
     0x1d6 slli a4,s2,4 ; 0x1da addi a4,a4,32
     0x1de auipc/addi a5,&disk ; 0x1e6 c.add a5,a4
     0x1e8 sd   x0,8(a5)        disk.info[head].b = 0
     0x1ec auipc/addi s3,&disk  -- s3 (which held b) is CLOBBERED here
     -- free_chain, three iterations, head at +0x1f4 --
     0x1f4 slli a4,s2,4 ; 0x1f8 ld a5,0(s3) ; 0x1fc c.add a5,a4
     0x1fe lhu  s1,12(a5)       s1 = desc[i].flags
     0x202 c.mv a0,s2 ; 0x204 lhu s2,14(a5)
     0x208 jal  free_desc
     0x20c c.andi s1,s1,1 ; 0x20e c.bnez s1,-26
     0x210 auipc/addi a0,&disk.vdisk_lock ; 0x218 jal release
     0x21c..0x22e c.ldsp ra,s0..s8 ; 0x230 c.addi16sp sp,96 ; 0x232 c.jr ra

   THE CONTENT is the payoff withdrawal.  P5 leaves the publisher's position
   PARKED, so P6 deletes it from [pk] (and from the claim auth and the triple
   map) and collects: [b->disk] back at 0, [info[head].b], the residual pin,
   the status byte at 0, the disk fragments and -- for a read -- the buffer.
   The residual pin is the ONE thing that has to be taken apart again: it is
   the fifteen descriptor/header windows the chain formatting wrote (plus, for
   a write, the payload), and [free_desc] wants them back as word cells.  That
   decomposition is the pure fact [vdrw_p5_exit] carries
   ([ProofVirtioDiskRwD.vdrwd_pinr_regions] + [pm_ok]); here it is cashed with
   [pm_split] and the [phys_map -> word] tier bridges.

   The free-chain loop runs EXACTLY three times ([desc[h].flags = 1],
   [desc[m2].flags ∈ {1,3}], [desc[t].flags = 2]), so it is unrolled with a
   literal trip count -- no Löb.

   Everything here is Qed-closed; there is no [Admitted]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import KptPt KMap.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import ProcGeom.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn SchedCtx FdSlots.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeHalf.
Require Import VirtioModel VirtioQueue DiskPtsto VirtioProto DiskInv.
Require Import VirtioModel.
Require Import WpUart.
Require Import PermInv.
Require Import SpecPanic.
Require Import SpecAcquire SpecRelease SpecSleepPrepare SpecSleep SpecFreeDesc.
Require Import CodeVirtioDiskRw.
Require Import SpecVirtioDiskRw.
Require Import VirtioDiskRwDefs.
Require Import ProofVirtioDiskRwD.
Require Import ProofVirtioDiskRwE.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).


(* ===================================================================== *)
(* §0  Pure helpers: the addresses, the immediates, and the [struct disk] *)
(*     alignment/canonicality facts the tier bridges need.               *)
(* ===================================================================== *)

(* ---- [struct disk] is 8-aligned, so every field offset that is a
   multiple of 2/4/8 is aligned at that width. ------------------------- *)

(* Stated over [KernelSyms.disk] rather than the literal: [disk] is a DATA
   symbol and it moves on most image bumps (0x80023470 -> 0x800234a0 this
   time).  Through the symbol this cannot go stale again. *)
Lemma vdrwf_disk_val :
  bv_unsigned (disk_base : SailStdpp.Values.mword 64) = KernelSyms.disk.
Proof. vm_compute. reflexivity. Qed.

Lemma vdrwf_rem_disk (k d : Z) :
  0 <= k -> k < 4096 -> 0 < d -> 8 mod d = 0 -> k mod d = 0 ->
  Z.rem ((KernelSyms.disk + k) mod 18446744073709551616) d = 0.
Proof.
  intros H0 H1 Hd Hd8 Hkd. unfold KernelSyms.disk.
  rewrite (Z.mod_small (2147628192 + k) 18446744073709551616); [| lia].
  rewrite Z.rem_mod_nonneg; [| lia | lia].
  apply Z.mod_divide; [lia|].
  apply Z.mod_divide in Hd8; [| lia].
  apply Z.mod_divide in Hkd; [| lia].
  apply Z.divide_add_r; [| exact Hkd].
  apply (Z.divide_trans d 8 2147628192 Hd8). exists 268453524%Z. reflexivity.
Qed.

Lemma vdrwf_disk_aligned (k : nat) (d : Z) :
  (Z.of_nat k < 4096)%Z -> (0 < d)%Z -> (8 mod d = 0)%Z ->
  (Z.of_nat k mod d = 0)%Z ->
  is_aligned_paddr (Physaddr (pa_add disk_base k)) d = true.
Proof.
  intros Hk Hd Hd8 Hkd. unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite uint_unsigned pa_add_unsigned.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  rewrite vdrwf_disk_val.
  apply vdrwf_rem_disk;
    [ exact (Nat2Z.is_nonneg k) | exact Hk | exact Hd | exact Hd8 | exact Hkd ].
Qed.

Lemma vdrwf_kdata_canon (a : Arch.pa) :
  addr_is_kdata a -> (uint (a : SailStdpp.Values.mword 64) < 274877906944)%Z.
Proof.
  intro Hka. unfold addr_is_kdata, ram_base, ram_size, text_end in Hka.
  first [ lia
        | (assert (Heq : (uint (a : SailStdpp.Values.mword 64) = uint a)%Z)
             by reflexivity; rewrite Heq; lia) ].
Qed.

Lemma vdrwf_disk_canon (k : nat) : (k < 4096)%nat ->
  (uint (pa_add disk_base k : SailStdpp.Values.mword 64) < 274877906944)%Z.
Proof. intro Hk. apply vdrwf_kdata_canon, vdrwd_disk_kdata, Hk. Qed.

(* THE BUFFER POINTER IS NON-NULL, out of the spec's kernel-data premise.
   [sleep_prepare] panics on a zero channel and P5 passes [b], so the fact
   has to reach [P5.wp_vdrw_p5_seam]; nothing P5 holds can produce it (a
   points-to says nothing about its address).  At [b = 0] the buffer's data
   window would start at byte 88, far below [text_end]. *)
Lemma vdrwf_bnz (b : Arch.pa) :
  addr_is_kdata (pa_add (b_data b) 0) ->
  eq_vec (b : SailStdpp.Values.mword 64) (zero_reg : SailStdpp.Values.mword 64) = false.
Proof.
  intro Hk.
  destruct (eq_vec (b : SailStdpp.Values.mword 64)
                   (zero_reg : SailStdpp.Values.mword 64)) eqn:Hb; [| reflexivity].
  exfalso. apply eq_vec_true_iff in Hb. rewrite Hb in Hk.
  unfold addr_is_kdata, text_end, ram_base, ram_size in Hk.
  assert (Hz : uint (pa_add (b_data (zero_reg : SailStdpp.Values.mword 64)) 0
                     : SailStdpp.Values.mword 64) = 88%Z)
    by (vm_compute; reflexivity).
  rewrite Hz in Hk. lia.
Qed.

(* the three [struct disk] windows P6 rebuilds *)
Lemma vdrwf_ops_align (i : nat) : (i < 8)%nat ->
  is_aligned_paddr (Physaddr (d_ops i)) 4 = true.
Proof.
  intro Hi. unfold d_ops. apply vdrwf_disk_aligned; [lia|lia|reflexivity|].
  replace (Z.of_nat (168 + 16 * i)) with ((42 + 4 * Z.of_nat i) * 4)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma vdrwf_opsr_align (i : nat) : (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add disk_base (168 + 16 * i + 4))) 4 = true.
Proof.
  intro Hi. apply vdrwf_disk_aligned; [lia|lia|reflexivity|].
  replace (Z.of_nat (168 + 16 * i + 4)) with ((43 + 4 * Z.of_nat i) * 4)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma vdrwf_opss_align (i : nat) : (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add disk_base (168 + 16 * i + 8))) 8 = true.
Proof.
  intro Hi. apply vdrwf_disk_aligned; [lia|lia|reflexivity|].
  replace (Z.of_nat (168 + 16 * i + 8)) with ((22 + 2 * Z.of_nat i) * 8)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

(* ---- descriptor-page window alignments: RESTATEMENTS of [DiskInv]'s --- *)

Lemma vdrwf_desc_align (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (d_desc pd i)) 8 = true.
Proof. exact (d_desc_aligned8 pd i). Qed.

Lemma vdrwf_dlen_align (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add pd (16 * i + 8))) 4 = true.
Proof. exact (d_desc_len_aligned4 pd i). Qed.

Lemma vdrwf_dflags_align (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add pd (16 * i + 12))) 2 = true.
Proof. exact (d_desc_flags_aligned2 pd i). Qed.

Lemma vdrwf_dnext_align (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add pd (16 * i + 14))) 2 = true.
Proof. exact (d_desc_next_aligned2 pd i). Qed.

(* ---- the immediates and jump targets ------------------------------- *)

Lemma vdrwf_a5disk :
  add_vec (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1de) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 2722 : mword 12))
  = (disk_base : SailStdpp.Values.mword 64).
Proof. unfold disk_base. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwf_s3disk :
  add_vec (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ec) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 2708 : mword 12))
  = (disk_base : SailStdpp.Values.mword 64).
Proof. unfold disk_base. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwf_a0lock :
  add_vec (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x210) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 2968 : mword 12))
  = (d_lock : SailStdpp.Values.mword 64).
Proof. unfold d_lock, disk_base. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwf_jfree :
  add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x208) : mword 64)
          (sign_extend' 64 (mword_of_int 2096058 : mword 21))
  = (mword_of_int KernelSyms.free_desc : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwf_jrel :
  add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x218) : mword 64)
          (sign_extend' 64 (mword_of_int 2077240 : mword 21))
  = (mword_of_int KernelSyms.release : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the descriptor-pointer cell address, [0(s3)] with s3 = &disk *)
Lemma vdrwf_dptr_addr :
  add_vec (disk_base : SailStdpp.Values.mword 64)
          (sign_extend' 64 (mword_of_int 0 : mword 12))
  = (d_desc_ptr : SailStdpp.Values.mword 64).
Proof.
  rewrite vdrw_addv_sext0. unfold d_desc_ptr.
  rewrite (vdrw_pa_add_moi (disk_base : SailStdpp.Values.mword 64) 0%nat).
  symmetry. apply bv_add_0_r. vm_compute. reflexivity.
Qed.

(* [info[i].b], as +0x1d6..+0x1e8 computes it *)
Lemma vdrwf_infob_addr (i : nat) :
  add_vec (add_vec (disk_base : SailStdpp.Values.mword 64)
                   (add_vec (mword_of_int (16 * Z.of_nat i) : mword 64)
                            (sign_extend' 64 (mword_of_int 32 : mword 12))))
          (sign_extend' 64 (mword_of_int 8 : mword 12))
  = (d_info_b i : SailStdpp.Values.mword 64).
Proof.
  rewrite vdrwc_sx32 vdrwc_sx8 (vdrwc_moi2 (16 * Z.of_nat i) 32).
  rewrite (vdrw_av2 (disk_base : SailStdpp.Values.mword 64)
             (16 * Z.of_nat i + 32) 8).
  unfold d_info_b.
  rewrite (vdrw_pa_add_moi (disk_base : SailStdpp.Values.mword 64) (40 + 16 * i)%nat).
  assert (Hz : (16 * Z.of_nat i + 32 + 8 = Z.of_nat (40 + 16 * i))%Z) by lia.
  rewrite Hz. reflexivity.
Qed.

(* ---- index/word normalisations -------------------------------------- *)

Lemma vdrwf_zext16 (i : nat) : (i < 8)%nat ->
  zero_extend' 64 (Z_to_bv 16 (Z.of_nat i) : SailStdpp.Values.mword 16)
  = (mword_of_int (Z.of_nat i) : SailStdpp.Values.mword 64).
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* the [c.andi s1,1] test on the three flag words the chain carries *)
Lemma vdrwf_bit0_1 :
  neq_vec (and_vec (zero_extend' 64 (Z_to_bv 16 1 : SailStdpp.Values.mword 16)
                    : SailStdpp.Values.mword 64)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
          (zero_reg : SailStdpp.Values.mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vdrwf_bit0_3 :
  neq_vec (and_vec (zero_extend' 64 (Z_to_bv 16 3 : SailStdpp.Values.mword 16)
                    : SailStdpp.Values.mword 64)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
          (zero_reg : SailStdpp.Values.mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vdrwf_bit0_2 :
  neq_vec (and_vec (zero_extend' 64 (Z_to_bv 16 2 : SailStdpp.Values.mword 16)
                    : SailStdpp.Values.mword 64)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
          (zero_reg : SailStdpp.Values.mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

(* the middle descriptor's flags are 1 or 3 -- either way bit 0 is set *)
Lemma vdrwf_bit0_flags (wr : SailStdpp.Values.mword 64) :
  neq_vec (and_vec (zero_extend' 64 (vdrw_flags wr : SailStdpp.Values.mword 16)
                    : SailStdpp.Values.mword 64)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
          (zero_reg : SailStdpp.Values.mword 64) = true.
Proof.
  destruct (vdrwc_ty_flags wr) as [_ Hfl]. rewrite Hfl.
  destruct (bv_unsigned (vdrw_ty wr) =? virtio_blk_t_out).
  - exact vdrwf_bit0_1.
  - exact vdrwf_bit0_3.
Qed.

(* THE DIRECTION BRIDGE: the slot's OUT-ness is exactly the spec's [write]
   argument being non-zero.  Both come from the same [snez]/[seqz] test. *)
Lemma vdrwf_pos (x : Z) : (0 <= x)%Z -> x <> 0%Z -> (0 <? x)%Z = true.
Proof. intros H0 H1. apply Z.ltb_lt. lia. Qed.

Lemma vdrwf_out_iff (wr : SailStdpp.Values.mword 64) :
  vdrwd_out wr = negb (eq_vec wr (zero_reg : SailStdpp.Values.mword 64)).
Proof.
  assert (Hz : uint (zero_reg : SailStdpp.Values.mword 64) = 0)
    by (vm_compute; reflexivity).
  assert (Hnn : (0 <= uint wr)%Z).
  { rewrite uint_unsigned. destruct (bv_unsigned_in_range _ wr). assumption. }
  assert (Heq : eq_vec wr (zero_reg : SailStdpp.Values.mword 64)
                = negb (0 <? uint wr)%Z).
  { destruct (eq_vec wr (zero_reg : SailStdpp.Values.mword 64)) eqn:He.
    - apply eq_vec_true_iff in He. rewrite He Hz. reflexivity.
    - apply eq_vec_false_iff in He.
      assert (Hne : uint wr <> 0%Z).
      { intro Hc. apply He. apply bv_eq.
        assert (Hzz : bv_unsigned (zero_reg : SailStdpp.Values.mword 64) = 0%Z)
          by (vm_compute; reflexivity).
        rewrite Hzz. rewrite uint_unsigned in Hc. exact Hc. }
      rewrite (vdrwf_pos (uint wr) Hnn Hne). reflexivity. }
  rewrite Heq negb_involutive.
  unfold vdrwd_out, vdrw_ty, vdrw_ty64, zopz0zI_u.
  rewrite Hz.
  destruct (0 <? uint wr)%Z; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* §1  Tier bridges, the direction the PAYOFF travels: an owned byte      *)
(*     window comes back from the protocol as one [phys_map] and has to   *)
(*     become word cells again.  These are the inverses of                *)
(*     [ProofVirtioDiskRwD.vdrwd_w2/_w4/_w8].                             *)
(* ===================================================================== *)

Section VdrwfBridges.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  Lemma vdrwf_w2b (a : Arch.pa) (w : bv 16) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 2)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_map (range_map a 2 (nth_byte w)) -∗ a ↦₂ w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb H".
    iEval (rewrite <- phys_word2_map) in "H".
    iApply (phys_to_word2 a w Hal Hs Hc with "Hb H").
  Qed.

  Lemma vdrwf_w4b (a : Arch.pa) (w : bv 32) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 4)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_map (range_map a 4 (nth_byte w)) -∗ a ↦₄ w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb H".
    iEval (rewrite <- phys_word4_map) in "H".
    iApply (phys_to_word4 a w Hal Hs Hc with "Hb H").
  Qed.

  Lemma vdrwf_w8b (a : Arch.pa) (w : bv 64) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    (forall j, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 8)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_map (range_map a 8 (nth_byte w)) -∗ a ↦₈ w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb H".
    iEval (rewrite <- vdrwd_pw8_map) in "H".
    iApply (phys_to_word8 a w Hal Hs Hc with "Hb H").
  Qed.

  (* the buffer, back at the VA tier where [buf_own] wants it *)
  Lemma vdrwf_plist_mem (a : Arch.pa) (bs : list (bv 8)) :
    (forall j, (j < length bs)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < length bs)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_list a bs -∗
    ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x).
  Proof.
    iIntros (Hs Hc) "#Hb H". rewrite /phys_list.
    iApply (big_sepL_impl with "H").
    iIntros "!>" (k x Hk) "Hx".
    assert (Hlt : (k < length bs)%nat) by (apply lookup_lt_Some in Hk; lia).
    iApply (phys_to_byte (pa_add a k) x (Hs k Hlt) (Hc k Hlt) with "Hb Hx").
  Qed.

  Lemma vdrwf_map_plist (a : Arch.pa) (bs : list (bv 8)) :
    (Z.of_nat (length bs) < 18446744073709551616)%Z ->
    phys_map (range_map a (length bs) (fun j => bs !!! j)) -∗ phys_list a bs.
  Proof. intro Hn. rewrite (phys_list_map a bs Hn). iIntros "$". Qed.

End VdrwfBridges.

(* the per-window canonicality premise, from a page-wide (or struct-wide)
   one -- the twin of [ProofVirtioDiskRwD.vdrwd_off_static]. *)
Lemma vdrwf_off_canon (base a : Arch.pa) (k n : nat) :
  a = pa_add base k -> (k + n <= 4096)%nat ->
  (forall j, (j < 4096)%nat ->
     (uint (pa_add base j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
  forall j, (j < n)%nat ->
    (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z.
Proof. intros -> Hkn Hc j Hj. rewrite pa_add_add. apply Hc. lia. Qed.

(* the window bounds and the frame arithmetic, as mword-FREE facts: [lia]
   is unreliable once a [bv_unsigned] hypothesis is in context. *)
Lemma vdrwf_dbnds (i : nat) : (i < 8)%nat ->
  (16 * i + 8 <= 4096)%nat /\ (16 * i + 8 + 4 <= 4096)%nat
  /\ (16 * i + 12 + 2 <= 4096)%nat /\ (16 * i + 14 + 2 <= 4096)%nat
  /\ (168 + 16 * i + 4 <= 4096)%nat /\ (168 + 16 * i + 4 + 4 <= 4096)%nat
  /\ (168 + 16 * i + 8 + 8 <= 4096)%nat.
Proof. intro Hi. split_and!; lia. Qed.

Lemma vdrwf_Kk (K : nat) : (K_virtio_disk_rw <= K)%nat -> ((K - 12) + 12)%nat = K.
Proof. unfold K_virtio_disk_rw. lia. Qed.

Lemma vdrwf_pop_z : (- (8 * Z.of_nat 12) + 96)%Z = 0%Z.
Proof. lia. Qed.

Lemma vdrwf_1024_lt : (Z.of_nat 1024 < 18446744073709551616)%Z.
Proof. lia. Qed.

Lemma vdrwf_sec512 (x : Z) : (2 * x * 512)%Z = (1024 * x)%Z.
Proof. lia. Qed.

Lemma vdrwf_below_seq (q nr np : nat) :
  (q < nr)%nat -> q ∉ set_seq (C := gset nat) nr (np - nr).
Proof. intros Hq Hin. apply elem_of_set_seq in Hin. lia. Qed.

(* THE TRIPLE-MEMBERSHIP AND DOMAIN FACTS, AS PURE LEMMAS.
   [set_solver] costs 100-270 s PER CALL inside a large Iris WP context (it
   rescans the whole hypothesis context -- optimization.md); proved here, in a
   context of three set variables, each is instant.  Never call [set_solver]
   from inside a phase proof. *)
Lemma vdrwf_tri_mem (h m2 t : nat) :
  h ∈ tri_set (h, m2, t) /\ m2 ∈ tri_set (h, m2, t) /\ t ∈ tri_set (h, m2, t).
Proof.
  unfold tri_set. cbn. split_and!.
  - apply elem_of_union_l, elem_of_union_l, elem_of_singleton. reflexivity.
  - apply elem_of_union_l, elem_of_union_r, elem_of_singleton. reflexivity.
  - apply elem_of_union_r, elem_of_singleton. reflexivity.
Qed.

Lemma vdrwf_dom_delete (q : nat) (F P T : gset nat) :
  T = F ∪ P -> q ∉ F -> T ∖ {[ q ]} = F ∪ (P ∖ {[ q ]}).
Proof. intros -> Hq. set_solver. Qed.

(* free_desc's argument bound, off the NORMALISED index word *)
Lemma vdrwf_uint_small (i : nat) : (i < 8)%nat ->
  uint (mword_of_int (Z.of_nat i) : SailStdpp.Values.mword 64) = Z.of_nat i.
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* ===================================================================== *)
(* §2  P6, the P5 -> P6 glue, the whole-function composition and the seal. *)
(* ===================================================================== *)

Module VirtioDiskRwProof (Acquire : ACQUIRE) (Release : RELEASE)
                         (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) (FreeDesc : FREEDESC) : VIRTIODISKRW.

Module P5 := VirtioDiskRwRestE Acquire Release SleepPrepare Sleep FreeDesc.
Module P4 := P5.P4.
Module P3 := P5.P4.P3.
Module P2 := P5.P4.P3.P2.
Module P1 := P5.P4.P3.P2.P1.

Notation Rra := (mword_of_int 1  : mword 5).
Notation Rtp := (mword_of_int 4  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Rs7 := (mword_of_int 23 : mword 5).
Notation Rs8 := (mword_of_int 24 : mword 5).

(* The free-chain iteration is reached AFTER the completion wait's park, so
   the hart it runs on is the one [P5.vdrw_p5_exit]'s [wp_next] delivers --
   NOT the one the function entered on.  It therefore may not sit in a
   section that FIXES [CpuId] (a section variable cannot be instantiated at
   its use site); [CID] is an ordinary binder of the lemma instead. *)
Section VdrwfP6.
  (* [eb] is the literal [true] in the epilogue, so [iNext] would otherwise
     descend through [cpu_own]'s [if b then ⌜…⌝ else …] and strip a later
     that is not ours.  Keep the bundle opaque. *)
  Local Typeclasses Opaque cpu_own.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  (* ------------------------------------------------------------------- *)
  (* ONE free_chain iteration: +0x1f4 .. +0x208, landing at +0x20c with    *)
  (* s1 = desc[i].flags and s2 = desc[i].next (both callee-saved, so they   *)
  (* survive the call), and descriptor [i] back in the free pool.           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_vdrwf_iter `{GEN : GenId} `{CID : CpuId}  (γs : list gname)
      (pd : SailStdpp.Values.mword 64) (i : nat) (fr : nat -> bool)
      (va : SailStdpp.Values.mword 64) (vl : SailStdpp.Values.mword 32)
      (vf vn : SailStdpp.Values.mword 16)
      (M : regfile) (av : nat) (eb : bool) (pme : SailStdpp.Values.mword 64)
      (C : iProp Σ) :
    (K_free_desc <= av)%nat -> (i < 8)%nat -> fr i = false ->
    length γs = NPROC ->
    M !!! Regidx Rs2 = (mword_of_int (Z.of_nat i) : SailStdpp.Values.mword 64) ->
    M !!! Regidx Rs3 = (disk_base : SailStdpp.Values.mword 64) ->
    sie_cap_gpr M av false pme -∗
    cpu_own 1 eb pme C false -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x1f4) : mword 64) -∗
    panic_wp_any -∗ procs_inv γs -∗
    d_desc_ptr ↦₈□ pd -∗
    d_desc pd i ↦₈ va -∗ pa_add pd (16 * i + 8) ↦₄ vl -∗
    pa_add pd (16 * i + 12) ↦₂ vf -∗ pa_add pd (16 * i + 14) ↦₂ vn -∗
    free_bundles pd fr -∗ vdrw_slot_rest i -∗
    ( ∀ Mf : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true ->
            r <> Rs1 -> r <> Rs2 -> Mf !!! Regidx r = M !!! Regidx r)
         /\ Mf !!! Regidx Rs1 = (zero_extend' 64 vf : SailStdpp.Values.mword 64)
         /\ Mf !!! Regidx Rs2 = (zero_extend' 64 vn : SailStdpp.Values.mword 64)⌝ -∗
        sie_cap_gpr Mf av false pme -∗
        cpu_own 1 eb pme C false -∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x20c) : mword 64) -∗
        free_bundles pd (fr_upd fr i true) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hi8 Hfri Hlen Hs2 Hs3.
    iIntros "Hcg Hown #Htext Hpc #Hpanic #Hpinv #Hdp Hd0 Hd8 Hd12 Hd14 Hbun Hrest Hcont".
    iPoseProof (rwi_1f4 with "Htext") as "Hi1d2".
    iPoseProof (rwi_1f8 with "Htext") as "Hi1d6".
    iPoseProof (rwi_1fc with "Htext") as "Hi1da".
    iPoseProof (rwi_1fe with "Htext") as "Hi1dc".
    iPoseProof (rwi_202 with "Htext") as "Hi1e0".
    iPoseProof (rwi_204 with "Htext") as "Hi1e2".
    iPoseProof (rwi_208 with "Htext") as "Hi1e6".
    (* ---- +0x1f4  slli a4,s2,4 ---- *)
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1f4) : mword 64) Ra4 Rs2
              (mword_of_int 4 : mword 6)
              (mword_of_int (16 * Z.of_nat i) : SailStdpp.Values.mword 64) M av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgall; rewrite Hs2; exact (vdrwc_slli4' i Hi8))
              with "Hcg Hpc Hi1d2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N1 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat i) : SailStdpp.Values.mword 64)]> M).
    change (<[Regidx Ra4 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat i) : SailStdpp.Values.mword 64)]> M) with N1.
    assert (Hp1d6 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1f4) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1f8)) by pcstep.
    iEval (rewrite Hp1d6) in "Hpc".
    assert (HN1s3 : N1 !!! Regidx Rs3 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N1 upd_ne; [| reg_neq]; exact Hs3).
    assert (HN1a4 : N1 !!! Regidx Ra4
                    = (mword_of_int (16 * Z.of_nat i) : SailStdpp.Values.mword 64))
      by (rewrite /N1; apply upd_eq).
    (* ---- +0x1f8  ld a5,0(s3) : a5 = disk.desc ---- *)
    assert (Hdptr : add_vec (N1 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = (d_desc_ptr : SailStdpp.Values.mword 64))
      by (rewrite HN1s3; apply vdrwf_dptr_addr).
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1f8) : mword 64) Ra5 Rs3
              (mword_of_int 0 : mword 12) N1 av pd false (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1d6 [] [-]").
    { rgall. iEval (rewrite Hdptr). iExact "Hdp". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc _". rgall.
    set (N2 := <[Regidx Ra5 := regval_into_reg pd]> N1).
    change (<[Regidx Ra5 := regval_into_reg pd]> N1) with N2.
    assert (Hp1da : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1f8) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1fc)) by pcstep.
    iEval (rewrite Hp1da) in "Hpc".
    assert (HN2a5 : N2 !!! Regidx Ra5 = pd) by (rewrite /N2; apply upd_eq).
    assert (HN2a4 : N2 !!! Regidx Ra4
                    = (mword_of_int (16 * Z.of_nat i) : SailStdpp.Values.mword 64))
      by (rewrite /N2 upd_ne; [| reg_neq]; exact HN1a4).
    (* ---- +0x1fc  c.add a5,a4 : a5 = &desc[i] ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1fc) : mword 64) Ra5 Ra4 N2 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1da [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (N2 !!! Regidx Ra5) (N2 !!! Regidx Ra4))]> N2).
    change (<[Regidx Ra5 := regval_into_reg
                  (add_vec (N2 !!! Regidx Ra5) (N2 !!! Regidx Ra4))]> N2) with N3.
    assert (HN3a5 : N3 !!! Regidx Ra5 = (d_desc pd i : SailStdpp.Values.mword 64)).
    { rewrite /N3 upd_eq HN2a5 HN2a4. apply vdrwc_desc_addr'. }
    assert (Hp1dc : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1fc) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1fe)) by pcstep.
    iEval (rewrite Hp1dc) in "Hpc".
    (* ---- +0x1fe  lhu s1,12(a5) : the flags ---- *)
    assert (Hfaddr : add_vec (N3 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 12 : mword 12))
                     = (pa_add pd (16 * i + 12)%nat : SailStdpp.Values.mword 64))
      by (rewrite HN3a5; apply vdrwc_desc_flags).
    iApply (wp_lhu_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1fe) : mword 64) Rs1 Ra5
              (mword_of_int 12 : mword 12) N3 av vf false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1dc [Hd12] [-]").
    { rgall. iEval (rewrite Hfaddr). iExact "Hd12". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hd12". rgall.
    iEval (rewrite Hfaddr) in "Hd12".
    set (N4 := <[Regidx Rs1 := regval_into_reg (zero_extend' 64 vf)]> N3).
    change (<[Regidx Rs1 := regval_into_reg (zero_extend' 64 vf)]> N3) with N4.
    assert (Hp1e0 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1fe) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x202)) by pcstep.
    iEval (rewrite Hp1e0) in "Hpc".
    assert (HN4s2 : N4 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat i) : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [| reg_neq]. exact Hs2. }
    assert (HN4a5 : N4 !!! Regidx Ra5 = (d_desc pd i : SailStdpp.Values.mword 64))
      by (rewrite /N4 upd_ne; [| reg_neq]; exact HN3a5).
    (* ---- +0x202  c.mv a0,s2 : the argument ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x202) : mword 64) Ra0 Rs2 N4 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e0 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (N4 !!! Regidx Rs2))]> N4).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (N4 !!! Regidx Rs2))]> N4) with N5.
    assert (HN5a0 : N5 !!! Regidx Ra0
                    = (mword_of_int (Z.of_nat i) : SailStdpp.Values.mword 64)).
    { rewrite /N5 upd_eq vdrwe_addv_zero. exact HN4s2. }
    assert (Hp1e2 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x202) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x204)) by pcstep.
    iEval (rewrite Hp1e2) in "Hpc".
    assert (HN5a5 : N5 !!! Regidx Ra5 = (d_desc pd i : SailStdpp.Values.mword 64))
      by (rewrite /N5 upd_ne; [| reg_neq]; exact HN4a5).
    (* ---- +0x204  lhu s2,14(a5) : the next index ---- *)
    assert (Hnaddr : add_vec (N5 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 14 : mword 12))
                     = (pa_add pd (16 * i + 14)%nat : SailStdpp.Values.mword 64))
      by (rewrite HN5a5; apply vdrwc_desc_next).
    iApply (wp_lhu_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x204) : mword 64) Rs2 Ra5
              (mword_of_int 14 : mword 12) N5 av vn false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e2 [Hd14] [-]").
    { rgall. iEval (rewrite Hnaddr). iExact "Hd14". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hd14". rgall.
    iEval (rewrite Hnaddr) in "Hd14".
    set (N6 := <[Regidx Rs2 := regval_into_reg (zero_extend' 64 vn)]> N5).
    change (<[Regidx Rs2 := regval_into_reg (zero_extend' 64 vn)]> N5) with N6.
    assert (Hp1e6 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x204) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x208)) by pcstep.
    iEval (rewrite Hp1e6) in "Hpc".
    (* ---- +0x208  jal ra,free_desc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x208) : mword 64) Rra
              (mword_of_int 2096058 : mword 21) N6 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1e6 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x208) : mword 64) 4)]> N6).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x208) : mword 64) 4)]> N6) with N7.
    iEval (rewrite vdrwf_jfree) in "Hpc".
    assert (HN7a0 : uint (N7 !!! Regidx Ra0 : SailStdpp.Values.mword 64) = Z.of_nat i).
    { rewrite /N7 upd_ne; [| reg_neq]. rewrite /N6 upd_ne; [| reg_neq].
      rewrite HN5a0. exact (vdrwf_uint_small i Hi8). }
    assert (HN7ra : N7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x208) : mword 64) 4)
      by (rewrite /N7; apply upd_eq).
    assert (HN7s1 : N7 !!! Regidx Rs1 = (zero_extend' 64 vf : SailStdpp.Values.mword 64)).
    { rewrite /N7 upd_ne; [| reg_neq]. rewrite /N6 upd_ne; [| reg_neq].
      rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4; apply upd_eq. }
    assert (HN7s2 : N7 !!! Regidx Rs2 = (zero_extend' 64 vn : SailStdpp.Values.mword 64)).
    { rewrite /N7 upd_ne; [| reg_neq]. rewrite /N6; apply upd_eq. }
    (* the (already cleared) free cell for [i] *)
    iEval (rewrite (free_bundles_split pd fr i Hi8)) in "Hbun".
    iDestruct "Hbun" as "[[Hcell _] Hbrest]".
    iEval (rewrite Hfri) in "Hcell".
    iApply (FreeDesc.wp_free_desc_sconf γs pd i N7 av 1%nat eb pme C va vl vf vn false
              Hav Hi8 HN7a0 ltac:(intro r; apply rf_to_gmap_dom) Hlen vdrwb_lvl1
              with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Hcell Hd0 Hd8 Hd12 Hd14 [-]").
    iApply wp_next_off_intro. iIntros (Mf) "%Hf Hcg Hown _ Hpc Hcell Hd0 Hd8 Hd12 Hd14".
    destruct Hf as (Hcs & _).
    assert (Hret : ret_pc (N7 !!! Regidx Rra) = mword_of_int (KernelSyms.virtio_disk_rw + 0x20c))
      by (rewrite HN7ra; pcstep).
    iEval (rewrite Hret) in "Hpc".
    iApply ("Hcont" $! Mf with "[%] Hcg Hown Hpc [Hcell Hbrest Hrest Hd0 Hd8 Hd12 Hd14]").
    { split_and!.
      - intros r Hr Hn1 Hn2.
        rewrite (callee_saved_lookup Hcs r Hr).
        rewrite /N7 upd_ne;
          [| apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hr]].
        rewrite /N6 upd_ne; [| intro He; injection He as He2; exact (Hn2 He2)].
        rewrite /N5 upd_ne;
          [| apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hr]].
        rewrite /N4 upd_ne; [| intro He; injection He as He2; exact (Hn1 He2)].
        rewrite /N3 upd_ne;
          [| apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hr]].
        rewrite /N2 upd_ne;
          [| apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hr]].
        rewrite /N1 upd_ne;
          [| apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hr]].
        reflexivity.
      - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact HN7s1.
      - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact HN7s2. }
    rewrite (free_bundles_split pd (fr_upd fr i true) i Hi8).
    rewrite fr_upd_eq.
    rewrite -(free_bundles_but_upd pd fr i true).
    iDestruct "Hrest" as "(Hops & Hst & Hib)".
    iFrame "Hbrest Hcell Hops Hst Hib".
    iExists (zero_reg : SailStdpp.Values.mword 64), (mword_of_int 0 : mword 32),
            (mword_of_int 0 : mword 16), (mword_of_int 0 : mword 16).
    iFrame "Hd0 Hd8 Hd12 Hd14".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* P6 (+0x1d2 .. +0x234), packaged as the wand P5 consumes.              *)
  (*                                                                      *)
  (* The completion wait has already parked, so P6 runs on whatever hart    *)
  (* [P5.vdrw_p5_exit]'s [wp_next] delivers -- and its own continuation is  *)
  (* [wp_next]-anchored in turn, because the release at +0x218 pops to      *)
  (* level 0 with the saved base [eb] and the epilogue below it runs at     *)
  (* that arm, which is interruptible whenever [eb = true].                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_vdrw_p6_seam `{GEN : GenId} `{CID : CpuId} (γk : gname)
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (m : regfile) (wr sector : SailStdpp.Values.mword 64)
      (bno : SailStdpp.Values.mword 32) (bs_buf bs_disk : list (bv 8))
      (Q : iProp Σ) (kq : nat * positive) :
    (K_virtio_disk_rw <= K)%nat -> length γs = NPROC ->
    length bs_buf = 1024%nat -> length bs_disk = 1024%nat ->
    (bv_unsigned sector * 512)%Z = (1024 * uint bno)%Z ->
    (forall k, (k < 1024)%nat -> addr_is_kdata (pa_add (b_data b) k)) ->
    m !!! Regidx csp_rs1 = (sp0 : SailStdpp.Values.mword 64) ->
    kernel_text -∗ panic_wp_any -∗ procs_inv γs -∗
    (* THE CRASH-PERMIT CHANNEL (PermInv.v): the invariant to collect the
       receipt from, and the persistent handle that says WHICH receipt is
       ours -- the claim pins [vs_perm] of our own slot, so the token the
       parked payoff carries is at exactly this [kq]. *)
    perm_inv gen_id (dn_perm γd) -∗
    perm_receipt kq.2 Q -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    vdrw_saved sp0 m -∗
    b_blockno b ↦₄{DfracOwn (1/2)} bno -∗
    (* NO caller-held [trap_csrs_pay]: the function is trap-CSR-balanced, so
       the ONE pay in play is the one the interior acquire minted and the
       release at +0x218 spends -- the complement the acquire's pay did NOT
       absorb rides in and back out as [trap_csrs_ext]/[cpu_claim_ext].  See
       SpecVirtioDiskRw.v. *)
    wp_next (CID0 := CID) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K eb (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C eb -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra)) -∗
        buf_own b bno (mword_of_int 0 : SailStdpp.Values.mword 32)
                (vdrwd_sldata wr bs_buf bs_disk) -∗
        disk_block γd (uint bno) (vdrwd_sldata wr bs_buf bs_disk) -∗
        (* THE RECEIPT: what the client's own view shift produced when this
           request's write landed, at the DMA completion. *)
        ▷ Q -∗
        WP (Loop : expr riscv_lang)) -∗
    P5.vdrw_p5_exit CID γk γs j γd pd pav pu K eb C sp0 b wr sector bs_buf
                    bs_disk m kq.
  Proof.
    intros HK Hglen Hlenbuf Hlendisk Hsec Hbufkd Hsp0m.
    iIntros "#Htext #Hpanic #Hpinv #Hqinv #Hrcpt #Hgeom #Hlk Hsaved Hbno Hcont".
    rewrite /P5.vdrw_p5_exit.
    iIntros (CIDx Hsx M q np nr fl pk tr fr h m2 t pin)
            "%Hrh %Hok %Hpq %Hpinr %Hal Hcg Hown Htc Hclm Hpc Htok
             Hbody Hclaim Hrm Hrt Hidx".
    (* SPLIT AT THE INDEX, ONCE, RIGHT HERE: [Hpay] rides UNCHANGED through
       the whole free-chain/release stretch below exactly as it always did,
       and the complement [Hext] rides alongside it, untouched, until the
       epilogue hands it to the caller. *)
    iDestruct (arm_pay_ext_split eb _ with "Htc Hclm") as "[Hpay Hext]".
    iDestruct "Hext" as "[Hextc Hextm]".
    destruct Hrh as (Hregs & Hhi).
    destruct Hregs as (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
    pose proof Hok as (Hhm & Hht & Hmt & Hh8 & Hm8 & Ht8). cbn in Hhm, Hht, Hmt.
    destruct Hpinr as (Hpineq & Hpmok).
    destruct Hal as (Hal11 & Hal12).
    destruct (vdrwf_dbnds h Hh8) as (Bh1 & Bh2 & Bh3 & Bh4 & Bh5 & Bh6 & Bh7).
    destruct (vdrwf_dbnds m2 Hm8) as (Bm1 & Bm2 & Bm3 & Bm4 & _ & _ & _).
    destruct (vdrwf_dbnds t Ht8) as (Bt1 & Bt2 & Bt3 & Bt4 & _ & _ & _).
    (* ---- the geometry ---- *)
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    iDestruct (disk_geom_static with "Hgeom") as %(Hspd & _ & _).
    iDestruct (disk_geom_canonical with "Hgeom") as %(Hcpd & _ & _).
    iPoseProof "Hgeom" as "Hgeom2".
    iDestruct "Hgeom2" as "(#Hdp & _ & _ & %Hal0 & _ & _ & _ & _)".
    destruct Hal0 as (Hald & _ & _).
    assert (Hsbuf : forall k, (k < 1024)%nat ->
              kmap_static (svpn_of (pa_add (b_data b) k)) KP_rw)
      by (intros k Hk; apply kdata_svpn_class, Hbufkd, Hk).
    assert (Hcbuf : forall k, (k < 1024)%nat ->
              (uint (pa_add (b_data b) k : SailStdpp.Values.mword 64)
               < 274877906944)%Z)
      by (intros k Hk; apply vdrwf_kdata_canon, Hbufkd, Hk).
    (* ================= STEP 1: withdraw the parked payoff ============== *)
    rewrite /vdrw_body.
    iDestruct "Hbody" as "(%Hdfl & %Hpkb & %Hdtr & %Hcoh & %Htrok & %Htrdj & %Htrfr &
                           Hpub & #Hlb & Hcl & Huidx & Hflm & Hpkm & Hfb & Hring)".
    assert (Hqpk : q ∈ dom pk) by (apply elem_of_dom; eexists; exact Hpq).
    assert (Hqnr : (q < nr)%nat) by exact (Hpkb q Hqpk).
    assert (Hnflq : q ∉ dom fl)
      by (rewrite Hdfl; exact (vdrwf_below_seq q nr np Hqnr)).
    assert (Hflq : fl !! q = None) by (apply not_elem_of_dom; exact Hnflq).
    assert (Huq : (fl ∪ pk) !! q = Some (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin))
      by (rewrite (lookup_union_r fl pk q Hflq); exact Hpq).
    assert (Htrq : tr !! q = Some (h, m2, t)) by exact (Hcoh q _ Huq).
    destruct (vdrwf_tri_mem h m2 t) as (Hinh & Hinm & Hint).
    assert (Hfrh : fr h = false) by exact (Htrfr q _ h Htrq Hinh).
    assert (Hfrm : fr m2 = false) by exact (Htrfr q _ m2 Htrq Hinm).
    assert (Hfrt : fr t = false) by exact (Htrfr q _ t Htrq Hint).
    iDestruct (big_sepM_delete (fun p v => parked_res γd pav p v) pk q _ Hpq
                 with "Hpkm") as "[Hpayoff Hpkm]".
    iMod (ghost_map_delete with "Hcl Hclaim") as "Hcl".
    assert (Hdelu : delete q (fl ∪ pk) = fl ∪ delete q pk)
      by (rewrite delete_union (delete_notin fl q Hflq); reflexivity).
    iEval (rewrite Hdelu) in "Hcl".
    (* ---- the payoff, with the claim's projections named ---- *)
    rewrite /parked_res.
    iDestruct "Hpayoff" as (bs)
      "(%Hlink & %Hbslen & %Hbsdata & Hbdisk & Hinfob & Hpinm & Hstat & Hdbytes &
        Hperm & Hbufp)".
    (* ======== COLLECT THE RECEIPT (PermInv.v) ========================= *)
    (* The parked payoff carries the SPENT permit's token at our own [kq]
       (the claim pinned [vs_perm] of the slot WE published), so this is the
       instant the client's receipt comes home.  Two laters: one is the
       permit invariant's own (it is not timeless -- it holds arbitrary
       client view shifts), one is the saved-proposition agreement's.  Both
       are paid off by the [iNext]s of the instructions this proof still has
       to execute before it reaches its continuation, which is why the
       postcondition below is a single [▷ Q]. *)
    iApply fupd_wp.
    iMod (perm_collect gen_id (dn_perm γd) kq.1 kq.2 _ Q ⊤ ltac:(solve_ndisj)
            with "Hqinv Hrcpt Hperm") as "HQ".
    iModIntro.
    assert (Hdcb : dc_buf (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin) = b) by reflexivity.
    assert (Hdcs : dc_slot (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin) = (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk))) by reflexivity.
    assert (Hvsts : vr_status (vs_req (dc_slot (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin))) = d_info_status h)
      by reflexivity.
    assert (Hvsout : vs_is_out (dc_slot (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin)) = vdrwd_out wr) by reflexivity.
    assert (Hvsbuf : vr_buf (vs_req (dc_slot (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin))) = b_data b) by reflexivity.
    assert (Hslen : vs_len (dc_slot (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin)) = 1024%nat) by exact vdrwd_len1024.
    assert (Hsloff : vs_sector_off (dc_slot (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin)) = (1024 * uint bno)%Z).
    { transitivity (bv_unsigned sector * 512)%Z; [| exact Hsec].
      exact (vdrwd_slot_off kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)
               (bv_unsigned sector) eq_refl). }
    assert (Hbs : bs = vdrwd_sldata wr bs_buf bs_disk)
      by (rewrite Hbsdata; reflexivity).
    assert (Hlensl : length (vdrwd_sldata wr bs_buf bs_disk) = 1024%nat).
    { unfold vdrwd_sldata. destruct (vdrwd_out wr); assumption. }
    assert (Hsl_out : vdrwd_out wr = true -> vdrwd_sldata wr bs_buf bs_disk = bs_buf)
      by (unfold vdrwd_sldata; intro Ho; rewrite Ho; reflexivity).
    assert (Hsl_in : vdrwd_out wr = false -> vdrwd_sldata wr bs_buf bs_disk = bs_disk)
      by (unfold vdrwd_sldata; intro Ho; rewrite Ho; reflexivity).
    assert (Hbufwin_out : vdrwd_out wr = true ->
              vdrwd_bufwin b wr bs_buf
              = range_map (b_data b) 1024 (fun k => bs_buf !!! k)).
    { intro Ho. unfold vdrwd_out in Ho. unfold vdrwd_bufwin. rewrite Ho. reflexivity. }
    iEval (rewrite Hdcb) in "Hbdisk".
    iEval (rewrite Hdcs) in "Hinfob".
    iEval (rewrite (vdrwd_slot_head kq b h wr sector
                      (vdrwd_sldata wr bs_buf bs_disk) Hh8)) in "Hinfob".
    iEval (rewrite Hdcb) in "Hinfob".
    iEval (rewrite Hvsts) in "Hstat".
    iEval (rewrite Hsloff) in "Hdbytes".
    iEval (rewrite Hvsout) in "Hbufp".
    iEval (rewrite Hvsbuf) in "Hbufp".
    (* ---- the residual pin, split into its fifteen (+1) windows ---- *)
    assert (Hpinreq : dc_pinr pav q (DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) (h, m2, t) pin)
                      = foldr union ∅ (vdrwd_pinr_regions pd b h m2 t wr sector
                                         (vdrwd_bufwin b wr bs_buf))).
    { rewrite /dc_pinr /dc_ring_map. cbn [dc_pin dc_slot].
      unfold vdrwd_slot, rw_slot. cbn [vs_req vr_head]. exact Hpineq. }
    iEval (rewrite Hpinreq) in "Hpinm".
    iDestruct (pm_split _ Hpmok with "Hpinm") as "Hpl".
    rewrite /pm_list /vdrwd_pinr_regions.
    iDestruct "Hpl" as "(Wd0 & Wl0 & Wf0 & Wn0 & Wd1 & Wl1 & Wf1 & Wn1 &
                         Wd2 & Wl2 & Wf2 & Wn2 & Wo0 & Wo1 & Wo2 & Wbuf & _)".
    iDestruct (vdrwf_w8b (d_desc pd h) (d_ops h : SailStdpp.Values.mword 64)
                 (vdrwf_desc_align pd h Hald Hh8)
                 (vdrwd_off_static pd _ (16 * h)%nat 8 eq_refl Bh1 Hspd)
                 (vdrwf_off_canon pd _ (16 * h)%nat 8 eq_refl Bh1 Hcpd)
                 with "Hkm Wd0") as "Wd0".
    iDestruct (vdrwf_w4b (pa_add pd (16 * h + 8)) (Z_to_bv 32 16)
                 (vdrwf_dlen_align pd h Hald Hh8)
                 (vdrwd_off_static pd _ (16 * h + 8)%nat 4 eq_refl Bh2 Hspd)
                 (vdrwf_off_canon pd _ (16 * h + 8)%nat 4 eq_refl Bh2 Hcpd)
                 with "Hkm Wl0") as "Wl0".
    iDestruct (vdrwf_w2b (pa_add pd (16 * h + 12)) (Z_to_bv 16 1)
                 (vdrwf_dflags_align pd h Hald Hh8)
                 (vdrwd_off_static pd _ (16 * h + 12)%nat 2 eq_refl Bh3 Hspd)
                 (vdrwf_off_canon pd _ (16 * h + 12)%nat 2 eq_refl Bh3 Hcpd)
                 with "Hkm Wf0") as "Wf0".
    iDestruct (vdrwf_w2b (pa_add pd (16 * h + 14)) (Z_to_bv 16 (Z.of_nat m2))
                 (vdrwf_dnext_align pd h Hald Hh8)
                 (vdrwd_off_static pd _ (16 * h + 14)%nat 2 eq_refl Bh4 Hspd)
                 (vdrwf_off_canon pd _ (16 * h + 14)%nat 2 eq_refl Bh4 Hcpd)
                 with "Hkm Wn0") as "Wn0".
    iDestruct (vdrwf_w8b (d_desc pd m2) (b_data b : SailStdpp.Values.mword 64)
                 (vdrwf_desc_align pd m2 Hald Hm8)
                 (vdrwd_off_static pd _ (16 * m2)%nat 8 eq_refl Bm1 Hspd)
                 (vdrwf_off_canon pd _ (16 * m2)%nat 8 eq_refl Bm1 Hcpd)
                 with "Hkm Wd1") as "Wd1".
    iDestruct (vdrwf_w4b (pa_add pd (16 * m2 + 8)) (Z_to_bv 32 1024)
                 (vdrwf_dlen_align pd m2 Hald Hm8)
                 (vdrwd_off_static pd _ (16 * m2 + 8)%nat 4 eq_refl Bm2 Hspd)
                 (vdrwf_off_canon pd _ (16 * m2 + 8)%nat 4 eq_refl Bm2 Hcpd)
                 with "Hkm Wl1") as "Wl1".
    iDestruct (vdrwf_w2b (pa_add pd (16 * m2 + 12)) (vdrw_flags wr)
                 (vdrwf_dflags_align pd m2 Hald Hm8)
                 (vdrwd_off_static pd _ (16 * m2 + 12)%nat 2 eq_refl Bm3 Hspd)
                 (vdrwf_off_canon pd _ (16 * m2 + 12)%nat 2 eq_refl Bm3 Hcpd)
                 with "Hkm Wf1") as "Wf1".
    iDestruct (vdrwf_w2b (pa_add pd (16 * m2 + 14)) (Z_to_bv 16 (Z.of_nat t))
                 (vdrwf_dnext_align pd m2 Hald Hm8)
                 (vdrwd_off_static pd _ (16 * m2 + 14)%nat 2 eq_refl Bm4 Hspd)
                 (vdrwf_off_canon pd _ (16 * m2 + 14)%nat 2 eq_refl Bm4 Hcpd)
                 with "Hkm Wn1") as "Wn1".
    iDestruct (vdrwf_w8b (d_desc pd t) (d_info_status h : SailStdpp.Values.mword 64)
                 (vdrwf_desc_align pd t Hald Ht8)
                 (vdrwd_off_static pd _ (16 * t)%nat 8 eq_refl Bt1 Hspd)
                 (vdrwf_off_canon pd _ (16 * t)%nat 8 eq_refl Bt1 Hcpd)
                 with "Hkm Wd2") as "Wd2".
    iDestruct (vdrwf_w4b (pa_add pd (16 * t + 8)) (Z_to_bv 32 1)
                 (vdrwf_dlen_align pd t Hald Ht8)
                 (vdrwd_off_static pd _ (16 * t + 8)%nat 4 eq_refl Bt2 Hspd)
                 (vdrwf_off_canon pd _ (16 * t + 8)%nat 4 eq_refl Bt2 Hcpd)
                 with "Hkm Wl2") as "Wl2".
    iDestruct (vdrwf_w2b (pa_add pd (16 * t + 12)) (Z_to_bv 16 2)
                 (vdrwf_dflags_align pd t Hald Ht8)
                 (vdrwd_off_static pd _ (16 * t + 12)%nat 2 eq_refl Bt3 Hspd)
                 (vdrwf_off_canon pd _ (16 * t + 12)%nat 2 eq_refl Bt3 Hcpd)
                 with "Hkm Wf2") as "Wf2".
    iDestruct (vdrwf_w2b (pa_add pd (16 * t + 14)) (Z_to_bv 16 0)
                 (vdrwf_dnext_align pd t Hald Ht8)
                 (vdrwd_off_static pd _ (16 * t + 14)%nat 2 eq_refl Bt4 Hspd)
                 (vdrwf_off_canon pd _ (16 * t + 14)%nat 2 eq_refl Bt4 Hcpd)
                 with "Hkm Wn2") as "Wn2".
    iDestruct (vdrwf_w4b (d_ops h) (vdrw_ty wr) (vdrwf_ops_align h Hh8)
                 (vdrwd_off_static disk_base _ (168 + 16 * h)%nat 4 eq_refl Bh5
                    vdrwd_disk_static)
                 (vdrwf_off_canon disk_base _ (168 + 16 * h)%nat 4 eq_refl Bh5
                    vdrwf_disk_canon)
                 with "Hkm Wo0") as "Wo0".
    iDestruct (vdrwf_w4b (pa_add disk_base (168 + 16 * h + 4))
                 (SailStdpp.Values.mword_of_int (len := 32) 0) (vdrwf_opsr_align h Hh8)
                 (vdrwd_off_static disk_base _ (168 + 16 * h + 4)%nat 4 eq_refl Bh6
                    vdrwd_disk_static)
                 (vdrwf_off_canon disk_base _ (168 + 16 * h + 4)%nat 4 eq_refl Bh6
                    vdrwf_disk_canon)
                 with "Hkm Wo1") as "Wo1".
    iDestruct (vdrwf_w8b (pa_add disk_base (168 + 16 * h + 8)) sector
                 (vdrwf_opss_align h Hh8)
                 (vdrwd_off_static disk_base _ (168 + 16 * h + 8)%nat 8 eq_refl Bh7
                    vdrwd_disk_static)
                 (vdrwf_off_canon disk_base _ (168 + 16 * h + 8)%nat 8 eq_refl Bh7
                    vdrwf_disk_canon)
                 with "Hkm Wo2") as "Wo2".
    (* premises by NAME, not spliced in as [ltac:(…)]: the proofmode
       re-elaborates a spliced term without the [Qed] vm-seal, and these two
       cost 3.9 s in that position against ~0.1 s hoisted.  optimization.md. *)
    assert (Hstatst : kmap_static (svpn_of (d_info_status h)) KP_rw)
      by (unfold d_info_status; apply vdrwd_disk_static; lia).
    assert (Hcanst : (uint (d_info_status h : SailStdpp.Values.mword 64)
                      < 274877906944)%Z)
      by (unfold d_info_status; apply vdrwf_disk_canon; lia).
    iDestruct (phys_to_byte (d_info_status h) byte_zero Hstatst Hcanst
                 with "Hkm Hstat") as "Hstat".
    (* ================= +0x1d2 .. +0x1f0 ============================== *)
    iPoseProof (rwi_1d2 with "Htext") as "Hi1b0".
    iPoseProof (rwi_1d6 with "Htext") as "Hi1b4".
    iPoseProof (rwi_1da with "Htext") as "Hi1b8".
    iPoseProof (rwi_1de with "Htext") as "Hi1bc".
    iPoseProof (rwi_1e2 with "Htext") as "Hi1c0".
    iPoseProof (rwi_1e6 with "Htext") as "Hi1c4".
    iPoseProof (rwi_1e8 with "Htext") as "Hi1c6".
    iPoseProof (rwi_1ec with "Htext") as "Hi1ca".
    iPoseProof (rwi_1f0 with "Htext") as "Hi1ce".
    iDestruct "Hidx" as "(Hx0 & Hx1 & Hx2 & Hxp)".
    assert (Hidxa : add_vec (M !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4000 : mword 12))
                    = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite Hs0; apply vdrw_idx0_addr).
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1d2) : mword 64) Rs2 Rs0
              (mword_of_int 4000 : mword 12) M (trap_res eb + (K - 12))%nat
              (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 32) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1b0 [Hx0] [-]").
    { rgall. iEval (rewrite Hidxa). iExact "Hx0". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hx0". rgall.
    iEval (rewrite Hidxa) in "Hx0".
    set (E1 := <[Regidx Rs2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat h)
                                     : SailStdpp.Values.mword 32))]> M).
    change (<[Regidx Rs2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat h)
                                     : SailStdpp.Values.mword 32))]> M) with E1.
    assert (HE1s2 : E1 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64)).
    { rewrite /E1 upd_eq. exact (vdrwc_sext32 h Hh8). }
    assert (Hp1b4 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1d2) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1d6)) by pcstep.
    iEval (rewrite Hp1b4) in "Hpc".
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1d6) : mword 64) Ra4 Rs2
              (mword_of_int 4 : mword 6)
              (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64) E1 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgall; rewrite HE1s2; exact (vdrwc_slli4' h Hh8))
              with "Hcg Hpc Hi1b4 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E2 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> E1).
    change (<[Regidx Ra4 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> E1) with E2.
    assert (Hp1b8 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1d6) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1da)) by pcstep.
    iEval (rewrite Hp1b8) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1da) : mword 64) Ra4 Ra4
              (mword_of_int 32 : mword 12) E2 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1b8 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E3 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (E2 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 32 : mword 12)))]> E2).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (E2 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 32 : mword 12)))]> E2) with E3.
    assert (HE3a4 : E3 !!! Regidx Ra4
                    = add_vec (mword_of_int (16 * Z.of_nat h)
                                : SailStdpp.Values.mword 64)
                              (sign_extend' 64 (mword_of_int 32 : mword 12))).
    { rewrite /E3 upd_eq /E2 upd_eq. reflexivity. }
    assert (Hp1bc : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1da) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1de)) by pcstep.
    iEval (rewrite Hp1bc) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1de) : mword 64) Ra5
              (mword_of_int 30 : mword 20) E3 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1bc [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1de) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> E3).
    change (<[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1de) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> E3) with E4.
    assert (Hp1c0 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1de) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1e2)) by pcstep.
    iEval (rewrite Hp1c0) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1e2) : mword 64) Ra5 Ra5
              (mword_of_int 2722 : mword 12) E4 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c0 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (E4 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 2722 : mword 12)))]> E4).
    change (<[Regidx Ra5 := regval_into_reg
                  (add_vec (E4 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 2722 : mword 12)))]> E4) with E5.
    assert (HE5a5 : E5 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /E5 upd_eq /E4 upd_eq. exact vdrwf_a5disk. }
    assert (HE5a4 : E5 !!! Regidx Ra4
                    = add_vec (mword_of_int (16 * Z.of_nat h)
                                : SailStdpp.Values.mword 64)
                              (sign_extend' 64 (mword_of_int 32 : mword 12))).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq]. exact HE3a4. }
    assert (Hp1c4 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1e2) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1e6)) by pcstep.
    iEval (rewrite Hp1c4) in "Hpc".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1e6) : mword 64) Ra5 Ra4 E5
              (trap_res eb + (K - 12))%nat false ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi1c4 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E6 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (E5 !!! Regidx Ra5) (E5 !!! Regidx Ra4))]> E5).
    change (<[Regidx Ra5 := regval_into_reg
                  (add_vec (E5 !!! Regidx Ra5) (E5 !!! Regidx Ra4))]> E5) with E6.
    assert (Hp1c6 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1e6) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1e8)) by pcstep.
    iEval (rewrite Hp1c6) in "Hpc".
    assert (Hiba : add_vec (E6 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (d_info_b h : SailStdpp.Values.mword 64)).
    { rewrite /E6 upd_eq HE5a5 HE5a4. apply vdrwf_infob_addr. }
    iApply (wp_sd_zero_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1e8) : mword 64) Ra5
              (mword_of_int 8 : mword 12) E6 (trap_res eb + (K - 12))%nat
              (b : SailStdpp.Values.mword 64) false
              with "Hcg Hpc Hi1c6 [Hinfob] [-]").
    { rgall. iEval (rewrite Hiba). iExact "Hinfob". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hinfob". rgall.
    iEval (rewrite Hiba) in "Hinfob".
    assert (Hp1ca : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1e8) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1ec)) by pcstep.
    iEval (rewrite Hp1ca) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ec) : mword 64) Rs3
              (mword_of_int 30 : mword 20) E6 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1ca [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E7 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ec) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> E6).
    change (<[Regidx Rs3 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ec) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> E6) with E7.
    assert (Hp1ce : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ec) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1f0)) by pcstep.
    iEval (rewrite Hp1ce) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1f0) : mword 64) Rs3 Rs3
              (mword_of_int 2708 : mword 12) E7 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1ce [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (E8 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (E7 !!! Regidx Rs3)
                     (sign_extend' 64 (mword_of_int 2708 : mword 12)))]> E7).
    change (<[Regidx Rs3 := regval_into_reg
                  (add_vec (E7 !!! Regidx Rs3)
                     (sign_extend' 64 (mword_of_int 2708 : mword 12)))]> E7) with E8.
    assert (HE8s3 : E8 !!! Regidx Rs3 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /E8 upd_eq /E7 upd_eq. exact vdrwf_s3disk. }
    assert (HE8s2 : E8 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64)).
    { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. exact HE1s2. }
    assert (HE8s0 : E8 !!! Regidx Rs0 = (sp0 : SailStdpp.Values.mword 64)).
    { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq]. exact Hs0. }
    assert (HE8sp : E8 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64)).
    { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq]. exact Hsp. }
    assert (Hp1d2 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1f0) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1f4)) by pcstep.
    iEval (rewrite Hp1d2) in "Hpc".
    iAssert (vdrw_slot_rest h) with "[Wo0 Wo1 Wo2 Hstat Hinfob]" as "Hrh".
    { rewrite /vdrw_slot_rest /ops_own.
      iSplitL "Wo0 Wo1 Wo2".
      { iExists (vdrw_ty wr), (SailStdpp.Values.mword_of_int (len := 32) 0), sector.
        iFrame "Wo0 Wo1 Wo2". }
      iSplitL "Hstat"; [iExists byte_zero; iExact "Hstat"|].
      iExists (zero_reg : SailStdpp.Values.mword 64). iExact "Hinfob". }
    (* ================= the three free_chain iterations ================ *)
    iPoseProof (rwi_20c with "Htext") as "Hi1ea".
    iPoseProof (rwi_20e with "Htext") as "Hi1ec".
    assert (Hbrk : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x20e) : mword 64)
                     (sign_extend' 64 (sign_extend' 13
                        (concat_vec (mword_of_int 243 : mword 8) ('b"0"))))
                   = mword_of_int (KernelSyms.virtio_disk_rw + 0x1f4)) by pcstep.
    assert (Hp1ec1 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x20c) : mword 64) 2
                     = mword_of_int (KernelSyms.virtio_disk_rw + 0x20e)) by pcstep.
    iApply (wp_vdrwf_iter (CID := CIDx)  γs pd h fr (d_ops h : SailStdpp.Values.mword 64)
              (Z_to_bv 32 16) (Z_to_bv 16 1) (Z_to_bv 16 (Z.of_nat m2))
              E8 (trap_res eb + (K - 12))%nat eb (proc_addr j) C
              ltac:(pose proof (vdrwb_K20 K HK); lia) Hh8 Hfrh Hglen HE8s2 HE8s3
              with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Wd0 Wl0 Wf0 Wn0 Hfb Hrh [-]").
    iIntros (F1) "%HF1 Hcg Hown Hpc Hfb".
    destruct HF1 as (HF1thr & HF1s1 & HF1s2).
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x20c) : mword 64) Rs1
              (mword_of_int 1 : mword 6) F1 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1ea [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G1 := <[Regidx Rs1 := regval_into_reg
                  (and_vec (F1 !!! Regidx Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> F1).
    change (<[Regidx Rs1 := regval_into_reg
                  (and_vec (F1 !!! Regidx Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> F1)
      with G1.
    iEval (rewrite Hp1ec1) in "Hpc".
    iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x20e) : mword 64)
              (mword_of_int 243 : mword 8) (Cregidx (mword_of_int 1)) Rs1 G1 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgall; rewrite /G1 upd_eq HF1s1; exact vdrwf_bit0_1)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1ec [-]").
    iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hbrk) in "Hpc".
    assert (HG1s2 : G1 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat m2) : SailStdpp.Values.mword 64)).
    { rewrite /G1 upd_ne; [| reg_neq]. rewrite HF1s2. exact (vdrwf_zext16 m2 Hm8). }
    assert (HG1s3 : G1 !!! Regidx Rs3 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /G1 upd_ne; [| reg_neq].
      rewrite (HF1thr Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      exact HE8s3. }
    assert (HG1s0 : G1 !!! Regidx Rs0 = (sp0 : SailStdpp.Values.mword 64)).
    { rewrite /G1 upd_ne; [| reg_neq].
      rewrite (HF1thr Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      exact HE8s0. }
    assert (HG1sp : G1 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64)).
    { rewrite /G1 upd_ne; [| reg_neq].
      rewrite (HF1thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      exact HE8sp. }
    assert (Hfr1m : fr_upd fr h true m2 = false)
      by (rewrite (fr_upd_ne fr h m2 true (not_eq_sym Hhm)); exact Hfrm).
    iApply (wp_vdrwf_iter (CID := CIDx)  γs pd m2 (fr_upd fr h true)
              (b_data b : SailStdpp.Values.mword 64)
              (Z_to_bv 32 1024) (vdrw_flags wr) (Z_to_bv 16 (Z.of_nat t))
              G1 (trap_res eb + (K - 12))%nat eb (proc_addr j) C
              ltac:(pose proof (vdrwb_K20 K HK); lia) Hm8 Hfr1m Hglen HG1s2 HG1s3
              with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Wd1 Wl1 Wf1 Wn1 Hfb Hrm [-]").
    iIntros (F2) "%HF2 Hcg Hown Hpc Hfb".
    destruct HF2 as (HF2thr & HF2s1 & HF2s2).
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x20c) : mword 64) Rs1
              (mword_of_int 1 : mword 6) F2 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1ea [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G2 := <[Regidx Rs1 := regval_into_reg
                  (and_vec (F2 !!! Regidx Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> F2).
    change (<[Regidx Rs1 := regval_into_reg
                  (and_vec (F2 !!! Regidx Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> F2)
      with G2.
    iEval (rewrite Hp1ec1) in "Hpc".
    iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x20e) : mword 64)
              (mword_of_int 243 : mword 8) (Cregidx (mword_of_int 1)) Rs1 G2 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgall; rewrite /G2 upd_eq HF2s1; exact (vdrwf_bit0_flags wr))
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1ec [-]").
    iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hbrk) in "Hpc".
    assert (HG2s2 : G2 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat t) : SailStdpp.Values.mword 64)).
    { rewrite /G2 upd_ne; [| reg_neq]. rewrite HF2s2. exact (vdrwf_zext16 t Ht8). }
    assert (HG2s3 : G2 !!! Regidx Rs3 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /G2 upd_ne; [| reg_neq].
      rewrite (HF2thr Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      exact HG1s3. }
    assert (HG2s0 : G2 !!! Regidx Rs0 = (sp0 : SailStdpp.Values.mword 64)).
    { rewrite /G2 upd_ne; [| reg_neq].
      rewrite (HF2thr Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      exact HG1s0. }
    assert (HG2sp : G2 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64)).
    { rewrite /G2 upd_ne; [| reg_neq].
      rewrite (HF2thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      exact HG1sp. }
    assert (Hfr2t : fr_upd (fr_upd fr h true) m2 true t = false).
    { rewrite (fr_upd_ne (fr_upd fr h true) m2 t true (not_eq_sym Hmt)).
      rewrite (fr_upd_ne fr h t true (not_eq_sym Hht)). exact Hfrt. }
    iApply (wp_vdrwf_iter (CID := CIDx)  γs pd t (fr_upd (fr_upd fr h true) m2 true)
              (d_info_status h : SailStdpp.Values.mword 64)
              (Z_to_bv 32 1) (Z_to_bv 16 2) (Z_to_bv 16 0)
              G2 (trap_res eb + (K - 12))%nat eb (proc_addr j) C
              ltac:(pose proof (vdrwb_K20 K HK); lia) Ht8 Hfr2t Hglen HG2s2 HG2s3
              with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Wd2 Wl2 Wf2 Wn2 Hfb Hrt [-]").
    iIntros (F3) "%HF3 Hcg Hown Hpc Hfb".
    destruct HF3 as (HF3thr & HF3s1 & HF3s2).
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x20c) : mword 64) Rs1
              (mword_of_int 1 : mword 6) F3 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1ea [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G3 := <[Regidx Rs1 := regval_into_reg
                  (and_vec (F3 !!! Regidx Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> F3).
    change (<[Regidx Rs1 := regval_into_reg
                  (and_vec (F3 !!! Regidx Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> F3)
      with G3.
    iEval (rewrite Hp1ec1) in "Hpc".
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x20e) : mword 64)
              (mword_of_int 243 : mword 8) (Cregidx (mword_of_int 1)) Rs1 G3 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgall; rewrite /G3 upd_eq HF3s1; exact vdrwf_bit0_2)
              with "Hcg Hpc Hi1ec [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp1ee : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x20e) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x210)) by pcstep.
    iEval (rewrite Hp1ee) in "Hpc".
    assert (HG3sp : G3 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64)).
    { rewrite /G3 upd_ne; [| reg_neq].
      rewrite (HF3thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      exact HG2sp. }
    (* ================= the lock resource, re-folded =================== *)
    set (fr' := fr_upd (fr_upd (fr_upd fr h true) m2 true) t true).
    assert (Hfr'other : forall i, i <> h -> i <> m2 -> i <> t -> fr' i = fr i).
    { intros i N1 N2 N3. rewrite /fr' (fr_upd_ne _ t i true N3)
        (fr_upd_ne _ m2 i true N2) (fr_upd_ne fr h i true N1). reflexivity. }
    iAssert (disk_res γd pd pav pu)
      with "[Hpub Hcl Huidx Hflm Hpkm Hfb Hring]" as "HR".
    { iApply (vdrw_body_close γd pd pav pu np nr fl (delete q pk) (delete q tr) fr').
      rewrite /vdrw_body.
      iSplitR; [iPureIntro; exact Hdfl|].
      iSplitR.
      { iPureIntro. intros p Hp. apply Hpkb.
        rewrite dom_delete_L in Hp. apply elem_of_difference in Hp as [Hp _]. exact Hp. }
      iSplitR.
      { iPureIntro. rewrite !dom_delete_L.
        exact (vdrwf_dom_delete q (dom fl) (dom pk) (dom tr) Hdtr Hnflq). }
      iSplitR.
      { iPureIntro. intros p v Hp.
        assert (Hpq' : p <> q).
        { intro Hc. subst p. rewrite (lookup_union_r fl (delete q pk) q Hflq) in Hp.
          rewrite lookup_delete in Hp. discriminate. }
        rewrite (lookup_delete_ne tr q p (not_eq_sym Hpq')). apply Hcoh.
        destruct (fl !! p) as [w|] eqn:Hfp.
        - rewrite (lookup_union_Some_l fl pk p w Hfp).
          rewrite (lookup_union_Some_l fl (delete q pk) p w Hfp) in Hp. exact Hp.
        - rewrite (lookup_union_r fl pk p Hfp).
          rewrite (lookup_union_r fl (delete q pk) p Hfp) in Hp.
          rewrite (lookup_delete_ne pk q p (not_eq_sym Hpq')) in Hp. exact Hp. }
      iSplitR.
      { iPureIntro. intros p T Hp.
        apply lookup_delete_Some in Hp as [_ Hp]. exact (Htrok p T Hp). }
      iSplitR.
      { iPureIntro. intros p p' Tp Tq Hne Hp Hp'.
        apply lookup_delete_Some in Hp as [_ Hp].
        apply lookup_delete_Some in Hp' as [_ Hp'].
        exact (Htrdj p p' Tp Tq Hne Hp Hp'). }
      iSplitR.
      { iPureIntro. intros p T i Hp Hi.
        apply lookup_delete_Some in Hp as [Hpne Hp].
        pose proof (Htrdj p q T (h, m2, t) (not_eq_sym Hpne) Hp Htrq) as Hdj.
        assert (Hnh : i <> h)
          by (intro Hc; subst i; exact (proj1 (elem_of_disjoint _ _) Hdj h Hi Hinh)).
        assert (Hnm : i <> m2)
          by (intro Hc; subst i; exact (proj1 (elem_of_disjoint _ _) Hdj m2 Hi Hinm)).
        assert (Hnt : i <> t)
          by (intro Hc; subst i; exact (proj1 (elem_of_disjoint _ _) Hdj t Hi Hint)).
        rewrite (Hfr'other i Hnh Hnm Hnt). exact (Htrfr p T i Hp Hi). }
      iFrame "Hpub Hlb Hcl Huidx Hflm Hpkm Hfb Hring". }
    (* ================= +0x210 .. +0x218: release ====================== *)
    iPoseProof (rwi_210 with "Htext") as "Hi1ee".
    iPoseProof (rwi_214 with "Htext") as "Hi1f2".
    iPoseProof (rwi_218 with "Htext") as "Hi1f6".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x210) : mword 64) Ra0
              (mword_of_int 30 : mword 20) G3 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1ee [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (H1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x210) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> G3).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x210) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> G3) with H1.
    assert (Hp1f2 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x210) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x214)) by pcstep.
    iEval (rewrite Hp1f2) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x214) : mword 64) Ra0 Ra0
              (mword_of_int 2968 : mword 12) H1 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1f2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (H2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (H1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 2968 : mword 12)))]> H1).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (H1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 2968 : mword 12)))]> H1) with H2.
    assert (HH2a0 : H2 !!! Regidx Ra0 = (d_lock : SailStdpp.Values.mword 64)).
    { rewrite /H2 upd_eq /H1 upd_eq. exact vdrwf_a0lock. }
    assert (Hp1f6 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x214) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x218)) by pcstep.
    iEval (rewrite Hp1f6) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x218) : mword 64) Rra
              (mword_of_int 2077240 : mword 21) H2 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1f6 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (H3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x218) : mword 64) 4)]> H2).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x218) : mword 64) 4)]> H2) with H3.
    iEval (rewrite vdrwf_jrel) in "Hpc".
    assert (HH3a0 : add_vec (H3 !!! Regidx Ra0)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = (d_lock : SailStdpp.Values.mword 64)).
    { rewrite /H3 upd_ne; [| reg_neq]. rewrite HH2a0. apply vdrw_addv_sext0. }
    assert (HH3ra : H3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x218) : mword 64) 4)
      by (rewrite /H3; apply upd_eq).
    assert (HH3sp : H3 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64)).
    { rewrite /H3 upd_ne; [| reg_neq]. rewrite /H2 upd_ne; [| reg_neq].
      rewrite /H1 upd_ne; [| reg_neq]. exact HG3sp. }
    iApply (Release.wp_release_sconf (CID := CIDx) γk d_lock "virtio_disk"%string
              (disk_res γd pd pav pu) H3 0%nat eb (proc_addr j) C (K - 12)%nat
              HH3a0 ltac:(pose proof (vdrw_K10 K HK); lia)
              with "Hcg Htext Hpc Hlk Htok HR Hown Hpay [-]").
    iIntros (CIDr Hsr MR) "Hcg Hpc %HcsR Hown".
    assert (Hp1fa : ret_pc (H3 !!! Regidx Rra) = mword_of_int (KernelSyms.virtio_disk_rw + 0x21c))
      by (rewrite HH3ra; pcstep).
    iEval (rewrite Hp1fa) in "Hpc".
    assert (HMRsp : MR !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite (callee_saved_lookup HcsR csp_rs1 ltac:(vm_compute; reflexivity)); exact HH3sp).
    (* ================= the epilogue =================================== *)
    rewrite /vdrw_saved.
    iDestruct "Hsaved" as "(Hk1 & Hk2 & Hk3 & Hk4 & Hk5 & Hk6 & Hk7 & Hk8 & Hk9 & Hk10)".
    assert (Hb1 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = (pa_stk sp0 1 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = (pa_stk sp0 2 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = (pa_stk sp0 3 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = (pa_stk sp0 4 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb5 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = (pa_stk sp0 5 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb6 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = (pa_stk sp0 6 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb7 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = (pa_stk sp0 7 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb8 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = (pa_stk sp0 8 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb9 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = (pa_stk sp0 9 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb10 : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = (pa_stk sp0 10 : SailStdpp.Values.mword 64)).
    { unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (rwi_21c with "Htext") as "Hj1".
    iPoseProof (rwi_21e with "Htext") as "Hj2".
    iPoseProof (rwi_220 with "Htext") as "Hj3".
    iPoseProof (rwi_222 with "Htext") as "Hj4".
    iPoseProof (rwi_224 with "Htext") as "Hj5".
    iPoseProof (rwi_226 with "Htext") as "Hj6".
    iPoseProof (rwi_228 with "Htext") as "Hj7".
    iPoseProof (rwi_22a with "Htext") as "Hj8".
    iPoseProof (rwi_22c with "Htext") as "Hj9".
    iPoseProof (rwi_22e with "Htext") as "Hj10".
    iPoseProof (rwi_230 with "Htext") as "Hj11".
    iPoseProof (rwi_232 with "Htext") as "Hj12".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x21c) : mword 64)
              (mword_of_int 11 : mword 6) Rra MR (K - 12)%nat (m !!! Regidx Rra) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj1 [Hk1] [-]").
    { rgall. iEval (rewrite HMRsp Hb1). iExact "Hk1". }
    iIntros (CIDp1 Hsp1) "Hcg Hpc Hk1". rgall. iEval (rewrite HMRsp Hb1) in "Hk1".
    set (R1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> MR).
    change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> MR) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R1 upd_ne; [| reg_neq]; exact HMRsp).
    assert (Hq2 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x21c) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x21e)) by pcstep.
    iEval (rewrite Hq2) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x21e) : mword 64)
              (mword_of_int 10 : mword 6) Rs0 R1 (K - 12)%nat (m !!! Regidx Rs0) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj2 [Hk2] [-]").
    { rgall. iEval (rewrite HR1sp Hb2). iExact "Hk2". }
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hk2". rgall. iEval (rewrite HR1sp Hb2) in "Hk2".
    set (R2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> R1).
    change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> R1) with R2.
    assert (HR2sp : R2 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R2 upd_ne; [| reg_neq]; exact HR1sp).
    assert (Hq3 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x21e) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x220)) by pcstep.
    iEval (rewrite Hq3) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x220) : mword 64)
              (mword_of_int 9 : mword 6) Rs1 R2 (K - 12)%nat (m !!! Regidx Rs1) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj3 [Hk3] [-]").
    { rgall. iEval (rewrite HR2sp Hb3). iExact "Hk3". }
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hk3". rgall. iEval (rewrite HR2sp Hb3) in "Hk3".
    set (R3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> R2).
    change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> R2) with R3.
    assert (HR3sp : R3 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R3 upd_ne; [| reg_neq]; exact HR2sp).
    assert (Hq4 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x220) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x222)) by pcstep.
    iEval (rewrite Hq4) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x222) : mword 64)
              (mword_of_int 8 : mword 6) Rs2 R3 (K - 12)%nat (m !!! Regidx Rs2) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj4 [Hk4] [-]").
    { rgall. iEval (rewrite HR3sp Hb4). iExact "Hk4". }
    iIntros (CIDp4 Hsp4) "Hcg Hpc Hk4". rgall. iEval (rewrite HR3sp Hb4) in "Hk4".
    set (R4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> R3).
    change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> R3) with R4.
    assert (HR4sp : R4 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R4 upd_ne; [| reg_neq]; exact HR3sp).
    assert (Hq5 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x222) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x224)) by pcstep.
    iEval (rewrite Hq5) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x224) : mword 64)
              (mword_of_int 7 : mword 6) Rs3 R4 (K - 12)%nat (m !!! Regidx Rs3) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj5 [Hk5] [-]").
    { rgall. iEval (rewrite HR4sp Hb5). iExact "Hk5". }
    iIntros (CIDp5 Hsp5) "Hcg Hpc Hk5". rgall. iEval (rewrite HR4sp Hb5) in "Hk5".
    set (R5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> R4).
    change (<[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> R4) with R5.
    assert (HR5sp : R5 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R5 upd_ne; [| reg_neq]; exact HR4sp).
    assert (Hq6 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x224) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x226)) by pcstep.
    iEval (rewrite Hq6) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x226) : mword 64)
              (mword_of_int 6 : mword 6) Rs4 R5 (K - 12)%nat (m !!! Regidx Rs4) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj6 [Hk6] [-]").
    { rgall. iEval (rewrite HR5sp Hb6). iExact "Hk6". }
    iIntros (CIDp6 Hsp6) "Hcg Hpc Hk6". rgall. iEval (rewrite HR5sp Hb6) in "Hk6".
    set (R6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> R5).
    change (<[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> R5) with R6.
    assert (HR6sp : R6 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R6 upd_ne; [| reg_neq]; exact HR5sp).
    assert (Hq7 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x226) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x228)) by pcstep.
    iEval (rewrite Hq7) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x228) : mword 64)
              (mword_of_int 5 : mword 6) Rs5 R6 (K - 12)%nat (m !!! Regidx Rs5) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj7 [Hk7] [-]").
    { rgall. iEval (rewrite HR6sp Hb7). iExact "Hk7". }
    iIntros (CIDp7 Hsp7) "Hcg Hpc Hk7". rgall. iEval (rewrite HR6sp Hb7) in "Hk7".
    set (R7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> R6).
    change (<[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> R6) with R7.
    assert (HR7sp : R7 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R7 upd_ne; [| reg_neq]; exact HR6sp).
    assert (Hq8 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x228) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x22a)) by pcstep.
    iEval (rewrite Hq8) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x22a) : mword 64)
              (mword_of_int 4 : mword 6) Rs6 R7 (K - 12)%nat (m !!! Regidx Rs6) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj8 [Hk8] [-]").
    { rgall. iEval (rewrite HR7sp Hb8). iExact "Hk8". }
    iIntros (CIDp8 Hsp8) "Hcg Hpc Hk8". rgall. iEval (rewrite HR7sp Hb8) in "Hk8".
    set (R8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> R7).
    change (<[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> R7) with R8.
    assert (HR8sp : R8 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R8 upd_ne; [| reg_neq]; exact HR7sp).
    assert (Hq9 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x22a) : mword 64) 2
                  = mword_of_int (KernelSyms.virtio_disk_rw + 0x22c)) by pcstep.
    iEval (rewrite Hq9) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x22c) : mword 64)
              (mword_of_int 3 : mword 6) Rs7 R8 (K - 12)%nat (m !!! Regidx Rs7) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj9 [Hk9] [-]").
    { rgall. iEval (rewrite HR8sp Hb9). iExact "Hk9". }
    iIntros (CIDp9 Hsp9) "Hcg Hpc Hk9". rgall. iEval (rewrite HR8sp Hb9) in "Hk9".
    set (R9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> R8).
    change (<[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> R8) with R9.
    assert (HR9sp : R9 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R9 upd_ne; [| reg_neq]; exact HR8sp).
    assert (Hq10 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x22c) : mword 64) 2
                   = mword_of_int (KernelSyms.virtio_disk_rw + 0x22e)) by pcstep.
    iEval (rewrite Hq10) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x22e) : mword 64)
              (mword_of_int 2 : mword 6) Rs8 R9 (K - 12)%nat (m !!! Regidx Rs8) eb
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hj10 [Hk10] [-]").
    { rgall. iEval (rewrite HR9sp Hb10). iExact "Hk10". }
    iIntros (CIDp10 Hsp10) "Hcg Hpc Hk10". rgall. iEval (rewrite HR9sp Hb10) in "Hk10".
    set (R10 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> R9).
    change (<[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> R9) with R10.
    assert (HR10sp : R10 !!! Regidx csp_rs1 = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite /R10 upd_ne; [| reg_neq]; exact HR9sp).
    assert (Hq11 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x22e) : mword 64) 2
                   = mword_of_int (KernelSyms.virtio_disk_rw + 0x230)) by pcstep.
    iEval (rewrite Hq11) in "Hpc".
    (* ---- +0x230  c.addi16sp sp,96 : the frame pop ---- *)
    iDestruct (vdrw_idx_join sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                 (mword_of_int (Z.of_nat t)) Hal11 Hal12 with "[Hx0 Hx1 Hx2 Hxp]")
      as "Hscratch".
    { rewrite /vdrw_idx. iFrame "Hx0 Hx1 Hx2 Hxp". }
    iDestruct "Hscratch" as (w11 w12) "[Hs11 Hs12]".
    assert (Hspup : add_vec (pa_stk sp0 12 : SailStdpp.Values.mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))
                    = (sp0 : SailStdpp.Values.mword 64)).
    { assert (H96 : sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))
                    = (mword_of_int 96 : SailStdpp.Values.mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite H96. unfold pa_stk, add_vec_int.
      rewrite (vdrw_av2 (sp0 : SailStdpp.Values.mword 64) (- (8 * Z.of_nat 12)) 96).
      rewrite vdrwf_pop_z. apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hwv : add_vec (R10 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))
                  = (sp0 : SailStdpp.Values.mword 64))
      by (rewrite HR10sp; exact Hspup).
    assert (Hpop : R10 !!! Regidx csp_rs1
                   = pa_stk (add_vec (R10 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12)
      by (rewrite Hwv; exact HR10sp).
    iAssert (stack_own sp0 12) with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10 Hs11 Hs12]"
      as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hk1";  [iExists _; iExact "Hk1"|].
      iSplitL "Hk2";  [iExists _; iExact "Hk2"|].
      iSplitL "Hk3";  [iExists _; iExact "Hk3"|].
      iSplitL "Hk4";  [iExists _; iExact "Hk4"|].
      iSplitL "Hk5";  [iExists _; iExact "Hk5"|].
      iSplitL "Hk6";  [iExists _; iExact "Hk6"|].
      iSplitL "Hk7";  [iExists _; iExact "Hk7"|].
      iSplitL "Hk8";  [iExists _; iExact "Hk8"|].
      iSplitL "Hk9";  [iExists _; iExact "Hk9"|].
      iSplitL "Hk10"; [iExists _; iExact "Hk10"|].
      iSplitL "Hs11"; [iExists _; iExact "Hs11"|].
      iSplitL "Hs12"; [iExists _; iExact "Hs12"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x230) : mword 64)
              (mword_of_int 6 : mword 6) R10 (K - 12)%nat 12 eb Hpop
              with "Hcg Hpc Hj11 Hframe [-]").
    iIntros (CIDp11 Hsp11) "Hcg Hpc". rgall.
    set (R11 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (R10 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> R10).
    change (<[Regidx csp_rs1 := regval_into_reg
                   (add_vec (R10 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> R10)
      with R11.
    (* [rewrite] needs an EQUATION, not an ltac-discharged inequality: this
       site re-spells the popped index [(K - 12) + 12] as [K].  (The carve
       sweep briefly turned this into [ltac:(...; lia)], which cannot elaborate
       -- there is no expected type for the term, so [lia] is handed an open
       goal and reports "Cannot find witness".) *)
    iEval (rewrite (vdrwf_Kk K HK)) in "Hcg".
    assert (Hq12 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x230) : mword 64) 2
                   = mword_of_int (KernelSyms.virtio_disk_rw + 0x232)) by pcstep.
    iEval (rewrite Hq12) in "Hpc".
    assert (HR11ra : R11 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
      rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
      rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
      rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1; apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x232) : mword 64) Rra R11 K eb
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hj12 [-]").
    iIntros (CIDp12 Hsp12) "Hcg Hpc". rgall.
    iEval (rewrite HR11ra) in "Hpc".
    (* ================= the spec's continuation ======================== *)
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 ->
              r <> Rs4 -> r <> Rs5 -> r <> Rs6 -> r <> Rs7 -> r <> Rs8 ->
              R11 !!! Regidx r = M !!! Regidx r).
    { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6 N7 N8.
      assert (Nra : r <> Rra)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (Na0 : r <> Ra0)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (Na4 : r <> Ra4)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (Na5 : r <> Ra5)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /R11 upd_ne; [| congruence]. rewrite /R10 upd_ne; [| congruence].
      rewrite /R9 upd_ne; [| congruence]. rewrite /R8 upd_ne; [| congruence].
      rewrite /R7 upd_ne; [| congruence]. rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence]. rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence]. rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsR r Hr).
      rewrite /H3 upd_ne; [| congruence]. rewrite /H2 upd_ne; [| congruence].
      rewrite /H1 upd_ne; [| congruence].
      rewrite /G3 upd_ne; [| congruence].
      rewrite (HF3thr r Hr N1 N2).
      rewrite /G2 upd_ne; [| congruence].
      rewrite (HF2thr r Hr N1 N2).
      rewrite /G1 upd_ne; [| congruence].
      rewrite (HF1thr r Hr N1 N2).
      rewrite /E8 upd_ne; [| congruence]. rewrite /E7 upd_ne; [| congruence].
      rewrite /E6 upd_ne; [| congruence]. rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence]. rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence]. rewrite /E1 upd_ne; [| congruence].
      reflexivity. }
    assert (Hcs : callee_saved m R11).
    { unfold callee_saved. split_and!.
      - rewrite /R11 upd_eq HR10sp Hspup. symmetry. exact Hsp0m.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
        rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
        rewrite /R3; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9; apply upd_eq.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10; apply upd_eq.
      - rewrite (Hthr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity));
          try reg_neq.
        exact (Hhi (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)).
      - rewrite (Hthr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity));
          try reg_neq.
        exact (Hhi (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)).
      - rewrite (Hthr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity));
          try reg_neq.
        exact (Hhi (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). }
    iAssert ([∗ list] k ↦ x ∈ vdrwd_sldata wr bs_buf bs_disk,
               pa_add (b_data b) k ↦ₘ x)%I with "[Wbuf Hbufp]" as "Hbufm".
    { destruct (vdrwd_out wr) eqn:Hout.
      - rewrite (Hsl_out eq_refl).
        iEval (rewrite (Hbufwin_out eq_refl)) in "Wbuf".
        iEval (rewrite -Hlenbuf) in "Wbuf".
        iDestruct (vdrwf_map_plist (b_data b) bs_buf
                     ltac:(rgall; rewrite Hlenbuf; exact vdrwf_1024_lt) with "Wbuf") as "Wbuf".
        iApply (vdrwf_plist_mem (b_data b) bs_buf
                  ltac:(rgall; rewrite Hlenbuf; exact Hsbuf)
                  ltac:(rgall; rewrite Hlenbuf; exact Hcbuf) with "Hkm Wbuf").
      - assert (Hbsd : bs = bs_disk)
          by (rewrite Hbs; exact (Hsl_in eq_refl)).
        rewrite (Hsl_in eq_refl) -Hbsd.
        iApply (vdrwf_plist_mem (b_data b) bs
                  ltac:(rgall; rewrite Hbsd Hlendisk; exact Hsbuf)
                  ltac:(rgall; rewrite Hbsd Hlendisk; exact Hcbuf) with "Hkm Hbufp"). }
    (* [Hown] stopped transporting for free the moment the epilogue's SIE
       index became the VARIABLE [eb] instead of the literal [true]: at
       [b = true], [cpu_own]'s payload sits entirely in [sie_arm true] and
       the hart drops out by reduction, but an abstract [eb] cannot reduce
       that way, so the hart change across release + the epilogue needs the
       same explicit transport as the complement below. *)
    iDestruct (cpu_own_transport CIDr CIDp12 0 eb (proc_addr j) C eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* the complement the release did not take, at the hart the epilogue
       ends on.  Free at both indices: [emp] at [eb = true], and at
       [eb = false] no step from the split onward could have moved the
       hart. *)
    iDestruct (trap_csrs_ext_transport CIDx CIDp12 eb (proc_addr j) ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDx CIDp12 eb (proc_addr j) ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iSpecialize ("Hcont" $! CIDp12 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! R11 with
              "[%] Hcg Hown Hextc Hextm Hpc [Hbno Hbdisk Hbufm] [Hdbytes] [HQ]").
    - exact Hcs.
    - rewrite /buf_own. iFrame "Hbno Hbdisk Hbufm".
      iPureIntro. exact Hlensl.
    - rewrite /disk_block. iSplitR; [iPureIntro; exact Hlensl|].
      iEval (rewrite Hbs) in "Hdbytes". iExact "Hdbytes".
    - (* the receipt.  Whatever laters survived the instruction stream since
         [perm_collect] ran, [▷ Q] is weaker, so this closes either way. *)
      iExact "HQ".
  Qed.
End VdrwfP6.

Section ProofVirtioDiskRwF.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Typeclasses Opaque cpu_own.

  (* ------------------------------------------------------------------- *)
  (* THE WHOLE FUNCTION: P1 -> P2 -> P3 -> P4 -> P5 -> P6.                 *)
  (*                                                                      *)
  (* Every phase but P1/P2 is packaged as a wand from ITS exit predicate   *)
  (* to its predecessor's, so the composition is a straight chain: apply   *)
  (* the prologue, then the allocator, then peel the seams inwards.        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_virtio_disk_rw_sconf
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : SailStdpp.Values.mword 64)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (bno dsk0 : SailStdpp.Values.mword 32) (bs_buf bs_disk : list (bv 8))
      (b : bool) (Q : iProp Σ)
    : wp_virtio_disk_rw_sconf_body γs j γl γu γd γk pd pav pu
                                   m K eb C bno dsk0 bs_buf bs_disk b Q.
  Proof.
    cbv beta zeta delta [wp_virtio_disk_rw_sconf_body].
    intros HK Hbnolt Hbufkd Hj Hjl.
    iIntros "Hcg Hown Hextc Hextm #Htext Hpc #Hpanic #Hpinv
             #Hdinv #Hgeom #Hlk Hbuf Hdisk Hperm Hcont".
    (* LEVEL 0 TIES THE TWO INDICES: [cpu_own_eb_agree] gives [eb = b]
       outright, so the function runs at ONE index throughout and there is
       nothing left to pin.  This used to derive [b = true] from an
       [eb = true] premise; with that premise gone the derivation is the
       agreement alone, which is what makes the [eb = false] instance live
       rather than vacuous. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm. cbn in Hbm. subst b.
    iPoseProof "Hpinv" as "Hpinv2".
    iDestruct "Hpinv2" as "[%Hglen _]".
    iDestruct "Hbuf" as "(Hbno & Hbdisk & %Hlenbuf & Hbufm)".
    iDestruct "Hdisk" as "[%Hlendisk Hdb]".
    iAssert (disk_block γd (uint bno) bs_disk) with "[Hdb]" as "Hdisk".
    { rewrite /disk_block. iSplitR; [iPureIntro; exact Hlendisk|]. iExact "Hdb". }
    (* ======== DEPOSIT THE CRASH PERMIT (PermInv.v) ==================== *)
    (* Before any of the request is formatted: the channel chooses the key
       [kq], which then travels INSIDE the published slot ([vs_perm]) so the
       DMA completion can find the view shift and this proof can find its
       receipt after the wake.  A plain fupd -- no program step is needed,
       because a deposit only ADDS under the invariant's later. *)
    iDestruct (dev_inv_perm with "Hdinv") as "#Hqinv".
    iApply fupd_wp.
    iMod (perm_deposit_kq gen_id (dn_perm γd) _ Q ⊤ ltac:(solve_ndisj)
            with "Hqinv Hperm") as (kq) "[Hpend #Hrcpt]".
    iModIntro.
    (* the permit's INDEX, restated in the pin layer's vocabulary: the spec
       states it as "this call's own block", the publish needs it as the
       published slot's [vs_wr]. *)
    assert (Hpermidx :
      (if negb (eq_vec (m !!! Regidx Ra1) (zero_reg : SailStdpp.Values.mword 64))
       then Some ((1024 * uint bno)%Z, bs_buf) else None)
      = vdrwd_wr (m !!! Regidx Ra1) (1024 * uint bno)%Z bs_buf).
    { unfold vdrwd_wr. rewrite (vdrwf_out_iff (m !!! Regidx Ra1)). reflexivity. }
    iEval (rewrite Hpermidx) in "Hpend".
    assert (Hsecval : (bv_unsigned (vdrw_sector_raw bno) * 512)%Z
                      = (1024 * uint bno)%Z).
    { rewrite (vdrwd_sector_raw_val bno Hbnolt). apply vdrwf_sec512. }
    assert (Hsld : vdrwd_sldata (m !!! Regidx Ra1) bs_buf bs_disk
                   = if negb (eq_vec (m !!! Regidx Ra1)
                                (zero_reg : SailStdpp.Values.mword 64))
                     then bs_buf else bs_disk).
    { unfold vdrwd_sldata. rewrite (vdrwf_out_iff (m !!! Regidx Ra1)). reflexivity. }
    assert (Hpc0 : (mword_of_int KernelSyms.virtio_disk_rw
                     : SailStdpp.Values.mword 64)
                   = (mword_of_int (KernelSyms.virtio_disk_rw + 0x000) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0) in "Hpc".
    (* ---- P1: prologue + acquire ---- *)
    iApply (P1.wp_vdrw_p1 γd γk pd pav pu m K eb (proc_addr j) C bno HK
              with "Hcg Hown Hextc Hextm Htext Hpc Hpanic Hlk Hbno [-]").
    iIntros (CIDa Hsa M) "%Hrh Hcg Hown Hpay Hextc Hextm Hpc Htok HR Hsaved Hscr Hbno".
    destruct Hrh as (Hregs & Hhi).
    (* JOIN AT THE INDEX: P1's own acquire freed the pair at [eb = true] and
       nothing at [eb = false], where the caller (our own precondition)
       brought it.  P1 already carried the complement to THIS hart
       internally (the same way it carries [Hown]), so there is nothing
       left to transport here -- just join. *)
    iDestruct (arm_pay_ext_join eb _ with "Hpay [$Hextc $Hextm]") as "[Htc Hclm]".
    (* ---- P2: the descriptor allocator (with its sleep-retry loop) ---- *)
    iApply (P2.wp_vdrw_p2 (CID := CIDa) γk γs j γl γd pd pav pu M K eb C
              (m !!! Regidx csp_rs1) (m !!! Regidx Ra0) (m !!! Regidx Ra1)
              (vdrw_sector_raw bno) m HK Hj Hjl Hglen Hregs Hhi
              with "Hcg Hown Htc Hclm Htext Hpc Hpanic Hpinv Hgeom Hlk
                    Htok HR Hscr [-]").
    (* ---- P3: the chain formatting ---- *)
    iApply (P3.wp_vdrw_p3_seam (CID := CIDa) γk γs j γd pd pav pu K eb C
              (m !!! Regidx csp_rs1) (m !!! Regidx Ra0) (m !!! Regidx Ra1)
              (vdrw_sector_raw bno) dsk0 m with "Htext Hgeom Hbdisk [-]").
    (* ---- P4: the ring write and THE PUBLISH ---- *)
    iApply (P4.wp_vdrw_p4_seam (CID := CIDa) γk γs j γu γd pd pav pu K eb C
              (m !!! Regidx csp_rs1) (m !!! Regidx Ra0) (m !!! Regidx Ra1)
              bno bs_buf bs_disk m kq Hbnolt Hlenbuf Hbufkd
              with "Htext Hdinv Hgeom Hbufm Hdisk Hpend [-]").
    (* ---- P5: the device kick and the completion wait ---- *)
    iApply (P5.wp_vdrw_p5_seam (CID := CIDa) γk γs j γl γu γd pd pav pu K eb C
              (m !!! Regidx csp_rs1) (m !!! Regidx Ra0) (m !!! Regidx Ra1)
              (vdrw_sector_raw bno) bs_buf bs_disk m kq HK Hj Hjl
              (vdrwf_bnz _ (Hbufkd 0%nat ltac:(lia)))
              with "Htext Hpanic Hpinv Hdinv Hlk [-]").
    (* ---- P6: the payoff, free_chain, release, epilogue ---- *)
    iApply (wp_vdrw_p6_seam (CID := CIDa) γk γs j γd pd pav pu K eb C
              (m !!! Regidx csp_rs1) (m !!! Regidx Ra0) m (m !!! Regidx Ra1)
              (vdrw_sector_raw bno) bno bs_buf bs_disk Q kq
              HK Hglen Hlenbuf Hlendisk Hsecval Hbufkd eq_refl
              with "Htext Hpanic Hpinv Hqinv Hrcpt Hgeom Hlk Hsaved Hbno [-]").
    iIntros (CIDf Hsf mf) "%Hcsf Hcg Hown Hextc Hextm Hpc Hbufo Hdisko HQ".
    iEval (rewrite Hsld) in "Hbufo".
    iEval (rewrite Hsld) in "Hdisko".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with
              "[%] Hcg Hown Hextc Hextm Hpc Hbufo Hdisko HQ").
    exact Hcsf.
  Qed.

End ProofVirtioDiskRwF.
End VirtioDiskRwProof.
