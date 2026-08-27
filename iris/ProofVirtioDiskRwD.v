(* ProofVirtioDiskRwD.v -- virtio_disk_rw, phase P4: the ring write and THE
   PUBLISH (+0x176 .. +0x19a).

   The continuation of ProofVirtioDiskRwC.v, which proves P3 and leaves the
   seam [VirtioDiskRwRestC.vdrw_p3_exit] at +0x176.

     0x176 c.ld a3,8(a5)     a3 = disk.avail = pav
     0x178 lhu  a4,2(a3)     AU: read avail->idx      (= wrap16 np)
     0x17c c.andi a4,a4,7 ; 0x17e c.slli a4,a4,1 ; 0x180 c.add a3,a3,a4
     0x182 sh   a0,4(a3)     PLAIN store of the head into ring slot np mod 8
     0x186 fence rw,rw
     0x18a c.ld a4,8(a5) ; 0x18c lhu a5,2(a4)   the SAME np again
     0x190 c.addiw a5,a5,1
     0x192 sh   a5,2(a4)     THE PUBLISH (AU: avail->idx := wrap16 (S np))
     0x196 fence rw,rw

   A FOURTH file, purely for build latency (see the worklist).  Nothing in
   P4 calls a callee, so the phase itself lives in plain Sections; only the
   P3 -> P4 glue re-opens the functor.

   NOTE (the ProofVirtioDiskIntr helpers): a sibling owns that file, so the
   four small things P4 needs from it -- the [fence rw,rw] execution fact and
   its leaf, the page-offset alignment lemma, and the bitvector arithmetic of
   the 16-bit counter -- are CLONED here under [vdrwd_] names rather than
   imported.

   P5 follows in ProofVirtioDiskRwE.v and P6 in ProofVirtioDiskRwF.v.
   The whole function is composed and sealed in ProofVirtioDiskRwF.v
   ([Module VirtioDiskRwProof … : VIRTIODISKRW]) and instantiated in
   LinkVirtioDiskRw.v.  Everything here is Qed-closed.
 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import InstrBytes.
Require Import RegFile.
Require Import KMap.
Require Import KptPt.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import MinstretInv.
Require Import MemAccessGen.
Require Import WpSmodeHalf.
Require Import VirtioQueue DiskPtsto VirtioProto DiskInv.
Require Import VirtioModel.
Require Import WpUart.
Require Import PermInv.
Require Import CodeVirtioDiskRw.
Require Import VirtioDiskRwDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).


(* ===================================================================== *)
(* §1  Pure arithmetic.  Everything [lia] touches is mword-free; every    *)
(*     bitvector identity is a closed [vm_compute] or an 8-way destruct.  *)
(* ===================================================================== *)

(* ---- the modular arithmetic of the 16-bit counters ---- *)

Lemma vdrwd_wrap16_z (a : Z) : bv_wrap 16 a = (a `mod` 65536)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 16) with 16%Z. reflexivity. Qed.

Lemma vdrwd_wrap32_z (a : Z) : bv_wrap 32 a = (a `mod` 4294967296)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32%Z. reflexivity. Qed.

Lemma vdrwd_wrap64_z (a : Z) : bv_wrap 64 a = (a `mod` 18446744073709551616)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. reflexivity. Qed.

Lemma vdrwd_mod_32_16 (a : Z) : ((a `mod` 4294967296) `mod` 65536)%Z = (a `mod` 65536)%Z.
Proof.
  rewrite (Z.mod_mod_divide a 4294967296 65536); [reflexivity|].
  exists 65536%Z. reflexivity.
Qed.

Lemma vdrwd_mod_64_16 (a : Z) : ((a `mod` 18446744073709551616) `mod` 65536)%Z = (a `mod` 65536)%Z.
Proof.
  rewrite (Z.mod_mod_divide a 18446744073709551616 65536); [reflexivity|].
  exists 281474976710656%Z. reflexivity.
Qed.

Lemma vdrwd_mod_64_32 (a : Z) :
  ((a `mod` 18446744073709551616) `mod` 4294967296)%Z = (a `mod` 4294967296)%Z.
Proof.
  rewrite (Z.mod_mod_divide a 18446744073709551616 4294967296); [reflexivity|].
  exists 4294967296%Z. reflexivity.
Qed.

Lemma vdrwd_land7_z (x : Z) : Z.land x 7 = (x `mod` 8)%Z.
Proof. change 7%Z with (Z.ones 3). rewrite (Z.land_ones x 3 ltac:(lia)). reflexivity. Qed.

Lemma vdrwd_mod8_bound_z (k : nat) : (0 <= Z.of_nat (k `mod` 8) < 8)%Z.
Proof. pose proof (Nat.mod_upper_bound k 8 ltac:(lia)). lia. Qed.

Lemma vdrwd_mod8_z (k : nat) : (Z.of_nat k `mod` 8)%Z = Z.of_nat (k `mod` 8)%nat.
Proof. rewrite Nat2Z.inj_mod. reflexivity. Qed.

Lemma vdrwd_small_wrap64 (k : Z) : (0 <= k)%Z -> (k < 4096)%Z -> bv_wrap 64 k = k.
Proof.
  intros H0 H1. rewrite vdrwd_wrap64_z. apply Z.mod_small. lia.
Qed.

(* ---- the WINDOW bound, from the descriptor-triple counting alone ------ *)
(* [tri_card_8] already bounds the number of RECORDED triples by two, so
   the live window is at most two positions wide -- and three consecutive
   positions are pairwise distinct mod 8, which is all the ring-slot
   freshness argument needs.  (A sharper bound of ONE is provable, but it
   needs the publisher's own triple to be disjoint from every recorded one;
   this weaker route needs nothing beyond [disk_res]'s own conjuncts.) *)

Lemma vdrwd_mod8_ne (p q : nat) :
  (p < q)%nat -> (q - p <= 2)%nat -> (p `mod` 8)%nat <> (q `mod` 8)%nat.
Proof.
  intros Hlt Hle Heq.
  pose proof (Nat.div_mod_eq p 8) as Hp.
  pose proof (Nat.div_mod_eq q 8) as Hq.
  assert (Hd : (p / 8 <= q / 8)%nat) by (apply Nat.Div0.div_le_mono; lia).
  lia.
Qed.

Lemma vdrwd_mod8_fresh (nr np : nat) :
  (np - nr <= 2)%nat -> (np `mod` 8)%nat ∉ mod8 (set_seq nr (np - nr)).
Proof.
  intros Hw Hin. rewrite /mod8 in Hin.
  apply elem_of_map in Hin as (p & Hp & Hpin).
  apply elem_of_set_seq in Hpin.
  exact (vdrwd_mod8_ne p np ltac:(lia) ltac:(lia) (eq_sym Hp)).
Qed.

Lemma vdrwd_window_le2 {A : Type} (np nr : nat) (fl pk : gmap nat A)
    (tr : gmap nat (nat * nat * nat)) :
  dom fl = set_seq nr (np - nr) ->
  dom tr = dom fl ∪ dom pk ->
  (forall p T, tr !! p = Some T -> tri_ok T) ->
  (forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
     tri_set Tp ## tri_set Tq) ->
  (np - nr <= 2)%nat.
Proof.
  intros Hfl Htr Hok Hdisj.
  pose proof (tri_card_8 tr Hok Hdisj) as Hsz.
  assert (Hdom : (size (dom fl) <= size (dom tr))%nat)
    by (apply subseteq_size; rewrite Htr; apply union_subseteq_l).
  rewrite Hfl size_set_seq size_dom in Hdom. lia.
Qed.

(* the [set_seq] surgery at publish: [np] joins the window *)
Lemma vdrwd_set_seq_snoc (nr np : nat) :
  (nr <= np)%nat -> set_seq nr (S np - nr) = (set_seq nr (np - nr) : gset nat) ∪ {[ np ]}.
Proof.
  intro Hle. apply set_eq. intro x.
  rewrite elem_of_union elem_of_singleton !elem_of_set_seq. lia.
Qed.

(* The same surgery on the FREE map's domain, as a pure fact over set
   variables.  It is stated here — rather than run inline at the publish
   step — because that step's goal sits under a whole-function Iris context:
   [set_solver] there rescans every hypothesis and cost 417 s of this file's
   455 s, while the identical goal in this three-variable context is instant.
   See optimization.md, "never call [set_solver] from inside a phase proof". *)
Lemma vdrwd_dom_fl_ins {A : Type} (nr np : nat) (fl : gmap nat A) (b : A) :
  (nr <= np)%nat -> dom fl = set_seq nr (np - nr) ->
  dom (<[ np := b ]> fl) = (set_seq nr (S np - nr) : gset nat).
Proof.
  intros Hle Hdfl.
  rewrite dom_insert_L Hdfl (vdrwd_set_seq_snoc nr np Hle).
  apply union_comm_L.
Qed.

(* ---- bitvector-level structural helpers ------------------------------ *)

Lemma vdrwd_zext16_unsigned (x : SailStdpp.Values.mword 16) :
  bv_unsigned (zero_extend' 64 x : SailStdpp.Values.mword 64) = bv_unsigned x.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       Values.to_word get_word MachineWord.MachineWord.zero_extend].
  rewrite bv_zero_extend_unsigned. reflexivity.
  first [ lia | vm_compute; discriminate | done ].
Qed.

Lemma vdrwd_and_vec_unsigned (a b : mword 64) :
  bv_unsigned (and_vec a b) = Z.land (bv_unsigned a) (bv_unsigned b).
Proof.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word SailStdpp.Values.to_word SailStdpp.Values.get_word].
  unfold MachineWord.MachineWord.and. apply bv_and_unsigned.
Qed.

Lemma vdrwd_trunc16_subrange (w : mword 64) : trunc16 w = subrange_vec_dec w 15 0.
Proof.
  unfold trunc16. change (Z.sub (Z.mul 2 8) 1) with 15%Z.
  change (15 - 0 + 1)%Z with 16%Z. apply autocast_id.
Qed.

Lemma vdrwd_trunc16_unsigned (w : mword 64) :
  bv_unsigned (trunc16 w) = bv_wrap 16 (bv_unsigned w).
Proof.
  rewrite vdrwd_trunc16_subrange.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, SailStdpp.Values.to_word.
  rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold SailStdpp.Values.get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (15 - 0 + 1)) with 16%N.
  reflexivity.
Qed.

Lemma vdrwd_sub32_unsigned (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 31 0 : SailStdpp.Values.mword 32)
  = (bv_unsigned x `mod` 4294967296)%Z.
Proof. rewrite <- trunc32_subrange. rewrite trunc32_unsigned. apply vdrwd_wrap32_z. Qed.

Lemma vdrwd_sext32_mod32 (w : SailStdpp.Values.mword 32) :
  ((bv_unsigned (sign_extend' 64 w : mword 64)) `mod` 4294967296)%Z = bv_unsigned w.
Proof.
  pose proof (f_equal bv_unsigned (trunc32_sext w)) as He.
  rewrite trunc32_unsigned vdrwd_wrap32_z in He. exact He.
Qed.

Lemma vdrwd_sext32_mod16 (w : SailStdpp.Values.mword 32) :
  ((bv_unsigned (sign_extend' 64 w : mword 64)) `mod` 65536)%Z
  = (bv_unsigned w `mod` 65536)%Z.
Proof.
  rewrite <- (vdrwd_mod_32_16 (bv_unsigned (sign_extend' 64 w : mword 64))).
  rewrite vdrwd_sext32_mod32. reflexivity.
Qed.

(* ---- the ring index [avail->idx & 7] and its doubling ---------------- *)

Lemma vdrwd_ring_idx (np : nat) :
  and_vec (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6)))
  = (mword_of_int (Z.of_nat (np `mod` 8)) : mword 64).
Proof.
  apply bv_eq. rewrite vdrwd_and_vec_unsigned vq_moi_unsigned.
  replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6)) : mword 64))
    with 7%Z by (vm_compute; reflexivity).
  rewrite vdrwd_zext16_unsigned vdrwd_land7_z wrap16_mod8 vdrwd_mod8_z.
  pose proof (vdrwd_mod8_bound_z np) as Hb.
  rewrite (vdrwd_small_wrap64 _ (proj1 Hb) ltac:(lia)). reflexivity.
Qed.

Lemma vdrwd_shl1 (k : nat) : (k < 8)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat k) : mword 64)
    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (Z.of_nat (2 * k)) : mword 64).
Proof. intro H. do 8 (destruct k as [|k]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

Lemma vdrwd_zring (k : nat) : (Z.of_nat (2 * k) + 4 = Z.of_nat (4 + 2 * k))%Z.
Proof. lia. Qed.

Lemma vdrwd_ring_addr (pav : mword 64) (k : nat) :
  add_vec (add_vec (pav : mword 64) (mword_of_int (Z.of_nat (2 * k))))
          (sign_extend' 64 (mword_of_int 4 : mword 12))
  = (d_ring pav k : SailStdpp.Values.mword 64).
Proof.
  rewrite vdrwc_sx4.
  rewrite (vdrw_av2 pav (Z.of_nat (2 * k)) 4).
  rewrite vdrwd_zring. unfold d_ring. rewrite vdrw_pa_add_moi. reflexivity.
Qed.

Lemma vdrwd_idx_addr (pav : mword 64) :
  add_vec (pav : mword 64) (sign_extend' 64 (mword_of_int 2 : mword 12))
  = (pa_add pav 2%nat : SailStdpp.Values.mword 64).
Proof.
  assert (H2 : sign_extend' 64 (mword_of_int 2 : mword 12) = (mword_of_int 2 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H2. rewrite vdrw_pa_add_moi. reflexivity.
Qed.

Lemma vdrwd_avail_ptr_addr :
  add_vec (disk_base : SailStdpp.Values.mword 64)
          (sign_extend' 64 (mword_of_int 8 : mword 12))
  = (d_avail_ptr : SailStdpp.Values.mword 64).
Proof.
  rewrite vdrwc_sx8. unfold d_avail_ptr. rewrite vdrw_pa_add_moi. reflexivity.
Qed.

(* ---- the PUBLISH store value: [c.addiw a5,a5,1] then [sh] ------------ *)

Lemma vdrwd_publish_val (np : nat) :
  trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
  = (wrap16 (S np) : SailStdpp.Values.mword 16).
Proof.
  apply bv_eq.
  rewrite vdrwd_trunc16_unsigned vdrwd_wrap16_z.
  rewrite vdrwd_sext32_mod16 vdrwd_sub32_unsigned vdrwd_mod_32_16.
  rewrite vq_add_vec_unsigned vdrwd_wrap64_z vdrwd_mod_64_16.
  rewrite vdrwd_zext16_unsigned.
  replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64))
    with 1%Z by (vm_compute; reflexivity).
  unfold wrap16. rewrite !Z_to_bv_unsigned !vdrwd_wrap16_z.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* ---- the static [struct disk] is kernel DATA ------------------------- *)

Lemma vdrwd_disk_kdata_z (k : Z) :
  (0 <= k)%Z -> (k < 4096)%Z ->
  (2147512320 <= (KernelSyms.disk + k) `mod` 18446744073709551616 < 2281701376)%Z.
Proof. intros H0 H1. unfold KernelSyms.disk. rewrite Z.mod_small; lia. Qed.

Lemma vdrwd_disk_kdata (k : nat) : (k < 4096)%nat -> addr_is_kdata (pa_add disk_base k).
Proof.
  intro Hk. unfold addr_is_kdata, text_end, ram_base, ram_size.
  rewrite uint_unsigned pa_add_unsigned vdrwd_wrap64_z.
  replace (bv_unsigned (disk_base : SailStdpp.Values.mword 64)) with KernelSyms.disk
    by (vm_compute; reflexivity).
  change (0x80007000)%Z with 2147512320%Z.
  change (0x80000000 + 0x8000000)%Z with 2281701376%Z.
  apply vdrwd_disk_kdata_z; [ exact (Nat2Z.is_nonneg k) | lia ].
Qed.

Lemma vdrwd_disk_static (k : nat) : (k < 4096)%nat ->
  kmap_static (svpn_of (pa_add disk_base k)) KP_rw.
Proof. intro Hk. apply kdata_svpn_class, vdrwd_disk_kdata. exact Hk. Qed.

(* ---- THE SECTOR: [vdrw_sector_raw bno = 2 * uint bno] ----------------- *)
(* The one pure obligation P1 deferred.  The C source computes
   [b->blockno * (BSIZE/512)] in 32-bit arithmetic and then zero-extends with
   the [slli 32 / srli 32] pair, so under the spec's no-overflow premise the
   sector is exactly [2 * bno]. *)

Lemma vdrwd_shl32_unsigned (x : mword 64) :
  bv_unsigned (shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6)
                                    (Z.sub log2_xlen 1) 0))
  = ((bv_unsigned x * 4294967296) `mod` 18446744073709551616)%Z.
Proof.
  assert (Hn : shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6)
                                    (Z.sub log2_xlen 1) 0)
             = shiftl x 32).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hn.
  unfold shiftl, SailStdpp.Values.with_word, SailStdpp.Values.get_word,
    MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 32)) = 32%Z)
    by (vm_compute; reflexivity).
  rewrite Hsh vdrwd_wrap64_z Z.shiftl_mul_pow2; [| lia].
  change (2 ^ 32)%Z with 4294967296%Z. reflexivity.
Qed.

Lemma vdrwd_shr32_unsigned (x : mword 64) :
  bv_unsigned (shift_bits_right x (subrange_vec_dec (mword_of_int 32 : mword 6)
                                     (Z.sub log2_xlen 1) 0))
  = (bv_unsigned x / 4294967296)%Z.
Proof.
  assert (Hn : shift_bits_right x (subrange_vec_dec (mword_of_int 32 : mword 6)
                                     (Z.sub log2_xlen 1) 0)
             = shiftr x 32).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hn.
  unfold shiftr, SailStdpp.Values.with_word, SailStdpp.Values.get_word,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 32)) = 32%Z)
    by (vm_compute; reflexivity).
  rewrite Hsh Z.shiftr_div_pow2; [| lia].
  change (2 ^ 32)%Z with 4294967296%Z. reflexivity.
Qed.

Lemma vdrwd_shift32_z (u : Z) :
  ((u * 4294967296) `mod` 18446744073709551616 / 4294967296)%Z = (u `mod` 4294967296)%Z.
Proof.
  replace 18446744073709551616%Z with (4294967296 * 4294967296)%Z by reflexivity.
  rewrite (Z.mul_comm u 4294967296).
  rewrite (Z.mul_mod_distr_l u 4294967296 4294967296 ltac:(lia) ltac:(lia)).
  rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

Lemma vdrwd_shl1_32 (x : mword 32) :
  bv_unsigned (shift_bits_left x (mword_of_int 1 : mword 5))
  = ((bv_unsigned x * 2) `mod` 4294967296)%Z.
Proof.
  assert (Hn : shift_bits_left x (mword_of_int 1 : mword 5) = shiftl x 1).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hn.
  unfold shiftl, SailStdpp.Values.with_word, SailStdpp.Values.get_word,
    MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 32) (MachineWord.MachineWord.Z_idx 1)) = 1%Z)
    by (vm_compute; reflexivity).
  rewrite Hsh vdrwd_wrap32_z Z.shiftl_mul_pow2; [| lia].
  change (2 ^ 1)%Z with 2%Z. reflexivity.
Qed.

Lemma vdrwd_dbl_small (x : Z) :
  (0 <= x)%Z -> (x < 2147483648)%Z -> ((x * 2) `mod` 4294967296)%Z = (2 * x)%Z.
Proof. intros H0 H1. rewrite Z.mod_small; lia. Qed.

Lemma vdrwd_uint32 (a : SailStdpp.Values.mword 32) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

Lemma vdrwd_sector_raw_val (bno : SailStdpp.Values.mword 32) :
  (uint bno < 2147483648)%Z ->
  bv_unsigned (vdrw_sector_raw bno) = (2 * uint bno)%Z.
Proof.
  intro Hb.
  rewrite vdrwd_uint32 in Hb.
  pose proof (bv_unsigned_in_range 32 bno) as [Hnn _].
  unfold vdrw_sector_raw, vdrw_sh32.
  assert (Hsub : (subrange_vec_dec (sign_extend' 64 bno : mword 64) 31 0
                    : SailStdpp.Values.mword 32) = bno)
    by (rewrite <- trunc32_subrange; apply trunc32_sext).
  rewrite Hsub.
  rewrite vdrwd_shr32_unsigned vdrwd_shl32_unsigned vdrwd_shift32_z.
  rewrite vdrwd_sext32_mod32 vdrwd_shl1_32.
  rewrite vdrwd_uint32.
  exact (vdrwd_dbl_small (bv_unsigned bno) Hnn Hb).
Qed.

(* ---- page-offset alignment: RESTATEMENTS of [DiskInv]'s ---------------
   The family lives in DiskInv.v now (it is the queue pages' geometry, and
   three files had cloned it); these keep the local names so no call site
   below had to change. *)

Lemma vdrwd_wrap_off (x k : Z) :
  0 <= x -> x < 18446744073709551616 -> x mod 4096 = 0 ->
  0 <= k -> k < 4096 ->
  (x + k) mod 18446744073709551616 = x + k.
Proof. exact (pa_wrap_in_page x k). Qed.

Lemma vdrwd_rem_off (x k d : Z) :
  0 <= x -> x < 18446744073709551616 -> x mod 4096 = 0 ->
  0 <= k -> k < 4096 -> 0 < d -> 4096 mod d = 0 -> k mod d = 0 ->
  Z.rem ((x + k) mod 18446744073709551616) d = 0.
Proof. exact (pa_rem_in_page x k d). Qed.

Lemma vdrwd_aligned_off (p : Arch.pa) (k : nat) (d : Z) :
  bv_unsigned (p : SailStdpp.Values.mword 64) `mod` 4096 = 0 ->
  (Z.of_nat k < 4096)%Z -> (0 < d)%Z -> (4096 mod d = 0)%Z ->
  (Z.of_nat k mod d = 0)%Z ->
  is_aligned_paddr (Physaddr (pa_add p k)) d = true.
Proof. exact (pa_add_aligned_in_page p k d). Qed.

Lemma vdrwd_two_add_lt (j : nat) : (j < 2)%nat -> (2 + j < 4096)%nat.
Proof. intro Hj. lia. Qed.

Lemma vdrwd_ring_off_lt (k j : nat) : (k < 8)%nat -> (j < 2)%nat -> (4 + 2 * k + j < 4096)%nat.
Proof. intros Hk Hj. lia. Qed.

Lemma vdrwd_ring_off_lt_z (k : nat) : (k < 8)%nat -> (Z.of_nat (4 + 2 * k) < 4096)%Z.
Proof. intro Hk. lia. Qed.

Lemma vdrwd_ring_off_mod2 (k : nat) : (Z.of_nat (4 + 2 * k) mod 2 = 0)%Z.
Proof.
  replace (Z.of_nat (4 + 2 * k))%Z with ((2 + Z.of_nat k) * 2)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

(* ===================================================================== *)
(* §2  Assembling the PIN.                                               *)
(*                                                                       *)
(* [virtio_proto_publish_acc] wants ONE byte map [pin] with [phys_map]    *)
(* ownership and a [slot_pin_ok] whose clauses are [read_bytes] at six    *)
(* windows.  What the publisher HOLDS is seventeen separately owned word  *)
(* cells (plus, for a write request, the caller's buffer).  So the pin is *)
(* the disjoint union of that many [range_map]s, and the ONE induction    *)
(* below turns a list of separately-owned maps into the union together    *)
(* with the sub-map facts every [read_bytes] obligation needs.           *)
(* ===================================================================== *)

(* [l]'s elements are pairwise disjoint, in the prefix form the [foldr]
   induction produces.  Deliberately POLYMORPHIC in the key type: a
   [gmap Arch.pa _] spelled out here would pick up the wrong Countable
   instance (durable-notes' binder trap), so the instance is left to come
   from the caller. *)
Fixpoint pm_ok {K A} `{Countable K} (l : list (gmap K A)) : Prop :=
  match l with
  | [] => True
  | m :: l' => m ##ₘ foldr union ∅ l' /\ pm_ok l'
  end.

Lemma map_union_diff_l {K A} `{Countable K} (m1 m2 : gmap K A) :
  m1 ##ₘ m2 -> (m1 ∪ m2) ∖ m1 = m2.
Proof.
  intro Hd. apply map_eq. intro i.
  destruct (m1 !! i) as [x|] eqn:H1.
  - assert (H2 : m2 !! i = None).
    { destruct (m2 !! i) as [y|] eqn:Hy; [| reflexivity].
      exfalso. exact (proj1 (map_disjoint_spec m1 m2) Hd i x y H1 Hy). }
    rewrite H2. apply lookup_difference_None. right. exists x. exact H1.
  - destruct (m2 !! i) as [y|] eqn:H2.
    + apply lookup_difference_Some. split; [| exact H1].
      rewrite lookup_union_r; [exact H2 | exact H1].
    + apply lookup_difference_None. left.
      rewrite lookup_union_r; [exact H2 | exact H1].
Qed.

Section VdrwdMaps.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* NB the binder types are left to inference: a [gmap Arch.pa _] written
     out in a file that imports SailStdpp.Values picks up a DIFFERENT
     Countable instance from the one VirtioProto's [phys_map] uses
     (durable-notes' instance-leak trap), so every map binder here is [_]. *)
  Definition pm_list (l : list _) : iProp Σ :=
    ([∗ list] m ∈ l, phys_map m)%I.

  Lemma pm_union (l : list _) :
    pm_list l -∗
    phys_map (foldr union ∅ l) ∗ ⌜pm_ok l⌝ ∗
    ⌜forall m, m ∈ l -> m ⊆ foldr union ∅ l⌝.
  Proof.
    induction l as [|m l IH].
    - iIntros "_". rewrite /phys_map big_sepM_empty. iSplitR; [done|].
      iSplitR; [iPureIntro; exact I|].
      iPureIntro. intros m Hm. exfalso. exact (not_elem_of_nil m Hm).
    - rewrite /pm_list. iIntros "[Hm Hl]".
      iDestruct (IH with "Hl") as "(Hu & %Hokl & %Hsub)".
      iDestruct (phys_map_disj with "Hm Hu") as %Hd.
      iSplitL "Hm Hu".
      { cbn [foldr]. rewrite (phys_map_union m (foldr union ∅ l) Hd). iFrame. }
      iSplitR; [iPureIntro; exact (conj Hd Hokl)|].
      iPureIntro. intros m' Hm'. cbn [foldr].
      apply elem_of_cons in Hm' as [->|Hm'].
      + apply map_union_subseteq_l.
      + apply (transitivity (Hsub m' Hm')). apply map_union_subseteq_r. exact Hd.
  Qed.

  (* the converse: a pairwise-disjoint list's union splits back into the
     separately-owned windows.  This is what lets P6 take the parked payoff's
     one opaque [phys_map] apart into the cells [free_chain] hands back. *)
  Lemma pm_split (l : list _) :
    pm_ok l -> phys_map (foldr union ∅ l) -∗ pm_list l.
  Proof.
    induction l as [|m l IH]; intro Hok.
    - iIntros "_". rewrite /pm_list. done.
    - destruct Hok as [Hd Hokl].
      iIntros "H". cbn [foldr].
      rewrite (phys_map_union m (foldr union ∅ l) Hd).
      iDestruct "H" as "[Hm Hl]".
      rewrite /pm_list. iSplitL "Hm"; [iExact "Hm"|].
      iApply (IH Hokl with "Hl").
  Qed.

  (* the byte-window resources, all in the ONE [phys_map (range_map ...)]
     shape [pm_union] consumes *)
  Lemma vdrwd_pw8_map (a : Arch.pa) (w : bv 64) :
    phys_word8 a w ⊣⊢ phys_map (range_map a 8 (nth_byte w)).
  Proof. rewrite /phys_word8. symmetry. apply (phys_map_range a 8 (nth_byte w)). lia. Qed.

  (* A6.69: [VirtioProto.phys_map] is a big-op of [TsoCtx.phys_ledger], so
     the singleton bridge is stated at the LEDGER byte.  The raw
     [phys_pointsto] would drop the timestamp element and could not be
     re-entered (A6.9). *)
  Lemma vdrwd_pb_map (a : Arch.pa) (v : bv 8) :
    phys_ledger a (DfracOwn 1) v ⊣⊢ phys_map {[ a := v ]}.
  Proof. rewrite /phys_map big_sepM_singleton. reflexivity. Qed.

End VdrwdMaps.

(* the two read facts a region of the union supports *)
Lemma vdrwd_read_reg (a : Arch.pa) (n : N) (w : bv (8 * n)) (mm : _) :
  (Z.of_N n < 18446744073709551616)%Z ->
  range_map a (N.to_nat n) (nth_byte w) ⊆ mm ->
  read_bytes mm a n = Some w.
Proof.
  intros Hn Hsub. apply (read_bytes_mono _ _ _ _ _ Hsub).
  rewrite <- write_bytes_range_map. apply read_write_bytes. exact Hn.
Qed.

Lemma vdrwd_read_list (a : Arch.pa) (bs : list (bv 8)) (mm : _) :
  (Z.of_nat (length bs) < 18446744073709551616)%Z ->
  range_map a (length bs) (fun j => bs !!! j) ⊆ mm ->
  read_byte_list mm a (length bs) = Some bs.
Proof.
  intros Hn Hsub. apply (read_byte_list_mono _ _ _ _ _ Hsub).
  apply read_byte_list_intro; [reflexivity|].
  intros j b Hj.
  assert (Hjlt : (j < length bs)%nat) by (apply lookup_lt_Some in Hj; exact Hj).
  rewrite (range_map_lookup a (length bs) (fun k => bs !!! k) j Hn Hjlt).
  f_equal. apply list_lookup_total_correct. exact Hj.
Qed.

(* ===================================================================== *)
(* §3  The two leaves P4 needs beyond the plain ones: the dev_inv-        *)
(*     OPENING accesses to [avail->idx].  (The `fence rw,rw` is the       *)
(*     shared [WpSconfCtl.wp_fence_gen_s_sconf].)                         *)
(* ===================================================================== *)

Section VdrwdLeaves.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ---- the avail-ring INDEX read: [lhu rd,2(rs1)] with rs1 = disk.avail.
     Drives [virtio_proto_avail_idx_acc]: the value is the driver's OWN
     published count, so nothing new is learned about it -- what the read is
     for is that the code re-derives the ring slot from it.  The accessor
     for the USED index is run alongside (read-only, immediately closed) to
     export the window fact [nr <= np], which [disk_res] does not carry and
     the ring-slot freshness argument needs. ---- *)
  Lemma wp_vdrwd_lhu_avail (γu : uart_names) (γd : disk_names) (pme : Arch.pa) (pd pav pu : mword 64)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (np nr : nat) :
    add_vec (rget m rs1) (sign_extend' 64 imm) = (pa_add pav 2%nat : mword 64) ->
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr KT1 m n false pme -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 2)) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    disk_pub γd np -∗ disk_done_lb γd nr -∗
    ( ⌜(nr <= np)%nat⌝ -∗
      disk_pub γd np -∗
      sie_cap_gpr KT1 (<[Regidx rd := regval_into_reg
          (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16))]> m) n false pme -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hea Hrd Hrdsp.
    (* the class, consumed at [rs1] -- see [IntrDefs.SrcOk].  This wrapper
       applies a converted leaf at a VARIABLE register and carries no tp fact
       of its own, so the class has to be stated here; it is implicit, so this
       lemma's own call sites (which pass concrete registers) do not move.  The
       [assert] is the wiring check: it names the register the premise reads. *)
    assert (Hea_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm)
              = add_vec (rget (CID := CID) m rs1) (sign_extend' 64 imm))
      by (intros hh; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hdinv #Hgeom Hpub #Hlb0 Hcont".
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    iDestruct (disk_geom_static with "Hgeom") as %(_ & Hsta & _).
    iDestruct (disk_geom_canonical with "Hgeom") as %(_ & Hcana & _).
    iDestruct "Hgeom" as "(_ & _ & _ & %Hal0 & #Hcfg0 & _ & _ & _)".
    destruct Hal0 as (_ & Hala & _).
    assert (Halign : is_aligned_paddr (Physaddr (pa_add pav 2%nat)) 2 = true).
    { apply (vdrwd_aligned_off pav 2%nat 2 Hala);
        [ reflexivity | reflexivity | reflexivity | reflexivity ]. }
    assert (Hst2 : forall j, (j < 2)%nat ->
              kmap_static (svpn_of (pa_add (pa_add pav 2%nat) j)) KP_rw).
    { intros j Hj. rewrite pa_add_add. exact (Hsta (2 + j)%nat (vdrwd_two_add_lt j Hj)). }
    assert (Hcan2 : forall j, (j < 2)%nat ->
              (uint (pa_add (pa_add pav 2%nat) j : SailStdpp.Values.mword 64) < 274877906944)%Z).
    { intros j Hj. rewrite pa_add_add. exact (Hcana (2 + j)%nat (vdrwd_two_add_lt j Hj)). }
    (* THE ADDRESS CLAIM, READ OFF THE CELL ITSELF.  The per-node form takes
       [WpSconfMem.wordw_claim] beside the (linear) atomic update, so it has
       to arrive first; one peek-open of the device invariant runs the
       READ-ONLY avail-index accessor, takes the claim off the window's own
       points-to ([wordw_claim_of]) and hands the cell straight back.  The
       claim is persistent, so it survives the close. *)
    iApply fupd_wp.
    iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv0".
    iInv "Hvinv0" as ">Hdbodyp" "Hdclosep".
    iDestruct "Hdbodyp" as (vstp) "(Hvfp & Hprotop & %Hvokp)".
    iDestruct (virtio_proto_avail_idx_acc γd vstp np with "Hprotop Hpub")
      as "(_ & #Hcfgvp & _ & Hw2p & Hbackp)".
    iDestruct (disk_cfg_agree with "Hcfgvp Hcfg0") as %Hceqp.
    assert (Haddrp : avail_idx_pa (v_cfg vstp) = pa_add pav 2%nat)
      by (rewrite Hceqp; reflexivity).
    iEval (rewrite Haddrp) in "Hw2p".
    iDestruct (phys_to_word2 (pa_add pav 2%nat) (wrap16 np) Halign Hst2 Hcan2
                 with "Hkm Hw2p") as "Hcellp".
    iDestruct (wordw_claim_of (KTR := KT0) 2 (pa_add pav 2%nat) (DfracOwn 1)
                 (wrap16 np : SailStdpp.Values.mword 16) ltac:(lia)
                 with "Hcellp") as "#Hcl".
    iDestruct (word2_to_phys (pa_add pav 2%nat) (wrap16 np) Hst2
                 with "Hkm Hcellp") as "Hw2p".
    iEval (rewrite -Haddrp) in "Hw2p".
    iDestruct ("Hbackp" with "Hw2p") as "[Hprotop Hpub]".
    iMod ("Hdclosep" with "[Hvfp Hprotop]") as "_".
    { iNext. iExists vstp. iFrame. iPureIntro. exact Hvokp. }
    iModIntro.
    iApply (wp_load_s_sconf_au (kt := KT1) (ktd := KT0) 2 false true pc rd rs1 imm m n
              (fun w => zero_extend' 64 w)
              (fun w => (⌜w = wrap16 np⌝ ∗ ⌜(nr <= np)%nat⌝ ∗ disk_pub γd np)%I)
              (⊤ ∖ ↑minstretN ∖ ↑diskN) false (dqm := DfracOwn 1)
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 2048; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_2 data2_ext_2_unsigned Hrd Hrdsp
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [] [Hpub] [Hcont]").
    { rewrite Hea. iExact "Hcl". }
    { iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
      iInv "Hvinv" as ">Hdbody" "Hdclose".
      iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
      (* the window fact, read off the used-index accessor and given back *)
      iDestruct (virtio_proto_used_idx_acc γd vst np nr with "Hproto Hpub Hlb0")
        as (nc) "(%Hnrnc & %Hncnp & _ & _ & _ & Hwu & Hbacku)".
      iDestruct ("Hbacku" with "Hwu") as "[Hproto Hpub]".
      iDestruct (virtio_proto_avail_idx_acc γd vst np with "Hproto Hpub")
        as "(_ & #Hcfgv & _ & Hw2 & Hback)".
      iDestruct (disk_cfg_agree with "Hcfgv Hcfg0") as %Hceq.
      assert (Haddr : avail_idx_pa (v_cfg vst) = pa_add pav 2%nat)
        by (rewrite Hceq; reflexivity).
      iEval (rewrite Haddr) in "Hw2".
      iDestruct (phys_to_word2 (pa_add pav 2%nat) (wrap16 np) Halign Hst2 Hcan2
                   with "Hkm Hw2") as "Hcell".
      iModIntro. iExists (wrap16 np : SailStdpp.Values.mword 16).
      iSplitL "Hcell".
      { rewrite Hea. iExact "Hcell". }
      iIntros "Hcell". iEval (rewrite Hea) in "Hcell".
      iDestruct (word2_to_phys (pa_add pav 2%nat) (wrap16 np) Hst2 with "Hkm Hcell") as "Hw2".
      iEval (rewrite -Haddr) in "Hw2".
      iDestruct ("Hback" with "Hw2") as "[Hproto Hpub]".
      iMod ("Hdclose" with "[Hvf Hproto]") as "_".
      { iNext. iExists vst. iFrame. iPureIntro. exact Hvok. }
      iModIntro. iFrame "Hpub". iSplitR; [done|]. iPureIntro. lia. }
    iIntros (w). iApply wp_next_off_intro. iIntros "Hcg Hpc Hpost". rgall.
    iDestruct "Hpost" as "(-> & %Hle & Hpub)".
    iApply ("Hcont" with "[%] Hpub Hcg Hpc"). exact Hle.
  Qed.

  (* ---- THE PUBLISH: [sh rs2,2(rs1)] with rs1 = disk.avail and rs2 the
     incremented index.  Drives [virtio_proto_publish_acc]: the pin and the
     writable footprint go into the DMA lease, the disk fragments become the
     slot's pending resource, and what comes back is the bumped publisher
     credential plus the RECEIPT. ---- *)
  Lemma wp_vdrwd_sh_publish (γu : uart_names) (γd : disk_names) (pme : Arch.pa) (pd pav pu : mword 64)
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (np : nat) (sl : vslot) (pin wrb : _) :
    add_vec (rget m rs1) (sign_extend' 64 imm) = (pa_add pav 2%nat : mword 64) ->
    trunc16 (rget m rs2) = (wrap16 (S np) : SailStdpp.Values.mword 16) ->
    slot_pin_ok (virtio_init_cfg pd pav pu) np sl pin ->
    dom wrb = slot_wr sl ->
    slot_wr sl ## dom pin ->
    sie_cap_gpr KT1 m n false pme -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 2)) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    disk_pub γd np -∗ phys_map pin -∗ phys_map wrb -∗
    slot_pend_res γd (vs_all sl) sl -∗
    ( sie_cap_gpr KT1 m n false pme -∗
      pc_is (add_vec_int pc 4) -∗
      disk_pub γd (S np) -∗ disk_receipt γd np sl pin -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hea Hsv Hpinok Hwrbdom Hwrpin.
    (* the class, consumed at [rs1 / rs2] -- see [IntrDefs.SrcOk].  This wrapper
       applies a converted leaf at a VARIABLE register and carries no tp fact
       of its own, so the class has to be stated here; it is implicit, so this
       lemma's own call sites (which pass concrete registers) do not move.  The
       [assert] is the wiring check: it names the register the premise reads. *)
    assert (Hea_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm)
              = add_vec (rget (CID := CID) m rs1) (sign_extend' 64 imm))
      by (intros hh; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hdinv #Hgeom Hpub Hpin Hwrb Hpend Hcont".
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    iDestruct (disk_geom_static with "Hgeom") as %(_ & Hsta & _).
    iDestruct (disk_geom_canonical with "Hgeom") as %(_ & Hcana & _).
    iDestruct "Hgeom" as "(_ & _ & _ & %Hal0 & #Hcfg0 & _ & _ & _)".
    destruct Hal0 as (_ & Hala & _).
    assert (Halign : is_aligned_paddr (Physaddr (pa_add pav 2%nat)) 2 = true).
    { apply (vdrwd_aligned_off pav 2%nat 2 Hala);
        [ reflexivity | reflexivity | reflexivity | reflexivity ]. }
    assert (Hst2 : forall j, (j < 2)%nat ->
              kmap_static (svpn_of (pa_add (pa_add pav 2%nat) j)) KP_rw).
    { intros j Hj. rewrite pa_add_add. exact (Hsta (2 + j)%nat (vdrwd_two_add_lt j Hj)). }
    assert (Hcan2 : forall j, (j < 2)%nat ->
              (uint (pa_add (pa_add pav 2%nat) j : SailStdpp.Values.mword 64) < 274877906944)%Z).
    { intros j Hj. rewrite pa_add_add. exact (Hcana (2 + j)%nat (vdrwd_two_add_lt j Hj)). }
    (* THE ADDRESS CLAIM, READ OFF THE CELL ITSELF.  The per-node form takes
       [WpSconfMem.wordw_claim] beside the (linear) atomic update, so it has
       to arrive first; one peek-open of the device invariant runs the
       READ-ONLY avail-index accessor, takes the claim off the window's own
       points-to ([wordw_claim_of]) and hands the cell straight back.  The
       claim is persistent, so it survives the close. *)
    iApply fupd_wp.
    iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv0".
    iInv "Hvinv0" as ">Hdbodyp" "Hdclosep".
    iDestruct "Hdbodyp" as (vstp) "(Hvfp & Hprotop & %Hvokp)".
    iDestruct (virtio_proto_avail_idx_acc γd vstp np with "Hprotop Hpub")
      as "(_ & #Hcfgvp & _ & Hw2p & Hbackp)".
    iDestruct (disk_cfg_agree with "Hcfgvp Hcfg0") as %Hceqp.
    assert (Haddrp : avail_idx_pa (v_cfg vstp) = pa_add pav 2%nat)
      by (rewrite Hceqp; reflexivity).
    iEval (rewrite Haddrp) in "Hw2p".
    iDestruct (phys_to_word2 (pa_add pav 2%nat) (wrap16 np) Halign Hst2 Hcan2
                 with "Hkm Hw2p") as "Hcellp".
    iDestruct (wordw_claim_of (KTR := KT0) 2 (pa_add pav 2%nat) (DfracOwn 1)
                 (wrap16 np : SailStdpp.Values.mword 16) ltac:(lia)
                 with "Hcellp") as "#Hcl".
    iDestruct (word2_to_phys (pa_add pav 2%nat) (wrap16 np) Hst2
                 with "Hkm Hcellp") as "Hw2p".
    iEval (rewrite -Haddrp) in "Hw2p".
    iDestruct ("Hbackp" with "Hw2p") as "[Hprotop Hpub]".
    iMod ("Hdclosep" with "[Hvfp Hprotop]") as "_".
    { iNext. iExists vstp. iFrame. iPureIntro. exact Hvokp. }
    iModIntro.
    iApply (wp_store_s_sconf_au (kt := KT1) (ktd := KT0) 2 false pc rs2 rs1 imm m n
              (wrap16 (S np) : SailStdpp.Values.mword 16)
              (disk_pub γd (S np) ∗ disk_receipt γd np sl pin)%I
              (⊤ ∖ ↑minstretN ∖ ↑diskN) false
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 2048; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_2
              ltac:(rewrite (store_ext_2 (rget m rs2)); exact Hsv)
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [] [Hpub Hpin Hwrb Hpend] [Hcont]").
    { rewrite Hea. iExact "Hcl". }
    { iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
      iInv "Hvinv" as ">Hdbody" "Hdclose".
      iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
      (* pin the live configuration first: the publish accessor's pure premise
         is stated at [v_cfg vst], and the caller supplies it at the frozen
         [virtio_init_cfg]. *)
      iDestruct (virtio_proto_avail_idx_acc γd vst np with "Hproto Hpub")
        as "(_ & #Hcfgv & _ & Hw2 & Hback)".
      iDestruct (disk_cfg_agree with "Hcfgv Hcfg0") as %Hceq.
      iDestruct ("Hback" with "Hw2") as "[Hproto Hpub]".
      assert (Haddr : avail_idx_pa (v_cfg vst) = pa_add pav 2%nat)
        by (rewrite Hceq; reflexivity).
      iDestruct (virtio_proto_publish_acc γd vst np sl pin wrb
                   ltac:(rgall; rewrite Hceq; exact Hpinok) Hwrbdom Hwrpin
                   with "Hproto Hpub Hpin Hwrb Hpend") as "(_ & _ & Hw2 & Hclose)".
      iEval (rewrite Haddr) in "Hw2".
      iDestruct (phys_to_word2 (pa_add pav 2%nat) (wrap16 np) Halign Hst2 Hcan2
                   with "Hkm Hw2") as "Hcell".
      iModIntro. iExists (wrap16 np : SailStdpp.Values.mword 16).
      iSplitL "Hcell".
      { rewrite Hea. iExact "Hcell". }
      iIntros "Hcell". iEval (rewrite Hea) in "Hcell".
      iDestruct (word2_to_phys (pa_add pav 2%nat) (wrap16 (S np)) Hst2
                   with "Hkm Hcell") as "Hw2".
      iEval (rewrite -Haddr) in "Hw2".
      iMod ("Hclose" with "Hw2") as "(Hproto & Hpub & Hrcpt)".
      iMod ("Hdclose" with "[Hvf Hproto]") as "_".
      { iNext. iExists vst. iFrame. iPureIntro. exact Hvok. }
      iModIntro. iFrame "Hpub Hrcpt". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc [Hpub Hrcpt]". rgall.
    iApply ("Hcont" with "Hcg Hpc Hpub Hrcpt").
  Qed.

End VdrwdLeaves.

(* ===================================================================== *)
(* §4  THE PIN, as a pure fact and as ownership.                          *)
(* ===================================================================== *)

(* the slot [virtio_disk_rw] publishes *)
(* [kq] is the crash-permit key ([VirtioQueue.vs_perm]); it comes FIRST so
   that every downstream statement about the published slot threads it as a
   leading parameter, exactly like a section variable would. *)
Definition vdrwd_slot (kq : nat * positive)
    (b : Arch.pa) (h : nat)
    (wr sector : SailStdpp.Values.mword 64)
    (bs : list (bv 8)) : vslot :=
  rw_slot h (vdrw_ty wr) sector (b_data b) (d_info_status h) bs kq.

(* whether the request is a WRITE, as the pin sees it *)
Definition vdrwd_out (wr : SailStdpp.Values.mword 64) : bool :=
  bv_unsigned (vdrw_ty wr) =? virtio_blk_t_out.

(* the slot's DATA field: the block's content in both directions -- a write's
   payload (which the pin covers) or a read's current disk content (which the
   published pending resource pins).  See [VirtioQueue.vs_data]. *)
Definition vdrwd_sldata (wr : SailStdpp.Values.mword 64)
    (bs_buf bs_disk : list (bv 8)) : list (bv 8) :=
  if vdrwd_out wr then bs_buf else bs_disk.

(* the buffer window, which is inside the PIN for a write and inside the
   device-WRITABLE footprint for a read *)
Definition vdrwd_bufwin (b : Arch.pa) (wr : SailStdpp.Values.mword 64)
    (bs : list (bv 8)) :=
  if bv_unsigned (vdrw_ty wr) =? virtio_blk_t_out
  then range_map (b_data b) 1024 (fun j => bs !!! j)
  else ∅.

(* THE PIN, minus its avail-ring entry: the fifteen word windows the chain
   formatting wrote plus (for a write) the payload.  This is exactly what the
   interrupt handler leaves in [DiskInv.dc_pinr], i.e. what P6 gets back and
   has to split into cells again.  (No return-type annotation: a
   [gmap Arch.pa _] spelled out here would pick the wrong Countable
   instance.) *)
Definition vdrwd_pinr_regions (pd : SailStdpp.Values.mword 64) (b : Arch.pa)
    (h m2 t : nat) (wr sector : SailStdpp.Values.mword 64) (mbuf : _) :=
  [ range_map (d_desc pd h) 8 (nth_byte (d_ops h : SailStdpp.Values.mword 64))
  ; range_map (pa_add pd (16 * h + 8)) 4 (nth_byte (Z_to_bv 32 16))
  ; range_map (pa_add pd (16 * h + 12)) 2 (nth_byte (Z_to_bv 16 1))
  ; range_map (pa_add pd (16 * h + 14)) 2 (nth_byte (Z_to_bv 16 (Z.of_nat m2)))
  ; range_map (d_desc pd m2) 8 (nth_byte (b_data b : SailStdpp.Values.mword 64))
  ; range_map (pa_add pd (16 * m2 + 8)) 4 (nth_byte (Z_to_bv 32 1024))
  ; range_map (pa_add pd (16 * m2 + 12)) 2 (nth_byte (vdrw_flags wr))
  ; range_map (pa_add pd (16 * m2 + 14)) 2 (nth_byte (Z_to_bv 16 (Z.of_nat t)))
  ; range_map (d_desc pd t) 8 (nth_byte (d_info_status h : SailStdpp.Values.mword 64))
  ; range_map (pa_add pd (16 * t + 8)) 4 (nth_byte (Z_to_bv 32 1))
  ; range_map (pa_add pd (16 * t + 12)) 2 (nth_byte (Z_to_bv 16 2))
  ; range_map (pa_add pd (16 * t + 14)) 2 (nth_byte (Z_to_bv 16 0))
  ; range_map (d_ops h) 4 (nth_byte (vdrw_ty wr))
  ; range_map (pa_add disk_base (168 + 16 * h + 4)) 4
      (nth_byte (mword_of_int 0 : SailStdpp.Values.mword 32))
  ; range_map (pa_add disk_base (168 + 16 * h + 8)) 8 (nth_byte sector)
  ; mbuf ].

(* ...and the pin itself: the avail-ring entry, then those fifteen (+ the
   payload window).  Written as a CONS so that [pin ∖ ring] is one
   [map_union_diff_l]. *)
Definition vdrwd_regions (pd pav : SailStdpp.Values.mword 64) (b : Arch.pa)
    (np h m2 t : nat) (wr sector : SailStdpp.Values.mword 64) (mbuf : _) :=
  range_map (d_ring pav (np `mod` 8)) 2 (nth_byte (Z_to_bv 16 (Z.of_nat h)))
  :: vdrwd_pinr_regions pd b h m2 t wr sector mbuf.

Lemma vdrwd_ring_off_nat (k : nat) :
  Z.to_nat (4 + 2 * Z.of_nat (k `mod` 8))%Z = (4 + 2 * (k `mod` 8))%nat.
Proof. lia. Qed.

Lemma vdrwd_ring_pa (pd pav pu : SailStdpp.Values.mword 64) (k : nat) :
  ring_entry_pa (virtio_init_cfg pd pav pu) k = d_ring pav (k `mod` 8).
Proof.
  unfold ring_entry_pa, d_ring, pa_off, vq_avail_ring_off, virtio_init_cfg.
  cbn [vc_avail]. rewrite vdrwd_mod8_z vdrwd_ring_off_nat. reflexivity.
Qed.

Lemma vdrwd_ops_sec_pa (h : nat) :
  pa_add (d_ops h : Arch.pa) 8 = pa_add disk_base (168 + 16 * h + 8).
Proof. unfold d_ops. rewrite pa_add_add. reflexivity. Qed.

Lemma vdrwd_len1024 : Z.to_nat (bv_unsigned (Z_to_bv 32 1024)) = 1024%nat.
Proof. vm_compute. reflexivity. Qed.

(* THE pure half: a pin that CONTAINS the sixteen windows (and, for a write
   request, the payload) parses to exactly the request the driver meant. *)
Lemma vdrwd_mk_pin (kq : nat * positive)
    (pd pav pu : SailStdpp.Values.mword 64) (b : Arch.pa)
    (np h m2 t : nat) (wr sector : SailStdpp.Values.mword 64)
    (bs : list (bv 8)) (pin mbuf : _) :
  (h < 8)%nat -> (m2 < 8)%nat -> (t < 8)%nat ->
  length bs = 1024%nat ->
  (forall m, m ∈ vdrwd_regions pd pav b np h m2 t wr sector mbuf -> m ⊆ pin) ->
  (bv_unsigned (vdrw_ty wr) = virtio_blk_t_out ->
     range_map (b_data b) 1024 (fun j => bs !!! j) ⊆ pin) ->
  d_info_status h ∉ pa_range (b_data b) 1024 ->
  slot_pin_ok (virtio_init_cfg pd pav pu) np (vdrwd_slot kq b h wr sector bs) pin.
Proof.
  intros Hh Hm Ht Hlen Hsub Hbuf Hstat.
  destruct (vdrwc_ty_flags wr) as [Htyv Hflags].
  unfold vdrwd_slot.
  apply (mk_pin_slot_ok (virtio_init_cfg pd pav pu) np pd pin h m2 t
           (d_ops h) (b_data b) (d_info_status h) (vdrw_ty wr) sector bs kq).
  - reflexivity.
  - reflexivity.
  - exact Hh.
  - exact Hm.
  - exact Ht.
  - rewrite vdrwd_ring_pa.
    apply (vdrwd_read_reg _ 2 (Z_to_bv 16 (Z.of_nat h)) pin ltac:(lia)).
    apply Hsub. apply (elem_of_list_lookup_2 _ 0). reflexivity.
  - split_and!.
    + apply (vdrwd_read_reg _ 8 (d_ops h : SailStdpp.Values.mword 64) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 1). reflexivity.
    + apply (vdrwd_read_reg _ 4 (Z_to_bv 32 16) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 2). reflexivity.
    + apply (vdrwd_read_reg _ 2 (Z_to_bv 16 1) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 3). reflexivity.
    + apply (vdrwd_read_reg _ 2 (Z_to_bv 16 (Z.of_nat m2)) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 4). reflexivity.
  - split_and!.
    + apply (vdrwd_read_reg _ 8 (b_data b : SailStdpp.Values.mword 64) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 5). reflexivity.
    + apply (vdrwd_read_reg _ 4 (Z_to_bv 32 1024) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 6). reflexivity.
    + assert (Hr : read_bytes pin (pa_add pd (16 * m2 + 12)) 2 = Some (vdrw_flags wr)).
      { apply (vdrwd_read_reg _ 2 (vdrw_flags wr) pin ltac:(lia)).
        apply Hsub. apply (elem_of_list_lookup_2 _ 7). reflexivity. }
      rewrite Hr Hflags. reflexivity.
    + apply (vdrwd_read_reg _ 2 (Z_to_bv 16 (Z.of_nat t)) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 8). reflexivity.
  - split_and!.
    + apply (vdrwd_read_reg _ 8 (d_info_status h : SailStdpp.Values.mword 64) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 9). reflexivity.
    + apply (vdrwd_read_reg _ 4 (Z_to_bv 32 1) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 10). reflexivity.
    + apply (vdrwd_read_reg _ 2 (Z_to_bv 16 2) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 11). reflexivity.
    + apply (vdrwd_read_reg _ 2 (Z_to_bv 16 0) pin ltac:(lia)).
      apply Hsub. apply (elem_of_list_lookup_2 _ 12). reflexivity.
  - apply (vdrwd_read_reg _ 4 (vdrw_ty wr) pin ltac:(lia)).
    apply Hsub. apply (elem_of_list_lookup_2 _ 13). reflexivity.
  - rewrite vdrwd_ops_sec_pa.
    apply (vdrwd_read_reg _ 8 sector pin ltac:(lia)).
    apply Hsub. apply (elem_of_list_lookup_2 _ 15). reflexivity.
  - exact Htyv.
  - intro Hout.
    replace 1024%nat with (length bs) by exact Hlen.
    apply (vdrwd_read_list (b_data b) bs pin ltac:(lia)).
    rewrite Hlen. exact (Hbuf Hout).
  - exact Hstat.
Qed.

(* the per-window identity-mapping premise, from a page-wide (or struct-wide)
   one: every address the chain formatting touches is [base + k]. *)
Lemma vdrwd_off_static (base a : Arch.pa) (k n : nat) :
  a = pa_add base k -> (k + n <= 4096)%nat ->
  (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add base j)) KP_rw) ->
  forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw.
Proof. intros -> Hkn Hs j Hj. rewrite pa_add_add. apply Hs. lia. Qed.

Section VdrwdPinRes.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{XI : CurCtx}.

  (* the three word widths and the byte, straight into the [range_map] shape *)
  Lemma vdrwd_w2 (a : Arch.pa) (w : bv 16) :
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₂ w -∗ phys_map (range_map a 2 (nth_byte w)).
  Proof.
    iIntros (Hs) "#Hb H". rewrite <- phys_word2_map.
    iApply (word2_to_phys a w Hs with "Hb H").
  Qed.

  Lemma vdrwd_w4 (a : Arch.pa) (w : bv 32) :
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₄ w -∗ phys_map (range_map a 4 (nth_byte w)).
  Proof.
    iIntros (Hs) "#Hb H". rewrite <- phys_word4_map.
    iApply (word4_to_phys a w Hs with "Hb H").
  Qed.

  Lemma vdrwd_w8 (a : Arch.pa) (w : bv 64) :
    (forall j, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₈ w -∗ phys_map (range_map a 8 (nth_byte w)).
  Proof.
    iIntros (Hs) "#Hb H". rewrite <- vdrwd_pw8_map.
    iApply (word8_to_phys a w Hs with "Hb H").
  Qed.

  Lemma vdrwd_buf_to_phys (a : Arch.pa) (bs : list (bv 8)) :
    (forall j, (j < length bs)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x) -∗ phys_list a bs.
  Proof.
    iIntros (Hs) "#Hb H". rewrite /phys_list.
    iApply (big_sepL_impl with "H").
    iIntros "!>" (k x Hk) "Hx".
    (* [↦ₚ] has not flipped (M1 stage 2): the ctx byte crosses into the raw
       disassembly law *)
    iDestruct (TsoCtx.ctx_pointsto_forget with "Hx") as "Hx".
    iApply (mem_ident_phys (pa_add a k) (DfracOwn 1) x
              (Hs k ltac:(apply lookup_lt_Some in Hk; lia)) with "Hb Hx").
  Qed.

  Lemma vdrwd_plist_map (a : Arch.pa) (bs : list (bv 8)) :
    (Z.of_nat (length bs) < 18446744073709551616)%Z ->
    phys_list a bs -∗ phys_map (range_map a (length bs) (fun j => bs !!! j)).
  Proof. intro Hn. rewrite (phys_list_map a bs Hn). iIntros "$". Qed.

  (* the status byte is in [struct disk], the buffer in a [struct buf]: an
     address disequality, and hence provable from OWNERSHIP alone. *)
  Lemma vdrwd_stat_out (sts a : Arch.pa) (v : bv 8) (bs : list (bv 8)) :
    length bs = 1024%nat ->
    phys_pointsto sts (DfracOwn 1) v -∗ phys_list a bs -∗
    ⌜sts ∉ pa_range a 1024⌝.
  Proof.
    iIntros (Hlen) "Hs Hl".
    destruct (decide (sts ∈ pa_range a 1024)) as [Hin|Hout]; [| iPureIntro; exact Hout ].
    apply pa_range_elim in Hin as (j & Hj & ->).
    assert (Hb : is_Some (bs !! j)) by (apply lookup_lt_is_Some; lia).
    destruct Hb as [x Hx].
    iDestruct (big_sepL_lookup _ bs j x Hx with "Hl") as "Hb".
    rewrite /phys_pointsto.
    iDestruct "Hs" as "[Hs _]". iDestruct "Hb" as "[Hb _]".
    iDestruct (pointsto_ne with "Hs Hb") as %Hne.
    destruct (Hne eq_refl).
  Qed.

End VdrwdPinRes.

Section VdrwdPinBuild.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{XI : CurCtx}.

  (* THE ownership half: the seventeen formatted cells, the ring cell and the
     caller's buffer become the pin and the writable footprint the publish
     accessor consumes -- plus, for a WRITE, the payload moves from the
     writable side into the pin. *)
  Lemma vdrwd_pin_res (kq : nat * positive)
      (pd pav pu : SailStdpp.Values.mword 64) (b : Arch.pa)
      (np h m2 t : nat) (wr sector : SailStdpp.Values.mword 64)
      (bs bsl : list (bv 8)) :
    (h < 8)%nat -> (m2 < 8)%nat -> (t < 8)%nat ->
    length bs = 1024%nat -> length bsl = 1024%nat ->
    (vdrwd_out wr = true -> bsl = bs) ->
    (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add pd j)) KP_rw) ->
    (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add pav j)) KP_rw) ->
    (forall j, (j < 1024)%nat -> kmap_static (svpn_of (pa_add (b_data b) j)) KP_rw) ->
    kmap_static_claims -∗
    d_ring pav (np `mod` 8) ↦₂ (Z_to_bv 16 (Z.of_nat h)) -∗
    vdrw_chain pd b h m2 t wr sector -∗
    ([∗ list] j ↦ x ∈ bs, pa_add (b_data b) j ↦ₘ x) -∗
    ∃ pin wrb,
      ⌜slot_pin_ok (virtio_init_cfg pd pav pu) np (vdrwd_slot kq b h wr sector bsl) pin⌝ ∗
      ⌜dom wrb = slot_wr (vdrwd_slot kq b h wr sector bsl)⌝ ∗
      ⌜slot_wr (vdrwd_slot kq b h wr sector bsl) ## dom pin⌝ ∗
      (* THE STRUCTURE OF THE PIN, for P6: the residue after the interrupt
         handler splits the avail-ring entry back off is exactly the fifteen
         formatted windows (plus a write's payload), pairwise disjoint. *)
      ⌜pin ∖ range_map (d_ring pav (np `mod` 8)) 2
                (nth_byte (Z_to_bv 16 (Z.of_nat h)))
        = foldr union ∅ (vdrwd_pinr_regions pd b h m2 t wr sector
                           (vdrwd_bufwin b wr bs))
       /\ pm_ok (vdrwd_pinr_regions pd b h m2 t wr sector
                   (vdrwd_bufwin b wr bs))⌝ ∗
      phys_map pin ∗ phys_map wrb ∗
      d_info_b h ↦₈ (b : SailStdpp.Values.mword 64) ∗
      b_disk b ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) ∗
      vdrw_slot_rest m2 ∗ vdrw_slot_rest t.
  Proof.
    intros Hh Hm Ht Hlen Hlensl Hbsl Hspd Hspav Hsbuf.
    iIntros "#Hkm Hring Hchain Hbuf".
    rewrite /vdrw_chain.
    iDestruct "Hchain" as "(Hops0 & Hops1 & Hops2 & Hda0 & Hdl0 & Hdf0 & Hdn0 &
                            Hda1 & Hdl1 & Hdf1 & Hdn1 & Hda2 & Hdl2 & Hdf2 & Hdn2 &
                            Hst & Hib & Hbd & Hrm & Hrt)".
    (* ---- every window into the [phys_map (range_map ...)] shape ---- *)
    iDestruct (vdrwd_w2 (d_ring pav (np `mod` 8)) (Z_to_bv 16 (Z.of_nat h))
                 ltac:(apply (vdrwd_off_static pav _ (4 + 2 * (np `mod` 8))%nat 2 eq_refl
                                ltac:(pose proof (Nat.mod_upper_bound np 8 ltac:(lia)); lia) Hspav))
                 with "Hkm Hring") as "Hring".
    iDestruct (vdrwd_w8 (d_desc pd h) (d_ops h : SailStdpp.Values.mword 64)
                 ltac:(apply (vdrwd_off_static pd _ (16 * h)%nat 8 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hda0") as "Hda0".
    iDestruct (vdrwd_w4 (pa_add pd (16 * h + 8)) (Z_to_bv 32 16)
                 ltac:(apply (vdrwd_off_static pd _ (16 * h + 8)%nat 4 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdl0") as "Hdl0".
    iDestruct (vdrwd_w2 (pa_add pd (16 * h + 12)) (Z_to_bv 16 1)
                 ltac:(apply (vdrwd_off_static pd _ (16 * h + 12)%nat 2 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdf0") as "Hdf0".
    iDestruct (vdrwd_w2 (pa_add pd (16 * h + 14)) (Z_to_bv 16 (Z.of_nat m2))
                 ltac:(apply (vdrwd_off_static pd _ (16 * h + 14)%nat 2 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdn0") as "Hdn0".
    iDestruct (vdrwd_w8 (d_desc pd m2) (b_data b : SailStdpp.Values.mword 64)
                 ltac:(apply (vdrwd_off_static pd _ (16 * m2)%nat 8 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hda1") as "Hda1".
    iDestruct (vdrwd_w4 (pa_add pd (16 * m2 + 8)) (Z_to_bv 32 1024)
                 ltac:(apply (vdrwd_off_static pd _ (16 * m2 + 8)%nat 4 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdl1") as "Hdl1".
    iDestruct (vdrwd_w2 (pa_add pd (16 * m2 + 12)) (vdrw_flags wr)
                 ltac:(apply (vdrwd_off_static pd _ (16 * m2 + 12)%nat 2 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdf1") as "Hdf1".
    iDestruct (vdrwd_w2 (pa_add pd (16 * m2 + 14)) (Z_to_bv 16 (Z.of_nat t))
                 ltac:(apply (vdrwd_off_static pd _ (16 * m2 + 14)%nat 2 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdn1") as "Hdn1".
    iDestruct (vdrwd_w8 (d_desc pd t) (d_info_status h : SailStdpp.Values.mword 64)
                 ltac:(apply (vdrwd_off_static pd _ (16 * t)%nat 8 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hda2") as "Hda2".
    iDestruct (vdrwd_w4 (pa_add pd (16 * t + 8)) (Z_to_bv 32 1)
                 ltac:(apply (vdrwd_off_static pd _ (16 * t + 8)%nat 4 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdl2") as "Hdl2".
    iDestruct (vdrwd_w2 (pa_add pd (16 * t + 12)) (Z_to_bv 16 2)
                 ltac:(apply (vdrwd_off_static pd _ (16 * t + 12)%nat 2 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdf2") as "Hdf2".
    iDestruct (vdrwd_w2 (pa_add pd (16 * t + 14)) (Z_to_bv 16 0)
                 ltac:(apply (vdrwd_off_static pd _ (16 * t + 14)%nat 2 eq_refl ltac:(lia) Hspd))
                 with "Hkm Hdn2") as "Hdn2".
    iDestruct (vdrwd_w4 (d_ops h) (vdrw_ty wr)
                 ltac:(apply (vdrwd_off_static disk_base _ (168 + 16 * h)%nat 4 eq_refl
                                ltac:(lia) vdrwd_disk_static))
                 with "Hkm Hops0") as "Hops0".
    iDestruct (vdrwd_w4 (pa_add disk_base (168 + 16 * h + 4))
                 (SailStdpp.Values.mword_of_int (len := 32) 0)
                 ltac:(apply (vdrwd_off_static disk_base _ (168 + 16 * h + 4)%nat 4 eq_refl
                                ltac:(lia) vdrwd_disk_static))
                 with "Hkm Hops1") as "Hops1".
    iDestruct (vdrwd_w8 (pa_add disk_base (168 + 16 * h + 8)) sector
                 ltac:(apply (vdrwd_off_static disk_base _ (168 + 16 * h + 8)%nat 8 eq_refl
                                ltac:(lia) vdrwd_disk_static))
                 with "Hkm Hops2") as "Hops2".
    (* ---- the status byte and the buffer, still in their own tiers ---- *)
    iDestruct (byte_to_phys (d_info_status h) (Z_to_bv 8 255)
                 ltac:(unfold d_info_status; apply vdrwd_disk_static; lia)
                 with "Hkm Hst") as "Hst".
    iDestruct (vdrwd_buf_to_phys (b_data b) bs
                 ltac:(rgall; rewrite Hlen; exact Hsbuf) with "Hkm Hbuf") as "Hbuf".
    iDestruct (vdrwd_stat_out (d_info_status h) (b_data b) (Z_to_bv 8 255) bs Hlen
                 with "Hst Hbuf") as %Hstat.
    iEval (rewrite vdrwd_pb_map) in "Hst".
    iDestruct (vdrwd_plist_map (b_data b) bs ltac:(lia) with "Hbuf") as "Hbuf".
    iEval (rewrite Hlen) in "Hbuf".
    (* ---- the sixteen fixed windows, as a function of the last one ---- *)
    iAssert (∀ mm, phys_map mm -∗
               pm_list (vdrwd_regions pd pav b np h m2 t wr sector mm))%I
      with "[Hring Hda0 Hdl0 Hdf0 Hdn0 Hda1 Hdl1 Hdf1 Hdn1 Hda2 Hdl2 Hdf2 Hdn2
             Hops0 Hops1 Hops2]" as "Hpl".
    { iIntros (mm) "Hmm".
      rewrite /pm_list /vdrwd_regions /vdrwd_pinr_regions.
      iSplitL "Hring"; [iExact "Hring"|].
      iSplitL "Hda0"; [iExact "Hda0"|].
      iSplitL "Hdl0"; [iExact "Hdl0"|].
      iSplitL "Hdf0"; [iExact "Hdf0"|].
      iSplitL "Hdn0"; [iExact "Hdn0"|].
      iSplitL "Hda1"; [iExact "Hda1"|].
      iSplitL "Hdl1"; [iExact "Hdl1"|].
      iSplitL "Hdf1"; [iExact "Hdf1"|].
      iSplitL "Hdn1"; [iExact "Hdn1"|].
      iSplitL "Hda2"; [iExact "Hda2"|].
      iSplitL "Hdl2"; [iExact "Hdl2"|].
      iSplitL "Hdf2"; [iExact "Hdf2"|].
      iSplitL "Hdn2"; [iExact "Hdn2"|].
      iSplitL "Hops0"; [iExact "Hops0"|].
      iSplitL "Hops1"; [iExact "Hops1"|].
      iSplitL "Hops2"; [iExact "Hops2"|].
      iSplitL "Hmm"; [iExact "Hmm"|].
      done. }
    (* ---- the two branches: a WRITE pins its payload, a READ leases it ---- *)
    destruct (bv_unsigned (vdrw_ty wr) =? virtio_blk_t_out) eqn:Hout.
    - (* OUT *)
      assert (Hbe : bsl = bs) by (apply Hbsl; unfold vdrwd_out; exact Hout).
      iDestruct ("Hpl" with "Hbuf") as "Hpl".
      iDestruct (pm_union with "Hpl") as "(Hpin & %Hpmok & %Hsub)".
      iExists (foldr union ∅ (vdrwd_regions pd pav b np h m2 t wr sector
                 (range_map (b_data b) 1024 (fun j => bs !!! j)))),
              {[ d_info_status h := Z_to_bv 8 255 ]}.
      iDestruct (phys_map_disj with "Hpin Hst") as %Hpw.
      iFrame "Hpin Hst Hib Hbd Hrm Hrt".
      destruct Hpmok as [Hdring Hpmok'].
      iPureIntro. split_and!.
      + apply (vdrwd_mk_pin kq pd pav pu b np h m2 t wr sector bsl _
                 (range_map (b_data b) 1024 (fun j => bs !!! j))
                 Hh Hm Ht Hlensl).
        * exact Hsub.
        * intros _. rewrite Hbe.
          apply Hsub. apply (elem_of_list_lookup_2 _ 16). reflexivity.
        * exact Hstat.
      + rewrite dom_singleton_L.
        unfold slot_wr, vdrwd_slot, vs_is_out.
        cbn [rw_slot vs_req vr_type vr_status].
        rewrite Hout union_empty_r_L. reflexivity.
      + unfold slot_wr, vdrwd_slot, vs_is_out.
        cbn [rw_slot vs_req vr_type vr_status].
        rewrite Hout.
        assert (Hd : dom ({[ d_info_status h := Z_to_bv 8 255 ]} : gmap _ _)
                     ## dom (foldr union ∅ (vdrwd_regions pd pav b np h m2 t wr sector
                               (range_map (b_data b) 1024 (fun j => bs !!! j)))))
          by (apply map_disjoint_dom; symmetry; exact Hpw).
        rewrite dom_singleton_L in Hd. rewrite union_empty_r_L. exact Hd.
      + rewrite /vdrwd_bufwin Hout.
        cbn [vdrwd_regions foldr] in Hdring |- *.
        apply map_union_diff_l. exact Hdring.
      + rewrite /vdrwd_bufwin Hout. exact Hpmok'.
    - (* IN *)
      iDestruct (phys_map_disj with "Hst Hbuf") as %Hsb.
      iAssert (phys_map ∅)%I as "Hemp".
      { rewrite /phys_map big_sepM_empty. done. }
      iDestruct ("Hpl" $! ∅ with "Hemp") as "Hpl".
      iDestruct (pm_union with "Hpl") as "(Hpin & %Hpmok & %Hsub)".
      iExists (foldr union ∅ (vdrwd_regions pd pav b np h m2 t wr sector ∅)),
              ({[ d_info_status h := Z_to_bv 8 255 ]}
                 ∪ range_map (b_data b) 1024 (fun j => bs !!! j)).
      iAssert (phys_map ({[ d_info_status h := Z_to_bv 8 255 ]}
                 ∪ range_map (b_data b) 1024 (fun j => bs !!! j)))
        with "[Hst Hbuf]" as "Hwrb".
      { rewrite (phys_map_union _ _ Hsb). iFrame. }
      iDestruct (phys_map_disj with "Hpin Hwrb") as %Hpw.
      iFrame "Hpin Hwrb Hib Hbd Hrm Hrt".
      destruct Hpmok as [Hdring Hpmok'].
      iPureIntro. split_and!.
      + apply (vdrwd_mk_pin kq pd pav pu b np h m2 t wr sector bsl _ ∅
                 Hh Hm Ht Hlensl).
        * exact Hsub.
        * intro Hc. exfalso. rewrite Hc Z.eqb_refl in Hout. discriminate.
        * exact Hstat.
      + rewrite dom_union_L dom_singleton_L range_map_dom.
        unfold slot_wr, vdrwd_slot, vs_is_out, vs_len.
        cbn [rw_slot vs_req vr_type vr_status vr_buf vr_len].
        rewrite Hout vdrwd_len1024. reflexivity.
      + assert (Hd : dom ({[ d_info_status h := Z_to_bv 8 255 ]}
                            ∪ range_map (b_data b) 1024 (fun j => bs !!! j))
                     ## dom (foldr union ∅
                               (vdrwd_regions pd pav b np h m2 t wr sector ∅)))
          by (apply map_disjoint_dom; symmetry; exact Hpw).
        rewrite dom_union_L dom_singleton_L range_map_dom in Hd.
        unfold slot_wr, vdrwd_slot, vs_is_out, vs_len.
        cbn [rw_slot vs_req vr_type vr_status vr_buf vr_len].
        rewrite Hout vdrwd_len1024. exact Hd.
      + rewrite /vdrwd_bufwin Hout.
        cbn [vdrwd_regions foldr] in Hdring |- *.
        apply map_union_diff_l. exact Hdring.
      + rewrite /vdrwd_bufwin Hout. exact Hpmok'.
  Qed.

End VdrwdPinBuild.

(* ===================================================================== *)
(* §5  The [disk_res] surgery at publish, as pure set/map facts.          *)
(* ===================================================================== *)

Lemma vdrwd_mod8_insert (X : gset nat) (p : nat) :
  mod8 ({[ p ]} ∪ X) = mod8 X ∪ {[ (p `mod` 8)%nat ]}.
Proof.
  unfold mod8. apply set_eq. intro x.
  rewrite elem_of_union elem_of_singleton. split.
  - intro Hx. apply elem_of_map in Hx as (y & -> & Hy).
    apply elem_of_union in Hy as [Hy|Hy].
    + apply elem_of_singleton in Hy as ->. right. reflexivity.
    + left. apply elem_of_map. exists y. split; [reflexivity | exact Hy].
  - intros [Hx|Hx].
    + apply elem_of_map in Hx as (y & -> & Hy). apply elem_of_map.
      exists y. split; [reflexivity | apply elem_of_union_r; exact Hy].
    + subst x. apply elem_of_map. exists p. split; [reflexivity |].
      apply elem_of_union_l, elem_of_singleton. reflexivity.
Qed.

Lemma vdrwd_fresh_pos {A : Type} (np nr : nat) (fl pk : gmap nat A) :
  (nr <= np)%nat ->
  dom fl = set_seq nr (np - nr) ->
  (forall p, p ∈ dom pk -> (p < nr)%nat) ->
  (fl ∪ pk) !! np = None.
Proof.
  intros Hle Hdfl Hpk.
  apply not_elem_of_dom. rewrite dom_union_L. rewrite elem_of_union.
  intros [Hin|Hin].
  - rewrite Hdfl in Hin. apply elem_of_set_seq in Hin. lia.
  - pose proof (Hpk np Hin). lia.
Qed.

Lemma vdrwd_fl_fresh {A : Type} (np nr : nat) (fl : gmap nat A) :
  (nr <= np)%nat -> dom fl = set_seq nr (np - nr) -> fl !! np = None.
Proof.
  intros Hle Hdfl. apply not_elem_of_dom. rewrite Hdfl.
  intro Hin. apply elem_of_set_seq in Hin. lia.
Qed.

Lemma vdrwd_tr_fresh {A : Type} (np nr : nat) (fl pk : gmap nat A)
    (tr : gmap nat (nat * nat * nat)) :
  (nr <= np)%nat ->
  dom fl = set_seq nr (np - nr) ->
  (forall p, p ∈ dom pk -> (p < nr)%nat) ->
  dom tr = dom fl ∪ dom pk ->
  tr !! np = None.
Proof.
  intros Hle Hdfl Hpk Hdtr. apply not_elem_of_dom. rewrite Hdtr elem_of_union.
  intros [Hin|Hin].
  - rewrite Hdfl in Hin. apply elem_of_set_seq in Hin. lia.
  - pose proof (Hpk np Hin). lia.
Qed.

(* the four [tr] conjuncts, after recording the publisher's own triple *)
Lemma vdrwd_tr_ok_ins (tr : gmap nat (nat * nat * nat)) (np : nat) (T0 : nat * nat * nat) :
  tri_ok T0 -> (forall p T, tr !! p = Some T -> tri_ok T) ->
  forall p T, <[ np := T0 ]> tr !! p = Some T -> tri_ok T.
Proof.
  intros HT0 Hok p T Hp. destruct (decide (p = np)) as [->|Hne].
  - rewrite lookup_insert in Hp. injection Hp as <-. exact HT0.
  - rewrite (lookup_insert_ne tr np p T0 (not_eq_sym Hne)) in Hp. exact (Hok p T Hp).
Qed.

Lemma vdrwd_tr_disj_ins (tr : gmap nat (nat * nat * nat)) (np : nat)
    (T0 : nat * nat * nat) :
  (forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
     tri_set Tp ## tri_set Tq) ->
  (forall p T, tr !! p = Some T -> tri_set T ## tri_set T0) ->
  forall p q Tp Tq, p <> q -> <[ np := T0 ]> tr !! p = Some Tp ->
    <[ np := T0 ]> tr !! q = Some Tq -> tri_set Tp ## tri_set Tq.
Proof.
  intros Hdisj Hdisj0 p q Tp Tq Hpq Hp Hq.
  destruct (decide (p = np)) as [->|Hpn]; destruct (decide (q = np)) as [->|Hqn].
  - congruence.
  - rewrite lookup_insert in Hp. injection Hp as <-.
    rewrite (lookup_insert_ne tr np q T0 (not_eq_sym Hqn)) in Hq.
    apply gset_disj_sym. exact (Hdisj0 q Tq Hq).
  - rewrite lookup_insert in Hq. injection Hq as <-.
    rewrite (lookup_insert_ne tr np p T0 (not_eq_sym Hpn)) in Hp.
    exact (Hdisj0 p Tp Hp).
  - rewrite (lookup_insert_ne tr np p T0 (not_eq_sym Hpn)) in Hp.
    rewrite (lookup_insert_ne tr np q T0 (not_eq_sym Hqn)) in Hq.
    exact (Hdisj p q Tp Tq Hpq Hp Hq).
Qed.

Lemma vdrwd_tri_set_elem (h m2 t i : nat) :
  i ∈ tri_set (h, m2, t) -> i = h \/ i = m2 \/ i = t.
Proof.
  unfold tri_set. cbn. rewrite !elem_of_union !elem_of_singleton. tauto.
Qed.

Lemma vdrwd_tr_free_ins (tr : gmap nat (nat * nat * nat)) (np : nat)
    (h m2 t : nat) (fr : nat -> bool) :
  fr h = false -> fr m2 = false -> fr t = false ->
  (forall p T i, tr !! p = Some T -> i ∈ tri_set T -> fr i = false) ->
  forall p T i, <[ np := (h, m2, t) ]> tr !! p = Some T -> i ∈ tri_set T ->
    fr i = false.
Proof.
  intros Hh Hm Ht Hfree p T i Hp Hi.
  destruct (decide (p = np)) as [->|Hne].
  - rewrite lookup_insert in Hp. injection Hp as <-.
    destruct (vdrwd_tri_set_elem h m2 t i Hi) as [-> | [-> | ->] ]; assumption.
  - rewrite (lookup_insert_ne tr np p (h, m2, t) (not_eq_sym Hne)) in Hp.
    exact (Hfree p T i Hp Hi).
Qed.

(* the claims/triples coherence conjunct, after recording the publisher's
   own position in BOTH maps *)
Lemma vdrwd_coh_ins (np : nat) (fl pk : gmap nat dclaim)
    (tr : gmap nat (nat * nat * nat)) (v : dclaim) :
  (forall p w, (fl ∪ pk) !! p = Some w -> tr !! p = Some (dc_tri w)) ->
  forall p w, (<[ np := v ]> fl ∪ pk) !! p = Some w ->
    <[ np := dc_tri v ]> tr !! p = Some (dc_tri w).
Proof.
  intros Hcoh p w Hp. rewrite -(insert_union_l fl pk np v) in Hp.
  destruct (decide (p = np)) as [->|Hne].
  - rewrite lookup_insert in Hp. injection Hp as <-. apply lookup_insert.
  - rewrite (lookup_insert_ne (fl ∪ pk) np p v (not_eq_sym Hne)) in Hp.
    rewrite (lookup_insert_ne tr np p (dc_tri v) (not_eq_sym Hne)).
    exact (Hcoh p w Hp).
Qed.

Lemma vdrwd_dom_tr_ins {A : Type} (np : nat) (fl pk : gmap nat A)
    (tr : gmap nat (nat * nat * nat)) (T0 : nat * nat * nat) (b : A) :
  dom tr = dom fl ∪ dom pk ->
  dom (<[ np := T0 ]> tr) = dom (<[ np := b ]> fl) ∪ dom pk.
Proof. intro H. rewrite !dom_insert_L H. set_solver. Qed.

(* the slot the publisher records really does describe the caller's buffer *)
Lemma vdrwd_slot_link (kq : nat * positive) (b : Arch.pa) (h : nat)
    (wr sector : SailStdpp.Values.mword 64)
    (bs : list (bv 8)) :
  (h < 8)%nat -> slot_buf_link (vdrwd_slot kq b h wr sector bs) b.
Proof.
  intro Hh. unfold slot_buf_link, vdrwd_slot.
  exists h. cbn [rw_slot vs_req vr_head vr_status vr_buf].
  split_and!.
  - exact Hh.
  - apply bv16_small. exact Hh.
  - reflexivity.
  - reflexivity.
  - unfold vs_len. cbn [rw_slot vs_req vr_len]. exact vdrwd_len1024.
Qed.

Lemma vdrwd_slot_head (kq : nat * positive) (b : Arch.pa) (h : nat)
    (wr sector : SailStdpp.Values.mword 64)
    (bs : list (bv 8)) :
  (h < 8)%nat -> sl_head (vdrwd_slot kq b h wr sector bs) = h.
Proof.
  intro Hh. unfold sl_head, vdrwd_slot. cbn [rw_slot vs_req vr_head].
  rewrite (bv16_small h Hh). lia.
Qed.

Lemma vdrwd_slot_off (kq : nat * positive) (b : Arch.pa) (h : nat)
    (wr sector : SailStdpp.Values.mword 64)
    (bs : list (bv 8)) (o : Z) :
  bv_unsigned sector = o ->
  vs_sector_off (vdrwd_slot kq b h wr sector bs) = (o * 512)%Z.
Proof.
  intro Ho. unfold vs_sector_off, vdrwd_slot, virtio_sector_size.
  cbn [rw_slot vs_req vr_sector]. rewrite Ho. reflexivity.
Qed.

(* THE PUBLISHED SLOT'S CRASH-PERMIT INDEX (phase C2a): what this request
   does to the disk image, in the vocabulary of the CALLER's arguments.
   Independent of the head index and of the buffer address, which is exactly
   what lets the permit be deposited BEFORE the descriptor chain is chosen. *)
Definition vdrwd_wr (wr : SailStdpp.Values.mword 64) (sec_off : Z)
    (bs_buf : list (bv 8)) : disk_wr :=
  if vdrwd_out wr then Some (sec_off, bs_buf) else None.

Lemma vdrwd_slot_is_out (kq : nat * positive) (b : Arch.pa) (h : nat)
    (wr sector : SailStdpp.Values.mword 64) (bs : list (bv 8)) :
  vs_is_out (vdrwd_slot kq b h wr sector bs) = vdrwd_out wr.
Proof.
  unfold vs_is_out, vdrwd_out, vdrwd_slot. cbn [rw_slot vs_req vr_type].
  reflexivity.
Qed.

Lemma vdrwd_slot_wr (kq : nat * positive) (b : Arch.pa) (h : nat)
    (wr sector : SailStdpp.Values.mword 64)
    (bs_buf bs_disk : list (bv 8)) (sec_off : Z) :
  (bv_unsigned sector * 512)%Z = sec_off ->
  vs_wr (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk))
  = vdrwd_wr wr sec_off bs_buf.
Proof.
  intro Hoff. unfold vs_wr, vdrwd_wr.
  rewrite vdrwd_slot_is_out.
  destruct (vdrwd_out wr) eqn:Ho; [|reflexivity].
  rewrite (vdrwd_slot_off kq b h wr sector _ (bv_unsigned sector) eq_refl) Hoff.
  unfold vs_data, vdrwd_slot. cbn [rw_slot].
  unfold vdrwd_sldata. rewrite Ho. reflexivity.
Qed.

(* ===================================================================== *)
(* §6  P4 -- +0x176 .. +0x19a, the ring write and THE PUBLISH.            *)
(* ===================================================================== *)

Section VdrwdP4.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.


  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Ltac csne :=
    apply not_eq_sym, is_cs_idx_true_neq; [ vm_compute; reflexivity | assumption ].

  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  Lemma wp_vdrw_p4 (kq : nat * positive)
      (γu : uart_names) (γd : disk_names) (pme : Arch.pa)
      (M : regfile) (av : nat)
      (pd pav pu : SailStdpp.Values.mword 64) (b : Arch.pa)
      (wr sector : SailStdpp.Values.mword 64)
      (np nr h m2 t : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool)
      (bs_buf bs_disk : list (bv 8)) (sec_off : Z) :
    tri_ok (h, m2, t) ->
    (forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t)) ->
    fr h = false -> fr m2 = false -> fr t = false ->
    length bs_buf = 1024%nat -> length bs_disk = 1024%nat ->
    (forall j, (j < 1024)%nat -> addr_is_kdata (pa_add (b_data b) j)) ->
    (bv_unsigned sector * 512)%Z = sec_off ->
    M !!! Regidx Ra0 = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64) ->
    sie_cap_gpr KT1 M av false pme -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x176) : mword 64) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    vdrw_body γd pd pav np nr fl pk tr fr -∗
    vdrw_chain pd b h m2 t wr sector -∗
    ([∗ list] j ↦ x ∈ bs_buf, pa_add (b_data b) j ↦ₘ x) -∗
    disk_bytes γd sec_off bs_disk -∗
    (* THE CRASH PERMIT's token, deposited before the chain was formatted and
       spent into the published slot here (PermInv.v).  It is the TIMELESS
       skeleton of the client's SEQUENTIAL view shift: the shift itself is in
       [perm_inv] at the single key [kq], indexed at the sectors still to
       land -- all of them, since nothing has landed yet
       (sector-atomic-disk.md §6e). *)
    perm_pend (dn_perm γd) kq (vdrwd_wr wr sec_off bs_buf)
      (set_seq 0 (wr_nsectors (vdrwd_wr wr sec_off bs_buf))) -∗
    ( ∀ (M1 : regfile) pin,
        ⌜(forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r)
         /\ M1 !!! Regidx Ra1 = M !!! Regidx Ra1⌝ -∗
        ⌜pin ∖ range_map (d_ring pav (np `mod` 8)) 2
                 (nth_byte (Z_to_bv 16 (Z.of_nat h)))
          = foldr union ∅ (vdrwd_pinr_regions pd b h m2 t wr sector
                             (vdrwd_bufwin b wr bs_buf))
         /\ pm_ok (vdrwd_pinr_regions pd b h m2 t wr sector
                     (vdrwd_bufwin b wr bs_buf))⌝ -∗
        sie_cap_gpr KT1 M1 av false pme -∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x19a) : mword 64) -∗
        vdrw_body γd pd pav (S np) nr
                  (<[ np := DClaim b (vdrwd_slot kq b h wr sector
                                        (vdrwd_sldata wr bs_buf bs_disk))
                                   (h, m2, t) pin ]> fl) pk
                  (<[ np := (h, m2, t) ]> tr) fr -∗
        disk_claim γd np (DClaim b (vdrwd_slot kq b h wr sector
                                      (vdrwd_sldata wr bs_buf bs_disk))
                                 (h, m2, t) pin) -∗
        vdrw_slot_rest m2 -∗ vdrw_slot_rest t -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Htok Hdisj0 Hfrh Hfrm Hfrt Hlenbuf Hlendisk Hbufkd Hoff Ha0 Ha5.
    destruct Htok as (Hhm & Hht & Hmt & Hh8 & Hm8 & Ht8). cbn in Hh8, Hm8, Ht8.
    iIntros "Hcg #Htext Hpc #Hdinv #Hgeom Hbody Hchain Hbuf Hdisk Hpend Hcont".
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    iDestruct (disk_geom_static with "Hgeom") as %(Hspd & Hspav & _).
    iPoseProof "Hgeom" as "Hgeom2".
    iDestruct "Hgeom2" as "(_ & #Hap & _ & _ & _ & _ & _ & _)".
    (* the buffer's identity mapping *)
    assert (Hsbuf : forall j, (j < 1024)%nat ->
              kmap_static (svpn_of (pa_add (b_data b) j)) KP_rw)
      by (intros j Hj; apply kdata_svpn_class, Hbufkd, Hj).
    (* ---- open the lock resource ---- *)
    rewrite /vdrw_body.
    iDestruct "Hbody" as "(%Hdfl & %Hpkb & %Hdtr & %Hcoh & %Htrok & %Htrdj & %Htrfr &
                           Hpub & #Hlb & Hclaim & Huidx & Hflm & Hpkm & Hfb & Hring)".
    (* ---- +0x176  c.ld a3,8(a5) ---- *)
    assert (Hava : add_vec (M !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (d_avail_ptr : SailStdpp.Values.mword 64))
      by (rewrite Ha5; apply vdrwd_avail_ptr_addr).
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.virtio_disk_rw + 0x176) : mword 64) Ra3 Ra5
              (mword_of_int 8 : mword 12) M av pav false (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] []").
    { iApply (rwi_176 with "Htext"). }
    { rgall. iEval (rewrite Hava). iExact "Hap". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc _". rgall.
    set (N1 := <[Regidx Ra3 := regval_into_reg (pav : SailStdpp.Values.mword 64)]> M).
    change (<[Regidx Ra3 := regval_into_reg (pav : SailStdpp.Values.mword 64)]> M) with N1.
    assert (HN1a3 : N1 !!! Regidx Ra3 = (pav : SailStdpp.Values.mword 64))
      by (rewrite /N1; apply upd_eq).
    assert (HN1a5 : N1 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N1 upd_ne; [| reg_neq]; exact Ha5).
    assert (HN1a0 : N1 !!! Regidx Ra0
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /N1 upd_ne; [| reg_neq]; exact Ha0).
    assert (Hp164 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x176) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x178)) by pcstep.
    iEval (rewrite Hp164) in "Hpc".
    (* ---- +0x178  lhu a4,2(a3)  -- the avail-index read ---- *)
    assert (Hidxa : add_vec (rget N1 Ra3) (sign_extend' 64 (mword_of_int 2 : mword 12))
                    = (pa_add pav 2%nat : SailStdpp.Values.mword 64))
      by (rgall; rewrite HN1a3; apply vdrwd_idx_addr).
    iApply (wp_vdrwd_lhu_avail γu γd pme pd pav pu
              (mword_of_int (KernelSyms.virtio_disk_rw + 0x178) : mword 64) Ra4 Ra3
              (mword_of_int 2 : mword 12) N1 av np nr Hidxa
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hdinv Hgeom Hpub Hlb").
    { iApply (rwi_178 with "Htext"). }
    iIntros "%Hle Hpub Hcg Hpc".
    set (N2 := <[Regidx Ra4 := regval_into_reg
                  (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16))]> N1).
    change (<[Regidx Ra4 := regval_into_reg
                  (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16))]> N1) with N2.
    assert (HN2a4 : N2 !!! Regidx Ra4
                    = (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16)
                       : SailStdpp.Values.mword 64))
      by (rewrite /N2; apply upd_eq).
    assert (HN2a3 : N2 !!! Regidx Ra3 = (pav : SailStdpp.Values.mword 64))
      by (rewrite /N2 upd_ne; [| reg_neq]; exact HN1a3).
    assert (HN2a0 : N2 !!! Regidx Ra0
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /N2 upd_ne; [| reg_neq]; exact HN1a0).
    assert (HN2a5 : N2 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N2 upd_ne; [| reg_neq]; exact HN1a5).
    assert (Hp168 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x178) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x17c)) by pcstep.
    iEval (rewrite Hp168) in "Hpc".
    (* ---- THE RING SLOT IS FREE: the window is at most two positions wide ---- *)
    assert (Hw2 : (np - nr <= 2)%nat)
      by exact (vdrwd_window_le2 np nr fl pk tr Hdfl Hdtr Htrok Htrdj).
    assert (Hfresh : (np `mod` 8)%nat ∉ mod8 (dom fl))
      by (rewrite Hdfl; exact (vdrwd_mod8_fresh nr np Hw2)).
    assert (Hmod8 : ((np `mod` 8) < 8)%nat) by (apply Nat.mod_upper_bound; lia).
    iDestruct (ring_slots_take pav (mod8 (dom fl)) (np `mod` 8)%nat Hmod8 Hfresh
                 with "Hring") as "[Hcell Hring]".
    iDestruct "Hcell" as (w0) "Hcell".
    (* ---- +0x17c  c.andi a4,a4,7 ---- *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x17c) : mword 64) Ra4
              (mword_of_int 7 : mword 6) N2 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rwi_17c with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N3 := <[Regidx Ra4 := regval_into_reg
                  (and_vec (N2 !!! Regidx Ra4)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6))))]> N2).
    change (<[Regidx Ra4 := regval_into_reg
                  (and_vec (N2 !!! Regidx Ra4)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6))))]> N2)
      with N3.
    assert (HN3a4 : N3 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat (np `mod` 8)) : SailStdpp.Values.mword 64)).
    { rewrite /N3 upd_eq HN2a4. apply vdrwd_ring_idx. }
    assert (HN3a3 : N3 !!! Regidx Ra3 = (pav : SailStdpp.Values.mword 64))
      by (rewrite /N3 upd_ne; [| reg_neq]; exact HN2a3).
    assert (HN3a0 : N3 !!! Regidx Ra0
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /N3 upd_ne; [| reg_neq]; exact HN2a0).
    assert (HN3a5 : N3 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N3 upd_ne; [| reg_neq]; exact HN2a5).
    assert (Hp16a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x17c) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x17e)) by pcstep.
    iEval (rewrite Hp16a) in "Hpc".
    (* ---- +0x17e  c.slli a4,a4,1 ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x17e) : mword 64)
              (Regidx Ra4) Ra4 (mword_of_int 1 : mword 6) N3 av false
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rwi_17e with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N4 := <[Regidx Ra4 := regval_into_reg
                  (shift_bits_left (N3 !!! Regidx Ra4)
                     (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> N3).
    change (<[Regidx Ra4 := regval_into_reg
                  (shift_bits_left (N3 !!! Regidx Ra4)
                     (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> N3)
      with N4.
    assert (HN4a4 : N4 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat (2 * (np `mod` 8)))
                       : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_eq HN3a4. apply vdrwd_shl1. exact Hmod8. }
    assert (HN4a3 : N4 !!! Regidx Ra3 = (pav : SailStdpp.Values.mword 64))
      by (rewrite /N4 upd_ne; [| reg_neq]; exact HN3a3).
    assert (HN4a0 : N4 !!! Regidx Ra0
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /N4 upd_ne; [| reg_neq]; exact HN3a0).
    assert (HN4a5 : N4 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N4 upd_ne; [| reg_neq]; exact HN3a5).
    assert (Hp16c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x17e) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x180)) by pcstep.
    iEval (rewrite Hp16c) in "Hpc".
    (* ---- +0x180  c.add a3,a3,a4 ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x180) : mword 64) Ra3 Ra4 N4 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rwi_180 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N5 := <[Regidx Ra3 := regval_into_reg
                  (add_vec (N4 !!! Regidx Ra3) (N4 !!! Regidx Ra4))]> N4).
    change (<[Regidx Ra3 := regval_into_reg
                  (add_vec (N4 !!! Regidx Ra3) (N4 !!! Regidx Ra4))]> N4) with N5.
    assert (HN5a3 : N5 !!! Regidx Ra3
                    = add_vec (pav : SailStdpp.Values.mword 64)
                        (mword_of_int (Z.of_nat (2 * (np `mod` 8)))))
      by (rewrite /N5 upd_eq HN4a3 HN4a4; reflexivity).
    assert (HN5a0 : N5 !!! Regidx Ra0
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /N5 upd_ne; [| reg_neq]; exact HN4a0).
    assert (HN5a5 : N5 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N5 upd_ne; [| reg_neq]; exact HN4a5).
    assert (Hp16e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x180) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x182)) by pcstep.
    iEval (rewrite Hp16e) in "Hpc".
    (* ---- +0x182  sh a0,4(a3)   ring[np mod 8] := h ---- *)
    assert (Hring : add_vec (N5 !!! Regidx Ra3)
                      (sign_extend' 64 (mword_of_int 4 : mword 12))
                    = (d_ring pav (np `mod` 8) : SailStdpp.Values.mword 64))
      by (rewrite HN5a3; apply vdrwd_ring_addr).
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.virtio_disk_rw + 0x182) : mword 64) Ra0 Ra3
              (mword_of_int 4 : mword 12) N5 av w0 false with "Hcg Hpc [] [Hcell]").
    { iApply (rwi_182 with "Htext"). }
    { rgall. iEval (rewrite Hring). iExact "Hcell". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell". rgall.
    iEval (rewrite Hring HN5a0 (vdrwc_trunc16_idx' h Hh8)) in "Hcell".
    assert (Hp172 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x182) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x186)) by pcstep.
    iEval (rewrite Hp172) in "Hpc".
    (* ---- +0x186  fence rw,rw ---- *)
    iApply (wp_fence_gen_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x186) : mword 64)
              (mword_of_int 0) (mword_of_int 15) (mword_of_int 15)
              (Regidx (mword_of_int 0)) (Regidx (mword_of_int 0)) N5 av false
              with "Hcg Hpc []").
    { iApply (rwi_186 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp176 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x186) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x18a)) by pcstep.
    iEval (rewrite Hp176) in "Hpc".
    (* ---- +0x18a  c.ld a4,8(a5) ---- *)
    assert (Hava2 : add_vec (N5 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = (d_avail_ptr : SailStdpp.Values.mword 64))
      by (rewrite HN5a5; apply vdrwd_avail_ptr_addr).
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.virtio_disk_rw + 0x18a) : mword 64) Ra4 Ra5
              (mword_of_int 8 : mword 12) N5 av pav false (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] []").
    { iApply (rwi_18a with "Htext"). }
    { rgall. iEval (rewrite Hava2). iExact "Hap". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc _". rgall.
    set (N6 := <[Regidx Ra4 := regval_into_reg (pav : SailStdpp.Values.mword 64)]> N5).
    change (<[Regidx Ra4 := regval_into_reg (pav : SailStdpp.Values.mword 64)]> N5) with N6.
    assert (HN6a4 : N6 !!! Regidx Ra4 = (pav : SailStdpp.Values.mword 64))
      by (rewrite /N6; apply upd_eq).
    assert (Hp178 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x18a) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x18c)) by pcstep.
    iEval (rewrite Hp178) in "Hpc".
    (* ---- +0x18c  lhu a5,2(a4) ---- *)
    assert (Hidxa2 : add_vec (rget N6 Ra4)
                       (sign_extend' 64 (mword_of_int 2 : mword 12))
                     = (pa_add pav 2%nat : SailStdpp.Values.mword 64))
      by (rgall; rewrite HN6a4; apply vdrwd_idx_addr).
    iApply (wp_vdrwd_lhu_avail γu γd pme pd pav pu
              (mword_of_int (KernelSyms.virtio_disk_rw + 0x18c) : mword 64) Ra5 Ra4
              (mword_of_int 2 : mword 12) N6 av np nr Hidxa2
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hdinv Hgeom Hpub Hlb").
    { iApply (rwi_18c with "Htext"). }
    iIntros "_ Hpub Hcg Hpc".
    set (N7 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16))]> N6).
    change (<[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16))]> N6) with N7.
    assert (HN7a5 : N7 !!! Regidx Ra5
                    = (zero_extend' 64 (wrap16 np : SailStdpp.Values.mword 16)
                       : SailStdpp.Values.mword 64))
      by (rewrite /N7; apply upd_eq).
    assert (HN7a4 : N7 !!! Regidx Ra4 = (pav : SailStdpp.Values.mword 64))
      by (rewrite /N7 upd_ne; [| reg_neq]; exact HN6a4).
    assert (Hp17c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x18c) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x190)) by pcstep.
    iEval (rewrite Hp17c) in "Hpc".
    (* ---- +0x190  c.addiw a5,a5,1 ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x190) : mword 64) Ra5
              (mword_of_int 1 : mword 6) N7 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rwi_190 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N8 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (N7 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> N7).
    change (<[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (N7 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> N7)
      with N8.
    assert (HN8sv : trunc16 (N8 !!! Regidx Ra5)
                    = (wrap16 (S np) : SailStdpp.Values.mword 16)).
    { rewrite /N8 upd_eq HN7a5. apply vdrwd_publish_val. }
    assert (HN8a4 : N8 !!! Regidx Ra4 = (pav : SailStdpp.Values.mword 64))
      by (rewrite /N8 upd_ne; [| reg_neq]; exact HN7a4).
    assert (Hp17e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x190) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x192)) by pcstep.
    iEval (rewrite Hp17e) in "Hpc".
    (* ---- assemble the pin and the writable footprint ---- *)
    assert (Hlensl : length (vdrwd_sldata wr bs_buf bs_disk) = 1024%nat).
    { unfold vdrwd_sldata. destruct (vdrwd_out wr); assumption. }
    assert (Hbsl : vdrwd_out wr = true -> vdrwd_sldata wr bs_buf bs_disk = bs_buf).
    { unfold vdrwd_sldata. intro Ho. rewrite Ho. reflexivity. }
    iDestruct (vdrwd_pin_res kq pd pav pu b np h m2 t wr sector bs_buf
                 (vdrwd_sldata wr bs_buf bs_disk)
                 Hh8 Hm8 Ht8 Hlenbuf Hlensl Hbsl Hspd Hspav Hsbuf
                 with "Hkm Hcell Hchain Hbuf") as
      (pin wrb) "(%Hpinok & %Hwrbdom & %Hwrpin & %Hpinr & Hpin & Hwrb & Hib & Hbd & Hrm & Hrt)".
    (* ---- +0x192  sh a5,2(a4)  -- THE PUBLISH ---- *)
    assert (Hidxa3 : add_vec (rget N8 Ra4)
                       (sign_extend' 64 (mword_of_int 2 : mword 12))
                     = (pa_add pav 2%nat : SailStdpp.Values.mword 64))
      by (rgall; rewrite HN8a4; apply vdrwd_idx_addr).
    iApply (wp_vdrwd_sh_publish γu γd pme pd pav pu
              (mword_of_int (KernelSyms.virtio_disk_rw + 0x192) : mword 64) Ra5 Ra4
              (mword_of_int 2 : mword 12) N8 av np
              (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk)) pin wrb
              Hidxa3 HN8sv Hpinok Hwrbdom Hwrpin
              with "Hcg Hpc [] Hdinv Hgeom Hpub Hpin Hwrb [Hdisk Hpend]").
    { iApply (rwi_192 with "Htext"). }
    { iExists bs_disk. iSplitR.
      - iPureIntro. unfold vs_len, vdrwd_slot. cbn [rw_slot vs_req vr_len].
        rewrite vdrwd_len1024. exact Hlendisk.
      - iSplitR.
        + iPureIntro. unfold vs_is_out, vs_data, vdrwd_slot, vdrwd_sldata, vdrwd_out.
          cbn [rw_slot vs_req vr_type]. intro Ho. rewrite Ho. reflexivity.
        + (* NOTHING HAS DRAINED YET: the whole write is still owed, so the
             torn set is empty ([vs_kept_full]) and the permit is at its
             ROOT -- which is exactly the index [PermInv.perm_deposit_kq]
             handed the enqueuer back. *)
          iSplitR; [iPureIntro; rewrite vs_kept_full; apply vs_torn_empty|].
          iSplitL "Hdisk".
          * rewrite (vdrwd_slot_off kq b h wr sector
                       (vdrwd_sldata wr bs_buf bs_disk)
                       (bv_unsigned sector) eq_refl) Hoff.
            iExact "Hdisk".
          * (* [vs_perm (vdrwd_slot kq …) = kq] by conversion; the entry's
               INDEX has to be rewritten to the slot's own [vs_wr], and its
               remaining set is every sector -- nothing has landed. *)
            rewrite /vs_all.
            rewrite (vdrwd_slot_wr kq b h wr sector bs_buf bs_disk sec_off Hoff).
            iExact "Hpend". }
    iIntros "Hcg Hpc Hpub Hrcpt".
    assert (Hp182 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x192) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x196)) by pcstep.
    iEval (rewrite Hp182) in "Hpc".
    (* ---- +0x196  fence rw,rw ---- *)
    iApply (wp_fence_gen_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x196) : mword 64)
              (mword_of_int 0) (mword_of_int 15) (mword_of_int 15)
              (Regidx (mword_of_int 0)) (Regidx (mword_of_int 0)) N8 av false
              with "Hcg Hpc []").
    { iApply (rwi_196 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp186 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x196) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x19a)) by pcstep.
    iEval (rewrite Hp186) in "Hpc".
    (* ---- the claim, and the rebuilt lock resource ---- *)
    set (V := DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk))
                     (h, m2, t) pin).
    iMod (ghost_map_insert np V
            (vdrwd_fresh_pos np nr fl pk Hle Hdfl Hpkb)
            with "Hclaim") as "[Hclaim Hfrag]".
    iDestruct (big_sepM_insert (fun p v => flight_res γd p v) fl np V
                 (vdrwd_fl_fresh np nr fl Hle Hdfl)
                 with "[Hflm Hrcpt Hib Hbd]") as "Hflm".
    { iSplitR "Hflm"; [| iExact "Hflm"]. rewrite /flight_res /V.
      cbn [dc_buf dc_slot dc_tri dc_pin].
      iSplitR; [iPureIntro;
        exact (vdrwd_slot_link kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk) Hh8)|].
      iFrame "Hrcpt Hbd".
      rewrite (vdrwd_slot_head kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk) Hh8).
      iExact "Hib". }
    iApply ("Hcont" $! N8 pin with "[%] [%] Hcg Hpc [-Hfrag Hrm Hrt] [Hfrag] Hrm Hrt").
    { split.
      - intros r Hr.
        rewrite /N8 upd_ne; [| csne]. rewrite /N7 upd_ne; [| csne].
        rewrite /N6 upd_ne; [| csne]. rewrite /N5 upd_ne; [| csne].
        rewrite /N4 upd_ne; [| csne]. rewrite /N3 upd_ne; [| csne].
        rewrite /N2 upd_ne; [| csne]. rewrite /N1 upd_ne; [| csne]. reflexivity.
      - rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
        rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
        rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
        rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [| reg_neq]. reflexivity. }
    { exact Hpinr. }
    2:{ rewrite /disk_claim. iExact "Hfrag". }
    rewrite /vdrw_body.
    iSplitR.
    { iPureIntro. exact (vdrwd_dom_fl_ins nr np fl _ Hle Hdfl). }
    iSplitR; [iPureIntro; exact Hpkb|].
    iSplitR.
    { iPureIntro. exact (vdrwd_dom_tr_ins np fl pk tr (h, m2, t) V Hdtr). }
    iSplitR.
    { iPureIntro. exact (vdrwd_coh_ins np fl pk tr V Hcoh). }
    iSplitR.
    { iPureIntro.
      apply (vdrwd_tr_ok_ins tr np (h, m2, t)); [| exact Htrok].
      unfold tri_ok. cbn. split_and!; assumption. }
    iSplitR.
    { iPureIntro. exact (vdrwd_tr_disj_ins tr np (h, m2, t) Htrdj Hdisj0). }
    iSplitR.
    { iPureIntro. exact (vdrwd_tr_free_ins tr np h m2 t fr Hfrh Hfrm Hfrt Htrfr). }
    iFrame "Hpub Hlb".
    rewrite (insert_union_l fl pk np V). iFrame "Hclaim".
    iFrame "Huidx Hflm Hpkm Hfb".
    rewrite dom_insert_L vdrwd_mod8_insert. iExact "Hring".
  Qed.

End VdrwdP4.

(* ===================================================================== *)
(* §7  The P3 -> P4 glue and the P4/P5 SEAM.                              *)
(*                                                                       *)
(* [P3.vdrw_p3_exit] lives inside ProofVirtioDiskRwC's functor, so the    *)
(* glue re-opens the functor over the same four callee module types.      *)
(*                                                                       *)
(* !! THE ONE MISSING CONJUNCT.  What P4 provides is [vdrw_p3_exit_x],    *)
(* which is [P3.vdrw_p3_exit] plus ONE extra pure hypothesis:             *)
(*                                                                       *)
(*   ⌜forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t)⌝    *)
(*                                                                       *)
(* -- the publisher's own descriptor triple is disjoint from every        *)
(* recorded one.  [disk_res]'s sixth conjunct says every recorded triple  *)
(* member has [fr i = false], and the allocator held [fr h = fr m2 =      *)
(* fr t = true] BEFORE it cleared those three bits -- but the seam        *)
(* exports the body at the CLEARED [fr], for which the conjunct is        *)
(* vacuous at h/m2/t, so the fact is no longer derivable downstream.      *)
(* It is available (and one line) in P2.3, where the bits are still set;  *)
(* adding it to [vdrw_p2_exit]/[vdrw_p3_exit] and threading it through    *)
(* [wp_vdrw_p3_seam] is what makes [vdrw_p3_exit_x] equal to              *)
(* [P3.vdrw_p3_exit] and closes the composition.  P4 needs it BOTH to     *)
(* record [np |-> (h,m2,t)] in [tr] (disk_res's fifth conjunct) and       *)
(* nowhere else -- the ring-slot freshness is derived here from the       *)
(* triple-counting bound alone ([vdrwd_window_le2]).                      *)
(* ===================================================================== *)

