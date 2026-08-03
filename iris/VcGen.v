(* VcGen.v -- a reflective verification-condition generator for SEQUENTIAL
   (straight-line) instruction blocks.

   Motivation.  Today a straight-line block is verified by chaining the
   per-instruction WPs (wp_addi_gpr / wp_store_gpr / ...) by hand: one
   [iApply] per instruction, re-threading mmode_config / pc_is / gpr_file /
   points-to through every step (WpTimerinit, WpStartNew, ... are 20-35 such
   steps and 1-3 kloc each).  All of that Iris plumbing is IDENTICAL per
   instruction shape; only the data (registers, immediates, addresses) vary.

   This file factors the plumbing out ONCE.  A block is described in a small
   deep-embedded language:

     - [sval]     symbolic 64-bit values: either a CONSTANT [SC z] or a
                  symbolic variable plus concrete offset [SX x off]
                  (offsets canonicalized mod 2^64).  The var/offset normal
                  form is what makes memory addressing DECIDABLE: two
                  addresses match iff they are syntactically equal.
     - [vop]      the instruction alphabet the VCgen understands (currently
                  addi / add / lui / ld / sd -- the straight-line workhorses;
                  extending it = one [vop] constructor + one case in
                  [vc_step] + one case in [wp_vc_block]).
     - [vstate]   a symbolic machine state: concrete pc, a symbolic register
                  file [gmap regidx sval], and a symbolic word heap
                  [list (sval * sval)] of 8-byte cells (address, value).
                  The heap IS the block's memory footprint: it lists exactly
                  the points-to facts (with full ownership -- this is
                  sequential code) the block needs.
     - [vc_step] / [vc_block]   the symbolic executor.  Purely computational:
                  for a concrete program it runs by [vm_compute].

   The single Iris lemma [wp_vc_block] (proved once, by induction on the
   program, dispatching to the EXISTING per-instruction leaf WPs) says: if
   [vc_block st prog = Some st'] then the block's WP holds, taking the
   resources described by [st] (pc_is / gpr_file / one [a ↦₈ v] per heap
   cell) and handing the continuation the resources described by [st'].

   Using it on a concrete block therefore costs:
     - the [instr] decode facts (needed by any approach; built from
       [kernel_text] with the existing ti_mk / kv_mk templates), and
     - ONE [vm_compute]-discharged [vc_block ... = Some ...] premise, and
     - one [iApply wp_vc_block].
   No per-instruction Iris reasoning, no manual resource threading.

   Lifting into Iris / concurrency.  [wp_vc_block] is an ordinary lemma about
   [WP Loop] in the same CSL as everything else: its pre/post are plain
   [↦ᵣ]/[↦₈] resources, so a client can take the footprint out of a lock
   invariant before the block and put the (symbolically updated) footprint
   back afterwards -- concurrent reasoning happens before/after exactly as
   with the hand-chained proofs.  The determinism/ownership assumption lives
   only INSIDE the block: full ownership of the touched cells for its
   duration.

   Scope / assumptions (v1):
     - M-mode straight-line code (the [mmode_config]/[wp_instr] layer).  The
       S-mode layer (SmodeCore) has structurally identical leaf WPs; an
       S-mode [wp_vc_block_s] is the same induction over those leaves.
     - 8-byte loads/stores ([ld]/[sd], incl. their RVC forms via the [instr]
       ExecuteAs indirection).  Byte accesses (lb/sb) would add a byte-cell
       flavor to the heap.
     - no control flow: branches/jumps end a block (compose blocks with the
       existing jal/jalr/beq WPs). *)
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExtras WpGpr.
Require Import InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. Symbolic values.                                                     *)
(* ====================================================================== *)

(* A symbolic 64-bit value: a constant, or "variable x + concrete offset".
   Constants and offsets are kept CANONICAL in [0, 2^64) ([wrap64]d by every
   operation), so syntactic equality [sval_beq] decides denotational equality
   for same-variable values -- which is what memory-address matching needs. *)
(* 32-bit symbolic values, for tracking lw/sw/addiw word (32-bit) data:
   a constant, or "low 32 bits of variable x, plus offset".  [trunc32] is
   spelled EXACTLY as the model's store-value extraction (wp_csw_s's
   [storeval]), so the leaf WPs' terms match syntactically. *)
Definition wrap32 (z : Z) : Z := bv_wrap 32 z.
(* [trunc32] now lives in [RiscvExtras] (spelled EXACTLY as wp_csw_s's
   [storeval]), so the low-level leaf WPs can share it. *)

Inductive sval32 : Type :=
  | SC32 (z : Z)               (* the constant [mword_of_int z : mword 32] *)
  | SX32 (x : nat) (off : Z).  (* [trunc32 (ρ x) + off]                     *)

Definition sval32_den (ρ : nat -> mword 64) (v : sval32) : mword 32 :=
  match v with
  | SC32 z => mword_of_int z
  | SX32 x off => add_vec (trunc32 (ρ x)) (mword_of_int off)
  end.

Definition sval32_addZ (v : sval32) (d : Z) : sval32 :=
  match v with
  | SC32 z => SC32 (wrap32 (z + d))
  | SX32 x o => SX32 x (wrap32 (o + d))
  end.

Definition sval32_beq (v w : sval32) : bool :=
  match v, w with
  | SC32 z1, SC32 z2 => Z.eqb z1 z2
  | SX32 xa oa, SX32 xb ob => Nat.eqb xa xb && Z.eqb oa ob
  | _, _ => false
  end.

Inductive sval : Type :=
  | SC (z : Z)                 (* the constant [mword_of_int z]            *)
  | SX (x : nat) (off : Z)     (* [ρ x + off] for the valuation ρ          *)
  | S32 (v : sval32).          (* [sign_extend' 64 (sval32_den ρ v)] -- a
                                  register holding a sign-extended WORD
                                  (the result of an lw / addiw)            *)

Definition wrap64 (z : Z) : Z := bv_wrap 64 z.

Definition sval_den (ρ : nat -> mword 64) (v : sval) : mword 64 :=
  match v with
  | SC z => mword_of_int z
  | SX x off => add_vec (ρ x) (mword_of_int off)
  | S32 w => sign_extend' 64 (sval32_den ρ w)
  end.

(* 64-bit offset arithmetic is only meaningful on the non-S32 shapes; the
   executors guard every use of [sval_addZ]/[sval_add] with [sval_is64]. *)
Definition sval_is64 (v : sval) : bool :=
  match v with S32 _ => false | _ => true end.

(* add a concrete offset (the ADDI/address-computation workhorse). *)
Definition sval_addZ (v : sval) (d : Z) : sval :=
  match v with
  | SC z => SC (wrap64 (z + d))
  | SX x o => SX x (wrap64 (o + d))
  | S32 w => S32 w   (* junk clause; unreachable under the sval_is64 guards *)
  end.

(* symbolic ADD: defined when at least one side is a constant.  var + var is
   representable in no normal form here, so the VCgen (honestly) fails on it. *)

Definition sval_beq (v w : sval) : bool :=
  match v, w with
  | SC z1, SC z2 => Z.eqb z1 z2
  | SX xa oa, SX xb ob => Nat.eqb xa xb && Z.eqb oa ob
  | S32 a, S32 b => sval32_beq a b
  | _, _ => false
  end.

Lemma sval32_beq_eq (v w : sval32) : sval32_beq v w = true -> v = w.
Proof.
  destruct v as [za|xa oa], w as [zb|xb ob]; simpl; intro H; try discriminate.
  - apply Z.eqb_eq in H. by subst.
  - apply andb_true_iff in H as [Hx Ho].
    apply Nat.eqb_eq in Hx. apply Z.eqb_eq in Ho. by subst.
Qed.

Lemma sval_beq_eq (v w : sval) : sval_beq v w = true -> v = w.
Proof.
  destruct v as [za|xa oa|va], w as [zb|xb ob|vb]; simpl; intro H; try discriminate.
  - apply Z.eqb_eq in H. by subst.
  - apply andb_true_iff in H as [Hx Ho].
    apply Nat.eqb_eq in Hx. apply Z.eqb_eq in Ho. by subst.
  - apply sval32_beq_eq in H. by subst.
Qed.

(* ---- denotation algebra: the symbolic ops track the model's [add_vec] ---- *)

(* mword_of_int is invariant under wrapping (Z_to_bv wraps anyway). *)
Lemma mword_of_int_wrap (z : Z) :
  (mword_of_int (wrap64 z) : mword 64) = mword_of_int z.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold wrap64. apply bv_wrap_bv_wrap. lia.
Qed.

(* mword_of_int inverts uint (64-bit). *)
Lemma mword_of_int_uint (w : mword 64) : mword_of_int (uint w) = w.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite uint_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  apply Z_to_bv_bv_unsigned.
Qed.


(* the one lemma every register/address computation reduces to (for the
   64-bit shapes; the executors never apply [sval_addZ] to an [S32]) *)
Lemma sval_den_addZ (ρ : nat -> mword 64) (v : sval) (d : Z) :
  sval_is64 v = true ->
  sval_den ρ (sval_addZ v d) = add_vec (sval_den ρ v) (mword_of_int d).
Proof.
  destruct v as [z|x o|w]; [intros _..|discriminate]; simpl.
  - rewrite mword_of_int_wrap.
    change (add_vec (mword_of_int z) (mword_of_int d))
      with (add_vec_int (mword_of_int z : mword 64) d).
    symmetry. apply avi_mword.
  - rewrite mword_of_int_wrap.
    change (add_vec (add_vec (ρ x) (mword_of_int o)) (mword_of_int d))
      with (add_vec_int (add_vec_int (ρ x) o) d).
    change (add_vec (ρ x) (mword_of_int (o + d)))
      with (add_vec_int (ρ x) (o + d)).
    symmetry. apply avi_assoc.
Qed.


(* the immediate of an I-type/load/store instruction, as the canonical Z of
   its sign-extension -- so that [mword_of_int (zimm12 imm)] IS the model's
   [sign_extend' 64 imm].  Computable ([vm_compute]) for concrete [imm]. *)
Definition zimm12 (imm : mword 12) : Z := uint (sign_extend' 64 imm : mword 64).

(* the ADDIW immediate as a canonical 32-bit Z (c.addiw carries a 6-bit
   immediate that the decoder widens twice). *)
Definition zimm32 (imm : mword 6) : Z :=
  uint (trunc32 (sign_extend' 64 (sign_extend' 12 imm)) : mword 32).

Lemma sval_den_add_imm (ρ : nat -> mword 64) (v : sval) (imm : mword 12) :
  sval_is64 v = true ->
  sval_den ρ (sval_addZ v (zimm12 imm)) =
  add_vec (sval_den ρ v) (sign_extend' 64 imm).
Proof.
  intro H64. rewrite (sval_den_addZ _ _ _ H64). unfold zimm12.
  by rewrite mword_of_int_uint.
Qed.

(* the fully general offset form (any 64-bit offset word, canonical Z = its
   uint) -- used by the S-mode c.sdsp/c.ldsp cases, whose offsets are
   zero-extended rather than sign-extended. *)
Lemma sval_den_add_off (ρ : nat -> mword 64) (v : sval) (off : mword 64) :
  sval_is64 v = true ->
  sval_den ρ (sval_addZ v (uint off)) = add_vec (sval_den ρ v) off.
Proof.
  intro H64. rewrite (sval_den_addZ _ _ _ H64). by rewrite mword_of_int_uint.
Qed.

(* collapse two consecutive concrete offsets into one canonical one; the
   seam lemma for matching a hand-proof's [add_vec (add_vec x o1) o2]
   address spelling against the VCgen's canonical [x + wrap64 (o1+o2)]. *)
Lemma add_vec_off2 (x o1 o2 : mword 64) :
  add_vec (add_vec x o1) o2 = add_vec x (mword_of_int (wrap64 (uint o1 + uint o2))).
Proof.
  rewrite -{1}(mword_of_int_uint o1) -{1}(mword_of_int_uint o2).
  rewrite mword_of_int_wrap.
  change (add_vec (add_vec x (mword_of_int (uint o1))) (mword_of_int (uint o2)))
    with (add_vec_int (add_vec_int x (uint o1)) (uint o2)).
  change (add_vec x (mword_of_int (uint o1 + uint o2)))
    with (add_vec_int x (uint o1 + uint o2)).
  apply avi_assoc.
Qed.

(* ---- the 32-bit (word) algebra: trunc32 / sign-extension interplay ---- *)

(* the ADDIW leaf spells the truncation as a bare [subrange _ 31 0]; the
   outer [autocast] of [trunc32] is between CONVERTIBLE indices
   ((4*8-1)-0+1 vs 32), so [change] them equal first. *)
Lemma trunc32_subrange (w : mword 64) :
  trunc32 w = subrange_vec_dec w 31 0.
Proof.
  unfold trunc32.
  change (Z.sub (Z.mul 4 8) 1) with 31.
  change (31 - 0 + 1) with 32.
  apply autocast_id.
Qed.

(* the unsigned view of [trunc32]: plain wrap to 32 bits. *)
Lemma trunc32_unsigned (w : mword 64) :
  bv_unsigned (trunc32 w) = bv_wrap 32 (bv_unsigned w).
Proof.
  rewrite trunc32_subrange.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (31 - 0 + 1)) with 32%N.
  reflexivity.
Qed.

(* wrapping a signed reading back to 32 bits recovers the unsigned reading. *)
Lemma wrap32_swrap (u : Z) : bv_wrap 32 (bv_swrap 32 u) = bv_wrap 32 u.
Proof.
  unfold bv_swrap, bv_wrap.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* truncation cancels sign extension (an lw'd value stored back by sw). *)
Lemma trunc32_sext (w : mword 32) : trunc32 (sign_extend' 64 w) = w.
Proof.
  apply bv_eq. rewrite trunc32_unsigned.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  rewrite bv_wrap_bv_wrap; [|lia].
  unfold bv_signed. rewrite wrap32_swrap.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* truncation distributes over 64-bit addition (low bits of a sum). *)
Lemma trunc32_add (a b : mword 64) :
  trunc32 (add_vec a b) = add_vec (trunc32 a) (trunc32 b).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
         SailStdpp.Values.with_word, MachineWord.MachineWord.add.
  apply bv_eq.
  rewrite trunc32_unsigned.
  rewrite bv_add_unsigned.
  rewrite bv_add_unsigned.
  rewrite !trunc32_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite bv_wrap_bv_wrap; [|lia].
  rewrite bv_wrap_add_idemp. reflexivity.
Qed.

(* [c.addiw rd,rd,1] on a small non-negative [int]: the 32-bit truncation of
   the widened result is the literal successor.  This is the whole arithmetic
   content of "++ on an int field", shared by push_off's noff and filedup's
   f->ref. *)
Lemma moi32_storeval_succ (z : Z) : (0 <= z)%Z -> (z + 1 < 2^31)%Z ->
  trunc32 (sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 (mword_of_int z : mword 32))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
  = (mword_of_int (z + 1) : mword 32).
Proof.
  intros Hz0 Hb.
  rewrite <- trunc32_subrange. rewrite trunc32_sext. rewrite trunc32_add.
  rewrite trunc32_sext.
  assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) = (mword_of_int 1 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HK.
  apply bv_eq.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  rewrite (moi32_small z ltac:(change (2^32) with (2*2^31); lia)).
  rewrite (moi32_small 1 ltac:(lia)).
  rewrite moi32_unsigned.
  rewrite (bvw32_small (z+1) ltac:(change (2^32) with (2*2^31); lia)).
  lia.
Qed.

(* truncation of a 64-bit constant is the 32-bit constant. *)
Lemma trunc32_mword_of_int (z : Z) :
  trunc32 (mword_of_int z : mword 64) = (mword_of_int z : mword 32).
Proof.
  apply bv_eq. rewrite trunc32_unsigned.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite !Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite bv_wrap_bv_wrap; [|lia]. reflexivity.
Qed.

(* the 32-bit twins of the 64-bit constant lemmas. *)
Lemma mword_of_int_wrap32' (z : Z) :
  (mword_of_int (wrap32 z) : mword 32) = mword_of_int z.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  unfold wrap32. apply bv_wrap_bv_wrap. lia.
Qed.

Lemma mword_of_int_uint32 (w : mword 32) : mword_of_int (uint w) = w.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  pose proof (bv_unsigned_in_range _ w) as Hr.
  rewrite Z2N.id; [|lia].
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma avi_assoc32 (a : mword 32) (x y : Z) :
  add_vec (add_vec a (mword_of_int x)) (mword_of_int y)
  = add_vec a (mword_of_int (x + y)).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
         SailStdpp.Values.with_word, mword_of_int,
         MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite !bv_add_unsigned !Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite bv_wrap_add_idemp_l.
  rewrite !bv_wrap_add_idemp_r.
  rewrite Z.add_shuffle0.
  rewrite bv_wrap_add_idemp_r.
  f_equal. lia.
Qed.

(* 32-bit "+0 is identity" (the twin of avi0). *)

(* sval32 offset arithmetic tracks 32-bit add_vec. *)
Lemma sval32_den_addZ (ρ : nat -> mword 64) (v : sval32) (d : Z) :
  sval32_den ρ (sval32_addZ v d) = add_vec (sval32_den ρ v) (mword_of_int d).
Proof.
  destruct v as [z|x o]; simpl.
  - rewrite mword_of_int_wrap32'.
    unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
    apply bv_eq. rewrite bv_add_unsigned !Z_to_bv_unsigned.
    change (MachineWord.MachineWord.Z_idx 32) with 32%N.
    rewrite bv_wrap_add_idemp. reflexivity.
  - rewrite mword_of_int_wrap32'.
    symmetry. apply avi_assoc32.
Qed.

(* a plain variable (offset 0) denotes the valuation directly -- the shape
   clients use to seed a register with its current (unknown) value. *)
Lemma sval_den_SX0 (ρ : nat -> mword 64) (x : nat) :
  sval_den ρ (SX x 0) = ρ x.
Proof.
  cbn [sval_den].
  change (add_vec (ρ x) (mword_of_int 0)) with (add_vec_int (ρ x) 0).
  apply avi0.
Qed.

(* truncate a 64-bit symbolic value to a 32-bit one (total; sound). *)
Definition sval_trunc32 (v : sval) : sval32 :=
  match v with
  | SC z => SC32 (wrap32 z)
  | SX x off => SX32 x (wrap32 off)
  | S32 w => w
  end.

Lemma sval_trunc32_den (ρ : nat -> mword 64) (v : sval) :
  sval32_den ρ (sval_trunc32 v) = trunc32 (sval_den ρ v).
Proof.
  destruct v as [z|x o|w]; simpl.
  - rewrite mword_of_int_wrap32' trunc32_mword_of_int. reflexivity.
  - rewrite trunc32_add trunc32_mword_of_int mword_of_int_wrap32'.
    reflexivity.
  - rewrite trunc32_sext. reflexivity.
Qed.

(* decidable equality on register indices (via the uint injection). *)
Definition regidx_eqb (a b : regidx) : bool :=
  match a, b with Regidx x, Regidx y => Z.eqb (uint x) (uint y) end.

(* ====================================================================== *)
(* 2. The instruction alphabet and the symbolic machine state.             *)
(* ====================================================================== *)

(* The VCgen's instruction alphabet.  Each constructor's [vop_ast] is the
   TARGET instruction of an [instr pc is_rvc i] fact, so RVC forms (c.addi /
   c.mv / c.ldsp / c.sdsp / ...) are covered through the [instr] ExecuteAs
   indirection with [is_rvc = true], exactly as for the leaf WPs. *)


(* one program entry: fetch width (RVC?) + the target instruction *)

(* symbolic state: concrete pc, symbolic registers, symbolic word heap.
   The heap holds 8-byte cells (address, value); every cell corresponds to
   one FULLY-OWNED [a ↦₈ v] in the Iris lifting, so distinctness of the
   cells' concrete addresses is guaranteed by separation -- the VCgen itself
   never reasons about aliasing beyond syntactic address matching. *)
Record vstate := VSt {
  vpc   : Z;
  vregs : gmap regidx sval;
  vheap : list (sval * sval);       (* 8-byte cells: (address, value)      *)
  vheap4 : list (sval * sval32);    (* 4-byte cells: (address, word value) *)
}.

(* find the heap cell at (syntactically) address [a]: index + stored value.
   Polymorphic in the cell datum (8-byte cells store [sval], 4-byte [sval32]). *)
Fixpoint vheap_find {A : Type} (h : list (sval * A)) (a : sval) : option (nat * A) :=
  match h with
  | nil => None
  | (a', v) :: t => if sval_beq a' a then Some (0%nat, v)
                    else match vheap_find t a with
                         | Some (i, v') => Some (S i, v')
                         | None => None
                         end
  end.

Lemma vheap_find_lookup {A : Type} (h : list (sval * A)) (a : sval) (i : nat) (v : A) :
  vheap_find h a = Some (i, v) -> h !! i = Some (a, v).
Proof.
  revert i. induction h as [|[a' v'] t IH]; intros i H; simpl in H; [discriminate|].
  destruct (sval_beq a' a) eqn:Hbeq.
  - injection H as <- <-. apply sval_beq_eq in Hbeq. by subst a'.
  - destruct (vheap_find t a) as [[j v'']|] eqn:Hrec; [|discriminate].
    injection H as <- <-. simpl. by apply IH.
Qed.

(* ====================================================================== *)
(* 3. The symbolic executor.                                               *)
(* ====================================================================== *)



(* ====================================================================== *)
(* 4. Denotation of a symbolic state into resources.                       *)
(* ====================================================================== *)

(* The concrete register file is now a [regfile] (RegFile.v).  [vregs_den] turns
   the symbolic map [m : gmap regidx sval] into the total concrete function; a
   register absent from [m] denotes [sval_den ρ inhabitant] (never observed, as
   the symbolic map is kept total where it feeds [gpr_file]). *)
Global Instance sval_inhabited : Inhabited sval := populate (SC 0).

Definition vregs_den (ρ : nat -> mword 64) (m : gmap regidx sval)
    : regfile := fun r => sval_den ρ (m !!! r).

Lemma vregs_den_lookup (ρ : nat -> mword 64) (m : gmap regidx sval) r sv :
  m !! r = Some sv -> vregs_den ρ m !!! r = sval_den ρ sv.
Proof.
  intro H. unfold vregs_den. rewrite rf_lookup. f_equal.
  rewrite lookup_total_alt H. reflexivity.
Qed.

Lemma vregs_den_insert (ρ : nat -> mword 64) (m : gmap regidx sval) r sv :
  <[r := sval_den ρ sv]> (vregs_den ρ m) = vregs_den ρ (<[r := sv]> m).
Proof.
  apply functional_extensionality; intro r'.
  unfold vregs_den, insert, regfile_insert, rf_upd.
  destruct (bool_decide (r' = r)) eqn:Hb.
  - apply bool_decide_eq_true in Hb as ->. rewrite lookup_total_insert. reflexivity.
  - apply bool_decide_eq_false in Hb.
    rewrite lookup_total_insert_ne; [reflexivity | congruence].
Qed.

Section VcGenIris.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* one fully-owned 8-byte points-to per heap cell *)
  Definition vheap_own (ρ : nat -> mword 64) (h : list (sval * sval)) : iProp Σ :=
    ([∗ list] c ∈ h, (sval_den ρ c.1) ↦₈ (sval_den ρ c.2))%I.

  (* the block's code: one [instr] fact per program entry, at consecutive pcs *)


End VcGenIris.

(* ====================================================================== *)
(* 5. A canonical initial symbolic register file.                          *)
(*                                                                         *)
(* Blocks usually start from a register file about which nothing is known: *)
(* [vregs_init] maps x0 to the constant 0 and every other register xk to    *)
(* its own fresh variable [SX k 0].  [vregs_den_init] connects it to an     *)
(* ARBITRARY complete runtime file [m] (the shape a surrounding proof       *)
(* holds): choosing the valuation ρ k := m !!! xk makes the denotation of   *)
(* [vregs_init] literally [m], so [wp_vc_block] plugs into an existing      *)
(* [gpr_file m] without rearranging it.                                     *)
(* ====================================================================== *)

(* stored PRE-NORMALIZED ([Eval vm_compute]): the 32 mword-keyed inserts cost
   ~0.4s to normalize, and every [vm_compute]d symbolic run over a state built
   on [vregs_init] would otherwise pay that again on BOTH sides of the
   equation (and once more at Qed). *)
Definition vregs_init : gmap regidx sval :=
  Eval vm_compute in
  (list_to_map
    ((fun k => (Regidx (mword_of_int (Z.of_nat k) : mword 5),
                if Nat.eqb k 0 then SC 0 else SX k 0)) <$> seq 0 32)
   : gmap regidx sval).

(* mword_of_int inverts uint at width 5 (for the register-index geometry). *)
Lemma mword5_of_uint (i : mword 5) : mword_of_int (uint i) = i.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  pose proof (bv_unsigned_in_range _ i) as Hr.
  rewrite Z2N.id; [|lia].
  change (MachineWord.MachineWord.Z_idx 5) with 5%N.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma regidx_eqb_eq (a b : regidx) : regidx_eqb a b = true -> a = b.
Proof.
  destruct a as [x], b as [y]; simpl; intro H. apply Z.eqb_eq in H.
  f_equal. rewrite -(mword5_of_uint x) H. apply mword5_of_uint.
Qed.

Lemma vregs_init_lookup (i : mword 5) :
  vregs_init !! Regidx i
  = Some (if Z.eqb (uint i) 0 then SC 0 else SX (Z.to_nat (uint i)) 0).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    rewrite -(mword5_of_uint i) H; vm_compute; reflexivity.
Qed.

(* the AGREEMENT form: any valuation that matches [m] on the 32 register
   variables denotes [vregs_init] to [m] -- variables >= 32 are free for the
   caller's heap-cell values, which is what mid-proof seams need. *)
Lemma vregs_den_init_agree (ρ : nat -> mword 64) (m : regfile) :
  m !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ->
  (forall k : nat, (k < 32)%nat ->
     ρ k = m !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)) ->
  vregs_den ρ vregs_init = m.
Proof.
  intros Hx0 Hagree. apply functional_extensionality. intros r. destruct r as [i].
  unfold vregs_den. rewrite (lookup_total_correct _ _ _ (vregs_init_lookup i)).
  change (m (Regidx i)) with (m !!! Regidx i).
  destruct (Z.eqb (uint i) 0) eqn:Hz; simpl.
  - (* x0: den (SC 0) = mword_of_int 0 = zero_reg = m !!! x0 *)
    apply Z.eqb_eq in Hz.
    assert (Ei : i = mword_of_int 0) by (rewrite -(mword5_of_uint i) Hz; reflexivity).
    rewrite Ei Hx0.
    apply bv_eq. vm_compute. reflexivity.
  - (* xk: den (SX k 0) = ρ k + 0 = m !!! xk *)
    pose proof (uint5_lt i) as Hb.
    simpl. rewrite (Hagree (Z.to_nat (uint i)) ltac:(lia)).
    rewrite Z2Nat.id; [|lia].
    rewrite mword5_of_uint.
    change (add_vec (m !!! Regidx i) (mword_of_int 0))
      with (add_vec_int (m !!! Regidx i) 0).
    apply avi0.
Qed.

(* the canonical-valuation corollary (ρ k := m !!! xk). *)

(* dom-completeness is preserved by insert (for threading a complete file
   through a chain of register writes). *)
