(* ProofPipewrite.v -- the whole-function WP for xv6's pipewrite().

     int pipewrite(struct pipe *pi, uint64 addr, int n)

   The contract is SpecPipewrite.v; the 95 instruction facts are
   WpPipewriteDecode.v ([pwi_<off>]).  Structure of the proof:

   - THREE iAssert'ed shared continuations, nested exactly as
     ProofPipealloc's EPI/T8/T4C recipe: [pw_epi] (the epilogue at +0x58,
     reached by every path), then [pw_exits := pw_tail /\ pw_minus1] -- the
     wakeup/release tail at +0xd8 and the readopen==0/killed arm at +0x46 --
     offered as a CONJUNCTION because exactly one of them is taken and they
     must therefore SHARE the frame cells and the caller's continuation.

   - the while loop is UNBOUNDED (the sleep arm re-runs the same iteration),
     so it is an iLöb over [pw_loop], the loop-BODY assertion at +0x7e.  The
     guard [bge s2,s4] at +0x7a is NOT part of the body -- the first entry
     jumps past it (+0x44 -> +0x7e, i = 0 < n is already known) and both back
     edges arrive at it -- so it is factored as the Lemma [pw_guard_step],
     which takes the loop assertion itself as a premise.  The back edges are
     the ONLY places that still want a real [iNext] before applying the Löb IH
     (the +0xcc [c.j], and on the sleep arm the +0x98 [beq]-taken, whose later
     is stripped BEFORE wakeup/sleep run): there the [▷] has to come off [IH]
     and [HEX] as well as off the goal, and stripping [▷ sched_vc] with them is
     the price -- so those three sites keep the [iNext] and the [sched_vc]
     re-introduction after it.  EVERY OTHER instruction step wants only the
     goal's later gone, and uses [iApply bi.later_intro], which does not walk
     the context at all.  See optimization.md: [iNext] costs ~1.1 s a call in
     this proof and [bi.later_intro] ~0.06 s.

   - the pipe's fields are held ASSEMBLED ([pipe_res]) at every join point and
     destructed freshly inside each iteration; [pipe_count_ok] rides through
     untouched except at the [nwrite++], where [PipeInv.pipe_count_incr_w]
     re-establishes it from the FAILED [nwrite == nread + PIPESIZE] test.

   - the 1-byte local [ch] is byte 7 of frame slot 13 (s0-97 = sp+15):
     [pw_chslot] carves that slot into [StackBytes.bytes_own] and keeps the
     8-alignment fact with it, so the slot can become a word again for the
     [c.addi16sp] pop.  copyin's destination buffer is that single byte. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.algebra Require Import frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvModelBytes.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn StackBytes CalleeSaved KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import WpLock ProcGeom CpuOwn KernelRvcDecode.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv ProcInv.
Require Import PipeInv.
Require Import SpecMyproc SpecAcquire SpecKilled SpecWakeup SpecSleep SpecCopyin SpecRelease.
Require Import CodePipewrite.
Require Import SpecPipewrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal --
   away from tp the two are the same lookup and every index here is a
   literal.  See ProofPiperead.v for why [cpu_own] must also be opaque to
   typeclass search once the base enable is the literal [true]. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).

Local Notation Rx0  := (mword_of_int 0 : mword 5).
Local Notation Rra  := (mword_of_int 1 : mword 5).
Local Notation Rtp  := (mword_of_int 4 : mword 5).
Local Notation Rs0  := (mword_of_int 8 : mword 5).
Local Notation Rs1  := (mword_of_int 9 : mword 5).
Local Notation Ra0  := (mword_of_int 10 : mword 5).
Local Notation Ra1  := (mword_of_int 11 : mword 5).
Local Notation Ra2  := (mword_of_int 12 : mword 5).
Local Notation Ra3  := (mword_of_int 13 : mword 5).
Local Notation Ra4  := (mword_of_int 14 : mword 5).
Local Notation Ra5  := (mword_of_int 15 : mword 5).
Local Notation Rs2  := (mword_of_int 18 : mword 5).
Local Notation Rs3  := (mword_of_int 19 : mword 5).
Local Notation Rs4  := (mword_of_int 20 : mword 5).
Local Notation Rs5  := (mword_of_int 21 : mword 5).
Local Notation Rs6  := (mword_of_int 22 : mword 5).
Local Notation Rs7  := (mword_of_int 23 : mword 5).
Local Notation Rs8  := (mword_of_int 24 : mword 5).
Local Notation Rs9  := (mword_of_int 25 : mword 5).
Local Notation Rs10 := (mword_of_int 26 : mword 5).
Local Notation Rs11 := (mword_of_int 27 : mword 5).

(* ===================================================================== *)
(*  Pure arithmetic (kept mword/bv-free where [lia] must run).            *)
(* ===================================================================== *)
(* ---- width-32 unsigned arithmetic ---- *)
Lemma pw_add32_unsigned (x y : mword 32) :
  bv_unsigned (add_vec x y) = bv_wrap 32 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma pw_wrap32 (z : Z) : bv_wrap 32 z = z mod 4294967296.
Proof. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma pw_wrap64 (z : Z) : bv_wrap 64 z = z mod 18446744073709551616.
Proof. unfold bv_wrap, bv_modulus. reflexivity. Qed.

(* the low 32 bits of a sign extension are the original word *)
Lemma pw_sext_low32 (v : mword 32) :
  (bv_unsigned (sign_extend' 64 v : mword 64) mod 4294967296)%Z = bv_unsigned v.
Proof.
  rewrite <- (subrange_31_0_unsigned (sign_extend' 64 v : mword 64)).
  f_equal.
  pose proof (trunc32_sext64 v) as H. unfold trunc32 in H.
  rewrite autocast_id in H. exact H.
Qed.

(* the ADDIW of a small immediate onto a sign-extended 32-bit cell *)
Lemma pw_z_addlow (z c u : Z) :
  (z mod 4294967296 = u)%Z ->
  (((z + c) mod 18446744073709551616) mod 4294967296
   = (u + c mod 4294967296) mod 4294967296)%Z.
Proof.
  intro Hu.
  rewrite (Z.mod_mod_divide (z + c) 18446744073709551616 4294967296
             ltac:(exists 4294967296; vm_compute; reflexivity)).
  rewrite <- (Zplus_mod_idemp_l z c 4294967296). rewrite Hu.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma pw_addiw_lit (v : mword 32) (co : mword 12) (c : Z) :
  bv_unsigned (sign_extend' 64 co : mword 64) = c ->
  (subrange_vec_dec (add_vec (sign_extend' 64 v : mword 64) (sign_extend' 64 co)) 31 0 : mword 32)
  = add_vec v (mword_of_int c : mword 32).
Proof.
  intro Hco. apply bv_eq.
  rewrite subrange_31_0_unsigned.
  rewrite add_vec64_unsigned Hco.
  rewrite pw_add32_unsigned moi32_unsigned !pw_wrap32 pw_wrap64.
  apply pw_z_addlow. apply pw_sext_low32.
Qed.

(* the s2 increment: [c.addiw s2,s2,1] on a small non-negative literal *)
Lemma pw_addiw_i (i : Z) :
  (0 <= i)%Z -> (i + 1 < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int i : mword 64)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
  = (mword_of_int (i + 1) : mword 64).
Proof.
  intros H0 H1.
  assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite H231 in H1.
  assert (E : (subrange_vec_dec
                 (add_vec (mword_of_int i : mword 64)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0 : mword 32)
              = (mword_of_int (i + 1) : mword 32)).
  { apply bv_eq. rewrite subrange_31_0_unsigned add_vec64_unsigned moi64_unsigned.
    assert (H1c : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64) = 1%Z)
      by (vm_compute; reflexivity).
    rewrite H1c moi32_unsigned !pw_wrap32 !pw_wrap64.
    rewrite (Z.mod_small i 18446744073709551616); [| lia].
    rewrite (Z.mod_small (i + 1) 18446744073709551616); [| lia].
    reflexivity. }
  rewrite E. apply bv_eq.
  rewrite (sext64_moi32_unsigned (i + 1) ltac:(rgall; rewrite H231; lia)).
  rewrite moi64_unsigned pw_wrap64. symmetry. apply Z.mod_small. lia.
Qed.

(* ---- the %PIPESIZE index ---- *)
Lemma pw_land511 (z : Z) : Z.land z 511 = z mod 512.
Proof.
  assert (H : Z.ones 9 = 511) by (vm_compute; reflexivity).
  rewrite <- H. rewrite Z.land_ones; [| lia].
  f_equal; try (vm_compute; reflexivity).
Qed.

Lemma pw_idx_lt (nw : mword 32) : (Z.to_nat (bv_unsigned nw mod 512) < 512)%nat.
Proof.
  assert (H : (0 <= bv_unsigned nw mod 512 < 512)%Z)
    by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

Lemma pw_andi_idx (nw : mword 32) :
  bv_unsigned (and_vec (sign_extend' 64 nw : mword 64)
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
  = Z.of_nat (Z.to_nat (bv_unsigned nw mod 512)).
Proof.
  assert (Hb : (0 <= bv_unsigned nw mod 512 < 512)%Z)
    by (apply Z.mod_pos_bound; lia).
  rewrite Z2Nat.id; [| lia].
  rewrite and_vec64_unsigned.
  assert (H511 : bv_unsigned (sign_extend' 64 (mword_of_int 511 : mword 12) : mword 64) = 511%Z)
    by (vm_compute; reflexivity).
  rewrite H511 pw_land511.
  rewrite <- (pw_sext_low32 nw). symmetry.
  apply (Z.mod_mod_divide (bv_unsigned (sign_extend' 64 nw : mword 64)) 4294967296 512).
  exists 8388608. vm_compute. reflexivity.
Qed.

(* the byte-store address inside [pipe_data] *)
Lemma pw_data_addr (p A o : mword 64) (idx : nat) :
  bv_unsigned A = Z.of_nat idx -> bv_unsigned o = 24%Z ->
  add_vec (add_vec A p) o = pa_add p (pipe_data_off + idx)%nat.
Proof.
  intros HA Ho.
  transitivity (add_vec_int p (Z.of_nat (pipe_data_off + idx)%nat)); [| reflexivity ].
  apply bv_eq. unfold add_vec_int.
  rewrite !add_vec64_unsigned moi64_unsigned HA Ho.
  rewrite !bv_wrap_add_idemp_l !bv_wrap_add_idemp_r.
  f_equal. unfold pipe_data_off. rewrite Nat2Z.inj_add.
  replace (Z.of_nat 24%nat) with 24%Z by (vm_compute; reflexivity).
  ring.
Qed.

(* ---- signed comparisons on 64-bit literals ---- *)
Lemma pw_sint_moi (z : Z) :
  (- 2 ^ 63 <= z < 2 ^ 63)%Z -> sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned bv_swrap_wrap.
  apply bv_swrap_small. rewrite Hhm. lia.
Qed.

Lemma pw_geb_s (a b : Z) :
  (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  zopz0zKzJ_s (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.geb a b.
Proof.
  intros Ha Hb. unfold zopz0zKzJ_s.
  rewrite (pw_sint_moi a Ha) (pw_sint_moi b Hb). reflexivity.
Qed.

Lemma pw_geb_s0 (b : Z) :
  (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int b : mword 64) = Z.geb 0 b.
Proof.
  intro Hb. unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hz (pw_sint_moi b Hb). reflexivity.
Qed.

(* ---- the 14-slot frame geometry ---- *)
Lemma pw_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 14%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 14%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite po_addv_assoc H. reflexivity.
Qed.

Lemma pw_ch_addr (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3999 : mword 12)) = pa_add (pa_stk X 13%nat) 7%nat.
Proof.
  unfold pa_add, pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma pw_s0_val (X : mword 64) :
  add_vec (pa_stk X 14%nat) (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))) = X.
Proof.
  unfold pa_stk, add_vec_int. apply frame_cancel.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma pw_pop_val (X : mword 64) :
  add_vec (pa_stk X 14%nat) (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))) = X.
Proof.
  unfold pa_stk, add_vec_int. apply frame_cancel.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma pw_push_val (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))) = pa_stk X 14%nat.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.


(* ===================================================================== *)
(*  Register pins at the join points.                                     *)
(* ===================================================================== *)
(* what the EPILOGUE at +0x58 needs: sp at the pushed frame, tp = cpuid, and
   s6..s11 already back at the caller's values (the three shrink-wrapped arms
   reload s6..s10 before jumping here; the n <= 0 arm never touched them). *)
Definition pw_base_regs (m M : regfile) (spr : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spr /\
  M !!! Regidx Rs6 = m !!! Regidx Rs6 /\
  M !!! Regidx Rs7 = m !!! Regidx Rs7 /\
  M !!! Regidx Rs8 = m !!! Regidx Rs8 /\
  M !!! Regidx Rs9 = m !!! Regidx Rs9 /\
  M !!! Regidx Rs10 = m !!! Regidx Rs10 /\
  M !!! Regidx Rs11 = m !!! Regidx Rs11.

Lemma pw_base_regs_cs (m M1 M2 : regfile) (spr : mword 64) :
  callee_saved M1 M2 -> pw_base_regs m M1 spr -> pw_base_regs m M2 spr.
Proof.
  intros Hcs (A & C & D & E & F & G & H). unfold pw_base_regs.
  split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity)). exact C.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity)). exact D.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity)). exact E.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity)). exact F.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity)). exact G.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity)). exact H.
Qed.

(* the readopen==0 / killed arm at +0x46: s6..s10 are still the loop's
   scratch, so only sp / tp / s1 / s11 are pinned. *)
Definition pw_min_regs (m M : regfile) (spr pi : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spr /\
  M !!! Regidx Rs1 = pi /\
  M !!! Regidx Rs11 = m !!! Regidx Rs11.

Lemma pw_min_regs_cs (m M1 M2 : regfile) (spr pi : mword 64) :
  callee_saved M1 M2 -> pw_min_regs m M1 spr pi -> pw_min_regs m M2 spr pi.
Proof.
  intros Hcs (A & C & D). unfold pw_min_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact C.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity)). exact D.
Qed.

(* the loop's own pins: every register the body reads back. *)
Definition pw_loop_regs (m M : regfile)
    (spr sp0 pi pj addr : mword 64) (n i : Z) : Prop :=
  M !!! Regidx csp_rs1 = spr /\
  M !!! Regidx Rs0 = sp0 /\
  M !!! Regidx Rs1 = pi /\
  M !!! Regidx Rs2 = (mword_of_int i : mword 64) /\
  M !!! Regidx Rs3 = pj /\
  M !!! Regidx Rs4 = (mword_of_int n : mword 64) /\
  M !!! Regidx Rs5 = addr /\
  M !!! Regidx Rs6 = (mword_of_int (-1) : mword 64) /\
  M !!! Regidx Rs7 = (mword_of_int 1 : mword 64) /\
  M !!! Regidx Rs8 = pa_add (pa_stk sp0 13%nat) 7%nat /\
  M !!! Regidx Rs9 = a_pnwrite pi /\
  M !!! Regidx Rs10 = a_pnread pi /\
  M !!! Regidx Rs11 = m !!! Regidx Rs11.

Lemma pw_loop_regs_cs (m M1 M2 : regfile)
    (spr sp0 pi pj addr : mword 64) (n i : Z) :
  callee_saved M1 M2 ->
  pw_loop_regs m M1 spr sp0 pi pj addr n i ->
  pw_loop_regs m M2 spr sp0 pi pj addr n i.
Proof.
  intros Hcs (A & C & D & E & F & G & H & I & J & K & L & N & O).
  unfold pw_loop_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 8) ltac:(vm_compute; reflexivity)). exact C.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact D.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact E.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19) ltac:(vm_compute; reflexivity)). exact F.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20) ltac:(vm_compute; reflexivity)). exact G.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21) ltac:(vm_compute; reflexivity)). exact H.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity)). exact I.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity)). exact J.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity)). exact K.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity)). exact L.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity)). exact N.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity)). exact O.
Qed.

Lemma pw_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.
Lemma pw_pv_upt_upd (V : pprivate) (P : uptd) : pv_upt (upd_upt V P) = P.
Proof. destruct V; reflexivity. Qed.
Lemma pw_pv_sz_upd (V : pprivate) (P : uptd) : pv_sz (upd_upt V P) = pv_sz V.
Proof. destruct V; reflexivity. Qed.
Lemma pw_upd_upt_upd (V : pprivate) (P Q : uptd) : upd_upt (upd_upt V P) Q = upd_upt V Q.
Proof. destruct V; reflexivity. Qed.

Section PwPieces.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* copyin CONSUMES [kalloc_env] and hands nothing back, and the loop calls it
     once per byte -- so the bundle has to be duplicable.  At [on = None] every
     conjunct is persistent ([is_lock], [kalloc_sealed], [panic_wp_any]), which is
     exactly why the sealed form is the one the copy chain takes. *)
  (* [kalloc_env _ None _] is persistent: KvmSpec.kalloc_env_None_persistent. *)

  (* the seven prologue-saved slots (ra, s0..s5), holding the caller's values *)
  Definition pw_frame7 (m : regfile) (sp0 : mword 64) : iProp Σ :=
    (pa_stk sp0 1%nat ↦₈ (m !!! Regidx Rra) ∗
     pa_stk sp0 2%nat ↦₈ (m !!! Regidx Rs0) ∗
     pa_stk sp0 3%nat ↦₈ (m !!! Regidx Rs1) ∗
     pa_stk sp0 4%nat ↦₈ (m !!! Regidx Rs2) ∗
     pa_stk sp0 5%nat ↦₈ (m !!! Regidx Rs3) ∗
     pa_stk sp0 6%nat ↦₈ (m !!! Regidx Rs4) ∗
     pa_stk sp0 7%nat ↦₈ (m !!! Regidx Rs5))%I.

  (* the five SHRINK-WRAPPED slots (s6..s10), saved only on the copy path *)
  Definition pw_frame5 (m : regfile) (sp0 : mword 64) : iProp Σ :=
    (pa_stk sp0 8%nat  ↦₈ (m !!! Regidx Rs6) ∗
     pa_stk sp0 9%nat  ↦₈ (m !!! Regidx Rs7) ∗
     pa_stk sp0 10%nat ↦₈ (m !!! Regidx Rs8) ∗
     pa_stk sp0 11%nat ↦₈ (m !!! Regidx Rs9) ∗
     pa_stk sp0 12%nat ↦₈ (m !!! Regidx Rs10))%I.

  (* slot 13 as BYTES (the 1-byte local [ch] is its byte 7) plus the untouched
     slot 14.  The 8-alignment of slot 13 rides along: a byte run does not
     carry it and the [c.addi16sp] pop needs the slot to be a word again. *)
  Definition pw_chslot (sp0 : mword 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr (pa_stk sp0 13%nat)) 8 = true⌝ ∗
     bytes_own (DfracOwn 1) (pa_stk sp0 13%nat) 8 ∗
     (∃ v : bv 64, pa_stk sp0 14%nat ↦₈ v))%I.

  Lemma pw_slot_eq (sp0 : mword 64) (k K : nat) :
    (7 + k)%nat = K -> pa_stk (pa_stk sp0 7%nat) k = pa_stk sp0 K.
  Proof. intro H. rewrite pa_stk_assoc H. reflexivity. Qed.

  Lemma pw_hi_split (sp0 : mword 64) :
    stack_own (pa_stk sp0 7%nat) 7%nat ⊢
      (∃ w8 w9 w10 w11 w12 : bv 64,
         pa_stk sp0 8%nat ↦₈ w8 ∗ pa_stk sp0 9%nat ↦₈ w9 ∗ pa_stk sp0 10%nat ↦₈ w10 ∗
         pa_stk sp0 11%nat ↦₈ w11 ∗ pa_stk sp0 12%nat ↦₈ w12) ∗ pw_chslot sp0.
  Proof.
    assert (E8  : pa_stk (pa_stk sp0 7%nat) 1%nat = pa_stk sp0 8%nat)  by (apply pw_slot_eq; reflexivity).
    assert (E9  : pa_stk (pa_stk sp0 7%nat) 2%nat = pa_stk sp0 9%nat)  by (apply pw_slot_eq; reflexivity).
    assert (E10 : pa_stk (pa_stk sp0 7%nat) 3%nat = pa_stk sp0 10%nat) by (apply pw_slot_eq; reflexivity).
    assert (E11 : pa_stk (pa_stk sp0 7%nat) 4%nat = pa_stk sp0 11%nat) by (apply pw_slot_eq; reflexivity).
    assert (E12 : pa_stk (pa_stk sp0 7%nat) 5%nat = pa_stk sp0 12%nat) by (apply pw_slot_eq; reflexivity).
    assert (E13 : pa_stk (pa_stk sp0 7%nat) 6%nat = pa_stk sp0 13%nat) by (apply pw_slot_eq; reflexivity).
    assert (E14 : pa_stk (pa_stk sp0 7%nat) 7%nat = pa_stk sp0 14%nat) by (apply pw_slot_eq; reflexivity).
    rewrite stack_own_slots. cbn [seq].
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & _)".
    iDestruct "A1" as (w8) "H8".   iEval (rewrite E8) in "H8".
    iDestruct "A2" as (w9) "H9".   iEval (rewrite E9) in "H9".
    iDestruct "A3" as (w10) "H10". iEval (rewrite E10) in "H10".
    iDestruct "A4" as (w11) "H11". iEval (rewrite E11) in "H11".
    iDestruct "A5" as (w12) "H12". iEval (rewrite E12) in "H12".
    iDestruct "A6" as (w13) "H13". iEval (rewrite E13) in "H13".
    iDestruct "A7" as (w14) "H14". iEval (rewrite E14) in "H14".
    iDestruct (slot_bytes_own with "H13") as "[%Hal Hb13]".
    iSplitL "H8 H9 H10 H11 H12".
    { iExists w8, w9, w10, w11, w12. iFrame "H8 H9 H10 H11 H12". }
    rewrite /pw_chslot. iSplitR; [done|]. iFrame "Hb13". iExists w14. iFrame "H14".
  Qed.

  Lemma pw_hi_intro (sp0 : mword 64) (w8 w9 w10 w11 w12 : bv 64) :
    pa_stk sp0 8%nat ↦₈ w8 -∗ pa_stk sp0 9%nat ↦₈ w9 -∗ pa_stk sp0 10%nat ↦₈ w10 -∗
    pa_stk sp0 11%nat ↦₈ w11 -∗ pa_stk sp0 12%nat ↦₈ w12 -∗
    pw_chslot sp0 -∗ stack_own (pa_stk sp0 7%nat) 7%nat.
  Proof.
    assert (E8  : pa_stk (pa_stk sp0 7%nat) 1%nat = pa_stk sp0 8%nat)  by (apply pw_slot_eq; reflexivity).
    assert (E9  : pa_stk (pa_stk sp0 7%nat) 2%nat = pa_stk sp0 9%nat)  by (apply pw_slot_eq; reflexivity).
    assert (E10 : pa_stk (pa_stk sp0 7%nat) 3%nat = pa_stk sp0 10%nat) by (apply pw_slot_eq; reflexivity).
    assert (E11 : pa_stk (pa_stk sp0 7%nat) 4%nat = pa_stk sp0 11%nat) by (apply pw_slot_eq; reflexivity).
    assert (E12 : pa_stk (pa_stk sp0 7%nat) 5%nat = pa_stk sp0 12%nat) by (apply pw_slot_eq; reflexivity).
    assert (E13 : pa_stk (pa_stk sp0 7%nat) 6%nat = pa_stk sp0 13%nat) by (apply pw_slot_eq; reflexivity).
    assert (E14 : pa_stk (pa_stk sp0 7%nat) 7%nat = pa_stk sp0 14%nat) by (apply pw_slot_eq; reflexivity).
    iIntros "H8 H9 H10 H11 H12 (%Hal & Hb13 & H14)".
    iDestruct "H14" as (w14) "H14".
    iDestruct (bytes_own_slot (pa_stk sp0 13%nat) Hal with "Hb13") as (w13) "H13".
    rewrite stack_own_slots. cbn [seq].
    iSplitL "H8".  { iExists w8.  iEval (rewrite E8).  iExact "H8". }
    iSplitL "H9".  { iExists w9.  iEval (rewrite E9).  iExact "H9". }
    iSplitL "H10". { iExists w10. iEval (rewrite E10). iExact "H10". }
    iSplitL "H11". { iExists w11. iEval (rewrite E11). iExact "H11". }
    iSplitL "H12". { iExists w12. iEval (rewrite E12). iExact "H12". }
    iSplitL "H13". { iExists w13. iEval (rewrite E13). iExact "H13". }
    iSplitL "H14". { iExists w14. iEval (rewrite E14). iExact "H14". }
    done.
  Qed.

  (* re-assembling the pipe's fields *)
  Lemma pw_res_intro (γp : pipe_names) (pi : mword 64)
      (nr nw ro wo : mword 32) (vname : mword 64) (bs : list (bv 8)) :
    pipe_count_ok nr nw -> length bs = PIPESIZE ->
    lock_name_field pi ↦₈ vname -∗
    a_pnread pi ↦₄ nr -∗ a_pnwrite pi ↦₄ nw -∗
    a_popen pi false ↦₄ ro -∗ a_popen pi true ↦₄ wo -∗
    pipe_endstate γp false ro -∗ pipe_endstate γp true wo -∗
    pipe_data pi bs -∗ pipe_slack pi -∗ pipe_res γp pi.
  Proof.
    intros Hc Hl. iIntros "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack".
    iExists nr, nw, ro, wo, vname, bs.
    iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack". done.
  Qed.

  (* borrow byte [idx] of the pipe buffer and put a new one back *)
  Lemma pw_data_acc (pi : mword 64) (bs : list (bv 8)) (idx : nat) (b : bv 8) :
    bs !! idx = Some b ->
    pipe_data pi bs ⊢ (pa_add pi (pipe_data_off + idx)%nat ↦ₘ b) ∗
      (∀ b' : bv 8, pa_add pi (pipe_data_off + idx)%nat ↦ₘ b' -∗
                    pipe_data pi (<[idx := b']> bs)).
  Proof.
    intro Hl. rewrite /pipe_data. iIntros "H".
    iDestruct (big_sepL_insert_acc
                 (fun (k : nat) (y : bv 8) => (pa_add pi (pipe_data_off + k)%nat ↦ₘ y)%I)
                 bs idx b Hl with "H") as "[Hb Hcl]".
    iFrame "Hb". iIntros (b') "Hb'". iApply ("Hcl" $! b' with "Hb'").
  Qed.

End PwPieces.

(* ===================================================================== *)
(*  The shared continuations, as named iProps.                            *)
(* ===================================================================== *)
Section PwConts.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ}.

  (* +0x58: the common epilogue (mv a0,s2; reload ra/s0..s5; pop; ret). *)
  Definition pw_epi `{GEN : GenId} (CID0 : CPU) (γf : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat)
      (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (P' : uptd),
       ⌜pw_base_regs m M (pa_stk sp0 14%nat)⌝ -∗
       ⌜pipe_rw_ret n (M !!! Regidx Rs2)⌝ -∗
       ⌜uptd_ext (pv_upt V) P'⌝ -∗
       pw_frame7 m sp0 -∗
       stack_own (pa_stk sp0 7%nat) 7%nat -∗
       sie_cap_gpr M (av - 14)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) C true -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0x58) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv γf (proc_addr j) pid (upd_upt V P') -∗
       running_claim j -∗
       WP (Loop : expr riscv_lang)))%I.

  (* +0xd8: wakeup(&pi->nread); release(&pi->lock); jump to the epilogue.  Three
     paths land here: the n <= 0 arm, the loop exit and the copyin failure. *)
  Definition pw_tail `{GEN : GenId} (CID0 : CPU) (γf : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (P' : uptd),
       ⌜pw_base_regs m M (pa_stk sp0 14%nat)⌝ -∗
       ⌜M !!! Regidx Rs1 = pi⌝ -∗
       ⌜pipe_rw_ret n (M !!! Regidx Rs2)⌝ -∗
       ⌜uptd_ext (pv_upt V) P'⌝ -∗
       pw_frame7 m sp0 -∗
       stack_own (pa_stk sp0 7%nat) 7%nat -∗
       sie_cap_gpr M (av - 14)%nat false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) C false -∗
       arm_pay 0%nat eb (proc_addr j) -∗
       locked γl cpu_id -∗
       pipe_res γp pi -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0xd8) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv γf (proc_addr j) pid (upd_upt V P') -∗
       running_claim j -∗
       WP (Loop : expr riscv_lang)))%I.

  (* +0x46: release(&pi->lock); i := -1; reload s6..s10; fall into the
     epilogue.  Reached when readopen == 0 or the process was killed. *)
  Definition pw_minus1 `{GEN : GenId} (CID0 : CPU) (γf : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (P' : uptd),
       ⌜pw_min_regs m M (pa_stk sp0 14%nat) pi⌝ -∗
       ⌜uptd_ext (pv_upt V) P'⌝ -∗
       pw_frame7 m sp0 -∗
       pw_frame5 m sp0 -∗
       pw_chslot sp0 -∗
       sie_cap_gpr M (av - 14)%nat false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) C false -∗
       arm_pay 0%nat eb (proc_addr j) -∗
       locked γl cpu_id -∗
       pipe_res γp pi -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0x46) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv γf (proc_addr j) pid (upd_upt V P') -∗
       running_claim j -∗
       WP (Loop : expr riscv_lang)))%I.

  (* exactly ONE of the two is taken, so they are offered as a conjunction and
     SHARE the epilogue closure. *)
  Definition pw_exits `{GEN : GenId} (CID0 : CPU) (γf : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi : mword 64) : iProp Σ :=
    (pw_tail CID0 γf Φ γs j γl γp w q m av eb C pid V n sp0 pi
     ∧ pw_minus1 CID0 γf Φ γs j γl γp w q m av eb C pid V n sp0 pi)%I.

  (* +0x7e: the loop BODY, entered with 0 <= i < n. *)
  Definition pw_loop `{GEN : GenId} (CID0 : CPU) (γa γf : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi addr : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (i : Z) (M : regfile) (Pc : uptd),
       ⌜(0 <= i < n)%Z⌝ -∗
       ⌜uptd_ext (pv_upt V) Pc⌝ -∗
       ⌜pw_loop_regs m M (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i⌝ -∗
       pw_frame7 m sp0 -∗
       pw_frame5 m sp0 -∗
       pw_chslot sp0 -∗
       sie_cap_gpr M (av - 14)%nat false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) C false -∗
       arm_pay 0%nat eb (proc_addr j) -∗
       locked γl cpu_id -∗
       pipe_res γp pi -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv γf (proc_addr j) pid (upd_upt V Pc) -∗
       kalloc_env γa None -∗
       running_claim j -∗
       pw_exits CID0 γf Φ γs j γl γp w q m av eb C pid V n sp0 pi -∗
       WP (Loop : expr riscv_lang)))%I.

End PwConts.

(* ===================================================================== *)
(*  The shrink-wrapped reload block (s6..s10), shared by the three arms    *)
(*  that saved them: +0x4e, +0xce and +0xec.                              *)
(* ===================================================================== *)
Section PwRestore.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Definition pw_restored (m M M' : regfile) : Prop :=
    M' !!! Regidx Rs6 = m !!! Regidx Rs6 /\
    M' !!! Regidx Rs7 = m !!! Regidx Rs7 /\
    M' !!! Regidx Rs8 = m !!! Regidx Rs8 /\
    M' !!! Regidx Rs9 = m !!! Regidx Rs9 /\
    M' !!! Regidx Rs10 = m !!! Regidx Rs10 /\
    (forall r : mword 5, r <> mword_of_int 22 -> r <> mword_of_int 23 ->
       r <> mword_of_int 24 -> r <> mword_of_int 25 -> r <> mword_of_int 26 ->
       M' !!! Regidx r = M !!! Regidx r).

  Lemma pw_restore5 (pme : mword 64) (b : bool)
      (p0 p1 p2 p3 p4 p5 : mword 64) (M m : regfile) (K : nat) (sp0 : mword 64) :
    M !!! Regidx csp_rs1 = pa_stk sp0 14%nat ->
    add_vec_int p0 2 = p1 -> add_vec_int p1 2 = p2 -> add_vec_int p2 2 = p3 ->
    add_vec_int p3 2 = p4 -> add_vec_int p4 2 = p5 ->
    sie_cap_gpr M K b pme -∗ pc_is p0 -∗
    instr p0 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx Rs6, false, 8)) -∗
    instr p1 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx Rs7, false, 8)) -∗
    instr p2 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx Rs8, false, 8)) -∗
    instr p3 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx Rs9, false, 8)) -∗
    instr p4 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx Rs10, false, 8)) -∗
    pw_frame5 m sp0 -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ M' : regfile, ⌜ pw_restored m M M' ⌝ -∗
        sie_cap_gpr M' K b pme -∗ pc_is p5 -∗ pw_frame5 m sp0 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp E1 E2 E3 E4 E5.
    iIntros "Hcg Hpc Hi0 Hi1 Hi2 Hi3 Hi4 (F8 & F9 & F10 & F11 & F12) Hcont".
    assert (Hb8 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 8%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb9 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 9%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb10 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 10%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb11 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 11%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb12 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 12%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    (* s6 *)
    iEval (rewrite -Hb8 -Hsp) in "F8".
    iApply (wp_cldsp_s_sconf p0 (mword_of_int 6 : mword 6) Rs6 M K (m !!! Regidx Rs6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0 F8 [-]").
    iIntros (CIDr1 Hsr1) "Hcg Hpc F8". rgall.
    iEval (rewrite Hsp Hb8) in "F8".
    set (N1 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> M).
    change (<[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> M) with N1.
    iEval (rewrite E1) in "Hpc".
    assert (HspN1 : N1 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N1 upd_ne; [exact Hsp | reg_neq]).
    (* s7 *)
    iEval (rewrite -Hb9 -HspN1) in "F9".
    iApply (wp_cldsp_s_sconf p1 (mword_of_int 5 : mword 6) Rs7 N1 K (m !!! Regidx Rs7) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1 F9 [-]").
    iIntros (CIDr2 Hsr2) "Hcg Hpc F9". rgall.
    iEval (rewrite HspN1 Hb9) in "F9".
    set (N2 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> N1).
    change (<[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> N1) with N2.
    iEval (rewrite E2) in "Hpc".
    assert (HspN2 : N2 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N2 upd_ne; [exact HspN1 | reg_neq]).
    (* s8 *)
    iEval (rewrite -Hb10 -HspN2) in "F10".
    iApply (wp_cldsp_s_sconf p2 (mword_of_int 4 : mword 6) Rs8 N2 K (m !!! Regidx Rs8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2 F10 [-]").
    iIntros (CIDr3 Hsr3) "Hcg Hpc F10". rgall.
    iEval (rewrite HspN2 Hb10) in "F10".
    set (N3 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> N2).
    change (<[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> N2) with N3.
    iEval (rewrite E3) in "Hpc".
    assert (HspN3 : N3 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N3 upd_ne; [exact HspN2 | reg_neq]).
    (* s9 *)
    iEval (rewrite -Hb11 -HspN3) in "F11".
    iApply (wp_cldsp_s_sconf p3 (mword_of_int 3 : mword 6) Rs9 N3 K (m !!! Regidx Rs9) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3 F11 [-]").
    iIntros (CIDr4 Hsr4) "Hcg Hpc F11". rgall.
    iEval (rewrite HspN3 Hb11) in "F11".
    set (N4 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> N3).
    change (<[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> N3) with N4.
    iEval (rewrite E4) in "Hpc".
    assert (HspN4 : N4 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N4 upd_ne; [exact HspN3 | reg_neq]).
    (* s10 *)
    iEval (rewrite -Hb12 -HspN4) in "F12".
    iApply (wp_cldsp_s_sconf p4 (mword_of_int 2 : mword 6) Rs10 N4 K (m !!! Regidx Rs10) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4 F12 [-]").
    iIntros (CIDr5 Hsr5) "Hcg Hpc F12". rgall.
    iEval (rewrite HspN4 Hb12) in "F12".
    set (N5 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10)]> N4).
    change (<[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10)]> N4) with N5.
    iEval (rewrite E5) in "Hpc".
    iSpecialize ("Hcont" $! CIDr5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! N5 with "[%] Hcg Hpc [F8 F9 F10 F11 F12]").
    { unfold pw_restored. split_and!.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
        rewrite /N1 upd_eq. reflexivity.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_eq. reflexivity.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_eq. reflexivity.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_eq. reflexivity.
      - rewrite /N5 upd_eq. reflexivity.
      - intros r N22 N23 N24 N25 N26.
        rewrite /N5 upd_ne; [| congruence]. rewrite /N4 upd_ne; [| congruence].
        rewrite /N3 upd_ne; [| congruence]. rewrite /N2 upd_ne; [| congruence].
        rewrite /N1 upd_ne; [| congruence]. reflexivity. }
    rewrite /pw_frame5. iFrame "F8 F9 F10 F11 F12".
  Qed.

End PwRestore.

(* ===================================================================== *)
(*  The loop GUARD at +0x7a ([bge s2,s4]).                                *)
(*  It is not part of the loop body: the first entry (+0x44) jumps PAST it *)
(*  and both back edges arrive AT it, so it takes the loop assertion as a  *)
(*  premise instead of being folded into the iLöb.                        *)
(* ===================================================================== *)
Section PwGuard.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma pw_stack7_of (m : regfile) (sp0 : mword 64) :
    pw_frame5 m sp0 -∗ pw_chslot sp0 -∗ stack_own (pa_stk sp0 7%nat) 7%nat.
  Proof.
    iIntros "(F8 & F9 & F10 & F11 & F12) HCH".
    iApply (pw_hi_intro sp0 with "F8 F9 F10 F11 F12 HCH").
  Qed.

  Lemma pw_guard_step (CID0 : CPU) (γa γf : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi addr : mword 64)
      (i : Z) (M : regfile) (Pc : uptd) :
    (0 < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= i <= n)%Z ->
    (true = false \/ proc_addr j = zero_reg -> (CID : CPU) = CID0) ->
    uptd_ext (pv_upt V) Pc ->
    pw_loop_regs m M (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i ->
    kernel_text -∗
    pw_frame7 m sp0 -∗ pw_frame5 m sp0 -∗ pw_chslot sp0 -∗
    sie_cap_gpr M (av - 14)%nat false (proc_addr j) -∗
    cpu_own 1%nat eb (proc_addr j) C false -∗
    arm_pay 0%nat eb (proc_addr j) -∗
    locked γl cpu_id -∗
    pipe_res γp pi -∗
    pc_is (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64) -∗
    pipe_ref γp w q -∗
    proc_priv γf (proc_addr j) pid (upd_upt V Pc) -∗
    kalloc_env γa None -∗
    running_claim j -∗
    pw_exits CID0 γf Φ γs j γl γp w q m av eb C pid V n sp0 pi -∗
    pw_loop CID0 γa γf Φ γs j γl γp w q m av eb C pid V n sp0 pi addr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn0 Hn31 Hi Hanch Hext Hregs.
    assert (H63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (H31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    rewrite H31 in Hn31.
    assert (Hri : (- 2 ^ 63 <= i < 2 ^ 63)%Z) by (rewrite H63; lia).
    assert (Hrn : (- 2 ^ 63 <= n < 2 ^ 63)%Z) by (rewrite H63; lia).
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 &
                        Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
    assert (Hcmp : zopz0zKzJ_s (M !!! Regidx Rs2) (M !!! Regidx Rs4) = Z.geb i n)
      by (rewrite Hs2 Hs4; apply pw_geb_s; assumption).
    iIntros "#Htext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv #Henv Hpark HEX HLP".
    iPoseProof (pwi_7a with "Htext") as "Hi7a".
    destruct (Z.geb i n) eqn:Hgb.
    - (* ==== i >= n : the copy is done, restore s6..s10 and take the tail ==== *)
      assert (Hge : (n <= i)%Z).
      { assert (Hx := Hgb). rewrite Z.geb_leb in Hx. by apply Z.leb_le. }
      assert (Hgt : zopz0zKzJ_s (M !!! Regidx Rs2) (M !!! Regidx Rs4) = true)
        by exact Hcmp.
      assert (Hal : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64)
                       (sign_extend' 64 (mword_of_int 84 : mword 13))) 0) ('b"0") = true)
        by (vm_compute; reflexivity).
      iApply (wp_bge_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x7a)) (mword_of_int 84 : mword 13)
                Rs4 Rs2 M (av - 14)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hgt Hal with "Hcg Hpc Hi7a [-]").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjce : add_vec (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64)
                       (sign_extend' 64 (mword_of_int 84 : mword 13))
                     = (mword_of_int (KernelSyms.pipewrite + 0xce) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjce) in "Hpc".
      iPoseProof (pwi_ce with "Htext") as "Hj0".
      iPoseProof (pwi_d0 with "Htext") as "Hj1".
      iPoseProof (pwi_d2 with "Htext") as "Hj2".
      iPoseProof (pwi_d4 with "Htext") as "Hj3".
      iPoseProof (pwi_d6 with "Htext") as "Hj4".
      assert (Ed0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xce) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xd0)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ed2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd0) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xd2)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ed4 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd2) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xd4)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ed6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd4) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xd6)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ed8 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd6) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (pw_restore5 (proc_addr j) false (mword_of_int (KernelSyms.pipewrite + 0xce)) (mword_of_int (KernelSyms.pipewrite + 0xd0))
                (mword_of_int (KernelSyms.pipewrite + 0xd2)) (mword_of_int (KernelSyms.pipewrite + 0xd4)) (mword_of_int (KernelSyms.pipewrite + 0xd6))
                (mword_of_int (KernelSyms.pipewrite + 0xd8)) M m (av - 14)%nat sp0
                Hsp Ed0 Ed2 Ed4 Ed6 Ed8
                with "Hcg Hpc Hj0 Hj1 Hj2 Hj3 Hj4 HF5 [-]").
      iApply wp_next_off_intro. iIntros (M') "%Hrst Hcg Hpc HF5".
      destruct Hrst as (R6 & R7 & R8 & R9 & R10 & Rrest).
      assert (Hsp' : M' !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
      { rewrite (Rrest csp_rs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hsp. }
      assert (Hs1' : M' !!! Regidx Rs1 = pi).
      { rewrite (Rrest (mword_of_int 9) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs1. }
      assert (Hs2' : M' !!! Regidx Rs2 = (mword_of_int i : mword 64)).
      { rewrite (Rrest (mword_of_int 18) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs2. }
      assert (Hs11' : M' !!! Regidx Rs11 = m !!! Regidx Rs11).
      { rewrite (Rrest (mword_of_int 27) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs11. }
      iDestruct "HEX" as "[TAIL _]". rewrite /pw_tail.
      iSpecialize ("TAIL" $! CID with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! M' Pc with "[%] [%] [%] [%] HF7 [HF5 HCH] Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Hpark").
      + unfold pw_base_regs. split_and!; assumption.
      + exact Hs1'.
      + rewrite Hs2'. right. exists i. split; [reflexivity | lia].
      + exact Hext.
      + iApply (pw_stack7_of m sp0 with "HF5 HCH").
    - (* ==== i < n : fall through into the body ==== *)
      assert (Hlt : (i < n)%Z).
      { assert (Hx := Hgb). rewrite Z.geb_leb in Hx. by apply Z.leb_gt. }
      assert (Hgf : zopz0zKzJ_s (M !!! Regidx Rs2) (M !!! Regidx Rs4) = false)
        by exact Hcmp.
      iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x7a)) (mword_of_int 84 : mword 13)
                Rs4 Rs2 M (av - 14)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hgf with "Hcg Hpc Hi7a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x7e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp7e) in "Hpc".
      rewrite /pw_loop.
      iSpecialize ("HLP" $! CID with "[%]"); [wp_next_chain|].
      iApply ("HLP" $! i M Pc with "[%] [%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Henv Hpark HEX").
      + lia.
      + exact Hext.
      + exact Hregs.
  Qed.

End PwGuard.

(* ===================================================================== *)
(*  The whole-function proof.                                             *)
(* ===================================================================== *)
Module PipewriteProof (Myproc : MYPROC) (AcquireGen : ACQUIRE_GEN) (Killed : KILLED)
                      (Wakeup : WAKEUP) (SleepGen : SLEEP_GEN) (Copyin : COPYIN)
                      (ReleaseGen : RELEASE_GEN) : PIPEWRITE.

Section ProofPipewrite.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.
  Local Ltac nz := vm_compute; discriminate.
  (* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal --
     away from tp the two are the same lookup and every index here is a
     literal.  See ProofPiperead.v for why [cpu_own] must also be opaque to
     typeclass search once the base enable is the literal [true]. *)
  Local Typeclasses Opaque cpu_own.

  Lemma wp_pipewrite_sconf (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γlp : gname)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool)
    : wp_pipewrite_sconf_body γa γf Φ γs j γlp γl γp w q m av eb C pid V n b.
  Proof.
    cbv beta delta [wp_pipewrite_sconf_body].
    intros pcE pj pi ret_tgt Hj Hjlp Hlen Ha2 Hnrange Hav Heb. subst eb.
    assert (Hav64 : (64 <= av)%nat) by (unfold pipewrite_stack in Hav; exact Hav).
    assert (H31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (H63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hcpune : eq_vec (zero_reg : mword 64) (mycpu_ret cid_word) = false)
      by (apply mycpu_ret_nonzero; apply tp_ok_cid).
    assert (Hn31 : (n < 2 ^ 31)%Z) by (destruct Hnrange as [_ HB]; exact HB).
    assert (Hn31L : (n < 2147483648)%Z) by (rewrite H31 in Hn31; exact Hn31).
    iIntros "Hcg Hown #Htext Hpc #Hpipe Href Hpriv #Henv #Hpinv #Hscheds #Hpanic Hpark Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    assert (Hbt : b = true) by (symmetry; exact Hbm).
    clear Hbm. subst b.
    iDestruct (is_pipe_valid with "Hpipe") as %Hpv.
    iPoseProof (is_pipe_openable with "Hpipe") as "#Hopen".
    iDestruct (proc_priv_sz_bound with "Hpriv") as %Hszb.
    (* ================================================================= *)
    (* EPI -- the common epilogue at +0x58.                              *)
    (* ================================================================= *)
    iAssert (pw_epi CID γf Φ γs j γp w q m av true C pid V n sp0) with "[Hcont]" as "EPI".
    { rewrite /pw_epi. iIntros (CIDep Hsep M P') "%Hbr %Hrw %Hext (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7) Hhi Hcg Hown Hpc Href Hpriv Hpark".
      destruct Hbr as (Hsp & B6 & B7 & B8 & B9 & B10 & B11).
      assert (Hb1 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = pa_stk sp0 1%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb2 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = pa_stk sp0 2%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb3 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = pa_stk sp0 3%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb4 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = pa_stk sp0 4%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb5 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 5%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb6 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 6%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb7 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 7%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      (* +0x58 c.mv a0,s2 *)
      iPoseProof (pwi_58 with "Htext") as "Hi58".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x58)) Ra0 Rs2 M (av - 14)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi58 [-]").
      iIntros (CIDp6 Hsp6) "Hcg Hpc". rgall.
      set (E1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs2))]> M).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs2))]> M) with E1.
      assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5a) in "Hpc".
      assert (HspE1 : E1 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
      (* +0x5a c.ldsp ra,104(sp) *)
      iPoseProof (pwi_5a with "Htext") as "Hi5a".
      iEval (rewrite -Hb1 -HspE1) in "Hc1".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x5a)) (mword_of_int 13 : mword 6) Rra
                E1 (av - 14)%nat (m !!! Regidx Rra) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi5a Hc1 [-]").
      iIntros (CIDp7 Hsp7) "Hcg Hpc Hc1". rgall.
      iEval (rewrite HspE1 Hb1) in "Hc1".
      set (E2 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E1).
      change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E1) with E2.
      assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5c) in "Hpc".
      assert (HspE2 : E2 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E2 upd_ne; [exact HspE1 | reg_neq]).
      (* +0x5c c.ldsp s0,96(sp) *)
      iPoseProof (pwi_5c with "Htext") as "Hi5c".
      iEval (rewrite -Hb2 -HspE2) in "Hc2".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x5c)) (mword_of_int 12 : mword 6) Rs0
                E2 (av - 14)%nat (m !!! Regidx Rs0) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi5c Hc2 [-]").
      iIntros (CIDp8 Hsp8) "Hcg Hpc Hc2". rgall.
      iEval (rewrite HspE2 Hb2) in "Hc2".
      set (E3 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E2).
      change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E2) with E3.
      assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5e) in "Hpc".
      assert (HspE3 : E3 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E3 upd_ne; [exact HspE2 | reg_neq]).
      (* +0x5e c.ldsp s1,88(sp) *)
      iPoseProof (pwi_5e with "Htext") as "Hi5e".
      iEval (rewrite -Hb3 -HspE3) in "Hc3".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x5e)) (mword_of_int 11 : mword 6) Rs1
                E3 (av - 14)%nat (m !!! Regidx Rs1) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi5e Hc3 [-]").
      iIntros (CIDp9 Hsp9) "Hcg Hpc Hc3". rgall.
      iEval (rewrite HspE3 Hb3) in "Hc3".
      set (E4 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> E3).
      change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> E3) with E4.
      assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp60) in "Hpc".
      assert (HspE4 : E4 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E4 upd_ne; [exact HspE3 | reg_neq]).
      (* +0x60 c.ldsp s2,80(sp) *)
      iPoseProof (pwi_60 with "Htext") as "Hi60".
      iEval (rewrite -Hb4 -HspE4) in "Hc4".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x60)) (mword_of_int 10 : mword 6) Rs2
                E4 (av - 14)%nat (m !!! Regidx Rs2) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi60 Hc4 [-]").
      iIntros (CIDp10 Hsp10) "Hcg Hpc Hc4". rgall.
      iEval (rewrite HspE4 Hb4) in "Hc4".
      set (E5 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> E4).
      change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> E4) with E5.
      assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp62) in "Hpc".
      assert (HspE5 : E5 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E5 upd_ne; [exact HspE4 | reg_neq]).
      (* +0x62 c.ldsp s3,72(sp) *)
      iPoseProof (pwi_62 with "Htext") as "Hi62".
      iEval (rewrite -Hb5 -HspE5) in "Hc5".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x62)) (mword_of_int 9 : mword 6) Rs3
                E5 (av - 14)%nat (m !!! Regidx Rs3) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi62 Hc5 [-]").
      iIntros (CIDp11 Hsp11) "Hcg Hpc Hc5". rgall.
      iEval (rewrite HspE5 Hb5) in "Hc5".
      set (E6 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> E5).
      change (<[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> E5) with E6.
      assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp64) in "Hpc".
      assert (HspE6 : E6 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E6 upd_ne; [exact HspE5 | reg_neq]).
      (* +0x64 c.ldsp s4,64(sp) *)
      iPoseProof (pwi_64 with "Htext") as "Hi64".
      iEval (rewrite -Hb6 -HspE6) in "Hc6".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x64)) (mword_of_int 8 : mword 6) Rs4
                E6 (av - 14)%nat (m !!! Regidx Rs4) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi64 Hc6 [-]").
      iIntros (CIDp12 Hsp12) "Hcg Hpc Hc6". rgall.
      iEval (rewrite HspE6 Hb6) in "Hc6".
      set (E7 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> E6).
      change (<[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> E6) with E7.
      assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp66) in "Hpc".
      assert (HspE7 : E7 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E7 upd_ne; [exact HspE6 | reg_neq]).
      (* +0x66 c.ldsp s5,56(sp) *)
      iPoseProof (pwi_66 with "Htext") as "Hi66".
      iEval (rewrite -Hb7 -HspE7) in "Hc7".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x66)) (mword_of_int 7 : mword 6) Rs5
                E7 (av - 14)%nat (m !!! Regidx Rs5) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi66 Hc7 [-]").
      iIntros (CIDp13 Hsp13) "Hcg Hpc Hc7". rgall.
      iEval (rewrite HspE7 Hb7) in "Hc7".
      set (E8 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> E7).
      change (<[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> E7) with E8.
      assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp68) in "Hpc".
      assert (HspE8 : E8 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E8 upd_ne; [exact HspE7 | reg_neq]).
      (* +0x68 c.addi16sp sp,112 -- the frame trade back *)
      iAssert (stack_own sp0 14%nat) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hhi]" as "Hframe".
      { iApply (stack_own_split_2 sp0 7%nat 14%nat ltac:(lia)). iSplitR "Hhi"; [| iExact "Hhi"].
        rewrite stack_own_slots. cbn [seq].
        iSplitL "Hc1". { iExists _. iExact "Hc1". }
        iSplitL "Hc2". { iExists _. iExact "Hc2". }
        iSplitL "Hc3". { iExists _. iExact "Hc3". }
        iSplitL "Hc4". { iExists _. iExact "Hc4". }
        iSplitL "Hc5". { iExists _. iExact "Hc5". }
        iSplitL "Hc6". { iExists _. iExact "Hc6". }
        iSplitL "Hc7". { iExists _. iExact "Hc7". }
        done. }
      assert (Hwv : add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))) = sp0)
        by (rewrite HspE8; apply pw_pop_val).
      assert (Hpop : E8 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6)))) 14%nat)
        by (rewrite Hwv HspE8; reflexivity).
      iEval (rewrite -Hwv) in "Hframe".
      iPoseProof (pwi_68 with "Htext") as "Hi68".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x68)) (mword_of_int 7 : mword 6)
                E8 (av - 14)%nat 14%nat true Hpop with "Hcg Hpc Hi68 Hframe [-]").
      iIntros (CIDp14 Hsp14) "Hcg Hpc". rgall.
      assert (Hnk : ((av - 14) + 14)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      set (E9 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))))]> E8).
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))))]> E8) with E9.
      assert (Hpp6a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp6a) in "Hpc".
      (* +0x6a c.ret *)
      assert (HraE9 : E9 !!! Regidx Rra = m !!! Regidx Rra).
      { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
      iPoseProof (pwi_6a with "Htext") as "Hi6a".
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x6a)) Rra E9 av true ltac:(nz)
                with "Hcg Hpc Hi6a [-]").
      iIntros (CIDp15 Hsp15) "Hcg Hpc". rgall.
      assert (Hrf : ret_pc (E9 !!! Regidx Rra) = ret_tgt) by (rewrite HraE9; reflexivity).
      iEval (rewrite Hrf) in "Hpc".
      (* the return value: a0 was written at +0x58 and never touched again *)
      assert (Ha0E9 : E9 !!! Regidx Ra0 = M !!! Regidx Rs2).
      { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_eq. unfold regval_into_reg. apply add_vec_zero_l. }
      (* callee_saved m E9 *)
      assert (HcsE9 : callee_saved m E9).
      { unfold callee_saved. split_and!.
        - rewrite /E9 upd_eq. unfold regval_into_reg. rewrite Hwv. reflexivity.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
          rewrite /E3 upd_eq. reflexivity.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. reflexivity.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_eq. reflexivity.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_eq. reflexivity.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_eq. reflexivity.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_eq. reflexivity.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
          rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
          rewrite /E1 upd_ne; [| reg_neq]. exact B6.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
          rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
          rewrite /E1 upd_ne; [| reg_neq]. exact B7.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
          rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
          rewrite /E1 upd_ne; [| reg_neq]. exact B8.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
          rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
          rewrite /E1 upd_ne; [| reg_neq]. exact B9.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
          rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
          rewrite /E1 upd_ne; [| reg_neq]. exact B10.
        - rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
          rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
          rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
          rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
          rewrite /E1 upd_ne; [| reg_neq]. exact B11. }
      iSpecialize ("Hcont" $! CIDp15 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! E9 P' with "[%] [%] [%] Hcg Hown Hpc Href Hpriv Hpark").
      - exact HcsE9.
      - exact Hext.
      - rewrite Ha0E9. exact Hrw. }
    (* ================================================================= *)
    (* EXITS -- the +0xd8 tail and the +0x46 (-1) arm, CONJOINED: exactly *)
    (* one of them is taken, so they must SHARE the epilogue closure.     *)
    (* ================================================================= *)
    iAssert (pw_exits CID γf Φ γs j γl γp w q m av true C pid V n sp0 pi) with "[EPI]" as "EXITS".
    { rewrite /pw_exits. iSplit.
      - (* ---------------- +0xd8: wakeup(&pi->nread); release ---------------- *)
        rewrite /pw_tail. iIntros (CIDtl Hstl).
        iIntros (M P') "%Hbr %Hs1M %Hrw %Hext HF7 Hhi Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Hpark".
        iPoseProof (pwi_d8 with "Htext") as "Hid8".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xd8)) Ra0 Rs1
                  (mword_of_int 536 : mword 12) M (av - 14)%nat false ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hid8 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (T1 := <[Regidx Ra0 := regval_into_reg
            (add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> M).
        change (<[Regidx Ra0 := regval_into_reg
            (add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> M) with T1.
        assert (Hppdc : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd8) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xdc)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppdc) in "Hpc".
        iPoseProof (pwi_dc with "Htext") as "Hidc".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xdc)) Rra (mword_of_int 2087374 : mword 21)
                  T1 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hidc [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (T2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xdc) : mword 64) 4)]> T1).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xdc) : mword 64) 4)]> T1) with T2.
        assert (Hjwk : add_vec (mword_of_int (KernelSyms.pipewrite + 0xdc) : mword 64) (sign_extend' 64 (mword_of_int 2087374 : mword 21))
                       = mword_of_int KernelSyms.wakeup) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjwk) in "Hpc".
        destruct Hbr as (Hsp & B6 & B7 & B8 & B9 & B10 & B11).
        (* every wakeup premise pre-established by NAME (optimization.md) *)
        assert (HwK : (18 <= av - 14)%nat) by lia.
        assert (HwdomW : forall r : regidx, r ∈ dom (rf_to_gmap T2)) by (intro r; apply rf_to_gmap_dom).
        assert (Hwa0f : mycpu_ret (rget T2 Rtp) = mycpu_ret cid_word) by (rewrite rget_tp; reflexivity).
        assert (Hwnz : eq_vec (zero_reg : mword 64) (mycpu_ret (rget T2 Rtp)) = false)
          by (rewrite rget_tp; apply mycpu_ret_nonzero; apply tp_ok_cid).
        assert (Hwlvl : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
        iApply (Wakeup.wp_wakeup_sconf Φ T2 γs (mycpu_ret cid_word) (proc_addr j) 1%nat (av - 14)%nat true C false
                  HwK HwdomW Hlen Hwa0f Hwnz Hwlvl
                  with "Hcg Hown Htext Hpc Hpanic Hpinv [-]").
        iApply wp_next_off_intro. iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hown Htext2 Hpc". rgall.
        assert (HraT2 : T2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xdc) : mword 64) 4)
          by (rewrite /T2; apply upd_eq).
        iEval (rewrite HraT2) in "Hpc".
        assert (Hppe0 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xdc) : mword 64) 4)
                        = (mword_of_int (KernelSyms.pipewrite + 0xe0) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppe0) in "Hpc".
        assert (HcsMT2 : callee_saved M T2).
        { rewrite /T2 /T1. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
        assert (HcsMMw : callee_saved M Mw) by (apply (callee_saved_trans M T2 Mw HcsMT2 Hwcs)).
        assert (Hs1Mw : Mw !!! Regidx Rs1 = pi).
        { rewrite (callee_saved_lookup HcsMMw (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1M. }
        (* +0xe0 c.mv a0,s1 *)
        iPoseProof (pwi_e0 with "Htext") as "Hie0".
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xe0)) Ra0 Rs1 Mw (av - 14)%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hie0 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (T3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw) with T3.
        assert (Hppe2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe0) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xe2)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppe2) in "Hpc".
        (* +0xe2 jal release *)
        iPoseProof (pwi_e2 with "Htext") as "Hie2".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xe2)) Rra (mword_of_int 2082556 : mword 21)
                  T3 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hie2 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (T4 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe2) : mword 64) 4)]> T3).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe2) : mword 64) 4)]> T3) with T4.
        assert (Hjrl : add_vec (mword_of_int (KernelSyms.pipewrite + 0xe2) : mword 64) (sign_extend' 64 (mword_of_int 2082556 : mword 21))
                       = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrl) in "Hpc".
        assert (Ha0T4 : T4 !!! Regidx Ra0 = pi).
        { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_eq. unfold regval_into_reg.
          rewrite Hs1Mw. apply add_vec_zero_l. }
        assert (HlkaT4 : add_vec (T4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
        { rewrite Ha0T4.
          replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero. }
        assert (HavR : (10 <= av - 14)%nat) by lia.
        iApply (ReleaseGen.wp_release_gen_sconf γl pi (pipe_res γp pi) (pipe_dead γl γp) emp%I
                  T4 0%nat true (proc_addr j) C (av - 14)%nat HlkaT4 HavR
                  ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                  with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay [-]").
        { iApply lock_finisher_close. }
        iIntros (CIDrr Hsrr mr) "_ Hcg Hpc %Hcsr Hown". rgall.
        assert (HraT4 : T4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe2) : mword 64) 4)
          by (rewrite /T4; apply upd_eq).
        iEval (rewrite HraT4) in "Hpc".
        assert (Hppe6 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe2) : mword 64) 4)
                        = (mword_of_int (KernelSyms.pipewrite + 0xe6) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppe6) in "Hpc".
        (* +0xe6 c.j -> the epilogue *)
        assert (HcsMwT4 : callee_saved Mw T4).
        { rewrite /T4 /T3. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
        assert (HcsMmr : callee_saved M mr).
        { apply (callee_saved_trans M Mw mr HcsMMw).
          apply (callee_saved_trans Mw T4 mr HcsMwT4 Hcsr). }
        iPoseProof (pwi_e6 with "Htext") as "Hie6".
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xe6))
                  (sign_extend' 21 (concat_vec (mword_of_int 1977 : mword 11) ('b"0")))
                  mr (av - 14)%nat true ltac:(vm_compute; reflexivity) with "Hcg Hpc Hie6 [-]").
        iIntros (CIDp16 Hsp16). iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
        assert (Hjep : add_vec (mword_of_int (KernelSyms.pipewrite + 0xe6) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1977 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.pipewrite + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjep) in "Hpc".
        rewrite /pw_epi.
        iSpecialize ("EPI" $! CIDp16 with "[%]"); [wp_next_chain|].
        iApply ("EPI" $! mr P' with "[%] [%] [%] HF7 Hhi Hcg Hown Hpc Href Hpriv Hpark").
        + apply (pw_base_regs_cs m M mr (pa_stk sp0 14%nat) HcsMmr).
          unfold pw_base_regs. split_and!; assumption.
        + rewrite (callee_saved_lookup HcsMmr (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact Hrw.
        + exact Hext.
      - (* ---------------- +0x46: release; i := -1; reload s6..s10 ---------------- *)
        rewrite /pw_minus1. iIntros (CIDmn Hsmn).
        iIntros (M P') "%Hmr %Hext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Hpark".
        destruct Hmr as (Hsp & Hs1M & Hs11M).
        iPoseProof (pwi_46 with "Htext") as "Hi46".
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x46)) Ra0 Rs1 M (av - 14)%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi46 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (Q1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M) with Q1.
        assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp48) in "Hpc".
        iPoseProof (pwi_48 with "Htext") as "Hi48".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x48)) Rra (mword_of_int 2082710 : mword 21)
                  Q1 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi48 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (Q2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) 4)]> Q1).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) 4)]> Q1) with Q2.
        assert (Hjrl : add_vec (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) (sign_extend' 64 (mword_of_int 2082710 : mword 21))
                       = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrl) in "Hpc".
        assert (Ha0Q2 : Q2 !!! Regidx Ra0 = pi).
        { rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_eq. unfold regval_into_reg.
          rewrite Hs1M. apply add_vec_zero_l. }
        assert (HlkaQ2 : add_vec (Q2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
        { rewrite Ha0Q2.
          replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero. }
        assert (HavR : (10 <= av - 14)%nat) by lia.
        iApply (ReleaseGen.wp_release_gen_sconf γl pi (pipe_res γp pi) (pipe_dead γl γp) emp%I
                  Q2 0%nat true (proc_addr j) C (av - 14)%nat HlkaQ2 HavR
                  ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                  with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay [-]").
        { iApply lock_finisher_close. }
        iIntros (CIDrr Hsrr mr) "_ Hcg Hpc %Hcsr Hown". rgall.
        assert (HraQ2 : Q2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) 4)
          by (rewrite /Q2; apply upd_eq).
        iEval (rewrite HraQ2) in "Hpc".
        assert (Hpp4c : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) 4)
                        = (mword_of_int (KernelSyms.pipewrite + 0x4c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp4c) in "Hpc".
        assert (HcsMQ2 : callee_saved M Q2).
        { rewrite /Q2 /Q1. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
        assert (HcsMmr : callee_saved M mr) by (apply (callee_saved_trans M Q2 mr HcsMQ2 Hcsr)).
        (* +0x4c c.li s2,-1 *)
        iPoseProof (pwi_4c with "Htext") as "Hi4c".
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x4c)) Rs2 (mword_of_int 63 : mword 6)
                  (mword_of_int (-1) : mword 64) mr (av - 14)%nat true ltac:(nz) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi4c [-]").
        iIntros (CIDp17 Hsp17) "Hcg Hpc". rgall.
        set (Q3 := <[Regidx Rs2 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr).
        change (<[Regidx Rs2 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr) with Q3.
        assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp4e) in "Hpc".
        assert (HspQ3 : Q3 !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
        { rewrite /Q3 upd_ne; [| reg_neq].
          rewrite (callee_saved_lookup HcsMmr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
        assert (Hs11Q3 : Q3 !!! Regidx Rs11 = m !!! Regidx Rs11).
        { rewrite /Q3 upd_ne; [| reg_neq].
          rewrite (callee_saved_lookup HcsMmr (mword_of_int 27) ltac:(vm_compute; reflexivity)). exact Hs11M. }
        assert (Hs2Q3 : Q3 !!! Regidx Rs2 = (mword_of_int (-1) : mword 64))
          by (rewrite /Q3 upd_eq; reflexivity).
        (* +0x4e .. +0x56 reload s6..s10, falling into the epilogue *)
        iPoseProof (pwi_4e with "Htext") as "Hj0".
        iPoseProof (pwi_50 with "Htext") as "Hj1".
        iPoseProof (pwi_52 with "Htext") as "Hj2".
        iPoseProof (pwi_54 with "Htext") as "Hj3".
        iPoseProof (pwi_56 with "Htext") as "Hj4".
        assert (E50 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E52 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E54 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E56 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E58 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
        iApply (pw_restore5 (proc_addr j) true (mword_of_int (KernelSyms.pipewrite + 0x4e)) (mword_of_int (KernelSyms.pipewrite + 0x50))
                  (mword_of_int (KernelSyms.pipewrite + 0x52)) (mword_of_int (KernelSyms.pipewrite + 0x54)) (mword_of_int (KernelSyms.pipewrite + 0x56))
                  (mword_of_int (KernelSyms.pipewrite + 0x58)) Q3 m (av - 14)%nat sp0
                  HspQ3 E50 E52 E54 E56 E58
                  with "Hcg Hpc Hj0 Hj1 Hj2 Hj3 Hj4 HF5 [-]").
        iIntros (CIDrs Hsrs M') "%Hrst Hcg Hpc HF5".
        destruct Hrst as (R6 & R7 & R8 & R9 & R10 & Rrest).
        assert (Hsp' : M' !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
        { rewrite (Rrest csp_rs1 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact HspQ3. }
        assert (Hs11' : M' !!! Regidx Rs11 = m !!! Regidx Rs11).
        { rewrite (Rrest (mword_of_int 27) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Hs11Q3. }
        assert (Hs2' : M' !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)).
        { rewrite (Rrest (mword_of_int 18) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Hs2Q3. }
        rewrite /pw_epi.
        iSpecialize ("EPI" $! CIDrs with "[%]"); [wp_next_chain|].
        iApply ("EPI" $! M' P' with "[%] [%] [%] HF7 [HF5 HCH] Hcg Hown Hpc Href Hpriv Hpark").
        + unfold pw_base_regs. split_and!; assumption.
        + rewrite Hs2'. by left.
        + exact Hext.
        + iApply (pw_stack7_of m sp0 with "HF5 HCH"). }
    (* ================================================================= *)
    (* PROLOGUE +0x00 .. +0x16: 14-slot frame, save ra/s0..s5, set s0/s1/s4/s5 *)
    (* ================================================================= *)
    iPoseProof (pwi_00 with "Htext") as "Hi00".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 14%nat) by (apply pw_push_val).
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 57 : mword 6) m av 14%nat true ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CIDp18 Hsp18) "Hcg Hframe Hpc". rgall.
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))))]> m) with A0.
    assert (HspA0 : A0 !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
    { rewrite /A0 upd_eq. unfold regval_into_reg. rewrite Hpush Hspm. reflexivity. }
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* the seven low slots become the seven prologue cells *)
    iAssert (stack_own sp0 7%nat ∗ stack_own (pa_stk sp0 7%nat) 7%nat)%I with "[Hframe]" as "[Hlo Hhi]".
    { iApply (stack_own_split_1 sp0 7%nat 14%nat ltac:(lia)). iExact "Hframe". }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hlo".
    iDestruct "Hlo" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    iDestruct "S3" as (v3) "Hc3". iDestruct "S4" as (v4) "Hc4".
    iDestruct "S5" as (v5) "Hc5". iDestruct "S6" as (v6) "Hc6".
    iDestruct "S7" as (v7) "Hc7".
    assert (Hb1 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = pa_stk sp0 1%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb2 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = pa_stk sp0 2%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb3 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = pa_stk sp0 3%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb4 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = pa_stk sp0 4%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb5 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 5%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb6 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 6%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (Hb7 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 7%nat)
      by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
    assert (HraA0 : A0 !!! Regidx Rra = m !!! Regidx Rra) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs0A0 : A0 !!! Regidx Rs0 = m !!! Regidx Rs0) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs1A0 : A0 !!! Regidx Rs1 = m !!! Regidx Rs1) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs2A0 : A0 !!! Regidx Rs2 = m !!! Regidx Rs2) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs3A0 : A0 !!! Regidx Rs3 = m !!! Regidx Rs3) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs4A0 : A0 !!! Regidx Rs4 = m !!! Regidx Rs4) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs5A0 : A0 !!! Regidx Rs5 = m !!! Regidx Rs5) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    (* +0x02 c.sdsp ra,104(sp) *)
    iPoseProof (pwi_02 with "Htext") as "Hi02".
    iEval (rewrite -Hb1 -HspA0) in "Hc1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x02)) (mword_of_int 13 : mword 6) Rra
              A0 (av - 14)%nat v1 true with "Hcg Hpc Hi02 Hc1 [-]").
    iIntros (CIDp19 Hsp19) "Hcg Hpc Hc1". rgall.
    iEval (rewrite HspA0 Hb1 HraA0) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,96(sp) *)
    iPoseProof (pwi_04 with "Htext") as "Hi04".
    iEval (rewrite -Hb2 -HspA0) in "Hc2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x04)) (mword_of_int 12 : mword 6) Rs0
              A0 (av - 14)%nat v2 true with "Hcg Hpc Hi04 Hc2 [-]").
    iIntros (CIDp20 Hsp20) "Hcg Hpc Hc2". rgall.
    iEval (rewrite HspA0 Hb2 Hs0A0) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,88(sp) *)
    iPoseProof (pwi_06 with "Htext") as "Hi06".
    iEval (rewrite -Hb3 -HspA0) in "Hc3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x06)) (mword_of_int 11 : mword 6) Rs1
              A0 (av - 14)%nat v3 true with "Hcg Hpc Hi06 Hc3 [-]").
    iIntros (CIDp21 Hsp21) "Hcg Hpc Hc3". rgall.
    iEval (rewrite HspA0 Hb3 Hs1A0) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,80(sp) *)
    iPoseProof (pwi_08 with "Htext") as "Hi08".
    iEval (rewrite -Hb4 -HspA0) in "Hc4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x08)) (mword_of_int 10 : mword 6) Rs2
              A0 (av - 14)%nat v4 true with "Hcg Hpc Hi08 Hc4 [-]").
    iIntros (CIDp22 Hsp22) "Hcg Hpc Hc4". rgall.
    iEval (rewrite HspA0 Hb4 Hs2A0) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,72(sp) *)
    iPoseProof (pwi_0a with "Htext") as "Hi0a".
    iEval (rewrite -Hb5 -HspA0) in "Hc5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x0a)) (mword_of_int 9 : mword 6) Rs3
              A0 (av - 14)%nat v5 true with "Hcg Hpc Hi0a Hc5 [-]").
    iIntros (CIDp23 Hsp23) "Hcg Hpc Hc5". rgall.
    iEval (rewrite HspA0 Hb5 Hs3A0) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp s4,64(sp) *)
    iPoseProof (pwi_0c with "Htext") as "Hi0c".
    iEval (rewrite -Hb6 -HspA0) in "Hc6".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x0c)) (mword_of_int 8 : mword 6) Rs4
              A0 (av - 14)%nat v6 true with "Hcg Hpc Hi0c Hc6 [-]").
    iIntros (CIDp24 Hsp24) "Hcg Hpc Hc6". rgall.
    iEval (rewrite HspA0 Hb6 Hs4A0) in "Hc6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp s5,56(sp) *)
    iPoseProof (pwi_0e with "Htext") as "Hi0e".
    iEval (rewrite -Hb7 -HspA0) in "Hc7".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x0e)) (mword_of_int 7 : mword 6) Rs5
              A0 (av - 14)%nat v7 true with "Hcg Hpc Hi0e Hc7 [-]").
    iIntros (CIDp25 Hsp25) "Hcg Hpc Hc7". rgall.
    iEval (rewrite HspA0 Hb7 Hs5A0) in "Hc7".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iAssert (pw_frame7 m sp0) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7]" as "HF7".
    { rewrite /pw_frame7. iFrame "Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7". }
    (* +0x10 c.addi4spn s0,sp,112 *)
    iPoseProof (pwi_10 with "Htext") as "Hi10".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x10)) (Cregidx (mword_of_int 0))
              (mword_of_int 28 : mword 8) Rs0 A0 (av - 14)%nat true
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10 [-]").
    iIntros (CIDp26 Hsp26) "Hcg Hpc". rgall.
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))))]> A0) with A1.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.mv s1,a0 *)
    iPoseProof (pwi_12 with "Htext") as "Hi12".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x12)) Rs1 Ra0 A1 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi12 [-]").
    iIntros (CIDp27 Hsp27) "Hcg Hpc". rgall.
    set (A2 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1) with A2.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv s5,a1 *)
    iPoseProof (pwi_14 with "Htext") as "Hi14".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x14)) Rs5 Ra1 A2 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14 [-]").
    iIntros (CIDp28 Hsp28) "Hcg Hpc". rgall.
    set (A3 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2).
    change (<[Regidx Rs5 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2) with A3.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv s4,a2 *)
    iPoseProof (pwi_16 with "Htext") as "Hi16".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x16)) Rs4 Ra2 A3 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi16 [-]").
    iIntros (CIDp29 Hsp29) "Hcg Hpc". rgall.
    set (A4 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (A3 !!! Regidx Ra2))]> A3).
    change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (A3 !!! Regidx Ra2))]> A3) with A4.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 jal myproc *)
    iPoseProof (pwi_18 with "Htext") as "Hi18".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x18)) Rra (mword_of_int 2085948 : mword 21)
              A4 (av - 14)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CIDp30 Hsp30) "Hcg Hpc". rgall.
    set (A5 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x18) : mword 64) 4)]> A4).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x18) : mword 64) 4)]> A4) with A5.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.pipewrite + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2085948 : mword 21))
                   = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    (* the register facts A5 carries into myproc *)
    pose (addr := (m !!! Regidx Ra1 : mword 64)).
    assert (HspA5 : A5 !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. exact HspA0. }
    assert (Hs0A5 : A5 !!! Regidx Rs0 = sp0).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_eq. unfold regval_into_reg. rewrite HspA0. apply pw_s0_val. }
    assert (Hs1A5 : A5 !!! Regidx Rs1 = pi).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_eq. unfold regval_into_reg.
      rewrite (_ : A1 !!! Regidx Ra0 = pi); [apply add_vec_zero_l|].
      rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    assert (Hs5A5 : A5 !!! Regidx Rs5 = addr).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_eq. unfold regval_into_reg.
      rewrite (_ : A2 !!! Regidx Ra1 = addr); [apply add_vec_zero_l|].
      rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    assert (Hs4A5 : A5 !!! Regidx Rs4 = (mword_of_int n : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_eq. unfold regval_into_reg.
      rewrite (_ : A3 !!! Regidx Ra2 = (mword_of_int n : mword 64)); [apply add_vec_zero_l|].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [exact Ha2 | reg_neq]. }
    assert (HthrA5 : forall r : mword 5, r <> mword_of_int 1 -> r <> csp_rs1 -> r <> mword_of_int 8 ->
              r <> mword_of_int 9 -> r <> mword_of_int 20 -> r <> mword_of_int 21 ->
              A5 !!! Regidx r = m !!! Regidx r).
    { intros r N1 N2 N8 N9 N20 N21.
      rewrite /A5 upd_ne; [| congruence]. rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence]. rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence]. rewrite /A0 upd_ne; [reflexivity | congruence]. }
    assert (HraA5 : A5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x18) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (Hlvl0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
    assert (Hav10 : (10 <= av - 14)%nat) by lia.
    iDestruct (cpu_own_transport CID CIDp30 0 true pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Myproc.wp_myproc_sconf A5 (av - 14)%nat 0%nat true pj C true
              Hlvl0 Hav10 with "Hcg Hown Htext Hpc [-]").
    iIntros (CIDmp Hsmp ms M0) "%Hms Hcg Hown Hpc %HcsM0". rgall.
    destruct HcsM0 as [HcsM0 Ha0M0].
    assert (Hpp1c : ret_pc (A5 !!! Regidx Rra) = (mword_of_int (KernelSyms.pipewrite + 0x1c) : mword 64))
      by (rewrite HraA5; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.mv s3,a0 *)
    iPoseProof (pwi_1c with "Htext") as "Hi1c".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x1c)) Rs3 Ra0 M0 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1c [-]").
    iIntros (CIDp31 Hsp31) "Hcg Hpc". rgall.
    set (B1 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (M0 !!! Regidx Ra0))]> M0).
    change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (M0 !!! Regidx Ra0))]> M0) with B1.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.mv a0,s1 *)
    assert (Hs1M0 : M0 !!! Regidx Rs1 = pi).
    { rewrite (callee_saved_lookup HcsM0 (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1A5. }
    iPoseProof (pwi_1e with "Htext") as "Hi1e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x1e)) Ra0 Rs1 B1 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1e [-]").
    iIntros (CIDp32 Hsp32) "Hcg Hpc". rgall.
    set (B2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Rs1))]> B1).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Rs1))]> B1) with B2.
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 jal acquire *)
    iPoseProof (pwi_20 with "Htext") as "Hi20".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x20)) Rra (mword_of_int 2082614 : mword 21)
              B2 (av - 14)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CIDp33 Hsp33) "Hcg Hpc". rgall.
    set (B3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) 4)]> B2).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) 4)]> B2) with B3.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) (sign_extend' 64 (mword_of_int 2082614 : mword 21))
                   = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    assert (Ha0B3 : B3 !!! Regidx Ra0 = pi).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_eq. unfold regval_into_reg.
      rewrite (_ : B1 !!! Regidx Rs1 = pi); [apply add_vec_zero_l|].
      rewrite /B1 upd_ne; [exact Hs1M0 | reg_neq]. }
    assert (HraB3 : B3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) 4)
      by (rewrite /B3; apply upd_eq).
    (* the facts B3 parks across acquire.  NOTE [callee_saved M0 B3] is FALSE:
       +0x1c writes s3, which IS callee-saved -- so the threading fact is
       stated register-wise instead. *)
    assert (HthrB3 : forall r : mword 5, r <> mword_of_int 1 -> r <> mword_of_int 10 ->
              r <> mword_of_int 19 -> B3 !!! Regidx r = M0 !!! Regidx r).
    { intros r N1 N10 N19.
      rewrite /B3 upd_ne; [| congruence]. rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [reflexivity | congruence]. }
    assert (Hs3B3 : B3 !!! Regidx Rs3 = pj).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
      rewrite /B1 upd_eq. unfold regval_into_reg. rewrite Ha0M0. apply add_vec_zero_l. }
    iDestruct (cpu_own_transport CIDmp CIDp33 0 true pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (AcquireGen.wp_acquire_gen_sconf γl (pipe_res γp pi) (pipe_ref γp w q)
              (pipe_dead γl γp) B3 0%nat true pj C (av - 14)%nat true Hlvl0 Hav10
              ltac:(iApply pipe_ref_dead) ltac:(intros ?i; iApply locked_pre_dead)
              with "Hcg Hown Htext Hpc [] Href Hpanic [-]").
    { rgall. iEval (rewrite Ha0B3). iExact "Hopen". }
    iIntros (CIDaq Hsaq ms2 M1) "%Hms2 Href Hcg Hpc %HcsM1 Hlocked Hres Hown Hpay". rgall.
    iEval (rewrite HraB3) in "Hpc".
    assert (Hpp24 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) 4)
                    = (mword_of_int (KernelSyms.pipewrite + 0x24) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* the whole register state at the +0x24 test *)
    assert (HthrM1 : forall r : mword 5, is_cs_idx r = true -> r <> mword_of_int 19 ->
              M1 !!! Regidx r = A5 !!! Regidx r).
    { intros r Hcs N19.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      rewrite (callee_saved_lookup HcsM1 r Hcs).
      rewrite (HthrB3 r N1 N10 N19).
      rewrite (callee_saved_lookup HcsM0 r Hcs). reflexivity. }
    assert (HspM1 : M1 !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
    { rewrite (HthrM1 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact HspA5. }
    assert (Hs0M1 : M1 !!! Regidx Rs0 = sp0).
    { rewrite (HthrM1 (mword_of_int 8) ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs0A5. }
    assert (Hs1M1 : M1 !!! Regidx Rs1 = pi).
    { rewrite (HthrM1 (mword_of_int 9) ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs1A5. }
    assert (Hs4M1 : M1 !!! Regidx Rs4 = (mword_of_int n : mword 64)).
    { rewrite (HthrM1 (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs4A5. }
    assert (Hs5M1 : M1 !!! Regidx Rs5 = addr).
    { rewrite (HthrM1 (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs5A5. }
    assert (Hs3M1 : M1 !!! Regidx Rs3 = pj).
    { rewrite (callee_saved_lookup HcsM1 (mword_of_int 19) ltac:(vm_compute; reflexivity)). exact Hs3B3. }
    assert (HthrM1m : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> mword_of_int 8 ->
              r <> mword_of_int 9 -> r <> mword_of_int 20 -> r <> mword_of_int 21 ->
              r <> mword_of_int 19 -> M1 !!! Regidx r = m !!! Regidx r).
    { intros r Hcs N2 N8 N9 N20 N21 N19.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      rewrite (HthrM1 r Hcs N19). apply HthrA5; assumption. }
    assert (Hs6M1 : M1 !!! Regidx Rs6 = m !!! Regidx Rs6)
      by (apply HthrM1m; [vm_compute; reflexivity | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]).
    assert (Hs7M1 : M1 !!! Regidx Rs7 = m !!! Regidx Rs7)
      by (apply HthrM1m; [vm_compute; reflexivity | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]).
    assert (Hs8M1 : M1 !!! Regidx Rs8 = m !!! Regidx Rs8)
      by (apply HthrM1m; [vm_compute; reflexivity | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]).
    assert (Hs9M1 : M1 !!! Regidx Rs9 = m !!! Regidx Rs9)
      by (apply HthrM1m; [vm_compute; reflexivity | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]).
    assert (Hs10M1 : M1 !!! Regidx Rs10 = m !!! Regidx Rs10)
      by (apply HthrM1m; [vm_compute; reflexivity | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]).
    assert (Hs11M1 : M1 !!! Regidx Rs11 = m !!! Regidx Rs11)
      by (apply HthrM1m; [vm_compute; reflexivity | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq]).
    assert (HbaseM1 : pw_base_regs m M1 (pa_stk sp0 14%nat))
      by (unfold pw_base_regs; split_and!; assumption).
    (* ================================================================= *)
    (* +0x24  blez s4  --  the [n <= 0] test                              *)
    (* ================================================================= *)
    assert (Hrn : (- 2 ^ 63 <= n < 2 ^ 63)%Z) by (rewrite H63; rewrite H31 in Hnrange; lia).
    assert (Hcmp0 : zopz0zKzJ_s (zero_reg : mword 64) (M1 !!! Regidx Rs4) = Z.geb 0 n)
      by (rewrite Hs4M1; apply pw_geb_s0; exact Hrn).
    iPoseProof (pwi_24 with "Htext") as "Hi24".
    destruct (Z.geb 0 n) eqn:Hb0.
    - (* ======= n <= 0: i := 0 and go straight to the +0xd8 tail ======= *)
      assert (Hn0 : (n <= 0)%Z).
      { assert (Hx := Hb0). rewrite Z.geb_leb in Hx. by apply Z.leb_le. }
      assert (Hgt0 : zopz0zKzJ_s (zero_reg : mword 64) (M1 !!! Regidx Rs4) = true) by exact Hcmp0.
      assert (Hal0 : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 196 : mword 13))) 0) ('b"0") = true)
        by (vm_compute; reflexivity).
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x24)) (mword_of_int 196 : mword 13)
                Rs4 M1 (av - 14)%nat false ltac:(nz) Hgt0 Hal0 with "Hcg Hpc Hi24 [-]").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hje8 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 196 : mword 13))
                     = mword_of_int (KernelSyms.pipewrite + 0xe8)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hje8) in "Hpc".
      (* +0xe8 c.li s2,0 *)
      iPoseProof (pwi_e8 with "Htext") as "Hie8".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xe8)) Rs2 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) M1 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hie8 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (Z1 := <[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1).
      change (<[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1) with Z1.
      assert (Hppea : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe8) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xea)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppea) in "Hpc".
      (* +0xea c.j -> the tail *)
      iPoseProof (pwi_ea with "Htext") as "Hiea".
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xea))
                (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")))
                Z1 (av - 14)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiea [-]").
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjd8 : add_vec (mword_of_int (KernelSyms.pipewrite + 0xea) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.pipewrite + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjd8) in "Hpc".
      iDestruct "EXITS" as "[TAIL _]".
      rewrite /pw_tail.
      iSpecialize ("TAIL" $! CIDaq with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! Z1 (pv_upt V) with "[%] [%] [%] [%] HF7 Hhi Hcg Hown Hpay Hlocked Hres Hpc Href [Hpriv] Hpark").
      + (* [callee_saved M1 Z1] is false (s2 is callee-saved), so peel directly *)
        unfold pw_base_regs. split_and!.
        { rewrite /Z1 upd_ne; [exact HspM1 | reg_neq]. }
        { rewrite /Z1 upd_ne; [exact Hs6M1 | reg_neq]. }
        { rewrite /Z1 upd_ne; [exact Hs7M1 | reg_neq]. }
        { rewrite /Z1 upd_ne; [exact Hs8M1 | reg_neq]. }
        { rewrite /Z1 upd_ne; [exact Hs9M1 | reg_neq]. }
        { rewrite /Z1 upd_ne; [exact Hs10M1 | reg_neq]. }
        { rewrite /Z1 upd_ne; [exact Hs11M1 | reg_neq]. }
      + rewrite /Z1 upd_ne; [exact Hs1M1 | reg_neq].
      + rewrite /Z1 upd_eq. right. exists 0%Z. split; [reflexivity | lia].
      + apply uptd_ext_refl.
      + rewrite pw_upd_upt_id. iExact "Hpriv".
    - (* ======= n > 0: save s6..s10, set up the loop registers ======= *)
      assert (Hn0 : (0 < n)%Z).
      { assert (Hx := Hb0). rewrite Z.geb_leb in Hx. by apply Z.leb_gt. }
      assert (Hgf0 : zopz0zKzJ_s (zero_reg : mword 64) (M1 !!! Regidx Rs4) = false) by exact Hcmp0.
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x24)) (mword_of_int 196 : mword 13)
                Rs4 M1 (av - 14)%nat false ltac:(nz) Hgf0 with "Hcg Hpc Hi24 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* carve slots 8..14: five spill cells, the [ch] slot and the dead slot *)
      iDestruct (pw_hi_split sp0 with "Hhi") as "[Hcells HCH]".
      iDestruct "Hcells" as (u8 u9 u10 u11 u12) "(G8 & G9 & G10 & G11 & G12)".
      assert (Hb8 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 8%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb9 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 9%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb10 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 10%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb11 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 11%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      assert (Hb12 : add_vec (pa_stk sp0 14%nat) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 12%nat)
        by (apply pw_slot_bridge; apply bv_eq; vm_compute; reflexivity).
      (* +0x28 .. +0x30  spill s6..s10 *)
      iPoseProof (pwi_28 with "Htext") as "Hi28".
      iEval (rewrite -Hb8 -HspM1) in "G8".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x28)) (mword_of_int 6 : mword 6) Rs6
                M1 (av - 14)%nat u8 false with "Hcg Hpc Hi28 G8 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc G8". rgall.
      iEval (rewrite HspM1 Hb8 Hs6M1) in "G8".
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iPoseProof (pwi_2a with "Htext") as "Hi2a".
      iEval (rewrite -Hb9 -HspM1) in "G9".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x2a)) (mword_of_int 5 : mword 6) Rs7
                M1 (av - 14)%nat u9 false with "Hcg Hpc Hi2a G9 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc G9". rgall.
      iEval (rewrite HspM1 Hb9 Hs7M1) in "G9".
      assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      iPoseProof (pwi_2c with "Htext") as "Hi2c".
      iEval (rewrite -Hb10 -HspM1) in "G10".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x2c)) (mword_of_int 4 : mword 6) Rs8
                M1 (av - 14)%nat u10 false with "Hcg Hpc Hi2c G10 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc G10". rgall.
      iEval (rewrite HspM1 Hb10 Hs8M1) in "G10".
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      iPoseProof (pwi_2e with "Htext") as "Hi2e".
      iEval (rewrite -Hb11 -HspM1) in "G11".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x2e)) (mword_of_int 3 : mword 6) Rs9
                M1 (av - 14)%nat u11 false with "Hcg Hpc Hi2e G11 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc G11". rgall.
      iEval (rewrite HspM1 Hb11 Hs9M1) in "G11".
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      iPoseProof (pwi_30 with "Htext") as "Hi30".
      iEval (rewrite -Hb12 -HspM1) in "G12".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x30)) (mword_of_int 2 : mword 6) Rs10
                M1 (av - 14)%nat u12 false with "Hcg Hpc Hi30 G12 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc G12". rgall.
      iEval (rewrite HspM1 Hb12 Hs10M1) in "G12".
      assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      iAssert (pw_frame5 m sp0) with "[G8 G9 G10 G11 G12]" as "HF5".
      { rewrite /pw_frame5. iFrame "G8 G9 G10 G11 G12". }
      (* +0x32 c.li s2,0 *)
      iPoseProof (pwi_32 with "Htext") as "Hi32".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x32)) Rs2 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) M1 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi32 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (C1 := <[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1).
      change (<[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1) with C1.
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      (* +0x34 addi s8,s0,-97 *)
      iPoseProof (pwi_34 with "Htext") as "Hi34".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x34)) Rs8 Rs0
                (mword_of_int 3999 : mword 12) C1 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi34 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (C2 := <[Regidx Rs8 := regval_into_reg
          (add_vec (C1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3999 : mword 12)))]> C1).
      change (<[Regidx Rs8 := regval_into_reg
          (add_vec (C1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3999 : mword 12)))]> C1) with C2.
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.li s7,1 *)
      iPoseProof (pwi_38 with "Htext") as "Hi38".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x38)) Rs7 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) C2 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi38 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (C3 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> C2).
      change (<[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> C2) with C3.
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.li s6,-1 *)
      iPoseProof (pwi_3a with "Htext") as "Hi3a".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x3a)) Rs6 (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) C3 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi3a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (C4 := <[Regidx Rs6 := regval_into_reg (mword_of_int (-1) : mword 64)]> C3).
      change (<[Regidx Rs6 := regval_into_reg (mword_of_int (-1) : mword 64)]> C3) with C4.
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c addi s10,s1,536 *)
      iPoseProof (pwi_3c with "Htext") as "Hi3c".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x3c)) Rs10 Rs1
                (mword_of_int 536 : mword 12) C4 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi3c [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (C5 := <[Regidx Rs10 := regval_into_reg
          (add_vec (C4 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> C4).
      change (<[Regidx Rs10 := regval_into_reg
          (add_vec (C4 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> C4) with C5.
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* +0x40 addi s9,s1,540 *)
      iPoseProof (pwi_40 with "Htext") as "Hi40".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x40)) Rs9 Rs1
                (mword_of_int 540 : mword 12) C5 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi40 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (C6 := <[Regidx Rs9 := regval_into_reg
          (add_vec (C5 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)))]> C5).
      change (<[Regidx Rs9 := regval_into_reg
          (add_vec (C5 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)))]> C5) with C6.
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* the loop-entry register invariant *)
      assert (Hs1C4 : C4 !!! Regidx Rs1 = pi).
      { rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
        rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [exact Hs1M1 | reg_neq]. }
      assert (Hs1C5 : C5 !!! Regidx Rs1 = pi) by (rewrite /C5 upd_ne; [exact Hs1C4 | reg_neq]).
      assert (Hs0C1 : C1 !!! Regidx Rs0 = sp0) by (rewrite /C1 upd_ne; [exact Hs0M1 | reg_neq]).
      assert (HregsC6 : pw_loop_regs m C6 (pa_stk sp0 14%nat) sp0 pi pj addr n 0%Z).
      { unfold pw_loop_regs. split_and!.
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [exact HspM1 | reg_neq]. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. exact Hs0C1. }
        { rewrite /C6 upd_ne; [| reg_neq]. exact Hs1C5. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_eq. reflexivity. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [exact Hs3M1 | reg_neq]. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [exact Hs4M1 | reg_neq]. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [exact Hs5M1 | reg_neq]. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_eq. reflexivity. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_eq. reflexivity. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_eq. unfold regval_into_reg. rewrite Hs0C1. apply pw_ch_addr. }
        { rewrite /C6 upd_eq. unfold regval_into_reg. rewrite Hs1C5. reflexivity. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_eq. unfold regval_into_reg.
          rewrite Hs1C4. reflexivity. }
        { rewrite /C6 upd_ne; [| reg_neq]. rewrite /C5 upd_ne; [| reg_neq].
          rewrite /C4 upd_ne; [| reg_neq]. rewrite /C3 upd_ne; [| reg_neq].
          rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [exact Hs11M1 | reg_neq]. } }
      (* ================================================================= *)
      (* THE LOOP (iLöb at the body, +0x7e)                                 *)
      (* ================================================================= *)
      iAssert (pw_loop CID γa γf Φ γs j γl γp w q m av true C pid V n sp0 pi addr) with "[]" as "LOOP".
      { iLöb as "IH". rewrite /pw_loop.
        iIntros (CIDlp Hslp i M Pc) "%Hi %Hext %Hregs HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv _ Hpark HEX".
        pose proof Hregs as Hregs2.
        destruct Hregs2 as (Hsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 &
                            Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
        assert (Hi1 : (i + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
        iDestruct "Hres" as (nr nw ro wo vname bs)
          "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hcnt & %Hbslen & Hdat & Hslack)".
        (* ---- +0x7e  lw a5,544(s1)  : readopen ---- *)
        assert (Hroaddr : add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 544 : mword 12)) = a_popen pi false)
          by (rewrite Hs1; reflexivity).
        iPoseProof (pwi_7e with "Htext") as "Hi7e".
        iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x7e)) Ra5 Rs1 (mword_of_int 544 : mword 12)
                  M (av - 14)%nat ro false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7e [Hro] [-]").
        { rgall. iEval (rewrite Hroaddr). iExact "Hro". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hro". rgall.
        iEval (rewrite Hroaddr) in "Hro".
        set (L1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ro)]> M).
        change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 ro)]> M) with L1.
        assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp82) in "Hpc".
        assert (Ha5L1 : L1 !!! Regidx Ra5 = sign_extend' 64 ro) by (rewrite /L1; apply upd_eq).
        assert (HcsML1 : callee_saved M L1)
          by (rewrite /L1; apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]).
        iPoseProof (pwi_82 with "Htext") as "Hi82".
        destruct (eq_vec (sign_extend' 64 ro) (zero_reg : mword 64)) eqn:Hroz.
        - (* ==== readopen == 0 : the -1 arm ==== *)
          assert (Hcz : eq_vec (L1 !!! Regidx Ra5) (zero_reg : mword 64) = true)
            by (rewrite Ha5L1; exact Hroz).
          assert (Halz : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x82) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 226 : mword 8) ('b"0"))))) 0) ('b"0") = true)
            by (vm_compute; reflexivity).
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x82)) (mword_of_int 226 : mword 8)
                    (Cregidx (mword_of_int 7)) Ra5 L1 (av - 14)%nat false
                    ltac:(vm_compute; reflexivity) ltac:(nz) Hcz Halz with "Hcg Hpc Hi82 [-]").
          iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          assert (Hj46 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x82) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 226 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.pipewrite + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hj46) in "Hpc".
          iDestruct "HEX" as "[_ MIN]". rewrite /pw_minus1.
          iSpecialize ("MIN" $! CIDlp with "[%]"); [wp_next_chain|].
          iApply ("MIN" $! L1 Pc with "[%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked [Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack] Hpc Href Hpriv Hpark").
          + unfold pw_min_regs. split_and!.
            { rewrite (callee_saved_lookup HcsML1 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
            { rewrite (callee_saved_lookup HcsML1 (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1. }
            { rewrite (callee_saved_lookup HcsML1 (mword_of_int 27) ltac:(vm_compute; reflexivity)). exact Hs11. }
          + exact Hext.
          + iApply (pw_res_intro γp pi nr nw ro wo vname bs Hcnt Hbslen
                      with "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack").
        - (* ==== readopen /= 0 : ask killed() ==== *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x82)) (mword_of_int 226 : mword 8)
                    (Cregidx (mword_of_int 7)) Ra5 L1 (av - 14)%nat false
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgall; rewrite Ha5L1; exact Hroz) with "Hcg Hpc Hi82 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp84) in "Hpc".
          (* +0x84 c.mv a0,s3 *)
          iPoseProof (pwi_84 with "Htext") as "Hi84".
          iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x84)) Ra0 Rs3 L1 (av - 14)%nat false
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          set (L2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs3))]> L1).
          change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs3))]> L1) with L2.
          assert (Hpp86 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x84) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp86) in "Hpc".
          (* +0x86 jal killed *)
          iPoseProof (pwi_86 with "Htext") as "Hi86".
          iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x86)) Rra (mword_of_int 2087956 : mword 21)
                    L2 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi86 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          set (L3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x86) : mword 64) 4)]> L2).
          change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x86) : mword 64) 4)]> L2) with L3.
          assert (Hjkl : add_vec (mword_of_int (KernelSyms.pipewrite + 0x86) : mword 64) (sign_extend' 64 (mword_of_int 2087956 : mword 21))
                         = mword_of_int KernelSyms.killed) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjkl) in "Hpc".
          assert (Hs3L1 : L1 !!! Regidx Rs3 = proc_addr j)
            by (rewrite /L1 upd_ne; [exact Hs3 | reg_neq]).
          assert (Ha0L3 : L3 !!! Regidx Ra0 = proc_addr j).
          { rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_eq. unfold regval_into_reg.
            rewrite Hs3L1. apply add_vec_zero_l. }
          assert (Hlvl1 : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
          assert (Hav14 : (14 <= av - 14)%nat) by lia.
          iApply (Killed.wp_killed_sconf Φ γs j γlp L3 (av - 14)%nat 1%nat true (proc_addr j) C false
                    Ha0L3 Hj Hjlp Hlvl1 Hav14
                    with "Hcg Hown Htext Hpc Hpinv Hpanic [-]").
          iApply wp_next_off_intro. iIntros (K0 kl) "%Hkfacts Hcg Hown Hpc". rgall.
          destruct Hkfacts as [Hkcs Hka0].
          assert (HraL3 : L3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x86) : mword 64) 4)
            by (rewrite /L3; apply upd_eq).
          iEval (rewrite HraL3) in "Hpc".
          assert (Hpp8a : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x86) : mword 64) 4)
                          = (mword_of_int (KernelSyms.pipewrite + 0x8a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp8a) in "Hpc".
          assert (HcsML3 : callee_saved M L3).
          { rewrite /L3 /L2 /L1.
            apply callee_saved_insert_r; [vm_compute; reflexivity|].
            apply callee_saved_insert_r; [vm_compute; reflexivity|].
            apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
          assert (HcsMK0 : callee_saved M K0) by (apply (callee_saved_trans M L3 K0 HcsML3 Hkcs)).
          assert (HregsK0 : pw_loop_regs m K0 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i)
            by (apply (pw_loop_regs_cs m M K0 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i HcsMK0 Hregs)).
          pose proof HregsK0 as HregsK0'.
          destruct HregsK0' as (KspF & Ks0F & Ks1F & Ks2F & Ks3F & Ks4F & Ks5F &
                                Ks6F & Ks7F & Ks8F & Ks9F & Ks10F & Ks11F).
          iPoseProof (pwi_8a with "Htext") as "Hi8a".
          destruct (neq_vec (sign_extend' 64 kl : mword 64) (zero_reg : mword 64)) eqn:Hklz.
          + (* ==== killed: the -1 arm ==== *)
            assert (Hcnz : neq_vec (K0 !!! Regidx Ra0) (zero_reg : mword 64) = true)
              by (rewrite Hka0; exact Hklz).
            assert (Halz : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x8a) : mword 64)
                             (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 222 : mword 8) ('b"0"))))) 0) ('b"0") = true)
              by (vm_compute; reflexivity).
            iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x8a)) (mword_of_int 222 : mword 8)
                      (Cregidx (mword_of_int 2)) Ra0 K0 (av - 14)%nat false
                      ltac:(vm_compute; reflexivity) ltac:(nz) Hcnz Halz with "Hcg Hpc Hi8a [-]").
            iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
            assert (Hj46 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x8a) : mword 64)
                             (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 222 : mword 8) ('b"0"))))
                           = mword_of_int (KernelSyms.pipewrite + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hj46) in "Hpc".
            iDestruct "HEX" as "[_ MIN]". rewrite /pw_minus1.
            iSpecialize ("MIN" $! CIDlp with "[%]"); [wp_next_chain|].
            iApply ("MIN" $! K0 Pc with "[%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked [Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack] Hpc Href Hpriv Hpark").
            * unfold pw_min_regs. split_and!; assumption.
            * exact Hext.
            * iApply (pw_res_intro γp pi nr nw ro wo vname bs Hcnt Hbslen
                        with "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack").
          + (* ==== alive: read the counters ==== *)
            iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x8a)) (mword_of_int 222 : mword 8)
                      (Cregidx (mword_of_int 2)) Ra0 K0 (av - 14)%nat false
                      ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgall; rewrite Hka0; exact Hklz) with "Hcg Hpc Hi8a [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
            assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x8a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpp8c) in "Hpc".
            (* +0x8c lw a5,536(s1) : nread *)
            assert (Hnraddr : add_vec (K0 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)) = a_pnread pi)
              by (rewrite Ks1F; reflexivity).
            iPoseProof (pwi_8c with "Htext") as "Hi8c".
            iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x8c)) Ra5 Rs1 (mword_of_int 536 : mword 12)
                      K0 (av - 14)%nat nr false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c [Hnr] [-]").
            { rgall. iEval (rewrite Hnraddr). iExact "Hnr". }
            iApply wp_next_off_intro. iIntros "Hcg Hpc Hnr". rgall.
            iEval (rewrite Hnraddr) in "Hnr".
            set (K1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> K0).
            change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> K0) with K1.
            assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x8c) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpp90) in "Hpc".
            (* +0x90 lw a4,540(s1) : nwrite *)
            assert (Hnwaddr : add_vec (K1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi).
            { rewrite /K1 upd_ne; [| reg_neq]. rewrite Ks1F. reflexivity. }
            iPoseProof (pwi_90 with "Htext") as "Hi90".
            iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x90)) Ra4 Rs1 (mword_of_int 540 : mword 12)
                      K1 (av - 14)%nat nw false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90 [Hnw] [-]").
            { rgall. iEval (rewrite Hnwaddr). iExact "Hnw". }
            iApply wp_next_off_intro. iIntros "Hcg Hpc Hnw". rgall.
            iEval (rewrite Hnwaddr) in "Hnw".
            set (K2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 nw)]> K1).
            change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 nw)]> K1) with K2.
            assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x90) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpp94) in "Hpc".
            (* +0x94 addiw a5,a5,512 *)
            iPoseProof (pwi_94 with "Htext") as "Hi94".
            iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x94)) Ra5 Ra5
                      (mword_of_int 512 : mword 12) K2 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                      with "Hcg Hpc Hi94 [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
            set (K3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                (add_vec (K2 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 512 : mword 12))) 31 0))]> K2).
            change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                (add_vec (K2 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 512 : mword 12))) 31 0))]> K2) with K3.
            assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x94) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpp98) in "Hpc".
            assert (Ha5K2 : K2 !!! Regidx Ra5 = sign_extend' 64 nr).
            { rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_eq. reflexivity. }
            assert (H512 : (subrange_vec_dec (add_vec (sign_extend' 64 nr : mword 64)
                              (sign_extend' 64 (mword_of_int 512 : mword 12))) 31 0 : mword 32)
                           = add_vec nr (mword_of_int 512 : mword 32))
              by (apply (pw_addiw_lit nr (mword_of_int 512 : mword 12) 512); vm_compute; reflexivity).
            assert (Ha5K3 : K3 !!! Regidx Ra5 = sign_extend' 64 (add_vec nr (mword_of_int 512 : mword 32))).
            { rewrite /K3 upd_eq. unfold regval_into_reg. rewrite Ha5K2 H512. reflexivity. }
            assert (Ha4K3 : K3 !!! Regidx Ra4 = sign_extend' 64 nw).
            { rewrite /K3 upd_ne; [| reg_neq]. rewrite /K2 upd_eq. reflexivity. }
            assert (HcsK0K3 : callee_saved K0 K3).
            { rewrite /K3 /K2 /K1.
              apply callee_saved_insert_r; [vm_compute; reflexivity|].
              apply callee_saved_insert_r; [vm_compute; reflexivity|].
              apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
            assert (HregsK3 : pw_loop_regs m K3 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i)
              by (apply (pw_loop_regs_cs m K0 K3 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i HcsK0K3 HregsK0)).
            pose proof HregsK3 as HregsK3'.
            destruct HregsK3' as (Jsp & Js0 & Js1 & Js2 & Js3 & Js4 & Js5 &
                                  Js6 & Js7 & Js8 & Js9 & Js10 & Js11).
            (* +0x98 beq a4,a5 : the pipe-full test *)
            iPoseProof (pwi_98 with "Htext") as "Hi98".
            destruct (eq_vec (K3 !!! Regidx Ra4) (K3 !!! Regidx Ra5)) eqn:Hfull.
            * (* ======== FULL: wakeup(&nread); sleep(&nwrite, &lock) ======== *)
              assert (Half : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x98) : mword 64)
                               (sign_extend' 64 (mword_of_int 8148 : mword 13))) 0) ('b"0") = true)
                by (vm_compute; reflexivity).
              iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x98)) (mword_of_int 8148 : mword 13)
                        Ra5 Ra4 K3 (av - 14)%nat false ltac:(nz) ltac:(nz) Hfull Half
                        with "Hcg Hpc Hi98 [-]").
              iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              assert (Hj6c : add_vec (mword_of_int (KernelSyms.pipewrite + 0x98) : mword 64)
                               (sign_extend' 64 (mword_of_int 8148 : mword 13))
                             = mword_of_int (KernelSyms.pipewrite + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hj6c) in "Hpc".
              (* the pipe goes back together untouched *)
              iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
              { iApply (pw_res_intro γp pi nr nw ro wo vname bs Hcnt Hbslen
                          with "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack"). }
              (* +0x6c c.mv a0,s10 *)
              iPoseProof (pwi_6c with "Htext") as "Hi6c".
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x6c)) Ra0 Rs10 K3 (av - 14)%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6c [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (F1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs10))]> K3).
              change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs10))]> K3) with F1.
              assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp6e) in "Hpc".
              (* +0x6e jal wakeup *)
              iPoseProof (pwi_6e with "Htext") as "Hi6e".
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x6e)) Rra (mword_of_int 2087484 : mword 21)
                        F1 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc Hi6e [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (F2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) 4)]> F1).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) 4)]> F1) with F2.
              assert (Hjwk : add_vec (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) (sign_extend' 64 (mword_of_int 2087484 : mword 21))
                             = mword_of_int KernelSyms.wakeup) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjwk) in "Hpc".
              assert (HwK : (18 <= av - 14)%nat) by lia.
              assert (HwdomF : forall r : regidx, r ∈ dom (rf_to_gmap F2)) by (intro r; apply rf_to_gmap_dom).
              assert (Hwa0f : mycpu_ret (rget F2 Rtp) = mycpu_ret cid_word) by (rewrite rget_tp; reflexivity).
              assert (Hwnz : eq_vec (zero_reg : mword 64) (mycpu_ret (rget F2 Rtp)) = false)
          by (rewrite rget_tp; apply mycpu_ret_nonzero; apply tp_ok_cid).
              assert (Hwlvl : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
              iApply (Wakeup.wp_wakeup_sconf Φ F2 γs (mycpu_ret cid_word) (proc_addr j) 1%nat (av - 14)%nat true C false
                        HwK HwdomF Hlen Hwa0f Hwnz Hwlvl
                        with "Hcg Hown Htext Hpc Hpanic Hpinv [-]").
              iApply wp_next_off_intro. iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hown Htext2 Hpc". rgall.
              assert (HraF2 : F2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) 4)
                by (rewrite /F2; apply upd_eq).
              iEval (rewrite HraF2) in "Hpc".
              assert (Hpp72 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0x72) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp72) in "Hpc".
              assert (HcsK3F2 : callee_saved K3 F2).
              { rewrite /F2 /F1. apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
              assert (HcsK3Mw : callee_saved K3 Mw) by (apply (callee_saved_trans K3 F2 Mw HcsK3F2 Hwcs)).
              assert (HregsMw : pw_loop_regs m Mw (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i)
                by (apply (pw_loop_regs_cs m K3 Mw (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i HcsK3Mw HregsK3)).
              pose proof HregsMw as HregsMw'.
              destruct HregsMw' as (Wsp & Ws0 & Ws1 & Ws2 & Ws3 & Ws4 & Ws5 &
                                    Ws6 & Ws7 & Ws8 & Ws9 & Ws10 & Ws11).
              (* +0x72 c.mv a1,s1 *)
              iPoseProof (pwi_72 with "Htext") as "Hi72".
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x72)) Ra1 Rs1 Mw (av - 14)%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi72 [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (G1 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw).
              change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw) with G1.
              assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp74) in "Hpc".
              (* +0x74 c.mv a0,s9 *)
              iPoseProof (pwi_74 with "Htext") as "Hi74".
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x74)) Ra0 Rs9 G1 (av - 14)%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74 [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (G2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Rs9))]> G1).
              change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Rs9))]> G1) with G2.
              assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x74) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp76) in "Hpc".
              (* +0x76 jal sleep *)
              iPoseProof (pwi_76 with "Htext") as "Hi76".
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x76)) Rra (mword_of_int 2087400 : mword 21)
                        G2 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc Hi76 [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (G3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x76) : mword 64) 4)]> G2).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x76) : mword 64) 4)]> G2) with G3.
              assert (Hjsl : add_vec (mword_of_int (KernelSyms.pipewrite + 0x76) : mword 64) (sign_extend' 64 (mword_of_int 2087400 : mword 21))
                             = mword_of_int KernelSyms.sleep) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjsl) in "Hpc".
              assert (Ha1G3 : G3 !!! Regidx Ra1 = pi).
              { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
                rewrite /G1 upd_eq. unfold regval_into_reg. rewrite Ws1. apply add_vec_zero_l. }
              assert (HlkaG3 : add_vec (G3 !!! Regidx Ra1) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
              { rewrite Ha1G3.
                replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
                  by (apply bv_eq; vm_compute; reflexivity).
                apply kv_addv_zero. }
              assert (Hav22 : (22 <= av - 14)%nat) by lia.
              iApply (SleepGen.wp_sleep_gen_sconf Φ γs j γlp γl pi (pipe_res γp pi)
                        (pipe_ref γp w q) (pipe_dead γl γp) G3 (av - 14)%nat true C
                        Hj Hjlp HlkaG3 eq_refl Hav22
                        ltac:(iApply pipe_ref_dead) ltac:(intros ?i; iApply locked_dead)
                        ltac:(intros ?i; iApply locked_pre_dead)
                        with "Hcg Hown Hpay Htext Hpc Hpinv Hscheds Hopen Href Hlocked Hres Hpanic Hpark [-]").
              iIntros (CIDsl Hssl Ms) "%Hscs Hcg Hown Hpay Hpc Href Hlocked Hres Hpark". rgall.
              assert (HraG3 : G3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x76) : mword 64) 4)
                by (rewrite /G3; apply upd_eq).
              iEval (rewrite HraG3) in "Hpc".
              assert (Hpp7a : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x76) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp7a) in "Hpc".
              assert (HcsMwG3 : callee_saved Mw G3).
              { rewrite /G3 /G2 /G1.
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
              assert (HregsMs : pw_loop_regs m Ms (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i).
              { apply (pw_loop_regs_cs m G3 Ms (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i Hscs).
                apply (pw_loop_regs_cs m Mw G3 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i HcsMwG3 HregsMw). }
              iApply (pw_guard_step (CID := CIDsl) CID γa γf Φ γs j γl γp w q m av true C pid V n sp0 pi addr i Ms Pc
                        Hn0 Hn31 ltac:(lia) ltac:(wp_next_chain) Hext HregsMs
                        with "Htext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Henv Hpark HEX IH").
            * (* ======== NOT full: copy one byte in ======== *)
              assert (Hfeq : eq_vec (sign_extend' 64 nw : mword 64)
                               (sign_extend' 64 (add_vec nr (mword_of_int 512 : mword 32))) = false).
              { rewrite -Ha4K3 -Ha5K3. exact Hfull. }
              assert (Hne : nw <> add_vec nr (mword_of_int 512 : mword 32)).
              { intro Heq.
                assert (Hc : eq_vec (sign_extend' 64 nw : mword 64)
                               (sign_extend' 64 (add_vec nr (mword_of_int 512 : mword 32))) = true)
                  by (apply eq_vec_true_iff; rewrite Heq; reflexivity).
                rewrite Hc in Hfeq. discriminate. }
              iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x98)) (mword_of_int 8148 : mword 13)
                        Ra5 Ra4 K3 (av - 14)%nat false ltac:(nz) ltac:(nz) Hfull
                        with "Hcg Hpc Hi98 [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x98) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp9c) in "Hpc".
              (* +0x9c c.mv a3,s7 *)
              iPoseProof (pwi_9c with "Htext") as "Hi9c".
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x9c)) Ra3 Rs7 K3 (av - 14)%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9c [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (N1 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs7))]> K3).
              change (<[Regidx Ra3 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs7))]> K3) with N1.
              assert (Hpp9e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x9c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp9e) in "Hpc".
              (* +0x9e add a2,s2,s5 *)
              iPoseProof (pwi_9e with "Htext") as "Hi9e".
              iApply (wp_add_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x9e)) Ra2 Rs2 Rs5
                        (add_vec (N1 !!! Regidx Rs2) (N1 !!! Regidx Rs5)) N1 (av - 14)%nat false
                        ltac:(nz) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi9e [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (N2 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (N1 !!! Regidx Rs2) (N1 !!! Regidx Rs5))]> N1).
              change (<[Regidx Ra2 := regval_into_reg
                  (add_vec (N1 !!! Regidx Rs2) (N1 !!! Regidx Rs5))]> N1) with N2.
              assert (Hppa2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x9e) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppa2) in "Hpc".
              (* +0xa2 c.mv a1,s8 *)
              iPoseProof (pwi_a2 with "Htext") as "Hia2".
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xa2)) Ra1 Rs8 N2 (av - 14)%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia2 [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (N3 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (N2 !!! Regidx Rs8))]> N2).
              change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (N2 !!! Regidx Rs8))]> N2) with N3.
              assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa2) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppa4) in "Hpc".
              (* the ONE borrow out of [proc_priv] for this iteration *)
              iDestruct (proc_priv_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
              iEval (rewrite (pw_pv_sz_upd V Pc)) in "Hszc".
              iEval (rewrite (pw_pv_upt_upd V Pc)) in "Hptc".
              iEval (rewrite (pw_pv_upt_upd V Pc)) in "Hpt".
              iEval (rewrite (pw_pv_sz_upd V Pc) (pw_pv_upt_upd V Pc)) in "Hpback".
              (* +0xa4 ld a0,80(s3) : p->pagetable *)
              assert (Hs3N3 : N3 !!! Regidx Rs3 = proc_addr j).
              { rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
                rewrite /N1 upd_ne; [exact Js3 | reg_neq]. }
              assert (Hptaddr : add_vec (N3 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 80 : mword 12))
                                = p_pagetable (proc_addr j)) by (rewrite Hs3N3; reflexivity).
              iPoseProof (pwi_a4 with "Htext") as "Hia4".
              iEval (rewrite -Hptaddr) in "Hptc".
              iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xa4)) Ra0 Rs3
                        (mword_of_int 80 : mword 12) N3 (av - 14)%nat (page_base (ud_root Pc)) false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia4 Hptc [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc Hptc". rgall.
              iEval (rewrite Hptaddr) in "Hptc".
              set (N4 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root Pc))]> N3).
              change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root Pc))]> N3) with N4.
              assert (Hppa8 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa4) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppa8) in "Hpc".
              (* +0xa8 jal copyin *)
              iPoseProof (pwi_a8 with "Htext") as "Hia8".
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xa8)) Rra (mword_of_int 2085258 : mword 21)
                        N4 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc Hia8 [-]").
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              set (N5 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa8) : mword 64) 4)]> N4).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa8) : mword 64) 4)]> N4) with N5.
              assert (Hjci : add_vec (mword_of_int (KernelSyms.pipewrite + 0xa8) : mword 64) (sign_extend' 64 (mword_of_int 2085258 : mword 21))
                             = mword_of_int KernelSyms.copyin) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjci) in "Hpc".
              assert (Ha0N5 : N5 !!! Regidx Ra0 = page_base (ud_root Pc)).
              { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_eq. reflexivity. }
              assert (Ha1N5 : N5 !!! Regidx Ra1 = pa_add (pa_stk sp0 13%nat) 7%nat).
              { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
                rewrite /N3 upd_eq. unfold regval_into_reg.
                rewrite (_ : N2 !!! Regidx Rs8 = pa_add (pa_stk sp0 13%nat) 7%nat); [apply add_vec_zero_l|].
                rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact Js8 | reg_neq]. }
              assert (Ha3N5 : N5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
              { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
                rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
                rewrite /N1 upd_eq. unfold regval_into_reg. rewrite Js7.
                rewrite add_vec_zero_l. apply bv_eq; vm_compute; reflexivity. }
              assert (HK50 : (50 <= av - 14)%nat) by lia.
              assert (Hlen1 : (Z.of_nat 1%nat < 2 ^ 64)%Z) by (vm_compute; reflexivity).
              (* the single byte [ch] IS copyin's destination buffer *)
              iDestruct "HCH" as "(%Hal13 & Hb13 & Hslot14)".
              iDestruct (bytes_own_acc (DfracOwn 1) (pa_stk sp0 13%nat) 8%nat 7%nat ltac:(lia) with "Hb13")
                as "[Hchx Hchback]".
              iDestruct "Hchx" as (b0) "Hch".
              iAssert ([∗ list] k ∈ seq 0 1, (pa_add (N5 !!! Regidx Ra1) k) ↦ₘ ((fun _ : nat => b0) k))%I
                with "[Hch]" as "Hbuf".
              { cbn [seq]. iSplitL "Hch"; [| done]. iEval (rewrite Ha1N5 pa_add_0). iExact "Hch". }
              iApply (Copyin.wp_copyin_sconf γa N5 Pc (pv_sz V) 1%nat (fun _ : nat => b0)
                        (av - 14)%nat 1%nat true (proc_addr j) C (DfracOwn 1) (DfracOwn 1) false
                        HK50 Ha0N5 Ha3N5 Hlen1 Hszb Hlvl1
                        with "Hcg Hown Htext Hpc Hszc Hptc Hpt Henv Hbuf [-]").
              iApply wp_next_off_intro. iIntros (mr P' dst_new) "Hcg Hown Hpc Hszc Hptc Hpt Hbuf %Hcsr %Hextr %Hret". rgall.
              assert (HraN5 : N5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa8) : mword 64) 4)
                by (rewrite /N5; apply upd_eq).
              iEval (rewrite HraN5) in "Hpc".
              assert (Hppac : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa8) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0xac) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppac) in "Hpc".
              (* the destination byte back out of copyin's buffer *)
              iEval (cbn [seq]) in "Hbuf".
              iDestruct "Hbuf" as "[Hch _]".
              iEval (rewrite Ha1N5 pa_add_0) in "Hch".
              (* rebuild [proc_priv] at the extended descriptor *)
              iAssert (⌜uptd_ext_sz (pv_sz V) Pc P'⌝)%I as "#Hxe";
                [iPureIntro; exact Hextr|].
              iDestruct ("Hpback" $! P' with "Hxe Hszc Hptc Hpt") as "Hpriv".
              iEval (rewrite (pw_upd_upt_upd V Pc P')) in "Hpriv".
              assert (Hext' : uptd_ext (pv_upt V) P')
                by (apply (uptd_ext_trans (pv_upt V) Pc P' Hext
                             (uptd_ext_sz_ext _ _ _ Hextr))).
              (* the register state survived copyin *)
              assert (HcsK3N5 : callee_saved K3 N5).
              { rewrite /N5 /N4 /N3 /N2 /N1.
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
              assert (Hcsmr : callee_saved K3 mr) by (apply (callee_saved_trans K3 N5 mr HcsK3N5 Hcsr)).
              assert (Hregsmr : pw_loop_regs m mr (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i)
                by (apply (pw_loop_regs_cs m K3 mr (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i Hcsmr HregsK3)).
              pose proof Hregsmr as Hregsmr'.
              destruct Hregsmr' as (Rsp & Rs0f & Rs1f & Rs2f & Rs3f & Rs4f & Rs5f &
                                    Rs6f & Rs7f & Rs8f & Rs9f & Rs10f & Rs11f).
              (* +0xac beq a0,s6 : did the copy fail? *)
              iPoseProof (pwi_ac with "Htext") as "Hiac".
              destruct (eq_vec (mr !!! Regidx Ra0) (mr !!! Regidx Rs6)) eqn:Hfail.
              ** (* ==== copyin failed: break, returning the current i ==== *)
                 assert (Half : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0xac) : mword 64)
                                  (sign_extend' 64 (mword_of_int 64 : mword 13))) 0) ('b"0") = true)
                   by (vm_compute; reflexivity).
                 iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xac)) (mword_of_int 64 : mword 13)
                           Rs6 Ra0 mr (av - 14)%nat false ltac:(nz) ltac:(nz) Hfail Half
                           with "Hcg Hpc Hiac [-]").
                 iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 assert (Hjec : add_vec (mword_of_int (KernelSyms.pipewrite + 0xac) : mword 64)
                                  (sign_extend' 64 (mword_of_int 64 : mword 13))
                                = mword_of_int (KernelSyms.pipewrite + 0xec)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hjec) in "Hpc".
                 (* put the [ch] byte back and re-bundle the slot *)
                 iDestruct ("Hchback" $! (dst_new 0%nat) with "Hch") as "Hb13".
                 iAssert (pw_chslot sp0) with "[Hb13 Hslot14]" as "HCH".
                 { rewrite /pw_chslot. iSplitR; [done|]. iFrame "Hb13 Hslot14". }
                 (* +0xec .. +0xf4 reload s6..s10 *)
                 iPoseProof (pwi_ec with "Htext") as "Hj0".
                 iPoseProof (pwi_ee with "Htext") as "Hj1".
                 iPoseProof (pwi_f0 with "Htext") as "Hj2".
                 iPoseProof (pwi_f2 with "Htext") as "Hj3".
                 iPoseProof (pwi_f4 with "Htext") as "Hj4".
                 assert (Eee : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xec) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xee)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (Ef0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xee) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf0)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (Ef2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf0) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf2)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (Ef4 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf2) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf4)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (Ef6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf4) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf6)) by (apply bv_eq; vm_compute; reflexivity).
                 iApply (pw_restore5 (proc_addr j) false (mword_of_int (KernelSyms.pipewrite + 0xec)) (mword_of_int (KernelSyms.pipewrite + 0xee))
                           (mword_of_int (KernelSyms.pipewrite + 0xf0)) (mword_of_int (KernelSyms.pipewrite + 0xf2)) (mword_of_int (KernelSyms.pipewrite + 0xf4))
                           (mword_of_int (KernelSyms.pipewrite + 0xf6)) mr m (av - 14)%nat sp0
                           Rsp Eee Ef0 Ef2 Ef4 Ef6
                           with "Hcg Hpc Hj0 Hj1 Hj2 Hj3 Hj4 HF5 [-]").
                 iApply wp_next_off_intro. iIntros (M') "%Hrst Hcg Hpc HF5".
                 destruct Hrst as (R6 & R7 & R8 & R9 & R10 & Rrest).
                 assert (Hsp' : M' !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
                 { rewrite (Rrest csp_rs1 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Rsp. }
                 assert (Hs1' : M' !!! Regidx Rs1 = pi).
                 { rewrite (Rrest (mword_of_int 9) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Rs1f. }
                 assert (Hs2' : M' !!! Regidx Rs2 = (mword_of_int i : mword 64)).
                 { rewrite (Rrest (mword_of_int 18) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Rs2f. }
                 assert (Hs11' : M' !!! Regidx Rs11 = m !!! Regidx Rs11).
                 { rewrite (Rrest (mword_of_int 27) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Rs11f. }
                 (* +0xf6 c.j -> the wakeup/release tail *)
                 iPoseProof (pwi_f6 with "Htext") as "Hif6".
                 iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xf6))
                           (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")))
                           M' (av - 14)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif6 [-]").
                 iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc". rgall.
                 assert (Hjd8 : add_vec (mword_of_int (KernelSyms.pipewrite + 0xf6) : mword 64)
                                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0"))))
                                = mword_of_int (KernelSyms.pipewrite + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hjd8) in "Hpc".
                 iDestruct "HEX" as "[TAIL _]". rewrite /pw_tail.
                 iSpecialize ("TAIL" $! CIDlp with "[%]"); [wp_next_chain|].
                 iApply ("TAIL" $! M' P' with "[%] [%] [%] [%] HF7 [HF5 HCH] Hcg Hown Hpay Hlocked [Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack] Hpc Href Hpriv Hpark").
                 --- unfold pw_base_regs. split_and!; assumption.
                 --- exact Hs1'.
                 --- rewrite Hs2'. right. exists i. split; [reflexivity | lia].
                 --- exact Hext'.
                 --- iApply (pw_stack7_of m sp0 with "HF5 HCH").
                 --- iApply (pw_res_intro γp pi nr nw ro wo vname bs Hcnt Hbslen
                               with "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack").
              ** (* ==== copyin succeeded: nwrite++, store the byte, i++ ==== *)
                 iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xac)) (mword_of_int 64 : mword 13)
                           Rs6 Ra0 mr (av - 14)%nat false ltac:(nz) ltac:(nz) Hfail
                           with "Hcg Hpc Hiac [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 assert (Hppb0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xac) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppb0) in "Hpc".
                 (* +0xb0 lw a5,540(s1) *)
                 assert (Hnwaddr2 : add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi)
                   by (rewrite Rs1f; reflexivity).
                 iPoseProof (pwi_b0 with "Htext") as "Hib0".
                 iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xb0)) Ra5 Rs1 (mword_of_int 540 : mword 12)
                           mr (av - 14)%nat nw false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib0 [Hnw] [-]").
                 { rgall. iEval (rewrite Hnwaddr2). iExact "Hnw". }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hnw". rgall.
                 iEval (rewrite Hnwaddr2) in "Hnw".
                 set (P1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw)]> mr).
                 change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw)]> mr) with P1.
                 assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xb0) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xb4)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppb4) in "Hpc".
                 assert (Ha5P1 : P1 !!! Regidx Ra5 = sign_extend' 64 nw) by (rewrite /P1; apply upd_eq).
                 (* +0xb4 addiw a4,a5,1 *)
                 iPoseProof (pwi_b4 with "Htext") as "Hib4".
                 iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xb4)) Ra4 Ra5
                           (mword_of_int 1 : mword 12) P1 (av - 14)%nat false ltac:(nz) ltac:(rdok)
                           with "Hcg Hpc Hib4 [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 set (P2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> P1).
                 change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> P1) with P2.
                 assert (Hppb8 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xb4) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xb8)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppb8) in "Hpc".
                 assert (HX1 : (subrange_vec_dec (add_vec (sign_extend' 64 nw : mword 64)
                                  (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0 : mword 32)
                               = add_vec nw (mword_of_int 1 : mword 32))
                   by (apply (pw_addiw_lit nw (mword_of_int 1 : mword 12) 1); vm_compute; reflexivity).
                 assert (Ha4P2 : P2 !!! Regidx Ra4 = sign_extend' 64 (add_vec nw (mword_of_int 1 : mword 32))).
                 { rewrite /P2 upd_eq. unfold regval_into_reg. rewrite Ha5P1 HX1. reflexivity. }
                 assert (Hstore : trunc32 (P2 !!! Regidx Ra4) = add_vec nw (mword_of_int 1 : mword 32))
                   by (rewrite Ha4P2; apply trunc32_sext64).
                 (* +0xb8 sw a4,540(s1) *)
                 assert (Hnwaddr3 : add_vec (P2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi).
                 { rewrite /P2 upd_ne; [| reg_neq]. rewrite /P1 upd_ne; [| reg_neq].
                   rewrite Rs1f. reflexivity. }
                 iPoseProof (pwi_b8 with "Htext") as "Hib8".
                 iEval (rewrite -Hnwaddr3) in "Hnw".
                 iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xb8)) Ra4 Rs1
                           (mword_of_int 540 : mword 12) P2 (av - 14)%nat nw false
                           with "Hcg Hpc Hib8 Hnw [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hnw". rgall.
                 iEval (rewrite Hstore Hnwaddr3) in "Hnw".
                 assert (Hppbc : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xb8) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xbc)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppbc) in "Hpc".
                 assert (Hcnt' : pipe_count_ok nr (add_vec nw (mword_of_int 1 : mword 32)))
                   by (apply pipe_count_incr_w; [exact Hcnt | exact Hne]).
                 (* +0xbc andi a5,a5,511 -- the %PIPESIZE index *)
                 assert (Ha5P2 : P2 !!! Regidx Ra5 = sign_extend' 64 nw)
                   by (rewrite /P2 upd_ne; [exact Ha5P1 | reg_neq]).
                 iPoseProof (pwi_bc with "Htext") as "Hibc".
                 iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xbc)) Ra5 Ra5
                           (mword_of_int 511 : mword 12)
                           (and_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 (mword_of_int 511 : mword 12)))
                           P2 (av - 14)%nat false ltac:(nz) ltac:(rdok) ltac:(rgall; rewrite Ha5P2; reflexivity)
                           with "Hcg Hpc Hibc [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 set (P3 := <[Regidx Ra5 := regval_into_reg
                     (and_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 (mword_of_int 511 : mword 12)))]> P2).
                 change (<[Regidx Ra5 := regval_into_reg
                     (and_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 (mword_of_int 511 : mword 12)))]> P2) with P3.
                 assert (Hppc0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xbc) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xc0)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppc0) in "Hpc".
                 (* +0xc0 c.add a5,a5,s1 *)
                 iPoseProof (pwi_c0 with "Htext") as "Hic0".
                 iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xc0)) Ra5 Rs1 P3 (av - 14)%nat false
                           ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic0 [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 set (P4 := <[Regidx Ra5 := regval_into_reg
                     (add_vec (P3 !!! Regidx Ra5) (P3 !!! Regidx Rs1))]> P3).
                 change (<[Regidx Ra5 := regval_into_reg
                     (add_vec (P3 !!! Regidx Ra5) (P3 !!! Regidx Rs1))]> P3) with P4.
                 assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xc0) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xc2)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppc2) in "Hpc".
                 assert (Hs1P3 : P3 !!! Regidx Rs1 = pi).
                 { rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
                   rewrite /P1 upd_ne; [exact Rs1f | reg_neq]. }
                 assert (Hs0P4 : P4 !!! Regidx Rs0 = sp0).
                 { rewrite /P4 upd_ne; [| reg_neq]. rewrite /P3 upd_ne; [| reg_neq].
                   rewrite /P2 upd_ne; [| reg_neq]. rewrite /P1 upd_ne; [exact Rs0f | reg_neq]. }
                 assert (Ha5P4 : P4 !!! Regidx Ra5
                                 = add_vec (and_vec (sign_extend' 64 nw : mword 64)
                                     (sign_extend' 64 (mword_of_int 511 : mword 12))) pi).
                 { rewrite /P4 upd_eq. unfold regval_into_reg. rewrite Hs1P3.
                   rewrite (_ : P3 !!! Regidx Ra5
                                = and_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 (mword_of_int 511 : mword 12)));
                     [reflexivity | rewrite /P3; apply upd_eq]. }
                 (* +0xc2 lbu a4,-97(s0) -- the byte copyin just wrote *)
                 assert (Hchaddr : add_vec (P4 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3999 : mword 12))
                                   = pa_add (pa_stk sp0 13%nat) 7%nat)
                   by (rewrite Hs0P4; apply pw_ch_addr).
                 iPoseProof (pwi_c2 with "Htext") as "Hic2".
                 iEval (rewrite -Hchaddr) in "Hch".
                 iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xc2)) Ra4 Rs0
                           (mword_of_int 3999 : mword 12) P4 (av - 14)%nat ((dst_new 0%nat) : mword 8) false
                           ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic2 Hch [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hch". rgall.
                 iEval (rewrite Hchaddr) in "Hch".
                 set (P5 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 ((dst_new 0%nat) : mword 8))]> P4).
                 change (<[Regidx Ra4 := regval_into_reg (zero_extend' 64 ((dst_new 0%nat) : mword 8))]> P4) with P5.
                 assert (Hppc6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xc2) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xc6)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppc6) in "Hpc".
                 (* the [ch] byte goes back into the frame slot *)
                 iDestruct ("Hchback" $! (dst_new 0%nat) with "Hch") as "Hb13".
                 iAssert (pw_chslot sp0) with "[Hb13 Hslot14]" as "HCH".
                 { rewrite /pw_chslot. iSplitR; [done|]. iFrame "Hb13 Hslot14". }
                 (* +0xc6 sb a4,24(a5) -- into pi->data[nwrite % PIPESIZE] *)
                 set (idx := Z.to_nat (bv_unsigned nw mod 512)).
                 assert (Hidx : (idx < 512)%nat) by (rewrite /idx; apply pw_idx_lt).
                 assert (HAu : bv_unsigned (and_vec (sign_extend' 64 nw : mword 64)
                                 (sign_extend' 64 (mword_of_int 511 : mword 12))) = Z.of_nat idx)
                   by (rewrite /idx; apply pw_andi_idx).
                 assert (Ha5P5 : P5 !!! Regidx Ra5
                                 = add_vec (and_vec (sign_extend' 64 nw : mword 64)
                                     (sign_extend' 64 (mword_of_int 511 : mword 12))) pi)
                   by (rewrite /P5 upd_ne; [exact Ha5P4 | reg_neq]).
                 assert (Hsbaddr : add_vec (P5 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 24 : mword 12))
                                   = pa_add pi (pipe_data_off + idx)%nat).
                 { rewrite Ha5P5. apply (pw_data_addr pi _ _ idx HAu). vm_compute. reflexivity. }
                 assert (Hlk : exists b1 : bv 8, bs !! idx = Some b1).
                 { apply lookup_lt_is_Some_2. rewrite Hbslen. unfold PIPESIZE. exact Hidx. }
                 destruct Hlk as [b1 Hlk].
                 iDestruct (pw_data_acc pi bs idx b1 Hlk with "Hdat") as "[Hcell Hdatback]".
                 iPoseProof (pwi_c6 with "Htext") as "Hic6".
                 iEval (rewrite -Hsbaddr) in "Hcell".
                 iApply (wp_sb_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xc6)) Ra4 Ra5
                           (mword_of_int 24 : mword 12) P5 (av - 14)%nat b1 false
                           with "Hcg Hpc Hic6 Hcell [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell". rgall.
                 iEval (rewrite Hsbaddr) in "Hcell".
                 iDestruct ("Hdatback" $! (trunc8 (P5 !!! Regidx Ra4)) with "Hcell") as "Hdat".
                 assert (Hbslen' : length (<[idx := trunc8 (P5 !!! Regidx Ra4)]> bs) = PIPESIZE)
                   by (rewrite length_insert; exact Hbslen).
                 assert (Hppca : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xc6) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xca)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppca) in "Hpc".
                 (* +0xca c.addiw s2,s2,1 *)
                 iPoseProof (pwi_ca with "Htext") as "Hica".
                 iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xca)) Rs2 (mword_of_int 1 : mword 6)
                           P5 (av - 14)%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hica [-]").
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 set (P6 := <[Regidx Rs2 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P5 !!! Regidx Rs2) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> P5).
                 change (<[Regidx Rs2 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P5 !!! Regidx Rs2) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> P5) with P6.
                 assert (Hppcc : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xca) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xcc)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppcc) in "Hpc".
                 (* the loop invariant at i+1 *)
                 assert (Hcsmp5 : callee_saved mr P5).
                 { rewrite /P5 /P4 /P3 /P2 /P1.
                   apply callee_saved_insert_r; [vm_compute; reflexivity|].
                   apply callee_saved_insert_r; [vm_compute; reflexivity|].
                   apply callee_saved_insert_r; [vm_compute; reflexivity|].
                   apply callee_saved_insert_r; [vm_compute; reflexivity|].
                   apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
                 assert (HregsP5 : pw_loop_regs m P5 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i)
                   by (apply (pw_loop_regs_cs m mr P5 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i Hcsmp5 Hregsmr)).
                 pose proof HregsP5 as HregsP5'.
                 destruct HregsP5' as (Q1 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 &
                                       Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
                 assert (HregsP6 : pw_loop_regs m P6 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n (i + 1)%Z).
                 { unfold pw_loop_regs. split_and!.
                   { rewrite /P6 upd_ne; [exact Q1 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q3 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q4 | reg_neq]. }
                   { rewrite /P6 upd_eq. unfold regval_into_reg. rewrite Q5.
                     apply pw_addiw_i; lia. }
                   { rewrite /P6 upd_ne; [exact Q6 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q7 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q8 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q9 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q10 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q11 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q12 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q13 | reg_neq]. }
                   { rewrite /P6 upd_ne; [exact Q14 | reg_neq]. } }
                 (* the pipe goes back together with the incremented counter *)
                 iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
                 { iApply (pw_res_intro γp pi nr (add_vec nw (mword_of_int 1 : mword 32)) ro wo vname
                             (<[idx := trunc8 (P5 !!! Regidx Ra4)]> bs) Hcnt' Hbslen'
                             with "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack"). }
                 (* +0xcc c.j -> the guard, with i+1 *)
                 iPoseProof (pwi_cc with "Htext") as "Hicc".
                 iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xcc))
                           (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")))
                           P6 (av - 14)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hicc [-]").
                 iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc". rgall.
                 assert (Hj7a : add_vec (mword_of_int (KernelSyms.pipewrite + 0xcc) : mword 64)
                                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0"))))
                                = mword_of_int (KernelSyms.pipewrite + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hj7a) in "Hpc".
                 iApply (pw_guard_step (CID := CIDlp) CID γa γf Φ γs j γl γp w q m av true C pid V n sp0 pi addr
                           (i + 1)%Z P6 P' Hn0 Hn31 ltac:(lia) ltac:(wp_next_chain) Hext' HregsP6
                           with "Htext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Henv Hpark HEX IH"). }
      (* ---- +0x44 c.j -> the loop body, with i = 0 ---- *)
      iPoseProof (pwi_44 with "Htext") as "Hi44".
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x44))
                (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0")))
                C6 (av - 14)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi44 [-]").
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj7e : add_vec (mword_of_int (KernelSyms.pipewrite + 0x44) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.pipewrite + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hj7e) in "Hpc".
      rewrite /pw_loop.
      iSpecialize ("LOOP" $! CIDaq with "[%]"); [wp_next_chain|].
      iApply ("LOOP" $! 0%Z C6 (pv_upt V) with "[%] [%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href [Hpriv] Henv Hpark EXITS").
      + lia.
      + apply uptd_ext_refl.
      + exact HregsC6.
      + rewrite pw_upd_upt_id. iExact "Hpriv".
  Qed.


End ProofPipewrite.
End PipewriteProof.
