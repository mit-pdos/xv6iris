(* ProofPipewrite.v -- the whole-function WP for xv6's pipewrite().

     int pipewrite(struct pipe *pi, uint64 addr, int n)

   The contract is SpecPipewrite.v; the 108 instruction facts are
   CodePipewrite.v ([pwi_<off>]).  TWO upstream changes shaped the current
   text.  (1) xv6 `4f2fc8b` gave copyin a [psz] argument in a1, so the call
   site loads BOTH [pr->sz] (+0xb2) and [pr->pagetable] (+0xb6) and the other
   three arguments moved down a register; that extra instruction is why
   everything from +0xb2 to +0xde sits four bytes higher than it used to.
   (2) xv6 `76821fc` made a copyin failure report -1 when NOTHING had been
   copied yet, so the break arm became a [beqz s2] at +0xe0 over two restore
   blocks -- +0xf0 sets i := a0 (= -1) and +0xe4 keeps the partial count --
   which is a genuine new control-flow path, not relayout.  Both arms land on
   the same tail, and [PipeInvDefs.pipe_rw_ret] already admitted -1, so the
   contract in SpecPipewrite.v needed no change.  THE SLEEP PROTOCOL IS SPLIT IN TWO
   (SpecSleep.v): pipewrite drops and re-takes pi->lock itself at +0x7a /
   +0x84, through the ordinary [RELEASE_GEN] / [ACQUIRE_GEN] contracts, so the
   cancellable-lock genericity that used to ride inside sleep is just this
   function's own two calls -- see the block at +0x72.  Structure of the
   proof:

   - THREE iAssert'ed shared continuations, nested exactly as
     ProofPipealloc's EPI/T8/T4C recipe: [pw_epi] (the epilogue at +0x58,
     reached by every path), then [pw_exits := pw_tail /\ pw_minus1] -- the
     wakeup/release tail at +0x108 and the readopen==0/killed arm at +0x46 --
     offered as a CONJUNCTION because exactly one of them is taken and they
     must therefore SHARE the frame cells and the caller's continuation.

   - the while loop is UNBOUNDED (the sleep arm re-runs the same iteration),
     so it is an iLöb over [pw_loop], the loop-BODY assertion at +0x8c.  The
     guard [bge s2,s4] at +0x88 is NOT part of the body -- the first entry
     jumps past it (+0x44 -> +0x8c, i = 0 < n is already known) and both back
     edges arrive at it -- so it is factored as the Lemma [pw_guard_step],
     which takes the loop assertion itself as a premise.  The back edges are
     the ONLY places that still want a real [iNext] before applying the Löb IH
     (the +0xde [c.j], and on the sleep arm the +0xa6 [beq]-taken, whose later
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
     [pw_chslot] carves that slot into [StackBytes.bytes_own (KTR := KT1)] and keeps the
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
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn StackBytes CalleeSaved KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import WpLock ProcGeom CpuOwn KernelRvcDecode.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import PipeInvDefs.
Require Import PageGeom.
Require Import SpecMyproc SpecAcquire SpecKilled SpecWakeup SpecSleepPrepare SpecSleep SpecCopyin SpecRelease.
Require Import CodePipewrite.
Require Import SpecPipewrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal --
   away from tp the two are the same lookup and every index here is a
   literal.  See ProofPiperead.v for why [cpu_own] must also be opaque to
   typeclass search once the base enable is the literal [true]. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).

(* WHY THIS [Strategy] -- ProofVirtioDiskInit.v's register-tower cost at small
   scale.  The deepest chain in this proof is SEVEN links (the loop's [∀ M],
   then K0 -> K1 -> K2 -> K3 -> N1 -> N2 -> N3 -> N3b -> N4 -> N5 down the
   copy block) rather than that file's twenty-four, so the tower costs seconds
   rather than minutes -- but with [rget]/[tp_pin]/[rf_upd] transparent it is
   still the largest item in this file after the [Qed].  Measured 2026-08-13,
   isolated [coqc -time -async-proofs off], min of >=3 interleaved runs:

     as committed before this line ...........  98.3 s   (Qed 18.9 s)
     + Strategy opaque, three constants ......  92.2 s   (Qed 15.5 s)
     + [pose] for [set] (below) ..............  91.0 s   (Qed 15.5 s)

   Per sentence, the opacity BUYS (the leaf's unifier no longer walks
   [rget -> tp_pin -> rf_upd] down the chain):

     +0xb6 [ld a0,80(s3)]  ... 2.58 s -> 0.22 s
     +0xac [add a3,s2,s5]  ... 2.55 s -> 0.16 s
     +0xb2 [ld a1,72(s3)]  ... 1.81 s -> 0.22 s
     +0xd8 [lbu]           ... 1.07 s -> 0.28 s
     the final [Qed]       .. 18.91 s -> 15.45 s

   and it COSTS, at the three sites that hand a leaf a premise spelled with
   [!!!] where the leaf's statement says [rget], and which therefore used to
   bridge for free by delta:

     +0xa6 [beq] taken ([Hfull])   ... 2.50 s -> 4.81 s
     +0xa6 [beq] fall  ([Hfull])   ... 2.53 s -> 4.83 s
     +0xca [sw a4,540(s1)] ([Hnwaddr3]) 0.38 s -> 1.14 s

   Net -6.1 s, and no proof-script change is needed for it.  THE THREE
   REGRESSIONS ARE RECOVERABLE the way ProofVirtioDiskInit recovered its
   thirteen: restate the premise in the [rget] spelling with [rget_ne]
   (HartTp.v) just before the [iApply] -- [Hfull] at the two [beq]s and
   [Hnwaddr3] at the [sw] -- which should take the file to ~86 s.  Left as a
   follow-up because it is three hand edits, not a mechanical sweep.

   [reg_neq] / [upd_eq] / [upd_ne] / [peel] / [rgall] all keep working with
   the three sealed: they are lemma-driven, not conversion-driven, and
   [rgall]'s [rget_ne] is the only [rget] this file names.

   DONE 2026-08-13: the three regressions above are now restated in the
   [rget] spelling ([Hfullr] at both [beq]s, [Hnwaddr3r] at the [sw]) right
   before their [iApply]; each site is back under 0.4 s.  Separately,
   [pw_chslot]'s two deep re-bundles now go through the constructor lemma
   [pw_chslot_mk] (small context) instead of an in-place [iSplitR; [done|]]
   in the whole-function context.  Isolated [-async-proofs off], min of 2
   interleaved runs: baseline 91.63 s -> fixed 75.34 s. *)
Local Strategy opaque [rget].
Local Strategy opaque [tp_pin].
Local Strategy opaque [rf_upd].

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

(* the [beqz s2] that decides between "return -1" and "return the partial
   count": a strictly positive literal is not x0. *)
Lemma pw_moi_nz0 (z : Z) : (0 < z < 18446744073709551616)%Z ->
  eq_vec (mword_of_int z : mword 64) zero_reg = false.
Proof.
  intro Hz. apply eq_vec_false_iff.
  intro Hc. apply (f_equal bv_unsigned) in Hc.
  rewrite moi64_unsigned in Hc.
  assert (Hzz : bv_unsigned (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hzz in Hc.
  assert (Hb : bv_wrap 64 z = z)
    by (apply bvw64_small; change (2^64)%Z with 18446744073709551616%Z; lia).
  rewrite Hb in Hc. lia.
Qed.

(* ---- the 14-slot frame geometry ---- *)
Lemma pw_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 14%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 14%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_assoc H. reflexivity.
Qed.

(* A FIELD OF A KALLOC'D PAGE IS NEVER NULL -- sleep_prepare's
   [panic("sleep_prepare: zero chan")] arm, refuted.  The page's own base is
   >= [kmem_lo], and [page_in_range_addr_is_kdata] carries that to every
   in-page offset. *)
Lemma pw_pfield_nz (p : mword 64) (k : nat) :
  page_valid p -> (k < 4096)%nat ->
  eq_vec (pa_add p k : mword 64) (zero_reg : mword 64) = false.
Proof.
  intros Hv Hk.
  pose proof (page_in_range_addr_is_kdata p k Hv Hk) as Hkd.
  apply eq_vec_false_iff. intro Hc.
  unfold addr_is_kdata in Hkd. rewrite Hc in Hkd.
  assert (Hz : uint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hz in Hkd. unfold text_end in Hkd. lia.
Qed.

Lemma pw_pnwrite_pa (p : mword 64) : a_pnwrite p = pa_add p 540%nat.
Proof.
  unfold a_pnwrite, poff_of, pa_add, add_vec_int.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma pw_pnwrite_nz (p : mword 64) :
  page_valid p -> eq_vec (a_pnwrite p : mword 64) (zero_reg : mword 64) = false.
Proof. intro Hv. rewrite pw_pnwrite_pa. apply pw_pfield_nz; [exact Hv | lia]. Qed.

Lemma pw_ch_addr (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3999 : mword 12)) = pa_add (pa_stk X 13%nat) 7%nat.
Proof.
  unfold pa_add, pa_stk, add_vec_int. rewrite add_vec_assoc.
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* copyin CONSUMES [kalloc_env] and hands nothing back, and the loop calls it
     once per byte -- so the bundle has to be duplicable.  At [on = None] every
     conjunct is persistent ([is_lock], [kalloc_sealed]), which is
     exactly why the sealed form is the one the copy chain takes. *)
  (* [kalloc_env _ None _] is persistent: KvmSpec.kalloc_env_None_persistent. *)

  (* the seven prologue-saved slots (ra, s0..s5), holding the caller's values *)
  Definition pw_frame7 (m : regfile) (sp0 : mword 64) : iProp Σ :=
    (pa_stk sp0 1%nat ↦₈[KT1] (m !!! Regidx Rra) ∗
     pa_stk sp0 2%nat ↦₈[KT1] (m !!! Regidx Rs0) ∗
     pa_stk sp0 3%nat ↦₈[KT1] (m !!! Regidx Rs1) ∗
     pa_stk sp0 4%nat ↦₈[KT1] (m !!! Regidx Rs2) ∗
     pa_stk sp0 5%nat ↦₈[KT1] (m !!! Regidx Rs3) ∗
     pa_stk sp0 6%nat ↦₈[KT1] (m !!! Regidx Rs4) ∗
     pa_stk sp0 7%nat ↦₈[KT1] (m !!! Regidx Rs5))%I.

  (* the five SHRINK-WRAPPED slots (s6..s10), saved only on the copy path *)
  Definition pw_frame5 (m : regfile) (sp0 : mword 64) : iProp Σ :=
    (pa_stk sp0 8%nat  ↦₈[KT1] (m !!! Regidx Rs6) ∗
     pa_stk sp0 9%nat  ↦₈[KT1] (m !!! Regidx Rs7) ∗
     pa_stk sp0 10%nat ↦₈[KT1] (m !!! Regidx Rs8) ∗
     pa_stk sp0 11%nat ↦₈[KT1] (m !!! Regidx Rs9) ∗
     pa_stk sp0 12%nat ↦₈[KT1] (m !!! Regidx Rs10))%I.

  (* slot 13 as BYTES (the 1-byte local [ch] is its byte 7) plus the untouched
     slot 14.  The 8-alignment of slot 13 rides along: a byte run does not
     carry it and the [c.addi16sp] pop needs the slot to be a word again. *)
  Definition pw_chslot (sp0 : mword 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr (pa_stk sp0 13%nat)) 8 = true⌝ ∗
     bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 13%nat) 8 ∗
     (∃ v : bv 64, pa_stk sp0 14%nat ↦₈[KT1] v))%I.

  (* Constructor for [pw_chslot], proved HERE where the context is just [sp0]
     -- so the [done] on the pure alignment conjunct runs in a 1-hypothesis
     context instead of the whole-function one.  The two re-bundle sites deep
     in [wp_pipewrite] call this instead of unfolding [pw_chslot] in place. *)
  Lemma pw_chslot_mk (sp0 : mword 64) :
    is_aligned_paddr (Physaddr (pa_stk sp0 13%nat)) 8 = true ->
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 13%nat) 8 -∗
    (∃ v : bv 64, pa_stk sp0 14%nat ↦₈[KT1] v) -∗
    pw_chslot sp0.
  Proof.
    intros Hal. rewrite /pw_chslot. iIntros "Hb Hv". iSplitR; [done|]. iFrame.
  Qed.

  Lemma pw_slot_eq (sp0 : mword 64) (k K : nat) :
    (7 + k)%nat = K -> pa_stk (pa_stk sp0 7%nat) k = pa_stk sp0 K.
  Proof. intro H. rewrite pa_stk_assoc H. reflexivity. Qed.

  Lemma pw_hi_split (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 7%nat) 7%nat ⊢
      (∃ w8 w9 w10 w11 w12 : bv 64,
         pa_stk sp0 8%nat ↦₈[KT1] w8 ∗ pa_stk sp0 9%nat ↦₈[KT1] w9 ∗ pa_stk sp0 10%nat ↦₈[KT1] w10 ∗
         pa_stk sp0 11%nat ↦₈[KT1] w11 ∗ pa_stk sp0 12%nat ↦₈[KT1] w12) ∗ pw_chslot sp0.
  Proof.
    assert (E8  : pa_stk (pa_stk sp0 7%nat) 1%nat = pa_stk sp0 8%nat)  by (apply pw_slot_eq; reflexivity).
    assert (E9  : pa_stk (pa_stk sp0 7%nat) 2%nat = pa_stk sp0 9%nat)  by (apply pw_slot_eq; reflexivity).
    assert (E10 : pa_stk (pa_stk sp0 7%nat) 3%nat = pa_stk sp0 10%nat) by (apply pw_slot_eq; reflexivity).
    assert (E11 : pa_stk (pa_stk sp0 7%nat) 4%nat = pa_stk sp0 11%nat) by (apply pw_slot_eq; reflexivity).
    assert (E12 : pa_stk (pa_stk sp0 7%nat) 5%nat = pa_stk sp0 12%nat) by (apply pw_slot_eq; reflexivity).
    assert (E13 : pa_stk (pa_stk sp0 7%nat) 6%nat = pa_stk sp0 13%nat) by (apply pw_slot_eq; reflexivity).
    assert (E14 : pa_stk (pa_stk sp0 7%nat) 7%nat = pa_stk sp0 14%nat) by (apply pw_slot_eq; reflexivity).
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & _)".
    iDestruct "A1" as (w8) "H8".   iEval (rewrite E8) in "H8".
    iDestruct "A2" as (w9) "H9".   iEval (rewrite E9) in "H9".
    iDestruct "A3" as (w10) "H10". iEval (rewrite E10) in "H10".
    iDestruct "A4" as (w11) "H11". iEval (rewrite E11) in "H11".
    iDestruct "A5" as (w12) "H12". iEval (rewrite E12) in "H12".
    iDestruct "A6" as (w13) "H13". iEval (rewrite E13) in "H13".
    iDestruct "A7" as (w14) "H14". iEval (rewrite E14) in "H14".
    iDestruct (slot_bytes_own (KTR := KT1) with "H13") as "[%Hal Hb13]".
    iSplitL "H8 H9 H10 H11 H12".
    { iExists w8, w9, w10, w11, w12. iFrame "H8 H9 H10 H11 H12". }
    rewrite /pw_chslot. iSplitR; [done|]. iFrame "Hb13". iExists w14. iFrame "H14".
  Qed.

  Lemma pw_hi_intro (sp0 : mword 64) (w8 w9 w10 w11 w12 : bv 64) :
    pa_stk sp0 8%nat ↦₈[KT1] w8 -∗ pa_stk sp0 9%nat ↦₈[KT1] w9 -∗ pa_stk sp0 10%nat ↦₈[KT1] w10 -∗
    pa_stk sp0 11%nat ↦₈[KT1] w11 -∗ pa_stk sp0 12%nat ↦₈[KT1] w12 -∗
    pw_chslot sp0 -∗ stack_own (KTR := KT1) (pa_stk sp0 7%nat) 7%nat.
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
    iDestruct (bytes_own_slot (KTR := KT1) (pa_stk sp0 13%nat) Hal with "Hb13") as (w13) "H13".
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
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

  (* [pw_res_intro] with the five fields the pipewrite loop body never reads
     between the initial [iDestruct] and reassembly ([Hnm], [Hwo], the two
     [pipe_endstate]s, [Hslack]) pre-combined into one hypothesis.  The
     whole-function proof [iCombine]s them into "Hrest" right after
     destructuring [Hres], so every instruction step in between carries FIVE
     pipe hypotheses (Hrest, Hnr, Hnw, Hro, Hdat) instead of nine -- each
     [iApply]'s own environment bookkeeping is |Δ|-proportional (see
     optimization.md's account of ProofNamex's [iApply] cost), so this is
     five fewer entries at EVERY step of a ~700-line stretch, not just at the
     point of reassembly. *)
  Lemma pw_res_intro_rest (γp : pipe_names) (pi : mword 64)
      (nr nw ro wo : mword 32) (vname : mword 64) (bs : list (bv 8)) :
    pipe_count_ok nr nw -> length bs = PIPESIZE ->
    (lock_name_field pi ↦₈ vname ∗ a_popen pi true ↦₄ wo ∗
     pipe_endstate γp false ro ∗ pipe_endstate γp true wo ∗ pipe_slack pi) -∗
    a_pnread pi ↦₄ nr -∗ a_pnwrite pi ↦₄ nw -∗
    a_popen pi false ↦₄ ro -∗
    pipe_data pi bs -∗ pipe_res γp pi.
  Proof.
    intros Hc Hl. iIntros "(Hnm & Hwo & Hst0 & Hst1 & Hslack) Hnr Hnw Hro Hdat".
    iApply (pw_res_intro γp pi nr nw ro wo vname bs Hc Hl
              with "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack").
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.

  (* +0x58: the common epilogue (mv a0,s2; reload ra/s0..s5; pop; ret). *)
  Definition pw_epi `{GEN : GenId} (CID0 : CPU) (γf : gname)  (γs : list gname) (j : nat)
      (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (P' : uptd),
       ⌜pw_base_regs m M (pa_stk sp0 14%nat)⌝ -∗
       ⌜pipe_rw_ret n (M !!! Regidx Rs2)⌝ -∗
       ⌜uptd_ext (pv_upt V) P'⌝ -∗
       pw_frame7 m sp0 -∗
       stack_own (KTR := KT1) (pa_stk sp0 7%nat) 7%nat -∗
       sie_cap_gpr KT1 M (av - 14)%nat true (proc_addr j) -∗
       cpu_own 0%nat eb (proc_addr j) true ∅ -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0x58) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv_core (proc_addr j) pid (upd_upt V P') -∗
       WP (Loop : expr riscv_lang)))%I.

  (* +0x108: wakeup(&pi->nread); release(&pi->lock); jump to the epilogue.  Three
     paths land here: the n <= 0 arm, the loop exit and the copyin failure. *)
  Definition pw_tail `{GEN : GenId} (CID0 : CPU) (γf : gname)  (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (lks : gset string)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (P' : uptd),
       ⌜pw_base_regs m M (pa_stk sp0 14%nat)⌝ -∗
       ⌜M !!! Regidx Rs1 = pi⌝ -∗
       ⌜pipe_rw_ret n (M !!! Regidx Rs2)⌝ -∗
       ⌜uptd_ext (pv_upt V) P'⌝ -∗
       pw_frame7 m sp0 -∗
       stack_own (KTR := KT1) (pa_stk sp0 7%nat) 7%nat -∗
       sie_cap_gpr KT1 M (trap_res true + (av - 14))%nat false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) false ({["pipe"]} ∪ lks) -∗
       arm_pay KT1 0%nat eb (proc_addr j) -∗
       locked γl cpu_id -∗
       pipe_res γp pi -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0x108) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv_core (proc_addr j) pid (upd_upt V P') -∗
       WP (Loop : expr riscv_lang)))%I.

  (* +0x46: release(&pi->lock); i := -1; reload s6..s10; fall into the
     epilogue.  Reached when readopen == 0 or the process was killed. *)
  Definition pw_minus1 `{GEN : GenId} (CID0 : CPU) (γf : gname)  (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (lks : gset string)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (P' : uptd),
       ⌜pw_min_regs m M (pa_stk sp0 14%nat) pi⌝ -∗
       ⌜uptd_ext (pv_upt V) P'⌝ -∗
       pw_frame7 m sp0 -∗
       pw_frame5 m sp0 -∗
       pw_chslot sp0 -∗
       sie_cap_gpr KT1 M (trap_res true + (av - 14))%nat false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) false ({["pipe"]} ∪ lks) -∗
       arm_pay KT1 0%nat eb (proc_addr j) -∗
       locked γl cpu_id -∗
       pipe_res γp pi -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0x46) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv_core (proc_addr j) pid (upd_upt V P') -∗
       WP (Loop : expr riscv_lang)))%I.

  (* exactly ONE of the two is taken, so they are offered as a conjunction and
     SHARE the epilogue closure. *)
  Definition pw_exits `{GEN : GenId} (CID0 : CPU) (γf : gname) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (lks : gset string)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi : mword 64) : iProp Σ :=
    (pw_tail CID0 γf γs j γl γp w q m av eb lks pid V n sp0 pi
     ∧ pw_minus1 CID0 γf γs j γl γp w q m av eb lks pid V n sp0 pi)%I.

  (* +0x8c: the loop BODY, entered with 0 <= i < n. *)
  Definition pw_loop `{GEN : GenId} (CID0 : CPU) (γa γf : gname) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (lks : gset string)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi addr : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (i : Z) (M : regfile) (Pc : uptd),
       ⌜(0 <= i < n)%Z⌝ -∗
       ⌜uptd_ext (pv_upt V) Pc⌝ -∗
       ⌜pw_loop_regs m M (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i⌝ -∗
       pw_frame7 m sp0 -∗
       pw_frame5 m sp0 -∗
       pw_chslot sp0 -∗
       sie_cap_gpr KT1 M (trap_res true + (av - 14))%nat false (proc_addr j) -∗
       cpu_own 1%nat eb (proc_addr j) false ({["pipe"]} ∪ lks) -∗
       arm_pay KT1 0%nat eb (proc_addr j) -∗
       locked γl cpu_id -∗
       pipe_res γp pi -∗
       pc_is (mword_of_int (KernelSyms.pipewrite + 0x8c) : mword 64) -∗
       pipe_ref γp w q -∗
       proc_priv_core (proc_addr j) pid (upd_upt V Pc) -∗
       kalloc_env γa None -∗
       pw_exits CID0 γf γs j γl γp w q m av eb lks pid V n sp0 pi -∗
       WP (Loop : expr riscv_lang)))%I.

  (* MEASURED AND REJECTED (2026-08-13): routing the +0xde back edge's [▷]
     strip through a two-hypothesis lemma [(P -∗ Q) -∗ ▷ P -∗ ▷ Q], to spare
     [iNext] its context-wide [IntoLaterN] search, DOES NOT WORK HERE.  The
     back edge does not merely need the later off [IH]: [iApply
     pw_guard_step ... with "... IH"] wants IH *and* [HEX] and the goal all
     un-latered together, so the [iRevert "IH"] the lemma needs leaves IH in
     the way of its own re-introduction ("iIntro: IH not fresh").  The three
     sites the file header names keep their [iNext] for exactly this reason.
     Do not re-attempt without a lemma that strips both IH and HEX; the
     [bi.later_intro] swap at every OTHER instruction step is the part of
     this idea that pays, and it is landed. *)

End PwConts.

(* ===================================================================== *)
(*  The shrink-wrapped reload block (s6..s10), shared by the three arms    *)
(*  that saved them: +0x4e, +0xfe, +0xe4 and +0xf2.                              *)
(* ===================================================================== *)
Section PwRestore.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
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
    sie_cap_gpr KT1 M K b pme -∗ pc_is p0 -∗
    instr p0 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx Rs6, false, 8)) -∗
    instr p1 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx Rs7, false, 8)) -∗
    instr p2 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx Rs8, false, 8)) -∗
    instr p3 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx Rs9, false, 8)) -∗
    instr p4 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx Rs10, false, 8)) -∗
    pw_frame5 m sp0 -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ M' : regfile, ⌜ pw_restored m M M' ⌝ -∗
        sie_cap_gpr KT1 M' K b pme -∗ pc_is p5 -∗ pw_frame5 m sp0 -∗
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
              with "Hcg Hpc Hi0 F8").
    iIntros (CIDr1 Hsr1) "Hcg Hpc F8". rgall.
    iEval (rewrite Hsp Hb8) in "F8".
    pose (N1 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> M).
    change (<[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> M) with N1.
    iEval (rewrite E1) in "Hpc".
    assert (HspN1 : N1 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N1 upd_ne; [exact Hsp | reg_neq]).
    (* s7 *)
    iEval (rewrite -Hb9 -HspN1) in "F9".
    iApply (wp_cldsp_s_sconf p1 (mword_of_int 5 : mword 6) Rs7 N1 K (m !!! Regidx Rs7) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1 F9").
    iIntros (CIDr2 Hsr2) "Hcg Hpc F9". rgall.
    iEval (rewrite HspN1 Hb9) in "F9".
    pose (N2 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> N1).
    change (<[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> N1) with N2.
    iEval (rewrite E2) in "Hpc".
    assert (HspN2 : N2 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N2 upd_ne; [exact HspN1 | reg_neq]).
    (* s8 *)
    iEval (rewrite -Hb10 -HspN2) in "F10".
    iApply (wp_cldsp_s_sconf p2 (mword_of_int 4 : mword 6) Rs8 N2 K (m !!! Regidx Rs8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2 F10").
    iIntros (CIDr3 Hsr3) "Hcg Hpc F10". rgall.
    iEval (rewrite HspN2 Hb10) in "F10".
    pose (N3 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> N2).
    change (<[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> N2) with N3.
    iEval (rewrite E3) in "Hpc".
    assert (HspN3 : N3 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N3 upd_ne; [exact HspN2 | reg_neq]).
    (* s9 *)
    iEval (rewrite -Hb11 -HspN3) in "F11".
    iApply (wp_cldsp_s_sconf p3 (mword_of_int 3 : mword 6) Rs9 N3 K (m !!! Regidx Rs9) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3 F11").
    iIntros (CIDr4 Hsr4) "Hcg Hpc F11". rgall.
    iEval (rewrite HspN3 Hb11) in "F11".
    pose (N4 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> N3).
    change (<[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> N3) with N4.
    iEval (rewrite E4) in "Hpc".
    assert (HspN4 : N4 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
      by (rewrite /N4 upd_ne; [exact HspN3 | reg_neq]).
    (* s10 *)
    iEval (rewrite -Hb12 -HspN4) in "F12".
    iApply (wp_cldsp_s_sconf p4 (mword_of_int 2 : mword 6) Rs10 N4 K (m !!! Regidx Rs10) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4 F12").
    iIntros (CIDr5 Hsr5) "Hcg Hpc F12". rgall.
    iEval (rewrite HspN4 Hb12) in "F12".
    pose (N5 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10)]> N4).
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
(*  The loop GUARD at +0x88 ([bge s2,s4]).                                *)
(*  It is not part of the loop body: the first entry (+0x44) jumps PAST it *)
(*  and both back edges arrive AT it, so it takes the loop assertion as a  *)
(*  premise instead of being folded into the iLöb.                        *)
(* ===================================================================== *)
Section PwGuard.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma pw_stack7_of (m : regfile) (sp0 : mword 64) :
    pw_frame5 m sp0 -∗ pw_chslot sp0 -∗ stack_own (KTR := KT1) (pa_stk sp0 7%nat) 7%nat.
  Proof.
    iIntros "(F8 & F9 & F10 & F11 & F12) HCH".
    iApply (pw_hi_intro sp0 with "F8 F9 F10 F11 F12 HCH").
  Qed.

  Lemma pw_guard_step (CID0 : CPU) (γa γf : gname) (γs : list gname) (j : nat)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (lks : gset string)
      (pid : mword 32) (V : pprivate) (n : Z) (sp0 pi addr : mword 64)
      (i : Z) (M : regfile) (Pc : uptd) :
    (0 < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= i <= n)%Z ->
    (true = false \/ proc_addr j = zero_reg -> (CID : CPU) = CID0) ->
    uptd_ext (pv_upt V) Pc ->
    pw_loop_regs m M (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i ->
    kernel_text -∗
    pw_frame7 m sp0 -∗ pw_frame5 m sp0 -∗ pw_chslot sp0 -∗
    sie_cap_gpr KT1 M (trap_res true + (av - 14))%nat false (proc_addr j) -∗
    cpu_own 1%nat eb (proc_addr j) false ({["pipe"]} ∪ lks) -∗
    arm_pay KT1 0%nat eb (proc_addr j) -∗
    locked γl cpu_id -∗
    pipe_res γp pi -∗
    pc_is (mword_of_int (KernelSyms.pipewrite + 0x88) : mword 64) -∗
    pipe_ref γp w q -∗
    proc_priv_core (proc_addr j) pid (upd_upt V Pc) -∗
    kalloc_env γa None -∗
    pw_exits CID0 γf γs j γl γp w q m av eb lks pid V n sp0 pi -∗
    pw_loop CID0 γa γf γs j γl γp w q m av eb lks pid V n sp0 pi addr -∗
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
    iIntros "#Htext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv #Henv HEX HLP".
    destruct (Z.geb i n) eqn:Hgb.
    - (* ==== i >= n : the copy is done, restore s6..s10 and take the tail ==== *)
      assert (Hge : (n <= i)%Z).
      { assert (Hx := Hgb). rewrite Z.geb_leb in Hx. by apply Z.leb_le. }
      assert (Hgt : zopz0zKzJ_s (M !!! Regidx Rs2) (M !!! Regidx Rs4) = true)
        by exact Hcmp.
      assert (Hal : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x88) : mword 64)
                       (sign_extend' 64 (mword_of_int 118 : mword 13))) 0) ('b"0") = true)
        by (vm_compute; reflexivity).
      iApply (wp_bge_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x88)) (mword_of_int 118 : mword 13)
                Rs4 Rs2 M (trap_res true + (av - 14))%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hgt Hal with "Hcg Hpc []").
      { iApply (pwi_88 with "Htext"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjdc : add_vec (mword_of_int (KernelSyms.pipewrite + 0x88) : mword 64)
                       (sign_extend' 64 (mword_of_int 118 : mword 13))
                     = (mword_of_int (KernelSyms.pipewrite + 0xfe) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjdc) in "Hpc".
      assert (Ede : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xfe) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x100)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ee0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x100) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x102)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ee2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x102) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x104)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ee4 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x104) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x106)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Ee6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x106) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (pw_restore5 (proc_addr j) false (mword_of_int (KernelSyms.pipewrite + 0xfe)) (mword_of_int (KernelSyms.pipewrite + 0x100))
                (mword_of_int (KernelSyms.pipewrite + 0x102)) (mword_of_int (KernelSyms.pipewrite + 0x104)) (mword_of_int (KernelSyms.pipewrite + 0x106))
                (mword_of_int (KernelSyms.pipewrite + 0x108)) M m (trap_res true + (av - 14))%nat sp0
                Hsp Ede Ee0 Ee2 Ee4 Ee6
                with "Hcg Hpc [] [] [] [] [] HF5").
      { iApply (pwi_fe with "Htext"). }
      { iApply (pwi_100 with "Htext"). }
      { iApply (pwi_102 with "Htext"). }
      { iApply (pwi_104 with "Htext"). }
      { iApply (pwi_106 with "Htext"). }
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
      iApply ("TAIL" $! M' Pc with "[%] [%] [%] [%] HF7 [HF5 HCH] Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv").
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
      iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x88)) (mword_of_int 118 : mword 13)
                Rs4 Rs2 M (trap_res true + (av - 14))%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hgf with "Hcg Hpc []").
      { iApply (pwi_88 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x88) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x8c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp8c) in "Hpc".
      rewrite /pw_loop.
      iSpecialize ("HLP" $! CID with "[%]"); [wp_next_chain|].
      iApply ("HLP" $! i M Pc with "[%] [%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Henv HEX").
      + lia.
      + exact Hext.
      + exact Hregs.
  Qed.

End PwGuard.

(* ===================================================================== *)
(*  The whole-function proof.                                             *)
(* ===================================================================== *)
Module PipewriteProof (Myproc : MYPROC) (AcquireGen : ACQUIRE_GEN) (Killed : KILLED)
                      (Wakeup : WAKEUP) (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP)
                      (Copyin : COPYIN) (ReleaseGen : RELEASE_GEN) : PIPEWRITE.

Section ProofPipewrite.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
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

  Lemma wp_pipewrite_sconf (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool) (lks : gset string)
    : wp_pipewrite_sconf_body γa γf γs j γlp γl γp w q m av eb pid V n b lks.
  Proof.
    cbv beta delta [wp_pipewrite_sconf_body].
    intros pcE pj pi ret_tgt Hj Hjlp Hlen Ha2 Hnrange Hav Heb Hbelow. subst eb.
    (* every callee that wants "proc" (wakeup / killed / sleep_prepare /
       sleep) is reached with the held set still at [lks] (the entry set --
       see claude-notes/completed/lock-set.md's note on this function's
       region-crossing threading), so this one lift covers all of them. *)
    assert (Hbelowproc : locks_below lks "proc")
      by lkbelow.
    assert (Hav64 : (64 <= av)%nat) by (exact Hav).
    assert (H31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (H63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hcpune : eq_vec (zero_reg : mword 64) (mycpu_ret cid_word) = false)
      by (apply mycpu_ret_nonzero; apply tp_ok_cid).
    assert (Hn31 : (n < 2 ^ 31)%Z) by (destruct Hnrange as [_ HB]; exact HB).
    assert (Hn31L : (n < 2147483648)%Z) by (rewrite H31 in Hn31; exact Hn31).
    iIntros "Hcg Hown #Htext Hpc #Hpipe Href Hpriv #Henv #Hpinv Hcont".
    (* pipewrite's contract pins depth 0, so the held set is FORCED empty.
       Keep the equation rather than substituting it: the script still names
       [lks] in a dozen argument lists, and the interrupts-on arms hand back
       a [cpu_own] whose set is the literal [∅] the SIE seam reconstructs. *)
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    assert (Hbt : b = true) by (symmetry; exact Hbm).
    clear Hbm. subst b.
    iDestruct (is_pipe_valid with "Hpipe") as %Hpv.
    iPoseProof (is_pipe_openable with "Hpipe") as "#Hopen".
    iDestruct (proc_priv_core_sz_bound with "Hpriv") as %Hszb.
    (* ================================================================= *)
    (* EPI -- the common epilogue at +0x58.                              *)
    (* ================================================================= *)
    iAssert (pw_epi CID γf γs j γp w q m av true pid V n sp0) with "[Hcont]" as "EPI".
    { rewrite /pw_epi. iIntros (CIDep Hsep M P') "%Hbr %Hrw %Hext (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7) Hhi Hcg Hown Hpc Href Hpriv".
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
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x58)) Ra0 Rs2 M (av - 14)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (pwi_58 with "Htext"). }
      iIntros (CIDp6 Hsp6) "Hcg Hpc". rgall.
      pose (E1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs2))]> M).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs2))]> M) with E1.
      assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5a) in "Hpc".
      assert (HspE1 : E1 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
      (* +0x5a c.ldsp ra,104(sp) *)
      iEval (rewrite -Hb1 -HspE1) in "Hc1".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x5a)) (mword_of_int 13 : mword 6) Rra
                E1 (av - 14)%nat (m !!! Regidx Rra) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hc1").
      { iApply (pwi_5a with "Htext"). }
      iIntros (CIDp7 Hsp7) "Hcg Hpc Hc1". rgall.
      iEval (rewrite HspE1 Hb1) in "Hc1".
      pose (E2 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E1).
      change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E1) with E2.
      assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5c) in "Hpc".
      assert (HspE2 : E2 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E2 upd_ne; [exact HspE1 | reg_neq]).
      (* +0x5c c.ldsp s0,96(sp) *)
      iEval (rewrite -Hb2 -HspE2) in "Hc2".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x5c)) (mword_of_int 12 : mword 6) Rs0
                E2 (av - 14)%nat (m !!! Regidx Rs0) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hc2").
      { iApply (pwi_5c with "Htext"). }
      iIntros (CIDp8 Hsp8) "Hcg Hpc Hc2". rgall.
      iEval (rewrite HspE2 Hb2) in "Hc2".
      pose (E3 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E2).
      change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E2) with E3.
      assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5e) in "Hpc".
      assert (HspE3 : E3 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E3 upd_ne; [exact HspE2 | reg_neq]).
      (* +0x5e c.ldsp s1,88(sp) *)
      iEval (rewrite -Hb3 -HspE3) in "Hc3".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x5e)) (mword_of_int 11 : mword 6) Rs1
                E3 (av - 14)%nat (m !!! Regidx Rs1) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hc3").
      { iApply (pwi_5e with "Htext"). }
      iIntros (CIDp9 Hsp9) "Hcg Hpc Hc3". rgall.
      iEval (rewrite HspE3 Hb3) in "Hc3".
      pose (E4 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> E3).
      change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> E3) with E4.
      assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp60) in "Hpc".
      assert (HspE4 : E4 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E4 upd_ne; [exact HspE3 | reg_neq]).
      (* +0x60 c.ldsp s2,80(sp) *)
      iEval (rewrite -Hb4 -HspE4) in "Hc4".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x60)) (mword_of_int 10 : mword 6) Rs2
                E4 (av - 14)%nat (m !!! Regidx Rs2) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hc4").
      { iApply (pwi_60 with "Htext"). }
      iIntros (CIDp10 Hsp10) "Hcg Hpc Hc4". rgall.
      iEval (rewrite HspE4 Hb4) in "Hc4".
      pose (E5 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> E4).
      change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> E4) with E5.
      assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp62) in "Hpc".
      assert (HspE5 : E5 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E5 upd_ne; [exact HspE4 | reg_neq]).
      (* +0x62 c.ldsp s3,72(sp) *)
      iEval (rewrite -Hb5 -HspE5) in "Hc5".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x62)) (mword_of_int 9 : mword 6) Rs3
                E5 (av - 14)%nat (m !!! Regidx Rs3) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hc5").
      { iApply (pwi_62 with "Htext"). }
      iIntros (CIDp11 Hsp11) "Hcg Hpc Hc5". rgall.
      iEval (rewrite HspE5 Hb5) in "Hc5".
      pose (E6 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> E5).
      change (<[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> E5) with E6.
      assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp64) in "Hpc".
      assert (HspE6 : E6 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E6 upd_ne; [exact HspE5 | reg_neq]).
      (* +0x64 c.ldsp s4,64(sp) *)
      iEval (rewrite -Hb6 -HspE6) in "Hc6".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x64)) (mword_of_int 8 : mword 6) Rs4
                E6 (av - 14)%nat (m !!! Regidx Rs4) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hc6").
      { iApply (pwi_64 with "Htext"). }
      iIntros (CIDp12 Hsp12) "Hcg Hpc Hc6". rgall.
      iEval (rewrite HspE6 Hb6) in "Hc6".
      pose (E7 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> E6).
      change (<[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> E6) with E7.
      assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp66) in "Hpc".
      assert (HspE7 : E7 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E7 upd_ne; [exact HspE6 | reg_neq]).
      (* +0x66 c.ldsp s5,56(sp) *)
      iEval (rewrite -Hb7 -HspE7) in "Hc7".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x66)) (mword_of_int 7 : mword 6) Rs5
                E7 (av - 14)%nat (m !!! Regidx Rs5) true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hc7").
      { iApply (pwi_66 with "Htext"). }
      iIntros (CIDp13 Hsp13) "Hcg Hpc Hc7". rgall.
      iEval (rewrite HspE7 Hb7) in "Hc7".
      pose (E8 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> E7).
      change (<[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> E7) with E8.
      assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp68) in "Hpc".
      assert (HspE8 : E8 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
        by (rewrite /E8 upd_ne; [exact HspE7 | reg_neq]).
      (* +0x68 c.addi16sp sp,112 -- the frame trade back *)
      iAssert (stack_own (KTR := KT1) sp0 14%nat) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hhi]" as "Hframe".
      { iApply (stack_own_split_2 (KTR := KT1) sp0 7%nat 14%nat ltac:(lia)). iSplitR "Hhi"; [| iExact "Hhi"].
        rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
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
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x68)) (mword_of_int 7 : mword 6)
                E8 (av - 14)%nat 14%nat true Hpop with "Hcg Hpc [] Hframe").
      { iApply (pwi_68 with "Htext"). }
      iIntros (CIDp14 Hsp14) "Hcg Hpc". rgall.
      assert (Hnk : ((av - 14) + 14)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      pose (E9 := <[Regidx csp_rs1 := regval_into_reg
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
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x6a)) Rra E9 av true ltac:(nz)
                with "Hcg Hpc []").
      { iApply (pwi_6a with "Htext"). }
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
      iEval (rewrite Hlkempty) in "Hcont".
      iApply ("Hcont" $! E9 P' with "[%] [%] [%] Hcg Hown Hpc Href Hpriv").
      - exact HcsE9.
      - exact Hext.
      - rewrite Ha0E9. exact Hrw. }
    (* ================================================================= *)
    (* EXITS -- the +0x108 tail and the +0x46 (-1) arm, CONJOINED: exactly *)
    (* one of them is taken, so they must SHARE the epilogue closure.     *)
    (* ================================================================= *)
    iAssert (pw_exits CID γf γs j γl γp w q m av true lks pid V n sp0 pi) with "[EPI]" as "EXITS".
    { rewrite /pw_exits. iSplit.
      - (* ---------------- +0x108: wakeup(&pi->nread); release ---------------- *)
        rewrite /pw_tail. iIntros (CIDtl Hstl).
        iIntros (M P') "%Hbr %Hs1M %Hrw %Hext HF7 Hhi Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x108)) Ra0 Rs1
                  (mword_of_int 536 : mword 12) M (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (pwi_108 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        pose (T1 := <[Regidx Ra0 := regval_into_reg
            (add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> M).
        change (<[Regidx Ra0 := regval_into_reg
            (add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> M) with T1.
        assert (Hppea : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x108) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x10c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppea) in "Hpc".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x10c)) Rra (mword_of_int 2087120 : mword 21)
                  T1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (pwi_10c with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        pose (T2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x10c) : mword 64) 4)]> T1).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x10c) : mword 64) 4)]> T1) with T2.
        assert (Hjwk : add_vec (mword_of_int (KernelSyms.pipewrite + 0x10c) : mword 64) (sign_extend' 64 (mword_of_int 2087120 : mword 21))
                       = mword_of_int KernelSyms.wakeup) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjwk) in "Hpc".
        destruct Hbr as (Hsp & B6 & B7 & B8 & B9 & B10 & B11).
        (* every wakeup premise pre-established by NAME (optimization.md) *)
        assert (HwK : (18 <= trap_res true + (av - 14))%nat) by lia.
        assert (HwdomW : forall r : regidx, r ∈ dom (rf_to_gmap T2)) by (intro r; apply rf_to_gmap_dom).
        assert (Hwlvl : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
        iApply (Wakeup.wp_wakeup_sconf T2 γs (proc_addr j) 1%nat (trap_res true + (av - 14))%nat true false
                  ({["pipe"]} ∪ lks)
                  HwK HwdomW Hlen Hwlvl ltac:(lkbelow)
                  with "Hcg Hown Htext Hpc Hpinv").
        all: try lkbelow.
        iApply wp_next_off_intro. iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hown Htext2 Hpc". rgall.
        assert (HraT2 : T2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x10c) : mword 64) 4)
          by (rewrite /T2; apply upd_eq).
        iEval (rewrite HraT2) in "Hpc".
        assert (Hppee : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x10c) : mword 64) 4)
                        = (mword_of_int (KernelSyms.pipewrite + 0x110) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppee) in "Hpc".
        assert (HcsMT2 : callee_saved M T2).
        { rewrite /T2 /T1. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
        assert (HcsMMw : callee_saved M Mw) by (apply (callee_saved_trans M T2 Mw HcsMT2 Hwcs)).
        assert (Hs1Mw : Mw !!! Regidx Rs1 = pi).
        { rewrite (callee_saved_lookup HcsMMw (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1M. }
        (* +0x110 c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x110)) Ra0 Rs1 Mw (trap_res true + (av - 14))%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (pwi_110 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        pose (T3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw) with T3.
        assert (Hppf0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x110) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x112)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppf0) in "Hpc".
        (* +0x112 jal release *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x112)) Rra (mword_of_int 2082220 : mword 21)
                  T3 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (pwi_112 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        pose (T4 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x112) : mword 64) 4)]> T3).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x112) : mword 64) 4)]> T3) with T4.
        assert (Hjrl : add_vec (mword_of_int (KernelSyms.pipewrite + 0x112) : mword 64) (sign_extend' 64 (mword_of_int 2082220 : mword 21))
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
        iApply (ReleaseGen.wp_release_gen_sconf KT1 γl pi "pipe" (pipe_res γp pi) (pipe_dead γl γp) emp%I
                  T4 0%nat true (proc_addr j) (av - 14)%nat ({["pipe"]} ∪ lks) HlkaT4 HavR
                  ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                  with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay").
        { iApply lock_finisher_close. }
        iIntros (CIDrr Hsrr mr) "_ Hcg Hpc %Hcsr Hown". rgall.
        assert (HraT4 : T4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x112) : mword 64) 4)
          by (rewrite /T4; apply upd_eq).
        iEval (rewrite HraT4) in "Hpc".
        assert (Hppf4 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x112) : mword 64) 4)
                        = (mword_of_int (KernelSyms.pipewrite + 0x116) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppf4) in "Hpc".
        (* +0x116 c.j -> the epilogue *)
        assert (HcsMwT4 : callee_saved Mw T4).
        { rewrite /T4 /T3. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
        assert (HcsMmr : callee_saved M mr).
        { apply (callee_saved_trans M Mw mr HcsMMw).
          apply (callee_saved_trans Mw T4 mr HcsMwT4 Hcsr). }
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x116))
                  (sign_extend' 21 (concat_vec (mword_of_int 1953 : mword 11) ('b"0")))
                  mr (av - 14)%nat true ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (pwi_116 with "Htext"). }
        iIntros (CIDp16 Hsp16). iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
        assert (Hjep : add_vec (mword_of_int (KernelSyms.pipewrite + 0x116) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1953 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.pipewrite + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjep) in "Hpc".
        rewrite /pw_epi.
        (* the pipe lock's release left [({[rank "pipe"]} ∪ lks) ∖ {[rank
           "pipe"]}]; [lks = ∅] at depth 0 makes that the empty set [pw_epi]'s
           fixed [∅] binder names. *)
        iEval (rewrite Hlkempty locks_union_empty locks_self_del) in "Hown".
        iSpecialize ("EPI" $! CIDp16 with "[%]"); [wp_next_chain|].
        iApply ("EPI" $! mr P' with "[%] [%] [%] HF7 Hhi Hcg Hown Hpc Href Hpriv").
        + apply (pw_base_regs_cs m M mr (pa_stk sp0 14%nat) HcsMmr).
          unfold pw_base_regs. split_and!; assumption.
        + rewrite (callee_saved_lookup HcsMmr (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact Hrw.
        + exact Hext.
      - (* ---------------- +0x46: release; i := -1; reload s6..s10 ---------------- *)
        rewrite /pw_minus1. iIntros (CIDmn Hsmn).
        iIntros (M P') "%Hmr %Hext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv".
        destruct Hmr as (Hsp & Hs1M & Hs11M).
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x46)) Ra0 Rs1 M (trap_res true + (av - 14))%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (pwi_46 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        pose (Q1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M) with Q1.
        assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp48) in "Hpc".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x48)) Rra (mword_of_int 2082422 : mword 21)
                  Q1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (pwi_48 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        pose (Q2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) 4)]> Q1).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) 4)]> Q1) with Q2.
        assert (Hjrl : add_vec (mword_of_int (KernelSyms.pipewrite + 0x48) : mword 64) (sign_extend' 64 (mword_of_int 2082422 : mword 21))
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
        iApply (ReleaseGen.wp_release_gen_sconf KT1 γl pi "pipe" (pipe_res γp pi) (pipe_dead γl γp) emp%I
                  Q2 0%nat true (proc_addr j) (av - 14)%nat ({["pipe"]} ∪ lks) HlkaQ2 HavR
                  ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                  with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay").
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
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x4c)) Rs2 (mword_of_int 63 : mword 6)
                  (mword_of_int (-1) : mword 64) mr (av - 14)%nat true ltac:(nz) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (pwi_4c with "Htext"). }
        iIntros (CIDp17 Hsp17) "Hcg Hpc". rgall.
        pose (Q3 := <[Regidx Rs2 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr).
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
        assert (E50 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E52 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E54 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E56 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
        assert (E58 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
        iApply (pw_restore5 (proc_addr j) true (mword_of_int (KernelSyms.pipewrite + 0x4e)) (mword_of_int (KernelSyms.pipewrite + 0x50))
                  (mword_of_int (KernelSyms.pipewrite + 0x52)) (mword_of_int (KernelSyms.pipewrite + 0x54)) (mword_of_int (KernelSyms.pipewrite + 0x56))
                  (mword_of_int (KernelSyms.pipewrite + 0x58)) Q3 m (av - 14)%nat sp0
                  HspQ3 E50 E52 E54 E56 E58
                  with "Hcg Hpc [] [] [] [] [] HF5").
        { iApply (pwi_4e with "Htext"). }
        { iApply (pwi_50 with "Htext"). }
        { iApply (pwi_52 with "Htext"). }
        { iApply (pwi_54 with "Htext"). }
        { iApply (pwi_56 with "Htext"). }
        iIntros (CIDrs Hsrs M') "%Hrst Hcg Hpc HF5".
        destruct Hrst as (R6 & R7 & R8 & R9 & R10 & Rrest).
        assert (Hsp' : M' !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
        { rewrite (Rrest csp_rs1 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact HspQ3. }
        assert (Hs11' : M' !!! Regidx Rs11 = m !!! Regidx Rs11).
        { rewrite (Rrest (mword_of_int 27) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Hs11Q3. }
        assert (Hs2' : M' !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)).
        { rewrite (Rrest (mword_of_int 18) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact Hs2Q3. }
        rewrite /pw_epi.
        (* the pipe lock's release left [({[rank "pipe"]} ∪ lks) ∖ {[rank
           "pipe"]}]; [lks = ∅] at depth 0 makes that the empty set [pw_epi]'s
           fixed [∅] binder names. *)
        iEval (rewrite Hlkempty locks_union_empty locks_self_del) in "Hown".
        iSpecialize ("EPI" $! CIDrs with "[%]"); [wp_next_chain|].
        iApply ("EPI" $! M' P' with "[%] [%] [%] HF7 [HF5 HCH] Hcg Hown Hpc Href Hpriv").
        + unfold pw_base_regs. split_and!; assumption.
        + rewrite Hs2'. by left.
        + exact Hext.
        + iApply (pw_stack7_of m sp0 with "HF5 HCH"). }
    (* ================================================================= *)
    (* PROLOGUE +0x00 .. +0x16: 14-slot frame, save ra/s0..s5, set s0/s1/s4/s5 *)
    (* ================================================================= *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 14%nat) by (apply pw_push_val).
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 57 : mword 6) m av 14%nat true ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (pwi_00 with "Htext"). }
    iIntros (CIDp18 Hsp18) "Hcg Hframe Hpc". rgall.
    iEval (rewrite Hspm) in "Hframe".
    pose (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))))]> m) with A0.
    assert (HspA0 : A0 !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
    { rewrite /A0 upd_eq. unfold regval_into_reg. rewrite Hpush Hspm. reflexivity. }
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* the seven low slots become the seven prologue cells *)
    iAssert (stack_own (KTR := KT1) sp0 7%nat ∗ stack_own (KTR := KT1) (pa_stk sp0 7%nat) 7%nat)%I with "[Hframe]" as "[Hlo Hhi]".
    { iApply (stack_own_split_1 (KTR := KT1) sp0 7%nat 14%nat ltac:(lia)). iExact "Hframe". }
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hlo".
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
    iEval (rewrite -Hb1 -HspA0) in "Hc1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x02)) (mword_of_int 13 : mword 6) Rra
              A0 (av - 14)%nat v1 true with "Hcg Hpc [] Hc1").
    { iApply (pwi_02 with "Htext"). }
    iIntros (CIDp19 Hsp19) "Hcg Hpc Hc1". rgall.
    iEval (rewrite HspA0 Hb1 HraA0) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,96(sp) *)
    iEval (rewrite -Hb2 -HspA0) in "Hc2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x04)) (mword_of_int 12 : mword 6) Rs0
              A0 (av - 14)%nat v2 true with "Hcg Hpc [] Hc2").
    { iApply (pwi_04 with "Htext"). }
    iIntros (CIDp20 Hsp20) "Hcg Hpc Hc2". rgall.
    iEval (rewrite HspA0 Hb2 Hs0A0) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,88(sp) *)
    iEval (rewrite -Hb3 -HspA0) in "Hc3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x06)) (mword_of_int 11 : mword 6) Rs1
              A0 (av - 14)%nat v3 true with "Hcg Hpc [] Hc3").
    { iApply (pwi_06 with "Htext"). }
    iIntros (CIDp21 Hsp21) "Hcg Hpc Hc3". rgall.
    iEval (rewrite HspA0 Hb3 Hs1A0) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,80(sp) *)
    iEval (rewrite -Hb4 -HspA0) in "Hc4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x08)) (mword_of_int 10 : mword 6) Rs2
              A0 (av - 14)%nat v4 true with "Hcg Hpc [] Hc4").
    { iApply (pwi_08 with "Htext"). }
    iIntros (CIDp22 Hsp22) "Hcg Hpc Hc4". rgall.
    iEval (rewrite HspA0 Hb4 Hs2A0) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,72(sp) *)
    iEval (rewrite -Hb5 -HspA0) in "Hc5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x0a)) (mword_of_int 9 : mword 6) Rs3
              A0 (av - 14)%nat v5 true with "Hcg Hpc [] Hc5").
    { iApply (pwi_0a with "Htext"). }
    iIntros (CIDp23 Hsp23) "Hcg Hpc Hc5". rgall.
    iEval (rewrite HspA0 Hb5 Hs3A0) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp s4,64(sp) *)
    iEval (rewrite -Hb6 -HspA0) in "Hc6".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x0c)) (mword_of_int 8 : mword 6) Rs4
              A0 (av - 14)%nat v6 true with "Hcg Hpc [] Hc6").
    { iApply (pwi_0c with "Htext"). }
    iIntros (CIDp24 Hsp24) "Hcg Hpc Hc6". rgall.
    iEval (rewrite HspA0 Hb6 Hs4A0) in "Hc6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp s5,56(sp) *)
    iEval (rewrite -Hb7 -HspA0) in "Hc7".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x0e)) (mword_of_int 7 : mword 6) Rs5
              A0 (av - 14)%nat v7 true with "Hcg Hpc [] Hc7").
    { iApply (pwi_0e with "Htext"). }
    iIntros (CIDp25 Hsp25) "Hcg Hpc Hc7". rgall.
    iEval (rewrite HspA0 Hb7 Hs5A0) in "Hc7".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iAssert (pw_frame7 m sp0) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7]" as "HF7".
    { rewrite /pw_frame7. iFrame "Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7". }
    (* +0x10 c.addi4spn s0,sp,112 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x10)) (Cregidx (mword_of_int 0))
              (mword_of_int 28 : mword 8) Rs0 A0 (av - 14)%nat true
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (pwi_10 with "Htext"). }
    iIntros (CIDp26 Hsp26) "Hcg Hpc". rgall.
    pose (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))))]> A0) with A1.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x12)) Rs1 Ra0 A1 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (pwi_12 with "Htext"). }
    iIntros (CIDp27 Hsp27) "Hcg Hpc". rgall.
    pose (A2 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1) with A2.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv s5,a1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x14)) Rs5 Ra1 A2 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (pwi_14 with "Htext"). }
    iIntros (CIDp28 Hsp28) "Hcg Hpc". rgall.
    pose (A3 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2).
    change (<[Regidx Rs5 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra1))]> A2) with A3.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv s4,a2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x16)) Rs4 Ra2 A3 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (pwi_16 with "Htext"). }
    iIntros (CIDp29 Hsp29) "Hcg Hpc". rgall.
    pose (A4 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (A3 !!! Regidx Ra2))]> A3).
    change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (A3 !!! Regidx Ra2))]> A3) with A4.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 jal myproc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x18)) Rra (mword_of_int 2085694 : mword 21)
              A4 (av - 14)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (pwi_18 with "Htext"). }
    iIntros (CIDp30 Hsp30) "Hcg Hpc". rgall.
    pose (A5 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x18) : mword 64) 4)]> A4).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x18) : mword 64) 4)]> A4) with A5.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.pipewrite + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2085694 : mword 21))
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
    iDestruct (cpu_own_transport CID CIDp30 0 true pj true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Myproc.wp_myproc_sconf A5 (av - 14)%nat 0%nat true pj true _
              Hlvl0 Hav10 with "Hcg Hown Htext Hpc").
    iIntros (CIDmp Hsmp ms M0) "%Hms Hcg Hown Hpc %HcsM0". rgall.
    destruct HcsM0 as [HcsM0 Ha0M0].
    assert (Hpp1c : ret_pc (A5 !!! Regidx Rra) = (mword_of_int (KernelSyms.pipewrite + 0x1c) : mword 64))
      by (rewrite HraA5; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.mv s3,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x1c)) Rs3 Ra0 M0 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (pwi_1c with "Htext"). }
    iIntros (CIDp31 Hsp31) "Hcg Hpc". rgall.
    pose (B1 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (M0 !!! Regidx Ra0))]> M0).
    change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (M0 !!! Regidx Ra0))]> M0) with B1.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.mv a0,s1 *)
    assert (Hs1M0 : M0 !!! Regidx Rs1 = pi).
    { rewrite (callee_saved_lookup HcsM0 (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1A5. }
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x1e)) Ra0 Rs1 B1 (av - 14)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (pwi_1e with "Htext"). }
    iIntros (CIDp32 Hsp32) "Hcg Hpc". rgall.
    pose (B2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Rs1))]> B1).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Rs1))]> B1) with B2.
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 jal acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x20)) Rra (mword_of_int 2082326 : mword 21)
              B2 (av - 14)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (pwi_20 with "Htext"). }
    iIntros (CIDp33 Hsp33) "Hcg Hpc". rgall.
    pose (B3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) 4)]> B2).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) 4)]> B2) with B3.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.pipewrite + 0x20) : mword 64) (sign_extend' 64 (mword_of_int 2082326 : mword 21))
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
    iDestruct (cpu_own_transport CIDmp CIDp33 0 true pj true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (AcquireGen.wp_acquire_gen_sconf KT1 γl "pipe" (pipe_res γp pi) (pipe_ref γp w q)
              (pipe_dead γl γp) B3 0%nat true pj (av - 14)%nat true _ Hlvl0 Hav10 Hbelow
              ltac:(iApply pipe_ref_dead) ltac:(intros ?i; iApply locked_pre_dead)
              with "Hcg Hown Htext Hpc [] Href").
    all: try lkbelow.
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
    destruct (Z.geb 0 n) eqn:Hb0.
    - (* ======= n <= 0: i := 0 and go straight to the +0x108 tail ======= *)
      assert (Hn0 : (n <= 0)%Z).
      { assert (Hx := Hb0). rewrite Z.geb_leb in Hx. by apply Z.leb_le. }
      assert (Hgt0 : zopz0zKzJ_s (zero_reg : mword 64) (M1 !!! Regidx Rs4) = true) by exact Hcmp0.
      assert (Hal0 : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 244 : mword 13))) 0) ('b"0") = true)
        by (vm_compute; reflexivity).
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x24)) (mword_of_int 244 : mword 13)
                Rs4 M1 (trap_res true + (av - 14))%nat false ltac:(nz) Hgt0 Hal0 with "Hcg Hpc []").
      { iApply (pwi_24 with "Htext"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjf6 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 244 : mword 13))
                     = mword_of_int (KernelSyms.pipewrite + 0x118)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjf6) in "Hpc".
      (* +0x118 c.li s2,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x118)) Rs2 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) M1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (pwi_118 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      pose (Z1 := <[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1).
      change (<[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1) with Z1.
      assert (Hppf8 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x118) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x11a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppf8) in "Hpc".
      (* +0x11a c.j -> the tail *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x11a))
                (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")))
                Z1 (trap_res true + (av - 14))%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (pwi_11a with "Htext"). }
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
      assert (Hje6 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x11a) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.pipewrite + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hje6) in "Hpc".
      iDestruct "EXITS" as "[TAIL _]".
      rewrite /pw_tail.
      iSpecialize ("TAIL" $! CIDaq with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! Z1 (pv_upt V) with "[%] [%] [%] [%] HF7 Hhi Hcg Hown Hpay Hlocked Hres Hpc Href [Hpriv]").
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
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x24)) (mword_of_int 244 : mword 13)
                Rs4 M1 (trap_res true + (av - 14))%nat false ltac:(nz) Hgf0 with "Hcg Hpc []").
      { iApply (pwi_24 with "Htext"). }
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
      iEval (rewrite -Hb8 -HspM1) in "G8".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x28)) (mword_of_int 6 : mword 6) Rs6
                M1 (trap_res true + (av - 14))%nat u8 false with "Hcg Hpc [] G8").
      { iApply (pwi_28 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G8". rgall.
      iEval (rewrite HspM1 Hb8 Hs6M1) in "G8".
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iEval (rewrite -Hb9 -HspM1) in "G9".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x2a)) (mword_of_int 5 : mword 6) Rs7
                M1 (trap_res true + (av - 14))%nat u9 false with "Hcg Hpc [] G9").
      { iApply (pwi_2a with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G9". rgall.
      iEval (rewrite HspM1 Hb9 Hs7M1) in "G9".
      assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      iEval (rewrite -Hb10 -HspM1) in "G10".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x2c)) (mword_of_int 4 : mword 6) Rs8
                M1 (trap_res true + (av - 14))%nat u10 false with "Hcg Hpc [] G10").
      { iApply (pwi_2c with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G10". rgall.
      iEval (rewrite HspM1 Hb10 Hs8M1) in "G10".
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      iEval (rewrite -Hb11 -HspM1) in "G11".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x2e)) (mword_of_int 3 : mword 6) Rs9
                M1 (trap_res true + (av - 14))%nat u11 false with "Hcg Hpc [] G11").
      { iApply (pwi_2e with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G11". rgall.
      iEval (rewrite HspM1 Hb11 Hs9M1) in "G11".
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      iEval (rewrite -Hb12 -HspM1) in "G12".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x30)) (mword_of_int 2 : mword 6) Rs10
                M1 (trap_res true + (av - 14))%nat u12 false with "Hcg Hpc [] G12").
      { iApply (pwi_30 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc G12". rgall.
      iEval (rewrite HspM1 Hb12 Hs10M1) in "G12".
      assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      iAssert (pw_frame5 m sp0) with "[G8 G9 G10 G11 G12]" as "HF5".
      { rewrite /pw_frame5. iFrame "G8 G9 G10 G11 G12". }
      (* +0x32 c.li s2,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x32)) Rs2 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) M1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (pwi_32 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      pose (C1 := <[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1).
      change (<[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> M1) with C1.
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      (* +0x34 addi s8,s0,-97 *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x34)) Rs8 Rs0
                (mword_of_int 3999 : mword 12) C1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (pwi_34 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      pose (C2 := <[Regidx Rs8 := regval_into_reg
          (add_vec (C1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3999 : mword 12)))]> C1).
      change (<[Regidx Rs8 := regval_into_reg
          (add_vec (C1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3999 : mword 12)))]> C1) with C2.
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.li s7,1 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x38)) Rs7 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) C2 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (pwi_38 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      pose (C3 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> C2).
      change (<[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> C2) with C3.
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.li s6,-1 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x3a)) Rs6 (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) C3 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (pwi_3a with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      pose (C4 := <[Regidx Rs6 := regval_into_reg (mword_of_int (-1) : mword 64)]> C3).
      change (<[Regidx Rs6 := regval_into_reg (mword_of_int (-1) : mword 64)]> C3) with C4.
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c addi s10,s1,536 *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x3c)) Rs10 Rs1
                (mword_of_int 536 : mword 12) C4 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (pwi_3c with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      pose (C5 := <[Regidx Rs10 := regval_into_reg
          (add_vec (C4 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> C4).
      change (<[Regidx Rs10 := regval_into_reg
          (add_vec (C4 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> C4) with C5.
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* +0x40 addi s9,s1,540 *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x40)) Rs9 Rs1
                (mword_of_int 540 : mword 12) C5 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (pwi_40 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      pose (C6 := <[Regidx Rs9 := regval_into_reg
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
      (* THE LOOP (iLöb at the body, +0x8c)                                 *)
      (* ================================================================= *)
      iAssert (pw_loop CID γa γf γs j γl γp w q m av true lks pid V n sp0 pi addr) with "[]" as "LOOP".
      { iLöb as "IH". rewrite /pw_loop.
        iIntros (CIDlp Hslp i M Pc) "%Hi %Hext %Hregs HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv _ HEX".
        pose proof Hregs as Hregs2.
        destruct Hregs2 as (Hsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 &
                            Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
        assert (Hi1 : (i + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
        iDestruct "Hres" as (nr nw ro wo vname bs)
          "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hcnt & %Hbslen & Hdat & Hslack)".
        (* [Hnm]/[Hwo]/the two [pipe_endstate]s/[Hslack] are read nowhere in
           the loop body between here and whichever [pw_res_intro_rest] call
           reassembles them; bundling them now keeps them out of every
           instruction step's Δ until then (see [pw_res_intro_rest]'s
           comment). *)
        iCombine "Hnm Hwo Hst0 Hst1 Hslack" as "Hrest".
        (* ---- +0x8c  lw a5,544(s1)  : readopen ---- *)
        assert (Hroaddr : add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 544 : mword 12)) = a_popen pi false)
          by (rewrite Hs1; reflexivity).
        iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.pipewrite + 0x8c)) Ra5 Rs1 (mword_of_int 544 : mword 12)
                  M (trap_res true + (av - 14))%nat ro false ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hro]").
        { iApply (pwi_8c with "Htext"). }
        { rgall. iEval (rewrite Hroaddr). iExact "Hro". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hro". rgall.
        iEval (rewrite Hroaddr) in "Hro".
        pose (L1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 ro)]> M).
        change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 ro)]> M) with L1.
        assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x8c) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp90) in "Hpc".
        assert (Ha5L1 : L1 !!! Regidx Ra5 = sign_extend' 64 ro) by (rewrite /L1; apply upd_eq).
        assert (HcsML1 : callee_saved M L1)
          by (rewrite /L1; apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]).
        destruct (eq_vec (sign_extend' 64 ro) (zero_reg : mword 64)) eqn:Hroz.
        - (* ==== readopen == 0 : the -1 arm ==== *)
          assert (Hcz : eq_vec (L1 !!! Regidx Ra5) (zero_reg : mword 64) = true)
            by (rewrite Ha5L1; exact Hroz).
          assert (Halz : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x90) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 219 : mword 8) ('b"0"))))) 0) ('b"0") = true)
            by (vm_compute; reflexivity).
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x90)) (mword_of_int 219 : mword 8)
                    (Cregidx (mword_of_int 7)) Ra5 L1 (trap_res true + (av - 14))%nat false
                    ltac:(vm_compute; reflexivity) ltac:(nz) Hcz Halz with "Hcg Hpc []").
          { iApply (pwi_90 with "Htext"). }
          iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          assert (Hj46 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x90) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 219 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.pipewrite + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hj46) in "Hpc".
          iDestruct "HEX" as "[_ MIN]". rewrite /pw_minus1.
          iSpecialize ("MIN" $! CIDlp with "[%]"); [wp_next_chain|].
          iApply ("MIN" $! L1 Pc with "[%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked [Hrest Hnr Hnw Hro Hdat] Hpc Href Hpriv").
          + unfold pw_min_regs. split_and!.
            { rewrite (callee_saved_lookup HcsML1 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
            { rewrite (callee_saved_lookup HcsML1 (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1. }
            { rewrite (callee_saved_lookup HcsML1 (mword_of_int 27) ltac:(vm_compute; reflexivity)). exact Hs11. }
          + exact Hext.
          + iApply (pw_res_intro_rest γp pi nr nw ro wo vname bs Hcnt Hbslen
                      with "Hrest Hnr Hnw Hro Hdat").
        - (* ==== readopen /= 0 : ask killed() ==== *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x90)) (mword_of_int 219 : mword 8)
                    (Cregidx (mword_of_int 7)) Ra5 L1 (trap_res true + (av - 14))%nat false
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgall; rewrite Ha5L1; exact Hroz) with "Hcg Hpc []").
          { iApply (pwi_90 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          assert (Hpp92 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x90) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp92) in "Hpc".
          (* +0x92 c.mv a0,s3 *)
          iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x92)) Ra0 Rs3 L1 (trap_res true + (av - 14))%nat false
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (pwi_92 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          pose (L2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs3))]> L1).
          change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs3))]> L1) with L2.
          assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x92) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp94) in "Hpc".
          (* +0x94 jal killed *)
          iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x94)) Rra (mword_of_int 2087732 : mword 21)
                    L2 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (pwi_94 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
          pose (L3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x94) : mword 64) 4)]> L2).
          change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x94) : mword 64) 4)]> L2) with L3.
          assert (Hjkl : add_vec (mword_of_int (KernelSyms.pipewrite + 0x94) : mword 64) (sign_extend' 64 (mword_of_int 2087732 : mword 21))
                         = mword_of_int KernelSyms.killed) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjkl) in "Hpc".
          assert (Hs3L1 : L1 !!! Regidx Rs3 = proc_addr j)
            by (rewrite /L1 upd_ne; [exact Hs3 | reg_neq]).
          assert (Ha0L3 : L3 !!! Regidx Ra0 = proc_addr j).
          { rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_eq. unfold regval_into_reg.
            rewrite Hs3L1. apply add_vec_zero_l. }
          assert (Hlvl1 : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
          assert (Hav14 : (14 <= trap_res true + (av - 14))%nat) by lia.
          iApply (Killed.wp_killed_sconf γs j γlp L3 (trap_res true + (av - 14))%nat 1%nat true (proc_addr j) false
                    ({["pipe"]} ∪ lks)
                    Ha0L3 Hj Hjlp Hlvl1 Hav14 ltac:(lkbelow)
                    with "Hcg Hown Htext Hpc Hpinv").
          all: try lkbelow.
          iApply wp_next_off_intro. iIntros (K0 kl) "%Hkfacts Hcg Hown Hpc". rgall.
          destruct Hkfacts as [Hkcs Hka0].
          assert (HraL3 : L3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x94) : mword 64) 4)
            by (rewrite /L3; apply upd_eq).
          iEval (rewrite HraL3) in "Hpc".
          assert (Hpp98 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x94) : mword 64) 4)
                          = (mword_of_int (KernelSyms.pipewrite + 0x98) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp98) in "Hpc".
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
          destruct (neq_vec (sign_extend' 64 kl : mword 64) (zero_reg : mword 64)) eqn:Hklz.
          + (* ==== killed: the -1 arm ==== *)
            assert (Hcnz : neq_vec (K0 !!! Regidx Ra0) (zero_reg : mword 64) = true)
              by (rewrite Hka0; exact Hklz).
            assert (Halz : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0x98) : mword 64)
                             (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 215 : mword 8) ('b"0"))))) 0) ('b"0") = true)
              by (vm_compute; reflexivity).
            iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x98)) (mword_of_int 215 : mword 8)
                      (Cregidx (mword_of_int 2)) Ra0 K0 (trap_res true + (av - 14))%nat false
                      ltac:(vm_compute; reflexivity) ltac:(nz) Hcnz Halz with "Hcg Hpc []").
            { iApply (pwi_98 with "Htext"). }
            iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
            assert (Hj46 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x98) : mword 64)
                             (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 215 : mword 8) ('b"0"))))
                           = mword_of_int (KernelSyms.pipewrite + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hj46) in "Hpc".
            iDestruct "HEX" as "[_ MIN]". rewrite /pw_minus1.
            iSpecialize ("MIN" $! CIDlp with "[%]"); [wp_next_chain|].
            iApply ("MIN" $! K0 Pc with "[%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked [Hrest Hnr Hnw Hro Hdat] Hpc Href Hpriv").
            * unfold pw_min_regs. split_and!; assumption.
            * exact Hext.
            * iApply (pw_res_intro_rest γp pi nr nw ro wo vname bs Hcnt Hbslen
                        with "Hrest Hnr Hnw Hro Hdat").
          + (* ==== alive: read the counters ==== *)
            iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x98)) (mword_of_int 215 : mword 8)
                      (Cregidx (mword_of_int 2)) Ra0 K0 (trap_res true + (av - 14))%nat false
                      ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgall; rewrite Hka0; exact Hklz) with "Hcg Hpc []").
            { iApply (pwi_98 with "Htext"). }
            iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
            assert (Hpp9a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x98) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpp9a) in "Hpc".
            (* +0x9a lw a5,536(s1) : nread *)
            assert (Hnraddr : add_vec (K0 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)) = a_pnread pi)
              by (rewrite Ks1F; reflexivity).
            iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.pipewrite + 0x9a)) Ra5 Rs1 (mword_of_int 536 : mword 12)
                      K0 (trap_res true + (av - 14))%nat nr false ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hnr]").
            { iApply (pwi_9a with "Htext"). }
            { rgall. iEval (rewrite Hnraddr). iExact "Hnr". }
            iApply wp_next_off_intro. iIntros "Hcg Hpc Hnr". rgall.
            iEval (rewrite Hnraddr) in "Hnr".
            pose (K1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> K0).
            change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> K0) with K1.
            assert (Hpp9e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x9a) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpp9e) in "Hpc".
            (* +0x9e lw a4,540(s1) : nwrite *)
            assert (Hnwaddr : add_vec (K1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi).
            { rewrite /K1 upd_ne; [| reg_neq]. rewrite Ks1F. reflexivity. }
            iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.pipewrite + 0x9e)) Ra4 Rs1 (mword_of_int 540 : mword 12)
                      K1 (trap_res true + (av - 14))%nat nw false ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hnw]").
            { iApply (pwi_9e with "Htext"). }
            { rgall. iEval (rewrite Hnwaddr). iExact "Hnw". }
            iApply wp_next_off_intro. iIntros "Hcg Hpc Hnw". rgall.
            iEval (rewrite Hnwaddr) in "Hnw".
            pose (K2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 nw)]> K1).
            change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 nw)]> K1) with K2.
            assert (Hppa2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x9e) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hppa2) in "Hpc".
            (* +0xa2 addiw a5,a5,512 *)
            iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xa2)) Ra5 Ra5
                      (mword_of_int 512 : mword 12) K2 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                      with "Hcg Hpc []").
            { iApply (pwi_a2 with "Htext"). }
            iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
            pose (K3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                (add_vec (K2 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 512 : mword 12))) 31 0))]> K2).
            change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                (add_vec (K2 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 512 : mword 12))) 31 0))]> K2) with K3.
            assert (Hppa6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa2) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hppa6) in "Hpc".
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
            (* +0xa6 beq a4,a5 : the pipe-full test *)
            destruct (eq_vec (K3 !!! Regidx Ra4) (K3 !!! Regidx Ra5)) eqn:Hfull.
            * (* ======== FULL: wakeup(&nread); sleep(&nwrite, &lock) ======== *)
              assert (Half : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0xa6) : mword 64)
                               (sign_extend' 64 (mword_of_int 8134 : mword 13))) 0) ('b"0") = true)
                by (vm_compute; reflexivity).
              (* [rget]-spelled restatement of [Hfull] -- the leaf wants
                 [rget], not [!!!]; see the [Strategy opaque] comment above. *)
              assert (Hfullr : eq_vec (rget K3 Ra4) (rget K3 Ra5) = true)
                by (rewrite !rget_ne; [exact Hfull | vm_compute; discriminate | vm_compute; discriminate]).
              iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xa6)) (mword_of_int 8134 : mword 13)
                        Ra5 Ra4 K3 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(nz) Hfullr Half
                        with "Hcg Hpc []").
              { iApply (pwi_a6 with "Htext"). }
              iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              assert (Hj6c : add_vec (mword_of_int (KernelSyms.pipewrite + 0xa6) : mword 64)
                               (sign_extend' 64 (mword_of_int 8134 : mword 13))
                             = mword_of_int (KernelSyms.pipewrite + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hj6c) in "Hpc".
              (* the pipe goes back together untouched *)
              iAssert (pipe_res γp pi) with "[Hrest Hnr Hnw Hro Hdat]" as "Hres".
              { iApply (pw_res_intro_rest γp pi nr nw ro wo vname bs Hcnt Hbslen
                          with "Hrest Hnr Hnw Hro Hdat"). }
              (* +0x6c c.mv a0,s10 *)
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x6c)) Ra0 Rs10 K3 (trap_res true + (av - 14))%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
              { iApply (pwi_6c with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (F1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs10))]> K3).
              change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs10))]> K3) with F1.
              assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp6e) in "Hpc".
              (* +0x6e jal wakeup *)
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x6e)) Rra (mword_of_int 2087278 : mword 21)
                        F1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc []").
              { iApply (pwi_6e with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (F2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) 4)]> F1).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) 4)]> F1) with F2.
              assert (Hjwk : add_vec (mword_of_int (KernelSyms.pipewrite + 0x6e) : mword 64) (sign_extend' 64 (mword_of_int 2087278 : mword 21))
                             = mword_of_int KernelSyms.wakeup) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjwk) in "Hpc".
              assert (HwK : (18 <= trap_res true + (av - 14))%nat) by lia.
              assert (HwdomF : forall r : regidx, r ∈ dom (rf_to_gmap F2)) by (intro r; apply rf_to_gmap_dom).
              assert (Hwlvl : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z) by (rewrite H31; lia).
              iApply (Wakeup.wp_wakeup_sconf F2 γs (proc_addr j) 1%nat (trap_res true + (av - 14))%nat true false
                        ({["pipe"]} ∪ lks)
                        HwK HwdomF Hlen Hwlvl ltac:(lkbelow)
                        with "Hcg Hown Htext Hpc Hpinv").
              all: try lkbelow.
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
              (* ======= THE SPLIT SLEEP PROTOCOL, +0x72 .. +0x84 =======
                   0x72 c.mv a0,s9        a0 := &pi->nwrite
                   0x74 jal sleep_prepare record the channel, under pi->lock
                   0x78 c.mv a0,s1        a0 := &pi->lock
                   0x7a jal release       THE CALLER'S OWN release: 1 -> 0
                   0x7e jal sleep         park, if no wakeup arrived first
                   0x82 c.mv a0,s1
                   0x84 jal acquire       THE CALLER'S OWN re-acquire: 0 -> 1

                 The condition lock has left sleep's contract entirely, so the
                 [lock_openable]/credential genericity that [SLEEP_GEN] used to
                 carry for a pipe is now just these two ordinary calls --
                 instantiated exactly as the entry acquire at +0x20 and the
                 early-exit release at +0x48 are.

                 THE SLEEPER STILL CANNOT LOSE THE PIPE UNDER ITSELF: this
                 frame holds [Href : pipe_ref γp w q] -- the write end
                 pipewrite is running on behalf of -- across all four calls, so
                 [pipe_dead] is refuted here for the whole park, and it is that
                 same reference the re-acquire presents as its credential.

                 From the release to the re-acquire the thread holds no lock
                 and pop_off has turned interrupts back on ([outb = eb =
                 true]), so that stretch is [b = true]-indexed: its leaves hand
                 the hart on through [wp_next true] rather than
                 [wp_next_off_intro], and [cpu_own] is re-anchored with
                 [cpu_own_transport], as on the entry path. *)
              (* +0x72 c.mv a0,s9 *)
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x72)) Ra0 Rs9 Mw (trap_res true + (av - 14))%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
              { iApply (pwi_72 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (G1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs9))]> Mw).
              change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs9))]> Mw) with G1.
              assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp74) in "Hpc".
              (* +0x74 jal sleep_prepare *)
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x74)) Rra (mword_of_int 2087164 : mword 21)
                        G1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc []").
              { iApply (pwi_74 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (G2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x74) : mword 64) 4)]> G1).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x74) : mword 64) 4)]> G1) with G2.
              assert (Hjsp : add_vec (mword_of_int (KernelSyms.pipewrite + 0x74) : mword 64) (sign_extend' 64 (mword_of_int 2087164 : mword 21))
                             = mword_of_int KernelSyms.sleep_prepare) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjsp) in "Hpc".
              assert (Ha0G2 : G2 !!! Regidx Ra0 = a_pnwrite pi).
              { rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_eq. unfold regval_into_reg.
                rewrite Ws9. apply add_vec_zero_l. }
              assert (HraG2 : G2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x74) : mword 64) 4)
                by (rewrite /G2; apply upd_eq).
              assert (HcsMwG2 : callee_saved Mw G2).
              { rewrite /G2 /G1.
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
              iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γlp G2
                        (trap_res true + (av - 14))%nat 1%nat true false
                        ({["pipe"]} ∪ lks)
                        Hj Hjlp ltac:(rewrite Ha0G2; exact (pw_pnwrite_nz pi Hpv)) Hlvl1 Hav14 ltac:(lkbelow)
                        with "Hcg Hown Htext Hpc Hpinv").
              all: try lkbelow.
              iApply wp_next_off_intro. iIntros (Msp) "%Hspcs Hcg Hown Hpc". rgall.
              iEval (rewrite HraG2) in "Hpc".
              assert (Hpp78 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x74) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0x78) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp78) in "Hpc".
              assert (HcsMwMsp : callee_saved Mw Msp) by (apply (callee_saved_trans Mw G2 Msp HcsMwG2 Hspcs)).
              assert (Hs1Msp : Msp !!! Regidx Rs1 = pi)
                by (rewrite (callee_saved_lookup HcsMwMsp Rs1 ltac:(vm_compute; reflexivity)); exact Ws1).
              (* +0x78 c.mv a0,s1 *)
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x78)) Ra0 Rs1 Msp (trap_res true + (av - 14))%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
              { iApply (pwi_78 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (G3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Msp !!! Regidx Rs1))]> Msp).
              change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Msp !!! Regidx Rs1))]> Msp) with G3.
              assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp7a) in "Hpc".
              (* +0x7a jal release -- the caller's own release of pi->lock *)
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x7a)) Rra (mword_of_int 2082372 : mword 21)
                        G3 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc []").
              { iApply (pwi_7a with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (G4 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64) 4)]> G3).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64) 4)]> G3) with G4.
              assert (Hjrl0 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64) (sign_extend' 64 (mword_of_int 2082372 : mword 21))
                              = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjrl0) in "Hpc".
              assert (Ha0G4 : G4 !!! Regidx Ra0 = pi).
              { rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3 upd_eq. unfold regval_into_reg.
                rewrite Hs1Msp. apply add_vec_zero_l. }
              assert (HraG4 : G4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64) 4)
                by (rewrite /G4; apply upd_eq).
              assert (HlkaG4 : add_vec (G4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
              { rewrite Ha0G4.
                replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
                  by (apply bv_eq; vm_compute; reflexivity).
                apply kv_addv_zero. }
              assert (HcsMwG4 : callee_saved Mw G4).
              { rewrite /G4 /G3.
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsMwMsp. }
              iApply (ReleaseGen.wp_release_gen_sconf KT1 γl pi "pipe" (pipe_res γp pi) (pipe_dead γl γp) emp%I
                        G4 0%nat true (proc_addr j) (av - 14)%nat ({["pipe"]} ∪ lks) HlkaG4 Hav10
                        ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                        with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay").
              { iApply lock_finisher_close. }
              iIntros (CIDrs Hsrs Mrl) "_ Hcg Hpc %Hcsrl Hown". rgall.
              iEval (rewrite HraG4) in "Hpc".
              assert (Hpp7e : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7a) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp7e) in "Hpc".
              assert (HcsMwMrl : callee_saved Mw Mrl) by (apply (callee_saved_trans Mw G4 Mrl HcsMwG4 Hcsrl)).
              (* +0x7e jal sleep -- the park.  Its contract names no lock. *)
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x7e)) Rra (mword_of_int 2087214 : mword 21)
                        Mrl (av - 14)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc []").
              { iApply (pwi_7e with "Htext"). }
              iIntros (CIDp50 Hsp50) "Hcg Hpc". rgall.
              pose (G5 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64) 4)]> Mrl).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64) 4)]> Mrl) with G5.
              assert (Hjsl : add_vec (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64) (sign_extend' 64 (mword_of_int 2087214 : mword 21))
                             = mword_of_int KernelSyms.sleep) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjsl) in "Hpc".
              assert (HraG5 : G5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64) 4)
                by (rewrite /G5; apply upd_eq).
              assert (HcsMwG5 : callee_saved Mw G5).
              { rewrite /G5. apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsMwMrl. }
              iDestruct (cpu_own_transport CIDrs CIDp50 0 true (proc_addr j) true ltac:(wp_next_chain)
                           with "Hown") as "Hown".
              (* the release above left [({[rank "pipe"]} ∪ lks) ∖ {[rank
                 "pipe"]}]; [lks = ∅] at depth 0 makes that the empty set,
                 which is renamed back to [lks] -- the bare entry set sleep's
                 contract names. *)
              iEval (rewrite Hlkempty locks_union_empty locks_self_del -Hlkempty) in "Hown".
              (* both extra premises are [emp] here: sleep is reached at noff 0
                 with interrupts ENABLED, so [trap_csrs_ext true = emp] and
                 [cpu_claim_ext true pj = emp] -- sleep's own acquire mints the
                 pair out of the enabled SIE arm. *)
              iApply (Sleep.wp_sleep_sconf γs j γlp G5 (av - 14)%nat true lks
                        Hj Hjlp ltac:(lia) Hbelowproc
                        with "Hcg Hown Htext Hpc Hpinv [] []").
              all: try lkbelow.
              { rewrite /trap_csrs_ext. done. }
              { rewrite /cpu_claim_ext. done. }
              iIntros (CIDsl0 Hssl0 Msl) "%Hslcs Hcg Hown Hpc _ _". rgall.
              iEval (rewrite HraG5) in "Hpc".
              assert (Hpp82 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x7e) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0x82) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp82) in "Hpc".
              assert (HcsMwMsl : callee_saved Mw Msl) by (apply (callee_saved_trans Mw G5 Msl HcsMwG5 Hslcs)).
              assert (Hs1Msl : Msl !!! Regidx Rs1 = pi)
                by (rewrite (callee_saved_lookup HcsMwMsl Rs1 ltac:(vm_compute; reflexivity)); exact Ws1).
              (* +0x82 c.mv a0,s1 *)
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x82)) Ra0 Rs1 Msl (av - 14)%nat true
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
              { iApply (pwi_82 with "Htext"). }
              iIntros (CIDp51 Hsp51) "Hcg Hpc". rgall.
              pose (G6 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Msl !!! Regidx Rs1))]> Msl).
              change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Msl !!! Regidx Rs1))]> Msl) with G6.
              assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp84) in "Hpc".
              (* +0x84 jal acquire -- the caller's own re-acquire, on the very
                 [pipe_ref] this frame carried through the park *)
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x84)) Rra (mword_of_int 2082226 : mword 21)
                        G6 (av - 14)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc []").
              { iApply (pwi_84 with "Htext"). }
              iIntros (CIDp52 Hsp52) "Hcg Hpc". rgall.
              pose (G7 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x84) : mword 64) 4)]> G6).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x84) : mword 64) 4)]> G6) with G7.
              assert (Hjaq2 : add_vec (mword_of_int (KernelSyms.pipewrite + 0x84) : mword 64) (sign_extend' 64 (mword_of_int 2082226 : mword 21))
                              = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjaq2) in "Hpc".
              assert (Ha0G7 : G7 !!! Regidx Ra0 = pi).
              { rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_eq. unfold regval_into_reg.
                rewrite Hs1Msl. apply add_vec_zero_l. }
              assert (HraG7 : G7 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x84) : mword 64) 4)
                by (rewrite /G7; apply upd_eq).
              assert (HcsMwG7 : callee_saved Mw G7).
              { rewrite /G7 /G6.
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
                apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsMwMsl. }
              iDestruct (cpu_own_transport CIDsl0 CIDp52 0 true pj true ltac:(wp_next_chain)
                           with "Hown") as "Hown".
              iApply (AcquireGen.wp_acquire_gen_sconf KT1 γl "pipe" (pipe_res γp pi) (pipe_ref γp w q)
                        (pipe_dead γl γp) G7 0%nat true pj (av - 14)%nat true _ Hlvl0 Hav10 Hbelow
                        ltac:(iApply pipe_ref_dead) ltac:(intros ?i; iApply locked_pre_dead)
                        with "Hcg Hown Htext Hpc [] Href").
              all: try lkbelow.
              { rgall. iEval (rewrite Ha0G7). iExact "Hopen". }
              iIntros (CIDsl Hssl ms4 Ms) "%Hms4 Href Hcg Hpc %Hcsaq2 Hlocked Hres Hown Hpay". rgall.
              iEval (rewrite HraG7) in "Hpc".
              assert (Hpp88 : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0x84) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0x88) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hpp88) in "Hpc".
              assert (HregsMs : pw_loop_regs m Ms (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i).
              { apply (pw_loop_regs_cs m G7 Ms (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i Hcsaq2).
                apply (pw_loop_regs_cs m Mw G7 (pa_stk sp0 14%nat) sp0 pi (proc_addr j) addr n i HcsMwG7 HregsMw). }
              iApply (pw_guard_step (CID := CIDsl) CID γa γf γs j γl γp w q m av true lks pid V n sp0 pi addr i Ms Pc
                        Hn0 Hn31 ltac:(lia) ltac:(wp_next_chain) Hext HregsMs
                        with "Htext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Henv HEX IH").
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
              (* [rget]-spelled restatement of [Hfull] -- the leaf wants
                 [rget], not [!!!]; see the [Strategy opaque] comment above. *)
              assert (Hfullr : eq_vec (rget K3 Ra4) (rget K3 Ra5) = false)
                by (rewrite !rget_ne; [exact Hfull | vm_compute; discriminate | vm_compute; discriminate]).
              iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xa6)) (mword_of_int 8134 : mword 13)
                        Ra5 Ra4 K3 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(nz) Hfullr
                        with "Hcg Hpc []").
              { iApply (pwi_a6 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              assert (Hppaa : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xa6) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppaa) in "Hpc".
              (* +0xaa c.mv a4,s7 -- copyin's arguments all sit one register
                 lower since it gained [psz] in a1 (xv6 `4f2fc8b`). *)
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xaa)) Ra4 Rs7 K3 (trap_res true + (av - 14))%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
              { iApply (pwi_aa with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (N1 := <[Regidx Ra4 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs7))]> K3).
              change (<[Regidx Ra4 := regval_into_reg (add_vec zero_reg (K3 !!! Regidx Rs7))]> K3) with N1.
              assert (Hppac : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xaa) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppac) in "Hpc".
              (* +0xac add a3,s2,s5 *)
              iApply (wp_add_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xac)) Ra3 Rs2 Rs5
                        (add_vec (N1 !!! Regidx Rs2) (N1 !!! Regidx Rs5)) N1 (trap_res true + (av - 14))%nat false
                        ltac:(nz) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc []").
              { iApply (pwi_ac with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (N2 := <[Regidx Ra3 := regval_into_reg
                  (add_vec (N1 !!! Regidx Rs2) (N1 !!! Regidx Rs5))]> N1).
              change (<[Regidx Ra3 := regval_into_reg
                  (add_vec (N1 !!! Regidx Rs2) (N1 !!! Regidx Rs5))]> N1) with N2.
              assert (Hppb0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xac) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppb0) in "Hpc".
              (* +0xb0 c.mv a2,s8 *)
              iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xb0)) Ra2 Rs8 N2 (trap_res true + (av - 14))%nat false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
              { iApply (pwi_b0 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (N3 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (N2 !!! Regidx Rs8))]> N2).
              change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (N2 !!! Regidx Rs8))]> N2) with N3.
              assert (Hppb2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xb0) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppb2) in "Hpc".
              (* the ONE borrow out of [proc_priv] for this iteration *)
              iDestruct (proc_priv_core_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
              iEval (rewrite (pw_pv_sz_upd V Pc)) in "Hszc".
              iEval (rewrite (pw_pv_upt_upd V Pc)) in "Hptc".
              iEval (rewrite (pw_pv_upt_upd V Pc)) in "Hpt".
              iEval (rewrite (pw_pv_sz_upd V Pc) (pw_pv_upt_upd V Pc)) in "Hpback".
              assert (Hs3N3 : N3 !!! Regidx Rs3 = proc_addr j).
              { rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
                rewrite /N1 upd_ne; [exact Js3 | reg_neq]. }
              (* +0xb2 ld a1,72(s3) : p->sz, copyin's NEW [psz] argument.  The
                 cell is only READ here; the contract no longer takes it. *)
              assert (Hszaddr : add_vec (N3 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 72 : mword 12))
                                = p_sz (proc_addr j)) by (rewrite Hs3N3; reflexivity).
              iEval (rewrite -Hszaddr) in "Hszc".
              iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.pipewrite + 0xb2)) Ra1 Rs3
                        (mword_of_int 72 : mword 12) N3 (trap_res true + (av - 14))%nat (pv_sz V) false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hszc").
              { iApply (pwi_b2 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc Hszc". rgall.
              iEval (rewrite Hszaddr) in "Hszc".
              pose (N3b := <[Regidx Ra1 := regval_into_reg (pv_sz V)]> N3).
              change (<[Regidx Ra1 := regval_into_reg (pv_sz V)]> N3) with N3b.
              assert (Hppb2' : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xb2) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xb6)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppb2') in "Hpc".
              (* +0xb6 ld a0,80(s3) : p->pagetable *)
              assert (Hs3N3b : N3b !!! Regidx Rs3 = proc_addr j)
                by (rewrite /N3b upd_ne; [exact Hs3N3 | reg_neq]).
              assert (Hptaddr : add_vec (N3b !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 80 : mword 12))
                                = p_pagetable (proc_addr j)) by (rewrite Hs3N3b; reflexivity).
              iEval (rewrite -Hptaddr) in "Hptc".
              iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.pipewrite + 0xb6)) Ra0 Rs3
                        (mword_of_int 80 : mword 12) N3b (trap_res true + (av - 14))%nat (page_base (ud_root Pc)) false
                        ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hptc").
              { iApply (pwi_b6 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc Hptc". rgall.
              iEval (rewrite Hptaddr) in "Hptc".
              pose (N4 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root Pc))]> N3b).
              change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root Pc))]> N3b) with N4.
              assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xb6) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xba)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppb6) in "Hpc".
              (* +0xba jal copyin *)
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xba)) Rra (mword_of_int 2084764 : mword 21)
                        N4 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc []").
              { iApply (pwi_ba with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
              pose (N5 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xba) : mword 64) 4)]> N4).
              change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xba) : mword 64) 4)]> N4) with N5.
              assert (Hjci : add_vec (mword_of_int (KernelSyms.pipewrite + 0xba) : mword 64) (sign_extend' 64 (mword_of_int 2084764 : mword 21))
                             = mword_of_int KernelSyms.copyin) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hjci) in "Hpc".
              assert (Ha0N5 : N5 !!! Regidx Ra0 = page_base (ud_root Pc)).
              { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_eq. reflexivity. }
              assert (Ha1N5 : N5 !!! Regidx Ra1 = pv_sz V).
              { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
                rewrite /N3b upd_eq. reflexivity. }
              assert (Ha2N5 : N5 !!! Regidx Ra2 = pa_add (pa_stk sp0 13%nat) 7%nat).
              { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
                rewrite /N3b upd_ne; [| reg_neq]. rewrite /N3 upd_eq. unfold regval_into_reg.
                rewrite (_ : N2 !!! Regidx Rs8 = pa_add (pa_stk sp0 13%nat) 7%nat); [apply add_vec_zero_l|].
                rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact Js8 | reg_neq]. }
              assert (Ha4N5 : N5 !!! Regidx Ra4 = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
              { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
                rewrite /N3b upd_ne; [| reg_neq].
                rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
                rewrite /N1 upd_eq. unfold regval_into_reg. rewrite Js7.
                rewrite add_vec_zero_l. apply bv_eq; vm_compute; reflexivity. }
              assert (HK50 : (50 <= trap_res true + (av - 14))%nat) by lia.
              assert (Hlen1 : (Z.of_nat 1%nat < 2 ^ 64)%Z) by (vm_compute; reflexivity).
              (* the single byte [ch] IS copyin's destination buffer *)
              iDestruct "HCH" as "(%Hal13 & Hb13 & Hslot14)".
              iDestruct (bytes_own_acc (KTR := KT1) (DfracOwn 1) (pa_stk sp0 13%nat) 8%nat 7%nat ltac:(lia) with "Hb13")
                as "[Hchx Hchback]".
              iDestruct "Hchx" as (b0) "Hch".
              iAssert ([∗ list] k ∈ seq 0 1, (pa_add (N5 !!! Regidx Ra2) k) ↦ₘ[KT1] ((fun _ : nat => b0) k))%I
                with "[Hch]" as "Hbuf".
              { cbn [seq]. iSplitL "Hch"; [| done]. iEval (rewrite Ha2N5 pa_add_0). iExact "Hch". }
              iApply (Copyin.wp_copyin_sconf KT1 γa N5 Pc (pv_sz V) 1%nat (fun _ : nat => b0)
                        (trap_res true + (av - 14))%nat 1%nat true (proc_addr j) false ({["pipe"]} ∪ lks)
                        HK50 Ha0N5 Ha1N5 Ha4N5 Hlen1 Hszb Hlvl1
                        with "Hcg Hown Htext Hpc Hpt Henv Hbuf").
              all: try lkbelow.
              iApply wp_next_off_intro. iIntros (mr P' dst_new) "Hcg Hown Hpc Hpt Hbuf %Hcsr %Hextr %Hret". rgall.
              assert (HraN5 : N5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xba) : mword 64) 4)
                by (rewrite /N5; apply upd_eq).
              iEval (rewrite HraN5) in "Hpc".
              assert (Hppba : ret_pc (add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xba) : mword 64) 4)
                              = (mword_of_int (KernelSyms.pipewrite + 0xbe) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
              iEval (rewrite Hppba) in "Hpc".
              (* the destination byte back out of copyin's buffer *)
              iEval (cbn [seq]) in "Hbuf".
              iDestruct "Hbuf" as "[Hch _]".
              iEval (rewrite Ha2N5 pa_add_0) in "Hch".
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
              { rewrite /N5 /N4 /N3b /N3 /N2 /N1.
                apply callee_saved_insert_r; [vm_compute; reflexivity|].
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
              (* +0xbe beq a0,s6 : did the copy fail? *)
              destruct (eq_vec (mr !!! Regidx Ra0) (mr !!! Regidx Rs6)) eqn:Hfail.
              ** (* ==== copyin failed: break.  SINCE xv6 `76821fc` this arm
                        is TWO arms: a copy that got nowhere (i == 0) reports
                        -1, one that got somewhere keeps its partial count.
                        Both restore s6..s10 and take the same tail. ==== *)
                 assert (Half : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.pipewrite + 0xbe) : mword 64)
                                  (sign_extend' 64 (mword_of_int 34 : mword 13))) 0) ('b"0") = true)
                   by (vm_compute; reflexivity).
                 iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xbe)) (mword_of_int 34 : mword 13)
                           Rs6 Ra0 mr (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(nz) Hfail Half
                           with "Hcg Hpc []").
                 { iApply (pwi_be with "Htext"). }
                 iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 assert (Hje0 : add_vec (mword_of_int (KernelSyms.pipewrite + 0xbe) : mword 64)
                                  (sign_extend' 64 (mword_of_int 34 : mword 13))
                                = mword_of_int (KernelSyms.pipewrite + 0xe0)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hje0) in "Hpc".
                 (* put the [ch] byte back and re-bundle the slot *)
                 iDestruct ("Hchback" $! (dst_new 0%nat) with "Hch") as "Hb13".
                 iDestruct (pw_chslot_mk sp0 Hal13 with "Hb13 Hslot14") as "HCH".
                 (* the branch we took says a0 = s6 = -1, which is the value
                    the [i = -1] arm below moves into s2. *)
                 assert (Ha0m1 : mr !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)).
                 { apply eq_vec_true_iff in Hfail. rewrite Hfail. exact Rs6f. }
                 destruct (decide (i = 0%Z)) as [Hi0 | Hinz].
                 { (* ---- i == 0: beqz taken -> +0xf0, i := a0 = -1 ---- *)
                   iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xe0)) (mword_of_int 16 : mword 13)
                             Rs2 mr (trap_res true + (av - 14))%nat false ltac:(nz)
                             ltac:(rgall; rewrite Rs2f Hi0; vm_compute; reflexivity)
                             ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
                   { iApply (pwi_e0 with "Htext"). }
                   iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                   assert (Hjf0 : add_vec (mword_of_int (KernelSyms.pipewrite + 0xe0) : mword 64)
                                    (sign_extend' 64 (mword_of_int 16 : mword 13))
                                  = mword_of_int (KernelSyms.pipewrite + 0xf0)) by (apply bv_eq; vm_compute; reflexivity).
                   iEval (rewrite Hjf0) in "Hpc".
                   (* +0xf0 c.mv s2,a0 : i := -1 *)
                   iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xf0)) Rs2 Ra0 mr (trap_res true + (av - 14))%nat false
                             ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
                   { iApply (pwi_f0 with "Htext"). }
                   iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                   pose (Z1 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Ra0))]> mr).
                   change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Ra0))]> mr) with Z1.
                   assert (Hppf2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf0) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf2)) by (apply bv_eq; vm_compute; reflexivity).
                   iEval (rewrite Hppf2) in "Hpc".
                   assert (HZ1s2 : Z1 !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)).
                   { rewrite /Z1 upd_eq. unfold regval_into_reg. rewrite Ha0m1. apply add_vec_zero_l. }
                   assert (HZ1sp : Z1 !!! Regidx csp_rs1 = pa_stk sp0 14%nat)
                     by (rewrite /Z1 upd_ne; [exact Rsp | reg_neq]).
                   assert (HZ1s1 : Z1 !!! Regidx Rs1 = pi)
                     by (rewrite /Z1 upd_ne; [exact Rs1f | reg_neq]).
                   assert (HZ1s11 : Z1 !!! Regidx Rs11 = m !!! Regidx Rs11)
                     by (rewrite /Z1 upd_ne; [exact Rs11f | reg_neq]).
                   (* +0xf2 .. +0xfa reload s6..s10 *)
                   assert (Gf4 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf2) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf4)) by (apply bv_eq; vm_compute; reflexivity).
                   assert (Gf6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf4) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf6)) by (apply bv_eq; vm_compute; reflexivity).
                   assert (Gf8 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf6) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xf8)) by (apply bv_eq; vm_compute; reflexivity).
                   assert (Gfa : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xf8) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xfa)) by (apply bv_eq; vm_compute; reflexivity).
                   assert (Gfc : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xfa) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xfc)) by (apply bv_eq; vm_compute; reflexivity).
                   iApply (pw_restore5 (proc_addr j) false (mword_of_int (KernelSyms.pipewrite + 0xf2)) (mword_of_int (KernelSyms.pipewrite + 0xf4))
                             (mword_of_int (KernelSyms.pipewrite + 0xf6)) (mword_of_int (KernelSyms.pipewrite + 0xf8)) (mword_of_int (KernelSyms.pipewrite + 0xfa))
                             (mword_of_int (KernelSyms.pipewrite + 0xfc)) Z1 m (trap_res true + (av - 14))%nat sp0
                             HZ1sp Gf4 Gf6 Gf8 Gfa Gfc
                             with "Hcg Hpc [] [] [] [] [] HF5").
                   { iApply (pwi_f2 with "Htext"). }
                   { iApply (pwi_f4 with "Htext"). }
                   { iApply (pwi_f6 with "Htext"). }
                   { iApply (pwi_f8 with "Htext"). }
                   { iApply (pwi_fa with "Htext"). }
                   iApply wp_next_off_intro. iIntros (M') "%Hrst Hcg Hpc HF5".
                   destruct Hrst as (R6 & R7 & R8 & R9 & R10 & Rrest).
                   assert (Hsp' : M' !!! Regidx csp_rs1 = pa_stk sp0 14%nat).
                   { rewrite (Rrest csp_rs1 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact HZ1sp. }
                   assert (Hs1' : M' !!! Regidx Rs1 = pi).
                   { rewrite (Rrest (mword_of_int 9) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact HZ1s1. }
                   assert (Hs2' : M' !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)).
                   { rewrite (Rrest (mword_of_int 18) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact HZ1s2. }
                   assert (Hs11' : M' !!! Regidx Rs11 = m !!! Regidx Rs11).
                   { rewrite (Rrest (mword_of_int 27) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)). exact HZ1s11. }
                   (* +0xfc c.j -> the wakeup/release tail *)
                   iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xfc))
                             (sign_extend' 21 (concat_vec (mword_of_int 6 : mword 11) ('b"0")))
                             M' (trap_res true + (av - 14))%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
                   { iApply (pwi_fc with "Htext"). }
                   iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
                   assert (Hjt1 : add_vec (mword_of_int (KernelSyms.pipewrite + 0xfc) : mword 64)
                                    (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 6 : mword 11) ('b"0"))))
                                  = mword_of_int (KernelSyms.pipewrite + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
                   iEval (rewrite Hjt1) in "Hpc".
                   iDestruct "HEX" as "[TAIL _]". rewrite /pw_tail.
                   iSpecialize ("TAIL" $! CIDlp with "[%]"); [wp_next_chain|].
                   iApply ("TAIL" $! M' P' with "[%] [%] [%] [%] HF7 [HF5 HCH] Hcg Hown Hpay Hlocked [Hrest Hnr Hnw Hro Hdat] Hpc Href Hpriv").
                   --- unfold pw_base_regs. split_and!; assumption.
                   --- exact Hs1'.
                   --- rewrite Hs2'. left. reflexivity.
                   --- exact Hext'.
                   --- iApply (pw_stack7_of m sp0 with "HF5 HCH").
                   --- iApply (pw_res_intro_rest γp pi nr nw ro wo vname bs Hcnt Hbslen
                                 with "Hrest Hnr Hnw Hro Hdat"). }
                 (* ---- i /= 0: beqz falls through, keep the partial count ---- *)
                 iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xe0)) (mword_of_int 16 : mword 13)
                           Rs2 mr (trap_res true + (av - 14))%nat false ltac:(nz)
                           ltac:(rgall; rewrite Rs2f; apply pw_moi_nz0; lia)
                           with "Hcg Hpc []").
                 { iApply (pwi_e0 with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 assert (Hjfa : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe0) : mword 64) 4
                                = mword_of_int (KernelSyms.pipewrite + 0xe4)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hjfa) in "Hpc".
                 (* +0xe4 .. +0xec reload s6..s10 *)
                 assert (Efc : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe4) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xe6)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (Efe : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe6) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xe8)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (E100 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xe8) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xea)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (E102 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xea) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xec)) by (apply bv_eq; vm_compute; reflexivity).
                 assert (E104 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xec) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xee)) by (apply bv_eq; vm_compute; reflexivity).
                 iApply (pw_restore5 (proc_addr j) false (mword_of_int (KernelSyms.pipewrite + 0xe4)) (mword_of_int (KernelSyms.pipewrite + 0xe6))
                           (mword_of_int (KernelSyms.pipewrite + 0xe8)) (mword_of_int (KernelSyms.pipewrite + 0xea)) (mword_of_int (KernelSyms.pipewrite + 0xec))
                           (mword_of_int (KernelSyms.pipewrite + 0xee)) mr m (trap_res true + (av - 14))%nat sp0
                           Rsp Efc Efe E100 E102 E104
                           with "Hcg Hpc [] [] [] [] [] HF5").
                 { iApply (pwi_e4 with "Htext"). }
                 { iApply (pwi_e6 with "Htext"). }
                 { iApply (pwi_e8 with "Htext"). }
                 { iApply (pwi_ea with "Htext"). }
                 { iApply (pwi_ec with "Htext"). }
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
                 (* +0xee c.j -> the wakeup/release tail *)
                 iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xee))
                           (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0")))
                           M' (trap_res true + (av - 14))%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
                 { iApply (pwi_ee with "Htext"). }
                 iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
                 assert (Hje6 : add_vec (mword_of_int (KernelSyms.pipewrite + 0xee) : mword 64)
                                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0"))))
                                = mword_of_int (KernelSyms.pipewrite + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hje6) in "Hpc".
                 iDestruct "HEX" as "[TAIL _]". rewrite /pw_tail.
                 iSpecialize ("TAIL" $! CIDlp with "[%]"); [wp_next_chain|].
                 iApply ("TAIL" $! M' P' with "[%] [%] [%] [%] HF7 [HF5 HCH] Hcg Hown Hpay Hlocked [Hrest Hnr Hnw Hro Hdat] Hpc Href Hpriv").
                 --- unfold pw_base_regs. split_and!; assumption.
                 --- exact Hs1'.
                 --- rewrite Hs2'. right. exists i. split; [reflexivity | lia].
                 --- exact Hext'.
                 --- iApply (pw_stack7_of m sp0 with "HF5 HCH").
                 --- iApply (pw_res_intro_rest γp pi nr nw ro wo vname bs Hcnt Hbslen
                               with "Hrest Hnr Hnw Hro Hdat").
              ** (* ==== copyin succeeded: nwrite++, store the byte, i++ ==== *)
                 iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xbe)) (mword_of_int 34 : mword 13)
                           Rs6 Ra0 mr (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(nz) Hfail
                           with "Hcg Hpc []").
                 { iApply (pwi_be with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 assert (Hppbe : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xbe) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xc2)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppbe) in "Hpc".
                 (* +0xc2 lw a5,540(s1) *)
                 assert (Hnwaddr2 : add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi)
                   by (rewrite Rs1f; reflexivity).
                 iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.pipewrite + 0xc2)) Ra5 Rs1 (mword_of_int 540 : mword 12)
                           mr (trap_res true + (av - 14))%nat nw false ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hnw]").
                 { iApply (pwi_c2 with "Htext"). }
                 { rgall. iEval (rewrite Hnwaddr2). iExact "Hnw". }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hnw". rgall.
                 iEval (rewrite Hnwaddr2) in "Hnw".
                 pose (P1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw)]> mr).
                 change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw)]> mr) with P1.
                 assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xc2) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xc6)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppc2) in "Hpc".
                 assert (Ha5P1 : P1 !!! Regidx Ra5 = sign_extend' 64 nw) by (rewrite /P1; apply upd_eq).
                 (* +0xc6 addiw a4,a5,1 *)
                 iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xc6)) Ra4 Ra5
                           (mword_of_int 1 : mword 12) P1 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok)
                           with "Hcg Hpc []").
                 { iApply (pwi_c6 with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 pose (P2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> P1).
                 change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> P1) with P2.
                 assert (Hppc6 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xc6) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xca)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppc6) in "Hpc".
                 assert (HX1 : (subrange_vec_dec (add_vec (sign_extend' 64 nw : mword 64)
                                  (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0 : mword 32)
                               = add_vec nw (mword_of_int 1 : mword 32))
                   by (apply (pw_addiw_lit nw (mword_of_int 1 : mword 12) 1); vm_compute; reflexivity).
                 assert (Ha4P2 : P2 !!! Regidx Ra4 = sign_extend' 64 (add_vec nw (mword_of_int 1 : mword 32))).
                 { rewrite /P2 upd_eq. unfold regval_into_reg. rewrite Ha5P1 HX1. reflexivity. }
                 assert (Hstore : trunc32 (P2 !!! Regidx Ra4) = add_vec nw (mword_of_int 1 : mword 32))
                   by (rewrite Ha4P2; apply trunc32_sext64).
                 (* +0xca sw a4,540(s1) *)
                 assert (Hnwaddr3 : add_vec (P2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi).
                 { rewrite /P2 upd_ne; [| reg_neq]. rewrite /P1 upd_ne; [| reg_neq].
                   rewrite Rs1f. reflexivity. }
                 (* [rget]-spelled restatement -- the leaf's [pa] is written
                    with [rget], not [!!!]; see the [Strategy opaque] comment
                    above. *)
                 assert (Hnwaddr3r : add_vec (rget P2 Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi)
                   by (rewrite rget_ne; [exact Hnwaddr3 | vm_compute; discriminate]).
                 iEval (rewrite -Hnwaddr3r) in "Hnw".
                 iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xca)) Ra4 Rs1
                           (mword_of_int 540 : mword 12) P2 (trap_res true + (av - 14))%nat nw false
                           with "Hcg Hpc [] Hnw").
                 { iApply (pwi_ca with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hnw". rgall.
                 iEval (rewrite Hstore Hnwaddr3) in "Hnw".
                 assert (Hppca : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xca) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xce)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppca) in "Hpc".
                 assert (Hcnt' : pipe_count_ok nr (add_vec nw (mword_of_int 1 : mword 32)))
                   by (apply pipe_count_incr_w; [exact Hcnt | exact Hne]).
                 (* +0xce andi a5,a5,511 -- the %PIPESIZE index *)
                 assert (Ha5P2 : P2 !!! Regidx Ra5 = sign_extend' 64 nw)
                   by (rewrite /P2 upd_ne; [exact Ha5P1 | reg_neq]).
                 iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xce)) Ra5 Ra5
                           (mword_of_int 511 : mword 12)
                           (and_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 (mword_of_int 511 : mword 12)))
                           P2 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) ltac:(rgall; rewrite Ha5P2; reflexivity)
                           with "Hcg Hpc []").
                 { iApply (pwi_ce with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 pose (P3 := <[Regidx Ra5 := regval_into_reg
                     (and_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 (mword_of_int 511 : mword 12)))]> P2).
                 change (<[Regidx Ra5 := regval_into_reg
                     (and_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 (mword_of_int 511 : mword 12)))]> P2) with P3.
                 assert (Hppce : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xce) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xd2)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppce) in "Hpc".
                 (* +0xd2 c.add a5,a5,s1 *)
                 iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xd2)) Ra5 Rs1 P3 (trap_res true + (av - 14))%nat false
                           ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
                 { iApply (pwi_d2 with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 pose (P4 := <[Regidx Ra5 := regval_into_reg
                     (add_vec (P3 !!! Regidx Ra5) (P3 !!! Regidx Rs1))]> P3).
                 change (<[Regidx Ra5 := regval_into_reg
                     (add_vec (P3 !!! Regidx Ra5) (P3 !!! Regidx Rs1))]> P3) with P4.
                 assert (Hppd0 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd2) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xd4)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppd0) in "Hpc".
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
                 (* +0xd4 lbu a4,-97(s0) -- the byte copyin just wrote *)
                 assert (Hchaddr : add_vec (P4 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3999 : mword 12))
                                   = pa_add (pa_stk sp0 13%nat) 7%nat)
                   by (rewrite Hs0P4; apply pw_ch_addr).
                 iEval (rewrite -Hchaddr) in "Hch".
                 iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xd4)) Ra4 Rs0
                           (mword_of_int 3999 : mword 12) P4 (trap_res true + (av - 14))%nat ((dst_new 0%nat) : mword 8) false
                           ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hch").
                 { iApply (pwi_d4 with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hch". rgall.
                 iEval (rewrite Hchaddr) in "Hch".
                 pose (P5 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 ((dst_new 0%nat) : mword 8))]> P4).
                 change (<[Regidx Ra4 := regval_into_reg (zero_extend' 64 ((dst_new 0%nat) : mword 8))]> P4) with P5.
                 assert (Hppd4 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd4) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppd4) in "Hpc".
                 (* the [ch] byte goes back into the frame slot *)
                 iDestruct ("Hchback" $! (dst_new 0%nat) with "Hch") as "Hb13".
                 iDestruct (pw_chslot_mk sp0 Hal13 with "Hb13 Hslot14") as "HCH".
                 (* +0xd8 sb a4,24(a5) -- into pi->data[nwrite % PIPESIZE] *)
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
                 iEval (rewrite -Hsbaddr) in "Hcell".
                 iApply (wp_sb_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xd8)) Ra4 Ra5
                           (mword_of_int 24 : mword 12) P5 (trap_res true + (av - 14))%nat b1 false
                           with "Hcg Hpc [] Hcell").
                 { iApply (pwi_d8 with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell". rgall.
                 iEval (rewrite Hsbaddr) in "Hcell".
                 iDestruct ("Hdatback" $! (trunc8 (P5 !!! Regidx Ra4)) with "Hcell") as "Hdat".
                 assert (Hbslen' : length (<[idx := trunc8 (P5 !!! Regidx Ra4)]> bs) = PIPESIZE)
                   by (rewrite length_insert; exact Hbslen).
                 assert (Hppd8 : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xd8) : mword 64) 4 = mword_of_int (KernelSyms.pipewrite + 0xdc)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppd8) in "Hpc".
                 (* +0xdc c.addiw s2,s2,1 *)
                 iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xdc)) Rs2 (mword_of_int 1 : mword 6)
                           P5 (trap_res true + (av - 14))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
                 { iApply (pwi_dc with "Htext"). }
                 iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
                 pose (P6 := <[Regidx Rs2 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P5 !!! Regidx Rs2) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> P5).
                 change (<[Regidx Rs2 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
                     (add_vec (P5 !!! Regidx Rs2) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> P5) with P6.
                 assert (Hppda : add_vec_int (mword_of_int (KernelSyms.pipewrite + 0xdc) : mword 64) 2 = mword_of_int (KernelSyms.pipewrite + 0xde)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hppda) in "Hpc".
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
                 iAssert (pipe_res γp pi) with "[Hrest Hnr Hnw Hro Hdat]" as "Hres".
                 { iApply (pw_res_intro_rest γp pi nr (add_vec nw (mword_of_int 1 : mword 32)) ro wo vname
                             (<[idx := trunc8 (P5 !!! Regidx Ra4)]> bs) Hcnt' Hbslen'
                             with "Hrest Hnr Hnw Hro Hdat"). }
                 (* +0xde c.j -> the guard, with i+1 *)
                 iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0xde))
                           (sign_extend' 21 (concat_vec (mword_of_int 2005 : mword 11) ('b"0")))
                           P6 (trap_res true + (av - 14))%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
                 { iApply (pwi_de with "Htext"). }
                 iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc". rgall.
                 assert (Hj88 : add_vec (mword_of_int (KernelSyms.pipewrite + 0xde) : mword 64)
                                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2005 : mword 11) ('b"0"))))
                                = mword_of_int (KernelSyms.pipewrite + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
                 iEval (rewrite Hj88) in "Hpc".
                 iApply (pw_guard_step (CID := CIDlp) CID γa γf γs j γl γp w q m av true lks pid V n sp0 pi addr
                           (i + 1)%Z P6 P' Hn0 Hn31 ltac:(lia) ltac:(wp_next_chain) Hext' HregsP6
                           with "Htext HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href Hpriv Henv HEX IH"). }
      (* ---- +0x44 c.j -> the loop body, with i = 0 ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.pipewrite + 0x44))
                (sign_extend' 21 (concat_vec (mword_of_int 36 : mword 11) ('b"0")))
                C6 (trap_res true + (av - 14))%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (pwi_44 with "Htext"). }
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj8c : add_vec (mword_of_int (KernelSyms.pipewrite + 0x44) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 36 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.pipewrite + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hj8c) in "Hpc".
      rewrite /pw_loop.
      iSpecialize ("LOOP" $! CIDaq with "[%]"); [wp_next_chain|].
      iApply ("LOOP" $! 0%Z C6 (pv_upt V) with "[%] [%] [%] HF7 HF5 HCH Hcg Hown Hpay Hlocked Hres Hpc Href [Hpriv] Henv EXITS").
      + lia.
      + apply uptd_ext_refl.
      + exact HregsC6.
      + rewrite pw_upd_upt_id. iExact "Hpriv".
  Qed.


End ProofPipewrite.
End PipewriteProof.
