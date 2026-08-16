(* ProofSysUnlinkParts.v -- sys_unlink's PURE side conditions and its frame
   arithmetic: everything the walk needs that does not apply a callee's
   contract, and therefore everything that can live outside the module
   functor.

   The walk itself is [ProofSysUnlink.v]; the op-wide log ledger is
   [SysUnlinkBudget.v]; the contract is [SpecSysUnlink.v], whose header
   carries the arm graph and the frame map.

   NOTHING HERE IS IMPORTED FROM ANOTHER FUNCTION'S PROOF.  The clusters
   below are restated rather than taken from [ProofSysLinkParts] /
   [ProofSysOpenParts]: a whole-function proof file is not a dependency any
   other one may take.

   THREE THINGS ARE sys_unlink's OWN, and they are why this file is not a
   rename of [ProofSysLinkParts.v]:

   * BOTH DECREMENTS ARE [lhu], SO THEY SHARE ONE CLUSTER.  sys_link's [++]
     reuses the SIGN-extended [lh] the NLINK_MAX guard already loaded, while
     its [--] does its own ZERO-extended [lhu], so the two needed separate
     chains.  sys_unlink has no [++] at all and both of its [--]s
     ([ip->nlink--] at +0xbe..+0xc4 off s2, [dp->nlink--] at +0x146..+0x14c
     off s1) are [lhu] / [c.addiw -1] / [sh] -- the same three instructions
     at two addresses -- so ONE cluster ([su_nlink_decr]) serves both flushes.
   * THE PANIC GUARD IS A [blez], i.e. a [bge] WITH x0 IN rs1.  [ip->nlink < 1]
     compiled to [bge zero,a5] at +0x7c, so the leaf is
     [WpSconfBtype.wp_bge_x0_*] and the pure side condition is over
     [zopz0zKzJ_s zero_reg _].  Its FALL-THROUGH is what hands the walk
     [di_nlink ip <> 0] -- the liveness [DirView.dir_dots_ix]'s guard wants,
     and the only place it comes from.
   * [off] IS NOT SLOT-ALIGNED.  [uint off] lives at [s0-212], the UPPER word
     of slot 27, so [su_offcell] is [ProofSysOpenParts.so_omode]'s shape and
     carries the same warning: never [vm_compute] an address goal with a free
     [X] in it. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelRvcDecode.
Require Import BvShift.
Require Import StackOwn StackBytes.
Require Import CalleeSaved KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeHalf.
Require Import IntrDefs.
Require Import ByteBuf.
Require Import ProcGeom.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIupdate.
Require Import SpecIunlockput.
Require Import SpecNamecmp.
Require Import SpecDirlookup.
Require Import SpecReadi.
Require Import SpecWritei.
Require Import SpecNameiparent.
Require Import CodeSysUnlink.
Require Import SpecSysUnlink.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

Notation SU := KernelSyms.sys_unlink (only parsing).

(* ===================================================================== *)
(*  THE REGISTER LEDGER                                                   *)
(* ===================================================================== *)

(* the five registers this frame moves: sp, s0 (the frame pointer),
   s1 = dp, s2 = ip, s3 (dual-use: isdirempty's [off] counter, then the
   address of writei's [de]).  Everything else callee-saved rides straight
   through, and it is stated POSITIVELY -- the five exceptions are exactly
   the five the code writes, each accounted for by its own equation. *)
Definition su_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) ->
    c <> (mword_of_int 19 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma su_thr_refl (m : regfile) : su_thr m m.
Proof. intros c _ _ _ _ _ _. reflexivity. Qed.

Lemma su_thr_trans (m M P : regfile) : su_thr m M -> su_thr M P -> su_thr m P.
Proof.
  intros H1 H2 c Hc N2 N8 N9 N18 N19.
  rewrite (H2 c Hc N2 N8 N9 N18 N19). exact (H1 c Hc N2 N8 N9 N18 N19).
Qed.

Definition su_sp (sp0 : mword 64) (M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk sp0 30.

(* ===================================================================== *)
(*  THE FRAME ARITHMETIC -- 240 bytes, THIRTY slots                       *)
(* ===================================================================== *)

(* -240 / +240, both a [c.addi16sp] (49 is -15 in a 6-bit field, x16;
   15 is +15). *)
Lemma su_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 49 : mword 6)))
  = pa_stk X 30.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_pop (X : mword 64) :
  add_vec (pa_stk X 30) (sign_extend' 64 (caddi16sp_imm (mword_of_int 15 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,240] -- the frame pointer, back at the entry sp. *)
Lemma su_fp (X : mword 64) :
  add_vec (pa_stk X 30) (sign_extend' 64 (caddi4spn_imm (mword_of_int 60 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* the four SLOT-ALIGNED bases, off the frame pointer (which IS the entry
   sp): [path] at -208 (+0x0c / +0x24), [name] at -80 (+0x20 / +0x3c /
   +0x50 / +0x62), writei's [de] at -64 (+0x8a), isdirempty's [de] at
   -232 (+0x10a, and the [lhu] at +0x11c). *)
Lemma su_bufpath (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3888 : mword 12)) = pa_stk X 26.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_bufname (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4016 : mword 12)) = pa_stk X 10.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_bufde (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4032 : mword 12)) = pa_stk X 8.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_bufdel (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3864 : mword 12)) = pa_stk X 29.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* [uint off] at [s0-212]: the UPPER WORD of slot 27 (+0x5e writes its
   address into a2 for dirlookup, +0x9a reads it back for writei).  This is
   the ONLY place sys_unlink needs a 4-byte view of a frame slot. *)
Lemma su_offcell (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3884 : mword 12))
  = pa_add (pa_stk X 27) 4.
Proof.
  (* NEVER [vm_compute] this goal whole: [X] is free, so the bytecode
     evaluator unfolds the whole 64-bit adder against an open term and the
     process dies with "allocation failure during minor GC" -- which reads
     like a resource limit and is a proof-shape mistake.  Compose the two
     shifts SYMBOLICALLY first ([avi_assoc]); what is left is CLOSED. *)
  unfold pa_add, pa_stk. rewrite avi_assoc. unfold add_vec_int.
  f_equal. all: apply bv_eq; vm_compute; reflexivity.
Qed.

(* the c.sdsp / c.ldsp displacements off the pushed sp *)
Lemma su_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (bv_wrap 64 (uint (mword_of_int (- (8 * Z.of_nat 30)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 30) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite pa_stk_off2. apply f_equal. exact H.
Qed.

Lemma su_frm1 (X : mword 64) :
  add_vec (pa_stk X 30)
    (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply su_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_frm2 (X : mword 64) :
  add_vec (pa_stk X 30)
    (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply su_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_frm3 (X : mword 64) :
  add_vec (pa_stk X 30)
    (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply su_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_frm4 (X : mword 64) :
  add_vec (pa_stk X 30)
    (zero_extend' 64 (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply su_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_frm5 (X : mword 64) :
  add_vec (pa_stk X 30)
    (zero_extend' 64 (concat_vec (mword_of_int 25 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. apply su_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* [K_sys_unlink]'s single premise, turned into every bound the ten callees
   and the [sie_cap_gpr] pop want.  memset's own frame is two slots, which
   is the [2 <= K - 30] conjunct. *)
Lemma su_kb (K : nat) : (K_sys_unlink <= K)%nat ->
  (K_nameiparent <= K - 30)%nat /\ (K_dirlookup <= K - 30)%nat /\
  (K_readi <= K - 30)%nat /\ (K_writei <= K - 30)%nat /\
  (argstr_stack <= K - 30)%nat /\
  (K_begin_op <= K - 30)%nat /\ (K_end_op <= K - 30)%nat /\
  (K_ilock <= K - 30)%nat /\ (K_iupdate <= K - 30)%nat /\
  (K_iunlockput <= K - 30)%nat /\ (K_namecmp <= K - 30)%nat /\
  (2 <= K - 30)%nat /\ (10 <= K - 30)%nat /\
  (30 <= K)%nat /\ ((K - 30) + 30 = K)%nat.
Proof.
  unfold K_sys_unlink, K_nameiparent, K_dirlookup, K_readi, K_writei,
         argstr_stack, K_begin_op, K_end_op, K_ilock, K_iupdate,
         K_iunlockput, K_namecmp.
  intro H. split_and!; lia.
Qed.

(* ===================================================================== *)
(*  THE SIGN CLUSTER: the [bltz] at +0x16 (argstr's return)               *)
(* ===================================================================== *)

Lemma su_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned. rewrite bvw64_small; [| lia].
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity. rewrite Hhm.
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

Lemma su_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (su_sint_moi z Hz). lia.
Qed.

Lemma su_m1_neg :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma su_len_range (k : nat) : (k < 128)%nat -> (0 <= Z.of_nat k < 2 ^ 31)%Z.
Proof.
  intro Hk.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

Lemma su_maxpath_lt : (Z.of_nat 128 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma su_arg0_lt : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

(* ===================================================================== *)
(*  THE PANIC GUARD: [blez a5] at +0x7c, i.e. [bge x0,a5]                  *)
(*                                                                        *)
(*  [WpSconfBtype.wp_bge_x0_*] is the leaf, so the side condition is over  *)
(*  [zopz0zKzJ_s zero_reg _] with the SIGN-extended halfword on the right. *)
(*  The FALL-THROUGH arm is what the whole T_DIR story rests on: it is the *)
(*  only source of [di_nlink ip <> 0], which is [DirView.dir_dots_ix]'s    *)
(*  own guard.                                                            *)
(* ===================================================================== *)

Lemma su_sext16_sint (h : mword 16) :
  sint (sign_extend' 64 h : mword 64) = bv_signed h.
Proof.
  change (sint ?x) with (bv_signed x).
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_signed; [reflexivity |].
  apply N.leb_le; vm_compute; reflexivity.
Qed.

(* the guard FALLS THROUGH (the count is signed-positive, i.e. the inode is
   live) *)
Lemma su_nlink_pos_fall (h : mword 16) : (0 < bv_signed h)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (sign_extend' 64 h : mword 64) = false.
Proof.
  intro Hp. unfold zopz0zKzJ_s. rewrite Z.geb_leb. apply Z.leb_gt.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite su_sext16_sint. exact Hp.
Qed.

(* ...and the guard is TAKEN (the panic arm, which never returns) *)
Lemma su_nlink_pos_taken (h : mword 16) : (bv_signed h <= 0)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (sign_extend' 64 h : mword 64) = true.
Proof.
  intro Hp. unfold zopz0zKzJ_s. rewrite Z.geb_leb. apply Z.leb_le.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite su_sext16_sint. exact Hp.
Qed.

(* WHAT THE FALL-THROUGH BUYS, and it is the whole point of the guard: a
   signed-positive count is a NONZERO count, which is
   [DirView.dir_dots_ix]'s guard and [DirLinks.dir_link_at_unlink]'s
   home-live premise in the other direction. *)
Lemma su_signed_pos_nz (h : mword 16) : (0 < bv_signed h)%Z ->
  bv_unsigned h <> 0%Z.
Proof.
  intros Hp Hz.
  assert (Hh : h = (mword_of_int 0 : mword 16))
    by (apply bv_eq; rewrite Hz; vm_compute; reflexivity).
  assert (Hs : bv_signed (mword_of_int 0 : mword 16) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hh Hs in Hp. exact (Z.lt_irrefl 0%Z Hp).
Qed.

(* the CONTRAPOSITIVE reading, which the walk uses at the panic arm to see
   that a zero count is refuted by whatever it holds *)
Lemma su_nz_signed_pos (h : mword 16) :
  (bv_signed h <= 0)%Z -> (0 < bv_signed h)%Z -> False.
Proof. lia. Qed.

(* ===================================================================== *)
(*  THE SIXTEEN-BIT COMPARE CLUSTER: the two T_DIR tests, at +0x86         *)
(*  (before the isdirempty loop) and at +0xb4 (after the zeroing).  BOTH   *)
(*  are [beq] against a sign-extended [lh] of [ip->type] and the literal   *)
(*  one, so both go through the same injectivity lemma.                    *)
(* ===================================================================== *)

Lemma su_sext16_inj (x y : mword 16) :
  (sign_extend' 64 x : mword 64) = (sign_extend' 64 y : mword 64) -> x = y.
Proof.
  intros H. apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H;
    [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

Lemma su_sext_one :
  (sign_extend' 64 (mword_of_int 1 : mword 16) : mword 64)
  = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* both tests are [beq a5,a4] with a4 = sign_extend(ip->type) and
   a5 = [c.li 1]: the branch CONDITION is [eq_vec a4 a5]. *)
Lemma su_tdir_eq (t : mword 16) : t = (mword_of_int 1 : mword 16) ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = true.
Proof.
  intros ->. rewrite su_sext_one.
  exact (proj2 (eq_vec_true_iff _ _) eq_refl).
Qed.

Lemma su_tdir_ne (t : mword 16) : t <> (mword_of_int 1 : mword 16) ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)).
  intro Hc. apply Hne. apply su_sext16_inj. rewrite Hc su_sext_one.
  reflexivity.
Qed.

(* the [c.li a5,1] the two tests compare against, and [T_DIR] as a
   halfword: the walk holds [bv_unsigned (di_type dn) = T_DIR_z] or its
   negation, and this is the bridge to the literal. *)
Lemma su_tdir_z (t : mword 16) :
  bv_unsigned t = T_DIR_z -> t = (mword_of_int 1 : mword 16).
Proof.
  intro Ht. apply bv_eq. rewrite Ht. vm_compute. reflexivity.
Qed.

Lemma su_tdir_z_ne (t : mword 16) :
  bv_unsigned t <> T_DIR_z -> t <> (mword_of_int 1 : mword 16).
Proof.
  intros Ht Hc. apply Ht. rewrite Hc. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  THE "== sizeof(de)" CLUSTER: the [bne a0,a5] at +0xaa (writei's        *)
(*  return) and at +0x118 (readi's).  Both compare a 64-bit return value   *)
(*  against the [c.li a5,16] literal, so both are one lemma pair over      *)
(*  [mword_of_int (Z.of_nat tot)].                                        *)
(* ===================================================================== *)

Lemma su_li16 :
  (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
  = (mword_of_int 16 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_moi64_small_inj (a c : Z) :
  (0 <= a < 2 ^ 63)%Z -> (0 <= c < 2 ^ 63)%Z ->
  (mword_of_int a : mword 64) = (mword_of_int c : mword 64) -> a = c.
Proof.
  intros Ha Hc H. apply (f_equal bv_unsigned) in H.
  rewrite !moi64_unsigned in H.
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  rewrite !bvw64_small in H; lia.
Qed.

Lemma su_tot16_eq (tot : nat) : (tot <= 16)%nat ->
  eq_vec (mword_of_int (Z.of_nat tot) : mword 64) (mword_of_int 16 : mword 64)
  = true -> tot = 16%nat.
Proof.
  intros Hle Heq.
  assert (Hm : (mword_of_int (Z.of_nat tot) : mword 64)
               = (mword_of_int 16 : mword 64))
    by exact (proj1 (eq_vec_true_iff _ _) Heq).
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  assert (H : Z.of_nat tot = 16%Z)
    by (apply su_moi64_small_inj; [lia | lia | exact Hm]).
  lia.
Qed.

Lemma su_tot16_ne (tot : nat) : (tot <= 16)%nat -> tot <> 16%nat ->
  eq_vec (mword_of_int (Z.of_nat tot) : mword 64) (mword_of_int 16 : mword 64)
  = false.
Proof.
  intros Hle Hne. apply (proj2 (eq_vec_false_iff _ _)). intro Hc.
  apply Hne. exact (su_tot16_eq tot Hle (proj2 (eq_vec_true_iff _ _) Hc)).
Qed.

(* ===================================================================== *)
(*  THE isdirempty LOOP'S OWN ARITHMETIC                                  *)
(*                                                                        *)
(*  Three tests and one bump, all thirty-two bit and all UNSIGNED, which   *)
(*  is right: [off] and [dp->size] are both [uint].                       *)
(*    +0x100  [bgeu a5,a4]  with a5 = 32, a4 = ip->size  (the entry test)  *)
(*    +0x128  [bltu s3,a5]  with a5 = ip->size           (the back edge)   *)
(*    +0x122  [c.addiw s3,s3,16]                         (the bump)        *)
(*    +0x120  [c.bnez a5]   with a5 = zero_extend(de.inum) (the answer)    *)
(* ===================================================================== *)

Lemma su_li32 :
  (sign_extend' 64 (mword_of_int 32 : mword 12) : mword 64)
  = (mword_of_int 32 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_uint_moi (z : Z) : (0 <= z < 18446744073709551616)%Z ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro Hz. rewrite uint_unsigned. apply moi64_small. exact Hz. Qed.

Lemma su_u31_range (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  (0 <= z < 18446744073709551616)%Z.
Proof.
  intro Hz.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* the entry test at +0x100: [32 >=u size] TAKES the branch (the directory
   holds nothing past its two dots, so it IS empty). *)
Lemma su_loop_entry_taken (sz : Z) : (0 <= sz <= 32)%Z ->
  zopz0zKzJ_u (mword_of_int 32 : mword 64) (mword_of_int sz : mword 64) = true.
Proof.
  intro Hsz. unfold zopz0zKzJ_u.
  rewrite (su_uint_moi 32%Z ltac:(lia)) (su_uint_moi sz ltac:(lia)).
  rewrite Z.geb_leb. apply Z.leb_le. lia.
Qed.

Lemma su_loop_entry_fall (sz : Z) : (32 < sz < 2 ^ 31)%Z ->
  zopz0zKzJ_u (mword_of_int 32 : mword 64) (mword_of_int sz : mword 64) = false.
Proof.
  intro Hsz.
  assert (Hr : (0 <= sz < 18446744073709551616)%Z)
    by (apply su_u31_range; lia).
  unfold zopz0zKzJ_u.
  rewrite (su_uint_moi 32%Z ltac:(lia)) (su_uint_moi sz Hr).
  rewrite Z.geb_leb. apply Z.leb_gt. lia.
Qed.

(* the back edge at +0x128: [off <u size] RE-ENTERS the body. *)
Lemma su_loop_back_taken (off sz : Z) :
  (0 <= off < sz)%Z -> (sz < 2 ^ 31)%Z ->
  zopz0zI_u (mword_of_int off : mword 64) (mword_of_int sz : mword 64) = true.
Proof.
  intros Hoff Hsz.
  assert (Hrs : (0 <= sz < 18446744073709551616)%Z)
    by (apply su_u31_range; lia).
  assert (Hro : (0 <= off < 18446744073709551616)%Z)
    by (apply su_u31_range; lia).
  unfold zopz0zI_u.
  rewrite (su_uint_moi off Hro) (su_uint_moi sz Hrs).
  apply Z.ltb_lt. lia.
Qed.

Lemma su_loop_back_fall (off sz : Z) :
  (0 <= sz <= off)%Z -> (off < 2 ^ 31)%Z ->
  zopz0zI_u (mword_of_int off : mword 64) (mword_of_int sz : mword 64) = false.
Proof.
  intros Hoff Hsz.
  assert (Hrs : (0 <= sz < 18446744073709551616)%Z)
    by (apply su_u31_range; lia).
  assert (Hro : (0 <= off < 18446744073709551616)%Z)
    by (apply su_u31_range; lia).
  unfold zopz0zI_u.
  rewrite (su_uint_moi off Hro) (su_uint_moi sz Hrs).
  apply Z.ltb_ge. lia.
Qed.

(* the [c.bnez a5] at +0x120: [a5] is the ZERO-extended [de.inum] halfword,
   so the branch is taken exactly when the record is LIVE. *)
Lemma su_inum_zero (w : mword 16) : bv_unsigned w = 0%Z ->
  eq_vec (zero_extend' 64 w : mword 64) (zero_reg : mword 64) = true.
Proof.
  intro Hw. apply (proj2 (eq_vec_true_iff _ _)). apply bv_eq.
  rewrite (bv_zero_extend_unsigned 64 w ltac:(vm_compute; discriminate)).
  rewrite Hw. reflexivity.
Qed.

Lemma su_inum_nz (w : mword 16) : bv_unsigned w <> 0%Z ->
  eq_vec (zero_extend' 64 w : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hw. apply (proj2 (eq_vec_false_iff _ _)). intro Hc.
  apply Hw. apply (f_equal bv_unsigned) in Hc.
  rewrite (bv_zero_extend_unsigned 64 w ltac:(vm_compute; discriminate)) in Hc.
  rewrite Hc. reflexivity.
Qed.

(* ===================================================================== *)
(*  THE [--] CLUSTER: [lhu] (zero), [c.addiw -1], [sh].                   *)
(*                                                                        *)
(*  ONE cluster for BOTH flushes.  [ip->nlink--] at +0xbe..+0xc4 (off s2)  *)
(*  and [dp->nlink--] at +0x146..+0x14c (off s1) are the same three        *)
(*  instructions at two addresses -- unlike sys_link, whose [++] reused a  *)
(*  SIGN-extended [lh] and therefore needed a second chain.               *)
(* ===================================================================== *)

Lemma su_uns16 (h : mword 16) : (0 <= bv_unsigned h < 65536)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ h) as H0. unfold bv_modulus in H0.
  exact H0.
Qed.

Definition su_dinner (h : mword 16) : bv 32 :=
  bv_extract 0 32 (bv_add (bv_zero_extend 64 h)
      (bv_sign_extend 64 (bv_sign_extend 12 (mword_of_int 63 : mword 6)))).

Lemma su_dinner_unsigned (h : mword 16) :
  bv_unsigned (su_dinner h)
  = ((bv_unsigned h + 18446744073709551615) `mod` 4294967296)%Z.
Proof.
  unfold su_dinner.
  rewrite bv_extract_unsigned bv_add_unsigned.
  rewrite (bv_zero_extend_unsigned 64 h ltac:(vm_compute; discriminate)).
  assert (Hc : bv_unsigned (bv_sign_extend 64
                  (bv_sign_extend 12 (mword_of_int 63 : mword 6)) : bv 64)
               = 18446744073709551615%Z)
    by (vm_compute; reflexivity).
  rewrite Hc.
  change (Z.of_N 0) with 0%Z.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite mod_2_64_32. reflexivity.
Qed.

Lemma su_dbump_bv (h : mword 16) :
  bv_unsigned (trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (zero_extend' 64 h : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))
         : mword 64)) 31 0)))
  = bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (su_dinner h))).
Proof. reflexivity. Qed.

Lemma su_dbump_unsigned (h : mword 16) :
  bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (su_dinner h)))
  = ((bv_unsigned h + 18446744073709551615) `mod` 65536)%Z.
Proof.
  rewrite bv_extract_unsigned bv_sign_extend_unsigned.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (2 ^ Z.of_N 16)%Z with 65536%Z.
  rewrite mod_2_64_16 swrap_low_32_16 su_dinner_unsigned mod_2_32_16.
  reflexivity.
Qed.

(* THE CLAUSE [SpecIupdate.wp_iupdate_unlink] ACTUALLY TAKES, and it is the
   Z one: the OLD count is the new one plus one.  Sound at BOTH flushes
   because the [blez] at +0x7c is walked before either -- for [ip] the
   count is literally the one the guard tested, and for [dp] it is the one
   [IregLinkNz.ireg_link_nz] reads off the [ilink] the ".." record's ticket
   supplies. *)
Lemma su_nlink_decr (h : mword 16) :
  bv_unsigned h <> 0%Z ->
  bv_unsigned h
  = (bv_unsigned (trunc16 (sign_extend' 64 (subrange_vec_dec
       (add_vec (zero_extend' 64 h : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))
           : mword 64)) 31 0))) + 1)%Z.
Proof.
  intro Hnz. rewrite su_dbump_bv su_dbump_unsigned.
  pose proof (su_uns16 h) as Hr.
  assert (Hstep : ((bv_unsigned h + 18446744073709551615) `mod` 65536)%Z
                  = (bv_unsigned h - 1)%Z).
  { replace (bv_unsigned h + 18446744073709551615)%Z
       with ((bv_unsigned h - 1) + 281474976710656 * 65536)%Z by lia.
    rewrite (Z.mod_add (bv_unsigned h - 1)%Z 281474976710656%Z 65536%Z
               ltac:(lia)).
    exact (Z.mod_small (bv_unsigned h - 1)%Z 65536%Z ltac:(lia)). }
  rewrite Hstep. lia.
Qed.

(* ===================================================================== *)
(*  THE RECORD EITHER FLUSH WRITES                                        *)
(*                                                                        *)
(*  Both [--]s move ONE halfword, so the new record is the old one with    *)
(*  [di_nlink] replaced -- and every pure clause a re-park owes            *)
(*  ([InodeLock.inode_ok], [DirView.dir_ok]) reads only the type, the size *)
(*  and the addrs, so all three ride the change by [reflexivity].          *)
(* ===================================================================== *)

Definition su_setnl (dn : dinode) (nl : mword 16) : dinode :=
  MkDinode (di_type dn) (di_major dn) (di_minor dn) nl (di_size dn)
           (di_addrs dn).

Lemma su_setnl_type (dn : dinode) (nl : mword 16) :
  di_type (su_setnl dn nl) = di_type dn.
Proof. reflexivity. Qed.

Lemma su_setnl_nlink (dn : dinode) (nl : mword 16) :
  di_nlink (su_setnl dn nl) = nl.
Proof. reflexivity. Qed.

Lemma su_setnl_size (dn : dinode) (nl : mword 16) :
  di_size (su_setnl dn nl) = di_size dn.
Proof. reflexivity. Qed.

Lemma su_setnl_addrs (dn : dinode) (nl : mword 16) :
  di_addrs (su_setnl dn nl) = di_addrs dn.
Proof. reflexivity. Qed.

Lemma su_setnl_inode_ok (cov : gset Z) (ls : Z) (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (nl : mword 16) :
  inode_ok cov ls dn bm data -> inode_ok cov ls (su_setnl dn nl) bm data.
Proof. unfold inode_ok, su_setnl. cbn. exact (fun H => H). Qed.

Lemma su_setnl_dir_ok (nib : nat) (dn : dinode) (data : nat -> list (bv 8))
    (nl : mword 16) :
  dir_ok nib dn data -> dir_ok nib (su_setnl dn nl) data.
Proof. unfold dir_ok, su_setnl. cbn. exact (fun H => H). Qed.

(* [di_type_stable] / [di_nlink_stable], which every flush's contract takes
   over the record it is REBUILDING: the type is untouched and the count is
   exactly the one the store committed. *)
Lemma su_setnl_type_stable (dn : dinode) (nl : mword 16) :
  di_type_stable (su_setnl dn nl) dn.
Proof. apply di_type_stable_eq. reflexivity. Qed.
