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
Require Import IcacheRef.
Require Import DirLinks.
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
(*  THE REGISTER BUNDLE -- [ProofSysLink.sl_regs]' shape at FIVE pinned    *)
(*  registers, with [su_thr] as the fifth conjunct                         *)
(*                                                                        *)
(*  A whole-function walk that carries its pinned registers as a per-      *)
(*  register [assert] chain pays the same proof once per register per      *)
(*  instruction; sys_link showed the shape at four and sys_unlink needs    *)
(*  FIVE (sp, s0, s1 = dp, s2 = ip, s3 = the dual-use counter/address), so *)
(*  the chain is 25 % longer again.  The bundle plus its three movers --   *)
(*  a CALLER-saved write, a callee's [callee_saved] report, and a write to *)
(*  one of the three pinned callee-saved registers -- is what the walk     *)
(*  threads instead.                                                       *)
(*                                                                        *)
(*  s0 IS [sp0], NOT a slot: [c.addi4spn s0,sp,240] at +0x06 puts the      *)
(*  frame pointer back at the ENTRY sp ([su_fp]), which is why every       *)
(*  buffer base below is off [sp0] and not off the pushed sp.              *)
(* ===================================================================== *)

Local Ltac su_rne1 Hf :=
  first [ apply is_cs_idx_true_neq; [exact Hf | vm_compute; reflexivity]
        | apply not_eq_sym; apply is_cs_idx_true_neq;
          [exact Hf | vm_compute; reflexivity] ].

Local Ltac su_rne2 Hf Ht :=
  first [ apply is_cs_idx_true_neq; [exact Hf | exact Ht]
        | apply not_eq_sym; apply is_cs_idx_true_neq; [exact Hf | exact Ht] ].

Local Ltac su_xne N :=
  let Hq := fresh "Hq" in
  intro Hq; apply N;
  first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ].

Local Ltac sunz := vm_compute; discriminate.

Definition su_regs (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile)
  : Prop :=
  Mx !!! Regidx csp_rs1 = pa_stk sp0 30
  /\ Mx !!! Regidx (mword_of_int 8 : mword 5) = sp0
  /\ Mx !!! Regidx (mword_of_int 9 : mword 5) = dpv
  /\ Mx !!! Regidx (mword_of_int 18 : mword 5) = ipv
  /\ Mx !!! Regidx (mword_of_int 19 : mword 5) = s3v
  /\ su_thr m Mx.

Lemma su_regs_sp (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile) :
  su_regs m sp0 dpv ipv s3v Mx -> su_sp sp0 Mx.
Proof. intros (H & _). exact H. Qed.

Lemma su_regs_s0 (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile) :
  su_regs m sp0 dpv ipv s3v Mx ->
  (Mx !!! Regidx (mword_of_int 8 : mword 5) : mword 64) = sp0.
Proof. intros (_ & H & _). exact H. Qed.

Lemma su_regs_s1 (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile) :
  su_regs m sp0 dpv ipv s3v Mx ->
  (Mx !!! Regidx (mword_of_int 9 : mword 5) : mword 64) = dpv.
Proof. intros (_ & _ & H & _). exact H. Qed.

Lemma su_regs_s2 (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile) :
  su_regs m sp0 dpv ipv s3v Mx ->
  (Mx !!! Regidx (mword_of_int 18 : mword 5) : mword 64) = ipv.
Proof. intros (_ & _ & _ & H & _). exact H. Qed.

Lemma su_regs_s3 (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile) :
  su_regs m sp0 dpv ipv s3v Mx ->
  (Mx !!! Regidx (mword_of_int 19 : mword 5) : mword 64) = s3v.
Proof. intros (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma su_regs_thr (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile) :
  su_regs m sp0 dpv ipv s3v Mx -> su_thr m Mx.
Proof. intros (_ & _ & _ & _ & _ & H). exact H. Qed.

(* a CALLER-saved write leaves every pinned register alone *)
Lemma su_regs_caller (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx : regfile)
    (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> su_regs m sp0 dpv ipv s3v Mx ->
  su_regs m sp0 dpv ipv s3v (<[Regidx r := v]> Mx).
Proof.
  intros Hr (H2 & H8 & H9 & H18 & H19 & Hthr). unfold su_regs. split_and!.
  - rewrite upd_ne; [exact H2 | su_rne1 Hr].
  - rewrite upd_ne; [exact H8 | su_rne1 Hr].
  - rewrite upd_ne; [exact H9 | su_rne1 Hr].
  - rewrite upd_ne; [exact H18 | su_rne1 Hr].
  - rewrite upd_ne; [exact H19 | su_rne1 Hr].
  - intros c Hc N2 N8 N9 N18' N19'.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18' N19') | su_rne2 Hr Hc].
Qed.

(* ...and so does a callee's [callee_saved] report *)
Lemma su_regs_cs (m : regfile) (sp0 dpv ipv s3v : mword 64) (Mx My : regfile) :
  callee_saved Mx My ->
  su_regs m sp0 dpv ipv s3v Mx -> su_regs m sp0 dpv ipv s3v My.
Proof.
  intros Hcs (H2 & H8 & H9 & H18 & H19 & Hthr). unfold su_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    exact H2.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 8 : mword 5)
               ltac:(vm_compute; reflexivity)).
    exact H8.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5)
               ltac:(vm_compute; reflexivity)).
    exact H9.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5)
               ltac:(vm_compute; reflexivity)).
    exact H18.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5)
               ltac:(vm_compute; reflexivity)).
    exact H19.
  - intros c Hc N2 N8 N9 N18' N19'. rewrite (callee_saved_lookup Hcs c Hc).
    exact (Hthr c Hc N2 N8 N9 N18' N19').
Qed.

(* the [c.mv s1,a0] at +0x2c -- dp *)
Lemma su_regs_wr_s1 (m : regfile) (sp0 dpv dpv' ipv s3v : mword 64)
    (Mx : regfile) (v : mword 64) :
  v = dpv' -> su_regs m sp0 dpv ipv s3v Mx ->
  su_regs m sp0 dpv' ipv s3v (<[Regidx (mword_of_int 9 : mword 5) := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H19 & Hthr). unfold su_regs. split_and!.
  - rewrite upd_ne; [exact H2 | sunz].
  - rewrite upd_ne; [exact H8 | sunz].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H18 | sunz].
  - rewrite upd_ne; [exact H19 | sunz].
  - intros c Hc N2 N8 N9 N18' N19'.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18' N19') | su_xne N9].
Qed.

(* the [c.mv s2,a0] at +0x6c -- ip *)
Lemma su_regs_wr_s2 (m : regfile) (sp0 dpv ipv ipv' s3v : mword 64)
    (Mx : regfile) (v : mword 64) :
  v = ipv' -> su_regs m sp0 dpv ipv s3v Mx ->
  su_regs m sp0 dpv ipv' s3v (<[Regidx (mword_of_int 18 : mword 5) := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H19 & Hthr). unfold su_regs. split_and!.
  - rewrite upd_ne; [exact H2 | sunz].
  - rewrite upd_ne; [exact H8 | sunz].
  - rewrite upd_ne; [exact H9 | sunz].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H19 | sunz].
  - intros c Hc N2 N8 N9 N18' N19'.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18' N19') | su_xne N18'].
Qed.

(* [s3] is DUAL-USE, so it is written twice: [c.mv s3,a5] at +0x104 (the
   isdirempty counter) and [addi s3,s0,-64] at +0x8a (writei's [&de]), plus
   the [c.addiw s3,s3,16] bump at +0x122. *)
Lemma su_regs_wr_s3 (m : regfile) (sp0 dpv ipv s3v s3v' : mword 64)
    (Mx : regfile) (v : mword 64) :
  v = s3v' -> su_regs m sp0 dpv ipv s3v Mx ->
  su_regs m sp0 dpv ipv s3v' (<[Regidx (mword_of_int 19 : mword 5) := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H19 & Hthr). unfold su_regs. split_and!.
  - rewrite upd_ne; [exact H2 | sunz].
  - rewrite upd_ne; [exact H8 | sunz].
  - rewrite upd_ne; [exact H9 | sunz].
  - rewrite upd_ne; [exact H18 | sunz].
  - rewrite upd_eq. exact Hv.
  - intros c Hc N2 N8 N9 N18' N19'.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18' N19') | su_xne N19'].
Qed.

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

(* ===================================================================== *)
(*  THE FRAME CARVE: 30 slots = FIVE saved words + FOUR byte windows +     *)
(*  the [off] slot + two dead ones                                        *)
(*                                                                        *)
(*    slot  1   ra                slot  2   s0                            *)
(*    slot  3   s1 (dp)           slot  4   s2 (ip)      slot 5  s3        *)
(*    slot  6   dead                                                      *)
(*    slots 7..8    [struct dirent de]  -- writei's, based at [pa_stk 8]   *)
(*    slots 9..10   [char name[DIRSIZ]] -- based at [pa_stk 10]            *)
(*    slots 11..26  [char path[MAXPATH]]-- based at [pa_stk 26]            *)
(*    slot  27      [uint off] in its UPPER word                          *)
(*    slots 28..29  [struct dirent de]  -- isdirempty's, at [pa_stk 29]    *)
(*    slot  30      dead (the frame's bottom)                             *)
(*                                                                        *)
(*  Slot 27's own alignment is NOT part of [su_al]: it comes off the       *)
(*  points-to itself ([word_pointsto_aligned_p]) at the one site that      *)
(*  splits it, exactly as sys_open's omode cell does.                      *)
(* ===================================================================== *)

Definition su_al (sp0 : mword 64) : Prop :=
  (forall i, (i < 2)%nat ->
     is_aligned_paddr (Physaddr (pa_stk sp0 (8 - i))) 8 = true)
  /\ (forall i, (i < 2)%nat ->
     is_aligned_paddr (Physaddr (pa_stk sp0 (10 - i))) 8 = true)
  /\ (forall i, (i < 16)%nat ->
     is_aligned_paddr (Physaddr (pa_stk sp0 (26 - i))) 8 = true)
  /\ (forall i, (i < 2)%nat ->
     is_aligned_paddr (Physaddr (pa_stk sp0 (29 - i))) 8 = true).

Section ProofSysUnlinkFrame.
  Context `{!riscvGS Σ}.

  Context {kt : ktier}.
  Lemma su_frame_carve (sp0 : mword 64) :
    stack_own (KTR := kt) sp0 30 -∗
    ⌜su_al sp0⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 5) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 6) ↦₈ w) ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 8) 16 ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 10) 16 ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 26) 128 ∗
    (∃ w : mword 64, (pa_stk sp0 27) ↦₈ w) ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 29) 16 ∗
    (∃ w : mword 64, (pa_stk sp0 30) ↦₈ w).
  Proof.
    iIntros "H". rewrite (stack_own_slots (KTR := kt)). cbn [seq].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                       H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 &
                       H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 &
                       H29 & H30 & _)".
    change 16%nat with (8 * 2)%nat at 1.
    iDestruct (slotsn_bytes_own sp0 8 2 ltac:(lia) with "[H7 H8]")
      as "[%HalD HbD]".
    { cbn [seq]. iSplitL "H8"; [iExact "H8" |]. iSplitL "H7"; [iExact "H7" |].
      done. }
    change 16%nat with (8 * 2)%nat at 1.
    iDestruct (slotsn_bytes_own sp0 10 2 ltac:(lia) with "[H9 H10]")
      as "[%HalN HbN]".
    { cbn [seq]. iSplitL "H10"; [iExact "H10" |].
      iSplitL "H9"; [iExact "H9" |]. done. }
    change 128%nat with (8 * 16)%nat at 1.
    iDestruct (slotsn_bytes_own sp0 26 16 ltac:(lia)
                 with "[H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23
                        H24 H25 H26]") as "[%HalP HbP]".
    { cbn [seq].
      iSplitL "H26"; [iExact "H26" |]. iSplitL "H25"; [iExact "H25" |].
      iSplitL "H24"; [iExact "H24" |]. iSplitL "H23"; [iExact "H23" |].
      iSplitL "H22"; [iExact "H22" |]. iSplitL "H21"; [iExact "H21" |].
      iSplitL "H20"; [iExact "H20" |]. iSplitL "H19"; [iExact "H19" |].
      iSplitL "H18"; [iExact "H18" |]. iSplitL "H17"; [iExact "H17" |].
      iSplitL "H16"; [iExact "H16" |]. iSplitL "H15"; [iExact "H15" |].
      iSplitL "H14"; [iExact "H14" |]. iSplitL "H13"; [iExact "H13" |].
      iSplitL "H12"; [iExact "H12" |]. iSplitL "H11"; [iExact "H11" |].
      done. }
    change 16%nat with (8 * 2)%nat.
    iDestruct (slotsn_bytes_own sp0 29 2 ltac:(lia) with "[H28 H29]")
      as "[%HalE HbE]".
    { cbn [seq]. iSplitL "H29"; [iExact "H29" |].
      iSplitL "H28"; [iExact "H28" |]. done. }
    iFrame "H1 H2 H3 H4 H5 H6 HbD HbN HbP H27 HbE H30". iPureIntro.
    split_and!; assumption.
  Qed.

  Lemma su_frame_join (sp0 : mword 64) (w1 w2 w3 w4 w5 w6 w27 w30 : mword 64) :
    su_al sp0 ->
    (pa_stk sp0 1) ↦₈ w1 -∗ (pa_stk sp0 2) ↦₈ w2 -∗
    (pa_stk sp0 3) ↦₈ w3 -∗ (pa_stk sp0 4) ↦₈ w4 -∗
    (pa_stk sp0 5) ↦₈ w5 -∗ (pa_stk sp0 6) ↦₈ w6 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 8) 16 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 10) 16 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 26) 128 -∗
    (pa_stk sp0 27) ↦₈ w27 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 29) 16 -∗
    (pa_stk sp0 30) ↦₈ w30 -∗
    stack_own (KTR := kt) sp0 30.
  Proof.
    intros (HalD & HalN & HalP & HalE).
    iIntros "H1 H2 H3 H4 H5 H6 HbD HbN HbP H27 HbE H30".
    (* the [8 * n] conversions go INSIDE the framing braces, never on the
       goal -- a goal-level [change] survives into the [cbn [seq]] and then
       leaves the frame's own [seq] partially reduced. *)
    iDestruct (bytes_own_slotsn sp0 8 2 ltac:(lia) HalD with "[HbD]") as "HsD".
    { change (8 * 2)%nat with 16%nat. iExact "HbD". }
    iDestruct (bytes_own_slotsn sp0 10 2 ltac:(lia) HalN with "[HbN]") as "HsN".
    { change (8 * 2)%nat with 16%nat. iExact "HbN". }
    iDestruct (bytes_own_slotsn sp0 26 16 ltac:(lia) HalP with "[HbP]") as "HsP".
    { change (8 * 16)%nat with 128%nat. iExact "HbP". }
    iDestruct (bytes_own_slotsn sp0 29 2 ltac:(lia) HalE with "[HbE]") as "HsE".
    { change (8 * 2)%nat with 16%nat. iExact "HbE". }
    cbn [seq].
    iDestruct "HsD" as "(K8 & K7 & _)".
    iDestruct "HsN" as "(K10 & K9 & _)".
    iDestruct "HsP" as "(K26 & K25 & K24 & K23 & K22 & K21 & K20 & K19 & K18 &
                         K17 & K16 & K15 & K14 & K13 & K12 & K11 & _)".
    iDestruct "HsE" as "(K29 & K28 & _)".
    rewrite (stack_own_slots (KTR := kt)). cbn [seq].
    iSplitL "H1"; [iExists w1; iExact "H1" |].
    iSplitL "H2"; [iExists w2; iExact "H2" |].
    iSplitL "H3"; [iExists w3; iExact "H3" |].
    iSplitL "H4"; [iExists w4; iExact "H4" |].
    iSplitL "H5"; [iExists w5; iExact "H5" |].
    iSplitL "H6"; [iExists w6; iExact "H6" |].
    iSplitL "K7"; [iExact "K7" |].    iSplitL "K8"; [iExact "K8" |].
    iSplitL "K9"; [iExact "K9" |].    iSplitL "K10"; [iExact "K10" |].
    iSplitL "K11"; [iExact "K11" |].  iSplitL "K12"; [iExact "K12" |].
    iSplitL "K13"; [iExact "K13" |].  iSplitL "K14"; [iExact "K14" |].
    iSplitL "K15"; [iExact "K15" |].  iSplitL "K16"; [iExact "K16" |].
    iSplitL "K17"; [iExact "K17" |].  iSplitL "K18"; [iExact "K18" |].
    iSplitL "K19"; [iExact "K19" |].  iSplitL "K20"; [iExact "K20" |].
    iSplitL "K21"; [iExact "K21" |].  iSplitL "K22"; [iExact "K22" |].
    iSplitL "K23"; [iExact "K23" |].  iSplitL "K24"; [iExact "K24" |].
    iSplitL "K25"; [iExact "K25" |].  iSplitL "K26"; [iExact "K26" |].
    iSplitL "H27"; [iExists w27; iExact "H27" |].
    iSplitL "K28"; [iExact "K28" |].  iSplitL "K29"; [iExact "K29" |].
    iSplitL "H30"; [iExists w30; iExact "H30" |].
    done.
  Qed.

  (* the buffers, named as bytes and back: argstr / nameiparent / namecmp /
     dirlookup / memset / readi / writei all speak the [seq]-indexed byte
     window, not [bytes_own]. *)
  Lemma su_bytes_name (a : mword 64) (N : nat) :
    bytes_own (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j.
  Proof. rewrite /bytes_own. exact (bb_any_named a N). Qed.

  Lemma su_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j) ⊢ bytes_own (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any a N f). Qed.

  (* 128 = (k+1) + (127-k): nameiparent reads the NUL-terminated prefix and
     the rest rides through untouched *)
  Lemma su_buf_split (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 128, pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ f j)
    ∗ ([∗ list] j ∈ seq 0 (127 - k)%nat,
         pa_add (pa_add a (S k)) j ↦ₘ f (S k + j)%nat).
  Proof.
    intro Hk.
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite (bb_split a (S k) (127 - k)%nat f). iIntros "[$ $]".
  Qed.

  Lemma su_buf_join (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat,
       pa_add (pa_add a (S k)) j ↦ₘ f (S k + j)%nat) -∗
    bytes_own (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (su_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (su_name_bytes (pa_add a (S k)) (127 - k)%nat
                 (fun j => f (S k + j)%nat) with "H2") as "B2".
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite bytes_own_app. iFrame.
  Qed.

  (* the NAME buffer is sixteen bytes of frame but FOURTEEN of DIRSIZ; the
     two trailing bytes ride through nameiparent and both namecmps and
     dirlookup untouched. *)
  Lemma su_nm_split (a : mword 64) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ f j)
    ∗ ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 14) j ↦ₘ f (14 + j)%nat).
  Proof.
    change 16%nat with (14 + 2)%nat.
    rewrite (bb_split a 14 2 f). iIntros "[$ $]".
  Qed.

  Lemma su_nm_join (a : mword 64) (f g : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ g j) -∗
    ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 14) j ↦ₘ f (14 + j)%nat) -∗
    bytes_own (DfracOwn 1) a 16.
  Proof.
    iIntros "H1 H2".
    iDestruct (su_name_bytes a 14 g with "H1") as "B1".
    iDestruct (su_name_bytes (pa_add a 14) 2
                 (fun j => f (14 + j)%nat) with "H2") as "B2".
    change 16%nat with (14 + 2)%nat.
    rewrite bytes_own_app. iFrame.
  Qed.

  (* THE [off] CELL, the one 4-byte view of a frame slot sys_unlink needs.
     The LOWER word of slot 27 is dead; it rides through as an arbitrary
     word and comes back. *)
  Lemma su_off_split (sp0 : mword 64) (w : mword 64) :
    (pa_stk sp0 27) ↦₈ w ⊢
    (pa_stk sp0 27) ↦₄ word_lo w ∗ (pa_add (pa_stk sp0 27) 4) ↦₄ word_hi w.
  Proof. apply word_pointsto_split4. Qed.

  Lemma su_off_join (sp0 : mword 64) (lo hi : bv 32) :
    is_aligned_paddr (Physaddr (pa_stk sp0 27)) 8 = true ->
    (pa_stk sp0 27) ↦₄ lo -∗ (pa_add (pa_stk sp0 27) 4) ↦₄ hi -∗
    (pa_stk sp0 27) ↦₈ word_of_words lo hi.
  Proof. intro Hal. apply word_pointsto_join4. exact Hal. Qed.

End ProofSysUnlinkFrame.

(* ===================================================================== *)
(*  +0x168 .. +0x16e : THE EPILOGUE, which all six arms leave through.     *)
(*                                                                        *)
(*  FOUR instructions, and it restores only ra and s0 -- NOT s1, s2 or s3, *)
(*  each of which is reloaded (or never saved) by the arm itself, which is *)
(*  why all three appear here at EXISTENTIAL slot contents and as          *)
(*  register-equation premises.  a0 is already set: each arm writes its    *)
(*  own literal (+0xd8 writes 0, +0x164 and +0x170 write -1).              *)
(* ===================================================================== *)

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac scidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofSysUnlinkEpilogue.
  Context `{!riscvGS Σ, !sieG Σ}.

  Context {kt : ktier}.
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma su_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64)
      (w3 w4 w5 w6 w27 w30 : mword 64) (bd bn bp be : nat -> bv 8) :
    (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_sp sp0 M -> su_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    su_al sp0 ->
    sie_cap_gpr kt M (K - 30) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SU + 0x168)) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ w3 -∗
    (pa_stk sp0 4) ↦₈ w4 -∗
    (pa_stk sp0 5) ↦₈ w5 -∗
    (pa_stk sp0 6) ↦₈ w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ bd jj) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ bn jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ bp jj) -∗
    (pa_stk sp0 27) ↦₈ w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ be jj) -∗
    (pa_stk sp0 30) ↦₈ w30 -∗
    (* THE INDEX IS [b], NOT [true]: the epilogue is four PLAIN
       instructions, so every crossing it makes is a [b]-link.  A caller
       whose own continuation is at [true] weakens into this for free. *)
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64)⌝ -∗
        sie_cap_gpr kt mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK30 Kpop Hsp0 HMsp HMthr HMs1 HMs2 HMs3 Hal.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP H27 HbE H30
              Hcont".
    iPoseProof (suli_168 with "Htext") as "Hi168".
    iPoseProof (suli_16a with "Htext") as "Hi16a".
    iPoseProof (suli_16c with "Htext") as "Hi16c".
    iPoseProof (suli_16e with "Htext") as "Hi16e".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HMsp; apply su_frm1).
    (* ===== +0x168 c.ldsp ra,232(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SU + 0x168))
              (mword_of_int 29 : mword 6) Rra M (K - 30)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi168 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (M1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HM1sp : su_sp sp0 M1)
      by (rewrite /su_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : su_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp16a : add_vec_int (mword_of_int (SU + 0x168) : mword 64) 2
                     = mword_of_int (SU + 0x16a)) by pcw.
    iEval (rewrite Hpp16a) in "Hpc".
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply su_frm2).
    (* ===== +0x16a c.ldsp s0,224(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SU + 0x16a))
              (mword_of_int 28 : mword 6) Rs0 M1 (K - 30)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi16a [Hf2]").
    { iEval (rewrite Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    set (M2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> M1).
    assert (HM2sp : su_sp sp0 M2)
      by (rewrite /su_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1ra | nz]).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : su_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp16c : add_vec_int (mword_of_int (SU + 0x16a) : mword 64) 2
                     = mword_of_int (SU + 0x16c)) by pcw.
    iEval (rewrite Hpp16c) in "Hpc".
    (* ===== +0x16c c.addi16sp sp,240 : the pop ===== *)
    assert (Hwv : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 15 : mword 6)))
                  = sp0)
      by (rewrite HM2sp; apply su_pop).
    assert (Hpop : (M2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 15 : mword 6)))) 30)
      by (rewrite Hwv HM2sp; reflexivity).
    iDestruct (su_name_bytes (pa_stk sp0 8) 16 bd with "HbD") as "BD".
    iDestruct (su_name_bytes (pa_stk sp0 10) 16 bn with "HbN") as "BN".
    iDestruct (su_name_bytes (pa_stk sp0 26) 128 bp with "HbP") as "BP".
    iDestruct (su_name_bytes (pa_stk sp0 29) 16 be with "HbE") as "BE".
    iDestruct (su_frame_join sp0 _ _ w3 w4 w5 w6 w27 w30 Hal
                 with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 BD BN BP H27 BE H30") as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SU + 0x16c))
              (mword_of_int 15 : mword 6) M2 (K - 30)%nat 30 b Hpop
              with "Hcg Hpc Hi16c Hstk").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (M3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 15 : mword 6))))]> M2).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp16e : add_vec_int (mword_of_int (SU + 0x16c) : mword 64) 2
                     = mword_of_int (SU + 0x16e)) by pcw.
    iEval (rewrite Hpp16e) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    (* ===== +0x16e c.ret ===== *)
    iApply (wp_cret_s_sconf (mword_of_int (SU + 0x16e)) Rra M3 K b
              ltac:(nz) with "Hcg Hpc Hi16e").
    iIntros (CID4 Hq4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HM3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE HANDOVER ===== *)
    assert (Hwv' : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 15 : mword 6)))
                   = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite Hwv; exact Hsp0).
    assert (Csp : (M3 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /M3 upd_eq; exact Hwv').
    assert (Cs0 : (M3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (Cs1 : (M3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (Cs2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s2 | nz]).
    assert (Cs3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s3 | nz]).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2a0 | nz]).
    assert (Hfin : su_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! M3 with "[%] [%] Hcg Hpc").
    { unfold callee_saved. split_and!;
        [ exact Csp | exact Cs0 | exact Cs1 | exact Cs2 | exact Cs3
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx | apply Hfin; scidx ]. }
    { exact HM3a0. }
  Qed.

End ProofSysUnlinkEpilogue.

(* ===================================================================== *)
(*  THE T_DIR ARM'S RE-PARK OF [ip], and the ONE premise it cannot supply  *)
(*                                                                        *)
(*  On the T_DIR arm the walk spends [ip]'s [".."] ticket at              *)
(*  [dp->nlink--] ([DirLinks.dir_links_dotdot_out] hands out the           *)
(*  [ilink dp], [SpecIupdate.wp_iupdate_unlink] consumes it) and must then *)
(*  hand [ip]'s payload back at [iunlockput(ip)] -- so record 1 of [ip]    *)
(*  needs a ticket it no longer has.  [DirLinks.dir_link_at] offers        *)
(*  exactly three ways to have one:                                       *)
(*                                                                        *)
(*    * the record is FREE     -- false: [dir_dots_ix] says record 1 is a  *)
(*                                live [".."];                            *)
(*    * the record is the SELF record -- false, same clause;               *)
(*    * [ilink]                -- SPENT at [dp->nlink--];                  *)
(*    * [igrey] AND the HOME's count is ZERO -- the grey half is free      *)
(*      ([InodeRegion.ireg_link_grey], no premise at all), the HOME half   *)
(*      is [bv_unsigned (di_nlink dn') = 0] and IS NOT DERIVABLE.          *)
(*                                                                        *)
(*  This lemma is the constructor for the fourth route, stated with that   *)
(*  one fact as a PREMISE rather than assumed: everything else the re-park *)
(*  needs is already in hand -- record 0 is the self record and records    *)
(*  2.. are dead, both out of the isdirempty loop and [dir_dots_ix].       *)
(*                                                                        *)
(*  WHAT THE PREMISE MEANS, AND WHY IT HAS NO SUPPLIER.  [ip->nlink--]     *)
(*  lands at zero exactly when [ip]'s count was ONE going in, i.e. when an *)
(*  empty directory's link count is 1 -- true of xv6 (a directory's count  *)
(*  is 1 + its subdirectory count, and [isdirempty] says there are none)   *)
(*  but stated NOWHERE in the model: [InodeRegion.ireg_link_ok] bounds the *)
(*  ledger BELOW the count ((L1), [w <= nlink]) and nothing bounds it      *)
(*  above.  design/fs-icache.md 20.17.4 sharpening (a) asserts the fact    *)
(*  ("the home still has nlink = 1") without a carrier.  See               *)
(*  projects/fs-sysfile.md, S7-unlink, FINDING 3.                          *)
(* ===================================================================== *)

Section ProofSysUnlinkOrphan.
  Context `{!icacheG Σ} `{ICFG : icfg}.

  (* record 0 is the SELF record, so its ticket is [emp] *)
  Lemma su_link_self (self : Z) (dn' : dinode) (data : nat -> list (bv 8)) :
    bv_unsigned (dir_inum data 0) = self ->
    ⊢ dir_link_at self dn' data 0.
  Proof.
    intro Hs. rewrite /dir_link_at.
    rewrite (bool_decide_eq_true_2 (bv_unsigned (dir_inum data 0) = self) Hs).
    rewrite andb_false_r. done.
  Qed.

  (* ...and a record the isdirempty loop found FREE carries nothing *)
  Lemma su_link_dead (self : Z) (dn' : dinode) (data : nat -> list (bv 8))
      (k : nat) :
    dir_inum data k = bv_0 16 -> ⊢ dir_link_at self dn' data k.
  Proof. intro Hz. exact (dir_link_at_zeroed self dn' data k Hz). Qed.

  (* THE CONSTRUCTOR.  [igrey] in, [ip]'s whole [dir_links] out. *)
  Lemma su_dir_links_orphan (self : Z) (dn' : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn') = 0 ->
    bv_unsigned (dir_inum data 0) = self ->
    (forall k : nat, (2 <= k)%nat ->
       (k < dir_nrec (bv_unsigned (di_size dn')))%nat ->
       dir_inum data k = bv_0 16) ->
    igrey (bv_unsigned (dir_inum data 1)) -∗ dir_links self dn' data.
  Proof.
    (* THE CONTENT MOVED DOWN TO [DirLinks.dir_links_orphan] (V2, the count
       clause).  [dir_links] now carries [DirView.dlc_bound] over an
       existential flavour map, so building it record by record is the
       payload's own business rather than this file's -- and the clause is
       free at the premise this lemma already takes ([nlink = 0] gives
       [0 <= 1 + _]).  The STATEMENT is unchanged, and so is what the walk
       owes: the one pure premise below. *)
    exact (dir_links_orphan self dn' data).
  Qed.

End ProofSysUnlinkOrphan.
