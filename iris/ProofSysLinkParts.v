(* ProofSysLinkParts.v -- sys_link's PURE side conditions, its frame carve
   and its epilogue: everything the walk needs that does not apply a
   callee's contract, and therefore everything that can live outside the
   module functor.

   The walk itself is [ProofSysLink.v]; the op-wide log ledger is
   [SysLinkBudget.v]; the contract is [SpecSysLink.v], whose header carries
   the arm graph and the frame map.

   NOTHING HERE IS IMPORTED FROM ANOTHER FUNCTION'S PROOF.  The sign
   cluster, the sixteen-bit compare cluster and the [++] / [--] clusters
   are restated rather than taken from [ProofSysChdir] / [ProofCreate]: a
   whole-function proof file is not a dependency any other one may take,
   and the two arithmetic clusters are not the same lemmas anyway -- see
   the [lh] / [lhu] note on [sl_nlink_incr]. *)
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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
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
Require Import SpecIunlock.
Require Import SpecIupdate.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamei.
Require Import SpecNameiparent.
Require Import CodeSysLink.
Require Import SpecSysLink.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

Set Printing Depth 40.

Notation SL := KernelSyms.sys_link (only parsing).

(* ===================================================================== *)
(*  THE REGISTER LEDGER                                                   *)
(* ===================================================================== *)

(* the four registers this frame moves: sp, s0 (the frame pointer),
   s1 (ip), s2 (dp).  Everything else callee-saved rides straight through,
   and it is stated POSITIVELY where it matters -- the four exceptions are
   exactly the four the code writes, each accounted for by its own
   equation. *)
Definition sl_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma sl_thr_refl (m : regfile) : sl_thr m m.
Proof. intros c _ _ _ _ _. reflexivity. Qed.

Lemma sl_thr_trans (m M P : regfile) : sl_thr m M -> sl_thr M P -> sl_thr m P.
Proof.
  intros H1 H2 c Hc N2 N8 N9 N18.
  rewrite (H2 c Hc N2 N8 N9 N18). exact (H1 c Hc N2 N8 N9 N18).
Qed.

Definition sl_sp (sp0 : mword 64) (M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk sp0 38.

(* ===================================================================== *)
(*  THE FRAME ARITHMETIC -- 304 bytes, THIRTY-EIGHT slots                 *)
(* ===================================================================== *)

(* -304 / +304, both a [c.addi16sp] (45 is -19 in a 6-bit field, x16;
   19 is +19). *)
Lemma sl_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 45 : mword 6)))
  = pa_stk X 38.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_pop (X : mword 64) :
  add_vec (pa_stk X 38) (sign_extend' 64 (caddi16sp_imm (mword_of_int 19 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,304] -- the frame pointer, back at the entry sp. *)
Lemma sl_fp (X : mword 64) :
  add_vec (pa_stk X 38) (sign_extend' 64 (caddi4spn_imm (mword_of_int 76 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* the three buffer bases, off the frame pointer (which IS the entry sp):
   [old] at -304, [new] at -176, [name] at -48. *)
Lemma sl_bufold (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3792 : mword 12)) = pa_stk X 38.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_bufnew (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3920 : mword 12)) = pa_stk X 22.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_bufname (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4048 : mword 12)) = pa_stk X 6.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* the c.sdsp / c.ldsp displacements off the pushed sp *)
Lemma sl_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (bv_wrap 64 (uint (mword_of_int (- (8 * Z.of_nat 38)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 38) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite pa_stk_off2. apply f_equal. exact H.
Qed.

Lemma sl_frm1 (X : mword 64) :
  add_vec (pa_stk X 38)
    (zero_extend' 64 (concat_vec (mword_of_int 37 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply sl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_frm2 (X : mword 64) :
  add_vec (pa_stk X 38)
    (zero_extend' 64 (concat_vec (mword_of_int 36 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply sl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_frm3 (X : mword 64) :
  add_vec (pa_stk X 38)
    (zero_extend' 64 (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply sl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_frm4 (X : mword 64) :
  add_vec (pa_stk X 38)
    (zero_extend' 64 (concat_vec (mword_of_int 34 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply sl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_sys_link's single premise, turned into every bound the eleven callees
   and the [sie_cap_gpr] pop want. *)
Lemma sl_kb (K : nat) : (K_sys_link <= K)%nat ->
  (K_namei <= K - 38)%nat /\ (K_nameiparent <= K - 38)%nat /\
  (K_dirlink <= K - 38)%nat /\ (argstr_stack <= K - 38)%nat /\
  (K_begin_op <= K - 38)%nat /\ (K_end_op <= K - 38)%nat /\
  (K_ilock <= K - 38)%nat /\ (K_iunlock <= K - 38)%nat /\
  (K_iupdate <= K - 38)%nat /\
  (K_iput <= K - 38)%nat /\ (K_iunlockput <= K - 38)%nat /\
  (10 <= K - 38)%nat /\ (38 <= K)%nat /\ ((K - 38) + 38 = K)%nat.
Proof.
  
  intro H. split_and!; lia.
Qed.

(* ===================================================================== *)
(*  THE SIGN CLUSTER: the three [bltz]s (+0x18, +0x2c, +0xa0)             *)
(* ===================================================================== *)

Lemma sl_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
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

Lemma sl_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (sl_sint_moi z Hz). lia.
Qed.

Lemma sl_m1_neg :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma sl_zero_nonneg :
  zopz0zI_s (mword_of_int 0 : mword 64) (zero_reg : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

Lemma sl_len_range (k : nat) : (k < 128)%nat -> (0 <= Z.of_nat k < 2 ^ 31)%Z.
Proof.
  intro Hk.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

Lemma sl_plen_lt (k : nat) : (k < 128)%nat -> (Z.of_nat k < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma sl_maxpath_lt : (Z.of_nat 128 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma sl_arg0_lt : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma sl_arg1_lt : (1 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma sl_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* ===================================================================== *)
(*  THE SIXTEEN-BIT COMPARE CLUSTER: the type test (+0x4c) and the        *)
(*  NLINK_MAX guard (+0x58).  BOTH are [BEQ] against a sign-extended      *)
(*  [lh], so both go through the same injectivity lemma.                  *)
(* ===================================================================== *)

Lemma sl_sext16_inj (x y : mword 16) :
  (sign_extend' 64 x : mword 64) = (sign_extend' 64 y : mword 64) -> x = y.
Proof.
  intros H. apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H;
    [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

Lemma sl_sext_one :
  (sign_extend' 64 (mword_of_int 1 : mword 16) : mword 64)
  = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x4c [beq a5,a4] with a4 = sign_extend(ip->type), a5 = 1: the branch
   CONDITION is [eq_vec a4 a5]. *)
Lemma sl_tdir_eq (t : mword 16) : t = (mword_of_int 1 : mword 16) ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = true.
Proof.
  intros ->. rewrite sl_sext_one.
  exact (proj2 (eq_vec_true_iff _ _) eq_refl).
Qed.

Lemma sl_tdir_ne (t : mword 16) : t <> (mword_of_int 1 : mword 16) ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)).
  intro Hc. apply Hne. apply sl_sext16_inj. rewrite Hc sl_sext_one.
  reflexivity.
Qed.

(* +0x88 [c.beqz a5] with a5 = sign_extend(dp->nlink): THE ORPHAN GUARD
   (xv6 f60ff58), create's re-check after [ilock(dp)] given to sys_link.
   The branch CONDITION is [eq_vec a5 zero], and the pair below is the
   [sl_tdir_*] pair at the other literal -- [sl_sext16_inj] decides both. *)
Lemma sl_sext_zero :
  (sign_extend' 64 (mword_of_int 0 : mword 16) : mword 64)
  = (zero_reg : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_nlz_eq (h : mword 16) : h = (mword_of_int 0 : mword 16) ->
  eq_vec (sign_extend' 64 h : mword 64) (zero_reg : mword 64) = true.
Proof.
  intros ->. exact (proj2 (eq_vec_true_iff _ _) sl_sext_zero).
Qed.

Lemma sl_nlz_ne (h : mword 16) : h <> (mword_of_int 0 : mword 16) ->
  eq_vec (sign_extend' 64 h : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)).
  intro Hc. apply Hne. apply sl_sext16_inj. rewrite Hc sl_sext_zero.
  reflexivity.
Qed.

(* [c.lui a4,0x8] then [c.addi a4,a4,-1] is 0x7fff = 32767 = NLINK_MAX,
   which is SHRT_MAX -- which is why gcc turned [nlink >= NLINK_MAX] into
   a [beq] rather than a compare. *)
Lemma sl_sext_max :
  (sign_extend' 64 (mword_of_int 32767 : mword 16) : mword 64)
  = (mword_of_int 32767 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x58 [beq a4,a5] with a5 = sign_extend(ip->nlink), a4 = 32767: the
   branch CONDITION is [eq_vec a5 a4]. *)
Lemma sl_nmax_eq (h : mword 16) : h = (mword_of_int 32767 : mword 16) ->
  eq_vec (sign_extend' 64 h : mword 64) (mword_of_int 32767 : mword 64) = true.
Proof.
  intros ->. rewrite sl_sext_max.
  exact (proj2 (eq_vec_true_iff _ _) eq_refl).
Qed.

Lemma sl_nmax_ne (h : mword 16) : h <> (mword_of_int 32767 : mword 16) ->
  eq_vec (sign_extend' 64 h : mword 64) (mword_of_int 32767 : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)).
  intro Hc. apply Hne. apply sl_sext16_inj. rewrite Hc sl_sext_max.
  reflexivity.
Qed.

(* ===================================================================== *)
(*  THE [++] AT +0x5e/+0x60 AND THE [--] AT +0xfe/+0x100                    *)
(*                                                                        *)
(*  BOTH sixteen-bit, and the two do NOT share a lemma, because the two    *)
(*  READS do not share an extension: the [++] reuses the SIGN-extended     *)
(*  [lh] the NLINK_MAX guard already loaded (+0x50), while the [--] does   *)
(*  its own ZERO-extended [lhu] (+0xfa).  [ProofCreate.cr_nlink_incr]'s    *)
(*  chain is the [lhu] one, so it transfers to the [--] and not to the     *)
(*  [++]; the extra step the signed read costs is [sl_sext16_low], one     *)
(*  [Zminus_mod_idemp_l] over the half modulus.                            *)
(* ===================================================================== *)

(* a signed sixteen-bit reading and an unsigned one agree modulo 2^16 --
   the fact that lets the [++] be walked without a case split on the sign
   of [nlink].  [BvShift.swrap_low] does not apply here (its divisibility
   premise is [m | h], and at 16->16 that is [65536 | 32768]). *)
Lemma sl_uns16 (h : mword 16) : (0 <= bv_unsigned h < 65536)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ h) as H0. unfold bv_modulus in H0.
  exact H0.
Qed.

Lemma sl_sext16_low (h : mword 16) :
  (bv_unsigned (bv_sign_extend 64 h) `mod` 65536)%Z = bv_unsigned h.
Proof.
  pose proof (sl_uns16 h) as Hr.
  rewrite bv_sign_extend_unsigned.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite mod_2_64_16.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z.
  change (65536 / 2)%Z with 32768%Z.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned h + 32768 - 32768)%Z with (bv_unsigned h) by lia.
  apply Z.mod_small. lia.
Qed.

(* ---- (a) THE [++]: [lh] (sign), [c.addiw +1], [sh]. ---- *)
Definition sl_ninner (h : mword 16) : bv 32 :=
  bv_extract 0 32 (bv_add (bv_sign_extend 64 h)
      (bv_sign_extend 64 (bv_sign_extend 12 (mword_of_int 1 : mword 6)))).

Lemma sl_ninner_unsigned (h : mword 16) :
  bv_unsigned (sl_ninner h)
  = ((bv_unsigned (bv_sign_extend 64 h) + 1) `mod` 4294967296)%Z.
Proof.
  unfold sl_ninner.
  rewrite bv_extract_unsigned bv_add_unsigned.
  assert (Hc : bv_unsigned (bv_sign_extend 64
                  (bv_sign_extend 12 (mword_of_int 1 : mword 6)) : bv 64) = 1%Z)
    by (vm_compute; reflexivity).
  rewrite Hc.
  change (Z.of_N 0) with 0%Z.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite mod_2_64_32. reflexivity.
Qed.

Lemma sl_nbump_bv (h : mword 16) :
  bv_unsigned (trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 h : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
         : mword 64)) 31 0)))
  = bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (sl_ninner h))).
Proof. reflexivity. Qed.

Lemma sl_nbump_unsigned (h : mword 16) :
  bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (sl_ninner h)))
  = ((bv_unsigned h + 1) `mod` 65536)%Z.
Proof.
  rewrite bv_extract_unsigned bv_sign_extend_unsigned.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (2 ^ Z.of_N 16)%Z with 65536%Z.
  rewrite mod_2_64_16 swrap_low_32_16 sl_ninner_unsigned mod_2_32_16.
  rewrite -Zplus_mod_idemp_l sl_sext16_low. reflexivity.
Qed.

Lemma sl_nlink_incr (h : mword 16) :
  trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 h : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
         : mword 64)) 31 0))
  = add_vec h (mword_of_int 1 : mword 16).
Proof.
  apply bv_eq. rewrite sl_nbump_bv sl_nbump_unsigned.
  rewrite add_vec_unsigned.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 16) = 1%Z)
    by (vm_compute; reflexivity).
  rewrite H1. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z.
  reflexivity.
Qed.

(* ---- (b) THE [--]: [lhu] (zero), [c.addiw -1], [sh].  The value the
   [sh] commits is [add_vec h (-1)], and what
   [SpecIupdate.wp_iupdate_unlink] wants is the Z equation
   [bv_unsigned h = bv_unsigned (result) + 1], which needs the count to be
   nonzero -- true here because the walk INCREMENTED it three calls ago. *)
Definition sl_dinner (h : mword 16) : bv 32 :=
  bv_extract 0 32 (bv_add (bv_zero_extend 64 h)
      (bv_sign_extend 64 (bv_sign_extend 12 (mword_of_int 63 : mword 6)))).

Lemma sl_dinner_unsigned (h : mword 16) :
  bv_unsigned (sl_dinner h)
  = ((bv_unsigned h + 18446744073709551615) `mod` 4294967296)%Z.
Proof.
  unfold sl_dinner.
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

Lemma sl_dbump_bv (h : mword 16) :
  bv_unsigned (trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (zero_extend' 64 h : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))
         : mword 64)) 31 0)))
  = bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (sl_dinner h))).
Proof. reflexivity. Qed.

Lemma sl_dbump_unsigned (h : mword 16) :
  bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (sl_dinner h)))
  = ((bv_unsigned h + 18446744073709551615) `mod` 65536)%Z.
Proof.
  rewrite bv_extract_unsigned bv_sign_extend_unsigned.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (2 ^ Z.of_N 16)%Z with 65536%Z.
  rewrite mod_2_64_16 swrap_low_32_16 sl_dinner_unsigned mod_2_32_16.
  reflexivity.
Qed.

(* THE CLAUSE [wp_iupdate_unlink] ACTUALLY TAKES, and it is the Z one:
   the OLD count is the new one plus one.  Sound because the walk's own
   [++] put [h] at least one -- the hypothesis below. *)
Lemma sl_nlink_decr (h : mword 16) :
  bv_unsigned h <> 0%Z ->
  bv_unsigned h
  = (bv_unsigned (trunc16 (sign_extend' 64 (subrange_vec_dec
       (add_vec (zero_extend' 64 h : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))
           : mword 64)) 31 0))) + 1)%Z.
Proof.
  intro Hnz. rewrite sl_dbump_bv sl_dbump_unsigned.
  pose proof (sl_uns16 h) as Hr.
  assert (Hstep : ((bv_unsigned h + 18446744073709551615) `mod` 65536)%Z
                  = (bv_unsigned h - 1)%Z).
  { replace (bv_unsigned h + 18446744073709551615)%Z
       with ((bv_unsigned h - 1) + 281474976710656 * 65536)%Z by lia.
    rewrite (Z.mod_add (bv_unsigned h - 1)%Z 281474976710656%Z 65536%Z
               ltac:(lia)).
    exact (Z.mod_small (bv_unsigned h - 1)%Z 65536%Z ltac:(lia)). }
  rewrite Hstep. lia.
Qed.

(* ---- (c) THE RECORD EITHER FLUSH WRITES.  Both the [++] and the [--]
   move ONE halfword, so the new record is the old one with [di_nlink]
   replaced -- and every pure clause a re-park owes ([InodeLock.inode_ok],
   [DirView.dir_ok]) reads only the type, the size and the addrs, so all
   three ride the change by [reflexivity].  The RESOURCE clause
   ([DirLinks.dir_links]) does not, and its move is
   [IregLinkNz.dir_links_nlink_drop]: at a nonzero count the grey colour is
   refuted, and an [ilink] ticket says nothing about the home record. *)
Definition sl_setnl (dn : dinode) (nl : mword 16) : dinode :=
  MkDinode (di_type dn) (di_major dn) (di_minor dn) nl (di_size dn)
           (di_addrs dn).

Lemma sl_setnl_type (dn : dinode) (nl : mword 16) :
  di_type (sl_setnl dn nl) = di_type dn.
Proof. reflexivity. Qed.

Lemma sl_setnl_nlink (dn : dinode) (nl : mword 16) :
  di_nlink (sl_setnl dn nl) = nl.
Proof. reflexivity. Qed.

Lemma sl_setnl_size (dn : dinode) (nl : mword 16) :
  di_size (sl_setnl dn nl) = di_size dn.
Proof. reflexivity. Qed.

Lemma sl_setnl_addrs (dn : dinode) (nl : mword 16) :
  di_addrs (sl_setnl dn nl) = di_addrs dn.
Proof. reflexivity. Qed.

Lemma sl_setnl_inode_ok (cov : gset Z) (ls : Z) (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (nl : mword 16) :
  inode_ok cov ls dn bm data -> inode_ok cov ls (sl_setnl dn nl) bm data.
Proof. unfold inode_ok, sl_setnl. cbn. exact (fun H => H). Qed.

Lemma sl_setnl_dir_ok (nib : nat) (dn : dinode) (data : nat -> list (bv 8))
    (nl : mword 16) :
  dir_ok nib dn data -> dir_ok nib (sl_setnl dn nl) data.
Proof. unfold dir_ok, sl_setnl. cbn. exact (fun H => H). Qed.

(* ...and the ".." index clause across the same store.  [sl_setnl] moves only
   the COUNT, and [dir_dots_ix] is guarded on it, so unlike [dir_ok] this
   one is not a [cbn]: the congruence needs the home to be live, which both
   sys_link re-parks have in hand -- the tail from the [ilink] it is about to
   spend, ARM E from [ip] not being a directory at all. *)
Lemma sl_setnl_ddix (self : Z) (dn : dinode) (data : nat -> list (bv 8))
    (nl : mword 16) :
  bv_unsigned (di_nlink dn) <> 0 ->
  dir_dots_ix self dn data -> dir_dots_ix self (sl_setnl dn nl) data.
Proof.
  intros Hnz Hd.
  apply (dir_dots_ix_eq self dn (sl_setnl dn nl) data data).
  - exact (sl_setnl_type dn nl).
  - intros _. exact Hnz.
  - rewrite sl_setnl_size. lia.
  - reflexivity.
  - exact Hd.
Qed.

Lemma sl_setnl_type_stable (dn : dinode) (nl : mword 16) :
  di_type_stable (sl_setnl dn nl) dn.
Proof. right. exact (sl_setnl_type dn nl). Qed.

(* the halfword the [sh] at +0x100 commits, named so the walk's store and
   [wp_iupdate_unlink]'s Z premise can be spelled at one term *)
Definition sl_ndec (h : mword 16) : mword 16 :=
  trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (zero_extend' 64 h : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))
         : mword 64)) 31 0)).

Lemma sl_ndec_decr (h : mword 16) :
  bv_unsigned h <> 0%Z ->
  bv_unsigned h = (bv_unsigned (sl_ndec h) + 1)%Z.
Proof. unfold sl_ndec. exact (sl_nlink_decr h). Qed.

(* ===================================================================== *)
(*  THE FRAME CARVE: 38 slots = FOUR saved words + THREE byte buffers     *)
(* ===================================================================== *)

Definition sl_al (sp0 : mword 64) : Prop :=
  (forall i, (i < 16)%nat ->
     is_aligned_paddr (Physaddr (pa_stk sp0 (38 - i)%nat)) 8 = true)
  /\ (forall i, (i < 16)%nat ->
        is_aligned_paddr (Physaddr (pa_stk sp0 (22 - i)%nat)) 8 = true)
  /\ (forall i, (i < 2)%nat ->
        is_aligned_paddr (Physaddr (pa_stk sp0 (6 - i)%nat)) 8 = true).

Section ProofSysLinkFrame.
  Context `{!riscvGS Σ}.

  Lemma sl_frame_carve `{XI : CurCtx} (sp0 : mword 64) :
    stack_own (KTR := KT1) sp0 38 -∗
    ⌜sl_al sp0⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈[KT1] w) ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 6) 16 ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 22) 128 ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 38) 128.
  Proof.
    iIntros "H". rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                       H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 &
                       H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 &
                       H29 & H30 & H31 & H32 & H33 & H34 & H35 & H36 & H37 &
                       H38 & _)".
    change 16%nat with (8 * 2)%nat at 1.
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 6 2 ltac:(lia) with "[H5 H6]")
      as "[%HalN HbN]".
    { cbn [seq]. iSplitL "H6"; [iExact "H6" |]. iSplitL "H5"; [iExact "H5" |].
      done. }
    change 128%nat with (8 * 16)%nat at 1.
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 22 16 ltac:(lia)
                 with "[H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20
                        H21 H22]") as "[%HalW HbW]".
    { cbn [seq].
      iSplitL "H22"; [iExact "H22" |]. iSplitL "H21"; [iExact "H21" |].
      iSplitL "H20"; [iExact "H20" |]. iSplitL "H19"; [iExact "H19" |].
      iSplitL "H18"; [iExact "H18" |]. iSplitL "H17"; [iExact "H17" |].
      iSplitL "H16"; [iExact "H16" |]. iSplitL "H15"; [iExact "H15" |].
      iSplitL "H14"; [iExact "H14" |]. iSplitL "H13"; [iExact "H13" |].
      iSplitL "H12"; [iExact "H12" |]. iSplitL "H11"; [iExact "H11" |].
      iSplitL "H10"; [iExact "H10" |]. iSplitL "H9"; [iExact "H9" |].
      iSplitL "H8"; [iExact "H8" |]. iSplitL "H7"; [iExact "H7" |].
      done. }
    change 128%nat with (8 * 16)%nat.
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 38 16 ltac:(lia)
                 with "[H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35
                        H36 H37 H38]") as "[%HalO HbO]".
    { cbn [seq].
      iSplitL "H38"; [iExact "H38" |]. iSplitL "H37"; [iExact "H37" |].
      iSplitL "H36"; [iExact "H36" |]. iSplitL "H35"; [iExact "H35" |].
      iSplitL "H34"; [iExact "H34" |]. iSplitL "H33"; [iExact "H33" |].
      iSplitL "H32"; [iExact "H32" |]. iSplitL "H31"; [iExact "H31" |].
      iSplitL "H30"; [iExact "H30" |]. iSplitL "H29"; [iExact "H29" |].
      iSplitL "H28"; [iExact "H28" |]. iSplitL "H27"; [iExact "H27" |].
      iSplitL "H26"; [iExact "H26" |]. iSplitL "H25"; [iExact "H25" |].
      iSplitL "H24"; [iExact "H24" |]. iSplitL "H23"; [iExact "H23" |].
      done. }
    iDestruct (TsoCtxShim.ctx_eslot_of_mem with "H1") as "H1".
    iDestruct (TsoCtxShim.ctx_eslot_of_mem with "H2") as "H2".
    iDestruct (TsoCtxShim.ctx_eslot_of_mem with "H3") as "H3".
    iDestruct (TsoCtxShim.ctx_eslot_of_mem with "H4") as "H4".
    iFrame "H1 H2 H3 H4 HbN HbW HbO". iPureIntro.
    split_and!; assumption.
  Qed.

  Lemma sl_frame_join `{XI : CurCtx} (sp0 : mword 64) (w1 w2 w3 w4 : mword 64) :
    sl_al sp0 ->
    (pa_stk sp0 1) ↦₈[KT1] w1 -∗ (pa_stk sp0 2) ↦₈[KT1] w2 -∗
    (pa_stk sp0 3) ↦₈[KT1] w3 -∗ (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 6) 16 -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 22) 128 -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 38) 128 -∗
    stack_own (KTR := KT1) sp0 38.
  Proof.
    intros (HalO & HalW & HalN). iIntros "H1 H2 H3 H4 HbN HbW HbO".
    (* the [8 * n] conversions are done INSIDE the framing braces, never on
       the goal: a goal-level [change 128 with (8*16)] survives into the
       [cbn [seq]] below, which then partially reduces the product and
       leaves the frame's own [seq] unreduced twenty-four slots in. *)
    iDestruct (bytes_own_slotsn (KTR := KT1) sp0 6 2 ltac:(lia) HalN with "[HbN]") as "HsN".
    { change (8 * 2)%nat with 16%nat. iExact "HbN". }
    iDestruct (bytes_own_slotsn (KTR := KT1) sp0 22 16 ltac:(lia) HalW with "[HbW]") as "HsW".
    { change (8 * 16)%nat with 128%nat. iExact "HbW". }
    iDestruct (bytes_own_slotsn (KTR := KT1) sp0 38 16 ltac:(lia) HalO with "[HbO]") as "HsO".
    { change (8 * 16)%nat with 128%nat. iExact "HbO". }
    cbn [seq].
    iDestruct "HsN" as "(K6 & K5 & _)".
    iDestruct "HsW" as "(K22 & K21 & K20 & K19 & K18 & K17 & K16 & K15 & K14 &
                         K13 & K12 & K11 & K10 & K9 & K8 & K7 & _)".
    iDestruct "HsO" as "(K38 & K37 & K36 & K35 & K34 & K33 & K32 & K31 & K30 &
                         K29 & K28 & K27 & K26 & K25 & K24 & K23 & _)".
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iSplitL "H1"; [iExists w1; iExact "H1" |].
    iSplitL "H2"; [iExists w2; iExact "H2" |].
    iSplitL "H3"; [iExists w3; iExact "H3" |].
    iSplitL "H4"; [iExists w4; iExact "H4" |].
    iSplitL "K5"; [iExact "K5" |].    iSplitL "K6"; [iExact "K6" |].
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
    iSplitL "K27"; [iExact "K27" |].  iSplitL "K28"; [iExact "K28" |].
    iSplitL "K29"; [iExact "K29" |].  iSplitL "K30"; [iExact "K30" |].
    iSplitL "K31"; [iExact "K31" |].  iSplitL "K32"; [iExact "K32" |].
    iSplitL "K33"; [iExact "K33" |].  iSplitL "K34"; [iExact "K34" |].
    iSplitL "K35"; [iExact "K35" |].  iSplitL "K36"; [iExact "K36" |].
    iSplitL "K37"; [iExact "K37" |].  iSplitL "K38"; [iExact "K38" |].
    done.
  Qed.

  (* the buffers, named as bytes and back: argstr / namei / nameiparent /
     dirlink all speak the [seq]-indexed byte window, not [bytes_own]. *)
  Lemma sl_bytes_name `{XI : CurCtx} (a : mword 64) (N : nat) :
    bytes_own (KTR := KT1) (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j.
  Proof. rewrite /bytes_own. exact (bb_any_named (KTR := KT1) a N). Qed.

  Lemma sl_name_bytes `{XI : CurCtx} (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j) ⊢ bytes_own (KTR := KT1) (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any (KTR := KT1) a N f). Qed.

  (* 128 = (k+1) + (127-k): the walkers read the NUL-terminated prefix, the
     rest rides through untouched *)
  Lemma sl_buf_split `{XI : CurCtx} (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 128, pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ[KT1] f j)
    ∗ ([∗ list] j ∈ seq 0 (127 - k)%nat,
         pa_add (pa_add a (S k)) j ↦ₘ[KT1] f (S k + j)%nat).
  Proof.
    intro Hk.
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite (bb_split a (S k) (127 - k)%nat f). iIntros "[$ $]".
  Qed.

  Lemma sl_buf_join `{XI : CurCtx} (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat,
       pa_add (pa_add a (S k)) j ↦ₘ[KT1] f (S k + j)%nat) -∗
    bytes_own (KTR := KT1) (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (sl_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (sl_name_bytes (pa_add a (S k)) (127 - k)%nat
                 (fun j => f (S k + j)%nat) with "H2") as "B2".
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite bytes_own_app. iFrame.
  Qed.

  (* the NAME buffer is sixteen bytes of frame but FOURTEEN of DIRSIZ; the
     two trailing bytes ride through the two walkers untouched. *)
  Lemma sl_nm_split `{XI : CurCtx} (a : mword 64) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] f j)
    ∗ ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 14) j ↦ₘ[KT1] f (14 + j)%nat).
  Proof.
    change 16%nat with (14 + 2)%nat.
    rewrite (bb_split a 14 2 f). iIntros "[$ $]".
  Qed.

  Lemma sl_nm_join `{XI : CurCtx} (a : mword 64) (f g : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] g j) -∗
    ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 14) j ↦ₘ[KT1] f (14 + j)%nat) -∗
    bytes_own (KTR := KT1) (DfracOwn 1) a 16.
  Proof.
    iIntros "H1 H2".
    iDestruct (sl_name_bytes a 14 g with "H1") as "B1".
    iDestruct (sl_name_bytes (pa_add a 14) 2
                 (fun j => f (14 + j)%nat) with "H2") as "B2".
    change 16%nat with (14 + 2)%nat.
    rewrite bytes_own_app. iFrame.
  Qed.

End ProofSysLinkFrame.

(* ===================================================================== *)
(*  +0x11a .. +0x122 : THE EPILOGUE, which all eight arms leave through.   *)
(*                                                                        *)
(*  It restores ra and s0 and pops -- and NOT s1 or s2, each of which is   *)
(*  reloaded (or never saved) by the arm itself, which is why both appear  *)
(*  here as PREMISES.  Everything else an arm is holding rides in its own  *)
(*  continuation premise, so this lemma has no file-system parameter at    *)
(*  all.                                                                   *)
(* ===================================================================== *)

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac scidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofSysLinkEpilogue.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Lemma sl_epilogue `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64)
      (w3 w4 : mword 64) (bn bw bo : nat -> bv 8) :
    (38 <= K)%nat -> ((K - 38) + 38 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sl_sp sp0 M -> sl_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    sl_al sp0 ->
    sie_cap_gpr KT1 M (K - 38) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SL + 0x11a)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] w3 -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 6) jj ↦ₘ[KT1] bn jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bw jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 38) jj ↦ₘ[KT1] bo jj) -∗
    (* THE INDEX IS [b], NOT [true]: the epilogue is five PLAIN
       instructions, so every crossing it makes is a [b]-link and the
       [b]-form chain is what it can hand back.  A caller whose own
       continuation is at [true] weakens into this for free ([or_intror],
       which is what [wp_next_chain] tries).  See fs-sysfile's sys_chdir
       rule. *)
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra5 : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK38 Kpop Hsp0 HMsp HMthr HMs1 HMs2 Hal.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO Hcont".
    (* ===== +0x11a c.mv a0,a5 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SL + 0x11a)) Ra0 Ra5
              M (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (slki_11a with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Ra5))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra5 : mword 64)).
    { etransitivity; [ rewrite /M1; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HM1sp : sl_sp sp0 M1)
      by (rewrite /sl_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    assert (Hpp11c : add_vec_int (mword_of_int (SL + 0x11a) : mword 64) 2
                     = mword_of_int (SL + 0x11c)) by pcw.
    iEval (rewrite Hpp11c) in "Hpc".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 37 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply sl_frm1).
    (* ===== +0x11c c.ldsp ra,296(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SL + 0x11c))
              (mword_of_int 37 : mword 6) Rra M1 (K - 38)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (slki_11c with "Htext"). }
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (M2 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M1).
    assert (HM2sp : sl_sp sp0 M2)
      by (rewrite /sl_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra5 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2thr : sl_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    assert (Hpp11e : add_vec_int (mword_of_int (SL + 0x11c) : mword 64) 2
                     = mword_of_int (SL + 0x11e)) by pcw.
    iEval (rewrite Hpp11e) in "Hpc".
    assert (Hc2 : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 36 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM2sp; apply sl_frm2).
    (* ===== +0x11e c.ldsp s0,288(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SL + 0x11e))
              (mword_of_int 36 : mword 6) Rs0 M2 (K - 38)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf2]").
    { iApply (slki_11e with "Htext"). }
    { iEval (rewrite Hc2). iExact "Hf2". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    set (M3 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> M2).
    assert (HM3sp : sl_sp sp0 M3)
      by (rewrite /sl_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M3; apply upd_eq).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra5 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2a0 | nz]).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s2 | nz]).
    assert (HM3thr : sl_thr m M3).
    { intros c Hc N2 N8 N9 N18. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8 N9 N18). }
    assert (Hpp120 : add_vec_int (mword_of_int (SL + 0x11e) : mword 64) 2
                     = mword_of_int (SL + 0x120)) by pcw.
    iEval (rewrite Hpp120) in "Hpc".
    (* ===== +0x120 c.addi16sp sp,304 : the pop ===== *)
    assert (Hwv : add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 19 : mword 6)))
                  = sp0)
      by (rewrite HM3sp; apply sl_pop).
    assert (Hpop : (M3 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 19 : mword 6)))) 38)
      by (rewrite Hwv HM3sp; reflexivity).
    iDestruct (sl_name_bytes (pa_stk sp0 6) 16 bn with "HbN") as "BN".
    iDestruct (sl_name_bytes (pa_stk sp0 22) 128 bw with "HbW") as "BW".
    iDestruct (sl_name_bytes (pa_stk sp0 38) 128 bo with "HbO") as "BO".
    iDestruct (sl_frame_join sp0 _ _ w3 w4 Hal with "Hf1 Hf2 Hf3 Hf4 BN BW BO")
      as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SL + 0x120))
              (mword_of_int 19 : mword 6) M3 (K - 38)%nat 38 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (slki_120 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 19 : mword 6))))]> M3).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp122 : add_vec_int (mword_of_int (SL + 0x120) : mword 64) 2
                     = mword_of_int (SL + 0x122)) by pcw.
    iEval (rewrite Hpp122) in "Hpc".
    assert (HM4ra : (M4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3ra | nz]).
    (* ===== +0x122 c.ret ===== *)
    iApply (wp_cret_s_sconf (mword_of_int (SL + 0x122)) Rra M4 K b
              ltac:(nz) with "Hcg Hpc []").
    { iApply (slki_122 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (M4 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HM4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE HANDOVER ===== *)
    assert (Hwv' : add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 19 : mword 6)))
                   = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite Hwv; exact Hsp0).
    assert (Csp : (M4 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /M4 upd_eq; exact Hwv').
    assert (Cs0 : (M4 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s0 | nz]).
    assert (Cs1 : (M4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s1 | nz]).
    assert (Cs2 : (M4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s2 | nz]).
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra5 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3a0 | nz]).
    assert (Hfin : sl_thr m M4).
    { intros c Hc N2 N8 N9 N18. rewrite /M4 upd_ne; [| regne].
      exact (HM3thr c Hc N2 N8 N9 N18). }
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! M4 with "[%] [%] Hcg Hpc").
    { unfold callee_saved. split_and!;
        [ exact Csp | exact Cs0 | exact Cs1 | exact Cs2
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx ]. }
    { exact HM4a0. }
  Qed.

End ProofSysLinkEpilogue.
