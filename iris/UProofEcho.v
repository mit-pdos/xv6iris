(* UProofEcho.v -- the VERIFIED-EXECUTION proofs of `echo`'s two DIVERGING
   functions (claude-notes/projects/user-echo.md):

     wp_echo_main   main  @0x0    prologue; the argv loop; exit(0)
     wp_echo_start  start @0x7c   prologue; jal main; (jal exit is dead)

   The leaf functions -- the two syscall stubs and `strlen` -- are
   UProofEchoA.v.  `wp_echo_start` is THE top-level statement about the echo
   process: from the loaded image, the argument area `exec()` built and the
   entry registers, the machine runs safely forever under the kernel's trap
   services, and every buffer it hands to write() is a readable window of its
   own image.

   `main`'s loop is proved by ordinary Rocq induction on `argc - 1 - i`, not
   by `iLöb`: it is BOUNDED, so no leaf has to expose a `▷`. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import AlignBits UserBits.
Require Import ExecCommon WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeFetch.
Require Import WpUmodeStep WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UCodeEcho USpecEcho UProofEchoA.
Require User.EchoSyms User.EchoInstrs User.EchoData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 THE ARGV INDEX CHAIN -- main's one piece of real arithmetic.        *)
(*                                                                        *)
(* The C source's                                                         *)
(*     s1 = argv + 1;  s5 = &argv[argc-1];  s4 = &argv[argc];             *)
(* compiles to seven instructions that never mention argc-1 or argc:       *)
(*                                                                        *)
(*   1a  addi   s1,a1,8           s1 = argv + 8                            *)
(*   1e  addiw  a0,a0,-2          a0 = (int32) (argc - 2)                  *)
(*   20  slli   a5,a0,0x20        \  the zero-extend-and-scale idiom:      *)
(*   24  srli   a0,a5,0x1d        /  a0 = (uint32)(argc-2) * 8             *)
(*   28  add    s5,s1,a0                                                   *)
(*   2c  addi   a1,a1,16                                                   *)
(*   2e  add    s4,a1,a0                                                   *)
(*                                                                        *)
(* Discharged ONCE, here, in the exact shape the leaves hand each value    *)
(* over, so the WP walk itself only ever rewrites by this lemma.  The      *)
(* generic half -- [moi_addw], [moi_shl32_shr29], [moi_add] -- is          *)
(* UmodeArith.v; what is echo-specific is only the immediates.            *)
(* ===================================================================== *)

Lemma echo_argv_chain (argc av : Z) :
  2 <= argc < 2 ^ 31 -> 0 <= av -> av + 8 * argc <= 2 ^ 38 ->
  let a0_1 := sign_extend' 64
       (subrange_vec_dec
          (add_vec (mword_of_int argc : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6)))) 31 0) in
  let a0_2 := shift_bits_right
       (shift_bits_left a0_1
          (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
       (subrange_vec_dec (mword_of_int 29 : mword 6) (Z.sub log2_xlen 1) 0) in
  let s1   := add_vec (mword_of_int av : mword 64)
                (sign_extend' 64 (mword_of_int 8 : mword 12)) in
  let s5   := add_vec s1 a0_2 in
  let a1_1 := add_vec (mword_of_int av : mword 64)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) in
  let s4   := add_vec a1_1 a0_2 in
  a0_2 = mword_of_int (8 * (argc - 2)) /\
  s5   = mword_of_int (av + 8 * (argc - 1)) /\
  s4   = mword_of_int (av + 8 * argc).
Proof.
  intros Hargc Hav Hhi a0_1 a0_2 s1 s5 a1_1 s4.
  assert (E62 : sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6))
                = (mword_of_int (-2) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (E8 : sign_extend' 64 (mword_of_int 8 : mword 12) = (mword_of_int 8 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (E16 : sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))
                = (mword_of_int 16 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Ha1 : a0_1 = mword_of_int (argc - 2)).
  { unfold a0_1. rewrite E62. apply moi_addw. unfold Z31; lia. }
  assert (Ha2 : a0_2 = mword_of_int (8 * (argc - 2))).
  { unfold a0_2. rewrite Ha1.
    rewrite (moi_shl32_shr29 (argc - 2) ltac:(unfold Z32; lia)).
    f_equal; lia. }
  split_and!.
  - exact Ha2.
  - unfold s5, s1. rewrite E8 Ha2 !moi_add. f_equal; lia.
  - unfold s4, a1_1. rewrite E16 Ha2 !moi_add. f_equal; lia.
Qed.

(* ===================================================================== *)
(* §2 PURE BRICKS.                                                        *)
(*                                                                        *)
(* Four small facts the walk below needs and that the generic layer does   *)
(* not (yet) carry.  All of them are HOIST CANDIDATES -- see the comment   *)
(* at each.                                                               *)
(* ===================================================================== *)

(* HOIST CANDIDATE (UmodeAbi.v, beside [uz_mod4096_of_mod16]): its mod-8
   twin.  An 8-aligned address leaves at least 8 bytes in its page, which
   is exactly the load leaf's [Z.rem (uint va) 4096 <= 4088] premise. *)

(* HOIST CANDIDATE (UmodeAbi.v, beside [uv_stack_slot]): the argument
   area's counterpart of a stack slot -- every side condition an 8-byte
   ACCESS needs at an 8-aligned, Sv39-canonical address that is NOT on the
   stack.  [main]'s [ld s2,0(s1)] is the one instance. *)

(* [uv_stack_slot] with the slot address NORMALIZED to [mword_of_int]:
   every live value in this proof is carried in that shape, and a raw
   [add_vec_int (add_vec_int sp0 (- n)) d] tower in the middle of a store's
   side conditions would have to be re-normalized at each of main's eight
   prologue stores.  HOIST CANDIDATE: this is the shape [uv_stack_slot]
   should have had. *)

(* the bottom of a budget, normalized the same way *)

(* HOIST CANDIDATE (UmodeAbi.v, beside [uM_only]): ONE 8-byte store inside
   the disturbed window is a [uM_only]. *)
Lemma uM_only_store8 (M : gmap Z (bv 8)) (a lo n : Z) (v : mword 64) :
  lo <= a -> a + 8 <= lo + n -> uM_only M (uM_store8 M a v) lo n.
Proof.
  intros H1 H2. split.
  - intros k Hk. exact (uM_store8_is_Some M a v k Hk).
  - intros k Hk. apply uM_store8_lookup_ne.
    intros j Hj. pose proof (Nat2Z.is_nonneg j). lia.
Qed.

(* [upd_eq] / [upd_ne] in the shape a lookup CHAIN wants.  A register that
   survives a call is read back through a sixteen-deep insert tower, and
   [apply]ing these peels one insert per step (the durable-notes rule: never
   [rewrite upd_eq]). *)
Lemma upd_ne_tr (f : regfile) (kk jj : regidx) (v w : mword 64) :
  jj <> kk -> f !!! jj = w -> (<[kk := v]> f) !!! jj = w.
Proof. intros Hne Hw. rewrite (upd_ne f kk jj v Hne). exact Hw. Qed.

Lemma upd_eq_tr (f : regfile) (kk : regidx) (v w : mword 64) :
  v = w -> (<[kk := v]> f) !!! kk = w.
Proof. intro H. rewrite (upd_eq f kk v). exact H. Qed.

(* HOIST CANDIDATE (UmodeAbi.v, beside [ucallee_saved]): writing a
   CALLER-saved register preserves the callee-saved set.  Without it a
   loop body's five register invariants have to be walked back through a
   sixteen-deep insert tower one [upd_ne] at a time. *)

(* ===================================================================== *)
(* §3 THE TWO DIVERGING FUNCTIONS.                                        *)
(* ===================================================================== *)

Section UProofEcho.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  Local Notation Ysxv6 := (xv6_sys_protocol C pt).

  (* ------------------------------------------------------------------- *)
  (* THE PROLOGUE STORE, once.  main spills eight registers and start two, *)
  (* all by [c.sdsp rs2, d(sp)] into a slot of the budget the function      *)
  (* just carved; the only things that vary are the pc, the register, the   *)
  (* offset and the budget's size.                                         *)
  (* ------------------------------------------------------------------- *)
  Local Lemma echo_pro_store (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 pc : mword 64) (uimm : mword 6) (rs2 : mword 5) (n d : Z) :
    uinstr pt M pc true (C_SDSP (uimm, Regidx rs2)) ->
    uv_stack pt M sp0 n ->
    0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
    m !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - n) : mword 64) ->
    (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64)
      = mword_of_int d ->
    uv_cap_gpr (CID := CIDp) C pt Ysxv6 M m -∗
    pc_is (CID := CIDp) pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ysxv6
         (uM_store8 M (uint sp0 - n + d) (m !!! Regidx rs2)) m -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui HS Hd0 Hdn Hd8 Hsp Himm.
    destruct (uv_stack_slot_moi pt M sp0 n d (mword_of_int (uint sp0 - n + d))
                HS Hd0 Hdn Hd8 eq_refl)
      as (Hu & (w & Hl & Hok & _) & Hcanon & Hpg & Hal & Hb).
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_csdsp C pt Ysxv6 M m pc uimm rs2 w
              (mword_of_int (uint sp0 - n + d)) (m !!! Regidx rs2)
              Hui
              ltac:(rewrite Hsp; rewrite Himm; rewrite moi_add; reflexivity)
              eq_refl Hl Hok Hcanon Hpg Hal Hb
              with "Hcg Hpc [Hcont]").
    iIntros (CID0) "Hcg Hpc".
    iEval (rewrite Hu) in "Hcg".
    iApply ("Hcont" with "Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE EXIT TAIL @0x76: c.li a0,0; jal exit.  Reached from the           *)
  (* [argc <= 1] arm of main's guard and from the newline path at the end  *)
  (* of the loop -- and from nowhere else.                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma echo_exit_tail (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    echo_layout pt -> echo_text_sub M ->
    uv_cap_gpr (CID := CIDp) C pt Ysxv6 M m -∗
    pc_is (CID := CIDp) (mword_of_int 0x76) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Htext.
    iIntros "Hcg Hpc".
    (* ---- 0x76  c.li a0,0 ---- *)
    assert (Hw0 : (mword_of_int 0 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Ysxv6 M m (mword_of_int 0x76)
              (mword_of_int 0 : mword 6) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 64)
              (ui_echo_76 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hw0
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m).
    assert (E76 : add_vec_int (mword_of_int 0x76 : mword 64) 2 = mword_of_int 0x78)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E76) in "Hpc".
    (* ---- 0x78  jal ra,0x332 <exit> -- diverges ---- *)
    assert (Htj : (mword_of_int EchoSyms.exit : mword 64)
                  = add_vec (mword_of_int 0x78)
                      (sign_extend' 64 (mword_of_int 698 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x7c : mword 64)
                  = add_vec_int (mword_of_int 0x78 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Ysxv6 M m1 (mword_of_int 0x78)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int EchoSyms.exit) (mword_of_int 0x7c)
              (ui_echo_78 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iApply (wp_echo_exit C pt CID2 M
              (<[Regidx ra_idx := regval_into_reg (mword_of_int 0x7c : mword 64)]> m1)
              Hlay Htext with "Hcg Hpc").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE ARGV LOOP @0x4e -- an ORDINARY Rocq induction on the nat measure  *)
  (* [k] bounding [argc - 1 - i], NOT an [iLoeb]: the loop is BOUNDED and  *)
  (* every leaf it uses is later-free (WpUmodeBranch.v).  The loop         *)
  (* DIVERGES (it ends in exit), so it has no continuation.                *)
  (* ------------------------------------------------------------------- *)
  Lemma echo_loop (sp0 : mword 64) (argc av : Z) (k : nat) :
    forall (CIDp : CpuId) (Mc : gmap Z (bv 8)) (mc : regfile) (i : Z),
      echo_layout pt ->
      echo_img_sub Mc ->
      uargs pt Mc av argc (uint sp0) ->
      uv_stack pt Mc sp0 80 ->
      1 <= i <= argc - 1 ->
      argc - 1 - i < Z.of_nat k ->
      mc !!! Regidx (mword_of_int 9 : mword 5)
        = (mword_of_int (av + 8 * i) : mword 64) ->
      mc !!! Regidx (mword_of_int 21 : mword 5)
        = (mword_of_int (av + 8 * (argc - 1)) : mword 64) ->
      mc !!! Regidx (mword_of_int 20 : mword 5)
        = (mword_of_int (av + 8 * argc) : mword 64) ->
      mc !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 1 : mword 64) ->
      mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 2352 : mword 64) ->
      mc !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Ysxv6 Mc mc -∗
      pc_is (CID := CIDp) (mword_of_int 0x4e) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction k as [ | k IH ];
      intros CIDp Mc mc i Hlay Himg Hargs Hst Hi Hk Hr9 Hr21 Hr20 Hr19 Hr22 Hrsp.
    { (* k = 0 is vacuous: the measure is STRICTLY below it *)
      exfalso. lia. }
    assert (Hk' : argc - 1 - i <= Z.of_nat k)
      by (rewrite Nat2Z.inj_succ in Hk; lia).
    pose proof (echo_img_text Mc Himg) as Htext.
    pose proof (echo_img_data Mc Himg) as Hdata.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    pose proof (ua_al _ _ _ _ _ Hargs) as Halr.
    pose proof (ua_argc _ _ _ _ _ Hargs) as Hargcb.
    assert (Hargcz : 0 <= argc < 2147483648)
      by (change (2 ^ 31) with 2147483648 in Hargcb; exact Hargcb).
    pose proof (ua_rd _ _ _ _ _ Hargs) as Hrdav.
    pose proof (urd_lo _ _ _ _ Hrdav) as Hav0.
    pose proof (urd_hi _ _ _ _ Hrdav) as Havhi0.
    assert (Havhi : av + 8 * argc <= 274877906944)
      by (change (2 ^ 38) with 274877906944 in Havhi0; exact Havhi0).
    assert (Havm8 : av mod 8 = 0)
      by (rewrite Z.rem_mod_nonneg in Halr; [ exact Halr | lia | lia ]).
    pose proof (us_lo _ _ _ _ Hst) as Hlo80.
    pose proof (us_canon _ _ _ _ Hst) as Hcan80.
    assert (Hcanz : uint sp0 <= 274877906944)
      by (change (2 ^ 38) with 274877906944 in Hcan80; exact Hcan80).
    (* strlen's 16-byte slice, at main's post-prologue sp *)
    destruct (uv_stack_split pt Mc sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    assert (Hst16 : uv_stack pt Mc (mword_of_int (uint sp0 - 64) : mword 64) 16)
      by (rewrite <- (uv_stack_sp_moi pt Mc sp0 64 Hstf); exact Hstm).
    assert (Hu64 : uint (mword_of_int (uint sp0 - 64) : mword 64) = uint sp0 - 64)
      by (apply uint_moi; unfold Z64; lia).
    (* the argv entry at index i *)
    destruct (ua_ptr _ _ _ _ _ Hargs i ltac:(lia))
      as (p & len & Hbytes & Hp0 & Hplo & Hlen & Hstr & Hrdp).
    assert (Hlenz : 0 <= len < 2147483648)
      by (change (2 ^ 31) with 2147483648 in Hlen; exact Hlen).
    pose proof (urd_hi _ _ _ _ Hrdp) as Hphi0.
    assert (Hphi : p + (len + 1) <= 274877906944)
      by (change (2 ^ 38) with 274877906944 in Hphi0; exact Hphi0).
    (* the load's address, and every side condition it needs *)
    destruct (uv_slot8_facts (av + 8 * i) (mword_of_int (av + 8 * i))
                ltac:(lia)
                ltac:(rewrite Zplus_mod; rewrite Havm8;
                      replace (8 * i) with (i * 8) by lia;
                      rewrite Z_mod_mult; reflexivity)
                ltac:(change (2 ^ 38) with 274877906944; lia)
                eq_refl)
      as (Huva & Hcanva & Hpgva & Halva).
    destruct (urd_leaf _ _ _ _ Hrdav (8 * i) ltac:(lia)) as (wld & Hwld & Hwldok).
    assert (Hldb : forall j : nat, (j < 8)%nat ->
              exists bb : bv 8,
                Mc !! (uint (mword_of_int (av + 8 * i) : mword 64) + Z.of_nat j)
                   = Some bb).
    { intros j Hj. rewrite Huva. eexists. exact (Hbytes j Hj). }
    assert (Hwv : (mword_of_int p : mword 64)
                  = uM_word Mc (uint (mword_of_int (av + 8 * i) : mword 64)) 8).
    { rewrite Huva. symmetry.
      apply (uM_bytes_inj Mc (av + 8 * i)).
      - refine (uM_word_bytes Mc (av + 8 * i) 8 ltac:(lia) _).
        intros j Hj. eexists. exact (Hbytes j Hj).
      - exact Hbytes. }
    iIntros "Hcg Hpc".
    (* ---- 0x4e  ld s2,0(s1) -- s2 := argv[i] ---- *)
    iApply (wp_uv_ld C pt Ysxv6 Mc mc (mword_of_int 0x4e)
              (mword_of_int 0 : mword 12) (mword_of_int 9 : mword 5)
              (mword_of_int 18 : mword 5)
              wld (mword_of_int (av + 8 * i)) (mword_of_int p)
              (ui_echo_4e pt Mc Hlay Htext)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hr9;
                    assert (E0 : (sign_extend' 64 (mword_of_int 0 : mword 12)
                                  : mword 64) = mword_of_int 0)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite E0; rewrite moi_add; f_equal; lia)
              Hwld Hwldok Hcanva Hpgva Halva Hldb Hwv
              with "Hcg Hpc").
    iIntros (K1) "Hcg Hpc".
    set (n1 := <[Regidx (mword_of_int 18 : mword 5)
                 := regval_into_reg (mword_of_int p : mword 64)]> mc).
    assert (E4e : add_vec_int (mword_of_int 0x4e : mword 64) 4 = mword_of_int 0x52)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E4e) in "Hpc".
    (* ---- 0x52  c.mv a0,s2 ---- *)
    assert (Hs2_1 : n1 !!! Regidx (mword_of_int 18 : mword 5)
                    = (mword_of_int p : mword 64))
      by (apply upd_eq_tr; reflexivity).
    iApply (wp_uv_cmv C pt Ysxv6 Mc n1 (mword_of_int 0x52)
              (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              (mword_of_int p : mword 64)
              (ui_echo_52 pt Mc Hlay Htext)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_1; rewrite moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (K2) "Hcg Hpc".
    set (n2 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (mword_of_int p : mword 64)]> n1).
    assert (E52 : add_vec_int (mword_of_int 0x52 : mword 64) 2 = mword_of_int 0x54)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E52) in "Hpc".
    (* ---- 0x54  jal ra,0xdc <strlen> ---- *)
    assert (Htj1 : (mword_of_int EchoSyms.strlen : mword 64)
                   = add_vec (mword_of_int 0x54)
                       (sign_extend' 64 (mword_of_int 136 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj1 : (mword_of_int 0x58 : mword 64)
                   = add_vec_int (mword_of_int 0x54 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Ysxv6 Mc n2 (mword_of_int 0x54)
              (mword_of_int 136 : mword 21) ra_idx
              (mword_of_int EchoSyms.strlen) (mword_of_int 0x58)
              (ui_echo_54 pt Mc Hlay Htext)
              ltac:(vm_compute; discriminate) Htj1 Hwj1
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K3) "Hcg Hpc".
    set (n3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x58 : mword 64)]> n2).
    (* ---- the call: strlen(argv[i]) ---- *)
    assert (Hsp_3 : n3 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hrsp. }
    assert (Ha0_3 : n3 !!! Regidx a0_idx = (mword_of_int p : mword 64)).
    { rewrite /n3. apply upd_ne_tr; [ vm_compute; discriminate | ].
      rewrite /n2. apply upd_eq_tr; reflexivity. }
    assert (Hra_3 : n3 !!! Regidx ra_idx = (mword_of_int 0x58 : mword 64))
      by (apply upd_eq_tr; reflexivity).
    iApply (wp_echo_strlen C pt K3 Mc n3 (mword_of_int (uint sp0 - 64)) p len
              Hlay Htext Hsp_3 Hst16 Ha0_3 Hstr Hrdp
              ltac:(change (2 ^ 31) with 2147483648; lia)
              ltac:(rewrite Hu64; lia)
              ltac:(rewrite Hra_3; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K4 mp Mp) "%Hcs0 %Hpa0 %Hponly Hcg Hpc".
    iEval (rewrite Hra_3) in "Hpc".
    rewrite Hu64 in Hponly.
    replace (uint sp0 - 64 - 16) with (uint sp0 - 80) in Hponly by lia.
    (* every image predicate, carried across strlen's frame in one step *)
    assert (HkT : forall (kk : Z) (bb : bv 8),
              EchoInstrs.echo_bytes !! kk = Some bb -> kk < uint sp0 - 80)
      by (intros kk bb Hkb; pose proof (echo_bytes_key_lt kk bb Hkb); lia).
    assert (HkD : forall (kk : Z) (bb : bv 8),
              EchoData.echo_data !! kk = Some bb -> kk < uint sp0 - 80)
      by (intros kk bb Hkb; pose proof (echo_data_key_lt kk bb Hkb); lia).
    assert (HtP : echo_text_sub Mp)
      by exact (uM_only_img EchoInstrs.echo_bytes Mc Mp (uint sp0 - 80) 16
                  HkT Hponly Htext).
    assert (HdP : echo_data_sub Mp)
      by exact (uM_only_img EchoData.echo_data Mc Mp (uint sp0 - 80) 16
                  HkD Hponly Hdata).
    assert (HiP : echo_img_sub Mp) by exact (conj HtP HdP).
    assert (HstP : uv_stack pt Mp sp0 80)
      by exact (uM_only_stack pt Mc Mp sp0 80 (uint sp0 - 80) 16 Hponly Hst).
    assert (HargsP : uargs pt Mp av argc (uint sp0))
      by exact (uM_only_uargs pt Mc Mp av argc (uint sp0) (uint sp0 - 80) 16
                  Hponly ltac:(lia) Hargs).
    assert (Hdisj : uint sp0 - 80 + 16 <= p \/ p + (len + 1) <= uint sp0 - 80)
      by (left; lia).
    assert (HrdpP : uv_rd pt Mp p (len + 1))
      by exact (uM_only_rd pt Mc Mp p (len + 1) (uint sp0 - 80) 16
                  Hponly Hdisj Hrdp).
    assert (Hpa0' : mp !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int len : mword 64)) by exact Hpa0.
    (* ---- 0x58  c.mv a2,a0 ---- *)
    iApply (wp_uv_cmv C pt Ysxv6 Mp mp (mword_of_int 0x58)
              (mword_of_int 12 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int len : mword 64)
              (ui_echo_58 pt Mp Hlay HtP)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hpa0'; rewrite moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (K5) "Hcg Hpc".
    set (n4 := <[Regidx (mword_of_int 12 : mword 5)
                 := regval_into_reg (mword_of_int len : mword 64)]> mp).
    assert (E58 : add_vec_int (mword_of_int 0x58 : mword 64) 2 = mword_of_int 0x5a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E58) in "Hpc".
    (* ---- 0x5a  c.mv a1,s2 (s2 survived the call: it is callee-saved) ---- *)
    assert (Hs2_P : mp !!! Regidx (mword_of_int 18 : mword 5)
                    = (mword_of_int p : mword 64)).
    { rewrite (Hcs0 (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n3 /n2.
      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hs2_1. }
    assert (Hs2_4 : n4 !!! Regidx (mword_of_int 18 : mword 5)
                    = (mword_of_int p : mword 64)).
    { rewrite /n4. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hs2_P. }
    iApply (wp_uv_cmv C pt Ysxv6 Mp n4 (mword_of_int 0x5a)
              (mword_of_int 11 : mword 5) (mword_of_int 18 : mword 5)
              (mword_of_int p : mword 64)
              (ui_echo_5a pt Mp Hlay HtP)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_4; rewrite moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (K6) "Hcg Hpc".
    set (n5 := <[Regidx (mword_of_int 11 : mword 5)
                 := regval_into_reg (mword_of_int p : mword 64)]> n4).
    assert (E5a : add_vec_int (mword_of_int 0x5a : mword 64) 2 = mword_of_int 0x5c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E5a) in "Hpc".
    (* ---- 0x5c  c.mv a0,s3 ---- *)
    assert (Hs3_5 : n5 !!! Regidx (mword_of_int 19 : mword 5)
                    = (mword_of_int 1 : mword 64)).
    { rewrite /n5 /n4.
      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      rewrite (Hcs0 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hr19. }
    iApply (wp_uv_cmv C pt Ysxv6 Mp n5 (mword_of_int 0x5c)
              (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5)
              (mword_of_int 1 : mword 64)
              (ui_echo_5c pt Mp Hlay HtP)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_5; rewrite moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (K7) "Hcg Hpc".
    set (n6 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (mword_of_int 1 : mword 64)]> n5).
    assert (E5c : add_vec_int (mword_of_int 0x5c : mword 64) 2 = mword_of_int 0x5e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E5c) in "Hpc".
    (* ---- 0x5e  jal ra,0x352 <write> ---- *)
    assert (Htj2 : (mword_of_int EchoSyms.write : mword 64)
                   = add_vec (mword_of_int 0x5e)
                       (sign_extend' 64 (mword_of_int 756 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj2 : (mword_of_int 0x62 : mword 64)
                   = add_vec_int (mword_of_int 0x5e : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Ysxv6 Mp n6 (mword_of_int 0x5e)
              (mword_of_int 756 : mword 21) ra_idx
              (mword_of_int EchoSyms.write) (mword_of_int 0x62)
              (ui_echo_5e pt Mp Hlay HtP)
              ltac:(vm_compute; discriminate) Htj2 Hwj2
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K8) "Hcg Hpc".
    set (n7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x62 : mword 64)]> n6).
    (* ---- the call: write(1, argv[i], strlen(argv[i])) ---- *)
    assert (Ha1_7 : n7 !!! Regidx a1_idx = (mword_of_int p : mword 64)).
    { rewrite /n7 /n6.
      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      rewrite /n5. apply upd_eq_tr; reflexivity. }
    assert (Ha2_7 : n7 !!! Regidx a2_idx = (mword_of_int len : mword 64)).
    { rewrite /n7 /n6 /n5.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      rewrite /n4. apply upd_eq_tr; reflexivity. }
    assert (Hra_7 : n7 !!! Regidx ra_idx = (mword_of_int 0x62 : mword 64))
      by (apply upd_eq_tr; reflexivity).
    assert (Hbuf1 : uv_rd pt Mp (uint (n7 !!! Regidx a1_idx))
                      (uint (n7 !!! Regidx a2_idx))).
    { rewrite Ha1_7. rewrite Ha2_7.
      rewrite (uint_moi p ltac:(unfold Z64; lia)).
      rewrite (uint_moi len ltac:(unfold Z64; lia)).
      exact (uv_rd_sub pt Mp p (len + 1) p len HrdpP ltac:(lia) ltac:(lia)
               ltac:(lia)). }
    iApply (wp_echo_write C pt K8 Mp n7 Hlay HtP Hbuf1
              ltac:(rewrite Hra_7; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K9 ret1) "Hcg Hpc".
    iEval (rewrite Hra_7) in "Hpc".
    set (n8 := <[Regidx a0_idx := ret1]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> n7)).
    (* the callee-saved set survived BOTH the call and the clobbers around it *)
    assert (Hcsa : ucallee_saved n1 n2)
      by (rewrite /n2; apply ucs_caller; vm_compute; reflexivity).
    assert (Hcsb : ucallee_saved n1 n3).
    { apply (ucallee_saved_trans n1 n2 n3 Hcsa).
      rewrite /n3. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsc : ucallee_saved n1 mp)
      by exact (ucallee_saved_trans n1 n3 mp Hcsb Hcs0).
    assert (Hcsd : ucallee_saved n1 n4).
    { apply (ucallee_saved_trans n1 mp n4 Hcsc).
      rewrite /n4. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcse : ucallee_saved n1 n5).
    { apply (ucallee_saved_trans n1 n4 n5 Hcsd).
      rewrite /n5. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsf : ucallee_saved n1 n6).
    { apply (ucallee_saved_trans n1 n5 n6 Hcse).
      rewrite /n6. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsg : ucallee_saved n1 n7).
    { apply (ucallee_saved_trans n1 n6 n7 Hcsf).
      rewrite /n7. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsh : ucallee_saved n1 n8).
    { apply (ucallee_saved_trans n1 n7 n8 Hcsg).
      apply (ucallee_saved_trans n7
               (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> n7) n8).
      - apply ucs_caller; vm_compute; reflexivity.
      - rewrite /n8. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hs1_8 : n8 !!! Regidx (mword_of_int 9 : mword 5)
                    = (mword_of_int (av + 8 * i) : mword 64)).
    { rewrite (Hcsh (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr9. }
    assert (Hs5_8 : n8 !!! Regidx (mword_of_int 21 : mword 5)
                    = (mword_of_int (av + 8 * (argc - 1)) : mword 64)).
    { rewrite (Hcsh (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr21. }
    assert (Hs4_8 : n8 !!! Regidx (mword_of_int 20 : mword 5)
                    = (mword_of_int (av + 8 * argc) : mword 64)).
    { rewrite (Hcsh (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr20. }
    assert (Hs3_8 : n8 !!! Regidx (mword_of_int 19 : mword 5)
                    = (mword_of_int 1 : mword 64)).
    { rewrite (Hcsh (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr19. }
    assert (Hs6_8 : n8 !!! Regidx (mword_of_int 22 : mword 5)
                    = (mword_of_int 2352 : mword 64)).
    { rewrite (Hcsh (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr22. }
    assert (Hsp_8 : n8 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (Hcsh (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hrsp. }
    (* ---- 0x62  bne s1,s5,0x3e -- separator or newline? ---- *)
    assert (Etgt3e : (mword_of_int 0x3e : mword 64)
                     = add_vec (mword_of_int 0x62)
                         (sign_extend' 64 (mword_of_int 8156 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec i (argc - 1)) as [Hieq | Hine].
    - (* i = argc-1: the last argument -- newline, then exit *)
      iApply (wp_uv_btype C pt Ysxv6 Mp n8 (mword_of_int 0x62)
                (mword_of_int 8156 : mword 13) (mword_of_int 21 : mword 5)
                (mword_of_int 9 : mword 5) BNE false (mword_of_int 0x3e)
                (ui_echo_62 pt Mp Hlay HtP)
                ltac:(cbn [uv_btaken]; rewrite Hs1_8; rewrite Hs5_8;
                      rewrite (moi_neq_vec (av + 8 * i) (av + 8 * (argc - 1))
                                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia));
                      rewrite Hieq; rewrite Z.eqb_refl; reflexivity)
                Etgt3e ltac:(intro Hc; discriminate Hc)
                with "Hcg Hpc").
      iIntros (K10) "Hcg Hpc".
      assert (E62 : (if false then (mword_of_int 0x3e : mword 64)
                     else add_vec_int (mword_of_int 0x62 : mword 64) 4)
                    = mword_of_int 0x66)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E62) in "Hpc".
      (* ---- 0x66  c.li a2,1 ---- *)
      assert (Hw1 : (mword_of_int 1 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cli C pt Ysxv6 Mp n8 (mword_of_int 0x66)
                (mword_of_int 1 : mword 6) (mword_of_int 12 : mword 5)
                (mword_of_int 1 : mword 64)
                (ui_echo_66 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate) Hw1
                with "Hcg Hpc").
      iIntros (K11) "Hcg Hpc".
      set (q1 := <[Regidx (mword_of_int 12 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> n8).
      assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2 = mword_of_int 0x68)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E66) in "Hpc".
      (* ---- 0x68  auipc a1,0x1 ---- *)
      iApply (wp_uv_auipc C pt Ysxv6 Mp q1 (mword_of_int 0x68)
                (mword_of_int 1 : mword 20) (mword_of_int 11 : mword 5)
                (mword_of_int 4200 : mword 64)
                (ui_echo_68 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K12) "Hcg Hpc".
      set (q2 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (mword_of_int 4200 : mword 64)]> q1).
      assert (E68 : add_vec_int (mword_of_int 0x68 : mword 64) 4 = mword_of_int 0x6c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E68) in "Hpc".
      (* ---- 0x6c  addi a1,a1,-1840 -- a1 := 0x938, the "\n" literal ---- *)
      assert (Ha1_q2 : q2 !!! Regidx (mword_of_int 11 : mword 5)
                       = (mword_of_int 4200 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uv_addi C pt Ysxv6 Mp q2 (mword_of_int 0x6c)
                (mword_of_int 2256 : mword 12) (mword_of_int 11 : mword 5)
                (mword_of_int 11 : mword 5) (mword_of_int 2360 : mword 64)
                (ui_echo_6c pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_q2; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K13) "Hcg Hpc".
      set (q3 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (mword_of_int 2360 : mword 64)]> q2).
      assert (E6c : add_vec_int (mword_of_int 0x6c : mword 64) 4 = mword_of_int 0x70)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E6c) in "Hpc".
      (* ---- 0x70  c.mv a0,a2 ---- *)
      assert (Ha2_q3 : q3 !!! Regidx (mword_of_int 12 : mword 5)
                       = (mword_of_int 1 : mword 64)).
      { rewrite /q3 /q2.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        rewrite /q1. apply upd_eq_tr; reflexivity. }
      iApply (wp_uv_cmv C pt Ysxv6 Mp q3 (mword_of_int 0x70)
                (mword_of_int 10 : mword 5) (mword_of_int 12 : mword 5)
                (mword_of_int 1 : mword 64)
                (ui_echo_70 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha2_q3; rewrite moi_add_zero_l; reflexivity)
                with "Hcg Hpc").
      iIntros (K14) "Hcg Hpc".
      set (q4 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> q3).
      assert (E70 : add_vec_int (mword_of_int 0x70 : mword 64) 2 = mword_of_int 0x72)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E70) in "Hpc".
      (* ---- 0x72  jal ra,0x352 <write> ---- *)
      assert (Htj3 : (mword_of_int EchoSyms.write : mword 64)
                     = add_vec (mword_of_int 0x72)
                         (sign_extend' 64 (mword_of_int 736 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hwj3 : (mword_of_int 0x76 : mword 64)
                     = add_vec_int (mword_of_int 0x72 : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_jal C pt Ysxv6 Mp q4 (mword_of_int 0x72)
                (mword_of_int 736 : mword 21) ra_idx
                (mword_of_int EchoSyms.write) (mword_of_int 0x76)
                (ui_echo_72 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate) Htj3 Hwj3
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K15) "Hcg Hpc".
      set (q5 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x76 : mword 64)]> q4).
      assert (Ha1_q5 : q5 !!! Regidx a1_idx = (mword_of_int 2360 : mword 64)).
      { rewrite /q5 /q4.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        rewrite /q3. apply upd_eq_tr; reflexivity. }
      assert (Ha2_q5 : q5 !!! Regidx a2_idx = (mword_of_int 1 : mword 64)).
      { rewrite /q5 /q4 /q3 /q2.
        do 4 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        rewrite /q1. apply upd_eq_tr; reflexivity. }
      assert (Hra_q5 : q5 !!! Regidx ra_idx = (mword_of_int 0x76 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      assert (Hbuf2 : uv_rd pt Mp (uint (q5 !!! Regidx a1_idx))
                        (uint (q5 !!! Regidx a2_idx))).
      { rewrite Ha1_q5. rewrite Ha2_q5.
        rewrite (uint_moi 2360 ltac:(unfold Z64; lia)).
        rewrite (uint_moi 1 ltac:(unfold Z64; lia)).
        exact (proj2 (echo_rodata_rd pt Mp Hlay HdP)). }
      iApply (wp_echo_write C pt K15 Mp q5 Hlay HtP Hbuf2
                ltac:(rewrite Hra_q5; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K16 ret2) "Hcg Hpc".
      iEval (rewrite Hra_q5) in "Hpc".
      iApply (echo_exit_tail K16 Mp _ Hlay HtP with "Hcg Hpc").
    - (* i < argc-1: the separator, then the next iteration *)
      iApply (wp_uv_btype C pt Ysxv6 Mp n8 (mword_of_int 0x62)
                (mword_of_int 8156 : mword 13) (mword_of_int 21 : mword 5)
                (mword_of_int 9 : mword 5) BNE true (mword_of_int 0x3e)
                (ui_echo_62 pt Mp Hlay HtP)
                ltac:(cbn [uv_btaken]; rewrite Hs1_8; rewrite Hs5_8;
                      rewrite (moi_neq_vec (av + 8 * i) (av + 8 * (argc - 1))
                                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia));
                      rewrite (proj2 (Z.eqb_neq (av + 8 * i)
                                        (av + 8 * (argc - 1))) ltac:(lia));
                      reflexivity)
                Etgt3e ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K10) "Hcg Hpc".
      (* [if true then _ else _] reduces by iota, so no pc rewrite is needed *)
      (* ---- 0x3e  c.mv a2,s3 ---- *)
      iApply (wp_uv_cmv C pt Ysxv6 Mp n8 (mword_of_int 0x3e)
                (mword_of_int 12 : mword 5) (mword_of_int 19 : mword 5)
                (mword_of_int 1 : mword 64)
                (ui_echo_3e pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_8; rewrite moi_add_zero_l; reflexivity)
                with "Hcg Hpc").
      iIntros (K11) "Hcg Hpc".
      set (r1 := <[Regidx (mword_of_int 12 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> n8).
      assert (E3e : add_vec_int (mword_of_int 0x3e : mword 64) 2 = mword_of_int 0x40)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E3e) in "Hpc".
      (* ---- 0x40  c.mv a1,s6 ---- *)
      assert (Hs6_r1 : r1 !!! Regidx (mword_of_int 22 : mword 5)
                       = (mword_of_int 2352 : mword 64)).
      { rewrite /r1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hs6_8. }
      iApply (wp_uv_cmv C pt Ysxv6 Mp r1 (mword_of_int 0x40)
                (mword_of_int 11 : mword 5) (mword_of_int 22 : mword 5)
                (mword_of_int 2352 : mword 64)
                (ui_echo_40 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs6_r1; rewrite moi_add_zero_l; reflexivity)
                with "Hcg Hpc").
      iIntros (K12) "Hcg Hpc".
      set (r2 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (mword_of_int 2352 : mword 64)]> r1).
      assert (E40 : add_vec_int (mword_of_int 0x40 : mword 64) 2 = mword_of_int 0x42)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E40) in "Hpc".
      (* ---- 0x42  c.mv a0,s3 ---- *)
      assert (Hs3_r2 : r2 !!! Regidx (mword_of_int 19 : mword 5)
                       = (mword_of_int 1 : mword 64)).
      { rewrite /r2 /r1.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]). exact Hs3_8. }
      iApply (wp_uv_cmv C pt Ysxv6 Mp r2 (mword_of_int 0x42)
                (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5)
                (mword_of_int 1 : mword 64)
                (ui_echo_42 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_r2; rewrite moi_add_zero_l; reflexivity)
                with "Hcg Hpc").
      iIntros (K13) "Hcg Hpc".
      set (r3 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> r2).
      assert (E42 : add_vec_int (mword_of_int 0x42 : mword 64) 2 = mword_of_int 0x44)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E42) in "Hpc".
      (* ---- 0x44  jal ra,0x352 <write> ---- *)
      assert (Htj3 : (mword_of_int EchoSyms.write : mword 64)
                     = add_vec (mword_of_int 0x44)
                         (sign_extend' 64 (mword_of_int 782 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hwj3 : (mword_of_int 0x48 : mword 64)
                     = add_vec_int (mword_of_int 0x44 : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_jal C pt Ysxv6 Mp r3 (mword_of_int 0x44)
                (mword_of_int 782 : mword 21) ra_idx
                (mword_of_int EchoSyms.write) (mword_of_int 0x48)
                (ui_echo_44 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate) Htj3 Hwj3
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K14) "Hcg Hpc".
      set (r4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x48 : mword 64)]> r3).
      assert (Ha1_r4 : r4 !!! Regidx a1_idx = (mword_of_int 2352 : mword 64)).
      { rewrite /r4 /r3.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        rewrite /r2. apply upd_eq_tr; reflexivity. }
      assert (Ha2_r4 : r4 !!! Regidx a2_idx = (mword_of_int 1 : mword 64)).
      { rewrite /r4 /r3 /r2.
        do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        rewrite /r1. apply upd_eq_tr; reflexivity. }
      assert (Hra_r4 : r4 !!! Regidx ra_idx = (mword_of_int 0x48 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      assert (Hbuf2 : uv_rd pt Mp (uint (r4 !!! Regidx a1_idx))
                        (uint (r4 !!! Regidx a2_idx))).
      { rewrite Ha1_r4. rewrite Ha2_r4.
        rewrite (uint_moi 2352 ltac:(unfold Z64; lia)).
        rewrite (uint_moi 1 ltac:(unfold Z64; lia)).
        exact (proj1 (echo_rodata_rd pt Mp Hlay HdP)). }
      iApply (wp_echo_write C pt K14 Mp r4 Hlay HtP Hbuf2
                ltac:(rewrite Hra_r4; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K15 ret2) "Hcg Hpc".
      iEval (rewrite Hra_r4) in "Hpc".
      set (r5 := <[Regidx a0_idx := ret2]>
                   (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> r4)).
      assert (Hcs85 : ucallee_saved n8 r5).
      { assert (T1 : ucallee_saved n8 r1)
          by (rewrite /r1; apply ucs_caller; vm_compute; reflexivity).
        assert (T2 : ucallee_saved n8 r2).
        { apply (ucallee_saved_trans n8 r1 r2 T1).
          rewrite /r2. apply ucs_caller; vm_compute; reflexivity. }
        assert (T3 : ucallee_saved n8 r3).
        { apply (ucallee_saved_trans n8 r2 r3 T2).
          rewrite /r3. apply ucs_caller; vm_compute; reflexivity. }
        assert (T4 : ucallee_saved n8 r4).
        { apply (ucallee_saved_trans n8 r3 r4 T3).
          rewrite /r4. apply ucs_caller; vm_compute; reflexivity. }
        apply (ucallee_saved_trans n8 r4 r5 T4).
        apply (ucallee_saved_trans r4
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> r4) r5).
        - apply ucs_caller; vm_compute; reflexivity.
        - rewrite /r5. apply ucs_caller; vm_compute; reflexivity. }
      (* ---- 0x48  c.addi s1,s1,8 -- i := i+1 ---- *)
      assert (Hs1_r5 : r5 !!! Regidx (mword_of_int 9 : mword 5)
                       = (mword_of_int (av + 8 * i) : mword 64)).
      { rewrite (Hcs85 (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs1_8. }
      iApply (wp_uv_caddi C pt Ysxv6 Mp r5 (mword_of_int 0x48)
                (mword_of_int 8 : mword 6) (mword_of_int 9 : mword 5)
                (mword_of_int (av + 8 * (i + 1)) : mword 64)
                (ui_echo_48 pt Mp Hlay HtP)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1_r5;
                      assert (E8b : (sign_extend' 64 (sign_extend' 12
                                       (mword_of_int 8 : mword 6)) : mword 64)
                                    = mword_of_int 8)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite E8b; rewrite moi_add; f_equal; lia)
                with "Hcg Hpc").
      iIntros (K16) "Hcg Hpc".
      set (r6 := <[Regidx (mword_of_int 9 : mword 5)
                   := regval_into_reg (mword_of_int (av + 8 * (i + 1))
                                       : mword 64)]> r5).
      assert (E48 : add_vec_int (mword_of_int 0x48 : mword 64) 2 = mword_of_int 0x4a)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E48) in "Hpc".
      (* ---- 0x4a  beq s1,s4,0x76 -- NEVER taken (i+1 <= argc-1 < argc) ---- *)
      assert (Hs1_r6 : r6 !!! Regidx (mword_of_int 9 : mword 5)
                       = (mword_of_int (av + 8 * (i + 1)) : mword 64))
        by (apply upd_eq_tr; reflexivity).
      assert (Hs4_r6 : r6 !!! Regidx (mword_of_int 20 : mword 5)
                       = (mword_of_int (av + 8 * argc) : mword 64)).
      { rewrite /r6. apply upd_ne_tr; [ vm_compute; discriminate | ].
        rewrite (Hcs85 (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs4_8. }
      iApply (wp_uv_btype C pt Ysxv6 Mp r6 (mword_of_int 0x4a)
                (mword_of_int 44 : mword 13) (mword_of_int 20 : mword 5)
                (mword_of_int 9 : mword 5) BEQ false (mword_of_int 0x76)
                (ui_echo_4a pt Mp Hlay HtP)
                ltac:(cbn [uv_btaken]; rewrite Hs1_r6; rewrite Hs4_r6;
                      rewrite (moi_eq_vec (av + 8 * (i + 1)) (av + 8 * argc)
                                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia));
                      rewrite (proj2 (Z.eqb_neq (av + 8 * (i + 1))
                                        (av + 8 * argc)) ltac:(lia));
                      reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc; discriminate Hc)
                with "Hcg Hpc").
      iIntros (K17) "Hcg Hpc".
      assert (E4a : (if false then (mword_of_int 0x76 : mword 64)
                     else add_vec_int (mword_of_int 0x4a : mword 64) 4)
                    = mword_of_int 0x4e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E4a) in "Hpc".
      (* ---- the next iteration: the measure strictly decreased ---- *)
      iApply (IH K17 Mp r6 (i + 1) Hlay HiP HargsP HstP
                ltac:(lia) ltac:(lia) Hs1_r6
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 21 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hs5_8)
                Hs4_r6
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 19 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hs3_8)
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 22 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hs6_8)
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 2 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hsp_8)
                with "Hcg Hpc").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* main @0x0: the eight-register prologue, the argc guard, the argv      *)
  (* index chain, then the loop.  DIVERGES.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_echo_main (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (argc av : Z) :
    wp_echo_main_body (CID := CIDp) C pt M m sp0 argc av.
  Proof.
    intros Hlay Himg Hsp Hst Hargc Hav Hargs.
    pose proof (echo_img_text M Himg) as Htext.
    pose proof (echo_img_data M Himg) as Hdata.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    pose proof (ua_argc _ _ _ _ _ Hargs) as Hargcb.
    assert (Hargcz : 0 <= argc < 2147483648)
      by (change (2 ^ 31) with 2147483648 in Hargcb; exact Hargcb).
    pose proof (ua_rd _ _ _ _ _ Hargs) as Hrdav.
    pose proof (urd_lo _ _ _ _ Hrdav) as Hav0.
    pose proof (urd_hi _ _ _ _ Hrdav) as Havhi0.
    assert (Havhi : av + 8 * argc <= 274877906944)
      by (change (2 ^ 38) with 274877906944 in Havhi0; exact Havhi0).
    destruct (uv_stack_split pt M sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    pose proof (us_lo _ _ _ _ Hst) as Hlo80.
    assert (HkT : forall (kk : Z) (bb : bv 8),
              EchoInstrs.echo_bytes !! kk = Some bb -> kk < uint sp0 - 64)
      by (intros kk bb Hkb; pose proof (echo_bytes_key_lt kk bb Hkb); lia).
    assert (HkD : forall (kk : Z) (bb : bv 8),
              EchoData.echo_data !! kk = Some bb -> kk < uint sp0 - 64)
      by (intros kk bb Hkb; pose proof (echo_data_key_lt kk bb Hkb); lia).
    iIntros "Hcg Hpc".
    iEval (rewrite Hsmain) in "Hpc".
    (* ---- 0x00  c.addi16sp sp,-64 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 64) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))
                    : mword 64) = mword_of_int (-64))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hsp' : m !!! Regidx csp_rs1 = (mword_of_int (uint sp0) : mword 64))
        by (rewrite moi_of_uint; exact Hsp).
      rewrite Hc. rewrite Hsp'. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Ysxv6 M m (mword_of_int 0x0)
              (mword_of_int 60 : mword 6) (mword_of_int (uint sp0 - 64))
              (ui_echo_00 pt M Hlay Htext) Hwsp
              with "Hcg Hpc").
    iIntros (K1) "Hcg Hpc".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64)]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64))).
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2 = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E00) in "Hpc".
    (* ---- 0x02  c.sdsp x1,56(sp) ---- *)
    iApply (echo_pro_store K1 M m1 sp0 (mword_of_int 0x02)
              (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5) 64 56
              (ui_echo_02 pt M Hlay Htext) Hstf
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K2) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 64 + 56)
                 (m1 !!! Regidx (mword_of_int 1 : mword 5))).
    assert (Ho1 : uM_only M M1 (uint sp0 - 64) 64).
    { rewrite /M1. apply uM_only_store8; lia. }
    assert (Ht1 : echo_text_sub M1)
      by exact (uM_only_img EchoInstrs.echo_bytes M M1 (uint sp0 - 64) 64
                  HkT Ho1 Htext).
    assert (Hs1 : uv_stack pt M1 sp0 64)
      by exact (uM_only_stack pt M M1 sp0 64 (uint sp0 - 64) 64 Ho1 Hstf).
    assert (E02 : add_vec_int (mword_of_int 0x02 : mword 64) 2 = mword_of_int 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E02) in "Hpc".
    (* ---- 0x04  c.sdsp x8,48(sp) ---- *)
    iApply (echo_pro_store K2 M1 m1 sp0 (mword_of_int 0x04)
              (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5) 64 48
              (ui_echo_04 pt M1 Hlay Ht1) Hs1
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K3) "Hcg Hpc".
    set (M2 := uM_store8 M1 (uint sp0 - 64 + 48)
                 (m1 !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Ho2 : uM_only M M2 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M1 M2 (uint sp0 - 64) 64 Ho1).
      rewrite /M2. apply uM_only_store8; lia. }
    assert (Ht2 : echo_text_sub M2)
      by exact (uM_only_img EchoInstrs.echo_bytes M M2 (uint sp0 - 64) 64
                  HkT Ho2 Htext).
    assert (Hs2 : uv_stack pt M2 sp0 64)
      by exact (uM_only_stack pt M M2 sp0 64 (uint sp0 - 64) 64 Ho2 Hstf).
    assert (E04 : add_vec_int (mword_of_int 0x04 : mword 64) 2 = mword_of_int 0x06)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E04) in "Hpc".
    (* ---- 0x06  c.sdsp x9,40(sp) ---- *)
    iApply (echo_pro_store K3 M2 m1 sp0 (mword_of_int 0x06)
              (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5) 64 40
              (ui_echo_06 pt M2 Hlay Ht2) Hs2
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K4) "Hcg Hpc".
    set (M3 := uM_store8 M2 (uint sp0 - 64 + 40)
                 (m1 !!! Regidx (mword_of_int 9 : mword 5))).
    assert (Ho3 : uM_only M M3 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M2 M3 (uint sp0 - 64) 64 Ho2).
      rewrite /M3. apply uM_only_store8; lia. }
    assert (Ht3 : echo_text_sub M3)
      by exact (uM_only_img EchoInstrs.echo_bytes M M3 (uint sp0 - 64) 64
                  HkT Ho3 Htext).
    assert (Hs3 : uv_stack pt M3 sp0 64)
      by exact (uM_only_stack pt M M3 sp0 64 (uint sp0 - 64) 64 Ho3 Hstf).
    assert (E06 : add_vec_int (mword_of_int 0x06 : mword 64) 2 = mword_of_int 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E06) in "Hpc".
    (* ---- 0x08  c.sdsp x18,32(sp) ---- *)
    iApply (echo_pro_store K4 M3 m1 sp0 (mword_of_int 0x08)
              (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5) 64 32
              (ui_echo_08 pt M3 Hlay Ht3) Hs3
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K5) "Hcg Hpc".
    set (M4 := uM_store8 M3 (uint sp0 - 64 + 32)
                 (m1 !!! Regidx (mword_of_int 18 : mword 5))).
    assert (Ho4 : uM_only M M4 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M3 M4 (uint sp0 - 64) 64 Ho3).
      rewrite /M4. apply uM_only_store8; lia. }
    assert (Ht4 : echo_text_sub M4)
      by exact (uM_only_img EchoInstrs.echo_bytes M M4 (uint sp0 - 64) 64
                  HkT Ho4 Htext).
    assert (Hs4 : uv_stack pt M4 sp0 64)
      by exact (uM_only_stack pt M M4 sp0 64 (uint sp0 - 64) 64 Ho4 Hstf).
    assert (E08 : add_vec_int (mword_of_int 0x08 : mword 64) 2 = mword_of_int 0x0a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E08) in "Hpc".
    (* ---- 0x0a  c.sdsp x19,24(sp) ---- *)
    iApply (echo_pro_store K5 M4 m1 sp0 (mword_of_int 0x0a)
              (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5) 64 24
              (ui_echo_0a pt M4 Hlay Ht4) Hs4
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K6) "Hcg Hpc".
    set (M5 := uM_store8 M4 (uint sp0 - 64 + 24)
                 (m1 !!! Regidx (mword_of_int 19 : mword 5))).
    assert (Ho5 : uM_only M M5 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M4 M5 (uint sp0 - 64) 64 Ho4).
      rewrite /M5. apply uM_only_store8; lia. }
    assert (Ht5 : echo_text_sub M5)
      by exact (uM_only_img EchoInstrs.echo_bytes M M5 (uint sp0 - 64) 64
                  HkT Ho5 Htext).
    assert (Hs5 : uv_stack pt M5 sp0 64)
      by exact (uM_only_stack pt M M5 sp0 64 (uint sp0 - 64) 64 Ho5 Hstf).
    assert (E0a : add_vec_int (mword_of_int 0x0a : mword 64) 2 = mword_of_int 0x0c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0a) in "Hpc".
    (* ---- 0x0c  c.sdsp x20,16(sp) ---- *)
    iApply (echo_pro_store K6 M5 m1 sp0 (mword_of_int 0x0c)
              (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5) 64 16
              (ui_echo_0c pt M5 Hlay Ht5) Hs5
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K7) "Hcg Hpc".
    set (M6 := uM_store8 M5 (uint sp0 - 64 + 16)
                 (m1 !!! Regidx (mword_of_int 20 : mword 5))).
    assert (Ho6 : uM_only M M6 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M5 M6 (uint sp0 - 64) 64 Ho5).
      rewrite /M6. apply uM_only_store8; lia. }
    assert (Ht6 : echo_text_sub M6)
      by exact (uM_only_img EchoInstrs.echo_bytes M M6 (uint sp0 - 64) 64
                  HkT Ho6 Htext).
    assert (Hs6 : uv_stack pt M6 sp0 64)
      by exact (uM_only_stack pt M M6 sp0 64 (uint sp0 - 64) 64 Ho6 Hstf).
    assert (E0c : add_vec_int (mword_of_int 0x0c : mword 64) 2 = mword_of_int 0x0e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0c) in "Hpc".
    (* ---- 0x0e  c.sdsp x21,8(sp) ---- *)
    iApply (echo_pro_store K7 M6 m1 sp0 (mword_of_int 0x0e)
              (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5) 64 8
              (ui_echo_0e pt M6 Hlay Ht6) Hs6
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K8) "Hcg Hpc".
    set (M7 := uM_store8 M6 (uint sp0 - 64 + 8)
                 (m1 !!! Regidx (mword_of_int 21 : mword 5))).
    assert (Ho7 : uM_only M M7 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M6 M7 (uint sp0 - 64) 64 Ho6).
      rewrite /M7. apply uM_only_store8; lia. }
    assert (Ht7 : echo_text_sub M7)
      by exact (uM_only_img EchoInstrs.echo_bytes M M7 (uint sp0 - 64) 64
                  HkT Ho7 Htext).
    assert (Hs7 : uv_stack pt M7 sp0 64)
      by exact (uM_only_stack pt M M7 sp0 64 (uint sp0 - 64) 64 Ho7 Hstf).
    assert (E0e : add_vec_int (mword_of_int 0x0e : mword 64) 2 = mword_of_int 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0e) in "Hpc".
    (* ---- 0x10  c.sdsp x22,0(sp) ---- *)
    iApply (echo_pro_store K8 M7 m1 sp0 (mword_of_int 0x10)
              (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5) 64 0
              (ui_echo_10 pt M7 Hlay Ht7) Hs7
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K9) "Hcg Hpc".
    set (M8 := uM_store8 M7 (uint sp0 - 64 + 0)
                 (m1 !!! Regidx (mword_of_int 22 : mword 5))).
    assert (Ho8 : uM_only M M8 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M7 M8 (uint sp0 - 64) 64 Ho7).
      rewrite /M8. apply uM_only_store8; lia. }
    assert (Ht8 : echo_text_sub M8)
      by exact (uM_only_img EchoInstrs.echo_bytes M M8 (uint sp0 - 64) 64
                  HkT Ho8 Htext).
    assert (Hs8 : uv_stack pt M8 sp0 64)
      by exact (uM_only_stack pt M M8 sp0 64 (uint sp0 - 64) 64 Ho8 Hstf).
    assert (E10 : add_vec_int (mword_of_int 0x10 : mword 64) 2 = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E10) in "Hpc".
    (* the image predicates at the post-prologue image, once *)
    assert (Hd8 : echo_data_sub M8)
      by exact (uM_only_img EchoData.echo_data M M8 (uint sp0 - 64) 64 HkD Ho8 Hdata).
    assert (Hi8 : echo_img_sub M8) by exact (conj Ht8 Hd8).
    assert (Hst8 : uv_stack pt M8 sp0 80)
      by exact (uM_only_stack pt M M8 sp0 80 (uint sp0 - 64) 64 Ho8 Hst).
    assert (Hargs8 : uargs pt M8 av argc (uint sp0))
      by exact (uM_only_uargs pt M M8 av argc (uint sp0) (uint sp0 - 64) 64
                  Ho8 ltac:(lia) Hargs).
    (* ---- 0x12  c.addi4spn s0,sp,64 ---- *)
    assert (Hw64 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8)))).
    { assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. rewrite Hsp1. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Ysxv6 M8 m1 (mword_of_int 0x12)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8)
              (mword_of_int 8 : mword 5) (mword_of_int (uint sp0))
              (ui_echo_12 pt M8 Hlay Ht8)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw64
              with "Hcg Hpc").
    iIntros (K10) "Hcg Hpc".
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 2 = mword_of_int 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E12) in "Hpc".
    (* ---- 0x14  c.li a5,1 ---- *)
    assert (Hw1 : (mword_of_int 1 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Ysxv6 M8 m2 (mword_of_int 0x14)
              (mword_of_int 1 : mword 6) (mword_of_int 15 : mword 5)
              (mword_of_int 1 : mword 64)
              (ui_echo_14 pt M8 Hlay Ht8)
              ltac:(vm_compute; discriminate) Hw1
              with "Hcg Hpc").
    iIntros (K11) "Hcg Hpc".
    set (m3 := <[Regidx (mword_of_int 15 : mword 5)
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m2).
    assert (E14 : add_vec_int (mword_of_int 0x14 : mword 64) 2 = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E14) in "Hpc".
    (* ---- 0x16  bge a5,a0,0x76 -- the argc guard ---- *)
    assert (Ha5_3 : m3 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int 1 : mword 64))
      by (apply upd_eq_tr; reflexivity).
    assert (Ha0_3 : m3 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int argc : mword 64)).
    { rewrite /m3 /m2.
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      rewrite /m1. apply upd_ne_tr; [ vm_compute; discriminate | ].
      exact Hargc. }
    assert (Ha1_3 : m3 !!! Regidx (mword_of_int 11 : mword 5)
                    = (mword_of_int av : mword 64)).
    { rewrite /m3 /m2.
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      rewrite /m1. apply upd_ne_tr; [ vm_compute; discriminate | ].
      exact Hav. }
    assert (Etgt76 : (mword_of_int 0x76 : mword 64)
                     = add_vec (mword_of_int 0x16)
                         (sign_extend' 64 (mword_of_int 96 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.geb 1 argc) eqn:Hge.
    - (* argc <= 1: the guard is taken, straight to the exit tail *)
      iApply (wp_uv_btype C pt Ysxv6 M8 m3 (mword_of_int 0x16)
                (mword_of_int 96 : mword 13) (mword_of_int 10 : mword 5)
                (mword_of_int 15 : mword 5) BGE true (mword_of_int 0x76)
                (ui_echo_16 pt M8 Hlay Ht8)
                ltac:(cbn [uv_btaken]; rewrite Ha5_3; rewrite Ha0_3;
                      rewrite (moi_ge_s 1 argc ltac:(unfold Z63; lia)
                                 ltac:(unfold Z63; lia));
                      exact (eq_sym Hge))
                Etgt76 ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K12) "Hcg Hpc".
      iApply (echo_exit_tail K12 M8 m3 Hlay Ht8 with "Hcg Hpc").
    - (* argc >= 2: the argv index chain, then the loop *)
      assert (Hargc2 : 2 <= argc).
      { destruct (Z.le_gt_cases argc 1) as [Hle | Hgt]; [ | lia ].
        exfalso. rewrite (proj2 (Z.geb_le 1 argc) Hle) in Hge. discriminate. }
      iApply (wp_uv_btype C pt Ysxv6 M8 m3 (mword_of_int 0x16)
                (mword_of_int 96 : mword 13) (mword_of_int 10 : mword 5)
                (mword_of_int 15 : mword 5) BGE false (mword_of_int 0x76)
                (ui_echo_16 pt M8 Hlay Ht8)
                ltac:(cbn [uv_btaken]; rewrite Ha5_3; rewrite Ha0_3;
                      rewrite (moi_ge_s 1 argc ltac:(unfold Z63; lia)
                                 ltac:(unfold Z63; lia));
                      exact (eq_sym Hge))
                Etgt76 ltac:(intro Hc; discriminate Hc)
                with "Hcg Hpc").
      iIntros (K12) "Hcg Hpc".
      assert (E16 : (if false then (mword_of_int 0x76 : mword 64)
                     else add_vec_int (mword_of_int 0x16 : mword 64) 4)
                    = mword_of_int 0x1a)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E16) in "Hpc".
      (* the whole index arithmetic, discharged by §1 *)
      assert (HP1 : 2 <= argc < 2 ^ 31)
        by (change (2 ^ 31) with 2147483648; lia).
      assert (HP3 : av + 8 * argc <= 2 ^ 38)
        by (change (2 ^ 38) with 274877906944; lia).
      destruct (echo_argv_chain argc av HP1 Hav0 HP3) as (Hch1 & Hch2 & Hch3).
      assert (Hs1val : add_vec (mword_of_int av : mword 64)
                         (sign_extend' 64 (mword_of_int 8 : mword 12))
                       = (mword_of_int (av + 8 * 1) : mword 64)).
      { assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                     = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
        rewrite E8. rewrite moi_add. f_equal; lia. }
      (* ---- 0x1a  addi s1,a1,8 ---- *)
      iApply (wp_uv_addi C pt Ysxv6 M8 m3 (mword_of_int 0x1a)
                (mword_of_int 8 : mword 12) (mword_of_int 11 : mword 5)
                (mword_of_int 9 : mword 5)
                (add_vec (mword_of_int av : mword 64)
                   (sign_extend' 64 (mword_of_int 8 : mword 12)))
                (ui_echo_1a pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_3; reflexivity)
                with "Hcg Hpc").
      iIntros (K13) "Hcg Hpc".
      set (m4 := <[Regidx (mword_of_int 9 : mword 5)
                   := regval_into_reg (add_vec (mword_of_int av : mword 64)
                        (sign_extend' 64 (mword_of_int 8 : mword 12)))]> m3).
      assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 4 = mword_of_int 0x1e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1a) in "Hpc".
      (* ---- 0x1e  c.addiw a0,a0,-2 ---- *)
      assert (Ha0_4 : m4 !!! Regidx (mword_of_int 10 : mword 5)
                      = (mword_of_int argc : mword 64)).
      { rewrite /m4. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Ha0_3. }
      iApply (wp_uv_caddiw C pt Ysxv6 M8 m4 (mword_of_int 0x1e)
                (mword_of_int 62 : mword 6) (mword_of_int 10 : mword 5)
                (sign_extend' 64
                   (subrange_vec_dec
                      (add_vec (mword_of_int argc : mword 64)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6))))
                      31 0))
                (ui_echo_1e pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_4; reflexivity)
                with "Hcg Hpc").
      iIntros (K14) "Hcg Hpc".
      set (m5 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (mword_of_int argc : mword 64)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 62 : mword 6))))
                           31 0))]> m4).
      assert (E1e : add_vec_int (mword_of_int 0x1e : mword 64) 2 = mword_of_int 0x20)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1e) in "Hpc".
      (* ---- 0x20  slli a5,a0,0x20 ---- *)
      assert (Ha0_5 : m5 !!! Regidx (mword_of_int 10 : mword 5)
                      = sign_extend' 64
                          (subrange_vec_dec
                             (add_vec (mword_of_int argc : mword 64)
                                (sign_extend' 64
                                   (sign_extend' 12 (mword_of_int 62 : mword 6))))
                             31 0))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uv_slli C pt Ysxv6 M8 m5 (mword_of_int 0x20)
                (mword_of_int 32 : mword 6) (mword_of_int 10 : mword 5)
                (mword_of_int 15 : mword 5)
                (shift_bits_left
                   (sign_extend' 64
                      (subrange_vec_dec
                         (add_vec (mword_of_int argc : mword 64)
                            (sign_extend' 64
                               (sign_extend' 12 (mword_of_int 62 : mword 6))))
                         31 0))
                   (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
                (ui_echo_20 pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_5; reflexivity)
                with "Hcg Hpc").
      iIntros (K15) "Hcg Hpc".
      set (m6 := <[Regidx (mword_of_int 15 : mword 5)
                   := regval_into_reg (shift_bits_left
                        (sign_extend' 64
                           (subrange_vec_dec
                              (add_vec (mword_of_int argc : mword 64)
                                 (sign_extend' 64
                                    (sign_extend' 12 (mword_of_int 62 : mword 6))))
                              31 0))
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0))]> m5).
      assert (E20 : add_vec_int (mword_of_int 0x20 : mword 64) 4 = mword_of_int 0x24)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E20) in "Hpc".
      (* ---- 0x24  srli a0,a5,0x1d -- a0 := 8*(argc-2) ---- *)
      assert (Ha5_6 : m6 !!! Regidx (mword_of_int 15 : mword 5)
                      = shift_bits_left
                          (sign_extend' 64
                             (subrange_vec_dec
                                (add_vec (mword_of_int argc : mword 64)
                                   (sign_extend' 64
                                      (sign_extend' 12 (mword_of_int 62 : mword 6))))
                                31 0))
                          (subrange_vec_dec (mword_of_int 32 : mword 6)
                             (Z.sub log2_xlen 1) 0))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uv_srli C pt Ysxv6 M8 m6 (mword_of_int 0x24)
                (mword_of_int 29 : mword 6) (mword_of_int 15 : mword 5)
                (mword_of_int 10 : mword 5)
                (mword_of_int (8 * (argc - 2)))
                (ui_echo_24 pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5_6; exact (eq_sym Hch1))
                with "Hcg Hpc").
      iIntros (K16) "Hcg Hpc".
      set (m7 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (mword_of_int (8 * (argc - 2)) : mword 64)]> m6).
      assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 4 = mword_of_int 0x28)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E24) in "Hpc".
      (* ---- 0x28  add s5,s1,a0 ---- *)
      assert (Hs1_7 : m7 !!! Regidx (mword_of_int 9 : mword 5)
                      = add_vec (mword_of_int av : mword 64)
                          (sign_extend' 64 (mword_of_int 8 : mword 12))).
      { rewrite /m7 /m6 /m5.
        apply upd_ne_tr; [ vm_compute; discriminate | ].
        apply upd_ne_tr; [ vm_compute; discriminate | ].
        apply upd_ne_tr; [ vm_compute; discriminate | ].
        apply upd_eq_tr; reflexivity. }
      assert (Ha0_7 : m7 !!! Regidx (mword_of_int 10 : mword 5)
                      = (mword_of_int (8 * (argc - 2)) : mword 64))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uv_add C pt Ysxv6 M8 m7 (mword_of_int 0x28)
                (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 21 : mword 5)
                (mword_of_int (av + 8 * (argc - 1)))
                (ui_echo_28 pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1_7; rewrite Ha0_7; rewrite <- Hch1;
                      exact (eq_sym Hch2))
                with "Hcg Hpc").
      iIntros (K17) "Hcg Hpc".
      set (m8 := <[Regidx (mword_of_int 21 : mword 5)
                   := regval_into_reg (mword_of_int (av + 8 * (argc - 1))
                                       : mword 64)]> m7).
      assert (E28 : add_vec_int (mword_of_int 0x28 : mword 64) 4 = mword_of_int 0x2c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E28) in "Hpc".
      (* ---- 0x2c  c.addi a1,a1,16 ---- *)
      assert (Ha1_8 : m8 !!! Regidx (mword_of_int 11 : mword 5)
                      = (mword_of_int av : mword 64)).
      { rewrite /m8 /m7 /m6 /m5 /m4.
        do 5 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        exact Ha1_3. }
      iApply (wp_uv_caddi C pt Ysxv6 M8 m8 (mword_of_int 0x2c)
                (mword_of_int 16 : mword 6) (mword_of_int 11 : mword 5)
                (add_vec (mword_of_int av : mword 64)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))
                (ui_echo_2c pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_8; reflexivity)
                with "Hcg Hpc").
      iIntros (K18) "Hcg Hpc".
      set (m9 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (add_vec (mword_of_int av : mword 64)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 16 : mword 6))))]> m8).
      assert (E2c : add_vec_int (mword_of_int 0x2c : mword 64) 2 = mword_of_int 0x2e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E2c) in "Hpc".
      (* ---- 0x2e  add s4,a1,a0 ---- *)
      assert (Ha1_9 : m9 !!! Regidx (mword_of_int 11 : mword 5)
                      = add_vec (mword_of_int av : mword 64)
                          (sign_extend' 64
                             (sign_extend' 12 (mword_of_int 16 : mword 6))))
        by (apply upd_eq_tr; reflexivity).
      assert (Ha0_9 : m9 !!! Regidx (mword_of_int 10 : mword 5)
                      = (mword_of_int (8 * (argc - 2)) : mword 64)).
      { rewrite /m9 /m8.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        exact Ha0_7. }
      iApply (wp_uv_add C pt Ysxv6 M8 m9 (mword_of_int 0x2e)
                (mword_of_int 11 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 20 : mword 5)
                (mword_of_int (av + 8 * argc))
                (ui_echo_2e pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_9; rewrite Ha0_9; rewrite <- Hch1;
                      exact (eq_sym Hch3))
                with "Hcg Hpc").
      iIntros (K19) "Hcg Hpc".
      set (m10 := <[Regidx (mword_of_int 20 : mword 5)
                    := regval_into_reg (mword_of_int (av + 8 * argc) : mword 64)]> m9).
      assert (E2e : add_vec_int (mword_of_int 0x2e : mword 64) 4 = mword_of_int 0x32)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E2e) in "Hpc".
      (* ---- 0x32  c.li s3,1 ---- *)
      iApply (wp_uv_cli C pt Ysxv6 M8 m10 (mword_of_int 0x32)
                (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
                (mword_of_int 1 : mword 64)
                (ui_echo_32 pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate) Hw1
                with "Hcg Hpc").
      iIntros (K20) "Hcg Hpc".
      set (m11 := <[Regidx (mword_of_int 19 : mword 5)
                    := regval_into_reg (mword_of_int 1 : mword 64)]> m10).
      assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 2 = mword_of_int 0x34)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E32) in "Hpc".
      (* ---- 0x34  auipc s6,0x1 ---- *)
      iApply (wp_uv_auipc C pt Ysxv6 M8 m11 (mword_of_int 0x34)
                (mword_of_int 1 : mword 20) (mword_of_int 22 : mword 5)
                (mword_of_int 4148 : mword 64)
                (ui_echo_34 pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K21) "Hcg Hpc".
      set (m12 := <[Regidx (mword_of_int 22 : mword 5)
                    := regval_into_reg (mword_of_int 4148 : mword 64)]> m11).
      assert (E34 : add_vec_int (mword_of_int 0x34 : mword 64) 4 = mword_of_int 0x38)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E34) in "Hpc".
      (* ---- 0x38  addi s6,s6,-1796 -- s6 := 0x930, the " " literal ---- *)
      assert (Hs6_12 : m12 !!! Regidx (mword_of_int 22 : mword 5)
                       = (mword_of_int 4148 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uv_addi C pt Ysxv6 M8 m12 (mword_of_int 0x38)
                (mword_of_int 2300 : mword 12) (mword_of_int 22 : mword 5)
                (mword_of_int 22 : mword 5) (mword_of_int 2352 : mword 64)
                (ui_echo_38 pt M8 Hlay Ht8)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs6_12; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K22) "Hcg Hpc".
      set (m13 := <[Regidx (mword_of_int 22 : mword 5)
                    := regval_into_reg (mword_of_int 2352 : mword 64)]> m12).
      assert (E38 : add_vec_int (mword_of_int 0x38 : mword 64) 4 = mword_of_int 0x3c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E38) in "Hpc".
      (* ---- 0x3c  c.j 0x4e -- enter the loop at i = 1 ---- *)
      iApply (wp_uv_cj C pt Ysxv6 M8 m13 (mword_of_int 0x3c)
                (mword_of_int 9 : mword 11) (mword_of_int 0x4e)
                (ui_echo_3c pt M8 Hlay Ht8)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (K23) "Hcg Hpc".
      (* ---- the loop, at i = 1 ---- *)
      iApply (echo_loop sp0 argc av (Z.to_nat (argc - 1)) K23 M8 m13 1
                Hlay Hi8 Hargs8 Hst8 ltac:(lia)
                ltac:(rewrite Z2Nat.id; lia)
                ltac:(rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5;
                      do 9 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; exact Hs1val)
                ltac:(rewrite /m13 /m12 /m11 /m10 /m9;
                      do 5 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; reflexivity)
                ltac:(rewrite /m13 /m12 /m11;
                      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; reflexivity)
                ltac:(rewrite /m13 /m12;
                      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; reflexivity)
                ltac:(apply upd_eq_tr; reflexivity)
                ltac:(rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2;
                      do 12 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      exact Hsp1)
                with "Hcg Hpc").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* start @0x7c -- the ELF entry, and THE top-level statement about the   *)
  (* echo process.  Prologue, then main; main diverges, so the jal exit at *)
  (* 0x88 is dead code with no [uinstr] fact.                              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_echo_start (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (argc av : Z) :
    wp_echo_start_body (CID := CIDp) C pt M m sp0 argc av.
  Proof.
    intros Hlay Himg Hsp Hst Hargc Hav Hargs.
    pose proof (echo_img_text M Himg) as Htext.
    pose proof (echo_img_data M Himg) as Hdata.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    destruct (uv_stack_split pt M sp0 96 16 80 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    pose proof (us_lo _ _ _ _ Hst) as Hlo96.
    pose proof (us_canon _ _ _ _ Hst) as Hcan96.
    assert (Hu16 : uint (mword_of_int (uint sp0 - 16) : mword 64) = uint sp0 - 16)
      by (apply uint_moi; unfold Z64;
          change (2 ^ 38) with 274877906944 in Hcan96; lia).
    assert (HkT : forall (kk : Z) (bb : bv 8),
              EchoInstrs.echo_bytes !! kk = Some bb -> kk < uint sp0 - 16)
      by (intros kk bb Hkb; pose proof (echo_bytes_key_lt kk bb Hkb); lia).
    assert (HkD : forall (kk : Z) (bb : bv 8),
              EchoData.echo_data !! kk = Some bb -> kk < uint sp0 - 16)
      by (intros kk bb Hkb; pose proof (echo_data_key_lt kk bb Hkb); lia).
    iIntros "Hcg Hpc".
    iEval (rewrite Hsstart) in "Hpc".
    (* ---- 0x7c  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 16) : mword 64)
                   = add_vec (m !!! Regidx (mword_of_int 2 : mword 5))
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hsp' : m !!! Regidx (mword_of_int 2 : mword 5)
                     = (mword_of_int (uint sp0) : mword 64))
        by (rewrite moi_of_uint; exact Hsp).
      rewrite Hc. rewrite Hsp'. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Ysxv6 M m (mword_of_int 0x7c)
              (mword_of_int 48 : mword 6) (mword_of_int 2 : mword 5)
              (mword_of_int (uint sp0 - 16))
              (ui_echo_7c pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (J1) "Hcg Hpc".
    set (n1 := <[Regidx (mword_of_int 2 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64)]> m).
    assert (Hsp1 : n1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 16) : mword 64))
      by exact (upd_eq m (Regidx (mword_of_int 2 : mword 5))
                  (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))).
    assert (E7c : add_vec_int (mword_of_int 0x7c : mword 64) 2 = mword_of_int 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7c) in "Hpc".
    (* ---- 0x7e  c.sdsp ra,8(sp) ---- *)
    iApply (echo_pro_store J1 M n1 sp0 (mword_of_int 0x7e)
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5) 16 8
              (ui_echo_7e pt M Hlay Htext) Hstf
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (J2) "Hcg Hpc".
    set (N1 := uM_store8 M (uint sp0 - 16 + 8)
                 (n1 !!! Regidx (mword_of_int 1 : mword 5))).
    assert (Ho1 : uM_only M N1 (uint sp0 - 16) 16).
    { rewrite /N1. apply uM_only_store8; lia. }
    assert (Ht1 : echo_text_sub N1)
      by exact (uM_only_img EchoInstrs.echo_bytes M N1 (uint sp0 - 16) 16
                  HkT Ho1 Htext).
    assert (Hs1 : uv_stack pt N1 sp0 16)
      by exact (uM_only_stack pt M N1 sp0 16 (uint sp0 - 16) 16 Ho1 Hstf).
    assert (E7e : add_vec_int (mword_of_int 0x7e : mword 64) 2 = mword_of_int 0x80)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7e) in "Hpc".
    (* ---- 0x80  c.sdsp s0,0(sp) ---- *)
    iApply (echo_pro_store J2 N1 n1 sp0 (mword_of_int 0x80)
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5) 16 0
              (ui_echo_80 pt N1 Hlay Ht1) Hs1
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (J3) "Hcg Hpc".
    set (N2 := uM_store8 N1 (uint sp0 - 16 + 0)
                 (n1 !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Ho2 : uM_only M N2 (uint sp0 - 16) 16).
    { apply (uM_only_trans M N1 N2 (uint sp0 - 16) 16 Ho1).
      rewrite /N2. apply uM_only_store8; lia. }
    assert (Ht2 : echo_text_sub N2)
      by exact (uM_only_img EchoInstrs.echo_bytes M N2 (uint sp0 - 16) 16
                  HkT Ho2 Htext).
    assert (Hd2 : echo_data_sub N2)
      by exact (uM_only_img EchoData.echo_data M N2 (uint sp0 - 16) 16
                  HkD Ho2 Hdata).
    assert (Hi2 : echo_img_sub N2) by exact (conj Ht2 Hd2).
    assert (E80 : add_vec_int (mword_of_int 0x80 : mword 64) 2 = mword_of_int 0x82)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E80) in "Hpc".
    (* ---- 0x82  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (n1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. rewrite Hsp1. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Ysxv6 N2 n1 (mword_of_int 0x82)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (mword_of_int (uint sp0))
              (ui_echo_82 pt N2 Hlay Ht2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hcg Hpc").
    iIntros (J4) "Hcg Hpc".
    set (n2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> n1).
    assert (E82 : add_vec_int (mword_of_int 0x82 : mword 64) 2 = mword_of_int 0x84)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E82) in "Hpc".
    (* ---- 0x84  jal ra,0x0 <main> ---- *)
    assert (Htj : (mword_of_int EchoSyms.main : mword 64)
                  = add_vec (mword_of_int 0x84)
                      (sign_extend' 64 (mword_of_int 2097020 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x88 : mword 64)
                  = add_vec_int (mword_of_int 0x84 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Ysxv6 N2 n2 (mword_of_int 0x84)
              (mword_of_int 2097020 : mword 21) ra_idx
              (mword_of_int EchoSyms.main) (mword_of_int 0x88)
              (ui_echo_84 pt N2 Hlay Ht2)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (J5) "Hcg Hpc".
    set (n3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x88 : mword 64)]> n2).
    (* ---- the call: main() -- diverges ---- *)
    (* ORDER MATTERS: carry [uargs] across the prologue at the OLD bound
       (where [uM_only_uargs]'s [a + n <= lo] holds exactly), and only then
       lower the bound to main's entry sp. *)
    assert (Hargs2 : uargs pt N2 av argc (uint sp0))
      by exact (uM_only_uargs pt M N2 av argc (uint sp0) (uint sp0 - 16) 16
                  Ho2 ltac:(lia) Hargs).
    assert (Hargs3 : uargs pt N2 av argc
                       (uint (mword_of_int (uint sp0 - 16) : mword 64))).
    { rewrite Hu16.
      exact (uargs_lo_le pt N2 av argc (uint sp0) (uint sp0 - 16)
               ltac:(lia) Hargs2). }
    assert (Hstm' : uv_stack pt M (mword_of_int (uint sp0 - 16) : mword 64) 80)
      by (rewrite <- (uv_stack_sp_moi pt M sp0 16 Hstf); exact Hstm).
    assert (Hst3 : uv_stack pt N2 (mword_of_int (uint sp0 - 16) : mword 64) 80)
      by exact (uM_only_stack pt M N2 (mword_of_int (uint sp0 - 16)) 80
                  (uint sp0 - 16) 16 Ho2 Hstm').
    assert (Hsp3 : n3 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 16) : mword 64)).
    { rewrite /n3 /n2.
      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hsp1. }
    assert (Hargc3 : n3 !!! Regidx a0_idx = (mword_of_int argc : mword 64)).
    { rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hargc. }
    assert (Hav3 : n3 !!! Regidx a1_idx = (mword_of_int av : mword 64)).
    { rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hav. }
    iApply (wp_echo_main J5 N2 n3 (mword_of_int (uint sp0 - 16)) argc av
              Hlay Hi2 Hsp3 Hst3 Hargc3 Hav3 Hargs3 with "Hcg Hpc").
  Qed.

End UProofEcho.

(* sentinel: the whole echo verification rests on nothing but the platform
   axioms and functional extensionality *)
Print Assumptions wp_echo_start.
