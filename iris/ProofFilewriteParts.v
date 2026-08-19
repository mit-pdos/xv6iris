(* ProofFilewriteParts.v -- the pure arithmetic and the SHARED CODE BLOCKS of
   filewrite, proved once so [ProofFilewrite.v] is only the function's own
   control flow and its ghost steps.

   filewrite's frame is 12 slots ([c.addi16sp sp,sp,-96] at +0x08):

     slot  1 = 88(sp)  saved ra      slot  7 = 40(sp)  saved s5
     slot  2 = 80(sp)  saved s0      slot  8 = 32(sp)  saved s6
     slot  3 = 72(sp)  saved s1      slot  9 = 24(sp)  saved s7
     slot  4 = 64(sp)  saved s2      slot 10 = 16(sp)  saved s8
     slot  5 = 56(sp)  saved s3      slot 11 =  8(sp)  saved s9
     slot  6 = 48(sp)  saved s4      slot 12 =  0(sp)  unused

   THE THREE STRUCTURAL FACTS ABOUT THIS FRAME, all of them consequences of
   gcc's shrink-wrapping and all of them visible in the spill addresses:

   1. ra/s0/s2/s5/s6 are spilled in the PROLOGUE (+0x0a..+0x12).  They are
      the only registers every arm clobbers -- s2 = f, s6 = addr, s5 = n --
      and the shared epilogue at +0xfc restores exactly those five.
   2. s4 is spilled at +0x30, INSIDE the FD_INODE arm and BEFORE the
      hoisted [n <= 0] test at +0x32; it is the running [i], and it is
      restored on its own at +0xfa / +0x130.
   3. s1/s3/s7/s8/s9 are spilled at +0x36..+0x3e, AFTER that test, so the
      zero-trip path at +0xe6 neither writes nor restores them.  They are
      restored in one five-instruction block that gcc emitted TWICE
      (+0xda, the normal loop exit, and +0xea, the short-write break).

   So the epilogue takes slots 3, 5, 6 and 9..12 as ARBITRARY words and
   gets its [callee_saved] for s1/s3/s4/s7/s8/s9 from a PREMISE about the
   incoming map -- fileread's shape, one register wider.

   The blocks:

   * [fw_epi] -- the epilogue at +0xfc..+0x108 (restore ra/s0/s2/s5/s6,
     trade the 96-byte frame back, [c.jr ra]).  SIX exits reach it, at that
     one LITERAL pc, so it needs no pc parameters.  It does NOT set a0: the
     six exits each leave the return value there themselves (the callee's
     own a0 on the pipe and device arms, [c.mv a0,s5] at +0xf8 on the
     inode arm's success path, [c.li a0,-1] at +0x126/+0x12a/+0x12e).
   * [fw_rest5] -- the five [c.ldsp]s of fact 3, over the block's six pcs as
     LITERAL parameters (durable-notes' recipe: an [instr] fact whose
     address has to be CONVERTED makes every [iApply] reduce a [Z_to_bv]
     over a kernel address).
   * [fw_m1j] -- [c.li a0,-1; c.j +0xfc], the FD_DEVICE arm's two error
     exits (+0x126 the out-of-range major, +0x12a the null devsw slot).

   The read side's own Parts file is imported rather than copied: the
   dispatch's [c.li] immediates, the [short] zero-extension the major goes
   through, the [devsw] index shift and the [c.addw] store value are
   character-for-character fileread's, and [SpecFilewrite] already depends
   on [SpecFileread].

   Both blocks are hart-generic ([CID0] a binder): every exit runs after a
   call that may have parked and resumed the thread on another hart. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
(* [WpLock] for [lockG] itself: [Import] is not transitive, so without it the
   [!lockG Σ] binder below auto-generalizes instead of resolving. *)
Require Import WpLock SleepLock.
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import KernelDataInv.
Require Import PrintkArgs.
Require Import WpUart.
Require Import DiskPtsto.
Require Import WpLock.
Require Import SpecPanic.
Require Import CpuOwn.
Require Import LockRank.
Require Import IcacheRef.
Require Import CodeFilewrite.
Require Import ProofFilereadParts.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Set Printing Depth 40.

Notation FW := KernelSyms.filewrite (only parsing).

(* ===================================================================== *)
(*  THE PANIC MESSAGE.  filewrite's one live arm is [panic("filewrite")]  *)
(*  at +0x11e -- the ELSE of the type dispatch; the literal sits at       *)
(*  0x800075a8 in .rodata, nine characters and a NUL.  Hoisted as NAMED   *)
(*  pure lemmas rather than inline [ltac:] -- see optimization.md, and    *)
(*  the panic recipe's third trap ([lia]/[lkbelow] against an evar).      *)
(* ===================================================================== *)
Definition fw_msg_a : Z := 0x800075a8.
Definition fw_msg : string := "filewrite".

Lemma fw_panic_noff : (Z.of_nat 0 + 2 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* "log" (rank 1) is below "pr" (16).  A CLOSED lemma over the plain gset,
   not an inline [ltac:(lkbelow)]. *)
Lemma fw_panic_below (lks : gset string) :
  locks_below lks "log" -> locks_below lks "pr".
Proof. intros H. apply (locks_below_mono lks "log" "pr" H). vm_compute; lia. Qed.

Lemma fw_msg_nz : eq_vec (mword_of_int fw_msg_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma fw_msg_nonul : PrintkFmt.nonul fw_msg = true.
Proof. vm_compute; reflexivity. Qed.

Lemma fw_msg_bytes :
  forall j b, cstring_bytes fw_msg !! j = Some b ->
    KernelData.kernel_data !! (fw_msg_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 10 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Section FilewriteMsg.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma fw_msg_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int fw_msg_a : mword 64) ↦ₛ□ fw_msg.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string fw_msg_a fw_msg _ eq_refl
              ltac:(unfold text_end, fw_msg_a; lia)
              ltac:(vm_compute; discriminate) fw_msg_bytes with "Hd").
  Qed.
End FilewriteMsg.

(* ---------------------------------------------------------------------- *)
(*  THE 96-BYTE FRAME                                                      *)
(* ---------------------------------------------------------------------- *)

(* -96 / +96, both [c.addi16sp] (58 is -6 in a 6-bit field, scaled by 16). *)
Lemma fw_push_96 (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
  = pa_stk X 12.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fw_pop_96 (X : mword 64) :
  add_vec (pa_stk X 12) (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,96] at +0x14 -- the frame pointer, back at the entry sp *)
Lemma fw_fp_96 (X : mword 64) :
  add_vec (pa_stk X 12) (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* the eleven save-slot addresses, as the [c.sdsp]/[c.ldsp] displacements
   compute them off the PUSHED sp.  Named by SLOT, not by displacement. *)
Local Ltac fwfrm :=
  unfold pa_stk, add_vec_int; rewrite add_vec_off2;
  apply f_equal; apply bv_eq; vm_compute; reflexivity.

Lemma fw_frm1 (X : mword 64) :          (* 88(sp) : saved ra *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. fwfrm. Qed.

Lemma fw_frm2 (X : mword 64) :          (* 80(sp) : saved s0 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. fwfrm. Qed.

Lemma fw_frm3 (X : mword 64) :          (* 72(sp) : saved s1 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. fwfrm. Qed.

Lemma fw_frm4 (X : mword 64) :          (* 64(sp) : saved s2 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. fwfrm. Qed.

Lemma fw_frm5 (X : mword 64) :          (* 56(sp) : saved s3 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. fwfrm. Qed.

Lemma fw_frm6 (X : mword 64) :          (* 48(sp) : saved s4 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof. fwfrm. Qed.

Lemma fw_frm7 (X : mword 64) :          (* 40(sp) : saved s5 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 7.
Proof. fwfrm. Qed.

Lemma fw_frm8 (X : mword 64) :          (* 32(sp) : saved s6 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 8.
Proof. fwfrm. Qed.

Lemma fw_frm9 (X : mword 64) :          (* 24(sp) : saved s7 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 9.
Proof. fwfrm. Qed.

Lemma fw_frm10 (X : mword 64) :         (* 16(sp) : saved s8 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 10.
Proof. fwfrm. Qed.

Lemma fw_frm11 (X : mword 64) :         (*  8(sp) : saved s9 *)
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
  = pa_stk X 11.
Proof. fwfrm. Qed.

Lemma fw_frame_back (K : nat) : (12 <= K)%nat -> ((K - 12) + 12)%nat = K.
Proof. lia. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE CHUNK SIZE, as the two lui/addi pairs materialise it               *)
(* ---------------------------------------------------------------------- *)

(* [c.lui s7,0x1] / [lui a5,0x1] : 4096 *)
Lemma fw_lui1 :
  luival (sign_extend' 20 (mword_of_int 1 : mword 6)) = (mword_of_int 4096 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi s7,s7,-1024] : the 12-bit field holds 3072, i.e. -1024 signed *)
Lemma fw_addi_m1024 :
  add_vec (mword_of_int 4096 : mword 64)
          (sign_extend' 64 (mword_of_int 3072 : mword 12))
  = (mword_of_int 3072 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addiw a5,a5,-1024] : the same value, through the word-sized path *)
Lemma fw_addiw_m1024 :
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int 4096 : mword 64)
              (sign_extend' 64 (mword_of_int 3072 : mword 12))) 31 0)
  = (mword_of_int 3072 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.li s8,1] at +0x50 : writei's [user_src] argument, hoisted out of the
   loop by gcc.  (fileread's [fr_li1] is the same word, at [Ra0].) *)
Lemma fw_li0 :
  add_vec (zero_reg : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE LOOP'S 32-BIT ARITHMETIC                                           *)
(* ---------------------------------------------------------------------- *)

(* the two 32-bit binops the loop performs, on LITERALS.  Stated over plain
   [Z] and kept [mword]-free in their hypotheses: [lia] answers "Cannot find
   witness" with an [mword] merely in context, and the call sites are inside
   a whole-function proof whose context is full of them. *)
Lemma fw_addv32_moi2 (x y : Z) :
  add_vec (mword_of_int x : mword 32) (mword_of_int y : mword 32)
  = (mword_of_int (x + y) : mword 32).
Proof.
  apply bv_eq.
  rewrite (add_vec_unsigned (mword_of_int x : mword 32) (mword_of_int y : mword 32)).
  rewrite !moi32_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  unfold bv_wrap. by rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r.
Qed.

Lemma fw_subv32_moi (x y : Z) :
  sub_vec (mword_of_int x : mword 32) (mword_of_int y : mword 32)
  = (mword_of_int (x - y) : mword 32).
Proof.
  apply bv_eq. rewrite sub_vec32_unsigned !moi32_unsigned.
  unfold bv_wrap. by rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r.
Qed.

(* [addiw s3,s3,0] at +0x82 : gcc's [sext.w].  On a value that is already a
   sign-extended small non-negative literal it is the identity.  NOT
   [RiscvExtras.sextw_moi]: that one is stated at the [mword_of_int 0 :
   mword 12] spelling of a zero displacement, and this [addiw] decodes its
   immediate as [sign_extend' 12 (mword_of_int 0 : mword 6)]. *)
Lemma fw_sextw_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int z : mword 64)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)
  = (mword_of_int z : mword 64).
Proof.
  intro Hz.
  assert (Hid : add_vec (mword_of_int z : mword 64)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
                = (mword_of_int z : mword 64)).
  { rewrite (_ : (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)) : mword 64)
                 = (mword_of_int 0 : mword 64));
      [| apply bv_eq; vm_compute; reflexivity].
    rewrite fr_addv64_moi. f_equal. lia. }
  rewrite Hid. rewrite <- trunc32_subrange. rewrite trunc32_mword_of_int.
  apply fr_sext_moi32. exact Hz.
Qed.

(* [subw a5,s5,s4] at +0xcc : n - i, both small non-negative *)
Lemma fw_subw_moi (a c : Z) :
  (0 <= c <= a)%Z -> (a < 2 ^ 31)%Z ->
  sign_extend' 64 (sub_vec (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int c : mword 64) 31 0 : mword 32))
  = (mword_of_int (a - c) : mword 64).
Proof.
  intros Hc Ha.
  rewrite <- !trunc32_subrange. rewrite !trunc32_mword_of_int.
  rewrite fw_subv32_moi. apply fr_sext_moi32. lia.
Qed.

(* [addw s4,s4,s1] at +0xc4 : i + r, both small non-negative *)
Lemma fw_addw_moi (a c : Z) :
  (0 <= a)%Z -> (0 <= c)%Z -> (a + c < 2 ^ 31)%Z ->
  sign_extend' 64 (add_vec (subrange_vec_dec (mword_of_int c : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32))
  = (mword_of_int (c + a) : mword 64).
Proof.
  intros Ha Hc Hac.
  rewrite <- !trunc32_subrange. rewrite !trunc32_mword_of_int.
  rewrite fw_addv32_moi2. apply fr_sext_moi32. lia.
Qed.

(* the signed compares the loop's three tests reduce to.  All four operands
   are small non-negative literals, so [sint] is the literal. *)
Lemma fw_bge_moi (a c : Z) : (0 <= a < 2 ^ 31)%Z -> (0 <= c < 2 ^ 31)%Z ->
  zopz0zKzJ_s (mword_of_int a : mword 64) (mword_of_int c : mword 64)
  = Z.geb a c.
Proof.
  intros Ha Hc. unfold zopz0zKzJ_s.
  rewrite (fr_sint64_moi a ltac:(change (2^63)%Z with 9223372036854775808%Z;
                                 change (2^31)%Z with 2147483648%Z in Ha; lia)).
  rewrite (fr_sint64_moi c ltac:(change (2^63)%Z with 9223372036854775808%Z;
                                 change (2^31)%Z with 2147483648%Z in Hc; lia)).
  reflexivity.
Qed.

Lemma fw_bge0_moi (c : Z) : (0 <= c < 2 ^ 31)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int c : mword 64) = Z.geb 0 c.
Proof.
  intro Hc.
  assert (Hz : (zero_reg : mword 64) = (mword_of_int 0 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hz. apply fw_bge_moi; [lia | exact Hc].
Qed.

(* [bne s3,s1] at +0xc0 and [bne s5,s4] at +0xf4, on small literals *)
Lemma fw_neq_moi (a c : Z) : (0 <= a < 2 ^ 31)%Z -> (0 <= c < 2 ^ 31)%Z ->
  neq_vec (mword_of_int a : mword 64) (mword_of_int c : mword 64)
  = negb (Z.eqb a c).
Proof.
  intros Ha Hc. unfold neq_vec.
  change (2^31)%Z with 2147483648%Z in Ha, Hc.
  destruct (Z.eqb a c) eqn:Hab; cbn [negb].
  - apply Z.eqb_eq in Hab. subst c.
    rewrite (_ : eq_vec (mword_of_int a : mword 64) (mword_of_int a : mword 64) = true);
      [reflexivity | by apply eq_vec_true_iff].
  - apply Z.eqb_neq in Hab.
    rewrite (_ : eq_vec (mword_of_int a : mword 64) (mword_of_int c : mword 64) = false);
      [reflexivity |].
    apply eq_vec_false_iff. intro Hce.
    apply (f_equal (@bv_unsigned 64)) in Hce.
    rewrite !moi64_unsigned in Hce.
    rewrite (bvw64_small a ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)) in Hce.
    rewrite (bvw64_small c ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)) in Hce.
    exact (Hab Hce).
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE GENERATION-NAMED SHARE SPLITS                                      *)
(*                                                                         *)
(*  filewrite is the first caller that has to KEEP a generation across an   *)
(*  ilock/iunlock pair.  SpecIunlock hands the share back in the            *)
(*  ARITY-PRESERVING form ([inode_shr], i.e. ∃ g), and the loop needs the   *)
(*  SAME [g] on the next iteration -- both to feed SpecIlock and to join    *)
(*  [ity_shot]s with [ity_shot_agree].  The generation cannot in fact have  *)
(*  moved (§17.6: a bump needs the slot's WHOLE liveness unit, which this   *)
(*  caller's share denies), but the contract does not say so, so the        *)
(*  caller PROVES it: it lends ilock only HALF its share and keeps the      *)
(*  other half, whose [live_gen] pins the returned half's generation by     *)
(*  [live_gen_agree].  Two lemmas, and nothing else changes.                *)
(* ---------------------------------------------------------------------- *)
Section FwShare.
  Context `{!riscvGS Σ, ICFG : icfg, !icacheG Σ, !lockG Σ}.

  Lemma fw_shr_gen_split (k : nat) (s1 s2 : Qp) (dev inum : mword 32) (g : gname) :
    inode_shr_gen k (s1 + s2)%Qp dev inum g ⊣⊢
    inode_shr_gen k s1 dev inum g ∗ inode_shr_gen k s2 dev inum g.
  Proof.
    rewrite /inode_shr_gen inode_ident_split live_gen_split slh_tok_split.
    iSplit; [iIntros "[[$ $] [[$ $] [$ $]]]" | iIntros "[($ & $ & $) ($ & $ & $)]"].
  Qed.

  Lemma fw_shr_gen_halve (k : nat) (s : Qp) (dev inum : mword 32) (g : gname) :
    inode_shr_gen k s dev inum g ⊣⊢
    inode_shr_gen k (s/2)%Qp dev inum g ∗ inode_shr_gen k (s/2)%Qp dev inum g.
  Proof.
    pose proof (fw_shr_gen_split k (s/2)%Qp (s/2)%Qp dev inum g) as Hs.
    by rewrite {1}(Qp.div_2 s) in Hs.
  Qed.

  (* THE PIN.  A retained generation-named half and the half iunlock gave
     back name ONE generation, so the returned share can be re-labelled at
     the caller's own [g] and the two rejoined. *)
  Lemma fw_shr_regen (k : nat) (s1 s2 : Qp) (dev inum : mword 32) (g : gname) :
    inode_shr_gen k s1 dev inum g -∗ inode_shr k s2 dev inum -∗
    inode_shr_gen k (s1 + s2)%Qp dev inum g.
  Proof.
    iIntros "Hkeep Hback".
    iEval (rewrite inode_shr_gen_intro) in "Hback".
    iDestruct "Hback" as (g') "Hback".
    iDestruct "Hkeep" as "(Hid1 & Hlv1 & Hs1)".
    iDestruct "Hback" as "(Hid2 & Hlv2 & Hs2)".
    iDestruct (live_gen_agree with "Hlv1 Hlv2") as %<-.
    rewrite /inode_shr_gen inode_ident_split live_gen_split slh_tok_split. iFrame.
  Qed.

End FwShare.

Section ProofFilewriteParts.
  Context `{!riscvGS Σ, !sieG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).

  Local Ltac regne := reg_ne_side.


  (* =================================================================== *)
  (*  +0x08 .. +0x14 -- THE PROLOGUE.                                     *)
  (*                                                                      *)
  (*  Reached only from the FALL of the [f->writable] test at +0x04: the   *)
  (*  early return at +0x122 runs with sp UNTOUCHED (S3a's decode note 1), *)
  (*  which is why this block starts at +0x08 rather than at the symbol.   *)
  (*  It pushes twelve slots, spills the five registers every arm          *)
  (*  clobbers, and sets the frame pointer back at the entry sp.  The      *)
  (*  seven slots it does NOT write come out at arbitrary words -- three   *)
  (*  of the six exits never spill them (Parts' header, fact 3).           *)
  (* =================================================================== *)
  Lemma fw_pro `{GEN : GenId} `{CID0 : CpuId}
      (m : regfile) (K : nat) (sp0 : mword 64) (p : mword 64) (b : bool) :
    (12 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    sie_cap_gpr KT1 m K b p -∗
    kernel_text -∗
    pc_is (mword_of_int (FW + 0x08) : mword 64) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (Mr : regfile) (w3 w5 w6 w9 w10 w11 w12 : mword 64),
        ⌜ Mr !!! Regidx csp_rs1 = pa_stk sp0 12
          /\ Mr !!! Regidx Rs0 = sp0
          /\ (forall r : mword 5, r <> csp_rs1 -> r <> Rs0 ->
                Mr !!! Regidx r = m !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 Mr (K - 12)%nat b p -∗
        pc_is (mword_of_int (FW + 0x16) : mword 64) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) (m !!! Regidx Rra) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) (m !!! Regidx Rs0) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) w3 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) (m !!! Regidx Rs2) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) (m !!! Regidx Rs5) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) (m !!! Regidx Rs6) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0.
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (fwri_008 with "Htext") as "Hi08".
    iPoseProof (fwri_00a with "Htext") as "Hi0a".
    iPoseProof (fwri_00c with "Htext") as "Hi0c".
    iPoseProof (fwri_00e with "Htext") as "Hi0e".
    iPoseProof (fwri_010 with "Htext") as "Hi10".
    iPoseProof (fwri_012 with "Htext") as "Hi12".
    iPoseProof (fwri_014 with "Htext") as "Hi14".
    (* ---- +0x08 c.addi16sp sp,sp,-96 ---- *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (FW + 0x08))
              (mword_of_int 58 : mword 6) m K 12 b HK
              (fw_push_96 (m !!! Regidx csp_rs1)) with "Hcg Hpc Hi08").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    iEval (rewrite Hsp0) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /R1 upd_eq. rewrite <- Hsp0. apply fw_push_96. }
    assert (HR1thr : forall r : mword 5, r <> csp_rs1 ->
                       R1 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp. rewrite /R1 upd_ne; [reflexivity | regne]. }
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 &
                            S11 & S12 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
    iDestruct "S11" as (u11) "Hb11". iDestruct "S12" as (u12) "Hb12".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply fw_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply fw_frm2).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR1sp; apply fw_frm4).
    assert (Hf7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HR1sp; apply fw_frm7).
    assert (Hf8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HR1sp; apply fw_frm8).
    (* ---- +0x0a c.sdsp ra,88(sp) ---- *)
    iEval (rewrite -Hf1) in "Hb1".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x0a)) (mword_of_int 11 : mword 6) Rra
              R1 (K - 12)%nat u1 b with "Hcg Hpc Hi0a Hb1").
    iIntros (CID2 Hq2) "Hcg Hpc Hb1". iEval (rgne) in "Hb1".
    iEval (rewrite Hf1) in "Hb1".
    iEval (rewrite (HR1thr Rra ltac:(vm_compute; discriminate))) in "Hb1".
    assert (Hpp0c : add_vec_int (mword_of_int (FW + 0x0a) : mword 64) 2
                    = mword_of_int (FW + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ---- +0x0c c.sdsp s0,80(sp) ---- *)
    iEval (rewrite -Hf2) in "Hb2".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x0c)) (mword_of_int 10 : mword 6) Rs0
              R1 (K - 12)%nat u2 b with "Hcg Hpc Hi0c Hb2").
    iIntros (CID3 Hq3) "Hcg Hpc Hb2". iEval (rgne) in "Hb2".
    iEval (rewrite Hf2) in "Hb2".
    iEval (rewrite (HR1thr Rs0 ltac:(vm_compute; discriminate))) in "Hb2".
    assert (Hpp0e : add_vec_int (mword_of_int (FW + 0x0c) : mword 64) 2
                    = mword_of_int (FW + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- +0x0e c.sdsp s2,64(sp) ---- *)
    iEval (rewrite -Hf4) in "Hb4".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x0e)) (mword_of_int 8 : mword 6) Rs2
              R1 (K - 12)%nat u4 b with "Hcg Hpc Hi0e Hb4").
    iIntros (CID4 Hq4) "Hcg Hpc Hb4". iEval (rgne) in "Hb4".
    iEval (rewrite Hf4) in "Hb4".
    iEval (rewrite (HR1thr Rs2 ltac:(vm_compute; discriminate))) in "Hb4".
    assert (Hpp10 : add_vec_int (mword_of_int (FW + 0x0e) : mword 64) 2
                    = mword_of_int (FW + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- +0x10 c.sdsp s5,40(sp) ---- *)
    iEval (rewrite -Hf7) in "Hb7".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x10)) (mword_of_int 5 : mword 6) Rs5
              R1 (K - 12)%nat u7 b with "Hcg Hpc Hi10 Hb7").
    iIntros (CID5 Hq5) "Hcg Hpc Hb7". iEval (rgne) in "Hb7".
    iEval (rewrite Hf7) in "Hb7".
    iEval (rewrite (HR1thr Rs5 ltac:(vm_compute; discriminate))) in "Hb7".
    assert (Hpp12 : add_vec_int (mword_of_int (FW + 0x10) : mword 64) 2
                    = mword_of_int (FW + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- +0x12 c.sdsp s6,32(sp) ---- *)
    iEval (rewrite -Hf8) in "Hb8".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x12)) (mword_of_int 4 : mword 6) Rs6
              R1 (K - 12)%nat u8 b with "Hcg Hpc Hi12 Hb8").
    iIntros (CID6 Hq6) "Hcg Hpc Hb8". iEval (rgne) in "Hb8".
    iEval (rewrite Hf8) in "Hb8".
    iEval (rewrite (HR1thr Rs6 ltac:(vm_compute; discriminate))) in "Hb8".
    assert (Hpp14 : add_vec_int (mword_of_int (FW + 0x12) : mword 64) 2
                    = mword_of_int (FW + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ---- +0x14 c.addi4spn s0,sp,96 : the frame pointer ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (FW + 0x14)) (Cregidx (mword_of_int 0))
              (mword_of_int 24 : mword 8) Rs0 R1 (K - 12)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    assert (Hpp16 : add_vec_int (mword_of_int (FW + 0x14) : mword 64) 2
                    = mword_of_int (FW + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    iSpecialize ("Hcont" $! CID7 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! R2 u3 u5 u6 u9 u10 u11 u12 with
              "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12").
    split.
    { rewrite /R2 upd_ne; [exact HR1sp | vm_compute; discriminate]. }
    split.
    { rewrite /R2 upd_eq. unfold regval_into_reg. rewrite HR1sp. apply fw_fp_96. }
    intros r Nsp Ns0.
    rewrite /R2 upd_ne; [| regne].
    exact (HR1thr r Nsp).
  Qed.

  (* =================================================================== *)
  (*  +0xfc .. +0x108 -- THE EPILOGUE.  All six returning exits reach it.  *)
  (* =================================================================== *)
  Lemma fw_epi `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s20 s50 s60 : mword 64) (rv : mword 64)
      (w3 w5 w6 w9 w10 w11 w12 : mword 64)
      (p : mword 64) (b : bool) :
    (12 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs5 = s50 ->
    m !!! Regidx Rs6 = s60 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 12 ->
    Mt !!! Regidx Ra0 = rv ->
    (* everything but sp/s0/s2/s5/s6 already agrees with the entry map.
       s1, s3, s4, s7, s8 and s9 are in here, and that is the whole point:
       three of the six exits never spilled them. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs2 -> r <> Rs5 -> r <> Rs6 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 12)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (FW + 0xfc) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) s50 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) s60 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs20 Hs50 Hs60 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12 Hcont".
    iPoseProof (fwri_0fc with "Htext") as "Hifc".
    iPoseProof (fwri_0fe with "Htext") as "Hife".
    iPoseProof (fwri_100 with "Htext") as "Hi100".
    iPoseProof (fwri_102 with "Htext") as "Hi102".
    iPoseProof (fwri_104 with "Htext") as "Hi104".
    iPoseProof (fwri_106 with "Htext") as "Hi106".
    iPoseProof (fwri_108 with "Htext") as "Hi108".
    (* ---- +0xfc: c.ldsp ra,88(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                   = pa_stk sp0 1) by (rewrite Hmtsp; apply fw_frm1).
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (FW + 0xfc)) (mword_of_int 11 : mword 6) Rra
              Mt (K - 12)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hifc Hb1").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /T1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hppfe : add_vec_int (mword_of_int (FW + 0xfc) : mword 64) 2
                    = mword_of_int (FW + 0xfe)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppfe) in "Hpc".
    (* ---- +0xfe: c.ldsp s0,80(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                   = pa_stk sp0 2) by (rewrite HT1sp; apply fw_frm2).
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (FW + 0xfe)) (mword_of_int 10 : mword 6) Rs0
              T1 (K - 12)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hife Hb2").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (Hpp100 : add_vec_int (mword_of_int (FW + 0xfe) : mword 64) 2
                     = mword_of_int (FW + 0x100)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp100) in "Hpc".
    (* ---- +0x100: c.ldsp s2,64(sp) ---- *)
    assert (Hpa4 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                   = pa_stk sp0 4) by (rewrite HT2sp; apply fw_frm4).
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (FW + 0x100)) (mword_of_int 8 : mword 6) Rs2
              T2 (K - 12)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi100 Hb4").
    iIntros (CID3 Hs3) "Hcg Hpc Hb4". iEval (rewrite Hpa4) in "Hb4".
    set (T3 := <[Regidx Rs2 := regval_into_reg s20]> T2).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (Hpp102 : add_vec_int (mword_of_int (FW + 0x100) : mword 64) 2
                     = mword_of_int (FW + 0x102)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp102) in "Hpc".
    (* ---- +0x102: c.ldsp s5,40(sp) ---- *)
    assert (Hpa7 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                   = pa_stk sp0 7) by (rewrite HT3sp; apply fw_frm7).
    iEval (rewrite -Hpa7) in "Hb7".
    iApply (wp_cldsp_s_sconf (mword_of_int (FW + 0x102)) (mword_of_int 5 : mword 6) Rs5
              T3 (K - 12)%nat s50 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi102 Hb7").
    iIntros (CID4 Hs4) "Hcg Hpc Hb7". iEval (rewrite Hpa7) in "Hb7".
    set (T4 := <[Regidx Rs5 := regval_into_reg s50]> T3).
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    assert (Hpp104 : add_vec_int (mword_of_int (FW + 0x102) : mword 64) 2
                     = mword_of_int (FW + 0x104)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp104) in "Hpc".
    (* ---- +0x104: c.ldsp s6,32(sp) ---- *)
    assert (Hpa8 : add_vec (T4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                   = pa_stk sp0 8) by (rewrite HT4sp; apply fw_frm8).
    iEval (rewrite -Hpa8) in "Hb8".
    iApply (wp_cldsp_s_sconf (mword_of_int (FW + 0x104)) (mword_of_int 4 : mword 6) Rs6
              T4 (K - 12)%nat s60 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi104 Hb8").
    iIntros (CID5 Hs5) "Hcg Hpc Hb8". iEval (rewrite Hpa8) in "Hb8".
    set (T5 := <[Regidx Rs6 := regval_into_reg s60]> T4).
    assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /T5 upd_ne; [exact HT4sp | vm_compute; discriminate]).
    assert (Hpp106 : add_vec_int (mword_of_int (FW + 0x104) : mword 64) 2
                     = mword_of_int (FW + 0x106)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp106) in "Hpc".
    (* ---- +0x106: c.addi16sp sp,96 -- the frame goes back ---- *)
    assert (Hwv : add_vec (T5 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))) = sp0)
      by (rewrite HT5sp; apply fw_pop_96).
    assert (Hpop : T5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T5 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12)
      by (rewrite Hwv; exact HT5sp).
    iAssert (stack_own (KTR := KT1) sp0 12)
      with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      iSplitL "Hb7"; [iExists _; iExact "Hb7"|].
      iSplitL "Hb8"; [iExists _; iExact "Hb8"|].
      iSplitL "Hb9"; [iExists _; iExact "Hb9"|].
      iSplitL "Hb10"; [iExists _; iExact "Hb10"|].
      iSplitL "Hb11"; [iExists _; iExact "Hb11"|].
      iSplitL "Hb12"; [iExists _; iExact "Hb12"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (FW + 0x106))
              (mword_of_int 6 : mword 6) T5 (K - 12)%nat 12 b Hpop
              with "Hcg Hpc Hi106 Hframe").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hnk : ((K - 12) + 12)%nat = K) by exact (fw_frame_back K HK).
    iEval (rewrite Hnk) in "Hcg".
    set (T6 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T5 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> T5).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T5 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> T5) with T6.
    assert (Hpp108 : add_vec_int (mword_of_int (FW + 0x106) : mword 64) 2
                     = mword_of_int (FW + 0x108)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp108) in "Hpc".
    (* ---- +0x108: c.jr ra ---- *)
    assert (HT6ra : T6 !!! Regidx Rra = ra0).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1; apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (FW + 0x108)) Rra T6 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi108").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HT6ra) in "Hpc".
    iSpecialize ("Hcont" $! CID7 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! T6 with "[%] Hcg Hpc").
    assert (Hrest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                      r <> Rs0 -> r <> Rs2 -> r <> Rs5 -> r <> Rs6 -> r <> Rra ->
                      T6 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns2 Ns5 Ns6 Nra.
      rewrite /T6 upd_ne; [| regne].
      rewrite /T5 upd_ne; [| regne].
      rewrite /T4 upd_ne; [| regne].
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [| regne].
      exact (Hthr r Hr Nsp Ns0 Ns2 Ns5 Ns6). }
    assert (HT6a0 : T6 !!! Regidx Ra0 = rv).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [| vm_compute; discriminate].
      exact Hmta0. }
    split; [| exact HT6a0].
    rewrite /callee_saved. split_and!.
    9-13: apply Hrest; vm_compute; first [reflexivity | discriminate].
    5-6: apply Hrest; vm_compute; first [reflexivity | discriminate].
    3: apply Hrest; vm_compute; first [reflexivity | discriminate].
    - rewrite /T6 upd_eq Hwv Hsp0. reflexivity.
    - rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq Hs00. reflexivity.
    - rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq Hs20. reflexivity.
    - rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_eq Hs50. reflexivity.
    - rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_eq Hs60. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  [c.ldsp s1,72; c.ldsp s3,56; c.ldsp s7,24; c.ldsp s8,16;            *)
  (*   c.ldsp s9,8] -- TWICE (+0xda the normal exit, +0xea the break),     *)
  (*  one lemma over the block's six pcs as LITERALS.                      *)
  (* =================================================================== *)
  Lemma fw_rest5 `{GEN : GenId} `{CID0 : CpuId}
      (Mt : regfile) (K : nat) (sp0 : mword 64)
      (v1 v3 v7 v8 v9 : mword 64)
      (za zb zc zd ze zf : Z) (p : mword 64) (b : bool) :
    Mt !!! Regidx csp_rs1 = pa_stk sp0 12 ->
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec_int (mword_of_int zb : mword 64) 2 = mword_of_int zc ->
    add_vec_int (mword_of_int zc : mword 64) 2 = mword_of_int zd ->
    add_vec_int (mword_of_int zd : mword 64) 2 = mword_of_int ze ->
    add_vec_int (mword_of_int ze : mword 64) 2 = mword_of_int zf ->
    sie_cap_gpr KT1 Mt K b p -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")),
             sp, Regidx Rs1, false, 8)) -∗
    instr (mword_of_int zb : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")),
             sp, Regidx Rs3, false, 8)) -∗
    instr (mword_of_int zc : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")),
             sp, Regidx Rs7, false, 8)) -∗
    instr (mword_of_int zd : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")),
             sp, Regidx Rs8, false, 8)) -∗
    instr (mword_of_int ze : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
             sp, Regidx Rs9, false, 8)) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) v1 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) v3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) v7 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) v8 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) v9 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ Mr !!! Regidx csp_rs1 = pa_stk sp0 12
          /\ Mr !!! Regidx Rs1 = v1 /\ Mr !!! Regidx Rs3 = v3
          /\ Mr !!! Regidx Rs7 = v7 /\ Mr !!! Regidx Rs8 = v8
          /\ Mr !!! Regidx Rs9 = v9
          /\ (forall r : mword 5, is_cs_idx r = true ->
                r <> Rs1 -> r <> Rs3 -> r <> Rs7 -> r <> Rs8 -> r <> Rs9 ->
                Mr !!! Regidx r = Mt !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 Mr K b p -∗
        pc_is (mword_of_int zf : mword 64) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) v1 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) v3 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) v7 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) v8 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) v9 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hmtsp Hab Hbc Hcd Hde Hef.
    iIntros "Hcg Hpc Hia Hib Hic Hid Hie Hb3 Hb5 Hb9 Hb10 Hb11 Hcont".
    (* ---- s1 ---- *)
    assert (Hpa3 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                   = pa_stk sp0 3) by (rewrite Hmtsp; apply fw_frm3).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int za) (mword_of_int 9 : mword 6) Rs1
              Mt K v1 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia Hb3").
    iIntros (CID1 Hq1) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (U1 := <[Regidx Rs1 := regval_into_reg v1]> Mt).
    assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /U1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    iEval (rewrite Hab) in "Hpc".
    (* ---- s3 ---- *)
    assert (Hpa5 : add_vec (U1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                   = pa_stk sp0 5) by (rewrite HU1sp; apply fw_frm5).
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int zb) (mword_of_int 7 : mword 6) Rs3
              U1 K v3 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib Hb5").
    iIntros (CID2 Hq2) "Hcg Hpc Hb5". iEval (rewrite Hpa5) in "Hb5".
    set (U2 := <[Regidx Rs3 := regval_into_reg v3]> U1).
    assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /U2 upd_ne; [exact HU1sp | vm_compute; discriminate]).
    iEval (rewrite Hbc) in "Hpc".
    (* ---- s7 ---- *)
    assert (Hpa9 : add_vec (U2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk sp0 9) by (rewrite HU2sp; apply fw_frm9).
    iEval (rewrite -Hpa9) in "Hb9".
    iApply (wp_cldsp_s_sconf (mword_of_int zc) (mword_of_int 3 : mword 6) Rs7
              U2 K v7 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic Hb9").
    iIntros (CID3 Hq3) "Hcg Hpc Hb9". iEval (rewrite Hpa9) in "Hb9".
    set (U3 := <[Regidx Rs7 := regval_into_reg v7]> U2).
    assert (HU3sp : U3 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /U3 upd_ne; [exact HU2sp | vm_compute; discriminate]).
    iEval (rewrite Hcd) in "Hpc".
    (* ---- s8 ---- *)
    assert (Hpa10 : add_vec (U3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                    = pa_stk sp0 10) by (rewrite HU3sp; apply fw_frm10).
    iEval (rewrite -Hpa10) in "Hb10".
    iApply (wp_cldsp_s_sconf (mword_of_int zd) (mword_of_int 2 : mword 6) Rs8
              U3 K v8 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hid Hb10").
    iIntros (CID4 Hq4) "Hcg Hpc Hb10". iEval (rewrite Hpa10) in "Hb10".
    set (U4 := <[Regidx Rs8 := regval_into_reg v8]> U3).
    assert (HU4sp : U4 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /U4 upd_ne; [exact HU3sp | vm_compute; discriminate]).
    iEval (rewrite Hde) in "Hpc".
    (* ---- s9 ---- *)
    assert (Hpa11 : add_vec (U4 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                    = pa_stk sp0 11) by (rewrite HU4sp; apply fw_frm11).
    iEval (rewrite -Hpa11) in "Hb11".
    iApply (wp_cldsp_s_sconf (mword_of_int ze) (mword_of_int 1 : mword 6) Rs9
              U4 K v9 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie Hb11").
    iIntros (CID5 Hq5) "Hcg Hpc Hb11". iEval (rewrite Hpa11) in "Hb11".
    set (U5 := <[Regidx Rs9 := regval_into_reg v9]> U4).
    iEval (rewrite Hef) in "Hpc".
    iSpecialize ("Hcont" $! CID5 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! U5 with "[%] Hcg Hpc Hb3 Hb5 Hb9 Hb10 Hb11").
    assert (HU5sp : U5 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /U5 upd_ne; [exact HU4sp | vm_compute; discriminate]).
    split; [exact HU5sp|].
    split.
    { rewrite /U5 upd_ne; [| vm_compute; discriminate].
      rewrite /U4 upd_ne; [| vm_compute; discriminate].
      rewrite /U3 upd_ne; [| vm_compute; discriminate].
      rewrite /U2 upd_ne; [| vm_compute; discriminate].
      rewrite /U1; apply upd_eq. }
    split.
    { rewrite /U5 upd_ne; [| vm_compute; discriminate].
      rewrite /U4 upd_ne; [| vm_compute; discriminate].
      rewrite /U3 upd_ne; [| vm_compute; discriminate].
      rewrite /U2; apply upd_eq. }
    split.
    { rewrite /U5 upd_ne; [| vm_compute; discriminate].
      rewrite /U4 upd_ne; [| vm_compute; discriminate].
      rewrite /U3; apply upd_eq. }
    split.
    { rewrite /U5 upd_ne; [| vm_compute; discriminate].
      rewrite /U4; apply upd_eq. }
    split; [rewrite /U5; apply upd_eq|].
    intros r Hr N1 N3 N7 N8 N9.
    rewrite /U5 upd_ne; [| regne].
    rewrite /U4 upd_ne; [| regne].
    rewrite /U3 upd_ne; [| regne].
    rewrite /U2 upd_ne; [| regne].
    rewrite /U1 upd_ne; [reflexivity | regne].
  Qed.

  (* =================================================================== *)
  (*  [c.li a0,-1; c.j +0xfc] -- the FD_DEVICE arm's TWO error exits       *)
  (*  (+0x126 out-of-range major, +0x12a null devsw slot).  Unlike         *)
  (*  fileread's, the value goes straight into a0: filewrite's epilogue    *)
  (*  has no [c.mv a0,s2] of its own.                                      *)
  (* =================================================================== *)
  Lemma fw_m1j `{GEN : GenId} `{CID0 : CpuId}
      (Mt : regfile) (K : nat)
      (za zb : Z) (jimm : mword 21) (p : mword 64) (b : bool) :
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec (mword_of_int zb : mword 64) (sign_extend' 64 jimm)
      = mword_of_int (FW + 0xfc) ->
    sie_cap_gpr KT1 Mt K b p -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx Ra0, ADDI)) -∗
    instr (mword_of_int zb : mword 64) true (JAL (jimm, zreg)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ Mr !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
          /\ (forall r : mword 5, is_cs_idx r = true ->
                Mr !!! Regidx r = Mt !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 Mr K b p -∗
        pc_is (mword_of_int (FW + 0xfc) : mword 64) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hab Hjt.
    iIntros "Hcg Hpc Hia Hib Hcont".
    iApply (wp_cli_s_sconf (mword_of_int za) Ra0 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) Mt K b
              ltac:(vm_compute; discriminate) ltac:(rdok) fr_lim1
              with "Hcg Hpc Hia").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (W1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> Mt).
    iEval (rewrite Hab) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int zb) jimm W1 K b
              ltac:(rewrite Hjt; vm_compute; reflexivity)
              with "Hcg Hpc Hib").
    iIntros (CID2 Hq2). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Hjt) in "Hpc".
    iSpecialize ("Hcont" $! CID2 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! W1 with "[%] Hcg Hpc").
    split; [rewrite /W1; apply upd_eq|].
    intros r Hr. rewrite /W1 upd_ne; [reflexivity | regne].
  Qed.


  (* =================================================================== *)
  (*  [c.li a0,-1; c.ldsp s4,48(sp); c.j +0xfc] -- the SHORT-WRITE exit    *)
  (*  at +0x12e.  It is the [fw_m1j] block with s4's own restore wedged    *)
  (*  in, because the FD_INODE arm is the only one that spilled s4.        *)
  (* =================================================================== *)
  Lemma fw_m1j4 `{GEN : GenId} `{CID0 : CpuId}
      (Mt : regfile) (K : nat) (sp0 : mword 64) (v4 : mword 64)
      (za zb zc : Z) (jimm : mword 21) (p : mword 64) (b : bool) :
    Mt !!! Regidx csp_rs1 = pa_stk sp0 12 ->
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec_int (mword_of_int zb : mword 64) 2 = mword_of_int zc ->
    add_vec (mword_of_int zc : mword 64) (sign_extend' 64 jimm)
      = mword_of_int (FW + 0xfc) ->
    sie_cap_gpr KT1 Mt K b p -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx Ra0, ADDI)) -∗
    instr (mword_of_int zb : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")),
             sp, Regidx Rs4, false, 8)) -∗
    instr (mword_of_int zc : mword 64) true (JAL (jimm, zreg)) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) v4 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ Mr !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
          /\ Mr !!! Regidx Rs4 = v4
          /\ (forall r : mword 5, is_cs_idx r = true -> r <> Rs4 ->
                Mr !!! Regidx r = Mt !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 Mr K b p -∗
        pc_is (mword_of_int (FW + 0xfc) : mword 64) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) v4 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hmtsp Hab Hbc Hjt.
    iIntros "Hcg Hpc Hia Hib Hic Hb6 Hcont".
    iApply (wp_cli_s_sconf (mword_of_int za) Ra0 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) Mt K b
              ltac:(vm_compute; discriminate) ltac:(rdok) fr_lim1
              with "Hcg Hpc Hia").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (W1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> Mt).
    assert (HW1sp : W1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /W1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    iEval (rewrite Hab) in "Hpc".
    assert (Hpa6 : add_vec (W1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite HW1sp; apply fw_frm6).
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int zb) (mword_of_int 6 : mword 6) Rs4
              W1 K v4 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib Hb6").
    iIntros (CID2 Hq2) "Hcg Hpc Hb6". iEval (rewrite Hpa6) in "Hb6".
    set (W2 := <[Regidx Rs4 := regval_into_reg v4]> W1).
    iEval (rewrite Hbc) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int zc) jimm W2 K b
              ltac:(rewrite Hjt; vm_compute; reflexivity)
              with "Hcg Hpc Hic").
    iIntros (CID3 Hq3). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Hjt) in "Hpc".
    iSpecialize ("Hcont" $! CID3 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! W2 with "[%] Hcg Hpc Hb6").
    split.
    { rewrite /W2 upd_ne; [| vm_compute; discriminate].
      rewrite /W1; apply upd_eq. }
    split; [rewrite /W2; apply upd_eq|].
    intros r Hr N4.
    rewrite /W2 upd_ne; [| regne].
    rewrite /W1 upd_ne; [reflexivity | regne].
  Qed.

  (* =================================================================== *)
  (*  +0x6c .. +0x78 -- &devsw[major].write, and the slot's value.         *)
  (*                                                                      *)
  (*  Five instructions with no control flow and no ghost state, run       *)
  (*  after the [bltu] at +0x68 has established that the major is in       *)
  (*  range.  The field is at OFFSET 8 ([.read] is the first of the two    *)
  (*  function pointers) -- S3a's decode note 2, and the one place where   *)
  (*  copying fileread's block would have been WRONG.                      *)
  (* =================================================================== *)
  Lemma fw_devidx `{GEN : GenId} `{CID0 : CpuId}
      (Mt : regfile) (K : nat) (mj : Z) (slot : mword 64) (dq : dfrac)
      (p : mword 64) (b : bool) :
    (0 <= mj < 16)%Z ->
    Mt !!! Regidx Ra5 = (mword_of_int mj : mword 64) ->
    sie_cap_gpr KT1 Mt K b p -∗
    kernel_text -∗
    pc_is (mword_of_int (FW + 0x6c) : mword 64) -∗
    word_pointsto (mword_of_int (KernelSyms.devsw + 16 * mj + 8)) dq slot -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ Mr !!! Regidx Ra5 = slot
          /\ (forall r : mword 5, r <> Ra4 -> r <> Ra5 ->
                Mr !!! Regidx r = Mt !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 Mr K b p -∗
        pc_is (mword_of_int (FW + 0x7a) : mword 64) -∗
        word_pointsto (mword_of_int (KernelSyms.devsw + 16 * mj + 8)) dq slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hmj Ha5.
    iIntros "Hcg #Htext Hpc Hslot Hcont".
    iPoseProof (fwri_06c with "Htext") as "Hi6c".
    iPoseProof (fwri_06e with "Htext") as "Hi6e".
    iPoseProof (fwri_072 with "Htext") as "Hi72".
    iPoseProof (fwri_076 with "Htext") as "Hi76".
    iPoseProof (fwri_078 with "Htext") as "Hi78".
    (* ---- +0x6c c.slli a5,a5,4 : major * 16 ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int (FW + 0x6c)) (Regidx Ra5) Ra5
              (mword_of_int 4 : mword 6) Mt K b
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (shift_bits_left (rget Mt Ra5)
                     (subrange_vec_dec (mword_of_int 4 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> Mt).
    assert (HD1a5 : D1 !!! Regidx Ra5 = (mword_of_int (16 * mj) : mword 64)).
    { rewrite /D1 upd_eq. unfold regval_into_reg. rgne. rewrite Ha5.
      exact (fr_slli4_moi mj (proj1 Hmj) (proj2 Hmj)). }
    assert (Hpp6e : add_vec_int (mword_of_int (FW + 0x6c) : mword 64) 2
                    = mword_of_int (FW + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6e) in "Hpc".
    (* ---- +0x6e / +0x72: a4 := &devsw ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (FW + 0x6e)) Ra4
              (mword_of_int 30 : mword 20) D1 K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (D2 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (FW + 0x6e) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> D1).
    assert (Hpp72 : add_vec_int (mword_of_int (FW + 0x6e) : mword 64) 4
                    = mword_of_int (FW + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp72) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (FW + 0x72)) Ra4 Ra4
              (mword_of_int 204 : mword 12) D2 K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi72").
    iIntros (CID3 Hq3) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (D3 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (D2 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 204 : mword 12)))]> D2).
    assert (HD3a4 : D3 !!! Regidx Ra4 = (mword_of_int KernelSyms.devsw : mword 64)).
    { rewrite /D3 upd_eq /D2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HD3a5 : D3 !!! Regidx Ra5 = (mword_of_int (16 * mj) : mword 64)).
    { rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [exact HD1a5 | vm_compute; discriminate]. }
    assert (Hpp76 : add_vec_int (mword_of_int (FW + 0x72) : mword 64) 4
                    = mword_of_int (FW + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* ---- +0x76 c.add a5,a5,a4 ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (FW + 0x76)) Ra5 Ra4 D3 K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi76").
    iIntros (CID4 Hq4) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
    set (D4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (D3 !!! Regidx Ra5) (D3 !!! Regidx Ra4))]> D3).
    assert (HD4a5 : D4 !!! Regidx Ra5
                    = (mword_of_int (KernelSyms.devsw + 16 * mj) : mword 64)).
    { rewrite /D4 upd_eq. unfold regval_into_reg.
      rewrite HD3a5 HD3a4 fr_addv64_moi. f_equal. lia. }
    assert (Hpp78 : add_vec_int (mword_of_int (FW + 0x76) : mword 64) 2
                    = mword_of_int (FW + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp78) in "Hpc".
    (* ---- +0x78 c.ld a5,8(a5) : devsw[major].WRITE ---- *)
    assert (Hpsl : add_vec (rget D4 Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (mword_of_int (KernelSyms.devsw + 16 * mj + 8) : mword 64)).
    { rewrite (rget_ne D4 Ra5 ltac:(vm_compute; discriminate)) HD4a5.
      rewrite (_ : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                   = (mword_of_int 8 : mword 64));
        [| apply bv_eq; vm_compute; reflexivity].
      by rewrite fr_addv64_moi. }
    iEval (rewrite -Hpsl) in "Hslot".
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x78)) Ra5 Ra5
              (mword_of_int 8 : mword 12) D4 K slot b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 Hslot").
    iIntros (CID5 Hq5) "Hcg Hpc Hslot". iEval (rewrite Hpsl) in "Hslot".
    set (D5 := <[Regidx Ra5 := regval_into_reg slot]> D4).
    assert (Hpp7a : add_vec_int (mword_of_int (FW + 0x78) : mword 64) 2
                    = mword_of_int (FW + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7a) in "Hpc".
    iSpecialize ("Hcont" $! CID5 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! D5 with "[%] Hcg Hpc Hslot").
    split; [rewrite /D5; apply upd_eq|].
    intros r N4 N5.
    rewrite /D5 upd_ne; [| regne].
    rewrite /D4 upd_ne; [| regne].
    rewrite /D3 upd_ne; [| regne].
    rewrite /D2 upd_ne; [| regne].
    rewrite /D1 upd_ne; [reflexivity | regne].
  Qed.

  (* =================================================================== *)
  (*  +0x10a .. +0x11e -- THE ELSE ARM.  panic("filewrite").              *)
  (*                                                                      *)
  (*  A COMPLETE arm, not a fragment: panic never returns, so there is     *)
  (*  nothing after the [jal].  gcc emitted the six shrink-wrapped spills  *)
  (*  here too (the arm is laid out after the returns), which is why the   *)
  (*  block consumes six frame slots and gives nothing back.  Decode note  *)
  (*  3: this is the ELSE arm -- the type is none of FD_PIPE / FD_DEVICE / *)
  (*  FD_INODE -- and NOT a short-write panic.                             *)
  (*                                                                       *)
  (*  panic() IS AN ORDINARY CALL.  This file is a plain [Section], not a  *)
  (*  functor, so the contract arrives as a [Hypothesis] on the nested     *)
  (*  section below and only THIS lemma gains an argument; ProofFilewrite  *)
  (*  supplies it from its own [(PN : PANIC)].                             *)
  (* =================================================================== *)
  Section FwPanicArm.
    Context `{!lockG Σ, !uartGhostG Σ, !diskGhostG Σ}.
    Context `{GEN : GenId}.

    (* CID is EXPLICIT here, unlike [PANIC]'s own [`{CID : CpuId}]: a
       maximally-inserted implicit is instantiated the moment the constant
       is named, so [PN.wp_panic_sconf] passed as an argument would arrive
       already pinned at one hart.  The call site eta-expands. *)
    Hypothesis wp_panic_sconf :
      forall (CID : CpuId) (m : regfile) (K : nat)
        (n : nat) (eb : bool) (b : bool) (p : mword 64)
        (dm : pk_arg_desc) (lks : gset string),
        wp_panic_sconf_body KT1 (CID := CID) m K n eb b p dm lks.

  Lemma fw_panic `{CID0 : CpuId}
      (Mt : regfile) (K : nat) (sp0 : mword 64)
      (u3 u5 u6 u9 u10 u11 : mword 64) (p : mword 64) (eb b : bool)
      (lks : gset string) :
    Mt !!! Regidx csp_rs1 = pa_stk sp0 12 ->
    (panic_stack <= K)%nat ->
    locks_below lks "log" ->
    sie_cap_gpr KT1 Mt K b p -∗
    cpu_own 0%nat eb p b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (FW + 0x10a) : mword 64) -∗
    panic_env -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) u3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) u5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) u6 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) u9 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) u10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) u11 -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hmtsp HK Hbelow.
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv Hb3 Hb5 Hb6 Hb9 Hb10 Hb11".
    iPoseProof (fwri_10a with "Htext") as "Hi10a".
    iPoseProof (fwri_10c with "Htext") as "Hi10c".
    iPoseProof (fwri_10e with "Htext") as "Hi10e".
    iPoseProof (fwri_110 with "Htext") as "Hi110".
    iPoseProof (fwri_112 with "Htext") as "Hi112".
    iPoseProof (fwri_114 with "Htext") as "Hi114".
    iPoseProof (fwri_116 with "Htext") as "Hi116".
    iPoseProof (fwri_11a with "Htext") as "Hi11a".
    iPoseProof (fwri_11e with "Htext") as "Hi11e".
    (* ---- +0x10a c.sdsp s1,72(sp) ---- *)
    assert (Hpa3 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                   = pa_stk sp0 3) by (rewrite Hmtsp; apply fw_frm3).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x10a)) (mword_of_int 9 : mword 6) Rs1
              Mt K u3 b with "Hcg Hpc Hi10a Hb3").
    iIntros (CID1 Hq1) "Hcg Hpc Hb3".
    assert (Hpp10c : add_vec_int (mword_of_int (FW + 0x10a) : mword 64) 2
                     = mword_of_int (FW + 0x10c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10c) in "Hpc".
    (* ---- +0x10c c.sdsp s3,56(sp) ---- *)
    assert (Hpa5 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                   = pa_stk sp0 5) by (rewrite Hmtsp; apply fw_frm5).
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x10c)) (mword_of_int 7 : mword 6) Rs3
              Mt K u5 b with "Hcg Hpc Hi10c Hb5").
    iIntros (CID2 Hq2) "Hcg Hpc Hb5".
    assert (Hpp10e : add_vec_int (mword_of_int (FW + 0x10c) : mword 64) 2
                     = mword_of_int (FW + 0x10e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10e) in "Hpc".
    (* ---- +0x10e c.sdsp s4,48(sp) ---- *)
    assert (Hpa6 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite Hmtsp; apply fw_frm6).
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x10e)) (mword_of_int 6 : mword 6) Rs4
              Mt K u6 b with "Hcg Hpc Hi10e Hb6").
    iIntros (CID3 Hq3) "Hcg Hpc Hb6".
    assert (Hpp110 : add_vec_int (mword_of_int (FW + 0x10e) : mword 64) 2
                     = mword_of_int (FW + 0x110)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp110) in "Hpc".
    (* ---- +0x110 c.sdsp s7,24(sp) ---- *)
    assert (Hpa9 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk sp0 9) by (rewrite Hmtsp; apply fw_frm9).
    iEval (rewrite -Hpa9) in "Hb9".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x110)) (mword_of_int 3 : mword 6) Rs7
              Mt K u9 b with "Hcg Hpc Hi110 Hb9").
    iIntros (CID4 Hq4) "Hcg Hpc Hb9".
    assert (Hpp112 : add_vec_int (mword_of_int (FW + 0x110) : mword 64) 2
                     = mword_of_int (FW + 0x112)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp112) in "Hpc".
    (* ---- +0x112 c.sdsp s8,16(sp) ---- *)
    assert (Hpa10 : add_vec (Mt !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                    = pa_stk sp0 10) by (rewrite Hmtsp; apply fw_frm10).
    iEval (rewrite -Hpa10) in "Hb10".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x112)) (mword_of_int 2 : mword 6) Rs8
              Mt K u10 b with "Hcg Hpc Hi112 Hb10").
    iIntros (CID5 Hq5) "Hcg Hpc Hb10".
    assert (Hpp114 : add_vec_int (mword_of_int (FW + 0x112) : mword 64) 2
                     = mword_of_int (FW + 0x114)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp114) in "Hpc".
    (* ---- +0x114 c.sdsp s9,8(sp) ---- *)
    assert (Hpa11 : add_vec (Mt !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                    = pa_stk sp0 11) by (rewrite Hmtsp; apply fw_frm11).
    iEval (rewrite -Hpa11) in "Hb11".
    iApply (wp_csdsp_s_sconf (mword_of_int (FW + 0x114)) (mword_of_int 1 : mword 6) Rs9
              Mt K u11 b with "Hcg Hpc Hi114 Hb11").
    iIntros (CID6 Hq6) "Hcg Hpc Hb11".
    assert (Hpp116 : add_vec_int (mword_of_int (FW + 0x114) : mword 64) 2
                     = mword_of_int (FW + 0x116)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp116) in "Hpc".
    (* ---- +0x116 / +0x11a: a0 := "filewrite" ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (FW + 0x116)) Ra0
              (mword_of_int 3 : mword 20) Mt K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi116").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (FW + 0x116) : mword 64)
                     (auipc_off (mword_of_int 3 : mword 20)))]> Mt).
    assert (Hpp11a : add_vec_int (mword_of_int (FW + 0x116) : mword 64) 4
                     = mword_of_int (FW + 0x11a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp11a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (FW + 0x11a)) Ra0 Ra0
              (mword_of_int 396 : mword 12) P1 K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi11a").
    iIntros (CID8 Hq8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (P1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 396 : mword 12)))]> P1).
    assert (Hpp11e : add_vec_int (mword_of_int (FW + 0x11a) : mword 64) 4
                     = mword_of_int (FW + 0x11e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp11e) in "Hpc".
    (* ---- +0x11e jal ra,panic ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (FW + 0x11e)) Rra
              (mword_of_int 2081776 : mword 21) P2 K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi11e").
    iIntros (CID9 Hq9) "Hcg Hpc".
    assert (Htgtpanic : add_vec (mword_of_int (FW + 0x11e) : mword 64)
              (sign_extend' 64 (mword_of_int 2081776 : mword 21))
              = mword_of_int KernelSyms.panic)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpanic) in "Hpc".
    (* ---- panic() AS AN ORDINARY CALL, against SpecPanic ----
       a0 holds &"filewrite"; [kernel_data] mints the literal and
       [panic_env] is the console bundle printk needs.  [cpu_own] has to
       arrive AT THE PANIC HART (CID9), not at the one the block was
       entered on. *)
    iPoseProof (fw_msg_str with "Hkd") as "#Hstr".
    iDestruct (cpu_own_transport CID0 CID9 0%nat eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE REGFILE THE SPEC WANTS IS THE POST-JAL ONE: [wp_jal_s_sconf]
       hands back [sie_cap_gpr (<[rd := pc+4]> m)], so passing [P2] makes
       the unifier grind on [P2 =?= <[Rra := _]> P2] and never return. *)
    pose (P3 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (FW + 0x11e) : mword 64) 4)]> P2).
    assert (Ha0msg : P3 !!! Regidx Ra0 = (mword_of_int fw_msg_a : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_panic_sconf CID9 P3 K
              0%nat eb b p (PkAStr DfracDiscarded fw_msg) lks
              HK eq_refl fw_panic_noff (fw_panic_below lks Hbelow)
              with "Hcg Hcnt Htext Hkd Hpc Hpenv [Hstr]").
    { rewrite /pk_desc_res Ha0msg.
      iSplit; [iPureIntro; exact fw_msg_nonul|].
      iSplit; [iPureIntro; exact fw_msg_nz|]. iExact "Hstr". }
  Qed.

  End FwPanicArm.

  (* =================================================================== *)
  (*  +0xf4 .. the epilogue -- THE FD_INODE ARM'S WHOLE TAIL.             *)
  (*                                                                      *)
  (*  THREE paths reach +0xf4 and no other code does: the zero-trip jump   *)
  (*  at +0xe8, the normal loop exit through the five [c.ldsp]s at +0xda,  *)
  (*  and the short-write break through the SAME five at +0xea.  All       *)
  (*  three arrive in one shape -- s4 = i, s5 = n, s1/s3/s7/s8/s9 already  *)
  (*  back at the caller's values (the zero-trip path never spilled them;  *)
  (*  the other two just restored them) -- so the join is ONE lemma with   *)
  (*  [iz] a parameter, and the seven slots the epilogue does not restore  *)
  (*  stay arbitrary words exactly as Parts' header fact 3 says.           *)
  (*                                                                      *)
  (*  [bne s5,s4] at +0xf4 then decides between the two returning exits:   *)
  (*  fall (i = n) is [c.mv a0,s5 ; c.ldsp s4,48(sp)] into the epilogue,   *)
  (*  taken (i <> n) is +0x12e, i.e. [fw_m1j4].  The disjunction in the    *)
  (*  postcondition is what a caller turns into [filewrite_ret].           *)
  (* =================================================================== *)
  Lemma fw_tail `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s20 s40 s50 s60 : mword 64)
      (nz iz : Z)
      (w3 w5 w9 w10 w11 w12 : mword 64)
      (p : mword 64) (b : bool) :
    (12 <= K)%nat ->
    (0 <= nz < 2 ^ 31)%Z ->
    (0 <= iz < 2 ^ 31)%Z ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs4 = s40 ->
    m !!! Regidx Rs5 = s50 ->
    m !!! Regidx Rs6 = s60 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 12 ->
    Mt !!! Regidx Rs5 = (mword_of_int nz : mword 64) ->
    Mt !!! Regidx Rs4 = (mword_of_int iz : mword 64) ->
    (* s4 is EXCLUDED here and not in [fw_epi]'s list: it still holds [i],
       and the [c.ldsp] at +0xfa / +0x130 is what puts the caller's value
       back before the epilogue ever looks. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs2 -> r <> Rs4 -> r <> Rs5 -> r <> Rs6 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 12)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (FW + 0xf4) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) s40 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) s50 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) s60 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (mf : regfile) (rv : mword 64),
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv
          /\ (rv = (mword_of_int (-1) : mword 64)
              \/ (iz = nz /\ rv = (mword_of_int nz : mword 64)))⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hnz Hiz Hsp0 Hra0 Hs00 Hs20 Hs40 Hs50 Hs60 Hmtsp Hmts5 Hmts4 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12 Hcont".
    iPoseProof (fwri_0f4 with "Htext") as "Hif4".
    assert (Hcmp : neq_vec (rget Mt Rs5) (rget Mt Rs4) = negb (Z.eqb nz iz)).
    { rewrite (rget_ne Mt Rs5 ltac:(vm_compute; discriminate)).
      rewrite (rget_ne Mt Rs4 ltac:(vm_compute; discriminate)).
      rewrite Hmts5 Hmts4. exact (fw_neq_moi nz iz Hnz Hiz). }
    destruct (Z.eqb nz iz) eqn:Hqe.
    - (* ---- i = n : the FULL write.  [c.mv a0,s5] then s4's own restore ---- *)
      assert (Hzi : iz = nz) by (symmetry; apply Z.eqb_eq; exact Hqe).
      iPoseProof (fwri_0f8 with "Htext") as "Hif8".
      iPoseProof (fwri_0fa with "Htext") as "Hifa".
      iApply (wp_bne_fall_s_sconf (mword_of_int (FW + 0xf4))
                (mword_of_int 58 : mword 13) Rs4 Rs5 Mt (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hcmp; reflexivity)
                with "Hcg Hpc Hif4").
      iIntros (CID1 Hq1) "Hcg Hpc".
      assert (Hppf8 : add_vec_int (mword_of_int (FW + 0xf4) : mword 64) 4
                      = mword_of_int (FW + 0xf8)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppf8) in "Hpc".
      (* ---- +0xf8 c.mv a0,s5 : the return value is [n] ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (FW + 0xf8)) Ra0 Rs5 Mt (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hif8").
      iIntros (CID2 Hq2) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (E1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (Mt !!! Regidx Rs5))]> Mt).
      assert (HE1a0 : E1 !!! Regidx Ra0 = (mword_of_int nz : mword 64)).
      { rewrite /E1 upd_eq. unfold regval_into_reg.
        rewrite add_vec_zero_l. exact Hmts5. }
      assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /E1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
      assert (Hppfa : add_vec_int (mword_of_int (FW + 0xf8) : mword 64) 2
                      = mword_of_int (FW + 0xfa)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppfa) in "Hpc".
      (* ---- +0xfa c.ldsp s4,48(sp) : the caller's s4 comes back ---- *)
      assert (Hpa6 : add_vec (E1 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                     = pa_stk sp0 6) by (rewrite HE1sp; apply fw_frm6).
      iEval (rewrite -Hpa6) in "Hb6".
      iApply (wp_cldsp_s_sconf (mword_of_int (FW + 0xfa)) (mword_of_int 6 : mword 6) Rs4
                E1 (K - 12)%nat s40 b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hifa Hb6").
      iIntros (CID3 Hq3) "Hcg Hpc Hb6". iEval (rewrite Hpa6) in "Hb6".
      set (E2 := <[Regidx Rs4 := regval_into_reg s40]> E1).
      assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
      assert (HE2a0 : E2 !!! Regidx Ra0 = (mword_of_int nz : mword 64))
        by (rewrite /E2 upd_ne; [exact HE1a0 | vm_compute; discriminate]).
      assert (HE2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs2 -> r <> Rs5 -> r <> Rs6 ->
                E2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp Ns0 Ns2 Ns5 Ns6.
        destruct (decide (r = Rs4)) as [-> | N4].
        { rewrite /E2 upd_eq. unfold regval_into_reg. by rewrite Hs40. }
        rewrite /E2 upd_ne; [| regne].
        rewrite /E1 upd_ne; [| regne].
        exact (Hthr r Hr Nsp Ns0 Ns2 N4 Ns5 Ns6). }
      assert (Hppfc : add_vec_int (mword_of_int (FW + 0xfa) : mword 64) 2
                      = mword_of_int (FW + 0xfc)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppfc) in "Hpc".
      iApply (fw_epi (CID0 := CID3) m E2 K sp0 ra0 s00 s20 s50 s60
                (mword_of_int nz) w3 w5 s40 w9 w10 w11 w12 p b
                HK Hsp0 Hra0 Hs00 Hs20 Hs50 Hs60 HE2sp HE2a0 HE2thr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12").
      iIntros (CIDe Hse mf) "%Hcsr Hcg Hpc".
      destruct Hcsr as [Hcsf Hrv].
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! mf (mword_of_int nz) with "[%] Hcg Hpc").
      split_and!; [exact Hcsf | exact Hrv |].
      right. split; [exact Hzi | reflexivity].
    - (* ---- i <> n : the SHORT write.  +0x12e is [fw_m1j4] ---- *)
      iPoseProof (fwri_12e with "Htext") as "Hi12e".
      iPoseProof (fwri_130 with "Htext") as "Hi130".
      iPoseProof (fwri_132 with "Htext") as "Hi132".
      assert (Htgt12e : add_vec (mword_of_int (FW + 0xf4) : mword 64)
                (sign_extend' 64 (mword_of_int 58 : mword 13))
                = mword_of_int (FW + 0x12e))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bne_taken_s_sconf (mword_of_int (FW + 0xf4))
                (mword_of_int 58 : mword 13) Rs4 Rs5 Mt (K - 12)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hcmp; reflexivity)
                ltac:(rewrite Htgt12e; vm_compute; reflexivity)
                with "Hcg Hpc Hif4").
      iNext. iIntros (CID1 Hq1) "Hcg Hpc".
      iEval (rewrite Htgt12e) in "Hpc".
      iApply (fw_m1j4 (CID0 := CID1) Mt (K - 12)%nat sp0 s40
                (FW + 0x12e) (FW + 0x130) (FW + 0x132)
                (sign_extend' 21 (concat_vec (mword_of_int 2021 : mword 11) ('b"0")))
                p b Hmtsp
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi12e Hi130 Hi132 Hb6").
      iIntros (CID2 Hq2 Mr) "%Hmr Hcg Hpc Hb6".
      destruct Hmr as (Hmra0 & Hmrs4 & Hmrthr).
      assert (HMrsp : Mr !!! Regidx csp_rs1 = pa_stk sp0 12).
      { rewrite (Hmrthr csp_rs1 ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; discriminate)).
        exact Hmtsp. }
      assert (HMrthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs2 -> r <> Rs5 -> r <> Rs6 ->
                Mr !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp Ns0 Ns2 Ns5 Ns6.
        destruct (decide (r = Rs4)) as [-> | N4]; [by rewrite Hmrs4 Hs40 |].
        rewrite (Hmrthr r Hr N4).
        exact (Hthr r Hr Nsp Ns0 Ns2 N4 Ns5 Ns6). }
      iApply (fw_epi (CID0 := CID2) m Mr K sp0 ra0 s00 s20 s50 s60
                (mword_of_int (-1)) w3 w5 s40 w9 w10 w11 w12 p b
                HK Hsp0 Hra0 Hs00 Hs20 Hs50 Hs60 HMrsp Hmra0 HMrthr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12").
      iIntros (CIDe Hse mf) "%Hcsr Hcg Hpc".
      destruct Hcsr as [Hcsf Hrv].
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! mf (mword_of_int (-1)) with "[%] Hcg Hpc").
      split_and!; [exact Hcsf | exact Hrv |]. by left.
  Qed.

End ProofFilewriteParts.
