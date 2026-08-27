(* ProofSysOpenParts.v -- sys_open's PURE side conditions, its frame carve
   and its epilogue: everything the walk needs that does not apply a
   callee's contract, and therefore everything that can live outside the
   module functor.

   The walk itself is [ProofSysOpen.v]; the op-wide log ledger is
   [SysOpenBudget.v]; the contract is [SpecSysOpen.v], whose header carries
   the arm graph and the frame map.

   NOTHING HERE IS IMPORTED FROM ANOTHER FUNCTION'S PROOF.  The sign
   cluster and the sixteen-bit compare cluster are restated rather than
   taken from [ProofSysLinkParts] / [ProofSysChdir]: a whole-function proof
   file is not a dependency any other one may take.

   ==== THE ONE THING THAT IS NOT sys_link's SHAPE ======================

   THE CALLEE-SAVES ARE SHRINK-WRAPPED, so the frame CARVE is arm-dependent
   in the walk even though the two lemmas below are not.  [c.sdsp s1,168]
   runs at +0x28 only after the [argstr < 0] branch falls through,
   [c.sdsp s2,160] at +0x5e only after the T_DEVICE test, and
   [c.sdsp s3,152] at +0x68 only after filealloc succeeded; each exit
   reloads exactly the subset its own path saved, and ARM 0 never owns slot
   5 at all.  [stack_own] is [∃ w]-shaped PER SLOT, so the carve and the
   join below are uniform anyway -- what is arm-dependent is which of the
   five slots the walk can still prove holds the ENTRY value of its
   register, which is why [so_epilogue] takes slots 3, 4 and 5 at
   existential contents and the two saved-and-restored ones by name.

   THE OTHER DIFFERENCE IS THE OMODE CELL.  [omode] is an [int] at
   [s0-180], i.e. the UPPER WORD of slot 23, and every access to it is an
   [lw] (+0x2e, +0xf6, +0x8c, +0xa8).  So sys_open needs
   [InstrBytes.word_pointsto_split4] on exactly one slot and nothing else --
   the only other halfword traffic is [lh]/[lhu] on inode fields, which
   [IcacheEscrow]'s [inode_meta] already hands out at [↦₂], and the [sh]
   into [f->major], which [FileInvDefs.file_fields] already holds at
   [↦₂]. *)
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
Require Import StackOwn StackBytes.
Require Import CalleeSaved KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs.
Require Import WpLock.                (* [lockG] -- bound in the publication's
                                         section, and a class that is not
                                         IMPORTED becomes a fresh VARIABLE *)
Require Import ByteBuf.
Require Import ProcGeom.
Require Import DinodeEnc.
Require Import DirView.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED EARLY on purpose
   -- the [FsState*] stack exports [fs_view] and [byte_range], both of which
   have live twins below, and the LAST import wins (durable-notes, "AND
   WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsState.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import FsBlocks.              (* [fs_names] *)
Require Import BioDefs.               (* [BSIZE] *)
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IcacheRef.             (* the reference algebra the publication
                                         re-pins its generation in *)
(* KEPT against 43b8097e's sweep: it judged these dead in ITS tree, which
   does not carry our fragment-campaign content.  A surplus import costs a
   rebuild-cone edge; a missing one costs the build.  If the next nightly
   sweep still calls them dead against THIS tree, they can go then. *)
Require Import FsTree.
Require Import IcacheEscrow.          (* [ic_loaded] -- the O_TRUNC bridge *)
Require Import FileInvDefs.           (* [fcontent], [fc_wbool] -- the omode
                                         bit cluster's target *)
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIunlock.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecItrunc.
Require Import SpecNamei.
Require Import SpecCreate.
Require Import SpecFdalloc.
Require Import SpecFileclose.
Require Import CodeSysOpen.
Require Import SpecSysOpen.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import IrefSlots.  (* [iref_frac] rides [file_core] -- FileInvDefs *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Set Printing Depth 40.

Notation SO := KernelSyms.sys_open (only parsing).

(* ===================================================================== *)
(*  THE REGISTER LEDGER                                                   *)
(* ===================================================================== *)

(* the five registers this frame moves: sp, s0 (the frame pointer),
   s1 (ip), s2 (f), s3 (fd).  Everything else callee-saved rides straight
   through, and it is stated POSITIVELY where it matters -- the five
   exceptions are exactly the five the code writes, each accounted for by
   its own equation. *)
Definition so_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) ->
    c <> (mword_of_int 19 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma so_thr_refl (m : regfile) : so_thr m m.
Proof. intros c _ _ _ _ _ _. reflexivity. Qed.

Lemma so_thr_trans (m M P : regfile) : so_thr m M -> so_thr M P -> so_thr m P.
Proof.
  intros H1 H2 c Hc N2 N8 N9 N18 N19.
  rewrite (H2 c Hc N2 N8 N9 N18 N19). exact (H1 c Hc N2 N8 N9 N18 N19).
Qed.

Definition so_sp (sp0 : mword 64) (M : regfile) : Prop :=
  (M !!! Regidx csp_rs1 : mword 64) = pa_stk sp0 24.

(* ===================================================================== *)
(*  THE FRAME ARITHMETIC -- 192 bytes, TWENTY-FOUR slots                  *)
(* ===================================================================== *)

(* -192 / +192, both a [c.addi16sp] (52 is -12 in a 6-bit field, x16;
   12 is +12). *)
Lemma so_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 52 : mword 6)))
  = pa_stk X 24.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma so_pop (X : mword 64) :
  add_vec (pa_stk X 24) (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,192] -- the frame pointer, back at the entry sp. *)
Lemma so_fp (X : mword 64) :
  add_vec (pa_stk X 24) (sign_extend' 64 (caddi4spn_imm (mword_of_int 48 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [path] at [s0-176] (the frame pointer IS the entry sp), i.e. slots 7..22
   read from the top -- sixteen slots of byte buffer. *)
Lemma so_bufpath (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3920 : mword 12)) = pa_stk X 22.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* [omode] at [s0-180]: the UPPER WORD of slot 23.  This is the ONLY place
   sys_open needs a 4-byte view of a frame slot. *)
Lemma so_omode (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3916 : mword 12))
  = pa_add (pa_stk X 23) 4.
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
Lemma so_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (bv_wrap 64 (uint (mword_of_int (- (8 * Z.of_nat 24)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 24) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite pa_stk_off2. apply f_equal. exact H.
Qed.

Lemma so_frm1 (X : mword 64) :
  add_vec (pa_stk X 24)
    (zero_extend' 64 (concat_vec (mword_of_int 23 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply so_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma so_frm2 (X : mword 64) :
  add_vec (pa_stk X 24)
    (zero_extend' 64 (concat_vec (mword_of_int 22 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply so_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma so_frm3 (X : mword 64) :
  add_vec (pa_stk X 24)
    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply so_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma so_frm4 (X : mword 64) :
  add_vec (pa_stk X 24)
    (zero_extend' 64 (concat_vec (mword_of_int 20 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply so_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma so_frm5 (X : mword 64) :
  add_vec (pa_stk X 24)
    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. apply so_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* [K_sys_open]'s single premise, turned into every bound the twelve callees
   and the [sie_cap_gpr] pop want. *)
Lemma so_kb (K : nat) : (K_sys_open <= K)%nat ->
  (K_create <= K - 24)%nat /\ (K_namei <= K - 24)%nat /\
  (18 <= K - 24)%nat /\ (argstr_stack <= K - 24)%nat /\
  (K_begin_op <= K - 24)%nat /\ (K_end_op <= K - 24)%nat /\
  (K_ilock <= K - 24)%nat /\ (K_iunlock <= K - 24)%nat /\
  (K_itrunc <= K - 24)%nat /\
  (K_iput <= K - 24)%nat /\ (K_iunlockput <= K - 24)%nat /\
  (fileclose_stack <= K - 24)%nat /\ (14 <= K - 24)%nat /\
  (fdalloc_stack <= K - 24)%nat /\
  (10 <= K - 24)%nat /\ (24 <= K)%nat /\ ((K - 24) + 24 = K)%nat.
Proof.
  (* [fileclose_stack] is [8 + K_iput], so it has to be unfolded BEFORE
     [K_iput] -- [unfold] walks its argument list once, and a constant it
     EXPOSES later in the list stays folded. *)
  
  intro H. split_and!; lia.
Qed.

(* ===================================================================== *)
(*  THE SIGN CLUSTER: the two [bltz]s (+0x24 argstr, +0x70 fdalloc)       *)
(* ===================================================================== *)

Lemma so_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
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

Lemma so_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (so_sint_moi z Hz). lia.
Qed.

Lemma so_m1_neg :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma so_zero_nonneg :
  zopz0zI_s (mword_of_int 0 : mword 64) (zero_reg : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

Lemma so_len_range (k : nat) : (k < 128)%nat -> (0 <= Z.of_nat k < 2 ^ 31)%Z.
Proof.
  intro Hk.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

Lemma so_maxpath_lt : (Z.of_nat 128 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma so_arg0_lt : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma so_arg1_lt : (1 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma so_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* the descriptor fdalloc returns is in [0, NOFILE), hence signed-nonneg --
   which is what makes the [bltz a0] at +0x70 fall through on the success
   arm and what makes the returned a0 a legal descriptor literal. *)
Lemma so_fd_range (fd : nat) : (fd < NOFILE)%nat -> (0 <= Z.of_nat fd < 2 ^ 31)%Z.
Proof.
  intro Hk. unfold NOFILE in Hk.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* ===================================================================== *)
(*  THE SIXTEEN-BIT COMPARE CLUSTER: the three type tests.                *)
(*  ALL are [BEQ]/[BNE] against a sign-extended [lh] of [ip->type], so     *)
(*  all three go through the same injectivity lemma at three literals:     *)
(*  T_DIR = 1 (+0xf2), T_FILE = 2 (+0xb4), T_DEVICE = 3 (+0x50, +0x7a).    *)
(* ===================================================================== *)

Lemma so_sext16_inj (x y : mword 16) :
  (sign_extend' 64 x : mword 64) = (sign_extend' 64 y : mword 64) -> x = y.
Proof.
  intros H. apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H;
    [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

Lemma so_sext_lit (n : Z) : (0 <= n < 32768)%Z ->
  (sign_extend' 64 (mword_of_int n : mword 16) : mword 64)
  = (mword_of_int n : mword 64).
Proof.
  intro Hn.
  apply bv_eq.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  assert (Hs : bv_signed (mword_of_int n : mword 16) = n).
  { unfold bv_signed.
    assert (Hu : bv_unsigned (mword_of_int n : mword 16) = n).
    { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (Z.of_N 16) with 16%Z.
      assert (E16 : (2 ^ 16 = 65536)%Z) by (vm_compute; reflexivity).
      rewrite E16. rewrite Z.mod_small; [reflexivity | lia]. }
    rewrite Hu. apply bv_swrap_small.
    unfold bv_half_modulus, bv_modulus. change (Z.of_N 16) with 16%Z.
    assert (Eh : (2 ^ 16 / 2 = 32768)%Z) by (vm_compute; reflexivity).
    rewrite Eh. lia. }
  rewrite Hs. rewrite moi64_unsigned. reflexivity.
Qed.

Lemma so_ty_eq (t : mword 16) (n : Z) : (0 <= n < 32768)%Z ->
  t = (mword_of_int n : mword 16) ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int n : mword 64) = true.
Proof.
  intros Hn ->. rewrite (so_sext_lit n Hn).
  exact (proj2 (eq_vec_true_iff _ _) eq_refl).
Qed.

Lemma so_ty_ne (t : mword 16) (n : Z) : (0 <= n < 32768)%Z ->
  t <> (mword_of_int n : mword 16) ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int n : mword 64) = false.
Proof.
  intros Hn Hne. apply (proj2 (eq_vec_false_iff _ _)).
  intro Hc. apply Hne. apply so_sext16_inj. rewrite Hc (so_sext_lit n Hn).
  reflexivity.
Qed.

Lemma so_tdir_range : (0 <= 1 < 32768)%Z. Proof. lia. Qed.
Lemma so_tfile_range : (0 <= 2 < 32768)%Z. Proof. lia. Qed.
Lemma so_tdev_range : (0 <= 3 < 32768)%Z. Proof. lia. Qed.

(* ===================================================================== *)
(*  THE [major] BOUNDS CHECK IS ONE UNSIGNED TEST, NOT TWO                *)
(*                                                                        *)
(*  The C is [ip->major < 0 || ip->major >= NDEV]; gcc emitted an [lhu]    *)
(*  (+0x54, ZERO-extended) and a [bltu 9 <u a4] (+0x5a).  A negative       *)
(*  [short] zero-extends to at least 0x8000 > 9, so the single unsigned    *)
(*  compare decides BOTH disjuncts and the walk has one branch to price,   *)
(*  not a short-circuit pair.                                             *)
(* ===================================================================== *)

Lemma so_uint_zext16 (h : mword 16) :
  uint (zero_extend' 64 h : mword 64) = bv_unsigned h.
Proof.
  rewrite uint_unsigned.
  unfold zero_extend'.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.with_word' to_word get_word SailStdpp.Values.with_word
       autocast].
  cbn.
  unfold MachineWord.MachineWord.zero_extend, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  reflexivity.
Qed.

Lemma so_uint9 : uint (mword_of_int 9 : mword 64) = 9%Z.
Proof. vm_compute; reflexivity. Qed.

Lemma so_major_in (h : mword 16) : (bv_unsigned h <= 9)%Z ->
  zopz0zI_u (mword_of_int 9 : mword 64) (zero_extend' 64 h : mword 64) = false.
Proof.
  intro Hh. unfold zopz0zI_u. apply Z.ltb_ge.
  rewrite so_uint9 (so_uint_zext16 h). exact Hh.
Qed.

Lemma so_major_out (h : mword 16) : (9 < bv_unsigned h)%Z ->
  zopz0zI_u (mword_of_int 9 : mword 64) (zero_extend' 64 h : mword 64) = true.
Proof.
  intro Hh. unfold zopz0zI_u. apply Z.ltb_lt.
  rewrite so_uint9 (so_uint_zext16 h). exact Hh.
Qed.

(* The half of the C test the single compare absorbs -- a NEGATIVE [short]
   zero-extends to at least 0x8000 -- needs no lemma: the walk never tests
   the sign, so what it consumes is [so_major_in] on the fall-through (which
   IS "the major is a legal device index") and [so_major_out] on the arm.
   The disjunct's disappearance is a fact about the COMPILER, and it is
   discharged by there being one branch to walk. *)

(* ===================================================================== *)
(*  THE OMODE BIT CLUSTER -- AND THE THEOREM OF THIS WALK                 *)
(*                                                                        *)
(*  [omode] is an [int], so every read of it is an [lw] and what the ALU   *)
(*  sees is the SIGN EXTENSION of the stored 32-bit word.  Seven           *)
(*  instructions consume it, at four masks:                               *)
(*                                                                        *)
(*    +0x32  andi a5,a5,512     O_CREATE -- the entry split                *)
(*    +0xf6  (lw a5) beqz a5    [omode == O_RDONLY] -- the T_DIR refusal    *)
(*    +0x90  andi a4,a5,1       O_WRONLY        \  [f->readable] =          *)
(*    +0x94  xori a4,a4,1                       /    !(omode & O_WRONLY)    *)
(*    +0x9c  andi a4,a5,3       O_WRONLY|O_RDWR \  [f->writable] =          *)
(*    +0xa0  sltu a4,zero,a4    ([snez a4,a4])  /    (omode & 3) != 0       *)
(*    +0xa8  andi a5,a5,1024    O_TRUNC                                     *)
(*                                                                        *)
(*  gcc MERGED THE C's TWO WRITABLE DISJUNCTS INTO ONE MASK.  The source   *)
(*  is [(omode & O_WRONLY) || (omode & O_RDWR)] = [(omode & 1) ||          *)
(*  (omode & 2)], and the emitted code is a single [andi 3] plus a [snez]  *)
(*  -- branchless, so there is no short-circuit pair to price here either  *)
(*  (the [major] check above is the same story).                          *)
(*                                                                        *)
(*  THE CENTRAL THEOREM IS [so_pay_witness].  On any route that reaches    *)
(*  the field stores holding a T_DIR inode, the test at +0xf6 has already  *)
(*  forced [omode = O_RDONLY = 0]; at zero BOTH masks are empty, so the    *)
(*  [snez] stores a ZERO byte and [FileInvDefs.fc_wbool] of the published  *)
(*  content is [false].  That is precisely [inode_pay_alloc]'s             *)
(*  [wr = true -> ty <> T_DIR] premise, and it is where filewrite's        *)
(*  [DirView.dir_ok] obligation -- five frames up -- is actually paid.     *)
(*  The O_CREATE arm never reaches it: create was called with T_FILE, so   *)
(*  its witness is [so_tdir_zne] at a literal.                            *)
(* ===================================================================== *)

(* the word the [lw] delivers *)
Definition so_omv (om : mword 32) : mword 64 := sign_extend' 64 om.

(* what an [andi <mask>] leaves in its destination *)
Definition so_and (om : mword 32) (n : Z) : mword 64 :=
  and_vec (so_omv om) (sign_extend' 64 (mword_of_int n : mword 12)).

(* +0x90 then +0x94: the register whose low byte [sb a4,8(s2)] stores into
   [f->readable] *)
Definition so_rd_word (om : mword 32) : mword 64 :=
  xor_vec (so_and om 1) (sign_extend' 64 (mword_of_int 1 : mword 12)).

(* +0x9c then +0xa0: the register whose low byte [sb a4,9(s2)] stores into
   [f->writable].  [zero_reg] is the [snez]'s [rs1] -- the leaf reads it out
   of the capability with [sie_cap_gpr_x0]. *)
Definition so_wr_word (om : mword 32) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_u (zero_reg : mword 64) (so_and om 3))).

(* the 32 -> 64 companion of [so_sext16_inj]: the [lw]'s extension is
   injective, which is what turns the [beqz] at +0xf6 into a fact about the
   STORED word rather than about the register. *)
Lemma so_sext32_inj (x y : mword 32) :
  (sign_extend' 64 x : mword 64) = (sign_extend' 64 y : mword 64) -> x = y.
Proof.
  intros H. apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H;
    [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

Lemma so_omv_zero : so_omv (mword_of_int 0 : mword 32) = (zero_reg : mword 64).
Proof. unfold so_omv. apply bv_eq; vm_compute; reflexivity. Qed.

(* the +0xf6 [beqz a5]: the branch is taken EXACTLY at [omode = O_RDONLY],
   and that is the only thing the T_DIR route learns. *)
Lemma so_omode_eqz (om : mword 32) :
  eq_vec (so_omv om) (zero_reg : mword 64) = true ->
  om = (mword_of_int 0 : mword 32).
Proof.
  unfold so_omv. intro H. apply eq_vec_true_iff in H.
  apply so_sext32_inj. rewrite H. apply bv_eq; vm_compute; reflexivity.
Qed.

(* AT O_RDONLY EVERY MASK IS EMPTY.  Uniform in the mask, so the same lemma
   serves O_CREATE (512), O_WRONLY (1), the merged writable mask (3) and
   O_TRUNC (1024) -- there is nothing mask-specific to prove. *)
Lemma so_and_rdonly (n : Z) :
  so_and (mword_of_int 0 : mword 32) n = (mword_of_int 0 : mword 64).
Proof.
  unfold so_and, so_omv. apply bv_eq. rewrite and_vec64_unsigned.
  assert (Hz : bv_unsigned (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)
               = 0%Z) by (vm_compute; reflexivity).
  rewrite Hz Z.land_0_l. vm_compute; reflexivity.
Qed.

(* an empty mask fails its [beqz], i.e. the O_CREATE split takes the [namei]
   arm and the O_TRUNC tail is skipped *)
Lemma so_eqz_zero : eq_vec (mword_of_int 0 : mword 64) (zero_reg : mword 64) = true.
Proof. apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma so_wr_rdonly :
  so_wr_word (mword_of_int 0 : mword 32) = (mword_of_int 0 : mword 64).
Proof.
  unfold so_wr_word. rewrite (so_and_rdonly 3).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma so_wr_byte_rdonly :
  trunc8 (so_wr_word (mword_of_int 0 : mword 32)) = (mword_of_int 0 : mword 8).
Proof. rewrite so_wr_rdonly. apply bv_eq; vm_compute; reflexivity. Qed.

(* the readable byte at O_RDONLY, for completeness: [!(0 & 1)] is ONE.  The
   walk never needs its value -- nothing in the file layer is keyed on
   [f->readable] -- but it is the fact that says the published descriptor is
   a legal read fd. *)
Lemma so_rd_byte_rdonly :
  trunc8 (so_rd_word (mword_of_int 0 : mword 32)) = (mword_of_int 1 : mword 8).
Proof.
  unfold so_rd_word. rewrite (so_and_rdonly 1).
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* the sixteen-bit type test, read as the Z-level disequality [DirView] and
   [FileInvDefs] state their T_DIR conditions at.  This is the O_CREATE
   arm's whole witness: create was called with T_FILE. *)
Lemma so_tdir_zne (t : mword 16) :
  t <> (mword_of_int 1 : mword 16) -> bv_unsigned t <> T_DIR_z.
Proof.
  intros Hne Hc. apply Hne. apply bv_eq. rewrite Hc.
  unfold T_DIR_z. vm_compute. reflexivity.
Qed.

(* ...and its converse direction, which is how the else arm's branch fact
   ("the type test at +0xec fell through, so the +0xf6 test ran") reaches
   [so_pay_witness] in the vocabulary [inode_pay_alloc] speaks. *)
Lemma so_dir_forced (t : mword 16) (om : mword 32) :
  (t = (mword_of_int 1 : mword 16) -> om = (mword_of_int 0 : mword 32)) ->
  (bv_unsigned t = T_DIR_z -> om = (mword_of_int 0 : mword 32)).
Proof.
  intros H Hz. apply H. apply bv_eq. rewrite Hz.
  unfold T_DIR_z. vm_compute. reflexivity.
Qed.

(* ===== THE THEOREM =====================================================
   The published content's [f->writable] byte is the one the [snez] stored,
   and on a T_DIR inode [omode] was forced to zero -- so a WRITABLE fd is
   never a directory.  Stated in exactly [inode_pay_alloc]'s shape, so the
   walk's discharge is one [apply]. *)
Lemma so_pay_witness (om : mword 32) (ty : bv 16) (C : fcontent) :
  fc_writable C = trunc8 (so_wr_word om) ->
  (bv_unsigned ty = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
  (fc_wbool C = true -> bv_unsigned ty <> T_DIR_z).
Proof.
  intros HC Hdir Hw Hty.
  rewrite /fc_wbool HC (Hdir Hty) so_wr_byte_rdonly in Hw.
  vm_compute in Hw. discriminate Hw.
Qed.

(* ===================================================================== *)
(*  THE PUBLICATION -- R-open-1b's CHOREOGRAPHY, AS ONE GHOST STEP       *)
(*                                                                        *)
(*  Everything between the field stores and [ProcInv.proc_ofiles_repay]:  *)
(*  the two cinvs, the payload names and the [+1] inode reference that    *)
(*  never leaves.  It applies no callee contract and walks no             *)
(*  instruction, so it belongs here and not in the functor.               *)
(*                                                                        *)
(*  ==== WHERE IT RUNS, AND WHY IT IS NOT AT THE STORES ================  *)
(*                                                                        *)
(*  THE PUBLICATION CANNOT HAPPEN AT THE [sd s1,24(s2)] AT +0x88.  It     *)
(*  needs [FileInvDefs.inode_pay_alloc]'s two halves AT ONE FRACTION --   *)
(*  the parent SHORT by [Q] and a travelling share of exactly [Q] -- and  *)
(*  between ilock and iunlock the share [s] is inside the escrow, so all  *)
(*  the walk holds there is [inode_ref_short_gen kk (qi + s) qi],         *)
(*  i.e. the parent short by [s] with no [s] to pair it with.  Shedding   *)
(*  a fresh slice of the RETAINED [qi] does not fix it: the shed leaves   *)
(*  the parent short by [qi/2 + s] while the share is [qi/2], and         *)
(*  [inode_held_short]'s [qt = qi' + Q] equation is what refuses the      *)
(*  mismatch.  So the publication runs in ARM S's CONTINUATION -- after   *)
(*  [so_tail_s]'s iunlock has handed the share back -- and what the walk  *)
(*  carries across the tail is the six raw pieces below.  That is also    *)
(*  why [so_tail_s] returns [IcacheRef.inode_shr] at all: it is not a     *)
(*  courtesy, it is the other half of this lemma's input.                 *)
(*                                                                        *)
(*  THE SHARE COMES BACK GENERATION-ERASED ([SpecIunlock.v]:171), which   *)
(*  is what the middle three lines of the proof repair: name it, pin it   *)
(*  against the parent the walk kept with                                 *)
(*  [inode_ref_short_shr_gen_agree], and the payload's [ity_shot] is at   *)
(*  the generation ilock's postcondition spoke at.  (This is blocker 2's  *)
(*  answer on the ELSE arm; on the O_CREATE arm [create_locked] already   *)
(*  hands the parent over generation-NAMED.)                              *)
(*                                                                        *)
(*  THE OFF CINV IS RE-ARMED HERE TOO, and the names of BOTH cinvs go in  *)
(*  with ONE [fpay_tok_update] -- the exclusive holder installs them with *)
(*  no lock in hand, which is the whole point of the payload-names ghost. *)
(* ===================================================================== *)

Section ProofSysOpenPublish.
  (* NO STANDALONE [!icacheG Σ]: [FileInvDefs.fileG] carries both it and the
     [icfg] as field instances, and binding a second one gives two instances
     that print identically and never unify -- SpecCreate.v's banner records
     the same rule for the same reason. *)
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* the 1/2 + 1/2 join at [↦₈], which the tree has at [↦₄]
     ([RiscvPtsto.word4_pointsto_half]) and nowhere else -- and which the
     [f->ip] cell is the first 8-byte user of, the invariant's half and the
     reference's half being exactly this shape. *)
  Local Lemma so_word_half_join (a : mword 64) (w : mword 64) :
    a ↦₈{DfracOwn (1/2)} w -∗ a ↦₈{DfracOwn (1/2)} w -∗ a ↦₈ w.
  Proof.
    iIntros "H1 H2".
    iDestruct (bi.equiv_entails_1_2 _ _
                 (word_pointsto_frac_split a (1/2) (1/2) w) with "[H1 H2]")
      as "H"; [iFrame "H1 H2" |].
    iEval (rewrite Qp.div_2) in "H". iExact "H".
  Qed.

  (* ==== THE OTHER SIDE OF THE PUBLICATION: opening the fresh slot ======
     What filealloc hands over is a whole reference on an UNTYPED slot, and
     what the six field stores need is the six cells PLAIN -- [f->ip] WHOLE,
     which is the one the reference alone cannot give (the invariant keeps
     half of it, [FileInvDefs.file_fields]'s one asymmetry).  Cancelling the
     UNARMED off-cinv is what produces the other half, and there is nothing
     to refute because an unarmed body carries no disjunction: blocker 1's
     whole answer, spent in one line.

     AND IT HANDS BACK THE ENTRY'S OWN IREF UNIT.  An untyped slot's payload
     IS one unit ([FileInvDefs.file_core_none]), and the reference filealloc
     gave away carries the payload -- so opening the slot releases it.  It is
     not a windfall: the caller is about to park an inode reference in
     [f->ip], and once the type is FD_INODE the payload is [inode_pay], which
     is where that reference lives.  The entry holds exactly one unit's worth
     either way, which is what makes sys_open's whole allowance come back
     ([SpecSysOpen]'s ledger) rather than leak one per successful open. *)
  Lemma so_open_slot (E : coPset) (gf : gname) (kf : nat) (Cf : fcontent) :
    ↑(offN .@ kf) ⊆ E ->
    fc_type Cf = FD_NONE ->
    file_ref gf kf 1 Cf ={E}=∗
    ∃ (pn : fpnames) (voff : mword 32),
      ⌜off_wf voff⌝ ∗
      iref_slot ∗
      fref_tok gf kf 1 ∗ flive_tok gf kf ∗ fpay_tok gf kf 1 pn ∗
      a_ftype kf     ↦₄ fc_type Cf ∗
      a_freadable kf ↦ₘ fc_readable Cf ∗
      a_fwritable kf ↦ₘ fc_writable Cf ∗
      a_fpipe kf     ↦₈ fc_pipe Cf ∗
      a_fmajor kf    ↦₂ fc_major Cf ∗
      a_fip kf       ↦₈ fc_ip Cf ∗
      a_foff kf      ↦₄ voff.
  Proof.
    intros HE Ht.
    iIntros "(Href & Hflds & (%pn & Hnames & Hcore & Hoff) & Hlive)".
    rewrite (file_armed_none Cf Ht).
    iMod (off_hold_cancel_raw E gf kf (fp_ocv pn) HE with "Hoff") as "Hraw".
    iMod "Hraw" as "(%ipold & %voff & Hip2 & Hoffc & %Hwf)".
    iDestruct "Hflds" as "(Hty & Hrd & Hwr & Hpip & Hip1 & Hmaj)".
    iDestruct (word_pointsto_agree with "Hip2 Hip1") as %->.
    iDestruct (so_word_half_join with "Hip1 Hip2") as "Hip".
    iEval (rewrite (file_core_none 1 pn Cf Ht)) in "Hcore".
    iEval (rewrite -iref_slot_frac) in "Hcore".
    iModIntro. iExists pn, voff.
    iSplitR; [iPureIntro; exact Hwf |].
    iFrame "Hcore Href Hlive Hnames Hty Hrd Hwr Hpip Hmaj Hip Hoffc".
  Qed.

  Lemma so_publish (E : coPset) (gf : gname) (kf kk : nat) (qi s : Qp)
      (gy : gname) (inum : mword 32) (ty : bv 16) (C : fcontent)
      (pn : fpnames) (om : mword 32) (voff : mword 32) :
    ↑fileipN ⊆ E -> ↑(offN .@ kf) ⊆ E ->
    (kk < NINODE)%nat ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    fc_ip C = ientry kk ->
    (fc_type C = FD_INODE \/ fc_type C = FD_DEVICE) ->
    (* THE THEOREM OF THE WALK, in the form the two arms prove it: the
       [snez] stored [f->writable], and a T_DIR inode forced [omode = 0]. *)
    fc_writable C = trunc8 (so_wr_word om) ->
    (bv_unsigned ty = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    off_wf voff ->
    (* the parent the walk kept, short by the share it lent ilock ... *)
    inode_ref_short_gen kk (qi + s)%Qp qi icfg_dev inum gy -∗
    (* ... its PROVENANCE UNIT, which travels with the parent into the fd
       slot's [cinv] and comes back out at fileclose's withdraw (item
       7a-wire, iclaim-ledger.md §5''.3's step 6: the fd slot is one of the
       two rest homes, and it is [inode_held_short] that parks there) *)
    runit_any (bv_unsigned inum) -∗
    (* ... and that share, back from iunlock and generation-erased *)
    inode_shr kk s icfg_dev inum -∗
    ity_shot gy ty -∗
    (* the exclusive reference filealloc handed over, with the field cells
       already carrying the stored content *)
    fref_tok gf kf 1 -∗
    flive_tok gf kf -∗
    file_fields kf 1 C -∗
    fpay_tok gf kf 1 pn -∗
    (* the two cells the publisher wrote with the UNARMED cinv cancelled *)
    a_fip kf ↦₈{DfracOwn (1/2)} (ientry kk) -∗
    a_foff kf ↦₄ voff -∗
    |={E}=> file_ref gf kf 1 C.
  Proof.
    intros HEi HEo Hkk Hinb Hip Hty Hwrb Hdir Hwf.
    iIntros "Hkeep Hru Hshr #Hshot Href Hlive Hflds Hnames Hip Hoff".
    (* ---- the generation: name the returned share and pin it ---- *)
    rewrite inode_shr_gen_intro. iDestruct "Hshr" as (g2) "Hshr".
    iDestruct (inode_ref_short_shr_gen_agree with "Hkeep Hshr") as %<-.
    (* ---- the parked reference: the parent, short by exactly [s] ---- *)
    iAssert (inode_held_short (ientry kk) s) with "[Hkeep Hru]" as "Hsh".
    { iExists kk, (qi + s)%Qp, qi, inum.
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; exact Hkk|].
      iSplitR; [iPureIntro; exact Hinb|].
      iSplitR; [iPureIntro; reflexivity|]. iFrame "Hru".
      iApply (inode_ref_short_gen_forget with "Hkeep"). }
    iAssert (inode_shr_held_gen (ientry kk) s gy) with "[Hshr]" as "Hs".
    { iExists kk, inum.
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; exact Hkk|].
      iSplitR; [iPureIntro; exact Hinb|]. iExact "Hshr". }
    (* ---- the FD-type witness, and it is [so_pay_witness] ---- *)
    iMod (inode_pay_alloc E (ientry kk) s gy (fc_wbool C) ty
            (so_pay_witness om ty C Hwrb Hdir) with "Hsh Hs Hshot")
      as (gx) "Hpay".
    (* ---- the off cinv, re-armed ---- *)
    iMod (off_hold_alloc E gf kf true with "[Hip Hoff]") as (go) "Hoff".
    { iExists (ientry kk), voff. iFrame "Hip Hoff". iPureIntro. exact Hwf. }
    (* ---- ONE names update installs both ---- *)
    iMod (fpay_tok_update gf kf pn
            (MkFPNames (fp_lock pn) (fp_pipe pn) gx s gy go) with "Hnames")
      as "Hnames".
    iModIntro.
    (* ---- and that is [file_ref] ---- *)
    assert (Harm : file_armed C = true).
    { rewrite /file_armed. destruct Hty as [Ht | Ht]; rewrite Ht.
      - rewrite bool_decide_true; [reflexivity | reflexivity].
      - rewrite orb_true_r. reflexivity. }
    assert (Hnp : bool_decide (fc_type C = FD_PIPE) = false).
    { apply bool_decide_false. destruct Hty as [Ht | Ht]; rewrite Ht;
        intro Hc; by vm_compute in Hc. }
    rewrite /file_ref /file_pay /file_payload /file_core.
    iFrame "Href Hflds Hlive".
    iExists (MkFPNames (fp_lock pn) (fp_pipe pn) gx s gy go).
    iFrame "Hnames". rewrite Harm Hnp.
    assert (Hor : (bool_decide (fc_type C = FD_INODE)
                   || bool_decide (fc_type C = FD_DEVICE))%bool = true)
      by exact Harm.
    rewrite Hor. cbn [fp_icv fp_iq fp_ig fp_ocv].
    rewrite Hip. iFrame "Hpay Hoff".
  Qed.

  (* ==== THE O_TRUNC BRIDGE ============================================
     sys_open is the FIRST caller that has to REBUILD [ic_loaded] after
     itrunc: iput's itrunc is followed by [di_free], so no landed proof
     ever states the truncated record's [inode_ok].  The two lemmas below
     are that gap, and both halves of the record's own obligation are free
     because the guard at +0xae is [ip->type == T_FILE]:
     [DirView.dir_ok_not_dir] and [IcacheEscrow.dlinks_not_dir] discharge
     the directory clauses outright, and itrunc's own outputs
     ([bm_empty], the all-zero data) discharge the rest.  [di_trunc] keeps
     [type] and [nlink], so the type clause is the caller's premise
     verbatim. *)
  Lemma so_trunc_ok (logstart : Z) (dn : dinode) :
    bv_unsigned (di_type dn) <> 0 ->
    inode_ok fsc_cov logstart (di_trunc dn) bm_empty
             (fun _ => replicate BSIZE (bv_0 8)).
  Proof.
    intro Hty. rewrite /inode_ok /di_trunc. cbn [di_type di_size di_addrs].
    split_and!.
    - apply bm_empty_wf.
    - intros i _ Hlt. exfalso.
      assert (Hz : bv_unsigned (bv_0 32) = 0) by reflexivity.
      revert Hlt. cbn [di_size]. rewrite Hz.
      assert (Hb : (0 <= Z.of_nat i * Z.of_nat BSIZE)%Z) by lia. lia.
    - reflexivity.
    - exact Hty.
    - assert (Hz : bv_unsigned (bv_0 32) = 0) by reflexivity. rewrite Hz.
      unfold MAXFILE, BSIZE. lia.
    - apply bm_empty_holes. reflexivity.
    - apply inode_sized_zero.
  Qed.

  (* itrunc keeps the record's TYPE and its COUNT and zeroes the size, so
     the three record-only facts (durable-disk 2b-inode-3) ride across it:
     the enumeration by the type, the short by the count, and a directory's
     granularity vacuously at size 0. *)
  Lemma so_trunc_rec_local (dn : dinode) :
    inode_rec_local dn -> inode_rec_local (di_trunc dn).
  Proof.
    intros Hrl. apply (inode_rec_local_same_type dn (di_trunc dn) Hrl eq_refl).
    - exact (proj1 (proj2 Hrl)).
    - intros _. change (di_size (di_trunc dn)) with (bv_0 32).
      change (bv_unsigned (bv_0 32)) with 0. by exists 0.
  Qed.

  (* the open direction, one unfolding: [ic_loaded]'s [inode_addrs ∗
     ind_res] is itrunc's [inode_map]. *)
  Lemma so_loaded_open (gi : gname)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap) :
    ic_loaded fsc_fs gi fsc_cov logstart k inum dn bm -∗
    ∃ data : nat -> list (bv 8),
      ⌜inode_ok fsc_cov logstart dn bm data⌝ ∗ ⌜inode_rec_local dn⌝ ∗
      ⌜dir_ok icfg_nib dn data⌝ ∗
      dlinks fsc_fs (bv_unsigned inum) dn bm data ∗
      dinode_at gi inum dn ∗
      inode_meta (ientry k) dn ∗
      inode_map fsc_fs (ientry k) bm ∗
      inode_blocks fsc_fs bm data ∗
      (* ...and the CONTENTS HOLD (namei-pinned-lookup.md §9 W2): unlike the
         three clauses this peel discards, the hold is a RESOURCE and the
         re-seal below cannot conjure it, so it must come out here. *)
      dv_ride (bv_unsigned inum) (dv_of dn data) ∗
      fv_ride (bv_unsigned inum) (fv_of dn data) ∗
      (* ...and the era's abstract value (durable-disk 2b-inode-3): itrunc
         MOVES the record, so the walk retags it between this peel and the
         seal below ([InodeRegion.ireg_top_retag]). *)
      top_frag (fs_gamma_L fsc_fs) (bv_unsigned inum) (era_node dn bm data).
  Proof.
    iIntros "H".
    iDestruct (ic_loaded_open with "H") as (data)
      "(%Hok & %Hrl & %Hdir & %Hddix & %Hdoc & %Hduq & Hlnk & Hat & Hmeta &
        Haddr & Hind & Hblk & Hdv & Hfv & Htop)".
    (* Keep this structural: even [iFrame "%"] searches the whole goal, whose
       [inode_blocks] tail is large (171 s at this site).  The arity sweep's
       third, fourth and fifth pure conjuncts [Hddix]/[Hdoc]/[Hduq] are bound
       but NOT re-split: this lemma WEAKENS [ic_loaded], and the goal above
       carries only [inode_ok] and [dir_ok], so the two dot clauses and the
       uniqueness clause are all discarded here. *)
    iExists data.
    iSplit; [iPureIntro; exact Hok |].
    iSplit; [iPureIntro; exact Hrl |].
    iSplit; [iPureIntro; exact Hdir |].
    iSplitL "Hlnk"; [iExact "Hlnk" |].
    iSplitL "Hat"; [iExact "Hat" |].
    iSplitL "Hmeta"; [iExact "Hmeta" |].
    iSplitL "Haddr Hind".
    { rewrite /inode_map. iSplitL "Haddr"; [iExact "Haddr" | iExact "Hind"]. }
    iSplitL "Hblk"; [iExact "Hblk" |].
    iSplitL "Hdv"; [iExact "Hdv" |].
    iSplitL "Hfv"; [iExact "Hfv" | iExact "Htop"].
  Qed.

  (* ...and the close direction at itrunc's outputs. *)
  Lemma so_trunc_loaded (gi : gname)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) :
    bv_unsigned (di_type dn) <> 0 ->
    bv_unsigned (di_type dn) <> T_DIR_z ->
    inode_rec_local dn ->
    dinode_at gi inum (di_trunc dn) -∗
    inode_meta (ientry k) (di_trunc dn) -∗
    inode_map fsc_fs (ientry k) bm_empty -∗
    inode_blocks fsc_fs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
    (* THE MOVER (namei-pinned-lookup.md §9 W3, itrunc's row): itrunc zeroed
       the bytes and truncated the record, so the caller [dv_set]s the hold
       it peeled to the truncated record's own value and hands it in here.
       No delta is proved: the fragment is WHOLE, so the move is free. *)
    dv_ride (bv_unsigned inum)
            (dv_of (di_trunc dn) (fun _ => replicate BSIZE (bv_0 8))) -∗
    fv_ride (bv_unsigned inum)
            (fv_of (di_trunc dn) (fun _ => replicate BSIZE (bv_0 8))) -∗
    (* ...and the RETAGGED abstract value, at the truncated node *)
    top_frag (fs_gamma_L fsc_fs) (bv_unsigned inum)
             (era_node (di_trunc dn) bm_empty
                       (fun _ => replicate BSIZE (bv_0 8))) -∗
    ic_loaded fsc_fs gi fsc_cov logstart k inum (di_trunc dn) bm_empty.
  Proof.
    intros Hnz Hnd Hrl. iIntros "Hat Hmeta [Haddr Hind] Hblk Hdv Hfv Htop".
    assert (Hty : di_type (di_trunc dn) = di_type dn) by reflexivity.
    iApply (ic_mk_loaded fsc_fs gi fsc_cov logstart k inum (di_trunc dn) bm_empty
              (fun _ => replicate BSIZE (bv_0 8))
              (so_trunc_ok logstart dn Hnz)
              (* itrunc keeps the TYPE and zeroes the count and the size, so
                 the three record-only facts ride (durable-disk
                 2b-inode-3) *)
              (so_trunc_rec_local dn Hrl)
              (dir_ok_not_dir icfg_nib (di_trunc dn) _
                 ltac:(rewrite Hty; exact Hnd))
              (dir_dots_ix_not_dir (bv_unsigned inum) (di_trunc dn) _
                 ltac:(rewrite Hty; exact Hnd))
              (dir_orphan_clean_not_dir (di_trunc dn) _
                 ltac:(rewrite Hty; exact Hnd))
              (dir_uniq_not_dir (di_trunc dn) _
                 ltac:(rewrite Hty; exact Hnd))
              with "[] Hat Hmeta Haddr Hind Hblk Hdv Hfv Htop").
    iApply (dlinks_not_dir fsc_fs (bv_unsigned inum) (di_trunc dn) _ _).
    rewrite Hty. exact Hnd.
  Qed.

End ProofSysOpenPublish.

(* ===================================================================== *)
(*  THE FRAME CARVE: 24 slots = FIVE saved words + ONE byte buffer +      *)
(*  the omode slot + two dead ones                                        *)
(* ===================================================================== *)

Definition so_al (sp0 : mword 64) : Prop :=
  forall i, (i < 16)%nat ->
    is_aligned_paddr (Physaddr (pa_stk sp0 (22 - i)%nat)) 8 = true.

Section ProofSysOpenFrame.
  Context `{!riscvGS Σ, FSC : fscfg}.

  Lemma so_frame_carve (sp0 : mword 64) :
    stack_own (KTR := KT1) sp0 24 -∗
    ⌜so_al sp0⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 5) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 6) ↦₈[KT1] w) ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 22) 128 ∗
    (∃ w : mword 64, (pa_stk sp0 23) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 24) ↦₈[KT1] w).
  Proof.
    iIntros "H". rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                       H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 &
                       H20 & H21 & H22 & H23 & H24 & _)".
    change 128%nat with (8 * 16)%nat.
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 22 16 ltac:(lia)
                 with "[H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20
                        H21 H22]") as "[%HalP HbP]".
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
    iFrame "H1 H2 H3 H4 H5 H6 HbP H23 H24". iPureIntro. exact HalP.
  Qed.

  Lemma so_frame_join (sp0 : mword 64)
      (w1 w2 w3 w4 w5 w6 w23 w24 : mword 64) :
    so_al sp0 ->
    (pa_stk sp0 1) ↦₈[KT1] w1 -∗ (pa_stk sp0 2) ↦₈[KT1] w2 -∗
    (pa_stk sp0 3) ↦₈[KT1] w3 -∗ (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗ (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 22) 128 -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗ (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    stack_own (KTR := KT1) sp0 24.
  Proof.
    intro HalP. iIntros "H1 H2 H3 H4 H5 H6 HbP H23 H24".
    (* the [8 * n] conversion is done INSIDE the framing braces, never on the
       goal: a goal-level [change] survives into the [cbn [seq]] below, which
       then partially reduces the product and leaves the frame's own [seq]
       unreduced. *)
    iDestruct (bytes_own_slotsn (KTR := KT1) sp0 22 16 ltac:(lia) HalP with "[HbP]") as "HsP".
    { change (8 * 16)%nat with 128%nat. iExact "HbP". }
    cbn [seq].
    iDestruct "HsP" as "(K22 & K21 & K20 & K19 & K18 & K17 & K16 & K15 & K14 &
                         K13 & K12 & K11 & K10 & K9 & K8 & K7 & _)".
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
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
    iSplitL "H23"; [iExists w23; iExact "H23" |].
    iSplitL "H24"; [iExists w24; iExact "H24" |].
    done.
  Qed.

  (* THE OMODE CELL, and the only 4-byte view of a frame slot sys_open
     needs.  The lower word of slot 23 is dead (it is the [int fd] gcc never
     spilled); it rides through as an arbitrary word and comes back. *)
  Lemma so_omode_split (sp0 : mword 64) (w : mword 64) :
    (pa_stk sp0 23) ↦₈[KT1] w ⊢
    (pa_stk sp0 23) ↦₄[KT1] word_lo w ∗ (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] word_hi w.
  Proof. apply word_pointsto_split4. Qed.

  Lemma so_omode_join (sp0 : mword 64) (lo hi : bv 32) :
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    (pa_stk sp0 23) ↦₄[KT1] lo -∗ (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] hi -∗
    (pa_stk sp0 23) ↦₈[KT1] word_of_words lo hi.
  Proof. intro Hal. apply word_pointsto_join4. exact Hal. Qed.

  (* the buffer, named as bytes and back: argstr / namei / create all speak
     the [seq]-indexed byte window, not [bytes_own]. *)
  Lemma so_bytes_name (a : mword 64) (N : nat) :
    bytes_own (KTR := KT1) (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j.
  Proof. rewrite /bytes_own. exact (bb_any_named (KTR := KT1) a N). Qed.

  Lemma so_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j) ⊢ bytes_own (KTR := KT1) (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any (KTR := KT1) a N f). Qed.

  (* 128 = (k+1) + (127-k): the walkers read the NUL-terminated prefix, the
     rest rides through untouched *)
  Lemma so_buf_split (a : mword 64) (f : nat -> bv 8) (k : nat) :
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

  Lemma so_buf_join (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat,
       pa_add (pa_add a (S k)) j ↦ₘ[KT1] f (S k + j)%nat) -∗
    bytes_own (KTR := KT1) (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (so_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (so_name_bytes (pa_add a (S k)) (127 - k)%nat
                 (fun j => f (S k + j)%nat) with "H2") as "B2".
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite bytes_own_app. iFrame.
  Qed.

End ProofSysOpenFrame.

(* ===================================================================== *)
(*  +0xca .. +0xd0 : THE EPILOGUE, which all eight arms leave through.     *)
(*                                                                        *)
(*  FOUR instructions, and it restores only ra and s0 -- NOT s1, s2 or s3, *)
(*  each of which is reloaded (or never saved) by the arm itself, which is *)
(*  why all three appear here at EXISTENTIAL slot contents and as          *)
(*  register-equation premises.  a0 is already set: unlike sys_link there  *)
(*  is no [c.mv a0,a5] here, because each arm writes its own return value  *)
(*  (+0xd6/+0x106/+0x110/+0x120/+0x138 write -1; the success tail's        *)
(*  +0xc2 [c.mv a0,s3] writes the descriptor).  Everything else an arm is  *)
(*  holding rides in its own continuation premise, so this lemma has no    *)
(*  file-system parameter at all.                                          *)
(* ===================================================================== *)

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac scidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofSysOpenEpilogue.
  Context `{!riscvGS Σ, !xv6G Σ, FSC : fscfg}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma so_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64)
      (w3 w4 w5 w6 w23 w24 : mword 64) (bp : nat -> bv 8) :
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SO + 0xca)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] w3 -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    (* THE INDEX IS [b], NOT [true]: the epilogue is four PLAIN
       instructions, so every crossing it makes is a [b]-link and the
       [b]-form chain is what it can hand back.  A caller whose own
       continuation is at [true] weakens into this for free ([or_intror],
       which is what [wp_next_chain] tries). *)
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK24 Kpop Hsp0 HMsp HMthr HMs1 HMs2 HMs3 Hal.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24 Hcont".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 23 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HMsp; apply so_frm1).
    (* ===== +0xca c.ldsp ra,184(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SO + 0xca))
              (mword_of_int 23 : mword 6) Rra M (K - 24)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (soi_0ca with "Htext"). }
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (M1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
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
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp0cc : add_vec_int (mword_of_int (SO + 0xca) : mword 64) 2
                     = mword_of_int (SO + 0xcc)) by pcw.
    iEval (rewrite Hpp0cc) in "Hpc".
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 22 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply so_frm2).
    (* ===== +0xcc c.ldsp s0,176(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SO + 0xcc))
              (mword_of_int 22 : mword 6) Rs0 M1 (K - 24)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf2]").
    { iApply (soi_0cc with "Htext"). }
    { iEval (rewrite Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    set (M2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> M1).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
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
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp0ce : add_vec_int (mword_of_int (SO + 0xcc) : mword 64) 2
                     = mword_of_int (SO + 0xce)) by pcw.
    iEval (rewrite Hpp0ce) in "Hpc".
    (* ===== +0xce c.addi16sp sp,192 : the pop ===== *)
    assert (Hwv : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6)))
                  = sp0)
      by (rewrite HM2sp; apply so_pop).
    assert (Hpop : (M2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6)))) 24)
      by (rewrite Hwv HM2sp; reflexivity).
    iDestruct (so_name_bytes (pa_stk sp0 22) 128 bp with "HbP") as "BP".
    iDestruct (so_frame_join sp0 _ _ w3 w4 w5 w6 w23 w24 Hal
                 with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 BP H23 H24") as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SO + 0xce))
              (mword_of_int 12 : mword 6) M2 (K - 24)%nat 24 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (soi_0ce with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (M3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6))))]> M2).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp0d0 : add_vec_int (mword_of_int (SO + 0xce) : mword 64) 2
                     = mword_of_int (SO + 0xd0)) by pcw.
    iEval (rewrite Hpp0d0) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    (* ===== +0xd0 c.ret ===== *)
    iApply (wp_cret_s_sconf (mword_of_int (SO + 0xd0)) Rra M3 K b
              ltac:(nz) with "Hcg Hpc []").
    { iApply (soi_0d0 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HM3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE HANDOVER ===== *)
    assert (Hwv' : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 12 : mword 6)))
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
    assert (Hfin : so_thr m M3).
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

End ProofSysOpenEpilogue.
