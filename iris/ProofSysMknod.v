(* ProofSysMknod.v -- sys_mknod over the SIE-agnostic sconf world.

     uint64 sys_mknod(void) {
       struct inode *ip;  char path[MAXPATH];  int major, minor;
       begin_op();
       argint(1, &major);
       argint(2, &minor);
       if ((argstr(0, path, MAXPATH)) < 0 ||
           (ip = create(path, T_DEVICE, major, minor)) == 0) {
         end_op(); return -1; }
       iunlockput(ip);  end_op();  return 0;
     }

   96 bytes, 32 instructions, TWO arms that leave through one epilogue.
   Read off CodeSysMknod.v:

     +0x00  c.addi16sp sp,-160      the twenty-slot frame
     +0x02  c.sdsp ra,152(sp)       slot 1
     +0x04  c.sdsp s0,144(sp)       slot 2
     +0x06  c.addi4spn s0,sp,160    s0 = the ENTRY sp
     +0x08  jal begin_op
     +0x0c  addi a1,s0,-148 ; c.li a0,1 ; jal argint      (&major)
     +0x16  addi a1,s0,-152 ; c.li a0,2 ; jal argint      (&minor)
     +0x20  li a2,128 ; addi a1,s0,-144 ; c.li a0,0 ; jal argstr
     +0x2e  bltz a0 -> +0x58        ARM A: the string did not fetch
     +0x32  lh a3,-152(s0)          minor, SIGN-extended
     +0x36  lh a2,-148(s0)          major, SIGN-extended
     +0x3a  c.li a1,3 ; addi a0,s0,-144
     +0x40  jal create              (path, T_DEVICE, major, minor)
     +0x44  c.beqz a0 -> +0x58      ARM B: create failed
     +0x46  jal iunlockput          a0 IS STILL create's return
     +0x4a  jal end_op
     +0x4e  c.li a0,0
     +0x50  THE EPILOGUE: ldsp ra / ldsp s0 / addi16sp / ret
     +0x58  jal end_op ; c.li a0,-1 ; c.j +0x50     THE SHARED "-1" TAIL

   THE FRAME IS sys_mkdir'S PLUS ONE OCCUPIED SLOT.  Twenty slots: ra (1),
   s0 (2), the [char path[128]] local in slots 18 down to 3 (based at
   [s0-144], which is NOT the pushed sp here), **the two [int] locals
   SHARING slot 19** -- [minor] in its low word at [s0-152] and [major] in
   its high word at [s0-148] -- and slot 20 as padding that nothing ever
   addresses.  As in sys_mkdir, [ip] never leaves a0, so beyond ra and s0
   nothing is saved and [mn_thr] excludes exactly two registers.

   TWO C LOCALS IN ONE SLOT, AND A HALFWORD READ OUT OF EACH.  argint
   writes a 4-byte cell; create's parameters are [short], so the [lh]s at
   +0x32 / +0x36 read the LOW HALFWORD of each [int].  Slot 19 is therefore
   carved twice -- [InstrBytes.word_pointsto_split4] into the two [int]
   cells, then [word4_pointsto_split2 (KTR := KT1)] (this file's, see its banner) into
   halves -- and rejoined on the way to the epilogue.  This is sys_close's
   "a C local taken by address" one level further down.

   THE C SHORT-CIRCUIT IS ONE BLOCK, ENTERED TWICE, exactly as in
   sys_mkdir: the [bltz] at +0x2e and the [c.beqz] at +0x44 both target
   +0x58 with nothing in between, so [mn_m1_tail] takes no register-restore
   premise.

   ==== THE RESOURCE PLAN ================================================

   [proc_priv] is threaded WHOLE, with two borrows.  The pid quarter goes
   out to begin_op / iunlockput / end_op and comes straight back
   ([ProcInv.proc_priv_bare_acc]); the trapframe quarter AND the page go out to
   each argint and come straight back ([ProcInv.proc_priv_tf], ProofSysExit's
   move).  create takes the block whole and returns it at the same record;
   argstr returns it at [upd_upt V P'], and that page-table growth is the
   only record change anywhere in this function.

   THE LOCKED INODE create HANDS BACK is [SpecCreate.create_locked], which
   is [SpecIunlockput]'s precondition verbatim -- destructed once at +0x46
   and handed straight over.

   ==== THE COMPLEMENT IS DROPPED, NOT THREADED ==========================

   As in sys_mkdir, and for the same reason: create does not take the pair
   at all, so threading it would demand a transport across create's park.
   The walk drops it at the top and re-mints it per callee (begin_op,
   iunlockput, end_op) and once for the caller's continuation.  argint and
   argstr do not take it either. *)
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
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn StackBytes.
Require Import CalleeSaved KernelText.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import SpecPanic.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import UserPtTree.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import ProofKforkParts.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIunlockput.
Require Import SpecArgint.
Require Import SpecCreate.
Require Import CodeSysMknod.
Require Import SpecSysMknod.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

(* a failing tactic in a WP over [proc_priv] otherwise spends tens of
   minutes FORMATTING the goal -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

Notation MN := KernelSyms.sys_mknod (only parsing).

(* ===================================================================== *)
(*  THE PURE SIDE-CONDITIONS, as closed top-level facts (never run [lia]  *)
(*  or [vm_compute] inside a whole-function context).                     *)
(* ===================================================================== *)

(* the TWO registers this frame moves: sp and s0 (the frame pointer).
   Everything else callee-saved rides straight through, and it is stated
   POSITIVELY -- the two exceptions are exactly the two the code writes,
   each accounted for by its own equation. *)
Definition mn_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma mn_thr_refl (m : regfile) : mn_thr m m.
Proof. intros c _ _ _. reflexivity. Qed.

Lemma mn_thr_trans (m M P : regfile) : mn_thr m M -> mn_thr M P -> mn_thr m P.
Proof.
  intros H1 H2 c Hc N2 N8. rewrite (H2 c Hc N2 N8). exact (H1 c Hc N2 N8).
Qed.

Definition mn_sp (sp0 : mword 64) (M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk sp0 20.

(* -160 / +160, both a [c.addi16sp] (55 is -9 in a 6-bit field, x16). *)
Lemma mn_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 54 : mword 6)))
  = pa_stk X 20.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma mn_pop (X : mword 64) :
  add_vec (pa_stk X 20) (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,160] -- the frame pointer, back at the entry sp. *)
Lemma mn_fp (X : mword 64) :
  add_vec (pa_stk X 20) (sign_extend' 64 (caddi4spn_imm (mword_of_int 40 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi a1,s0,-144] off the frame pointer (which IS the entry sp) is the
   base of the path buffer -- slot 18, NOT the pushed sp: slot 19 holds the
   two [int] locals and slot 20 is padding. *)
Lemma mn_buf (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3952 : mword 12)) = pa_stk X 18.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi a1,s0,-152] is [&minor], the LOW word of slot 19; [addi a1,s0,-148]
   is [&major], its HIGH word.  The second is not a slot address at all --
   it is four bytes into one -- so it needs ProofSysExit's [sex_addr_n]
   shape rather than [stk_push]. *)
Lemma mn_min (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3944 : mword 12)) = pa_stk X 19.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma mn_maj (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3948 : mword 12))
  = pa_add (pa_stk X 19) 4.
Proof.
  unfold pa_stk, pa_add, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* the c.sdsp / c.ldsp displacements off the pushed sp *)
Lemma mn_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (bv_wrap 64 (uint (mword_of_int (- (8 * Z.of_nat 20)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 20) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite pa_stk_off2. apply f_equal. exact H.
Qed.

Lemma mn_frm1 (X : mword 64) :
  add_vec (pa_stk X 20)
    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply mn_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma mn_frm2 (X : mword 64) :
  add_vec (pa_stk X 20)
    (zero_extend' 64 (concat_vec (mword_of_int 18 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply mn_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_sys_mknod's single premise, turned into every bound the four callees
   and the [sie_cap_gpr] pop want. *)
Lemma mn_kb (K : nat) : (K_sys_mknod <= K)%nat ->
  (K_create <= K - 20)%nat /\ (argstr_stack <= K - 20)%nat /\
  (K_begin_op <= K - 20)%nat /\ (K_end_op <= K - 20)%nat /\
  (K_iunlockput <= K - 20)%nat /\ (18 <= K - 20)%nat /\
  (20 <= K)%nat /\ ((K - 20) + 20 = K)%nat.
Proof.
  
  intro H. split_and!; lia.
Qed.

(* the syscall argument index is in range, and [i = 0] is what a0 holds *)
Lemma mn_arg0_lt : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma mn_arg1_lt : (1 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma mn_arg2_lt : (2 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma mn_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma mn_maxpath_lt : (Z.of_nat 128 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma mn_plen_lt (k : nat) : (k < 128)%nat -> (Z.of_nat k < 2 ^ 31)%Z.
Proof. intro H. lia. Qed.

Lemma mn_len_range (k : nat) : (k < 128)%nat -> (0 <= Z.of_nat k < 2 ^ 31)%Z.
Proof.
  intro Hk.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* THE [bltz] AT +0x1a, decided.  argstr's answer is [fetchstr_ret]'s
   disjunction, so the branch turns on the SIGN of a value that is either
   [-1] or a length below 128.  ProofSysChdir's cluster, restated here
   rather than imported (a whole-function proof file is not a dependency
   any other one may take). *)
Lemma mn_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
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

Lemma mn_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (mn_sint_moi z Hz). lia.
Qed.

Lemma mn_m1_neg :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

(* create's live type premise at [ty := T_DEVICE] *)
Lemma mn_tdev_nz : bv_unsigned SpecCreate.T_DEVICE <> 0.
Proof. vm_compute. discriminate. Qed.

(* ===================================================================== *)
(*  THE FRAME: sixteen of the eighteen slots ARE [char path[128]].        *)
(* ===================================================================== *)

(* Opts back out of the [word4_pointsto] seal: this file destructs it directly.
   Local, so nothing above inherits the transparency. *)
Local Typeclasses Transparent word4_pointsto.

Section ProofSysMknodFrame.
  Context `{!riscvGS Σ, FSC : fscfg}.

  (* THE CARVE.  Sixteen of the twenty slots are [char path[128]] -- slot 18
     (the buffer's base, [s0-144]) down to slot 3 -- and the four that are
     not are ra (1), s0 (2), the two [int] locals sharing slot 19, and the
     padding slot 20 (the pushed sp itself, which nothing addresses). *)
  Lemma mn_frame_carve (sp0 : mword 64) :
    stack_own (KTR := KT1) sp0 20 -∗
    ⌜forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 19) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 20) ↦₈[KT1] w) ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 18) 128.
  Proof.
    iIntros "H". rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                       H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 &
                       H20 & _)".
    change 128%nat with (8 * 16)%nat.
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 18 16 ltac:(lia)
                 with "[H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16
                        H17 H18]") as "[%Hal Hb]".
    { cbn [seq].
      iSplitL "H18"; [iExact "H18" |]. iSplitL "H17"; [iExact "H17" |].
      iSplitL "H16"; [iExact "H16" |]. iSplitL "H15"; [iExact "H15" |].
      iSplitL "H14"; [iExact "H14" |]. iSplitL "H13"; [iExact "H13" |].
      iSplitL "H12"; [iExact "H12" |]. iSplitL "H11"; [iExact "H11" |].
      iSplitL "H10"; [iExact "H10" |]. iSplitL "H9"; [iExact "H9" |].
      iSplitL "H8"; [iExact "H8" |]. iSplitL "H7"; [iExact "H7" |].
      iSplitL "H6"; [iExact "H6" |]. iSplitL "H5"; [iExact "H5" |].
      iSplitL "H4"; [iExact "H4" |]. iSplitL "H3"; [iExact "H3" |].
      done. }
    iFrame "H1 H2 H19 H20 Hb". iPureIntro. exact Hal.
  Qed.

  Lemma mn_frame_join (sp0 : mword 64) (w1 w2 w19 w20 : mword 64) :
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true) ->
    (pa_stk sp0 1) ↦₈[KT1] w1 -∗ (pa_stk sp0 2) ↦₈[KT1] w2 -∗
    (pa_stk sp0 19) ↦₈[KT1] w19 -∗ (pa_stk sp0 20) ↦₈[KT1] w20 -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 18) 128 -∗
    stack_own (KTR := KT1) sp0 20.
  Proof.
    intro Hal. iIntros "H1 H2 H19 H20 Hb".
    change 128%nat with (8 * 16)%nat.
    iDestruct (bytes_own_slotsn (KTR := KT1) sp0 18 16 ltac:(lia) Hal with "Hb") as "Hs".
    cbn [seq].
    iDestruct "Hs" as "(K18 & K17 & K16 & K15 & K14 & K13 & K12 & K11 & K10 &
                        K9 & K8 & K7 & K6 & K5 & K4 & K3 & _)".
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iSplitL "H1"; [iExists w1; iExact "H1" |].
    iSplitL "H2"; [iExists w2; iExact "H2" |].
    iSplitL "K3"; [iExact "K3" |]. iSplitL "K4"; [iExact "K4" |].
    iSplitL "K5"; [iExact "K5" |]. iSplitL "K6"; [iExact "K6" |].
    iSplitL "K7"; [iExact "K7" |]. iSplitL "K8"; [iExact "K8" |].
    iSplitL "K9"; [iExact "K9" |]. iSplitL "K10"; [iExact "K10" |].
    iSplitL "K11"; [iExact "K11" |]. iSplitL "K12"; [iExact "K12" |].
    iSplitL "K13"; [iExact "K13" |]. iSplitL "K14"; [iExact "K14" |].
    iSplitL "K15"; [iExact "K15" |]. iSplitL "K16"; [iExact "K16" |].
    iSplitL "K17"; [iExact "K17" |]. iSplitL "K18"; [iExact "K18" |].
    iSplitL "H19"; [iExists w19; iExact "H19" |].
    iSplitL "H20"; [iExists w20; iExact "H20" |].
    done.
  Qed.

  (* the buffer, as bytes and back: argstr / create both speak the
     [seq]-indexed byte window, not [bytes_own] *)
  Lemma mn_bytes_name (a : mword 64) (N : nat) :
    bytes_own (KTR := KT1) (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j.
  Proof. rewrite /bytes_own. exact (bb_any_named (KTR := KT1) a N). Qed.

  Lemma mn_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j) ⊢ bytes_own (KTR := KT1) (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any (KTR := KT1) a N f). Qed.

  (* 128 = (k+1) + (127-k): create reads the NUL-terminated prefix, the rest
     rides through untouched *)
  Lemma mn_buf_split (a : mword 64) (f : nat -> bv 8) (k : nat) :
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

  Lemma mn_buf_join (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat,
       pa_add (pa_add a (S k)) j ↦ₘ[KT1] f (S k + j)%nat) -∗
    bytes_own (KTR := KT1) (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (mn_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (mn_name_bytes (pa_add a (S k)) (127 - k)%nat
                 (fun j => f (S k + j)%nat) with "H2") as "B2".
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite bytes_own_app. iFrame.
  Qed.

End ProofSysMknodFrame.


(* ===================================================================== *)
(*  THE HALFWORD LAYER: a 4-byte cell split into its two halves.          *)
(*                                                                        *)
(*  argint writes an [int] ([↦₄]); create's [short major, short minor]    *)
(*  are read back by the [lh]s at +0x32 / +0x36, whose leaf                *)
(*  ([WpSmodeHalf.wp_lh_s_sconf (kt := KT1) (ktd := KT0)]) takes a [↦₂].  The tree has the 8 -> 4  *)
(*  pair ([InstrBytes.word_pointsto_split4] / [_join4]) and NOT the 4 -> 2 *)
(*  one, because every other [lh] in the kernel reads an inode field,      *)
(*  which [inode_meta] already hands out at [↦₂].  This is the twin, in    *)
(*  the same [nth_byte]/[assemble_bytes] style so that every obligation is *)
(*  one [nth_byte_assemble_len] and no bit-shifting.  It is stated here    *)
(*  rather than in InstrBytes.v because sys_mknod is its only consumer     *)
(*  today; hoist it the moment a second one appears.                      *)
(* ===================================================================== *)

Definition hw_lo (w : mword 32) : mword 16 :=
  Z_to_bv 16 (assemble_bytes [nth_byte w 0; nth_byte w 1]).
Definition hw_hi (w : mword 32) : mword 16 :=
  Z_to_bv 16 (assemble_bytes [nth_byte w 2; nth_byte w 3]).
Definition hw_join (lo hi : mword 16) : mword 32 :=
  Z_to_bv 32 (assemble_bytes [nth_byte lo 0; nth_byte lo 1;
                              nth_byte hi 0; nth_byte hi 1]).

Local Lemma nb_assemble2 (bs : list (bv 8)) (j : nat) :
  length bs = 2%nat -> (j < 2)%nat ->
  nth_byte (Z_to_bv 16 (assemble_bytes bs) : bv 16) j = bs !!! j.
Proof.
  intros Hlen Hj. apply nth_byte_assemble_len; rewrite Hlen; [| exact Hj].
  change (Z.of_N 16) with 16%Z. change (Z.of_nat 2) with 2%Z. lia.
Qed.

Local Lemma nb_assemble4' (bs : list (bv 8)) (j : nat) :
  length bs = 4%nat -> (j < 4)%nat ->
  nth_byte (Z_to_bv 32 (assemble_bytes bs) : bv 32) j = bs !!! j.
Proof.
  intros Hlen Hj. apply nth_byte_assemble_len; rewrite Hlen; [| exact Hj].
  change (Z.of_N 32) with 32%Z. change (Z.of_nat 4) with 4%Z. lia.
Qed.

Lemma nth_byte_hw_lo (w : mword 32) (j : nat) :
  (j < 2)%nat -> nth_byte (hw_lo w) j = nth_byte w j.
Proof.
  intro Hj. unfold hw_lo. rewrite nb_assemble2; [| reflexivity | exact Hj].
  destruct j as [|[|]]; cbn; first [reflexivity | lia].
Qed.

Lemma nth_byte_hw_hi (w : mword 32) (j : nat) :
  (j < 2)%nat -> nth_byte (hw_hi w) j = nth_byte w (2 + j).
Proof.
  intro Hj. unfold hw_hi. rewrite nb_assemble2; [| reflexivity | exact Hj].
  destruct j as [|[|]]; cbn; first [reflexivity | lia].
Qed.

Lemma nth_byte_hw_join_lo (lo hi : mword 16) (j : nat) :
  (j < 2)%nat -> nth_byte (hw_join lo hi) j = nth_byte lo j.
Proof.
  intro Hj. unfold hw_join. rewrite nb_assemble4'; [| reflexivity | lia].
  destruct j as [|[|]]; cbn; first [reflexivity | lia].
Qed.

Lemma nth_byte_hw_join_hi (lo hi : mword 16) (j : nat) :
  (j < 2)%nat -> nth_byte (hw_join lo hi) (2 + j) = nth_byte hi j.
Proof.
  intro Hj. unfold hw_join. rewrite nb_assemble4'; [| reflexivity | lia].
  destruct j as [|[|]]; cbn; first [reflexivity | lia].
Qed.

(* ---- the alignment halves, the 4/2 twins of [aligned8_aligned4] ---- *)
Local Lemma z_rem4_rem2 (u : Z) : (0 <= u)%Z -> Z.rem u 4 = 0%Z -> Z.rem u 2 = 0%Z.
Proof.
  intros H0 H4.
  rewrite (Z.rem_mod_nonneg u 4 H0 ltac:(lia)) in H4.
  rewrite (Z.rem_mod_nonneg u 2 H0 ltac:(lia)).
  apply Z.mod_divide in H4; [| lia]. apply Z.mod_divide; [lia|].
  destruct H4 as [k Hk]. exists (2 * k)%Z. lia.
Qed.

Local Lemma z_rem4_rem2_hi (u : Z) :
  (0 <= u)%Z -> Z.rem u 4 = 0%Z -> Z.rem (u + 2) 2 = 0%Z.
Proof.
  intros H0 H4.
  rewrite (Z.rem_mod_nonneg u 4 H0 ltac:(lia)) in H4.
  rewrite (Z.rem_mod_nonneg (u + 2) 2 ltac:(lia) ltac:(lia)).
  apply Z.mod_divide in H4; [| lia]. apply Z.mod_divide; [lia|].
  destruct H4 as [k Hk]. exists (2 * k + 1)%Z. lia.
Qed.

Local Lemma z_rem4_no_wrap (u : Z) :
  (0 <= u < 18446744073709551616)%Z -> Z.rem u 4 = 0%Z ->
  (u + 2 < 18446744073709551616)%Z.
Proof.
  intros H0 H4.
  rewrite (Z.rem_mod_nonneg u 4 ltac:(lia) ltac:(lia)) in H4.
  apply Z.mod_divide in H4; [| lia]. destruct H4 as [k Hk]. lia.
Qed.

Lemma pa_add_2_unsigned (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 4 = true ->
  bv_unsigned (pa_add a 2) = (bv_unsigned a + 2)%Z.
Proof.
  unfold is_aligned_paddr. rewrite uint_unsigned. intro H4.
  apply Z.eqb_eq in H4.
  pose proof (bv_unsigned_in_range _ a) as [Hlo Hhi].
  unfold bv_modulus in Hhi. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in Hhi.
  pose proof (z_rem4_no_wrap _ (conj Hlo Hhi) H4) as Hnw.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', SailStdpp.Values.with_word, to_word, get_word,
    MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (H2 : bv_unsigned (mword_of_int (Z.of_nat 2) : mword 64) = 2%Z)
    by (vm_compute; reflexivity).
  rewrite H2. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  split; [apply Z.add_nonneg_nonneg; [exact Hlo | discriminate] | exact Hnw].
Qed.

Lemma aligned4_aligned2 (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 4 = true -> is_aligned_paddr (Physaddr a) 2 = true.
Proof.
  unfold is_aligned_paddr. rewrite !uint_unsigned.
  pose proof (bv_unsigned_in_range _ a) as [Hlo _].
  intro H4. apply Z.eqb_eq in H4. apply Z.eqb_eq.
  apply (z_rem4_rem2 _ Hlo H4).
Qed.

Lemma aligned4_aligned2_hi (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 4 = true ->
  is_aligned_paddr (Physaddr (pa_add a 2)) 2 = true.
Proof.
  intro H4. pose proof (pa_add_2_unsigned a H4) as Hpa.
  revert H4. unfold is_aligned_paddr. rewrite !uint_unsigned. rewrite Hpa.
  pose proof (bv_unsigned_in_range _ a) as [Hlo _].
  intro H4. apply Z.eqb_eq in H4. apply Z.eqb_eq.
  apply (z_rem4_rem2_hi _ Hlo H4).
Qed.

Section HalfWords.
  Context `{!riscvGS Σ, FSC : fscfg}.
  Context `{KTR : !CurKtier}.

  Local Lemma big_sepL_seq_shift2 (P : nat -> iProp Σ) (o n : nat) :
    ([∗ list] jj ∈ seq o n, P jj) ⊣⊢ ([∗ list] jj ∈ seq 0 n, P ((o + jj)%nat)).
  Proof.
    assert (Hf : seq o n = (Nat.add o) <$> seq 0 n).
    { rewrite fmap_add_seq. by rewrite Nat.add_0_r. }
    rewrite Hf big_sepL_fmap. reflexivity.
  Qed.

  Lemma word4_pointsto_split2 (a : Arch.pa) (dq : dfrac) (w : mword 32) :
    a ↦₄{dq} w ⊢ a ↦₂{dq} hw_lo w ∗ (pa_add a 2) ↦₂{dq} hw_hi w.
  Proof.
    iIntros "[%Hal Hbs]".
    assert (Hs : seq 0 4 = (seq 0 2 ++ seq 2 2)%list) by reflexivity.
    rewrite Hs big_sepL_app.
    iDestruct "Hbs" as "[Hlo Hhi]".
    iSplitL "Hlo".
    - iSplit; [iPureIntro; by apply aligned4_aligned2|].
      iApply (big_sepL_mono with "Hlo").
      intros k jj Hk. apply lookup_seq in Hk as [-> Hlt].
      rewrite nth_byte_hw_lo; [reflexivity | lia].
    - iSplit; [iPureIntro; by apply aligned4_aligned2_hi|].
      iEval (rewrite (big_sepL_seq_shift2 _ 2 2)) in "Hhi".
      iApply (big_sepL_mono with "Hhi").
      intros k jj Hk. apply lookup_seq in Hk as [-> Hlt].
      rewrite pa_add_add. rewrite nth_byte_hw_hi; [reflexivity | lia].
  Qed.

  Lemma word4_pointsto_join2 (a : Arch.pa) (dq : dfrac) (lo hi : mword 16) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    a ↦₂{dq} lo -∗ (pa_add a 2) ↦₂{dq} hi -∗ a ↦₄{dq} hw_join lo hi.
  Proof.
    iIntros (Hal) "[_ Hlo] [_ Hhi]".
    iSplit; [done|].
    assert (Hs : seq 0 4 = (seq 0 2 ++ seq 2 2)%list) by reflexivity.
    rewrite Hs big_sepL_app.
    iSplitL "Hlo".
    - iApply (big_sepL_mono with "Hlo").
      intros k jj Hk. apply lookup_seq in Hk as [-> Hlt].
      rewrite nth_byte_hw_join_lo; [reflexivity | lia].
    - rewrite (big_sepL_seq_shift2 _ 2 2).
      iApply (big_sepL_mono with "Hhi").
      intros k jj Hk. apply lookup_seq in Hk as [-> Hlt].
      rewrite pa_add_add. rewrite nth_byte_hw_join_hi; [reflexivity | lia].
  Qed.

End HalfWords.

(* ===================================================================== *)
(*  +0x50 .. +0x56 : THE EPILOGUE, which both arms leave through.         *)
(*                                                                        *)
(*  It touches no resource but the frame: [a0] already holds the result,  *)
(*  and what is left is the two [c.ldsp]s, the pop and the [c.ret].       *)
(*  Everything else an arm is holding rides in its own continuation        *)
(*  premise, which is why this lemma has no file-system parameter at all. *)
(* ===================================================================== *)

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac scidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofSysMknodEpilogue.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, FSC : fscfg}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma mn_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64)
      (w19 w20 : mword 64) (bf : nat -> bv 8) :
    (20 <= K)%nat -> ((K - 20) + 20 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    mn_sp sp0 M -> mn_thr m M ->
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true) ->
    sie_cap_gpr KT1 M (K - 20) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (MN + 0x50)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 19) ↦₈[KT1] w19 -∗
    (pa_stk sp0 20) ↦₈[KT1] w20 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 18) jj ↦ₘ[KT1] bf jj) -∗
    (* THE INDEX IS [b], NOT [true], and it has to be: the epilogue is four
       PLAIN instructions, so every crossing it makes is a [b]-link and the
       [b]-form chain is what it can hand back (ProofSysChdir's [sc_epilogue]
       paid for this rule).  A caller whose own continuation is at [true]
       weakens into this for free. *)
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK18 Kpop Hsp0 HMsp HMthr Hal.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hf19 Hf20 Hbuf Hcont".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HMsp; apply mn_frm1).
    (* ===== +0x38 c.ldsp ra,136(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (MN + 0x50))
              (mword_of_int 19 : mword 6) Rra M (K - 20)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (smni_50 with "Htext"). }
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (M1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HM1sp : mn_sp sp0 M1)
      by (rewrite /mn_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1thr : mn_thr m M1).
    { intros c Hc N2 N8. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8). }
    assert (Hpp3a : add_vec_int (mword_of_int (MN + 0x50) : mword 64) 2
                    = mword_of_int (MN + 0x52)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 18 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply mn_frm2).
    (* ===== +0x3a c.ldsp s0,128(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (MN + 0x52))
              (mword_of_int 18 : mword 6) Rs0 M1 (K - 20)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf2]").
    { iApply (smni_52 with "Htext"). }
    { iEval (rewrite Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    set (M2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> M1).
    assert (HM2sp : mn_sp sp0 M2)
      by (rewrite /mn_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1ra | nz]).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2thr : mn_thr m M2).
    { intros c Hc N2 N8. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8). }
    assert (Hpp3c : add_vec_int (mword_of_int (MN + 0x52) : mword 64) 2
                    = mword_of_int (MN + 0x54)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x54 c.addi16sp sp,160 : the pop ===== *)
    assert (Hwv : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))
                  = sp0)
      by (rewrite HM2sp; apply mn_pop).
    assert (Hpop : (M2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))) 20)
      by (rewrite Hwv HM2sp; reflexivity).
    iDestruct (mn_name_bytes (pa_stk sp0 18) 128 bf with "Hbuf") as "Hbytes".
    iDestruct (mn_frame_join sp0 _ _ _ _ Hal with "Hf1 Hf2 Hf19 Hf20 Hbytes")
      as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (MN + 0x54))
              (mword_of_int 10 : mword 6) M2 (K - 20)%nat 20 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (smni_54 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (M3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6))))]> M2).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp3e : add_vec_int (mword_of_int (MN + 0x54) : mword 64) 2
                    = mword_of_int (MN + 0x56)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    (* ===== +0x3e c.ret ===== *)
    iApply (wp_cret_s_sconf (mword_of_int (MN + 0x56)) Rra M3 K b
              ltac:(nz) with "Hcg Hpc []").
    { iApply (smni_56 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HM3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE HANDOVER ===== *)
    assert (Hwv' : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))
                   = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite Hwv; exact Hsp0).
    assert (Csp : (M3 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /M3 upd_eq; exact Hwv').
    assert (Cs0 : (M3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2a0 | nz]).
    assert (Hfin : mn_thr m M3).
    { intros c Hc N2 N8. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8). }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! M3 with "[%] [%] Hcg Hpc").
    { unfold callee_saved. split_and!;
        [ exact Csp | exact Cs0
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx | apply Hfin; scidx ]. }
    { exact HM3a0. }
  Qed.

End ProofSysMknodEpilogue.

(* ===================================================================== *)
(*  THE FUNCTOR.  Everything from here down applies a callee's contract,   *)
(*  so it lives inside the module the seal instantiates.                   *)
(* ===================================================================== *)
Module SysMknodProof (BeginOp : BEGIN_OP) (Argint : ARGINT) (Argstr : ARGSTR)
                     (Create : CREATE) (Iunlockput : IUNLOCKPUT) (EndOp : END_OP)
  : SYSMKNOD.

(* ===================================================================== *)
(*  +0x58 .. +0x5e : THE SHARED "-1" TAIL.                                *)
(*                                                                        *)
(*  end_op, [c.li a0,-1], and the [c.j] back into the epilogue.  BOTH     *)
(*  arms of the C-level [||] reach it and they reach it DIRECTLY -- the    *)
(*  [bltz] at +0x1a and the [c.beqz] at +0x2c both target +0x40, with no   *)
(*  intervening restore, which is why this lemma takes no register premise *)
(*  beyond the two the epilogue below it wants.                           *)
(* ===================================================================== *)
Section ProofSysMknodM1Tail.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, FSC : fscfg}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma mn_m1_tail `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (dev : mword 32)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w19 w20 : mword 64)
      (bf : nat -> bv 8) (Vpr : pprivate) :
    (K_end_op <= K - 20)%nat -> (20 <= K)%nat -> ((K - 20) + 20 = K)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    mn_sp sp0 M -> mn_thr m M ->
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true) ->
    sie_cap_gpr KT1 M (K - 20) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (MN + 0x58)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev fsc_cov) -∗
    log_ctx g bn gfs fsc_cov fsc_logst dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 19) ↦₈[KT1] w19 -∗
    (pa_stk sp0 20) ↦₈[KT1] w20 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 18) jj ↦ₘ[KT1] bf jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr jx) pidv Vpr -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKeo HK18 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf19 Hf20 Hbuf Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x40 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (MN + 0x58)) Rra
              (mword_of_int 2091500 : mword 21) M (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (smni_58 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (MN + 0x58) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (MN + 0x58) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091500 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (MN + 0x58) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : mn_sp sp0 M1)
      by (rewrite /mn_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1thr : mn_thr m M1).
    { intros c Hc N2 N8. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs fsc_cov fsc_logst dev u pidv dq M1 (K - 20)%nat eb b lks
              Vpr HKeo Hgeom Hj Hgl ltac:(lkbelow)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc5c : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (MN + 0x5c)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpc5c) in "Hpc".
    assert (Heosp : mn_sp sp0 meo).
    { rewrite /mn_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heothr : mn_thr m meo).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8). }
    (* ===== +0x44 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (MN + 0x5c)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 20)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (smni_5c with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : mn_sp sp0 P1)
      by (rewrite /mn_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1thr : mn_thr m P1).
    { intros c Hc N2 N8. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8). }
    assert (Hpp5e : add_vec_int (mword_of_int (MN + 0x5c) : mword 64) 2
                    = mword_of_int (MN + 0x5e)) by pcw.
    iEval (rewrite Hpp5e) in "Hpc".
    (* ===== +0x46 c.j +0x38 ===== *)
    iApply (wp_cj_s_sconf (CID := CID3) (mword_of_int (MN + 0x5e))
              (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")))
              P1 (K - 20)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (smni_5e with "Htext"). }
    iIntros (CID4 Hq4). iNext. iIntros "Hcg Hpc".
    assert (Htg50 : add_vec (mword_of_int (MN + 0x5e) : mword 64)
                      (sign_extend' 64
                         (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
                    = mword_of_int (MN + 0x50)) by pcw.
    iEval (rewrite Htg50) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID2 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID2 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (mn_epilogue (CID0 := CID4) m P1 sp0 K b (proc_addr jx) w19 w20 bf
              HK18 Kpop Hsp0 HP1sp HP1thr Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf19 Hf20 Hbuf
                    [Hown Htce Hcce Hpid Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID4 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID4 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID4 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid").
    { exact Hcsf. }
    { rewrite Ha0f. exact HP1a0. }
  Qed.

End ProofSysMknodM1Tail.

(* ===================================================================== *)
(*  THE WALK: +0x00 .. +0x4e, the two arms and the success tail.          *)
(* ===================================================================== *)

Section ProofSysMknodBody.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).

  (* the per-slot projection out of the boot family, at the copy THIS
     contract names ([ic_escrows] is IcacheEscrow's -- see fs-sysfile's
     trap 3 on the four [ic_sleeplocks] copies, which bites the same way). *)
  Lemma mn_esc_acc
      (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗ ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma wp_sys_mknod_sconf `{GEN : GenId} `{CID0 : CpuId}
      (gf ga gpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names)
      (gtl : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes : Z) (size : Z) (dev : mword 32)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_sys_mknod_sconf_body gf ga gpr gs j gl gu gd gk pd pav pu bn g
                            gtl bmapstart inodestart nib
                            ninodes size dev ns dqb dqs dqbs dqn v0 v1 v2
                            pid V m K eb b lks.
  Proof.
    cbv beta delta [wp_sys_mknod_sconf_body].
    intros pcE pj ret_tgt HK Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom
           Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb
           Hni1 Hni2 Hni3 Hush Hpkc Hnsb Hj Hgl Heb Hargv0 Hargv1 Hargv2.
    destruct (mn_kb K HK) as (Kcr & Kar & Kbo & Keo & Kiup & Kai & K18 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hpre #Hbio #Hlog Hseam
             Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks
             #Hireg #Hiopen Hsbn Hsbi Hsbs Hsbb #Hbmres #Hkenv #Hprocs Hir
             Hpriv Hcont".
    iPoseProof (printk_env_panic with "Hpre") as "#Hpe".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    (* ================= +0x00 c.addi16sp sp,-160 ================= *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 54 : mword 6) m K 20 b
              ltac:(lia) (mn_push sp0) with "Hcg Hpc []").
    { iApply (smni_00 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 54 : mword 6))))]> m).
    assert (HM1sp : mn_sp sp0 M1).
    { unfold mn_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply mn_push ]. }
    assert (HM1thr : mn_thr m M1).
    { intros c Hc N2 N8. rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (MN + 0x02))
      by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* the carve: sixteen of the TWENTY slots are [char path[128]]; slot 19
       holds the two [int] locals and slot 20 is padding *)
    iDestruct (mn_frame_carve sp0 with "Hframe")
      as "(%Hal & [%u1 Hf1] & [%u2 Hf2] & [%w19 Hf19] & [%w20 Hf20] & Hbytes)".
    (* slot 19, carved into the two [int] cells.  The 8-alignment comes out
       FIRST -- the halves no longer carry it and the join wants it back
       (durable-notes, "A C LOCAL TAKEN BY ADDRESS"). *)
    iDestruct (word_pointsto_aligned_p with "Hf19") as %Hal19.
    iDestruct (word_pointsto_split4 with "Hf19") as "[Hmin Hmaj]".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply mn_frm1).
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 18 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply mn_frm2).
    (* ================= +0x02 c.sdsp ra,152(sp) ================= *)
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (MN + 0x02))
              (mword_of_int 19 : mword 6) Rra M1 (K - 20)%nat u1 b
              with "Hcg Hpc [] Hf1").
    { iApply (smni_02 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (MN + 0x02) : mword 64) 2
                    = mword_of_int (MN + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ================= +0x04 c.sdsp s0,144(sp) ================= *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (MN + 0x04))
              (mword_of_int 18 : mword 6) Rs0 M1 (K - 20)%nat u2 b
              with "Hcg Hpc [] Hf2").
    { iApply (smni_04 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rgne; rewrite Hc2 HM1s0) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (MN + 0x04) : mword 64) 2
                    = mword_of_int (MN + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ================= +0x06 c.addi4spn s0,sp,160 ================= *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (MN + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 40 : mword 8) Rs0
              M1 (K - 20)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (smni_06 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 40 : mword 8))))]> M1).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { etransitivity; [ rewrite /M2; apply upd_eq |].
      rewrite HM1sp. apply mn_fp. }
    assert (HM2sp : mn_sp sp0 M2)
      by (rewrite /mn_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : mn_thr m M2).
    { intros c Hc N2 N8. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8). }
    assert (Hpp08 : add_vec_int (mword_of_int (MN + 0x06) : mword 64) 2
                    = mword_of_int (MN + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ================= +0x08 jal ra,begin_op ================= *)
    iApply (wp_jal_s_sconf (CID := CID4) (mword_of_int (MN + 0x08)) Rra
              (mword_of_int 2091440 : mword 21) M2 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (smni_08 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (MN + 0x08) : mword 64) 4)]> M2).
    assert (Hjbo : add_vec (mword_of_int (MN + 0x08) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091440 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iEval (rewrite Hjbo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (MN + 0x08) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : mn_sp sp0 M3)
      by (rewrite /mn_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3thr : mn_thr m M3).
    { intros c Hc N2 N8. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8). }
    (* the process BLOCK, LENT across begin_op and taken straight back *)
    iDestruct (proc_priv_bare_acc gf pj pid V with "Hpriv") as "[Hpbare Hpback0]".
    iDestruct (cpu_own_transport CID0 CID5 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (BeginOp.wp_begin_op_sconf (CID := CID5) gs j gl bn g fsc_fs fsc_cov fsc_logst
              dev pid (DfracOwn (1/4)) M3 (K - 20)%nat eb b lks
              V ltac:(lia) Hj Hgl (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hlog Hpbare Hprocs").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID6 Hq6 mbo) "%Hcsbo Hcg Hown _ _ Hpc Hpbare Hop".
    assert (Hpc0c : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = mword_of_int (MN + 0x0c)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc0c) in "Hpc".
    iDestruct ("Hpback0" with "Hpbare") as "Hpriv".
    assert (Hbosp : mn_sp sp0 mbo).
    { rewrite /mn_sp (callee_saved_lookup Hcsbo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Hbos0 : (mbo !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsbo Rs0 ltac:(vm_compute; reflexivity)).
      exact HM3s0. }
    assert (Hbothr : mn_thr m mbo).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcsbo c Hc).
      exact (HM3thr c Hc N2 N8). }
    (* ================= +0x0c addi a1,s0,-148 : &major ================= *)
    iApply (wp_addi4_s_sconf (CID := CID6) (mword_of_int (MN + 0x0c)) Ra1 Rs0
              (mword_of_int 3948 : mword 12) mbo (K - 20)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (smni_0c with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M4 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mbo !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3948 : mword 12)))]> mbo).
    assert (HM4a1 : (M4 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 19) 4).
    { etransitivity; [ rewrite /M4; apply upd_eq |].
      rewrite Hbos0. apply mn_maj. }
    assert (HM4sp : mn_sp sp0 M4)
      by (rewrite /mn_sp /M4 upd_ne; [exact Hbosp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact Hbos0 | nz]).
    assert (HM4thr : mn_thr m M4).
    { intros c Hc N2 N8. rewrite /M4 upd_ne; [| regne].
      exact (Hbothr c Hc N2 N8). }
    assert (Hpp10 : add_vec_int (mword_of_int (MN + 0x0c) : mword 64) 4
                    = mword_of_int (MN + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ================= +0x10 c.li a0,1 ================= *)
    iApply (wp_cli_s_sconf (CID := CID7) (mword_of_int (MN + 0x10)) Ra0
              (mword_of_int 1 : mword 6)
              (mword_of_int (Z.of_nat 1) : mword 64) M4 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (smni_10 with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (M5 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 1) : mword 64)]> M4).
    assert (HM5a0 : (M5 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 1) : mword 64))
      by (rewrite /M5; apply upd_eq).
    assert (HM5a1 : (M5 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 19) 4)
      by (rewrite /M5 upd_ne; [exact HM4a1 | nz]).
    assert (HM5sp : mn_sp sp0 M5)
      by (rewrite /mn_sp /M5 upd_ne; [exact HM4sp | nz]).
    assert (HM5s0 : (M5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M5 upd_ne; [exact HM4s0 | nz]).
    assert (HM5thr : mn_thr m M5).
    { intros c Hc N2 N8. rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2 N8). }
    assert (Hpp12 : add_vec_int (mword_of_int (MN + 0x10) : mword 64) 2
                    = mword_of_int (MN + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ================= +0x12 jal ra,argint : argint(1, &major) ========= *)
    iApply (wp_jal_s_sconf (CID := CID8) (mword_of_int (MN + 0x12)) Rra
              (mword_of_int 2086242 : mword 21) M5 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (smni_12 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (MN + 0x12) : mword 64) 4)]> M5).
    assert (Hjai1 : add_vec (mword_of_int (MN + 0x12) : mword 64)
                      (sign_extend' 64 (mword_of_int 2086242 : mword 21))
                    = mword_of_int KernelSyms.argint) by pcw.
    iEval (rewrite Hjai1) in "Hpc".
    assert (HM6ra : (M6 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (MN + 0x12) : mword 64) 4)
      by (rewrite /M6; apply upd_eq).
    assert (HM6a0 : (M6 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 1) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a0 | nz]).
    assert (HM6a1 : (M6 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 19) 4)
      by (rewrite /M6 upd_ne; [exact HM5a1 | nz]).
    assert (HM6sp : mn_sp sp0 M6)
      by (rewrite /mn_sp /M6 upd_ne; [exact HM5sp | nz]).
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M6 upd_ne; [exact HM5s0 | nz]).
    assert (HM6thr : mn_thr m M6).
    { intros c Hc N2 N8. rewrite /M6 upd_ne; [| regne].
      exact (HM5thr c Hc N2 N8). }
    (* the trapframe quarter and its page, BORROWED out of the block for the
       call and put straight back -- ProofSysExit's move, twice over. *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf gf pj pid V with "Hpriv") as "(Htf & Hpage & Hback1)".
    iEval (rewrite -HM6a1) in "Hmaj".
    iDestruct (cpu_own_transport CID6 CID9 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argint.wp_argint_sconf (CID := CID9) M6 (K - 20)%nat 0%nat eb pj
              1%nat (ud_tfp (pv_upt V)) (pv_tf V) v1 (word_hi w19)
              (DfracOwn (1/4)) b lks
              mn_arg1_lt HM6a0 Hargv1 mn_noff0 ltac:(lia) Hpv
              with "Hcg Hown Htext Hdata Hpc Htf Hpage Hmaj").
    iIntros (CID10 Hq10 mai1) "%Hcsai1 Hcg Hown Hpc Htf Hpage Hmaj".
    iEval (rewrite HM6a1) in "Hmaj".
    iDestruct ("Hback1" with "Htf Hpage") as "Hpriv".
    assert (Hpc16 : ret_pc (M6 !!! Regidx Rra : mword 64)
                    = mword_of_int (MN + 0x16)) by (rewrite HM6ra; pcw).
    iEval (rewrite Hpc16) in "Hpc".
    assert (Hai1sp : mn_sp sp0 mai1).
    { rewrite /mn_sp (callee_saved_lookup Hcsai1 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM6sp. }
    assert (Hai1s0 : (mai1 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsai1 Rs0 ltac:(vm_compute; reflexivity)).
      exact HM6s0. }
    assert (Hai1thr : mn_thr m mai1).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcsai1 c Hc).
      exact (HM6thr c Hc N2 N8). }
    (* ================= +0x16 addi a1,s0,-152 : &minor ================= *)
    iApply (wp_addi4_s_sconf (CID := CID10) (mword_of_int (MN + 0x16)) Ra1 Rs0
              (mword_of_int 3944 : mword 12) mai1 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (smni_16 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (M7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mai1 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3944 : mword 12)))]> mai1).
    assert (HM7a1 : (M7 !!! Regidx Ra1 : mword 64) = pa_stk sp0 19).
    { etransitivity; [ rewrite /M7; apply upd_eq |].
      rewrite Hai1s0. apply mn_min. }
    assert (HM7sp : mn_sp sp0 M7)
      by (rewrite /mn_sp /M7 upd_ne; [exact Hai1sp | nz]).
    assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M7 upd_ne; [exact Hai1s0 | nz]).
    assert (HM7thr : mn_thr m M7).
    { intros c Hc N2 N8. rewrite /M7 upd_ne; [| regne].
      exact (Hai1thr c Hc N2 N8). }
    assert (Hpp1a : add_vec_int (mword_of_int (MN + 0x16) : mword 64) 4
                    = mword_of_int (MN + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ================= +0x1a c.li a0,2 ================= *)
    iApply (wp_cli_s_sconf (CID := CID11) (mword_of_int (MN + 0x1a)) Ra0
              (mword_of_int 2 : mword 6)
              (mword_of_int (Z.of_nat 2) : mword 64) M7 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (smni_1a with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (M8 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 2) : mword 64)]> M7).
    assert (HM8a0 : (M8 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 2) : mword 64))
      by (rewrite /M8; apply upd_eq).
    assert (HM8a1 : (M8 !!! Regidx Ra1 : mword 64) = pa_stk sp0 19)
      by (rewrite /M8 upd_ne; [exact HM7a1 | nz]).
    assert (HM8sp : mn_sp sp0 M8)
      by (rewrite /mn_sp /M8 upd_ne; [exact HM7sp | nz]).
    assert (HM8s0 : (M8 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M8 upd_ne; [exact HM7s0 | nz]).
    assert (HM8thr : mn_thr m M8).
    { intros c Hc N2 N8. rewrite /M8 upd_ne; [| regne].
      exact (HM7thr c Hc N2 N8). }
    assert (Hpp1c : add_vec_int (mword_of_int (MN + 0x1a) : mword 64) 2
                    = mword_of_int (MN + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ================= +0x1c jal ra,argint : argint(2, &minor) ========= *)
    iApply (wp_jal_s_sconf (CID := CID12) (mword_of_int (MN + 0x1c)) Rra
              (mword_of_int 2086232 : mword 21) M8 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (smni_1c with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (M9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (MN + 0x1c) : mword 64) 4)]> M8).
    assert (Hjai2 : add_vec (mword_of_int (MN + 0x1c) : mword 64)
                      (sign_extend' 64 (mword_of_int 2086232 : mword 21))
                    = mword_of_int KernelSyms.argint) by pcw.
    iEval (rewrite Hjai2) in "Hpc".
    assert (HM9ra : (M9 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (MN + 0x1c) : mword 64) 4)
      by (rewrite /M9; apply upd_eq).
    assert (HM9a0 : (M9 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 2) : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a0 | nz]).
    assert (HM9a1 : (M9 !!! Regidx Ra1 : mword 64) = pa_stk sp0 19)
      by (rewrite /M9 upd_ne; [exact HM8a1 | nz]).
    assert (HM9sp : mn_sp sp0 M9)
      by (rewrite /mn_sp /M9 upd_ne; [exact HM8sp | nz]).
    assert (HM9s0 : (M9 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M9 upd_ne; [exact HM8s0 | nz]).
    assert (HM9thr : mn_thr m M9).
    { intros c Hc N2 N8. rewrite /M9 upd_ne; [| regne].
      exact (HM8thr c Hc N2 N8). }
    iDestruct (proc_priv_tf gf pj pid V with "Hpriv") as "(Htf & Hpage & Hback2)".
    iEval (rewrite -HM9a1) in "Hmin".
    iDestruct (cpu_own_transport CID10 CID13 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argint.wp_argint_sconf (CID := CID13) M9 (K - 20)%nat 0%nat eb pj
              2%nat (ud_tfp (pv_upt V)) (pv_tf V) v2 (word_lo w19)
              (DfracOwn (1/4)) b lks
              mn_arg2_lt HM9a0 Hargv2 mn_noff0 ltac:(lia) Hpv
              with "Hcg Hown Htext Hdata Hpc Htf Hpage Hmin").
    iIntros (CID14 Hq14 mai2) "%Hcsai2 Hcg Hown Hpc Htf Hpage Hmin".
    iEval (rewrite HM9a1) in "Hmin".
    iDestruct ("Hback2" with "Htf Hpage") as "Hpriv".
    assert (Hpc20 : ret_pc (M9 !!! Regidx Rra : mword 64)
                    = mword_of_int (MN + 0x20)) by (rewrite HM9ra; pcw).
    iEval (rewrite Hpc20) in "Hpc".
    assert (Hai2sp : mn_sp sp0 mai2).
    { rewrite /mn_sp (callee_saved_lookup Hcsai2 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM9sp. }
    assert (Hai2s0 : (mai2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsai2 Rs0 ltac:(vm_compute; reflexivity)).
      exact HM9s0. }
    assert (Hai2thr : mn_thr m mai2).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcsai2 c Hc).
      exact (HM9thr c Hc N2 N8). }
    (* ================= +0x20 li a2,128 ================= *)
    iApply (wp_li4_s_sconf (CID := CID14) (mword_of_int (MN + 0x20)) Ra2
              (mword_of_int 128 : mword 12)
              (mword_of_int (Z.of_nat 128) : mword 64) mai2 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (smni_20 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (M10 := <[Regidx Ra2 := regval_into_reg
                   (mword_of_int (Z.of_nat 128) : mword 64)]> mai2).
    assert (HM10a2 : (M10 !!! Regidx Ra2 : mword 64)
                     = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M10; apply upd_eq).
    assert (HM10sp : mn_sp sp0 M10)
      by (rewrite /mn_sp /M10 upd_ne; [exact Hai2sp | nz]).
    assert (HM10s0 : (M10 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M10 upd_ne; [exact Hai2s0 | nz]).
    assert (HM10thr : mn_thr m M10).
    { intros c Hc N2 N8. rewrite /M10 upd_ne; [| regne].
      exact (Hai2thr c Hc N2 N8). }
    assert (Hpp24 : add_vec_int (mword_of_int (MN + 0x20) : mword 64) 4
                    = mword_of_int (MN + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ================= +0x24 addi a1,s0,-144 ================= *)
    iApply (wp_addi4_s_sconf (CID := CID15) (mword_of_int (MN + 0x24)) Ra1 Rs0
              (mword_of_int 3952 : mword 12) M10 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (smni_24 with "Htext"). }
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (M11 := <[Regidx Ra1 := regval_into_reg
                   (add_vec (M10 !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 3952 : mword 12)))]> M10).
    assert (HM11a1 : (M11 !!! Regidx Ra1 : mword 64) = pa_stk sp0 18).
    { etransitivity; [ rewrite /M11; apply upd_eq |].
      rewrite HM10s0. apply mn_buf. }
    assert (HM11a2 : (M11 !!! Regidx Ra2 : mword 64)
                     = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M11 upd_ne; [exact HM10a2 | nz]).
    assert (HM11sp : mn_sp sp0 M11)
      by (rewrite /mn_sp /M11 upd_ne; [exact HM10sp | nz]).
    assert (HM11s0 : (M11 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M11 upd_ne; [exact HM10s0 | nz]).
    assert (HM11thr : mn_thr m M11).
    { intros c Hc N2 N8. rewrite /M11 upd_ne; [| regne].
      exact (HM10thr c Hc N2 N8). }
    assert (Hpp28 : add_vec_int (mword_of_int (MN + 0x24) : mword 64) 4
                    = mword_of_int (MN + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    (* ================= +0x28 c.li a0,0 ================= *)
    iApply (wp_cli_s_sconf (CID := CID16) (mword_of_int (MN + 0x28)) Ra0
              (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M11 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (smni_28 with "Htext"). }
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (M12 := <[Regidx Ra0 := regval_into_reg
                   (mword_of_int (Z.of_nat 0) : mword 64)]> M11).
    assert (HM12a0 : (M12 !!! Regidx Ra0 : mword 64)
                     = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M12; apply upd_eq).
    assert (HM12a1 : (M12 !!! Regidx Ra1 : mword 64) = pa_stk sp0 18)
      by (rewrite /M12 upd_ne; [exact HM11a1 | nz]).
    assert (HM12a2 : (M12 !!! Regidx Ra2 : mword 64)
                     = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M12 upd_ne; [exact HM11a2 | nz]).
    assert (HM12sp : mn_sp sp0 M12)
      by (rewrite /mn_sp /M12 upd_ne; [exact HM11sp | nz]).
    assert (HM12s0 : (M12 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M12 upd_ne; [exact HM11s0 | nz]).
    assert (HM12thr : mn_thr m M12).
    { intros c Hc N2 N8. rewrite /M12 upd_ne; [| regne].
      exact (HM11thr c Hc N2 N8). }
    assert (Hpp2a : add_vec_int (mword_of_int (MN + 0x28) : mword 64) 2
                    = mword_of_int (MN + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ================= +0x2a jal ra,argstr ================= *)
    iApply (wp_jal_s_sconf (CID := CID17) (mword_of_int (MN + 0x2a)) Rra
              (mword_of_int 2086274 : mword 21) M12 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (smni_2a with "Htext"). }
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (M13 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (MN + 0x2a) : mword 64) 4)]> M12).
    assert (Hjas : add_vec (mword_of_int (MN + 0x2a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086274 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iEval (rewrite Hjas) in "Hpc".
    assert (HM13ra : (M13 !!! Regidx Rra : mword 64)
                     = add_vec_int (mword_of_int (MN + 0x2a) : mword 64) 4)
      by (rewrite /M13; apply upd_eq).
    assert (HM13a0 : (M13 !!! Regidx Ra0 : mword 64)
                     = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M13 upd_ne; [exact HM12a0 | nz]).
    assert (HM13a1 : (M13 !!! Regidx Ra1 : mword 64) = pa_stk sp0 18)
      by (rewrite /M13 upd_ne; [exact HM12a1 | nz]).
    assert (HM13a2 : (M13 !!! Regidx Ra2 : mword 64)
                     = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M13 upd_ne; [exact HM12a2 | nz]).
    assert (HM13sp : mn_sp sp0 M13)
      by (rewrite /mn_sp /M13 upd_ne; [exact HM12sp | nz]).
    assert (HM13s0 : (M13 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M13 upd_ne; [exact HM12s0 | nz]).
    assert (HM13thr : mn_thr m M13).
    { intros c Hc N2 N8. rewrite /M13 upd_ne; [| regne].
      exact (HM12thr c Hc N2 N8). }
    iDestruct (mn_bytes_name (pa_stk sp0 18) 128 with "Hbytes") as (bf0) "Hbuf".
    iDestruct (cpu_own_transport CID14 CID18 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argstr.wp_argstr_sconf (CID := CID18) ga gf M13 (K - 20)%nat 0%nat eb pj
              0%nat v0 pid V 128%nat bf0 b lks
              mn_arg0_lt HM13a0 Hargv0 mn_noff0 ltac:(lia) HM13a2 mn_maxpath_lt
              (Hlb "kmem"%string)
              with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [Hbuf]").
    { iEval (rewrite HM13a1). iExact "Hbuf". }
    iIntros (CID19 Hq19 mas P' bf) "%Hcsas %Hupt Hcg Hown Hpc Hpriv Hbuf %Hfsr".
    iEval (rewrite HM13a1) in "Hbuf".
    assert (Hpc2e : ret_pc (M13 !!! Regidx Rra : mword 64)
                    = mword_of_int (MN + 0x2e)) by (rewrite HM13ra; pcw).
    iEval (rewrite Hpc2e) in "Hpc".
    assert (Hassp : mn_sp sp0 mas).
    { rewrite /mn_sp (callee_saved_lookup Hcsas csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM13sp. }
    assert (Hass0 : (mas !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsas Rs0 ltac:(vm_compute; reflexivity)).
      exact HM13s0. }
    assert (Hasthr : mn_thr m mas).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcsas c Hc).
      exact (HM13thr c Hc N2 N8). }
    (* ================= +0x2e bltz a0 -> ARM A ================= *)
    destruct Hfsr as [(pk & Hpk & Hpcstr & Hpr) | Hpr].
    - (* ---- the string fetched: the [bltz] FALLS THROUGH ---- *)
      iApply (wp_blt_x0_fall_s_sconf (CID := CID19) (mword_of_int (MN + 0x2e))
                (mword_of_int 42 : mword 13) Ra0 mas (K - 20)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Hpr; exact (mn_nonneg _ (mn_len_range pk Hpk)))
                with "Hcg Hpc []").
      { iApply (smni_2e with "Htext"). }
      iIntros (CID20 Hq20) "Hcg Hpc".
      assert (Hpp32 : add_vec_int (mword_of_int (MN + 0x2e) : mword 64) 4
                      = mword_of_int (MN + 0x32)) by pcw.
      iEval (rewrite Hpp32) in "Hpc".
      (* each [int] cell, halved: the [lh]s read the LOW half of each *)
      iDestruct (word4_pointsto_split2 (KTR := KT1) with "Hmin") as "[Hminlo Hminhi]".
      iDestruct (word4_pointsto_split2 (KTR := KT1) with "Hmaj") as "[Hmajlo Hmajhi]".
      (* ============ +0x32 lh a3,-152(s0) : minor ============ *)
      assert (Hamin : add_vec (rget (CID := CID20) mas Rs0)
                        (sign_extend' 64 (mword_of_int 3944 : mword 12))
                      = pa_stk sp0 19).
      { rewrite (rget_ne (CID := CID20) mas Rs0 ltac:(vm_compute; discriminate))
                Hass0. apply mn_min. }
      iEval (rewrite -Hamin) in "Hminlo".
      iApply (wp_lh_s_sconf (CID := CID20) (kt := KT1) (ktd := KT1) (mword_of_int (MN + 0x32)) Ra3 Rs0
                (mword_of_int 3944 : mword 12) mas (K - 20)%nat
                (hw_lo (arg_int32 v2)) b (dqm := DfracOwn 1)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hminlo").
      { iApply (smni_32 with "Htext"). }
      iIntros (CID21 Hq21) "Hcg Hpc Hminlo".
      iEval (rewrite Hamin) in "Hminlo".
      set (N0 := <[Regidx Ra3 := regval_into_reg
                    (sign_extend' 64 (hw_lo (arg_int32 v2)))]> mas).
      assert (HN0a3 : (N0 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v2))))
        by (rewrite /N0; apply upd_eq).
      assert (HN0sp : mn_sp sp0 N0)
        by (rewrite /mn_sp /N0 upd_ne; [exact Hassp | nz]).
      assert (HN0s0 : (N0 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N0 upd_ne; [exact Hass0 | nz]).
      assert (HN0thr : mn_thr m N0).
      { intros c Hc N2 N8. rewrite /N0 upd_ne; [| regne].
        exact (Hasthr c Hc N2 N8). }
      assert (Hpp36 : add_vec_int (mword_of_int (MN + 0x32) : mword 64) 4
                      = mword_of_int (MN + 0x36)) by pcw.
      iEval (rewrite Hpp36) in "Hpc".
      (* ============ +0x36 lh a2,-148(s0) : major ============ *)
      assert (Hamaj : add_vec (rget (CID := CID21) N0 Rs0)
                        (sign_extend' 64 (mword_of_int 3948 : mword 12))
                      = pa_add (pa_stk sp0 19) 4).
      { rewrite (rget_ne (CID := CID21) N0 Rs0 ltac:(vm_compute; discriminate))
                HN0s0. apply mn_maj. }
      iEval (rewrite -Hamaj) in "Hmajlo".
      iApply (wp_lh_s_sconf (CID := CID21) (kt := KT1) (ktd := KT1) (mword_of_int (MN + 0x36)) Ra2 Rs0
                (mword_of_int 3948 : mword 12) N0 (K - 20)%nat
                (hw_lo (arg_int32 v1)) b (dqm := DfracOwn 1)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmajlo").
      { iApply (smni_36 with "Htext"). }
      iIntros (CID22 Hq22) "Hcg Hpc Hmajlo".
      iEval (rewrite Hamaj) in "Hmajlo".
      set (N1 := <[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 (hw_lo (arg_int32 v1)))]> N0).
      assert (HN1a2 : (N1 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v1))))
        by (rewrite /N1; apply upd_eq).
      assert (HN1a3 : (N1 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v2))))
        by (rewrite /N1 upd_ne; [exact HN0a3 | nz]).
      assert (HN1sp : mn_sp sp0 N1)
        by (rewrite /mn_sp /N1 upd_ne; [exact HN0sp | nz]).
      assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N1 upd_ne; [exact HN0s0 | nz]).
      assert (HN1thr : mn_thr m N1).
      { intros c Hc N2 N8. rewrite /N1 upd_ne; [| regne].
        exact (HN0thr c Hc N2 N8). }
      assert (Hpp3a : add_vec_int (mword_of_int (MN + 0x36) : mword 64) 4
                      = mword_of_int (MN + 0x3a)) by pcw.
      iEval (rewrite Hpp3a) in "Hpc".
      (* the two cells, rejoined for the epilogue: nothing below reads them *)
      iDestruct (word4_pointsto_join2 (KTR := KT1) _ _ _ _
                   (aligned8_aligned4 _ Hal19) with "Hminlo Hminhi") as "Hmin".
      iDestruct (word4_pointsto_join2 (KTR := KT1) _ _ _ _
                   (aligned8_aligned4_hi _ Hal19) with "Hmajlo Hmajhi") as "Hmaj".
      iDestruct (word_pointsto_join4 _ _ _ _ Hal19 with "Hmin Hmaj") as "Hf19".
      (* ============ +0x3a c.li a1,3 : T_DEVICE ============ *)
      iApply (wp_cli_s_sconf (CID := CID22) (mword_of_int (MN + 0x3a)) Ra1
                (mword_of_int 3 : mword 6)
                (sign_extend' 64 SpecCreate.T_DEVICE) N1 (K - 20)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (smni_3a with "Htext"). }
      iIntros (CID23 Hq23) "Hcg Hpc".
      set (N2 := <[Regidx Ra1 := regval_into_reg
                    (sign_extend' 64 SpecCreate.T_DEVICE)]> N1).
      assert (HN2a1 : (N2 !!! Regidx Ra1 : mword 64)
                      = (sign_extend' 64 SpecCreate.T_DEVICE))
        by (rewrite /N2; apply upd_eq).
      assert (HN2a2 : (N2 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v1))))
        by (rewrite /N2 upd_ne; [exact HN1a2 | nz]).
      assert (HN2a3 : (N2 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v2))))
        by (rewrite /N2 upd_ne; [exact HN1a3 | nz]).
      assert (HN2sp : mn_sp sp0 N2)
        by (rewrite /mn_sp /N2 upd_ne; [exact HN1sp | nz]).
      assert (HN2s0 : (N2 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N2 upd_ne; [exact HN1s0 | nz]).
      assert (HN2thr : mn_thr m N2).
      { intros c Hc N2' N8. rewrite /N2 upd_ne; [| regne].
        exact (HN1thr c Hc N2' N8). }
      assert (Hpp3c : add_vec_int (mword_of_int (MN + 0x3a) : mword 64) 2
                      = mword_of_int (MN + 0x3c)) by pcw.
      iEval (rewrite Hpp3c) in "Hpc".
      (* ============ +0x3c addi a0,s0,-144 ============ *)
      iApply (wp_addi4_s_sconf (CID := CID23) (mword_of_int (MN + 0x3c)) Ra0 Rs0
                (mword_of_int 3952 : mword 12) N2 (K - 20)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (smni_3c with "Htext"). }
      iIntros (CID24 Hq24) "Hcg Hpc".
      set (N3 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (N2 !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 3952 : mword 12)))]> N2).
      assert (HN3a0 : (N3 !!! Regidx Ra0 : mword 64) = pa_stk sp0 18).
      { etransitivity; [ rewrite /N3; apply upd_eq |].
        rewrite HN2s0. apply mn_buf. }
      assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64)
                      = (sign_extend' 64 SpecCreate.T_DEVICE))
        by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
      assert (HN3a2 : (N3 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v1))))
        by (rewrite /N3 upd_ne; [exact HN2a2 | nz]).
      assert (HN3a3 : (N3 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v2))))
        by (rewrite /N3 upd_ne; [exact HN2a3 | nz]).
      assert (HN3sp : mn_sp sp0 N3)
        by (rewrite /mn_sp /N3 upd_ne; [exact HN2sp | nz]).
      assert (HN3s0 : (N3 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N3 upd_ne; [exact HN2s0 | nz]).
      assert (HN3thr : mn_thr m N3).
      { intros c Hc N2' N8. rewrite /N3 upd_ne; [| regne].
        exact (HN2thr c Hc N2' N8). }
      assert (Hpp40 : add_vec_int (mword_of_int (MN + 0x3c) : mword 64) 4
                      = mword_of_int (MN + 0x40)) by pcw.
      iEval (rewrite Hpp40) in "Hpc".
      (* ============ +0x40 jal ra,create ============ *)
      iApply (wp_jal_s_sconf (CID := CID24) (mword_of_int (MN + 0x40)) Rra
                (mword_of_int 2095296 : mword 21) N3 (K - 20)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (smni_40 with "Htext"). }
      iIntros (CID25 Hq25) "Hcg Hpc".
      set (N4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (MN + 0x40) : mword 64) 4)]> N3).
      assert (Hjcr : add_vec (mword_of_int (MN + 0x40) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095296 : mword 21))
                     = mword_of_int KernelSyms.create) by pcw.
      iEval (rewrite Hjcr) in "Hpc".
      assert (HN4ra : (N4 !!! Regidx Rra : mword 64)
                      = add_vec_int (mword_of_int (MN + 0x40) : mword 64) 4)
        by (rewrite /N4; apply upd_eq).
      assert (HN4a0 : (N4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 18)
        by (rewrite /N4 upd_ne; [exact HN3a0 | nz]).
      assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64)
                      = (sign_extend' 64 SpecCreate.T_DEVICE))
        by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
      assert (HN4a2 : (N4 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v1))))
        by (rewrite /N4 upd_ne; [exact HN3a2 | nz]).
      assert (HN4a3 : (N4 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (hw_lo (arg_int32 v2))))
        by (rewrite /N4 upd_ne; [exact HN3a3 | nz]).
      assert (HN4sp : mn_sp sp0 N4)
        by (rewrite /mn_sp /N4 upd_ne; [exact HN3sp | nz]).
      assert (HN4s0 : (N4 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N4 upd_ne; [exact HN3s0 | nz]).
      assert (HN4thr : mn_thr m N4).
      { intros c Hc N2' N8. rewrite /N4 upd_ne; [| regne].
        exact (HN3thr c Hc N2' N8). }
      iDestruct (mn_buf_split (pa_stk sp0 18) bf pk Hpk with "Hbuf")
        as "[Hbufk Hbufrest]".
      iDestruct (log_op_openS with "Hop") as (Sb0) "[HopS Htx]".
      iDestruct (cpu_own_transport CID19 CID25 0 eb pj b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Create.wp_create_sconf (CID := CID25) gs j gl gu gd gk pd pav pu
                bn g gtl ga gf gpr bmapstart inodestart
                nib ninodes size dev pk bf
                SpecCreate.T_DEVICE (hw_lo (arg_int32 v1)) (hw_lo (arg_int32 v2))
                (upd_upt V P') MAXOPBLOCKS Sb0 ns pid dqb dqs dqbs dqn
                N4 (K - 20)%nat eb b lks
                ltac:(lia) Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom Hsize
                Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr
                (mn_plen_lt pk Hpk) Hni1 Hni2 Hni3 Hush mn_tdev_nz SpecCreate.T_DEVICE_ty_ok Hpkc
                ltac:(unfold create_units; lia) Hnsb Hj Hgl
                HN4a1 HN4a2 HN4a3 Heb
                with "Hcg Hown Htext Hpc Hdata Hpre Hbio Hlog Hkenv
                      Hitab Hitinv Hescrows Hslks Hireg Hiopen Hsbn Hsbi Hsbs
                      Hsbb
                      Hbmres Hpriv [Hbufk] Hprocs Hdev Hgeo Hdlk Hbsl Hir HopS Htx").
      { iEval (rewrite HN4a0). iExact "Hbufk". }
      iIntros (CID26 Hq26 mcr ok made kk qi ss gy inum dn bm un1 Sb1 ns1)
        "%Hcscr Hcg Hown Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hbufk Hbsl
         %Hns1 Hir %Hun1 HopS Hok".
      iEval (rewrite HN4a0) in "Hbufk".
      assert (Hpc44 : ret_pc (N4 !!! Regidx Rra : mword 64)
                      = mword_of_int (MN + 0x44)) by (rewrite HN4ra; pcw).
      iEval (rewrite Hpc44) in "Hpc".
      assert (Hcrsp : mn_sp sp0 mcr).
      { rewrite /mn_sp (callee_saved_lookup Hcscr csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HN4sp. }
      assert (Hcrthr : mn_thr m mcr).
      { intros c Hc N2' N8. rewrite (callee_saved_lookup Hcscr c Hc).
        exact (HN4thr c Hc N2' N8). }
      (* ============ +0x2c c.beqz a0 -> ARM B ============ *)
      destruct ok.
      + (* ---------- create SUCCEEDED: the LOCKED inode ---------- *)
        iDestruct "Hok" as "[%Hokf Hlocked]".
        destruct Hokf as (Hcra0 & Hkk & Hinum & _).
        assert (Hipnz : ientry kk <> (zero_reg : mword 64))
          by (apply ientry_ne_zero; lia).
        iApply (wp_cbeqz_fall_s_sconf (CID := CID26) (mword_of_int (MN + 0x44))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  mcr (K - 20)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Hcra0;
                        apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
                  with "Hcg Hpc []").
        { iApply (smni_44 with "Htext"). }
        iIntros (CID27 Hq27) "Hcg Hpc".
        assert (Hpp46 : add_vec_int (mword_of_int (MN + 0x44) : mword 64) 2
                        = mword_of_int (MN + 0x46)) by pcw.
        iEval (rewrite Hpp46) in "Hpc".
        (* ============ +0x2e jal ra,iunlockput ============ *)
        iApply (wp_jal_s_sconf (CID := CID27) (mword_of_int (MN + 0x46)) Rra
                  (mword_of_int 2089308 : mword 21) mcr (K - 20)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (smni_46 with "Htext"). }
        iIntros (CID28 Hq28) "Hcg Hpc".
        set (P0 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (MN + 0x46) : mword 64) 4)]> mcr).
        assert (Hjiu : add_vec (mword_of_int (MN + 0x46) : mword 64)
                         (sign_extend' 64 (mword_of_int 2089308 : mword 21))
                       = mword_of_int KernelSyms.iunlockput) by pcw.
        iEval (rewrite Hjiu) in "Hpc".
        assert (HP0ra : (P0 !!! Regidx Rra : mword 64)
                        = add_vec_int (mword_of_int (MN + 0x46) : mword 64) 4)
          by (rewrite /P0; apply upd_eq).
        assert (HP0a0 : (P0 !!! Regidx Ra0 : mword 64) = ientry kk)
          by (rewrite /P0 upd_ne; [exact Hcra0 | nz]).
        assert (HP0sp : mn_sp sp0 P0)
          by (rewrite /mn_sp /P0 upd_ne; [exact Hcrsp | nz]).
        assert (HP0thr : mn_thr m P0).
        { intros c Hc N2' N8. rewrite /P0 upd_ne; [| regne].
          exact (Hcrthr c Hc N2' N8). }
        (* the ten conjuncts create hands back ARE iunlockput's precondition *)
        iDestruct "Hlocked" as (gil gisl)
          "(Hslk & Hslkd & Hdep & Hidev & Hiinum & Hivalid & Hload &
            Hshot & Hfrz & Href & Hru)".
        (* create's payout is GENERATION-NAMED now; iunlockput takes the
           erased reference, so weaken it back here.  One line, and the
           name is what sys_open's O_CREATE arm needs kept. *)
        iDestruct (inode_ref_short_gen_forget with "Href") as "Href".
        iDestruct (mn_esc_acc kk ltac:(lia)
                     with "Hescrows") as "#Hesc".
        (* CREATE'S PAYOUT IS THE ARMED DESCRIPTOR (durable-disk B''-tx2):
           the escrow parked half of the transaction's element at create's
           own [ilock(ip)] and create handed the other half over inside the
           bundle.  The release takes the ARMED contract (B''-tx4), which
           retires the descriptor in the ghost step that parks the payload
           and hands the whole token back. *)
        destruct (Hiregb inum ltac:(lia)) as [Hibcov Hiblog].
        iDestruct (proc_priv_bare_acc gf pj pid (upd_upt V P') with "Hpriv")
          as "[Hpbare Hpback]".
        iDestruct (cpu_own_transport CID26 CID28 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Iunlockput.wp_iunlockput_tx_sconf (CID := CID28) gs j gl gu gd gk
                  pd pav pu bn g gtl gil gisl bmapstart
                  inodestart nib size dev kk qi ss gy inum dn bm un1
                  pid (DfracOwn (1/4)) dqb dqs P0 (K - 20)%nat eb b lks
                  (upd_upt V P') ltac:(lia) ltac:(lia) Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                  Hibcov Hiblog ltac:(lia) Hcovb
                  ltac:(exact (proj2 (proj2 Hun1) eq_refl)) Hj Hgl HP0a0
                  (Hlb "log"%string) Hclog
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hitab Hitinv
                        Hesc Hireg [] Hslk Hslkd Hdep Hidev Hiinum Hivalid
                        Hload Hshot Hfrz [$Href $Hru] Hsbb Hsbi Hbmres Hpbare Hprocs Hdev
                        Hgeo Hdlk Hbsl [HopS]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        (* RULING G: a runtime caller lends the SEALED arm. *)
        { iExact "Hiopen". }
        { iApply (log_opS_opb with "HopS"). }
        iIntros (CID29 Hq29 miu n2)
          "%Hcsiu Hcg Hown _ _ Hpc Hpbare Hsbb Hsbi Hbsl %Hn2
           Hop Hislot".
        assert (Hpc4a : ret_pc (P0 !!! Regidx Rra : mword 64)
                        = mword_of_int (MN + 0x4a)) by (rewrite HP0ra; pcw).
        iEval (rewrite Hpc4a) in "Hpc".
        assert (Hiusp : mn_sp sp0 miu).
        { rewrite /mn_sp (callee_saved_lookup Hcsiu csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HP0sp. }
        assert (Hiuthr : mn_thr m miu).
        { intros c Hc N2' N8. rewrite (callee_saved_lookup Hcsiu c Hc).
          exact (HP0thr c Hc N2' N8). }
        (* ============ +0x32 jal ra,end_op ============ *)
        iApply (wp_jal_s_sconf (CID := CID29) (mword_of_int (MN + 0x4a)) Rra
                  (mword_of_int 2091514 : mword 21) miu (K - 20)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (smni_4a with "Htext"). }
        iIntros (CID30 Hq30) "Hcg Hpc".
        set (P1 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (MN + 0x4a) : mword 64) 4)]> miu).
        assert (Hjeo : add_vec (mword_of_int (MN + 0x4a) : mword 64)
                         (sign_extend' 64 (mword_of_int 2091514 : mword 21))
                       = mword_of_int KernelSyms.end_op) by pcw.
        iEval (rewrite Hjeo) in "Hpc".
        assert (HP1ra : (P1 !!! Regidx Rra : mword 64)
                        = add_vec_int (mword_of_int (MN + 0x4a) : mword 64) 4)
          by (rewrite /P1; apply upd_eq).
        assert (HP1sp : mn_sp sp0 P1)
          by (rewrite /mn_sp /P1 upd_ne; [exact Hiusp | nz]).
        assert (HP1thr : mn_thr m P1).
        { intros c Hc N2' N8. rewrite /P1 upd_ne; [| regne].
          exact (Hiuthr c Hc N2' N8). }
        iDestruct (cpu_own_transport CID29 CID30 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (EndOp.wp_end_op_sconf (CID := CID30) gs j gl gu gd gk pd pav pu
                  bn g fsc_fs fsc_cov fsc_logst dev n2 pid (DfracOwn (1/4))
                  P1 (K - 20)%nat eb b lks
                  (upd_upt V P') ltac:(lia) Hgeom Hj Hgl (Hlb "log"%string)
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                        Hpbare Hprocs Hdev Hgeo Hdlk Hop").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        iIntros (CID31 Hq31 meo) "%Hcseo Hcg Hown _ _ Hpc Hpbare".
        assert (Hpc4e : ret_pc (P1 !!! Regidx Rra : mword 64)
                        = mword_of_int (MN + 0x4e)) by (rewrite HP1ra; pcw).
        iEval (rewrite Hpc4e) in "Hpc".
        assert (Heosp : mn_sp sp0 meo).
        { rewrite /mn_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HP1sp. }
        assert (Heothr : mn_thr m meo).
        { intros c Hc N2' N8. rewrite (callee_saved_lookup Hcseo c Hc).
          exact (HP1thr c Hc N2' N8). }
        (* ============ +0x36 c.li a0,0 ============ *)
        iApply (wp_cli_s_sconf (CID := CID31) (mword_of_int (MN + 0x4e)) Ra0
                  (mword_of_int 0 : mword 6) (zero_reg : mword 64)
                  meo (K - 20)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc []").
        { iApply (smni_4e with "Htext"). }
        iIntros (CID32 Hq32) "Hcg Hpc".
        set (P2 := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> meo).
        assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (zero_reg : mword 64))
          by (rewrite /P2; apply upd_eq).
        assert (HP2sp : mn_sp sp0 P2)
          by (rewrite /mn_sp /P2 upd_ne; [exact Heosp | nz]).
        assert (HP2thr : mn_thr m P2).
        { intros c Hc N2' N8. rewrite /P2 upd_ne; [| regne].
          exact (Heothr c Hc N2' N8). }
        assert (Hpp50 : add_vec_int (mword_of_int (MN + 0x4e) : mword 64) 2
                        = mword_of_int (MN + 0x50)) by pcw.
        iEval (rewrite Hpp50) in "Hpc".
        (* the block goes back whole, the buffer whole, the slot back *)
        iDestruct ("Hpback" with "Hpbare") as "Hpriv".
        iDestruct (iref_slots_combine ns1 1 with "Hir Hislot") as "Hir".
        iDestruct (mn_buf_join (pa_stk sp0 18) bf pk Hpk with "Hbufk Hbufrest")
          as "Hbytes2".
        iDestruct (mn_bytes_name (pa_stk sp0 18) 128 with "Hbytes2") as (bf1) "Hbuf".
        iDestruct (cpu_own_transport CID31 CID32 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (mn_epilogue (CID0 := CID32) m P2 sp0 K b pj _ _ bf1
                  ltac:(lia) Kpop ltac:(reflexivity) HP2sp HP2thr Hal
                  with "Hcg Htext Hpc Hf1 Hf2 Hf19 Hf20 Hbuf
                        [Hown Hbsl Hsbn Hsbi Hsbs Hsbb Hir Hpriv Hcont]").
        iEval (rewrite /wp_next).
        iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CID32 CIDz 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf (ns1 + 1)%nat P' with "[%] [%] Hcg Hown
                  [] [] Hpc Hbsl Hsbn Hsbi Hsbs Hsbb [%] Hir Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt. }
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { cbn in Hns1. lia. }
        { rewrite /sys_mknod_ret. left. rewrite Ha0f. exact HP2a0. }
      + (* ---------- ARM B: create returned 0 ---------- *)
        iDestruct "Hok" as "[%Hcrz Htx]".
        iApply (wp_cbeqz_taken_s_sconf (CID := CID26) (mword_of_int (MN + 0x44))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  mcr (K - 20)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Hcrz; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (smni_44 with "Htext"). }
        iApply bi.later_intro. iIntros (CID27 Hq27) "Hcg Hpc".
        assert (Htg58 : add_vec (mword_of_int (MN + 0x44) : mword 64)
                          (sign_extend' 64
                             (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0"))))
                        = mword_of_int (MN + 0x58)) by pcw.
        iEval (rewrite Htg58) in "Hpc".
        iDestruct (mn_buf_join (pa_stk sp0 18) bf pk Hpk with "Hbufk Hbufrest")
          as "Hbytes2".
        iDestruct (mn_bytes_name (pa_stk sp0 18) 128 with "Hbytes2") as (bf1) "Hbuf".
        iDestruct (proc_priv_bare_acc gf pj pid (upd_upt V P') with "Hpriv")
          as "[Hpbare Hpback]".
        iDestruct (cpu_own_transport CID26 CID27 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (mn_m1_tail (CID0 := CID27) gs j gl gu gd gk pd pav pu bn g fsc_fs
                  dev un1 pid (DfracOwn (1/4))
                  m mcr sp0 K eb b lks _ _ bf1
                  (upd_upt V P') ltac:(lia) ltac:(lia) Kpop Hgeom Hj Hgl Hlkempty
                  ltac:(reflexivity) Hcrsp Hcrthr Hal
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                        Hpbare Hprocs Hdev Hgeo Hdlk [HopS Htx] Hf1 Hf2 Hf19 Hf20
                        Hbuf
                        [Hpback Hbsl Hsbn Hsbi Hsbs Hsbb Hir Hcont]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iApply (log_opS_op with "HopS Htx"). }
        iEval (rewrite /wp_next).
        iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hown _ _ Hpc Hpbare".
        iDestruct ("Hpback" with "Hpbare") as "Hpriv".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf ns1 P' with "[%] [%] Hcg Hown
                  [] [] Hpc Hbsl Hsbn Hsbi Hsbs Hsbb [%] Hir Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt. }
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { cbn in Hns1. exact Hns1. }
        { rewrite /sys_mknod_ret. right. exact Ha0f. }
    - (* ================= ARM A: argstr returned -1 =================
         The [bltz] is TAKEN, straight to the shared "-1" tail at +0x40. *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID19) (mword_of_int (MN + 0x2e))
                (mword_of_int 42 : mword 13) Ra0 mas (K - 20)%nat b
                ltac:(nz) ltac:(rgne; rewrite Hpr; exact mn_m1_neg)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (smni_2e with "Htext"). }
      iApply bi.later_intro. iIntros (CID20 Hq20) "Hcg Hpc".
      assert (Htg58 : add_vec (mword_of_int (MN + 0x2e) : mword 64)
                        (sign_extend' 64 (mword_of_int 42 : mword 13))
                      = mword_of_int (MN + 0x58)) by pcw.
      iEval (rewrite Htg58) in "Hpc".
      iDestruct (word_pointsto_join4 _ _ _ _ Hal19 with "Hmin Hmaj") as "Hf19".
      iDestruct (proc_priv_bare_acc gf pj pid (upd_upt V P') with "Hpriv")
        as "[Hpbare Hpback]".
      iDestruct (cpu_own_transport CID19 CID20 0 eb pj b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (mn_m1_tail (CID0 := CID20) gs j gl gu gd gk pd pav pu bn g fsc_fs
                dev MAXOPBLOCKS pid (DfracOwn (1/4))
                m mas sp0 K eb b lks _ _ bf
                (upd_upt V P') ltac:(lia) ltac:(lia) Kpop Hgeom Hj Hgl Hlkempty
                ltac:(reflexivity) Hassp Hasthr Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hpbare Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf19 Hf20 Hbuf
                      [Hpback Hbsl Hsbn Hsbi Hsbs Hsbb Hir Hcont]").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iEval (rewrite /wp_next).
      iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hown _ _ Hpc Hpbare".
      iDestruct ("Hpback" with "Hpbare") as "Hpriv".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns P' with "[%] [%] Hcg Hown
                [] [] Hpc Hbsl Hsbn Hsbi Hsbs Hsbb [%] Hir Hpriv [%]").
      { exact Hcsf. }
      { exact Hupt. }
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { reflexivity. }
      { rewrite /sys_mknod_ret. right. exact Ha0f. }
  Qed.

End ProofSysMknodBody.

End SysMknodProof.
