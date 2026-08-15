(* ProofSysMkdir.v -- sys_mkdir over the SIE-agnostic sconf world.

     uint64 sys_mkdir(void) {
       char path[MAXPATH];  struct inode *ip;
       begin_op();
       if (argstr(0, path, MAXPATH) < 0 || (ip = create(path, T_DIR, 0, 0)) == 0) {
         end_op(); return -1; }
       iunlockput(ip);  end_op();  return 0;
     }

   72 bytes, 26 instructions, TWO arms that leave through one epilogue.
   Read off CodeSysMkdir.v:

     +0x00  c.addi16sp sp,-144      the eighteen-slot frame
     +0x02  c.sdsp ra,136(sp)       slot 1
     +0x04  c.sdsp s0,128(sp)       slot 2
     +0x06  c.addi4spn s0,sp,144    s0 = the ENTRY sp
     +0x08  jal begin_op
     +0x0c  li a2,128 ; addi a1,s0,-144 ; c.li a0,0 ; jal argstr
     +0x1a  bltz a0 -> +0x40        ARM A: the string did not fetch
     +0x1e  c.li a3,0 ; c.li a2,0 ; c.li a1,1 ; addi a0,s0,-144
     +0x28  jal create              (path, T_DIR, 0, 0)
     +0x2c  c.beqz a0 -> +0x40      ARM B: create failed
     +0x2e  jal iunlockput          a0 IS STILL create's return
     +0x32  jal end_op
     +0x36  c.li a0,0
     +0x38  THE EPILOGUE: ldsp ra / ldsp s0 / addi16sp / ret
     +0x40  jal end_op ; c.li a0,-1 ; c.j +0x38     THE SHARED "-1" TAIL

   THE ONE STRUCTURAL POINT: NOTHING BUT ra AND s0 IS EVER SAVED.  [ip]
   never leaves a0 -- create returns it there and iunlockput's argument is
   already in place -- so there is no [s1] to spill, no arm-local restore,
   and [md_thr] excludes exactly two registers where sys_chdir's excludes
   four.  Every callee-saved register from s1 up rides straight through and
   the final [callee_saved] is eleven applications of one transport.

   THE C SHORT-CIRCUIT IS ONE BLOCK, ENTERED TWICE.  Both disjuncts branch
   to +0x40 directly: the [bltz] at +0x1a (argstr < 0) and the [c.beqz] at
   +0x2c (create == 0).  There is no rejoin instruction between them, which
   is why [md_m1_tail] takes no register-restore premise and both arms
   apply it with the register file they happen to hold.

   THE FRAME CARVE: sixteen of the eighteen slots ARE [char path[128]]
   ([md_frame_carve] / [md_frame_join]) -- slot 18 (the pushed sp) down to
   slot 3.  Nothing about the buffer reaches the contract.

   ==== THE RESOURCE PLAN ================================================

   [proc_priv] is threaded WHOLE and never split, with one exception: the
   pid quarter, which begin_op / iunlockput / end_op each want and which
   [ProcInv.proc_priv_pid] lends and takes straight back.  create takes the
   block whole (it needs p->cwd and the cwd reference for its nameiparent)
   and returns it at the same [V]; argstr returns it at [upd_upt V P'].  So
   the only record change anywhere in this function is argstr's page-table
   growth, and it is relayed verbatim.

   THE LOCKED INODE create HANDS BACK is [SpecCreate.create_locked], which
   is [SpecIunlockput]'s precondition verbatim -- ten conjuncts, destructed
   once at +0x2e and handed straight over.  Nothing inode-shaped survives
   the call, which is why this function's own post mentions none of it.

   ==== THE COMPLEMENT IS DROPPED, NOT THREADED ==========================

   The contract's [eb = true] premise makes [trap_csrs_ext eb] and
   [cpu_claim_ext eb pj] both [emp], and create -- the callee that dominates
   this function -- does not take them at all.  Threading them would demand
   a transport across create's park, which the [true] crossing cannot
   supply, so the walk drops the pair at the top and re-mints it at each
   callee that wants one (begin_op, iunlockput, end_op) and once more for
   the caller's continuation.  That is ProofNamex's device and ProofSysChdir
   uses it for the same reason. *)
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
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn StackBytes.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import PanicStub.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecArgstr.
Require Import SpecFetchstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecDirlookup.
Require Import SpecDirlink.
Require Import SpecCreate.
Require Import CodeSysMkdir.
Require Import SpecSysMkdir.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* a failing tactic in a WP over [proc_priv] otherwise spends tens of
   minutes FORMATTING the goal -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

Notation MD := KernelSyms.sys_mkdir (only parsing).

(* ===================================================================== *)
(*  THE PURE SIDE-CONDITIONS, as closed top-level facts (never run [lia]  *)
(*  or [vm_compute] inside a whole-function context).                     *)
(* ===================================================================== *)

(* the TWO registers this frame moves: sp and s0 (the frame pointer).
   Everything else callee-saved rides straight through, and it is stated
   POSITIVELY -- the two exceptions are exactly the two the code writes,
   each accounted for by its own equation. *)
Definition md_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma md_thr_refl (m : regfile) : md_thr m m.
Proof. intros c _ _ _. reflexivity. Qed.

Lemma md_thr_trans (m M P : regfile) : md_thr m M -> md_thr M P -> md_thr m P.
Proof.
  intros H1 H2 c Hc N2 N8. rewrite (H2 c Hc N2 N8). exact (H1 c Hc N2 N8).
Qed.

Definition md_sp (sp0 : mword 64) (M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk sp0 18.

(* -144 / +144, both a [c.addi16sp] (55 is -9 in a 6-bit field, x16). *)
Lemma md_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 55 : mword 6)))
  = pa_stk X 18.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma md_pop (X : mword 64) :
  add_vec (pa_stk X 18) (sign_extend' 64 (caddi16sp_imm (mword_of_int 9 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,144] -- the frame pointer, back at the entry sp. *)
Lemma md_fp (X : mword 64) :
  add_vec (pa_stk X 18) (sign_extend' 64 (caddi4spn_imm (mword_of_int 36 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi aN,s0,-144] off the frame pointer (which IS the entry sp) is the
   base of the path buffer, i.e. the lowest slot of the frame. *)
Lemma md_buf (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3952 : mword 12)) = pa_stk X 18.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* the c.sdsp / c.ldsp displacements off the pushed sp *)
Lemma md_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (bv_wrap 64 (uint (mword_of_int (- (8 * Z.of_nat 18)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 18) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite pa_stk_off2. apply f_equal. exact H.
Qed.

Lemma md_frm1 (X : mword 64) :
  add_vec (pa_stk X 18)
    (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply md_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma md_frm2 (X : mword 64) :
  add_vec (pa_stk X 18)
    (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply md_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_sys_mkdir's single premise, turned into every bound the four callees
   and the [sie_cap_gpr] pop want. *)
Lemma md_kb (K : nat) : (K_sys_mkdir <= K)%nat ->
  (K_create <= K - 18)%nat /\ (argstr_stack <= K - 18)%nat /\
  (K_begin_op <= K - 18)%nat /\ (K_end_op <= K - 18)%nat /\
  (K_iunlockput <= K - 18)%nat /\
  (18 <= K)%nat /\ ((K - 18) + 18 = K)%nat.
Proof.
  unfold K_sys_mkdir, K_create, argstr_stack, K_begin_op, K_end_op,
         K_iunlockput.
  intro H. split_and!; lia.
Qed.

(* the syscall argument index is in range, and [i = 0] is what a0 holds *)
Lemma md_arg0_lt : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma md_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma md_maxpath_lt : (Z.of_nat 128 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma md_plen_lt (k : nat) : (k < 128)%nat -> (Z.of_nat k < 2 ^ 31)%Z.
Proof. intro H. lia. Qed.

Lemma md_len_range (k : nat) : (k < 128)%nat -> (0 <= Z.of_nat k < 2 ^ 31)%Z.
Proof.
  intro Hk.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* THE [bltz] AT +0x1a, decided.  argstr's answer is [fetchstr_ret]'s
   disjunction, so the branch turns on the SIGN of a value that is either
   [-1] or a length below 128.  ProofSysChdir's cluster, restated here
   rather than imported (a whole-function proof file is not a dependency
   any other one may take). *)
Lemma md_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
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

Lemma md_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (md_sint_moi z Hz). lia.
Qed.

Lemma md_m1_neg :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

(* create's live type premise at [ty := T_DIR], and the two zero arguments *)
Lemma md_tdir_nz : bv_unsigned SpecDirlookup.T_DIR <> 0.
Proof. vm_compute. discriminate. Qed.

(* ===================================================================== *)
(*  THE FRAME: sixteen of the eighteen slots ARE [char path[128]].        *)
(* ===================================================================== *)

Section ProofSysMkdirFrame.
  Context `{!riscvGS Σ}.

  Lemma md_frame_carve (sp0 : mword 64) :
    stack_own sp0 18 -∗
    ⌜forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈ w) ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 18) 128.
  Proof.
    iIntros "H". rewrite stack_own_slots. cbn [seq].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                       H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & _)".
    change 128%nat with (8 * 16)%nat.
    iDestruct (slotsn_bytes_own sp0 18 16 ltac:(lia)
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
    iFrame "H1 H2 Hb". iPureIntro. exact Hal.
  Qed.

  Lemma md_frame_join (sp0 : mword 64) (w1 w2 : mword 64) :
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true) ->
    (pa_stk sp0 1) ↦₈ w1 -∗ (pa_stk sp0 2) ↦₈ w2 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 18) 128 -∗
    stack_own sp0 18.
  Proof.
    intro Hal. iIntros "H1 H2 Hb".
    change 128%nat with (8 * 16)%nat.
    iDestruct (bytes_own_slotsn sp0 18 16 ltac:(lia) Hal with "Hb") as "Hs".
    cbn [seq].
    iDestruct "Hs" as "(K18 & K17 & K16 & K15 & K14 & K13 & K12 & K11 & K10 &
                        K9 & K8 & K7 & K6 & K5 & K4 & K3 & _)".
    rewrite stack_own_slots. cbn [seq].
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
    done.
  Qed.

  (* the buffer, as bytes and back: argstr / create both speak the
     [seq]-indexed byte window, not [bytes_own] *)
  Lemma md_bytes_name (a : mword 64) (N : nat) :
    bytes_own (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j.
  Proof. rewrite /bytes_own. exact (bb_any_named a N). Qed.

  Lemma md_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j) ⊢ bytes_own (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any a N f). Qed.

  (* 128 = (k+1) + (127-k): create reads the NUL-terminated prefix, the rest
     rides through untouched *)
  Lemma md_buf_split (a : mword 64) (f : nat -> bv 8) (k : nat) :
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

  Lemma md_buf_join (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat,
       pa_add (pa_add a (S k)) j ↦ₘ f (S k + j)%nat) -∗
    bytes_own (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (md_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (md_name_bytes (pa_add a (S k)) (127 - k)%nat
                 (fun j => f (S k + j)%nat) with "H2") as "B2".
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite bytes_own_app. iFrame.
  Qed.

End ProofSysMkdirFrame.

(* ===================================================================== *)
(*  +0x38 .. +0x3e : THE EPILOGUE, which both arms leave through.         *)
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

Section ProofSysMkdirEpilogue.
  Context `{!riscvGS Σ, !sieG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma md_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64)
      (bf : nat -> bv 8) :
    (18 <= K)%nat -> ((K - 18) + 18 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    md_sp sp0 M -> md_thr m M ->
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true) ->
    sie_cap_gpr M (K - 18) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (MD + 0x38)) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 18) jj ↦ₘ bf jj) -∗
    (* THE INDEX IS [b], NOT [true], and it has to be: the epilogue is four
       PLAIN instructions, so every crossing it makes is a [b]-link and the
       [b]-form chain is what it can hand back (ProofSysChdir's [sc_epilogue]
       paid for this rule).  A caller whose own continuation is at [true]
       weakens into this for free. *)
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64)⌝ -∗
        sie_cap_gpr mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK18 Kpop Hsp0 HMsp HMthr Hal.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hbuf Hcont".
    iPoseProof (smdi_38 with "Htext") as "Hi38".
    iPoseProof (smdi_3a with "Htext") as "Hi3a".
    iPoseProof (smdi_3c with "Htext") as "Hi3c".
    iPoseProof (smdi_3e with "Htext") as "Hi3e".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HMsp; apply md_frm1).
    (* ===== +0x38 c.ldsp ra,136(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (MD + 0x38))
              (mword_of_int 17 : mword 6) Rra M (K - 18)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi38 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (M1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HM1sp : md_sp sp0 M1)
      by (rewrite /md_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1thr : md_thr m M1).
    { intros c Hc N2 N8. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8). }
    assert (Hpp3a : add_vec_int (mword_of_int (MD + 0x38) : mword 64) 2
                    = mword_of_int (MD + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply md_frm2).
    (* ===== +0x3a c.ldsp s0,128(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (MD + 0x3a))
              (mword_of_int 16 : mword 6) Rs0 M1 (K - 18)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi3a [Hf2]").
    { iEval (rewrite Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    set (M2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> M1).
    assert (HM2sp : md_sp sp0 M2)
      by (rewrite /md_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1ra | nz]).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2thr : md_thr m M2).
    { intros c Hc N2 N8. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8). }
    assert (Hpp3c : add_vec_int (mword_of_int (MD + 0x3a) : mword 64) 2
                    = mword_of_int (MD + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c c.addi16sp sp,144 : the pop ===== *)
    assert (Hwv : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 9 : mword 6)))
                  = sp0)
      by (rewrite HM2sp; apply md_pop).
    assert (Hpop : (M2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 9 : mword 6)))) 18)
      by (rewrite Hwv HM2sp; reflexivity).
    iDestruct (md_name_bytes (pa_stk sp0 18) 128 bf with "Hbuf") as "Hbytes".
    iDestruct (md_frame_join sp0 _ _ Hal with "Hf1 Hf2 Hbytes") as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (MD + 0x3c))
              (mword_of_int 9 : mword 6) M2 (K - 18)%nat 18 b Hpop
              with "Hcg Hpc Hi3c Hstk").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (M3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 9 : mword 6))))]> M2).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp3e : add_vec_int (mword_of_int (MD + 0x3c) : mword 64) 2
                    = mword_of_int (MD + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    (* ===== +0x3e c.ret ===== *)
    iApply (wp_cret_s_sconf (mword_of_int (MD + 0x3e)) Rra M3 K b
              ltac:(nz) with "Hcg Hpc Hi3e").
    iIntros (CID4 Hq4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HM3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE HANDOVER ===== *)
    assert (Hwv' : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 9 : mword 6)))
                   = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite Hwv; exact Hsp0).
    assert (Csp : (M3 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /M3 upd_eq; exact Hwv').
    assert (Cs0 : (M3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2a0 | nz]).
    assert (Hfin : md_thr m M3).
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

End ProofSysMkdirEpilogue.

(* ===================================================================== *)
(*  THE FUNCTOR.  Everything from here down applies a callee's contract,   *)
(*  so it lives inside the module the seal instantiates.                   *)
(* ===================================================================== *)
Module SysMkdirProof (BeginOp : BEGIN_OP) (Argstr : ARGSTR) (Create : CREATE)
                     (Iunlockput : IUNLOCKPUT) (EndOp : END_OP)
  : SYSMKDIR.

(* ===================================================================== *)
(*  +0x40 .. +0x46 : THE SHARED "-1" TAIL.                                *)
(*                                                                        *)
(*  end_op, [c.li a0,-1], and the [c.j] back into the epilogue.  BOTH     *)
(*  arms of the C-level [||] reach it and they reach it DIRECTLY -- the    *)
(*  [bltz] at +0x1a and the [c.beqz] at +0x2c both target +0x40, with no   *)
(*  intervening restore, which is why this lemma takes no register premise *)
(*  beyond the two the epilogue below it wants.                           *)
(* ===================================================================== *)
Section ProofSysMkdirM1Tail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma md_m1_tail `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (bf : nat -> bv 8) :
    (K_end_op <= K - 18)%nat -> (18 <= K)%nat -> ((K - 18) + 18 = K)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    md_sp sp0 M -> md_thr m M ->
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (18 - i)%nat)) 8 = true) ->
    sie_cap_gpr M (K - 18) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ pc_is (mword_of_int (MD + 0x40)) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 18) jj ↦ₘ bf jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKeo HK18 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr Hal.
    iIntros "Hcg Hown Htce Hcce #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hbuf Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (smdi_40 with "Htext") as "Hi40".
    iPoseProof (smdi_44 with "Htext") as "Hi44".
    iPoseProof (smdi_46 with "Htext") as "Hi46".
    (* ===== +0x40 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (MD + 0x40)) Rra
              (mword_of_int 2091624 : mword 21) M (K - 18)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi40").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (MD + 0x40) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (MD + 0x40) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091624 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (MD + 0x40) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : md_sp sp0 M1)
      by (rewrite /md_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1thr : md_thr m M1).
    { intros c Hc N2 N8. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M1 (K - 18)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(lkbelow)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc44 : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (MD + 0x44)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpc44) in "Hpc".
    assert (Heosp : md_sp sp0 meo).
    { rewrite /md_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heothr : md_thr m meo).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8). }
    (* ===== +0x44 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (MD + 0x44)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 18)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi44").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : md_sp sp0 P1)
      by (rewrite /md_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1thr : md_thr m P1).
    { intros c Hc N2 N8. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8). }
    assert (Hpp46 : add_vec_int (mword_of_int (MD + 0x44) : mword 64) 2
                    = mword_of_int (MD + 0x46)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    (* ===== +0x46 c.j +0x38 ===== *)
    iApply (wp_cj_s_sconf (CID := CID3) (mword_of_int (MD + 0x46))
              (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")))
              P1 (K - 18)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi46").
    iIntros (CID4 Hq4). iNext. iIntros "Hcg Hpc".
    assert (Htg38 : add_vec (mword_of_int (MD + 0x46) : mword 64)
                      (sign_extend' 64
                         (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
                    = mword_of_int (MD + 0x38)) by pcw.
    iEval (rewrite Htg38) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID2 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID2 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (md_epilogue (CID0 := CID4) m P1 sp0 K b (proc_addr jx) bf
              HK18 Kpop Hsp0 HP1sp HP1thr Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hbuf [Hown Htce Hcce Hpid Hcont]").
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

End ProofSysMkdirM1Tail.

(* ===================================================================== *)
(*  THE WALK: +0x00 .. +0x36, the two arms and the success tail.          *)
(* ===================================================================== *)

Section ProofSysMkdirBody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).

  (* the per-slot projection out of the boot family, at the copy THIS
     contract names ([ic_escrows] is IcacheEscrow's -- see fs-sysfile's
     trap 3 on the four [ic_sleeplocks] copies, which bites the same way). *)
  Lemma md_esc_acc (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn gfs gi cov logstart -∗ ic_escrow cn gfs gi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma wp_sys_mkdir_sconf `{GEN : GenId} `{CID0 : CpuId}
      (gf ga gpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_sys_mkdir_sconf_body gf ga gpr gs j gl gu gd gk pd pav pu bn g gfs gi
                            cn gtl cov logstart bmapstart inodestart nib
                            ninodes size dev used ns dqb dqs dqbs dqn v
                            pid V m K eb b lks.
  Proof.
    cbv beta delta [wp_sys_mkdir_sconf_body].
    intros pcE pj ret_tgt HK Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom
           Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb
           Hni1 Hni2 Hni3 Hush Hpkc Hnsb Hj Hgl Heb Hargv.
    destruct (md_kb K HK) as (Kcr & Kar & Kbo & Keo & Kiup & K18 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hpanic #Hpre #Hbio #Hlog Hseam
             Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks
             #Hireg Hsbn Hsbi Hsbs Hsbb Hbmres #Hkenv #Hprocs Hir Hpriv Hcont".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    iPoseProof (smdi_00 with "Htext") as "Hi00".
    iPoseProof (smdi_02 with "Htext") as "Hi02".
    iPoseProof (smdi_04 with "Htext") as "Hi04".
    iPoseProof (smdi_06 with "Htext") as "Hi06".
    iPoseProof (smdi_08 with "Htext") as "Hi08".
    iPoseProof (smdi_0c with "Htext") as "Hi0c".
    iPoseProof (smdi_10 with "Htext") as "Hi10".
    iPoseProof (smdi_14 with "Htext") as "Hi14".
    iPoseProof (smdi_16 with "Htext") as "Hi16".
    iPoseProof (smdi_1a with "Htext") as "Hi1a".
    iPoseProof (smdi_1e with "Htext") as "Hi1e".
    iPoseProof (smdi_20 with "Htext") as "Hi20".
    iPoseProof (smdi_22 with "Htext") as "Hi22".
    iPoseProof (smdi_24 with "Htext") as "Hi24".
    iPoseProof (smdi_28 with "Htext") as "Hi28".
    iPoseProof (smdi_2c with "Htext") as "Hi2c".
    iPoseProof (smdi_2e with "Htext") as "Hi2e".
    iPoseProof (smdi_32 with "Htext") as "Hi32".
    iPoseProof (smdi_36 with "Htext") as "Hi36".
    (* ================= +0x00 c.addi16sp sp,-144 ================= *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 55 : mword 6) m K 18 b
              ltac:(lia) (md_push sp0) with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 55 : mword 6))))]> m).
    assert (HM1sp : md_sp sp0 M1).
    { unfold md_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply md_push ]. }
    assert (HM1thr : md_thr m M1).
    { intros c Hc N2 N8. rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (MD + 0x02))
      by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* the carve: sixteen of the eighteen slots ARE [char path[128]] *)
    iDestruct (md_frame_carve sp0 with "Hframe")
      as "(%Hal & [%u1 Hf1] & [%u2 Hf2] & Hbytes)".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply md_frm1).
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply md_frm2).
    (* ================= +0x02 c.sdsp ra,136(sp) ================= *)
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (MD + 0x02))
              (mword_of_int 17 : mword 6) Rra M1 (K - 18)%nat u1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (MD + 0x02) : mword 64) 2
                    = mword_of_int (MD + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ================= +0x04 c.sdsp s0,128(sp) ================= *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (MD + 0x04))
              (mword_of_int 16 : mword 6) Rs0 M1 (K - 18)%nat u2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rgne; rewrite Hc2 HM1s0) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (MD + 0x04) : mword 64) 2
                    = mword_of_int (MD + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ================= +0x06 c.addi4spn s0,sp,144 ================= *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (MD + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 36 : mword 8) Rs0
              M1 (K - 18)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 36 : mword 8))))]> M1).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { etransitivity; [ rewrite /M2; apply upd_eq |].
      rewrite HM1sp. apply md_fp. }
    assert (HM2sp : md_sp sp0 M2)
      by (rewrite /md_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : md_thr m M2).
    { intros c Hc N2 N8. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8). }
    assert (Hpp08 : add_vec_int (mword_of_int (MD + 0x06) : mword 64) 2
                    = mword_of_int (MD + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ================= +0x08 jal ra,begin_op ================= *)
    iApply (wp_jal_s_sconf (CID := CID4) (mword_of_int (MD + 0x08)) Rra
              (mword_of_int 2091540 : mword 21) M2 (K - 18)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (MD + 0x08) : mword 64) 4)]> M2).
    assert (Hjbo : add_vec (mword_of_int (MD + 0x08) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091540 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iEval (rewrite Hjbo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (MD + 0x08) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : md_sp sp0 M3)
      by (rewrite /md_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3thr : md_thr m M3).
    { intros c Hc N2 N8. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8). }
    (* the pid quarter, LENT across begin_op and taken straight back *)
    iDestruct (proc_priv_pid gf pj pid V with "Hpriv") as "[Hpidq Hpback0]".
    iDestruct (cpu_own_transport CID0 CID5 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (BeginOp.wp_begin_op_sconf (CID := CID5) gs j gl bn g gfs cov logstart
              dev pid (DfracOwn (1/4)) M3 (K - 18)%nat eb b lks
              ltac:(lia) Hj Hgl (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hpanic Hlog Hpidq Hprocs").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID6 Hq6 mbo) "%Hcsbo Hcg Hown _ _ Hpc Hpidq Hop".
    assert (Hpc0c : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = mword_of_int (MD + 0x0c)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc0c) in "Hpc".
    iDestruct ("Hpback0" with "Hpidq") as "Hpriv".
    assert (Hbosp : md_sp sp0 mbo).
    { rewrite /md_sp (callee_saved_lookup Hcsbo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Hbos0 : (mbo !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsbo Rs0 ltac:(vm_compute; reflexivity)).
      exact HM3s0. }
    assert (Hbothr : md_thr m mbo).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcsbo c Hc).
      exact (HM3thr c Hc N2 N8). }
    (* ================= +0x0c li a2,128 ================= *)
    iApply (wp_li4_s_sconf (CID := CID6) (mword_of_int (MD + 0x0c)) Ra2
              (mword_of_int 128 : mword 12)
              (mword_of_int (Z.of_nat 128) : mword 64) mbo (K - 18)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi0c").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M4 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 128) : mword 64)]> mbo).
    assert (HM4a2 : (M4 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4sp : md_sp sp0 M4)
      by (rewrite /md_sp /M4 upd_ne; [exact Hbosp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact Hbos0 | nz]).
    assert (HM4thr : md_thr m M4).
    { intros c Hc N2 N8. rewrite /M4 upd_ne; [| regne].
      exact (Hbothr c Hc N2 N8). }
    assert (Hpp10 : add_vec_int (mword_of_int (MD + 0x0c) : mword 64) 4
                    = mword_of_int (MD + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ================= +0x10 addi a1,s0,-144 ================= *)
    iApply (wp_addi4_s_sconf (CID := CID7) (mword_of_int (MD + 0x10)) Ra1 Rs0
              (mword_of_int 3952 : mword 12) M4 (K - 18)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (M5 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M4 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3952 : mword 12)))]> M4).
    assert (HM5a1 : (M5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 18).
    { etransitivity; [ rewrite /M5; apply upd_eq |].
      rewrite HM4s0. apply md_buf. }
    assert (HM5a2 : (M5 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a2 | nz]).
    assert (HM5sp : md_sp sp0 M5)
      by (rewrite /md_sp /M5 upd_ne; [exact HM4sp | nz]).
    assert (HM5s0 : (M5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M5 upd_ne; [exact HM4s0 | nz]).
    assert (HM5thr : md_thr m M5).
    { intros c Hc N2 N8. rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2 N8). }
    assert (Hpp14 : add_vec_int (mword_of_int (MD + 0x10) : mword 64) 4
                    = mword_of_int (MD + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ================= +0x14 c.li a0,0 ================= *)
    iApply (wp_cli_s_sconf (CID := CID8) (mword_of_int (MD + 0x14)) Ra0
              (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M5 (K - 18)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi14").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M6 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> M5).
    assert (HM6a0 : (M6 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M6; apply upd_eq).
    assert (HM6a1 : (M6 !!! Regidx Ra1 : mword 64) = pa_stk sp0 18)
      by (rewrite /M6 upd_ne; [exact HM5a1 | nz]).
    assert (HM6a2 : (M6 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a2 | nz]).
    assert (HM6sp : md_sp sp0 M6)
      by (rewrite /md_sp /M6 upd_ne; [exact HM5sp | nz]).
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M6 upd_ne; [exact HM5s0 | nz]).
    assert (HM6thr : md_thr m M6).
    { intros c Hc N2 N8. rewrite /M6 upd_ne; [| regne].
      exact (HM5thr c Hc N2 N8). }
    assert (Hpp16 : add_vec_int (mword_of_int (MD + 0x14) : mword 64) 2
                    = mword_of_int (MD + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ================= +0x16 jal ra,argstr ================= *)
    iApply (wp_jal_s_sconf (CID := CID9) (mword_of_int (MD + 0x16)) Rra
              (mword_of_int 2086466 : mword 21) M6 (K - 18)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (M7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (MD + 0x16) : mword 64) 4)]> M6).
    assert (Hjas : add_vec (mword_of_int (MD + 0x16) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086466 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iEval (rewrite Hjas) in "Hpc".
    assert (HM7ra : (M7 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (MD + 0x16) : mword 64) 4)
      by (rewrite /M7; apply upd_eq).
    assert (HM7a0 : (M7 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6a0 | nz]).
    assert (HM7a1 : (M7 !!! Regidx Ra1 : mword 64) = pa_stk sp0 18)
      by (rewrite /M7 upd_ne; [exact HM6a1 | nz]).
    assert (HM7a2 : (M7 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6a2 | nz]).
    assert (HM7sp : md_sp sp0 M7)
      by (rewrite /md_sp /M7 upd_ne; [exact HM6sp | nz]).
    assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M7 upd_ne; [exact HM6s0 | nz]).
    assert (HM7thr : md_thr m M7).
    { intros c Hc N2 N8. rewrite /M7 upd_ne; [| regne].
      exact (HM6thr c Hc N2 N8). }
    (* the buffer, as the byte window argstr speaks *)
    iDestruct (md_bytes_name (pa_stk sp0 18) 128 with "Hbytes") as (bf0) "Hbuf".
    iDestruct (cpu_own_transport CID6 CID10 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argstr.wp_argstr_sconf (CID := CID10) ga gf M7 (K - 18)%nat 0%nat eb pj
              0%nat v pid V 128%nat bf0 b lks
              md_arg0_lt HM7a0 Hargv md_noff0 ltac:(lia) HM7a2 md_maxpath_lt
              (Hlb "kmem"%string)
              with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [Hbuf]").
    { iEval (rewrite HM7a1). iExact "Hbuf". }
    iIntros (CID11 Hq11 mas P' bf) "%Hcsas %Hupt Hcg Hown Hpc Hpriv Hbuf %Hfsr".
    iEval (rewrite HM7a1) in "Hbuf".
    assert (Hpc1a : ret_pc (M7 !!! Regidx Rra : mword 64)
                    = mword_of_int (MD + 0x1a)) by (rewrite HM7ra; pcw).
    iEval (rewrite Hpc1a) in "Hpc".
    assert (Hassp : md_sp sp0 mas).
    { rewrite /md_sp (callee_saved_lookup Hcsas csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM7sp. }
    assert (Hass0 : (mas !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsas Rs0 ltac:(vm_compute; reflexivity)).
      exact HM7s0. }
    assert (Hasthr : md_thr m mas).
    { intros c Hc N2 N8. rewrite (callee_saved_lookup Hcsas c Hc).
      exact (HM7thr c Hc N2 N8). }
    (* ================= +0x1a bltz a0 -> ARM A ================= *)
    destruct Hfsr as [(pk & Hpk & Hpcstr & Hpr) | Hpr].
    - (* ---- the string fetched: the [bltz] FALLS THROUGH ---- *)
      iApply (wp_blt_x0_fall_s_sconf (CID := CID11) (mword_of_int (MD + 0x1a))
                (mword_of_int 38 : mword 13) Ra0 mas (K - 18)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Hpr; exact (md_nonneg _ (md_len_range pk Hpk)))
                with "Hcg Hpc Hi1a").
      iIntros (CID12 Hq12) "Hcg Hpc".
      assert (Hpp1e : add_vec_int (mword_of_int (MD + 0x1a) : mword 64) 4
                      = mword_of_int (MD + 0x1e)) by pcw.
      iEval (rewrite Hpp1e) in "Hpc".
      (* ============ +0x1e c.li a3,0 : minor ============ *)
      iApply (wp_cli_s_sconf (CID := CID12) (mword_of_int (MD + 0x1e)) Ra3
                (mword_of_int 0 : mword 6)
                (sign_extend' 64 (mword_of_int 0 : mword 16)) mas (K - 18)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi1e").
      iIntros (CID13 Hq13) "Hcg Hpc".
      set (N0 := <[Regidx Ra3 := regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 16))]> mas).
      assert (HN0a3 : (N0 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N0; apply upd_eq).
      assert (HN0sp : md_sp sp0 N0)
        by (rewrite /md_sp /N0 upd_ne; [exact Hassp | nz]).
      assert (HN0s0 : (N0 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N0 upd_ne; [exact Hass0 | nz]).
      assert (HN0thr : md_thr m N0).
      { intros c Hc N2 N8. rewrite /N0 upd_ne; [| regne].
        exact (Hasthr c Hc N2 N8). }
      assert (Hpp20 : add_vec_int (mword_of_int (MD + 0x1e) : mword 64) 2
                      = mword_of_int (MD + 0x20)) by pcw.
      iEval (rewrite Hpp20) in "Hpc".
      (* ============ +0x20 c.li a2,0 : major ============ *)
      iApply (wp_cli_s_sconf (CID := CID13) (mword_of_int (MD + 0x20)) Ra2
                (mword_of_int 0 : mword 6)
                (sign_extend' 64 (mword_of_int 0 : mword 16)) N0 (K - 18)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi20").
      iIntros (CID14 Hq14) "Hcg Hpc".
      set (N1 := <[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 16))]> N0).
      assert (HN1a2 : (N1 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N1; apply upd_eq).
      assert (HN1a3 : (N1 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N1 upd_ne; [exact HN0a3 | nz]).
      assert (HN1sp : md_sp sp0 N1)
        by (rewrite /md_sp /N1 upd_ne; [exact HN0sp | nz]).
      assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N1 upd_ne; [exact HN0s0 | nz]).
      assert (HN1thr : md_thr m N1).
      { intros c Hc N2 N8. rewrite /N1 upd_ne; [| regne].
        exact (HN0thr c Hc N2 N8). }
      assert (Hpp22 : add_vec_int (mword_of_int (MD + 0x20) : mword 64) 2
                      = mword_of_int (MD + 0x22)) by pcw.
      iEval (rewrite Hpp22) in "Hpc".
      (* ============ +0x22 c.li a1,1 : T_DIR ============ *)
      iApply (wp_cli_s_sconf (CID := CID14) (mword_of_int (MD + 0x22)) Ra1
                (mword_of_int 1 : mword 6)
                (sign_extend' 64 SpecDirlookup.T_DIR) N1 (K - 18)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi22").
      iIntros (CID15 Hq15) "Hcg Hpc".
      set (N2 := <[Regidx Ra1 := regval_into_reg
                    (sign_extend' 64 SpecDirlookup.T_DIR)]> N1).
      assert (HN2a1 : (N2 !!! Regidx Ra1 : mword 64)
                      = (sign_extend' 64 SpecDirlookup.T_DIR))
        by (rewrite /N2; apply upd_eq).
      assert (HN2a2 : (N2 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N2 upd_ne; [exact HN1a2 | nz]).
      assert (HN2a3 : (N2 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N2 upd_ne; [exact HN1a3 | nz]).
      assert (HN2sp : md_sp sp0 N2)
        by (rewrite /md_sp /N2 upd_ne; [exact HN1sp | nz]).
      assert (HN2s0 : (N2 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N2 upd_ne; [exact HN1s0 | nz]).
      assert (HN2thr : md_thr m N2).
      { intros c Hc N2' N8. rewrite /N2 upd_ne; [| regne].
        exact (HN1thr c Hc N2' N8). }
      assert (Hpp24 : add_vec_int (mword_of_int (MD + 0x22) : mword 64) 2
                      = mword_of_int (MD + 0x24)) by pcw.
      iEval (rewrite Hpp24) in "Hpc".
      (* ============ +0x24 addi a0,s0,-144 ============ *)
      iApply (wp_addi4_s_sconf (CID := CID15) (mword_of_int (MD + 0x24)) Ra0 Rs0
                (mword_of_int 3952 : mword 12) N2 (K - 18)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24").
      iIntros (CID16 Hq16) "Hcg Hpc".
      set (N3 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (N2 !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 3952 : mword 12)))]> N2).
      assert (HN3a0 : (N3 !!! Regidx Ra0 : mword 64) = pa_stk sp0 18).
      { etransitivity; [ rewrite /N3; apply upd_eq |].
        rewrite HN2s0. apply md_buf. }
      assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64)
                      = (sign_extend' 64 SpecDirlookup.T_DIR))
        by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
      assert (HN3a2 : (N3 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N3 upd_ne; [exact HN2a2 | nz]).
      assert (HN3a3 : (N3 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N3 upd_ne; [exact HN2a3 | nz]).
      assert (HN3sp : md_sp sp0 N3)
        by (rewrite /md_sp /N3 upd_ne; [exact HN2sp | nz]).
      assert (HN3s0 : (N3 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N3 upd_ne; [exact HN2s0 | nz]).
      assert (HN3thr : md_thr m N3).
      { intros c Hc N2' N8. rewrite /N3 upd_ne; [| regne].
        exact (HN2thr c Hc N2' N8). }
      assert (Hpp28 : add_vec_int (mword_of_int (MD + 0x24) : mword 64) 4
                      = mword_of_int (MD + 0x28)) by pcw.
      iEval (rewrite Hpp28) in "Hpc".
      (* ============ +0x28 jal ra,create ============ *)
      iApply (wp_jal_s_sconf (CID := CID16) (mword_of_int (MD + 0x28)) Rra
                (mword_of_int 2095406 : mword 21) N3 (K - 18)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28").
      iIntros (CID17 Hq17) "Hcg Hpc".
      set (N4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (MD + 0x28) : mword 64) 4)]> N3).
      assert (Hjcr : add_vec (mword_of_int (MD + 0x28) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095406 : mword 21))
                     = mword_of_int KernelSyms.create) by pcw.
      iEval (rewrite Hjcr) in "Hpc".
      assert (HN4ra : (N4 !!! Regidx Rra : mword 64)
                      = add_vec_int (mword_of_int (MD + 0x28) : mword 64) 4)
        by (rewrite /N4; apply upd_eq).
      assert (HN4a0 : (N4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 18)
        by (rewrite /N4 upd_ne; [exact HN3a0 | nz]).
      assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64)
                      = (sign_extend' 64 SpecDirlookup.T_DIR))
        by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
      assert (HN4a2 : (N4 !!! Regidx Ra2 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N4 upd_ne; [exact HN3a2 | nz]).
      assert (HN4a3 : (N4 !!! Regidx Ra3 : mword 64)
                      = (sign_extend' 64 (mword_of_int 0 : mword 16)))
        by (rewrite /N4 upd_ne; [exact HN3a3 | nz]).
      assert (HN4sp : md_sp sp0 N4)
        by (rewrite /md_sp /N4 upd_ne; [exact HN3sp | nz]).
      assert (HN4s0 : (N4 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N4 upd_ne; [exact HN3s0 | nz]).
      assert (HN4thr : md_thr m N4).
      { intros c Hc N2' N8. rewrite /N4 upd_ne; [| regne].
        exact (HN3thr c Hc N2' N8). }
      iDestruct (md_buf_split (pa_stk sp0 18) bf pk Hpk with "Hbuf")
        as "[Hbufk Hbufrest]".
      iDestruct "Hop" as (Sb0) "HopS".
      iDestruct (cpu_own_transport CID11 CID17 0 eb pj b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Create.wp_create_sconf (CID := CID17) gs j gl gu gd gk pd pav pu
                bn g gfs gi cn gtl ga gf gpr cov logstart bmapstart inodestart
                nib ninodes size dev used pk bf
                SpecDirlookup.T_DIR (mword_of_int 0) (mword_of_int 0)
                (upd_upt V P') MAXOPBLOCKS Sb0 ns pid dqb dqs dqbs dqn
                N4 (K - 18)%nat eb b lks
                ltac:(lia) Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom Hsize
                Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr
                (md_plen_lt pk Hpk) Hni1 Hni2 Hni3 Hush md_tdir_nz Hpkc
                ltac:(unfold create_units; lia) Hnsb Hj Hgl
                HN4a1 HN4a2 HN4a3 Heb
                with "Hcg Hown Htext Hpc Hpanic Hdata Hpre Hbio Hlog Hkenv
                      Hitab Hitinv Hescrows Hslks Hireg Hsbn Hsbi Hsbs Hsbb
                      Hbmres Hpriv [Hbufk] Hprocs Hdev Hgeo Hdlk Hbsl Hir HopS").
      { iEval (rewrite HN4a0). iExact "Hbufk". }
      iIntros (CID18 Hq18 mcr ok made kk qi ss gy inum dn bm un1 Sb1 ns1 used1)
        "%Hcscr Hcg Hown Hpc Hsbn Hsbi Hsbs Hsbb Hbmres Hpriv Hbufk Hbsl
         %Hns1 Hir %Hun1 HopS Hok".
      iEval (rewrite HN4a0) in "Hbufk".
      assert (Hpc2c : ret_pc (N4 !!! Regidx Rra : mword 64)
                      = mword_of_int (MD + 0x2c)) by (rewrite HN4ra; pcw).
      iEval (rewrite Hpc2c) in "Hpc".
      assert (Hcrsp : md_sp sp0 mcr).
      { rewrite /md_sp (callee_saved_lookup Hcscr csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HN4sp. }
      assert (Hcrthr : md_thr m mcr).
      { intros c Hc N2' N8. rewrite (callee_saved_lookup Hcscr c Hc).
        exact (HN4thr c Hc N2' N8). }
      (* ============ +0x2c c.beqz a0 -> ARM B ============ *)
      destruct ok.
      + (* ---------- create SUCCEEDED: the LOCKED inode ---------- *)
        iDestruct "Hok" as "[%Hokf Hlocked]".
        destruct Hokf as (Hcra0 & Hkk & Hinum & _).
        assert (Hipnz : ientry kk <> (zero_reg : mword 64))
          by (apply ientry_ne_zero; lia).
        iApply (wp_cbeqz_fall_s_sconf (CID := CID18) (mword_of_int (MD + 0x2c))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  mcr (K - 18)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Hcra0;
                        apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
                  with "Hcg Hpc Hi2c").
        iIntros (CID19 Hq19) "Hcg Hpc".
        assert (Hpp2e : add_vec_int (mword_of_int (MD + 0x2c) : mword 64) 2
                        = mword_of_int (MD + 0x2e)) by pcw.
        iEval (rewrite Hpp2e) in "Hpc".
        (* ============ +0x2e jal ra,iunlockput ============ *)
        iApply (wp_jal_s_sconf (CID := CID19) (mword_of_int (MD + 0x2e)) Rra
                  (mword_of_int 2089432 : mword 21) mcr (K - 18)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi2e").
        iIntros (CID20 Hq20) "Hcg Hpc".
        set (P0 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (MD + 0x2e) : mword 64) 4)]> mcr).
        assert (Hjiu : add_vec (mword_of_int (MD + 0x2e) : mword 64)
                         (sign_extend' 64 (mword_of_int 2089432 : mword 21))
                       = mword_of_int KernelSyms.iunlockput) by pcw.
        iEval (rewrite Hjiu) in "Hpc".
        assert (HP0ra : (P0 !!! Regidx Rra : mword 64)
                        = add_vec_int (mword_of_int (MD + 0x2e) : mword 64) 4)
          by (rewrite /P0; apply upd_eq).
        assert (HP0a0 : (P0 !!! Regidx Ra0 : mword 64) = ientry kk)
          by (rewrite /P0 upd_ne; [exact Hcra0 | nz]).
        assert (HP0sp : md_sp sp0 P0)
          by (rewrite /md_sp /P0 upd_ne; [exact Hcrsp | nz]).
        assert (HP0thr : md_thr m P0).
        { intros c Hc N2' N8. rewrite /P0 upd_ne; [| regne].
          exact (Hcrthr c Hc N2' N8). }
        (* the ten conjuncts create hands back ARE iunlockput's precondition *)
        iDestruct "Hlocked" as (gil gisl)
          "(Hslk & Hslkd & Hslpid & Hdep & Hidev & Hiinum & Hivalid & Hload &
            Hshot & Href)".
        iDestruct (md_esc_acc cn gfs gi cov logstart kk ltac:(lia)
                     with "Hescrows") as "#Hesc".
        destruct (Hiregb inum ltac:(lia)) as [Hibcov Hiblog].
        iDestruct (proc_priv_pid gf pj pid (upd_upt V P') with "Hpriv")
          as "[Hpidq Hpback]".
        iDestruct (cpu_own_transport CID18 CID20 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Iunlockput.wp_iunlockput_sconf (CID := CID20) gs j gl gu gd gk
                  pd pav pu bn g gfs gi cn gtl gil gisl cov logstart bmapstart
                  inodestart nib size dev used1 kk qi ss gy inum dn bm un1
                  pid (DfracOwn (1/4)) dqb dqs P0 (K - 18)%nat eb b lks
                  ltac:(lia) ltac:(lia) Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                  Hibcov Hiblog ltac:(lia) Hcovb
                  ltac:(exact (proj2 (proj2 Hun1) eq_refl)) Hj Hgl HP0a0
                  (Hlb "log"%string)
                  with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hlog Hitab Hitinv
                        Hesc Hireg Hslk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                        Hload Hshot Href Hsbb Hsbi Hbmres Hpidq Hprocs Hdev
                        Hgeo Hdlk Hbsl [HopS]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iApply (log_opS_op with "HopS"). }
        iIntros (CID21 Hq21 miu n2 used2)
          "%Hcsiu Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
           Hop Hislot".
        assert (Hpc32 : ret_pc (P0 !!! Regidx Rra : mword 64)
                        = mword_of_int (MD + 0x32)) by (rewrite HP0ra; pcw).
        iEval (rewrite Hpc32) in "Hpc".
        assert (Hiusp : md_sp sp0 miu).
        { rewrite /md_sp (callee_saved_lookup Hcsiu csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HP0sp. }
        assert (Hiuthr : md_thr m miu).
        { intros c Hc N2' N8. rewrite (callee_saved_lookup Hcsiu c Hc).
          exact (HP0thr c Hc N2' N8). }
        (* ============ +0x32 jal ra,end_op ============ *)
        iApply (wp_jal_s_sconf (CID := CID21) (mword_of_int (MD + 0x32)) Rra
                  (mword_of_int 2091638 : mword 21) miu (K - 18)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi32").
        iIntros (CID22 Hq22) "Hcg Hpc".
        set (P1 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (MD + 0x32) : mword 64) 4)]> miu).
        assert (Hjeo : add_vec (mword_of_int (MD + 0x32) : mword 64)
                         (sign_extend' 64 (mword_of_int 2091638 : mword 21))
                       = mword_of_int KernelSyms.end_op) by pcw.
        iEval (rewrite Hjeo) in "Hpc".
        assert (HP1ra : (P1 !!! Regidx Rra : mword 64)
                        = add_vec_int (mword_of_int (MD + 0x32) : mword 64) 4)
          by (rewrite /P1; apply upd_eq).
        assert (HP1sp : md_sp sp0 P1)
          by (rewrite /md_sp /P1 upd_ne; [exact Hiusp | nz]).
        assert (HP1thr : md_thr m P1).
        { intros c Hc N2' N8. rewrite /P1 upd_ne; [| regne].
          exact (Hiuthr c Hc N2' N8). }
        iDestruct (cpu_own_transport CID21 CID22 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (EndOp.wp_end_op_sconf (CID := CID22) gs j gl gu gd gk pd pav pu
                  bn g gfs cov logstart dev n2 pid (DfracOwn (1/4))
                  P1 (K - 18)%nat eb b lks
                  ltac:(lia) Hgeom Hj Hgl (Hlb "log"%string)
                  with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                        Hpidq Hprocs Hdev Hgeo Hdlk Hop").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        iIntros (CID23 Hq23 meo) "%Hcseo Hcg Hown _ _ Hpc Hpidq".
        assert (Hpc36 : ret_pc (P1 !!! Regidx Rra : mword 64)
                        = mword_of_int (MD + 0x36)) by (rewrite HP1ra; pcw).
        iEval (rewrite Hpc36) in "Hpc".
        assert (Heosp : md_sp sp0 meo).
        { rewrite /md_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HP1sp. }
        assert (Heothr : md_thr m meo).
        { intros c Hc N2' N8. rewrite (callee_saved_lookup Hcseo c Hc).
          exact (HP1thr c Hc N2' N8). }
        (* ============ +0x36 c.li a0,0 ============ *)
        iApply (wp_cli_s_sconf (CID := CID23) (mword_of_int (MD + 0x36)) Ra0
                  (mword_of_int 0 : mword 6) (zero_reg : mword 64)
                  meo (K - 18)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi36").
        iIntros (CID24 Hq24) "Hcg Hpc".
        set (P2 := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> meo).
        assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (zero_reg : mword 64))
          by (rewrite /P2; apply upd_eq).
        assert (HP2sp : md_sp sp0 P2)
          by (rewrite /md_sp /P2 upd_ne; [exact Heosp | nz]).
        assert (HP2thr : md_thr m P2).
        { intros c Hc N2' N8. rewrite /P2 upd_ne; [| regne].
          exact (Heothr c Hc N2' N8). }
        assert (Hpp38 : add_vec_int (mword_of_int (MD + 0x36) : mword 64) 2
                        = mword_of_int (MD + 0x38)) by pcw.
        iEval (rewrite Hpp38) in "Hpc".
        (* the block goes back whole, the buffer whole, the slot back *)
        iDestruct ("Hpback" with "Hpidq") as "Hpriv".
        iDestruct (iref_slots_combine ns1 1 with "Hir Hislot") as "Hir".
        iDestruct (md_buf_join (pa_stk sp0 18) bf pk Hpk with "Hbufk Hbufrest")
          as "Hbytes2".
        iDestruct (md_bytes_name (pa_stk sp0 18) 128 with "Hbytes2") as (bf1) "Hbuf".
        iDestruct (cpu_own_transport CID23 CID24 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (md_epilogue (CID0 := CID24) m P2 sp0 K b pj bf1
                  ltac:(lia) Kpop ltac:(reflexivity) HP2sp HP2thr Hal
                  with "Hcg Htext Hpc Hf1 Hf2 Hbuf
                        [Hown Hbsl Hsbn Hsbi Hsbs Hsbb Hbmres Hir Hpriv Hcont]").
        iEval (rewrite /wp_next).
        iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CID24 CIDz 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf used2 (ns1 + 1)%nat P' with "[%] [%] Hcg Hown
                  [] [] Hpc Hbsl Hsbn Hsbi Hsbs Hsbb Hbmres [%] Hir Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt. }
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { destruct Hns1 as (Hlo & Hhi & Hstrict).
          split; [lia | pose proof (Hstrict eq_refl); lia]. }
        { rewrite /sys_mkdir_ret. left. rewrite Ha0f. exact HP2a0. }
      + (* ---------- ARM B: create returned 0 ---------- *)
        iDestruct "Hok" as "%Hcrz".
        iApply (wp_cbeqz_taken_s_sconf (CID := CID18) (mword_of_int (MD + 0x2c))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  mcr (K - 18)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Hcrz; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi2c").
        iApply bi.later_intro. iIntros (CID19 Hq19) "Hcg Hpc".
        assert (Htg40 : add_vec (mword_of_int (MD + 0x2c) : mword 64)
                          (sign_extend' 64
                             (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0"))))
                        = mword_of_int (MD + 0x40)) by pcw.
        iEval (rewrite Htg40) in "Hpc".
        iDestruct (md_buf_join (pa_stk sp0 18) bf pk Hpk with "Hbufk Hbufrest")
          as "Hbytes2".
        iDestruct (md_bytes_name (pa_stk sp0 18) 128 with "Hbytes2") as (bf1) "Hbuf".
        iDestruct (proc_priv_pid gf pj pid (upd_upt V P') with "Hpriv")
          as "[Hpidq Hpback]".
        iDestruct (cpu_own_transport CID18 CID19 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (md_m1_tail (CID0 := CID19) gs j gl gu gd gk pd pav pu bn g gfs
                  cov logstart dev un1 pid (DfracOwn (1/4))
                  m mcr sp0 K eb b lks bf1
                  ltac:(lia) ltac:(lia) Kpop Hgeom Hj Hgl Hlkempty
                  ltac:(reflexivity) Hcrsp Hcrthr Hal
                  with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                        Hpidq Hprocs Hdev Hgeo Hdlk [HopS] Hf1 Hf2 Hbuf
                        [Hpback Hbsl Hsbn Hsbi Hsbs Hsbb Hbmres Hir Hcont]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iApply (log_opS_op with "HopS"). }
        iEval (rewrite /wp_next).
        iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hown _ _ Hpc Hpidq".
        iDestruct ("Hpback" with "Hpidq") as "Hpriv".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf used1 ns1 P' with "[%] [%] Hcg Hown
                  [] [] Hpc Hbsl Hsbn Hsbi Hsbs Hsbb Hbmres [%] Hir Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt. }
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { destruct Hns1 as (Hlo & Hhi & _). split; [lia | lia]. }
        { rewrite /sys_mkdir_ret. right. exact Ha0f. }
    - (* ================= ARM A: argstr returned -1 =================
         The [bltz] is TAKEN, straight to the shared "-1" tail at +0x40. *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID11) (mword_of_int (MD + 0x1a))
                (mword_of_int 38 : mword 13) Ra0 mas (K - 18)%nat b
                ltac:(nz) ltac:(rgne; rewrite Hpr; exact md_m1_neg)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1a").
      iApply bi.later_intro. iIntros (CID12 Hq12) "Hcg Hpc".
      assert (Htg40 : add_vec (mword_of_int (MD + 0x1a) : mword 64)
                        (sign_extend' 64 (mword_of_int 38 : mword 13))
                      = mword_of_int (MD + 0x40)) by pcw.
      iEval (rewrite Htg40) in "Hpc".
      iDestruct (proc_priv_pid gf pj pid (upd_upt V P') with "Hpriv")
        as "[Hpidq Hpback]".
      iDestruct (cpu_own_transport CID11 CID12 0 eb pj b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (md_m1_tail (CID0 := CID12) gs j gl gu gd gk pd pav pu bn g gfs
                cov logstart dev MAXOPBLOCKS pid (DfracOwn (1/4))
                m mas sp0 K eb b lks bf
                ltac:(lia) ltac:(lia) Kpop Hgeom Hj Hgl Hlkempty
                ltac:(reflexivity) Hassp Hasthr Hal
                with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                      Hpidq Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hbuf
                      [Hpback Hbsl Hsbn Hsbi Hsbs Hsbb Hbmres Hir Hcont]").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iEval (rewrite /wp_next).
      iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hown _ _ Hpc Hpidq".
      iDestruct ("Hpback" with "Hpidq") as "Hpriv".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf used ns P' with "[%] [%] Hcg Hown
                [] [] Hpc Hbsl Hsbn Hsbi Hsbs Hsbb Hbmres [%] Hir Hpriv [%]").
      { exact Hcsf. }
      { exact Hupt. }
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { split; lia. }
      { rewrite /sys_mkdir_ret. right. exact Ha0f. }
  Qed.

End ProofSysMkdirBody.

End SysMkdirProof.
