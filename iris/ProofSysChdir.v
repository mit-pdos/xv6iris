(* ProofSysChdir.v -- sys_chdir over the SIE-agnostic sconf world.

     uint64 sys_chdir(void) {
       char path[MAXPATH];  struct inode *ip;
       struct proc *p = myproc();
       begin_op();
       if (argstr(0, path, MAXPATH) < 0 || (ip = namei(path)) == 0) {
         end_op(); return -1; }
       ilock(ip);
       if (ip->type != T_DIR) { iunlockput(ip); end_op(); return -1; }
       iunlock(ip);  iput(p->cwd);  end_op();  p->cwd = ip;  return 0;
     }

   128 bytes, 45 instructions, FOUR arms that all leave through one
   epilogue.  Read off CodeSysChdir.v:

     +0x00  c.addi16sp sp,-160      the twenty-slot frame
     +0x02  c.sdsp ra,152(sp)       slot 1
     +0x04  c.sdsp s0,144(sp)       slot 2
     +0x06  c.sdsp s2,128(sp)       slot 4
     +0x08  c.addi4spn s0,sp,160    s0 = the ENTRY sp
     +0x0a  jal myproc              s2 := p
     +0x10  jal begin_op
     +0x14  li a2,128 ; addi a1,s0,-160 ; c.li a0,0 ; jal argstr
     +0x22  bltz a0 -> +0x68        ARM A: the string did not fetch
     +0x26  c.sdsp s1,136(sp)       slot 3 -- ONLY on the arms that have an ip
     +0x28  addi a0,s0,-160 ; jal namei ; c.mv s1,a0
     +0x32  c.beqz a0 -> +0x66      ARM B: the path did not resolve
     +0x34  jal ilock
     +0x38  lh a4,68(s1) ; c.li a5,1
     +0x3e  bne a4,a5 -> +0x70      ARM C: not a directory
     +0x42  c.mv a0,s1 ; jal iunlock
     +0x48  ld a0,336(s2) ; jal iput ; jal end_op
     +0x54  sd s1,336(s2)           p->cwd = ip
     +0x58  c.li a0,0 ; c.ldsp s1,136(sp)
     +0x5c  THE EPILOGUE: ldsp ra / ldsp s0 / ldsp s2 / addi16sp / ret
     +0x66  c.ldsp s1,136(sp)       (arm B rejoins arm A here)
     +0x68  jal end_op ; c.li a0,-1 ; c.j +0x5c
     +0x70  c.mv a0,s1 ; jal iunlockput ; jal end_op ; c.li a0,-1 ;
            c.ldsp s1,136(sp) ; c.j +0x5c

   THE ONE STRUCTURAL POINT: [s1] IS SAVED LATE.  The [c.sdsp s1] at +0x26
   is AFTER the [bltz], and arm A therefore neither saves nor restores it --
   which is sound because arm A never writes it either, so slot 3 rides
   through as the caller's junk and the register rides through as the
   caller's value.  The other three arms each do their own [c.ldsp s1]
   before joining the epilogue (+0x5a, +0x66, +0x7c), so the epilogue
   itself never touches s1 and takes "M's s1 is m's s1" as a premise it
   does not have to establish.

   THE FRAME CARVE: sixteen of the twenty slots ARE [char path[128]]
   ([sc_frame_carve] / [sc_frame_join]), dirlookup's [de] move and namei's
   [name] move at a bigger width.  Nothing about the buffer reaches the
   contract.

   THE cwd SWAP, in resources: [proc_priv_split_cwd] takes the reference
   off the block BEFORE the walk, [proc_priv_nocwd_cwd_pid] lends the cell
   and the pid quarter across every call that wants one, and the block is
   rebuilt at the [sd s1,336(s2)] with the reference [namei] made --
   [iunlock] having handed the carved share back and [inode_held_gather]
   having re-formed it.

   ==== PARKED GREEN =====================================================

   WHAT IS HERE: the pure side conditions, the frame carve/join pair, and
   the EPILOGUE block (+0x5c .. +0x64) that all four arms leave through.
   Every lemma is [Qed]; the file carries no [Admitted] and no [Axiom].

   WHAT IS NOT HERE: the walk itself (+0x00 .. +0x5a and the three failure
   arms) and therefore the [SYSCHDIR] module functor, which is why this
   file is not yet in [_CoqProject] and why [LinkSysChdir.v] does not
   exist.  The design the walk consumes -- the arm graph, the resource
   plan arm by arm, and both ledgers' arithmetic -- is written up in
   claude-notes/projects/fs-sysfile.md under the sys_chdir stage. *)
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
Require Import PathElems.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecMyproc.
Require Import SpecArgstr.
Require Import SpecFetchstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIunlock.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecNamei.
Require Import CodeSysChdir.
Require Import SpecSysChdir.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

Notation SC := KernelSyms.sys_chdir (only parsing).

(* ===================================================================== *)
(*  THE PURE SIDE-CONDITIONS, as closed top-level facts (never run [lia]  *)
(*  or [vm_compute] inside a whole-function context).                     *)
(* ===================================================================== *)

(* the four registers this frame moves: sp, s0 (frame pointer), s1 (ip),
   s2 (p).  Everything else callee-saved rides straight through, and it is
   stated POSITIVELY where it matters -- the four exceptions are exactly
   the four the code writes, each accounted for by its own equation. *)
Definition sc_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma sc_thr_refl (m : regfile) : sc_thr m m.
Proof. intros c _ _ _ _ _. reflexivity. Qed.

Lemma sc_thr_trans (m M P : regfile) : sc_thr m M -> sc_thr M P -> sc_thr m P.
Proof. intros H1 H2 c Hc N2 N8 N9 N18. rewrite (H2 c Hc N2 N8 N9 N18). exact (H1 c Hc N2 N8 N9 N18). Qed.

Definition sc_sp (sp0 : mword 64) (M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk sp0 20.

(* -160 / +160, both a [c.addi16sp] (54 is -10 in a 6-bit field, x16). *)
Lemma sc_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 54 : mword 6)))
  = pa_stk X 20.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sc_pop (X : mword 64) :
  add_vec (pa_stk X 20) (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,160] -- the frame pointer, back at the entry sp. *)
Lemma sc_fp (X : mword 64) :
  add_vec (pa_stk X 20) (sign_extend' 64 (caddi4spn_imm (mword_of_int 40 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi aN,s0,-160] off the frame pointer (which IS the entry sp) is the
   base of the path buffer, i.e. the lowest slot of the frame. *)
Lemma sc_buf (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3936 : mword 12)) = pa_stk X 20.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* the c.sdsp / c.ldsp displacements off the pushed sp *)
Lemma sc_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (bv_wrap 64 (uint (mword_of_int (- (8 * Z.of_nat 20)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 20) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite pa_stk_off2. apply f_equal. exact H.
Qed.

Lemma sc_frm1 (X : mword 64) :
  add_vec (pa_stk X 20)
    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply sc_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sc_frm2 (X : mword 64) :
  add_vec (pa_stk X 20)
    (zero_extend' 64 (concat_vec (mword_of_int 18 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply sc_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sc_frm3 (X : mword 64) :
  add_vec (pa_stk X 20)
    (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply sc_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sc_frm4 (X : mword 64) :
  add_vec (pa_stk X 20)
    (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply sc_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_sys_chdir's single premise, turned into every bound the nine callees
   and the [sie_cap_gpr] pop want. *)
Lemma sc_kb (K : nat) : (K_sys_chdir <= K)%nat ->
  (K_namei <= K - 20)%nat /\ (argstr_stack <= K - 20)%nat /\
  (K_begin_op <= K - 20)%nat /\ (K_end_op <= K - 20)%nat /\
  (K_ilock <= K - 20)%nat /\ (K_iunlock <= K - 20)%nat /\
  (K_iput <= K - 20)%nat /\ (K_iunlockput <= K - 20)%nat /\
  (10 <= K - 20)%nat /\ (20 <= K)%nat /\ ((K - 20) + 20 = K)%nat.
Proof.
  unfold K_sys_chdir, K_namei, argstr_stack, K_begin_op, K_end_op,
         K_ilock, K_iunlock, K_iput, K_iunlockput.
  intro H. split_and!; lia.
Qed.

(* THE LOG BUDGET, closed.  begin_op mints ten; the walk needs at most
   four and spends at most one; the tail's iput needs three. *)
Lemma sc_bud_walk (L : nat) : (walk_need L <= MAXOPBLOCKS)%nat.
Proof. unfold walk_need, iput_units, MAXOPBLOCKS. destruct L; lia. Qed.

Lemma sc_bud_iput (L n' : nat) (w ok : bool) :
  ((MAXOPBLOCKS - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  unfold walk_spend, iput_units, MAXOPBLOCKS. destruct w, ok; lia.
Qed.

(* the syscall argument index is in range, and [i = 0] is what a0 holds *)
Lemma sc_arg0_lt : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma sc_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma sc_maxpath_lt : (Z.of_nat 128 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* fetchstr's success arm, unpacked: the fetched length is below the cap
   (so [S k] bytes are inside the buffer) and it fits an int. *)
Lemma sc_plen_lt (k : nat) : (k < 128)%nat -> (Z.of_nat k < 2 ^ 31)%Z.
Proof. lia. Qed.

Section ProofSysChdirFrame.
  Context `{!riscvGS Σ}.

  (* ---- THE FRAME CARVE: the low SIXTEEN slots ARE [char path[128]] ---- *)

  Lemma sc_frame_carve (sp0 : mword 64) :
    stack_own sp0 20 -∗
    ⌜forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (20 - i)%nat)) 8 = true⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈ w) ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 20) 128.
  Proof.
    iIntros "H". rewrite stack_own_slots. cbn [seq].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                       H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 &
                       H20 & _)".
    change 128%nat with (8 * 16)%nat.
    iDestruct (slotsn_bytes_own sp0 20 16 ltac:(lia)
                 with "[H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18
                        H19 H20]") as "[%Hal Hb]".
    { cbn [seq].
      iSplitL "H20"; [iExact "H20" |]. iSplitL "H19"; [iExact "H19" |].
      iSplitL "H18"; [iExact "H18" |]. iSplitL "H17"; [iExact "H17" |].
      iSplitL "H16"; [iExact "H16" |]. iSplitL "H15"; [iExact "H15" |].
      iSplitL "H14"; [iExact "H14" |]. iSplitL "H13"; [iExact "H13" |].
      iSplitL "H12"; [iExact "H12" |]. iSplitL "H11"; [iExact "H11" |].
      iSplitL "H10"; [iExact "H10" |]. iSplitL "H9"; [iExact "H9" |].
      iSplitL "H8"; [iExact "H8" |]. iSplitL "H7"; [iExact "H7" |].
      iSplitL "H6"; [iExact "H6" |]. iSplitL "H5"; [iExact "H5" |].
      done. }
    iFrame "H1 H2 H3 H4 Hb". iPureIntro. exact Hal.
  Qed.

  Lemma sc_frame_join (sp0 : mword 64) (w1 w2 w3 w4 : mword 64) :
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (20 - i)%nat)) 8 = true) ->
    (pa_stk sp0 1) ↦₈ w1 -∗ (pa_stk sp0 2) ↦₈ w2 -∗
    (pa_stk sp0 3) ↦₈ w3 -∗ (pa_stk sp0 4) ↦₈ w4 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 20) 128 -∗
    stack_own sp0 20.
  Proof.
    intro Hal. iIntros "H1 H2 H3 H4 Hb".
    change 128%nat with (8 * 16)%nat.
    iDestruct (bytes_own_slotsn sp0 20 16 ltac:(lia) Hal with "Hb") as "Hs".
    cbn [seq].
    iDestruct "Hs" as "(K20 & K19 & K18 & K17 & K16 & K15 & K14 & K13 & K12 &
                        K11 & K10 & K9 & K8 & K7 & K6 & K5 & _)".
    rewrite stack_own_slots. cbn [seq].
    iSplitL "H1"; [iExists w1; iExact "H1" |].
    iSplitL "H2"; [iExists w2; iExact "H2" |].
    iSplitL "H3"; [iExists w3; iExact "H3" |].
    iSplitL "H4"; [iExists w4; iExact "H4" |].
    iSplitL "K5"; [iExact "K5" |]. iSplitL "K6"; [iExact "K6" |].
    iSplitL "K7"; [iExact "K7" |]. iSplitL "K8"; [iExact "K8" |].
    iSplitL "K9"; [iExact "K9" |]. iSplitL "K10"; [iExact "K10" |].
    iSplitL "K11"; [iExact "K11" |]. iSplitL "K12"; [iExact "K12" |].
    iSplitL "K13"; [iExact "K13" |]. iSplitL "K14"; [iExact "K14" |].
    iSplitL "K15"; [iExact "K15" |]. iSplitL "K16"; [iExact "K16" |].
    iSplitL "K17"; [iExact "K17" |]. iSplitL "K18"; [iExact "K18" |].
    iSplitL "K19"; [iExact "K19" |]. iSplitL "K20"; [iExact "K20" |].
    done.
  Qed.

  (* the buffer, named as bytes and back: namei / argstr both speak the
     [seq]-indexed byte window, not [bytes_own] *)
  Lemma sc_bytes_name (a : mword 64) (N : nat) :
    bytes_own (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j.
  Proof. rewrite /bytes_own. exact (bb_any_named a N). Qed.

  Lemma sc_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j) ⊢ bytes_own (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any a N f). Qed.

  (* 128 = (k+1) + (127-k): namei reads the NUL-terminated prefix, the rest
     rides through untouched *)
  Lemma sc_buf_split (a : mword 64) (f : nat -> bv 8) (k : nat) :
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

  Lemma sc_buf_join (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat,
       pa_add (pa_add a (S k)) j ↦ₘ f (S k + j)%nat) -∗
    bytes_own (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (sc_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (sc_name_bytes (pa_add a (S k)) (127 - k)%nat
                 (fun j => f (S k + j)%nat) with "H2") as "B2".
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite bytes_own_app. iFrame.
  Qed.

End ProofSysChdirFrame.

(* ===================================================================== *)
(*  +0x5c .. +0x64 : THE EPILOGUE, which all four arms leave through.     *)
(*                                                                        *)
(*  It touches no resource but the frame: [s1] has already been restored  *)
(*  (or, on arm A, never moved), [a0] already holds the result, and what  *)
(*  is left is the three [c.ldsp]s, the pop and the [c.ret].  Everything  *)
(*  else an arm is holding rides in its own continuation premise, which   *)
(*  is why this lemma has no file-system parameter at all.                *)
(* ===================================================================== *)

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac scidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofSysChdirEpilogue.
  Context `{!riscvGS Σ, !sieG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma sc_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64)
      (w3 : mword 64) (bf : nat -> bv 8) :
    (20 <= K)%nat -> ((K - 20) + 20 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sc_sp sp0 M -> sc_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) ->
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (20 - i)%nat)) 8 = true) ->
    sie_cap_gpr M (K - 20) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SC + 0x5c)) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ w3 -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 20) jj ↦ₘ bf jj) -∗
    (* THE INDEX IS [b], NOT [true], and it has to be: the epilogue is five
       PLAIN instructions, so every crossing it makes is a [b]-link and the
       [b]-form chain is what it can hand back.  Stated at [true] the caller
       gets only "pj = zero_reg -> ...", which pins nothing at [b = false]
       and leaves every [cpu_own_transport] after the block unprovable.  A
       caller whose own continuation is at [true] weakens into this for
       free ([or_intror], which is what [wp_next_chain] tries). *)
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64)⌝ -∗
        sie_cap_gpr mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK20 Kpop Hsp0 HMsp HMthr HMs1 Hal.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hf3 Hf4 Hbuf Hcont".
    iPoseProof (schdi_5c with "Htext") as "Hi5c".
    iPoseProof (schdi_5e with "Htext") as "Hi5e".
    iPoseProof (schdi_60 with "Htext") as "Hi60".
    iPoseProof (schdi_62 with "Htext") as "Hi62".
    iPoseProof (schdi_64 with "Htext") as "Hi64".
    (* the three slot addresses, at THIS register file's sp *)
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HMsp; apply sc_frm1).
    (* ===== +0x5c c.ldsp ra,152(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SC + 0x5c))
              (mword_of_int 19 : mword 6) Rra M (K - 20)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi5c [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (M1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HM1sp : sc_sp sp0 M1)
      by (rewrite /sc_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1thr : sc_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    assert (Hpp5e : add_vec_int (mword_of_int (SC + 0x5c) : mword 64) 2
                    = mword_of_int (SC + 0x5e)) by pcw.
    iEval (rewrite Hpp5e) in "Hpc".
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 18 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply sc_frm2).
    (* ===== +0x5e c.ldsp s0,144(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SC + 0x5e))
              (mword_of_int 18 : mword 6) Rs0 M1 (K - 20)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi5e [Hf2]").
    { iEval (rewrite Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    set (M2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> M1).
    assert (HM2sp : sc_sp sp0 M2)
      by (rewrite /sc_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1ra | nz]).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2thr : sc_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    assert (Hpp60 : add_vec_int (mword_of_int (SC + 0x5e) : mword 64) 2
                    = mword_of_int (SC + 0x60)) by pcw.
    iEval (rewrite Hpp60) in "Hpc".
    assert (Hc4 : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HM2sp; apply sc_frm4).
    (* ===== +0x60 c.ldsp s2,128(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SC + 0x60))
              (mword_of_int 16 : mword 6) Rs2 M2 (K - 20)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi60 [Hf4]").
    { iEval (rewrite Hc4). iExact "Hf4". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf4".
    iEval (rewrite Hc4) in "Hf4".
    set (M3 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> M2).
    assert (HM3sp : sc_sp sp0 M3)
      by (rewrite /sc_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3; apply upd_eq).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2a0 | nz]).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (HM3thr : sc_thr m M3).
    { intros c Hc N2 N8 N9 N18. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8 N9 N18). }
    assert (Hpp62 : add_vec_int (mword_of_int (SC + 0x60) : mword 64) 2
                    = mword_of_int (SC + 0x62)) by pcw.
    iEval (rewrite Hpp62) in "Hpc".
    (* ===== +0x62 c.addi16sp sp,160 : the pop ===== *)
    assert (Hwv : add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))
                  = sp0)
      by (rewrite HM3sp; apply sc_pop).
    assert (Hpop : (M3 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))) 20)
      by (rewrite Hwv HM3sp; reflexivity).
    iDestruct (sc_name_bytes (pa_stk sp0 20) 128 bf with "Hbuf") as "Hbytes".
    iDestruct (sc_frame_join sp0 _ _ w3 _ Hal with "Hf1 Hf2 Hf3 Hf4 Hbytes")
      as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SC + 0x62))
              (mword_of_int 10 : mword 6) M3 (K - 20)%nat 20 b Hpop
              with "Hcg Hpc Hi62 Hstk").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6))))]> M3).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp64 : add_vec_int (mword_of_int (SC + 0x62) : mword 64) 2
                    = mword_of_int (SC + 0x64)) by pcw.
    iEval (rewrite Hpp64) in "Hpc".
    assert (HM4ra : (M4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3ra | nz]).
    (* ===== +0x64 c.ret ===== *)
    iApply (wp_cret_s_sconf (mword_of_int (SC + 0x64)) Rra M4 K b
              ltac:(nz) with "Hcg Hpc Hi64").
    iIntros (CID5 Hq5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (M4 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HM4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE HANDOVER ===== *)
    assert (Hwv' : add_vec (M3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 10 : mword 6)))
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
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3a0 | nz]).
    assert (Hfin : sc_thr m M4).
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

End ProofSysChdirEpilogue.

(* ===================================================================== *)
(*  +0x68 .. +0x6e : THE SHARED "-1" TAIL.                                *)
(*                                                                        *)
(*  end_op, [c.li a0,-1], and the [c.j] back into the epilogue.  BOTH     *)
(*  failure arms of the C-level [||] reach it: ARM A ([bltz] at +0x22)     *)
(*  branches straight here, ARM B ([c.beqz] at +0x32) restores s1 at       *)
(*  +0x66 and falls in.  Everything an arm still owns rides in its own     *)
(*  continuation premise, so the only file-system resources here are       *)
(*  end_op's own.                                                         *)
(* ===================================================================== *)
(* ===================================================================== *)
(*  THE FUNCTOR.  Everything from here down applies a callee's contract,   *)
(*  so it lives inside the module the seal instantiates.                   *)
(* ===================================================================== *)
Module SysChdirProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Argstr : ARGSTR)
                     (Namei : NAMEI) (Ilock : ILOCK) (Iunlock : IUNLOCK)
                     (Iput : IPUT) (Iunlockput : IUNLOCKPUT) (EndOp : END_OP).

Section ProofSysChdirM1Tail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma sc_m1_tail `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset string) (w3 : mword 64) (bf : nat -> bv 8) :
    (K_end_op <= K - 20)%nat -> (20 <= K)%nat -> ((K - 20) + 20 = K)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sc_sp sp0 M -> sc_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) ->
    (forall i, (i < 16)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (20 - i)%nat)) 8 = true) ->
    sie_cap_gpr M (K - 20) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ pc_is (mword_of_int (SC + 0x68)) -∗
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
    (pa_stk sp0 3) ↦₈ w3 -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 20) jj ↦ₘ bf jj) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKeo HK20 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hbuf Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (schdi_68 with "Htext") as "Hi68".
    iPoseProof (schdi_6c with "Htext") as "Hi6c".
    iPoseProof (schdi_6e with "Htext") as "Hi6e".
    (* ===== +0x68 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SC + 0x68)) Rra
              (mword_of_int 2091416 : mword 21) M (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi68").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SC + 0x68) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (SC + 0x68) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091416 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SC + 0x68) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : sc_sp sp0 M1)
      by (rewrite /sc_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1thr : sc_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M1 (K - 20)%nat eb C b lks
              HKeo Hgeom Hj Hgl ltac:(lkbelow)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc6c : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (SC + 0x6c)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpc6c) in "Hpc".
    assert (Heosp : sc_sp sp0 meo).
    { rewrite /sc_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heos1 : (meo !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs1 ltac:(vm_compute; reflexivity)).
      exact HM1s1. }
    assert (Heothr : sc_thr m meo).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8 N9 N18). }
    (* ===== +0x6c c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SC + 0x6c)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 20)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi6c").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : sc_sp sp0 P1)
      by (rewrite /sc_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos1 | nz]).
    assert (HP1thr : sc_thr m P1).
    { intros c Hc N2 N8 N9 N18. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18). }
    assert (Hpp6e : add_vec_int (mword_of_int (SC + 0x6c) : mword 64) 2
                    = mword_of_int (SC + 0x6e)) by pcw.
    iEval (rewrite Hpp6e) in "Hpc".
    (* ===== +0x6e c.j +0x5c ===== *)
    iApply (wp_cj_s_sconf (CID := CID3) (mword_of_int (SC + 0x6e))
              (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")))
              P1 (K - 20)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6e").
    iIntros (CID4 Hq4). iNext. iIntros "Hcg Hpc".
    assert (Htg5c : add_vec (mword_of_int (SC + 0x6e) : mword 64)
                      (sign_extend' 64
                         (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                    = mword_of_int (SC + 0x5c)) by pcw.
    iEval (rewrite Htg5c) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID4 0 eb (proc_addr jx) C b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID2 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID2 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (sc_epilogue (CID0 := CID4) m P1 sp0 K b (proc_addr jx) w3 bf
              HK20 Kpop Hsp0 HP1sp HP1thr HP1s1 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hbuf [Hown Htce Hcce Hpid Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID4 CIDy 0 eb (proc_addr jx) C b
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

End ProofSysChdirM1Tail.

End SysChdirProof.
