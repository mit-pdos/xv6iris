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

   ==== THE COMPLEMENT IS DROPPED, NOT THREADED ==========================

   The contract's [eb = true] premise makes [trap_csrs_ext eb] and
   [cpu_claim_ext eb pj] both [emp], and FIVE of the nine callees (myproc,
   argstr, namei, iunlock, and every plain instruction) do not take them.
   Threading them would therefore demand a transport across namei's park --
   which the [true] crossing cannot supply -- so the walk drops the pair at
   the top and re-mints it at each callee that wants one, and once more for
   the caller's continuation.  That is the same device ProofNamex uses. *)
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
Require Import PanicStub.
Require Import KernelDataInv.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import KallocInv.
Require Import PanicStub.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecMyproc.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIunlock.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecPanic.
Require Import SpecPrintk.
Require Import SpecNamei.
Require Import CodeSysChdir.
Require Import SpecSysChdir.
From Kernel Require KernelSyms.
Require Import ProcAvail.
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
  
  intro H. split_and!; lia.
Qed.

(* THE LOG BUDGET, closed.  begin_op mints ten; the walk needs at most
   four and spends at most one; the tail's iput needs three. *)
Lemma sc_bud_walk (L : nat) : (walk_need L <= MAXOPBLOCKS)%nat.
Proof. unfold walk_need, iput_units, MAXOPBLOCKS. destruct L; lia. Qed.

Lemma sc_bud_iput (n' : nat) (w ok : bool) :
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

(* THE [bltz] AT +0x22, decided.  argstr's answer is [fetchstr_ret]'s
   disjunction, so the branch turns on the SIGN of a value that is either
   [-1] or a length below 128 -- ProofSysDup's three-lemma cluster, restated
   here rather than imported (a whole-function proof file is not a
   dependency any other one may take). *)
Lemma sc_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
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

Lemma sc_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (sc_sint_moi z Hz). lia.
Qed.

Lemma sc_m1_neg :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma sc_len_range (k : nat) : (k < 128)%nat -> (0 <= Z.of_nat k < 2 ^ 31)%Z.
Proof.
  intro Hk.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* THE TYPE TEST at +0x38/+0x3e: the [lh] leaves a [sign_extend' 64] and the
   [bne] against a5 = 1 decides [di_type dn = T_DIR] exactly.  Restated here
   rather than imported from ProofNamexParts for the same reason the sign
   cluster above is: a whole-function proof file is not a dependency. *)
Lemma sc_sext16_inj (x y : mword 16) :
  (sign_extend' 64 x : mword 64) = (sign_extend' 64 y : mword 64) -> x = y.
Proof.
  intros H. apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H;
    [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

Lemma sc_sext_one :
  (sign_extend' 64 (mword_of_int 1 : mword 16) : mword 64)
  = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sc_tdir_eq (t : mword 16) : t = (mword_of_int 1 : mword 16) ->
  neq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = false.
Proof.
  intros ->. unfold neq_vec. rewrite sc_sext_one.
  rewrite (proj2 (eq_vec_true_iff _ _) eq_refl). reflexivity.
Qed.

Lemma sc_tdir_ne (t : mword 16) : t <> (mword_of_int 1 : mword 16) ->
  neq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = true.
Proof.
  intro Hne. unfold neq_vec.
  rewrite (proj2 (eq_vec_false_iff _ _)); [reflexivity |].
  intro Hc. apply Hne. apply sc_sext16_inj. rewrite Hc sc_sext_one.
  reflexivity.
Qed.

(* [upd_cwd V (pv_cwd V) = V] -- the two arms that put the block back
   UNCHANGED after the cwd cell has been out on loan. *)
Lemma sc_upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
Proof. destruct V; reflexivity. Qed.

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
                     (Iput : IPUT) (Iunlockput : IUNLOCKPUT) (EndOp : END_OP)
  : SYSCHDIR.

Section ProofSysChdirM1Tail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ,
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
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
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
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SC + 0x68)) -∗
    panic_wp_any -∗
    panic_env -∗
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
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKeo HK20 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpanic #Hpenv #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hbuf Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (schdi_68 with "Htext") as "Hi68".
    iPoseProof (schdi_6c with "Htext") as "Hi6c".
    iPoseProof (schdi_6e with "Htext") as "Hi6e".
    (* ===== +0x68 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SC + 0x68)) Rra
              (mword_of_int 2091402 : mword 21) M (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi68").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SC + 0x68) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (SC + 0x68) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091402 : mword 21))
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
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M1 (K - 20)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(lkbelow)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpanic Hpenv Hbio Hlog Hseam Hgen
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
    iDestruct (cpu_own_transport CID2 CID4 0 eb (proc_addr jx) b
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

End ProofSysChdirM1Tail.

(* ===================================================================== *)
(*  THE WALK: +0x00 .. +0x5a, the three failure arms and the success       *)
(*  tail.  Everything here applies a callee, so it lives inside the        *)
(*  functor.                                                              *)
(* ===================================================================== *)

Section ProofSysChdirBody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* the two per-slot projections out of the boot families, at the copies
     THIS contract names ([ic_escrows] is IcacheEscrow's, [ic_sleeplocks]
     SpecDirlink's -- see the worklist's trap 3). *)
  Lemma sc_esc_acc (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn gfs gi cov logstart -∗ ic_escrow cn gfs gi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma sc_slk_acc (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    (ic_sleeplocks cn -∗
     ∃ gil gisl : gname,
       is_sleeplock_gen gil gisl (i_lock (ientry k)) "inode"%string (ic_tok cn k) (slh_tok (icfg_isl k))
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  (* the three-slot pool, split for ilock's single [bslot] and rejoined *)
  Lemma sc_bs3 (bn : bio_names) :
    (bslots bn 3 : iProp Σ) ⊣⊢ bslot bn ∗ bslots bn 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  Lemma wp_sys_chdir_sconf `{GEN : GenId} `{CID0 : CpuId}
      (gf ga : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (dqb dqs : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_sys_chdir_sconf_body gf ga gs j gl gu gd gk pd pav pu bn g gfs gi
                            cn gtl cov logstart bmapstart inodestart nib
                            size dev used dqb dqs v pid V m K eb b lks.
  Proof.
    cbv beta delta [wp_sys_chdir_sconf_body].
    intros pcE pj ret_tgt HK Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom
           Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb Hargv.
    destruct (sc_kb K HK) as (Kna & Kar & Kbo & Keo & Kil & Kiu & Kip & Kiup
                              & K10 & K20 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hpanic #Hpe #Hbio #Hlog Hseam
             Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks
             #Hireg Hsbb Hsbi Hbmres #Hkenv #Hprocs Hir Hpriv Hcont".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    (* the complement is [emp] at [eb = true], so it is DROPPED here and
       re-minted at every callee that wants it: threading it would demand a
       transport across each of the five parking calls that do not take it. *)
    iPoseProof (schdi_00 with "Htext") as "Hi00".
    iPoseProof (schdi_02 with "Htext") as "Hi02".
    iPoseProof (schdi_04 with "Htext") as "Hi04".
    iPoseProof (schdi_06 with "Htext") as "Hi06".
    iPoseProof (schdi_08 with "Htext") as "Hi08".
    iPoseProof (schdi_0a with "Htext") as "Hi0a".
    iPoseProof (schdi_0e with "Htext") as "Hi0e".
    iPoseProof (schdi_10 with "Htext") as "Hi10".
    iPoseProof (schdi_14 with "Htext") as "Hi14".
    iPoseProof (schdi_18 with "Htext") as "Hi18".
    iPoseProof (schdi_1c with "Htext") as "Hi1c".
    iPoseProof (schdi_1e with "Htext") as "Hi1e".
    iPoseProof (schdi_22 with "Htext") as "Hi22".
    iPoseProof (schdi_26 with "Htext") as "Hi26".
    iPoseProof (schdi_28 with "Htext") as "Hi28".
    iPoseProof (schdi_2c with "Htext") as "Hi2c".
    iPoseProof (schdi_30 with "Htext") as "Hi30".
    iPoseProof (schdi_32 with "Htext") as "Hi32".
    iPoseProof (schdi_34 with "Htext") as "Hi34".
    iPoseProof (schdi_38 with "Htext") as "Hi38".
    iPoseProof (schdi_3c with "Htext") as "Hi3c".
    iPoseProof (schdi_3e with "Htext") as "Hi3e".
    iPoseProof (schdi_42 with "Htext") as "Hi42".
    iPoseProof (schdi_44 with "Htext") as "Hi44".
    iPoseProof (schdi_48 with "Htext") as "Hi48".
    iPoseProof (schdi_4c with "Htext") as "Hi4c".
    iPoseProof (schdi_50 with "Htext") as "Hi50".
    iPoseProof (schdi_54 with "Htext") as "Hi54".
    iPoseProof (schdi_58 with "Htext") as "Hi58".
    iPoseProof (schdi_5a with "Htext") as "Hi5a".
    iPoseProof (schdi_66 with "Htext") as "Hi66".
    iPoseProof (schdi_70 with "Htext") as "Hi70".
    iPoseProof (schdi_72 with "Htext") as "Hi72".
    iPoseProof (schdi_76 with "Htext") as "Hi76".
    iPoseProof (schdi_7a with "Htext") as "Hi7a".
    iPoseProof (schdi_7c with "Htext") as "Hi7c".
    iPoseProof (schdi_7e with "Htext") as "Hi7e".
    (* ================= +0x00 c.addi16sp sp,-160 ================= *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 54 : mword 6) m K 20 b
              ltac:(lia) (sc_push sp0) with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 54 : mword 6))))]> m).
    assert (HM1sp : sc_sp sp0 M1).
    { unfold sc_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply sc_push ]. }
    assert (HM1thr : sc_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SC + 0x02))
      by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* the carve: sixteen of the twenty slots ARE [char path[128]] *)
    iDestruct (sc_frame_carve sp0 with "Hframe")
      as "(%Hal & [%u1 Hf1] & [%u2 Hf2] & [%u3 Hf3] & [%u4 Hf4] & Hbytes)".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply sc_frm1).
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 18 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply sc_frm2).
    assert (Hc3 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HM1sp; apply sc_frm3).
    assert (Hc4 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HM1sp; apply sc_frm4).
    (* ================= +0x02 c.sdsp ra,152(sp) ================= *)
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (SC + 0x02))
              (mword_of_int 19 : mword 6) Rra M1 (K - 20)%nat u1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (SC + 0x02) : mword 64) 2
                    = mword_of_int (SC + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ================= +0x04 c.sdsp s0,144(sp) ================= *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SC + 0x04))
              (mword_of_int 18 : mword 6) Rs0 M1 (K - 20)%nat u2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rgne; rewrite Hc2 HM1s0) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (SC + 0x04) : mword 64) 2
                    = mword_of_int (SC + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ================= +0x06 c.sdsp s2,128(sp) ================= *)
    iEval (rewrite -Hc4) in "Hf4".
    iApply (wp_csdsp_s_sconf (mword_of_int (SC + 0x06))
              (mword_of_int 16 : mword 6) Rs2 M1 (K - 20)%nat u4 b
              with "Hcg Hpc Hi06 Hf4").
    iIntros (CID4 Hq4) "Hcg Hpc Hf4".
    iEval (rgne; rewrite Hc4 HM1s2) in "Hf4".
    assert (Hpp08 : add_vec_int (mword_of_int (SC + 0x06) : mword 64) 2
                    = mword_of_int (SC + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ================= +0x08 c.addi4spn s0,sp,160 ================= *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SC + 0x08))
              (Cregidx (mword_of_int 0)) (mword_of_int 40 : mword 8) Rs0
              M1 (K - 20)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 40 : mword 8))))]> M1).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { etransitivity; [ rewrite /M2; apply upd_eq |].
      rewrite HM1sp. apply sc_fp. }
    assert (HM2sp : sc_sp sp0 M2)
      by (rewrite /sc_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : sc_thr m M2).
    { intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18). }
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (Hpp0a : add_vec_int (mword_of_int (SC + 0x08) : mword 64) 2
                    = mword_of_int (SC + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ================= +0x0a jal ra,myproc ================= *)
    iApply (wp_jal_s_sconf (CID := CID5) (mword_of_int (SC + 0x0a)) Rra
              (mword_of_int 2082334 : mword 21) M2 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SC + 0x0a) : mword 64) 4)]> M2).
    assert (Hjmp : add_vec (mword_of_int (SC + 0x0a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2082334 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcw.
    iEval (rewrite Hjmp) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SC + 0x0a) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : sc_sp sp0 M3)
      by (rewrite /sc_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (HM3thr : sc_thr m M3).
    { intros c Hc N2 N8 N9 N18. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID6 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Myproc.wp_myproc_sconf (CID := CID6) M3 (K - 20)%nat 0%nat eb pj b lks
              sc_noff0 ltac:(lia) with "Hcg Hown Htext Hpc").
    iIntros (CID7 Hq7 ms0 mmp) "%Hmsf Hcg Hown Hpc [%Hcsmp %Hmpa0]".
    assert (Hpc0e : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SC + 0x0e)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc0e) in "Hpc".
    assert (Hmpsp : sc_sp sp0 mmp).
    { rewrite /sc_sp (callee_saved_lookup Hcsmp csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Hmps0 : (mmp !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsmp Rs0 ltac:(vm_compute; reflexivity)).
      exact HM3s0. }
    assert (Hmps1 : (mmp !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcsmp Rs1 ltac:(vm_compute; reflexivity)).
      exact HM3s1. }
    assert (Hmpthr : sc_thr m mmp).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsmp c Hc).
      exact (HM3thr c Hc N2 N8 N9 N18). }
    (* ================= +0x0e c.mv s2,a0 ================= *)
    iApply (wp_cmv_s_sconf (CID := CID7) (mword_of_int (SC + 0x0e)) Rs2 Ra0
              mmp (K - 20)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0e").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (M4 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (mmp !!! Regidx Ra0))]> mmp).
    assert (HM4s2 : (M4 !!! Regidx Rs2 : mword 64) = pj).
    { etransitivity; [ rewrite /M4; apply upd_eq |].
      rewrite add_vec_zero_l. exact Hmpa0. }
    assert (HM4sp : sc_sp sp0 M4)
      by (rewrite /sc_sp /M4 upd_ne; [exact Hmpsp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact Hmps0 | nz]).
    assert (HM4s1 : (M4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M4 upd_ne; [exact Hmps1 | nz]).
    assert (HM4thr : sc_thr m M4).
    { intros c Hc N2 N8 N9 N18. rewrite /M4 upd_ne; [| regne].
      exact (Hmpthr c Hc N2 N8 N9 N18). }
    assert (Hpp10 : add_vec_int (mword_of_int (SC + 0x0e) : mword 64) 2
                    = mword_of_int (SC + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ================= +0x10 jal ra,begin_op ================= *)
    iApply (wp_jal_s_sconf (CID := CID8) (mword_of_int (SC + 0x10)) Rra
              (mword_of_int 2091350 : mword 21) M4 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SC + 0x10) : mword 64) 4)]> M4).
    assert (Hjbo : add_vec (mword_of_int (SC + 0x10) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091350 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iEval (rewrite Hjbo) in "Hpc".
    assert (HM5ra : (M5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SC + 0x10) : mword 64) 4)
      by (rewrite /M5; apply upd_eq).
    assert (HM5sp : sc_sp sp0 M5)
      by (rewrite /sc_sp /M5 upd_ne; [exact HM4sp | nz]).
    assert (HM5s0 : (M5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M5 upd_ne; [exact HM4s0 | nz]).
    assert (HM5s1 : (M5 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s1 | nz]).
    assert (HM5s2 : (M5 !!! Regidx Rs2 : mword 64) = pj)
      by (rewrite /M5 upd_ne; [exact HM4s2 | nz]).
    assert (HM5thr : sc_thr m M5).
    { intros c Hc N2 N8 N9 N18. rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2 N8 N9 N18). }
    (* the pid quarter, LENT across begin_op and taken straight back *)
    iDestruct (proc_priv_pid gf pj pid V with "Hpriv") as "[Hpidq Hpback0]".
    iDestruct (cpu_own_transport CID7 CID9 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (BeginOp.wp_begin_op_sconf (CID := CID9) gs j gl bn g gfs cov logstart
              dev pid (DfracOwn (1/4)) M5 (K - 20)%nat eb b lks
              ltac:(lia) Hj Hgl (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hpanic Hlog Hpidq Hprocs").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID10 Hq10 mbo) "%Hcsbo Hcg Hown _ _ Hpc Hpidq Hop".
    assert (Hpc14 : ret_pc (M5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SC + 0x14)) by (rewrite HM5ra; pcw).
    iEval (rewrite Hpc14) in "Hpc".
    iDestruct ("Hpback0" with "Hpidq") as "Hpriv".
    assert (Hbosp : sc_sp sp0 mbo).
    { rewrite /sc_sp (callee_saved_lookup Hcsbo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM5sp. }
    assert (Hbos0 : (mbo !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsbo Rs0 ltac:(vm_compute; reflexivity)).
      exact HM5s0. }
    assert (Hbos1 : (mbo !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcsbo Rs1 ltac:(vm_compute; reflexivity)).
      exact HM5s1. }
    assert (Hbos2 : (mbo !!! Regidx Rs2 : mword 64) = pj).
    { rewrite (callee_saved_lookup Hcsbo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM5s2. }
    assert (Hbothr : sc_thr m mbo).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsbo c Hc).
      exact (HM5thr c Hc N2 N8 N9 N18). }
    (* ================= +0x14 li a2,128 ================= *)
    iApply (wp_li4_s_sconf (CID := CID10) (mword_of_int (SC + 0x14)) Ra2
              (mword_of_int 128 : mword 12)
              (mword_of_int (Z.of_nat 128) : mword 64) mbo (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi14").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (M6 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 128) : mword 64)]> mbo).
    assert (HM6a2 : (M6 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M6; apply upd_eq).
    assert (HM6sp : sc_sp sp0 M6)
      by (rewrite /sc_sp /M6 upd_ne; [exact Hbosp | nz]).
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M6 upd_ne; [exact Hbos0 | nz]).
    assert (HM6s1 : (M6 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M6 upd_ne; [exact Hbos1 | nz]).
    assert (HM6s2 : (M6 !!! Regidx Rs2 : mword 64) = pj)
      by (rewrite /M6 upd_ne; [exact Hbos2 | nz]).
    assert (HM6thr : sc_thr m M6).
    { intros c Hc N2 N8 N9 N18. rewrite /M6 upd_ne; [| regne].
      exact (Hbothr c Hc N2 N8 N9 N18). }
    assert (Hpp18 : add_vec_int (mword_of_int (SC + 0x14) : mword 64) 4
                    = mword_of_int (SC + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    (* ================= +0x18 addi a1,s0,-160 ================= *)
    iApply (wp_addi4_s_sconf (CID := CID11) (mword_of_int (SC + 0x18)) Ra1 Rs0
              (mword_of_int 3936 : mword 12) M6 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18").
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (M7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M6 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3936 : mword 12)))]> M6).
    assert (HM7a1 : (M7 !!! Regidx Ra1 : mword 64) = pa_stk sp0 20).
    { etransitivity; [ rewrite /M7; apply upd_eq |].
      rewrite HM6s0. apply sc_buf. }
    assert (HM7a2 : (M7 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6a2 | nz]).
    assert (HM7sp : sc_sp sp0 M7)
      by (rewrite /sc_sp /M7 upd_ne; [exact HM6sp | nz]).
    assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M7 upd_ne; [exact HM6s0 | nz]).
    assert (HM7s1 : (M7 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6s1 | nz]).
    assert (HM7s2 : (M7 !!! Regidx Rs2 : mword 64) = pj)
      by (rewrite /M7 upd_ne; [exact HM6s2 | nz]).
    assert (HM7thr : sc_thr m M7).
    { intros c Hc N2 N8 N9 N18. rewrite /M7 upd_ne; [| regne].
      exact (HM6thr c Hc N2 N8 N9 N18). }
    assert (Hpp1c : add_vec_int (mword_of_int (SC + 0x18) : mword 64) 4
                    = mword_of_int (SC + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ================= +0x1c c.li a0,0 ================= *)
    iApply (wp_cli_s_sconf (CID := CID12) (mword_of_int (SC + 0x1c)) Ra0
              (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M7 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi1c").
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (M8 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> M7).
    assert (HM8a0 : (M8 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M8; apply upd_eq).
    assert (HM8a1 : (M8 !!! Regidx Ra1 : mword 64) = pa_stk sp0 20)
      by (rewrite /M8 upd_ne; [exact HM7a1 | nz]).
    assert (HM8a2 : (M8 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7a2 | nz]).
    assert (HM8sp : sc_sp sp0 M8)
      by (rewrite /sc_sp /M8 upd_ne; [exact HM7sp | nz]).
    assert (HM8s0 : (M8 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M8 upd_ne; [exact HM7s0 | nz]).
    assert (HM8s1 : (M8 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7s1 | nz]).
    assert (HM8s2 : (M8 !!! Regidx Rs2 : mword 64) = pj)
      by (rewrite /M8 upd_ne; [exact HM7s2 | nz]).
    assert (HM8thr : sc_thr m M8).
    { intros c Hc N2 N8 N9 N18. rewrite /M8 upd_ne; [| regne].
      exact (HM7thr c Hc N2 N8 N9 N18). }
    assert (Hpp1e : add_vec_int (mword_of_int (SC + 0x1c) : mword 64) 2
                    = mword_of_int (SC + 0x1e)) by pcw.
    iEval (rewrite Hpp1e) in "Hpc".
    (* ================= +0x1e jal ra,argstr ================= *)
    iApply (wp_jal_s_sconf (CID := CID13) (mword_of_int (SC + 0x1e)) Rra
              (mword_of_int 2086276 : mword 21) M8 (K - 20)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1e").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (M9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SC + 0x1e) : mword 64) 4)]> M8).
    assert (Hjas : add_vec (mword_of_int (SC + 0x1e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086276 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iEval (rewrite Hjas) in "Hpc".
    assert (HM9ra : (M9 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SC + 0x1e) : mword 64) 4)
      by (rewrite /M9; apply upd_eq).
    assert (HM9a0 : (M9 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a0 | nz]).
    assert (HM9a1 : (M9 !!! Regidx Ra1 : mword 64) = pa_stk sp0 20)
      by (rewrite /M9 upd_ne; [exact HM8a1 | nz]).
    assert (HM9a2 : (M9 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a2 | nz]).
    assert (HM9sp : sc_sp sp0 M9)
      by (rewrite /sc_sp /M9 upd_ne; [exact HM8sp | nz]).
    assert (HM9s0 : (M9 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M9 upd_ne; [exact HM8s0 | nz]).
    assert (HM9s1 : (M9 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8s1 | nz]).
    assert (HM9s2 : (M9 !!! Regidx Rs2 : mword 64) = pj)
      by (rewrite /M9 upd_ne; [exact HM8s2 | nz]).
    assert (HM9thr : sc_thr m M9).
    { intros c Hc N2 N8 N9 N18. rewrite /M9 upd_ne; [| regne].
      exact (HM8thr c Hc N2 N8 N9 N18). }
    (* the buffer, as the byte window argstr speaks *)
    iDestruct (sc_bytes_name (pa_stk sp0 20) 128 with "Hbytes") as (bf0) "Hbuf".
    iDestruct (cpu_own_transport CID10 CID14 0 eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argstr.wp_argstr_sconf (CID := CID14) ga gf M9 (K - 20)%nat 0%nat eb pj
              0%nat v pid V 128%nat bf0 b lks
              sc_arg0_lt HM9a0 Hargv sc_noff0 ltac:(lia) HM9a2 sc_maxpath_lt
              (Hlb "kmem"%string)
              with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [Hbuf]").
    { iEval (rewrite HM9a1). iExact "Hbuf". }
    iIntros (CID15 Hq15 mas P' bf) "%Hcsas %Hupt Hcg Hown Hpc Hpriv Hbuf %Hfsr".
    iEval (rewrite HM9a1) in "Hbuf".
    assert (Hpc22 : ret_pc (M9 !!! Regidx Rra : mword 64)
                    = mword_of_int (SC + 0x22)) by (rewrite HM9ra; pcw).
    iEval (rewrite Hpc22) in "Hpc".
    assert (Hassp : sc_sp sp0 mas).
    { rewrite /sc_sp (callee_saved_lookup Hcsas csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM9sp. }
    assert (Hass0 : (mas !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsas Rs0 ltac:(vm_compute; reflexivity)).
      exact HM9s0. }
    assert (Hass1 : (mas !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcsas Rs1 ltac:(vm_compute; reflexivity)).
      exact HM9s1. }
    assert (Hass2 : (mas !!! Regidx Rs2 : mword 64) = pj).
    { rewrite (callee_saved_lookup Hcsas Rs2 ltac:(vm_compute; reflexivity)).
      exact HM9s2. }
    assert (Hasthr : sc_thr m mas).
    { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsas c Hc).
      exact (HM9thr c Hc N2 N8 N9 N18). }
    (* ================= +0x22 bltz a0 -> ARM A ================= *)
    destruct Hfsr as [(pk & Hpk & Hpcstr & Hpr) | Hpr].
    - (* ---- the string fetched: the [bltz] FALLS THROUGH ---- *)
      iApply (wp_blt_x0_fall_s_sconf (CID := CID15) (mword_of_int (SC + 0x22))
                (mword_of_int 70 : mword 13) Ra0 mas (K - 20)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Hpr; exact (sc_nonneg _ (sc_len_range pk Hpk)))
                with "Hcg Hpc Hi22").
      iIntros (CID16 Hq16) "Hcg Hpc".
      assert (Hpp26 : add_vec_int (mword_of_int (SC + 0x22) : mword 64) 4
                      = mword_of_int (SC + 0x26)) by pcw.
      iEval (rewrite Hpp26) in "Hpc".
      (* ============ +0x26 c.sdsp s1,136(sp) -- slot 3, saved LATE ======= *)
      assert (Hd3 : add_vec (mas !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
                    = pa_stk sp0 3) by (rewrite Hassp; apply sc_frm3).
      iEval (rewrite -Hd3) in "Hf3".
      iApply (wp_csdsp_s_sconf (CID := CID16) (mword_of_int (SC + 0x26))
                (mword_of_int 17 : mword 6) Rs1 mas (K - 20)%nat u3 b
                with "Hcg Hpc Hi26 Hf3").
      iIntros (CID17 Hq17) "Hcg Hpc Hf3".
      iEval (rgne; rewrite Hd3 Hass1) in "Hf3".
      assert (Hpp28 : add_vec_int (mword_of_int (SC + 0x26) : mword 64) 2
                      = mword_of_int (SC + 0x28)) by pcw.
      iEval (rewrite Hpp28) in "Hpc".
      (* ============ +0x28 addi a0,s0,-160 ============ *)
      iApply (wp_addi4_s_sconf (CID := CID17) (mword_of_int (SC + 0x28)) Ra0 Rs0
                (mword_of_int 3936 : mword 12) mas (K - 20)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi28").
      iIntros (CID18 Hq18) "Hcg Hpc".
      set (N0 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (mas !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 3936 : mword 12)))]> mas).
      assert (HN0a0 : (N0 !!! Regidx Ra0 : mword 64) = pa_stk sp0 20).
      { etransitivity; [ rewrite /N0; apply upd_eq |].
        rewrite Hass0. apply sc_buf. }
      assert (HN0sp : sc_sp sp0 N0)
        by (rewrite /sc_sp /N0 upd_ne; [exact Hassp | nz]).
      assert (HN0s0 : (N0 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N0 upd_ne; [exact Hass0 | nz]).
      assert (HN0s1 : (N0 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
        by (rewrite /N0 upd_ne; [exact Hass1 | nz]).
      assert (HN0s2 : (N0 !!! Regidx Rs2 : mword 64) = pj)
        by (rewrite /N0 upd_ne; [exact Hass2 | nz]).
      assert (HN0thr : sc_thr m N0).
      { intros c Hc N2 N8 N9 N18. rewrite /N0 upd_ne; [| regne].
        exact (Hasthr c Hc N2 N8 N9 N18). }
      assert (Hpp2c : add_vec_int (mword_of_int (SC + 0x28) : mword 64) 4
                      = mword_of_int (SC + 0x2c)) by pcw.
      iEval (rewrite Hpp2c) in "Hpc".
      (* ============ +0x2c jal ra,namei ============ *)
      iApply (wp_jal_s_sconf (CID := CID18) (mword_of_int (SC + 0x2c)) Rra
                (mword_of_int 2090844 : mword 21) N0 (K - 20)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2c").
      iIntros (CID19 Hq19) "Hcg Hpc".
      set (N1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SC + 0x2c) : mword 64) 4)]> N0).
      assert (Hjna : add_vec (mword_of_int (SC + 0x2c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2090844 : mword 21))
                     = mword_of_int KernelSyms.namei) by pcw.
      iEval (rewrite Hjna) in "Hpc".
      assert (HN1ra : (N1 !!! Regidx Rra : mword 64)
                      = add_vec_int (mword_of_int (SC + 0x2c) : mword 64) 4)
        by (rewrite /N1; apply upd_eq).
      assert (HN1a0 : (N1 !!! Regidx Ra0 : mword 64) = pa_stk sp0 20)
        by (rewrite /N1 upd_ne; [exact HN0a0 | nz]).
      assert (HN1sp : sc_sp sp0 N1)
        by (rewrite /sc_sp /N1 upd_ne; [exact HN0sp | nz]).
      assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N1 upd_ne; [exact HN0s0 | nz]).
      assert (HN1s1 : (N1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
        by (rewrite /N1 upd_ne; [exact HN0s1 | nz]).
      assert (HN1s2 : (N1 !!! Regidx Rs2 : mword 64) = pj)
        by (rewrite /N1 upd_ne; [exact HN0s2 | nz]).
      assert (HN1thr : sc_thr m N1).
      { intros c Hc N2 N8 N9 N18. rewrite /N1 upd_ne; [| regne].
        exact (HN0thr c Hc N2 N8 N9 N18). }
      (* THE RESOURCE PLAN'S STEP 3: the reference comes off the block, then
         the cell and the pid quarter, and all three stay out until the
         [sd s1,336(s2)] (or, on the failure arms, until the tail returns). *)
      iDestruct (proc_priv_split_cwd gf pj pid (upd_upt V P') with "Hpriv")
        as "[Hpnc Href]".
      iDestruct (proc_priv_nocwd_cwd_pid gf pj pid (upd_upt V P') with "Hpnc")
        as "(Hcwd & Hpidq & Hpback)".
      iDestruct (cwd_ref_held with "Href") as "Hcwdref".
      iEval (cbn [upd_upt pv_cwd]) in "Hcwd".
      iEval (cbn [upd_upt pv_cwd]) in "Hcwdref".
      iDestruct (sc_buf_split (pa_stk sp0 20) bf pk Hpk with "Hbuf")
        as "[Hbufk Hbufrest]".
      iDestruct "Hop" as (Sb0) "HopS".
      iDestruct (cpu_own_transport CID15 CID19 0 eb pj b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Namei.wp_namei_gen (CID := CID19) gs j gl gu gd gk pd pav pu bn
                g gfs gi cn gtl ga gf cov logstart bmapstart inodestart nib
                size dev used (pv_cwd V) pk bf MAXOPBLOCKS Sb0
                pid (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
                N1 (K - 20)%nat eb b lks
                ltac:(lia) Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom Hsize
                Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hpcstr
                (sc_plen_lt pk Hpk) (sc_bud_walk _) Hj Hgl Heb
                with "Hcg Hown Htext Hdata Hpc Hpanic Hpe Hbio Hlog Hkenv Hitab Hitinv
                      Hescrows Hslks Hireg Hprocs Hdev Hgeo Hdlk Hsbb Hsbi
                      Hbmres Hpidq Hcwd Hcwdref [Hbufk] Hbsl Hir HopS").
      { iEval (rewrite HN1a0). iExact "Hbufk". }
      iIntros (CID20 Hq20 mna n1 used1 Sb1 ok ipv w1)
        "%Hcsna Hcg Hown Hpc Hsbb Hsbi %Hused1 Hbmres Hpidq Hcwd Hcwdref
         Hbufk Hbsl %HSb1 %Hw1 %Hn1 HopS Hres".
      iEval (rewrite HN1a0) in "Hbufk".
      assert (Hpc30 : ret_pc (N1 !!! Regidx Rra : mword 64)
                      = mword_of_int (SC + 0x30)) by (rewrite HN1ra; pcw).
      iEval (rewrite Hpc30) in "Hpc".
      assert (Hnasp : sc_sp sp0 mna).
      { rewrite /sc_sp (callee_saved_lookup Hcsna csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HN1sp. }
      assert (Hnas0 : (mna !!! Regidx Rs0 : mword 64) = sp0).
      { rewrite (callee_saved_lookup Hcsna Rs0 ltac:(vm_compute; reflexivity)).
        exact HN1s0. }
      assert (Hnas1 : (mna !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
      { rewrite (callee_saved_lookup Hcsna Rs1 ltac:(vm_compute; reflexivity)).
        exact HN1s1. }
      assert (Hnas2 : (mna !!! Regidx Rs2 : mword 64) = pj).
      { rewrite (callee_saved_lookup Hcsna Rs2 ltac:(vm_compute; reflexivity)).
        exact HN1s2. }
      assert (Hnathr : sc_thr m mna).
      { intros c Hc N2 N8 N9 N18. rewrite (callee_saved_lookup Hcsna c Hc).
        exact (HN1thr c Hc N2 N8 N9 N18). }
      (* ============ +0x30 c.mv s1,a0 ============ *)
      iApply (wp_cmv_s_sconf (CID := CID20) (mword_of_int (SC + 0x30)) Rs1 Ra0
                mna (K - 20)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30").
      iIntros (CID21 Hq21) "Hcg Hpc".
      set (N2 := <[Regidx Rs1 := regval_into_reg
                    (add_vec zero_reg (mna !!! Regidx Ra0))]> mna).
      assert (HN2s1 : (N2 !!! Regidx Rs1 : mword 64)
                      = (mna !!! Regidx Ra0 : mword 64)).
      { etransitivity; [ rewrite /N2; apply upd_eq |]. apply add_vec_zero_l. }
      assert (HN2a0 : (N2 !!! Regidx Ra0 : mword 64)
                      = (mna !!! Regidx Ra0 : mword 64))
        by (rewrite /N2 upd_ne; [reflexivity | nz]).
      assert (HN2sp : sc_sp sp0 N2)
        by (rewrite /sc_sp /N2 upd_ne; [exact Hnasp | nz]).
      assert (HN2s0 : (N2 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /N2 upd_ne; [exact Hnas0 | nz]).
      assert (HN2s2 : (N2 !!! Regidx Rs2 : mword 64) = pj)
        by (rewrite /N2 upd_ne; [exact Hnas2 | nz]).
      assert (HN2thr : sc_thr m N2).
      { intros c Hc N2' N8 N9 N18. rewrite /N2 upd_ne; [| regne].
        exact (Hnathr c Hc N2' N8 N9 N18). }
      assert (Hpp32 : add_vec_int (mword_of_int (SC + 0x30) : mword 64) 2
                      = mword_of_int (SC + 0x32)) by pcw.
      iEval (rewrite Hpp32) in "Hpc".
      (* ============ +0x32 c.beqz a0 -> ARM B ============ *)
      destruct ok.
      + (* ---- the path RESOLVED ---- *)
        iDestruct "Hres" as "(%Hnaip & Hheldip & Hir)".
        iDestruct (inode_held_ne_zero with "Hheldip") as %Hipnz.
        (* ---- the path RESOLVED: the [c.beqz] falls through ---- *)
        iApply (wp_cbeqz_fall_s_sconf (CID := CID21) (mword_of_int (SC + 0x32))
                  (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  N2 (K - 20)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HN2a0 Hnaip;
                        apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
                  with "Hcg Hpc Hi32").
        iIntros (CID22 Hq22) "Hcg Hpc".
        assert (Hpp34 : add_vec_int (mword_of_int (SC + 0x32) : mword 64) 2
                        = mword_of_int (SC + 0x34)) by pcw.
        iEval (rewrite Hpp34) in "Hpc".
        (* THE REFERENCE namei MADE, taken apart: the slot it names is what
           ilock / iunlock / iunlockput are all indexed by. *)
        iDestruct "Hheldip" as (kk qq inum) "(%Hipe & %Hkk & %Hinumc & Hrefip)".
        iEval (rewrite -Hcdev) in "Hrefip".
        assert (Hinb : bv_unsigned inum < 16 * Z.of_nat nib)
          by (rewrite Hcnib; exact Hinumc).
        destruct (Hiregb inum Hinb) as [Hiblk Hiblog].
        iEval (rewrite inode_ref_shed) in "Hrefip".
        iDestruct "Hrefip" as "[Hkeep Hshr]".
        iEval (rewrite inode_shr_gen_intro) in "Hshr".
        iDestruct "Hshr" as (gsh) "Hshr".
        iDestruct (sc_esc_acc cn gfs gi cov logstart kk Hkk with "Hescrows")
          as "#Hesck".
        iDestruct (sc_slk_acc cn kk Hkk with "Hslks") as (gil gisl) "#Hslkk".
        iDestruct (sc_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
        (* ============ +0x34 jal ra,ilock ============ *)
        iApply (wp_jal_s_sconf (CID := CID22) (mword_of_int (SC + 0x34)) Rra
                  (mword_of_int 2088720 : mword 21) N2 (K - 20)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi34").
        iIntros (CID23 Hq23) "Hcg Hpc".
        set (P0 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (SC + 0x34) : mword 64) 4)]> N2).
        assert (Hjil : add_vec (mword_of_int (SC + 0x34) : mword 64)
                         (sign_extend' 64 (mword_of_int 2088720 : mword 21))
                       = mword_of_int KernelSyms.ilock) by pcw.
        iEval (rewrite Hjil) in "Hpc".
        assert (HP0ra : (P0 !!! Regidx Rra : mword 64)
                        = add_vec_int (mword_of_int (SC + 0x34) : mword 64) 4)
          by (rewrite /P0; apply upd_eq).
        assert (HP0a0 : (P0 !!! Regidx Ra0 : mword 64) = ientry kk).
        { rewrite /P0 upd_ne; [| nz]. rewrite HN2a0 Hnaip. exact Hipe. }
        assert (HP0s1 : (P0 !!! Regidx Rs1 : mword 64) = ientry kk).
        { rewrite /P0 upd_ne; [| nz]. rewrite HN2s1 Hnaip. exact Hipe. }
        assert (HP0sp : sc_sp sp0 P0)
          by (rewrite /sc_sp /P0 upd_ne; [exact HN2sp | nz]).
        assert (HP0s0 : (P0 !!! Regidx Rs0 : mword 64) = sp0)
          by (rewrite /P0 upd_ne; [exact HN2s0 | nz]).
        assert (HP0s2 : (P0 !!! Regidx Rs2 : mword 64) = pj)
          by (rewrite /P0 upd_ne; [exact HN2s2 | nz]).
        assert (HP0thr : sc_thr m P0).
        { intros c Hc N2' N8 N9 N18. rewrite /P0 upd_ne; [| regne].
          exact (HN2thr c Hc N2' N8 N9 N18). }
        iDestruct (cpu_own_transport CID20 CID23 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Ilock.wp_ilock_sconf (CID := CID23) gs j gl gu gd gk pd pav pu
                  bn gfs gi cn gil gisl cov logstart inodestart nib
                  kk (qq/2)%Qp gsh dev inum pid (DfracOwn (1/4)) dqs
                  P0 (K - 20)%nat eb b lks
                  ltac:(lia) Hkk Hgeom Hist0 Hiblk Hinb Hj Hgl HP0a0
                  (Hlb "bcache"%string)
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpanic Hpe Hbio Hitinv Hesck
                        Hireg Hslkk Hshr Hsbi Hpidq Hprocs Hdev Hgeo Hdlk Hbs1").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        iIntros (CID24 Hq24 mil dn bm fl)
          "%Hcsil Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1 Hslkd Hslpid Hdep
           Hidev Hiinum Hivalid Hload #Hshot %Hfl".
        assert (Hpc38 : ret_pc (P0 !!! Regidx Rra : mword 64)
                        = mword_of_int (SC + 0x38)) by (rewrite HP0ra; pcw).
        iEval (rewrite Hpc38) in "Hpc".
        assert (Hilsp : sc_sp sp0 mil).
        { rewrite /sc_sp (callee_saved_lookup Hcsil csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HP0sp. }
        assert (Hils0 : (mil !!! Regidx Rs0 : mword 64) = sp0).
        { rewrite (callee_saved_lookup Hcsil Rs0 ltac:(vm_compute; reflexivity)).
          exact HP0s0. }
        assert (Hils1 : (mil !!! Regidx Rs1 : mword 64) = ientry kk).
        { rewrite (callee_saved_lookup Hcsil Rs1 ltac:(vm_compute; reflexivity)).
          exact HP0s1. }
        assert (Hils2 : (mil !!! Regidx Rs2 : mword 64) = pj).
        { rewrite (callee_saved_lookup Hcsil Rs2 ltac:(vm_compute; reflexivity)).
          exact HP0s2. }
        assert (Hilthr : sc_thr m mil).
        { intros c Hc N2' N8 N9 N18. rewrite (callee_saved_lookup Hcsil c Hc).
          exact (HP0thr c Hc N2' N8 N9 N18). }
        iDestruct "Hload" as (dat)
          "(%Hiok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta & Haddrs & Hind
            & Hblocks)".
        iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
        iEval (rewrite /i_type) in "Hity".
        (* ============ +0x38 lh a4,68(s1) -- ip->type ============ *)
        iApply (wp_lh_s_sconf (CID := CID24) (mword_of_int (SC + 0x38)) Ra4 Rs1
                  (mword_of_int 68 : mword 12) mil (K - 20)%nat
                  (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi38 [Hity]").
        { iEval (rgne; rewrite Hils1). iExact "Hity". }
        iIntros (CID25 Hq25) "Hcg Hpc Hity".
        iEval (rgne; rewrite Hils1) in "Hity".
        set (P1 := <[Regidx Ra4 := regval_into_reg
                      (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> mil).
        assert (HP1a4 : (P1 !!! Regidx Ra4 : mword 64)
                        = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
          by (rewrite /P1; apply upd_eq).
        assert (HP1sp : sc_sp sp0 P1)
          by (rewrite /sc_sp /P1 upd_ne; [exact Hilsp | nz]).
        assert (HP1s0 : (P1 !!! Regidx Rs0 : mword 64) = sp0)
          by (rewrite /P1 upd_ne; [exact Hils0 | nz]).
        assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
          by (rewrite /P1 upd_ne; [exact Hils1 | nz]).
        assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = pj)
          by (rewrite /P1 upd_ne; [exact Hils2 | nz]).
        assert (HP1thr : sc_thr m P1).
        { intros c Hc N2' N8 N9 N18. rewrite /P1 upd_ne; [| regne].
          exact (Hilthr c Hc N2' N8 N9 N18). }
        assert (Hpp3c : add_vec_int (mword_of_int (SC + 0x38) : mword 64) 4
                        = mword_of_int (SC + 0x3c)) by pcw.
        iEval (rewrite Hpp3c) in "Hpc".
        (* ============ +0x3c c.li a5,1 ============ *)
        iApply (wp_cli_s_sconf (CID := CID25) (mword_of_int (SC + 0x3c)) Ra5
                  (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                  P1 (K - 20)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi3c").
        iIntros (CID26 Hq26) "Hcg Hpc".
        set (P2 := <[Regidx Ra5 := regval_into_reg
                      (mword_of_int 1 : mword 64)]> P1).
        assert (HP2a5 : (P2 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
          by (rewrite /P2; apply upd_eq).
        assert (HP2a4 : (P2 !!! Regidx Ra4 : mword 64)
                        = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
          by (rewrite /P2 upd_ne; [exact HP1a4 | nz]).
        assert (HP2sp : sc_sp sp0 P2)
          by (rewrite /sc_sp /P2 upd_ne; [exact HP1sp | nz]).
        assert (HP2s0 : (P2 !!! Regidx Rs0 : mword 64) = sp0)
          by (rewrite /P2 upd_ne; [exact HP1s0 | nz]).
        assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = ientry kk)
          by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
        assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = pj)
          by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
        assert (HP2thr : sc_thr m P2).
        { intros c Hc N2' N8 N9 N18. rewrite /P2 upd_ne; [| regne].
          exact (HP1thr c Hc N2' N8 N9 N18). }
        assert (Hpp3e : add_vec_int (mword_of_int (SC + 0x3c) : mword 64) 2
                        = mword_of_int (SC + 0x3e)) by pcw.
        iEval (rewrite Hpp3e) in "Hpc".
        (* the two log-budget figures the tail needs, once *)
        assert (Hiu : (iput_units <= n1)%nat)
          by exact (sc_bud_iput _ w1 true (proj1 Hn1)).
        (* ============ +0x3e bne a4,a5 -> ARM C ============ *)
        destruct (decide (di_type dn = (mword_of_int 1 : mword 16))) as [Hty | Hty].
        * (* ======== IT IS A DIRECTORY: the success tail ======== *)
          iApply (wp_bne_fall_s_sconf (CID := CID26) (mword_of_int (SC + 0x3e))
                    (mword_of_int 50 : mword 13) Ra5 Ra4 P2 (K - 20)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HP2a4 HP2a5; exact (sc_tdir_eq _ Hty))
                    with "Hcg Hpc Hi3e").
          iIntros (CID27 Hq27) "Hcg Hpc".
          assert (Hpp42 : add_vec_int (mword_of_int (SC + 0x3e) : mword 64) 4
                          = mword_of_int (SC + 0x42)) by pcw.
          iEval (rewrite Hpp42) in "Hpc".
          (* ============ +0x42 c.mv a0,s1 ============ *)
          iApply (wp_cmv_s_sconf (CID := CID27) (mword_of_int (SC + 0x42)) Ra0 Rs1
                    P2 (K - 20)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi42").
          iIntros (CID28 Hq28) "Hcg Hpc".
          set (P3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec zero_reg (P2 !!! Regidx Rs1))]> P2).
          assert (HP3a0 : (P3 !!! Regidx Ra0 : mword 64) = ientry kk).
          { etransitivity; [ rewrite /P3; apply upd_eq |].
            rewrite add_vec_zero_l. exact HP2s1. }
          assert (HP3sp : sc_sp sp0 P3)
            by (rewrite /sc_sp /P3 upd_ne; [exact HP2sp | nz]).
          assert (HP3s0 : (P3 !!! Regidx Rs0 : mword 64) = sp0)
            by (rewrite /P3 upd_ne; [exact HP2s0 | nz]).
          assert (HP3s1 : (P3 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /P3 upd_ne; [exact HP2s1 | nz]).
          assert (HP3s2 : (P3 !!! Regidx Rs2 : mword 64) = pj)
            by (rewrite /P3 upd_ne; [exact HP2s2 | nz]).
          assert (HP3thr : sc_thr m P3).
          { intros c Hc N2' N8 N9 N18. rewrite /P3 upd_ne; [| regne].
            exact (HP2thr c Hc N2' N8 N9 N18). }
          assert (Hpp44 : add_vec_int (mword_of_int (SC + 0x42) : mword 64) 2
                          = mword_of_int (SC + 0x44)) by pcw.
          iEval (rewrite Hpp44) in "Hpc".
          (* ============ +0x44 jal ra,iunlock ============ *)
          iApply (wp_jal_s_sconf (CID := CID28) (mword_of_int (SC + 0x44)) Rra
                    (mword_of_int 2088878 : mword 21) P3 (K - 20)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi44").
          iIntros (CID29 Hq29) "Hcg Hpc".
          set (P4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (SC + 0x44) : mword 64) 4)]> P3).
          assert (Hjiu : add_vec (mword_of_int (SC + 0x44) : mword 64)
                           (sign_extend' 64 (mword_of_int 2088878 : mword 21))
                         = mword_of_int KernelSyms.iunlock) by pcw.
          iEval (rewrite Hjiu) in "Hpc".
          assert (HP4ra : (P4 !!! Regidx Rra : mword 64)
                          = add_vec_int (mword_of_int (SC + 0x44) : mword 64) 4)
            by (rewrite /P4; apply upd_eq).
          assert (HP4a0 : (P4 !!! Regidx Ra0 : mword 64) = ientry kk)
            by (rewrite /P4 upd_ne; [exact HP3a0 | nz]).
          assert (HP4sp : sc_sp sp0 P4)
            by (rewrite /sc_sp /P4 upd_ne; [exact HP3sp | nz]).
          assert (HP4s0 : (P4 !!! Regidx Rs0 : mword 64) = sp0)
            by (rewrite /P4 upd_ne; [exact HP3s0 | nz]).
          assert (HP4s1 : (P4 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /P4 upd_ne; [exact HP3s1 | nz]).
          assert (HP4s2 : (P4 !!! Regidx Rs2 : mword 64) = pj)
            by (rewrite /P4 upd_ne; [exact HP3s2 | nz]).
          assert (HP4thr : sc_thr m P4).
          { intros c Hc N2' N8 N9 N18. rewrite /P4 upd_ne; [| regne].
            exact (HP3thr c Hc N2' N8 N9 N18). }
          iAssert (ic_loaded gfs gi cov logstart kk inum dn bm)
            with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind Hblocks Hdlnk]"
            as "Hload".
          { rewrite /ic_loaded. iExists dat.
            iSplitR; [iPureIntro; exact Hiok |].
            iSplitR; [iPureIntro; exact Hdok |].
            iSplitR; [iPureIntro; exact Hddix |].
            iSplitR; [iPureIntro; exact Hdoc |].
            iSplitR; [iPureIntro; exact Hduq |].
            iSplitL "Hdlnk"; [iExact "Hdlnk" |].
            iFrame "Hdiat".
            iSplitL "Hity Himaj Himin Hinl Hisz".
            - rewrite /inode_meta /i_type. iFrame.
            - iFrame. }
          iDestruct (cpu_own_transport CID24 CID29 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (Iunlock.wp_iunlock_sconf (CID := CID29) gs gfs gi cn gil gisl
                    cov logstart kk (qq/2)%Qp gsh dev inum dn bm
                    pid (DfracOwn (1/4)) P4 (K - 20)%nat eb pj b lks
                    ltac:(lia) Hkk HP4a0 (Hlb "sleep lock"%string)
                    with "Hcg Hown Htext Hpc Hpanic Hitinv Hesck Hslkk Hslkd
                          Hslpid Hpidq Hprocs Hdep Hidev Hiinum Hivalid Hload
                          Hshot").
          iIntros (CID30 Hq30 miu) "%Hcsiu Hcg Hown Hpc Hpidq Hshr".
          iDestruct (inode_shr_gen_forget with "Hshr") as "Hshr".
          assert (Hpc48 : ret_pc (P4 !!! Regidx Rra : mword 64)
                          = mword_of_int (SC + 0x48)) by (rewrite HP4ra; pcw).
          iEval (rewrite Hpc48) in "Hpc".
          assert (Hiusp : sc_sp sp0 miu).
          { rewrite /sc_sp (callee_saved_lookup Hcsiu csp_rs1 ltac:(vm_compute; reflexivity)).
            exact HP4sp. }
          assert (Hius0 : (miu !!! Regidx Rs0 : mword 64) = sp0).
          { rewrite (callee_saved_lookup Hcsiu Rs0 ltac:(vm_compute; reflexivity)).
            exact HP4s0. }
          assert (Hius1 : (miu !!! Regidx Rs1 : mword 64) = ientry kk).
          { rewrite (callee_saved_lookup Hcsiu Rs1 ltac:(vm_compute; reflexivity)).
            exact HP4s1. }
          assert (Hius2 : (miu !!! Regidx Rs2 : mword 64) = pj).
          { rewrite (callee_saved_lookup Hcsiu Rs2 ltac:(vm_compute; reflexivity)).
            exact HP4s2. }
          assert (Hiuthr : sc_thr m miu).
          { intros c Hc N2' N8 N9 N18. rewrite (callee_saved_lookup Hcsiu c Hc).
            exact (HP4thr c Hc N2' N8 N9 N18). }
          (* the reference, re-formed: this is the one the [sd] installs *)
          iDestruct (inode_ref_gather with "Hkeep Hshr") as "Hrefnew".
          (* ============ +0x48 ld a0,336(s2) -- a0 := p->cwd ============ *)
          iApply (wp_ld_s_sconf (CID := CID30) (mword_of_int (SC + 0x48)) Ra0 Rs2
                    (mword_of_int 336 : mword 12) miu (K - 20)%nat (pv_cwd V) b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi48 [Hcwd]").
          { iEval (rgne; rewrite Hius2 p_cwd_sext). iExact "Hcwd". }
          iIntros (CID31 Hq31) "Hcg Hpc Hcwd".
          iEval (rgne; rewrite Hius2 p_cwd_sext) in "Hcwd".
          set (P5 := <[Regidx Ra0 := regval_into_reg (pv_cwd V)]> miu).
          assert (HP5a0 : (P5 !!! Regidx Ra0 : mword 64) = pv_cwd V)
            by (rewrite /P5; apply upd_eq).
          assert (HP5sp : sc_sp sp0 P5)
            by (rewrite /sc_sp /P5 upd_ne; [exact Hiusp | nz]).
          assert (HP5s0 : (P5 !!! Regidx Rs0 : mword 64) = sp0)
            by (rewrite /P5 upd_ne; [exact Hius0 | nz]).
          assert (HP5s1 : (P5 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /P5 upd_ne; [exact Hius1 | nz]).
          assert (HP5s2 : (P5 !!! Regidx Rs2 : mword 64) = pj)
            by (rewrite /P5 upd_ne; [exact Hius2 | nz]).
          assert (HP5thr : sc_thr m P5).
          { intros c Hc N2' N8 N9 N18. rewrite /P5 upd_ne; [| regne].
            exact (Hiuthr c Hc N2' N8 N9 N18). }
          assert (Hpp4c : add_vec_int (mword_of_int (SC + 0x48) : mword 64) 4
                          = mword_of_int (SC + 0x4c)) by pcw.
          iEval (rewrite Hpp4c) in "Hpc".
          (* ============ +0x4c jal ra,iput -- the OLD cwd ============ *)
          iApply (wp_jal_s_sconf (CID := CID31) (mword_of_int (SC + 0x4c)) Rra
                    (mword_of_int 2089082 : mword 21) P5 (K - 20)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi4c").
          iIntros (CID32 Hq32) "Hcg Hpc".
          set (P6 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (SC + 0x4c) : mword 64) 4)]> P5).
          assert (Hjip : add_vec (mword_of_int (SC + 0x4c) : mword 64)
                           (sign_extend' 64 (mword_of_int 2089082 : mword 21))
                         = mword_of_int KernelSyms.iput) by pcw.
          iEval (rewrite Hjip) in "Hpc".
          assert (HP6ra : (P6 !!! Regidx Rra : mword 64)
                          = add_vec_int (mword_of_int (SC + 0x4c) : mword 64) 4)
            by (rewrite /P6; apply upd_eq).
          assert (HP6a0 : (P6 !!! Regidx Ra0 : mword 64) = pv_cwd V)
            by (rewrite /P6 upd_ne; [exact HP5a0 | nz]).
          assert (HP6sp : sc_sp sp0 P6)
            by (rewrite /sc_sp /P6 upd_ne; [exact HP5sp | nz]).
          assert (HP6s0 : (P6 !!! Regidx Rs0 : mword 64) = sp0)
            by (rewrite /P6 upd_ne; [exact HP5s0 | nz]).
          assert (HP6s1 : (P6 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /P6 upd_ne; [exact HP5s1 | nz]).
          assert (HP6s2 : (P6 !!! Regidx Rs2 : mword 64) = pj)
            by (rewrite /P6 upd_ne; [exact HP5s2 | nz]).
          assert (HP6thr : sc_thr m P6).
          { intros c Hc N2' N8 N9 N18. rewrite /P6 upd_ne; [| regne].
            exact (HP5thr c Hc N2' N8 N9 N18). }
          (* THE OLD WORKING DIRECTORY's reference, taken apart *)
          iDestruct "Hcwdref" as (kc qc inumc) "(%Hcwde & %Hkc & %Hinumcc & Hrefc)".
          iEval (rewrite -Hcdev) in "Hrefc".
          assert (Hinbc : bv_unsigned inumc < 16 * Z.of_nat nib)
            by (rewrite Hcnib; exact Hinumcc).
          destruct (Hiregb inumc Hinbc) as [Hiblkc Hiblogc].
          iDestruct (sc_esc_acc cn gfs gi cov logstart kc Hkc with "Hescrows")
            as "#Hescc".
          iDestruct (sc_slk_acc cn kc Hkc with "Hslks") as (gilc gislc) "#Hslkc".
          iDestruct (sc_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (cpu_own_transport CID30 CID32 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (Iput.wp_iput_sconf (CID := CID32) gs j gl gu gd gk pd pav pu bn
                    g gfs gi cn gtl gilc gislc cov logstart bmapstart inodestart
                    nib size dev used1 kc qc inumc n1 pid (DfracOwn (1/4)) dqb dqs
                    P6 (K - 20)%nat eb b lks
                    ltac:(lia) Hkc Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                    Hiblkc Hiblogc Hinbc Hcovb Hiu Hj Hgl
                    ltac:(rewrite HP6a0; exact Hcwde) (Hlb "log"%string)
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpanic Hpe Hbio Hlog Hitab Hitinv
                          Hescc Hireg Hslkc Hrefc Hsbb Hsbi Hbmres Hpidq Hprocs
                          Hdev Hgeo Hdlk Hbsl [HopS]").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { rewrite /log_op. iExists Sb1. iExact "HopS". }
          iIntros (CID33 Hq33 mip n2 used2)
            "%Hcsip Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
             Hop Hislot".
          assert (Hpc50 : ret_pc (P6 !!! Regidx Rra : mword 64)
                          = mword_of_int (SC + 0x50)) by (rewrite HP6ra; pcw).
          iEval (rewrite Hpc50) in "Hpc".
          assert (Hipsp : sc_sp sp0 mip).
          { rewrite /sc_sp (callee_saved_lookup Hcsip csp_rs1 ltac:(vm_compute; reflexivity)).
            exact HP6sp. }
          assert (Hips0 : (mip !!! Regidx Rs0 : mword 64) = sp0).
          { rewrite (callee_saved_lookup Hcsip Rs0 ltac:(vm_compute; reflexivity)).
            exact HP6s0. }
          assert (Hips1 : (mip !!! Regidx Rs1 : mword 64) = ientry kk).
          { rewrite (callee_saved_lookup Hcsip Rs1 ltac:(vm_compute; reflexivity)).
            exact HP6s1. }
          assert (Hips2 : (mip !!! Regidx Rs2 : mword 64) = pj).
          { rewrite (callee_saved_lookup Hcsip Rs2 ltac:(vm_compute; reflexivity)).
            exact HP6s2. }
          assert (Hipthr : sc_thr m mip).
          { intros c Hc N2' N8 N9 N18. rewrite (callee_saved_lookup Hcsip c Hc).
            exact (HP6thr c Hc N2' N8 N9 N18). }
          (* ============ +0x50 jal ra,end_op ============ *)
          iApply (wp_jal_s_sconf (CID := CID33) (mword_of_int (SC + 0x50)) Rra
                    (mword_of_int 2091426 : mword 21) mip (K - 20)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi50").
          iIntros (CID34 Hq34) "Hcg Hpc".
          set (P7 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (SC + 0x50) : mword 64) 4)]> mip).
          assert (Hjeo : add_vec (mword_of_int (SC + 0x50) : mword 64)
                           (sign_extend' 64 (mword_of_int 2091426 : mword 21))
                         = mword_of_int KernelSyms.end_op) by pcw.
          iEval (rewrite Hjeo) in "Hpc".
          assert (HP7ra : (P7 !!! Regidx Rra : mword 64)
                          = add_vec_int (mword_of_int (SC + 0x50) : mword 64) 4)
            by (rewrite /P7; apply upd_eq).
          assert (HP7sp : sc_sp sp0 P7)
            by (rewrite /sc_sp /P7 upd_ne; [exact Hipsp | nz]).
          assert (HP7s0 : (P7 !!! Regidx Rs0 : mword 64) = sp0)
            by (rewrite /P7 upd_ne; [exact Hips0 | nz]).
          assert (HP7s1 : (P7 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /P7 upd_ne; [exact Hips1 | nz]).
          assert (HP7s2 : (P7 !!! Regidx Rs2 : mword 64) = pj)
            by (rewrite /P7 upd_ne; [exact Hips2 | nz]).
          assert (HP7thr : sc_thr m P7).
          { intros c Hc N2' N8 N9 N18. rewrite /P7 upd_ne; [| regne].
            exact (Hipthr c Hc N2' N8 N9 N18). }
          iDestruct (cpu_own_transport CID33 CID34 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (EndOp.wp_end_op_sconf (CID := CID34) gs j gl gu gd gk pd pav pu
                    bn g gfs cov logstart dev n2 pid (DfracOwn (1/4))
                    P7 (K - 20)%nat eb b lks
                    ltac:(lia) Hgeom Hj Hgl (Hlb "log"%string)
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpanic Hpe Hbio Hlog Hseam Hgen
                          Hpidq Hprocs Hdev Hgeo Hdlk Hop").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          iIntros (CID35 Hq35 meo) "%Hcseo Hcg Hown _ _ Hpc Hpidq".
          assert (Hpc54 : ret_pc (P7 !!! Regidx Rra : mword 64)
                          = mword_of_int (SC + 0x54)) by (rewrite HP7ra; pcw).
          iEval (rewrite Hpc54) in "Hpc".
          assert (Heosp : sc_sp sp0 meo).
          { rewrite /sc_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
            exact HP7sp. }
          assert (Heos0 : (meo !!! Regidx Rs0 : mword 64) = sp0).
          { rewrite (callee_saved_lookup Hcseo Rs0 ltac:(vm_compute; reflexivity)).
            exact HP7s0. }
          assert (Heos1 : (meo !!! Regidx Rs1 : mword 64) = ientry kk).
          { rewrite (callee_saved_lookup Hcseo Rs1 ltac:(vm_compute; reflexivity)).
            exact HP7s1. }
          assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = pj).
          { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
            exact HP7s2. }
          assert (Heothr : sc_thr m meo).
          { intros c Hc N2' N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
            exact (HP7thr c Hc N2' N8 N9 N18). }
          (* ============ +0x54 sd s1,336(s2) -- p->cwd = ip ============ *)
          iApply (wp_sd_s_sconf (CID := CID35) (mword_of_int (SC + 0x54)) Rs1 Rs2
                    (mword_of_int 336 : mword 12) meo (K - 20)%nat (pv_cwd V) b
                    with "Hcg Hpc Hi54 [Hcwd]").
          { iEval (rgne; rewrite Heos2 p_cwd_sext). iExact "Hcwd". }
          iIntros (CID36 Hq36) "Hcg Hpc Hcwd".
          iEval (rgne; rgne; rewrite Heos2 Heos1 p_cwd_sext) in "Hcwd".
          assert (Hpp58 : add_vec_int (mword_of_int (SC + 0x54) : mword 64) 4
                          = mword_of_int (SC + 0x58)) by pcw.
          iEval (rewrite Hpp58) in "Hpc".
          (* THE BLOCK, REBUILT at the new working directory *)
          iAssert (inode_held (ientry kk)) with "[Hrefnew]" as "Hheldnew".
          { rewrite /inode_held. iExists kk, (qq/2 + qq/2)%Qp, inum.
            iSplitR; [done |]. iSplitR; [iPureIntro; exact Hkk |].
            iSplitR; [iPureIntro; exact Hinumc |].
            iEval (rewrite -Hcdev). iExact "Hrefnew". }
          iDestruct ("Hpback" $! (ientry kk) with "Hcwd Hpidq") as "Hpnc".
          iDestruct (cwd_ref_of_held with "Hheldnew") as "Hrefcwd".
          iAssert (proc_priv gf pj pid (upd_cwd (upd_upt V P') (ientry kk)))
            with "[Hpnc Hrefcwd]" as "Hpriv".
          { rewrite (proc_priv_split_cwd gf pj pid (upd_cwd (upd_upt V P') (ientry kk))).
            iSplitL "Hpnc"; [iExact "Hpnc" |].
            iEval (cbn [upd_cwd pv_cwd]). iExact "Hrefcwd". }
          iDestruct (iref_slots_combine 1 1 with "Hislot Hir") as "Hir".
          (* ============ +0x58 c.li a0,0 ============ *)
          iApply (wp_cli_s_sconf (CID := CID36) (mword_of_int (SC + 0x58)) Ra0
                    (mword_of_int 0 : mword 6) (zero_reg : mword 64)
                    meo (K - 20)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc Hi58").
          iIntros (CID37 Hq37) "Hcg Hpc".
          set (P8 := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> meo).
          assert (HP8a0 : (P8 !!! Regidx Ra0 : mword 64) = (zero_reg : mword 64))
            by (rewrite /P8; apply upd_eq).
          assert (HP8sp : sc_sp sp0 P8)
            by (rewrite /sc_sp /P8 upd_ne; [exact Heosp | nz]).
          assert (HP8s1 : (P8 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /P8 upd_ne; [exact Heos1 | nz]).
          assert (HP8thr : sc_thr m P8).
          { intros c Hc N2' N8 N9 N18. rewrite /P8 upd_ne; [| regne].
            exact (Heothr c Hc N2' N8 N9 N18). }
          assert (Hpp5a : add_vec_int (mword_of_int (SC + 0x58) : mword 64) 2
                          = mword_of_int (SC + 0x5a)) by pcw.
          iEval (rewrite Hpp5a) in "Hpc".
          (* ============ +0x5a c.ldsp s1,136(sp) ============ *)
          assert (Hg3 : add_vec (P8 !!! Regidx csp_rs1 : mword 64)
                          (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
                        = pa_stk sp0 3) by (rewrite HP8sp; apply sc_frm3).
          iApply (wp_cldsp_s_sconf (CID := CID37) (mword_of_int (SC + 0x5a))
                    (mword_of_int 17 : mword 6) Rs1 P8 (K - 20)%nat
                    (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc Hi5a [Hf3]").
          { iEval (rewrite Hg3). iExact "Hf3". }
          iIntros (CID38 Hq38) "Hcg Hpc Hf3".
          iEval (rewrite Hg3) in "Hf3".
          set (P9 := <[Regidx Rs1 := regval_into_reg
                        (m !!! Regidx Rs1 : mword 64)]> P8).
          assert (HP9s1 : (P9 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
            by (rewrite /P9; apply upd_eq).
          assert (HP9a0 : (P9 !!! Regidx Ra0 : mword 64) = (zero_reg : mword 64))
            by (rewrite /P9 upd_ne; [exact HP8a0 | nz]).
          assert (HP9sp : sc_sp sp0 P9)
            by (rewrite /sc_sp /P9 upd_ne; [exact HP8sp | nz]).
          assert (HP9thr : sc_thr m P9).
          { intros c Hc N2' N8 N9 N18. rewrite /P9 upd_ne; [| regne].
            exact (HP8thr c Hc N2' N8 N9 N18). }
          assert (Hpp5c : add_vec_int (mword_of_int (SC + 0x5a) : mword 64) 2
                          = mword_of_int (SC + 0x5c)) by pcw.
          iEval (rewrite Hpp5c) in "Hpc".
          (* the buffer, whole again *)
          iDestruct (sc_buf_join (pa_stk sp0 20) bf pk Hpk with "Hbufk Hbufrest")
            as "Hbytes2".
          iDestruct (sc_bytes_name (pa_stk sp0 20) 128 with "Hbytes2") as (bf1) "Hbuf".
          iApply (sc_epilogue (CID0 := CID38) m P9 sp0 K b pj
                    (m !!! Regidx Rs1 : mword 64) bf1
                    ltac:(lia) Kpop ltac:(reflexivity) HP9sp HP9thr HP9s1 Hal
                    with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hbuf
                          [Hown Hbsl Hsbb Hsbi Hbmres Hir Hpriv Hcont]").
          iEval (rewrite /wp_next).
          iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
          iDestruct (cpu_own_transport CID35 CIDz 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
          iApply ("Hcont" $! mf used2 P' with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                    Hsbb Hsbi [%] Hbmres Hir [Hpriv]").
          { exact Hcsf. }
          { exact Hupt. }
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { etransitivity; [exact Hused2 | exact Hused1]. }
          { rewrite /sys_chdir_post. iRight. iExists (ientry kk).
            iSplitR; [iPureIntro; rewrite Ha0f; exact HP9a0 |]. iExact "Hpriv". }
        * (* ======== ARM C: NOT a directory ======== *)
          iApply (wp_bne_taken_s_sconf (CID := CID26) (mword_of_int (SC + 0x3e))
                    (mword_of_int 50 : mword 13) Ra5 Ra4 P2 (K - 20)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HP2a4 HP2a5; exact (sc_tdir_ne _ Hty))
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi3e").
          iApply bi.later_intro. iIntros (CID27 Hq27) "Hcg Hpc".
          assert (Htg70 : add_vec (mword_of_int (SC + 0x3e) : mword 64)
                            (sign_extend' 64 (mword_of_int 50 : mword 13))
                          = mword_of_int (SC + 0x70)) by pcw.
          iEval (rewrite Htg70) in "Hpc".
          (* ============ +0x70 c.mv a0,s1 ============ *)
          iApply (wp_cmv_s_sconf (CID := CID27) (mword_of_int (SC + 0x70)) Ra0 Rs1
                    P2 (K - 20)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi70").
          iIntros (CID28 Hq28) "Hcg Hpc".
          set (Q0 := <[Regidx Ra0 := regval_into_reg
                        (add_vec zero_reg (P2 !!! Regidx Rs1))]> P2).
          assert (HQ0a0 : (Q0 !!! Regidx Ra0 : mword 64) = ientry kk).
          { etransitivity; [ rewrite /Q0; apply upd_eq |].
            rewrite add_vec_zero_l. exact HP2s1. }
          assert (HQ0sp : sc_sp sp0 Q0)
            by (rewrite /sc_sp /Q0 upd_ne; [exact HP2sp | nz]).
          assert (HQ0s1 : (Q0 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /Q0 upd_ne; [exact HP2s1 | nz]).
          assert (HQ0thr : sc_thr m Q0).
          { intros c Hc N2' N8 N9 N18. rewrite /Q0 upd_ne; [| regne].
            exact (HP2thr c Hc N2' N8 N9 N18). }
          assert (Hpp72 : add_vec_int (mword_of_int (SC + 0x70) : mword 64) 2
                          = mword_of_int (SC + 0x72)) by pcw.
          iEval (rewrite Hpp72) in "Hpc".
          (* ============ +0x72 jal ra,iunlockput ============ *)
          iApply (wp_jal_s_sconf (CID := CID28) (mword_of_int (SC + 0x72)) Rra
                    (mword_of_int 2089182 : mword 21) Q0 (K - 20)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi72").
          iIntros (CID29 Hq29) "Hcg Hpc".
          set (Q1 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (SC + 0x72) : mword 64) 4)]> Q0).
          assert (Hjiup : add_vec (mword_of_int (SC + 0x72) : mword 64)
                            (sign_extend' 64 (mword_of_int 2089182 : mword 21))
                          = mword_of_int KernelSyms.iunlockput) by pcw.
          iEval (rewrite Hjiup) in "Hpc".
          assert (HQ1ra : (Q1 !!! Regidx Rra : mword 64)
                          = add_vec_int (mword_of_int (SC + 0x72) : mword 64) 4)
            by (rewrite /Q1; apply upd_eq).
          assert (HQ1a0 : (Q1 !!! Regidx Ra0 : mword 64) = ientry kk)
            by (rewrite /Q1 upd_ne; [exact HQ0a0 | nz]).
          assert (HQ1sp : sc_sp sp0 Q1)
            by (rewrite /sc_sp /Q1 upd_ne; [exact HQ0sp | nz]).
          assert (HQ1s1 : (Q1 !!! Regidx Rs1 : mword 64) = ientry kk)
            by (rewrite /Q1 upd_ne; [exact HQ0s1 | nz]).
          assert (HQ1thr : sc_thr m Q1).
          { intros c Hc N2' N8 N9 N18. rewrite /Q1 upd_ne; [| regne].
            exact (HQ0thr c Hc N2' N8 N9 N18). }
          iAssert (ic_loaded gfs gi cov logstart kk inum dn bm)
            with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind Hblocks Hdlnk]"
            as "Hload".
          { rewrite /ic_loaded. iExists dat.
            iSplitR; [iPureIntro; exact Hiok |].
            iSplitR; [iPureIntro; exact Hdok |].
            iSplitR; [iPureIntro; exact Hddix |].
            iSplitR; [iPureIntro; exact Hdoc |].
            iSplitR; [iPureIntro; exact Hduq |].
            iSplitL "Hdlnk"; [iExact "Hdlnk" |].
            iFrame "Hdiat".
            iSplitL "Hity Himaj Himin Hinl Hisz".
            - rewrite /inode_meta /i_type. iFrame.
            - iFrame. }
          iDestruct (sc_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (cpu_own_transport CID24 CID29 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (Iunlockput.wp_iunlockput_sconf (CID := CID29) gs j gl gu gd gk
                    pd pav pu bn g gfs gi cn gtl gil gisl cov logstart bmapstart
                    inodestart nib size dev used1 kk (qq/2)%Qp (qq/2)%Qp gsh inum
                    dn bm n1 pid (DfracOwn (1/4)) dqb dqs
                    Q1 (K - 20)%nat eb b lks
                    ltac:(lia) Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                    Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl HQ1a0 (Hlb "log"%string)
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpanic Hpe Hbio Hlog Hitab Hitinv
                          Hesck Hireg Hslkk Hslkd Hslpid Hdep Hidev Hiinum
                          Hivalid Hload Hshot Hkeep Hsbb Hsbi Hbmres Hpidq
                          Hprocs Hdev Hgeo Hdlk Hbsl [HopS]").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { rewrite /log_op. iExists Sb1. iExact "HopS". }
          iIntros (CID30 Hq30 mup n2 used2)
            "%Hcsup Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
             Hop Hislot".
          assert (Hpc76 : ret_pc (Q1 !!! Regidx Rra : mword 64)
                          = mword_of_int (SC + 0x76)) by (rewrite HQ1ra; pcw).
          iEval (rewrite Hpc76) in "Hpc".
          assert (Hupsp : sc_sp sp0 mup).
          { rewrite /sc_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
            exact HQ1sp. }
          assert (Hupthr : sc_thr m mup).
          { intros c Hc N2' N8 N9 N18. rewrite (callee_saved_lookup Hcsup c Hc).
            exact (HQ1thr c Hc N2' N8 N9 N18). }
          (* ============ +0x76 jal ra,end_op ============ *)
          iApply (wp_jal_s_sconf (CID := CID30) (mword_of_int (SC + 0x76)) Rra
                    (mword_of_int 2091388 : mword 21) mup (K - 20)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi76").
          iIntros (CID31 Hq31) "Hcg Hpc".
          set (Q2 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (SC + 0x76) : mword 64) 4)]> mup).
          assert (Hjeo2 : add_vec (mword_of_int (SC + 0x76) : mword 64)
                            (sign_extend' 64 (mword_of_int 2091388 : mword 21))
                          = mword_of_int KernelSyms.end_op) by pcw.
          iEval (rewrite Hjeo2) in "Hpc".
          assert (HQ2ra : (Q2 !!! Regidx Rra : mword 64)
                          = add_vec_int (mword_of_int (SC + 0x76) : mword 64) 4)
            by (rewrite /Q2; apply upd_eq).
          assert (HQ2sp : sc_sp sp0 Q2)
            by (rewrite /sc_sp /Q2 upd_ne; [exact Hupsp | nz]).
          assert (HQ2thr : sc_thr m Q2).
          { intros c Hc N2' N8 N9 N18. rewrite /Q2 upd_ne; [| regne].
            exact (Hupthr c Hc N2' N8 N9 N18). }
          iDestruct (cpu_own_transport CID30 CID31 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (EndOp.wp_end_op_sconf (CID := CID31) gs j gl gu gd gk pd pav pu
                    bn g gfs cov logstart dev n2 pid (DfracOwn (1/4))
                    Q2 (K - 20)%nat eb b lks
                    ltac:(lia) Hgeom Hj Hgl (Hlb "log"%string)
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpanic Hpe Hbio Hlog Hseam Hgen
                          Hpidq Hprocs Hdev Hgeo Hdlk Hop").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          iIntros (CID32 Hq32 meo) "%Hcseo Hcg Hown _ _ Hpc Hpidq".
          assert (Hpc7a : ret_pc (Q2 !!! Regidx Rra : mword 64)
                          = mword_of_int (SC + 0x7a)) by (rewrite HQ2ra; pcw).
          iEval (rewrite Hpc7a) in "Hpc".
          assert (Heosp : sc_sp sp0 meo).
          { rewrite /sc_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
            exact HQ2sp. }
          assert (Heothr : sc_thr m meo).
          { intros c Hc N2' N8 N9 N18. rewrite (callee_saved_lookup Hcseo c Hc).
            exact (HQ2thr c Hc N2' N8 N9 N18). }
          (* ============ +0x7a c.li a0,-1 ============ *)
          iApply (wp_cli_s_sconf (CID := CID32) (mword_of_int (SC + 0x7a)) Ra0
                    (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                    meo (K - 20)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc Hi7a").
          iIntros (CID33 Hq33) "Hcg Hpc".
          set (Q3 := <[Regidx Ra0 := regval_into_reg
                        (mword_of_int (-1) : mword 64)]> meo).
          assert (HQ3a0 : (Q3 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
            by (rewrite /Q3; apply upd_eq).
          assert (HQ3sp : sc_sp sp0 Q3)
            by (rewrite /sc_sp /Q3 upd_ne; [exact Heosp | nz]).
          assert (HQ3thr : sc_thr m Q3).
          { intros c Hc N2' N8 N9 N18. rewrite /Q3 upd_ne; [| regne].
            exact (Heothr c Hc N2' N8 N9 N18). }
          assert (Hpp7c : add_vec_int (mword_of_int (SC + 0x7a) : mword 64) 2
                          = mword_of_int (SC + 0x7c)) by pcw.
          iEval (rewrite Hpp7c) in "Hpc".
          (* ============ +0x7c c.ldsp s1,136(sp) ============ *)
          assert (Hh3 : add_vec (Q3 !!! Regidx csp_rs1 : mword 64)
                          (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
                        = pa_stk sp0 3) by (rewrite HQ3sp; apply sc_frm3).
          iApply (wp_cldsp_s_sconf (CID := CID33) (mword_of_int (SC + 0x7c))
                    (mword_of_int 17 : mword 6) Rs1 Q3 (K - 20)%nat
                    (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc Hi7c [Hf3]").
          { iEval (rewrite Hh3). iExact "Hf3". }
          iIntros (CID34 Hq34) "Hcg Hpc Hf3".
          iEval (rewrite Hh3) in "Hf3".
          set (Q4 := <[Regidx Rs1 := regval_into_reg
                        (m !!! Regidx Rs1 : mword 64)]> Q3).
          assert (HQ4s1 : (Q4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
            by (rewrite /Q4; apply upd_eq).
          assert (HQ4a0 : (Q4 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
            by (rewrite /Q4 upd_ne; [exact HQ3a0 | nz]).
          assert (HQ4sp : sc_sp sp0 Q4)
            by (rewrite /sc_sp /Q4 upd_ne; [exact HQ3sp | nz]).
          assert (HQ4thr : sc_thr m Q4).
          { intros c Hc N2' N8 N9 N18. rewrite /Q4 upd_ne; [| regne].
            exact (HQ3thr c Hc N2' N8 N9 N18). }
          assert (Hpp7e : add_vec_int (mword_of_int (SC + 0x7c) : mword 64) 2
                          = mword_of_int (SC + 0x7e)) by pcw.
          iEval (rewrite Hpp7e) in "Hpc".
          (* ============ +0x7e c.j +0x5c ============ *)
          iApply (wp_cj_s_sconf (CID := CID34) (mword_of_int (SC + 0x7e))
                    (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")))
                    Q4 (K - 20)%nat b ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi7e").
          iIntros (CID35 Hq35). iNext. iIntros "Hcg Hpc".
          assert (Htg5c : add_vec (mword_of_int (SC + 0x7e) : mword 64)
                            (sign_extend' 64
                               (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
                          = mword_of_int (SC + 0x5c)) by pcw.
          iEval (rewrite Htg5c) in "Hpc".
          (* the block goes back UNCHANGED: [p->cwd] never moved *)
          iDestruct ("Hpback" $! (pv_cwd V) with "Hcwd Hpidq") as "Hpnc".
          iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
          iAssert (proc_priv gf pj pid (upd_upt V P')) with "[Hpnc Href]" as "Hpriv".
          { rewrite (proc_priv_split_cwd gf pj pid (upd_upt V P')).
            iSplitL "Hpnc".
            - iEval (rewrite -(sc_upd_cwd_id (upd_upt V P'))). iExact "Hpnc".
            - iEval (cbn [upd_upt pv_cwd]). iExact "Href". }
          iDestruct (iref_slots_combine 1 1 with "Hislot Hir") as "Hir".
          (* the buffer, whole again *)
          iDestruct (sc_buf_join (pa_stk sp0 20) bf pk Hpk with "Hbufk Hbufrest")
            as "Hbytes2".
          iDestruct (sc_bytes_name (pa_stk sp0 20) 128 with "Hbytes2") as (bf1) "Hbuf".
          iDestruct (cpu_own_transport CID32 CID35 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (sc_epilogue (CID0 := CID35) m Q4 sp0 K b pj
                    (m !!! Regidx Rs1 : mword 64) bf1
                    ltac:(lia) Kpop ltac:(reflexivity) HQ4sp HQ4thr HQ4s1 Hal
                    with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hbuf
                          [Hown Hbsl Hsbb Hsbi Hbmres Hir Hpriv Hcont]").
          iEval (rewrite /wp_next).
          iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
          iDestruct (cpu_own_transport CID35 CIDz 0 eb pj b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
          iApply ("Hcont" $! mf used2 P' with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                    Hsbb Hsbi [%] Hbmres Hir [Hpriv]").
          { exact Hcsf. }
          { exact Hupt. }
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { etransitivity; [exact Hused2 | exact Hused1]. }
          { rewrite /sys_chdir_post. iLeft. iFrame "Hpriv". iPureIntro.
            rewrite Ha0f. exact HQ4a0. }
      + (* ================= ARM B: namei returned 0 =================
           +0x66 restores s1 and falls into the shared "-1" tail. *)
        iDestruct "Hres" as "(%Hnaz & Hir)".
        iApply (wp_cbeqz_taken_s_sconf (CID := CID21) (mword_of_int (SC + 0x32))
                  (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  N2 (K - 20)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HN2a0 Hnaz; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi32").
        iApply bi.later_intro. iIntros (CID22 Hq22) "Hcg Hpc".
        assert (Htg66 : add_vec (mword_of_int (SC + 0x32) : mword 64)
                          (sign_extend' 64
                             (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0"))))
                        = mword_of_int (SC + 0x66)) by pcw.
        iEval (rewrite Htg66) in "Hpc".
        (* ============ +0x66 c.ldsp s1,136(sp) ============ *)
        assert (He3 : add_vec (N2 !!! Regidx csp_rs1 : mword 64)
                        (zero_extend' 64 (concat_vec (mword_of_int 17 : mword 6) ('b"000")))
                      = pa_stk sp0 3) by (rewrite HN2sp; apply sc_frm3).
        iApply (wp_cldsp_s_sconf (CID := CID22) (mword_of_int (SC + 0x66))
                  (mword_of_int 17 : mword 6) Rs1 N2 (K - 20)%nat
                  (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi66 [Hf3]").
        { iEval (rewrite He3). iExact "Hf3". }
        iIntros (CID23 Hq23) "Hcg Hpc Hf3".
        iEval (rewrite He3) in "Hf3".
        set (N3 := <[Regidx Rs1 := regval_into_reg
                      (m !!! Regidx Rs1 : mword 64)]> N2).
        assert (HN3s1 : (N3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
          by (rewrite /N3; apply upd_eq).
        assert (HN3sp : sc_sp sp0 N3)
          by (rewrite /sc_sp /N3 upd_ne; [exact HN2sp | nz]).
        assert (HN3thr : sc_thr m N3).
        { intros c Hc N2' N8 N9 N18. rewrite /N3 upd_ne; [| regne].
          exact (HN2thr c Hc N2' N8 N9 N18). }
        assert (Hpp68 : add_vec_int (mword_of_int (SC + 0x66) : mword 64) 2
                        = mword_of_int (SC + 0x68)) by pcw.
        iEval (rewrite Hpp68) in "Hpc".
        (* the buffer, whole again, for the tail and the epilogue *)
        iDestruct (sc_buf_join (pa_stk sp0 20) bf pk Hpk with "Hbufk Hbufrest")
          as "Hbytes2".
        iDestruct (sc_bytes_name (pa_stk sp0 20) 128 with "Hbytes2") as (bf1) "Hbuf".
        iDestruct (cpu_own_transport CID20 CID23 0 eb pj b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (sc_m1_tail (CID0 := CID23) gs j gl gu gd gk pd pav pu bn g gfs
                  cov logstart dev n1 pid (DfracOwn (1/4))
                  m N3 sp0 K eb b lks (m !!! Regidx Rs1 : mword 64) bf1
                  ltac:(lia) ltac:(lia) Kpop Hgeom Hj Hgl Hlkempty
                  ltac:(reflexivity) HN3sp HN3thr HN3s1 Hal
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpanic Hpe Hbio Hlog Hseam Hgen
                        Hpidq Hprocs Hdev Hgeo Hdlk [HopS] Hf1 Hf2 Hf3 Hf4 Hbuf
                        [Hpback Hcwd Hcwdref Hbsl Hsbb Hsbi Hbmres Hir Hcont]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { rewrite /log_op. iExists Sb1. iExact "HopS". }
        iEval (rewrite /wp_next).
        iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hown _ _ Hpc Hpidq".
        iDestruct ("Hpback" $! (pv_cwd V) with "Hcwd Hpidq") as "Hpnc".
        iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
        iAssert (proc_priv gf pj pid (upd_upt V P')) with "[Hpnc Href]" as "Hpriv".
        { rewrite (proc_priv_split_cwd gf pj pid (upd_upt V P')).
          iSplitL "Hpnc".
          - iEval (rewrite -(sc_upd_cwd_id (upd_upt V P'))). iExact "Hpnc".
          - iEval (cbn [upd_upt pv_cwd]). iExact "Href". }
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf used1 P' with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                  Hsbb Hsbi [%] Hbmres Hir [Hpriv]").
        { exact Hcsf. }
        { exact Hupt. }
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { exact Hused1. }
        { rewrite /sys_chdir_post. iLeft. iFrame "Hpriv". iPureIntro. exact Ha0f. }
    - (* ================= ARM A: argstr returned -1 =================
         The [bltz] is TAKEN, straight to the shared "-1" tail at +0x68.
         s1 was never written on this path, so slot 3 rides through as the
         caller's junk and the register as the caller's value -- which is
         exactly the premise [sc_m1_tail] takes. *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID15) (mword_of_int (SC + 0x22))
                (mword_of_int 70 : mword 13) Ra0 mas (K - 20)%nat b
                ltac:(nz) ltac:(rgne; rewrite Hpr; exact sc_m1_neg)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi22").
      iApply bi.later_intro. iIntros (CID16 Hq16) "Hcg Hpc".
      assert (Htg68 : add_vec (mword_of_int (SC + 0x22) : mword 64)
                        (sign_extend' 64 (mword_of_int 70 : mword 13))
                      = mword_of_int (SC + 0x68)) by pcw.
      iEval (rewrite Htg68) in "Hpc".
      iDestruct (proc_priv_pid gf pj pid (upd_upt V P') with "Hpriv")
        as "[Hpidq Hpback]".
      iDestruct (cpu_own_transport CID15 CID16 0 eb pj b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (sc_m1_tail (CID0 := CID16) gs j gl gu gd gk pd pav pu bn g gfs
                cov logstart dev MAXOPBLOCKS pid (DfracOwn (1/4))
                m mas sp0 K eb b lks u3 bf
                ltac:(lia) ltac:(lia) Kpop Hgeom Hj Hgl Hlkempty
                ltac:(reflexivity) Hassp Hasthr Hass1 Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpanic Hpe Hbio Hlog Hseam Hgen
                      Hpidq Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hbuf
                      [Hpback Hbsl Hsbb Hsbi Hbmres Hir Hcont]").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iEval (rewrite /wp_next).
      iIntros (CIDz) "%Hqz". iIntros (mf) "%Hcsf %Ha0f Hcg Hown _ _ Hpc Hpidq".
      iDestruct ("Hpback" with "Hpidq") as "Hpriv".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf used P' with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                Hsbb Hsbi [%] Hbmres Hir [Hpriv]").
      { exact Hcsf. }
      { exact Hupt. }
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { reflexivity. }
      { rewrite /sys_chdir_post. iLeft. iFrame "Hpriv". iPureIntro. exact Ha0f. }
  Qed.

End ProofSysChdirBody.

End SysChdirProof.
