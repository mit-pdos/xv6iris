(* ProofSysLink.v -- THE sys_link WALK, +0x00 .. +0xba, and the seal.

     uint64 sys_link(void) {
       char name[DIRSIZ], new[MAXPATH], old[MAXPATH];
       struct inode *dp, *ip;
       if (argstr(0, old, MAXPATH) < 0 || argstr(1, new, MAXPATH) < 0)
         return -1;                                            ARM A
       begin_op();
       if ((ip = namei(old)) == 0) { end_op(); return -1; }     ARM B
       ilock(ip);
       if (ip->type == T_DIR)      { iunlockput(ip); ... }      ARM C
       if (ip->nlink >= NLINK_MAX) { iunlockput(ip); ... }      ARM D
       ip->nlink++; iupdate(ip); iunlock(ip);                   THE MINT
       if ((dp = nameiparent(new, name)) == 0) goto bad;        ARM E
       ilock(dp);
       if (dp->nlink == 0) { iunlockput(dp); goto bad; }        ARM E2
       if (dp->dev != ip->dev || dirlink(dp,name,ip->inum) < 0) ARM F
         { iunlockput(dp); goto bad; }
       iunlockput(dp); iput(ip); end_op(); return 0;            ARM G
      bad: ...                                                  the tail
     }

   The contract is [SpecSysLink.v] and its header carries the frame map and
   the two ledgers; the op-wide log ledger is [SysLinkBudget.v]; the pure
   side conditions, the frame carve and the epilogue are
   [ProofSysLinkParts.v]; ARMs B, C, D, E2 and the whole [bad:] tail are
   [ProofSysLinkTails.v], instantiated here beside this file's own callee
   arguments.  What is left for this file is the walk, the join of every arm
   and the seal.

   ==== THE ORPHAN GUARD AT +0x84 (xv6 f60ff58) ========================

   nameiparent returns the parent UNLOCKED, so a concurrent rmdir can zero
   [dp->nlink] before the [ilock(dp)] at +0x80; a [dirlink] into an orphan
   then appends a record the parent's own [itrunc] discards WITHOUT
   dropping [ip->nlink], stranding this walk's [ilink].  create has
   re-checked since 9da28f5 and namex since 03e5422a; sys_link did not, and
   that -- not the model -- is what refuted the STRONG isdirempty
   invariant (fs-fragments-campaign.md).  The guard is ARM E2 and its walk
   is nine lines plus [Tails.sl_tail_e2], because it LEAVES: create's own
   guard cost an [∧] of two [wp_next]-wrapped continuations only because
   its taken arm and the NLINK_MAX gate below it rejoin.

   ==== THE CROSS-DEVICE BRANCH AT +0x92 IS REFUTED ====================

   [dp->dev != ip->dev] cannot be taken: the itable is SINGLE-DEVICE
   (design/fs-icache.md §13.11), so both [i_dev] cells hold the ambient
   [dev] -- dp's out of [ilock]'s checkout, ip's out of the REFERENCE this
   walk still holds.  So sys_link has EIGHT arms and not nine, and the
   [bne] falls through by [eq_vec_refl].

   ==== ip->dev AND ip->inum ARE READ WITH NO LOCK HELD =================

   +0x90 and +0x96 read [ip]'s identity cells between the [iunlock] at
   +0x6c and the [bad:] arm's [ilock] at +0xf6.  That is sound and needs no
   accessor: [IcacheRef.inode_ref] IS the two cells at the holder's own
   fraction ("a reference holder reads ip->dev / ip->inum with no lock at
   all", IcacheRef.v §4), so the walk simply keeps the shed pair across the
   window and lends the halves for the two loads.

   ==== THE REGISTER BUNDLE ============================================

   [sl_regs m sp0 ipv dpv Mx] pins sp, s0, s1 and s2 and carries
   [ProofSysLinkParts.sl_thr] for the rest.  Its four movers (a caller-saved
   write, a callee's [callee_saved], the [mv s1,a0] at +0x3e and the
   [mv s2,a0] at +0x7c) replace what would otherwise be five [assert]s per
   instruction. *)
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
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import LockRank.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import DirLinks.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIunlock.
Require Import SpecIupdate.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecWritei.
Require Import SpecDirlookup.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecPrintk.
Require Import SpecNamei.
Require Import SpecNameiparent.
Require Import CodeSysLink.
Require Import SpecSysLink.
Require Import SysLinkBudget.
Require Import ProofSysLinkParts.
Require Import ProofSysLinkTails.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac scidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Local Ltac sl_rne1 Hf :=
  first [ apply is_cs_idx_true_neq; [exact Hf | vm_compute; reflexivity]
        | apply not_eq_sym; apply is_cs_idx_true_neq;
          [exact Hf | vm_compute; reflexivity] ].

Local Ltac sl_rne2 Hf Ht :=
  first [ apply is_cs_idx_true_neq; [exact Hf | exact Ht]
        | apply not_eq_sym; apply is_cs_idx_true_neq; [exact Hf | exact Ht] ].

Local Ltac sl_xne N :=
  let Hq := fresh "Hq" in
  intro Hq; apply N;
  first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ].

(* Keep [wp_next_chain] out of [cpu_own_transport]'s argument list.  At the
   deep call sites below, elaborating that inline tactic re-walks the entire
   accumulated context; a named equality has a fixed type and is cheap to
   pass to the Iris lemma. *)
Local Ltac sl_own_transport CIDa CIDb eb0 pj0 b0 :=
  let Htr := fresh "Htr" in
  assert (Htr : b0 = false \/ pj0 = zero_reg ->
                  (CIDb : CPU) = (CIDa : CPU)) by wp_next_chain;
  iDestruct (cpu_own_transport CIDa CIDb 0 eb0 pj0 b0 Htr
               with "Hown") as "Hown".

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

(* ===================================================================== *)
(*  1.  THE REGISTER BUNDLE                                               *)
(* ===================================================================== *)

Definition sl_regs (m : regfile) (sp0 ipv dpv : mword 64) (Mx : regfile)
  : Prop :=
  Mx !!! Regidx csp_rs1 = pa_stk sp0 38
  /\ Mx !!! Regidx Rs0 = sp0
  /\ Mx !!! Regidx Rs1 = ipv
  /\ Mx !!! Regidx Rs2 = dpv
  /\ sl_thr m Mx.

Lemma sl_regs_sp (m : regfile) (sp0 ipv dpv : mword 64) (Mx : regfile) :
  sl_regs m sp0 ipv dpv Mx -> sl_sp sp0 Mx.
Proof. intros (H & _). exact H. Qed.

Lemma sl_regs_s0 (m : regfile) (sp0 ipv dpv : mword 64) (Mx : regfile) :
  sl_regs m sp0 ipv dpv Mx -> (Mx !!! Regidx Rs0 : mword 64) = sp0.
Proof. intros (_ & H & _). exact H. Qed.

Lemma sl_regs_s1 (m : regfile) (sp0 ipv dpv : mword 64) (Mx : regfile) :
  sl_regs m sp0 ipv dpv Mx -> (Mx !!! Regidx Rs1 : mword 64) = ipv.
Proof. intros (_ & _ & H & _). exact H. Qed.

Lemma sl_regs_s2 (m : regfile) (sp0 ipv dpv : mword 64) (Mx : regfile) :
  sl_regs m sp0 ipv dpv Mx -> (Mx !!! Regidx Rs2 : mword 64) = dpv.
Proof. intros (_ & _ & _ & H & _). exact H. Qed.

Lemma sl_regs_thr (m : regfile) (sp0 ipv dpv : mword 64) (Mx : regfile) :
  sl_regs m sp0 ipv dpv Mx -> sl_thr m Mx.
Proof. intros (_ & _ & _ & _ & H). exact H. Qed.

(* a CALLER-saved write leaves every pinned register alone *)
Lemma sl_regs_caller (m : regfile) (sp0 ipv dpv : mword 64) (Mx : regfile)
    (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> sl_regs m sp0 ipv dpv Mx ->
  sl_regs m sp0 ipv dpv (<[Regidx r := v]> Mx).
Proof.
  intros Hr (H2 & H8 & H9 & H18 & Hthr). unfold sl_regs. split_and!.
  - rewrite upd_ne; [exact H2 | sl_rne1 Hr].
  - rewrite upd_ne; [exact H8 | sl_rne1 Hr].
  - rewrite upd_ne; [exact H9 | sl_rne1 Hr].
  - rewrite upd_ne; [exact H18 | sl_rne1 Hr].
  - intros c Hc N2 N8 N9 N18'.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18') | sl_rne2 Hr Hc].
Qed.

(* ...and so does a callee's [callee_saved] report *)
Lemma sl_regs_cs (m : regfile) (sp0 ipv dpv : mword 64) (Mx My : regfile) :
  callee_saved Mx My -> sl_regs m sp0 ipv dpv Mx -> sl_regs m sp0 ipv dpv My.
Proof.
  intros Hcs (H2 & H8 & H9 & H18 & Hthr). unfold sl_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    exact H2.
  - rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)).
    exact H8.
  - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)).
    exact H9.
  - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)).
    exact H18.
  - intros c Hc N2 N8 N9 N18'. rewrite (callee_saved_lookup Hcs c Hc).
    exact (Hthr c Hc N2 N8 N9 N18').
Qed.

(* the [c.mv s1,a0] at +0x3e *)
Lemma sl_regs_wr_s1 (m : regfile) (sp0 ipv ipv' dpv : mword 64)
    (Mx : regfile) (v : mword 64) :
  v = ipv' -> sl_regs m sp0 ipv dpv Mx ->
  sl_regs m sp0 ipv' dpv (<[Regidx Rs1 := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & Hthr). unfold sl_regs. split_and!.
  - rewrite upd_ne; [exact H2 | nz].
  - rewrite upd_ne; [exact H8 | nz].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H18 | nz].
  - intros c Hc N2 N8 N9 N18'.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18') | sl_xne N9].
Qed.

(* the [c.mv s2,a0] at +0x7c *)
Lemma sl_regs_wr_s2 (m : regfile) (sp0 ipv dpv dpv' : mword 64)
    (Mx : regfile) (v : mword 64) :
  v = dpv' -> sl_regs m sp0 ipv dpv Mx ->
  sl_regs m sp0 ipv dpv' (<[Regidx Rs2 := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & Hthr). unfold sl_regs. split_and!.
  - rewrite upd_ne; [exact H2 | nz].
  - rewrite upd_ne; [exact H8 | nz].
  - rewrite upd_ne; [exact H9 | nz].
  - rewrite upd_eq. exact Hv.
  - intros c Hc N2 N8 N9 N18'.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18') | sl_xne N18'].
Qed.

(* ===================================================================== *)
(*  2.  THE WALK'S OWN PURE FACTS                                         *)
(* ===================================================================== *)

(* [c.lui a4,0x8] then [c.addi a4,a4,-1] is NLINK_MAX = SHRT_MAX. *)
(* the cross-device [bne] at +0x92: both cells hold the AMBIENT dev, so the
   branch is refuted by reflexivity (fs-icache.md 13.11's single-device
   itable).  This is why sys_link has EIGHT arms and not nine. *)
Lemma sl_neq_refl (x : mword 64) : neq_vec x x = false.
Proof. unfold neq_vec. by rewrite (proj2 (eq_vec_true_iff x x) eq_refl). Qed.

Lemma sl_lui8 :
  luival (sign_extend' 20 (mword_of_int 8 : mword 6)) = (mword_of_int 32768 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sl_nmax_const :
  add_vec (mword_of_int 32768 : mword 64)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int 32767 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the [c.li a5,1] at +0x4a and the [c.li a5,0] at +0xb4 *)
Lemma sl_li_one : (mword_of_int (Z.of_nat 1) : mword 64) = (mword_of_int 1 : mword 64).
Proof. reflexivity. Qed.

(* the record the [++] at +0x5e / +0x60 commits *)
Definition sl_incnl (dn : dinode) : dinode :=
  sl_setnl dn (add_vec (di_nlink dn : mword 16) (mword_of_int 1)).

(* +0x96's [lw a2,4(s1)] SIGN-extends the 32-bit inum cell and
   [SpecDirlink] takes a ZERO-extended halfword; mkfs's [ushort] geometry
   is what closes the gap.  ProofCreate's cluster, restated (a
   whole-function proof file is not a dependency any other one may take). *)
Definition sl_low16 (v : mword 32) : mword 16 := mword_of_int (bv_unsigned v).

Lemma sl_moi16_unsigned (z : Z) :
  bv_unsigned (mword_of_int z : mword 16) = bv_wrap 16 z.
Proof.
  unfold mword_of_int, SailStdpp.Values.mword_of_int,
         MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 16) with 16%N. reflexivity.
Qed.

Lemma sl_low16_unsigned (v : mword 32) :
  bv_unsigned v < 2 ^ 16 -> bv_unsigned (sl_low16 v) = bv_unsigned v.
Proof.
  intro Hv. pose proof (bv_unsigned_in_range _ v) as Hlo.
  unfold sl_low16. rewrite sl_moi16_unsigned.
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 16)%Z with (2^16)%Z. lia.
Qed.

Lemma sl_zext64_16_unsigned (h : mword 16) :
  bv_unsigned (zero_extend' 64 h : mword 64) = bv_unsigned h.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       to_word get_word MachineWord.MachineWord.zero_extend].
  rewrite bv_zero_extend_unsigned; [ reflexivity | cbn; lia ].
Qed.

Lemma sl_sext64_32_unsigned (v : mword 32) :
  bv_unsigned v < 2 ^ 31 ->
  bv_unsigned (sign_extend' 64 v : mword 64) = bv_unsigned v.
Proof.
  intro Hv.
  pose proof (bv_unsigned_in_range _ v) as Hlo.
  assert (Hhm32 : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2^31)
    by reflexivity.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed.
  rewrite bv_swrap_small; [ apply bvw64_small; lia | rewrite Hhm32; lia ].
Qed.

Lemma sl_a2_halfword (v : mword 32) (h : mword 16) :
  bv_unsigned v = bv_unsigned h ->
  (sign_extend' 64 v : mword 64) = (zero_extend' 64 h : mword 64).
Proof.
  intro Hvh.
  pose proof (bv_unsigned_in_range _ h) as Hh. unfold bv_modulus in Hh.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z in Hh.
  apply bv_eq.
  rewrite sl_zext64_16_unsigned.
  rewrite (sl_sext64_32_unsigned v ltac:(rewrite Hvh; lia)).
  exact Hvh.
Qed.

Lemma sl_a2_low16 (v : mword 32) :
  bv_unsigned v < 2 ^ 16 ->
  (sign_extend' 64 v : mword 64) = (zero_extend' 64 (sl_low16 v) : mword 64).
Proof.
  intro Hv. apply sl_a2_halfword. rewrite (sl_low16_unsigned v Hv). reflexivity.
Qed.

(* the two record-shape identities the process block needs across the pair
   of [argstr]s and the two walks *)
Lemma sl_upd_upt_idem (V : pprivate) (P1 P2 : uptd) :
  upd_upt (upd_upt V P1) P2 = upd_upt V P2.
Proof. reflexivity. Qed.

Lemma sl_upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
Proof. destruct V; reflexivity. Qed.

Lemma sl_upd_cwd_upt (V : pprivate) (P : uptd) :
  upd_cwd (upd_upt V P) (pv_cwd V) = upd_upt V P.
Proof. destruct V; reflexivity. Qed.

(* THE LOG BUDGET's entry figure: begin_op mints ten and a walk needs at
   most four, whatever the path length ([SpecNamex.walk_need]). *)
Lemma sl_bud_walk (L : nat) : (walk_need L <= MAXOPBLOCKS)%nat.
Proof. unfold walk_need, iput_units, MAXOPBLOCKS. destruct L; lia. Qed.

(* ...and what is left after it, which is what the two guard arms' own
   [iunlockput] needs.  Both branch ABOVE the mint, so nothing but the
   namei walk has spent anything. *)
Lemma sl_bud_iput (n' : nat) (w ok : bool) :
  ((MAXOPBLOCKS - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof. unfold walk_spend, iput_units, MAXOPBLOCKS. destruct w, ok; lia. Qed.

(* ---- THE OP-WIDE LEDGER, THREADED --------------------------------------

   [SysLinkBudget]'s figures are the EXACT counts and what a walk holds are
   the contracts' LOWER bounds, so every arm's closure is one of that file's
   theorems composed with a monotonicity step.  All of them are closed here,
   as pure facts over plain [nat]s: a hot [lia] inside a syscall-altitude
   Iris context is what durable-notes warns about.

   [sl_crok] is the correlation clause as a walk-level hypothesis: a call
   that PAID for the bitmap block reports it in the set, so an entry set
   WITHOUT the block pins both walks' reports to [false] -- which is the one
   corner [SysLinkBudget.sl_corr] is about. *)
Definition sl_crok (crb w1 w2 : bool) : Prop :=
  crb = false -> w1 = false /\ w2 = false.

Lemma sl_cnt_u1 (w1 : bool) (n1 u1 : nat) :
  ((MAXOPBLOCKS - (walk_spend w1 + 0))%nat <= n1)%nat -> n1 = S u1 ->
  (sl_u2 w1 <= u1)%nat.
Proof.
  intros Hn Heq. subst n1.
  unfold sl_u2, sl_u1, sl_u0, sl_iu, walk_spend, MAXOPBLOCKS in *.
  destruct w1; lia.
Qed.

Lemma sl_cnt_u3 (w1 w2 : bool) (u1 n2 : nat) :
  (sl_u2 w1 <= u1)%nat -> ((u1 - (walk_spend w2 + 0))%nat <= n2)%nat ->
  (sl_u3 w1 w2 <= n2)%nat.
Proof.
  intros H1 H2.
  unfold sl_u3, sl_u2, sl_u1, sl_u0, sl_iu, walk_spend, MAXOPBLOCKS in *.
  destruct w1, w2; lia.
Qed.

Lemma sl_cnt_u3f (w1 w2 : bool) (u1 n2 : nat) :
  (sl_u2 w1 <= u1)%nat -> ((u1 - (walk_spend w2 + 1))%nat <= n2)%nat ->
  (sl_u3f w1 w2 <= n2)%nat.
Proof.
  intros H1 H2.
  unfold sl_u3f, sl_u2, sl_u1, sl_u0, sl_iu, walk_spend, MAXOPBLOCKS in *.
  destruct w1, w2; lia.
Qed.

(* the SECOND walk's need, met with room: the mint leaves at least eight. *)
Lemma sl_walk2_need (L : nat) (w1 : bool) (u1 : nat) :
  (sl_u2 w1 <= u1)%nat -> (walk_need L <= u1)%nat.
Proof.
  intro H.
  unfold sl_u2, sl_u1, sl_u0, sl_iu, walk_spend, MAXOPBLOCKS, walk_need,
         iput_units in *.
  destruct w1, L; lia.
Qed.

(* ARM E: [bad:] entered from nameiparent returning 0. *)
Lemma sl_bad_iput (w1 w2 : bool) (n2 : nat) :
  (sl_u3f w1 w2 <= n2)%nat -> (iput_units <= n2)%nat.
Proof.
  intro H. destruct (sl_bad1_closes w1 w2) as [Ha Hb].
  assert (Hz : sl_iu true = 0%nat) by reflexivity. rewrite Hz in Hb. lia.
Qed.

(* ARM E2: the ORPHAN GUARD's route to [bad:] (xv6 f60ff58).  The count is
   nameiparent's, untouched -- the guard fires before the dirlink -- so both
   figures come off [sl_orphan_closes] with no corner analysis. *)
Lemma sl_orphan_entry (w1 w2 : bool) (n2 : nat) :
  (sl_u3 w1 w2 <= n2)%nat -> (iput_units <= n2)%nat.
Proof.
  intro Hn2. destruct (sl_orphan_closes w1 w2 false) as (Ha & _ & _). lia.
Qed.

Lemma sl_orphan_close (w1 w2 w : bool) (n2 n' : nat) :
  (sl_u3 w1 w2 <= n2)%nat ->
  ((n2 - ip_spend_w w false false)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros Hn2 Hn'.
  assert (Hz : sl_iu true = 0%nat) by reflexivity.
  destruct (sl_orphan_closes w1 w2 w) as (Ha & Hb & Hcc). rewrite Hz in Hcc.
  lia.
Qed.

(* dirlink's ENTRY requirement. *)
Lemma sl_dl_need_ok (crb w1 w2 ind : bool) (n2 : nat) :
  sl_crok crb w1 w2 -> (sl_u3 w1 w2 <= n2)%nat -> (dl_need crb ind <= n2)%nat.
Proof.
  intros Hc Hn. destruct crb.
  - exact (Nat.le_trans _ _ _ (sl_dl_need_credited w1 w2 ind) Hn).
  - destruct (Hc eq_refl) as [Hw1 Hw2]. subst w1 w2.
    exact (Nat.le_trans _ _ _ (sl_dl_need_uncredited ind) Hn).
Qed.

(* dirlink's [di_size < 2^31] premise, off [inode_ok]'s size cap. *)
Lemma sl_size_lt (z : Z) :
  (z <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z -> (z < 2 ^ 31)%Z.
Proof.
  intro H. unfold MAXFILE, NDIRECT, NINDIRECT, BSIZE in H.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* writei's record: only the size and the addrs move. *)
Lemma sl_wi_size_max (dn : dinode) (bm' : blkmap) (off tot : nat) :
  (Z.of_nat (off + tot) < 2 ^ 32)%Z ->
  bv_unsigned (di_size (wi_dinode dn bm' off tot))
  = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (off + tot)).
Proof.
  intro Hlt. rewrite /wi_dinode. cbn [di_size].
  case_decide as Hd.
  - rewrite (moi32_small (Z.of_nat (off + tot))
               (conj (Nat2Z.is_nonneg (off + tot)) Hlt)). lia.
  - lia.
Qed.

(* ...and the window it writes fits a 32-bit size: the append slot is at
   most [dir_nrec (MAXFILE * BSIZE)]. *)
Lemma sl_off32 (dn : dinode) (data : nat -> list (bv 8)) (tot : nat) :
  (bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
  (tot <= 16)%nat ->
  (Z.of_nat (16 * dir_slot data (dir_nrec (bv_unsigned (di_size dn))) + tot)
   < 2 ^ 32)%Z.
Proof.
  intros Hsz Ht.
  pose proof (dir_slot_le data (dir_nrec (bv_unsigned (di_size dn)))) as Hk.
  pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hnn.
  destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hnn) as [Hr1 Hr2].
  unfold MAXFILE, NDIRECT, NINDIRECT, BSIZE in Hsz.
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

Lemma sl_wi_mono (crb crd cru al ind : bool) :
  (wi16_spend crb crd cru al ind <= wi16_spend crb crd false al ind)%nat.
Proof. destruct crb, crd, cru, al, ind; vm_compute; lia. Qed.

Lemma sl_sub_le (n k : nat) : (n - k <= n)%nat.
Proof. lia. Qed.

Lemma sl_atomic_lt16 (tot : nat) :
  (tot = 0%nat \/ tot = 16%nat) -> (tot < 16)%nat -> tot = 0%nat.
Proof. lia. Qed.

(* ARM G, the success append: the parent's free and then [iput(ip)]. *)
Lemma sl_ok_close (crb crd cru al ind w1 w2 wd : bool) (n2 n3 n4 : nat) :
  sl_crok crb w1 w2 -> (sl_u3 w1 w2 <= n2)%nat ->
  ((n2 - wi16_spend crb crd cru al ind)%nat <= n3)%nat ->
  ((n3 - ip_spend_w wd true false)%nat <= n4)%nat ->
  (iput_units <= n3)%nat /\ (iput_units <= n4)%nat.
Proof.
  intros Hc Hn2 Hn3 Hn4.
  pose proof (sl_wi_mono crb crd cru al ind) as Hmono.
  destruct crb.
  - destruct (sl_ok_closes_credited w1 w2 crd al ind wd) as [Ha Hb].
    split; lia.
  - destruct (Hc eq_refl) as [Hw1 Hw2]. subst w1 w2.
    destruct (sl_ok_closes_uncredited crd al ind wd) as [Ha Hb].
    split; lia.
Qed.

(* ARM F-0, the EMPTY append: entry, then the closure the [bad:] tail's own
   entry lemma takes as a premise. *)
Lemma sl_fail0_entry (crb crd cru al ind w1 w2 : bool) (n2 n3 : nat) :
  sl_crok crb w1 w2 -> (sl_u3 w1 w2 <= n2)%nat ->
  ((n2 - wi16_spend crb crd cru al ind)%nat <= n3)%nat ->
  (iput_units <= n3)%nat.
Proof.
  intros Hc Hn2 Hn3. pose proof (sl_wi_mono crb crd cru al ind) as Hmono.
  destruct crb.
  - destruct (sl_fail0_closes_credited w1 w2 crd al ind) as (Ha & Hb & Hcc). lia.
  - destruct (Hc eq_refl) as [Hw1 Hw2]. subst w1 w2.
    destruct (sl_fail0_closes_uncredited crd al ind false) as (Ha & Hb & Hcc).
    lia.
Qed.

Lemma sl_fail0_close (crb crb3 crd cru al ind w1 w2 w : bool) (n2 n3 n' : nat) :
  sl_crok crb w1 w2 -> (crb = true -> crb3 = true) ->
  (sl_u3 w1 w2 <= n2)%nat ->
  ((n2 - wi16_spend crb crd cru al ind)%nat <= n3)%nat ->
  (crb3 = true -> w = false) ->
  ((n3 - ip_spend_w w false false)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros Hc Himp Hn2 Hn3 Hw Hn'.
  pose proof (sl_wi_mono crb crd cru al ind) as Hmono.
  assert (Hz : sl_iu true = 0%nat) by reflexivity.
  destruct crb.
  - rewrite (Hw (Himp eq_refl)) in Hn'.
    destruct (sl_fail0_closes_credited w1 w2 crd al ind) as (Ha & Hb & Hcc).
    rewrite Hz in Hcc. lia.
  - destruct (Hc eq_refl) as [Hw1 Hw2]. subst w1 w2.
    destruct (sl_fail0_closes_uncredited crd al ind w) as (Ha & Hb & Hcc).
    rewrite Hz in Hcc. lia.
Qed.

(* ARM F-FOUND: the arm sys_link cannot refute, paid for by SpecDirlink's
   own found-arm clause. *)
Lemma sl_found_entry (w1 w2 : bool) (n2 n3 : nat) :
  (sl_u3 w1 w2 <= n2)%nat -> ((n2 - iput_units)%nat <= n3)%nat ->
  (iput_units <= n3)%nat.
Proof.
  intros Hn2 Hn3.
  destruct (sl_found_closes_at_iput_units_credited w1 w2) as (Ha & Hb & Hcc).
  lia.
Qed.

Lemma sl_found_close (crb3 w1 w2 w : bool) (n2 n3 n' : nat) :
  sl_crok crb3 w1 w2 -> (sl_u3 w1 w2 <= n2)%nat ->
  ((n2 - iput_units)%nat <= n3)%nat ->
  (crb3 = true -> w = false) ->
  ((n3 - ip_spend_w w false false)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros Hc Hn2 Hn3 Hw Hn'.
  assert (Hz : sl_iu true = 0%nat) by reflexivity.
  destruct crb3.
  - rewrite (Hw eq_refl) in Hn'.
    destruct (sl_found_closes_at_iput_units_credited w1 w2) as (Ha & Hb & Hcc).
    rewrite Hz in Hcc. lia.
  - destruct (Hc eq_refl) as [Hw1 Hw2]. subst w1 w2.
    destruct (sl_found_closes_at_iput_units_uncredited w) as (Ha & Hb & Hcc).
    rewrite Hz in Hcc. lia.
Qed.

Lemma sl_tf_upt (V : pprivate) (P : uptd) : pv_tf (upd_upt V P) = pv_tf V.
Proof. reflexivity. Qed.

Lemma sl_cwd_upt (V : pprivate) (P : uptd) : pv_cwd (upd_upt V P) = pv_cwd V.
Proof. reflexivity. Qed.

(* [di_type dn <> T_DIR] at the sixteen-bit width, read as the Z-level
   disequality [DirView] / [DirLinks] state their type tests at *)
Lemma sl_tdir_zne (t : mword 16) :
  t <> (mword_of_int 1 : mword 16) -> bv_unsigned t <> T_DIR_z.
Proof.
  intros Hne Hc. apply Hne. apply bv_eq. rewrite Hc.
  unfold T_DIR_z, T_DIR. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  THE WALK                                                          *)
(* ===================================================================== *)

Module SysLinkProof (Argstr : ARGSTR) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                    (Nameiparent : NAMEIPARENT) (Ilock : ILOCK)
                    (Iunlock : IUNLOCK) (Iupdate : IUPDATE)
                    (Dirlink : DIRLINK) (Iput : IPUT)
                    (Iunlockput : IUNLOCKPUT) (EndOp : END_OP) : SYSLINK.

Module Tails := SysLinkTails Ilock Iupdate Iunlockput EndOp.

Section ProofSysLinkBody.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  (* the two per-slot projections out of the boot families, at the copies
     THIS contract names ([ic_escrows] is IcacheEscrow's, [ic_sleeplocks]
     SpecDirlink's -- see fs-sysfile's sys_chdir trap 3). *)
  Lemma sl_esc_acc (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn gfs gi cov logstart -∗ ic_escrow cn gfs gi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma sl_slk_acc (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    (ic_sleeplocks cn -∗
     ∃ gil gisl : gname,
       is_sleeplock_gen gil gisl (i_lock (ientry k)) "inode"%string
                        (ic_tok cn k) (slh_tok (icfg_isl k))
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma sl_bs3 (bn : bio_names) :
    (bslots bn 3 : iProp Σ) ⊣⊢ bslot bn ∗ bslots bn 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* the reference allowance, split for the FIRST walk: namei takes two and
     hands one back, and the third is [ip]'s own -- held out here so that
     [nameiparent] can be handed a full two while [ip] is still live. *)
  Lemma sl_ir3 : (iref_slots 3 : iProp Σ) ⊣⊢ iref_slots 2 ∗ iref_slots 1.
  Proof. change 3%nat with (2 + 1)%nat. apply iref_slots_op. Qed.

  (* THE GENERATION-NAMED SHED.  [IcacheRef.inode_ref_shed] loses the
     generation, and nameiparent's [inode_held_ty] payout is exactly the
     claim that the share handed to ilock names the SAME generation as the
     type one-shot beside it -- which is what turns the parent's promised
     T_DIR into [di_type dnd = T_DIR] at the record ilock returns.  Pure
     resource algebra; its home is [IcacheRef.v] and it is here for that
     file's rebuild-cone reason. *)
  Lemma sl_carve_gen (k : nat) (q s : Qp) (dev inum : mword 32) (g : gname) :
    inode_ref_gen k (q + s)%Qp dev inum g ⊣⊢
    inode_ref_short_gen k (q + s)%Qp q dev inum g ∗ inode_shr_gen k s dev inum g.
  Proof.
    rewrite /inode_ref_gen /inode_ref_short_gen /inode_shr_gen
            live_gen_split inode_ident_split SleepLock.slh_tok_split.
    iSplit.
    - iIntros "($ & [$ Hl2] & [$ Hi2] & [$ Hs2])". iFrame.
    - iIntros "[($ & $ & $ & $) ($ & $ & $)]".
  Qed.

  Lemma sl_shed_gen (k : nat) (q : Qp) (dev inum : mword 32) (g : gname) :
    inode_ref_gen k q dev inum g ⊣⊢
    inode_ref_short_gen k (q/2 + q/2)%Qp (q/2)%Qp dev inum g ∗
    inode_shr_gen k (q/2)%Qp dev inum g.
  Proof.
    pose proof (sl_carve_gen k (q/2)%Qp (q/2)%Qp dev inum g) as Hc.
    by rewrite {1}(Qp.div_2 q) in Hc.
  Qed.

  Lemma wp_sys_link_sconf `{GEN : GenId} `{CID0 : CpuId}
      (γf : gname) (γa : gname) (γpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_sys_link_sconf_body γf γa γpr gs j gl gu gd gk pd pav pu bn g gfs gi
                           cn gtl cov logstart bmapstart inodestart nib
                           size dev dqb dqs dqbs v0 v1 pid V
                           m K eb b lks.
  Proof.
    cbv beta delta [wp_sys_link_sconf_body].
    intros pcE pj ret_tgt HK Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom Hsize
           Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hnib16 Hprkc Hj Hgl
           Heb Harg0 Harg1.
    destruct (sl_kb K HK) as (Kna & Knp & Kdl & Kar & Kbo & Keo & Kil & Kiu
                              & Kiupd & Kip & Kiup & K10 & K38 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hprk #Hbio #Hlog Hseam
             Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks
             #Hireg #Hropen Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hir Hpriv Hcont".
    iPoseProof (printk_env_panic with "Hprk") as "#Hpe".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Htg10c18 : add_vec (mword_of_int (SL + 0x18) : mword 64)
              (sign_extend' 64 (mword_of_int 258 : mword 13))
              = mword_of_int (SL + 0x11a)) by pcw.
    assert (Htg10c2c : add_vec (mword_of_int (SL + 0x2c) : mword 64)
              (sign_extend' 64 (mword_of_int 238 : mword 13))
              = mword_of_int (SL + 0x11a)) by pcw.
    iPoseProof (slki_00 with "Htext") as "Hi00".
    iPoseProof (slki_02 with "Htext") as "Hi02".
    iPoseProof (slki_04 with "Htext") as "Hi04".
    iPoseProof (slki_06 with "Htext") as "Hi06".
    iPoseProof (slki_08 with "Htext") as "Hi08".
    iPoseProof (slki_0c with "Htext") as "Hi0c".
    iPoseProof (slki_10 with "Htext") as "Hi10".
    iPoseProof (slki_12 with "Htext") as "Hi12".
    iPoseProof (slki_16 with "Htext") as "Hi16".
    iPoseProof (slki_18 with "Htext") as "Hi18".
    iPoseProof (slki_1c with "Htext") as "Hi1c".
    iPoseProof (slki_20 with "Htext") as "Hi20".
    iPoseProof (slki_24 with "Htext") as "Hi24".
    iPoseProof (slki_26 with "Htext") as "Hi26".
    iPoseProof (slki_2a with "Htext") as "Hi2a".
    iPoseProof (slki_2c with "Htext") as "Hi2c".
    (* ================= +0x00 c.addi16sp sp,-304 ================= *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 45 : mword 6) m K 38 b
              ltac:(exact K38) (sl_push sp0) with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 45 : mword 6))))]> m).
    assert (HM1sp : sl_sp sp0 M1).
    { unfold sl_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply sl_push ]. }
    assert (HM1thr : sl_thr m M1).
    { intros c Hc N2 N8 N9 N18. rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SL + 0x2))
      by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (sl_frame_carve sp0 with "Hframe")
      as "(%Hal & [%u1 Hf1] & [%u2 Hf2] & [%u3 Hf3] & [%u4 Hf4] & HbN & HbW & HbO)".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 37 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply sl_frm1).
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 36 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply sl_frm2).
    (* ================= +0x02 c.sdsp ra,296(sp) ================= *)
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (SL + 0x2))
              (mword_of_int 37 : mword 6) Rra M1 (K - 38)%nat u1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (SL + 0x2) : mword 64) 2
                    = mword_of_int (SL + 0x4)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ================= +0x04 c.sdsp s0,288(sp) ================= *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SL + 0x4))
              (mword_of_int 36 : mword 6) Rs0 M1 (K - 38)%nat u2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rgne; rewrite Hc2 HM1s0) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (SL + 0x4) : mword 64) 2
                    = mword_of_int (SL + 0x6)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ================= +0x06 c.addi4spn s0,sp,304 ================= *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SL + 0x6))
              (Cregidx (mword_of_int 0)) (mword_of_int 76 : mword 8) Rs0
              M1 (K - 38)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 76 : mword 8))))]> M1).
    assert (HM2regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) M2).
    { unfold sl_regs. split_and!.
      - rewrite /M2 upd_ne; [exact HM1sp | nz].
      - etransitivity; [ rewrite /M2; apply upd_eq |].
        rewrite HM1sp. apply sl_fp.
      - rewrite /M2 upd_ne; [exact HM1s1 | nz].
      - rewrite /M2 upd_ne; [exact HM1s2 | nz].
      - intros c Hc N2 N8 N9 N18. rewrite /M2 upd_ne; [| regne].
        exact (HM1thr c Hc N2 N8 N9 N18). }
    assert (Hpp08 : add_vec_int (mword_of_int (SL + 0x6) : mword 64) 2
                    = mword_of_int (SL + 0x8)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ================= +0x08 li a2,128 ================= *)
    iApply (wp_li4_s_sconf (CID := CID4) (mword_of_int (SL + 0x8)) Ra2
              (mword_of_int 128 : mword 12)
              (mword_of_int (Z.of_nat 128) : mword 64) M2 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M3 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 128) : mword 64)]> M2).
    assert (HM3a2 : (M3 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M3; apply upd_eq).
    assert (HM3regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) M3)
      by (rewrite /M3; apply sl_regs_caller; [exact Hcsa2 | exact HM2regs]).
    assert (Hpp0c : add_vec_int (mword_of_int (SL + 0x8) : mword 64) 4
                    = mword_of_int (SL + 0xc)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ================= +0x0c addi a1,s0,-304 ================= *)
    iApply (wp_addi4_s_sconf (CID := CID5) (mword_of_int (SL + 0xc)) Ra1 Rs0
              (mword_of_int 3792 : mword 12) M3 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (M4 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3792 : mword 12)))]> M3).
    assert (HM4a1 : (M4 !!! Regidx Ra1 : mword 64) = pa_stk sp0 38).
    { etransitivity; [ rewrite /M4; apply upd_eq |].
      rewrite (sl_regs_s0 _ _ _ _ _ HM3regs). apply sl_bufold. }
    assert (HM4a2 : (M4 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3a2 | nz]).
    assert (HM4regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) M4)
      by (rewrite /M4; apply sl_regs_caller; [exact Hcsa1 | exact HM3regs]).
    assert (Hpp10 : add_vec_int (mword_of_int (SL + 0xc) : mword 64) 4
                    = mword_of_int (SL + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ================= +0x10 c.li a0,0 ================= *)
    iApply (wp_cli_s_sconf (CID := CID6) (mword_of_int (SL + 0x10)) Ra0
              (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M4 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi10").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M5 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> M4).
    assert (HM5a0 : (M5 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M5; apply upd_eq).
    assert (HM5a1 : (M5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 38)
      by (rewrite /M5 upd_ne; [exact HM4a1 | nz]).
    assert (HM5a2 : (M5 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a2 | nz]).
    assert (HM5regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) M5)
      by (rewrite /M5; apply sl_regs_caller; [exact Hcsa0 | exact HM4regs]).
    assert (Hpp12 : add_vec_int (mword_of_int (SL + 0x10) : mword 64) 2
                    = mword_of_int (SL + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ================= +0x12 jal ra,argstr ================= *)
    iApply (wp_jal_s_sconf (CID := CID7) (mword_of_int (SL + 0x12)) Rra
              (mword_of_int 2087382 : mword 21) M5 (K - 38)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (M6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SL + 0x12) : mword 64) 4)]> M5).
    assert (Hjas : add_vec (mword_of_int (SL + 0x12) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087382 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iEval (rewrite Hjas) in "Hpc".
    assert (HM6ra : (M6 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SL + 0x12) : mword 64) 4)
      by (rewrite /M6; apply upd_eq).
    assert (HM6a0 : (M6 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a0 | nz]).
    assert (HM6a1 : (M6 !!! Regidx Ra1 : mword 64) = pa_stk sp0 38)
      by (rewrite /M6 upd_ne; [exact HM5a1 | nz]).
    assert (HM6a2 : (M6 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a2 | nz]).
    assert (HM6regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) M6)
      by (rewrite /M6; apply sl_regs_caller; [exact Hcsra | exact HM5regs]).
    iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO") as (bo0) "HbO".
    sl_own_transport CID0 CID8 eb pj b.
    iApply (Argstr.wp_argstr_sconf (CID := CID8) γa γf M6 (K - 38)%nat 0%nat eb
              pj 0%nat v0 pid V 128%nat bo0 b lks
              sl_arg0_lt HM6a0 Harg0 sl_noff0 ltac:(exact Kar) HM6a2
              sl_maxpath_lt (Hlb "kmem"%string)
              with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [HbO]").
    { iEval (rewrite HM6a1). iExact "HbO". }
    iIntros (CID9 Hq9 mas P1 bo1) "%Hcsas %Hupt1 Hcg Hown Hpc Hpriv HbO %Hfsr1".
    iEval (rewrite HM6a1) in "HbO".
    assert (Hpc16 : ret_pc (M6 !!! Regidx Rra : mword 64)
                    = mword_of_int (SL + 0x16)) by (rewrite HM6ra; pcw).
    iEval (rewrite Hpc16) in "Hpc".
    assert (Hasregs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) mas)
      by exact (sl_regs_cs m sp0 _ _ M6 mas Hcsas HM6regs).
    (* ================= +0x16 c.li a5,-1 ================= *)
    iApply (wp_cli_s_sconf (CID := CID9) (mword_of_int (SL + 0x16)) Ra5
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              mas (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi16").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (M7 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (-1) : mword 64)]> mas).
    assert (HM7a5 : (M7 !!! Regidx Ra5 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /M7; apply upd_eq).
    assert (HM7a0 : (M7 !!! Regidx Ra0 : mword 64) = (mas !!! Regidx Ra0 : mword 64))
      by (rewrite /M7 upd_ne; [reflexivity | nz]).
    assert (HM7regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) M7)
      by (rewrite /M7; apply sl_regs_caller; [exact Hcsa5 | exact Hasregs]).
    assert (Hpp18 : add_vec_int (mword_of_int (SL + 0x16) : mword 64) 2
                    = mword_of_int (SL + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    (* ================= +0x18 bltz a0 -> ARM A ================= *)
    destruct Hfsr1 as [(pk1 & Hpk1 & Hpcstr1 & Hpr1) | Hpr1].
    - (* ------------ the FIRST string fetched: fall through ------------ *)
      iApply (wp_blt_x0_fall_s_sconf (CID := CID10) (mword_of_int (SL + 0x18))
                (mword_of_int 258 : mword 13) Ra0 M7 (K - 38)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite HM7a0 Hpr1;
                      exact (sl_nonneg _ (sl_len_range pk1 Hpk1)))
                with "Hcg Hpc Hi18").
      iIntros (CID11 Hq11) "Hcg Hpc".
      assert (Hpp1c : add_vec_int (mword_of_int (SL + 0x18) : mword 64) 4
                      = mword_of_int (SL + 0x1c)) by pcw.
      iEval (rewrite Hpp1c) in "Hpc".
      (* ================= +0x1c li a2,128 ================= *)
      iApply (wp_li4_s_sconf (CID := CID11) (mword_of_int (SL + 0x1c)) Ra2
                (mword_of_int 128 : mword 12)
                (mword_of_int (Z.of_nat 128) : mword 64) M7 (K - 38)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi1c").
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (N0 := <[Regidx Ra2 := regval_into_reg
                    (mword_of_int (Z.of_nat 128) : mword 64)]> M7).
      assert (HN0a2 : (N0 !!! Regidx Ra2 : mword 64)
                      = (mword_of_int (Z.of_nat 128) : mword 64))
        by (rewrite /N0; apply upd_eq).
      assert (HN0regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) N0)
        by (rewrite /N0; apply sl_regs_caller; [exact Hcsa2 | exact HM7regs]).
      assert (Hpp20 : add_vec_int (mword_of_int (SL + 0x1c) : mword 64) 4
                      = mword_of_int (SL + 0x20)) by pcw.
      iEval (rewrite Hpp20) in "Hpc".
      (* ================= +0x20 addi a1,s0,-176 ================= *)
      iApply (wp_addi4_s_sconf (CID := CID12) (mword_of_int (SL + 0x20)) Ra1 Rs0
                (mword_of_int 3920 : mword 12) N0 (K - 38)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
      iIntros (CID13 Hq13) "Hcg Hpc".
      set (N1 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (N0 !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> N0).
      assert (HN1a1 : (N1 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22).
      { etransitivity; [ rewrite /N1; apply upd_eq |].
        rewrite (sl_regs_s0 _ _ _ _ _ HN0regs). apply sl_bufnew. }
      assert (HN1a2 : (N1 !!! Regidx Ra2 : mword 64)
                      = (mword_of_int (Z.of_nat 128) : mword 64))
        by (rewrite /N1 upd_ne; [exact HN0a2 | nz]).
      assert (HN1regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) N1)
        by (rewrite /N1; apply sl_regs_caller; [exact Hcsa1 | exact HN0regs]).
      assert (Hpp24 : add_vec_int (mword_of_int (SL + 0x20) : mword 64) 4
                      = mword_of_int (SL + 0x24)) by pcw.
      iEval (rewrite Hpp24) in "Hpc".
      (* ================= +0x24 c.li a0,1 ================= *)
      iApply (wp_cli_s_sconf (CID := CID13) (mword_of_int (SL + 0x24)) Ra0
                (mword_of_int 1 : mword 6)
                (mword_of_int (Z.of_nat 1) : mword 64) N1 (K - 38)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi24").
      iIntros (CID14 Hq14) "Hcg Hpc".
      set (N2 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (Z.of_nat 1) : mword 64)]> N1).
      assert (HN2a0 : (N2 !!! Regidx Ra0 : mword 64)
                      = (mword_of_int (Z.of_nat 1) : mword 64))
        by (rewrite /N2; apply upd_eq).
      assert (HN2a1 : (N2 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22)
        by (rewrite /N2 upd_ne; [exact HN1a1 | nz]).
      assert (HN2a2 : (N2 !!! Regidx Ra2 : mword 64)
                      = (mword_of_int (Z.of_nat 128) : mword 64))
        by (rewrite /N2 upd_ne; [exact HN1a2 | nz]).
      assert (HN2regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) N2)
        by (rewrite /N2; apply sl_regs_caller; [exact Hcsa0 | exact HN1regs]).
      assert (Hpp26 : add_vec_int (mword_of_int (SL + 0x24) : mword 64) 2
                      = mword_of_int (SL + 0x26)) by pcw.
      iEval (rewrite Hpp26) in "Hpc".
      (* ================= +0x26 jal ra,argstr ================= *)
      iApply (wp_jal_s_sconf (CID := CID14) (mword_of_int (SL + 0x26)) Rra
                (mword_of_int 2087362 : mword 21) N2 (K - 38)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi26").
      iIntros (CID15 Hq15) "Hcg Hpc".
      set (N3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SL + 0x26) : mword 64) 4)]> N2).
      assert (Hjas2 : add_vec (mword_of_int (SL + 0x26) : mword 64)
                        (sign_extend' 64 (mword_of_int 2087362 : mword 21))
                      = mword_of_int KernelSyms.argstr) by pcw.
      iEval (rewrite Hjas2) in "Hpc".
      assert (HN3ra : (N3 !!! Regidx Rra : mword 64)
                      = add_vec_int (mword_of_int (SL + 0x26) : mword 64) 4)
        by (rewrite /N3; apply upd_eq).
      assert (HN3a0 : (N3 !!! Regidx Ra0 : mword 64)
                      = (mword_of_int (Z.of_nat 1) : mword 64))
        by (rewrite /N3 upd_ne; [exact HN2a0 | nz]).
      assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22)
        by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
      assert (HN3a2 : (N3 !!! Regidx Ra2 : mword 64)
                      = (mword_of_int (Z.of_nat 128) : mword 64))
        by (rewrite /N3 upd_ne; [exact HN2a2 | nz]).
      assert (HN3regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) N3)
        by (rewrite /N3; apply sl_regs_caller; [exact Hcsra | exact HN2regs]).
      iDestruct (sl_bytes_name (pa_stk sp0 22) 128 with "HbW") as (bw0) "HbW".
      sl_own_transport CID9 CID15 eb pj b.
      iApply (Argstr.wp_argstr_sconf (CID := CID15) γa γf N3 (K - 38)%nat 0%nat
                eb pj 1%nat v1 pid (upd_upt V P1) 128%nat bw0 b lks
                sl_arg1_lt HN3a0 Harg1 sl_noff0 ltac:(exact Kar) HN3a2
                sl_maxpath_lt (Hlb "kmem"%string)
                with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [HbW]").
      { iEval (rewrite HN3a1). iExact "HbW". }
      iIntros (CID16 Hq16 mas2 P2 bw1)
        "%Hcsas2 %Hupt2 Hcg Hown Hpc Hpriv HbW %Hfsr2".
      iEval (rewrite HN3a1) in "HbW".
      iEval (rewrite sl_upd_upt_idem) in "Hpriv".
      assert (Hpc2a : ret_pc (N3 !!! Regidx Rra : mword 64)
                      = mword_of_int (SL + 0x2a)) by (rewrite HN3ra; pcw).
      iEval (rewrite Hpc2a) in "Hpc".
      assert (Hupt : uptd_ext (pv_upt V) P2).
      { apply (uptd_ext_trans (pv_upt V) P1 P2); [exact Hupt1 | exact Hupt2]. }
      assert (Has2regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                           (m !!! Regidx Rs2 : mword 64) mas2)
        by exact (sl_regs_cs m sp0 _ _ N3 mas2 Hcsas2 HN3regs).
      (* ================= +0x2a c.li a5,-1 ================= *)
      iApply (wp_cli_s_sconf (CID := CID16) (mword_of_int (SL + 0x2a)) Ra5
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                mas2 (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hi2a").
      iIntros (CID17 Hq17) "Hcg Hpc".
      set (N4 := <[Regidx Ra5 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> mas2).
      assert (HN4a5 : (N4 !!! Regidx Ra5 : mword 64)
                      = (mword_of_int (-1) : mword 64))
        by (rewrite /N4; apply upd_eq).
      assert (HN4a0 : (N4 !!! Regidx Ra0 : mword 64)
                      = (mas2 !!! Regidx Ra0 : mword 64))
        by (rewrite /N4 upd_ne; [reflexivity | nz]).
      assert (HN4regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) N4)
        by (rewrite /N4; apply sl_regs_caller; [exact Hcsa5 | exact Has2regs]).
      assert (Hpp2c : add_vec_int (mword_of_int (SL + 0x2a) : mword 64) 2
                      = mword_of_int (SL + 0x2c)) by pcw.
      iEval (rewrite Hpp2c) in "Hpc".
      (* ================= +0x2c bltz a0 -> ARM A ================= *)
      destruct Hfsr2 as [(pk2 & Hpk2 & Hpcstr2 & Hpr2) | Hpr2].
      + (* ========== BOTH strings fetched: on to begin_op ========== *)
        iApply (wp_blt_x0_fall_s_sconf (CID := CID17) (mword_of_int (SL + 0x2c))
                  (mword_of_int 238 : mword 13) Ra0 N4 (K - 38)%nat b
                  ltac:(nz)
                  ltac:(rgne; rewrite HN4a0 Hpr2;
                        exact (sl_nonneg _ (sl_len_range pk2 Hpk2)))
                  with "Hcg Hpc Hi2c").
        iIntros (CID18 Hq18) "Hcg Hpc".
        assert (Hpp30 : add_vec_int (mword_of_int (SL + 0x2c) : mword 64) 4
                        = mword_of_int (SL + 0x30)) by pcw.
        iEval (rewrite Hpp30) in "Hpc".
        (* THE PROCESS BLOCK, OPENED for the two walks: the cwd reference
           comes off, then the cell and the pid quarter, and all three stay
           out until whichever arm rebuilds the block. *)
        (* three-way now: [FirstTok.first_tok] parks beside the reference and
           every rebuilding arm below hands it straight back. *)
        iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2) with "Hpriv")
          as "[Hpnc [Href Hftok]]".
        iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
        iDestruct "Hpnc" as "[Hpidq Hofiles]".
        iDestruct (cwd_ref_held with "Href") as "Hcwdref".
        iEval (cbn [upd_upt pv_cwd]) in "Hcwdref".
        iDestruct (sl_ir3 with "Hir") as "[Hir2 Hir1]".
        iClear "Hi00 Hi02 Hi04 Hi06 Hi08 Hi0c Hi10 Hi12 Hi16 Hi18 Hi1c Hi20
                Hi24 Hi26 Hi2a Hi2c".
        iPoseProof (slki_30 with "Htext") as "Hi30".
        iPoseProof (slki_32 with "Htext") as "Hi32".
        iPoseProof (slki_36 with "Htext") as "Hi36".
        iPoseProof (slki_3a with "Htext") as "Hi3a".
        iPoseProof (slki_3e with "Htext") as "Hi3e".
        iPoseProof (slki_40 with "Htext") as "Hi40".
        assert (Htgbc : add_vec (mword_of_int (SL + 0x40) : mword 64)
                  (sign_extend' 64
                     (sign_extend' 13
                        (concat_vec (mword_of_int 62 : mword 8) ('b"0"))))
                  = mword_of_int (SL + 0xbc)) by pcw.
        assert (HN4s1 : (N4 !!! Regidx Rs1 : mword 64)
                        = (m !!! Regidx Rs1 : mword 64))
          by exact (sl_regs_s1 _ _ _ _ _ HN4regs).
        (* ===== +0x30 c.sdsp s1,280(sp) -- slot 3, saved LATE ===== *)
        assert (Hd3 : add_vec (N4 !!! Regidx csp_rs1 : mword 64)
                        (zero_extend' 64
                           (concat_vec (mword_of_int 35 : mword 6) ('b"000")))
                      = pa_stk sp0 3)
          by (rewrite (sl_regs_sp _ _ _ _ _ HN4regs); apply sl_frm3).
        iEval (rewrite -Hd3) in "Hf3".
        iApply (wp_csdsp_s_sconf (CID := CID18) (mword_of_int (SL + 0x30))
                  (mword_of_int 35 : mword 6) Rs1 N4 (K - 38)%nat u3 b
                  with "Hcg Hpc Hi30 Hf3").
        iIntros (CID19 Hq19) "Hcg Hpc Hf3".
        iEval (rgne; rewrite Hd3 HN4s1) in "Hf3".
        assert (Hpp32 : add_vec_int (mword_of_int (SL + 0x30) : mword 64) 2
                        = mword_of_int (SL + 0x32)) by pcw.
        iEval (rewrite Hpp32) in "Hpc".
        (* ===== +0x32 jal ra,begin_op ===== *)
        iApply (wp_jal_s_sconf (CID := CID19) (mword_of_int (SL + 0x32)) Rra
                  (mword_of_int 2092482 : mword 21) N4 (K - 38)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi32").
        iIntros (CID20 Hq20) "Hcg Hpc".
        set (Q0 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (SL + 0x32) : mword 64) 4)]> N4).
        assert (Hjbo : add_vec (mword_of_int (SL + 0x32) : mword 64)
                         (sign_extend' 64 (mword_of_int 2092482 : mword 21))
                       = mword_of_int KernelSyms.begin_op) by pcw.
        iEval (rewrite Hjbo) in "Hpc".
        assert (HQ0ra : (Q0 !!! Regidx Rra : mword 64)
                        = add_vec_int (mword_of_int (SL + 0x32) : mword 64) 4)
          by (rewrite /Q0; apply upd_eq).
        assert (HQ0regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                            (m !!! Regidx Rs2 : mword 64) Q0)
          by (rewrite /Q0; apply sl_regs_caller; [exact Hcsra | exact HN4regs]).
        sl_own_transport CID16 CID20 eb pj b.
        iApply (BeginOp.wp_begin_op_sconf (CID := CID20) gs j gl bn g gfs cov
                  logstart dev pid (DfracOwn (1/4)) Q0 (K - 38)%nat eb b lks
                  (upd_upt V P2) ltac:(exact Kbo) Hj Hgl (Hlb "log"%string)
                  with "Hcg Hown [] [] Htext Hpc Hlog Hpidq Hprocs").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        iIntros (CID21 Hq21 mbo) "%Hcsbo Hcg Hown _ _ Hpc Hpidq Hop".
        assert (Hpc36 : ret_pc (Q0 !!! Regidx Rra : mword 64)
                        = mword_of_int (SL + 0x36)) by (rewrite HQ0ra; pcw).
        iEval (rewrite Hpc36) in "Hpc".
        assert (Hboregs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                            (m !!! Regidx Rs2 : mword 64) mbo)
          by exact (sl_regs_cs m sp0 _ _ Q0 mbo Hcsbo HQ0regs).
        (* ===== +0x36 addi a0,s0,-304 ===== *)
        iApply (wp_addi4_s_sconf (CID := CID21) (mword_of_int (SL + 0x36)) Ra0 Rs0
                  (mword_of_int 3792 : mword 12) mbo (K - 38)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi36").
        iIntros (CID22 Hq22) "Hcg Hpc".
        set (Q1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mbo !!! Regidx Rs0)
                         (sign_extend' 64 (mword_of_int 3792 : mword 12)))]> mbo).
        assert (HQ1a0 : (Q1 !!! Regidx Ra0 : mword 64) = pa_stk sp0 38).
        { etransitivity; [ rewrite /Q1; apply upd_eq |].
          rewrite (sl_regs_s0 _ _ _ _ _ Hboregs). apply sl_bufold. }
        assert (HQ1regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                            (m !!! Regidx Rs2 : mword 64) Q1)
          by (rewrite /Q1; apply sl_regs_caller; [exact Hcsa0 | exact Hboregs]).
        assert (Hpp3a : add_vec_int (mword_of_int (SL + 0x36) : mword 64) 4
                        = mword_of_int (SL + 0x3a)) by pcw.
        iEval (rewrite Hpp3a) in "Hpc".
        (* ===== +0x3a jal ra,namei ===== *)
        iApply (wp_jal_s_sconf (CID := CID22) (mword_of_int (SL + 0x3a)) Rra
                  (mword_of_int 2091996 : mword 21) Q1 (K - 38)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi3a").
        iIntros (CID23 Hq23) "Hcg Hpc".
        set (Q2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (SL + 0x3a) : mword 64) 4)]> Q1).
        assert (Hjna : add_vec (mword_of_int (SL + 0x3a) : mword 64)
                         (sign_extend' 64 (mword_of_int 2091996 : mword 21))
                       = mword_of_int KernelSyms.namei) by pcw.
        iEval (rewrite Hjna) in "Hpc".
        assert (HQ2ra : (Q2 !!! Regidx Rra : mword 64)
                        = add_vec_int (mword_of_int (SL + 0x3a) : mword 64) 4)
          by (rewrite /Q2; apply upd_eq).
        assert (HQ2a0 : (Q2 !!! Regidx Ra0 : mword 64) = pa_stk sp0 38)
          by (rewrite /Q2 upd_ne; [exact HQ1a0 | nz]).
        assert (HQ2regs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                            (m !!! Regidx Rs2 : mword 64) Q2)
          by (rewrite /Q2; apply sl_regs_caller; [exact Hcsra | exact HQ1regs]).
        iDestruct "Hop" as (Sb0) "HopS".
        iDestruct (sl_buf_split (pa_stk sp0 38) bo1 pk1 Hpk1 with "HbO")
          as "[Hbufk Hbufrest]".
        sl_own_transport CID21 CID23 eb pj b.
        iApply (Namei.wp_namei_gen (CID := CID23) gs j gl gu gd gk pd pav pu bn
                  g gfs gi cn gtl γa γf cov logstart bmapstart inodestart nib
                  size dev pk1 bo1 MAXOPBLOCKS Sb0
                  pid (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
                  Q2 (K - 38)%nat eb b lks (upd_upt V P2)
                  ltac:(exact Kna) Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom
                  Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hpcstr1
                  (sl_plen_lt pk1 Hpk1) (sl_bud_walk _) Hj Hgl
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hkenv Hitab Hitinv
                        Hescrows Hslks Hireg Hropen Hprocs Hdev Hgeo Hdlk Hsbb Hsbi
                        Hbmres Hpidq Hcwdref [Hbufk] Hbsl Hir2 HopS").
        (* namei is eb-generic now; sys_link is still at [eb = true]. *)
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iEval (rewrite HQ2a0). iExact "Hbufk". }
        iIntros (CID24 Hq24 mna n1 Sb1 ok ipv w1)
          "%Hcsna Hcg Hown _ _ Hpc Hsbb Hsbi Hpidq Hcwdref
           Hbufk Hbsl %HSb1 %Hw1 %Hn1 HopS Hres".
        iEval (rewrite HQ2a0) in "Hbufk".
        assert (Hpc3e : ret_pc (Q2 !!! Regidx Rra : mword 64)
                        = mword_of_int (SL + 0x3e)) by (rewrite HQ2ra; pcw).
        iEval (rewrite Hpc3e) in "Hpc".
        assert (Hnaregs : sl_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                            (m !!! Regidx Rs2 : mword 64) mna)
          by exact (sl_regs_cs m sp0 _ _ Q2 mna Hcsna HQ2regs).
        (* ===== +0x3e c.mv s1,a0 ===== *)
        iApply (wp_cmv_s_sconf (CID := CID24) (mword_of_int (SL + 0x3e)) Rs1 Ra0
                  mna (K - 38)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3e").
        iIntros (CID25 Hq25) "Hcg Hpc".
        set (Q3 := <[Regidx Rs1 := regval_into_reg
                      (add_vec zero_reg (mna !!! Regidx Ra0))]> mna).
        assert (HQ3a0 : (Q3 !!! Regidx Ra0 : mword 64)
                        = (mna !!! Regidx Ra0 : mword 64))
          by (rewrite /Q3 upd_ne; [reflexivity | nz]).
        assert (HQ3regs : sl_regs m sp0 (mna !!! Regidx Ra0 : mword 64)
                            (m !!! Regidx Rs2 : mword 64) Q3).
        { rewrite /Q3.
          exact (sl_regs_wr_s1 m sp0 _ _ _ mna _ (add_vec_zero_l _) Hnaregs). }
        assert (HQ3s2 : (Q3 !!! Regidx Rs2 : mword 64)
                        = (m !!! Regidx Rs2 : mword 64))
          by exact (sl_regs_s2 _ _ _ _ _ HQ3regs).
        assert (Hpp40 : add_vec_int (mword_of_int (SL + 0x3e) : mword 64) 2
                        = mword_of_int (SL + 0x40)) by pcw.
        iEval (rewrite Hpp40) in "Hpc".
        (* ===== +0x40 c.beqz a0 -> ARM B ===== *)
        destruct ok.
        * (* ---------- the path RESOLVED ---------- *)
          iDestruct "Hres" as "(%Hnaip & Hheldip & Hir1b)".
          iDestruct (inode_held_ne_zero with "Hheldip") as %Hipnz.
          iApply (wp_cbeqz_fall_s_sconf (CID := CID25) (mword_of_int (SL + 0x40))
                    (mword_of_int 62 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    Q3 (K - 38)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HQ3a0 Hnaip;
                          apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
                    with "Hcg Hpc Hi40").
          iIntros (CID26 Hq26) "Hcg Hpc".
          assert (Hpp42 : add_vec_int (mword_of_int (SL + 0x40) : mword 64) 2
                          = mword_of_int (SL + 0x42)) by pcw.
          iEval (rewrite Hpp42) in "Hpc".
          (* THE REFERENCE namei MADE, taken apart: the slot it names is what
             ilock / iunlock / iupdate / iunlockput are all indexed by. *)
          iDestruct "Hheldip" as (kk qq inum) "(%Hipe & %Hkk & %Hinumc & Hrefip & Hru)".
          iEval (rewrite -Hcdev) in "Hrefip".
          assert (Hinb : bv_unsigned inum < 16 * Z.of_nat nib)
            by (rewrite Hcnib; exact Hinumc).
          destruct (Hiregb inum Hinb) as [Hiblk Hiblog].
          iEval (rewrite inode_ref_shed) in "Hrefip".
          iDestruct "Hrefip" as "[Hkeep Hshr]".
          iEval (rewrite inode_shr_gen_intro) in "Hshr".
          iDestruct "Hshr" as (gsh) "Hshr".
          iDestruct (sl_esc_acc cn gfs gi cov logstart kk Hkk with "Hescrows")
            as "#Hesck".
          iDestruct (sl_slk_acc cn kk Hkk with "Hslks") as (gil gisl) "#Hslkk".
          iDestruct (sl_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
          rewrite Hnaip Hipe in HQ3regs.
          assert (HQ3s1 : (Q3 !!! Regidx Rs1 : mword 64) = ientry kk)
            by exact (sl_regs_s1 _ _ _ _ _ HQ3regs).
          assert (HQ3ia0 : (Q3 !!! Regidx Ra0 : mword 64) = ientry kk)
            by (rewrite HQ3a0 Hnaip; exact Hipe).
          assert (Hiu1 : (iput_units <= n1)%nat)
            by exact (sl_bud_iput _ w1 true (proj1 Hn1)).
          iClear "Hi30 Hi32 Hi36 Hi3a Hi3e Hi40".
          iPoseProof (slki_42 with "Htext") as "Hi42".
          iPoseProof (slki_46 with "Htext") as "Hi46".
          iPoseProof (slki_4a with "Htext") as "Hi4a".
          iPoseProof (slki_4c with "Htext") as "Hi4c".
          iPoseProof (slki_50 with "Htext") as "Hi50".
          iPoseProof (slki_54 with "Htext") as "Hi54".
          iPoseProof (slki_56 with "Htext") as "Hi56".
          iPoseProof (slki_58 with "Htext") as "Hi58".
          assert (Htgc6 : add_vec (mword_of_int (SL + 0x4c) : mword 64)
                    (sign_extend' 64 (mword_of_int 122 : mword 13))
                    = mword_of_int (SL + 0xc6)) by pcw.
          assert (Htgd6 : add_vec (mword_of_int (SL + 0x58) : mword 64)
                    (sign_extend' 64 (mword_of_int 126 : mword 13))
                    = mword_of_int (SL + 0xd6)) by pcw.
          (* ===== +0x42 jal ra,ilock ===== *)
          iApply (wp_jal_s_sconf (CID := CID26) (mword_of_int (SL + 0x42)) Rra
                    (mword_of_int 2089800 : mword 21) Q3 (K - 38)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi42").
          iIntros (CID27 Hq27) "Hcg Hpc".
          set (R0 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (SL + 0x42) : mword 64) 4)]> Q3).
          assert (Hjil : add_vec (mword_of_int (SL + 0x42) : mword 64)
                           (sign_extend' 64 (mword_of_int 2089800 : mword 21))
                         = mword_of_int KernelSyms.ilock) by pcw.
          iEval (rewrite Hjil) in "Hpc".
          assert (HR0ra : (R0 !!! Regidx Rra : mword 64)
                          = add_vec_int (mword_of_int (SL + 0x42) : mword 64) 4)
            by (rewrite /R0; apply upd_eq).
          assert (HR0a0 : (R0 !!! Regidx Ra0 : mword 64) = ientry kk)
            by (rewrite /R0 upd_ne; [exact HQ3ia0 | nz]).
          assert (HR0regs : sl_regs m sp0 (ientry kk)
                              (m !!! Regidx Rs2 : mword 64) R0)
            by (rewrite /R0; apply sl_regs_caller; [exact Hcsra | exact HQ3regs]).
          sl_own_transport CID24 CID27 eb pj b.
          iApply (Ilock.wp_ilock_sconf (CID := CID27) gs j gl gu gd gk pd pav pu
                    bn gfs gi cn gil gisl cov logstart inodestart nib
                    kk (qq/2)%Qp gsh PlainK dev inum pid (DfracOwn (1/4)) dqs
                    R0 (K - 38)%nat eb b lks
                    (upd_upt V P2) ltac:(exact Kil) Hkk Hgeom Hist0 Hiblk Hinb Hj Hgl HR0a0
                    (Hlb "bcache"%string)
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hitinv Hesck
                          Hireg Hslkk Hshr Hru Hsbi Hpidq Hprocs Hdev Hgeo Hdlk
                          Hbs1").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          iIntros (CID28 Hq28 mil dn bm fl)
            "%Hcsil Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1 Hslkd Hdep
             Hidev Hiinum Hivalid Hload #Hshot Hfrz %Hfl Hru %Hilkp".
          assert (Hpc46 : ret_pc (R0 !!! Regidx Rra : mword 64)
                          = mword_of_int (SL + 0x46)) by (rewrite HR0ra; pcw).
          iEval (rewrite Hpc46) in "Hpc".
          assert (Hilregs : sl_regs m sp0 (ientry kk)
                              (m !!! Regidx Rs2 : mword 64) mil)
            by exact (sl_regs_cs m sp0 _ _ R0 mil Hcsil HR0regs).
          assert (Hils1 : (mil !!! Regidx Rs1 : mword 64) = ientry kk)
            by exact (sl_regs_s1 _ _ _ _ _ Hilregs).
          iDestruct "Hload" as (dat)
            "(%Hiok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta & Haddrs & Hind &
              Hblocks)".
          iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
          iEval (rewrite /i_type) in "Hity".
          iEval (rewrite /i_nlink) in "Hinl".
          (* ===== +0x46 lh a4,68(s1) -- ip->type ===== *)
          iApply (wp_lh_s_sconf (CID := CID28) (kt := KT1) (ktd := KT0) (mword_of_int (SL + 0x46)) Ra4 Rs1
                    (mword_of_int 68 : mword 12) mil (K - 38)%nat
                    (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc Hi46 [Hity]").
          { iEval (rgne; rewrite Hils1). iExact "Hity". }
          iIntros (CID29 Hq29) "Hcg Hpc Hity".
          iEval (rgne; rewrite Hils1) in "Hity".
          set (R1 := <[Regidx Ra4 := regval_into_reg
                        (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> mil).
          assert (HR1a4 : (R1 !!! Regidx Ra4 : mword 64)
                          = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
            by (rewrite /R1; apply upd_eq).
          assert (HR1regs : sl_regs m sp0 (ientry kk)
                              (m !!! Regidx Rs2 : mword 64) R1)
            by (rewrite /R1; apply sl_regs_caller; [exact Hcsa4 | exact Hilregs]).
          assert (Hpp4a : add_vec_int (mword_of_int (SL + 0x46) : mword 64) 4
                          = mword_of_int (SL + 0x4a)) by pcw.
          iEval (rewrite Hpp4a) in "Hpc".
          (* ===== +0x4a c.li a5,1 ===== *)
          iApply (wp_cli_s_sconf (CID := CID29) (mword_of_int (SL + 0x4a)) Ra5
                    (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                    R1 (K - 38)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc Hi4a").
          iIntros (CID30 Hq30) "Hcg Hpc".
          set (R2 := <[Regidx Ra5 := regval_into_reg
                        (mword_of_int 1 : mword 64)]> R1).
          assert (HR2a5 : (R2 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
            by (rewrite /R2; apply upd_eq).
          assert (HR2a4 : (R2 !!! Regidx Ra4 : mword 64)
                          = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
            by (rewrite /R2 upd_ne; [exact HR1a4 | nz]).
          assert (HR2regs : sl_regs m sp0 (ientry kk)
                              (m !!! Regidx Rs2 : mword 64) R2)
            by (rewrite /R2; apply sl_regs_caller; [exact Hcsa5 | exact HR1regs]).
          assert (HR2s1 : (R2 !!! Regidx Rs1 : mword 64) = ientry kk)
            by exact (sl_regs_s1 _ _ _ _ _ HR2regs).
          assert (HR2s2 : (R2 !!! Regidx Rs2 : mword 64)
                          = (m !!! Regidx Rs2 : mword 64))
            by exact (sl_regs_s2 _ _ _ _ _ HR2regs).
          assert (Hpp4c : add_vec_int (mword_of_int (SL + 0x4a) : mword 64) 2
                          = mword_of_int (SL + 0x4c)) by pcw.
          iEval (rewrite Hpp4c) in "Hpc".
          (* ===== +0x4c beq a4,a5 -> ARM C ===== *)
          destruct (decide (di_type dn = (mword_of_int 1 : mword 16))) as [Hty | Hty].
          -- (* ======== ARM C: it IS a directory ======== *)
             iApply (wp_beq_taken_s_sconf (CID := CID30) (mword_of_int (SL + 0x4c))
                       (mword_of_int 122 : mword 13) Ra5 Ra4 R2 (K - 38)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HR2a4 HR2a5;
                             exact (sl_tdir_eq _ Hty))
                       ltac:(vm_compute; reflexivity)
                       with "Hcg Hpc Hi4c").
             iIntros (CID31 Hq31). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htgc6) in "Hpc".
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
               - rewrite /inode_meta /i_type /i_nlink. iFrame.
               - iFrame. }
             iDestruct (sl_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
               [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
             iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                          with "Hbufk Hbufrest") as "HbO".
             iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO") as (bo2) "HbO".
             iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN") as (bn0) "HbN".
             iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID31)
                          ltac:(wp_next_chain) with "Hcont") as "Hcont".
             sl_own_transport CID28 CID31 eb pj b.
             iApply (Tails.sl_tail_c (CID0 := CID31) gs j gl gu gd gk pd pav pu
                       bn g gfs gi cn gtl gil gisl cov logstart bmapstart
                       inodestart nib size dev kk (qq/2)%Qp (qq/2)%Qp gsh
                       inum dn bm n1 pid (DfracOwn (1/4)) dqb dqs
                       m R2 sp0 K eb b lks u4 bn0 bw1 bo2
                       (upd_upt V P2) ltac:(exact Kiup) ltac:(exact Keo) K38 Kpop Hkk Hgeom
                       Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb Hcovb
                       Hiu1 Hj Hgl Hlkempty ltac:(reflexivity)
                       (sl_regs_sp _ _ _ _ _ HR2regs)
                       (sl_regs_thr _ _ _ _ _ HR2regs) HR2s1 HR2s2 Hal
                       with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                             Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd Hdep
                             Hidev Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb
                             Hsbi
                             Hbmres Hpidq Hprocs Hdev Hgeo Hdlk Hbsl [HopS]
                             Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                             [Hsbs Hir1 Hir1b Hcwdref Hofiles Hftok Hcont]").
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             { rewrite /log_op. iExists Sb1. iExact "HopS". }
             iEval (rewrite /wp_next).
             iIntros (CIDy) "%Hqy". iIntros (mf)
               "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpidq Hsbb Hsbi
                Hbsl Hislot".
             iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
             iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
             iCombine "Hpidq Hofiles" as "Hpnc".
             iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
             iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                          with "[Hpnc Href Hftok]") as "Hpriv";
               [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
             iDestruct (iref_slots_combine 1 1 with "Hir1 Hir1b") as "Hir2c".
             iDestruct (iref_slots_combine 2 1 with "Hir2c Hislot") as "Hir".
             iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                       Hbsl Hsbb Hsbi Hsbs Hir Hpriv [%]").
             { exact Hcsf. }
             { exact Hupt. }
             { left. rewrite Ha0f. reflexivity. }
          -- (* ======== not a directory: on to the NLINK_MAX guard ======== *)
             iApply (wp_beq_fall_s_sconf (CID := CID30) (mword_of_int (SL + 0x4c))
                       (mword_of_int 122 : mword 13) Ra5 Ra4 R2 (K - 38)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HR2a4 HR2a5;
                             exact (sl_tdir_ne _ Hty))
                       with "Hcg Hpc Hi4c").
             iIntros (CID31 Hq31) "Hcg Hpc".
             assert (Hpp50 : add_vec_int (mword_of_int (SL + 0x4c) : mword 64) 4
                             = mword_of_int (SL + 0x50)) by pcw.
             iEval (rewrite Hpp50) in "Hpc".
             (* ===== +0x50 lh a5,74(s1) -- ip->nlink, SIGN extended ===== *)
             iApply (wp_lh_s_sconf (CID := CID31) (kt := KT1) (ktd := KT0) (mword_of_int (SL + 0x50)) Ra5 Rs1
                       (mword_of_int 74 : mword 12) R2 (K - 38)%nat
                       (di_nlink dn : mword 16) b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc Hi50 [Hinl]").
             { iEval (rgne; rewrite HR2s1). iExact "Hinl". }
             iIntros (CID32 Hq32) "Hcg Hpc Hinl".
             iEval (rgne; rewrite HR2s1) in "Hinl".
             set (R3 := <[Regidx Ra5 := regval_into_reg
                           (sign_extend' 64 (di_nlink dn : mword 16) : mword 64)]> R2).
             assert (HR3a5 : (R3 !!! Regidx Ra5 : mword 64)
                             = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
               by (rewrite /R3; apply upd_eq).
             assert (HR3regs : sl_regs m sp0 (ientry kk)
                                 (m !!! Regidx Rs2 : mword 64) R3)
               by (rewrite /R3; apply sl_regs_caller; [exact Hcsa5 | exact HR2regs]).
             assert (Hpp54 : add_vec_int (mword_of_int (SL + 0x50) : mword 64) 4
                             = mword_of_int (SL + 0x54)) by pcw.
             iEval (rewrite Hpp54) in "Hpc".
             (* ===== +0x54 c.lui a4,0x8 ===== *)
             iApply (wp_clui_s_sconf (CID := CID32) (mword_of_int (SL + 0x54)) Ra4
                       (sign_extend' 20 (mword_of_int 8 : mword 6))
                       (mword_of_int 32768 : mword 64) R3 (K - 38)%nat b
                       ltac:(nz) ltac:(rdok) sl_lui8 with "Hcg Hpc Hi54").
             iIntros (CID33 Hq33) "Hcg Hpc".
             set (R4 := <[Regidx Ra4 := regval_into_reg
                           (mword_of_int 32768 : mword 64)]> R3).
             assert (HR4a4 : (R4 !!! Regidx Ra4 : mword 64)
                             = (mword_of_int 32768 : mword 64))
               by (rewrite /R4; apply upd_eq).
             assert (HR4a5 : (R4 !!! Regidx Ra5 : mword 64)
                             = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
               by (rewrite /R4 upd_ne; [exact HR3a5 | nz]).
             assert (HR4regs : sl_regs m sp0 (ientry kk)
                                 (m !!! Regidx Rs2 : mword 64) R4)
               by (rewrite /R4; apply sl_regs_caller; [exact Hcsa4 | exact HR3regs]).
             assert (Hpp56 : add_vec_int (mword_of_int (SL + 0x54) : mword 64) 2
                             = mword_of_int (SL + 0x56)) by pcw.
             iEval (rewrite Hpp56) in "Hpc".
             (* ===== +0x56 c.addi a4,a4,-1 : NLINK_MAX = 32767 ===== *)
             iApply (wp_caddi_s_sconf (CID := CID33) (mword_of_int (SL + 0x56)) Ra4
                       (mword_of_int 63 : mword 6) R4 (K - 38)%nat b
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi56").
             iIntros (CID34 Hq34) "Hcg Hpc".
             set (R5 := <[Regidx Ra4 := regval_into_reg
                           (add_vec (rget R4 Ra4)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> R4).
             assert (HR5a4 : (R5 !!! Regidx Ra4 : mword 64)
                             = (mword_of_int 32767 : mword 64)).
             { rewrite /R5 upd_eq. rgne. rewrite HR4a4. exact sl_nmax_const. }
             assert (HR5a5 : (R5 !!! Regidx Ra5 : mword 64)
                             = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
               by (rewrite /R5 upd_ne; [exact HR4a5 | nz]).
             assert (HR5regs : sl_regs m sp0 (ientry kk)
                                 (m !!! Regidx Rs2 : mword 64) R5)
               by (rewrite /R5; apply sl_regs_caller; [exact Hcsa4 | exact HR4regs]).
             assert (HR5s1 : (R5 !!! Regidx Rs1 : mword 64) = ientry kk)
               by exact (sl_regs_s1 _ _ _ _ _ HR5regs).
             assert (HR5s2 : (R5 !!! Regidx Rs2 : mword 64)
                             = (m !!! Regidx Rs2 : mword 64))
               by exact (sl_regs_s2 _ _ _ _ _ HR5regs).
             assert (Hpp58 : add_vec_int (mword_of_int (SL + 0x56) : mword 64) 2
                             = mword_of_int (SL + 0x58)) by pcw.
             iEval (rewrite Hpp58) in "Hpc".
             (* ===== +0x58 beq a5,a4 -> ARM D ===== *)
             destruct (decide (di_nlink dn = (mword_of_int 32767 : mword 16)))
               as [Hnl | Hnl].
             ++ (* ======== ARM D: the guard fires ======== *)
                iApply (wp_beq_taken_s_sconf (CID := CID34)
                          (mword_of_int (SL + 0x58)) (mword_of_int 126 : mword 13)
                          Ra4 Ra5 R5 (K - 38)%nat b ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HR5a4 HR5a5;
                                exact (sl_nmax_eq _ Hnl))
                          ltac:(vm_compute; reflexivity)
                          with "Hcg Hpc Hi58").
                iIntros (CID35 Hq35). iApply bi.later_intro. iIntros "Hcg Hpc".
                iEval (rewrite Htgd6) in "Hpc".
                iAssert (ic_loaded gfs gi cov logstart kk inum dn bm)
                  with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind Hblocks
                         Hdlnk]" as "Hload".
                { rewrite /ic_loaded. iExists dat.
                  iSplitR; [iPureIntro; exact Hiok |].
                  iSplitR; [iPureIntro; exact Hdok |].
                  iSplitR; [iPureIntro; exact Hddix |].
                  iSplitR; [iPureIntro; exact Hdoc |].
                  iSplitR; [iPureIntro; exact Hduq |].
                  iSplitL "Hdlnk"; [iExact "Hdlnk" |].
                  iFrame "Hdiat".
                  iSplitL "Hity Himaj Himin Hinl Hisz".
                  - rewrite /inode_meta /i_type /i_nlink. iFrame.
                  - iFrame. }
                iDestruct (sl_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
                  [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
                iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                             with "Hbufk Hbufrest") as "HbO".
                iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO")
                  as (bo2) "HbO".
                iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN")
                  as (bn0) "HbN".
                iDestruct (wp_next_shift (b := true) (CIDa := CID0)
                             (CIDb := CID35) ltac:(wp_next_chain)
                             with "Hcont") as "Hcont".
                sl_own_transport CID28 CID35 eb pj b.
                iApply (Tails.sl_tail_d (CID0 := CID35) gs j gl gu gd gk pd pav pu
                          bn g gfs gi cn gtl gil gisl cov logstart bmapstart
                          inodestart nib size dev kk (qq/2)%Qp (qq/2)%Qp gsh
                          inum dn bm n1 pid (DfracOwn (1/4)) dqb dqs
                          m R5 sp0 K eb b lks u4 bn0 bw1 bo2
                          (upd_upt V P2) ltac:(exact Kiup) ltac:(exact Keo) K38 Kpop Hkk Hgeom
                          Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb Hcovb
                          Hiu1 Hj Hgl Hlkempty ltac:(reflexivity)
                          (sl_regs_sp _ _ _ _ _ HR5regs)
                          (sl_regs_thr _ _ _ _ _ HR5regs) HR5s1 HR5s2 Hal
                          with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam
                                Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                                Hdep Hidev Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru
                                Hsbb
                                Hsbi Hbmres Hpidq Hprocs Hdev Hgeo Hdlk Hbsl
                                [HopS] Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                                [Hsbs Hir1 Hir1b Hcwdref Hofiles Hftok Hcont]").
                { rewrite Heb /trap_csrs_ext. done. }
                { rewrite Heb /cpu_claim_ext. done. }
                { rewrite /log_op. iExists Sb1. iExact "HopS". }
                iEval (rewrite /wp_next).
                iIntros (CIDy) "%Hqy". iIntros (mf)
                  "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpidq Hsbb Hsbi
                   Hbsl Hislot".
                iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
                iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
                iCombine "Hpidq Hofiles" as "Hpnc".
                iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
                iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                             with "[Hpnc Href Hftok]") as "Hpriv";
                  [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
                iDestruct (iref_slots_combine 1 1 with "Hir1 Hir1b") as "Hir2c".
                iDestruct (iref_slots_combine 2 1 with "Hir2c Hislot") as "Hir".
                iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown Htce Hcce
                          Hpc Hbsl Hsbb Hsbi Hsbs Hir Hpriv [%]").
                { exact Hcsf. }
                { exact Hupt. }
                { left. rewrite Ha0f. reflexivity. }
             ++ (* ======== the guard PASSES: the mint ======== *)
                iApply (wp_beq_fall_s_sconf (CID := CID34)
                          (mword_of_int (SL + 0x58)) (mword_of_int 126 : mword 13)
                          Ra4 Ra5 R5 (K - 38)%nat b ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HR5a4 HR5a5;
                                exact (sl_nmax_ne _ Hnl))
                          with "Hcg Hpc Hi58").
                iIntros (CID35 Hq35) "Hcg Hpc".
                assert (Hpp5c : add_vec_int (mword_of_int (SL + 0x58) : mword 64) 4
                                = mword_of_int (SL + 0x5c)) by pcw.
                iEval (rewrite Hpp5c) in "Hpc".
                (* the namei walk left at least nine, so the mint's own
                   [log_opS (S u)] is available and the second walk's need
                   is met with room. *)
                destruct n1 as [| c1];
                  [exfalso; unfold iput_units in Hiu1; lia |].
                assert (Hu2 : (sl_u2 w1 <= c1)%nat)
                  by exact (sl_cnt_u1 w1 (S c1) c1 (proj1 Hn1) eq_refl).
                iClear "Hi42 Hi46 Hi4a Hi4c Hi50 Hi54 Hi56 Hi58".
                iPoseProof (slki_5c with "Htext") as "Hi5c".
                iPoseProof (slki_5e with "Htext") as "Hi5e".
                iPoseProof (slki_60 with "Htext") as "Hi60".
                iPoseProof (slki_64 with "Htext") as "Hi64".
                iPoseProof (slki_66 with "Htext") as "Hi66".
                iPoseProof (slki_6a with "Htext") as "Hi6a".
                iPoseProof (slki_6c with "Htext") as "Hi6c".
                iPoseProof (slki_70 with "Htext") as "Hi70".
                iPoseProof (slki_74 with "Htext") as "Hi74".
                iPoseProof (slki_78 with "Htext") as "Hi78".
                iPoseProof (slki_7c with "Htext") as "Hi7c".
                iPoseProof (slki_7e with "Htext") as "Hi7e".
                (* ===== +0x5c c.sdsp s2,272(sp) -- slot 4, saved LATER ===== *)
                assert (Hd4 : add_vec (R5 !!! Regidx csp_rs1 : mword 64)
                          (zero_extend' 64
                             (concat_vec (mword_of_int 34 : mword 6) ('b"000")))
                          = pa_stk sp0 4)
                  by (rewrite (sl_regs_sp _ _ _ _ _ HR5regs); apply sl_frm4).
                iEval (rewrite -Hd4) in "Hf4".
                iApply (wp_csdsp_s_sconf (CID := CID35) (mword_of_int (SL + 0x5c))
                          (mword_of_int 34 : mword 6) Rs2 R5 (K - 38)%nat u4 b
                          with "Hcg Hpc Hi5c Hf4").
                iIntros (CID36 Hq36) "Hcg Hpc Hf4".
                iEval (rgne; rewrite Hd4 HR5s2) in "Hf4".
                assert (Hpp5e : add_vec_int (mword_of_int (SL + 0x5c) : mword 64) 2
                                = mword_of_int (SL + 0x5e)) by pcw.
                iEval (rewrite Hpp5e) in "Hpc".
                (* ===== +0x5e c.addiw a5,a5,1 -- ip->nlink++ ===== *)
                iApply (wp_caddiw_s_sconf (CID := CID36) (mword_of_int (SL + 0x5e))
                          Ra5 (mword_of_int 1 : mword 6) R5 (K - 38)%nat b
                          ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
                iIntros (CID37 Hq37) "Hcg Hpc".
                set (S0 := <[Regidx Ra5 := regval_into_reg
                              (sign_extend' 64 (subrange_vec_dec
                                 (add_vec (rget R5 Ra5)
                                    (sign_extend' 64
                                       (sign_extend' 12
                                          (mword_of_int 1 : mword 6))))
                                 31 0))]> R5).
                assert (HS0a5 : (S0 !!! Regidx Ra5 : mword 64)
                                = sign_extend' 64 (subrange_vec_dec
                                    (add_vec
                                       (sign_extend' 64 (di_nlink dn : mword 16)
                                        : mword 64)
                                       (sign_extend' 64
                                          (sign_extend' 12
                                             (mword_of_int 1 : mword 6))
                                        : mword 64)) 31 0)).
                { rewrite /S0 upd_eq. rgne. rewrite HR5a5. reflexivity. }
                assert (HS0regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) S0)
                  by (rewrite /S0; apply sl_regs_caller;
                      [exact Hcsa5 | exact HR5regs]).
                assert (HS0s1 : (S0 !!! Regidx Rs1 : mword 64) = ientry kk)
                  by exact (sl_regs_s1 _ _ _ _ _ HS0regs).
                assert (Hpp60 : add_vec_int (mword_of_int (SL + 0x5e) : mword 64) 2
                                = mword_of_int (SL + 0x60)) by pcw.
                iEval (rewrite Hpp60) in "Hpc".
                (* ===== +0x60 sh a5,74(s1) ===== *)
                iApply (wp_sh_s_sconf (CID := CID37) (kt := KT1) (ktd := KT0) (mword_of_int (SL + 0x60))
                          Ra5 Rs1 (mword_of_int 74 : mword 12) S0 (K - 38)%nat
                          (di_nlink dn : mword 16) b with "Hcg Hpc Hi60 [Hinl]").
                { iEval (rgne; rewrite HS0s1). iExact "Hinl". }
                iIntros (CID38 Hq38) "Hcg Hpc Hinl".
                iEval (rgne; rgne; rewrite HS0s1 HS0a5) in "Hinl".
                iEval (rewrite (sl_nlink_incr (di_nlink dn))) in "Hinl".
                iAssert (inode_meta (ientry kk) (sl_incnl dn))
                  with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
                { rewrite /inode_meta /sl_incnl /sl_setnl /=.
                  rewrite /i_type /i_nlink. iFrame. }
                iAssert (inode_map gfs (ientry kk) bm)
                  with "[Haddrs Hind]" as "Hmap".
                { rewrite /inode_map. iFrame. }
                assert (Hpp64 : add_vec_int (mword_of_int (SL + 0x60) : mword 64) 4
                                = mword_of_int (SL + 0x64)) by pcw.
                iEval (rewrite Hpp64) in "Hpc".
                (* ===== +0x64 c.mv a0,s1 ===== *)
                iApply (wp_cmv_s_sconf (CID := CID38) (mword_of_int (SL + 0x64))
                          Ra0 Rs1 S0 (K - 38)%nat b ltac:(nz) ltac:(rdok)
                          with "Hcg Hpc Hi64").
                iIntros (CID39 Hq39) "Hcg Hpc".
                set (S1 := <[Regidx Ra0 := regval_into_reg
                              (add_vec zero_reg (S0 !!! Regidx Rs1))]> S0).
                assert (HS1a0 : (S1 !!! Regidx Ra0 : mword 64) = ientry kk).
                { etransitivity; [ rewrite /S1; apply upd_eq |].
                  rewrite add_vec_zero_l. exact HS0s1. }
                assert (HS1regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) S1)
                  by (rewrite /S1; apply sl_regs_caller;
                      [exact Hcsa0 | exact HS0regs]).
                assert (Hpp66 : add_vec_int (mword_of_int (SL + 0x64) : mword 64) 2
                                = mword_of_int (SL + 0x66)) by pcw.
                iEval (rewrite Hpp66) in "Hpc".
                (* ===== +0x66 jal ra,iupdate -- THE MINT ===== *)
                iApply (wp_jal_s_sconf (CID := CID39) (mword_of_int (SL + 0x66)) Rra
                          (mword_of_int 2089584 : mword 21) S1 (K - 38)%nat b
                          ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                          with "Hcg Hpc Hi66").
                iIntros (CID40 Hq40) "Hcg Hpc".
                set (S2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (SL + 0x66) : mword 64) 4)]> S1).
                assert (Hjiu : add_vec (mword_of_int (SL + 0x66) : mword 64)
                                 (sign_extend' 64 (mword_of_int 2089584 : mword 21))
                               = mword_of_int KernelSyms.iupdate) by pcw.
                iEval (rewrite Hjiu) in "Hpc".
                assert (HS2ra : (S2 !!! Regidx Rra : mword 64)
                                = add_vec_int (mword_of_int (SL + 0x66) : mword 64) 4)
                  by (rewrite /S2; apply upd_eq).
                assert (HS2a0 : (S2 !!! Regidx Ra0 : mword 64) = ientry kk)
                  by (rewrite /S2 upd_ne; [exact HS1a0 | nz]).
                assert (HS2regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) S2)
                  by (rewrite /S2; apply sl_regs_caller;
                      [exact Hcsra | exact HS1regs]).
                assert (Htynz : bv_unsigned (di_type dn) <> 0)
                  by exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
                assert (Haddreq : di_addrs dn = bm_cells bm)
                  by exact (proj1 (proj2 (proj2 Hiok))).
                assert (Hdirlen : length (bm_dir bm) = NDIRECT)
                  by exact (blkmap_wf_dir_len cov logstart bm (proj1 Hiok)).
                sl_own_transport CID28 CID40 eb pj b.
                iApply (Iupdate.wp_iupdate_link (CID := CID40) gs j gl gu gd gk
                          pd pav pu bn g gfs gi cov logstart inodestart nib dev
                          (ientry kk) inum (sl_incnl dn) dn bm c1 Sb1 false None
                          (* pin = true: this site pays the TOKEN arm (§3.9) *)
                          true pid
                          (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
                          S2 (K - 38)%nat eb b lks
                          (upd_upt V P2) ltac:(exact Kiupd) ltac:(discriminate) Hgeom Hist0
                          Hiblk Hiblog Hinb
                          ltac:(exact (sl_setnl_type_stable dn _))
                          ltac:(rewrite /sl_incnl sl_setnl_type; exact Htynz)
                          ltac:(intros od Hc; discriminate Hc)
                          ltac:(intros _; rewrite /sl_incnl sl_setnl_type;
                                exact (sl_tdir_zne _ Hty))
                          ltac:(intros pv Hc; discriminate Hc)
                          ltac:(rewrite /sl_incnl; apply sl_setnl_nlink)
                          Hnl
                          (* ===== THE IIIc WALL, SITE 2 OF 2 -- PAID
                             (RULING A-prime, iclaim-ledger.md §3.9) ==========
                             [SpecIupdate.wp_iupdate_link]'s freeze-pin premise
                             is the two-armed
                               |_di_nlink dn <> 0_| \/ ifreeze_off (…inum),
                             and this walk pays the RIGHT arm with [Hfrz].
                             The LEFT arm is genuinely unavailable here, as
                             IIIc checked on the lane: xv6's sys_link has no
                             [ip->nlink == 0] guard (ARM D is the NLINK_MAX
                             test alone, and ARM E2's zero test is about [dp],
                             after this mint), [InodeLock.inode_ok] carries no
                             [nlink] conjunct, and this walk holds no [ilink]
                             for [ip] -- [namei]'s licence is borrowed and
                             returned at the iget (IgetLic §7.1.6), so
                             [IregLinkNz.ireg_link_nz] has no fragment to read.
                             [Hfrz] is [ip]'s own freeze token, handed over by
                             the [ilock(ip)] at +0x4a: A-custody puts it on the
                             payload's path and [SpecIlock]'s post now surfaces
                             it.  Borrowed -- it comes back below and goes home
                             at the [iunlockput(ip)]. *)
                          ltac:(rewrite /sl_incnl sl_setnl_addrs; exact Haddreq)
                          Hdirlen Hj Hgl HS2a0 Heb (Hlb "log"%string)
                          with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog Hidev Hiinum
                                Hmeta Hmap Hsbi Hireg Hdiat [Hfrz] Hpidq Hprocs
                                Hdev Hgeo Hdlk Hbs2 HopS").
                { rewrite /InodeRegion.ireg_link_pin. iExact "Hfrz". }
                iIntros (CID41 Hq41 miu)
                  "%Hcsiu Hcg Hown Hpc Hpidq Hidev Hiinum Hmeta Hmap Hsbi Hdiat
                   Hilink Hpin Hbs2 HopS".
                (* at [pin = true] the premise that comes back IS the token,
                   by [InodeRegion.ireg_link_pin]'s own definition. *)
                iEval (rewrite /InodeRegion.ireg_link_pin) in "Hpin".
                iRename "Hpin" into "Hfrz".
                assert (Hpc6a : ret_pc (S2 !!! Regidx Rra : mword 64)
                                = mword_of_int (SL + 0x6a)) by (rewrite HS2ra; pcw).
                iEval (rewrite Hpc6a) in "Hpc".
                assert (Hiuregs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) miu)
                  by exact (sl_regs_cs m sp0 _ _ S2 miu Hcsiu HS2regs).
                assert (Hius1 : (miu !!! Regidx Rs1 : mword 64) = ientry kk)
                  by exact (sl_regs_s1 _ _ _ _ _ Hiuregs).
                (* the payload, RE-PARKED at the raised record: [ip] is not a
                   directory ([Hty] refuted it at +0x4c), so its ledger big-op
                   is [emp] whatever the count does. *)
                iAssert (dir_links (bv_unsigned inum) (sl_incnl dn) dat)
                  as "Hdlnk2".
                { iApply (dir_links_not_dir (bv_unsigned inum) (sl_incnl dn) dat).
                  rewrite /sl_incnl sl_setnl_type. exact (sl_tdir_zne _ Hty). }
                iAssert (ity_shot gsh (di_type (sl_incnl dn))) as "#Hshot2".
                { rewrite /sl_incnl sl_setnl_type. iExact "Hshot". }
                (* HOISTED, not spelled inline at the four tail applications:
                   an [ltac:] in argument position at this depth is the
                   recorded budget trap, and all four tails want the same
                   fact -- the [+0x4a] refusal, carried to the [bad:] tails
                   through [Hshot2]'s generation. *)
                assert (Hncd : bv_unsigned (di_type (sl_incnl dn)) <> T_DIR_z)
                  by (rewrite /sl_incnl sl_setnl_type;
                      exact (sl_tdir_zne _ Hty)).
                iAssert (ic_loaded gfs gi cov logstart kk inum (sl_incnl dn) bm)
                  with "[Hdlnk2 Hdiat Hmeta Hmap Hblocks]" as "Hload".
                { rewrite /ic_loaded. iExists dat.
                  iSplitR;
                    [iPureIntro; exact (sl_setnl_inode_ok cov logstart dn bm dat _ Hiok) |].
                  iSplitR;
                    [iPureIntro; exact (sl_setnl_dir_ok icfg_nib dn dat _ Hdok) |].
                  iSplitR;
                    [iPureIntro; apply (dir_dots_ix_not_dir (bv_unsigned inum));
                     rewrite /sl_incnl sl_setnl_type;
                     exact (sl_tdir_zne _ Hty) |].
                  iSplitR;
                    [iPureIntro; apply dir_orphan_clean_not_dir;
                     rewrite /sl_incnl sl_setnl_type;
                     exact (sl_tdir_zne _ Hty) |].
                  iSplitR;
                    [iPureIntro; apply dir_uniq_not_dir;
                     rewrite /sl_incnl sl_setnl_type;
                     exact (sl_tdir_zne _ Hty) |].
                  iSplitL "Hdlnk2"; [iExact "Hdlnk2" |].
                  iFrame "Hdiat Hmeta". rewrite /inode_map.
                  iDestruct "Hmap" as "[Ha Hi]". iFrame "Ha Hi Hblocks". }
                iClear "Hdlnk".
                (* ===== +0x6a c.mv a0,s1 ===== *)
                iApply (wp_cmv_s_sconf (CID := CID41) (mword_of_int (SL + 0x6a))
                          Ra0 Rs1 miu (K - 38)%nat b ltac:(nz) ltac:(rdok)
                          with "Hcg Hpc Hi6a").
                iIntros (CID42 Hq42) "Hcg Hpc".
                set (S3 := <[Regidx Ra0 := regval_into_reg
                              (add_vec zero_reg (miu !!! Regidx Rs1))]> miu).
                assert (HS3a0 : (S3 !!! Regidx Ra0 : mword 64) = ientry kk).
                { etransitivity; [ rewrite /S3; apply upd_eq |].
                  rewrite add_vec_zero_l. exact Hius1. }
                assert (HS3regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) S3)
                  by (rewrite /S3; apply sl_regs_caller;
                      [exact Hcsa0 | exact Hiuregs]).
                assert (Hpp6c : add_vec_int (mword_of_int (SL + 0x6a) : mword 64) 2
                                = mword_of_int (SL + 0x6c)) by pcw.
                iEval (rewrite Hpp6c) in "Hpc".
                (* ===== +0x6c jal ra,iunlock ===== *)
                iApply (wp_jal_s_sconf (CID := CID42) (mword_of_int (SL + 0x6c)) Rra
                          (mword_of_int 2089932 : mword 21) S3 (K - 38)%nat b
                          ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                          with "Hcg Hpc Hi6c").
                iIntros (CID43 Hq43) "Hcg Hpc".
                set (S4 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (SL + 0x6c) : mword 64) 4)]> S3).
                assert (Hjul : add_vec (mword_of_int (SL + 0x6c) : mword 64)
                                 (sign_extend' 64 (mword_of_int 2089932 : mword 21))
                               = mword_of_int KernelSyms.iunlock) by pcw.
                iEval (rewrite Hjul) in "Hpc".
                assert (HS4ra : (S4 !!! Regidx Rra : mword 64)
                                = add_vec_int (mword_of_int (SL + 0x6c) : mword 64) 4)
                  by (rewrite /S4; apply upd_eq).
                assert (HS4a0 : (S4 !!! Regidx Ra0 : mword 64) = ientry kk)
                  by (rewrite /S4 upd_ne; [exact HS3a0 | nz]).
                assert (HS4regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) S4)
                  by (rewrite /S4; apply sl_regs_caller;
                      [exact Hcsra | exact HS3regs]).
                sl_own_transport CID41 CID43 eb pj b.
                iApply (Iunlock.wp_iunlock_sconf (CID := CID43) gs gfs gi cn gil
                          gisl cov logstart kk (qq/2)%Qp gsh dev inum
                          (sl_incnl dn) bm pid (DfracOwn (1/4))
                          S4 (K - 38)%nat eb pj b lks
                          (upd_upt V P2) ltac:(exact Kiu) Hkk HS4a0 (Hlb "sleep lock"%string)
                          with "Hcg Hown Htext Hpc Hitinv Hesck Hslkk
                                Hslkd Hpidq Hprocs Hdep Hidev Hiinum
                                Hivalid Hload Hshot2 Hfrz").
                iIntros (CID44 Hq44 mul) "%Hcsul Hcg Hown Hpc Hpidq Hshr".
                (* THE GENERATION SURVIVES THE WINDOW, and sys_link is the
                   caller that needs it: the share it still holds denies the
                   recycler [live_gen_bump]'s whole unit, so the [ity_shot]
                   minted before this [iunlock] still names the record the
                   [bad:] tail will re-[ilock].  Kept BOUND rather than
                   forgotten -- everything else in the tree forgets here. *)
                assert (Hpc70 : ret_pc (S4 !!! Regidx Rra : mword 64)
                                = mword_of_int (SL + 0x70)) by (rewrite HS4ra; pcw).
                iEval (rewrite Hpc70) in "Hpc".
                assert (Hulregs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) mul)
                  by exact (sl_regs_cs m sp0 _ _ S4 mul Hcsul HS4regs).
                (* ===== +0x70 addi a1,s0,-48 -- &name ===== *)
                iApply (wp_addi4_s_sconf (CID := CID44) (mword_of_int (SL + 0x70))
                          Ra1 Rs0 (mword_of_int 4048 : mword 12) mul (K - 38)%nat b
                          ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi70").
                iIntros (CID45 Hq45) "Hcg Hpc".
                set (T0 := <[Regidx Ra1 := regval_into_reg
                              (add_vec (mul !!! Regidx Rs0)
                                 (sign_extend' 64 (mword_of_int 4048 : mword 12)))]> mul).
                assert (HT0a1 : (T0 !!! Regidx Ra1 : mword 64) = pa_stk sp0 6).
                { etransitivity; [ rewrite /T0; apply upd_eq |].
                  rewrite (sl_regs_s0 _ _ _ _ _ Hulregs). apply sl_bufname. }
                assert (HT0regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) T0)
                  by (rewrite /T0; apply sl_regs_caller;
                      [exact Hcsa1 | exact Hulregs]).
                assert (Hpp74 : add_vec_int (mword_of_int (SL + 0x70) : mword 64) 4
                                = mword_of_int (SL + 0x74)) by pcw.
                iEval (rewrite Hpp74) in "Hpc".
                (* ===== +0x74 addi a0,s0,-176 -- new ===== *)
                iApply (wp_addi4_s_sconf (CID := CID45) (mword_of_int (SL + 0x74))
                          Ra0 Rs0 (mword_of_int 3920 : mword 12) T0 (K - 38)%nat b
                          ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
                iIntros (CID46 Hq46) "Hcg Hpc".
                set (T1 := <[Regidx Ra0 := regval_into_reg
                              (add_vec (T0 !!! Regidx Rs0)
                                 (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> T0).
                assert (HT1a0 : (T1 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22).
                { etransitivity; [ rewrite /T1; apply upd_eq |].
                  rewrite (sl_regs_s0 _ _ _ _ _ HT0regs). apply sl_bufnew. }
                assert (HT1a1 : (T1 !!! Regidx Ra1 : mword 64) = pa_stk sp0 6)
                  by (rewrite /T1 upd_ne; [exact HT0a1 | nz]).
                assert (HT1regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) T1)
                  by (rewrite /T1; apply sl_regs_caller;
                      [exact Hcsa0 | exact HT0regs]).
                assert (Hpp78 : add_vec_int (mword_of_int (SL + 0x74) : mword 64) 4
                                = mword_of_int (SL + 0x78)) by pcw.
                iEval (rewrite Hpp78) in "Hpc".
                (* ===== +0x78 jal ra,nameiparent ===== *)
                iApply (wp_jal_s_sconf (CID := CID46) (mword_of_int (SL + 0x78)) Rra
                          (mword_of_int 2091960 : mword 21) T1 (K - 38)%nat b
                          ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                          with "Hcg Hpc Hi78").
                iIntros (CID47 Hq47) "Hcg Hpc".
                set (T2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (SL + 0x78) : mword 64) 4)]> T1).
                assert (Hjnp : add_vec (mword_of_int (SL + 0x78) : mword 64)
                                 (sign_extend' 64 (mword_of_int 2091960 : mword 21))
                               = mword_of_int KernelSyms.nameiparent) by pcw.
                iEval (rewrite Hjnp) in "Hpc".
                assert (HT2ra : (T2 !!! Regidx Rra : mword 64)
                                = add_vec_int (mword_of_int (SL + 0x78) : mword 64) 4)
                  by (rewrite /T2; apply upd_eq).
                assert (HT2a0 : (T2 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22)
                  by (rewrite /T2 upd_ne; [exact HT1a0 | nz]).
                assert (HT2a1 : (T2 !!! Regidx Ra1 : mword 64) = pa_stk sp0 6)
                  by (rewrite /T2 upd_ne; [exact HT1a1 | nz]).
                assert (HT2regs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) T2)
                  by (rewrite /T2; apply sl_regs_caller;
                      [exact Hcsra | exact HT1regs]).
                iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN") as (bn0) "HbN".
                iDestruct (sl_nm_split (pa_stk sp0 6) bn0 with "HbN")
                  as "[Hnm14 Hnm2]".
                iDestruct (sl_buf_split (pa_stk sp0 22) bw1 pk2 Hpk2 with "HbW")
                  as "[Hbufw Hbufwr]".
                iDestruct (iref_slots_combine 1 1 with "Hir1b Hir1") as "Hir2".
                iDestruct (sl_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
                  [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
                sl_own_transport CID44 CID47 eb pj b.
                iApply (Nameiparent.wp_nameiparent_gen (CID := CID47) gs j gl gu
                          gd gk pd pav pu bn g gfs gi cn gtl γa γf cov logstart
                          bmapstart inodestart nib size dev
                          pk2 bw1 bn0 c1 (Sb1 ∪ {[IBLOCK inum inodestart]})
                          pid (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
                          T2 (K - 38)%nat eb b lks (upd_upt V P2)
                          ltac:(exact Knp) Hcdev Hcnib Hclog Hcist HdevR Hnib0
                          Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb
                          Hpcstr2 (sl_plen_lt pk2 Hpk2)
                          ltac:(exact (sl_walk2_need _ w1 c1 Hu2)) Hj Hgl
                          with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hkenv Hitab
                                Hitinv Hescrows Hslks Hireg Hropen Hprocs Hdev Hgeo Hdlk
                                Hsbb Hsbi Hbmres Hpidq Hcwdref [Hbufw]
                                [Hnm14] Hbsl Hir2 HopS").
                (* nameiparent is eb-generic now; sys_link is at [eb = true]. *)
                { rewrite Heb /trap_csrs_ext. done. }
                { rewrite Heb /cpu_claim_ext. done. }
                { iEval (rewrite HT2a0). iExact "Hbufw". }
                { iEval (rewrite HT2a1). iExact "Hnm14". }
                iIntros (CID48 Hq48 mnp n2 Sb2 ok2 nf dpv w2)
                  "%Hcsnp Hcg Hown _ _ Hpc Hsbb Hsbi Hpidq
                   Hcwdref Hbufw Hnm14 Hbsl %HSb2 %Hw2 %Hn2 HopS Hres2".
                iEval (rewrite HT2a0) in "Hbufw".
                iEval (rewrite HT2a1) in "Hnm14".
                assert (Hpc7c : ret_pc (T2 !!! Regidx Rra : mword 64)
                                = mword_of_int (SL + 0x7c)) by (rewrite HT2ra; pcw).
                iEval (rewrite Hpc7c) in "Hpc".
                assert (Hnpregs : sl_regs m sp0 (ientry kk)
                                    (m !!! Regidx Rs2 : mword 64) mnp)
                  by exact (sl_regs_cs m sp0 _ _ T2 mnp Hcsnp HT2regs).
                assert (Hmem2 : IBLOCK inum inodestart
                                ∈ (Sb1 ∪ {[IBLOCK inum inodestart]}))
                  by (apply elem_of_union_r, elem_of_singleton; reflexivity).
                assert (Hmem2' : IBLOCK inum inodestart ∈ Sb2)
                  by exact (HSb2 _ Hmem2).
                (* ===== +0x7c c.mv s2,a0 ===== *)
                iApply (wp_cmv_s_sconf (CID := CID48) (mword_of_int (SL + 0x7c))
                          Rs2 Ra0 mnp (K - 38)%nat b ltac:(nz) ltac:(rdok)
                          with "Hcg Hpc Hi7c").
                iIntros (CID49 Hq49) "Hcg Hpc".
                set (T3 := <[Regidx Rs2 := regval_into_reg
                              (add_vec zero_reg (mnp !!! Regidx Ra0))]> mnp).
                assert (HT3a0 : (T3 !!! Regidx Ra0 : mword 64)
                                = (mnp !!! Regidx Ra0 : mword 64))
                  by (rewrite /T3 upd_ne; [reflexivity | nz]).
                assert (HT3regs : sl_regs m sp0 (ientry kk)
                                    (mnp !!! Regidx Ra0 : mword 64) T3).
                { rewrite /T3.
                  exact (sl_regs_wr_s2 m sp0 _ _ _ mnp _ (add_vec_zero_l _) Hnpregs). }
                assert (Hpp7e : add_vec_int (mword_of_int (SL + 0x7c) : mword 64) 2
                                = mword_of_int (SL + 0x7e)) by pcw.
                iEval (rewrite Hpp7e) in "Hpc".
                assert (Htgf4 : add_vec (mword_of_int (SL + 0x7e) : mword 64)
                          (sign_extend' 64
                             (sign_extend' 13
                                (concat_vec (mword_of_int 59 : mword 8) ('b"0"))))
                          = mword_of_int (SL + 0xf4)) by pcw.
                (* ===== +0x7e c.beqz a0 -> ARM E ===== *)
                destruct ok2.
                ** (* ---------- the parent RESOLVED ---------- *)
                   iDestruct "Hres2" as "(%Hnpe & Hhelddp & Hir1c)".
                   iDestruct "Hhelddp" as (kd qd dinum gyd)
                     "(%Hdpe & %Hkd & %Hdinumc & Hrefdp & #Hshotd & Hrud)".
                   assert (Hdpnz : dpv <> (zero_reg : mword 64))
                     by (rewrite Hdpe; apply ientry_ne_zero; lia).
                   assert (Hu3 : (sl_u3 w1 w2 <= n2)%nat)
                     by exact (sl_cnt_u3 w1 w2 c1 n2 Hu2 (proj1 Hn2)).
                   rewrite (proj1 Hnpe) Hdpe in HT3regs.
                   iApply (wp_cbeqz_fall_s_sconf (CID := CID49)
                             (mword_of_int (SL + 0x7e)) (mword_of_int 59 : mword 8)
                             (Cregidx (mword_of_int 2)) Ra0 T3 (K - 38)%nat b
                             ltac:(vm_compute; reflexivity) ltac:(nz)
                             ltac:(rgne; rewrite HT3a0 (proj1 Hnpe);
                                   apply (proj2 (eq_vec_false_iff _ _));
                                   exact Hdpnz)
                             with "Hcg Hpc Hi7e").
                   iIntros (CID50 Hq50) "Hcg Hpc".
                   assert (Hpp80 : add_vec_int (mword_of_int (SL + 0x7e) : mword 64) 2
                                   = mword_of_int (SL + 0x80)) by pcw.
                   iEval (rewrite Hpp80) in "Hpc".
                   (* dp's reference, shed at the SAME generation the type
                      one-shot names -- which is what lets [ity_shot_agree]
                      turn nameiparent's [inode_held_ty] into
                      [di_type dnd = T_DIR] at ilock's own record. *)
                   iEval (rewrite sl_shed_gen) in "Hrefdp".
                   iDestruct "Hrefdp" as "[Hkeepd Hshrd]".
                   iEval (rewrite -Hcdev) in "Hkeepd".
                   iEval (rewrite -Hcdev) in "Hshrd".
                   iDestruct (inode_ref_short_gen_forget with "Hkeepd") as "Hkeepd".
                   assert (Hdinb : bv_unsigned dinum < 16 * Z.of_nat nib)
                     by (rewrite Hcnib; exact Hdinumc).
                   destruct (Hiregb dinum Hdinb) as [Hdiblk Hdiblog].
                   iDestruct (sl_esc_acc cn gfs gi cov logstart kd Hkd
                                with "Hescrows") as "#Hescd".
                   iDestruct (sl_slk_acc cn kd Hkd with "Hslks")
                     as (gild gisld) "#Hslkd0".
                   iDestruct (sl_bs3 bn with "Hbsl") as "[Hbs1d Hbs2d]".
                   iClear "Hi5c Hi5e Hi60 Hi64 Hi66 Hi6a Hi6c Hi70 Hi74 Hi78
                           Hi7c Hi7e".
                   iPoseProof (slki_80 with "Htext") as "Hi80".
                   iPoseProof (slki_84 with "Htext") as "Hi84".
                   iPoseProof (slki_88 with "Htext") as "Hi88".
                   iPoseProof (slki_8a with "Htext") as "Hi8a".
                   iPoseProof (slki_8c with "Htext") as "Hi8c".
                   iPoseProof (slki_90 with "Htext") as "Hi90".
                   iPoseProof (slki_92 with "Htext") as "Hi92".
                   iPoseProof (slki_96 with "Htext") as "Hi96".
                   iPoseProof (slki_98 with "Htext") as "Hi98".
                   iPoseProof (slki_9c with "Htext") as "Hi9c".
                   iPoseProof (slki_a0 with "Htext") as "Hia0".
                   iPoseProof (slki_a4 with "Htext") as "Hia4".
                   iPoseProof (slki_a6 with "Htext") as "Hia6".
                   iPoseProof (slki_aa with "Htext") as "Hiaa".
                   iPoseProof (slki_ac with "Htext") as "Hiac".
                   iPoseProof (slki_b0 with "Htext") as "Hib0".
                   iPoseProof (slki_b4 with "Htext") as "Hib4".
                   iPoseProof (slki_b6 with "Htext") as "Hib6".
                   iPoseProof (slki_b8 with "Htext") as "Hib8".
                   iPoseProof (slki_ba with "Htext") as "Hiba".
                   assert (Htgee_92 : add_vec (mword_of_int (SL + 0x92) : mword 64)
                             (sign_extend' 64 (mword_of_int 92 : mword 13))
                             = mword_of_int (SL + 0xee)) by pcw.
                   assert (Htgee_a0 : add_vec (mword_of_int (SL + 0xa0) : mword 64)
                             (sign_extend' 64 (mword_of_int 78 : mword 13))
                             = mword_of_int (SL + 0xee)) by pcw.
                   assert (Htg11aba : add_vec (mword_of_int (SL + 0xba) : mword 64)
                             (sign_extend' 64
                                (sign_extend' 21
                                   (concat_vec (mword_of_int 48 : mword 11) ('b"0"))))
                             = mword_of_int (SL + 0x11a)) by pcw.
                   assert (HT3a0d : (T3 !!! Regidx Ra0 : mword 64) = ientry kd)
                     by (rewrite HT3a0 (proj1 Hnpe); exact Hdpe).
                   assert (HT3s2d : (T3 !!! Regidx Rs2 : mword 64) = ientry kd)
                     by exact (sl_regs_s2 _ _ _ _ _ HT3regs).
                   (* ===== +0x80 jal ra,ilock ===== *)
                   iApply (wp_jal_s_sconf (CID := CID50) (mword_of_int (SL + 0x80))
                             Rra (mword_of_int 2089738 : mword 21) T3 (K - 38)%nat b
                             ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                             with "Hcg Hpc Hi80").
                   iIntros (CID51 Hq51) "Hcg Hpc".
                   set (U0 := <[Regidx Rra := regval_into_reg
                                 (add_vec_int (mword_of_int (SL + 0x80) : mword 64) 4)]> T3).
                   assert (Hjild : add_vec (mword_of_int (SL + 0x80) : mword 64)
                                     (sign_extend' 64 (mword_of_int 2089738 : mword 21))
                                   = mword_of_int KernelSyms.ilock) by pcw.
                   iEval (rewrite Hjild) in "Hpc".
                   assert (HU0ra : (U0 !!! Regidx Rra : mword 64)
                                   = add_vec_int (mword_of_int (SL + 0x80) : mword 64) 4)
                     by (rewrite /U0; apply upd_eq).
                   assert (HU0a0 : (U0 !!! Regidx Ra0 : mword 64) = ientry kd)
                     by (rewrite /U0 upd_ne; [exact HT3a0d | nz]).
                   assert (HU0regs : sl_regs m sp0 (ientry kk) (ientry kd) U0)
                     by (rewrite /U0; apply sl_regs_caller;
                         [exact Hcsra | exact HT3regs]).
                   sl_own_transport CID48 CID51 eb pj b.
                   iApply (Ilock.wp_ilock_sconf (CID := CID51) gs j gl gu gd gk pd
                             pav pu bn gfs gi cn gild gisld cov logstart inodestart
                             nib kd (qd/2)%Qp gyd PlainK dev dinum pid
                             (DfracOwn (1/4)) dqs
                             U0 (K - 38)%nat eb b lks
                             (upd_upt V P2) ltac:(exact Kil) Hkd Hgeom Hist0 Hdiblk Hdinb Hj Hgl
                             HU0a0 (Hlb "bcache"%string)
                             with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hitinv
                                   Hescd Hireg Hslkd0 Hshrd Hrud Hsbi Hpidq Hprocs
                                   Hdev Hgeo Hdlk Hbs1d").
                   { rewrite Heb /trap_csrs_ext. done. }
                   { rewrite Heb /cpu_claim_ext. done. }
                   iIntros (CID52 Hq52 mild dnd bmd fld)
                     "%Hcsild Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1d Hslkdd
                      Hdepd Hidevd Hiinumd Hivalidd Hloadd #Hshotd2 Hfrzd
                      %Hfld Hrud %Hilkpd".
                   (* ilock's RETURN ADDRESS IS +0x84, NOT +0x8a.  The
                      relayout maps offsets by where the OLD instruction
                      went, and old +0x84 (the [c.mv a0,s2]) went to +0x8a --
                      but this assertion is not about that instruction, it is
                      about "the four bytes after the [jal] at +0x80", and
                      what sits there now is the guard's [lh]. *)
                   assert (Hpc84 : ret_pc (U0 !!! Regidx Rra : mword 64)
                                   = mword_of_int (SL + 0x84)) by (rewrite HU0ra; pcw).
                   iEval (rewrite Hpc84) in "Hpc".
                   assert (Hildregs : sl_regs m sp0 (ientry kk) (ientry kd) mild)
                     by exact (sl_regs_cs m sp0 _ _ U0 mild Hcsild HU0regs).
                   assert (Hilds1 : (mild !!! Regidx Rs1 : mword 64) = ientry kk)
                     by exact (sl_regs_s1 _ _ _ _ _ Hildregs).
                   assert (Hilds2 : (mild !!! Regidx Rs2 : mword 64) = ientry kd)
                     by exact (sl_regs_s2 _ _ _ _ _ Hildregs).
                   iDestruct (ity_shot_agree with "Hshotd Hshotd2") as %Htyd0.
                   assert (Htyd : di_type dnd = SpecDirlookup.T_DIR)
                     by (symmetry; exact Htyd0).
                   iDestruct "Hloadd" as (datd)
                     "(%Hdiok & %Hddok & %Hddixd & %Hdocd & %Hduqd & Hdlnkd & Hdiatd &
                       Hmetad & Haddrsd & Hindd & Hblocksd)".
                   (* ============================================================ *)
                   (*  THE ORPHAN GUARD, +0x84 .. +0x88 (xv6 f60ff58).              *)
                   (*                                                              *)
                   (*  nameiparent hands the parent back UNLOCKED, so a concurrent  *)
                   (*  rmdir can zero its link count in the window before this      *)
                   (*  [ilock(dp)]; a [dirlink] into an orphan then appends a        *)
                   (*  record that the parent's own [itrunc] later discards WITHOUT  *)
                   (*  dropping [ip->nlink], stranding this walk's [ilink] forever.  *)
                   (*  create has re-checked for exactly that since 9da28f5; this is *)
                   (*  the same guard, given to sys_link, and it is what makes       *)
                   (*  fs-fragments-campaign.md's STRONG isdirempty invariant true   *)
                   (*  of the binary instead of refuted by it.                       *)
                   (*                                                              *)
                   (*  IT IS NOT A DIAMOND, and that is the difference from create's *)
                   (*  own.  create's guard has the NLINK_MAX gate below it and the  *)
                   (*  two rejoin at +0x3e, so the tail had to be handed to both     *)
                   (*  arms through an [∧] of two [wp_next]-wrapped continuations.   *)
                   (*  Here the taken arm LEAVES -- it is a [bad:] route and never   *)
                   (*  comes back -- so the ordinary [destruct (decide ...)] is the   *)
                   (*  whole of it and the 900 lines below are untouched.            *)
                   (* ============================================================ *)
                   iDestruct "Hmetad" as "(Hityd & Himajd & Himind & Hinld & Hiszd)".
                   iEval (rewrite /i_nlink) in "Hinld".
                   (* ===== +0x84 lh a5,74(s2) : dp->nlink ===== *)
                   iApply (wp_lh_s_sconf (CID := CID52) (kt := KT1) (ktd := KT0) (mword_of_int (SL + 0x84))
                             Ra5 Rs2 (mword_of_int 74 : mword 12) mild
                             (K - 38)%nat (di_nlink dnd : mword 16) b
                             ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84 [Hinld]").
                   { iEval (rgne; rewrite Hilds2). iExact "Hinld". }
                   iIntros (CIDg0 Hqg0) "Hcg Hpc Hinld".
                   iEval (rgne; rewrite Hilds2) in "Hinld".
                   set (Ug := <[Regidx Ra5 := regval_into_reg
                                 (sign_extend' 64 (di_nlink dnd : mword 16)
                                  : mword 64)]> mild).
                   assert (HUga5 : (Ug !!! Regidx Ra5 : mword 64)
                                   = (sign_extend' 64 (di_nlink dnd : mword 16)
                                      : mword 64))
                     by (rewrite /Ug; apply upd_eq).
                   assert (HUgregs : sl_regs m sp0 (ientry kk) (ientry kd) Ug)
                     by (rewrite /Ug; apply sl_regs_caller;
                         [exact Hcsa5 | exact Hildregs]).
                   assert (HUgs1 : (Ug !!! Regidx Rs1 : mword 64) = ientry kk)
                     by exact (sl_regs_s1 _ _ _ _ _ HUgregs).
                   assert (HUgs2 : (Ug !!! Regidx Rs2 : mword 64) = ientry kd)
                     by exact (sl_regs_s2 _ _ _ _ _ HUgregs).
                   assert (Hpp88 : add_vec_int (mword_of_int (SL + 0x84) : mword 64) 4
                                   = mword_of_int (SL + 0x88)) by pcw.
                   iEval (rewrite Hpp88) in "Hpc".
                   assert (Htge6_88 : add_vec (mword_of_int (SL + 0x88) : mword 64)
                             (sign_extend' 64 (sign_extend' 13
                                (concat_vec (mword_of_int 47 : mword 8) ('b"0"))))
                             = mword_of_int (SL + 0xe6)) by pcw.
                   iAssert (inode_meta (ientry kd) dnd)
                     with "[Hityd Himajd Himind Hinld Hiszd]" as "Hmetad".
                   { rewrite /inode_meta /i_nlink. iFrame. }
                   destruct (decide (di_nlink dnd = (mword_of_int 0 : mword 16)))
                     as [Hdnl0 | Hdnl0].
                   { (* ===== ARM E2: THE PARENT IS ORPHANED -- goto bad ===== *)
                     iApply (wp_cbeqz_taken_s_sconf (CID := CIDg0)
                               (mword_of_int (SL + 0x88)) (mword_of_int 47 : mword 8)
                               (Cregidx (mword_of_int 7)) Ra5 Ug (K - 38)%nat b
                               ltac:(vm_compute; reflexivity) ltac:(nz)
                               ltac:(rgne; rewrite HUga5; exact (sl_nlz_eq _ Hdnl0))
                               ltac:(rewrite Htge6_88; vm_compute; reflexivity)
                               with "Hcg Hpc Hi88").
                     iIntros (CIDg1 Hqg1). iNext. iIntros "Hcg Hpc".
                     iEval (rewrite Htge6_88) in "Hpc".
                     (* the parent's record, handed back whole: the guard READ
                        the halfword and wrote nothing. *)
                     iDestruct (ic_mk_loaded gfs gi cov logstart kd dinum dnd bmd
                                  datd Hdiok Hddok Hddixd Hdocd Hduqd
                                  with "Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd")
                       as "Hloadd".
                     iDestruct (sl_bs3 bn with "[Hbs1d Hbs2d]") as "Hbsl";
                       [iSplitL "Hbs1d"; [iExact "Hbs1d" | iExact "Hbs2d"] |].
                     (* the three buffers, rejoined for the epilogue *)
                     iDestruct (sl_buf_join (pa_stk sp0 22) bw1 pk2 Hpk2
                                  with "Hbufw Hbufwr") as "HbW".
                     iDestruct (sl_bytes_name (pa_stk sp0 22) 128 with "HbW")
                       as (bw2) "HbW".
                     iDestruct (sl_nm_join (pa_stk sp0 6) bn0 nf
                                  with "Hnm14 Hnm2") as "HbN".
                     iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN")
                       as (bn1) "HbN".
                     iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                                  with "Hbufk Hbufrest") as "HbO".
                     iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO")
                       as (bo2) "HbO".
                     (* the generation is ALREADY in hand: [iunlock] hands [gsh] back
                        (SpecIunlock's amended post), so the tail re-[ilock]s under the
                        very generation the [ity_shot] above names. *)
                     iDestruct (log_opS_named with "HopS") as (e0) "HopE".
                     iDestruct (wp_next_shift (b := true) (CIDa := CID0)
                                  (CIDb := CIDg1) ltac:(wp_next_chain)
                                  with "Hcont") as "Hcont".
                     sl_own_transport CID52 CIDg1 eb pj b.
                     iApply (Tails.sl_tail_e2 (CID0 := CIDg1) gs j gl gu gd gk pd
                               pav pu bn g gfs gi cn gtl gil gisl gild gisld cov
                               logstart bmapstart inodestart nib size dev
                               kk (qq/2)%Qp (qq/2)%Qp gsh inum
                               (di_type (sl_incnl dn))
                               kd (qd/2)%Qp (qd/2)%Qp gyd dinum dnd bmd
                               n2 Sb2 e0 pid (DfracOwn (1/4)) dqb dqs
                               m Ug sp0 K eb b lks bn1 bw2 bo2
                               (upd_upt V P2) ltac:(exact Kil) ltac:(exact Kiupd)
                               ltac:(exact Kiup) ltac:(exact Keo) K38 Kpop
                               Hkk Hkd Hclog Hcist Hgeom Hsize Hbm0 Hbmcov
                               Hbmlog Hist0 Hiblk Hiblog Hinb
                               Hdiblk Hdiblog
                               Hdinb Hcovb Hmem2'
                               ltac:(exact (sl_orphan_entry w1 w2 n2 Hu3))
                               ltac:(exact (fun w n' Hn' =>
                                       sl_orphan_close w1 w2 w n2 n' Hu3 Hn'))
                               Hj Hgl Hlkempty Heb ltac:(reflexivity)
                               (sl_regs_sp _ _ _ _ _ HUgregs)
                               (sl_regs_thr _ _ _ _ _ HUgregs) HUgs1 HUgs2 Hal
                               Hncd
                               with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog Hseam
                                     Hgen Hitab Hitinv Hesck Hescd Hireg Hropen Hslkk
                                     Hslkd0 Hkeep Hru Hshr Hshot2 Hilink Hslkdd
                                     Hdepd Hidevd Hiinumd Hivalidd Hloadd Hshotd2
                                     Hfrzd Hkeepd Hrud Hsbb Hsbi Hbmres Hpidq Hprocs Hdev
                                     Hgeo Hdlk Hbsl HopE Hf1 Hf2 Hf3 Hf4
                                     HbN HbW HbO
                                     [Hsbs Hir1c Hcwdref Hofiles Hftok Hcont]").
                     iEval (rewrite /wp_next).
                     iIntros (CIDy) "%Hqy". iIntros (mf)
                       "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpidq Hsbb
                        Hsbi Hbsl Hislots".
                     iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
                     iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
                     iCombine "Hpidq Hofiles" as "Hpnc".
                     iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
                     iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                                  with "[Hpnc Href Hftok]") as "Hpriv";
                       [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
                     iDestruct (iref_slots_combine 1 2 with "Hir1c Hislots") as "Hir".
                     iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown Htce
                               Hcce Hpc Hbsl Hsbb Hsbi Hsbs Hir Hpriv [%]").
                     { exact Hcsf. }
                     { exact Hupt. }
                     { left. rewrite Ha0f. reflexivity. } }
                   (* ===== +0x88 c.beqz a5 FALLS THROUGH: the parent is live ===== *)
                   iApply (wp_cbeqz_fall_s_sconf (CID := CIDg0)
                             (mword_of_int (SL + 0x88)) (mword_of_int 47 : mword 8)
                             (Cregidx (mword_of_int 7)) Ra5 Ug (K - 38)%nat b
                             ltac:(vm_compute; reflexivity) ltac:(nz)
                             ltac:(rgne; rewrite HUga5; exact (sl_nlz_ne _ Hdnl0))
                             with "Hcg Hpc Hi88").
                   iIntros (CIDg1 Hqg1) "Hcg Hpc".
                   assert (Hpp8a : add_vec_int (mword_of_int (SL + 0x88) : mword 64) 2
                                   = mword_of_int (SL + 0x8a)) by pcw.
                   iEval (rewrite Hpp8a) in "Hpc".
                   (* ===== +0x8a c.mv a0,s2 ===== *)
                   iApply (wp_cmv_s_sconf (CID := CIDg1) (mword_of_int (SL + 0x8a))
                             Ra0 Rs2 Ug (K - 38)%nat b ltac:(nz) ltac:(rdok)
                             with "Hcg Hpc Hi8a").
                   iIntros (CID53 Hq53) "Hcg Hpc".
                   set (U1 := <[Regidx Ra0 := regval_into_reg
                                 (add_vec zero_reg (Ug !!! Regidx Rs2))]> Ug).
                   assert (HU1a0 : (U1 !!! Regidx Ra0 : mword 64) = ientry kd).
                   { etransitivity; [ rewrite /U1; apply upd_eq |].
                     rewrite add_vec_zero_l. exact HUgs2. }
                   assert (HU1regs : sl_regs m sp0 (ientry kk) (ientry kd) U1)
                     by (rewrite /U1; apply sl_regs_caller;
                         [exact Hcsa0 | exact HUgregs]).
                   assert (HU1s1 : (U1 !!! Regidx Rs1 : mword 64) = ientry kk)
                     by exact (sl_regs_s1 _ _ _ _ _ HU1regs).
                   assert (HU1s2 : (U1 !!! Regidx Rs2 : mword 64) = ientry kd)
                     by exact (sl_regs_s2 _ _ _ _ _ HU1regs).
                   assert (Hpp8c : add_vec_int (mword_of_int (SL + 0x8a) : mword 64) 2
                                   = mword_of_int (SL + 0x8c)) by pcw.
                   iEval (rewrite Hpp8c) in "Hpc".
                   (* ===== +0x8c lw a4,0(s2) -- dp->dev ===== *)
                   iEval (rewrite /i_dev) in "Hidevd".
                   iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (CID := CID53) (mword_of_int (SL + 0x8c))
                             Ra4 Rs2 (mword_of_int 0 : mword 12) U1 (K - 38)%nat
                             dev b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c [Hidevd]").
                   { iEval (rgne; rewrite HU1s2). iExact "Hidevd". }
                   iIntros (CID54 Hq54) "Hcg Hpc Hidevd".
                   iEval (rgne; rewrite HU1s2) in "Hidevd".
                   set (U2 := <[Regidx Ra4 := regval_into_reg
                                 (sign_extend' 64 dev : mword 64)]> U1).
                   assert (HU2a4 : (U2 !!! Regidx Ra4 : mword 64)
                                   = (sign_extend' 64 dev : mword 64))
                     by (rewrite /U2; apply upd_eq).
                   assert (HU2regs : sl_regs m sp0 (ientry kk) (ientry kd) U2)
                     by (rewrite /U2; apply sl_regs_caller;
                         [exact Hcsa4 | exact HU1regs]).
                   assert (HU2a0 : (U2 !!! Regidx Ra0 : mword 64) = ientry kd)
                     by (rewrite /U2 upd_ne; [exact HU1a0 | nz]).
                   assert (HU2s1 : (U2 !!! Regidx Rs1 : mword 64) = ientry kk)
                     by exact (sl_regs_s1 _ _ _ _ _ HU2regs).
                   assert (Hpp90 : add_vec_int (mword_of_int (SL + 0x8c) : mword 64) 4
                                   = mword_of_int (SL + 0x90)) by pcw.
                   iEval (rewrite Hpp90) in "Hpc".
                   (* ===== +0x90 c.lw a5,0(s1) -- ip->dev, READ OFF THE
                      REFERENCE: ip is UNLOCKED here and needs no lock for it. *)
                   iEval (rewrite /inode_ref_short /inode_ident /i_dev /i_inum)
                     in "Hkeep".
                   (* [inode_ref_short] carries the sleeplock share on the
                      SLICE since GR-25, so the flattened shape is
                      [iref_frag ∗ live_frac ∗ (i_dev ∗ i_inum) ∗ slh_tok]:
                      the identity pair needs its own bracket, and the share
                      rides along to the reassembly at +0xa0 below. *)
                   iDestruct "Hkeep"
                     as "(Hkfrag & Hklive & (Hipdev & Hipinum) & Hkshare)".
                   iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (CID := CID54) (mword_of_int (SL + 0x90))
                             Ra5 Rs1 (mword_of_int 0 : mword 12) U2 (K - 38)%nat
                             dev b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90 [Hipdev]").
                   { iEval (rgne; rewrite HU2s1). iExact "Hipdev". }
                   iIntros (CID55 Hq55) "Hcg Hpc Hipdev".
                   iEval (rgne; rewrite HU2s1) in "Hipdev".
                   set (U3 := <[Regidx Ra5 := regval_into_reg
                                 (sign_extend' 64 dev : mword 64)]> U2).
                   assert (HU3a5 : (U3 !!! Regidx Ra5 : mword 64)
                                   = (sign_extend' 64 dev : mword 64))
                     by (rewrite /U3; apply upd_eq).
                   assert (HU3a4 : (U3 !!! Regidx Ra4 : mword 64)
                                   = (sign_extend' 64 dev : mword 64))
                     by (rewrite /U3 upd_ne; [exact HU2a4 | nz]).
                   assert (HU3regs : sl_regs m sp0 (ientry kk) (ientry kd) U3)
                     by (rewrite /U3; apply sl_regs_caller;
                         [exact Hcsa5 | exact HU2regs]).
                   assert (HU3a0 : (U3 !!! Regidx Ra0 : mword 64) = ientry kd)
                     by (rewrite /U3 upd_ne; [exact HU2a0 | nz]).
                   assert (HU3s1 : (U3 !!! Regidx Rs1 : mword 64) = ientry kk)
                     by exact (sl_regs_s1 _ _ _ _ _ HU3regs).
                   assert (Hpp92 : add_vec_int (mword_of_int (SL + 0x90) : mword 64) 2
                                   = mword_of_int (SL + 0x92)) by pcw.
                   iEval (rewrite Hpp92) in "Hpc".
                   (* ===== +0x92 bne a4,a5 -- REFUTED: ONE DEVICE ===== *)
                   iApply (wp_bne_fall_s_sconf (CID := CID55)
                             (mword_of_int (SL + 0x92)) (mword_of_int 92 : mword 13)
                             Ra5 Ra4 U3 (K - 38)%nat b ltac:(nz) ltac:(nz)
                             ltac:(rgne; rgne; rewrite HU3a4 HU3a5;
                                   apply sl_neq_refl)
                             with "Hcg Hpc Hi92").
                   iIntros (CID56 Hq56) "Hcg Hpc".
                   assert (Hpp96 : add_vec_int (mword_of_int (SL + 0x92) : mword 64) 4
                                   = mword_of_int (SL + 0x96)) by pcw.
                   iEval (rewrite Hpp96) in "Hpc".
                   (* ===== +0x96 c.lw a2,4(s1) -- ip->inum ===== *)
                   iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (CID := CID56) (mword_of_int (SL + 0x96))
                             Ra2 Rs1 (mword_of_int 4 : mword 12) U3 (K - 38)%nat
                             inum b ltac:(nz) ltac:(rdok)
                             with "Hcg Hpc Hi96 [Hipinum]").
                   { iEval (rgne; rewrite HU3s1). iExact "Hipinum". }
                   iIntros (CID57 Hq57) "Hcg Hpc Hipinum".
                   iEval (rgne; rewrite HU3s1) in "Hipinum".
                   set (U4 := <[Regidx Ra2 := regval_into_reg
                                 (sign_extend' 64 inum : mword 64)]> U3).
                   assert (HU4a2 : (U4 !!! Regidx Ra2 : mword 64)
                                   = (zero_extend' 64 (sl_low16 inum) : mword 64)).
                   { rewrite /U4 upd_eq. apply sl_a2_low16.
                     assert (E16 : (2 ^ 16 = 65536)%Z) by (vm_compute; reflexivity).
                     lia. }
                   assert (HU4a0 : (U4 !!! Regidx Ra0 : mword 64) = ientry kd)
                     by (rewrite /U4 upd_ne; [exact HU3a0 | nz]).
                   assert (HU4regs : sl_regs m sp0 (ientry kk) (ientry kd) U4)
                     by (rewrite /U4; apply sl_regs_caller;
                         [exact Hcsa2 | exact HU3regs]).
                   assert (Hpp98 : add_vec_int (mword_of_int (SL + 0x96) : mword 64) 2
                                   = mword_of_int (SL + 0x98)) by pcw.
                   iEval (rewrite Hpp98) in "Hpc".
                   (* ===== +0x98 addi a1,s0,-48 ===== *)
                   iApply (wp_addi4_s_sconf (CID := CID57) (mword_of_int (SL + 0x98))
                             Ra1 Rs0 (mword_of_int 4048 : mword 12) U4 (K - 38)%nat b
                             ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi98").
                   iIntros (CID58 Hq58) "Hcg Hpc".
                   set (U5 := <[Regidx Ra1 := regval_into_reg
                                 (add_vec (U4 !!! Regidx Rs0)
                                    (sign_extend' 64 (mword_of_int 4048 : mword 12)))]> U4).
                   assert (HU5a1 : (U5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 6).
                   { etransitivity; [ rewrite /U5; apply upd_eq |].
                     rewrite (sl_regs_s0 _ _ _ _ _ HU4regs). apply sl_bufname. }
                   assert (HU5a0 : (U5 !!! Regidx Ra0 : mword 64) = ientry kd)
                     by (rewrite /U5 upd_ne; [exact HU4a0 | nz]).
                   assert (HU5a2 : (U5 !!! Regidx Ra2 : mword 64)
                                   = (zero_extend' 64 (sl_low16 inum) : mword 64))
                     by (rewrite /U5 upd_ne; [exact HU4a2 | nz]).
                   assert (HU5regs : sl_regs m sp0 (ientry kk) (ientry kd) U5)
                     by (rewrite /U5; apply sl_regs_caller;
                         [exact Hcsa1 | exact HU4regs]).
                   assert (Hpp9c : add_vec_int (mword_of_int (SL + 0x98) : mword 64) 4
                                   = mword_of_int (SL + 0x9c)) by pcw.
                   iEval (rewrite Hpp9c) in "Hpc".
                   (* ===== +0x9c jal ra,dirlink ===== *)
                   iApply (wp_jal_s_sconf (CID := CID58) (mword_of_int (SL + 0x9c))
                             Rra (mword_of_int 2091728 : mword 21) U5 (K - 38)%nat b
                             ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                             with "Hcg Hpc Hi9c").
                   iIntros (CID59 Hq59) "Hcg Hpc".
                   set (U6 := <[Regidx Rra := regval_into_reg
                                 (add_vec_int (mword_of_int (SL + 0x9c) : mword 64) 4)]> U5).
                   assert (Hjdl : add_vec (mword_of_int (SL + 0x9c) : mword 64)
                                    (sign_extend' 64 (mword_of_int 2091728 : mword 21))
                                  = mword_of_int KernelSyms.dirlink) by pcw.
                   iEval (rewrite Hjdl) in "Hpc".
                   assert (HU6ra : (U6 !!! Regidx Rra : mword 64)
                                   = add_vec_int (mword_of_int (SL + 0x9c) : mword 64) 4)
                     by (rewrite /U6; apply upd_eq).
                   assert (HU6a0 : (U6 !!! Regidx Ra0 : mword 64) = ientry kd)
                     by (rewrite /U6 upd_ne; [exact HU5a0 | nz]).
                   assert (HU6a1 : (U6 !!! Regidx Ra1 : mword 64) = pa_stk sp0 6)
                     by (rewrite /U6 upd_ne; [exact HU5a1 | nz]).
                   assert (HU6a2 : (U6 !!! Regidx Ra2 : mword 64)
                                   = (zero_extend' 64 (sl_low16 inum) : mword 64))
                     by (rewrite /U6 upd_ne; [exact HU5a2 | nz]).
                   assert (HU6regs : sl_regs m sp0 (ientry kk) (ientry kd) U6)
                     by (rewrite /U6; apply sl_regs_caller;
                         [exact Hcsra | exact HU5regs]).
                   iDestruct (sl_bs3 bn with "[Hbs1d Hbs2d]") as "Hbsl";
                     [iSplitL "Hbs1d"; [iExact "Hbs1d" | iExact "Hbs2d"] |].
                   iAssert (inode_map gfs (ientry kd) bmd)
                     with "[Haddrsd Hindd]" as "Hmapd".
                   { rewrite /inode_map. iFrame. }
                   (* the entry claims, and the correlation clause as a
                      walk-level fact: a call that PAID reports the block. *)
                   assert (Hcrok2 : sl_crok (bool_decide (bmapstart ∈ Sb2)) w1 w2).
                   { intro Hf. apply bool_decide_eq_false in Hf. split.
                     - destruct w1; [| reflexivity]. exfalso. apply Hf.
                       apply HSb2. apply elem_of_union_l. exact (Hw1 eq_refl).
                     - destruct w2; [| reflexivity]. exfalso. apply Hf.
                       exact (Hw2 eq_refl). }
                   assert (Hlow16 : bv_unsigned (sl_low16 inum) < 16 * Z.of_nat nib).
                   { rewrite sl_low16_unsigned; [exact Hinb |].
                     assert (E16 : (2 ^ 16 = 65536)%Z) by (vm_compute; reflexivity).
                     lia. }
                   assert (Hlow16i : bv_unsigned (sl_low16 inum)
                                     < 16 * Z.of_nat icfg_nib)
                     by (rewrite -Hcnib; exact Hlow16).
                   sl_own_transport CID52 CID59 eb pj b.
                   iApply (Dirlink.wp_dirlink_gen (CID := CID59) gs j gl gu gd gk pd
                             pav pu bn g gfs gi cn gtl γa γf γpr cov logstart
                             inodestart nib bmapstart size dev (ientry kd)
                             dinum bmd datd dnd dnd nf (sl_low16 inum) n2 Sb2
                             pid (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1)
                             dqs dqb dqbs (DfracOwn (1/2))
                             U6 (K - 38)%nat eb b lks
                             (upd_upt V P2) ltac:(exact Kdl) Htyd
                             ltac:(exact (proj1 (proj2 Hdiok)))
                             ltac:(exact (proj1 (proj2 (proj2 (proj2 (proj2 Hdiok))))))
                             ltac:(rewrite Hcnib;
                                   exact (Hddok ltac:(rewrite Htyd;
                                                      vm_compute; reflexivity)))
                             (* THE BORROWED LICENCE, LEFT DISJUNCT: earned by
                                sys_link's OWN orphan guard at [sysfile.c:161]
                                ([if(dp->nlink == 0) goto bad;], the +0x84/+0x88
                                pair above).  The fall-through REFUTED it and
                                left [Hdnl0], so the directory this [dirlink]
                                appends into is live and the inner [dirlookup]'s
                                [iget] needs no name-side excuse.
                                (fs-fragments.md §7.5.6, the sys_link row.) *)
                             ltac:(left; clear -Hdnl0; intro Hc; apply Hdnl0;
                                   apply bv_eq; rewrite Hc; vm_compute;
                                   reflexivity)
                             Hdocd
                             ltac:(exact (di_type_stable_refl _))
                             ltac:(exact (di_nlink_stable_refl _
                                     (proj1 (proj2 (proj2 (proj2 Hdiok))))))
                             Hgeom ltac:(exact (proj1 Hdiok))
                             ltac:(exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hdiok)))))))
                             ltac:(exact (proj1 (proj2 (proj2 Hdiok))))
                             ltac:(exact (sl_size_lt _
                                     (proj1 (proj2 (proj2 (proj2 (proj2 Hdiok)))))))
                             Hist0 Hdiblk Hdiblog Hdinb Hlow16 Hbmgeo Hprkc Hsize
                             Hbm0 Hbmcov Hbmlog Hcovb Hiregb
                             ltac:(exact (sl_dl_need_ok _ w1 w2 _ n2 Hcrok2 Hu3))
                             Hj Hgl HU6a0 HU6a2 Heb (Hlb "log"%string)
                             with "Hcg Hown Htext Hpc Hdata Hprk Hbio Hlog
                                   Hkenv Hidevd Hiinumd Hmetad Hmapd Hblocksd
                                   [Hnm14] Hsbi Hsbs Hsbb Hbmres Hireg Hropen Hdiatd Hpidq
                                   Hprocs Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows
                                   Hslks Hir1c Hdlnkd HopS").
                   { iEval (rewrite HU6a1). iExact "Hnm14". }
                   iIntros (CID60 Hq60 mdl found bmd' datd' dnd' dnd0' n3 Sb3 tot)
                     "%Hcsdl Hcg Hown Hpc Hidevd Hiinumd Hmetad Hmapd Hblocksd
                      Hnm14 Hsbi Hsbs Hsbb Hdiatd Hpidq Hbsl Hir1c Hdlnkd %Hn3
                      %HSb3 %Hdlp %Hfnd HopS %Hcapd %Hsizedd %Harm".
                   iEval (rewrite HU6a1) in "Hnm14".
                   assert (Hpca0 : ret_pc (U6 !!! Regidx Rra : mword 64)
                                   = mword_of_int (SL + 0xa0)) by (rewrite HU6ra; pcw).
                   iEval (rewrite Hpca0) in "Hpc".
                   assert (Hdlregs : sl_regs m sp0 (ientry kk) (ientry kd) mdl)
                     by exact (sl_regs_cs m sp0 _ _ U6 mdl Hcsdl HU6regs).
                   assert (Hdls1 : (mdl !!! Regidx Rs1 : mword 64) = ientry kk)
                     by exact (sl_regs_s1 _ _ _ _ _ Hdlregs).
                   assert (Hdls2 : (mdl !!! Regidx Rs2 : mword 64) = ientry kd)
                     by exact (sl_regs_s2 _ _ _ _ _ Hdlregs).
                   assert (Hcrok3 : sl_crok (bool_decide (bmapstart ∈ Sb3)) w1 w2).
                   { intro Hf. apply bool_decide_eq_false in Hf. split.
                     - destruct w1; [| reflexivity]. exfalso. apply Hf.
                       apply HSb3. apply HSb2. apply elem_of_union_l.
                       exact (Hw1 eq_refl).
                     - destruct w2; [| reflexivity]. exfalso. apply Hf.
                       apply HSb3. exact (Hw2 eq_refl). }
                   assert (Hcrimp : bool_decide (bmapstart ∈ Sb2) = true ->
                                    bool_decide (bmapstart ∈ Sb3) = true).
                   { intro Ht. apply bool_decide_eq_true.
                     apply HSb3. exact (proj1 (bool_decide_eq_true _) Ht). }
                   assert (Hmem3 : IBLOCK inum inodestart ∈ Sb3)
                     by exact (HSb3 _ Hmem2').
                   iAssert (inode_ref_short kk (qq/2 + qq/2)%Qp (qq/2)%Qp dev inum)
                     with "[Hkfrag Hklive Hipdev Hipinum Hkshare]" as "Hkeep".
                   { rewrite /inode_ref_short /inode_ident /i_dev /i_inum. iFrame. }
                   (* the three post-dirlink arms.  TWO of them go to
                      [bad:] through the [iunlockput(dp)] at +0xee, and the
                      third is the success append. *)
                   assert (Hnrec0 : dir_nrec (bv_unsigned (di_size dnd))
                                    = dir_nrec (bv_unsigned (di_size dnd)))
                     by reflexivity.
                   assert (Hli : bv_unsigned (sl_low16 inum) = bv_unsigned inum).
                   { apply sl_low16_unsigned.
                     assert (E16 : (2 ^ 16 = 65536)%Z) by (vm_compute; reflexivity).
                     lia. }
                   destruct found.
                   --- (* ============ ARM F-FOUND: the name was there ======= *)
                       destruct Harm as (Hfst & Ha0m & Hbme & Hdate & Hdne &
                                         Hdn0e & Htot0).
                       assert (Hiu3 : (iput_units <= n3)%nat)
                         by exact (sl_found_entry w1 w2 n2 n3 Hu3 (Hfnd eq_refl)).
                       iApply (wp_blt_x0_taken_s_sconf (CID := CID60)
                                 (mword_of_int (SL + 0xa0))
                                 (mword_of_int 78 : mword 13) Ra0 mdl (K - 38)%nat b
                                 ltac:(nz) ltac:(rgne; rewrite Ha0m; exact sl_m1_neg)
                                 ltac:(rewrite Htgee_a0; vm_compute; reflexivity)
                                 with "Hcg Hpc Hia0").
                       iIntros (CID61 Hq61). iApply bi.later_intro. iIntros "Hcg Hpc".
                       iEval (rewrite Htgee_a0) in "Hpc".
                       subst bmd' datd' dnd' dnd0'.
                       iAssert (ic_loaded gfs gi cov logstart kd dinum dnd bmd)
                         with "[Hdlnkd Hdiatd Hmetad Hmapd Hblocksd]" as "Hloadd".
                       { rewrite /ic_loaded. iExists datd.
                         iSplitR; [iPureIntro; exact Hdiok |].
                         iSplitR; [iPureIntro; exact Hddok |].
                         iSplitR; [iPureIntro; exact Hddixd |].
                         iSplitR; [iPureIntro; exact Hdocd |].
                         iSplitR; [iPureIntro; exact Hduqd |].
                         iSplitL "Hdlnkd"; [iExact "Hdlnkd" |].
                         iFrame "Hdiatd Hmetad". rewrite /inode_map.
                         iDestruct "Hmapd" as "[Ha Hi]". iFrame "Ha Hi Hblocksd". }
                       (* the generation is ALREADY in hand: [iunlock] hands [gsh] back
                          (SpecIunlock's amended post), so the tail re-[ilock]s under the
                          very generation the [ity_shot] above names. *)
                       iDestruct (sl_nm_join (pa_stk sp0 6) bn0 nf
                                    with "Hnm14 Hnm2") as "HbN".
                       iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN")
                         as (bn1) "HbN".
                       iDestruct (sl_buf_join (pa_stk sp0 22) bw1 pk2 Hpk2
                                    with "Hbufw Hbufwr") as "HbW".
                       iDestruct (sl_bytes_name (pa_stk sp0 22) 128 with "HbW")
                         as (bw2) "HbW".
                       iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                                    with "Hbufk Hbufrest") as "HbO".
                       iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO")
                         as (bo2) "HbO".
                       iDestruct (log_opS_named with "HopS") as (e0) "HopE".
                       iDestruct (wp_next_shift (b := true) (CIDa := CID0)
                                    (CIDb := CID61) ltac:(wp_next_chain)
                                    with "Hcont") as "Hcont".
                       sl_own_transport CID60 CID61 eb pj b.
                       iApply (Tails.sl_tail_f (CID0 := CID61) gs j gl gu gd gk pd
                                 pav pu bn g gfs gi cn gtl gil gisl gild gisld cov
                                 logstart bmapstart inodestart nib size dev
                                 kk (qq/2)%Qp (qq/2)%Qp gsh inum
                                 (di_type (sl_incnl dn))
                                 kd (qd/2)%Qp (qd/2)%Qp gyd dinum dnd bmd
                                 n3 Sb3 (bool_decide (bmapstart ∈ Sb3)) false e0
                                 pid (DfracOwn (1/4)) dqb dqs
                                 m mdl sp0 K eb b lks bn1 bw2 bo2
                                 (upd_upt V P2) ltac:(exact Kil) ltac:(exact Kiupd)
                                 ltac:(exact Kiup) ltac:(exact Keo) K38 Kpop
                                 Hkk Hkd Hclog Hcist Hgeom Hsize Hbm0 Hbmcov
                                 Hbmlog Hist0 Hiblk Hiblog Hinb
                               Hdiblk Hdiblog
                                 Hdinb Hcovb
                                 ltac:(exact (proj1 (bool_decide_eq_true _)))
                                 ltac:(discriminate) Hmem3 Hiu3
                                 ltac:(exact (fun w n' Hw Hn' =>
                                         sl_found_close _ w1 w2 w n2 n3 n'
                                           Hcrok3 Hu3 (Hfnd eq_refl) Hw Hn'))
                                 Hj Hgl Hlkempty Heb ltac:(reflexivity)
                                 (sl_regs_sp _ _ _ _ _ Hdlregs)
                                 (sl_regs_thr _ _ _ _ _ Hdlregs) Hdls1 Hdls2 Hal
                                 Hncd
                                 with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog Hseam
                                       Hgen Hitab Hitinv Hesck Hescd Hireg Hropen Hslkk
                                       Hslkd0 Hkeep Hru Hshr Hshot2 Hilink Hslkdd
                                       Hdepd Hidevd Hiinumd Hivalidd Hloadd Hshotd2
                                       Hfrzd Hkeepd Hrud Hsbb Hsbi Hbmres Hpidq Hprocs Hdev
                                       Hgeo Hdlk Hbsl HopE Hf1 Hf2 Hf3 Hf4
                                       HbN HbW HbO
                                       [Hsbs Hir1c Hcwdref Hofiles Hftok Hcont]").
                       iEval (rewrite /wp_next).
                       iIntros (CIDy) "%Hqy". iIntros (mf)
                         "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpidq Hsbb
                          Hsbi Hbsl Hislots".
                       iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
                       iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
                       iCombine "Hpidq Hofiles" as "Hpnc".
                       iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
                       iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                                    with "[Hpnc Href Hftok]") as "Hpriv";
                         [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
                       iDestruct (iref_slots_combine 1 2 with "Hir1c Hislots") as "Hir".
                       iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown Htce
                                 Hcce Hpc Hbsl Hsbb Hsbi Hsbs Hir Hpriv [%]").
                       { exact Hcsf. }
                       { exact Hupt. }
                       { left. rewrite Ha0f. reflexivity. }
                   --- (* ============ the APPEND arm ========================= *)
                       destruct Harm as (Hnone & Hwf3 & Hholes3 & Haddr3 &
                                         Hsz313 & Hcov3 & Hdne & Hdn0imp & Htotle &
                                         Hrng & Hbl).
                       destruct (Hdlp eq_refl) as (Hspend & Hatom & Hmemtrio).
                       assert (Hdn0e : dnd0' = dnd') by exact (Hdn0imp eq_refl).
                       assert (Htyeq : di_type dnd' = di_type dnd)
                         by (rewrite Hdne; reflexivity).
                       assert (Hnleq : di_nlink dnd' = di_nlink dnd)
                         by (rewrite Hdne; reflexivity).
                       assert (Hoff32 : (Z.of_nat
                                 (16 * dir_slot datd
                                         (dir_nrec (bv_unsigned (di_size dnd)))
                                  + tot) < 2 ^ 32)%Z)
                         by exact (sl_off32 dnd datd tot
                                     (proj1 (proj2 (proj2 (proj2 (proj2 Hdiok)))))
                                     Htotle).
                       assert (Hszmax : bv_unsigned (di_size dnd')
                                 = Z.max (bv_unsigned (di_size dnd))
                                     (Z.of_nat
                                        (16 * dir_slot datd
                                                (dir_nrec (bv_unsigned (di_size dnd)))
                                         + tot)))
                         by (rewrite Hdne; exact (sl_wi_size_max dnd bmd' _ tot Hoff32)).
                       assert (Hszmono :
                                 (bv_unsigned (di_size dnd)
                                  <= bv_unsigned (di_size dnd'))%Z)
                         by (clear -Hszmax; rewrite Hszmax; lia).
                       assert (Hddok' : dir_ok icfg_nib dnd' datd').
                       { apply (dir_ok_dirlink icfg_nib dnd dnd' datd datd'
                                 (sl_low16 inum) (bname 14 nf)
                                 (dir_nrec (bv_unsigned (di_size dnd)))
                                 (dir_slot datd (dir_nrec (bv_unsigned (di_size dnd))))
                                 tot eq_refl eq_refl Htotle Hlow16i
                                 Htyeq Hszmax Hrng Hddok). }
                       (* ...and the ".." index clause across the same write.
                          The window is [dir_slot], which the clause's own
                          liveness at index 1 keeps away from it, and the
                          count rides on [Hszmax] -- a dirlink only grows
                          the size. *)
                       assert (Hddix' : dir_dots_ix (bv_unsigned dinum) dnd' datd').
                       { apply (dir_dots_ix_dirlink (bv_unsigned dinum)
                                 dnd dnd' datd datd'
                                 (sl_low16 inum) (bname 14 nf)
                                 (dir_nrec (bv_unsigned (di_size dnd)))
                                 (dir_slot datd (dir_nrec (bv_unsigned (di_size dnd))))
                                 tot eq_refl eq_refl Htotle Htyeq Hnleq
                                 Hszmono Hrng Hddixd). }
                       (* ...and the COMPLEMENT clause, which the KERNEL FIX
                          is what makes free: xv6 f60ff58's orphan guard at
                          +0x84 has already refused an orphaned parent, so
                          the record this dirlink appends to is LIVE and the
                          clause says nothing about it.  Without ARM E2 this
                          is exactly the site where the strong isdirempty
                          invariant was FALSE of the binary. *)
                       assert (Hdoc' : dir_orphan_clean dnd' datd').
                       { apply dir_orphan_clean_live. rewrite Hnleq.
                         intro Hc. apply Hdnl0. apply bv_eq. rewrite Hc.
                         vm_compute. reflexivity. }
                       (* ...and the UNIQUENESS clause across the same write.
                          [Hatom] -- SpecDirlink's relay of writei's
                          single-block atomicity -- is what makes it true at
                          all: a PARTIAL record would go live carrying the
                          name bytes the last deletion left, and those may
                          duplicate a live name.  [Hnone] is dirlink's own
                          guard, and it is what pays for the full write. *)
                       assert (Hduq' : dir_uniq dnd' datd').
                       { apply (dir_uniq_dirlink dnd dnd' datd datd'
                                 (sl_low16 inum) (bname 14 nf)
                                 (dir_nrec (bv_unsigned (di_size dnd)))
                                 (dir_slot datd (dir_nrec (bv_unsigned (di_size dnd))))
                                 tot eq_refl eq_refl Hatom
                                 (bname_length_le 14 nf) (cut_nul_nonul _)
                                 Htyeq Hszmax Hrng Hnone Hduqd). }
                       assert (Hdtynz : bv_unsigned (di_type dnd') <> 0)
                         by (rewrite Htyeq;
                             exact (proj1 (proj2 (proj2 (proj2 Hdiok))))).
                       assert (Hdiok' : inode_ok cov logstart dnd' bmd' datd').
                       { unfold inode_ok. split_and!.
                         - exact Hwf3.
                         - exact Hcov3.
                         - exact Haddr3.
                         - exact Hdtynz.
                         - exact (Hcapd
                                    (proj1 (proj2 (proj2 (proj2 (proj2 Hdiok)))))).
                         - exact Hholes3.
                         - exact (Hsizedd
                                    (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdiok))))))). }
                       destruct Hbl as [[Ha0z Ht16] | [Ha0m Htlt]].
                       ++++ (* ====== ARM G: the whole record went in ====== *)
                            assert (Htot2 : (2 <= tot)%nat)
                              by (clear -Ht16; lia).
                            assert (Htotpos : (0 < tot)%nat)
                              by (clear -Ht16; lia).
                            iApply (wp_blt_x0_fall_s_sconf (CID := CID60)
                                      (mword_of_int (SL + 0xa0))
                                      (mword_of_int 78 : mword 13) Ra0 mdl
                                      (K - 38)%nat b ltac:(nz)
                                      ltac:(rgne; rewrite Ha0z; exact sl_zero_nonneg)
                                      with "Hcg Hpc Hia0").
                            iIntros (CID61 Hq61) "Hcg Hpc".
                            assert (Hppa4 : add_vec_int
                                      (mword_of_int (SL + 0xa0) : mword 64) 4
                                      = mword_of_int (SL + 0xa4)) by pcw.
                            iEval (rewrite Hppa4) in "Hpc".
                            (* THE DEPOSIT.  The [ilink] the [++] minted at
                               +0x5e goes into the PARENT's ledger here,
                               caller-side (fs-icache.md 20.18 ruling 1 keeps
                               every ledger resource out of SpecDirlink), and
                               this is the only arm on which it does. *)
                            iDestruct (dir_link_at_dirlink (bv_unsigned dinum)
                                         dnd' datd datd' (sl_low16 inum)
                                         (bname 14 nf)
                                         (dir_slot datd
                                            (dir_nrec (bv_unsigned (di_size dnd))))
                                         tot Htot2 Hrng with "[Hilink]")
                              as "Hk0".
                            { rewrite Hli. iExact "Hilink". }
                            (* V5': the appended slot is not the [".."] the
                               parent tie names.  [DirLinks.dir_slot_dots_ge2]
                               reads it off the dots clause under ARM E2's
                               own live-parent fall-through. *)
                            assert (Hslot1 : dir_slot datd
                                     (dir_nrec (bv_unsigned (di_size dnd)))
                                     <> 1%nat).
                            { pose proof (dir_slot_dots_ge2 (bv_unsigned dinum)
                                            dnd datd
                                            (dir_nrec (bv_unsigned (di_size dnd)))
                                            ltac:(clear -Htyd; rewrite Htyd;
                                                  vm_compute; reflexivity)
                                            ltac:(clear -Hdnl0; intro Hc;
                                                  apply Hdnl0; apply bv_eq;
                                                  rewrite Hc; vm_compute;
                                                  reflexivity)
                                            Hddixd eq_refl) as Hge2.
                              clear -Hge2. lia. }
                            iDestruct (dir_links_dirlink (bv_unsigned dinum)
                                         dnd dnd' datd datd' (sl_low16 inum)
                                         (bname 14 nf)
                                         (dir_nrec (bv_unsigned (di_size dnd)))
                                         (dir_slot datd
                                            (dir_nrec (bv_unsigned (di_size dnd))))
                                         tot eq_refl eq_refl Htotle Hslot1
                                         Htyeq Hnleq
                                         Hszmax Hrng with "Hk0 Hdlnkd") as "Hdlnkd'".
                            iAssert (ic_loaded gfs gi cov logstart kd dinum dnd' bmd')
                              with "[Hdlnkd' Hdiatd Hmetad Hmapd Hblocksd]"
                              as "Hloadd".
                            { rewrite /ic_loaded. iExists datd'.
                              iSplitR; [iPureIntro; exact Hdiok' |].
                              iSplitR; [iPureIntro; exact Hddok' |].
                              iSplitR; [iPureIntro; exact Hddix' |].
                              iSplitR; [iPureIntro; exact Hdoc' |].
                              iSplitR; [iPureIntro; exact Hduq' |].
                              iSplitL "Hdlnkd'"; [iExact "Hdlnkd'" |].
                              rewrite Hdn0e. iFrame "Hdiatd Hmetad".
                              rewrite /inode_map.
                              iDestruct "Hmapd" as "[Ha Hi]".
                              iFrame "Ha Hi Hblocksd". }
                            iAssert (ity_shot gyd (di_type dnd')) as "#Hshotd3".
                            { rewrite Htyeq. iExact "Hshotd2". }
                            destruct (Hmemtrio Htotpos)
                              as (Hmtgt & Hmiblk & Hmbmap).
                            (* ===== +0xa4 c.mv a0,s2 ===== *)
                            iApply (wp_cmv_s_sconf (CID := CID61)
                                      (mword_of_int (SL + 0xa4)) Ra0 Rs2 mdl
                                      (K - 38)%nat b ltac:(nz) ltac:(rdok)
                                      with "Hcg Hpc Hia4").
                            iIntros (CID62 Hq62) "Hcg Hpc".
                            set (W0 := <[Regidx Ra0 := regval_into_reg
                                          (add_vec zero_reg (mdl !!! Regidx Rs2))]> mdl).
                            assert (HW0a0 : (W0 !!! Regidx Ra0 : mword 64) = ientry kd).
                            { etransitivity; [ rewrite /W0; apply upd_eq |].
                              rewrite add_vec_zero_l. exact Hdls2. }
                            assert (HW0regs : sl_regs m sp0 (ientry kk) (ientry kd) W0)
                              by (rewrite /W0; apply sl_regs_caller;
                                  [exact Hcsa0 | exact Hdlregs]).
                            assert (Hppa6 : add_vec_int
                                      (mword_of_int (SL + 0xa4) : mword 64) 2
                                      = mword_of_int (SL + 0xa6)) by pcw.
                            iEval (rewrite Hppa6) in "Hpc".
                            (* ===== +0xa6 jal ra,iunlockput -- the PARENT ===== *)
                            iApply (wp_jal_s_sconf (CID := CID62)
                                      (mword_of_int (SL + 0xa6)) Rra
                                      (mword_of_int 2090296 : mword 21) W0
                                      (K - 38)%nat b ltac:(nz) ltac:(rdok)
                                      ltac:(vm_compute; reflexivity)
                                      with "Hcg Hpc Hia6").
                            iIntros (CID63 Hq63) "Hcg Hpc".
                            set (W1 := <[Regidx Rra := regval_into_reg
                                          (add_vec_int
                                             (mword_of_int (SL + 0xa6) : mword 64) 4)]> W0).
                            assert (Hjupd : add_vec
                                      (mword_of_int (SL + 0xa6) : mword 64)
                                      (sign_extend' 64 (mword_of_int 2090296 : mword 21))
                                      = mword_of_int KernelSyms.iunlockput) by pcw.
                            iEval (rewrite Hjupd) in "Hpc".
                            assert (HW1ra : (W1 !!! Regidx Rra : mword 64)
                                      = add_vec_int
                                          (mword_of_int (SL + 0xa6) : mword 64) 4)
                              by (rewrite /W1; apply upd_eq).
                            assert (HW1a0 : (W1 !!! Regidx Ra0 : mword 64) = ientry kd)
                              by (rewrite /W1 upd_ne; [exact HW0a0 | nz]).
                            assert (HW1regs : sl_regs m sp0 (ientry kk) (ientry kd) W1)
                              by (rewrite /W1; apply sl_regs_caller;
                                  [exact Hcsra | exact HW0regs]).
                            assert (Hiu3 : (iput_units <= n3)%nat)
                              by exact (proj1 (sl_ok_close _ _ _ _ _ w1 w2 false
                                          n2 n3 n3 Hcrok2 Hu3 Hspend
                                          (sl_sub_le _ _))).
                            iDestruct (log_opS_named with "HopS") as (e0) "HopE".
                            sl_own_transport CID60 CID63 eb pj b.
                            iApply (Iunlockput.wp_iunlockput_gen (CID := CID63) gs j
                                      gl gu gd gk pd pav pu bn g gfs gi cn gtl gild
                                      gisld cov logstart bmapstart inodestart nib
                                      size dev kd (qd/2)%Qp (qd/2)%Qp gyd
                                      dinum dnd' bmd' n3 Sb3
                                      (bool_decide (bmapstart ∈ Sb3)) true false e0
                                      pid (DfracOwn (1/4)) dqb dqs
                                      W1 (K - 38)%nat eb b lks
                                      (upd_upt V P2) ltac:(exact Kiup) Hkd
                                      ltac:(exact (proj1 (bool_decide_eq_true _)))
                                      ltac:(intros _; exact Hmiblk)
                                      Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hdiblk
                                      Hdiblog Hdinb Hcovb Hiu3 Hj Hgl HW1a0
                                      ltac:(rewrite Hlkempty; apply locks_below_empty)
                                      with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog
                                            Hitab Hitinv Hescd Hireg Hropen Hslkd0 Hslkdd
                                            Hdepd Hidevd Hiinumd Hivalidd
                                            Hloadd Hshotd3 Hfrzd [$Hkeepd $Hrud] Hsbb Hsbi
                                            Hbmres
                                            Hpidq Hprocs Hdev Hgeo Hdlk Hbsl [] HopE").
                            { rewrite Heb /trap_csrs_ext. done. }
                            { rewrite Heb /cpu_claim_ext. done. }
                            { done. }
                            iIntros (CID64 Hq64 mupd n4 Sb4 wd)
                              "%Hcsupd Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi
                               Hbsl %HSb4 %Hwd %Hcrbwd %Hn4 HopS Hislotd".
                            assert (Hpcaa : ret_pc (W1 !!! Regidx Rra : mword 64)
                                      = mword_of_int (SL + 0xaa))
                              by (rewrite HW1ra; pcw).
                            iEval (rewrite Hpcaa) in "Hpc".
                            assert (Hupdregs : sl_regs m sp0 (ientry kk) (ientry kd)
                                                 mupd)
                              by exact (sl_regs_cs m sp0 _ _ W1 mupd Hcsupd HW1regs).
                            assert (Hupds1 : (mupd !!! Regidx Rs1 : mword 64)
                                             = ientry kk)
                              by exact (sl_regs_s1 _ _ _ _ _ Hupdregs).
                            assert (Hiu4 : (iput_units <= n4)%nat)
                              by exact (proj2 (sl_ok_close _ _ _ _ _ w1 w2 wd
                                          n2 n3 n4 Hcrok2 Hu3 Hspend (proj1 Hn4))).
                            (* ===== +0xaa c.mv a0,s1 ===== *)
                            iApply (wp_cmv_s_sconf (CID := CID64)
                                      (mword_of_int (SL + 0xaa)) Ra0 Rs1 mupd
                                      (K - 38)%nat b ltac:(nz) ltac:(rdok)
                                      with "Hcg Hpc Hiaa").
                            iIntros (CID65 Hq65) "Hcg Hpc".
                            set (W2 := <[Regidx Ra0 := regval_into_reg
                                          (add_vec zero_reg
                                             (mupd !!! Regidx Rs1))]> mupd).
                            assert (HW2a0 : (W2 !!! Regidx Ra0 : mword 64) = ientry kk).
                            { etransitivity; [ rewrite /W2; apply upd_eq |].
                              rewrite add_vec_zero_l. exact Hupds1. }
                            assert (HW2regs : sl_regs m sp0 (ientry kk) (ientry kd) W2)
                              by (rewrite /W2; apply sl_regs_caller;
                                  [exact Hcsa0 | exact Hupdregs]).
                            assert (Hppac : add_vec_int
                                      (mword_of_int (SL + 0xaa) : mword 64) 2
                                      = mword_of_int (SL + 0xac)) by pcw.
                            iEval (rewrite Hppac) in "Hpc".
                            (* ===== +0xac jal ra,iput -- the CHILD ===== *)
                            iApply (wp_jal_s_sconf (CID := CID65)
                                      (mword_of_int (SL + 0xac)) Rra
                                      (mword_of_int 2090080 : mword 21) W2
                                      (K - 38)%nat b ltac:(nz) ltac:(rdok)
                                      ltac:(vm_compute; reflexivity)
                                      with "Hcg Hpc Hiac").
                            iIntros (CID66 Hq66) "Hcg Hpc".
                            set (W3 := <[Regidx Rra := regval_into_reg
                                          (add_vec_int
                                             (mword_of_int (SL + 0xac) : mword 64) 4)]> W2).
                            assert (Hjip : add_vec
                                      (mword_of_int (SL + 0xac) : mword 64)
                                      (sign_extend' 64 (mword_of_int 2090080 : mword 21))
                                      = mword_of_int KernelSyms.iput) by pcw.
                            iEval (rewrite Hjip) in "Hpc".
                            assert (HW3ra : (W3 !!! Regidx Rra : mword 64)
                                      = add_vec_int
                                          (mword_of_int (SL + 0xac) : mword 64) 4)
                              by (rewrite /W3; apply upd_eq).
                            assert (HW3a0 : (W3 !!! Regidx Ra0 : mword 64) = ientry kk)
                              by (rewrite /W3 upd_ne; [exact HW2a0 | nz]).
                            assert (HW3regs : sl_regs m sp0 (ientry kk) (ientry kd) W3)
                              by (rewrite /W3; apply sl_regs_caller;
                                  [exact Hcsra | exact HW2regs]).
                            (* this arm hands the reference to [iput] and
                               wants nothing from the name: forget here. *)
                            iDestruct (inode_shr_gen_forget with "Hshr")
                              as "Hshr".
                            iDestruct (inode_ref_gather with "Hkeep Hshr") as "Hrefip".
                            sl_own_transport CID64 CID66 eb pj b.
                            iApply (Iput.wp_iput_sconf (CID := CID66) gs j gl gu gd gk
                                      pd pav pu bn g gfs gi cn gtl gil gisl cov
                                      logstart bmapstart inodestart nib size dev
                                      kk (qq/2 + qq/2)%Qp inum n4
                                      pid (DfracOwn (1/4)) dqb dqs
                                      W3 (K - 38)%nat eb b lks
                                      (upd_upt V P2) ltac:(exact Kip) Hkk Hgeom Hsize Hbm0 Hbmcov
                                      Hbmlog Hist0 Hiblk Hiblog Hinb Hcovb Hiu4 Hj
                                      Hgl HW3a0
                                      ltac:(rewrite Hlkempty; apply locks_below_empty)
                                      with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog
                                            Hitab Hitinv Hesck Hireg Hropen Hslkk [$Hrefip $Hru]
                                            Hsbb Hsbi Hbmres Hpidq Hprocs Hdev Hgeo
                                            Hdlk Hbsl [HopS]").
                            { rewrite Heb /trap_csrs_ext. done. }
                            { rewrite Heb /cpu_claim_ext. done. }
                            { rewrite /log_op. iExists Sb4. iExact "HopS". }
                            iIntros (CID67 Hq67 mip n5)
                              "%Hcsip Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi
                               Hbsl %Hn5 Hop Hisloti".
                            assert (Hpcb0 : ret_pc (W3 !!! Regidx Rra : mword 64)
                                      = mword_of_int (SL + 0xb0))
                              by (rewrite HW3ra; pcw).
                            iEval (rewrite Hpcb0) in "Hpc".
                            assert (Hipregs : sl_regs m sp0 (ientry kk) (ientry kd) mip)
                              by exact (sl_regs_cs m sp0 _ _ W3 mip Hcsip HW3regs).
                            (* ===== +0xb0 jal ra,end_op ===== *)
                            iApply (wp_jal_s_sconf (CID := CID67)
                                      (mword_of_int (SL + 0xb0)) Rra
                                      (mword_of_int 2092496 : mword 21) mip
                                      (K - 38)%nat b ltac:(nz) ltac:(rdok)
                                      ltac:(vm_compute; reflexivity)
                                      with "Hcg Hpc Hib0").
                            iIntros (CID68 Hq68) "Hcg Hpc".
                            set (W4 := <[Regidx Rra := regval_into_reg
                                          (add_vec_int
                                             (mword_of_int (SL + 0xb0) : mword 64) 4)]> mip).
                            assert (Hjeo : add_vec
                                      (mword_of_int (SL + 0xb0) : mword 64)
                                      (sign_extend' 64 (mword_of_int 2092496 : mword 21))
                                      = mword_of_int KernelSyms.end_op) by pcw.
                            iEval (rewrite Hjeo) in "Hpc".
                            assert (HW4ra : (W4 !!! Regidx Rra : mword 64)
                                      = add_vec_int
                                          (mword_of_int (SL + 0xb0) : mword 64) 4)
                              by (rewrite /W4; apply upd_eq).
                            assert (HW4regs : sl_regs m sp0 (ientry kk) (ientry kd) W4)
                              by (rewrite /W4; apply sl_regs_caller;
                                  [exact Hcsra | exact Hipregs]).
                            sl_own_transport CID67 CID68 eb pj b.
                            iApply (EndOp.wp_end_op_sconf (CID := CID68) gs j gl gu gd
                                      gk pd pav pu bn g gfs cov logstart dev n5 pid
                                      (DfracOwn (1/4)) W4 (K - 38)%nat eb b lks
                                      (upd_upt V P2) ltac:(exact Keo) Hgeom Hj Hgl
                                      ltac:(rewrite Hlkempty; apply locks_below_empty)
                                      with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog
                                            Hseam Hgen Hpidq Hprocs Hdev Hgeo Hdlk Hop").
                            { rewrite Heb /trap_csrs_ext. done. }
                            { rewrite Heb /cpu_claim_ext. done. }
                            iIntros (CID69 Hq69 meo) "%Hcseo Hcg Hown _ _ Hpc Hpidq".
                            assert (Hpcb4 : ret_pc (W4 !!! Regidx Rra : mword 64)
                                      = mword_of_int (SL + 0xb4))
                              by (rewrite HW4ra; pcw).
                            iEval (rewrite Hpcb4) in "Hpc".
                            assert (Heoregs : sl_regs m sp0 (ientry kk) (ientry kd) meo)
                              by exact (sl_regs_cs m sp0 _ _ W4 meo Hcseo HW4regs).
                            (* ===== +0xb4 c.li a5,0 ===== *)
                            iApply (wp_cli_s_sconf (CID := CID69)
                                      (mword_of_int (SL + 0xb4)) Ra5
                                      (mword_of_int 0 : mword 6)
                                      (zero_reg : mword 64) meo (K - 38)%nat b
                                      ltac:(nz) ltac:(rdok) ltac:(pcw)
                                      with "Hcg Hpc Hib4").
                            iIntros (CID70 Hq70) "Hcg Hpc".
                            set (W5 := <[Regidx Ra5 := regval_into_reg
                                          (zero_reg : mword 64)]> meo).
                            assert (HW5a5 : (W5 !!! Regidx Ra5 : mword 64)
                                            = (zero_reg : mword 64))
                              by (rewrite /W5; apply upd_eq).
                            assert (HW5regs : sl_regs m sp0 (ientry kk) (ientry kd) W5)
                              by (rewrite /W5; apply sl_regs_caller;
                                  [exact Hcsa5 | exact Heoregs]).
                            assert (Hppb6 : add_vec_int
                                      (mword_of_int (SL + 0xb4) : mword 64) 2
                                      = mword_of_int (SL + 0xb6)) by pcw.
                            iEval (rewrite Hppb6) in "Hpc".
                            (* ===== +0xb6 c.ldsp s1,280(sp) ===== *)
                            assert (Hg3 : add_vec (W5 !!! Regidx csp_rs1 : mword 64)
                                      (zero_extend' 64
                                         (concat_vec (mword_of_int 35 : mword 6)
                                            ('b"000")))
                                      = pa_stk sp0 3)
                              by (rewrite (sl_regs_sp _ _ _ _ _ HW5regs);
                                  apply sl_frm3).
                            iApply (wp_cldsp_s_sconf (CID := CID70)
                                      (mword_of_int (SL + 0xb6))
                                      (mword_of_int 35 : mword 6) Rs1 W5 (K - 38)%nat
                                      (m !!! Regidx Rs1 : mword 64) b ltac:(nz)
                                      ltac:(rdok) with "Hcg Hpc Hib6 [Hf3]").
                            { iEval (rewrite Hg3). iExact "Hf3". }
                            iIntros (CID71 Hq71) "Hcg Hpc Hf3".
                            iEval (rewrite Hg3) in "Hf3".
                            set (W6 := <[Regidx Rs1 := regval_into_reg
                                          (m !!! Regidx Rs1 : mword 64)]> W5).
                            assert (HW6s1 : (W6 !!! Regidx Rs1 : mword 64)
                                            = (m !!! Regidx Rs1 : mword 64))
                              by (rewrite /W6; apply upd_eq).
                            assert (HW6a5 : (W6 !!! Regidx Ra5 : mword 64)
                                            = (zero_reg : mword 64))
                              by (rewrite /W6 upd_ne; [exact HW5a5 | nz]).
                            assert (HW6regs : sl_regs m sp0
                                      (m !!! Regidx Rs1 : mword 64) (ientry kd) W6).
                            { rewrite /W6.
                              exact (sl_regs_wr_s1 m sp0 _ _ _ W5 _ eq_refl HW5regs). }
                            assert (Hppb8 : add_vec_int
                                      (mword_of_int (SL + 0xb6) : mword 64) 2
                                      = mword_of_int (SL + 0xb8)) by pcw.
                            iEval (rewrite Hppb8) in "Hpc".
                            (* ===== +0xb8 c.ldsp s2,272(sp) ===== *)
                            assert (Hg4 : add_vec (W6 !!! Regidx csp_rs1 : mword 64)
                                      (zero_extend' 64
                                         (concat_vec (mword_of_int 34 : mword 6)
                                            ('b"000")))
                                      = pa_stk sp0 4)
                              by (rewrite (sl_regs_sp _ _ _ _ _ HW6regs);
                                  apply sl_frm4).
                            iApply (wp_cldsp_s_sconf (CID := CID71)
                                      (mword_of_int (SL + 0xb8))
                                      (mword_of_int 34 : mword 6) Rs2 W6 (K - 38)%nat
                                      (m !!! Regidx Rs2 : mword 64) b ltac:(nz)
                                      ltac:(rdok) with "Hcg Hpc Hib8 [Hf4]").
                            { iEval (rewrite Hg4). iExact "Hf4". }
                            iIntros (CID72 Hq72) "Hcg Hpc Hf4".
                            iEval (rewrite Hg4) in "Hf4".
                            set (W7 := <[Regidx Rs2 := regval_into_reg
                                          (m !!! Regidx Rs2 : mword 64)]> W6).
                            assert (HW7a5 : (W7 !!! Regidx Ra5 : mword 64)
                                            = (zero_reg : mword 64))
                              by (rewrite /W7 upd_ne; [exact HW6a5 | nz]).
                            assert (HW7regs : sl_regs m sp0
                                      (m !!! Regidx Rs1 : mword 64)
                                      (m !!! Regidx Rs2 : mword 64) W7).
                            { rewrite /W7.
                              exact (sl_regs_wr_s2 m sp0 _ _ _ W6 _ eq_refl HW6regs). }
                            assert (Hppba : add_vec_int
                                      (mword_of_int (SL + 0xb8) : mword 64) 2
                                      = mword_of_int (SL + 0xba)) by pcw.
                            iEval (rewrite Hppba) in "Hpc".
                            (* ===== +0xba c.j +0x11a ===== *)
                            iApply (wp_cj_s_sconf (CID := CID72)
                                      (mword_of_int (SL + 0xba))
                                      (sign_extend' 21
                                         (concat_vec (mword_of_int 48 : mword 11)
                                            ('b"0"))) W7 (K - 38)%nat b
                                      ltac:(vm_compute; reflexivity)
                                      with "Hcg Hpc Hiba").
                            iIntros (CID73 Hq73). iApply bi.later_intro. iIntros "Hcg Hpc".
                            iEval (rewrite Htg11aba) in "Hpc".
                            iDestruct (sl_nm_join (pa_stk sp0 6) bn0 nf
                                         with "Hnm14 Hnm2") as "HbN".
                            iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN")
                              as (bn1) "HbN".
                            iDestruct (sl_buf_join (pa_stk sp0 22) bw1 pk2 Hpk2
                                         with "Hbufw Hbufwr") as "HbW".
                            iDestruct (sl_bytes_name (pa_stk sp0 22) 128 with "HbW")
                              as (bw2) "HbW".
                            iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                                         with "Hbufk Hbufrest") as "HbO".
                            iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO")
                              as (bo2) "HbO".
                            iDestruct (wp_next_shift (b := true) (CIDa := CID0)
                                         (CIDb := CID73) ltac:(wp_next_chain)
                                         with "Hcont") as "Hcont".
                            sl_own_transport CID69 CID73 eb pj b.
                            iApply (sl_epilogue (CID0 := CID73) m W7 sp0 K b pj
                                      (m !!! Regidx Rs1 : mword 64)
                                      (m !!! Regidx Rs2 : mword 64) bn1 bw2 bo2
                                      K38 Kpop ltac:(reflexivity)
                                      (sl_regs_sp _ _ _ _ _ HW7regs)
                                      (sl_regs_thr _ _ _ _ _ HW7regs)
                                      (sl_regs_s1 _ _ _ _ _ HW7regs)
                                      (sl_regs_s2 _ _ _ _ _ HW7regs) Hal
                                      with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                                            [Hown Hbsl Hsbb Hsbi Hsbs Hir1c
                                             Hislotd Hisloti Hcwdref Hofiles
                                             Hpidq Hftok Hcont]").
                            iEval (rewrite /wp_next).
                            iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
                            sl_own_transport CID73 CIDy eb pj b.
                            iSpecialize ("Hcont" $! CIDy with "[%]");
                              [wp_next_chain |].
                            iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
                            iCombine "Hpidq Hofiles" as "Hpnc".
                            iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
                            iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                                         with "[Hpnc Href Hftok]") as "Hpriv";
                              [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
                            iDestruct (iref_slots_combine 1 1
                                         with "Hir1c Hislotd") as "Hir2e".
                            iDestruct (iref_slots_combine 2 1
                                         with "Hir2e Hisloti") as "Hir".
                            iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown
                                      [] [] Hpc Hbsl Hsbb Hsbi Hsbs Hir
                                      Hpriv [%]").
                            { exact Hcsf. }
                            { exact Hupt. }
                            { rewrite Heb /trap_csrs_ext. done. }
                            { rewrite Heb /cpu_claim_ext. done. }
                            { right. rewrite Ha0f HW7a5. reflexivity. }
                       ++++ (* ====== ARM F-0: the EMPTY append ====== *)
                            assert (Htot0 : tot = 0%nat)
                              by exact (sl_atomic_lt16 tot Hatom Htlt).
                            iApply (wp_blt_x0_taken_s_sconf (CID := CID60)
                                      (mword_of_int (SL + 0xa0))
                                      (mword_of_int 78 : mword 13) Ra0 mdl
                                      (K - 38)%nat b ltac:(nz)
                                      ltac:(rgne; rewrite Ha0m; exact sl_m1_neg)
                                      ltac:(rewrite Htgee_a0; vm_compute; reflexivity)
                                      with "Hcg Hpc Hia0").
                            iIntros (CID61 Hq61). iApply bi.later_intro. iIntros "Hcg Hpc".
                            iEval (rewrite Htgee_a0) in "Hpc".
                            iDestruct (dir_links_dirlink_nop (bv_unsigned dinum)
                                         dnd dnd' datd datd' (sl_low16 inum)
                                         (bname 14 nf)
                                         (dir_nrec (bv_unsigned (di_size dnd)))
                                         (dir_slot datd
                                            (dir_nrec (bv_unsigned (di_size dnd))))
                                         eq_refl eq_refl Htyeq Hnleq
                                         ltac:(rewrite Hszmax Htot0; reflexivity)
                                         ltac:(rewrite Htot0 in Hrng; exact Hrng)
                                         with "Hdlnkd") as "Hdlnkd'".
                            iAssert (ic_loaded gfs gi cov logstart kd dinum dnd' bmd')
                              with "[Hdlnkd' Hdiatd Hmetad Hmapd Hblocksd]"
                              as "Hloadd".
                            { rewrite /ic_loaded. iExists datd'.
                              iSplitR; [iPureIntro; exact Hdiok' |].
                              iSplitR; [iPureIntro; exact Hddok' |].
                              iSplitR; [iPureIntro; exact Hddix' |].
                              iSplitR; [iPureIntro; exact Hdoc' |].
                              iSplitR; [iPureIntro; exact Hduq' |].
                              iSplitL "Hdlnkd'"; [iExact "Hdlnkd'" |].
                              rewrite Hdn0e. iFrame "Hdiatd Hmetad".
                              rewrite /inode_map.
                              iDestruct "Hmapd" as "[Ha Hi]".
                              iFrame "Ha Hi Hblocksd". }
                            iAssert (ity_shot gyd (di_type dnd')) as "#Hshotd3".
                            { rewrite Htyeq. iExact "Hshotd2". }
                            assert (Hiu3 : (iput_units <= n3)%nat)
                              by exact (sl_fail0_entry _ _ _ _ _ w1 w2 n2 n3
                                          Hcrok2 Hu3 Hspend).
                            (* the generation is ALREADY in hand: [iunlock] hands [gsh] back
                               (SpecIunlock's amended post), so the tail re-[ilock]s under the
                               very generation the [ity_shot] above names. *)
                            iDestruct (sl_nm_join (pa_stk sp0 6) bn0 nf
                                         with "Hnm14 Hnm2") as "HbN".
                            iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN")
                              as (bn1) "HbN".
                            iDestruct (sl_buf_join (pa_stk sp0 22) bw1 pk2 Hpk2
                                         with "Hbufw Hbufwr") as "HbW".
                            iDestruct (sl_bytes_name (pa_stk sp0 22) 128 with "HbW")
                              as (bw2) "HbW".
                            iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                                         with "Hbufk Hbufrest") as "HbO".
                            iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO")
                              as (bo2) "HbO".
                            iDestruct (log_opS_named with "HopS") as (e0) "HopE".
                            iDestruct (wp_next_shift (b := true) (CIDa := CID0)
                                         (CIDb := CID61) ltac:(wp_next_chain)
                                         with "Hcont") as "Hcont".
                            sl_own_transport CID60 CID61 eb pj b.
                            iApply (Tails.sl_tail_f (CID0 := CID61) gs j gl gu gd gk
                                      pd pav pu bn g gfs gi cn gtl gil gisl gild
                                      gisld cov logstart bmapstart inodestart nib
                                      size dev kk (qq/2)%Qp (qq/2)%Qp gsh
                                      inum (di_type (sl_incnl dn))
                                      kd (qd/2)%Qp (qd/2)%Qp gyd dinum dnd' bmd'
                                      n3 Sb3 (bool_decide (bmapstart ∈ Sb3)) false e0
                                      pid (DfracOwn (1/4)) dqb dqs
                                      m mdl sp0 K eb b lks bn1 bw2 bo2
                                      (upd_upt V P2) ltac:(exact Kil) ltac:(exact Kiupd)
                                      ltac:(exact Kiup) ltac:(exact Keo) K38 Kpop
                                      Hkk Hkd Hclog Hcist Hgeom Hsize Hbm0 Hbmcov
                                      Hbmlog Hist0 Hiblk Hiblog Hinb
                               Hdiblk Hdiblog
                                      Hdinb Hcovb
                                      ltac:(exact (proj1 (bool_decide_eq_true _)))
                                      ltac:(discriminate) Hmem3 Hiu3
                                      ltac:(exact (fun w n' Hw Hn' =>
                                              sl_fail0_close _ _ _ _ _ _ w1 w2 w
                                                n2 n3 n' Hcrok2 Hcrimp Hu3 Hspend
                                                Hw Hn'))
                                      Hj Hgl Hlkempty Heb ltac:(reflexivity)
                                      (sl_regs_sp _ _ _ _ _ Hdlregs)
                                      (sl_regs_thr _ _ _ _ _ Hdlregs) Hdls1 Hdls2 Hal
                                      Hncd
                                      with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog
                                            Hseam Hgen Hitab Hitinv Hesck Hescd
                                            Hireg Hropen Hslkk Hslkd0 Hkeep Hru Hshr Hshot2
                                            Hilink
                                            Hslkdd Hdepd Hidevd Hiinumd
                                            Hivalidd Hloadd Hshotd3 Hfrzd Hkeepd Hrud
                                            Hsbb
                                            Hsbi Hbmres Hpidq Hprocs Hdev Hgeo
                                            Hdlk Hbsl HopE Hf1 Hf2 Hf3 Hf4
                                            HbN HbW HbO
                                            [Hsbs Hir1c Hcwdref Hofiles Hftok Hcont]").
                            iEval (rewrite /wp_next).
                            iIntros (CIDy) "%Hqy". iIntros (mf)
                              "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpidq
                               Hsbb Hsbi Hbsl Hislots".
                            iSpecialize ("Hcont" $! CIDy with "[%]");
                              [wp_next_chain |].
                            iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
                            iCombine "Hpidq Hofiles" as "Hpnc".
                            iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
                            iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                                         with "[Hpnc Href Hftok]") as "Hpriv";
                              [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
                            iDestruct (iref_slots_combine 1 2 with "Hir1c Hislots")
                              as "Hir".
                            iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown
                                      Htce Hcce Hpc Hbsl Hsbb Hsbi Hsbs Hir
                                      Hpriv [%]").
                            { exact Hcsf. }
                            { exact Hupt. }
                            { left. rewrite Ha0f. reflexivity. }
                ** (* ---------- ARM E: no parent -- goto bad ---------- *)
                   iDestruct "Hres2" as "(%Hnpe & Hir2d)".
                   iApply (wp_cbeqz_taken_s_sconf (CID := CID49)
                             (mword_of_int (SL + 0x7e)) (mword_of_int 59 : mword 8)
                             (Cregidx (mword_of_int 2)) Ra0 T3 (K - 38)%nat b
                             ltac:(vm_compute; reflexivity) ltac:(nz)
                             ltac:(rgne; rewrite HT3a0 Hnpe; vm_compute; reflexivity)
                             ltac:(vm_compute; reflexivity)
                             with "Hcg Hpc Hi7e").
                   iIntros (CID50 Hq50). iApply bi.later_intro. iIntros "Hcg Hpc".
                   iEval (rewrite Htgf4) in "Hpc".
                   (* the two buffers, rejoined for the epilogue *)
                   iDestruct (sl_buf_join (pa_stk sp0 22) bw1 pk2 Hpk2
                                with "Hbufw Hbufwr") as "HbW".
                   iDestruct (sl_bytes_name (pa_stk sp0 22) 128 with "HbW")
                     as (bw2) "HbW".
                   iDestruct (sl_nm_join (pa_stk sp0 6) bn0 nf
                                with "Hnm14 Hnm2") as "HbN".
                   iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN")
                     as (bn1) "HbN".
                   iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                                with "Hbufk Hbufrest") as "HbO".
                   iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO")
                     as (bo2) "HbO".
                   (* the generation is ALREADY in hand: [iunlock] hands [gsh] back
                      (SpecIunlock's amended post), so the tail re-[ilock]s under the
                      very generation the [ity_shot] above names. *)
                   iDestruct (wp_next_shift (b := true) (CIDa := CID0)
                                (CIDb := CID50) ltac:(wp_next_chain)
                                with "Hcont") as "Hcont".
                   sl_own_transport CID48 CID50 eb pj b.
                   assert (Hu3f : (sl_u3f w1 w2 <= n2)%nat)
                     by exact (sl_cnt_u3f w1 w2 c1 n2 Hu2 (proj1 Hn2)).
                   assert (Hiu2 : (iput_units <= n2)%nat)
                     by exact (sl_bad_iput w1 w2 n2 Hu3f).
                   destruct n2 as [| c2];
                     [exfalso; unfold iput_units in Hiu2; lia |].
                   iApply (Tails.sl_tail_bad (CID0 := CID50) gs j gl gu gd gk pd
                             pav pu bn g gfs gi cn gtl gil gisl cov logstart
                             bmapstart inodestart nib size dev kk
                             (qq/2)%Qp (qq/2)%Qp gsh inum
                             (di_type (sl_incnl dn)) c2 Sb2
                             pid (DfracOwn (1/4)) dqb dqs
                             m T3 sp0 K eb b lks bn1 bw2 bo2
                             (upd_upt V P2) ltac:(exact Kil) ltac:(exact Kiupd) ltac:(exact Kiup)
                             ltac:(exact Keo) K38 Kpop Hkk Hclog Hcist Hgeom
                             Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb
                             Hcovb Hmem2'
                             ltac:(exact Hiu2)
                             Hj Hgl Hlkempty Heb ltac:(reflexivity)
                             (sl_regs_sp _ _ _ _ _ HT3regs)
                             (sl_regs_thr _ _ _ _ _ HT3regs)
                             (sl_regs_s1 _ _ _ _ _ HT3regs) Hal Hncd
                             with "Hcg Hown Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                                   Hitab Hitinv Hesck Hireg Hropen Hslkk Hkeep Hru Hshr
                                   Hshot2 Hilink Hsbb Hsbi Hbmres Hpidq Hprocs
                                   Hdev Hgeo
                                   Hdlk Hbsl HopS Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                                   [Hsbs Hir2d Hcwdref Hofiles Hftok Hcont]").
                   iEval (rewrite /wp_next).
                   iIntros (CIDy) "%Hqy". iIntros (mf)
                     "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpidq Hsbb Hsbi
                      Hbsl Hislot".
                   iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
                   iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
                   iCombine "Hpidq Hofiles" as "Hpnc".
                   iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
                   iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                                with "[Hpnc Href Hftok]") as "Hpriv";
                     [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
                   iDestruct (iref_slots_combine 2 1 with "Hir2d Hislot") as "Hir".
                   iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown Htce Hcce
                             Hpc Hbsl Hsbb Hsbi Hsbs Hir Hpriv [%]").
                   { exact Hcsf. }
                   { exact Hupt. }
                   { left. rewrite Ha0f. reflexivity. }
        * (* ---------- ARM B: the path did not resolve ---------- *)
          iDestruct "Hres" as "(%Hnaip & Hir2b)".
          iApply (wp_cbeqz_taken_s_sconf (CID := CID25) (mword_of_int (SL + 0x40))
                    (mword_of_int 62 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    Q3 (K - 38)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HQ3a0 Hnaip; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi40").
          iIntros (CID26 Hq26). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htgbc) in "Hpc".
          iDestruct (sl_buf_join (pa_stk sp0 38) bo1 pk1 Hpk1
                       with "Hbufk Hbufrest") as "HbO".
          iDestruct (sl_bytes_name (pa_stk sp0 38) 128 with "HbO") as (bo2) "HbO".
          iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN") as (bn0) "HbN".
          iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID26)
                       ltac:(wp_next_chain) with "Hcont") as "Hcont".
          sl_own_transport CID24 CID26 eb pj b.
          iApply (Tails.sl_tail_b (CID0 := CID26) gs j gl gu gd gk pd pav pu bn
                    g gfs cov logstart dev n1 pid (DfracOwn (1/4)) m Q3 sp0 K eb
 b lks u4 bn0 bw1 bo2
                    (upd_upt V P2) ltac:(exact Keo) K38 Kpop Hgeom Hj Hgl Hlkempty
                    ltac:(reflexivity)
                    (sl_regs_sp _ _ _ _ _ HQ3regs) (sl_regs_thr _ _ _ _ _ HQ3regs)
                    HQ3s2 Hal
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                          Hpidq Hprocs Hdev Hgeo Hdlk [HopS] Hf1 Hf2 Hf3 Hf4
                          HbN HbW HbO
                          [Hbsl Hsbb Hsbi Hsbs Hir1 Hir2b Hcwdref
                           Hofiles Hftok Hcont]").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { rewrite /log_op. iExists Sb1. iExact "HopS". }
          iEval (rewrite /wp_next).
          iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce
                                               Hpc Hpidq".
          iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
          iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
          iCombine "Hpidq Hofiles" as "Hpnc".
          iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
          iDestruct (proc_priv_split_cwd γf pj pid (upd_upt V P2)
                       with "[Hpnc Href Hftok]") as "Hpriv";
            [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
          iDestruct (iref_slots_combine 1 2 with "Hir1 Hir2b") as "Hir".
          iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                    Hbsl Hsbb Hsbi Hsbs Hir Hpriv [%]").
          { exact Hcsf. }
          { exact Hupt. }
          { left. rewrite Ha0f. reflexivity. }
      + (* ========== ARM A: the SECOND string did not fetch ========== *)
        iApply (wp_blt_x0_taken_s_sconf (CID := CID17) (mword_of_int (SL + 0x2c))
                  (mword_of_int 238 : mword 13) Ra0 N4 (K - 38)%nat b
                  ltac:(nz) ltac:(rgne; rewrite HN4a0 Hpr2; exact sl_m1_neg)
                  ltac:(rewrite Htg10c2c; vm_compute; reflexivity)
                  with "Hcg Hpc Hi2c").
        iIntros (CID18 Hq18). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg10c2c) in "Hpc".
        iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN") as (bn0) "HbN".
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID18)
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply (sl_epilogue (CID0 := CID18) m N4 sp0 K b pj u3 u4 bn0 bw1 bo1
                  K38 Kpop ltac:(reflexivity)
                  (sl_regs_sp _ _ _ _ _ HN4regs) (sl_regs_thr _ _ _ _ _ HN4regs)
                  (sl_regs_s1 _ _ _ _ _ HN4regs) (sl_regs_s2 _ _ _ _ _ HN4regs)
                  Hal
                  with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                        [Hown Hbsl Hsbb Hsbi Hsbs Hir Hpriv Hcont]").
        iEval (rewrite /wp_next).
        iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
        sl_own_transport CID16 CIDy eb pj b.
        iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf P2 with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                  Hsbb Hsbi Hsbs Hir Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt. }
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { rewrite Ha0f HN4a5. left. reflexivity. }
    - (* ------------ ARM A: the FIRST string did not fetch ------------ *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID10) (mword_of_int (SL + 0x18))
                (mword_of_int 258 : mword 13) Ra0 M7 (K - 38)%nat b
                ltac:(nz) ltac:(rgne; rewrite HM7a0 Hpr1; exact sl_m1_neg)
                ltac:(rewrite Htg10c18; vm_compute; reflexivity)
                with "Hcg Hpc Hi18").
      iIntros (CID11 Hq11). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg10c18) in "Hpc".
      iDestruct (sl_bytes_name (pa_stk sp0 6) 16 with "HbN") as (bn0) "HbN".
      iDestruct (sl_bytes_name (pa_stk sp0 22) 128 with "HbW") as (bw0) "HbW".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID11)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (sl_epilogue (CID0 := CID11) m M7 sp0 K b pj u3 u4 bn0 bw0 bo1
                K38 Kpop ltac:(reflexivity)
                (sl_regs_sp _ _ _ _ _ HM7regs) (sl_regs_thr _ _ _ _ _ HM7regs)
                (sl_regs_s1 _ _ _ _ _ HM7regs) (sl_regs_s2 _ _ _ _ _ HM7regs)
                Hal
                with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 HbN HbW HbO
                      [Hown Hbsl Hsbb Hsbi Hsbs Hir Hpriv Hcont]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
      sl_own_transport CID9 CIDy eb pj b.
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                Hsbb Hsbi Hsbs Hir Hpriv [%]").
      { exact Hcsf. }
      { exact Hupt1. }
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { rewrite Ha0f HM7a5. left. reflexivity. }
  Qed.

End ProofSysLinkBody.

End SysLinkProof.
