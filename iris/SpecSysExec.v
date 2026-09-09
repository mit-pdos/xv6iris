(* SpecSysExec.v -- sys_exec's ONE CONTRACT [SYSEXEC]: [SpecKexec]'s
   bundle and arms lifted to the syscall boundary, where the arguments
   are READ OFF THE USER IMAGE rather than handed in.  A STATEMENT FILE.

   Design of record: SpecKexec.v's header (the exec AU: the walk, the
   one observation, the caller's own u-mode WP for the program observed)
   and claude-notes/design/user-wp-slot.md (the slot, and the trap
   contract's exec arm this level feeds).

   ==== WHAT THIS CONTRACT IS ==========================================

   THE ONLY CONTRACT sys_exec has, and the only seal the dispatcher may
   take: [SysExecDefs.v] below is the vocabulary leaf
   ([K_sys_exec], [sys_exec_post]).  The frame is that file's own premise
   list row for row -- the block-layer geometry relayed to kexec, the two
   trapframe arguments, [eb = true], the fabric, the process -- with the
   bundle [EXTRA] after the process block and the armed post in the pure
   slot ([sys_exec_arms_landed] reads [sys_exec_post] back out of it).

   THE ONE THING THIS LEVEL ADDS: the path and the argument vector are
   not parameters.  sys_exec [argstr]s the path out of the user's image
   at trapframe argument 0, [fetchaddr]s each [argv[i]] at trapframe
   argument 1 and [fetchstr]s each string into a kernel page, then calls
   kexec with what it read.  So the caller's WP premise is quantified
   over what kexec may be handed ([sys_exec_slot_pre]), and the success
   arm names what it ran at.

   THE PATH IS READ.  The premise on it is [exec_path_of (us_M U) v0 pl]
   below -- the bytes of [pl] ARE the process's bytes at argument 0, with
   the NUL after them -- so a caller that knows its own image and its own
   argument 0 (init: "/init" at a known address) instantiates the bundle
   at ONE path, which is what a pinned caller's cursor needs.  It is
   [SpecArgstr]'s postcondition read through
   [SpecFetchstr.fetchstr_got] to [SpecCopyinstr.copyinstr_got], and
   [exec_path_of_bview] below is the one step.

   THE ARGV VECTOR IS STILL OWED.  The intended premise is the twin
   reading [exec_args_of (us_M U) v1 na alen afun] below, kept as the
   named upgrade target.  It is not derivable today:
   [SpecFetchaddr.fetchaddr_post] is about OWNERSHIP of the destination
   word, not its value, so the argv POINTERS are unread even though the
   strings they point at now are.  So that premise is quantified over
   every vector of the right SHAPE ([exec_args_shape]: below MAXARG,
   NUL-terminated strings within a page -- kexec's own premises) and
   nothing else.  For the init -> sh chain this loses nothing: xv6's sh
   ignores its arguments, so sh's start WP holds at every vector.  The
   upgrade is a memory-indexed [wp_fetchaddr_sconf_mem] paying out of
   [SpecCopyin.copyin_got], threaded through sys_exec's argv loop
   alongside the [copyinstr_got] the string half already carries, after
   which [sys_exec_slot_pre] moves from [exec_args_shape] to
   [exec_args_of] and every arm below is unchanged.

   THE CONTINUATION binds [(mf, P', M')] with the page-table growth
   report and an EXISTENTIAL image (milestone J item 1's staging).  The
   U-mode side's row for exec's failure is [r = -1 /\ M' = M]
   ([UsysMemOk]); tightening this frame's failure arm to same-M is an
   open item, recorded and not taken.

   ==== THE ARMS ========================================================

   ret = argc: [SpecKexec.exec_post_ok] at the block after the
   copy-ins' growth ([us_upt U P']), at the reading [na alen afun] the
   success arm exhibits.  Its arm (a) hands back [S (exec_key U' sts
   na)] -- THE PROPOSITION THE DISPATCH DEPOSITS for the new process, at
   the slot predicate [S] the whole contract is parametric in (SpecKexec
   header) -- and arm (b) the refunds.
   ret = -1: the landed failure equation on the block ([us_V U' =
   us_upt-ed V]) beside [SpecKexec.exec_post_fail]'s three-way fold,
   plus a FOURTH disjunct this level owns: sys_exec failed BEFORE kexec
   (a bad path or argv pointer, too many arguments, out of kernel
   pages), with the whole bundle back unspent -- indistinguishable from
   kexec's (i) by the return value, so folded into the same [∨].

   ==== WHERE THE PROOF PAYS EACH PIECE ================================

   1. The path reading: [exec_path_of] is [argstr]'s
      [SpecFetchstr.fetchstr_got] at trapframe argument 0, turned into a
      list by [exec_path_of_bview].  The argv shape:
      [exec_args_shape] is the walk's own loop invariant ([fetchstr]'s
      [bb_cstr] and length, the MAXARG bound) -- free.  The argv reading
      [exec_args_of] is the upgrade that is still owed (header).
   2. [SpecKexec.KEXEC] at that reading, with the bundle specialized by
      [sys_exec_slot_pre]'s ∀.
   3. The kfree/kalloc bookkeeping, shared with the blocks in
      [ProofSysExecParts].

   BINDERS: SysExecDefs's plus [ufdG] (the slot). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import Xv6Cameras.
Require Import BioDefs.
Require Import LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRefDefs.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import ByteBuf.        (* [bb_cstr]                          *)
Require Import SpecCopyinstr.  (* [copyinstr_got]: the path's content *)
Require Import PathElems.      (* [path_elems]                       *)
Require Import DirentEnc.      (* [bview]                            *)
Require Import FsAbsEra.       (* [ex_start]: the walk at ONE path    *)
Require Import FsBlocks.       (* [fs_names]                         *)
Require Import KexecDefs.      (* [MAXARG], [kexec_ok]               *)
Require Import SysExecDefs.    (* the vocabulary leaf: [K_sys_exec], [sys_exec_post] *)
Require Import UserFd.         (* [ufdG]                             *)
Require Import UexecSlot.      (* [uvis]                             *)
Require Import SysOpenDefs.  (* [namei_walk_pre_era], [aopen_commit_at] *)
Require Import SpecKexec.    (* [exec_slot_pre], [exec_post_ok], [exec_post_fail] *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.          (* LAST (FsAbs's own rule)            *)
Require Import FsBytesGamma.   (* [fs_gamma_L]                       *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE ARGUMENT VECTOR, AS A READING OF THE USER IMAGE               *)
(* ===================================================================== *)

(* the eight-byte little-endian word at [a] in the (lazy) image [M] *)
Definition uimg_word_at (M : gmap Z (bv 8)) (a : Z) (w : mword 64) : Prop :=
  forall k, (k < 8)%nat ->
    M !! (a + Z.of_nat k) = bv_to_little_endian 8 8 (bv_unsigned w) !! k.

(* THE SHAPE of an argument vector kexec accepts (its own premises):
   below MAXARG, each argument a NUL-terminated string of [alen i]
   characters ([bb_cstr]: non-NUL below, NUL at [alen i]) shorter than a
   page.  This is what the WP premise is quantified over today (header). *)
Definition exec_args_shape (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) : Prop :=
  (na < MAXARG)%nat
  /\ (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i))
  /\ (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z).

(* THE READING sys_exec performs -- the upgrade target (header): the
   shape, and [argv[0 .. na)] non-null pointers read at [av + 8 i],
   [argv[na]] NULL, each pointer naming its string's bytes in the image.

   The string bytes are indexed the way the copy loop walks them,
   [uint (add_vec_int p j)] -- the machine's own arithmetic, modulo 2^64 --
   which is the spelling [SpecCopyinstr.copyinstr_got] hands over and the
   spelling [exec_path_of] below uses, so path and argument are one reading
   at two arguments. *)
Definition exec_args_of (M : gmap Z (bv 8)) (av : mword 64)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) : Prop :=
  exec_args_shape na alen afun
  /\ (exists avf : nat -> mword 64,
        (forall i, (i <= na)%nat ->
           uimg_word_at M (bv_unsigned av + 8 * Z.of_nat i) (avf i))
        /\ (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64))
        /\ avf na = (mword_of_int 0 : mword 64)
        /\ (forall i, (i < na)%nat ->
              (forall j, (j <= alen i)%nat ->
                 M !! uint (add_vec_int (avf i) (Z.of_nat j))
                   = Some (afun i j)))).

Lemma exec_args_of_shape (M : gmap Z (bv 8)) (av : mword 64)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
  exec_args_of M av na alen afun -> exec_args_shape na alen afun.
Proof. intros [H _]. exact H. Qed.

(* THE PATH, THE SAME PAIR ONE ARGUMENT OVER.  sys_exec [argstr]s the
   path at trapframe argument 0 into a kernel page and hands kexec the
   buffer; the bundle's walk premise is therefore stated AT ONE [pl]
   ([FsAbsEra.ex_start]) under a guard on that string, and not at every
   path.  THE GUARD IS THE READING, [exec_path_of]: the shape
   ([exec_path_shape]: NUL-free, int-sized) AND the tie to the image --
   byte [j] of [pl] is the process's byte at [pv + j], counted the copy
   loop's way ([exec_args_of] above), with a NUL just past the end.  So
   the bundle is owed at the ONE path the caller actually passed, which
   is what a pinned caller's cursor needs.

   [exec_path_shape] is named separately because the reading is the pair
   and a proof usually wants one half at a time ([exec_path_of_shape]
   projects it); nothing takes the shape alone as a premise. *)
Definition exec_path_shape (pl : list (bv 8)) : Prop :=
  (Z.of_nat (length pl) < 2 ^ 31)%Z
  /\ (forall (j : nat) (b : bv 8), pl !! j = Some b ->
        b <> (mword_of_int 0 : mword 8)).

Definition exec_path_of (M : gmap Z (bv 8)) (pv : mword 64)
    (pl : list (bv 8)) : Prop :=
  exec_path_shape pl
  /\ (forall (j : nat) (b : bv 8), pl !! j = Some b ->
        M !! uint (add_vec_int pv (Z.of_nat j)) = Some b)
  /\ M !! uint (add_vec_int pv (Z.of_nat (length pl))) = Some (bv_0 8).

Lemma exec_path_of_shape (M : gmap Z (bv 8)) (pv : mword 64)
    (pl : list (bv 8)) :
  exec_path_of M pv pl -> exec_path_shape pl.
Proof. intros [H _]. exact H. Qed.

(* ...and the SHAPE supplier: the buffer sys_exec handed kexec.  [bb_cstr]
   is exactly [fetchstr]'s shape promise about it. *)
Lemma exec_path_shape_bview (plen : nat) (pfun : nat -> bv 8) :
  (Z.of_nat plen < 2 ^ 31)%Z -> bb_cstr pfun plen ->
  exec_path_shape (bview plen pfun).
Proof.
  intros Hlen [Hnn _]. split; [ by rewrite bview_length | ].
  intros j b Hb.
  destruct (decide (j < plen)%nat) as [Hj | Hj].
  - rewrite (bview_lookup plen pfun j Hj) in Hb. injection Hb as <-.
    exact (Hnn j Hj).
  - rewrite lookup_ge_None_2 in Hb; [ discriminate | rewrite bview_length; lia ].
Qed.

(* ...and the READING supplier, the one step from the syscall's own
   vocabulary.  [SpecCopyinstr.copyinstr_got] is what [argstr] relays about
   the path buffer ([SpecFetchstr.fetchstr_got]); [bview] is the same buffer
   as a list.

   The step is an index shuffle and nothing else: both sides count bytes as
   [uint (add_vec_int pv j)], the machine's own arithmetic, so there is no
   no-wrap side condition to discharge -- a user may pass any 64-bit pointer
   and the reading is about the addresses the copy loop actually touched.
   [copyinstr_got]'s [j <= plen] range covers the terminator, which is the
   third conjunct here. *)
Lemma exec_path_of_bview (M : gmap Z (bv 8)) (pv : mword 64)
    (plen : nat) (pfun : nat -> bv 8) :
  (Z.of_nat plen < 2 ^ 31)%Z ->
  bb_cstr pfun plen ->
  copyinstr_got M pv pfun plen ->
  exec_path_of M pv (bview plen pfun).
Proof.
  intros Hlen Hcstr Hgot.
  split_and!.
  - exact (exec_path_shape_bview plen pfun Hlen Hcstr).
  - intros j b Hb.
    destruct (decide (j < plen)%nat) as [Hj | Hj].
    + rewrite (bview_lookup plen pfun j Hj) in Hb. injection Hb as <-.
      exact (Hgot j ltac:(lia)).
    + rewrite lookup_ge_None_2 in Hb; [ discriminate | rewrite bview_length; lia ].
  - rewrite bview_length (Hgot plen ltac:(lia)) (proj2 Hcstr).
    f_equal. apply bv_eq. vm_compute. reflexivity.
Qed.

(* THE READING PINS THE PATH.  [exec_path_of M pv] is a FUNCTION of the
   image and the pointer: the bytes below the terminator are [M]'s, the
   terminator is at [length pl], and the shape says no earlier byte is a
   NUL -- so two readings at one [(M, pv)] have the same length and, byte
   for byte, the same content.  This is what a bundle owed at every path
   the caller MIGHT have passed reduces to at a caller whose image is
   known: the one path it did pass ([PinnedExec.v] takes
   [exec_path_of M pv pl] as its premise and answers the ∀ through this
   lemma). *)
Lemma exec_path_of_uniq (M : gmap Z (bv 8)) (pv : mword 64)
    (pl1 pl2 : list (bv 8)) :
  exec_path_of M pv pl1 -> exec_path_of M pv pl2 -> pl1 = pl2.
Proof.
  intros (Hs1 & Hb1 & Hn1) (Hs2 & Hb2 & Hn2).
  assert (Hz : bv_0 8 = (mword_of_int 0 : mword 8))
    by (apply bv_eq; vm_compute; reflexivity).
  (* the terminator of the shorter reading is a non-NUL byte of the
     longer one, which its shape forbids *)
  assert (Hcut : forall (q1 q2 : list (bv 8)),
             (forall (j : nat) (b : bv 8), q2 !! j = Some b ->
                M !! uint (add_vec_int pv (Z.of_nat j)) = Some b) ->
             (forall (j : nat) (b : bv 8), q2 !! j = Some b ->
                b <> (mword_of_int 0 : mword 8)) ->
             M !! uint (add_vec_int pv (Z.of_nat (length q1))) = Some (bv_0 8) ->
             (length q2 <= length q1)%nat).
  { intros q1 q2 Hb Hnn Hnul.
    destruct (decide (length q2 <= length q1)%nat) as [Hle | Hgt]; [ exact Hle | ].
    exfalso.
    destruct (lookup_lt_is_Some_2 q2 (length q1) ltac:(lia)) as [b Hbj].
    pose proof (Hb _ _ Hbj) as HM. rewrite Hnul in HM.
    apply Some_inj in HM. rewrite Hz in HM.
    exact (Hnn _ _ Hbj (eq_sym HM)). }
  assert (Hlen : length pl1 = length pl2).
  { pose proof (Hcut pl1 pl2 Hb2 (proj2 Hs2) Hn1) as H12.
    pose proof (Hcut pl2 pl1 Hb1 (proj2 Hs1) Hn2) as H21. lia. }
  apply list_eq. intros j.
  destruct (pl1 !! j) as [b1 |] eqn:H1.
  - destruct (lookup_lt_is_Some_2 pl2 j
                ltac:(rewrite -Hlen; exact (lookup_lt_Some _ _ _ H1)))
      as [b2 H2].
    rewrite H2. f_equal.
    pose proof (Hb1 _ _ H1) as E1. pose proof (Hb2 _ _ H2) as E2.
    rewrite E1 in E2. by apply Some_inj in E2.
  - apply lookup_ge_None in H1. symmetry.
    apply lookup_ge_None_2. lia.
Qed.

(* ===================================================================== *)
(*  2.  THE BUNDLE AND THE ARMS AT THE SYSCALL BOUNDARY                   *)
(* ===================================================================== *)

Section SysExecAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* the caller's WP, for every argument vector of the right shape
     (header: the image reading is the upgrade target; the [M av]
     parameters are kept so the upgrade moves nothing but this wand) *)
  (* A PIECE, so its two families stay BARE: [S] is what the wand
     concludes at and [Φo] is the observation receipt it consumes. *)
  (* ...and over the PATHS it may have fetched, at the same guard the walk
     premise carries, because the cursor the slot wand consumes is at the
     last hop of THAT path ([exec_slot_pre]'s [Pfin]). *)
  Definition sys_exec_slot_pre (S : uvis -> iProp Σ)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) : iProp Σ :=
    (∀ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
       (afun : nat -> nat -> bv 8),
       ⌜exec_path_of M pv pl⌝ -∗ ⌜exec_args_shape na alen afun⌝ -∗
       exec_slot_pre S (P (length (path_elems pl))) Φo na alen afun sts)%I.

  (* Both one-shot pieces at their pairs ([SpecKexec.exec_au_pre]'s
     shape, at the argument-shape-quantified slot wand). *)
  Definition sys_exec_au_pre (Fs : pfam Σ (uvis -> iProp Σ)) Γ
      (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜exec_path_of M pv pl⌝ -∗ ex_start γfs cw P Pmiss pl)
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ pf_at (fun S => sys_exec_slot_pre S P Fo.(pf_recv) M pv av sts) Fs)%I.

  (* non-expansive in the slot predicate, as [SpecKexec.exec_au_pre_ne]:
     what UexecExecInst.v's instance at the fixpoint variable needs *)
  Lemma sys_exec_slot_pre_ne (n : nat) (S S' : uvis -d> iPropO Σ)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    S ≡{n}≡ S' ->
    sys_exec_slot_pre S P Φo M pv av sts
    ≡{n}≡ sys_exec_slot_pre S' P Φo M pv av sts.
  Proof.
    intros HS. rewrite /sys_exec_slot_pre.
    apply bi.forall_ne; intros pl.
    apply bi.forall_ne; intros na. apply bi.forall_ne; intros alen.
    apply bi.forall_ne; intros afun. apply bi.wand_ne; [reflexivity |].
    apply bi.wand_ne; [reflexivity |].
    exact (exec_slot_pre_ne n S S' (P (length (path_elems pl)))
             Φo na alen afun sts HS).
  Qed.

  Lemma sys_exec_au_pre_ne (n : nat) (S S' : uvis -d> iPropO Σ) (Rs : iProp Σ)
      Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    S ≡{n}≡ S' ->
    sys_exec_au_pre (MkPfam S Rs) Γ γfs cw P Pmiss Fo M pv av sts
    ≡{n}≡ sys_exec_au_pre (MkPfam S' Rs) Γ γfs cw P Pmiss Fo M pv av sts.
  Proof.
    intros HS. rewrite /sys_exec_au_pre /pf_at. cbn [pf_recv pf_refund].
    by rewrite (sys_exec_slot_pre_ne n S S' P Fo.(pf_recv) M pv av sts HS).
  Qed.

  (* ret = -1: sys_exec's own early exits (the whole bundle back) folded
     with kexec's three-way fold at the reading it ran at *)
  Definition sys_exec_post_fail (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) : iProp Σ :=
    (sys_exec_au_pre Fs Γ γfs cw P Pmiss Fo M pv av sts
     ∨ (∃ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
          (afun : nat -> nat -> bv 8),
          ⌜exec_path_of M pv pl⌝ ∗ ⌜exec_args_shape na alen afun⌝ ∗
          exec_post_fail Fs Γ γfs cw P Pmiss Fo pl na alen afun sts))%I.

  (* the armed disjunction on the block after the copy-ins' growth [V]
     and the returned a0; [M] is the image the arguments were read from *)
  Definition sys_exec_arms (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (pj : mword 64) (pid : mword 32)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (V : pprivate) (r : mword 64) : iProp Σ :=
    (∃ U' : ustate,
       proc_priv γf pj pid U' ∗
       ((⌜r = (mword_of_int (-1) : mword 64) /\ us_V U' = V /\ us_M U' = M⌝
         ∗ sys_exec_post_fail Fs Γ γfs cw P Pmiss Fo M pv av sts)
        ∨ (∃ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
             (afun : nat -> nat -> bv 8),
             ⌜exec_path_of M pv pl⌝ ∗ ⌜exec_args_shape na alen afun⌝ ∗
             exec_post_ok Fs Γ P Fo pl na alen afun sts (MkUstate V M) U' r)))%I.

  (* SANITY: the arms imply the landed [SysExecDefs.sys_exec_post] *)
  Lemma sys_exec_arms_landed (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (pj : mword 64) (pid : mword 32)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (V : pprivate) (r : mword 64) :
    sys_exec_arms Fs Γ γfs cw γf pj pid P Pmiss Fo M pv av sts V r ⊢
      sys_exec_post γf pj pid V r.
  Proof.
    rewrite /sys_exec_arms /sys_exec_post.
    iIntros "H". iDestruct "H" as (U') "[Hp [[(%Hr & %HV & _) _] | H]]".
    - iExists U', 0%nat, (fun _ => 0%nat),
        (mword_of_int 0), (mword_of_int 0), (mword_of_int 0).
      iFrame "Hp". iPureIntro. left. split; [exact Hr | exact HV].
    - iDestruct "H" as (pl na alen afun) "[_ [_ H]]".
      iDestruct (exec_arms_landed Fs Γ γfs cw P Pmiss Fo pl na alen afun sts
                   (MkUstate V M) U' r with "[H]") as %(entry & spv & szv' & Hok).
      { rewrite /exec_arms. iRight. iExact "H". }
      iExists U', na, alen, entry, spv, szv'. iFrame "Hp". iPureIntro. exact Hok.
  Qed.

End SysExecAU.

Global Typeclasses Opaque sys_exec_au_pre sys_exec_post_fail sys_exec_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SysExecDefs's frame + the AU                *)
(* ===================================================================== *)

Definition wp_sys_exec_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (Fs : pfam Σ (uvis -> iProp Σ))                  (* the slot predicate the caller's WP concludes at *)
    (γf : gname)                           (* ftable, kalloc      *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (dqb dqs : dfrac)
    (v0 v1 : mword 64)                        (* syscall arguments 0 and 1 *)
    (pid : mword 32) (U : ustate) (sts : list fdstate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_exec in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let Γfs := fs_gamma_L fsc_fs in
  (K_sys_exec <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  eb = true ->
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  pv_tf (us_V U) !! tf_arg_idx 1 = Some v1 ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  fs_fabric gs pd pav pu -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  bslots 3 -∗
  kalloc_env fsc_kalloc None -∗
  iref_slots 2 -∗
  proc_priv γf pj pid U -∗
  (* ---- THE BUNDLE, the one addition to the premise list the vocabulary
     leaf's header describes: the arguments are read off THIS image at
     argument 1 ---- *)
  sys_exec_au_pre Fs Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Fo (us_M U) v0 v1 sts -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd) (M' : gmap Z (bv 8)),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      bslots 3 -∗
      kalloc_env fsc_kalloc None -∗
      iref_slots 2 -∗
      (* the armed post: the block after the copy-ins' growth, the
         arguments as read off the entry image, and -- on success at a
         loadable file -- the caller's slot at the resume key *)
      sys_exec_arms Fs Γfs fsc_fs (pv_cwi (us_V U)) γf pj pid P Pmiss Fo (us_M U) v0 v1 sts
        (upd_upt (us_V U) P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSEXEC.
  Parameter wp_sys_exec_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (Fs : pfam Σ (uvis -> iProp Σ))
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (U : ustate) (sts : list fdstate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)),
      wp_sys_exec_sconf_body Fs γf gs j gl pd pav pu dqb dqs v0 v1 pid U sts
        m K eb b lks P Pmiss Fo.
End SYSEXEC.
