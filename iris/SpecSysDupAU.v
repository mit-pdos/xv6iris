(* SpecSysDupAU.v -- sys_dup's descriptor-level contract, stated in the
   landed fd vocabulary.  A STATEMENT FILE: definitions, structural
   lemmas, and a [Module Type] seal -- no walk, no proof against the
   machine.

   Design of record: claude-notes/design/fs-syscall-specs.md and lane W of
   claude-notes/projects/fs-syscall-specs.md.  The molds are
   SpecSysReadAU.v / SpecSysWriteAU.v (the fd-premise threading: [arg_fd]
   as a pure premise, the caller's own fragment knowledge in, exclusion by
   premise) and SpecSysOpenAU.v's [open_fd_ok] (the fd-success tail: the
   LEAST free descriptor, an EXPLICIT state list, the [us_ofile] cell
   write).  The family's SIMPLEST member, and deliberately so: dup touches
   NO fs state -- no walk, no commits, no [aview], no user memory -- so
   this file carries no AU bundle at all.  What is "atomic" about it is
   already atomic in the landed vocabulary: the descriptor table is
   thread-local and the one ghost step is [ProcInv.proc_priv_settle]'s.

   THE DRIVING CONSUMER is xv6's init.c: [dup(0); dup(0);] right after
   [open("console", O_RDWR)] returned fd 0.  After the two calls fds 0, 1
   and 2 all name the SAME open file description -- the console -- which
   is what makes the shell's stdin/stdout/stderr three names for one
   [struct file].

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecSysDup.wp_sys_dup_sconf] (R10: the landed
   contract does not move).  Same calling convention, same ambient
   premises, same threaded resources -- the frame below is
   [wp_sys_dup_sconf_body] premise for premise -- with the fd side
   SHARPENED at both ends:

   - IN: the landed [fd_frags_any] becomes [fd_frags] at an EXPLICIT
     state list [sts] (the sanctioned move -- FdSlots' header: "a client
     that wants to state a DELTA takes [fd_frags] at an explicit [sts]
     instead; that is a change of parameter at the holder, not a
     re-plumb"), plus the two pure premises of the family pattern:
     [arg_fd v (pv_ofile (us_V U)) = Some (fd0, fv)] (argument 0 names
     descriptor [fd0], whose cell holds [fv]) and
     [sts !! fd0 = Some (FdOpen rb wb t)] (the caller's own row: the
     source descriptor is OPEN, at any [fdtype] -- files, devices and
     pipes all dup).
   - OUT: the success arm returns the bundle at
     [<[fd1 := FdOpen rb wb t]> sts] -- the source's row UNTOUCHED (it is
     still [sts]'s, and [fd1 <> fd0]), the NEW descriptor's row at the
     VERY SAME state -- beside the landed cell write
     [us_ofile U fd1 fv].

   ==== THE SAME OPEN FILE DESCRIPTION, AND WHERE IT IS SAID ===========

   The crucial semantic sentence: after a successful dup, [fd0] and [fd1]
   name the same [struct file] -- the same OPEN FILE DESCRIPTION, hence a
   SHARED offset.  Where each half lives:

   - AT THE ARRAY ([pv_ofile], the sharp fact): the success arm's block
     is [proc_priv ... (us_ofile U fd1 fv)] with [fv] THE PREMISE'S OWN
     WORD -- the destination cell now holds the very pointer the source
     cell holds.  [dup_same_cell] below spells it as the two lookups:
     the updated array reads [Some fv] at BOTH [fd0] and [fd1].  This is
     the landed post's own content, relayed (the landed success arm
     already writes [fv] into the new cell); nothing new is minted.
   - AT THE GHOST LEVEL (the client-visible echo): both rows of the
     returned bundle read [FdOpen rb wb t] ([dup_rows_both]).  Stated
     honestly: an EQUAL [fdstate] does not by itself pin an equal file
     description -- two separate open()s of one inum have equal states
     too -- so the fdstate-level fact is the echo, and the [fv] cell tie
     above is the identity.  A dedicated file-description carrier is the
     offset seam's business (owner question 3).
   - THE SHARED OFFSET has no client-facing carrier to state it on:
     [f->off] lives in [fcontent] behind [file_ref] (lane A item (iv),
     the offset seam, still owed).  Its CONSUMER is already landed:
     SpecSysWriteAU's per-chunk-EXISTENTIAL offset honesty is priced
     exactly on "the struct file is SHARED (dup, fork)" -- this contract
     is the syscall that makes that sharing real, and the write AU's
     stance is the one that stays honest against it.

   ==== THE ARMS, AGAINST SpecSysDup's THREE ===========================

   The landed [sys_dup_post] has three arms; this form has TWO, because
   the bad-fd arm is REFUTED BY PREMISE (the family pattern, read/write
   AU verbatim: [arg_fd = Some] is the caller's own trapframe argument
   against its own array, so the premise costs nothing and argfd cannot
   fail under it).  The remaining split is [fd_frees], also
   caller-computable, so which arm runs is DETERMINED (the landed
   stance):

   ret = fd1 (the LEAST free descriptor, [fd_frees]'s head):
     [proc_priv] back at [us_ofile U fd1 fv], the bundle back at
     [<[fd1 := FdOpen rb wb t]> sts], and the freed row's old state
     exposed ([sts !! fd1 = Some FdClosed] -- the prover learns it from
     [ofile_slot]'s null-arm authority against the bundle's fragment,
     so exposing it is free).
   ret = -1 (the table is full, [fd_frees = []]):
     everything back exactly as handed in -- xv6 takes no reference on
     this path, and the block never even splits.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NO REFCOUNT.  filedup's [f->ref++] is internal bookkeeping: the
   fraction [file_ref] splits is existentially swallowed by [ofile_slot]
   on both ends ([SpecSysDup]'s header, THE FRACTION IS NOT OBSERVABLE --
   which is precisely what lets dup be called any number of times).
   NOTHING ABOUT fs STATE: no observation fires, because dup reads and
   writes no inode, no directory, no byte -- there is no instant to
   linearize.  NOTHING ABOUT USER MEMORY: dup copies none, and the
   continuation accordingly binds NO [M']/[P'] (the landed continuation's
   own shape, kept verbatim -- contrast the read/write frames).  And NO
   STABLE COROLLARY -- there is nothing to stabilize: no commit closure
   exists whose receipts a share could pin.

   ==== WHAT THE PROVER OWES ===========================================

   1. THE LANDED WALK, RE-TARGETED: ProofSysDup's own proof (argfd, the
      loan [proc_priv_lend], fdalloc on the split block, filedup, the
      settle) with the bundle EXPLICIT: [FdSlots.fd_frags_acc] at [fd1]
      opens the row (its state learned [FdClosed] by [fd_st_agree]
      against the null cell's authority -- [fd_frees_head] names the
      cell, [ofile_slot_null] its authority half), and
      [proc_priv_settle]'s payout closes it back at [FdOpen rb wb t];
      the insert-shaped give-back is [fd_frags_acc]'s own wand.
   2. THE SOURCE ROW'S AGREEMENT: [proc_priv_lend]'s authority for [fd0]
      against the premise row -- [fd_st_agree] turns the loan's abstract
      [st <> FdClosed] into THE [FdOpen rb wb t] the premise names, which
      is the state filedup's [file_ref] rides at.  The source's fragment
      never leaves the bundle: the loan runs on the authority half alone,
      so the row survives to the postcondition untouched.
   3. THE HEAD RELAY: fdalloc's least-free fact into the arm key
      ([fd_frees]'s head is [fd1]); [fd1 < NOFILE] from [fd_frees_head]
      + [proc_priv]'s length invariant, which is what [fd_frags_acc]
      wants.
   4. THE -1 ARM: fdalloc's full-table exit with the bundle handed back
      as received (the landed arm 2, at the explicit bundle).

   ==== OPEN QUESTIONS FOR THE OWNER ===================================

   1. The success arm does NOT expose the popped free list
      ([fd_frees (pv_ofile (us_V (us_ofile U fd1 fv))) = l]): it is
      caller-derivable, purely -- [SpecFdalloc.fd_frees_insert] at
      [fv <> 0] ([arg_fd_lookup]) over [dup_same_cell]'s array reading --
      so exposing it would be redundant vocabulary.  Confirm, or prefer
      it spelled in the arm as the open/pipe composition will want it?
   2. The EXPLICIT-[sts] premise (vs open's [fd_frags_any] in +
      existential [sts] out): chosen because dup's driving caller knows
      its table exactly and the give-back "your rows, plus one" is the
      whole point.  A caller that does not know its table can still weaken
      in ([fd_frags_any_acc] is not enough -- it opens one row -- but any
      caller holding the bundle holds it AT some [sts]).  Confirm the
      asymmetry with open is intended.
   3. The same-open-file-description fact at the ghost level is the
      [fv]-cell tie plus the equal-state echo (header).  When the offset
      seam (lane A item (iv)) lands, its carrier will presumably KEY on
      the file description -- worth designing that carrier so dup's
      success arm can hand back two names for one key, or leave dup's
      story at the cell tie permanently?

   ==== INIT'S INSTANTIATION (the driving consumer), in two lines ======

   After [open("console", O_RDWR)] typed fd 0 ([SpecSysOpenAU]'s device
   arm: [sts0] with row 0 = [FdOpen true true (FdDevice 1)], the console
   cell [fv]), [dup(0)] runs at [fd0 = 0, rb = wb = true,
   t = FdDevice 1]: [fd_frees]'s head is 1, so ret = 1 and the bundle
   returns with rows 0 AND 1 at [FdOpen true true (FdDevice 1)]
   ([dup_rows_both]), both cells holding [fv] ([dup_same_cell]); the
   second [dup(0)] repeats the move at head 2 -- fds 0, 1, 2: one console.

   BINDERS: the section context is [SpecSysDup]'s verbatim ([GenId]
   because the arms carry [proc_priv]); no fs-side class is bound because
   no fs-side resource appears.  [dup_fd_frags_any] restates
   [SpecSysOpenAU.open_fd_frags_any] locally rather than importing it:
   that file's section binds the whole FsAbs stack ([pavG], the live Γ),
   none of which this no-fs contract should drag in. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecArgfd SpecFdalloc.
Require Import SpecSysDup.     (* the landed contract this file states a
                                  parallel form beside; [sys_dup_post],
                                  [sys_dup_stack] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Require Import TsoCtx.
Local Open Scope Z_scope.


(* ===================================================================== *)
(*  1.  THE PURE TIES: one pointer, two names                             *)
(* ===================================================================== *)

(* the source and the destination are DIFFERENT descriptors: the source's
   cell is non-null ([arg_fd]'s shape), the destination's is null
   ([fd_frees]'s head names a free cell) *)
Lemma dup_src_ne_dst (v : mword 64) (fs : list (mword 64))
    (fd0 fd1 : nat) (fv : mword 64) (l : list nat) :
  arg_fd v fs = Some (fd0, fv) ->
  fd_frees fs = fd1 :: l ->
  fd0 <> fd1.
Proof.
  intros Ha Hf.
  destruct (arg_fd_lookup v fs fd0 fv Ha) as (_ & Hlk0 & Hnz & _).
  pose proof (fd_frees_head fs fd1 l Hf) as Hlk1.
  intros ->. congruence.
Qed.

(* THE CELL TIE (header: THE SAME OPEN FILE DESCRIPTION): after the
   success arm's [us_ofile] write, the array holds the ONE pointer [fv]
   at BOTH descriptors -- the source untouched, the destination freshly
   written.  Pure, so a caller reads it off the arm with no resource. *)
Lemma dup_same_cell (U : ustate) (v fv : mword 64) (fd0 fd1 : nat)
    (l : list nat) :
  arg_fd v (pv_ofile (us_V U)) = Some (fd0, fv) ->
  fd_frees (pv_ofile (us_V U)) = fd1 :: l ->
  pv_ofile (us_V (us_ofile U fd1 fv)) !! fd0 = Some fv
  /\ pv_ofile (us_V (us_ofile U fd1 fv)) !! fd1 = Some fv.
Proof.
  intros Ha Hf.
  destruct (arg_fd_lookup _ _ _ _ Ha) as (_ & Hlk0 & Hnz & _).
  pose proof (fd_frees_head _ _ _ Hf) as Hlk1.
  pose proof (dup_src_ne_dst _ _ _ _ _ _ Ha Hf) as Hne.
  assert (Hpv : pv_ofile (us_V (us_ofile U fd1 fv))
                = <[fd1 := fv]> (pv_ofile (us_V U))) by reflexivity.
  rewrite Hpv. split.
  - rewrite list_lookup_insert_ne; [exact Hlk0 | congruence].
  - apply list_lookup_insert. eapply lookup_lt_Some. exact Hlk1.
Qed.

(* the ghost-level echo, at the bundle's state list: writing the source's
   state into the freed row leaves BOTH rows reading it.  [fd0 <> fd1]
   comes from the STATES alone -- the source row is open where the freed
   row is closed -- so this needs neither [arg_fd] nor [fd_frees]. *)
Lemma dup_frags_rows (sts : list fdstate) (fd0 fd1 : nat)
    (st st1 : fdstate) :
  sts !! fd0 = Some st -> sts !! fd1 = Some st1 -> fd0 <> fd1 ->
  <[fd1 := st]> sts !! fd0 = Some st
  /\ <[fd1 := st]> sts !! fd1 = Some st.
Proof.
  intros H0 H1 Hne. split.
  - rewrite list_lookup_insert_ne; [exact H0 | congruence].
  - apply list_lookup_insert. eapply lookup_lt_Some. exact H1.
Qed.

Lemma dup_rows_both (sts : list fdstate) (fd0 fd1 : nat)
    (rb wb : bool) (t : fdtype) :
  sts !! fd0 = Some (FdOpen rb wb t) ->
  sts !! fd1 = Some FdClosed ->
  <[fd1 := FdOpen rb wb t]> sts !! fd0 = Some (FdOpen rb wb t)
  /\ <[fd1 := FdOpen rb wb t]> sts !! fd1 = Some (FdOpen rb wb t).
Proof.
  intros H0 H1.
  assert (Hne : fd0 <> fd1) by congruence.
  exact (dup_frags_rows sts fd0 fd1 _ FdClosed H0 H1 Hne).
Qed.

(* ===================================================================== *)
(*  2.  THE ARMS                                                          *)
(* ===================================================================== *)

Section SpecSysDupAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  (* [GenId], for [ProcInv.proc_priv]'s own index (SpecSysDup's note) *)
  Context `{GEN : GenId}.

  (* the sharpened bundle implies the landed shape
     ([SpecSysOpenAU.open_fd_frags_any] restated locally -- header,
     BINDERS) *)
  Lemma dup_fd_frags_any (γ : gname) (sts : list fdstate) :
    fd_frags γ sts ⊢ fd_frags_any γ.
  Proof. rewrite /fd_frags_any. iIntros "H". by iExists sts. Qed.

  (* sys_dup's result, keyed by the returned a0.  TWO arms where the
     landed post has three: the bad-fd arm is refuted by the [arg_fd]
     premise (header, THE ARMS).  Which arm runs is a function of
     [fd_frees] over the caller's own array -- the landed determinism,
     kept. *)
  Definition sys_dup_au_post `{XI : CurCtx} (γf : gname) (p : mword 64) (pid : mword 32)
      (U : ustate) (fd0 : nat) (fv : mword 64)
      (rb wb : bool) (t : fdtype) (sts : list fdstate)
      (r : mword 64) : iProp Σ :=
    ((* the table is full.  xv6 takes no reference on this path, so
        everything comes back exactly as handed in -- the bundle at the
        caller's OWN [sts], not an existential. *)
     (⌜r = (mword_of_int (-1) : mword 64) /\
       fd_frees (pv_ofile (us_V U)) = []⌝ ∗
      proc_priv γf p pid U ∗ fd_frags (pv_fdg (us_V U)) sts)
     ∨
     (* duplicated: the least free descriptor now names the SAME file the
        source does -- the cell write carries the premise's own [fv]
        ([dup_same_cell] is the two-lookup reading), and the bundle
        returns with the new row at the source's state and every other
        row untouched ([dup_rows_both]). *)
     (∃ (fd1 : nat) (l : list nat),
        ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64) /\
         fd_frees (pv_ofile (us_V U)) = fd1 :: l /\
         sts !! fd1 = Some FdClosed⌝ ∗
        proc_priv γf p pid (us_ofile U fd1 fv) ∗
        fd_frags (pv_fdg (us_V U)) (<[fd1 := FdOpen rb wb t]> sts)))%I.

  (* SANITY: under the frame's own premise the arms IMPLY the landed
     [sys_dup_post] -- the parallel form never contradicts the landed
     contract (arm 1 there is unreachable, arms 2/3 are these two with
     the bundle weakened through [dup_fd_frags_any]). *)
  Lemma sys_dup_au_post_sound `{XI : CurCtx} (γf : gname) (p : mword 64) (pid : mword 32)
      (U : ustate) (v fv : mword 64) (fd0 : nat)
      (rb wb : bool) (t : fdtype) (sts : list fdstate) (r : mword 64) :
    arg_fd v (pv_ofile (us_V U)) = Some (fd0, fv) ->
    (* THE SOURCE ROW, TIED TO THE TABLE.  The AU form names the source's
       state as the parameters [rb wb t]; the landed post says the
       destination lands at [sts !!! fd0].  This premise is what identifies
       the two, and it is the frame's own -- an AU caller knows its source
       descriptor's state, since that is the whole premise of the AU form
       (this file's header, point 2 of WHAT THE PROVER OWES). *)
    sts !! fd0 = Some (FdOpen rb wb t) ->
    sys_dup_au_post γf p pid U fd0 fv rb wb t sts r
    ⊢ sys_dup_post γf p pid U sts v r.
  Proof.
    iIntros (Ha Hsrc) "[[[%Hr %Hfr] [Hp Hb]] |
                   (%fd1 & %l & (%Hr & %Hfr & %Hcl) & Hp & Hb)]".
    - iRight. iLeft. iExists fd0, fv.
      iSplitR.
      { iPureIntro. split; [exact Hr | split; [exact Ha | exact Hfr]]. }
      iFrame "Hp Hb".
    - iRight. iRight. iExists fd0, fd1, fv, l.
      iSplitR.
      { iPureIntro. split_and!;
          [exact Hr | exact Ha | exact Hfr | exact Hcl]. }
      rewrite (list_lookup_total_correct sts fd0 (FdOpen rb wb t) Hsrc).
      iFrame "Hp Hb".
  Qed.

End SpecSysDupAU.

(* [fd_frags] is a big-op body, and it rides both arms: sealed, per the
   family convention (durable-notes; optimization.md, "a big-op body is
   the predictor"). *)
Global Typeclasses Opaque sys_dup_au_post.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecSysDup's frame + the sharpened fd side  *)
(* ===================================================================== *)

(* [SpecSysDup.wp_sys_dup_sconf_body]'s premises and threaded resources
   VERBATIM (R10 -- the landed calling convention, not a new one), with
   the fd side sharpened (header: WHAT THIS CONTRACT IS): the two pure
   fd premises added, [fd_frags_any] replaced by the explicit bundle, and
   the landed post replaced by the two arms (which imply it,
   [sys_dup_au_post_sound]).  The continuation binds NO [M']/[P']: dup
   copies no user memory, exactly as the landed continuation says. *)
Definition wp_sys_dup_au_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γl γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (v : mword 64) (pid : mword 32) (U : ustate) (b : bool) (lks : gset string)
    (fd0 : nat) (fv : mword 64) (rb wb : bool) (t : fdtype)
    (sts : list fdstate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_dup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* sys_dup reads syscall argument 0, out of the trapframe page
     [proc_priv] carries *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  (* push_off's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (sys_dup_stack <= av)%nat ->
  (* the rank bound, for filedup's "ftable" -- SpecSysDup's note verbatim *)
  locks_below lks "ftable" ->
  (* THE FD SIDE's pure half (the family pattern): argument 0 names
     descriptor [fd0] of the caller's own array, whose cell holds [fv]
     (non-null by [arg_fd]'s shape) -- so argfd cannot fail... *)
  arg_fd v (pv_ofile (us_V U)) = Some (fd0, fv) ->
  (* ...and the caller's own row for it: the source descriptor is OPEN,
     at any [fdtype] -- files, devices and pipes all dup *)
  sts !! fd0 = Some (FdOpen rb wb t) ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the ftable lock, for filedup's ghost step *)
  is_ftable γl γf -∗
  proc_priv γf p pid U -∗
  (* THE FD SIDE's resource half: the landed bundle at the caller's OWN
     state list -- row [fd0] is the premise's, row [fd1] will move *)
  fd_frags (pv_fdg (us_V U)) sts -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      sys_dup_au_post γf p pid U fd0 fv rb wb t sts
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

(* NO STABLE COROLLARY -- deliberately ABSENT rather than sealed vacuous:
   there is no commit closure here whose receipts a share could pin
   (header: WHAT IT DELIBERATELY DOES NOT SAY). *)
Module Type SYSDUP_AU.
  Parameter wp_sys_dup_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γl γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (v : mword 64) (pid : mword 32) (U : ustate) (b : bool)
      (lks : gset string)
      (fd0 : nat) (fv : mword 64) (rb wb : bool) (t : fdtype)
      (sts : list fdstate),
      wp_sys_dup_au_body γl γf m av n eb p v pid U b lks
        fd0 fv rb wb t sts.
End SYSDUP_AU.
