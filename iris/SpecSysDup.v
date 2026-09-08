(* SpecSysDup.v -- the public interface of sys_dup(), stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     uint64 sys_dup(void) {
       struct file *f; int fd;
       if (argfd(0, 0, &f) < 0) return -1;
       if ((fd = fdalloc(f)) < 0) return -1;
       filedup(f);
       return fd;
     }

   @ KernelSyms.sys_dup = 0x80004bd6, 24 instructions (a 48-byte frame; the
   [struct file *f] local lives at s0-40, [f] rides in the callee-saved s1 and
   the descriptor in s2 across the filedup call).  Decode: CodeSysDup.v.

   THE WINDOW, AND WHY IT IS THE INTERESTING PART.  [fdalloc] stores the
   pointer BEFORE [filedup] bumps the count, so between the two calls two
   descriptors name one [struct file] and only one reference exists.  That is
   not a soundness problem -- the fd table is thread-local, so no other core
   can observe it -- but nothing in [ProcInv.proc_priv] can STATE it: the
   destination's cell names a file and [ofile_slot] then demands a reference
   that is not there.

   Worse, the reference [filedup] needs in hand is the SOURCE descriptor's, so
   that descriptor is payloadless too -- and it must stay that way ACROSS the
   fdalloc call, which itself wants the descriptor array.  A borrow with
   [ProcInv.proc_priv_ofile] cannot span the call (its wand demands the whole
   slot back first), which is exactly why the block is split at the fd table
   and the deficit tracked in [ProcInv.proc_ofiles_owe].  sys_dup is the
   function that forced that design; see claude-notes/design/file-table.md.

   THE LEDGER BALANCES WITH ZERO ALLOWANCE, and that is worth stating: the
   [fd_slot] fdalloc releases when it fills the destination descriptor is
   exactly the one [filedup] consumes to pay for the higher count.  So sys_dup
   needs none of the process's [FdSlots.FDSPARE] units -- unlike sys_open (one)
   or sys_pipe (two), which hold references in locals before installing them.
   The fd-slot conservation law never even wobbles here.

   DETERMINISM.  Which of the three exits runs is a function of the syscall
   argument and the process's own descriptor array, both of which the caller
   knows, so the postcondition says so ([SpecArgfd.arg_fd] and
   [SpecFdalloc.fd_frees]) rather than offering an unconstrained "duplicated
   it, or didn't": a kernel that always returned -1 would not satisfy this
   spec.  And the descriptor sys_dup returns is the LEAST free one, naming the
   very pointer the source held.

   THE FRACTION IS NOT OBSERVABLE, deliberately.  filedup halves the source's
   [file_ref] fraction, but [ofile_slot] existentially quantifies it, so the
   postcondition never mentions [q] -- which is what lets sys_dup be called any
   number of times without the spec accumulating halvings.

   ==== ONE CONTRACT ===================================================

   [Module Type SYSDUP] is sys_dup's only seal and [sys_dup_post] its only
   reading.  A caller that knows the row of the descriptor argument 0 names
   reads the post SHARPENED -- the bad-fd arm refuted by its own premise, the
   destination's new row spelled [FdOpen rb wb t] rather than [sts !!! fd0],
   the source pointer [fv] named rather than existential -- and that reading
   is the DERIVED [sys_dup_post_sharp], never a second contract against the
   code.  The premise-free post is what the seal states because it is what
   the DISPATCHER can call: a user's argument 0 may name no open descriptor
   at all, so a contract premised on [arg_fd ... = Some _] would cover only
   part of the syscall.  Nothing about dup is atomic in the file-system
   sense -- there is no bundle to hand in -- so the descriptor row IS the
   whole client-facing content.

   THE DRIVING CONSUMER is xv6's init.c: [dup(0); dup(0);] right after
   [open("console", O_RDWR)] returned fd 0.  After the two calls fds 0, 1 and
   2 all name the SAME open file description -- the console -- which is what
   makes the shell's stdin/stdout/stderr three names for one [struct file].
   Each call runs at [fd_frees]'s head (1, then 2) and returns the bundle
   with the new row at the source's state.

   ==== THE SAME OPEN FILE DESCRIPTION, AND WHERE IT IS SAID ===========

   After a successful dup, [fd0] and [fd1] name one [struct file] -- one open
   file description, hence a shared offset.  Each half of that sentence has
   its own home:

   - AT THE ARRAY ([pv_ofile], the sharp fact): the success arm's block is
     [proc_priv ... (us_ofile U fd1 fv)] with [fv] the pointer [arg_fd] read
     out of the SOURCE cell, so the destination cell now holds the very word
     the source cell holds.  [dup_same_cell] below spells it as the two
     lookups.
   - AT THE GHOST LEVEL (the client-visible echo): both rows of the returned
     bundle read the source's state ([dup_rows_both]).  Stated honestly, an
     EQUAL [fdstate] does not by itself pin an equal file description -- two
     separate opens of one inum have equal states too -- so the fdstate-level
     fact is the echo and the [fv] cell tie above is the identity.
   - THE SHARED OFFSET has no client-facing carrier: [f->off] lives in
     [fcontent] behind [file_ref].  Its consumer is landed all the same --
     the write chain's per-chunk EXISTENTIAL offset is priced exactly on the
     struct file being shared (dup, fork), and dup is the syscall that makes
     that sharing real.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NO REFCOUNT: filedup's [f->ref++] is internal bookkeeping, swallowed by
   [ofile_slot]'s existential fraction on both ends (THE FRACTION IS NOT
   OBSERVABLE, above).  NOTHING ABOUT fs STATE: dup reads and writes no
   inode, no directory, no byte, so there is no instant to linearize and no
   observation to fire.  NOTHING ABOUT USER MEMORY: dup copies none, and the
   continuation accordingly binds no [M']/[P'] -- contrast the read and write
   frames.  NO STABLE COROLLARY: there is nothing to stabilize, since no
   commit closure exists whose receipts a share could pin. *)
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
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Require Import TsoCtx.
Local Open Scope Z_scope.


(* sys_dup's own frame is 6 slots (addi sp,sp,-48); argfd wants 24 below it,
   fdalloc 14 and filedup 14, so argfd sets the bound. *)
Notation sys_dup_stack := (30%nat) (only parsing).

(* ===================================================================== *)
(*  THE PURE TIES: one pointer, two names                                 *)
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

(* THE CELL TIE (header: THE SAME OPEN FILE DESCRIPTION): after the success
   arm's [us_ofile] write, the array holds the ONE pointer [fv] at BOTH
   descriptors -- the source untouched, the destination freshly written.
   Pure, so a caller reads it off the arm with no resource. *)
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
   state into the freed row leaves BOTH rows reading it.  [fd0 <> fd1] comes
   from the STATES alone -- the source row is open where the freed row is
   closed -- so this needs neither [arg_fd] nor [fd_frees]. *)
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
Section SpecSysDup.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  (* [GenId], for [ProcInv.proc_priv]'s own index: the private block now
     carries [FirstTok.first_tok], whose boot arm names [gen_cert].  The
     definitions below mention the block, so the section has to bind it. *)
  Context `{GEN : GenId}.

  (* sys_dup's result, keyed by the returned a0.  THREE arms, because there are
     two ways to fail and they are distinguishable: no such descriptor, or no
     room for another one.  Both leave the process exactly as it was. *)
  (* THE fd-STATE FRAGMENT BUNDLE rides in and out on all three arms.  Only
     the third spends it: duplicating opens a NEW descriptor, so that
     descriptor's authority has to move from [FdClosed] to the source file's
     type ([ProcInv.proc_priv_settle]).  The SOURCE descriptor's state does
     not change and its authority round-trips through the loan, which is why
     one bundle access is enough for a two-descriptor syscall. *)
  (* THE TABLE IS NAMED, and the three arms differ in exactly one row.  The
     two failure arms hand [sts] back untouched; the success arm hands back
     [<[fd1 := sts !!! fd0]> sts] -- the DESTINATION becomes a COPY of the
     SOURCE, which is what dup means at this level: filedup only bumps
     [f->ref], so the two descriptors name one [struct file] and therefore
     have one state.  The source row is unchanged, and [list_insert] says
     every other row is too.  This is [UsysMemOk.usys_fd_ok]'s dup row.

     [sts !!! fd0] RATHER THAN A PREMISE naming the source's state: the
     total lookup needs nothing of the caller and it is the form the
     syscall table already uses, so the two compose without a translation
     step -- and it is what keeps the post callable where the caller knows
     nothing about the descriptor, which is every dispatch.  A caller that
     DOES know the row reads the premise form off [sys_dup_post_sharp].
     The proof pays for the total lookup once, with [FdSlots.fd_st_agree]
     against the loan's own authority -- see [ProofSysDup]. *)
  Definition sys_dup_post `{XI : CurCtx} (γf : gname) (p : mword 64) (pid : mword 32)
      (U : ustate) (sts : list fdstate) (v : mword 64) (r : mword 64) : iProp Σ :=
    ((* argfd said no: the argument is not an open descriptor *)
     ⌜r = (mword_of_int (-1) : mword 64) /\ arg_fd v (pv_ofile (us_V U)) = None⌝ ∗
       proc_priv γf p pid U ∗ fd_frags (pv_fdg (us_V U)) sts
     ∨
     (* the descriptor exists but the table is full.  xv6 does NOT close
        anything here -- it never took a reference -- so the block is
        untouched, and the [fd_slot] fdalloc would have released was never
        released either. *)
     (∃ (fd0 : nat) (fv : mword 64),
        ⌜r = (mword_of_int (-1) : mword 64) /\
         arg_fd v (pv_ofile (us_V U)) = Some (fd0, fv) /\
         fd_frees (pv_ofile (us_V U)) = []⌝ ∗
        proc_priv γf p pid U ∗ fd_frags (pv_fdg (us_V U)) sts)
     ∨
     (* duplicated: the least free descriptor now names the same file the
        source did, and the count behind it has gone up by one. *)
     (∃ (fd0 fd1 : nat) (fv : mword 64) (l : list nat),
        ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64) /\
         arg_fd v (pv_ofile (us_V U)) = Some (fd0, fv) /\
         fd_frees (pv_ofile (us_V U)) = fd1 :: l /\
         (* ...AND THE DESTINATION SLOT WAS CLOSED -- see [SpecSysOpen]'s
            note on the same conjunct.  Learned, not guessed: fdalloc hands
            its authority back still at [FdClosed] and [fd_st_agree] against
            the row the bundle yields turns that into this. *)
         sts !! fd1 = Some FdClosed⌝ ∗
        proc_priv γf p pid (us_ofile U fd1 fv) ∗
        fd_frags (pv_fdg (us_V U)) (<[fd1 := sts !!! fd0]> sts)))%I.

  (* ---- THE SHARPENED READING, DERIVED --------------------------------
     What a caller that knows its source descriptor's row gets out of the
     post above: TWO arms, because the bad-fd arm is refuted by the caller's
     own [arg_fd] premise, and the success arm at the premise's own [fv] and
     [FdOpen rb wb t] rather than at the existential pointer and the total
     lookup.  It is a LEMMA and not a second contract: the seal states the
     premise-free post, which is the one the dispatcher can call (header,
     ONE CONTRACT).  The reading is spelled out here rather than named,
     since the post is the only definition dup needs. *)
  Lemma sys_dup_post_sharp `{XI : CurCtx} (γf : gname) (p : mword 64)
      (pid : mword 32) (U : ustate) (v fv : mword 64) (fd0 : nat)
      (rb wb : bool) (t : fdtype) (sts : list fdstate) (r : mword 64) :
    arg_fd v (pv_ofile (us_V U)) = Some (fd0, fv) ->
    sts !! fd0 = Some (FdOpen rb wb t) ->
    sys_dup_post γf p pid U sts v r
    ⊢ ((* the table is full.  xv6 takes no reference on this path, so
          everything comes back exactly as handed in. *)
       (⌜r = (mword_of_int (-1) : mword 64) /\
         fd_frees (pv_ofile (us_V U)) = []⌝ ∗
        proc_priv γf p pid U ∗ fd_frags (pv_fdg (us_V U)) sts)
       ∨
       (* duplicated: the least free descriptor now names the SAME file the
          source does -- the cell write carries the premise's own [fv]
          ([dup_same_cell] is the two-lookup reading), and the bundle returns
          with the new row at the source's state and every other row
          untouched ([dup_rows_both]). *)
       (∃ (fd1 : nat) (l : list nat),
          ⌜r = (mword_of_int (Z.of_nat fd1) : mword 64) /\
           fd_frees (pv_ofile (us_V U)) = fd1 :: l /\
           sts !! fd1 = Some FdClosed⌝ ∗
          proc_priv γf p pid (us_ofile U fd1 fv) ∗
          fd_frags (pv_fdg (us_V U)) (<[fd1 := FdOpen rb wb t]> sts)))%I.
  Proof.
    iIntros (Ha Hsrc) "H". rewrite /sys_dup_post.
    iDestruct "H" as "[[[%Hr %Hn] [Hp Hb]] |
                       [(%fd0' & %fv' & (%Hr & %Ha' & %Hfr) & Hp & Hb) |
                        (%fd0' & %fd1 & %fv' & %l & (%Hr & %Ha' & %Hfr & %Hcl)
                         & Hp & Hb)]]".
    - (* argfd said no: refuted by the caller's own premise *)
      rewrite Ha in Hn. discriminate.
    - iLeft. iFrame "Hp Hb". iPureIntro. split; [exact Hr | exact Hfr].
    - (* [arg_fd] is a function, so the arm's existentials ARE the premise's *)
      rewrite Ha in Ha'. injection Ha' as <- <-.
      rewrite (list_lookup_total_correct sts fd0 (FdOpen rb wb t) Hsrc).
      iRight. iExists fd1, l. iFrame "Hp Hb". iPureIntro.
      split_and!; [exact Hr | exact Hfr | exact Hcl].
  Qed.

End SpecSysDup.

Definition wp_sys_dup_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γl γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (v : mword 64) (pid : mword 32) (U : ustate) (sts : list fdstate)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_dup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* sys_dup reads syscall argument 0, out of the trapframe page [proc_priv]
     carries *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  (* push_off's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (sys_dup_stack <= av)%nat ->
  (* THE RANK BOUND, FOR THE ONE LOCK BELOW.  sys_dup takes no lock of its
     own, but filedup acquires "ftable", and the rank discipline needs every
     rank the caller arrives holding to sit strictly BELOW that one --
     [LockRank.locks_below], not mere non-membership, because only the bound
     composes across a call chain ([locks_below_mono] weakens it to any higher
     rank, [locks_below_not_elem] recovers the non-membership a ghost step
     wants).  It is passed straight through to filedup, which states it in
     exactly this shape.  A syscall entry point holds nothing, so at every
     real instantiation [lks] is ∅ and this is [locks_below_empty]; the body
     is stated ∀-generically in [lks], so it has to be said. *)
  locks_below lks "ftable" ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the ftable lock, for filedup's ghost step *)
  is_ftable γl γf -∗
  proc_priv γf p pid U -∗
  (* the descriptor-state fragments -- spent on the destination descriptor,
     at the table the post states its row against *)
  fd_frags (pv_fdg (us_V U)) sts -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      sys_dup_post γf p pid U sts v (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSDUP.
  Parameter wp_sys_dup_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γl γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (v : mword 64) (pid : mword 32) (U : ustate) (sts : list fdstate)
    (b : bool) (lks : gset string),
      wp_sys_dup_sconf_body γl γf m av n eb p v pid U sts b lks.
End SYSDUP.
