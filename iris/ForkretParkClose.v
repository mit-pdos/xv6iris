(* ForkretParkClose.v -- REDUCING [forkret_park_pkg] TO A SHORT LIST.

   [ProofForkretPark.v] proves the park at the precondition
   [SpecForkretParkPaid.forkret_park_pkg], and nobody has ever paid it, so
   [LinkForkretPark.v]'s [Axiom] is still what kfork and userinit use.  The
   obstacle has always been described as "the residue closer", a wand that
   builds the trap loop's whole kernel-side bundle for a process that has
   not run yet -- which sounds like it needs the world.

   IT DOES NOT.  This file discharges everything in that package that is
   persistent or threadable, and what is left over is TWO resources,
   named once as [park_own]:

     [bslots (un_bn N) 3]            a draw from the 1024-slot bio pool
     [initproc ↦₈{un_dqi N} _]       a share of the initproc pointer

   Everything else the closer must produce it can produce for free:
   [ut_caps] is persistent (and already carries [procs_inv] and the
   [is_kstack] the park takes as an argument), the syscall environment is
   persistent, and [proc_priv_nopt] / [ut_trap_parked] / the two allowances
   are what [forkret_yield] and the closer's own arguments hand it.

   So the remaining question is not "how does a fresh process get a trap
   environment" but the much smaller "where do those two come from".  As
   surveyed when this file was written:

     [initproc ↦₈{dq}] -- CHEAPEST.  Only userinit writes the cell; every
       consumer downstream ([SpecKexit], [SpecReparent], [SpecSyscall]) already
       takes it at an ARBITRARY [dfrac] and hands it back, and [un_dqi] is a
       field the record's builder picks.  So persisting it once after userinit
       ([DfracDiscarded]) makes every later copy free and needs NO downstream
       contract change -- only a producer-side change in userinit's
       postcondition and main's threading, since main currently carries the
       exclusive BSS cell ([ProofMain.v]'s [Hinitproc]).

     [bslots (un_bn N) 3] -- NOT free from persistent facts, though the pool
       has room (BSLOTS = 1024, 3 * NPROC = 192).  The authority
       [BioInv.bslots_auth] lives inside [bcache_res], i.e. behind the bcache
       lock, so minting three fragments is a lock acquisition -- a WP step in
       whoever allocates the child, not a ghost update a bystander can do.

     THE BLOCK BITMAP USED TO BE THE THIRD, and the design question: it
       unfolded through [fileclose_bm] and [bitmap_res] to [fsblock] and
       [free_pool], exclusive, one per file system, so every process holding
       a residue across user execution held the block bitmap.  It is now the
       persistent [BitmapInv.bitmap_inv], carried inside
       [SpecFileclose.fileclose_ic_env] and [FsReady.fs_ready], and the
       residue no longer names it (design/fs-bitmap.md).

   NOTHING DEPENDS ON THIS FILE.  It is a leaf that states the reduction; the
   callers that will use it (kfork, userinit) still take the assumed park. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import KernelText WireInv.
Require Import KptExecMap.
Require Import StackOwn.
Require Import ProcGeom ProcDefs ProcInv ProcAvail.
Require Import SchedCtx.
Require Import FdSlots IrefSlots FileInvDefs.
Require Import BioDefs.
Require Import SpecFileclose.
Require Import UsertrapRes.
Require Import SpecUsertrap.
Require Import SpecForkret.
Require Import SpecForkretPark.
Require Import SpecForkretParkPaid.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.
Local Open Scope Z_scope.

Section ForkretParkClose.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* [procs_inv] read off the caps bundle without taking it apart -- the
     bundle goes nowhere, only its first conjunct is copied out. *)
  Lemma ut_caps_procs (N : ut_names) : ut_caps N -∗ procs_inv (un_s N).
  Proof. iIntros "(H & _)". iExact "H". Qed.

  (* THE RESIDUAL.  One definition rather than two loose conjuncts so that
     what is still owed has a name a later file can state a producer for. *)
  Definition park_own (N : ut_names) : iProp Σ :=
    (bslots (un_bn N) 3 ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{un_dqi N} (un_ip N))%I.

  (* THE CLOSER, BUILT.  [ut_caps] is persistent and [Rsys] is consumed once
     -- the wand can only be applied once, because applying it consumes the
     wand itself, so the exclusive members are spent exactly when the record
     is resumed. *)
  Lemma forkret_park_closer_intro
      (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) (av : nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    ut_caps N -∗
    Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N) -∗
    park_own N -∗
    (∀ (h : CpuId) (V' : pprivate),
       ⌜pv_upt V' = pv_upt V⌝ -∗
       forkret_yield (CID := h) (un_f N) (un_pj N)
         (add_vec (un_ks N) (mword_of_int 4096)) (un_pid N) av V' -∗
       fd_slots FDSPARE -∗
       iref_slots IREFSPARE -∗
       ut_res_bare (CID := h) Rsys (pv_upt V)
         (add_vec (un_ks N) (mword_of_int 4096))).
  Proof.
    iIntros (Hwf Hav) "#Hcaps Hsys Hown".
    iIntros (h V') "%Hupt (Htrap & Hpriv) Hfd Hiref".
    iDestruct "Hown" as "(Hbs & Hip)".
    rewrite /ut_res_bare.
    iExists N, V', av.
    iSplitR; [iPureIntro; exact Hupt|].
    iSplitR; [iPureIntro; reflexivity|].
    iSplitR; [iPureIntro; exact Hwf|].
    iSplitR; [iPureIntro; exact Hav|].
    iFrame "Htrap".
    rewrite /ut_env_nopt /ut_own_nopt.
    iFrame "Hcaps". iFrame "Hbs Hip Hfd Hiref Hpriv Hsys".
  Qed.

  (* ...AND THE WHOLE PACKAGE.  [procs_inv] is not a premise: [ut_caps]
     already carries it.  What is left on the left of the turnstile is three
     persistent globals, the slot marker allocproc's postcondition gives, the
     kernel stack procinit's postcondition already produces (SpecProcinit.v's
     [stack_own] per slot -- it is carrying it forward that is missing, not
     minting it), and [park_own]. *)
  Lemma forkret_park_pkg_intro
      (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (V : pprivate) (av : nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    kernel_text -∗
    wire_inv -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    pslot_used_at (un_pj N) -∗
    stack_own (KTR := KT1) (add_vec (un_ks N) (mword_of_int 4096)) av -∗
    ut_caps N -∗
    Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N) -∗
    park_own N -∗
    forkret_park_pkg (fun h : CpuId => ut_res_bare (CID := h) Rsys)
      (un_s N) (un_f N) (un_pj N) (un_ks N) (un_pid N) V av.
  Proof.
    iIntros (Hwf Hav) "#Htext #Hwire #Hkmap Hslot Hstack #Hcaps Hsys Hown".
    rewrite /forkret_park_pkg.
    iDestruct (ut_caps_procs with "Hcaps") as "#Hprocs".
    (* SIX [iSplitR]/[iSplitL]s, NOT ONE [iFrame], for two reasons at once:
       the package's LAST conjunct is the residue closer, a whole
       forall-closure over [forkret_yield] and [URes], so every
       (name x conjunct) attempt a named [iFrame] makes has to walk past it
       (measured 29 s -- claude-notes/optimization.md, "THE CHEAPEST FIX IS
       USUALLY TO SPLIT THE BIG CONJUNCT OFF FIRST"); and [fs_ready] now
       rides inside [ut_caps], so a named [iFrame "Htext"] would also dive
       into the closer's conclusion and frame the copy of [kernel_text] it
       finds THERE, leaving a goal of the wrong shape. *)
    iSplitR; [iExact "Htext"|].
    iSplitR; [iExact "Hwire"|].
    iSplitR; [iExact "Hkmap"|].
    iSplitR; [iExact "Hprocs"|].
    iSplitL "Hslot"; [iExact "Hslot"|].
    iSplitL "Hstack"; [iExact "Hstack"|].
    iApply (forkret_park_closer_intro with "Hcaps Hsys Hown"); assumption.
  Qed.

End ForkretParkClose.
