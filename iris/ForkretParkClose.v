(* ForkretParkClose.v -- REDUCING [forkret_park_pkg] TO A SHORT LIST.

   A proof of the park is stated against
   [SpecForkretParkPaid.forkret_park_pkg], and its last conjunct -- "the
   residue closer", a wand that builds the trap loop's whole kernel-side
   bundle for a process that has not run yet -- is what has always made the
   package look as though paying it needed the world.

   IT DOES NOT, and this file is the arithmetic.  Of everything
   [UsertrapRes.ut_res_bare] is made of:

     - [ut_caps] and the syscall environment are DERIVED, not owned.  Both
       are persistent, both are almost entirely [FsReady.fs_ready], and the
       syscall environment's fourth conjunct is [FirstTok.first_done] --
       which is [first_addr ↦₄□ 0 ∗ fs_ready] and is now an ARGUMENT of the
       closer (SpecForkret.v's last header section).  So what a builder owes
       is the WAND [first_done -∗ ut_caps N ∗ Rsys ...], i.e. only the rows
       neither half supplies: [is_ftable], the [wait_lock], the ticks lock,
       [devintr_caps_any], [procs_avail], the nextpid lock,
       [console_ready].  All seven are persistent and all seven exist before
       either parker runs -- main creates them, and kfork's parent carries
       them.

       THAT INDIRECTION IS THE WHOLE POINT.  Owning either half at park time
       is impossible at the site that most needs it: userinit parks the
       first process BEFORE forkret's boot arm establishes the file system,
       and the discarded [first] cell is minted by that same arm's release
       store.  Owning the wand is not, because the wand is about what
       happens later.

     - [ut_trap_parked] and [proc_priv_nopt] are what [forkret_yield]
       hands the closer, and the two allowances are its own arguments.

     - [bslots 3] and the [initproc] share -- [UsertrapRes.park_own] --
       are the only rows the builder must actually OWN.  Both are sourced
       now: the [initproc] cell is discarded persistent right after
       userinit's store at +0x14, and the three bio slots ride in
       [ProcDefs.proc_dormant], carved one triple per slot at procinit and
       handed out by allocproc (commit bbcd2687).  Every path that takes a
       process out of its dormant slot returns them --
       [ProcInv.proc_priv_to_dormant_zombie] cannot be applied without
       three units -- so this is a ledger, not a leak.

     THE BLOCK BITMAP USED TO BE ON THIS LIST, and it was the one entry
       that was a design problem rather than a plumbing one: it unfolded
       through [fileclose_bm] and [bitmap_res] to [fsblock] and
       [free_pool], exclusive, one per file system, so every process
       holding a residue across user execution held the block bitmap --
       which would have serialized user mode.  It is the persistent
       [BitmapInv.bitmap_inv] now, a conjunct of [FsReady.fs_ready], and
       the residue does not name it (design/fs-bitmap.md).

   NOTHING DEPENDS ON THIS FILE.  It is a leaf that states the reduction;
   the callers that will use it (kfork, userinit) still take the assumed
   park ([LinkForkretPark.v]'s [Axiom]). *)
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
Require Import UserPtTree.   (* [uptd] -- the closer is quantified over the descriptor *)
Require Import ProcPtOwn.    (* [proc_pt_wf] / [ud_data] / [ud_pas] *)
Require Import ProcGeom ProcDefs ProcInv ProcAvail.
Require Import SchedCtx.
Require Import FdSlots IrefSlots FileInvDefs.
Require Import BioDefs.
Require Import SpecFileclose.
Require Import FsReady.
Require Import FirstTok.
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* [procs_inv] read off the caps bundle without taking it apart -- the
     bundle goes nowhere, only its first conjunct is copied out.  Not used
     by [forkret_park_pkg_intro] below, which takes [procs_inv] as its own
     premise: the caps bundle is behind the derivation wand now, so it is
     not in hand when the package is assembled.  Kept because it is the
     fact that makes that premise free rather than new -- any party that
     will be able to produce [ut_caps] at all already has it. *)
  Lemma ut_caps_procs (N : ut_names) : ut_caps N -∗ procs_inv (un_s N).
  Proof. iIntros "(H & _)". iExact "H". Qed.

  (* THE CLOSER, BUILT.  [Rsys] is abstract because this file must not
     depend on [ProofSyscall.v] to name [syscall_env]; nothing here uses
     its structure.  The derivation wand and [park_own] are both consumed
     once, which is right: applying the closer consumes the closer, so the
     exclusive members are spent exactly when the record is resumed. *)
  Lemma forkret_park_closer_intro
      (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (av : nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    (first_done -∗ ut_caps N ∗ Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N)) -∗
    park_own N -∗
    (∀ (h : CpuId) (pt' : uptd) (V' : pprivate),
       ⌜pv_upt V' = pt'⌝ -∗
       ⌜ud_data pt' = ud_pas pt'⌝ -∗
       ⌜proc_pt_wf pt'⌝ -∗
       first_done -∗
       forkret_yield (CID := h) (un_f N) (un_pj N)
         (add_vec (un_ks N) (mword_of_int 4096)) (un_pid N) av V' -∗
       fd_slots FDSPARE -∗
       iref_slots IREFSPARE -∗
       ut_res_bare (CID := h) Rsys pt'
         (add_vec (un_ks N) (mword_of_int 4096))).
  Proof.
    iIntros (Hwf Hav) "Hderive Hown".
    iIntros (h pt' V') "%Hupt %Hnorm %Hptwf Hdone (Htrap & Hpriv) Hfd Hiref".
    (* the two page-table facts are the loop's, not this wand's: they are
       handed in so forkret can prove them of the descriptor it actually
       ends on, and [ut_res_bare] does not restate them. *)
    clear Hnorm Hptwf.
    iDestruct ("Hderive" with "Hdone") as "[#Hcaps Hsys]".
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

  (* ...AND THE WHOLE PACKAGE.  What is left on the left of the turnstile is
     four persistent globals, the slot marker allocproc's postcondition
     gives, the kernel stack [ProcDefs.kstack_free] hands back beside it,
     the derivation wand, and [park_own]. *)
  Lemma forkret_park_pkg_intro
      (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (N : ut_names) (av : nat) :
    ut_wf N ->
    (K_usertrap <= av)%nat ->
    kernel_text -∗
    wire_inv -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    procs_inv (un_s N) -∗
    pslot_used_at (un_pj N) -∗
    stack_own (KTR := KT1) (add_vec (un_ks N) (mword_of_int 4096)) av -∗
    (first_done -∗ ut_caps N ∗ Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N)) -∗
    park_own N -∗
    forkret_park_pkg (fun h : CpuId => ut_res_bare (CID := h) Rsys)
      (un_s N) (un_f N) (un_pj N) (un_ks N) (un_pid N) av.
  Proof.
    iIntros (Hwf Hav) "#Htext #Hwire #Hkmap #Hprocs Hslot Hstack Hderive Hown".
    rewrite /forkret_park_pkg.
    (* SIX [iSplitR]/[iSplitL]s, NOT ONE [iFrame], for two reasons at once:
       the package's LAST conjunct is the residue closer, a whole
       forall-closure over [forkret_yield] and [URes], so every
       (name x conjunct) attempt a named [iFrame] makes has to walk past it
       (measured 29 s -- claude-notes/optimization.md, "THE CHEAPEST FIX IS
       USUALLY TO SPLIT THE BIG CONJUNCT OFF FIRST"); and [fs_ready] rides
       inside the closer's own argument list, so a named [iFrame "Htext"]
       would also dive into the closer's conclusion and frame the copy of
       [kernel_text] it finds THERE, leaving a goal of the wrong shape. *)
    iSplitR; [iExact "Htext"|].
    iSplitR; [iExact "Hwire"|].
    iSplitR; [iExact "Hkmap"|].
    iSplitR; [iExact "Hprocs"|].
    iSplitL "Hslot"; [iExact "Hslot"|].
    iSplitL "Hstack"; [iExact "Hstack"|].
    iApply (forkret_park_closer_intro with "Hderive Hown"); assumption.
  Qed.

End ForkretParkClose.
