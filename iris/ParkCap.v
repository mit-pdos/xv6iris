(* ParkCap.v -- THE PARK TOKEN: parking a fresh process, as a RESOURCE.

   WHY A RESOURCE.  Parking a process that has never run means building
   [SchedCtx.proc_ctx] for it -- a WP for everything that happens when the
   scheduler resumes it: forkret, userret, user mode, uservec, usertrap,
   the syscall dispatch, and inside that dispatch sys_fork -> kfork, which
   PARKS THE NEXT PROCESS.  So the theorem "a package of resources builds a
   [proc_ctx]" is used inside its own proof, one resumption deeper.  At the
   module level that is a cycle no functor application can tie (kfork's
   proof would have to be a functor over the park's proof, which is a
   functor over forkret's, which is a functor over the trap loop's, which
   contains kfork); it is why [LinkForkretPark.v] was an [Axiom].

   The knot is tied HERE instead, in the logic, where it belongs: the park
   is a persistent proposition [park_token γs] that a process HOLDS (inside
   its syscall environment, [ProofSyscall.syscall_env]) and hands to every
   child it forks, and that proposition is a GUARDED FIXPOINT -- the
   package a parker hands in is consumed under the [▷] of the context it
   builds, so the token it hands the child may itself sit under a [▷].
   kfork consumes the token as a resource and names no module;
   the only place the token is PROVED is at the top
   ([ProofForkretPark.park_token_intro]), from forkret's proof, and only
   main's cone ever refers to that.

   THE TWO HALVES of the token, for one residue [URB]:

     * THE CAP: the package plus the child's own rows build [▷ proc_ctx];
       the package is taken under a [▷] because the park's proof uses it
       only after the context's own later ([ProofForkretPark]'s [iNext]).
     * THE CHANNEL: the residue's producer-side entry
       ([UsertrapRes.ut_park_intro_body]) at [W := park_token γs] -- which
       is what makes the child's syscall environment carry a token too --
       under a [▷] for the same reason: the closer it yields is a package
       row, and the package is consumed under the later.

   Both occurrences of the token inside its own definition are under [▷],
   which is what makes the functional contractive. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import KernelText WireInv.
Require Import KptExecMap.
Require Import StackOwn.
Require Import ProcGeom ProcDefs ProcInv ProcAvail.
Require Import SchedCtx SwtchCtx.
Require Import FdSlots IrefSlots FileInvDefs.
Require Import FirstTok TimerCap.
Require Import UserPtTree ProcPtOwn.   (* [uptd] / [ud_data] / [ud_pas] / [proc_pt_wf] *)
Require Import WaitInv.  (* [ch_frag] -- the children row the park captures *)
Require Import UsertrapRes.
Require Import UexecSlot. (* [uvis] / [uvis_of] -- the slot's key, and the
                             projection of a resumed record onto it *)
Require Import UexecRet.  (* [uslot] -- the KEYED slot the resume closer now
                             yields.  Required DIRECTLY: the [Typeclasses
                             Opaque] seal on [uslot] does not travel through a
                             re-export (durable-notes). *)
From Kernel Require KernelSyms.
Require Import Xv6G.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import ChildTok.  (* [my_pay] -- the boot arm's payload row *)
Require Import InitBoot.  (* [init_boot_bundle] -- the first process's exec
                               bundle, the BOOT mode's payload *)

Section ParkCap.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.
  (* NO [ctokG] BINDER OF ITS OWN: [Xv6G.xv6_ctok] is in scope and meets the
     class's index; a second [Context `{!ctokG Σ}] beside it would win
     resolution here while every file that has only [xv6G] resolves to the
     field -- two instances that print alike and do not match ([UexecSG]'s
     note).  The SG binder is NON-generalizing (braces) so that its index
     resolves rather than abstracting a fresh one. *)
  Context {SG : uexecSG Σ}.

  (* the saved-context head the park installs: forkret's entry, and the
     kernel stack's top -- [SpecAllocproc.forkret_pc]'s value *)
  Definition park_forkret_pc : mword 64 := mword_of_int KernelSyms.forkret.

  (* THE PACKAGE a parker hands in ([SpecForkretParkPaid.forkret_park_pkg]
     is this, verbatim).  [W] is what the residue closer is handed at the
     resume beside [first_done] and the timer capability. *)
  Definition park_pkg `{XI : CurCtx}
      (URB : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> gset gname -> mword 32 -> iProp Σ) (W : iProp Σ)
      (γs : list gname) (γw γft γf γtl : gname) (pa ks : mword 64)
      (* the parked process's fd-state ghost name -- see
         [SpecForkretParkPaid.forkret_park_pkg], which is this verbatim *)
      (g : gname)
      (* ...AND ITS CHILDREN-ROW GHOST NAME, beside the descriptor
         one and for its reason: the parked row is at
         [ProcDefs.pv_chg] of the parked block, and the closer's pure
         premise below demands the resumed record name the same one --
         nothing between the park and the resume re-incarnates the
         slot. *)
      (γch : gname)
      (* ...and its cwd's inum, for the same reason the name is here: the
         row the parker captured is restricted to it ([park_token_park] and
         [park_token_park_steady] below), so the closer needs the resumed
         record to agree *)
      (cw : Z)
      (* ...AND THE PARKED PROCESS'S DESCRIPTOR STATES.  The parker holds
         the [FdSlots.fd_frags] bundle and therefore names the list; the
         closer hands the residue back at it and the BOOT mode's bundle is
         owed at it, so the two halves are one list named ONCE, here.  It
         is a parameter and not the closer's existential because forkret's
         boot arm has to spell it BEFORE the closer runs: it is the [sts]
         kexec builds its resume key at. *)
      (sts : list fdstate)
      (* ...AND THE PARKED PROCESS'S GENERATION AND CHILDREN SET, beside
         [sts] and for its reason: the resume key carries both, the
         residue is indexed by the set, and the closer builds both -- so
         the party that read them off the kernel's cells names them here.
         NEITHER IS THE PARKER'S TO CHOOSE.  [park_cap] below passes the
         parked block's own [ProcDefs.pv_gen] for the generation, and the
         set is the one the parker's [WaitInv.ch_frag] is at
         ([park_token_park] / [_steady] take the row as a premise, exactly
         as they take the fragment bundle).  Both stay PARAMETERS rather
         than projections of the closer's [U'], because what pins the
         RESUMED record is a premise of the closer and not a definition:
         the two pure pins above ([pv_fdg]/[pv_chg]) are how the parked
         names reach it. *)
      (gn : gname) (cs : gset gname)
      (* THE PARKED RUN KEY, WHEN THERE IS ONE.  A park has two modes and
         this is the parameter that selects them ([park_cap]'s [steady] bit
         is what a parker passes):

           [None]    -- THE BOOT MODE.  Whoever resumes this record may
                        replace its address space first: forkret's boot arm
                        runs kexec("/init") between the park and the
                        resume, so no key captured at the park survives it
                        (userinit's park; projects/user-wp-slot.md SS4c,
                        refutation R-b).  What the parker hands over
                        instead is the EXEC BUNDLE that boot arm spends
                        ([InitBoot.init_boot_bundle], the row below), whose
                        slot piece answers at the key kexec builds -- so
                        the closer owes no slot on this mode and the kernel
                        mints none.

           [Some Wk] -- the parker holds [FirstTok.first_done], so the boot
                        arm is DEAD for this record and the resume is
                        forkret's steady arm, which lands on a record with
                        the parked one's RUN KEY ([UexecRet.urun_eq]).  The
                        parker captures ONE slot, at [Wk], and the closer's
                        pure premise below re-keys it (kfork's child). *)
      (Wk : option uvis)
      (pid : mword 32) (av : nat) : iProp Σ :=
    (kernel_text ∗
     wire_inv ∗
     kmap_at tramp_vpn tramp_ppn KP_rx ∗
     procs_inv γs ∗
     (* THE PARKER'S GLOBALS, at ITS context (L8, A12.19): the cap moves
        them into the running twin ([ProofForkretPark], by [ctx_move]),
        which is what the twin's forkret needs to apply the closer below. *)
     park_globals cur_ctx γs γw γft γf γtl ∗
     pslot_used_at pa ∗
     stack_own (KTR := KT1) (add_vec ks (mword_of_int 4096)) av ∗
     (* THE MODE'S PAYLOAD.

        [Some]: THE PARKER'S EVIDENCE THAT THE BOOT ARM IS DEAD.  A [Some]
        package promises the resume lands on a record with the parked run
        key, which is true only if nothing runs kexec("/init") in between
        -- and the resource that says so is [FirstTok.first_done], whose
        [first_addr ↦₄□ 0] half is incompatible with the boot arm's
        [first_addr ↦₄ 1] ([FirstTok.first_tok_boot_excl]).  So forkret
        REFUTES the boot arm out of this row rather than owing the closer a
        key it cannot have.  Persistent, so a parker that has it pays
        nothing.

        [None]: THE FIRST PROCESS'S EXEC BUNDLE, which is what the boot arm
        the mode admits actually spends -- kexec("/init") at this record's
        working directory and descriptor states, whose slot piece hands
        back the slot at the key kexec built.  LINEAR, and NOT under the
        later: forkret's boot arm runs it before the closer, so it is a row
        of the package like [stack_own] and not a capture of the closer's
        ([InitBoot]'s header). *)
     (match Wk with
      | Some _ => first_done
      | None => init_boot_bundle cw sts
      end) ∗
     (* THE CLOSER IS UNDER A LATER, the rows above are not: the cap needs
        the rows now, to deposit them into the twin, and only the closer is
        spent a step later, by forkret.  Quantified over the RESUMER's context
        [Xc], at which every context-indexed row it is handed lives. *)
     ▷ (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (U' : ustate),
        ⌜pv_upt (us_V U') = pt'⌝ -∗
        ⌜ud_data pt' = ud_pas pt'⌝ -∗
        ⌜proc_pt_wf pt'⌝ -∗
        (* the resumed record names the parked process's fd-state ghost *)
        ⌜pv_fdg (us_V U') = g⌝ -∗
        (* ...and its children row -- see [γch] above *)
        ⌜pv_chg (us_V U') = γch⌝ -∗
        ⌜pv_gen (us_V U') = gn⌝ -∗
        (* ...and is at the parked process's working directory: nothing
           between park and resume calls chdir (forkret's boot arm runs
           kexec, which inherits it) *)
        ⌜pv_cwi (us_V U') = cw⌝ -∗
        (* ...AND, ON THE STEADY MODE, THAT THE RESUMED RECORD CARRIES THE
           PARKED RUN KEY ([UexecRet.urun_eq]: the resume register file, the
           resume pc, the image, the permission view, the size and the cwd
           -- everything the slot reads of its key but the descriptor view).
           forkret's steady arm has exactly these facts: [tf_ueq] out of
           prepare_return, [us_M] untouched, [ud_um (ud_norm P) = ud_um P],
           and neither the size nor the cwd moves.  [None] asks nothing --
           that mode's closer instantiates a family instead. *)
        ⌜match Wk with Some W0 => urun_eq W0 U' | None => True end⌝ -∗
        park_globals Xc γs γw γft γf γtl -∗
        ut_tfk (CID := h) (add_vec ks (mword_of_int 4096)) (us_V U') -∗
        first_done (XI := Xc) -∗
        W -∗
        timer_cap (CID := h) -∗
        ut_trap_parked (CID := h) (XI := Xc) pa (add_vec ks (mword_of_int 4096)) av ∅ -∗
        proc_priv_nopt (XI := Xc) γf pa pid (us_V U') -∗
        fd_slots FDSPARE -∗
        iref_slots IREFSPARE -∗
        (* THE RESUMED BUNDLE, AND A SLOT KEYED AT THE RECORD THE RESUME
           ACTUALLY LANDS ON -- which is the key the CLOSER produces, on
           either mode.  At [None] the parker captured the family
           [∀ W, uslot W] restricted to its table ([park_token_park] below)
           and the closer instantiates it here, at [uvis_of U']: a key
           captured at the park would be stale, because [ProofForkret]'s
           boot arm runs kexec("/init") between the park and the resume and
           applies this closer at the POST-EXEC record
           (projects/user-wp-slot.md SS4c, refutation R-b).  At [Some Wk] the
           parker captured ONE slot, at [Wk], and the pure premise above
           re-keys it onto [uvis_of U'] ([UexecRet.uslot_of_urun_eq]) --
           sound because that mode's [first_done] makes the boot arm dead
           ([park_token_park_steady] below). *)
        (* ...AT THE RECORD'S OWN DESCRIPTOR VIEW, AND THE RESIDUE'S IS THE
           SAME ONE: the package's [sts] parameter names both, which is the
           tie stated rather than merely arranged -- the residue the resume
           hands back carries [FdSlots.fd_frags] at [sts]
           ([UsertrapRes.ut_own]'s conjunct) and the slot is keyed at
           [uvis_of U' sts].  The PRODUCER picks it, and the producer is
           the party holding the fragments ([park_token_park] below passes
           the very list its bundle is at); the reading stays true across
           the park because moving a descriptor's state needs BOTH halves
           ([FdSlots.fd_st_both_update]) and this closure holds one -- not
           even forkret's boot arm, whose kexec("/init") does not touch the
           descriptor array.

           THE SLOT IS THE STEADY MODE'S ALONE.  On the boot mode the
           record's slot comes out of kexec, through the exec bundle the
           package's row above handed the boot arm, so there is nothing for
           the closer to produce and nothing for the kernel to mint. *)
        (URB h Xc pt' (add_vec ks (mword_of_int 4096)) U' sts cs pid
         ∗ match Wk with
           (* ...AND AT THE PARKED PROCESS'S PID, which the package
              already carries ([pid] below, the number the resumed block is
              at): the key records it ([UexecSlot.uvis_pid]) because
              getpid(2) answers with it, and the park is where it is read
              -- the closer hands back [proc_priv_nopt ... pid ...], so the
              slot and the block name one number by construction. *)
           | Some _ => uslot (uvis_of U' sts gn cs pid)
           | None => emp
           end)))%I.

  (* the child's own rows, the ones the park spends.

     THE BLOCK IS MODE-DEPENDENT, and that is the seam that makes the boot
     mode a fact about the record rather than a promise about it.  On the
     STEADY mode the block goes over whole: its [FirstTok.first_tok] may be
     on either arm and the package's own [first_done] refutes the boot one.
     On the BOOT mode the parker hands the block SPLIT -- the deficit block
     and the working-directory reference, with [FirstTok.first_boot]'s four
     rows BESIDE them -- so "this record is the first process" is a row of
     the park and not an assumption: forkret's steady arm reads [first] as
     0 out of [first_done] and the boot rows' [first_addr ↦₄ 1] refutes
     that reading ([FirstTok.first_boot_done_excl]).  The rows rejoin the
     block at the release store, exactly where the boot arm puts them back
     ([ProofForkret]'s [fkr_boot], which takes them split already). *)
  Definition park_child `{XI : CurCtx} (γs : list gname) (γf : gname) (pa ks : mword 64)
      (rest : list (mword 64)) (pid : mword 32) (U : ustate) (steady : bool) : iProp Σ :=
    (is_kstack pa ks ∗
     ctx_cells (p_context pa) (park_forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) ∗
     (* THE BOOT ARM HANDS THE BLOCK SPLIT, and the incarnation's pair is
        one of the pieces: it joins the block at the same store the working
        directory and the token do ([ProcInv.proc_priv_split_cwd] is
        six-way), so a parker that has not closed the block yet carries it
        beside them. *)
     (if steady then proc_priv γf pa pid U
      else proc_priv_nocwd γf pa pid U
           ∗ cwd_ref_at (pv_cwd (us_V U)) (pv_cwi (us_V U))
           ∗ first_boot
           (* AT THE TRIVIAL PAYLOAD, and this arm is the one place it can
              be said: the boot park is <init>'s, and <init> has no parent
              to owe ([SpecUserinit] splits its incarnation at
              [fun _ => True] and drops the parent's quarter).  The
              persistent half is what forkret's boot arm hands
              kexec("/init") for the exec'd image's slot
              ([SpecKexec.exec_slot_pre]). *)
           ∗ gen_kq (pv_gen (us_V U)) pa pid (fun _ => True)%I
           ∗ my_pay (pv_gen (us_V U)) (fun _ => True)%I
           (* ...AND THE TWO QUARTERS ([SlotGen.gen_halves_priv]), on the
              pair's footing: <init>'s three quarters were dropped at the
              split ([SpecUserinit]) -- it has no parent, so no entry is
              deposited under <wait_lock> and its parent cell stays 0. *)
           ∗ gen_halves_priv pa pid (pv_gen (us_V U))
           (* ...and the slot's half of [p->xstate], which the block the
              boot arm closes carries ([ProcInv.proc_priv_core]) *)
           ∗ (∃ xsv : mword 32, p_xstate pa ↦₄{DfracOwn (1/2)} xsv)) ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE)%I.

  (* THE CAP, at a given [W]: the statement of
     [SpecForkretParkPaid.forkret_park_paid_body], as a [□] wand *)
  Definition park_cap
      (URB : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> gset gname -> mword 32 -> iProp Σ) (W : iProp Σ)
      (γs : list gname) : iProp Σ :=
    (□ ∀ (hp : CpuId) (ξp : CtxId) (γw γft γf γtl : gname) (pa ks : mword 64)
         (rest : list (mword 64)) (pid : mword 32) (U : ustate)
         (* THE PARKED DESCRIPTOR STATES -- [park_pkg]'s parameter, which
            the parker names off the fragment bundle it holds *)
         (* THE PARKED CHILDREN SET, which the parker names off the
            [WaitInv.ch_frag] it holds, exactly as it names [sts] off the
            fragment bundle -- the binder stays because no projection of
            [U] determines it: the row is a resource beside the block, and
            the residue is indexed by the set that row is at.  THE
            GENERATION IS NOT HERE: the block determines it
            ([ProcDefs.pv_gen]), so the cap passes the block's field and
            the package's closer demands the resumed record carry the same
            one. *)
         (sts : list fdstate) (cs : gset gname) (av : nat)
         (* WHICH OF THE PACKAGE'S TWO MODES the parker is paying: [true]
            hands the package the parked record's RUN KEY and owes
            [FirstTok.first_done] with it, [false] hands no key and owes
            nothing.  See [park_pkg]'s [Wk] parameter, and
            [park_token_park] / [park_token_park_steady] for the two
            parkers.  The key is the parked record's own projection, at a
            placeholder descriptor view: [UexecRet.urun_eq] does not read
            [uvis_fd], and the party that names the view is the one holding
            the fragment bundle. *)
         (steady : bool),
       ⌜length rest = 12%nat⌝ -∗
       ⌜exists j : nat, pa = proc_addr j /\ (j < NPROC)%nat⌝ -∗
       ⌜(K_usertrap <= av)%nat⌝ -∗
       (* THE PARKER'S RUNNING TOKEN, in and out (L8, A12.19): the park
          twins it for the child's context and moves the record's rows there
          -- see [ProofForkretPark]. *)
       own_context (CID := hp) ξp -∗
       park_pkg (XI := ξp) URB W γs γw γft γf γtl pa ks (pv_fdg (us_V U))
         (pv_chg (us_V U)) (pv_cwi (us_V U)) sts (pv_gen (us_V U)) cs
         (if steady then Some (uvis_of U [] (pv_gen (us_V U)) cs pid) else None)
         pid av -∗
       (* ...and [W] itself, for forkret to hand the closer: under the same
          later, for the same reason *)
       ▷ W -∗
       park_child (XI := ξp) γs γf pa ks rest pid U steady -∗
       (* THE CONCLUSION IS THE RECORD PARKED UNDER THE PARKER'S CONTEXT:
          the child's rows live at the record's own existential identity
          ([SwtchCtx.valid_context_pre]'s [XIp]) and its token is
          [ctx_parked XIp ξp], so the only ξ the statement names is the
          binder's own -- which is what [UtResFits] needs of
          [park_cap]/[park_token]. *)
       |==> own_context (CID := hp) ξp ∗ proc_ctx (XI := ξp) γs pa)%I.

  (* THE CHANNEL, at a given [W], as a [□] proposition under a later -- for
     the records of THIS table ([un_s N = γs]), which is all the token for
     [γs] ever parks *)
  Definition park_chan
      (URB : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> gset gname -> mword 32 -> iProp Σ) (W : iProp Σ)
      (γs : list gname) : iProp Σ :=
    (□ ∀ (ξp : CtxId) (N : ut_names) (av : nat),
       ⌜un_s N = γs⌝ -∗ ⌜ut_wf N⌝ -∗ ⌜(K_usertrap <= av)%nat⌝ -∗
       ▷ (park_env (XI := ξp) N -∗ park_own (XI := ξp) N -∗
          (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (U' : ustate)
             (sts : list fdstate) (cs : gset gname),
             ⌜pv_upt (us_V U') = pt'⌝ -∗
             park_globals Xc (un_s N) (un_w N) (un_ft N) (un_f N) (un_tk N) -∗
             ut_tfk (CID := h) (add_vec (un_ks N) (mword_of_int 4096)) (us_V U') -∗
             first_done (XI := Xc) -∗
             W -∗
             timer_cap (CID := h) -∗
             ut_trap_parked (CID := h) (XI := Xc) (un_pj N)
               (add_vec (un_ks N) (mword_of_int 4096)) av ∅ -∗
             proc_priv_nopt (XI := Xc) (un_f N) (un_pj N) (un_pid N) (us_V U') -∗
             fd_slots FDSPARE -∗
             iref_slots IREFSPARE -∗
             (* NO USER-EXECUTION WP ROW: this mirrors
                [UsertrapRes.ut_park_intro_body] row for row, and the residue
                carries no ∀-state WP for the channel to spend.  The keyed
                [uslot (uvis_of U' sts)] in [park_pkg]'s closer above is what
                crosses the park. *)
             fd_frags (pv_fdg (us_V U')) sts -∗
             (* ...AND THE CHILDREN ROW AT A NAMED SET, beside the
                fragments: this mirrors [UsertrapRes.ut_park_intro_body]
                row for row. *)
             ch_frag (pv_chg (us_V U')) (un_pj N) cs -∗
             URB h Xc pt' (add_vec (un_ks N) (mword_of_int 4096)) U' sts cs
               (un_pid N))))%I.

  (* THE TOKEN: some residue, its cap and its channel, both at [W := the
     token itself] *)
  Definition park_token_F (γs : list gname) (X : iProp Σ) : iProp Σ :=
    (∃ URB : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> gset gname -> mword 32 -> iProp Σ,
       park_cap URB X γs ∗ park_chan URB X γs)%I.

  Local Instance park_token_F_contractive γs : Contractive (park_token_F γs).
  Proof.
    rewrite /park_token_F /park_cap /park_chan /park_pkg.
    solve_contractive.
  Qed.

  Definition park_token (γs : list gname) : iProp Σ := fixpoint (park_token_F γs).

  Lemma park_token_unfold (γs : list gname) :
    park_token γs ⊣⊢ park_token_F γs (park_token γs).
  Proof. apply (fixpoint_unfold (park_token_F γs)). Qed.

  Global Instance park_token_persistent γs : Persistent (park_token γs).
  Proof.
    rewrite /Persistent park_token_unfold /park_token_F.
    iIntros "H". iDestruct "H" as (URB) "[#Hcap #Hchan]".
    iModIntro. iExists URB. iFrame "Hcap Hchan".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* USING IT: what userinit and kfork do at their park.                    *)
  (*                                                                        *)
  (* TWO PARKERS, TWO MODES.  [park_token_park] below is the park of a       *)
  (* record whose resume still runs forkret's BOOT arm -- kexec("/init")     *)
  (* replaces the address space between the park and the resume, so no key   *)
  (* captured here survives it and what the parker must own is the EXEC      *)
  (* BUNDLE that arm spends, whose slot piece answers at the key kexec       *)
  (* builds (userinit's park).                                               *)
  (* [park_token_park_steady] is the park of a record whose parker holds     *)
  (* [FirstTok.first_done]: the boot arm is dead, the resume is forkret's    *)
  (* steady arm, and that arm lands on a record with the parked one's RUN    *)
  (* KEY ([UexecRet.urun_eq]) -- so ONE slot at the parked record is enough  *)
  (* and the closer re-keys it (kfork's child).                             *)
  (* ------------------------------------------------------------------- *)
  Lemma park_token_park `{CID : CpuId} (N : ut_names) (rest : list (mword 64)) (U : ustate)
      (sts : list fdstate) (cs : gset gname) :
    ut_wf N ->
    length rest = 12%nat ->
    (* the parker's running token, in and out -- the cap's premise *)
    own_context cur_ctx -∗
    park_token (un_s N) -∗
    kernel_text -∗
    wire_inv -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    pslot_used_at (un_pj N) -∗
    stack_own (KTR := KT1) (add_vec (un_ks N) (mword_of_int 4096)) KSTACK_AV -∗
    park_env N -∗
    park_own N -∗
    (* THE CHILD'S DESCRIPTOR-STATE FRAGMENTS.  They are NOT part of
       [park_child]: that bundle is handed straight to the cap, whereas
       these have to be captured by the package's RESUME closer, which is
       built here.  allocproc minted them with the block; the resume hands
       them to [UsertrapRes.ut_own], re-keyed by the closer's own
       [pv_fdg V' = pv_fdg V] premise. *)
    (* AT A NAMED TABLE.  This used to take the bundle [∃]-weakened, which
       threw away exactly the fact the parker had just been handed:
       allocproc proves [fd_frags γ fdt0] and a park that forgets it makes
       a fresh process's descriptors unstateable.  The states the package
       resumes at are THESE, which is what lets the caller say what the
       child's table is. *)
    fd_frags (pv_fdg (us_V U)) sts -∗
    (* ...AND ITS CHILDREN ROW, AT A NAMED SET, on the fragments' route
       exactly: the row is one entry of the map [wait_lock] owns
       ([WaitInv.ch_frag]), born at boot with the slot and handed to the
       parker by allocproc ([SpecAllocproc.allocproc_post]), and the resume
       hands it into the residue re-keyed by the closer's own
       [pv_chg V' = pv_chg V] premise. *)
    ch_frag (pv_chg (us_V U)) (un_pj N) cs -∗
    (* THE FIRST PROCESS'S EXEC BUNDLE, on the fd fragments' route exactly:
       not part of [park_child] (that bundle goes straight to the cap) but a
       row of the package built here, spent by forkret's boot arm on
       kexec("/init").  NOT A SLOT, and not a slot family: the party that
       resumes this record replaces its address space first, so no key
       named here survives (projects/user-wp-slot.md SS4c, R-b) -- what
       DOES survive is the bundle whose slot piece answers at the key kexec
       builds, which is why the boot mode carries this instead.  THE KERNEL
       THEREFORE MINTS NOTHING: the bundle comes from the application,
       through the system theorem's [Hinit_boot].
       AT THE PARKED BLOCK'S WORKING DIRECTORY AND TABLE, the two key
       fields the resume does not choose: kexec inherits the cwd and does
       not touch the descriptor array. *)
    init_boot_bundle (pv_cwi (us_V U)) sts -∗
    (* THE CHILD'S ROWS, WITH THE BLOCK SPLIT: this parker is parking the
       FIRST PROCESS, and the boot rows travel as their own rows so that
       the record's mode is a resource forkret can read.  See
       [park_child]. *)
    park_child (un_s N) (un_f N) (un_pj N) (un_ks N) rest (un_pid N) U false -∗
    |==> own_context cur_ctx ∗ proc_ctx (un_s N) (un_pj N).
  Proof.
    iIntros (Hwf Hrest) "Hrun #Htok #Htext #Hwire #Hkmap #Hmk Hstack #Henv Hown Hfrag Hch Hbundle Hchild".
    assert (Hkav : (K_usertrap <= KSTACK_AV)%nat) by (vm_compute; lia).
    iPoseProof "Htok" as "Htok'".
    iEval (rewrite park_token_unfold /park_token_F) in "Htok'".
    iDestruct "Htok'" as (URB) "[#Hcap #Hchan]".
    iAssert (procs_inv (un_s N)) as "#Hprocs".
    { iDestruct "Henv" as "[Hcaps _]". iDestruct "Hcaps" as "(_ & $ & _)". }
    (* the parker's globals, out of the environment it holds anyway *)
    iAssert (park_globals cur_ctx (un_s N) (un_w N) (un_ft N) (un_f N) (un_tk N)) as "#Hglobp".
    { iDestruct "Henv" as "[Hcaps Hextra]".
      iApply (park_globals_of_park_env with "Hcaps Hextra"). }
    iDestruct ("Hchan" $! cur_ctx N KSTACK_AV with "[%] [%] [%]") as "Hclose";
      [reflexivity | exact Hwf | exact Hkav |].
    iApply ("Hcap" $! cpu_id cur_ctx (un_w N) (un_ft N) (un_f N) (un_tk N) (un_pj N)
              (un_ks N) rest (un_pid N) U sts cs KSTACK_AV false
              with "[%] [%] [%] Hrun [Hstack Hown Hclose Hfrag Hch Hbundle] [] Hchild").
    - exact Hrest.
    - destruct Hwf as (Hj & _). exists (un_j N). split; [reflexivity | exact Hj].
    - exact Hkav.
    - rewrite /park_pkg.
      iFrame "Htext Hwire Hkmap Hmk Hstack".
      (* [procs_inv] and the globals by [iExact], not [iFrame]: the persistent
         [Hprocs] would otherwise be framed INTO the (transparent) globals
         bundle's own first row and leave the bundle half-built *)
      iSplitR; [iExact "Hprocs"|].
      iSplitR; [iExact "Hglobp"|].
      (* the mode row: this park is the one whose resume still runs the
         boot arm, so the package carries no run key and carries instead
         the bundle that arm spends *)
      iSplitL "Hbundle"; [iExact "Hbundle"|].
      iNext.
      iDestruct ("Hclose" with "Henv Hown") as "Hclose'".
      iIntros (h Xc pt' U') "%Hupt %Hnorm %Hptwf %Hfg %Hcg %Hgenp %Hcwi _ #Hglob #Htfk #Hdone HW #Htc Htrap Hpriv Hfd Hiref".
      (* the parked bundle, re-keyed onto the resumed record *)
      iEval (rewrite -Hfg) in "Hfrag".
      iEval (rewrite -Hcg) in "Hch".
      (* ...AND ITS STATES, NAMED.  This is the only place in the park
         channel where the descriptor states are in hand as a value, and it
         is the place the key is minted -- so the key is minted AT them.
         The bundle is handed on to the residue unchanged, so the view the
         slot is keyed at and the view the residue carries are the same list
         by construction. *)
      (* THE BOOT MODE OWES NO SLOT: the record's is exec's receipt, so
         all the closer produces is the residue, at the package's own
         [sts] -- the list the fragments below are at. *)
      iSplitL; [| iEmpIntro].
      iApply ("Hclose'" $! h Xc pt' U' sts cs
                with "[%] Hglob Htfk Hdone HW Htc Htrap Hpriv Hfd Hiref Hfrag Hch").
      exact Hupt.
    - iNext. iExact "Htok".
  Qed.

  (* THE STEADY PARK: one slot at the parked record, re-keyed at the resume.

     THE PREMISE IT ADDS is [FirstTok.first_done], which is what makes the
     shorter slot premise honest: the boot arm reads [first_addr] and its
     [↦₄ 1] is incompatible with the [↦₄□ 0] this resource carries, so the
     record this parks CANNOT be resumed through kexec("/init") and the only
     resume left is forkret's steady arm -- which lands on a record carrying
     the parked one's RUN KEY ([UexecRet.urun_eq]: the resume register file,
     the resume pc, the image, the permission view, the size and the cwd).
     Persistent, so a parker that has it (kfork's parent hands its child a
     copy) pays nothing for it.

     THE PREMISE IT REPLACES is the exec bundle.  [park_token_park] above
     demands [InitBoot.init_boot_bundle], because that park's resume runs
     kexec("/init") and the key comes out of it; this one demands ONE
     slot, at the parked record's own key, and the closer moves it onto
     the record the resume produces ([UexecRet.uslot_of_urun_eq]).  That is
     the shape a parent forking a VERIFIED program can pay: it has a
     continuation for its child at ONE record -- the trapframe it just
     copied with a0 := 0 -- and at no other.

     Everything else is [park_token_park]'s, row for row. *)
  Lemma park_token_park_steady `{CID : CpuId} (N : ut_names) (rest : list (mword 64))
      (U : ustate) (sts : list fdstate) (cs : gset gname) :
    ut_wf N ->
    length rest = 12%nat ->
    (* the parker's running token, in and out -- the cap's premise *)
    own_context cur_ctx -∗
    park_token (un_s N) -∗
    kernel_text -∗
    wire_inv -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    pslot_used_at (un_pj N) -∗
    stack_own (KTR := KT1) (add_vec (un_ks N) (mword_of_int 4096)) KSTACK_AV -∗
    park_env N -∗
    park_own N -∗
    (* THE BOOT ARM IS DEAD FOR THIS RECORD -- see the header above *)
    first_done -∗
    (* the child's descriptor-state fragments, at a named table, exactly as
       [park_token_park] takes them *)
    fd_frags (pv_fdg (us_V U)) sts -∗
    (* ...AND ITS CHILDREN ROW, AT A NAMED SET, on the fragments' route
       exactly: the row is one entry of the map [wait_lock] owns
       ([WaitInv.ch_frag]), born at boot with the slot and handed to the
       parker by allocproc ([SpecAllocproc.allocproc_post]), and the resume
       hands it into the residue re-keyed by the closer's own
       [pv_chg V' = pv_chg V] premise. *)
    ch_frag (pv_chg (us_V U)) (un_pj N) cs -∗
    (* ONE SLOT, AT THE PARKED RECORD, at the very table the fragments name *)
    (* AT THE BLOCK'S OWN GENERATION: the key's [UexecSlot.uvis_gen] is
       the field [ProcDefs.pv_gen], so the parked slot is keyed at it and
       nothing here chooses. *)
    uslot (uvis_of U sts (pv_gen (us_V U)) cs (un_pid N)) -∗
    (* the child's rows with the block WHOLE -- the steady mode's shape *)
    park_child (un_s N) (un_f N) (un_pj N) (un_ks N) rest (un_pid N) U true -∗
    |==> own_context cur_ctx ∗ proc_ctx (un_s N) (un_pj N).
  Proof.
    iIntros (Hwf Hrest)
      "Hrun #Htok #Htext #Hwire #Hkmap #Hmk Hstack #Henv Hown Hdone0 Hfrag Hch Hslot Hchild".
    assert (Hkav : (K_usertrap <= KSTACK_AV)%nat) by (vm_compute; lia).
    iPoseProof "Htok" as "Htok'".
    iEval (rewrite park_token_unfold /park_token_F) in "Htok'".
    iDestruct "Htok'" as (URB) "[#Hcap #Hchan]".
    iAssert (procs_inv (un_s N)) as "#Hprocs".
    { iDestruct "Henv" as "[Hcaps _]". iDestruct "Hcaps" as "(_ & $ & _)". }
    iAssert (park_globals cur_ctx (un_s N) (un_w N) (un_ft N) (un_f N) (un_tk N)) as "#Hglobp".
    { iDestruct "Henv" as "[Hcaps Hextra]".
      iApply (park_globals_of_park_env with "Hcaps Hextra"). }
    iDestruct ("Hchan" $! cur_ctx N KSTACK_AV with "[%] [%] [%]") as "Hclose";
      [reflexivity | exact Hwf | exact Hkav |].
    iApply ("Hcap" $! cpu_id cur_ctx (un_w N) (un_ft N) (un_f N) (un_tk N) (un_pj N)
              (un_ks N) rest (un_pid N) U sts cs KSTACK_AV true
              with "[%] [%] [%] Hrun [Hstack Hown Hclose Hfrag Hch Hslot Hdone0] [] Hchild").
    - exact Hrest.
    - destruct Hwf as (Hj & _). exists (un_j N). split; [reflexivity | exact Hj].
    - exact Hkav.
    - rewrite /park_pkg.
      (* ROW BY ROW, NOT [iFrame].  The mode row below is
         [FirstTok.first_done], whose [FsReady.fs_ready] half CONTAINS
         [kernel_text] and the device rows -- so a frame of the persistent
         names would reach inside it and hand back a bundle with those
         conjuncts already discharged, which is not [first_done] any more.
         (claude-notes/optimization.md: name the context side, construct the
         goal side.) *)
      iSplitR; [iExact "Htext"|].
      iSplitR; [iExact "Hwire"|].
      iSplitR; [iExact "Hkmap"|].
      iSplitR; [iExact "Hprocs"|].
      iSplitR; [iExact "Hglobp"|].
      iSplitR; [iExact "Hmk"|].
      iSplitL "Hstack"; [iExact "Hstack"|].
      (* the mode row: this park hands the package a run key, so it owes the
         evidence that the boot arm cannot run -- which is the premise *)
      iSplitL "Hdone0"; [iExact "Hdone0"|].
      iNext.
      iDestruct ("Hclose" with "Henv Hown") as "Hclose'".
      iIntros (h Xc pt' U')
        "%Hupt %Hnorm %Hptwf %Hfg %Hcg %Hgenp %Hcwi %Hrk #Hglob #Htfk #Hdone HW #Htc Htrap Hpriv Hfd Hiref".
      iEval (rewrite -Hfg) in "Hfrag".
      iEval (rewrite -Hcg) in "Hch".
      iSplitR "Hslot".
      + iApply ("Hclose'" $! h Xc pt' U' sts cs
                  with "[%] Hglob Htfk Hdone HW Htc Htrap Hpriv Hfd Hiref Hfrag Hch").
        exact Hupt.
      + (* THE RE-KEY -- the whole of the steady park.  The package's run key
           is the parked record's projection at the placeholder view, and the
           slot in hand is that same projection at [sts]: [urun_eq] reads
           neither, so the closer's premise is the fact this needs.  Then
           [uslot_of_urun_eq] moves the slot onto the record the resume
           produces, at the descriptor states the residue is about to carry. *)
        assert (Hrk' : urun_eq (uvis_of U sts (pv_gen (us_V U)) cs (un_pid N)) U')
          by exact Hrk.
        iApply (bi.equiv_entails_1_1 _ _
                  (uslot_of_urun_eq (uvis_of U sts (pv_gen (us_V U)) cs (un_pid N)) U'
                     sts (pv_gen (us_V U)) cs (un_pid N) Hrk'
                     eq_refl eq_refl eq_refl eq_refl)).
        iExact "Hslot".
    - iNext. iExact "Htok".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* INTRODUCING IT: from a proof of the cap at [W := the token] and the    *)
  (* residue's own channel.  [ProofForkretPark.park_token_intro] is the    *)
  (* one caller: the cap is [forkret_park_paid] and the channel is          *)
  (* [usertrap_res_bare_park], both at [URB := usertrap_res_bare].          *)
  (* ------------------------------------------------------------------- *)
  Lemma park_token_intro_of
      (URB : CpuId -> CurCtx -> uptd -> mword 64 -> ustate -> list fdstate -> gset gname -> mword 32 -> iProp Σ) (γs : list gname) :
    (forall N av, ut_park_intro_body URB (park_token (un_s N)) N av) ->
    park_cap URB (park_token γs) γs -∗
    park_token γs.
  Proof.
    iIntros (Hchan) "#Hcap".
    iEval (rewrite park_token_unfold /park_token_F).
    iExists URB. iFrame "Hcap".
    rewrite /park_chan. iModIntro.
    iIntros (ξp N av Hs Hwf Hav). iNext.
    iPoseProof (Hchan N av Hwf Hav) as "H". iSpecialize ("H" $! ξp).
    rewrite Hs. iExact "H".
  Qed.

End ParkCap.
