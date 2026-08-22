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
Require Import UsertrapRes.
From Kernel Require KernelSyms.
Require Import Xv6G.
Local Open Scope Z_scope.
Import Defs.

Section ParkCap.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* the saved-context head the park installs: forkret's entry, and the
     kernel stack's top -- [SpecAllocproc.forkret_pc]'s value *)
  Definition park_forkret_pc : mword 64 := mword_of_int KernelSyms.forkret.

  (* THE PACKAGE a parker hands in ([SpecForkretParkPaid.forkret_park_pkg]
     is this, verbatim).  [W] is what the residue closer is handed at the
     resume beside [first_done] and the timer capability. *)
  Definition park_pkg
      (URB : CpuId -> uptd -> mword 64 -> iProp Σ) (W : iProp Σ)
      (γs : list gname) (γf : gname) (pa ks : mword 64)
      (pid : mword 32) (av : nat) : iProp Σ :=
    (kernel_text ∗
     wire_inv ∗
     kmap_at tramp_vpn tramp_ppn KP_rx ∗
     procs_inv γs ∗
     pslot_used_at pa ∗
     stack_own (KTR := KT1) (add_vec ks (mword_of_int 4096)) av ∗
     (∀ (h : CpuId) (pt' : uptd) (V' : pprivate),
        ⌜pv_upt V' = pt'⌝ -∗
        ⌜ud_data pt' = ud_pas pt'⌝ -∗
        ⌜proc_pt_wf pt'⌝ -∗
        ut_tfk (CID := h) (add_vec ks (mword_of_int 4096)) V' -∗
        first_done -∗
        W -∗
        timer_cap (CID := h) -∗
        ut_trap_parked (CID := h) pa (add_vec ks (mword_of_int 4096)) av ∅ -∗
        proc_priv_nopt γf pa pid V' -∗
        fd_slots FDSPARE -∗
        iref_slots IREFSPARE -∗
        URB h pt' (add_vec ks (mword_of_int 4096))))%I.

  (* the child's own rows, the ones the park spends *)
  Definition park_child (γs : list gname) (γf : gname) (pa ks : mword 64)
      (rest : list (mword 64)) (pid : mword 32) (V : pprivate) : iProp Σ :=
    (is_kstack pa ks ∗
     ctx_cells (p_context pa) (park_forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) ∗
     proc_priv γf pa pid V ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE)%I.

  (* THE CAP, at a given [W]: the statement of
     [SpecForkretParkPaid.forkret_park_paid_body], as a [□] wand *)
  Definition park_cap
      (URB : CpuId -> uptd -> mword 64 -> iProp Σ) (W : iProp Σ)
      (γs : list gname) : iProp Σ :=
    (□ ∀ (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
         (pid : mword 32) (V : pprivate) (av : nat),
       ⌜length rest = 12%nat⌝ -∗
       ⌜exists j : nat, pa = proc_addr j /\ (j < NPROC)%nat⌝ -∗
       ⌜(K_usertrap <= av)%nat⌝ -∗
       ▷ park_pkg URB W γs γf pa ks pid av -∗
       (* ...and [W] itself, for forkret to hand the closer: under the same
          later, for the same reason *)
       ▷ W -∗
       park_child γs γf pa ks rest pid V -∗
       |==> ▷ proc_ctx γs pa)%I.

  (* THE CHANNEL, at a given [W], as a [□] proposition under a later -- for
     the records of THIS table ([un_s N = γs]), which is all the token for
     [γs] ever parks *)
  Definition park_chan
      (URB : CpuId -> uptd -> mword 64 -> iProp Σ) (W : iProp Σ)
      (γs : list gname) : iProp Σ :=
    (□ ∀ (N : ut_names) (av : nat),
       ⌜un_s N = γs⌝ -∗ ⌜ut_wf N⌝ -∗ ⌜(K_usertrap <= av)%nat⌝ -∗
       ▷ (park_env N -∗ park_own N -∗
          (∀ (h : CpuId) (pt' : uptd) (V' : pprivate),
             ⌜pv_upt V' = pt'⌝ -∗
             ut_tfk (CID := h) (add_vec (un_ks N) (mword_of_int 4096)) V' -∗
             first_done -∗
             W -∗
             timer_cap (CID := h) -∗
             ut_trap_parked (CID := h) (un_pj N)
               (add_vec (un_ks N) (mword_of_int 4096)) av ∅ -∗
             proc_priv_nopt (un_f N) (un_pj N) (un_pid N) V' -∗
             fd_slots FDSPARE -∗
             iref_slots IREFSPARE -∗
             URB h pt' (add_vec (un_ks N) (mword_of_int 4096)))))%I.

  (* THE TOKEN: some residue, its cap and its channel, both at [W := the
     token itself] *)
  Definition park_token_F (γs : list gname) (X : iProp Σ) : iProp Σ :=
    (∃ URB : CpuId -> uptd -> mword 64 -> iProp Σ,
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
  (* ------------------------------------------------------------------- *)
  Lemma park_token_park (N : ut_names) (rest : list (mword 64)) (V : pprivate) :
    ut_wf N ->
    length rest = 12%nat ->
    park_token (un_s N) -∗
    kernel_text -∗
    wire_inv -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    pslot_used_at (un_pj N) -∗
    stack_own (KTR := KT1) (add_vec (un_ks N) (mword_of_int 4096)) KSTACK_AV -∗
    park_env N -∗
    park_own N -∗
    park_child (un_s N) (un_f N) (un_pj N) (un_ks N) rest (un_pid N) V -∗
    |==> ▷ proc_ctx (un_s N) (un_pj N).
  Proof.
    iIntros (Hwf Hrest) "#Htok #Htext #Hwire #Hkmap #Hslot Hstack #Henv Hown Hchild".
    assert (Hkav : (K_usertrap <= KSTACK_AV)%nat) by (vm_compute; lia).
    iPoseProof "Htok" as "Htok'".
    iEval (rewrite park_token_unfold /park_token_F) in "Htok'".
    iDestruct "Htok'" as (URB) "[#Hcap #Hchan]".
    iAssert (procs_inv (un_s N)) as "#Hprocs".
    { iDestruct "Henv" as "[Hcaps _]". iDestruct "Hcaps" as "(_ & _ & $ & _)". }
    iDestruct ("Hchan" $! N KSTACK_AV with "[%] [%] [%]") as "Hclose";
      [reflexivity | exact Hwf | exact Hkav |].
    iApply ("Hcap" $! (un_f N) (un_pj N) (un_ks N) rest (un_pid N) V KSTACK_AV
              with "[%] [%] [%] [Hstack Hown Hclose] [] Hchild").
    - exact Hrest.
    - destruct Hwf as (Hj & _). exists (un_j N). split; [reflexivity | exact Hj].
    - exact Hkav.
    - rewrite /park_pkg.
      iNext.
      iFrame "Htext Hwire Hkmap Hprocs Hslot Hstack".
      iDestruct ("Hclose" with "Henv Hown") as "Hclose'".
      iIntros (h pt' V') "%Hupt %Hnorm %Hptwf #Htfk #Hdone HW #Htc Htrap Hpriv Hfd Hiref".
      iApply ("Hclose'" $! h pt' V' with "[%] Htfk Hdone HW Htc Htrap Hpriv Hfd Hiref").
      exact Hupt.
    - iNext. iExact "Htok".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* INTRODUCING IT: from a proof of the cap at [W := the token] and the    *)
  (* residue's own channel.  [ProofForkretPark.park_token_intro] is the    *)
  (* one caller: the cap is [forkret_park_paid] and the channel is          *)
  (* [usertrap_res_bare_park], both at [URB := usertrap_res_bare].          *)
  (* ------------------------------------------------------------------- *)
  Lemma park_token_intro_of
      (URB : CpuId -> uptd -> mword 64 -> iProp Σ) (γs : list gname) :
    (forall N av, ut_park_intro_body URB (park_token (un_s N)) N av) ->
    park_cap URB (park_token γs) γs -∗
    park_token γs.
  Proof.
    iIntros (Hchan) "#Hcap".
    iEval (rewrite park_token_unfold /park_token_F).
    iExists URB. iFrame "Hcap".
    rewrite /park_chan. iModIntro.
    iIntros (N av Hs Hwf Hav). iNext.
    iPoseProof (Hchan N av Hwf Hav) as "H". rewrite Hs. iExact "H".
  Qed.

End ParkCap.
