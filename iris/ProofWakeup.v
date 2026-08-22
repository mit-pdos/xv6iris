(* ProofWakeup.v -- the wakeup proc[]-table loop over the SIE-agnostic
   sconf world (kalloc cone, stage 8).  The sconf mirror of [wp_wakeup_loop]
   (CodeWakeup.v): a bounded fuel induction over the 64-entry proc[] table
   that, per proc, acquires the proc lock, CLEARS [p->chan] if it matches,
   wakes the proc if it was also SLEEPING, and releases -- threading the
   counting token [intr_count] NET-ZERO across each acquire/release pair
   (acquire lvl->S lvl, release S lvl->lvl).

   THE SCAN NO LONGER SKIPS ITSELF (upstream ae96fd0): there is no [myproc]
   call and no [p != myproc()] guard, so the loop head at 0x38 is the acquire
   itself.  Reaching the caller's OWN slot costs no new resource: p->lock
   hands out only the invariant's half of the state mirror, and the write arm
   is licensed by the state READ being SLEEPING -- an unclaimed state, at
   which [SchedCtx.pstate_lock] carries BOTH halves.  The proof therefore
   never learns which slot is the caller's; it cases on the value read,
   exactly as it does for every other slot.  [p->chan] sits at the top level
   of [proc_lock_res], so clearing it is free at every state.

   EXPLICIT-CPUID NOTE.  wakeup is [b]-GENERIC and it CALLS things (acquire,
   release) at that index, so a trap taken anywhere outside the lock-held
   stretch may migrate the thread.  Consequently the LOOP INVARIANT itself is
   hart-generic: it is a [wp_next b (fun CID => ...)], the shape whose
   obligation composes with [wp_next_chain].  Three propositions carry the
   hart that way -- the loop head (0x38), the shared p++/test tail (0x30)
   and the exit continuation (0x54) -- and all three are ANCHORED AT THE
   LEMMA'S OWN [CID0], so forwarding one across an iteration is the identity
   and only a USE needs the chained equality.

   The stretch between acquire's return and release's call runs at the literal
   index [false] (a held lock pins noff >= 1), so the hart cannot move there:
   those leaves collapse with [wp_next_off] and read exactly as they did
   before the refactor.  That is also why the release tail [Hrel] needs no
   hart binder.

   tp: [callee_saved] no longer preserves x4 and [tp_pin] makes any claim
   about the map's tp slot vacuous, so the loop's register shape [wkl_regs]
   below carries none -- and with the tp conjunct go the loop's [rtp]/[a0f]
   parameters, whose only consumers were the tp premises of
   acquire/release. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved.
Require Import RiscvExtras.
Require Import IntrDefs HartTp WpNext.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import SpecAcquire SpecRelease.
Require Import CodeWakeup SpecWakeupParts.
Require Import FdSlots.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcGeom.
Require Import SpecWakeup.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* wakeup's 7-entry callee-save frame, over [SpecWakeupParts.wk_fcell]: ra/s0
   and s1..s5 at spF+56 down to spF+8, written by the prologue and read back
   by the epilogue. *)
Definition wk_frame `{!riscvGS Σ} (spF : mword 64)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 : mword 64) : iProp Σ :=
  (wk_fcell spF 7 ↦₈[KT1] vra ∗ wk_fcell spF 6 ↦₈[KT1] vs0 ∗ wk_fcell spF 5 ↦₈[KT1] vs1 ∗
   wk_fcell spF 4 ↦₈[KT1] vs2 ∗ wk_fcell spF 3 ↦₈[KT1] vs3 ∗ wk_fcell spF 2 ↦₈[KT1] vs4 ∗
   wk_fcell spF 1 ↦₈[KT1] vs5)%I.

(* a state cell holding a value whose 64-bit sign-extension is 2 is SLEEPING;
   used in the wake path where the c.lw-loaded [sext st] compared equal to
   s3 = 2. *)
Lemma wk_sext_sleeping (st : mword 32) :
  sign_extend' 64 st = (mword_of_int 2 : mword 64) -> st = SLEEPING.
Proof.
  intro H.
  assert (Ht : trunc32 (sign_extend' 64 st) = trunc32 (mword_of_int 2 : mword 64))
    by (rewrite H; reflexivity).
  rewrite trunc32_sext64 in Ht. rewrite Ht. apply bv_eq; vm_compute; reflexivity.
Qed.

(* the register shape the loop invariant threads through every iteration,
   minus the tp conjunct; see the header. *)
Definition wkl_regs (M : regfile) (spF chan : mword 64)
    (vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (k : nat) : Prop :=
  M !!! Regidx (mword_of_int 9)  = proc_addr k /\
  M !!! Regidx (mword_of_int 2)  = spF /\
  M !!! Regidx (mword_of_int 18) = chan /\
  M !!! Regidx (mword_of_int 19) = proc_addr NPROC /\
  M !!! Regidx (mword_of_int 20) = (mword_of_int 2 : mword 64) /\
  M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64) /\
  M !!! Regidx (mword_of_int 22) = vs6 /\
  M !!! Regidx (mword_of_int 23) = vs7 /\
  M !!! Regidx (mword_of_int 24) = vs8 /\
  M !!! Regidx (mword_of_int 25) = vs9 /\
  M !!! Regidx (mword_of_int 26) = vs10 /\
  M !!! Regidx (mword_of_int 27) = vs11 /\
  (forall r : regidx, r ∈ dom (rf_to_gmap M)).


Module WakeupProof (Acquire : ACQUIRE) (Release : RELEASE) (WakeupParts : WAKEUPPARTS) : WAKEUP.

Section ProofWakeup.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  (* NO [Context `{GEN : GenId} `{CID : CpuId}]: the loop lemma is applied at the hart the
     prologue's own [wp_next] hands back, which a section variable could not
     express.  Every lemma below takes its own implicit [CID0]. *)

  (* ---- THE BLOCK CONTINUATIONS, NAMED (RULE ONE,
     claude-notes/optimization.md): each stays TRANSPARENT so a later
     [iSpecialize]/[iApply] still unifies through it, and only the part
     AFTER [fun CIDx : CpuId =>] is folded -- the surrounding
     [wp_next]/[∀ fuel] stay syntactically visible at every site that
     states them.  Unlike [ProofNamex]/[ProofDirlookup] this section has NO
     [Context `{GEN : GenId} `{CID : CpuId}] (file header: the loop lemma is
     applied at whatever hart the prologue's [wp_next] hands back, which a
     section variable could not express), so each definition below that
     calls [wp_next]/[pc_is]/[sie_cap_gpr]/[cpu_own] takes its own [GEN] and
     the relevant hart(s) as explicit/generalized arguments instead. *)

  (* the loop's exit continuation, control at the epilogue entry
     [wakeup+0x54]: the SAME statement is both the lemma's own [Hqexit]
     hypothesis below and the tail [wk_loop_body] hands [wp_next] on exit
     (both anchored at the lemma's own [CID0], per the file header). *)
  Definition wk_exit_body `{GEN : GenId}
      (pme spF : mword 64) (vra vs0 vs1 vs2 vs3 vs4 vs5
       vs6 vs7 vs8 vs9 vs10 vs11 : mword 64)
      (av lvl : nat) (eb : bool) (b : bool) (lks : gset string)
      (CID : CpuId) : iProp Σ :=
    (∀ Mexit : regfile,
       ⌜ Mexit !!! Regidx csp_rs1 = spF
         /\ Mexit !!! Regidx (mword_of_int 22) = vs6
         /\ Mexit !!! Regidx (mword_of_int 23) = vs7
         /\ Mexit !!! Regidx (mword_of_int 24) = vs8
         /\ Mexit !!! Regidx (mword_of_int 25) = vs9
         /\ Mexit !!! Regidx (mword_of_int 26) = vs10
         /\ Mexit !!! Regidx (mword_of_int 27) = vs11
         /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mexit)) ⌝ -∗
       sie_cap_gpr KT1 Mexit av b pme -∗
       cpu_own lvl eb pme b lks -∗
       kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x54)) -∗
       wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
       WP (Loop : expr riscv_lang))%I.

  (* the fuel-indexed scan invariant at the loop head [wakeup+0x38]; the
     [∀ fuel]/[wp_next] wrapper stays at each [iAssert] site (RULE 3), only
     what follows [fun CID : CpuId =>] is named here. *)
  Definition wk_loop_body `{GEN : GenId}
      (pme spF chan : mword 64) (vra vs0 vs1 vs2 vs3 vs4 vs5
       vs6 vs7 vs8 vs9 vs10 vs11 : mword 64)
      (av lvl : nat) (eb : bool) (b : bool) (lks : gset string)
      (CID0 : CpuId) (fuel : nat) (CID : CpuId) : iProp Σ :=
    (∀ (k : nat) (M : regfile),
       ⌜(NPROC - k <= fuel)%nat⌝ -∗ ⌜(k < NPROC)%nat⌝ -∗
       ⌜wkl_regs M spF chan vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
       wp_next (CID0 := CID0) b pme (fun (CIDq : CpuId) =>
         wk_exit_body pme spF vra vs0 vs1 vs2 vs3 vs4 vs5
           vs6 vs7 vs8 vs9 vs10 vs11 av lvl eb b lks CIDq) -∗
       sie_cap_gpr KT1 M av b pme -∗
       cpu_own lvl eb pme b lks -∗
       kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗
       wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
       WP (Loop : expr riscv_lang))%I.

  (* the shared release tail [Hrel] both arms of the state test (and the
     chan-mismatch exit) hand control to; the whole stretch back to the
     release call runs at the FIXED hart [CID] (a held lock pins
     noff >= 1, file header), so unlike the two definitions above this one
     carries no [wp_next]/hart binder of its own. *)
  Definition wk_rel_body `{GEN : GenId}
      (γs : list gname) (γk : gname) (pme spF chan : mword 64)
      (av lvl k : nat) (eb b : bool)
      (vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (CID : CpuId) : iProp Σ :=
    (∀ (Mr : regfile),
       ⌜ Mr !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k /\
         Mr !!! Regidx (mword_of_int 2 : mword 5) = spF /\
         Mr !!! Regidx (mword_of_int 18 : mword 5) = chan /\
         Mr !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC /\
         Mr !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 2 : mword 64) /\
         Mr !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64) /\
         Mr !!! Regidx (mword_of_int 22 : mword 5) = vs6 /\
         Mr !!! Regidx (mword_of_int 23 : mword 5) = vs7 /\
         Mr !!! Regidx (mword_of_int 24 : mword 5) = vs8 /\
         Mr !!! Regidx (mword_of_int 25 : mword 5) = vs9 /\
         Mr !!! Regidx (mword_of_int 26 : mword 5) = vs10 /\
         Mr !!! Regidx (mword_of_int 27 : mword 5) = vs11 /\
         (forall r : regidx, r ∈ dom (rf_to_gmap Mr)) ⌝ -∗
       sie_cap_gpr KT1 (CID := CID) Mr (trap_res b + av)%nat false pme -∗
       pc_is (CID := CID) (mword_of_int (KernelSyms.wakeup + 0x2a)) -∗
       locked γk CID -∗ proc_lock_res γs γk (proc_addr k) -∗
       WP (LoopE gen_id CID : expr riscv_lang))%I.

  (* wakeup only RELAYS parked contexts (SLEEPING->RUNNABLE, untouched), never
     resumes them, so [proc_lock_res] (SchedCtx.v, whose context slot is the
     ▷-guarded [proc_ctx] over the scheduler swtch chain) is threaded OPAQUELY
     here: the ▷-slot is carried between elim and intro/wakeup, never stripped. *)
  Lemma wp_wakeup_loop_sconf `{GEN : GenId} `{CID0 : CpuId}
      
      (γs : list gname) (spF pme chan : mword 64)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 : mword 64)
      (vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (lvl : nat) (av : nat)
      (eb : bool) (b : bool) (lks : gset string) :
    length γs = NPROC ->
    (* the acquire/release + myproc push_off keep the transient +1 in range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (10 <= av)%nat ->
    (* acquire's order premise, threaded to every iteration's acquire/release
       pair -- see [wp_wakeup_sconf] where it originates *)
    locks_below lks "proc" ->
    procs_inv γs -∗
    (* acquire's "already holding" arm sits above panic() *)
    (* the loop's exit continuation: control at the epilogue entry [wakeup+0x54],
       at whatever hart the scan ended on. *)
    wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
      wk_exit_body pme spF vra vs0 vs1 vs2 vs3 vs4 vs5
        vs6 vs7 vs8 vs9 vs10 vs11 av lvl eb b lks CID) -∗
    ∀ (k : nat) (M : regfile),
      ⌜(k < NPROC)%nat⌝ -∗ ⌜wkl_regs M spF chan vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
      sie_cap_gpr KT1 M av b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗
      wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen Hlvl Hav Hfresh.
    iIntros "#Hpinv Hqexit".
    (* BOUNDED loop: ordinary Coq induction on a [fuel] bounding the remaining
       iterations [NPROC - k] -- no Löb needed.  The body is a [wp_next b]
       so the induction hypothesis is re-enterable at a migrated hart. *)
    iAssert (∀ (fuel : nat),
               wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
                 wk_loop_body pme spF chan vra vs0 vs1 vs2 vs3 vs4 vs5
                   vs6 vs7 vs8 vs9 vs10 vs11 av lvl eb b lks CID0 fuel CID))%I
      with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown Htext Hpc Hframe".
        exfalso. lia. }
      iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown #Htext Hpc Hframe".
      destruct Hregs as (Hs1 & Hsp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11 & Hdom).
      iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbmatch. symmetry in Hbmatch.
      (* ---- shared tail [pc = wakeup+0x30]: p++ (0x30 addi s1,s1,360), then the
         termination test (0x34 beq s1,s3): exit to the epilogue at wakeup+0x54,
         else recurse into iteration k+1.  Reached only from the release return
         (0x2c) now that the self-skip is gone, but still at an ARBITRARY hart,
         hence the [wp_next] wrapper. ---- *)
      iAssert (wp_next (CID0 := CID0) b pme (fun (CIDt : CpuId) =>
                 ∀ Mt : regfile,
                   ⌜ wkl_regs Mt spF chan vs6 vs7 vs8 vs9 vs10 vs11 k ⌝ -∗
                   sie_cap_gpr KT1 Mt av b pme -∗
                   cpu_own lvl eb pme b lks -∗
                   pc_is (mword_of_int (KernelSyms.wakeup + 0x30)) -∗
                   wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
                   WP (Loop : expr riscv_lang)))%I
        with "[Hqx]" as "Htail".
      { iIntros (CIDt Hst Mt) "%Hmt Hcg Hown Hpc Hframe".
        destruct Hmt as (Ht1 & Htsp & Ht18 & Ht19 & Ht20 & Ht21 & Ht22 & Ht23 & Ht24 & Ht25 & Ht26 & Ht27 & Htdom).
        iPoseProof (wki_30 with "Htext") as "Hi30".
        iPoseProof (wki_34 with "Htext") as "Hi34".
        (* 0x30 addi s1,s1,360 : s1 := &proc[k+1] *)
        assert (Hrgt9 : rget (CID := CIDt) Mt (mword_of_int 9 : mword 5)
                        = Mt !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        iApply (wp_addi4_s_sconf (CID := CIDt) (mword_of_int (KernelSyms.wakeup + 0x30))
                  (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 360 : mword 12)
                  Mt av b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi30").
        iIntros (CIDt1 Hst1) "Hcg Hpc".
        iEval (rewrite Hrgt9) in "Hcg".
        set (Mt30 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
             (add_vec (Mt !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> Mt).
        assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x34))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp34) in "Hpc".
        assert (HMt30_9 : Mt30 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr (S k)).
        { rewrite /Mt30 upd_eq. rewrite Ht1. apply (proc_addr_succ k). }
        assert (HMt30_19 : Mt30 !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC).
        { rewrite /Mt30 upd_ne; [| vm_compute; discriminate]. exact Ht19. }
        (* 0x34 beq s1,s3 : exit iff &proc[k+1] = &proc[NPROC]. *)
        assert (Hrg30_9 : rget (CID := CIDt1) Mt30 (mword_of_int 9 : mword 5)
                          = Mt30 !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        assert (Hrg30_19 : rget (CID := CIDt1) Mt30 (mword_of_int 19 : mword 5)
                           = Mt30 !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
        destruct (eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                         (Mt30 !!! Regidx (mword_of_int 19 : mword 5))) eqn:Hcmp.
        + (* TAKEN: p reached &proc[NPROC]; exit to epilogue at wakeup+0x54 *)
          assert (Hcmpr : eq_vec (rget (CID := CIDt1) Mt30 (mword_of_int 9 : mword 5))
                                 (rget (CID := CIDt1) Mt30 (mword_of_int 19 : mword 5)) = true)
            by (rewrite Hrg30_9 Hrg30_19; exact Hcmp).
          iApply (wp_beq_taken_s_sconf (CID := CIDt1) (mword_of_int (KernelSyms.wakeup + 0x34))
                    (mword_of_int 32 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 9 : mword 5)
                    Mt30 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi34").
          iNext. iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (Htgt54 : add_vec (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64)
                             (sign_extend' 64 (mword_of_int 32 : mword 13)) = mword_of_int (KernelSyms.wakeup + 0x54))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt54) in "Hpc".
          iDestruct (cpu_own_transport CIDt CIDt2 lvl eb pme b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("Hqx" $! CIDt2 with "[%]"); [wp_next_chain|].
          iApply ("Hqx" $! Mt30 with "[] Hcg Hown Htext Hpc Hframe").
          iPureIntro.
          split; [rewrite /Mt30 upd_ne; [exact Htsp | vm_compute; discriminate]|].
          split; [rewrite /Mt30 upd_ne; [exact Ht22 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 upd_ne; [exact Ht23 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 upd_ne; [exact Ht24 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 upd_ne; [exact Ht25 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 upd_ne; [exact Ht26 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 upd_ne; [exact Ht27 | vm_compute; discriminate]|].
          intro r. rewrite /Mt30 rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Htdom.
        + (* FALL: p < &proc[NPROC]; recurse into iteration k+1 *)
          assert (Hcmpr : eq_vec (rget (CID := CIDt1) Mt30 (mword_of_int 9 : mword 5))
                                 (rget (CID := CIDt1) Mt30 (mword_of_int 19 : mword 5)) = false)
            by (rewrite Hrg30_9 Hrg30_19; exact Hcmp).
          iApply (wp_beq_fall_s_sconf (CID := CIDt1) (mword_of_int (KernelSyms.wakeup + 0x34))
                    (mword_of_int 32 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 9 : mword 5)
                    Mt30 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr with "Hcg Hpc Hi34").
          iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (HkS : (S k < NPROC)%nat).
          { destruct (Nat.lt_ge_cases (S k) NPROC) as [Hlt | Hge]; [exact Hlt|].
            assert (HeqN : S k = NPROC) by lia.
            exfalso.
            assert (Hbad : eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                             (Mt30 !!! Regidx (mword_of_int 19 : mword 5)) = true).
            { rewrite HMt30_9 HMt30_19 HeqN. apply eq_vec_refl. }
            rewrite Hcmp in Hbad. discriminate. }
          assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x38))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp38) in "Hpc".
          iDestruct (cpu_own_transport CIDt CIDt2 lvl eb pme b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("IHf" $! CIDt2 with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S k) Mt30 with "[%] [%] [%] Hqx Hcg Hown Htext Hpc Hframe").
          * lia.
          * exact HkS.
          * unfold wkl_regs.
            split; [exact HMt30_9|].
            split; [rewrite /Mt30 upd_ne; [exact Htsp | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht18 | vm_compute; discriminate]|].
            split; [exact HMt30_19|].
            split; [rewrite /Mt30 upd_ne; [exact Ht20 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht21 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht22 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht23 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht24 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht25 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht26 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 upd_ne; [exact Ht27 | vm_compute; discriminate]|].
            intro r. rewrite /Mt30 rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Htdom. }
      (* ==================== loop body [0x38 .. 0x30] ==================== *)
      (* the per-proc lock for proc[k] and its protected resource. *)
      destruct (lookup_lt_is_Some_2 γs k ltac:(rewrite Hlen; exact Hk)) as [γk Hγk].
      iDestruct (procs_inv_lookup γs k γk Hγk with "Hpinv") as "#Hlockk".
      (* ---- 0x38 c.mv a0,s1 : a0 := &proc[k] ---- *)
      iPoseProof (wki_38 with "Htext") as "Hi38".
      assert (Hrgk9 : rget (CID := CIDk) M (mword_of_int 9 : mword 5)
                      = M !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
      iApply (wp_cmv_s_sconf (CID := CIDk) (mword_of_int (KernelSyms.wakeup + 0x38))
                (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                M av b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi38").
      iIntros (CIDd Hsd) "Hcg Hpc".
      iEval (rewrite Hrgk9) in "Hcg".
      set (M38 := <[Regidx (mword_of_int 10 : mword 5) :=
                    regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M).
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) 2
                      = mword_of_int (KernelSyms.wakeup + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* ---- 0x3a jal ra,acquire ---- *)
      iPoseProof (wki_3a with "Htext") as "Hi3a".
      iApply (wp_jal_s_sconf (CID := CIDd) (mword_of_int (KernelSyms.wakeup + 0x3a))
                (mword_of_int 1 : mword 5) (mword_of_int 2092080 : mword 21) M38 av b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a").
      iIntros (CIDe Hse) "Hcg Hpc".
      set (M3a := <[Regidx (mword_of_int 1 : mword 5) :=
                    regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x3a) : mword 64) 4)]> M38).
      assert (Hjtgt_aq : add_vec (mword_of_int (KernelSyms.wakeup + 0x3a) : mword 64)
                          (sign_extend' 64 (mword_of_int 2092080 : mword 21)) = mword_of_int KernelSyms.acquire)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjtgt_aq) in "Hpc".
      assert (HM3a_ra : M3a !!! Regidx (mword_of_int 1 : mword 5)
                        = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x3a) : mword 64) 4)
        by (rewrite /M3a; apply upd_eq).
      assert (HM3a_a0 : M3a !!! Regidx (mword_of_int 10 : mword 5) = proc_addr k).
      { rewrite /M3a upd_ne; [| vm_compute; discriminate].
        rewrite /M38 upd_eq. rewrite add_vec_zero_l. exact Hs1. }
      (* acquire(&proc[k]->lock): cpu_own lvl -> S lvl; returns locked +
         proc_lock_res + pay.  NOTE the slot may be the CALLER'S OWN -- nothing
         here or below needs to know, see the file header. *)
      iDestruct (cpu_own_transport CIDk CIDe lvl eb pme b ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iApply (Acquire.wp_acquire_sconf KT1 (CID := CIDe) γk "proc"%string (proc_lock_res γs γk (proc_addr k)) M3a
                lvl eb pme av b lks
                ltac:(lia)
                ltac:(lia)
                Hfresh
                with "Hcg Hown Htext Hpc [Hlockk]").
      all: try lkbelow.
      { iEval (rewrite HM3a_a0). iExact "Hlockk". }
      iIntros (CIDf Hsf ms Macq) "%Hms Hcg Hpc %Hpins Htok HR Hown Hpay".
      (* acquire returned: pc = wakeup+0x3e, cpu_own (S lvl) + trap_csrs_pay lvl eb.
         FROM HERE TO THE RELEASE the index is the literal [false] (a held lock
         pins noff >= 1), so no leaf can migrate and everything stays at CIDf. *)
      assert (Hpc3e : ret_pc (M3a !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.wakeup + 0x3e)).
      { rewrite HM3a_ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc3e) in "Hpc".
      iDestruct (proc_lock_res_elim γs γk (proc_addr k) with "HR") as (st ch) "(Hpst & Hpg & Hpch & Hpub & Hctx)".
      (* Macq's callee-saved registers all equal the loop-entry values: compose
         [callee_saved] across the a0/ra writes + acquire (Hpins), then project. *)
      assert (HcsM38 : callee_saved M M38).
      { rewrite /M38. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
      assert (HcsM3a : callee_saved M M3a).
      { rewrite /M3a. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsM38]. }
      assert (HcsMacq : callee_saved M Macq) by (eapply callee_saved_trans; [exact HcsM3a | exact Hpins]).
      assert (HMacq9 : Macq !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs1).
      assert (HMacq2 : Macq !!! Regidx (mword_of_int 2 : mword 5) = spF)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)); exact Hsp).
      assert (HMacq18 : Macq !!! Regidx (mword_of_int 18 : mword 5) = chan)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs2).
      assert (HMacq19 : Macq !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs3).
      assert (HMacq20 : Macq !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 2 : mword 64))
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs4).
      assert (HMacq21 : Macq !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs5).
      assert (HMacq22 : Macq !!! Regidx (mword_of_int 22 : mword 5) = vs6)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs6).
      assert (HMacq23 : Macq !!! Regidx (mword_of_int 23 : mword 5) = vs7)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs7).
      assert (HMacq24 : Macq !!! Regidx (mword_of_int 24 : mword 5) = vs8)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs8).
      assert (HMacq25 : Macq !!! Regidx (mword_of_int 25 : mword 5) = vs9)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs9).
      assert (HMacq26 : Macq !!! Regidx (mword_of_int 26 : mword 5) = vs10)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs10).
      assert (HMacq27 : Macq !!! Regidx (mword_of_int 27 : mword 5) = vs11)
        by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs11).
      assert (Hdomacq : forall r : regidx, r ∈ dom (rf_to_gmap Macq)) by (intro r; apply rf_to_gmap_dom).
      (* =============================================================== *)
      (* shared release tail [Hrel], reached from all 3 exits (chan       *)
      (* mismatch, chan cleared but not SLEEPING, or after waking):       *)
      (* 0x2a mv a0,s1; 0x2c jal release (intr_count S lvl -> lvl); then  *)
      (* the p++ tail at 0x30.                                            *)
      (* Stated at the FIXED hart CIDf -- the whole stretch is at [false]. *)
      (* =============================================================== *)
      iAssert (wk_rel_body γs γk pme spF chan av lvl k eb b
                 vs6 vs7 vs8 vs9 vs10 vs11 CIDf)%I
        with "[Hown Hpay Hframe Htail]"
        as "Hrel".
      { iIntros (Mr) "%Hmr Hcg Hpc Htok HR".
        destruct Hmr as (Hr9 & Hr2 & Hr18 & Hr19 & Hr20 & Hr21 & Hr22 & Hr23 & Hr24 & Hr25 & Hr26 & Hr27 & Hrdom).
        iPoseProof (wki_2a with "Htext") as "Hi2a".
        iPoseProof (wki_2c with "Htext") as "Hi2c".
        (* 0x2a c.mv a0,s1 : a0 := &proc[k] *)
        assert (Hrgr9 : rget (CID := CIDf) Mr (mword_of_int 9 : mword 5)
                        = Mr !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x2a))
                  (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  Mr (trap_res b + av)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi2a").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        iEval (rewrite Hrgr9) in "Hcg".
        set (Mr2a := <[Regidx (mword_of_int 10 : mword 5) :=
                       regval_into_reg (add_vec zero_reg (Mr !!! Regidx (mword_of_int 9 : mword 5)))]> Mr).
        assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.wakeup + 0x2c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2c) in "Hpc".
        (* 0x2c jal ra,release *)
        iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x2c))
                  (mword_of_int 1 : mword 5) (mword_of_int 2092230 : mword 21) Mr2a (trap_res b + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi2c").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        set (Mr2c := <[Regidx (mword_of_int 1 : mword 5) :=
                       regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) 4)]> Mr2a).
        assert (Hjtgt_rl : add_vec (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64)
                            (sign_extend' 64 (mword_of_int 2092230 : mword 21)) = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjtgt_rl) in "Hpc".
        assert (HMr2c_ra : Mr2c !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) 4)
          by (rewrite /Mr2c; apply upd_eq).
        assert (HMr2c_a0 : Mr2c !!! Regidx (mword_of_int 10 : mword 5) = proc_addr k).
        { rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_eq. rewrite add_vec_zero_l. exact Hr9. }
        assert (HMr2c_csp : Mr2c !!! Regidx csp_rs1 = spF).
        { rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr2. }
        (* release premises, pre-established over the opaque loop map [Mr2c]. *)
        assert (Hlka2 : add_vec (Mr2c !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k)
          by (rewrite HMr2c_a0; apply addv_sext0).
        (* release(&proc[k]->lock): cpu_own S lvl -> lvl (pay consumed).  Its
           exit index is the very [match] [b] is equal to, so the back edge
           lands on the loop invariant unchanged. *)
        (* [b] IS [outb] ([cpu_own] forces it, = [Hbmatch]); pure re-spelling
           so that the acquire/release pair composes back to [av]. *)
        iEval (rewrite Hbmatch) in "Hcg".
        iApply (Release.wp_release_sconf KT1 (CID := CIDf) γk (proc_addr k) "proc"%string (proc_lock_res γs γk (proc_addr k)) Mr2c
                  lvl eb pme av ({["proc"]} ∪ lks)
                  Hlka2
                  ltac:(lia)
                  with "Hcg Htext Hpc Hlockk Htok HR Hown Hpay").
        rewrite -Hbmatch.
        iIntros (CIDg Hsg mr) "Hcg Hpc %Hpinsr Hown".
        (* each iteration is BALANCED: what it acquired it released, so the
           set release hands back collapses to the loop invariant's [lks]. *)
        pose proof (locks_below_not_elem lks "proc" Hfresh) as Hnotin.
        assert (Hsetback : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
        iEval (rewrite Hsetback) in "Hown".
        (* pc = wakeup+0x30 (release's return target). *)
        assert (Hpc30 : ret_pc (Mr2c !!! Regidx (mword_of_int 1 : mword 5))
                        = mword_of_int (KernelSyms.wakeup + 0x30)).
        { rewrite HMr2c_ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpc30) in "Hpc".
        assert (Hdommr : forall r : regidx, r ∈ dom (rf_to_gmap mr)) by (intro r; apply rf_to_gmap_dom).
        iSpecialize ("Htail" $! CIDg with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! mr with "[%] Hcg Hown Hpc Hframe").
        (* wkl_regs mr spF chan k *)
        unfold wkl_regs.
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr9. }
        split; [rewrite (callee_saved_lookup Hpinsr (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)); exact HMr2c_csp|].
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr18. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr19. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr20. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr21. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr22. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr23. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr24. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr25. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr26. }
        split.
        { rewrite (callee_saved_lookup Hpinsr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mr2c upd_ne; [| vm_compute; discriminate].
          rewrite /Mr2a upd_ne; [| vm_compute; discriminate]. exact Hr27. }
        exact Hdommr. }
      (* ===== 0x3e..0x52: chan test, chan clear, state test + wake, then Hrel ===== *)
      (* ---- 0x3e c.ld a5,32(s1) : a5 := p->chan ---- *)
      iPoseProof (wki_3e with "Htext") as "Hi3e".
      assert (Hea3e : add_vec (rget (CID := CIDf) Macq (mword_of_int 9 : mword 5))
                        (sign_extend' 64 (mword_of_int 32 : mword 12)) = p_chan (proc_addr k)).
      { rewrite (rget_ne Macq (mword_of_int 9 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
        rewrite HMacq9. rewrite /p_chan /chan_off.
        replace (sign_extend' 64 (mword_of_int 32 : mword 12)) with (mword_of_int 32 : mword 64)
          by (apply bv_eq; vm_compute; reflexivity).
        reflexivity. }
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x3e))
                (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 32 : mword 12)
                Macq (trap_res b + av)%nat ch false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e [Hpch]").
      { iEval (rewrite Hea3e). iExact "Hpch". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hpch".
      iEval (rewrite Hea3e) in "Hpch".
      set (M3e := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch]> Macq).
      assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x3e) : mword 64) 2
                      = mword_of_int (KernelSyms.wakeup + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc40) in "Hpc".
      assert (HM3e_a5 : M3e !!! Regidx (mword_of_int 15 : mword 5) = ch)
        by (rewrite /M3e upd_eq; reflexivity).
      assert (HM3e_9 : M3e !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
        by (rewrite /M3e upd_ne; [exact HMacq9 | vm_compute; discriminate]).
      assert (HM3e_2 : M3e !!! Regidx (mword_of_int 2 : mword 5) = spF)
        by (rewrite /M3e upd_ne; [exact HMacq2 | vm_compute; discriminate]).
      assert (HM3e_18 : M3e !!! Regidx (mword_of_int 18 : mword 5) = chan)
        by (rewrite /M3e upd_ne; [exact HMacq18 | vm_compute; discriminate]).
      assert (HM3e_19 : M3e !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC)
        by (rewrite /M3e upd_ne; [exact HMacq19 | vm_compute; discriminate]).
      assert (HM3e_20 : M3e !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 2 : mword 64))
        by (rewrite /M3e upd_ne; [exact HMacq20 | vm_compute; discriminate]).
      assert (HM3e_21 : M3e !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
        by (rewrite /M3e upd_ne; [exact HMacq21 | vm_compute; discriminate]).
      assert (HM3e_22 : M3e !!! Regidx (mword_of_int 22 : mword 5) = vs6)
        by (rewrite /M3e upd_ne; [exact HMacq22 | vm_compute; discriminate]).
      assert (HM3e_23 : M3e !!! Regidx (mword_of_int 23 : mword 5) = vs7)
        by (rewrite /M3e upd_ne; [exact HMacq23 | vm_compute; discriminate]).
      assert (HM3e_24 : M3e !!! Regidx (mword_of_int 24 : mword 5) = vs8)
        by (rewrite /M3e upd_ne; [exact HMacq24 | vm_compute; discriminate]).
      assert (HM3e_25 : M3e !!! Regidx (mword_of_int 25 : mword 5) = vs9)
        by (rewrite /M3e upd_ne; [exact HMacq25 | vm_compute; discriminate]).
      assert (HM3e_26 : M3e !!! Regidx (mword_of_int 26 : mword 5) = vs10)
        by (rewrite /M3e upd_ne; [exact HMacq26 | vm_compute; discriminate]).
      assert (HM3e_27 : M3e !!! Regidx (mword_of_int 27 : mword 5) = vs11)
        by (rewrite /M3e upd_ne; [exact HMacq27 | vm_compute; discriminate]).
      assert (HdomM3e : forall r : regidx, r ∈ dom (rf_to_gmap M3e)).
      { intro r. rewrite /M3e rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Hdomacq. }
      (* ---- 0x40 bne a5,s2 : if p->chan != chan -> release ---- *)
      iPoseProof (wki_40 with "Htext") as "Hi40".
      assert (Hrg40_15 : rget (CID := CIDf) M3e (mword_of_int 15 : mword 5)
                         = M3e !!! Regidx (mword_of_int 15 : mword 5)) by (rgne; reflexivity).
      assert (Hrg40_18 : rget (CID := CIDf) M3e (mword_of_int 18 : mword 5)
                         = M3e !!! Regidx (mword_of_int 18 : mword 5)) by (rgne; reflexivity).
      destruct (neq_vec (M3e !!! Regidx (mword_of_int 15 : mword 5))
                        (M3e !!! Regidx (mword_of_int 18 : mword 5))) eqn:Hcmp40.
      + (* TAKEN: chan mismatch -> reassemble proc_lock_res untouched, release *)
        assert (Hcmp40r : neq_vec (rget (CID := CIDf) M3e (mword_of_int 15 : mword 5))
                                  (rget (CID := CIDf) M3e (mword_of_int 18 : mword 5)) = true)
          by (rewrite Hrg40_15 Hrg40_18; exact Hcmp40).
        iApply (wp_bne_taken_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x40))
                  (mword_of_int 8170 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
                  M3e (trap_res b + av)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp40r ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi40").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (H40tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x40) : mword 64)
                          (sign_extend' 64 (mword_of_int 8170 : mword 13))
                        = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite H40tgt) in "Hpc".
        iDestruct (proc_lock_res_intro γs γk (proc_addr k) st ch with "Hpst Hpg Hpch Hpub Hctx") as "HR".
        iApply ("Hrel" $! M3e with "[%] Hcg Hpc Htok HR").
        repeat split; [exact HM3e_9 | exact HM3e_2 | exact HM3e_18
                      | exact HM3e_19 | exact HM3e_20 | exact HM3e_21
                      | exact HM3e_22 | exact HM3e_23 | exact HM3e_24
                      | exact HM3e_25 | exact HM3e_26 | exact HM3e_27 | exact HdomM3e].
      + (* FALL: chan matches -> clear it, then look at the state *)
        assert (Hcmp40r : neq_vec (rget (CID := CIDf) M3e (mword_of_int 15 : mword 5))
                                  (rget (CID := CIDf) M3e (mword_of_int 18 : mword 5)) = false)
          by (rewrite Hrg40_15 Hrg40_18; exact Hcmp40).
        iApply (wp_bne_fall_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x40))
                  (mword_of_int 8170 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
                  M3e (trap_res b + av)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp40r with "Hcg Hpc Hi40").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x40) : mword 64) 4
                        = mword_of_int (KernelSyms.wakeup + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc44) in "Hpc".
        (* ---- 0x44 sd zero,32(s1) : p->chan := 0.  THE WAKEUP FLAG CLEAR.
           [p_chan] is unconditional in [proc_lock_res] -- no guard is opened
           and the state is irrelevant, which is what makes this arm free. ---- *)
        iPoseProof (wki_44 with "Htext") as "Hi44".
        assert (Hea44 : add_vec (rget (CID := CIDf) M3e (mword_of_int 9 : mword 5))
                          (sign_extend' 64 (mword_of_int 32 : mword 12)) = p_chan (proc_addr k)).
        { rewrite (rget_ne M3e (mword_of_int 9 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
          rewrite HM3e_9. rewrite /p_chan /chan_off.
          replace (sign_extend' 64 (mword_of_int 32 : mword 12)) with (mword_of_int 32 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          reflexivity. }
        iApply (wp_sd_zero_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x44))
                  (mword_of_int 9 : mword 5) (mword_of_int 32 : mword 12)
                  M3e (trap_res b + av)%nat ch false
                  with "Hcg Hpc Hi44 [Hpch]").
        { iEval (rewrite Hea44). iExact "Hpch". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hpch".
        iEval (rewrite Hea44) in "Hpch".
        assert (Hpc48 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x44) : mword 64) 4
                        = mword_of_int (KernelSyms.wakeup + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc48) in "Hpc".
        (* ---- 0x48 c.lw a5,24(s1) : a5 := sext(p->state) ---- *)
        iPoseProof (wki_48 with "Htext") as "Hi48".
        assert (Hea48 : add_vec (rget (CID := CIDf) M3e (mword_of_int 9 : mword 5))
                          (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr k)).
        { rewrite (rget_ne M3e (mword_of_int 9 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
          rewrite HM3e_9. rewrite /p_state /state_off.
          replace (sign_extend' 64 (mword_of_int 24 : mword 12)) with (mword_of_int 24 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          reflexivity. }
        iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x48))
                  (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 24 : mword 12)
                  M3e (trap_res b + av)%nat st false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi48 [Hpst]").
        { iEval (rewrite Hea48). iExact "Hpst". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hpst".
        iEval (rewrite Hea48) in "Hpst".
        set (M48 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 st)]> M3e).
        assert (Hpc4a : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64) 2
                        = mword_of_int (KernelSyms.wakeup + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc4a) in "Hpc".
        assert (HM48a5 : M48 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 st)
          by (rewrite /M48 upd_eq; reflexivity).
        assert (HM48_9 : M48 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
          by (rewrite /M48 upd_ne; [exact HM3e_9 | vm_compute; discriminate]).
        assert (HM48_2 : M48 !!! Regidx (mword_of_int 2 : mword 5) = spF)
          by (rewrite /M48 upd_ne; [exact HM3e_2 | vm_compute; discriminate]).
        assert (HM48_18 : M48 !!! Regidx (mword_of_int 18 : mword 5) = chan)
          by (rewrite /M48 upd_ne; [exact HM3e_18 | vm_compute; discriminate]).
        assert (HM48_19 : M48 !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC)
          by (rewrite /M48 upd_ne; [exact HM3e_19 | vm_compute; discriminate]).
        assert (HM48_20 : M48 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 2 : mword 64))
          by (rewrite /M48 upd_ne; [exact HM3e_20 | vm_compute; discriminate]).
        assert (HM48_21 : M48 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
          by (rewrite /M48 upd_ne; [exact HM3e_21 | vm_compute; discriminate]).
        assert (HM48_22 : M48 !!! Regidx (mword_of_int 22 : mword 5) = vs6)
          by (rewrite /M48 upd_ne; [exact HM3e_22 | vm_compute; discriminate]).
        assert (HM48_23 : M48 !!! Regidx (mword_of_int 23 : mword 5) = vs7)
          by (rewrite /M48 upd_ne; [exact HM3e_23 | vm_compute; discriminate]).
        assert (HM48_24 : M48 !!! Regidx (mword_of_int 24 : mword 5) = vs8)
          by (rewrite /M48 upd_ne; [exact HM3e_24 | vm_compute; discriminate]).
        assert (HM48_25 : M48 !!! Regidx (mword_of_int 25 : mword 5) = vs9)
          by (rewrite /M48 upd_ne; [exact HM3e_25 | vm_compute; discriminate]).
        assert (HM48_26 : M48 !!! Regidx (mword_of_int 26 : mword 5) = vs10)
          by (rewrite /M48 upd_ne; [exact HM3e_26 | vm_compute; discriminate]).
        assert (HM48_27 : M48 !!! Regidx (mword_of_int 27 : mword 5) = vs11)
          by (rewrite /M48 upd_ne; [exact HM3e_27 | vm_compute; discriminate]).
        assert (HdomM48 : forall r : regidx, r ∈ dom (rf_to_gmap M48)).
        { intro r. rewrite /M48 rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply HdomM3e. }
        (* ---- 0x4a bne a5,s4 : if state != SLEEPING -> release ---- *)
        iPoseProof (wki_4a with "Htext") as "Hi4a".
        assert (Hrg4a_15 : rget (CID := CIDf) M48 (mword_of_int 15 : mword 5)
                           = M48 !!! Regidx (mword_of_int 15 : mword 5)) by (rgne; reflexivity).
        assert (Hrg4a_20 : rget (CID := CIDf) M48 (mword_of_int 20 : mword 5)
                           = M48 !!! Regidx (mword_of_int 20 : mword 5)) by (rgne; reflexivity).
        destruct (neq_vec (M48 !!! Regidx (mword_of_int 15 : mword 5))
                          (M48 !!! Regidx (mword_of_int 20 : mword 5))) eqn:Hcmp4a.
        * (* TAKEN: not SLEEPING -- the flag is cleared, the state stands *)
          assert (Hcmp4ar : neq_vec (rget (CID := CIDf) M48 (mword_of_int 15 : mword 5))
                                    (rget (CID := CIDf) M48 (mword_of_int 20 : mword 5)) = true)
            by (rewrite Hrg4a_15 Hrg4a_20; exact Hcmp4a).
          iApply (wp_bne_taken_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x4a))
                    (mword_of_int 8160 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                    M48 (trap_res b + av)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp4ar ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi4a").
          iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (H4atgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x4a) : mword 64)
                            (sign_extend' 64 (mword_of_int 8160 : mword 13))
                          = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite H4atgt) in "Hpc".
          iDestruct (proc_lock_res_intro γs γk (proc_addr k) st zero_reg with "Hpst Hpg Hpch Hpub Hctx") as "HR".
          iApply ("Hrel" $! M48 with "[%] Hcg Hpc Htok HR").
          repeat split; [exact HM48_9 | exact HM48_2 | exact HM48_18
                        | exact HM48_19 | exact HM48_20 | exact HM48_21
                        | exact HM48_22 | exact HM48_23 | exact HM48_24
                        | exact HM48_25 | exact HM48_26 | exact HM48_27 | exact HdomM48].
        * (* FALL: state == SLEEPING -> wake (state := RUNNABLE) *)
          assert (Hcmp4ar : neq_vec (rget (CID := CIDf) M48 (mword_of_int 15 : mword 5))
                                    (rget (CID := CIDf) M48 (mword_of_int 20 : mword 5)) = false)
            by (rewrite Hrg4a_15 Hrg4a_20; exact Hcmp4a).
          iApply (wp_bne_fall_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x4a))
                    (mword_of_int 8160 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                    M48 (trap_res b + av)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp4ar with "Hcg Hpc Hi4a").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Heq2 : sign_extend' 64 st = (mword_of_int 2 : mword 64)).
          { rewrite HM48a5 HM48_20 in Hcmp4a. unfold neq_vec in Hcmp4a.
            rewrite negb_false_iff in Hcmp4a. apply eq_vec_true_iff in Hcmp4a. exact Hcmp4a. }
          pose proof (wk_sext_sleeping st Heq2) as Hst_sl.
          assert (Hpc4e : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4a) : mword 64) 4
                          = mword_of_int (KernelSyms.wakeup + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc4e) in "Hpc".
          (* ---- 0x4e sw s5,24(s1) : p->state := RUNNABLE ---- *)
          iPoseProof (wki_4e with "Htext") as "Hi4e".
          assert (Hea4e : add_vec (rget (CID := CIDf) M48 (mword_of_int 9 : mword 5))
                            (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr k)).
          { rewrite (rget_ne M48 (mword_of_int 9 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
            rewrite HM48_9. rewrite /p_state /state_off.
            replace (sign_extend' 64 (mword_of_int 24 : mword 12)) with (mword_of_int 24 : mword 64)
              by (apply bv_eq; vm_compute; reflexivity).
            reflexivity. }
          iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x4e))
                    (mword_of_int 21 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 24 : mword 12)
                    M48 (trap_res b + av)%nat st false with "Hcg Hpc Hi4e [Hpst]").
          { iEval (rewrite Hea4e). iExact "Hpst". }
          iApply wp_next_off_intro.
          iIntros "Hcg Hpc Hpst".
          assert (Hstored : trunc32 (rget (CID := CIDf) M48 (mword_of_int 21 : mword 5)) = RUNNABLE).
          { rewrite (rget_ne M48 (mword_of_int 21 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
            rewrite HM48_21. rewrite /RUNNABLE. apply bv_eq; vm_compute; reflexivity. }
          iEval (rewrite Hstored) in "Hpst". iEval (rewrite Hea4e) in "Hpst".
          assert (Hpc52 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64) 4
                          = mword_of_int (KernelSyms.wakeup + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc52) in "Hpc".
          (* reassemble proc_lock_res via the wakeup transition, at the CLEARED
             chan.  SLEEPING -> RUNNABLE stays in one guard class: the slots
             cross untouched, so no guard is opened (proc_slots_recast).  Both
             mirror halves are lock-resident at SLEEPING, which is why this arm
             needs nothing from the running thread even when the slot is its
             own. *)
          iApply fupd_wp.
          iMod (proc_lock_res_wakeup γs γk (proc_addr k) st zero_reg Hst_sl
                  with "Hpst Hpg Hpch Hpub Hctx") as "HR".
          iModIntro.
          (* ---- 0x52 c.j release ---- *)
          iPoseProof (wki_52 with "Htext") as "Hi52".
          assert (H52tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x52) : mword 64)
                            (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0"))))
                          = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_cj_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x52))
                    (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))
                    M48 (trap_res b + av)%nat false ltac:(rewrite H52tgt; vm_compute; reflexivity)
                    with "Hcg Hpc Hi52").
          iApply wp_next_off_intro.
          iNext. iIntros "Hcg Hpc".
          iEval (rewrite H52tgt) in "Hpc".
          iApply ("Hrel" $! M48 with "[%] Hcg Hpc Htok HR").
          repeat split; [exact HM48_9 | exact HM48_2 | exact HM48_18
                        | exact HM48_19 | exact HM48_20 | exact HM48_21
                        | exact HM48_22 | exact HM48_23 | exact HM48_24
                        | exact HM48_25 | exact HM48_26 | exact HM48_27 | exact HdomM48].
    }
    iIntros (k M) "%Hk %Hregs Hcg Hown Htext Hpc Hframe".
    iSpecialize ("Hloop" $! (NPROC - k)%nat).
    iSpecialize ("Hloop" $! CID0 with "[%]"); [by intros|].
    iApply ("Hloop" $! k M with "[%] [%] [%] Hqexit Hcg Hown Htext Hpc Hframe");
      [lia | exact Hk | exact Hregs].
  Qed.

  (* ===================================================================== *)
  (* Whole-function WP for wakeup(chan) over sconf: prologue -> loop        *)
  (* (k=0, exiting to the epilogue at 0x54) -> return.  The caller supplies  *)
  (* deep-K custody (K>=18, so deep-10 remains for the loop after the        *)
  (* prologue's 8-slot frame carve) and procs_inv.  proc_lock_res            *)
  (* (SchedCtx.v) is threaded opaquely, ▷-slot untouched.                    *)
  (* ===================================================================== *)
  Lemma wp_wakeup_sconf `{GEN : GenId} `{CID0 : CpuId}
      
      (m : regfile) (γs : list gname) (pme : mword 64)
      (lvl K : nat) (eb : bool) (b : bool) (lks : gset string)
    : wp_wakeup_sconf_body m γs pme lvl K eb b lks.
  Proof.
    cbv beta delta [wp_wakeup_sconf_body].
    intros sp0 spF rettgt HK Hdom Hlen Hlvl Hfresh.
    iIntros "Hcg Hown #Htext Hpc #Hpinv Hcont".
    (* ---- prologue: save frame (carve 8 from the cap's avail), set up loop regs ---- *)
    iApply (WakeupParts.wp_wakeup_prologue_sconf (CID := CID0) m K b pme ltac:(lia) Hdom
              with "Hcg Htext Hpc").
    iIntros (CIDpro Hspro M vpad) "%Hpro Hcg Hpc Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0".
    destruct Hpro as (HM9 & HM19 & HM20 & HM21 & HM18 & HMcsp & HM1 & HM22 & HM23 & HM24 & HM25 & HM26 & HM27 & HMdom).
    iDestruct (cpu_own_transport CID0 CIDpro lvl eb pme b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* ---- the loop, with the epilogue as its exit continuation ---- *)
    iPoseProof (wp_wakeup_loop_sconf (CID0 := CIDpro)  γs spF pme
                  (m !!! Regidx (mword_of_int 10 : mword 5))
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                  (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                  (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                  (m !!! Regidx (mword_of_int 21 : mword 5))
                  (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5))
                  (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 25 : mword 5))
                  (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) lvl
                  (K - 8)%nat eb b lks
                  Hlen Hlvl ltac:(lia) Hfresh
                  with "Hpinv") as "Hloop".
    iSpecialize ("Hloop" with "[Hf0 Hcont]").
    { (* exit continuation = epilogue at wakeup+0x54 *)
      iIntros (CIDex Hsex Mexit) "(%Hecsp & %He22 & %He23 & %He24 & %He25 & %He26 & %He27 & %Hedom)
                       Hcg Hown Htextx Hpc Hframe".
      iDestruct "Hframe" as "(Hf7 & Hf6 & Hf5 & Hf4 & Hf3 & Hf2 & Hf1)".
      iApply (WakeupParts.wp_wakeup_epilogue_sconf (CID := CIDex) Mexit K
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                (m !!! Regidx (mword_of_int 21 : mword 5)) vpad b pme
                ltac:(lia) Hedom
                with "Hcg Htextx Hpc [Hf7] [Hf6] [Hf5] [Hf4] [Hf3] [Hf2] [Hf1] [Hf0]").
      { iEval (rewrite Hecsp). iExact "Hf7". }
      { iEval (rewrite Hecsp). iExact "Hf6". }
      { iEval (rewrite Hecsp). iExact "Hf5". }
      { iEval (rewrite Hecsp). iExact "Hf4". }
      { iEval (rewrite Hecsp). iExact "Hf3". }
      { iEval (rewrite Hecsp). iExact "Hf2". }
      { iEval (rewrite Hecsp). iExact "Hf1". }
      { iEval (rewrite Hecsp). iExact "Hf0". }
      iIntros (CIDend Hsend Mf) "%Hepi Hcg Hpc".
      destruct Hepi as (Hf1v & Hf0v & Hf9v & Hf18v & Hf19v & Hf20v & Hf21v & Hfcsp & Hf22v & Hf23v & Hf24v & Hf25v & Hf26v & Hf27v & Hfdom).
      (* the epilogue's restored sp equals the caller's sp0 (the -64/+60+4 cancel) *)
      assert (Hspcancel : add_vec (Mexit !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0)
        by (rewrite Hecsp; subst spF sp0; apply frame_cancel_64).
      iDestruct (cpu_own_transport CIDex CIDend lvl eb pme b ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iSpecialize ("Hcont" $! CIDend with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! Mf with "[%] Hcg Hown Htext [Hpc]").
      - (* callee_saved m Mf /\ dom Mf *)
        split; [| exact Hfdom].
        unfold callee_saved.
        rewrite Hfcsp Hf0v Hf9v Hf18v Hf19v Hf20v Hf21v Hf22v Hf23v Hf24v Hf25v Hf26v Hf27v.
        rewrite He22 He23 He24 He25 He26 He27.
        repeat split; try reflexivity. exact Hspcancel.
      - (* pc_is rettgt : the epilogue's rettgt matches the caller's *)
        iExact "Hpc". }
    (* discharge the loop at k=0 with the prologue's loop-head map M *)
    iApply ("Hloop" $! 0%nat M with "[%] [%] Hcg Hown Htext Hpc [Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1]").
    - unfold NPROC. lia.
    - unfold wkl_regs.
      split; [exact HM9|]. split; [exact HMcsp|].
      split; [exact HM18|]. split; [exact HM19|]. split; [exact HM20|].
      split; [exact HM21|]. split; [exact HM22|]. split; [exact HM23|].
      split; [exact HM24|]. split; [exact HM25|]. split; [exact HM26|].
      split; [exact HM27|]. exact HMdom.
    - rewrite /wk_frame. iFrame "Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1".
  Qed.

End ProofWakeup.

End WakeupProof.
