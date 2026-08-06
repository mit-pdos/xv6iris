(* ProofWakeup.v -- the wakeup proc[]-table loop over the SIE-agnostic
   sconf world (kalloc cone, stage 8).  The sconf mirror of [wp_wakeup_loop]
   (CodeWakeup.v): a bounded fuel induction over the 64-entry proc[] table that,
   per proc, acquires the proc lock, wakes it if SLEEPING on the given chan,
   and releases -- threading the counting token [intr_count] NET-ZERO across
   each acquire/release pair (acquire lvl->S lvl, release S lvl->lvl).

   EXPLICIT-CPUID NOTE.  wakeup is [b]-GENERIC and it CALLS things (myproc,
   acquire, release) at that index, so a trap taken anywhere outside the
   lock-held stretch may migrate the thread.  Consequently the LOOP INVARIANT
   itself is hart-generic: it is a [wp_next b (fun CID => ...)], the shape
   whose obligation composes with [wp_next_chain].  Three propositions carry
   the hart that way -- the loop head (0x38), the shared p++/test tail (0x30)
   and the exit continuation (0x58) -- and all three are ANCHORED AT THE
   LEMMA'S OWN [CID0], so forwarding one across an iteration is the identity
   and only a USE needs the chained equality.

   The stretch between acquire's return and release's call runs at the literal
   index [false] (a held lock pins noff >= 1), so the hart cannot move there:
   those leaves collapse with [wp_next_off] and read exactly as they did
   before the refactor.  That is also why the release tail [Hrel] needs no
   hart binder.

   tp: [callee_saved] no longer preserves x4 and [tp_pin] makes any claim
   about the map's tp slot vacuous, so CodeWakeup's [wk_loop_regs] (which still
   carries one) is restated here as [wkl_regs] without it -- and with it go
   the loop's [rtp]/[a0f] parameters, whose only consumers were the tp
   premises of myproc/acquire/release. *)
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
Require Import SmodeCore.
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
Require Import ProcGeom SpecMyproc.
Require Import SpecWakeup.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import CodeWakeupAux.
Local Open Scope Z_scope.

(* CodeWakeup's [wk_loop_regs] minus the tp conjunct -- see the header. *)
Definition wkl_regs (M : regfile) (spF chan : mword 64)
    (vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (k : nat) : Prop :=
  M !!! Regidx (mword_of_int 9)  = proc_addr k /\
  M !!! Regidx (mword_of_int 2)  = spF /\
  M !!! Regidx (mword_of_int 18) = proc_addr NPROC /\
  M !!! Regidx (mword_of_int 19) = (mword_of_int 2 : mword 64) /\
  M !!! Regidx (mword_of_int 20) = chan /\
  M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64) /\
  M !!! Regidx (mword_of_int 22) = vs6 /\
  M !!! Regidx (mword_of_int 23) = vs7 /\
  M !!! Regidx (mword_of_int 24) = vs8 /\
  M !!! Regidx (mword_of_int 25) = vs9 /\
  M !!! Regidx (mword_of_int 26) = vs10 /\
  M !!! Regidx (mword_of_int 27) = vs11 /\
  (forall r : regidx, r ∈ dom (rf_to_gmap M)).


Module WakeupProof (Myproc : MYPROC) (Acquire : ACQUIRE) (Release : RELEASE) (WakeupParts : WAKEUPPARTS) : WAKEUP.

Section ProofWakeup.
  Context `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !sieG Σ}.
  (* NO [Context `{GEN : GenId} `{CID : CpuId}]: the loop lemma is applied at the hart the
     prologue's own [wp_next] hands back, which a section variable could not
     express.  Every lemma below takes its own implicit [CID0]. *)

  (* wakeup only RELAYS parked contexts (SLEEPING->RUNNABLE, untouched), never
     resumes them, so [proc_lock_res] (SchedCtx.v, whose context slot is the
     ▷-guarded [proc_ctx] over the scheduler swtch chain) is threaded OPAQUELY
     here: the ▷-slot is carried between elim and intro/wakeup, never stripped. *)
  Lemma wp_wakeup_loop_sconf `{GEN : GenId} `{CID0 : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (spF pme chan : mword 64)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 : mword 64)
      (vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (lvl : nat) (av : nat)
      (eb : bool) (C : iProp Σ) (b : bool) :
    length γs = NPROC ->
    (* the acquire/release + myproc push_off keep the transient +1 in range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (10 <= av)%nat ->
    procs_inv Φ γs -∗
    (* acquire's "already holding" arm sits above panic() *)
    panic_wp_any -∗
    (* the loop's exit continuation: control at the epilogue entry [wakeup+0x58],
       at whatever hart the scan ended on. *)
    wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
      ∀ Mexit : regfile,
        ⌜ Mexit !!! Regidx csp_rs1 = spF
          /\ Mexit !!! Regidx (mword_of_int 22) = vs6
          /\ Mexit !!! Regidx (mword_of_int 23) = vs7
          /\ Mexit !!! Regidx (mword_of_int 24) = vs8
          /\ Mexit !!! Regidx (mword_of_int 25) = vs9
          /\ Mexit !!! Regidx (mword_of_int 26) = vs10
          /\ Mexit !!! Regidx (mword_of_int 27) = vs11
          /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mexit)) ⌝ -∗
        sie_cap_gpr Mexit av b pme -∗
        cpu_own lvl eb pme C b -∗
        kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗
        wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    ∀ (k : nat) (M : regfile),
      ⌜(k < NPROC)%nat⌝ -∗ ⌜wkl_regs M spF chan vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
      sie_cap_gpr M av b pme -∗
      cpu_own lvl eb pme C b -∗
      kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗
      wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hlen Hlvl Hav.
    iIntros "#Hpinv #Hpanic Hqexit".
    (* BOUNDED loop: ordinary Coq induction on a [fuel] bounding the remaining
       iterations [NPROC - k] -- no Löb needed.  The body is a [wp_next b]
       so the induction hypothesis is re-enterable at a migrated hart. *)
    iAssert (∀ (fuel : nat),
               wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
                 ∀ (k : nat) (M : regfile),
                   ⌜(NPROC - k <= fuel)%nat⌝ -∗ ⌜(k < NPROC)%nat⌝ -∗
                   ⌜wkl_regs M spF chan vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
                   wp_next (CID0 := CID0) b pme (fun (CIDq : CpuId) =>
                     ∀ Mexit : regfile,
                       ⌜ Mexit !!! Regidx csp_rs1 = spF
                         /\ Mexit !!! Regidx (mword_of_int 22) = vs6
                         /\ Mexit !!! Regidx (mword_of_int 23) = vs7
                         /\ Mexit !!! Regidx (mword_of_int 24) = vs8
                         /\ Mexit !!! Regidx (mword_of_int 25) = vs9
                         /\ Mexit !!! Regidx (mword_of_int 26) = vs10
                         /\ Mexit !!! Regidx (mword_of_int 27) = vs11
                         /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mexit)) ⌝ -∗
                       sie_cap_gpr Mexit av b pme -∗
                       cpu_own lvl eb pme C b -∗
                       kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗
                       wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
                       WP (Loop : expr riscv_lang) {{ Φ }}) -∗
                   sie_cap_gpr M av b pme -∗
                   cpu_own lvl eb pme C b -∗
                   kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗
                   wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
                   WP (Loop : expr riscv_lang) {{ Φ }}))%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown Htext Hpc Hframe".
        exfalso. lia. }
      iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown #Htext Hpc Hframe".
      destruct Hregs as (Hs1 & Hsp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11 & Hdom).
      iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbmatch. symmetry in Hbmatch.
      (* ---- shared tail [pc = wakeup+0x30]: p++ (0x30 addi s1,s1,360), then the
         termination test (0x34 beq s1,s2): exit to the epilogue at wakeup+0x58,
         else recurse into iteration k+1.  Captured once, reached from both the
         skip-self path (0x3c taken) and the release-return path (0x2c) -- and
         from DIFFERENT harts, hence the [wp_next] wrapper. ---- *)
      iAssert (wp_next (CID0 := CID0) b pme (fun (CIDt : CpuId) =>
                 ∀ Mt : regfile,
                   ⌜ wkl_regs Mt spF chan vs6 vs7 vs8 vs9 vs10 vs11 k ⌝ -∗
                   sie_cap_gpr Mt av b pme -∗
                   cpu_own lvl eb pme C b -∗
                   pc_is (mword_of_int (KernelSyms.wakeup + 0x30)) -∗
                   wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
                   WP (Loop : expr riscv_lang) {{ Φ }}))%I
        with "[Hqx]" as "Htail".
      { iIntros (CIDt Hst Mt) "%Hmt Hcg Hown Hpc Hframe".
        destruct Hmt as (Ht1 & Htsp & Ht18 & Ht19 & Ht20 & Ht21 & Ht22 & Ht23 & Ht24 & Ht25 & Ht26 & Ht27 & Htdom).
        iPoseProof (wki_30 with "Htext") as "Hi30".
        iPoseProof (wki_34 with "Htext") as "Hi34".
        (* 0x30 addi s1,s1,360 : s1 := &proc[k+1] *)
        assert (Hrgt9 : rget (CID := CIDt) Mt (mword_of_int 9 : mword 5)
                        = Mt !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        iApply (wp_addi4_s_sconf (CID := CIDt) Φ (mword_of_int (KernelSyms.wakeup + 0x30))
                  (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 360 : mword 12)
                  Mt av b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi30 [-]").
        iIntros (CIDt1 Hst1) "Hcg Hpc".
        iEval (rewrite Hrgt9) in "Hcg".
        set (Mt30 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
             (add_vec (Mt !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> Mt).
        assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x34))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp34) in "Hpc".
        assert (HMt30_9 : Mt30 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr (S k)).
        { rewrite /Mt30 upd_eq. rewrite Ht1. apply (proc_addr_succ k). }
        assert (HMt30_18 : Mt30 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC).
        { rewrite /Mt30 upd_ne; [| vm_compute; discriminate]. exact Ht18. }
        (* 0x34 beq s1,s2 : exit iff &proc[k+1] = &proc[NPROC]. *)
        assert (Hrg30_9 : rget (CID := CIDt1) Mt30 (mword_of_int 9 : mword 5)
                          = Mt30 !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        assert (Hrg30_18 : rget (CID := CIDt1) Mt30 (mword_of_int 18 : mword 5)
                           = Mt30 !!! Regidx (mword_of_int 18 : mword 5)) by (rgne; reflexivity).
        destruct (eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                         (Mt30 !!! Regidx (mword_of_int 18 : mword 5))) eqn:Hcmp.
        + (* TAKEN: p reached &proc[NPROC]; exit to epilogue at wakeup+0x58 *)
          assert (Hcmpr : eq_vec (rget (CID := CIDt1) Mt30 (mword_of_int 9 : mword 5))
                                 (rget (CID := CIDt1) Mt30 (mword_of_int 18 : mword 5)) = true)
            by (rewrite Hrg30_9 Hrg30_18; exact Hcmp).
          iApply (wp_beq_taken_s_sconf (CID := CIDt1) Φ (mword_of_int (KernelSyms.wakeup + 0x34))
                    (mword_of_int 36 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                    Mt30 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi34 [-]").
          iNext. iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (Htgt58 : add_vec (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64)
                             (sign_extend' 64 (mword_of_int 36 : mword 13)) = mword_of_int (KernelSyms.wakeup + 0x58))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt58) in "Hpc".
          iDestruct (cpu_own_transport CIDt CIDt2 lvl eb pme C b ltac:(wp_next_chain)
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
                                 (rget (CID := CIDt1) Mt30 (mword_of_int 18 : mword 5)) = false)
            by (rewrite Hrg30_9 Hrg30_18; exact Hcmp).
          iApply (wp_beq_fall_s_sconf (CID := CIDt1) Φ (mword_of_int (KernelSyms.wakeup + 0x34))
                    (mword_of_int 36 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                    Mt30 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr with "Hcg Hpc Hi34 [-]").
          iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (HkS : (S k < NPROC)%nat).
          { destruct (Nat.lt_ge_cases (S k) NPROC) as [Hlt | Hge]; [exact Hlt|].
            assert (HeqN : S k = NPROC) by lia.
            exfalso.
            assert (Hbad : eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                             (Mt30 !!! Regidx (mword_of_int 18 : mword 5)) = true).
            { rewrite HMt30_9 HMt30_18 HeqN. apply wk_eq_vec_refl. }
            rewrite Hcmp in Hbad. discriminate. }
          assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x38))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp38) in "Hpc".
          iDestruct (cpu_own_transport CIDt CIDt2 lvl eb pme C b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("IHf" $! CIDt2 with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S k) Mt30 with "[%] [%] [%] Hqx Hcg Hown Htext Hpc Hframe").
          * lia.
          * exact HkS.
          * unfold wkl_regs.
            split; [exact HMt30_9|].
            split; [rewrite /Mt30 upd_ne; [exact Htsp | vm_compute; discriminate]|].
            split; [exact HMt30_18|].
            split; [rewrite /Mt30 upd_ne; [exact Ht19 | vm_compute; discriminate]|].
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
      iPoseProof (wki_38 with "Htext") as "Hi38".
      (* ---- 0x38: jal ra, myproc (base JAL, 2-aligned target) ---- *)
      iApply (wp_jal_s_sconf (CID := CIDk) Φ (mword_of_int (KernelSyms.wakeup + 0x38))
                (mword_of_int 1 : mword 5) (mword_of_int 2095482 : mword 21) M av b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi38 [-]").
      iIntros (CIDa Hsa) "Hcg Hpc".
      set (Mj := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) 4)]> M).
      assert (Hjtgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64)
                        (sign_extend' 64 (mword_of_int 2095482 : mword 21)) = mword_of_int KernelSyms.myproc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjtgt) in "Hpc".
      assert (HMjra : Mj !!! Regidx (mword_of_int 1 : mword 5)
                      = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) 4)
        by (rewrite /Mj; apply upd_eq).
      assert (HMjcsp : Mj !!! Regidx csp_rs1 = spF).
      { rewrite /Mj upd_ne; [| vm_compute; discriminate]. exact Hsp. }
      (* ---- myproc(): a0 = pme EXACTLY (from cpu_own's proc field);
         callee-saved preserved.  cpu_own [lvl] round-trips unchanged. ---- *)
      iDestruct (cpu_own_transport CIDk CIDa lvl eb pme C b ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iApply (Myproc.wp_myproc_sconf (CID := CIDa) Φ Mj av lvl eb pme C b
                ltac:(lia)
                ltac:(lia)
                with "Hcg Hown Htext Hpc [-]").
      iIntros (CIDb Hsb msmp mret) "%Hmsmp Hcg Hown Hpc %Hpresc".
      destruct Hpresc as [Hpres _].
      (* pc is now wakeup+0x3c (myproc's bit-0-cleared return target) *)
      assert (Hret3c : ret_pc (Mj !!! Regidx (mword_of_int 1 : mword 5))
                       = mword_of_int (KernelSyms.wakeup + 0x3c)).
      { rewrite HMjra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret3c) in "Hpc".
      (* s1 preserved by myproc: mret!!!s1 = proc_addr k *)
      assert (Hmrets1 : mret !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k).
      { rewrite (callee_saved_lookup Hpres (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
        rewrite /Mj upd_ne; [| vm_compute; discriminate]. exact Hs1. }
      (* ---- 0x3c: beq a0,s1 : skip-self test ---- *)
      iPoseProof (wki_3c with "Htext") as "Hi3c".
      assert (Hrgb10 : rget (CID := CIDb) mret (mword_of_int 10 : mword 5)
                       = mret !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
      assert (Hrgb9 : rget (CID := CIDb) mret (mword_of_int 9 : mword 5)
                      = mret !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
      destruct (eq_vec (mret !!! Regidx (mword_of_int 10 : mword 5))
                       (mret !!! Regidx (mword_of_int 9 : mword 5))) eqn:Hcmp3.
      - (* TAKEN: a0 = s1 (current proc is myproc): skip to 0x30 (p++) *)
        assert (Hcmp3r : eq_vec (rget (CID := CIDb) mret (mword_of_int 10 : mword 5))
                                (rget (CID := CIDb) mret (mword_of_int 9 : mword 5)) = true)
          by (rewrite Hrgb10 Hrgb9; exact Hcmp3).
        iApply (wp_beq_taken_s_sconf (CID := CIDb) Φ (mword_of_int (KernelSyms.wakeup + 0x3c))
                  (mword_of_int 8180 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                  mret av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp3r ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi3c [-]").
        iNext. iIntros (CIDc Hsc) "Hcg Hpc".
        assert (Htgt30 : add_vec (mword_of_int (KernelSyms.wakeup + 0x3c) : mword 64)
                           (sign_extend' 64 (mword_of_int 8180 : mword 13)) = mword_of_int (KernelSyms.wakeup + 0x30))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt30) in "Hpc".
        assert (Hdommret : forall r : regidx, r ∈ dom (rf_to_gmap mret)) by (intro r; apply rf_to_gmap_dom).
        iDestruct (cpu_own_transport CIDb CIDc lvl eb pme C b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        iSpecialize ("Htail" $! CIDc with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! mret with "[%] Hcg Hown Hpc Hframe").
        unfold wkl_regs.
          split; [exact Hmrets1|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)); exact HMjcsp|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs2 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs3 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs4 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs5 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs6 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs7 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs8 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs9 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs10 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj upd_ne; [exact Hs11 | vm_compute; discriminate]|].
          exact Hdommret.
      - (* FALL: a0 <> s1: acquire proc[k], check state/chan, maybe wake, release *)
        assert (Hcmp3r : eq_vec (rget (CID := CIDb) mret (mword_of_int 10 : mword 5))
                                (rget (CID := CIDb) mret (mword_of_int 9 : mword 5)) = false)
          by (rewrite Hrgb10 Hrgb9; exact Hcmp3).
        iApply (wp_beq_fall_s_sconf (CID := CIDb) Φ (mword_of_int (KernelSyms.wakeup + 0x3c))
                  (mword_of_int 8180 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                  mret av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp3r with "Hcg Hpc Hi3c [-]").
        iIntros (CIDc Hsc) "Hcg Hpc".
        assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x40))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp40) in "Hpc".
        (* the per-proc lock for proc[k] and its protected resource. *)
        destruct (lookup_lt_is_Some_2 γs k ltac:(rewrite Hlen; exact Hk)) as [γk Hγk].
        iDestruct (procs_inv_lookup Φ γs k γk Hγk with "Hpinv") as "#Hlockk".
        (* sp preserved through myproc. *)
        assert (Hmret2 : mret !!! Regidx (mword_of_int 2 : mword 5) = spF).
        { rewrite (callee_saved_lookup Hpres (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)). exact HMjcsp. }
        iPoseProof (wki_40 with "Htext") as "Hi40".
        (* 0x40 c.mv a0,s1 : a0 := &proc[k] *)
        assert (Hrgc9 : rget (CID := CIDc) mret (mword_of_int 9 : mword 5)
                        = mret !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        iApply (wp_cmv_s_sconf (CID := CIDc) Φ (mword_of_int (KernelSyms.wakeup + 0x40))
                  (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  mret av b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi40 [-]").
        iIntros (CIDd Hsd) "Hcg Hpc".
        iEval (rewrite Hrgc9) in "Hcg".
        set (M40 := <[Regidx (mword_of_int 10 : mword 5) :=
                      regval_into_reg (add_vec zero_reg (mret !!! Regidx (mword_of_int 9 : mword 5)))]> mret).
        assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.wakeup + 0x42))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp42) in "Hpc".
        iPoseProof (wki_42 with "Htext") as "Hi42".
        (* 0x42 jal ra,acquire *)
        iApply (wp_jal_s_sconf (CID := CIDd) Φ (mword_of_int (KernelSyms.wakeup + 0x42))
                  (mword_of_int 1 : mword 5) (mword_of_int 2092148 : mword 21) M40 av b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi42 [-]").
        iIntros (CIDe Hse) "Hcg Hpc".
        set (M42 := <[Regidx (mword_of_int 1 : mword 5) :=
                      regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) 4)]> M40).
        assert (Hjtgt_aq : add_vec (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64)
                            (sign_extend' 64 (mword_of_int 2092148 : mword 21)) = mword_of_int KernelSyms.acquire)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjtgt_aq) in "Hpc".
        assert (HM42ra : M42 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) 4)
          by (rewrite /M42; apply upd_eq).
        assert (HM42a0 : M42 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr k).
        { rewrite /M42 upd_ne; [| vm_compute; discriminate].
          rewrite /M40 upd_eq. rewrite add_vec_zero_l. exact Hmrets1. }
        assert (HM42csp : M42 !!! Regidx csp_rs1 = spF).
        { rewrite /M42 upd_ne; [| vm_compute; discriminate].
          rewrite /M40 upd_ne; [| vm_compute; discriminate]. exact Hmret2. }
        (* acquire(&proc[k]->lock): cpu_own lvl -> S lvl; returns locked + proc_lock_res + pay. *)
        iDestruct (cpu_own_transport CIDb CIDe lvl eb pme C b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        iApply (Acquire.wp_acquire_sconf (CID := CIDe) Φ γk "proc"%string (proc_lock_res Φ γs γk (proc_addr k)) M42
                  lvl eb pme C av b
                  ltac:(lia)
                  ltac:(lia)
                  with "Hcg Hown Htext Hpc [Hlockk] Hpanic [-]").
        { iEval (rewrite HM42a0). iExact "Hlockk". }
        iIntros (CIDf Hsf ms Macq) "%Hms Hcg Hpc %Hpins Htok HR Hown Hpay".
        (* acquire returned: pc = wakeup+0x46, cpu_own (S lvl) + trap_csrs_pay lvl eb.
           FROM HERE TO THE RELEASE the index is the literal [false] (a held lock
           pins noff >= 1), so no leaf can migrate and everything stays at CIDf. *)
        assert (Hpc46 : ret_pc (M42 !!! Regidx (mword_of_int 1 : mword 5))
                        = mword_of_int (KernelSyms.wakeup + 0x46)).
        { rewrite HM42ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpc46) in "Hpc".
        iDestruct (proc_lock_res_elim Φ γs γk (proc_addr k) with "HR") as (st ch) "(Hpst & Hpch & Hpub & Hctx)".
        (* register-preservation through acquire (callee_saved M42 Macq). *)
        assert (HMacq9 : Macq !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k).
        { rewrite (callee_saved_lookup Hpins (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M42 upd_ne; [| vm_compute; discriminate].
          rewrite /M40 upd_ne; [| vm_compute; discriminate]. exact Hmrets1. }
        (* =============================================================== *)
        (* shared release tail [Hrel], reached from all 3 exits (state !=   *)
        (* SLEEPING, chan mismatch, or after waking): 0x2a mv a0,s1;        *)
        (* 0x2c jal release (intr_count S lvl -> lvl); then p++ tail at 0x30.*)
        (* Stated at the FIXED hart CIDf -- the whole stretch is at [false]. *)
        (* =============================================================== *)
        iAssert (∀ (Mr : regfile),
                   ⌜ Mr !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k /\
                     Mr !!! Regidx (mword_of_int 2 : mword 5) = spF /\
                     Mr !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC /\
                     Mr !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64) /\
                     Mr !!! Regidx (mword_of_int 20 : mword 5) = chan /\
                     Mr !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64) /\
                     Mr !!! Regidx (mword_of_int 22 : mword 5) = vs6 /\
                     Mr !!! Regidx (mword_of_int 23 : mword 5) = vs7 /\
                     Mr !!! Regidx (mword_of_int 24 : mword 5) = vs8 /\
                     Mr !!! Regidx (mword_of_int 25 : mword 5) = vs9 /\
                     Mr !!! Regidx (mword_of_int 26 : mword 5) = vs10 /\
                     Mr !!! Regidx (mword_of_int 27 : mword 5) = vs11 /\
                     (forall r : regidx, r ∈ dom (rf_to_gmap Mr)) ⌝ -∗
                   sie_cap_gpr (CID := CIDf) Mr av false pme -∗
                   pc_is (CID := CIDf) (mword_of_int (KernelSyms.wakeup + 0x2a)) -∗
                   locked γk CIDf -∗ proc_lock_res Φ γs γk (proc_addr k) -∗
                   WP (LoopE gen_id CIDf : expr riscv_lang) {{ Φ }})%I
          with "[Hown Hpay Hframe Htail]"
          as "Hrel".
        { iIntros (Mr) "%Hmr Hcg Hpc Htok HR".
          destruct Hmr as (Hr9 & Hr2 & Hr18 & Hr19 & Hr20 & Hr21 & Hr22 & Hr23 & Hr24 & Hr25 & Hr26 & Hr27 & Hrdom).
          iPoseProof (wki_2a with "Htext") as "Hi2a".
          iPoseProof (wki_2c with "Htext") as "Hi2c".
          (* 0x2a c.mv a0,s1 : a0 := &proc[k] *)
          assert (Hrgr9 : rget (CID := CIDf) Mr (mword_of_int 9 : mword 5)
                          = Mr !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
          iApply (wp_cmv_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x2a))
                    (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                    Mr av false ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi2a [-]").
          iApply wp_next_off_intro.
          iIntros "Hcg Hpc".
          iEval (rewrite Hrgr9) in "Hcg".
          set (Mr2a := <[Regidx (mword_of_int 10 : mword 5) :=
                         regval_into_reg (add_vec zero_reg (Mr !!! Regidx (mword_of_int 9 : mword 5)))]> Mr).
          assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.wakeup + 0x2c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp2c) in "Hpc".
          (* 0x2c jal ra,release *)
          iApply (wp_jal_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x2c))
                    (mword_of_int 1 : mword 5) (mword_of_int 2092306 : mword 21) Mr2a av false
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi2c [-]").
          iApply wp_next_off_intro.
          iIntros "Hcg Hpc".
          set (Mr2c := <[Regidx (mword_of_int 1 : mword 5) :=
                         regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) 4)]> Mr2a).
          assert (Hjtgt_rl : add_vec (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64)
                              (sign_extend' 64 (mword_of_int 2092306 : mword 21)) = mword_of_int KernelSyms.release)
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
          iApply (Release.wp_release_sconf (CID := CIDf) Φ γk (proc_addr k) "proc"%string (proc_lock_res Φ γs γk (proc_addr k)) Mr2c
                    lvl eb pme C av
                    Hlka2
                    ltac:(lia)
                    with "Hcg Htext Hpc Hlockk Htok HR Hown Hpay [-]").
          rewrite -Hbmatch.
          iIntros (CIDg Hsg mr) "Hcg Hpc %Hpinsr Hown".
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
        (* ===== 0x46..0x56: state/chan test + conditional wake, then Hrel ===== *)
        (* Macq's callee-saved registers all equal the loop-entry values: compose
           [callee_saved] across myproc (Hpres) + the a0/ra writes + acquire
           (Hpins), then project. *)
        assert (HcsMj : callee_saved M Mj).
        { rewrite /Mj. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
        assert (HcsMret : callee_saved M mret) by (eapply callee_saved_trans; [exact HcsMj | exact Hpres]).
        assert (HcsM40 : callee_saved M M40).
        { rewrite /M40. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsMret]. }
        assert (HcsM42 : callee_saved M M42).
        { rewrite /M42. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsM40]. }
        assert (HcsMacq : callee_saved M Macq) by (eapply callee_saved_trans; [exact HcsM42 | exact Hpins]).
        assert (HMacq2 : Macq !!! Regidx (mword_of_int 2 : mword 5) = spF)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)); exact Hsp).
        assert (HMacq18 : Macq !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs2).
        assert (HMacq19 : Macq !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs3).
        assert (HMacq20 : Macq !!! Regidx (mword_of_int 20 : mword 5) = chan)
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
        (* ---- 0x46 c.lw a5,24(s1) : a5 := sext(state) ---- *)
        iPoseProof (wki_46 with "Htext") as "Hi46".
        assert (Hea46 : add_vec (rget (CID := CIDf) Macq (mword_of_int 9 : mword 5))
                          (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00"))))
                        = p_state (proc_addr k)).
        { rewrite (rget_ne Macq (mword_of_int 9 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
          rewrite HMacq9. rewrite /p_state /state_off.
          replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00"))))
             with (mword_of_int 24 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          reflexivity. }
        iApply (wp_clw_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x46))
                  (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                  (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")))
                  Macq av st false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi46 [Hpst] [-]").
        { iEval (rewrite Hea46). iExact "Hpst". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hpst".
        iEval (rewrite Hea46) in "Hpst".
        set (M48 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 st)]> Macq).
        assert (Hpc48 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x46) : mword 64) 2
                        = mword_of_int (KernelSyms.wakeup + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc48) in "Hpc".
        assert (HM48a5 : M48 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 st)
          by (rewrite /M48 upd_eq; reflexivity).
        assert (HM48_9 : M48 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
          by (rewrite /M48 upd_ne; [exact HMacq9 | vm_compute; discriminate]).
        assert (HM48_2 : M48 !!! Regidx (mword_of_int 2 : mword 5) = spF)
          by (rewrite /M48 upd_ne; [exact HMacq2 | vm_compute; discriminate]).
        assert (HM48_18 : M48 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
          by (rewrite /M48 upd_ne; [exact HMacq18 | vm_compute; discriminate]).
        assert (HM48_19 : M48 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
          by (rewrite /M48 upd_ne; [exact HMacq19 | vm_compute; discriminate]).
        assert (HM48_20 : M48 !!! Regidx (mword_of_int 20 : mword 5) = chan)
          by (rewrite /M48 upd_ne; [exact HMacq20 | vm_compute; discriminate]).
        assert (HM48_21 : M48 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
          by (rewrite /M48 upd_ne; [exact HMacq21 | vm_compute; discriminate]).
        assert (HM48_22 : M48 !!! Regidx (mword_of_int 22 : mword 5) = vs6)
          by (rewrite /M48 upd_ne; [exact HMacq22 | vm_compute; discriminate]).
        assert (HM48_23 : M48 !!! Regidx (mword_of_int 23 : mword 5) = vs7)
          by (rewrite /M48 upd_ne; [exact HMacq23 | vm_compute; discriminate]).
        assert (HM48_24 : M48 !!! Regidx (mword_of_int 24 : mword 5) = vs8)
          by (rewrite /M48 upd_ne; [exact HMacq24 | vm_compute; discriminate]).
        assert (HM48_25 : M48 !!! Regidx (mword_of_int 25 : mword 5) = vs9)
          by (rewrite /M48 upd_ne; [exact HMacq25 | vm_compute; discriminate]).
        assert (HM48_26 : M48 !!! Regidx (mword_of_int 26 : mword 5) = vs10)
          by (rewrite /M48 upd_ne; [exact HMacq26 | vm_compute; discriminate]).
        assert (HM48_27 : M48 !!! Regidx (mword_of_int 27 : mword 5) = vs11)
          by (rewrite /M48 upd_ne; [exact HMacq27 | vm_compute; discriminate]).
        assert (HdomM48 : forall r : regidx, r ∈ dom (rf_to_gmap M48)).
        { intro r. rewrite /M48 rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Hdomacq. }
        (* ---- 0x48 bne a5,s3 : if state != SLEEPING -> release ---- *)
        iPoseProof (wki_48 with "Htext") as "Hi48".
        assert (Hrg48_15 : rget (CID := CIDf) M48 (mword_of_int 15 : mword 5)
                           = M48 !!! Regidx (mword_of_int 15 : mword 5)) by (rgne; reflexivity).
        assert (Hrg48_19 : rget (CID := CIDf) M48 (mword_of_int 19 : mword 5)
                           = M48 !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
        destruct (neq_vec (M48 !!! Regidx (mword_of_int 15 : mword 5))
                          (M48 !!! Regidx (mword_of_int 19 : mword 5))) eqn:Hcmp48.
        + (* TAKEN: state != SLEEPING -> reassemble proc_lock_res, release *)
          assert (Hcmp48r : neq_vec (rget (CID := CIDf) M48 (mword_of_int 15 : mword 5))
                                    (rget (CID := CIDf) M48 (mword_of_int 19 : mword 5)) = true)
            by (rewrite Hrg48_15 Hrg48_19; exact Hcmp48).
          iApply (wp_bne_taken_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x48))
                    (mword_of_int 8162 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                    M48 av false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp48r ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi48 [-]").
          iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (H48tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64)
                            (sign_extend' 64 (mword_of_int 8162 : mword 13))
                          = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite H48tgt) in "Hpc".
          iDestruct (proc_lock_res_intro Φ γs γk (proc_addr k) st ch with "Hpst Hpch Hpub Hctx") as "HR".
          iApply ("Hrel" $! M48 with "[%] Hcg Hpc Htok HR").
          repeat split; [exact HM48_9 | exact HM48_2 | exact HM48_18
                        | exact HM48_19 | exact HM48_20 | exact HM48_21
                        | exact HM48_22 | exact HM48_23 | exact HM48_24
                        | exact HM48_25 | exact HM48_26 | exact HM48_27 | exact HdomM48].
        + (* FALL: state == SLEEPING -> load chan *)
          assert (Hcmp48r : neq_vec (rget (CID := CIDf) M48 (mword_of_int 15 : mword 5))
                                    (rget (CID := CIDf) M48 (mword_of_int 19 : mword 5)) = false)
            by (rewrite Hrg48_15 Hrg48_19; exact Hcmp48).
          iApply (wp_bne_fall_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x48))
                    (mword_of_int 8162 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                    M48 av false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp48r with "Hcg Hpc Hi48 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Heq2 : sign_extend' 64 st = (mword_of_int 2 : mword 64)).
          { rewrite HM48a5 HM48_19 in Hcmp48. unfold neq_vec in Hcmp48.
            rewrite negb_false_iff in Hcmp48. apply eq_vec_true_iff in Hcmp48. exact Hcmp48. }
          pose proof (wk_sext_sleeping st Heq2) as Hst_sl.
          assert (Hpc4c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64) 4
                          = mword_of_int (KernelSyms.wakeup + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc4c) in "Hpc".
          (* ---- 0x4c c.ld a5,32(s1) : a5 := p->chan ---- *)
          iPoseProof (wki_4c with "Htext") as "Hi4c".
          assert (Hea4c : add_vec (rget (CID := CIDf) M48 (mword_of_int 9 : mword 5))
                            (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))) = p_chan (proc_addr k)).
          { rewrite (rget_ne M48 (mword_of_int 9 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
            rewrite HM48_9. rewrite /p_chan /chan_off.
            replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))) with (mword_of_int 32 : mword 64)
              by (apply bv_eq; vm_compute; reflexivity).
            reflexivity. }
          iApply (wp_cld_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x4c))
                    (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))
                    M48 av ch false ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi4c [Hpch] [-]").
          { iEval (rewrite Hea4c). iExact "Hpch". }
          iApply wp_next_off_intro.
          iIntros "Hcg Hpc Hpch".
          iEval (rewrite Hea4c) in "Hpch".
          set (M4e := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch]> M48).
          assert (Hpc4e : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4c) : mword 64) 2
                          = mword_of_int (KernelSyms.wakeup + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc4e) in "Hpc".
          assert (HM4e_a5 : M4e !!! Regidx (mword_of_int 15 : mword 5) = ch)
            by (rewrite /M4e upd_eq; reflexivity).
          assert (HM4e_9 : M4e !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
            by (rewrite /M4e upd_ne; [exact HM48_9 | vm_compute; discriminate]).
          assert (HM4e_2 : M4e !!! Regidx (mword_of_int 2 : mword 5) = spF)
            by (rewrite /M4e upd_ne; [exact HM48_2 | vm_compute; discriminate]).
          assert (HM4e_18 : M4e !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
            by (rewrite /M4e upd_ne; [exact HM48_18 | vm_compute; discriminate]).
          assert (HM4e_19 : M4e !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
            by (rewrite /M4e upd_ne; [exact HM48_19 | vm_compute; discriminate]).
          assert (HM4e_20 : M4e !!! Regidx (mword_of_int 20 : mword 5) = chan)
            by (rewrite /M4e upd_ne; [exact HM48_20 | vm_compute; discriminate]).
          assert (HM4e_21 : M4e !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
            by (rewrite /M4e upd_ne; [exact HM48_21 | vm_compute; discriminate]).
          assert (HM4e_22 : M4e !!! Regidx (mword_of_int 22 : mword 5) = vs6)
            by (rewrite /M4e upd_ne; [exact HM48_22 | vm_compute; discriminate]).
          assert (HM4e_23 : M4e !!! Regidx (mword_of_int 23 : mword 5) = vs7)
            by (rewrite /M4e upd_ne; [exact HM48_23 | vm_compute; discriminate]).
          assert (HM4e_24 : M4e !!! Regidx (mword_of_int 24 : mword 5) = vs8)
            by (rewrite /M4e upd_ne; [exact HM48_24 | vm_compute; discriminate]).
          assert (HM4e_25 : M4e !!! Regidx (mword_of_int 25 : mword 5) = vs9)
            by (rewrite /M4e upd_ne; [exact HM48_25 | vm_compute; discriminate]).
          assert (HM4e_26 : M4e !!! Regidx (mword_of_int 26 : mword 5) = vs10)
            by (rewrite /M4e upd_ne; [exact HM48_26 | vm_compute; discriminate]).
          assert (HM4e_27 : M4e !!! Regidx (mword_of_int 27 : mword 5) = vs11)
            by (rewrite /M4e upd_ne; [exact HM48_27 | vm_compute; discriminate]).
          assert (HdomM4e : forall r : regidx, r ∈ dom (rf_to_gmap M4e)).
          { intro r. rewrite /M4e rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply HdomM48. }
          (* ---- 0x4e bne a5,s4 : if chan != arg -> release ---- *)
          iPoseProof (wki_4e with "Htext") as "Hi4e".
          assert (Hrg4e_15 : rget (CID := CIDf) M4e (mword_of_int 15 : mword 5)
                             = M4e !!! Regidx (mword_of_int 15 : mword 5)) by (rgne; reflexivity).
          assert (Hrg4e_20 : rget (CID := CIDf) M4e (mword_of_int 20 : mword 5)
                             = M4e !!! Regidx (mword_of_int 20 : mword 5)) by (rgne; reflexivity).
          destruct (neq_vec (M4e !!! Regidx (mword_of_int 15 : mword 5))
                            (M4e !!! Regidx (mword_of_int 20 : mword 5))) eqn:Hcmp4e.
          * (* TAKEN: chan mismatch -> release *)
            assert (Hcmp4er : neq_vec (rget (CID := CIDf) M4e (mword_of_int 15 : mword 5))
                                      (rget (CID := CIDf) M4e (mword_of_int 20 : mword 5)) = true)
              by (rewrite Hrg4e_15 Hrg4e_20; exact Hcmp4e).
            iApply (wp_bne_taken_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x4e))
                      (mword_of_int 8156 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                      M4e av false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                      Hcmp4er ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hi4e [-]").
            iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
            assert (H4etgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64)
                              (sign_extend' 64 (mword_of_int 8156 : mword 13))
                            = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite H4etgt) in "Hpc".
            iDestruct (proc_lock_res_intro Φ γs γk (proc_addr k) st ch with "Hpst Hpch Hpub Hctx") as "HR".
            iApply ("Hrel" $! M4e with "[%] Hcg Hpc Htok HR").
            repeat split; [exact HM4e_9 | exact HM4e_2 | exact HM4e_18
                          | exact HM4e_19 | exact HM4e_20 | exact HM4e_21
                          | exact HM4e_22 | exact HM4e_23 | exact HM4e_24
                          | exact HM4e_25 | exact HM4e_26 | exact HM4e_27 | exact HdomM4e].
          * (* FALL: chan matches -> wake (state := RUNNABLE) *)
            assert (Hcmp4er : neq_vec (rget (CID := CIDf) M4e (mword_of_int 15 : mword 5))
                                      (rget (CID := CIDf) M4e (mword_of_int 20 : mword 5)) = false)
              by (rewrite Hrg4e_15 Hrg4e_20; exact Hcmp4e).
            iApply (wp_bne_fall_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x4e))
                      (mword_of_int 8156 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                      M4e av false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                      Hcmp4er with "Hcg Hpc Hi4e [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            assert (Hpc52 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64) 4
                            = mword_of_int (KernelSyms.wakeup + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpc52) in "Hpc".
            (* ---- 0x52 sw s5,24(s1) : p->state := RUNNABLE ---- *)
            iPoseProof (wki_52 with "Htext") as "Hi52".
            assert (Hea52 : add_vec (rget (CID := CIDf) M4e (mword_of_int 9 : mword 5))
                              (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr k)).
            { rewrite (rget_ne M4e (mword_of_int 9 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
              rewrite HM4e_9. rewrite /p_state /state_off.
              replace (sign_extend' 64 (mword_of_int 24 : mword 12)) with (mword_of_int 24 : mword 64)
                by (apply bv_eq; vm_compute; reflexivity).
              reflexivity. }
            iApply (wp_sw_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x52))
                      (mword_of_int 21 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 24 : mword 12)
                      M4e av st false with "Hcg Hpc Hi52 [Hpst] [-]").
            { iEval (rewrite Hea52). iExact "Hpst". }
            iApply wp_next_off_intro.
            iIntros "Hcg Hpc Hpst".
            assert (Hstored : trunc32 (rget (CID := CIDf) M4e (mword_of_int 21 : mword 5)) = RUNNABLE).
            { rewrite (rget_ne M4e (mword_of_int 21 : mword 5) ltac:(intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence)).
              rewrite HM4e_21. rewrite /RUNNABLE. apply bv_eq; vm_compute; reflexivity. }
            iEval (rewrite Hstored) in "Hpst". iEval (rewrite Hea52) in "Hpst".
            assert (Hpc56 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x52) : mword 64) 4
                            = mword_of_int (KernelSyms.wakeup + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpc56) in "Hpc".
            (* reassemble proc_lock_res via the wakeup transition.
               SLEEPING -> RUNNABLE stays in one guard class: the slots cross
               untouched, so no guard is opened (proc_slots_recast). *)
            iDestruct (proc_lock_res_wakeup Φ γs γk (proc_addr k) st ch Hst_sl with "Hpst Hpch Hpub Hctx") as "HR".
            (* ---- 0x56 c.j release ---- *)
            iPoseProof (wki_56 with "Htext") as "Hi56".
            assert (H56tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x56) : mword 64)
                              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))))
                            = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
            iApply (wp_cj_s_sconf (CID := CIDf) Φ (mword_of_int (KernelSyms.wakeup + 0x56))
                      (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")))
                      M4e av false ltac:(rewrite H56tgt; vm_compute; reflexivity)
                      with "Hcg Hpc Hi56 [-]").
            iApply wp_next_off_intro.
            iNext. iIntros "Hcg Hpc".
            iEval (rewrite H56tgt) in "Hpc".
            iApply ("Hrel" $! M4e with "[%] Hcg Hpc Htok HR").
            repeat split; [exact HM4e_9 | exact HM4e_2 | exact HM4e_18
                          | exact HM4e_19 | exact HM4e_20 | exact HM4e_21
                          | exact HM4e_22 | exact HM4e_23 | exact HM4e_24
                          | exact HM4e_25 | exact HM4e_26 | exact HM4e_27 | exact HdomM4e].
    }
    iIntros (k M) "%Hk %Hregs Hcg Hown Htext Hpc Hframe".
    iSpecialize ("Hloop" $! (NPROC - k)%nat).
    iSpecialize ("Hloop" $! CID0 with "[%]"); [by intros|].
    iApply ("Hloop" $! k M with "[%] [%] [%] Hqexit Hcg Hown Htext Hpc Hframe");
      [lia | exact Hk | exact Hregs].
  Qed.

  (* ===================================================================== *)
  (* Whole-function WP for wakeup(chan) over sconf: prologue -> loop        *)
  (* (k=0, exiting to the epilogue) -> return.  Mirrors the smode wp_wakeup  *)
  (* (CodeWakeup.v).  The caller supplies deep-K custody (K>=18, so deep-10    *)
  (* remains for the loop after the prologue's 8-slot frame carve) and       *)
  (* procs_inv.  proc_lock_res (SchedCtx.v) is threaded opaquely, ▷-slot     *)
  (* untouched.                                                             *)
  (* ===================================================================== *)
  Lemma wp_wakeup_sconf `{GEN : GenId} `{CID0 : CpuId}
      (Φ : mval -> iProp Σ)
      (m : regfile) (γs : list gname) (a0f pme : mword 64)
      (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool)
    : wp_wakeup_sconf_body Φ m γs a0f pme lvl K eb C b.
  Proof.
    cbv beta delta [wp_wakeup_sconf_body].
    intros sp0 spF rettgt HK Hdom Hlen Hmycpu Hmycpu_nz Hlvl.
    iIntros "Hcg Hown #Htext Hpc #Hpanic #Hpinv Hcont".
    (* ---- prologue: save frame (carve 8 from the cap's avail), set up loop regs ---- *)
    iApply (WakeupParts.wp_wakeup_prologue_sconf (CID := CID0) Φ m K b pme ltac:(lia) Hdom
              with "Hcg Htext Hpc [-]").
    iIntros (CIDpro Hspro M vpad) "%Hpro Hcg Hpc Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0".
    destruct Hpro as (HM9 & HM18 & HM19 & HM21 & HM20 & HMcsp & HM1 & HM22 & HM23 & HM24 & HM25 & HM26 & HM27 & HMdom).
    iDestruct (cpu_own_transport CID0 CIDpro lvl eb pme C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* ---- the loop, with the epilogue as its exit continuation ---- *)
    iPoseProof (wp_wakeup_loop_sconf (CID0 := CIDpro) Φ γs spF pme
                  (m !!! Regidx (mword_of_int 10 : mword 5))
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                  (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                  (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                  (m !!! Regidx (mword_of_int 21 : mword 5))
                  (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5))
                  (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 25 : mword 5))
                  (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) lvl
                  (K - 8)%nat eb C b
                  Hlen Hlvl ltac:(lia)
                  with "Hpinv Hpanic") as "Hloop".
    iSpecialize ("Hloop" with "[Hf0 Hcont]").
    { (* exit continuation = epilogue at wakeup+0x58 *)
      iIntros (CIDex Hsex Mexit) "(%Hecsp & %He22 & %He23 & %He24 & %He25 & %He26 & %He27 & %Hedom)
                       Hcg Hown Htextx Hpc Hframe".
      iDestruct "Hframe" as "(Hf7 & Hf6 & Hf5 & Hf4 & Hf3 & Hf2 & Hf1)".
      iApply (WakeupParts.wp_wakeup_epilogue_sconf (CID := CIDex) Φ Mexit K
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                (m !!! Regidx (mword_of_int 21 : mword 5)) vpad b pme
                ltac:(lia) Hedom
                with "Hcg Htextx Hpc [Hf7] [Hf6] [Hf5] [Hf4] [Hf3] [Hf2] [Hf1] [Hf0] [-]").
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
      iDestruct (cpu_own_transport CIDex CIDend lvl eb pme C b ltac:(wp_next_chain)
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
