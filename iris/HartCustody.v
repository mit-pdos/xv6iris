(* HartCustody.v -- CUSTODY: a client fupd against [state_interp]'s started
   counter, at any expression of the thread's generation, WITHOUT a step.

   Design: claude-notes/design/sync.md §4.3 item 3a; the crash-invariant side
   in claude-notes/design/crash.md.  The ghost commit of the durability work
   (a [mWP e -∗ mWP e] rule run at an arbitrary point of a kernel proof)
   needs [start_auth (gen_id + 1)] -- the started counter's AUTH, which only
   [state_interp] holds -- together with, for [wp_crash_fupd], the crash
   invariant opened at [⊤].  Neither needs the machine to MOVE.

   THE ONE DESIGN POINT.  A client fupd runs against the state
   interpretation without taking a step because the WP is UNFOLDED ONCE:
   [wp_unfold] exposes [∀ σ, state_interp σ ={⊤,∅}=∗ ...]; the fupd runs at
   [⊤] BEFORE the mask drops, on the [start_auth] conjunct; and the SAME
   [state_interp] (same [σ], same counts, same trace) is handed on to the
   continuation's own unfolding, which then takes the step the continuation
   was going to take anyway.  So no instruction leaf changes and the
   instruction chain ([swp_loop] → [swp_tick_wrap_ex] → … →
   [RiscvExec.wp_hart_step]) is untouched.  The case split is
   [wp_hart_step]'s: LIVE ([ggen = gen_id], power on) pins [start_count g =
   gen_id + 1]; DEAD ([gen_id < ggen]) hands the untouched [state_interp] to
   the unfolded [RiscvExec.wp_dead] (the hook is never run, and need not
   be: a dead thread's continuation is never reached); current-but-off is
   refuted by [gen_started].

   THE SECOND OPENER OF [crash_inv].  [RiscvPtsto.crash_inv]'s comment
   names the DMA completion ([WpUart.wp_disk_loop]) as its only opener;
   [wp_crash_fupd] below is the second.  It opens the invariant inside the
   custody fupd at [⊤], i.e. at a point where no step is being taken, so it
   composes with anything the continuation's step opens later. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat invariants.
From iris.program_logic Require Import language weakestpre.
Require Import RiscvLang RiscvPtsto RiscvExec.

Section Custody.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_start_auth_fupd (e : mexpr) (P : iProp Σ) :
    thread_gen e = Some gen_id ->
    gen_cert -∗
    (∀ n : nat, ⌜n = (gen_id + 1)%nat⌝ -∗ start_auth n ={⊤}=∗ start_auth n ∗ P) -∗
    (P -∗ mWP e) -∗ mWP e.
  Proof using .
    intros Hg.
    iIntros "#(Hborn & Hstarted & _) Hhook Hk".
    iEval (rewrite /wp_triv wp_unfold /wp_pre /=).
    iIntros (g ns κ κs nt) "((Hgauth & Hsauth & Htie & HR) & Hobs)".
    iDestruct (mono_nat_auth_lb_own_valid with "Hgauth Hborn") as %[_ Hbge].
    iDestruct (mono_nat_auth_lb_own_valid with "Hsauth Hstarted") as %[_ Hsge].
    destruct (decide (g.(ggen) = gen_id)) as [Heq|Hne]; last first.
    { (* DEAD -- the birth bound rules out the unborn side *)
      iDestruct (mono_nat_lb_own_get with "Hgauth") as "#Hlb".
      iDestruct (mono_nat_lb_own_le (n := g.(ggen)) (S gen_id) with "Hlb")
        as "#Hdead"; [lia|].
      iPoseProof (wp_dead e gen_id Hg with "Hdead") as "Hwp".
      iEval (rewrite /wp_triv wp_unfold /wp_pre /=) in "Hwp".
      iApply ("Hwp" $! g ns κ κs nt).
      iFrame "Hgauth Hsauth Htie HR Hobs". }
    (* current-but-off is refuted by [gen_started]; LIVE pins the count *)
    assert (Hsc : start_count g = (gen_id + 1)%nat).
    { revert Hsge. rewrite /start_count. destruct (gpow g); lia. }
    iMod ("Hhook" $! (start_count g) with "[] Hsauth") as "[Hsauth HP]".
    { iPureIntro. exact Hsc. }
    iPoseProof ("Hk" with "HP") as "Hwp".
    iEval (rewrite /wp_triv wp_unfold /wp_pre /=) in "Hwp".
    iApply ("Hwp" $! g ns κ κs nt).
    iFrame "Hgauth Hsauth Htie HR Hobs".
  Qed.

  Lemma wp_crash_fupd (e : mexpr) (P : iProp Σ) :
    thread_gen e = Some gen_id ->
    gen_cert -∗ crash_inv -∗
    (∀ n : nat, ⌜n = (gen_id + 1)%nat⌝ -∗ start_auth n -∗ ▷ riscv_crash_pred
       ={⊤ ∖ ↑crashN}=∗ start_auth n ∗ ▷ riscv_crash_pred ∗ P) -∗
    (P -∗ mWP e) -∗ mWP e.
  Proof using .
    intros Hg.
    iIntros "#Hcert #Hinv Hhook Hk".
    iApply (wp_start_auth_fupd e P Hg with "Hcert [Hhook] Hk").
    iIntros (n) "%Hn Hs".
    iInv "Hinv" as "Hc" "Hclose".
    iMod ("Hhook" $! n with "[//] Hs Hc") as "(Hs & Hc & HP)".
    iMod ("Hclose" with "Hc") as "_".
    iModIntro. iFrame "Hs HP".
  Qed.

  (* the instance at the instruction boundary *)
  Lemma wp_crash_fupd_loop (P : iProp Σ) :
    gen_cert -∗ crash_inv -∗
    (∀ n : nat, ⌜n = (gen_id + 1)%nat⌝ -∗ start_auth n -∗ ▷ riscv_crash_pred
       ={⊤ ∖ ↑crashN}=∗ start_auth n ∗ ▷ riscv_crash_pred ∗ P) -∗
    (P -∗ mWP (Loop : expr riscv_lang)) -∗ mWP (Loop : expr riscv_lang).
  Proof using . apply wp_crash_fupd. reflexivity. Qed.
End Custody.
