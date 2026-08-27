(* WpSconfFencePub.v -- THE PUBLISHING FENCE, at the sconf tier
   (tso-machine-flip.md A6.72; the owner ruling of 2026-08-27).

   [HartBarrier.wp_hart_barrier] is A6.5's ratified barrier leaf -- the
   separate rule over the Barrier node that DRAINS and MINTS the receipt.
   This file lifts it to the leaf tier a whole-function proof calls:
   [wp_fence_pub_s_sconf] is [WpSconfCtl.wp_fence_gen_s_sconf] with a
   [HartBarrier.pub_step] threaded through, i.e. `fence rw,rw` as a
   PUBLICATION POINT.

   WHY rw,rw AND NOT A GENERIC pred/succ.  Only four of the model's nine
   barrier kinds drain under Ztso ([RiscvLang.fence_drains]: the W->R
   edges), and the dispatch's fallback arm is not a barrier at all -- so a
   pred/succ-generic publishing rule would be false.  `fence rw,rw` is
   [__sync_synchronize], the ONE fence in xv6 that is a release point for
   everything the hart has written, and it is the one main() uses before
   `started = 1`.  The dispatch is decided here once: bits [1:0] of both
   sets are 11 whatever [effective_fence_set] does with FIOM, so the arm is
   [Barrier_RISCV_rw_rw] at either value of the CSR bit.

   THE CONTINUATION IS UNDER A LATER, as [wp_fence_gen_later_s_sconf]'s is
   and for the same reason: a fence IS a program step, and the ghost step
   this rule runs happens INSIDE it.  A caller with nothing to strip uses
   the non-publishing leaf. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes RegFile HartTp WpNext.
Require Import RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import HartSwp HartLift HartEvents HartBarrier.
Require Import WpSconfEngine.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import Xv6G.
Require Import TsoMemPa TsoGhost TsoCtx.
Import Defs.

(* THE DISPATCH FACT, once: `fence rw,rw`'s effective sets keep bits [1:0]
   at 11 whether or not FIOM is set, so the model's nine-way chain takes its
   FIRST arm and the barrier is [Barrier_RISCV_rw_rw]. *)
Lemma fence_rw_bits (fiom : bool) :
  eq_vec (subrange_vec_dec
            (effective_fence_set (mword_of_int 3 : mword 4) fiom) 1 0)
    ('b"11") = true.
Proof. destruct fiom; vm_compute; reflexivity. Qed.

Section WpSconfFencePub.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {kt : ktier}.
  Context {p : mword 64}.

  (* ------------------------------------------------------------------ *)
  (* §1 THE BARRIER NODE, in the shape the model's dispatch leaves it.    *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_barrier_pub (bk : rv64d_types.barrier_kind) (P Q : iProp Σ) :
    fence_drains bk = true ->
    gen_cert -∗ pub_step P Q -∗ P -∗
    swp (Defs.bind0 (sail_barrier bk) (returnM RETIRE_SUCCESS))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ Q).
  Proof.
    iIntros (Hdrain) "#Hcert Hpub HP".
    iApply (swp_hart_barrier (X := ExecutionResult) bk
              (Defs.bind0 (sail_barrier bk) (returnM RETIRE_SUCCESS)) _ P Q
              ltac:(reflexivity) Hdrain with "Hcert Hpub HP").
    iNext. iIntros "HQ". iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §2 `fence rw,rw` AS A WHOLE INSTRUCTION.                             *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_execute_FENCE_pub_S (fm : mword 4) (rs rd : regidx)
      (menv : mword 64) (P Q : iProp Σ) :
    gen_cert -∗ cur_privilege ↦ᵣ Supervisor -∗ menvcfg ↦ᵣ menv -∗
    pub_step P Q -∗ P -∗
    swp (execute (FENCE (fm, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4,
                         rs, rd)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ Q ∗
                cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ menv).
  Proof.
    iIntros "#Hcert Hpriv Hmenv Hpub HP".
    change (execute (FENCE (fm, mword_of_int 3 : mword 4,
                            mword_of_int 3 : mword 4, rs, rd)))
      with (execute_FENCE fm (mword_of_int 3 : mword 4)
              (mword_of_int 3 : mword 4) rs rd).
    unfold execute_FENCE.
    iApply (swp_bind_use (is_fiom_active tt) _
              (fun v => ⌜v = eq_vec (_get_MEnvcfg_FIOM menv) ('b"1")⌝ ∗
                        cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ menv)%I _
              with "[Hpriv Hmenv] [-]").
    { iApply (swp_is_fiom_active_S menv with "Hcert Hpriv Hmenv"). }
    iIntros (v) "(-> & Hpriv & Hmenv)".
    cbn match.
    rewrite (fence_rw_bits (eq_vec (_get_MEnvcfg_FIOM menv) ('b"1"))).
    cbn match.
    iApply (swp_mono _ (fun e : ExecutionResult =>
                          ⌜e = RETIRE_SUCCESS⌝ ∗ Q)%I _
              with "[Hpriv Hmenv] [Hpub HP]").
    - iIntros (e) "[-> HQ]". iSplitR; [done|]. iFrame.
    - iApply (swp_barrier_pub rv64d_types.Barrier_RISCV_rw_rw P Q ltac:(reflexivity)
                with "Hcert Hpub HP").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3 THE LEAF, AT INTERRUPTS-OFF -- and that is not a convenience.      *)
  (*                                                                      *)
  (* [pub_step] is HART-INDEXED (its receipt is [hart_view_lb] at THIS     *)
  (* hart, and the token a publisher spends is [own_context], which A6.64  *)
  (* found is [CpuId]-indexed too).  The generic engine's step obligation  *)
  (* is stated at a ∀-BOUND hart, so a publishing leaf cannot go through   *)
  (* it: it goes through [WpSmodeIntr.wp_instr_s_sconf] and collapses the  *)
  (* binder with [WpNext.wp_next_off_intro] -- the [WpSconfSfence]         *)
  (* precedent, and the same reason ([tlb ↦ᵣ] there, the token here).      *)
  (* [__sync_synchronize] runs in main's boot arm with interrupts off, so  *)
  (* the premise costs the one caller nothing.                            *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_fence_pub_s_sconf
      (pc : mword 64) (fm : mword 4) (rs rd : regidx)
      (m : regfile) (n : nat) (P Q : iProp Σ) :
    sie_cap_gpr kt m n false p -∗
    pc_is pc -∗
    instr pc false (FENCE (fm, mword_of_int 3 : mword 4,
                           mword_of_int 3 : mword 4, rs, rd)) -∗
    pub_step P Q -∗ P -∗
    ▷ (sie_cap_gpr kt m n false p -∗
       pc_is (add_vec_int pc 4) -∗ Q -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr Hpub HP Hcont".
    iApply (wp_instr_s_sconf m n false false pc false
              (FENCE (fm, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4,
                      rs, rd))
              (fun (_ : CpuId) npc _ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗ Q)%I
              with "Hcg Hpc Hinstr [Hpub HP Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_ctl_acc with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      iApply (swp_mono with
                "[Hcap Hfile HPC HnPC Hresv Hback] [Hpriv Hmenv Hpub HP]");
        [| iApply (swp_execute_FENCE_pub_S fm rs rd MENVCFG_S P Q
                     with "Hcert Hpriv Hmenv Hpub HP") ].
      iIntros (e) "(-> & HQ & Hpriv & Hmenv)". iSplitR; [done|].
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc".
      iDestruct (sconf_at_priv_open with "Hsc") as (ms') "Hscp".
      iExists (add_vec_int pc 4), ms', m, n.
      iFrame "HPC HnPC Hresv Hscp Hcap Hfile HQ". by iPureIntro.
    - iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & HQ)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" with "Hcg' Hpc' HQ").
  Qed.

End WpSconfFencePub.
