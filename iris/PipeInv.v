(* PipeInv.v -- carving kalloc's page into the cells [struct pipe] names
   ([pipe_raw]), and the construction/destruction lemmas ([new_pipe],
   [page_own_pipe_raw], [pipe_raw_page_own], [pipe_bytes_page_own]) that only
   pipealloc / pipeclose / pipewrite need.

   The geometry, reference algebra, and [is_pipe] well-formedness predicate
   that everything ELSE (starting with [FileInv]'s [file_payload]) needs to
   merely HOLD a pipe reference now live in PipeInvDefs.v.  This file is that
   Defs file plus the page-carving/bitvector machinery below it, split out so
   the latter -- needed only by the four proofs above -- compiles IN PARALLEL
   with FileInv/ProcInv/SchedCtx/SpecPiperead/ProofPiperead instead of sitting
   as a serial prerequisite of all of them.  `Require Import PipeInv` still
   gets everything (this file `Require Export`s PipeInvDefs); switch to
   `Require Import PipeInvDefs` wherever only the light half is needed.  See
   claude-notes/optimization.md.

   Design: claude-notes/design/pipe.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.algebra Require Import frac dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import RiscvPtsto.
Require Import InstrBytes.
Require Import KallocInv.
Require Import PageFields.
Require Import WpLock.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Export PipeInvDefs.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Section PipeInv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (*  Carving kalloc's page into the cells [struct pipe] names            *)
  (* ------------------------------------------------------------------ *)

  (* the field addresses, as page offsets.  Each is one [add_vec] of a closed
     addend, so the bridge between the byte view ([pa_add]) and the
     instruction view ([poff_of] / WpLock's field forms) is a conversion. *)
  Lemma pa_pipe_lock (pi : mword 64) : pa_add pi 0%nat = pi.
  Proof. unfold pa_add. change (Z.of_nat 0) with 0. apply avi0. Qed.
  Lemma pa_pipe_name (pi : mword 64) : pa_add pi 8%nat = lock_name_field pi.
  Proof. unfold pa_add, add_vec_int, lock_name_field. apply f_equal.
         apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma pa_pipe_cpu (pi : mword 64) : pa_add pi 16%nat = lock_cpu pi.
  Proof. unfold pa_add, add_vec_int, lock_cpu. apply f_equal.
         apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma pa_pipe_nread (pi : mword 64) : pa_add pi 536%nat = a_pnread pi.
  Proof. unfold pa_add, add_vec_int, a_pnread, poff_of. apply f_equal.
         apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma pa_pipe_nwrite (pi : mword 64) : pa_add pi 540%nat = a_pnwrite pi.
  Proof. unfold pa_add, add_vec_int, a_pnwrite, poff_of. apply f_equal.
         apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma pa_pipe_ro (pi : mword 64) : pa_add pi 544%nat = a_popen pi false.
  Proof. unfold pa_add, add_vec_int, a_popen, poff_of. apply f_equal.
         apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma pa_pipe_wo (pi : mword 64) : pa_add pi 548%nat = a_popen pi true.
  Proof. unfold pa_add, add_vec_int, a_popen, poff_of. apply f_equal.
         apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma pipe_data_rebase (pi : mword 64) (bs : list (bv 8)) :
    ([∗ list] j ↦ b ∈ bs, pa_add (pa_add pi pipe_data_off) j ↦ₘ b) ⊣⊢ pipe_data pi bs.
  Proof.
    rewrite /pipe_data. apply big_sepL_proper. intros k b _. by rewrite pa_add_add.
  Qed.

  (* the ten windows [struct pipe] divides its page into. *)
  Local Lemma pipe_windows (pi : mword 64) :
    page_own pi ⊢
      ([∗ list] j ∈ seq 0 4, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 4 4, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 8 8, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 16 8, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 24 512, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 536 4, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 540 4, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 544 4, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 548 4, byte_any (pa_add pi j)) ∗
      ([∗ list] j ∈ seq 552 3544, byte_any (pa_add pi j)).
  Proof.
    rewrite /page_own.
    replace 4096%nat with (4 + 4092)%nat by lia.
    rewrite (bwin_split pi 0 4 4092). replace (0 + 4)%nat with 4%nat by lia.
    replace 4092%nat with (4 + 4088)%nat by lia.
    rewrite (bwin_split pi 4 4 4088). replace (4 + 4)%nat with 8%nat by lia.
    replace 4088%nat with (8 + 4080)%nat by lia.
    rewrite (bwin_split pi 8 8 4080). replace (8 + 8)%nat with 16%nat by lia.
    replace 4080%nat with (8 + 4072)%nat by lia.
    rewrite (bwin_split pi 16 8 4072). replace (16 + 8)%nat with 24%nat by lia.
    replace 4072%nat with (512 + 3560)%nat by lia.
    rewrite (bwin_split pi 24 512 3560). replace (24 + 512)%nat with 536%nat by lia.
    replace 3560%nat with (4 + 3556)%nat by lia.
    rewrite (bwin_split pi 536 4 3556). replace (536 + 4)%nat with 540%nat by lia.
    replace 3556%nat with (4 + 3552)%nat by lia.
    rewrite (bwin_split pi 540 4 3552). replace (540 + 4)%nat with 544%nat by lia.
    replace 3552%nat with (4 + 3548)%nat by lia.
    rewrite (bwin_split pi 544 4 3548). replace (544 + 4)%nat with 548%nat by lia.
    replace 3548%nat with (4 + 3544)%nat by lia.
    rewrite (bwin_split pi 548 4 3544). replace (548 + 4)%nat with 552%nat by lia.
    done.
  Qed.

  Local Lemma pipe_windows_named (pi : mword 64) (c : bv 8) :
    page_filled pi c ⊢
      ([∗ list] j ∈ seq 0 4, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 4 4, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 8 8, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 16 8, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 24 512, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 536 4, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 540 4, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 544 4, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 548 4, (pa_add pi j) ↦ₘ c) ∗
      ([∗ list] j ∈ seq 552 3544, (pa_add pi j) ↦ₘ c).
  Proof.
    rewrite /page_filled.
    replace 4096%nat with (4 + 4092)%nat by lia.
    rewrite (bwin_named_split pi 0 4 4092). replace (0 + 4)%nat with 4%nat by lia.
    replace 4092%nat with (4 + 4088)%nat by lia.
    rewrite (bwin_named_split pi 4 4 4088). replace (4 + 4)%nat with 8%nat by lia.
    replace 4088%nat with (8 + 4080)%nat by lia.
    rewrite (bwin_named_split pi 8 8 4080). replace (8 + 8)%nat with 16%nat by lia.
    replace 4080%nat with (8 + 4072)%nat by lia.
    rewrite (bwin_named_split pi 16 8 4072). replace (16 + 8)%nat with 24%nat by lia.
    replace 4072%nat with (512 + 3560)%nat by lia.
    rewrite (bwin_named_split pi 24 512 3560). replace (24 + 512)%nat with 536%nat by lia.
    replace 3560%nat with (4 + 3556)%nat by lia.
    rewrite (bwin_named_split pi 536 4 3556). replace (536 + 4)%nat with 540%nat by lia.
    replace 3556%nat with (4 + 3552)%nat by lia.
    rewrite (bwin_named_split pi 540 4 3552). replace (540 + 4)%nat with 544%nat by lia.
    replace 3552%nat with (4 + 3548)%nat by lia.
    rewrite (bwin_named_split pi 544 4 3548). replace (544 + 4)%nat with 548%nat by lia.
    replace 3548%nat with (4 + 3544)%nat by lia.
    rewrite (bwin_named_split pi 548 4 3544). replace (548 + 4)%nat with 552%nat by lia.
    done.
  Qed.

  (* THE carve: kalloc's page becomes the raw [struct pipe].  Every cell is in
     the exact shape the instruction that touches it produces, so pipealloc's
     stores need no address rewriting.  [pipe_raw] is the pipe analogue of
     SleepLock's [sl_raw]. *)
  Definition pipe_raw (pi : mword 64) : iProp Σ :=
    ((∃ vlock : mword 32, pi ↦₄ vlock) ∗
     (∃ vname : mword 64, lock_name_field pi ↦₈ vname) ∗
     (∃ vcpu : mword 64, lock_cpu pi ↦₈ vcpu) ∗
     (∃ bs : list (bv 8), ⌜length bs = PIPESIZE⌝ ∗ pipe_data pi bs) ∗
     (∃ nr : mword 32, a_pnread pi ↦₄ nr) ∗
     (∃ nw : mword 32, a_pnwrite pi ↦₄ nw) ∗
     (∃ ro : mword 32, a_popen pi false ↦₄ ro) ∗
     (∃ wo : mword 32, a_popen pi true ↦₄ wo) ∗
     pipe_slack pi)%I.

  (* A6.87: THE CARVE IS OFF THE *WRITE*.  [page_own] is the
     visibility-free page now, so a pipe cannot be carved out of one --
     [pipealloc] carves the page KALLOC MEMSET, which arrives as
     [KallocInv.page_filled] and is a named window at every field. *)
  Lemma page_filled_pipe_raw (pi : mword 64) (c : bv 8) :
    page_valid pi -> page_filled pi c ⊢ pipe_raw pi.
  Proof.
    intro Hpv. rewrite pipe_windows_named /pipe_raw /pipe_slack.
    iIntros "(W0 & W4 & W8 & W16 & Wd & W536 & W540 & W544 & W548 & Wtail)".
    iSplitL "W0".
    { rewrite (page_field4_named pi 0 (fun _ => c) Hpv ltac:(lia) ltac:(exists 0; reflexivity)).
      iDestruct "W0" as (w) "Hw". iExists w.
      iEval (rewrite pa_pipe_lock) in "Hw". iExact "Hw". }
    iSplitL "W8".
    { rewrite (page_field8_named pi 8 (fun _ => c) Hpv ltac:(lia) ltac:(exists 1; vm_compute; reflexivity)).
      iDestruct "W8" as (w) "Hw". iExists w.
      iEval (rewrite pa_pipe_name) in "Hw". iExact "Hw". }
    iSplitL "W16".
    { rewrite (page_field8_named pi 16 (fun _ => c) Hpv ltac:(lia) ltac:(exists 2; vm_compute; reflexivity)).
      iDestruct "W16" as (w) "Hw". iExists w.
      iEval (rewrite pa_pipe_cpu) in "Hw". iExact "Hw". }
    iSplitL "Wd".
    { rewrite bwin_named_rebase (bwin_named_bytes_list (pa_add pi 24%nat) 512 (fun _ => c)).
      iDestruct "Wd" as (bs) "[%Hlen Hbs]". iExists bs.
      iSplit; [iPureIntro; rewrite Hlen; reflexivity|].
      rewrite -pipe_data_rebase. iExact "Hbs". }
    iSplitL "W536".
    { rewrite (page_field4_named pi 536 (fun _ => c) Hpv ltac:(lia) ltac:(exists 134; vm_compute; reflexivity)).
      iDestruct "W536" as (w) "Hw". iExists w.
      iEval (rewrite pa_pipe_nread) in "Hw". iExact "Hw". }
    iSplitL "W540".
    { rewrite (page_field4_named pi 540 (fun _ => c) Hpv ltac:(lia) ltac:(exists 135; vm_compute; reflexivity)).
      iDestruct "W540" as (w) "Hw". iExists w.
      iEval (rewrite pa_pipe_nwrite) in "Hw". iExact "Hw". }
    iSplitL "W544".
    { rewrite (page_field4_named pi 544 (fun _ => c) Hpv ltac:(lia) ltac:(exists 136; vm_compute; reflexivity)).
      iDestruct "W544" as (w) "Hw". iExists w.
      iEval (rewrite pa_pipe_ro) in "Hw". iExact "Hw". }
    iSplitL "W548".
    { rewrite (page_field4_named pi 548 (fun _ => c) Hpv ltac:(lia) ltac:(exists 137; vm_compute; reflexivity)).
      iDestruct "W548" as (w) "Hw". iExists w.
      iEval (rewrite pa_pipe_wo) in "Hw". iExact "Hw". }
    iSplitL "W4"; [ iApply bwin_named_any; iExact "W4" | ].
    iApply bwin_named_any. iExact "Wtail".
  Qed.

  (* THE carve, run backwards: the object's fields become the page again.
     [bwin_split] / [bwin_rebase] are equivalences and PageFields has the
     backward leaves, so this is [page_own_pipe_raw] read bottom-up.  It is
     what turns release's spoils back into [kfree_pre]. *)
  Lemma pipe_raw_page_own (pi : mword 64) :
    pipe_raw pi ⊢ page_own pi.
  Proof.
    rewrite /page_own /pipe_raw /pipe_slack.
    replace 4096%nat with (4 + 4092)%nat by lia.
    rewrite (bwin_split pi 0 4 4092). replace (0 + 4)%nat with 4%nat by lia.
    replace 4092%nat with (4 + 4088)%nat by lia.
    rewrite (bwin_split pi 4 4 4088). replace (4 + 4)%nat with 8%nat by lia.
    replace 4088%nat with (8 + 4080)%nat by lia.
    rewrite (bwin_split pi 8 8 4080). replace (8 + 8)%nat with 16%nat by lia.
    replace 4080%nat with (8 + 4072)%nat by lia.
    rewrite (bwin_split pi 16 8 4072). replace (16 + 8)%nat with 24%nat by lia.
    replace 4072%nat with (512 + 3560)%nat by lia.
    rewrite (bwin_split pi 24 512 3560). replace (24 + 512)%nat with 536%nat by lia.
    replace 3560%nat with (4 + 3556)%nat by lia.
    rewrite (bwin_split pi 536 4 3556). replace (536 + 4)%nat with 540%nat by lia.
    replace 3556%nat with (4 + 3552)%nat by lia.
    rewrite (bwin_split pi 540 4 3552). replace (540 + 4)%nat with 544%nat by lia.
    replace 3552%nat with (4 + 3548)%nat by lia.
    rewrite (bwin_split pi 544 4 3548). replace (544 + 4)%nat with 548%nat by lia.
    replace 3548%nat with (4 + 3544)%nat by lia.
    rewrite (bwin_split pi 548 4 3544). replace (548 + 4)%nat with 552%nat by lia.
    iIntros "(Hw & Hnm & Hcpu & Hdat & Hnr & Hnw & Hro & Hwo & Hpad & Htail)".
    iSplitL "Hw".
    { iDestruct "Hw" as (v) "Hv". by iApply word4_bwin. }
    iFrame "Hpad".
    iSplitL "Hnm".
    { iDestruct "Hnm" as (v) "Hv". iEval (rewrite -(pa_pipe_name pi)) in "Hv".
      by iApply (page_field8_back pi 8). }
    iSplitL "Hcpu".
    { iDestruct "Hcpu" as (v) "Hv". iEval (rewrite -(pa_pipe_cpu pi)) in "Hv".
      by iApply (page_field8_back pi 16). }
    iSplitL "Hdat".
    { iDestruct "Hdat" as (bs) "[%Hlen Hbs]".
      iEval (rewrite -pipe_data_rebase) in "Hbs".
      rewrite (bwin_rebase pi 24 512).
      iPoseProof (bytes_list_bwin (pa_add pi pipe_data_off) bs with "Hbs") as "Hbs".
      rewrite Hlen. iExact "Hbs". }
    iSplitL "Hnr".
    { iDestruct "Hnr" as (v) "Hv". iEval (rewrite -(pa_pipe_nread pi)) in "Hv".
      by iApply (page_field4_back pi 536). }
    iSplitL "Hnw".
    { iDestruct "Hnw" as (v) "Hv". iEval (rewrite -(pa_pipe_nwrite pi)) in "Hv".
      by iApply (page_field4_back pi 540). }
    iSplitL "Hro".
    { iDestruct "Hro" as (v) "Hv". iEval (rewrite -(pa_pipe_ro pi)) in "Hv".
      by iApply (page_field4_back pi 544). }
    iSplitL "Hwo"; [| iExact "Htail" ].
    iDestruct "Hwo" as (v) "Hv". iEval (rewrite -(pa_pipe_wo pi)) in "Hv".
    by iApply (page_field4_back pi 548).
  Qed.

  (* §0.26′ / A6.86: THE SAME REASSEMBLY AT THE FREE TIER, and it is the
     site that forced the whole ruling (A6.84 §(2)).  After the M4 flip the
     owner window is eight LEDGER cells; they cannot re-enter the ctx tower
     (that needs a drain) and they do not have to -- [kfree_pre] is
     [page_free] now, so the page came down to meet the cell.  The proof is
     [pipe_raw_page_own]'s, window for window, with [bwin_split] and a
     [bwin_any_free] on each REGISTERED window; the owner window is already
     free bytes ([WpLock.lk_cpu_fresh_free]). *)
  (* what release hands back, reassembled into what kfree wants. *)
  Lemma pipe_bytes_page_own (pi : mword 64) (v : mword 32) :
    pi ↦₄ v -∗ WpLock.lk_cpu_fresh pi -∗ pipe_bytes pi -∗ page_own pi.
  Proof.
    iIntros "Hw Hcpu Hb".
    iDestruct "Hb" as (vname nr nw ro wo bs) "(Hnm & Hnr & Hnw & Hro & Hwo & %Hlen & Hdat & Hslack)".
    iDestruct (WpLock.lk_cpu_fresh_free with "Hcpu") as "Hcpu".
    rewrite /page_own /pipe_slack.
    replace 4096%nat with (4 + 4092)%nat by lia.
    rewrite (bwin_split pi 0 4 4092). replace (0 + 4)%nat with 4%nat by lia.
    replace 4092%nat with (4 + 4088)%nat by lia.
    rewrite (bwin_split pi 4 4 4088). replace (4 + 4)%nat with 8%nat by lia.
    replace 4088%nat with (8 + 4080)%nat by lia.
    rewrite (bwin_split pi 8 8 4080). replace (8 + 8)%nat with 16%nat by lia.
    replace 4080%nat with (8 + 4072)%nat by lia.
    rewrite (bwin_split pi 16 8 4072). replace (16 + 8)%nat with 24%nat by lia.
    replace 4072%nat with (512 + 3560)%nat by lia.
    rewrite (bwin_split pi 24 512 3560). replace (24 + 512)%nat with 536%nat by lia.
    replace 3560%nat with (4 + 3556)%nat by lia.
    rewrite (bwin_split pi 536 4 3556). replace (536 + 4)%nat with 540%nat by lia.
    replace 3556%nat with (4 + 3552)%nat by lia.
    rewrite (bwin_split pi 540 4 3552). replace (540 + 4)%nat with 544%nat by lia.
    replace 3552%nat with (4 + 3548)%nat by lia.
    rewrite (bwin_split pi 544 4 3548). replace (544 + 4)%nat with 548%nat by lia.
    replace 3548%nat with (4 + 3544)%nat by lia.
    rewrite (bwin_split pi 548 4 3544). replace (548 + 4)%nat with 552%nat by lia.
    iDestruct "Hslack" as "[Hpad Htail]".
    iSplitL "Hw".
    { by iApply word4_bwin. }
    iSplitL "Hpad"; [ iExact "Hpad" | ].
    iSplitL "Hnm".
    {
      iEval (rewrite -(pa_pipe_name pi)) in "Hnm".
      by iApply (page_field8_back pi 8). }
    iSplitL "Hcpu".
    { rewrite (bwin_rebase pi 16 8).
      iEval (rewrite (pa_pipe_cpu pi)). iExact "Hcpu". }
    iSplitL "Hdat".
    {
      iEval (rewrite -pipe_data_rebase) in "Hdat".
      rewrite (bwin_rebase pi 24 512).
      iPoseProof (bytes_list_bwin (pa_add pi pipe_data_off) bs with "Hdat") as "Hdat".
      rewrite Hlen. iExact "Hdat". }
    iSplitL "Hnr".
    {
      iEval (rewrite -(pa_pipe_nread pi)) in "Hnr".
      by iApply (page_field4_back pi 536). }
    iSplitL "Hnw".
    {
      iEval (rewrite -(pa_pipe_nwrite pi)) in "Hnw".
      by iApply (page_field4_back pi 540). }
    iSplitL "Hro".
    {
      iEval (rewrite -(pa_pipe_ro pi)) in "Hro".
      by iApply (page_field4_back pi 544). }
    iSplitL "Hwo".
    {
      iEval (rewrite -(pa_pipe_wo pi)) in "Hwo".
      by iApply (page_field4_back pi 548). }
    iExact "Htail".
  Qed.


  (* ------------------------------------------------------------------ *)
  (*  Construction: pipealloc's ghost step                               *)
  (* ------------------------------------------------------------------ *)

  (* the four end ghosts: a reference and a marker per end. *)
  Lemma pipe_ends_alloc :
    ⊢ |==> ∃ γp : pipe_names,
             pipe_end_full γp false ∗ pipe_end_full γp true ∗
             pipe_openmark γp false ∗ pipe_openmark γp true.
  Proof.
    iMod (own_alloc (1%Qp : fracR)) as (γr) "Hr"; [done|].
    iMod (own_alloc (1%Qp : fracR)) as (γw) "Hw"; [done|].
    iMod (own_alloc (DfracOwn 1)) as (γmr) "Hmr"; [done|].
    iMod (own_alloc (DfracOwn 1)) as (γmw) "Hmw"; [done|].
    iModIntro. iExists (MkPipeNames γr γw γmr γmw).
    by iFrame "Hr Hw Hmr Hmw".
  Qed.

  (* The state pipealloc has in hand once initlock returns: the four fields it
     wrote (readopen = writeopen = 1, nread = nwrite = 0), the lock's two words
     zeroed and its name sealed, the untouched data buffer, and the rest of the
     page.  Out come the pipe and its two ends, one for each of the two files.

     Note the data buffer is NOT zeroed by pipealloc -- [bs] is whatever kalloc
     handed over -- which is exactly right: no byte of it is readable until
     nwrite has passed it. *)
  Lemma new_pipe `{CID : RiscvLang.CpuId} E (pi : mword 64) (vname : mword 64)
      (bs : list (bv 8)) :
    page_valid pi ->
    length bs = PIPESIZE ->
    lock_name_field pi ↦₈ vname -∗
    pi ↦₄ (mword_of_int 0 : mword 32) -∗
    WpLock.lk_cpu_fresh pi -∗
    a_pnread pi ↦₄ (mword_of_int 0 : mword 32) -∗
    a_pnwrite pi ↦₄ (mword_of_int 0 : mword 32) -∗
    a_popen pi false ↦₄ (mword_of_int 1 : mword 32) -∗
    a_popen pi true ↦₄ (mword_of_int 1 : mword 32) -∗
    pipe_data pi bs -∗
    pipe_slack pi -∗
    own_context cur_ctx
    ={E}=∗ own_context cur_ctx ∗ ∃ (γl : gname) (γp : pipe_names),
             is_pipe γl γp pi ∗ pipe_ref γp false 1 ∗ pipe_ref γp true 1.
  Proof.
    iIntros (Hpv Hlen) "Hnm Hword Hcpu Hnr Hnw Hro Hwo Hdata Hslack Hrun".
    (* the lock's state gname FIRST: [pipe_dead] mentions it. *)
    iMod (newlock_d E pi with "Hword Hcpu") as (γl) "Hmake".
    iMod pipe_ends_alloc as (γp) "(Hrd & Hwr & Hm0 & Hm1)".
    (* A6.67: the DELAYED form takes [CtxMorph] as a pure premise and the
       running token beside the payload (A6.66); both come straight back. *)
    iMod ("Hmake" $! (<{ pipe_res γp pi }>) (pipe_dead γl γp) with "[%] Hrun
            [Hnm Hnr Hnw Hro Hwo Hdata Hslack Hm0 Hm1]") as "[Hrun #Hlk]".
    { apply _. }
    { iExists (mword_of_int 0 : mword 32), (mword_of_int 0 : mword 32),
              (mword_of_int 1 : mword 32), (mword_of_int 1 : mword 32), vname, bs.
      iFrame "Hnm Hnr Hnw Hro Hwo Hdata Hslack".
      iSplitL "Hm0"; [by iApply (pipe_endstate_open_intro _ _ _ pflag_one_open with "Hm0")|].
      iSplitL "Hm1"; [by iApply (pipe_endstate_open_intro _ _ _ pflag_one_open with "Hm1")|].
      iSplit; [iPureIntro; exact pipe_count_ok_00 | done]. }
    iModIntro. iFrame "Hrun". iExists γl, γp.
    rewrite /is_pipe. iFrame "Hrd Hwr".
    iSplit; [done|]. iExact "Hlk".
  Qed.

End PipeInv.
