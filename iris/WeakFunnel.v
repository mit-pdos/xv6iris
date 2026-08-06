(** * WeakFunnel.v — the weak-memory M-mode instruction funnel (M4-prep)

    Every SC leaf in the tree goes through [InstrBytes.wp_instr]: the caller
    supplies [InstrBytes.instr pc is_rvc i] plus the M-mode config bundle and
    owes exactly ONE [execute] fact.  On the weak side the leaf-facing rule is
    [WeakInstr.wp_winstr], whose callback owes the WHOLE
    [exec (riscv_step tick) (WeakBridge.wflat_st σ)] for both ticks — fetch,
    decode, the [try_step] wrapper and all.  Nothing bridged the two.  THIS
    FILE IS THAT BRIDGE.

    Three pieces, in dependency order.

    §1  [exec_fetch_flat] — [InstrBytes.fetch_from_instr_bytes] with ALL the
        Iris removed.  That lemma consumes [RiscvPtsto.mstate_interp] for
        exactly two reasons: [reg_valid_dq] to read the fetch config
        registers, and [phys_valid]/[phys_ram]/[text_ident_phys] to turn
        [↦ₓ] byte ownership into [σ.(mem) !! pa = Some b] plus [addr_is_ram].
        Neither is available on the weak side (the weak [riscvGS] heap gname
        is an unused placeholder), so both become PURE hypotheses, packaged as
        [fetch_flat_ok].  The VA→PA machinery ([kmap_static] /
        [text_ident_phys]) disappears outright: weak addresses are already
        physical and [fetch_pa_id] says [fetch_pa pc = pc].  All three
        alignment arms are kept (F_Base 4-aligned, F_Base 2-aligned-not-4,
        F_RVC at either alignment).

        [InstrBytes.fetch_from_instr_bytes] is a ~10-line corollary of this
        lemma (own the bytes, [phys_valid]/[phys_ram] them into
        [fetch_flat_ok], apply); that file is not edited here.

    §2  [winstr] — the weak twin of [InstrBytes.instr].  [instr] cannot be
        reused: its [instr_bytes] component is [↦ₓ] gen_heap ownership and its
        decode field is a wand taking [mstate_interp].  [winstr]'s bytes are
        the [WeakInstr.wkernel_text] spelling ([wlat_pointsto … DfracDiscarded
        0 …], an [iProp]: objective AND persistent) and its decode field is
        [InstrBytes.instr]'s decode field with the [mstate_interp σ -∗]
        wrapper STRIPPED, [σ] universally quantified as a plain [t : mstate]
        and the conclusion left pure.  Nothing in it needs resources — which
        is the point: THE DECODE FACTS A CALLER FEEDS IN ARE REUSABLE VERBATIM
        from the existing decode libraries.

    §3  [wwp_instr] — the funnel.  Built on [WeakInstr.wp_winstr], it does the
        entire [riscv_step] wrapper (read cur_privilege; [should_inc_minstret]
        → [b]; write [minstret_increment := b]; read hart_state;
        [run_hart_active 0]; tick PC; maybe bump minstret; and, on the tick
        branch, [tick_clock]).  What is left for the leaf is ONE [execute]
        fact, exactly as in the SC world.

    THE THREE THINGS THAT MAKE §3 WORK (all consequences of the two sides'
    shapes, recorded so they need not be rediscovered):

    (a) [wp_winstr] demands the [exec] fact at [wflat_st σ] for the state the
        WEAK machine holds, so the [minstret_increment] pre-write is INSIDE
        the run: the caller's [execute] fact is instantiated at
        [set_reg (wflat_st σ) (R_bool minstret_increment) b] with [b] a
        FUNNEL-chosen bool ([MinstretInv.exec_should_inc_minstret_Some]).
        That is why [b] is a parameter of the callback.  Every SC library
        execute lemma is stated at a generic state, so the extra [set_reg]
        costs the caller nothing.

    (b) The register bookkeeping is the funnel's job, not the leaf's:
        [minstret_inv] is opened at ⊤ and held across the [▷] (mirroring
        [MinstretInv.wp_exec_step_hart_active_inv]); [minstret_increment := b]
        is [reg_update]d BEFORE the interp reaches the callback; PC (and
        minstret, when [b]) are [reg_update]d after the [execute] fact is in
        hand; and on the TICK branch [clock_inv] is opened and its three
        cells scribbled, which is what [MinstretInv.wp_exec_step_clock] does
        one layer down in the SC tree.

    (c) The seam the leaf borrows is [WeakAcquire.wmstate_rest] minus the
        registers ([wmstate_norg] below): the funnel keeps [reg_interp] and
        the whole register tower, the leaf keeps the weak-memory conjuncts it
        must update.  [wlat_interp] is borrowed and handed straight back by a
        leaf that only READS memory.

    Only the M-MODE tier.  The S-mode/[sconf] tier is deliberately out of
    scope: its fetch goes through [SmodeCorePt.tlb_inv_pt_fetch], a page-table
    walk that consumes and returns [mstate_interp] as a bundle. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes SmodeCore.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakExec.
Require Import WeakView WeakVProp WeakFence WeakBridge WeakInstr.
Require Import WeakCert WeakAcquire.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE FETCH LEMMA, MADE PURE

    [fetch_flat_ok t pc r] is everything [exec (fetch tt) t = Some (r, t)]
    needs BEYOND the fetch configuration registers: the geometry, the RAM
    class of the four bytes at [pc], and what the memory holds there.

    ONE DEVIATION from [InstrBytes.instr_bytes], and it simplifies both this
    lemma and §2: the footprint is ALWAYS the four bytes of one 32-bit word
    [w] at [pc], with [r] saying how [w] is read ([F_Base w] itself, or
    [F_RVC] of its low half).  [instr_bytes] dispatches on
    [is_aligned_vaddr pc 4] in the [F_RVC] arm and owns only TWO bytes when
    [pc] is not 4-aligned; but the 2-aligned fetch reduction reads the low
    half of a word anyway ([nth_byte_subrange_lo]), and for kernel text the
    two extra bytes are free (they are the next instruction's first half).
    Dropping the dispatch removes an entire case from the resource, and —
    more importantly — it is what makes [winstr_pinned] able to produce
    [pinned_read] for the FULL four-byte window, which is exactly what
    [WeakInstr.wp_winstr] asks for. *)

Definition fetch_flat_ok (t : mstate) (pc : SailStdpp.Values.mword 64)
    (r : FetchResult) : Prop :=
  is_aligned_vaddr (Virtaddr pc) 2 = true /\
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) /\
  exists w : SailStdpp.Values.mword 32,
    (match r with
     | F_Base w' => w' = w /\ isRVC (subrange_vec_dec w 15 0) = false
     | F_RVC h   => subrange_vec_dec w 15 0 = h /\ isRVC h = true
     | _         => False
     end) /\
    (forall j : nat, (j < 4)%nat -> t.(mem) !! pa_add pc j = Some (nth_byte w j)).

(** Only the MEMORY of [t] is looked at, so the predicate transfers along any
    register-only state change — which is how the funnel moves it past the
    [minstret_increment] pre-write. *)
Lemma fetch_flat_ok_mem (t t' : mstate) pc r :
  t'.(mem) = t.(mem) -> fetch_flat_ok t pc r -> fetch_flat_ok t' pc r.
Proof.
  intros Hm (H2 & Hram & w & Hr & Hb). split; [exact H2|]. split; [exact Hram|].
  exists w. split; [exact Hr|]. intros j Hj. rewrite Hm. exact (Hb j Hj).
Qed.

Lemma exec_fetch_flat (t : mstate) (pc : SailStdpp.Values.mword 64)
    (r : FetchResult) :
  pmp_allows_all (register_lookup pmpcfg_n t.(sregs)) ->
  pma_allows_all (register_lookup pma_regions t.(sregs)) ->
  eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
  register_lookup PC t.(sregs) = pc ->
  register_lookup cur_privilege t.(sregs) = Machine ->
  register_lookup htif_tohost_base t.(sregs) = None ->
  fetch_flat_ok t pc r ->
  exec (fetch tt) t = Some (r, t).
Proof.
  intros Hpmp Hpma HmisaC Lpc Lpriv Lhtif (H2al & Hram & w & Hr & Hbytes).
  (* the four RAM facts, at the [fetch_pa]-spelled addresses the reductions use *)
  assert (Hram0 : addr_is_ram (fetch_pa pc)).
  { rewrite fetch_pa_id. rewrite <- (RiscvExtras.pa_add_0 pc). apply Hram. lia. }
  assert (Hram3 : addr_is_ram (pa_add (fetch_pa pc) 3)).
  { rewrite fetch_pa_id. apply Hram. lia. }
  assert (Hram1 : addr_is_ram (pa_add (fetch_pa pc) 1)).
  { rewrite fetch_pa_id. apply Hram. lia. }
  assert (Hbf : forall j : nat, (N.of_nat j < 4)%N ->
            t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)).
  { intros j Hj. rewrite fetch_pa_id. apply Hbytes. lia. }
  pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
  pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
  destruct r as [e | w' | h | erx]; [ destruct Hr | | | destruct Hr ].
  - (* F_Base w' : w' = w, not compressed *)
    destruct Hr as [<- HnotRVC].
    destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
    + (* 4-aligned: one 4-byte read *)
      destruct (pma_all_ram Hpma (fetch_pa pc) 4
                 (pma_access_ram _ _ _ Hram0 Hram3
                    (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
        as (region & Hmatch & Hexec0 & _ & _).
      exact (exec_fetch_done pc region w' t Lpc Lpriv Hpmp Hmatch Hexec0
               (within_clint_false (fetch_pa pc) 4 t Hnc ltac:(lia))
               (within_sig_false  (fetch_pa pc) 4 t Hns ltac:(lia))
               (within_htif_false (fetch_pa pc) 4 t Lhtif)
               (addr_is_ram_not_dev _ Hram0) Hbf Hal HnotRVC).
    + (* 2-aligned, not 4-aligned: two 2-byte reads at pc and pc+2 *)
      destruct (InstrBytes.align2_not4_facts pc H2al Hal)
        as (Halignl & Hbit0 & Hbit1).
      pose proof (InstrBytes.align2_plus2 pc H2al) as Halignh.
      assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                pa_add (fetch_pa (add_vec_int pc 2)) j
                  = pa_add (fetch_pa pc) (2 + j)).
      { intros j _. rewrite !fetch_pa_id. unfold pa_add.
        rewrite InstrBytes.avi_assoc. f_equal. lia. }
      assert (Hoff : fetch_pa (add_vec_int pc 2) = pa_add (fetch_pa pc) 2).
      { specialize (Haddr 0%nat ltac:(lia)).
        rewrite RiscvExtras.pa_add_0 in Haddr. exact Haddr. }
      assert (Hramh : addr_is_ram (fetch_pa (add_vec_int pc 2))).
      { rewrite Hoff fetch_pa_id. apply Hram. lia. }
      assert (Hramh1 : addr_is_ram (pa_add (fetch_pa (add_vec_int pc 2)) 1)).
      { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat.
        exact Hram3. }
      pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch.
      pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
      destruct (pma_all_ram Hpma (fetch_pa pc) 2
                 (pma_access_ram _ _ _ Hram0 Hram3
                    (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
        as (regl & Hml & Hxl & _ & _).
      destruct (pma_all_ram Hpma (fetch_pa (add_vec_int pc 2)) 2
                 (pma_access_ram _ _ _ Hramh Hramh1
                    (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
        as (regh & Hmh & Hxh & _ & _).
      assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
                t.(mem) !! (pa_add (fetch_pa pc) j)
                  = Some (nth_byte (subrange_vec_dec w' 15 0 : SailStdpp.Values.mword 16) j)).
      { intros j Hj. rewrite InstrBytes.nth_byte_subrange_lo; [|exact Hj].
        apply Hbf. lia. }
      assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
                t.(mem) !! (pa_add (fetch_pa (add_vec_int pc 2)) j)
                  = Some (nth_byte (subrange_vec_dec w' 31 16 : SailStdpp.Values.mword 16) j)).
      { intros j Hj. rewrite InstrBytes.nth_byte_subrange_hi; [|exact Hj].
        rewrite (Haddr j Hj). apply Hbf. lia. }
      exact (exec_fetch_F_Base_2 pc regl regh w' t Lpc Lpriv Hpmp Hml Hmh
               Halignl Halignh Hxl Hxh
               (within_clint_false (fetch_pa pc) 2 t Hnc ltac:(lia))
               (within_sig_false  (fetch_pa pc) 2 t Hns ltac:(lia))
               (within_htif_false (fetch_pa pc) 2 t Lhtif)
               (within_clint_false (fetch_pa (add_vec_int pc 2)) 2 t Hnch ltac:(lia))
               (within_sig_false  (fetch_pa (add_vec_int pc 2)) 2 t Hnsh ltac:(lia))
               (within_htif_false (fetch_pa (add_vec_int pc 2)) 2 t Lhtif)
               (addr_is_ram_not_dev _ Hram0) (addr_is_ram_not_dev _ Hramh)
               Hbl Hbh Hbit0 Hbit1 Hal HmisaC HnotRVC
               (InstrBytes.concat_subranges_id w')).
  - (* F_RVC h : h is the low half of w *)
    destruct Hr as [Hsub HisRVC].
    destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
    + (* 4-aligned: whole word read, result is its low half *)
      destruct (pma_all_ram Hpma (fetch_pa pc) 4
                 (pma_access_ram _ _ _ Hram0 Hram3
                    (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
        as (region & Hmatch & Hexec0 & _ & _).
      assert (HisRVC' : isRVC (subrange_vec_dec w 15 0) = true)
        by (rewrite Hsub; exact HisRVC).
      rewrite <- Hsub.
      exact (exec_fetch_RVC_4 pc region w t Lpc Lpriv Hpmp Hmatch Hexec0
               (within_clint_false (fetch_pa pc) 4 t Hnc ltac:(lia))
               (within_sig_false  (fetch_pa pc) 4 t Hns ltac:(lia))
               (within_htif_false (fetch_pa pc) 4 t Lhtif)
               (addr_is_ram_not_dev _ Hram0) Hbf Hal HisRVC').
    + (* 2-aligned, not 4-aligned: two-byte read of [h] *)
      destruct (InstrBytes.align2_not4_facts pc H2al Hal)
        as (Halign & Hbit0 & Hbit1).
      destruct (pma_all_ram Hpma (fetch_pa pc) 2
                 (pma_access_ram _ _ _ Hram0 Hram1
                    (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
        as (region & Hmatch & Hexec0 & _ & _).
      assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
                t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte h j)).
      { intros j Hj. rewrite <- Hsub.
        rewrite InstrBytes.nth_byte_subrange_lo; [|exact Hj]. apply Hbf. lia. }
      exact (exec_fetch_RVC_2 pc region h t Lpc Lpriv Hpmp Hmatch Halign Hexec0
               (within_clint_false (fetch_pa pc) 2 t Hnc ltac:(lia))
               (within_sig_false  (fetch_pa pc) 2 t Hns ltac:(lia))
               (within_htif_false (fetch_pa pc) 2 t Lhtif)
               (addr_is_ram_not_dev _ Hram0) Hbh Hbit0 Hbit1 Hal HmisaC HisRVC).
Qed.

(* ====================================================================== *)
(** ** 2. THE WEAK INSTRUCTION RESOURCE

    [InstrBytes.instr] cannot be reused: its [instr_bytes] component is [↦ₓ]
    gen_heap ownership and its decode field is a wand taking [mstate_interp].
    [winstr] is the twin, and the two differences are exactly those two:

      - the bytes are [WeakInstr.wkernel_text]'s spelling
        ([wlat_pointsto (pa_z a) DfracDiscarded 0 b], an [iProp] — OBJECTIVE
        and PERSISTENT, so a decode fact derived once is usable at every hart
        and after every step);
      - the decode field is [InstrBytes.instr]'s VERBATIM, with the
        [mstate_interp σ -∗] wrapper stripped, [σ] universally quantified as a
        plain [t : mstate] and the conclusion a pure [Prop].  Nothing in it
        ever needed resources, which is why the existing decode libraries'
        facts are reusable here WITHOUT restatement. *)

Section winstr.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition winstr_bytes (pc : SailStdpp.Values.mword 64) (r : FetchResult)
      : iProp Σ :=
    (⌜is_aligned_vaddr (Virtaddr pc) 2 = true⌝ ∗
     ⌜acc_wf pc 4⌝ ∗
     ⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝ ∗
     ∃ w : SailStdpp.Values.mword 32,
       ⌜match r with
        | F_Base w' => w' = w /\ isRVC (subrange_vec_dec w 15 0) = false
        | F_RVC h   => subrange_vec_dec w 15 0 = h /\ isRVC h = true
        | _         => False
        end⌝ ∗
       ([∗ list] j ∈ seq 0 4,
          wlat_pointsto (pa_z (pa_add pc j)) DfracDiscarded 0%nat
            (nth_byte w j)))%I.

  Global Instance winstr_bytes_persistent pc r : Persistent (winstr_bytes pc r).
  Proof. rewrite /winstr_bytes. apply _. Qed.

  Definition winstr (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) : iProp Σ :=
    (⌜is_lpad_instruction i = false⌝ ∗
     ∃ r : FetchResult,
       ⌜fetch_is_rvc r = is_rvc⌝ ∗
       winstr_bytes pc r ∗
       ⌜forall t : mstate,
          priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
          eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
          eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
          register_lookup misa t.(sregs) = MISA_C ->
          cfg_ok t ->
          if fetch_is_rvc r
          then exists i0 : instruction,
                 exec (decode_fetch r) t = Some (i0, t) /\
                 is_lpad_instruction i0 = false /\
                 (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s))
          else exec (decode_fetch r) t = Some (i, t)⌝)%I.

  Global Instance winstr_persistent pc is_rvc i : Persistent (winstr pc is_rvc i).
  Proof. rewrite /winstr. apply _. Qed.

  (** *** 2a. THE CONSTRUCTORS a decode file uses. *)

  (** The bytes, off the objective kernel-text resource.

      NOTE THE PREMISE ORDER: the per-byte lookup fact is a [⌜⌝] premise
      AFTER [wkernel_text bs], not a [Prop] premise before it.  A [gmap
      Arch.pa _] binder in a file that imports [SailStdpp.Base] elaborates
      against a DIFFERENT [Countable] instance from the one [WeakInstr] used
      (durable notes, "binder-position instance trap"), and the two print
      identically; letting [wkernel_text bs] elaborate FIRST pins the right
      one. *)
  Lemma winstr_bytes_of_text bs
      (pc : SailStdpp.Values.mword 64) (r : FetchResult)
      (w : SailStdpp.Values.mword 32) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    acc_wf pc 4 ->
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
    (match r with
     | F_Base w' => w' = w /\ isRVC (subrange_vec_dec w 15 0) = false
     | F_RVC h   => subrange_vec_dec w 15 0 = h /\ isRVC h = true
     | _         => False
     end) ->
    wkernel_text bs -∗
    ⌜forall j : nat, (j < 4)%nat -> bs !! pa_add pc j = Some (nth_byte w j)⌝ -∗
    winstr_bytes pc r.
  Proof.
    intros H2 Hacc Hram Hr. iIntros "#Ht %Hlk".
    rewrite /winstr_bytes.
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    iExists w. iSplitR; [by iPureIntro|].
    rewrite /wkernel_text.
    pose proof (Hlk 0%nat ltac:(lia)) as Hl0.
    pose proof (Hlk 1%nat ltac:(lia)) as Hl1.
    pose proof (Hlk 2%nat ltac:(lia)) as Hl2.
    pose proof (Hlk 3%nat ltac:(lia)) as Hl3.
    iDestruct (big_sepM_lookup _ _ _ _ Hl0 with "Ht") as "#H0".
    iDestruct (big_sepM_lookup _ _ _ _ Hl1 with "Ht") as "#H1".
    iDestruct (big_sepM_lookup _ _ _ _ Hl2 with "Ht") as "#H2".
    iDestruct (big_sepM_lookup _ _ _ _ Hl3 with "Ht") as "#H3".
    cbn [seq]. iFrame "H0 H1 H2 H3". done.
  Qed.

  (** ... and the whole resource, from the bytes plus the PURE decode fact. *)
  Lemma winstr_intro (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) (r : FetchResult) :
    is_lpad_instruction i = false ->
    fetch_is_rvc r = is_rvc ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       if fetch_is_rvc r
       then exists i0 : instruction,
              exec (decode_fetch r) t = Some (i0, t) /\
              is_lpad_instruction i0 = false /\
              (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s))
       else exec (decode_fetch r) t = Some (i, t)) ->
    winstr_bytes pc r -∗ winstr pc is_rvc i.
  Proof.
    intros Hlpad Hrvc Hdec. iIntros "#Hb". rewrite /winstr.
    iSplitR; [by iPureIntro|]. iExists r.
    iSplitR; [by iPureIntro|]. iFrame "Hb". by iPureIntro.
  Qed.

  (** *** 2b. THE ELIMINATORS the funnel uses. *)

  Lemma winstr_bytes_acc_wf pc r : winstr_bytes pc r ⊢ ⌜acc_wf pc 4⌝.
  Proof. iIntros "(_ & % & _)". by iPureIntro. Qed.

  (** The per-byte element determines the flat byte AND its timestamp; the
      two conclusions below are exactly the two things a fetch needs. *)
  Lemma winstr_bytes_lookup (σ : wmstate) pc r :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc r -∗
    ⌜(forall j : nat, (j < 4)%nat -> latest_ts (wm_log σ) (pa_z (pa_add pc j)) = 0%nat)
     /\ fetch_flat_ok (wflat_st σ) pc r⌝.
  Proof.
    intros Hwf. iIntros "Hi #Hb".
    iDestruct "Hb" as "(%H2 & %Hacc & %Hram & Hw)".
    iDestruct "Hw" as (w) "[%Hr Hbytes]".
    iAssert (⌜forall j : nat, (j < 4)%nat ->
               wflat (wm_img σ) (wm_log σ) !! pa_add pc j = Some (nth_byte w j)
               /\ latest_ts (wm_log σ) (pa_z (pa_add pc j)) = 0%nat⌝)%I as %Hall.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iApply (wpt_img_flat_lookup σ (pa_add pc j) DfracDiscarded (nth_byte w j)
                Hwf with "Hi Hbj"). }
    iPureIntro. split.
    - intros j Hj. exact (proj2 (Hall j Hj)).
    - split; [exact H2|]. split; [exact Hram|].
      exists w. split; [exact Hr|].
      intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  (** The FLAT half: [fetch_flat_ok] at the flat projection, which is what §1
      turns into the fetch reduction. *)
  Lemma winstr_flat (σ : wmstate) pc r :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc r -∗
    ⌜fetch_flat_ok (wflat_st σ) pc r⌝.
  Proof.
    intros Hwf. iIntros "Hi #Hb".
    iDestruct (winstr_bytes_lookup σ pc r Hwf with "Hi Hb") as %[_ Hok].
    by iPureIntro.
  Qed.

  (** The PINNED half — [WeakInstr.wp_winstr]'s text obligation, over the
      FULL four-byte window (which is why §1/§2 keep four bytes even in the
      compressed arm).  Text is unwritten this era, so it is FREE
      ([WeakBridge.pinned_read_unwritten]). *)
  Lemma winstr_pinned (σ : wmstate) pc r :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc r -∗
    ⌜forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pc j)⌝.
  Proof.
    intros Hwf. iIntros "Hi #Hb".
    iDestruct (winstr_bytes_acc_wf with "Hb") as %Hacc.
    iDestruct (winstr_bytes_lookup σ pc r Hwf with "Hi Hb") as %[Hts _].
    iPureIntro. intros j Hj. apply pinned_read_unwritten.
    rewrite -(acc_wf_byte pc 4 j Hacc ltac:(lia)). exact (Hts j Hj).
  Qed.

End winstr.

(* ====================================================================== *)
(** ** 3. THE FUNNEL

    [wwp_instr] is the weak [InstrBytes.wp_instr].  It does the ENTIRE
    [riscv_step] wrapper, so what the leaf owes is what an SC leaf owes today:
    ONE [execute] fact.

    The two SEAMS.  [WeakAcquire.wmstate_rest] peels the latest-write
    authority off [WeakGhost.wmstate_interp]; this file peels one more
    conjunct — [reg_interp] — off [wmstate_rest], because the whole point of
    the funnel is that IT owns the register bookkeeping.  [wmstate_norg] is
    what is left, and it is what the leaf carries across the step. *)

(** THE FUNNEL'S REGISTER READS, PACKAGED — everything [wwp_instr] takes off
    the [mmode_config] / [hw_config] bundle it is handed, restated at [σ]'s
    OWN register file.

    Handing this to the callback is what spares every leaf a SECOND
    [mmode_config] split and nine [reg_valid_dq]s plus their transports past
    the [minstret_increment] pre-write (≈ 40 lines, measured on the [ld]
    leaf), and it is what lets a leaf discharge the decode bridge's
    [agree_on D] premise AT [σ]: the premise itself still has to be stated
    ∀-over-register-files in the leaf's own statement (the leaf is stated
    before [σ] exists — [wwp_cb] quantifies over it), but instantiating it is
    now three [exact]s off this record rather than three register reads.

    The list is exactly what [WeakFetchEff.wP_eff_of_leaf_base] and a leaf's
    [execute] lemma consume; [misa] and [mseccfg] are pinned to their WHOLE
    values because that is what the concrete-state decode bridge compares
    (durable notes: a read-frame/agreement bridge is whole-value by
    construction). *)
Definition wcfg_regs (σ : wmstate) (pmpcfg0 : type_of_register pmpcfg_n)
    : Prop :=
  register_lookup cur_privilege (wm_regs σ) = Machine
  /\ register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt
  /\ register_lookup misa (wm_regs σ) = MISA_C
  /\ register_lookup mseccfg (wm_regs σ) = mword_of_int 0
  /\ register_lookup pmpcfg_n (wm_regs σ) = pmpcfg0
  /\ pma_allows_all (register_lookup pma_regions (wm_regs σ))
  /\ register_lookup htif_tohost_base (wm_regs σ) = None
  /\ eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true
  /\ eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
       = false
  /\ eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (wm_regs σ))) ('b"1")
       = false
  /\ pmm_mode_backwards
       (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ))) = PMM_Disabled
  /\ eq_vec (register_lookup elp (wm_regs σ))
       (landing_pad_bits_backwards LP_EXPECTED) = false.

(** The decode bridge's config precondition, at the flat state — the M-mode
    arm of [RiscvFetchExec.cfg_ok], read straight off the record. *)
Lemma wcfg_regs_cfg_ok σ pmpcfg0 :
  wcfg_regs σ pmpcfg0 -> cfg_ok (wflat_st σ).
Proof.
  intros (Hpriv & _ & _ & Hsec & _). left. rewrite wflat_st_regs.
  exact (conj Hpriv Hsec).
Qed.

Section funnel.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** [wmstate_rest] minus the registers. *)
  Definition wmstate_norg (σ : wmstate) : iProp Σ :=
    (⌜ws_bounded σ.(wm_ws) (length σ.(wm_log))⌝ ∗
     ⌜wlog_wf σ.(wm_log)⌝ ∗
     dev_interp σ.(wm_dev) ∗
     wlog_auth σ.(wm_log) ∗
     wws_auth cpu_id σ.(wm_ws))%I.

  Lemma wmstate_rest_split σ :
    wmstate_rest σ ⊣⊢ reg_interp (wm_regs σ) ∗ wmstate_norg σ.
  Proof.
    rewrite /wmstate_rest /wmstate_norg. iSplit.
    - iIntros "(%Hb & %Hw & Hr & Hd & Hl & Hws)". iFrame "Hr".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
    - iIntros "(Hr & %Hb & %Hw & Hd & Hl & Hws)".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  Lemma wmstate_interp_split_regs σ :
    wmstate_interp σ ⊣⊢
      reg_interp (wm_regs σ) ∗ wlat_interp (wm_img σ) (wm_log σ) ∗ wmstate_norg σ.
  Proof.
    rewrite wmstate_interp_split wmstate_rest_split. iSplit.
    - iIntros "(Hlat & Hr & Hn)". iFrame.
    - iIntros "(Hr & Hlat & Hn)". iFrame.
  Qed.

  Lemma wmstate_norg_facts σ :
    wmstate_norg σ -∗
    ⌜ws_bounded σ.(wm_ws) (length σ.(wm_log)) /\ wlog_wf σ.(wm_log)⌝.
  Proof. iIntros "(% & % & _)". by iPureIntro. Qed.

  (** The one register-tower fact the whole wrapper needs: the
      [minstret_increment] pre-write is invisible to every OTHER register. *)
  Lemma set_mi_lookup (r : register) (s : mstate) (b : bool) :
    register_beq r (R_bool minstret_increment) = false ->
    register_lookup r (set_reg s (R_bool minstret_increment) b).(sregs)
      = register_lookup r s.(sregs).
  Proof. intros H. rewrite sregs_set_reg. by apply irrelevant_register_set. Qed.

  (** THE LEAF'S OBLIGATION, named — [wwp_instr]'s last premise.  Read it as
      [InstrBytes.wp_instr]'s callback with three changes and nothing else:

        - [b] is the funnel-chosen [minstret_increment] flag, and the caller's
          [execute] fact is stated at [wflat_st σ] with that flag ALREADY
          written (every SC library execute lemma is stated at a generic
          state, so this costs the caller nothing);
        - what is handed over instead of [mstate_interp σ] is the SPLIT weak
          interpretation: the latest-write authority, the (already-updated)
          registers, and [wmstate_norg] — plus [⌜wcfg_regs σ pmpcfg0⌝], the
          config reads the funnel has just done, so the leaf need not do them
          again (and need not keep a second half of [mmode_config] to do them
          with);
        - the continuation runs after the step, at a successor [σ'] described
          by [WeakInstr.wstep_post] over the SC successor [t], and gives back
          the config bundle, the stepped PC, and the weak conjuncts at [σ'].

      THE DEVICE FRAME, [⌜mdev t = mdev s_exec⌝], IS HANDED OVER BECAUSE ONLY
      THE FUNNEL KNOWS IT.  [wstep_post] says [wm_dev σ' = mdev t] and the
      leaf must give back [dev_interp (wm_dev σ')] — an authoritative half it
      cannot move without its fragment — so it needs to know what [mdev t] IS.
      [t] is built by the funnel out of [s_exec] by REGISTER writes only (the
      PC tick, the [minstret] bump, and on the tick branch [tick_clock]'s
      three cells), so the fact is free here and unobtainable there: without
      it a leaf has to replay the entire [riscv_step] a second time at the
      flat state and identify the two successors by determinism of [exec]
      (116 lines, ×50 over the sweep — the batch-2 interface defect).
      It is stated against [mdev s_exec], not against [wm_dev σ]: the leaf
      owns the [execute] fact, so it knows [mdev s_exec] outright (one line
      for a RAM instruction, whose [execute] moves no device), and a future
      MMIO leaf — whose [execute] DOES move [mdev] — can still use it. *)
  Definition wwp_cb Φ (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) (pmpcfg0 : type_of_register pmpcfg_n) (dq : dfrac)
      (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) : iProp Σ :=
    (∀ (σ : wmstate) (b : bool),
       ⌜register_lookup PC (wm_regs σ) = pc⌝ -∗
       ⌜wcfg_regs σ pmpcfg0⌝ -∗
       wlat_interp (wm_img σ) (wm_log σ) -∗
       reg_interp (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) b)) -∗
       wmstate_norg σ
       ={⊤ ∖ ↑minstretN, ∅}=∗
         (⌜P σ⌝ ∗
          ∃ s_exec : mstate,
            ⌜exec (execute i)
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               = Some (RETIRE_SUCCESS, s_exec)⌝ ∗
            reg_interp (sregs s_exec) ∗
            ▷ (∀ (tick : bool) (σ' : wmstate) (t : mstate),
                 ⌜exec (riscv_step tick) (wflat_st σ) = Some (tt, t)⌝ -∗
                 ⌜mdev t = mdev s_exec⌝ -∗
                 ⌜wstep_post σ σ' t⌝ -∗
                 ⌜Q σ σ'⌝ -∗
                 mmode_config dq -∗
                 pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
                 PC ↦ᵣ (register_lookup nextPC (sregs s_exec)) -∗
                 (|={∅, ⊤ ∖ ↑minstretN}=>
                    (wlat_interp (wm_img σ') (wm_log σ') ∗
                     wmstate_norg σ' ∗
                     WP (Loop : expr weak_riscv_lang) {{ Φ }})))))%I.

  Lemma wwp_instr Φ (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) (pmpcfg0 : type_of_register pmpcfg_n) {dq : dfrac}
      (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) :
    gen_id = 0%nat ->
    acc_wf pc 4 ->
    pmp_allows_all pmpcfg0 ->
    wstep_cert (fin_to_nat cpu_id) pc P Q ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    winstr pc is_rvc i -∗
    wwp_cb Φ pc is_rvc i pmpcfg0 dq P Q -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    rewrite /wwp_cb.
    iIntros (Hgid Haccpc Hpmp Hcert) "Hmm Hpmpc Hpc Hinstr H".
    iDestruct "Hmm" as "(#Hhw & #Hmiv0 & Hhs & Hpriv & Hmst0)".
    iDestruct "Hmst0" as (mstatus0) "(Hmstatus & %HmIE & %HMPRV & %HSXL & %HKF)".
    iAssert (minstret_inv) as "#Hmiv"; [iExact "Hmiv0"|].
    iDestruct "Hmiv0" as "#(Hinv & Hcinv & Hgc)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hinstr]".
    iDestruct "Hinstr" as (r) "(%Hrvc & #Hb & %Hdec)".
    iApply (wp_winstr Φ pc P Q Hgid Haccpc Hcert).
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split_regs σ with "Hσ") as "(Hreg & Hlat & Hnorg)".
    iDestruct (wmstate_norg_facts with "Hnorg") as %[Hbnd Hwf].
    (* open the minstret invariant: ⊤ -> ⊤ ∖ ↑minstretN, held across the ▷ *)
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (mst0 mi0) "[Hmst Hmi]".
    (* every register the wrapper / fetch / decode reads, at [wm_regs σ] *)
    iDestruct (reg_valid    with "Hreg Hpc")       as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")     as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")     as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")     as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lmseccfg.
    iDestruct (reg_valid_dq with "Hreg Hmstatus")  as %Lmstatus.
    iDestruct (reg_valid_dq with "Hreg Help")      as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hhs")       as %Lhs.
    (* the same reads, packaged for the leaf *)
    assert (Hcfg : wcfg_regs σ pmpcfg0).
    { rewrite /wcfg_regs Lpriv Lhs Lmisa Lmseccfg Lpmpc Lpma Lhtif Lmstatus
              Lelp.
      split_and!;
        [ reflexivity | reflexivity | exact Hmisa_val0 | exact Hmseccfg_val0
        | reflexivity | exact Hpma_all | reflexivity | exact HmisaS
        | exact HmIE | exact HMPRV | exact Hseccfg1 | exact Help_np ]. }
    (* the two facts the weak fetch needs, off the text elements *)
    iDestruct (winstr_flat σ pc r Hwf with "Hlat Hb") as %Hfok.
    iDestruct (winstr_pinned σ pc r Hwf with "Hlat Hb") as %Hpin.
    (* the funnel's own choice of the increment flag *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege (wflat_st σ).(sregs)) (wflat_st σ))
      as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi")
      as "[Hreg Hmi]".
    (* ---- the state the run really starts from ---- *)
    assert (Lpriv_a : register_lookup cur_privilege
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = Machine).
    { rewrite (set_mi_lookup cur_privilege _ b eq_refl) wflat_st_regs. exact Lpriv. }
    assert (Lpc_a : register_lookup PC
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = pc).
    { rewrite (set_mi_lookup PC _ b eq_refl) wflat_st_regs. exact Lpc. }
    assert (Lmisa_a : register_lookup misa
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = misa0).
    { rewrite (set_mi_lookup misa _ b eq_refl) wflat_st_regs. exact Lmisa. }
    assert (Lmstatus_a : register_lookup mstatus
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = mstatus0).
    { rewrite (set_mi_lookup mstatus _ b eq_refl) wflat_st_regs. exact Lmstatus. }
    assert (Lelp_a : register_lookup elp
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = elp0).
    { rewrite (set_mi_lookup elp _ b eq_refl) wflat_st_regs. exact Lelp. }
    assert (Lmseccfg_a : register_lookup mseccfg
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = mseccfg0).
    { rewrite (set_mi_lookup mseccfg _ b eq_refl) wflat_st_regs. exact Lmseccfg. }
    assert (Lhs_a : register_lookup hart_state
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = HART_ACTIVE tt).
    { rewrite (set_mi_lookup hart_state _ b eq_refl) wflat_st_regs. exact Lhs. }
    (* fetch, at the post-write state (only the MEMORY matters, and it moved not) *)
    assert (Hfetch : exec (fetch tt)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (r, set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply (exec_fetch_flat _ pc r).
      - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl) wflat_st_regs Lpmpc. exact Hpmp.
      - rewrite (set_mi_lookup pma_regions _ b eq_refl) wflat_st_regs Lpma.
        exact Hpma_all.
      - rewrite Lmisa_a. exact HmisaC.
      - exact Lpc_a.
      - exact Lpriv_a.
      - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl) wflat_st_regs.
        exact Lhtif.
      - apply (fetch_flat_ok_mem (wflat_st σ)); [apply mem_set_reg | exact Hfok]. }
    (* the interrupt dispatch is a no-op: misa.S set, mstatus.MIE clear *)
    assert (Hdisp : exec (dispatchInterrupt Machine)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (None, set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none _ _
               (exec_currentlyEnabled_S
                  (set_reg (wflat_st σ) (R_bool minstret_increment) b))).
      - rewrite Lmisa_a. exact HmisaS.
      - rewrite Lmstatus_a. exact HmIE. }
    assert (Help_a : eq_vec (register_lookup elp
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { rewrite Lelp_a. exact Help_np. }
    assert (HZca_a : exec (currentlyEnabled Ext_Zca)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (true, set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa_a. exact HmisaC. }
    (* the decode obligation, discharged from the PURE field of [winstr] *)
    specialize (Hdec (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                  ltac:(rewrite Lpriv_a; reflexivity)
                  ltac:(rewrite Lmisa_a; exact HmisaC)
                  ltac:(rewrite Lmisa_a; exact HmisaA)
                  ltac:(rewrite Lmisa_a; exact Hmisa_val0)
                  ltac:(unfold cfg_ok; left; split;
                        [ exact Lpriv_a
                        | rewrite Lmseccfg_a; exact Hmseccfg_val0 ])).
    (* ---- the leaf's obligation ---- *)
    iMod ("H" $! σ b with "[%] [%] Hlat Hreg Hnorg") as "(%HP & Hcb)";
      [exact Lpc | exact Hcfg |].
    iDestruct "Hcb" as (s_exec) "(%Hexec & Hreg & Hcont)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs_e.
    iDestruct (reg_valid    with "Hreg Hmi") as %Lmi_e.
    (* ---- the [run_hart_active] progress fact, by width ---- *)
    pose proof Hfok as Hfok'.
    destruct Hfok' as (_ & _ & wfw & Hrm & _).
    assert (Hha : exec (run_hart_active 0)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (Step_Execute (RETIRE_SUCCESS,
                        (match r with
                         | F_Base w => zero_extend' 32 w
                         | F_RVC h  => zero_extend' 32 h
                         | _ => mword_of_int 0
                         end : SailStdpp.Values.mword 32)), s_exec)).
    { destruct r as [e | w | h | erx]; [destruct Hrm | | | destruct Hrm].
      - (* F_Base: direct decode, one execute *)
        cbn [fetch_is_rvc] in Hrvc, Hdec. subst is_rvc.
        exact (exec_hart_active_progress_base_gen Machine
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 s_exec w i pc RETIRE_SUCCESS
                 Lpriv_a Hdisp Hfetch Hdec
                 Help_a Hnlpad Lpc_a Hexec I).
      - (* F_RVC: indirect decode through the state-generic [ExecuteAs] *)
        cbn [fetch_is_rvc] in Hrvc, Hdec. subst is_rvc.
        destruct Hdec as (i0 & Hdec0 & Hnlpad0 & Hexp).
        exact (exec_hart_active_progress_RVC_gen Machine
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 s_exec h i0 i pc RETIRE_SUCCESS
                 Lpriv_a Hdisp Hfetch Hdec0
                 Help_a Lpc_a HZca_a (Hexp _) Hexec). }
    pose proof (exec_riscv_step_hart_active (wflat_st σ) s_exec _ b
                  Hsi Lhs_a Hha Lhs_e Lmi_e) as Hstep0.
    (* ---- the wrapper's own register writes: tick PC, maybe bump minstret ---- *)
    iAssert (|==> ∃ t0 : mstate,
                ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
                ⌜mdev t0 = mdev s_exec⌝ ∗
                reg_interp (sregs t0) ∗ minstret_inv_body ∗
                PC ↦ᵣ (register_lookup nextPC (sregs s_exec)))%I
      with "[Hreg Hmst Hmi Hpc]" as ">Hw".
    { iMod (reg_update _ PC _ (register_lookup nextPC (sregs s_exec))
              with "Hreg Hpc") as "[Hreg Hpc]".
      destruct b.
      - iMod (reg_update _ minstret _
                (add_vec_int (register_lookup minstret
                   (sregs (set_reg s_exec PC
                             (register_lookup nextPC (sregs s_exec))))) 1)
                with "Hreg Hmst") as "[Hreg Hmst]".
        iModIntro. iExists _. iSplitR; [iPureIntro; exact Hstep0|].
        iSplitR; [iPureIntro; by rewrite !mdev_set_reg|].
        iFrame "Hreg Hpc". iExists _, true. iFrame.
      - iModIntro. iExists _. iSplitR; [iPureIntro; exact Hstep0|].
        iSplitR; [iPureIntro; by rewrite !mdev_set_reg|].
        iFrame "Hreg Hpc". iExists _, false. iFrame. }
    iDestruct "Hw" as (t0) "(%Hst0 & %Hdev0 & Hreg & Hbody & Hpc)".
    destruct (exec_tick_clock t0) as (c' & ti' & p' & Htick).
    pose proof (exec_riscv_step_tick _ _ _ Hst0 Htick) as Hst1.
    (* ---- hand the two successors to [wp_winstr] ---- *)
    iModIntro.
    iSplitR; [iPureIntro; exact Lpc|].
    iSplitR; [iPureIntro; exact Hpin|].
    iSplitR; [iPureIntro; exact HP|].
    iExists t0, (set_reg (set_reg (set_reg t0 mcycle c') mtime ti') mip p').
    iSplitR; [iPureIntro; exact Hst0|].
    iSplitR; [iPureIntro; exact Hst1|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    iSpecialize ("Hcont" $! tick σ' (if tick then
        set_reg (set_reg (set_reg t0 mcycle c') mtime ti') mip p' else t0)).
    iSpecialize ("Hcont" with "[%]");
      [destruct tick; [exact Hst1 | exact Hst0]|].
    iSpecialize ("Hcont" with "[%]");
      [destruct tick; [rewrite !mdev_set_reg; exact Hdev0 | exact Hdev0]|].
    iSpecialize ("Hcont" with "[%]"); [exact Hpost|].
    iSpecialize ("Hcont" with "[%]"); [exact HQ|].
    iSpecialize ("Hcont" with "[Hhs Hpriv Hmstatus]").
    { iApply (mmode_config_rebuild dq mstatus0 HmIE HMPRV HSXL HKF
                with "Hhw Hmiv Hhs Hpriv Hmstatus"). }
    iSpecialize ("Hcont" with "Hpmpc").
    iSpecialize ("Hcont" with "Hpc").
    iMod "Hcont" as "(Hlat' & Hnorg' & HWP)".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct tick.
    - (* TICK: [tick_clock] wrote mcycle / mtime / mip, all owned by clock_inv *)
      iInv "Hcinv" as ">Hcb" "Hclosec".
      iDestruct "Hcb" as (c0 t0c p0) "(Hc & Ht & Hp)".
      iMod (reg_update _ mcycle _ c' with "Hreg Hc") as "[Hreg Hc]".
      iMod (reg_update _ mtime _ ti' with "Hreg Ht") as "[Hreg Ht]".
      iMod (reg_update _ mip _ p' with "Hreg Hp") as "[Hreg Hp]".
      iMod ("Hclosec" with "[Hc Ht Hp]") as "_".
      { iNext. iExists c', ti', p'. iFrame. }
      iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
      iModIntro. rewrite (wmstate_interp_split_regs σ'). iFrame "HWP Hlat' Hnorg'".
      rewrite Hregs. iExact "Hreg".
    - (* NO TICK: the registers are already those of [t0] *)
      iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
      iModIntro. rewrite (wmstate_interp_split_regs σ'). iFrame "HWP Hlat' Hnorg'".
      rewrite Hregs. iExact "Hreg".
  Qed.

End funnel.

(* ====================================================================== *)
(** ** 4. SMOKE TEST: the funnel composing with a certificate

    Not a theorem of record — the check that a leaf stated the way today's
    [InstrBytes.wp_instr]-consuming leaves are stated really does have a weak
    funnel to go through.  [WeakCert.wstep_cert_conf_none] discharges the
    certificate UNCONDITIONALLY for [P := WeakCert.wP_conf] and
    [Q := WeakInstr.wQ_none] (the shape of every non-sync instruction: no
    weak-memory effect to state), so what is left for the leaf is exactly:

      - [wP_conf σ] — the confined-witness obligation, i.e. a window [W] and
        ONE re-instantiation of its own SC library lemma at the restricted
        memory (porting guide §2: ~20–40 lines, no model reduction);
      - its ONE [execute] fact;
      - the weak-side bookkeeping of whatever memory it touched.

    Everything else — fetch, decode, the [try_step] wrapper, [minstret], the
    clock tick, and all the register plumbing — is gone. *)

Section smoke.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_instr_conf Φ (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) (pmpcfg0 : type_of_register pmpcfg_n) (dq : dfrac) :
    gen_id = 0%nat ->
    acc_wf pc 4 ->
    pmp_allows_all pmpcfg0 ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    winstr pc is_rvc i -∗
    wwp_cb Φ pc is_rvc i pmpcfg0 dq wP_conf wQ_none -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hacc Hpmp.
    exact (wwp_instr Φ pc is_rvc i pmpcfg0 (dq := dq) wP_conf wQ_none
             Hgid Hacc Hpmp (wstep_cert_conf_none (fin_to_nat cpu_id) pc)).
  Qed.

End smoke.
