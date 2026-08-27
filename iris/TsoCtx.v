(* TsoCtx.v -- THE CONTEXT SURFACE, REAL (TSO) INSTANTIATION.

   The TSO port's ownership interface Sigma
   ([claude-notes/projects/tso-port.md], legs M and C): every memory
   points-to fact is indexed by a CONTEXT -- a ghost identity for a thread
   of control -- and the ONLY ways a fact changes context are the exported
   transport laws.  UNTIL THE MACHINE FLIP the definitions below ignored
   the index under the seal; NOW ([claude-notes/projects/
   tso-machine-flip.md] §5) they are the TsoCtxTwin2 construction wired
   to the live machine ghosts ([TsoGhost.v] at [riscvEraGS]'s era names,
   over the Ztso semantics of [RiscvLang.mnode_step]):

     - [ctx_pointsto ξ a dq v] is mem_pointsto's body PLUS the byte's
       latest-write TIMESTAMP (a [ts_name] fragment at the fact's own
       dq) PLUS the clean/dirty BIT: clean = a persistent lower bound of
       ξ's own bound covering the timestamp; dirty = a fragment of ξ's
       own dirty set at (t, pa).
     - [own_context ξ] is THE TIE between the CPU's view and the context
       object: both of ξ's authorities (its bound, its dirty set), a
       stable view receipt of the AMBIENT hart dominating the bound
       ([view_lb (hart_agent cpu_id) K] with [B ≤ K] -- every clean fact
       of mine is visible on the hart I am running on), and the per-entry
       justification of the dirty set (mine-on-this-hart, or under the
       bound).
     - [ctx_parked ξ T]: the authorities with no hart tie; the bound IS
       the stamp (park raised it past every dirty entry).
     - [hart_view_lb K] = [view_lb] at the ambient hart: the persistent,
       monotone acquire receipt.
     - [ctx_dom ξ ξ'] carries HALF of ξ's authorities plus a bound-lb of
       ξ' dominating ξ's bound and dirty watermark -- statable with no
       machine state, which is what makes [CtxMorph]'s bare shape true
       as written.

   Every law below was first proven of the self-contained twin
   ([TsoCtxTwin2.v], kept as the discovery record); the twin lemma is
   named beside each.  The kit-facing gates at the bottom (the load
   gate, the view-receipt mint, the acquire-side domination mint) are
   what the leaf re-proofs against the Ztso machine consume.

   THE THREE RULINGS THIS FILE ENCODES (owner-ratified) are unchanged:

   1. [CurCtx] IS AMBIENT, LIKE [CpuId] AND [CurKtier]: a file binds its
      context once ([Context `{XI : CurCtx}]) and its spec text does not
      change.  There is deliberately NO default instance.

   2. THE CONTEXT RIDES IN [sie_cap_gpr]: the ambient kernel-execution
      bundle carries [own_context cur_ctx], so no proof threads a NEW
      separation-logic resource, and [wp_next]'s continuation re-anchors
      [CpuId] while cur_ctx STAYS.  [own_context] is what ties the
      context to the current CPU's view state -- now for real.

   3. NO CONTEXT-IRRELEVANCE ESCAPES: a lemma of the shape
      [ctx_pointsto ξ ⊣⊢ ctx_pointsto ξ'] is FALSE here and must never
      exist above the seal.  (The SC-era shim equivalences died with the
      SC bodies; TsoCtxShim.v now carries only the still-true mint.)

   THE SEAL IS STILL HERMETIC (the cutover-rehearsal sig-projection
   idiom): the five surface facts are Qed-opaque, each with a named
   [_unseal] equation.  The licensed unseal set grows from {this file's
   law proofs, TsoCtxShim} to include the BELOW-Σ kit re-proofs (the
   load/store leaves, the lock internals) -- they are the instantiation,
   not clients. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_var ghost_map mono_nat gen_heap.
(* SailStdpp.Base is deliberately ABSENT (the SC file imported it): it
   exports [Countable_mword]/[Decidable_eq_mword], which would make every
   [gmap]/[ghost_map] over [Arch.pa] in THIS file elaborate at the Sail
   key instances while [TsoGhost]'s classes carry stdpp's -- the
   riscvF_kmapGS trap, live.  [Values] alone does not export them. *)
Require Import SailStdpp.Values.
Require Import SailStdpp.Operators_mwords.  (* [uint]; exports no mword key instances *)
Require Import Riscv.rv64d_types Riscv.rv64d.   (* [is_aligned_paddr]/[Physaddr]: the word tower's alignment vocabulary *)
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.

(* ------------------------------------------------------------------ *)
(* The context identity and the ambient class                          *)
(* ------------------------------------------------------------------ *)

(* TWO GNAMES, BOTH THE CONTEXT'S OWN ([TsoCtxTwin2.CtxId] is the same
   record): the BOUND authority (one monotone nat -- clean facts'
   justification) and the DIRTY-SET authority (a ghost map keyed by
   (timestamp, byte)).  The identity carrying its own ghost names is
   what lets a token -- and hence every authority -- be minted wherever
   the identity can, with no global roster: the corrected construction's
   cornerstone. *)
Record CtxId := MkCtxId { ctx_bound_name : gname; ctx_dirty_name : gname }.
Add Printing Constructor CtxId.

Global Instance ctx_id_eq_dec : EqDecision CtxId.
Proof. solve_decision. Defined.
(* INHABITED IS LOAD-BEARING, not decoration: a [CtxId] existentially bound
   inside a ▷-guarded record (the parked context, SwtchCtx.valid_context_pre)
   can only have its later pushed inward by [bi.later_exist], which HOLDS
   ONLY OVER AN INHABITED DOMAIN.  Without this instance the resumer cannot
   open the record it is about to run. *)
Global Instance ctx_id_inhabited : Inhabited CtxId :=
  populate (MkCtxId inhabitant inhabitant).

Global Instance ctx_id_countable : Countable CtxId.
Proof.
  apply (inj_countable' (λ ξ, (ctx_bound_name ξ, ctx_dirty_name ξ))
           (λ p, MkCtxId p.1 p.2)).
  by intros [].
Qed.

(* Ambient, and -- unlike [CurKtier] -- WITHOUT a default instance; see
   ruling 1 above. *)
Class CurCtx := cur_ctx : CtxId.

(* ---------------------------------------------------------------------- *)
(* [pa_add] IS INJECTIVE IN ITS INDEX -- the kit needs it for exactly one   *)
(* thing (A6.16): a store's window has DISTINCT addresses, so the byte LIST *)
(* a leaf holds and the message's byte MAP the log records are one and the  *)
(* same resource.  [VirtioQueue.pa_add_inj] is this fact, but that file     *)
(* sits far above the kit; these are LOCAL so the names cannot collide      *)
(* there.                                                                  *)
(* ---------------------------------------------------------------------- *)
Local Lemma tso_add_vec_unsigned (x y : SailStdpp.Values.mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, SailStdpp.Values.to_word,
    SailStdpp.Values.get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Local Lemma tso_moi_unsigned (k : Z) :
  bv_unsigned (SailStdpp.Values.mword_of_int k : SailStdpp.Values.mword 64)
  = bv_wrap 64 k.
Proof.
  unfold SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* the [: mword 64] ascription is load-bearing: [pa_add] lands in [Arch.pa],
   whose width is an unreduced [Z_idx] match, and [bv_unsigned] would
   elaborate at THAT width (they print identically and then fail to
   rewrite) -- VirtioQueue.v's own note, kept. *)
Local Lemma tso_pa_add_unsigned (a : Arch.pa) (j : nat) :
  bv_unsigned (pa_add a j : SailStdpp.Values.mword 64)
  = bv_wrap 64 (bv_unsigned (a : SailStdpp.Values.mword 64) + Z.of_nat j).
Proof.
  unfold pa_add, add_vec_int.
  rewrite tso_add_vec_unsigned tso_moi_unsigned bv_wrap_add_idemp_r.
  reflexivity.
Qed.

Local Lemma tso_mod64 : bv_modulus 64 = 18446744073709551616%Z.
Proof. vm_compute. reflexivity. Qed.

Local Lemma tso_wrap_cancel (u i j : Z) :
  (0 <= i < 18446744073709551616)%Z -> (0 <= j < 18446744073709551616)%Z ->
  ((u + i) `mod` 18446744073709551616 = (u + j) `mod` 18446744073709551616)%Z ->
  i = j.
Proof.
  intros Hi Hj Heq.
  assert (Hd : ((i - j) `mod` 18446744073709551616 = 0)%Z).
  { replace (i - j)%Z with ((u + i) - (u + j))%Z by lia.
    rewrite Zminus_mod Heq Z.sub_diag. reflexivity. }
  apply Z.mod_divide in Hd; [| lia ].
  destruct Hd as [k Hk]. nia.
Qed.

Local Lemma tso_pa_add_inj (a : Arch.pa) (i j : nat) :
  (Z.of_nat i < 18446744073709551616)%Z ->
  (Z.of_nat j < 18446744073709551616)%Z ->
  pa_add a i = pa_add a j -> i = j.
Proof.
  intros Hi Hj Heq.
  assert (Hu : bv_unsigned (pa_add a i : SailStdpp.Values.mword 64)
               = bv_unsigned (pa_add a j : SailStdpp.Values.mword 64))
    by (by rewrite Heq).
  rewrite !tso_pa_add_unsigned in Hu. unfold bv_wrap in Hu.
  rewrite tso_mod64 in Hu.
  assert (Hz : Z.of_nat i = Z.of_nat j)
    by (apply (tso_wrap_cancel (bv_unsigned (a : SailStdpp.Values.mword 64)));
        [ lia | lia | exact Hu ]).
  lia.
Qed.

Local Lemma tso_foldr_ins_dom {A} (l : list nat) (pa : Arch.pa)
    (f : nat -> A) (mm : gmap Arch.pa A) :
  dom (foldr (fun j acc => <[pa_add pa j := f j]> acc) mm l)
  = list_to_set (pa_add pa <$> l) ∪ dom mm.
Proof.
  induction l as [|j l IH].
  - cbn [foldr fmap list_fmap list_to_set]. set_solver.
  - cbn [foldr fmap list_fmap list_to_set]. rewrite dom_insert_L IH. set_solver.
Qed.

Local Lemma tso_nodup_win (pa : Arch.pa) (k : nat) :
  (Z.of_nat k <= 18446744073709551616)%Z ->
  base.NoDup (pa_add pa <$> seq 0 k).
Proof.
  intros Hk. apply NoDup_fmap_2_strong; [| apply NoDup_seq].
  intros i j Hi Hj Heq. apply elem_of_seq in Hi. apply elem_of_seq in Hj.
  apply (tso_pa_add_inj pa i j); [ lia | lia | exact Heq ].
Qed.

Section ctx.
  Context `{!riscvGS Σ}.

  (* ---------------------------------------------------------------- *)
  (* The per-context authorities                                       *)
  (* ---------------------------------------------------------------- *)

  (* Both authorities at a fraction ([TsoCtxTwin2.ctx_at]): the halves
     are what [ctx_dom] borrows; agreement across halves is what pins
     the borrow. *)
  Definition ctx_at (ξ : CtxId) (q : Qp) (B : nat)
      (D : gmap (nat * Arch.pa) unit) : iProp Σ :=
    (mono_nat_auth_own (ctx_bound_name ξ) q B ∗
     ghost_map_auth (ctx_dirty_name ξ) q D)%I.

  Lemma ctx_at_halves ξ B D :
    ctx_at ξ 1 B D ⊣⊢ ctx_at ξ (1/2) B D ∗ ctx_at ξ (1/2) B D.
  Proof.
    rewrite /ctx_at.
    rewrite (fractional_half (mono_nat_auth_own (ctx_bound_name ξ) 1 B)).
    rewrite (fractional_half (ghost_map_auth (ctx_dirty_name ξ) 1 D)).
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  Lemma ctx_at_agree ξ q1 q2 B1 D1 B2 D2 :
    ctx_at ξ q1 B1 D1 -∗ ctx_at ξ q2 B2 D2 -∗ ⌜B1 = B2 ∧ D1 = D2⌝.
  Proof.
    iIntros "[Hb1 Hd1] [Hb2 Hd2]".
    iDestruct (mono_nat_auth_own_agree with "Hb1 Hb2") as %[_ ?].
    iDestruct (ghost_map_auth_agree with "Hd1 Hd2") as %?.
    by iPureIntro.
  Qed.

  (* [TsoGhost.llb_valid] at a FRACTION of the authority.  [ctx_dom] holds
     half of the bound authority ([ctx_at ξ (1/2) …]) and still has to read
     the clean arm off a fact, so the whole-authority form does not serve.
     Same proof; [mono_nat_lb_own_valid] is fraction-generic already. *)
  Local Lemma llb_valid_q (γ : gname) (q : Qp) (n K : nat) :
    mono_nat_auth_own γ q n -∗ llb γ K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* own_context: the running-thread token -- THE TIE                  *)
  (* ---------------------------------------------------------------- *)

  (* THE RUNNING TOKEN: "this hart is running as ξ"
     ([TsoCtxTwin2.own_context] at the ambient hart).  Both of ξ's
     authorities; the stable view receipt tying the bound to THIS
     hart's view ([B ≤ K] and [view_lb (hart_agent cpu_id) K] --
     forever, since views only grow: every clean fact of mine is
     visible here); the dirty watermark [W] (every dirty timestamp is a
     legal log position at most W -- what lets park and fork stamp
     without the interp); and the per-entry justification (my own
     message on THIS hart, or under the bound).  It lives inside
     [sie_cap_gpr] (ruling 2), is born at boot ([own_context_boot], one
     per hart), exchanged at swtch, and dropped at a zombie park. *)
  Definition own_context_def `{CID : CpuId} (ξ : CtxId) : iProp Σ :=
    (∃ (B K W : nat) (D : gmap (nat * Arch.pa) unit),
      ctx_at ξ 1 B D ∗
      view_lb view_name loglen_name (hart_agent cpu_id) K ∗ ⌜(B ≤ K)%nat⌝ ∗
      llb loglen_name W ∗ ⌜∀ k, k ∈ dom D → (k.1 ≤ W)%nat⌝ ∗
      [∗ map] k ↦ _ ∈ D, dirty_ok logm_name (hart_agent cpu_id) B k)%I.
  Lemma own_context_aux : { f | f = @own_context_def }.
  Proof. by eexists. Qed.
  Definition own_context `{CID : CpuId} (ξ : CtxId) : iProp Σ :=
    proj1_sig own_context_aux CID ξ.
  Lemma own_context_unseal `{CID : CpuId} (ξ : CtxId) :
    own_context ξ = own_context_def ξ.
  Proof. unfold own_context. by rewrite (proj2_sig own_context_aux). Qed.

  (* THE PARKED TOKEN ([TsoCtxTwin2.ctx_parked]): a thread of control
     not running anywhere -- ξ's authorities with no hart tie.  The
     bound IS the stamp: park raised it past every dirty entry (the
     dirty→clean conversion), so a parked context's facts are all clean
     at [T] and the resumer needs exactly [T ≤ its view].  [llb T]
     keeps the stamp a legal log position.  Deliberately NOT
     hart-ambient: a parked record is migratable, and this token is why
     that is type-correct. *)
  Definition ctx_parked_def (ξ : CtxId) (T : nat) : iProp Σ :=
    (∃ D : gmap (nat * Arch.pa) unit,
      ctx_at ξ 1 T D ∗ llb loglen_name T ∗
      ⌜∀ k, k ∈ dom D → (k.1 ≤ T)%nat⌝)%I.
  Lemma ctx_parked_aux : { f | f = ctx_parked_def }.
  Proof. by eexists. Qed.
  Definition ctx_parked (ξ : CtxId) (T : nat) : iProp Σ :=
    proj1_sig ctx_parked_aux ξ T.
  Lemma ctx_parked_unseal (ξ : CtxId) (T : nat) :
    ctx_parked ξ T = ctx_parked_def ξ T.
  Proof. unfold ctx_parked. by rewrite (proj2_sig ctx_parked_aux). Qed.

  (* THE STABLE HART-VIEW LOWER BOUND ([TsoCtxTwin2.view_lb] at the
     ambient hart): "this hart's view has passed K".  Persistent and
     monotone -- the honest, never-falsified form of the resume premise
     "the hart is at least as fresh as the parked stamp".  Minted below
     the seam at the AMO-acquire leaf ([hart_view_lb_get] at the
     bottom of this file, the [twin_passed_get] image). *)
  Definition hart_view_lb_def `{CID : CpuId} (K : nat) : iProp Σ :=
    view_lb view_name loglen_name (hart_agent cpu_id) K.
  Lemma hart_view_lb_aux : { f | f = @hart_view_lb_def }.
  Proof. by eexists. Qed.
  Definition hart_view_lb `{CID : CpuId} (K : nat) : iProp Σ :=
    proj1_sig hart_view_lb_aux CID K.
  Lemma hart_view_lb_unseal `{CID : CpuId} (K : nat) :
    hart_view_lb K = hart_view_lb_def K.
  Proof. unfold hart_view_lb. by rewrite (proj2_sig hart_view_lb_aux). Qed.

  Global Instance hart_view_lb_persistent `{CID : CpuId} K :
    Persistent (hart_view_lb K).
  Proof. rewrite hart_view_lb_unseal /hart_view_lb_def. apply _. Qed.
  Global Instance hart_view_lb_timeless `{CID : CpuId} K :
    Timeless (hart_view_lb K).
  Proof. rewrite hart_view_lb_unseal /hart_view_lb_def. apply _. Qed.

  Lemma hart_view_lb_le `{CID : CpuId} (K K' : nat) :
    (K' ≤ K)%nat → hart_view_lb K -∗ hart_view_lb K'.
  Proof.
    rewrite !hart_view_lb_unseal /hart_view_lb_def. apply view_lb_le.
  Qed.

  (* Exclusivity, in all three pairings: one bound authority per context,
     one token.  ([TsoCtxTwin2.own_context_excl] / [ctx_parked_excl] /
     [own_context_parked_excl]; the running form holds across DIFFERENT
     ambient harts too, which is the statement here.) *)
  Lemma own_context_excl {CID1 CID2 : CpuId} (ξ : CtxId) :
    own_context (CID := CID1) ξ -∗ own_context (CID := CID2) ξ -∗ False.
  Proof.
    rewrite !own_context_unseal /own_context_def.
    iIntros "(%B1 & %K1 & %W1 & %D1 & [Hb1 _] & _)".
    iIntros "(%B2 & %K2 & %W2 & %D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Lemma ctx_parked_excl (ξ : CtxId) (T1 T2 : nat) :
    ctx_parked ξ T1 -∗ ctx_parked ξ T2 -∗ False.
  Proof.
    rewrite !ctx_parked_unseal /ctx_parked_def.
    iIntros "(%D1 & [Hb1 _] & _) (%D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Lemma own_context_parked_excl `{CID : CpuId} (ξ : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξ T -∗ False.
  Proof.
    rewrite own_context_unseal /own_context_def
            ctx_parked_unseal /ctx_parked_def.
    iIntros "(%B & %K & %W & %D & [Hb1 _] & _) (%D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Global Instance own_context_timeless `{CID : CpuId} ξ :
    Timeless (own_context ξ).
  Proof. rewrite own_context_unseal /own_context_def. apply _. Qed.
  Global Instance ctx_parked_timeless ξ T : Timeless (ctx_parked ξ T).
  Proof. rewrite ctx_parked_unseal /ctx_parked_def. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (* The token lifecycle (ruling 4's three primitives, plus deposit)    *)
  (* ---------------------------------------------------------------- *)

  (* FRESH ALLOCATION YIELDS A PARKED CONTEXT, and the mint is PURE (no
     interp, no premise): a context that has never run claims no hart and
     no visibility.  Stamp 0 suffices because [ctx_deposit] raises the
     stamp per deposited fact.  ([TsoCtxTwin2.twin_parked_alloc].)
     This is [ProofForkretPark]'s mint. *)
  Lemma ctx_parked_alloc : ⊢ |==> ∃ ξc : CtxId, ctx_parked ξc 0.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod (ghost_map_alloc_empty (K := nat * Arch.pa) (V := unit)) as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd).
    rewrite ctx_parked_unseal /ctx_parked_def.
    iExists ∅. iFrame "Hb Hd".
    iSplitR; first by iApply llb_0.
    iPureIntro. intros k Hk. rewrite dom_empty in Hk. set_solver.
  Qed.

  (* BOOT'S MINT: a hart's FIRST running token.  One per hart, at
     [SystemAdequacy.xv6_boot_era], and nowhere else (the sweep-era
     throwaway mints live in [TsoCtxShim.own_context_alloc] and die with
     it).  Sound unconditionally ([TsoCtxTwin2.twin_run_alloc]: a
     context born at bound 0 with an empty dirty set claims nothing any
     hart could not honour), so this is licensing by NAME, not a lie. *)
  Lemma own_context_boot `{CID : CpuId} : ⊢ |==> ∃ ξ : CtxId, own_context ξ.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod (ghost_map_alloc_empty (K := nat * Arch.pa) (V := unit)) as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd).
    rewrite own_context_unseal /own_context_def.
    iExists 0%nat, 0%nat, 0%nat, ∅. iFrame "Hb Hd".
    iSplitR; first by iApply view_lb_0.
    iSplitR; first done.
    iSplitR; first by iApply llb_0.
    iSplitR; first (iPureIntro; intros k Hk; rewrite dom_empty in Hk;
                    set_solver).
    by iApply big_sepM_empty.
  Qed.

  (* PARK: publish and let go of the hart.  ONE BOUND-RAISE converts
     every dirty entry to clean; the stamp is K ⊔ W -- the token's own
     receipts -- so the scheduler needs nothing from the machine.
     ([TsoCtxTwin2.twin_park], interp-free.) *)
  Lemma ctx_park `{CID : CpuId} (ξ : CtxId) :
    own_context ξ ==∗ ∃ T, ctx_parked ξ T.
  Proof.
    rewrite own_context_unseal /own_context_def.
    iIntros "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & _)".
    set (T := Nat.max K W).
    iMod (mono_nat_own_update T with "Hb") as "[Hb _]"; first lia.
    iModIntro. iExists T.
    rewrite ctx_parked_unseal /ctx_parked_def.
    iExists D. iFrame "Hb Hd".
    iSplitR.
    { iApply (llb_max with "[] HW"). by iApply view_lb_llb. }
    iPureIntro. intros k Hk. have := HDW _ Hk. lia.
  Qed.

  (* RESUME: re-host a parked context on THIS hart.  The premise is the
     stable pair -- a persistent view receipt dominating the parked stamp
     -- and NOTHING relates the parking and resuming harts.  The bundle
     is re-founded with every dirty entry on its clean arm.
     ([TsoCtxTwin2.twin_resume]; the receipt/stamp comparison is minted
     at the resuming hart's lock acquire, [hart_view_lb_get] below.) *)
  Lemma ctx_resume `{CID : CpuId} (ξ : CtxId) (T K : nat) :
    (T ≤ K)%nat →
    hart_view_lb K -∗ ctx_parked ξ T ==∗ own_context ξ.
  Proof.
    rewrite hart_view_lb_unseal /hart_view_lb_def
            ctx_parked_unseal /ctx_parked_def
            own_context_unseal /own_context_def.
    iIntros (HTK) "#HK (%D & Hat & #HT & %HDT)".
    iModIntro. iExists T, K, T, D. iFrame "Hat HK HT".
    iSplitR; first done.
    iSplitR; first done.
    iApply big_sepM_intro. iIntros "!>" (k [] Hk).
    iLeft. iPureIntro. apply HDT. by eapply elem_of_dom_2.
  Qed.

  (* THE SWTCH EXCHANGE: a hart always runs exactly one thread, so the
     primitive crossing swaps the running token against a parked one --
     the parker's identity parks, the target's runs, on this hart.
     ([TsoCtxTwin2.twin_exchange], derived from park + resume.) *)
  Lemma ctx_exchange `{CID : CpuId} (ξ1 ξ2 : CtxId) (T K : nat) :
    (T ≤ K)%nat →
    hart_view_lb K -∗ own_context ξ1 -∗ ctx_parked ξ2 T ==∗
    own_context ξ2 ∗ ∃ T1, ctx_parked ξ1 T1.
  Proof.
    iIntros (HTK) "#HK Hrun Hpk".
    iMod (ctx_park with "Hrun") as (T1) "Hpk1".
    iMod (ctx_resume ξ2 T K HTK with "HK Hpk") as "Hrun".
    iModIntro. iFrame "Hrun". iExists T1. iExact "Hpk1".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The context-indexed points-to                                     *)
  (* ---------------------------------------------------------------- *)

  (* [ctx_pointsto ξ a dq v]: the byte fact, registered to context ξ --
     [mem_pointsto]'s body (the kmap claim, the canonicality/RAM/tier
     pins, the FLAT byte at the fact's dq) PLUS the byte's latest-write
     timestamp (a [ts_name] fragment, dq-mirrored so fractions and
     discards move all three together) PLUS the twin's clean/dirty bit.
     The disjunction is never client-visible (the seal).
     ([TsoCtxTwin2.ctx_pointsto], with the VA plumbing riding along.)

     THE CLEAN ARM IS [llb]-SHAPED, NOT A BARE [mono_nat_lb_own]
     (tso-machine-flip.md §6 amendment A6.10): [llb γ t] is
     [mono_nat_lb_own γ t ∨ ⌜t = 0⌝], and the second arm is not a
     convenience -- it is the TIMESTAMP-0 FACT.  A byte whose latest write
     is the era image is visible to every agent at every view
     ([TsoMemPa.read_down_0]), so its justification needs NO context at
     all; with the bare lower bound it would need one bupd PER CONTEXT
     ([mono_nat_lb_own_0] is an update), which is exactly what makes the
     ∀-context image facts ([KernelDataInv.kernel_data], kernel text)
     unmintable.  Everything downstream is unaffected: [llb_valid] gives
     [t ≤ B] on the [t ≠ 0] arm and [t = 0 ≤ B] on the other, which is all
     [ctx_load_ok] and [ctx_morph_pointsto] ever ask of it.  [TsoGhost.llb]
     carries the same trick at the log length for the same reason. *)
  Definition ctx_pointsto_def `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ (ppn : mword 44) (t : nat),
       kmap_at (svpn_of va) ppn KP_rw ∗
       ⌜(uint va < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn va)⌝ ∗
       ⌜ktier_pin cur_ktier ppn va⌝ ∗
       pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn va) dq v ∗
       (pa_of ppn va) ↪[ts_name]{dq} (t, None) ∗
       (llb (ctx_bound_name ξ) t                             (* CLEAN *)
        ∨ (t, pa_of ppn va) ↪[ctx_dirty_name ξ]{dq} ()))%I.  (* DIRTY *)
  Lemma ctx_pointsto_aux : { f | f = @ctx_pointsto_def }.
  Proof. by eexists. Qed.
  Definition ctx_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    proj1_sig ctx_pointsto_aux KTR ξ va dq v.
  Lemma ctx_pointsto_unseal `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_pointsto ξ va dq v = ctx_pointsto_def ξ va dq v.
  Proof. unfold ctx_pointsto. by rewrite (proj2_sig ctx_pointsto_aux). Qed.

  (* the ctx fact FORGETS to the raw flat fact (sound: gen_heap tracks
     the flat cache, and the pointsto inside IS the flat byte at the
     fact's dq).  Used INTERNALLY to derive the pure laws, and exported
     ONCE, under a name that says what it costs ([ctx_pointsto_forget]
     below). *)
  Local Lemma ctx_pointsto_mem_proj {KTR : CurKtier} ξ a dq v :
    ctx_pointsto_def (KTR := KTR) ξ a dq v ⊢ mem_pointsto (KTR := KTR) a dq v.
  Proof.
    iIntros "(%ppn & %t & #Hk & % & % & % & Hp & _ & _)".
    rewrite /mem_pointsto. iExists ppn. by iFrame "Hk Hp".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE FORGETFUL PROJECTION (tso-machine-flip.md §6 amendment A6.8). *)
  (*                                                                   *)
  (* The ONE direction of the dead shim's [ctx_*_of/to_mem] pair that   *)
  (* survives the machine flip, and the ONLY sanctioned way a ctx fact  *)
  (* leaves the ledger.  Its price is stated once here so no call site  *)
  (* has to re-derive it:                                              *)
  (*                                                                   *)
  (*   IT IS ONE-WAY AND LOSSY.  It drops the byte's latest-write       *)
  (*   TIMESTAMP fragment and the clean/dirty BIT.  Neither can be      *)
  (*   recovered: the timestamp element is a [ghost_map] fragment that  *)
  (*   was handed out once, so nothing above the interp can mint it     *)
  (*   again ([TsoCtxShim]'s header: the [_of_mem] directions are FALSE *)
  (*   at TSO, and this is why).                                       *)
  (*                                                                   *)
  (*   THE RESULT LICENSES NO PLAIN LOAD.  [ctx_load_ok] -- the gate    *)
  (*   that discharges §6's [Mobl_ram_plain] -- needs exactly the two   *)
  (*   conjuncts this drops.  A [mem_pointsto] is still good for value  *)
  (*   agreement, canonicality, the tier pin, the RAM claim, and for    *)
  (*   the strongly-ordered arms (fetch / page walk / exclusive), which *)
  (*   read the flat cache.                                            *)
  (*                                                                   *)
  (* So [grep ctx_pointsto_forget] is the honest inventory of the       *)
  (* places where the tree still parks a byte OUTSIDE the ledger: the   *)
  (* unflipped towers ([↦ₛ], [↦₂]/[↦₄]), the deliberately-raw lock      *)
  (* metadata (tso-port.md §0.8' ruling 2) and the phys tier (ruling    *)
  (* 6).  Each is a stage-2 / M4 worklist entry, not a leak.            *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_forget {KTR : CurKtier} ξ a dq v :
    ctx_pointsto (KTR := KTR) ξ a dq v ⊢ mem_pointsto (KTR := KTR) a dq v.
  Proof. rewrite ctx_pointsto_unseal. apply ctx_pointsto_mem_proj. Qed.

  (* The law surface, mirroring [mem_pointsto]'s (RiscvPtsto.v).  Each is
     the twin lemma with the VA plumbing riding along; a law that could
     not be proven here is a law that must not be added. *)

  Global Instance ctx_pointsto_timeless (KTR : CurKtier) ξ a dq v :
    Timeless (ctx_pointsto (KTR := KTR) ξ a dq v).
  Proof. rewrite ctx_pointsto_unseal /ctx_pointsto_def. apply _. Qed.

  Global Instance ctx_pointsto_discarded_persistent (KTR : CurKtier) ξ a v :
    Persistent (ctx_pointsto (KTR := KTR) ξ a DfracDiscarded v).
  Proof. rewrite ctx_pointsto_unseal /ctx_pointsto_def. apply _. Qed.

  (* agreement is CROSS-context (two registered facts about one byte name
     one flat cell): sound at TSO, and the form invariants need. *)
  Lemma ctx_pointsto_agree {kt1 kt2 : ktier} ξ1 ξ2 a dq1 b1 dq2 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a dq1 b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a dq2 b2 -∗ ⌜b1 = b2⌝.
  Proof.
    rewrite !ctx_pointsto_unseal.
    iIntros "H1 H2".
    iDestruct (ctx_pointsto_mem_proj with "H1") as "H1".
    iDestruct (ctx_pointsto_mem_proj with "H2") as "H2".
    iApply (mem_pointsto_agree with "H1 H2").
  Qed.

  Lemma ctx_pointsto_ne {kt1 kt2 : ktier} ξ1 ξ2 a1 a2 dq b1 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a1 (DfracOwn 1) b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a2 dq b2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    rewrite !ctx_pointsto_unseal.
    iIntros "H1 H2".
    iDestruct (ctx_pointsto_mem_proj with "H1") as "H1".
    iDestruct (ctx_pointsto_mem_proj with "H2") as "H2".
    iApply (mem_pointsto_ne with "H1 H2").
  Qed.

  Lemma ctx_pointsto_frac_split `{KTR : !CurKtier} ξ a q1 q2 b :
    ctx_pointsto ξ a (DfracOwn (q1 + q2)) b ⊣⊢
    ctx_pointsto ξ a (DfracOwn q1) b ∗ ctx_pointsto ξ a (DfracOwn q2) b.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iSplit.
    - iIntros "(%ppn & %t & #Hk & %Hc & %Hr & %Hp & Hpt & Hts & Hbit)".
      iDestruct "Hpt" as "[Hpt1 Hpt2]".
      iDestruct "Hts" as "[Hts1 Hts2]".
      iDestruct "Hbit" as "[#Hcl | Hdt]".
      + iSplitL "Hpt1 Hts1".
        * iExists ppn, t. iFrame "Hk Hpt1 Hts1".
          iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. by iLeft.
        * iExists ppn, t. iFrame "Hk Hpt2 Hts2".
          iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. by iLeft.
      + iDestruct "Hdt" as "[Hdt1 Hdt2]".
        iSplitL "Hpt1 Hts1 Hdt1".
        * iExists ppn, t. iFrame "Hk Hpt1 Hts1 Hdt1".
          iSplit; [done|]. iSplit; [done|]. done.
        * iExists ppn, t. iFrame "Hk Hpt2 Hts2 Hdt2".
          iSplit; [done|]. iSplit; [done|]. done.
    - iIntros "[(%ppn1 & %t1 & #Hk1 & %Hc & %Hr1 & %Hp1 & Hpt1 & Hts1 & Hbit1)
                (%ppn2 & %t2 & #Hk2 & %  & %Hr2 & %Hp2 & Hpt2 & Hts2 & Hbit2)]".
      iDestruct (kmap_at_agree with "Hk1 Hk2") as %[<- _].
      iDestruct (ghost_map_elem_combine with "Hts1 Hts2") as "[Hts %Heq]".
      injection Heq as Heq. subst t2.
      iCombine "Hpt1 Hpt2" as "Hpt".
      rewrite !dfrac_op_own.
      iExists ppn1, t1. iFrame "Hk1 Hpt Hts".
      iSplit; first done. iSplit; first done. iSplit; first done.
      iDestruct "Hbit1" as "[#Hcl | Hdt1]"; first by iLeft.
      iDestruct "Hbit2" as "[#Hcl | Hdt2]"; first by iLeft.
      iDestruct (ghost_map_elem_combine with "Hdt1 Hdt2") as "[Hdt _]".
      rewrite dfrac_op_own. by iRight.
  Qed.

  Lemma ctx_pointsto_persist `{KTR : !CurKtier} ξ a dq b :
    ctx_pointsto ξ a dq b ==∗ ctx_pointsto ξ a DfracDiscarded b.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & #Hk & % & % & % & Hpt & Hts & Hbit)".
    iMod (pointsto_persist with "Hpt") as "Hpt".
    iMod (ghost_map_elem_persist with "Hts") as "Hts".
    iDestruct "Hbit" as "[#Hcl | Hdt]".
    - iModIntro. iExists ppn, t. iFrame "Hk Hpt Hts".
      iSplit; first done. iSplit; first done. iSplit; first done. by iLeft.
    - iMod (ghost_map_elem_persist with "Hdt") as "Hdt".
      iModIntro. iExists ppn, t. iFrame "Hk Hpt Hts".
      iSplit; first done. iSplit; first done. iSplit; first done. by iRight.
  Qed.

  (* THE PURE CONJUNCTS, read off the fact ([mem_canonical]'s and
     [mem_pointsto_ram]'s images).  Stated here rather than left to
     [ctx_pointsto_forget] + the raw law because they cost the holder
     NOTHING: a pure fact is not a place where the ledger can leak. *)
  Lemma ctx_pointsto_canonical `{KTR : !CurKtier} ξ a dq v :
    ctx_pointsto ξ a dq v -∗ ⌜(uint a < 274877906944)%Z⌝.
  Proof.
    rewrite ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & _ & %Hc & _)". iPureIntro. exact Hc.
  Qed.

  (* THE TIER WEAKENING ([mem_ktier_mono]'s image).  The pin is the only
     tier-dependent conjunct of the body and it weakens ([ktier_pin_mono]),
     exactly as at the raw fact -- so this law needs no crossing at all,
     which is what retires the rehearsal-era "mem_ktier_mono rides the raw
     law between two shims" seam (tso-port.md §0.9'). *)
  Lemma ctx_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'} ξ a dq v :
    ctx_pointsto (KTR := kt) ξ a dq v ⊢ ctx_pointsto (KTR := kt') ξ a dq v.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & #Hk & %Hc & %Hd & %Hp & Hpt & Hts & Hbit)".
    iExists ppn, t. iFrame "Hk Hpt Hts Hbit".
    iSplit; [iPureIntro; exact Hc|]. iSplit; [iPureIntro; exact Hd|].
    iPureIntro. exact (ktier_pin_mono kt kt' ppn a Hp).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The context-indexed WORD tower (the M1 notation flip's carrier)    *)
  (* ---------------------------------------------------------------- *)

  (* Derived from [ctx_pointsto]'s exported surface alone, so the tower
     is honest with no extra proof obligations.  Text unchanged from the
     SC-era file. *)

  (* byte-window agreement and splitting, the two engine lemmas *)
  Lemma ctx_bytes_agree {m : N} {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId)
      (a : Arch.pa) (k n : nat) (dq1 dq2 : dfrac) (w1 w2 : bv m) :
    ([∗ list] j ∈ seq k n,
       ctx_pointsto (KTR := kt1) ξ1 (pa_add a j) dq1 (nth_byte w1 j)) -∗
    ([∗ list] j ∈ seq k n,
       ctx_pointsto (KTR := kt2) ξ2 (pa_add a j) dq2 (nth_byte w2 j)) -∗
    ⌜forall j, (k <= j < k + n)%nat -> nth_byte w1 j = nth_byte w2 j⌝.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. lia.
    - iIntros "[Hh1 Ht1] [Hh2 Ht2]".
      iDestruct (ctx_pointsto_agree with "Hh1 Hh2") as %Heq.
      iDestruct (IH (S k) with "Ht1 Ht2") as %Hrest.
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hne]; [exact Heq|].
      apply Hrest. lia.
  Qed.

  Lemma ctx_bytes_frac_split `{KTR : !CurKtier} {m : N} (ξ : CtxId)
      (a : Arch.pa) (k n : nat) (q1 q2 : Qp) (w : bv m) :
    ([∗ list] j ∈ seq k n,
       ctx_pointsto ξ (pa_add a j) (DfracOwn (q1 + q2)) (nth_byte w j)) ⊣⊢
    ([∗ list] j ∈ seq k n,
       ctx_pointsto ξ (pa_add a j) (DfracOwn q1) (nth_byte w j)) ∗
    ([∗ list] j ∈ seq k n,
       ctx_pointsto ξ (pa_add a j) (DfracOwn q2) (nth_byte w j)).
  Proof.
    rewrite -big_sepL_sep. apply big_opL_proper. intros ? j ?.
    apply ctx_pointsto_frac_split.
  Qed.

  Definition ctx_word_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Section ctx_word.
    Context `{KTR : !CurKtier}.

    Lemma ctx_word_pointsto_unfold ξ a dq w :
      ctx_word_pointsto ξ a dq w ⊣⊢
      ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
      ([∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j)).
    Proof. reflexivity. Qed.

    Lemma ctx_word_pointsto_aligned_p ξ a dq w :
      ctx_word_pointsto ξ a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
    Proof. iIntros "[$ _]". Qed.

    Lemma ctx_word_pointsto_bytes ξ a dq w :
      ctx_word_pointsto ξ a dq w ⊢
      [∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j).
    Proof. iIntros "[_ $]". Qed.

    Lemma ctx_word_pointsto_intro ξ a dq w :
      is_aligned_paddr (Physaddr a) 8 = true ->
      ([∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))
      ⊢ ctx_word_pointsto ξ a dq w.
    Proof. iIntros (Hal) "H". by iFrame. Qed.

    Global Instance ctx_word_pointsto_timeless ξ a dq w :
      Timeless (ctx_word_pointsto ξ a dq w).
    Proof. rewrite /ctx_word_pointsto. apply _. Qed.

    Global Instance ctx_word_pointsto_discarded_persistent ξ a w :
      Persistent (ctx_word_pointsto ξ a DfracDiscarded w).
    Proof. rewrite /ctx_word_pointsto. apply _. Qed.

    Lemma ctx_word_pointsto_frac_split ξ a q1 q2 w :
      ctx_word_pointsto ξ a (DfracOwn (q1 + q2)) w ⊣⊢
      ctx_word_pointsto ξ a (DfracOwn q1) w ∗
      ctx_word_pointsto ξ a (DfracOwn q2) w.
    Proof.
      rewrite /ctx_word_pointsto (ctx_bytes_frac_split ξ a 0 8 q1 q2 w).
      iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
    Qed.

    Lemma ctx_word_pointsto_persist ξ a dq w :
      ctx_word_pointsto ξ a dq w ==∗ ctx_word_pointsto ξ a DfracDiscarded w.
    Proof.
      iIntros "[#Hal H]".
      iAssert (|==> [∗ list] j ∈ seq 0 8,
        ctx_pointsto ξ (pa_add a j) DfracDiscarded (nth_byte w j))%I
        with "[H]" as ">H".
      { iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
        iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_persist. }
      iModIntro. by iFrame "Hal H".
    Qed.
  End ctx_word.

  (* the tower's forgetful projection and tier weakening: [ctx_word_pointsto]
     is [word_pointsto]'s body over the sealed byte, so both are the byte law
     under the big-op.  The [_forget] form carries the same warning its byte
     original does -- it is what the raw lock metadata (tso-port.md §0.8'
     ruling 2) and the [↦₂]/[↦₄] towers cross on. *)
  Lemma ctx_word_pointsto_forget `{KTR : !CurKtier} ξ a dq w :
    ctx_word_pointsto ξ a dq w ⊢ word_pointsto a dq w.
  Proof.
    rewrite /ctx_word_pointsto /word_pointsto.
    iIntros "[$ H]". iApply (big_sepL_mono with "H").
    iIntros (k j _) "H". iApply (ctx_pointsto_forget with "H").
  Qed.

  Lemma ctx_word_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'} ξ a dq w :
    ctx_word_pointsto (KTR := kt) ξ a dq w ⊢
    ctx_word_pointsto (KTR := kt') ξ a dq w.
  Proof.
    rewrite /ctx_word_pointsto. iIntros "[$ H]".
    iApply (big_sepL_mono with "H").
    iIntros (k j _) "H". iApply (ctx_ktier_mono kt kt' with "H").
  Qed.

  Lemma ctx_word_pointsto_agree {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId) a dq1 w1 dq2 w2 :
    ctx_word_pointsto (KTR := kt1) ξ1 a dq1 w1 -∗
    ctx_word_pointsto (KTR := kt2) ξ2 a dq2 w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (ctx_bytes_agree ξ1 ξ2 a 0 8 with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=8)). intros j Hj. apply Hb. lia.
  Qed.


  (* ---- the 2-BYTE tower ([↦₂]), M1 STAGE 2 ---------------------
     Character-for-character the 8-byte tower above at width 2; the two
     differ only in the alignment constant and the byte count, which is why
     stage 2 costs nothing beyond re-declaring the notations.  NOT SEALED,
     for the reason [ctx_word_pointsto] is not: a tower OVER the sealed byte
     leaks nothing, and the tree's proofs destruct and frame the word shape
     structurally. *)
  Definition ctx_word2_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 16) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 2 = true⌝ ∗
     [∗ list] j ∈ seq 0 2, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Section ctx_word2.
    Context `{KTR : !CurKtier}.

    Lemma ctx_word2_pointsto_unfold ξ a dq w :
      ctx_word2_pointsto ξ a dq w ⊣⊢
      ⌜is_aligned_paddr (Physaddr a) 2 = true⌝ ∗
      ([∗ list] j ∈ seq 0 2, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j)).
    Proof. reflexivity. Qed.

    Lemma ctx_word2_pointsto_aligned_p ξ a dq w :
      ctx_word2_pointsto ξ a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 2 = true⌝.
    Proof. iIntros "[$ _]". Qed.

    Lemma ctx_word2_pointsto_bytes ξ a dq w :
      ctx_word2_pointsto ξ a dq w ⊢
      [∗ list] j ∈ seq 0 2, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j).
    Proof. iIntros "[_ $]". Qed.

    Lemma ctx_word2_pointsto_intro ξ a dq w :
      is_aligned_paddr (Physaddr a) 2 = true ->
      ([∗ list] j ∈ seq 0 2, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))
      ⊢ ctx_word2_pointsto ξ a dq w.
    Proof. iIntros (Hal) "H". by iFrame. Qed.

    Global Instance ctx_word2_pointsto_timeless ξ a dq w :
      Timeless (ctx_word2_pointsto ξ a dq w).
    Proof. rewrite /ctx_word2_pointsto. apply _. Qed.

    Global Instance ctx_word2_pointsto_discarded_persistent ξ a w :
      Persistent (ctx_word2_pointsto ξ a DfracDiscarded w).
    Proof. rewrite /ctx_word2_pointsto. apply _. Qed.

    Lemma ctx_word2_pointsto_frac_split ξ a q1 q2 w :
      ctx_word2_pointsto ξ a (DfracOwn (q1 + q2)) w ⊣⊢
      ctx_word2_pointsto ξ a (DfracOwn q1) w ∗
      ctx_word2_pointsto ξ a (DfracOwn q2) w.
    Proof.
      rewrite /ctx_word2_pointsto (ctx_bytes_frac_split ξ a 0 2 q1 q2 w).
      iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
    Qed.

    Lemma ctx_word2_pointsto_persist ξ a dq w :
      ctx_word2_pointsto ξ a dq w ==∗
      ctx_word2_pointsto ξ a DfracDiscarded w.
    Proof.
      iIntros "[#Hal H]".
      iAssert (|==> [∗ list] j ∈ seq 0 2,
        ctx_pointsto ξ (pa_add a j) DfracDiscarded (nth_byte w j))%I
        with "[H]" as ">H".
      { iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
        iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_persist. }
      iModIntro. by iFrame "Hal H".
    Qed.

    (* the HALF split/join, the form the escrow and fraction protocols
       use ([word2_pointsto_half*]'s images) *)
    Lemma ctx_word2_pointsto_half ξ a w :
      ctx_word2_pointsto ξ a (DfracOwn 1) w ⊣⊢
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w ∗
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w.
    Proof. rewrite -ctx_word2_pointsto_frac_split Qp.div_2. reflexivity. Qed.

    Lemma ctx_word2_pointsto_half_split ξ a w :
      ctx_word2_pointsto ξ a (DfracOwn 1) w -∗
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w ∗
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w.
    Proof. rewrite ctx_word2_pointsto_half. iIntros "$". Qed.

    Lemma ctx_word2_pointsto_half_join ξ a w :
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w -∗
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w -∗
      ctx_word2_pointsto ξ a (DfracOwn 1) w.
    Proof. iIntros "H1 H2". rewrite ctx_word2_pointsto_half. iFrame "H1 H2". Qed.

    (* the forgetful projection at the tower ([ctx_pointsto_forget]'s
       warning applies verbatim -- one-way, and the result licenses no
       plain load) *)
    Lemma ctx_word2_pointsto_forget ξ a dq w :
      ctx_word2_pointsto ξ a dq w ⊢ word2_pointsto a dq w.
    Proof.
      rewrite /ctx_word2_pointsto /word2_pointsto.
      iIntros "[$ H]". iApply (big_sepL_mono with "H").
      iIntros (k j _) "H". iApply (ctx_pointsto_forget with "H").
    Qed.
  End ctx_word2.

  Lemma ctx_word2_pointsto_agree {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId)
      a dq1 w1 dq2 w2 :
    ctx_word2_pointsto (KTR := kt1) ξ1 a dq1 w1 -∗
    ctx_word2_pointsto (KTR := kt2) ξ2 a dq2 w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (ctx_bytes_agree ξ1 ξ2 a 0 2 with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=2)). intros j Hj. apply Hb. lia.
  Qed.

  Lemma ctx_word2_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'} ξ a dq w :
    ctx_word2_pointsto (KTR := kt) ξ a dq w ⊢
    ctx_word2_pointsto (KTR := kt') ξ a dq w.
  Proof.
    rewrite /ctx_word2_pointsto. iIntros "[$ H]".
    iApply (big_sepL_mono with "H").
    iIntros (k j _) "H". iApply (ctx_ktier_mono kt kt' with "H").
  Qed.


  (* ---- the 4-BYTE tower ([↦₄]), M1 STAGE 2 ---------------------
     Character-for-character the 8-byte tower above at width 4; the two
     differ only in the alignment constant and the byte count, which is why
     stage 2 costs nothing beyond re-declaring the notations.  NOT SEALED,
     for the reason [ctx_word_pointsto] is not: a tower OVER the sealed byte
     leaks nothing, and the tree's proofs destruct and frame the word shape
     structurally. *)
  Definition ctx_word4_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 32) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
     [∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Section ctx_word4.
    Context `{KTR : !CurKtier}.

    Lemma ctx_word4_pointsto_unfold ξ a dq w :
      ctx_word4_pointsto ξ a dq w ⊣⊢
      ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
      ([∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j)).
    Proof. reflexivity. Qed.

    Lemma ctx_word4_pointsto_aligned_p ξ a dq w :
      ctx_word4_pointsto ξ a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
    Proof. iIntros "[$ _]". Qed.

    Lemma ctx_word4_pointsto_bytes ξ a dq w :
      ctx_word4_pointsto ξ a dq w ⊢
      [∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j).
    Proof. iIntros "[_ $]". Qed.

    Lemma ctx_word4_pointsto_intro ξ a dq w :
      is_aligned_paddr (Physaddr a) 4 = true ->
      ([∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))
      ⊢ ctx_word4_pointsto ξ a dq w.
    Proof. iIntros (Hal) "H". by iFrame. Qed.

    Global Instance ctx_word4_pointsto_timeless ξ a dq w :
      Timeless (ctx_word4_pointsto ξ a dq w).
    Proof. rewrite /ctx_word4_pointsto. apply _. Qed.

    Global Instance ctx_word4_pointsto_discarded_persistent ξ a w :
      Persistent (ctx_word4_pointsto ξ a DfracDiscarded w).
    Proof. rewrite /ctx_word4_pointsto. apply _. Qed.

    Lemma ctx_word4_pointsto_frac_split ξ a q1 q2 w :
      ctx_word4_pointsto ξ a (DfracOwn (q1 + q2)) w ⊣⊢
      ctx_word4_pointsto ξ a (DfracOwn q1) w ∗
      ctx_word4_pointsto ξ a (DfracOwn q2) w.
    Proof.
      rewrite /ctx_word4_pointsto (ctx_bytes_frac_split ξ a 0 4 q1 q2 w).
      iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
    Qed.

    Lemma ctx_word4_pointsto_persist ξ a dq w :
      ctx_word4_pointsto ξ a dq w ==∗
      ctx_word4_pointsto ξ a DfracDiscarded w.
    Proof.
      iIntros "[#Hal H]".
      iAssert (|==> [∗ list] j ∈ seq 0 4,
        ctx_pointsto ξ (pa_add a j) DfracDiscarded (nth_byte w j))%I
        with "[H]" as ">H".
      { iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
        iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_persist. }
      iModIntro. by iFrame "Hal H".
    Qed.

    (* the HALF split/join, the form the escrow and fraction protocols
       use ([word4_pointsto_half*]'s images) *)
    Lemma ctx_word4_pointsto_half ξ a w :
      ctx_word4_pointsto ξ a (DfracOwn 1) w ⊣⊢
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w ∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w.
    Proof. rewrite -ctx_word4_pointsto_frac_split Qp.div_2. reflexivity. Qed.

    Lemma ctx_word4_pointsto_half_split ξ a w :
      ctx_word4_pointsto ξ a (DfracOwn 1) w -∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w ∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w.
    Proof. rewrite ctx_word4_pointsto_half. iIntros "$". Qed.

    Lemma ctx_word4_pointsto_half_join ξ a w :
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w -∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w -∗
      ctx_word4_pointsto ξ a (DfracOwn 1) w.
    Proof. iIntros "H1 H2". rewrite ctx_word4_pointsto_half. iFrame "H1 H2". Qed.

    (* the forgetful projection at the tower ([ctx_pointsto_forget]'s
       warning applies verbatim -- one-way, and the result licenses no
       plain load) *)
    Lemma ctx_word4_pointsto_forget ξ a dq w :
      ctx_word4_pointsto ξ a dq w ⊢ word4_pointsto a dq w.
    Proof.
      rewrite /ctx_word4_pointsto /word4_pointsto.
      iIntros "[$ H]". iApply (big_sepL_mono with "H").
      iIntros (k j _) "H". iApply (ctx_pointsto_forget with "H").
    Qed.
  End ctx_word4.

  Lemma ctx_word4_pointsto_agree {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId)
      a dq1 w1 dq2 w2 :
    ctx_word4_pointsto (KTR := kt1) ξ1 a dq1 w1 -∗
    ctx_word4_pointsto (KTR := kt2) ξ2 a dq2 w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (ctx_bytes_agree ξ1 ξ2 a 0 4 with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=4)). intros j Hj. apply Hb. lia.
  Qed.

  Lemma ctx_word4_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'} ξ a dq w :
    ctx_word4_pointsto (KTR := kt) ξ a dq w ⊢
    ctx_word4_pointsto (KTR := kt') ξ a dq w.
  Proof.
    rewrite /ctx_word4_pointsto. iIntros "[$ H]".
    iApply (big_sepL_mono with "H").
    iIntros (k j _) "H". iApply (ctx_ktier_mono kt kt' with "H").
  Qed.


  (* ---------------------------------------------------------------- *)
  (* Transport: the ONLY ways a fact changes context                   *)
  (* ---------------------------------------------------------------- *)

  (* [ctx_dom ξ ξ']: ξ's facts may be re-registered to ξ'
     ([TsoCtxTwin2.ctx_dom] -- the checkpoint's "one correction, three
     problems" in one definition).  It carries HALF of ξ's own
     authorities (borrowed out of ξ's token, value-pinned by agreement
     with the half left behind) plus a bound-lb of ξ' dominating both
     ξ's bound and ξ's dirty watermark.  Nothing about the machine: Σ's
     constraint that [ctx_dom] be statable without the state
     interpretation holds BY CONSTRUCTION.  Minted ONLY inside the lock
     release/acquire and scheduler park/resume proofs
     ([ctx_dom_to_parked] / [ctx_dom_of_parked] below).  It is
     deliberately NOT persistent (a persistent domination would license
     registering later facts -- the unsound step the `weak-memory`
     branch's notes call out). *)
  Definition ctx_dom_def (ξ ξ' : CtxId) : iProp Σ :=
    (∃ (B W B' : nat) (D : gmap (nat * Arch.pa) unit),
      ctx_at ξ (1/2) B D ∗
      ⌜∀ k, k ∈ dom D → (k.1 ≤ W)%nat⌝ ∗
      ⌜(B ≤ B')%nat⌝ ∗ ⌜(W ≤ B')%nat⌝ ∗
      mono_nat_lb_own (ctx_bound_name ξ') B')%I.
  Lemma ctx_dom_aux : { f | f = ctx_dom_def }.
  Proof. by eexists. Qed.
  Definition ctx_dom (ξ ξ' : CtxId) : iProp Σ := proj1_sig ctx_dom_aux ξ ξ'.
  Lemma ctx_dom_unseal (ξ ξ' : CtxId) : ctx_dom ξ ξ' = ctx_dom_def ξ ξ'.
  Proof. unfold ctx_dom. by rewrite (proj2_sig ctx_dom_aux). Qed.

  (* A context-indexed payload that transports along domination.  This is
     the obligation lock payloads pick up in the M3 sweep: any payload
     failing it at SC is a payload the TSO flip would break -- found
     early, which is the point of the sweeps. *)
  Class CtxMorph (R : CtxId → iProp Σ) :=
    ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ ==∗ ctx_dom ξ ξ' ∗ R ξ'.

  (* The structural instances.  NOTE what is absent: no instance for
     [own_context] (the running-thread token never transfers by
     domination), and no blanket instance for persistent-but-ξ-dependent
     propositions (the clean lower bound is persistent AND pinned to its
     context).  ξ-CONSTANT propositions -- pure facts, ghost state,
     invariant handles, whole lock handles -- are covered by
     [ctx_morph_const]. *)

  (* LOW PRIORITY, and it is a guard, not a tuning: [ctx_morph_const]
     unifies with ANY payload whose context argument is still an evar
     ([?R := λ _, ?P]), so an eager resolution while a call site's payload
     is not yet pinned would silently commit it to a CONSTANT embedding.
     With the priority, the pointsto/structural instances win whenever the
     payload is known, and an evar payload stays pending until the framed
     [is_lock]/[R cur_ctx] hypothesis pins it -- which is what makes
     passing [_] for the payload at acquire/release call sites safe. *)
  Global Instance ctx_morph_const (P : iProp Σ) : CtxMorph (λ _, P) | 100.
  Proof. iIntros (ξ ξ') "Hd HP !>". iFrame. Qed.

  (* THE TRANSPORT OF A FACT ([TsoCtxTwin2.ctx_morph_pointsto]): a clean
     fact re-indexes by COPYING its justification (t ≤ B ≤ B', and ξ''s
     lb is persistent); a dirty one's timestamp sits under the watermark
     (t ≤ W ≤ B'), and its fragment is dropped -- the pinned key is a
     timestamp, never reused, so the leftover entry is inert. *)
  Global Instance ctx_morph_pointsto (kt : ktier) a dq v :
    CtxMorph (λ ξ, ctx_pointsto (KTR := kt) ξ a dq v).
  Proof.
    iIntros (ξ ξ') "Hd HP".
    rewrite ctx_dom_unseal /ctx_dom_def !ctx_pointsto_unseal /ctx_pointsto_def.
    iDestruct "Hd" as
      "(%B & %W & %B' & %D & [Hb Hdm] & %HDW & %HBB' & %HWB' & #Hlb')".
    iDestruct "HP" as "(%ppn & %t & #Hk & % & % & % & Hpt & Hts & Hbit)".
    iAssert (⌜(t ≤ B')%nat⌝)%I as %HtB'.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid_q with "Hb Hcl") as %HtB.
        iPureIntro. lia.
      - iDestruct (ghost_map_lookup with "Hdm Hdt") as %HDt.
        have HtW : ((t, pa_of ppn a).1 ≤ W)%nat
          by apply HDW; eapply elem_of_dom_2.
        simpl in HtW. iPureIntro. lia. }
    iClear "Hbit". iModIntro.
    iSplitL "Hb Hdm".
    { iExists B, W, B', D. iFrame "Hb Hdm Hlb'". by iPureIntro. }
    iExists ppn, t. iFrame "Hk Hpt Hts".
    iSplit; first done. iSplit; first done. iSplit; first done.
    iLeft. rewrite /llb. iLeft.
    iApply (mono_nat_lb_own_le with "Hlb'"). lia.
  Qed.

  Global Instance ctx_morph_sep (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR1 HR2]".
    iMod (ctx_morph with "Hd HR1") as "[Hd HR1]".
    iMod (ctx_morph with "Hd HR2") as "[Hd HR2]".
    iModIntro. iFrame.
  Qed.

  Global Instance ctx_morph_exist {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ ξ ξ') "Hd [%x HR]".
    iMod (ctx_morph with "Hd HR") as "[Hd HR]".
    iModIntro. iFrame "Hd". iExists x. iExact "HR".
  Qed.

  Global Instance ctx_morph_big_sepL {A} (l : list A)
      (Φ : nat → A → CtxId → iProp Σ) :
    (∀ i x, CtxMorph (Φ i x)) →
    CtxMorph (λ ξ, [∗ list] i ↦ x ∈ l, Φ i x ξ)%I.
  Proof.
    revert Φ. induction l as [|x l IH] => Φ HΦ.
    - iIntros (ξ ξ') "Hd _ !>". by iFrame.
    - iIntros (ξ ξ') "Hd [HR HRs]".
      iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iMod (IH (λ i y, Φ (S i) y) _ ξ ξ' with "Hd HRs") as "[Hd HRs]".
      iModIntro. iFrame.
  Qed.

  (* the word cell's transport obligation, once for every payload *)
  Global Instance ctx_morph_word (kt : ktier) a dq w :
    CtxMorph (λ ξ, ctx_word_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iMod (ctx_morph_big_sepL (seq 0 8)
            (λ _ j ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.

  (* … and the same for the stage-2 towers. *)
  Global Instance ctx_morph_word2 (kt : ktier) a dq w :
    CtxMorph (λ ξ, ctx_word2_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iMod (ctx_morph_big_sepL (seq 0 2)
            (λ _ j ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance ctx_morph_word4 (kt : ktier) a dq w :
    CtxMorph (λ ξ, ctx_word4_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iMod (ctx_morph_big_sepL (seq 0 4)
            (λ _ j ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.

  (* The composition acid test: a lock-payload-shaped assertion is
     morphable by typeclass search alone.  If this ever needs a manual
     proof, an instance regressed. *)
  Lemma ctx_morph_demo (kt : ktier) a1 a2 v1 (P : iProp Σ) :
    CtxMorph (λ ξ, ctx_pointsto (KTR := kt) ξ a1 (DfracOwn 1) v1 ∗
                   (∃ v2 : bv 8, ⌜v2 ≠ v1⌝ ∗
                      ctx_pointsto (KTR := kt) ξ a2 (DfracOwn 1) v2) ∗
                   P)%I.
  Proof. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (* The ctx_dom mints -- borrow accessors on the tokens               *)
  (* ---------------------------------------------------------------- *)

  (* RELEASE-SIDE / FORK-SIDE MINT, INTERP-FREE
     ([TsoCtxTwin2.ctx_dom_to_parked]): domination into a PARKED target.
     The target's stamp is raised to cover everything the source could
     deposit (its bound receipt K and its dirty watermark W -- both
     legal log positions by their [llb]s, so no interp is consulted).
     The give-back wand re-agrees the halves, so the source token comes
     back exactly as it went in. *)
  Lemma ctx_dom_to_parked `{CID : CpuId} (ξ ξ' : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξ' T ==∗
    ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξ' T' ∗ ctx_dom ξ ξ' ∗
          (ctx_dom ξ ξ' -∗ own_context ξ).
  Proof.
    iIntros "Hrun Hpk".
    iEval (rewrite own_context_unseal /own_context_def) in "Hrun".
    iEval (rewrite ctx_parked_unseal /ctx_parked_def) in "Hpk".
    iDestruct "Hrun" as "(%B & %K & %W & %D & Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hpk" as "(%D' & [Hb' Hd'] & #HT & %HD'T)".
    set (T' := Nat.max T (Nat.max K W)).
    iMod (mono_nat_own_update T' with "Hb'") as "[Hb' #Hlb']"; first lia.
    iModIntro. iExists T'.
    rewrite ctx_parked_unseal /ctx_parked_def ctx_dom_unseal /ctx_dom_def
            own_context_unseal /own_context_def.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iSplitR; first (iPureIntro; lia).
    iSplitL "Hb' Hd'".
    { iExists D'. iFrame "Hb' Hd'".
      iSplitR.
      { iApply (llb_max with "HT").
        iApply (llb_max with "[] HW"). by iApply view_lb_llb. }
      iPureIntro. intros k Hk. have := HD'T _ Hk. lia. }
    iSplitL "Hat1".
    { iExists B, W, T', D. iFrame "Hat1 Hlb'". iPureIntro.
      split_and!; [done | lia | lia]. }
    (* the give-back *)
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _ & _ & _ & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat".
    rewrite -ctx_at_halves.
    iExists B, K, W, D. iFrame "Hat HK HW Hoks". by iPureIntro.
  Qed.

  (* THE DEPOSIT: a running context hands ANY morphable payload to a
     PARKED one, the parked stamp raised to cover it -- so a fork's
     hand-me-downs (including bytes the parent wrote after the child's
     mint: uvmcopy) have NOTHING TO PROVE at the deposit site; the
     resumer's lock acquire pays the raised stamp.
     ([TsoCtxTwin2.twin_deposit], interp-free.) *)
  Lemma ctx_deposit `{CID : CpuId} (R : CtxId → iProp Σ) `{!CtxMorph R}
      (ξ ξc : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξc T -∗ R ξ ==∗
    own_context ξ ∗ ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξc T' ∗ R ξc.
  Proof.
    iIntros "Hrun Hpk HR".
    iMod (ctx_dom_to_parked ξ ξc T with "Hrun Hpk")
      as (T') "(%HTT' & Hpk & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iSplitL "Hback Hdom"; first by iApply "Hback".
    iExists T'. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE KIT-FACING GATES: where the surface meets the machine's        *)
  (* interpretation.  Consumed by the below-Σ leaf re-proofs against    *)
  (* the Ztso arms (tso-machine-flip.md §6); each is the image of a     *)
  (* TsoCtxTwin2 gate lemma at the live interp [tso_interp_at].         *)
  (* ---------------------------------------------------------------- *)

  (* the parked stamp's own log-length receipt, exported off the token
     ([TsoCtxTwin2.ctx_parked_llb]) -- what the proc-lock payload carries
     to the acquire leaf *)
  Lemma ctx_parked_llb ξ T :
    ctx_parked ξ T -∗ ctx_parked ξ T ∗ llb loglen_name T.
  Proof.
    rewrite ctx_parked_unseal /ctx_parked_def.
    iIntros "(%D & Hat & #HT & %HDT)".
    iSplitL "Hat"; last iExact "HT".
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  (* THE VIEW-RECEIPT MINT ([TsoCtxTwin2.twin_passed_get]): at the
     AMO-acquire leaf the hart's view sits at the log top, so the parked
     record's own [llb T] receipt yields the STABLE pair
     [hart_view_lb K ∗ ⌜T ≤ K⌝] that [ctx_resume]/[ctx_exchange]
     consume -- persistent-monotone, so it survives every step between
     the acquire and the swtch. *)
  Lemma hart_view_lb_get `{CID : CpuId} (g : gstate) (T : nat) :
    (length g.(glog) ≤ g.(gtv) cpu_id)%nat →
    tso_interp_at riscv_eraGS g -∗ llb loglen_name T -∗
    tso_interp_at riscv_eraGS g ∗
    hart_view_lb (g.(gtv) cpu_id) ∗ ⌜(T ≤ g.(gtv) cpu_id)%nat⌝.
  Proof.
    rewrite hart_view_lb_unseal /hart_view_lb_def.
    iIntros (Htop) "Hint #HT".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htv].
    iDestruct (llb_valid with "Hlen HT") as %HTlen.
    iDestruct (view_lb_get _ _ (avf g) (length g.(glog)) (hart_agent cpu_id)
                with "Hv Hlen") as "(Hv & Hlen & #Hrcpt)".
    { rewrite avf_hart. apply Htv. }
    rewrite avf_hart.
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iFrame "Hrcpt". iPureIntro. lia.
  Qed.

  (* ACQUIRE-SIDE MINT ([TsoCtxTwin2.ctx_dom_of_parked]): domination
     FROM a parked source INTO the running acquirer, whose hart sits at
     the log top (what the AMO delivers).  The one mint that needs the
     interp -- it must compare the source's stamp with the log length
     and raise the acquirer's bound to its hart's view. *)
  Lemma ctx_dom_of_parked `{CID : CpuId} (g : gstate) (ξ ξ' : CtxId) (T : nat) :
    (length g.(glog) ≤ g.(gtv) cpu_id)%nat →
    tso_interp_at riscv_eraGS g -∗ own_context ξ' -∗ ctx_parked ξ T ==∗
    tso_interp_at riscv_eraGS g ∗ own_context ξ' ∗
    ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_parked ξ T).
  Proof.
    rewrite own_context_unseal /own_context_def
            ctx_parked_unseal /ctx_parked_def ctx_dom_unseal /ctx_dom_def.
    iIntros (Htop) "Hint Hrun Hpk".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htv].
    iDestruct "Hrun"
      as "(%B' & %K & %W & %D' & [Hb' Hd'] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hpk" as "(%D & Hat & #HT & %HDT)".
    (* the source stamp is a legal log position, hence under the view *)
    iDestruct (llb_valid with "Hlen HT") as %HTlen.
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    (* raise the acquirer's bound to its (top) view *)
    iMod (mono_nat_own_update (g.(gtv) cpu_id) with "Hb'") as "[Hb' #Hlb']".
    { lia. }
    iDestruct (view_lb_get _ _ (avf g) (length g.(glog)) (hart_agent cpu_id)
                with "Hv Hlen") as "(Hv & Hlen & #Hrcpt)".
    { rewrite avf_hart. apply Htv. }
    rewrite avf_hart.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iModIntro.
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iSplitL "Hb' Hd'".
    { iExists (g.(gtv) cpu_id), (g.(gtv) cpu_id), W, D'. iFrame "Hb' Hd'".
      iSplitR; first iExact "Hrcpt".
      iSplitR; first done.
      iFrame "HW". iSplitR; first done.
      iApply (big_sepM_impl with "Hoks").
      iIntros "!>" (k [] Hk) "Hok".
      iApply (dirty_ok_mono with "Hok"). lia. }
    iSplitL "Hat1".
    { iExists T, T, (g.(gtv) cpu_id), D. iFrame "Hat1 Hlb'".
      iPureIntro. split_and!; [exact HDT | lia | lia]. }
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* A6.66 THE ACQUIRE-SIDE GATE, and at THIS machine it is honest.      *)
  (* [ctx_deposit] above is the release side and is INTERP-FREE (a       *)
  (* parked target's stamp may be raised at will).  Its dual is not:     *)
  (* claiming a parked record's facts INTO the running context needs the *)
  (* at-the-top evidence, because the claimer must show its own view     *)
  (* already covers the whole log -- that is [ctx_dom_of_parked]'s       *)
  (* [length glog ≤ gtv cpu_id] premise, and it is what the AMO leaf     *)
  (* actually establishes when it reads at the top.                      *)
  (*                                                                     *)
  (* THIS IS WHY THE FLIP MAKES THE LOCK KIT *BETTER*, NOT WORSE         *)
  (* (tso-port.md §0.18′): at SC the same lemma is provable with         *)
  (* [ctx_dom_unseal; done] and a CONJURED [hart_view_lb], because SC's  *)
  (* [ctx_dom] is vacuous.  Here the receipt is real and the conjured    *)
  (* lower bound has no role left at the acquire -- the interp supplies  *)
  (* it.  The premise is therefore a STRENGTHENING of the statement and  *)
  (* a WEAKENING of what the caller must invent.                         *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_absorb `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R}
      (g : gstate) (ξ ξ' : CtxId) (T : nat) :
    (length g.(glog) <= g.(gtv) cpu_id)%nat ->
    tso_interp_at riscv_eraGS g -∗
    own_context ξ' -∗ ctx_parked ξ T -∗ R ξ ==∗
    tso_interp_at riscv_eraGS g ∗ own_context ξ' ∗ ctx_parked ξ T ∗ R ξ'.
  Proof.
    iIntros (Htop) "Hint Hrun Hpk HR".
    iMod (ctx_dom_of_parked g ξ ξ' T Htop with "Hint Hrun Hpk")
      as "(Hint & Hrun & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iFrame "Hint Hrun HR". by iApply "Hback".
  Qed.


  (* THE LOAD GATE ([TsoCtxTwin2.twin_load_ok]): a running context's
     fact predicts the machine's plain load at EVERY admissible view
     advance of its hart -- both arms: a clean fact through the
     bound-under-view tie, a dirty one through the author/forwarding
     arm.  Any fraction; nothing is consumed.  This is what the
     [Mobl_ram_plain] leaf obligation (tso-machine-flip.md §6)
     discharges the arm's [tso_read] premise with; the gen_heap conjunct
     rides beside [tso_interp_at] because the fact's VALUE lives in the
     flat cell while its TIMESTAMP lives in the tso ghosts. *)
  Lemma ctx_load_ok `{CID : CpuId} {KTR : CurKtier} (g : gstate)
      (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_pointsto (KTR := KTR) ξ a dq v -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    own_context ξ ∗ ctx_pointsto (KTR := KTR) ξ a dq v ∗
    ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗
      ⌜∀ tv', (g.(gtv) cpu_id ≤ tv')%nat →
         tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_of ppn a)
         = Some v⌝.
  Proof.
    rewrite own_context_unseal /own_context_def
            ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "Hgh Hint Hrun Hfact".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htv].
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hfact"
      as "(%ppn & %t & #Hk & %Hc & %Hr & %Hpin & Hpt & Htse & Hbit)".
    (* the flat cell pins the value; the timestamp ghost pins its t *)
    iDestruct (gen_heap_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    (* the hart's view dominates the context's bound *)
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    (* visibility of [t], by the bit *)
    iAssert (⌜∀ tv', (g.(gtv) cpu_id ≤ tv')%nat →
               visibleb (hart_agent cpu_id) tv' g.(glog) t = true⌝)%I
      as %Hvis.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - (* clean: t ≤ B ≤ K ≤ gtv ≤ tv' -- and on [llb]'s [t = 0] arm,
           [0 ≤ tv'] outright (the image byte needs no bound at all) *)
        iDestruct (llb_valid with "Hb Hcl") as %HtB.
        iPureIntro. intros tv' Htv'. apply visibleb_below. lia.
      - (* dirty: the bundle's justification *)
        iDestruct (ghost_map_lookup with "Hd Hdt") as %HDt.
        iDestruct (big_sepM_lookup _ _ _ _ HDt with "Hoks") as "[%HtB | Hown]".
        + iPureIntro. intros tv' Htv'. apply visibleb_below.
          simpl in HtB. lia.
        + iDestruct "Hown" as (i m) "(%Hti & Hi & %Htid)".
          iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
          iPureIntro. intros tv' _. simpl in Hti. rewrite Hti.
          apply (visibleb_own _ _ _ _ m); [by rewrite -HLM | done]. }
    (* reassemble everything *)
    iSplitL "Hgh"; first iExact "Hgh".
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iSplitL "Hb Hd".
    { iExists B, K, W, D. iFrame "Hb Hd HK HW Hoks". by iPureIntro. }
    iSplitL.
    { iExists ppn, t. iFrame "Hk Hpt Htse Hbit". by iPureIntro. }
    iExists ppn. iFrame "Hk". iPureIntro.
    intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|by apply Hvis].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE PRISTINE BYTE, and the load gate that needs NO context         *)
  (* (tso-machine-flip.md §6 amendment A6.10).                          *)
  (*                                                                   *)
  (* [ctx_load_ok] above is the general gate and it costs a ledger fact *)
  (* plus a running token.  There is a second, much cheaper one, and it *)
  (* is the RAW tiers' only honest way to discharge §6's                 *)
  (* [Mobl_ram_plain]: a byte whose LATEST WRITE IS THE ERA IMAGE --     *)
  (* timestamp 0 -- is visible to EVERY agent at EVERY view             *)
  (* ([TsoMemPa.read_down_0]: [visibleb h tv log 0] is unconditionally   *)
  (* true), so its value is the same no matter where the loading hart's  *)
  (* view sits and no matter who else is running.  This is the standing  *)
  (* text-is-timestamp-0 ruling, stated as a RESOURCE and extended from  *)
  (* text to every never-written image byte.                             *)
  (*                                                                   *)
  (* THE RESOURCE IS THE TIMESTAMP ELEMENT AT 0, DISCARDED.  Persistent  *)
  (* and duplicable, so it costs a holder nothing and can be handed to   *)
  (* every consumer of an image byte at once; and DISCARDED is exactly   *)
  (* the right strength, because it also says the byte can never be      *)
  (* STORED to again (a store must UPDATE the element, which a discarded *)
  (* one forbids).  Read-only-forever and readable-from-anywhere are the *)
  (* same fact here, which is why one resource says both.                *)
  (*                                                                   *)
  (* WHO MINTS IT: the era's initial-state ghosts (step 6 / adequacy),   *)
  (* beside [kernel_text]/[kernel_data]'s own mints -- the image is      *)
  (* where timestamp 0 comes from.  WHO CONSUMES IT: every raw-tier load *)
  (* of an image byte, [WpMmodeLoad]'s [phys_word_pointsto] leaf first   *)
  (* (see the amendment for the exact statement it wants).              *)
  (* ---------------------------------------------------------------- *)
  (* A6.63 / carve Q3: THE ALIAS.  This was a character-for-character
     duplicate of [RiscvPtsto.pristine_elem] under a second name, which is
     how the two drift apart.  DIRECTION IS FIXED BY IMPORT ORDER: TsoCtx
     imports RiscvPtsto, so [pristine_elem] is the definition and this is
     the alias -- never the other way round.  Kept as a [Definition] (not a
     [Notation]) so the two persistence/timeless instances below and every
     existing [rewrite /pristine_byte] keep working; the bodies are
     convertible, so no proof in the tree changes. *)
  Definition pristine_byte (a : Arch.pa) : iProp Σ := pristine_elem a.

  Global Instance pristine_byte_persistent a : Persistent (pristine_byte a).
  Proof. rewrite /pristine_byte. apply _. Qed.
  Global Instance pristine_byte_timeless a : Timeless (pristine_byte a).
  Proof. rewrite /pristine_byte. apply _. Qed.

  Definition pristine_win (a : Arch.pa) (n : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n, pristine_byte (pa_add a j))%I.

  Global Instance pristine_win_persistent a n : Persistent (pristine_win a n).
  Proof. rewrite /pristine_win. apply _. Qed.

  (* THE GATE.  Note what is NOT quantified away: the conclusion holds at
     EVERY agent and EVERY view, so a caller does not have to know its own
     hart's view, its context's bound, or the log's length.  That is the
     whole point -- it is the one load fact a raw byte can carry. *)
  Lemma pristine_read_ok (g : gstate) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    phys_pointsto a dq v -∗ pristine_byte a -∗
    ⌜∀ (h : agent) (tv : nat), tso_read g.(gimg) g.(glog) h tv a = Some v⌝.
  Proof.
    iIntros "Hgh Hint Hpt #Hpr".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (ghost_map_lookup with "Hts Hpr") as %HTM.
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iPureIntro. intros h tv.
    apply (tso_read_of_latest _ _ _ _ _ 0%nat); [exact Hlat|].
    apply visibleb_below. lia.
  Qed.

  (* the window form, in the shape [HartMLoad.robl_ram] is stated at --
     [∀ tv'] with no lower bound at all, so the caller's [tv <= tv'] and
     [tv' <= length log] premises are simply not needed *)
  Lemma pristine_read_bytes_ok (g : gstate) (a : Arch.pa) (n : N) {m : N}
      (w : bv m) (dq : dfrac) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_pointsto (pa_add a j) dq (nth_byte w j)) -∗
    pristine_win a (N.to_nat n) -∗
    ⌜∀ (h : agent) (tv : nat),
       tso_read_bytes g.(gimg) g.(glog) h tv a n w⌝.
  Proof.
    iIntros "Hgh Hint Hb #Hpr".
    iAssert (⌜∀ j : nat, (N.of_nat j < n)%N →
               ∀ (h : agent) (tv : nat),
                 tso_read g.(gimg) g.(glog) h tv (pa_add a j)
                 = Some (nth_byte w j)⌝)%I with "[Hgh Hint Hb]" as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hpr")
        as "Hprj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (pristine_read_ok g (pa_add a j) dq (nth_byte w j)
                with "Hgh Hint Hbj Hprj"). }
    iPureIntro. intros h tv j Hj. exact (HH j Hj h tv).
  Qed.

  (* THE IMAGE MINT -- and the reason the clean arm is [llb]-shaped.  A
     DISCARDED byte plus its pristine receipt IS a ledger fact, at EVERY
     context, with NO ghost step and NO update modality: the timestamp
     element is the pristine one (discarded, so the fractions line up
     exactly) and the justification is [llb]'s [t = 0] arm, which mentions
     no context.  This is what makes the ∀-context image resources
     ([KernelDataInv.kernel_data]'s [∀ ξ, …], kernel text) MINTABLE: with a
     bare [mono_nat_lb_own] the mint would need one bupd per context, i.e.
     infinitely many under the ∀, and the boot carve could not build the
     fact it hands the whole tree.

     [ppn] is passed explicitly and pinned by the caller's own [kmap_at]
     ([kmap_at_agree]), because the mem fact's page number is existential
     and the pristine receipt lives at the PHYSICAL address. *)
  Lemma ctx_pointsto_of_pristine `{KTR : !CurKtier} (ξ : CtxId)
      (ppn : mword 44) (a : Arch.pa) (v : bv 8) :
    kmap_at (svpn_of a) ppn KP_rw -∗
    mem_pointsto a DfracDiscarded v -∗
    pristine_byte (pa_of ppn a) -∗
    ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    rewrite ctx_pointsto_unseal /ctx_pointsto_def /mem_pointsto.
    iIntros "#Hk (%ppn' & #Hk' & %Hc & %Hr & %Hp & Hpt) #Hpr".
    iDestruct (kmap_at_agree with "Hk Hk'") as %[<- _].
    iExists ppn, 0%nat. iFrame "Hk Hpt Hpr".
    iSplit; first done. iSplit; first done. iSplit; first done.
    iLeft. iApply llb_0.
  Qed.

  (* … and the form the boot carve actually wants: every premise is
     persistent, so the ∀ costs nothing. *)
  Lemma ctx_pointsto_of_pristine_all `{KTR : !CurKtier}
      (ppn : mword 44) (a : Arch.pa) (v : bv 8) :
    kmap_at (svpn_of a) ppn KP_rw -∗
    mem_pointsto a DfracDiscarded v -∗
    pristine_byte (pa_of ppn a) -∗
    ∀ ξ : CtxId, ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    iIntros "#Hk #Hm #Hpr" (ξ).
    iApply (ctx_pointsto_of_pristine ξ ppn a v with "Hk Hm Hpr").
  Qed.

  (* THE VA-SIDE RECEIPT, which is the one a caller can actually hold.
     [pristine_byte] lives at a PHYSICAL address (the interpretation is keyed
     there), while every consumer of an image byte names it by its VA and
     does not know the page number -- so the receipt carries its own page
     claim, and [kmap_at_agree] is what lets it meet the [mem_pointsto]'s
     existential.  Persistent, like both of its conjuncts. *)
  Definition pristine_va `{KTR : !CurKtier} (a : Arch.pa) : iProp Σ :=
    (∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗ pristine_byte (pa_of ppn a))%I.

  Global Instance pristine_va_persistent `{KTR : !CurKtier} a :
    Persistent (pristine_va a).
  Proof. rewrite /pristine_va. apply _. Qed.

  Lemma ctx_pointsto_of_pristine_va `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (v : bv 8) :
    mem_pointsto a DfracDiscarded v -∗ pristine_va a -∗
    ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    iIntros "Hm (%ppn & #Hk & #Hpr)".
    iApply (ctx_pointsto_of_pristine ξ ppn a v with "Hk Hm Hpr").
  Qed.

  (* the every-context form: THE BOOT MINT.  A persisted image byte plus its
     receipt IS [KernelDataInv.kernel_data]'s per-byte conjunct at every
     context at once. *)
  Lemma ctx_pointsto_of_pristine_va_all `{KTR : !CurKtier}
      (a : Arch.pa) (v : bv 8) :
    mem_pointsto a DfracDiscarded v -∗ pristine_va a -∗
    ∀ ξ : CtxId, ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    iIntros "#Hm #Hpr" (ξ).
    iApply (ctx_pointsto_of_pristine_va ξ a v with "Hm Hpr").
  Qed.

  (* ================================================================== *)
  (* THE PHYSICAL LEDGER BYTE, AND THE STORE GATE                       *)
  (* (tso-machine-flip.md §6 amendment A6.16)                           *)
  (*                                                                   *)
  (* WHY A SECOND BYTE FAMILY AT ALL.  [ctx_pointsto] is keyed by VA and *)
  (* carries [mem_pointsto]'s kernel-mapping plumbing; the MACHINE, and  *)
  (* every one of A6.14's four members, works at PHYSICAL addresses --   *)
  (* [HartMemRun.bytes_own] is a [gmap Arch.pa], [WpMmodeStore] and      *)
  (* [KptTree] hold [↦ₚ₈], the DMA lease is a [phys_map].  So the ledger *)
  (* fact those tiers need is [phys_pointsto] PLUS the timestamp element *)
  (* PLUS the clean/dirty bit -- [ctx_pointsto]'s body with the VA       *)
  (* plumbing stripped off, which is exactly what the era interp and the *)
  (* twin's gates are stated over ([pristine_byte] is already keyed      *)
  (* physically, for the same reason).                                   *)
  (*                                                                   *)
  (* IT IS NOT A NEW TIER: [ctx_pointsto_phys] below is a [⊣⊢], so the   *)
  (* VA family IS the kmap claim over this one.  The gates are stated    *)
  (* here, once, and the VA forms are corollaries.                       *)
  (* ================================================================== *)
  Definition ctx_phys_pointsto_def (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) : iProp Σ :=
    (∃ t : nat,
       phys_pointsto a dq v ∗
       a ↪[ts_name]{dq} (t, None) ∗
       (llb (ctx_bound_name ξ) t                          (* CLEAN *)
        ∨ (t, a) ↪[ctx_dirty_name ξ]{dq} ()))%I.          (* DIRTY *)
  Lemma ctx_phys_pointsto_aux : { f | f = ctx_phys_pointsto_def }.
  Proof. by eexists. Qed.
  Definition ctx_phys_pointsto (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) : iProp Σ := proj1_sig ctx_phys_pointsto_aux ξ a dq v.
  Lemma ctx_phys_pointsto_unseal (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) :
    ctx_phys_pointsto ξ a dq v = ctx_phys_pointsto_def ξ a dq v.
  Proof.
    unfold ctx_phys_pointsto. by rewrite (proj2_sig ctx_phys_pointsto_aux).
  Qed.

  Global Instance ctx_phys_pointsto_timeless ξ a dq v :
    Timeless (ctx_phys_pointsto ξ a dq v).
  Proof. rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def. apply _. Qed.
  Global Instance ctx_phys_pointsto_discarded_persistent ξ a v :
    Persistent (ctx_phys_pointsto ξ a DfracDiscarded v).
  Proof. rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def. apply _. Qed.

  (* the forgetful projection at this tier (A6.8's price, same words) *)
  Lemma ctx_phys_pointsto_forget ξ a dq v :
    ctx_phys_pointsto ξ a dq v ⊢ phys_pointsto a dq v.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    by iIntros "(% & $ & _)".
  Qed.

  Lemma ctx_phys_pointsto_ram ξ a dq v :
    ctx_phys_pointsto ξ a dq v ⊢ ⌜addr_is_ram a⌝.
  Proof.
    rewrite ctx_phys_pointsto_forget /phys_pointsto. by iIntros "[_ $]".
  Qed.

  Lemma ctx_phys_pointsto_agree ξ1 ξ2 a dq1 b1 dq2 b2 :
    ctx_phys_pointsto ξ1 a dq1 b1 -∗ ctx_phys_pointsto ξ2 a dq2 b2 -∗
    ⌜b1 = b2⌝.
  Proof.
    rewrite !ctx_phys_pointsto_forget /phys_pointsto.
    iIntros "[H1 _] [H2 _]".
    by iDestruct (pointsto_agree with "H1 H2") as %->.
  Qed.

  (* THE VA FAMILY IS THIS ONE UNDER THE KMAP CLAIM.  Both directions:
     the ledger residue never moves, only the mapping plumbing does. *)
  Lemma ctx_pointsto_phys `{KTR : !CurKtier} (ξ : CtxId) (va : Arch.pa)
      (dq : dfrac) (v : bv 8) :
    ctx_pointsto ξ va dq v ⊣⊢
    ∃ ppn : mword 44,
      kmap_at (svpn_of va) ppn KP_rw ∗
      ⌜(uint va < 274877906944)%Z⌝ ∗
      ⌜ktier_pin cur_ktier ppn va⌝ ∗
      ctx_phys_pointsto ξ (pa_of ppn va) dq v.
  Proof.
    iSplit.
    - rewrite ctx_pointsto_unseal /ctx_pointsto_def.
      iIntros "(%ppn & %t & #Hk & %Hc & %Hr & %Hp & Hpt & Hts & Hbit)".
      iExists ppn. iFrame "Hk". iSplit; [done|]. iSplit; [done|].
      rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /phys_pointsto.
      iExists t. iFrame "Hpt Hts Hbit". by iPureIntro.
    - iIntros "(%ppn & #Hk & %Hc & %Hp & Hb)".
      rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /phys_pointsto
              ctx_pointsto_unseal /ctx_pointsto_def.
      iDestruct "Hb" as "(%t & [Hpt %Hr] & Hts & Hbit)".
      iExists ppn, t. iFrame "Hk Hpt Hts Hbit". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* A6.61: THE TIER WEAKENING, the ctx twin of                        *)
  (* [RiscvPtsto.mem_ktier_mono].  It is the one kit item the owners'   *)
  (* mechanical residue needed and the tree did not have: four sites    *)
  (* ([ProofCreateParts] x2, [ProofForkretParts], [ProofKexecTail])     *)
  (* reached KT1 from a KT0 datum by dropping to the raw tower, using   *)
  (* [mem_ktier_mono] there and crossing back -- and the return leg is  *)
  (* the direction the flip makes FALSE.                                *)
  (*                                                                    *)
  (* It is sound for EXACTLY the raw lemma's reason and no new one: of  *)
  (* the seven conjuncts of [ctx_pointsto_def] only [ktier_pin] mentions*)
  (* the tier, and it weakens ([ktier_pin_mono]; at KT1 there is nothing*)
  (* to prove).  The timestamp, the ledger element and the clean/dirty  *)
  (* bit are tier-BLIND -- which is why this is a weakening and not a   *)
  (* re-mint, and why A6.9's prohibition is not in play.                *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'}
      (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_pointsto (KTR := kt) ξ a dq v ⊢ ctx_pointsto (KTR := kt') ξ a dq v.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & #Hk & %Hc & %Hr & %Hp & Hpt & Hts & Hbit)".
    iExists ppn, t. iFrame "Hk Hpt Hts Hbit".
    iPureIntro. split_and!.
    - exact Hc.
    - exact Hr.
    - exact (ktier_pin_mono kt kt' ppn a Hp).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The per-byte half of the store gate.  THE THREE AUTHORITIES that   *)
  (* hold a ledger byte -- gen_heap (the flat cell), [ts_name] (the     *)
  (* timestamp) and ξ's own dirty set -- move together over the write's *)
  (* whole footprint, in ONE modality, against ONE appended message.     *)
  (* A byte at a time would be a message at a time, i.e. a different    *)
  (* machine, so this loop is primitive and not a fold of a byte gate.   *)
  (* ---------------------------------------------------------------- *)
  Local Lemma ctx_store_bytes (ξ : CtxId) (h : agent) (B i : nat)
      (msg : pwmsg) (Pold Pnew mem : gmap Arch.pa (bv 8))
      (TM : gmap Arch.pa ts_elem) (D : gmap (nat * Arch.pa) unit) :
    dom Pold = dom Pnew ->
    (forall k, k ∈ dom D -> (k.1 <= i)%nat) ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    ghost_map_auth ts_name 1 TM -∗
    ghost_map_auth (ctx_dirty_name ξ) 1 D -∗
    ([∗ map] a ↦ v ∈ Pold, ctx_phys_pointsto ξ a (DfracOwn 1) v) ==∗
    ∃ D' : gmap (nat * Arch.pa) unit,
      ⌜dom Pnew ⊆ dom mem⌝ ∗
      ⌜forall k, k ∈ dom D' <-> (k ∈ dom D \/ (k.1 = S i /\ k.2 ∈ dom Pnew))⌝ ∗
      gen_heap_interp (hG := riscv_memGS) (Pnew ∪ mem) ∗
      ghost_map_auth ts_name 1 (((fun _ => (S i, None)) <$> Pnew) ∪ TM) ∗
      ghost_map_auth (ctx_dirty_name ξ) 1 D' ∗
      ([∗ map] a ↦ v ∈ Pnew,
         phys_pointsto a (DfracOwn 1) v ∗ a ↪[ts_name] (S i, None) ∗
         (S i, a) ↪[ctx_dirty_name ξ] ()).
  Proof.
    revert Pold. induction Pnew as [|a vn P2 Hfresh IH] using map_ind;
      intros Pold Hdom HD.
    - (* empty footprint: nothing moves *)
      rewrite dom_empty_L in Hdom.
      apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hgh Hts Hd _". iModIntro. iExists D.
      rewrite fmap_empty !left_id_L !big_sepM_empty.
      iFrame "Hgh Hts Hd". iPureIntro. split; first set_solver.
      intros k. rewrite dom_empty_L. set_solver.
    - iIntros "Hgh Hts Hd Hold".
      (* pull the byte's OLD entry out of [Pold] *)
      assert (Ha : a ∈ dom Pold).
      { rewrite Hdom dom_insert_L. set_solver. }
      apply elem_of_dom in Ha as [vo Hvo].
      iDestruct (big_sepM_delete _ _ a vo Hvo with "Hold") as "[Hb Hrest]".
      assert (Hdom2 : dom (delete a Pold) = dom P2).
      { rewrite dom_delete_L Hdom dom_insert_L.
        assert (a ∉ dom P2) by (by apply not_elem_of_dom). set_solver. }
      iMod (IH (delete a Pold) Hdom2 HD with "Hgh Hts Hd Hrest")
        as "(%D2 & %Hsub2 & %HD2 & Hgh & Hts & Hd & Hbig)".
      (* now the one byte *)
      rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
      iDestruct "Hb" as "(%t & Hpt & Hte & Hbit)".
      iDestruct (phys_valid with "Hgh Hpt") as %Hmem.
      iMod (phys_update _ a vo vn with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update (S i, None) with "Hts Hte") as "[Hts Hte]".
      (* the dirty key is FRESH: every old key is at or below [i] and every
         key this loop has added names an address of [P2], which [a] is not *)
      assert (Hfr : D2 !! (S i, a) = None).
      { destruct (D2 !! (S i, a)) as [[]|] eqn:Hlk; last done. exfalso.
        assert (Hin : (S i, a) ∈ dom D2) by (by apply elem_of_dom_2 in Hlk).
        apply HD2 in Hin as [Hin|[_ Hin]].
        - have := HD _ Hin. simpl. lia.
        - simpl in Hin. by apply not_elem_of_dom in Hfresh. }
      iMod (ghost_map_insert (S i, a) () Hfr with "Hd") as "[Hd Hdt]".
      iClear "Hbit". iModIntro.
      iExists (<[(S i, a) := ()]> D2).
      rewrite fmap_insert -!insert_union_l !big_sepM_insert //.
      iFrame "Hgh Hts Hd Hbig Hpt Hte Hdt".
      iPureIntro. split.
      { rewrite dom_insert_L. apply union_least; [|exact Hsub2].
        assert (Hin : a ∈ dom mem).
        { apply elem_of_dom_2 in Hmem. rewrite dom_union_L elem_of_union in Hmem.
          destruct Hmem as [Hx|Hx]; last done.
          apply not_elem_of_dom in Hfresh. set_solver. }
        set_solver. }
      intros k. rewrite dom_insert_L elem_of_union elem_of_singleton
                        dom_insert_L.
      split.
      + intros [->|Hk]; first (right; simpl; set_solver).
        apply HD2 in Hk as [Hk|[Hk1 Hk2]]; [by left|]. right. set_solver.
      + intros [Hk|[Hk1 Hk2]]; first (right; apply HD2; by left).
        apply elem_of_union in Hk2 as [Hk2|Hk2].
        * apply elem_of_singleton in Hk2. left. destruct k; cbn in *. by subst.
        * right. apply HD2. right. by split.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE STORE GATE ([TsoCtxTwin2.twin_store_ok] at the surface types;  *)
  (* tso-machine-flip.md §6's [Wobl_ram]).  A running context's OWNED   *)
  (* footprint is written, publishing ONE message authored by the       *)
  (* ambient hart, and the append's four ghost steps are paid here:     *)
  (*   (1) every byte's [ts_name] element moves to the new top;         *)
  (*   (2) the message is PERSISTED in the log map (append-only, so     *)
  (*       stable -- it is what carries the dirty entries' author tie); *)
  (*   (3) the log-length [mono_nat] is bumped;                          *)
  (*   (4) each written byte's entry is INSERTED into ξ's dirty set at  *)
  (*       the new timestamp, and the running token's watermark rises.  *)
  (* The bytes come back DIRTY -- visible to this hart by the           *)
  (* forwarding arm, to any other only after a park raises the bound.   *)
  (*                                                                   *)
  (* NO RECEIPT AND NO VIEW MOVE: a plain store is buffered (§2), which *)
  (* is why the post-state's [gtv] is the pre-state's.  The AMO half    *)
  (* takes the view past its own append and mints its receipt in the    *)
  (* leaf (A6.6(b)), not here.                                          *)
  (*                                                                   *)
  (* THE POST-STATE IS GIVEN BY FIELD EQUATIONS rather than built: the  *)
  (* leaf already has the machine's successor state in hand and only    *)
  (* the four fields [tso_interp_at] reads are constrained, so this     *)
  (* form applies without a [gs_of] round trip on the way out.  The     *)
  (* memory equation is spelled [Pnew ∪ mem], which is exactly          *)
  (* [TsoMemPa.write_bytes_union]'s reading of the arm's [write_bytes]. *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_store_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (Pold Pnew : gmap Arch.pa (bv 8)) :
    dom Pold = dom Pnew ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew (hart_agent cpu_id)])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (* THE VIEW MOVES MONOTONELY OR NOT AT ALL.  A plain store buffers, so
       the author's entry does not move and this is an equality; the AMO /
       conditional half takes the view PAST its own append, which is still
       a legal post-state -- [own_context]'s receipt is a LOWER bound and
       views only grow, so nothing in the running token is falsified. *)
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ map] a ↦ v ∈ Pold, ctx_phys_pointsto ξ a (DfracOwn 1) v) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ map] a ↦ v ∈ Pnew, ctx_phys_pointsto ξ a (DfracOwn 1) v).
  Proof.
    iIntros (Hdom Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hold".
    rewrite own_context_unseal /own_context_def.
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdomtm & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htvok].
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    (* (2) the message is persisted, at slot [length glog] *)
    set (msg := PWMsg Pnew (hart_agent cpu_id)).
    iDestruct (llb_valid with "Hlen HW") as %HWlen.
    assert (HLMfresh : LM !! length g.(glog) = None).
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length g.(glog)) msg HLMfresh with "Hm")
      as "[Hm #Hlogm]".
    (* (3) the length bump *)
    iMod (mono_nat_own_update (length g'.(glog)) with "Hlen") as "[Hlen #Hlb]".
    { rewrite Hlog length_app /=. lia. }
    (* (1) + (4): the footprint *)
    assert (HDi : forall k, k ∈ dom D -> (k.1 <= length g.(glog))%nat).
    { intros k Hk. have := HDW _ Hk. lia. }
    iMod (ctx_store_bytes ξ (hart_agent cpu_id) B (length g.(glog)) msg
            Pold Pnew g.(gmem) TM D Hdom HDi with "Hgh Hts Hd Hold")
      as "(%D' & %Hsub & %HD' & Hgh & Hts & Hd & Hbig)".
    assert (Hlen' : length g'.(glog) = S (length g.(glog))).
    { rewrite Hlog length_app /=. lia. }
    (* THE ONE VIEW MOVE A PLAIN STORE MAKES, and it is not the author's:
       every BUS-MASTER agent is pinned to the top (RULING 2), so the
       append carries the disk's view with it.  The harts, this one
       included, keep theirs -- store buffering. *)
    assert (Havf : forall x, (avf g x <= avf g' x)%nat).
    { intros x. rewrite /avf Hlog length_app /=.
      destruct (lt_dec x NCPU) as [Hx|Hx]; [apply Htv | lia]. }
    iMod (view_auth_update _ (avf g) (avf g') Havf with "Hv") as "Hv".
    iModIntro.
    iSplitL "Hgh"; first by rewrite Hmem.
    iSplitL "Hts Hm Hlen Hv".
    { iExists (((fun _ : bv 8 => ((S (length g.(glog)), None) : ts_elem)) <$> Pnew) ∪ TM),
              (<[length g.(glog) := msg]> LM).
      iFrame "Hts Hm Hlen Hv".
      iSplitR.
      { iPureIntro.
        rewrite dom_union_L dom_fmap_L Hmem dom_union_L Hdomtm.
        by rewrite (subseteq_union_1_L _ _ Hsub). }
      iSplitR.
      { (* THE ELEMENT TIE, both halves.  The written bytes' elements are
           UNPINNED by definition of the payer ([ctx_phys_pointsto] pins
           the option to [None]), so their new elements are unpinned too
           and owe only the latest tie; and an address OUTSIDE the
           footprint has [msg_byte msg a = None], which is
           [TsoMemPa.pin_ok_app]'s free arm -- so an unpinned store gate
           needs no new premise (tso-pin-memo.md §5.3). *)
        iPureIntro. intros a e Hlk.
        destruct (Pnew !! a) as [vn|] eqn:Hpa.
        - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), None) : ts_elem)) <$> Pnew) !! a
                       = Some ((S (length g.(glog)), None) : ts_elem))
            by (rewrite lookup_fmap Hpa //).
          rewrite (lookup_union_Some_l _ _ _ _ Hl) in Hlk.
          injection Hlk as <-.
          apply (ts_ok_unpinned _ _ _ _ _ vn).
          { rewrite Hmem. by apply lookup_union_Some_l. }
          rewrite Hlog Himg. apply latest_app_new. by rewrite /msg_byte /=.
        - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), None) : ts_elem)) <$> Pnew) !! a = None)
            by (rewrite lookup_fmap Hpa //).
          rewrite (lookup_union_r _ _ _ Hl) in Hlk.
          pose proof (Htie _ _ Hlk) as Hok.
          assert (Hmb : msg_byte msg a = None) by (rewrite /msg_byte /=; exact Hpa).
          split.
          + destruct (ts_ok_latest _ _ _ _ _ Hok) as (v0 & Hgm & Hlat).
            exists v0. split.
            { rewrite Hmem. by rewrite lookup_union_r. }
            rewrite Hlog Himg. by apply latest_app_frame.
          + intros Sv Bp He2. rewrite Hlog Himg.
            apply (pin_ok_app_frame _ _ _ _ _ _
                     (ts_ok_pin _ _ _ _ _ _ _ Hok He2) Hmb). }
      iSplitR.
      { iPureIntro. intros j. rewrite Hlog.
        destruct (decide (j = length g.(glog))) as [->|Hne].
        - rewrite lookup_insert. symmetry. by apply list_lookup_middle.
        - rewrite lookup_insert_ne; last congruence. rewrite HLM.
          destruct (decide (j < length g.(glog))%nat) as [Hlt|Hge].
          + by rewrite lookup_app_l.
          + rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia. }
      iPureIntro. split.
      - rewrite Hmem Hlog Himg flat_snoc /=. by rewrite -Hflat.
      - intros c. have := Htvok' c. lia. }
    iSplitL "Hb Hd".
    { iExists B, K, (length g'.(glog)), D'. iFrame "Hb Hd HK".
      iSplitR; first done.
      iSplitR; first (iLeft; iExact "Hlb").
      iSplitR.
      { iPureIntro. intros k Hk. apply HD' in Hk as [Hk|[Hk1 _]].
        - have := HDW _ Hk. lia.
        - rewrite Hk1 Hlen'. lia. }
      iApply big_sepM_intro. iIntros "!>" (k [] Hk).
      assert (Hk' : k ∈ dom D') by (by eapply elem_of_dom_2).
      apply HD' in Hk' as [Hin|[Hk1 _]].
      - apply elem_of_dom in Hin as [[] Hin].
        by iApply (big_sepM_lookup _ _ _ _ Hin with "Hoks").
      - iRight. iExists (length g.(glog)), msg. iFrame "Hlogm".
        by iPureIntro. }
    iApply (big_sepM_mono with "Hbig").
    iIntros (a v _) "(Hpt & Hte & Hdt)".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iExists (S (length g.(glog))). iFrame "Hpt Hte". by iRight.
  Qed.

  (* ================================================================== *)
  (* THE WRITE-ONLY LEDGER BYTE, AND THE CONTEXT-FREE STORE GATE        *)
  (* (tso-machine-flip.md §6 amendment A6.20)                           *)
  (*                                                                   *)
  (* A store's four ghost steps need the TIMESTAMP ELEMENTS.  They do    *)
  (* NOT need a context: the clean/dirty BIT is what licenses a later    *)
  (* plain LOAD, and a byte nobody loads through the ledger does not     *)
  (* need one.  Dropping it gives a resource that                        *)
  (*   - can be stored to for ever (it holds the element), and           *)
  (*   - licenses no plain load (it holds no bit),                       *)
  (* which is exactly right for memory that is WRITTEN by one tier and   *)
  (* READ through a strongly-ordered arm.                                *)
  (*                                                                   *)
  (* ITS CONSUMER IS THE PAGE TABLE, and that is why it exists.  The     *)
  (* kernel page table's slots live inside a BARE [inv] shared by every  *)
  (* S-mode thread ([KptShare.kpt_inv]), so its body cannot name a       *)
  (* context (tso-port.md §0.8' ruling 2) -- and it does not have to:    *)
  (* a PTE is read at [Read_ttw], RULING 1's FLAT arm, so no load        *)
  (* license is ever wanted, while the Svadu A/D write-back is a real    *)
  (* store and owes the append.  Context-free ledger is the ONLY sound   *)
  (* shape there and it is also the cheapest.                            *)
  (*                                                                   *)
  (* (A6.17 measured this shape at [WpMmodeStore] and rejected it there, *)
  (* because [own_context] already arrives at the M-mode bracket and a   *)
  (* loadable byte is strictly stronger.  Here the judgement reverses:   *)
  (* [own_context] CANNOT be used, because the owner is an invariant.)   *)
  (* ================================================================== *)
  Definition phys_ledger_def (a : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat, phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, None))%I.
  Lemma phys_ledger_aux : { f | f = phys_ledger_def }.
  Proof. by eexists. Qed.
  Definition phys_ledger (a : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    proj1_sig phys_ledger_aux a dq v.
  Lemma phys_ledger_unseal (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    phys_ledger a dq v = phys_ledger_def a dq v.
  Proof. unfold phys_ledger. by rewrite (proj2_sig phys_ledger_aux). Qed.

  Global Instance phys_ledger_timeless a dq v : Timeless (phys_ledger a dq v).
  Proof. rewrite phys_ledger_unseal /phys_ledger_def. apply _. Qed.

  Lemma phys_ledger_forget a dq v : phys_ledger a dq v ⊢ phys_pointsto a dq v.
  Proof.
    rewrite phys_ledger_unseal /phys_ledger_def. by iIntros "(% & $ & _)".
  Qed.

  (* two ledger bytes, one of them fully owned, cannot name the same address
     -- the DMA lease's disjointness argument, at the sealed tier (A6.48) *)
  Lemma phys_ledger_ne (a1 a2 : Arch.pa) (dq2 : dfrac) (v1 v2 : bv 8) :
    phys_ledger a1 (DfracOwn 1) v1 -∗ phys_ledger a2 dq2 v2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (phys_ledger_forget with "H1") as "Hp1".
    iDestruct (phys_ledger_forget with "H2") as "Hp2".
    iEval (rewrite /phys_pointsto) in "Hp1". iDestruct "Hp1" as "[Hp1 _]".
    iEval (rewrite /phys_pointsto) in "Hp2". iDestruct "Hp2" as "[Hp2 _]".
    by iDestruct (pointsto_ne with "Hp1 Hp2") as %?.
  Qed.

  Lemma phys_ledger_ram a dq v : phys_ledger a dq v ⊢ ⌜addr_is_ram a⌝.
  Proof.
    iIntros "H". iDestruct (phys_ledger_forget with "H") as "Hp".
    iEval (rewrite /phys_pointsto) in "Hp". by iDestruct "Hp" as "[_ $]".
  Qed.

  (* [phys_ledger] with its timestamp EXPOSED -- the sealed form hides  *)
  (* [t] existentially and every discharge below has to compare it      *)
  (* against a receipt.                                                 *)
  Definition phys_ledger_at (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t : nat) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, None))%I.

  Global Instance phys_ledger_at_timeless a dq v t :
    Timeless (phys_ledger_at a dq v t).
  Proof. rewrite /phys_ledger_at. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (* THE CANON-PINNED LEDGER BYTE (tso-pin-memo.md §5.2; ruling 2).     *)
  (*                                                                   *)
  (* The SAME two authorities as [phys_ledger_at], with the element's   *)
  (* option arm SET.  What the pin buys is stated by the interp, not    *)
  (* here: [(t, Some (Sv, B))] ties the address to [TsoMemPa.pin_ok]    *)
  (* -- "from view [B] on, EVERY agent's read of [a] lands in [Sv]" --  *)
  (* which IS the kernel-PT walk's discharge conclusion.  Carrying the  *)
  (* bound in the ELEMENT is what keeps [kpt_inv]'s arity fixed (142    *)
  (* mention sites across 36 files) and what leaves every existing      *)
  (* store gate sound with no new premise: [phys_ledger] /              *)
  (* [ctx_pointsto] / [ctx_phys_pointsto] all pin the option to [None]  *)
  (* by DEFINITION, so the tie's frame arm applies definitionally.      *)
  (* ---------------------------------------------------------------- *)
  Definition phys_ledger_pin (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t B : nat) (Sv : gset (bv 8)) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, Some (Sv, B)))%I.

  Global Instance phys_ledger_pin_timeless a dq v t B Sv :
    Timeless (phys_ledger_pin a dq v t B Sv).
  Proof. rewrite /phys_ledger_pin. apply _. Qed.

  Lemma phys_ledger_pin_ram a dq v t B Sv :
    phys_ledger_pin a dq v t B Sv ⊢ ⌜addr_is_ram a⌝.
  Proof.
    iIntros "[Hp _]". rewrite /phys_pointsto. by iDestruct "Hp" as "[_ $]".
  Qed.

  Lemma phys_ledger_pin_forget a dq v t B Sv :
    phys_ledger_pin a dq v t B Sv ⊢ phys_pointsto a dq v.
  Proof. by iIntros "[$ _]". Qed.

  (* two pinned bytes, one fully owned, cannot name the same address *)
  Lemma phys_ledger_pin_ne a1 a2 dq2 v1 v2 t1 t2 B1 B2 S1 S2 :
    phys_ledger_pin a1 (DfracOwn 1) v1 t1 B1 S1 -∗
    phys_ledger_pin a2 dq2 v2 t2 B2 S2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (phys_ledger_pin_forget with "H1") as "Hp1".
    iDestruct (phys_ledger_pin_forget with "H2") as "Hp2".
    iEval (rewrite /phys_pointsto) in "Hp1". iDestruct "Hp1" as "[Hp1 _]".
    iEval (rewrite /phys_pointsto) in "Hp2". iDestruct "Hp2" as "[Hp2 _]".
    by iDestruct (pointsto_ne with "Hp1 Hp2") as %?.
  Qed.

  (* the OWNED footprint of a pinned store, per-address sets *)
  Definition pin_map_own (Pv : gmap Arch.pa (bv 8)) (dq : dfrac) (B : nat)
      (Sf : Arch.pa -> gset (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ v ∈ Pv, ∃ t : nat, phys_ledger_pin a dq v t B (Sf a))%I.

  Lemma phys_ledger_at_ledger a dq v t :
    phys_ledger_at a dq v t ⊢ phys_ledger a dq v.
  Proof.
    rewrite /phys_ledger_at phys_ledger_unseal /phys_ledger_def.
    iIntros "[Hp He]". iExists t. iFrame.
  Qed.

  Lemma phys_ledger_of_at a dq v :
    phys_ledger a dq v ⊢ ∃ t, phys_ledger_at a dq v t.
  Proof.
    rewrite phys_ledger_unseal /phys_ledger_def /phys_ledger_at.
    iIntros "(%t & Hp & He)". iExists t. iFrame.
  Qed.

  Lemma phys_ledger_at_forget a dq v t :
    phys_ledger_at a dq v t ⊢ phys_pointsto a dq v.
  Proof. by iIntros "[$ _]". Qed.

  (* ---------------------------------------------------------------- *)
  (* THE AUTHOR TIE (A6.47 ruling 1 -- the ratified replacement for the *)
  (* withdrawn [sfence.vma] drain).  The log's entries are PERSISTED at *)
  (* append (§4), so naming one costs nothing and is duplicable; what   *)
  (* it buys is [TsoMemPa.visibleb]'s OWN-AUTHOR arm, i.e. STORE        *)
  (* FORWARDING: a hart always sees its own writes, at any view, with   *)
  (* no receipt and no fence.  That is hart 0's whole read story for    *)
  (* the page table it built between [kvminit] and [kvminithart] -- the *)
  (* boot path never migrates, so naming the AGENT is honest there.     *)
  (* ---------------------------------------------------------------- *)
  Definition ledger_msg_at (i : nat) (m : pwmsg) : iProp Σ :=
    (i ↪[logm_name]□ m)%I.

  Global Instance ledger_msg_at_persistent i m :
    Persistent (ledger_msg_at i m).
  Proof. rewrite /ledger_msg_at. apply _. Qed.
  Global Instance ledger_msg_at_timeless i m :
    Timeless (ledger_msg_at i m).
  Proof. rewrite /ledger_msg_at. apply _. Qed.

  (* THE READ LICENCE AT ONE TIMESTAMP, and the reason hart 0 and the
     secondaries end up using the SAME gate (which is what the withdrawn
     ruling wanted and this one delivers): "[t] is visible to [h] at every
     view at or above [B]" -- either because [t] is under the bound, or
     because [h] wrote it.  Structurally [TsoGhost.dirty_ok]'s disjunction,
     lifted off the dirty set and stated about a bare timestamp. *)
  Definition ledger_vis (h : agent) (B t : nat) : iProp Σ :=
    (⌜(t ≤ B)%nat⌝ ∨
     ∃ i m, ⌜t = S i⌝ ∗ ledger_msg_at i m ∗ ⌜pm_tid m = h⌝)%I.

  Global Instance ledger_vis_persistent h B t : Persistent (ledger_vis h B t).
  Proof. rewrite /ledger_vis. apply _. Qed.

  Lemma ledger_vis_below (h : agent) (B t : nat) :
    (t ≤ B)%nat -> ⊢ ledger_vis h B t.
  Proof. iIntros (Hle). iLeft. by iPureIntro. Qed.

  Lemma ledger_vis_own (h : agent) (B i : nat) (m : pwmsg) :
    pm_tid m = h -> ledger_msg_at i m -∗ ledger_vis h B (S i).
  Proof.
    iIntros (Htid) "#Hm". iRight. iExists i, m. iFrame "Hm".
    iSplit; by iPureIntro.
  Qed.

  Lemma ledger_vis_mono (h : agent) (B B' t : nat) :
    (B ≤ B')%nat -> ledger_vis h B t -∗ ledger_vis h B' t.
  Proof.
    iIntros (Hle) "[%Hb|H]"; [iLeft; iPureIntro; lia | by iRight].
  Qed.


  (* ---------------------------------------------------------------- *)
  (* THE ERA-INITIAL ELEMENT, AND THE ONE BRIDGE OFF IT (A6.28's far end). *)
  (*                                                                      *)
  (* [pristine_byte] is the DISCARDED element and says "image byte, never  *)
  (* stored to again".  A region that IS stored to -- the M-mode boot      *)
  (* stack -- needs the same element at FULL ownership, and the boot carve *)
  (* has to be able to turn its raw bytes into ledger ones.  A6.9 is not   *)
  (* weakened by this: nothing here MINTS an element.  [ledger_elem0] is   *)
  (* handed out exactly once, by the era's initial-state ghost allocation  *)
  (* (the same place [BootCarve]'s image bytes and [pristine_va] receipts  *)
  (* come from), and these two laws only let the carve pair it back up     *)
  (* with the byte it belongs to.  The timestamp is 0 because at era       *)
  (* allocation the log is empty, which is also what makes the CLEAN arm   *)
  (* free ([TsoGhost.llb]'s [⌜K = 0⌝] disjunct -- no bupd, no context).    *)
  (* ---------------------------------------------------------------- *)
  Definition ledger_elem0 (a : Arch.pa) (dq : dfrac) : iProp Σ :=
    (a ↪[ts_name]{dq} (0%nat, None))%I.

  Lemma phys_ledger_of_elem (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    phys_pointsto a dq v -∗ ledger_elem0 a dq -∗ phys_ledger a dq v.
  Proof.
    iIntros "Hp He". rewrite phys_ledger_unseal /phys_ledger_def.
    iExists 0%nat. iFrame "Hp He".
  Qed.

  Lemma ctx_phys_pointsto_of_elem (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) :
    phys_pointsto a dq v -∗ ledger_elem0 a dq -∗ ctx_phys_pointsto ξ a dq v.
  Proof.
    iIntros "Hp He".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iExists 0%nat. iFrame "Hp He". iLeft. iApply llb_0.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* A6.63 THE READ-ONLY MINT, and it is what unblocks the last of the   *)
  (* shim tail.  A rodata byte lives at the RAW tower ([↦ₛ]/[↦ₘ□],       *)
  (* KernelDataInv's image bytes) but the load leaves now demand a CTX   *)
  (* byte, and that direction is the one the flip makes false -- A6.62's *)
  (* four residual sites ([ProofPrintk] x2, [ProofSyscall],              *)
  (* [WpSconfLock]) are all this.                                        *)
  (*                                                                     *)
  (* It is payable, and for one reason: AT TIMESTAMP 0 THE CLEAN ARM IS  *)
  (* FREE ([TsoGhost.llb_0]).  So a byte needs no new authority to enter *)
  (* the tier -- it needs its LEDGER ELEMENT, and A6.9 says the era's    *)
  (* initial allocation is the only supplier of those.  That allocation  *)
  (* is the element carve, which is why this lemma could not be written  *)
  (* before it and why the carve unblocks step 5's tail as well as       *)
  (* step 6's (A6.62).                                                   *)
  (*                                                                     *)
  (* The caller supplies [ppn] with its [kmap_at] witness -- every leaf   *)
  (* site already holds one -- so the element is indexed at the PHYSICAL  *)
  (* address, exactly as [ctx_pointsto_def] holds it.                     *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_of_ro `{KTR : !CurKtier} (ξ : CtxId) (a : Arch.pa)
      (ppn : mword 44) (dq : dfrac) (v : bv 8) :
    kmap_at (svpn_of a) ppn KP_rw -∗
    mem_pointsto a dq v -∗
    ledger_elem0 (pa_of ppn a) dq -∗
    ctx_pointsto ξ a dq v.
  Proof.
    iIntros "#Hk Hm He".
    rewrite /mem_pointsto.
    iDestruct "Hm" as (ppn') "(#Hk' & %Hc & %Hr & %Hp & Hpt)".
    iDestruct (kmap_at_agree with "Hk Hk'") as %[-> _].
    rewrite ctx_pointsto_unseal /ctx_pointsto_def.
    iExists ppn', 0%nat.
    iSplitR; [iExact "Hk'" |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iFrame "Hpt He". iLeft. iApply llb_0.
  Qed.


  (* the 8-byte tower, so a PT slot can be spelled at either tier *)
  Definition phys_ledger_word (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, phys_ledger (pa_add a j) dq (nth_byte w j))%I.

  Lemma phys_ledger_word_unfold a dq w :
    phys_ledger_word a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, phys_ledger (pa_add a j) dq (nth_byte w j)).
  Proof. reflexivity. Qed.

  Lemma phys_ledger_word_aligned_p a dq w :
    phys_ledger_word a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.

  Lemma phys_ledger_word_bytes a dq w :
    phys_ledger_word a dq w ⊢
    [∗ list] j ∈ seq 0 8, phys_ledger (pa_add a j) dq (nth_byte w j).
  Proof. iIntros "[_ $]". Qed.

  Lemma phys_ledger_word_intro a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, phys_ledger (pa_add a j) dq (nth_byte w j))
    ⊢ phys_ledger_word a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.

  Global Instance phys_ledger_word_timeless a dq w :
    Timeless (phys_ledger_word a dq w).
  Proof. rewrite /phys_ledger_word. apply _. Qed.

  Lemma phys_ledger_word_forget a dq w :
    phys_ledger_word a dq w ⊢ phys_word_pointsto a dq w.
  Proof.
    iIntros "[%Hal Hb]". rewrite /phys_word_pointsto. iSplitR; first done.
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
    by iApply phys_ledger_forget.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE PINNED WORD TOWER (tso-pin-memo.md §5.4; A6.53's ruling 1).     *)
  (*                                                                    *)
  (* [phys_ledger_word]'s twin at the pinned byte, with the allowed sets *)
  (* indexed by BYTE OFFSET: for a kernel PT slot, byte 0's set is the   *)
  (* four-element A/D class of the slot's own word and bytes 1..7's are  *)
  (* singletons (§2's measurement).  The set FAMILY is a parameter here  *)
  (* on purpose -- naming [pte_canon] at this layer is the layering      *)
  (* violation candidate (iv) was rejected for; [PtTree.pte_slot_set]    *)
  (* supplies it.                                                       *)
  (* ---------------------------------------------------------------- *)
  Definition phys_ledger_word_pin (a : Arch.pa) (dq : dfrac) (w : bv 64)
      (B : nat) (Sf : nat -> TsoMemPa.byteset) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, ∃ t : nat,
       phys_ledger_pin (pa_add a j) dq (nth_byte w j) t B (Sf j))%I.

  Lemma phys_ledger_word_pin_unfold a dq w B Sf :
    phys_ledger_word_pin a dq w B Sf ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       phys_ledger_pin (pa_add a j) dq (nth_byte w j) t B (Sf j)).
  Proof. reflexivity. Qed.

  Lemma phys_ledger_word_pin_aligned_p a dq w B Sf :
    phys_ledger_word_pin a dq w B Sf ⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.

  Lemma phys_ledger_word_pin_bytes a dq w B Sf :
    phys_ledger_word_pin a dq w B Sf ⊢
    [∗ list] j ∈ seq 0 8, ∃ t : nat,
      phys_ledger_pin (pa_add a j) dq (nth_byte w j) t B (Sf j).
  Proof. iIntros "[_ $]". Qed.

  Lemma phys_ledger_word_pin_intro a dq w B Sf :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       phys_ledger_pin (pa_add a j) dq (nth_byte w j) t B (Sf j))
    ⊢ phys_ledger_word_pin a dq w B Sf.
  Proof. iIntros (Hal) "H". by iFrame. Qed.

  Global Instance phys_ledger_word_pin_timeless a dq w B Sf :
    Timeless (phys_ledger_word_pin a dq w B Sf).
  Proof. rewrite /phys_ledger_word_pin. apply _. Qed.

  (* the pinned word forgets to the RAW physical word -- which is all the
     pure memory facts of the walk lane ever wanted of a slot, and is why
     [PtTree.pt_slot_own_forget] stays a one-liner at both arms.  It does
     NOT forget to [phys_ledger_word]: that tier's element is [None] by
     definition, so the two are incomparable and the A6.21 remark about the
     registered tier being "strictly stronger" no longer applies to the
     KERNEL arm.  Nothing used it. *)
  Lemma phys_ledger_word_pin_forget a dq w B Sf :
    phys_ledger_word_pin a dq w B Sf ⊢ phys_word_pointsto a dq w.
  Proof.
    iIntros "[%Hal Hb]". rewrite /phys_word_pointsto. iSplitR; first done.
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "(%t & H)".
    by iApply phys_ledger_pin_forget.
  Qed.

  (* the set family may be replaced by a pointwise-equal one -- which is
     what makes the pin survive its OWN A/D write-back: the written word's
     set family is the old one ([PtTree.pte_slot_set_set_ad]). *)
  Lemma phys_ledger_word_pin_sets a dq w B (Sf Sg : nat -> TsoMemPa.byteset) :
    (forall j, (j < 8)%nat -> Sf j = Sg j) ->
    phys_ledger_word_pin a dq w B Sf ⊢ phys_ledger_word_pin a dq w B Sg.
  Proof.
    intros HS. iIntros "[%Hal Hb]". iSplitR; first done.
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    by rewrite (HS (0 + k)%nat ltac:(lia)).
  Qed.

  (* the REGISTERED byte forgets to the unregistered one -- the bit is what
     is dropped, and with it the load license, nothing else *)
  Lemma ctx_phys_pointsto_ledger ξ a dq v :
    ctx_phys_pointsto ξ a dq v ⊢ phys_ledger a dq v.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def
            phys_ledger_unseal /phys_ledger_def.
    iIntros "(%t & Hpt & Hts & _)". iExists t. iFrame.
  Qed.

  (* exclusivity at the REGISTERED physical tier, the companion of
     [phys_ledger_ne] one tier up: two owned bytes cannot name the same
     address.  A6.49's user-memory flip needs it -- [UmodeMem.umem_inj]
     derives the va -> pa injectivity from the ownership alone, and the
     sealed tier wants a law rather than an unfolding (A6.48's
     [phys_map_disj] precedent). *)
  Lemma ctx_phys_pointsto_ne (ξ1 ξ2 : CtxId) (a1 a2 : Arch.pa) (dq2 : dfrac)
      (v1 v2 : bv 8) :
    ctx_phys_pointsto ξ1 a1 (DfracOwn 1) v1 -∗
    ctx_phys_pointsto ξ2 a2 dq2 v2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ctx_phys_pointsto_ledger with "H1") as "H1".
    iDestruct (ctx_phys_pointsto_ledger with "H2") as "H2".
    by iApply (phys_ledger_ne with "H1 H2").
  Qed.

  (* the per-byte half, TWO authorities instead of three: no dirty set, so
     no freshness obligation and no context anywhere *)
  Local Lemma ledger_store_bytes (i : nat)
      (Pold Pnew mem : gmap Arch.pa (bv 8)) (TM : gmap Arch.pa ts_elem) :
    dom Pold = dom Pnew ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    ghost_map_auth ts_name 1 TM -∗
    ([∗ map] a ↦ v ∈ Pold, phys_ledger a (DfracOwn 1) v) ==∗
    ⌜dom Pnew ⊆ dom mem⌝ ∗
    gen_heap_interp (hG := riscv_memGS) (Pnew ∪ mem) ∗
    ghost_map_auth ts_name 1 (((fun _ => (S i, None)) <$> Pnew) ∪ TM) ∗
    ([∗ map] a ↦ v ∈ Pnew, phys_ledger_at a (DfracOwn 1) v (S i)).
  Proof.
    revert Pold. induction Pnew as [|a vn P2 Hfresh IH] using map_ind;
      intros Pold Hdom.
    - rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hgh Hts _". iModIntro.
      rewrite fmap_empty !left_id_L !big_sepM_empty.
      iFrame "Hgh Hts". iPureIntro. set_solver.
    - iIntros "Hgh Hts Hold".
      assert (Ha : a ∈ dom Pold) by (rewrite Hdom dom_insert_L; set_solver).
      apply elem_of_dom in Ha as [vo Hvo].
      iDestruct (big_sepM_delete _ _ a vo Hvo with "Hold") as "[Hb Hrest]".
      assert (Hdom2 : dom (delete a Pold) = dom P2).
      { rewrite dom_delete_L Hdom dom_insert_L.
        assert (a ∉ dom P2) by (by apply not_elem_of_dom). set_solver. }
      iMod (IH (delete a Pold) Hdom2 with "Hgh Hts Hrest")
        as "(%Hsub2 & Hgh & Hts & Hbig)".
      rewrite phys_ledger_unseal /phys_ledger_def.
      iDestruct "Hb" as "(%t & Hpt & Hte)".
      iDestruct (phys_valid with "Hgh Hpt") as %Hmem.
      iMod (phys_update _ a vo vn with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update (S i, None) with "Hts Hte") as "[Hts Hte]".
      iModIntro.
      rewrite fmap_insert -!insert_union_l !big_sepM_insert //.
      iFrame "Hgh Hts Hbig".
      iSplitR.
      { iPureIntro. rewrite dom_insert_L. apply union_least; [|exact Hsub2].
        assert (Hin : a ∈ dom mem).
        { apply elem_of_dom_2 in Hmem. rewrite dom_union_L elem_of_union in Hmem.
          destruct Hmem as [Hx|Hx]; last done.
          apply not_elem_of_dom in Hfresh. set_solver. }
        set_solver. }
      rewrite /phys_ledger_at. iFrame "Hpt Hte".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* (3) THE PINNED STORE GATE (tso-pin-memo.md §5.3).  The A/D           *)
  (* write-back's own gate: same message, same three ghost steps, and     *)
  (* ONE extra premise -- every written byte lands in its address's       *)
  (* allowed set.  The pin's bound [B] and sets [Sf] are UNCHANGED (they  *)
  (* are fixed at the mint), so the tie is re-established by              *)
  (* [TsoMemPa.pin_ok_app] on the footprint and [pin_ok_app_frame] off    *)
  (* it -- and a byte's pin survives its own write-back, which is the     *)
  (* property that makes the shared kernel table canon-INVARIANT rather   *)
  (* than merely canon-monotone.                                          *)
  (* ---------------------------------------------------------------- *)
  Definition pin_tm (i B : nat) (Sf : Arch.pa -> gset (bv 8))
      (Pv : gmap Arch.pa (bv 8)) : gmap Arch.pa ts_elem :=
    map_imap (fun a _ => Some ((S i, Some (Sf a, B)) : ts_elem)) Pv.

  Local Lemma pin_tm_lookup i B Sf Pv a :
    pin_tm i B Sf Pv !! a
    = (fun _ : bv 8 => ((S i, Some (Sf a, B)) : ts_elem)) <$> (Pv !! a).
  Proof.
    rewrite /pin_tm map_lookup_imap. by destruct (Pv !! a).
  Qed.

  Local Lemma pin_tm_empty i B Sf : pin_tm i B Sf ∅ = ∅.
  Proof. apply map_eq. intros k. by rewrite pin_tm_lookup lookup_empty. Qed.

  Local Lemma pin_tm_insert i B Sf (P : gmap Arch.pa (bv 8)) a v :
    pin_tm i B Sf (<[a := v]> P)
    = <[a := ((S i, Some (Sf a, B)) : ts_elem)]> (pin_tm i B Sf P).
  Proof.
    apply map_eq. intros k. rewrite pin_tm_lookup.
    destruct (decide (k = a)) as [->|Hne].
    - by rewrite !lookup_insert.
    - rewrite !lookup_insert_ne // pin_tm_lookup //.
  Qed.

  Local Lemma ledger_store_pin_bytes (i B : nat) (Sf : Arch.pa -> gset (bv 8))
      (Pold Pnew mem : gmap Arch.pa (bv 8)) (TM : gmap Arch.pa ts_elem) :
    dom Pold = dom Pnew ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    ghost_map_auth ts_name 1 TM -∗
    pin_map_own Pold (DfracOwn 1) B Sf ==∗
    ⌜dom Pnew ⊆ dom mem⌝ ∗
    (* the OLD elements, so the caller can re-establish the pin tie on the
       footprint out of [TsoMemPa.pin_ok_app] rather than out of nothing *)
    ⌜forall a, a ∈ dom Pnew ->
       exists t, TM !! a = Some ((t, Some (Sf a, B)) : ts_elem)⌝ ∗
    gen_heap_interp (hG := riscv_memGS) (Pnew ∪ mem) ∗
    ghost_map_auth ts_name 1 (pin_tm i B Sf Pnew ∪ TM) ∗
    ([∗ map] a ↦ v ∈ Pnew, phys_ledger_pin a (DfracOwn 1) v (S i) B (Sf a)).
  Proof.
    revert Pold. rewrite /pin_map_own.
    induction Pnew as [|a vn P2 Hfresh IH] using map_ind; intros Pold Hdom.
    - rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hgh Hts _". iModIntro.
      rewrite pin_tm_empty !left_id_L !big_sepM_empty.
      iFrame "Hgh Hts". iPureIntro. split; first set_solver.
      intros a Ha. rewrite dom_empty_L in Ha. set_solver.
    - iIntros "Hgh Hts Hold".
      assert (Ha : a ∈ dom Pold) by (rewrite Hdom dom_insert_L; set_solver).
      apply elem_of_dom in Ha as [vo Hvo].
      iDestruct (big_sepM_delete _ _ a vo Hvo with "Hold") as "[Hb Hrest]".
      assert (Hdom2 : dom (delete a Pold) = dom P2).
      { rewrite dom_delete_L Hdom dom_insert_L.
        assert (a ∉ dom P2) by (by apply not_elem_of_dom). set_solver. }
      iMod (IH (delete a Pold) Hdom2 with "Hgh Hts Hrest")
        as "(%Hsub2 & %Hold2 & Hgh & Hts & Hbig)".
      iDestruct "Hb" as "(%t & Hpt & Hte)".
      iDestruct (phys_valid with "Hgh Hpt") as %Hmem.
      iDestruct (ghost_map_lookup with "Hts Hte") as %Hlk.
      assert (HTMa : TM !! a = Some ((t, Some (Sf a, B)) : ts_elem)).
      { rewrite lookup_union_r in Hlk; first exact Hlk.
        rewrite pin_tm_lookup. by rewrite Hfresh. }
      iMod (phys_update _ a vo vn with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update ((S i, Some (Sf a, B)) : ts_elem) with "Hts Hte")
        as "[Hts Hte]".
      iModIntro.
      rewrite pin_tm_insert -!insert_union_l !big_sepM_insert //.
      iFrame "Hgh Hts Hbig".
      iSplitR.
      { iPureIntro. rewrite dom_insert_L. apply union_least; [|exact Hsub2].
        assert (Hin : a ∈ dom mem).
        { apply elem_of_dom_2 in Hmem. rewrite dom_union_L elem_of_union in Hmem.
          destruct Hmem as [Hx|Hx]; last done.
          apply not_elem_of_dom in Hfresh. set_solver. }
        set_solver. }
      iSplitR.
      { iPureIntro. intros a' Ha'. rewrite dom_insert_L elem_of_union in Ha'.
        destruct Ha' as [Ha'|Ha'].
        - apply elem_of_singleton in Ha' as ->. by exists t.
        - exact (Hold2 a' Ha'). }
      rewrite /phys_ledger_pin. iFrame "Hpt Hte".
  Qed.

  Lemma ledger_store_pin_ok (g g' : gstate) (auth : agent)
      (Pold Pnew : gmap Arch.pa (bv 8)) (B : nat)
      (Sf : Arch.pa -> gset (bv 8)) :
    dom Pold = dom Pnew ->
    (* THE ONE NEW PREMISE *)
    (forall a v, Pnew !! a = Some v -> v ∈ Sf a) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew auth])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    pin_map_own Pold (DfracOwn 1) B Sf ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog)) (PWMsg Pnew auth) ∗
    ([∗ map] a ↦ v ∈ Pnew,
       phys_ledger_pin a (DfracOwn 1) v (S (length g.(glog))) B (Sf a)).
  Proof.
    iIntros (Hdom Hin Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdomtm & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htvok].
    set (msg := PWMsg Pnew auth).
    assert (HLMfresh : LM !! length g.(glog) = None).
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length g.(glog)) msg HLMfresh with "Hm")
      as "[Hm #Hmsg]".
    iMod (mono_nat_own_update (length g'.(glog)) with "Hlen") as "[Hlen _]".
    { rewrite Hlog length_app /=. lia. }
    iMod (ledger_store_pin_bytes (length g.(glog)) B Sf Pold Pnew g.(gmem) TM
            Hdom with "Hgh Hts Hold")
      as "(%Hsub & %Hold2 & Hgh & Hts & Hbig)".
    assert (Hlen' : length g'.(glog) = S (length g.(glog))).
    { rewrite Hlog length_app /=. lia. }
    assert (Havf : forall x, (avf g x <= avf g' x)%nat).
    { intros x. rewrite /avf Hlog length_app /=.
      destruct (lt_dec x NCPU) as [Hx|Hx]; [apply Htv | lia]. }
    iMod (view_auth_update _ (avf g) (avf g') Havf with "Hv") as "Hv".
    iModIntro.
    iSplitL "Hgh"; first by rewrite Hmem.
    iFrame "Hbig". iFrame "Hmsg".
    iExists (pin_tm (length g.(glog)) B Sf Pnew ∪ TM),
            (<[length g.(glog) := msg]> LM).
    iFrame "Hts Hm Hlen Hv".
    iSplitR.
    { iPureIntro.
      assert (Hdpin : dom (pin_tm (length g.(glog)) B Sf Pnew) = dom Pnew).
      { apply set_eq. intros k.
        by rewrite !elem_of_dom pin_tm_lookup fmap_is_Some. }
      rewrite dom_union_L Hdpin Hmem dom_union_L Hdomtm.
      by rewrite (subseteq_union_1_L _ _ Hsub). }
    iSplitR.
    { iPureIntro. intros a e Hlk.
      destruct (Pnew !! a) as [vn|] eqn:Hpa.
      - assert (Hl : pin_tm (length g.(glog)) B Sf Pnew !! a
                     = Some ((S (length g.(glog)), Some (Sf a, B)) : ts_elem))
          by (rewrite pin_tm_lookup Hpa //).
        rewrite (lookup_union_Some_l _ _ _ _ Hl) in Hlk. injection Hlk as <-.
        assert (Hmb : msg_byte msg a = Some vn)
          by (rewrite /msg_byte /=; exact Hpa).
        split.
        + exists vn. split.
          { rewrite Hmem. by apply lookup_union_Some_l. }
          rewrite Hlog Himg. apply latest_app_new. exact Hmb.
        + intros Sv' B' Heq. cbn in Heq. injection Heq as <- <-.
          destruct (Hold2 a ltac:(by apply elem_of_dom)) as (told & HTMa).
          rewrite Hlog Himg.
          apply pin_ok_app.
          * exact (ts_ok_pin _ _ _ _ _ _ _ (Htie _ _ HTMa) eq_refl).
          * right. exists vn. split; [exact Hmb | exact (Hin a vn Hpa)].
      - assert (Hl : pin_tm (length g.(glog)) B Sf Pnew !! a = None)
          by (rewrite pin_tm_lookup Hpa //).
        rewrite (lookup_union_r _ _ _ Hl) in Hlk.
        pose proof (Htie _ _ Hlk) as Hok.
        assert (Hmb : msg_byte msg a = None) by (rewrite /msg_byte /=; exact Hpa).
        split.
        + destruct (ts_ok_latest _ _ _ _ _ Hok) as (v0 & Hgm & Hlat).
          exists v0. split.
          { rewrite Hmem. by rewrite lookup_union_r. }
          rewrite Hlog Himg. by apply latest_app_frame.
        + intros Sv' B' He2. rewrite Hlog Himg.
          apply (pin_ok_app_frame _ _ _ _ _ _
                   (ts_ok_pin _ _ _ _ _ _ _ Hok He2) Hmb). }
    iSplitR.
    { iPureIntro. intros j. rewrite Hlog.
      destruct (decide (j = length g.(glog))) as [->|Hne].
      - rewrite lookup_insert. symmetry. by apply list_lookup_middle.
      - rewrite lookup_insert_ne; last congruence. rewrite HLM.
        destruct (decide (j < length g.(glog))%nat) as [Hlt|Hge].
        + by rewrite lookup_app_l.
        + rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia. }
    iPureIntro. split.
    - rewrite Hmem Hlog Himg flat_snoc /=. by rewrite -Hflat.
    - intros c. have := Htvok' c. lia.
  Qed.

  (* THE CONTEXT-FREE STORE GATE.  Same three of the four ghost steps as
     [ctx_store_ok] -- γts to the new top, γlogm persist, the mono_nat bump
     -- and NO dirty-set insert, because there is no context to insert into.
     The view premises are the same and for the same reason. *)
  (* A6.28: THE AUTHOR IS A PARAMETER, NOT THE AMBIENT HART.  The
     context-free ledger has no author tie to keep -- there is no dirty set
     and no load licence -- and the proof never uses the hart-ness of the
     message's [pm_tid] ([msg_byte] ignores it, and both [latest_app_*] laws
     are author-blind).  So one gate serves an M-mode store's append
     ([hart_agent cpu_id]) AND the DMA lease's reclaim ([disk_agent], A6.9).
     [CID] stays because the [gtv] premises quantify over harts. *)
  (* NO [CpuId] BINDER: the author is a PARAMETER, and the disk agent is not
     a hart (A6.48 ruling 4 -- [WpUart]'s disk loop applies this at
     [disk_agent] and has no ambient hart to offer). *)
  Lemma ledger_store_ok (g g' : gstate) (auth : agent)
      (Pold Pnew : gmap Arch.pa (bv 8)) :
    dom Pold = dom Pnew ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew auth])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ map] a ↦ v ∈ Pold, phys_ledger a (DfracOwn 1) v) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    (* A6.47 ruling 1: the append's own message, PERSISTED, so the writer
       can hand its slot the AUTHOR tie -- that is what lets hart 0's own
       later walks discharge by store forwarding without any receipt.  The
       timestamp is exposed for the same reason: an existential [t] cannot
       be compared against the message index. *)
    ledger_msg_at (length g.(glog)) (PWMsg Pnew auth) ∗
    ([∗ map] a ↦ v ∈ Pnew,
       phys_ledger_at a (DfracOwn 1) v (S (length g.(glog)))).
  Proof.
    iIntros (Hdom Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdomtm & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htvok].
    set (msg := PWMsg Pnew auth).
    assert (HLMfresh : LM !! length g.(glog) = None).
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length g.(glog)) msg HLMfresh with "Hm")
      as "[Hm #Hmsg]".
    iMod (mono_nat_own_update (length g'.(glog)) with "Hlen") as "[Hlen _]".
    { rewrite Hlog length_app /=. lia. }
    iMod (ledger_store_bytes (length g.(glog)) Pold Pnew g.(gmem) TM Hdom
            with "Hgh Hts Hold") as "(%Hsub & Hgh & Hts & Hbig)".
    assert (Hlen' : length g'.(glog) = S (length g.(glog))).
    { rewrite Hlog length_app /=. lia. }
    assert (Havf : forall x, (avf g x <= avf g' x)%nat).
    { intros x. rewrite /avf Hlog length_app /=.
      destruct (lt_dec x NCPU) as [Hx|Hx]; [apply Htv | lia]. }
    iMod (view_auth_update _ (avf g) (avf g') Havf with "Hv") as "Hv".
    iModIntro.
    iSplitL "Hgh"; first by rewrite Hmem.
    iFrame "Hbig". iFrame "Hmsg".
    iExists (((fun _ : bv 8 => ((S (length g.(glog)), None) : ts_elem)) <$> Pnew) ∪ TM),
            (<[length g.(glog) := msg]> LM).
    iFrame "Hts Hm Hlen Hv".
    iSplitR.
    { iPureIntro. rewrite dom_union_L dom_fmap_L Hmem dom_union_L Hdomtm.
      by rewrite (subseteq_union_1_L _ _ Hsub). }
    iSplitR.
    { (* both halves; see [ctx_store_ok]'s note *)
      iPureIntro. intros a e Hlk.
      destruct (Pnew !! a) as [vn|] eqn:Hpa.
      - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), None) : ts_elem)) <$> Pnew) !! a
                     = Some ((S (length g.(glog)), None) : ts_elem))
          by (rewrite lookup_fmap Hpa //).
        rewrite (lookup_union_Some_l _ _ _ _ Hl) in Hlk. injection Hlk as <-.
        apply (ts_ok_unpinned _ _ _ _ _ vn).
        { rewrite Hmem. by apply lookup_union_Some_l. }
        rewrite Hlog Himg. apply latest_app_new. by rewrite /msg_byte /=.
      - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), None) : ts_elem)) <$> Pnew) !! a = None)
          by (rewrite lookup_fmap Hpa //).
        rewrite (lookup_union_r _ _ _ Hl) in Hlk.
        pose proof (Htie _ _ Hlk) as Hok.
        assert (Hmb : msg_byte msg a = None) by (rewrite /msg_byte /=; exact Hpa).
        split.
        + destruct (ts_ok_latest _ _ _ _ _ Hok) as (v0 & Hgm & Hlat).
          exists v0. split.
          { rewrite Hmem. by rewrite lookup_union_r. }
          rewrite Hlog Himg. by apply latest_app_frame.
        + intros Sv Bp He2. rewrite Hlog Himg.
          apply (pin_ok_app_frame _ _ _ _ _ _
                   (ts_ok_pin _ _ _ _ _ _ _ Hok He2) Hmb). }
    iSplitR.
    { iPureIntro. intros j. rewrite Hlog.
      destruct (decide (j = length g.(glog))) as [->|Hne].
      - rewrite lookup_insert. symmetry. by apply list_lookup_middle.
      - rewrite lookup_insert_ne; last congruence. rewrite HLM.
        destruct (decide (j < length g.(glog))%nat) as [Hlt|Hge].
        + by rewrite lookup_app_l.
        + rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia. }
    iPureIntro. split.
    - rewrite Hmem Hlog Himg flat_snoc /=. by rewrite -Hflat.
    - intros c. have := Htvok' c. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE SUBMAP FORM: the writer owns MORE than it writes.              *)
  (*                                                                   *)
  (* [HartMemRun]'s user-tier walker carries its whole owned byte map    *)
  (* and writes a window inside it, so it needs the gate at             *)
  (* "footprint ⊆ owned" rather than at "footprint = owned".  The split  *)
  (* is done here, once, rather than at every walker arm: the owned map  *)
  (* is [Pold ∪ rest] at [Pold := mm ∩ Pnew] (stdpp's intersection keeps *)
  (* the LEFT values, i.e. the OLD bytes at the written keys), the gate  *)
  (* moves [Pold] to [Pnew], and the rejoined map is [Pnew ∪ mm] --      *)
  (* which is exactly [TsoMemPa.write_bytes_union]'s reading of          *)
  (* [write_bytes mm pa n v].                                           *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_store_sub_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (mm Pnew : gmap Arch.pa (bv 8)) :
    dom Pnew ⊆ dom mm ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew (hart_agent cpu_id)])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ map] a ↦ v ∈ mm, ctx_phys_pointsto ξ a (DfracOwn 1) v) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ map] a ↦ v ∈ Pnew ∪ mm, ctx_phys_pointsto ξ a (DfracOwn 1) v).
  Proof.
    iIntros (Hsub Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hown".
    set (Pold := mm ∩ Pnew).
    assert (HPsub : Pold ⊆ mm).
    { rewrite map_subseteq_spec. intros a b Hab.
      by apply lookup_intersection_Some in Hab as [? _]. }
    assert (Hdom : dom Pold = dom Pnew).
    { rewrite /Pold dom_intersection_L. set_solver. }
    assert (Hdisj : Pold ##ₘ mm ∖ Pold)
      by apply (map_disjoint_difference_r mm Pold Pold), reflexivity.
    assert (Hsplit : mm = Pold ∪ (mm ∖ Pold))
      by (symmetry; by apply map_difference_union).
    assert (Hdisj2 : Pnew ##ₘ mm ∖ Pold).
    { apply map_disjoint_dom. rewrite dom_difference_L -Hdom. set_solver. }
    assert (Hjoin : Pnew ∪ mm = Pnew ∪ (mm ∖ Pold)).
    { apply map_eq. intros a. destruct (Pnew !! a) as [b|] eqn:Hp.
      - by rewrite !(lookup_union_Some_l _ _ _ _ Hp).
      - rewrite !lookup_union_r //.
        destruct (mm !! a) as [c|] eqn:Hm; last first.
        { symmetry. apply lookup_difference_None. by left. }
        symmetry. rewrite lookup_difference_Some. split; first done.
        by rewrite /Pold lookup_intersection Hm Hp. }
    rewrite Hsplit big_sepM_union //.
    iDestruct "Hown" as "[Hfp Hrest]".
    rewrite -Hsplit.
    iMod (ctx_store_ok g g' ξ Pold Pnew Hdom Himg Hlog Hmem Htv Htvok'
            with "Hgh Hint Hrun Hfp") as "($ & $ & $ & Hfp)".
    iModIntro. rewrite Hjoin big_sepM_union //. iFrame "Hfp Hrest".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE WINDOW BRIDGE: a leaf's byte LIST and the log message's byte   *)
  (* MAP are the same resource.  [write_bytes]/[snap_of] is a foldr of  *)
  (* inserts over [seq 0 n] and the addresses are distinct              *)
  (* ([tso_pa_add_inj]), so the two big-ops agree conjunct for          *)
  (* conjunct.  This is what makes [ctx_store_ok]'s map form -- the one *)
  (* [TsoMemPa.write_bytes_union] states the arm's update in -- usable  *)
  (* at a leaf that owns [↦ₚ₈]-shaped bytes.                            *)
  (* ---------------------------------------------------------------- *)

  Local Lemma big_sepM_foldr_ins {A} (Φ : Arch.pa -> A -> iProp Σ)
      (f : nat -> A) (pa : Arch.pa) (l : list nat) :
    base.NoDup (pa_add pa <$> l) ->
    ([∗ list] j ∈ l, Φ (pa_add pa j) (f j)) ⊣⊢
    ([∗ map] a ↦ b ∈ foldr (fun j acc => <[pa_add pa j := f j]> acc) ∅ l,
       Φ a b).
  Proof.
    induction l as [|x xs IH]; intros Hnd.
    - by rewrite big_sepM_empty.
    - cbn [fmap list_fmap] in Hnd.
      pose proof (list_relations.NoDup_cons_1_1 _ _ Hnd) as Hx.
      pose proof (list_relations.NoDup_cons_1_2 _ _ Hnd) as Hnd2.
      cbn [foldr]. rewrite big_sepM_insert; last first.
      { apply not_elem_of_dom. rewrite tso_foldr_ins_dom dom_empty_L.
        rewrite right_id_L elem_of_list_to_set. exact Hx. }
      cbn [big_opL]. by rewrite (IH Hnd2).
  Qed.

  Lemma phys_ledger_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger (pa_add pa j) dq (nth_byte v j)) ⊣⊢
    ([∗ map] a ↦ b ∈ snap_of pa n v, phys_ledger a dq b).
  Proof.
    intros Hn. rewrite /snap_of /write_bytes.
    apply (big_sepM_foldr_ins (fun a b => phys_ledger a dq b)
             (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))).
    by apply tso_nodup_win.
  Qed.

  (* the context-free gate in the shape a leaf's [Wobl_ram] is stated in --
     the A/D write-back's, and any other store by a tier whose owner is an
     invariant (A6.20) *)
  Lemma ledger_store_win_ok `{CID : CpuId} (g g' : gstate)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger (pa_add pa j) (DfracOwn 1) (nth_byte vold j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    rewrite (phys_ledger_win_map pa n vold _ Hn).
    iMod (ledger_store_ok g g' (hart_agent cpu_id)
            (snap_of pa n vold) (snap_of pa n vnew)
            ltac:(by rewrite !dom_snap_of) Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & _ & Hnew)".
    iModIntro. rewrite (phys_ledger_win_map pa n vnew _ Hn).
    iApply (big_sepM_mono with "Hnew"). iIntros (a v _) "H".
    by iApply phys_ledger_at_ledger.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE PINNED WINDOW (A6.53).  Same [big_sepM_foldr_ins] regrouping as *)
  (* [phys_ledger_win_map], with the allowed sets re-keyed from BYTE     *)
  (* OFFSET (which is how a word states them) to ADDRESS (which is how   *)
  (* the store gate's footprint map states them).  The re-keying is a    *)
  (* premise rather than a definition so the caller keeps its own        *)
  (* spelling -- [PtTree]'s is [pte_slot_set w] at the slot's base.      *)
  (* ---------------------------------------------------------------- *)
  Lemma phys_ledger_pin_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) (B : nat)
      (Sf : nat -> TsoMemPa.byteset) (Sg : Arch.pa -> TsoMemPa.byteset) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Sg (pa_add pa j) = Sf j) ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) dq (nth_byte v j) t B (Sf j))
    ⊣⊢ pin_map_own (snap_of pa n v) dq B Sg.
  Proof.
    intros Hn HS. rewrite /pin_map_own /snap_of /write_bytes.
    rewrite <- (big_sepM_foldr_ins
                 (fun a b => ∃ t : nat, phys_ledger_pin a dq b t B (Sg a))%I
                 (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))
                 ltac:(by apply tso_nodup_win)).
    apply big_opL_proper. intros k j Hk.
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    by rewrite (HS (0 + k)%nat ltac:(lia)).
  Qed.

  (* THE PINNED WINDOW STORE, and it is the A/D write-back's own gate:   *)
  (* one message over the slot's eight bytes, the pin's bound and sets   *)
  (* UNCHANGED, and the only new premise is that each written byte lands *)
  (* in its offset's allowed set.                                        *)
  Lemma ledger_store_win_pin_ok `{CID : CpuId} (g g' : gstate)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) (B : nat)
      (Sf : nat -> TsoMemPa.byteset) (Sg : Arch.pa -> TsoMemPa.byteset) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Sg (pa_add pa j) = Sf j) ->
    (forall j : nat, (j < N.to_nat n)%nat -> nth_byte vnew j ∈ Sf j) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) (DfracOwn 1) (nth_byte vold j) t B (Sf j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) (DfracOwn 1) (nth_byte vnew j) t B (Sf j)).
  Proof.
    iIntros (Hn HS Hin Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    rewrite (phys_ledger_pin_win_map pa n vold _ B Sf Sg Hn HS).
    iMod (ledger_store_pin_ok g g' (hart_agent cpu_id)
            (snap_of pa n vold) (snap_of pa n vnew) B Sg
            ltac:(by rewrite !dom_snap_of)
            ltac:(intros a b Hab;
                  destruct (snap_of_lookup_Some _ _ _ _ _ Hab) as (j & Hj & -> & ->);
                  rewrite (HS j ltac:(lia)); exact (Hin j ltac:(lia)))
            Himg Hlog ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & _ & Hnew)".
    iModIntro. rewrite (phys_ledger_pin_win_map pa n vnew _ B Sf Sg Hn HS).
    rewrite /pin_map_own.
    iApply (big_sepM_mono with "Hnew"). iIntros (a v _) "H".
    by iExists (S (length g.(glog))).
  Qed.

  (* the [_at] window map, for the strengthened store gate below *)
  Lemma phys_ledger_at_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) (t : nat) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_at (pa_add pa j) dq (nth_byte v j) t) ⊣⊢
    ([∗ map] a ↦ b ∈ snap_of pa n v, phys_ledger_at a dq b t).
  Proof.
    intros Hn. rewrite /snap_of /write_bytes.
    apply (big_sepM_foldr_ins (fun a b => phys_ledger_at a dq b t)
             (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))).
    by apply tso_nodup_win.
  Qed.

  (* THE STRENGTHENED STORE GATE (A6.47 ruling 1).  Same premises as
     [ledger_store_win_ok]; what it hands back additionally is the append's
     OWN message fragment and the window at the NEW timestamp, which is
     what a page-table writer needs to re-establish its slot's licence --
     [ledger_vis_own] turns the pair into "visible to me at any view", and
     [ledger_vis_below] turns it into "visible to everyone past the bound"
     once the bound is published.  The weak form above is kept so the
     existing [Wobl_ram] payers do not move. *)
  Lemma ledger_store_win_at_ok `{CID : CpuId} (g g' : gstate)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger (pa_add pa j) (DfracOwn 1) (nth_byte vold j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog))
      (PWMsg (snap_of pa n vnew) (hart_agent cpu_id)) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_at (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)
         (S (length g.(glog)))).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    rewrite (phys_ledger_win_map pa n vold _ Hn).
    iMod (ledger_store_ok g g' (hart_agent cpu_id)
            (snap_of pa n vold) (snap_of pa n vnew)
            ltac:(by rewrite !dom_snap_of) Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & $ & Hnew)".
    iModIntro. by rewrite (phys_ledger_at_win_map pa n vnew _ _ Hn).
  Qed.

  Lemma ctx_phys_win_map (ξ : CtxId) (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add pa j) dq (nth_byte v j)) ⊣⊢
    ([∗ map] a ↦ b ∈ snap_of pa n v, ctx_phys_pointsto ξ a dq b).
  Proof.
    intros Hn. rewrite /snap_of /write_bytes.
    apply (big_sepM_foldr_ins (fun a b => ctx_phys_pointsto ξ a dq b)
             (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))).
    by apply tso_nodup_win.
  Qed.

  (* ... and the store gate in the shape a leaf's [Wobl_ram] is stated in:
     the arm's [write_bytes] update, the arm's own [snap_of] message, and
     the byte window on both sides. *)
  Lemma ctx_store_win_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add pa j) (DfracOwn 1) (nth_byte vold j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hold".
    rewrite (ctx_phys_win_map ξ pa n vold _ Hn).
    iMod (ctx_store_ok g g' ξ (snap_of pa n vold) (snap_of pa n vnew)
            ltac:(by rewrite !dom_snap_of) Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hrun Hold") as "($ & $ & $ & Hnew)".
    iModIntro. by rewrite (ctx_phys_win_map ξ pa n vnew _ Hn).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE LOAD GATE AT THE PHYSICAL TIER ([ctx_load_ok] without the VA   *)
  (* plumbing): a running context's ledger byte predicts the machine's  *)
  (* plain load at EVERY admissible view advance of its hart.  Nothing  *)
  (* is consumed and the conclusion is PURE, so a caller keeps its      *)
  (* fact and its token.                                               *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_phys_load_ok `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_phys_pointsto ξ a dq v -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    rewrite own_context_unseal /own_context_def
            ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iIntros "Hgh Hint Hrun Hfact".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htv].
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hfact" as "(%t & Hpt & Htse & Hbit)".
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    iAssert (⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
               visibleb (hart_agent cpu_id) tv' g.(glog) t = true⌝)%I
      as %Hvis.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid with "Hb Hcl") as %HtB.
        iPureIntro. intros tv' Htv'. apply visibleb_below. lia.
      - iDestruct (ghost_map_lookup with "Hd Hdt") as %HDt.
        iDestruct (big_sepM_lookup _ _ _ _ HDt with "Hoks") as "[%HtB | Hown]".
        + iPureIntro. intros tv' Htv'. apply visibleb_below.
          simpl in HtB. lia.
        + iDestruct "Hown" as (i mg) "(%Hti & Hi & %Htid)".
          iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
          iPureIntro. intros tv' _. simpl in Hti. rewrite Hti.
          apply (visibleb_own _ _ _ _ mg); [by rewrite -HLM | done]. }
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|by apply Hvis].
  Qed.

  (* the window form, in the shape [HartEvents.wp_hart_ram_read_plain]'s
     obligation is stated at ([Mobl_ram_plain]). *)
  Lemma ctx_phys_load_bytes_ok `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (a : Arch.pa) (n : N) {m : N} (w : bv m) (dq : dfrac) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j)) -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a n w⌝.
  Proof.
    iIntros "Hgh Hint Hrun Hb".
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_add a j)
                 = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ctx_phys_load_ok g ξ (pa_add a j) dq (nth_byte w j)
                with "Hgh Hint Hrun Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. exact (HH j Hj tv' Htv').
  Qed.

  (* ================================================================== *)
  (* THE CONTEXT-FREE LOAD GATE: A LEDGER BYTE PLUS A MACHINE RECEIPT   *)
  (* (tso-machine-flip.md A6.37, the secondary-hart half of the         *)
  (* corrected RULING 1 discharge plan)                                 *)
  (*                                                                   *)
  (* WHY IT IS NEEDED.  A6.20 built [phys_ledger] as the WRITE-ONLY     *)
  (* ledger byte on the argument that its consumer -- the kernel page   *)
  (* table, owned by a bare [inv] that cannot name a context -- would   *)
  (* only ever be READ through a strongly-ordered arm.  The owner's     *)
  (* overruling of RULING 1 deleted that arm, so those slots now need a *)
  (* read story, and it cannot be [ctx_phys_load_ok]'s: there is no     *)
  (* [own_context] to be had inside a shared invariant.                 *)
  (*                                                                   *)
  (* WHAT REPLACES THE CONTEXT'S BOUND IS THE MACHINE'S OWN RECEIPT.    *)
  (* [own_context] certifies -- my view has passed my context's bound B *)
  (* -- and nothing else about it is used here;                         *)
  (* here the caller instead exhibits [view_lb h F] -- minted at an     *)
  (* AMO/acquire leaf, §6 amendment A6.6(b) -- together with            *)
  (* [⌜t ≤ F⌝] for the byte's own timestamp.  Boot's message-passing    *)
  (* shape is exactly that: hart 0 writes the page table (every slot at *)
  (* some [t ≤ B]) and then the [started] flag at [F > B]; a secondary  *)
  (* that has READ the flag holds [view_lb h F], and every later walk   *)
  (* of the shared table discharges from the inv-opened slot fact.      *)
  (*                                                                   *)
  (* AND WITHIN ONE OPENING THE READ IS EXACT.  [phys_ledger_at] holds  *)
  (* the timestamp ELEMENT, and [era_interp]'s tie says that element IS *)
  (* the latest write at that address -- so there is no later message   *)
  (* at all, and any view at or above [t] returns exactly [v].  No      *)
  (* history predicate over the log, and no -- every later message is  *)
  (* an A/D variant -- invariant: the A/D write-back is itself a        *)
  (* [ledger_store_ok] under the same invariant and cannot interleave   *)
  (* inside an opening.  The modulo-A-D weakening the walk certificates *)
  (* need lives one tier up and is already there ([ptree_canon]).       *)
  (* ================================================================== *)

  (* THE GATE, one byte.  Same proof shape as [ctx_phys_load_ok]'s clean
     arm, with the context's [llb] bound replaced by the receipt: the
     receipt gives [F ≤ gtv], the premise gives [t ≤ F], so the byte's own
     latest write is BELOW every reachable view and [visibleb_below]
     closes it. *)
  (* ---------------------------------------------------------------- *)
  (* THE GENERAL GATE (A6.47 ruling 1): ONE lemma for both routes.  The *)
  (* caller exhibits a receipt at [B] and a per-timestamp LICENCE; the  *)
  (* licence's two arms are exactly [visibleb]'s two, so a secondary    *)
  (* hart uses [ledger_vis_below] with the boot receipt and hart 0 uses *)
  (* [ledger_vis_own] with the author fragment its own store handed     *)
  (* back, and NOTHING downstream has to know which.  ([view_lb_0]      *)
  (* makes the receipt free at [B = 0], which is the pure-forwarding    *)
  (* case.)                                                             *)
  (* ---------------------------------------------------------------- *)
  Lemma ledger_read_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t B : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ledger_vis (hart_agent cpu_id) B t -∗
    phys_ledger_at a dq v t -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    iIntros "Hgh Hint #HB #Hvis [Hpt Htse]".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HB") as %HBtvs.
    rewrite avf_hart in HBtvs.
    iAssert (⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
               visibleb (hart_agent cpu_id) tv' g.(glog) t = true⌝)%I as %Hvis.
    { iDestruct "Hvis" as "[%Hb | (%i & %mg & %Hti & Hi & %Htid)]".
      - iPureIntro. intros tv' Htv'. apply visibleb_below. lia.
      - iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
        iPureIntro. intros tv' _. rewrite Hti.
        apply (visibleb_own _ _ _ _ mg); [by rewrite -HLM | done]. }
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|by apply Hvis].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE PIN'S THREE GATES (tso-pin-memo.md §5).                        *)
  (* ---------------------------------------------------------------- *)

  (* (1) THE MINT, at the pin's PUBLICATION point.  One-way, done once,  *)
  (* and it CREATES NO ELEMENT -- it updates one at full fraction, so    *)
  (* A6.9's "the ledger has no mint" rule stands.  The obligation is     *)
  (* exactly A6.47's refuted [t ≤ B] tie: false as a standing invariant, *)
  (* TRUE here, which is the whole re-framing.                           *)
  Lemma ledger_pin_mint (g : gstate) (a : Arch.pa) (v : bv 8)
      (t B : nat) (Sv : gset (bv 8)) :
    (t <= B)%nat -> v ∈ Sv ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_at a (DfracOwn 1) v t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    phys_ledger_pin a (DfracOwn 1) v t B Sv.
  Proof.
    iIntros (HtB Hv) "Hgh Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iMod (ghost_map_update ((t, Some (Sv, B)) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro. iFrame "Hgh Hpt Hts".
    iExists (<[a := ((t, Some (Sv, B)) : ts_elem)]> TM), LM.
    iFrame "Hauth Hm Hlen Hvw".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Ha : a ∈ dom g.(gmem)) by (by eapply elem_of_dom_2).
      set_solver. }
    iSplitR; last (iPureIntro; split; [exact HLM | exact Hmm]).
    iPureIntro. intros a' e Hlk.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Hlk. injection Hlk as <-. split.
      + exists v. split; [exact Hgm | exact Hlat].
      + intros Sv' B' Heq. cbn in Heq. injection Heq as <- <-.
        exact (pin_ok_mint _ _ _ _ _ t v Hlat HtB Hv).
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.

  (* (2) THE READ, and it is a PROJECTION: the pin's tie IS the           *)
  (* conclusion, so all this does is turn the reader's receipt into       *)
  (* [B ≤ tv'].  Agent-generic on purpose -- the confinement holds of     *)
  (* every agent, which is what makes it usable inside [fobl_ram]'s       *)
  (* ∀-quantified view.                                                   *)
  Lemma ledger_read_pin_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t B : nat) (Sv : gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    phys_ledger_pin a dq v t B Sv -∗
    ⌜forall (h : agent) (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
       exists b, tso_read g.(gimg) g.(glog) h tv' a = Some b /\ b ∈ Sv⌝.
  Proof.
    iIntros "Hint #HB [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    pose proof (ts_ok_pin _ _ _ _ _ _ _ (Htie _ _ HTM) eq_refl) as Hpin.
    iDestruct (view_auth_valid with "Hvw HB") as %HBtvs.
    rewrite avf_hart in HBtvs.
    iPureIntro. intros h tv' Htv'. apply Hpin. lia.
  Qed.

  (* the window form: eight pinned bytes, one per-offset set *)
  Lemma ledger_read_pin_bytes_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8) (B : nat)
      (Sf : nat -> gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ([∗ list] j ∈ seq 0 n, ∃ t : nat,
       phys_ledger_pin (pa_add a j) dq (f j) t B (Sf j)) -∗
    ⌜forall (h : agent) (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
       forall j : nat, (j < n)%nat ->
         exists b, tso_read g.(gimg) g.(glog) h tv' (pa_add a j) = Some b
                   /\ b ∈ Sf j⌝.
  Proof.
    iIntros "Hint #HB Hb".
    iAssert (⌜forall j : nat, (j < n)%nat ->
               forall (h : agent) (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
                 exists b, tso_read g.(gimg) g.(glog) h tv' (pa_add a j) = Some b
                           /\ b ∈ Sf j⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb") as (t) "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_pin_ok g (pa_add a j) dq (f j) t B (Sf j)
                with "Hint HB Hbj"). }
    iPureIntro. intros h tv' Htv' j Hj. exact (HH j Hj h tv' Htv').
  Qed.

  (* the window form of the general gate *)
  Lemma ledger_read_bytes_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : N) {m : N} (w : bv m) (dq : dfrac) (B : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, ledger_vis (hart_agent cpu_id) B t ∗
         phys_ledger_at (pa_add a j) dq (nth_byte w j) t) -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a n w⌝.
  Proof.
    iIntros "Hgh Hint #HB Hb".
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_add a j)
                 = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as (t) "[#Hvis Hbj]".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_vis_ok g (pa_add a j) dq (nth_byte w j) t B
                with "Hgh Hint HB Hvis Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. exact (HH j Hj tv' Htv').
  Qed.

  Lemma ledger_read_at_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t F : nat) :
    (t ≤ F)%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) F -∗
    phys_ledger_at a dq v t -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    iIntros (HtF) "Hgh Hint #HF [Hpt Htse]".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HF") as %HFtvs.
    rewrite avf_hart in HFtvs.
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|].
    apply visibleb_below. lia.
  Qed.

  (* the window form, in the shape the plain read rule asks for: the slot
     facts arrive one per byte, each with its OWN timestamp under the same
     receipt (a page-table page is written slot by slot, so a single [t]
     for the whole window would be a lie). *)
  Lemma ledger_read_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : N) {m : N} (w : bv m) (dq : dfrac) (F : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) F -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, ⌜(t ≤ F)%nat⌝ ∗
         phys_ledger_at (pa_add a j) dq (nth_byte w j) t) -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a n w⌝.
  Proof.
    iIntros "Hgh Hint #HF Hb".
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_add a j)
                 = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as (t) "[%HtF Hbj]".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_at_ok g (pa_add a j) dq (nth_byte w j) t F HtF
                with "Hgh Hint HF Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. exact (HH j Hj tv' Htv').
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE 8-BYTE PHYSICAL LEDGER WORD -- [phys_word_pointsto]'s twin, and *)
  (* the resource THREE of A6.14's four members actually hold ([↦ₚ₈]):   *)
  (* [WpMmodeStore]'s target cell, [KptTree]'s PT slot, and the DMA      *)
  (* lease's descriptor doubleword.  Character for character            *)
  (* [ctx_word_pointsto] at the physical tier, so the towers' law names  *)
  (* line up.                                                           *)
  (* ---------------------------------------------------------------- *)
  Definition ctx_phys_word_pointsto (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (w : bv 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Lemma ctx_phys_word_pointsto_unfold ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j)).
  Proof. reflexivity. Qed.

  Lemma ctx_phys_word_pointsto_aligned_p ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.

  Lemma ctx_phys_word_pointsto_bytes ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊢
    [∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j).
  Proof. iIntros "[_ $]". Qed.

  Lemma ctx_phys_word_pointsto_intro ξ a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j))
    ⊢ ctx_phys_word_pointsto ξ a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.

  Global Instance ctx_phys_word_pointsto_timeless ξ a dq w :
    Timeless (ctx_phys_word_pointsto ξ a dq w).
  Proof. rewrite /ctx_phys_word_pointsto. apply _. Qed.
  Global Instance ctx_phys_word_pointsto_discarded_persistent ξ a w :
    Persistent (ctx_phys_word_pointsto ξ a DfracDiscarded w).
  Proof. rewrite /ctx_phys_word_pointsto. apply _. Qed.

  Lemma ctx_phys_word_pointsto_forget ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊢ phys_word_pointsto a dq w.
  Proof.
    iIntros "[%Hal Hb]". rewrite /phys_word_pointsto. iSplitR; first done.
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
    by iApply ctx_phys_pointsto_forget.
  Qed.

  Lemma ctx_phys_word_ledger ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊢ phys_ledger_word a dq w.
  Proof.
    iIntros "[%Hal Hb]". rewrite /phys_ledger_word. iSplitR; first done.
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
    by iApply ctx_phys_pointsto_ledger.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE IDENTITY-MAPPED CROSSING between the VA ledger family and the  *)
  (* PHYSICAL one, BOTH DIRECTIONS AND LOSSLESS (A6.16).                *)
  (*                                                                   *)
  (* This is what repairs A6.14's [KptTree] entry.  The PT-slot pair    *)
  (* [pt_slot_phys_to_mem] / [pt_slot_mem_to_phys] is an OUT-AND-BACK   *)
  (* with a STORE inside, and A6.9 says a byte that leaves the ledger   *)
  (* can never come back -- true, and the reason the residue trick      *)
  (* fails.  But the round trip never has to leave: at an IDENTITY      *)
  (* mapping the two families are the SAME resource under a persistent  *)
  (* [kmap_at], so the crossing is an isomorphism and the timestamp and *)
  (* the bit ride through it untouched.  The tier the walker takes a    *)
  (* slot down to is not the RAW tier, it is the physical LEDGER.       *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_to_phys `{KTR : !CurKtier} (ξ : CtxId) (ppn : mword 44)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    pa_of ppn a = a ->
    kmap_at (svpn_of a) ppn KP_rw -∗ ctx_pointsto ξ a dq v -∗
    ctx_phys_pointsto ξ a dq v.
  Proof.
    intros Hid. rewrite ctx_pointsto_phys.
    iIntros "#Hk (%ppn' & #Hk' & _ & _ & Hb)".
    iDestruct (kmap_at_agree with "Hk Hk'") as %[<- _].
    by rewrite Hid.
  Qed.

  Lemma ctx_pointsto_of_phys `{KTR : !CurKtier} (ξ : CtxId) (ppn : mword 44)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    pa_of ppn a = a ->
    (uint a < 274877906944)%Z ->
    ktier_pin cur_ktier ppn a ->
    kmap_at (svpn_of a) ppn KP_rw -∗ ctx_phys_pointsto ξ a dq v -∗
    ctx_pointsto ξ a dq v.
  Proof.
    intros Hid Hc Hp. rewrite ctx_pointsto_phys.
    iIntros "#Hk Hb". iExists ppn. iFrame "Hk".
    iSplit; first done. iSplit; first done. by rewrite Hid.
  Qed.

End ctx.

(* The notation family, mirroring [mem_pointsto]'s ([RiscvPtsto.v]) with
   [↦c] in place of [↦ₘ]: the context index is AMBIENT ([cur_ctx], like
   the tier), so converted spec text reads as before --
   [a ↦c[ktb] v], [a ↦c v], [a ↦c{dq} v], [a ↦c□ v].  A statement that
   needs an EXPLICIT context (lock internals, the kit) spells
   [ctx_pointsto] directly.  At the M1 notation flip these became the
   [↦ₘ] spellings and [↦c] is retired by attrition.  The tier-bracket form
   goes through Iris's custom [dfrac] entry for the same lexer reason as
   [↦ₘ[kt]]'s (see the note there: a fused "]{" token would break
   ghost_map's [↪[γ]] tree-wide). *)
Notation "a ↦c{ dq } v" := (ctx_pointsto cur_ctx a dq v)
  (at level 20, format "a  ↦c{ dq }  v") : bi_scope.
Notation "a ↦c□ v" := (ctx_pointsto cur_ctx a DfracDiscarded v)
  (at level 20, format "a  ↦c□  v") : bi_scope.
Notation "a ↦c v" := (ctx_pointsto cur_ctx a (DfracOwn 1) v)
  (at level 20, format "a  ↦c  v") : bi_scope.
Notation "a ↦c[ kt ] dq v" := (ctx_pointsto (KTR := kt) cur_ctx a dq v)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦c[ kt ] dq  v") : bi_scope.

(* THE PAYLOAD WRAPPER (the M3 sweep's client spelling; the `weak-memory`
   branch's `<{ }>`, adopted with ONE deliberate change).  A lock client
   writes its payload as a plain [iProp] with the ambient spellings; this
   turns it into the [CtxId → iProp] the lock surface needs as a CONSTANT
   embedding.

   IT IS A COMBINATOR, NOT A λ.  Any [CurCtx]-typed binder -- even
   anonymous -- is a TC candidate inside [P], resolved site-dependently
   (the silent-drop hazard, measured live twice); with [const_pay], [P]
   is elaborated as the combinator's ARGUMENT -- outside any
   [CurCtx]-typed binder -- so its ambient facts always bind the
   caller's context, identically at every site.
   THE SPELLING IS [<{ P }>] AND NOT [<[ P ]>]: stdpp's insert notation
   shares the [<[] prefix and Coq reports the two as incompatible
   (measured on the branch; the brace form is free). *)
Definition const_pay {Σ : gFunctors} (P : iProp Σ) : CtxId → iProp Σ :=
  λ _, P.
Notation "<{ P }>" := (const_pay P%I)
  (at level 0, P at level 200, format "<{  P  }>").

(* the combinator's transport obligation: same guard role and priority
   story as [ctx_morph_const] (which still serves bare λ-spellings). *)
Global Instance ctx_morph_const_pay `{!riscvGS Σ} (P : iProp Σ) :
  CtxMorph (const_pay P) | 99.
Proof. iIntros (ξ ξ') "Hd HP !>". iFrame. Qed.

(* The class TYPE is transparent to typeclass unification: [CurCtx] is
   definitionally [CtxId], and instance search must see through the
   wrapper's binder type or every [Persistent (is_lock … <{P}>)] /
   [CtxMorph <{P}>] resolution dies at the (CurCtx → iProp) vs
   (CtxId → iProp) seam.  This transparency is about the TYPE only; which
   ambient [CurCtx] INSTANCE a term picks up is unaffected (the
   silent-drop hazard in tso-port.md §2d concerns instance selection, not
   type unfolding). *)
Global Typeclasses Transparent CurCtx.

(* ================================================================== *)
(* THE M1 NOTATION FLIP (stage 1: the byte and 8-byte-word families).
   The [↦ₘ] and [↦₈] spellings are REBOUND here to the context-indexed
   facts; this declaration OVERRIDES [RiscvPtsto]'s in every file that
   imports this one after [RiscvPtsto].  Files below this one -- the kit
   -- never import it and keep the raw meanings; that split IS the seam.
   The spellings are character-identical, which is the whole point:
   statement text above the seam does not change, its MEANING does.
   [↦c] is a synonym, retired by attrition.  Stage 2 flips
   [↦₄]/[↦₂]/[↦ₛ]/[↦ₚ]; [↦ₓ] (text) and [↦ᵣ] (registers) NEVER flip --
   text is timestamp-0 context-free by the port's ruling, and registers
   are per-hart machine state. *)
Notation "a ↦ₘ{ dq } v" := (ctx_pointsto cur_ctx a dq v)
  (at level 20, format "a  ↦ₘ{ dq }  v") : bi_scope.
Notation "a ↦ₘ□ v" := (ctx_pointsto cur_ctx a DfracDiscarded v)
  (at level 20, format "a  ↦ₘ□  v") : bi_scope.
Notation "a ↦ₘ v" := (ctx_pointsto cur_ctx a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₘ  v") : bi_scope.
Notation "a ↦ₘ[ kt ] dq v" := (ctx_pointsto (KTR := kt) cur_ctx a dq v)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦ₘ[ kt ] dq  v") : bi_scope.

Notation "a ↦₈{ dq } w" := (ctx_word_pointsto cur_ctx a dq w)
  (at level 20, format "a  ↦₈{ dq }  w") : bi_scope.
Notation "a ↦₈ w" := (ctx_word_pointsto cur_ctx a (DfracOwn 1) w)
  (at level 20, format "a  ↦₈  w") : bi_scope.
Notation "a ↦₈□ w" := (ctx_word_pointsto cur_ctx a DfracDiscarded w)
  (at level 20, format "a  ↦₈□  w") : bi_scope.
Notation "a ↦₈[ kt ] dq w" := (ctx_word_pointsto (KTR := kt) cur_ctx a dq w)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦₈[ kt ] dq  w") : bi_scope.

(* ================================================================== *)
(* M1 STAGE 2: the [↦₂] and [↦₄] families.  Same mechanism as stage 1 --
   the spellings are character-identical, the MEANING becomes the
   context-indexed tower, and import order decides (a file that imports
   this one after RiscvPtsto parses the flipped meaning; the kit below
   never imports it and keeps the raw one).  All four dfrac spellings of
   each family are re-declared, bracket form included, with the modifiers
   copied EXACTLY -- an omitted [dq custom dfrac at level 1] leaves the
   ε-dq spellings parsing raw, silently.

   [↦ₛ] IS DELIBERATELY NOT FLIPPED; see the block after the seal. *)
Notation "a ↦₂{ dq } w" := (ctx_word2_pointsto cur_ctx a dq w)
  (at level 20, format "a  ↦₂{ dq }  w") : bi_scope.
Notation "a ↦₂ w" := (ctx_word2_pointsto cur_ctx a (DfracOwn 1) w)
  (at level 20, format "a  ↦₂  w") : bi_scope.
Notation "a ↦₂□ w" := (ctx_word2_pointsto cur_ctx a DfracDiscarded w)
  (at level 20, format "a  ↦₂□  w") : bi_scope.
Notation "a ↦₂[ kt ] dq w" := (ctx_word2_pointsto (KTR := kt) cur_ctx a dq w)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦₂[ kt ] dq  w") : bi_scope.

Notation "a ↦₄{ dq } w" := (ctx_word4_pointsto cur_ctx a dq w)
  (at level 20, format "a  ↦₄{ dq }  w") : bi_scope.
Notation "a ↦₄ w" := (ctx_word4_pointsto cur_ctx a (DfracOwn 1) w)
  (at level 20, format "a  ↦₄  w") : bi_scope.
Notation "a ↦₄□ w" := (ctx_word4_pointsto cur_ctx a DfracDiscarded w)
  (at level 20, format "a  ↦₄□  w") : bi_scope.
Notation "a ↦₄[ kt ] dq w" := (ctx_word4_pointsto (KTR := kt) cur_ctx a dq w)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦₄[ kt ] dq  w") : bi_scope.

(* WHY [↦ₛ] STAYS RAW (the stage-2 assessment, tso-machine-flip.md §6
   amendment A6.15).  It was listed with [↦₂]/[↦₄] and it is the one that
   should NOT move, for two independent reasons:

   1. IT WOULD PUT A CONTEXT INSIDE [is_lock].  [WpLock.lock_name] is
      [∃ p, word_pointsto (lock_name_field lk) □ p ∗ p ↦ₛ□ s], and
      [lock_name] is half of the PERSISTENT lock handle.  Flipping [↦ₛ]
      makes the handle ξ-dependent for real -- not as the artifact of the
      constant embedding that tso-port.md §0.11′ measured, but in the
      statement -- and a boot-minted [is_lock] then cannot be stated at
      another thread.  That is tso-port.md §0.8′ RULING 2, and it is the
      root the park and trap protocols were just routed around.
   2. IT WOULD BUY NOTHING.  Every string fact in this tree is a
      DISCARDED image literal (lock names, panic messages).  A discarded
      byte is read-only forever, so it can never owe [Wobl_ram]; and its
      load obligation is discharged by the PRISTINE gate (A6.10), which
      needs no context at all.  The ledger index would be dead weight on
      37 files.

   Net effect of flipping it would be: one [forget] use removed in
   [KernelDataInv.kernel_data_string], one ADDED in [WpLock.lock_name_intro],
   a [CurCtx] binder on 37 files, and a real ξ in the lock handle.  So
   [↦ₛ] leaves the stage-2 list and joins [↦ₓ]/[↦ᵣ]/[↦ₚ] as deliberately
   raw. *)

(* The seal.  [ctx_dom] and [hart_view_lb] stay opaque too: nothing above
   this file may learn their bodies, and nothing may learn what
   [ctx_parked] does with its stamp. *)
Global Typeclasses Opaque own_context ctx_parked hart_view_lb
  ctx_pointsto ctx_dom ctx_phys_pointsto.
Global Opaque own_context ctx_parked hart_view_lb ctx_pointsto ctx_dom
  ctx_phys_pointsto.
(* [ctx_phys_pointsto] (A6.16) is sealed for exactly [ctx_pointsto]'s
   reason: the rehearsal's finding was that a PERMEABLE seal lets ctx↔raw
   cross silently by δ, and the physical family faces [phys_pointsto] the
   way the VA one faces [mem_pointsto].  [ctx_phys_word_pointsto] is NOT
   sealed -- a tower over the sealed byte, like [ctx_word_pointsto]. *)
(* [ctx_word_pointsto] is NOT sealed at all: it is a tower OVER the sealed
   byte fact, so exposing its ⌜aligned⌝ ∗ big-op shape leaks nothing --
   and the tree's proofs destruct/frame the word shape structurally. *)
