(* KMap.v -- the monotone kernel-mapping claim ghost (rwx-kmap project).

   [kmap_at vpn ppn pc] is a persistent, timeless CLAIM: "under the
   current and all future kernel translation regimes, virtual page [vpn]
   maps to physical page [ppn] with (at least) permission class [pc]".

   INTERFACE: the static identity regions (kernel text / data / devices,
   classified by KptPt §15's [kmap_class]) ride a PURE arm -- a static
   claim is constructible from address arithmetic alone ([kmap_at_static]),
   no resources, anywhere -- while dynamically minted mappings (the
   per-proc kernel stacks) are persisted [ghost_map] fragments.

   STORAGE: the authoritative map ([kmap_auth M]) holds static AND
   dynamic entries -- [M] always extends [kmap_M0] ([kmap_wf]) -- so the
   generalized tree spec above ([kpt_tree_spec_gen], KptTree) is a
   uniform two-clause form over [M], and every absorption proof is
   single-path through [kmap_at_lookup]: both claim arms land in the
   same [M !! vpn = Some (ppn, pc)] conclusion.

   The auth lives in the translation slot's two arms (IntrDefs
   [strans_inv]): the Bare arm holds [kmap_auth kmap_M0] EXACTLY, so
   every claim honored under Bare is a static identity entry
   ([kmap_at_M0_static]); the KPT arm holds [kmap_auth M] for the
   existential [M] of [tlb_inv_pt].  Monotonicity: fragments are
   persisted and entries are never deleted.  Bare->KPT is ONE-WAY: once
   a kstack fragment is persisted, [kmap_auth kmap_M0] can never be
   re-established (the fragment's vpn looks up to [None] in [kmap_M0]).

   The TRAMPOLINE mapping is deliberately NOT a claim (a non-identity
   pure fact would be usable under Bare -- unsound); it stays the
   dedicated clause in the tree spec, and [kmap_wf_tramp] keeps it out
   of [M].  See claude-notes/projects/rwx-kmap.md. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvPtsto.
Require Import KptPt.
Require Import KptExecMap.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 Pure layer: the dynamic-entry window and the auth well-formedness.  *)
(* ===================================================================== *)

(* the per-proc kernel-stack vpn window, just below the trampoline:
   KSTACK(p) = TRAMPOLINE - (p+1)*2*PGSIZE for p in [0, NPROC=64), i.e.
   the stack vpns are {tramp_vpn - 2(p+1)} (odd offsets are the guard
   slots).  The wf invariant only needs a WINDOW disjoint from the
   static regions and excluding [tramp_vpn] itself; the kvminithart
   switch lemma inserts exactly the 64 stack vpns. *)
Definition kstack_vpn_lo : Z := 0x3FFFFFF - 128.
Definition kstack_vpn_range (vpn : mword 27) : Prop :=
  kstack_vpn_lo <= bv_unsigned vpn < 0x3FFFFFF.

(* a legal dynamic entry: a kstack vpn mapped to a whole RAM page at
   class RW *)
Definition kmap_dyn_ok (vpn : mword 27) (e : mword 44 * kperm) : Prop :=
  kstack_vpn_range vpn /\
  ram_base <= bv_unsigned e.1 * 4096 /\
  (bv_unsigned e.1 + 1) * 4096 <= ram_base + ram_size /\
  e.2 = KP_rw.

(* the auth's well-formedness: M extends the static map, and every entry
   is a static entry or a legal dynamic one *)
Definition kmap_wf (M : gmap (mword 27) (mword 44 * kperm)) : Prop :=
  kmap_M0 ⊆ M /\
  (forall vpn e, M !! vpn = Some e -> kmap_M0 !! vpn = Some e \/ kmap_dyn_ok vpn e).

Lemma kmap_wf_M0 : kmap_wf kmap_M0.
Proof. split; [reflexivity | intros vpn e He; left; exact He]. Qed.

Lemma kmap_wf_insert (M : gmap (mword 27) (mword 44 * kperm))
    (vpn : mword 27) (e : mword 44 * kperm) :
  kmap_wf M -> M !! vpn = None -> kmap_dyn_ok vpn e ->
  kmap_wf (<[vpn := e]> M).
Proof.
  intros [Hsub Hent] Hfresh Hdyn. split.
  - transitivity M; [exact Hsub | apply insert_subseteq; exact Hfresh].
  - intros v e' Hl. destruct (decide (v = vpn)) as [-> | Hne].
    + rewrite lookup_insert in Hl. injection Hl as <-. right. exact Hdyn.
    + rewrite lookup_insert_ne in Hl; [| exact (not_eq_sym Hne)]. exact (Hent _ _ Hl).
Qed.

(* a wf map never carries the trampoline vpn (its static class is None
   and the dynamic window sits strictly below it) -- so the tree spec's
   dedicated tramp clause never collides with the maps-clause *)
Lemma kmap_wf_tramp (M : gmap (mword 27) (mword 44 * kperm)) :
  kmap_wf M -> M !! tramp_vpn = None.
Proof.
  intros [_ Hent].
  destruct (M !! tramp_vpn) as [e|] eqn:HM; [| reflexivity].
  exfalso.
  assert (Ht : bv_unsigned tramp_vpn = 0x3FFFFFF) by (vm_compute; reflexivity).
  destruct (Hent _ _ HM) as [H0 | Hd].
  - rewrite kmap_M0_lookup in H0.
    unfold kmap_class in H0. rewrite Ht in H0. vm_compute in H0. discriminate.
  - destruct Hd as [[_ Hhi] _]. lia.
Qed.

(* ===================================================================== *)
(* §2 The ghost: [kmap_at] claims over an explicitly-named auth.          *)
(* ===================================================================== *)

(* CpuId-style gname-in-class bundle (cf. [riscvGS]'s [uart_name]): the
   instance is constructed at adequacy init from [kmap_alloc]'s gname. *)
Class kmapGS (Σ : gFunctors) := KmapGS {
  kmap_inG :: ghost_mapG Σ (mword 27) (mword 44 * kperm);
  kmap_name : gname;
}.

(* allocation (adequacy/boot): ONE update mints the auth over the whole
   ~49k-entry static map -- the returned static fragments are dropped,
   static claims use the pure arm instead *)
Lemma kmap_alloc `{!ghost_mapG Σ (mword 27) (mword 44 * kperm)} :
  ⊢ |==> ∃ γ : gname, ghost_map_auth γ 1 kmap_M0.
Proof.
  iMod (ghost_map_alloc kmap_M0) as (γ) "[Hauth _]".
  iModIntro. iExists γ. iExact "Hauth".
Qed.

Section KMap.
  Context `{!kmapGS Σ}.

  (* THE claim.  Static arm: identity-only by construction (the ppn is
     pinned to [kpt_leaf_ppn vpn]).  Ghost arm: a persisted fragment. *)
  Definition kmap_at (vpn : mword 27) (ppn : mword 44) (pc : kperm) : iProp Σ :=
    (⌜kmap_static vpn pc /\ ppn = kpt_leaf_ppn vpn⌝
     ∨ vpn ↪[kmap_name]□ (ppn, pc))%I.

  Global Instance kmap_at_persistent vpn ppn pc : Persistent (kmap_at vpn ppn pc).
  Proof. apply _. Qed.
  Global Instance kmap_at_timeless vpn ppn pc : Timeless (kmap_at vpn ppn pc).
  Proof. apply _. Qed.

  (* the auth, with the wf facts bundled *)
  Definition kmap_auth (M : gmap (mword 27) (mword 44 * kperm)) : iProp Σ :=
    (ghost_map_auth kmap_name 1 M ∗ ⌜kmap_wf M⌝)%I.

  Global Instance kmap_auth_timeless M : Timeless (kmap_auth M).
  Proof. apply _. Qed.

  Lemma kmap_auth_intro (M : gmap (mword 27) (mword 44 * kperm)) :
    kmap_wf M -> ghost_map_auth kmap_name 1 M -∗ kmap_auth M.
  Proof. iIntros (Hwf) "Hauth". iFrame "Hauth". iPureIntro. exact Hwf. Qed.

  (* ---- the three working lemmas ---- *)

  (* free construction: any statically classified vpn's identity claim,
     from pure arithmetic alone *)
  Lemma kmap_at_static (vpn : mword 27) (pc : kperm) :
    kmap_static vpn pc -> ⊢ kmap_at vpn (kpt_leaf_ppn vpn) pc.
  Proof. intros Hs. iLeft. iPureIntro. split; [exact Hs | reflexivity]. Qed.

  (* THE synthesis point: both claim arms land in the SAME lookup fact,
     so everything downstream (the tree spec's uniform maps-clause) is
     single-path *)
  Lemma kmap_at_lookup (M : gmap (mword 27) (mword 44 * kperm))
      (vpn : mword 27) (ppn : mword 44) (pc : kperm) :
    kmap_auth M -∗ kmap_at vpn ppn pc -∗ ⌜M !! vpn = Some (ppn, pc)⌝.
  Proof.
    iIntros "[Hauth %Hwf] [%Hstat | Hfrag]".
    - destruct Hstat as [Hs ->]. iPureIntro.
      eapply lookup_weaken; [| exact (proj1 Hwf)].
      rewrite kmap_M0_lookup. unfold kmap_static in Hs. rewrite Hs. reflexivity.
    - iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hl.
      iPureIntro. exact Hl.
  Qed.

  (* dynamic minting (the kvminithart switch inserts the 64 kstack
     entries, one [kmap_insert] each, persisting the fragments) *)
  Lemma kmap_insert (M : gmap (mword 27) (mword 44 * kperm))
      (vpn : mword 27) (ppn : mword 44) (pc : kperm) :
    M !! vpn = None -> kmap_dyn_ok vpn (ppn, pc) ->
    kmap_auth M ==∗ kmap_auth (<[vpn := (ppn, pc)]> M) ∗ kmap_at vpn ppn pc.
  Proof.
    iIntros (Hfresh Hdyn) "[Hauth %Hwf]".
    iMod (ghost_map_insert_persist vpn (ppn, pc) Hfresh with "Hauth")
      as "[Hauth #Hfrag]".
    iModIntro. iSplitL "Hauth".
    - iFrame "Hauth". iPureIntro. apply kmap_wf_insert; assumption.
    - iRight. iExact "Hfrag".
  Qed.

  (* ---- derived facts ---- *)

  (* the Bare-arm honoring fact: against the EXACT static auth, every
     claim -- either arm -- is a static identity claim.  (This is also
     the one-way Bare->KPT argument: a persisted kstack fragment's vpn
     has [kmap_class = None], contradicting the conclusion.) *)
  Lemma kmap_at_M0_static (vpn : mword 27) (ppn : mword 44) (pc : kperm) :
    kmap_auth kmap_M0 -∗ kmap_at vpn ppn pc -∗
    ⌜kmap_static vpn pc /\ ppn = kpt_leaf_ppn vpn⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (kmap_at_lookup with "Hauth Hat") as %Hl.
    iPureIntro. rewrite kmap_M0_lookup in Hl.
    destruct (kmap_class vpn) as [pc'|] eqn:Hc; [| discriminate].
    cbn in Hl. injection Hl as <- <-.
    split; [exact Hc | reflexivity].
  Qed.

End KMap.
