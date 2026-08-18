(* KMap.v -- the kernel-mapping ghost AUTH + static bundle (rwx-kmap /
   uniform-claims).

   The persistent CLAIM [kmap_at vpn ppn pc] itself now lives in
   RiscvPtsto (it needs only [riscv_kmapGS] + the ghost_map ↪-notation): a
   BARE persisted fragment [vpn ↪[kmap_name]□ (ppn, pc)], "under the current
   and all future kernel translation regimes, vpn maps to ppn at class pc".
   Uniqueness is ghost-map library agreement ([kmap_at_agree]).

   This file keeps everything that needs [kmap_M0] (KptPt): the AUTH
   ([kmap_auth M] = bare [ghost_map_auth]), the lookup/insert working
   lemmas, and the persistent STATIC-CLAIMS bundle [kmap_static_claims]
   (every identity mapping's fragment, minted+persisted at adequacy init and
   carried in [hw_config]) with its extraction lemma [kmap_static_claims_at].

   Under full fragment-keying the persisted fragments themselves are the
   monotonicity witnesses, so nothing rides the auth: the old
   [kmap_M0 ⊆ M] / [kmap_wf] reification is GONE, and the auth is bare.

   The auth is a GLOBAL BOOT TOKEN (claude-notes/projects/
   bare-inv-generic.md): adequacy mints it, it travels through main's
   precondition into kvminithart, which grows it by the trampoline + 64
   kstack entries and retires it into [KptShare.kpt_inv].  It is NOT in the
   translation slot's Bare arm any more -- that arm is per-hart and holds
   nothing global, and honors exactly the IDENTITY claims (the [sr_adm]
   field, SRegime.v).  See claude-notes/design/tlb-translation.md. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvPtsto.
Require Import KptPt.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Allocation (adequacy init): ONE [ghost_map_alloc] mints the auth over  *)
(* the whole static map; the returned static fragments are PERSISTED and  *)
(* distributed (into the identity ↦ₘ/↦ₓ□ and the bundle below).           *)
(* ===================================================================== *)
Lemma kmap_alloc `{!ghost_mapG Σ (mword 27) (mword 44 * kperm)} :
  ⊢ |==> ∃ γ : gname, ghost_map_auth γ 1 kmap_M0.
Proof.
  iMod (ghost_map_alloc kmap_M0) as (γ) "[Hauth _]".
  iModIntro. iExists γ. iExact "Hauth".
Qed.

Section KMap.
  Context `{!riscvGS Σ}.
  (* the ambient TIER: the ↦ₘ ⇄ ↦ₚ bridge below is tier-generic -- it
     never looks at the pin in the consuming direction, and in the
     producing direction the static claim it already demands gives the
     identity, hence the pin at EVERY tier ([ktier_pin_of_id]). *)
  Context `{KTR : !CurKtier}.

  (* ===================================================================== *)
  (* The bare auth.                                                         *)
  (* ===================================================================== *)
  Definition kmap_auth (M : gmap (mword 27) (mword 44 * kperm)) : iProp Σ :=
    ghost_map_auth kmap_name 1 M.

  Global Instance kmap_auth_timeless M : Timeless (kmap_auth M).
  Proof. apply _. Qed.

  (* ---- the two working lemmas ---- *)

  (* a claim agrees with the auth: its vpn is mapped as claimed *)
  Lemma kmap_at_lookup (M : gmap (mword 27) (mword 44 * kperm))
      (vpn : mword 27) (ppn : mword 44) (pc : kperm) :
    kmap_auth M -∗ kmap_at vpn ppn pc -∗ ⌜M !! vpn = Some (ppn, pc)⌝.
  Proof.
    rewrite /kmap_auth /kmap_at.
    iIntros "Hauth Hfrag".
    iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hl.
    iPureIntro. exact Hl.
  Qed.

  (* dynamic minting (the kvminithart switch inserts the kstack entries,
     one [kmap_insert] each, persisting the fragments as claims) *)
  Lemma kmap_insert (M : gmap (mword 27) (mword 44 * kperm))
      (vpn : mword 27) (ppn : mword 44) (pc : kperm) :
    M !! vpn = None ->
    kmap_auth M ==∗ kmap_auth (<[vpn := (ppn, pc)]> M) ∗ kmap_at vpn ppn pc.
  Proof.
    rewrite /kmap_auth /kmap_at.
    iIntros (Hfresh) "Hauth".
    iMod (ghost_map_insert_persist vpn (ppn, pc) Hfresh with "Hauth")
      as "[Hauth #Hfrag]".
    iModIntro. iFrame "Hauth". iExact "Hfrag".
  Qed.

  (* ===================================================================== *)
  (* The persistent STATIC-CLAIMS bundle (uniform-claims stage A'):         *)
  (* every identity mapping's fragment, minted and persisted at adequacy    *)
  (* init and carried in [hw_config].  Never normalized: extraction is by   *)
  (* [big_sepM_lookup] + [kmap_M0_lookup].                                  *)
  (* ===================================================================== *)

  Definition kmap_static_claims : iProp Σ :=
    ([∗ map] vpn ↦ e ∈ kmap_M0, kmap_at vpn e.1 e.2)%I.

  Global Instance kmap_static_claims_persistent : Persistent kmap_static_claims.
  Proof. apply _. Qed.

  (* extraction: any statically classified vpn's identity claim, off the
     bundle -- this is how a proof with no claim in hand gets one (the
     bundle is persistent and rides in [hw_config], so it is ambient) *)
  Lemma kmap_static_claims_at (vpn : mword 27) (pc : kperm) :
    kmap_static vpn pc ->
    kmap_static_claims -∗ kmap_at vpn (kpt_leaf_ppn vpn) pc.
  Proof.
    iIntros (Hs) "#Hb".
    iApply (big_sepM_lookup _ _ vpn (kpt_leaf_ppn vpn, pc) with "Hb").
    rewrite kmap_M0_lookup. unfold kmap_static in Hs. rewrite Hs. reflexivity.
  Qed.

  (* KEEP-UNREFERENCED: against the EXACT static auth (i.e. before
     kvminithart's mint), a claim's vpn is statically classified and its ppn
     is the identity leaf ppn.  This used to be the Bare arm's honoring
     mechanism; the Bare arm now takes the identity as an [sr_adm] premise
     that the consumer's own resource supplies, so nothing global is
     needed and every hart can be Bare at once. *)
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

  (* ===================================================================== *)
  (* Tier bridge (uniform-claims PHYSICAL TIER): a static (identity) kernel *)
  (* va converts between the VA-based ↦ₘ/↦ₓ and the PHYSICAL ↦ₚ tiers.  The *)
  (* static claim comes off the bundle ([kmap_static_claims_at]); the ppn   *)
  (* is pinned to [kpt_leaf_ppn] ([kmap_at_agree], via [mem_pointsto_pin]), *)
  (* and [pa_of_id] gives [pa_of (kpt_leaf_ppn (svpn_of pa)) pa = pa].      *)
  (* ===================================================================== *)

  (* disassembly ↦ₘ → ↦ₚ: the byte a static kdata va owns IS the physical
     byte at [pa] *)
  Lemma mem_ident_phys (pa : mword 64) dq b :
    kmap_static (svpn_of pa) KP_rw ->
    kmap_static_claims -∗ pa ↦ₘ{dq} b -∗ pa ↦ₚ{dq} b.
  Proof.
    iIntros (Hs) "#Hb H".
    iDestruct (kmap_static_claims_at (svpn_of pa) KP_rw Hs with "Hb") as "#Hk0".
    iDestruct (mem_pointsto_pin pa dq b (kpt_leaf_ppn (svpn_of pa)) with "Hk0 H")
      as "(%Hc & %Hd & _ & Hp & _)".
    rewrite (pa_of_id pa Hc) in Hd.
    iEval (rewrite (pa_of_id pa Hc)) in "Hp".
    rewrite /phys_pointsto. iFrame "Hp". iPureIntro. exact Hd.
  Qed.

  (* assembly ↦ₚ → ↦ₘ: a physical byte at a static kdata va re-forms ↦ₘ *)
  Lemma phys_ident_mem (pa : mword 64) dq b :
    kmap_static (svpn_of pa) KP_rw ->
    addr_is_ram pa -> (uint pa < 274877906944)%Z ->
    kmap_static_claims -∗ pa ↦ₚ{dq} b -∗ pa ↦ₘ{dq} b.
  Proof.
    iIntros (Hs Hram Hc) "#Hb H".
    iDestruct (kmap_static_claims_at (svpn_of pa) KP_rw Hs with "Hb") as "#Hk0".
    iEval (rewrite /phys_pointsto) in "H". iDestruct "H" as "[Hp _]".
    rewrite /mem_pointsto. iExists (kpt_leaf_ppn (svpn_of pa)).
    rewrite (pa_of_id pa Hc). iFrame "Hk0 Hp". iPureIntro.
    split; [exact Hc | split; [exact Hram |
      exact (ktier_pin_of_id cur_ktier (kpt_leaf_ppn (svpn_of pa)) pa (pa_of_id pa Hc))]].
  Qed.

  (* ---- TIER STRENGTHENING (the counterpart of [mem_ktier_mono]).  The pin
     is PURE, so a datum that LOST it by weakening -- or one minted at KT1 --
     can be brought back to KT0 with no ghost cost, given only the pure
     static class of its va: the ambient bundle supplies that vpn's identity
     claim, [kmap_at_agree] forces the datum's existential ppn to match it,
     and [pa_of_id] turns that into the identity.  This is exactly the dance
     [mem_ident_phys] runs, stopped one step earlier, and it is what makes
     "weaken to pass through a KT1 context, strengthen on the way back" a
     complete round trip rather than a one-way door. ---- *)
  Lemma mem_ktier_pin_intro (kt : ktier) (va : mword 64) dq b :
    kmap_static (svpn_of va) KP_rw ->
    kmap_static_claims -∗ va ↦ₘ[kt]{dq} b -∗ va ↦ₘ[KT0]{dq} b.
  Proof.
    iIntros (Hs) "#Hb H".
    iDestruct (kmap_static_claims_at (svpn_of va) KP_rw Hs with "Hb") as "#Hk0".
    iDestruct (mem_pointsto_pin (KTR := kt) va dq b (kpt_leaf_ppn (svpn_of va))
                 with "Hk0 H") as "(%Hc & %Hd & _ & Hp & _)".
    rewrite /mem_pointsto. iExists (kpt_leaf_ppn (svpn_of va)).
    iFrame "Hk0 Hp". iPureIntro.
    split; [exact Hc | split; [exact Hd | exact (pa_of_id va Hc)]].
  Qed.

  (* text tier: ↦ₓ ⇄ ↦ₚ at KP_rx / addr_is_text *)
  Lemma text_ident_phys (pa : mword 64) dq b :
    kmap_static (svpn_of pa) KP_rx ->
    kmap_static_claims -∗ pa ↦ₓ{dq} b -∗ pa ↦ₚ{dq} b.
  Proof.
    iIntros (Hs) "#Hb H".
    iDestruct (kmap_static_claims_at (svpn_of pa) KP_rx Hs with "Hb") as "#Hk0".
    iDestruct (text_pointsto_pin pa dq b (kpt_leaf_ppn (svpn_of pa)) with "Hk0 H")
      as "(%Hc & %Hd & _ & Hp & _)".
    rewrite (pa_of_id pa Hc) in Hd.
    iEval (rewrite (pa_of_id pa Hc)) in "Hp".
    rewrite /phys_pointsto. iFrame "Hp". iPureIntro. exact (addr_is_text_ram _ Hd).
  Qed.

  (* PAGE disassembly ↦ₘ → ↦ₚ over a 4096-byte page (the kalloc-page ->
     PT-node boundary in the walk): each byte of an identity kdata page
     converts pointwise via [mem_ident_phys].  The per-byte static premise is
     supplied by [page_in_range_addr_is_kdata] + [kdata_svpn_class] at the
     call site (the page is [page_valid]). *)
  Lemma mem_page_to_phys (p : mword 64) dq (b : bv 8) :
    (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add p j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 4096, (pa_add p j) ↦ₘ{dq} b) -∗
    ([∗ list] j ∈ seq 0 4096, (pa_add p j) ↦ₚ{dq} b).
  Proof.
    iIntros (Hstat) "#Hb Hbytes".
    iApply (big_sepL_impl with "Hbytes").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    iApply (mem_ident_phys (pa_add p (0 + k)%nat) dq b (Hstat (0 + k)%nat ltac:(lia)) with "Hb H").
  Qed.

  Lemma phys_ident_text (pa : mword 64) dq b :
    kmap_static (svpn_of pa) KP_rx ->
    addr_is_text pa -> (uint pa < 274877906944)%Z ->
    kmap_static_claims -∗ pa ↦ₚ{dq} b -∗ pa ↦ₓ{dq} b.
  Proof.
    iIntros (Hs Htx Hc) "#Hb H".
    iDestruct (kmap_static_claims_at (svpn_of pa) KP_rx Hs with "Hb") as "#Hk0".
    iEval (rewrite /phys_pointsto) in "H". iDestruct "H" as "[Hp _]".
    rewrite /text_pointsto. iExists (kpt_leaf_ppn (svpn_of pa)).
    rewrite (pa_of_id pa Hc). iFrame "Hk0 Hp". iPureIntro.
    (* TIER-GENERIC: an identity-mapped va satisfies the pin at EVERY tier,
       so this keeps its exact signature and serves whatever tier the
       caller's ambient instance selects (as [phys_to_mem_claim] does). *)
    split; [exact Hc | split; [exact Htx |
      exact (ktier_pin_of_id cur_ktier (kpt_leaf_ppn (svpn_of pa)) pa (pa_of_id pa Hc))]].
  Qed.

End KMap.
