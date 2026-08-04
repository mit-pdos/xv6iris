(* ====================================================================== *)
(* BootCarve.v -- THE BOOT-IMAGE CARVING LIBRARY.                          *)
(*                                                                         *)
(* A boot client is handed, by [RiscvAdequacy.power_boot_res] (and by       *)
(* [riscv_system_adequacy]'s single-generation analogue), the machine's     *)
(* memory as RAW per-byte [pointsto] fragments plus the RAW static-kmap     *)
(* fragments -- and nothing else.  Everything a kernel WP precondition      *)
(* mentions ([KernelText.kernel_text], [KernelDataInv.kernel_data], the     *)
(* typed cells, the kalloc page run) has to be CARVED out of those two.     *)
(* This file is where that carving lives, so that the eventual boot         *)
(* composition is pure assembly.                                           *)
(*                                                                         *)
(* Slice 1 -- the THREE-WAY SPLIT at [text_end]:                            *)
(*   §1 [kmap_static_claims_intro] -- the persisted static-claims bundle,   *)
(*      out of the raw kmap fragments.                                     *)
(*   §2 [boot_bytes_split] -- the raw byte map cut at [text_end].           *)
(*   §3 [boot_text_persist] -- the sub-[text_end] half, upgraded through    *)
(*      the identity claim to [↦ₓ] and PERSISTED to the immutable image     *)
(*      [↦ₓ□].                                                             *)
(*   §4 [boot_data_own] -- the [text_end]-and-above half, upgraded to the   *)
(*      OWNED [↦ₘ] image.                                                  *)
(*                                                                         *)
(* These four were, until this file existed, inlined in                     *)
(* [riscv_system_adequacy]'s proof; that proof now applies them, so there   *)
(* is ONE copy of each and the crash-layer boot client (which has the same  *)
(* raw inputs at a fresh era) reuses it rather than duplicating it.  Order  *)
(* matters and is fixed by the resources, not by taste: §1 FIRST -- the     *)
(* claims come from the kmap fragments, which do not overlap the memory map *)
(* at all, and both §3 and §4 need the whole bundle.                        *)
(* ====================================================================== *)
(* NB the memory is taken as the GSTATE, never as a [gmap Arch.pa (bv 8)]
   binder: the kmap files this file needs ([KptPt]/[KMap], for the mword-27
   claim instances) make [Instances.Countable_mword] canonical, so a binder
   written here would be a DIFFERENT type from [RiscvLang]'s [gmem] field --
   the two print identically and the caller fails with "has type
   @gmap Arch.pa (bv_eq_dec …) … while it is expected to have type
   @gmap Arch.pa (@Instances.Decidable_eq_mword …) …".  Naming the state
   sidesteps the whole trap and is what the callers have anyway
   (durable-notes' [gmap Arch.pa] binder trap). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import KptPt KMap.
Local Open Scope Z_scope.

Section BootCarve.
  Context `{!riscvGS Σ}.

  (* the raw memory conjunct's shape, named once: a per-byte [pointsto] at
     full ownership, exactly what [gen_heap_init_names] mints. *)
  Definition boot_raw_bytes (g : gstate) : iProp Σ :=
    ([∗ map] a ↦ b ∈ g.(gmem), pointsto (L:=Arch.pa) (V:=bv 8) a (DfracOwn 1) b)%I.

  (* the two halves of the rwx split (KERNEL TEXT below [etext], kernel DATA
     at and above it -- RiscvPtsto's [addr_is_text] / [addr_is_kdata]). *)
  Definition sub_text (g : gstate) :=
    base.filter (fun p : Arch.pa * bv 8 => (uint p.1 < text_end)%Z) g.(gmem).
  Definition supra_text (g : gstate) :=
    base.filter (fun p : Arch.pa * bv 8 => (text_end <= uint p.1)%Z) g.(gmem).

  (* the two halves' RAW forms.  Like [boot_raw_bytes] they are indexed by the
     STATE, never by a map binder (see the header note). *)
  Definition boot_text_raw (g : gstate) : iProp Σ :=
    ([∗ map] a ↦ b ∈ sub_text g, pointsto (L:=Arch.pa) (V:=bv 8) a (DfracOwn 1) b)%I.
  Definition boot_data_raw (g : gstate) : iProp Σ :=
    ([∗ map] a ↦ b ∈ supra_text g, pointsto (L:=Arch.pa) (V:=bv 8) a (DfracOwn 1) b)%I.

  (* the literal COMPLEMENT of [sub_text]'s predicate -- [map_filter_union_
     complement]'s own second half.  Named because a [¬] written inside an
     [iAssert] parses in [bi_scope] and elaborates as bi-negation. *)
  Local Definition co_sub_text (g : gstate) :=
    base.filter (fun p : Arch.pa * bv 8 => ¬ (uint p.1 < text_end)%Z) g.(gmem).

  Local Lemma supra_co_sub (g : gstate) : supra_text g = co_sub_text g.
  Proof.
    rewrite /supra_text /co_sub_text.
    apply (proj1 (map_filter_ext _ _ g.(gmem))). intros i x _. cbn. split; lia.
  Qed.

  (* ================================================================== *)
  (* §1  The persisted static-claims bundle.                            *)
  (* ================================================================== *)

  (* SYMBOLIC: the ~49k-entry [kmap_M0] is never enumerated -- one
     [big_sepM_bupd] over a [big_sepM_mono]. *)
  Lemma kmap_static_claims_intro :
    ([∗ map] vpn ↦ e ∈ kmap_M0, ghost_map_elem kmap_name vpn (DfracOwn 1) e)
    ==∗ kmap_static_claims.
  Proof.
    iIntros "Hkfrags". rewrite /kmap_static_claims. iApply big_sepM_bupd.
    iApply (big_sepM_mono with "Hkfrags").
    iIntros (vpn e Hlk) "Hfrag".
    iMod (ghost_map_elem_persist with "Hfrag") as "Hf".
    iModIntro. rewrite /kmap_at. destruct e as [ppn pc]. iExact "Hf".
  Qed.

  (* ================================================================== *)
  (* §2  The cut at [text_end].                                         *)
  (* ================================================================== *)

  Lemma boot_bytes_split (g : gstate) :
    boot_raw_bytes g ⊢ boot_text_raw g ∗ boot_data_raw g.
  Proof.
    rewrite /boot_raw_bytes /boot_text_raw /boot_data_raw.
    pose proof (map_filter_union_complement
                  (fun p : Arch.pa * bv 8 => (uint p.1 < text_end)%Z) g.(gmem)) as Heq.
    iIntros "H".
    iAssert ([∗ map] a ↦ b ∈ (sub_text g ∪ co_sub_text g),
               pointsto (L:=Arch.pa) (V:=bv 8) a (DfracOwn 1) b)%I with "[H]" as "H'".
    { rewrite /sub_text /co_sub_text Heq. iExact "H". }
    iDestruct (big_sepM_union with "H'") as "[Ht Hd]";
      [rewrite /sub_text /co_sub_text; apply map_disjoint_filter_complement |].
    rewrite /sub_text. iFrame "Ht".
    rewrite (supra_co_sub g). iExact "Hd".
  Qed.

  (* ================================================================== *)
  (* §3  The text half: raw → [↦ₓ] → the persistent image [↦ₓ□].        *)
  (* ================================================================== *)

  (* The per-byte assembly is: raw [pointsto] + the byte's RAM fact make a
     [↦ₚ]; the static claim off the bundle turns that into [↦ₓ]
     ([KMap.phys_ident_text], the uniform-claims PHYSICAL tier); and
     [text_pointsto_persist] freezes it.  [Hram] is the caller's "nothing
     outside RAM" fact -- [boot_facts]' second clause, or
     [riscv_system_adequacy]'s [Hram] premise. *)
  Lemma boot_text_persist (g : gstate) :
    (forall a b, g.(gmem) !! a = Some b -> addr_is_ram a) ->
    kmap_static_claims -∗ boot_text_raw g
    ==∗ ([∗ map] a ↦ b ∈ sub_text g, a ↦ₓ□ b).
  Proof.
    iIntros (Hram) "#Hkbundle Ht".
    rewrite /boot_text_raw.
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Ht").
    iIntros "!>" (a b Ha) "Hb".
    apply map_lookup_filter_Some in Ha. destruct Ha as [Ha Hlt]. cbn in Hlt.
    pose proof (Hram a b Ha) as [Hlo _].
    assert (Htext : addr_is_text a) by (split; [exact Hlo | exact Hlt]).
    assert (Hcanon : (uint a < 274877906944)%Z)
      by (unfold addr_is_text, text_end in Htext; lia).
    iApply text_pointsto_persist.
    iApply (phys_ident_text a (DfracOwn 1) b (text_svpn_class a Htext) Htext Hcanon
              with "Hkbundle [Hb]").
    rewrite /phys_pointsto. iFrame "Hb". iPureIntro. exact (addr_is_text_ram a Htext).
  Qed.

  (* ================================================================== *)
  (* §4  The data half: raw → the OWNED [↦ₘ] image.                     *)
  (* ================================================================== *)

  Lemma boot_data_own (g : gstate) :
    (forall a b, g.(gmem) !! a = Some b -> addr_is_ram a) ->
    kmap_static_claims -∗ boot_data_raw g
    -∗ ([∗ map] a ↦ b ∈ supra_text g, a ↦ₘ b).
  Proof.
    iIntros (Hram) "#Hkbundle Hd".
    rewrite /boot_data_raw.
    iApply (big_sepM_impl with "Hd").
    iIntros "!>" (a b Ha) "Hb".
    apply map_lookup_filter_Some in Ha. destruct Ha as [Ha Hge]. cbn in Hge.
    pose proof (Hram a b Ha) as [_ Hhi].
    assert (Hkd : addr_is_kdata a) by (split; [lia | exact Hhi]).
    assert (Hcanon : (uint a < 274877906944)%Z)
      by (unfold addr_is_kdata, ram_base, ram_size, text_end in Hkd; lia).
    iApply (phys_ident_mem a (DfracOwn 1) b (kdata_svpn_class a Hkd)
              (addr_is_kdata_ram a Hkd) Hcanon with "Hkbundle [Hb]").
    rewrite /phys_pointsto. iFrame "Hb". iPureIntro. exact (addr_is_kdata_ram a Hkd).
  Qed.

End BootCarve.
