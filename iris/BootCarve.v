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
Require Import RiscvExtras PowerBoot.   (* [boot_uint_pa]: the RAM-range address round-trip *)
Require Import StackOwn.                (* [pa_stk] / [uint_pa_stk] / [stack_own_phys] *)
Require Import KernelText.             (* the [kernel_text] bundle this produces *)
Require Import KernelDataInv.          (* ... and the [kernel_data] one *)
From Kernel Require KernelInstrs KernelData.
Local Open Scope Z_scope.

(* the addresses of the range [lo, lo + n), as a list.  A Fixpoint on the
   LENGTH (so §6's run induction is structural) with the [seq]-indexed
   spelling available through [zrun_fmap] (so a consumer can index its
   bytes by [pa_add base j]). *)
Fixpoint zrun (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S k => lo :: zrun (lo + 1) k end.

(* the two bits of plain-[Z] arithmetic the carve needs, packaged as closed
   facts (durable-notes: [lia] is unusable once an [mword] is in context). *)
Lemma z_mod8_sub (u d : Z) : u mod 8 = 0 -> (u - 8 * d) mod 8 = 0.
Proof.
  intro H. rewrite Zminus_mod H (Z.mul_comm 8 d) Z_mod_mult. reflexivity.
Qed.

Lemma zrun_fmap (lo : Z) (n : nat) :
  zrun lo n = (fun i : nat => lo + Z.of_nat i) <$> seq 0 n.
Proof.
  revert lo. induction n as [|k IH]; intro lo; [reflexivity |].
  cbn [zrun seq fmap list_fmap]. f_equal; [lia |].
  rewrite (IH (lo + 1)) -fmap_S_seq -list_fmap_compose.
  apply list_fmap_ext. intros i x _. cbn. lia.
Qed.

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

  (* ================================================================== *)
  (* §5  The NAMED text bundle.                                         *)
  (* ================================================================== *)

  (* [KernelText.kernel_text] is a [big_sepM] over the WHOLE 23340-entry
     [KernelInstrs.kernel_bytes], so producing it from the text half needs
     "every key of that map is in RAM and below [text_end]" -- and that is the
     fact whose hand proof is fatal (going back through [list_to_map] puts the
     list into the proof term and the [Qed] never returns).  It is therefore
     GENERATED, by tools/dump_elf.py, as [KernelInstrs.kernel_bytes_range]: a
     decidable [map_Forall] check closed by one [vm_compute], whose proof term
     is [eq_refl].  All this lemma does is bridge its LITERAL bounds (that file
     is below iris/ and cannot name [ram_lo]/[text_end]) and read the image
     value back out of [boot_byte]. *)

  (* the loader really did leave [kernel_bytes]' byte at its address *)
  Local Lemma boot_byte_text (a : Z) (b : bv 8) :
    KernelInstrs.kernel_bytes !! a = Some b -> boot_byte a = b.
  Proof.
    intro Hlk.
    pose proof (KernelInstrs.kernel_bytes_range a b Hlk) as Hr.
    unfold KernelInstrs.kernel_bytes_lo, KernelInstrs.kernel_bytes_hi in Hr.
    unfold boot_byte, boot_image.
    rewrite (map_lookup_filter_Some_2 _ _ a b);
      [ reflexivity
      | apply lookup_union_Some_l; exact Hlk
      | cbn; unfold img_end; lia ].
  Qed.

  (* [kernel_text] is PERSISTENT and so is the half it comes from, so nothing
     is consumed: the input can be re-used for the physical cuts. *)
  Lemma kernel_text_intro (g : gstate) :
    (forall a : Z, (ram_lo <= a < ram_hi)%Z ->
       g.(gmem) !! (SailStdpp.Values.mword_of_int a : Arch.pa) = Some (boot_byte a)) ->
    ([∗ map] a ↦ b ∈ sub_text g, a ↦ₓ□ b) -∗ kernel_text.
  Proof.
    iIntros (Hmem) "#Ht". rewrite /kernel_text.
    iApply big_sepM_intro. iIntros "!>" (a b Hlk).
    pose proof (KernelInstrs.kernel_bytes_range a b Hlk) as Hr.
    unfold KernelInstrs.kernel_bytes_lo, KernelInstrs.kernel_bytes_hi in Hr.
    assert (Hram : (ram_lo <= a < ram_hi)%Z) by (unfold ram_lo, ram_hi; lia).
    assert (Huint : uint (SailStdpp.Values.mword_of_int a : Arch.pa) = a)
      by exact (boot_uint_pa a Hram).
    iApply (big_sepM_lookup _ _ (SailStdpp.Values.mword_of_int a : Arch.pa) b with "Ht").
    rewrite /sub_text. apply map_lookup_filter_Some_2.
    - rewrite <- (boot_byte_text a b Hlk). exact (Hmem a Hram).
    - cbn. rewrite Huint. unfold text_end. lia.
  Qed.

  (* ================================================================== *)
  (* §6  ADDRESS RANGES -- the vocabulary every remaining cut is spelled *)
  (*     in, and the ONE induction that turns a range into a run.        *)
  (* ================================================================== *)

  (* Everything still to be carved out of the [text_end]-and-above half is a
     RANGE of physical addresses: [text_end, img_end) for the initialized
     globals ([kernel_data]), a hart's 4096-byte [stack0] slice
     ([stack_own_phys]), the .bss cells the typed globals sit in, and
     [s1entry, PHYSTOP) for kinit's page run.  So ONE cut lemma and ONE
     range-to-run lemma serve all of them, and BOTH are symbolic: no proof
     here ever enumerates [g.(gmem)], and the run induction is over the
     range's LENGTH, so its cost is paid once, here. *)
  Definition ran_bytes (g : gstate) (lo hi : Z) :=
    base.filter (fun p : Arch.pa * bv 8 => (lo <= uint p.1 < hi)%Z) g.(gmem).
  Definition boot_raw_ran (g : gstate) (lo hi : Z) : iProp Σ :=
    ([∗ map] a ↦ b ∈ ran_bytes g lo hi,
       pointsto (L:=Arch.pa) (V:=bv 8) a (DfracOwn 1) b)%I.

  Local Lemma ran_bytes_union (g : gstate) (lo mid hi : Z) :
    lo <= mid -> mid <= hi ->
    ran_bytes g lo hi = ran_bytes g lo mid ∪ ran_bytes g mid hi.
  Proof.
    intros H1 H2.
    pose proof (map_filter_union_complement
                  (fun p : Arch.pa * bv 8 => (uint p.1 < mid)%Z)
                  (ran_bytes g lo hi)) as Heq.
    etransitivity; [ symmetry; exact Heq |].
    rewrite /ran_bytes !map_filter_filter. f_equal.
    - apply (proj1 (map_filter_ext _ _ g.(gmem))). intros i x _. cbn. split; lia.
    - apply (proj1 (map_filter_ext _ _ g.(gmem))). intros i x _. cbn. split; lia.
  Qed.

  Local Lemma ran_bytes_disj (g : gstate) (lo mid hi : Z) :
    ran_bytes g lo mid ##ₘ ran_bytes g mid hi.
  Proof.
    apply map_disjoint_spec. intros i x y Hx Hy. rewrite /ran_bytes in Hx Hy.
    apply map_lookup_filter_Some in Hx. apply map_lookup_filter_Some in Hy.
    destruct Hx as [_ Hx]. destruct Hy as [_ Hy]. cbn in Hx, Hy. lia.
  Qed.

  (* THE CUT.  Every remaining slice is a chain of these. *)
  Lemma boot_ran_split (g : gstate) (lo mid hi : Z) :
    lo <= mid -> mid <= hi ->
    boot_raw_ran g lo hi ⊢ boot_raw_ran g lo mid ∗ boot_raw_ran g mid hi.
  Proof.
    intros H1 H2. rewrite /boot_raw_ran (ran_bytes_union g lo mid hi H1 H2).
    iIntros "H".
    iDestruct (big_sepM_union with "H") as "[H1 H2]"; [apply ran_bytes_disj |].
    iFrame "H1 H2".
  Qed.

  (* the bridge from §2's [text_end]-and-above half into the range
     vocabulary: with "nothing outside RAM" the half IS the range
     [text_end, ram_hi). *)
  Local Lemma supra_text_ran (g : gstate) :
    (forall a b, g.(gmem) !! a = Some b -> addr_is_ram a) ->
    supra_text g = ran_bytes g text_end ram_hi.
  Proof.
    intro Hram. rewrite /supra_text /ran_bytes.
    apply (proj1 (map_filter_ext _ _ g.(gmem))). intros i x Hlk. cbn.
    pose proof (Hram i x Hlk) as Hr.
    unfold addr_is_ram, ram_base, ram_size in Hr. unfold ram_hi.
    split; lia.
  Qed.

  Lemma boot_data_ran (g : gstate) :
    (forall a b, g.(gmem) !! a = Some b -> addr_is_ram a) ->
    boot_data_raw g ⊢ boot_raw_ran g text_end ram_hi.
  Proof.
    intro Hram. rewrite /boot_data_raw /boot_raw_ran (supra_text_ran g Hram).
    iIntros "$".
  Qed.

  (* A ONE-BYTE range is a SINGLETON map, and that is the fact that pins a
     range's domain: a key whose [uint] is [a] can only be [pa_of_z a]
     ([PowerBoot.pa_of_z_uint]).  Without it a filter by address says nothing
     about WHICH keys survive. *)
  Local Lemma ran_bytes_one (g : gstate) (a : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    ram_lo <= a < ram_hi ->
    ran_bytes g a (a + 1) = {[ pa_of_z a := boot_byte a ]}.
  Proof.
    intros Hmem Ha. apply map_eq. intros k. rewrite /ran_bytes.
    destruct (decide (k = pa_of_z a)) as [-> | Hne].
    - rewrite lookup_singleton.
      apply map_lookup_filter_Some_2;
        [ exact (Hmem a Ha) | cbn; rewrite (boot_uint_pa a Ha); lia ].
    - assert (Hne' : pa_of_z a <> k) by (intro Hq; apply Hne; symmetry; exact Hq).
      rewrite (lookup_singleton_ne _ _ _ Hne').
      apply map_lookup_filter_None. right. intros x _ Hg. cbn in Hg.
      apply Hne. rewrite <- (pa_of_z_uint k). f_equal. lia.
  Qed.

  (* THE RUN.  A range of the loaded image, as the list of its bytes -- the
     one induction in this file, over the range's LENGTH, so no consumer ever
     pays for it again. *)
  Lemma boot_ran_bytes (g : gstate) (lo : Z) (n : nat) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    ram_lo <= lo -> lo + Z.of_nat n <= ram_hi ->
    boot_raw_ran g lo (lo + Z.of_nat n)
    ⊢ [∗ list] a ∈ zrun lo n,
        pointsto (L:=Arch.pa) (V:=bv 8) (pa_of_z a) (DfracOwn 1) (boot_byte a).
  Proof.
    intro Hmem. revert lo. induction n as [|k IH]; intros lo Hlo Hhi.
    - iIntros "_". done.
    - assert (Hsplit : lo + Z.of_nat (S k) = lo + 1 + Z.of_nat k) by lia.
      assert (H1 : lo <= lo + 1) by lia.
      assert (H2 : lo + 1 <= lo + 1 + Z.of_nat k) by lia.
      assert (Hlo1 : ram_lo <= lo + 1) by lia.
      assert (Hhi1 : lo + 1 + Z.of_nat k <= ram_hi) by lia.
      assert (Hain : ram_lo <= lo < ram_hi) by lia.
      rewrite Hsplit.
      iIntros "H".
      iDestruct (boot_ran_split g lo (lo + 1) (lo + 1 + Z.of_nat k) H1 H2
                   with "H") as "[H1 H2]".
      change (zrun lo (S k)) with (lo :: zrun (lo + 1) k).
      iSplitL "H1".
      + rewrite /boot_raw_ran (ran_bytes_one g lo Hmem Hain) big_sepM_singleton.
        iExact "H1".
      + iApply (IH (lo + 1) Hlo1 Hhi1 with "H2").
  Qed.

  (* ================================================================== *)
  (* §7  The NAMED data bundle [kernel_data], and the [entry_ld_ea] word. *)
  (* ================================================================== *)

  (* the [↦ₘ] upgrade of a range, at or above [text_end] -- §4's per-byte
     step, over the range vocabulary. *)
  Lemma boot_ran_own (g : gstate) (lo hi : Z) :
    (forall a b, g.(gmem) !! a = Some b -> addr_is_ram a) ->
    text_end <= lo ->
    kmap_static_claims -∗ boot_raw_ran g lo hi
    -∗ ([∗ map] a ↦ b ∈ ran_bytes g lo hi, a ↦ₘ b).
  Proof.
    iIntros (Hram Hlo) "#Hkbundle Hd". rewrite /boot_raw_ran.
    iApply (big_sepM_impl with "Hd").
    iIntros "!>" (a b Ha) "Hb".
    rewrite /ran_bytes in Ha.
    apply map_lookup_filter_Some in Ha. destruct Ha as [Ha Hge]. cbn in Hge.
    pose proof (Hram a b Ha) as Hr.
    assert (Hkd : addr_is_kdata a)
      by (unfold addr_is_kdata; unfold addr_is_ram in Hr; lia).
    assert (Hcanon : uint a < 274877906944)
      by (unfold addr_is_kdata, ram_base, ram_size, text_end in Hkd; lia).
    iApply (phys_ident_mem a (DfracOwn 1) b (kdata_svpn_class a Hkd)
              (addr_is_kdata_ram a Hkd) Hcanon with "Hkbundle [Hb]").
    rewrite /phys_pointsto. iFrame "Hb". iPureIntro. exact (addr_is_kdata_ram a Hkd).
  Qed.

  Lemma boot_ran_persist (g : gstate) (lo hi : Z) :
    ([∗ map] a ↦ b ∈ ran_bytes g lo hi, a ↦ₘ b)
    ==∗ ([∗ map] a ↦ b ∈ ran_bytes g lo hi, a ↦ₘ□ b).
  Proof.
    iIntros "Hd". iApply big_sepM_bupd. iApply (big_sepM_mono with "Hd").
    iIntros (a b _) "H". by iApply mem_pointsto_persist.
  Qed.

  (* the loader really did leave [KernelData]'s byte at its address.  Above
     [text_end] the text map is exhausted ([kernel_bytes]' keys stop at
     0x80006120), so the union takes the DATA side; and [kernel_data]'s upper
     bound is exactly [img_end], which is what puts the byte inside
     [boot_image]'s filter. *)
  Local Lemma boot_byte_data (a : Z) (b : bv 8) :
    text_end <= a -> KernelData.kernel_data !! a = Some b -> boot_byte a = b.
  Proof.
    intros Hlo Hlk.
    pose proof (KernelData.kernel_data_range a b Hlk) as Hr.
    unfold KernelData.kernel_data_lo, KernelData.kernel_data_hi in Hr.
    assert (Hnone : KernelInstrs.kernel_bytes !! a = None).
    { destruct (KernelInstrs.kernel_bytes !! a) as [b'|] eqn:E; [| reflexivity].
      pose proof (KernelInstrs.kernel_bytes_range a b' E) as Hrt.
      unfold KernelInstrs.kernel_bytes_lo, KernelInstrs.kernel_bytes_hi in Hrt.
      unfold text_end in Hlo. lia. }
    unfold boot_byte, boot_image.
    rewrite (map_lookup_filter_Some_2 _ _ a b);
      [ reflexivity
      | apply lookup_union_Some_raw; right; split; [exact Hnone | exact Hlk]
      | cbn; unfold img_end; lia ].
  Qed.

  (* [KernelDataInv.kernel_data] is the PERSISTED ([↦ₘ□]) initialized-globals
     image, filtered at [text_end] (its sub-etext bytes belong to the [↦ₓ□]
     half).  Its keys stop at [img_end], which is why the SECOND cut of the
     data half goes there: below [img_end] the bytes persist into this
     bundle, at or above it they stay OWNED for the typed .bss cells and the
     page run.  Nothing is left over that anything wants -- the range's
     non-[KernelData] bytes are padding. *)
  Lemma kernel_data_intro (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    ([∗ map] a ↦ b ∈ ran_bytes g text_end img_end, a ↦ₘ□ b) -∗ kernel_data.
  Proof.
    iIntros (Hmem) "#Hd". rewrite /kernel_data.
    iApply big_sepM_intro. iIntros "!>" (a b Hlk).
    apply map_lookup_filter_Some in Hlk. destruct Hlk as [Hlk Hge]. cbn in Hge.
    pose proof (KernelData.kernel_data_range a b Hlk) as Hr.
    unfold KernelData.kernel_data_lo, KernelData.kernel_data_hi in Hr.
    assert (Hram : ram_lo <= a < ram_hi)
      by (unfold ram_lo, ram_hi, text_end in *; lia).
    iApply (big_sepM_lookup _ _ (pa_of_z a) b with "Hd").
    rewrite /ran_bytes. apply map_lookup_filter_Some_2.
    - rewrite <- (boot_byte_data a b Hge Hlk). exact (Hmem a Hram).
    - cbn. rewrite (boot_uint_pa a Hram). unfold img_end. lia.
  Qed.

  (* ================================================================== *)
  (* §8  Words: a range's 8 bytes as a doubleword.                        *)
  (* ================================================================== *)

  Local Lemma aligned8_of_mod (a : mword 64) :
    uint a mod 8 = 0 -> is_aligned_paddr (Physaddr a) 8 = true.
  Proof.
    intro Hm. unfold is_aligned_paddr. apply Z.eqb_eq.
    pose proof (bv_unsigned_in_range _ a) as [Hnn _].
    rewrite uint_unsigned in Hm |- *.
    rewrite Z.rem_mod_nonneg; [exact Hm | exact Hnn | lia].
  Qed.

  (* An 8-byte, 8-ALIGNED range of the image is a doubleword of ARBITRARY
     contents at the physical tier -- which is all a stack slot (or any
     scratch word) ever needs.  The value is the little-endian assembly of
     the loader's bytes, so it is existential rather than pinned. *)
  Lemma boot_ran_word (g : gstate) (base : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    ram_lo <= base -> base + 8 <= ram_hi -> base mod 8 = 0 ->
    boot_raw_ran g base (base + 8)
    ⊢ ∃ w : bv 64, phys_word_pointsto (pa_of_z base) (DfracOwn 1) w.
  Proof.
    intros Hmem Hlo Hhi Hal.
    assert (E8 : base + 8 = base + Z.of_nat 8%nat) by (cbn; lia).
    assert (Hhi8 : base + Z.of_nat 8%nat <= ram_hi) by (cbn; lia).
    assert (Halb : uint (pa_of_z base) mod 8 = 0)
      by (rewrite (boot_uint_pa base ltac:(lia)); exact Hal).
    rewrite E8. iIntros "H".
    iDestruct (boot_ran_bytes g base 8%nat Hmem Hlo Hhi8 with "H") as "H".
    rewrite zrun_fmap big_sepL_fmap.
    iExists (Z_to_bv 64 (assemble_bytes
               [boot_byte (base + Z.of_nat 0%nat); boot_byte (base + Z.of_nat 1%nat);
                boot_byte (base + Z.of_nat 2%nat); boot_byte (base + Z.of_nat 3%nat);
                boot_byte (base + Z.of_nat 4%nat); boot_byte (base + Z.of_nat 5%nat);
                boot_byte (base + Z.of_nat 6%nat); boot_byte (base + Z.of_nat 7%nat)])
              : mword 64).
    iApply (phys_word_pointsto_intro _ _ _ (aligned8_of_mod _ Halb)).
    iApply (big_sepL_impl with "H"). iIntros "!>" (kk i Hk) "Hb".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    assert (Hin : ram_lo <= base + Z.of_nat (0 + kk)%nat < ram_hi).
    { change (0 + kk)%nat with kk. cbn in Hhi8. lia. }
    rewrite pa_add_mword.
    assert (Hnb : nth_byte (Z_to_bv 64 (assemble_bytes
                    [boot_byte (base + Z.of_nat 0%nat); boot_byte (base + Z.of_nat 1%nat);
                     boot_byte (base + Z.of_nat 2%nat); boot_byte (base + Z.of_nat 3%nat);
                     boot_byte (base + Z.of_nat 4%nat); boot_byte (base + Z.of_nat 5%nat);
                     boot_byte (base + Z.of_nat 6%nat); boot_byte (base + Z.of_nat 7%nat)])
                    : mword 64) (0 + kk)%nat
                  = boot_byte (base + Z.of_nat (0 + kk)%nat)).
    { rewrite (nth_byte_assemble_len 64 _ (0 + kk)%nat); [| cbn; lia | cbn; lia].
      destruct kk as [|[|[|[|[|[|[|[|kk']]]]]]]]; [.. | cbn in Hlt; lia];
        reflexivity. }
    rewrite Hnb /phys_pointsto. iFrame "Hb". iPureIntro.
    unfold addr_is_ram, ram_base, ram_size.
    rewrite (boot_uint_pa _ Hin). unfold ram_lo, ram_hi in Hin. lia.
  Qed.

  (* the PHYSICAL-tier doubleword of the INITIALIZED image, at a pinned value:
     what M-mode boot code reads (it has no translation).  [kernel_data]'s
     [↦ₘ□] bytes sit at STATIC (identity) kernel-data addresses, so
     [KMap.mem_ident_phys] disassembles each one.  This is the shape the
     [entry_ld_ea] word ([_entry]'s GOT slot, holding &stack0) comes out at;
     the instantiation lives with the client, which is the only place that
     knows [entry_ld_ea]'s literal value (this file stays below the M-mode
     tower on purpose). *)
  Lemma kernel_data_phys_word (A : Z) (w : bv 64) (a : mword 64) :
    a = pa_of_z A -> text_end <= A -> A + 8 <= img_end ->
    A mod 8 = 0 ->
    (forall j, (j < 8)%nat ->
       KernelData.kernel_data !! (A + Z.of_nat j) = Some (nth_byte w j)) ->
    kmap_static_claims -∗ kernel_data -∗ a ↦ₚ₈□ w.
  Proof.
    iIntros (-> HA Hhi Hal Hbytes) "#Hkbundle #Hd".
    unfold text_end in HA. unfold img_end in Hhi.
    assert (Hram : ram_lo <= A < ram_hi) by (unfold ram_lo, ram_hi; lia).
    assert (Halb : uint (pa_of_z A) mod 8 = 0)
      by (rewrite (boot_uint_pa A Hram); exact Hal).
    iApply (phys_word_pointsto_intro _ _ _ (aligned8_of_mod _ Halb)).
    iDestruct (kernel_data_window (wd := 64) A w 8%nat (pa_of_z A) eq_refl HA Hbytes
                 with "Hd") as "Hbs".
    iApply (big_sepL_impl with "Hbs"). iIntros "!>" (kk j Hk) "Hb".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    change (0 + kk)%nat with kk.
    assert (Hin : ram_lo <= A + Z.of_nat kk < ram_hi).
    { unfold ram_lo, ram_hi. lia. }
    assert (Hkd : addr_is_kdata (pa_add (pa_of_z A) kk)).
    { rewrite pa_add_mword. unfold addr_is_kdata, ram_base, ram_size, text_end.
      rewrite (boot_uint_pa _ Hin). lia. }
    iApply (mem_ident_phys _ DfracDiscarded _ (kdata_svpn_class _ Hkd)
              with "Hkbundle Hb").
  Qed.

  (* ================================================================== *)
  (* §9  The PHYSICAL stack carve.                                       *)
  (*                                                                    *)
  (* [SpecEntry.wp_entry_boot] wants [stack_own_phys sp0 n] -- the [n]    *)
  (* doublewords BELOW the sp [_entry] computed, at the PHYSICAL tier     *)
  (* (M-mode does not translate).  That is exactly the address range      *)
  (* [uint sp0 - 8n, uint sp0), so the boot client simply cuts it out of  *)
  (* the image: nothing here mentions [stack0], and a per-hart carve is   *)
  (* the same lemma at that hart's sp.  (The VA-tier [stack_own] the      *)
  (* S-mode capability wants is BootBridge's                             *)
  (* [stack_own_phys_to_stack] on top of this.)                          *)
  (* ================================================================== *)

  Lemma boot_stack_own_phys (g : gstate) (sp : mword 64) (n : nat) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    ram_lo + 8 * Z.of_nat n <= uint sp -> uint sp <= ram_hi ->
    uint sp mod 8 = 0 ->
    boot_raw_ran g (uint sp - 8 * Z.of_nat n) (uint sp) ⊢ stack_own_phys sp n.
  Proof.
    intro Hmem. induction n as [|k IH]; intros Hlo Hhi Hal.
    - iIntros "_". rewrite /stack_own_phys. iExists []. by iSplitR.
    - assert (HSk : (S k = k + 1)%nat) by lia.
      assert (Hd1 : uint sp - 8 * Z.of_nat (S k)
                    <= uint sp - 8 * Z.of_nat (S k) + 8) by lia.
      assert (Hd2 : uint sp - 8 * Z.of_nat (S k) + 8 <= uint sp) by lia.
      assert (Hmid : uint sp - 8 * Z.of_nat (S k) + 8
                     = uint sp - 8 * Z.of_nat k) by lia.
      assert (Hwlo : ram_lo <= uint sp - 8 * Z.of_nat (S k)) by lia.
      assert (Hwhi : uint sp - 8 * Z.of_nat (S k) + 8 <= ram_hi) by lia.
      assert (Hklo : ram_lo + 8 * Z.of_nat k <= uint sp) by lia.
      assert (Hstk8 : 8 * Z.of_nat (S k) <= uint sp) by (unfold ram_lo in Hlo; lia).
      assert (Hstk : pa_of_z (uint sp - 8 * Z.of_nat (S k)) = pa_stk sp (S k)).
      { rewrite <- (uint_pa_stk sp (S k) Hstk8). apply pa_of_z_uint. }
      iIntros "H".
      iDestruct (boot_ran_split g _ (uint sp - 8 * Z.of_nat (S k) + 8) (uint sp)
                   Hd1 Hd2 with "H") as "[Hw Hrest]".
      iDestruct (boot_ran_word g (uint sp - 8 * Z.of_nat (S k)) Hmem Hwlo Hwhi
                   (z_mod8_sub _ _ Hal) with "Hw") as (w) "Hw".
      iEval (rewrite Hmid) in "Hrest".
      rewrite HSk (stack_own_phys_app sp k 1).
      iSplitL "Hrest"; [iApply (IH Hklo Hhi Hal with "Hrest") |].
      iApply (stack_own_phys_1_intro (pa_stk sp k) w).
      rewrite (pa_stk_assoc sp k 1) -HSk -Hstk. iExact "Hw".
  Qed.

End BootCarve.
