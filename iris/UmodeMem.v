(* UmodeMem.v -- the CONCRETE memory layer of VERIFIED user-mode execution
   (the Umode tier -- see claude-notes/projects/user-verified.md).

   The safety tier (User*.v) owns a process's pages with EXISTENTIAL contents
   ([udata_own], UserPtTree.v): safety never depends on what the bytes are.
   Verified execution of a SPECIFIC program is about the bytes, so this file
   gives the concrete twin:

     [uva_pa pt va]     the physical address user virtual address [va]
                        translates to through the (fixed) user table [pt] --
                        a TOTAL function (garbage off the mapped vpns; specs
                        only ever put mapped vas in an image).
     [umem pt M]        ownership of the process image [M] -- a gmap keyed by
                        USER VIRTUAL address (same keying as the dumped
                        [sync_bytes]) -- realized as the same [↦ₚ] bytes the
                        safety tier's [UserPtTree.umem_own] holds.  The two
                        are now the SAME definition up to the domain
                        constraint the safety tier carries.
     [uinstr pt M pc is_rvc i]
                        the PURE per-instruction fact: the instruction [i]'s
                        bytes sit in [M] at [pc], [pc]'s vpn is mapped
                        fetch-executable in [pt], and the word decodes to [i]
                        on any U-mode machine (transportable decode facts,
                        stated against the U-mode reference state [dstateU]).
                        Per-program [UCode<Prog>.v] files prove these from
                        the dumped image.

   File-naming rule: the verified tier uses the [Umode] prefix -- distinct
   from the kernel's [Smode]/[Mmode] leaf files AND from the safety tier's
   [User*] files. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import CommonWalk.
Require Import UserPtTree.
Require Import WpDecodeBridge DecodeTotalU.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The va -> pa view of a fixed user table.                             *)
(* ===================================================================== *)

(* [uva_pa pt va] -- the pa [va] translates to through [pt]'s abstract map
   -- now lives in UserPtTree.v, where the SAFETY tier's own byte map
   ([umem_own]) is keyed by it; this file only reads it. *)

Lemma uva_pa_mapped (pt : uptd) (va : Z) (w : mword 64) :
  ud_um pt !! svpn_of (mword_of_int va) = Some w ->
  uva_pa pt va = u_walk_pa w (mword_of_int va).
Proof. intro Hl. unfold uva_pa. rewrite Hl. reflexivity. Qed.

(* ===================================================================== *)
(* §2 The owned image.                                                     *)
(* ===================================================================== *)

Section UmodeMem.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the process image, keyed by user va.  One flat byte map: code, data,
     bss and stack are all just entries (the dumped [sync_bytes]/[sync_data]
     unioned with the zero bss and the stack page's bytes). *)
  Definition umem (pt : uptd) (M : gmap Z (bv 8)) : iProp Σ :=
    ([∗ map] va ↦ b ∈ M, (uva_pa pt va : Arch.pa) ↦ₚ b)%I.

  (* read access to one byte *)
  Lemma umem_lookup_acc (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
    M !! va = Some b ->
    umem pt M -∗
    ((uva_pa pt va : Arch.pa) ↦ₚ b ∗
     ((uva_pa pt va : Arch.pa) ↦ₚ b -∗ umem pt M)).
  Proof.
    iIntros (Hl) "HM".
    iApply (big_sepM_lookup_acc with "HM"). exact Hl.
  Qed.

  (* write access to one byte: hand the cell back at a NEW value and the
     image is [M] with that byte updated *)
  Lemma umem_insert_acc (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
    M !! va = Some b ->
    umem pt M -∗
    ((uva_pa pt va : Arch.pa) ↦ₚ b ∗
     (∀ b' : bv 8, (uva_pa pt va : Arch.pa) ↦ₚ b' -∗ umem pt (<[va := b']> M))).
  Proof.
    iIntros (Hl) "HM".
    iDestruct (big_sepM_insert_acc with "HM") as "[Hb Hrest]"; [exact Hl |].
    iFrame "Hb". iIntros (b') "Hb". iApply ("Hrest" with "Hb").
  Qed.

End UmodeMem.

(* ===================================================================== *)
(* §3 Pure byte-window and decode vocabulary.                              *)
(* ===================================================================== *)

(* [k] consecutive image bytes spelling out the little-endian word [w] *)
Definition uM_bytes {n : N} (M : gmap Z (bv 8)) (a : Z) (k : nat) (w : bv n) : Prop :=
  forall j : nat, (j < k)%nat -> M !! (a + Z.of_nat j) = Some (nth_byte w j).

(* Sv39 canonicality of a user va (bits 63..38 = sign extension of bit 38;
   spelled exactly as the translate lemmas' premise) *)
Definition uva_canon (va : mword 64) : Prop :=
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.

(* the pc's page is mapped with a leaf every fetch-access variant passes *)
Definition uva_fetch_leaf (pt : uptd) (pc : mword 64) : Prop :=
  exists w : mword 64,
    ud_um pt !! svpn_of pc = Some w /\
    uleaf_ok (InstructionFetch tt) w.

(* transportable decode facts: proved once against the U-mode reference
   state ([dstateU] / the misa.C gate), transported to the fetched machine
   state by the caller's agreement facts. *)
Definition udecode_base (w : mword 32) (i : instruction) : Prop :=
  forall s : mstate, agree_on D_u s dstateU ->
    exec (ext_decode w) s = Some (i, s).

Definition udecode_rvc (h : mword 16) (i : instruction) : Prop :=
  forall s : mstate,
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h) s = Some (i, s).

(* ===================================================================== *)
(* §4 [uinstr] -- the per-instruction fact a verified leaf takes.          *)
(*                                                                         *)
(* The fetch geometry (RiscvFetchExec.v): a 4-ALIGNED pc is fetched with   *)
(* ONE 4-byte read even when the instruction is compressed (the read grabs *)
(* the next instruction's 2 bytes too), so the RVC-at-4-aligned case needs *)
(* the following two bytes present in [M] as well.  A 2-mod-4 pc reads 2   *)
(* bytes, then (base case) 2 more at pc+2.  [ui_inpage] keeps the whole    *)
(* 4-byte window on one page, so one leaf fact serves every byte.          *)
(* ===================================================================== *)

Record uinstr (pt : uptd) (M : gmap Z (bv 8)) (pc : mword 64)
    (is_rvc : bool) (i : instruction) : Prop := UInstr {
  ui_al2    : is_aligned_vaddr (Virtaddr pc) 2 = true;
  ui_canon  : uva_canon pc;
  ui_leaf   : uva_fetch_leaf pt pc;
  ui_inpage : Z.rem (uint pc) 4096 <= 4092;
  ui_code   :
    if is_rvc
    then exists h : mword 16,
        isRVC h = true /\
        uM_bytes M (uint pc) 2 h /\
        udecode_rvc h i /\
        (is_aligned_vaddr (Virtaddr pc) 4 = true ->
         exists b2 b3 : bv 8,
           M !! (uint pc + 2) = Some b2 /\ M !! (uint pc + 3) = Some b3)
    else exists w : mword 32,
        isRVC (subrange_vec_dec w 15 0) = false /\
        uM_bytes M (uint pc) 4 w /\
        udecode_base w i
}.

(* ===================================================================== *)
(* §5 THE BRIDGE TO THE PER-NODE ENGINE'S PHYSICAL BYTE MAP.               *)
(*                                                                         *)
(* [umem pt M] is keyed by user VA and pushed through [uva_pa pt]; the     *)
(* per-node engine ([HartMemRun]) works with [bytes_own : PtBytes.pamap -> *)
(* iProp], keyed by PHYSICAL address.  [upa_map pt M] is [M] re-keyed, and *)
(* the two resources are the same separating conjunction -- PROVIDED the   *)
(* re-keying loses nothing, i.e. [uva_pa pt] is injective on [dom M].      *)
(*                                                                         *)
(* THAT INJECTIVITY IS NOT ASSUMED: [umem_inj] DERIVES it from the         *)
(* ownership itself ([↦ₚ] is exclusive, so two image bytes cannot sit at   *)
(* one physical address), exactly as [PtBytes.bytes_own_list_disj] derives *)
(* map disjointness rather than taking it as a hypothesis.  So the forward *)
(* direction [umem_to_bytes] needs NO premise; only the backward one       *)
(* (which has no [umem] to interrogate) carries [uva_inj].                 *)
(*                                                                         *)
(* IMPORT-SET NOTE (user-tier-port.md §8.1): this file imports             *)
(* [SailStdpp.Base]/[Values], so a [gmap Arch.pa (bv 8)] elaborated HERE   *)
(* takes [Countable_mword], NOT the [bv_countable] that [bytes_own] /      *)
(* [bytes_owned] are stated at -- the two print identically and do not     *)
(* unify.  Hence [upa_map]'s result type is spelled [PtBytes.pamap] and    *)
(* the [gset Arch.pa] of a [dom] is never ascribed: it is inferred from    *)
(* the map, which pins the right instance.                                 *)
(* ===================================================================== *)

Require Import HartMemRun PtBytes.

(* [uva_pa pt] is injective on the image's keys -- the exact content of
   "the re-keying loses nothing" *)
Definition uva_inj (pt : uptd) (M : gmap Z (bv 8)) : Prop :=
  forall va1 va2 : Z,
    va1 ∈ dom M -> va2 ∈ dom M ->
    uva_pa pt va1 = uva_pa pt va2 -> va1 = va2.

(* the image's association list, re-keyed by [uva_pa pt] *)
Definition upa_list (pt : uptd) (M : gmap Z (bv 8)) : list (Arch.pa * bv 8) :=
  (fun p : Z * bv 8 => ((uva_pa pt p.1 : Arch.pa), p.2)) <$> map_to_list M.

(* THE RE-KEYED IMAGE.  Result type spelled [PtBytes.pamap] -- see the
   import-set note above. *)
Definition upa_map (pt : uptd) (M : gmap Z (bv 8)) : PtBytes.pamap :=
  list_to_map (upa_list pt M).

Lemma upa_list_keys (pt : uptd) (M : gmap Z (bv 8)) :
  (upa_list pt M).*1
  = (fun va : Z => (uva_pa pt va : Arch.pa)) <$> (map_to_list M).*1.
Proof.
  rewrite /upa_list. induction (map_to_list M) as [| p l IH]; [reflexivity |].
  csimpl. by rewrite IH.
Qed.

Lemma upa_keys_dom (M : gmap Z (bv 8)) (x : Z) :
  x ∈ (map_to_list M).*1 <-> x ∈ dom M.
Proof.
  split.
  - intros Hx. apply elem_of_list_fmap in Hx as [[k v] [Heq Hkv]].
    cbn in Heq. subst x. apply elem_of_map_to_list in Hkv.
    by eapply elem_of_dom_2.
  - intros Hx. apply elem_of_dom in Hx as [v Hv].
    apply elem_of_list_fmap. exists (x, v). split; [reflexivity |].
    by apply elem_of_map_to_list.
Qed.

(* the injectivity is exactly what makes the re-keyed association list a
   FUNCTION -- everything below goes through this *)
Lemma upa_list_nodup (pt : uptd) (M : gmap Z (bv 8)) :
  uva_inj pt M -> base.NoDup ((upa_list pt M).*1).
Proof.
  intros Hinj. rewrite upa_list_keys.
  apply NoDup_fmap_2_strong; [| apply NoDup_fst_map_to_list].
  intros x y Hx Hy Heq.
  apply Hinj; [ by apply upa_keys_dom | by apply upa_keys_dom | exact Heq ].
Qed.

Lemma upa_map_lookup (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
  uva_inj pt M -> M !! va = Some b -> upa_map pt M !! uva_pa pt va = Some b.
Proof.
  intros Hinj Hva. rewrite /upa_map.
  apply elem_of_list_to_map_1; [ by apply upa_list_nodup |].
  rewrite /upa_list. apply elem_of_list_fmap.
  exists (va, b). split; [reflexivity |]. by apply elem_of_map_to_list.
Qed.

Lemma upa_map_lookup_inv (pt : uptd) (M : gmap Z (bv 8)) (a : Arch.pa) (b : bv 8) :
  upa_map pt M !! a = Some b ->
  exists va : Z, uva_pa pt va = a /\ M !! va = Some b.
Proof.
  intros Ha. rewrite /upa_map in Ha. apply elem_of_list_to_map_2 in Ha.
  rewrite /upa_list in Ha. apply elem_of_list_fmap in Ha as [[va b'] [Heq Hin]].
  cbn in Heq. injection Heq as -> ->.
  exists va. split; [reflexivity |]. by apply elem_of_map_to_list.
Qed.

(* the DOMAIN of the re-keyed image, in the two forms the engine asks for:
   as a set literal, and as the membership characterisation. *)
Lemma upa_map_dom (pt : uptd) (M : gmap Z (bv 8)) :
  dom (upa_map pt M)
  = list_to_set ((fun va : Z => (uva_pa pt va : Arch.pa)) <$> (map_to_list M).*1).
Proof. rewrite /upa_map dom_list_to_map_L upa_list_keys. reflexivity. Qed.

Lemma upa_map_dom_elem (pt : uptd) (M : gmap Z (bv 8)) (a : Arch.pa) :
  a ∈ dom (upa_map pt M) <-> exists va : Z, va ∈ dom M /\ uva_pa pt va = a.
Proof.
  rewrite upa_map_dom elem_of_list_to_set elem_of_list_fmap. split.
  - intros [va [Heq Hva]]. exists va.
    split; [ by apply upa_keys_dom | by symmetry ].
  - intros [va [Hva Heq]]. exists va.
    split; [ by symmetry | by apply upa_keys_dom ].
Qed.

(* WHAT THE ENGINE ACTUALLY TAKES: [uinstr]'s "these bytes are in [M]"
   turned into [HartMemRun.bytes_owned] over the re-keyed map.
   The window premise is [UmodeFetch.uva_pa_window]'s CONCLUSION verbatim
   -- that lemma cannot be used here (UmodeFetch.v imports THIS file), so
   the caller supplies it, one application per byte. *)
Lemma upa_map_owned (pt : uptd) (M : gmap Z (bv 8)) (w va : mword 64) (k : nat) :
  uva_inj pt M ->
  (forall j : nat, (j < k)%nat ->
     uva_pa pt (uint va + Z.of_nat j) = pa_add (u_walk_pa w va) j) ->
  (forall j : nat, (j < k)%nat -> is_Some (M !! (uint va + Z.of_nat j))) ->
  bytes_owned (upa_map pt M) (u_walk_pa w va) (N.of_nat k) = true.
Proof.
  intros Hinj Hwin Hin. apply bytes_owned_of_dom. intros j Hj.
  rewrite Nat2N.id in Hj.
  rewrite <- (Hwin j Hj). apply elem_of_dom.
  destruct (Hin j Hj) as [b Hb]. exists b.
  exact (upa_map_lookup pt M _ b Hinj Hb).
Qed.

Section UmodeMemBridge.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE INJECTIVITY, OUT OF THE OWNERSHIP.  Two distinct image keys own
     two [↦ₚ] cells; [PtBytes.phys_pointsto_ne] (the exclusivity of the
     physical points-to) says their addresses differ.  Nothing is assumed. *)
  Lemma umem_inj (pt : uptd) (M : gmap Z (bv 8)) :
    umem pt M ⊢ ⌜forall va1 va2 : Z,
        va1 ∈ dom M -> va2 ∈ dom M ->
        uva_pa pt va1 = uva_pa pt va2 -> va1 = va2⌝.
  Proof.
    rewrite /umem. iIntros "HM".
    rewrite bi.pure_forall. iIntros (va1).
    rewrite bi.pure_forall. iIntros (va2).
    rewrite !bi.pure_impl. iIntros (H1 H2 Heq).
    destruct (decide (va1 = va2)) as [-> | Hne]; [by iPureIntro |].
    apply elem_of_dom in H1 as [b1 Hb1]. apply elem_of_dom in H2 as [b2 Hb2].
    iDestruct (big_sepM_delete _ _ _ _ Hb1 with "HM") as "[Hb1 HM]".
    assert (Hb2' : delete va1 M !! va2 = Some b2).
    { rewrite (lookup_delete_ne M va1 va2 Hne). exact Hb2. }
    iDestruct (big_sepM_lookup _ _ _ _ Hb2' with "HM") as "Hb2".
    iDestruct (phys_pointsto_ne with "Hb1 Hb2") as %Hpne.
    iPureIntro. exfalso. exact (Hpne Heq).
  Qed.

  (* the same fact, folded *)
  Lemma umem_uva_inj (pt : uptd) (M : gmap Z (bv 8)) :
    umem pt M ⊢ ⌜uva_inj pt M⌝.
  Proof. apply umem_inj. Qed.

  (* THE VIEW LEMMA: with the re-keying injective, the two big-ops are the
     same list of cells. *)
  Lemma umem_bytes_own (pt : uptd) (M : gmap Z (bv 8)) :
    uva_inj pt M -> umem pt M ⊣⊢ bytes_own (upa_map pt M).
  Proof.
    intros Hinj. rewrite /umem /bytes_own /upa_map.
    rewrite big_sepM_list_to_map; [| by apply upa_list_nodup].
    rewrite /upa_list big_sepL_fmap big_sepM_map_to_list. reflexivity.
  Qed.

  (* what the engine needs: NO premise -- the injectivity comes out of the
     resource being handed over *)
  Lemma umem_to_bytes (pt : uptd) (M : gmap Z (bv 8)) :
    umem pt M ⊢ bytes_own (upa_map pt M).
  Proof.
    apply (bi.pure_elim (uva_inj pt M)); [ apply umem_uva_inj |].
    intros Hinj. by rewrite (umem_bytes_own pt M Hinj).
  Qed.

  (* what re-establishing [umem] after a step needs: here the injectivity
     must be carried, since there is no [umem] left to derive it from *)
  Lemma bytes_to_umem (pt : uptd) (M : gmap Z (bv 8)) :
    uva_inj pt M -> bytes_own (upa_map pt M) ⊢ umem pt M.
  Proof. intros Hinj. by rewrite (umem_bytes_own pt M Hinj). Qed.

End UmodeMemBridge.
