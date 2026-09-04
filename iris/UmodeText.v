(* UmodeText.v -- A VERIFIED PROCESS'S TEXT AS STAMPED BYTES
   (claude-notes/projects/icache.md, "The verified tier: text OUTSIDE the
   walker").

   The verified user-mode tier fetches the program's OWN word, so its fetch
   node must pay [HartMFetch.fobl_ifetch] -- the icache agent reads the
   byte at every view from the hart's instruction view up -- and the payer
   is the stamped byte [TsoCtx.ctx_phys_xpointsto ξ IK a 1 b] (latest write
   at or below [IK]) beside the hart's receipt [hart_iview_lb_at cpu_id IK]
   (its instruction view has passed [IK]).  Both are born at [userret]'s
   [fence.i] (STEP 0) and die at the trap back into the kernel.

   THE TEXT is the image's bytes on the EXECUTABLE-AND-NOT-WRITABLE pages
   of the page table -- [UserHeap.utext_part]'s class, read off the PTE
   bits rather than the permission projection so that no [sz] is needed --
   and it is exactly what the walker must never own: [HartMemRunX] frames
   the stamped submap of [bytes_own_p] around every walk, so a stamp
   survives the process's execution by construction (every store lands on
   a W page, hence not on text).

   Layout: §1 the text pages and the image's split; §2 the per-address
   payload [uv_F] over the physical image; §3 the stamped image [umem_x],
   its view as [bytes_own_p], the mint at a [fence.i] and the forget.      *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import TsoMemPa.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import UptTree UserPtTree UserPerm ProcPtOwn.
Require Import TsoCtx.
Require Import HartMemRun HartMemRunX HartBarrier PtBytes.
Require Import UmodeMem UmodeArith.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 The text pages, and the image split by them.                         *)
(* ===================================================================== *)

(* [uva_text] itself lives in [UmodeMem] (it is a field of [uinstr]);
   [UserPerm.pte_bit] is the same test, spelled for the projection. *)
Lemma uva_text_bits (pt : uptd) (va : Z) :
  uva_text pt va <->
  exists w : mword 64,
    ud_um pt !! svpn_of (mword_of_int va : mword 64) = Some w /\
    pte_bit w 3 = true /\ pte_bit w 2 = false.
Proof. reflexivity. Qed.

(* the heap's classes agree with it: an X-and-not-W page of the projection
   IS a text page of the table *)
Lemma uva_text_of_perm (pt : uptd) (sz : Z) (va : Z) (q : uperm) :
  uperm_at (perm_of (ud_um pt) sz) (mword_of_int va : mword 64) = Some q ->
  up_X q = true -> up_W q = false ->
  uva_text pt va.
Proof.
  intros Hq Hx Hw. unfold uperm_at in Hq.
  destruct (perm_of_lookup_Some _ _ _ _ Hq) as [(w & Hl & _ & _ & ->) | [_ ->]].
  - exists w. split_and!; [exact Hl | exact Hx | exact Hw].
  - discriminate Hx.
Qed.

Definition uM_text (pt : uptd) (M : gmap Z (bv 8)) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => uva_text pt kv.1) M.

Definition uM_data (pt : uptd) (M : gmap Z (bv 8)) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => ~ uva_text pt kv.1) M.

Lemma uM_union (pt : uptd) (M : gmap Z (bv 8)) :
  uM_text pt M ∪ uM_data pt M = M.
Proof. apply map_filter_union_complement. Qed.

Lemma uM_disj (pt : uptd) (M : gmap Z (bv 8)) :
  uM_text pt M ##ₘ uM_data pt M.
Proof. apply map_disjoint_filter_complement. Qed.

Lemma uM_text_sub (pt : uptd) (M : gmap Z (bv 8)) : uM_text pt M ⊆ M.
Proof. apply map_filter_subseteq. Qed.

Lemma uM_data_sub (pt : uptd) (M : gmap Z (bv 8)) : uM_data pt M ⊆ M.
Proof. apply map_filter_subseteq. Qed.

Lemma uM_text_lookup (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
  uM_text pt M !! va = Some b <-> M !! va = Some b /\ uva_text pt va.
Proof. rewrite /uM_text map_lookup_filter_Some. reflexivity. Qed.

Lemma uM_data_lookup (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
  uM_data pt M !! va = Some b <-> M !! va = Some b /\ ~ uva_text pt va.
Proof. rewrite /uM_data map_lookup_filter_Some. reflexivity. Qed.

(* a store on a non-text address leaves the text half alone and updates
   the data half in place *)
Lemma uM_text_insert_data (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
  ~ uva_text pt va -> uM_text pt (<[va := b]> M) = uM_text pt M.
Proof.
  intros Hn. rewrite /uM_text. apply map_filter_insert_not'; [exact Hn |].
  intros y _. exact Hn.
Qed.

Lemma uM_data_insert_data (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
  ~ uva_text pt va -> uM_data pt (<[va := b]> M) = <[va := b]> (uM_data pt M).
Proof. intros Hn. rewrite /uM_data. by apply map_filter_insert_True. Qed.

(* injectivity restricts to a submap *)
Lemma uva_inj_sub (pt : uptd) (M M' : gmap Z (bv 8)) :
  M' ⊆ M -> uva_inj pt M -> uva_inj pt M'.
Proof.
  intros Hsub Hinj va1 va2 H1 H2 Heq.
  apply Hinj; [| | exact Heq]; eapply subseteq_dom; [exact Hsub | exact H1 | exact Hsub | exact H2].
Qed.

(* the re-keyed image splits the same way *)
Lemma upa_map_sub (pt : uptd) (M M' : gmap Z (bv 8)) :
  M' ⊆ M -> uva_inj pt M -> upa_map pt M' ⊆ upa_map pt M.
Proof.
  intros Hsub Hinj. apply map_subseteq_spec. intros a b Ha.
  apply upa_map_lookup_inv in Ha as (va & <- & Hva).
  apply upa_map_lookup; [exact Hinj |].
  eapply lookup_weaken; [exact Hva | exact Hsub].
Qed.

Lemma upa_map_split_disj (pt : uptd) (M : gmap Z (bv 8)) :
  uva_inj pt M ->
  upa_map pt (uM_text pt M) ##ₘ upa_map pt (uM_data pt M).
Proof.
  intros Hinj. apply map_disjoint_spec. intros a b1 b2 H1 H2.
  apply upa_map_lookup_inv in H1 as (va1 & Ha1 & Hva1).
  apply upa_map_lookup_inv in H2 as (va2 & Ha2 & Hva2).
  apply uM_text_lookup in Hva1 as [Hva1 Ht1].
  apply uM_data_lookup in Hva2 as [Hva2 Ht2].
  assert (va1 = va2).
  { apply Hinj; [by eapply elem_of_dom_2 | by eapply elem_of_dom_2 | congruence]. }
  subst va2. exact (Ht2 Ht1).
Qed.

Lemma upa_map_split (pt : uptd) (M : gmap Z (bv 8)) :
  uva_inj pt M ->
  upa_map pt M = upa_map pt (uM_text pt M) ∪ upa_map pt (uM_data pt M).
Proof.
  intros Hinj.
  pose proof (uva_inj_sub pt M _ (uM_text_sub pt M) Hinj) as Hinjt.
  pose proof (uva_inj_sub pt M _ (uM_data_sub pt M) Hinj) as Hinjd.
  pose proof (upa_map_split_disj pt M Hinj) as Hd.
  apply map_eq. intros a. apply option_eq. intros b. split.
  - intros Ha. apply upa_map_lookup_inv in Ha as (va & Heq & Hva). subst a.
    destruct (decide (uva_text pt va)) as [Ht | Hn].
    + apply lookup_union_Some_l. apply upa_map_lookup; [exact Hinjt |].
      apply uM_text_lookup. by split.
    + apply lookup_union_Some_r; [exact Hd |].
      apply upa_map_lookup; [exact Hinjd |]. apply uM_data_lookup. by split.
  - intros Ha.
    destruct (proj1 (lookup_union_Some _ _ _ _ Hd) Ha) as [Hx | Hx];
      apply upa_map_lookup_inv in Hx as (va & Heq & Hva); subst a;
      [ apply uM_text_lookup in Hva as [Hva _]
      | apply uM_data_lookup in Hva as [Hva _] ];
      exact (upa_map_lookup pt M va b Hinj Hva).
Qed.

(* ===================================================================== *)
(* §2 The per-address payload over the physical image.                     *)
(* ===================================================================== *)

Definition uv_F (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (a : Arch.pa)
    : option nat :=
  if decide (a ∈ (dom (upa_map pt (uM_text pt M)) : gset Arch.pa))
  then Some IK else None.

Lemma uv_F_text (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (a : Arch.pa) :
  a ∈ (dom (upa_map pt (uM_text pt M)) : gset Arch.pa) -> uv_F pt M IK a = Some IK.
Proof. intros Ha. rewrite /uv_F decide_True //. Qed.

Lemma uv_F_none (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (a : Arch.pa) :
  a ∉ (dom (upa_map pt (uM_text pt M)) : gset Arch.pa) -> uv_F pt M IK a = None.
Proof. intros Ha. rewrite /uv_F decide_False //. Qed.

Lemma uv_F_none_inv (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (a : Arch.pa) :
  uv_F pt M IK a = None -> a ∉ (dom (upa_map pt (uM_text pt M)) : gset Arch.pa).
Proof. rewrite /uv_F. intros H Ha. rewrite decide_True // in H. Qed.

Lemma uv_F_some_inv (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (a : Arch.pa) :
  ~ (uv_F pt M IK a = None) -> a ∈ (dom (upa_map pt (uM_text pt M)) : gset Arch.pa).
Proof.
  rewrite /uv_F. intros H. destruct (decide (a ∈ dom (upa_map pt (uM_text pt M)))); [done |].
  exfalso. by apply H.
Qed.

(* the payload is a function of the TEXT half: a data store keeps it *)
Lemma uv_F_insert_data (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (va : Z) (b : bv 8) :
  ~ uva_text pt va -> uv_F pt (<[va := b]> M) IK = uv_F pt M IK.
Proof. intros Hn. unfold uv_F. rewrite (uM_text_insert_data pt M va b Hn). reflexivity. Qed.

(* the payload is a function of the TEXT half, pointwise *)
Lemma uv_F_ext (pt : uptd) (M M' : gmap Z (bv 8)) (IK : nat) :
  uM_text pt M' = uM_text pt M ->
  forall a : Arch.pa, uv_F pt M IK a = uv_F pt M' IK a.
Proof. intros Htext a. unfold uv_F. rewrite Htext. reflexivity. Qed.

(* a W page of the projection is NOT text *)
Lemma uva_text_not_W (pt : uptd) (sz : Z) (va : mword 64) (q : uperm) :
  uperm_at (perm_of (ud_um pt) sz) va = Some q -> up_W q = true ->
  ~ uva_text pt (uint va).
Proof.
  intros Hq Hw (w & Hl & _ & Hnw). unfold uperm_at in Hq.
  rewrite moi_of_uint in Hl.
  destruct (perm_of_W_mapped _ _ _ _ _ Hq Hw Hl) as (_ & _ & Hwb).
  unfold pte_bit in Hwb. rewrite Hwb in Hnw. discriminate.
Qed.

(* the unstamped submap of the re-keyed image is the data half *)
Lemma uf_none_upa (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) :
  uva_inj pt M ->
  uf_none (uv_F pt M IK) (upa_map pt M) = upa_map pt (uM_data pt M).
Proof.
  intros Hinj.
  pose proof (upa_map_split_disj pt M Hinj) as Hd.
  apply map_eq. intros a. apply option_eq. intros b. split.
  - intros H. apply uf_none_lookup in H as [Ha HF].
    rewrite (upa_map_split pt M Hinj) in Ha.
    destruct (proj1 (lookup_union_Some _ _ _ _ Hd) Ha) as [Hx | Hx]; [| exact Hx].
    exfalso. apply uv_F_none_inv in HF. apply HF. apply elem_of_dom. by exists b.
  - intros Hb. apply uf_none_lookup. split.
    + rewrite (upa_map_split pt M Hinj). apply lookup_union_Some_r; [exact Hd | exact Hb].
    + apply uv_F_none. intros Ht. apply elem_of_dom in Ht as [b' Hb'].
      exact (proj1 (map_disjoint_spec _ _) Hd a b' b Hb' Hb).
Qed.

Lemma uf_some_upa (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) :
  uva_inj pt M ->
  uf_some (uv_F pt M IK) (upa_map pt M) = upa_map pt (uM_text pt M).
Proof.
  intros Hinj.
  pose proof (upa_map_split_disj pt M Hinj) as Hd.
  apply map_eq. intros a. apply option_eq. intros b. split.
  - intros H. apply uf_some_lookup in H as [Ha HF].
    rewrite (upa_map_split pt M Hinj) in Ha.
    destruct (proj1 (lookup_union_Some _ _ _ _ Hd) Ha) as [Hx | Hx]; [exact Hx |].
    exfalso. apply HF. apply uv_F_none. intros Ht.
    apply elem_of_dom in Ht as [b' Hb'].
    exact (proj1 (map_disjoint_spec _ _) Hd a b' b Hb' Hx).
  - intros Hb. apply uf_some_lookup. split.
    + rewrite (upa_map_split pt M Hinj). apply lookup_union_Some_l. exact Hb.
    + rewrite uv_F_text; [discriminate |]. apply elem_of_dom. by exists b.
Qed.

(* ===================================================================== *)
(* §3 The stamped image.                                                   *)
(* ===================================================================== *)

Section UmodeText.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the text half, stamped at [IK] *)
  Definition umem_text (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) : iProp Σ :=
    ([∗ map] va ↦ b ∈ uM_text pt M,
       TsoCtx.ctx_phys_xpointsto XI IK (uva_pa pt va : Arch.pa) (DfracOwn 1) b)%I.

  (* THE STAMPED IMAGE: the text half stamped at some [IK] the hart's
     instruction view has passed, the data half plain *)
  Definition umem_x (pt : uptd) (M : gmap Z (bv 8)) : iProp Σ :=
    (∃ IK : nat,
       hart_iview_lb_at cpu_id IK ∗
       umem_text pt M IK ∗
       umem pt (uM_data pt M))%I.

  Lemma umem_split (pt : uptd) (M : gmap Z (bv 8)) :
    umem pt M ⊣⊢ umem pt (uM_text pt M) ∗ umem pt (uM_data pt M).
  Proof.
    rewrite /umem -{1}(uM_union pt M). apply big_sepM_union. apply uM_disj.
  Qed.

  (* the stamps are forgotten at the trap back into the kernel *)
  Lemma umem_text_forget (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) :
    umem_text pt M IK ⊢ umem pt (uM_text pt M).
  Proof.
    rewrite /umem_text /umem. apply big_sepM_mono. intros va b _.
    apply ctx_phys_xpointsto_forget.
  Qed.

  Lemma umem_x_forget (pt : uptd) (M : gmap Z (bv 8)) :
    umem_x pt M ⊢ umem pt M.
  Proof.
    rewrite /umem_x. iIntros "(%IK & _ & Ht & Hd)".
    rewrite (umem_split pt M). iFrame "Hd". by iApply umem_text_forget.
  Qed.

  Lemma umem_x_uva_inj (pt : uptd) (M : gmap Z (bv 8)) :
    umem_x pt M ⊢ ⌜uva_inj pt M⌝.
  Proof. rewrite umem_x_forget. apply umem_uva_inj. Qed.

  (* two separately owned maps are disjoint whatever the payload *)
  Lemma bytes_own_p_disj (F : Arch.pa -> option nat) (m1 m2 : PtBytes.pamap) :
    bytes_own m1 -∗ bytes_own_p F m2 -∗ ⌜m1 ##ₘ m2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (bytes_own_p_forget with "H2") as "H2".
    iApply (bytes_own_disj with "H1 H2").
  Qed.


  (* the re-keying, for any body: [umem_bytes_own]'s proof, generalised *)
  Lemma upa_big_sepM (pt : uptd) (M : gmap Z (bv 8))
      (Φ : Arch.pa -> bv 8 -> iProp Σ) :
    uva_inj pt M ->
    ([∗ map] a ↦ b ∈ upa_map pt M, Φ a b)
    ⊣⊢ ([∗ map] va ↦ b ∈ M, Φ (uva_pa pt va : Arch.pa) b).
  Proof.
    intros Hinj. rewrite /upa_map.
    rewrite big_sepM_list_to_map; [| by apply upa_list_nodup].
    rewrite /upa_list big_sepL_fmap big_sepM_map_to_list. reflexivity.
  Qed.

  (* THE VIEW: the stamped image at [IK] IS the payload-indexed byte map
     over the re-keyed image *)
  Lemma umem_x_bytes (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) :
    uva_inj pt M ->
    umem_text pt M IK ∗ umem pt (uM_data pt M)
    ⊣⊢ bytes_own_p (uv_F pt M IK) (upa_map pt M).
  Proof.
    intros Hinj.
    pose proof (uva_inj_sub pt M _ (uM_text_sub pt M) Hinj) as Hinjt.
    pose proof (uva_inj_sub pt M _ (uM_data_sub pt M) Hinj) as Hinjd.
    pose proof (upa_map_split_disj pt M Hinj) as Hd.
    rewrite (upa_map_split pt M Hinj) (bytes_own_p_union _ _ _ Hd).
    apply bi.sep_proper.
    - rewrite /bytes_own_p (upa_big_sepM pt (uM_text pt M) _ Hinjt) /umem_text.
      apply big_sepM_proper. intros va b Hb.
      rewrite /xbyte uv_F_text; [reflexivity |].
      apply elem_of_dom. exists b. by apply upa_map_lookup.
    - rewrite bytes_own_p_of_none.
      + rewrite (umem_bytes_own pt (uM_data pt M) Hinjd). reflexivity.
      + intros a Ha. apply uv_F_none. intros Ht.
        apply map_disjoint_dom in Hd. set_solver.
  Qed.

  Lemma umem_x_to_bytes (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) :
    uva_inj pt M ->
    umem_text pt M IK ∗ umem pt (uM_data pt M) ⊢ bytes_own_p (uv_F pt M IK) (upa_map pt M).
  Proof. intros Hinj. rewrite (umem_x_bytes pt M IK Hinj). reflexivity. Qed.

  Lemma bytes_to_umem_x (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) :
    uva_inj pt M ->
    bytes_own_p (uv_F pt M IK) (upa_map pt M) ⊢ umem_text pt M IK ∗ umem pt (uM_data pt M).
  Proof. intros Hinj. rewrite (umem_x_bytes pt M IK Hinj). reflexivity. Qed.

  (* ---- THE MINT, at a [fence.i]: every text byte of a RUNNING image is
     stamped at the raised instruction view ([TsoCtx.ctx_phys_xstamp], one
     byte at a time under the same interp), and the hart's receipt is what
     the leaf hands in.  Shaped as [HartBarrier.ifence_step] so that
     [userret] STEP 0 runs it through [swp_hart_fence_i]. *)
  Lemma umem_text_stamp (pt : uptd) (T : gmap Z (bv 8)) (g : gstate) (IK : nat) :
    (g.(gtv) cpu_id <= IK)%nat ->
    (own_pub (hart_agent cpu_id) g.(glog) <= IK)%nat ->
    tso_interp_at riscv_eraGS g -∗ TsoCtx.own_context XI -∗
    ([∗ map] va ↦ b ∈ T,
       TsoCtx.ctx_phys_pointsto XI (uva_pa pt va : Arch.pa) (DfracOwn 1) b) -∗
    tso_interp_at riscv_eraGS g ∗ TsoCtx.own_context XI ∗
    ([∗ map] va ↦ b ∈ T,
       TsoCtx.ctx_phys_xpointsto XI IK (uva_pa pt va : Arch.pa) (DfracOwn 1) b).
  Proof.
    intros Htv Hpub.
    induction T as [|va b T Hfresh IH] using map_ind.
    - iIntros "Hint Hrun _". rewrite big_sepM_empty. by iFrame.
    - iIntros "Hint Hrun Hm". rewrite !big_sepM_insert //.
      iDestruct "Hm" as "[Hb Hm]".
      iDestruct (IH with "Hint Hrun Hm") as "(Hint & Hrun & Hm)".
      iDestruct (ctx_phys_xstamp g XI IK (uva_pa pt va : Arch.pa) (DfracOwn 1) b
                   Htv Hpub with "Hint Hrun Hb") as "(Hint & Hrun & Hb)".
      iFrame.
  Qed.

  Lemma umem_x_mint (pt : uptd) (M : gmap Z (bv 8)) :
    ⊢ ifence_step (umem pt M ∗ TsoCtx.own_context XI)
                  (umem_x pt M ∗ TsoCtx.own_context XI).
  Proof.
    rewrite /ifence_step. iIntros (g IK) "%Htv %Hpub #Hlb Hgh Hint [Hm Hrun]".
    rewrite (umem_split pt M). iDestruct "Hm" as "[Ht Hd]".
    iDestruct (umem_text_stamp pt (uM_text pt M) g IK Htv Hpub
                 with "Hint Hrun Ht") as "(Hint & Hrun & Ht)".
    iModIntro. iFrame "Hgh Hint Hrun".
    iExists IK. iFrame "Hlb Hd". iExact "Ht".
  Qed.

  (* ================================================================== *)
  (* §4 THE KERNEL'S LAZY VIEW, STAMPED.  [UserPtTree.user_ptm_inv]'s     *)
  (* twin with the image in the stamped form [umem_x]: what the slot's   *)
  (* bundle ([UexecRet.uvb_F]) carries while the process RUNS.  Born at   *)
  (* [userret]'s [fence.i] ([user_ptm_inv_x_mint]), forgotten at the trap  *)
  (* back into the kernel ([user_ptm_inv_x_forget]).                       *)
  (* ================================================================== *)
  Definition umem_own_x (P : uptd) (M : gmap Z (bv 8)) : iProp Σ :=
    (⌜dom M = uva_dom P⌝ ∗ umem_x P M)%I.

  Definition umem_lazy_x (P : uptd) (sz : Z) (M : gmap Z (bv 8)) : iProp Σ :=
    (∃ Mp : gmap Z (bv 8),
       ⌜Mp ⊆ M⌝ ∗
       ⌜forall va, is_Some (M !! va) <-> (uva_mapped P va \/ uva_live sz va)⌝ ∗
       ⌜forall va, ~ uva_mapped P va -> uva_live sz va ->
                   M !! va = Some (bv_0 8)⌝ ∗
       umem_own_x P Mp)%I.

  Definition user_ptm_inv_x (P : uptd) (sz : Z) (M : gmap Z (bv 8)) : iProp Σ :=
    (utlb_inv_pt P.(ud_root) P.(ud_tfp) P.(ud_um) ∗
     umem_lazy_x P sz M ∗
     ⌜uva_pa_inj P⌝ ∗
     ⌜upt_acc_wf P.(ud_um)⌝)%I.

  Lemma umem_lazy_x_forget (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    umem_lazy_x P sz M ⊢ umem_lazy P sz M.
  Proof.
    rewrite /umem_lazy_x /umem_lazy /umem_own_x /umem_own.
    iIntros "(%Mp & %Hsub & %Hiff & %Hz & %Hdom & Hm)".
    iExists Mp. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iApply (umem_x_forget with "Hm").
  Qed.

  Lemma user_ptm_inv_x_forget (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    user_ptm_inv_x P sz M ⊢ user_ptm_inv P sz M.
  Proof.
    rewrite /user_ptm_inv_x /user_ptm_inv.
    iIntros "(Htlb & Hm & %Hinj & %Hacc)". iFrame "Htlb".
    iSplitL "Hm"; [iApply (umem_lazy_x_forget with "Hm") |].
    iPureIntro. exact (conj Hinj Hacc).
  Qed.

  (* the mint, shaped for [userret] STEP 0 ([HartBarrier.ifence_step]) *)
  Lemma user_ptm_inv_x_mint (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    ⊢ ifence_step (user_ptm_inv P sz M ∗ TsoCtx.own_context XI)
                  (user_ptm_inv_x P sz M ∗ TsoCtx.own_context XI).
  Proof.
    rewrite /ifence_step. iIntros (g IK) "%Htv %Hpub #Hlb Hgh Hint [Hpt Hrun]".
    rewrite /user_ptm_inv /user_ptm_inv_x /umem_lazy /umem_lazy_x /umem_own /umem_own_x.
    iDestruct "Hpt" as "(Htlb & (%Mp & %Hsub & %Hiff & %Hz & %Hdom & Hm) & %Hinj & %Hacc)".
    iAssert (umem P Mp) with "[Hm]" as "Hm"; [iExact "Hm" |].
    rewrite (umem_split P Mp).
    iDestruct "Hm" as "[Ht Hd]".
    iDestruct (umem_text_stamp P (uM_text P Mp) g IK Htv Hpub
                 with "Hint Hrun Ht") as "(Hint & Hrun & Ht)".
    iModIntro. iFrame "Hgh Hint Hrun Htlb".
    iSplitL; [| iPureIntro; exact (conj Hinj Hacc)].
    iExists Mp. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iExists IK. iFrame "Hlb Hd". iExact "Ht".
  Qed.

  (* the same mint at the LAZY view alone, which is what [userret] holds *)
  Lemma umem_lazy_x_mint (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    ⊢ ifence_step (umem_lazy P sz M ∗ TsoCtx.own_context XI)
                  (umem_lazy_x P sz M ∗ TsoCtx.own_context XI).
  Proof.
    rewrite /ifence_step. iIntros (g IK) "%Htv %Hpub #Hlb Hgh Hint [Hlz Hrun]".
    rewrite /umem_lazy /umem_lazy_x /umem_own /umem_own_x.
    iDestruct "Hlz" as "(%Mp & %Hsub & %Hiff & %Hz & %Hdom & Hm)".
    iAssert (umem P Mp) with "[Hm]" as "Hm"; [iExact "Hm" |].
    rewrite (umem_split P Mp).
    iDestruct "Hm" as "[Ht Hd]".
    iDestruct (umem_text_stamp P (uM_text P Mp) g IK Htv Hpub
                 with "Hint Hrun Ht") as "(Hint & Hrun & Ht)".
    iModIntro. iFrame "Hgh Hint Hrun".
    iExists Mp. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iExists IK. iFrame "Hlb Hd". iExact "Ht".
  Qed.

  (* THE STAMPED MAPPED VIEW: [UserPtTree.user_pt_inv]'s twin, what a
     verified slot's body ([UexecWp.uexec_F]) is handed *)
  Definition user_pt_inv_x (P : uptd) (M : gmap Z (bv 8)) : iProp Σ :=
    (utlb_inv_pt P.(ud_root) P.(ud_tfp) P.(ud_um) ∗
     umem_own_x P M ∗
     ⌜uva_pa_inj P⌝ ∗
     ⌜upt_acc_wf P.(ud_um)⌝)%I.

  Lemma user_pt_inv_x_forget (P : uptd) (M : gmap Z (bv 8)) :
    user_pt_inv_x P M ⊢ user_pt_inv P M.
  Proof.
    rewrite /user_pt_inv_x /user_pt_inv /umem_own_x /umem_own.
    iIntros "(Htlb & (%Hdom & Hm) & %Hinj & %Hacc)". iFrame "Htlb".
    iSplitL "Hm"; [ iSplitR; [done|]; iApply (umem_x_forget with "Hm") | ].
    iPureIntro. exact (conj Hinj Hacc).
  Qed.

  (* the mapped sub-image at some map ([UserPtTree.user_ptm_inv_pt]) *)
  Lemma user_ptm_inv_x_pt (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    user_ptm_inv_x P sz M -∗ ∃ Mp : gmap Z (bv 8), user_pt_inv_x P Mp.
  Proof.
    rewrite /user_ptm_inv_x /umem_lazy_x /user_pt_inv_x.
    iIntros "(Htlb & (%Mp & _ & _ & _ & Hm) & %Hinj & %Hacc)".
    iExists Mp. iFrame "Htlb Hm". iPureIntro. exact (conj Hinj Hacc).
  Qed.

  (* [ProcPtOwn.user_ptm_inv_close] at the stamped view: the trap round's
     exit, where userret's fence.i has just re-minted the pages *)
  Lemma user_ptm_inv_x_close (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    proc_pt_wf P ->
    utlb_inv_pt P.(ud_root) P.(ud_tfp) P.(ud_um) -∗
    umem_lazy_x P sz M -∗
    user_ptm_inv_x (ud_norm P) sz M.
  Proof.
    intros (Hmwf & Hacc & _ & Hinj & _).
    rewrite /user_ptm_inv_x.
    unfold ud_norm; cbn [ud_root ud_tfp ud_um ud_data].
    iIntros "Htlb Hm".
    iSplitL "Htlb"; [iExact "Htlb" |].
    iSplitL "Hm"; [iExact "Hm" |].
    iPureIntro. split; [exact (uva_pa_inj_of_wf P Hmwf Hinj) | exact Hacc].
  Qed.

End UmodeText.
