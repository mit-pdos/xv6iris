(* ===================================================================== *)
(* UkCatFIface.v -- THE PRODUCER [cat f]'s MERGED REGISTRY (union.md      *)
(* C9d', review items S5 and the seams (b) and (c)).                      *)
(*                                                                        *)
(* [cat f] at the head of an N-stage pipeline holds two kinds of          *)
(* endpoint the landed instances keep apart: the INPUT on `f` (the file   *)
(* application's [UkFileIface], the deed at a pinned fraction) and the    *)
(* round's pipe write end with the N-family console writer (the          *)
(* pipeline's [UkPipesIface]).  This file is ONE [UkHandler.ep_ifaceP]   *)
(* over a registry of two kinds:                                          *)
(*                                                                        *)
(*   [UDIn s nm i γo]   an input on the file named [nm] (seam (b): the    *)
(*                      name is a field, pinned to [fname_f] by the       *)
(*                      binding's last clause), at a tail handle or --   *)
(*                      [s] set -- a standard slot;                       *)
(*   [UDProd pn gp w A X]                                                  *)
(*                      THE PRODUCER DEVICE ([ProgTree.DProd]): fd 1 the  *)
(*                      first pipe's write end at [pn], fd 2 the family   *)
(*                      writer [w], its diagnostics among [A] and its     *)
(*                      FAILURE REPORTS among [X].                        *)
(*                                                                        *)
(* THE REFUSED-OPEN DEPOSIT.  When the open of `f` is refused, the round  *)
(* expects the stage's untouched write permit [wcur pn 0] deposited at    *)
(* the first byte of [cat: cannot open f] ([UShPipesDefs.pdep]).  The     *)
(* permit is the pipe's; the report is the console's.  With the two as   *)
(* SEPARATE devices no instance can pay: [ProgTree.conforms] at           *)
(* [catf_env (DOutH [c; []]) [[]; cat_dg_open f; cat_dg_write]] admits a  *)
(* tree that writes on fd 1 and THEN reports on fd 2, and one that       *)
(* reports and then writes, and each law must pay its write at every     *)
(* state -- both need the one exclusive permit, and nothing refutes the   *)
(* second (the family's exclusions are between deposits, and no deposit   *)
(* exists yet).  Shared state in [ei_fds] cannot help: it decides who     *)
(* holds the permit, never that the other write cannot come.  So the     *)
(* pairing is PURE: one device number on both descriptors                 *)
(* ([ProgTree.DProd], [ProgTreePipes.cat_file_prod_conforms]), the report *)
(* chosen only while the pipe is untouched and leaving it owing nothing,  *)
(* the first pipe byte retiring the report.  The device's resource        *)
(* ([cif_pbody]) holds the permit while nothing has fired, the report's   *)
(* kit as a wand FROM the permit ([□ (wcur pn 0 -∗ dep w x)]), and the    *)
(* report's first byte spends the permit into the deposit.  No model     *)
(* corner and no ruling: the line model is untouched.                     *)
(*                                                                        *)
(* THE CLAIM is [PipeOutN.peclV] at ANY line model with a pipeline view   *)
(* (S5): the union's claim C9e' is that shape at the union model.  The    *)
(* file side needs only [AppFile]'s deed and credential ([cf], [rf]),     *)
(* which the union keeps.  The scope is over [uname] (seam (c)).          *)
(*                                                                        *)
(* THE EXIT.  [ei_fds] carries the exit wand [cif_xk]: from the taint, or *)
(* from every protected device's FINAL state ([cif_final]) and the deed   *)
(* back, to the payload -- the deed goes back through the payload; a     *)
(* terminal round's payload may drop it (B3).                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From Stdlib Require Import FunctionalExtensionality.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UkRun UkRunSys UkRunLeaf.
Require Import SpecConsolewrite.
Require Import SpecSysRead.
Require Import WpUart.
Require Import UkWriteLeaf.
Require Import FdSlots ProcGeom UserFd UserCwd.
Require Import UsysMemOk UexecSG UexecSlot UexecRet.
Require Import UexecExecInst.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import FsCfg AppCfg AppInv.
Require Import FsImg FsImgCheck.
Require Import SysOpenDefs.
Require Import LineWords LineBytes EchoDisc.
Require Import EchoOut AppEcho.
Require Import LineModel LineModelLinks.
Require Import GenOutPure GenOut.
Require Import FileDisc.
Require Import AppFile AppFileCons FileOpen UserOff UkFileOpen.
Require Import PipesPair PipesDisc PipeBothNPure PipeBothN PipeOutN PipesView.
Require Import PipeOut PipeNames PipeQueue PipeReg PipeProto.
Require Import CtxIdDefs.
Require Import UserHeap.
Require Import ProgTree ProgTreePipes UkTree UkStub.
Require Import UkCatTree.   (* [bvs_moi_small] *)
Require Import UkConsOut UkPipeDev UkFileDev.
Require Import UkHandler UkFreeHandler.
Require Import UkPipesIface.
Import PipeNames.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE NAME CLASS (seam (c)) AND THE REGISTRY                        *)
(* ===================================================================== *)

(* the user files a line may name: the model's class [FileDisc.uname]
   (claude-notes/design/filenames.md) *)

Inductive cfdev :=
  | UDIn (s : bool) (nm : list (bv 8)) (i : Z) (γo : gname)
  | UDProd (pn : pnames) (gp : pipe_names) (w : wid) (A X : list (list (bv 8))).

Definition cifRegR := discrete_funUR (fun _ : nat => optionUR (dfrac_agreeR (leibnizO cfdev))).
Class cifRegG (Σ : gFunctors) := CifRegG { cif_reg_inG :: inG Σ cifRegR }.
Definition cifRegΣ : gFunctors := #[GFunctor cifRegR].
Global Instance subG_cifRegΣ {Σ} : subG cifRegΣ Σ -> cifRegG Σ.
Proof using . solve_inG. Qed.

Definition cif_pool (B : gset nat) (w : nat -> cfdev) : cifRegR :=
  fun d => if decide (d ∈ B) then None
           else Some (to_dfrac_agree (DfracOwn 1) (w d : leibnizO cfdev)).

Definition cif_single (d : nat) (q : Qp) (v : cfdev) : cifRegR :=
  discrete_fun_singleton d (Some (to_dfrac_agree (DfracOwn q) (v : leibnizO cfdev))).

Lemma cif_dfa_valid (v : cfdev) : ✓ (to_dfrac_agree (DfracOwn 1) (v : leibnizO cfdev)).
Proof using . split; [apply dfrac_valid_own; reflexivity | done]. Qed.

Lemma cif_pool_valid (B : gset nat) (w : nat -> cfdev) : ✓ cif_pool B w.
Proof using .
  intros d. rewrite /cif_pool. case_decide; [done |].
  apply Some_valid, cif_dfa_valid.
Qed.

Lemma cif_pool_take (B : gset nat) (w : nat -> cfdev) (d : nat) :
  d ∉ B -> cif_pool B w ≡ cif_pool ({[d]} ∪ B) w ⋅ cif_single d 1 (w d).
Proof using .
  intros Hd x. rewrite discrete_fun_lookup_op /cif_pool /cif_single.
  destruct (decide (x = d)) as [-> | Hne].
  - rewrite discrete_fun_lookup_singleton.
    rewrite decide_False; [| exact Hd]. rewrite decide_True; [| set_solver].
    by rewrite left_id.
  - rewrite discrete_fun_lookup_singleton_ne; [| congruence]. rewrite right_id.
    destruct (decide (x ∈ B)) as [Hx | Hx];
      [rewrite decide_True; [done | set_solver] | rewrite decide_False; [done | set_solver]].
Qed.

Lemma cif_pool_ext (B B' : gset nat) (w w' : nat -> cfdev) :
  B = B' -> (forall x, x ∉ B -> w x = w' x) -> cif_pool B w = cif_pool B' w'.
Proof using .
  intros <- Hw.
  assert (H : forall x, cif_pool B w x = cif_pool B w' x).
  { intros x. rewrite /cif_pool. case_decide as Hx; [reflexivity |]. by rewrite (Hw x Hx). }
  exact (functional_extensionality _ _ H).
Qed.

Lemma cif_pool_update (B : gset nat) (w : nat -> cfdev) (v : cfdev) :
  cif_pool B w ~~> cif_pool B (fun _ => v).
Proof using .
  apply discrete_fun_update. intros a. rewrite /cif_pool.
  case_decide; [reflexivity |].
  apply option_update, cmra_update_exclusive, cif_dfa_valid.
Qed.

Lemma cif_reg_alloc `{!cifRegG Σ} (w : nat -> cfdev) : ⊢ |==> ∃ γ, own γ (cif_pool ∅ w).
Proof using . iApply own_alloc. apply cif_pool_valid. Qed.

(* the row a descriptor's device demands of it *)
Definition cif_row (ov : option cfdev) (fd : Z) (l : list fdstate) : Prop :=
  match ov with
  | Some (UDIn true _ i γo) => fd < Z.of_nat NSTD
                   /\ l !! Z.to_nat fd = Some (FdOpen true false (FdInode i γo OffHeld))
  | Some (UDIn false _ _ _) => Z.of_nat NSTD <= fd
  | Some (UDProd _ gp _ _ _) =>
      (fd = prod_out /\ exists rb, l !! 1%nat = Some (FdOpen rb true (FdPipe gp)))
      \/ (fd = prod_err /\ exists rb, l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)))
  | None => False
  end.

(* THE BINDING: the descriptors against the ledger and the registry's
   values, the protected devices [kds] at their values throughout, and
   every input's name pinned to `f` (seam (b)) *)
Definition cif_ok (kds : list (nat * cfdev)) (fdm : fdmap) (l : list fdstate)
    (vs : gmap nat cfdev) : Prop :=
  (forall fd d, fdm !! fd = Some d -> 0 <= fd < Z.of_nat NOFILE)
  /\ (forall fd d, fdm !! fd = Some d -> cif_row (vs !! d) fd l)
  /\ (forall d, d ∈ dom vs -> (exists fd, fdm !! fd = Some d) \/ d ∈ kds.*1)
  /\ (forall fd d, fdm !! fd = Some d -> d ∈ dom vs)
  /\ (forall fd fd' d s nm i γo, fdm !! fd = Some d -> fdm !! fd' = Some d ->
        vs !! d = Some (UDIn s nm i γo) -> fd = fd')
  /\ (forall dk, dk ∈ kds -> vs !! dk.1 = Some dk.2)
  /\ (forall d s nm i γo, vs !! d = Some (UDIn s nm i γo) -> nm = fname_f).

Lemma cif_slot_ne (k : nat) (fd : Z) : 0 <= fd -> fd <> Z.of_nat k -> k <> Z.to_nat fd.
Proof using .
  intros H0 Hne Heq. apply Hne. symmetry. rewrite Heq. apply Z2Nat.id. exact H0.
Qed.

Section cif_ok_lemmas.
  Context (kds : list (nat * cfdev)).
  Local Notation Dp := (kds.*1).

  Lemma cif_ok_lookup fdm l vs fd d :
    cif_ok kds fdm l vs -> fdm !! fd = Some d -> exists v, vs !! d = Some v.
  Proof using .
    intros (_ & _ & _ & H4 & _) Hfd. apply elem_of_dom. exact (H4 fd d Hfd).
  Qed.

  Lemma cif_ok_reg_insert (fdm : fdmap) (vs : gmap nat cfdev) (k : nat) (d : nat) (v : cfdev) :
    (forall d, d ∈ dom vs -> (exists fd, fdm !! fd = Some d) \/ d ∈ Dp) ->
    (forall fd d, fdm !! fd = Some d -> d ∈ dom vs) ->
    fdm !! Z.of_nat k = None ->
    (forall d', d' ∈ dom (<[d := v]> vs) ->
       (exists fd, <[Z.of_nat k := d]> fdm !! fd = Some d') \/ d' ∈ Dp)
    /\ (forall fd d', <[Z.of_nat k := d]> fdm !! fd = Some d' -> d' ∈ dom (<[d := v]> vs)).
  Proof using .
    intros H3 H4 Hnone. split.
    - intros d'. rewrite dom_insert_L elem_of_union elem_of_singleton. intros [-> | Hd'].
      + left. exists (Z.of_nat k). apply lookup_insert.
      + destruct (H3 d' Hd') as [(fd & Hfd) | HD]; [left | by right].
        exists fd. rewrite lookup_insert_ne; [exact Hfd |]. intros Heq.
        rewrite <- Heq in Hfd. congruence.
    - intros fd d'. rewrite dom_insert_L elem_of_union elem_of_singleton.
      destruct (decide (fd = Z.of_nat k)) as [-> |].
      + rewrite lookup_insert. intros [= <-]. by left.
      + rewrite lookup_insert_ne; [| congruence]. intros Hfd. right. exact (H4 fd d' Hfd).
  Qed.

  (* a fresh input on `f` at a fresh tail handle *)
  Lemma cif_ok_open fdm l vs (k : nat) (d : nat) (i : Z) (γo : gname) :
    cif_ok kds fdm l vs -> (NSTD <= k < NOFILE)%nat ->
    fdm !! Z.of_nat k = None -> (forall fd', fdm !! fd' <> Some d) -> d ∉ Dp ->
    cif_ok kds (<[Z.of_nat k := d]> fdm) l (<[d := UDIn false fname_f i γo]> vs).
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hk Hnone Hfr HD.
    destruct (cif_ok_reg_insert fdm vs k d (UDIn false fname_f i γo) H3 H4 Hnone) as [H3' H4'].
    split; [| split; [| split; [exact H3' | split; [exact H4' | split; [| split]]]]].
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
      + intros _. lia.
      + rewrite lookup_insert_ne; [| congruence]. apply H1.
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
      + rewrite lookup_insert. intros [= <-]. rewrite lookup_insert. simpl. lia.
      + rewrite (lookup_insert_ne fdm); [| congruence]. intros Hfd.
        rewrite (lookup_insert_ne vs); [| intros ->; exact (Hfr fd Hfd)]. exact (H2 fd d' Hfd).
    - intros fd fd' d' s' nm' i' γo'.
      destruct (decide (d' = d)) as [-> |].
      + intros Ha Hb _.
        destruct (decide (fd = Z.of_nat k)) as [-> |];
          [| rewrite lookup_insert_ne in Ha; [by destruct (Hfr fd) | congruence]].
        destruct (decide (fd' = Z.of_nat k)) as [-> |];
          [done | rewrite lookup_insert_ne in Hb; [by destruct (Hfr fd') | congruence]].
      + rewrite (lookup_insert_ne vs); [| congruence].
        intros Ha Hb.
        destruct (decide (fd = Z.of_nat k)) as [-> |];
          [rewrite lookup_insert in Ha; congruence | rewrite lookup_insert_ne in Ha; [| congruence]].
        destruct (decide (fd' = Z.of_nat k)) as [-> |];
          [rewrite lookup_insert in Hb; congruence | rewrite lookup_insert_ne in Hb; [| congruence]].
        apply (H5 fd fd' d' s' nm' i' γo' Ha Hb).
    - intros dk Hdk. rewrite lookup_insert_ne; [exact (H6 dk Hdk) |].
      intros Hq. apply HD. rewrite Hq. by apply elem_of_list_fmap_1.
    - intros d' s' nm' i' γo'. destruct (decide (d' = d)) as [-> |].
      + rewrite lookup_insert. intros [= _ <- _ _]. reflexivity.
      + rewrite lookup_insert_ne; [| congruence]. apply H7.
  Qed.

  (* every standard slot a descriptor names is OPEN, so a closed one is
     named by none *)
  Lemma cif_ok_closed_fresh fdm l vs (k : nat) :
    cif_ok kds fdm l vs -> length l = NSTD -> l !! k = Some FdClosed ->
    fdm !! Z.of_nat k = None.
  Proof using .
    intros (_ & H2 & _ & H4 & _) Hlen Hk.
    destruct (fdm !! Z.of_nat k) as [d |] eqn:E; [exfalso | reflexivity].
    assert (Hd : exists v, vs !! d = Some v) by (apply elem_of_dom; exact (H4 _ _ E)).
    destruct Hd as [v Hv]. specialize (H2 _ _ E). rewrite Hv in H2.
    pose proof (lookup_lt_Some _ _ _ Hk) as Hkl.
    destruct v as [[|] nm i γo | pn gp w A X]; simpl in H2.
    - destruct H2 as (_ & Hl). rewrite Nat2Z.id in Hl. congruence.
    - lia.
    - destruct H2 as [(Hk1 & rb & Hl) | (Hk2 & rb & Hl)].
      + unfold prod_out in Hk1. assert (k = 1%nat) as -> by lia. congruence.
      + unfold prod_err in Hk2. assert (k = 2%nat) as -> by lia. congruence.
  Qed.

  Lemma cif_ok_ledger fdm l l' vs :
    cif_ok kds fdm l vs ->
    (forall fd d, fdm !! fd = Some d -> l' !! Z.to_nat fd = l !! Z.to_nat fd) ->
    cif_ok kds fdm l' vs.
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hl.
    split; [exact H1 | split; [| exact (conj H3 (conj H4 (conj H5 (conj H6 H7))))]].
    intros fd d Hfd. specialize (H2 fd d Hfd). pose proof (Hl fd d Hfd) as Hq. unfold cif_row in *.
    revert H2. destruct (vs !! d) as [[[|] nm i γo | pn gp w A X] |]; intros H2; try exact H2.
    - rewrite Hq. exact H2.
    - destruct H2 as [(Hf & H) | (Hf & H)].
      + left. split; [exact Hf |]. subst fd. change (Z.to_nat prod_out) with 1%nat in Hq.
        rewrite Hq. exact H.
      + right. split; [exact Hf |]. subst fd. change (Z.to_nat prod_err) with 2%nat in Hq.
        rewrite Hq. exact H.
  Qed.

  Lemma cif_ok_open_std fdm l vs (k : nat) (d : nat) (i : Z) (γo : gname) :
    cif_ok kds fdm l vs -> length l = NSTD -> l !! k = Some FdClosed ->
    (forall fd', fdm !! fd' <> Some d) -> d ∉ Dp ->
    cif_ok kds (<[Z.of_nat k := d]> fdm) (<[k := FdOpen true false (FdInode i γo OffHeld)]> l)
      (<[d := UDIn true fname_f i γo]> vs).
  Proof using .
    intros Hok Hlen Hk Hfr HD.
    pose proof (cif_ok_closed_fresh fdm l vs k Hok Hlen Hk) as Hnone.
    pose proof (lookup_lt_Some _ _ _ Hk) as Hkl.
    assert (Hok' : cif_ok kds fdm (<[k := FdOpen true false (FdInode i γo OffHeld)]> l) vs).
    { apply (cif_ok_ledger fdm l _ vs Hok). intros fd d' Hfd.
      destruct Hok as (H1 & _). destruct (H1 fd d' Hfd) as [H0 _].
      apply list_lookup_insert_ne. intros Hq. apply (f_equal Z.of_nat) in Hq.
      rewrite Z2Nat.id in Hq; [| exact H0]. rewrite -Hq in Hfd. congruence. }
    destruct Hok' as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    destruct (cif_ok_reg_insert fdm vs k d (UDIn true fname_f i γo) H3 H4 Hnone) as [H3' H4'].
    split; [| split; [| split; [exact H3' | split; [exact H4' | split; [| split]]]]].
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
      + intros _. unfold NSTD, NOFILE in *. lia.
      + rewrite lookup_insert_ne; [| congruence]. apply H1.
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> | Hne].
      + rewrite lookup_insert. intros [= <-]. rewrite lookup_insert. simpl.
        split; [unfold NSTD in *; lia |]. rewrite Nat2Z.id. apply list_lookup_insert. exact Hkl.
      + rewrite (lookup_insert_ne fdm); [| congruence]. intros Hfd.
        rewrite (lookup_insert_ne vs); [| intros ->; exact (Hfr fd Hfd)]. exact (H2 fd d' Hfd).
    - intros fd fd' d' s' nm' i' γo'.
      destruct (decide (d' = d)) as [-> |].
      + intros Ha Hb _.
        destruct (decide (fd = Z.of_nat k)) as [-> |];
          [| rewrite lookup_insert_ne in Ha; [by destruct (Hfr fd) | congruence]].
        destruct (decide (fd' = Z.of_nat k)) as [-> |];
          [done | rewrite lookup_insert_ne in Hb; [by destruct (Hfr fd') | congruence]].
      + rewrite (lookup_insert_ne vs); [| congruence].
        intros Ha Hb.
        destruct (decide (fd = Z.of_nat k)) as [-> |];
          [rewrite lookup_insert in Ha; congruence | rewrite lookup_insert_ne in Ha; [| congruence]].
        destruct (decide (fd' = Z.of_nat k)) as [-> |];
          [rewrite lookup_insert in Hb; congruence | rewrite lookup_insert_ne in Hb; [| congruence]].
        apply (H5 fd fd' d' s' nm' i' γo' Ha Hb).
    - intros dk Hdk. rewrite lookup_insert_ne; [exact (H6 dk Hdk) |].
      intros Hq. apply HD. rewrite Hq. by apply elem_of_list_fmap_1.
    - intros d' s' nm' i' γo'. destruct (decide (d' = d)) as [-> |].
      + rewrite lookup_insert. intros [= _ <- _ _]. reflexivity.
      + rewrite lookup_insert_ne; [| congruence]. apply H7.
  Qed.

  Lemma cif_not_shared fdm fd d :
    ~ fd_shared fdm fd d -> forall fd', fd' <> fd -> fdm !! fd' <> Some d.
  Proof using .
    intros Hns fd' Hne Hfd'. apply Hns. exists fd'. split; [| exact Hfd'].
    apply elem_of_dom. rewrite lookup_delete_ne; [| congruence]. by eexists.
  Qed.

  Lemma cif_ok_close fdm l vs fd d :
    cif_ok kds fdm l vs -> fdm !! fd = Some d -> ~ fd_shared fdm fd d -> d ∉ Dp ->
    cif_ok kds (delete fd fdm) l (delete d vs).
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hfd Hns HD.
    pose proof (cif_not_shared fdm fd d Hns) as Hn.
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
    - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
      rewrite (lookup_delete_ne vs); [exact (H2 fd' d' Hf) |].
      intros Heq. subst d'. exact (Hn fd' (not_eq_sym Hne) Hf).
    - intros d'. rewrite dom_delete_L elem_of_difference elem_of_singleton.
      intros [Hd' Hne]. destruct (H3 d' Hd') as [(fd' & Hfd') | HD']; [left | by right].
      exists fd'. apply lookup_delete_Some. split; [| exact Hfd'].
      intros Heq. subst fd. rewrite Hfd in Hfd'. injection Hfd' as Hdd. exact (Hne (eq_sym Hdd)).
    - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
      rewrite dom_delete_L elem_of_difference elem_of_singleton.
      split; [exact (H4 fd' d' Hf) |]. intros Heq. subst d'. exact (Hn fd' (not_eq_sym Hne) Hf).
    - intros fa fb d' s' nm' i' γo' Ha Hb Hv.
      apply lookup_delete_Some in Ha as [_ Ha]. apply lookup_delete_Some in Hb as [_ Hb].
      apply lookup_delete_Some in Hv as [_ Hv].
      exact (H5 fa fb d' s' nm' i' γo' Ha Hb Hv).
    - intros dk Hdk. rewrite lookup_delete_ne; [exact (H6 dk Hdk) |].
      intros Hq. apply HD. rewrite Hq. by apply elem_of_list_fmap_1.
    - intros d' s' nm' i' γo' Hv. apply lookup_delete_Some in Hv as [_ Hv]. exact (H7 _ _ _ _ _ Hv).
  Qed.

  Lemma cif_ok_close_shared fdm l vs fd d :
    cif_ok kds fdm l vs -> fdm !! fd = Some d -> fd_shared_p Dp fdm fd d ->
    cif_ok kds (delete fd fdm) l vs.
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hfd Hsh. apply fd_shared_p_iff in Hsh.
    split; [| split; [| split; [| split; [| split; [| exact (conj H6 H7)]]]]].
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H2 fd' d' Hf).
    - intros d' Hd'. destruct (H3 d' Hd') as [(fd' & Hfd') | HD']; [| by right].
      destruct (decide (fd' = fd)) as [-> | Hne].
      + rewrite Hfd in Hfd'. injection Hfd' as <-.
        destruct Hsh as [HD | (fd'' & Hin & Hfd'')]; [by right | left].
        exists fd''. apply elem_of_dom in Hin as [d'' Hd'']. apply lookup_delete_Some in Hd'' as [Hne _].
        apply lookup_delete_Some. by split.
      + left. exists fd'. apply lookup_delete_Some. by split.
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H4 fd' d' Hf).
    - intros fa fb d' s' nm' i' γo' Ha Hb Hv.
      apply lookup_delete_Some in Ha as [_ Ha]. apply lookup_delete_Some in Hb as [_ Hb].
      exact (H5 fa fb d' s' nm' i' γo' Ha Hb Hv).
  Qed.
End cif_ok_lemmas.

(* the deed's content, read off the scope's files *)
Lemma cif_dst_some (s : dst) (content : list (bv 8)) :
  snd <$> s = Some content -> exists i : Z, s = Some (i, content).
Proof using . destruct s as [[i c] |]; simpl; [intros [= ->]; by exists i | discriminate]. Qed.

Lemma cif_dst_none (s : dst) : snd <$> s = None -> s = None.
Proof using . destruct s as [[i c] |]; simpl; [discriminate | reflexivity]. Qed.

(* a mode without O_CREATE, as the kernel reads it ([UkFileIface.fif_om_create]) *)
Lemma cif_om_create (m : Z) :
  ~ mode_create m -> SysOpenDefs.om_create (mword_of_int m : mword 64) = false.
Proof using .
  unfold mode_create, SysOpenDefs.om_create, om_arg. intros Hm.
  rewrite moi64_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_pow2_bits_low _ 32 9); [| lia].
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N 64) 9); [| lia].
  assert (Hl : Z.land m 512 = 0) by (destruct (Z.eq_dec (Z.land m 512) 0); [done | tauto]).
  pose proof (Z.land_spec m 512 9) as Hs. rewrite Hl Z.bits_0 in Hs.
  change (Z.testbit 512 9) with true in Hs. rewrite andb_true_r in Hs. by rewrite <- Hs.
Qed.

(* ===================================================================== *)
(*  1.  THE INSTANCE                                                      *)
(* ===================================================================== *)

Section UkCatFIface.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pipesNG Σ, !cifRegG Σ}.
  #[local] Existing Instance eo_turn | 0.

  (* THE FILE SIDE: the application's deed and credential names *)
  Context (cf : file_fixed) (rf : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred cf) rf).

  (* THE ROUND ([UkPipesIface]'s section context, name for name) *)
  Context (g : pipe_gn).
  Context (M : lmodel) (V : pview M) (G : gen_cparams M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Local Notation T := (gcT G).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV g M G sd WA).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Hypothesis Hsup : ⊢ □ (T -∗ app_sup).
  Context (v : era_pins) (I : list (bv 8)) (sR : lm_st M) (lR : pline').
  Hypothesis HlR : pv_line V (lineV M I) = Some lR.
  Hypothesis Hfc : fc_ok (pv_fc V sR).
  Context (Hadmit : pns_admV V lR) (Hplok : pl_ok lR).
  Context (L : list (bv 8)) (HL31 : pns_short L).
  Context (TERM : wid -> list (bv 8) -> bool)
          (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop).
  Context (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s)).
  Context (γc γm : wid -> gname).

  Local Notation wsN := (wids (lcats lR)).
  Local Notation RUNN := (runN (pv_fc V sR) lR).
  Local Notation PWN := (pwc_blkV g M (gcPIN G) (gcW G) T v I sR).
  Local Notation WITN := (pwitV M I sR).
  Local Notation FAM := (blkN_inv wsN RUNN PWN TERM TOK dep pnsN (S gen_id) γc γm).
  Local Notation PKIT := (pns_kit M V I sR lR TERM TOK dep).
  Local Notation PCON := (pns_con g M V G v I sR lR TERM TOK dep γc γm).
  Local Notation CSTEP := (cstep_okN wsN RUNN WITN TERM TOK).

  #[local] Instance cif_T_pers0 : Persistent T | 0 := gcT_pers G.
  #[local] Instance cif_T_tl0 : Timeless T | 0 := gcT_tl G.
  #[local] Instance cif_kit_pers0 w s : Persistent (PKIT w s) | 0 :=
    pns_kit_persistent M V I sR lR TERM TOK dep w s.

  (* ------------------------------------------------------------------- *)
  (*  1a. THE PRODUCER DEVICE'S CONSOLE HALF, at a failure report         *)
  (* ------------------------------------------------------------------- *)

  (* the family writer [w] FIRED at the report [x], at cursor [c] *)
  Definition cif_conF (w : wid) (x : list (bv 8)) (c : nat) (alts : list (list (bv 8)))
      : iProp Σ :=
    (⌜w ∈ wsN⌝ ∗ FAM
     ∗ ⌜((0 < c)%nat /\ (c <= length x)%nat) /\ alts = [drop c x] /\ cons_short alts⌝
     ∗ ⌜forall c', (0 < c' < length x)%nat -> CSTEP w x c'⌝
     ∗ wcurN γc w (1/2) c ∗ wmodeN γm w (1/2) (Some x))%I.

  (* ...or UNFIRED, owing exactly the report, its kit and deposit held *)
  Definition cif_conX (w : wid) (x : list (bv 8)) (alts : list (list (bv 8))) : iProp Σ :=
    ((⌜alts = [x] /\ cons_short [x] /\ w ∈ wsN⌝ ∗ FAM
      ∗ wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None ∗ PKIT w x ∗ dep w x)
     ∨ (∃ c : nat, cif_conF w x c alts))%I.

  Lemma cif_conX_short (w : wid) (x : list (bv 8)) (alts : list (list (bv 8))) :
    cif_conX w x alts -∗ ⌜cons_short alts⌝.
  Proof using .
    iIntros "[(%Hp & _) | (%c & _ & _ & %Hp & _)]".
    - destruct Hp as (-> & Hs & _). by iPureIntro.
    - destruct Hp as (_ & _ & Hs). by iPureIntro.
  Qed.

  Lemma cif_conX_sub (w : wid) (x : list (bv 8)) (alts : list (list (bv 8))) (a : list (bv 8)) :
    a ∈ alts -> cif_conX w x alts -∗ cif_conX w x [a].
  Proof using .
    intros Ha.
    iIntros "[(%Hp & #Hinv & Hc & Hm & #Hkit & Hdep) | (%c & %Hw & #Hinv & %Hp & %Hst & Hc & Hm)]".
    - destruct Hp as (-> & Hs & Hw). apply elem_of_list_singleton in Ha as ->.
      iLeft. iFrame "Hinv Hc Hm Hkit Hdep". iPureIntro. split_and!; done.
    - destruct Hp as ([Hc0 Hc1] & -> & Hs). apply elem_of_list_singleton in Ha as ->.
      iRight. iExists c. rewrite /cif_conF. iFrame "Hinv Hc Hm". iPureIntro. split_and!; done.
  Qed.

  Lemma cif_conX_step (w : wid) (x y : list (bv 8)) (b : bv 8) :
    y !! 0%nat = Some b ->
    cif_conX w x [y] -∗ out_link Uart0 (S gen_id) b (cif_conX w x [drop 1 y]).
  Proof using Hadmit Hcons Hext Hfc HlR Hplok dep_tl.
    intros Hb.
    iIntros "[(%Hp & #Hinv & Hc & Hm & #Hkit & Hdep) | (%c & %Hw & #Hinv & %Hp & %Hst & Hc & Hm)]".
    - destruct Hp as (Hy & Hs & Hw). injection Hy as <-.
      iApply (pns_fam_fire g M V G sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok
                TERM TOK dep dep_tl γc γm w y b with "Hkit Hinv Hc Hm Hdep");
        [exact Hw | exact Hb |].
      iIntros "Hc Hm". iRight. iExists 1%nat. iDestruct "Hkit" as "[_ %Hst]".
      rewrite /cif_conF. iFrame "Hinv Hc Hm". iPureIntro.
      pose proof (lookup_lt_Some _ _ _ Hb) as Hl.
      split_and!; [done | lia | lia | reflexivity | exact (pns_short_drop y 1 Hs) | exact Hst].
    - destruct Hp as ([Hc0 HcS] & Hy & Hs). injection Hy as ->.
      rewrite lookup_drop Nat.add_0_r in Hb.
      pose proof (lookup_lt_Some _ _ _ Hb) as Hl.
      iApply (pns_fam_cstep g M V G sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok
                TERM TOK dep dep_tl γc γm w x c b with "Hinv Hc Hm");
        [exact Hw | exact Hc0 | exact Hb | apply Hst; lia |].
      iIntros "Hc Hm". iRight. iExists (S c). rewrite /cif_conF. iFrame "Hinv Hc Hm". iPureIntro.
      assert (Hdd : drop 1 (drop c x) = drop (S c) x) by (rewrite drop_drop; f_equal; lia).
      pose proof (pns_short_drop (drop c x) 1 Hs) as Hs'.
      split_and!; [done | lia | lia | by rewrite Hdd | exact Hs' | exact Hst].
  Qed.

  (* after a nonempty write the report has fired *)
  Lemma cif_conX_fired (w : wid) (x y : list (bv 8)) :
    (length y < length x)%nat -> cif_conX w x [y] -∗ ∃ c, cif_conF w x c [y].
  Proof using .
    intros Hlt. iIntros "[((%Hy & _) & _) | H]"; [| iExact "H"].
    injection Hy as ->. lia.
  Qed.

  (* a drained fired report is its whole source *)
  Lemma cif_conF_final (w : wid) (x : list (bv 8)) (c : nat) (alts : list (list (bv 8))) :
    [] ∈ alts -> cif_conF w x c alts -∗ pns_wfin γc γm w (Some x).
  Proof using .
    intros Hn. iIntros "(_ & _ & %Hp & _ & Hc & Hm)".
    destruct Hp as ([_ HcS] & -> & _). apply elem_of_list_singleton in Hn.
    assert (c = length x) as ->.
    { symmetry in Hn. pose proof (pns_drop_nil_le x c Hn). lia. }
    cbn [pns_wfin]. iFrame "Hc Hm".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1b. THE PRODUCER DEVICE'S BODY                                      *)
  (* ------------------------------------------------------------------- *)

  (* nothing fired: the pipe's permit, the writer unfired, a kit and a
     deposit for each diagnostic of [ds], a kit and the deposit FROM THE
     PERMIT for each report of [xs] *)
  Definition cif_unf (pn : pnames) (w : wid) (A X : list (list (bv 8)))
      (ds xs : list (list (bv 8))) : iProp Σ :=
    (⌜w ∈ wsN⌝ ∗ FAM ∗ ⌜cons_short ds /\ cons_short xs⌝
     ∗ ⌜(forall a, a ∈ ds -> a ∈ A) /\ (forall x, x ∈ xs -> x ∈ X)⌝
     ∗ wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None
     ∗ ([∗ list] a ∈ ds, ⌜a = []⌝ ∨ (PKIT w a ∗ dep w a))
     ∗ ([∗ list] x ∈ xs, ⌜x = []⌝ ∨ (PKIT w x ∗ □ (wcur pn 0%nat -∗ dep w x))))%I.

  (* the four states: nothing fired; a diagnostic fired, the pipe
     untouched; the pipe fired; a report fired (the permit deposited) *)
  Definition cif_pbody (pn : pnames) (w : wid) (A X : list (list (bv 8)))
      (outs xs ds : list (list (bv 8))) : iProp Σ :=
    ((⌜outs = [L; []]⌝ ∗ wcur pn 0%nat ∗ pws_lb pn [] ∗ cif_unf pn w A X ds xs)
     ∨ (⌜xs = [] /\ outs = [L; []]⌝ ∗ wcur pn 0%nat ∗ pws_lb pn [] ∗ PCON w A ds)
     ∨ (⌜xs = []⌝ ∗ (∃ S : list (bv 8), ⌜outs = [S]⌝ ∗ pipe_out pn L S) ∗ PCON w A ds)
     ∨ (⌜xs = [] /\ outs = [[]]⌝ ∗ ∃ (x : list (bv 8)) (c : nat), ⌜x ∈ X⌝ ∗ cif_conF w x c ds))%I.

  (* the unfired console half, read as the landed writer's device *)
  Lemma cif_unf_con (pn : pnames) (w : wid) (A X ds xs : list (list (bv 8))) :
    cif_unf pn w A X ds xs -∗ PCON w A ds.
  Proof using .
    iIntros "(%Hw & #Hinv & [%Hs _] & [%HA _] & Hc & Hm & Hks & _)".
    iApply (pns_con_lend g M V G v I sR lR TERM TOK dep γc γm w A ds Hs Hw HA
              with "Hinv Hc Hm Hks").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1c. THE PROCESS, ITS REGISTRY AND ITS RESOURCES                     *)
  (* ------------------------------------------------------------------- *)

  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{HPc : !Persistent (up_code P)}.
  Context `{HNc : !ukn_const N}.
  Hypothesis Hsr : ⊢ stub_law N (up_code P) 5 (up_read P).
  Hypothesis Hsw : ⊢ stub_law N (up_code P) 16 (up_write P).
  Hypothesis Hso : ⊢ stub_law N (up_code P) 15 (up_open P).
  Hypothesis Hsc : ⊢ stub_law N (up_code P) 21 (up_close P).
  Hypothesis Hse : ⊢ exit_stub_law N (up_code P) (up_exit P).

  (* the registry's name, the protected devices (producer devices only),
     and the deed at its pinned fraction and content *)
  Context (γreg : gname).

  Local Notation γfd := (ukn_fd N).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  Definition cif_tok (d : nat) (q : Qp) (x : cfdev) : iProp Σ := own γreg (cif_single d q x).

  Lemma cif_tok_agree (d : nat) (q1 q2 : Qp) (x1 x2 : cfdev) :
    cif_tok d q1 x1 -∗ cif_tok d q2 x2 -∗ ⌜x1 = x2⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite /cif_single discrete_fun_singleton_op discrete_fun_singleton_valid
      -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    by destruct Hv as [_ ?].
  Qed.

  Lemma cif_tok_halves (d : nat) (x : cfdev) :
    cif_tok d 1 x ⊣⊢ cif_tok d (1/2) x ∗ cif_tok d (1/2) x.
  Proof using .
    rewrite /cif_tok -own_op /cif_single. f_equiv.
    rewrite (discrete_fun_singleton_op d). f_equiv.
    rewrite -Some_op /to_dfrac_agree -pair_op agree_idemp dfrac_op_own Qp.half_half //.
  Qed.

  Lemma cif_pool_own_take (B : gset nat) (wv : nat -> cfdev) (d : nat) :
    d ∉ B -> own γreg (cif_pool B wv) ⊣⊢ own γreg (cif_pool ({[d]} ∪ B) wv) ∗ cif_tok d 1 (wv d).
  Proof using . intros Hd. rewrite /cif_tok -own_op -cif_pool_take //. Qed.

  Lemma cif_pool_give (vs : gmap nat cfdev) (wv : nat -> cfdev) (d : nat) (x : cfdev) :
    d ∈ dom vs ->
    own γreg (cif_pool (dom vs) wv) -∗ cif_tok d 1 x -∗
    own γreg (cif_pool (dom (delete d vs)) (fun y => if decide (y = d) then x else wv y)).
  Proof using .
    iIntros (Hd) "Hp Ht".
    set (w' := fun y => if decide (y = d) then x else wv y).
    assert (Hw' : w' d = x) by (rewrite /w'; by case_decide).
    rewrite (cif_pool_own_take (dom (delete d vs)) w' d); [| rewrite dom_delete_L; set_solver].
    rewrite Hw'. iFrame "Ht".
    assert (HB : dom vs = {[d]} ∪ dom (delete d vs)).
    { rewrite dom_delete_L. apply set_eq. intros y. rewrite elem_of_union elem_of_singleton
        elem_of_difference elem_of_singleton. split; [| intros [-> | []]; done].
      intros Hy. destruct (decide (y = d)); [by left | by right]. }
    assert (Hww : forall y, y ∉ dom vs -> wv y = w' y).
    { intros y Hy. unfold w'. case_decide as Hyd; [| done]. subst y. done. }
    rewrite (cif_pool_ext (dom vs) ({[d]} ∪ dom (delete d vs)) wv w' HB Hww). done.
  Qed.

  Lemma cif_toks_agree (vs : gmap nat cfdev) (d : nat) (x x' : cfdev) (q : Qp) :
    vs !! d = Some x ->
    ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x) -∗ cif_tok d q x' -∗
    ⌜x = x'⌝ ∗ ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x) ∗ cif_tok d q x'.
  Proof using .
    iIntros (Hv) "Hm Ht".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hv with "Hm") as "[Hx Hcl]".
    iDestruct (cif_tok_agree with "Hx Ht") as %->.
    iFrame "Ht". iSplit; [done |]. iApply ("Hcl" with "Hx").
  Qed.

  Context (kds : list (nat * cfdev)).
  Hypothesis Hkds : stdpp.base.NoDup kds.*1.
  Hypothesis Hkdp : forall dk, dk ∈ kds -> exists pn gp w A X, dk.2 = UDProd pn gp w A X.
  Context (qf : Qp) (sf : dst).
  Local Notation Dp := (kds.*1).

  (* the handle an input's TAIL descriptor holds *)
  Definition cif_hdl (fd : Z) (ov : option cfdev) : iProp Σ :=
    match ov with
    | Some (UDIn false _ i γo) =>
        UserFd.ufd γfd (Z.to_nat fd) (FdOpen true false (FdInode i γo OffHeld))
    | _ => emp
    end%I.

  (* the persistent context: the file's taint wands, the image's
     invariant, the read leaves' credential, the producer's pipe *)
  Definition cif_pk_inv (kd : cfdev) : iProp Σ :=
    match kd with
    | UDIn _ _ _ _ => True
    | UDProd pn gp _ _ _ => pipe_inv pn gp L
    end%I.

  Global Instance cif_pk_inv_persistent kd : Persistent (cif_pk_inv kd).
  Proof using . destruct kd; cbn [cif_pk_inv]; apply _. Qed.

  Definition cif_env (vs : gmap nat cfdev) : iProp Σ :=
    (□ (app_taint -∗ file_taint cf) ∗ □ (file_taint cf -∗ app_taint)
     ∗ app_inv fsc_fs ∗ (∃ jo : option Z, file_cons_cred cf rf jo)
     ∗ [∗ map] d ↦ kd ∈ vs, cif_pk_inv kd)%I.

  Global Instance cif_env_persistent vs : Persistent (cif_env vs).
  Proof using . rewrite /cif_env. apply _. Qed.

  Lemma cif_env_lookup (vs : gmap nat cfdev) (d : nat) (kd : cfdev) :
    vs !! d = Some kd -> cif_env vs -∗ cif_pk_inv kd.
  Proof using .
    intros Hv. iIntros "(_ & _ & _ & _ & Hm)". iApply (big_sepM_lookup with "Hm"). exact Hv.
  Qed.

  Lemma cif_env_delete (vs : gmap nat cfdev) (d : nat) :
    cif_env vs -∗ cif_env (delete d vs).
  Proof using .
    iIntros "(#H1 & #H2 & #H3 & #H4 & #Hm)". iFrame "H1 H2 H3 H4".
    destruct (vs !! d) as [kd |] eqn:Hv.
    - iDestruct (big_sepM_delete with "Hm") as "[_ $]". exact Hv.
    - rewrite delete_notin; [iExact "Hm" | exact Hv].
  Qed.

  Lemma cif_env_insert (vs : gmap nat cfdev) (d : nat) (kd : cfdev) :
    vs !! d = None -> cif_env vs -∗ cif_pk_inv kd -∗ cif_env (<[d := kd]> vs).
  Proof using .
    iIntros (Hv) "(#H1 & #H2 & #H3 & #H4 & #Hm) #Hk". iFrame "H1 H2 H3 H4".
    rewrite big_sepM_insert; [| exact Hv]. iFrame "Hk Hm".
  Qed.

  (* the file's taint is the round's *)
  Lemma cif_T_of_file (vs : gmap nat cfdev) : file_taint cf -∗ cif_env vs -∗ T.
  Proof using Hkill.
    iIntros "#Ht (_ & #H2 & _)". rewrite -Hkill. iApply ("H2" with "Ht").
  Qed.

  (* ---- THE FINAL STATES, and the exit wand ---- *)
  Definition cif_final (kd : cfdev) : iProp Σ :=
    match kd with
    | UDIn _ _ _ _ => True
    | UDProd pn _ w A X =>
        ((pns_lexit L pn ∨ wcur pn 0%nat) ∗ pns_con_final γc γm w A)
        ∨ (∃ x, ⌜x ∈ X⌝ ∗ pns_wfin γc γm w (Some x))
    end%I.

  Definition cif_xkQ (kl : list (nat * cfdev)) (Q : Z -> iProp Σ) : iProp Σ :=
    ((T ∨ (([∗ list] dk ∈ kl, cif_final dk.2) ∗ fdq rf qf sf)) -∗ Q (-1))%I.

  Definition cif_xk : iProp Σ := cif_xkQ kds (ukn_pay N).

  (* ---- [ei_fds] ---- *)
  Definition cif_fds_at (fdm : fdmap) (l : list fdstate) (vs : gmap nat cfdev)
      (wv : nat -> cfdev) : iProp Σ :=
    (UserFd.ustd γfd l ∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO
     ∗ ⌜cif_ok kds fdm l vs⌝
     ∗ own γreg (cif_pool (dom vs) wv)
     ∗ ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x)
     ∗ ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d))
     ∗ fdq rf qf sf ∗ cif_env vs ∗ cif_xk)%I.

  Definition cif_fds (fdm : fdmap) : iProp Σ :=
    (∃ (l : list fdstate) (vs : gmap nat cfdev) (wv : nat -> cfdev), cif_fds_at fdm l vs wv)%I.

  Lemma cif_fds_of (fdm : fdmap) (l : list fdstate) (vs : gmap nat cfdev) (wv : nat -> cfdev) :
    cif_ok kds fdm l vs ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
    own γreg (cif_pool (dom vs) wv) -∗ ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x) -∗
    ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d)) -∗ fdq rf qf sf -∗ cif_env vs -∗
    cif_xk -∗ cif_fds fdm.
  Proof using .
    intros Hok. iIntros "Hstd Hcwd Hpool Htoks Hhs Hdq #He Hk".
    iExists l, vs, wv. iFrame "Hk Hstd Hcwd Hpool Htoks Hhs Hdq He". by iPureIntro.
  Qed.

  (* ---- the devices ---- *)
  Definition cif_in (d : nat) (S : list (bv 8)) : iProp Σ :=
    (∃ (s : bool) (nm : list (bv 8)) (i : Z) (γo : gname) (p : nat),
       cif_tok d (1/2) (UDIn s nm i γo)
       ∗ ⌜exists content, sf = Some (i, content) /\ S = drop p content⌝
       ∗ uoff γo p)%I.

  Definition cif_prod (d : nat) (outs xs ds : list (list (bv 8))) : iProp Σ :=
    (∃ (pn : pnames) (gp : pipe_names) (w : wid) (A X : list (list (bv 8))),
       cif_tok d (1/2) (UDProd pn gp w A X) ∗ cif_pbody pn w A X outs xs ds)%I.

  Definition cif_prod_halt (d : nat) (ds : list (list (bv 8))) : iProp Σ :=
    (∃ (pn : pnames) (gp : pipe_names) (w : wid) (A X : list (list (bv 8))),
       cif_tok d (1/2) (UDProd pn gp w A X) ∗ pipe_halt pn ∗ PCON w A ds)%I.

  Definition cif_dev (d : nat) (x : dspec) : iProp Σ :=
    match x with
    | DIn Sin => cif_in d Sin
    | DProd outs xs ds => cif_prod d outs xs ds
    | DProdHalt ds => cif_prod_halt d ds
    | _ => False
    end%I.

  (* THE SCOPE (seam (c)): the described paths are user files, and the
     files are the deed's *)
  Definition cif_filesr (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) : iProp Σ :=
    (⌜forall p, p ∈ paths -> uname p⌝ ∗ ⌜files fname_f = snd <$> sf⌝)%I.

  Global Instance cif_filesr_persistent files paths : Persistent (cif_filesr files paths).
  Proof using . rewrite /cif_filesr. apply _. Qed.

  Definition cif_taint (held : gset Z) : iProp Σ := fh_taint T N held.

  (* ------------------------------------------------------------------- *)
  (*  1d. SMALL FACTS                                                     *)
  (* ------------------------------------------------------------------- *)

  Definition cif_hf (vs : gmap nat cfdev) (d : nat) : option fdstate :=
    match vs !! d with
    | Some (UDIn false _ i γo) => Some (FdOpen true false (FdInode i γo OffHeld))
    | _ => None
    end.

  Lemma cif_hdls_hm (fdm : fdmap) (vs : gmap nat cfdev) :
    ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d))
    ⊣⊢ [∗ map] fd ↦ st ∈ omap (cif_hf vs) fdm, UserFd.ufd γfd (Z.to_nat fd) st.
  Proof using .
    rewrite big_sepM_omap. apply big_sepM_proper. intros fd d _.
    rewrite /cif_hdl /cif_hf. destruct (vs !! d) as [[[|] nm i γo | pn gp w A X] |]; done.
  Qed.

  Lemma cif_held_ok_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat cfdev) :
    cif_ok kds fdm l vs -> fh_held_ok (dom fdm) l (omap (cif_hf vs) fdm).
  Proof using L TERM dep γc γm.
    intros Hok fd Hfd. apply elem_of_dom in Hfd as [d Hd].
    pose proof Hok as (H1 & H2 & _). split; [exact (H1 fd d Hd) |].
    pose proof (H2 fd d Hd) as Hr.
    destruct (vs !! d) as [[[|] nm i γo | pn gp w A X] |] eqn:Ev; simpl in Hr.
    - left. destruct Hr as (Hs & Hl). split; [exact Hs |].
      eexists; split; [exact Hl | discriminate].
    - right. split; [exact Hr |]. rewrite lookup_omap Hd /= /cif_hf Ev. by eexists.
    - left. destruct Hr as [(-> & rb & Hl) | (-> & rb & Hl)];
        (split; [cbv [prod_out prod_err NSTD]; lia |]); eexists;
        (split; [exact Hl | discriminate]).
    - done.
  Qed.

  (* THE TAINT, out of what a law holds at a taint arm *)
  Lemma cif_taint_of_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat cfdev) :
    cif_ok kds fdm l vs ->
    T -∗ UserFd.ustd γfd l -∗ ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d)) -∗
    cif_xk -∗ cif_taint (dom fdm).
  Proof using Hkill Hsup TERM dep.
    intros Hok. iIntros "#Ht Hstd Hhs Hxk". rewrite /cif_taint /fh_taint.
    iDestruct ("Hxk" with "[]") as "Hpay"; [by iLeft |].
    iFrame "Ht Hpay". iSplitR; [iIntros "!> HT"; by rewrite Hkill |].
    iSplitR; [iApply Hsup |].
    iExists l, (omap (cif_hf vs) fdm). iFrame "Hstd". iSplit.
    - iPureIntro. by apply cif_held_ok_fds.
    - by rewrite cif_hdls_hm.
  Qed.

  Lemma cif_taint_pays (held : gset Z) (t : proc) :
    safe_fds held t -> cif_taint held -∗ tree_pay N P t.
  Proof using HNc Hsc Hse Hso Hsr Hsw.
    exact (fh_taint_pays T N P Hsr Hsw Hso Hsc Hse held t).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1e. THE PRODUCER DEVICE'S LAWS                                      *)
  (* ------------------------------------------------------------------- *)

  Local Ltac cif_repack :=
    iApply (cif_fds_of with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hxk"); assumption.

  (* the producer's two rows *)
  Lemma cif_prod_row_out (l : list fdstate) (pn : pnames) (gp : pipe_names) (w : wid)
      (A X : list (list (bv 8))) (fd : Z) :
    cif_row (Some (UDProd pn gp w A X)) fd l -> fd = prod_out ->
    exists rb, l !! 1%nat = Some (FdOpen rb true (FdPipe gp)).
  Proof using L TERM dep γc γm.
    intros [(_ & H) | (-> & _)] Hf; [exact H | cbv [prod_out prod_err] in Hf; lia].
  Qed.

  Lemma cif_prod_row_err (l : list fdstate) (pn : pnames) (gp : pipe_names) (w : wid)
      (A X : list (list (bv 8))) (fd : Z) :
    cif_row (Some (UDProd pn gp w A X)) fd l -> fd = prod_err ->
    exists rb, l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)).
  Proof using L TERM dep γc γm.
    intros [(-> & _) | (_ & H)] Hf; [cbv [prod_out prod_err] in Hf; lia | exact H].
  Qed.

  Lemma cif_conF_shape (w : wid) (x : list (bv 8)) (c : nat) (alts : list (list (bv 8))) :
    cif_conF w x c alts -∗ ⌜alts = [drop c x] /\ (0 < c)%nat⌝.
  Proof using . iIntros "(_ & _ & %Hp & _)". iPureIntro. destruct Hp as ([? _] & ? & _). done. Qed.

  Lemma cif_conF_X (w : wid) (x : list (bv 8)) (c : nat) (alts : list (list (bv 8))) :
    cif_conF w x c alts -∗ cif_conX w x alts.
  Proof using . iIntros "H". iRight. iExists c. iExact "H". Qed.

  (* an output write: the pipe's write, the console half kept *)
  Lemma cif_write_prod (fdm : fdmap) (fd : Z) (d : nat) (outs xs ds : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = prod_out -> a ∈ outs -> bs `prefix_of` a ->
    cif_fds fdm -∗ cif_prod d outs xs ds -∗
    ((cif_fds fdm -∗ cif_prod d [drop (length bs) a] [] ds -∗ K (Z.of_nat (length bs)))
     ∧ (cif_fds fdm -∗ cif_prod_halt d ds -∗ K (-1))
     ∧ (∀ x, cif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HL31 Hkill Hsup Hsw.
    intros Hne Hfd Hfo Ha Hpre. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pn gp w A X) "[Htk Hb]".
    iAssert (∃ S, ⌜a ∈ [S]⌝ ∗ pipe_out pn L S ∗ PCON w A ds)%I with "[Hb]"
      as (S) "(%Ha1 & Hpo & Hcon)".
    { iDestruct "Hb" as "[(-> & Hw & #Hlb & Hu) | [(%Hp & Hw & #Hlb & Hcon)
                        | [(%Hp & (%S & -> & Hpo) & Hcon) | (%Hp & _)]]]".
      - iExists L. iSplitR.
        { iPureIntro. apply elem_of_cons in Ha as [-> | Ha]; [by left |].
          apply elem_of_list_singleton in Ha as ->. exfalso. apply Hne. by apply prefix_nil_inv. }
        iSplitL "Hw"; [| iApply (cif_unf_con with "Hu")].
        rewrite /pipe_out. iExists 0%nat. rewrite drop_0 take_0. iFrame "Hw Hlb".
        iPureIntro. split; [reflexivity | exact HL31].
      - destruct Hp as [_ ->]. iExists L. iSplitR.
        { iPureIntro. apply elem_of_cons in Ha as [-> | Ha]; [by left |].
          apply elem_of_list_singleton in Ha as ->. exfalso. apply Hne. by apply prefix_nil_inv. }
        iFrame "Hcon". rewrite /pipe_out. iExists 0%nat. rewrite drop_0 take_0. iFrame "Hw Hlb".
        iPureIntro. split; [reflexivity | exact HL31].
      - iExists S. iFrame "Hpo Hcon". by iPureIntro.
      - destruct Hp as [_ ->]. apply elem_of_list_singleton in Ha as ->.
        exfalso. apply Hne. by apply prefix_nil_inv. }
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    pose proof Hok as (_ & H2 & _). pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (cif_prod_row_out l pn gp w A X fd Hrow Hfo) as [rb Hrow1].
    iPoseProof (cif_env_lookup vs d _ Hv with "He") as "#Hinv". cbn [cif_pk_inv].
    subst fd. change prod_out with (Z.of_nat 1%nat).
    iApply (pipe_write N P Hsw pn gp L S l 1 rb a bs K ltac:(unfold NSTD; lia) Hrow1 Ha1 Hpre Hne
              with "Hinv Hstd Hpo").
    iSplit; [| iSplit].
    - iIntros "Hstd Hpo". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hpo Htk Hcon] [Htk Hpo Hcon]"); [cif_repack |].
      iExists pn, gp, w, A, X. iFrame "Htk". iRight. iRight. iLeft.
      iSplitR; [done |]. iFrame "Hcon". iExists (drop (length bs) a). iFrame "Hpo". by iPureIntro.
    - iIntros "Hstd Hh". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Hh Htk Hcon] [Htk Hh Hcon]"); [cif_repack |].
      iExists pn, gp, w, A, X. iFrame "Htk Hh Hcon".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (cif_taint_of_fds fdm l vs Hok with "[] Hstd Hhs Hxk"). by rewrite -Hkill.
  Qed.

  (* ...at the halted output *)
  Lemma cif_write_prod_halt (fdm : fdmap) (fd : Z) (d : nat) (ds : list (list (bv 8)))
      (bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fdm !! fd = Some d -> fd = prod_out ->
    cif_fds fdm -∗ cif_prod_halt d ds -∗
    ((cif_fds fdm -∗ cif_prod_halt d ds -∗ K (-1)) ∧ (∀ x, cif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hkill Hsup Hsw.
    intros Hne Hbnd Hfd Hfo. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pn gp w A X) "(Htk & Hh & Hcon)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    pose proof Hok as (_ & H2 & _). pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (cif_prod_row_out l pn gp w A X fd Hrow Hfo) as [rb Hrow1].
    iPoseProof (cif_env_lookup vs d _ Hv with "He") as "#Hinv". cbn [cif_pk_inv].
    subst fd. change prod_out with (Z.of_nat 1%nat).
    iApply (pipe_write_halt N P Hsw pn gp L l 1 rb bs K ltac:(unfold NSTD; lia) Hrow1 Hne Hbnd
              with "Hinv Hstd Hh").
    iSplit.
    - iIntros "Hstd Hh". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hh Htk Hcon] [Htk Hh Hcon]"); [cif_repack |].
      iExists pn, gp, w, A, X. iFrame "Htk Hh Hcon".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (cif_taint_of_fds fdm l vs Hok with "[] Hstd Hhs Hxk"). by rewrite -Hkill.
  Qed.

  Local Notation PCSHORT w A := (pns_con_short g M V G v I sR lR TERM TOK dep γc γm w A).
  Local Notation PCSUB w A := (pns_con_sub g M V G v I sR lR TERM TOK dep γc γm w A).
  Local Notation PCSTEP w A :=
    (pns_con_step g M V G sd WA Hext Hcons v I sR lR HlR Hfc Hadmit Hplok TERM TOK dep dep_tl γc γm w A).

  (* a diagnostic write: the console's write at the writer's device *)
  Lemma cif_write_prod_err (fdm : fdmap) (fd : Z) (d : nat) (outs xs ds : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = prod_err -> a ∈ ds -> bs `prefix_of` a ->
    cif_fds fdm -∗ cif_prod d outs xs ds -∗
    ((cif_fds fdm -∗ cif_prod d outs [] [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, cif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HPc Hadmit Hcons Hext Hfc HlR Hplok Hsw dep_tl.
    intros Hne Hfd Hfe Ha Hpre. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pn gp w A X) "[Htk Hb]".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    pose proof Hok as (_ & H2 & _). pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (cif_prod_row_err l pn gp w A X fd Hrow Hfe) as [rb Hrow2].
    subst fd. change prod_err with (Z.of_nat 2%nat).
    iDestruct "HK" as "[HK _]".
    iDestruct "Hb" as "[(-> & Hw & #Hlb & Hu) | [(%Hp & Hw & #Hlb & Hcon)
                        | [(%Hp & Hpo & Hcon) | (%Hp & %x & %c & %HxX & Hcf)]]]".
    - iDestruct (cif_unf_con with "Hu") as "Hcon".
      iApply (cons_write N P (HPc := HPc) Hsw (PCON w A) (PCSHORT w A) (PCSUB w A) (PCSTEP w A)
                l 2 rb ds a bs K ltac:(unfold NSTD; lia) Hrow2 Ha Hpre with "Hstd Hcon").
      iIntros "Hstd Hcon".
      iApply ("HK" with "[-Htk Hw Hcon] [Htk Hw Hcon]"); [cif_repack |].
      iExists pn, gp, w, A, X. iFrame "Htk". iRight. iLeft. iFrame "Hw Hlb Hcon". by iPureIntro.
    - destruct Hp as [-> ->].
      iApply (cons_write N P (HPc := HPc) Hsw (PCON w A) (PCSHORT w A) (PCSUB w A) (PCSTEP w A)
                l 2 rb ds a bs K ltac:(unfold NSTD; lia) Hrow2 Ha Hpre with "Hstd Hcon").
      iIntros "Hstd Hcon".
      iApply ("HK" with "[-Htk Hw Hcon] [Htk Hw Hcon]"); [cif_repack |].
      iExists pn, gp, w, A, X. iFrame "Htk". iRight. iLeft. iFrame "Hw Hlb Hcon". by iPureIntro.
    - iApply (cons_write N P (HPc := HPc) Hsw (PCON w A) (PCSHORT w A) (PCSUB w A) (PCSTEP w A)
                l 2 rb ds a bs K ltac:(unfold NSTD; lia) Hrow2 Ha Hpre with "Hstd Hcon").
      iIntros "Hstd Hcon".
      iApply ("HK" with "[-Htk Hpo Hcon] [Htk Hpo Hcon]"); [cif_repack |].
      iExists pn, gp, w, A, X. iFrame "Htk". iRight. iRight. iLeft. iFrame "Hpo Hcon". by iPureIntro.
    - destruct Hp as [-> ->].
      iDestruct (cif_conF_shape with "Hcf") as %[Hds Hc0]. subst ds.
      apply elem_of_list_singleton in Ha as ->.
      iDestruct (cif_conF_X with "Hcf") as "Hcx".
      iApply (cons_write N P (HPc := HPc) Hsw (cif_conX w x) (cif_conX_short w x)
                (cif_conX_sub w x) (cif_conX_step w x)
                l 2 rb [drop c x] (drop c x) bs K ltac:(unfold NSTD; lia) Hrow2
                ltac:(by left) Hpre with "Hstd Hcx").
      iIntros "Hstd Hcx".
      iDestruct (cif_conX_fired w x (drop (length bs) (drop c x)) with "Hcx") as (c') "Hcf".
      { rewrite !length_drop. destruct bs; [done |]. cbn [length].
        pose proof (prefix_length _ _ Hpre) as Hl. rewrite length_drop in Hl. cbn [length] in Hl. lia. }
      iApply ("HK" with "[-Htk Hcf] [Htk Hcf]"); [cif_repack |].
      iExists pn, gp, w, A, X. iFrame "Htk". iRight. iRight. iRight.
      iSplitR; [by iPureIntro |]. iExists x, c'. iFrame "Hcf". by iPureIntro.
  Qed.

  (* a FAILURE REPORT: the permit spent into the report's deposit, the pipe
     then owing nothing *)
  Lemma cif_write_prod_fail (fdm : fdmap) (fd : Z) (d : nat) (outs xs ds : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = prod_err -> [] ∈ outs -> a ∈ xs ->
    bs `prefix_of` a ->
    cif_fds fdm -∗ cif_prod d outs xs ds -∗
    ((cif_fds fdm -∗ cif_prod d [[]] [] [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, cif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HPc Hadmit Hcons Hext Hfc HlR Hplok Hsw dep_tl.
    intros Hne Hfd Hfe Hon Ha Hpre. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pn gp w A X) "[Htk Hb]".
    iDestruct "Hb" as "[(-> & Hw & #Hlb & Hu) | [(%Hp & _) | [(%Hp & _) | (%Hp & _)]]]";
      [| destruct Hp as [-> _]; by apply elem_of_nil in Ha
       | subst xs; by apply elem_of_nil in Ha
       | destruct Hp as [-> _]; by apply elem_of_nil in Ha].
    iDestruct "Hu" as "(%Hw0 & #Hinv & [%Hsd %Hsx] & [%HA %HX] & Hc & Hm & _ & Hxs)".
    destruct (elem_of_list_lookup_1 xs a Ha) as [j Hj].
    iDestruct (big_sepL_lookup_acc _ _ j a Hj with "Hxs") as "[Hx _]".
    iDestruct "Hx" as "[%Hnil | [#Hkit #Hdw]]".
    { subst a. exfalso. apply Hne. by apply prefix_nil_inv. }
    iDestruct ("Hdw" with "Hw") as "Hdep".
    assert (Hsa : cons_short [a]).
    { rewrite /cons_short Forall_singleton. exact (Forall_lookup_1 _ _ _ _ Hsx Hj). }
    iAssert (cif_conX w a [a]) with "[Hc Hm Hdep]" as "Hcx".
    { iLeft. iFrame "Hinv Hc Hm Hkit Hdep". iPureIntro. split_and!; done. }
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    pose proof Hok as (_ & H2 & _). pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (cif_prod_row_err l pn gp w A X fd Hrow Hfe) as [rb Hrow2].
    subst fd. change prod_err with (Z.of_nat 2%nat).
    iDestruct "HK" as "[HK _]".
    iApply (cons_write N P (HPc := HPc) Hsw (cif_conX w a) (cif_conX_short w a)
              (cif_conX_sub w a) (cif_conX_step w a)
              l 2 rb [a] a bs K ltac:(unfold NSTD; lia) Hrow2 ltac:(by left) Hpre
              with "Hstd Hcx").
    iIntros "Hstd Hcx".
    iDestruct (cif_conX_fired w a (drop (length bs) a) with "Hcx") as (c') "Hcf".
    { rewrite length_drop. destruct bs as [| b0 bs']; [done |].
      pose proof (prefix_length _ _ Hpre) as Hl. cbn [length] in Hl |- *. lia. }
    iApply ("HK" with "[-Htk Hcf] [Htk Hcf]"); [cif_repack |].
    iExists pn, gp, w, A, X. iFrame "Htk". iRight. iRight. iRight.
    iSplitR; [by iPureIntro |]. iExists a, c'. iFrame "Hcf". iPureIntro. by apply HX.
  Qed.

  (* a diagnostic at the halted output *)
  Lemma cif_write_prod_halt_err (fdm : fdmap) (fd : Z) (d : nat) (ds : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = prod_err -> a ∈ ds -> bs `prefix_of` a ->
    cif_fds fdm -∗ cif_prod_halt d ds -∗
    ((cif_fds fdm -∗ cif_prod_halt d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, cif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HPc Hadmit Hcons Hext Hfc HlR Hplok Hsw dep_tl.
    intros Hne Hfd Hfe Ha Hpre. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pn gp w A X) "(Htk & Hh & Hcon)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    pose proof Hok as (_ & H2 & _). pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (cif_prod_row_err l pn gp w A X fd Hrow Hfe) as [rb Hrow2].
    subst fd. change prod_err with (Z.of_nat 2%nat).
    iDestruct "HK" as "[HK _]".
    iApply (cons_write N P (HPc := HPc) Hsw (PCON w A) (PCSHORT w A) (PCSUB w A) (PCSTEP w A)
              l 2 rb ds a bs K ltac:(unfold NSTD; lia) Hrow2 Ha Hpre with "Hstd Hcon").
    iIntros "Hstd Hcon".
    iApply ("HK" with "[-Htk Hh Hcon] [Htk Hh Hcon]"); [cif_repack |].
    iExists pn, gp, w, A, X. iFrame "Htk Hh Hcon".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1f. THE ZERO-LENGTH WRITE, THE INPUT, THE OPEN                      *)
  (* ------------------------------------------------------------------- *)

  (* the token of a device, whatever its state *)
  Lemma cif_dev_tok (d : nat) (x : dspec) :
    cif_dev d x -∗ ∃ kd : cfdev, cif_tok d (1/2) kd ∗ (cif_tok d (1/2) kd -∗ cif_dev d x).
  Proof using .
    destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p | | outs xs ds | ds];
      cbn [cif_dev]; try (iIntros "[]").
    - iIntros "(%s & %nm & %i & %γo & %p & Htk & Hr)". iExists (UDIn s nm i γo). iFrame "Htk".
      iIntros "Htk". iExists s, nm, i, γo, p. iFrame "Htk Hr".
    - iIntros "(%pn & %gp & %w & %A & %X & Htk & Hr)". iExists (UDProd pn gp w A X).
      iFrame "Htk". iIntros "Htk". iExists pn, gp, w, A, X. iFrame "Htk Hr".
    - iIntros "(%pn & %gp & %w & %A & %X & Htk & Hr)". iExists (UDProd pn gp w A X).
      iFrame "Htk". iIntros "Htk". iExists pn, gp, w, A, X. iFrame "Htk Hr".
  Qed.

  (* a ZERO-LENGTH write at a console row, at any device resource
     ([UkPipesIface.pns_cons_nil], verbatim) *)
  Lemma cif_cons_nil (l : list fdstate) (fd : nat) (rb : bool) (R : iProp Σ)
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ R -∗ (UserFd.ustd γfd l -∗ R -∗ K 0) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using HPc Hsw L TERM dep.
    intros Hfd Hlk. iIntros "Hstd Hd HK".
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 #Hcode Hsrc Hrun Hcont".
    cbn [length] in *.
    iEval (rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx)) 0 f
                      (or_introl eq_refl))) in "Hsrc".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Ham0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _ ltac:(vm_compute; discriminate)).
    assert (Ham1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _ ltac:(vm_compute; discriminate)).
    assert (Ham2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _ ltac:(vm_compute; discriminate)).
    assert (Hi0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd)
      by (rewrite Ham0; exact Ha0).
    assert (Hcz : sys_rw_count (mword_of_int (Z.of_nat 0) : mword 64) = Z.of_nat 0)
      by (apply cons_count_is; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count (m1 !!! Regidx a2_idx)) = 0%nat)
      by (rewrite Ham2 Ha2 Hcz; lia).
    assert (Hsys : usysno m1 = 16).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute. reflexivity. }
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Hal6 Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr
                    (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4)) 2
                  = true) by (rewrite E6; exact Hal6).
    unfold stub_ret.
    iApply (cons_leaf N h1 m1 _ avail
              (xfam_wr (fun _ : nat => (R ∗ emp)%I) (ukn_pay N))
              l tx dq 0 f Hsys Hal with "Hec Hrun [Hd] Hstd [Hsrc]").
    { iApply (uwrite_chain_sup_ret N (fun _ : nat => R) emp%I _ _ l fd rb CONSOLE Hi0 Hfd Hlk).
      iIntros (Mh pm sz) "Hheap". iFrame "Hheap". iSplitR; [done |].
      rewrite Hcnt. cbn [cons_out_chain]. iExact "Hd". }
    { rewrite Ham1. iExact "Hsrc". }
    iIntros (h' ret Wv cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun _ : nat => (R ∗ emp)%I)
                 (ukn_pay N) Wv ret (uvis_M Wv) (uvis_fd Wv) cw' cs'
                 l fd rb 0
                 ltac:(rewrite Hka0; exact Hi0)
                 Hfd Htk Hlk
                 ltac:(rewrite Hka2 Ham2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hret [Hd _]]".
    rewrite Ham1 E6.
    iApply ("Hret" $! h' ret with "Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[HK Hstd Hd] [Hs1] Hrun").
    - rewrite Hret. change (bv_signed (mword_of_int (Z.of_nat 0) : mword 64)) with 0.
      iApply ("HK" with "Hstd Hd").
    - rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx)) 0 f
                 (or_introl eq_refl)).
      iExact "Hs1".
  Qed.

  (* [ei_write_nil]: by the row the device's kind demands *)
  Lemma cif_write_nil (fdm : fdmap) (fd : Z) (d : nat) (x : dspec) (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    cif_fds fdm -∗ cif_dev d x -∗
    ((cif_fds fdm -∗ cif_dev d x -∗ K 0) ∧ (cif_fds fdm -∗ cif_dev d x -∗ K (-1))
     ∧ (∀ y, cif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.
  Proof using HPc Hkill Hsup Hsw.
    intros Hfd. iIntros "Hfds Hd HK".
    iDestruct (cif_dev_tok with "Hd") as (kd) "(Htk & Hback)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd' Hv].
    iDestruct (cif_toks_agree vs d kd' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd'.
    iDestruct ("Hback" with "Htk") as "Hd".
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (Z_of_nat_complete fd H0) as [k ->].
    destruct kd as [[|] nm i γo | pn gp w A X]; cbn [cif_row] in Hrow.
    - destruct Hrow as (Hs & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_write_nil_std_ro N P Hsw k l true (FdInode i γo OffHeld) K
                ltac:(unfold NSTD in *; lia) Hrow with "Hstd").
      iSplit; iIntros "Hstd".
      + iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hd] Hd"). cif_repack.
      + iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hd] Hd"). cif_repack.
    - iDestruct (big_sepM_lookup_acc _ _ _ _ Hfd with "Hhs") as "[Hh Hcl]".
      iEval (rewrite /cif_hdl Hv) in "Hh". iEval (rewrite Nat2Z.id) in "Hh".
      iApply (file_write_nil_hdl_ro N P Hsw k true (FdInode i γo OffHeld) K
                ltac:(lia) with "Hh").
      iSplit; iIntros "Hh".
      + iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hd] Hd").
        iApply (cif_fds_of with "Hstd Hcwd Hpool Htoks [Hh Hcl] Hdq He Hxk"); [exact Hok |].
        iApply "Hcl". rewrite /cif_hdl Hv Nat2Z.id. iExact "Hh".
      + iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hd] Hd").
        iApply (cif_fds_of with "Hstd Hcwd Hpool Htoks [Hh Hcl] Hdq He Hxk"); [exact Hok |].
        iApply "Hcl". rewrite /cif_hdl Hv Nat2Z.id. iExact "Hh".
    - destruct Hrow as [(Hk & rb & Hrow) | (Hk & rb & Hrow)].
      + assert (k = 1%nat) as -> by (cbv [prod_out] in Hk; lia).
        iApply (UkPipeDev.pipe_write_nil N P Hsw gp l 1 rb (cif_dev d x) K
                  ltac:(unfold NSTD; lia) Hrow with "Hstd Hd").
        iSplit; [| iSplit].
        * iIntros "Hstd Hd". iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hd] Hd"). cif_repack.
        * iIntros "Hstd Hd". iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hd] Hd"). cif_repack.
        * iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
          iApply (cif_taint_of_fds with "[] Hstd Hhs Hxk"); [exact Hok |]. by rewrite -Hkill.
      + assert (k = 2%nat) as -> by (cbv [prod_err] in Hk; lia).
        iApply (cif_cons_nil l 2 rb (cif_dev d x) K ltac:(unfold NSTD; lia) Hrow with "Hstd Hd").
        iIntros "Hstd Hd". iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hd] Hd"). cif_repack.
  Qed.

  (* the deed lent to an input's leaf, and back *)
  Lemma cif_in_file_in (d : nat) (S : list (bv 8)) :
    cif_in d S -∗ fdq rf qf sf -∗
    ∃ (s : bool) (nm : list (bv 8)) (i : Z) (γo : gname) (content : list (bv 8)),
      ⌜sf = Some (i, content)⌝ ∗ cif_tok d (1/2) (UDIn s nm i γo)
      ∗ file_in rf i γo qf content S.
  Proof using .
    iIntros "Hin Hd". iDestruct "Hin" as (s nm i γo p) "(Htk & %Hc & Hu)".
    destruct Hc as (content & Hsf & HS). iExists s, nm, i, γo, content.
    iSplit; [done |]. iFrame "Htk". iExists p. iFrame "Hu". iSplit; [iPureIntro; exact HS |].
    rewrite -Hsf. iExact "Hd".
  Qed.

  Lemma cif_in_of_file_in (d : nat) (S content : list (bv 8)) (s : bool) (nm : list (bv 8))
      (i : Z) (γo : gname) :
    sf = Some (i, content) ->
    cif_tok d (1/2) (UDIn s nm i γo) -∗ file_in rf i γo qf content S -∗
    cif_in d S ∗ fdq rf qf sf.
  Proof using .
    intros Hsf. iIntros "Htk Hin". iDestruct "Hin" as (p) "(%HS & Hu & Hd)".
    rewrite Hsf. iFrame "Hd". iExists s, nm, i, γo, p. iFrame "Htk Hu". iPureIntro.
    by exists content.
  Qed.

  (* [ei_read] at an input: the deed lent from the core and back *)
  Lemma cif_read (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    cif_fds fdm -∗ cif_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        cif_fds fdm -∗ cif_in d S' -∗ K (RdBytes cb))
     ∧ (∀ x, cif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Heq Hkill Hsr Hsup TERM dep.
    intros Hn Hfd. iIntros "Hfds Hin HK".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    iDestruct (cif_in_file_in d Sin with "Hin Hdq") as (s nm i γo content) "(%Hsf & Htk & Hin)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hs. rewrite Hv in Hs. simpl in Hs.
    iPoseProof "He" as "(#Hbr & #Hrb & #Hinv & #Hm & _)".
    iDestruct "Hm" as (jo) "#Hm".
    destruct (Z_of_nat_complete fd H0) as [k ->].
    destruct s.
    - destruct Hs as (Hsk & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_read_std cf rf Heq N P Hsr k l false i γo qf jo content Sin n K
                ltac:(unfold NSTD in *; lia) Hrow Hn with "Hbr Hrb Hm Hinv Hstd Hin").
      iSplit.
      + iIntros (cb S') "%Hc Hstd Hin". iDestruct "HK" as "[HK _]".
        iDestruct (cif_in_of_file_in d S' content true nm i γo Hsf with "Htk Hin") as "[Hin Hdq]".
        iApply ("HK" $! cb S' with "[%] [-Hin] Hin"); [exact Hc |]. cif_repack.
      + iIntros (x) "#Htn Hstd Hin". iDestruct "HK" as "[_ HK]". iApply "HK".
        iApply (cif_taint_of_fds fdm l vs Hok with "[] Hstd Hhs Hxk").
        iApply (cif_T_of_file with "Htn He").
    - iDestruct (big_sepM_lookup_acc _ _ _ _ Hfd with "Hhs") as "[Hh Hcl]".
      iEval (rewrite /cif_hdl Hv) in "Hh". iEval (rewrite Nat2Z.id) in "Hh".
      iApply (file_read cf rf Heq N P Hsr k false i γo qf jo content Sin n K
                ltac:(lia) Hn with "Hbr Hrb Hm Hinv Hh Hin").
      iSplit.
      + iIntros (cb S') "%Hc Hh Hin". iDestruct "HK" as "[HK _]".
        iDestruct (cif_in_of_file_in d S' content false nm i γo Hsf with "Htk Hin") as "[Hin Hdq]".
        iApply ("HK" $! cb S' with "[%] [-Hin] Hin"); [exact Hc |].
        iApply (cif_fds_of with "Hstd Hcwd Hpool Htoks [Hh Hcl] Hdq He Hxk"); [exact Hok |].
        iApply "Hcl". rewrite /cif_hdl Hv Nat2Z.id. iExact "Hh".
      + iIntros (x) "#Htn Hh Hin". iDestruct "HK" as "[_ HK]". iApply "HK".
        iAssert ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d))%I with "[Hh Hcl]" as "Hhs".
        { iApply "Hcl". rewrite /cif_hdl Hv Nat2Z.id. iExact "Hh". }
        iApply (cif_taint_of_fds fdm l vs Hok with "[] Hstd Hhs Hxk").
        iApply (cif_T_of_file with "Htn He").
  Qed.

  Lemma cif_ans_ok (l : list fdstate) (ret : mword 64) :
    uk_open_taint_fd γfd l ret -∗ ⌜bv_signed ret = -1 \/ 0 <= bv_signed ret⌝.
  Proof using L TERM dep.
    rewrite /uk_open_taint_fd. iIntros "[Hal | [%Hr _]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb _]". destruct Hb as (Hr & Hfdlt & _).
      iPureIntro. right. rewrite Hr bvs_moi_small; [lia |].
      unfold NOFILE in Hfdlt.
      assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia.
    - iPureIntro. left. rewrite Hr. exact fdev_m1.
  Qed.

  Lemma cif_fresh_fd (fdm : fdmap) (l : list fdstate) (vs : gmap nat cfdev) (k : nat)
      (st : fdstate) :
    cif_ok kds fdm l vs -> (NSTD <= k)%nat ->
    ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d)) -∗ UserFd.ufd γfd k st -∗
    ⌜fdm !! Z.of_nat k = None⌝ ∗ ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d))
    ∗ UserFd.ufd γfd k st.
  Proof using L TERM dep γc γm.
    intros Hok Hk. iIntros "Hm Hh".
    destruct (fdm !! Z.of_nat k) as [d |] eqn:E; [| by iFrame].
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok E) as [kv Hv].
    pose proof Hok as (_ & H2 & _). specialize (H2 _ _ E). rewrite Hv in H2.
    destruct kv as [[|] nm i γo | pn gp w A X]; cbn [cif_row] in H2.
    - destruct H2 as [Hlt _]. lia.
    - iDestruct (big_sepM_lookup_acc _ _ _ _ E with "Hm") as "[Hx _]".
      rewrite /cif_hdl Hv Nat2Z.id.
      iDestruct "Hx" as "[Hx _]". iDestruct "Hh" as "[Hh _]".
      iDestruct (ghost_map_elem_ne with "Hx Hh") as %Hne. by destruct Hne.
    - exfalso. destruct H2 as [(Hq & _) | (Hq & _)]; cbv [prod_out prod_err NSTD] in *; lia.
  Qed.

  Lemma cif_open_taint (l : list fdstate) (ret : mword 64) (fdm : fdmap)
      (vs : gmap nat cfdev) :
    length l = NSTD -> cif_ok kds fdm l vs ->
    T -∗ uk_open_taint_fd γfd l ret -∗
    ([∗ map] fd ↦ d ∈ fdm, cif_hdl fd (vs !! d)) -∗ cif_xk -∗
    cif_taint (open_held fdm (bv_signed ret)).
  Proof using Hkill Hsup TERM dep.
    intros Hlen Hok. iIntros "#Htn Hof Hhs Hxk".
    iDestruct ("Hxk" with "[]") as "Hpay"; [by iLeft |].
    rewrite /uk_open_taint_fd.
    iDestruct "Hof" as "[Hal | [%Hr Hstd]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]". destruct Hb as (Hr & Hfdlt & _).
      assert (Hsig : bv_signed ret = Z.of_nat fd).
      { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
        assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia. }
      rewrite Hsig /open_held decide_True; [| lia].
      rewrite cif_hdls_hm.
      pose proof (cif_held_ok_fds fdm l vs Hok) as Hho.
      rewrite /cif_taint /fh_taint. iFrame "Htn Hpay".
      iSplitR; [iIntros "!> HT"; by rewrite Hkill |].
      iSplitR; [iApply Hsup |].
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + iDestruct (ualloc_std γfd l fd k0 _ Elc with "Hal") as "[%Hfk Hstd]". subst fd.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        pose proof (lookup_lt_Some _ _ _ Hk0) as Hk0l.
        iExists (<[k0 := FdOpen rd wr t]> l), (omap (cif_hf vs) fdm). iFrame "Hstd Hhs".
        iPureIntro. intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
        * apply elem_of_singleton in Hx as ->. split; [unfold NSTD, NOFILE in *; lia |].
          left. split; [unfold NSTD in *; lia |]. exists (FdOpen rd wr t).
          rewrite Nat2Z.id list_lookup_insert; [split; [done | discriminate] | exact Hk0l].
        * destruct (Hho x Hx) as [Hb Hc]. split; [exact Hb |].
          destruct Hc as [(Hs' & st' & Hl' & Hne') | Hc]; [left | by right].
          split; [exact Hs' |].
          destruct (decide (Z.to_nat x = k0)) as [-> | Hne].
          -- exists (FdOpen rd wr t). rewrite list_lookup_insert; [split; [done | discriminate] |].
             exact Hk0l.
          -- exists st'. rewrite list_lookup_insert_ne; [split; [exact Hl' | exact Hne'] |].
             congruence.
      + iDestruct (ualloc_hi γfd l fd (FdOpen rd wr t) Elc with "Hal")
          as "(%Hhi & Hstd & Hh)".
        iDestruct (fh_hm_fresh N with "Hhs Hh") as "(%Hfr & Hhs & Hh)".
        iExists l, (<[Z.of_nat fd := FdOpen rd wr t]> (omap (cif_hf vs) fdm)). iFrame "Hstd".
        iSplit.
        * iPureIntro. intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
          -- apply elem_of_singleton in Hx as ->. split; [lia |]. right.
             split; [lia |]. rewrite lookup_insert. by eexists.
          -- destruct (Hho x Hx) as [Hb Hc]. split; [exact Hb |].
             destruct Hc as [Hc | (Hs & Hsm)]; [by left | right]. split; [exact Hs |].
             destruct (decide (x = Z.of_nat fd)) as [-> | Hne];
               [rewrite lookup_insert; by eexists | rewrite lookup_insert_ne; [exact Hsm | congruence]].
        * rewrite big_sepM_insert; [| exact Hfr]. rewrite Nat2Z.id. iFrame "Hh Hhs".
    - rewrite Hr fdev_m1 /open_held. case_decide; [lia |].
      rewrite cif_hdls_hm. rewrite /cif_taint /fh_taint. iFrame "Htn Hpay".
      iSplitR; [iIntros "!> HT"; by rewrite Hkill |].
      iSplitR; [iApply Hsup |].
      iExists l, (omap (cif_hf vs) fdm). iFrame "Hstd Hhs". iPureIntro.
      by apply cif_held_ok_fds.
  Qed.

  (* [ei_open] of a present user file: the descriptor the ledger names,
     the token of a fresh device minted as an input on `f` *)
  Lemma cif_open (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path content : list (bv 8)) (K : Z -> iProp Σ) :
    path ∈ paths -> files path = Some content ->
    cif_fds fdm -∗ cif_filesr files paths -∗
    ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm !! fd = None⌝ -∗
        (∀ d : nat, ⌜dev_fresh_p Dp fdm d⌝ -∗
           cif_fds (<[fd := d]> fdm) ∗ cif_in d content) -∗
        cif_filesr files paths -∗ K fd)
     ∧ (cif_fds fdm -∗ cif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ cif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path 0 K.
  Proof using Heq Hkill Hso Hsup TERM dep.
    intros Hp Hf. iIntros "Hfds #Hfiles HK".
    iAssert (⌜(forall p, p ∈ paths -> uname p) /\ files fname_f = snd <$> sf⌝)%I
      as %[Hpaths Hfs].
    { iDestruct "Hfiles" as "[%A %B]". by iPureIntro. }
    pose proof (Hpaths path Hp) as Hun. rewrite /uname in Hun. subst path.
    rewrite Hf in Hfs.
    destruct (cif_dst_some sf content (eq_sym Hfs)) as [i Hsf].
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hd & #He & Hxk)".
    iPoseProof "He" as "(_ & _ & #Hinv & _)".
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen.
    iAssert (fdq rf qf (Some (i, content))) with "[Hd]" as "Hd"; [by rewrite -Hsf |].
    iPoseProof (fdq_split rf (qf / 2) (qf / 2) (Some (i, content)) with "[Hd]") as "[Hd1 Hd2]".
    { rewrite Qp.div_2. iExact "Hd". }
    iAssert (□ (fdq rf (qf / 2) (Some (i, content)) -∗ fdq rf (qf / 2) (Some (i, content))
                -∗ fdq rf qf sf))%I as "#Hjoin".
    { iIntros "!> Ha Hb". iDestruct (fdq_join with "Ha Hb") as "Hd".
      rewrite Qp.div_2 Hsf. iExact "Hd". }
    iApply (file_open_present cf rf Heq N P Hso l FsImg.ROOTINO (qf / 2) (qf / 2) i content K
              eq_refl with "Hinv Hstd Hcwd Hd1 Hd2").
    iSplit; [| iSplit].
    - iIntros (fd γo) "%Hfdlt Hal Hcwd Hin Hd1".
      iDestruct "Hin" as (p) "(%Hp0 & Hu & Hd2)".
      iDestruct ("Hjoin" with "Hd1 Hd2") as "Hd".
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + iDestruct (ualloc_std γfd l fd k0 _ Elc with "Hal") as "[%Hfk Hstd]". subst fd.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        pose proof (cif_ok_closed_fresh kds fdm l vs k0 Hok Hlen Hk0) as Hnb.
        iMod (own_update with "Hpool") as "Hpool";
          [apply (cif_pool_update _ wv (UDIn true fname_f i γo)) |].
        iModIntro.
        iDestruct "HK" as "[HK _]".
        iApply ("HK" $! (Z.of_nat k0) with "[%] [%] [-] []"); [lia | exact Hnb | | iExact "Hfiles"].
        iIntros (d) "%Hfr". apply dev_fresh_p_iff in Hfr as [HD Hfr].
        assert (Hvd : vs !! d = None).
        { apply not_elem_of_dom. pose proof Hok as (_ & _ & H3 & _). intros Hd.
          destruct (H3 d Hd) as [(fd' & Hfd') | HD']; [exact (Hfr fd' Hfd') | done]. }
        assert (Hdn : d ∉ dom vs) by (by apply not_elem_of_dom).
        iEval (rewrite (cif_pool_own_take _ _ d Hdn) cif_tok_halves) in "Hpool".
        iDestruct "Hpool" as "(Hpool & Htk1 & Htk2)".
        iSplitR "Htk2 Hu".
        * iExists (<[k0 := FdOpen true false (FdInode i γo OffHeld)]> l),
            (<[d := UDIn true fname_f i γo]> vs), (fun _ => UDIn true fname_f i γo).
          iFrame "Hxk Hstd Hcwd Hd".
          iSplit.
          { iPureIntro. apply cif_ok_open_std; [exact Hok | exact Hlen | exact Hk0 | exact Hfr | exact HD]. }
          iSplitL "Hpool"; [by rewrite dom_insert_L |].
          iSplitL "Htoks Htk1".
          { rewrite big_sepM_insert; [| exact Hvd]. iFrame "Htk1 Htoks". }
          iSplitL "Hhs".
          { rewrite big_sepM_insert; [| exact Hnb]. iSplitR.
            { rewrite /cif_hdl lookup_insert. done. }
            iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
            rewrite lookup_insert_ne; [iExact "Hx" |]. intros ->. exact (Hfr fd' Hfd'). }
          iApply (cif_env_insert vs d _ Hvd with "He"). cbn [cif_pk_inv]. by iPureIntro.
        * iExists true, fname_f, i, γo, p. iFrame "Htk2 Hu". iPureIntro. by exists content.
      + iDestruct (ualloc_hi γfd l fd _ Elc with "Hal") as "(%Hhi & Hstd & Hh)".
        iDestruct (cif_fresh_fd fdm l vs fd with "Hhs Hh") as "(%Hnb & Hhs & Hh)";
          [exact Hok | lia |].
        iMod (own_update with "Hpool") as "Hpool";
          [apply (cif_pool_update _ wv (UDIn false fname_f i γo)) |].
        iModIntro.
        iDestruct "HK" as "[HK _]".
        iApply ("HK" $! (Z.of_nat fd) with "[%] [%] [-] []"); [lia | exact Hnb | | iExact "Hfiles"].
        iIntros (d) "%Hfr". apply dev_fresh_p_iff in Hfr as [HD Hfr].
        assert (Hvd : vs !! d = None).
        { apply not_elem_of_dom. pose proof Hok as (_ & _ & H3 & _). intros Hd.
          destruct (H3 d Hd) as [(fd' & Hfd') | HD']; [exact (Hfr fd' Hfd') | done]. }
        assert (Hdn : d ∉ dom vs) by (by apply not_elem_of_dom).
        iEval (rewrite (cif_pool_own_take _ _ d Hdn) cif_tok_halves) in "Hpool".
        iDestruct "Hpool" as "(Hpool & Htk1 & Htk2)".
        iSplitR "Htk2 Hu".
        * iExists l, (<[d := UDIn false fname_f i γo]> vs), (fun _ => UDIn false fname_f i γo).
          iFrame "Hxk Hstd Hcwd Hd".
          iSplit.
          { iPureIntro. apply cif_ok_open; [exact Hok | exact (conj Hhi Hfdlt) | exact Hnb | exact Hfr | exact HD]. }
          iSplitL "Hpool"; [by rewrite dom_insert_L |].
          iSplitL "Htoks Htk1".
          { rewrite big_sepM_insert; [| exact Hvd]. iFrame "Htk1 Htoks". }
          iSplitL "Hhs Hh".
          { rewrite big_sepM_insert; [| exact Hnb]. iSplitL "Hh".
            { rewrite /cif_hdl lookup_insert Nat2Z.id. iExact "Hh". }
            iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
            rewrite lookup_insert_ne; [iExact "Hx" |]. intros ->. exact (Hfr fd' Hfd'). }
          iApply (cif_env_insert vs d _ Hvd with "He"). cbn [cif_pk_inv]. by iPureIntro.
        * iExists false, fname_f, i, γo, p. iFrame "Htk2 Hu". iPureIntro. by exists content.
    - iIntros "Hstd Hcwd Hd1 Hd2". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-] []"); [| iExact "Hfiles"].
      iApply (cif_fds_of with "Hstd Hcwd Hpool Htoks Hhs [Hd1 Hd2] He Hxk"); [exact Hok |].
      iApply ("Hjoin" with "Hd1 Hd2").
    - iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ [_ HK]]".
      iDestruct (cif_ans_ok with "Hof") as %Hans.
      iApply ("HK" with "[%]"); [exact Hans |].
      iApply (cif_open_taint l ret fdm vs Hlen Hok with "[] Hof Hhs Hxk").
      iApply (cif_T_of_file with "Htn He").
  Qed.

  (* [ei_open_absent] of a user file, at a mode that does not create *)
  Lemma cif_open_absent (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    path ∈ paths -> ~ mode_create m -> files path = None ->
    cif_fds fdm -∗ cif_filesr files paths -∗
    ((cif_fds fdm -∗ cif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ cif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path m K.
  Proof using Heq Hkill Hso Hsup TERM dep.
    intros Hp Hcm Hf. iIntros "Hfds #Hfiles HK".
    iAssert (⌜(forall p, p ∈ paths -> uname p) /\ files fname_f = snd <$> sf⌝)%I
      as %[Hpaths Hfs].
    { iDestruct "Hfiles" as "[%A %B]". by iPureIntro. }
    pose proof (Hpaths path Hp) as Hun. rewrite /uname in Hun. subst path.
    rewrite Hf in Hfs. pose proof (cif_dst_none sf (eq_sym Hfs)) as Hs.
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hd & #He & Hxk)".
    iPoseProof "He" as "(_ & _ & #Hinv & _)".
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen.
    iAssert (fdq rf qf None) with "[Hd]" as "Hd"; [by rewrite -Hs |].
    iApply (file_open_absent cf rf Heq N P Hso l FsImg.ROOTINO qf m K eq_refl
              (cif_om_create m Hcm) with "Hinv Hstd Hcwd Hd").
    iSplit.
    - iIntros "Hstd Hcwd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-] []"); [| iExact "Hfiles"].
      iApply (cif_fds_of with "Hstd Hcwd Hpool Htoks Hhs [Hd] He Hxk"); [exact Hok |].
      by rewrite Hs.
    - iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ HK]".
      iDestruct (cif_ans_ok with "Hof") as %Hans.
      iApply ("HK" with "[%]"); [exact Hans |].
      iApply (cif_open_taint l ret fdm vs Hlen Hok with "[] Hof Hhs Hxk").
      iApply (cif_T_of_file with "Htn He").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1g. THE CLOSE                                                       *)
  (* ------------------------------------------------------------------- *)

  (* the close of a standard slot, by the row its registered kind demands *)
  Lemma cif_close_row (vs : gmap nat cfdev) (d : nat) (kd : cfdev) (k : nat) (l : list fdstate)
      (K : Z -> iProp Σ) :
    vs !! d = Some kd -> cif_row (Some kd) (Z.of_nat k) l -> (k < NSTD)%nat ->
    cif_env vs -∗ UserFd.ustd γfd l -∗ (UserFd.ustd γfd (<[k := FdClosed]> l) -∗ K 0) -∗
    cl_obl N P (Z.of_nat k) K.
  Proof using Hsc TERM dep γc γm.
    intros Hv Hrow Hlt. iIntros "#He Hstd HK".
    iPoseProof (cif_env_lookup vs d kd Hv with "He") as "Hi".
    destruct kd as [[|] nm i γo | pn gp w A X]; cbn [cif_row cif_pk_inv] in Hrow |- *.
    - destruct Hrow as (_ & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd HK").
    - exfalso. unfold NSTD in *. lia.
    - iDestruct "Hi" as "#Hi".
      destruct Hrow as [(Hk & rb & Hrow) | (Hk & rb & Hrow)].
      + assert (k = 1%nat) as -> by (cbv [prod_out] in Hk; lia).
        iPoseProof (pipe_reg_of_inv pn gp L with "Hi") as "#Hreg".
        iApply (pipe_close N P Hsc gp l 1 rb true K Hlt Hrow with "Hreg Hstd HK").
      + assert (k = 2%nat) as -> by (cbv [prod_err] in Hk; lia).
        iApply (file_close_std N P Hsc 2 l _ K Hlt Hrow ltac:(discriminate) Logic.I
                  with "Hstd HK").
  Qed.

  (* the descriptors after an UNPROTECTED device's last descriptor closed *)
  Lemma cif_fds_after_close (fdm : fdmap) (l l' : list fdstate) (vs : gmap nat cfdev)
      (wv : nat -> cfdev) (fd : Z) (d : nat) (kd : cfdev) :
    cif_ok kds fdm l vs -> fdm !! fd = Some d -> ~ fd_shared fdm fd d -> d ∉ Dp ->
    vs !! d = Some kd ->
    (forall fd' d', fd' <> fd -> fdm !! fd' = Some d' -> l' !! Z.to_nat fd' = l !! Z.to_nat fd') ->
    UserFd.ustd γfd l' -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
    own γreg (cif_pool (dom vs) wv) -∗
    ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x) -∗ cif_tok d (1/2) kd -∗
    ([∗ map] fd ↦ d ∈ delete fd fdm, cif_hdl fd (vs !! d)) -∗ fdq rf qf sf -∗ cif_env vs -∗
    cif_xk -∗ cif_fds (delete fd fdm).
  Proof using .
    intros Hok Hfd Hns HD Hv Hl. iIntros "Hstd Hcwd Hpool Htoks Htk Hhs Hdq #He Hxk".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (cif_tok d 1 kd) with "[Htk Htk']" as "Htk".
    { rewrite cif_tok_halves. iFrame "Htk Htk'". }
    assert (Hdd : d ∈ dom vs) by (apply elem_of_dom; by eexists).
    iDestruct (cif_pool_give vs wv d kd Hdd with "Hpool Htk") as "Hpool".
    iPoseProof (cif_env_delete vs d with "He") as "#He'".
    pose proof (cif_ok_close kds fdm l vs fd d Hok Hfd Hns HD) as Hok'.
    pose proof (cif_not_shared fdm fd d Hns) as Hn.
    assert (Hok'' : cif_ok kds (delete fd fdm) l' (delete d vs)).
    { apply (cif_ok_ledger kds (delete fd fdm) l l' (delete d vs) Hok').
      intros fd' d' Hfd'. apply lookup_delete_Some in Hfd' as [Hne Hfd'].
      exact (Hl fd' d' (not_eq_sym Hne) Hfd'). }
    iApply (cif_fds_of (delete fd fdm) l' (delete d vs) _ Hok''
              with "Hstd Hcwd Hpool Htoks [Hhs] Hdq He' Hxk").
    iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
    rewrite lookup_delete_ne; [iExact "Hx" |].
    intros ->. apply lookup_delete_Some in Hfd' as [Hne Hfd'].
    exact (Hn fd' (not_eq_sym Hne) Hfd').
  Qed.

  (* [ei_close]: the last descriptor of an UNPROTECTED device *)
  Lemma cif_close (fdm : fdmap) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared_p Dp fdm fd d -> drained_at_close x ->
    cif_fds fdm -∗ cif_filesr files paths -∗ cif_dev d x -∗
    ((cif_fds (delete fd fdm) -∗ cif_filesr files paths -∗ K 0)
     ∧ (∀ y, cif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hnsp _.
    assert (HD : d ∉ Dp) by (intros H; apply Hnsp; apply fd_shared_p_iff; by left).
    assert (Hns : ~ fd_shared fdm fd d) by (intros H; apply Hnsp; apply fd_shared_p_iff; by right).
    iIntros "Hfds #Hfiles Hd HK".
    iDestruct (cif_dev_tok with "Hd") as (kd) "(Htk & _)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd' Hv].
    iDestruct (cif_toks_agree vs d kd' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd'.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 _].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[Hh Hhs]".
    destruct (Z_of_nat_complete fd H0) as [k ->].
    iDestruct "HK" as "[HK _]".
    assert (Hled : forall fd' d', fd' <> Z.of_nat k -> fdm !! fd' = Some d' ->
                     (<[k := FdClosed]> l) !! Z.to_nat fd' = l !! Z.to_nat fd').
    { intros fd' d' Hne' Hfd'. destruct (H1 fd' d' Hfd') as [H0' _].
      apply list_lookup_insert_ne. exact (cif_slot_ne k fd' H0' Hne'). }
    destruct kd as [[|] nm i γo | pn gp w A X].
    - (* a standard slot's input *)
      pose proof Hrow as Hrow'. cbn [cif_row] in Hrow'. destruct Hrow' as (Hlt & _).
      iApply (cif_close_row vs d _ k l K Hv Hrow ltac:(unfold NSTD in *; lia) with "He Hstd").
      iIntros "Hstd". iApply ("HK" with "[-] Hfiles").
      iApply (cif_fds_after_close fdm l _ vs wv (Z.of_nat k) d _ Hok Hfd Hns HD Hv Hled
                with "Hstd Hcwd Hpool Htoks Htk Hhs Hdq He Hxk").
    - (* a tail handle *)
      iEval (rewrite /cif_hdl Hv Nat2Z.id) in "Hh".
      iApply (file_close N P Hsc k (FdOpen true false (FdInode i γo OffHeld)) K Logic.I with "Hh").
      iApply ("HK" with "[-] Hfiles").
      iApply (cif_fds_after_close fdm l l vs wv (Z.of_nat k) d _ Hok Hfd Hns HD Hv
                ltac:(intros; reflexivity)
                with "Hstd Hcwd Hpool Htoks Htk Hhs Hdq He Hxk").
    - (* the producer device, unprotected *)
      assert (Hlt : (k < NSTD)%nat).
      { cbn [cif_row] in Hrow. destruct Hrow as [(Hk & _) | (Hk & _)]; cbv [prod_out prod_err NSTD] in *; lia. }
      iApply (cif_close_row vs d _ k l K Hv Hrow Hlt with "He Hstd").
      iIntros "Hstd". iApply ("HK" with "[-] Hfiles").
      iApply (cif_fds_after_close fdm l _ vs wv (Z.of_nat k) d _ Hok Hfd Hns HD Hv Hled
                with "Hstd Hcwd Hpool Htoks Htk Hhs Hdq He Hxk").
  Qed.

  (* [ei_close_shared]: a dup, or a PROTECTED device's descriptor -- the
     device stays, only the ledger's slot closes *)
  Lemma cif_close_shared (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> fd_shared_p Dp fdm fd d ->
    cif_fds fdm -∗
    ((cif_fds (delete fd fdm) -∗ K 0) ∧ (∀ y, cif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hkdp Hsc TERM dep.
    intros Hfd Hsh. iIntros "Hfds HK".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He & Hxk)".
    destruct (cif_ok_lookup kds _ _ _ _ _ Hok Hfd) as [kd Hv].
    pose proof Hok as (H1 & H2 & _ & _ & H5 & H6 & _). destruct (H1 fd d Hfd) as [H0 _].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    pose proof (cif_ok_close_shared kds fdm l vs fd d Hok Hfd Hsh) as Hok'.
    apply fd_shared_p_iff in Hsh.
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[_ Hhs]".
    assert (Hlt : fd < Z.of_nat NSTD).
    { destruct kd as [[|] nm i γo | pn gp w A X]; cbn [cif_row] in Hrow.
      - by destruct Hrow.
      - exfalso. destruct Hsh as [HD | (fd' & Hin' & Hfd')].
        + apply elem_of_list_fmap in HD as (dk & -> & Hdk).
          destruct (Hkdp dk Hdk) as (pn & gp & w & A & X & Hq).
          pose proof (H6 dk Hdk) as Hw. rewrite Hv Hq in Hw. discriminate Hw.
        + apply elem_of_dom in Hin' as [d'' Hd'']. apply lookup_delete_Some in Hd'' as [Hne _].
          exact (Hne (H5 fd fd' d false nm i γo Hfd Hfd' Hv)).
      - destruct Hrow as [(-> & _) | (-> & _)]; cbv [prod_out prod_err NSTD]; lia. }
    destruct (Z_of_nat_complete fd H0) as [k ->].
    iApply (cif_close_row vs d kd k l K Hv Hrow ltac:(unfold NSTD in *; lia) with "He Hstd").
    iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
    assert (Hok'' : cif_ok kds (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) vs).
    { apply (cif_ok_ledger kds (delete (Z.of_nat k) fdm) l _ vs Hok').
      intros fd' d' Hfd'. apply lookup_delete_Some in Hfd' as [Hne' Hfd'].
      destruct (H1 fd' d' Hfd') as [H0' _].
      apply list_lookup_insert_ne. exact (cif_slot_ne k fd' H0' (not_eq_sym Hne')). }
    iApply (cif_fds_of (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) vs wv Hok''
              with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hxk").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1h. THE EXIT                                                        *)
  (* ------------------------------------------------------------------- *)

  Lemma cif_dev_final (vs : gmap nat cfdev) (d : nat) (kd : cfdev) (x : dspec) :
    vs !! d = Some kd -> drained x ->
    cif_env vs -∗ ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x) -∗ cif_dev d x ={⊤}=∗
    ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x) ∗ cif_final kd.
  Proof using .
    intros Hv Hdr. iIntros "#He Htoks Hd".
    iPoseProof (cif_env_lookup vs d kd Hv with "He") as "#Hi".
    destruct x as [alts | alts | cs | | Sin | Sin | | h Sc p | h p | | outs xs ds | ds];
      cbn [cif_dev drained] in Hdr |- *; try (iDestruct "Hd" as "[]").
    - iDestruct "Hd" as (s nm i γo p) "(Htk & _)".
      iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [cif_final]. iModIntro. by iFrame "Htoks".
    - destruct Hdr as [Hon Hdn].
      iDestruct "Hd" as (pn gp w A X) "[Htk Hb]".
      iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [cif_final cif_pk_inv]. iFrame "Htoks".
      iDestruct "Hb" as "[(-> & Hw & _ & Hu) | [(%Hp & Hw & _ & Hcon)
                        | [(%Hp & (%S & -> & Hpo) & Hcon) | (%Hp & %x & %c & %HxX & Hcf)]]]".
      + iModIntro. iLeft. iSplitL "Hw"; [by iRight |].
        iApply (pns_con_drained g M V G v I sR lR TERM TOK dep γc γm w A ds Hdn).
        iApply (cif_unf_con with "Hu").
      + iModIntro. iLeft. iSplitL "Hw"; [by iRight |].
        iApply (pns_con_drained g M V G v I sR lR TERM TOK dep γc γm w A ds Hdn with "Hcon").
      + apply elem_of_list_singleton in Hon as <-.
        iMod (pns_lexit_of_lend L TERM dep pn gp with "Hi [Hpo]") as "Hle"; [by iLeft |].
        iModIntro. iLeft. iSplitL "Hle"; [by iLeft |].
        iApply (pns_con_drained g M V G v I sR lR TERM TOK dep γc γm w A ds Hdn with "Hcon").
      + iModIntro. iRight. iExists x. iSplitR; [by iPureIntro |].
        iApply (cif_conF_final w x c ds Hdn with "Hcf").
    - iDestruct "Hd" as (pn gp w A X) "(Htk & Hh & Hcon)".
      iDestruct (cif_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [cif_final cif_pk_inv]. iFrame "Htoks".
      iMod (pns_lexit_of_lend L TERM dep pn gp with "Hi [Hh]") as "Hle"; [by iRight |].
      iModIntro. iLeft. iSplitL "Hle"; [by iLeft |].
      iApply (pns_con_drained g M V G v I sR lR TERM TOK dep γc γm w A ds Hdr with "Hcon").
  Qed.

  Lemma cif_finals (vs : gmap nat cfdev) (dv : nat -> dspec) (kl : list (nat * cfdev)) :
    (forall dk, dk ∈ kl -> vs !! dk.1 = Some dk.2 /\ drained (dv dk.1)) ->
    cif_env vs -∗ ([∗ map] d ↦ x ∈ vs, cif_tok d (1/2) x) -∗
    ([∗ list] dk ∈ kl, cif_dev dk.1 (dv dk.1)) ={⊤}=∗ [∗ list] dk ∈ kl, cif_final dk.2.
  Proof using .
    induction kl as [| dk kl IH]; intros Hall; iIntros "#He Htoks Hdev".
    - by iModIntro.
    - iDestruct "Hdev" as "[Hd Hdev]".
      destruct (Hall dk (elem_of_list_here _ _)) as [Hv Hdr].
      iMod (cif_dev_final vs dk.1 dk.2 (dv dk.1) Hv Hdr with "He Htoks Hd") as "[Htoks Hf]".
      iMod (IH with "He Htoks Hdev") as "Hfs".
      { intros dk' Hdk'. apply Hall. by apply elem_of_list_further. }
      iModIntro. iSplitL "Hf"; [iExact "Hf" | iExact "Hfs"].
  Qed.

  (* [ei_exit]: every protected device is among the drained ones; read at
     its kind, the finals and the deed pay the wand *)
  Lemma cif_exit (s : Z) (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (dv : nat -> dspec) (ds : gset nat) :
    (forall d, d ∈ ds -> drained (dv d)) ->
    dom_ok_p Dp fdm ds ->
    cif_fds fdm -∗ cif_filesr files paths -∗ ([∗ set] d ∈ ds, cif_dev d (dv d)) -∗
    ex_obl N P s.
  Proof using HNc Hkds Hse.
    intros Hdr Hds. iIntros "Hfds _ Hdev".
    iDestruct "Hfds" as (l vs wv) "(_ & _ & %Hok & _ & Htoks & _ & Hdq & #He & Hxk)".
    pose proof Hok as (_ & _ & _ & _ & _ & Hkd & _).
    apply dom_ok_p_iff in Hds as [Hdp _].
    assert (Hsub : (list_to_set Dp : gset nat) ⊆ ds).
    { intros d Hd. apply elem_of_list_to_set in Hd. exact (Hdp d Hd). }
    iDestruct (big_sepS_subseteq _ ds _ Hsub with "Hdev") as "Hdev".
    iEval (rewrite (big_sepS_list_to_set (fun d => cif_dev d (dv d)) Dp Hkds)
             big_sepL_fmap) in "Hdev".
    iIntros (h m avail) "%Hst Hcode Hrun".
    iApply fupd_wp.
    iMod (cif_finals vs dv kds with "He Htoks Hdev") as "Hfin".
    { intros dk Hdk. split; [exact (Hkd dk Hdk) |]. apply Hdr, Hdp.
      apply elem_of_list_fmap_1. exact Hdk. }
    iDestruct ("Hxk" with "[Hfin Hdq]") as "Hpay"; [iRight; iFrame "Hfin Hdq" |].
    iModIntro.
    iPoseProof (fh_exit_pay N P Hse s with "Hpay") as "Hex".
    iApply ("Hex" $! h m avail with "[%] Hcode Hrun"). exact Hst.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1i. THE RECORD                                                      *)
  (* ------------------------------------------------------------------- *)

  Definition cif_iface : ep_ifaceP (Dp := kds.*1) N P.
  Proof using Heq Hcons Hkill Hsup HPc HNc Hsr Hsw Hso Hsc Hse Hfc Hadmit Hext HlR Hplok
              dep_tl HL31 Hkds Hkdp v TERM TOK γc γm γreg qf sf cifRegG0 pipesNG0 pipeProtoG0.
    refine (MkEIP (Dp := kds.*1) N P cif_fds
              (fun _ _ => False%I) (fun _ _ => False%I) (fun _ => False%I) (fun _ _ => False%I)
              cif_in (fun _ _ => False%I) (fun _ => False%I)
              (fun _ _ _ _ _ _ => False%I) (fun _ _ _ _ => False%I) (fun _ _ => False%I)
              cif_prod cif_prod_halt
              cif_filesr cif_taint cif_taint_pays
              _ _ _ _ cif_write_nil cif_read _ _ _ _ _ _ _ _ _ _ _ cif_open cif_open_absent
              cif_close cif_close_shared cif_exit
              cif_write_prod cif_write_prod_halt cif_write_prod_err cif_write_prod_fail
              cif_write_prod_halt_err).
    all: intros; iIntros "_ []".
  Defined.

  Lemma cif_ei_fds : ei_fds N P cif_iface = cif_fds.
  Proof using . reflexivity. Qed.
  Lemma cif_ei_files : ei_files N P cif_iface = cif_filesr.
  Proof using . reflexivity. Qed.
  Lemma cif_dev_of (d : nat) (x : dspec) : dev_of N P cif_iface d x = cif_dev d x.
  Proof using . by destruct x. Qed.

  (* ------------------------------------------------------------------- *)
  (*  1j. WHAT THE PRODUCER STAGE IS LENT, AND ITS ENVIRONMENT            *)
  (* ------------------------------------------------------------------- *)

  (* the first pipe's invariant and untouched permit, the family writer
     unfired with its kits (the reports' deposits FROM the permit), the
     deed, the file's persistent context, and the exit wand to [Q] *)
  Definition cif_catf_lend (pn : pnames) (gp : pipe_names) (w : wid)
      (A X ds xs : list (list (bv 8))) (Q : Z -> iProp Σ) : iProp Σ :=
    (pipe_inv pn gp L ∗ wcur pn 0%nat ∗ pws_lb pn [] ∗ cif_unf pn w A X ds xs
     ∗ fdq rf qf sf
     ∗ □ (app_taint -∗ file_taint cf) ∗ □ (file_taint cf -∗ app_taint)
     ∗ app_inv fsc_fs ∗ (∃ jo : option Z, file_cons_cred cf rf jo)
     ∗ cif_xkQ [(0%nat, UDProd pn gp w A X)] Q)%I.

  (* ---- the environment of [cat f]: fds 1 and 2 on the producer device
          (device 0, protected) ---- *)
  Lemma cif_catf_env_res (pn : pnames) (gp : pipe_names) (w : wid)
      (A X ds xs : list (list (bv 8))) (l : list fdstate) (rb1 rb2 : bool)
      (wv : nat -> cfdev) (files : list (bv 8) -> option (list (bv 8))) :
    kds = [(0%nat, UDProd pn gp w A X)] -> wv 0%nat = UDProd pn gp w A X ->
    l !! 1%nat = Some (FdOpen rb1 true (FdPipe gp)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    files fname_f = snd <$> sf ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗ own γreg (cif_pool ∅ wv) -∗
    cif_catf_lend pn gp w A X ds xs (ukn_pay N) -∗
    env_res N P cif_iface (catp_env (DProd [L; []] xs ds) files [fname_f]) {[0%nat]}.
  Proof using .
    intros Hk Hw0 Hl1 Hl2 Hfs.
    set (fdm := (<[1 := 0%nat]> {[2 := 0%nat]} : fdmap)).
    set (vs := ({[0%nat := UDProd pn gp w A X]} : gmap nat cfdev)).
    assert (Hv0 : vs !! 0%nat = Some (UDProd pn gp w A X)) by (rewrite /vs; apply lookup_singleton).
    assert (Hfdm : forall fd d, fdm !! fd = Some d -> d = 0%nat /\ (fd = 1 \/ fd = 2)).
    { intros fd d. rewrite /fdm. destruct (decide (fd = 1)) as [-> |].
      - rewrite lookup_insert. intros [= <-]. split; [done | by left].
      - rewrite lookup_insert_ne; [| done]. rewrite lookup_singleton_Some. intros [<- <-].
        split; [done | by right]. }
    assert (Hok : cif_ok kds fdm l vs).
    { split; [| split; [| split; [| split; [| split; [| split]]]]].
      - intros fd d Hfd. destruct (Hfdm fd d Hfd) as [_ [-> | ->]]; unfold NOFILE; lia.
      - intros fd d Hfd. destruct (Hfdm fd d Hfd) as [-> [-> | ->]]; rewrite Hv0; cbn [cif_row].
        + left. split; [reflexivity | by exists rb1].
        + right. split; [reflexivity | by exists rb2].
      - intros d. rewrite /vs dom_singleton_L elem_of_singleton.
        intros ->. left. exists 1. rewrite /fdm. apply lookup_insert.
      - intros fd d Hfd. destruct (Hfdm fd d Hfd) as [-> _].
        rewrite /vs dom_singleton_L. set_solver.
      - intros fd fd' d s nm i γo _ _ Hv. rewrite /vs lookup_singleton_Some in Hv.
        by destruct Hv as [_ Hq].
      - intros dk. rewrite Hk elem_of_list_singleton. intros ->. exact Hv0.
      - intros d s nm i γo Hv. rewrite /vs lookup_singleton_Some in Hv.
        by destruct Hv as [_ Hq]. }
    iIntros "Hstd Hcwd Hpool (#Hinv & Hw & #Hlb & Hu & Hdq & #Hbr & #Hrb & #Hai & #Hcr & Hxk)".
    rewrite /env_res.
    iDestruct (cif_pool_own_take ∅ wv 0%nat with "Hpool") as "[Hpool Htk]"; [set_solver |].
    rewrite Hw0. iDestruct (cif_tok_halves with "Htk") as "[Htk1 Htk2]".
    iAssert (cif_env vs) as "#He".
    { rewrite /cif_env. iFrame "Hbr Hrb Hai Hcr".
      rewrite /vs big_sepM_singleton. cbn [cif_pk_inv]. iExact "Hinv". }
    iSplit.
    { iPureIntro. intros fd d Hfd. cbn [catp_env pe_fd] in Hfd.
      destruct (Hfdm fd d Hfd) as [-> _]. set_solver. }
    iSplitL "Hstd Hcwd Hxk Hpool Htk1 Hdq".
    { rewrite cif_ei_fds. cbn [catp_env pe_fd].
      iApply (cif_fds_of fdm l vs wv Hok with "Hstd Hcwd [Hpool] [Htk1] [] Hdq He [Hxk]").
      - by rewrite /vs dom_singleton_L right_id_L.
      - by rewrite /vs big_sepM_singleton.
      - iApply big_sepM_intro. iIntros "!>" (fd d Hfd).
        destruct (Hfdm fd d Hfd) as [-> _]. rewrite Hv0. done.
      - rewrite /cif_xk Hk. iExact "Hxk". }
    iSplitR.
    { rewrite cif_ei_files /cif_filesr. cbn [catp_env pe_paths pe_files]. iPureIntro. split.
      - intros p Hp. apply elem_of_list_singleton in Hp as ->. reflexivity.
      - exact Hfs. }
    rewrite /dev_res big_sepS_singleton cif_dev_of.
    assert (E0 : pe_dev (catp_env (DProd [L; []] xs ds) files [fname_f]) 0%nat
                 = DProd [L; []] xs ds) by reflexivity.
    rewrite E0. cbn [cif_dev].
    iExists pn, gp, w, A, X. iFrame "Htk2". iLeft. iFrame "Hw Hlb Hu". by iPureIntro.
  Qed.

  (* ---- the tree, paid ---- *)
  Theorem cif_catf_paid (f : list (bv 8)) (xs ds : list (list (bv 8)))
      (files : list (bv 8) -> option (list (bv 8))) :
    uname f -> dp_in (kds.*1) {[0%nat]} ->
    (files f = Some L /\ cat_dg_open f ∈ xs /\ [] ∈ ds /\ cat_dg_write ∈ ds)
    \/ (files f = None /\ cat_dg_open f ∈ xs) ->
    env_res N P cif_iface (catp_env (DProd [L; []] xs ds) files [f]) {[0%nat]} -∗
    tree_pay N P (cat_tree [sb "cat"; f]).
  Proof using .
    intros Hf Hdp Hc. iIntros "H".
    assert (Hconf : conforms (catp_env (DProd [L; []] xs ds) files [f]) (cat_tree [sb "cat"; f])).
    { destruct Hc as [(Hs & Hx & Hn & Hw) | (Hs & Hx)].
      - apply (cat_file_prod_conforms_gen f L); [exact Hs | by left | by right; left
                                                | exact Hx | exact Hn | exact Hw].
      - apply (cat_file_prod_absent_conforms_gen f); [exact Hs | by right; left | exact Hx]. }
    iApply (tree_pay_of_conforms_p N P cif_iface _ _ _ Hconf (cat_tree_safe _ _) Hdp with "H").
  Qed.
End UkCatFIface.
