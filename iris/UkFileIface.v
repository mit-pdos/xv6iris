(* ===================================================================== *)
(* UkFileIface.v -- THE FILE APPLICATION'S ENDPOINT INTERFACE: one         *)
(* [UkHandler.ep_ifaceP] from the console ([UkConsOut]) and the file       *)
(* ([UkFileDev]), which [UkFileEntries] spends through the once-glue     *)
(* [UkHandler.tree_pay_of_conforms_p] to pay cat f / echo > f / echo      *)
(* (program-specs cut 4(c), cut 5 lane D).                                *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4b-SS3.4e.             *)
(*                                                                        *)
(* THE REGISTRY IS GHOST STATE.  A device is a natural number in the pure *)
(* layer; what it IS -- the console at the ROUND [(v, I)] owing one of    *)
(* the codes [C] it was lent ([FDCons v I C]), the file `f` held at a     *)
(* standard slot for writing at the LINE [ws] ([FDFile i γo ws]), or an   *)
(* input on `f` ([FDIn s i γo]: at a tail handle, or with [s] set at a    *)
(* STANDARD slot the ledger names) -- is a token [fif_tok d q v] in one   *)
(* camera.  [ei_fds] holds the POOL (the whole token of every number no   *)
(* device is registered at) and HALF of the token of every registered    *)
(* number; the device's resource holds the other half.  An open mints the *)
(* token of a fresh number out of the pool, a close of the last           *)
(* descriptor of an UNPROTECTED device gives it back.                      *)
(*                                                                        *)
(* THE EXIT RETURNS THE ASSEMBLY'S POSTCONDITION (SS3.4e).  The exit       *)
(* payload is not held up front: [ei_fds] is the CORE ([fif_core]: the    *)
(* ledger, the cwd, the registry, the handles, the deed [fif_dq] -- at a *)
(* FIXED fraction and content [fdq r qf sf], or none at a redirect -- the  *)
(* application's facts) beside                                            *)
(* the EXIT WAND [fif_exit_k], universal over the final state, which the  *)
(* round supplies and the exit applies to the final core, files and      *)
(* drained devices.  The round's indices are PINNED in the registry: the  *)
(* entry devices [D0] have the values [w0] throughout ([fif_ok]'s last    *)
(* clause), so the wand finds the console at the round's [(v, I, C)] and *)
(* the file at its [(i, γo, ws)].  The glue lemmas prove the wand from   *)
(* the landed entries' payloads: [fif_exit_k_cat] from                    *)
(* [UCatLend.catq_cat]'s wand (the drained console names a code of        *)
(* [RCRan; RCNoOpen], and its body's length is [UCatOut.cat_out_len]),    *)
(* [fif_exit_k_redir] from [UEchoFile.ef_exit]'s; echo at the console's   *)
(* is [UkFileEntries.fif_exit_k_echo_cons_d].                             *)
(*                                                                        *)
(* THE PROTECTED DEVICES.  A close of an entry device's last descriptor  *)
(* would drop the very cursor the wand needs, so the record's [Dp] is     *)
(* [D0] here: such a close is a SHARED close ([fif_close_shared]: the     *)
(* ledger slot closes, the device stays registered and with the handler) *)
(* and the exit finds every entry device among the drained ones          *)
(* ([UkHandler.dom_ok_p]).  So [fif_ok]'s registration clause reads: a   *)
(* registered device is bound or protected.                              *)
(*                                                                        *)
(* THE DEED LIVES IN THE CORE, not in [ei_files]: the read law receives  *)
(* no files, and [UkFileDev.file_in] needs the deed's fraction at every  *)
(* read.  [fif_filesr] is the pure scope ([f] is the one path described, *)
(* [files f] is the deed's content); an input device holds the program's *)
(* half of the offset ([UserOff.uoff]) and the deed is lent to each leaf *)
(* from the core and comes straight back, at [qf] throughout.  The       *)
(* console device remembers its codes ([UkConsOut.cons_dev_atc]).         *)
(*                                                                        *)
(* ...UNLESS A REGISTERED DEVICE HOLDS IT (lane DEED-SPLIT).  At a        *)
(* redirect the child's whole share of the deed ([AppFile.fown], the      *)
(* holder's half) rides in the write device's cursor ([UkFileDev.         *)
(* file_out] -> [FileWrite.file_wq]) and the claim holds the other half,  *)
(* so the core can hold no fraction.  The MODE [fif_wr D0 w0] -- an entry *)
(* device is `f` held for writing -- is read off the pinned indices (an   *)
(* open mints only inputs, so the write devices are the entry ones): in   *)
(* it the core's [fif_dq] is [emp], the console-node credential the read  *)
(* leaves take is [True] ([fif_cred]), the scope is empty and no input    *)
(* exists ([fif_filesr], [fif_in] carry the read mode), so no read and no *)
(* open can be asked for.                                                 *)
(*                                                                        *)
(* WHAT IS NOT, as a section hypothesis at the narrowest refused case:    *)
(*                                                                        *)
(*   Nothing, any more.  The truncating open of an absent `f` closed       *)
(*   kernel-side (TRUNC-PERMIT: the plain surface's permit tied to the     *)
(*   walk's terminal), and the zero-length write at an INPUT -- a tail    *)
(*   handle, or the read-only standard slot of [FDIn true] -- closed off  *)
(*   row 16's return blanket at count 0 ([fif_nil_in], lane NIL-RET).      *)
(*   At the console: [fif_cons_nil]; at the file held for writing:        *)
(*   [fif_file_nil] over [UkFileDev.file_write_nil].                       *)
(*                                                                        *)
(* THE TAINT PAYS ANY DISCIPLINED TREE: [UkFreeHandler.fh_taint_pays] at  *)
(* [T := file_taint c]; the payload the free handler needs comes from the *)
(* persistent wand [file_taint c -* ukn_pay N (-1)] in [fif_env], which   *)
(* every landed entry already takes.                                      *)
(*                                                                        *)
(* AND AT ECHO: [UkEchoTree.echo_prog] names all five stubs at echo's own *)
(* addresses, so SS5 instantiates the record at echo's program with no  *)
(* stub hypothesis and no other.                                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From Stdlib Require Import FunctionalExtensionality.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import ProgTree UkTree UkStub.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi UserBits.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import FdSlots UserFd UserCwd.
Require Import UserHeap UserPerm UserPtTree.
Require Import ProcGeom.
Require Import CtxIdDefs.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst UexecExecMint.
Require Import UsysMemOk.
Require Import SpecSysRead.            (* [sys_rw_count] *)
Require Import SpecConsolewrite UkWriteLeaf.  (* [cons_out_chain], the console write rows *)
Require Import ConsoleInv.             (* [CONSOLE] *)
Require Import FsCfg.
Require Import AppCfg AppInv.
Require Import FsInitPin FsShPin FsEchoPin FsCatPin FsGrepPin.
Require Import EchoDisc EchoOut LineWords.
Require Import FileState.              (* [echo_chunks] *)
Require Import AppFile AppFileCons FileOpen.
Require Import UserOff.
Require Import UkFileOpen.
Require Import FileWrite UEchoFile.
Require Import FsImg FsImgCheck.
Require Import SysOpenDefs.
Require Import LineModel LineModelInst FileDisc GenOut FileOut.
Require Import FileLinks FileLinksLine FileLinkGen.   (* [file_links], [f0w], [file_params] *)
Require Import UkConsOut UkFileDev.
Require Import UkHandler UkFreeHandler ProgTreeFile.
Require Import GenLinksLine LineModelLinks FileHooks.   (* [gwc_post], [lm_body], [fline] *)
Require Import UCatOut UCatLend.          (* [cch], [catq_cat]: the round's cat payload *)
Require Import UCodeCat UkCatTree.
Require Import UCodeEcho UkEchoTree.   (* echo's instance: [echo_prog] *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE REGISTRY                                                      *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  0.  THE REGISTRY                                                      *)
(* ===================================================================== *)

(* what a device is: the console at its round and codes, `f` held for
   writing at a standard slot at its line, or an input on `f` *)
Inductive fdev :=
  | FDCons (v : era_pins) (I : list (bv 8)) (C : list nat)
  | FDFile (i : Z) (γo : gname) (ws : wordline)
  | FDIn (s : bool) (i : Z) (γo : gname).

Definition fifRegR := discrete_funUR (fun _ : nat => optionUR (dfrac_agreeR (leibnizO fdev))).
Class fifRegG (Σ : gFunctors) := FifRegG { fif_reg_inG :: inG Σ fifRegR }.
Definition fifRegΣ : gFunctors := #[GFunctor fifRegR].
Global Instance subG_fifRegΣ {Σ} : subG fifRegΣ Σ -> fifRegG Σ.
Proof. solve_inG. Qed.

(* the pool: the whole token of every number outside [B], at [w] *)
Definition fif_pool (B : gset nat) (w : nat -> fdev) : fifRegR :=
  fun d => if decide (d ∈ B) then None
           else Some (to_dfrac_agree (DfracOwn 1) (w d : leibnizO fdev)).

Definition fif_single (d : nat) (q : Qp) (v : fdev) : fifRegR :=
  discrete_fun_singleton d (Some (to_dfrac_agree (DfracOwn q) (v : leibnizO fdev))).

Lemma fif_dfa_valid (v : fdev) : ✓ (to_dfrac_agree (DfracOwn 1) (v : leibnizO fdev)).
Proof. split; [apply dfrac_valid_own; reflexivity | done]. Qed.

Lemma fif_pool_valid (B : gset nat) (w : nat -> fdev) : ✓ fif_pool B w.
Proof.
  intros d. rewrite /fif_pool. case_decide; [done |].
  apply Some_valid, fif_dfa_valid.
Qed.

Lemma fif_pool_take (B : gset nat) (w : nat -> fdev) (d : nat) :
  d ∉ B -> fif_pool B w ≡ fif_pool ({[d]} ∪ B) w ⋅ fif_single d 1 (w d).
Proof.
  intros Hd x. rewrite discrete_fun_lookup_op /fif_pool /fif_single.
  destruct (decide (x = d)) as [-> | Hne].
  - rewrite discrete_fun_lookup_singleton.
    rewrite decide_False; [| exact Hd]. rewrite decide_True; [| set_solver].
    by rewrite left_id.
  - rewrite discrete_fun_lookup_singleton_ne; [| congruence]. rewrite right_id.
    destruct (decide (x ∈ B)) as [Hx | Hx];
      [rewrite decide_True; [done | set_solver] | rewrite decide_False; [done | set_solver]].
Qed.

Lemma fif_pool_ext (B B' : gset nat) (w w' : nat -> fdev) :
  B = B' -> (forall x, x ∉ B -> w x = w' x) -> fif_pool B w = fif_pool B' w'.
Proof.
  intros <- Hw.
  assert (H : forall x, fif_pool B w x = fif_pool B w' x).
  { intros x. rewrite /fif_pool. case_decide as Hx; [reflexivity |]. by rewrite (Hw x Hx). }
  exact (functional_extensionality _ _ H).
Qed.

Lemma fif_pool_update (B : gset nat) (w : nat -> fdev) (v : fdev) :
  fif_pool B w ~~> fif_pool B (fun _ => v).
Proof.
  apply discrete_fun_update. intros a. rewrite /fif_pool.
  case_decide; [reflexivity |].
  apply option_update, cmra_update_exclusive, fif_dfa_valid.
Qed.

(* the files the application describes: `f` -- the pure [FileDisc.files_of]
   (cut C9b); this name is kept for the file application's statements *)
Definition fif_files (s : option (list (bv 8))) : list (bv 8) -> option (list (bv 8)) :=
  files_of s.

Lemma fif_files_f (s : option (list (bv 8))) : fif_files s fname_f = s.
Proof. unfold fif_files. exact (files_of_f s). Qed.

(* the row a descriptor's device demands of it *)
Definition fif_row (ov : option fdev) (fd : Z) (l : list fdstate) : Prop :=
  match ov with
  | Some (FDCons _ _ _) => fd < Z.of_nat NSTD
                   /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdDevice CONSOLE))
  | Some (FDFile i γo _) => fd < Z.of_nat NSTD
                   /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdInode i γo OffHeld))
  | Some (FDIn true i γo) => fd < Z.of_nat NSTD
                   /\ l !! Z.to_nat fd = Some (FdOpen true false (FdInode i γo OffHeld))
  | Some (FDIn false _ _) => Z.of_nat NSTD <= fd
  | None => False
  end.

(* THE MODE: an entry device is `f` held for WRITING (a redirect).  Then
   the child's whole share of the deed rides in that device's cursor
   ([UkFileDev.file_out], [FileWrite.file_wq]'s [fown]) and the core holds
   none; otherwise the core holds the deed at its pinned fraction.  The
   registered write devices are exactly the entry ones (an open mints only
   inputs), so this reads the pinned indices, never the registry. *)
Definition fdev_wr (v : fdev) : bool :=
  match v with FDFile _ _ _ => true | _ => false end.

Definition fif_wr (D0 : list nat) (w0 : nat -> fdev) : bool :=
  existsb (fun d => fdev_wr (w0 d)) D0.

Lemma fif_wr_0 (D0 : list nat) (w0 : nat -> fdev) :
  D0 = [0%nat] -> fif_wr D0 w0 = fdev_wr (w0 0%nat).
Proof. intros ->. cbn [fif_wr existsb]. by rewrite orb_false_r. Qed.

(* the slot a descriptor other than [k]'s names is not [k] *)
Lemma fif_slot_ne (k : nat) (fd : Z) : 0 <= fd -> fd <> Z.of_nat k -> k <> Z.to_nat fd.
Proof.
  intros H0 Hne Heq. apply Hne. symmetry. rewrite Heq. apply Z2Nat.id. exact H0.
Qed.

(* THE PURE HALF OF [ei_fds]: the binding against the ledger [l] and the
   registry's values [vs], with the entry devices [D0] at their values
   [w0] throughout (a registered device is bound or protected) *)
Definition fif_ok (D0 : list nat) (w0 : nat -> fdev) (fdm : fdmap) (l : list fdstate)
    (vs : gmap nat fdev) : Prop :=
  (forall fd d, fdm !! fd = Some d -> 0 <= fd < Z.of_nat NOFILE)
  /\ (forall fd d, fdm !! fd = Some d -> fif_row (vs !! d) fd l)
  /\ (forall d, d ∈ dom vs -> (exists fd, fdm !! fd = Some d) \/ d ∈ D0)
  /\ (forall fd d, fdm !! fd = Some d -> d ∈ dom vs)
  /\ (forall fd fd' d s i γo, fdm !! fd = Some d -> fdm !! fd' = Some d ->
        vs !! d = Some (FDIn s i γo) -> fd = fd')
  /\ (forall d, d ∈ D0 -> vs !! d = Some (w0 d)).

Section fif_ok_lemmas.
  Context (D0 : list nat) (w0 : nat -> fdev).

  Lemma fif_ok_lookup fdm l vs fd d :
    fif_ok D0 w0 fdm l vs -> fdm !! fd = Some d -> exists v, vs !! d = Some v.
  Proof using .
    intros (_ & _ & _ & H4 & _) Hfd. apply elem_of_dom. exact (H4 fd d Hfd).
  Qed.

  Lemma fif_ok_D0 fdm l vs d :
    fif_ok D0 w0 fdm l vs -> d ∈ D0 -> vs !! d = Some (w0 d).
  Proof using . intros (_ & _ & _ & _ & _ & H6). exact (H6 d). Qed.

  (* the two registration clauses after a fresh device is bound at a fresh
     descriptor *)
  Lemma fif_ok_reg_insert (fdm : fdmap) (vs : gmap nat fdev) (k : nat) (d : nat) (v : fdev) :
    (forall d, d ∈ dom vs -> (exists fd, fdm !! fd = Some d) \/ d ∈ D0) ->
    (forall fd d, fdm !! fd = Some d -> d ∈ dom vs) ->
    fdm !! Z.of_nat k = None ->
    (forall d', d' ∈ dom (<[d := v]> vs) ->
       (exists fd, <[Z.of_nat k := d]> fdm !! fd = Some d') \/ d' ∈ D0)
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

  Lemma fif_ok_open fdm l vs (k : nat) (d : nat) (i : Z) (γo : gname) :
    fif_ok D0 w0 fdm l vs -> (NSTD <= k < NOFILE)%nat ->
    fdm !! Z.of_nat k = None -> (forall fd', fdm !! fd' <> Some d) -> d ∉ D0 ->
    fif_ok D0 w0 (<[Z.of_nat k := d]> fdm) l (<[d := FDIn false i γo]> vs).
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6) Hk Hnone Hfr HD.
    destruct (fif_ok_reg_insert fdm vs k d (FDIn false i γo) H3 H4 Hnone) as [H3' H4'].
    split; [| split; [| split; [exact H3' | split; [exact H4' | split]]]].
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
      + intros _. lia.
      + rewrite lookup_insert_ne; [| congruence]. apply H1.
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
      + rewrite lookup_insert. intros [= <-]. rewrite lookup_insert. simpl. lia.
      + rewrite (lookup_insert_ne fdm); [| congruence]. intros Hfd.
        rewrite (lookup_insert_ne vs); [| intros ->; exact (Hfr fd Hfd)]. exact (H2 fd d' Hfd).
    - intros fd fd' d' s' i' γo'.
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
        apply (H5 fd fd' d' s' i' γo' Ha Hb).
    - intros d' Hd'. rewrite lookup_insert_ne; [exact (H6 d' Hd') |]. intros ->. done.
  Qed.

  (* every standard slot a descriptor names is OPEN, so a closed one is
     named by none: where the next open lands is free *)
  Lemma fif_ok_closed_fresh fdm l vs (k : nat) :
    fif_ok D0 w0 fdm l vs -> length l = NSTD -> l !! k = Some FdClosed ->
    fdm !! Z.of_nat k = None.
  Proof using .
    intros (_ & H2 & _ & H4 & _) Hlen Hk.
    destruct (fdm !! Z.of_nat k) as [d |] eqn:E; [exfalso | reflexivity].
    assert (Hd : exists v, vs !! d = Some v) by (apply elem_of_dom; exact (H4 _ _ E)).
    destruct Hd as [v Hv]. specialize (H2 _ _ E). rewrite Hv in H2.
    pose proof (lookup_lt_Some _ _ _ Hk) as Hkl.
    destruct v as [vc Ic Cc | i γo ws | [|] i γo]; simpl in H2.
    - destruct H2 as (_ & rb & Hl). rewrite Nat2Z.id in Hl. congruence.
    - destruct H2 as (_ & rb & Hl). rewrite Nat2Z.id in Hl. congruence.
    - destruct H2 as (_ & Hl). rewrite Nat2Z.id in Hl. congruence.
    - lia.
  Qed.

  (* the binding reads the ledger only at the standard slots the descriptors
     name *)
  Lemma fif_ok_ledger fdm l l' vs :
    fif_ok D0 w0 fdm l vs ->
    (forall fd d, fdm !! fd = Some d -> l' !! Z.to_nat fd = l !! Z.to_nat fd) ->
    fif_ok D0 w0 fdm l' vs.
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6) Hl. split; [exact H1 | split; [| exact (conj H3 (conj H4 (conj H5 H6)))]].
    intros fd d Hfd. specialize (H2 fd d Hfd). unfold fif_row in *. revert H2.
    destruct (vs !! d) as [[vc Ic Cc | i γo ws | [|] i γo] |]; intros H2; rewrite ?(Hl fd d Hfd); exact H2.
  Qed.

  (* ...and an open landing in the lowest CLOSED standard slot [k]: the new
     descriptor's row is the slot, the others are untouched *)
  Lemma fif_ok_open_std fdm l vs (k : nat) (d : nat) (i : Z) (γo : gname) :
    fif_ok D0 w0 fdm l vs -> length l = NSTD -> l !! k = Some FdClosed ->
    (forall fd', fdm !! fd' <> Some d) -> d ∉ D0 ->
    fif_ok D0 w0 (<[Z.of_nat k := d]> fdm) (<[k := FdOpen true false (FdInode i γo OffHeld)]> l)
      (<[d := FDIn true i γo]> vs).
  Proof using .
    intros Hok Hlen Hk Hfr HD.
    pose proof (fif_ok_closed_fresh fdm l vs k Hok Hlen Hk) as Hnone.
    pose proof (lookup_lt_Some _ _ _ Hk) as Hkl.
    destruct Hok as (H1 & H2 & H3 & H4 & H5 & H6).
    destruct (fif_ok_reg_insert fdm vs k d (FDIn true i γo) H3 H4 Hnone) as [H3' H4'].
    split; [| split; [| split; [exact H3' | split; [exact H4' | split]]]].
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> |].
      + intros _. unfold NSTD, NOFILE in *. lia.
      + rewrite lookup_insert_ne; [| congruence]. apply H1.
    - intros fd d'. destruct (decide (fd = Z.of_nat k)) as [-> | Hne].
      + rewrite lookup_insert. intros [= <-]. rewrite lookup_insert. simpl.
        split; [unfold NSTD in *; lia |]. rewrite Nat2Z.id. apply list_lookup_insert. exact Hkl.
      + rewrite (lookup_insert_ne fdm); [| congruence]. intros Hfd.
        rewrite (lookup_insert_ne vs); [| intros ->; exact (Hfr fd Hfd)].
        specialize (H2 fd d' Hfd). destruct (H1 fd d' Hfd) as [H0 _].
        pose proof (fif_slot_ne k fd H0 Hne) as Hkne.
        unfold fif_row in *. revert H2.
        destruct (vs !! d') as [[vc Ic Cc | i' γo' ws' | [|] i' γo'] |]; intros H2;
          rewrite ?(list_lookup_insert_ne l k (Z.to_nat fd)
                      (FdOpen true false (FdInode i γo OffHeld)) Hkne); exact H2.
    - intros fd fd' d' s' i' γo'.
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
        apply (H5 fd fd' d' s' i' γo' Ha Hb).
    - intros d' Hd'. rewrite lookup_insert_ne; [exact (H6 d' Hd') |]. intros ->. done.
  Qed.

  Lemma fif_not_shared fdm fd d :
    ~ fd_shared fdm fd d -> forall fd', fd' <> fd -> fdm !! fd' <> Some d.
  Proof using .
    intros Hns fd' Hne Hfd'. apply Hns. exists fd'. split; [| exact Hfd'].
    apply elem_of_dom. rewrite lookup_delete_ne; [| congruence]. by eexists.
  Qed.

  (* the close of an UNPROTECTED device's last descriptor unregisters it *)
  Lemma fif_ok_close fdm l vs fd d :
    fif_ok D0 w0 fdm l vs -> fdm !! fd = Some d -> ~ fd_shared fdm fd d -> d ∉ D0 ->
    fif_ok D0 w0 (delete fd fdm) l (delete d vs).
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6) Hfd Hns HD.
    pose proof (fif_not_shared fdm fd d Hns) as Hn.
    split; [| split; [| split; [| split; [| split]]]].
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
    - intros fa fb d' s' i' γo' Ha Hb Hv.
      apply lookup_delete_Some in Ha as [_ Ha]. apply lookup_delete_Some in Hb as [_ Hb].
      apply lookup_delete_Some in Hv as [_ Hv].
      exact (H5 fa fb d' s' i' γo' Ha Hb Hv).
    - intros d' Hd'. rewrite lookup_delete_ne; [exact (H6 d' Hd') |]. intros ->. done.
  Qed.

  (* ...and of a descriptor whose device stays: another one names it, or
     it is protected *)
  Lemma fif_ok_close_shared fdm l vs fd d :
    fif_ok D0 w0 fdm l vs -> fdm !! fd = Some d -> fd_shared_p D0 fdm fd d ->
    fif_ok D0 w0 (delete fd fdm) l vs.
  Proof using .
    intros (H1 & H2 & H3 & H4 & H5 & H6) Hfd Hsh. apply fd_shared_p_iff in Hsh.
    split; [| split; [| split; [| split; [| split; [| exact H6]]]]].
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
    - intros fa fb d' s' i' γo' Ha Hb Hv.
      apply lookup_delete_Some in Ha as [_ Ha]. apply lookup_delete_Some in Hb as [_ Hb].
      exact (H5 fa fb d' s' i' γo' Ha Hb Hv).
  Qed.
End fif_ok_lemmas.

(* the chunk a write at the line's cursor carries *)
Lemma fif_drop_cons {A : Type} `{!Inhabited A} (xs : list A) (b : nat) (y : A) (ys : list A) :
  drop b xs = y :: ys ->
  (b < length xs)%nat /\ xs !!! b = y /\ ys = drop (S b) xs.
Proof.
  intros Hd.
  assert (Hl : xs !! b = Some y).
  { rewrite <- (Nat.add_0_r b), <- lookup_drop, Hd. reflexivity. }
  split; [exact (lookup_lt_Some _ _ _ Hl) |]. split.
  - by apply list_lookup_total_correct.
  - replace (S b) with (b + 1)%nat by lia. rewrite <- drop_drop, Hd. reflexivity.
Qed.

(* a mode without O_CREATE, as the kernel reads it *)
Lemma fif_om_create (m : Z) :
  ~ mode_create m -> SysOpenDefs.om_create (mword_of_int m : mword 64) = false.
Proof.
  unfold mode_create, SysOpenDefs.om_create, om_arg. intros Hm.
  rewrite moi64_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_pow2_bits_low _ 32 9); [| lia].
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N 64) 9); [| lia].
  assert (Hl : Z.land m 512 = 0) by (destruct (Z.eq_dec (Z.land m 512) 0); [done | tauto]).
  pose proof (Z.land_spec m 512 9) as Hs. rewrite Hl Z.bits_0 in Hs.
  change (Z.testbit 512 9) with true in Hs. rewrite andb_true_r in Hs. by rewrite <- Hs.
Qed.


(* the deed's content, read off the scope's files *)
Lemma dst_some_of_snd (s : dst) (content : list (bv 8)) :
  snd <$> s = Some content -> exists i : Z, s = Some (i, content).
Proof. destruct s as [[i c] |]; simpl; [intros [= ->]; by exists i | discriminate]. Qed.

Lemma dst_none_of_snd (s : dst) : snd <$> s = None -> s = None.
Proof. destruct s as [[i c] |]; simpl; [discriminate | reflexivity]. Qed.

(* ===================================================================== *)
(*  1.  THE INSTANCE                                                      *)
(* ===================================================================== *)

Section UkFileIface.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !fifRegG Σ}.

  (* the file application: its console claim, its deed *)
  Context (g : file_gn) (r : file_names).
  Local Notation c := (fgn_cl g).
  Context (Heq : file_app = MkAppcfg file_names (file_pred c) r).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  (* the process, and ANY program instance with its five stubs *)
  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{HPc : !Persistent (up_code P)}.
  Context `{HNc : !ukn_const N}.
  Hypothesis Hsr : ⊢ stub_law N (up_code P) 5 (up_read P).
  Hypothesis Hsw : ⊢ stub_law N (up_code P) 16 (up_write P).
  Hypothesis Hso : ⊢ stub_law N (up_code P) 15 (up_open P).
  Hypothesis Hsc : ⊢ stub_law N (up_code P) 21 (up_close P).
  Hypothesis Hse : ⊢ exit_stub_law N (up_code P) (up_exit P).

  (* the registry's name *)
  Context (γreg : gname).

  Local Notation γfd := (ukn_fd N).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ------------------------------------------------------------------- *)
  (*  the registry's tokens                                               *)
  (* ------------------------------------------------------------------- *)

  Definition fif_tok (d : nat) (q : Qp) (v : fdev) : iProp Σ := own γreg (fif_single d q v).

  Lemma fif_tok_agree (d : nat) (q1 q2 : Qp) (v1 v2 : fdev) :
    fif_tok d q1 v1 -∗ fif_tok d q2 v2 -∗ ⌜v1 = v2⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite /fif_single discrete_fun_singleton_op discrete_fun_singleton_valid
      -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    by destruct Hv as [_ ?].
  Qed.

  Lemma fif_tok_halves (d : nat) (v : fdev) :
    fif_tok d 1 v ⊣⊢ fif_tok d (1/2) v ∗ fif_tok d (1/2) v.
  Proof using .
    rewrite /fif_tok -own_op /fif_single. f_equiv.
    rewrite (discrete_fun_singleton_op d). f_equiv.
    rewrite -Some_op /to_dfrac_agree -pair_op agree_idemp dfrac_op_own Qp.half_half //.
  Qed.

  Lemma fif_pool_own_take (B : gset nat) (w : nat -> fdev) (d : nat) :
    d ∉ B -> own γreg (fif_pool B w) ⊣⊢ own γreg (fif_pool ({[d]} ∪ B) w) ∗ fif_tok d 1 (w d).
  Proof using . intros Hd. rewrite /fif_tok -own_op -fif_pool_take //. Qed.

  (* a token of a registered device comes home to the pool *)
  Lemma fif_pool_give (vs : gmap nat fdev) (w : nat -> fdev) (d : nat) (v : fdev) :
    d ∈ dom vs ->
    own γreg (fif_pool (dom vs) w) -∗ fif_tok d 1 v -∗
    own γreg (fif_pool (dom (delete d vs)) (fun x => if decide (x = d) then v else w x)).
  Proof using .
    iIntros (Hd) "Hp Ht".
    set (w' := fun x => if decide (x = d) then v else w x).
    assert (Hw' : w' d = v) by (rewrite /w'; by case_decide).
    rewrite (fif_pool_own_take (dom (delete d vs)) w' d); [| rewrite dom_delete_L; set_solver].
    rewrite Hw'. iFrame "Ht".
    assert (HB : dom vs = {[d]} ∪ dom (delete d vs)).
    { rewrite dom_delete_L. apply set_eq. intros x. rewrite elem_of_union elem_of_singleton
        elem_of_difference elem_of_singleton. split; [| intros [-> | []]; done].
      intros Hx. destruct (decide (x = d)); [by left | by right]. }
    assert (Hww : forall x, x ∉ dom vs -> w x = w' x).
    { intros x Hx. unfold w'. case_decide as Hxd; [| done]. subst x. done. }
    rewrite (fif_pool_ext (dom vs) ({[d]} ∪ dom (delete d vs)) w w' HB Hww). done.
  Qed.

  (* THE ROUND'S INDICES, PINNED: the entry devices and their values (a
     protected device is never an input), the deed's fraction and content *)
  Context (D0 : list nat) (w0 : nat -> fdev).
  Context (qf : Qp) (sf : dst).

  (* ------------------------------------------------------------------- *)
  (*  the resources                                                       *)
  (* ------------------------------------------------------------------- *)

  (* THE READ SIDE'S TWO PIECES, held only off the write mode ([fif_wr]):
     the deed at the pinned fraction and content, and the console-node
     credential the read leaves take.  At a redirect the child's share of
     the deed is the write device's, and nothing can read. *)
  Definition fif_dq : iProp Σ := if fif_wr D0 w0 then emp%I else fdq r qf sf.

  Definition fif_cred : iProp Σ :=
    if fif_wr D0 w0 then True%I else (∃ jo : option Z, file_cons_cred c r jo)%I.

  Global Instance fif_cred_persistent : Persistent fif_cred.
  Proof using . rewrite /fif_cred. destruct (fif_wr D0 w0); apply _. Qed.

  Lemma fif_dq_rd : fif_wr D0 w0 = false -> fif_dq ⊣⊢ fdq r qf sf.
  Proof using . intros Hrd. by rewrite /fif_dq Hrd. Qed.

  Lemma fif_dq_wr : fif_wr D0 w0 = true -> ⊢ fif_dq.
  Proof using . intros Hwr. by rewrite /fif_dq Hwr. Qed.

  Lemma fif_cred_rd : fif_wr D0 w0 = false -> fif_cred ⊣⊢ ∃ jo : option Z, file_cons_cred c r jo.
  Proof using . intros Hrd. by rewrite /fif_cred Hrd. Qed.

  (* the application's persistent facts the device laws read, and the
     taint's payload: the wand every landed entry takes *)
  Definition fif_env : iProp Σ :=
    (□ (app_taint -∗ file_taint c) ∗ □ (file_taint c -∗ app_taint)
     ∗ □ (file_taint c -∗ ukn_pay N (-1))
     ∗ app_inv fsc_fs ∗ fif_cred)%I.

  Global Instance fif_env_persistent : Persistent fif_env.
  Proof using . rewrite /fif_env. apply _. Qed.

  (* the handle an input's TAIL descriptor holds (a standard slot's row is
     the ledger's) *)
  Definition fif_hdl (fd : Z) (ov : option fdev) : iProp Σ :=
    match ov with
    | Some (FDIn false i γo) =>
        UserFd.ufd γfd (Z.to_nat fd) (FdOpen true false (FdInode i γo OffHeld))
    | _ => emp
    end%I.

  (* a protected device is never a tail input: its close is a standard
     slot's *)
  Context (Hw0 : forall d, d ∈ D0 -> forall i γo, w0 d <> FDIn false i γo).

  (* =================================================================== *)
  (*  THE CONSOLE'S CLAIM, ABSTRACT (union.md, review item S5).  Every    *)
  (*  law from here to the record reads the claim only through the        *)
  (*  console device, [UkConsOut.cons_dev_atc] at a line model [M], its   *)
  (*  link parameters [Pm] and a persistent links bundle [LINKS] entailing *)
  (*  the three console leaves ([UkConsOutGen]'s pattern): the file       *)
  (*  application instantiates them at [file_links] (the glue below and   *)
  (*  [UkFileEntries]), the union's claim C9e' at its own record.         *)
  (* =================================================================== *)
  (* the registry's entry state: device 0 at its pinned value, every
     descriptor the environment names bound to it *)
  Lemma fif_ok_entry (fdm : fdmap) (l : list fdstate) :
    D0 = [0%nat] ->
    (forall fd d, fdm !! fd = Some d -> d = 0%nat) ->
    (forall fd d, fdm !! fd = Some d -> fif_row (Some (w0 0%nat)) fd l) ->
    (forall fd d, fdm !! fd = Some d -> 0 <= fd < Z.of_nat NOFILE) ->
    (forall s i γo, w0 0%nat <> FDIn s i γo) ->
    fif_ok D0 w0 fdm l {[0%nat := w0 0%nat]}.
  Proof using .
    intros HD0 Hd0 Hrow Hbnd Hnin. rewrite HD0.
    split; [exact Hbnd | split; [| split; [| split; [| split]]]].
    - intros fd d Hfd. rewrite (Hd0 fd d Hfd) lookup_singleton. exact (Hrow fd d Hfd).
    - intros d. rewrite dom_singleton_L elem_of_singleton. intros ->. right. constructor.
    - intros fd d Hfd. rewrite (Hd0 fd d Hfd) dom_singleton_L. by apply elem_of_singleton.
    - intros fd fd' d s i γo Hfd _ Hv. apply lookup_singleton_Some in Hv as [<- Hv].
      by destruct (Hnin s i γo).
    - intros d Hd. apply elem_of_list_singleton in Hd as ->. apply lookup_singleton.
  Qed.

  Section UkFileIfaceGen.
  Context (M : lmodel) (Pm : gen_params M).
  Context (LINKS : iProp Σ) {LINKS_pers : Persistent LINKS}.
  #[local] Existing Instance LINKS_pers.
  Context (LINKS_w : LINKS -∗ gl_w M Pm).
  Context (LINKS_blk : LINKS -∗ gl_blk M Pm).
  Context (LINKS_taint : LINKS -∗ gl_taint M Pm).
  Local Notation fcons_atc := (cons_dev_atc M Pm LINKS).

  (* the console at its round, remembering its codes *)
  Definition fif_out (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    (∃ (v : era_pins) (I : list (bv 8)) (C : list nat),
       fif_tok d (1/2) (FDCons v I C) ∗ fcons_atc C v I alts)%I.

  (* the file a redirect holds: the line's chunks from [b] on are owed *)
  Definition fif_out_ok (i : Z) (ws : wordline) : Prop :=
    i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO /\ i <> CAT_INO /\ i <> GREP_INO
    /\ Forall (fun ch => (length ch <= EchoDisc.line_max)%nat) (echo_chunks ws).

  Definition fif_outm (d : nat) (chunks : list (list (bv 8))) : iProp Σ :=
    (∃ (i : Z) (γo : gname) (ws : wordline), fif_tok d (1/2) (FDFile i γo ws)
       ∗ ∃ b : nat, ⌜chunks = drop b (echo_chunks ws)⌝ ∗ ⌜fif_out_ok i ws⌝
           ∗ file_out c r i γo ws b)%I.

  (* an input the process opened on `f`, at a tail handle or a standard
     slot: the program's half of the offset; the deed is the core's *)
  Definition fif_in (d : nat) (S : list (bv 8)) : iProp Σ :=
    (∃ (s : bool) (i : Z) (γo : gname) (p : nat), fif_tok d (1/2) (FDIn s i γo)
       ∗ ⌜fif_wr D0 w0 = false /\ exists content, sf = Some (i, content) /\ S = drop p content⌝
       ∗ uoff γo p)%I.

  Definition fif_dev (d : nat) (x : dspec) : iProp Σ :=
    match x with
    | DOut alts => fif_out d alts | DOutH _ => False | DOutM cs => fif_outm d cs
    | DHalt => False | DIn Sin => fif_in d Sin | DInE _ => False | DInEnd => False
    | DCopy _ _ _ => False | DCopyEnd _ _ => False | DCopyHalt => False
    | DProd _ _ _ => False | DProdHalt _ => False
    end%I.

  (* the scope: `f` is the one path described, at the deed's content, and
     only off the write mode (a redirect's scope is empty) *)
  Definition fif_filesr (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      : iProp Σ :=
    (⌜forall p, p ∈ paths -> p = fname_f /\ fif_wr D0 w0 = false⌝
     ∗ ⌜files fname_f = snd <$> sf⌝)%I.

  Global Instance fif_filesr_persistent files paths : Persistent (fif_filesr files paths).
  Proof using . rewrite /fif_filesr. apply _. Qed.

  (* THE CORE: the process's resources at its ledger, the registry's values
     and its pool, and the deed *)
  Definition fif_core (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev)
      (w : nat -> fdev) : iProp Σ :=
    (UserFd.ustd γfd l ∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO
     ∗ ⌜fif_ok D0 w0 fdm l vs⌝
     ∗ own γreg (fif_pool (dom vs) w)
     ∗ ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v)
     ∗ ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))
     ∗ fif_dq
     ∗ fif_env)%I.

  (* THE EXIT WAND: the round's payload, from the final core, files and
     drained devices, with every entry device among them *)
  Definition fif_exit_k : iProp Σ :=
    (∀ (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) (w : nat -> fdev)
       (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
       (dv : nat -> dspec) (ds : gset nat),
       ⌜forall d, d ∈ ds -> drained (dv d)⌝ -∗ ⌜dom_ok_p D0 fdm ds⌝ -∗
       fif_core fdm l vs w -∗ fif_filesr files paths -∗
       ([∗ set] d ∈ ds, fif_dev d (dv d)) -∗ ukn_pay N (-1))%I.

  (* [ei_fds], at its ledger, its registry's values and its pool *)
  Definition fif_fds_at (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev)
      (w : nat -> fdev) : iProp Σ :=
    (fif_core fdm l vs w ∗ fif_exit_k)%I.

  Definition fif_fds (fdm : fdmap) : iProp Σ :=
    (∃ (l : list fdstate) (vs : gmap nat fdev) (w : nat -> fdev), fif_fds_at fdm l vs w)%I.

  (* THE TAINT: the free handler's, at the application's flag *)
  Definition fif_taint (held : gset Z) : iProp Σ := fh_taint (file_taint c) N held.

  (* ------------------------------------------------------------------- *)
  (*  small facts                                                         *)
  (* ------------------------------------------------------------------- *)

  Definition fif_hf (vs : gmap nat fdev) (d : nat) : option fdstate :=
    match vs !! d with
    | Some (FDIn false i γo) => Some (FdOpen true false (FdInode i γo OffHeld))
    | _ => None
    end.

  Lemma fif_hdls_hm (fdm : fdmap) (vs : gmap nat fdev) :
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))
    ⊣⊢ [∗ map] fd ↦ st ∈ omap (fif_hf vs) fdm, UserFd.ufd γfd (Z.to_nat fd) st.
  Proof using .
    rewrite big_sepM_omap. apply big_sepM_proper. intros fd d _.
    rewrite /fif_hdl /fif_hf. destruct (vs !! d) as [[vc Ic Cc | i γo ws | [|] i γo] |]; done.
  Qed.

  Lemma fif_held_ok_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) :
    fif_ok D0 w0 fdm l vs -> fh_held_ok (dom fdm) l (omap (fif_hf vs) fdm).
  Proof using .
    intros Hok fd Hfd. apply elem_of_dom in Hfd as [d Hd].
    pose proof Hok as (H1 & H2 & _). split; [exact (H1 fd d Hd) |].
    pose proof (H2 fd d Hd) as Hr.
    destruct (vs !! d) as [[vc Ic Cc | i γo ws | [|] i γo] |] eqn:Ev; simpl in Hr.
    - left. destruct Hr as (Hs & rb & Hl). split; [exact Hs |].
      eexists; split; [exact Hl | discriminate].
    - left. destruct Hr as (Hs & rb & Hl). split; [exact Hs |].
      eexists; split; [exact Hl | discriminate].
    - left. destruct Hr as (Hs & Hl). split; [exact Hs |].
      eexists; split; [exact Hl | discriminate].
    - right. split; [exact Hr |]. rewrite lookup_omap Hd /= /fif_hf Ev. by eexists.
    - done.
  Qed.

  Lemma fif_app_sup : file_taint c -∗ app_sup.
  Proof using Heq.
    iIntros "#HT". rewrite /AppInv.app_sup. rewrite Heq. cbn [app_pred app_run].
    iApply (AppFile.file_sup_of_taint c r with "HT").
  Qed.

  (* the taint, out of what a law holds at a taint arm *)
  Lemma fif_taint_of_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) :
    fif_ok D0 w0 fdm l vs ->
    file_taint c -∗ fif_env -∗ UserFd.ustd γfd l -∗
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗ fif_taint (dom fdm).
  Proof using Heq.
    intros Hok. iIntros "#Ht #(Hbr & Hk & Hpay & Hinv & Hm) Hstd Hhs". rewrite /fif_taint /fh_taint.
    iFrame "Ht Hk". iSplitR; [iIntros "!> HT"; iApply (fif_app_sup with "HT") |].
    iSplitR; [iApply ("Hpay" with "Ht") |].
    iExists l, (omap (fif_hf vs) fdm). iFrame "Hstd". iSplit.
    - iPureIntro. by apply fif_held_ok_fds.
    - by rewrite fif_hdls_hm.
  Qed.

  (* the value the registry holds for a registered device, read off its token *)
  Lemma fif_toks_agree (vs : gmap nat fdev) (d : nat) (v v' : fdev) (q : Qp) :
    vs !! d = Some v ->
    ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v) -∗ fif_tok d q v' -∗
    ⌜v = v'⌝ ∗ ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v) ∗ fif_tok d q v'.
  Proof using .
    iIntros (Hv) "Hm Ht".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hv with "Hm") as "[Hx Hcl]".
    iDestruct (fif_tok_agree with "Hx Ht") as %->.
    iFrame "Ht". iSplit; [done |]. iApply ("Hcl" with "Hx").
  Qed.

  (* a descriptor the kernel just handed back is none the process names *)
  Lemma fif_fresh_fd (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) (k : nat)
      (st : fdstate) :
    fif_ok D0 w0 fdm l vs -> (NSTD <= k)%nat ->
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗ UserFd.ufd γfd k st -∗
    ⌜fdm !! Z.of_nat k = None⌝ ∗ ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))
    ∗ UserFd.ufd γfd k st.
  Proof using .
    intros Hok Hk. iIntros "Hm Hh".
    destruct (fdm !! Z.of_nat k) as [d |] eqn:E; [| by iFrame].
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok E) as [v Hv].
    pose proof Hok as (_ & H2 & _). specialize (H2 _ _ E). rewrite Hv in H2.
    destruct v as [vc Ic Cc | i γo ws | [|] i γo];
      [destruct H2 as [Hlt _]; lia | destruct H2 as [Hlt _]; lia
       | destruct H2 as [Hlt _]; lia |].
    iDestruct (big_sepM_lookup_acc _ _ _ _ E with "Hm") as "[Hx _]".
    rewrite /fif_hdl Hv Nat2Z.id.
    iDestruct "Hx" as "[Hx _]". iDestruct "Hh" as "[Hh _]".
    iDestruct (ghost_map_elem_ne with "Hx Hh") as %Hne. by destruct Hne.
  Qed.

  Lemma fif_ans_ok (l : list fdstate) (ret : mword 64) :
    uk_open_taint_fd γfd l ret -∗ ⌜bv_signed ret = -1 \/ 0 <= bv_signed ret⌝.
  Proof using .
    clear Hw0 D0 w0 qf sf.
    rewrite /uk_open_taint_fd. iIntros "[Hal | [%Hr _]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb _]". destruct Hb as (Hr & Hfdlt & _).
      iPureIntro. right. rewrite Hr bvs_moi_small; [lia |].
      unfold NOFILE in Hfdlt.
      assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia.
    - iPureIntro. left. rewrite Hr. exact fdev_m1.
  Qed.

  Lemma fif_open_taint (l : list fdstate) (ret : mword 64) (fdm : fdmap)
      (vs : gmap nat fdev) :
    length l = NSTD -> fif_ok D0 w0 fdm l vs ->
    file_taint c -∗ fif_env -∗
    uk_open_taint_fd γfd l ret -∗
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗
    fif_taint (open_held fdm (bv_signed ret)).
  Proof using Heq GEN.
    intros Hlen Hok. iIntros "#Htn #(Hbr & Hk & Hpay & Hinv & Hm) Hof Hhs".
    rewrite /uk_open_taint_fd.
    iDestruct "Hof" as "[Hal | [%Hr Hstd]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]". destruct Hb as (Hr & Hfdlt & _).
      assert (Hsig : bv_signed ret = Z.of_nat fd).
      { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
        assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia. }
      rewrite Hsig /open_held decide_True; [| lia].
      rewrite fif_hdls_hm.
      pose proof (fif_held_ok_fds fdm l vs Hok) as Hho.
      rewrite /fif_taint /fh_taint. iFrame "Htn Hk".
      iSplitR; [iIntros "!> HT"; iApply (fif_app_sup with "HT") |].
      iSplitR; [iApply ("Hpay" with "Htn") |].
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + (* the lowest closed standard slot *)
        iDestruct (ualloc_std γfd l fd k0 _ Elc with "Hal") as "[%Hfk Hstd]". subst fd.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        pose proof (lookup_lt_Some _ _ _ Hk0) as Hk0l.
        iExists (<[k0 := FdOpen rd wr t]> l), (omap (fif_hf vs) fdm). iFrame "Hstd Hhs".
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
      + (* a fresh tail handle *)
        iDestruct (ualloc_hi γfd l fd (FdOpen rd wr t) Elc with "Hal")
          as "(%Hhi & Hstd & Hh)".
        iDestruct (fh_hm_fresh N with "Hhs Hh") as "(%Hfr & Hhs & Hh)".
        iExists l, (<[Z.of_nat fd := FdOpen rd wr t]> (omap (fif_hf vs) fdm)). iFrame "Hstd".
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
      iApply (fif_taint_of_fds fdm l vs Hok with "Htn [] Hstd Hhs").
      iFrame "Hbr Hk Hpay Hinv Hm".
  Qed.

  (* the deed lent to an input's leaf, and back: [UkFileDev.file_in] out of
     the core's deed and the device's offset half *)
  Lemma fif_in_file_in (d : nat) (S : list (bv 8)) :
    fif_in d S -∗ fif_dq -∗
    ∃ (s : bool) (i : Z) (γo : gname) (content : list (bv 8)),
      ⌜fif_wr D0 w0 = false⌝ ∗ ⌜sf = Some (i, content)⌝ ∗ fif_tok d (1/2) (FDIn s i γo)
      ∗ file_in r i γo qf content S.
  Proof using .
    iIntros "Hin Hd". iDestruct "Hin" as (s i γo p) "(Htk & %Hc & Hu)".
    destruct Hc as (Hrd & content & Hsf & HS). iExists s, i, γo, content.
    iSplit; [done |]. iSplit; [done |].
    iFrame "Htk". iExists p. iFrame "Hu". iSplit; [iPureIntro; exact HS |].
    rewrite -Hsf. iEval (rewrite (fif_dq_rd Hrd)) in "Hd". iExact "Hd".
  Qed.

  Lemma fif_in_of_file_in (d : nat) (S content : list (bv 8)) (s : bool) (i : Z)
      (γo : gname) :
    fif_wr D0 w0 = false -> sf = Some (i, content) ->
    fif_tok d (1/2) (FDIn s i γo) -∗ file_in r i γo qf content S -∗
    fif_in d S ∗ fif_dq.
  Proof using .
    intros Hrd Hsf. iIntros "Htk Hin". iDestruct "Hin" as (p) "(%HS & Hu & Hd)".
    rewrite (fif_dq_rd Hrd) Hsf. iFrame "Hd". iExists s, i, γo, p. iFrame "Htk Hu". iPureIntro.
    split; [exact Hrd | by exists content].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE FREE HANDLER, and the exit                                      *)
  (* ------------------------------------------------------------------- *)

  Definition fif_taint_pays := fh_taint_pays (file_taint c) N P Hsr Hsw Hso Hsc Hse.

  Lemma fif_exit (s : Z) (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (dv : nat -> dspec) (ds : gset nat) :
    (forall d, d ∈ ds -> drained (dv d)) ->
    dom_ok_p D0 fdm ds ->
    fif_fds fdm -∗ fif_filesr files paths -∗ ([∗ set] d ∈ ds, fif_dev d (dv d)) -∗
    ex_obl N P s.
  Proof using HNc Hse.
    intros Hdr Hdom. iIntros "Hfds Hfiles Hdev".
    iDestruct "Hfds" as (l vs w) "[Hcore Hk]".
    iApply (fh_exit_pay N P Hse).
    iApply ("Hk" $! fdm l vs w files paths dv ds with "[%] [%] Hcore Hfiles Hdev");
      [exact Hdr | exact Hdom].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE LAWS                                                            *)
  (* ------------------------------------------------------------------- *)

  (* the core and the wand, reassembled *)
  Lemma fif_fds_of (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev) (w : nat -> fdev) :
    fif_ok D0 w0 fdm l vs ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
    own γreg (fif_pool (dom vs) w) -∗ ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v) -∗
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗ fif_dq -∗ fif_env -∗
    fif_exit_k -∗ fif_fds fdm.
  Proof using .
    intros Hok. iIntros "Hstd Hcwd Hpool Htoks Hhs Hdq #He Hk".
    iExists l, vs, w. iFrame "Hk Hstd Hcwd Hpool Htoks Hhs Hdq He". by iPureIntro.
  Qed.

  (* [ei_write] at the console: the device's slot is a console row *)
  Lemma fif_write (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    fif_fds fdm -∗ fif_out d alts -∗
    ((fif_fds fdm -∗ fif_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, fif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using LINKS_blk LINKS_pers LINKS_taint LINKS_w Hsw HPc.
    intros _ Hfd Ha Hpre. iIntros "Hfds Hout HK".
    iDestruct "Hout" as (v I C) "[Htk Hout]".
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v' Hv].
    iDestruct (fif_toks_agree vs d v' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v'.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (cons_write_gl_atc M Pm LINKS (LINKS_pers := LINKS_pers)
              LINKS_w LINKS_blk LINKS_taint
              N P Hsw C v I l k rb alts a bs K
              ltac:(unfold NSTD in *; lia) Hrow Ha Hpre with "Hstd Hout").
    iIntros "Hstd Hout". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[-Hout Htk] [Htk Hout]").
    - iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
    - iExists v, I, C. iFrame "Htk Hout".
  Qed.

  (* a ZERO-LENGTH write at the console: [UkConsOut.cons_write]'s walk at
     no bytes, where the chain is its own stop and the device [D] -- any
     resource -- comes back untouched *)
  Lemma fif_cons_nil (l : list fdstate) (fd : nat) (rb : bool) (D : iProp Σ)
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ D -∗ (UserFd.ustd γfd l -∗ D -∗ K 0) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw HPc.
    clear Hw0 D0 w0 qf sf. intros Hfd Hl. iIntros "Hstd Hd HK".
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
              (xfam_wr (fun _ : nat => (D ∗ emp)%I) (ukn_pay N))
              l tx dq 0 f Hsys Hal with "Hec Hrun [Hd] Hstd [Hsrc]").
    { iApply (uwrite_chain_sup_ret N (fun _ : nat => D) emp%I _ _ l fd rb CONSOLE Hi0 Hfd Hl).
      iIntros (Mh pm sz) "Hheap". iFrame "Hheap". iSplitR; [done |].
      rewrite Hcnt. cbn [cons_out_chain]. iExact "Hd". }
    { rewrite Ham1. iExact "Hsrc". }
    iIntros (h' ret Wv cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
    iDestruct (uwrite_no_short (fun _ : nat => (D ∗ emp)%I) (ukn_pay N) Wv ret (uvis_M Wv)
                 (uvis_fd Wv) cw' cs' l fd rb 0
                 ltac:(rewrite Hka0; exact Hi0)
                 Hfd Htk Hl
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

  (* a ZERO-LENGTH write at the file a redirect holds: the row is the held
     inode slot the registry names, and [UkFileDev.file_write_nil] answers
     0 or -1 with nothing lent -- the cursor is not even looked at *)
  Lemma fif_file_nil (fdm : fdmap) (fd : Z) (d : nat) (cs : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_outm d cs -∗
    ((fif_fds fdm -∗ fif_outm d cs -∗ K 0) ∧ (fif_fds fdm -∗ fif_outm d cs -∗ K (-1))) -∗
    wr_obl N P fd [] K.
  Proof using Hsw.
    intros Hfd. iIntros "Hfds Hout HK".
    iDestruct "Hout" as (i γo ws) "[Htk Hout]".
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (file_write_nil N P Hsw k l rb i γo K ltac:(unfold NSTD in *; lia) Hrow with "Hstd").
    iSplit; iIntros "Hstd".
    - iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hout Htk] [Htk Hout]").
      + iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
      + iExists i, γo, ws. iFrame "Htk Hout".
    - iDestruct "HK" as "[_ HK]". iApply ("HK" with "[-Hout Htk] [Htk Hout]").
      + iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
      + iExists i, γo, ws. iFrame "Htk Hout".
  Qed.

  (* [ei_write_m] at the file a redirect holds: chunk [b] of the line *)
  Lemma fif_write_m (fdm : fdmap) (fd : Z) (d : nat) (rest : list (list (bv 8)))
      (bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_outm d (bs :: rest) -∗
    ((fif_fds fdm -∗ fif_outm d rest -∗ K (Z.of_nat (length bs)))
     ∧ (fif_fds fdm -∗ fif_outm d rest -∗ K (-1))
     ∧ (∀ x, fif_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Heq Hsw.
    intros Hne Hfd. iIntros "Hfds Hout HK".
    iDestruct "Hout" as (i γo ws) "[Htk Hout]".
    iDestruct "Hout" as (b) "(%Hch & %Hwok & Hout)".
    destruct (fif_drop_cons _ _ _ _ (eq_sym Hch)) as (Hb & Hbs & Hrest).
    pose proof Hwok as (Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hlm).
    assert (Hbl : (length bs <= EchoDisc.line_max)%nat).
    { rewrite <- Hbs. apply (proj1 (Forall_lookup _ _) Hlm b).
      apply list_lookup_lookup_total_lt. exact Hb. }
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
    iDestruct "He" as "#(Hbr & Hrb & Hpay & Hinv & Hm)".
    iAssert fif_env with "[]" as "#He"; [by iFrame "Hbr Hrb Hpay Hinv Hm" |].
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
    iApply (file_write c r Heq N P Hsw k l rb i γo ws b b bs K
              ltac:(unfold NSTD in *; lia) Hrow Hb ltac:(lia) Hbs
              ltac:(destruct bs; [done | simpl; lia]) Hbl Hi1 Hi2 Hi3 Hi4 Hi5
              with "Hbr Hinv Hstd Hout").
    iSplit.
    - iIntros "Hstd Hout". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Htk Hout] [Htk Hout]").
      + iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
      + iExists i, γo, ws. iFrame "Htk". iExists (S b). iFrame "Hout". by iPureIntro.
    - iIntros "Hstd Hout". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Htk Hout] [Htk Hout]").
      + iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
      + iExists i, γo, ws. iFrame "Htk". iExists (S b). iFrame "Hout". by iPureIntro.
  Qed.

  (* [ei_read] at an input: the token names the inode and the offset, and
     whether the descriptor is a tail handle or a standard slot the ledger
     holds; the deed is lent from the core and comes back *)
  Lemma fif_read (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        fif_fds fdm -∗ fif_in d S' -∗ K (RdBytes cb))
     ∧ (∀ x, fif_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Heq Hsr.
    intros Hn Hfd. iIntros "Hfds Hin HK".
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
    iDestruct (fif_in_file_in d Sin with "Hin Hdq") as (s i γo content) "(%Hrd & %Hsf & Htk & Hin)".
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hs. rewrite Hv in Hs. simpl in Hs.
    iDestruct "He" as "#(Hbr & Hrb & Hpay & Hinv & Hcr)".
    iAssert fif_env with "[]" as "#He"; [by iFrame "Hbr Hrb Hpay Hinv Hcr" |].
    iEval (rewrite (fif_cred_rd Hrd)) in "Hcr". iDestruct "Hcr" as (jo) "#Hm".
    destruct (Z_of_nat_complete fd H0) as [k ->].
    destruct s.
    - (* a standard slot: the ledger is the handle *)
      destruct Hs as (Hsk & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_read_std c r Heq N P Hsr k l false i γo qf jo content Sin n K
                ltac:(unfold NSTD in *; lia) Hrow Hn with "Hbr Hrb Hm Hinv Hstd Hin").
      iSplit.
      + iIntros (cb S') "%Hc Hstd Hin". iDestruct "HK" as "[HK _]".
        iDestruct (fif_in_of_file_in d S' content true i γo Hrd Hsf with "Htk Hin") as "[Hin Hdq]".
        iApply ("HK" $! cb S' with "[%] [-Hin] Hin"); [exact Hc |].
        iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
      + iIntros (x) "#Htn Hstd Hin". iDestruct "HK" as "[_ HK]". iApply "HK".
        iApply (fif_taint_of_fds fdm l vs Hok with "Htn He Hstd Hhs").
    - (* a tail handle *)
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hfd with "Hhs") as "[Hh Hcl]".
      iEval (rewrite /fif_hdl Hv) in "Hh". iEval (rewrite Nat2Z.id) in "Hh".
      iApply (file_read c r Heq N P Hsr k false i γo qf jo content Sin n K
                ltac:(lia) Hn with "Hbr Hrb Hm Hinv Hh Hin").
      iSplit.
      + iIntros (cb S') "%Hc Hh Hin". iDestruct "HK" as "[HK _]".
        iDestruct (fif_in_of_file_in d S' content false i γo Hrd Hsf with "Htk Hin") as "[Hin Hdq]".
        iApply ("HK" $! cb S' with "[%] [-Hin] Hin"); [exact Hc |].
        iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks [Hh Hcl] Hdq He Hk").
        iApply "Hcl". rewrite /fif_hdl Hv Nat2Z.id. iExact "Hh".
      + iIntros (x) "#Htn Hh Hin". iDestruct "HK" as "[_ HK]". iApply "HK".
        iAssert ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d))%I with "[Hh Hcl]" as "Hhs".
        { iApply "Hcl". rewrite /fif_hdl Hv Nat2Z.id. iExact "Hh". }
        iApply (fif_taint_of_fds fdm l vs Hok with "Htn He Hstd Hhs").
  Qed.

  (* [ei_open] for `f` present: the descriptor the LEDGER names -- the
     lowest closed standard slot, else a fresh tail handle -- with the
     token of a fresh device out of the pool; or -1; or the taint *)
  Lemma fif_open (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path content : list (bv 8)) (K : Z -> iProp Σ) :
    path ∈ paths -> files path = Some content ->
    fif_fds fdm -∗ fif_filesr files paths -∗
    ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm !! fd = None⌝ -∗
        (∀ d : nat, ⌜dev_fresh_p D0 fdm d⌝ -∗
           fif_fds (<[fd := d]> fdm) ∗ fif_in d content) -∗
        fif_filesr files paths -∗ K fd)
     ∧ (fif_fds fdm -∗ fif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ fif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path 0 K.
  Proof using Heq Hso.
    intros Hp Hf. iIntros "Hfds #Hfiles HK".
    iAssert (⌜(forall p, p ∈ paths -> p = fname_f /\ fif_wr D0 w0 = false)
              /\ files fname_f = snd <$> sf⌝)%I
      as %[Hpaths Hfs].
    { iDestruct "Hfiles" as "[%A %B]". by iPureIntro. }
    pose proof (Hpaths path Hp) as [-> Hrd].
    rewrite Hf in Hfs.
    destruct (dst_some_of_snd sf content (eq_sym Hfs)) as [i Hsf].
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hd & #He) Hk]".
    iDestruct "He" as "#(Hbr & Hrb & Hpay & Hinv & Hm)".
    iAssert fif_env with "[]" as "#He"; [by iFrame "Hbr Hrb Hpay Hinv Hm" |].
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen.
    iAssert (fdq r qf (Some (i, content))) with "[Hd]" as "Hd".
    { rewrite -Hsf. iEval (rewrite (fif_dq_rd Hrd)) in "Hd". iExact "Hd". }
    iPoseProof (fdq_split r (qf / 2) (qf / 2) (Some (i, content)) with "[Hd]") as "[Hd1 Hd2]".
    { rewrite Qp.div_2. iExact "Hd". }
    iAssert (□ (fdq r (qf / 2) (Some (i, content)) -∗ fdq r (qf / 2) (Some (i, content))
                -∗ fif_dq))%I as "#Hjoin".
    { iIntros "!> Ha Hb". iDestruct (fdq_join with "Ha Hb") as "Hd".
      rewrite Qp.div_2 (fif_dq_rd Hrd) Hsf. iExact "Hd". }
    iApply (file_open_present c r Heq N P Hso l FsImg.ROOTINO (qf / 2) (qf / 2) i content K
              eq_refl with "Hinv Hstd Hcwd Hd1 Hd2").
    iSplit; [| iSplit].
    - (* the handle, where the ledger says the allocation landed *)
      iIntros (fd γo) "%Hfdlt Hal Hcwd Hin Hd1".
      iDestruct "Hin" as (p) "(%Hp0 & Hu & Hd2)".
      iDestruct ("Hjoin" with "Hd1 Hd2") as "Hd".
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + (* the lowest closed standard slot: its row in the ledger *)
        iDestruct (ualloc_std γfd l fd k0 _ Elc with "Hal") as "[%Hfk Hstd]". subst fd.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        pose proof (fif_ok_closed_fresh D0 w0 fdm l vs k0 Hok Hlen Hk0) as Hnb.
        iMod (own_update with "Hpool") as "Hpool";
          [apply (fif_pool_update _ w (FDIn true i γo)) |].
        iModIntro.
        iDestruct "HK" as "[HK _]".
        iApply ("HK" $! (Z.of_nat k0) with "[%] [%] [-] []"); [lia | exact Hnb | | iExact "Hfiles"].
        iIntros (d) "%Hfr". apply dev_fresh_p_iff in Hfr as [HD Hfr].
        assert (Hvd : vs !! d = None).
        { apply not_elem_of_dom. pose proof Hok as (_ & _ & H3 & _). intros Hd.
          destruct (H3 d Hd) as [(fd' & Hfd') | HD']; [exact (Hfr fd' Hfd') | done]. }
        assert (Hdn : d ∉ dom vs) by (by apply not_elem_of_dom).
        iEval (rewrite (fif_pool_own_take _ _ d Hdn) fif_tok_halves) in "Hpool".
        iDestruct "Hpool" as "(Hpool & Htk1 & Htk2)".
        iSplitR "Htk2 Hu".
        * iExists (<[k0 := FdOpen true false (FdInode i γo OffHeld)]> l),
            (<[d := FDIn true i γo]> vs), (fun _ => FDIn true i γo).
          iFrame "Hk Hstd Hcwd Hd He".
          iSplit.
          { iPureIntro. apply fif_ok_open_std; [exact Hok | exact Hlen | exact Hk0 | exact Hfr | exact HD]. }
          iSplitL "Hpool"; [by rewrite dom_insert_L |].
          iSplitL "Htoks Htk1".
          { rewrite big_sepM_insert; [| exact Hvd]. iFrame "Htk1 Htoks". }
          rewrite big_sepM_insert; [| exact Hnb]. iSplitR.
          { rewrite /fif_hdl lookup_insert. done. }
          iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
          rewrite lookup_insert_ne; [iExact "Hx" |]. intros ->. exact (Hfr fd' Hfd').
        * iExists true, i, γo, p. iFrame "Htk2 Hu". iPureIntro.
          split; [exact Hrd | by exists content].
      + (* a fresh tail handle *)
        iDestruct (ualloc_hi γfd l fd _ Elc with "Hal") as "(%Hhi & Hstd & Hh)".
        iDestruct (fif_fresh_fd fdm l vs fd with "Hhs Hh") as "(%Hnb & Hhs & Hh)";
          [exact Hok | lia |].
        iMod (own_update with "Hpool") as "Hpool";
          [apply (fif_pool_update _ w (FDIn false i γo)) |].
        iModIntro.
        iDestruct "HK" as "[HK _]".
        iApply ("HK" $! (Z.of_nat fd) with "[%] [%] [-] []"); [lia | exact Hnb | | iExact "Hfiles"].
        iIntros (d) "%Hfr". apply dev_fresh_p_iff in Hfr as [HD Hfr].
        assert (Hvd : vs !! d = None).
        { apply not_elem_of_dom. pose proof Hok as (_ & _ & H3 & _). intros Hd.
          destruct (H3 d Hd) as [(fd' & Hfd') | HD']; [exact (Hfr fd' Hfd') | done]. }
        assert (Hdn : d ∉ dom vs) by (by apply not_elem_of_dom).
        iEval (rewrite (fif_pool_own_take _ _ d Hdn) fif_tok_halves) in "Hpool".
        iDestruct "Hpool" as "(Hpool & Htk1 & Htk2)".
        iSplitR "Htk2 Hu".
        * iExists l, (<[d := FDIn false i γo]> vs), (fun _ => FDIn false i γo).
          iFrame "Hk Hstd Hcwd Hd He".
          iSplit.
          { iPureIntro. apply fif_ok_open; [exact Hok | exact (conj Hhi Hfdlt) | exact Hnb | exact Hfr | exact HD]. }
          iSplitL "Hpool"; [by rewrite dom_insert_L |].
          iSplitL "Htoks Htk1".
          { rewrite big_sepM_insert; [| exact Hvd]. iFrame "Htk1 Htoks". }
          rewrite big_sepM_insert; [| exact Hnb]. iSplitL "Hh".
          { rewrite /fif_hdl lookup_insert Nat2Z.id. iExact "Hh". }
          iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
          rewrite lookup_insert_ne; [iExact "Hx" |]. intros ->. exact (Hfr fd' Hfd').
        * iExists false, i, γo, p. iFrame "Htk2 Hu". iPureIntro.
          split; [exact Hrd | by exists content].
    - (* -1 *)
      iIntros "Hstd Hcwd Hd1 Hd2". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-] []"); [| iExact "Hfiles"].
      iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs [Hd1 Hd2] He Hk").
      iApply ("Hjoin" with "Hd1 Hd2").
    - (* the taint *)
      iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ [_ HK]]".
      iDestruct (fif_ans_ok with "Hof") as %Hans.
      iApply ("HK" with "[%]"); [exact Hans |].
      iApply (fif_open_taint l ret fdm vs Hlen Hok with "Htn He Hof Hhs").
  Qed.

  (* [ei_open_absent] for `f`, at any mode that does not create (the
     truncate's permit at an absent `f` is the dead walk's cursor, paid
     out of the taint: [UkFileDev.file_open_absent], lane TRUNC-PERMIT) *)
  Lemma fif_open_absent_nt (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    path ∈ paths -> ~ mode_create m -> files path = None ->
    fif_fds fdm -∗ fif_filesr files paths -∗
    ((fif_fds fdm -∗ fif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ fif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path m K.
  Proof using Heq Hso.
    intros Hp Hcm Hf. iIntros "Hfds #Hfiles HK".
    iAssert (⌜(forall p, p ∈ paths -> p = fname_f /\ fif_wr D0 w0 = false)
              /\ files fname_f = snd <$> sf⌝)%I
      as %[Hpaths Hfs].
    { iDestruct "Hfiles" as "[%A %B]". by iPureIntro. }
    pose proof (Hpaths path Hp) as [-> Hrd].
    rewrite Hf in Hfs. pose proof (dst_none_of_snd sf (eq_sym Hfs)) as Hs.
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hd & #He) Hk]".
    iDestruct "He" as "#(Hbr & Hrb & Hpay & Hinv & Hm)".
    iAssert fif_env with "[]" as "#He"; [by iFrame "Hbr Hrb Hpay Hinv Hm" |].
    iDestruct (UserFd.ustd_len with "Hstd") as %Hlen.
    iAssert (fdq r qf None) with "[Hd]" as "Hd". { rewrite -Hs. iEval (rewrite (fif_dq_rd Hrd)) in "Hd". iExact "Hd". }
    iApply (file_open_absent c r Heq N P Hso l FsImg.ROOTINO qf m K eq_refl
              (fif_om_create m Hcm) with "Hinv Hstd Hcwd Hd").
    iSplit.
    - iIntros "Hstd Hcwd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-] []"); [| iExact "Hfiles"].
      iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs [Hd] He Hk").
      rewrite (fif_dq_rd Hrd) Hs. iExact "Hd".
    - iIntros (ret) "#Htn Hof Hcwd". iDestruct "HK" as "[_ HK]".
      iDestruct (fif_ans_ok with "Hof") as %Hans.
      iApply ("HK" with "[%]"); [exact Hans |].
      iApply (fif_open_taint l ret fdm vs Hlen Hok with "Htn He Hof Hhs").
  Qed.

  (* the ledger after a close of an unprotected device's last descriptor,
     rebuilt: the device's token home to the pool, the descriptor's handle
     (if a tail one) gone with it, the ledger [l'] agreeing with [l] at
     every other descriptor's slot *)
  Lemma fif_fds_close (fdm : fdmap) (fd : Z) (d : nat) (v : fdev) (l l' : list fdstate)
      (vs : gmap nat fdev) (w : nat -> fdev) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> d ∉ D0 ->
    fif_ok D0 w0 fdm l vs -> vs !! d = Some v ->
    (forall fd' d', fd' <> fd -> fdm !! fd' = Some d' ->
       l' !! Z.to_nat fd' = l !! Z.to_nat fd') ->
    UserFd.ustd γfd l' -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
    own γreg (fif_pool (dom vs) w) -∗
    ([∗ map] d ↦ v ∈ delete d vs, fif_tok d (1/2) v) -∗ fif_tok d 1 v -∗
    ([∗ map] fd ↦ d ∈ delete fd fdm, fif_hdl fd (vs !! d)) -∗ fif_dq -∗ fif_env -∗
    fif_exit_k -∗ fif_fds (delete fd fdm).
  Proof using .
    intros Hfd Hns HD Hok Hv Hl. iIntros "Hstd Hcwd Hpool Htoks Htk Hhs Hdq #He Hk".
    pose proof (fif_ok_close D0 w0 fdm l vs fd d Hok Hfd Hns HD) as Hok'.
    pose proof (fif_not_shared fdm fd d Hns) as Hn.
    assert (Hdd : d ∈ dom vs) by (apply elem_of_dom; by eexists).
    iDestruct (fif_pool_give vs w d v Hdd with "Hpool Htk") as "Hpool".
    assert (Hok'' : fif_ok D0 w0 (delete fd fdm) l' (delete d vs)).
    { apply (fif_ok_ledger D0 w0 (delete fd fdm) l l' (delete d vs) Hok').
      intros fd' d' Hfd'. apply lookup_delete_Some in Hfd' as [Hne Hfd'].
      exact (Hl fd' d' (not_eq_sym Hne) Hfd'). }
    iApply (fif_fds_of (delete fd fdm) l' (delete d vs) _ Hok'' with "Hstd Hcwd Hpool Htoks [Hhs] Hdq He Hk").
    iApply (big_sepM_impl with "Hhs"). iIntros "!>" (fd' d' Hfd') "Hx".
    rewrite lookup_delete_ne; [iExact "Hx" |].
    intros ->. apply lookup_delete_Some in Hfd' as [Hne Hfd'].
    exact (Hn fd' (not_eq_sym Hne) Hfd').
  Qed.

  (* [ei_close] of an input's descriptor: the handle (or the ledger's
     slot), the deed straight back to the core, the token home to the
     pool *)
  Lemma fif_close_in (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8))
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> d ∉ D0 ->
    fif_fds fdm -∗ fif_filesr files paths -∗ fif_in d Sin -∗
    ((fif_fds (delete fd fdm) -∗ fif_filesr files paths -∗ K 0)
     ∧ (∀ y, fif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns HD. iIntros "Hfds #Hfiles Hin HK".
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
    iDestruct (fif_in_file_in d Sin with "Hin Hdq") as (s i γo content) "(%Hrd & %Hsf & Htk & Hin)".
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hs. rewrite Hv in Hs. simpl in Hs.
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[Hh Hhs]".
    iEval (rewrite /fif_hdl Hv) in "Hh".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (fif_tok d 1 (FDIn s i γo)) with "[Htk Htk']" as "Htk".
    { rewrite fif_tok_halves. iFrame "Htk Htk'". }
    destruct (Z_of_nat_complete fd H0) as [k ->].
    iDestruct "HK" as "[HK _]".
    destruct s.
    - (* a standard slot: the ledger's row goes to [FdClosed] *)
      destruct Hs as (Hsk & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_in_std r N P Hsc k l false i γo qf content Sin K
                ltac:(unfold NSTD in *; lia) Hrow with "Hstd Hin").
      iIntros "Hstd Hd". iAssert fif_dq with "[Hd]" as "Hd".
      { rewrite (fif_dq_rd Hrd) Hsf. iExact "Hd". }
      iApply ("HK" with "[-] []"); [| iExact "Hfiles"].
      iApply (fif_fds_close fdm (Z.of_nat k) d (FDIn true i γo) l (<[k := FdClosed]> l) vs w
                Hfd Hns HD Hok Hv with "Hstd Hcwd Hpool Htoks Htk Hhs Hd He Hk").
      intros fd' d' Hne Hfd'. destruct (H1 fd' d' Hfd') as [H0' _].
      apply list_lookup_insert_ne. exact (fif_slot_ne k fd' H0' Hne).
    - (* a tail handle *)
      iEval (rewrite Nat2Z.id) in "Hh".
      iApply (file_close_in r N P Hsc k false i γo qf content Sin K with "Hh Hin").
      iIntros "Hd". iAssert fif_dq with "[Hd]" as "Hd".
      { rewrite (fif_dq_rd Hrd) Hsf. iExact "Hd". }
      iApply ("HK" with "[-] []"); [| iExact "Hfiles"].
      iApply (fif_fds_close fdm (Z.of_nat k) d (FDIn false i γo) l l vs w
                Hfd Hns HD Hok Hv with "Hstd Hcwd Hpool Htoks Htk Hhs Hd He Hk").
      intros; reflexivity.
  Qed.

  (* ...of a STANDARD stream of any other kind (the console, the file a
     redirect holds), unprotected: the ledger's slot to [FdClosed], the
     device dropped, the token home *)
  Lemma fif_close_std_dev (fdm : fdmap) (fd : Z) (d : nat) (v : fdev) (l : list fdstate)
      (vs : gmap nat fdev) (w : nat -> fdev) (st : fdstate) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared fdm fd d -> d ∉ D0 ->
    fif_ok D0 w0 fdm l vs -> vs !! d = Some v ->
    0 <= fd -> fd < Z.of_nat NSTD -> l !! Z.to_nat fd = Some st -> st <> FdClosed ->
    fdst_nopipe st ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
    own γreg (fif_pool (dom vs) w) -∗
    ([∗ map] d ↦ v ∈ vs, fif_tok d (1/2) v) -∗ fif_tok d (1/2) v -∗
    ([∗ map] fd ↦ d ∈ fdm, fif_hdl fd (vs !! d)) -∗ fif_dq -∗ fif_env -∗ fif_exit_k -∗
    (fif_fds (delete fd fdm) -∗ K 0) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns HD Hok Hv H0 Hs Hl Hne Hnp.
    iIntros "Hstd Hcwd Hpool Htoks Htk Hhs Hdq #He Hk HK".
    pose proof Hok as (H1 & _).
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[_ Hhs]".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (fif_tok d 1 v) with "[Htk Htk']" as "Htk".
    { rewrite fif_tok_halves. iFrame "Htk Htk'". }
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hl.
    iApply (file_close_std N P Hsc k l st K ltac:(unfold NSTD in *; lia) Hl Hne Hnp
              with "Hstd").
    iIntros "Hstd". iApply "HK".
    iApply (fif_fds_close fdm (Z.of_nat k) d v l (<[k := FdClosed]> l) vs w Hfd Hns HD Hok Hv
              with "Hstd Hcwd Hpool Htoks Htk Hhs Hdq He Hk").
    intros fd' d' Hne' Hfd'. destruct (H1 fd' d' Hfd') as [H0' _].
    apply list_lookup_insert_ne. exact (fif_slot_ne k fd' H0' Hne').
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE FIELDS THE KERNEL REFUSES (the header's list)                   *)
  (* ------------------------------------------------------------------- *)

  (* the gap is a NAMED proposition, so that an instance section (SS5,
     echo's) can assume it at its own program by name *)
  Definition fif_nil_in_law : Prop :=
    forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (K : Z -> iProp Σ),
    fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_in d Sin -∗
    ((fif_fds fdm -∗ fif_in d Sin -∗ K 0) ∧ (fif_fds fdm -∗ fif_in d Sin -∗ K (-1))
     ∧ (∀ y, fif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.

  (* THE INPUT'S ZERO-LENGTH WRITE IS PROVED (lane NIL-RET): row 16
     carries [SpecFilewrite.filewrite_ret], so at a read-only row -- where
     [filewrite_extra] is [emp] -- the U tier still learns the answer is 0
     or -1, and nothing moves.  [UkFileDev.file_write_nil_std_ro] at the
     standard slot [FDIn true] pins in the ledger,
     [UkFileDev.file_write_nil_hdl_ro] at the tail handle [FDIn false]
     holds; the taint arm is never taken. *)
  Lemma fif_nil_in : fif_nil_in_law.
  Proof using Hsw.
    intros fdm fd d Sin K Hfd. iIntros "Hfds Hin HK".
    iDestruct "Hin" as (s i γo p) "(Htk & %Hsin & Hoff)".
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v Hv].
    iDestruct (fif_toks_agree vs d v with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst v.
    pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
    pose proof (H2 fd d Hfd) as Hs. rewrite Hv in Hs. simpl in Hs.
    destruct (Z_of_nat_complete fd H0) as [k ->].
    destruct s.
    - (* a standard slot: the ledger is the handle *)
      destruct Hs as (Hsk & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_write_nil_std_ro N P Hsw k l true (FdInode i γo OffHeld) K
                ltac:(unfold NSTD in *; lia) Hrow with "Hstd").
      iSplit; iIntros "Hstd".
      + iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hoff Htk] [Htk Hoff]").
        * iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
        * iExists true, i, γo, p. iFrame "Htk Hoff". by iPureIntro.
      + iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hoff Htk] [Htk Hoff]").
        * iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
        * iExists true, i, γo, p. iFrame "Htk Hoff". by iPureIntro.
    - (* a tail handle *)
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hfd with "Hhs") as "[Hh Hcl]".
      iEval (rewrite /fif_hdl Hv) in "Hh". iEval (rewrite Nat2Z.id) in "Hh".
      iApply (file_write_nil_hdl_ro N P Hsw k true (FdInode i γo OffHeld) K
                ltac:(lia) with "Hh").
      iSplit; iIntros "Hh".
      + iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hoff Htk] [Htk Hoff]").
        * iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks [Hh Hcl] Hdq He Hk").
          iApply "Hcl". rewrite /fif_hdl Hv Nat2Z.id. iExact "Hh".
        * iExists false, i, γo, p. iFrame "Htk Hoff". by iPureIntro.
      + iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hoff Htk] [Htk Hoff]").
        * iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks [Hh Hcl] Hdq He Hk").
          iApply "Hcl". rewrite /fif_hdl Hv Nat2Z.id. iExact "Hh".
        * iExists false, i, γo, p. iFrame "Htk Hoff". by iPureIntro.
  Qed.

  (* the laws assembled from their cases *)
  Lemma fif_write_nil (fdm : fdmap) (fd : Z) (d : nat) (x : dspec) (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    fif_fds fdm -∗ fif_dev d x -∗
    ((fif_fds fdm -∗ fif_dev d x -∗ K 0) ∧ (fif_fds fdm -∗ fif_dev d x -∗ K (-1))
     ∧ (∀ y, fif_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.
  Proof using Hsw HPc.
    intros Hfd. iIntros "Hfds Hd HK".
    destruct x as [alts | | cs | | Sin | | | | | | |]; simpl; try (iDestruct "Hd" as "[]").
    - (* the console *)
      iDestruct "Hd" as (v I C) "[Htk Hd]".
      iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
      destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v' Hv].
      iDestruct (fif_toks_agree vs d v' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst v'.
      pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 Hlt].
      pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
      destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hrow.
      iApply (fif_cons_nil l k rb (fcons_atc C v I alts) K ltac:(unfold NSTD in *; lia) Hrow
                with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]").
      + iApply (fif_fds_of fdm l vs w Hok with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
      + iExists v, I, C. iFrame "Htk Hd".
    - (* the file held for writing *)
      iApply (fif_file_nil fdm fd d cs K Hfd with "Hfds Hd").
      iSplit; [iDestruct "HK" as "[HK _]" | iDestruct "HK" as "[_ [HK _]]"]; iExact "HK".
    - (* an input: the header's list *)
      iApply (fif_nil_in fdm fd d Sin K Hfd with "Hfds Hd HK").
  Qed.

  Lemma fif_open_absent (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    path ∈ paths -> ~ mode_create m -> files path = None ->
    fif_fds fdm -∗ fif_filesr files paths -∗
    ((fif_fds fdm -∗ fif_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ fif_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path m K.
  Proof using Heq Hso.
    exact (fif_open_absent_nt fdm files paths path m K).
  Qed.

  (* [ei_close]: the last descriptor of an UNPROTECTED device (the file
     application has no copy device and no haltable output, so the close's
     [drained_at_close] fact is not needed) *)
  Lemma fif_close (fdm : fdmap) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared_p D0 fdm fd d -> drained_at_close x ->
    fif_fds fdm -∗ fif_filesr files paths -∗ fif_dev d x -∗
    ((fif_fds (delete fd fdm) -∗ fif_filesr files paths -∗ K 0)
     ∧ (∀ y, fif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hnsp _.
    assert (HD : d ∉ D0) by (intros H; apply Hnsp; apply fd_shared_p_iff; by left).
    assert (Hns : ~ fd_shared fdm fd d) by (intros H; apply Hnsp; apply fd_shared_p_iff; by right).
    iIntros "Hfds #Hfiles Hdev HK".
    destruct x as [alts | alts | cs | | Sin | Sin | | | | | |]; simpl;
      try (iDestruct "Hdev" as "[]").
    - (* the console: a standard slot, its row a console row *)
      iDestruct "Hdev" as (v Ic C) "[Htk _]".
      iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
      destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v' Hv].
      iDestruct (fif_toks_agree vs d v' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst v'. pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 _].
      pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
      iApply (fif_close_std_dev fdm fd d (FDCons v Ic C) l vs w _ K Hfd Hns HD Hok Hv H0 Hs Hrow
                ltac:(discriminate) I with "Hstd Hcwd Hpool Htoks Htk Hhs Hdq He Hk").
      iIntros "Hfds". iDestruct "HK" as "[HK _]". iApply ("HK" with "Hfds Hfiles").
    - (* the file a redirect holds: a standard slot, its row the held one *)
      iDestruct "Hdev" as (i γo ws) "[Htk _]".
      iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
      destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v' Hv].
      iDestruct (fif_toks_agree vs d v' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst v'. pose proof Hok as (H1 & H2 & _). destruct (H1 fd d Hfd) as [H0 _].
      pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow. destruct Hrow as (Hs & rb & Hrow).
      iApply (fif_close_std_dev fdm fd d (FDFile i γo ws) l vs w _ K Hfd Hns HD Hok Hv H0 Hs Hrow
                ltac:(discriminate) I with "Hstd Hcwd Hpool Htoks Htk Hhs Hdq He Hk").
      iIntros "Hfds". iDestruct "HK" as "[HK _]". iApply ("HK" with "Hfds Hfiles").
    - iApply (fif_close_in fdm fd d Sin files paths K Hfd Hns HD with "Hfds Hfiles Hdev HK").
  Qed.

  (* [ei_close_shared]: a dup, or a PROTECTED device's descriptor -- the
     device stays registered and with the handler, only the ledger's slot
     closes *)
  Lemma fif_close_shared (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> fd_shared_p D0 fdm fd d ->
    fif_fds fdm -∗
    ((fif_fds (delete fd fdm) -∗ K 0) ∧ (∀ y, fif_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc Hw0.
    intros Hfd Hsh. iIntros "Hfds HK".
    iDestruct "Hfds" as (l vs w) "[(Hstd & Hcwd & %Hok & Hpool & Htoks & Hhs & Hdq & #He) Hk]".
    destruct (fif_ok_lookup D0 w0 _ _ _ _ _ Hok Hfd) as [v Hv].
    pose proof Hok as (H1 & H2 & _ & _ & H5 & H6). destruct (H1 fd d Hfd) as [H0 _].
    pose proof (H2 fd d Hfd) as Hr. rewrite Hv in Hr.
    pose proof (fif_ok_close_shared D0 w0 fdm l vs fd d Hok Hfd Hsh) as Hok'.
    apply fd_shared_p_iff in Hsh.
    iDestruct (big_sepM_delete _ _ _ _ Hfd with "Hhs") as "[_ Hhs]".
    (* a shared or protected descriptor is a standard stream of any kind
       but a tail input, which has one descriptor and is never protected *)
    assert (Hrow : exists st, fd < Z.of_nat NSTD /\ l !! Z.to_nat fd = Some st
                              /\ st <> FdClosed /\ fdst_nopipe st).
    { destruct v as [vc Ic Cc | i γo ws | [|] i γo].
      - destruct Hr as (Hs & rb & Hl). exists (FdOpen rb true (FdDevice CONSOLE)).
        split_and!; [exact Hs | exact Hl | discriminate | exact Logic.I].
      - destruct Hr as (Hs & rb & Hl). exists (FdOpen rb true (FdInode i γo OffHeld)).
        split_and!; [exact Hs | exact Hl | discriminate | exact Logic.I].
      - destruct Hr as (Hs & Hl). exists (FdOpen true false (FdInode i γo OffHeld)).
        split_and!; [exact Hs | exact Hl | discriminate | exact Logic.I].
      - exfalso. destruct Hsh as [HD | (fd' & Hin' & Hfd')].
        + pose proof (H6 d HD) as Hw. rewrite Hv in Hw. injection Hw as Hw.
          exact (Hw0 d HD i γo (eq_sym Hw)).
        + apply elem_of_dom in Hin' as [d'' Hd'']. apply lookup_delete_Some in Hd'' as [Hne _].
          exact (Hne (H5 fd fd' d false i γo Hfd Hfd' Hv)). }
    destruct Hrow as (st & Hs & Hl & Hne & Hnp).
    destruct (Z_of_nat_complete fd H0) as [k ->]. rewrite Nat2Z.id in Hl.
    iApply (file_close_std N P Hsc k l st K ltac:(unfold NSTD in *; lia) Hl Hne Hnp
              with "Hstd").
    iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
    assert (Hok'' : fif_ok D0 w0 (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) vs).
    { apply (fif_ok_ledger D0 w0 (delete (Z.of_nat k) fdm) l _ vs Hok').
      intros fd' d' Hfd'. apply lookup_delete_Some in Hfd' as [Hne' Hfd'].
      destruct (H1 fd' d' Hfd') as [H0' _].
      apply list_lookup_insert_ne. exact (fif_slot_ne k fd' H0' (not_eq_sym Hne')). }
    iApply (fif_fds_of (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) vs w Hok''
              with "Hstd Hcwd Hpool Htoks Hhs Hdq He Hk").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE RECORD, at the protected devices [D0]                           *)
  (* ------------------------------------------------------------------- *)

  Definition file_iface : ep_ifaceP (Dp := D0) N P.
  Proof using LINKS_blk LINKS_pers LINKS_taint LINKS_w Heq HPc HNc Hsr Hsw Hso Hsc Hse D0 w0 Hw0
              qf sf γreg fifRegG0.
    refine (MkEIP (Dp := D0) N P fif_fds fif_out (fun _ _ => False%I) (fun _ => False%I) fif_outm
              fif_in (fun _ _ => False%I) (fun _ => False%I)
              (fun _ _ _ _ => False%I) (fun _ _ _ => False%I) (fun _ => False%I)
              (fun _ _ _ _ => False%I) (fun _ _ => False%I)
              fif_filesr fif_taint fif_taint_pays
              fif_write _ fif_write_m _ fif_write_nil fif_read _ _ _ _ _ _ _ _ _ fif_open fif_open_absent
              fif_close fif_close_shared fif_exit _ _ _ _ _).
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    (* the copy device (design SS3.4f): no copy device in the file application *)
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    (* the producer device (union.md C9d'): not the file application's *)
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
  Defined.

  Lemma fif_ei_fds : ei_fds N P file_iface = fif_fds.
  Proof. reflexivity. Qed.
  Lemma fif_ei_files : ei_files N P file_iface = fif_filesr.
  Proof. reflexivity. Qed.
  Lemma fif_dev_of (d : nat) (x : dspec) : dev_of N P file_iface d x = fif_dev d x.
  Proof. by destruct x. Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE GLUE AT ANY LINK PARAMETERS (cut C9f1, design union.md S5): the *)
  (*  file application's glue of section 2 and 3 below, stated over the  *)
  (*  abstract console so that the union's entries ([UkUnionEntries])     *)
  (*  spend it at their own record.  The file application keeps its own  *)
  (*  statements; these are their parameter-generic twins.               *)
  (* ------------------------------------------------------------------- *)

  (* entry device 0 is among the drained devices, at its pinned value *)
  Lemma fif_exit_dev0_g (fdm : fdmap) (l : list fdstate) (vs : gmap nat fdev)
      (dv : nat -> dspec) (ds : gset nat) :
    D0 = [0%nat] ->
    (forall d, d ∈ ds -> drained (dv d)) -> dom_ok_p D0 fdm ds -> fif_ok D0 w0 fdm l vs ->
    ([∗ set] d ∈ ds, fif_dev d (dv d)) -∗
    ⌜drained (dv 0%nat)⌝ ∗ ⌜vs !! 0%nat = Some (w0 0%nat)⌝ ∗ fif_dev 0%nat (dv 0%nat).
  Proof using .
    intros HD0 Hdr Hdom Hok. iIntros "Hdev".
    rewrite HD0 in Hdom, Hok. apply dom_ok_p_iff in Hdom as [Hdp _].
    assert (H0 : 0%nat ∈ ds) by (apply Hdp; constructor).
    iDestruct (big_sepS_delete _ _ 0%nat H0 with "Hdev") as "[Hd0 _]".
    iFrame "Hd0". iPureIntro. split; [exact (Hdr _ H0) |].
    apply (fif_ok_D0 [0%nat] w0 fdm l vs 0%nat Hok). constructor.
  Qed.

  (* THE CONSOLE GLUE: the drained console at one of the codes [C] it was
     lent is the round's post at that code, and the core's deed comes
     back beside it *)
  Lemma fif_exit_k_cons_g (C : list nat) (v : era_pins) (I0 : list (bv 8))
      (F : iProp Σ) :
    gT Pm = file_taint c ->
    D0 = [0%nat] -> w0 0%nat = FDCons v I0 C ->
    □ (∀ a : nat, ⌜a ∈ C⌝ -∗ gwc_post M Pm (S gen_id) v I0 a -∗
         fdq r qf sf -∗ F -∗ ukn_pay N (-1)) -∗
    F -∗ fif_exit_k.
  Proof using .
    intros HPT HD0 Hw. iIntros "#HQ HF".
    iIntros (fdm l vs w files paths dv ds) "%Hdr %Hdom Hcore _ Hdev".
    iDestruct "Hcore" as "(_ & _ & %Hok & _ & Htoks & _ & Hdq & #(_ & _ & Hpay & _))".
    iEval (rewrite (fif_dq_rd ltac:(by rewrite (fif_wr_0 D0 w0 HD0) Hw))) in "Hdq".
    iDestruct (fif_exit_dev0_g fdm l vs dv ds HD0 Hdr Hdom Hok with "Hdev")
      as "(%Hd0 & %Hv0 & Hd0)".
    rewrite Hw in Hv0.
    destruct (dv 0%nat) as [alts | | cs' | | S' | | | | | | |]; simpl in Hd0; simpl;
      try (iDestruct "Hd0" as "[]").
    - iDestruct "Hd0" as (v' I' C') "[Htk Hd]".
      iDestruct (fif_toks_agree vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      injection Heqv as <- <- <-.
      iDestruct (cons_dev_atc_sub M Pm LINKS C v I0 alts [] Hd0 with "Hd") as "Hd".
      iDestruct (cons_dev_atc_drained M Pm LINKS C v I0 with "Hd") as "[_ [HT | Hd]]".
      { iEval (rewrite HPT) in "HT". iApply ("Hpay" with "HT"). }
      iDestruct "Hd" as (ps cs s1 pos a) "(%Hw' & %HaC & %Hadm & _ & Hc)".
      iApply ("HQ" $! a with "[%] [Hc] Hdq HF"); [exact HaC |].
      iApply (cons_cur_gwc_post M Pm v ps cs s1 I0 pos a Hw' with "Hc").
    - iDestruct "Hd0" as (i γo ws) "[Htk _]".
      iDestruct (fif_toks_agree vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      discriminate Heqv.
    - iDestruct "Hd0" as (s i γo p) "(Htk & _)".
      iDestruct (fif_toks_agree vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      discriminate Heqv.
  Qed.

  (* THE REDIRECT GLUE: [UEchoFile.ef_exit]'s payload, the era's credential
     as lent framed and the deed's cursor at whatever landed *)
  Lemma fif_exit_k_redir_g (i : Z) (γo : gname) (ws : wordline) (Wq : iProp Σ) :
    D0 = [0%nat] -> w0 0%nat = FDFile i γo ws ->
    □ (UEchoFile.ef_exit c r Wq i γo ws -∗ ukn_pay N (-1)) -∗ Wq
    -∗ fif_exit_k.
  Proof using .
    intros HD0 Hw. iIntros "#HQ HWq".
    iIntros (fdm l vs w files paths dv ds) "%Hdr %Hdom Hcore _ Hdev".
    iDestruct "Hcore" as "(_ & _ & %Hok & _ & Htoks & _ & _ & _)".
    iDestruct (fif_exit_dev0_g fdm l vs dv ds HD0 Hdr Hdom Hok with "Hdev")
      as "(%Hd0 & %Hv0 & Hd0)".
    rewrite Hw in Hv0.
    destruct (dv 0%nat) as [alts | | cs' | | S' | | | | | | |]; simpl in Hd0; simpl;
      try (iDestruct "Hd0" as "[]").
    - iDestruct "Hd0" as (v' I' C') "[Htk _]".
      iDestruct (fif_toks_agree vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      discriminate Heqv.
    - iDestruct "Hd0" as (i' γo' ws') "[Htk Hd]".
      iDestruct (fif_toks_agree vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      injection Heqv as <- <- <-.
      iDestruct "Hd" as (b) "(_ & _ & Hq)". rewrite /file_out /UEchoFile.efany.
      iDestruct "Hq" as (sel) "[_ Hq]".
      iApply "HQ". rewrite /UEchoFile.ef_exit. iFrame "HWq". iExists sel. iExact "Hq".
    - iDestruct "Hd0" as (s i' γo' p) "(Htk & _)".
      iDestruct (fif_toks_agree vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      discriminate Heqv.
  Qed.

  (* WHAT THE ROUND LENDS, as [env_res], at any link parameters *)
  Lemma fif_env_res_g (E : penv) (l : list fdstate) :
    D0 = [0%nat] ->
    (forall fd d, pe_fd E !! fd = Some d -> d = 0%nat) ->
    (forall fd d, pe_fd E !! fd = Some d -> fif_row (Some (w0 0%nat)) fd l) ->
    (forall fd d, pe_fd E !! fd = Some d -> 0 <= fd < Z.of_nat NOFILE) ->
    (forall s i γo, w0 0%nat <> FDIn s i γo) ->
    (forall fd d, pe_fd E !! fd = Some d -> fif_hdl fd (Some (w0 0%nat)) = emp%I) ->
    (forall p, p ∈ pe_paths E -> p = fname_f /\ fif_wr D0 w0 = false) ->
    pe_files E fname_f = snd <$> sf ->
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO
    -∗ fif_exit_k -∗
    fif_env -∗ fif_dq -∗ own γreg (fif_pool ∅ w0) -∗
    (fif_tok 0%nat (1/2) (w0 0%nat) -∗ fif_dev 0%nat (pe_dev E 0%nat)) -∗
    env_res N P file_iface E {[0%nat]}.
  Proof using .
    intros HD0 Hd0 Hrow Hbnd Hnin Hhdl Hpaths Hfiles.
    iIntros "Hstd Hcwd Hk #He Hd Hpool Hdev". rewrite /env_res.
    iDestruct (fif_pool_own_take ∅ w0 0%nat with "Hpool") as "[Hpool Htk]"; [set_solver |].
    iDestruct (fif_tok_halves with "Htk") as "[Htk1 Htk2]".
    iSplit.
    { iPureIntro. intros fd d Hfd. rewrite (Hd0 fd d Hfd). set_solver. }
    iSplitL "Hstd Hcwd Hk Hd Hpool Htk1".
    { rewrite fif_ei_fds. iExists l, {[0%nat := w0 0%nat]}, w0.
      iFrame "Hk Hstd Hcwd Hd He".
      iSplit; [iPureIntro; exact (fif_ok_entry (pe_fd E) l HD0 Hd0 Hrow Hbnd Hnin) |].
      iSplitL "Hpool"; [by rewrite dom_singleton_L right_id_L |].
      iSplitL "Htk1"; [by rewrite big_sepM_singleton |].
      iApply big_sepM_intro. iIntros "!>" (fd d) "%Hfd".
      rewrite (Hd0 fd d Hfd) lookup_singleton (Hhdl fd d Hfd). done. }
    iSplitR.
    { rewrite fif_ei_files. iPureIntro. split; [exact Hpaths | exact Hfiles]. }
    rewrite /dev_res big_sepS_singleton fif_dev_of. iApply ("Hdev" with "Htk2").
  Qed.
  End UkFileIfaceGen.

  (* THE FILE APPLICATION'S INSTANCE: the console at [file_links] *)
  Local Notation fcons_atc := (cons_dev_atc file_lm (file_params g) (file_links g)).

  Lemma fif_cat_dg_open : cat_dg_open fname_f = dg_catopen.
  Proof using . apply (bool_decide_unpack _). vm_compute. exact Logic.I. Qed.

  Lemma fif_fname_img : fname_f = FsImgCheck.fname_f.
  Proof using . apply (bool_decide_unpack _). vm_compute. exact Logic.I. Qed.


  Lemma fif_files_some (i : Z) (content : list (bv 8)) :
    sf = Some (i, content) -> fif_files (snd <$> sf) fname_f = Some content.
  Proof using . intros Hsf. rewrite fif_files_f Hsf. reflexivity. Qed.

  Lemma fif_files_none : sf = None -> fif_files (snd <$> sf) fname_f = None.
  Proof using . intros Hsf. rewrite fif_files_f Hsf. reflexivity. Qed.

  Lemma fif_dp0 : D0 = [0%nat] -> dp_in D0 {[0%nat]}.
  Proof using .
    intros HD0 d Hd. rewrite HD0 in Hd. apply elem_of_list_singleton in Hd as ->. set_solver.
  Qed.

  (* the two-descriptor console environment's pure side, once *)
  Lemma fif_cat_env_pure (l : list fdstate) (rb1 rb2 : bool) (v : era_pins) (I0 : list (bv 8))
      (C : list nat) (alts : list (list (bv 8))) files :
    w0 0%nat = FDCons v I0 C ->
    l !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    (forall fd d, pe_fd (cat_env0 alts files [fname_f]) !! fd = Some d -> d = 0%nat)
    /\ (forall fd d, pe_fd (cat_env0 alts files [fname_f]) !! fd = Some d ->
          fif_row (Some (w0 0%nat)) fd l)
    /\ (forall fd d, pe_fd (cat_env0 alts files [fname_f]) !! fd = Some d ->
          0 <= fd < Z.of_nat NOFILE).
  Proof using .
    intros Hw Hl1 Hl2. cbn [cat_env0 pe_fd]. split_and!.
    - intros fd d. rewrite lookup_insert_Some lookup_singleton_Some.
      intros [[_ <-] | (_ & _ & <-)]; reflexivity.
    - intros fd d. rewrite lookup_insert_Some lookup_singleton_Some Hw. simpl.
      intros [[<- _] | (_ & <- & _)]; (split; [unfold NSTD; lia |]); [by exists rb1 | by exists rb2].
    - intros fd d. rewrite lookup_insert_Some lookup_singleton_Some. unfold NOFILE.
      intros [[<- _] | (_ & <- & _)]; lia.
  Qed.

End UkFileIface.

(* the registry's birth: the whole pool, at any values *)
Lemma fif_reg_alloc `{!fifRegG Σ} (w : nat -> fdev) : ⊢ |==> ∃ γ, own γ (fif_pool ∅ w).
Proof. iApply own_alloc. apply fif_pool_valid. Qed.

(* ===================================================================== *)
(*  4.  THE VACUITY WITNESSES: every proved law at cat's instance         *)
(* ===================================================================== *)

Section UkFileIfaceCat.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !fifRegG Σ}.
  Context (g : file_gn) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).
  Context (N : uk_names Σ) `{!ukn_const N}.
  Context (γreg : gname).
  Context (D0 : list nat) (w0 : nat -> fdev) (qf : Qp) (sf : dst).

  Local Instance fif_cat_code_persistent : Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.
End UkFileIfaceCat.
