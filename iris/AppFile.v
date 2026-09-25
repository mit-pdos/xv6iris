(* AppFile.v -- THE FILE APPLICATION, THE CLAIM (layer A): what the files
   of the user-file class ([FileDisc.uname], FileName.v's laws) may hold,
   as a resource over the abstract view, with the DEED the shell's process
   chain holds against it -- ONE deed over the map of those files (cut W2
   of claude-notes/design/filenames.md, section 2).

   Design of record: claude-notes/design/app-file.md (section 2 is this
   file; section 3 is the deed's life, which the program lanes prove).

   THE CLAIM.  [file_pred c r av] is the echo application's predicate
   ([AppEcho.echo_pred]: the taint, or the pins beside the console's state)
   with a FOURTH conjunct, [f_state]: every class name in the root
   directory is in the state the deed's map says -- absent, or present
   with exactly these bytes -- and each present file's bytes are a chunk
   subset of an [echo … > N] line at its own name the console has seen (a
   lower bound of the ledger's line list says which lines those are).

   THE DEED is a [ghost_var] over [FileState.fstate] in two halves: the claim
   keeps one, the process chain (sh, its forked child, the exec'd echo or
   cat) the other, beside a TICKET of the same shape.  Agreement makes the
   claim's state KNOWN to the holder -- that is how a write step knows the
   row it appends to is its line's, and how cat knows the bytes it prints
   are the file's.

   A MOVE IS TWO PHASES, exactly the tree layer's ([AppTree] section 7.2 of
   design/user-tree.md), and for the same structural reason: the step a
   fire takes ([AppInv.app_step]) is a wand INTO the claim, so it can park
   the holder's half but cannot hand anything back.  Phase 1
   ([file_step_park], update-free) parks the deed half: the claim's arm
   goes from EXACT (one half, the content at the deed's value) to IN
   FLIGHT (the whole deed at the OLD value, the content at the NEW one).
   Phase 2 ([file_resync], a fancy update at a mask holding [appN], where
   the fire's own phase 2 runs) opens the invariant with the TICKET: the
   in-flight arm is the only one it can meet -- the exact arm is refuted by
   the ticket's agreement against the view's content, the taint arm hands
   the ticket back beside the taint -- and both ghosts move to the new
   value, one half of each returning to the holder.  A READER holding a
   deed half refutes the in-flight arm outright (the whole deed is in it),
   so the deed law reads the exact arm and nothing weakens.

   THE STATE IS THE CONTENT ([FileState.v]'s note): [f_ok av s] determines
   [s] from the view ([f_ok_fcontent]), so the transport allocates the
   copy's fresh ghosts at [fcontent_of av] OUTSIDE the later, exactly as
   [AppEcho.echo_xfer] allocates its flag at [cons_inum av] -- and an
   in-flight original copies to an EXACT copy at the view's content.  The
   pins and the console state ride at the projections, so every console
   lemma of [AppEcho] applies here through [file_pred_cons].

   WHAT IS HERE: the fixed part and the instance names; the line list's
   two shapes; the deed and ticket algebra; [f_ok] and its reading; the
   claim, its timelessness, the deed law; the free step, the two phases,
   the tainted step; the supply off the taint and its converse; the two
   transports (commit and boot); the era-0 claim at the image.  WHAT IS
   NOT HERE (layer B, lane STAGE): the record [app_file], its ledger, tag
   and console interface, which need the stage grown by design section 4. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map invariants.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.         (* [bioslotG] *)
Require Import Xv6G.               (* [xv6G] *)
Require Import FdSlots.            (* [fdslotG] *)
Require Import IrefSlots.          (* [irefslotG] *)
Require Import ProcAvail.          (* [pavG] *)
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsImgDisk.
Require Import FsBootParams.
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsState.
Require Import FsTree.             (* [fname] *)
Require Import FsAbsDefs.
Require Import FsInitPin.
Require Import FsInitPinBoot.
Require Import FsConsPin.
Require Import FsCfgBoot.
Require Import FsDurImg.
Require Import FsBlocks.           (* [fs_names], [fs_top] *)
Require Import FsNode.             (* [fs_node] *)
Require Import FileInvDefs.        (* [fileG] / [file_app]: the era's record *)
Require Import AppCfg.
Require Import AppInv.
Require Import EchoDisc.           (* [line_ok] *)
Require Import EchoOut.
Require Import AppEcho.            (* [echo_taint], [echo_cl], [cons_state],
                                      [echo_boot], [echo_pred]'s pieces *)
Require Export FileState.          (* [fstate], [echo_chunks], [subseq], [sel_ok] *)
Require Import FileFsPure.         (* [file_fs_pure] = echo's pins and cat's *)
Require FileDisc.                  (* the class [FileDisc.uname] *)
Require Import FileName.           (* its laws: [txt_laws], L4 at era 0 *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  NAMES: THE FIXED PART AND THE INSTANCE                             *)
(* ====================================================================== *)

(* a typed line, as the console sees it: the words of one [echo … > N] *)
Definition wordline : Type := list (list (bv 8)).

(* ...AND THE LINE THE LEDGER FILES: the file the line redirects to beside
   its words -- the model's [FileDisc.echof_ws] shape, so the ledger's list
   IS the history's [FileDisc.echof_lines_of] (cut W2 of
   claude-notes/design/filenames.md) *)
Definition fwline : Type := list (bv 8) * wordline.

(* THE FIXED PART: echo's (the taint counter and the era map) beside the
   LINE LIST's name -- a [mono_list] of the [echo … > N] lines the console
   has received, in order, whose authority the ledger keeps and whose
   lower bounds ride the input tag (design section 4). *)
Definition file_fixed : Type := echo_fixed * gname.

(* THE INSTANCE: echo's console pair beside THE DEED's and THE TICKET's
   names *)
Record file_names := MkFileNames {
  fn_cons : echo_names;
  fn_deed : gname;
  fn_tkt  : gname;
  fn_esc  : gname;                     (* THE ESCROW LEDGER (section 2a) *)
}.

(* THE DEED'S STATE: the model's [fstate] with each file's INUM beside its
   bytes (cut W2: a map over the class [FileDisc.uname]).  The inum is
   what lets a holder identify the row its descriptor sits on with its
   file's (lane F-WRITE's finding: at an existential inum the deed says
   what a file holds and never which row is it, and a free step could even
   relocate it); the model reads the contents only ([dst_content]). *)
Definition dst : Type := gmap fname (Z * list (bv 8)).
Definition dst_content (s : dst) : fstate := snd <$> s.

Lemma dst_content_lookup (s : dst) (N : fname) :
  dst_content s !! N = snd <$> s !! N.
Proof using . exact (lookup_fmap _ _ _). Qed.

Lemma dst_content_insert (s : dst) (N : fname) (i : Z) (bs : list (bv 8)) :
  dst_content (<[N := (i, bs)]> s) = <[N := bs]> (dst_content s).
Proof using . exact (fmap_insert _ _ _ _). Qed.

Lemma dst_content_empty : dst_content ∅ = ∅.
Proof using . exact (fmap_empty _). Qed.

(* ONE ESCROW, as the claim's ledger records it: the content the deed was
   parked AT, and the one-shot name whose token the holder keeps.  The
   ledger is a [mono_list] of these, so a reader's witness of an entry is
   PERSISTENT and survives every arm of the syscall's fold -- which is the
   whole reason the escrow can be read by a piece that carries nothing
   linear (section 2a). *)
Definition esc_rec : Type := dst * gname.

Class fileAppG (Σ : gFunctors) := FileAppG {
  fa_deed : ghost_varG Σ dst;
  fa_fl   : inG Σ (mono_listR (leibnizO fwline));
  fa_esc  : inG Σ (mono_listR (leibnizO esc_rec));
}.
#[global] Existing Instances fa_deed fa_fl fa_esc.

Definition fileAppΣ : gFunctors :=
  #[ ghost_varΣ dst; GFunctor (mono_listR (leibnizO fwline));
     GFunctor (mono_listR (leibnizO esc_rec)) ].

Global Instance subG_fileAppΣ {Σ} : subG fileAppΣ Σ -> fileAppG Σ.
Proof. solve_inG. Qed.

Section FileClaim.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* ---------------------------------------------------------------- *)
  (*  1a.  THE TAINT, AT THE PROJECTION                                 *)
  (* ---------------------------------------------------------------- *)

  Definition file_taint (c : file_fixed) : iProp Σ := echo_taint c.1.

  Global Instance file_taint_persistent c : Persistent (file_taint c).
  Proof using . rewrite /file_taint. apply _. Qed.
  Global Instance file_taint_timeless c : Timeless (file_taint c).
  Proof using . rewrite /file_taint. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (*  1b.  THE LINE LIST: authority (the ledger's) and lower bounds     *)
  (* ---------------------------------------------------------------- *)

  Definition fl_auth (c : file_fixed) (ls : list fwline) : iProp Σ :=
    own c.2 (●ML (ls : list (leibnizO fwline))).

  Definition fl_lb (c : file_fixed) (ls : list fwline) : iProp Σ :=
    own c.2 (◯ML (ls : list (leibnizO fwline))).

  Global Instance fl_lb_persistent c ls : Persistent (fl_lb c ls).
  Proof using . rewrite /fl_lb. apply _. Qed.
  Global Instance fl_lb_timeless c ls : Timeless (fl_lb c ls).
  Proof using . rewrite /fl_lb. apply _. Qed.
  Global Instance fl_auth_timeless c ls : Timeless (fl_auth c ls).
  Proof using . rewrite /fl_auth. apply _. Qed.

  Lemma fl_auth_lb (c : file_fixed) (ls : list fwline) :
    fl_auth c ls -∗ fl_auth c ls ∗ fl_lb c ls.
  Proof using .
    rewrite /fl_auth /fl_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML (ls : list (leibnizO fwline))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  Lemma fl_lb_prefix (c : file_fixed) (ls ls' : list fwline) :
    fl_auth c ls -∗ fl_lb c ls' -∗ ⌜ls' `prefix_of` ls⌝.
  Proof using .
    rewrite /fl_auth /fl_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    by iPureIntro.
  Qed.

  (* two lower bounds of one list are comparable *)
  Lemma fl_lb_lb (c : file_fixed) (ls ls' : list fwline) :
    fl_lb c ls -∗ fl_lb c ls' -∗ ⌜ls `prefix_of` ls' \/ ls' `prefix_of` ls⌝.
  Proof using .
    rewrite /fl_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    by iPureIntro.
  Qed.

  Lemma fl_auth_grow (c : file_fixed) (ls : list fwline) (ws : fwline) :
    fl_auth c ls ==∗ fl_auth c (ls ++ [ws]) ∗ fl_lb c (ls ++ [ws]).
  Proof using .
    rewrite /fl_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((ls ++ [ws]) : list (leibnizO fwline)))
            with "Ha") as "Ha".
    { apply mono_list_update. by exists [ws]. }
    iModIntro. iApply (fl_auth_lb with "Ha").
  Qed.

  (* THE BIRTH: echo's counter and era map, and the line list empty *)
  Definition file_cl (c : file_fixed) : iProp Σ :=
    (echo_cl c.1 ∗ fl_auth c [])%I.

  Lemma file_birth : ⊢ |==> ∃ c : file_fixed, file_cl c.
  Proof using .
    iMod echo_birth as (γ) "He".
    iMod (own_alloc (●ML ([] : list (leibnizO fwline)))) as (g) "Hl";
      [ apply mono_list_auth_valid |].
    iModIntro. iExists (γ, g). rewrite /file_cl /fl_auth /=. iFrame "He Hl".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2.  THE DEED AND THE TICKET                                       *)
  (* ---------------------------------------------------------------- *)

  Definition fdeed (r : file_names) (s : dst) : iProp Σ :=
    ghost_var (fn_deed r) (1/2) s.
  Definition fdeed_whole (r : file_names) (s : dst) : iProp Σ :=
    ghost_var (fn_deed r) 1 s.
  Definition ftkt (r : file_names) (s : dst) : iProp Σ :=
    ghost_var (fn_tkt r) (1/2) s.

  (* what a holder normally has: both halves, at one value *)
  Definition fown (r : file_names) (s : dst) : iProp Σ :=
    (fdeed r s ∗ ftkt r s)%I.

  Global Instance fdeed_timeless r s : Timeless (fdeed r s).
  Proof using . rewrite /fdeed. apply _. Qed.
  Global Instance fdeed_whole_timeless r s : Timeless (fdeed_whole r s).
  Proof using . rewrite /fdeed_whole. apply _. Qed.
  Global Instance ftkt_timeless r s : Timeless (ftkt r s).
  Proof using . rewrite /ftkt. apply _. Qed.
  Global Instance fown_timeless r s : Timeless (fown r s).
  Proof using . rewrite /fown. apply _. Qed.

  Lemma fdeed_agree (r : file_names) (s s' : dst) :
    fdeed r s -∗ fdeed r s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /fdeed. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  Lemma ftkt_agree (r : file_names) (s s' : dst) :
    ftkt r s -∗ ftkt r s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /ftkt. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  (* a half beside the whole is three halves: the exclusion the reader's
     law and the parking step both run on *)
  Lemma fdeed_whole_excl (r : file_names) (s s' : dst) :
    fdeed r s -∗ fdeed_whole r s' -∗ False.
  Proof using .
    rewrite /fdeed /fdeed_whole. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    iPureIntro. rewrite Qp.add_comm in Hq. exact (Qp.not_add_le_l _ _ Hq).
  Qed.

  Lemma fdeed_join (r : file_names) (s s' : dst) :
    fdeed r s -∗ fdeed r s' -∗ fdeed_whole r s.
  Proof using .
    iIntros "H1 H2". iDestruct (fdeed_agree with "H1 H2") as %<-.
    rewrite /fdeed /fdeed_whole.
    assert (Heq : (1 : Qp) = (1/2 + 1/2)%Qp) by (symmetry; exact Qp.half_half).
    rewrite Heq. iCombine "H1 H2" as "H". iExact "H".
  Qed.

  Lemma fdeed_split (r : file_names) (s : dst) :
    fdeed_whole r s -∗ fdeed r s ∗ fdeed r s.
  Proof using .
    rewrite /fdeed /fdeed_whole. iIntros "H".
    assert (Heq : (1 : Qp) = (1/2 + 1/2)%Qp) by (symmetry; exact Qp.half_half).
    iEval (rewrite Heq) in "H". iDestruct (ghost_var_split with "H") as "[H1 H2]".
    iFrame "H1 H2".
  Qed.

  Lemma fdeed_whole_update (r : file_names) (s s' : dst) :
    fdeed_whole r s ==∗ fdeed_whole r s'.
  Proof using . rewrite /fdeed_whole. iApply ghost_var_update. Qed.

  Lemma ftkt_update (r : file_names) (s s' s'' : dst) :
    ftkt r s -∗ ftkt r s' ==∗ ftkt r s'' ∗ ftkt r s''.
  Proof using .
    rewrite /ftkt. iIntros "H1 H2".
    iMod (ghost_var_update_halves s'' with "H1 H2") as "[H1 H2]".
    iModIntro. iFrame "H1 H2".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2a.  THE ESCROW                                                   *)
  (*                                                                    *)
  (*  A move the deed's holder cannot make with its own half -- the      *)
  (*  create's parent leg at `f`, whose park joins the holder's half     *)
  (*  with the claim's -- can be made by the CLAIM, if the holder parks  *)
  (*  the half there BEFORE the call.  That is the escrow: the deed      *)
  (*  WHOLE inside the claim at the exact content, and in the holder's   *)
  (*  hands a ONE-SHOT TOKEN that says the escrow has not been spent.    *)
  (*                                                                    *)
  (*  WHY THE LEDGER IS A [mono_list] AND NOT A SECOND HALF (lane        *)
  (*  F-OPEN-5's ruling correction).  The reader the escrow exists for   *)
  (*  -- create's [dirlookup] observation -- carries NOTHING LINEAR:     *)
  (*  the syscall's fold DROPS its receipt on the arm where the permit   *)
  (*  was never paid ([SpecSysOpen.cre_rcpt_kept] is [emp] at a          *)
  (*  truncating create), so a fraction handed to that piece is a        *)
  (*  fraction the deed can never get back.  So the reader's tie to the  *)
  (*  escrow must be PERSISTENT, and a persistent tie to a slot that is  *)
  (*  opened and closed once per shell round can only be an entry in a   *)
  (*  GROWING structure.  Hence: the claim keeps [esc_auth] over the     *)
  (*  list of every escrow it has ever opened, a reader keeps            *)
  (*  [esc_wit] -- a persistent lower bound naming one entry -- and the  *)
  (*  claim's invariant is that every entry but a LIVE head has been     *)
  (*  spent ([esc_recs]).  A reader then always concludes the            *)
  (*  disjunction "the claim is at my content, or my escrow is spent",   *)
  (*  and the holder of the unspent token refutes the second half.       *)
  (* ---------------------------------------------------------------- *)

  (* THE ONE-SHOT, at [mono_nat] (the taint counter's algebra, already in
     [echoOutG]): the whole authority at 0 is the token, a lower bound of
     1 is the persistent record that it was spent. *)
  Definition esc_tok (g : gname) : iProp Σ := mono_nat_auth_own g 1 0%nat.
  Definition esc_spent (g : gname) : iProp Σ := mono_nat_lb_own g 1%nat.

  Global Instance esc_spent_persistent g : Persistent (esc_spent g).
  Proof using . rewrite /esc_spent. apply _. Qed.
  Global Instance esc_spent_timeless g : Timeless (esc_spent g).
  Proof using . rewrite /esc_spent. apply _. Qed.
  Global Instance esc_tok_timeless g : Timeless (esc_tok g).
  Proof using . rewrite /esc_tok. apply _. Qed.

  Lemma esc_alloc : ⊢ |==> ∃ g : gname, esc_tok g.
  Proof using .
    iMod (mono_nat_own_alloc 0%nat) as (g) "[Ht _]".
    iModIntro. iExists g. iExact "Ht".
  Qed.

  Lemma esc_spend (g : gname) : esc_tok g ==∗ esc_spent g.
  Proof using .
    rewrite /esc_tok /esc_spent. iIntros "Ht".
    iMod (mono_nat_own_update 1%nat with "Ht") as "[_ #Hlb]"; [ lia |].
    iModIntro. iExact "Hlb".
  Qed.

  (* the refutation the truncate on the EXISTS run runs on *)
  Lemma esc_tok_spent (g : gname) : esc_tok g -∗ esc_spent g -∗ False.
  Proof using .
    rewrite /esc_tok /esc_spent. iIntros "Ht Hlb".
    iDestruct (mono_nat_lb_own_valid with "Ht Hlb") as %[_ Hle].
    iPureIntro. lia.
  Qed.

  (* THE LEDGER: the claim's authority, and a reader's persistent entry *)
  Definition esc_auth (r : file_names) (h : list esc_rec) : iProp Σ :=
    own (fn_esc r) (●ML (h : list (leibnizO esc_rec))).

  Definition esc_lb (r : file_names) (h : list esc_rec) : iProp Σ :=
    own (fn_esc r) (◯ML (h : list (leibnizO esc_rec))).

  Definition esc_wit (r : file_names) (n : nat) (s : dst) (g : gname)
      : iProp Σ :=
    (∃ h : list esc_rec, esc_lb r h ∗ ⌜h !! n = Some (s, g)⌝)%I.

  Global Instance esc_lb_persistent r h : Persistent (esc_lb r h).
  Proof using . rewrite /esc_lb. apply _. Qed.
  Global Instance esc_wit_persistent r n s g : Persistent (esc_wit r n s g).
  Proof using . rewrite /esc_wit. apply _. Qed.
  Global Instance esc_auth_timeless r h : Timeless (esc_auth r h).
  Proof using . rewrite /esc_auth. apply _. Qed.
  Global Instance esc_wit_timeless r n s g : Timeless (esc_wit r n s g).
  Proof using . rewrite /esc_wit /esc_lb. apply _. Qed.

  Lemma esc_auth_wit (r : file_names) (h : list esc_rec) (n : nat)
      (s : dst) (g : gname) :
    h !! n = Some (s, g) -> esc_auth r h -∗ esc_auth r h ∗ esc_wit r n s g.
  Proof using .
    intros Hn. rewrite /esc_auth /esc_wit /esc_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML (h : list (leibnizO esc_rec))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha". iExists h. iFrame "Hb". by iPureIntro.
  Qed.

  Lemma esc_wit_lookup (r : file_names) (h : list esc_rec) (n : nat)
      (s : dst) (g : gname) :
    esc_auth r h -∗ esc_wit r n s g -∗ ⌜h !! n = Some (s, g)⌝.
  Proof using .
    rewrite /esc_auth /esc_wit /esc_lb. iIntros "Ha Hw".
    iDestruct "Hw" as (h') "[Hb %Hn]".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro.
    change (h' !! n = Some (s, g)) in Hn.
    exact (prefix_lookup_Some _ _ _ _ Hn Hv).
  Qed.

  Lemma esc_auth_grow (r : file_names) (h : list esc_rec) (s : dst)
      (g : gname) :
    esc_auth r h ==∗ esc_auth r (h ++ [(s, g)]) ∗ esc_wit r (length h) s g.
  Proof using .
    rewrite /esc_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((h ++ [(s, g)]) : list (leibnizO esc_rec)))
            with "Ha") as "Ha".
    { apply mono_list_update. by exists [(s, g)]. }
    iModIntro.
    iApply (esc_auth_wit r (h ++ [(s, g)]) (length h) s g with "Ha").
    by apply list_lookup_middle.
  Qed.

  (* WHICH ENTRY OF THE LEDGER A WITNESS NAMES, once the claim is open:
     the LIVE head, or one that has been spent.  This is the one piece of
     arithmetic the escrow needs, and every reader below runs on it. *)
  Lemma esc_wit_head (h0 : list esc_rec) (n : nat) (s s0 : dst)
      (g g0 : gname) :
    (h0 ++ [(s0, g0)]) !! n = Some (s, g) ->
    (n < length h0)%nat /\ h0 !! n = Some (s, g)
    \/ (s0 = s /\ g0 = g).
  Proof using .
    intros Hn. apply lookup_snoc_Some in Hn.
    destruct Hn as [[Hlt Hn0] | [_ Hpair]].
    - left. by split.
    - right. by injection Hpair as -> ->.
  Qed.

  (* THE LEDGER'S INVARIANT: every escrow the claim has recorded is spent
     -- which is what the [f_esc_wrap] arm of the claim says, and what a
     reader of an entry that is NOT the live head reads off it. *)
  Definition esc_recs (h : list esc_rec) : iProp Σ :=
    ([∗ list] p ∈ h, esc_spent p.2)%I.

  Global Instance esc_recs_persistent h : Persistent (esc_recs h).
  Proof using . rewrite /esc_recs. apply _. Qed.
  Global Instance esc_recs_timeless h : Timeless (esc_recs h).
  Proof using . rewrite /esc_recs. apply _. Qed.

  Lemma esc_recs_at (h : list esc_rec) (n : nat) (s : dst) (g : gname) :
    h !! n = Some (s, g) -> esc_recs h -∗ esc_spent g.
  Proof using .
    intros Hn. rewrite /esc_recs. iIntros "#Hh".
    iDestruct (big_sepL_lookup _ _ n (s, g) Hn with "Hh") as "H".
    iExact "H".
  Qed.

  Lemma esc_recs_snoc (h : list esc_rec) (p : esc_rec) :
    esc_recs h -∗ esc_spent p.2 -∗ esc_recs (h ++ [p]).
  Proof using .
    rewrite /esc_recs. iIntros "#Hh #Hp".
    iApply big_sepL_app. iFrame "Hh". rewrite big_sepL_singleton. iExact "Hp".
  Qed.

  (* THE KEY A PARKED HOLDER CARRIES: the ledger entry, or the taint.  A
     TAINTED claim has no [f_state] at all -- [file_step_taint] drops it,
     and [file_sup_of_taint] says the taint alone answers for every view
     -- so there is no ledger to name an escrow in; the holder's key is
     then the taint itself, which is what every arm of every piece below
     already answers with.  This is what lets the park ALWAYS succeed, so
     that no program above has a branch on it. *)
  Definition esc_key (c : file_fixed) (r : file_names) (n : nat) (s : dst)
      (g : gname) : iProp Σ :=
    (esc_wit r n s g ∨ file_taint c)%I.

  Global Instance esc_key_persistent c r n s g : Persistent (esc_key c r n s g).
  Proof using . rewrite /esc_key. apply _. Qed.
  Global Instance esc_key_timeless c r n s g : Timeless (esc_key c r n s g).
  Proof using . rewrite /esc_key. apply _. Qed.

  (* fresh names, both halves of both ghosts, at any value, and the
     escrow ledger EMPTY: what every transport and the era-0 mint
     allocate.  (Lane F-OPEN-5: the ledger is the claim's alone -- no
     half of it is ever outside the claim, which is why [fown] did not
     have to change.) *)
  Lemma fnames_alloc (r1 : echo_names) (s : dst) :
    ⊢ |==> ∃ r : file_names,
        ⌜fn_cons r = r1⌝ ∗ fdeed r s ∗ fdeed r s ∗ ftkt r s ∗ ftkt r s
        ∗ esc_auth r [].
  Proof using .
    iMod (ghost_var_alloc s) as (gd) "Hd".
    iMod (ghost_var_alloc s) as (gt) "Ht".
    iMod (own_alloc (●ML ([] : list (leibnizO esc_rec)))) as (ge) "He";
      [ apply mono_list_auth_valid |].
    iModIntro. iExists (MkFileNames r1 gd gt ge).
    rewrite /fdeed /ftkt /esc_auth /=.
    iDestruct "Hd" as "[Hd1 Hd2]". iDestruct "Ht" as "[Ht1 Ht2]".
    iFrame "Hd1 Hd2 Ht1 Ht2 He". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  THE FILES' STATE ON THE VIEW                                  *)
  (* ---------------------------------------------------------------- *)

  (* THE TWO SHAPES a name of the root takes on the view, which every leg
     of [FileDeltas] is stated over: absent, or resolving to [ino] whose
     row is [a] ([FsConsPin.cons_absent] and [FsFPin.f_absent] are the
     first, definitionally). *)
  Definition name_absent (nm : fname) (av : aview) : Prop :=
    astep av FsImg.ROOTINO nm = None.

  Definition node_pin (nm : fname) (ino : Z) (a : anode) (av : aview) : Prop :=
    astep av FsImg.ROOTINO nm = Some ino /\ av !! ino = Some a.

  (* ONE NAME'S ROW, as the deed's entry says: absent, or a plain file with
     exactly these bytes and one link at the entry's inum.  The link count
     is pinned at 1 because the application never links a file (a link by
     an unverified process is an unpaid move: taint), and the pinned
     observation the read runs on wants the row on the nose. *)
  Definition f_row (av : aview) (N : fname) (o : option (Z * list (bv 8))) : Prop :=
    match o with
    | None => name_absent N av
    | Some (i, bs) => node_pin N i (MkAnode (AFile bs) 1%nat) av
    end.

  (* THE CLAIM'S READING OF THE VIEW (cut W2): every name of the class is
     in the state the deed's map says -- absent where the map has none,
     pinned where it has one -- the map names only class names, and no
     two names share an inum.  The last is a real premise: nothing in the
     view says two root entries are different rows, and a truncate or a
     write at one file's inode must leave every other file alone. *)
  Definition f_ok (av : aview) (s : dst) : Prop :=
    (forall N : fname, FileDisc.uname N -> f_row av N (s !! N))
    /\ map_Forall (fun N _ => FileDisc.uname N) s
    /\ (forall (N M : fname) (i : Z) (bs bs' : list (bv 8)),
          s !! N = Some (i, bs) -> s !! M = Some (i, bs') -> N = M).

  Lemma f_ok_row (av : aview) (s : dst) (N : fname) :
    f_ok av s -> FileDisc.uname N -> f_row av N (s !! N).
  Proof using . intros (Hr & _ & _) HN. exact (Hr N HN). Qed.

  Lemma f_ok_dom (av : aview) (s : dst) (N : fname) (p : Z * list (bv 8)) :
    f_ok av s -> s !! N = Some p -> FileDisc.uname N.
  Proof using . intros (_ & Hd & _) Hs. exact (Hd N p Hs). Qed.

  Lemma f_ok_inj (av : aview) (s : dst) (N M : fname) (i : Z)
      (bs bs' : list (bv 8)) :
    f_ok av s -> s !! N = Some (i, bs) -> s !! M = Some (i, bs') -> N = M.
  Proof using . intros (_ & _ & Hi). exact (Hi N M i bs bs'). Qed.

  (* a present entry's pin, and an absent class name's *)
  Lemma f_ok_pin (av : aview) (s : dst) (N : fname) (i : Z)
      (bs : list (bv 8)) :
    f_ok av s -> s !! N = Some (i, bs) ->
    node_pin N i (MkAnode (AFile bs) 1%nat) av.
  Proof using .
    intros Hok Hs. pose proof (f_ok_row av s N Hok (f_ok_dom av s N _ Hok Hs)) as H.
    rewrite Hs in H. exact H.
  Qed.

  Lemma f_ok_absent (av : aview) (s : dst) (N : fname) :
    f_ok av s -> FileDisc.uname N -> s !! N = None -> name_absent N av.
  Proof using .
    intros Hok HN Hs. pose proof (f_ok_row av s N Hok HN) as H.
    rewrite Hs in H. exact H.
  Qed.

  (* the row an inum holds, read as a deed entry: a plain file's bytes *)
  Definition f_rowc (av : aview) (i : Z) : option (Z * list (bv 8)) :=
    match av !! i with
    | Some (MkAnode (AFile bs) _) => Some (i, bs)
    | _ => None
    end.

  (* the contents the view holds: the root's entries FILTERED TO THE CLASS,
     each read at its row -- an entry whose row is not a plain file reads
     as nothing, which [f_ok] excludes *)
  Definition fcontent_of (av : aview) : dst :=
    match aents av FsImg.ROOTINO with
    | None => ∅
    | Some ents =>
        omap (f_rowc av) (filter (fun kv : fname * Z => FileDisc.uname kv.1) ents)
    end.

  Lemma fcontent_of_lookup (av : aview) (N : fname) :
    fcontent_of av !! N
    = if decide (FileDisc.uname N) then astep av FsImg.ROOTINO N ≫= f_rowc av
      else None.
  Proof using .
    rewrite /fcontent_of /astep.
    destruct (aents av FsImg.ROOTINO) as [ents |]; cbn [mbind option_bind];
      last first.
    { rewrite lookup_empty. by case_decide. }
    rewrite lookup_omap.
    destruct (decide (FileDisc.uname N)) as [HN | HN].
    - destruct (ents !! N) as [i |] eqn:He.
      + rewrite (map_lookup_filter_Some_2 _ ents N i He HN). reflexivity.
      + rewrite (map_lookup_filter_None_2 _ ents N); [reflexivity |]. by left.
    - rewrite (map_lookup_filter_None_2 _ ents N); [reflexivity |].
      right. intros x _. exact HN.
  Qed.

  Lemma f_ok_fcontent (av : aview) (s : dst) :
    f_ok av s -> fcontent_of av = s.
  Proof using .
    intros Hok. apply map_eq. intros N.
    change (fcontent_of av !! N = s !! N). rewrite fcontent_of_lookup.
    destruct (decide (FileDisc.uname N)) as [HN | HN].
    - pose proof (f_ok_row av s N Hok HN) as Hr.
      destruct (s !! N) as [[i bs] |] eqn:Hs; cbn [f_row] in Hr.
      + destruct Hr as (Hst & Hrow). rewrite Hst /= /f_rowc Hrow //.
      + rewrite /name_absent in Hr. by rewrite Hr.
    - destruct (s !! N) as [p |] eqn:Hs; [| reflexivity].
      exfalso. exact (HN (f_ok_dom av s N p Hok Hs)).
  Qed.

  (* THE EMPTY MAP, at a view where no class name is in the root *)
  Lemma f_ok_empty (av : aview) :
    (forall N : fname, FileDisc.uname N -> name_absent N av) -> f_ok av ∅.
  Proof using .
    intros Hab. split_and!.
    - intros N HN. rewrite lookup_empty. exact (Hab N HN).
    - apply map_Forall_empty.
    - intros N M i bs bs' Hs. by rewrite lookup_empty in Hs.
  Qed.

  (* a file's bytes are a chunk subset of an [echo … > N] line AT ITS OWN
     NAME, and the line is an ADMISSIBLE one ([EchoDisc.line_ok]:
     alphanumeric words, fewer than ten, shorter than sh's buffer) -- the
     ledger appends nothing else, and the bound is what keeps a file's row
     apart from the pinned binaries' rows (35 KB and more) at a truncate
     or a write: two rows with different contents are different inums. *)
  Definition f_bytes_typed (ls : list fwline) (N : fname) (bs : list (bv 8))
      : Prop :=
    exists (ws : wordline) (sel : list nat),
      (N, ws) ∈ ls /\ EchoDisc.line_ok ws /\ sel_ok (echo_chunks ws) sel
      /\ bs = subseq (echo_chunks ws) sel.

  Lemma f_bytes_typed_mono (ls ls' : list fwline) (N : fname) (bs : list (bv 8)) :
    ls `prefix_of` ls' -> f_bytes_typed ls N bs -> f_bytes_typed ls' N bs.
  Proof using .
    intros Hp (ws & sel & Hin & Hok & Hsel & Hbs). exists ws, sel.
    split; [| by split_and!]. eapply elem_of_prefix; [exact Hin | exact Hp].
  Qed.

  (* ...as the claim carries it: nothing at the empty map, and ONE lower
     bound of the line list serving every entry otherwise, each entry's
     name in the class (the ledger files only admitted lines).  The lower
     bound sits only in the second arm: a lower bound of the fixed-part
     list is not mintable from nothing ([◯ML []] is not a unit), and era 0
     holds no file. *)
  Definition f_typed (c : file_fixed) (s : dst) : iProp Σ :=
    (⌜s = ∅⌝
     ∨ ∃ ls : list fwline,
         fl_lb c ls
         ∗ ⌜map_Forall (fun N p => FileDisc.uname N /\ f_bytes_typed ls N p.2) s⌝)%I.

  Global Instance f_typed_persistent c s : Persistent (f_typed c s).
  Proof using . rewrite /f_typed. apply _. Qed.
  Global Instance f_typed_timeless c s : Timeless (f_typed c s).
  Proof using . rewrite /f_typed. apply _. Qed.

  Lemma f_typed_empty (c : file_fixed) : ⊢ f_typed c ∅.
  Proof using . rewrite /f_typed. by iLeft. Qed.

  (* one entry's witness *)
  Lemma f_typed_lookup (c : file_fixed) (s : dst) (N : fname) (i : Z)
      (bs : list (bv 8)) :
    s !! N = Some (i, bs) ->
    f_typed c s -∗ ∃ ls : list fwline, fl_lb c ls ∗ ⌜f_bytes_typed ls N bs⌝.
  Proof using .
    intros Hs. rewrite /f_typed. iIntros "[%He | (%ls & Hlb & %Hall)]".
    { subst s. by rewrite lookup_empty in Hs. }
    iExists ls. iFrame "Hlb". iPureIntro. exact (proj2 (Hall N (i, bs) Hs)).
  Qed.

  (* THE ONE WAY a process re-proves the typed fact at a new content: the
     entry it wrote, typed at a lower bound of its own, joins the rest --
     two lower bounds of one list are comparable, and the longer serves
     both *)
  Lemma f_typed_insert (c : file_fixed) (s : dst) (ls : list fwline)
      (N : fname) (i : Z) (bs : list (bv 8)) :
    FileDisc.uname N -> f_bytes_typed ls N bs ->
    f_typed c s -∗ fl_lb c ls -∗ f_typed c (<[N := (i, bs)]> s).
  Proof using .
    intros HN Hbt. iIntros "Hty #Hlb". rewrite /f_typed.
    iDestruct "Hty" as "[%He | (%ls0 & #Hlb0 & %Hall)]".
    { subst s. iRight. iExists ls. iFrame "Hlb". iPureIntro.
      apply map_Forall_insert_2; [by split | apply map_Forall_empty]. }
    iDestruct (fl_lb_lb with "Hlb Hlb0") as %[Hp | Hp].
    - iRight. iExists ls0. iFrame "Hlb0". iPureIntro.
      apply map_Forall_insert_2;
        [split; [exact HN | exact (f_bytes_typed_mono ls ls0 N bs Hp Hbt)] |].
      exact Hall.
    - iRight. iExists ls. iFrame "Hlb". iPureIntro.
      apply map_Forall_insert_2; [by split |].
      intros M p Hp'. destruct (Hall M p Hp') as [HM Hb].
      split; [exact HM | exact (f_bytes_typed_mono ls0 ls M p.2 Hp Hb)].
  Qed.

  (* ...at a chunk subset of a line the list holds *)
  Lemma f_typed_some (c : file_fixed) (s : dst) (ls : list fwline) (N : fname)
      (ws : wordline) (sel : list nat) (i : Z) :
    FileDisc.uname N ->
    (N, ws) ∈ ls -> EchoDisc.line_ok ws -> sel_ok (echo_chunks ws) sel ->
    f_typed c s -∗ fl_lb c ls -∗
    f_typed c (<[N := (i, subseq (echo_chunks ws) sel)]> s).
  Proof using .
    intros HN Hin Hok Hsel. iIntros "Hty #Hlb".
    iApply (f_typed_insert c s ls N i with "Hty Hlb"); [exact HN |]. by exists ws, sel.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4.  THE CLAIM                                                     *)
  (* ---------------------------------------------------------------- *)

  (* EXACT: the claim's halves at the content.  IN FLIGHT: the whole deed
     at the OLD value, the ticket's half at the old value, the content at
     the NEW one -- the window between a fire's two phases.  The two
     together are THE CORE, which is what every move the deed's holder
     pays for itself runs on. *)
  Definition f_core (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    ((∃ s : dst, fdeed r s ∗ ftkt r s ∗ f_typed c s ∗ ⌜f_ok av s⌝)
     ∨ (∃ s s' : dst, fdeed_whole r s ∗ ftkt r s ∗ f_typed c s' ∗ ⌜f_ok av s'⌝))%I.

  (* NO LIVE ESCROW: the ledger, and every escrow in it spent (section 2a).
     A claim in this arm is the claim as it was before lane F-OPEN-5 --
     the core -- with the ledger beside it. *)
  Definition f_esc_wrap (r : file_names) : iProp Σ :=
    (∃ h : list esc_rec, esc_auth r h ∗ esc_recs h)%I.

  (* THE ESCROW ARM: the deed WHOLE inside the claim at the exact content,
     the ticket's half as ever, and the ledger's HEAD naming this escrow
     -- the entry whose one-shot the holder still has.  There is no
     separate "fired" arm: a fire SPENDS the head's token, and a spent
     head is an ordinary ledger entry, so the claim is back in the arm
     above with the core IN FLIGHT. *)
  Definition f_esc_live (c : file_fixed) (r : file_names) (av : aview)
      : iProp Σ :=
    (∃ (h0 : list esc_rec) (s : dst) (g : gname),
       esc_auth r (h0 ++ [(s, g)]) ∗ esc_recs h0 ∗
       fdeed_whole r s ∗ ftkt r s ∗ f_typed c s ∗ ⌜f_ok av s⌝)%I.

  Definition f_state (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    ((f_esc_wrap r ∗ f_core c r av) ∨ f_esc_live c r av)%I.

  Global Instance f_core_timeless c r av : Timeless (f_core c r av).
  Proof using . rewrite /f_core. apply _. Qed.
  Global Instance f_esc_wrap_timeless r : Timeless (f_esc_wrap r).
  Proof using . rewrite /f_esc_wrap. apply _. Qed.
  Global Instance f_esc_live_timeless c r av : Timeless (f_esc_live c r av).
  Proof using . rewrite /f_esc_live. apply _. Qed.
  Global Instance f_state_timeless c r av : Timeless (f_state c r av).
  Proof using . rewrite /f_state. apply _. Qed.

  (* the core, built at the exact arm *)
  Lemma f_core_exact (c : file_fixed) (r : file_names) (av : aview) (s : dst) :
    f_ok av s ->
    fdeed r s -∗ ftkt r s -∗ f_typed c s -∗ f_core c r av.
  Proof using .
    intros Hok. iIntros "Hd Ht #Hty". rewrite /f_core. iLeft. iExists s.
    iFrame "Hd Ht Hty". by iPureIntro.
  Qed.

  (* ...and the claim's file state off a core, at the ledger as it stands *)
  Lemma f_state_of_core (c : file_fixed) (r : file_names) (av : aview) :
    f_esc_wrap r -∗ f_core c r av -∗ f_state c r av.
  Proof using . iIntros "Hw Hc". rewrite /f_state. iLeft. iFrame "Hw Hc". Qed.

  (* THE PREDICATE: tainted, or the four binaries are the image's AND the
     console is in one of its states AND the files are in the deed's state. *)
  Definition file_pred (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    (file_taint c
     ∨ (⌜file_fs_pure av⌝ ∗ cons_state (fn_cons r) av ∗ f_state c r av))%I.

  Global Instance file_pred_timeless c r av : Timeless (file_pred c r av).
  Proof using . rewrite /file_pred. apply _. Qed.

  (* the exact arm, as the transports and the era mint build it.  THE
     LEDGER IS A PREMISE (lane F-OPEN-5): the claim carries it in both
     arms, so a producer of the claim must hand it in -- the era mint
     hands the fresh empty one, a fire hands back the one it opened. *)
  Lemma file_pred_exact (c : file_fixed) (r : file_names) (av : aview) (s : dst) :
    file_fs_pure av -> f_ok av s ->
    cons_state (fn_cons r) av -∗ f_esc_wrap r -∗
    fdeed r s -∗ ftkt r s -∗ f_typed c s -∗
    file_pred c r av.
  Proof using .
    intros Hp Hok. iIntros "Hc Hw Hd Ht #Hty". rewrite /file_pred. iRight.
    iSplitR; [ by iPureIntro |]. iFrame "Hc".
    iApply (f_state_of_core with "Hw").
    iApply (f_core_exact c r av s Hok with "Hd Ht Hty").
  Qed.

  (* THE ECHO APPLICATION'S CLAIM IS THIS ONE WITH THE FILE FORGOTTEN --
     which is what lets every console law [AppEcho] proves at [echo_pred]
     be read here: open, apply, close with the file conjunct framed.
     Stated as an ACCESSOR so that nothing is lost. *)
  Lemma file_pred_cons (c : file_fixed) (r : file_names) (av : aview) :
    file_pred c r av -∗
    echo_pred c.1 (fn_cons r) av ∗
    (echo_pred c.1 (fn_cons r) av -∗ file_pred c r av).
  Proof using .
    rewrite /file_pred /echo_pred /file_taint.
    iIntros "[#Ht | (%Hp & Hc & Hf)]".
    { iSplitR; [ by iLeft |]. iIntros "_". by iLeft. }
    iSplitL "Hc".
    { iRight. iFrame "Hc". iPureIntro. exact (file_fs_pure_echo av Hp). }
    iIntros "[#Ht | (_ & Hc)]".
    { by iLeft. }
    iRight. iFrame "Hc Hf". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4a.  THE DEED LAW: what a holder reads off the claim              *)
  (* ---------------------------------------------------------------- *)

  (* LINEAR, [AppEcho.echo_cons_abs_law]'s shape and
     [PinnedObs.pobs_walk_dead]'s premise: the deed goes in and comes back,
     and the fact is the claim's file state at the deed's value, with its
     typed witness -- or the taint.  A holder of a half meets no in-flight
     arm. *)
  Lemma file_deed_law (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (s : dst),
           fdeed r s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdeed r s ∗
           ((⌜f_ok v s⌝ ∗ f_typed c s) ∨ file_taint c)).
  Proof using .
    iIntros "!>" (v s) "Hd Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { iSplitR; [ by iLeft |]. iFrame "Hd". by iRight. }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hw Hf] | Hf]"; last first.
    { (* THE ESCROW ARM: the deed is WHOLE in the claim, so a holder of a
         half meets it exactly as it meets the in-flight arm *)
      rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s0 g) "(_ & _ & Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    rewrite /f_core.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1) "(Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s') "(Hd' & Ht & #Hty & %Hok)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iSplitL "Hc Hw Hd' Ht".
    { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc".
      iApply (f_state_of_core with "Hw").
      iApply (f_core_exact c r v s Hok with "Hd' Ht Hty"). }
    iFrame "Hd". iLeft. iFrame "Hty". by iPureIntro.
  Qed.

  (* ...and its pure-only reading *)
  Lemma file_deed_law_pure (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (s : dst),
           fdeed r s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdeed r s ∗ (⌜f_ok v s⌝ ∨ file_taint c)).
  Proof using .
    iIntros "!>" (v s) "Hd Hp".
    iDestruct (file_deed_law c r with "Hd Hp") as "(Hp & Hd & [[%H _] | #Ht])";
      iFrame "Hp Hd"; [ iLeft; by iPureIntro | by iRight ].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  4a'.  THE ESCROW LAW: what a reader of an ESCROW reads            *)
  (*                                                                    *)
  (*  [file_deed_law]'s twin for a holder that has parked its half.  It  *)
  (*  costs NOTHING LINEAR: the witness is persistent, so a piece whose  *)
  (*  receipt the syscall's fold may drop can carry it.  What comes back *)
  (*  is a DISJUNCTION, and the second half is refuted by the unspent    *)
  (*  token ([file_escrow_law] below), which is the whole protocol.      *)
  (* ---------------------------------------------------------------- *)

  Lemma file_escrow_read (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (n : nat) (s : dst) (g : gname),
           esc_key c r n s g -∗ file_pred c r v -∗
           file_pred c r v ∗
           ((⌜f_ok v s /\ file_fs_pure v⌝ ∗ f_typed c s)
            ∨ esc_spent g ∨ file_taint c)).
  Proof using .
    iIntros "!>" (v n s g) "#Hkey Hp".
    iDestruct "Hkey" as "[#Hwit | #Ht0]"; last first.
    { iFrame "Hp". iRight. by iRight. }
    rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { iSplitR; [ by iLeft |]. iRight. by iRight. }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hwr Hf] | Hf]".
    - (* NO LIVE ESCROW: every entry of the ledger is spent, mine too *)
      rewrite /f_esc_wrap. iDestruct "Hwr" as (h) "[Ha #Hrec]".
      iDestruct (esc_wit_lookup with "Ha Hwit") as %Hn.
      iDestruct (esc_recs_at h n s g Hn with "Hrec") as "#Hsp".
      iSplitL "Hc Ha Hf".
      { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc". iLeft.
        iFrame "Hf". rewrite /f_esc_wrap. iExists h. iFrame "Ha Hrec". }
      iRight. by iLeft.
    - rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s0 g0) "(Ha & #Hrec & Hwh & Htk & #Hty & %Hok)".
      iDestruct (esc_wit_lookup with "Ha Hwit") as %Hn.
      iAssert (f_esc_live c r v ∗
               ((⌜f_ok v s /\ file_fs_pure v⌝ ∗ f_typed c s) ∨ esc_spent g))%I
        with "[Ha Hwh Htk]" as "[Hlive Hres]".
      { iSplitL "Ha Hwh Htk".
        { rewrite /f_esc_live. iExists h0, s0, g0.
          iFrame "Ha Hrec Hwh Htk Hty". by iPureIntro. }
        destruct (esc_wit_head h0 n s s0 g g0 Hn) as [[_ Hn0] | [-> ->]].
        - iRight. iApply (esc_recs_at h0 n s g Hn0 with "Hrec").
        - iLeft. iFrame "Hty". by iPureIntro. }
      iSplitL "Hc Hlive".
      { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc". by iRight. }
      iDestruct "Hres" as "[Hok | #Hsp]"; [ by iLeft | iRight; by iLeft ].
  Qed.

  (* ...AND WITH THE TOKEN IN HAND, which refutes the spent disjunct: the
     claim is AT THE ESCROWED CONTENT, full stop. *)
  Lemma file_escrow_law (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (n : nat) (s : dst) (g : gname),
           esc_key c r n s g -∗ esc_tok g -∗ file_pred c r v -∗
           file_pred c r v ∗ esc_tok g ∗
           ((⌜f_ok v s /\ file_fs_pure v⌝ ∗ f_typed c s) ∨ file_taint c)).
  Proof using .
    iDestruct (file_escrow_read c r) as "#Hrd".
    iIntros "!>" (v n s g) "#Hkey Htok Hp".
    iDestruct ("Hrd" $! v n s g with "Hkey Hp") as "[Hp Hres]".
    iDestruct "Hres" as "[Hok | [#Hsp | #Ht]]".
    - iFrame "Hp Htok". by iLeft.
    - iDestruct (esc_tok_spent g with "Htok Hsp") as %[].
    - iFrame "Hp Htok". by iRight.
  Qed.


  (* ---------------------------------------------------------------- *)
  (*  4b.  THE STEPS                                                    *)
  (*                                                                    *)
  (*  Every view move an application program pays is one of these, at   *)
  (*  the shape [AppInv.app_step] takes.  The pure premises are the     *)
  (*  deltas' business: the fire hands the mover [av] and [av'] and the *)
  (*  lanes prove them from [FsAbsDelta]'s legs.                        *)
  (* ---------------------------------------------------------------- *)

  (* the console's state is carried across a move that leaves the console
     where it was: [cons_state]'s four arms are pure guards over ghosts,
     so a move preserving both pure predicates preserves the arm *)
  Lemma cons_state_mono (r1 : echo_names) (av av' : aview) :
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    cons_state r1 av -∗ cons_state r1 av'.
  Proof using .
    intros Hab Hpr. rewrite /cons_state.
    iIntros "[[%H Htok] | [Hc | [Hc | [%H [Htok Hseal]]]]]".
    - iLeft. iFrame "Htok". iPureIntro. by apply Hab.
    - iDestruct "Hc" as (i) "(%Hp & Hk & Ht)". iRight. iLeft. iExists i.
      iFrame "Hk Ht". iPureIntro. by apply Hpr.
    - iDestruct "Hc" as (i) "(%Hp & Hk & Hs)". iRight. iRight. iLeft.
      iExists i. iFrame "Hk Hs". iPureIntro. by apply Hpr.
    - iRight. iRight. iRight. iFrame "Htok Hseal". iPureIntro. by apply Hab.
  Qed.

  (* the files' state is carried across a move that leaves them where they
     were: init's console mknod, every open that creates nothing *)
  Lemma f_core_mono (c : file_fixed) (r : file_names) (av av' : aview) :
    (forall s, f_ok av s -> f_ok av' s) ->
    f_core c r av -∗ f_core c r av'.
  Proof using .
    intros Hok. rewrite /f_core. iIntros "[Hf | Hf]".
    - iDestruct "Hf" as (s) "(Hd & Ht & #Hty & %H)". iLeft. iExists s.
      iFrame "Hd Ht Hty". iPureIntro. by apply Hok.
    - iDestruct "Hf" as (s s') "(Hw & Ht & #Hty & %H)". iRight. iExists s, s'.
      iFrame "Hw Ht Hty". iPureIntro. by apply Hok.
  Qed.

  Lemma f_state_mono (c : file_fixed) (r : file_names) (av av' : aview) :
    (forall s, f_ok av s -> f_ok av' s) ->
    f_state c r av -∗ f_state c r av'.
  Proof using .
    intros Hok. rewrite /f_state. iIntros "[[Hw Hf] | Hf]".
    - iLeft. iFrame "Hw". iApply (f_core_mono c r av av' Hok with "Hf").
    - rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s g) "(Ha & #Hh & Hwh & Ht & #Hty & %H)".
      iRight. iExists h0, s, g. iFrame "Ha Hh Hwh Ht Hty". iPureIntro.
      by apply Hok.
  Qed.

  (* THE FREE STEP: a move that touches neither the console nor a file --
     what a step wand of [AppInv.app_step]'s shape is built from at every
     such fire, and what a CONSOLE step ([UInitCons]'s four) composes with
     through [file_pred_cons]. *)
  Lemma file_step_free (c : file_fixed) (r : file_names) (av av' : aview) :
    (file_fs_pure av -> file_fs_pure av') ->
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    (forall s, f_ok av s -> f_ok av' s) ->
    file_pred c r av -∗ file_pred c r av'.
  Proof using .
    intros Hpins Hab Hpr Hok. rewrite /file_pred.
    iIntros "[#Ht | (%Hp & Hc & Hf)]"; [ by iLeft |].
    iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    by iApply (f_state_mono with "Hf").
  Qed.

  (* PHASE 1, THE PARK: the holder's deed half goes in, the arm goes from
     exact to in flight at the new content.  Update-free, so it is
     [AppInv.app_step]'s wand verbatim once lifted by [iModIntro]. *)
  Lemma file_step_park (c : file_fixed) (r : file_names) (av av' : aview)
      (s s' : dst) :
    (file_fs_pure av -> file_fs_pure av') ->
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    (f_ok av s -> f_ok av' s') ->
    fdeed r s -∗ f_typed c s' -∗
    file_pred c r av -∗ file_pred c r av'.
  Proof using .
    intros Hpins Hab Hpr Hok. iIntros "Hd #Hty' Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hp & Hc & Hf)]"; [ by iLeft |].
    iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    rewrite /f_state.
    iDestruct "Hf" as "[[Hw Hf] | Hf]"; last first.
    { rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s0 g) "(_ & _ & Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iLeft. iFrame "Hw". rewrite /f_core.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1) "(Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s0) "(Hd' & Ht & _ & %Hok0)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iDestruct (fdeed_join with "Hd Hd'") as "Hwh".
    iRight. iExists s, s'. iFrame "Hwh Ht Hty'". iPureIntro. by apply Hok.
  Qed.

  (* THE TAINTED STEP: a holder of the supply moves the view without
     answering for it ([AppInv.app_step_acc]'s consumer shape). *)
  Lemma file_step_taint (c : file_fixed) (r : file_names) (av av' : aview) :
    file_taint c -∗ file_pred c r av -∗ file_pred c r av'.
  Proof using . iIntros "#Ht _". rewrite /file_pred. by iLeft. Qed.

  (* ---------------------------------------------------------------- *)
  (*  4a''.  THE FIRE: the escrow moves the content and SPENDS          *)
  (*                                                                    *)
  (*  [file_step_park]'s twin at a parked deed, and it is ONE phase in   *)
  (*  the claim instead of two: the escrow already holds the deed whole, *)
  (*  so the arm goes straight to IN FLIGHT at the new content -- and    *)
  (*  the spent head is an ordinary ledger entry, which is why there is  *)
  (*  no third arm.  Phase 2 is [file_resync] exactly as it is today,    *)
  (*  keyed on the ticket the holder kept.                              *)
  (* ---------------------------------------------------------------- *)

  Lemma file_escrow_step (c : file_fixed) (r : file_names) (av av' : aview)
      (n : nat) (s s' : dst) (g : gname) :
    (file_fs_pure av -> file_fs_pure av') ->
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    (f_ok av s -> f_ok av' s') ->
    esc_key c r n s g -∗ esc_tok g -∗ f_typed c s' -∗
    file_pred c r av ==∗ file_pred c r av'.
  Proof using .
    intros Hpins Hab Hpr Hok. iIntros "#Hkey Htok #Hty' Hp".
    iDestruct "Hkey" as "[#Hwit | #Ht0]"; last first.
    { iModIntro. rewrite /file_pred. by iLeft. }
    rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins0 & Hc & Hf)]".
    { iModIntro. by iLeft. }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hwr Hf] | Hf]".
    { (* the ledger has no live head: my entry is spent, and the token
         says it is not *)
      rewrite /f_esc_wrap. iDestruct "Hwr" as (h) "[Ha #Hrec]".
      iDestruct (esc_wit_lookup with "Ha Hwit") as %Hn.
      iDestruct (esc_recs_at h n s g Hn with "Hrec") as "#Hsp".
      iDestruct (esc_tok_spent g with "Htok Hsp") as %[]. }
    rewrite /f_esc_live.
    iDestruct "Hf" as (h0 s0 g0) "(Ha & #Hrec & Hwh & Htk & _ & %Hok0)".
    iDestruct (esc_wit_lookup with "Ha Hwit") as %Hn.
    destruct (esc_wit_head h0 n s s0 g g0 Hn) as [[_ Hn0] | [-> ->]].
    { iDestruct (esc_recs_at h0 n s g Hn0 with "Hrec") as "#Hsp".
      iDestruct (esc_tok_spent g with "Htok Hsp") as %[]. }
    iMod (esc_spend g with "Htok") as "#Hsp".
    iModIntro. iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    iLeft. iSplitL "Ha".
    { rewrite /f_esc_wrap. iExists (h0 ++ [(s, g)]). iFrame "Ha".
      iApply (esc_recs_snoc h0 (s, g) with "Hrec"). iExact "Hsp". }
    rewrite /f_core. iRight. iExists s, s'. iFrame "Hwh Htk Hty'".
    iPureIntro. by apply Hok.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  5.  THE SUPPLY, OFF THE TAINT, AND ITS CONVERSE                   *)
  (* ---------------------------------------------------------------- *)

  Lemma file_sup_of_taint (c : file_fixed) (r : file_names) :
    file_taint c -∗ app_sup_raw (file_pred c) r.
  Proof using .
    iIntros "#Ht". rewrite /app_sup_raw. iIntros "!>" (av).
    rewrite /file_pred. by iLeft.
  Qed.

  Lemma file_taint_of_sup (c : file_fixed) (r : file_names) :
    app_sup_raw (file_pred c) r -∗ file_taint c.
  Proof using .
    rewrite /app_sup_raw. iIntros "#Hs".
    iSpecialize ("Hs" $! (∅ : aview)).
    rewrite /file_pred.
    iDestruct "Hs" as "[Ht | [%Hp _]]"; [ iExact "Ht" | ].
    exfalso. apply file_fs_pure_echo in Hp.
    destruct Hp as (_ & (_ & Hc & _) & _).
    by apply lookup_empty_Some in Hc.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  6.  THE TRANSPORTS                                                *)
  (* ---------------------------------------------------------------- *)

  (* the copy's file state is EXACT at the view's own content, whatever
     arm the original is in; the typed witness duplicates *)
  (* THE TOKEN DOES NOT CROSS (lane F-OPEN-5): the copy's LEDGER IS EMPTY
     and its arm is the EXACT one at the view's own content -- which, when
     the original is ESCROWED, is the escrowed content itself.  A durable
     copy is never stepped, so it never needs an escrow; and a one-shot
     that crossed would be a token two claims could spend. *)
  Lemma f_state_copy (c : file_fixed) (r r' : file_names) (av : aview) :
    esc_auth r' [] -∗
    fdeed r' (fcontent_of av) -∗ ftkt r' (fcontent_of av) -∗
    f_state c r av -∗ f_state c r av ∗ f_state c r' av.
  Proof using .
    iIntros "Ha' Hd' Ht'".
    iAssert (f_esc_wrap r') with "[Ha']" as "Hw'".
    { rewrite /f_esc_wrap. iExists []. iFrame "Ha'". rewrite /esc_recs //. }
    rewrite /f_state. iIntros "[[Hw Hf] | Hf]".
    - rewrite /f_core. iDestruct "Hf" as "[Hf | Hf]".
      + iDestruct "Hf" as (s) "(Hd & Ht & #Hty & %Hok)".
        pose proof (f_ok_fcontent av s Hok) as Hc.
        iSplitL "Hw Hd Ht".
        * iLeft. iFrame "Hw". iLeft. iExists s. iFrame "Hd Ht Hty".
          by iPureIntro.
        * iLeft. iFrame "Hw'". iLeft. iExists (fcontent_of av).
          iFrame "Hd' Ht'". rewrite Hc. iFrame "Hty". by iPureIntro.
      + iDestruct "Hf" as (s s') "(Hwh & Ht & #Hty & %Hok)".
        pose proof (f_ok_fcontent av s' Hok) as Hc.
        iSplitL "Hw Hwh Ht".
        * iLeft. iFrame "Hw". iRight. iExists s, s'. iFrame "Hwh Ht Hty".
          by iPureIntro.
        * iLeft. iFrame "Hw'". iLeft. iExists (fcontent_of av).
          iFrame "Hd' Ht'". rewrite Hc. iFrame "Hty". by iPureIntro.
    - rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s g) "(Ha & #Hh & Hwh & Ht & #Hty & %Hok)".
      pose proof (f_ok_fcontent av s Hok) as Hc.
      iSplitL "Ha Hwh Ht".
      + iRight. iExists h0, s, g. iFrame "Ha Hh Hwh Ht Hty". by iPureIntro.
      + iLeft. iFrame "Hw'". iLeft. iExists (fcontent_of av).
        iFrame "Hd' Ht'". rewrite Hc. iFrame "Hty". by iPureIntro.
  Qed.

  (* the typed witness at the view's own content, off either arm *)
  Lemma f_state_typed_at (c : file_fixed) (r : file_names) (av : aview) :
    f_state c r av -∗ f_state c r av ∗ f_typed c (fcontent_of av).
  Proof using .
    rewrite /f_state. iIntros "[[Hw Hf] | Hf]".
    - rewrite /f_core. iDestruct "Hf" as "[Hf | Hf]".
      + iDestruct "Hf" as (s) "(Hd & Ht & #Hty & %Hok)".
        rewrite (f_ok_fcontent av s Hok). iSplitL; [| iExact "Hty"].
        iLeft. iFrame "Hw". iLeft. iExists s. iFrame "Hd Ht Hty".
        by iPureIntro.
      + iDestruct "Hf" as (s s') "(Hwh & Ht & #Hty & %Hok)".
        rewrite (f_ok_fcontent av s' Hok). iSplitL; [| iExact "Hty"].
        iLeft. iFrame "Hw". iRight. iExists s, s'. iFrame "Hwh Ht Hty".
        by iPureIntro.
    - rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s g) "(Ha & #Hh & Hwh & Ht & #Hty & %Hok)".
      rewrite (f_ok_fcontent av s Hok). iSplitL; [| iExact "Hty"].
      iRight. iExists h0, s, g. iFrame "Ha Hh Hwh Ht Hty". by iPureIntro.
  Qed.

  (* the original, read as its echo half and its file half, under the
     later the transports receive it at *)
  Lemma file_pred_split (c : file_fixed) (r : file_names) (av : aview) :
    file_pred c r av -∗
    echo_pred c.1 (fn_cons r) av
    ∗ (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av)).
  Proof using .
    rewrite /file_pred /echo_pred /file_taint.
    iIntros "[#Ht | (%Hp & Hc & Hf)]".
    { iSplitR; by iLeft. }
    iSplitL "Hc".
    { iRight. iFrame "Hc". iPureIntro. exact (file_fs_pure_echo av Hp). }
    iRight. iFrame "Hf". by iPureIntro.
  Qed.

  (* ...and put back together, at any console pair the echo half came
     back at *)
  Lemma file_pred_join (c : file_fixed) (r : file_names) (av : aview) :
    echo_pred c.1 (fn_cons r) av -∗
    (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av)) -∗
    file_pred c r av.
  Proof using .
    rewrite /file_pred /echo_pred /file_taint.
    iIntros "[#Ht | (_ & Hc)] [#Ht' | (%Hp & Hf)]"; try by iLeft.
    iRight. iFrame "Hc Hf". by iPureIntro.
  Qed.

  (* THE COMMIT'S TRANSPORT ([App.Happ_xfer]): the echo half by echo's
     transport, the file half by a fresh deed and ticket allocated at the
     view's content OUTSIDE the later.  The copy's console pair is the one
     echo's transport chose. *)
  Lemma file_xfer (c : file_fixed) : ⊢ app_xfer_raw (file_pred c).
  Proof using .
    rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    iDestruct (echo_xfer c.1) as "#Hex".
    iAssert (▷ (echo_pred c.1 (fn_cons r) av
                ∗ (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av))))%I
      with "[H]" as "[He Hrest]".
    { iNext. by iApply file_pred_split. }
    iMod ("Hex" $! (fn_cons r) av with "He") as "[He He']".
    iDestruct "He'" as (rc) "He'".
    iMod (fnames_alloc rc (fcontent_of av)) as (r') "(%Hrc & Hd1 & _ & Ht1 & _ & Ha1)".
    iModIntro.
    iAssert (▷ (file_pred c r av ∗ file_pred c r' av))%I
      with "[He He' Hrest Hd1 Ht1 Ha1]" as "[H1 H2]"; last first.
    { iFrame "H1". iExists r'. iExact "H2". }
    iNext.
    iDestruct "Hrest" as "[#Ht | (%Hp & Hf)]".
    { iSplitL "He".
      { iApply (file_pred_join with "He"). by iLeft. }
      iApply (file_pred_join with "[He']").
      { rewrite Hrc. iExact "He'". }
      by iLeft. }
    iDestruct (f_state_copy c r r' av with "Ha1 Hd1 Ht1 Hf") as "[Hf Hf']".
    iSplitL "He Hf".
    { iApply (file_pred_join with "He"). iRight. iFrame "Hf". by iPureIntro. }
    iApply (file_pred_join with "[He']").
    { rewrite Hrc. iExact "He'". }
    iRight. iFrame "Hf'". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  6a.  THE BOOT RESOURCE, AND THE BOOT TRANSPORT                    *)
  (* ---------------------------------------------------------------- *)

  (* WHAT /init IS HANDED AT THE ERA MINT: echo's (the console key or
     flag) and THE DEED -- both halves the process chain owns, at the
     clone's content -- beside the typed witness of that content, or the
     taint.  The witness sits under ONE later: it is read off the
     original arm, which the transport only sees under [▷]; /init strips
     it at its first step, everything under it being timeless. *)
  Definition file_boot (c : file_fixed) (k : nat) (r : file_names) : iProp Σ :=
    (echo_boot c.1 k (fn_cons r)
     ∗ ∃ s : dst, fown r s ∗ ▷ (f_typed c s ∨ file_taint c))%I.

  Lemma file_xfer_boot (c : file_fixed) (k : nat) :
    ⊢ □ (∀ (r : file_names) (av : aview),
           ▷ file_pred c r av ==∗ ▷ file_pred c r av ∗
           ∃ r' : file_names, ▷ file_pred c r' av ∗ file_boot c k r').
  Proof using .
    iIntros "!>" (r av) "H".
    iDestruct (echo_xfer_boot c.1 k) as "#Hex".
    iAssert (▷ (echo_pred c.1 (fn_cons r) av
                ∗ (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av))))%I
      with "[H]" as "[He Hrest]".
    { iNext. by iApply file_pred_split. }
    iMod ("Hex" $! (fn_cons r) av with "He") as "[He He']".
    iDestruct "He'" as (rc) "[He' Hb]".
    iMod (fnames_alloc rc (fcontent_of av)) as (r') "(%Hrc & Hd1 & Hd2 & Ht1 & Ht2 & Ha1)".
    iModIntro.
    iAssert (▷ (file_pred c r av ∗ file_pred c r' av
                ∗ (f_typed c (fcontent_of av) ∨ file_taint c)))%I
      with "[He He' Hrest Hd1 Ht1 Ha1]" as "(H1 & H2 & H3)"; last first.
    { iFrame "H1". iExists r'. iFrame "H2". rewrite /file_boot Hrc. iFrame "Hb".
      iExists (fcontent_of av). rewrite /fown. iFrame "Hd2 Ht2 H3". }
    iNext.
    iDestruct "Hrest" as "[#Ht | (%Hp & Hf)]".
    { iSplitL "He"; [ iApply (file_pred_join with "He"); by iLeft |].
      iSplitL "He'"; [| by iRight ].
      iApply (file_pred_join with "[He']").
      { rewrite Hrc. iExact "He'". }
      by iLeft. }
    iDestruct (f_state_typed_at with "Hf") as "[Hf #Hty]".
    iDestruct (f_state_copy c r r' av with "Ha1 Hd1 Ht1 Hf") as "[Hf Hf']".
    iSplitL "He Hf".
    { iApply (file_pred_join with "He"). iRight. iFrame "Hf". by iPureIntro. }
    iSplitL "He' Hf'"; [| by iLeft ].
    iApply (file_pred_join with "[He']").
    { rewrite Hrc. iExact "He'". }
    iRight. iFrame "Hf'". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  7.  THE ERA-0 CLAIM                                               *)
  (* ---------------------------------------------------------------- *)

  (* at the map a boot founds its file system at, when the disk is mkfs's
     image: echo's era-0 claim (its console key beside it, unused here)
     with NO FILE of the class present -- law L4, the class is absent from
     the image's root -- and the deed at the empty map *)
  Lemma file_init (c : file_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    ⊢ |==> ∃ r : file_names, file_pred c r (abs_view (fss_inodes S)).
  Proof using .
    intros Hdk Hrec HS.
    iMod (echo_init c.1 dk D S Hdk Hrec HS) as (rc) "He".
    iMod (fnames_alloc rc ∅) as (r) "(%Hrc & Hd1 & _ & Ht1 & _ & Ha1)".
    iModIntro. iExists r.
    iApply (file_pred_join with "[He]").
    { rewrite Hrc. iExact "He". }
    iRight. iSplitR.
    { iPureIntro. exact (file_fs_era0 dk D S Hdk Hrec HS). }
    rewrite /f_state. iLeft. iSplitL "Ha1".
    { rewrite /f_esc_wrap. iExists []. iFrame "Ha1". rewrite /esc_recs //. }
    rewrite /f_core. iLeft. iExists ∅.
    iSplitL "Hd1"; [ iExact "Hd1" |].
    iSplitL "Ht1"; [ iExact "Ht1" |].
    iSplitR; [ iApply f_typed_empty |].
    iPureIntro. apply f_ok_empty. intros N HN.
    exact (era0_recovery_class_absent txt_name dk D S N txt_laws
             Hdk Hrec HS HN).
  Qed.

  (* ...at the theorem's own literal shape ([App.xv6_app_adequacy]'s
     [Happ_init]), [AppEcho.echo_init_img]'s composition verbatim *)
  Lemma file_init_img (c : file_fixed) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    fs_blocks dk = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    ⊢ |==> ∃ r : file_names,
        file_pred c r (abs_view (fss_inodes
          (FsDurImg.img_state (fs_blocks dk) sb nib))).
  Proof using .
    intros Himg Hdk -> ->.
    pose proof (img_snap_ok dk ndisk fsimg_sb nib fsimg_cov Himg) as HS.
    rewrite Hdk in HS. rewrite Hdk.
    exact (file_init c dk era0_D _ Hdk (era0_recovery dk Hdk) HS).
  Qed.
End FileClaim.

(* ====================================================================== *)
(*  8.  THE STEPS AT THE ERA'S RECORD                                      *)
(*                                                                        *)
(*  [AppInv.app_step] and [app_inv] name the era's record ([file_app]) and *)
(*  the kernel's classes; the two shapes a fire consumes are stated here, *)
(*  at the context [TreeMove] uses for the same two.                       *)
(* ====================================================================== *)
Section FileClaimEra.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* ...at [AppInv.app_step]'s own shape, with the record equation the era
     carries: the fire hands the mover the node it chose and the mover
     answers with the step.  [tree_app_step_of]'s twin. *)
  Lemma file_app_step_park (c : file_fixed) (r : file_names)
      (i : Z) (I : gmap Z fs_node) (av' : aview) (s s' : dst) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (file_fs_pure (abs_view I) -> file_fs_pure av') ->
    (cons_absent (abs_view I) -> cons_absent av') ->
    (forall j, cons_present_at j (abs_view I) -> cons_present_at j av') ->
    (f_ok (abs_view I) s -> f_ok av' s') ->
    fdeed r s -∗ f_typed c s' -∗ app_step i I av'.
  Proof using .
    intros Heq Hpins Hab Hpr Hok. iIntros "Hd #Hty'". rewrite /app_step.
    iIntros (n') "%Hav Hp". rewrite Heq. cbn [app_pred app_run app_names].
    rewrite Hav. iModIntro. iNext.
    iApply (file_step_park c r _ _ s s' Hpins Hab Hpr Hok with "Hd Hty' Hp").
  Qed.

  (* THE TAINTED STEP at [AppInv.app_step]'s shape ([TreeMove.tree_app_step_taint]'s
     twin): a holder of the taint answers any move. *)
  Lemma file_app_step_taint (c : file_fixed) (r : file_names)
      (i : Z) (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    file_taint c -∗ app_step i I av'.
  Proof using .
    intros Heq. iIntros "#Ht". rewrite /app_step.
    iIntros (n') "%Hav Hp". rewrite Heq. cbn [app_pred app_run app_names].
    iModIntro. iNext. iApply (file_step_taint with "Ht Hp").
  Qed.

  (* PHASE 2, THE RESYNC: at the era's record, inside the fire's own fupd
     (the mask holds [appN]), the ticket buys both ghosts at the content
     the post view actually has -- or the taint hands the ticket back. *)
  Lemma file_resync (γfs : fs_names) (c : file_fixed)
      (r : file_names) (s s' : dst) (I' : gmap Z fs_node) (E : coPset) :
    ↑appN ⊆ E ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    fcontent_of (abs_view I') = s' -> s <> s' ->
    app_inv γfs -∗ ftkt r s -∗
    ghost_map_auth (fs_top γfs) (1/2) I' ={E}=∗
      ghost_map_auth (fs_top γfs) (1/2) I' ∗
      (fown r s' ∨ (ftkt r s ∗ file_taint c)).
  Proof using .
    intros HE Heq Hcont Hne. iIntros "#Hinv Htk Hka".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { (* TAINTED: the ticket comes back beside the taint *)
      iMod ("Hclose" with "[Hh Hx]") as "_".
      { iNext. rewrite /app_body. iExists I'. iFrame "Hh Hx".
        rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
        iSplitL; [ by iLeft | by iPureIntro ]. }
      iModIntro. iFrame "Hka". iRight. iFrame "Htk Ht". }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hw Hf] | Hf]"; last first.
    { (* THE ESCROW ARM: refuted exactly as the exact arm is -- the ticket
         says the claim is at the OLD content, and the escrow parks the
         deed AT that content, while the view says it moved *)
      rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s0 g) "(_ & _ & _ & Ht' & _ & %Hok)".
      iDestruct (ftkt_agree with "Htk Ht'") as %<-.
      exfalso. apply Hne. rewrite -Hcont. symmetry. exact (f_ok_fcontent _ _ Hok). }
    rewrite /f_core.
    iDestruct "Hf" as "[Hf | Hf]".
    { (* EXACT: refuted -- the ticket says the claim's value is the OLD
         content, the view says the content moved *)
      iDestruct "Hf" as (s0) "(Hd & Ht' & _ & %Hok)".
      iDestruct (ftkt_agree with "Htk Ht'") as %<-.
      exfalso. apply Hne. rewrite -Hcont. symmetry. exact (f_ok_fcontent _ _ Hok). }
    iDestruct "Hf" as (s0 s1) "(Hwh & Ht' & #Hty & %Hok)".
    iDestruct (ftkt_agree with "Htk Ht'") as %<-.
    assert (Hs1 : s1 = s') by (rewrite -Hcont; symmetry; exact (f_ok_fcontent _ _ Hok)).
    subst s1.
    iMod (fdeed_whole_update r s s' with "Hwh") as "Hwh".
    iDestruct (fdeed_split with "Hwh") as "[Hd1 Hd2]".
    iMod (ftkt_update r s s s' with "Htk Ht'") as "[Htk Ht']".
    iMod ("Hclose" with "[Hh Hx Hc Hw Hd2 Ht']") as "_".
    { iNext. rewrite /app_body. iExists I'. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names].
      iApply (file_pred_exact c r _ s' Hpins Hok with "Hc Hw Hd2 Ht' Hty"). }
    iModIntro. iFrame "Hka". iLeft. rewrite /fown. iFrame "Hd1 Htk".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  9.  THE ESCROW AT THE ERA'S RECORD (lane F-OPEN-5)                  *)
  (*                                                                      *)
  (*  PARK, FIRE, RETURN.  The park and the return move no view, so they   *)
  (*  are not [app_step]s: they open [app_inv] on their own, at any mask   *)
  (*  holding [appN] -- which is where the redirect child is before and    *)
  (*  after its [open] and NOT where a commit fires, so the mask that      *)
  (*  refuted F-OPEN-4's second invariant is never in play.                *)
  (* ------------------------------------------------------------------ *)

  (* THE PARK: the holder's half goes into the claim, a fresh one-shot is
     appended to the ledger, and the holder keeps the TICKET (which is what
     [file_resync] keys on) beside the token and the persistent witness. *)
  Lemma file_escrow_park (γfs : fs_names) (c : file_fixed) (r : file_names)
      (s : dst) (E : coPset) :
    ↑appN ⊆ E ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ fown r s ={E}=∗
      ∃ (n : nat) (g : gname), esc_key c r n s g ∗ esc_tok g ∗ ftkt r s.
  Proof using .
    intros HE Heq. iIntros "#Hinv [Hd Htk]".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hka & Hp & >%Hdom & #Hx)".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { iMod ("Hclose" with "[Hka Hx]") as "_".
      { iNext. rewrite /app_body. iExists I0. iFrame "Hka Hx".
        iSplitL; [| by iPureIntro ].
        rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
        by iLeft. }
      iMod esc_alloc as (g) "Htok". iModIntro.
      iExists 0%nat, g. iFrame "Htok Htk". rewrite /esc_key. by iRight. }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hwr Hf] | Hf]"; last first.
    { (* an escrow is already live: its whole deed refutes the holder's
         half, so the park meets no escrow of anybody else's *)
      rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s0 g0) "(_ & _ & Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    rewrite /f_core.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1) "(Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s0) "(Hd' & Htk' & #Hty & %Hok)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iDestruct (fdeed_join with "Hd Hd'") as "Hwh".
    iMod esc_alloc as (g) "Htok".
    rewrite /f_esc_wrap. iDestruct "Hwr" as (h) "[Ha #Hrec]".
    iMod (esc_auth_grow r h s g with "Ha") as "[Ha #Hwit]".
    iMod ("Hclose" with "[Hka Hx Hc Ha Hwh Htk']") as "_".
    { iNext. rewrite /app_body. iExists I0. iFrame "Hka Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
      iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc".
      rewrite /f_state. iRight. rewrite /f_esc_live.
      iExists h, s, g. iFrame "Ha Hrec Hwh Htk' Hty". by iPureIntro. }
    iModIntro. iExists (length h), g. iFrame "Htok Htk".
    rewrite /esc_key. by iLeft.
  Qed.

  (* THE RETURN: an escrow that never fired comes home.  The token is SPENT
     on the way out -- that is what keeps the ledger's invariant ("every
     entry but a live head is spent") true, and it is what makes a stale
     witness of this escrow read [esc_spent] ever after. *)
  Lemma file_escrow_return (γfs : fs_names) (c : file_fixed) (r : file_names)
      (n : nat) (s : dst) (g : gname) (E : coPset) :
    ↑appN ⊆ E ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ esc_key c r n s g -∗ esc_tok g -∗ ftkt r s ={E}=∗
      fown r s ∨ file_taint c.
  Proof using .
    intros HE Heq. iIntros "#Hinv #Hkey Htok Htk".
    iDestruct "Hkey" as "[#Hwit | #Ht0]"; last first.
    { iModIntro. by iRight. }
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hka & Hp & >%Hdom & #Hx)".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { iMod ("Hclose" with "[Hka Hx]") as "_".
      { iNext. rewrite /app_body. iExists I0. iFrame "Hka Hx".
        iSplitL; [| by iPureIntro ].
        rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
        by iLeft. }
      iModIntro. iRight. iExact "Ht". }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hwr Hf] | Hf]".
    { rewrite /f_esc_wrap. iDestruct "Hwr" as (h) "[Ha #Hrec]".
      iDestruct (esc_wit_lookup with "Ha Hwit") as %Hn.
      iDestruct (esc_recs_at h n s g Hn with "Hrec") as "#Hsp".
      iDestruct (esc_tok_spent g with "Htok Hsp") as %[]. }
    rewrite /f_esc_live.
    iDestruct "Hf" as (h0 s0 g0) "(Ha & #Hrec & Hwh & Htk' & #Hty & %Hok)".
    iDestruct (esc_wit_lookup with "Ha Hwit") as %Hn.
    destruct (esc_wit_head h0 n s s0 g g0 Hn) as [[_ Hn0] | [-> ->]].
    { iDestruct (esc_recs_at h0 n s g Hn0 with "Hrec") as "#Hsp".
      iDestruct (esc_tok_spent g with "Htok Hsp") as %[]. }
    iMod (esc_spend g with "Htok") as "#Hsp".
    iDestruct (fdeed_split with "Hwh") as "[Hd1 Hd2]".
    iMod ("Hclose" with "[Hka Hx Hc Ha Hd2 Htk']") as "_".
    { iNext. rewrite /app_body. iExists I0. iFrame "Hka Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names].
      iApply (file_pred_exact c r _ s Hpins Hok with "Hc [Ha] Hd2 Htk' Hty").
      rewrite /f_esc_wrap. iExists (h0 ++ [(s, g)]). iFrame "Ha".
      iApply (esc_recs_snoc h0 (s, g) with "Hrec"). iExact "Hsp". }
    iModIntro. iLeft. rewrite /fown. iFrame "Hd1 Htk".
  Qed.

  (* THE FIRE, at [AppInv.app_step]'s own shape ([file_app_step_park]'s
     twin at a parked deed): the escrow moves the content and spends. *)
  Lemma file_app_step_escrow (c : file_fixed) (r : file_names)
      (i : Z) (I : gmap Z fs_node) (av' : aview)
      (n : nat) (s s' : dst) (g : gname) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (file_fs_pure (abs_view I) -> file_fs_pure av') ->
    (cons_absent (abs_view I) -> cons_absent av') ->
    (forall j, cons_present_at j (abs_view I) -> cons_present_at j av') ->
    (f_ok (abs_view I) s -> f_ok av' s') ->
    esc_key c r n s g -∗ esc_tok g -∗ f_typed c s' -∗ app_step i I av'.
  Proof using .
    intros Heq Hpins Hab Hpr Hok. iIntros "#Hkey Htok #Hty'".
    rewrite /app_step. iIntros (nd) "%Hav Hp".
    rewrite Heq. cbn [app_pred app_run app_names]. rewrite Hav.
    iDestruct "Hp" as ">Hp".
    iMod (file_escrow_step c r (abs_view I) av' n s s' g
            Hpins Hab Hpr Hok with "Hkey Htok Hty' Hp") as "Hp".
    iModIntro. iNext. iExact "Hp".
  Qed.

End FileClaimEra.
