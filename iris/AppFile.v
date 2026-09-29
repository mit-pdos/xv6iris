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

   THE DEED is a [ghost_var_frac] over [FileState.fstate] in two halves: the claim
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
Require UnionAdm.                  (* [UnionAdm.srec]: the sync lists' records *)
Require Import FileName.           (* its laws: [txt_laws], L4 at era 0 *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  NAMES: THE FIXED PART AND THE INSTANCE                             *)
(* ====================================================================== *)

(* a typed line, as the console sees it: the words of one [echo … > N] *)
Definition wordline : Type := list (list (bv 8)).

(* ...AND A REDIRECT LINE AS THE FILE MODEL READS IT: the file the line
   redirects to beside its words -- the model's [FileDisc.echof_ws] shape
   (cut W2 of claude-notes/design/filenames.md) *)
Definition fwline : Type := list (bv 8) * wordline.

(* THE LINE THE LEDGER FILES: EVERY complete line, as the model parses it
   (a [sync] line an entry like a redirect, sync design section 4.5), so a
   lower bound ending in a line names that line's global position; the
   redirect lines are the list's projection ([fl_redirs]) *)
Definition fl_line : Type := FileDisc.uline.

Notation fl_redirs ls := (omap FileDisc.echof_ws ls).

(* a list ending in a redirect line has the line among its redirects *)
Lemma fl_redirs_last (ls : list fl_line) (ws : list (list (bv 8))) (N : list (bv 8)) :
  last ls = Some (FileDisc.LEchoF ws N) -> (N, ws) ∈ fl_redirs ls.
Proof using .
  intros Hl. destruct ls as [| x ls0] using rev_ind; [discriminate Hl |].
  rewrite last_snoc in Hl. injection Hl as ->.
  rewrite omap_app. apply elem_of_app. right. cbn. by apply list_elem_of_singleton.
Qed.

Lemma fl_redirs_prefix (ls ls' : list fl_line) :
  ls `prefix_of` ls' -> fl_redirs ls `prefix_of` fl_redirs ls'.
Proof using . intros [z ->]. rewrite omap_app. by eexists. Qed.

(* THE FIXED PART: echo's (the taint counter and the era map) beside the
   LINE LIST's name -- a [mono_list] of the complete lines ([fl_line]) the
   console has received, in order, whose authority the ledger keeps and whose
   lower bounds ride the input tag (design section 4) -- and THE SYNC PART's
   run-long names (sync design section 4.5, ruling (i) after SY3-A3b: the
   sync ghost state belongs to the file application): the sync REGISTRY
   (era -> that era's sync list, a [ghost_map nat gname] whose authority the
   ledger keeps), the COMMIT-ERA counter (a [mono_nat], its full authority
   in the durable copy) and the MACHINE's started counter's gname, which the
   birth is handed and stores.  Both counters are read at [fa_st]. *)
Record file_fixed := MkFileFixed {
  ff_echo : echo_fixed;
  ff_fl   : gname;
  ff_reg  : gname;
  ff_cm   : gname;
  ff_st   : gname;
  (* THE RUN-LONG SYNC HISTORY (sync SY3-A4, the owner's ruling on the
     floor): a [mono_list] of sync records whose FULL authority travels
     with the durable copy across every era (the copy's list and it have
     the same content), so a lower bound of it -- the ledger's floor --
     is below every later copy's list without naming an era *)
  ff_hist : gname;
  (* THE RUN REGISTRY (sync SY3-A4): era -> the era's RUNNING claim's round
     position and deed gnames, a [ghost_map nat (gname * gname)] whose
     authority travels with the durable copy and which the PowerOn transport
     writes when it founds the era's running claim.  The sync hook is fired
     at whatever running record the kernel's runner holds; the registration
     is how the deed's holder (sh) learns that record is its own *)
  ff_run  : gname;
}.

(* THE INSTANCE: echo's console pair beside THE DEED's and THE TICKET's
   names *)
Record file_names := MkFileNames {
  fn_cons : echo_names;
  fn_deed : gname;
  fn_tkt  : gname;
  fn_esc  : gname;                     (* THE ESCROW LEDGER (section 2a) *)
  (* THE SYNC PART (sync design section 4.5, lane SY3-A3a; the union's
     [sync_claim] reads them): the instance's SYNC LIST (a
     [mono_list] of [UnionAdm.srec]), its ERA -- pure, in the LEDGER's
     numbering (the birth is era 0, the boot at [gen_id] era [S gen_id])
     -- and its ROLE: [true] the durable copy, [false] the running claim *)
  fn_sync : gname;
  fn_era  : nat;
  fn_role : bool;
  (* THE ROUND POSITION (sync design section 4.5 "The round position", lane
     SY3-A3b): a [ghost_var_frac nat], "lines consumed" -- one half in the
     running claim's sync part, one with the deed's holder (sh's deed
     lend), both advanced at each round's start ([fpos_update]).  A
     durable copy carries none. *)
  fn_pos  : gname;
}.

Global Instance file_names_inhabited : Inhabited file_names :=
  populate (MkFileNames inhabitant inhabitant inhabitant inhabitant inhabitant 0 false inhabitant).

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

(* ...and the SYNC cameras (sync design section 4.5, lanes SY3-A3a/A3bc):
   the per-era SYNC LISTS and the REGISTRY era -> that era's sync list's
   gname, as ordinary instances; and TWO NON-INSTANCE fields, [fa_st] and
   [fa_pos] (single colon: NEVER resolved).  [fa_st] is the camera both
   counters ([ff_st], [ff_cm]) are read at: [ff_st] is the MACHINE's
   started counter, so its [mono_natG] must be the machine's
   ([RiscvAdequacy.riscv_pre_genGS], lined up with the record's by A1's
   equation [riscvF_genGS = riscv_pre_genGS]) -- the union's top theorem
   BUILDS its instance with [fa_st := riscv_pre_genGS]
   ([UUnionBootAdequacy]).  [fa_pos] is the round position's camera
   ([fpos]).  Every use is spelled [@mono_nat_auth_own Σ fa_st … (DfracOwn q) …] /
   [@ghost_var Σ nat fa_pos … (DfracOwn q) …]: a scope has several [mono_natG] and
   [ghost_varG nat] instances ([echoOutG]'s among them), and a second one
   picked by resolution is the duplicate-class trap. *)
Class fileAppG (Σ : gFunctors) := FileAppG {
  fa_deed : ghost_varG Σ dst;
  fa_fl   : inG Σ (mono_listR (leibnizO fl_line));
  fa_esc  : inG Σ (mono_listR (leibnizO esc_rec));
  fa_sync : inG Σ (mono_listR (leibnizO UnionAdm.srec));
  fa_reg  : ghost_mapG Σ nat gname;
  fa_run  : ghost_mapG Σ nat (gname * gname);
  fa_st   : mono_natG Σ;
  fa_pos  : ghost_varG Σ nat;
}.
#[global] Existing Instances fa_deed fa_fl fa_esc fa_sync fa_reg fa_run.

Definition fileAppΣ : gFunctors :=
  #[ ghost_varΣ dst; GFunctor (mono_listR (leibnizO fl_line));
     GFunctor (mono_listR (leibnizO esc_rec));
     GFunctor (mono_listR (leibnizO UnionAdm.srec));
     ghost_mapΣ nat gname; ghost_mapΣ nat (gname * gname) ].

(* NOT an instance: the two camera fields are the CALLER's choice (the
   machine's started counter's, and a [ghost_varG nat] it already has) *)
Definition fileAppG_of {Σ} (HS : subG fileAppΣ Σ) (HSt : mono_natG Σ)
    (HPos : ghost_varG Σ nat) : fileAppG Σ.
Proof.
  refine (FileAppG Σ _ _ _ _ _ _ HSt HPos); solve_inG.
Defined.

Section FileClaim.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* ---------------------------------------------------------------- *)
  (*  1a.  THE TAINT, AT THE PROJECTION                                 *)
  (* ---------------------------------------------------------------- *)

  Definition file_taint (c : file_fixed) : iProp Σ := echo_taint (ff_echo c).

  Global Instance file_taint_persistent c : Persistent (file_taint c).
  Proof using . rewrite /file_taint. apply _. Qed.
  Global Instance file_taint_timeless c : Timeless (file_taint c).
  Proof using . rewrite /file_taint. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (*  1b.  THE LINE LIST: authority (the ledger's) and lower bounds     *)
  (* ---------------------------------------------------------------- *)

  Definition fl_auth (c : file_fixed) (ls : list fl_line) : iProp Σ :=
    own (ff_fl c) (●ML (ls : list (leibnizO fl_line))).

  Definition fl_lb (c : file_fixed) (ls : list fl_line) : iProp Σ :=
    own (ff_fl c) (◯ML (ls : list (leibnizO fl_line))).

  Global Instance fl_lb_persistent c ls : Persistent (fl_lb c ls).
  Proof using . rewrite /fl_lb. apply _. Qed.
  Global Instance fl_lb_timeless c ls : Timeless (fl_lb c ls).
  Proof using . rewrite /fl_lb. apply _. Qed.
  Global Instance fl_auth_timeless c ls : Timeless (fl_auth c ls).
  Proof using . rewrite /fl_auth. apply _. Qed.

  Lemma fl_auth_lb (c : file_fixed) (ls : list fl_line) :
    fl_auth c ls -∗ fl_auth c ls ∗ fl_lb c ls.
  Proof using .
    rewrite /fl_auth /fl_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML (ls : list (leibnizO fl_line))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  Lemma fl_lb_prefix (c : file_fixed) (ls ls' : list fl_line) :
    fl_auth c ls -∗ fl_lb c ls' -∗ ⌜ls' `prefix_of` ls⌝.
  Proof using .
    rewrite /fl_auth /fl_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    by iPureIntro.
  Qed.

  (* two lower bounds of one list are comparable *)
  Lemma fl_lb_lb (c : file_fixed) (ls ls' : list fl_line) :
    fl_lb c ls -∗ fl_lb c ls' -∗ ⌜ls `prefix_of` ls' \/ ls' `prefix_of` ls⌝.
  Proof using .
    rewrite /fl_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    by iPureIntro.
  Qed.

  Lemma fl_auth_grow (c : file_fixed) (ls : list fl_line) (ws : fl_line) :
    fl_auth c ls ==∗ fl_auth c (ls ++ [ws]) ∗ fl_lb c (ls ++ [ws]).
  Proof using .
    rewrite /fl_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((ls ++ [ws]) : list (leibnizO fl_line)))
            with "Ha") as "Ha".
    { apply mono_list_update. by exists [ws]. }
    iModIntro. iApply (fl_auth_lb with "Ha").
  Qed.

  (* THE BIRTH: echo's counter and era map, and the line list empty *)
  Definition file_cl (c : file_fixed) : iProp Σ :=
    (echo_cl (ff_echo c) ∗ fl_auth c [])%I.

  (* ...handed the machine's started counter's name, which it stores.  The
     sync registry's and the commit-era counter's names are fresh; their
     ghosts are founded by the birth's split (sync SY3-A3bc item 5), and
     until then nothing is kept at them *)
  Lemma file_birth (γst : gname) :
    ⊢ |==> ∃ c : file_fixed, ⌜ff_st c = γst⌝ ∗ file_cl c
        ∗ ghost_map_auth_frac (ff_reg c) 1 (∅ : gmap nat gname)
        ∗ @mono_nat_auth_own Σ fa_st (ff_cm c) (DfracOwn 1) 0%nat
        ∗ own (ff_hist c) (●ML ([] : list (leibnizO UnionAdm.srec)))
        ∗ ghost_map_auth_frac (ff_run c) 1 (∅ : gmap nat (gname * gname)).
  Proof using .
    iMod echo_birth as (γ) "He".
    iMod (own_alloc (●ML ([] : list (leibnizO fl_line)))) as (g) "Hl";
      [ apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname)) as (greg) "Hreg".
    iMod (@mono_nat_own_alloc Σ fa_st 0) as (gcm) "[Hcm _]".
    iMod (own_alloc (●ML ([] : list (leibnizO UnionAdm.srec)))) as (gh) "Hh";
      [ apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname * gname)) as (grun) "Hrun".
    iModIntro. iExists (MkFileFixed γ g greg gcm γst gh grun).
    rewrite /file_cl /fl_auth /=. iSplitR; [done |]. iFrame "He Hl Hreg Hcm Hh Hrun".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2.  THE DEED AND THE TICKET                                       *)
  (* ---------------------------------------------------------------- *)

  Definition fdeed (r : file_names) (s : dst) : iProp Σ :=
    ghost_var_frac (fn_deed r) (1/2) s.
  Definition fdeed_whole (r : file_names) (s : dst) : iProp Σ :=
    ghost_var_frac (fn_deed r) 1 s.
  Definition ftkt (r : file_names) (s : dst) : iProp Σ :=
    ghost_var_frac (fn_tkt r) (1/2) s.

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
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _]. rewrite dfrac_op_own dfrac_valid_own in Hq.
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

  (* THE ROUND POSITION (sync SY3-A3b/A3bc), at the NON-INSTANCE camera
     [fa_pos] ([fileAppG]'s header): every holder names it through these
     definitions, so no other [ghost_varG nat] in a caller's scope can
     capture it (the duplicate-class trap).  [fposf] is a raw fraction;
     the HOLDER's half [fpos] carries the fact that the instance is a
     RUNNING claim (only a running claim has a position), and splits into
     two QUARTERS [fposq] -- one of which a two-phase move PARKS in the
     claim between its phases ([f_core]'s in-flight arm).  THE SHARES
     (lane SY3-A3bc): the running claim holds a quarter, the holder the
     half [fpos] AND a further quarter, [fposh] -- the half is what a move
     spends and gets back, the extra quarter is the ROUND's witness: it
     stays with the round while the half travels through a call (the
     redirect's open and writes), and on the half's return it names the
     value the half is at.  Only all three together move the position
     ([fposf_update]). *)
  Definition fposf (r : file_names) (q : Qp) (n : nat) : iProp Σ :=
    @ghost_var Σ nat fa_pos (fn_pos r) (DfracOwn q) n.
  Definition fpos (r : file_names) (n : nat) : iProp Σ :=
    (⌜fn_role r = false⌝ ∗ fposf r (1/2) n)%I.
  Definition fposq (r : file_names) (n : nat) : iProp Σ :=
    (⌜fn_role r = false⌝ ∗ fposf r (1/4) n)%I.
  Definition fposh (r : file_names) (n : nat) : iProp Σ :=
    (fpos r n ∗ fposq r n)%I.

  Global Instance fposf_timeless r q n : Timeless (fposf r q n).
  Proof using . rewrite /fposf. apply _. Qed.
  Global Instance fpos_timeless r n : Timeless (fpos r n).
  Proof using . rewrite /fpos. apply _. Qed.
  Global Instance fposq_timeless r n : Timeless (fposq r n).
  Proof using . rewrite /fposq. apply _. Qed.
  Global Instance fposh_timeless r n : Timeless (fposh r n).
  Proof using . rewrite /fposh. apply _. Qed.

  Lemma fposf_agree (r : file_names) (q q' : Qp) (n n' : nat) :
    fposf r q n -∗ fposf r q' n' -∗ ⌜n = n'⌝.
  Proof using .
    rewrite /fposf. iIntros "H1 H2".
    iDestruct (ghost_var_agree (ghost_varG0 := fa_pos) with "H1 H2") as %Heq.
    by iPureIntro.
  Qed.

  Lemma fpos_agree (r : file_names) (n n' : nat) :
    fpos r n -∗ fpos r n' -∗ ⌜n = n'⌝.
  Proof using .
    iIntros "[_ H1] [_ H2]". iApply (fposf_agree with "H1 H2").
  Qed.

  Lemma fposf_split (r : file_names) (q1 q2 : Qp) (n : nat) :
    fposf r (q1 + q2) n ⊣⊢ fposf r q1 n ∗ fposf r q2 n.
  Proof using .
    rewrite /fposf. iSplit.
    - iApply (ghost_var_split (ghost_varG0 := fa_pos)).
    - iIntros "[H1 H2]". iCombine "H1 H2" as "H". iExact "H".
  Qed.

  (* the holder's half is two quarters *)
  Lemma fpos_quarters (r : file_names) (n : nat) :
    fpos r n ⊣⊢ fposq r n ∗ fposq r n.
  Proof using .
    rewrite /fpos /fposq. rewrite -{1}Qp.quarter_quarter fposf_split.
    iSplit; [iIntros "(% & H1 & H2)"; by iFrame | iIntros "([% H1] & [_ H2])"; by iFrame].
  Qed.

  (* two quarters at different values are one value *)
  Lemma fposq_join (r : file_names) (n n' : nat) :
    fposq r n -∗ fposq r n' -∗ fpos r n.
  Proof using .
    iIntros "[%Hr H1] [_ H2]". iDestruct (fposf_agree with "H1 H2") as %<-.
    rewrite /fpos. iSplitR; [done |]. rewrite -Qp.quarter_quarter fposf_split.
    iFrame "H1 H2".
  Qed.

  (* the claim's quarter, the holder's half and its quarter are the whole *)
  Lemma fposf_whole (r : file_names) (n : nat) :
    fposf r (1/4) n ∗ fposf r (1/2) n ∗ fposf r (1/4) n ⊣⊢ fposf r 1 n.
  Proof using .
    iSplit.
    - iIntros "(H1 & H2 & H3)".
      iAssert (fposf r (1/4 + 1/4) n) with "[H1 H3]" as "H13".
      { rewrite fposf_split. iFrame "H1 H3". }
      iEval (rewrite Qp.quarter_quarter) in "H13".
      iAssert (fposf r (1/2 + 1/2) n) with "[H13 H2]" as "H".
      { rewrite fposf_split. iFrame "H13 H2". }
      iEval (rewrite Qp.half_half) in "H". iExact "H".
    - iIntros "H". iEval (rewrite -Qp.half_half fposf_split) in "H".
      iDestruct "H" as "[H13 H2]".
      iEval (rewrite -Qp.quarter_quarter fposf_split) in "H13".
      iDestruct "H13" as "[H1 H3]". iFrame "H1 H2 H3".
  Qed.

  (* all three shares together move to any value *)
  Lemma fposf_update (r : file_names) (n n' : nat) :
    fposf r (1/4) n -∗ fposf r (1/2) n -∗ fposf r (1/4) n ==∗
      fposf r (1/4) n' ∗ fposf r (1/2) n' ∗ fposf r (1/4) n'.
  Proof using .
    iIntros "H1 H2 H3".
    iAssert (fposf r 1 n) with "[H1 H2 H3]" as "H".
    { rewrite -(fposf_whole r n). iFrame "H1 H2 H3". }
    rewrite {1}/fposf.
    iMod (ghost_var_update (ghost_varG0 := fa_pos) n' with "H") as "H".
    iModIntro. rewrite (fposf_whole r n'). iExact "H".
  Qed.

  (* a fresh position: the claim's quarter, the holder's half and quarter *)
  Lemma fpos_alloc (n : nat) :
    ⊢ |==> ∃ γp : gname,
        @ghost_var Σ nat fa_pos γp (DfracOwn (1/4)) n ∗ @ghost_var Σ nat fa_pos γp (DfracOwn (1/2)) n
        ∗ @ghost_var Σ nat fa_pos γp (DfracOwn (1/4)) n.
  Proof using .
    iMod (ghost_var_alloc (ghost_varG0 := fa_pos) n) as (γp) "H".
    set (r := MkFileNames inhabitant inhabitant inhabitant inhabitant
                inhabitant inhabitant inhabitant γp).
    iAssert (fposf r 1 n) with "[H]" as "H"; [rewrite /fposf /=; iExact "H" |].
    iEval (rewrite -fposf_whole) in "H".
    iModIntro. iExists γp. rewrite /fposf /=. iExact "H".
  Qed.

  Lemma fposh_rec_eq (r1 r2 : file_names) (n : nat) :
    fn_role r1 = fn_role r2 -> fn_pos r1 = fn_pos r2 -> fposh r1 n -∗ fposh r2 n.
  Proof using .
    destruct r1, r2; cbn. intros -> ->. rewrite /fposh /fpos /fposq /fposf.
    cbn [fn_role fn_pos]. iIntros "H". iExact "H".
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
  Definition esc_tok (g : gname) : iProp Σ := mono_nat_auth_own_frac g 1 0%nat.
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
    iDestruct (mono_nat_auth_lb_own_valid with "Ht Hlb") as %[_ Hle].
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
     have to change.)  The SYNC PART's data ([fn_sync], [fn_era],
     [fn_role]) is the caller's: it names ghosts the caller owns.  The
     ROUND POSITION is fresh, both halves at [n0] (sync SY3-A3b). *)
  Lemma fnames_alloc (r1 : echo_names) (s : dst) (γs : gname) (k : nat)
      (b : bool) (n0 : nat) :
    ⊢ |==> ∃ r : file_names,
        ⌜fn_cons r = r1⌝ ∗ ⌜fn_sync r = γs /\ fn_era r = k /\ fn_role r = b⌝
        ∗ fdeed r s ∗ fdeed r s ∗ ftkt r s ∗ ftkt r s ∗ esc_auth r []
        ∗ fposf r (1/2) n0 ∗ fposf r (1/2) n0.
  Proof using .
    iMod (ghost_var_alloc s) as (gd) "Hd".
    iMod (ghost_var_alloc s) as (gt) "Ht".
    iMod (own_alloc (●ML ([] : list (leibnizO esc_rec)))) as (ge) "He";
      [ apply mono_list_auth_valid |].
    iMod (ghost_var_alloc (ghost_varG0 := fa_pos) n0) as (gp) "[Hp1 Hp2]".
    iModIntro. iExists (MkFileNames r1 gd gt ge γs k b gp).
    rewrite /fdeed /ftkt /esc_auth /fposf /=.
    iDestruct "Hd" as "[Hd1 Hd2]". iDestruct "Ht" as "[Ht1 Ht2]".
    iFrame "Hd1 Hd2 Ht1 Ht2 He Hp1 Hp2". by iPureIntro.
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
     ∨ ∃ ls : list fl_line,
         fl_lb c ls
         ∗ ⌜map_Forall (fun N p => FileDisc.uname N
                                   /\ f_bytes_typed (fl_redirs ls) N p.2) s⌝)%I.

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
    f_typed c s -∗ ∃ ls : list fl_line, fl_lb c ls ∗ ⌜f_bytes_typed (fl_redirs ls) N bs⌝.
  Proof using .
    intros Hs. rewrite /f_typed. iIntros "[%He | (%ls & Hlb & %Hall)]".
    { subst s. by rewrite lookup_empty in Hs. }
    iExists ls. iFrame "Hlb". iPureIntro. exact (proj2 (Hall N (i, bs) Hs)).
  Qed.

  (* THE ONE WAY a process re-proves the typed fact at a new content: the
     entry it wrote, typed at a lower bound of its own, joins the rest --
     two lower bounds of one list are comparable, and the longer serves
     both *)
  Lemma f_typed_insert (c : file_fixed) (s : dst) (ls : list fl_line)
      (N : fname) (i : Z) (bs : list (bv 8)) :
    FileDisc.uname N -> f_bytes_typed (fl_redirs ls) N bs ->
    f_typed c s -∗ fl_lb c ls -∗ f_typed c (<[N := (i, bs)]> s).
  Proof using .
    intros HN Hbt. iIntros "Hty #Hlb". rewrite /f_typed.
    iDestruct "Hty" as "[%He | (%ls0 & #Hlb0 & %Hall)]".
    { subst s. iRight. iExists ls. iFrame "Hlb". iPureIntro.
      apply map_Forall_insert_2; [by split | apply map_Forall_empty]. }
    iDestruct (fl_lb_lb with "Hlb Hlb0") as %[Hp | Hp].
    - iRight. iExists ls0. iFrame "Hlb0". iPureIntro.
      apply map_Forall_insert_2;
        [split; [exact HN | exact (f_bytes_typed_mono _ _ N bs (fl_redirs_prefix ls ls0 Hp) Hbt)] |].
      exact Hall.
    - iRight. iExists ls. iFrame "Hlb". iPureIntro.
      apply map_Forall_insert_2; [by split |].
      intros M p Hp'. destruct (Hall M p Hp') as [HM Hb].
      split; [exact HM | exact (f_bytes_typed_mono _ _ M p.2 (fl_redirs_prefix ls0 ls Hp) Hb)].
  Qed.

  (* ...at a chunk subset of a line the list holds *)
  Lemma f_typed_some (c : file_fixed) (s : dst) (ls : list fl_line) (N : fname)
      (ws : wordline) (sel : list nat) (i : Z) :
    FileDisc.uname N ->
    (N, ws) ∈ fl_redirs ls -> EchoDisc.line_ok ws -> sel_ok (echo_chunks ws) sel ->
    f_typed c s -∗ fl_lb c ls -∗
    f_typed c (<[N := (i, subseq (echo_chunks ws) sel)]> s).
  Proof using .
    intros HN Hin Hok Hsel. iIntros "Hty #Hlb".
    iApply (f_typed_insert c s ls N i with "Hty Hlb"); [exact HN |]. by exists ws, sel.
  Qed.

End FileClaim.

(* ====================================================================== *)
(*  3b.  THE SYNC PART OF THE CLAIM, ITS TOKEN AND ITS HOOK               *)
(*  (sync design section 4.5; lanes SY3-A3a/A3b, moved here from the     *)
(*  union's wrapper by ruling (i) after A3b: the sync ghost state belongs *)
(*  to the file application, stated over [file_fixed]).                  *)
(*                                                                        *)
(*  THE SHARES.  Each era's SYNC LIST (a [mono_list] of sync records      *)
(*  [UnionAdm.srec]) is split three ways: [●{½}] in the durable copy,     *)
(*  [●{¼}] in the running claim, [●{¼}] in the era's TOKEN [union_tk]     *)
(*  (which the log invariant holds).  The REGISTRY [ff_reg] names each    *)
(*  era's list; the COMMIT-ERA counter [ff_cm] has its full authority in  *)
(*  the durable copy; the copy also carries a lower bound of the          *)
(*  MACHINE's started counter [ff_st] at its era (“that many PowerOns     *)
(*  have happened”), which the loan of the machine's [start_auth] bounds. *)
(*  Both counters are at the camera [fa_st], the round position at        *)
(*  [fa_pos] ([fileAppG]'s header).                                      *)
(*                                                                        *)
(*  THE ERA is the instance's PURE field [fn_era] (ledger numbering: the  *)
(*  birth is era 0, the boot at [gen_id] era [S gen_id]); the running      *)
(*  claim's is read from the record predicate [file_ok].                  *)
(*                                                                        *)
(*  THE CHAIN.  [sync_chain ls Ls]: the records of [srec0 :: Ls] rise      *)
(*  ([srec_le] at the line list [ls]), AND the last record's sync line is  *)
(*  in [ls] ([ls !! (p-1) = LSync] at its position [p], or [p = 0]): what *)
(*  bounds the last record's position by the claim's own lower bound and  *)
(*  tells a redirect line from the record's sync line.                    *)
(*                                                                        *)
(*  THE ROUND POSITION (design 4.5 "The round position").  The HOOK and a *)
(*  REDIRECT round need the last record's position to be at most the      *)
(*  caller's own line position.  Two lower bounds of the line list are    *)
(*  merely comparable, so that is sh's serial order, carried by a         *)
(*  resource: the instance's round position [fn_pos] ([fpos]), one half   *)
(*  in the running claim's sync part above every record's position, the   *)
(*  other with the deed's holder at its round's line count.  The copy     *)
(*  carries no position; the re-base founds a fresh one.                  *)
(* ====================================================================== *)
Import UnionAdm.
Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  PURE: THE LAST RECORD, THE CHAIN                                  *)
(* ===================================================================== *)

(* the files a view holds, as the model reads them *)
Definition fcont_of (av : aview) : fstate := dst_content (fcontent_of av).

Lemma fcont_of_empty : fcont_of ∅ = ∅.
Proof using. rewrite /fcont_of /fcontent_of /aents lookup_empty /=. exact dst_content_empty. Qed.

(* the last record of a list, [srec0] before the first *)
Definition slast (Ls : list srec) : srec := default srec0 (last Ls).

Lemma slast_nil : slast [] = srec0.
Proof using. reflexivity. Qed.

Lemma slast_snoc (Ls : list srec) (r : srec) : slast (Ls ++ [r]) = r.
Proof using. rewrite /slast last_snoc //. Qed.

(* ...at its index in the list with [srec0] in front *)
Lemma slast_lookup (Ls : list srec) : (srec0 :: Ls) !! length Ls = Some (slast Ls).
Proof using.
  induction Ls as [| r Ls _] using rev_ind; [reflexivity |].
  rewrite slast_snoc length_app /= Nat.add_1_r /=.
  rewrite lookup_app_r; [| lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

(* THE CHAIN: the records rise from [srec0] on, and the last record's sync
   line (at its position minus one) is in the line list *)
Definition sync_chain (ls : list fl_line) (Ls : list srec) : Prop :=
  (forall (j : nat) (r r' : srec),
     (srec0 :: Ls) !! j = Some r -> (srec0 :: Ls) !! S j = Some r' -> srec_le ls r r')
  /\ ((slast Ls).1 = 0 \/ ls !! pred (slast Ls).1 = Some FileDisc.LSync).

Lemma sync_chain_nil (ls : list fl_line) : sync_chain ls [].
Proof using.
  split; [| left; reflexivity].
  intros j r r' _ H. simpl in H. destruct j; discriminate H.
Qed.

Lemma sync_chain_mono (ls ls' : list fl_line) (Ls : list srec) :
  ls `prefix_of` ls' -> sync_chain ls Ls -> sync_chain ls' Ls.
Proof using.
  intros Hp [Hc Hs]. split.
  - intros j r r' H1 H2. exact (srec_le_mono ls ls' r r' Hp (Hc j r r' H1 H2)).
  - destruct Hs as [Hs | Hs]; [by left | right].
    exact (prefix_lookup_Some _ _ _ _ Hs Hp).
Qed.

(* the last record's position is within the list *)
Lemma sync_chain_pos (ls : list fl_line) (Ls : list srec) :
  sync_chain ls Ls -> (slast Ls).1 <= length ls.
Proof using.
  intros [_ [H | H]]; [lia |]. apply lookup_lt_Some in H.
  unfold fl_line in *. revert H. destruct (slast Ls).1; simpl; intros H; lia.
Qed.

(* THE RECORDS RISE: every record's position is at most the last's *)
Lemma sync_chain_le_last (ls : list fl_line) (Ls : list srec) :
  sync_chain ls Ls -> forall rec : srec, rec ∈ Ls -> rec.1 <= (slast Ls).1.
Proof using.
  intros [Hc _]. clear -Hc. revert Hc.
  induction Ls as [| x L IH] using rev_ind; intros Hc rec Hin.
  - by apply elem_of_nil in Hin.
  - rewrite slast_snoc.
    assert (HcL : forall (j : nat) (r r' : srec),
               (srec0 :: L) !! j = Some r -> (srec0 :: L) !! S j = Some r' ->
               srec_le ls r r').
    { intros j r r' H1 H2. apply (Hc j).
      - change (srec0 :: L ++ [x]) with ((srec0 :: L) ++ [x]).
        by apply lookup_app_l_Some.
      - change (srec0 :: L ++ [x]) with ((srec0 :: L) ++ [x]).
        by apply lookup_app_l_Some. }
    assert (Hlast : (slast L).1 <= x.1).
    { assert (H1 : (srec0 :: L ++ [x]) !! length L = Some (slast L)).
      { change (srec0 :: L ++ [x]) with ((srec0 :: L) ++ [x]).
        apply lookup_app_l_Some. apply slast_lookup. }
      assert (H2 : (srec0 :: L ++ [x]) !! S (length L) = Some x).
      { simpl. rewrite lookup_app_r; [| lia].
        rewrite Nat.sub_diag. reflexivity. }
      pose proof (Hc _ _ _ H1 H2) as Hs. destruct Hs as [Hs _]. exact Hs. }
    apply elem_of_app in Hin as [Hin | Hin].
    + pose proof (IH HcL rec Hin). lia.
    + apply list_elem_of_singleton in Hin as ->. lia.
Qed.

(* a bound on every record bounds the last *)
Lemma slast_bound (Ls : list srec) (n : nat) :
  (forall rec : srec, rec ∈ Ls -> rec.1 <= n) -> (slast Ls).1 <= n.
Proof using.
  intros H. rewrite /slast. destruct (last Ls) as [x |] eqn:E; cbn; [| lia].
  apply H. by apply last_Some_elem_of.
Qed.

(* APPEND: a record above the last, whose sync line is in the list *)
Lemma sync_chain_snoc (ls : list fl_line) (Ls : list srec) (r : srec) :
  sync_chain ls Ls -> srec_le ls (slast Ls) r ->
  ls !! pred r.1 = Some FileDisc.LSync -> sync_chain ls (Ls ++ [r]).
Proof using.
  intros [Hc _] Hle Hr. split; [| right; rewrite slast_snoc; exact Hr].
  intros j x x' H1 H2.
  change (srec0 :: Ls ++ [r]) with ((srec0 :: Ls) ++ [r]) in H1, H2.
  destruct (decide (S j < length (srec0 :: Ls))) as [Hlt | Hge].
  - rewrite lookup_app_l in H1; [| simpl in *; lia].
    rewrite lookup_app_l in H2; [| exact Hlt].
    exact (Hc j x x' H1 H2).
  - assert (j = length Ls) as ->.
    { apply lookup_lt_Some in H2. rewrite length_app /= in H2. simpl in Hge. lia. }
    rewrite lookup_app_l in H1; [| simpl; lia].
    rewrite slast_lookup in H1. injection H1 as <-.
    rewrite lookup_app_r in H2; [| simpl; lia].
    rewrite (_ : S (length Ls) - length (srec0 :: Ls) = 0) in H2; [| simpl; lia].
    injection H2 as <-. exact Hle.
Qed.

(* THE BOOT FACT: along the chain, a state admissible after the last
   record is admissible after the last record of any prefix *)
Lemma sync_chain_shrink (ls : list fl_line) (Ls F : list srec) (s : fstate) :
  sync_chain ls Ls -> F `prefix_of` Ls ->
  uadm ls (slast Ls) s -> uadm ls (slast F) s.
Proof using.
  intros [Hc _] [G ->] H.
  set (rec := fun j => default srec0 ((srec0 :: F ++ G) !! j)).
  assert (HF : rec (length F) = slast F).
  { rewrite /rec. change (srec0 :: F ++ G) with ((srec0 :: F) ++ G).
    rewrite lookup_app_l; [| simpl; lia]. rewrite slast_lookup. reflexivity. }
  assert (HL : rec (length (F ++ G)) = slast (F ++ G)).
  { rewrite /rec slast_lookup. reflexivity. }
  rewrite -HF. apply (uadm_shrink_chain ls rec (length F) (length (F ++ G)) s).
  - intros j Hj1 Hj2. rewrite /rec.
    destruct ((srec0 :: F ++ G) !! j) as [x |] eqn:E1;
      [| apply lookup_ge_None in E1; simpl in E1; lia].
    destruct ((srec0 :: F ++ G) !! S j) as [x' |] eqn:E2;
      [| apply lookup_ge_None in E2; simpl in E2; lia].
    exact (Hc j x x' E1 E2).
  - rewrite length_app. lia.
  - rewrite HL. exact H.
Qed.

(* A REDIRECT LINE IS NOT THE RECORD'S SYNC LINE: a writer's line at [j],
   with the last record at most one past it, is at or after the record *)
Lemma sync_chain_redir_pos (ls ls_w : list fl_line) (Ls : list srec) (j : nat)
    (ws : list (list (bv 8))) (N : list (bv 8)) :
  sync_chain ls Ls -> (ls `prefix_of` ls_w \/ ls_w `prefix_of` ls) ->
  ls_w !! j = Some (FileDisc.LEchoF ws N) -> (slast Ls).1 <= S j ->
  (slast Ls).1 <= j.
Proof using.
  intros [_ Hs] Hcmp Hj Hp. destruct Hs as [H0 | Hs]; [lia |].
  destruct (decide ((slast Ls).1 = S j)) as [E | ]; [| lia]. exfalso.
  rewrite E /= in Hs.
  destruct Hcmp as [Hp' | Hp'].
  - pose proof (prefix_lookup_Some _ _ _ _ Hs Hp') as H. rewrite Hj in H. discriminate H.
  - pose proof (prefix_lookup_Some _ _ _ _ Hj Hp') as H. rewrite Hs in H. discriminate H.
Qed.

(* ===================================================================== *)
(*  2.  THE INSTANCE'S RECORD MOVES                                       *)
(* ===================================================================== *)

(* the instance at a new sync list, era, role and round position (the
   deed, ticket and escrow names kept) *)
Definition fn_with_pos (r : file_names) (γ : gname) (k : nat) (b : bool)
    (γp : gname) : file_names :=
  MkFileNames (fn_cons r) (fn_deed r) (fn_tkt r) (fn_esc r) γ k b γp.

(* ...keeping the position's name too *)
Definition fn_with (r : file_names) (γ : gname) (k : nat) (b : bool) : file_names :=
  fn_with_pos r γ k b (fn_pos r).

(* the era's RUNNING claim founded by the PowerOn transport: the copy's
   console, ticket and escrow names, a fresh deed [d] and position [γp], the
   era's list (sync SY3-A4) *)
Definition fn_run (r : file_names) (d : gname) (γ : gname) (k : nat) (γp : gname) : file_names :=
  MkFileNames (fn_cons r) d (fn_tkt r) (fn_esc r) γ k false γp.

(* the running claim's instance as the new durable copy's *)
Definition to_copy (r : file_names) : file_names := fn_with r (fn_sync r) (fn_era r) true.

(* THE ERA'S RECORD PREDICATE ([App.app_ok] for the union) *)
Definition file_ok (c : file_fixed) (k : nat) (r : file_names) : Prop := fn_era r = k.

(* ===================================================================== *)
(*  3.  THE SHARES, THE REGISTRY, THE COUNTERS, THE CLAIM, THE TOKEN      *)
(* ===================================================================== *)
Section sync.
  (* the counters at [fa_st] and the position at [fa_pos], EXPLICITLY
     ([fileAppG]'s header): no [mono_natG] or [ghost_varG nat] instance is
     in this section's scope, so a stray resolution fails loudly *)
  Context {Σ : gFunctors} `{!fileAppG Σ}.

  (* ---- the sync list's shares ---- *)
  Definition sl_auth (γ : gname) (q : Qp) (Ls : list srec) : iProp Σ :=
    own γ (●ML{#q} (Ls : list (leibnizO srec))).
  Definition sl_lb (γ : gname) (Ls : list srec) : iProp Σ :=
    own γ (◯ML (Ls : list (leibnizO srec))).

  Global Instance sl_auth_timeless γ q Ls : Timeless (sl_auth γ q Ls).
  Proof using . rewrite /sl_auth. apply _. Qed.
  Global Instance sl_lb_timeless γ Ls : Timeless (sl_lb γ Ls).
  Proof using . rewrite /sl_lb. apply _. Qed.
  Global Instance sl_lb_persistent γ Ls : Persistent (sl_lb γ Ls).
  Proof using . rewrite /sl_lb. apply _. Qed.

  Lemma sl_auth_agree γ q q' Ls Ls' :
    sl_auth γ q Ls -∗ sl_auth γ q' Ls' -∗ ⌜Ls = Ls'⌝.
  Proof using .
    rewrite /sl_auth. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[_ ?]%mono_list_auth_dfrac_op_valid_L.
    done.
  Qed.

  Lemma sl_auth_lb_prefix γ q Ls Ls' :
    sl_auth γ q Ls -∗ sl_lb γ Ls' -∗ ⌜Ls' `prefix_of` Ls⌝.
  Proof using .
    rewrite /sl_auth /sl_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[_ ?]%mono_list_both_dfrac_valid_L.
    done.
  Qed.

  (* the full authority excludes any other share *)
  Lemma sl_auth_1_excl γ q Ls Ls' : sl_auth γ 1 Ls -∗ sl_auth γ q Ls' -∗ False.
  Proof using .
    rewrite /sl_auth. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hv _]%mono_list_auth_dfrac_op_valid_L.
    apply dfrac_valid_own_l in Hv. by apply (irreflexivity (<)%Qp) in Hv.
  Qed.

  Lemma sl_lb_get γ q Ls : sl_auth γ q Ls -∗ sl_lb γ Ls.
  Proof using .
    rewrite /sl_auth /sl_lb. iApply own_mono. apply mono_list_included.
  Qed.

  Lemma sl_auth_update γ Ls Ls' :
    Ls `prefix_of` Ls' -> sl_auth γ 1 Ls ==∗ sl_auth γ 1 Ls'.
  Proof using .
    intros Hp. rewrite /sl_auth. iApply own_update. by apply mono_list_update.
  Qed.

  Lemma sl_auth_split γ q1 q2 Ls :
    sl_auth γ (q1 + q2) Ls ⊣⊢ sl_auth γ q1 Ls ∗ sl_auth γ q2 Ls.
  Proof using .
    rewrite /sl_auth -dfrac_op_own mono_list_auth_dfrac_op own_op //.
  Qed.

  (* the era's three shares: ½ + ¼ + ¼ *)
  Lemma sl_auth_split3 γ Ls :
    sl_auth γ 1 Ls ⊣⊢
      sl_auth γ (1/2) Ls ∗ sl_auth γ (1/4) Ls ∗ sl_auth γ (1/4) Ls.
  Proof using .
    by rewrite -!sl_auth_split Qp.quarter_quarter Qp.half_half.
  Qed.

  Lemma sl_auth_join3 γ Ls :
    sl_auth γ (1/2) Ls -∗ sl_auth γ (1/4) Ls -∗ sl_auth γ (1/4) Ls -∗ sl_auth γ 1 Ls.
  Proof using . rewrite sl_auth_split3. iIntros "H1 H2 H3". iFrame "H1 H2 H3". Qed.

  Lemma sl_auth_split3_1 γ Ls :
    sl_auth γ 1 Ls -∗ sl_auth γ (1/2) Ls ∗ sl_auth γ (1/4) Ls ∗ sl_auth γ (1/4) Ls.
  Proof using . rewrite sl_auth_split3. iIntros "H". iExact "H". Qed.

  (* ---- the registry: era -> that era's sync list ---- *)
  Definition sync_reg (c : file_fixed) (k : nat) (γ : gname) : iProp Σ :=
    k ↪[ff_reg c]□ γ.

  Global Instance sync_reg_persistent c k γ : Persistent (sync_reg c k γ).
  Proof using . rewrite /sync_reg. apply _. Qed.
  Global Instance sync_reg_timeless c k γ : Timeless (sync_reg c k γ).
  Proof using . rewrite /sync_reg. apply _. Qed.

  Lemma sync_reg_agree c k γ γ' : sync_reg c k γ -∗ sync_reg c k γ' -∗ ⌜γ = γ'⌝.
  Proof using .
    rewrite /sync_reg. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  (* ---- the run registry: era -> the running claim's position and deed
          gnames (sync SY3-A4) ---- *)
  Definition run_reg (c : file_fixed) (k : nat) (p d : gname) : iProp Σ :=
    k ↪[ff_run c]□ (p, d).

  Global Instance run_reg_persistent c k p d : Persistent (run_reg c k p d).
  Proof using . rewrite /run_reg. apply _. Qed.
  Global Instance run_reg_timeless c k p d : Timeless (run_reg c k p d).
  Proof using . rewrite /run_reg. apply _. Qed.

  Lemma run_reg_agree c k p d p' d' :
    run_reg c k p d -∗ run_reg c k p' d' -∗ ⌜p = p' /\ d = d'⌝.
  Proof using .
    rewrite /run_reg. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    by injection Heq as -> ->.
  Qed.

  (* the registry's authority, as the durable copy holds it: eras at most
     the copy's *)
  Definition run_auth (c : file_fixed) (k : nat) : iProp Σ :=
    (∃ M : gmap nat (gname * gname), ghost_map_auth_frac (ff_run c) 1 M
       ∗ ⌜forall j, j ∈ dom M -> j <= k⌝)%I.

  Global Instance run_auth_timeless c k : Timeless (run_auth c k).
  Proof using . rewrite /run_auth. apply _. Qed.

  Lemma run_auth_mono c k k' : k <= k' -> run_auth c k -∗ run_auth c k'.
  Proof using .
    intros Hk. iIntros "(%M & HM & %HM)". iExists M. iFrame "HM".
    iPureIntro. intros j Hj. pose proof (HM j Hj). lia.
  Qed.

  (* the transport's registration of the new era's running claim *)
  Lemma run_auth_register c k k' p d :
    k < k' -> run_auth c k ==∗ run_auth c k' ∗ run_reg c k' p d.
  Proof using .
    intros Hk. iIntros "(%M & HM & %HM)".
    iMod (ghost_map_insert_persist k' (p, d) with "HM") as "[HM #Hel]".
    { apply not_elem_of_dom. intros Hin. pose proof (HM k' Hin). lia. }
    iModIntro. iFrame "Hel". iExists _. iFrame "HM". iPureIntro.
    intros j Hj. rewrite dom_insert_L elem_of_union elem_of_singleton in Hj.
    destruct Hj as [-> | Hj]; [lia |]. pose proof (HM j Hj). lia.
  Qed.

  Lemma run_auth_0 c : ghost_map_auth_frac (ff_run c) 1 (∅ : gmap nat (gname * gname)) -∗ run_auth c 0.
  Proof using .
    iIntros "H". iExists ∅. iFrame "H". iPureIntro. intros j Hj. set_solver.
  Qed.

  (* ---- the counters, at the machine's instance ---- *)
  Definition sync_cm_auth (c : file_fixed) (k : nat) : iProp Σ :=
    @mono_nat_auth_own Σ fa_st (ff_cm c) (DfracOwn 1) k.
  Definition sync_cm_lb (c : file_fixed) (k : nat) : iProp Σ :=
    @mono_nat_lb_own Σ fa_st (ff_cm c) k.
  Definition sync_st_lb (c : file_fixed) (k : nat) : iProp Σ :=
    @mono_nat_lb_own Σ fa_st (ff_st c) k.
  (* the LOAN's shape: the machine's [start_auth n], at the union's copy of
     its gname ([App.app_born] identifies the two; sync SY3-A3b) *)
  Definition sync_st_auth (c : file_fixed) (n : nat) : iProp Σ :=
    @mono_nat_auth_own Σ fa_st (ff_st c) (DfracOwn 1) n.

  Global Instance sync_cm_lb_persistent c k : Persistent (sync_cm_lb c k).
  Proof using . rewrite /sync_cm_lb. apply _. Qed.
  Global Instance sync_st_lb_persistent c k : Persistent (sync_st_lb c k).
  Proof using . rewrite /sync_st_lb. apply _. Qed.

  (* ---- THE SYNC PART OF THE CLAIM ---- *)

  (* the role's shares: the durable copy's half, the counter's authority
     and the started certificate; or the running claim's quarter, the
     counter's lower bound and THE ROUND POSITION's quarter, above every
     record's position (lane SY3-A3b) *)
  Definition sync_role (c : file_fixed) (r : file_names) (Ls : list srec) : iProp Σ :=
    if fn_role r
    then (sl_auth (fn_sync r) (1/2) Ls ∗ sync_cm_auth c (fn_era r)
          ∗ sync_st_lb c (fn_era r)
          (* ...and THE RUN-LONG HISTORY's authority, at the same content
             (sync SY3-A4) *)
          ∗ sl_auth (ff_hist c) 1 Ls
          (* ...and THE RUN REGISTRY's (sync SY3-A4) *)
          ∗ run_auth c (fn_era r))%I
    else (sl_auth (fn_sync r) (1/4) Ls ∗ sync_cm_lb c (fn_era r)
          ∗ (∃ n : nat, fposf r (1/4) n ∗ ⌜forall rec : srec, rec ∈ Ls -> rec.1 <= n⌝)
          (* ...registered at its era (sync SY3-A4) *)
          ∗ run_reg c (fn_era r) (fn_pos r) (fn_deed r))%I.

  Definition sync_body (c : file_fixed) (r : file_names) (av : aview)
      (ls : list fl_line) (Ls : list srec) : iProp Σ :=
    (sync_reg c (fn_era r) (fn_sync r)
     ∗ fl_lb c ls
     ∗ ⌜sync_chain ls Ls⌝
     ∗ ⌜uadm ls (slast Ls) (fcont_of av)⌝
     ∗ sync_role c r Ls)%I.

  Definition sync_claim (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    (∃ (ls : list fl_line) (Ls : list srec), sync_body c r av ls Ls)%I.

  Global Instance sync_role_timeless c r Ls : Timeless (sync_role c r Ls).
  Proof using . rewrite /sync_role. destruct (fn_role r); apply _. Qed.
  Global Instance sync_body_timeless c r av ls Ls : Timeless (sync_body c r av ls Ls).
  Proof using . rewrite /sync_body. apply _. Qed.
  Global Instance sync_claim_timeless c r av : Timeless (sync_claim c r av).
  Proof using . rewrite /sync_claim. apply _. Qed.

  Lemma sync_body_intro c r av ls Ls :
    sync_chain ls Ls -> uadm ls (slast Ls) (fcont_of av) ->
    sync_reg c (fn_era r) (fn_sync r) -∗ fl_lb c ls -∗
    sync_role c r Ls -∗ sync_body c r av ls Ls.
  Proof using .
    intros Hc Hw. iIntros "H1 H2 H3". rewrite /sync_body.
    iFrame (Hc Hw) "H1 H2 H3".
  Qed.

  (* ---- THE ERA'S TOKEN ([App.app_tk]), indexed by [gen_id] ---- *)
  Definition union_tkb (c : file_fixed) (k : nat) : iProp Σ :=
    (∃ (γ : gname) (Ls : list srec),
       sync_reg c (S k) γ ∗ sl_auth γ (1/4) Ls ∗ sync_cm_lb c (S k))%I.

  Global Instance union_tkb_timeless c k : Timeless (union_tkb c k).
  Proof using . rewrite /union_tkb. apply _. Qed.

  (* two lower bounds of the line list, and one covering both *)
  Lemma fl_lb_join (g : file_fixed) (ls ls' : list fl_line) :
    fl_lb g ls -∗ fl_lb g ls' -∗
    ∃ L : list fl_line, fl_lb g L ∗ ⌜ls `prefix_of` L /\ ls' `prefix_of` L⌝.
  Proof using .
    iIntros "#H1 #H2". iDestruct (fl_lb_lb with "H1 H2") as %[Hp | Hp].
    - iExists ls'. iFrame "H2". iPureIntro. split; [exact Hp | reflexivity].
    - iExists ls. iFrame "H1". iPureIntro. split; [reflexivity | exact Hp].
  Qed.

  (* =================================================================== *)
  (*  4.  THE CLOSURE LEMMAS                                             *)
  (* =================================================================== *)

  (* THE MERGE (design 4.5 "The merge"; [App.al_merge]'s wand): the old
     durable copy at ANY era, the running claim at the era [S gen]
     ([file_ok]), the token, the loan of the started auth at [gen + 1].
     The running lower bound of the counter against the copy's authority
     gives [S gen <= era_o]; the copy's started certificate against the
     loan gives [era_o <= S gen]; the registry pins the lists' names; the
     three shares agree; the half and the counter move into the new copy,
     whose witness is the running claim's.  The old copy's leftovers are
     dropped. *)
  Lemma union_merge_closes (c : file_fixed) (r_o r : file_names) (av_o av : aview)
      (gen : nat) :
    fn_role r_o = true -> fn_role r = false -> fn_era r = S gen ->
    sync_claim c r_o av_o -∗ sync_claim c r av -∗ union_tkb c gen -∗
    sync_st_auth c (gen + 1) ==∗
      sync_claim c (to_copy r) av ∗ sync_claim c r av ∗ union_tkb c gen
      ∗ sync_st_auth c (gen + 1).
  Proof using .
    destruct r_o as [oc od ot oe oγ ok ob op]; destruct r as [rc rd rt re rγ rk rb rp].
    cbn [fn_role fn_era fn_sync to_copy fn_with fn_with_pos fn_pos]. intros -> -> ->.
    iIntros "(%ls_o & %Ls_o & #Hrego & _ & _ & _ & Hro)".
    iIntros "(%ls & %Ls & #Hreg & #Hlb & %Hch & %Hw & Hr)".
    iIntros "(%γ & %Lt & #Hregt & Hqt & #Hcmt) Hst".
    unfold sync_role; cbn [fn_role fn_era fn_sync].
    iDestruct "Hro" as "(Ho & Hcmo & #Hsto & Hho & Hra)".
    iDestruct "Hr" as "(Hq & #Hcml & Hpos & #Hrr)".
    iDestruct (mono_nat_auth_lb_own_valid (mono_natG0 := fa_st) with "Hcmo Hcml") as %[_ Hle1].
    iDestruct (mono_nat_auth_lb_own_valid (mono_natG0 := fa_st) with "Hst Hsto") as %[_ Hle2].
    assert (ok = S gen) as -> by lia.
    iDestruct (sync_reg_agree with "Hrego Hreg") as %->.
    iDestruct (sync_reg_agree with "Hreg Hregt") as %->.
    iDestruct (sl_auth_agree with "Ho Hq") as %->.
    iDestruct (sl_auth_agree with "Hq Hqt") as %<-.
    iModIntro.
    iSplitL "Ho Hcmo Hho Hra".
    { iExists ls, Ls. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch Hw) "Hreg Hlb Ho Hcmo Hsto Hho Hra". }
    iSplitL "Hq Hpos".
    { iExists ls, Ls. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync fn_pos fn_deed].
      iFrame (Hch Hw) "Hreg Hlb Hq Hcml Hpos Hrr". }
    iFrame "Hst". iExists γ, Ls. iFrame "Hregt Hqt Hcmt".
  Qed.

  (* THE HOOK (design 4.5 "The hook"; [union_hk]'s body): the guest (the
     new durable copy the merge made) and the running claim at the era
     [S gen], the token, and sh's lend: a lower bound [ls'] of the line
     list ending in the sync line, and the deed's state [s] (its tie to
     the view is A4's; here a premise).  ½ + ¼ + ¼ is the whole list:
     append [(length ls', s)], both witnesses at the new record
     ([uadm_self]), the chain rising because the running state was
     admissible after the last record.  Out: the three, a lower bound of
     the new list and the counter's lower bound -- the design's [Q].
     THE POSITION PREMISE [(slast Ls).1 <= length ls'] (the header): the
     last record is not younger than sh's sync line.  It is stated over
     the running claim's BODY, whose list [Ls] it names.  THE POSITION
     (lane SY3-A3b): the deed holder's half of the round position at sh's
     line count [length ls']; against the running claim's half it bounds
     every record, hence the last. *)
  Lemma union_hook_closes (c : file_fixed) (r' r : file_names) (av : aview)
      (gen : nat) (ls : list fl_line) (Ls : list srec) (ls' : list fl_line)
      (s : fstate) (n : nat) :
    fn_role r' = true -> fn_era r' = S gen ->
    fn_role r = false -> fn_era r = S gen ->
    last ls' = Some FileDisc.LSync -> fcont_of av = s ->
    n = length ls' ->
    sync_claim c r' av -∗ sync_body c r av ls Ls -∗ union_tkb c gen -∗
    fl_lb c ls' -∗ fpos r n ==∗
      sync_claim c r' av ∗ sync_claim c r av ∗ union_tkb c gen
      ∗ sl_lb (ff_hist c) (Ls ++ [(length ls', s)])
      ∗ fpos r n.
  Proof using .
    destruct r' as [gc gd gt ge gγ gk gb gp]; destruct r as [rc rd rt re rγ rk rb rp].
    cbn [fn_role fn_era fn_sync]. intros -> -> -> -> Hlast <- ->.
    iIntros "(%ls_g & %Ls_g & #Hregg & _ & _ & _ & Hg)".
    iIntros "(#Hreg & #Hlb & %Hch & %Hw & Hr) (%γ & %Lt & #Hregt & Hqt & #Hcmt) #Hlb' Hph".
    unfold sync_role; cbn [fn_role fn_era fn_sync].
    iDestruct "Hg" as "(Hg & Hcmg & #Hstg & Hhg & Hrag)".
    iDestruct "Hr" as "(Hq & #Hcml & (%m & Hpm & %Hbm) & #Hrr)".
    iDestruct "Hph" as "[%Hrole Hph]".
    iDestruct (fposf_agree with "Hpm Hph") as %->.
    pose proof (slast_bound Ls _ Hbm) as Hpos.
    iDestruct (sync_reg_agree with "Hregg Hreg") as %->.
    iDestruct (sync_reg_agree with "Hreg Hregt") as %->.
    iDestruct (sl_auth_agree with "Hg Hq") as %->.
    iDestruct (sl_auth_agree with "Hq Hqt") as %<-.
    (* the whole list, and the append *)
    iDestruct (sl_auth_join3 with "Hg Hq Hqt") as "Ha".
    iMod (sl_auth_update _ Ls (Ls ++ [(length ls', fcont_of av)]) with "Ha") as "Ha";
      [by apply prefix_app_r |].
    iDestruct (sl_auth_split3_1 with "Ha") as "(Hg & Hq & Hqt)".
    (* ...and the run-long history, at the same content *)
    iMod (sl_auth_update _ Ls (Ls ++ [(length ls', fcont_of av)]) with "Hhg") as "Hhg";
      [by apply prefix_app_r |].
    iDestruct (sl_lb_get with "Hhg") as "#Hnew".
    (* the line list covering both *)
    iDestruct (fl_lb_join with "Hlb Hlb'") as (L) "[#HL %HL]".
    destruct HL as [HlsL Hls'L].
    assert (Hsync : L !! pred (length ls') = Some FileDisc.LSync).
    { rewrite last_lookup in Hlast. exact (prefix_lookup_Some _ _ _ _ Hlast Hls'L). }
    assert (Hch' : sync_chain L (Ls ++ [(length ls', fcont_of av)])).
    { apply sync_chain_snoc; [exact (sync_chain_mono ls L Ls HlsL Hch) | | exact Hsync].
      split; [exact Hpos |].
      exact (uadm_mono ls L (slast Ls) _ HlsL Hw). }
    assert (Hw' : uadm L (slast (Ls ++ [(length ls', fcont_of av)])) (fcont_of av)).
    { rewrite slast_snoc. exact (uadm_self L (length ls', fcont_of av)). }
    assert (Hbm' : forall rec : srec, rec ∈ Ls ++ [(length ls', fcont_of av)] ->
                     rec.1 <= length ls').
    { intros rec Hin. apply elem_of_app in Hin as [Hin | Hin]; [exact (Hbm rec Hin) |].
      apply list_elem_of_singleton in Hin as ->. cbn. lia. }
    iModIntro.
    iSplitL "Hg Hcmg Hhg Hrag".
    { iExists L, (Ls ++ [(length ls', fcont_of av)]).
      unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch' Hw') "Hregg HL Hg Hcmg Hstg Hhg Hrag". }
    iSplitL "Hq Hpm".
    { iExists L, (Ls ++ [(length ls', fcont_of av)]).
      unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync fn_pos fn_deed].
      iFrame (Hch' Hw') "Hreg HL Hq Hcml Hrr". iExists (length ls').
      iFrame "Hpm". iPureIntro. exact Hbm'. }
    iFrame "Hnew". iSplitR "Hph".
    { iExists γ, (Ls ++ [(length ls', fcont_of av)]). iFrame "Hregt Hqt Hcmt". }
    rewrite /fpos. iFrame "Hph". done.
  Qed.

  (* A REDIRECT ROUND'S STEP (design 4.3 item 1, [uadm_redir]): the
     writer's line [LEchoF ws N] is the last of its lower bound [ls_w], and
     the round sets [N] to a chunk subset of it.  The witness moves to the
     new view at the SAME records; the line list grows to cover the
     writer's.  THE POSITION (lane SY3-A3b; the header): the deed
     holder's half of the round position at the writer's line count
     [length ls_w], against the running claim's half, puts the last record
     no later than the writer's line; then the line is at or after the
     record ([sync_chain_redir_pos]: the redirect is not the record's sync
     line).  The running claim only (a durable copy never steps); the
     shares are untouched and the holder's half comes back. *)
  Lemma sync_claim_redir_step (c : file_fixed) (r : file_names) (av av' : aview)
      (ls : list fl_line) (Ls : list srec) (ls_w : list fl_line) (j : nat)
      (ws : list (list (bv 8))) (N : list (bv 8)) (sel : list nat) (n : nat) :
    fn_role r = false ->
    ls_w !! j = Some (FileDisc.LEchoF ws N) -> length ls_w = S j ->
    sel_ok (echo_chunks ws) sel ->
    n = length ls_w ->
    fcont_of av' = <[N := subseq (echo_chunks ws) sel]> (fcont_of av) ->
    sync_body c r av ls Ls -∗ fl_lb c ls_w -∗ fposq r n -∗
    (∃ L : list fl_line, sync_body c r av' L Ls) ∗ fposq r n.
  Proof using .
    intros Hrole Hj Hlen Hsel -> Hav'.
    iIntros "(#Hreg & #Hlb & %Hch & %Hw & Hr) #Hlbw Hph".
    iAssert (sync_role c r Ls ∗ ⌜(slast Ls).1 <= length ls_w⌝ ∗ fposq r (length ls_w))%I
      with "[Hr Hph]" as "(Hr & %Hpos & Hph)".
    { rewrite /sync_role Hrole. cbn [fn_role].
      iDestruct "Hr" as "(Hq & #Hcml & (%m & Hpm & %Hbm) & #Hrr)".
      iDestruct "Hph" as "[%Hrl Hph]".
      iDestruct (fposf_agree with "Hpm Hph") as %->.
      iSplitL "Hq Hpm".
      { iFrame "Hq Hcml Hrr". iExists (length ls_w). iFrame "Hpm". iPureIntro. exact Hbm. }
      iSplitR; [iPureIntro; exact (slast_bound Ls _ Hbm) | by iFrame "Hph"]. }
    iDestruct (fl_lb_lb with "Hlb Hlbw") as %Hcmp.
    iDestruct (fl_lb_join with "Hlb Hlbw") as (L) "[#HL %HL]".
    destruct HL as [HlsL HlswL].
    assert (Hpj : (slast Ls).1 <= j).
    { apply (sync_chain_redir_pos ls ls_w Ls j ws N Hch Hcmp Hj). lia. }
    assert (Hin : FileDisc.LEchoF ws N ∈ drop (slast Ls).1 L).
    { apply list_elem_of_lookup. exists (j - (slast Ls).1). rewrite lookup_drop.
      rewrite (_ : (slast Ls).1 + (j - (slast Ls).1) = j); [| lia].
      exact (prefix_lookup_Some _ _ _ _ Hj HlswL). }
    pose proof (sync_chain_mono ls L Ls HlsL Hch) as Hch'.
    assert (Hw' : uadm L (slast Ls) (fcont_of av')).
    { rewrite Hav'. apply (uadm_redir L (slast Ls) (fcont_of av) ws N sel Hin Hsel).
      exact (uadm_mono ls L (slast Ls) _ HlsL Hw). }
    iFrame "Hph". iExists L.
    iApply (sync_body_intro c r av' L Ls Hch' Hw' with "Hreg HL Hr").
  Qed.

  (* the sync part and the position read only an instance's sync fields *)
  Lemma sync_claim_rec_eq (c : file_fixed) (r1 r2 : file_names) (av : aview) :
    fn_sync r1 = fn_sync r2 -> fn_era r1 = fn_era r2 -> fn_role r1 = fn_role r2 ->
    fn_pos r1 = fn_pos r2 -> fn_deed r1 = fn_deed r2 ->
    sync_claim c r1 av -∗ sync_claim c r2 av.
  Proof using .
    destruct r1, r2; cbn. intros -> -> -> -> ->.
    iIntros "(%ls & %Ls & H)". iExists ls, Ls.
    rewrite /sync_body /sync_role /fposf. cbn [fn_sync fn_era fn_role fn_pos fn_deed].
    iExact "H".
  Qed.

  Lemma fpos_rec_eq (r1 r2 : file_names) (n : nat) :
    fn_role r1 = fn_role r2 -> fn_pos r1 = fn_pos r2 -> fpos r1 n -∗ fpos r2 n.
  Proof using .
    destruct r1, r2; cbn. intros -> ->. rewrite /fpos /fposf.
    cbn [fn_role fn_pos]. iIntros "H". iExact "H".
  Qed.

  (* a lower bound shrinks *)
  Lemma sl_lb_mono (γ : gname) (Ls Ls' : list srec) :
    Ls' `prefix_of` Ls -> sl_lb γ Ls -∗ sl_lb γ Ls'.
  Proof using .
    intros Hp. rewrite /sl_lb. iApply own_mono. by apply mono_list_lb_mono.
  Qed.

  (* A MOVE THAT LEAVES THE FILES: the claim reads the view through its
     files alone *)
  Lemma sync_claim_same (c : file_fixed) (r : file_names) (av av' : aview) :
    fcont_of av = fcont_of av' -> sync_claim c r av -∗ sync_claim c r av'.
  Proof using .
    intros He. iIntros "(%ls & %Ls & #Hreg & #Hlb & %Hch & %Hw & Hr)".
    iExists ls, Ls. iFrame "Hreg Hlb Hr". rewrite -He. by iPureIntro.
  Qed.

  (* THE REDIRECT PERMIT a writer hands a move of its line's file: its
     line's lower bound (the round's list, ENDING at the line), the chunk
     subset the move sets the file to, and its QUARTER of the round
     position at the list's length -- the one linear piece, which the move
     keeps (a two-phase move parks it in the claim).  At the files the
     move goes between. *)
  Definition sync_redir (c : file_fixed) (r : file_names) (S S' : fstate) : iProp Σ :=
    (∃ (ls_w : list fl_line) (ws : list (list (bv 8))) (N : list (bv 8))
       (sel : list nat) (n : nat),
       ⌜last ls_w = Some (FileDisc.LEchoF ws N)⌝ ∗ ⌜sel_ok (echo_chunks ws) sel⌝
       ∗ ⌜n = length ls_w⌝ ∗ ⌜S' = <[N := subseq (echo_chunks ws) sel]> S⌝
       ∗ fl_lb c ls_w ∗ fposq r n)%I.

  Global Instance sync_redir_timeless c r S S' : Timeless (sync_redir c r S S').
  Proof using . rewrite /sync_redir. apply _. Qed.

  (* ...and the move: the running claim at the new files, the quarter out *)
  Lemma sync_claim_redir (c : file_fixed) (r : file_names) (av av' : aview) :
    sync_redir c r (fcont_of av) (fcont_of av') -∗ sync_claim c r av -∗
      sync_claim c r av' ∗ ∃ n : nat, fposq r n.
  Proof using .
    iIntros "(%ls_w & %ws & %N & %sel & %n & %Hlast & %Hsel & %Hn & %Hav & #Hlbw & Hq)".
    iIntros "(%ls & %Ls & Hb)".
    iAssert (⌜fn_role r = false⌝)%I as %Hrole; [by iDestruct "Hq" as "[% _]" |].
    destruct ls_w as [| x ls0] using rev_ind; [discriminate Hlast |].
    rewrite last_snoc in Hlast. injection Hlast as ->.
    iDestruct (sync_claim_redir_step c r av av' ls Ls (ls0 ++ [FileDisc.LEchoF ws N])
                 (length ls0) ws N sel n Hrole
                 ltac:(by rewrite lookup_app_r // Nat.sub_diag)
                 ltac:(rewrite length_app /=; lia) Hsel Hn Hav
                 with "Hb Hlbw Hq") as "[Hb Hq]".
    iDestruct "Hb" as (L) "Hb". iSplitR "Hq"; [iExists L, Ls; iExact "Hb" |].
    iExists n. iExact "Hq".
  Qed.

  (* THE ROUND POSITION ADVANCES (design 4.5 "The round position"): the
     holder's half and the running claim's, both, to a LATER count -- the
     records stay below it *)
  Lemma sync_claim_advance (c : file_fixed) (r : file_names) (av : aview)
      (n n' : nat) :
    n <= n' ->
    sync_claim c r av -∗ fposh r n ==∗ sync_claim c r av ∗ fposh r n'.
  Proof using .
    intros Hle. iIntros "(%ls & %Ls & #Hreg & #Hlb & %Hch & %Hw & Hr) [[%Hrole Hh] [_ Hw4]]".
    rewrite /sync_role Hrole.
    iDestruct "Hr" as "(Hq & #Hcml & (%m & Hpm & %Hbm) & #Hrr)".
    iDestruct (fposf_agree with "Hpm Hh") as %->.
    iMod (fposf_update r n n' with "Hpm Hh Hw4") as "(Hpm & Hh & Hw4)".
    iModIntro. iSplitR "Hh Hw4"; [| by iFrame "Hh Hw4"].
    iExists ls, Ls. iFrame "Hreg Hlb". iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. rewrite /sync_role Hrole.
    iFrame "Hq Hcml Hrr". iExists n'. iFrame "Hpm". iPureIntro.
    intros rec Hin. pose proof (Hbm rec Hin). lia.
  Qed.

  (* POWERON'S RE-BASE (design 4.5 "PowerOn"; [App.al_xfer]'s body): the
     durable copy at its era [k], the new era's fresh list (full authority
     at [[]]) registered at [S gen], the ledger's floor [F] at the copy's
     list, the loan at [gen + 1].  [F ⊑ Ls_c] (the half against the
     fragment); the fresh list is set to [Ls_c]; the counter bumps to
     [S gen] ([k <= gen + 1]: the copy's started certificate against the
     loan); the certificate is re-minted at [S gen] off the loan.  Out: the
     re-based copy, the running claim, the token, and for the ledger's
     return hook the new list's lower bound, [F ⊑ Ls_c] and the BOOT FACT
     (the view admissible after the floor's last record,
     [sync_chain_shrink]); the dead era's half is dropped.  THE ROUND
     POSITION (lane SY3-A3b): the running claim's is FRESH, founded at the
     copy's line count [length ls] (the chain puts every record's line in
     [ls]); its other half goes out beside the ledger's part, for the deed
     holder. *)
  Lemma sync_claim_rebase (c : file_fixed) (r : file_names) (av : aview) (γ : gname)
      (gen : nat) (F : list srec) (d : gname) :
    fn_role r = true ->
    sync_claim c r av -∗ sl_auth γ 1 [] -∗ sync_reg c (S gen) γ -∗
    sl_lb (ff_hist c) F -∗ sync_st_auth c (gen + 1) ==∗
      ∃ γp : gname,
      sync_claim c (fn_with r γ (S gen) true) av
      ∗ sync_claim c (fn_run r d γ (S gen) γp) av
      ∗ union_tkb c gen
      ∗ (∃ (ls : list fl_line) (Ls_c : list srec),
           fl_lb c ls ∗ sl_lb γ Ls_c ∗ sl_lb (ff_hist c) Ls_c
           ∗ ⌜F `prefix_of` Ls_c⌝ ∗ ⌜uadm ls (slast F) (fcont_of av)⌝
           ∗ fposh (fn_run r d γ (S gen) γp) (length ls)
           ∗ run_reg c (S gen) γp d)
      ∗ sync_st_auth c (gen + 1).
  Proof using .
    destruct r as [rc rd rt re rγ rk rb rp].
    cbn [fn_role fn_era fn_sync fn_with fn_with_pos fn_pos fn_run]. intros ->.
    iIntros "(%ls & %Ls_c & #Hrego & #Hlb & %Hch & %Hw & Hr) Hnew #Hreg #HF Hst".
    unfold sync_role; cbn [fn_role fn_era fn_sync].
    iDestruct "Hr" as "(Ho & Hcm & #Hsto & Hho & Hra)".
    iDestruct (sl_auth_lb_prefix with "Hho HF") as %HFc.
    iDestruct (sl_lb_get with "Hho") as "#Hhlb".
    iDestruct (mono_nat_auth_lb_own_valid (mono_natG0 := fa_st) with "Hst Hsto") as %[_ Hk].
    (* the copy is of an EARLIER era: at [S gen] its list would be the fresh
       one, whose full authority is in hand *)
    iAssert ⌜rk <> S gen⌝%I as %Hne.
    { destruct (decide (rk = S gen)) as [-> | Hne]; [| by iPureIntro].
      iDestruct (sync_reg_agree with "Hrego Hreg") as %->.
      iDestruct (sl_auth_1_excl with "Hnew Ho") as %[]. }
    (* the new era's running claim, registered *)
    iMod (fpos_alloc (length ls)) as (γp) "(Hp1 & Hp2 & Hp3)".
    iMod (run_auth_register c rk (S gen) γp d ltac:(lia) with "Hra") as "[Hra #Hrr]".
    (* the fresh list at the copy's *)
    iMod (sl_auth_update γ [] Ls_c with "Hnew") as "Hnew"; [apply prefix_nil |].
    iDestruct (sl_lb_get with "Hnew") as "#Hnlb".
    iDestruct (sl_auth_split3_1 with "Hnew") as "(Hh & Hq & Hqt)".
    (* the counter, and the certificate *)
    iMod (mono_nat_own_update (mono_natG0 := fa_st) (S gen) with "Hcm") as "[Hcm #Hcml]"; [lia |].
    iDestruct (mono_nat_lb_own_get (mono_natG0 := fa_st) with "Hst") as "#Hst'".
    (* the fresh round position (above), at the copy's line count, above
       every record *)
    assert (Hbm : forall rec : srec, rec ∈ Ls_c -> rec.1 <= length ls).
    { intros rec Hin. pose proof (sync_chain_le_last ls Ls_c Hch rec Hin).
      pose proof (sync_chain_pos ls Ls_c Hch). lia. }
    rewrite (_ : (gen + 1)%nat = S gen); [| lia].
    iModIntro. iExists γp.
    iSplitL "Hh Hcm Hho Hra".
    { iExists ls, Ls_c. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch Hw) "Hreg Hlb Hh Hcm Hst' Hho Hra". }
    iSplitL "Hq Hp1".
    { iExists ls, Ls_c. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync fn_pos fn_deed].
      iFrame (Hch Hw) "Hreg Hlb Hq Hcml Hrr". iExists (length ls).
      rewrite /fposf /=. iFrame "Hp1". iPureIntro. exact Hbm. }
    iSplitL "Hqt".
    { iExists γ, Ls_c. iFrame "Hreg Hqt Hcml". }
    iFrame "Hst". iExists ls, Ls_c. iFrame "Hlb Hnlb Hhlb Hrr".
    iSplitR; [iPureIntro; exact HFc |].
    iSplitR; [iPureIntro; exact (sync_chain_shrink ls Ls_c F _ Hch HFc Hw) |].
    rewrite /fposh /fpos /fposq /fposf /=. iFrame "Hp2 Hp3". done.
  Qed.

  (* THE BIRTH (design 4.5 "Birth"): era 0's durable copy, from the
     birth's era-0 registration, the half of the fresh empty list, the
     counter's authority at 0 and any lower bound of the line list, at a
     view with no user file.  The started certificate at 0 is free. *)
  Lemma sync_claim_birth (c : file_fixed) (r0 : file_names) (av0 : aview)
      (γ0 : gname) (ls : list fl_line) :
    fn_role r0 = true -> fn_era r0 = 0 -> fn_sync r0 = γ0 -> fcontent_of av0 = ∅ ->
    sync_reg c 0 γ0 -∗ sl_auth γ0 (1/2) [] -∗ sync_cm_auth c 0 -∗
    sl_auth (ff_hist c) 1 [] -∗ run_auth c 0 -∗ fl_lb c ls ==∗ sync_claim c r0 av0.
  Proof using .
    destruct r0 as [rc rd rt re rγ rk rb rp].
    cbn [fn_role fn_era fn_sync]. intros -> -> -> Hav.
    iIntros "#Hreg Hh Hcm Hhi Hra #Hlb".
    iMod (mono_nat_lb_own_0 (mono_natG0 := fa_st) (ff_st c)) as "#Hst".
    assert (Hw : uadm ls (slast []) (fcont_of av0)).
    { rewrite /fcont_of Hav dst_content_empty. exact (uadm_self ls srec0). }
    pose proof (sync_chain_nil ls) as Hch.
    iModIntro. iExists ls, []. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
    iFrame (Hch Hw) "Hreg Hlb Hh Hcm Hst Hhi Hra".
  Qed.

  (* =================================================================== *)
  (*  5.  VACUITY: THE PREMISES ARE JOINTLY SATISFIABLE                   *)
  (* =================================================================== *)

  (* the merge's: a copy and a running claim at era [S gen], at one list,
     the token, the loan -- all from fresh allocations *)
  Lemma union_merge_closes_sat (gen : nat) (ef : echo_fixed) (r0 : file_names) :
    ⊢ |==> ∃ (c : file_fixed) (r_o r : file_names) (av : aview),
        ⌜fn_role r_o = true /\ fn_role r = false /\ fn_era r = S gen⌝
        ∗ sync_claim c r_o av ∗ sync_claim c r av ∗ union_tkb c gen
        ∗ sync_st_auth c (gen + 1).
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO fl_line)))) as (γfl) "Hfl";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γs) "Hs";
      [apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname)) as (γreg) "Hreg".
    iMod (ghost_map_insert_persist (S gen) γs with "Hreg") as "[_ #Hel]";
      [apply lookup_empty |].
    iMod (@mono_nat_own_alloc Σ fa_st (S gen)) as (γcm) "[Hcm #Hcml]".
    iMod (@mono_nat_own_alloc Σ fa_st (gen + 1)) as (γst) "[Hst #Hstl]".
    iMod (fpos_alloc 0) as (γp) "(Hp & _ & _)".
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γh) "Hhi";
      [apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname * gname)) as (γrun) "Hrun".
    iDestruct (run_auth_0 (MkFileFixed ef γfl γreg γcm γst γh γrun) with "Hrun") as "Hra".
    iMod (run_auth_register _ 0 (S gen) γp (fn_deed r0) ltac:(lia) with "Hra") as "[Hra #Hrr]".
    iDestruct (fl_auth_lb (MkFileFixed ef γfl γreg γcm γst γh γrun) [] with "Hfl") as "[_ #Hlb]".
    iDestruct (sl_auth_split3_1 γs [] with "Hs") as "(Hh & Hq & Hqt)".
    rewrite (_ : (gen + 1)%nat = S gen); [| lia].
    iModIntro.
    iExists (MkFileFixed ef γfl γreg γcm γst γh γrun),
      (fn_with r0 γs (S gen) true), (fn_with_pos r0 γs (S gen) false γp), ∅.
    iSplitR; [iPureIntro; cbn [fn_role fn_era fn_with fn_with_pos]; done |].
    assert (Hw : uadm [] (slast []) (fcont_of ∅)).
    { rewrite fcont_of_empty. exact (uadm_self [] srec0). }
    pose proof (sync_chain_nil []) as Hch.
    iSplitL "Hh Hcm Hhi Hra".
    { iExists [], []. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync fn_with fn_with_pos].
      iFrame (Hch Hw) "Hel Hlb Hh Hcm Hstl Hra". iExact "Hhi". }
    iSplitL "Hq Hp".
    { iExists [], []. unfold sync_body, sync_role;
        cbn [fn_role fn_era fn_sync fn_with fn_with_pos fn_pos fn_deed].
      iFrame (Hch Hw) "Hel Hlb Hq Hcml Hrr". iExists 0. rewrite /fposf /=.
      iFrame "Hp". iPureIntro. intros rec Hin. by apply elem_of_nil in Hin. }
    iFrame "Hst". iExists γs, []. iFrame "Hel Hqt Hcml".
  Qed.

  (* the re-base's: an era-0 copy, a fresh list registered at [S gen], the
     floor at the copy's list, the loan *)
  Lemma sync_claim_rebase_sat (gen : nat) (ef : echo_fixed) (r0 : file_names) :
    ⊢ |==> ∃ (c : file_fixed) (r : file_names) (av : aview) (γ : gname) (F : list srec),
        ⌜fn_role r = true⌝
        ∗ sync_claim c r av ∗ sl_auth γ 1 [] ∗ sync_reg c (S gen) γ
        ∗ sl_lb (ff_hist c) F ∗ sync_st_auth c (gen + 1).
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO fl_line)))) as (γfl) "Hfl";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γ0) "H0";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γ) "Hnew";
      [apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname)) as (γreg) "Hreg".
    iMod (ghost_map_insert_persist 0 γ0 with "Hreg") as "[Hreg #H0el]";
      [apply lookup_empty |].
    iMod (ghost_map_insert_persist (S gen) γ with "Hreg") as "[_ #Hel]";
      [by rewrite lookup_insert_ne |].
    iMod (@mono_nat_own_alloc Σ fa_st 0) as (γcm) "[Hcm _]".
    iMod (@mono_nat_own_alloc Σ fa_st (gen + 1)) as (γst) "[Hst _]".
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γh) "Hhi";
      [apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname * gname)) as (γrun) "Hrun".
    iDestruct (run_auth_0 (MkFileFixed ef γfl γreg γcm γst γh γrun) with "Hrun") as "Hra".
    iDestruct (fl_auth_lb (MkFileFixed ef γfl γreg γcm γst γh γrun) [] with "Hfl") as "[_ #Hlb]".
    iDestruct (sl_auth_split3_1 γ0 [] with "H0") as "(Hh & _ & _)".
    iDestruct (sl_lb_get γh 1 [] with "Hhi") as "#HF".
    iMod (sync_claim_birth (MkFileFixed ef γfl γreg γcm γst γh γrun)
            (fn_with r0 γ0 0 true) ∅ γ0 [] with "H0el Hh Hcm Hhi Hra Hlb") as "Hcl";
      [reflexivity | reflexivity | reflexivity
      | rewrite /fcontent_of /aents lookup_empty; reflexivity |].
    iModIntro.
    iExists (MkFileFixed ef γfl γreg γcm γst γh γrun),
      (fn_with r0 γ0 0 true), ∅, γ, [].
    iSplitR; [done |]. iFrame "Hcl Hnew Hel HF Hst".
  Qed.
End sync.

(* ===================================================================== *)
(*  6.  THE HOOK FAMILY ([App.app_hk]), over an abstract claim, and at    *)
(*      [file_pred]                                                       *)
(* ===================================================================== *)
Section union_tk.
  Context {Σ : gFunctors} `{!echoOutG Σ, !fileAppG Σ}.

  (* ...AND THE TOKEN AS THE ERA HOLDS IT: the shares, or the taint (a
     tainted durable copy carries no sync part, so the PowerOn transport
     cannot rebuild the era's shares out of it) *)
  Definition union_tk (c : file_fixed) (k : nat) : iProp Σ :=
    (file_taint c ∨ union_tkb c k)%I.

  Global Instance union_tk_timeless c k : Timeless (union_tk c k).
  Proof using . rewrite /union_tk. apply _. Qed.
End union_tk.

Section union_hk.
  Context {Σ : gFunctors} `{!echoOutG Σ, !fileAppG Σ}.

  (* the design's [Hk c k Q]: both instances at the era [S k], the new
     durable copy and the running claim at one map, the token; everything
     back, and [Q].  The new copy's record is a COPY's (its durable-copy
     predicate, [App.app_okc], which the runner receives off the merge --
     lane SY3-A3b).  A BASIC update under [◇] (sync SY3-A3bc): the hook
     family is DATA of the application's fixed record, which exists before
     any machine instance, so it names no invariant class; the runner's
     fancy update absorbs both, and frames the guest's half of the map
     itself. *)
  Definition union_hk (A : file_fixed -> file_names -> aview -> iProp Σ)
      (c : file_fixed) (k : nat) (Q : iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (r r' : file_names),
       ⌜fn_era r = S k⌝ -∗ ⌜fn_era r' = S k⌝ -∗ ⌜fn_role r' = true⌝ -∗
       ▷ A c r' (abs_view I) -∗ ▷ A c r (abs_view I) -∗
       union_tk c k ==∗
         ◇ (▷ A c r' (abs_view I) ∗ ▷ A c r (abs_view I) ∗ union_tk c k ∗ Q))%I.
End union_hk.

Local Open Scope Z_scope.
Section FileClaim2.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* ---------------------------------------------------------------- *)
  (*  4.  THE CLAIM                                                     *)
  (* ---------------------------------------------------------------- *)

  (* EXACT: the claim's halves at the content.  IN FLIGHT: the whole deed
     at the OLD value, the ticket's half at the old value, the content at
     the NEW one -- the window between a fire's two phases -- and the
     QUARTER of the round position the move's writer parked (sync SY3-A3bc:
     the move re-closed the claim's sync part at the new content with it,
     and phase 2 hands it back).  The two together are THE CORE, which is
     what every move the deed's holder pays for itself runs on. *)
  Definition f_core (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    ((∃ s : dst, fdeed r s ∗ ftkt r s ∗ f_typed c s ∗ ⌜f_ok av s⌝)
     ∨ (∃ (s s' : dst) (n : nat), fdeed_whole r s ∗ ftkt r s ∗ f_typed c s'
          ∗ ⌜f_ok av s'⌝ ∗ fposq r n))%I.

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
     console is in one of its states AND the files are in the deed's state
     AND (sync SY3-A3bc) the files are admissible after the instance's last
     recorded sync ([sync_claim], section 3b). *)
  Definition file_pred (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    (file_taint c
     ∨ (⌜file_fs_pure av⌝ ∗ cons_state (fn_cons r) av ∗ f_state c r av
        ∗ sync_claim c r av))%I.

  (* every arm of the file state reads the view at SOME deed state *)
  Lemma f_state_fok (c : file_fixed) (r : file_names) (av : aview) :
    f_state c r av -∗ ⌜exists s : dst, f_ok av s⌝.
  Proof using .
    rewrite /f_state /f_core /f_esc_live.
    iIntros "[[_ [(%s & _ & _ & _ & %Hok) | (%s & %s' & %n & _ & _ & _ & %Hok & _)]]
             | (%h0 & %s & %g & _ & _ & _ & _ & _ & %Hok)]"; by iExists _.
  Qed.

  Global Instance file_pred_timeless c r av : Timeless (file_pred c r av).
  Proof using . rewrite /file_pred. apply _. Qed.

  (* the exact arm, as the transports and the era mint build it.  THE
     LEDGER IS A PREMISE (lane F-OPEN-5): the claim carries it in both
     arms, so a producer of the claim must hand it in -- the era mint
     hands the fresh empty one, a fire hands back the one it opened. *)
  Lemma file_pred_exact (c : file_fixed) (r : file_names) (av : aview) (s : dst) :
    file_fs_pure av -> f_ok av s ->
    cons_state (fn_cons r) av -∗ f_esc_wrap r -∗
    fdeed r s -∗ ftkt r s -∗ f_typed c s -∗ sync_claim c r av -∗
    file_pred c r av.
  Proof using .
    intros Hp Hok. iIntros "Hc Hw Hd Ht #Hty Hsy". rewrite /file_pred. iRight.
    iSplitR; [ by iPureIntro |]. iFrame "Hc Hsy".
    iApply (f_state_of_core with "Hw").
    iApply (f_core_exact c r av s Hok with "Hd Ht Hty").
  Qed.

  (* THE ECHO APPLICATION'S CLAIM IS THIS ONE WITH THE FILE FORGOTTEN --
     which is what lets every console law [AppEcho] proves at [echo_pred]
     be read here: open, apply, close with the file conjunct framed.
     Stated as an ACCESSOR so that nothing is lost. *)
  Lemma file_pred_cons (c : file_fixed) (r : file_names) (av : aview) :
    file_pred c r av -∗
    echo_pred (ff_echo c) (fn_cons r) av ∗
    (echo_pred (ff_echo c) (fn_cons r) av -∗ file_pred c r av).
  Proof using .
    rewrite /file_pred /echo_pred /file_taint.
    iIntros "[#Ht | (%Hp & Hc & Hf & Hsy)]".
    { iSplitR; [ by iLeft |]. iIntros "_". by iLeft. }
    iSplitL "Hc".
    { iRight. iFrame "Hc". iPureIntro. exact (file_fs_pure_echo av Hp). }
    iIntros "[#Ht | (_ & Hc)]".
    { by iLeft. }
    iRight. iFrame "Hc Hf Hsy". by iPureIntro.
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
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf & Hsy)]".
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
    { iDestruct "Hf" as (s0 s1 np) "(Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s') "(Hd' & Ht & #Hty & %Hok)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iSplitL "Hc Hw Hd' Ht Hsy".
    { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc Hsy".
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
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf & Hsy)]".
    { iSplitR; [ by iLeft |]. iRight. by iRight. }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hwr Hf] | Hf]".
    - (* NO LIVE ESCROW: every entry of the ledger is spent, mine too *)
      rewrite /f_esc_wrap. iDestruct "Hwr" as (h) "[Ha #Hrec]".
      iDestruct (esc_wit_lookup with "Ha Hwit") as %Hn.
      iDestruct (esc_recs_at h n s g Hn with "Hrec") as "#Hsp".
      iSplitL "Hc Ha Hf Hsy".
      { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc Hsy". iLeft.
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
      iSplitL "Hc Hlive Hsy".
      { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc Hsy". by iRight. }
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
    - iDestruct "Hf" as (s s' np) "(Hw & Ht & #Hty & %H & Hq)". iRight. iExists s, s', np.
      iFrame "Hw Ht Hty Hq". iPureIntro. by apply Hok.
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
    iIntros "[#Ht | (%Hp & Hc & Hf & Hsy)]"; [ by iLeft |].
    iDestruct (f_state_fok with "Hf") as %[s0 Hok0].
    iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    iSplitL "Hf"; [ by iApply (f_state_mono with "Hf") |].
    iApply (sync_claim_same with "Hsy"). rewrite /fcont_of.
    by rewrite (f_ok_fcontent _ _ Hok0) (f_ok_fcontent _ _ (Hok _ Hok0)).
  Qed.

  (* PHASE 1, THE PARK: the holder's deed half goes in, the arm goes from
     exact to in flight at the new content.  Update-free, so it is
     [AppInv.app_step]'s wand verbatim once lifted by [iModIntro].
     ...AND THE WRITER'S REDIRECT PERMIT (sync SY3-A3bc): the claim's sync
     part moves to the new files with it ([sync_claim_redir]), and the
     permit's position quarter is PARKED in the in-flight arm, which phase 2
     ([file_resync]) hands back. *)
  Lemma file_step_park (c : file_fixed) (r : file_names) (av av' : aview)
      (s s' : dst) :
    (file_fs_pure av -> file_fs_pure av') ->
    (cons_absent av -> cons_absent av') ->
    (forall i, cons_present_at i av -> cons_present_at i av') ->
    (f_ok av s -> f_ok av' s') ->
    fdeed r s -∗ f_typed c s' -∗ sync_redir c r (dst_content s) (dst_content s') -∗
    file_pred c r av -∗ file_pred c r av'.
  Proof using .
    intros Hpins Hab Hpr Hok. iIntros "Hd #Hty' Hre Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hp & Hc & Hf & Hsy)]"; [ by iLeft |].
    iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    rewrite /f_state.
    iDestruct "Hf" as "[[Hw Hf] | Hf]"; last first.
    { rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s0 g) "(_ & _ & Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    rewrite /f_core.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1 np) "(Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s0) "(Hd' & Ht & _ & %Hok0)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iDestruct (fdeed_join with "Hd Hd'") as "Hwh".
    iDestruct (sync_claim_redir c r av av' with "[Hre] Hsy") as "[Hsy Hq]".
    { rewrite /fcont_of (f_ok_fcontent _ _ Hok0) (f_ok_fcontent _ _ (Hok Hok0)).
      iExact "Hre". }
    iDestruct "Hq" as (np) "Hq".
    iSplitR "Hsy"; [| iExact "Hsy"].
    iLeft. iFrame "Hw". iRight. iExists s, s', np. iFrame "Hwh Ht Hty' Hq".
    iPureIntro. by apply Hok.
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
    sync_redir c r (dst_content s) (dst_content s') -∗
    file_pred c r av ==∗ file_pred c r av'.
  Proof using .
    intros Hpins Hab Hpr Hok. iIntros "#Hkey Htok #Hty' Hre Hp".
    iDestruct "Hkey" as "[#Hwit | #Ht0]"; last first.
    { iModIntro. rewrite /file_pred. by iLeft. }
    rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins0 & Hc & Hf & Hsy)]".
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
    iDestruct (sync_claim_redir c r av av' with "[Hre] Hsy") as "[Hsy Hq]".
    { rewrite /fcont_of (f_ok_fcontent _ _ Hok0) (f_ok_fcontent _ _ (Hok Hok0)).
      iExact "Hre". }
    iDestruct "Hq" as (np) "Hq".
    iModIntro. iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hc"; [ by iApply (cons_state_mono with "Hc") |].
    iSplitR "Hsy"; [| iExact "Hsy"].
    iLeft. iSplitL "Ha".
    { rewrite /f_esc_wrap. iExists (h0 ++ [(s, g)]). iFrame "Ha".
      iApply (esc_recs_snoc h0 (s, g) with "Hrec"). iExact "Hsp". }
    rewrite /f_core. iRight. iExists s, s', np. iFrame "Hwh Htk Hty' Hq".
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
      + iDestruct "Hf" as (s s' np) "(Hwh & Ht & #Hty & %Hok & Hq)".
        pose proof (f_ok_fcontent av s' Hok) as Hc.
        iSplitL "Hw Hwh Ht Hq".
        * iLeft. iFrame "Hw". iRight. iExists s, s', np. iFrame "Hwh Ht Hty Hq".
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
      + iDestruct "Hf" as (s s' np) "(Hwh & Ht & #Hty & %Hok & Hq)".
        rewrite (f_ok_fcontent av s' Hok). iSplitL; [| iExact "Hty"].
        iLeft. iFrame "Hw". iRight. iExists s, s', np. iFrame "Hwh Ht Hty Hq".
        by iPureIntro.
    - rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s g) "(Ha & #Hh & Hwh & Ht & #Hty & %Hok)".
      rewrite (f_ok_fcontent av s Hok). iSplitL; [| iExact "Hty"].
      iRight. iExists h0, s, g. iFrame "Ha Hh Hwh Ht Hty". by iPureIntro.
  Qed.

  (* the original, read as its echo half and its file half, under the
     later the transports receive it at *)
  (* THE FILE HALF: the taint, or the pins, the files' state and the sync
     part *)
  Definition file_rest (c : file_fixed) (r : file_names) (av : aview) : iProp Σ :=
    (file_taint c ∨ (⌜file_fs_pure av⌝ ∗ f_state c r av ∗ sync_claim c r av))%I.

  Global Instance file_rest_timeless c r av : Timeless (file_rest c r av).
  Proof using . rewrite /file_rest. apply _. Qed.

  Lemma file_pred_split (c : file_fixed) (r : file_names) (av : aview) :
    file_pred c r av -∗
    echo_pred (ff_echo c) (fn_cons r) av ∗ file_rest c r av.
  Proof using .
    rewrite /file_pred /echo_pred /file_taint /file_rest.
    iIntros "[#Ht | (%Hp & Hc & Hf & Hsy)]".
    { iSplitR; by iLeft. }
    iSplitL "Hc".
    { iRight. iFrame "Hc". iPureIntro. exact (file_fs_pure_echo av Hp). }
    iRight. iFrame "Hf Hsy". by iPureIntro.
  Qed.

  (* the file half is carried across a move that leaves the files where
     they were *)
  Lemma file_rest_mono (c : file_fixed) (r : file_names) (av av' : aview) :
    (file_fs_pure av -> file_fs_pure av') ->
    (forall s, f_ok av s -> f_ok av' s) ->
    file_rest c r av -∗ file_rest c r av'.
  Proof using .
    intros Hpins Hok. rewrite /file_rest.
    iIntros "[#Ht | (%Hp & Hf & Hsy)]"; [ by iLeft |].
    iDestruct (f_state_fok with "Hf") as %[s0 Hok0].
    iRight. iSplitR; [ iPureIntro; by apply Hpins |].
    iSplitL "Hf"; [ by iApply (f_state_mono with "Hf") |].
    iApply (sync_claim_same with "Hsy"). rewrite /fcont_of.
    by rewrite (f_ok_fcontent _ _ Hok0) (f_ok_fcontent _ _ (Hok _ Hok0)).
  Qed.

  (* ...and put back together, at any console pair the echo half came
     back at *)
  Lemma file_pred_join (c : file_fixed) (r : file_names) (av : aview) :
    echo_pred (ff_echo c) (fn_cons r) av -∗ file_rest c r av -∗
    file_pred c r av.
  Proof using .
    rewrite /file_pred /echo_pred /file_taint /file_rest.
    iIntros "[#Ht | (_ & Hc)] [#Ht' | (%Hp & Hf & Hsy)]"; try by iLeft.
    iRight. iFrame "Hc Hf Hsy". by iPureIntro.
  Qed.

  (* the file state and the console pair read only their own names *)
  Lemma f_state_rec_eq (c : file_fixed) (r r' : file_names) (av : aview) :
    fn_deed r = fn_deed r' -> fn_tkt r = fn_tkt r' -> fn_esc r = fn_esc r' ->
    fn_role r = fn_role r' -> fn_pos r = fn_pos r' ->
    f_state c r av ⊣⊢ f_state c r' av.
  Proof using .
    destruct r, r'; cbn. intros -> -> -> -> ->.
    rewrite /f_state /f_core /f_esc_live /f_esc_wrap /fdeed /fdeed_whole /ftkt
      /esc_auth /fposq /fposf.
    cbn [fn_deed fn_tkt fn_esc fn_role fn_pos]. reflexivity.
  Qed.

  (* a later absorbed into a basic update whose result is under [◇] *)
  Lemma bupd_except_0_elim (P : iProp Σ) : ◇ (|==> ◇ P) ⊢ |==> ◇ P.
  Proof using .
    rewrite /bi_except_0. iIntros "[H | H]"; [| iExact "H"].
    iModIntro. iLeft. iExact "H".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  6a.  THE BOOT RESOURCE, AND THE BOOT TRANSPORT                    *)
  (* ---------------------------------------------------------------- *)

  (* WHAT /init IS HANDED AT THE ERA MINT: echo's (the console key or
     flag), the instance's ERA (sync SY3-A3bc: [App.al_boot_ok] reads it),
     and THE DEED -- both halves the process chain owns, at the clone's
     content -- beside the typed witness of that content, or the taint.
     The witness sits under ONE later: it is read off the original arm,
     which the transport only sees under [▷]; /init strips it at its first
     step, everything under it being timeless. *)
  Definition file_boot_at (c : file_fixed) (k : nat) (r : file_names) (s : dst) : iProp Σ :=
    (echo_boot (ff_echo c) k (fn_cons r) ∗ ⌜fn_era r = k⌝
     ∗ fown r s ∗ ▷ (f_typed c s ∨ file_taint c))%I.

  (* ...at SOME deed state *)
  Definition file_boot (c : file_fixed) (k : nat) (r : file_names) : iProp Σ :=
    (∃ s : dst, file_boot_at c k r s)%I.

  (* THE POWER-ON TRANSPORT (sync SY3-A3bc, design 4.5 "PowerOn"; the floor
     re-ruled at SY3-A4): the slot's durable copy [r] (a COPY) re-based to
     the new era's list [γ] (full authority at [[]], registered at [S gen])
     under the loan of the started auth; the slot keeps it at [fn_with r γ
     (S gen) true]; the era's running claim [r'] at fresh deed names, the
     copy's re-based sync part and a FRESH round position founded at the
     copy's line count [length ls] -- whose holder's half goes out with the
     boot resource -- and the token.  THE FLOOR is a lower bound [F] of the
     RUN-LONG HISTORY, which the copy holds the authority of: [F ⊑ Ls_c],
     and the BOOT FACT -- the copy's files admissible after [F]'s last
     record -- follows along the copy's chain ([sync_chain_shrink]); no
     era is compared.  The boot resource names the deed's state, the
     copy's content, so the boot fact reaches /init at the state it files.
     A lower bound [ls0] of the line list stands in for [ls] when the copy
     is tainted.  The result is under [◇]: the copy's contents are
     timeless, and the counter bump needs them out of the slot's later. *)
  Lemma file_xfer_boot (c : file_fixed) (gen : nat) (r : file_names) (av : aview)
      (γ : gname) (ls0 : list fl_line) (F : list srec) :
    fn_role r = true ->
    sync_st_auth c (gen + 1) -∗ sl_auth γ 1 [] -∗ sync_reg c (S gen) γ -∗
    fl_lb c ls0 -∗ sl_lb (ff_hist c) F -∗
    ▷ file_pred c r av ==∗ ◇ (
      sync_st_auth c (gen + 1) ∗
      ▷ file_pred c (fn_with r γ (S gen) true) av ∗
      ∃ (r' : file_names) (ls : list fl_line),
        ⌜fn_era r' = S gen /\ fn_role r' = false /\ fn_sync r' = γ⌝ ∗
        ▷ file_pred c r' av ∗ file_boot_at c (S gen) r' (fcontent_of av) ∗ fl_lb c ls ∗
        (file_taint c
         ∨ (fposh r' (length ls) ∗ union_tkb c gen ∗ f_typed c (fcontent_of av)
            ∗ run_reg c (S gen) (fn_pos r') (fn_deed r')
            ∗ ∃ Ls_c : list srec, sl_lb γ Ls_c ∗ sl_lb (ff_hist c) Ls_c
                ∗ ⌜F `prefix_of` Ls_c /\ uadm ls (slast F) (fcont_of av)⌝))).
  Proof using .
    destruct r as [oc od ot oe oγ ok ob op]; cbn [fn_role fn_era fn_sync fn_with fn_with_pos].
    intros ->.
    iIntros "Hst Hnew #Hreg #Hls0 #HF Hp".
    iApply bupd_except_0_elim.
    iDestruct "Hp" as ">Hp". iModIntro.
    iDestruct (file_pred_split with "Hp") as "[He Hrest]".
    iDestruct (echo_xfer_boot (ff_echo c) (S gen)) as "#Hex".
    iMod ("Hex" $! oc av with "[He]") as "[He He']"; [iNext; iExact "He" |].
    iDestruct "He'" as (rc) "[He' Hb]".
    iMod (fnames_alloc rc (fcontent_of av) γ (S gen) false 0)
      as ([c1 d1 t1 e1 s1 k1 b1 p1]) "(%Hrc & %Hsy1 & Hd1 & Hd2 & Ht1 & Ht2 & Ha1 & _)".
    cbn [fn_cons fn_sync fn_era fn_role] in Hrc, Hsy1. destruct Hsy1 as (-> & -> & ->).
    subst c1.
    rewrite /file_rest.
    iDestruct "Hrest" as "[#Ht | (%Hpure & Hf & Hsy)]".
    { (* THE TAINTED COPY: everything answers with the taint *)
      iModIntro. iModIntro. iFrame "Hst".
      iSplitL "He".
      { iNext. iApply (file_pred_join c (MkFileNames oc od ot oe γ (S gen) true op) av
                         with "He"). by iLeft. }
      iExists (MkFileNames rc d1 t1 e1 γ (S gen) false p1), ls0.
      iSplitR; [iPureIntro; done |].
      iSplitL "He'".
      { iNext. iApply (file_pred_join c (MkFileNames rc d1 t1 e1 γ (S gen) false p1) av
                         with "He'"). by iLeft. }
      iSplitL; last first.
      { iSplitR; [iExact "Hls0" | by iLeft]. }
      rewrite /file_boot_at. iFrame "Hb". iSplitR; [done |].
      rewrite /fown. iFrame "Hd2 Ht2". iNext. by iRight. }
    iDestruct (f_state_typed_at with "Hf") as "[Hf #Hty]".
    iMod (sync_claim_rebase c (MkFileNames oc od ot oe oγ ok true op) av γ gen F d1 eq_refl
            with "Hsy Hnew Hreg HF Hst")
      as (γp) "(Hsys & Hsyr & Htk & Hout & Hst)".
    iDestruct "Hout" as (ls Ls_c) "(#Hlb & #HLc & #HHc & %HFc & %Hadm & Hpos & #Hrr)".
    iDestruct (f_state_copy c (MkFileNames oc od ot oe oγ ok true op)
                 (MkFileNames rc d1 t1 e1 γ (S gen) false γp) av
                 with "Ha1 Hd1 Ht1 Hf") as "[Hf Hf']".
    iModIntro. iModIntro. iFrame "Hst".
    iSplitL "He Hf Hsys".
    { iNext. iApply (file_pred_join c (MkFileNames oc od ot oe γ (S gen) true op) av
                       with "He"). iRight.
      iSplitR; [by iPureIntro |]. iFrame "Hsys".
      iApply (f_state_rec_eq with "Hf"); reflexivity. }
    iExists (MkFileNames rc d1 t1 e1 γ (S gen) false γp), ls.
    iSplitR; [iPureIntro; done |].
    iSplitL "He' Hf' Hsyr".
    { iNext. iApply (file_pred_join c (MkFileNames rc d1 t1 e1 γ (S gen) false γp) av
                       with "He'"). iRight.
      iSplitR; [by iPureIntro |]. iFrame "Hf'".
      iApply (sync_claim_rec_eq with "Hsyr"); reflexivity. }
    iSplitL "Hb Hd2 Ht2".
    { rewrite /file_boot_at. iFrame "Hb". iSplitR; [done |].
      rewrite /fown. iFrame "Hd2 Ht2".
      iNext. iLeft. iExact "Hty". }
    iSplitR; [iExact "Hlb" |].
    iRight. iSplitL "Hpos"; [iApply (fposh_rec_eq with "Hpos"); reflexivity |].
    iFrame "Htk Hty Hrr".
    iExists Ls_c. iFrame "HLc HHc". iPureIntro. done.
  Qed.

  (* ERA 0'S DURABLE COPY (sync SY3-A3bc, design 4.5 "Birth"): at the map a
     boot founds its file system at, when the disk is mkfs's image: echo's
     era-0 claim with NO FILE of the class present -- law L4 -- the deed at
     the empty map, and the SYNC PART the birth's slot share founds: the
     era-0 list's half, registered at 0, the commit-era counter's authority
     at 0 and a lower bound of the (empty) line list *)
  Lemma file_init (c : file_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) (γ0 : gname) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    sync_reg c 0 γ0 -∗ sl_auth γ0 (1/2) [] -∗ sync_cm_auth c 0 -∗
    sl_auth (ff_hist c) 1 [] -∗ run_auth c 0 -∗ fl_lb c [] ==∗
      ∃ r : file_names, ⌜fn_role r = true⌝ ∗ file_pred c r (abs_view (fss_inodes S)).
  Proof using .
    intros Hdk Hrec HS. iIntros "#Hreg Hh Hcm Hhi Hra #Hlb".
    iMod (echo_init (ff_echo c) dk D S Hdk Hrec HS) as (rc) "He".
    iMod (fnames_alloc rc ∅ γ0 0%nat true 0)
      as (r) "(%Hrc & %Hsy & Hd1 & _ & Ht1 & _ & Ha1 & _)".
    destruct Hsy as (Hγ & Hk & Hb).
    assert (Hok : f_ok (abs_view (fss_inodes S)) ∅).
    { apply f_ok_empty. intros N HN.
      exact (era0_recovery_class_absent txt_name dk D S N txt_laws
               Hdk Hrec HS HN). }
    iMod (sync_claim_birth c r (abs_view (fss_inodes S)) γ0 [] Hb Hk Hγ
            (f_ok_fcontent _ _ Hok) with "Hreg Hh Hcm Hhi Hra Hlb") as "Hsy".
    iModIntro. iExists r. iSplitR; [done |].
    iApply (file_pred_join with "[He]").
    { rewrite Hrc. iExact "He". }
    iRight. iSplitR.
    { iPureIntro. exact (file_fs_era0 dk D S Hdk Hrec HS). }
    iFrame "Hsy".
    rewrite /f_state. iLeft. iSplitL "Ha1".
    { rewrite /f_esc_wrap. iExists []. iFrame "Ha1". rewrite /esc_recs //. }
    rewrite /f_core. iLeft. iExists ∅.
    iSplitL "Hd1"; [ iExact "Hd1" |].
    iSplitL "Ht1"; [ iExact "Ht1" |].
    iSplitR; [ iApply f_typed_empty |].
    by iPureIntro.
  Qed.

  (* ...at the theorem's own literal shape ([App.xv6_app_adequacy]'s
     [Happ_init]), [AppEcho.echo_init_img]'s composition verbatim *)
  Lemma file_init_img (c : file_fixed) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) (γ0 : gname) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    fs_blocks dk = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    sync_reg c 0 γ0 -∗ sl_auth γ0 (1/2) [] -∗ sync_cm_auth c 0 -∗
    sl_auth (ff_hist c) 1 [] -∗ run_auth c 0 -∗ fl_lb c [] ==∗
      ∃ r : file_names, ⌜fn_role r = true⌝ ∗
        file_pred c r (abs_view (fss_inodes
          (FsDurImg.img_state (fs_blocks dk) sb nib))).
  Proof using .
    intros Himg Hdk -> ->.
    pose proof (img_snap_ok dk ndisk fsimg_sb nib fsimg_cov Himg) as HS.
    rewrite Hdk in HS. rewrite Hdk.
    exact (file_init c dk era0_D _ γ0 Hdk (era0_recovery dk Hdk) HS).
  Qed.
  (* ---------------------------------------------------------------- *)
  (*  6b.  THE SYNC HOOK AT THE FILE CLAIM (sync SY3-A4)                *)
  (* ---------------------------------------------------------------- *)

  (* a holder's half of the deed reads the claim's files *)
  Lemma f_state_deed_ok (c : file_fixed) (r : file_names) (av : aview) (s : dst) :
    fdeed r s -∗ f_state c r av -∗ f_state c r av ∗ fdeed r s ∗ ⌜f_ok av s⌝.
  Proof using .
    iIntros "Hd Hf". rewrite /f_state.
    iDestruct "Hf" as "[[Hw Hf] | Hf]"; last first.
    { rewrite /f_esc_live. iDestruct "Hf" as (h0 s0 g) "(_ & _ & Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    rewrite /f_core.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1 np) "(Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s') "(Hd' & Ht & #Hty & %Hok)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iSplitL "Hw Hd' Ht".
    { iLeft. iFrame "Hw". iLeft. iExists s. iFrame "Hd' Ht Hty". by iPureIntro. }
    iFrame "Hd". by iPureIntro.
  Qed.

  (* THE HOOK, OUT OF THE HOLDER'S LOAN.  The deed's holder (sh at a sync
     round) lends the hook its half of the deed at [s], its round position
     share at [n], a lower bound [ls'] of the line list ENDING at the sync
     line and the running claim's registration at the era.  Fired at
     whatever running record [r] and new durable copy [r'] the kernel's
     runner holds: the registration names [r]'s position and deed as the
     holder's; the deed's half reads the claim's files as [s]; the position
     advances to [length ls'] ([sync_claim_advance]) and the append closes
     ([union_hook_closes]).  The receipt [Q] is the caller's, built by the
     first continuation from the loan back (the position at [length ls'])
     and the run-long history's lower bound ending at the record
     [(length ls', dst_content s)]; under the taint, by the second from the
     loan untouched. *)
  Lemma union_hook_file (c : file_fixed) (k : nat) (r0 : file_names) (s : dst)
      (ls' : list fl_line) (n : nat) (Q : iProp Σ) :
    last ls' = Some FileDisc.LSync -> (n <= length ls')%nat ->
    fdeed r0 s -∗ fposh r0 n -∗ fl_lb c ls' -∗
    run_reg c (S k) (fn_pos r0) (fn_deed r0) -∗
    ((fdeed r0 s -∗ fposh r0 (length ls') -∗
        ∀ Ls : list srec, sl_lb (ff_hist c) (Ls ++ [(length ls', dst_content s)]) -∗ Q)
     ∧ (file_taint c -∗ fdeed r0 s -∗ fposh r0 n -∗ Q)) -∗
    union_hk file_pred c k Q.
  Proof using .
    intros Hlast Hn. iIntros "Hd Hpos #Hls' #Hrr0 Hk".
    rewrite /union_hk. iIntros (I r r') "%Hr %Hr' %Hrc Hg Hp Htk".
    iApply bupd_except_0_elim.
    iDestruct "Hg" as ">Hg". iDestruct "Hp" as ">Hp". iModIntro.
    (* THE TAINT, from any of its three sources: the loan untouched *)
    iDestruct "Htk" as "[#HT | Htk]".
    { iModIntro. iModIntro. iFrame "Hg Hp". iSplitR; [by iLeft |].
      iDestruct "Hk" as "[_ Hk]". iApply ("Hk" with "HT Hd Hpos"). }
    iEval (rewrite /file_pred) in "Hp".
    iDestruct "Hp" as "[#HT | (%Hpure & Hc & Hf & Hsy)]".
    { iModIntro. iModIntro. iFrame "Hg". iSplitR; [iNext; by iLeft |].
      iSplitL "Htk"; [by iRight |].
      iDestruct "Hk" as "[_ Hk]". iApply ("Hk" with "HT Hd Hpos"). }
    iEval (rewrite /file_pred) in "Hg".
    iDestruct "Hg" as "[#HT | (%Hpureg & Hcg & Hfg & Hsyg)]".
    { iModIntro. iModIntro. iSplitR; [iNext; by iLeft |].
      iSplitL "Hc Hf Hsy"; [iNext; iRight; iFrame (Hpure) "Hc Hf Hsy" |].
      iSplitL "Htk"; [by iRight |].
      iDestruct "Hk" as "[_ Hk]". iApply ("Hk" with "HT Hd Hpos"). }
    (* the guest is a COPY, so the running record is not one: the run-long
       history's full authority is the guest's *)
    iDestruct "Hsyg" as (lsg Lsg) "(#Hregg & #Hlbg & %Hchg & %Hwg & Hrog)".
    iEval (rewrite /sync_role Hrc) in "Hrog".
    iDestruct "Hrog" as "(Hgo & Hgcm & #Hgst & Hgh & Hgra)".
    iDestruct "Hsy" as (ls Ls) "(#Hreg & #Hlb & %Hch & %Hw & Hro)".
    destruct (fn_role r) eqn:Hrole.
    { iEval (rewrite /sync_role Hrole) in "Hro". iDestruct "Hro" as "(_ & _ & _ & Hh & _)".
      iDestruct (sl_auth_1_excl with "Hgh Hh") as %[]. }
    iEval (rewrite /sync_role Hrole) in "Hro".
    iDestruct "Hro" as "(Hq & #Hcml & Hpm & #Hrr)".
    (* THE REGISTRATION: the running record's position and deed are the
       holder's *)
    iEval (rewrite Hr) in "Hrr".
    iDestruct (run_reg_agree with "Hrr Hrr0") as %[Hpe Hde].
    iAssert (fdeed r s) with "[Hd]" as "Hd"; [rewrite /fdeed Hde; iExact "Hd" |].
    iDestruct "Hpos" as "[[%Hr0 Hp1] [_ Hp2]]".
    iAssert (fposh r n) with "[Hp1 Hp2]" as "Hpos".
    { rewrite /fposh /fpos /fposq /fposf Hpe. iSplitL "Hp1"; iFrame; by iPureIntro. }
    (* the deed reads the files *)
    iDestruct (f_state_deed_ok with "Hd Hf") as "(Hf & Hd & %Hok)".
    (* the position to the sync line's count, and the append *)
    iMod (sync_claim_advance c r (abs_view I) n (length ls') Hn with "[Hq Hpm] Hpos")
      as "[Hsy Hpos]".
    { iExists ls, Ls. iFrame "Hreg Hlb". iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. rewrite /sync_role Hrole Hr. iFrame "Hq Hcml Hpm Hrr". }
    iDestruct "Hsy" as (ls1 Ls1) "Hb".
    iDestruct "Hpos" as "[Hpf Hpq]".
    iMod (union_hook_closes c r' r (abs_view I) k ls1 Ls1 ls' (fcont_of (abs_view I))
            (length ls') Hrc Hr' Hrole Hr Hlast eq_refl eq_refl
            with "[Hgo Hgcm Hgh Hgra] Hb Htk Hls' Hpf")
      as "(Hsyg & Hsy & Htk & #Hnew & Hpf)".
    { iExists lsg, Lsg. iFrame "Hregg Hlbg". iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. rewrite /sync_role Hrc. iFrame "Hgo Hgcm Hgst Hgh Hgra". }
    iModIntro. iModIntro.
    iSplitL "Hcg Hfg Hsyg"; [iNext; iRight; iFrame (Hpureg) "Hcg Hfg Hsyg" |].
    iSplitL "Hc Hf Hsy"; [iNext; iRight; iFrame (Hpure) "Hc Hf Hsy" |].
    iSplitL "Htk"; [by iRight |].
    iDestruct "Hk" as "[Hk _]".
    iSpecialize ("Hk" with "[Hd] [Hpf Hpq]").
    { rewrite /fdeed -Hde. iExact "Hd". }
    { rewrite /fposh /fpos /fposq /fposf -Hpe.
      iDestruct "Hpf" as "[_ Hpf]". iDestruct "Hpq" as "[_ Hpq]".
      iSplitL "Hpf"; iFrame; by iPureIntro. }
    iApply ("Hk" $! Ls1).
    rewrite /fcont_of (f_ok_fcontent _ _ Hok). iExact "Hnew".
  Qed.
End FileClaim2.

(* ====================================================================== *)
(*  7a.  THE MERGE (sync SY3-A3bc, design 4.5 "The merge")                *)
(*                                                                        *)
(*  The commit's law at the era's token: the collection copies the running *)
(*  claim's files and console to fresh names (a COPY's record, era and list *)
(*  the running one's) and reads the running claim's sync witness, agreed   *)
(*  with the token's share; the wand, handed the old durable copy and the   *)
(*  loan, pins the old copy's era to the running one's (its counter against *)
(*  the token's lower bound, its started certificate against the loan), so  *)
(*  the registry names one list and the shares agree; the old copy's half  *)
(*  and counter move into the new copy.  Everything the old copy gives is   *)
(*  read UNDER its later (no update is needed), so the wand's basic update   *)
(*  never has to strip one.                                                *)
(* ====================================================================== *)
Section FileMerge.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !riscvFixedGS Σ}.

  Lemma file_merge (c : file_fixed) (gen : nat) :
    (forall n : nat, start_auth n ⊣⊢ sync_st_auth c n) ->
    ⊢ app_merge_raw (file_pred c) (file_ok c (S gen)) (fun r => fn_role r = true)
        (union_tk c gen) gen.
  Proof using .
    intros Hst. rewrite /app_merge_raw. iIntros "!>" (r av) "%Hok Hp HT".
    rewrite /file_ok in Hok.
    iDestruct (echo_xfer (ff_echo c)) as "#Hex". rewrite /app_xfer_raw.
    iAssert (▷ echo_pred (ff_echo c) (fn_cons r) av ∗ ▷ file_rest c r av)%I
      with "[Hp]" as "[He Hrest]".
    { rewrite -bi.later_sep. iNext. iApply (file_pred_split with "Hp"). }
    iMod ("Hex" $! (fn_cons r) av with "He") as "[He He']".
    iDestruct "He'" as (rc) "He'".
    iMod (fnames_alloc rc (fcontent_of av) (fn_sync r) (fn_era r) true 0)
      as (r') "(%Hrc & %Hsy' & Hd1 & _ & Ht1 & _ & Ha1 & _)".
    destruct Hsy' as (Hs' & He' & Hr').
    assert (Hok' : fn_era r' = S gen) by congruence.
    (* a TAINTED token: the new copy is tainted *)
    iDestruct "HT" as "[#HtT | HT]".
    { iModIntro. iSplitL "He Hrest".
      { iNext. iApply (file_pred_join with "He Hrest"). }
      iExists r'. iSplitR; [done |]. iSplitR; [done |].
      iSplit; [| by iLeft].
      iIntros (n ->) "Hsa _". iModIntro. iFrame "Hsa".
      iSplitR; [iNext; rewrite /file_pred; by iLeft | by iLeft]. }
    iDestruct "HT" as (γ Lt) "(#Hregt & Hqt & #Hcmt)".
    iEval (rewrite /file_rest) in "Hrest".
    iDestruct "Hrest" as "[#Htr | Hrest]".
    { (* the running claim is TAINTED: so is the new copy *)
      iModIntro. iSplitL "He".
      { iNext. iApply (file_pred_join with "He"). rewrite /file_rest. by iLeft. }
      iExists r'. iSplitR; [done |]. iSplitR; [done |].
      iSplit; last first.
      { iRight. iExists γ, Lt. iFrame "Hregt Hqt Hcmt". }
      iIntros (n ->) "Hsa _". iModIntro. iFrame "Hsa".
      iSplitR; [iNext; rewrite /file_pred; by iLeft |].
      iRight. iExists γ, Lt. iFrame "Hregt Hqt Hcmt". }
    iDestruct "Hrest" as "(#Hpure & Hf & Hsy)".
    iDestruct "Hsy" as (ls Ls) "(#Hreg & #Hlb & #Hch & #Hw & Hro)".
    (* the running claim's list is the token's *)
    iAssert (▷ ⌜fn_sync r = γ /\ Ls = Lt⌝ ∧ (▷ sync_role c r Ls ∗ sl_auth γ (1/4) Lt))%I
      with "[Hro Hqt]" as "[#Hag [Hro Hqt]]".
    { iSplit; [| iFrame "Hro Hqt"].
      iNext. rewrite Hok. iDestruct (sync_reg_agree with "Hreg Hregt") as %Hγ.
      rewrite /sync_role. rewrite Hγ.
      destruct (fn_role r).
      - iDestruct "Hro" as "(Ho & _)". iDestruct (sl_auth_agree with "Ho Hqt") as %->.
        by iPureIntro.
      - iDestruct "Hro" as "(Ho & _)". iDestruct (sl_auth_agree with "Ho Hqt") as %->.
        by iPureIntro. }
    iAssert (▷ (f_state c r av ∗ f_state c r' av))%I
      with "[Hf Ha1 Hd1 Ht1]" as "[Hf Hf']".
    { iNext. iApply (f_state_copy c r r' av with "Ha1 Hd1 Ht1 Hf"). }
    iModIntro. iSplitL "He Hf Hro".
    { iNext. iApply (file_pred_join with "He"). rewrite /file_rest. iRight.
      iFrame "Hpure Hf". iExists ls, Ls. iFrame "Hreg Hlb Hch Hw Hro". }
    iExists r'. iSplitR; [done |]. iSplitR; [done |].
    iSplit; last first.
    { iRight. iExists γ, Lt. iFrame "Hregt Hqt Hcmt". }
    (* THE WAND: the old durable copy *)
    iIntros (n ->) "Hsa Hold".
    iEval (rewrite Hst) in "Hsa".
    iDestruct "Hold" as (r_o av_o) "[#Hro_o Hold]".
    iEval (rewrite /file_pred) in "Hold".
    iDestruct "Hold" as "[#Hto | (_ & _ & _ & Hso)]".
    { iModIntro. iSplitR "Hqt Hsa"; [iNext; rewrite /file_pred; by iLeft |].
      iSplitL "Hqt"; [iRight; iExists γ, Lt; iFrame "Hregt Hqt Hcmt" |].
      rewrite Hst. iExact "Hsa". }
    iDestruct "Hso" as (ls_o Ls_o) "(#Hrego & _ & _ & _ & Hroo)".
    iAssert (▷ ⌜fn_era r_o = S gen /\ fn_sync r_o = γ /\ Ls_o = Lt⌝
             ∧ (▷ sync_role c r_o Ls_o ∗ sl_auth γ (1/4) Lt
                ∗ sync_st_auth c (gen + 1)))%I
      with "[Hroo Hqt Hsa]" as "[#Hag2 (Hroo & Hqt & Hsa)]".
    { iSplit; [| iFrame "Hroo Hqt Hsa"].
      iNext. iDestruct "Hro_o" as %Hro_o. rewrite /sync_role Hro_o.
      iDestruct "Hroo" as "(Ho & Hcmo & #Hsto & _)".
      rewrite /sync_cm_auth /sync_cm_lb /sync_st_lb /sync_st_auth.
      iDestruct (mono_nat_auth_lb_own_valid (mono_natG0 := fa_st) with "Hcmo Hcmt")
        as %[_ Hle1].
      iDestruct (mono_nat_auth_lb_own_valid (mono_natG0 := fa_st) with "Hsa Hsto")
        as %[_ Hle2].
      assert (He : fn_era r_o = S gen) by lia.
      rewrite He. iDestruct (sync_reg_agree with "Hrego Hregt") as %Hγ.
      rewrite Hγ. iDestruct (sl_auth_agree with "Ho Hqt") as %HL.
      by iPureIntro. }
    iModIntro. iSplitR "Hqt Hsa".
    { iNext. iDestruct "Hag" as %[Hγr HL]. iDestruct "Hag2" as %(Heo & Hγo & HL2).
      iDestruct "Hro_o" as %Hro_o. iDestruct "Hpure" as %Hpure.
      iDestruct "Hch" as %Hch. iDestruct "Hw" as %Hw.
      iApply (file_pred_join with "[He']"); [by rewrite Hrc |]. rewrite /file_rest.
      iRight. iSplitR; [done |]. iFrame "Hf'".
      iExists ls, Lt. rewrite /sync_body.
      rewrite Hs' Hok' Hγr Hok.
      iFrame "Hreg Hlb". subst Ls Lt. iSplitR; [done |]. iSplitR; [done |].
      rewrite /sync_role Hr' Hok' Hs'. rewrite /sync_role Hro_o Heo Hγo Hγr.
      iExact "Hroo". }
    iSplitL "Hqt"; [iRight; iExists γ, Lt; iFrame "Hregt Hqt Hcmt" |].
    rewrite Hst. iExact "Hsa".
  Qed.
End FileMerge.

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
    fdeed r s -∗ f_typed c s' -∗ sync_redir c r (dst_content s) (dst_content s') -∗
    app_step i I av'.
  Proof using .
    intros Heq Hpins Hab Hpr Hok. iIntros "Hd #Hty' Hre". rewrite /app_step.
    iIntros (n') "%Hav Hp". rewrite Heq. cbn [app_pred app_run app_names].
    rewrite Hav. iModIntro. iNext.
    iApply (file_step_park c r _ _ s s' Hpins Hab Hpr Hok with "Hd Hty' Hre Hp").
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
      (r : file_names) (s s' : dst) (n : nat) (I' : gmap Z fs_node) (E : coPset) :
    ↑appN ⊆ E ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    fcontent_of (abs_view I') = s' -> s <> s' ->
    app_inv γfs -∗ ftkt r s -∗ fposq r n -∗
    ghost_map_auth_frac (fs_top γfs) (1/2) I' ={E}=∗
      ghost_map_auth_frac (fs_top γfs) (1/2) I' ∗
      ((fown r s' ∗ fpos r n) ∨ (ftkt r s ∗ file_taint c)).
  Proof using .
    intros HE Heq Hcont Hne. iIntros "#Hinv Htk Hkq Hka".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf & Hsy)]".
    { (* TAINTED: the ticket comes back beside the taint *)
      iMod ("Hclose" with "[Hh]") as "_".
      { iNext. rewrite /app_body. iExists I'. iFrame "Hh".
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
    iDestruct "Hf" as (s0 s1 np) "(Hwh & Ht' & #Hty & %Hok & Hpq)".
    iDestruct (ftkt_agree with "Htk Ht'") as %<-.
    assert (Hs1 : s1 = s') by (rewrite -Hcont; symmetry; exact (f_ok_fcontent _ _ Hok)).
    subst s1.
    iMod (fdeed_whole_update r s s' with "Hwh") as "Hwh".
    iDestruct (fdeed_split with "Hwh") as "[Hd1 Hd2]".
    iMod (ftkt_update r s s s' with "Htk Ht'") as "[Htk Ht']".
    (* the parked quarter comes home beside the kept one *)
    iDestruct (fposq_join with "Hkq Hpq") as "Hpos".
    iMod ("Hclose" with "[Hh Hc Hw Hd2 Ht' Hsy]") as "_".
    { iNext. rewrite /app_body. iExists I'. iFrame "Hh".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names].
      iApply (file_pred_exact c r _ s' Hpins Hok with "Hc Hw Hd2 Ht' Hty Hsy"). }
    iModIntro. iFrame "Hka". iLeft. rewrite /fown. iFrame "Hd1 Htk Hpos".
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
    iDestruct "Hbody" as (I0) "(>Hka & Hp & >%Hdom)".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf & Hsy)]".
    { iMod ("Hclose" with "[Hka]") as "_".
      { iNext. rewrite /app_body. iExists I0. iFrame "Hka".
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
    { iDestruct "Hf" as (s0 s1 np) "(Hwh & _ & _ & _)".
      iDestruct (fdeed_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s0) "(Hd' & Htk' & #Hty & %Hok)".
    iDestruct (fdeed_agree with "Hd Hd'") as %<-.
    iDestruct (fdeed_join with "Hd Hd'") as "Hwh".
    iMod esc_alloc as (g) "Htok".
    rewrite /f_esc_wrap. iDestruct "Hwr" as (h) "[Ha #Hrec]".
    iMod (esc_auth_grow r h s g with "Ha") as "[Ha #Hwit]".
    iMod ("Hclose" with "[Hka Hc Ha Hwh Htk' Hsy]") as "_".
    { iNext. rewrite /app_body. iExists I0. iFrame "Hka".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
      iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc Hsy".
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
    iDestruct "Hbody" as (I0) "(>Hka & Hp & >%Hdom)".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf & Hsy)]".
    { iMod ("Hclose" with "[Hka]") as "_".
      { iNext. rewrite /app_body. iExists I0. iFrame "Hka".
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
    iMod ("Hclose" with "[Hka Hc Ha Hd2 Htk' Hsy]") as "_".
    { iNext. rewrite /app_body. iExists I0. iFrame "Hka".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names].
      iApply (file_pred_exact c r _ s Hpins Hok with "Hc [Ha] Hd2 Htk' Hty Hsy").
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
    esc_key c r n s g -∗ esc_tok g -∗ f_typed c s' -∗
    sync_redir c r (dst_content s) (dst_content s') -∗ app_step i I av'.
  Proof using .
    intros Heq Hpins Hab Hpr Hok. iIntros "#Hkey Htok #Hty' Hre".
    rewrite /app_step. iIntros (nd) "%Hav Hp".
    rewrite Heq. cbn [app_pred app_run app_names]. rewrite Hav.
    iDestruct "Hp" as ">Hp".
    iMod (file_escrow_step c r (abs_view I) av' n s s' g
            Hpins Hab Hpr Hok with "Hkey Htok Hty' Hre Hp") as "Hp".
    iModIntro. iNext. iExact "Hp".
  Qed.

  (* THE ROUND POSITION ADVANCES (sync SY3-A3bc, design 4.5 "The round
     position"): at a mask holding [appN], the deed holder's half and the
     claim's move together to a LATER count -- or the taint answers *)
  Lemma file_pos_advance (γfs : fs_names) (c : file_fixed) (r : file_names)
      (n n' : nat) (E : coPset) :
    ↑appN ⊆ E ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    (n <= n')%nat ->
    app_inv γfs -∗ fposh r n ={E}=∗ fposh r n' ∨ file_taint c.
  Proof using .
    intros HE Heq Hle. iIntros "#Hinv Hpos".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hka & Hp & >%Hdom)".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf & Hsy)]".
    { iMod ("Hclose" with "[Hka]") as "_".
      { iNext. rewrite /app_body. iExists I0. iFrame "Hka".
        iSplitL; [| by iPureIntro ].
        rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
        by iLeft. }
      iModIntro. by iRight. }
    iMod (sync_claim_advance c r _ n n' Hle with "Hsy Hpos") as "[Hsy Hpos]".
    iMod ("Hclose" with "[Hka Hc Hf Hsy]") as "_".
    { iNext. rewrite /app_body. iExists I0. iFrame "Hka".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. rewrite /file_pred.
      iRight. iFrame "Hc Hf Hsy". by iPureIntro. }
    iModIntro. by iLeft.
  Qed.

End FileClaimEra.
