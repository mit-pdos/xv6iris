(* FileOut.v -- THE FILE APPLICATION'S CONSOLE CLAIM, ITS TAG AND ITS LEDGER.

   Design of record: claude-notes/design/app-file.md section 4, deliverable
   2.  This is [EchoOut.v]'s twin at [FileDisc.sessf]: the same merged
   console claim over one [ConsLog.cons_hist], the same per-era authorities,
   the same ledger shape -- with the ERA'S BOOT FILE STATE added.  The echo
   files are NOT edited: every piece of ghost algebra this file needs
   ([EchoOut.era_pins], [turn], [cs_auth], [ps_auth], [Elist_auth],
   [dl_cnt], [ch_E] and its laws) is IMPORTED, and only what the file state
   adds is new.

   WHAT THE FILE ADDS, and where it lives.

   - ONE VALUE PER ERA.  The claim is [GenOut.gcl] at [file_lm], whose
     stage carries the state as an [option]: [None] until the era's first
     process byte files it, [Some s0] from then on; [GenOutPure.lm_out_pure]
     says [None] only ever occurs at the empty stage and that the state is a
     CONTENT ([FileDisc.fstate_ok]) -- the second is what the determinacy
     argument spends.  The file's state authority is the claim's one hook
     ([f0wa], [file_wa]).
   - A SECOND PER-ERA RECORD.  [EchoOut.era_pins] is not edited, so the
     boot state's [mono_list] gets its own gname in a record of its own
     ([file_era]) and its own per-era map, which the file ledger allocates
     beside [EchoOut]'s at power-on.  That map's authority needs a gname in
     the application's FIXED PART, and [AppFile.file_fixed] has none to
     spare -- so the RECORD's fixed part is [file_gn], AppFile's paired with
     that one gname.  Nothing in [AppFile.v] moves: every one of its lemmas
     is read at [fgn_cl g].
   - THE TYPED WITNESS.  The claim carries, beside the boot state, the deed's
     own evidence for it ([f0_typed]: a lower bound of the ledger's line list
     and the pure fact that the state is a chunk subset of one of its lines,
     or the taint).  The ledger's drain reads it against its own [fl_auth]
     and that is how [FileDisc.fadm_boot] is discharged.

   NOTHING IS TAKEN AS A HYPOTHESIS: the ledger's counter reads
   [FileDiscDec.disc_f_dec] (lane FILE-DEC).  Everything is closed. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import FileDisc.
Require Import FileDiscDec.   (* [disc_f_dec]: the ledger's counter *)
Require Import FileOutPure.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import FileHooks.        (* [file_hooks] *)
Require Import EchoOut.          (* the ghost algebra, [ch_E] and its laws *)
Require Import GenOutHist.
Require Import GenOut.           (* the claim once: [gcl] and its steps *)
Require Import AppEcho.          (* [echo_fixed] *)
Require Import AppFile.          (* [file_fixed], [fl_auth], [f_bytes_typed] *)
Local Open Scope list_scope.

(* the history of an entry of E *)
Local Notation ehist := (@fst (list mobs) (bv 8)).

(* ====================================================================== *)
(*  1.  WHAT THE READER KNOWS OF THE WRITER'S STAGE                        *)
(*                                                                        *)
(*  The claim's pure history layer is [GenOutHist]'s, at [file_lm]; what  *)
(*  stays here is the file's own name for the reader's stage fact, which  *)
(*  the link families read.                                               *)
(* ====================================================================== *)

(* WHAT THE CLAIM KNOWS OF THE WRITER'S STAGE at the input its log has
   echoed: [alts_pre] ties each entry to the line at its index. *)
Definition rd_stage_f (ps0 cs0 : list nat) (I : list (bv 8)) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps0
  /\ alts_pre I cs0
  /\ pro_pin_f ps0 cs0 I
  /\ (nlines (removelast I) <= length cs0)%nat.

Lemma rd_stage_f_lm ps0 cs0 s0 I : rd_stage_f ps0 cs0 I <-> lm_rd_stage file_lm ps0 cs0 s0 I.
Proof using.
  rewrite /rd_stage_f /lm_rd_stage.
  split; intros (H1 & H2 & H3 & H4).
  - split_and!; [exact H1 | exact H2 | by apply pro_pin_f_lm | exact H4].
  - split_and!; [exact H1 | exact H2 | by apply pro_pin_f_lm | exact H4].
Qed.

(* ====================================================================== *)
(*  2.  THE FIXED PART, AND THE SECOND PER-ERA RECORD                      *)
(*                                                                        *)
(*  [EchoOut.era_pins] is an echo file and is not edited, so the era's     *)
(*  boot state gets a record and a map of its own.  That map's AUTHORITY   *)
(*  needs a gname that outlives every era, and [AppFile.file_fixed] has    *)
(*  none to spare -- so the RECORD's fixed part is [file_gn], AppFile's    *)
(*  paired with it.  Nothing in [AppFile.v] moves: every one of its        *)
(*  definitions is read at [fgn_cl g].                                     *)
(* ====================================================================== *)

Record file_gn := MkFileGn {
  fgn_cl  : file_fixed;   (* AppFile's: the taint counter, the era map, the
                             line list *)
  fgn_era : gname;        (* ghost_map nat file_era: the era's BOOT STATE *)
}.

Definition fgn_echo (g : file_gn) : echo_fixed := fst (fgn_cl g).

Record file_era := MkFEra {
  fe_f0 : gname;   (* mono_list fstate: the era's BOOT STATE, filed by <init>
                      at its first instruction out of the deed it holds then
                      (RULING F0-BOOT): [] before, [s0] after; the persistent
                      witness [f0_bl] is the lower bound at [[s0]] *)
  fe_fl : gname;   (* mono_list fstate: [] until the era's FIRST PROCESS BYTE
                      files that state into the console claim, [s0] after;
                      its lower bound [f0_fd] is the writer's "filed" token *)
}.

Class fileOutG (Σ : gFunctors) := FileOutG {
  fog_era : ghost_mapG Σ nat file_era;
  fog_f0  : inG Σ (mono_listR (leibnizO fstate));
}.
#[global] Existing Instances fog_era fog_f0.

Definition fileOutΣ : gFunctors :=
  #[ ghost_mapΣ nat file_era; GFunctor (mono_listR (leibnizO fstate)) ].

Global Instance subG_fileOutΣ {Σ} : subG fileOutΣ Σ -> fileOutG Σ.
Proof. solve_inG. Qed.

(* the stage's [option fstate] as the monotone list sees it *)
Definition opt_list (f0 : option fstate) : list fstate :=
  match f0 with None => [] | Some s => [s] end.

Section file_out.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).

  (* ---- the era's BOOT-STATE ghost ---- *)

  Definition file_era_pin (k : nat) (v : file_era) : iProp Σ :=
    ghost_map_elem (fgn_era g) k DfracDiscarded v.

  Global Instance file_era_pin_persistent k v : Persistent (file_era_pin k v).
  Proof using . rewrite /file_era_pin. apply _. Qed.
  Global Instance file_era_pin_timeless k v : Timeless (file_era_pin k v).
  Proof using . rewrite /file_era_pin. apply _. Qed.

  Lemma file_era_pin_agree k v v' :
    file_era_pin k v -∗ file_era_pin k v' -∗ ⌜v = v'⌝.
  Proof using .
    rewrite /file_era_pin. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  (* THE BOOT LEDGER (RULING F0-BOOT): its authority rides in init's
     credential [fturn], and init files the boot state at boot. *)
  Definition f0_auth (v : file_era) (l : list fstate) : iProp Σ :=
    own (fe_f0 v) (●ML (l : list (leibnizO fstate))).
  Definition f0_bl (v : file_era) (s0 : fstate) : iProp Σ :=
    own (fe_f0 v) (◯ML ([s0] : list (leibnizO fstate))).

  (* THE FILED LEDGER: its authority lives in the console claim, and the
     era's first process byte files the (already decided) boot state. *)
  Definition f0f_auth (v : file_era) (l : list fstate) : iProp Σ :=
    own (fe_fl v) (●ML (l : list (leibnizO fstate))).
  Definition f0_fd (v : file_era) (s0 : fstate) : iProp Σ :=
    own (fe_fl v) (◯ML ([s0] : list (leibnizO fstate))).

  (* ...and what a WRITER carries past the era's first byte: the boot
     state, and that it is filed.  The reader's residue carries the boot
     half alone ([FileLinksLine.f0bw]), which is what exists at the head. *)
  Definition f0_lb (v : file_era) (s0 : fstate) : iProp Σ :=
    (f0_bl v s0 ∗ f0_fd v s0)%I.

  Global Instance f0_bl_persistent v s : Persistent (f0_bl v s).
  Proof using . rewrite /f0_bl. apply _. Qed.
  Global Instance f0_bl_timeless v s : Timeless (f0_bl v s).
  Proof using . rewrite /f0_bl. apply _. Qed.
  Global Instance f0_fd_persistent v s : Persistent (f0_fd v s).
  Proof using . rewrite /f0_fd. apply _. Qed.
  Global Instance f0_fd_timeless v s : Timeless (f0_fd v s).
  Proof using . rewrite /f0_fd. apply _. Qed.
  Global Instance f0f_auth_timeless v l : Timeless (f0f_auth v l).
  Proof using . rewrite /f0f_auth. apply _. Qed.

  Lemma f0_lb_bl (v : file_era) (s0 : fstate) : f0_lb v s0 -∗ f0_bl v s0.
  Proof using . rewrite /f0_lb. by iIntros "[$ _]". Qed.

  Global Instance f0_lb_persistent v s : Persistent (f0_lb v s).
  Proof using . rewrite /f0_lb. apply _. Qed.
  Global Instance f0_lb_timeless v s : Timeless (f0_lb v s).
  Proof using . rewrite /f0_lb. apply _. Qed.
  Global Instance f0_auth_timeless v l : Timeless (f0_auth v l).
  Proof using . rewrite /f0_auth. apply _. Qed.

  (* the lower bound READS the era's boot state: a one-element lower bound
     of a list of length at most one pins the list *)
  Lemma f0f_auth_lb_agree (v : file_era) (f0 : option fstate) (s : fstate) :
    f0f_auth v (opt_list f0) -∗ f0_fd v s -∗ ⌜f0 = Some s⌝.
  Proof using .
    rewrite /f0f_auth /f0_fd. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. destruct f0 as [s' |]; cbn [opt_list] in Hv.
    - destruct Hv as [z Hz]. destruct z as [| y z].
      + rewrite app_nil_r in Hz. by injection Hz as <-.
      + exfalso. apply (f_equal length) in Hz.
        rewrite length_app in Hz. cbn [length] in Hz. lia.
    - exfalso. by apply prefix_nil_inv in Hv.
  Qed.

  (* TWO LOWER BOUNDS OF THE ERA'S BOOT STATE AGREE, with no authority in
     hand: the era's list never grows past ONE entry, so two one-element
     lower bounds are comparable and hence equal.  This is what lets the
     ledger check a later drain's state against the one it fixed at the
     era's first. *)
  Lemma f0_bl_agree (v : file_era) (s s' : fstate) :
    f0_bl v s -∗ f0_bl v s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /f0_bl. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    destruct (mono_list_lb_op_valid_1_L _ _ Hv) as [[z Hz] | [z Hz]];
      (destruct z as [| y z];
       [ rewrite app_nil_r in Hz; by injection Hz as ->
       | exfalso; apply (f_equal length) in Hz;
         rewrite length_app in Hz; cbn [length] in Hz; lia ]).
  Qed.

  Lemma f0_lb_agree (v : file_era) (s s' : fstate) :
    f0_lb v s -∗ f0_lb v s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /f0_lb. iIntros "[H1 _] [H2 _]". iApply (f0_bl_agree with "H1 H2").
  Qed.

  Lemma f0f_lb_get (v : file_era) (s : fstate) :
    f0f_auth v [s] -∗ f0f_auth v [s] ∗ f0_fd v s.
  Proof using .
    rewrite /f0f_auth /f0_fd. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML ([s] : list (leibnizO fstate))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  (* INIT FILES THE BOOT STATE AT BOOT, once and for all; the authority is
     spent, since two lower bounds of a one-entry list agree on their own *)
  Lemma f0_file (v : file_era) (s : fstate) :
    f0_auth v [] ==∗ f0_bl v s.
  Proof using .
    rewrite /f0_auth /f0_bl. iIntros "Ha".
    iMod (own_update _ _ (●ML ([s] : list (leibnizO fstate))) with "Ha") as "Ha".
    { apply mono_list_update. by exists [s]. }
    iDestruct (own_mono _ _ (◯ML ([s] : list (leibnizO fstate))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iModIntro. iExact "Hb".
  Qed.

  (* THE ERA'S FIRST PROCESS BYTE FILES THAT STATE INTO THE CLAIM *)
  Lemma f0f_file (v : file_era) (s : fstate) :
    f0f_auth v [] ==∗ f0f_auth v [s] ∗ f0_fd v s.
  Proof using .
    rewrite /f0f_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ([s] : list (leibnizO fstate))) with "Ha") as "Ha".
    { apply mono_list_update. by exists [s]. }
    iModIntro. iApply (f0f_lb_get with "Ha").
  Qed.

  Lemma f0_alloc : ⊢ |==> ∃ v : file_era, f0_auth v [] ∗ f0f_auth v [].
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO fstate)))) as (gf) "Hf";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO fstate)))) as (gl) "Hl";
      [apply mono_list_auth_valid |].
    iModIntro. iExists (MkFEra gf gl). rewrite /f0_auth /fl_auth /=.
    iFrame "Hf Hl".
  Qed.

  (* THE CLAIM'S COPY OF THE BOOT WITNESS, deposited by the first byte, so
     that a read or a drain hands out the boot half beside the filed one *)
  Definition f0_wit (v : file_era) (f0 : option fstate) : iProp Σ :=
    match f0 with Some s => f0_bl v s | None => emp end.

  Global Instance f0_wit_persistent v f0 : Persistent (f0_wit v f0).
  Proof using . destruct f0; rewrite /f0_wit; apply _. Qed.
  Global Instance f0_wit_timeless v f0 : Timeless (f0_wit v f0).
  Proof using . destruct f0; rewrite /f0_wit; apply _. Qed.

  (* ---- THE TYPED WITNESS: what the deed's evidence for the era's boot
         state looks like once it is inside the claim ---- *)
  (* the state holds the deed's one file alone (cut W1 of
     claude-notes/design/filenames.md: the claim is at [f] until W2) *)
  Definition f0_typed (s : fstate) : iProp Σ :=
    (⌜forall N c, s !! N = Some c -> N = fname_m⌝
     ∗ match s !! fname_m with
       | None => emp
       | Some bs =>
           (∃ ls : list wordline, fl_lb (fgn_cl g) ls ∗ ⌜f_bytes_typed ls bs⌝)%I
       end)%I.

  Global Instance f0_typed_persistent s : Persistent (f0_typed s).
  Proof using . rewrite /f0_typed. case_match; apply _. Qed.
  Global Instance f0_typed_timeless s : Timeless (f0_typed s).
  Proof using . rewrite /f0_typed. case_match; apply _. Qed.

  Lemma f0_typed_none : ⊢ f0_typed ∅.
  Proof using .
    rewrite /f0_typed lookup_empty. iSplit; [| done].
    iPureIntro. intros N c Hc. by rewrite lookup_empty in Hc.
  Qed.

  (* the deed's typed witness, as the ledger's *)
  Lemma f0_typed_of_f_typed (s : dst) : f_typed (fgn_cl g) s -∗ f0_typed (dst_content s).
  Proof using .
    iIntros "Hty". destruct s as [[i bs] |]; cbn [dst_content fmap option_fmap option_map fst_of snd];
      [| iApply f0_typed_none].
    rewrite /f0_typed lookup_singleton. iSplit.
    - iPureIntro. intros N c Hc. by apply lookup_singleton_Some in Hc as [-> _].
    - iExact "Hty".
  Qed.

  (* ====================================================================== *)
  (*  3.  THE CLAIM, THE TAG AND THE TURN                                   *)
  (* ====================================================================== *)

  (* THE CLAIM IS [GenOut.gcl] AT THE FILE MODEL.  The application adds
     one thing to the generic claim, the STATE WITNESS'S AUTHORITY: the
     era's second record, the filed ledger's authority, the claim's copy of
     the boot witness and the deed's typed witness for that state
     ([f0wa]).  Under the taint there is nothing to say, as before. *)

  (* the writer's state witness, as the claim reads it: the era's second
     record and the boot state, filed *)
  Definition f0cw (k : nat) (s0 : fstate) : iProp Σ :=
    (∃ vf : file_era, file_era_pin k vf ∗ f0_lb vf s0)%I.

  Global Instance f0cw_persistent k s : Persistent (f0cw k s).
  Proof using . rewrite /f0cw. apply _. Qed.
  Global Instance f0cw_timeless k s : Timeless (f0cw k s).
  Proof using . rewrite /f0cw. apply _. Qed.

  Definition file_cparams : gen_cparams file_lm :=
    MkGCP file_lm file_lm_laws file_hooks (file_taint (fgn_cl g)) _ _
      (era_pin (fgn_echo g)) _ _ (era_pin_agree (fgn_echo g)) f0cw _ _.

  Definition f0wa (k : nat) (st : option fstate) : iProp Σ :=
    (∃ vf : file_era, file_era_pin k vf ∗ f0f_auth vf (opt_list st)
       ∗ f0_wit vf st ∗ f0_typed (default ∅ st))%I.

  Global Instance f0wa_timeless k st : Timeless (f0wa k st).
  Proof using . rewrite /f0wa. apply _. Qed.

  (* the boot evidence the era's first writer holds *)
  Definition f0boot (k : nat) (s0 : fstate) : iProp Σ :=
    (∃ vf : file_era, file_era_pin k vf ∗ f0_bl vf s0 ∗ f0_typed s0)%I.

  (* the writer's witness FILES the state: a filed lower bound pins the
     one-entry ledger *)
  Lemma f0wa_agree (k : nat) (st : option fstate) (s0 : fstate) :
    f0wa k st -∗ f0cw k s0 -∗ ⌜st = Some s0⌝.
  Proof using .
    iIntros "(%vf & #Hp & Ha & _ & _) (%vf' & #Hp' & [_ Hfd])".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0f_auth_lb_agree with "Ha Hfd").
  Qed.

  Lemma f0wa_agree_d (k : nat) (st : option fstate) (s0 : fstate) :
    f0wa k st -∗ f0cw k s0 -∗ ⌜default ∅ st = s0⌝.
  Proof using .
    iIntros "Ha Hw". by iDestruct (f0wa_agree with "Ha Hw") as %->.
  Qed.

  Lemma f0wa_W (k : nat) (s0 : fstate) :
    f0wa k (Some s0) -∗ f0wa k (Some s0) ∗ f0cw k s0 ∗ f0_typed s0.
  Proof using .
    iIntros "(%vf & #Hp & Ha & #Hw & #Hty)". cbn [opt_list default].
    iDestruct (f0f_lb_get with "Ha") as "[Ha #Hfd]".
    iSplitL "Ha"; [iExists vf; by iFrame "Hp Ha Hw Hty" |].
    iSplit; [| iExact "Hty"].
    iExists vf. iFrame "Hp". rewrite /f0_lb. iFrame "Hfd". iExact "Hw".
  Qed.

  Lemma f0wa_file (k : nat) (s0 : fstate) :
    f0wa k None -∗ f0boot k s0 ==∗ f0wa k (Some s0) ∗ f0cw k s0.
  Proof using .
    iIntros "(%vf & #Hp & Ha & _ & _) (%vf' & #Hp' & #Hbl & #Hty)".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-. cbn [opt_list].
    iMod (f0f_file vf s0 with "Ha") as "[Ha #Hfd]".
    iModIntro. iSplitL "Ha".
    - iExists vf. iFrame "Hp Ha". cbn [f0_wit default]. iFrame "Hbl Hty".
    - iExists vf. iFrame "Hp". rewrite /f0_lb. iFrame "Hbl Hfd".
  Qed.

  (* the file keeps no ledger of its process stream *)
  Lemma file_gext_grow (k : nat) (l : list (bv 8)) (b : bv 8) :
    (emp : iProp Σ) ==∗ emp.
  Proof using . by iIntros "_". Qed.

  Definition file_wa : gen_wa file_lm file_cparams ∅ :=
    @MkGWA Σ _ file_lm file_cparams ∅ f0wa _ f0wa_agree_d f0_typed _ f0wa_W
      f0boot f0wa_file True (fun _ => f0wa_agree)
      False (fun Hf => match Hf with end)
      (fun _ _ => emp%I) _ file_gext_grow.

  Definition fecl (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) : iProp Σ :=
    gcl file_lm file_cparams ∅ file_wa k ho H.

  Global Instance fecl_timeless k ho H : Timeless (fecl k ho H).
  Proof using . rewrite /fecl. apply _. Qed.

  (* THE LINE LIST the console has received, as a pure function of the
     history: the words of every complete [echo … > f] line, in order. *)
  Definition efl_of (h : list mobs) : list wordline := snd <$> echof_lines_of h.

  (* THE TAG: [EchoOut.etag] at the FILE discipline, with a lower bound of
     the ledger's line list beside it -- which is how a typed line reaches
     the child's create step. *)
  Definition ftag (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜disc_f h⌝ ∨ file_taint (fgn_cl g))
     ∗ fl_lb (fgn_cl g) (efl_of h))%I.

  Global Instance ftag_persistent h : Persistent (ftag h).
  Proof using . rewrite /ftag. apply _. Qed.
  Global Instance ftag_timeless h : Timeless (ftag h).
  Proof using . rewrite /ftag. apply _. Qed.

  (* THE CREDENTIAL INIT IS HANDED AT ITS ERA'S FIRST INSTRUCTION:
     [EchoOut.eturn] with the era's SECOND record beside its first, so that
     the first write can file the boot state. *)
  Definition fturn_core (k : nat) : iProp Σ :=
    (∃ (v : era_pins) (vf : file_era),
       era_pin (fgn_echo g) k v ∗ file_era_pin k vf
       ∗ turn v 0%nat ∗ dl_cnt v (1/2) 0%nat
       ∗ cs_lb v [] ∗ ps_lb v [] ∗ inp_lb v [])%I.

  (* ...WITH THE BOOT LEDGER'S AUTHORITY (RULING F0-BOOT): init files the
     era's boot state at its first instruction, out of the deed it holds
     then, and the writer's head and the reader's residue both carry the
     entry from there ([f0_bl]); the first process byte then only files
     it into the claim. *)
  Definition fturn (k : nat) : iProp Σ :=
    (∃ (v : era_pins) (vf : file_era),
       era_pin (fgn_echo g) k v ∗ file_era_pin k vf
       ∗ turn v 0%nat ∗ dl_cnt v (1/2) 0%nat
       ∗ cs_lb v [] ∗ ps_lb v [] ∗ inp_lb v []
       ∗ f0_auth vf [])%I.

  Global Instance fturn_core_timeless k : Timeless (fturn_core k).
  Proof using . rewrite /fturn_core. apply _. Qed.
  Global Instance fturn_timeless k : Timeless (fturn k).
  Proof using . rewrite /fturn. apply _. Qed.

  Lemma fturn_file (k : nat) (s0 : fstate) :
    fturn k ==∗
      fturn_core k ∗ ∃ vf : file_era, file_era_pin k vf ∗ f0_bl vf s0.
  Proof using .
    rewrite /fturn /fturn_core. iIntros "H".
    iDestruct "H" as (v vf) "(#Hpin & #Hfp & Ht & Hdl & #Hcs & #Hps & #HE & Hf0)".
    iMod (f0_file vf s0 with "Hf0") as "#Hbl".
    iModIntro. iSplitL.
    - iExists v, vf. iFrame "Hpin Hfp Ht Hdl Hcs Hps HE".
    - iExists vf. iFrame "Hfp Hbl".
  Qed.

  (* ====================================================================== *)
  (*  5.  THE LEDGER                                                        *)
  (*                                                                        *)
  (*  THE COUNTER IS AT [decide (FileDisc.disc_f h)].                       *)
  (*  [EchoOut.echo_led]'s taint counter is at [decide (EchoDisc.disc h)],  *)
  (*  and the file ledger's must be at [decide (FileDisc.disc_f h)]: the    *)
  (*  conclusion's antecedent is the FILE discipline, and [disc_f h] does   *)
  (*  not imply [disc h] (a [cat f] line is not an echo line), so echo's    *)
  (*  counter proves nothing here.  Only [al_rx] needs to DECIDE (every     *)
  (*  other step needs a [decide_ext] over one of [disc_f]'s closure laws), *)
  (*  and there the ledger must hand out the byte's tag, whose left arm IS  *)
  (*  the discipline.  The instance is [FileDiscDec.disc_f_dec], lane       *)
  (*  FILE-DEC: the per-cycle boot state, which [disc_f] quantifies over    *)
  (*  ALL byte lists, is canonicalised to a finite list read off the        *)
  (*  segment's own wire ([FileDiscDec.disc_seg_f'_canon]), and the rest of *)
  (*  the search ports from [EchoDisc.disc_seg'_dec].  So this file takes   *)
  (*  NO hypothesis of its own.                                            *)
  (* ====================================================================== *)

  (* the SECOND per-era map, beside [EchoOut.pin_map] *)
  Definition f0_map (h : list mobs) : iProp Σ :=
    (∃ Mf : gmap nat file_era,
       ghost_map_auth (fgn_era g) 1 Mf ∗ ⌜pin_dom Mf (obs_boots h)⌝)%I.

  Global Instance f0_map_timeless h : Timeless (f0_map h).
  Proof using . rewrite /f0_map. apply _. Qed.

  Lemma f0_map_step (h : list mobs) (e : mobs) :
    obs_boots [e] = 0%nat -> f0_map h -∗ f0_map (h ++ [e]).
  Proof using .
    intros He. rewrite /f0_map obs_boots_app He Nat.add_0_r. by iIntros "$".
  Qed.

  Lemma f0_map_on (h : list mobs) (vf : file_era) :
    f0_map h ==∗
      f0_map (h ++ [ObsPowerOn]) ∗ file_era_pin (S (obs_boots h)) vf.
  Proof using .
    rewrite /f0_map /file_era_pin obs_boots_app. cbn [obs_boots].
    rewrite Nat.add_1_r.
    iIntros "H". iDestruct "H" as (Mf) "[Hm %Hd]".
    iMod (ghost_map_insert_persist (S (obs_boots h)) vf
            (pin_dom_absent _ _ Hd) with "Hm") as "[Hm #Hpin]".
    iModIntro. iFrame "Hpin". iExists _. iFrame "Hm".
    iPureIntro. by apply pin_dom_insert.
  Qed.

  (* ---- the history's own line list moves ---- *)

  Lemma echof_lines_of_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> ins [e] = [] ->
    echof_lines_of (h ++ [e]) = echof_lines_of h.
  Proof using .
    intros Hsh Hio Hin.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite /echof_lines_of H1 H2 !fmap_app !concat_app.
    f_equal. cbn [fmap list_fmap concat].
    rewrite /echof_cyc ins_app Hin (app_nil_r (ins (open_seg h))).
    reflexivity.
  Qed.

  Lemma efl_of_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> ins [e] = [] ->
    efl_of (h ++ [e]) = efl_of h.
  Proof using . intros Hsh Hio Hin. by rewrite /efl_of echof_lines_of_io. Qed.

  Lemma efl_of_out (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true -> efl_of (h ++ [ObsUartOut i b]) = efl_of h.
  Proof using .
    intros Hsh. apply efl_of_io; [exact Hsh | by destruct i | by destruct i].
  Qed.

  Lemma echof_lines_of_out (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true -> echof_lines_of (h ++ [ObsUartOut i b]) = echof_lines_of h.
  Proof using .
    intros Hsh. apply echof_lines_of_io; [exact Hsh | by destruct i | by destruct i].
  Qed.

  Lemma efl_of_snoc (h : list mobs) (e : mobs) : efl_of h `prefix_of` efl_of (h ++ [e]).
  Proof using .
    destruct (echof_lines_of_snoc h e) as [z Hz]. exists (snd <$> z).
    by rewrite /efl_of Hz fmap_app.
  Qed.

  Lemma echof_lines_of_power (h : list mobs) (on : bool) :
    echof_lines_of (h ++ [if on then ObsPowerOff else ObsPowerOn]) = echof_lines_of h.
  Proof using .
    rewrite /echof_lines_of. destruct on.
    - by rewrite cycles_of_off.
    - rewrite cycles_of_on fmap_app concat_app.
      cbn [fmap list_fmap concat]. rewrite /echof_cyc.
      rewrite (_ : ins [] = []); [| reflexivity].
      rewrite /echof_lines_in /lines_of bodies_of_nil fmap_nil.
      by rewrite !app_nil_r.
  Qed.

  Lemma efl_of_power (h : list mobs) (on : bool) :
    efl_of (h ++ [if on then ObsPowerOff else ObsPowerOn]) = efl_of h.
  Proof using . by rewrite /efl_of echof_lines_of_power. Qed.


  (* ---- THE ERA'S PIN IN THE LEDGER.
         The OPEN cycle's entry of [s0s] is PROVISIONAL until the era's
         first drain: [None] is admissible against any line set and an
         empty cycle is [good_out_f] at any state, so the power step parks
         [None] there and the first drain REPLACES it.  What makes the
         replacement sound is that from that drain on the ledger keeps the
         drain's own LOWER BOUND of the era's boot state, so every later
         drain of the same era hands back the same state ([f0_lb_agree]).
         The condition -- has this cycle put anything on the console's
         wire? -- is PURE and reads the history alone. ---- *)
  Definition f0_pinned (h : list mobs) (s0s : list fstate) : iProp Σ :=
    (if decide (obs_wire Uart0 (open_seg h) = [])
     then emp
     else ∃ (vf : file_era) (s0 : fstate),
            ⌜exists u1, s0s = u1 ++ [s0]⌝ ∗ file_era_pin (obs_boots h) vf
            ∗ f0_lb vf s0)%I.

  Global Instance f0_pinned_persistent h s0s : Persistent (f0_pinned h s0s).
  Proof using . rewrite /f0_pinned. case_decide; apply _. Qed.
  Global Instance f0_pinned_timeless h s0s : Timeless (f0_pinned h s0s).
  Proof using . rewrite /f0_pinned. case_decide; apply _. Qed.

  (* before the era's first drain there is nothing to keep *)
  Lemma f0_pinned_undrained (h : list mobs) (s0s : list fstate) :
    obs_wire Uart0 (open_seg h) = [] -> ⊢ f0_pinned h s0s.
  Proof using .
    intro Hw. rewrite /f0_pinned decide_True; [| exact Hw]. by iIntros "".
  Qed.

  (* an event that puts nothing on the console's wire moves neither the
     condition nor the era *)
  Lemma f0_pinned_io (h : list mobs) (e : mobs) (s0s : list fstate) :
    is_io e = true -> obs_wire Uart0 [e] = [] ->
    f0_pinned h s0s -∗ f0_pinned (h ++ [e]) s0s.
  Proof using .
    intros Hio Hw. rewrite /f0_pinned.
    rewrite (open_seg_io h [e] (proj2 (Forall_singleton _ _) Hio)).
    rewrite obs_wire_app Hw app_nil_r.
    rewrite obs_boots_app (obs_boots_io [e] (proj2 (Forall_singleton _ _) Hio)).
    rewrite Nat.add_0_r. by iIntros "$".
  Qed.

  (* ...and the drain's two halves: reading the state the ledger fixed, and
     fixing it *)
  Lemma f0_pinned_drained (h : list mobs) (s0s : list fstate) (vf : file_era)
      (s0 : fstate) :
    obs_wire Uart0 (open_seg h) <> [] ->
    file_era_pin (obs_boots h) vf -∗ f0_lb vf s0 -∗ f0_pinned h s0s -∗
      ⌜exists u1, s0s = u1 ++ [s0]⌝.
  Proof using .
    intro Hw. rewrite /f0_pinned decide_False; [| exact Hw].
    iIntros "#Hfp #Hlb Hp".
    iDestruct "Hp" as (vf' s0') "(%Hl & #Hfp' & #Hlb')".
    iDestruct (file_era_pin_agree with "Hfp Hfp'") as %<-.
    iDestruct (f0_lb_agree with "Hlb Hlb'") as %<-.
    by iPureIntro.
  Qed.

  Lemma f0_pinned_drain (h : list mobs) (b : bv 8) (u1 : list fstate)
      (vf : file_era) (s0 : fstate) :
    file_era_pin (obs_boots h) vf -∗ f0_lb vf s0 -∗
      f0_pinned (h ++ [ObsUartOut Uart0 b]) (u1 ++ [s0]).
  Proof using .
    iIntros "#Hfp #Hlb". rewrite /f0_pinned.
    rewrite obs_boots_app
      (obs_boots_io [ObsUartOut Uart0 b]
         (proj2 (Forall_singleton _ _)
            (eq_refl : is_io (ObsUartOut Uart0 b) = true))) Nat.add_0_r.
    rewrite (open_seg_io h [ObsUartOut Uart0 b]
               (proj2 (Forall_singleton _ _)
                  (eq_refl : is_io (ObsUartOut Uart0 b) = true))).
    rewrite decide_False; last first.
    { rewrite obs_wire_app (_ : obs_wire Uart0 [ObsUartOut Uart0 b] = [b]);
        [| reflexivity].
      intros Hz. apply (f_equal length) in Hz.
      rewrite length_app in Hz. cbn [length] in Hz. lia. }
    iExists vf, s0. iFrame "Hfp Hlb". iPureIntro. by exists u1.
  Qed.

  (* the birth's yield *)
  Definition file_cl_all : iProp Σ :=
    (file_cl (fgn_cl g)
     ∗ ghost_map_auth (fgn_era g) 1 (∅ : gmap nat file_era))%I.


  (* the deed's typed witness, read against the ledger's own line list *)
  Lemma f0_typed_adm (Lp : list (list (bv 8) * wordline)) (s0 : fstate) :
    Forall (fun p => uname p.1) Lp ->
    fl_auth (fgn_cl g) (snd <$> Lp) -∗ f0_typed s0 -∗
      fl_auth (fgn_cl g) (snd <$> Lp) ∗ ⌜fadm_boot Lp s0⌝.
  Proof using .
    intros HN. iIntros "Ha [%Hdom Hty]".
    rewrite (fst_of_dom s0 Hdom).
    change fname_f with fname_m.
    destruct (s0 !! fname_m) as [bs |]; last first.
    { iFrame "Ha". iPureIntro. apply fadm_boot_fst_of; [exact HN | by left]. }
    iDestruct "Hty" as (ls) "[Hlb %Hbt]".
    iDestruct (fl_lb_prefix with "Ha Hlb") as %Hpre.
    iFrame "Ha". iPureIntro. apply fadm_boot_fst_of; [exact HN |]. right.
    destruct (f_bytes_typed_mono ls _ bs Hpre Hbt)
      as (ws & sel & Hin & _ & Hsel & ->).
    by exists ws, sel.
  Qed.

  (* the line list grows by whatever the new input completed *)
  Lemma fl_auth_grow_pre (ls ls' : list wordline) :
    ls `prefix_of` ls' ->
    fl_auth (fgn_cl g) ls ==∗
      fl_auth (fgn_cl g) ls' ∗ fl_lb (fgn_cl g) ls'.
  Proof using .
    intros Hp. rewrite /f0f_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML (ls' : list (leibnizO wordline))) with "Ha")
      as "Ha".
    { apply mono_list_update. by destruct Hp as [z ->]; exists z. }
    iModIntro. iApply (fl_auth_lb with "Ha").
  Qed.

End file_out.

(* ====================================================================== *)
(*  6.  THE BIRTH STEP                                                     *)
(*                                                                        *)
(*  [AppFile.file_birth] beside one more [ghost_map_alloc]: the record's   *)
(*  fixed part is AppFile's paired with the file era map's gname.          *)
(* ====================================================================== *)
Section file_birth.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  Lemma file_birth_all : ⊢ |==> ∃ g : file_gn, file_cl_all g.
  Proof using .
    iMod file_birth as (c) "Hc".
    iMod (ghost_map_alloc (∅ : gmap nat file_era)) as (ge) "[Hm _]".
    iModIntro. iExists (MkFileGn c ge). rewrite /file_cl_all /=.
    iFrame "Hc Hm".
  Qed.
End file_birth.
