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

Lemma rd_stage_f_0 : rd_stage_f [] [] [].
Proof using.
  rewrite /rd_stage_f. split_and!.
  - constructor.
  - apply alts_pre_nil.
  - intros q Hq. rewrite nstarted_nil in Hq. lia.
  - cbn [removelast]. rewrite nlines_nil. cbn [length]. lia.
Qed.

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
  Definition f0_typed (s : fstate) : iProp Σ :=
    match s with
    | None => emp
    | Some bs =>
        (∃ ls : list wordline, fl_lb (fgn_cl g) ls ∗ ⌜f_bytes_typed ls bs⌝)%I
    end.

  Global Instance f0_typed_persistent s : Persistent (f0_typed s).
  Proof using . destruct s as [bs |]; rewrite /f0_typed; apply _. Qed.
  Global Instance f0_typed_timeless s : Timeless (f0_typed s).
  Proof using . destruct s as [bs |]; rewrite /f0_typed; apply _. Qed.

  Lemma f0_typed_none : ⊢ f0_typed None.
  Proof using . by rewrite /f0_typed. Qed.

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
       ∗ f0_wit vf st ∗ f0_typed (default None st))%I.

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
    f0wa k st -∗ f0cw k s0 -∗ ⌜default None st = s0⌝.
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

  Definition file_wa : gen_wa file_lm file_cparams None :=
    @MkGWA Σ _ file_lm file_cparams None f0wa _ f0wa_agree_d f0_typed _ f0wa_W
      f0boot f0wa_file True (fun _ => f0wa_agree)
      False (fun Hf => match Hf with end)
      (fun _ _ => emp%I) _ file_gext_grow.

  Definition fecl (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) : iProp Σ :=
    gcl file_lm file_cparams None file_wa k ho H.

  Global Instance fecl_timeless k ho H : Timeless (fecl k ho H).
  Proof using . rewrite /fecl. apply _. Qed.

  (* THE LINE LIST the console has received, as a pure function of the
     history: the words of every complete [echo … > f] line, in order. *)
  Definition efl_of (h : list mobs) : list wordline := echof_lines_of h.

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
  (*  4.  THE STEPS OUTSIDE THE LINKS: [GenOut]'s, in the file's words.     *)
  (*  The writes, the read, the close and the byte are spent at the       *)
  (*  console contracts directly ([GenLinks] at this instance, from       *)
  (*  [FileLinks]); what stays is the echo shift's open, the taint's      *)
  (*  supply and the ledger's drain.                                      *)
  (* ====================================================================== *)

  Lemma fecl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    disc_seg_f (open_seg h) -> obs_boots h = k ->
    disc_f h -> trace_shape h true ->
    fecl k ho H -∗ fecl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh.
    exact (gcl_open file_lm file_cparams file_lm_byte_laws None file_wa k ho H
             h c cs Hok Hev Hd Hb (proj1 (disc_f_lm h) Hdh) Hsh).
  Qed.

  Lemma fecl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    file_taint (fgn_cl g) -∗ fecl k ho H ==∗ fecl k ho (ConsLog.cons_step H ev).
  Proof using . exact (gcl_sup file_lm file_cparams None file_wa k ho H ev). Qed.

  (* WHAT THE DRAIN HANDS THE LEDGER: the trace fact at the era's own boot
     state, that state's deed witness, the era pin and a lower bound of the
     state ([GenOut.gdrain_ret] at the file) *)
  Definition fdrain_ret (k : nat) (seg : list mobs) : iProp Σ :=
    (file_taint (fgn_cl g)
     ∨ ∃ (s0 : fstate) (vf : file_era),
         ⌜good_out_f s0 seg⌝ ∗ ⌜fstate_ok s0⌝ ∗ f0_typed s0
         ∗ file_era_pin k vf ∗ f0_lb vf s0)%I.

  Lemma fecl_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    fecl k ho CH -∗ fecl k ho CH ∗ fdrain_ret k seg.
  Proof using .
    intros Hsh Hk Hpre Hins Hwire Hne. iIntros "Hcl".
    iDestruct (gcl_drain file_lm file_cparams file_lm_byte_laws None file_wa
                 k h ho CH seg Hsh Hk Hpre Hins Hwire Hne with "Hcl") as "[$ Hd]".
    rewrite /fdrain_ret.
    iDestruct "Hd" as "[#HT | (%s0 & %Hgo & %Hok & #Hty & #Hw)]"; [by iLeft |].
    iRight. iDestruct "Hw" as (vf) "[#Hfp #Hlb]".
    iExists s0, vf. iFrame "Hty Hfp Hlb". iPureIntro.
    split; [by apply good_out_f_lm | exact Hok].
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

  Lemma efl_of_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> ins [e] = [] ->
    efl_of (h ++ [e]) = efl_of h.
  Proof using .
    intros Hsh Hio Hin.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite /efl_of /echof_lines_of H1 H2 !fmap_app !concat_app.
    f_equal. cbn [fmap list_fmap concat].
    rewrite /echof_cyc ins_app Hin (app_nil_r (ins (open_seg h))).
    reflexivity.
  Qed.

  Lemma efl_of_out (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true -> efl_of (h ++ [ObsUartOut i b]) = efl_of h.
  Proof using .
    intros Hsh. apply efl_of_io; [exact Hsh | by destruct i | by destruct i].
  Qed.

  Lemma efl_of_power (h : list mobs) (on : bool) :
    efl_of (h ++ [if on then ObsPowerOff else ObsPowerOn]) = efl_of h.
  Proof using .
    rewrite /efl_of /echof_lines_of. destruct on.
    - by rewrite cycles_of_off.
    - rewrite cycles_of_on fmap_app concat_app.
      cbn [fmap list_fmap concat]. rewrite /echof_cyc.
      rewrite (_ : ins [] = []); [| reflexivity].
      rewrite /echof_lines_in /lines_of bodies_of_nil fmap_nil.
      by rewrite !app_nil_r.
  Qed.

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

  (* ---- THE CONCLUSION'S PURE CARRIER.
         [FileDisc.file_phi] VERBATIM, its antecedent included: that is what
         lets the era's boot state be fixed at the era's FIRST drain, where
         the cycle has typed nothing ([FileOutPure.efl_of_first_out]).
         [disc_f] is prefix-closed, so every step below
         assumes the NEW history's discipline and reads the old one's
         witnesses off it. ---- *)
  Definition file_phi_res (h : list mobs) : iProp Σ :=
    (∃ s0s : list fstate,
       ⌜disc_f h -> file_phi_body h s0s⌝ ∗ f0_pinned h s0s)%I.

  Global Instance file_phi_res_timeless h : Timeless (file_phi_res h).
  Proof using . rewrite /file_phi_res. apply _. Qed.

  (* ...AND THE WHOLE LEDGER, which is what the record's [app_R] becomes. *)
  Definition file_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint (fgn_echo g)) 1
       (if decide (disc_f h) then 0%nat else 1%nat)
     ∗ pin_map (fgn_echo g) h
     ∗ f0_map h
     ∗ fl_auth (fgn_cl g) (efl_of h)
     ∗ (file_phi_res h ∨ file_taint (fgn_cl g)))%I.

  Global Instance file_led_timeless h : Timeless (file_led h).
  Proof using . rewrite /file_led. apply _. Qed.

  (* the birth's yield *)
  Definition file_cl_all : iProp Σ :=
    (file_cl (fgn_cl g)
     ∗ ghost_map_auth (fgn_era g) 1 (∅ : gmap nat file_era))%I.

  Lemma file_led_init : file_cl_all -∗ file_led [].
  Proof using .
    rewrite /file_cl_all /file_cl /echo_cl /file_led /pin_map /f0_map.
    iIntros "[[[Ht Hm] Hfl] Hmf]".
    rewrite decide_True; [| exact disc_f_nil].
    rewrite (_ : efl_of [] = []); last first.
    { rewrite /efl_of /echof_lines_of /cycles_of /cycles_rev /=. reflexivity. }
    iFrame "Ht Hfl".
    iSplitL "Hm"; [iExists ∅; iFrame "Hm"; iPureIntro; apply pin_dom_empty |].
    iSplitL "Hmf"; [iExists ∅; iFrame "Hmf"; iPureIntro; apply pin_dom_empty |].
    iLeft. iExists []. iSplitR.
    { iPureIntro. intros _. exact file_phi_body_nil. }
    iApply f0_pinned_undrained. reflexivity.
  Qed.


  (* ---- THE FOUNDING, as a resource split: the era's ghosts become the
         port's claim at the start of their era and init's credential ---- *)
  Lemma file_era_split (k : nat) (v : era_pins) (vf : file_era) :
    era_pin (fgn_echo g) k v -∗ file_era_pin k vf -∗
    era_full v -∗ f0_auth vf [] -∗ f0f_auth vf [] -∗
      fecl k [] (LogEntryDefs.MkCH [] [] [] None) ∗ fturn k.
  Proof using .
    iIntros "#Hpin #Hfp (Ht & Hcs & Hps & HE & Hdl & Hdll) Hf0 Hfla".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct "Ht" as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (dl_list_lb_get with "Hdll") as "[Hdll #Hdllb]".
    iSplitL "Ht1 Hcs Hps HE Hdl1 Hdll Hfla".
    { rewrite /fecl /gcl. iRight. iExists v, (gstage0 file_lm).
      cbn [gs_ps gs_cs gs_E gs_w gs_st gstage0 LogEntryDefs.ch_dl length].
      rewrite (_ : lm_pcount file_lm [] [] (gs_state file_lm None (gstage0 file_lm))
                     [] [] = 0%nat); [| reflexivity].
      iFrame "Hpin Ht1 Hcs Hps HE Hdl1 Hdll".
      iSplitL "Hfla".
      { iExists vf. iFrame "Hfp Hfla". cbn [f0_wit default f0_typed]. done. }
      iPureIntro.
      rewrite /gcl_pure.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      split_and!.
      - exact (lm_out_pure_0 file_lm None k [] I).
      - exact (lm_cs_len_ok_0 file_lm).
      - exact (lm_ps_len_ok_0 file_lm None).
      - exact (gin_pure_0 file_lm k).
      - by rewrite /garm_era.
      - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
        rewrite app_nil_r echoed_nil /seg_of fmap_nil. reflexivity.
      - exact (lm_dl_ok_0 file_lm). }
    rewrite /fturn. iExists v, vf. iFrame "Hpin Hfp Ht2 Hdl2 Hcslb Hpslb Hf0".
    iApply (inp_lb_of_dl_lb v [] []); [apply prefix_nil | iExact "Hdllb"].
  Qed.

  (* THE POWER STEP: the on-arm allocates BOTH per-era records, mints both
     pins, and splits the ghosts into the era's claim and init's credential. *)
  Lemma file_led_pow (h : list mobs) (on : bool) :
    file_led h ==∗
      file_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else fecl (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)
              ∗ fturn (S (obs_boots h))).
  Proof using .
    iIntros "(Ht & Hpm & Hfm & Hfl & Hphi)". rewrite /file_led.
    rewrite (decide_ext _ (disc_f h) 0%nat 1%nat (disc_f_power h on)).
    rewrite (efl_of_power h on).
    destruct on.
    - iDestruct (pin_map_step (fgn_echo g) h ObsPowerOff eq_refl with "Hpm")
        as "Hpm".
      iDestruct (f0_map_step h ObsPowerOff eq_refl with "Hfm") as "Hfm".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm Hfm Hfl".
      iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
      iLeft. iDestruct "Hphi" as (s0s) "[%Hb _]". iExists s0s. iSplitR.
      { iPureIntro. intros Hd.
        exact (file_phi_body_off h s0s
                 (Hb (proj1 (disc_f_power h true) Hd))). }
      iApply f0_pinned_undrained.
      by rewrite (open_seg_power h ObsPowerOff eq_refl).
    - iMod era_full_alloc as (v) "Hfull".
      iMod f0_alloc as (vf) "[Hf0 Hfla]".
      iMod (pin_map_on (fgn_echo g) h v with "Hpm") as "[Hpm #Hpin]".
      iMod (f0_map_on h vf with "Hfm") as "[Hfm #Hfp]".
      iDestruct (file_era_split (S (obs_boots h)) v vf
                   with "Hpin Hfp Hfull Hf0 Hfla") as "(Hcl & Hturn)".
      iModIntro. iSplitR "Hcl Hturn".
      + iFrame "Ht Hpm Hfm Hfl".
        iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
        iLeft. iDestruct "Hphi" as (s0s) "[%Hb _]".
        iExists (s0s ++ [None]). iSplitR.
        { iPureIntro. intros Hd.
          exact (file_phi_body_on h s0s
                   (Hb (proj1 (disc_f_power h false) Hd))). }
        iApply f0_pinned_undrained.
        by rewrite (open_seg_power h ObsPowerOn eq_refl).
      + iFrame "Hcl Hturn".
  Qed.


  (* the deed's typed witness, read against the ledger's own line list *)
  Lemma f0_typed_adm (Ls : list wordline) (s0 : fstate) :
    fl_auth (fgn_cl g) Ls -∗ f0_typed s0 -∗
      fl_auth (fgn_cl g) Ls ∗ ⌜fadm_boot Ls s0⌝.
  Proof using .
    iIntros "Ha Hty". destruct s0 as [bs |]; last first.
    { iFrame "Ha". iPureIntro. by left. }
    rewrite /f0_typed. iDestruct "Hty" as (ls) "[Hlb %Hbt]".
    iDestruct (fl_lb_prefix with "Ha Hlb") as %Hpre.
    iFrame "Ha". iPureIntro. right.
    destruct (f_bytes_typed_mono ls Ls bs Hpre Hbt)
      as (ws & sel & Hin & _ & Hsel & ->).
    by exists ws, sel.
  Qed.

  (* THE OUTPUT STEP, AND THE ERA'S FIRST DRAIN.
     The drain hands over the era's boot state [s0], its deed witness, and
     a LOWER BOUND of the state pinned to the era's record.  If the cycle
     has not yet put a byte on the console's wire then this is the era's
     FIRST drain: the entry the ledger parked at the power step was
     provisional, and it is replaced by [s0] -- whose admissibility comes
     out of the witness read against the ledger's own line list, which at
     that moment IS the list of lines typed in strictly earlier cycles
     ([FileOutPure.efl_of_first_out]; at cycle 0 that list is empty and the
     same reading refutes [f0_typed]'s [Some] arm, which is
     [FileDisc.file_phi]'s guarded first clause).  If the cycle HAS
     drained, the handed bound agrees with the one already kept
     ([f0_pinned_drained]), so the entry does not move and the body simply
     extends by the drain's own [good_out_f]. *)
  Lemma file_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (file_taint (fgn_cl g)
     ∨ (match i with
        | Uart0 => ∃ (s0 : fstate) (vf : file_era),
                     ⌜good_out_f s0 (open_seg h ++ [ObsUartOut Uart0 b])⌝
                     ∗ f0_typed s0 ∗ file_era_pin (obs_boots h) vf
                     ∗ f0_lb vf s0
        | _ => True
        end)) -∗
    file_led h ==∗ file_led (h ++ [ObsUartOut i b]).
  Proof using .
    intros Hsh. iIntros "Hgo (Ht & Hpm & Hfm & Hfl & Hphi)".
    iDestruct (pin_map_step (fgn_echo g) h (ObsUartOut i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step h (ObsUartOut i b) eq_refl with "Hfm") as "Hfm".
    rewrite /file_led.
    rewrite (decide_ext _ (disc_f h) 0%nat 1%nat (disc_f_out h i b Hsh)).
    rewrite (efl_of_out h i b Hsh).
    iFrame "Ht Hpm Hfm".
    iDestruct "Hphi" as "[Hphi | HT]"; last first.
    { iModIntro. iFrame "Hfl". by iRight. }
    iDestruct "Hphi" as (s0s) "[%Hb #Hpin0]".
    destruct i; last first.
    { iModIntro. iFrame "Hfl". iLeft. iExists s0s. iSplitR.
      { iPureIntro. intros Hd.
        apply (file_phi_body_step_io h (ObsUartOut Uart1 b) s0s Hsh eq_refl
                 eq_refl), Hb.
        exact (proj1 (disc_f_out h Uart1 b Hsh) Hd). }
      iApply (f0_pinned_io h (ObsUartOut Uart1 b) s0s eq_refl eq_refl
                with "Hpin0"). }
    iDestruct "Hgo" as "[#HT | Hgo]".
    { iModIntro. iFrame "Hfl". by iRight. }
    iDestruct "Hgo" as (s0 vf) "(%Hgo & #Hty & #Hfp & #Hlb)".
    iDestruct (f0_typed_adm (efl_of h) s0 with "Hfl Hty") as "[Hfl %Hadm]".
    iAssert (⌜obs_wire Uart0 (open_seg h) <> [] ->
               exists u1, s0s = u1 ++ [s0]⌝)%I as "%Hlast".
    { destruct (decide (obs_wire Uart0 (open_seg h) = [])) as [Hw | Hw].
      - iPureIntro. intro Hne. by destruct (Hne Hw).
      - iDestruct (f0_pinned_drained h s0s vf s0 Hw with "Hfp Hlb Hpin0")
          as %Hl. iPureIntro. by intros _. }
    iModIntro. iFrame "Hfl". iLeft.
    iExists (removelast s0s ++ [s0]). iSplitR; last first.
    { iApply (f0_pinned_drain h b (removelast s0s) vf s0 with "Hfp Hlb"). }
    iPureIntro. intros Hd.
    exact (file_phi_body_drain h b s0s s0 Hsh
             (proj1 (disc_f_out h Uart0 b Hsh) Hd) Hgo Hadm Hlast
             (Hb (proj1 (disc_f_out h Uart0 b Hsh) Hd))).
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

  Lemma file_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    file_led h ==∗
      file_led (h ++ [ObsUartIn i b]) ∗ ftag (h ++ [ObsUartIn i b]).
  Proof using .
    intros Hsh. iIntros "(Hcnt & Hpm & Hfm & Hfl & Hphi)".
    iDestruct (pin_map_step (fgn_echo g) h (ObsUartIn i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step h (ObsUartIn i b) eq_refl with "Hfm") as "Hfm".
    iMod (fl_auth_grow_pre (efl_of h) (efl_of (h ++ [ObsUartIn i b]))
            (echof_lines_of_snoc h (ObsUartIn i b)) with "Hfl")
      as "[Hfl #Hfllb]".
    iAssert (file_phi_res (h ++ [ObsUartIn i b]) ∨ file_taint (fgn_cl g))%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
      iLeft. iDestruct "Hphi" as (s0s) "[%Hb #Hp]".
      iExists s0s. iSplitR.
      - iPureIntro. intros Hd.
        apply (file_phi_body_step_io h (ObsUartIn i b) s0s Hsh
                 ltac:(by destruct i) ltac:(by destruct i)), Hb.
        destruct i;
          [ exact (disc_f_in h b Hsh Hd)
          | exact (proj1 (disc_f_other h (ObsUartIn Uart1 b) eq_refl I Hsh)
                     Hd) ].
      - iApply (f0_pinned_io h (ObsUartIn i b) s0s ltac:(by destruct i)
                  ltac:(by destruct i) with "Hp"). }
    assert (Hsh' : trace_shape (h ++ [ObsUartIn i b]) true)
      by (eapply trace_shape_snoc; [exact Hsh | reflexivity]).
    rewrite /file_led /ftag.
    destruct (decide (disc_f (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; last first.
      { destruct i;
          [ exact (disc_f_in h b Hsh Hd')
          | exact (proj1 (disc_f_other h (ObsUartIn Uart1 b) eq_refl I Hsh)
                     Hd') ]. }
      iModIntro. iFrame "Hcnt Hpm Hfm Hfl Hphi Hfllb".
      iSplitR; [by iPureIntro |]. iLeft. by iPureIntro.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (disc_f h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hfm Hfl Hphi Hfllb".
      iSplitR; [by iPureIntro |]. iRight. rewrite /file_taint /echo_taint.
      iExact "Hlb".
  Qed.

  (* PHI's read at the end of the run, in the owner's form: the guard is the
     WHOLE history's discipline. *)
  Lemma file_led_phi (h : list mobs) :
    file_led h -∗ ⌜file_phi h⌝.
  Proof using .
    iIntros "(Hcnt & _ & _ & _ & [Hphi | HT'])".
    { iDestruct "Hphi" as (s0s) "[%Hb _]". iPureIntro.
      exact (file_phi_of_body h s0s Hb). }
    rewrite /file_taint /echo_taint.
    iDestruct (mono_nat_lb_own_valid with "Hcnt HT'") as %[_ Hle].
    iPureIntro. rewrite /file_phi. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
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
