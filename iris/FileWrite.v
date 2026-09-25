(* ===================================================================== *)
(* FileWrite.v -- ECHO'S APPEND TO [f], PAID FROM THE DEED.              *)
(*                                                                       *)
(* design/app-file.md section 2's APPEND step and section 3's ECHO AT A   *)
(* FILE, at the shape [TreeMove.v] section 3 gives the tree layer:        *)
(* ONE CHUNK, BOTH PHASES, out of the claim's deed.                      *)
(*                                                                       *)
(*   [file_wq]              THE CURSOR: the deed at the content written   *)
(*                          so far ([subseq (echo_chunks ws) sel]), the   *)
(*                          offset equal to its length, the line's        *)
(*                          admissibility and the ledger's lower bound    *)
(*                          -- or the taint.                              *)
(*   [file_claim_read]      phase 1's read ([TreeMove.tree_claim_read]'s  *)
(*                          shape, at [AppFile.file_deed_law]).           *)
(*   [file_awrite_phases]   ONE CHUNK, BOTH PHASES: phase 1 parks the     *)
(*                          deed at the APPENDED content and hands the    *)
(*                          fire its step; phase 2 is [AppFile.           *)
(*                          file_resync] at [sel ++ [j]].                 *)
(*                                                                       *)
(* ===== WHY THERE IS NO [file_awrite_chain] HERE ====================== *)
(*                                                                       *)
(* [TreeMove.tree_awrite_chain] exists because the tree layer's cursor is *)
(* EXISTENTIAL in everything the kernel picks: [tree_wq] says only        *)
(* "[twrote i t t']" -- my tree, except at the file I wrote -- so a node  *)
(* can be built at ANY [(I, off, bs, bs0, nl)] the fire offers.  The FILE *)
(* claim's cursor is EXACT in the content ([AppFile.f_typed] admits only  *)
(* [subseq (echo_chunks ws) sel]), and [FsAbsWriteFire.awrite_full_at] /  *)
(* [awrite_part_at] are [∀]s over the fire's data with no premise slot,   *)
(* so a node must pay [AppInv.app_step] -- hence re-establish [f_typed]   *)
(* at [blk_splice off bs bs0] -- KNOWING NEITHER [off] NOR [bs].  Three   *)
(* separate facts are missing, and each is a CONTRACT fact, not a proof   *)
(* effort:                                                               *)
(*                                                                       *)
(*  (1) THE OFFSET.  The node is handed [off] and the KERNEL's half of    *)
(*      the offset shadow ([OffGv.off_gv γo (1/2)]); the client's half    *)
(*      ([UserOff.uoff], [FdPark.uoff_rcpt]) is what would agree with it  *)
(*      -- and in mode [hand] that half is INSIDE the kernel for the      *)
(*      duration of the call: [FdPark.off_supply_of_st_at_eq] takes the   *)
(*      caller's payment at the syscall boundary and spends it at each    *)
(*      fire ([ProofFilewrite]'s [Hoinvw]).  So no user-side resource can *)
(*      be held across the fire to derive [off = length bs0], and a PURE  *)
(*      [∀ I off bs bs0 nl, wri_pre … -> off = length bs0] premise is     *)
(*      REFUTABLE (two fires at one row with different [off] satisfy the  *)
(*      antecedent), i.e. vacuous.  The equation has to be RELAYED: the   *)
(*      held branch of [SpecFilewrite.filewrite_in] must hand each node   *)
(*      [⌜off = off0 + p⌝] at the caller's own anchor, which is           *)
(*      design/user-write.md section 3c's anchored cursor.                *)
(*                                                                       *)
(*  (2) THE CHUNK'S LENGTH -- LANDED (lane WRITE-RELAY, RELAY 3).         *)
(*      [SpecCopyin.ubytes_at M ua bs] is a pure [∀]-over-[bs]'s-indices  *)
(*      and is therefore PREFIX-CLOSED: the node used to promise only a   *)
(*      run of the caller's image at this base, and NOT the whole chunk.  *)
(*      [FsAbsWriteFire.awrite_full_at] now carries                       *)
(*      [⌜|bs| = SysWriteDefs.wchunk_at n k⌝] beside the content tie --   *)
(*      the count the kernel passed writei at node [k], which is the one  *)
(*      thing it holds for free at the fire -- and with the two together  *)
(*      [SpecCopyin.ubytes_at_inj] identifies [bs] with the chunk the     *)
(*      client MEANT to write, AT THE FIRE.  So [file_awrite_node] no     *)
(*      longer takes [⌜bs = bsk⌝] as a relay; it takes the chunk's own    *)
(*      length and content rows, which a writer holds about its own       *)
(*      buffer, and discharges the equation itself.                       *)
(*                                                                       *)
(*  (3) THE PARTIAL ARM'S DISTURBED TAIL, and this one refutes the        *)
(*      MODEL, not just the proof.  [awrite_part_at]'s delta is           *)
(*      [delta_write i off bs] with only [take r bs] the caller's and     *)
(*      [length bs <= r + BSIZE]: writei commits the partially copied     *)
(*      block, so up to one block of bytes NOBODY NAMES lands in [f].     *)
(*      [AppFile.f_bytes_typed] admits only whole-chunk subsequences, so  *)
(*      that arm's step cannot be paid at all -- and it is one of the two *)
(*      arms the kernel may pick at every node.  design/app-file.md       *)
(*      section 0's limit 1 ("the subset of echo's chunks that landed")   *)
(*      is therefore too strong: either the model admits a partial last   *)
(*      chunk plus a bounded junk tail, or the short-write arm is refuted *)
(*      at the capacity lane the design declines to take.                 *)
(*                                                                       *)
(* WHAT IS LANDED is everything that does NOT depend on those three: the  *)
(* delta algebra the step needs, the claim's read, and the ONE-CHUNK      *)
(* two-phase move at a fire whose [(off, bs, i)] are GIVEN.  The three    *)
(* facts appear as named premises of [file_awrite_phases]; the day the    *)
(* held member relays them, the chain is this lemma under                 *)
(* [FsAbsWriteFire.awrite_chain]'s induction and nothing else.            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.         (* [bioslotG] *)
Require Import Xv6G.               (* [xv6G] *)
Require Import FdSlots.            (* [fdslotG] *)
Require Import IrefSlots.          (* [irefslotG] *)
Require Import ProcAvail.          (* [pavG] *)
Require Import FileInvDefs.        (* [fileG], [file_app] *)
Require Import FsImg.              (* [ROOTINO] *)
Require Import FsImgCheck.         (* [fname_f] *)
Require Import FsBlocks.           (* [fs_names], [fs_top], [blk_splice] *)
Require Import FsNode.             (* [fs_node] *)
Require Import FsTree.             (* [fname] *)
Require Import FsAbsDefs.          (* [aview] / [astep] / [arow_at] *)
Require Import FsAbsDelta.         (* [delta_write] *)
Require Import FsBytesGamma.       (* [fs_gamma_L] *)
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import SysWriteDefs.       (* [wri_pre], [FW_MAX] *)
Require Import SpecCopyin.         (* [ubytes_at] *)
Require Import OffGv.              (* [off_gv] *)
Require Import AppCfg.
Require Import AppInv.             (* [app_inv], [app_body], [app_step], [appE] *)
Require Import FsInitPin.          (* [INIT_INO] *)
Require Import FsShPin.            (* [SH_INO], [era0_sh_pins] *)
Require Import FsEchoPin.          (* [ECHO_INO], [era0_echo_pins] *)
Require Import FsCatPin.           (* [CAT_INO], [era0_cat_pins] *)
Require Import FsGrepPin.          (* [GREP_INO], [era0_grep_pins] *)
Require Import FsConsPin.          (* [file_pin] and its family, [cons_state] *)
Require Import FileFsPure.         (* [file_fs_pure] *)
Require Import EchoDisc.           (* [line_ok] *)
Require Import EchoOut.            (* [echoOutG] *)
Require Import FileState.          (* [fstate], [echo_chunks], [subseq], [sel_ok] *)
Require Import AppFile.
Require Import UserOff.            (* [uoff] -- THE PROGRAM'S HALF *)
Require Import FsAbsWriteFire.     (* [awrite_full_adv] -- the advanced node *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE DELTA IS INVISIBLE TO THE DIRECTORY STRUCTURE                 *)
(*                                                                       *)
(*  [delta_write] rewrites ONE file row's bytes and nothing else, so no   *)
(*  directory's entry map moves -- at the written inum because a file has *)
(*  no entries either way, everywhere else because the row is untouched.  *)
(*  Every path fact of the claim (the four binaries' pins, the console's  *)
(*  presence or absence, [f]'s own [astep]) rides on that one lemma.      *)
(* ===================================================================== *)

Lemma delta_write_aents (av : aview) (i : Z) (off : nat)
    (new : list (bv 8)) (d : Z) :
  aents (delta_write i off new av) d = aents av d.
Proof.
  destruct (decide (d = i)) as [-> | Hne]; last first.
  { by rewrite /aents (delta_write_other av i off new d Hne). }
  destruct (av !! i) as [a |] eqn:Hi; last first.
  { by rewrite (delta_write_absent av i off new Hi). }
  destruct a as [n nl]. destruct n as [bs | e | ma mi].
  - by rewrite /aents (delta_write_lookup av i off new bs nl Hi) Hi.
  - by rewrite /delta_write Hi /=.
  - by rewrite /delta_write Hi /=.
Qed.

Lemma delta_write_astep (av : aview) (i : Z) (off : nat)
    (new : list (bv 8)) (d : Z) (s : fname) :
  astep (delta_write i off new av) d s = astep av d s.
Proof. by rewrite /astep delta_write_aents. Qed.

Lemma delta_write_apath (av : aview) (i : Z) (off : nat)
    (new : list (bv 8)) (d : Z) (ps : list fname) :
  apath_at (delta_write i off new av) d ps = apath_at av d ps.
Proof.
  revert d. induction ps as [| s ps IH]; intros d; [reflexivity |].
  rewrite !apath_at_cons delta_write_astep.
  destruct (astep av d s) as [c |]; [apply IH | reflexivity].
Qed.

Lemma delta_write_arun (av : aview) (i : Z) (off : nat)
    (new : list (bv 8)) (d : Z) (ps : list fname) (ds : list Z) :
  arun av d ps ds -> arun (delta_write i off new av) d ps ds.
Proof.
  induction 1 as [d0 | d0 c s ps0 ds0 Hst Hr IH]; [constructor |].
  econstructor; [| exact IH]. by rewrite delta_write_astep.
Qed.

(* ===================================================================== *)
(*  2.  THE PINS SURVIVE A WRITE AT ANY OTHER INUM                        *)
(* ===================================================================== *)

Lemma file_pin_write (nm : fname) (ino : Z) (bs : list (bv 8))
    (i : Z) (off : nat) (new : list (bv 8)) (av : aview) :
  i <> ino -> file_pin nm ino bs av -> file_pin nm ino bs (delta_write i off new av).
Proof.
  intros Hne Hp. pose proof Hp as (Hpath & Hrow & Hr). split_and!.
  - by rewrite delta_write_apath.
  - by rewrite (delta_write_other av i off new ino (not_eq_sym Hne)).
  - by apply delta_write_arun.
Qed.

(* cat's pins are [file_pin]'s fourth instance, exactly as [FsConsPin]'s
   [file_pin_init] / [_sh] / [_echo] are its first three *)
Lemma file_pin_cat (av : aview) :
  file_pin fname_cat CAT_INO cat_bytes av <-> era0_cat_pins av.
Proof. rewrite /file_pin /era0_cat_pins /cat_path. reflexivity. Qed.

(* ...and grep's its fifth (claude-notes/design/grep-pipes.md, cut G6) *)
Lemma file_pin_grep (av : aview) :
  file_pin fname_grep GREP_INO grep_bytes av <-> era0_grep_pins av.
Proof. rewrite /file_pin /era0_grep_pins /grep_path. reflexivity. Qed.

(* THE CONSOLE NEEDS NO PREMISE: its row is a DEVICE, and [delta_write]
   at a non-file row is the identity. *)
Lemma cons_present_write (jc : Z) (i : Z) (off : nat)
    (new : list (bv 8)) (av : aview) :
  cons_present_at jc av -> cons_present_at jc (delta_write i off new av).
Proof.
  intros Hp. pose proof Hp as (Hpath & Hrow & Hr). split_and!.
  - by rewrite delta_write_apath.
  - destruct (decide (jc = i)) as [-> | Hne]; last first.
    { by rewrite (delta_write_other av i off new jc Hne). }
    rewrite /delta_write Hrow /cons_dev /=. exact Hrow.
  - by apply delta_write_arun.
Qed.

Lemma cons_absent_write (i : Z) (off : nat) (new : list (bv 8)) (av : aview) :
  cons_absent av -> cons_absent (delta_write i off new av).
Proof. rewrite /cons_absent. by rewrite delta_write_astep. Qed.

Lemma file_fs_pure_write (i : Z) (off : nat) (new : list (bv 8)) (av : aview) :
  i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO -> i <> GREP_INO ->
  file_fs_pure av -> file_fs_pure (delta_write i off new av).
Proof.
  intros Hi Hs He Hc Hg ((Hin & Hsh & Hec) & Hcat & Hgrep).
  split; [split_and! | split].
  - apply file_pin_init, (file_pin_write _ _ _ i off new av Hi).
    by apply file_pin_init.
  - apply file_pin_sh, (file_pin_write _ _ _ i off new av Hs).
    by apply file_pin_sh.
  - apply file_pin_echo, (file_pin_write _ _ _ i off new av He).
    by apply file_pin_echo.
  - apply file_pin_cat, (file_pin_write _ _ _ i off new av Hc).
    by apply file_pin_cat.
  - apply file_pin_grep, (file_pin_write _ _ _ i off new av Hg).
    by apply file_pin_grep.
Qed.

(* ===================================================================== *)
(*  3.  [f]'s ROW UNDER THE WRITE, AND THE SPLICE AT THE END              *)
(* ===================================================================== *)

(* THE ONE LEMMA lane F-OPEN's [FileDeltas.v] will own (it is not on this
   branch yet, so it is proved here): a write at the inum [f]'s name
   resolves to moves [f]'s state by the splice, and moves nothing else. *)
Lemma f_ok_delta_write (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) :
  f_ok av (Some (i, bs0)) ->
  f_ok (delta_write i off new av) (Some (i, blk_splice off new bs0)).
Proof.
  intros (Hst0 & Hrow). split.
  - by rewrite delta_write_astep.
  - by rewrite (delta_write_lookup av i off new bs0 1%nat Hrow).
Qed.

(* AT THE END OF THE FILE the splice IS the append -- which is the whole
   of what the offset equation buys. *)
Lemma blk_splice_end (off : nat) (sub bs : list (bv 8)) :
  off = length bs -> blk_splice off sub bs = bs ++ sub.
Proof.
  intros ->. rewrite /blk_splice take_ge; [| lia].
  rewrite drop_ge; [| lia]. by rewrite app_nil_r.
Qed.

(* THE VACUITY CHECK (durable-notes' rule for a new premise).  The two
   pure facts [file_awrite_phases] adds to the fire's own [wri_pre] -- the
   NODE equation and the row the fire is at -- are jointly satisfiable, and
   with them the OFFSET equation at [off = length bs0]: the witness is the
   two-row view in which [f] is the root's only entry.

   ...AND THE FOURTH CLAUSE IS RELAY 3's (lane WRITE-RELAY): the length the
   node now carries is satisfiable at exactly echo's own shape -- ONE
   [write] per chunk, so the node is node 0 of a one-chunk request and
   [SysWriteDefs.wchunk_at] collapses to the chunk itself.  A chunk longer
   than [FW_MAX] would be split across nodes and this clause would name the
   cap instead; echo's four are bytes long. *)
Lemma file_write_premises_sat (i : Z) (bs0 bsk : list (bv 8)) :
  i <> FsImg.ROOTINO ->
  (Z.of_nat (length bsk) <= FW_MAX)%Z ->
  let av : aview :=
    <[ FsImg.ROOTINO := MkAnode (ADir {[ fname_f := i ]}) 1%nat ]>
      {[ i := MkAnode (AFile bs0) 1%nat ]} in
  astep av FsImg.ROOTINO fname_f = Some i
  /\ arow_at av i (MkAnode (AFile bs0) 1%nat)
  /\ (length bs0 <= length bs0)%nat
  /\ Z.of_nat (length bsk) = wchunk_at (Z.of_nat (length bsk)) 0.
Proof.
  intros Hne Hcap av. split_and!.
  - rewrite /astep /aents /av lookup_insert /= /anode_ents /=.
    by rewrite lookup_singleton.
  - apply arow_at_of_Some; [ done |].
    rewrite /av lookup_insert_ne; [| exact (not_eq_sym Hne)]. by rewrite lookup_singleton.
  - reflexivity.
  - rewrite /wchunk_at /=. lia.
Qed.

(* ===================================================================== *)
(*  4.  THE CURSOR AND THE MOVE                                           *)
(* ===================================================================== *)

Section FileWrite.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* THE CURSOR (design/app-file.md section 3, "echo at a file"): the deed
     AND the ticket at the content written so far, the offset equal to its
     length, and the two pure facts [AppFile.f_typed_some] wants beside the
     ledger's lower bound -- or the taint, which is what a move somebody
     else did not pay leaves behind.  [AppTree]'s [TreeMove.tree_wq] with
     the owner's subtree replaced by the deed's CONTENT. *)
  Definition file_wq (c : file_fixed) (r : file_names) (i : Z) (ws : wordline)
      (sel : list nat) (off : nat) : iProp Σ :=
    ((∃ ls : list wordline,
        fown r (Some (i, subseq (echo_chunks ws) sel))
        ∗ ⌜off = length (subseq (echo_chunks ws) sel)⌝
        ∗ ⌜EchoDisc.line_ok ws⌝
        ∗ ⌜sel_ok (echo_chunks ws) sel⌝
        ∗ fl_lb c ls ∗ ⌜ws ∈ ls⌝)
     ∨ file_taint c)%I.

  (* the tainted fire's step, [TreeMove.tree_app_step_taint]'s twin *)
  Lemma file_app_step_taint (c : file_fixed) (r : file_names) (i : Z)
      (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    file_taint c -∗ app_step i I av'.
  Proof using .
    intros Heq. iIntros "#Ht". rewrite /app_step Heq.
    cbn [app_pred app_run app_names]. iIntros (n') "%Hav Hp".
    iModIntro. iNext. iApply (file_step_taint c r (abs_view I) with "Ht Hp").
  Qed.

  (* PHASE 1's READ ([TreeMove.tree_claim_read]'s shape at
     [AppFile.file_deed_law]): the owner agrees the map the kernel lent it
     against the application's own half and reads [f]'s state off the
     claim.  LINEAR -- the deed goes in and comes back. *)
  Lemma file_claim_read (γfs : fs_names) (c : file_fixed) (r : file_names)
      (s : dst) (I : gmap Z fs_node) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ fdeed r s -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗ fdeed r s ∗
      ((⌜f_ok (abs_view I) s⌝ ∗ f_typed c s) ∨ file_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv Hd Hka".
    iDestruct (file_deed_law c r) as "#Hlaw".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp".
    iDestruct ("Hlaw" $! (abs_view I) s with "Hd Hp") as "(Hp & Hd & Hfact)".
    iMod ("Hclose" with "[Hh Hp Hx]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL "Hp"; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Hd Hfact".
  Qed.

  (* ONE CHUNK, BOTH PHASES -- [TreeMove.tree_awrite_phases]'s twin, one
     file over.  THE FULL AND THE PARTIAL ARM WOULD BE THE SAME PROOF
     (they differ in the bytes, never in the delta) -- see the header for
     why the partial arm cannot supply premise 3 at all.

     THE FOUR PREMISES.  [Hnode] and [Hoff] are the two facts the claim
     cannot give: the descriptor is on [f]'s row, and the fire's offset is
     the cursor's anchor ([FdPark.off_supply_of_st_at_eq]'s tie
     [⌜m = OffHeld -> off' = off⌝] at [OffHeld] is what discharges the
     second).  [Hbs] is the chunk equation (header (2)).  The four inum
     inequalities are what keeps the write off the pinned binaries' rows;
     a caller holding the open's receipt discharges them once, since a
     freshly created [f] is at an inum none of the four names. *)
  Lemma file_awrite_phases (γfs : fs_names) (c : file_fixed) (r : file_names)
      (i : Z) (ws : wordline) (sel : list nat) (jx : nat) (off offk : nat)
      (I : gmap Z fs_node) (bs bs0 : list (bv 8)) (nl : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (* the fire's own premise, as [FsAbsWriteFire.awrite_full_at] hands it *)
    wri_pre (abs_view I) i offk bs bs0 nl ->
    (* PREMISE 1 -- THE NODE EQUATION: the row the fire is at IS [f]'s *)
    astep (abs_view I) FsImg.ROOTINO fname_f = Some i ->
    (* PREMISE 2 -- THE OFFSET EQUATION: the held offset's tie *)
    offk = off ->
    (* PREMISE 3 -- THE CHUNK EQUATION: the bytes that land ARE chunk [jx] *)
    bs = echo_chunks ws !!! jx ->
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun k => (k < jx)%nat) sel ->
    (* PREMISE 4 -- [f] is not one of the four pinned binaries *)
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO -> i <> GREP_INO ->
    app_inv γfs -∗ file_wq c r i ws sel off -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
      app_step i I (delta_write i offk bs (abs_view I)) ∗
      (∀ I' : gmap Z fs_node,
         ⌜abs_view I' = delta_write i offk bs (abs_view I)⌝ -∗
         ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
         ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ∗
         file_wq c r i ws (sel ++ [jx]) (off + length bs)).
  Proof using .
    intros Heq Hpre Hnode Hoffk Hbs Hjx Hlt Hi1 Hi2 Hi3 Hi4 Hi5. subst offk.
    iIntros "#Hinv Hq Hka".
    rewrite {1}/file_wq.
    iDestruct "Hq" as "[Hq | #HT]"; last first.
    { (* THE TAINT: the step is free and the cursor comes back tainted *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_wq. by iRight. }
    iDestruct "Hq" as (ls) "([Hd Htk] & %Hoff & %Hline & %Hsel & #Hlb & %Hin)".
    iMod (file_claim_read γfs c r (Some (i, subseq (echo_chunks ws) sel)) I Heq
            with "Hinv Hd Hka") as "(Hka & Hd & [[%Hok _] | #HT])"; last first.
    { (* the claim is tainted: pay the step off the taint *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_wq. by iRight. }
    (* THE EXACT ARM: the deed's content IS the row the fire is at *)
    destruct Hpre as (Hrow & Hpos & Hle & Hcap).
    destruct Hok as (Hst0 & Hrow0).
    pose proof (arow_at_pinned (abs_view I) i _ _ Hrow Hrow0) as Hab.
    injection Hab as Hbs0 Hnl. subst bs0. clear Hnl.
    (* the offset equation, cashed: the fire is at the END of [f] *)
    assert (Hend : blk_splice off bs (subseq (echo_chunks ws) sel)
                   = subseq (echo_chunks ws) sel ++ bs)
      by exact (blk_splice_end off bs _ Hoff).
    assert (Hsnoc : subseq (echo_chunks ws) (sel ++ [jx])
                    = subseq (echo_chunks ws) sel ++ bs)
      by (rewrite subseq_snoc; by rewrite Hbs).
    assert (Hselok : sel_ok (echo_chunks ws) (sel ++ [jx]))
      by exact (sel_ok_snoc _ sel jx Hsel Hjx Hlt).
    (* the step's own obligations *)
    assert (Hstep : f_ok (abs_view I) (Some (i, subseq (echo_chunks ws) sel)) ->
                    f_ok (delta_write i off bs (abs_view I))
                      (Some (i, subseq (echo_chunks ws) (sel ++ [jx])))).
    { intros Hok. rewrite Hsnoc -Hend.
      exact (f_ok_delta_write (abs_view I) i off bs _ Hok). }
    iAssert (f_typed c (Some (i, subseq (echo_chunks ws) (sel ++ [jx]))))%I
      as "#Hty'".
    { iApply (f_typed_some c ls ws (sel ++ [jx]) i Hin Hline Hselok). iExact "Hlb". }
    iModIntro. iFrame "Hka". iSplitL "Hd".
    { iApply (file_app_step_park c r i I _
                (Some (i, subseq (echo_chunks ws) sel))
                (Some (i, subseq (echo_chunks ws) (sel ++ [jx]))) Heq
                (file_fs_pure_write i off bs (abs_view I) Hi1 Hi2 Hi3 Hi4 Hi5)
                (cons_absent_write i off bs (abs_view I))
                (fun jc => cons_present_write jc i off bs (abs_view I))
                Hstep with "Hd Hty'"). }
    (* PHASE 2 *)
    iIntros (I') "%Hav Hka'".
    assert (Hokpost : f_ok (abs_view I')
                        (Some (i, subseq (echo_chunks ws) (sel ++ [jx])))).
    { rewrite Hav. apply Hstep. split; [exact Hst0 | exact Hrow0]. }
    assert (Hne : (Some (i, subseq (echo_chunks ws) sel) : dst)
                  <> Some (i, subseq (echo_chunks ws) (sel ++ [jx]))).
    { intros Hc. injection Hc as Hc. rewrite Hsnoc in Hc.
      assert (Hl : length (subseq (echo_chunks ws) sel)
                   = length (subseq (echo_chunks ws) sel ++ bs))
        by (by rewrite -Hc).
      rewrite length_app in Hl. lia. }
    iMod (file_resync γfs c r (Some (i, subseq (echo_chunks ws) sel))
            (Some (i, subseq (echo_chunks ws) (sel ++ [jx]))) I' appE
            ltac:(set_solver) Heq (f_ok_fcontent _ _ Hokpost) Hne
            with "Hinv Htk [Hka']") as "[Hka' Hout]".
    { rewrite /fs_gamma_L /=. iExact "Hka'". }
    iModIntro.
    iSplitL "Hka'"; [ rewrite /fs_gamma_L /=; iExact "Hka'" |].
    rewrite /file_wq.
    iDestruct "Hout" as "[Hown | [_ #HT]]"; [| by iRight ].
    iLeft. iExists ls. iFrame "Hown Hlb". iPureIntro. split_and!.
    - rewrite Hsnoc length_app. lia.
    - exact Hline.
    - exact Hselok.
    - exact Hin.
  Qed.

  (* =================================================================== *)
  (*  5.  THE NODE THAT WOULD CLOSE THE CHAIN                              *)
  (*                                                                       *)
  (*  [FsAbsWriteFire.awrite_full_at] WITH THREE [⌜⌝] ARROWS ADDED and     *)
  (*  nothing else changed -- delete them and the definition is that one   *)
  (*  verbatim.  This is the precise statement of what the header's three  *)
  (*  missing facts are, and [file_awrite_node] below proves that with     *)
  (*  them the cursor chains: the day a held member relays them, the       *)
  (*  chain is that lemma under [awrite_chain]'s induction and nothing     *)
  (*  else.  WHO OWES WHICH is written at each arrow.                      *)
  (* =================================================================== *)
  Definition file_awrite_full_anchored (γfs : fs_names) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (nn : Z) (k : nat)
      (off0 : nat) (REST : iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       ⌜ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) bs⌝ -∗
       (* RELAY 3 -- LANDED, and it is [FsAbsWriteFire.awrite_full_at]'s
          OWN third arrow now: the bytes that land are the WHOLE chunk the
          node was called with, not merely a run of the caller's image at
          the chunk's base ([SpecCopyin.ubytes_at] is prefix-closed).  It
          is written here verbatim so that the two remaining arrows are
          all that separates this definition from the landed node. *)
       ⌜Z.of_nat (length bs) = wchunk_at nn k⌝ -∗
       (* RELAY 1 -- THE CLAIM OWES THIS ONE ([AppFile.f_ok] must name
          [f]'s INUM; today its [Some] arm quantifies it existentially, so
          a deed holder cannot say that the row its descriptor is on is
          [f]'s). *)
       ⌜astep (abs_view I) FsImg.ROOTINO fname_f = Some i⌝ -∗
       (* RELAY 2 -- THE KERNEL OWES THIS ONE: the anchored offset
          (design/user-write.md section 3c), which the held branch of
          [SpecFilewrite.filewrite_in] can relay off
          [FdPark.off_supply_of_st_at_eq]'s tie. *)
       ⌜off = off0⌝ -∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I -∗
       off_link γo (Z.of_nat off) ={appE}=∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
       app_step i I (delta_write i off bs (abs_view I)) ∗
       (∀ I' : gmap Z fs_node,
          ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
          ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
          ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ∗
          (* the node's own answer, verbatim from [awrite_full_at]: the
             half comes back UNMOVED or ADVANCED BY THE CHUNK, and this
             cursor proves the first ([OffGv.off_ret_keep]) until it holds
             a user half to advance. *)
          off_ret γo off (length bs) ∗ REST))%I.

  (* ...AND THE CURSOR PAYS IT.  [TreeMove.tree_awrite_chain]'s per-node
     step, at the deed: the node goes in at [sel] and comes back at
     [sel ++ [jx]], the offset advanced by the chunk. *)
  (* THE TWO ROWS THE WRITER HOLDS ABOUT ITS OWN BUFFER.  [Hbsk] is the
     content tie for the chunk it MEANT to write, at the same base the node
     states its own at; [Hlenk] is that chunk's length read against the
     count the call was made with.  For echo's four writes both are trivial:
     each chunk goes out in a [write] of its own, so [k = 0] and
     [wchunk_at |chunk| 0 = |chunk|] ([file_write_premises_sat]).  Together
     with the node's own RELAY 3 they give [bs = echo_chunks ws !!! jx] --
     which is the premise [file_awrite_phases] takes and the whole of what
     RELAY 3 was for. *)
  Lemma file_awrite_node (γfs : fs_names) (c : file_fixed) (r : file_names)
      (i : Z) (ws : wordline) (sel : list nat) (jx : nat) (off : nat)
      (γo : gname) (M : gmap Z (bv 8)) (ua : mword 64) (nn : Z) (k : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun q => (q < jx)%nat) sel ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO -> i <> GREP_INO ->
    ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k))
      (echo_chunks ws !!! jx) ->
    Z.of_nat (length (echo_chunks ws !!! jx)) = wchunk_at nn k ->
    app_inv γfs -∗ file_wq c r i ws sel off -∗
    file_awrite_full_anchored γfs i γo M ua nn k off
      (file_wq c r i ws (sel ++ [jx])
         (off + length (echo_chunks ws !!! jx))).
  Proof using .
    intros Heq Hjx Hlt Hi1 Hi2 Hi3 Hi4 Hi5 Hbsk Hlenk. iIntros "#Hinv Hq".
    rewrite /file_awrite_full_anchored.
    iIntros (I off1 bs bs0 nl) "%Hpre %Hby %Hlen %Hnode %Hoff Hka Hg".
    (* RELAY 3, CASHED: two runs of the caller's image at one base and of
       one length are one run ([SpecCopyin.ubytes_at_inj]). *)
    assert (Hbs : bs = echo_chunks ws !!! jx).
    { apply (ubytes_at_inj M (add_vec_int ua (FW_MAX * Z.of_nat k))
               bs (echo_chunks ws !!! jx) Hby Hbsk). lia. }
    iMod (file_awrite_phases γfs c r i ws sel jx off off1 I bs bs0 nl
            Heq Hpre Hnode Hoff Hbs Hjx Hlt Hi1 Hi2 Hi3 Hi4 Hi5
            with "Hinv Hq Hka") as "(Hka & Hstep & Hph2)".
    iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
    iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hq']".
    iModIntro. iFrame "Hka'".
    (* the node returns the borrow UNMOVED: this cursor holds no user half
       yet (that is design/app-file.md section 3's link arm, lane
       OFF-LINK), so [off_ret_keep] is the arm it can prove. *)
    iSplitL "Hg"; [iApply (off_ret_of_link with "Hg") |].
    rewrite Hbs. iExact "Hq'".
  Qed.

  (* =================================================================== *)
  (*  6.  THE CLIENT-ADVANCED NODE (RULING EFQ)                           *)
  (*                                                                     *)
  (*  THE CURSOR IS A PIPE, not a conjunction.  The landed cursor was      *)
  (*  [file_wq ∗ uoff] at the content's length, and that conjoins the      *)
  (*  program's half to the content on BOTH of [file_wq]'s arms -- so a    *)
  (*  tainted object, whose bytes nobody owes anything about, would still  *)
  (*  have to have the shadow at their length.  Nothing supplies that.     *)
  (*  The owner's shape is the pipe: FIRED, and then the half IS at the    *)
  (*  content's length; or TAINTED, and then the half is wherever the      *)
  (*  hijacker left it.                                                    *)
  (* =================================================================== *)
  Definition file_cur (c : file_fixed) (r : file_names) (i : Z)
      (ws : wordline) (sel : list nat) (γo : gname) : iProp Σ :=
    ((file_wq c r i ws sel (length (subseq (echo_chunks ws) sel))
      ∗ uoff γo (length (subseq (echo_chunks ws) sel)))
     ∨ (file_taint c ∗ ∃ p : nat, uoff γo p))%I.

  (* the two introductions, so a consumer never unfolds the pipe *)
  Lemma file_cur_fired (c : file_fixed) (r : file_names) (i : Z)
      (ws : wordline) (sel : list nat) (γo : gname) :
    file_wq c r i ws sel (length (subseq (echo_chunks ws) sel)) -∗
    uoff γo (length (subseq (echo_chunks ws) sel)) -∗
    file_cur c r i ws sel γo.
  Proof using . iIntros "Hq Hu". iLeft. iFrame "Hq Hu". Qed.

  Lemma file_cur_taint (c : file_fixed) (r : file_names) (i : Z)
      (ws : wordline) (sel : list nat) (γo : gname) (p : nat) :
    file_taint c -∗ uoff γo p -∗ file_cur c r i ws sel γo.
  Proof using . iIntros "#Ht Hu". iRight. iFrame "Ht". by iExists p. Qed.

  (* ...and the half is there on EITHER arm, which is what the node needs
     to read the position it is being fired at. *)
  Lemma file_cur_half (c : file_fixed) (r : file_names) (i : Z)
      (ws : wordline) (sel : list nat) (γo : gname) :
    file_cur c r i ws sel γo -∗ ∃ p : nat, uoff γo p.
  Proof using .
    iIntros "[[_ Hu] | [_ Hu]]"; [ by iExists _ | iExact "Hu" ].
  Qed.

  (* THE NODE.  [FsAbsWriteFire.awrite_full_adv] at the file's cursor, and
     the three relays are gone:

       RELAY 1 (the row the fire is at is [f]'s) is DERIVED HERE, inside
         the node, off the claim the deed names ([file_claim_read]) -- it
         was a relayed premise only because [file_awrite_phases] takes it,
         and the node is the party that can read it;
       RELAY 2 (the anchored offset) is gone with the anchor: the node
         reads [off] off the half in its own closure ([uoff_agree_k]),
         INSIDE its own [forall off];
       RELAY 3 is the node's own third arrow, cashed by [ubytes_at_inj].

     ...AND PHASE 2 HANDS THE BOX'S ARM BACK ADVANCED ([uoff_advance]
     moves both halves at once, since the node holds both), which is the
     whole of what a held descriptor's write costs the kernel. *)
  Lemma file_awrite_node_adv (γfs : fs_names) (c : file_fixed)
      (r : file_names) (i : Z) (ws : wordline) (sel : list nat) (jx : nat)
      (γo : gname) (M : gmap Z (bv 8)) (ua : mword 64) (nn : Z) (k : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun q => (q < jx)%nat) sel ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO -> i <> GREP_INO ->
    ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k))
      (echo_chunks ws !!! jx) ->
    Z.of_nat (length (echo_chunks ws !!! jx)) = wchunk_at nn k ->
    □ (app_taint -∗ file_taint c) -∗
    app_inv γfs -∗ file_cur c r i ws sel γo -∗
    awrite_full_adv (fs_gamma_L γfs) appE i γo M ua nn k
      (file_cur c r i ws (sel ++ [jx]) γo).
  Proof using .
    intros Heq Hjx Hlt Hi1 Hi2 Hi3 Hi4 Hi5 Hbsk Hlenk.
    iIntros "#Hbr #Hinv Hcur". rewrite /awrite_full_adv.
    iIntros (I off bs bs0 nl) "%Hpre %Hby %Hlen Hka Hg".
    (* RELAY 3, CASHED *)
    assert (Hbs : bs = echo_chunks ws !!! jx).
    { apply (ubytes_at_inj M (add_vec_int ua (FW_MAX * Z.of_nat k))
               bs (echo_chunks ws !!! jx) Hby Hbsk). lia. }
    (* THE BOX'S ARM: the kernel's half, or the disconnect. *)
    iDestruct "Hg" as "[Hk | #HTa]"; last first.
    { (* DISCONNECTED: the object is somebody else's, the step is free, and
         the cursor comes back on its taint arm with its half unmoved. *)
      iDestruct ("Hbr" with "HTa") as "#HTf".
      iDestruct (file_cur_half with "Hcur") as (p) "Hu".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HTf". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      iSplitR; [ by iApply off_link_taint | ].
      iApply (file_cur_taint with "HTf Hu"). }
    (* THE LINK.  Read the position off the half FIRST: it is the one fact
       the anchor used to relay. *)
    iDestruct "Hcur" as "[[Hq Hu] | [#HTf Hu]]"; last first.
    { (* the cursor is already tainted: the step is free, but the shadow
         still moves -- the kernel's fire advanced [f->off] and the box's
         arm has to come back at that value. *)
      iDestruct "Hu" as (p) "Hu".
      iDestruct (uoff_agree_k with "Hu Hk") as %Hz.
      assert (Hop : off = p) by lia. subst p.
      iMod (uoff_advance γo off (length bs) with "Hu Hk") as "[Hk Hu]".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HTf". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      iSplitL "Hk"; [ by iApply off_link_of | ].
      iApply (file_cur_taint with "HTf Hu"). }
    (* THE FIRED ARM.  The half pins [off] to the content's length ... *)
    iDestruct (uoff_agree_k with "Hu Hk") as %Hz.
    assert (Hoff : off = length (subseq (echo_chunks ws) sel)) by lia.
    iEval (rewrite -Hoff) in "Hu".
    (* ...and RELAY 1 comes off the claim, read through the deed. *)
    rewrite {1}/file_wq.
    iDestruct "Hq" as "[Hq | #HTf]"; last first.
    { (* the cursor's own taint arm *)
      iMod (uoff_advance γo off (length bs) with "Hu Hk") as "[Hk Hu]".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HTf". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      iSplitL "Hk"; [ by iApply off_link_of | ].
      iApply (file_cur_taint with "HTf Hu"). }
    iDestruct "Hq" as (ls) "([Hd Htk] & %Hoff0 & %Hline & %Hsel & #Hlb & %Hin)".
    iMod (file_claim_read γfs c r (Some (i, subseq (echo_chunks ws) sel)) I Heq
            with "Hinv Hd Hka") as "(Hka & Hd & [[%Hok _] | #HTf])"; last first.
    { (* the claim is tainted: same answer, off the claim's own taint *)
      iMod (uoff_advance γo off (length bs) with "Hu Hk") as "[Hk Hu]".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HTf". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      iSplitL "Hk"; [ by iApply off_link_of | ].
      iApply (file_cur_taint with "HTf Hu"). }
    destruct Hok as [Hnode _].
    (* the cursor goes back together for the phase lemma *)
    iAssert (file_wq c r i ws sel off) with "[Hd Htk]" as "Hq".
    { rewrite /file_wq. iLeft. iExists ls. iFrame "Hd Htk Hlb".
      iPureIntro. split_and!; [ exact Hoff | exact Hline | exact Hsel
                              | exact Hin ]. }
    iMod (file_awrite_phases γfs c r i ws sel jx off off I bs bs0 nl
            Heq Hpre Hnode eq_refl Hbs Hjx Hlt Hi1 Hi2 Hi3 Hi4 Hi5
            with "Hinv Hq Hka") as "(Hka & Hstep & Hph2)".
    iMod (uoff_advance γo off (length bs) with "Hu Hk") as "[Hk Hu]".
    iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
    iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hq']".
    iModIntro. iFrame "Hka'".
    iSplitL "Hk"; [ by iApply off_link_of | ].
    (* THE SNOC: the new content's length IS the old one plus the chunk *)
    assert (Hsnoc : length (subseq (echo_chunks ws) (sel ++ [jx]))
                    = (off + length bs)%nat).
    { rewrite subseq_snoc length_app Hbs. lia. }
    rewrite /file_cur Hsnoc. iLeft. iFrame "Hq' Hu".
  Qed.

End FileWrite.
