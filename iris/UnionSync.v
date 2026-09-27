(* ===================================================================== *)
(*  UnionSync.v -- THE UNION'S SYNC PART OF THE CLAIM, ITS TOKEN AND ITS  *)
(*  HOOK, AND THE CLOSURE LEMMAS THAT CHECK THE DESIGN (lane SY3-A3a;     *)
(*  design: claude-notes/design/sync.md section 4.5).                     *)
(*                                                                        *)
(*  THE SHARES.  Each era's SYNC LIST (a [mono_list] of sync records      *)
(*  [UnionAdm.srec]) is split three ways: [●{½}] in the durable copy,     *)
(*  [●{¼}] in the running claim, [●{¼}] in the era's TOKEN [union_tk]     *)
(*  (which the log invariant holds).  The REGISTRY [ugn_reg] names each   *)
(*  era's list; the COMMIT-ERA counter [ugn_cm] has its full authority in *)
(*  the durable copy; the copy also carries a lower bound of the          *)
(*  MACHINE's started counter [ugn_st] at its era (“that many PowerOns    *)
(*  have happened”), which the loan of the machine's [start_auth] bounds. *)
(*                                                                        *)
(*  THE COUNTERS' CAMERA IS A PARAMETER, [HSt].  [ugn_st] is the machine's *)
(*  own gname, so its [mono_natG] must be the machine's                    *)
(*  ([RiscvAdequacy.riscv_pre_genGS], which A1's equation                 *)
(*  [riscvF_genGS = riscv_pre_genGS] identifies with the record's); no    *)
(*  camera of [fileAppG] could ever be that instance, and a second        *)
(*  [mono_natG] beside [echoOutG]'s in one scope is the duplicate-class   *)
(*  trap.  So every definition here that reads a counter takes [HSt]      *)
(*  EXPLICITLY, and this file binds no other [mono_natG] (no [echoOutG]    *)
(*  in the claim's sections).  [ugn_cm] lives at the same instance.       *)
(*                                                                        *)
(*  THE ERA is the instance's PURE field [fn_era] (ledger numbering: the  *)
(*  birth is era 0, the boot at [gen_id] era [S gen_id]); the running      *)
(*  claim's is read from the record predicate [union_ok].                 *)
(*                                                                        *)
(*  THE CHAIN.  [sync_chain ls Ls]: the records of [srec0 :: Ls] rise      *)
(*  ([srec_le] at the line list [ls]), AND the last record's sync line is  *)
(*  in [ls] ([ls !! (p-1) = LSync] at its position [p], or [p = 0]).  The *)
(*  second conjunct is the POSITION fact the design did not state: it is  *)
(*  what bounds the last record's position by the claim's own lower bound *)
(*  and tells a redirect line from the record's sync line.                *)
(*                                                                        *)
(*  WHAT THE CLOSURE LEMMAS FOUND (section 5): the merge, the PowerOn     *)
(*  re-base and the birth close as the design states them.  The HOOK and  *)
(*  a REDIRECT round do not: each needs the last record's position to be  *)
(*  at most the caller's own line position ([(slast Ls).1 <= length ls']) *)
(*  -- “the sync being recorded, or the line being written, is not OLDER  *)
(*  than the last recorded sync”.  That is true of sh's serial rounds but *)
(*  is no ghost fact: two lower bounds of the line list are merely        *)
(*  comparable, and a stale lower bound (an older sync line, an older     *)
(*  redirect) refutes nothing.  Both lemmas are stated over the running   *)
(*  claim's BODY [sync_body] with that pure premise, and the premise is   *)
(*  the open design point for A3c/A4.                                     *)
(* ===================================================================== *)
From Stdlib Require Import Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own mono_nat ghost_map invariants.
From iris.algebra.lib Require Import mono_list.
Require Import Xv6Cameras.         (* [fsTopG]: the top map's ghost class *)
Require Import FsNode.             (* [fs_node] *)
Require Import FsAbsDefs.          (* [aview], [abs_view] *)
Require Import FileState.          (* [fstate], [echo_chunks], [subseq] *)
Require FileDisc.                  (* [LSync], [LEchoF] *)
Require Import UnionAdm.           (* [srec], [uadm], [srec_le], the shrink *)
Require Import EchoOut.            (* [echoOutG] (the hook at [file_pred]) *)
Require Import AppFile.            (* [file_names], [fl_lb], [fcontent_of] *)
Require Import FileOut.            (* [fgn_cl] *)
Require Import UnionOut.           (* [union_gn] *)
From stdpp Require Import list.

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

(* the instance at a new sync list, era and role (the deed, ticket and
   escrow names kept) *)
Definition fn_with (r : file_names) (γ : gname) (k : nat) (b : bool) : file_names :=
  MkFileNames (fn_cons r) (fn_deed r) (fn_tkt r) (fn_esc r) γ k b.

(* the running claim's instance as the new durable copy's *)
Definition to_copy (r : file_names) : file_names := fn_with r (fn_sync r) (fn_era r) true.

(* THE ERA'S RECORD PREDICATE ([App.app_ok] for the union) *)
Definition union_ok (c : union_gn) (k : nat) (r : file_names) : Prop := fn_era r = k.

(* ===================================================================== *)
(*  3.  THE SHARES, THE REGISTRY, THE COUNTERS, THE CLAIM, THE TOKEN      *)
(* ===================================================================== *)
Section sync.
  Context {Σ : gFunctors} `{!fileAppG Σ}.
  (* THE MACHINE'S [mono_natG] (the header): the only one in scope *)
  Context (HSt : mono_natG Σ).

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
  Definition sync_reg (c : union_gn) (k : nat) (γ : gname) : iProp Σ :=
    k ↪[ugn_reg c]□ γ.

  Global Instance sync_reg_persistent c k γ : Persistent (sync_reg c k γ).
  Proof using . rewrite /sync_reg. apply _. Qed.
  Global Instance sync_reg_timeless c k γ : Timeless (sync_reg c k γ).
  Proof using . rewrite /sync_reg. apply _. Qed.

  Lemma sync_reg_agree c k γ γ' : sync_reg c k γ -∗ sync_reg c k γ' -∗ ⌜γ = γ'⌝.
  Proof using .
    rewrite /sync_reg. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  (* ---- the counters, at the machine's instance ---- *)
  Definition sync_cm_auth (c : union_gn) (k : nat) : iProp Σ :=
    mono_nat_auth_own (ugn_cm c) 1 k.
  Definition sync_cm_lb (c : union_gn) (k : nat) : iProp Σ :=
    mono_nat_lb_own (ugn_cm c) k.
  Definition sync_st_lb (c : union_gn) (k : nat) : iProp Σ :=
    mono_nat_lb_own (ugn_st c) k.
  (* the LOAN's shape: the machine's [start_auth n], at the union's copy of
     its gname ([App.app_born] identifies the two; sync SY3-A3b) *)
  Definition sync_st_auth (c : union_gn) (n : nat) : iProp Σ :=
    mono_nat_auth_own (ugn_st c) 1 n.

  Global Instance sync_cm_lb_persistent c k : Persistent (sync_cm_lb c k).
  Proof using . rewrite /sync_cm_lb. apply _. Qed.
  Global Instance sync_st_lb_persistent c k : Persistent (sync_st_lb c k).
  Proof using . rewrite /sync_st_lb. apply _. Qed.

  (* ---- THE SYNC PART OF THE CLAIM ---- *)

  (* the role's shares: the durable copy's half, the counter's authority
     and the started certificate; or the running claim's quarter and the
     counter's lower bound *)
  Definition sync_role (c : union_gn) (r : file_names) (Ls : list srec) : iProp Σ :=
    if fn_role r
    then (sl_auth (fn_sync r) (1/2) Ls ∗ sync_cm_auth c (fn_era r)
          ∗ sync_st_lb c (fn_era r))%I
    else (sl_auth (fn_sync r) (1/4) Ls ∗ sync_cm_lb c (fn_era r))%I.

  Definition sync_body (c : union_gn) (r : file_names) (av : aview)
      (ls : list fl_line) (Ls : list srec) : iProp Σ :=
    (sync_reg c (fn_era r) (fn_sync r)
     ∗ fl_lb (fgn_cl (ugn_file c)) ls
     ∗ ⌜sync_chain ls Ls⌝
     ∗ ⌜uadm ls (slast Ls) (fcont_of av)⌝
     ∗ sync_role c r Ls)%I.

  Definition sync_claim (c : union_gn) (r : file_names) (av : aview) : iProp Σ :=
    (∃ (ls : list fl_line) (Ls : list srec), sync_body c r av ls Ls)%I.

  Global Instance sync_role_timeless c r Ls : Timeless (sync_role c r Ls).
  Proof using . rewrite /sync_role. destruct (fn_role r); apply _. Qed.
  Global Instance sync_body_timeless c r av ls Ls : Timeless (sync_body c r av ls Ls).
  Proof using . rewrite /sync_body. apply _. Qed.
  Global Instance sync_claim_timeless c r av : Timeless (sync_claim c r av).
  Proof using . rewrite /sync_claim. apply _. Qed.

  Lemma sync_body_intro c r av ls Ls :
    sync_chain ls Ls -> uadm ls (slast Ls) (fcont_of av) ->
    sync_reg c (fn_era r) (fn_sync r) -∗ fl_lb (fgn_cl (ugn_file c)) ls -∗
    sync_role c r Ls -∗ sync_body c r av ls Ls.
  Proof using .
    intros Hc Hw. iIntros "H1 H2 H3". rewrite /sync_body.
    iFrame (Hc Hw) "H1 H2 H3".
  Qed.

  (* ---- THE ERA'S TOKEN ([App.app_tk]), indexed by [gen_id] ---- *)
  Definition union_tk (c : union_gn) (k : nat) : iProp Σ :=
    (∃ (γ : gname) (Ls : list srec),
       sync_reg c (S k) γ ∗ sl_auth γ (1/4) Ls ∗ sync_cm_lb c (S k))%I.

  Global Instance union_tk_timeless c k : Timeless (union_tk c k).
  Proof using . rewrite /union_tk. apply _. Qed.

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
     ([union_ok]), the token, the loan of the started auth at [gen + 1].
     The running lower bound of the counter against the copy's authority
     gives [S gen <= era_o]; the copy's started certificate against the
     loan gives [era_o <= S gen]; the registry pins the lists' names; the
     three shares agree; the half and the counter move into the new copy,
     whose witness is the running claim's.  The old copy's leftovers are
     dropped. *)
  Lemma union_merge_closes (c : union_gn) (r_o r : file_names) (av_o av : aview)
      (gen : nat) :
    fn_role r_o = true -> fn_role r = false -> fn_era r = S gen ->
    sync_claim c r_o av_o -∗ sync_claim c r av -∗ union_tk c gen -∗
    sync_st_auth c (gen + 1) ==∗
      sync_claim c (to_copy r) av ∗ sync_claim c r av ∗ union_tk c gen
      ∗ sync_st_auth c (gen + 1).
  Proof using .
    destruct r_o as [oc od ot oe oγ ok ob]; destruct r as [rc rd rt re rγ rk rb].
    cbn [fn_role fn_era fn_sync to_copy fn_with]. intros -> -> ->.
    iIntros "(%ls_o & %Ls_o & #Hrego & _ & _ & _ & Hro)".
    iIntros "(%ls & %Ls & #Hreg & #Hlb & %Hch & %Hw & Hr)".
    iIntros "(%γ & %Lt & #Hregt & Hqt & #Hcmt) Hst".
    unfold sync_role; cbn [fn_role fn_era fn_sync].
    iDestruct "Hro" as "(Ho & Hcmo & #Hsto)".
    iDestruct "Hr" as "(Hq & #Hcml)".
    iDestruct (mono_nat_lb_own_valid with "Hcmo Hcml") as %[_ Hle1].
    iDestruct (mono_nat_lb_own_valid with "Hst Hsto") as %[_ Hle2].
    assert (ok = S gen) as -> by lia.
    iDestruct (sync_reg_agree with "Hrego Hreg") as %->.
    iDestruct (sync_reg_agree with "Hreg Hregt") as %->.
    iDestruct (sl_auth_agree with "Ho Hq") as %->.
    iDestruct (sl_auth_agree with "Hq Hqt") as %<-.
    iModIntro.
    iSplitL "Ho Hcmo".
    { iExists ls, Ls. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch Hw) "Hreg Hlb Ho Hcmo Hsto". }
    iSplitL "Hq".
    { iExists ls, Ls. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch Hw) "Hreg Hlb Hq Hcml". }
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
     the running claim's BODY, whose list [Ls] it names. *)
  Lemma union_hook_closes (c : union_gn) (r' r : file_names) (av : aview)
      (gen : nat) (ls : list fl_line) (Ls : list srec) (ls' : list fl_line)
      (s : fstate) :
    fn_role r' = true -> fn_era r' = S gen ->
    fn_role r = false -> fn_era r = S gen ->
    last ls' = Some FileDisc.LSync -> fcont_of av = s ->
    (slast Ls).1 <= length ls' ->
    sync_claim c r' av -∗ sync_body c r av ls Ls -∗ union_tk c gen -∗
    fl_lb (fgn_cl (ugn_file c)) ls' ==∗
      sync_claim c r' av ∗ sync_claim c r av ∗ union_tk c gen
      ∗ sl_lb (fn_sync r) (Ls ++ [(length ls', s)]) ∗ sync_cm_lb c (S gen).
  Proof using .
    destruct r' as [gc gd gt ge gγ gk gb]; destruct r as [rc rd rt re rγ rk rb].
    cbn [fn_role fn_era fn_sync]. intros -> -> -> -> Hlast <- Hpos.
    iIntros "(%ls_g & %Ls_g & #Hregg & _ & _ & _ & Hg)".
    iIntros "(#Hreg & #Hlb & %Hch & %Hw & Hr) (%γ & %Lt & #Hregt & Hqt & #Hcmt) #Hlb'".
    unfold sync_role; cbn [fn_role fn_era fn_sync].
    iDestruct "Hg" as "(Hg & Hcmg & #Hstg)".
    iDestruct "Hr" as "(Hq & #Hcml)".
    iDestruct (sync_reg_agree with "Hregg Hreg") as %->.
    iDestruct (sync_reg_agree with "Hreg Hregt") as %->.
    iDestruct (sl_auth_agree with "Hg Hq") as %->.
    iDestruct (sl_auth_agree with "Hq Hqt") as %<-.
    (* the whole list, and the append *)
    iDestruct (sl_auth_join3 with "Hg Hq Hqt") as "Ha".
    iMod (sl_auth_update _ Ls (Ls ++ [(length ls', fcont_of av)]) with "Ha") as "Ha";
      [by apply prefix_app_r |].
    iDestruct (sl_lb_get with "Ha") as "#Hnew".
    iDestruct (sl_auth_split3_1 with "Ha") as "(Hg & Hq & Hqt)".
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
    iModIntro.
    iSplitL "Hg Hcmg".
    { iExists L, (Ls ++ [(length ls', fcont_of av)]).
      unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch' Hw') "Hregg HL Hg Hcmg Hstg". }
    iSplitL "Hq".
    { iExists L, (Ls ++ [(length ls', fcont_of av)]).
      unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch' Hw') "Hreg HL Hq Hcml". }
    iFrame "Hcml Hnew".
    iExists γ, (Ls ++ [(length ls', fcont_of av)]). iFrame "Hregt Hqt Hcmt".
  Qed.

  (* A REDIRECT ROUND'S STEP (design 4.3 item 1, [uadm_redir]): the
     writer's line [LEchoF ws N] is the last of its lower bound [ls_w], and
     the round sets [N] to a chunk subset of it.  The witness moves to the
     new view at the SAME records; the line list grows to cover the
     writer's.  THE POSITION PREMISE [(slast Ls).1 <= length ls_w] (the
     header): the last record is not younger than the writer's line; with
     it the line is at or after the record ([sync_chain_redir_pos]: the
     redirect is not the record's sync line).  Any role: the shares are
     untouched. *)
  Lemma sync_claim_redir_step (c : union_gn) (r : file_names) (av av' : aview)
      (ls : list fl_line) (Ls : list srec) (ls_w : list fl_line) (j : nat)
      (ws : list (list (bv 8))) (N : list (bv 8)) (sel : list nat) :
    ls_w !! j = Some (FileDisc.LEchoF ws N) -> length ls_w = S j ->
    sel_ok (echo_chunks ws) sel ->
    (slast Ls).1 <= length ls_w ->
    fcont_of av' = <[N := subseq (echo_chunks ws) sel]> (fcont_of av) ->
    sync_body c r av ls Ls -∗ fl_lb (fgn_cl (ugn_file c)) ls_w -∗
    ∃ L : list fl_line, sync_body c r av' L Ls.
  Proof using .
    intros Hj Hlen Hsel Hpos Hav'.
    iIntros "(#Hreg & #Hlb & %Hch & %Hw & Hr) #Hlbw".
    iDestruct (fl_lb_lb with "Hlb Hlbw") as %Hcmp.
    iDestruct (fl_lb_join with "Hlb Hlbw") as (L) "[#HL %HL]".
    destruct HL as [HlsL HlswL].
    assert (Hpj : (slast Ls).1 <= j).
    { apply (sync_chain_redir_pos ls ls_w Ls j ws N Hch Hcmp Hj). lia. }
    assert (Hin : FileDisc.LEchoF ws N ∈ drop (slast Ls).1 L).
    { apply elem_of_list_lookup. exists (j - (slast Ls).1). rewrite lookup_drop.
      rewrite (_ : (slast Ls).1 + (j - (slast Ls).1) = j); [| lia].
      exact (prefix_lookup_Some _ _ _ _ Hj HlswL). }
    pose proof (sync_chain_mono ls L Ls HlsL Hch) as Hch'.
    assert (Hw' : uadm L (slast Ls) (fcont_of av')).
    { rewrite Hav'. apply (uadm_redir L (slast Ls) (fcont_of av) ws N sel Hin Hsel).
      exact (uadm_mono ls L (slast Ls) _ HlsL Hw). }
    iExists L. iApply (sync_body_intro c r av' L Ls Hch' Hw' with "Hreg HL Hr").
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
     [sync_chain_shrink]); the dead era's half is dropped. *)
  Lemma sync_claim_rebase (c : union_gn) (r : file_names) (av : aview) (γ : gname)
      (gen : nat) (F : list srec) :
    fn_role r = true ->
    sync_claim c r av -∗ sl_auth γ 1 [] -∗ sync_reg c (S gen) γ -∗
    sl_lb (fn_sync r) F -∗ sync_st_auth c (gen + 1) ==∗
      sync_claim c (fn_with r γ (S gen) true) av
      ∗ sync_claim c (fn_with r γ (S gen) false) av
      ∗ union_tk c gen
      ∗ (∃ (ls : list fl_line) (Ls_c : list srec),
           fl_lb (fgn_cl (ugn_file c)) ls ∗ sl_lb γ Ls_c
           ∗ ⌜F `prefix_of` Ls_c⌝ ∗ ⌜uadm ls (slast F) (fcont_of av)⌝)
      ∗ sync_st_auth c (gen + 1).
  Proof using .
    destruct r as [rc rd rt re rγ rk rb].
    cbn [fn_role fn_era fn_sync fn_with]. intros ->.
    iIntros "(%ls & %Ls_c & _ & #Hlb & %Hch & %Hw & Hr) Hnew #Hreg #HF Hst".
    unfold sync_role; cbn [fn_role fn_era fn_sync].
    iDestruct "Hr" as "(Ho & Hcm & #Hsto)".
    iDestruct (sl_auth_lb_prefix with "Ho HF") as %HFc.
    iDestruct (mono_nat_lb_own_valid with "Hst Hsto") as %[_ Hk].
    (* the fresh list at the copy's *)
    iMod (sl_auth_update γ [] Ls_c with "Hnew") as "Hnew"; [apply prefix_nil |].
    iDestruct (sl_lb_get with "Hnew") as "#Hnlb".
    iDestruct (sl_auth_split3_1 with "Hnew") as "(Hh & Hq & Hqt)".
    (* the counter, and the certificate *)
    iMod (mono_nat_own_update (S gen) with "Hcm") as "[Hcm #Hcml]"; [lia |].
    iDestruct (mono_nat_lb_own_get with "Hst") as "#Hst'".
    rewrite (_ : (gen + 1)%nat = S gen); [| lia].
    iModIntro.
    iSplitL "Hh Hcm".
    { iExists ls, Ls_c. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch Hw) "Hreg Hlb Hh Hcm Hst'". }
    iSplitL "Hq".
    { iExists ls, Ls_c. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
      iFrame (Hch Hw) "Hreg Hlb Hq Hcml". }
    iSplitL "Hqt".
    { iExists γ, Ls_c. iFrame "Hreg Hqt Hcml". }
    iFrame "Hst". iExists ls, Ls_c. iFrame "Hlb Hnlb". iPureIntro. split; [exact HFc |].
    exact (sync_chain_shrink ls Ls_c F _ Hch HFc Hw).
  Qed.

  (* THE BIRTH (design 4.5 "Birth"): era 0's durable copy, from the
     birth's era-0 registration, the half of the fresh empty list, the
     counter's authority at 0 and any lower bound of the line list, at a
     view with no user file.  The started certificate at 0 is free. *)
  Lemma sync_claim_birth (c : union_gn) (r0 : file_names) (av0 : aview)
      (γ0 : gname) (ls : list fl_line) :
    fn_role r0 = true -> fn_era r0 = 0 -> fn_sync r0 = γ0 -> fcontent_of av0 = ∅ ->
    sync_reg c 0 γ0 -∗ sl_auth γ0 (1/2) [] -∗ sync_cm_auth c 0 -∗
    fl_lb (fgn_cl (ugn_file c)) ls ==∗ sync_claim c r0 av0.
  Proof using .
    destruct r0 as [rc rd rt re rγ rk rb].
    cbn [fn_role fn_era fn_sync]. intros -> -> -> Hav.
    iIntros "#Hreg Hh Hcm #Hlb".
    iMod (mono_nat_lb_own_0 (ugn_st c)) as "#Hst".
    assert (Hw : uadm ls (slast []) (fcont_of av0)).
    { rewrite /fcont_of Hav dst_content_empty. exact (uadm_self ls srec0). }
    pose proof (sync_chain_nil ls) as Hch.
    iModIntro. iExists ls, []. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync].
    iFrame (Hch Hw) "Hreg Hlb Hh Hcm Hst".
  Qed.

  (* =================================================================== *)
  (*  5.  VACUITY: THE PREMISES ARE JOINTLY SATISFIABLE                   *)
  (* =================================================================== *)

  (* the merge's: a copy and a running claim at era [S gen], at one list,
     the token, the loan -- all from fresh allocations *)
  Lemma union_merge_closes_sat (gen : nat) (ef : EchoOut.echo_gn)
      (ge gp : gname) (r0 : file_names) :
    ⊢ |==> ∃ (c : union_gn) (r_o r : file_names) (av : aview),
        ⌜fn_role r_o = true /\ fn_role r = false /\ fn_era r = S gen⌝
        ∗ sync_claim c r_o av ∗ sync_claim c r av ∗ union_tk c gen
        ∗ sync_st_auth c (gen + 1).
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO fl_line)))) as (γfl) "Hfl";
      [apply mono_list_auth_valid |].
    iDestruct (fl_auth_lb (ef, γfl) [] with "Hfl") as "[_ #Hlb]".
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γs) "Hs";
      [apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname)) as (γreg) "Hreg".
    iMod (ghost_map_insert_persist (S gen) γs with "Hreg") as "[_ #Hel]";
      [apply lookup_empty |].
    iMod (mono_nat_own_alloc (S gen)) as (γcm) "[Hcm #Hcml]".
    iMod (mono_nat_own_alloc (gen + 1)) as (γst) "[Hst #Hstl]".
    iDestruct (sl_auth_split3_1 γs [] with "Hs") as "(Hh & Hq & Hqt)".
    rewrite (_ : (gen + 1)%nat = S gen); [| lia].
    iModIntro.
    iExists (MkUnionGn (MkFileGn (ef, γfl) ge) gp γst γreg γcm),
      (fn_with r0 γs (S gen) true), (fn_with r0 γs (S gen) false), ∅.
    iSplitR; [iPureIntro; cbn [fn_role fn_era fn_with]; done |].
    assert (Hw : uadm [] (slast []) (fcont_of ∅)).
    { rewrite fcont_of_empty. exact (uadm_self [] srec0). }
    pose proof (sync_chain_nil []) as Hch.
    iSplitL "Hh Hcm".
    { iExists [], []. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync fn_with].
      iFrame (Hch Hw) "Hel Hlb Hh Hcm Hstl". }
    iSplitL "Hq".
    { iExists [], []. unfold sync_body, sync_role; cbn [fn_role fn_era fn_sync fn_with].
      iFrame (Hch Hw) "Hel Hlb Hq Hcml". }
    iFrame "Hst". iExists γs, []. iFrame "Hel Hqt Hcml".
  Qed.

  (* the re-base's: an era-0 copy, a fresh list registered at [S gen], the
     floor at the copy's list, the loan *)
  Lemma sync_claim_rebase_sat (gen : nat) (ef : EchoOut.echo_gn)
      (ge gp : gname) (r0 : file_names) :
    ⊢ |==> ∃ (c : union_gn) (r : file_names) (av : aview) (γ : gname) (F : list srec),
        ⌜fn_role r = true⌝
        ∗ sync_claim c r av ∗ sl_auth γ 1 [] ∗ sync_reg c (S gen) γ
        ∗ sl_lb (fn_sync r) F ∗ sync_st_auth c (gen + 1).
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO fl_line)))) as (γfl) "Hfl";
      [apply mono_list_auth_valid |].
    iDestruct (fl_auth_lb (ef, γfl) [] with "Hfl") as "[_ #Hlb]".
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γ0) "H0";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γ) "Hnew";
      [apply mono_list_auth_valid |].
    iMod (ghost_map_alloc_empty (K := nat) (V := gname)) as (γreg) "Hreg".
    iMod (ghost_map_insert_persist 0 γ0 with "Hreg") as "[Hreg #H0el]";
      [apply lookup_empty |].
    iMod (ghost_map_insert_persist (S gen) γ with "Hreg") as "[_ #Hel]";
      [by rewrite lookup_insert_ne |].
    iMod (mono_nat_own_alloc 0) as (γcm) "[Hcm _]".
    iMod (mono_nat_own_alloc (gen + 1)) as (γst) "[Hst _]".
    iDestruct (sl_auth_split3_1 γ0 [] with "H0") as "(Hh & _ & _)".
    iDestruct (sl_lb_get with "Hh") as "#HF".
    iMod (sync_claim_birth (MkUnionGn (MkFileGn (ef, γfl) ge) gp γst γreg γcm)
            (fn_with r0 γ0 0 true) ∅ γ0 [] with "H0el Hh Hcm Hlb") as "Hcl";
      [reflexivity | reflexivity | reflexivity
      | rewrite /fcontent_of /aents lookup_empty; reflexivity |].
    iModIntro.
    iExists (MkUnionGn (MkFileGn (ef, γfl) ge) gp γst γreg γcm),
      (fn_with r0 γ0 0 true), ∅, γ, [].
    iSplitR; [done |]. iFrame "Hcl Hnew Hel HF Hst".
  Qed.
End sync.

(* ===================================================================== *)
(*  6.  THE HOOK FAMILY ([App.app_hk]), over an abstract claim, and at    *)
(*      [file_pred]                                                       *)
(* ===================================================================== *)
Section union_hk.
  Context {Σ : gFunctors} `{!fileAppG Σ, !invGS Σ, !fsTopG Σ}.
  Context (HSt : mono_natG Σ).

  (* the design's [Hk c k Q]: both instances at the era [S k], the guest
     half of the top map, the new durable copy and the running claim at
     one map, the token; everything back, and [Q] *)
  Definition union_hk (A : union_gn -> file_names -> aview -> iProp Σ)
      (c : union_gn) (k : nat) (Q : iProp Σ) : iProp Σ :=
    (∀ (gt : gname) (I : gmap Z fs_node) (r r' : file_names),
       ⌜fn_era r = S k⌝ -∗ ⌜fn_era r' = S k⌝ -∗
       ghost_map_auth gt (1/2) I -∗
       ▷ A c r' (abs_view I) -∗ ▷ A c r (abs_view I) -∗
       union_tk HSt c k ={∅}=∗
         ghost_map_auth gt (1/2) I ∗ ▷ A c r' (abs_view I) ∗ ▷ A c r (abs_view I)
         ∗ union_tk HSt c k ∗ Q)%I.
End union_hk.

Section union_hk_file.
  Context {Σ : gFunctors} `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)),
            !fileAppG Σ, !invGS Σ, !fsTopG Σ}.

  Definition union_hk_file (HSt : mono_natG Σ) (c : union_gn) (k : nat)
      (Q : iProp Σ) : iProp Σ :=
    union_hk HSt (fun c => file_pred (fgn_cl (ugn_file c))) c k Q.
End union_hk_file.
