(* ===================================================================== *)
(*  EchoLinks.v -- THE CONSOLE LINKS AS ONE PERSISTENT LAW                *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM: DESIGN OF RECORD";        *)
(*   lane IO-LEAF, decision D1.)                                          *)
(*                                                                       *)
(*  [EchoOut]'s five links are stated under the boot record's four        *)
(*  equations ([riscv_out_res = eout] and its three siblings), which the  *)
(*  top theorem fixes and no PROGRAM file may name: the U tier sits below *)
(*  the record and knows nothing about which application it is running.   *)
(*  So the links travel to the programs the way the write DEPOSIT does    *)
(*  today ([UkSh.sh_deps], [UkInit.init_deps]) -- as ONE PERSISTENT       *)
(*  RESOURCE a program takes as a premise and spends per byte:            *)
(*                                                                       *)
(*    [echo_links T γ] -- the six links as closed [□] wands, mentioning   *)
(*      the era's ghosts ([era_pin], [turn], [ps_lb], [cs_lb], [inp_lb],    *)
(*      [dl_cnt], [read_ret]) and the kernel's own console contracts      *)
(*      ([WpUart.out_link] / [read_link]) and NOTHING of the record;      *)
(*    [echo_links_holds] -- the entailment, proved where the equations    *)
(*      are in scope, i.e. exactly where [UInitBoot.echo_Hinit_boot]      *)
(*      already has them.                                                *)
(*                                                                       *)
(*  WHY A FILE OF ITS OWN and not a section of [EchoOut.v]: the law is a  *)
(*  PROGRAM-side interface and it changes with the programs, while        *)
(*  [EchoOut.v] is the claim.  A sibling file also keeps the two lanes    *)
(*  that touch them apart.                                               *)
(*                                                                       *)
(*  THE BUNDLE IS NOT CLOSED, and the six PROJECTIONS below are what      *)
(*  every consumer goes through, so a seventh link costs the consumers    *)
(*  nothing -- the fifth, [echo_link_pro] (PROLOGUE-ALTS-2's choice       *)
(*  byte), and the sixth, [echo_link_rd_taint] (lane IO-LEAF, M5),        *)
(*  arrived exactly that way.                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import EchoOut.
(* as in EchoDisc / EchoOutPure / EchoOut: the Sail imports leave
   string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.



(* ===================================================================== *)
(*  THE WRITER'S PLACE AT A LINE BOUNDARY (lane IO-LEAF, M6a)            *)
(*                                                                       *)
(*  The era's write credential ([EchoOut.turn] and the three lower       *)
(*  bounds) travels on the console lease, and the lease is handed on at  *)
(*  a LINE BOUNDARY.  WHAT A BOUNDARY IS is the PARSE of the era's input *)
(*  [I : list (bv 8)] and not a count of it: the input has stopped at a  *)
(*  newline ([rest_of I = []]) and the transcript owes one block per     *)
(*  COMPLETE line ([nlines I]).  A delivered count could only MEAN a     *)
(*  boundary while every round typed the same line; the input itself     *)
(*  says WHICH line each round typed, which is exactly what the          *)
(*  block's good alternative reads ([EchoDisc.line_alts_of (last_ws I)]).*)
(*                                                                       *)
(*  What a holder of the lease may do there is still not a function of   *)
(*  [I]: the stage [P] the writer stands at depends on which             *)
(*  alternatives the transcript has taken, and the prologue rounds [ps]  *)
(*  are free.  So the credential quantifies [ps], [cs] and [P] and pins  *)
(*  them with ONE of the three PURE shapes below.                        *)
(*                                                                       *)
(*    [wr_pro]   the round's PROLOGUE alternative is still open: the     *)
(*               next byte out is the round's choice byte, and for the   *)
(*               shell that byte is the '$' of its prompt                *)
(*               ([EchoDisc.pro_alts !!! 0]).  Round 0 at [I = []] is    *)
(*               this shape, with [ps = []], [cs = []] and [P = 18].     *)
(*    [wr_blk]   the round is settled and the LINE just echoed still     *)
(*               owes its block: the next byte out is that block's       *)
(*               first ([line_alts_of (last_ws I) !!! a]), and a shell   *)
(*               whose child recorded no choice writes its prompt there  *)
(*               (alternative 2).                                        *)
(*    [wr_open]  both are written: the writer stands at the start of the *)
(*               block the NEXT line will owe and can write nothing      *)
(*               until the input grows ([inp_lb] is what forbids it).    *)
(*                                                                       *)
(*  The two prompt shapes are [wr_owed]; the shell's "$ " takes either   *)
(*  of them to [wr_open], and the read of a line whose BODY is [l]       *)
(*  takes [wr_open] at [I] to [wr_blk] at [I ++ l ++ [wl_nl]].  Those    *)
(*  three steps are all the parsing the shell's command loop needs.      *)
(* ===================================================================== *)

Definition wr_pro (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ cs !!! (nlines I - 1)%nat = 3%nat)
  /\ ~ pro_done (pro_from (pro_idx cs (nlines I)) ps)
  /\ P = length (proc_stream ps cs I).

Definition wr_blk (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin ps cs I
  /\ rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before ps cs I).

Definition wr_open (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (pro_idx cs (nlines I) < pro_rounds ps)%nat
  /\ P = length (proc_stream ps cs I).

Definition wr_owed (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_pro ps cs I P \/ wr_blk ps cs I P.

(* ...AND THE HALF-WRITTEN PROMPT: the choice byte is out, the space is
   not, and what says so is that the round's stream is exactly one byte
   longer than the writer's cursor and that that byte is the space. *)
Definition wr_sp (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_open ps cs I (S P)
  /\ proc_stream ps cs I !! P = Some (u_prompt !!! 1%nat).

(* ---- the literals, by computation ---- *)
Lemma wr_prompt_len : length u_prompt = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma wr_pro_alts_0 : pro_alts !!! 0%nat = u_prompt.
Proof. reflexivity. Qed.

(* ALTERNATIVE 2 IS THE PROMPT AT EVERY LINE -- the child recorded no
   choice, so the block is what sh writes and not what was typed. *)
Lemma wr_line_alts_2 (ws : list (list (bv 8))) :
  line_alts_of ws !!! 2%nat = u_prompt.
Proof. reflexivity. Qed.

Lemma wr_prompt_head : u_prompt !! 0%nat = Some (u_prompt !!! 0%nat).
Proof. vm_compute. reflexivity. Qed.

Lemma wr_prompt_tail : u_prompt !! 1%nat = Some (u_prompt !!! 1%nat).
Proof. vm_compute. reflexivity. Qed.

(* ---- what [wr_blk] says about the input ---- *)
(* A block is owed only where a line has been completed, so the input is
   not empty -- which is what the block-first write link asks for. *)
Lemma wr_blk_nonnil (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk ps cs I P -> I <> [].
Proof.
  intros (_ & _ & Hn & _) Heq. rewrite Heq nlines_nil in Hn. discriminate.
Qed.

(* ---- the two cut facts a body read spends, stated once -------------- *)
(* A run with no newline in it adds no complete line and IS the remainder
   after the last one.  Both are [LineWords.wl_cut_app_nonl] read at its
   two projections. *)
Lemma bodies_of_app_nonl (I l : list (bv 8)) :
  wl_nl ∉ l -> bodies_of (I ++ l) = bodies_of I.
Proof.
  intro Hl.
  assert (Hc : wl_cut (I ++ l) = (bodies_of I, rest_of I ++ l))
    by exact (wl_cut_app_nonl I l Hl).
  rewrite /bodies_of Hc. by cbn [fst].
Qed.

Lemma nlines_app_nonl (I l : list (bv 8)) :
  wl_nl ∉ l -> nlines (I ++ l) = nlines I.
Proof. intro Hl. by rewrite /nlines (bodies_of_app_nonl I l Hl). Qed.

Lemma rest_of_app_nonl (I l : list (bv 8)) :
  rest_of I = [] -> wl_nl ∉ l -> rest_of (I ++ l) = l.
Proof.
  intros Hr Hl.
  assert (Hc : wl_cut (I ++ l) = (bodies_of I, rest_of I ++ l))
    by exact (wl_cut_app_nonl I l Hl).
  rewrite {1}/rest_of Hc. cbn [snd]. by rewrite Hr.
Qed.

(* ===================================================================== *)
(*  THE PROLOGUE GROWS BY EXACTLY ITS ALTERNATIVE.  [pro_of_snoc_head]   *)
(*  gives the prefix; the shell needs the LENGTH, because that is what   *)
(*  pins the stage its second prompt byte is written at.                 *)
(* ===================================================================== *)
Lemma pro_of_open_snoc_eq (ps : list nat) (a : nat) :
  ~ pro_done ps ->
  pro_of (ps ++ [a]) = pro_of ps ++ pro_alts !!! a.
Proof. intros Hnd. by rewrite (pro_of_open_app ps [a] Hnd) pro_of_singleton. Qed.

(* ...AND THE BLOCK AT A ROUND'S HEAD ENDS IN THAT PROLOGUE, whether the
   round is the transcript's first ([I = []], the block IS the prologue) or
   one a shell's fork panic opened ([cs !!! (nlines I - 1) = 3], the block
   is that alternative and then the prologue).  The PREFIX does not read
   [ps] at all -- and, since sh's panic line is a CONSTANT, it does not
   read the line that was typed either ([EchoOutPure.pending_at_round_pre])
   -- which is what makes the choice byte's effect a pure append. *)
Lemma pending_at_round_snoc (ps cs : list nat) (I : list (bv 8)) (a : nat) :
  rest_of I = [] ->
  (I = [] \/ cs !!! (nlines I - 1)%nat = 3%nat) ->
  ~ pro_done (pro_from (pro_idx cs (nlines I)) ps) ->
  (pro_idx cs (nlines I) <= pro_rounds ps)%nat ->
  pending_at (ps ++ [a]) cs I = pending_at ps cs I ++ pro_alts !!! a.
Proof.
  intros Hm Hr Hnd Hle.
  rewrite (pending_at_round_pre (ps ++ [a]) cs I Hm Hr)
          (pending_at_round_pre ps cs I Hm Hr)
          (pro_from_snoc_le (pro_idx cs (nlines I)) ps a Hle)
          (pro_of_open_snoc_eq _ a Hnd).
  by rewrite app_assoc.
Qed.


(* ===================================================================== *)
(*  THE ROUND'S BANNER, STILL OWED (lane IO-LEAF, M6a(2); PROLOGUE-ALTS-3). *)
(*                                                                       *)
(*  [wr_pro] is where the round's next LETTER goes, and at the head of    *)
(*  a round that letter is /init's banner ([EchoDisc.pro_alts !!! 3]) --  *)
(*  or, when /init's console is shut and it prints nothing, the shell's   *)
(*  bare prompt ([pro_alts !!! 0]).  That is the shape the console lease  *)
(*  carries between a child's exit and the fork that follows it --        *)
(*  /init's own loop head -- and the one thing it says beyond [wr_pro]'s  *)
(*  side conditions is WHICH open prologue it is in: [j] failed           *)
(*  sub-rounds ([EchoDisc.pro_fail j]), so the banner starts             *)
(*  [pro_round * j] bytes into the round's block.  The banner's first     *)
(*  byte FILES the letter ([echo_link_pro] at [a = 3]); the rest are      *)
(*  ordinary writes against the bound that returns                        *)
(*  ([EchoOut.proc_stream_round_banner_open]).                            *)
(* ===================================================================== *)
(* the round-opening block's prefix: sh's panic line, unless this is the
   head of the transcript.  It does NOT depend on [cs] -- the argument is
   kept so that every shape reads the same way. *)
Definition wr_pre (cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then [] else alt_panic.

Definition wr_ban (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ cs !!! (nlines I - 1)%nat = 3%nat)
  /\ (exists j : nat,
        pro_from (pro_idx cs (nlines I)) ps = pro_fail j
        /\ P = (length (proc_before ps cs I) + length (wr_pre cs I)
                + pro_round * j)%nat).

(* THE BANNER-OWED CREDENTIAL IS THE ROUND'S CHOICE SHAPE: the open round
   predicts nothing past its [j] failed sub-rounds, so the cursor stands
   exactly at the round's next letter. *)
Lemma wr_ban_pro (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban ps cs I P -> wr_pro ps cs I P.
Proof.
  intros (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)).
  rewrite /wr_pro. split_and!; try assumption.
  - rewrite Hopen. exact (pro_done_fail j).
  - rewrite /proc_stream (length_app (proc_before ps cs I) (pending_at ps cs I))
            (pending_at_round_pre ps cs I Hm Hr)
            (length_app (wr_pre cs I)
               (pro_of (pro_from (pro_idx cs (nlines I)) ps)))
            Hopen pro_of_fail_length HP.
    lia.
Qed.

(* ...and the shape the banner's first byte leaves: the letter filed, the
   cursor one in.  The stream strictly below [I] does not read the new
   letter, because every block below it stands at a round [pro_pin] has
   already settled. *)
Lemma wr_ban_low (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban ps cs I P ->
  proc_before (ps ++ [3%nat]) cs I = proc_before ps cs I.
Proof.
  intros (Hpin & _ & _ & _ & _).
  symmetry. apply proc_before_ext. intros J HJ Hne.
  apply (pending_at_ps_ext ps (ps ++ [3%nat]) cs J); [by eexists |].
  exact (pro_pin_at ps cs I (nlines J) Hpin (nstarted_strict J I HJ Hne)).
Qed.

Lemma wr_ban_filed (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban ps cs I P ->
  exists j : nat,
    pro_from (pro_idx cs (nlines I)) (ps ++ [3%nat]) = pro_fail j ++ [3%nat]
    /\ P = (length (proc_before (ps ++ [3%nat]) cs I) + length (wr_pre cs I)
            + pro_round * j)%nat.
Proof.
  intros Hw. pose proof Hw as (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)).
  exists j. split.
  - rewrite (pro_from_snoc_le _ ps 3%nat (pro_pin_idx_le ps cs I Hpin)).
    by rewrite Hopen.
  - by rewrite (wr_ban_low ps cs I P Hw).
Qed.

(* every banner byte is where the stream of the FILED round says *)
Lemma wr_ban_byte (ps cs : list nat) (I : list (bv 8)) (P i : nat) (b : bv 8) :
  wr_ban ps cs I P -> u_banner !! i = Some b ->
  proc_stream (ps ++ [3%nat]) cs I !! (P + i)%nat = Some b.
Proof.
  intros Hw Hb. pose proof Hw as (Hpin & Hm & Hdv & Hr & _).
  destruct (wr_ban_filed ps cs I P Hw) as (j & Hopen & HP).
  rewrite HP /wr_pre.
  exact (proc_stream_round_banner_open (ps ++ [3%nat]) cs I j i b Hm Hr Hopen Hb).
Qed.

(* ...and after the last banner byte the round is at its prompt: [wr_pro]
   with the banner filed, [length u_banner] bytes on *)
Lemma wr_ban_done (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban ps cs I P -> wr_pro (ps ++ [3%nat]) cs I (P + length u_banner)%nat.
Proof.
  intros Hw. pose proof Hw as (Hpin & Hm & Hdv & Hr & (j & Hopen & HP)).
  assert (Hle : (pro_idx cs (nlines I) <= pro_rounds ps)%nat)
    by exact (pro_pin_idx_le ps cs I Hpin).
  assert (Hnd : ~ pro_done (pro_from (pro_idx cs (nlines I)) ps))
    by (rewrite Hopen; exact (pro_done_fail j)).
  rewrite /wr_pro. split_and!.
  - exact (pro_pin_mono ps (ps ++ [3%nat]) cs I ltac:(by eexists) Hpin).
  - exact Hm.
  - exact Hdv.
  - exact Hr.
  - rewrite (pro_from_snoc_le _ ps 3%nat Hle) Hopen.
    apply pro_done_cont. rewrite Forall_app. split; [exact (pro_fail_cont j) |].
    constructor; [by right | constructor].
  - rewrite /proc_stream
            (length_app (proc_before (ps ++ [3%nat]) cs I)
               (pending_at (ps ++ [3%nat]) cs I))
            (wr_ban_low ps cs I P Hw)
            (pending_at_round_snoc ps cs I 3%nat Hm Hr Hnd Hle)
            (length_app (pending_at ps cs I) (pro_alts !!! 3%nat))
            (pending_at_round_pre ps cs I Hm Hr)
            (length_app (wr_pre cs I)
               (pro_of (pro_from (pro_idx cs (nlines I)) ps)))
            Hopen pro_of_fail_length pro_alts_3 HP.
    lia.
Qed.

Lemma wr_ban_head (b : bv 8) :
  u_banner !! 0%nat = Some b -> pro_alts !!! 3%nat !! 0%nat = Some b.
Proof. by rewrite pro_alts_3. Qed.

(* THE TRANSCRIPT'S HEAD: nothing typed, nothing filed, the cursor at 0. *)
Lemma wr_ban_round0 : wr_ban [] [] [] 0%nat.
Proof.
  rewrite /wr_ban. split_and!.
  - apply pro_pin_nil.
  - exact rest_of_nil.
  - by rewrite nlines_nil.
  - by left.
  - exists 0%nat. split.
    + by rewrite nlines_nil pro_fail_0.
    + rewrite proc_before_nil /wr_pre.
      case_decide as Hd; [| by destruct (Hd eq_refl)].
      cbn [length]. lia.
Qed.

(* ---- a run of inputs that owe nothing leaves the stream alone ------- *)
(* The replacement for the old count-based gap law: what the writer needs
   is not "sixteen counts with an empty block" but "every PROPER PREFIX of
   the run owes nothing", which is exactly the recursion's shape. *)
Lemma proc_before_from_gap (ps cs : list nat) (pre k : list (bv 8)) :
  (forall J : list (bv 8), J `prefix_of` k -> J <> k ->
     pending_at ps cs (pre ++ J) = []) ->
  proc_before_from ps cs pre k = [].
Proof.
  revert pre. induction k as [| b k IH]; intros pre Hj; [reflexivity |].
  assert (H0 : pending_at ps cs pre = []).
  { rewrite -(app_nil_r pre). apply Hj; [apply prefix_nil | discriminate]. }
  cbn [proc_before_from]. rewrite H0 app_nil_l.
  apply IH. intros J HJ Hne.
  rewrite (epu_app_snoc pre b J). apply Hj.
  - destruct HJ as [z ->]. exists z. by cbn [app].
  - intros Heq. apply Hne. by injection Heq.
Qed.

(* THE STREAM DOES NOT MOVE ACROSS A LINE'S ECHO.  The bytes of a body are
   echoed one at a time and each of them leaves the transcript owing
   nothing ([pending_at] is [] wherever the input stops mid-line), so the
   whole read contributes exactly the block that was owed AT [I]. *)
Lemma proc_before_line (ps cs : list nat) (I l : list (bv 8)) :
  rest_of I = [] -> wl_nl ∉ l ->
  proc_before ps cs (I ++ l ++ [wl_nl]) = proc_stream ps cs I.
Proof.
  intros Hr Hl. rewrite proc_before_app /proc_stream. f_equal.
  destruct l as [| b l'].
  - cbn [app proc_before_from]. by rewrite app_nil_r.
  - destruct (wl_nonl_cons b l' Hl) as [Hb Hl'].
    assert (Hgap : proc_before_from ps cs (I ++ [b]) (l' ++ [wl_nl]) = []).
    { apply proc_before_from_gap. intros J HJ Hne.
      assert (HJl : J `prefix_of` l').
      { rewrite -(epu_removelast_snoc l' wl_nl).
        exact (epu_prefix_of_removelast J (l' ++ [wl_nl]) HJ Hne). }
      assert (HJn : wl_nl ∉ J).
      { intro Hin. destruct HJl as [z ->].
        apply Hl'. apply elem_of_app. by left. }
      assert (Hshape : (I ++ [b]) ++ J = I ++ (b :: J)) by apply epu_app_snoc.
      rewrite Hshape /pending_at.
      rewrite decide_False;
        [| intros Hq; by destruct (app_eq_nil I (b :: J) Hq) as [_ Hc]].
      rewrite decide_False; [reflexivity |].
      rewrite (rest_of_app_nonl I (b :: J) Hr (wl_nonl_cons_2 b J Hb HJn)).
      discriminate. }
    cbn [app proc_before_from]. rewrite Hgap app_nil_r. reflexivity.
Qed.

Lemma pro_rounds_one : pro_rounds [0%nat] = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  THE THREE STEPS.                                                     *)
(* ===================================================================== *)

(* (1) THE ROUND'S CHOICE BYTE, at an open prologue: filing alternative 0 *)
(*     appends the prompt's two bytes to the round's block, so the        *)
(*     writer's cursor is one short of a stream two longer.               *)
Lemma wr_pro_dollar (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro ps cs I P -> wr_sp (ps ++ [0%nat]) cs I (S P).
Proof.
  intros (Hpin & Hm & Hdv & Hr & Hnd & HP).
  assert (Hle : (pro_idx cs (nlines I) <= pro_rounds ps)%nat)
    by exact (pro_pin_idx_le ps cs I Hpin).
  assert (Hpre : ps `prefix_of` (ps ++ [0%nat])) by by eexists.
  (* the stream strictly below [I], byte for byte *)
  assert (Hlow : proc_before (ps ++ [0%nat]) cs I = proc_before ps cs I).
  { symmetry. apply proc_before_ext. intros J HJ Hne.
    apply (pending_at_ps_ext ps (ps ++ [0%nat]) cs J Hpre).
    exact (pro_pin_at ps cs I (nlines J) Hpin (nstarted_strict J I HJ Hne)). }
  assert (Hup : proc_stream (ps ++ [0%nat]) cs I
                = proc_stream ps cs I ++ u_prompt).
  { rewrite {1}/proc_stream Hlow
      (pending_at_round_snoc ps cs I 0%nat Hm Hr Hnd Hle) wr_pro_alts_0.
    by rewrite /proc_stream app_assoc. }
  assert (Hlen : length (proc_stream (ps ++ [0%nat]) cs I) = S (S P)).
  { rewrite Hup (length_app (proc_stream ps cs I) u_prompt) wr_prompt_len. lia. }
  split.
  - rewrite /wr_open. split_and!.
    + exact (pro_pin_mono ps (ps ++ [0%nat]) cs I Hpre Hpin).
    + exact Hm.
    + exact Hdv.
    + rewrite pro_rounds_app pro_rounds_one. lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [| lia].
    replace (S P - length (proc_stream ps cs I))%nat with 1%nat by lia.
    exact wr_prompt_tail.
Qed.

(* (2) THE LINE'S CHOICE BYTE, at a settled round whose last line still    *)
(*     owes its block: filing alternative 2 -- the child recorded no       *)
(*     choice -- makes the block the prompt itself, whatever was typed.    *)
Lemma wr_blk_dollar (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk ps cs I P -> wr_sp ps (cs ++ [2%nat]) I (S P).
Proof.
  intros Hw. pose proof (wr_blk_nonnil ps cs I P Hw) as Hne.
  pose proof Hw as (Hpin & Hm & Hdv & HP).
  assert (Hpre : cs `prefix_of` (cs ++ [2%nat])) by by eexists.
  assert (Hnew : (cs ++ [2%nat]) !!! length cs = 2%nat).
  { rewrite list_lookup_total_alt lookup_app_r; [| lia].
    by rewrite Nat.sub_diag. }
  assert (Hold : forall j, (j < length cs)%nat ->
                   (cs ++ [2%nat]) !!! j = cs !!! j)
    by (intros j Hj; exact (lookup_total_prefix cs (cs ++ [2%nat]) j Hpre Hj)).
  assert (Hidx : forall j, (j <= length cs)%nat ->
                   pro_idx (cs ++ [2%nat]) j = pro_idx cs j).
  { apply (pro_idx_ext (cs ++ [2%nat]) cs (length cs)).
    intros j Hj. exact (Hold j Hj). }
  assert (Hstar : nstarted I = S (length cs))
    by (rewrite (nstarted_rest_nil I Hm); lia).
  (* the stream strictly below [I] does not read the new choice *)
  assert (Hlow : proc_before ps (cs ++ [2%nat]) I = proc_before ps cs I).
  { symmetry.
    apply (proc_before_cs_prefix ps ps cs (cs ++ [2%nat]) I
             ltac:(reflexivity) Hpre Hpin).
    rewrite (nlines_removelast I Hm). lia. }
  assert (Hpend : pending_at ps (cs ++ [2%nat]) I = u_prompt).
  { rewrite /pending_at decide_False; [| exact Hne].
    rewrite decide_True; [| exact Hm]. rewrite /alt_cont.
    replace (nlines I - 1)%nat with (length cs) by lia.
    rewrite Hnew. case_decide as H3; [exfalso; lia |].
    by rewrite wr_line_alts_2 app_nil_r. }
  assert (Hup : proc_stream ps (cs ++ [2%nat]) I = proc_before ps cs I ++ u_prompt)
    by (rewrite /proc_stream Hlow Hpend; reflexivity).
  assert (Hlen : length (proc_stream ps (cs ++ [2%nat]) I) = S (S P)).
  { rewrite Hup (length_app (proc_before ps cs I) u_prompt) wr_prompt_len. lia. }
  split.
  - rewrite /wr_open. split_and!.
    + intros q Hq. rewrite (Hidx q ltac:(lia)). exact (Hpin q Hq).
    + exact Hm.
    + rewrite (length_app cs [2%nat]) Hdv. cbn [length]. lia.
    + rewrite Hdv
        (pro_idx_Sne (cs ++ [2%nat]) (length cs)
           ltac:(rewrite Hnew; discriminate))
        (Hidx (length cs) ltac:(lia)).
      pose proof (Hpin (length cs) ltac:(lia)). lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [| lia].
    replace (S P - length (proc_before ps cs I))%nat with 1%nat by lia.
    exact wr_prompt_tail.
Qed.

(* (3) THE SPACE, and the state it leaves: the second prompt byte is the   *)
(*     last of the round's block, so the cursor lands exactly on the       *)
(*     stream's end -- [wr_open].                                          *)
Lemma wr_sp_open (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_sp ps cs I P -> wr_open ps cs I (S P).
Proof. by intros [H _]. Qed.

(* (4) THE READ: the line's BODY [l] and its newline are echoed, the       *)
(*     transcript owes that line's block and nothing has been written, so  *)
(*     the cursor has not moved and the shape is [wr_blk] at the longer    *)
(*     input.  Nothing here counts bytes -- the body may be any length.    *)
Lemma wr_open_read (ps cs : list nat) (I : list (bv 8)) (P : nat)
      (l : list (bv 8)) :
  wr_open ps cs I P -> wl_nl ∉ l -> wr_blk ps cs (I ++ l ++ [wl_nl]) P.
Proof.
  intros (Hpin & Hm & Hdv & Hrd & HP) Hl.
  assert (Hassoc : I ++ l ++ [wl_nl] = (I ++ l) ++ [wl_nl])
    by (by rewrite app_assoc).
  assert (Hnl : nlines (I ++ l) = nlines I) by exact (nlines_app_nonl I l Hl).
  assert (Hlines : nlines (I ++ l ++ [wl_nl]) = S (length cs))
    by (rewrite Hassoc nlines_snoc_nl Hnl Hdv; reflexivity).
  rewrite /wr_blk. split_and!.
  - intros q Hq. rewrite Hassoc nstarted_snoc Hnl Hdv in Hq.
    destruct (decide (q < length cs)%nat) as [Hlt | Hge].
    + apply Hpin. rewrite (nstarted_rest_nil I Hm) Hdv. exact Hlt.
    + assert (Hqe : q = length cs) by lia.
      rewrite Hqe -Hdv. exact Hrd.
  - rewrite Hassoc. exact (rest_of_snoc_nl (I ++ l)).
  - exact Hlines.
  - rewrite (proc_before_line ps cs I l Hm Hl). exact HP.
Qed.

(* ===================================================================== *)
(*  THE DISCIPLINE LEMMA (PROLOGUE-ALTS-3, deliverable 3): AN UNTAINTED    *)
(*  INPUT PAST A BOUNDARY MEANS THE BOUNDARY'S PROMPT WAS WRITTEN.         *)
(*                                                                       *)
(*  The claim says so (an echo past a boundary folds the WHOLE block --    *)
(*  prompt included -- into the transcript, [EchoOut.D_app]), and the     *)
(*  read hands the reader the two things that let it be spent without     *)
(*  opening any claim: a persistent lower bound of the writer's cursor at *)
(*  the end of every block the log's echoes closed ([EchoOut.turn_lb])    *)
(*  and the stage facts that make that stream computable from the         *)
(*  reader's own bounds ([EchoOut.rd_stage]).  A holder of the WRITER's   *)
(*  half whose credential says the block's prompt is not yet out          *)
(*  ([wr_owed]) then has a cursor strictly BELOW that bound, and          *)
(*  [EchoOut.turn_lb_le] refutes it.  In xv6 terms: the shell whose fd 2  *)
(*  is shut never printed its prompt, so no disciplined line arrives on   *)
(*  its fd 0 -- a read that delivers one is the taint.                    *)
(*                                                                       *)
(*  WHAT USED TO BE [n < m] IS NOW [I ⊑ I0] WITH [I <> I0]: the reader's  *)
(*  input strictly extends the writer's boundary.  Lengths would do as    *)
(*  well arithmetically and say nothing about the bytes; the prefix is    *)
(*  what the era's two lower bounds actually give ([inp_lb_cmp]).         *)
(* ===================================================================== *)

(* THE LINE'S BLOCK IS OWED, and the reader's echoes closed it: the block  *)
(* is a whole alternative OF THE LINE THAT WAS TYPED, of which the writer  *)
(* has at most [d] bytes out.                                              *)
Lemma wr_blk_read_refute (ps cs ps0 cs0 : list nat) (I I0 : list (bv 8))
      (P d : nat) :
  wr_blk ps cs I P ->
  cs `prefix_of` cs0 ->
  (d < length (line_alts_of (last_ws I) !!! (cs0 !!! length cs)))%nat ->
  I `prefix_of` I0 -> I <> I0 -> rd_stage ps0 cs0 I0 ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (length (proc_before ps0 cs0 I0) <= P + d)%nat -> False.
Proof.
  intros Hw Hcs Hd HI Hne (HFps0 & HFcs0 & Hpin0 & Hbnd0) Hps Hle.
  pose proof (wr_blk_nonnil ps cs I P Hw) as Hnil.
  pose proof Hw as (Hpin & Hm & Hdv & HP).
  assert (Hstar : nstarted I = S (length cs))
    by (rewrite (nstarted_rest_nil I Hm); lia).
  assert (Hb1 : (nlines (removelast I) <= length cs)%nat)
    by (rewrite (nlines_removelast I Hm); lia).
  destruct Hcs as [z Hz].
  (* the reader's pin, read at the writer's own line list *)
  assert (Hpin0c : pro_pin ps0 cs I).
  { intros q Hq.
    rewrite -(pro_idx_app_le cs z q ltac:(lia)) -Hz.
    apply Hpin0. pose proof (nstarted_strict I I0 HI Hne). lia. }
  (* the stream strictly below the block is the writer's *)
  assert (Hlow : proc_before ps0 cs0 I = proc_before ps cs I).
  { destruct Hps as [Hps | Hps].
    - symmetry.
      exact (proc_before_cs_prefix ps ps0 cs cs0 I Hps ltac:(by eexists)
               Hpin Hb1).
    - transitivity (proc_before ps0 cs I).
      + symmetry.
        exact (proc_before_cs_prefix ps0 ps0 cs cs0 I ltac:(reflexivity)
                 ltac:(by eexists) Hpin0c Hb1).
      + exact (proc_before_cs_prefix ps0 ps cs cs I Hps ltac:(reflexivity)
                 Hpin0c Hb1). }
  (* the block the reader's echoes closed is a whole alternative *)
  assert (Hpend : (length (line_alts_of (last_ws I) !!! (cs0 !!! length cs))
                   <= length (pending_at ps0 cs0 I))%nat).
  { rewrite /pending_at decide_False; [| exact Hnil].
    rewrite decide_True; [| exact Hm]. rewrite /alt_cont.
    rewrite -(last_ws_lta I).
    replace (nlines I - 1)%nat with (length cs) by lia.
    rewrite (length_app (line_alts_of (last_ws I) !!! (cs0 !!! length cs)) _).
    apply Nat.le_add_r. }
  assert (Hmono : (length (proc_stream ps0 cs0 I)
                   <= length (proc_before ps0 cs0 I0))%nat)
    by (apply prefix_length, (proc_stream_before ps0 cs0 I I0 HI Hne)).
  rewrite /proc_stream
    (length_app (proc_before ps0 cs0 I) (pending_at ps0 cs0 I)) Hlow in Hmono.
  lia.
Qed.

(* ...AND EITHER SHAPE OF AN UNWRITTEN PROMPT: the round's letter still  *)
(* to come, or the line's block.                                          *)
Lemma wr_owed_read_refute (ps cs ps0 cs0 : list nat) (I I0 : list (bv 8))
      (P : nat) :
  wr_owed ps cs I P ->
  I `prefix_of` I0 -> I <> I0 -> rd_stage ps0 cs0 I0 ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (cs `prefix_of` cs0 \/ cs0 `prefix_of` cs) ->
  (length (proc_before ps0 cs0 I0) <= P)%nat -> False.
Proof.
  intros Hw HI Hne Hrs Hps Hcs Hle.
  pose proof Hrs as (HFps0 & HFcs0 & Hpin0 & Hbnd0).
  assert (Hqle : (nlines I <= length cs0)%nat).
  { etrans; [| exact Hbnd0].
    apply nlines_prefix, (epu_prefix_of_removelast I I0 HI Hne). }
  destruct Hw as [Hw | Hw]; last first.
  { (* the block owed: its first byte is unwritten *)
    pose proof Hw as (Hpin & Hm & Hdv & HP).
    assert (Hcs' : cs `prefix_of` cs0).
    { destruct Hcs as [Hc | Hc]; [exact Hc |].
      apply prefix_length in Hc. exfalso. lia. }
    assert (Hd0 : (0 < length (line_alts_of (last_ws I)
                                 !!! (cs0 !!! length cs)))%nat).
    { destruct (line_alts_of (last_ws I) !!! (cs0 !!! length cs))
        as [| y ys] eqn:Hy; [| cbn [length]; lia].
      exfalso.
      exact (line_alts_of_nonnil _ _ (cs_ok_of_Forall _ HFcs0 _) Hy). }
    exact (wr_blk_read_refute ps cs ps0 cs0 I I0 P 0 Hw Hcs' Hd0 HI Hne Hrs Hps
             ltac:(lia)). }
  (* the prologue open: the reader's round is settled, so its prologue is
     strictly longer than the writer's *)
  pose proof Hw as (Hpin & Hm & Hdv & Hr & Hnd & HP).
  assert (Hcs' : cs `prefix_of` cs0).
  { destruct Hcs as [Hc | Hc]; [exact Hc |].
    pose proof (prefix_length _ _ Hc) as Hlc.
    rewrite (prefix_length_eq _ _ Hc ltac:(lia)). reflexivity. }
  destruct Hcs' as [z Hz].
  assert (Hidx : pro_idx cs0 (nlines I) = pro_idx cs (nlines I)).
  { rewrite Hz. apply pro_idx_app_le. lia. }
  assert (Hdone0 : pro_done (pro_from (pro_idx cs (nlines I)) ps0)).
  { apply pro_from_done. rewrite -Hidx.
    exact (pro_pin_at ps0 cs0 I0 (nlines I) Hpin0
             (nstarted_strict I I0 HI Hne)). }
  destruct Hps as [Hps | Hps]; last first.
  { apply Hnd. exact (pro_done_mono _ _ (pro_from_mono _ _ _ Hps) Hdone0). }
  assert (Hlow : proc_before ps cs I = proc_before ps0 cs0 I).
  { apply (proc_before_cs_prefix ps ps0 cs cs0 I Hps ltac:(by eexists) Hpin).
    etrans; [apply nlines_prefix, epu_removelast_prefix | lia]. }
  assert (Hr0 : I = [] \/ cs0 !!! (nlines I - 1)%nat = 3%nat).
  { destruct (decide (I = [])) as [-> | Hn0]; [by left | right].
    destruct Hr as [Hr | Hr]; [done |].
    assert (Hq1 : (1 <= length cs)%nat)
      by (pose proof (nlines_pos_of_rest_nil I Hn0 Hm); lia).
    rewrite Hz (lookup_total_prefix cs (cs ++ z) (nlines I - 1)%nat
                  ltac:(by eexists) ltac:(lia)).
    exact Hr. }
  assert (Hlt : (length (pending_at ps cs I)
                 < length (pending_at ps0 cs0 I))%nat).
  { rewrite (pending_at_round_pre ps cs I Hm Hr)
            (pending_at_round_pre ps0 cs0 I Hm Hr0).
    (* PINNED: a bare [!length_app] takes [alt_panic] apart as well *)
    rewrite !(length_app (if decide (I = []) then [] else alt_panic) _) Hidx.
    pose proof (pro_of_open_done_lt _ _ Hnd Hdone0 (pro_from_mono _ _ _ Hps)
                  (pro_from_Forall _ _ _ HFps0)).
    lia. }
  assert (Hmono : (length (proc_stream ps0 cs0 I)
                   <= length (proc_before ps0 cs0 I0))%nat)
    by (apply prefix_length, (proc_stream_before ps0 cs0 I I0 HI Hne)).
  rewrite HP /proc_stream
    (length_app (proc_before ps cs I) (pending_at ps cs I)) Hlow in Hle.
  rewrite /proc_stream
    (length_app (proc_before ps0 cs0 I) (pending_at ps0 cs0 I)) in Hmono.
  lia.
Qed.

Section echo_links.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* ------------------------------------------------------------------ *)
  (*  THE LAW.  Each conjunct is [EchoOut]'s link with its Coq-level      *)
  (*  premises turned into [⌜⌝] wands, so that the whole thing is one     *)
  (*  [iProp] a program can hold; each is a CLOSED entailment under the   *)
  (*  equations, hence intuitionistic, hence persistent.                  *)
  (* ------------------------------------------------------------------ *)
  Definition echo_link_w : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P : nat) (b : bv 8)
         (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜(nlines I0 <= length cs0)%nat⌝ -∗
        ⌜pro_pin ps0 cs0 I0⌝ -∗
        ⌜proc_stream ps0 cs0 I0 !! P = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* THE BLOCK-FIRST BYTE files alternative [a] of the block the LINE
     THAT WAS TYPED owes -- [line_alts_of (last_ws I0)], the parse of the
     input's last body, and not a constant list. *)
  Definition echo_link_blk : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜I0 <> []⌝ -∗
        ⌜rest_of I0 = []⌝ -∗
        ⌜(nlines I0 <= S (length cs0))%nat⌝ -∗
        ⌜pro_pin ps0 cs0 I0⌝ -∗
        ⌜P = length (proc_before ps0 cs0 I0)⌝ -∗
        ⌜(a < 4)%nat⌝ -∗
        ⌜line_alts_of (last_ws I0) !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* (W'') THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE, the
     block-first link's twin one level up: the writer that resolves the
     round's alternative (init after an exec failure or a fork failure,
     sh after its [fork1] panic) files the INDEX and the bound that comes
     back has grown by one -- in [ps], not in [cs]. *)
  Definition echo_link_pro : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜rest_of I0 = []⌝ -∗
        ⌜I0 = [] \/ cs0 !!! (nlines I0 - 1)%nat = 3%nat⌝ -∗
        ⌜(nlines I0 <= length cs0)%nat⌝ -∗
        ⌜pro_pin ps0 cs0 I0⌝ -∗
        ⌜~ pro_done (pro_from (pro_idx cs0 (nlines I0)) ps0)⌝ -∗
        ⌜P = length (proc_stream ps0 cs0 I0)⌝ -∗
        ⌜(a < length pro_alts)%nat⌝ -∗
        ⌜pro_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* THE TAINT ROUTE, and it is not a convenience: every per-byte loop
     invariant of a program tower is [<the era's cursor> ∨ T], so the
     TAINT arm of byte [i] has to produce byte [i+1]'s link on its own. *)
  Definition echo_link_taint : iProp Σ :=
    (□ ∀ (k : nat) (b : bv 8) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)%I.

  Definition echo_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        era_pin γ k v -∗ dl_cnt v (1/2) n -∗
        (read_ret T k v n ws -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  (* THE READ SIDE'S TAINT ROUTE, [echo_link_taint]'s twin and needed for
     the same reason (lane IO-LEAF, M5): what sh's lease carries is the
     era's delivered-count half OR the taint, and on the taint arm the
     read must still be able to move the boundary's [dl].
     [EchoOut.ein_sup_deliv] is exactly that move, and it is the READ half
     of what [App.al_sup] gives the licence route. *)
  Definition echo_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition echo_links : iProp Σ :=
    (echo_link_w ∗ echo_link_blk ∗ echo_link_pro ∗ echo_link_taint
     ∗ echo_link_rd ∗ echo_link_rd_taint)%I.

  Global Instance echo_link_w_persistent : Persistent echo_link_w.
  Proof using . rewrite /echo_link_w. apply _. Qed.
  Global Instance echo_link_blk_persistent : Persistent echo_link_blk.
  Proof using . rewrite /echo_link_blk. apply _. Qed.
  Global Instance echo_link_pro_persistent : Persistent echo_link_pro.
  Proof using . rewrite /echo_link_pro. apply _. Qed.
  Global Instance echo_link_taint_persistent : Persistent echo_link_taint.
  Proof using . rewrite /echo_link_taint. apply _. Qed.
  Global Instance echo_link_rd_persistent : Persistent echo_link_rd.
  Proof using . rewrite /echo_link_rd. apply _. Qed.
  Global Instance echo_link_rd_taint_persistent : Persistent echo_link_rd_taint.
  Proof using . rewrite /echo_link_rd_taint. apply _. Qed.
  Global Instance echo_links_persistent : Persistent echo_links.
  Proof using . rewrite /echo_links. apply _. Qed.

  (* ---- the six projections, which is all a consumer ever uses ---- *)
  Lemma echo_links_w : echo_links -∗ echo_link_w.
  Proof using . by iIntros "($ & _ & _ & _ & _ & _)". Qed.
  Lemma echo_links_blk : echo_links -∗ echo_link_blk.
  Proof using . by iIntros "(_ & $ & _ & _ & _ & _)". Qed.
  Lemma echo_links_pro : echo_links -∗ echo_link_pro.
  Proof using . by iIntros "(_ & _ & $ & _ & _ & _)". Qed.
  Lemma echo_links_taint : echo_links -∗ echo_link_taint.
  Proof using . by iIntros "(_ & _ & _ & $ & _ & _)". Qed.
  Lemma echo_links_rd : echo_links -∗ echo_link_rd.
  Proof using . by iIntros "(_ & _ & _ & _ & $ & _)". Qed.
  Lemma echo_links_rd_taint : echo_links -∗ echo_link_rd_taint.
  Proof using . by iIntros "(_ & _ & _ & _ & _ & $)". Qed.

  (* =================================================================== *)
  (*  THE ERA'S WRITE CREDENTIAL AT A LINE BOUNDARY (lane IO-LEAF, M6a)   *)
  (*                                                                     *)
  (*  What the console lease carries besides the reader's half of the     *)
  (*  delivered count: the era's cursor, the three lower bounds and the   *)
  (*  pure shape that says where the cursor stands.  THE BOUNDARY IS THE  *)
  (*  INPUT [I], which is why the credential carries [inp_lb v I] and not *)
  (*  a count: it is what says which line the block answers.  OR THE      *)
  (*  TAINT, for every other credential's reason -- a tainted era owes no *)
  (*  transcript and the lease's holder proves nothing about the wire.    *)
  (* =================================================================== *)
  Definition ewc_owed (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_owed ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  Definition ewc_sp (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_sp ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  Definition ewc_open (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_open ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  Global Instance ewc_owed_timeless v I : Timeless (ewc_owed v I).
  Proof using Timeless0. rewrite /ewc_owed. apply _. Qed.
  Global Instance ewc_sp_timeless v I : Timeless (ewc_sp v I).
  Proof using Timeless0. rewrite /ewc_sp. apply _. Qed.
  Global Instance ewc_open_timeless v I : Timeless (ewc_open v I).
  Proof using Timeless0. rewrite /ewc_open. apply _. Qed.

  Lemma ewc_owed_taint v I : T -∗ ewc_owed v I.
  Proof using . iIntros "HT". rewrite /ewc_owed. by iRight. Qed.
  Lemma ewc_open_taint v I : T -∗ ewc_open v I.
  Proof using . iIntros "HT". rewrite /ewc_open. by iRight. Qed.

  (* ...AND THE THREE AS ONE FAMILY, indexed by how many of the shell's two
     prompt bytes are out (lane IO-LEAF, M6a(1)/M6a(3)): [0] the boundary
     itself, [1] the '$' written, [2] the whole prompt written.  What the
     shell's command loop carries beside its cursor is this at [0], what
     its prompt leaves is this at [2], and the read of the next line takes
     [2] at [I] back to [0] at [I ++ l ++ [wl_nl]] ([ewc_read]). *)
  Definition ewc_pr (v : era_pins) (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => ewc_owed v I
    | S O => ewc_sp v I
    | _ => ewc_open v I
    end.

  Global Instance ewc_pr_timeless v I p : Timeless (ewc_pr v I p).
  Proof using Timeless0. rewrite /ewc_pr. destruct p as [| [| p]]; apply _. Qed.

  (* ...WITH THE ERA'S PIN BESIDE IT, which is the shape a program below
     the application holds: the shell's loop names no [v], so the pin
     travels inside and every step re-reads it ([EchoOut.era_pin_agree]). *)
  Definition ewc_cred (k : nat) (I : list (bv 8)) (p : nat) : iProp Σ :=
    (∃ v : era_pins, era_pin γ k v ∗ ewc_pr v I p)%I.

  Global Instance ewc_cred_timeless k I p : Timeless (ewc_cred k I p).
  Proof using Timeless0. rewrite /ewc_cred. apply _. Qed.

  (* ...AND THE ONE PLACE THE CREDENTIAL IS BORN: round 0, at the EMPTY
     input, with the banner filed, no line resolved and the writer
     eighteen banner bytes in.  [UInitBanner] is what supplies it, from
     [wr_ban_round0]. *)
  Lemma wr_owed_round0 : wr_owed [3%nat] [] [] 18%nat.
  Proof using .
    left. rewrite /wr_pro. split_and!.
    - apply pro_pin_nil.
    - exact rest_of_nil.
    - by rewrite nlines_nil.
    - by left.
    - rewrite nlines_nil. cbn [pro_idx pro_from]. intros H.
      apply Exists_cons in H as [H | H];
        [apply H; by right | by apply Exists_nil in H].
    - rewrite /proc_stream proc_before_nil pending_at_nil app_nil_l.
      by vm_compute.
  Qed.

  (* =================================================================== *)
  (*  /INIT'S BANNER, AT AN ARBITRARY ROUND (lane IO-LEAF, M6a(2);        *)
  (*  PROLOGUE-ALTS-3).                                                   *)
  (*                                                                     *)
  (*  The credential at [wr_ban] with [i] of the banner's eighteen bytes  *)
  (*  already out.  The FIRST byte files the banner letter                *)
  (*  ([echo_link_pro] at [a = 3]), so from then on the writer's bound    *)
  (*  names the letter ([ps ++ [3]]) and every later byte is an ORDINARY  *)
  (*  write of what the letter owes ([echo_link_w]); what the walk ends   *)
  (*  at is [wr_pro]: the prompt's own shape.  That is how the credential *)
  (*  gets from /init's loop head to the shell it forks, round 0 and      *)
  (*  every restart alike.  At [i = 0] the same credential pays the       *)
  (*  shell's bare prompt instead ([ewc_ban_owed]): the ruling that the   *)
  (*  banner is optional.                                                 *)
  (* =================================================================== *)
  Definition wr_banp (ps cs : list nat) (I : list (bv 8)) (P i : nat) : Prop :=
    match i with
    | O => wr_ban ps cs I P
    | S _ => exists ps' : list nat, ps = ps' ++ [3%nat] /\ wr_ban ps' cs I P
    end.

  Definition ewc_ban (v : era_pins) (I : list (bv 8)) (i : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_banp ps cs I P i⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  Global Instance ewc_ban_timeless v I i : Timeless (ewc_ban v I i).
  Proof using Timeless0. rewrite /ewc_ban. apply _. Qed.

  Lemma ewc_ban_taint v I i : T -∗ ewc_ban v I i.
  Proof using . iIntros "HT". rewrite /ewc_ban. by iRight. Qed.

  Lemma echo_banner_step (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    u_banner !! i = Some b ->
    era_pin γ k v -∗ echo_links -∗ ewc_ban v I i -∗
    (ewc_ban v I (S i) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_pro with "Hlk") as "#Hpro".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_ban. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct i as [| i].
    - (* the first byte FILES the banner letter *)
      cbn [wr_banp] in Hw.
      pose proof (wr_ban_pro ps cs I P Hw) as Hpr.
      pose proof Hw as (Hpin & Hm & Hdv & Hr & _).
      destruct Hpr as (_ & _ & _ & _ & Hnd & HP).
      rewrite Nat.add_0_r.
      iApply ("Hpro" $! k v P 3%nat b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact Hnd. }
      { exact HP. }
      { rewrite pro_alts_length. lia. }
      { exact (wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [3%nat]), cs, P.
      replace (P + 1)%nat with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE'". iPureIntro. cbn [wr_banp]. by exists ps.
    - (* every later byte is an ordinary write of the filed letter *)
      cbn [wr_banp] in Hw. destruct Hw as (ps' & -> & Hw).
      pose proof (wr_ban_byte ps' cs I P (S i) b Hw Hb) as Hby.
      pose proof Hw as (Hpin & Hm & Hdv & Hr & _).
      iApply ("Hw" $! k v (P + S i)%nat b (ps' ++ [3%nat]) cs I Φ
                with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { lia. }
      { exact (pro_pin_mono ps' (ps' ++ [3%nat]) cs I ltac:(by eexists) Hpin). }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps' ++ [3%nat]), cs, P.
      replace (P + S (S i))%nat with (S (P + S i))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'". iPureIntro. cbn [wr_banp]. by exists ps'.
  Qed.

  (* ...AND WHAT THE LAST BANNER BYTE LEAVES: the prompt's own credential
     at the same input, which is what /init lends the shell. *)
  Lemma ewc_ban_done (v : era_pins) (I : list (bv 8)) :
    ewc_ban v I (length u_banner) -∗ ewc_owed v I.
  Proof using Persistent0.
    rewrite /ewc_ban /ewc_owed.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18 in Hw. cbn [wr_banp] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. left.
    exact (wr_ban_done ps' cs I P Hw).
  Qed.

  (* ...AND WHAT THE BANNER-OWED CREDENTIAL IS BEFORE ANY BYTE (the ruling
     of 2026-09-14): the round's choice shape, so the shell's bare prompt
     pays from it exactly as from [wr_pro] -- [echo_prompt_dollar] at this
     arm files [pro_alts !!! 0] with no banner before it. *)
  Lemma ewc_ban_pro (v : era_pins) (I : list (bv 8)) :
    ewc_ban v I 0%nat -∗
    ((∃ ps cs P : _, ⌜wr_pro ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T).
  Proof using Persistent0.
    rewrite /ewc_ban.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    cbn [wr_banp] in Hw. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (wr_ban_pro ps cs I P Hw).
  Qed.

  Lemma ewc_ban_owed (v : era_pins) (I : list (bv 8)) :
    ewc_ban v I 0%nat -∗ ewc_owed v I.
  Proof using Persistent0.
    iIntros "Hc". iDestruct (ewc_ban_pro with "Hc") as "[Hl | #HT]";
      rewrite /ewc_owed; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. by left.
  Qed.

  (* =================================================================== *)
  (*  THE SHELL'S PROMPT, BYTE BY BYTE, AT EITHER SHAPE.                  *)
  (*                                                                     *)
  (*  The '$' RESOLVES something in both cases -- the round's prologue    *)
  (*  alternative ([echo_link_pro] at [a = 0]) when the round is still    *)
  (*  open, the LINE's block ([echo_link_blk] at [a = 2] -- the child     *)
  (*  recorded no choice) when it is not -- and the [ ] after it is an    *)
  (*  ordinary byte of what the first one fixed ([echo_link_w]).  So the  *)
  (*  shell's walk spends ONE pair of steps at every prompt it prints,    *)
  (*  round 0's and every later one alike.                                *)
  (* =================================================================== *)
  Lemma echo_prompt_dollar (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links -∗ ewc_owed v I -∗ (ewc_sp v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_blk with "Hlk") as "#Hblk".
    iDestruct (echo_links_pro with "Hlk") as "#Hpro".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_owed. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /ewc_sp. by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hhd : pro_alts !!! 0%nat !! 0%nat = Some b)
      by (rewrite wr_pro_alts_0 Hb; exact wr_prompt_head).
    assert (Hhd2 : line_alts_of (last_ws I) !!! 2%nat !! 0%nat = Some b)
      by (rewrite wr_line_alts_2 Hb; exact wr_prompt_head).
    destruct Hw as [Hw | Hw].
    - (* the round's prologue is open: the '$' files alternative 0 *)
      pose proof (wr_pro_dollar ps cs I P Hw) as Hsp.
      destruct Hw as (Hpin & Hm & Hdv & Hr & Hnd & HP).
      iApply ("Hpro" $! k v P 0%nat b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact Hnd. }
      { exact HP. }
      { vm_compute. lia. }
      { exact Hhd. }
      iIntros "Hres". iApply "HΦ". rewrite /ewc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [0%nat]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
    - (* the round is settled: the '$' is the line's block, alternative 2 *)
      pose proof (wr_blk_dollar ps cs I P Hw) as Hsp.
      pose proof (wr_blk_nonnil ps cs I P Hw) as Hne.
      destruct Hw as (Hpin & Hm & Hdv & HP).
      iApply ("Hblk" $! k v P 2%nat b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hne. }
      { exact Hm. }
      { lia. }
      { exact Hpin. }
      { exact HP. }
      { lia. }
      { exact Hhd2. }
      iIntros "Hres". iApply "HΦ". rewrite /ewc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, (cs ++ [2%nat]), (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
  Qed.

  Lemma echo_prompt_space (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    era_pin γ k v -∗ echo_links -∗ ewc_sp v I -∗ (ewc_open v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_sp. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /ewc_open. by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct Hw as [Hop Hby].
    pose proof Hop as (Hpin & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v P b ps cs I Φ
              with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { lia. }
    { exact Hpin. }
    { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /ewc_open.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    by iPureIntro.
  Qed.

  (* THE SHELL'S '$' FROM THE BANNER-OWED SHAPE (PROLOGUE-ALTS-3): /init
     printed nothing -- its console was shut -- and lent the shell the
     credential at the round's head; the '$' is then the round's first
     byte and files the bare prompt.  [EchoLinksBan.echo_prompt_dollar_ban]
     is this at the tight shapes of [EchoLinksLine]. *)
  Lemma echo_prompt_dollar_ban (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links -∗ ewc_ban v I 0%nat -∗ (ewc_sp v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (echo_prompt_dollar k v I b Φ Hb with "Hpin Hlk [Hc] HΦ").
    by iApply ewc_ban_owed.
  Qed.

  (* ...AND WHAT A LINE'S READ DOES TO IT: nothing at all to the cursor
     ([EchoOut.pcount_echo]), and everything to the shape -- the line just
     echoed owes its block, so the credential is back at [wr_blk] and the
     next prompt is that block's first byte.  The body [l] may be any run
     of bytes with no newline in it, which is the whole of what a line
     per round changes here.  The fresh bound comes off the read's own
     receipt ([EchoOut.read_ret]). *)
  Lemma ewc_read (v : era_pins) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ ewc_open v I -∗
    ewc_owed v (I ++ l ++ [wl_nl]).
  Proof using Persistent0.
    intros Hl. iIntros "#HE' Hc". rewrite /ewc_open /ewc_owed.
    iDestruct "Hc" as "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE'".
    iPureIntro. right. exact (wr_open_read ps cs I P l Hw Hl).
  Qed.

  (* =================================================================== *)
  (*  THE DISCIPLINE LEMMA, AS THE SHELL SPENDS IT: a credential that     *)
  (*  says the boundary's prompt is not out, and a read at that boundary  *)
  (*  that delivered a byte, are together the taint.  Everything is       *)
  (*  handed back, so the caller keeps whatever arm it was on.            *)
  (*                                                                     *)
  (*  [length I = n] is what ties the credential's boundary to the read's *)
  (*  -- the lease carries the two together ([dl_cnt v (1/2) n] beside    *)
  (*  [inp_lb v I]), and with it the two lower bounds of one era's input  *)
  (*  settle that the reader's input STRICTLY EXTENDS the writer's        *)
  (*  boundary ([EchoOut.inp_lb_cmp]).                                    *)
  (* =================================================================== *)
  Lemma ewc_owed_read_refute (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> (0 < length ws)%nat ->
    ewc_owed v I -∗ read_ret T k v n ws -∗
    T ∗ ewc_owed v I ∗ read_ret T k v n ws.
  Proof using Persistent0.
    intros HIn Hws. iIntros "Hc Hr".
    rewrite /ewc_owed. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iSplitR; [iExact "HT" |]. iSplitR "Hr"; [by iRight | iExact "Hr"]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    rewrite /read_ret. iDestruct "Hr" as "[[#HT Hdl] | [Hdlr Hfacts]]".
    { iSplitR; [iExact "HT" |]. iSplitL "Htn".
      - iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". by iPureIntro.
      - iLeft. iSplitR; [iExact "HT" | iExact "Hdl"]. }
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0) "(#Hcs0 & #Hps0 & %Hbd & #Htlb & %Hrs)".
    iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
    iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
    iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
    iDestruct (inp_lb_cmp with "HE Hinp") as %Hic.
    iExFalso. iPureIntro.
    assert (Hlen : length (snd <$> (dl ++ ws)) = (n + length ws)%nat).
    { by rewrite length_fmap length_app Hdl. }
    assert (HI : I `prefix_of` (snd <$> (dl ++ ws))).
    { destruct Hic as [Hc | Hc]; [exact Hc |].
      exfalso. apply prefix_length in Hc. lia. }
    assert (Hne : I <> (snd <$> (dl ++ ws)))
      by (intros Hq; rewrite Hq Hlen in HIn; lia).
    exact (wr_owed_read_refute ps cs ps0 cs0 I (snd <$> (dl ++ ws)) P Hw
             HI Hne Hrs Hpsc Hcsc Hle).
  Qed.

  Lemma ewc_owed_read_taint (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> (0 < length ws)%nat ->
    ewc_owed v I -∗ read_ret T k v n ws -∗ T.
  Proof using Persistent0.
    intros HIn Hws. iIntros "Hc Hr".
    iDestruct (ewc_owed_read_refute k v n I ws HIn Hws with "Hc Hr")
      as "($ & _ & _)".
  Qed.

  (* =================================================================== *)
  (*  ...AND THE LAW HOLDS, under the record's four equations.  This is  *)
  (*  the one place in the arc where the application's claims and the    *)
  (*  kernel's console contracts are the same object, and it is exactly  *)
  (*  where [UInitBoot.echo_Hinit_boot] already stands.                  *)
  (* ================================================================== *)
  Section echo_links_holds.
    (* ONE claim equation since the redesign, where there were three *)
    Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ecl T γ).
    Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = etag T).

    Lemma echo_links_holds : ⊢ echo_links.
    Proof using Hcons Persistent0.
      rewrite /echo_links /echo_link_w /echo_link_blk /echo_link_pro
              /echo_link_taint /echo_link_rd /echo_link_rd_taint.
      iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit]]]].
      - iIntros "!>" (k v P b ps0 cs0 I0 Φ) "%Hbnd %Hpin0 %Hb".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k v P a b ps0 cs0 I0 Φ).
        iIntros "%Hpos %Hrest %Hbnd %Hpin0 %HPeq %Halt %Hhead".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link_blk with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k v P a b ps0 cs0 I0 Φ).
        iIntros "%Hrest %Hpr %Hbnd %Hpin0 %Hnd %HPeq %Halt %Hhead".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link_pro with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k b Φ) "HT HΦ".
        iApply (echo_write_link_taint T γ with "HT HΦ"); try assumption.
      - iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
        iApply (echo_read_link with "Hpin Hdl HΦ"); try assumption.
      - (* the read's taint route is the ONE taint route now: every event
           on a tainted claim is free *)
        iIntros "!>" (k ws Φ) "#HT HΦ".
        iApply (cons_link_of_taint T γ with "HT [HΦ]"); try assumption.
        by iApply "HΦ".
    Qed.
  End echo_links_holds.

End echo_links.
