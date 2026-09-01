(* ===================================================================== *)
(* UkShParse.v -- the `sh` PARSER on the urun engine, SH LANE STAGE 4.     *)
(*                                                                        *)
(* The lane's stages 1-2 (iris/UkSh.v) walked the ELF entry, main's        *)
(* console preamble and the command loop down to the blank-line test, and  *)
(* stopped at [ush_rest] -- an abstract continuation standing for the rest *)
(* of main's body.  Stage 4 is the biggest piece of that body: the         *)
(* recursive-descent parser and the lexer under it,                        *)
(*                                                                        *)
(*   parsecmd -> parseline -> parsepipe -> parseexec -> parseredirs        *)
(*            over peek / gettoken / strchr / strlen, then nulterminate,   *)
(*                                                                        *)
(* 564 instructions in eleven functions.                                   *)
(*                                                                        *)
(* ITS OWN CATALOG, FOR A MEASURED REASON.  [UCodeShP.v] is a THIRD        *)
(* catalog over the same dump as [UCodeSh.v] (the first-generation         *)
(* [uinstr] form) and [UCodeShK.v] (stages 1-2 on urun).  Stage 1          *)
(* re-measured the catalog's compile cost serially and found it LINEAR in  *)
(* instructions -- ~22 s fixed plus ~1.9 s each, with no superlinear term  *)
(* to remove -- so the parser's 564 instructions are a file of their own   *)
(* rather than 564 more rows in UCodeShK.v.  Measured: 18 min 58 s          *)
(* serially, 4 % over what that law predicts.  [shp_code] and [shk_code]   *)
(* are the SAME proposition ([utext_img g ShInstrs.sh_bytes]);             *)
(* [ushp_code_shk] below is the one-line bridge, and it is what will let   *)
(* this walk call UkSh.v's [memset] instead of re-walking it.              *)
(*                                                                        *)
(* THAT REUSE IS LIVE.  It was blocked, and the block was a CONTRACT, not  *)
(* a proof: [UkSh.wp_ksh_memset]'s postcondition used to be               *)
(* [∃ g, ubytes γd a N g] -- the buffer came back OWNED but with UNKNOWN   *)
(* CONTENTS, which is enough for stage 2 (getcmd only needs the buffer     *)
(* back) and NOT enough for stage 4: [execcmd] is [malloc(168);            *)
(* memset(cmd, 0, 168); cmd->type = EXEC], and the only reason             *)
(* [cmd->argv[0] == 0] -- the NULL cap the tree predicate and              *)
(* [nulterminate]'s loop both turn on -- is that the memset ZEROED it.     *)
(* The stage-5 lane strengthened it in tree to hand back                   *)
(* [ubytes γd a N (fun _ => nth_byte (m !!! a1_idx) 0)], so §7 below walks *)
(* [execcmd] end to end and the constructor chain can start.               *)
(*                                                                        *)
(* WHAT IS HERE.                                                           *)
(*                                                                        *)
(* (1) THE PURE VOCABULARY, ported.  [ushp_is_ws] / [ushp_is_sym] /        *)
(* [ushp_skipws] / [ushp_toklen] / [ushp_tokens] / [ushp_find] are         *)
(* USpecSh.v's and USpecShParse.v's definitions, re-stated over an INDEX   *)
(* FUNCTION ([nat -> bv 8], which is what [UserHeap.ubytes] and            *)
(* [UserHeap.ustr] are indexed by) rather than over a [list (bv 8)].  They *)
(* are re-stated and not required for the reason UkSh.v re-stated          *)
(* [USpecSh.SH_BUF] as [sh_buf]: requiring USpecShParse.v drags UCodeSh.v  *)
(* (10 148 lines), UmodeIo and Xv6G -- the whole first-generation engine -- *)
(* into a urun-tier file.  Stage 6 reconciles the two spellings; R10 keeps *)
(* the old statements where they are.                                     *)
(*                                                                        *)
(* (2) THE TREE PREDICATE, the deliverable interface for stages 5-6:       *)
(* [ushp_tree] -- a well-formed cmd tree for this token list sits at this *)
(* address in the heap.  It is an [iProp], not a [Prop] over a [gmap]:     *)
(* on urun a node's bytes are OWNED.  The sibling stage-5 lane states its  *)
(* own copy of the same idea; stage 6 reconciles them, per the lane brief. *)
(*                                                                        *)
(* (3) THE MALLOC HYPOTHESIS.  sh's five cmd constructors all begin        *)
(* [cmd = malloc(sizeof( *cmd))], and stage 3 (malloc/morecore/sbrk/free)   *)
(* is blocked on upstream's [wp_uk_ecall_sbrk] leaf.  So malloc's contract *)
(* is ONE named local Hypothesis, [ushp_malloc_ok], stated in urun         *)
(* vocabulary at the wait_null/window-leaf idiom -- it consumes the run at *)
(* malloc's ENTRY pc and hands it back at the return address, so not one   *)
(* instruction of the allocator is fetched here and none is catalogued.    *)
(* EVERY LEMMA THAT DEPENDS ON IT SAYS SO IN ITS OWN HEADER, exactly as    *)
(* stage 2 labelled the seven lemmas that carried [ush_read_leaf].         *)
(*                                                                        *)
(* THE OBSTACLE THIS FILE WAS PARKED AGAINST -- FOUND AND FIXED             *)
(* (2026-09-01).  [wp_kshp_peek]'s body is IN and green; what follows is    *)
(* the record, because the bug is a one-line idiom that any of the six      *)
(* remaining walks can re-introduce.                                        *)
(*                                                                        *)
(* THE SYMPTOM.  One [iApply] -- the body's seven-entry                     *)
(* [iApply (wp_kshp_spill spn (2 + nn) ...)] -- ran to 17.5 GB of RSS and   *)
(* was still climbing when killed at 300 s.                                 *)
(*                                                                        *)
(* THE CAUSE, one line, inside that [iApply]'s second [ltac:] premise:      *)
(*                                                                        *)
(*     exact (eq_sym (Hm1 _ ltac:(vm_compute; discriminate)))              *)
(*                                                                        *)
(* The [_] is the REGISTER, and it is still an EVAR when the nested         *)
(* [ltac:] runs -- so [vm_compute] is asked to evaluate                     *)
(* [Regidx ?q <> Regidx csp_rs1] with [?q] open.  That is the 17 GB.  This  *)
(* is durable gotcha (2) of this lane (a [_] among a lemma's arguments      *)
(* leaves an evar the accompanying [ltac:] cannot see) -- and the lesson is *)
(* that it does not merely FAIL, it can DIVERGE.                            *)
(*                                                                        *)
(* THE FIX, also one line -- [refine] first, side condition after, so the   *)
(* register is fixed by unification before anything computes:               *)
(*                                                                        *)
(*     refine (eq_sym (Hm1 _ _)); vm_compute; discriminate                 *)
(*                                                                        *)
(* Measured on an isolated rig, everything else held fixed: 60 s+ and       *)
(* still climbing with the [exact ... ltac:] form, 0.191 s with [refine].   *)
(* execcmd never hit this because it writes the register EXPLICITLY         *)
(* ([Hm1 ra_idx ltac:(...)]); [wp_kshp_peek_epi] has no such script.        *)
(*                                                                        *)
(* SIX EXPLANATIONS WERE TESTED AND REFUTED FIRST, each by its own timed    *)
(* run; they are recorded in the SH lane's stage-4 section of               *)
(* claude-notes/projects/fs-syscall-specs.md so nobody pays for them twice: *)
(* the leaf's [Prop] premises, the [""[]""] spec pattern, the proofmode     *)
(* context (both [iClear] of every spatial hypothesis and [clear] of every  *)
(* pure one, plus [clearbody] on every [set]), the unsealed-big-op rule,    *)
(* an explicit end-pc parameter on the two frame runs, and the existential  *)
(* under [wp_kshp_spill]'s frame big-op.  A standalone rig applying         *)
(* [wp_kshp_spill] at k = 3..7 measures 0.075 / 0.096 / 0.118 / 0.139 /     *)
(* 0.167 s -- LINEAR at ~24 ms a spill -- so neither the lemma nor the      *)
(* arity was ever the problem.                                              *)
(*                                                                        *)
(* (4) THE WALKS, bottom-up, so that every landed lemma is a theorem about *)
(* real code and nothing is stated that is not proved.  This file has ZERO *)
(* [Admitted] and ZERO [Axiom]; its audit is the standing three            *)
(* ([resv_matches], [resv_is_valid], funext), plus [ushp_malloc_ok] on the *)
(* lemmas whose headers name it.  What is landed and what the measured     *)
(* obstacle to the rest is are recorded in the SH lane's stage-4 row of    *)
(* claude-notes/projects/fs-syscall-specs.md.                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import UCodeShK UCodeShP.
Require Import UkSh.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.



(* ===================================================================== *)
(* §1 THE PURE VOCABULARY.                                                *)
(*                                                                        *)
(* USpecSh.v / USpecShParse.v index the buffer by a [list (bv 8)]; urun    *)
(* indexes it by a function [nat -> bv 8] together with a length, because  *)
(* that is what [UserHeap.ubytes] and [UserHeap.ustr] carry.  Everything   *)
(* below is those files' definitions transposed into that indexing and     *)
(* nothing else -- same tables, same predicates, same induction.           *)
(* ===================================================================== *)

(* the two static tables of sh.c, verbatim from USpecSh.v:
     char whitespace[] = " \t\r\n\v";   char symbols[] = "<|>&;()";   *)
Definition ushp_ws_bytes : list (bv 8) :=
  (fun z => Z_to_bv 8 z) <$> [32; 9; 13; 10; 11].
Definition ushp_sym_bytes : list (bv 8) :=
  (fun z => Z_to_bv 8 z) <$> [60; 124; 62; 38; 59; 40; 41].

Definition ushp_is_ws  (b : bv 8) : bool := bool_decide (b ∈ ushp_ws_bytes).
Definition ushp_is_sym (b : bv 8) : bool := bool_decide (b ∈ ushp_sym_bytes).

(* THE ADDRESSES of those two tables in sh's .data page -- not guessed:
   `symbols' and `whitespace' are ELF symbols, and this pins them the way
   the catalog's [shp_syms_pins] pins the code addresses. *)
Definition ushp_symbols    : Z := 0x2000.
Definition ushp_whitespace : Z := 0x2008.

Lemma ushp_tbl_pins :
  ShSyms.symbols = ushp_symbols /\ ShSyms.whitespace = ushp_whitespace.
Proof.
  unfold ShSyms.symbols, ShSyms.whitespace, ushp_symbols, ushp_whitespace.
  split; reflexivity.
Qed.

(* ---- the lexer's two measures, over an index function ---------------- *)

(* [ushp_skipws n i f] -- how far `while (s < es && strchr(whitespace, *s))
   s++' advances from index [i], looking at no more than [n] bytes.  [n] is
   not a fuel in the "might run out" sense: every caller instantiates it at
   the number of bytes actually left, and the NUL that terminates the line
   stops the scan anyway (0 is not a whitespace byte). *)
Fixpoint ushp_skipws (n i : nat) (f : nat -> bv 8) : nat :=
  match n with
  | O => O
  | S n' => if ushp_is_ws (f i) then S (ushp_skipws n' (S i) f) else O
  end.

(* ... and how far [gettoken]'s default arm then runs *)
Fixpoint ushp_toklen (n i : nat) (f : nat -> bv 8) : nat :=
  match n with
  | O => O
  | S n' =>
      if ushp_is_ws (f i) || ushp_is_sym (f i)
      then O else S (ushp_toklen n' (S i) f)
  end.

Lemma ushp_skipws_le (n i : nat) (f : nat -> bv 8) :
  (ushp_skipws n i f <= n)%nat.
Proof.
  revert i. induction n as [| n IH ]; intros i; cbn; [ lia | ].
  destruct (ushp_is_ws (f i)); [ | lia ]. pose proof (IH (S i)). lia.
Qed.

(* the two one-step readings of [ushp_skipws] a scan's proof needs, so no
   walk ever has to [cbn] a [Fixpoint] inside a proofmode goal *)
Lemma ushp_skipws_stop (n i : nat) (f : nat -> bv 8) :
  ushp_is_ws (f i) = false -> ushp_skipws n i f = 0%nat.
Proof.
  intro H. destruct n as [| n ]; cbn; [ reflexivity | rewrite H; reflexivity ].
Qed.

Lemma ushp_skipws_zero (i : nat) (f : nat -> bv 8) :
  ushp_skipws 0 i f = 0%nat.
Proof. reflexivity. Qed.

Lemma ushp_skipws_step (n i : nat) (f : nat -> bv 8) :
  ushp_is_ws (f i) = true ->
  ushp_skipws (S n) i f = S (ushp_skipws n (S i) f).
Proof. intro H. cbn. rewrite H. reflexivity. Qed.

Lemma ushp_toklen_le (n i : nat) (f : nat -> bv 8) :
  (ushp_toklen n i f <= n)%nat.
Proof.
  revert i. induction n as [| n IH ]; intros i; cbn; [ lia | ].
  destruct (ushp_is_ws (f i) || ushp_is_sym (f i)); [ lia | ].
  pose proof (IH (S i)). lia.
Qed.

(* ---- THE TOKENIZATION MODEL.  USpecShParse.sh_tokens, transposed. ----- *)
(* Scanning the [len] bytes from index [off], the maximal non-whitespace
   runs are exactly [toks], as (start, end) index pairs.  It is defined in
   the shape [parseexec]'s argument loop runs in, so that loop's invariant
   is literally one constructor -- which is the whole reason the port keeps
   this predicate instead of inventing one. *)
Inductive ushp_tokens (len : nat) (f : nat -> bv 8)
  : nat -> list (nat * nat) -> Prop :=
| UshpTokNil (off : nat) :
    (off + ushp_skipws (len - off) off f = len)%nat ->
    ushp_tokens len f off []
| UshpTokCons (off : nat) (toks : list (nat * nat)) :
    let k := ushp_skipws (len - off) off f in
    let n := ushp_toklen (len - (off + k)) (off + k) f in
    (0 < n)%nat ->
    ushp_tokens len f (off + k + n)%nat toks ->
    ushp_tokens len f off ((off + k, off + k + n)%nat :: toks).

(* the tokens of a line are ordered, non-empty and inside it -- the three
   facts every consumer of [ushp_tokens] needs and none of which is a new
   assumption *)
Lemma ushp_tokens_in (len : nat) (f : nat -> bv 8) (off : nat)
    (toks : list (nat * nat)) :
  ushp_tokens len f off toks -> (off <= len)%nat ->
  forall (i : nat) (t : nat * nat), toks !! i = Some t ->
    (off <= fst t < snd t /\ snd t <= len)%nat.
Proof.
  induction 1 as [ off Hnil | off toks k n Hn Htoks IH ]; intros Hoff i t Hi.
  - rewrite lookup_nil in Hi. discriminate.
  - assert (Hk : (k <= len - off)%nat)
      by exact (ushp_skipws_le (len - off) off f).
    assert (Hn' : (n <= len - (off + k))%nat)
      by exact (ushp_toklen_le (len - (off + k)) (off + k) f).
    assert (Hnext : (off + k + n <= len)%nat) by lia.
    destruct i as [| i ]; cbn in Hi.
    + injection Hi as <-. cbn. lia.
    + destruct (IH Hnext i t Hi) as [ Hlo Hhi ]. split; lia.
Qed.

(* no symbol byte anywhere in the line -- what keeps [gettoken] in its
   default arm and [parseredirs] / [parsepipe] / [parseline] out of their
   loops, hence what makes the parse of a line an EXEC node.  It is the
   premise that scopes stage 4, and it is why [parseblock], [redircmd],
   [pipecmd], [listcmd] and [backcmd] are not in the catalog. *)
Definition ushp_no_symbols (len : nat) (f : nat -> bv 8) : Prop :=
  forall j : nat, (j < len)%nat -> ushp_is_sym (f j) = false.

(* ---- strchr's pure model, over an index function --------------------- *)
(* USpecSh.ustr_find, transposed: the first index in [[i, i+n)] at which
   [f] takes the value [c]. *)
Fixpoint ushp_find (n i : nat) (f : nat -> bv 8) (c : bv 8) : option nat :=
  match n with
  | O => None
  | S n' => if bool_decide (f i = c) then Some i else ushp_find n' (S i) f c
  end.

Lemma ushp_find_0 (i : nat) (f : nat -> bv 8) (c : bv 8) :
  ushp_find 0 i f c = None.
Proof. reflexivity. Qed.

Lemma ushp_find_S_hit (n i : nat) (f : nat -> bv 8) (c : bv 8) :
  f i = c -> ushp_find (S n) i f c = Some i.
Proof. intro H. cbn. rewrite (bool_decide_eq_true_2 _ H). reflexivity. Qed.

Lemma ushp_find_S_miss (n i : nat) (f : nat -> bv 8) (c : bv 8) :
  f i <> c -> ushp_find (S n) i f c = ushp_find n (S i) f c.
Proof. intro H. cbn. rewrite (bool_decide_eq_false_2 _ H). reflexivity. Qed.

Lemma ushp_find_ge (n i : nat) (f : nat -> bv 8) (c : bv 8) (j : nat) :
  ushp_find n i f c = Some j -> (i <= j < i + n)%nat.
Proof.
  revert i. induction n as [| n IH ]; intros i H; cbn in H; [ discriminate | ].
  destruct (bool_decide (f i = c)).
  - injection H as <-. lia.
  - pose proof (IH (S i) H). lia.
Qed.

(* what a HIT means, and what a MISS means -- the two facts the lexer's
   table lookups turn on, proved once over an arbitrary window rather than
   at each of the three tables [peek] and [gettoken] search. *)
Lemma ushp_find_some_val (n i j : nat) (f : nat -> bv 8) (c : bv 8) :
  ushp_find n i f c = Some j -> f j = c.
Proof.
  revert i. induction n as [| n IH ]; intros i H; cbn in H; [ discriminate | ].
  destruct (decide (f i = c)) as [ E | E ].
  - rewrite (bool_decide_eq_true_2 _ E) in H. injection H as <-. exact E.
  - rewrite (bool_decide_eq_false_2 _ E) in H. exact (IH (S i) H).
Qed.

Lemma ushp_find_some_of (n i j : nat) (f : nat -> bv 8) (c : bv 8) :
  (i <= j < i + n)%nat -> f j = c ->
  exists k : nat, ushp_find n i f c = Some k.
Proof.
  revert i. induction n as [| n IH ]; intros i Hj Hf; [ lia | ].
  cbn. destruct (decide (f i = c)) as [ E | E ].
  - rewrite (bool_decide_eq_true_2 _ E). exists i. reflexivity.
  - rewrite (bool_decide_eq_false_2 _ E).
    destruct (Nat.eq_dec i j) as [ Hij | Hne ];
      [ exfalso; apply E; rewrite Hij; exact Hf | ].
    exact (IH (S i) ltac:(lia) Hf).
Qed.

(* ---- THE WHITESPACE TABLE, as a [ustr]'s content function -------------- *)
(* [ushp_ws_bytes] is the five bytes as a LIST, which is what [ushp_is_ws]
   is stated over; this is the same five as the INDEX FUNCTION a [ustr] at
   0x2008 carries.  Both spellings are needed and the four lemmas below are
   the bridge: [strchr(whitespace, c)] is nonzero exactly when
   [ushp_is_ws c], which is what makes [ushp_skipws] the measure of peek's
   and gettoken's scans. *)
Definition ushp_ws_f (i : nat) : bv 8 :=
  match i with
  | 0%nat => Z_to_bv 8 32 | 1%nat => Z_to_bv 8 9 | 2%nat => Z_to_bv 8 13
  | 3%nat => Z_to_bv 8 10 | _ => Z_to_bv 8 11
  end.

(* the table IS a C string: five bytes, none of them NUL *)
Lemma ushp_ws_f_nonul (j : nat) : (j < 5)%nat -> ushp_ws_f j <> ubyte0.
Proof.
  intro Hj. destruct j as [| [| [| [| [| j ]]]]];
    vm_compute; discriminate.
Qed.

Lemma ushp_ws_mem (j : nat) : (j < 5)%nat -> ushp_ws_f j ∈ ushp_ws_bytes.
Proof.
  intro Hj. unfold ushp_ws_bytes.
  destruct j as [| [| [| [| [| j ]]]]]; cbn [fmap list_fmap ushp_ws_f];
    [ apply elem_of_list_here
    | apply elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_further, elem_of_list_here
    | lia ].
Qed.

Lemma ushp_ws_mem_inv (c : bv 8) :
  c ∈ ushp_ws_bytes -> exists j : nat, (j < 5)%nat /\ ushp_ws_f j = c.
Proof.
  unfold ushp_ws_bytes. cbn [fmap list_fmap]. intro H.
  apply elem_of_cons in H; destruct H as [ -> | H ];
    [ exists 0%nat; split; [ lia | reflexivity ] | ].
  apply elem_of_cons in H; destruct H as [ -> | H ];
    [ exists 1%nat; split; [ lia | reflexivity ] | ].
  apply elem_of_cons in H; destruct H as [ -> | H ];
    [ exists 2%nat; split; [ lia | reflexivity ] | ].
  apply elem_of_cons in H; destruct H as [ -> | H ];
    [ exists 3%nat; split; [ lia | reflexivity ] | ].
  apply elem_of_cons in H; destruct H as [ -> | H ];
    [ exists 4%nat; split; [ lia | reflexivity ] | ].
  apply elem_of_nil in H. destruct H.
Qed.


(* ... and what the code returns for it: the address of that byte, or NULL.
   Note that xv6's strchr returns 0 -- NOT a pointer to the terminator --
   when [c] is the NUL byte, and [ushp_find] agrees, because a [ustr]'s
   body bytes are all non-NUL. *)
Definition ushp_chr (s : Z) (n i : nat) (f : nat -> bv 8) (c : bv 8) : Z :=
  match ushp_find n i f c with
  | Some j => s + Z.of_nat j
  | None => 0
  end.

Lemma ushp_chr_hit (s : Z) (n i : nat) (f : nat -> bv 8) (c : bv 8) (j : nat) :
  ushp_find n i f c = Some j -> ushp_chr s n i f c = s + Z.of_nat j.
Proof. intro H. unfold ushp_chr. rewrite H. reflexivity. Qed.

Lemma ushp_chr_miss (s : Z) (n i : nat) (f : nat -> bv 8) (c : bv 8) :
  ushp_find n i f c = None -> ushp_chr s n i f c = 0.
Proof. intro H. unfold ushp_chr. rewrite H. reflexivity. Qed.

(* ...and what [strchr] over it RETURNS: 0 exactly on a non-whitespace byte,
   an address inside the table on a whitespace one *)
Lemma ushp_ws_chr_z (c : bv 8) :
  ushp_is_ws c = false ->
  ushp_chr ushp_whitespace 5 0%nat ushp_ws_f c = 0.
Proof.
  intro H. apply ushp_chr_miss.
  destruct (ushp_find 5 0%nat ushp_ws_f c) as [ j | ] eqn:E;
    [ exfalso | reflexivity ].
  pose proof (ushp_find_ge 5 0%nat ushp_ws_f c j E) as Hj.
  pose proof (ushp_find_some_val 5 0%nat j ushp_ws_f c E) as Hv.
  unfold ushp_is_ws in H. rewrite bool_decide_eq_false in H. apply H.
  rewrite <- Hv. exact (ushp_ws_mem j ltac:(lia)).
Qed.

Lemma ushp_ws_chr_nz (c : bv 8) :
  ushp_is_ws c = true ->
  exists j : nat, (j < 5)%nat /\
    ushp_chr ushp_whitespace 5 0%nat ushp_ws_f c = ushp_whitespace + Z.of_nat j.
Proof.
  intro H. unfold ushp_is_ws in H. rewrite bool_decide_eq_true in H.
  destruct (ushp_ws_mem_inv c H) as [ j [ Hj Hv ] ].
  destruct (ushp_find_some_of 5 0%nat j ushp_ws_f c ltac:(lia) Hv)
    as [ k Hk ].
  pose proof (ushp_find_ge 5 0%nat ushp_ws_f c k Hk) as Hkr.
  exists k. split; [ lia | ].
  exact (ushp_chr_hit ushp_whitespace 5 0%nat ushp_ws_f c k Hk).
Qed.

Section UkShParse.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).

  (* ===================================================================== *)
  (* THE CATALOG BRIDGE.  [shp_code] and [shk_code] are the SAME            *)
  (* proposition -- both unfold to [utext_img g ShInstrs.sh_bytes] -- so    *)
  (* the parser's walk can hand its own code resource to a stage-2 lemma.   *)
  (* This is the only thing the two catalogs share, and it is why splitting *)
  (* them costs nothing but one extra ~22 s prelude.                        *)
  (* ===================================================================== *)
  Lemma ushp_code_shk (g : gname) : shp_code g -∗ shk_code g.
  Proof. rewrite /shp_code /shk_code. iIntros "#H". iExact "H". Qed.

  (* ---- the symbol pins this file uses, one name each ------------------ *)
  Local Lemma shpp_strchr : ShSyms.strchr = 0xa82.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&_&_&_&H). exact H. Qed.
  Local Lemma shpp_strlen : ShSyms.strlen = 0xa30.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shpp_execcmd : ShSyms.execcmd = 0x1d2.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&_&H&_&_). exact H. Qed.
  Local Lemma shpp_gettoken : ShSyms.gettoken = 0x310.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&H&_&_&_). exact H. Qed.
  Local Lemma shpp_peek : ShSyms.peek = 0x448.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&H&_&_&_&_). exact H. Qed.

  (* ===================================================================== *)
  (* §2 THE BYTE / REGISTER ALGEBRA THIS FILE NEEDS.                        *)
  (*                                                                       *)
  (* Every one of these is stage 2's -- but stage 2 declared them           *)
  (* [Local Lemma] inside [Section UkSh], so they do not leave UkSh.v.      *)
  (* RELOCATION ASK (relayed in the lane report): these, together with      *)
  (* [UkSh]'s [ush_bytes_upd] and [urun_x0], are ENGINE algebra rather than *)
  (* sh facts and belong beside [UserHeap.ustr_byte].                       *)
  (* ===================================================================== *)

  Local Lemma ushp_ridx_eq (r q : mword 5) : uint r = uint q -> Regidx r = Regidx q.
  Proof.
    intro H. f_equal. apply bv_eq. rewrite <- !(uint_unsigned_n 5). exact H.
  Qed.

  Local Lemma ushp_ridx_ne (r q : mword 5) : uint r <> uint q -> Regidx r <> Regidx q.
  Proof.
    intros H He. apply H.
    assert (Hrq : r = q) by (injection He; trivial). rewrite Hrq. reflexivity.
  Qed.

  Local Lemma ushp_cs_ne (r q : mword 5) :
    ucallee_saved_idx r = true -> ucallee_saved_idx q = false ->
    Regidx r <> Regidx q.
  Proof.
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  (* a byte's numeric value is in range *)
  Local Lemma ushp_byte_rng (b : bv 8) : 0 <= bv_unsigned b < 256.
  Proof.
    pose proof (bv_unsigned_in_range 8 b) as Hr8.
    assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite Em8 in Hr8. exact Hr8.
  Qed.

  (* two bytes are equal exactly when their zero-extended words are.  This
     is the whole content of strchr's comparison: [beq a1,a5] runs on the
     64-bit registers, and both were filled by an [lbu]. *)
  Local Lemma ushp_zext_eq (b c : bv 8) :
    eq_vec (mword_of_int (bv_unsigned c) : mword 64)
           (mword_of_int (bv_unsigned b) : mword 64)
    = bool_decide (b = c).
  Proof.
    pose proof (ushp_byte_rng b) as Hb. pose proof (ushp_byte_rng c) as Hc.
    rewrite (moi_eq_vec (bv_unsigned c) (bv_unsigned b)
               ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
    destruct (decide (b = c)) as [ Hbc | Hbc ].
    - rewrite (bool_decide_eq_true_2 _ Hbc). subst c.
      apply Z.eqb_eq. reflexivity.
    - rewrite (bool_decide_eq_false_2 _ Hbc).
      apply Z.eqb_neq. intro He. apply Hbc. apply bv_eq. symmetry. exact He.
  Qed.

  (* ... and a byte is NUL exactly when its zero-extended word is zero *)
  Local Lemma ushp_zext_nul (b : bv 8) :
    eq_vec (mword_of_int (bv_unsigned b) : mword 64) zero_reg
    = bool_decide (b = ubyte0).
  Proof.
    pose proof (ushp_byte_rng b) as Hb.
    assert (Ez : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ez.
    rewrite (moi_eq_vec (bv_unsigned b) 0
               ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
    destruct (decide (b = ubyte0)) as [ Hb0 | Hb0 ].
    - rewrite (bool_decide_eq_true_2 _ Hb0). subst b.
      apply Z.eqb_eq. vm_compute. reflexivity.
    - rewrite (bool_decide_eq_false_2 _ Hb0).
      apply Z.eqb_neq. intro He. apply Hb0. apply bv_eq. rewrite He.
      vm_compute. reflexivity.
  Qed.

  (* x0's VALUE is not readable off [m] -- the register file says nothing
     about it -- but the bundle inside [urun] does.  [peek] ends on
     [snez a0,a0], which the decoder gives as [sltu a0,x0,a0], so without
     this the return value could not be named.  Stage 2 has the same lemma
     as a [Local Lemma] inside [Section UkSh] for the STORE of x0; that is
     the same relocation ask, one instruction class over. *)
  Local Lemma urun_x0 (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat) :
    urun γt γd γs h m pc avail -∗
    ⌜ m !!! Regidx x0_idx = zero_reg ⌝ ∗ urun γt γd γs h m pc avail.
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv)
      "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv. iFrame "Hheap Hstk Hb".
    iPureIntro. split; [ exact Hlo | exact Hpm ].
  Qed.

  (* ...and what that instruction WRITES: 1 exactly when its operand is
     nonzero, which is how peek turns a strchr result into a C boolean. *)
  Local Lemma ushp_snez_val (v : Z) :
    0 <= v < Z64 ->
    (zero_extend' 64 (bool_to_bit (zopz0zI_u (zero_reg : mword 64)
                                     (mword_of_int v))) : mword 64)
    = mword_of_int (if Z.ltb 0 v then 1 else 0).
  Proof.
    intro Hv.
    assert (Ez : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ez (moi_lt_u 0 v ltac:(unfold Z64; lia) Hv).
    destruct (Z.ltb 0 v); apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §3 strchr @0xa82 -- 17 instructions, a two-word frame, one loop.       *)
  (*                                                                       *)
  (*   char *strchr(const char *s, char c)                                  *)
  (*   { for(; *s; s++) if ( *s == c) return (char * )s; return 0; }        *)
  (*                                                                       *)
  (* THE BOTTOM OF THE PARSER.  [peek] calls it once per whitespace byte    *)
  (* and once for the token test; [gettoken] calls it in three separate     *)
  (* loops.  The contract is stated over an arbitrary [ustr] at an          *)
  (* arbitrary dfrac, so the two static tables (which a caller may hold     *)
  (* persistently) and the command buffer (which it owns) are the same      *)
  (* instance -- there is no table-specific version of this lemma.          *)
  (*                                                                       *)
  (* THE LOOP IS A BOUNDED ROCQ INDUCTION, not an iLob: what bounds it is   *)
  (* the [ustr] RESOURCE -- the terminator at [s + len] is one of its       *)
  (* conjuncts, and the back edge at 0xa9a is taken only on a non-NUL byte. *)
  (* echo's strlen mold, one function down.                                 *)
  (* ===================================================================== *)

  (* ===================================================================== *)
  (* THE TWO-WORD FRAME, ONCE.                                              *)
  (*                                                                       *)
  (* gcc gives every leaf function in this catalog the same opening and     *)
  (* closing, differing only in the frame's size:                           *)
  (*                                                                       *)
  (*   c.addi sp,sp,-16 ; c.sdsp ra,8(sp) ; c.sdsp s0,0(sp)                 *)
  (*                                     ; c.addi4spn s0,sp,16             *)
  (*   ...                                                                  *)
  (*   c.ldsp ra,8(sp) ; c.ldsp s0,0(sp) ; c.addi sp,sp,16 ; c.jr ra        *)
  (*                                                                       *)
  (* [strchr] and [strlen] are both two-word frames, and [strchr] reaches   *)
  (* its epilogue three different ways (hit, exhausted, empty string), so   *)
  (* writing the eight instructions out per function per path would be six  *)
  (* copies of one argument.  These two lemmas are that argument once: the  *)
  (* PCs are parameters and the four [uinstr_is] facts are premises, so a   *)
  (* call site is four one-line [iApply]s of its own catalog rows.  The     *)
  (* same shape at a bigger frame is what peek/gettoken/parseexec need, and *)
  (* generalising over the frame size [k] is the obvious next step -- but   *)
  (* it needs an [ustack_k] split per size, so it is not free.              *)
  (* ===================================================================== *)

  (* [add_vec_int] on a literal pc, without a [vm_compute] per instruction.
     Stage 2 proved one [assert (Exxx : add_vec_int (mword_of_int 0xNNN) k =
     mword_of_int 0xMMM) by (apply bv_eq; vm_compute; reflexivity)] at EVERY
     step; this is that fact once, and it is unconditional, because
     [mword_of_int] already reduces mod 2^64. *)
  Local Lemma ushp_pc_step (x d : Z) :
    add_vec_int (mword_of_int x : mword 64) d = mword_of_int (x + d).
  Proof. unfold add_vec_int. apply moi_add. Qed.

  (* THE FRAME POINTER, AS A PREMISE-FREE STEP.  [c.addi4spn s0,sp,N] is
     the last instruction of every prologue in this catalog and no function
     in the parser reads s0 except through its own epilogue, so what a walk
     needs of it is only "s0 gets SOMETHING" -- hiding the value behind a
     [∀ v] is both tidier at the call site and one fewer term for the
     unifier to carry.  NOT YET USED: it was written for peek's 0x458 and
     peek's body is parked (see the header's OBSTACLE note); gettoken,
     parsecmd, parseline, parsepipe, parseredirs and nulterminate all want
     it too. *)
  Local Lemma wp_kshp_fp (h : CpuId) (m : regfile) (p : Z) (nz : mword 8)
      (nn : nat) :
    uinstr_is γt (mword_of_int p) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), nz)) -∗
    urun γt γd γs h m (mword_of_int p) nn -∗
    (∀ (h' : CpuId) (v : mword 64),
       urun γt γd γs h' (<[Regidx s0_idx := regval_into_reg v]> m)
         (mword_of_int (p + 2)) nn -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hi Hrun Hcont".
    iApply (wp_uk_caddi4spn γt γd γs h m (mword_of_int p)
              (mword_of_int 0 : mword 3) nz s0_idx
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm nz))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "Hi Hrun").
    rewrite (ushp_pc_step p 2). iIntros (h1) "Hrun".
    iApply ("Hcont" $! h1 with "Hrun").
  Qed.

  (* THE PROLOGUE.  It hands back the two spilled words as [uword]s at the
     caller's own [sp], which is what makes the epilogue below a pure
     inverse: nothing about WHAT was spilled crosses the function body. *)
  Local Lemma wp_kshp_pro2 (h : CpuId) (m : regfile)
      (p0 p1 p2 p3 p4 : Z) (nn : nat) :
    p1 = p0 + 2 -> p2 = p1 + 2 -> p3 = p2 + 2 -> p4 = p3 + 2 ->
    uinstr_is γt (mword_of_int p0) true
      (C_ADDI (mword_of_int 48 : mword 6, Regidx csp_rs1)) -∗
    uinstr_is γt (mword_of_int p1) true
      (C_SDSP (mword_of_int 1 : mword 6, Regidx ra_idx)) -∗
    uinstr_is γt (mword_of_int p2) true
      (C_SDSP (mword_of_int 0 : mword 6, Regidx s0_idx)) -∗
    uinstr_is γt (mword_of_int p3) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)) -∗
    urun γt γd γs h m (mword_of_int p0) (2 + nn) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 16 <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1
           = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)) ⌝ -∗
       ⌜ forall q : mword 5,
           Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
           m' !!! Regidx q = m !!! Regidx q ⌝ -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 8) (m !!! Regidx ra_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 16) (m !!! Regidx s0_idx) -∗
       urun γt γd γs h' m' (mword_of_int p4) nn -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hp1 Hp2 Hp3 Hp4. subst p1 p2 p3 p4.
    iIntros "#Hi0 #Hi1 #Hi2 #Hi3 Hrun Hcont".
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 16 <= uint sp0) by lia.
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- p0  c.addi sp,sp,-16 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int p0)
              (mword_of_int 48 : mword 6) 2 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hi0 Hrun").
    rewrite Hsp ustack_2 (ushp_pc_step p0 2).
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    (* ---- p1  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h1 m1 (mword_of_int (p0 + 2))
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 nn
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "Hi1 Hw8 Hrun").
    iIntros "Hw8".
    rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    rewrite (ushp_pc_step (p0 + 2) 2). iIntros (h2) "Hrun".
    (* ---- p2  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h2 m1 (mword_of_int (p0 + 2 + 2))
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 nn
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "Hi2 Hw0 Hrun").
    iIntros "Hw0".
    rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    rewrite (ushp_pc_step (p0 + 2 + 2) 2). iIntros (h3) "Hrun".
    (* ---- p3  c.addi4spn s0,sp,16 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs h3 m1 (mword_of_int (p0 + 2 + 2 + 2))
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "Hi3 Hrun").
    rewrite (ushp_pc_step (p0 + 2 + 2 + 2) 2). iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    iApply ("Hcont" $! h4 m2 with "[] [] [] [] Hw8 Hw0 Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro.
      rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1.
    - iPureIntro. intros q Hqsp Hqs0.
      rewrite (Hm2 q Hqs0). exact (Hm1 q Hqsp).
  Qed.

  (* THE EPILOGUE -- the prologue's inverse, and the point at which the
     caller's [ucallee_saved] read-back is assembled. *)
  Local Lemma wp_kshp_epi2 (h : CpuId) (me : regfile)
      (q0 q1 q2 q3 : Z) (sp0 vra vs0 : mword 64) (nn : nat) :
    q1 = q0 + 2 -> q2 = q1 + 2 -> q3 = q2 + 2 ->
    uint sp0 mod 8 = 0 ->
    16 <= uint sp0 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)) ->
    uinstr_is γt (mword_of_int q0) true
      (C_LDSP (mword_of_int 1 : mword 6, Regidx ra_idx)) -∗
    uinstr_is γt (mword_of_int q1) true
      (C_LDSP (mword_of_int 0 : mword 6, Regidx s0_idx)) -∗
    uinstr_is γt (mword_of_int q2) true
      (C_ADDI (mword_of_int 16 : mword 6, Regidx csp_rs1)) -∗
    uinstr_is γt (mword_of_int q3) true (C_JR (Regidx ra_idx)) -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    urun γt γd γs h me (mword_of_int q0) nn -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ forall q : mword 5,
           Regidx q <> Regidx ra_idx -> Regidx q <> Regidx s0_idx ->
           Regidx q <> Regidx csp_rs1 ->
           m' !!! Regidx q = me !!! Regidx q ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       urun γt γd γs h' m' (ret_pc vra) (2 + nn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hq1 Hq2 Hq3 Hal8 Hlo Hsp. subst q1 q2 q3.
    iIntros "#Hi0 #Hi1 #Hi2 #Hi3 Hw8 Hw0 Hrun Hcont".
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- q0  c.ldsp ra,8(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h me (mword_of_int q0)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) vra nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "Hi0 Hw8 Hrun").
    iIntros "Hw8".
    rewrite (ushp_pc_step q0 2). iIntros (h1) "Hrun".
    set (e1 := <[Regidx ra_idx := regval_into_reg vra]> me).
    assert (Hspe1 : e1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (upd_ne me (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp. }
    (* ---- q1  c.ldsp s0,0(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h1 e1 (mword_of_int (q0 + 2))
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) vs0 nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspe1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "Hi1 Hw0 Hrun").
    iIntros "Hw0".
    rewrite (ushp_pc_step (q0 + 2) 2). iIntros (h2) "Hrun".
    set (e2 := <[Regidx s0_idx := regval_into_reg vs0]> e1).
    assert (Hspe2 : e2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (upd_ne e1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspe1. }
    (* ---- q2  c.addi sp,sp,16 -- THE POP ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt2 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   + 8 * Z.of_nat 2 < Z64)
      by (rewrite Hbsp1; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    (8 * Z.of_nat 2) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                 (8 * Z.of_nat 2) ltac:(lia) Hlt2).
      rewrite Hbsp1. lia. }
    iApply (wp_uk_caddi_sp_up γt γd γs h2 e2 (mword_of_int (q0 + 2 + 2))
              (mword_of_int 16 : mword 6) 2 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hi2 [Hw8 Hw0] Hrun").
    { rewrite Hspe2 Hup ustack_2.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hw8"; [ iExists vra; iFrame | iExists vs0; iFrame ]. }
    rewrite Hspe2 Hup (ushp_pc_step (q0 + 2 + 2) 2).
    iIntros (h3) "Hrun".
    set (e3 := <[Regidx csp_rs1 := regval_into_reg sp0]> e2).
    assert (Hra3 : e3 !!! Regidx ra_idx = vra).
    { rewrite (upd_ne e2 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne e1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq me (Regidx ra_idx) (regval_into_reg vra)). }
    (* ---- q3  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h3 e3 (mword_of_int (q0 + 2 + 2 + 2)) ra_idx
              (ret_pc vra) (2 + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra3; reflexivity)
              with "Hi3 Hrun").
    iIntros (h4) "Hrun".
    iApply ("Hcont" $! h4 e3 with "[] [] [] Hrun").
    - iPureIntro. intros q Hqra Hqs0 Hqsp.
      rewrite /e3 (upd_ne e2 (Regidx csp_rs1) (Regidx q) _ Hqsp).
      rewrite /e2 (upd_ne e1 (Regidx s0_idx) (Regidx q) _ Hqs0).
      exact (upd_ne me (Regidx ra_idx) (Regidx q) _ Hqra).
    - iPureIntro.
      exact (upd_eq e2 (Regidx csp_rs1) (regval_into_reg sp0)).
    - iPureIntro.
      rewrite /e3 (upd_ne e2 (Regidx csp_rs1) (Regidx s0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq e1 (Regidx s0_idx) (regval_into_reg vs0)).
  Qed.

  (* the loop body, 0xa90..0xa9a:
       beq a1,a5,0xa9e ; c.addi a0,a0,1 ; lbu a5,0(a0) ; c.bnez a5,0xa90
     [j] is the index the scan has reached, [r = len - j] the measure, and
     a5 already holds the byte AT [j] (the previous [lbu] loaded it). *)
  Local Lemma wp_kshp_strchr_loop (dq : dfrac) (s : Z) (len : nat)
      (f : nat -> bv 8) (c : bv 8) (nn : nat) :
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s -> s + Z.of_nat len < Z64 ->
    mc !!! Regidx a0_idx = mword_of_int (s + Z.of_nat j) ->
    mc !!! Regidx a5_idx = mword_of_int (bv_unsigned (f j)) ->
    mc !!! Regidx a1_idx = mword_of_int (bv_unsigned c) ->
    shp_code γt -∗
    ustr γd dq s len f -∗
    urun γt γd γs h mc (mword_of_int 0xa90) nn -∗
    (ustr γd dq s len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5,
             Regidx q <> Regidx a0_idx -> Regidx q <> Regidx a5_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx a0_idx
             = mword_of_int (ushp_chr s (len - j) j f c) ⌝ -∗
         urun γt γd γs h' mc' (mword_of_int 0xa9e) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Ha0 Ha5 Ha1;
      iIntros "#Hcode Hstr Hrun Hcont"; [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    destruct (decide (f j = c)) as [ Hhit | Hhit ].
    { (* ---- 0xa90  beq a1,a5 -- TAKEN: this byte IS the one ---- *)
      assert (Htk : true = uv_btaken BEQ (mc !!! Regidx a1_idx)
                             (mc !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha1 Ha5.
        rewrite (ushp_zext_eq (f j) c). symmetry.
        exact (bool_decide_eq_true_2 _ Hhit). }
      iApply (wp_uk_btype γt γd γs h mc (mword_of_int 0xa90)
                (mword_of_int 14 : mword 13) a5_idx a1_idx BEQ true
                (mword_of_int 0xa9e) nn
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_a90 with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros q _ _. reflexivity.
      - iPureIntro. rewrite Ha0 Hr.
        rewrite (ushp_chr_hit s (S r) j f c j (ushp_find_S_hit r j f c Hhit)).
        reflexivity. }
    (* ---- 0xa90  beq a1,a5 -- NOT taken ---- *)
    assert (Htk : false = uv_btaken BEQ (mc !!! Regidx a1_idx)
                            (mc !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Ha1 Ha5.
      rewrite (ushp_zext_eq (f j) c). symmetry.
      exact (bool_decide_eq_false_2 _ Hhit). }
    iApply (wp_uk_btype γt γd γs h mc (mword_of_int 0xa90)
              (mword_of_int 14 : mword 13) a5_idx a1_idx BEQ false
              (mword_of_int 0xa9e) nn
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_a90 with "Hcode"). }
    assert (Ea90 : add_vec_int (mword_of_int 0xa90 : mword 64) 4
                   = mword_of_int 0xa94)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea90. iIntros (h1) "Hrun".
    (* ---- 0xa94  c.addi a0,a0,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs h1 mc (mword_of_int 0xa94)
              (mword_of_int 1 : mword 6) a0_idx
              (mword_of_int (s + Z.of_nat (S j))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0 E1 moi_add;
                    replace (s + Z.of_nat (S j)) with (s + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_a94 with "Hcode"). }
    assert (Ea94 : add_vec_int (mword_of_int 0xa94 : mword 64) 2
                   = mword_of_int 0xa96)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea94. iIntros (h2) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (s + Z.of_nat (S j))
                                     : mword 64)]> mc).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m1 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = mword_of_int (s + Z.of_nat (S j)))
      by exact (upd_eq mc (Regidx a0_idx)
                  (regval_into_reg (mword_of_int (s + Z.of_nat (S j))
                                    : mword 64))).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = mword_of_int (bv_unsigned c))
      by (rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)); exact Ha1).
    (* ---- 0xa96  lbu a5,0(a0) -- the NEXT byte.  It is the string's       *)
    (* [S j]-th when there is one and its TERMINATOR when there is not, and *)
    (* those are two different conjuncts of [ustr], so the walk splits.     *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* ---- the terminator: the loop ends and strchr returns 0 ---- *)
      iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_uk_lbu γt γd γs h2 m1 (mword_of_int 0xa96)
                (mword_of_int 0 : mword 12) a0_idx a5_idx dq
                (s + Z.of_nat len) ubyte0 nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha0_1 Hend
                        (uint_moi (s + Z.of_nat len)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_shp_a96 with "Hcode"). }
      iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
      assert (Ea96 : add_vec_int (mword_of_int 0xa96 : mword 64) 4
                     = mword_of_int 0xa9a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea96. iIntros (h3) "Hrun".
      set (m2 := <[Regidx a5_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8) : mword 64)]> m1).
      assert (Ha5_2 : m2 !!! Regidx a5_idx
                      = mword_of_int (bv_unsigned ubyte0)).
      { rewrite (upd_eq m1 (Regidx a5_idx)
                   (regval_into_reg (zero_extend' 64 (ubyte0 : mword 8) : mword 64))).
        exact (zext8_moi ubyte0). }
      assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                      m2 !!! Regidx q = m1 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m1 (Regidx a5_idx) (Regidx q) _ Hq)).
      (* ---- 0xa9a  c.bnez a5,0xa90 -- NOT taken ---- *)
      assert (Htk2 : false = neq_vec (m2 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_2. unfold neq_vec. rewrite (ushp_zext_nul ubyte0).
        rewrite (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl).
        reflexivity. }
      iApply (wp_uk_cbnez γt γd γs h3 m2 (mword_of_int 0xa9a)
                (mword_of_int 251 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx false (mword_of_int 0xa90) nn
                ltac:(vm_compute; reflexivity) Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_a9a with "Hcode"). }
      assert (Ea9a : add_vec_int (mword_of_int 0xa9a : mword 64) 2
                     = mword_of_int 0xa9c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea9a. iIntros (h4) "Hrun".
      (* ---- 0xa9c  c.li a0,0 (compressed, so the step is 2) ---- *)
      iApply (wp_uk_cli γt γd γs h4 m2 (mword_of_int 0xa9c)
                (mword_of_int 0 : mword 6) a0_idx nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_a9c with "Hcode"). }
      assert (Ea9c : add_vec_int (mword_of_int 0xa9c : mword 64) 2
                     = mword_of_int 0xa9e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea9c. iIntros (h5) "Hrun".
      assert (Hnone : ushp_find (len - j) j f c = None).
      { rewrite Hr (ushp_find_S_miss r j f c Hhit).
        assert (Hr0 : r = 0%nat) by lia. rewrite Hr0.
        exact (ushp_find_0 (S j) f c). }
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros q Hq0 Hq5.
        rewrite (upd_ne m2 (Regidx a0_idx) (Regidx q) _ Hq0).
        rewrite (Hm2 q Hq5). exact (Hm1 q Hq0).
      - iPureIntro.
        rewrite (upd_eq m2 (Regidx a0_idx)
                   (regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64))).
        rewrite (ushp_chr_miss s (len - j) j f c Hnone).
        apply bv_eq. vm_compute. reflexivity. }
    (* ---- a BODY byte: the loop goes round ---- *)
    assert (Hj1 : (S j < len)%nat) by lia.
    iDestruct (ustr_byte γd dq s len f (S j) Hj1 with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs h2 m1 (mword_of_int 0xa96)
              (mword_of_int 0 : mword 12) a0_idx a5_idx dq
              (s + Z.of_nat (S j)) (f (S j)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_1
                      (uint_moi (s + Z.of_nat (S j))
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_a96 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    assert (Ea96 : add_vec_int (mword_of_int 0xa96 : mword 64) 4
                   = mword_of_int 0xa9a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea96. iIntros (h3) "Hrun".
    set (m2 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 ((f (S j)) : mword 8)
                                     : mword 64)]> m1).
    assert (Ha5_2 : m2 !!! Regidx a5_idx = mword_of_int (bv_unsigned (f (S j)))).
    { rewrite (upd_eq m1 (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 ((f (S j)) : mword 8) : mword 64))).
      exact (zext8_moi (f (S j))). }
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int (s + Z.of_nat (S j)))
      by (rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_1).
    assert (Ha1_2 : m2 !!! Regidx a1_idx = mword_of_int (bv_unsigned c))
      by (rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)); exact Ha1_1).
    (* ---- 0xa9a  c.bnez a5,0xa90 -- TAKEN: the byte is not the NUL ---- *)
    assert (Htk2 : true = neq_vec (m2 !!! Regidx a5_idx) zero_reg).
    { rewrite Ha5_2. unfold neq_vec. rewrite (ushp_zext_nul (f (S j))).
      rewrite (bool_decide_eq_false_2 (f (S j) = ubyte0) (Hne (S j) Hj1)).
      reflexivity. }
    iApply (wp_uk_cbnez γt γd γs h3 m2 (mword_of_int 0xa9a)
              (mword_of_int 251 : mword 8) (mword_of_int 7 : mword 3)
              a5_idx true (mword_of_int 0xa90) nn
              ltac:(vm_compute; reflexivity) Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_a9a with "Hcode"). }
    iIntros (h4) "Hrun".
    iApply (IH (S j) h4 m2 ltac:(lia) Hj1 Hs0 Hs64 Ha0_2 Ha5_2 Ha1_2
              with "Hcode Hstr Hrun").
    iIntros "Hstr" (h5 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr [] [] Hrun").
    - iPureIntro. intros q Hq0 Hq5.
      rewrite (Hpres q Hq0 Hq5). rewrite (Hm2 q Hq5). exact (Hm1 q Hq0).
    - iPureIntro. rewrite Hret.
      assert (Erj : (len - j)%nat = S (len - S j)%nat) by lia.
      unfold ushp_chr. rewrite Erj (ushp_find_S_miss (len - S j) j f c Hhit).
      reflexivity.
  Qed.

  (* ---- strchr, the whole function ------------------------------------- *)
  Lemma wp_kshp_strchr (h : CpuId) (m : regfile) (dq : dfrac) (s : Z)
      (len : nat) (f : nat -> bv 8) (c : bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s ->
    m !!! Regidx a1_idx = mword_of_int (bv_unsigned c) ->
    0 <= s -> s + Z.of_nat len < Z64 ->
    shp_code γt -∗
    ustr γd dq s len f -∗
    urun γt γd γs h m (mword_of_int ShSyms.strchr) (2 + nn) -∗
    (ustr γd dq s len f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int (ushp_chr s len 0%nat f c) ⌝ -∗
         urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hs0 Hs64. iIntros "#Hcode Hstr Hrun Hcont".
    rewrite shpp_strchr.
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    set (sp0 := m !!! Regidx csp_rs1).
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    (* ---- 0xa82..0xa88, the two-word prologue ---- *)
    iApply (wp_kshp_pro2 h m 0xa82 0xa84 0xa86 0xa88 0xa8a nn
              ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
              ltac:(reflexivity)
              with "[] [] [] [] Hrun").
    { iApply (uis_shp_a82 with "Hcode"). }
    { iApply (uis_shp_a84 with "Hcode"). }
    { iApply (uis_shp_a86 with "Hcode"). }
    { iApply (uis_shp_a88 with "Hcode"). }
    iIntros (h4 m2) "%Hal8 %Hlo %Hsp2 %Hm12 Hw8 Hw0 Hrun".
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int s)
      by (rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha0).
    assert (Ha1_2 : m2 !!! Regidx a1_idx = mword_of_int (bv_unsigned c))
      by (rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha1).
    (* WHAT THE CALLER READS BACK, in both arms: the epilogue restores ra,
       s0 and sp, and everything the body wrote is a-register traffic, so
       what comes back is exactly [ucallee_saved]. *)
    (* ---- 0xa8a  lbu a5,0(a0) -- the FIRST byte, which is the string's
       byte 0 when it is non-empty and its TERMINATOR when it is not ---- *)
    destruct (Nat.eq_dec len 0) as [ Hlen0 | Hlen0 ].
    { (* ---- the EMPTY string: strchr returns 0 without the loop ---- *)
      iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_uk_lbu γt γd γs h4 m2 (mword_of_int 0xa8a)
                (mword_of_int 0 : mword 12) a0_idx a5_idx dq
                (s + Z.of_nat len) ubyte0 nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha0_2 Hlen0;
                      rewrite (uint_moi s ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_shp_a8a with "Hcode"). }
      iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
      assert (Ea8a : add_vec_int (mword_of_int 0xa8a : mword 64) 4
                     = mword_of_int 0xa8e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea8a. iIntros (h5) "Hrun".
      set (m3 := <[Regidx a5_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8) : mword 64)]> m2).
      assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int (bv_unsigned ubyte0)).
      { rewrite (upd_eq m2 (Regidx a5_idx)
                   (regval_into_reg (zero_extend' 64 (ubyte0 : mword 8) : mword 64))).
        exact (zext8_moi ubyte0). }
      assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                      m3 !!! Regidx q = m2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m2 (Regidx a5_idx) (Regidx q) _ Hq)).
      (* ---- 0xa8e  c.beqz a5,0xaa6 -- TAKEN ---- *)
      assert (Htk : true = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (ushp_zext_nul ubyte0). symmetry.
        exact (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl). }
      iApply (wp_uk_cbeqz γt γd γs h5 m3 (mword_of_int 0xa8e)
                (mword_of_int 12 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0xaa6) nn
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_a8e with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0xaa6  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs h6 m3 (mword_of_int 0xaa6)
                (mword_of_int 0 : mword 6) a0_idx nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_aa6 with "Hcode"). }
      assert (Eaa6 : add_vec_int (mword_of_int 0xaa6 : mword 64) 2
                     = mword_of_int 0xaa8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eaa6. iIntros (h7) "Hrun".
      set (m4 := <[Regidx a0_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)]> m3).
      (* ---- 0xaa8  c.j 0xa9e ---- *)
      iApply (wp_uk_cj γt γd γs h7 m4 (mword_of_int 0xaa8)
                (mword_of_int 2043 : mword 11) (mword_of_int 0xa9e) nn
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_aa8 with "Hcode"). }
      iIntros (h8) "Hrun".
      assert (Hsp4 : m4 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 2))).
      { rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
      iApply (wp_kshp_epi2 h8 m4 0xa9e 0xaa0 0xaa2 0xaa4 sp0 vra vs0 nn
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hal8 Hlo Hsp4
                with "[] [] [] [] Hw8 Hw0 Hrun").
      { iApply (uis_shp_a9e with "Hcode"). }
      { iApply (uis_shp_aa0 with "Hcode"). }
      { iApply (uis_shp_aa2 with "Hcode"). }
      { iApply (uis_shp_aa4 with "Hcode"). }
      iIntros (h9 m') "%Hpres %Hspf %Hs0f Hrun".
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros q Hq.
        destruct (Z.eq_dec (uint q) 2) as [ Eq2 | Eq2 ].
        { rewrite (ushp_ridx_eq q csp_rs1
                     ltac:(rewrite Eq2; vm_compute; reflexivity)).
          exact Hspf. }
        destruct (Z.eq_dec (uint q) 8) as [ Eq8 | Eq8 ].
        { rewrite (ushp_ridx_eq q s0_idx
                     ltac:(rewrite Eq8; vm_compute; reflexivity)).
          exact Hs0f. }
        assert (Hqsp : Regidx q <> Regidx csp_rs1)
          by (apply ushp_ridx_ne;
              assert (Hc2 : uint csp_rs1 = 2) by (vm_compute; reflexivity);
              rewrite Hc2; exact Eq2).
        assert (Hqs0 : Regidx q <> Regidx s0_idx)
          by (apply ushp_ridx_ne;
              assert (Hc8 : uint s0_idx = 8) by (vm_compute; reflexivity);
              rewrite Hc8; exact Eq8).
        assert (Hqra : Regidx q <> Regidx ra_idx)
          by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
        rewrite (Hpres q Hqra Hqs0 Hqsp).
        rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx q) _
                       (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
        rewrite (Hm3 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
        exact (Hm12 q Hqsp Hqs0).
      - iPureIntro.
        rewrite (Hpres a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /m4 (upd_eq m3 (Regidx a0_idx)
                       (regval_into_reg
                          (sign_extend' 64 (mword_of_int 0 : mword 6)
                           : mword 64))).
        assert (Hnone : ushp_find len 0%nat f c = None)
          by (rewrite Hlen0; exact (ushp_find_0 0%nat f c)).
        rewrite (ushp_chr_miss s len 0%nat f c Hnone).
        apply bv_eq. vm_compute. reflexivity. }
    (* ---- a NON-EMPTY string: byte 0 is [f 0] and the loop is entered --- *)
    assert (H0len : (0 < len)%nat) by lia.
    iDestruct (ustr_byte γd dq s len f 0%nat H0len with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs h4 m2 (mword_of_int 0xa8a)
              (mword_of_int 0 : mword 12) a0_idx a5_idx dq
              (s + Z.of_nat 0) (f 0%nat) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_2;
                    replace (s + Z.of_nat 0) with s by lia;
                    rewrite (uint_moi s ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_a8a with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    assert (Ea8a : add_vec_int (mword_of_int 0xa8a : mword 64) 4
                   = mword_of_int 0xa8e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea8a. iIntros (h5) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 ((f 0%nat) : mword 8)
                                     : mword 64)]> m2).
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int (bv_unsigned (f 0%nat))).
    { rewrite (upd_eq m2 (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 ((f 0%nat) : mword 8) : mword 64))).
      exact (zext8_moi (f 0%nat)). }
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int (s + Z.of_nat 0%nat)).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      replace (s + Z.of_nat 0%nat) with s by lia. exact Ha0_2. }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (bv_unsigned c))
      by (rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)); exact Ha1_2).
    assert (Hsp3 : m3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp2).
    (* ---- 0xa8e  c.beqz a5,0xaa6 -- NOT taken: byte 0 is not the NUL ---- *)
    assert (Htk : false = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
    { rewrite Ha5_3 (ushp_zext_nul (f 0%nat)). symmetry.
      exact (bool_decide_eq_false_2 (f 0%nat = ubyte0) (Hne 0%nat H0len)). }
    iApply (wp_uk_cbeqz γt γd γs h5 m3 (mword_of_int 0xa8e)
              (mword_of_int 12 : mword 8) (mword_of_int 7 : mword 3)
              a5_idx false (mword_of_int 0xaa6) nn
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_a8e with "Hcode"). }
    assert (Ea8e : add_vec_int (mword_of_int 0xa8e : mword 64) 2
                   = mword_of_int 0xa90)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea8e. iIntros (h6) "Hrun".
    iApply (wp_kshp_strchr_loop dq s len f c nn (len - 0)%nat 0%nat h6 m3
              eq_refl H0len Hs0 Hs64 Ha0_3 Ha5_3 Ha1_3
              with "Hcode Hstr Hrun").
    iIntros "Hstr" (h7 mc') "%Hpres %Hret Hrun".
    assert (Hspc : mc' !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hpres csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp3).
    iApply (wp_kshp_epi2 h7 mc' 0xa9e 0xaa0 0xaa2 0xaa4 sp0 vra vs0 nn
              ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
              Hal8 Hlo Hspc
              with "[] [] [] [] Hw8 Hw0 Hrun").
    { iApply (uis_shp_a9e with "Hcode"). }
    { iApply (uis_shp_aa0 with "Hcode"). }
    { iApply (uis_shp_aa2 with "Hcode"). }
    { iApply (uis_shp_aa4 with "Hcode"). }
    iIntros (h8 m') "%Hpres2 %Hspf %Hs0f Hrun".
    iApply ("Hcont" with "Hstr [] [] Hrun").
    - iPureIntro. intros q Hq.
      destruct (Z.eq_dec (uint q) 2) as [ Eq2 | Eq2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite Eq2; vm_compute; reflexivity)).
        exact Hspf. }
      destruct (Z.eq_dec (uint q) 8) as [ Eq8 | Eq8 ].
      { rewrite (ushp_ridx_eq q s0_idx
                   ltac:(rewrite Eq8; vm_compute; reflexivity)).
        exact Hs0f. }
      assert (Hqsp : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
              assert (Hc2 : uint csp_rs1 = 2) by (vm_compute; reflexivity);
              rewrite Hc2; exact Eq2).
      assert (Hqs0 : Regidx q <> Regidx s0_idx)
        by (apply ushp_ridx_ne;
              assert (Hc8 : uint s0_idx = 8) by (vm_compute; reflexivity);
              rewrite Hc8; exact Eq8).
      assert (Hqra : Regidx q <> Regidx ra_idx)
        by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
      rewrite (Hpres2 q Hqra Hqs0 Hqsp).
      rewrite (Hpres q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))
                 (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm3 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
      exact (Hm12 q Hqsp Hqs0).
    - iPureIntro.
      rewrite (Hpres2 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite Hret. replace (len - 0)%nat with len by lia. reflexivity.
  Qed.


  (* ===================================================================== *)
  (* §4 strlen @0xa30 -- 18 instructions, a two-word frame, one loop.        *)
  (*                                                                       *)
  (*   int strlen(const char *s)                                            *)
  (*   { int n; for(n = 0; s[n]; n++) ; return n; }                         *)
  (*                                                                       *)
  (* [parsecmd]'s FIRST act: [es = s + strlen(s)] is how the parser learns  *)
  (* where the line ends, and every [peek] and [gettoken] below it takes    *)
  (* that [es] as its bound.  So the whole parser's notion of where the     *)
  (* input ends is this lemma's postcondition, and the postcondition is     *)
  (* [len] EXACTLY -- the length the [ustr] resource already pins, not a    *)
  (* fresh existential.                                                     *)
  (*                                                                       *)
  (* gcc's loop is one instruction off the source: it carries [a3] = the    *)
  (* address of the byte it is ABOUT to test and [a5] = that address plus   *)
  (* one, and the count is recovered at the end by [subw a0,a3,a0] -- a     *)
  (* 32-BIT subtraction, which is why [ustr] carries [len < 2^31] as part   *)
  (* of what a string IS rather than as a caller's side condition.          *)
  (* ===================================================================== *)

  (* [c.mv rd,rs] is [add rd,x0,rs], so the value written is [0 + rs]. *)
  Local Lemma ushp_mv_val (v : Z) :
    add_vec zero_reg (mword_of_int v : mword 64) = mword_of_int v.
  Proof.
    assert (Ez : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ez moi_add. f_equal; lia.
  Qed.

  (* the loop body, 0xa42..0xa4a:
       c.mv a3,a5 ; c.addi a5,a5,1 ; lbu a4,-1(a5) ; c.bnez a4,0xa42
     [k] is the index of the last byte KNOWN non-NUL, so [a5] is one past
     it and the byte the iteration tests is [s + k + 1].  The measure is
     [len - k] and the [ustr] terminator is what stops it. *)
  Local Lemma wp_kshp_strlen_loop (dq : dfrac) (s : Z) (len : nat)
      (f : nat -> bv 8) (nn : nat) :
    forall (r k : nat) (h : CpuId) (mc : regfile),
    (len - k = r)%nat -> (k < len)%nat ->
    0 <= s -> s + Z.of_nat len + 1 < Z64 ->
    mc !!! Regidx a5_idx = mword_of_int (s + Z.of_nat k + 1) ->
    shp_code γt -∗
    ustr γd dq s len f -∗
    urun γt γd γs h mc (mword_of_int 0xa42) nn -∗
    (ustr γd dq s len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5,
             Regidx q <> Regidx a3_idx -> Regidx q <> Regidx a4_idx ->
             Regidx q <> Regidx a5_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx a3_idx = mword_of_int (s + Z.of_nat len) ⌝ -∗
         urun γt γd γs h' mc' (mword_of_int 0xa4c) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros k h mc Hr Hk Hs0 Hs64 Ha5;
      iIntros "#Hcode Hstr Hrun Hcont"; [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- 0xa42  c.mv a3,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs h mc (mword_of_int 0xa42)
              a3_idx a5_idx (mword_of_int (s + Z.of_nat k + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5; symmetry;
                    exact (ushp_mv_val (s + Z.of_nat k + 1)))
              with "[] Hrun").
    { iApply (uis_shp_a42 with "Hcode"). }
    rewrite (ushp_pc_step 0xa42 2). iIntros (h1) "Hrun".
    set (m1 := <[Regidx a3_idx
                 := regval_into_reg (mword_of_int (s + Z.of_nat k + 1)
                                     : mword 64)]> mc).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx a3_idx ->
                    m1 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc (Regidx a3_idx) (Regidx q) _ Hq)).
    assert (Ha3_1 : m1 !!! Regidx a3_idx = mword_of_int (s + Z.of_nat k + 1))
      by exact (upd_eq mc (Regidx a3_idx)
                  (regval_into_reg (mword_of_int (s + Z.of_nat k + 1)
                                    : mword 64))).
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int (s + Z.of_nat k + 1))
      by (rewrite (Hm1 a5_idx ltac:(vm_compute; discriminate)); exact Ha5).
    (* ---- 0xa44  c.addi a5,a5,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs h1 m1 (mword_of_int 0xa44)
              (mword_of_int 1 : mword 6) a5_idx
              (mword_of_int (s + Z.of_nat k + 2)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1 E1 moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_a44 with "Hcode"). }
    rewrite (ushp_pc_step 0xa44 2). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (s + Z.of_nat k + 2)
                                     : mword 64)]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_2 : m2 !!! Regidx a5_idx = mword_of_int (s + Z.of_nat k + 2))
      by exact (upd_eq m1 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + Z.of_nat k + 2)
                                    : mword 64))).
    assert (Ha3_2 : m2 !!! Regidx a3_idx = mword_of_int (s + Z.of_nat k + 1))
      by (rewrite (Hm2 a3_idx ltac:(vm_compute; discriminate)); exact Ha3_1).
    (* ---- 0xa46  lbu a4,-1(a5) -- the byte at [s + k + 1], which is the
       string's [S k]-th when there is one and its TERMINATOR when not ---- *)
    assert (Haddr : s + Z.of_nat (S k)
                    = uint (m2 !!! Regidx a5_idx)
                      + uoff_i12 (mword_of_int 4095 : mword 12)).
    { rewrite Ha5_2 (uint_moi (s + Z.of_nat k + 2) ltac:(unfold Z64 in *; lia)).
      vm_compute uoff_i12. lia. }
    destruct (Nat.eq_dec (S k) len) as [ Hend | Hend ].
    { (* ---- the terminator: the loop ends and [a3] names the NUL ---- *)
      iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_uk_lbu γt γd γs h2 m2 (mword_of_int 0xa46)
                (mword_of_int 4095 : mword 12) a5_idx a4_idx dq
                (s + Z.of_nat len) ubyte0 nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite <- Hend; exact Haddr)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_shp_a46 with "Hcode"). }
      iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
      rewrite (ushp_pc_step 0xa46 4). iIntros (h3) "Hrun".
      set (m3 := <[Regidx a4_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                       : mword 64)]> m2).
      assert (Ha4_3 : m3 !!! Regidx a4_idx
                      = mword_of_int (bv_unsigned ubyte0)).
      { rewrite (upd_eq m2 (Regidx a4_idx)
                   (regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                     : mword 64))).
        exact (zext8_moi ubyte0). }
      assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                      m3 !!! Regidx q = m2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m2 (Regidx a4_idx) (Regidx q) _ Hq)).
      (* ---- 0xa4a  c.bnez a4,0xa42 -- NOT taken ---- *)
      assert (Htk : false = neq_vec (m3 !!! Regidx a4_idx) zero_reg).
      { rewrite Ha4_3. unfold neq_vec. rewrite (ushp_zext_nul ubyte0).
        rewrite (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl).
        reflexivity. }
      iApply (wp_uk_cbnez γt γd γs h3 m3 (mword_of_int 0xa4a)
                (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3)
                a4_idx false (mword_of_int 0xa42) nn
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_a4a with "Hcode"). }
      rewrite (ushp_pc_step 0xa4a 2). iIntros (h4) "Hrun".
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros q Hq3 Hq4 Hq5.
        rewrite (Hm3 q Hq4). rewrite (Hm2 q Hq5). exact (Hm1 q Hq3).
      - iPureIntro.
        rewrite (Hm3 a3_idx ltac:(vm_compute; discriminate)) Ha3_2.
        f_equal; lia. }
    (* ---- a BODY byte: the loop goes round ---- *)
    assert (Hk1 : (S k < len)%nat) by lia.
    iDestruct (ustr_byte γd dq s len f (S k) Hk1 with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs h2 m2 (mword_of_int 0xa46)
              (mword_of_int 4095 : mword 12) a5_idx a4_idx dq
              (s + Z.of_nat (S k)) (f (S k)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_a46 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0xa46 4). iIntros (h3) "Hrun".
    set (m3 := <[Regidx a4_idx
                 := regval_into_reg (zero_extend' 64 ((f (S k)) : mword 8)
                                     : mword 64)]> m2).
    assert (Ha4_3 : m3 !!! Regidx a4_idx = mword_of_int (bv_unsigned (f (S k)))).
    { rewrite (upd_eq m2 (Regidx a4_idx)
                 (regval_into_reg (zero_extend' 64 ((f (S k)) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f (S k))). }
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha5_3 : m3 !!! Regidx a5_idx
                    = mword_of_int (s + Z.of_nat (S k) + 1)).
    { rewrite (Hm3 a5_idx ltac:(vm_compute; discriminate)) Ha5_2.
      f_equal; lia. }
    (* ---- 0xa4a  c.bnez a4,0xa42 -- TAKEN ---- *)
    assert (Htk : true = neq_vec (m3 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_3. unfold neq_vec. rewrite (ushp_zext_nul (f (S k))).
      rewrite (bool_decide_eq_false_2 (f (S k) = ubyte0) (Hne (S k) Hk1)).
      reflexivity. }
    iApply (wp_uk_cbnez γt γd γs h3 m3 (mword_of_int 0xa4a)
              (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3)
              a4_idx true (mword_of_int 0xa42) nn
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_a4a with "Hcode"). }
    iIntros (h4) "Hrun".
    iApply (IH (S k) h4 m3 ltac:(lia) Hk1 Hs0 Hs64 Ha5_3
              with "Hcode Hstr Hrun").
    iIntros "Hstr" (h5 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr [] [] Hrun").
    - iPureIntro. intros q Hq3 Hq4 Hq5.
      rewrite (Hpres q Hq3 Hq4 Hq5).
      rewrite (Hm3 q Hq4). rewrite (Hm2 q Hq5). exact (Hm1 q Hq3).
    - iPureIntro. exact Hret.
  Qed.

  (* a pointer comparison against a NAMED address, as the back edge of a
     scan tests it *)
  Local Lemma ushp_moi_neq (x y : Z) :
    0 <= x < Z64 -> 0 <= y < Z64 ->
    neq_vec (mword_of_int x : mword 64) (mword_of_int y) = negb (Z.eqb x y).
  Proof.
    intros Hx Hy. unfold neq_vec. rewrite (moi_eq_vec x y Hx Hy). reflexivity.
  Qed.

  (* ---- strlen, the whole function ------------------------------------- *)
  Lemma wp_kshp_strlen (h : CpuId) (m : regfile) (dq : dfrac) (s : Z)
      (len : nat) (f : nat -> bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s ->
    0 <= s -> s + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    ustr γd dq s len f -∗
    urun γt γd γs h m (mword_of_int ShSyms.strlen) (2 + nn) -∗
    (ustr γd dq s len f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int (Z.of_nat len) ⌝ -∗
         urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hs0 Hs64. iIntros "#Hcode Hstr Hrun Hcont".
    rewrite shpp_strlen.
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    iDestruct (ustr_len with "Hstr") as %Hlen31.
    set (sp0 := m !!! Regidx csp_rs1).
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    (* ---- 0xa30..0xa36, the two-word prologue ---- *)
    iApply (wp_kshp_pro2 h m 0xa30 0xa32 0xa34 0xa36 0xa38 nn
              ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
              ltac:(reflexivity)
              with "[] [] [] [] Hrun").
    { iApply (uis_shp_a30 with "Hcode"). }
    { iApply (uis_shp_a32 with "Hcode"). }
    { iApply (uis_shp_a34 with "Hcode"). }
    { iApply (uis_shp_a36 with "Hcode"). }
    iIntros (h4 m2) "%Hal8 %Hlo %Hsp2 %Hm12 Hw8 Hw0 Hrun".
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int s)
      by (rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha0).
    (* ---- 0xa38  lbu a5,0(a0) ---- *)
    destruct (Nat.eq_dec len 0) as [ Hlen0 | Hlen0 ].
    { (* ---- the EMPTY string: [a0] is set to 0 and the loop is skipped -- *)
      iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_uk_lbu γt γd γs h4 m2 (mword_of_int 0xa38)
                (mword_of_int 0 : mword 12) a0_idx a5_idx dq
                (s + Z.of_nat len) ubyte0 nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha0_2 Hlen0;
                      rewrite (uint_moi s ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_shp_a38 with "Hcode"). }
      iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
      rewrite (ushp_pc_step 0xa38 4). iIntros (h5) "Hrun".
      set (m3 := <[Regidx a5_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                       : mword 64)]> m2).
      assert (Ha5_3 : m3 !!! Regidx a5_idx
                      = mword_of_int (bv_unsigned ubyte0)).
      { rewrite (upd_eq m2 (Regidx a5_idx)
                   (regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                     : mword 64))).
        exact (zext8_moi ubyte0). }
      assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                      m3 !!! Regidx q = m2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m2 (Regidx a5_idx) (Regidx q) _ Hq)).
      (* ---- 0xa3c  c.beqz a5,0xa58 -- TAKEN ---- *)
      assert (Htk : true = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (ushp_zext_nul ubyte0). symmetry.
        exact (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl). }
      iApply (wp_uk_cbeqz γt γd γs h5 m3 (mword_of_int 0xa3c)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0xa58) nn
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_a3c with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0xa58  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs h6 m3 (mword_of_int 0xa58)
                (mword_of_int 0 : mword 6) a0_idx nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_a58 with "Hcode"). }
      rewrite (ushp_pc_step 0xa58 2). iIntros (h7) "Hrun".
      set (m4 := <[Regidx a0_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)]> m3).
      (* ---- 0xa5a  c.j 0xa50 ---- *)
      iApply (wp_uk_cj γt γd γs h7 m4 (mword_of_int 0xa5a)
                (mword_of_int 2043 : mword 11) (mword_of_int 0xa50) nn
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_a5a with "Hcode"). }
      iIntros (h8) "Hrun".
      assert (Hsp4 : m4 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 2))).
      { rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
      iApply (wp_kshp_epi2 h8 m4 0xa50 0xa52 0xa54 0xa56 sp0 vra vs0 nn
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hal8 Hlo Hsp4
                with "[] [] [] [] Hw8 Hw0 Hrun").
      { iApply (uis_shp_a50 with "Hcode"). }
      { iApply (uis_shp_a52 with "Hcode"). }
      { iApply (uis_shp_a54 with "Hcode"). }
      { iApply (uis_shp_a56 with "Hcode"). }
      iIntros (h9 m') "%Hpres %Hspf %Hs0f Hrun".
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros q Hq.
        destruct (Z.eq_dec (uint q) 2) as [ Eq2 | Eq2 ].
        { rewrite (ushp_ridx_eq q csp_rs1
                     ltac:(rewrite Eq2; vm_compute; reflexivity)).
          exact Hspf. }
        destruct (Z.eq_dec (uint q) 8) as [ Eq8 | Eq8 ].
        { rewrite (ushp_ridx_eq q s0_idx
                     ltac:(rewrite Eq8; vm_compute; reflexivity)).
          exact Hs0f. }
        assert (Hqsp : Regidx q <> Regidx csp_rs1)
          by (apply ushp_ridx_ne;
              assert (Hc2 : uint csp_rs1 = 2) by (vm_compute; reflexivity);
              rewrite Hc2; exact Eq2).
        assert (Hqs0 : Regidx q <> Regidx s0_idx)
          by (apply ushp_ridx_ne;
              assert (Hc8 : uint s0_idx = 8) by (vm_compute; reflexivity);
              rewrite Hc8; exact Eq8).
        assert (Hqra : Regidx q <> Regidx ra_idx)
          by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
        rewrite (Hpres q Hqra Hqs0 Hqsp).
        rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx q) _
                       (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
        rewrite (Hm3 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
        exact (Hm12 q Hqsp Hqs0).
      - iPureIntro.
        rewrite (Hpres a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /m4 (upd_eq m3 (Regidx a0_idx)
                       (regval_into_reg
                          (sign_extend' 64 (mword_of_int 0 : mword 6)
                           : mword 64))).
        rewrite Hlen0. apply bv_eq. vm_compute. reflexivity. }
    (* ---- a NON-EMPTY string: byte 0 is [f 0] and the loop is entered ---- *)
    assert (H0len : (0 < len)%nat) by lia.
    iDestruct (ustr_byte γd dq s len f 0%nat H0len with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs h4 m2 (mword_of_int 0xa38)
              (mword_of_int 0 : mword 12) a0_idx a5_idx dq
              (s + Z.of_nat 0) (f 0%nat) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_2;
                    replace (s + Z.of_nat 0) with s by lia;
                    rewrite (uint_moi s ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_a38 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0xa38 4). iIntros (h5) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 ((f 0%nat) : mword 8)
                                     : mword 64)]> m2).
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int (bv_unsigned (f 0%nat))).
    { rewrite (upd_eq m2 (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 ((f 0%nat) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f 0%nat)). }
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int s)
      by (rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_2).
    assert (Hsp3 : m3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp2).
    (* ---- 0xa3c  c.beqz a5,0xa58 -- NOT taken ---- *)
    assert (Htk : false = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
    { rewrite Ha5_3 (ushp_zext_nul (f 0%nat)). symmetry.
      exact (bool_decide_eq_false_2 (f 0%nat = ubyte0) (Hne 0%nat H0len)). }
    iApply (wp_uk_cbeqz γt γd γs h5 m3 (mword_of_int 0xa3c)
              (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3)
              a5_idx false (mword_of_int 0xa58) nn
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_a3c with "Hcode"). }
    rewrite (ushp_pc_step 0xa3c 2). iIntros (h6) "Hrun".
    (* ---- 0xa3e  addi a5,a0,1 ---- *)
    assert (E1' : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs h6 m3 (mword_of_int 0xa3e)
              (mword_of_int 1 : mword 12) a0_idx a5_idx
              (mword_of_int (s + Z.of_nat 0%nat + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_3 E1' moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_a3e with "Hcode"). }
    rewrite (ushp_pc_step 0xa3e 4). iIntros (h7) "Hrun".
    set (m4 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (s + Z.of_nat 0%nat + 1)
                                     : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_4 : m4 !!! Regidx a5_idx
                    = mword_of_int (s + Z.of_nat 0%nat + 1))
      by exact (upd_eq m3 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + Z.of_nat 0%nat + 1)
                                    : mword 64))).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int s)
      by (rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_3).
    assert (Hsp4 : m4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp3).
    (* ---- 0xa42..0xa4a, the scan ---- *)
    iApply (wp_kshp_strlen_loop dq s len f nn (len - 0)%nat 0%nat h7 m4
              eq_refl H0len Hs0 Hs64 Ha5_4 with "Hcode Hstr Hrun").
    iIntros "Hstr" (h8 mc') "%Hpres %Ha3 Hrun".
    assert (Ha0_c : mc' !!! Regidx a0_idx = mword_of_int s)
      by (rewrite (Hpres a0_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha0_4).
    assert (Hsp_c : mc' !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hpres csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp4).
    (* ---- 0xa4c  subw a0,a3,a0 -- the count, as a 32-bit difference ---- *)
    iApply (wp_uk_subw γt γd γs h8 mc' (mword_of_int 0xa4c)
              a3_idx a0_idx a0_idx (mword_of_int (Z.of_nat len)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha3 Ha0_c;
                    rewrite (moi_subw (s + Z.of_nat len) s
                               ltac:(unfold Z31 in *; lia));
                    f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_a4c with "Hcode"). }
    rewrite (ushp_pc_step 0xa4c 4). iIntros (h9) "Hrun".
    set (m5 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (Z.of_nat len)
                                     : mword 64)]> mc').
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m5 !!! Regidx q = mc' !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc' (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hsp5 : m5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp_c).
    iApply (wp_kshp_epi2 h9 m5 0xa50 0xa52 0xa54 0xa56 sp0 vra vs0 nn
              ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
              Hal8 Hlo Hsp5
              with "[] [] [] [] Hw8 Hw0 Hrun").
    { iApply (uis_shp_a50 with "Hcode"). }
    { iApply (uis_shp_a52 with "Hcode"). }
    { iApply (uis_shp_a54 with "Hcode"). }
    { iApply (uis_shp_a56 with "Hcode"). }
    iIntros (h10 m') "%Hpres2 %Hspf %Hs0f Hrun".
    iApply ("Hcont" with "Hstr [] [] Hrun").
    - iPureIntro. intros q Hq.
      destruct (Z.eq_dec (uint q) 2) as [ Eq2 | Eq2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite Eq2; vm_compute; reflexivity)).
        exact Hspf. }
      destruct (Z.eq_dec (uint q) 8) as [ Eq8 | Eq8 ].
      { rewrite (ushp_ridx_eq q s0_idx
                   ltac:(rewrite Eq8; vm_compute; reflexivity)).
        exact Hs0f. }
      assert (Hqsp : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
            assert (Hc2 : uint csp_rs1 = 2) by (vm_compute; reflexivity);
            rewrite Hc2; exact Eq2).
      assert (Hqs0 : Regidx q <> Regidx s0_idx)
        by (apply ushp_ridx_ne;
            assert (Hc8 : uint s0_idx = 8) by (vm_compute; reflexivity);
            rewrite Hc8; exact Eq8).
      assert (Hqra : Regidx q <> Regidx ra_idx)
        by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
      rewrite (Hpres2 q Hqra Hqs0 Hqsp).
      rewrite (Hm5 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hpres q (ushp_cs_ne q a3_idx Hq ltac:(vm_compute; reflexivity))
                 (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity))
                 (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm4 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm3 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
      exact (Hm12 q Hqsp Hqs0).
    - iPureIntro.
      rewrite (Hpres2 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mc' (Regidx a0_idx)
               (regval_into_reg (mword_of_int (Z.of_nat len) : mword 64))).
  Qed.

  (* ===================================================================== *)
  (* §4b THE FRAME, GENERALISED OVER ITS SIZE AND ITS SPILL LIST.           *)
  (*                                                                       *)
  (* [wp_kshp_pro2] / [wp_kshp_epi2] above are the two-word frame written   *)
  (* out once.  Every other function in this catalog has the SAME frame     *)
  (* code at a different size [k] and with a different number [j] of        *)
  (* callee-saved spills:                                                   *)
  (*                                                                       *)
  (*   c.addi / c.addi16sp  sp,sp,-8k                                       *)
  (*   c.sdsp r0,8(k-1)(sp) ; ... ; c.sdsp r(j-1),8(k-j)(sp)                *)
  (*   c.addi4spn s0,sp,8k                                                  *)
  (*     ... the body ...                                                   *)
  (*   c.ldsp r0,8(k-1)(sp) ; ... ; c.ldsp r(j-1),8(k-j)(sp)                *)
  (*   c.addi / c.addi16sp  sp,sp,8k  ;  c.jr ra                            *)
  (*                                                                       *)
  (* execcmd and nulterminate are k=4 j=3, peek k=8 j=7, gettoken k=8 j=8,  *)
  (* parseline and parsepipe k=6 j=6, parsecmd k=8 j=5, parseredirs k=14    *)
  (* j=11.  So the economy is a lemma over the LIST of spills, and the two  *)
  (* below are that: the SPILL run and the RESTORE run, by induction on a   *)
  (* list of (register, c.sdsp immediate) PAIRS.  The immediates are the    *)
  (* caller's own catalog spelling, so no call site ever has to argue that  *)
  (* [mword_of_int (Z.of_nat (k - 1 - i))] is the word the decoder made.    *)
  (*                                                                       *)
  (* THERE IS NO INDEX ARITHMETIC INSIDE EITHER INDUCTION.  The pcs and the *)
  (* slot addresses are FUNCTIONS [pcs] / [ad] of the spill index, and the  *)
  (* step hands the tail [fun i => pcs (S i)] / [fun i => ad (S i)] -- a    *)
  (* beta-reduction, not a [lia].  What a call site owes instead is one     *)
  (* pure fact per instruction, at concrete numbers, which is exactly the   *)
  (* [vm_compute] stage 2 was paying per step anyway.                       *)
  (*                                                                       *)
  (* THE PUSH AND THE POP ARE NOT IN HERE, deliberately: they are           *)
  (* [wp_uk_caddi_sp_dn] or [wp_uk_caddi16sp_dn] (gcc picks by size, and    *)
  (* picks INCONSISTENTLY -- execcmd pushes with [c.addi] and pops with     *)
  (* [c.addi16sp]), each one [iApply] at the call site, and folding them in *)
  (* would need a two-armed premise for no saving.                          *)
  (* ===================================================================== *)

  (* the same [∗ list] over a list and over [seq 0 (length l)] -- the shape *)
  (* [ustack_body] hands a frame out in, and the shape the two runs below   *)
  (* consume it in *)
  Local Lemma ushp_sepL_seq {A : Type} (l : list A) (Φ : nat -> iProp Σ) :
    ([∗ list] i ∈ seq 0 (length l), Φ i) ⊣⊢ ([∗ list] i ↦ _ ∈ l, Φ i).
  Proof.
    revert Φ. induction l as [| x l IH ]; intros Φ; [ reflexivity | ].
    cbn [length seq]. rewrite !big_sepL_cons.
    rewrite <- (seq_shift (length l) 0), big_sepL_fmap.
    rewrite (IH (fun i => Φ (S i))). reflexivity.
  Qed.

  (* a slot of an 8-aligned frame is itself 8-aligned *)
  Local Lemma ushp_slot_al (sp : Z) (i : nat) :
    sp mod 8 = 0 -> (sp - 8 * (Z.of_nat i + 1)) mod 8 = 0.
  Proof.
    intro H. rewrite Zminus_mod H.
    assert (E : (8 * (Z.of_nat i + 1)) mod 8 = 0)
      by (rewrite Z.mul_comm; apply Z_mod_mult).
    rewrite E. reflexivity.
  Qed.

  (* THE FRESH FRAME, SPLIT: the top [length rs] words are the spill slots  *)
  (* the runs below address, the rest are the function's locals. *)
  Local Lemma ushp_frame_split (sp0 sp1 : mword 64) (n : nat)
      (rs : list (mword 5 * mword 6)) :
    uint sp1 = uint sp0 - 8 * Z.of_nat (length rs) ->
    ustack γd sp0 (length rs + n) -∗
      ([∗ list] i ↦ _ ∈ rs,
         ∃ w : mword 64, uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) w) ∗
      ustack γd sp1 n.
  Proof.
    intros Hsp1. rewrite (ustack_app γd sp0 sp1 (length rs) n Hsp1).
    rewrite /ustack /ustack_body.
    rewrite (ushp_sepL_seq rs
      (fun i => ∃ w : mword 64, uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) w)%I).
    iIntros "[[_ $] $]".
  Qed.

  (* ...and put back together, which is what the pop consumes *)
  Local Lemma ushp_frame_join (sp0 sp1 : mword 64) (n : nat)
      (rs : list (mword 5 * mword 6)) (vals : nat -> mword 64) :
    uint sp1 = uint sp0 - 8 * Z.of_nat (length rs) ->
    ([∗ list] i ↦ _ ∈ rs,
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd sp1 n -∗
    ustack γd sp0 (length rs + n).
  Proof.
    intros Hsp1. rewrite (ustack_app γd sp0 sp1 (length rs) n Hsp1).
    rewrite /ustack /ustack_body.
    rewrite (ushp_sepL_seq rs
      (fun i => ∃ w : mword 64, uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) w)%I).
    iIntros "Hs [%Hal Hr]".
    iSplitR "Hr".
    - iSplit.
      + iPureIntro.
        assert (E : uint sp0 = uint sp1 + 8 * Z.of_nat (length rs)) by lia.
        assert (H8 : (8 * Z.of_nat (length rs)) mod 8 = 0)
          by (rewrite Z.mul_comm; apply Z_mod_mult).
        rewrite E Zplus_mod Hal H8. reflexivity.
      + iApply (big_sepL_mono with "Hs"). intros i x _.
        iIntros "H". iExists (vals i). iExact "H".
    - iSplit; [ iPureIntro; exact Hal | iExact "Hr" ].
  Qed.

  (* THE SPILL RUN.  [c.sdsp] writes no register, so [m] is the SAME at     *)
  (* every step -- which is why this induction carries nothing but the pc.  *)
  Local Lemma wp_kshp_spill (spn : mword 64) (nn : nat) :
    forall (rs : list (mword 5 * mword 6)) (pcs ad : nat -> Z)
           (vals : nat -> mword 64) (h : CpuId) (m : regfile),
    m !!! Regidx csp_rs1 = spn ->
    (forall i : nat, (i < length rs)%nat -> pcs (S i) = pcs i + 2) ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! i = Some (r, u) ->
       ad i = uint spn + uoff_sdsp u /\ ad i mod 8 = 0 /\
       vals i = m !!! Regidx r) ->
    ([∗ list] i ↦ ru ∈ rs,
       uinstr_is γt (mword_of_int (pcs i)) true
         (C_SDSP (snd ru, Regidx (fst ru)))) -∗
    ([∗ list] i ↦ _ ∈ rs, ∃ w : mword 64, uword γd (ad i) w) -∗
    urun γt γd γs h m (mword_of_int (pcs 0%nat)) nn -∗
    (([∗ list] i ↦ _ ∈ rs, uword γd (ad i) (vals i)) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (mword_of_int (pcs (length rs))) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    induction rs as [| ru rs IH ];
      intros pcs ad vals h m Hsp Hpc Hoff; iIntros "#Hi Hw Hrun Hcont".
    - iSpecialize ("Hcont" with "Hw"). cbn [length].
      iApply ("Hcont" $! h with "Hrun").
    - rewrite !big_sepL_cons.
      iDestruct "Hi" as "[#Hi0 #Hir]".
      iDestruct "Hw" as "[[%w0 Hw0] Hwr]".
      destruct (Hoff 0%nat (fst ru) (snd ru)
                  ltac:(destruct ru; reflexivity)) as [ Had0 [ Hal0 Hv0 ] ].
      iApply (wp_uk_csdsp γt γd γs h m (mword_of_int (pcs 0%nat))
                (snd ru) (fst ru) (ad 0%nat) w0 nn
                ltac:(rewrite Hsp; exact Had0) Hal0
                with "Hi0 Hw0 Hrun").
      iIntros "Hw0". rewrite <- Hv0.
      rewrite (ushp_pc_step (pcs 0%nat) 2).
      rewrite <- (Hpc 0%nat ltac:(cbn [length]; lia)).
      iIntros (h1) "Hrun".
      iApply (IH (fun i => pcs (S i)) (fun i => ad (S i))
                (fun i => vals (S i)) h1 m Hsp
                ltac:(intros i Hi; exact (Hpc (S i) ltac:(cbn [length]; lia)))
                ltac:(intros i r u Hi; exact (Hoff (S i) r u Hi))
                with "Hir Hwr Hrun").
      iIntros "Hwr" (h2) "Hrun".
      (* the [rewrite !big_sepL_cons] above already split [Hcont]'s premise *)
      iApply ("Hcont" with "[Hw0 Hwr]"); [ | iApply "Hrun" ].
      iFrame "Hw0 Hwr".
  Qed.

  (* the register file a RESTORE run leaves behind: the spills written back *)
  (* in order, so a later one overrides an earlier one.  At a concrete list *)
  (* this [cbn]s into the insert tower a call site already reads with       *)
  (* [upd_eq] / [upd_ne], which is why no no-duplicates premise is needed.  *)
  Fixpoint ushp_spillback (rs : list (mword 5 * mword 6))
      (vals : nat -> mword 64) (me : regfile) : regfile :=
    match rs with
    | [] => me
    | ru :: rs' =>
        ushp_spillback rs' (fun i => vals (S i))
          (<[Regidx (fst ru) := regval_into_reg (vals 0%nat)]> me)
    end.

  Lemma ushp_spillback_ne (rs : list (mword 5 * mword 6))
      (vals : nat -> mword 64) (me : regfile) (q : mword 5) :
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! i = Some (r, u) -> Regidx q <> Regidx r) ->
    ushp_spillback rs vals me !!! Regidx q = me !!! Regidx q.
  Proof.
    revert vals me. induction rs as [| ru rs IH ]; intros vals me Hne;
      [ reflexivity | ].
    cbn [ushp_spillback].
    rewrite (IH (fun i => vals (S i))
               (<[Regidx (fst ru) := regval_into_reg (vals 0%nat)]> me)
               ltac:(intros i r u Hi; exact (Hne (S i) r u Hi))).
    apply (upd_ne me (Regidx (fst ru)) (Regidx q)).
    exact (Hne 0%nat (fst ru) (snd ru) ltac:(destruct ru; reflexivity)).
  Qed.

  (* THE RESTORE RUN.  Each [c.ldsp] DOES write a register, so the register *)
  (* file the continuation gets is [ushp_spillback] of the list.            *)
  Local Lemma wp_kshp_restore (spn : mword 64) (nn : nat) :
    forall (rs : list (mword 5 * mword 6)) (pcs ad : nat -> Z)
           (vals : nat -> mword 64) (h : CpuId) (m : regfile),
    m !!! Regidx csp_rs1 = spn ->
    (forall i : nat, (i < length rs)%nat -> pcs (S i) = pcs i + 2) ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! i = Some (r, u) ->
       ad i = uint spn + uoff_sdsp u /\ ad i mod 8 = 0 /\
       unot_sp r /\ uint r <> 0) ->
    ([∗ list] i ↦ ru ∈ rs,
       uinstr_is γt (mword_of_int (pcs i)) true
         (C_LDSP (snd ru, Regidx (fst ru)))) -∗
    ([∗ list] i ↦ _ ∈ rs, uword γd (ad i) (vals i)) -∗
    urun γt γd γs h m (mword_of_int (pcs 0%nat)) nn -∗
    (([∗ list] i ↦ _ ∈ rs, uword γd (ad i) (vals i)) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' (ushp_spillback rs vals m)
           (mword_of_int (pcs (length rs))) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    induction rs as [| ru rs IH ];
      intros pcs ad vals h m Hsp Hpc Hoff; iIntros "#Hi Hw Hrun Hcont".
    - iSpecialize ("Hcont" with "Hw"). cbn [length ushp_spillback].
      iApply ("Hcont" $! h with "Hrun").
    - rewrite !big_sepL_cons.
      iDestruct "Hi" as "[#Hi0 #Hir]".
      iDestruct "Hw" as "[Hw0 Hwr]".
      destruct (Hoff 0%nat (fst ru) (snd ru)
                  ltac:(destruct ru; reflexivity))
        as [ Had0 [ Hal0 [ Hnsp0 Hnz0 ] ] ].
      iApply (wp_uk_cldsp γt γd γs h m (mword_of_int (pcs 0%nat))
                (snd ru) (fst ru) (ad 0%nat) (vals 0%nat) nn
                Hnsp0 ltac:(rewrite Hsp; exact Had0) Hal0 Hnz0
                with "Hi0 Hw0 Hrun").
      iIntros "Hw0".
      rewrite (ushp_pc_step (pcs 0%nat) 2).
      rewrite <- (Hpc 0%nat ltac:(cbn [length]; lia)).
      iIntros (h1) "Hrun".
      assert (Hsp1 : (<[Regidx (fst ru) := regval_into_reg (vals 0%nat)]> m)
                       !!! Regidx csp_rs1 = spn).
      { rewrite (upd_ne m (Regidx (fst ru)) (Regidx csp_rs1)
                   (regval_into_reg (vals 0%nat)) Hnsp0). exact Hsp. }
      cbn [ushp_spillback].
      iApply (IH (fun i => pcs (S i)) (fun i => ad (S i))
                (fun i => vals (S i)) h1
                (<[Regidx (fst ru) := regval_into_reg (vals 0%nat)]> m)
                Hsp1
                ltac:(intros i Hi; exact (Hpc (S i) ltac:(cbn [length]; lia)))
                ltac:(intros i r u Hi; exact (Hoff (S i) r u Hi))
                with "Hir Hwr Hrun").
      iIntros "Hwr" (h2) "Hrun".
      iApply ("Hcont" with "[Hw0 Hwr]"); [ | iApply "Hrun" ].
      iFrame "Hw0 Hwr".
  Qed.

  (* ===================================================================== *)
  (* §5 THE TREE PREDICATE -- the deliverable interface for stages 5-6.     *)
  (*                                                                       *)
  (* -- a well-formed cmd tree for this token list sits at this address   *)
  (* in the heap.  On the first-generation tier this was a [Prop] over a    *)
  (* [gmap] ([USpecShParse.sh_execcmd_argv] plus [USpecSh.sh_exec_below]);  *)
  (* on urun a node's bytes are OWNED, so it is an [iProp] -- which is also *)
  (* what makes it usable as a loop invariant, since [parseexec]'s argument *)
  (* loop hands the node round its cycle.                                   *)
  (*                                                                       *)
  (* THE SHAPE IS SH'S OWN STRUCT LAYOUT, not an abstraction of it:         *)
  (*                                                                       *)
  (*   struct execcmd { int type; char *argv[10]; char *eargv[10]; }        *)
  (*      type @ 0, argv @ 8..88, eargv @ 88..168                           *)
  (*   struct redircmd { int type; struct cmd *cmd; char *file, *efile;     *)
  (*                     int mode, fd; }   @ 0, 8, 16, 24, 32, 36           *)
  (*   struct pipecmd / listcmd { int type; struct cmd *left, *right; }     *)
  (*      @ 0, 8, 16                                                        *)
  (*   struct backcmd { int type; struct cmd *cmd; }   @ 0, 8               *)
  (*                                                                       *)
  (* A TOKEN IS A PAIR OF INDEXES INTO THE LINE, not a string: that is      *)
  (* exactly what the parser records, and it is [nulterminate] -- not       *)
  (* [parseexec] -- that turns the pair into a C string by storing a NUL at *)
  (* the end index.  Keeping the predicate at indexes is what lets the same *)
  (* predicate state both sides of that step.                               *)
  (*                                                                       *)
  (* Only the EXEC arm is reachable under [ushp_no_symbols], so only that   *)
  (* arm is EXERCISED by stage 4; the other four are stated because stage 5 *)
  (* walks [runcmd]'s five-way jump table and needs the vocabulary.  The    *)
  (* sibling stage-5 lane states its own copy; stage 6 reconciles.          *)
  (* ===================================================================== *)

  Inductive ushp_cmd : Type :=
  | UshpExec  (toks : list (nat * nat))
  | UshpRedir (c : ushp_cmd) (q eq : nat) (mode fd : Z)
  | UshpPipe  (l r : ushp_cmd)
  | UshpList  (l r : ushp_cmd)
  | UshpBack  (c : ushp_cmd).

  (* the type word each arm stores: EXEC 1, REDIR 2, PIPE 3, LIST 4,
     BACK 5 -- sh.c's #defines, and the index [nulterminate]'s jump table
     at 0x13b0 is keyed by *)
  Definition ushp_ty (t : ushp_cmd) : Z :=
    match t with
    | UshpExec _ => 1 | UshpRedir _ _ _ _ _ => 2 | UshpPipe _ _ => 3
    | UshpList _ _ => 4 | UshpBack _ => 5
    end.

  (* the type field, its four bytes of padding, and a plain 8-byte cell *)
  Definition ushp_type_at (p : Z) (t : ushp_cmd) : iProp Σ :=
    (ubytes γd p 4 (nth_byte (mword_of_int (ushp_ty t) : mword 32)) ∗
     (∃ g : nat -> bv 8, ubytes γd (p + 4) 4 g))%I.

  (* one argv/eargv slot: a token boundary while [i] indexes a token, the
     NULL cap at [i = |toks|], and an unconstrained cell above that -- which
     is the honest reading, because [parseexec] writes only up to the cap
     and [memset] put whatever it put in the rest. *)
  Definition ushp_slot (s0 base : Z) (toks : list (nat * nat))
      (sel : nat * nat -> nat) (i : nat) : iProp Σ :=
    match toks !! i with
    | Some tk =>
        uword γd (base + 8 * Z.of_nat i)
          (mword_of_int (s0 + Z.of_nat (sel tk)))
    | None =>
        if bool_decide (i = length toks)
        then uword γd (base + 8 * Z.of_nat i) (mword_of_int 0)
        else (∃ w : mword 64, uword γd (base + 8 * Z.of_nat i) w)%I
    end.

  (* MAXARGS = 10, and the cap has to fit, so a parse of ten tokens would
     overflow the node -- which is exactly the [panic("too many args")]
     arm parseexec guards with, and why the bound is [< 10] here too. *)
  Definition ushp_exec_at (s0 p : Z) (toks : list (nat * nat)) : iProp Σ :=
    (⌜ (length toks < 10)%nat ⌝ ∗ ⌜ 0 < p ⌝ ∗ ⌜ p mod 8 = 0 ⌝ ∗
     ushp_type_at p (UshpExec toks) ∗
     ([∗ list] i ∈ seq 0 10, ushp_slot s0 (p + 8) toks fst i) ∗
     ([∗ list] i ∈ seq 0 10, ushp_slot s0 (p + 88) toks snd i))%I.

  Fixpoint ushp_tree (s0 p : Z) (t : ushp_cmd) : iProp Σ :=
    match t with
    | UshpExec toks => ushp_exec_at s0 p toks
    | UshpRedir c q eq mode fd =>
        (⌜ 0 < p ⌝ ∗ ⌜ p mod 8 = 0 ⌝ ∗
         ushp_type_at p t ∗
         (∃ pc : Z, uword γd (p + 8) (mword_of_int pc) ∗ ushp_tree s0 pc c) ∗
         uword γd (p + 16) (mword_of_int (s0 + Z.of_nat q)) ∗
         uword γd (p + 24) (mword_of_int (s0 + Z.of_nat eq)) ∗
         ubytes γd (p + 32) 4 (nth_byte (mword_of_int mode : mword 32)) ∗
         ubytes γd (p + 36) 4 (nth_byte (mword_of_int fd : mword 32)))%I
    | UshpPipe l r =>
        (⌜ 0 < p ⌝ ∗ ⌜ p mod 8 = 0 ⌝ ∗
         ushp_type_at p t ∗
         (∃ pl : Z, uword γd (p + 8) (mword_of_int pl) ∗ ushp_tree s0 pl l) ∗
         (∃ pr : Z, uword γd (p + 16) (mword_of_int pr) ∗ ushp_tree s0 pr r))%I
    | UshpList l r =>
        (⌜ 0 < p ⌝ ∗ ⌜ p mod 8 = 0 ⌝ ∗
         ushp_type_at p t ∗
         (∃ pl : Z, uword γd (p + 8) (mword_of_int pl) ∗ ushp_tree s0 pl l) ∗
         (∃ pr : Z, uword γd (p + 16) (mword_of_int pr) ∗ ushp_tree s0 pr r))%I
    | UshpBack c =>
        (⌜ 0 < p ⌝ ∗ ⌜ p mod 8 = 0 ⌝ ∗
         ushp_type_at p t ∗
         (∃ pc : Z, uword γd (p + 8) (mword_of_int pc) ∗ ushp_tree s0 pc c))%I
    end.

  (* THE PARSE RELATION, at the shape stage 6's theorem needs: on a line
     with no symbol byte, the tree [parsecmd] returns is the EXEC node whose
     argv are the line's tokens.  It is a definition, not an assumption --
     the theorem that the code establishes it is what the remaining walks
     owe, and nothing here claims it. *)
  Definition ushp_parses (s0 : Z) (len : nat) (f : nat -> bv 8)
      (p : Z) (t : ushp_cmd) : Prop :=
    exists toks : list (nat * nat),
      ushp_tokens len f 0%nat toks /\ (length toks < 10)%nat /\
      t = UshpExec toks.

  (* the tree predicate's one structural fact, and the only one the walks
     need before the node is filled: an EXEC node pins its own address *)
  Lemma ushp_exec_at_addr (s0 p : Z) (toks : list (nat * nat)) :
    ushp_exec_at s0 p toks -∗ ⌜ 0 < p /\ p mod 8 = 0 ⌝.
  Proof.
    rewrite /ushp_exec_at. iIntros "(_ & %Hp & %Hal & _)".
    iPureIntro. exact (conj Hp Hal).
  Qed.

  (* ---- turning a MEMSET'D RUN into a node ------------------------------ *)
  (* [execcmd] hands [ushp_exec_at] its 168 bytes as one zeroed run, and    *)
  (* every conjunct of the predicate is a slice of it.  These four lemmas   *)
  (* are the cutting.                                                      *)

  (* the byte run, pointwise -- the honest form of a funext the run's       *)
  (* content function does not deserve *)
  Local Lemma ushp_ubytes_ext (a : Z) (n : nat) (f g : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> f j = g j) ->
    ubytes γd a n f -∗ ubytes γd a n g.
  Proof.
    intros Hfg. rewrite /ubytes /ubytesq. iIntros "H".
    iApply (big_sepL_mono with "H"). intros i j Hj.
    apply lookup_seq in Hj as [ -> Hlt ]. rewrite Nat.add_0_l.
    rewrite (Hfg i Hlt). done.
  Qed.

  (* the split of a run at a NAMED address, so a caller never carries an
     [a + Z.of_nat k] it then has to normalise *)
  Local Lemma ushp_peel (a b : Z) (k n : nat) (f : nat -> bv 8) :
    b = a + Z.of_nat k ->
    ubytes γd a (k + n) f -∗
      ubytes γd a k f ∗ ubytes γd b n (fun j => f (k + j)%nat).
  Proof.
    intros Hb. rewrite (ubytes_app γd a k n f) Hb. iIntros "$".
  Qed.

  (* ...and the same at the ZEROED run [memset] hands back, where keeping
     the content function literally constant is what lets a call site name
     it in the next lemma's arguments *)
  Local Lemma ushp_peel0 (a b : Z) (k n : nat) :
    b = a + Z.of_nat k ->
    ubytes γd a (k + n) (fun _ : nat => ubyte0) -∗
      ubytes γd a k (fun _ : nat => ubyte0) ∗
      ubytes γd b n (fun _ : nat => ubyte0).
  Proof.
    intros Hb. rewrite (ubytes_app γd a k n (fun _ : nat => ubyte0)) Hb.
    iIntros "$".
  Qed.

  Local Lemma ushp_nth_byte_zero (j : nat) :
    (j < 8)%nat -> nth_byte (mword_of_int 0 : mword 64) j = ubyte0.
  Proof.
    intro Hj. destruct j as [| [| [| [| [| [| [| [| j ]]]]]]]];
      try (vm_compute; reflexivity). lia.
  Qed.

  (* the ten argv (or eargv) slots of a FRESH node.  memset zeroed all
     eighty bytes, so slot 0 is exactly the NULL cap [ushp_slot] asks for at
     [|toks| = 0] and the nine above it are its unconstrained cells. *)
  Local Lemma ushp_slots_nil (t0 base : Z) (sel : nat * nat -> nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < 8)%nat -> f j = ubyte0) ->
    ubytes γd base 80 f -∗
    [∗ list] i ∈ seq 0 10, ushp_slot t0 base [] sel i.
  Proof.
    intros Hf. iIntros "Hb".
    iDestruct (ushp_peel base (base + 8) 8 72 _ ltac:(lia) with "Hb")
      as "[H0 Hb]".
    iDestruct (ushp_peel (base + 8) (base + 16) 8 64 _ ltac:(lia) with "Hb")
      as "[H1 Hb]".
    iDestruct (ushp_peel (base + 16) (base + 24) 8 56 _ ltac:(lia) with "Hb")
      as "[H2 Hb]".
    iDestruct (ushp_peel (base + 24) (base + 32) 8 48 _ ltac:(lia) with "Hb")
      as "[H3 Hb]".
    iDestruct (ushp_peel (base + 32) (base + 40) 8 40 _ ltac:(lia) with "Hb")
      as "[H4 Hb]".
    iDestruct (ushp_peel (base + 40) (base + 48) 8 32 _ ltac:(lia) with "Hb")
      as "[H5 Hb]".
    iDestruct (ushp_peel (base + 48) (base + 56) 8 24 _ ltac:(lia) with "Hb")
      as "[H6 Hb]".
    iDestruct (ushp_peel (base + 56) (base + 64) 8 16 _ ltac:(lia) with "Hb")
      as "[H7 Hb]".
    iDestruct (ushp_peel (base + 64) (base + 72) 8 8 _ ltac:(lia) with "Hb")
      as "[H8 H9]".
    rewrite /ushp_slot /=.
    assert (A0 : base + 8 * Z.of_nat 0 = base) by lia.
    assert (A1 : base + 8 * Z.of_nat 1 = base + 8) by lia.
    assert (A2 : base + 8 * Z.of_nat 2 = base + 16) by lia.
    assert (A3 : base + 8 * Z.of_nat 3 = base + 24) by lia.
    assert (A4 : base + 8 * Z.of_nat 4 = base + 32) by lia.
    assert (A5 : base + 8 * Z.of_nat 5 = base + 40) by lia.
    assert (A6 : base + 8 * Z.of_nat 6 = base + 48) by lia.
    assert (A7 : base + 8 * Z.of_nat 7 = base + 56) by lia.
    assert (A8 : base + 8 * Z.of_nat 8 = base + 64) by lia.
    assert (A9 : base + 8 * Z.of_nat 9 = base + 72) by lia.
    rewrite A0 A1 A2 A3 A4 A5 A6 A7 A8 A9.
    iSplitL "H0".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext base 8 f
                (nth_byte (mword_of_int 0 : mword 64)) with "H0").
      intros j Hj. rewrite (Hf j Hj) (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H1"; [ iApply (uword_of_ubytes with "H1") | ].
    iSplitL "H2"; [ iApply (uword_of_ubytes with "H2") | ].
    iSplitL "H3"; [ iApply (uword_of_ubytes with "H3") | ].
    iSplitL "H4"; [ iApply (uword_of_ubytes with "H4") | ].
    iSplitL "H5"; [ iApply (uword_of_ubytes with "H5") | ].
    iSplitL "H6"; [ iApply (uword_of_ubytes with "H6") | ].
    iSplitL "H7"; [ iApply (uword_of_ubytes with "H7") | ].
    iSplitL "H8"; [ iApply (uword_of_ubytes with "H8") | ].
    iSplitL "H9"; [ iApply (uword_of_ubytes with "H9") | done ].
  Qed.

  (* ===================================================================== *)
  (* §6 THE ONE HYPOTHESIS OF STAGE 4: MALLOC.                              *)
  (*                                                                       *)
  (* All five cmd constructors begin [cmd = malloc(sizeof( *cmd))], and     *)
  (* malloc (0x118c, 91 instructions) -> morecore -> sbrk (0xc52) ->        *)
  (* sys_sbrk (0xd0e) is STAGE 3, which is blocked on the second unbuilt    *)
  (* consumer leaf, [wp_uk_ecall_sbrk] -- and that one moves [pi] and [sz], *)
  (* so it is strictly harder than the window row stage 2 needed.           *)
  (*                                                                       *)
  (* So malloc's contract is stated HERE, once, as a named local            *)
  (* Hypothesis, at the idiom of the landed function contracts in UkSh.v    *)
  (* ([wp_ksh_memset]'s binder order, [ucallee_saved] read-back, [ret_pc]   *)
  (* return) so that stage 3's discharge is [intros] + [exact] or a thin    *)
  (* adapter.  IT CONSUMES THE RUN AT MALLOC'S ENTRY PC AND HANDS IT BACK   *)
  (* AT THE RETURN ADDRESS, so no instruction of the allocator is ever      *)
  (* fetched by this walk and none is in tools/ucode_shp.txt.               *)
  (*                                                                       *)
  (* THE STACK BUDGET IS THE CALL CHAIN SPELLED OUT, as the durable notes   *)
  (* require: malloc's own frame is 64 bytes (8 words) and the deepest       *)
  (* thing it calls is [free] or [sbrk], 16 bytes (2 words) each, so it is  *)
  (* [10 + avail] -- not a round number.                                    *)
  (*                                                                       *)
  (* WHAT IT DOES NOT SAY, and why that is honest rather than convenient:   *)
  (* THERE IS NO FAILURE ARM.  sh's constructors do not test malloc's       *)
  (* result -- [execcmd] goes straight into [memset(cmd, 0, 168)] -- so a   *)
  (* NULL return is a FAULT in sh, not a branch, and a contract with a NULL *)
  (* arm would be unusable by the very code it is for.  The first           *)
  (* generation drew the line in the same place and named it: its           *)
  (* [wp_sh_malloc_first_body] is FIRST-CALL-ONLY ([freep == 0], so the     *)
  (* [morecore] path), which is the only call sh's parse of one line makes. *)
  (*                                                                       *)
  (* WHAT IT TAINTS, TODAY: exactly one lemma, [wp_kshp_execcmd] in §7,     *)
  (* which is the only caller of a constructor this file has.  Everything   *)
  (* else -- the pure vocabulary, the frame runs of §4b, [wp_kshp_strchr],  *)
  (* [wp_kshp_strlen], the tree algebra -- is UNCONDITIONAL, and            *)
  (* [Print Assumptions] on any of them is the standing three or *closed    *)
  (* under the global context*.  When [parseexec], [parsepipe],             *)
  (* [parseline] and [parsecmd] land they will carry it THROUGH §7, each    *)
  (* labelled in its own header the way stage 2 labelled its seven.         *)
  (* ===================================================================== *)
  Hypothesis ushp_malloc_ok :
    forall (h : CpuId) (m : regfile) (nbytes : Z) (avail : nat),
      m !!! Regidx a0_idx = mword_of_int nbytes ->
      0 < nbytes -> nbytes < Z31 ->
      shp_code γt -∗
      urun γt γd γs h m (mword_of_int ShSyms.malloc) (10 + avail) -∗
      (∀ (h' : CpuId) (m' : regfile) (p : Z) (g : nat -> bv 8),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         ⌜ 0 < p /\ p mod 16 = 0 /\ p + nbytes < 2 ^ 38 ⌝ -∗
         ubytes γd p (Z.to_nat nbytes) g -∗
         urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + avail) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).

  (* ===================================================================== *)
  (* §8 peek @0x448 -- 40 instructions, an EIGHT-word frame, one scan.      *)
  (*                                                                       *)
  (*   int peek(char **ps, char *es, char *toks) {                          *)
  (*     char *s = *ps;                                                     *)
  (*     while(s < es && strchr(whitespace, *s)) s++;                       *)
  (*     *ps = s;                                                           *)
  (*     return *s && strchr(toks, *s);  }                                  *)
  (*                                                                       *)
  (* THE PARSER'S ONE-TOKEN LOOKAHEAD: every one of parsecmd, parseline,    *)
  (* parsepipe, parseexec and parseredirs asks it whether the next          *)
  (* non-blank byte is in a given set, and it is what [ushp_no_symbols]     *)
  (* answers "no" to at four of those five sites.  It is also the only      *)
  (* function in the parser that MOVES THE LEXER'S CURSOR AS A SIDE         *)
  (* EFFECT -- [*ps = s] -- which is why the cursor cell is a [uword] in    *)
  (* the contract rather than a value.                                      *)
  (*                                                                       *)
  (* THE SCAN IS A BOUNDED ROCQ INDUCTION AND WHAT BOUNDS IT IS [es]:       *)
  (* [s2] holds the end pointer and the back edge tests against it, so the  *)
  (* scan reads only BODY bytes of the line and the terminator never enters *)
  (* it -- unlike strchr's loop, which is bounded by the NUL.  The measure  *)
  (* is [len - j] and the answer is [ushp_skipws], the ported spelling.     *)
  (* ===================================================================== *)

  (* peek's whitespace scan, 0x46e..0x47c:
       lbu a1,0(s1) ; c.mv a0,s3 ; jal strchr ; c.beqz a0,0x482 ;
       c.addi s1,s1,1 ; bne s2,s1,0x46e
     [j] is the index the scan has reached.  Only the CALLEE-SAVED half of
     the register file is promised across it, because every turn calls
     strchr and that is all strchr's contract gives; s1 is excluded because
     the scan is what moves it. *)
  Local Lemma wp_kshp_peek_scan (dq dw : dfrac) (s0 : Z) (len : nat)
      (f : nat -> bv 8) (nn : nat) :
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs h mc (mword_of_int 0x46e) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs h' mc' (mword_of_int 0x482) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3;
      iIntros "#Hcode Hstr Hws Hrun Hcont"; [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- 0x46e  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs h mc (mword_of_int 0x46e)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat j)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_46e with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x46e 4). iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                     : mword 64)]> mc).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                    m1 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc (Regidx a1_idx) (Regidx q) _ Hq)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (upd_eq mc (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f j)). }
    (* ---- 0x472  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs h1 m1 (mword_of_int 0x472) a0_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3;
                    symmetry; exact (ushp_mv_val ushp_whitespace))
              with "[] Hrun").
    { iApply (uis_shp_472 with "Hcode"). }
    rewrite (ushp_pc_step 0x472 2). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x474  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs h2 m2 (mword_of_int 0x474)
              (mword_of_int 1550 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x478) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_474 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x478 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int ushp_whitespace).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ushp_whitespace : mword 64))). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)). exact Ha1_1. }
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = mword_of_int 0x478).
    { rewrite (upd_eq m2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x478 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* the callee-saved half of [mc] survives all three writes *)
    assert (Hcs3 : forall q : mword 5, ucallee_saved_idx q = true ->
                     m3 !!! Regidx q = mc !!! Regidx q).
    { intros q Hq.
      rewrite (Hm3 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm2 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      exact (Hm1 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity))). }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h3 m3 dw ushp_whitespace 5 ushp_ws_f (f j) nn
              Ha0_3 Ha1_3 ltac:(unfold ushp_whitespace; lia)
              ltac:(unfold ushp_whitespace, Z64; lia)
              with "Hcode Hws Hrun").
    iIntros "Hws" (h4 m4) "%Hcs34 %Ha0_4 Hrun".
    rewrite Eret.
    assert (Hcs4 : forall q : mword 5, ucallee_saved_idx q = true ->
                     m4 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; rewrite (Hcs34 q Hq); exact (Hcs3 q Hq)).
    assert (Hs1_4 : m4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hcs4 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hs2_4 : m4 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hcs4 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_4 : m4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    (* ---- 0x478  c.beqz a0,0x482 -- the byte's membership decides ---- *)
    destruct (ushp_is_ws (f j)) eqn:Ews.
    2: { (* NOT whitespace: the scan stops here and [s1] never moved *)
      assert (Htk : true = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (ushp_ws_chr_z (f j) Ews).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz γt γd γs h4 m4 (mword_of_int 0x478)
                (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x482) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_478 with "Hcode"). }
      iIntros (h5) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q Hq _. exact (Hcs4 q Hq).
      - iPureIntro. rewrite Hs1_4.
        rewrite (ushp_skipws_stop (len - j) j f Ews). f_equal. lia. }
    (* WHITESPACE: the loop goes round *)
    destruct (ushp_ws_chr_nz (f j) Ews) as [ k [ Hk Hchr ] ].
    assert (Htk : false = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_4 Hchr.
      rewrite (moi_eq_zero (ushp_whitespace + Z.of_nat k)
                 ltac:(unfold ushp_whitespace, Z64; lia)).
      symmetry. apply Z.eqb_neq. unfold ushp_whitespace. lia. }
    iApply (wp_uk_cbeqz γt γd γs h4 m4 (mword_of_int 0x478)
              (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x482) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_478 with "Hcode"). }
    rewrite (ushp_pc_step 0x478 2). iIntros (h5) "Hrun".
    (* ---- 0x47a  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs h5 m4 (mword_of_int 0x47a)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S j))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_4 E1 moi_add;
                    replace (s0 + Z.of_nat (S j)) with (s0 + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_47a with "Hcode"). }
    rewrite (ushp_pc_step 0x47a 2). iIntros (h6) "Hrun".
    set (m5 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                     : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_5 : m5 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S j)))
      by exact (upd_eq m4 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                    : mword 64))).
    assert (Hs2_5 : m5 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_4).
    assert (Hs3_5 : m5 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hm5 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_4).
    (* ---- 0x47c  bne s2,s1,0x46e ---- *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* the scan ran to [es]: fall through to 0x480, which is a no-op *)
      assert (Htk2 : false = uv_btaken BNE (m5 !!! Regidx s2_idx)
                               (m5 !!! Regidx s1_idx)).
      { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5 Hend.
        rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(lia) ltac:(lia)).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype γt γd γs h6 m5 (mword_of_int 0x47c)
                (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int 0x46e) (2 + nn)
                Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_47c with "Hcode"). }
      rewrite (ushp_pc_step 0x47c 4). iIntros (h7) "Hrun".
      (* ---- 0x480  c.mv s1,s2 -- [s = es], which it already is ---- *)
      iApply (wp_uk_cmv γt γd γs h7 m5 (mword_of_int 0x480) s1_idx s2_idx
                (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_5; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_480 with "Hcode"). }
      rewrite (ushp_pc_step 0x480 2). iIntros (h8) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q Hq Hqs1.
        rewrite (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hqs1).
        rewrite (Hm5 q Hqs1). exact (Hcs4 q Hq).
      - iPureIntro.
        rewrite (upd_eq m5 (Regidx s1_idx)
                   (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64))).
        rewrite Hr (ushp_skipws_step r j f Ews).
        assert (Hz : r = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero (S j) f).
        assert (Ee : (s0 + Z.of_nat len) = (s0 + Z.of_nat (j + 1))) by lia.
        rewrite Ee. reflexivity. }
    (* ...or the loop goes round *)
    assert (Hj1 : (S j < len)%nat) by lia.
    assert (Htk2 : true = uv_btaken BNE (m5 !!! Regidx s2_idx)
                            (m5 !!! Regidx s1_idx)).
    { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5.
      rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat (S j))
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      assert (Hne2 : (s0 + Z.of_nat len =? s0 + Z.of_nat (S j)) = false)
        by (apply Z.eqb_neq; lia).
      rewrite Hne2. reflexivity. }
    iApply (wp_uk_btype γt γd γs h6 m5 (mword_of_int 0x47c)
              (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE true
              (mword_of_int 0x46e) (2 + nn)
              Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_47c with "Hcode"). }
    iIntros (h7) "Hrun".
    iApply (IH (S j) h7 m5 ltac:(lia) Hj1 Hs0 Hs64 Hs1_5 Hs2_5 Hs3_5
              with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h8 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. intros q Hq Hqs1.
      rewrite (Hpres q Hq Hqs1). rewrite (Hm5 q Hqs1). exact (Hcs4 q Hq).
    - iPureIntro. rewrite Hret Hr (ushp_skipws_step r j f Ews).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      f_equal. lia.
  Qed.

  (* the scan's ENTRY test, 0x46a: [bgeu s1,a1,0x482] is the [s < es] half of
     the [&&], and it is what makes the cursor's index [j] range over
     [0..len] rather than [0..len-1].  Folding it in here rather than at the
     call site is what lets everything from 0x46a to 0x482 be ONE lemma with
     ONE postcondition, so peek's body has no branch until 0x48c. *)
  Local Lemma wp_kshp_peek_enter (dq dw : dfrac) (s0 : Z) (len j : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (j <= len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    mc !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs h mc (mword_of_int 0x46a) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs h' mc' (mword_of_int 0x482) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Hs1 Hs2 Hs3 Ha1.
    iIntros "#Hcode Hstr Hws Hrun Hcont".
    destruct (Nat.eq_dec j len) as [ Hend | Hne ].
    { (* the cursor is already at [es]: the scan is skipped entirely *)
      assert (Htk : true = uv_btaken BGEU (mc !!! Regidx s1_idx)
                             (mc !!! Regidx a1_idx)).
      { cbn [uv_btaken]. rewrite Hs1 Ha1 Hend.
        rewrite (moi_ge_u (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply Z.geb_le. lia. }
      iApply (wp_uk_btype γt γd γs h mc (mword_of_int 0x46a)
                (mword_of_int 24 : mword 13) a1_idx s1_idx BGEU true
                (mword_of_int 0x482) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_46a with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q _ _. reflexivity.
      - iPureIntro. rewrite Hs1.
        assert (Hz : (len - j)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero j f). f_equal. lia. }
    (* ...otherwise the scan runs *)
    assert (Hjlt : (j < len)%nat) by lia.
    assert (Htk : false = uv_btaken BGEU (mc !!! Regidx s1_idx)
                            (mc !!! Regidx a1_idx)).
    { cbn [uv_btaken]. rewrite Hs1 Ha1.
      rewrite (moi_ge_u (s0 + Z.of_nat j) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs h mc (mword_of_int 0x46a)
              (mword_of_int 24 : mword 13) a1_idx s1_idx BGEU false
              (mword_of_int 0x482) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_46a with "Hcode"). }
    rewrite (ushp_pc_step 0x46a 4). iIntros (h1) "Hrun".
    iApply (wp_kshp_peek_scan dq dw s0 len f nn (len - j)%nat j h1 mc
              eq_refl Hjlt Hs0 Hs64 Hs1 Hs2 Hs3 with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* peek's epilogue, 0x48e..0x49e.  It is reached BOTH ways -- with a0
     already 0 because the byte at the cursor is the line's terminator, and
     with a0 the [snez] of a second strchr because it is not -- so it is
     stated once, at whatever a0 holds.  Nothing it runs touches a0, so the
     caller reads the result back through [ushp_spillback_ne]. *)
  Local Lemma wp_kshp_peek_epi (sp0 spl : mword 64) (vals : nat -> mword 64)
      (nn : nat) :
    forall (h : CpuId) (me : regfile),
    uint sp0 mod 8 = 0 -> 64 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 56 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 7 : mword 6);
                       (s0_idx, mword_of_int 6 : mword 6);
                       (s1_idx, mword_of_int 5 : mword 6);
                       (s2_idx, mword_of_int 4 : mword 6);
                       (s3_idx, mword_of_int 3 : mword 6);
                       (s4_idx, mword_of_int 2 : mword 6);
                       (s5_idx, mword_of_int 1 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 1 -∗
    urun γt γd γs h me (mword_of_int 0x48e) (2 + nn) -∗
    (∀ h' : CpuId,
       urun γt γd γs h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 7 : mword 6);
                             (s0_idx, mword_of_int 6 : mword 6);
                             (s1_idx, mword_of_int 5 : mword 6);
                             (s2_idx, mword_of_int 4 : mword 6);
                             (s3_idx, mword_of_int 3 : mword 6);
                             (s4_idx, mword_of_int 2 : mword 6);
                             (s5_idx, mword_of_int 1 : mword 6)] vals me))
         (ret_pc (vals 0%nat)) (8 + (2 + nn)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros h me Hal8 Hlo Hhi Hsplu Hsp.
    iIntros "#Hcode Hsl Hloc Hrun Hcont".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hoff : forall (i : nat) (r : mword 5) (u : mword 6),
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6)] !! i = Some (r, u) ->
              (uint sp0 - 8 * (Z.of_nat i + 1)) = uint spn + uoff_sdsp u /\
              (uint sp0 - 8 * (Z.of_nat i + 1)) mod 8 = 0 /\
              unot_sp r /\ uint r <> 0).
    { intros i r u Hi.
      destruct i as [| [| [| [| [| [| [| i ]]]]]]]; cbn in Hi;
        try discriminate; injection Hi as Hr Hu0; subst;
        (split;
         [ rewrite Hspu; vm_compute uoff_sdsp; lia
         | split;
           [ exact (ushp_slot_al (uint sp0) _ Hal8)
           | split; [ unfold unot_sp; vm_compute; discriminate
                    | vm_compute; discriminate ] ] ]). }
    (* ---- 0x48e..0x49a  the seven restores ---- *)
    iApply (wp_kshp_restore spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x48e | 1%nat => 0x490
                              | 2%nat => 0x492 | 3%nat => 0x494
                              | 4%nat => 0x496 | 5%nat => 0x498
                              | 6%nat => 0x49a | _ => 0x49c end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h me Hsp
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              Hoff
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_48e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_490 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_492 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_494 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_496 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_498 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_49a with "Hcode") | done ]. }
    iIntros "Hsl" (h1) "Hrun". cbn [length].
    set (mr := ushp_spillback
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6)] vals me).
    assert (Hspr : mr !!! Regidx csp_rs1 = spn).
    { rewrite /mr (ushp_spillback_ne
                     [(ra_idx, mword_of_int 7 : mword 6);
                      (s0_idx, mword_of_int 6 : mword 6);
                      (s1_idx, mword_of_int 5 : mword 6);
                      (s2_idx, mword_of_int 4 : mword 6);
                      (s3_idx, mword_of_int 3 : mword 6);
                      (s4_idx, mword_of_int 2 : mword 6);
                      (s5_idx, mword_of_int 1 : mword 6)] vals me csp_rs1
                     ltac:(intros i r u Hi;
                           destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                           cbn in Hi; try discriminate;
                           injection Hi as Hr Hu0; subst;
                           vm_compute; discriminate)).
      exact Hsp. }
    assert (Hrar : mr !!! Regidx ra_idx = vals 0%nat).
    { rewrite /mr. cbn [ushp_spillback fst].
      rewrite (upd_ne _ (Regidx s5_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s4_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s3_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq me (Regidx ra_idx) (regval_into_reg (vals 0%nat))). }
    assert (Hup : add_vec_int spn (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 8) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    (* ---- 0x49c  c.addi16sp sp,sp,64 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs h1 mr (mword_of_int 0x49c)
              (mword_of_int 4 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hsl Hloc] Hrun").
    { iApply (uis_shp_49c with "Hcode"). }
    { rewrite Hspr Hup.
      iApply (ushp_frame_join sp0 spl 1
                [(ra_idx, mword_of_int 7 : mword 6);
                 (s0_idx, mword_of_int 6 : mword 6);
                 (s1_idx, mword_of_int 5 : mword 6);
                 (s2_idx, mword_of_int 4 : mword 6);
                 (s3_idx, mword_of_int 3 : mword 6);
                 (s4_idx, mword_of_int 2 : mword 6);
                 (s5_idx, mword_of_int 1 : mword 6)]
                vals ltac:(cbn [length]; lia) with "Hsl Hloc"). }
    rewrite Hspr Hup (ushp_pc_step 0x49c 2). iIntros (h2) "Hrun".
    (* ---- 0x49e  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h2
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mr)
              (mword_of_int 0x49e) ra_idx (ret_pc (vals 0%nat)) (8 + (2 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mr (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_49e with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hrun").
  Qed.

  (* peek's ANSWER.  0 once the cursor has run to [es] -- the byte there is
     the line's terminator and C's [&&] short-circuits -- and otherwise
     whether the byte at the cursor is one of [toks]. *)
  Definition ushp_peek_res (len : nat) (f : nat -> bv 8) (k tlen : nat)
      (tf : nat -> bv 8) : Z :=
    if bool_decide (k < len)%nat
    then (match ushp_find tlen 0%nat tf (f k) with
          | Some _ => 1 | None => 0 end)
    else 0.


  (* ---- peek, the whole function --------------------------------------- *)
  Lemma wp_kshp_peek (h : CpuId) (m : regfile) (dq dw dt : dfrac)
      (ps s0 toks : Z) (len off tlen : nat) (f tf : nat -> bv 8)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int toks ->
    (off <= len)%nat ->
    (* the cursor cell currently holds the lexer's position: this is
       what the postcondition's [off] REFERS TO, and without it the
       statement does not mention where the scan starts. *)
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < toks -> toks + Z.of_nat tlen < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dt toks tlen tf -∗
    urun γt γd γs h m (mword_of_int ShSyms.peek) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dt toks tlen tf -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushp_peek_res len f
                    (off + ushp_skipws (len - off) off f) tlen tf) ⌝ -∗
         urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (2 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hs0 Hs64 Ht0 Ht64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode Hcur Hstr Hws Htoks Hrun Hcont".
    rewrite shpp_peek.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    set (kk := (off + ushp_skipws (len - off) off f)%nat).
    assert (Hkk : (kk <= len)%nat).
    { unfold kk. pose proof (ushp_skipws_le (len - off) off f). lia. }
    (* ---- 0x448  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs h m (mword_of_int 0x448)
              (mword_of_int 60 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_448 with "Hcode"). }
    rewrite (ushp_pc_step 0x448 2). iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 56) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 56)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 1
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | _ => m !!! Regidx s5_idx end).
    (* ---- 0x44a..0x456  the seven spills ---- *)
    iApply (wp_kshp_spill spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x44a | 1%nat => 0x44c
                              | 2%nat => 0x44e | 3%nat => 0x450
                              | 4%nat => 0x452 | 5%nat => 0x454
                              | 6%nat => 0x456 | _ => 0x458 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         (* NOT [exact (eq_sym (Hm1 _ ltac:(...)))]: with the
                            register left as [_] the nested [ltac:] runs
                            [vm_compute] on a goal whose register is still an
                            EVAR, and that is the 17 GB.  [refine] fixes the
                            evar by unification FIRST and leaves the side
                            condition as a goal.  Measured: 60 s+ vs 0.19 s. *)
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_44a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_44c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_44e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_450 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_452 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_454 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_456 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x458  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_kshp_fp h2 m1 0x458 (mword_of_int 16 : mword 8) (2 + nn)
              with "[] Hrun").
    { iApply (uis_shp_458 with "Hcode"). }
    iIntros (h3 v458) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v458]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x45a  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs h3 m2 (mword_of_int 0x45a) s4_idx a0_idx
              (mword_of_int ps) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_45a with "Hcode"). }
    rewrite (ushp_pc_step 0x45a 2). iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x45c  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs h4 m3 (mword_of_int 0x45c) s2_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_45c with "Hcode"). }
    rewrite (ushp_pc_step 0x45c 2). iIntros (h5) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x45e  c.mv s5,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs h5 m4 (mword_of_int 0x45e) s5_idx a2_idx
              (mword_of_int toks) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val toks))
              with "[] Hrun").
    { iApply (uis_shp_45e with "Hcode"). }
    rewrite (ushp_pc_step 0x45e 2). iIntros (h6) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int toks : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx s5_idx) (Regidx q) _ Hq)).
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x460  c.ld s1,0(a0) -- the cursor ---- *)
    iApply (wp_uk_cld γt γd γs h6 m5 (mword_of_int 0x460)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx ps w0 (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_5 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              Hps8 ltac:(vm_compute; discriminate)
              with "[] Hcur Hrun").
    { iApply (uis_shp_460 with "Hcode"). }
    iIntros "Hcur". rewrite (ushp_pc_step 0x460 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s1_idx := regval_into_reg w0]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x462  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs h7 m6 (mword_of_int 0x462)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x2462) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_462 with "Hcode"). }
    rewrite (ushp_pc_step 0x462 4). iIntros (h8) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x2462 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x466  addi s3,s3,-1114  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi γt γd γs h8 m7 (mword_of_int 0x466)
              (mword_of_int 2982 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m6 (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x2462
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_466 with "Hcode"). }
    rewrite (ushp_pc_step 0x466 4). iIntros (h9) "Hrun".
    set (m8 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* the register file the scan starts from *)
    assert (Hs1_8 : m8 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat off)).
    { rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m5 (Regidx s1_idx) (regval_into_reg w0)).
      exact Hw0. }
    assert (Hs2_8 : m8 !!! Regidx s2_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s2_idx)
               (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                 : mword 64))). }
    assert (Hs3_8 : m8 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq m7 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    assert (Ha1_8 : m8 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm8 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Hs4_8 : m8 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hm8 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs5_8 : m8 !!! Regidx s5_idx = mword_of_int toks).
    { rewrite (Hm8 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s5_idx)
               (regval_into_reg (mword_of_int toks : mword 64))). }
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* the callee-saved registers the prologue and the setup did NOT write *)
    assert (Hkeep8 : forall q : mword 5,
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              Regidx q <> Regidx s5_idx ->
              m8 !!! Regidx q = m !!! Regidx q).
    { intros q H2 H8 H9 H18 H19 H20 H21.
      rewrite (Hm8 q H19) (Hm7 q H19) (Hm6 q H9) (Hm5 q H21) (Hm4 q H18)
              (Hm3 q H20) (Hm2 q H8). exact (Hm1 q H2). }
    (* ---- 0x46a..0x480  the entry test and the scan ---- *)
    iApply (wp_kshp_peek_enter dq dw s0 len off f nn h9 m8
              Hoffle Hs0 Hs64 Hs1_8 Hs2_8 Hs3_8 Ha1_8
              with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h10 mc') "%Hpres %Hs1c Hrun".
    (* [set] folded [kk] into the goal but [Hs1c] is fresh, so fold it too --
       otherwise [lia] sees [kk] and the expansion as two unrelated atoms *)
    assert (Hkkd : (off + ushp_skipws (len - off) off f)%nat = kk)
      by reflexivity.
    rewrite Hkkd in Hs1c.
    assert (Hs4_c : mc' !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (Hpres s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4_8).
    assert (Hs5_c : mc' !!! Regidx s5_idx = mword_of_int toks)
      by (rewrite (Hpres s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs5_8).
    assert (Hsp_c : mc' !!! Regidx csp_rs1 = spn)
      by (rewrite (Hpres csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hsp8).
    (* ---- 0x482  sd s1,0(s4)  --  *ps = s ---- *)
    iApply (wp_uk_sd γt γd γs h10 mc' (mword_of_int 0x482)
              (mword_of_int 0 : mword 12) s4_idx s1_idx ps w0 (2 + nn)
              ltac:(rewrite Hs4_c (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hps8
              with "[] Hcur Hrun").
    { iApply (uis_shp_482 with "Hcode"). }
    iIntros "Hcur". rewrite Hs1c.
    rewrite (ushp_pc_step 0x482 4). iIntros (h11) "Hrun".
    (* ---- 0x486  lbu a1,0(s1) -- a BODY byte, or the terminator ---- *)
    destruct (Nat.eq_dec kk len) as [ Hkend | Hkne ].
    { (* the cursor ran to [es]: the byte is the NUL and peek answers 0 *)
      iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_uk_lbu γt γd γs h11 mc' (mword_of_int 0x486)
                (mword_of_int 0 : mword 12) s1_idx a1_idx dq
                (s0 + Z.of_nat len) ubyte0 (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs1c Hkend
                        (uint_moi (s0 + Z.of_nat len)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_shp_486 with "Hcode"). }
      iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
      rewrite (ushp_pc_step 0x486 4). iIntros (h12) "Hrun".
      set (n9 := <[Regidx a1_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                       : mword 64)]> mc').
      assert (Hn9 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                      n9 !!! Regidx q = mc' !!! Regidx q)
        by (intros q Hq; exact (upd_ne mc' (Regidx a1_idx) (Regidx q) _ Hq)).
      (* ---- 0x48a  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs h12 n9 (mword_of_int 0x48a)
                (mword_of_int 0 : mword 6) a0_idx (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_48a with "Hcode"). }
      rewrite (ushp_pc_step 0x48a 2). iIntros (h13) "Hrun".
      set (n10 := <[Regidx a0_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 0 : mword 6)
                          : mword 64)]> n9).
      assert (Hn10 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                       n10 !!! Regidx q = n9 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n9 (Regidx a0_idx) (Regidx q) _ Hq)).
      (* ---- 0x48c  c.bnez a1,0x4a0 -- NOT taken ---- *)
      assert (Ha1_10 : n10 !!! Regidx a1_idx
                       = mword_of_int (bv_unsigned ubyte0)).
      { rewrite (Hn10 a1_idx ltac:(vm_compute; discriminate)).
        rewrite (upd_eq mc' (Regidx a1_idx)
                   (regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                     : mword 64))).
        exact (zext8_moi ubyte0). }
      assert (Htk : false = neq_vec (n10 !!! Regidx a1_idx) zero_reg).
      { rewrite Ha1_10. unfold neq_vec. rewrite (ushp_zext_nul ubyte0).
        rewrite (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl).
        reflexivity. }
      iApply (wp_uk_cbnez γt γd γs h13 n10 (mword_of_int 0x48c)
                (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3)
                a1_idx false (mword_of_int 0x4a0) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_48c with "Hcode"). }
      rewrite (ushp_pc_step 0x48c 2). iIntros (h14) "Hrun".
      assert (Hspn10 : n10 !!! Regidx csp_rs1 = spn).
      { rewrite (Hn10 csp_rs1 ltac:(vm_compute; discriminate)).
        rewrite (Hn9 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_c. }
      iApply (wp_kshp_peek_epi sp0 spl vals nn h14 n10
                Hal8 Hlo ltac:(lia) Hsplu Hspn10
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with "Hcur Hstr Hws Htoks [] [] Hrun").
      - iPureIntro. intros q Hq.
        cbn [ushp_spillback fst].
        destruct (Z.eq_dec (uint q) 2) as [ E2 | E2 ].
        { rewrite (ushp_ridx_eq q csp_rs1
                     ltac:(rewrite E2; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx csp_rs1) (regval_into_reg sp0)). }
        assert (Hq2 : Regidx q <> Regidx csp_rs1)
          by (apply ushp_ridx_ne;
              assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
              rewrite Hc; exact E2).
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx q) _ Hq2).
        destruct (Z.eq_dec (uint q) 21) as [ E21 | E21 ].
        { rewrite (ushp_ridx_eq q s5_idx
                     ltac:(rewrite E21; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx s5_idx)
                   (regval_into_reg (m !!! Regidx s5_idx))). }
        assert (Hq21 : Regidx q <> Regidx s5_idx)
          by (apply ushp_ridx_ne;
              assert (Hc : uint s5_idx = 21) by (vm_compute; reflexivity);
              rewrite Hc; exact E21).
        rewrite (upd_ne _ (Regidx s5_idx) (Regidx q) _ Hq21).
        destruct (Z.eq_dec (uint q) 20) as [ E20 | E20 ].
        { rewrite (ushp_ridx_eq q s4_idx
                     ltac:(rewrite E20; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx s4_idx)
                   (regval_into_reg (m !!! Regidx s4_idx))). }
        assert (Hq20 : Regidx q <> Regidx s4_idx)
          by (apply ushp_ridx_ne;
              assert (Hc : uint s4_idx = 20) by (vm_compute; reflexivity);
              rewrite Hc; exact E20).
        rewrite (upd_ne _ (Regidx s4_idx) (Regidx q) _ Hq20).
        destruct (Z.eq_dec (uint q) 19) as [ E19 | E19 ].
        { rewrite (ushp_ridx_eq q s3_idx
                     ltac:(rewrite E19; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx s3_idx)
                   (regval_into_reg (m !!! Regidx s3_idx))). }
        assert (Hq19 : Regidx q <> Regidx s3_idx)
          by (apply ushp_ridx_ne;
              assert (Hc : uint s3_idx = 19) by (vm_compute; reflexivity);
              rewrite Hc; exact E19).
        rewrite (upd_ne _ (Regidx s3_idx) (Regidx q) _ Hq19).
        destruct (Z.eq_dec (uint q) 18) as [ E18 | E18 ].
        { rewrite (ushp_ridx_eq q s2_idx
                     ltac:(rewrite E18; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx s2_idx)
                   (regval_into_reg (m !!! Regidx s2_idx))). }
        assert (Hq18 : Regidx q <> Regidx s2_idx)
          by (apply ushp_ridx_ne;
              assert (Hc : uint s2_idx = 18) by (vm_compute; reflexivity);
              rewrite Hc; exact E18).
        rewrite (upd_ne _ (Regidx s2_idx) (Regidx q) _ Hq18).
        destruct (Z.eq_dec (uint q) 9) as [ E9 | E9 ].
        { rewrite (ushp_ridx_eq q s1_idx
                     ltac:(rewrite E9; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx s1_idx)
                   (regval_into_reg (m !!! Regidx s1_idx))). }
        assert (Hq9 : Regidx q <> Regidx s1_idx)
          by (apply ushp_ridx_ne;
              assert (Hc : uint s1_idx = 9) by (vm_compute; reflexivity);
              rewrite Hc; exact E9).
        rewrite (upd_ne _ (Regidx s1_idx) (Regidx q) _ Hq9).
        destruct (Z.eq_dec (uint q) 8) as [ E8 | E8 ].
        { rewrite (ushp_ridx_eq q s0_idx
                     ltac:(rewrite E8; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx s0_idx)
                   (regval_into_reg (m !!! Regidx s0_idx))). }
        assert (Hq8 : Regidx q <> Regidx s0_idx)
          by (apply ushp_ridx_ne;
              assert (Hc : uint s0_idx = 8) by (vm_compute; reflexivity);
              rewrite Hc; exact E8).
        rewrite (upd_ne _ (Regidx s0_idx) (Regidx q) _ Hq8).
        assert (Hqra : Regidx q <> Regidx ra_idx)
          by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
        rewrite (upd_ne _ (Regidx ra_idx) (Regidx q) _ Hqra).
        rewrite (Hn10 q (ushp_cs_ne q a0_idx Hq
                           ltac:(vm_compute; reflexivity))).
        rewrite (Hn9 q (ushp_cs_ne q a1_idx Hq
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hpres q Hq Hq9).
        exact (Hkeep8 q Hq2 Hq8 Hq9 Hq18 Hq19 Hq20 Hq21).
      - iPureIntro. cbn [ushp_spillback fst].
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx s5_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx s4_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx s3_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx s2_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx s1_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_eq n9 (Regidx a0_idx)
                   (regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64))).
        unfold ushp_peek_res.
        rewrite (bool_decide_eq_false_2 (kk < len)%nat ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
    (* THE CURSOR IS ON A BODY BYTE: peek asks the token table ---- *)
    assert (Hklt : (kk < len)%nat) by lia.
    iDestruct (ustr_nonul with "Hstr") as %Hnenul.
    iDestruct (ustr_byte γd dq s0 len f kk Hklt with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs h11 mc' (mword_of_int 0x486)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat kk) (f kk) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1c
                      (uint_moi (s0 + Z.of_nat kk)
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_486 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x486 4). iIntros (h12) "Hrun".
    set (n9 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f kk) : mword 8)
                                     : mword 64)]> mc').
    assert (Hn9 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                    n9 !!! Regidx q = mc' !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc' (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x48a  c.li a0,0 ---- *)
    iApply (wp_uk_cli γt γd γs h12 n9 (mword_of_int 0x48a)
              (mword_of_int 0 : mword 6) a0_idx (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_48a with "Hcode"). }
    rewrite (ushp_pc_step 0x48a 2). iIntros (h13) "Hrun".
    set (n10 := <[Regidx a0_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 0 : mword 6)
                        : mword 64)]> n9).
    assert (Hn10 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n10 !!! Regidx q = n9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n9 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha1_10 : n10 !!! Regidx a1_idx
                     = mword_of_int (bv_unsigned (f kk))).
    { rewrite (Hn10 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq mc' (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f kk) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f kk)). }
    (* ---- 0x48c  c.bnez a1,0x4a0 -- TAKEN ---- *)
    assert (Htk : true = neq_vec (n10 !!! Regidx a1_idx) zero_reg).
    { rewrite Ha1_10. unfold neq_vec. rewrite (ushp_zext_nul (f kk)).
      rewrite (bool_decide_eq_false_2 (f kk = ubyte0) (Hnenul kk Hklt)).
      reflexivity. }
    iApply (wp_uk_cbnez γt γd γs h13 n10 (mword_of_int 0x48c)
              (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3)
              a1_idx true (mword_of_int 0x4a0) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_48c with "Hcode"). }
    iIntros (h14) "Hrun".
    (* ---- 0x4a0  c.mv a0,s5 ---- *)
    assert (Hs5_10 : n10 !!! Regidx s5_idx = mword_of_int toks).
    { rewrite (Hn10 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn9 s5_idx ltac:(vm_compute; discriminate)). exact Hs5_c. }
    iApply (wp_uk_cmv γt γd γs h14 n10 (mword_of_int 0x4a0) a0_idx s5_idx
              (mword_of_int toks) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_10; symmetry; exact (ushp_mv_val toks))
              with "[] Hrun").
    { iApply (uis_shp_4a0 with "Hcode"). }
    rewrite (ushp_pc_step 0x4a0 2). iIntros (h15) "Hrun".
    set (n11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int toks : mword 64)]> n10).
    assert (Hn11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n11 !!! Regidx q = n10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x4a2  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs h15 n11 (mword_of_int 0x4a2)
              (mword_of_int 1504 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x4a6) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4a2 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (n12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x4a6 : mword 64)]> n11).
    assert (Hn12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     n12 !!! Regidx q = n11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha0_12 : n12 !!! Regidx a0_idx = mword_of_int toks).
    { rewrite (Hn12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int toks : mword 64))). }
    assert (Ha1_12 : n12 !!! Regidx a1_idx
                     = mword_of_int (bv_unsigned (f kk))).
    { rewrite (Hn12 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn11 a1_idx ltac:(vm_compute; discriminate)). exact Ha1_10. }
    assert (Eret : ret_pc (n12 !!! Regidx ra_idx) = mword_of_int 0x4a6).
    { rewrite (upd_eq n11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x4a6 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h16 n12 dt toks tlen tf (f kk) nn
              Ha0_12 Ha1_12 ltac:(lia) ltac:(unfold Z64 in *; lia)
              with "Hcode Htoks Hrun").
    iIntros "Htoks" (h17 n13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret.
    (* ---- 0x4a6  snez a0,a0  --  sltu a0,x0,a0 ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Hchrb : 0 <= ushp_chr toks tlen 0%nat tf (f kk) < Z64).
    { unfold ushp_chr.
      destruct (ushp_find tlen 0%nat tf (f kk)) as [ jj | ] eqn:Ej;
        [ | unfold Z64; lia ].
      pose proof (ushp_find_ge tlen 0%nat tf (f kk) jj Ej) as Hjr.
      unfold Z64 in *. lia. }
    iApply (wp_uk_sltu γt γd γs h17 n13 (mword_of_int 0x4a6)
              x0_idx a0_idx a0_idx
              (mword_of_int (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                             then 1 else 0)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hx0 Ha0_13; symmetry;
                    exact (ushp_snez_val
                             (ushp_chr toks tlen 0%nat tf (f kk)) Hchrb))
              with "[] Hrun").
    { iApply (uis_shp_4a6 with "Hcode"). }
    rewrite (ushp_pc_step 0x4a6 4). iIntros (h18) "Hrun".
    set (n14 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int
                          (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                           then 1 else 0) : mword 64)]> n13).
    assert (Hn14 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n14 !!! Regidx q = n13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x4aa  c.j 0x48e ---- *)
    iApply (wp_uk_cj γt γd γs h18 n14 (mword_of_int 0x4aa)
              (mword_of_int 2034 : mword 11) (mword_of_int 0x48e) (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4aa with "Hcode"). }
    iIntros (h19) "Hrun".
    assert (Hspn14 : n14 !!! Regidx csp_rs1 = spn).
    { rewrite (Hn14 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hn12 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn11 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn10 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_c. }
    iApply (wp_kshp_peek_epi sp0 spl vals nn h19 n14
              Hal8 Hlo ltac:(lia) Hsplu Hspn14
              with "Hcode Hsl Hloc Hrun").
    iIntros (hf) "Hrun".
    iApply ("Hcont" with "Hcur Hstr Hws Htoks [] [] Hrun").
    - iPureIntro. intros q Hq.
      cbn [ushp_spillback fst].
      destruct (Z.eq_dec (uint q) 2) as [ E2 | E2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite E2; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx csp_rs1) (regval_into_reg sp0)). }
      assert (Hq2 : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
            assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
            rewrite Hc; exact E2).
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx q) _ Hq2).
      destruct (Z.eq_dec (uint q) 21) as [ E21 | E21 ].
      { rewrite (ushp_ridx_eq q s5_idx
                   ltac:(rewrite E21; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s5_idx)
                 (regval_into_reg (m !!! Regidx s5_idx))). }
      assert (Hq21 : Regidx q <> Regidx s5_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s5_idx = 21) by (vm_compute; reflexivity);
            rewrite Hc; exact E21).
      rewrite (upd_ne _ (Regidx s5_idx) (Regidx q) _ Hq21).
      destruct (Z.eq_dec (uint q) 20) as [ E20 | E20 ].
      { rewrite (ushp_ridx_eq q s4_idx
                   ltac:(rewrite E20; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s4_idx)
                 (regval_into_reg (m !!! Regidx s4_idx))). }
      assert (Hq20 : Regidx q <> Regidx s4_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s4_idx = 20) by (vm_compute; reflexivity);
            rewrite Hc; exact E20).
      rewrite (upd_ne _ (Regidx s4_idx) (Regidx q) _ Hq20).
      destruct (Z.eq_dec (uint q) 19) as [ E19 | E19 ].
      { rewrite (ushp_ridx_eq q s3_idx
                   ltac:(rewrite E19; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s3_idx)
                 (regval_into_reg (m !!! Regidx s3_idx))). }
      assert (Hq19 : Regidx q <> Regidx s3_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s3_idx = 19) by (vm_compute; reflexivity);
            rewrite Hc; exact E19).
      rewrite (upd_ne _ (Regidx s3_idx) (Regidx q) _ Hq19).
      destruct (Z.eq_dec (uint q) 18) as [ E18 | E18 ].
      { rewrite (ushp_ridx_eq q s2_idx
                   ltac:(rewrite E18; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s2_idx)
                 (regval_into_reg (m !!! Regidx s2_idx))). }
      assert (Hq18 : Regidx q <> Regidx s2_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s2_idx = 18) by (vm_compute; reflexivity);
            rewrite Hc; exact E18).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx q) _ Hq18).
      destruct (Z.eq_dec (uint q) 9) as [ E9 | E9 ].
      { rewrite (ushp_ridx_eq q s1_idx
                   ltac:(rewrite E9; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s1_idx)
                 (regval_into_reg (m !!! Regidx s1_idx))). }
      assert (Hq9 : Regidx q <> Regidx s1_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s1_idx = 9) by (vm_compute; reflexivity);
            rewrite Hc; exact E9).
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx q) _ Hq9).
      destruct (Z.eq_dec (uint q) 8) as [ E8 | E8 ].
      { rewrite (ushp_ridx_eq q s0_idx
                   ltac:(rewrite E8; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s0_idx)
                 (regval_into_reg (m !!! Regidx s0_idx))). }
      assert (Hq8 : Regidx q <> Regidx s0_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s0_idx = 8) by (vm_compute; reflexivity);
            rewrite Hc; exact E8).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx q) _ Hq8).
      assert (Hqra : Regidx q <> Regidx ra_idx)
        by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx q) _ Hqra).
      rewrite (Hn14 q (ushp_cs_ne q a0_idx Hq
                         ltac:(vm_compute; reflexivity))).
      rewrite (Hcs1213 q Hq).
      rewrite (Hn12 q Hqra).
      rewrite (Hn11 q (ushp_cs_ne q a0_idx Hq
                         ltac:(vm_compute; reflexivity))).
      rewrite (Hn10 q (ushp_cs_ne q a0_idx Hq
                         ltac:(vm_compute; reflexivity))).
      rewrite (Hn9 q (ushp_cs_ne q a1_idx Hq
                        ltac:(vm_compute; reflexivity))).
      rewrite (Hpres q Hq Hq9).
      exact (Hkeep8 q Hq2 Hq8 Hq9 Hq18 Hq19 Hq20 Hq21).
    - iPureIntro. cbn [ushp_spillback fst].
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s5_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s4_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s3_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq n13 (Regidx a0_idx)
                 (regval_into_reg
                    (mword_of_int
                       (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                        then 1 else 0) : mword 64))).
      unfold ushp_peek_res.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt).
      unfold ushp_chr.
      destruct (ushp_find tlen 0%nat tf (f kk)) as [ jj | ] eqn:Ej.
      + assert (Hgt : (0 <? toks + Z.of_nat jj) = true)
          by (apply Z.ltb_lt; lia).
        rewrite Hgt. reflexivity.
      + assert (Hgt : (0 <? 0) = false) by reflexivity.
        rewrite Hgt. reflexivity.
  Qed.



  (* ===================================================================== *)
  (* §7 execcmd @0x1d2 -- 19 instructions, a four-word frame, NO branch.    *)
  (*                                                                       *)
  (*   struct cmd *execcmd(void) {                                          *)
  (*     struct execcmd *cmd;                                               *)
  (*     cmd = malloc(sizeof( *cmd));                                       *)
  (*     memset(cmd, 0, sizeof( *cmd));                                     *)
  (*     cmd->type = EXEC;                                                  *)
  (*     return (struct cmd * )cmd;  }                                      *)
  (*                                                                       *)
  (* THE FIRST LEMMA IN THIS FILE THAT CARRIES [ushp_malloc_ok], and the    *)
  (* only one that carries it directly: parseexec, parsepipe, parseline and *)
  (* parsecmd will carry it THROUGH this lemma.  Everything above §7 is     *)
  (* unconditional; this one is not, and says so here rather than only in   *)
  (* the lane report.                                                       *)
  (*                                                                       *)
  (* WHAT THE POSTCONDITION SAYS, and why it is the honest reading.  The    *)
  (* node comes back as [ushp_exec_at s0 p []] -- an EXEC node whose token  *)
  (* list is EMPTY.  That is not a weakening: parseexec fills the slots     *)
  (* itself, one per [gettoken], and the invariant it runs its argument     *)
  (* loop on is this predicate at the tokens recorded SO FAR.  The empty    *)
  (* list is the loop's base case, and the NULL cap it demands at slot 0 is *)
  (* exactly what the [memset] zeroed -- which is why the whole stage was   *)
  (* blocked on [wp_ksh_memset]'s postcondition and is not any more.  [s0]  *)
  (* is unconstrained because an empty token list mentions no line at all.  *)
  (*                                                                       *)
  (* THE BUDGET IS THE CALL CHAIN: four words of execcmd's own frame on top *)
  (* of malloc's ten (its 64-byte frame plus [free]/[sbrk]'s two), and      *)
  (* memset's two fit inside those ten.                                     *)
  (* ===================================================================== *)

  Local Lemma shpp_malloc : ShSyms.malloc = 0x118c.
  Proof. unfold ShSyms.malloc. reflexivity. Qed.
  Local Lemma shpp_memset : ShSyms.memset = 0xa5c.
  Proof. unfold ShSyms.memset. reflexivity. Qed.

  Lemma wp_kshp_execcmd (h : CpuId) (m : regfile) (s0 : Z) (nn : nat) :
    shp_code γt -∗
    urun γt γd γs h m (mword_of_int ShSyms.execcmd) (4 + (10 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ 0 < p /\ p mod 16 = 0 /\ p + 168 < 2 ^ 38 ⌝ -∗
       ushp_exec_at s0 p [] -∗
       urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (10 + nn)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    iDestruct (ushp_code_shk γt with "Hcode") as "#Hkcode".
    rewrite shpp_execcmd.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    (* ---- 0x1d2  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0x1d2)
              (mword_of_int 32 : mword 6) 4 (10 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1d2 with "Hcode"). }
    rewrite (ushp_pc_step 0x1d2 2). iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 4))).
    assert (Hspu : uint spn = uint sp0 - 32).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    (* ---- the frame: three spill slots on top of one unused local ---- *)
    set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 24)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 1
                 [(ra_idx, mword_of_int 3 : mword 6);
                  (s0_idx, mword_of_int 2 : mword 6);
                  (s1_idx, mword_of_int 1 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    (* the one pure fact per spill instruction, at concrete numbers *)
    assert (Hoff : forall (i : nat) (r : mword 5) (u : mword 6),
              [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] !! i = Some (r, u) ->
              (uint sp0 - 8 * (Z.of_nat i + 1)) = uint spn + uoff_sdsp u /\
              (uint sp0 - 8 * (Z.of_nat i + 1)) mod 8 = 0 /\
              unot_sp r /\ uint r <> 0).
    { intros i r u Hi.
      destruct i as [| [| [| i ]]]; cbn in Hi; try discriminate;
        injection Hi as Hr Hu0; subst.
      - assert (Hu : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
          by (vm_compute; reflexivity).
        rewrite Hu Hspu.
        repeat split; [ lia | exact (ushp_slot_al (uint sp0) 0 Hal8)
                      | unfold unot_sp; vm_compute; discriminate
                      | vm_compute; discriminate ].
      - assert (Hu : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
          by (vm_compute; reflexivity).
        rewrite Hu Hspu.
        repeat split; [ lia | exact (ushp_slot_al (uint sp0) 1 Hal8)
                      | unfold unot_sp; vm_compute; discriminate
                      | vm_compute; discriminate ].
      - assert (Hu : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
          by (vm_compute; reflexivity).
        rewrite Hu Hspu.
        repeat split; [ lia | exact (ushp_slot_al (uint sp0) 2 Hal8)
                      | unfold unot_sp; vm_compute; discriminate
                      | vm_compute; discriminate ]. }
    (* ---- 0x1d4..0x1d8  the three spills ---- *)
    iApply (wp_kshp_spill spn (10 + nn)
              [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x1d4 | 1%nat => 0x1d6
                              | 2%nat => 0x1d8 | _ => 0x1da end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              (fun i : nat => match i with
                              | 0%nat => m !!! Regidx ra_idx
                              | 1%nat => m !!! Regidx s0_idx
                              | _ => m !!! Regidx s1_idx end)
              h1 m1 Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| i ]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct (Hoff i r u Hi) as [ H1 [ H2 [ H3 H4 ]]];
                    split; [ exact H1 | split; [ exact H2 | ] ];
                    destruct i as [| [| [| i ]]]; cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst; cbn;
                    [ exact (eq_sym (Hm1 ra_idx ltac:(vm_compute; discriminate)))
                    | exact (eq_sym (Hm1 s0_idx ltac:(vm_compute; discriminate)))
                    | exact (eq_sym (Hm1 s1_idx ltac:(vm_compute; discriminate))) ])
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_1d4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1d6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1d8 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x1da  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_uk_caddi4spn γt γd γs h2 m1 (mword_of_int 0x1da)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))
              (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shp_1da with "Hcode"). }
    rewrite (ushp_pc_step 0x1da 2). iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 8 : mword 8))))]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn)
      by (rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    (* ---- 0x1dc  li a0,168 ---- *)
    assert (E168 : (sign_extend' 64 (mword_of_int 168 : mword 12) : mword 64)
                   = mword_of_int 168)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_li γt γd γs h3 m2 (mword_of_int 0x1dc)
              (mword_of_int 168 : mword 12) a0_idx (mword_of_int 168) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E168; symmetry; exact (ushp_mv_val 168))
              with "[] Hrun").
    { iApply (uis_shp_1dc with "Hcode"). }
    rewrite (ushp_pc_step 0x1dc 4). iIntros (h4) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 168 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x1e0  jal 118c <malloc> ---- *)
    iApply (wp_uk_jal γt γd γs h4 m3 (mword_of_int 0x1e0)
              (mword_of_int 4012 : mword 21) ra_idx
              (mword_of_int 0x118c) (mword_of_int 0x1e4) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1e0 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1e4 : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int 168).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int 168 : mword 64))). }
    assert (Eret1 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x1e4).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x1e4 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_malloc.
    (* ---- malloc(168) -- THE HYPOTHESIS, and this lemma's only taint ---- *)
    iApply (ushp_malloc_ok h5 m4 168 nn Ha0_4 ltac:(lia)
              ltac:(unfold Z31; lia) with "Hcode Hrun").
    iIntros (h6 m5 p g) "%Hcs45 %Ha0_5 %Hpb Hbs Hrun".
    rewrite Eret1.
    destruct Hpb as [ Hp0 [ Hp16 Hpsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Hp64 : 0 <= p < Z64)
      by (rewrite H38 in Hpsz; unfold Z64; lia).
    assert (Hp8 : p mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp16 ]. }
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    assert (E168n : Z.to_nat 168 = 168%nat) by (vm_compute; reflexivity).
    rewrite E168n.
    (* ---- 0x1e4  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs h6 m5 (mword_of_int 0x1e4) s1_idx a0_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_1e4 with "Hcode"). }
    rewrite (ushp_pc_step 0x1e4 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_6 : m6 !!! Regidx s1_idx = mword_of_int p)
      by exact (upd_eq m5 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    (* ---- 0x1e6  li a2,168 ---- *)
    iApply (wp_uk_li γt γd γs h7 m6 (mword_of_int 0x1e6)
              (mword_of_int 168 : mword 12) a2_idx (mword_of_int 168) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E168; symmetry; exact (ushp_mv_val 168))
              with "[] Hrun").
    { iApply (uis_shp_1e6 with "Hcode"). }
    rewrite (ushp_pc_step 0x1e6 4). iIntros (h8) "Hrun".
    set (m7 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 168 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x1ea  c.li a1,0 ---- *)
    iApply (wp_uk_cli γt γd γs h8 m7 (mword_of_int 0x1ea)
              (mword_of_int 0 : mword 6) a1_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_1ea with "Hcode"). }
    rewrite (ushp_pc_step 0x1ea 2). iIntros (h9) "Hrun".
    set (m8 := <[Regidx a1_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x1ec  jal a5c <memset> ---- *)
    iApply (wp_uk_jal γt γd γs h9 m8 (mword_of_int 0x1ec)
              (mword_of_int 2160 : mword 21) ra_idx
              (mword_of_int 0xa5c) (mword_of_int 0x1f0) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1ec with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1f0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha1_9 : m9 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite (Hm9 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m7 (Regidx a1_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_9 : m9 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm9 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_5. }
    assert (Ha2_9 : m9 !!! Regidx a2_idx = mword_of_int (Z.of_nat 168)).
    { rewrite (Hm9 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m6 (Regidx a2_idx)
                 (regval_into_reg (mword_of_int 168 : mword 64))).
      now f_equal. }
    assert (Eret2 : ret_pc (m9 !!! Regidx ra_idx) = mword_of_int 0x1f0).
    { rewrite (upd_eq m8 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x1f0 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_memset.
    (* ---- memset(cmd, 0, 168) -- UkSh.v's, across the code bridge ---- *)
    iApply (wp_ksh_memset γt γd γs h10 m9 p 168%nat g (8 + nn)
              Ha0_9 Ha2_9 ltac:(lia) ltac:(unfold Z31; lia)
              with "Hkcode Hbs Hrun").
    iIntros "Hbs" (h11 m10) "%Hcs910 Hrun".
    rewrite Eret2 Ha1_9.
    assert (Eb0 : nth_byte (mword_of_int 0 : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    rewrite Eb0.
    (* ---- the node's four slices: type, padding, argv, eargv ---- *)
    iDestruct (ushp_peel0 p (p + 4) 4 164 ltac:(lia) with "Hbs")
      as "[Hty Hbs]".
    iDestruct (ushp_peel0 (p + 4) (p + 8) 4 160 ltac:(lia) with "Hbs")
      as "[Hpad Hbs]".
    iDestruct (ushp_peel0 (p + 8) (p + 88) 80 80 ltac:(lia) with "Hbs")
      as "[Hav Hev]".
    (* ---- 0x1f0  c.li a5,1 ---- *)
    iApply (wp_uk_cli γt γd γs h11 m10 (mword_of_int 0x1f0)
              (mword_of_int 1 : mword 6) a5_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_1f0 with "Hcode"). }
    rewrite (ushp_pc_step 0x1f0 2). iIntros (h12) "Hrun".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 1 : mword 6)
                        : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_11 : m11 !!! Regidx a5_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_eq m10 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs1_11 : m11 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hm11 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_6. }
    (* ---- 0x1f2  c.sw a5,0(s1)  --  cmd->type = EXEC ---- *)
    iApply (wp_uk_csw γt γd γs h12 m11 (mword_of_int 0x1f2)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 7 : mword 3) s1_idx a5_idx p
              (mword_of_int 0 : mword 64) (10 + nn)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_11 (uint_moi p Hp64);
                    vm_compute uoff_c4; lia)
              Hp4
              with "[] [Hty] Hrun").
    { iApply (uis_shp_1f2 with "Hcode"). }
    { iApply (ushp_ubytes_ext p 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hty").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hty". rewrite Ha5_11.
    rewrite (ushp_pc_step 0x1f2 2). iIntros (h13) "Hrun".
    (* ---- 0x1f4  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs h13 m11 (mword_of_int 0x1f4) a0_idx s1_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_1f4 with "Hcode"). }
    rewrite (ushp_pc_step 0x1f4 2). iIntros (h14) "Hrun".
    set (m12 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hsp12 : m12 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm12 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm11 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0x1f6..0x1fa  the three restores ---- *)
    iApply (wp_kshp_restore spn (10 + nn)
              [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x1f6 | 1%nat => 0x1f8
                              | 2%nat => 0x1fa | _ => 0x1fc end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              (fun i : nat => match i with
                              | 0%nat => m !!! Regidx ra_idx
                              | 1%nat => m !!! Regidx s0_idx
                              | _ => m !!! Regidx s1_idx end)
              h14 m12 Hsp12
              ltac:(intros i Hi; destruct i as [| [| [| i ]]];
                    cbn in Hi |- *; try reflexivity; lia)
              Hoff
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_1f6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1f8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1fa with "Hcode") | done ]. }
    iIntros "Hsl" (h15) "Hrun". cbn [length ushp_spillback fst].
    set (me := <[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]>
                 (<[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]>
                    (<[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]>
                       m12))).
    assert (Hspe : me !!! Regidx csp_rs1 = spn).
    { rewrite /me.
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp12. }
    assert (Hup : add_vec_int spn (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 4) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    (* ---- 0x1fc  c.addi16sp sp,sp,32 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs h15 me (mword_of_int 0x1fc)
              (mword_of_int 2 : mword 6) 4 (10 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hsl Hloc] Hrun").
    { iApply (uis_shp_1fc with "Hcode"). }
    { rewrite Hspe Hup.
      iApply (ushp_frame_join sp0 spl 1
                [(ra_idx, mword_of_int 3 : mword 6);
                 (s0_idx, mword_of_int 2 : mword 6);
                 (s1_idx, mword_of_int 1 : mword 6)]
                (fun i : nat => match i with
                                | 0%nat => m !!! Regidx ra_idx
                                | 1%nat => m !!! Regidx s0_idx
                                | _ => m !!! Regidx s1_idx end)
                ltac:(cbn [length]; lia) with "Hsl Hloc"). }
    rewrite Hspe Hup (ushp_pc_step 0x1fc 2). iIntros (h16) "Hrun".
    set (mf := <[Regidx csp_rs1 := regval_into_reg sp0]> me).
    assert (Hraf : mf !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m12 (Regidx ra_idx)
               (regval_into_reg (m !!! Regidx ra_idx))). }
    (* ---- 0x1fe  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h16 mf (mword_of_int 0x1fe) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (4 + (10 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraf; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1fe with "Hcode"). }
    iIntros (h17) "Hrun".
    (* ---- what the caller reads back ---- *)
    iApply ("Hcont" $! h17 mf p with "[] [] [] [Hty Hpad Hav Hev] Hrun").
    - iPureIntro. intros q Hq.
      destruct (Z.eq_dec (uint q) 2) as [ Eq2 | Eq2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite Eq2; vm_compute; reflexivity)).
        rewrite /mf. exact (upd_eq me (Regidx csp_rs1)
                              (regval_into_reg sp0)). }
      destruct (Z.eq_dec (uint q) 8) as [ Eq8 | Eq8 ].
      { rewrite (ushp_ridx_eq q s0_idx
                   ltac:(rewrite Eq8; vm_compute; reflexivity)).
        rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx s0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx s0_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (upd_eq _ (Regidx s0_idx)
                 (regval_into_reg (m !!! Regidx s0_idx))). }
      destruct (Z.eq_dec (uint q) 9) as [ Eq9 | Eq9 ].
      { rewrite (ushp_ridx_eq q s1_idx
                   ltac:(rewrite Eq9; vm_compute; reflexivity)).
        rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /me. exact (upd_eq _ (Regidx s1_idx)
                              (regval_into_reg (m !!! Regidx s1_idx))). }
      assert (Hqsp : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
            assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
            rewrite Hc; exact Eq2).
      assert (Hqs0 : Regidx q <> Regidx s0_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s0_idx = 8) by (vm_compute; reflexivity);
            rewrite Hc; exact Eq8).
      assert (Hqs1 : Regidx q <> Regidx s1_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s1_idx = 9) by (vm_compute; reflexivity);
            rewrite Hc; exact Eq9).
      assert (Hqra : Regidx q <> Regidx ra_idx)
        by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
      rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx q) _ Hqsp).
      rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx q) _ Hqs1).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx q) _ Hqs0).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx q) _ Hqra).
      rewrite (Hm12 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm11 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hcs910 q Hq).
      rewrite (Hm9 q Hqra).
      rewrite (Hm8 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm7 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm6 q Hqs1).
      rewrite (Hcs45 q Hq).
      rewrite (Hm4 q Hqra).
      rewrite (Hm3 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm2 q Hqs0). exact (Hm1 q Hqsp).
    - iPureIntro.
      rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx a0_idx)
               (regval_into_reg (mword_of_int p : mword 64))).
    - iPureIntro. exact (conj Hp0 (conj Hp16 Hpsz)).
    - rewrite /ushp_exec_at /ushp_type_at.
      iSplitR; [ iPureIntro; cbn [length]; lia | ].
      iSplitR; [ iPureIntro; exact Hp0 | ].
      iSplitR; [ iPureIntro; exact Hp8 | ].
      iSplitL "Hty Hpad".
      + iSplitL "Hty".
        * iApply (ushp_ubytes_ext p 4
                    (nth_byte (mword_of_int 1 : mword 64))
                    (nth_byte (mword_of_int 1 : mword 32)) with "Hty").
          intros j Hj. destruct j as [| [| [| [| j ]]]];
            [ vm_compute; reflexivity | vm_compute; reflexivity
            | vm_compute; reflexivity | vm_compute; reflexivity | lia ].
        * iExists (fun _ : nat => ubyte0). iExact "Hpad".
      + iSplitL "Hav".
        * iApply (ushp_slots_nil s0 (p + 8) fst (fun _ : nat => ubyte0)
                    ltac:(intros j _; reflexivity) with "Hav").
        * iApply (ushp_slots_nil s0 (p + 88) snd (fun _ : nat => ubyte0)
                    ltac:(intros j _; reflexivity) with "Hev").
  Qed.

End UkShParse.
