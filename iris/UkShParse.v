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
(* THE MERGE THIS FILE WAS PARKED THROUGH, RECONCILED (2026-09-01).        *)
(* Two edits crossed: upstream's fd/gfd wave threaded a FOURTH gname       *)
(* through [urun] (the program's own descriptor table, [UserFd.ufd_auth],  *)
(* whose authority rides inside the run's bundle), adapting this file's    *)
(* then-current text at 203 lines; and this lane landed [wp_kshp_peek]'s   *)
(* ~877-line body against the THREE-gname [urun].  Both sides merged       *)
(* textually clean and the file was off-build, so no compiler ever saw the *)
(* union.  It does now, and the whole reconciliation was mechanical: 22    *)
(* [urun]/[wp_uk_*] sites inside peek's statement and body took [γfd].     *)
(* NOTHING ELSE CROSSED -- upstream's adaptation is pure gname threading   *)
(* plus the [Hufd] conjunct in [urun_x0]'s destruct, and peek's body       *)
(* neither destructs the run's bundle nor touches a descriptor.  The       *)
(* union compiles in 20.8 s at the standing three-axiom audit.             *)
(*                                                                        *)
(* (4) THE WALKS, bottom-up, so that every landed lemma is a theorem about *)
(* real code and nothing is stated that is not proved.  This file has ZERO *)
(* [Admitted] and ZERO [Axiom]; its audit is the standing three            *)
(* ([resv_matches], [resv_is_valid], funext), plus the TWO named           *)
(* Hypotheses on the lemmas whose headers name them.  What is landed is    *)
(* recorded in the SH lane's stage-4 row of                                *)
(* claude-notes/projects/fs-syscall-specs.md.                              *)
(*                                                                        *)
(* THE PARSER IS COMPLETE (round 4, 2026-09-01).  All eleven catalogued    *)
(* functions are walked and [wp_kshp_parser] at the foot of the file is    *)
(* the theorem: on a NUL-terminated command line with no symbol byte in    *)
(* it, sh's [parsecmd] returns a node holding exactly that line's tokens,  *)
(* with the line NUL-cut at each token's end, the callee-saved file        *)
(* intact, and at the return address.  Its [Print Assumptions] is the      *)
(* standing three and nothing else; the two Hypotheses are section         *)
(* variables and so appear as its premises.                                *)
(*                                                                        *)
(* THE TWO HYPOTHESES, AND WHY THERE ARE EXACTLY TWO.                      *)
(*   [ushp_malloc_ok]   -- stage 3's allocator, reached through execcmd.   *)
(*   [ushp_clw_text_ok] -- the four-byte load out of the TEXT half, which  *)
(*      nulterminate's jump table needs because .rodata shares the         *)
(*      executable segment's pages.  It IS [UkShRun.wp_uk_clw_text],       *)
(*      built for runcmd's own jump table and merely [Local] to that       *)
(*      file, so the discharge is one [exact] once relocation ask 3 moves  *)
(*      it into [UkRunMem.v].  (Round 3 recorded this as a BASE-encoding   *)
(*      [lw]; the catalog says [c.lw], so the compressed leaf is the one   *)
(*      that is wanted -- and it already exists.)                          *)
(*                                                                        *)
(* THE DEFECT ROUND 4 FOUND AND FIXED, because any later walk can          *)
(* reintroduce it: [peek]'s token table is a STRING LITERAL at every one   *)
(* of its seven call sites, and a literal lives in .rodata, which is the   *)
(* TEXT half.  The landed [wp_kshp_peek] took it as [ustr γd], a DATA-half *)
(* string, and [UserHeap.uheap_ubyte] says a γd byte's page is WRITABLE --  *)
(* so at every real call site that premise CONTRADICTED the layout and no  *)
(* caller could ever have supplied it.  §2c is the fix: [ushp_sstr] is a   *)
(* C string generalised over which half holds it, and both instances are   *)
(* [reflexivity].  Only [strchr] -- the one function that LOADS from the   *)
(* table -- needed a real edit.                                            *)
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

(* ---- THE SYMBOLS TABLE, the same four lemmas at the second table ------ *)
(* [gettoken]'s default arm searches BOTH tables per byte -- whitespace to
   end the token, symbols to end it too -- so the bridge the whitespace
   table got is owed at [symbols] as well, and it is the same four lemmas
   at a seven-entry list.  [ushp_no_symbols] is what makes the second of
   them the one that never fires on a line stage 4 accepts. *)
Definition ushp_sym_f (i : nat) : bv 8 :=
  match i with
  | 0%nat => Z_to_bv 8 60 | 1%nat => Z_to_bv 8 124 | 2%nat => Z_to_bv 8 62
  | 3%nat => Z_to_bv 8 38 | 4%nat => Z_to_bv 8 59 | 5%nat => Z_to_bv 8 40
  | _ => Z_to_bv 8 41
  end.

Lemma ushp_sym_f_nonul (j : nat) : (j < 7)%nat -> ushp_sym_f j <> ubyte0.
Proof.
  intro Hj. destruct j as [| [| [| [| [| [| [| j ]]]]]]];
    vm_compute; discriminate.
Qed.

Lemma ushp_sym_mem (j : nat) : (j < 7)%nat -> ushp_sym_f j ∈ ushp_sym_bytes.
Proof.
  intro Hj. unfold ushp_sym_bytes.
  destruct j as [| [| [| [| [| [| [| j ]]]]]]];
    cbn [fmap list_fmap ushp_sym_f];
    [ apply elem_of_list_here
    | apply elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_here
    | apply elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_further,
            elem_of_list_further, elem_of_list_further, elem_of_list_here
    | lia ].
Qed.

Lemma ushp_sym_mem_inv (c : bv 8) :
  c ∈ ushp_sym_bytes -> exists j : nat, (j < 7)%nat /\ ushp_sym_f j = c.
Proof.
  unfold ushp_sym_bytes. cbn [fmap list_fmap]. intro H.
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
  apply elem_of_cons in H; destruct H as [ -> | H ];
    [ exists 5%nat; split; [ lia | reflexivity ] | ].
  apply elem_of_cons in H; destruct H as [ -> | H ];
    [ exists 6%nat; split; [ lia | reflexivity ] | ].
  apply elem_of_nil in H. destruct H.
Qed.

Lemma ushp_sym_chr_z (c : bv 8) :
  ushp_is_sym c = false ->
  ushp_chr ushp_symbols 7 0%nat ushp_sym_f c = 0.
Proof.
  intro H. apply ushp_chr_miss.
  destruct (ushp_find 7 0%nat ushp_sym_f c) as [ j | ] eqn:E;
    [ exfalso | reflexivity ].
  pose proof (ushp_find_ge 7 0%nat ushp_sym_f c j E) as Hj.
  pose proof (ushp_find_some_val 7 0%nat j ushp_sym_f c E) as Hv.
  unfold ushp_is_sym in H. rewrite bool_decide_eq_false in H. apply H.
  rewrite <- Hv. exact (ushp_sym_mem j ltac:(lia)).
Qed.

Lemma ushp_sym_chr_nz (c : bv 8) :
  ushp_is_sym c = true ->
  exists j : nat, (j < 7)%nat /\
    ushp_chr ushp_symbols 7 0%nat ushp_sym_f c = ushp_symbols + Z.of_nat j.
Proof.
  intro H. unfold ushp_is_sym in H. rewrite bool_decide_eq_true in H.
  destruct (ushp_sym_mem_inv c H) as [ j [ Hj Hv ] ].
  destruct (ushp_find_some_of 7 0%nat j ushp_sym_f c ltac:(lia) Hv)
    as [ k Hk ].
  pose proof (ushp_find_ge 7 0%nat ushp_sym_f c k Hk) as Hkr.
  exists k. split; [ lia | ].
  exact (ushp_chr_hit ushp_symbols 7 0%nat ushp_sym_f c k Hk).
Qed.

(* the SEVEN numeric refutations gettoken's switch turns on: a byte that is
   not in [symbols] is none of the seven values the dispatch chain tests.
   Stated on [bv_unsigned] because that is what the branch compares, the
   [lbu] having zero-extended it. *)
Lemma ushp_nsym_bv (b : bv 8) :
  ushp_is_sym b = false ->
  bv_unsigned b <> 60 /\ bv_unsigned b <> 124 /\ bv_unsigned b <> 62 /\
  bv_unsigned b <> 38 /\ bv_unsigned b <> 59 /\ bv_unsigned b <> 40 /\
  bv_unsigned b <> 41.
Proof.
  intro H. unfold ushp_is_sym in H. rewrite bool_decide_eq_false in H.
  repeat split; intro E; apply H.
  - assert (Eb : b = ushp_sym_f 0%nat)
      by (apply bv_eq; rewrite E; vm_compute; reflexivity).
    rewrite Eb. exact (ushp_sym_mem 0%nat ltac:(lia)).
  - assert (Eb : b = ushp_sym_f 1%nat)
      by (apply bv_eq; rewrite E; vm_compute; reflexivity).
    rewrite Eb. exact (ushp_sym_mem 1%nat ltac:(lia)).
  - assert (Eb : b = ushp_sym_f 2%nat)
      by (apply bv_eq; rewrite E; vm_compute; reflexivity).
    rewrite Eb. exact (ushp_sym_mem 2%nat ltac:(lia)).
  - assert (Eb : b = ushp_sym_f 3%nat)
      by (apply bv_eq; rewrite E; vm_compute; reflexivity).
    rewrite Eb. exact (ushp_sym_mem 3%nat ltac:(lia)).
  - assert (Eb : b = ushp_sym_f 4%nat)
      by (apply bv_eq; rewrite E; vm_compute; reflexivity).
    rewrite Eb. exact (ushp_sym_mem 4%nat ltac:(lia)).
  - assert (Eb : b = ushp_sym_f 5%nat)
      by (apply bv_eq; rewrite E; vm_compute; reflexivity).
    rewrite Eb. exact (ushp_sym_mem 5%nat ltac:(lia)).
  - assert (Eb : b = ushp_sym_f 6%nat)
      by (apply bv_eq; rewrite E; vm_compute; reflexivity).
    rewrite Eb. exact (ushp_sym_mem 6%nat ltac:(lia)).
Qed.

(* the one-step readings of [ushp_toklen] the token scan needs, beside the
   three [ushp_skipws] already has *)
Lemma ushp_toklen_stop (n i : nat) (f : nat -> bv 8) :
  ushp_is_ws (f i) || ushp_is_sym (f i) = true -> ushp_toklen n i f = 0%nat.
Proof.
  intro H. destruct n as [| n ]; cbn; [ reflexivity | rewrite H; reflexivity ].
Qed.

Lemma ushp_toklen_zero (i : nat) (f : nat -> bv 8) :
  ushp_toklen 0 i f = 0%nat.
Proof. reflexivity. Qed.

Lemma ushp_toklen_step (n i : nat) (f : nat -> bv 8) :
  ushp_is_ws (f i) || ushp_is_sym (f i) = false ->
  ushp_toklen (S n) i f = S (ushp_toklen n (S i) f).
Proof. intro H. cbn. rewrite H. reflexivity. Qed.

(* ---- WHAT [parseexec]'s LOOP NEEDS OF THE MODEL, ONCE ----------------- *)
(* Every turn of the argument loop moves the cursor twice for free -- peek
   skips whitespace before the guard, and parseredirs skips it again after
   the token -- so the loop's invariant has to survive a skip.  It does,
   and the reason is that the scan is IDEMPOTENT: it stops either at the
   end of the line or on a non-blank byte, and in both cases a second scan
   from where it stopped moves nothing. *)

Lemma ushp_skipws_end (n i : nat) (f : nat -> bv 8) :
  (ushp_skipws n i f < n)%nat ->
  ushp_is_ws (f (i + ushp_skipws n i f)%nat) = false.
Proof.
  revert i. induction n as [| n IH ]; intros i H.
  - cbn [ushp_skipws] in H. lia.
  - cbn [ushp_skipws] in H |- *. destruct (ushp_is_ws (f i)) eqn:Hw.
    + assert (E : (i + S (ushp_skipws n (S i) f))%nat
                  = (S i + ushp_skipws n (S i) f)%nat) by lia.
      rewrite E. apply IH. lia.
    + rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma ushp_skipws_idem (len off : nat) (f : nat -> bv 8) :
  (off <= len)%nat ->
  ushp_skipws (len - (off + ushp_skipws (len - off) off f))
    (off + ushp_skipws (len - off) off f) f = 0%nat.
Proof.
  intro Hoff.
  destruct (Nat.eq_dec (off + ushp_skipws (len - off) off f) len)
    as [ Hend | Hend ].
  - rewrite Hend Nat.sub_diag. reflexivity.
  - pose proof (ushp_skipws_le (len - off) off f) as Hle.
    apply ushp_skipws_stop. apply ushp_skipws_end. lia.
Qed.

(* the two constructors, at the shape a walk can APPLY -- the [let]s in
   [ushp_tokens]'s own constructors make them unusable by [apply] once the
   cursor has been moved by anything the term does not mention *)
Lemma ushp_tokens_nil' (len i : nat) (f : nat -> bv 8) :
  i = len -> ushp_tokens len f i [].
Proof.
  intros ->. apply UshpTokNil. rewrite Nat.sub_diag.
  cbn [ushp_skipws]. lia.
Qed.

Lemma ushp_tokens_cons' (len : nat) (f : nat -> bv 8) (i n : nat)
    (toks : list (nat * nat)) :
  ushp_skipws (len - i) i f = 0%nat ->
  ushp_toklen (len - i) i f = n ->
  (0 < n)%nat ->
  ushp_tokens len f (i + n)%nat toks ->
  ushp_tokens len f i ((i, (i + n)%nat) :: toks).
Proof.
  intros Hk Hn Hpos Ht.
  assert (E : (i + ushp_skipws (len - i) i f)%nat = i) by (rewrite Hk; lia).
  assert (C := UshpTokCons len f i toks).
  cbv zeta in C. rewrite E in C. rewrite Hn in C.
  exact (C Hpos Ht).
Qed.

(* ...and the two inversions *)
Lemma ushp_tokens_nil_inv (len i : nat) (f : nat -> bv 8) :
  ushp_tokens len f i [] -> (i + ushp_skipws (len - i) i f)%nat = len.
Proof. inversion 1. assumption. Qed.

Lemma ushp_tokens_cons_inv (len i : nat) (f : nat -> bv 8)
    (tk : nat * nat) (rest : list (nat * nat)) :
  ushp_tokens len f i (tk :: rest) ->
  (0 < ushp_toklen (len - (i + ushp_skipws (len - i) i f))
         (i + ushp_skipws (len - i) i f) f)%nat /\
  tk = ((i + ushp_skipws (len - i) i f)%nat,
        (i + ushp_skipws (len - i) i f
         + ushp_toklen (len - (i + ushp_skipws (len - i) i f))
             (i + ushp_skipws (len - i) i f) f)%nat) /\
  ushp_tokens len f
    (i + ushp_skipws (len - i) i f
     + ushp_toklen (len - (i + ushp_skipws (len - i) i f))
         (i + ushp_skipws (len - i) i f) f)%nat rest.
Proof.
  inversion 1 as [ | off toks0 Hn Ht Eoff Etoks ]; subst.
  cbv zeta in *. split; [ assumption | ].
  split; [ reflexivity | assumption ].
Qed.

(* the same inversion with the two derived positions as PARAMETERS, so a
   walk that has already named them gets the facts in its own vocabulary *)
Lemma ushp_tokens_cons_inv' (len i j q : nat) (f : nat -> bv 8)
    (tk : nat * nat) (rest : list (nat * nat)) :
  j = (i + ushp_skipws (len - i) i f)%nat ->
  q = ushp_toklen (len - j) j f ->
  ushp_tokens len f i (tk :: rest) ->
  (0 < q)%nat /\ tk = (j, (j + q)%nat) /\ ushp_tokens len f (j + q)%nat rest.
Proof. intros -> ->. apply ushp_tokens_cons_inv. Qed.

(* two list facts, self-contained so no naming drift bites *)
Lemma ushp_len_app1 {A : Type} (l : list A) (x : A) :
  length (l ++ [x]) = S (length l).
Proof.
  induction l as [| y l IH ]; cbn [length app]; [ reflexivity | ].
  rewrite IH. reflexivity.
Qed.

Lemma ushp_app_cons {A : Type} (l : list A) (x : A) (r : list A) :
  (l ++ [x]) ++ r = l ++ x :: r.
Proof.
  induction l as [| y l IH ]; cbn [app]; [ reflexivity | ].
  rewrite IH. reflexivity.
Qed.

Lemma ushp_len_app_cons {A : Type} (l : list A) (x : A) (r : list A) :
  length (l ++ x :: r) = S (length l + length r).
Proof.
  induction l as [| y l IH ]; cbn [length app]; [ reflexivity | ].
  rewrite IH. reflexivity.
Qed.

Lemma ushp_lookup_app_mid' {A : Type} (l : list A) (x : A) (r : list A) :
  (l ++ x :: r) !! (length l) = Some x.
Proof.
  induction l as [| y l IH ]; cbn [length app]; [ reflexivity | exact IH ].
Qed.

Lemma ushp_lookup_app_next {A : Type} (l : list A) (x y : A) (r : list A) :
  (l ++ x :: y :: r) !! S (length l) = Some y.
Proof.
  induction l as [| z l IH ]; cbn [length app]; [ reflexivity | exact IH ].
Qed.

Lemma ushp_lookup_app_past {A : Type} (l : list A) (x : A) :
  (l ++ [x]) !! S (length l) = None.
Proof.
  induction l as [| y l IH ]; cbn [length app]; [ reflexivity | exact IH ].
Qed.

(* THE SKIP THE LOOP SURVIVES *)
Lemma ushp_tokens_skip (len : nat) (f : nat -> bv 8) (off : nat)
    (toks : list (nat * nat)) :
  (off <= len)%nat ->
  ushp_tokens len f off toks ->
  ushp_tokens len f (off + ushp_skipws (len - off) off f)%nat toks.
Proof.
  intros Hoff H.
  pose proof (ushp_skipws_idem len off f Hoff) as Hk0.
  pose proof (ushp_skipws_le (len - off) off f) as Hle.
  destruct toks as [| tk rest ].
  - apply ushp_tokens_nil'.
    pose proof (ushp_tokens_nil_inv len off f H) as Hnil. lia.
  - destruct (ushp_tokens_cons_inv len off f tk rest H)
      as (Hn & Htk & Hrest).
    subst tk.
    exact (ushp_tokens_cons' len f (off + ushp_skipws (len - off) off f)
             (ushp_toklen (len - (off + ushp_skipws (len - off) off f))
                (off + ushp_skipws (len - off) off f) f) rest
             Hk0 eq_refl Hn Hrest).
Qed.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section UkShParse.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

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
  Local Lemma shpp_nulterminate : ShSyms.nulterminate = 0x7ee.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&H&_&_&_&_&_). exact H. Qed.
  Local Lemma shpp_parseredirs : ShSyms.parseredirs = 0x4ac.
  Proof. destruct shp_syms_pins as (_&_&_&_&H&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shpp_parseexec : ShSyms.parseexec = 0x590.
  Proof. destruct shp_syms_pins as (_&_&_&H&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shpp_parsepipe : ShSyms.parsepipe = 0x682.
  Proof. destruct shp_syms_pins as (_&_&H&_&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shpp_parseline : ShSyms.parseline = 0x6e2.
  Proof. destruct shp_syms_pins as (_&H&_&_&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shpp_parsecmd : ShSyms.parsecmd = 0x86e.
  Proof. destruct shp_syms_pins as (H&_&_&_&_&_&_&_&_&_&_). exact H. Qed.

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
    urun γt γd γs γfd h m pc avail -∗
    ⌜ m !!! Regidx x0_idx = zero_reg ⌝ ∗ urun γt γd γs γfd h m pc avail.
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv)
      "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv.
    iFrame "Hheap Hstk Hufd Hb".
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
  (* §2c A C STRING IN EITHER HALF OF THE HEAP -- AND WHY THE PARSER        *)
  (*      CANNOT BE WALKED WITHOUT IT.                                      *)
  (*                                                                       *)
  (* FOUND WHILE STARTING [parseredirs], AND IT IS A DEFECT IN THE LANDED   *)
  (* CONTRACTS, NOT IN THE CODE.  [peek(ps, es, toks)] is called at seven   *)
  (* sites and EVERY [toks] it is passed is a STRING LITERAL:               *)
  (*                                                                       *)
  (*   parseredirs  "<>"   @0x12f0     parseexec  "("    @0x12f8            *)
  (*   parseexec    "|)&;" @0x1318     parsepipe  "|"    @0x1320            *)
  (*   parseline    "&"    @0x1328     parseline  ";"    @0x1330            *)
  (*   parsecmd     ""     @0x1288                                          *)
  (*                                                                       *)
  (* and all seven sit in .rodata (0x1280..0x13d9), which shares the        *)
  (* EXECUTABLE segment's pages -- the same reason [UCodeShP.shp_rodata]    *)
  (* exists and is a [utext_img] under GAMMA-T.  The landed [wp_kshp_peek]  *)
  (* took its table as [ustr γd dt toks tlen tf], a DATA-half string, and   *)
  (* [UserHeap.uheap_ubyte] says a γd byte's page is WRITABLE.  So at any   *)
  (* of the seven real addresses that premise is not merely unproved: it    *)
  (* CONTRADICTS the layout, and no caller could ever have supplied it.     *)
  (* [wp_kshp_peek] was true and unusable.                                  *)
  (*                                                                       *)
  (* THE FIX IS ONE BOOLEAN, and it is [UkShDiag]'s [shd_str] idiom: a C    *)
  (* string generalised over WHICH HALF holds it.  [ushp_sstr false dq] is  *)
  (* [ustr γd dq] and [ushp_sstr true dq] is [utext_str γt], BOTH BY        *)
  (* [reflexivity] -- the four conjuncts are literally the same -- so the   *)
  (* five landed call sites that pass a γd table (the whitespace and symbol *)
  (* tables at 0x2008 / 0x2000, which really are in .data) change by one    *)
  (* argument and nothing else.  Only [strchr] -- the one function that     *)
  (* LOADS from the table -- needs a real edit, and it is four [lbu] sites. *)
  (*                                                                       *)
  (* RELOCATION ASK: this is [UkShDiag.shd_sb]/[shd_str]/[wp_shd_lbu] a     *)
  (* THIRD time (UkShDiag has it, this file now has it), which is exactly   *)
  (* what ask 3 of the lane report already asks for -- move the family      *)
  (* beside [UserHeap.ustr] and its load beside [UkRunMem.wp_uk_lbu].       *)
  (* ===================================================================== *)

  (* one byte of such a string *)
  Definition ushp_sbq (tx : bool) (dq : dfrac) (a : Z) (b : bv 8) : iProp Σ :=
    (if tx then utext γt a b else ubyteq γd dq a b)%I.

  (* ...and the string, spelled exactly as [UserHeap.ustr] /
     [UserHeap.utext_str] spell it, so both directions are [reflexivity] *)
  Definition ushp_sstr (tx : bool) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) : iProp Σ :=
    (⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝ ∗
     ⌜ Z.of_nat len < 2 ^ 31 ⌝ ∗
     ([∗ list] j ∈ seq 0 len, ushp_sbq tx dq (a + Z.of_nat j) (f j)) ∗
     ushp_sbq tx dq (a + Z.of_nat len) ubyte0)%I.

  Lemma ushp_sstr_data (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    ushp_sstr false dq a len f = ustr γd dq a len f.
  Proof. reflexivity. Qed.

  Lemma ushp_sstr_text (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    ushp_sstr true dq a len f = utext_str γt a len f.
  Proof. reflexivity. Qed.

  (* the three accessors [strchr]'s walk uses, at either half.  The
     give-back wand is kept even in the text case (where the byte is
     persistent and nothing has to come back) so that ONE script serves
     both halves. *)
  Lemma ushp_sstr_nonul (tx : bool) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    ushp_sstr tx dq a len f -∗ ⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝.
  Proof. iIntros "(%H & _ & _ & _)". iPureIntro. exact H. Qed.

  Lemma ushp_sstr_len (tx : bool) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    ushp_sstr tx dq a len f -∗ ⌜ Z.of_nat len < 2 ^ 31 ⌝.
  Proof. iIntros "(_ & %H & _ & _)". iPureIntro. exact H. Qed.

  Lemma ushp_sstr_byte (tx : bool) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) (j : nat) :
    (j < len)%nat ->
    ushp_sstr tx dq a len f -∗
      ushp_sbq tx dq (a + Z.of_nat j) (f j) ∗
      (ushp_sbq tx dq (a + Z.of_nat j) (f j) -∗ ushp_sstr tx dq a len f).
  Proof.
    intros Hj. iIntros "(#Hne & #Hlen & Hbs & Hnul)".
    iDestruct (big_sepL_lookup_acc _ _ j j with "Hbs") as "[Hb Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hj ] | ].
    iFrame "Hb". iIntros "Hb".
    rewrite /ushp_sstr. iFrame "Hne Hlen Hnul". iApply ("Hcl" with "Hb").
  Qed.

  Lemma ushp_sstr_nul (tx : bool) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    ushp_sstr tx dq a len f -∗
      ushp_sbq tx dq (a + Z.of_nat len) ubyte0 ∗
      (ushp_sbq tx dq (a + Z.of_nat len) ubyte0 -∗ ushp_sstr tx dq a len f).
  Proof.
    iIntros "(#Hne & #Hlen & Hbs & Hnul)". iFrame "Hnul". iIntros "Hnul".
    rewrite /ushp_sstr. iFrame "Hne Hlen Hbs Hnul".
  Qed.

  (* THE ONE LOAD, at either half.  [wp_uk_lbu] and [wp_uk_lbu_text] have
     the same premises and the same register effect; they differ only in
     which resource they consume, and the text one does not consume it. *)
  Local Lemma wp_ushp_lbu (tx : bool) (dq : dfrac) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (a : Z)
      (b0 : mword 8) (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    ushp_sbq tx dq a b0 -∗
    urun γt γd γs γfd h m pc avail -∗
    (ushp_sbq tx dq a b0 -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx rd := regval_into_reg (zero_extend' 64 b0)]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hrd. iIntros "#Hi Hb Hrun Hcont".
    destruct tx.
    - rewrite /ushp_sbq. iDestruct "Hb" as "#Hb".
      iApply (wp_uk_lbu_text γt γd γs γfd h m pc imm rs1 rd a b0 avail
                Hns Ha Hrd with "Hi Hb Hrun").
      iIntros (h') "Hrun". iApply ("Hcont" with "Hb Hrun").
    - iApply (wp_uk_lbu γt γd γs γfd h m pc imm rs1 rd dq a b0 avail
                Hns Ha Hrd with "Hi Hb Hrun").
      iIntros "Hb" (h') "Hrun". iApply ("Hcont" with "Hb Hrun").
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

  (* ...and the same with the DESTINATION named, so a walk never carries a
     [mword_of_int (0x420 + 4)] a later [rewrite] then fails to match. *)
  Local Lemma ushp_pc_step' (x d y : Z) :
    x + d = y ->
    add_vec_int (mword_of_int x : mword 64) d = mword_of_int y.
  Proof. intro H. rewrite ushp_pc_step. f_equal. exact H. Qed.


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
    urun γt γd γs γfd h m (mword_of_int p) nn -∗
    (∀ (h' : CpuId) (v : mword 64),
       urun γt γd γs γfd h' (<[Regidx s0_idx := regval_into_reg v]> m)
         (mword_of_int (p + 2)) nn -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hi Hrun Hcont".
    iApply (wp_uk_caddi4spn γt γd γs γfd h m (mword_of_int p)
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
    urun γt γd γs γfd h m (mword_of_int p0) (2 + nn) -∗
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
       urun γt γd γs γfd h' m' (mword_of_int p4) nn -∗
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
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int p0)
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
    iApply (wp_uk_csdsp γt γd γs γfd h1 m1 (mword_of_int (p0 + 2))
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 nn
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "Hi1 Hw8 Hrun").
    iIntros "Hw8".
    rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    rewrite (ushp_pc_step (p0 + 2) 2). iIntros (h2) "Hrun".
    (* ---- p2  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h2 m1 (mword_of_int (p0 + 2 + 2))
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 nn
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "Hi2 Hw0 Hrun").
    iIntros "Hw0".
    rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    rewrite (ushp_pc_step (p0 + 2 + 2) 2). iIntros (h3) "Hrun".
    (* ---- p3  c.addi4spn s0,sp,16 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 m1 (mword_of_int (p0 + 2 + 2 + 2))
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
    urun γt γd γs γfd h me (mword_of_int q0) nn -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ forall q : mword 5,
           Regidx q <> Regidx ra_idx -> Regidx q <> Regidx s0_idx ->
           Regidx q <> Regidx csp_rs1 ->
           m' !!! Regidx q = me !!! Regidx q ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc vra) (2 + nn) -∗
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
    iApply (wp_uk_cldsp γt γd γs γfd h me (mword_of_int q0)
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
    iApply (wp_uk_cldsp γt γd γs γfd h1 e1 (mword_of_int (q0 + 2))
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
    iApply (wp_uk_caddi_sp_up γt γd γs γfd h2 e2 (mword_of_int (q0 + 2 + 2))
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
    iApply (wp_uk_cjr γt γd γs γfd h3 e3 (mword_of_int (q0 + 2 + 2 + 2)) ra_idx
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
  Local Lemma wp_kshp_strchr_loop (tx : bool) (dq : dfrac) (s : Z) (len : nat)
      (f : nat -> bv 8) (c : bv 8) (nn : nat) :
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s -> s + Z.of_nat len < Z64 ->
    mc !!! Regidx a0_idx = mword_of_int (s + Z.of_nat j) ->
    mc !!! Regidx a5_idx = mword_of_int (bv_unsigned (f j)) ->
    mc !!! Regidx a1_idx = mword_of_int (bv_unsigned c) ->
    shp_code γt -∗
    ushp_sstr tx dq s len f -∗
    urun γt γd γs γfd h mc (mword_of_int 0xa90) nn -∗
    (ushp_sstr tx dq s len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5,
             Regidx q <> Regidx a0_idx -> Regidx q <> Regidx a5_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx a0_idx
             = mword_of_int (ushp_chr s (len - j) j f c) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0xa9e) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Ha0 Ha5 Ha1;
      iIntros "#Hcode Hstr Hrun Hcont"; [ lia | ].
    iDestruct (ushp_sstr_nonul with "Hstr") as %Hne.
    destruct (decide (f j = c)) as [ Hhit | Hhit ].
    { (* ---- 0xa90  beq a1,a5 -- TAKEN: this byte IS the one ---- *)
      assert (Htk : true = uv_btaken BEQ (mc !!! Regidx a1_idx)
                             (mc !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha1 Ha5.
        rewrite (ushp_zext_eq (f j) c). symmetry.
        exact (bool_decide_eq_true_2 _ Hhit). }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0xa90)
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
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0xa90)
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
    iApply (wp_uk_caddi γt γd γs γfd h1 mc (mword_of_int 0xa94)
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
      iDestruct (ushp_sstr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_ushp_lbu tx dq h2 m1 (mword_of_int 0xa96)
                (mword_of_int 0 : mword 12) a0_idx a5_idx
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
      iApply (wp_uk_cbnez γt γd γs γfd h3 m2 (mword_of_int 0xa9a)
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
      iApply (wp_uk_cli γt γd γs γfd h4 m2 (mword_of_int 0xa9c)
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
    iDestruct (ushp_sstr_byte tx dq s len f (S j) Hj1 with "Hstr") as "[Hb Hcl]".
    iApply (wp_ushp_lbu tx dq h2 m1 (mword_of_int 0xa96)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
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
    iApply (wp_uk_cbnez γt γd γs γfd h3 m2 (mword_of_int 0xa9a)
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
  Lemma wp_kshp_strchr (h : CpuId) (m : regfile) (tx : bool) (dq : dfrac)
      (s : Z)
      (len : nat) (f : nat -> bv 8) (c : bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s ->
    m !!! Regidx a1_idx = mword_of_int (bv_unsigned c) ->
    0 <= s -> s + Z.of_nat len < Z64 ->
    shp_code γt -∗
    ushp_sstr tx dq s len f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.strchr) (2 + nn) -∗
    (ushp_sstr tx dq s len f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int (ushp_chr s len 0%nat f c) ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hs0 Hs64. iIntros "#Hcode Hstr Hrun Hcont".
    rewrite shpp_strchr.
    iDestruct (ushp_sstr_nonul with "Hstr") as %Hne.
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
      iDestruct (ushp_sstr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_ushp_lbu tx dq h4 m2 (mword_of_int 0xa8a)
                (mword_of_int 0 : mword 12) a0_idx a5_idx
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
      iApply (wp_uk_cbeqz γt γd γs γfd h5 m3 (mword_of_int 0xa8e)
                (mword_of_int 12 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0xaa6) nn
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_a8e with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0xaa6  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs γfd h6 m3 (mword_of_int 0xaa6)
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
      iApply (wp_uk_cj γt γd γs γfd h7 m4 (mword_of_int 0xaa8)
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
    iDestruct (ushp_sstr_byte tx dq s len f 0%nat H0len with "Hstr") as "[Hb Hcl]".
    iApply (wp_ushp_lbu tx dq h4 m2 (mword_of_int 0xa8a)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
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
    iApply (wp_uk_cbeqz γt γd γs γfd h5 m3 (mword_of_int 0xa8e)
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
    iApply (wp_kshp_strchr_loop tx dq s len f c nn (len - 0)%nat 0%nat h6 m3
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
    urun γt γd γs γfd h mc (mword_of_int 0xa42) nn -∗
    (ustr γd dq s len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5,
             Regidx q <> Regidx a3_idx -> Regidx q <> Regidx a4_idx ->
             Regidx q <> Regidx a5_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx a3_idx = mword_of_int (s + Z.of_nat len) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0xa4c) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros k h mc Hr Hk Hs0 Hs64 Ha5;
      iIntros "#Hcode Hstr Hrun Hcont"; [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- 0xa42  c.mv a3,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h mc (mword_of_int 0xa42)
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
    iApply (wp_uk_caddi γt γd γs γfd h1 m1 (mword_of_int 0xa44)
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
      iApply (wp_uk_lbu γt γd γs γfd h2 m2 (mword_of_int 0xa46)
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
      iApply (wp_uk_cbnez γt γd γs γfd h3 m3 (mword_of_int 0xa4a)
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
    iApply (wp_uk_lbu γt γd γs γfd h2 m2 (mword_of_int 0xa46)
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
    iApply (wp_uk_cbnez γt γd γs γfd h3 m3 (mword_of_int 0xa4a)
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
    urun γt γd γs γfd h m (mword_of_int ShSyms.strlen) (2 + nn) -∗
    (ustr γd dq s len f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int (Z.of_nat len) ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
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
      iApply (wp_uk_lbu γt γd γs γfd h4 m2 (mword_of_int 0xa38)
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
      iApply (wp_uk_cbeqz γt γd γs γfd h5 m3 (mword_of_int 0xa3c)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0xa58) nn
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_a3c with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0xa58  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs γfd h6 m3 (mword_of_int 0xa58)
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
      iApply (wp_uk_cj γt γd γs γfd h7 m4 (mword_of_int 0xa5a)
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
    iApply (wp_uk_lbu γt γd γs γfd h4 m2 (mword_of_int 0xa38)
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
    iApply (wp_uk_cbeqz γt γd γs γfd h5 m3 (mword_of_int 0xa3c)
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
    iApply (wp_uk_addi γt γd γs γfd h6 m3 (mword_of_int 0xa3e)
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
    iApply (wp_uk_subw γt γd γs γfd h8 mc' (mword_of_int 0xa4c)
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

  (* ...and a SLOT of an 8-aligned node likewise: the argv and eargv
     vectors both start at a multiple of eight from the node's base, so
     every store into them is aligned by the node's own alignment. *)
  Local Lemma ushp_slot_al8 (p c : Z) (k : nat) :
    p mod 8 = 0 -> (p + 8 * c + 8 * Z.of_nat k) mod 8 = 0.
  Proof.
    intro Hp.
    assert (Hm : (8 * (c + Z.of_nat k)) mod 8 = 0)
      by (rewrite Z.mul_comm; apply Z_mod_mult).
    replace (p + 8 * c + 8 * Z.of_nat k)
      with (p + 8 * (c + Z.of_nat k)) by lia.
    rewrite Zplus_mod Hp Hm. reflexivity.
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
    urun γt γd γs γfd h m (mword_of_int (pcs 0%nat)) nn -∗
    (([∗ list] i ↦ _ ∈ rs, uword γd (ad i) (vals i)) -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h' m (mword_of_int (pcs (length rs))) nn -∗
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
      iApply (wp_uk_csdsp γt γd γs γfd h m (mword_of_int (pcs 0%nat))
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

  (* ...and the ONE entry a return address is read back out of.  gcc spills
     [ra] first in every frame in this catalog, so the epilogue's [c.jr ra]
     reads slot 0 -- provided no LATER spill is [ra] too, which is the
     second premise and is a [vm_compute] at any concrete list. *)
  Lemma ushp_spillback_ra (rs : list (mword 5 * mword 6)) (u0 : mword 6)
      (vals : nat -> mword 64) (me : regfile) :
    rs !! 0%nat = Some (ra_idx, u0) ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! (S i) = Some (r, u) -> Regidx ra_idx <> Regidx r) ->
    ushp_spillback rs vals me !!! Regidx ra_idx = vals 0%nat.
  Proof.
    destruct rs as [| ru0 rs' ]; intros Hra0 Htl; [ discriminate | ].
    cbn in Hra0. injection Hra0 as Hru0. subst ru0.
    cbn [ushp_spillback fst].
    rewrite (ushp_spillback_ne rs' (fun i : nat => vals (S i))
               (<[Regidx ra_idx := regval_into_reg (vals 0%nat)]> me) ra_idx
               ltac:(intros i r u Hi; exact (Htl i r u Hi))).
    exact (upd_eq me (Regidx ra_idx) (regval_into_reg (vals 0%nat))).
  Qed.

  (* THE READ-BACK, ONCE.  A restore run leaves an insert tower, and every
     landed contract then has to say [ucallee_saved m m'] about it.  peek
     paid ~90 lines peeling that tower one [Z.eq_dec] per spill; this is
     the same argument by INDUCTION on the list, so a call site owes only
     the two facts it actually knows -- what the run spilled, and that the
     body left the OTHER callee-saved registers alone.

     [ushp_spillback_eq] is the peel: a register the list writes gets the
     value the list carries, and one it does not gets whatever the body
     left -- and the two premises are exactly those two cases, so a
     DUPLICATE in the list needs no argument (a later entry simply
     overrides an earlier one, and both are asked for the same value). *)
  Lemma ushp_spillback_eq (rs : list (mword 5 * mword 6))
      (vals : nat -> mword 64) (me : regfile) (w : mword 64) (r : mword 5) :
    ((forall (i : nat) (r' : mword 5) (u : mword 6),
        rs !! i = Some (r', u) -> Regidx r' <> Regidx r) ->
     me !!! Regidx r = w) ->
    (forall (i : nat) (r' : mword 5) (u : mword 6),
       rs !! i = Some (r', u) -> Regidx r' = Regidx r -> vals i = w) ->
    ushp_spillback rs vals me !!! Regidx r = w.
  Proof.
    revert vals me. induction rs as [| ru rs' IH ]; intros vals me Hmiss Hhit.
    - cbn [ushp_spillback]. apply Hmiss.
      intros i r' u Hi. rewrite lookup_nil in Hi. discriminate.
    - cbn [ushp_spillback]. apply IH.
      + intros Hmiss'.
        destruct (decide (Regidx (fst ru) = Regidx r)) as [ E | E ].
        * rewrite <- E.
          rewrite (upd_eq me (Regidx (fst ru)) (regval_into_reg (vals 0%nat))).
          exact (Hhit 0%nat (fst ru) (snd ru)
                   ltac:(destruct ru; reflexivity) E).
        * rewrite (upd_ne me (Regidx (fst ru)) (Regidx r) _
                     ltac:(intro He; exact (E (eq_sym He)))).
          apply Hmiss. intros i r' u Hi.
          destruct i as [| i ]; cbn in Hi.
          { injection Hi as Hru. subst ru. exact E. }
          exact (Hmiss' i r' u Hi).
      + intros i r' u Hi He. exact (Hhit (S i) r' u Hi He).
  Qed.

  (* ...and the contract's own conjunct, assembled from it. *)
  Lemma ushp_frame_cs (rs : list (mword 5 * mword 6))
      (vals : nat -> mword 64) (m me : regfile) (sp0 : mword 64) :
    m !!! Regidx csp_rs1 = sp0 ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! i = Some (r, u) -> vals i = m !!! Regidx r) ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       Regidx r <> Regidx csp_rs1 ->
       (forall (i : nat) (r' : mword 5) (u : mword 6),
          rs !! i = Some (r', u) -> Regidx r <> Regidx r') ->
       me !!! Regidx r = m !!! Regidx r) ->
    ucallee_saved m
      (<[Regidx csp_rs1 := regval_into_reg sp0]> (ushp_spillback rs vals me)).
  Proof.
    intros Hsp Hvals Hkeep r Hr.
    destruct (decide (Regidx r = Regidx csp_rs1)) as [ E | E ].
    - rewrite E.
      rewrite (upd_eq _ (Regidx csp_rs1) (regval_into_reg sp0)).
      exact (eq_sym Hsp).
    - rewrite (upd_ne _ (Regidx csp_rs1) (Regidx r) _ E).
      apply ushp_spillback_eq.
      + intro Hmiss. apply (Hkeep r Hr E).
        intros i r' u Hi He. exact (Hmiss i r' u Hi (eq_sym He)).
      + intros i r' u Hi He. rewrite (Hvals i r' u Hi) He. reflexivity.
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
    urun γt γd γs γfd h m (mword_of_int (pcs 0%nat)) nn -∗
    (([∗ list] i ↦ _ ∈ rs, uword γd (ad i) (vals i)) -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h' (ushp_spillback rs vals m)
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
      iApply (wp_uk_cldsp γt γd γs γfd h m (mword_of_int (pcs 0%nat))
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
  (* §4c THE WHOLE PROLOGUE AND THE WHOLE EPILOGUE, AT ANY FRAME SIZE.      *)
  (*                                                                       *)
  (* §4b generalised the two SPILL RUNS.  peek and gettoken still wrote the *)
  (* push, the frame split, the [c.addi4spn] and their three mirrors out by *)
  (* hand -- about 140 lines apiece, and the five parser functions would    *)
  (* have paid it five more times.  These two lemmas are that boilerplate   *)
  (* once, over [k] (the frame in words) and the spill list.                *)
  (*                                                                       *)
  (* ALL FIVE PARSER FUNCTIONS PUSH AND POP WITH [c.addi16sp], so unlike    *)
  (* §4b's note there is no two-armed premise to write: [imm] is a          *)
  (* parameter and the ONE pure fact about it is the [sign_extend'] the     *)
  (* leaf wants, at the call site's own literal.                            *)
  (*                                                                       *)
  (* WHAT A CALL SITE OWES is the §4b bargain again -- pure facts at        *)
  (* CONCRETE numbers: the pcs step by two, and each spill's [c.sdsp]       *)
  (* immediate is the slot the frame split hands out.  Nothing here does    *)
  (* index arithmetic; [pcs] and the offsets are functions of the spill     *)
  (* index and the step passes their tails.                                 *)
  (* ===================================================================== *)

  Local Lemma wp_kshp_frame_pro (k n : nat) (rs : list (mword 5 * mword 6))
      (p0 : Z) (pcs : nat -> Z) (imm : mword 6) (nz : mword 8)
      (vals : nat -> mword 64) (nn : nat) (h : CpuId) (m : regfile) :
    (length rs + n)%nat = k ->
    (sign_extend' 64 (caddi16sp_imm imm) : mword 64)
      = mword_of_int (- (8 * Z.of_nat k)) ->
    pcs 0%nat = p0 + 2 ->
    (forall i : nat, (i < length rs)%nat -> pcs (S i) = pcs i + 2) ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! i = Some (r, u) ->
       uoff_sdsp u = 8 * Z.of_nat k - 8 * (Z.of_nat i + 1) /\
       Regidx r <> Regidx csp_rs1 /\ vals i = m !!! Regidx r) ->
    uinstr_is γt (mword_of_int p0) true (C_ADDI16SP imm) -∗
    ([∗ list] i ↦ ru ∈ rs,
       uinstr_is γt (mword_of_int (pcs i)) true
         (C_SDSP (snd ru, Regidx (fst ru)))) -∗
    uinstr_is γt (mword_of_int (pcs (length rs))) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), nz)) -∗
    urun γt γd γs γfd h m (mword_of_int p0) (k + nn) -∗
    (∀ (h' : CpuId) (v : mword 64),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 8 * Z.of_nat k <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ uint (m !!! Regidx csp_rs1) < Z64 ⌝ -∗
       ([∗ list] i ↦ _ ∈ rs,
          uword γd (uint (m !!! Regidx csp_rs1) - 8 * (Z.of_nat i + 1))
            (vals i)) -∗
       ustack γd
         (mword_of_int
            (uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat (length rs)))
         n -∗
       urun γt γd γs γfd h'
         (<[Regidx s0_idx := regval_into_reg v]>
            (<[Regidx csp_rs1
               := regval_into_reg
                    (add_vec_int (m !!! Regidx csp_rs1)
                       (- (8 * Z.of_nat k)))]> m))
         (mword_of_int (pcs (length rs) + 2)) nn -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ek Himm Hp0 Hpc Hoff.
    iIntros "#Hi0 #Hisp #Hifp Hrun Hcont".
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 8 * Z.of_nat k <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    (* ---- the push ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int p0) imm k nn
              Himm with "Hi0 Hrun").
    rewrite (ushp_pc_step' p0 2 (pcs 0%nat) ltac:(lia)).
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat k))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hspu : uint spn = uint sp0 - 8 * Z.of_nat k).
    { unfold spn. rewrite !uint_unsigned.
      exact (uv_avi_neg sp0 (8 * Z.of_nat k) ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (spl := (mword_of_int (uint sp0 - 8 * Z.of_nat (length rs))
                 : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 8 * Z.of_nat (length rs)).
    { unfold spl. apply uint_moi.
      assert (H8 : 8 * Z.of_nat (length rs) <= 8 * Z.of_nat k) by lia. lia. }
    iDestruct (ushp_frame_split sp0 spl n rs Hsplu
                 with "[Hstk]") as "[Hsl Hloc]"; [ rewrite Ek; iExact "Hstk" | ].
    (* ---- the spills ---- *)
    iApply (wp_kshp_spill spn nn rs pcs
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1 Hpc
              ltac:(intros i r u Hi;
                    destruct (Hoff i r u Hi) as [ Hu [ Hnsp Hv ] ];
                    split;
                    [ rewrite Hspu Hu; lia
                    | split;
                      [ exact (ushp_slot_al (uint sp0) i Hal8)
                      | rewrite Hv;
                        exact (eq_sym
                                 (upd_ne m (Regidx csp_rs1) (Regidx r) _
                                    Hnsp)) ] ])
              with "Hisp Hsl Hrun").
    iIntros "Hsl" (h2) "Hrun".
    (* ---- the frame pointer ---- *)
    iApply (wp_kshp_fp h2 m1 (pcs (length rs)) nz nn with "Hifp Hrun").
    iIntros (h3 v) "Hrun".
    iApply ("Hcont" $! h3 v with "[] [] [] Hsl Hloc Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro. lia.
  Qed.

  (* ...and its mirror: the restores, the pop and the [c.jr ra]. *)
  Local Lemma wp_kshp_frame_epi (k n : nat) (rs : list (mword 5 * mword 6))
      (u0 : mword 6) (pcs : nat -> Z) (imm : mword 6)
      (sp0 spl : mword 64) (vals : nat -> mword 64) (nn : nat)
      (h : CpuId) (me : regfile) :
    (length rs + n)%nat = k ->
    uint sp0 mod 8 = 0 -> 8 * Z.of_nat k <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 8 * Z.of_nat (length rs) ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat k)) ->
    (sign_extend' 64 (caddi16sp_imm imm) : mword 64)
      = mword_of_int (8 * Z.of_nat k) ->
    (forall i : nat, (i < length rs)%nat -> pcs (S i) = pcs i + 2) ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! i = Some (r, u) ->
       uoff_sdsp u = 8 * Z.of_nat k - 8 * (Z.of_nat i + 1) /\
       unot_sp r /\ uint r <> 0) ->
    rs !! 0%nat = Some (ra_idx, u0) ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! (S i) = Some (r, u) -> Regidx ra_idx <> Regidx r) ->
    shp_code γt -∗
    ([∗ list] i ↦ ru ∈ rs,
       uinstr_is γt (mword_of_int (pcs i)) true
         (C_LDSP (snd ru, Regidx (fst ru)))) -∗
    uinstr_is γt (mword_of_int (pcs (length rs))) true (C_ADDI16SP imm) -∗
    uinstr_is γt (mword_of_int (pcs (length rs) + 2)) true
      (C_JR (Regidx ra_idx)) -∗
    ([∗ list] i ↦ _ ∈ rs,
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl n -∗
    urun γt γd γs γfd h me (mword_of_int (pcs 0%nat)) nn -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]> (ushp_spillback rs vals me))
         (ret_pc (vals 0%nat)) (k + nn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ek Hal8 Hlo Hhi Hsplu Hsp Himm Hpc Hoff Hra0 Hratl.
    iIntros "#Hcode #Hild #Hipop #Hijr Hsl Hloc Hrun Hcont".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat k))).
    assert (Hspu : uint spn = uint sp0 - 8 * Z.of_nat k).
    { unfold spn. rewrite !uint_unsigned.
      exact (uv_avi_neg sp0 (8 * Z.of_nat k) ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    (* ---- the restores ---- *)
    iApply (wp_kshp_restore spn nn rs pcs
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h me
              Hsp Hpc
              ltac:(intros i r u Hi;
                    destruct (Hoff i r u Hi) as [ Hu [ Hnsp Hnz ] ];
                    split;
                    [ rewrite Hspu Hu; lia
                    | split;
                      [ exact (ushp_slot_al (uint sp0) i Hal8)
                      | split; [ exact Hnsp | exact Hnz ] ] ])
              with "Hild Hsl Hrun").
    iIntros "Hsl" (h1) "Hrun".
    set (mr := ushp_spillback rs vals me).
    assert (Hspr : mr !!! Regidx csp_rs1 = spn).
    { rewrite /mr (ushp_spillback_ne rs vals me csp_rs1
                     ltac:(intros i r u Hi;
                           exact (proj1 (proj2 (Hoff i r u Hi))))).
      exact Hsp. }
    assert (Hrar : mr !!! Regidx ra_idx = vals 0%nat)
      by exact (ushp_spillback_ra rs u0 vals me Hra0 Hratl).
    assert (Hup : add_vec_int spn (8 * Z.of_nat k) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat k) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    (* ---- the pop ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h1 mr
              (mword_of_int (pcs (length rs))) imm k nn Himm
              with "Hipop [Hsl Hloc] Hrun").
    { rewrite Hspr Hup.
      iDestruct (ushp_frame_join sp0 spl n rs vals Hsplu with "Hsl Hloc")
        as "H".
      rewrite Ek. iExact "H". }
    rewrite Hspr Hup (ushp_pc_step (pcs (length rs)) 2).
    iIntros (h2) "Hrun".
    (* ---- the [c.jr ra] ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h2
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mr)
              (mword_of_int (pcs (length rs) + 2)) ra_idx
              (ret_pc (vals 0%nat)) (k + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mr (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrar; reflexivity)
              with "Hijr Hrun").
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hrun").
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
  (* §5b THE NODE WHILE IT IS BEING FILLED.                                 *)
  (*                                                                       *)
  (* [ushp_exec_at] is the node as stages 5-6 read it, and it FORGETS what  *)
  (* is above the NULL cap -- slot [i > |toks|] is an unconstrained cell.   *)
  (* That is the right reading of a finished node and the WRONG loop        *)
  (* invariant: [parseexec] writes slot [argc] and then needs slot          *)
  (* [argc + 1] to be the new cap, which an unconstrained cell cannot       *)
  (* become.  So the loop carries [ushp_exec_pre], which says the truth --  *)
  (* [memset] zeroed all eighty bytes and the loop has only written the     *)
  (* slots below [argc], so every slot at or above it is still ZERO -- and  *)
  (* [ushp_exec_pre_at] is the one-way door to the published form.          *)
  (* ===================================================================== *)

  Definition ushp_slot0 (s0 base : Z) (toks : list (nat * nat))
      (sel : nat * nat -> nat) (i : nat) : iProp Σ :=
    match toks !! i with
    | Some tk =>
        uword γd (base + 8 * Z.of_nat i)
          (mword_of_int (s0 + Z.of_nat (sel tk)))
    | None => uword γd (base + 8 * Z.of_nat i) (mword_of_int 0)
    end.

  Definition ushp_exec_pre (s0 p : Z) (toks : list (nat * nat)) : iProp Σ :=
    (⌜ (length toks < 10)%nat ⌝ ∗ ⌜ 0 < p ⌝ ∗ ⌜ p mod 8 = 0 ⌝ ∗
     ushp_type_at p (UshpExec toks) ∗
     ([∗ list] i ∈ seq 0 10, ushp_slot0 s0 (p + 8) toks fst i) ∗
     ([∗ list] i ∈ seq 0 10, ushp_slot0 s0 (p + 88) toks snd i))%I.

  Local Lemma ushp_slots_weaken (s0 base : Z) (toks : list (nat * nat))
      (sel : nat * nat -> nat) :
    ([∗ list] i ∈ seq 0 10, ushp_slot0 s0 base toks sel i) -∗
    ([∗ list] i ∈ seq 0 10, ushp_slot  s0 base toks sel i).
  Proof.
    iIntros "H". iApply (big_sepL_mono with "H").
    intros k y Hy. apply lookup_seq in Hy as [ -> Hlt ].
    rewrite Nat.add_0_l /ushp_slot0 /ushp_slot.
    destruct (toks !! k) as [ tk | ] eqn:Htk; [ iIntros "$" | ].
    destruct (bool_decide (k = length toks)); [ iIntros "$" | ].
    iIntros "H". iExists (mword_of_int 0). iExact "H".
  Qed.

  Lemma ushp_exec_pre_at (s0 p : Z) (toks : list (nat * nat)) :
    ushp_exec_pre s0 p toks -∗ ushp_exec_at s0 p toks.
  Proof.
    rewrite /ushp_exec_pre /ushp_exec_at.
    iIntros "(%H1 & %H2 & %H3 & Hty & Hav & Hev)".
    iSplitR; [ iPureIntro; exact H1 | ].
    iSplitR; [ iPureIntro; exact H2 | ].
    iSplitR; [ iPureIntro; exact H3 | ].
    iFrame "Hty".
    iSplitL "Hav"; [ iApply (ushp_slots_weaken with "Hav")
                   | iApply (ushp_slots_weaken with "Hev") ].
  Qed.

  Lemma ushp_exec_pre_addr (s0 p : Z) (toks : list (nat * nat)) :
    ushp_exec_pre s0 p toks -∗ ⌜ 0 < p /\ p mod 8 = 0 ⌝.
  Proof.
    rewrite /ushp_exec_pre. iIntros "(_ & %Hp & %Hal & _)".
    iPureIntro. exact (conj Hp Hal).
  Qed.

  (* the FRESH node's ten slots, all of them the zero the memset left *)
  Local Lemma ushp_slots_nil0 (t0 base : Z) (sel : nat * nat -> nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < 80)%nat -> f j = ubyte0) ->
    ubytes γd base 80 f -∗
    [∗ list] i ∈ seq 0 10, ushp_slot0 t0 base [] sel i.
  Proof.
    intros Hf. iIntros "Hb".
    iDestruct (ushp_ubytes_ext base 80 f (fun _ : nat => ubyte0) Hf
                 with "Hb") as "Hb".
    iDestruct (ushp_peel0 base (base + 8) 8 72 ltac:(lia) with "Hb")
      as "[H0 Hb]".
    iDestruct (ushp_peel0 (base + 8) (base + 16) 8 64 ltac:(lia) with "Hb")
      as "[H1 Hb]".
    iDestruct (ushp_peel0 (base + 16) (base + 24) 8 56 ltac:(lia) with "Hb")
      as "[H2 Hb]".
    iDestruct (ushp_peel0 (base + 24) (base + 32) 8 48 ltac:(lia) with "Hb")
      as "[H3 Hb]".
    iDestruct (ushp_peel0 (base + 32) (base + 40) 8 40 ltac:(lia) with "Hb")
      as "[H4 Hb]".
    iDestruct (ushp_peel0 (base + 40) (base + 48) 8 32 ltac:(lia) with "Hb")
      as "[H5 Hb]".
    iDestruct (ushp_peel0 (base + 48) (base + 56) 8 24 ltac:(lia) with "Hb")
      as "[H6 Hb]".
    iDestruct (ushp_peel0 (base + 56) (base + 64) 8 16 ltac:(lia) with "Hb")
      as "[H7 Hb]".
    iDestruct (ushp_peel0 (base + 64) (base + 72) 8 8 ltac:(lia) with "Hb")
      as "[H8 Hb]".
    rewrite /ushp_slot0 /=.
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
      iApply (ushp_ubytes_ext base 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H0").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H1".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 8) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H1").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H2".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 16) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H2").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H3".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 24) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H3").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H4".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 32) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H4").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H5".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 40) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H5").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H6".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 48) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H6").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H7".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 56) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H7").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "H8".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 64) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "H8").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iSplitL "Hb"; [ | done ].
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (base + 72) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hb").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
  Qed.

  (* [(done ++ [tk]) !! y] is [done !! y] anywhere but at the new slot *)
  Local Lemma ushp_lookup_app_ne (done : list (nat * nat)) (tk : nat * nat)
      (y : nat) :
    y <> length done -> (done ++ [tk]) !! y = done !! y.
  Proof.
    intro Hy. destruct (Nat.lt_ge_cases y (length done)) as [ Hlt | Hge ].
    - apply lookup_app_l. exact Hlt.
    - assert (Hla : (done ++ [tk]) !! y = [tk] !! (y - length done)%nat)
        by (apply lookup_app_r; lia).
      rewrite Hla (lookup_ge_None_2 done y Hge).
      remember (y - length done)%nat as d eqn:Hd.
      destruct d as [| d' ]; [ exfalso; lia | reflexivity ].
  Qed.

  Local Lemma ushp_lookup_app_mid (done : list (nat * nat)) (tk : nat * nat) :
    (done ++ [tk]) !! (length done) = Some tk.
  Proof.
    assert (Hla : (done ++ [tk]) !! (length done)
                  = [tk] !! (length done - length done)%nat)
      by (apply lookup_app_r; lia).
    rewrite Hla.
    assert (Hz : (length done - length done)%nat = 0%nat) by lia.
    rewrite Hz. reflexivity.
  Qed.

  (* ...and the CAP, read and put back unchanged: [parseexec]'s two closing
     stores write a zero into a slot that is already zero, so the node comes
     out of them exactly as it went in.  That is not a redundancy in sh --
     the slot is only zero because [memset] made it so, and C does not know
     that -- but it is why the exit block costs no case analysis. *)
  Local Lemma ushp_slots_cap (s0 base : Z) (toks : list (nat * nat))
      (sel : nat * nat -> nat) :
    (length toks < 10)%nat ->
    ([∗ list] i ∈ seq 0 10, ushp_slot0 s0 base toks sel i) -∗
    uword γd (base + 8 * Z.of_nat (length toks)) (mword_of_int 0) ∗
    (uword γd (base + 8 * Z.of_nat (length toks)) (mword_of_int 0) -∗
     [∗ list] i ∈ seq 0 10, ushp_slot0 s0 base toks sel i).
  Proof.
    intro Hlt. iIntros "H".
    assert (Hj : seq 0 10 !! (length toks) = Some (length toks))
      by (apply lookup_seq; lia).
    assert (Hnone : ushp_slot0 s0 base toks sel (length toks)
                    = uword γd (base + 8 * Z.of_nat (length toks))
                        (mword_of_int 0)).
    { rewrite /ushp_slot0 (lookup_ge_None_2 toks (length toks) ltac:(lia)).
      reflexivity. }
    rewrite (big_sepL_delete (fun _ i : nat => ushp_slot0 s0 base toks sel i)
               (seq 0 10) (length toks) (length toks) Hj).
    rewrite Hnone.
    iDestruct "H" as "[Hj Hrest]". iFrame "Hj". iIntros "Hj".
    iFrame "Hj Hrest".
  Qed.

  (* THE LOOP'S ONE RESOURCE STEP: slot [argc] is the zero the memset left,
     and writing a token boundary into it appends that token.  Nothing else
     in the vector moves, which is the whole content of [big_sepL_delete]
     here -- the other nine slots' predicates do not even mention the
     token that was appended. *)
  Local Lemma ushp_slots_upd (s0 base : Z) (done : list (nat * nat))
      (tk : nat * nat) (sel : nat * nat -> nat) :
    (length done < 10)%nat ->
    ([∗ list] i ∈ seq 0 10, ushp_slot0 s0 base done sel i) -∗
    uword γd (base + 8 * Z.of_nat (length done)) (mword_of_int 0) ∗
    (uword γd (base + 8 * Z.of_nat (length done))
       (mword_of_int (s0 + Z.of_nat (sel tk))) -∗
     [∗ list] i ∈ seq 0 10, ushp_slot0 s0 base (done ++ [tk]) sel i).
  Proof.
    intro Hlt. iIntros "H".
    assert (Hj : seq 0 10 !! (length done) = Some (length done))
      by (apply lookup_seq; lia).
    assert (Hnone : ushp_slot0 s0 base done sel (length done)
                    = uword γd (base + 8 * Z.of_nat (length done))
                        (mword_of_int 0)).
    { rewrite /ushp_slot0 (lookup_ge_None_2 done (length done) ltac:(lia)).
      reflexivity. }
    assert (Hsome : ushp_slot0 s0 base (done ++ [tk]) sel (length done)
                    = uword γd (base + 8 * Z.of_nat (length done))
                        (mword_of_int (s0 + Z.of_nat (sel tk)))).
    { rewrite /ushp_slot0 (ushp_lookup_app_mid done tk). reflexivity. }
    rewrite (big_sepL_delete (fun _ i : nat => ushp_slot0 s0 base done sel i)
               (seq 0 10) (length done) (length done) Hj).
    rewrite Hnone.
    iDestruct "H" as "[Hj Hrest]". iFrame "Hj". iIntros "Hj".
    rewrite (big_sepL_delete
               (fun _ i : nat => ushp_slot0 s0 base (done ++ [tk]) sel i)
               (seq 0 10) (length done) (length done) Hj).
    rewrite Hsome.
    iSplitL "Hj"; [ iExact "Hj" | ].
    iApply (big_sepL_mono with "Hrest").
    intros k y Hy. apply lookup_seq in Hy as [ -> Hlt10 ].
    rewrite Nat.add_0_l.
    destruct (decide (k = length done)) as [ Ek | Ek ]; [ done | ].
    assert (Heq : ushp_slot0 s0 base (done ++ [tk]) sel k
                  = ushp_slot0 s0 base done sel k).
    { rewrite /ushp_slot0 (ushp_lookup_app_ne done tk k Ek). reflexivity. }
    rewrite Heq. done.
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
      urun γt γd γs γfd h m (mword_of_int ShSyms.malloc) (10 + avail) -∗
      (∀ (h' : CpuId) (m' : regfile) (p : Z) (g : nat -> bv 8),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         ⌜ 0 < p /\ p mod 16 = 0 /\ p + nbytes < 2 ^ 38 ⌝ -∗
         ubytes γd p (Z.to_nat nbytes) g -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + avail) -∗
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
    urun γt γd γs γfd h mc (mword_of_int 0x46e) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x482) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3;
      iIntros "#Hcode Hstr Hws Hrun Hcont"; [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- 0x46e  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int 0x46e)
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
    iApply (wp_uk_cmv γt γd γs γfd h1 m1 (mword_of_int 0x472) a0_idx s3_idx
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
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int 0x474)
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
    iApply (wp_kshp_strchr h3 m3 false dw ushp_whitespace 5 ushp_ws_f (f j) nn
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
      iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int 0x478)
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
    iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int 0x478)
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
    iApply (wp_uk_caddi γt γd γs γfd h5 m4 (mword_of_int 0x47a)
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
      iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int 0x47c)
                (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int 0x46e) (2 + nn)
                Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_47c with "Hcode"). }
      rewrite (ushp_pc_step 0x47c 4). iIntros (h7) "Hrun".
      (* ---- 0x480  c.mv s1,s2 -- [s = es], which it already is ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h7 m5 (mword_of_int 0x480) s1_idx s2_idx
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
    iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int 0x47c)
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
    urun γt γd γs γfd h mc (mword_of_int 0x46a) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x482) (2 + nn) -∗
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
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x46a)
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
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x46a)
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
    urun γt γd γs γfd h me (mword_of_int 0x48e) (2 + nn) -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
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
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h1 mr (mword_of_int 0x49c)
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
    iApply (wp_uk_cjr γt γd γs γfd h2
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
  Lemma wp_kshp_peek (h : CpuId) (m : regfile) (dq dw : dfrac)
      (tt : bool) (dt : dfrac)
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
    ushp_sstr tt dt toks tlen tf -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.peek) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ushp_sstr tt dt toks tlen tf -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushp_peek_res len f
                    (off + ushp_skipws (len - off) off f) tlen tf) ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (2 + nn)) -∗
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
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x448)
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
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x45a) s4_idx a0_idx
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
    iApply (wp_uk_cmv γt γd γs γfd h4 m3 (mword_of_int 0x45c) s2_idx a1_idx
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
    iApply (wp_uk_cmv γt γd γs γfd h5 m4 (mword_of_int 0x45e) s5_idx a2_idx
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
    iApply (wp_uk_cld γt γd γs γfd h6 m5 (mword_of_int 0x460)
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
    iApply (wp_uk_auipc γt γd γs γfd h7 m6 (mword_of_int 0x462)
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
    iApply (wp_uk_addi γt γd γs γfd h8 m7 (mword_of_int 0x466)
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
    iApply (wp_uk_sd γt γd γs γfd h10 mc' (mword_of_int 0x482)
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
      iApply (wp_uk_lbu γt γd γs γfd h11 mc' (mword_of_int 0x486)
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
      iApply (wp_uk_cli γt γd γs γfd h12 n9 (mword_of_int 0x48a)
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
      iApply (wp_uk_cbnez γt γd γs γfd h13 n10 (mword_of_int 0x48c)
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
    iApply (wp_uk_lbu γt γd γs γfd h11 mc' (mword_of_int 0x486)
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
    iApply (wp_uk_cli γt γd γs γfd h12 n9 (mword_of_int 0x48a)
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
    iApply (wp_uk_cbnez γt γd γs γfd h13 n10 (mword_of_int 0x48c)
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
    iApply (wp_uk_cmv γt γd γs γfd h14 n10 (mword_of_int 0x4a0) a0_idx s5_idx
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
    iApply (wp_uk_jal γt γd γs γfd h15 n11 (mword_of_int 0x4a2)
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
    iApply (wp_kshp_strchr h16 n12 tt dt toks tlen tf (f kk) nn
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
    iApply (wp_uk_sltu γt γd γs γfd h17 n13 (mword_of_int 0x4a6)
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
    iApply (wp_uk_cj γt γd γs γfd h18 n14 (mword_of_int 0x4aa)
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
  (* §8b THE SEVEN TOKEN TABLES, AS ONE PERSISTENT PREMISE.                 *)
  (*                                                                       *)
  (* peek's third argument is a string literal at all seven call sites, and *)
  (* §2c established that a literal is a TEXT-half string.  All seven come  *)
  (* out of the SAME resource -- [UCodeShP.shp_rodata], the read-only image *)
  (* -- which is persistent, so a walk carries ONE premise for all of them  *)
  (* and never has to thread a table in and out of a call.                  *)
  (*                                                                       *)
  (* THE BYTES ARE NOT WRITTEN OUT.  [ushp_lit base] reads them out of the  *)
  (* dump, [ushp_lit_ok] decides whether that is a C string of that length, *)
  (* and [ushp_lit_sym] decides whether every byte of it is one of sh-s     *)
  (* seven symbol characters -- one [vm_compute] each, and the two together *)
  (* are exactly what a REFUTED peek needs.  UkShDiag.v does the same for   *)
  (* the printer's format strings; this is that idiom at a second consumer, *)
  (* which is the third leg of relocation ask 3.                            *)
  (* ===================================================================== *)

  (* the byte function of the literal based at [base] *)
  Definition ushp_lit (base : Z) : nat -> bv 8 :=
    fun j => default ubyte0 (shp_ro !! (base + Z.of_nat j)%Z).

  (* ...and what makes it a C string of length [len] *)
  Definition ushp_lit_ok (base : Z) (len : nat) : bool :=
    forallb (fun j => match shp_ro !! (base + Z.of_nat j)%Z with
                      | Some b => negb (Z.eqb (bv_unsigned b) 0)
                      | None => false
                      end)
            (seq 0 len)
    && match shp_ro !! (base + Z.of_nat len)%Z with
       | Some b => Z.eqb (bv_unsigned b) 0
       | None => false
       end.

  (* ...and that every byte of it is one of [ushp_sym_bytes] *)
  Definition ushp_lit_sym (base : Z) (len : nat) : bool :=
    forallb (fun j => ushp_is_sym (ushp_lit base j)) (seq 0 len).

  Local Lemma ushp_lit_ok_body (base : Z) (len j : nat) :
    ushp_lit_ok base len = true -> (j < len)%nat ->
    shp_ro !! (base + Z.of_nat j)%Z = Some (ushp_lit base j)
    /\ ushp_lit base j <> ubyte0.
  Proof.
    unfold ushp_lit_ok, ushp_lit. intros H Hj.
    apply andb_true_iff in H as [ H _ ].
    rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    destruct (shp_ro !! (base + Z.of_nat j)%Z) as [ b | ] eqn:Hb;
      [ | discriminate ].
    apply negb_true_iff, Z.eqb_neq in H.
    cbn [default from_option id]. split; [ reflexivity | ].
    intro He. apply H. rewrite He. vm_compute. reflexivity.
  Qed.

  Local Lemma ushp_lit_ok_nul (base : Z) (len : nat) :
    ushp_lit_ok base len = true ->
    shp_ro !! (base + Z.of_nat len)%Z = Some ubyte0.
  Proof.
    unfold ushp_lit_ok. intro H.
    apply andb_true_iff in H as [ _ H ].
    destruct (shp_ro !! (base + Z.of_nat len)%Z) as [ b | ] eqn:Hb;
      [ | discriminate ].
    apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H.
    vm_compute. reflexivity.
  Qed.

  (* THE TABLE, AS THE RESOURCE peek TAKES.  [true] is the text half. *)
  Lemma ushp_lit_str (base : Z) (len : nat) (dq : dfrac) :
    ushp_lit_ok base len = true ->
    Z.of_nat len < 2 ^ 31 ->
    shp_rodata γt -∗ ushp_sstr true dq base len (ushp_lit base).
  Proof.
    intros Hok Hlen. iIntros "#Hro".
    rewrite ushp_sstr_text /shp_rodata.
    iApply (utext_str_of_img γt shp_ro base len (ushp_lit base)).
    - intros j Hj. exact (proj2 (ushp_lit_ok_body base len j Hok Hj)).
    - exact Hlen.
    - intros j Hj. exact (proj1 (ushp_lit_ok_body base len j Hok Hj)).
    - exact (ushp_lit_ok_nul base len Hok).
    - iExact "Hro".
  Qed.

  (* [strchr] misses a table none of whose bytes is the one looked for *)
  Local Lemma ushp_find_none (n i : nat) (f : nat -> bv 8) (b : bv 8) :
    (forall j : nat, (i <= j < i + n)%nat -> f j <> b) ->
    ushp_find n i f b = None.
  Proof.
    revert i. induction n as [| n IH ]; intros i Hne; [ reflexivity | ].
    cbn [ushp_find].
    destruct (bool_decide (f i = b)) eqn:Hb.
    { apply bool_decide_eq_true in Hb. exfalso. exact (Hne i ltac:(lia) Hb). }
    apply IH. intros j Hj. exact (Hne j ltac:(lia)).
  Qed.

  (* THE ONE FACT THE FIVE REFUTED PEEKS NEED.  On a line with no symbol
     byte, a peek for a table of symbol bytes is 0 -- at the end of the
     line because the cursor has run out, and inside it because the byte
     there is not in the table. *)
  Lemma ushp_peek_res_sym (len : nat) (f : nat -> bv 8) (k tlen : nat)
      (base : Z) :
    ushp_no_symbols len f -> ushp_lit_sym base tlen = true ->
    ushp_peek_res len f k tlen (ushp_lit base) = 0.
  Proof.
    intros Hnos Hsym. rewrite /ushp_peek_res.
    destruct (bool_decide (k < len)%nat) eqn:Hk; [ | reflexivity ].
    apply bool_decide_eq_true in Hk.
    rewrite (ushp_find_none tlen 0%nat (ushp_lit base) (f k)).
    - reflexivity.
    - intros j Hj He.
      rewrite /ushp_lit_sym forallb_forall in Hsym.
      specialize (Hsym j ltac:(apply in_seq; lia)).
      rewrite He (Hnos k Hk) in Hsym. discriminate.
  Qed.

  (* ---- the seven bases, named ------------------------------------------ *)
  Definition ushp_T_redir : Z := 0x12f0.   (* the two redirection bytes, parseredirs *)
  Definition ushp_T_block : Z := 0x12f8.   (* the open paren, parseexec *)
  Definition ushp_T_arg   : Z := 0x1318.   (* the four argument-loop stoppers, parseexec *)
  Definition ushp_T_pipe  : Z := 0x1320.   (* the pipe byte, parsepipe *)
  Definition ushp_T_back  : Z := 0x1328.   (* the ampersand, parseline *)
  Definition ushp_T_list  : Z := 0x1330.   (* the semicolon, parseline *)
  Definition ushp_T_none  : Z := 0x1288.   (* the empty table, parsecmd *)

  (* ...and the two decidable checks, discharged once each *)
  Local Lemma ushp_T_redir_ok : ushp_lit_ok ushp_T_redir 2 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_block_ok : ushp_lit_ok ushp_T_block 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_arg_ok   : ushp_lit_ok ushp_T_arg 4 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_pipe_ok  : ushp_lit_ok ushp_T_pipe 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_back_ok  : ushp_lit_ok ushp_T_back 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_list_ok  : ushp_lit_ok ushp_T_list 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_none_ok  : ushp_lit_ok ushp_T_none 0 = true.
  Proof. vm_compute. reflexivity. Qed.

  Local Lemma ushp_T_redir_sym : ushp_lit_sym ushp_T_redir 2 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_block_sym : ushp_lit_sym ushp_T_block 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_arg_sym   : ushp_lit_sym ushp_T_arg 4 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_pipe_sym  : ushp_lit_sym ushp_T_pipe 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_back_sym  : ushp_lit_sym ushp_T_back 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_list_sym  : ushp_lit_sym ushp_T_list 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Lemma ushp_T_none_sym  : ushp_lit_sym ushp_T_none 0 = true.
  Proof. reflexivity. Qed.

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
    urun γt γd γs γfd h m (mword_of_int ShSyms.execcmd) (4 + (10 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ 0 < p /\ p mod 16 = 0 /\ p + 168 < 2 ^ 38 ⌝ -∗
       ushp_exec_pre s0 p [] -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (10 + nn)) -∗
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
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x1d2)
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
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 m1 (mword_of_int 0x1da)
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
    iApply (wp_uk_li γt γd γs γfd h3 m2 (mword_of_int 0x1dc)
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
    iApply (wp_uk_jal γt γd γs γfd h4 m3 (mword_of_int 0x1e0)
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
    iApply (wp_uk_cmv γt γd γs γfd h6 m5 (mword_of_int 0x1e4) s1_idx a0_idx
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
    iApply (wp_uk_li γt γd γs γfd h7 m6 (mword_of_int 0x1e6)
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
    iApply (wp_uk_cli γt γd γs γfd h8 m7 (mword_of_int 0x1ea)
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
    iApply (wp_uk_jal γt γd γs γfd h9 m8 (mword_of_int 0x1ec)
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
    iApply (wp_ksh_memset γt γd γs γfd h10 m9 p 168%nat g (8 + nn)
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
    iApply (wp_uk_cli γt γd γs γfd h11 m10 (mword_of_int 0x1f0)
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
    iApply (wp_uk_csw γt γd γs γfd h12 m11 (mword_of_int 0x1f2)
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
    iApply (wp_uk_cmv γt γd γs γfd h13 m11 (mword_of_int 0x1f4) a0_idx s1_idx
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
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h15 me (mword_of_int 0x1fc)
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
    iApply (wp_uk_cjr γt γd γs γfd h16 mf (mword_of_int 0x1fe) ra_idx
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
    - rewrite /ushp_exec_pre /ushp_type_at.
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
        * iApply (ushp_slots_nil0 s0 (p + 8) fst (fun _ : nat => ubyte0)
                    ltac:(intros j _; reflexivity) with "Hav").
        * iApply (ushp_slots_nil0 s0 (p + 88) snd (fun _ : nat => ubyte0)
                    ltac:(intros j _; reflexivity) with "Hev").
  Qed.

  (* ===================================================================== *)
  (* §9 gettoken @0x310 -- 104 instructions, an EIGHT-word frame, THREE      *)
  (* scans and a switch.                                                    *)
  (*                                                                       *)
  (*   int gettoken(char **ps, char *es, char **q, char **eq) {             *)
  (*     char *s = *ps;  int ret;                                          *)
  (*     while(s < es && strchr(whitespace, *s)) s++;                       *)
  (*     if(q) *q = s;                                                     *)
  (*     ret = *s;                                                         *)
  (*     switch( *s ){ case 0: break;                                        *)
  (*       case '|': case '(': case ')': case ';': case '&': case '<':     *)
  (*         s++; break;                                                   *)
  (*       case '>': s++; if( *s == '>'){ ret = '+'; s++; } break;          *)
  (*       default: ret = 'a';                                             *)
  (*         while(s < es && !strchr(whitespace, *s)                       *)
  (*                      && !strchr(symbols, *s)) s++;                    *)
  (*         break; }                                                      *)
  (*     if(eq) *eq = s;                                                   *)
  (*     while(s < es && strchr(whitespace, *s)) s++;                       *)
  (*     *ps = s;  return ret; }                                           *)
  (*                                                                       *)
  (* THE LEXER PROPER: peek only LOOKS, gettoken CONSUMES.  It moves the    *)
  (* cursor past one token and reports what kind it was, and its two out    *)
  (* parameters [q] / [eq] are what [parseexec] records as the token's      *)
  (* boundary pair -- which is why the tree predicate indexes tokens by     *)
  (* PAIRS OF INDEXES and not by strings.                                   *)
  (*                                                                       *)
  (* SCOPED BY [ushp_no_symbols], AND THAT IS WHAT MAKES IT TRACTABLE.      *)
  (* The switch has eight arms in the source and four in the object code    *)
  (* (a NUL arm, a six-value symbol arm, a '>' arm with its own '>>'        *)
  (* lookahead, and a default).  On a line with no symbol byte only TWO of  *)
  (* them are reachable, and WHICH ONE is decided by a single fact: the     *)
  (* byte at the cursor is NUL exactly when the cursor has reached [es],    *)
  (* because a [ustr]'s body bytes are all non-NUL.  So the postcondition   *)
  (* is a dichotomy on [k = len], not an eight-way case analysis -- and     *)
  (* the six symbol arms and the '>' arm are REFUTED, at the branch, from   *)
  (* [ushp_nsym_bv]'s seven numeric disequalities.                          *)
  (*                                                                       *)
  (* THREE SCANS, TWO MOULDS.  The leading and trailing whitespace scans    *)
  (* are the SAME CODE as peek's, at 0x33a and 0x39c rather than 0x46e --   *)
  (* identical widths, identical branch immediates, only the [jal]'s        *)
  (* pc-relative offset differs -- so §8's scan is re-stated once over its  *)
  (* base pc and its [jal] immediate ([wp_kshp_ws_scan]) and applied three  *)
  (* times.  The token-body scan at 0x400 is the new one: the same loop     *)
  (* with TWO [strchr] calls per turn, measured by [ushp_toklen].            *)
  (* ===================================================================== *)

  (* ---- the two pieces of 32-bit algebra the switch needs ---------------- *)

  (* what [sign_extend'] DOES to a 32-bit word, as a Z.  [sext32_small] is
     the special case that fits; gettoken's [addiw a5,a5,-40] does NOT fit
     when the byte is below 40, and the following [andi] is what makes that
     harmless -- so what is needed is the unconditional formula. *)
  Local Lemma ushp_sext32_unsigned (w : mword 32) :
    bv_unsigned (sign_extend' 64 w : mword 64)
    = (((bv_unsigned w + Z31) mod Z32) - Z31) mod Z64.
  Proof.
    cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
         to_word get_word MachineWord.MachineWord.sign_extend].
    rewrite bv_sign_extend_unsigned.
    unfold bv_signed, bv_swrap, bv_wrap.
    assert (Eh32 : bv_half_modulus 32 = Z31) by (vm_compute; reflexivity).
    rewrite Zmod32 Eh32 Zmod64. reflexivity.
  Qed.

  (* ...and why the sign extension is harmless: [zext.b] keeps the low eight
     bits, and sign extension does not touch them. *)
  Local Lemma ushp_and255_sext (w : mword 32) :
    and_vec (sign_extend' 64 w : mword 64) (mword_of_int 255)
    = mword_of_int (bv_unsigned w mod 256).
  Proof.
    apply bv_eq. rewrite and_vec64_unsigned.
    assert (H255 : bv_unsigned (mword_of_int 255 : mword 64) = 255)
      by (vm_compute; reflexivity).
    rewrite H255 ushp_sext32_unsigned !moi_unsigned.
    set (u := bv_unsigned w).
    assert (Ho : (255 = Z.ones 8)) by (vm_compute; reflexivity).
    rewrite Ho.
    rewrite (Z.land_ones ((((u + Z31) mod Z32) - Z31) mod Z64) 8 ltac:(lia)).
    assert (E8 : 2 ^ 8 = 256) by (vm_compute; reflexivity). rewrite E8.
    rewrite <- (Znumtheory.Zmod_div_mod 256 Z64 (((u + Z31) mod Z32) - Z31)
                  ltac:(lia) ltac:(unfold Z64; lia)
                  ltac:(exists 72057594037927936; unfold Z64; reflexivity)).
    rewrite Zminus_mod.
    rewrite <- (Znumtheory.Zmod_div_mod 256 Z32 (u + Z31)
                  ltac:(lia) ltac:(unfold Z32; lia)
                  ltac:(exists 16777216; unfold Z32; reflexivity)).
    assert (EZ31 : Z31 mod 256 = 0) by (vm_compute; reflexivity).
    rewrite EZ31 Z.sub_0_r Zmod_mod Zplus_mod EZ31 Z.add_0_r Zmod_mod.
    rewrite (Z.mod_small (u mod 256) Z64
               ltac:(pose proof (Z.mod_pos_bound u 256 ltac:(lia));
                     unfold Z64; lia)).
    reflexivity.
  Qed.

  (* [sext.w s5,a5] on a byte: the value is already in range, so it is the
     identity -- which is why [ret] and the compared byte are the same Z. *)
  Local Lemma ushp_sextw_byte (v : Z) :
    0 <= v < 256 ->
    (sign_extend' 64
       (subrange_vec_dec
          (add_vec (mword_of_int v : mword 64)
             (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0 : mword 32)
     : mword 64)
    = mword_of_int v.
  Proof.
    intro Hv.
    assert (E0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                 = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 (moi_addw v 0 ltac:(unfold Z31; lia)).
    f_equal. lia.
  Qed.

  (* [addiw a5,a5,-40 ; zext.b a5,a5] -- the switch's range test, as a Z.
     Below 40 the [addiw] wraps and the [zext.b] unwraps it; the composite
     is exactly [(v - 40) mod 256], which is 0 or 1 on precisely the two
     bytes '(' and ')' -- both of them symbols. *)
  Local Lemma ushp_addiw_andi (v : Z) :
    0 <= v < 256 ->
    and_vec
      (sign_extend' 64
         (subrange_vec_dec
            (add_vec (mword_of_int v : mword 64)
               (sign_extend' 64 (mword_of_int 4056 : mword 12))) 31 0
          : mword 32) : mword 64)
      (sign_extend' 64 (mword_of_int 255 : mword 12))
    = mword_of_int ((v - 40) mod 256).
  Proof.
    intro Hv.
    assert (Ei : (sign_extend' 64 (mword_of_int 4056 : mword 12) : mword 64)
                 = mword_of_int (-40))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : (sign_extend' 64 (mword_of_int 255 : mword 12) : mword 64)
                 = mword_of_int 255)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ei Em moi_add.
    rewrite (ushp_and255_sext
               (subrange_vec_dec (mword_of_int (v + -40) : mword 64) 31 0)).
    rewrite low32_moi.
    f_equal.
    rewrite <- (Znumtheory.Zmod_div_mod 256 Z32 (v + -40)
                  ltac:(lia) ltac:(unfold Z32; lia)
                  ltac:(exists 16777216; unfold Z32; reflexivity)).
    f_equal; lia.
  Qed.

  (* ---- the scan mould, over its base pc --------------------------------- *)

  (* [ushp_pc_step] at a pc the caller wants NAMED rather than summed: the
     walks below run at [p + 4], [p + 6], ... and every step would otherwise
     leave an [p + 6 + 4] the next [uinstr_is] does not match. *)
  (* THE WHITESPACE SCAN, ONCE, FOR ALL THREE OF ITS COPIES.
       p+0   lbu a1,0(s1)     p+4   c.mv a0,s3      p+6   jal strchr
       p+10  c.beqz a0,p+20   p+12  c.addi s1,s1,1  p+14  bne s2,s1,p
       p+18  c.mv s1,s2       p+20  the exit
     peek's is at p = 0x46e and gettoken's two at p = 0x33a and p = 0x39c --
     the SAME widths and the SAME branch immediates, gcc having emitted the
     same loop three times; only the [jal]'s pc-relative offset differs, and
     that is the parameter [ji].  What a call site owes instead of the four
     [vm_compute]s this proof used to do inline is four pure facts at
     CONCRETE numbers ([Hjt], [Hjr], [Hal20], [Halp]) -- the §4b bargain. *)
  Local Lemma wp_kshp_ws_scan (p : Z) (ji : mword 21) (dq dw : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (nn : nat) :
    (mword_of_int 0xa82 : mword 64)
      = add_vec (mword_of_int (p + 6)) (sign_extend' 64 ji) ->
    ret_pc (mword_of_int (p + 10) : mword 64) = mword_of_int (p + 10) ->
    eq_vec (access_vec_dec (mword_of_int (p + 20) : mword 64) 0) ('b"0")
      = true ->
    eq_vec (access_vec_dec (mword_of_int p : mword 64) 0) ('b"0") = true ->
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    uinstr_is γt (mword_of_int p) false
      (LOAD (mword_of_int 0 : mword 12, Regidx s1_idx, Regidx a1_idx,
             true, 1)) -∗
    uinstr_is γt (mword_of_int (p + 4)) true
      (C_MV (Regidx a0_idx, Regidx s3_idx)) -∗
    uinstr_is γt (mword_of_int (p + 6)) false (JAL (ji, Regidx ra_idx)) -∗
    uinstr_is γt (mword_of_int (p + 10)) true
      (C_BEQZ (mword_of_int 5 : mword 8, Cregidx (mword_of_int 2))) -∗
    uinstr_is γt (mword_of_int (p + 12)) true
      (C_ADDI (mword_of_int 1 : mword 6, Regidx s1_idx)) -∗
    uinstr_is γt (mword_of_int (p + 14)) false
      (BTYPE (mword_of_int 8178 : mword 13, Regidx s1_idx, Regidx s2_idx,
              BNE)) -∗
    uinstr_is γt (mword_of_int (p + 18)) true
      (C_MV (Regidx s1_idx, Regidx s2_idx)) -∗
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int p) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int (p + 20)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjt Hjr Hal20 Halp.
    assert (Ebz : (mword_of_int (p + 20) : mword 64)
                  = add_vec (mword_of_int (p + 10))
                      (sign_extend' 64 (sign_extend' 13
                         (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))).
    { assert (E : (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 5 : mword 8) ('b"0")))
                   : mword 64) = mword_of_int 10)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E moi_add. f_equal; lia. }
    assert (Ebn : (mword_of_int p : mword 64)
                  = add_vec (mword_of_int (p + 14))
                      (sign_extend' 64 (mword_of_int 8178 : mword 13))).
    { assert (E : (sign_extend' 64 (mword_of_int 8178 : mword 13)
                   : mword 64) = mword_of_int (-14))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E moi_add. f_equal; lia. }
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3;
      iIntros "#Hi0 #Hi1 #Hi2 #Hi3 #Hi4 #Hi5 #Hi6 #Hcode Hstr Hws Hrun Hcont";
      [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- p+0  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int p)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat j)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "Hi0 Hb Hrun").
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step' p 4 (p + 4) ltac:(lia)). iIntros (h1) "Hrun".
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
    (* ---- p+4  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m1 (mword_of_int (p + 4)) a0_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3;
                    symmetry; exact (ushp_mv_val ushp_whitespace))
              with "Hi1 Hrun").
    rewrite (ushp_pc_step' (p + 4) 2 (p + 6) ltac:(lia)). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- p+6  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int (p + 6))
              ji ra_idx (mword_of_int 0xa82) (mword_of_int (p + 10)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              Hjt
              ltac:(symmetry;
                    exact (ushp_pc_step' (p + 6) 4 (p + 10) ltac:(lia)))
              ltac:(vm_compute; reflexivity)
              with "Hi2 Hrun").
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int (p + 10) : mword 64)]> m2).
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
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = mword_of_int (p + 10)).
    { rewrite (upd_eq m2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int (p + 10) : mword 64))).
      exact Hjr. }
    assert (Hcs3 : forall q : mword 5, ucallee_saved_idx q = true ->
                     m3 !!! Regidx q = mc !!! Regidx q).
    { intros q Hq.
      rewrite (Hm3 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm2 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      exact (Hm1 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity))). }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h3 m3 false dw ushp_whitespace 5 ushp_ws_f (f j) nn
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
    (* ---- p+10  c.beqz a0,p+20 -- the byte's membership decides ---- *)
    destruct (ushp_is_ws (f j)) eqn:Ews.
    2: { (* NOT whitespace: the scan stops here and [s1] never moved *)
      assert (Htk : true = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (ushp_ws_chr_z (f j) Ews).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int (p + 10))
                (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int (p + 20)) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk Ebz
                ltac:(intros _; exact Hal20)
                with "Hi3 Hrun").
      iIntros (h5) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q Hq _. exact (Hcs4 q Hq).
      - iPureIntro. rewrite Hs1_4.
        rewrite (ushp_skipws_stop (len - j) j f Ews). f_equal; lia. }
    (* WHITESPACE: the loop goes round *)
    destruct (ushp_ws_chr_nz (f j) Ews) as [ k [ Hk Hchr ] ].
    assert (Htk : false = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_4 Hchr.
      rewrite (moi_eq_zero (ushp_whitespace + Z.of_nat k)
                 ltac:(unfold ushp_whitespace, Z64; lia)).
      symmetry. apply Z.eqb_neq. unfold ushp_whitespace. lia. }
    iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int (p + 10))
              (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int (p + 20)) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk Ebz
              ltac:(discriminate)
              with "Hi3 Hrun").
    rewrite (ushp_pc_step' (p + 10) 2 (p + 12) ltac:(lia)).
    iIntros (h5) "Hrun".
    (* ---- p+12  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h5 m4 (mword_of_int (p + 12))
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S j))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_4 E1 moi_add;
                    replace (s0 + Z.of_nat (S j)) with (s0 + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "Hi4 Hrun").
    rewrite (ushp_pc_step' (p + 12) 2 (p + 14) ltac:(lia)).
    iIntros (h6) "Hrun".
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
    (* ---- p+14  bne s2,s1,p ---- *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* the scan ran to [es]: fall through to p+18, which is a no-op *)
      assert (Htk2 : false = uv_btaken BNE (m5 !!! Regidx s2_idx)
                               (m5 !!! Regidx s1_idx)).
      { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5 Hend.
        rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(lia) ltac:(lia)).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int (p + 14))
                (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int p) (2 + nn)
                Htk2 Ebn ltac:(discriminate)
                with "Hi5 Hrun").
      rewrite (ushp_pc_step' (p + 14) 4 (p + 18) ltac:(lia)).
      iIntros (h7) "Hrun".
      (* ---- p+18  c.mv s1,s2 -- [s = es], which it already is ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h7 m5 (mword_of_int (p + 18))
                s1_idx s2_idx (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_5; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "Hi6 Hrun").
      rewrite (ushp_pc_step' (p + 18) 2 (p + 20) ltac:(lia)).
      iIntros (h8) "Hrun".
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
    iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int (p + 14))
              (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE true
              (mword_of_int p) (2 + nn)
              Htk2 Ebn ltac:(intros _; exact Halp)
              with "Hi5 Hrun").
    iIntros (h7) "Hrun".
    iApply (IH (S j) h7 m5 ltac:(lia) Hj1 Hs0 Hs64 Hs1_5 Hs2_5 Hs3_5
              with "Hi0 Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h8 mc') "%Hpres %Hret2 Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. intros q Hq Hqs1.
      rewrite (Hpres q Hq Hqs1). rewrite (Hm5 q Hqs1). exact (Hcs4 q Hq).
    - iPureIntro. rewrite Hret2 Hr (ushp_skipws_step r j f Ews).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      f_equal; lia.
  Qed.

  (* the scan's ENTRY test, folded in FRONT so the cursor's index ranges over
     [0..len] and the whole of [q .. q+24] has ONE postcondition.  The
     compared register is a PARAMETER: gettoken's first copy tests against
     [a1] (the argument is still live) and its second against [s2], and
     peek's tests against [a1] -- same instruction, different rs2. *)
  Local Lemma wp_kshp_ws_enter (q : Z) (re : mword 5) (ji : mword 21)
      (dq dw : dfrac) (s0 : Z) (len j : nat) (f : nat -> bv 8) (nn : nat)
      (h : CpuId) (mc : regfile) :
    (mword_of_int 0xa82 : mword 64)
      = add_vec (mword_of_int (q + 10)) (sign_extend' 64 ji) ->
    ret_pc (mword_of_int (q + 14) : mword 64) = mword_of_int (q + 14) ->
    eq_vec (access_vec_dec (mword_of_int (q + 24) : mword 64) 0) ('b"0")
      = true ->
    eq_vec (access_vec_dec (mword_of_int (q + 4) : mword 64) 0) ('b"0")
      = true ->
    (j <= len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    mc !!! Regidx re = mword_of_int (s0 + Z.of_nat len) ->
    uinstr_is γt (mword_of_int q) false
      (BTYPE (mword_of_int 24 : mword 13, Regidx re, Regidx s1_idx, BGEU)) -∗
    uinstr_is γt (mword_of_int (q + 4)) false
      (LOAD (mword_of_int 0 : mword 12, Regidx s1_idx, Regidx a1_idx,
             true, 1)) -∗
    uinstr_is γt (mword_of_int (q + 8)) true
      (C_MV (Regidx a0_idx, Regidx s3_idx)) -∗
    uinstr_is γt (mword_of_int (q + 10)) false (JAL (ji, Regidx ra_idx)) -∗
    uinstr_is γt (mword_of_int (q + 14)) true
      (C_BEQZ (mword_of_int 5 : mword 8, Cregidx (mword_of_int 2))) -∗
    uinstr_is γt (mword_of_int (q + 16)) true
      (C_ADDI (mword_of_int 1 : mword 6, Regidx s1_idx)) -∗
    uinstr_is γt (mword_of_int (q + 18)) false
      (BTYPE (mword_of_int 8178 : mword 13, Regidx s1_idx, Regidx s2_idx,
              BNE)) -∗
    uinstr_is γt (mword_of_int (q + 22)) true
      (C_MV (Regidx s1_idx, Regidx s2_idx)) -∗
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int q) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int (q + 24)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjt Hjr Hal24 Hal4 Hjle Hs0 Hs64 Hs1 Hs2 Hs3 Hre.
    iIntros "#Hib #Hi0 #Hi1 #Hi2 #Hi3 #Hi4 #Hi5 #Hi6 #Hcode Hstr Hws Hrun Hcont".
    assert (Ebg : (mword_of_int (q + 24) : mword 64)
                  = add_vec (mword_of_int q)
                      (sign_extend' 64 (mword_of_int 24 : mword 13))).
    { assert (E : (sign_extend' 64 (mword_of_int 24 : mword 13) : mword 64)
                  = mword_of_int 24) by (apply bv_eq; vm_compute; reflexivity).
      rewrite E moi_add. f_equal; lia. }
    destruct (Nat.eq_dec j len) as [ Hend | Hne ].
    { (* the cursor is already at [es]: the scan is skipped entirely *)
      assert (Htk : true = uv_btaken BGEU (mc !!! Regidx s1_idx)
                             (mc !!! Regidx re)).
      { cbn [uv_btaken]. rewrite Hs1 Hre Hend.
        rewrite (moi_ge_u (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply Z.geb_le. lia. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int q)
                (mword_of_int 24 : mword 13) re s1_idx BGEU true
                (mword_of_int (q + 24)) (2 + nn)
                Htk Ebg ltac:(intros _; exact Hal24)
                with "Hib Hrun").
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros t _ _. reflexivity.
      - iPureIntro. rewrite Hs1.
        assert (Hz : (len - j)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero j f). f_equal; lia. }
    (* ...otherwise the scan runs *)
    assert (Hjlt : (j < len)%nat) by lia.
    assert (Htk : false = uv_btaken BGEU (mc !!! Regidx s1_idx)
                            (mc !!! Regidx re)).
    { cbn [uv_btaken]. rewrite Hs1 Hre.
      rewrite (moi_ge_u (s0 + Z.of_nat j) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int q)
              (mword_of_int 24 : mword 13) re s1_idx BGEU false
              (mword_of_int (q + 24)) (2 + nn)
              Htk Ebg ltac:(discriminate)
              with "Hib Hrun").
    rewrite (ushp_pc_step' q 4 (q + 4) ltac:(lia)). iIntros (h1) "Hrun".
    iApply (wp_kshp_ws_scan (q + 4) ji dq dw s0 len f nn
              ltac:(replace (q + 4 + 6) with (q + 10) by lia; exact Hjt)
              ltac:(replace (q + 4 + 10) with (q + 14) by lia; exact Hjr)
              ltac:(replace (q + 4 + 20) with (q + 24) by lia; exact Hal24)
              Hal4
              (len - j)%nat j h1 mc
              eq_refl Hjlt Hs0 Hs64 Hs1 Hs2 Hs3
              with "[] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { replace (q + 4 + 0) with (q + 4) by lia. iApply "Hi0". }
    { replace (q + 4 + 4) with (q + 8) by lia. iApply "Hi1". }
    { replace (q + 4 + 6) with (q + 10) by lia. iApply "Hi2". }
    { replace (q + 4 + 10) with (q + 14) by lia. iApply "Hi3". }
    { replace (q + 4 + 12) with (q + 16) by lia. iApply "Hi4". }
    { replace (q + 4 + 14) with (q + 18) by lia. iApply "Hi5". }
    { replace (q + 4 + 18) with (q + 22) by lia. iApply "Hi6". }
    iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    replace (q + 4 + 20) with (q + 24) by lia.
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* ---- the token-body scan, 0x400..0x41a -------------------------------- *)

  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).

  (* WHERE THE TOKEN SCAN COMES OUT.  Its two live exits are the SAME
     instruction pair -- [li s5,97 ; c.j 0x388] at 0x432 and again at 0x438,
     gcc having duplicated the tail -- so a byte that ends the token (either
     table) leaves the scan at 0x388 with the answer already in s5, and only
     running off the end of the line leaves it anywhere else (0x424, past
     the third copy of [li s5,97] at 0x420).  Folding the three stubs into
     the scan is what makes the caller's case analysis TWO arms and not
     four. *)
  Definition ushp_tok_exit (len : nat) (f : nat -> bv 8) (j : nat) : Z :=
    if bool_decide ((j + ushp_toklen (len - j) j f) < len)%nat
    then 0x388 else 0x424.

  (* [while(s < es && !strchr(whitespace, *s) && !strchr(symbols, *s)) s++].
     TWO calls a turn, so the register promise is thinner than the
     whitespace scan's by one more register: s5 holds [&symbols] through
     the loop and the ANSWER after it. *)
  Local Lemma wp_kshp_tok_scan (dq dw dv : dfrac) (s0 : Z) (len : nat)
      (f : nat -> bv 8) (nn : nat) :
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    mc !!! Regidx s5_idx = mword_of_int ushp_symbols ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x400) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s5_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_toklen (len - j) j f)) ⌝ -∗
         ⌜ mc' !!! Regidx s5_idx = mword_of_int 97 ⌝ -∗
         urun γt γd γs γfd h' mc'
           (mword_of_int (ushp_tok_exit len f j)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3 Hs5;
      iIntros "#Hcode Hstr Hws Hsy Hrun Hcont"; [ lia | ].
    (* ---- 0x400  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int 0x400)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat j)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_400 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x400 4). iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                     : mword 64)]> mc).
    assert (Hm1 : forall t : mword 5, Regidx t <> Regidx a1_idx ->
                    m1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx a1_idx) (Regidx t) _ Ht)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (upd_eq mc (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f j)). }
    (* ---- 0x404  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m1 (mword_of_int 0x404) a0_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3;
                    symmetry; exact (ushp_mv_val ushp_whitespace))
              with "[] Hrun").
    { iApply (uis_shp_404 with "Hcode"). }
    rewrite (ushp_pc_step 0x404 2). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx a0_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx a0_idx) (Regidx t) _ Ht)).
    (* ---- 0x406  jal a82 <strchr> -- the WHITESPACE table ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int 0x406)
              (mword_of_int 1660 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x40a) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_406 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x40a : mword 64)]> m2).
    assert (Hm3 : forall t : mword 5, Regidx t <> Regidx ra_idx ->
                    m3 !!! Regidx t = m2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m2 (Regidx ra_idx) (Regidx t) _ Ht)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int ushp_whitespace).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ushp_whitespace : mword 64))). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)). exact Ha1_1. }
    assert (Eret3 : ret_pc (m3 !!! Regidx ra_idx) = mword_of_int 0x40a).
    { rewrite (upd_eq m2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x40a : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hcs3 : forall t : mword 5, ucallee_saved_idx t = true ->
                     m3 !!! Regidx t = mc !!! Regidx t).
    { intros t Ht.
      rewrite (Hm3 t (ushp_cs_ne t ra_idx Ht ltac:(vm_compute; reflexivity))).
      rewrite (Hm2 t (ushp_cs_ne t a0_idx Ht ltac:(vm_compute; reflexivity))).
      exact (Hm1 t (ushp_cs_ne t a1_idx Ht ltac:(vm_compute; reflexivity))). }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h3 m3 false dw ushp_whitespace 5 ushp_ws_f (f j) nn
              Ha0_3 Ha1_3 ltac:(unfold ushp_whitespace; lia)
              ltac:(unfold ushp_whitespace, Z64; lia)
              with "Hcode Hws Hrun").
    iIntros "Hws" (h4 m4) "%Hcs34 %Ha0_4 Hrun".
    rewrite Eret3.
    assert (Hcs4 : forall t : mword 5, ucallee_saved_idx t = true ->
                     m4 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; rewrite (Hcs34 t Ht); exact (Hcs3 t Ht)).
    assert (Hs1_4 : m4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hcs4 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hs2_4 : m4 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hcs4 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_4 : m4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (Hs5_4 : m4 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by (rewrite (Hcs4 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
    (* ---- 0x40a  c.bnez a0,0x438 -- a whitespace byte ENDS the token ---- *)
    destruct (ushp_is_ws (f j)) eqn:Ews.
    { destruct (ushp_ws_chr_nz (f j) Ews) as [ k [ Hk Hchr ] ].
      assert (Htk : true = neq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 Hchr.
        rewrite (moi_neq_zero (ushp_whitespace + Z.of_nat k)
                   ltac:(unfold ushp_whitespace, Z64; lia)).
        assert (Hz : (ushp_whitespace + Z.of_nat k =? 0) = false)
          by (apply Z.eqb_neq; unfold ushp_whitespace; lia).
        rewrite Hz. reflexivity. }
      iApply (wp_uk_cbnez γt γd γs γfd h4 m4 (mword_of_int 0x40a)
                (mword_of_int 23 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x438) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_40a with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x438  li s5,97 ---- *)
      iApply (wp_uk_li γt γd γs γfd h5 m4 (mword_of_int 0x438)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_438 with "Hcode"). }
      rewrite (ushp_pc_step 0x438 4). iIntros (h6) "Hrun".
      (* ---- 0x43c  c.j 0x388 ---- *)
      iApply (wp_uk_cj γt γd γs γfd h6
                (<[Regidx s5_idx
                   := regval_into_reg (mword_of_int 97 : mword 64)]> m4)
                (mword_of_int 0x43c) (mword_of_int 1958 : mword 11)
                (mword_of_int 0x388) (2 + nn)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_43c with "Hcode"). }
      iIntros (h7) "Hrun".
      assert (Etl : ushp_toklen (len - j) j f = 0%nat)
        by (apply (ushp_toklen_stop (len - j) j f);
            rewrite Ews; reflexivity).
      assert (Eex : ushp_tok_exit len f j = 0x388).
      { unfold ushp_tok_exit. rewrite Etl.
        rewrite (bool_decide_eq_true_2 ((j + 0)%nat < len)%nat
                   ltac:(lia)). reflexivity. }
      rewrite <- Eex.
      iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
      - iPureIntro. intros t Ht _ Hts5.
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx t) _ Hts5).
        exact (Hcs4 t Ht).
      - iPureIntro.
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Hs1_4 Etl. f_equal; lia.
      - iPureIntro.
        exact (upd_eq m4 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 97 : mword 64))). }
    (* not whitespace: the second table is consulted *)
    assert (Htk : false = neq_vec (m4 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_4 (ushp_ws_chr_z (f j) Ews).
      rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uk_cbnez γt γd γs γfd h4 m4 (mword_of_int 0x40a)
              (mword_of_int 23 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x438) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_40a with "Hcode"). }
    rewrite (ushp_pc_step 0x40a 2). iIntros (h5) "Hrun".
    (* ---- 0x40c  lbu a1,0(s1) -- the same byte, read again ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h5 m4 (mword_of_int 0x40c)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_4 (uint_moi (s0 + Z.of_nat j)
                                    ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_40c with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x40c 4). iIntros (h6) "Hrun".
    set (n1 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                     : mword 64)]> m4).
    assert (Hn1 : forall t : mword 5, Regidx t <> Regidx a1_idx ->
                    n1 !!! Regidx t = m4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m4 (Regidx a1_idx) (Regidx t) _ Ht)).
    assert (Hb1_1 : n1 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (upd_eq m4 (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f j)). }
    (* ---- 0x410  c.mv a0,s5 -- the SYMBOLS table ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 n1 (mword_of_int 0x410) a0_idx s5_idx
              (mword_of_int ushp_symbols) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hn1 s5_idx ltac:(vm_compute; discriminate))
                      Hs5_4; symmetry; exact (ushp_mv_val ushp_symbols))
              with "[] Hrun").
    { iApply (uis_shp_410 with "Hcode"). }
    rewrite (ushp_pc_step 0x410 2). iIntros (h7) "Hrun".
    set (n2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_symbols
                                     : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx a0_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx a0_idx) (Regidx t) _ Ht)).
    (* ---- 0x412  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h7 n2 (mword_of_int 0x412)
              (mword_of_int 1648 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x416) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_412 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (n3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x416 : mword 64)]> n2).
    assert (Hn3 : forall t : mword 5, Regidx t <> Regidx ra_idx ->
                    n3 !!! Regidx t = n2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n2 (Regidx ra_idx) (Regidx t) _ Ht)).
    assert (Hc0_3 : n3 !!! Regidx a0_idx = mword_of_int ushp_symbols).
    { rewrite (Hn3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ushp_symbols : mword 64))). }
    assert (Hc1_3 : n3 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (Hn3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn2 a1_idx ltac:(vm_compute; discriminate)). exact Hb1_1. }
    assert (Eret7 : ret_pc (n3 !!! Regidx ra_idx) = mword_of_int 0x416).
    { rewrite (upd_eq n2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x416 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hcs7 : forall t : mword 5, ucallee_saved_idx t = true ->
                     n3 !!! Regidx t = m4 !!! Regidx t).
    { intros t Ht.
      rewrite (Hn3 t (ushp_cs_ne t ra_idx Ht ltac:(vm_compute; reflexivity))).
      rewrite (Hn2 t (ushp_cs_ne t a0_idx Ht ltac:(vm_compute; reflexivity))).
      exact (Hn1 t (ushp_cs_ne t a1_idx Ht ltac:(vm_compute; reflexivity))). }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h8 n3 false dv ushp_symbols 7 ushp_sym_f (f j) nn
              Hc0_3 Hc1_3 ltac:(unfold ushp_symbols; lia)
              ltac:(unfold ushp_symbols, Z64; lia)
              with "Hcode Hsy Hrun").
    iIntros "Hsy" (h9 n4) "%Hcs78 %Hc0_4 Hrun".
    rewrite Eret7.
    assert (Hcs8 : forall t : mword 5, ucallee_saved_idx t = true ->
                     n4 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; rewrite (Hcs78 t Ht) (Hcs7 t Ht); exact (Hcs4 t Ht)).
    assert (Hs1_8 : n4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hcs8 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hs2_8 : n4 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hcs8 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_8 : n4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hcs8 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (Hs5_8 : n4 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by (rewrite (Hcs8 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
    (* ---- 0x416  c.bnez a0,0x432 -- a symbol byte ENDS the token too ---- *)
    destruct (ushp_is_sym (f j)) eqn:Esy.
    { destruct (ushp_sym_chr_nz (f j) Esy) as [ k [ Hk Hchr ] ].
      assert (Htk2 : true = neq_vec (n4 !!! Regidx a0_idx) zero_reg).
      { rewrite Hc0_4 Hchr.
        rewrite (moi_neq_zero (ushp_symbols + Z.of_nat k)
                   ltac:(unfold ushp_symbols, Z64; lia)).
        assert (Hz : (ushp_symbols + Z.of_nat k =? 0) = false)
          by (apply Z.eqb_neq; unfold ushp_symbols; lia).
        rewrite Hz. reflexivity. }
      iApply (wp_uk_cbnez γt γd γs γfd h9 n4 (mword_of_int 0x416)
                (mword_of_int 14 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x432) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_416 with "Hcode"). }
      iIntros (h10) "Hrun".
      (* ---- 0x432  li s5,97 ---- *)
      iApply (wp_uk_li γt γd γs γfd h10 n4 (mword_of_int 0x432)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_432 with "Hcode"). }
      rewrite (ushp_pc_step 0x432 4). iIntros (h11) "Hrun".
      (* ---- 0x436  c.j 0x388 ---- *)
      iApply (wp_uk_cj γt γd γs γfd h11
                (<[Regidx s5_idx
                   := regval_into_reg (mword_of_int 97 : mword 64)]> n4)
                (mword_of_int 0x436) (mword_of_int 1961 : mword 11)
                (mword_of_int 0x388) (2 + nn)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_436 with "Hcode"). }
      iIntros (h12) "Hrun".
      assert (Etl : ushp_toklen (len - j) j f = 0%nat)
        by (apply (ushp_toklen_stop (len - j) j f);
            rewrite Ews Esy; reflexivity).
      assert (Eex : ushp_tok_exit len f j = 0x388).
      { unfold ushp_tok_exit. rewrite Etl.
        rewrite (bool_decide_eq_true_2 ((j + 0)%nat < len)%nat
                   ltac:(lia)). reflexivity. }
      rewrite <- Eex.
      iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
      - iPureIntro. intros t Ht _ Hts5.
        rewrite (upd_ne n4 (Regidx s5_idx) (Regidx t) _ Hts5).
        exact (Hcs8 t Ht).
      - iPureIntro.
        rewrite (upd_ne n4 (Regidx s5_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Hs1_8 Etl. f_equal; lia.
      - iPureIntro.
        exact (upd_eq n4 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 97 : mword 64))). }
    (* neither table: the byte is IN the token and the cursor advances *)
    assert (Hnn : ushp_is_ws (f j) || ushp_is_sym (f j) = false)
      by (rewrite Ews Esy; reflexivity).
    assert (Htk2 : false = neq_vec (n4 !!! Regidx a0_idx) zero_reg).
    { rewrite Hc0_4 (ushp_sym_chr_z (f j) Esy).
      rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uk_cbnez γt γd γs γfd h9 n4 (mword_of_int 0x416)
              (mword_of_int 14 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x432) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_416 with "Hcode"). }
    rewrite (ushp_pc_step 0x416 2). iIntros (h10) "Hrun".
    (* ---- 0x418  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h10 n4 (mword_of_int 0x418)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S j))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_8 E1 moi_add;
                    replace (s0 + Z.of_nat (S j)) with (s0 + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_418 with "Hcode"). }
    rewrite (ushp_pc_step 0x418 2). iIntros (h11) "Hrun".
    set (n5 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                     : mword 64)]> n4).
    assert (Hn5 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    n5 !!! Regidx t = n4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n4 (Regidx s1_idx) (Regidx t) _ Ht)).
    assert (Hs1_5 : n5 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S j)))
      by exact (upd_eq n4 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                    : mword 64))).
    assert (Hs2_5 : n5 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hn5 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_8).
    assert (Hs3_5 : n5 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hn5 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_8).
    assert (Hs5_5 : n5 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by (rewrite (Hn5 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_8).
    (* ---- 0x41a  bne s2,s1,0x400 ---- *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* the token ran to [es] *)
      assert (Htk3 : false = uv_btaken BNE (n5 !!! Regidx s2_idx)
                               (n5 !!! Regidx s1_idx)).
      { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5 Hend.
        rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(lia) ltac:(lia)).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h11 n5 (mword_of_int 0x41a)
                (mword_of_int 8166 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int 0x400) (2 + nn)
                Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_41a with "Hcode"). }
      rewrite (ushp_pc_step 0x41a 4). iIntros (h12) "Hrun".
      (* ---- 0x41e  c.mv s1,s2 ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h12 n5 (mword_of_int 0x41e)
                s1_idx s2_idx (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_5; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_41e with "Hcode"). }
      rewrite (ushp_pc_step 0x41e 2). iIntros (h13) "Hrun".
      set (n6 := <[Regidx s1_idx
                   := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                       : mword 64)]> n5).
      (* ---- 0x420  li s5,97 ---- *)
      iApply (wp_uk_li γt γd γs γfd h13 n6 (mword_of_int 0x420)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_420 with "Hcode"). }
      rewrite (ushp_pc_step' 0x420 4 0x424 ltac:(reflexivity)).
      iIntros (h14) "Hrun".
      assert (Etl : ushp_toklen (len - j) j f = 1%nat).
      { rewrite Hr (ushp_toklen_step r j f Hnn).
        assert (Hz : r = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_toklen_zero (S j) f). reflexivity. }
      assert (Eex : ushp_tok_exit len f j = 0x424).
      { unfold ushp_tok_exit. rewrite Etl.
        rewrite (bool_decide_eq_false_2 ((j + 1)%nat < len)%nat
                   ltac:(lia)). reflexivity. }
      rewrite <- Eex.
      iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
      - iPureIntro. intros t Ht Hts1 Hts5.
        rewrite (upd_ne n6 (Regidx s5_idx) (Regidx t) _ Hts5).
        rewrite /n6 (upd_ne n5 (Regidx s1_idx) (Regidx t) _ Hts1).
        rewrite (Hn5 t Hts1). exact (Hcs8 t Ht).
      - iPureIntro.
        rewrite (upd_ne n6 (Regidx s5_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite /n6 (upd_eq n5 (Regidx s1_idx)
                       (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                         : mword 64))).
        rewrite Etl.
        assert (Ee : (s0 + Z.of_nat len) = (s0 + Z.of_nat (j + 1))) by lia.
        rewrite Ee. reflexivity.
      - iPureIntro.
        exact (upd_eq n6 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 97 : mword 64))). }
    (* ...or the loop goes round *)
    assert (Hj1 : (S j < len)%nat) by lia.
    assert (Htk3 : true = uv_btaken BNE (n5 !!! Regidx s2_idx)
                            (n5 !!! Regidx s1_idx)).
    { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5.
      rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat (S j))
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      assert (Hne2 : (s0 + Z.of_nat len =? s0 + Z.of_nat (S j)) = false)
        by (apply Z.eqb_neq; lia).
      rewrite Hne2. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h11 n5 (mword_of_int 0x41a)
              (mword_of_int 8166 : mword 13) s1_idx s2_idx BNE true
              (mword_of_int 0x400) (2 + nn)
              Htk3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_41a with "Hcode"). }
    iIntros (h12) "Hrun".
    assert (Eex : ushp_tok_exit len f j = ushp_tok_exit len f (S j)).
    { unfold ushp_tok_exit. rewrite Hr (ushp_toklen_step r j f Hnn).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      replace ((j + S (ushp_toklen r (S j) f))%nat)
        with ((S j + ushp_toklen r (S j) f)%nat) by lia.
      reflexivity. }
    rewrite Eex.
    iApply (IH (S j) h12 n5 ltac:(lia) Hj1 Hs0 Hs64 Hs1_5 Hs2_5 Hs3_5 Hs5_5
              with "Hcode Hstr Hws Hsy Hrun").
    iIntros "Hstr Hws Hsy" (h13 mc') "%Hpres %Hret %Hans Hrun".
    iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
    - iPureIntro. intros t Ht Hts1 Hts5.
      rewrite (Hpres t Ht Hts1 Hts5) (Hn5 t Hts1). exact (Hcs8 t Ht).
    - iPureIntro. rewrite Hret Hr (ushp_toklen_step r j f Hnn).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      f_equal; lia.
    - iPureIntro. exact Hans.
  Qed.

  (* ---- the tail: the [*eq] store, the trailing scan, the epilogue ------- *)

  (* AN OPTIONAL OUT PARAMETER.  gettoken is called BOTH ways -- parseexec
     passes [&q, &eq] and parseredirs/parsepipe/parseline pass [0, 0] -- so
     the cell is a disjunction, not a [uword], and the address hygiene rides
     INSIDE it rather than as a premise a null caller could not meet. *)
  Definition ushp_cell (p : Z) (v : mword 64) : iProp Σ :=
    (⌜ p = 0 ⌝ ∨
     (⌜ 0 < p /\ p mod 8 = 0 /\ p + 8 < Z64 ⌝ ∗ uword γd p v))%I.

  (* THE TRAILING WHITESPACE SCAN, 0x390..0x3ae, with its table setup.
     [s3] is reloaded with [&whitespace] here even though it already holds
     it -- gcc rematerialises the address rather than keeping it live across
     the switch -- so s3 is written and drops out of the register promise. *)
  Local Lemma wp_kshp_gtk_ws2 (dq dw : dfrac) (s0 : Z) (len j : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (j <= len)%nat -> 0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x390) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Hs1 Hs2.
    iIntros "#Hcode Hstr Hws Hrun Hcont".
    (* ---- 0x390  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h mc (mword_of_int 0x390)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x2390)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_390 with "Hcode"). }
    rewrite (ushp_pc_step 0x390 4). iIntros (h1) "Hrun".
    set (m1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x2390 : mword 64)]> mc).
    assert (Hm1 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x394  addi s3,s3,-904  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi γt γd γs γfd h1 m1 (mword_of_int 0x394)
              (mword_of_int 3192 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mc (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x2390
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_394 with "Hcode"). }
    rewrite (ushp_pc_step 0x394 4). iIntros (h2) "Hrun".
    set (m2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx s3_idx) (Regidx t) _ Ht)).
    assert (Hs1_2 : m2 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hm2 s1_idx ltac:(vm_compute; discriminate))
                  (Hm1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
    assert (Hs2_2 : m2 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hm2 s2_idx ltac:(vm_compute; discriminate))
                  (Hm1 s2_idx ltac:(vm_compute; discriminate)); exact Hs2).
    assert (Hs3_2 : m2 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq m1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    (* ---- 0x398..0x3ae  the entry test and the scan ---- *)
    iApply (wp_kshp_ws_enter 0x398 s2_idx (mword_of_int 1760 : mword 21)
              dq dw s0 len j f nn h2 m2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hjle Hs0 Hs64 Hs1_2 Hs2_2 Hs3_2 Hs2_2
              with "[] [] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { iApply (uis_shp_398 with "Hcode"). }
    { iApply (uis_shp_39c with "Hcode"). }
    { iApply (uis_shp_3a0 with "Hcode"). }
    { iApply (uis_shp_3a2 with "Hcode"). }
    { iApply (uis_shp_3a6 with "Hcode"). }
    { iApply (uis_shp_3a8 with "Hcode"). }
    { iApply (uis_shp_3aa with "Hcode"). }
    { iApply (uis_shp_3ae with "Hcode"). }
    iIntros "Hstr Hws" (h3 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. intros t Ht Hts1 Hts3.
      rewrite (Hpres t Ht Hts1) (Hm2 t Hts3). exact (Hm1 t Hts3).
    - iPureIntro. exact Hret.
  Qed.

  (* [*eq = s], then the trailing scan.  0x38c is reached TWO ways -- from
     0x388's [beqz s6] falling through, and from 0x424's [bnez s6] being
     taken -- so it is stated once. *)
  Local Lemma wp_kshp_gtk_eqst (dq dw : dfrac) (s0 eqp : Z) (len j : nat)
      (f : nat -> bv 8) (v0 : mword 64) (nn : nat)
      (h : CpuId) (mc : regfile) :
    (j <= len)%nat -> 0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < eqp -> eqp mod 8 = 0 -> eqp + 8 < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int eqp ->
    shp_code γt -∗
    uword γd eqp v0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x38c) (2 + nn) -∗
    (uword γd eqp (mword_of_int (s0 + Z.of_nat j)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Heq0 Heq8 Heqsz Hs1 Hs2 Hs6.
    iIntros "#Hcode Hcell Hstr Hws Hrun Hcont".
    (* ---- 0x38c  sd s1,0(s6)  --  *eq = s ---- *)
    iApply (wp_uk_sd γt γd γs γfd h mc (mword_of_int 0x38c)
              (mword_of_int 0 : mword 12) s6_idx s1_idx eqp v0 (2 + nn)
              ltac:(rewrite Hs6 (uint_moi eqp ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Heq8
              with "[] Hcell Hrun").
    { iApply (uis_shp_38c with "Hcode"). }
    iIntros "Hcell". rewrite Hs1.
    rewrite (ushp_pc_step 0x38c 4). iIntros (h1) "Hrun".
    iApply (wp_kshp_gtk_ws2 dq dw s0 len j f nn h1 mc
              Hjle Hs0 Hs64 Hs1 Hs2 with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hcell Hstr Hws [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* 0x388: [if(eq) *eq = s], the NUL and symbol-free arms' way in. *)
  Local Lemma wp_kshp_gtk_388 (dq dw : dfrac) (s0 eqp : Z) (len j : nat)
      (f : nat -> bv 8) (v0 : mword 64) (nn : nat)
      (h : CpuId) (mc : regfile) :
    (j <= len)%nat -> 0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int eqp ->
    shp_code γt -∗
    ushp_cell eqp v0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x388) (2 + nn) -∗
    (ushp_cell eqp (mword_of_int (s0 + Z.of_nat j)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Hs1 Hs2 Hs6.
    iIntros "#Hcode Hcell Hstr Hws Hrun Hcont".
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    iDestruct "Hcell" as "[ %Hnull | [%Hrng Hw] ]".
    { (* eq == 0: the store is skipped *)
      assert (Htk : true = uv_btaken BEQ (mc !!! Regidx s6_idx)
                             (mc !!! Regidx x0_idx)).
      { cbn [uv_btaken]. rewrite Hs6 Hx0 Hnull.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x388)
                (mword_of_int 8 : mword 13) x0_idx s6_idx BEQ true
                (mword_of_int 0x390) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_388 with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply (wp_kshp_gtk_ws2 dq dw s0 len j f nn h1 mc
                Hjle Hs0 Hs64 Hs1 Hs2 with "Hcode Hstr Hws Hrun").
      iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
      iApply ("Hcont" with "[] Hstr Hws [] [] Hrun").
      - iLeft. iPureIntro. exact Hnull.
      - iPureIntro. exact Hpres.
      - iPureIntro. exact Hret. }
    (* eq != 0: the store runs *)
    destruct Hrng as [ Heq0 [ Heq8 Heqsz ] ].
    assert (Htk : false = uv_btaken BEQ (mc !!! Regidx s6_idx)
                            (mc !!! Regidx x0_idx)).
    { cbn [uv_btaken]. rewrite Hs6 Hx0.
      rewrite (moi_eq_zero eqp ltac:(unfold Z64 in *; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x388)
              (mword_of_int 8 : mword 13) x0_idx s6_idx BEQ false
              (mword_of_int 0x390) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_388 with "Hcode"). }
    rewrite (ushp_pc_step 0x388 4). iIntros (h1) "Hrun".
    iApply (wp_kshp_gtk_eqst dq dw s0 eqp len j f v0 nn h1 mc
              Hjle Hs0 Hs64 Heq0 Heq8 Heqsz Hs1 Hs2 Hs6
              with "Hcode Hw Hstr Hws Hrun").
    iIntros "Hw Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "[Hw] Hstr Hws [] [] Hrun").
    - iRight. iSplitR; [ iPureIntro; split; [ exact Heq0 | split; assumption ]
                       | iExact "Hw" ].
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* 0x424: the SAME [if(eq)] test, at the copy the default arm reaches when
     the token ran to [es].  The cursor is already at the end there, so the
     [c.j 0x3b0] that skips the trailing scan skips a no-op -- which is why
     this lemma is stated at [j = len] and lands on the same postcondition. *)
  Local Lemma wp_kshp_gtk_424 (dq dw : dfrac) (s0 eqp : Z) (len : nat)
      (f : nat -> bv 8) (v0 : mword 64) (nn : nat)
      (h : CpuId) (mc : regfile) :
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int eqp ->
    shp_code γt -∗
    ushp_cell eqp v0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x424) (2 + nn) -∗
    (ushp_cell eqp (mword_of_int (s0 + Z.of_nat len)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs0 Hs64 Hs1 Hs2 Hs6.
    iIntros "#Hcode Hcell Hstr Hws Hrun Hcont".
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Etl : (s0 + Z.of_nat (len + ushp_skipws (len - len) len f))
                  = (s0 + Z.of_nat len)).
    { assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
      rewrite (ushp_skipws_zero len f). f_equal. lia. }
    iDestruct "Hcell" as "[ %Hnull | [%Hrng Hw] ]".
    { (* eq == 0: straight to 0x3b0 ---- *)
      assert (Htk : false = uv_btaken BNE (mc !!! Regidx s6_idx)
                              (mc !!! Regidx x0_idx)).
      { cbn [uv_btaken]. rewrite Hs6 Hx0 Hnull.
        rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x424)
                (mword_of_int 8040 : mword 13) x0_idx s6_idx BNE false
                (mword_of_int 0x38c) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_424 with "Hcode"). }
      rewrite (ushp_pc_step 0x424 4). iIntros (h1) "Hrun".
      (* ---- 0x428  c.j 0x3b0 ---- *)
      iApply (wp_uk_cj γt γd γs γfd h1 mc (mword_of_int 0x428)
                (mword_of_int 1988 : mword 11) (mword_of_int 0x3b0) (2 + nn)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_428 with "Hcode"). }
      iIntros (h2) "Hrun".
      iApply ("Hcont" with "[] Hstr Hws [] [] Hrun").
      - iLeft. iPureIntro. exact Hnull.
      - iPureIntro. intros t _ _ _. reflexivity.
      - iPureIntro. exact Hs1. }
    (* eq != 0: the store runs, then the (empty) trailing scan *)
    destruct Hrng as [ Heq0 [ Heq8 Heqsz ] ].
    assert (Htk : true = uv_btaken BNE (mc !!! Regidx s6_idx)
                           (mc !!! Regidx x0_idx)).
    { cbn [uv_btaken]. rewrite Hs6 Hx0.
      rewrite (moi_neq_zero eqp ltac:(unfold Z64 in *; lia)).
      assert (Hz : (eqp =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Hz. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x424)
              (mword_of_int 8040 : mword 13) x0_idx s6_idx BNE true
              (mword_of_int 0x38c) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_424 with "Hcode"). }
    iIntros (h1) "Hrun".
    iApply (wp_kshp_gtk_eqst dq dw s0 eqp len len f v0 nn h1 mc
              ltac:(lia) Hs0 Hs64 Heq0 Heq8 Heqsz Hs1 Hs2 Hs6
              with "Hcode Hw Hstr Hws Hrun").
    iIntros "Hw Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    rewrite Etl in Hret.
    iApply ("Hcont" with "[Hw] Hstr Hws [] [] Hrun").
    - iRight. iSplitR; [ iPureIntro; split; [ exact Heq0 | split; assumption ]
                       | iExact "Hw" ].
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* gettoken's epilogue, 0x3b6..0x3c8: the EIGHT restores, the pop and the
     [c.jr].  [wp_kshp_peek_epi]'s twin at k = 8, j = 8 -- so the frame has
     no locals at all and [ushp_frame_join] puts it back at [n = 0]. *)
  Local Lemma wp_kshp_gtk_epi (sp0 spl : mword 64) (vals : nat -> mword 64)
      (nn : nat) :
    forall (h : CpuId) (me : regfile),
    uint sp0 mod 8 = 0 -> 64 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 64 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 7 : mword 6);
                       (s0_idx, mword_of_int 6 : mword 6);
                       (s1_idx, mword_of_int 5 : mword 6);
                       (s2_idx, mword_of_int 4 : mword 6);
                       (s3_idx, mword_of_int 3 : mword 6);
                       (s4_idx, mword_of_int 2 : mword 6);
                       (s5_idx, mword_of_int 1 : mword 6);
                       (s6_idx, mword_of_int 0 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 0 -∗
    urun γt γd γs γfd h me (mword_of_int 0x3b6) (2 + nn) -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 7 : mword 6);
                             (s0_idx, mword_of_int 6 : mword 6);
                             (s1_idx, mword_of_int 5 : mword 6);
                             (s2_idx, mword_of_int 4 : mword 6);
                             (s3_idx, mword_of_int 3 : mword 6);
                             (s4_idx, mword_of_int 2 : mword 6);
                             (s5_idx, mword_of_int 1 : mword 6);
                             (s6_idx, mword_of_int 0 : mword 6)] vals me))
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
               (s5_idx, mword_of_int 1 : mword 6);
               (s6_idx, mword_of_int 0 : mword 6)] !! i = Some (r, u) ->
              (uint sp0 - 8 * (Z.of_nat i + 1)) = uint spn + uoff_sdsp u /\
              (uint sp0 - 8 * (Z.of_nat i + 1)) mod 8 = 0 /\
              unot_sp r /\ uint r <> 0).
    { intros i r u Hi.
      destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]]; cbn in Hi;
        try discriminate; injection Hi as Hr Hu0; subst;
        (split;
         [ rewrite Hspu; vm_compute uoff_sdsp; lia
         | split;
           [ exact (ushp_slot_al (uint sp0) _ Hal8)
           | split; [ unfold unot_sp; vm_compute; discriminate
                    | vm_compute; discriminate ] ] ]). }
    (* ---- 0x3b6..0x3c4  the eight restores ---- *)
    iApply (wp_kshp_restore spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6);
               (s6_idx, mword_of_int 0 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x3b6 | 1%nat => 0x3b8
                              | 2%nat => 0x3ba | 3%nat => 0x3bc
                              | 4%nat => 0x3be | 5%nat => 0x3c0
                              | 6%nat => 0x3c2 | 7%nat => 0x3c4
                              | _ => 0x3c6 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h me Hsp
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              Hoff
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_3b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3c2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3c4 with "Hcode") | done ]. }
    iIntros "Hsl" (h1) "Hrun". cbn [length].
    set (mr := ushp_spillback
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6);
                  (s6_idx, mword_of_int 0 : mword 6)] vals me).
    assert (Hspr : mr !!! Regidx csp_rs1 = spn).
    { rewrite /mr (ushp_spillback_ne
                     [(ra_idx, mword_of_int 7 : mword 6);
                      (s0_idx, mword_of_int 6 : mword 6);
                      (s1_idx, mword_of_int 5 : mword 6);
                      (s2_idx, mword_of_int 4 : mword 6);
                      (s3_idx, mword_of_int 3 : mword 6);
                      (s4_idx, mword_of_int 2 : mword 6);
                      (s5_idx, mword_of_int 1 : mword 6);
                      (s6_idx, mword_of_int 0 : mword 6)] vals me csp_rs1
                     ltac:(intros i r u Hi;
                           destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                           cbn in Hi; try discriminate;
                           injection Hi as Hr Hu0; subst;
                           vm_compute; discriminate)).
      exact Hsp. }
    assert (Hrar : mr !!! Regidx ra_idx = vals 0%nat).
    { rewrite /mr. cbn [ushp_spillback fst].
      rewrite (upd_ne _ (Regidx s6_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
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
    (* ---- 0x3c6  c.addi16sp sp,sp,64 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h1 mr (mword_of_int 0x3c6)
              (mword_of_int 4 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hsl Hloc] Hrun").
    { iApply (uis_shp_3c6 with "Hcode"). }
    { rewrite Hspr Hup.
      iApply (ushp_frame_join sp0 spl 0
                [(ra_idx, mword_of_int 7 : mword 6);
                 (s0_idx, mword_of_int 6 : mword 6);
                 (s1_idx, mword_of_int 5 : mword 6);
                 (s2_idx, mword_of_int 4 : mword 6);
                 (s3_idx, mword_of_int 3 : mword 6);
                 (s4_idx, mword_of_int 2 : mword 6);
                 (s5_idx, mword_of_int 1 : mword 6);
                 (s6_idx, mword_of_int 0 : mword 6)]
                vals ltac:(cbn [length]; lia) with "Hsl Hloc"). }
    rewrite Hspr Hup (ushp_pc_step 0x3c6 2). iIntros (h2) "Hrun".
    (* ---- 0x3c8  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h2
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mr)
              (mword_of_int 0x3c8) ra_idx (ret_pc (vals 0%nat)) (8 + (2 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mr (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3c8 with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hrun").
  Qed.

  (* ---- the [*q] store and the switch ------------------------------------ *)

  (* 0x34e: [if(q) *q = s].  It writes NO register, so the continuation gets
     the SAME register file back -- which is what lets the switch below be
     stated at one entry state rather than two. *)
  Local Lemma wp_kshp_gtk_qst (s0 qp : Z) (k : nat) (v0 : mword 64)
      (nn : nat) (h : CpuId) (mc : regfile) :
    0 <= s0 -> s0 + Z.of_nat k < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    mc !!! Regidx s5_idx = mword_of_int qp ->
    shp_code γt -∗
    ushp_cell qp v0 -∗
    urun γt γd γs γfd h mc (mword_of_int 0x34e) (2 + nn) -∗
    (ushp_cell qp (mword_of_int (s0 + Z.of_nat k)) -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h' mc (mword_of_int 0x356) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs0 Hs64 Hs1 Hs5.
    iIntros "#Hcode Hcell Hrun Hcont".
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    iDestruct "Hcell" as "[ %Hnull | [%Hrng Hw] ]".
    { assert (Htk : true = uv_btaken BEQ (mc !!! Regidx s5_idx)
                             (mc !!! Regidx x0_idx)).
      { cbn [uv_btaken]. rewrite Hs5 Hx0 Hnull.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x34e)
                (mword_of_int 8 : mword 13) x0_idx s5_idx BEQ true
                (mword_of_int 0x356) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_34e with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "[] Hrun"). iLeft. iPureIntro. exact Hnull. }
    destruct Hrng as [ Hq0 [ Hq8 Hqsz ] ].
    assert (Htk : false = uv_btaken BEQ (mc !!! Regidx s5_idx)
                            (mc !!! Regidx x0_idx)).
    { cbn [uv_btaken]. rewrite Hs5 Hx0.
      rewrite (moi_eq_zero qp ltac:(unfold Z64 in *; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x34e)
              (mword_of_int 8 : mword 13) x0_idx s5_idx BEQ false
              (mword_of_int 0x356) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_34e with "Hcode"). }
    rewrite (ushp_pc_step 0x34e 4). iIntros (h1) "Hrun".
    (* ---- 0x352  sd s1,0(s5)  --  *q = s ---- *)
    iApply (wp_uk_sd γt γd γs γfd h1 mc (mword_of_int 0x352)
              (mword_of_int 0 : mword 12) s5_idx s1_idx qp v0 (2 + nn)
              ltac:(rewrite Hs5 (uint_moi qp ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hq8
              with "[] Hw Hrun").
    { iApply (uis_shp_352 with "Hcode"). }
    iIntros "Hw". rewrite Hs1.
    rewrite (ushp_pc_step 0x352 4). iIntros (h2) "Hrun".
    iApply ("Hcont" with "[Hw] Hrun").
    iRight. iSplitR; [ iPureIntro; split; [ exact Hq0 | split; assumption ]
                     | iExact "Hw" ].
  Qed.

  (* gettoken's ANSWER, on a line stage 4 accepts: 'a' at a real token and 0
     at the end of the line.  The six symbol arms and the '>' / '>>' arm are
     not weakened away -- they are REFUTED at the branch, from the seven
     numeric disequalities of [ushp_nsym_bv]. *)
  Definition ushp_gettok_res (len : nat) (f : nat -> bv 8) (k : nat) : Z :=
    if bool_decide (k < len)%nat then 97 else 0.

  (* where the token ends: the maximal non-whitespace, non-symbol run *)
  Definition ushp_gettok_end (len : nat) (f : nat -> bv 8) (k : nat) : nat :=
    (k + ushp_toklen (len - k) k f)%nat.

  (* THE SWITCH, 0x356..0x386 and its two out-of-line halves 0x3ca..0x3e8.
     Under [ushp_no_symbols] the eight-arm switch has TWO live arms and the
     byte at the cursor decides which: it is NUL exactly when the cursor has
     reached [es], because a [ustr]'s body bytes are all non-NUL.  Nothing
     here moves the cursor -- s1 is untouched -- and only a4, a5 and s5 are
     written. *)
  Local Lemma wp_kshp_gtk_disp (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (k <= len)%nat -> ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x356) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, Regidx t <> Regidx a4_idx ->
             Regidx t <> Regidx a5_idx -> Regidx t <> Regidx s5_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ (len <= k)%nat ->
             mc' !!! Regidx s5_idx = mword_of_int 0 ⌝ -∗
         urun γt γd γs γfd h' mc'
           (mword_of_int (if bool_decide (k < len)%nat then 0x3ec else 0x388))
           (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkle Hnosym Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnonul.
    iAssert (∃ b : bv 8,
               ⌜ (k < len)%nat -> b = f k ⌝ ∗ ⌜ k = len -> b = ubyte0 ⌝ ∗
               ubyteq γd dq (s0 + Z.of_nat k) b ∗
               (ubyteq γd dq (s0 + Z.of_nat k) b -∗ ustr γd dq s0 len f))%I
      with "[Hstr]" as (b Hbk Hb0) "[Hb Hcl]".
    { destruct (Nat.eq_dec k len) as [ He | Hne ].
      - iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
        rewrite He. iExists ubyte0.
        iSplitR; [ iPureIntro; intro; lia | ].
        iSplitR; [ iPureIntro; intro; reflexivity | ].
        iFrame "Hb Hcl".
      - iDestruct (ustr_byte γd dq s0 len f k ltac:(lia) with "Hstr")
          as "[Hb Hcl]".
        iExists (f k).
        iSplitR; [ iPureIntro; intro; reflexivity | ].
        iSplitR; [ iPureIntro; intro; lia | ].
        iFrame "Hb Hcl". }
    pose proof (ushp_byte_rng b) as Hvb.
    assert (Hz : k = len -> bv_unsigned b = 0)
      by (intro He; rewrite (Hb0 He); vm_compute; reflexivity).
    assert (Hnz : (k < len)%nat -> bv_unsigned b <> 0).
    { intros Hk Hzz. apply (Hnonul k Hk). rewrite <- (Hbk Hk).
      apply bv_eq. rewrite Hzz. vm_compute; reflexivity. }
    assert (Hns : (k < len)%nat -> ushp_is_sym b = false)
      by (intros Hk; rewrite (Hbk Hk); exact (Hnosym k Hk)).
    (* ---- 0x356  lbu a5,0(s1) ---- *)
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int 0x356)
              (mword_of_int 0 : mword 12) s1_idx a5_idx dq
              (s0 + Z.of_nat k) b (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat k)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_356 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x356 4). iIntros (h1) "Hrun".
    set (n1 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 (b : mword 8)
                                     : mword 64)]> mc).
    assert (Hn1 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    n1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Ha5_1 : n1 !!! Regidx a5_idx = mword_of_int (bv_unsigned b)).
    { rewrite (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 (b : mword 8) : mword 64))).
      exact (zext8_moi b). }
    (* ---- 0x35a  sext.w s5,a5 -- [ret = *s] ---- *)
    iApply (wp_uk_addiw γt γd γs γfd h1 n1 (mword_of_int 0x35a)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int (bv_unsigned b)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry;
                    exact (ushp_sextw_byte (bv_unsigned b) Hvb))
              with "[] Hrun").
    { iApply (uis_shp_35a with "Hcode"). }
    rewrite (ushp_pc_step 0x35a 4). iIntros (h2) "Hrun".
    set (n2 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b)
                                     : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Hs5_2 : n2 !!! Regidx s5_idx = mword_of_int (bv_unsigned b))
      by exact (upd_eq n1 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b) : mword 64))).
    assert (Ha5_2 : n2 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hn2 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_1).
    (* ---- 0x35e  li a4,60 ---- *)
    iApply (wp_uk_li γt γd γs γfd h2 n2 (mword_of_int 0x35e)
              (mword_of_int 60 : mword 12) a4_idx (mword_of_int 60) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_35e with "Hcode"). }
    rewrite (ushp_pc_step 0x35e 4). iIntros (h3) "Hrun".
    set (n3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 60 : mword 64)]> n2).
    assert (Hn3 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n3 !!! Regidx t = n2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n2 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_3 : n3 !!! Regidx a4_idx = mword_of_int 60)
      by exact (upd_eq n2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 60 : mword 64))).
    assert (Ha5_3 : n3 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_2).
    assert (Hs5_3 : n3 !!! Regidx s5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hn3 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_2).
    (* ---- 0x362  bltu a4,a5,0x3ca -- '<' and above go out of line ---- *)
    destruct (Z_lt_ge_dec 60 (bv_unsigned b)) as [ Hhi | Hlo ].
    { (* the byte is ABOVE '<': it is '>', '|', or an ordinary character *)
      assert (Hklt : (k < len)%nat).
      { destruct (Nat.eq_dec k len) as [ He | Hne2 ];
          [ exfalso; pose proof (Hz He); lia | lia ]. }
      destruct (ushp_nsym_bv b (Hns Hklt))
        as (N60 & N124 & N62 & N38 & N59 & N40 & N41).
      assert (Htk : true = uv_btaken BLTU (n3 !!! Regidx a4_idx)
                             (n3 !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha4_3 Ha5_3.
        rewrite (moi_lt_u 60 (bv_unsigned b) ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.ltb_lt. lia. }
      iApply (wp_uk_btype γt γd γs γfd h3 n3 (mword_of_int 0x362)
                (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU true
                (mword_of_int 0x3ca) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_362 with "Hcode"). }
      iIntros (h4) "Hrun".
      (* ---- 0x3ca  li a4,62 ---- *)
      iApply (wp_uk_li γt γd γs γfd h4 n3 (mword_of_int 0x3ca)
                (mword_of_int 62 : mword 12) a4_idx (mword_of_int 62) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3ca with "Hcode"). }
      rewrite (ushp_pc_step 0x3ca 4). iIntros (h5) "Hrun".
      set (n4 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 62 : mword 64)]> n3).
      assert (Hn4 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                      n4 !!! Regidx t = n3 !!! Regidx t)
        by (intros t Ht; exact (upd_ne n3 (Regidx a4_idx) (Regidx t) _ Ht)).
      assert (Ha4_4 : n4 !!! Regidx a4_idx = mword_of_int 62)
        by exact (upd_eq n3 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 62 : mword 64))).
      assert (Ha5_4 : n4 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
        by (rewrite (Hn4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
      (* ---- 0x3ce  bne a5,a4,0x3e4 -- NOT '>' ---- *)
      assert (Htk2 : true = uv_btaken BNE (n4 !!! Regidx a5_idx)
                              (n4 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha4_4 Ha5_4.
        rewrite (ushp_moi_neq (bv_unsigned b) 62 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        assert (Hq : (bv_unsigned b =? 62) = false)
          by (apply Z.eqb_neq; exact N62).
        rewrite Hq. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h5 n4 (mword_of_int 0x3ce)
                (mword_of_int 22 : mword 13) a4_idx a5_idx BNE true
                (mword_of_int 0x3e4) (2 + nn)
                Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3ce with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0x3e4  li a4,124 ---- *)
      iApply (wp_uk_li γt γd γs γfd h6 n4 (mword_of_int 0x3e4)
                (mword_of_int 124 : mword 12) a4_idx (mword_of_int 124)
                (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3e4 with "Hcode"). }
      rewrite (ushp_pc_step 0x3e4 4). iIntros (h7) "Hrun".
      set (n5 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 124 : mword 64)]> n4).
      assert (Hn5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                      n5 !!! Regidx t = n4 !!! Regidx t)
        by (intros t Ht; exact (upd_ne n4 (Regidx a4_idx) (Regidx t) _ Ht)).
      assert (Ha4_5 : n5 !!! Regidx a4_idx = mword_of_int 124)
        by exact (upd_eq n4 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 124 : mword 64))).
      assert (Ha5_5 : n5 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
        by (rewrite (Hn5 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_4).
      (* ---- 0x3e8  beq a5,a4,0x386 -- NOT '|', so the DEFAULT arm ---- *)
      assert (Htk3 : false = uv_btaken BEQ (n5 !!! Regidx a5_idx)
                               (n5 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha4_5 Ha5_5.
        rewrite (moi_eq_vec (bv_unsigned b) 124 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact N124. }
      iApply (wp_uk_btype γt γd γs γfd h7 n5 (mword_of_int 0x3e8)
                (mword_of_int 8094 : mword 13) a4_idx a5_idx BEQ false
                (mword_of_int 0x386) (2 + nn)
                Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_3e8 with "Hcode"). }
      rewrite (ushp_pc_step' 0x3e8 4 0x3ec ltac:(reflexivity)).
      iIntros (h8) "Hrun".
      rewrite (bool_decide_eq_true_2 (k < len)%nat Hklt).
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros t Ht4 Ht5 Hts5.
        rewrite (Hn5 t Ht4) (Hn4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5).
        exact (Hn1 t Ht5).
      - iPureIntro. intro Hge. lia. }
    (* the byte is AT MOST '<' *)
    assert (Hle58 : bv_unsigned b <= 58).
    { destruct (Nat.eq_dec k len) as [ He | Hne2 ].
      - pose proof (Hz He). lia.
      - destruct (ushp_nsym_bv b (Hns ltac:(lia)))
          as (N60 & N124 & N62 & N38 & N59 & N40 & N41). lia. }
    assert (Htk : false = uv_btaken BLTU (n3 !!! Regidx a4_idx)
                            (n3 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Ha4_3 Ha5_3.
      rewrite (moi_lt_u 60 (bv_unsigned b) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uk_btype γt γd γs γfd h3 n3 (mword_of_int 0x362)
              (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU false
              (mword_of_int 0x3ca) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_362 with "Hcode"). }
    rewrite (ushp_pc_step 0x362 4). iIntros (h4) "Hrun".
    (* ---- 0x366  li a4,58 ---- *)
    iApply (wp_uk_li γt γd γs γfd h4 n3 (mword_of_int 0x366)
              (mword_of_int 58 : mword 12) a4_idx (mword_of_int 58) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_366 with "Hcode"). }
    rewrite (ushp_pc_step 0x366 4). iIntros (h5) "Hrun".
    set (p4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 58 : mword 64)]> n3).
    assert (Hp4 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    p4 !!! Regidx t = n3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n3 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Hb4_4 : p4 !!! Regidx a4_idx = mword_of_int 58)
      by exact (upd_eq n3 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 58 : mword 64))).
    assert (Hb5_4 : p4 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hp4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
    assert (Hb55_4 : p4 !!! Regidx s5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hp4 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_3).
    (* ---- 0x36a  bltu a4,a5,0x386 -- ';' and '<' are refuted ---- *)
    assert (Htk2 : false = uv_btaken BLTU (p4 !!! Regidx a4_idx)
                             (p4 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Hb4_4 Hb5_4.
      rewrite (moi_lt_u 58 (bv_unsigned b) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uk_btype γt γd γs γfd h5 p4 (mword_of_int 0x36a)
              (mword_of_int 28 : mword 13) a5_idx a4_idx BLTU false
              (mword_of_int 0x386) (2 + nn)
              Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_36a with "Hcode"). }
    rewrite (ushp_pc_step 0x36a 4). iIntros (h6) "Hrun".
    (* ---- 0x36e  c.beqz a5,0x388 -- THE NUL ARM ---- *)
    destruct (Z.eq_dec (bv_unsigned b) 0) as [ Hbz | Hbnz ].
    { assert (Hkeq : k = len).
      { destruct (Nat.eq_dec k len) as [ He | Hne2 ];
          [ exact He | exfalso; exact (Hnz ltac:(lia) Hbz) ]. }
      assert (Htk3 : true = eq_vec (p4 !!! Regidx a5_idx) zero_reg).
      { rewrite Hb5_4 Hbz.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz γt γd γs γfd h6 p4 (mword_of_int 0x36e)
                (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0x388) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_36e with "Hcode"). }
      iIntros (h7) "Hrun".
      rewrite (bool_decide_eq_false_2 (k < len)%nat ltac:(lia)).
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros t Ht4 Ht5 Hts5.
        rewrite (Hp4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5). exact (Hn1 t Ht5).
      - iPureIntro. intros _. rewrite Hb55_4 Hbz. reflexivity. }
    (* an ORDINARY character: the default arm, through the range test *)
    assert (Hklt : (k < len)%nat).
    { destruct (Nat.eq_dec k len) as [ He | Hne2 ];
        [ exfalso; exact (Hbnz (Hz He)) | lia ]. }
    destruct (ushp_nsym_bv b (Hns Hklt))
      as (N60 & N124 & N62 & N38 & N59 & N40 & N41).
    assert (Htk3 : false = eq_vec (p4 !!! Regidx a5_idx) zero_reg).
    { rewrite Hb5_4.
      rewrite (moi_eq_zero (bv_unsigned b) ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. exact Hbnz. }
    iApply (wp_uk_cbeqz γt γd γs γfd h6 p4 (mword_of_int 0x36e)
              (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3)
              a5_idx false (mword_of_int 0x388) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_36e with "Hcode"). }
    rewrite (ushp_pc_step 0x36e 2). iIntros (h7) "Hrun".
    (* ---- 0x370  li a4,38 ---- *)
    iApply (wp_uk_li γt γd γs γfd h7 p4 (mword_of_int 0x370)
              (mword_of_int 38 : mword 12) a4_idx (mword_of_int 38) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_370 with "Hcode"). }
    rewrite (ushp_pc_step 0x370 4). iIntros (h8) "Hrun".
    set (p5 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 38 : mword 64)]> p4).
    assert (Hp5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    p5 !!! Regidx t = p4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p4 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Hb4_5 : p5 !!! Regidx a4_idx = mword_of_int 38)
      by exact (upd_eq p4 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 38 : mword 64))).
    assert (Hb5_5 : p5 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hp5 a5_idx ltac:(vm_compute; discriminate)); exact Hb5_4).
    (* ---- 0x374  beq a5,a4,0x386 -- '&' is refuted ---- *)
    assert (Htk4 : false = uv_btaken BEQ (p5 !!! Regidx a5_idx)
                             (p5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Hb4_5 Hb5_5.
      rewrite (moi_eq_vec (bv_unsigned b) 38 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. exact N38. }
    iApply (wp_uk_btype γt γd γs γfd h8 p5 (mword_of_int 0x374)
              (mword_of_int 18 : mword 13) a4_idx a5_idx BEQ false
              (mword_of_int 0x386) (2 + nn)
              Htk4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_374 with "Hcode"). }
    rewrite (ushp_pc_step 0x374 4). iIntros (h9) "Hrun".
    (* ---- 0x378  addiw a5,a5,-40 ---- *)
    iApply (wp_uk_addiw γt γd γs γfd h9 p5 (mword_of_int 0x378)
              (mword_of_int 4056 : mword 12) a5_idx a5_idx
              (sign_extend' 64
                 (subrange_vec_dec
                    (add_vec (mword_of_int (bv_unsigned b) : mword 64)
                       (sign_extend' 64 (mword_of_int 4056 : mword 12)))
                    31 0 : mword 32))
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hb5_5; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_378 with "Hcode"). }
    rewrite (ushp_pc_step 0x378 4). iIntros (h10) "Hrun".
    set (p6 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64
                         (subrange_vec_dec
                            (add_vec (mword_of_int (bv_unsigned b) : mword 64)
                               (sign_extend' 64
                                  (mword_of_int 4056 : mword 12)))
                            31 0 : mword 32))]> p5).
    assert (Hp6 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    p6 !!! Regidx t = p5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p5 (Regidx a5_idx) (Regidx t) _ Ht)).
    (* ---- 0x37c  zext.b a5,a5 -- the wrap is undone here ---- *)
    iApply (wp_uk_andi γt γd γs γfd h10 p6 (mword_of_int 0x37c)
              (mword_of_int 255 : mword 12) a5_idx a5_idx
              (mword_of_int ((bv_unsigned b - 40) mod 256)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq p5 (Regidx a5_idx) _); symmetry;
                    exact (ushp_addiw_andi (bv_unsigned b) Hvb))
              with "[] Hrun").
    { iApply (uis_shp_37c with "Hcode"). }
    rewrite (ushp_pc_step 0x37c 4). iIntros (h11) "Hrun".
    set (p7 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int ((bv_unsigned b - 40) mod 256)
                       : mword 64)]> p6).
    assert (Hp7 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    p7 !!! Regidx t = p6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p6 (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Hb5_7 : p7 !!! Regidx a5_idx
                    = mword_of_int ((bv_unsigned b - 40) mod 256))
      by exact (upd_eq p6 (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int ((bv_unsigned b - 40) mod 256)
                      : mword 64))).
    (* ---- 0x380  c.li a4,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli γt γd γs γfd h11 p7 (mword_of_int 0x380)
              (mword_of_int 1 : mword 6) a4_idx (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_380 with "Hcode"). }
    rewrite (ushp_pc_step 0x380 2). iIntros (h12) "Hrun".
    set (p8 := <[Regidx a4_idx
                 := regval_into_reg (sign_extend' 64
                                       (mword_of_int 1 : mword 6)
                                     : mword 64)]> p7).
    assert (Hp8 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    p8 !!! Regidx t = p7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p7 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Hb4_8 : p8 !!! Regidx a4_idx = mword_of_int 1).
    { rewrite (upd_eq p7 (Regidx a4_idx)
                 (regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6)
                                   : mword 64))).
      exact E1. }
    assert (Hb5_8 : p8 !!! Regidx a5_idx
                    = mword_of_int ((bv_unsigned b - 40) mod 256))
      by (rewrite (Hp8 a5_idx ltac:(vm_compute; discriminate)); exact Hb5_7).
    (* ---- 0x382  bltu a4,a5,0x3ec -- '(' and ')' are the only 0 and 1 --- *)
    assert (Hgt : 1 < (bv_unsigned b - 40) mod 256).
    { destruct (Z_lt_ge_dec (bv_unsigned b) 40) as [ Hlt40 | Hge40 ].
      - assert (E : (bv_unsigned b - 40) mod 256 = bv_unsigned b + 216).
        { replace (bv_unsigned b - 40)
            with ((bv_unsigned b + 216) + (-1) * 256) by lia.
          rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
        rewrite E. lia.
      - rewrite (Z.mod_small (bv_unsigned b - 40) 256 ltac:(lia)). lia. }
    assert (Hmr : 0 <= (bv_unsigned b - 40) mod 256 < 256)
      by (apply Z.mod_pos_bound; lia).
    assert (Htk5 : true = uv_btaken BLTU (p8 !!! Regidx a4_idx)
                            (p8 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Hb4_8 Hb5_8.
      rewrite (moi_lt_u 1 ((bv_unsigned b - 40) mod 256)
                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_lt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h12 p8 (mword_of_int 0x382)
              (mword_of_int 106 : mword 13) a5_idx a4_idx BLTU true
              (mword_of_int 0x3ec) (2 + nn)
              Htk5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_382 with "Hcode"). }
    iIntros (h13) "Hrun".
    rewrite (bool_decide_eq_true_2 (k < len)%nat Hklt).
    iApply ("Hcont" with "Hstr [] [] Hrun").
    - iPureIntro. intros t Ht4 Ht5 Hts5.
      rewrite (Hp8 t Ht4) (Hp7 t Ht5) (Hp6 t Ht5) (Hp5 t Ht4) (Hp4 t Ht4)
              (Hn3 t Ht4) (Hn2 t Hts5). exact (Hn1 t Ht5).
    - iPureIntro. intro Hge. lia.
  Qed.

  (* ---- the common landing, 0x3b0..0x3c8 --------------------------------- *)

  (* All THREE ways out of the switch converge here -- the NUL arm, the
     default arm's whitespace exit and its end-of-line exit -- so [*ps = s],
     [a0 = ret] and the epilogue are walked once, and so is the [ucallee_
     saved] read-back the caller needs.  Every callee-saved register except
     sp is either spilled (ra, s0..s6, restored by [ushp_spillback] to the
     value it had at entry) or never written at all (gp, tp, s7..s11), which
     is what makes that read-back a theorem rather than a promise. *)
  Local Lemma wp_kshp_gtk_fin (m : regfile) (sp0 spl : mword 64)
      (vals : nat -> mword 64) (ps res cur : Z) (w0 : mword 64) (nn : nat)
      (h : CpuId) (me : regfile) :
    uint sp0 mod 8 = 0 -> 64 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    vals = (fun i : nat => match i with
                           | 0%nat => m !!! Regidx ra_idx
                           | 1%nat => m !!! Regidx s0_idx
                           | 2%nat => m !!! Regidx s1_idx
                           | 3%nat => m !!! Regidx s2_idx
                           | 4%nat => m !!! Regidx s3_idx
                           | 5%nat => m !!! Regidx s4_idx
                           | 6%nat => m !!! Regidx s5_idx
                           | _ => m !!! Regidx s6_idx end) ->
    sp0 = m !!! Regidx csp_rs1 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    me !!! Regidx s4_idx = mword_of_int ps ->
    me !!! Regidx s1_idx = mword_of_int cur ->
    me !!! Regidx s5_idx = mword_of_int res ->
    (forall t : mword 5, ucallee_saved_idx t = true ->
       Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
       Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
       Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
       Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
       me !!! Regidx t = m !!! Regidx t) ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 7 : mword 6);
                       (s0_idx, mword_of_int 6 : mword 6);
                       (s1_idx, mword_of_int 5 : mword 6);
                       (s2_idx, mword_of_int 4 : mword 6);
                       (s3_idx, mword_of_int 3 : mword 6);
                       (s4_idx, mword_of_int 2 : mword 6);
                       (s5_idx, mword_of_int 1 : mword 6);
                       (s6_idx, mword_of_int 0 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 0 -∗
    urun γt γd γs γfd h me (mword_of_int 0x3b0) (2 + nn) -∗
    (uword γd ps (mword_of_int cur) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int res ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hal8 Hlo Hhi Hsplu Hps0 Hps8 Hpssz Hvals Hsp0 Hsp Hs4 Hs1 Hs5
           Hkeep.
    iIntros "#Hcode Hcur Hsl Hloc Hrun Hcont".
    (* ---- 0x3b0  sd s1,0(s4)  --  *ps = s ---- *)
    iApply (wp_uk_sd γt γd γs γfd h me (mword_of_int 0x3b0)
              (mword_of_int 0 : mword 12) s4_idx s1_idx ps w0 (2 + nn)
              ltac:(rewrite Hs4 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hps8
              with "[] Hcur Hrun").
    { iApply (uis_shp_3b0 with "Hcode"). }
    iIntros "Hcur". rewrite Hs1.
    rewrite (ushp_pc_step 0x3b0 4). iIntros (h1) "Hrun".
    (* ---- 0x3b4  c.mv a0,s5  -- the return value ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 me (mword_of_int 0x3b4) a0_idx s5_idx
              (mword_of_int res) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5; symmetry; exact (ushp_mv_val res))
              with "[] Hrun").
    { iApply (uis_shp_3b4 with "Hcode"). }
    rewrite (ushp_pc_step 0x3b4 2). iIntros (h2) "Hrun".
    set (mg := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int res : mword 64)]> me).
    assert (Hmg : forall t : mword 5, Regidx t <> Regidx a0_idx ->
                    mg !!! Regidx t = me !!! Regidx t)
      by (intros t Ht; exact (upd_ne me (Regidx a0_idx) (Regidx t) _ Ht)).
    assert (Hspg : mg !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by (rewrite (Hmg csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp).
    (* ---- 0x3b6..0x3c8  the epilogue ---- *)
    iApply (wp_kshp_gtk_epi sp0 spl vals nn h2 mg
              Hal8 Hlo Hhi Hsplu Hspg with "Hcode Hsl Hloc Hrun").
    iIntros (h3) "Hrun".
    subst vals.
    iApply ("Hcont" with "Hcur [] [] Hrun").
    - iPureIntro. intros q Hq. cbn [ushp_spillback fst].
      destruct (Z.eq_dec (uint q) 2) as [ E2 | E2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite E2; vm_compute; reflexivity)).
        rewrite (upd_eq _ (Regidx csp_rs1) (regval_into_reg sp0)).
        exact Hsp0. }
      assert (Hq2 : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
            assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
            rewrite Hc; exact E2).
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx q) _ Hq2).
      destruct (Z.eq_dec (uint q) 22) as [ E22 | E22 ].
      { rewrite (ushp_ridx_eq q s6_idx
                   ltac:(rewrite E22; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s6_idx)
                 (regval_into_reg (m !!! Regidx s6_idx))). }
      assert (Hq22 : Regidx q <> Regidx s6_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s6_idx = 22) by (vm_compute; reflexivity);
            rewrite Hc; exact E22).
      rewrite (upd_ne _ (Regidx s6_idx) (Regidx q) _ Hq22).
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
      rewrite (Hmg q (ushp_cs_ne q a0_idx Hq
                        ltac:(vm_compute; reflexivity))).
      exact (Hkeep q Hq Hq2 Hq8 Hq9 Hq18 Hq19 Hq20 Hq21 Hq22).
    - iPureIntro. cbn [ushp_spillback fst].
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s6_idx) (Regidx a0_idx) _
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
      exact (upd_eq me (Regidx a0_idx)
               (regval_into_reg (mword_of_int res : mword 64))).
  Qed.

  (* ---- gettoken, the whole function ------------------------------------- *)

  (* where the cursor ends up: past the token, then past the whitespace
     after it.  At the end of the line both runs are empty, so the same
     expression covers the NUL arm. *)
  Definition ushp_gettok_fin (len : nat) (f : nat -> bv 8) (k : nat) : nat :=
    let e := ushp_gettok_end len f k in (e + ushp_skipws (len - e) e f)%nat.

  Lemma wp_kshp_gettoken (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps qp eqp s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 wq weq : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int qp ->
    m !!! Regidx a3_idx = mword_of_int eqp ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ushp_cell qp wq -∗
    ushp_cell eqp weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.gettoken) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int
          (s0 + Z.of_nat
                  (ushp_gettok_fin len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ushp_cell qp
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ushp_cell eqp
       (mword_of_int
          (s0 + Z.of_nat
                  (ushp_gettok_end len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushp_gettok_res len f
                    (off + ushp_skipws (len - off) off f)) ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    rewrite shpp_gettoken.
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
    (* ---- 0x310  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x310)
              (mword_of_int 60 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_310 with "Hcode"). }
    rewrite (ushp_pc_step 0x310 2). iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall t : mword 5, Regidx t <> Regidx csp_rs1 ->
                    m1 !!! Regidx t = m !!! Regidx t)
      by (intros t Ht; exact (upd_ne m (Regidx csp_rs1) (Regidx t) _ Ht)).
    set (spl := (mword_of_int (uint sp0 - 64) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 64)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 0
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6);
                  (s6_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | 6%nat => m !!! Regidx s5_idx
                   | _ => m !!! Regidx s6_idx end).
    (* ---- 0x312..0x320  the eight spills ---- *)
    iApply (wp_kshp_spill spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6);
               (s6_idx, mword_of_int 0 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x312 | 1%nat => 0x314
                              | 2%nat => 0x316 | 3%nat => 0x318
                              | 4%nat => 0x31a | 5%nat => 0x31c
                              | 6%nat => 0x31e | 7%nat => 0x320
                              | _ => 0x322 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_312 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_314 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_316 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_318 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_320 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x322  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_kshp_fp h2 m1 0x322 (mword_of_int 16 : mword 8) (2 + nn)
              with "[] Hrun").
    { iApply (uis_shp_322 with "Hcode"). }
    iIntros (h3 v322) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v322]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx s0_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx s0_idx) (Regidx t) _ Ht)).
    (* ---- 0x324  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x324) s4_idx a0_idx
              (mword_of_int ps) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_324 with "Hcode"). }
    rewrite (ushp_pc_step 0x324 2). iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall t : mword 5, Regidx t <> Regidx s4_idx ->
                    m3 !!! Regidx t = m2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m2 (Regidx s4_idx) (Regidx t) _ Ht)).
    (* ---- 0x326  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m3 (mword_of_int 0x326) s2_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_326 with "Hcode"). }
    rewrite (ushp_pc_step 0x326 2). iIntros (h5) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64)]> m3).
    assert (Hm4 : forall t : mword 5, Regidx t <> Regidx s2_idx ->
                    m4 !!! Regidx t = m3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m3 (Regidx s2_idx) (Regidx t) _ Ht)).
    (* ---- 0x328  c.mv s5,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h5 m4 (mword_of_int 0x328) s5_idx a2_idx
              (mword_of_int qp) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val qp))
              with "[] Hrun").
    { iApply (uis_shp_328 with "Hcode"). }
    rewrite (ushp_pc_step 0x328 2). iIntros (h6) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int qp : mword 64)]> m4).
    assert (Hm5 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    m5 !!! Regidx t = m4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m4 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x32a  c.mv s6,a3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 m5 (mword_of_int 0x32a) s6_idx a3_idx
              (mword_of_int eqp) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm5 a3_idx ltac:(vm_compute; discriminate))
                      (Hm4 a3_idx ltac:(vm_compute; discriminate))
                      (Hm3 a3_idx ltac:(vm_compute; discriminate))
                      (Hm2 a3_idx ltac:(vm_compute; discriminate))
                      (Hm1 a3_idx ltac:(vm_compute; discriminate)) Ha3;
                    symmetry; exact (ushp_mv_val eqp))
              with "[] Hrun").
    { iApply (uis_shp_32a with "Hcode"). }
    rewrite (ushp_pc_step 0x32a 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int eqp : mword 64)]> m5).
    assert (Hm6 : forall t : mword 5, Regidx t <> Regidx s6_idx ->
                    m6 !!! Regidx t = m5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m5 (Regidx s6_idx) (Regidx t) _ Ht)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x32c  c.ld s1,0(a0) -- the cursor ---- *)
    iApply (wp_uk_cld γt γd γs γfd h7 m6 (mword_of_int 0x32c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx ps w0 (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_6 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              Hps8 ltac:(vm_compute; discriminate)
              with "[] Hcur Hrun").
    { iApply (uis_shp_32c with "Hcode"). }
    iIntros "Hcur". rewrite (ushp_pc_step 0x32c 2). iIntros (h8) "Hrun".
    set (m7 := <[Regidx s1_idx := regval_into_reg w0]> m6).
    assert (Hm7 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    m7 !!! Regidx t = m6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m6 (Regidx s1_idx) (Regidx t) _ Ht)).
    (* ---- 0x32e  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h8 m7 (mword_of_int 0x32e)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x232e)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_32e with "Hcode"). }
    rewrite (ushp_pc_step 0x32e 4). iIntros (h9) "Hrun".
    set (m8 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x232e : mword 64)]> m7).
    assert (Hm8 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m8 !!! Regidx t = m7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m7 (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x332  addi s3,s3,-806  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi γt γd γs γfd h9 m8 (mword_of_int 0x332)
              (mword_of_int 3290 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m7 (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x232e
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_332 with "Hcode"). }
    rewrite (ushp_pc_step 0x332 4). iIntros (h10) "Hrun".
    set (m9 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m8).
    assert (Hm9 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m9 !!! Regidx t = m8 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m8 (Regidx s3_idx) (Regidx t) _ Ht)).
    (* the register file the leading scan starts from *)
    assert (Hs1_9 : m9 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat off)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m6 (Regidx s1_idx) (regval_into_reg w0)). exact Hw0. }
    assert (Hs2_9 : m9 !!! Regidx s2_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s2_idx)
               (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                 : mword 64))). }
    assert (Hs3_9 : m9 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq m8 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    assert (Ha1_9 : m9 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Hs4_9 : m9 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hm9 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs5_9 : m9 !!! Regidx s5_idx = mword_of_int qp).
    { rewrite (Hm9 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s5_idx)
               (regval_into_reg (mword_of_int qp : mword 64))). }
    assert (Hs6_9 : m9 !!! Regidx s6_idx = mword_of_int eqp).
    { rewrite (Hm9 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s6_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s6_idx)
               (regval_into_reg (mword_of_int eqp : mword 64))). }
    assert (Hsp9 : m9 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    assert (Hkeep9 : forall t : mword 5,
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              m9 !!! Regidx t = m !!! Regidx t).
    { intros t H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (Hm9 t H19) (Hm8 t H19) (Hm7 t H9) (Hm6 t H22) (Hm5 t H21)
              (Hm4 t H18) (Hm3 t H20) (Hm2 t H8). exact (Hm1 t H2). }
    (* ---- 0x336..0x34c  the LEADING whitespace scan ---- *)
    iApply (wp_kshp_ws_enter 0x336 a1_idx (mword_of_int 1858 : mword 21)
              dq dw s0 len off f nn h10 m9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hoffle Hs0 Hs64 Hs1_9 Hs2_9 Hs3_9 Ha1_9
              with "[] [] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { iApply (uis_shp_336 with "Hcode"). }
    { iApply (uis_shp_33a with "Hcode"). }
    { iApply (uis_shp_33e with "Hcode"). }
    { iApply (uis_shp_340 with "Hcode"). }
    { iApply (uis_shp_344 with "Hcode"). }
    { iApply (uis_shp_346 with "Hcode"). }
    { iApply (uis_shp_348 with "Hcode"). }
    { iApply (uis_shp_34c with "Hcode"). }
    iIntros "Hstr Hws" (h11 mA) "%HpresA %Hs1A Hrun".
    assert (Hkkd : (off + ushp_skipws (len - off) off f)%nat = kk)
      by reflexivity.
    rewrite Hkkd in Hs1A.
    assert (Hs2_A : mA !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresA s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs2_9).
    assert (Hs4_A : mA !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresA s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4_9).
    assert (Hs5_A : mA !!! Regidx s5_idx = mword_of_int qp)
      by (rewrite (HpresA s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs5_9).
    assert (Hs6_A : mA !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresA s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs6_9).
    assert (Hsp_A : mA !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresA csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hsp9).
    (* ---- 0x34e..0x352  [if(q) *q = s] ---- *)
    iApply (wp_kshp_gtk_qst s0 qp kk wq nn h11 mA Hs0
              ltac:(unfold Z64 in *; lia) Hs1A Hs5_A with "Hcode Hq Hrun").
    iIntros "Hq" (h12) "Hrun".
    (* ---- 0x356..0x386 (and 0x3ca..0x3e8)  THE SWITCH ---- *)
    iApply (wp_kshp_gtk_disp dq s0 len kk f nn h12 mA
              Hkk Hnosym Hs0 Hs64 Hs1A with "Hcode Hstr Hrun").
    iIntros "Hstr" (h13 mB) "%HpresB %Hs5B Hrun".
    assert (Hs1_B : mB !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat kk))
      by (rewrite (HpresB s1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs1A).
    assert (Hs2_B : mB !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresB s2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs2_A).
    assert (Hs4_B : mB !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresB s4_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs4_A).
    assert (Hs6_B : mB !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresB s6_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs6_A).
    assert (Hsp_B : mB !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresB csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp_A).
    assert (HkeepB : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              mB !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (HpresB t (ushp_cs_ne t a4_idx Ht
                           ltac:(vm_compute; reflexivity))
                 (ushp_cs_ne t a5_idx Ht ltac:(vm_compute; reflexivity))
                 H21).
      rewrite (HpresA t Ht H9).
      exact (Hkeep9 t H2 H8 H9 H18 H19 H20 H21 H22). }
    destruct (lt_dec kk len) as [ Hklt | Hkge ].
    2: { (* THE NUL ARM: the cursor is at [es] and gettoken returns 0 ---- *)
      rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge).
      assert (Hkeq : kk = len) by lia.
      assert (Hfin : ushp_gettok_fin len f kk = len).
      { unfold ushp_gettok_fin, ushp_gettok_end. rewrite Hkeq.
        assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_toklen_zero len f).
        assert (Hz2 : (len + 0)%nat = len) by lia. rewrite Hz2 Hz.
        rewrite (ushp_skipws_zero len f). lia. }
      assert (Hend : ushp_gettok_end len f kk = len).
      { unfold ushp_gettok_end. rewrite Hkeq.
        assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_toklen_zero len f). lia. }
      assert (Hres : ushp_gettok_res len f kk = 0).
      { unfold ushp_gettok_res.
        rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge). reflexivity. }
      rewrite Hkeq in Hs1_B.
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len len f weq nn h13 mB
                ltac:(lia) Hs0 Hs64 Hs1_B Hs2_B Hs6_B
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h14 mC) "%HpresC %Hs1C Hrun".
      assert (Hz : (len - len)%nat = 0%nat) by lia.
      rewrite Hz (ushp_skipws_zero len f) in Hs1C.
      assert (Hlen0 : (len + 0)%nat = len) by lia.
      rewrite Hlen0 in Hs1C.
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps 0 (s0 + Z.of_nat len) w0 nn
                h14 mC Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresC csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_B)
                ltac:(rewrite (HpresC s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_B)
                Hs1C
                ltac:(rewrite (HpresC s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact (Hs5B ltac:(lia)))
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresC t Ht H9 H19);
                      exact (HkeepB t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite <- Hkkd. rewrite Hkkd.
      rewrite Hfin Hend Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* THE DEFAULT ARM: an ordinary token ---- *)
    rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt).
    assert (Hres : ushp_gettok_res len f kk = 97).
    { unfold ushp_gettok_res.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt). reflexivity. }
    (* ---- 0x3ec  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h13 mB (mword_of_int 0x3ec)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x23ec)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3ec with "Hcode"). }
    rewrite (ushp_pc_step 0x3ec 4). iIntros (h14) "Hrun".
    set (d1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x23ec : mword 64)]> mB).
    assert (Hd1 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d1 !!! Regidx t = mB !!! Regidx t)
      by (intros t Ht; exact (upd_ne mB (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x3f0  addi s3,s3,-996 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h14 d1 (mword_of_int 0x3f0)
              (mword_of_int 3100 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mB (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x23ec
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f0 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f0 4). iIntros (h15) "Hrun".
    set (d2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> d1).
    assert (Hd2 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d2 !!! Regidx t = d1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d1 (Regidx s3_idx) (Regidx t) _ Ht)).
    assert (Hs3_d2 : d2 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq d1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    (* ---- 0x3f4  auipc s5,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h15 d2 (mword_of_int 0x3f4)
              (mword_of_int 2 : mword 20) s5_idx (mword_of_int 0x23f4)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f4 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f4 4). iIntros (h16) "Hrun".
    set (d3 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 0x23f4 : mword 64)]> d2).
    assert (Hd3 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    d3 !!! Regidx t = d2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d2 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x3f8  addi s5,s5,-1012  -- s5 = &symbols ---- *)
    iApply (wp_uk_addi γt γd γs γfd h16 d3 (mword_of_int 0x3f8)
              (mword_of_int 3084 : mword 12) s5_idx s5_idx
              (mword_of_int ushp_symbols) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq d2 (Regidx s5_idx)
                               (regval_into_reg (mword_of_int 0x23f4
                                                 : mword 64)));
                    unfold ushp_symbols;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f8 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f8 4). iIntros (h17) "Hrun".
    set (d4 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int ushp_symbols
                                     : mword 64)]> d3).
    assert (Hd4 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    d4 !!! Regidx t = d3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d3 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Hs5_d4 : d4 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by exact (upd_eq d3 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int ushp_symbols : mword 64))).
    assert (Hs1_d4 : d4 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat kk))
      by (rewrite (Hd4 s1_idx ltac:(vm_compute; discriminate))
                  (Hd3 s1_idx ltac:(vm_compute; discriminate))
                  (Hd2 s1_idx ltac:(vm_compute; discriminate))
                  (Hd1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_B).
    assert (Hs2_d4 : d4 !!! Regidx s2_idx
                     = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hd4 s2_idx ltac:(vm_compute; discriminate))
                  (Hd3 s2_idx ltac:(vm_compute; discriminate))
                  (Hd2 s2_idx ltac:(vm_compute; discriminate))
                  (Hd1 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_B).
    assert (Hs3_d4 : d4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hd4 s3_idx ltac:(vm_compute; discriminate))
                  (Hd3 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_d2).
    assert (Hs4_d4 : d4 !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (Hd4 s4_idx ltac:(vm_compute; discriminate))
                  (Hd3 s4_idx ltac:(vm_compute; discriminate))
                  (Hd2 s4_idx ltac:(vm_compute; discriminate))
                  (Hd1 s4_idx ltac:(vm_compute; discriminate)); exact Hs4_B).
    assert (Hs6_d4 : d4 !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (Hd4 s6_idx ltac:(vm_compute; discriminate))
                  (Hd3 s6_idx ltac:(vm_compute; discriminate))
                  (Hd2 s6_idx ltac:(vm_compute; discriminate))
                  (Hd1 s6_idx ltac:(vm_compute; discriminate)); exact Hs6_B).
    assert (Hsp_d4 : d4 !!! Regidx csp_rs1 = spn)
      by (rewrite (Hd4 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd3 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd2 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd1 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp_B).
    assert (Hkeep_d4 : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              d4 !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (Hd4 t H21) (Hd3 t H21) (Hd2 t H19) (Hd1 t H19).
      exact (HkeepB t Ht H2 H8 H9 H18 H19 H20 H21 H22). }
    (* ---- 0x3fc  bgeu s1,s2,0x43e -- refuted: the cursor is inside ---- *)
    assert (Htk : false = uv_btaken BGEU (d4 !!! Regidx s1_idx)
                            (d4 !!! Regidx s2_idx)).
    { cbn [uv_btaken]. rewrite Hs1_d4 Hs2_d4.
      rewrite (moi_ge_u (s0 + Z.of_nat kk) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h17 d4 (mword_of_int 0x3fc)
              (mword_of_int 66 : mword 13) s2_idx s1_idx BGEU false
              (mword_of_int 0x43e) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3fc with "Hcode"). }
    rewrite (ushp_pc_step 0x3fc 4). iIntros (h18) "Hrun".
    (* ---- 0x400..0x41a  THE TOKEN-BODY SCAN ---- *)
    iApply (wp_kshp_tok_scan dq dw dv s0 len f nn (len - kk)%nat kk h18 d4
              eq_refl Hklt Hs0 Hs64 Hs1_d4 Hs2_d4 Hs3_d4 Hs5_d4
              with "Hcode Hstr Hws Hsy Hrun").
    iIntros "Hstr Hws Hsy" (h19 mE) "%HpresE %Hs1E %Hs5E Hrun".
    set (ee := ushp_gettok_end len f kk).
    assert (Heed : (kk + ushp_toklen (len - kk) kk f)%nat = ee)
      by reflexivity.
    rewrite Heed in Hs1E.
    assert (Heele : (ee <= len)%nat).
    { unfold ee, ushp_gettok_end.
      pose proof (ushp_toklen_le (len - kk) kk f). lia. }
    assert (Hexit : ushp_tok_exit len f kk
                    = if bool_decide (ee < len)%nat then 0x388 else 0x424)
      by (unfold ushp_tok_exit; rewrite Heed; reflexivity).
    rewrite Hexit.
    assert (Hs2_E : mE !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresE s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs2_d4).
    assert (Hs4_E : mE !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresE s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs4_d4).
    assert (Hs6_E : mE !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresE s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs6_d4).
    assert (Hsp_E : mE !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresE csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp_d4).
    assert (Hkeep_E : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              mE !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (HpresE t Ht H9 H21).
      exact (Hkeep_d4 t Ht H2 H8 H9 H18 H19 H20 H21 H22). }
    destruct (bool_decide (ee < len)%nat) eqn:Eee.
    { (* the token was ended by a byte: 0x388, then the trailing scan *)
      apply bool_decide_eq_true in Eee.
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len ee f weq nn h19 mE
                ltac:(lia) Hs0 Hs64 Hs1E Hs2_E Hs6_E
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h20 mF) "%HpresF %Hs1F Hrun".
      assert (Hfin : ushp_gettok_fin len f kk
                     = (ee + ushp_skipws (len - ee) ee f)%nat)
        by reflexivity.
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps 97
                (s0 + Z.of_nat (ee + ushp_skipws (len - ee) ee f)) w0 nn
                h20 mF Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresF csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_E)
                ltac:(rewrite (HpresF s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_E)
                Hs1F
                ltac:(rewrite (HpresF s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5E)
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresF t Ht H9 H19);
                      exact (Hkeep_E t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite Hfin Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* the token ran to [es]: 0x424, and the trailing scan is empty *)
    apply bool_decide_eq_false in Eee.
    assert (Heeq : ee = len) by lia.
    rewrite Heeq in Hs1E.
    assert (Hfin : ushp_gettok_fin len f kk = len).
    { assert (H1 : ushp_gettok_fin len f kk
                   = (ee + ushp_skipws (len - ee) ee f)%nat) by reflexivity.
      rewrite H1 Heeq.
      assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
      rewrite (ushp_skipws_zero len f). lia. }
    iApply (wp_kshp_gtk_424 dq dw s0 eqp len f weq nn h19 mE
              Hs0 Hs64 Hs1E Hs2_E Hs6_E with "Hcode Heq Hstr Hws Hrun").
    iIntros "Heq Hstr Hws" (h20 mF) "%HpresF %Hs1F Hrun".
    iApply (wp_kshp_gtk_fin m sp0 spl vals ps 97 (s0 + Z.of_nat len) w0 nn
              h20 mF Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
              eq_refl eq_refl
              ltac:(rewrite (HpresF csp_rs1 ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hsp_E)
              ltac:(rewrite (HpresF s4_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs4_E)
              Hs1F
              ltac:(rewrite (HpresF s5_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs5E)
              ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                    rewrite (HpresF t Ht H9 H19);
                    exact (Hkeep_E t Ht H2 H8 H9 H18 H19 H20 H21 H22))
              with "Hcode Hcur Hsl Hloc Hrun").
    iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
    rewrite Hfin Hres Heeq.
    iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Hafin.
  Qed.


  (* ===================================================================== *)
  (* §10 parseredirs @0x4ac -- 85 instructions, 40 of them REACHED.         *)
  (*                                                                       *)
  (*   struct cmd *parseredirs(struct cmd *cmd, char **ps, char *es) {      *)
  (*     while(peek(ps, es, "<>")) { ... }                                  *)
  (*     return cmd;  }                                                     *)
  (*                                                                       *)
  (* THE LOOP NEVER TURNS.  Its guard is a peek for the two redirection     *)
  (* bytes, both of them in sh's symbol table, so [ushp_no_symbols] refutes *)
  (* it at the [c.beqz] -- [ushp_peek_res_sym] is that refutation and it is *)
  (* the same one line at all five sites.  What is left is a fourteen-word  *)
  (* frame, eleven spills, eight register moves, ONE call and the return:   *)
  (* 40 instructions of the 85 catalogued, and the other 45 -- the two      *)
  (* [redircmd] arms, the [panic], the switch on the redirection byte --    *)
  (* are never fetched.                                                     *)
  (*                                                                       *)
  (* IT IS ALSO THE FIRST WALK THAT CONSUMES [wp_kshp_peek], and the        *)
  (* postcondition is exactly what it wanted: the cursor cell has moved to  *)
  (* the first non-blank byte and the answer is a [Z] this lemma computes   *)
  (* rather than a case it has to split on.                                 *)
  (* ===================================================================== *)

  Lemma wp_kshp_parseredirs (h : CpuId) (m : regfile) (dq dw : dfrac)
      (cmd ps s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parseredirs)
      (14 + (8 + (2 + nn))) -∗
    (uword γd ps
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int cmd ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
           (14 + (8 + (2 + nn))) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hrun Hcont".
    rewrite shpp_parseredirs.
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | 6%nat => m !!! Regidx s5_idx
                   | 7%nat => m !!! Regidx s6_idx
                   | 8%nat => m !!! Regidx s7_idx
                   | 9%nat => m !!! Regidx s8_idx
                   | _ => m !!! Regidx s9_idx end).
    (* ---- 0x4ac..0x4c4  the prologue: k = 14, eleven spills ---- *)
    iApply (wp_kshp_frame_pro 14 3 [(ra_idx, mword_of_int 13 : mword 6);
               (s0_idx, mword_of_int 12 : mword 6);
               (s1_idx, mword_of_int 11 : mword 6);
               (s2_idx, mword_of_int 10 : mword 6);
               (s3_idx, mword_of_int 9 : mword 6);
               (s4_idx, mword_of_int 8 : mword 6);
               (s5_idx, mword_of_int 7 : mword 6);
               (s6_idx, mword_of_int 6 : mword 6);
               (s7_idx, mword_of_int 5 : mword 6);
               (s8_idx, mword_of_int 4 : mword 6);
               (s9_idx, mword_of_int 3 : mword 6)] 0x4ac
              (fun i : nat => match i with
                              | 0%nat => 0x4ae | 1%nat => 0x4b0
                              | 2%nat => 0x4b2 | 3%nat => 0x4b4
                              | 4%nat => 0x4b6 | 5%nat => 0x4b8
                              | 6%nat => 0x4ba | 7%nat => 0x4bc
                              | 8%nat => 0x4be | 9%nat => 0x4c0
                              | 10%nat => 0x4c2 | 11%nat => 0x4c4
                              | _ => 0x4c6 end)
              (mword_of_int 57 : mword 6) (mword_of_int 28 : mword 8)
              vals (8 + (2 + nn)) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_4ac with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_4ae with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4c2 with "Hcode") | done ]. }
    { iApply (uis_shp_4c4 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 14))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x4c6  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m2 (mword_of_int 0x4c6) s4_idx a0_idx
              (mword_of_int cmd) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val cmd))
              with "[] Hrun").
    { iApply (uis_shp_4c6 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x4c8  c.mv s3,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h2 m3 (mword_of_int 0x4c8) s3_idx a1_idx
              (mword_of_int ps) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_4c8 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m4 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x4ca  c.mv s2,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m4 (mword_of_int 0x4ca) s2_idx a2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_4ca with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m5 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x4cc  auipc s6,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h4 m5 (mword_of_int 0x4cc)
              (mword_of_int 1 : mword 20) s6_idx
              (mword_of_int 0x14cc) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4cc with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 0x14cc : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_6 : m6 !!! Regidx s6_idx = mword_of_int 0x14cc)
      by exact (upd_eq m5 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int 0x14cc : mword 64))).
    (* ---- 0x4d0  addi s6,s6,-476 -- the table base 0x12f0 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h5 m6 (mword_of_int 0x4d0)
              (mword_of_int 3620 : mword 12) s6_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_6; unfold ushp_T_redir;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4d0 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m7 := <[Regidx s6_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_redir : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_7 : m7 !!! Regidx s6_idx = mword_of_int ushp_T_redir)
      by exact (upd_eq m6 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int ushp_T_redir : mword 64))).
    (* ---- 0x4d4  addi s9,s0,-112 -- &q, dead on this path ---- *)
    iApply (wp_uk_addi γt γd γs γfd h6 m7 (mword_of_int 0x4d4)
              (mword_of_int 3984 : mword 12) s0_idx s9_idx
              (add_vec (m7 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 3984 : mword 12)))
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shp_4d4 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m8 := <[Regidx s9_idx
                 := regval_into_reg
                      (add_vec (m7 !!! Regidx s0_idx)
                         (sign_extend' 64
                            (mword_of_int 3984 : mword 12)))]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s9_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s9_idx) (Regidx q) _ Hq)).
    (* ---- 0x4d8  addi s8,s0,-104 -- &eq, dead ---- *)
    iApply (wp_uk_addi γt γd γs γfd h7 m8 (mword_of_int 0x4d8)
              (mword_of_int 3992 : mword 12) s0_idx s8_idx
              (add_vec (m8 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 3992 : mword 12)))
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shp_4d8 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m9 := <[Regidx s8_idx
                 := regval_into_reg
                      (add_vec (m8 !!! Regidx s0_idx)
                         (sign_extend' 64
                            (mword_of_int 3992 : mword 12)))]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s8_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s8_idx) (Regidx q) _ Hq)).
    (* ---- 0x4dc  li s7,97 -- the 'a' the dead arm compares against ---- *)
    iApply (wp_uk_li γt γd γs γfd h8 m9 (mword_of_int 0x4dc)
              (mword_of_int 97 : mword 12) s7_idx (mword_of_int 97)
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 97))
              with "[] Hrun").
    { iApply (uis_shp_4dc with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m10 := <[Regidx s7_idx
                  := regval_into_reg (mword_of_int 97 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx s7_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx s7_idx) (Regidx q) _ Hq)).
    (* ---- 0x4e0  c.j 0x502 -- into the loop's GUARD ---- *)
    iApply (wp_uk_cj γt γd γs γfd h9 m10 (mword_of_int 0x4e0)
              (mword_of_int 17 : mword 11) (mword_of_int 0x502)
              (8 + (2 + nn))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4e0 with "Hcode"). }
    iIntros (h10) "Hrun".
    (* ---- 0x502  li s5,60 -- the '<' the dead switch compares against ---- *)
    iApply (wp_uk_li γt γd γs γfd h10 m10 (mword_of_int 0x502)
              (mword_of_int 60 : mword 12) s5_idx (mword_of_int 60)
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 60))
              with "[] Hrun").
    { iApply (uis_shp_502 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 60 : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x506  c.mv a2,s6 ---- *)
    assert (Hs6_11 : m11 !!! Regidx s6_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm11 s6_idx ltac:(vm_compute; discriminate))
              (Hm10 s6_idx ltac:(vm_compute; discriminate))
              (Hm9 s6_idx ltac:(vm_compute; discriminate))
              (Hm8 s6_idx ltac:(vm_compute; discriminate)). exact Hs6_7. }
    iApply (wp_uk_cmv γt γd γs γfd h11 m11 (mword_of_int 0x506) a2_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_11; symmetry;
                    exact (ushp_mv_val ushp_T_redir))
              with "[] Hrun").
    { iApply (uis_shp_506 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m12 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_redir : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x508  c.mv a1,s2 ---- *)
    assert (Hs2_12 : m12 !!! Regidx s2_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h12 m12 (mword_of_int 0x508) a1_idx s2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_12; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_508 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m13 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m12).
    assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m13 !!! Regidx q = m12 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m12 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x50a  c.mv a0,s3 ---- *)
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int ps).
    { rewrite (Hm13 s3_idx ltac:(vm_compute; discriminate))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hm5 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s3_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h13 m13 (mword_of_int 0x50a) a0_idx s3_idx
              (mword_of_int ps) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_13; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_50a with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m14 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x50c  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h14 m14 (mword_of_int 0x50c)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x510) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_50c with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m15 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x510 : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret : ret_pc (m15 !!! Regidx ra_idx) = mword_of_int 0x510).
    { rewrite (upd_eq m14 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x510 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_15 : m15 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm15 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m13 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_15 : m15 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm15 a1_idx ltac:(vm_compute; discriminate))
              (Hm14 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m12 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_15 : m15 !!! Regidx a2_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm15 a2_idx ltac:(vm_compute; discriminate))
              (Hm14 a2_idx ltac:(vm_compute; discriminate))
              (Hm13 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int ushp_T_redir : mword 64))). }
    rewrite <- shpp_peek.
    (* ---- peek(ps, es, the two redirection bytes) ---- *)
    iApply (wp_kshp_peek h15 m15 dq dw true DfracDiscarded ps s0
              ushp_T_redir len off 2 f (ushp_lit ushp_T_redir)
              (mword_of_int (s0 + Z.of_nat off)) nn
              Ha0_15 Ha1_15 Ha2_15 Hoffle eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_redir; lia)
              ltac:(unfold ushp_T_redir, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode [Hcur] Hstr Hws [] Hrun").
    { rewrite <- Hw0. iExact "Hcur". }
    { iApply (ushp_lit_str ushp_T_redir 2 DfracDiscarded
                ushp_T_redir_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h16 n0) "%Hcs %Ha0n0 Hrun".
    rewrite Eret.
    rewrite (ushp_peek_res_sym len f
               (off + ushp_skipws (len - off) off f) 2 ushp_T_redir
               Hnosym ushp_T_redir_sym) in Ha0n0.
    (* ---- 0x510  c.beqz a0 -- TAKEN: the loop never turns ---- *)
    iApply (wp_uk_cbeqz γt γd γs γfd h16 n0 (mword_of_int 0x510)
              (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x574) (8 + (2 + nn))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0n0; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_510 with "Hcode"). }
    iIntros (h17) "Hrun".
    (* ---- 0x574  c.mv a0,s4 -- the answer is the cmd we were handed ---- *)
    assert (Hs4_n0 : n0 !!! Regidx s4_idx = mword_of_int cmd).
    { rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity))
              (Hm15 s4_idx ltac:(vm_compute; discriminate))
              (Hm14 s4_idx ltac:(vm_compute; discriminate))
              (Hm13 s4_idx ltac:(vm_compute; discriminate))
              (Hm12 s4_idx ltac:(vm_compute; discriminate))
              (Hm11 s4_idx ltac:(vm_compute; discriminate))
              (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hm6 s4_idx ltac:(vm_compute; discriminate))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int cmd : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h17 n0 (mword_of_int 0x574) a0_idx s4_idx
              (mword_of_int cmd) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_n0; symmetry; exact (ushp_mv_val cmd))
              with "[] Hrun").
    { iApply (uis_shp_574 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> n0).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = n0 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n0 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 14))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    (* ---- 0x576..0x58e  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 14 3 [(ra_idx, mword_of_int 13 : mword 6);
               (s0_idx, mword_of_int 12 : mword 6);
               (s1_idx, mword_of_int 11 : mword 6);
               (s2_idx, mword_of_int 10 : mword 6);
               (s3_idx, mword_of_int 9 : mword 6);
               (s4_idx, mword_of_int 8 : mword 6);
               (s5_idx, mword_of_int 7 : mword 6);
               (s6_idx, mword_of_int 6 : mword 6);
               (s7_idx, mword_of_int 5 : mword 6);
               (s8_idx, mword_of_int 4 : mword 6);
               (s9_idx, mword_of_int 3 : mword 6)] (mword_of_int 13 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x576 | 1%nat => 0x578
                              | 2%nat => 0x57a | 3%nat => 0x57c
                              | 4%nat => 0x57e | 5%nat => 0x580
                              | 6%nat => 0x582 | 7%nat => 0x584
                              | 8%nat => 0x586 | 9%nat => 0x588
                              | 10%nat => 0x58a | 11%nat => 0x58c
                              | _ => 0x58e end)
              (mword_of_int 7 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 11)) vals
              (8 + (2 + nn)) h18 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    vm_compute; discriminate)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_576 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_578 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_580 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_582 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_584 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_586 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_588 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_58a with "Hcode") | done ]. }
    { iApply (uis_shp_58c with "Hcode"). }
    { iApply (uis_shp_58e with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" with "Hcur Hstr Hws [] [] Hrun").
    - iPureIntro.
      apply (ushp_frame_cs _ vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        rewrite (Hme q (ushp_cs_ne q a0_idx Hq
                          ltac:(vm_compute; reflexivity)))
                (Hcs q Hq)
                (Hm15 q (Hmiss 0%nat ra_idx (mword_of_int 13 : mword 6)
                           eq_refl))
                (Hm14 q (ushp_cs_ne q a0_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm13 q (ushp_cs_ne q a1_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm12 q (ushp_cs_ne q a2_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm11 q (Hmiss 6%nat s5_idx (mword_of_int 7 : mword 6)
                           eq_refl))
                (Hm10 q (Hmiss 8%nat s7_idx (mword_of_int 5 : mword 6)
                           eq_refl))
                (Hm9 q (Hmiss 9%nat s8_idx (mword_of_int 4 : mword 6)
                          eq_refl))
                (Hm8 q (Hmiss 10%nat s9_idx (mword_of_int 3 : mword 6)
                          eq_refl))
                (Hm7 q (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm6 q (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm5 q (Hmiss 3%nat s2_idx (mword_of_int 10 : mword 6)
                          eq_refl))
                (Hm4 q (Hmiss 4%nat s3_idx (mword_of_int 9 : mword 6)
                          eq_refl))
                (Hm3 q (Hmiss 5%nat s4_idx (mword_of_int 8 : mword 6)
                          eq_refl))
                (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 12 : mword 6)
                          eq_refl))
                (Hm1 q Hqsp).
        reflexivity.
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq n0 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int cmd : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* §11 parseexec @0x590 -- the ARGUMENT LOOP.                             *)
  (*                                                                       *)
  (*   struct cmd *parseexec(char **ps, char *es) {                         *)
  (*     if(peek(ps, es, "(")) return parseblock(ps, es);                   *)
  (*     ret = execcmd();  cmd = (struct execcmd * )ret;  argc = 0;         *)
  (*     ret = parseredirs(ret, ps, es);                                    *)
  (*     while(!peek(ps, es, "|)&;")) {                                     *)
  (*       if((tok = gettoken(ps, es, &q, &eq)) == 0) break;                *)
  (*       if(tok != 'a') panic("syntax");                                  *)
  (*       cmd->argv[argc] = q;  cmd->eargv[argc] = eq;  argc++;            *)
  (*       if(argc >= MAXARGS) panic("too many args");                      *)
  (*       ret = parseredirs(ret, ps, es);  }                               *)
  (*     cmd->argv[argc] = 0;  cmd->eargv[argc] = 0;  return ret;  }        *)
  (*                                                                       *)
  (* THE INVARIANT IS ONE PREDICATE AND ONE EQUATION: the node holds the    *)
  (* tokens consumed so far ([ushp_exec_pre s0 p done]) and the cursor is   *)
  (* where the tokens still to come start ([ushp_tokens len f cur rest]).   *)
  (* [s2] is [argc] and [s3] is [&argv[argc]], and both are DERIVED from    *)
  (* [length done] rather than tracked, which is why the step does no index *)
  (* arithmetic beyond one [c.addiw] and one [c.addi].                      *)
  (*                                                                       *)
  (* THREE ARMS ARE REFUTED, NOT WEAKENED.  [peek(ps,es,"|)&;")] is 0 by    *)
  (* [ushp_peek_res_sym]; [tok != 'a'] cannot happen because gettoken's     *)
  (* answer on a symbol-free line is 'a' or 0 and the 0 arm is the loop's   *)
  (* exit; and [argc >= MAXARGS] cannot happen because the caller's         *)
  (* [length toks < 10] bounds it.  So neither [panic] is fetched and       *)
  (* [parseblock] is not either.                                            *)
  (* ===================================================================== *)

  Local Lemma wp_kshp_pex_loop (dq dw dv : dfrac) (s0 ps p fp : Z)
      (len : nat) (f : nat -> bv 8) (nn : nat) :
    forall (rest done : list (nat * nat)) (cur : nat) (h : CpuId)
           (mc : regfile) (wq weq : mword 64),
    ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    0 < fp - 128 -> (fp - 128) mod 8 = 0 -> 0 <= fp -> fp < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (cur <= len)%nat ->
    (length done + length rest < 10)%nat ->
    ushp_tokens len f cur rest ->
    mc !!! Regidx s0_idx = mword_of_int fp ->
    mc !!! Regidx s1_idx = mword_of_int p ->
    mc !!! Regidx s2_idx = mword_of_int (Z.of_nat (length done)) ->
    mc !!! Regidx s3_idx
      = mword_of_int (p + 8 + 8 * Z.of_nat (length done)) ->
    mc !!! Regidx s4_idx = mword_of_int ps ->
    mc !!! Regidx s5_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int ushp_T_arg ->
    mc !!! Regidx s7_idx = mword_of_int (fp - 120) ->
    mc !!! Regidx s8_idx = mword_of_int (fp - 128) ->
    mc !!! Regidx s9_idx = mword_of_int 10 ->
    mc !!! Regidx s10_idx = mword_of_int 97 ->
    mc !!! Regidx s11_idx = mword_of_int p ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_exec_pre s0 p done -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    uword γd (fp - 120) wq -∗
    uword γd (fp - 128) weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x622) (24 + nn) -∗
    (ushp_exec_pre s0 p (done ++ rest) -∗
     uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
     (∃ w : mword 64, uword γd (fp - 120) w) -∗
     (∃ w : mword 64, uword γd (fp - 128) w) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
             Regidx r <> Regidx s3_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         ⌜ mc' !!! Regidx s2_idx
             = mword_of_int (Z.of_nat (length done + length rest)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int p ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x662) (24 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro rest.
    induction rest as [| tk rest IH ];
      intros done cur h mc wq weq Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz
        Hfp0 Hfp8 Hfpl Hfph Hp0 Hp8 Hpsz Hcur Hcnt Htoks
        Hs0v Hs1v Hs2v Hs3v Hs4v Hs5v Hs6v Hs7v Hs8v Hs9v Hs10v Hs11v;
      iIntros "#Hcode #Hro Hnode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    (* ---- the frame's two out-cells are hygienic wherever the frame is -- *)
    all: assert (Hq0 : 0 < fp - 120) by lia.
    all: assert (Hq8 : (fp - 120) mod 8 = 0);
      [ replace (fp - 120) with (fp - 128 + 8) by lia;
        rewrite Zplus_mod Hfp8; reflexivity | ].
    all: assert (Hqz : fp - 120 + 8 < Z64) by lia.
    all: assert (Hez : fp - 128 + 8 < Z64) by lia.
    all: assert (Hfp64 : 0 <= fp < Z64) by lia.
    all: assert (Hnodelen : (length done < 10)%nat)
      by (cbn [length] in Hcnt; lia).
    (* ---- and the position peek is about to leave the cursor at -------- *)
    all: pose (cur' := (cur + ushp_skipws (len - cur) cur f)%nat).
    all: assert (Hcure : cur' = (cur + ushp_skipws (len - cur) cur f)%nat)
      by reflexivity.
    all: assert (Hcur' : (cur' <= len)%nat);
      [ rewrite Hcure; pose proof (ushp_skipws_le (len - cur) cur f); lia | ].
    all: assert (Hz' : ushp_skipws (len - cur') cur' f = 0%nat)
      by exact (ushp_skipws_idem len cur f Hcur).
    all: assert (Ekk : (cur' + ushp_skipws (len - cur') cur' f)%nat = cur')
      by (rewrite Hz'; lia).
    (* ---- 0x622  c.mv a2,s6 ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h mc (mword_of_int 0x622) a2_idx
                   s6_idx (mword_of_int ushp_T_arg) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite Hs6v; symmetry;
                         exact (ushp_mv_val ushp_T_arg))
                   with "[] Hrun");
      [ iApply (uis_shp_622 with "Hcode") | ].
    all: iIntros (h1) "Hrun".
    all: set (n1 := <[Regidx a2_idx
                      := regval_into_reg
                           (mword_of_int ushp_T_arg : mword 64)]> mc).
    all: assert (Hk1 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n1 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          exact (upd_ne mc (Regidx a2_idx) (Regidx r) _
                   (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))).
    (* ---- 0x624  c.mv a1,s5 ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h1 n1 (mword_of_int 0x624) a1_idx
                   s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk1 s5_idx ltac:(vm_compute; reflexivity))
                           Hs5v; symmetry;
                         exact (ushp_mv_val (s0 + Z.of_nat len)))
                   with "[] Hrun");
      [ iApply (uis_shp_624 with "Hcode") | ].
    all: iIntros (h2) "Hrun".
    all: set (n2 := <[Regidx a1_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat len)
                            : mword 64)]> n1).
    all: assert (Hk2 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n2 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n1 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk1 r Hr)).
    (* ---- 0x626  c.mv a0,s4 ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h2 n2 (mword_of_int 0x626) a0_idx
                   s4_idx (mword_of_int ps) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk2 s4_idx ltac:(vm_compute; reflexivity))
                           Hs4v; symmetry; exact (ushp_mv_val ps))
                   with "[] Hrun");
      [ iApply (uis_shp_626 with "Hcode") | ].
    all: iIntros (h3) "Hrun".
    all: set (n3 := <[Regidx a0_idx
                      := regval_into_reg (mword_of_int ps : mword 64)]> n2).
    all: assert (Hk3 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n3 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n2 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk2 r Hr)).
    (* ---- 0x628  jal 448 <peek> ---- *)
    all: iApply (wp_uk_jal γt γd γs γfd h3 n3 (mword_of_int 0x628)
                   (mword_of_int 2096672 : mword 21) ra_idx
                   (mword_of_int 0x448) (mword_of_int 0x62c) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   with "[] Hrun");
      [ iApply (uis_shp_628 with "Hcode") | ].
    all: iIntros (h4) "Hrun".
    all: set (n4 := <[Regidx ra_idx
                      := regval_into_reg
                           (mword_of_int 0x62c : mword 64)]> n3).
    all: assert (Hk4 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n4 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n3 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk3 r Hr)).
    all: assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x62c);
      [ rewrite (upd_eq n3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x62c : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    all: assert (Ha0_4 : n4 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    all: assert (Ha1_4 : n4 !!! Regidx a1_idx
                         = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n1 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    all: assert (Ha2_4 : n4 !!! Regidx a2_idx = mword_of_int ushp_T_arg);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n1 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq mc (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int ushp_T_arg : mword 64))) | ].
    all: rewrite <- shpp_peek.
    all: iApply (wp_kshp_peek h4 n4 dq dw true DfracDiscarded ps s0
                   ushp_T_arg len cur 4 f (ushp_lit ushp_T_arg)
                   (mword_of_int (s0 + Z.of_nat cur)) (14 + nn)
                   Ha0_4 Ha1_4 Ha2_4 Hcur eq_refl Hs0 Hs64
                   ltac:(unfold ushp_T_arg; lia)
                   ltac:(unfold ushp_T_arg, Z64; lia) Hps0 Hps8 Hpssz
                   with "Hcode Hcur Hstr Hws [] Hrun");
      [ iApply (ushp_lit_str ushp_T_arg 4 DfracDiscarded
                  ushp_T_arg_ok ltac:(cbn; lia) with "Hro") | ].
    all: iIntros "Hcur Hstr Hws _" (h5 n5) "%Hcs45 %Ha0_5 Hrun".
    all: rewrite Eret4.
    all: rewrite (ushp_peek_res_sym len f
                    (cur + ushp_skipws (len - cur) cur f)%nat 4 ushp_T_arg
                    Hnosym ushp_T_arg_sym) in Ha0_5.
    all: assert (Hk5 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n5 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs45 r Hr); exact (Hk4 r Hr)).
    (* ---- 0x62c  c.bnez a0 -- NOT taken: the guard is refuted ---- *)
    all: iApply (wp_uk_cbnez γt γd γs γfd h5 n5 (mword_of_int 0x62c)
                   (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3)
                   a0_idx false (mword_of_int 0x662) (24 + nn)
                   ltac:(vm_compute; reflexivity)
                   ltac:(rewrite Ha0_5; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(discriminate)
                   with "[] Hrun");
      [ iApply (uis_shp_62c with "Hcode") | ].
    all: iIntros (h6) "Hrun".
    (* ---- 0x62e..0x634  the four argument moves ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h6 n5 (mword_of_int 0x62e) a3_idx
                   s8_idx (mword_of_int (fp - 128)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk5 s8_idx ltac:(vm_compute; reflexivity))
                           Hs8v; symmetry; exact (ushp_mv_val (fp - 128)))
                   with "[] Hrun");
      [ iApply (uis_shp_62e with "Hcode") | ].
    all: iIntros (h7) "Hrun".
    all: set (n6 := <[Regidx a3_idx
                      := regval_into_reg
                           (mword_of_int (fp - 128) : mword 64)]> n5).
    all: assert (Hk6 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n6 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n5 (Regidx a3_idx) (Regidx r) _
                     (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk5 r Hr)).
    all: iApply (wp_uk_cmv γt γd γs γfd h7 n6 (mword_of_int 0x630) a2_idx
                   s7_idx (mword_of_int (fp - 120)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk6 s7_idx ltac:(vm_compute; reflexivity))
                           Hs7v; symmetry; exact (ushp_mv_val (fp - 120)))
                   with "[] Hrun");
      [ iApply (uis_shp_630 with "Hcode") | ].
    all: iIntros (h8) "Hrun".
    all: set (n7 := <[Regidx a2_idx
                      := regval_into_reg
                           (mword_of_int (fp - 120) : mword 64)]> n6).
    all: assert (Hk7 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n7 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n6 (Regidx a2_idx) (Regidx r) _
                     (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk6 r Hr)).
    all: iApply (wp_uk_cmv γt γd γs γfd h8 n7 (mword_of_int 0x632) a1_idx
                   s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk7 s5_idx ltac:(vm_compute; reflexivity))
                           Hs5v; symmetry;
                         exact (ushp_mv_val (s0 + Z.of_nat len)))
                   with "[] Hrun");
      [ iApply (uis_shp_632 with "Hcode") | ].
    all: iIntros (h9) "Hrun".
    all: set (n8 := <[Regidx a1_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat len)
                            : mword 64)]> n7).
    all: assert (Hk8 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n8 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n7 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk7 r Hr)).
    all: iApply (wp_uk_cmv γt γd γs γfd h9 n8 (mword_of_int 0x634) a0_idx
                   s4_idx (mword_of_int ps) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk8 s4_idx ltac:(vm_compute; reflexivity))
                           Hs4v; symmetry; exact (ushp_mv_val ps))
                   with "[] Hrun");
      [ iApply (uis_shp_634 with "Hcode") | ].
    all: iIntros (h10) "Hrun".
    all: set (n9 := <[Regidx a0_idx
                      := regval_into_reg (mword_of_int ps : mword 64)]> n8).
    all: assert (Hk9 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n9 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk8 r Hr)).
    (* ---- 0x636  jal 310 <gettoken> ---- *)
    all: iApply (wp_uk_jal γt γd γs γfd h10 n9 (mword_of_int 0x636)
                   (mword_of_int 2096346 : mword 21) ra_idx
                   (mword_of_int 0x310) (mword_of_int 0x63a) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   with "[] Hrun");
      [ iApply (uis_shp_636 with "Hcode") | ].
    all: iIntros (h11) "Hrun".
    all: set (n10 := <[Regidx ra_idx
                       := regval_into_reg
                            (mword_of_int 0x63a : mword 64)]> n9).
    all: assert (Hk10 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n10 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n9 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk9 r Hr)).
    all: assert (Eret10 : ret_pc (n10 !!! Regidx ra_idx)
                          = mword_of_int 0x63a);
      [ rewrite (upd_eq n9 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x63a : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    all: assert (Ha0_10 : n10 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n8 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    all: assert (Ha1_10 : n10 !!! Regidx a1_idx
                          = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n7 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    all: assert (Ha2_10 : n10 !!! Regidx a2_idx = mword_of_int (fp - 120));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n6 (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int (fp - 120) : mword 64))) | ].
    all: assert (Ha3_10 : n10 !!! Regidx a3_idx = mword_of_int (fp - 128));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n6 (Regidx a2_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n5 (Regidx a3_idx)
                 (regval_into_reg
                    (mword_of_int (fp - 128) : mword 64))) | ].
    all: rewrite <- shpp_gettoken.
    all: iApply (wp_kshp_gettoken h11 n10 dq dw dv ps (fp - 120) (fp - 128)
                   s0 len cur' f (mword_of_int (s0 + Z.of_nat cur'))
                   wq weq (14 + nn)
                   Ha0_10 Ha1_10 Ha2_10 Ha3_10 Hcur' eq_refl Hnosym Hs0 Hs64
                   Hps0 Hps8 Hpssz
                   with "Hcode Hcur [Hq] [Heq] Hstr Hws Hsy Hrun");
      [ iRight; iSplitR;
        [ iPureIntro; exact (conj Hq0 (conj Hq8 Hqz)) | iExact "Hq" ]
      | iRight; iSplitR;
        [ iPureIntro; exact (conj Hfp0 (conj Hfp8 Hez)) | iExact "Heq" ]
      | ].
    all: iIntros "Hcur Hq Heq Hstr Hws Hsy" (h12 n11) "%Hcs1011 %Ha0_11 Hrun".
    all: rewrite Eret10.
    all: rewrite Ekk.
    all: rewrite Ekk in Ha0_11.
    all: iDestruct "Hq" as "[%Hbadq | [_ Hq]]"; [ exfalso; lia | ].
    all: iDestruct "Heq" as "[%Hbade | [_ Heq]]"; [ exfalso; lia | ].
    all: assert (Hk11 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n11 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs1011 r Hr); exact (Hk10 r Hr)).
    - (* =========== THE LOOP EXITS: no token is left =================== *)
      assert (Hend : cur' = len)
        by exact (ushp_tokens_nil_inv len cur f Htoks).
      assert (Hres0 : ushp_gettok_res len f cur' = 0);
        [ rewrite /ushp_gettok_res
            (bool_decide_eq_false_2 (cur' < len)%nat ltac:(lia));
          reflexivity | ].
      rewrite Hres0 in Ha0_11.
      assert (Heend : ushp_gettok_end len f cur' = len);
        [ rewrite /ushp_gettok_end Hend Nat.sub_diag;
          cbn [ushp_toklen]; lia | ].
      assert (Hfin : ushp_gettok_fin len f cur' = len);
        [ rewrite /ushp_gettok_fin; cbv zeta;
          rewrite Heend Nat.sub_diag; cbn [ushp_skipws]; lia | ].
      rewrite Hfin.
      (* ---- 0x63a  c.beqz a0 -- TAKEN: the line is exhausted ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h12 n11 (mword_of_int 0x63a)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x662) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_11; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_63a with "Hcode"). }
      iIntros (h13) "Hrun".
      cbn [length]. rewrite app_nil_r Nat.add_0_r.
      iApply ("Hcont" with "Hnode Hcur [Hq] [Heq] Hstr Hws Hsy [] [] [] Hrun").
      + iExists (mword_of_int (s0 + Z.of_nat cur')). iExact "Hq".
      + iExists (mword_of_int (s0 + Z.of_nat len)). rewrite Heend. iExact "Heq".
      + iPureIntro. intros r Hr _ _ _. exact (Hk11 r Hr).
      + iPureIntro.
        rewrite (Hk11 s2_idx ltac:(vm_compute; reflexivity)). exact Hs2v.
      + iPureIntro.
        rewrite (Hk11 s1_idx ltac:(vm_compute; reflexivity)). exact Hs1v.
    - (* =========== A TOKEN: store it and go round ===================== *)
      pose (q := ushp_toklen (len - cur') cur' f).
      assert (Hqe : q = ushp_toklen (len - cur') cur' f) by reflexivity.
      destruct (ushp_tokens_cons_inv' len cur cur' q f tk rest
                  Hcure Hqe Htoks) as (Hn & Htkeq & Hrest).
      pose (e := (cur' + q)%nat).
      assert (Hee : e = (cur' + q)%nat) by reflexivity.
      assert (Hele : (e <= len)%nat);
        [ rewrite Hee Hqe;
          pose proof (ushp_toklen_le (len - cur') cur' f); lia | ].
      pose (nxt := (e + ushp_skipws (len - e) e f)%nat).
      assert (Hnxte : nxt = (e + ushp_skipws (len - e) e f)%nat)
        by reflexivity.
      assert (Hnxt : (nxt <= len)%nat);
        [ rewrite Hnxte; pose proof (ushp_skipws_le (len - e) e f); lia | ].
      assert (Hres97 : ushp_gettok_res len f cur' = 97);
        [ rewrite /ushp_gettok_res
            (bool_decide_eq_true_2 (cur' < len)%nat
               ltac:(rewrite Hqe in Hn; lia));
          reflexivity | ].
      rewrite Hres97 in Ha0_11.
      assert (Hendv : ushp_gettok_end len f cur' = e) by reflexivity.
      assert (Hfin : ushp_gettok_fin len f cur' = nxt) by reflexivity.
      rewrite Hendv Hfin.
      (* ---- 0x63a  c.beqz a0 -- NOT taken ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h12 n11 (mword_of_int 0x63a)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx false (mword_of_int 0x662) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_11; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_63a with "Hcode"). }
      iIntros (h13) "Hrun".
      (* ---- 0x63c  bne a0,s10 -- NOT taken: the token IS a word ---- *)
      iApply (wp_uk_btype γt γd γs γfd h13 n11 (mword_of_int 0x63c)
                (mword_of_int 8140 : mword 13) s10_idx a0_idx BNE false
                (mword_of_int 0x608) (24 + nn)
                ltac:(cbn [uv_btaken]; rewrite Ha0_11
                        (Hk11 s10_idx ltac:(vm_compute; reflexivity)) Hs10v;
                      vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_63c with "Hcode"). }
      iIntros (h14) "Hrun".
      (* ---- 0x640  ld a5,-120(s0) -- q ---- *)
      assert (Hs0_11 : n11 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk11 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld γt γd γs γfd h14 n11 (mword_of_int 0x640)
                (mword_of_int 3976 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 120) (mword_of_int (s0 + Z.of_nat cur')) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_11 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hq8
                ltac:(vm_compute; discriminate)
                with "[] Hq Hrun").
      { iApply (uis_shp_640 with "Hcode"). }
      iIntros "Hq" (h15) "Hrun".
      set (n12 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat cur')
                          : mword 64)]> n11).
      assert (Hk12 : forall r : mword 5, ucallee_saved_idx r = true ->
                 n12 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n11 (Regidx a5_idx) (Regidx r) _
                       (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk11 r Hr)).
      assert (Ha5_12 : n12 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat cur'))
        by exact (upd_eq n11 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat cur') : mword 64))).
      assert (Hs3_12 : n12 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk12 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3v).
      (* ---- 0x644  sd a5,0(s3) -- argv[argc] = q ---- *)
      iDestruct "Hnode" as "(%Hdl & _ & _ & Hty & Hav & Hev)".
      iDestruct (ushp_slots_upd s0 (p + 8) done tk fst Hnodelen with "Hav")
        as "[Hav0 Havc]".
      iApply (wp_uk_sd γt γd γs γfd h15 n12 (mword_of_int 0x644)
                (mword_of_int 0 : mword 12) s3_idx a5_idx
                (p + 8 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + nn)
                ltac:(rewrite Hs3_12
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (length done) Hp8))
                with "[] [Hav0] Hrun").
      { iApply (uis_shp_644 with "Hcode"). }
      { iExact "Hav0". }
      iIntros "Hav0" (h16) "Hrun".
      rewrite Ha5_12.
      iDestruct ("Havc" with "[Hav0]") as "Hav";
        [ rewrite Htkeq; iExact "Hav0" | ].
      (* ---- 0x648  ld a5,-128(s0) -- eq ---- *)
      assert (Hs0_12 : n12 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk12 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld γt γd γs γfd h16 n12 (mword_of_int 0x648)
                (mword_of_int 3968 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 128) (mword_of_int (s0 + Z.of_nat e)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_12 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hfp8
                ltac:(vm_compute; discriminate)
                with "[] Heq Hrun").
      { iApply (uis_shp_648 with "Hcode"). }
      iIntros "Heq" (h17) "Hrun".
      set (n13 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat e) : mword 64)]> n12).
      assert (Hk13 : forall r : mword 5, ucallee_saved_idx r = true ->
                 n13 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n12 (Regidx a5_idx) (Regidx r) _
                       (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk12 r Hr)).
      assert (Ha5_13 : n13 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat e))
        by exact (upd_eq n12 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat e) : mword 64))).
      assert (Hs3_13 : n13 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk13 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3v).
      (* ---- 0x64c  sd a5,80(s3) -- eargv[argc] = eq ---- *)
      iDestruct (ushp_slots_upd s0 (p + 88) done tk snd Hnodelen with "Hev")
        as "[Hev0 Hevc]".
      iApply (wp_uk_sd γt γd γs γfd h17 n13 (mword_of_int 0x64c)
                (mword_of_int 80 : mword 12) s3_idx a5_idx
                (p + 88 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + nn)
                ltac:(rewrite Hs3_13
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 11 (length done) Hp8))
                with "[] [Hev0] Hrun").
      { iApply (uis_shp_64c with "Hcode"). }
      { iExact "Hev0". }
      iIntros "Hev0" (h18) "Hrun".
      rewrite Ha5_13.
      iDestruct ("Hevc" with "[Hev0]") as "Hev";
        [ rewrite Htkeq; iExact "Hev0" | ].
      (* ---- 0x650  c.addiw s2,s2,1 -- argc++ ---- *)
      assert (Hs2_13 : n13 !!! Regidx s2_idx
                       = mword_of_int (Z.of_nat (length done)))
        by (rewrite (Hk13 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2v).
      assert (Esx : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                    = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddiw γt γd γs γfd h18 n13 (mword_of_int 0x650)
                (mword_of_int 1 : mword 6) s2_idx
                (mword_of_int (Z.of_nat (length done) + 1)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_13 Esx; symmetry;
                      exact (moi_addw (Z.of_nat (length done)) 1
                               ltac:(unfold Z31; lia)))
                with "[] Hrun").
      { iApply (uis_shp_650 with "Hcode"). }
      iIntros (h19) "Hrun".
      set (n14 := <[Regidx s2_idx
                    := regval_into_reg
                         (mword_of_int (Z.of_nat (length done) + 1)
                          : mword 64)]> n13).
      assert (Hk14 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx ->
                 n14 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2;
            rewrite (upd_ne n13 (Regidx s2_idx) (Regidx r) _ Hr2);
            exact (Hk13 r Hr)).
      assert (Hs2_14 : n14 !!! Regidx s2_idx
                       = mword_of_int (Z.of_nat (length done) + 1))
        by exact (upd_eq n13 (Regidx s2_idx)
                    (regval_into_reg
                       (mword_of_int (Z.of_nat (length done) + 1)
                        : mword 64))).
      (* ---- 0x652  bne s2,s9 -- TAKEN: MAXARGS is not reached ---- *)
      iApply (wp_uk_btype γt γd γs γfd h19 n14 (mword_of_int 0x652)
                (mword_of_int 8130 : mword 13) s9_idx s2_idx BNE true
                (mword_of_int 0x614) (24 + nn)
                ltac:(cbn [uv_btaken]; rewrite Hs2_14
                        (Hk14 s9_idx ltac:(vm_compute; reflexivity)
                           ltac:(vm_compute; discriminate)) Hs9v;
                      rewrite (moi_neq_vec (Z.of_nat (length done) + 1) 10
                                 ltac:(unfold Z64; cbn [length] in Hcnt; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hne : (Z.of_nat (length done) + 1 =? 10)
                                    = false)
                        by (apply Z.eqb_neq; cbn [length] in Hcnt; lia);
                      rewrite Hne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_652 with "Hcode"). }
      iIntros (h20) "Hrun".
      (* ---- 0x614  c.addi s3,s3,8 ---- *)
      assert (Hs3_14 : n14 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk14 s3_idx ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; discriminate)); exact Hs3v).
      assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                     = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi γt γd γs γfd h20 n14 (mword_of_int 0x614)
                (mword_of_int 8 : mword 6) s3_idx
                (mword_of_int (p + 8 + 8 * Z.of_nat (length done) + 8))
                (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_14 Esx8; symmetry; apply moi_add)
                with "[] Hrun").
      { iApply (uis_shp_614 with "Hcode"). }
      iIntros (h21) "Hrun".
      set (n15 := <[Regidx s3_idx
                    := regval_into_reg
                         (mword_of_int
                            (p + 8 + 8 * Z.of_nat (length done) + 8)
                          : mword 64)]> n14).
      assert (Hk15 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n15 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n14 (Regidx s3_idx) (Regidx r) _ Hr3);
            exact (Hk14 r Hr Hr2)).
      (* ---- 0x616..0x61a  parseredirs(ret, ps, es) ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h21 n15 (mword_of_int 0x616) a2_idx
                s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk15 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs5v;
                      symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_616 with "Hcode"). }
      iIntros (h22) "Hrun".
      set (n16 := <[Regidx a2_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat len)
                          : mword 64)]> n15).
      assert (Hk16 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n16 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n15 (Regidx a2_idx) (Regidx r) _
                       (ushp_cs_ne r a2_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk15 r Hr Hr2 Hr3)).
      iApply (wp_uk_cmv γt γd γs γfd h22 n16 (mword_of_int 0x618) a1_idx
                s4_idx (mword_of_int ps) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk16 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs4v;
                      symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_618 with "Hcode"). }
      iIntros (h23) "Hrun".
      set (n17 := <[Regidx a1_idx
                    := regval_into_reg (mword_of_int ps : mword 64)]> n16).
      assert (Hk17 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n17 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n16 (Regidx a1_idx) (Regidx r) _
                       (ushp_cs_ne r a1_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk16 r Hr Hr2 Hr3)).
      iApply (wp_uk_cmv γt γd γs γfd h23 n17 (mword_of_int 0x61a) a0_idx
                s1_idx (mword_of_int p) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk17 s1_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs1v;
                      symmetry; exact (ushp_mv_val p))
                with "[] Hrun").
      { iApply (uis_shp_61a with "Hcode"). }
      iIntros (h24) "Hrun".
      set (n18 := <[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> n17).
      assert (Hk18 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n18 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n17 (Regidx a0_idx) (Regidx r) _
                       (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk17 r Hr Hr2 Hr3)).
      (* ---- 0x61c  jal 4ac <parseredirs> ---- *)
      iApply (wp_uk_jal γt γd γs γfd h24 n18 (mword_of_int 0x61c)
                (mword_of_int 2096784 : mword 21) ra_idx
                (mword_of_int 0x4ac) (mword_of_int 0x620) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_61c with "Hcode"). }
      iIntros (h25) "Hrun".
      set (n19 := <[Regidx ra_idx
                    := regval_into_reg
                         (mword_of_int 0x620 : mword 64)]> n18).
      assert (Hk19 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n19 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n18 (Regidx ra_idx) (Regidx r) _
                       (ushp_cs_ne r ra_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk18 r Hr Hr2 Hr3)).
      assert (Eret19 : ret_pc (n19 !!! Regidx ra_idx)
                       = mword_of_int 0x620);
        [ rewrite (upd_eq n18 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x620 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_19 : n19 !!! Regidx a0_idx = mword_of_int p);
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n17 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))) | ].
      assert (Ha1_19 : n19 !!! Regidx a1_idx = mword_of_int ps);
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n17 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n16 (Regidx a1_idx)
                   (regval_into_reg (mword_of_int ps : mword 64))) | ].
      assert (Ha2_19 : n19 !!! Regidx a2_idx
                       = mword_of_int (s0 + Z.of_nat len));
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n17 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n16 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n15 (Regidx a2_idx)
                   (regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
      rewrite <- shpp_parseredirs.
      iApply (wp_kshp_parseredirs h25 n19 dq dw p ps s0 len nxt f
                (mword_of_int (s0 + Z.of_nat nxt)) nn
                Ha0_19 Ha1_19 Ha2_19 Hnxt eq_refl Hnosym Hs0 Hs64
                Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hrun").
      iIntros "Hcur Hstr Hws" (h26 n20) "%Hcs1920 %Ha0_20 Hrun".
      rewrite Eret19.
      assert (Hnz : ushp_skipws (len - nxt) nxt f = 0%nat)
        by exact (ushp_skipws_idem len e f Hele).
      assert (Enx : (nxt + ushp_skipws (len - nxt) nxt f)%nat = nxt)
        by (rewrite Hnz; lia).
      rewrite Enx.
      assert (Hk20 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n20 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3; rewrite (Hcs1920 r Hr);
            exact (Hk19 r Hr Hr2 Hr3)).
      (* ---- 0x620  c.mv s1,a0 ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h26 n20 (mword_of_int 0x620) s1_idx
                a0_idx (mword_of_int p) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_20; symmetry; exact (ushp_mv_val p))
                with "[] Hrun").
      { iApply (uis_shp_620 with "Hcode"). }
      iIntros (h27) "Hrun".
      set (n21 := <[Regidx s1_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> n20).
      assert (Hk21 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
                 Regidx r <> Regidx s3_idx ->
                 n21 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr1 Hr2 Hr3;
            rewrite (upd_ne n20 (Regidx s1_idx) (Regidx r) _ Hr1);
            exact (Hk20 r Hr Hr2 Hr3)).
      assert (Hs3_15 : n15 !!! Regidx s3_idx
                       = mword_of_int
                           (p + 8 + 8 * Z.of_nat (length done) + 8))
        by exact (upd_eq n14 (Regidx s3_idx)
                    (regval_into_reg
                       (mword_of_int
                          (p + 8 + 8 * Z.of_nat (length done) + 8)
                        : mword 64))).
      assert (HIs3 : n21 !!! Regidx s3_idx
                     = mword_of_int
                         (p + 8 + 8 * Z.of_nat (length (done ++ [tk])))).
      { rewrite ushp_len_app1.
        rewrite (upd_ne n20 (Regidx s1_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (Hcs1920 s3_idx ltac:(vm_compute; reflexivity)).
        rewrite (upd_ne n18 (Regidx ra_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n17 (Regidx a0_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n16 (Regidx a1_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n15 (Regidx a2_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Hs3_15. f_equal. rewrite Nat2Z.inj_succ. lia. }
      (* ---- and round again, with the token banked ---- *)
      iApply (IH (done ++ [tk]) nxt h27 n21
                (mword_of_int (s0 + Z.of_nat cur'))
                (mword_of_int (s0 + Z.of_nat e))
                Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz Hfp0 Hfp8 Hfpl Hfph
                Hp0 Hp8 Hpsz Hnxt
                ltac:(rewrite ushp_len_app1; cbn [length] in Hcnt; lia)
                ltac:(exact (ushp_tokens_skip len f e rest Hele Hrest))
                ltac:(rewrite (Hk21 s0_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs0v)
                ltac:(exact (upd_eq n20 (Regidx s1_idx)
                               (regval_into_reg (mword_of_int p : mword 64))))
                ltac:(rewrite ushp_len_app1;
                      rewrite (upd_ne n20 (Regidx s1_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hcs1920 s2_idx ltac:(vm_compute; reflexivity));
                      rewrite (upd_ne n18 (Regidx ra_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n17 (Regidx a0_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n16 (Regidx a1_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n15 (Regidx a2_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n14 (Regidx s3_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite Hs2_14; f_equal; lia)
                HIs3
                ltac:(rewrite (Hk21 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4v)
                ltac:(rewrite (Hk21 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5v)
                ltac:(rewrite (Hk21 s6_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs6v)
                ltac:(rewrite (Hk21 s7_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs7v)
                ltac:(rewrite (Hk21 s8_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs8v)
                ltac:(rewrite (Hk21 s9_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs9v)
                ltac:(rewrite (Hk21 s10_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs10v)
                ltac:(rewrite (Hk21 s11_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs11v)
                with "Hcode Hro [Hty Hav Hev] Hcur Hq Heq Hstr Hws Hsy Hrun").
      { rewrite /ushp_exec_pre.
        iSplitR; [ iPureIntro; rewrite ushp_len_app1;
                   cbn [length] in Hcnt; lia | ].
        iSplitR; [ iPureIntro; exact Hp0 | ].
        iSplitR; [ iPureIntro; exact Hp8 | ].
        iFrame "Hav Hev". rewrite /ushp_type_at. iExact "Hty". }
      iIntros "Hnode Hcur Hq Heq Hstr Hws Hsy" (hf mf) "%Hpres %Hs2f %Hs1f Hrun".
      rewrite ushp_app_cons.
      iApply ("Hcont" with "Hnode Hcur Hq Heq Hstr Hws Hsy [] [] [] Hrun").
      + iPureIntro. intros r Hr Hr1 Hr2 Hr3.
        rewrite (Hpres r Hr Hr1 Hr2 Hr3). exact (Hk21 r Hr Hr1 Hr2 Hr3).
      + iPureIntro. rewrite Hs2f ushp_len_app1.
        assert (El : (S (length done) + length rest)%nat
                     = (length done + length (tk :: rest))%nat)
          by (cbn [length]; lia).
        rewrite El. reflexivity.
      + iPureIntro. exact Hs1f.
  Qed.


  (* ---- parseexec, the whole function ---------------------------------- *)
  (* THE FRAME IS SPLIT IN TWO, BOTH WAYS.  gcc spills ra/s0/s1/s4/s5 before
     the [peek(ps,es,"(")] that decides whether this is a block, and the
     other eight only on the fall-through -- so the [parseblock] arm pays
     for five saves instead of thirteen.  The restores mirror it: the eight
     come back at 0x670 and the five at 0x5fa, and the [c.j 0x5f8] between
     them is the join.  Neither §4c lemma fits that shape, so the frame is
     four separate runs over §4b's two, at the SLOT ADDRESSES rather than at
     consecutive indexes.
     TAINT: [ushp_malloc_ok], through [execcmd]. *)
  Lemma wp_kshp_parseexec (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps s0 : Z) (len off : nat) (f : nat -> bv 8) (w0 : mword 64)
      (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    ushp_tokens len f off toks ->
    (length toks < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parseexec) (16 + (24 + nn)) -∗
    (∀ p : Z,
       ⌜ p + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 p toks -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (16 + (24 + nn)) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy Hrun Hcont".
    rewrite shpp_parseexec.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 128 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    (* ---- 0x590  c.addi16sp sp,sp,-128 ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x590)
              (mword_of_int 56 : mword 6) 16 (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_590 with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 16))).
    assert (Hspu : uint spn = uint sp0 - 128).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 16)) with (-128) by lia.
      exact (uv_avi_neg sp0 128 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 104) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 104)
      by (unfold spl; apply uint_moi; lia).
    set (sp3 := (mword_of_int (uint sp0 - 128) : mword 64)).
    assert (Hsp3u : uint sp3 = uint sp0 - 128)
      by (unfold sp3; apply uint_moi; lia).
    (* ---- the frame, cut into thirteen spill slots and three locals ---- *)
    iDestruct (ushp_frame_split sp0 spl 3 [(ra_idx, mword_of_int 15 : mword 6);
                 (s0_idx, mword_of_int 14 : mword 6);
                 (s1_idx, mword_of_int 13 : mword 6);
                 (s2_idx, mword_of_int 12 : mword 6);
                 (s3_idx, mword_of_int 11 : mword 6);
                 (s4_idx, mword_of_int 10 : mword 6);
                 (s5_idx, mword_of_int 9 : mword 6);
                 (s6_idx, mword_of_int 8 : mword 6);
                 (s7_idx, mword_of_int 7 : mword 6);
                 (s8_idx, mword_of_int 6 : mword 6);
                 (s9_idx, mword_of_int 5 : mword 6);
                 (s10_idx, mword_of_int 4 : mword 6);
                 (s11_idx, mword_of_int 3 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    iDestruct (ushp_frame_split spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hloc") as "[Hlc Hbot]".
    rewrite !big_sepL_cons big_sepL_nil.
    iDestruct "Hsl" as "(C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 &
                         C10 & C11 & C12 & _)".
    iDestruct "Hlc" as "([%wl0 L0] & [%wq Lq] & [%weq Leq] & _)".
    assert (E0 : uint sp0 - 104 - 8 * (Z.of_nat 0 + 1) = uint sp0 - 112)
      by lia.
    assert (E1 : uint sp0 - 104 - 8 * (Z.of_nat 1 + 1) = uint sp0 - 120)
      by lia.
    assert (E2 : uint sp0 - 104 - 8 * (Z.of_nat 2 + 1) = uint sp0 - 128)
      by lia.
    rewrite Hsplu E0 E1 E2.
    set (valsA := fun i : nat =>
                    match i with
                    | 0%nat => m !!! Regidx ra_idx
                    | 1%nat => m !!! Regidx s0_idx
                    | 2%nat => m !!! Regidx s1_idx
                    | 3%nat => m !!! Regidx s4_idx
                    | _ => m !!! Regidx s5_idx end).
    set (valsB := fun i : nat =>
                    match i with
                    | 0%nat => m !!! Regidx s2_idx
                    | 1%nat => m !!! Regidx s3_idx
                    | 2%nat => m !!! Regidx s6_idx
                    | 3%nat => m !!! Regidx s7_idx
                    | 4%nat => m !!! Regidx s8_idx
                    | 5%nat => m !!! Regidx s9_idx
                    | 6%nat => m !!! Regidx s10_idx
                    | _ => m !!! Regidx s11_idx end).
    set (adA := fun i : nat =>
                  uint sp0 - 8 * (Z.of_nat (match i with
                                            | 0%nat => 0 | 1%nat => 1
                                            | 2%nat => 2 | 3%nat => 5
                                            | _ => 6 end) + 1)).
    set (adB := fun i : nat =>
                  uint sp0 - 8 * (Z.of_nat (match i with
                                            | 0%nat => 3 | 1%nat => 4
                                            | 2%nat => 7 | 3%nat => 8
                                            | 4%nat => 9 | 5%nat => 10
                                            | 6%nat => 11
                                            | _ => 12 end) + 1)).
    (* ---- 0x592..0x59a  the FIRST five spills ---- *)
    iApply (wp_kshp_spill spn (24 + nn) [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x592 | 1%nat => 0x594
                              | 2%nat => 0x596 | 3%nat => 0x598
                              | 4%nat => 0x59a | _ => 0x59c end)
              adA valsA h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adA; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adA; apply ushp_slot_al; exact Hal8
                       | unfold valsA;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] [C0 C1 C2 C5 C6] Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_592 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_594 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_596 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_598 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_59a with "Hcode") | done ]. }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplitL "C0"; [ iExact "C0" | ].
      iSplitL "C1"; [ iExact "C1" | ].
      iSplitL "C2"; [ iExact "C2" | ].
      iSplitL "C5"; [ iExact "C5" | ].
      iSplitL "C6"; [ iExact "C6" | done ]. }
    iIntros "HslA" (h2) "Hrun". cbn [length].
    (* ---- 0x59c  c.addi4spn s0,sp,128 ---- *)
    assert (Hup : add_vec_int spn (8 * Z.of_nat 16) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 16) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    assert (Efp : add_vec spn
                    (sign_extend' 64
                       (caddi4spn_imm (mword_of_int 32 : mword 8))) = sp0).
    { assert (Ei : (sign_extend' 64
                      (caddi4spn_imm (mword_of_int 32 : mword 8)) : mword 64)
                   = mword_of_int (8 * Z.of_nat 16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ei. exact Hup. }
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 m1 (mword_of_int 0x59c)
              (mword_of_int 0 : mword 3) (mword_of_int 32 : mword 8) s0_idx
              sp0 (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1; symmetry; exact Efp)
              with "[] Hrun").
    { iApply (uis_shp_59c with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hs0_2 : m2 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
      symmetry. exact (moi_of_uint sp0). }
    (* ---- 0x59e  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x59e) s4_idx a0_idx
              (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_59e with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x5a0  c.mv s5,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m3 (mword_of_int 0x5a0) s5_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_5a0 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m4 := <[Regidx s5_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x5a2  auipc a2,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h5 m4 (mword_of_int 0x5a2)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x15a2) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5a2 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0x15a2 : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int 0x15a2)
      by exact (upd_eq m4 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x15a2 : mword 64))).
    (* ---- 0x5a6  addi a2,a2,-682 -- the open-paren table ---- *)
    iApply (wp_uk_addi γt γd γs γfd h6 m5 (mword_of_int 0x5a6)
              (mword_of_int 3414 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_block) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_5; unfold ushp_T_block;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5a6 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m6 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_block : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x5aa  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h7 m6 (mword_of_int 0x5aa)
              (mword_of_int 2096798 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x5ae) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5aa with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x5ae : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret7 : ret_pc (m7 !!! Regidx ra_idx) = mword_of_int 0x5ae).
    { rewrite (upd_eq m6 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5ae : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_7 : m7 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm7 a0_idx ltac:(vm_compute; discriminate))
              (Hm6 a0_idx ltac:(vm_compute; discriminate))
              (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_7 : m7 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm7 a1_idx ltac:(vm_compute; discriminate))
              (Hm6 a1_idx ltac:(vm_compute; discriminate))
              (Hm5 a1_idx ltac:(vm_compute; discriminate))
              (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Ha2_7 : m7 !!! Regidx a2_idx = mword_of_int ushp_T_block).
    { rewrite (Hm7 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_block : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h8 m7 dq dw true DfracDiscarded ps s0
              ushp_T_block len off 1 f (ushp_lit ushp_T_block)
              w0 (14 + nn)
              Ha0_7 Ha1_7 Ha2_7 Hoffle Hw0 Hs0 Hs64
              ltac:(unfold ushp_T_block; lia)
              ltac:(unfold ushp_T_block, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_block 1 DfracDiscarded
                ushp_T_block_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h9 m8) "%Hcs78 %Ha0_8 Hrun".
    rewrite Eret7.
    rewrite (ushp_peek_res_sym len f
               (off + ushp_skipws (len - off) off f)%nat 1 ushp_T_block
               Hnosym ushp_T_block_sym) in Ha0_8.
    (* ---- 0x5ae  c.bnez a0 -- NOT taken: this is not a block ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h9 m8 (mword_of_int 0x5ae)
              (mword_of_int 32 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x5ee) (24 + nn)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_8; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_5ae with "Hcode"). }
    iIntros (h10) "Hrun".
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = spn).
    { rewrite (Hcs78 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* THE REGISTERS THE SECOND SPILL RUN SAVES, read back once.  s0, s4
       and s5 are excluded because the prologue has already written them;
       every register the run actually saves is outside that set, so the
       [vm_compute] at each concrete index closes it.  It is hoisted rather
       than inlined because an [ltac:] under a [_] the goal mentions is
       THE divergence of this lane (see the file header). *)
    assert (Hk8 : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s4_idx -> Regidx q <> Regidx s5_idx ->
              m8 !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hqs0 Hqs4 Hqs5.
      rewrite (Hcs78 q Hq)
              (Hm7 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm5 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q Hqs5) (Hm3 q Hqs4) (Hm2 q Hqs0) (Hm1 q Hsp).
      reflexivity. }
    (* ---- 0x5b0..0x5be  the OTHER eight spills ---- *)
    iApply (wp_kshp_spill spn (24 + nn) [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x5b0 | 1%nat => 0x5b2
                              | 2%nat => 0x5b4 | 3%nat => 0x5b6
                              | 4%nat => 0x5b8 | 5%nat => 0x5ba
                              | 6%nat => 0x5bc | 7%nat => 0x5be
                              | _ => 0x5c0 end)
              adB valsB h10 m8 Hsp8
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adB; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adB; apply ushp_slot_al; exact Hal8
                       | unfold valsB; cbn;
                         refine (eq_sym (Hk8 _ _ _ _ _ _));
                         vm_compute; first [ reflexivity | discriminate ] ] ]))
              with "[] [C3 C4 C7 C8 C9 C10 C11 C12] Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_5b0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5be with "Hcode") | done ]. }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplitL "C3"; [ iExact "C3" | ].
      iSplitL "C4"; [ iExact "C4" | ].
      iSplitL "C7"; [ iExact "C7" | ].
      iSplitL "C8"; [ iExact "C8" | ].
      iSplitL "C9"; [ iExact "C9" | ].
      iSplitL "C10"; [ iExact "C10" | ].
      iSplitL "C11"; [ iExact "C11" | ].
      iSplitL "C12"; [ iExact "C12" | done ]. }
    iIntros "HslB" (h11) "Hrun". cbn [length].
    (* ---- 0x5c0  c.mv s2,a0 -- argc = 0, and a0 IS 0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h11 m8 (mword_of_int 0x5c0) s2_idx a0_idx
              (mword_of_int 0) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_8; symmetry; exact (ushp_mv_val 0))
              with "[] Hrun").
    { iApply (uis_shp_5c0 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x5c2  jal 1d2 <execcmd> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h12 m9 (mword_of_int 0x5c2)
              (mword_of_int 2096144 : mword 21) ra_idx
              (mword_of_int 0x1d2) (mword_of_int 0x5c6) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5c2 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x5c6 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret10 : ret_pc (m10 !!! Regidx ra_idx) = mword_of_int 0x5c6).
    { rewrite (upd_eq m9 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5c6 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_execcmd.
    iApply (wp_kshp_execcmd h13 m10 s0 (10 + nn) with "Hcode Hrun").
    iIntros (h14 m11 p) "%Hcs1011 %Ha0_11 %Hpb Hnode Hrun".
    rewrite Eret10.
    destruct Hpb as [ Hp0 [ Hp16 Hpsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Hp64 : 0 <= p /\ p + 168 < Z64)
      by (rewrite H38 in Hpsz; unfold Z64; lia).
    assert (Hp8 : p mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp16 ]. }
    (* ---- 0x5c6  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h14 m11 (mword_of_int 0x5c6) s3_idx a0_idx
              (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5c6 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x5c8  c.mv s11,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h15 m12 (mword_of_int 0x5c8) s11_idx
              a0_idx (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate))
                      Ha0_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5c8 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m13 := <[Regidx s11_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m12).
    assert (Hm13 : forall q : mword 5, Regidx q <> Regidx s11_idx ->
                     m13 !!! Regidx q = m12 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m12 (Regidx s11_idx) (Regidx q) _ Hq)).
    (* ---- the register values the calls below read, once ---- *)
    assert (Hk13 : forall q : mword 5, ucallee_saved_idx q = true ->
                     Regidx q <> Regidx s2_idx -> Regidx q <> Regidx s3_idx ->
                     Regidx q <> Regidx s11_idx ->
                     m13 !!! Regidx q = m7 !!! Regidx q).
    { intros q Hq H2 H3 H11.
      rewrite (Hm13 q H11) (Hm12 q H3)
              (Hcs1011 q Hq)
              (Hm10 q (ushp_cs_ne q ra_idx Hq
                         ltac:(vm_compute; reflexivity)))
              (Hm9 q H2) (Hcs78 q Hq). reflexivity. }
    assert (Hs4_13 : m13 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hk13 s4_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hm6 s4_idx ltac:(vm_compute; discriminate))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs5_13 : m13 !!! Regidx s5_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hk13 s5_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm7 s5_idx ltac:(vm_compute; discriminate))
              (Hm6 s5_idx ltac:(vm_compute; discriminate))
              (Hm5 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s5_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Hs0_13 : m13 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hk13 s0_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm7 s0_idx ltac:(vm_compute; discriminate))
              (Hm6 s0_idx ltac:(vm_compute; discriminate))
              (Hm5 s0_idx ltac:(vm_compute; discriminate))
              (Hm4 s0_idx ltac:(vm_compute; discriminate))
              (Hm3 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_2. }
    (* ---- 0x5ca  c.mv a2,s5 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h16 m13 (mword_of_int 0x5ca) a2_idx
              s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_13; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_5ca with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m14 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len)
                        : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x5cc  c.mv a1,s4 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h17 m14 (mword_of_int 0x5cc) a1_idx
              s4_idx (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm14 s4_idx ltac:(vm_compute; discriminate))
                      Hs4_13; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_5cc with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m15 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x5ce  jal 4ac <parseredirs> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h18 m15 (mword_of_int 0x5ce)
              (mword_of_int 2096862 : mword 21) ra_idx
              (mword_of_int 0x4ac) (mword_of_int 0x5d2) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5ce with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m16 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x5d2 : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret16 : ret_pc (m16 !!! Regidx ra_idx) = mword_of_int 0x5d2).
    { rewrite (upd_eq m15 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5d2 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_16 : m16 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm16 a0_idx ltac:(vm_compute; discriminate))
              (Hm15 a0_idx ltac:(vm_compute; discriminate))
              (Hm14 a0_idx ltac:(vm_compute; discriminate))
              (Hm13 a0_idx ltac:(vm_compute; discriminate))
              (Hm12 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_11. }
    assert (Ha1_16 : m16 !!! Regidx a1_idx = mword_of_int ps).
    { rewrite (Hm16 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m14 (Regidx a1_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha2_16 : m16 !!! Regidx a2_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm16 a2_idx ltac:(vm_compute; discriminate))
              (Hm15 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m13 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    (* the cursor has already been moved once, by the block peek *)
    pose (off1 := (off + ushp_skipws (len - off) off f)%nat).
    assert (Hoff1e : off1 = (off + ushp_skipws (len - off) off f)%nat)
      by reflexivity.
    assert (Hoff1 : (off1 <= len)%nat);
      [ rewrite Hoff1e; pose proof (ushp_skipws_le (len - off) off f); lia | ].
    assert (Hz1 : ushp_skipws (len - off1) off1 f = 0%nat)
      by exact (ushp_skipws_idem len off f Hoffle).
    assert (Ez1 : (off1 + ushp_skipws (len - off1) off1 f)%nat = off1)
      by (rewrite Hz1; lia).
    rewrite <- shpp_parseredirs.
    iApply (wp_kshp_parseredirs h19 m16 dq dw p ps s0 len off1 f
              (mword_of_int (s0 + Z.of_nat off1)) nn
              Ha0_16 Ha1_16 Ha2_16 Hoff1 eq_refl Hnosym Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hrun").
    iIntros "Hcur Hstr Hws" (h20 m17) "%Hcs1617 %Ha0_17 Hrun".
    rewrite Eret16 Ez1.
    (* ---- 0x5d2  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h20 m17 (mword_of_int 0x5d2) s1_idx
              a0_idx (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_17; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5d2 with "Hcode"). }
    iIntros (h21) "Hrun".
    set (m18 := <[Regidx s1_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs3_18 : m18 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hm18 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1617 s3_idx ltac:(vm_compute; reflexivity))
              (Hm16 s3_idx ltac:(vm_compute; discriminate))
              (Hm15 s3_idx ltac:(vm_compute; discriminate))
              (Hm14 s3_idx ltac:(vm_compute; discriminate))
              (Hm13 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx s3_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    (* ---- 0x5d4  c.addi s3,s3,8 -- s3 = &argv[0] ---- *)
    assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                   = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h21 m18 (mword_of_int 0x5d4)
              (mword_of_int 8 : mword 6) s3_idx (mword_of_int (p + 8))
              (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_18 Esx8; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_5d4 with "Hcode"). }
    iIntros (h22) "Hrun".
    set (m19 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int (p + 8) : mword 64)]> m18).
    assert (Hm19 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m19 !!! Regidx q = m18 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m18 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x5d6/0x5da  the argument-loop table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h22 m19 (mword_of_int 0x5d6)
              (mword_of_int 1 : mword 20) s6_idx
              (mword_of_int 0x15d6) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5d6 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (m20 := <[Regidx s6_idx
                  := regval_into_reg (mword_of_int 0x15d6 : mword 64)]> m19).
    assert (Hm20 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                     m20 !!! Regidx q = m19 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m19 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_20 : m20 !!! Regidx s6_idx = mword_of_int 0x15d6)
      by exact (upd_eq m19 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int 0x15d6 : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h23 m20 (mword_of_int 0x5da)
              (mword_of_int 3394 : mword 12) s6_idx s6_idx
              (mword_of_int ushp_T_arg) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_20; unfold ushp_T_arg;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5da with "Hcode"). }
    iIntros (h24) "Hrun".
    set (m21 := <[Regidx s6_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_arg : mword 64)]> m20).
    assert (Hm21 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                     m21 !!! Regidx q = m20 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m20 (Regidx s6_idx) (Regidx q) _ Hq)).
    (* ---- 0x5de/0x5e2  &eq and &q, the two locals ---- *)
    assert (Hs0_21 : m21 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm21 s0_idx ltac:(vm_compute; discriminate))
              (Hm20 s0_idx ltac:(vm_compute; discriminate))
              (Hm19 s0_idx ltac:(vm_compute; discriminate))
              (Hm18 s0_idx ltac:(vm_compute; discriminate))
              (Hcs1617 s0_idx ltac:(vm_compute; reflexivity))
              (Hm16 s0_idx ltac:(vm_compute; discriminate))
              (Hm15 s0_idx ltac:(vm_compute; discriminate))
              (Hm14 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_13. }
    iApply (wp_uk_addi γt γd γs γfd h24 m21 (mword_of_int 0x5de)
              (mword_of_int 3968 : mword 12) s0_idx s8_idx
              (mword_of_int (uint sp0 - 128)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_21;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 3968 : mword 12)
                                  : mword 64) = mword_of_int (-128))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_5de with "Hcode"). }
    iIntros (h25) "Hrun".
    set (m22 := <[Regidx s8_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 128) : mword 64)]> m21).
    assert (Hm22 : forall q : mword 5, Regidx q <> Regidx s8_idx ->
                     m22 !!! Regidx q = m21 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m21 (Regidx s8_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_addi γt γd γs γfd h25 m22 (mword_of_int 0x5e2)
              (mword_of_int 3976 : mword 12) s0_idx s7_idx
              (mword_of_int (uint sp0 - 120)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm22 s0_idx ltac:(vm_compute; discriminate))
                      Hs0_21;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 3976 : mword 12)
                                  : mword 64) = mword_of_int (-120))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_5e2 with "Hcode"). }
    iIntros (h26) "Hrun".
    set (m23 := <[Regidx s7_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 120) : mword 64)]> m22).
    assert (Hm23 : forall q : mword 5, Regidx q <> Regidx s7_idx ->
                     m23 !!! Regidx q = m22 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m22 (Regidx s7_idx) (Regidx q) _ Hq)).
    (* ---- 0x5e6/0x5ea  the two constants ---- *)
    iApply (wp_uk_li γt γd γs γfd h26 m23 (mword_of_int 0x5e6)
              (mword_of_int 97 : mword 12) s10_idx (mword_of_int 97)
              (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 97))
              with "[] Hrun").
    { iApply (uis_shp_5e6 with "Hcode"). }
    iIntros (h27) "Hrun".
    set (m24 := <[Regidx s10_idx
                  := regval_into_reg (mword_of_int 97 : mword 64)]> m23).
    assert (Hm24 : forall q : mword 5, Regidx q <> Regidx s10_idx ->
                     m24 !!! Regidx q = m23 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m23 (Regidx s10_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cli γt γd γs γfd h27 m24 (mword_of_int 0x5ea)
              (mword_of_int 10 : mword 6) s9_idx (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_5ea with "Hcode"). }
    iIntros (h28) "Hrun".
    set (m25 := <[Regidx s9_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 10 : mword 6)
                        : mword 64)]> m24).
    assert (Hm25 : forall q : mword 5, Regidx q <> Regidx s9_idx ->
                     m25 !!! Regidx q = m24 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m24 (Regidx s9_idx) (Regidx q) _ Hq)).
    (* ---- 0x5ec  c.j 0x622 -- into the loop ---- *)
    iApply (wp_uk_cj γt γd γs γfd h28 m25 (mword_of_int 0x5ec)
              (mword_of_int 27 : mword 11) (mword_of_int 0x622) (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5ec with "Hcode"). }
    iIntros (h29) "Hrun".
    (* ---- the register file the loop is entered in ---- *)
    assert (Hk25 : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s3_idx ->
              Regidx q <> Regidx s6_idx -> Regidx q <> Regidx s7_idx ->
              Regidx q <> Regidx s8_idx -> Regidx q <> Regidx s9_idx ->
              Regidx q <> Regidx s10_idx ->
              m25 !!! Regidx q = m13 !!! Regidx q).
    { intros q Hq H1 H3 H6 H7 H8 H9 H10.
      rewrite (Hm25 q H9) (Hm24 q H10) (Hm23 q H7) (Hm22 q H8)
              (Hm21 q H6) (Hm20 q H6) (Hm19 q H3) (Hm18 q H1)
              (Hcs1617 q Hq)
              (Hm16 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity))).
      reflexivity. }
    assert (Hs2_13 : m13 !!! Regidx s2_idx = mword_of_int 0).
    { rewrite (Hm13 s2_idx ltac:(vm_compute; discriminate))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1011 s2_idx ltac:(vm_compute; reflexivity))
              (Hm10 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx s2_idx)
               (regval_into_reg (mword_of_int 0 : mword 64))). }
    assert (Hs11_13 : m13 !!! Regidx s11_idx = mword_of_int p)
      by exact (upd_eq m12 (Regidx s11_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hkm : forall q : mword 5, Regidx q <> Regidx s1_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s6_idx ->
              Regidx q <> Regidx s7_idx -> Regidx q <> Regidx s8_idx ->
              Regidx q <> Regidx s9_idx -> Regidx q <> Regidx s10_idx ->
              m25 !!! Regidx q = m18 !!! Regidx q).
    { intros q H1 H3 H6 H7 H8 H9 H10.
      rewrite (Hm25 q H9) (Hm24 q H10) (Hm23 q H7) (Hm22 q H8)
              (Hm21 q H6) (Hm20 q H6) (Hm19 q H3). reflexivity. }
    assert (Hs1_25 : m25 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hm25 s1_idx ltac:(vm_compute; discriminate))
              (Hm24 s1_idx ltac:(vm_compute; discriminate))
              (Hm23 s1_idx ltac:(vm_compute; discriminate))
              (Hm22 s1_idx ltac:(vm_compute; discriminate))
              (Hm21 s1_idx ltac:(vm_compute; discriminate))
              (Hm20 s1_idx ltac:(vm_compute; discriminate))
              (Hm19 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m17 (Regidx s1_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    assert (Hs3_25 : m25 !!! Regidx s3_idx = mword_of_int (p + 8)).
    { rewrite (Hm25 s3_idx ltac:(vm_compute; discriminate))
              (Hm24 s3_idx ltac:(vm_compute; discriminate))
              (Hm23 s3_idx ltac:(vm_compute; discriminate))
              (Hm22 s3_idx ltac:(vm_compute; discriminate))
              (Hm21 s3_idx ltac:(vm_compute; discriminate))
              (Hm20 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m18 (Regidx s3_idx)
               (regval_into_reg (mword_of_int (p + 8) : mword 64))). }
    assert (Hs6_25 : m25 !!! Regidx s6_idx = mword_of_int ushp_T_arg).
    { rewrite (Hm25 s6_idx ltac:(vm_compute; discriminate))
              (Hm24 s6_idx ltac:(vm_compute; discriminate))
              (Hm23 s6_idx ltac:(vm_compute; discriminate))
              (Hm22 s6_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m20 (Regidx s6_idx)
               (regval_into_reg (mword_of_int ushp_T_arg : mword 64))). }
    assert (Hs7_25 : m25 !!! Regidx s7_idx
                     = mword_of_int (uint sp0 - 120)).
    { rewrite (Hm25 s7_idx ltac:(vm_compute; discriminate))
              (Hm24 s7_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m22 (Regidx s7_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 120) : mword 64))). }
    assert (Hs8_25 : m25 !!! Regidx s8_idx
                     = mword_of_int (uint sp0 - 128)).
    { rewrite (Hm25 s8_idx ltac:(vm_compute; discriminate))
              (Hm24 s8_idx ltac:(vm_compute; discriminate))
              (Hm23 s8_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m21 (Regidx s8_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 128) : mword 64))). }
    assert (Hs9_25 : m25 !!! Regidx s9_idx = mword_of_int 10).
    { rewrite (upd_eq m24 (Regidx s9_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 10 : mword 6)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs10_25 : m25 !!! Regidx s10_idx = mword_of_int 97).
    { rewrite (Hm25 s10_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m23 (Regidx s10_idx)
               (regval_into_reg (mword_of_int 97 : mword 64))). }
    assert (Hsp8al : (uint sp0 - 128) mod 8 = 0).
    { rewrite Zminus_mod Hal8. reflexivity. }
    (* ---- 0x622..0x662  THE ARGUMENT LOOP ---- *)
    iApply (wp_kshp_pex_loop dq dw dv s0 ps p (uint sp0) len f nn
              toks (@nil (nat * nat)) off1 h29 m25 wq weq
              Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz
              ltac:(lia) Hsp8al ltac:(lia) ltac:(lia)
              Hp0 Hp8 ltac:(lia) Hoff1 ltac:(cbn [length]; lia)
              ltac:(exact (ushp_tokens_skip len f off toks Hoffle Htoks))
              ltac:(rewrite (Hk25 s0_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs0_13)
              Hs1_25
              ltac:(rewrite (Hk25 s2_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    rewrite Hs2_13; f_equal; cbn [length]; lia)
              ltac:(rewrite Hs3_25; f_equal; cbn [length]; lia)
              ltac:(rewrite (Hk25 s4_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs4_13)
              ltac:(rewrite (Hk25 s5_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs5_13)
              Hs6_25 Hs7_25 Hs8_25 Hs9_25 Hs10_25
              ltac:(rewrite (Hk25 s11_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs11_13)
              with "Hcode Hro Hnode Hcur Lq Leq Hstr Hws Hsy Hrun").
    iIntros "Hnode Hcur [%vq Lq] [%veq Leq] Hstr Hws Hsy"
      (h30 mf) "%Hpresf %Hs2f %Hs1f Hrun".
    assert (Hs2f' : mf !!! Regidx s2_idx
                    = mword_of_int (Z.of_nat (length toks))) by exact Hs2f.
    assert (Hsp_f : mf !!! Regidx csp_rs1 = spn).
    { rewrite (Hpresf csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hk25 csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1011 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp8. }
    assert (Hs11_f : mf !!! Regidx s11_idx = mword_of_int p).
    { rewrite (Hpresf s11_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hk25 s11_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hs11_13. }
    (* ---- 0x662  c.slli s2,s2,0x3 ---- *)
    iApply (wp_uk_cslli γt γd γs γfd h30 mf (mword_of_int 0x662)
              (mword_of_int 3 : mword 6) s2_idx
              (mword_of_int (8 * Z.of_nat (length toks))) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2f'
                      (moi_shl (Z.of_nat (length toks)) 3 ltac:(lia));
                    f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_662 with "Hcode"). }
    iIntros (h31) "Hrun".
    set (mg := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (8 * Z.of_nat (length toks))
                       : mword 64)]> mf).
    assert (Hmg : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    mg !!! Regidx q = mf !!! Regidx q)
      by (intros q Hq; exact (upd_ne mf (Regidx s2_idx) (Regidx q) _ Hq)).
    assert (Hs2_g : mg !!! Regidx s2_idx
                    = mword_of_int (8 * Z.of_nat (length toks)))
      by exact (upd_eq mf (Regidx s2_idx)
                  (regval_into_reg
                     (mword_of_int (8 * Z.of_nat (length toks))
                      : mword 64))).
    (* ---- 0x664  add a5,s11,s2 ---- *)
    iApply (wp_uk_add γt γd γs γfd h31 mg (mword_of_int 0x664)
              s11_idx s2_idx a5_idx
              (mword_of_int (p + 8 * Z.of_nat (length toks))) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_g (Hmg s11_idx ltac:(vm_compute; discriminate))
                      Hs11_f; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_664 with "Hcode"). }
    iIntros (h32) "Hrun".
    set (mh := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (p + 8 * Z.of_nat (length toks))
                       : mword 64)]> mg).
    assert (Hmh : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    mh !!! Regidx q = mg !!! Regidx q)
      by (intros q Hq; exact (upd_ne mg (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_h : mh !!! Regidx a5_idx
                    = mword_of_int (p + 8 * Z.of_nat (length toks)))
      by exact (upd_eq mg (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int (p + 8 * Z.of_nat (length toks))
                      : mword 64))).
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Ez : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    iDestruct "Hnode" as "(%Hdl & _ & _ & Hty & Hav & Hev)".
    (* ---- 0x668  sd zero,8(a5) -- argv[argc] = 0, which it already is ---- *)
    iDestruct (ushp_slots_cap s0 (p + 8) toks fst Htlen with "Hav")
      as "[Hav0 Havc]".
    iApply (wp_uk_sd γt γd γs γfd h32 mh (mword_of_int 0x668)
              (mword_of_int 8 : mword 12) a5_idx x0_idx
              (p + 8 + 8 * Z.of_nat (length toks)) (mword_of_int 0)
              (24 + nn)
              ltac:(rewrite Ha5_h
                      (uint_moi (p + 8 * Z.of_nat (length toks))
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(exact (ushp_slot_al8 p 1 (length toks) Hp8))
              with "[] [Hav0] Hrun").
    { iApply (uis_shp_668 with "Hcode"). }
    { iExact "Hav0". }
    iIntros "Hav0" (h33) "Hrun".
    rewrite Hx0 Ez.
    iDestruct ("Havc" with "Hav0") as "Hav".
    (* ---- 0x66c  sd zero,88(a5) -- eargv[argc] = 0 ---- *)
    iDestruct (ushp_slots_cap s0 (p + 88) toks snd Htlen with "Hev")
      as "[Hev0 Hevc]".
    iApply (wp_uk_sd γt γd γs γfd h33 mh (mword_of_int 0x66c)
              (mword_of_int 88 : mword 12) a5_idx x0_idx
              (p + 88 + 8 * Z.of_nat (length toks)) (mword_of_int 0)
              (24 + nn)
              ltac:(rewrite Ha5_h
                      (uint_moi (p + 8 * Z.of_nat (length toks))
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(exact (ushp_slot_al8 p 11 (length toks) Hp8))
              with "[] [Hev0] Hrun").
    { iApply (uis_shp_66c with "Hcode"). }
    { iExact "Hev0". }
    iIntros "Hev0" (h34) "Hrun".
    rewrite Hx0 Ez.
    iDestruct ("Hevc" with "Hev0") as "Hev".
    (* ---- 0x670..0x67e  the EIGHT restores ---- *)
    assert (Hsp_h : mh !!! Regidx csp_rs1 = spn).
    { rewrite (Hmh csp_rs1 ltac:(vm_compute; discriminate))
              (Hmg csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_f. }
    iApply (wp_kshp_restore spn (24 + nn) [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x670 | 1%nat => 0x672
                              | 2%nat => 0x674 | 3%nat => 0x676
                              | 4%nat => 0x678 | 5%nat => 0x67a
                              | 6%nat => 0x67c | 7%nat => 0x67e
                              | _ => 0x680 end)
              adB valsB h34 mh Hsp_h
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adB; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adB; apply ushp_slot_al; exact Hal8
                       | split; [ unfold unot_sp; vm_compute; discriminate
                                | vm_compute; discriminate ] ] ]))
              with "[] HslB Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_670 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_672 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_674 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_676 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_678 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_67a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_67c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_67e with "Hcode") | done ]. }
    iIntros "HslB" (h35) "Hrun". cbn [length].
    set (mi := ushp_spillback [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] valsB mh).
    assert (Hmi : forall q : mword 5,
              (forall (i : nat) (r : mword 5) (u : mword 6),
                 [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] !! i = Some (r, u) -> Regidx q <> Regidx r) ->
              mi !!! Regidx q = mh !!! Regidx q)
      by (intros q Hq; exact (ushp_spillback_ne [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] valsB mh q Hq)).
    assert (Hs1_i : mi !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hmi s1_idx
                 ltac:(intros i r u Hi;
                       destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                       cbn in Hi; try discriminate;
                       injection Hi as Hr Hu0; subst;
                       vm_compute; discriminate))
              (Hmh s1_idx ltac:(vm_compute; discriminate))
              (Hmg s1_idx ltac:(vm_compute; discriminate)). exact Hs1f. }
    assert (Hsp_i : mi !!! Regidx csp_rs1 = spn).
    { rewrite (Hmi csp_rs1
                 ltac:(intros i r u Hi;
                       destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                       cbn in Hi; try discriminate;
                       injection Hi as Hr Hu0; subst;
                       vm_compute; discriminate)). exact Hsp_h. }
    (* ---- 0x680  c.j 0x5f8 -- into the common tail ---- *)
    iApply (wp_uk_cj γt γd γs γfd h35 mi (mword_of_int 0x680)
              (mword_of_int 1980 : mword 11) (mword_of_int 0x5f8) (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_680 with "Hcode"). }
    iIntros (h36) "Hrun".
    (* ---- 0x5f8  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h36 mi (mword_of_int 0x5f8) a0_idx
              s1_idx (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_i; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5f8 with "Hcode"). }
    iIntros (h37) "Hrun".
    set (mj := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> mi).
    assert (Hmj : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    mj !!! Regidx q = mi !!! Regidx q)
      by (intros q Hq; exact (upd_ne mi (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hsp_j : mj !!! Regidx csp_rs1 = spn).
    { rewrite (Hmj csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_i. }
    (* ---- 0x5fa..0x602  the FIVE restores ---- *)
    iApply (wp_kshp_restore spn (24 + nn) [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x5fa | 1%nat => 0x5fc
                              | 2%nat => 0x5fe | 3%nat => 0x600
                              | 4%nat => 0x602 | _ => 0x604 end)
              adA valsA h37 mj Hsp_j
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adA; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adA; apply ushp_slot_al; exact Hal8
                       | split; [ unfold unot_sp; vm_compute; discriminate
                                | vm_compute; discriminate ] ] ]))
              with "[] HslA Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_5fa with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5fc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5fe with "Hcode") | ].
      iSplit; [ iApply (uis_shp_600 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_602 with "Hcode") | done ]. }
    iIntros "HslA" (h38) "Hrun". cbn [length].
    set (mk := ushp_spillback [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] valsA mj).
    assert (Hspk : mk !!! Regidx csp_rs1 = spn).
    { rewrite (ushp_spillback_ne [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] valsA mj csp_rs1
                 ltac:(intros i r u Hi;
                       destruct i as [| [| [| [| [| i ]]]]];
                       cbn in Hi; try discriminate;
                       injection Hi as Hr Hu0; subst;
                       vm_compute; discriminate)). exact Hsp_j. }
    assert (Hrak : mk !!! Regidx ra_idx = valsA 0%nat)
      by exact (ushp_spillback_ra [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] (mword_of_int 15 : mword 6) valsA mj
                  eq_refl
                  ltac:(intros i r u Hi;
                        destruct i as [| [| [| [| i ]]]];
                        cbn in Hi; try discriminate;
                        injection Hi as Hr Hu0; subst;
                        vm_compute; discriminate)).
    (* ---- the frame, put back together ---- *)
    set (valsAll := fun i : nat =>
                      match i with
                      | 0%nat => m !!! Regidx ra_idx
                      | 1%nat => m !!! Regidx s0_idx
                      | 2%nat => m !!! Regidx s1_idx
                      | 3%nat => m !!! Regidx s2_idx
                      | 4%nat => m !!! Regidx s3_idx
                      | 5%nat => m !!! Regidx s4_idx
                      | 6%nat => m !!! Regidx s5_idx
                      | 7%nat => m !!! Regidx s6_idx
                      | 8%nat => m !!! Regidx s7_idx
                      | 9%nat => m !!! Regidx s8_idx
                      | 10%nat => m !!! Regidx s9_idx
                      | 11%nat => m !!! Regidx s10_idx
                      | _ => m !!! Regidx s11_idx end).
    rewrite !big_sepL_cons big_sepL_nil.
    iDestruct "HslA" as "(A0 & A1 & A2 & A3 & A4 & _)".
    iDestruct "HslB" as "(B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & _)".
    (* ---- 0x604  c.addi16sp sp,sp,128 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h38 mk (mword_of_int 0x604)
              (mword_of_int 8 : mword 6) 16 (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 B5 B6 B7 L0 Lq Leq Hbot]
                   Hrun").
    { iApply (uis_shp_604 with "Hcode"). }
    { rewrite Hspk Hup.
      iDestruct (ushp_frame_join spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                   (fun i : nat => match i with
                                   | 0%nat => wl0 | 1%nat => vq
                                   | _ => veq end)
                   ltac:(cbn [length]; lia)
                   with "[L0 Lq Leq] Hbot") as "Hloc".
      { rewrite !big_sepL_cons big_sepL_nil Hsplu E0 E1 E2.
        iSplitL "L0"; [ iExact "L0" | ].
        iSplitL "Lq"; [ iExact "Lq" | ].
        iSplitL "Leq"; [ iExact "Leq" | done ]. }
      iDestruct (ushp_frame_join sp0 spl 3 [(ra_idx, mword_of_int 15 : mword 6);
                 (s0_idx, mword_of_int 14 : mword 6);
                 (s1_idx, mword_of_int 13 : mword 6);
                 (s2_idx, mword_of_int 12 : mword 6);
                 (s3_idx, mword_of_int 11 : mword 6);
                 (s4_idx, mword_of_int 10 : mword 6);
                 (s5_idx, mword_of_int 9 : mword 6);
                 (s6_idx, mword_of_int 8 : mword 6);
                 (s7_idx, mword_of_int 7 : mword 6);
                 (s8_idx, mword_of_int 6 : mword 6);
                 (s9_idx, mword_of_int 5 : mword 6);
                 (s10_idx, mword_of_int 4 : mword 6);
                 (s11_idx, mword_of_int 3 : mword 6)] valsAll
                   ltac:(cbn [length]; lia)
                   with "[A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 B5 B6 B7] Hloc")
        as "Hstk".
      { rewrite !big_sepL_cons big_sepL_nil.
        iSplitL "A0"; [ iExact "A0" | ].
        iSplitL "A1"; [ iExact "A1" | ].
        iSplitL "A2"; [ iExact "A2" | ].
        iSplitL "B0"; [ iExact "B0" | ].
        iSplitL "B1"; [ iExact "B1" | ].
        iSplitL "A3"; [ iExact "A3" | ].
        iSplitL "A4"; [ iExact "A4" | ].
        iSplitL "B2"; [ iExact "B2" | ].
        iSplitL "B3"; [ iExact "B3" | ].
        iSplitL "B4"; [ iExact "B4" | ].
        iSplitL "B5"; [ iExact "B5" | ].
        iSplitL "B6"; [ iExact "B6" | ].
        iSplitL "B7"; [ iExact "B7" | done ]. }
      iExact "Hstk". }
    rewrite Hspk Hup. iIntros (h39) "Hrun".
    (* ---- 0x606  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h39
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mk)
              (mword_of_int 0x606) ra_idx (ret_pc (m !!! Regidx ra_idx))
              (16 + (24 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mk (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrak; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_606 with "Hcode"). }
    iIntros (h40) "Hrun".
    iApply ("Hcont" $! p with "[] [Hty Hav Hev] Hcur Hstr Hws Hsy [] [] Hrun").
    - iPureIntro. lia.
    - iApply ushp_exec_pre_at. rewrite /ushp_exec_pre.
      iSplitR; [ iPureIntro; exact Htlen | ].
      iSplitR; [ iPureIntro; exact Hp0 | ].
      iSplitR; [ iPureIntro; exact Hp8 | ].
      iSplitL "Hty"; [ iExact "Hty" | ].
      iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] valsA m mj sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        rewrite (Hmj q (ushp_cs_ne q a0_idx Hq
                          ltac:(vm_compute; reflexivity))).
        apply ushp_spillback_eq.
        * intros Hmiss2.
          assert (HmB : forall (i : nat) (r' : mword 5) (u : mword 6),
                    [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] !! i = Some (r', u) -> Regidx q <> Regidx r')
            by (intros i r' u Hi He; exact (Hmiss2 i r' u Hi (eq_sym He))).
          rewrite (Hmh q (ushp_cs_ne q a5_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hmg q (HmB 0%nat s2_idx (mword_of_int 12 : mword 6)
                            eq_refl))
                  (Hpresf q Hq
                     (Hmiss 2%nat s1_idx (mword_of_int 13 : mword 6) eq_refl)
                     (HmB 0%nat s2_idx (mword_of_int 12 : mword 6) eq_refl)
                     (HmB 1%nat s3_idx (mword_of_int 11 : mword 6) eq_refl))
                  (Hk25 q Hq
                     (Hmiss 2%nat s1_idx (mword_of_int 13 : mword 6) eq_refl)
                     (HmB 1%nat s3_idx (mword_of_int 11 : mword 6) eq_refl)
                     (HmB 2%nat s6_idx (mword_of_int 8 : mword 6) eq_refl)
                     (HmB 3%nat s7_idx (mword_of_int 7 : mword 6) eq_refl)
                     (HmB 4%nat s8_idx (mword_of_int 6 : mword 6) eq_refl)
                     (HmB 5%nat s9_idx (mword_of_int 5 : mword 6) eq_refl)
                     (HmB 6%nat s10_idx (mword_of_int 4 : mword 6) eq_refl))
                  (Hm13 q (HmB 7%nat s11_idx (mword_of_int 3 : mword 6)
                             eq_refl))
                  (Hm12 q (HmB 1%nat s3_idx (mword_of_int 11 : mword 6)
                             eq_refl))
                  (Hcs1011 q Hq)
                  (Hm10 q (ushp_cs_ne q ra_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hm9 q (HmB 0%nat s2_idx (mword_of_int 12 : mword 6)
                            eq_refl))
                  (Hcs78 q Hq)
                  (Hm7 q (ushp_cs_ne q ra_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hm6 q (ushp_cs_ne q a2_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hm5 q (ushp_cs_ne q a2_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hm4 q (Hmiss 4%nat s5_idx (mword_of_int 9 : mword 6)
                            eq_refl))
                  (Hm3 q (Hmiss 3%nat s4_idx (mword_of_int 10 : mword 6)
                            eq_refl))
                  (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 14 : mword 6)
                            eq_refl))
                  (Hm1 q Hqsp).
          reflexivity.
        * intros i r u Hi He.
          destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
            cbn in Hi; try discriminate;
            injection Hi as Hr Hu0; subst; unfold valsB;
            rewrite <- He; reflexivity.
    - iPureIntro.
      rewrite (upd_ne mk (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq mi (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* §12 parsepipe @0x682 and parseline @0x6e2 -- the two one-line bodies.  *)
  (*                                                                       *)
  (*   parsepipe: cmd = parseexec(ps,es);                                   *)
  (*              if(peek(ps,es,"|")) { ... }  return cmd;                  *)
  (*   parseline: cmd = parsepipe(ps,es);                                   *)
  (*              while(peek(ps,es,"&")) { ... }                            *)
  (*              if(peek(ps,es,";")) { ... }  return cmd;                  *)
  (*                                                                       *)
  (* All three guards are peeks for a symbol byte, so all three are 0 by    *)
  (* ushp_peek_res_sym and neither [pipecmd], [backcmd] nor [listcmd] is    *)
  (* ever fetched -- which is exactly what the catalog's [skipfunc] lines   *)
  (* claimed and this is where the claim becomes a theorem.  Both frames    *)
  (* are k = 6, j = 6, no locals, and both are CONTIGUOUS, so §4c's two     *)
  (* lemmas take the whole prologue and the whole epilogue.                 *)
  (* ===================================================================== *)

  Lemma wp_kshp_parsepipe (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps s0 : Z) (len off : nat) (f : nat -> bv 8) (w0 : mword 64)
      (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    ushp_tokens len f off toks ->
    (length toks < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + nn))) -∗
    (∀ p : Z,
       ⌜ p + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 p toks -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + nn))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy Hrun Hcont".
    rewrite shpp_parsepipe.
    assert (Elen0 : (len + ushp_skipws (len - len) len f)%nat = len)
      by (rewrite Nat.sub_diag; cbn [ushp_skipws]; lia).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x682..0x690  the prologue ---- *)
    iApply (wp_kshp_frame_pro 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] 0x682
              (fun i : nat => match i with
                              | 0%nat => 0x684 | 1%nat => 0x686
                              | 2%nat => 0x688 | 3%nat => 0x68a
                              | 4%nat => 0x68c | 5%nat => 0x68e
                              | _ => 0x690 end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (16 + (24 + nn)) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_682 with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_684 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_686 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_688 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68e with "Hcode") | done ]. }
    { iApply (uis_shp_690 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (mA := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (HmA : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    mA !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (HspA : mA !!! Regidx csp_rs1 = spn).
    { rewrite (HmA csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x692  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 mA (mword_of_int 0x692) s2_idx a0_idx
              (mword_of_int ps) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_692 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> mA).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m2 !!! Regidx q = mA !!! Regidx q)
      by (intros q Hq; exact (upd_ne mA (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x694  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h2 m2 (mword_of_int 0x694) s4_idx a0_idx
              (mword_of_int ps) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_694 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x696  c.mv s1,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m3 (mword_of_int 0x696) s1_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (HmA a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_696 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x698  jal 590 <parseexec> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h4 m4 (mword_of_int 0x698)
              (mword_of_int 2096888 : mword 21) ra_idx
              (mword_of_int 0x590) (mword_of_int 0x69c) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_698 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x69c : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret5 : ret_pc (m5 !!! Regidx ra_idx) = mword_of_int 0x69c).
    { rewrite (upd_eq m4 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x69c : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (HmA a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_5 : m5 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate))
              (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (HmA a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    rewrite <- shpp_parseexec.
    iApply (wp_kshp_parseexec h5 m5 dq dw dv ps s0 len off f w0 toks nn
              Ha0_5 Ha1_5 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy Hrun").
    iIntros (p) "%Hpsz Hnode Hcur Hstr Hws Hsy".
    iIntros (h6 m6) "%Hcs56 %Ha0_6 Hrun".
    rewrite Eret5.
    (* ---- 0x69c  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 m6 (mword_of_int 0x69c) s3_idx a0_idx
              (mword_of_int p) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_69c with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x69e/0x6a2  the pipe table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h7 m7 (mword_of_int 0x69e)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x169e) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_69e with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0x169e : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_8 : m8 !!! Regidx a2_idx = mword_of_int 0x169e)
      by exact (upd_eq m7 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x169e : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h8 m8 (mword_of_int 0x6a2)
              (mword_of_int 3202 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_pipe) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_8; unfold ushp_T_pipe;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6a2 with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_pipe : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x6a6/0x6a8  peek's two other arguments ---- *)
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate))
              (Hm8 s1_idx ltac:(vm_compute; discriminate))
              (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hcs56 s1_idx ltac:(vm_compute; reflexivity))
              (Hm5 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hcs56 s2_idx ltac:(vm_compute; reflexivity))
              (Hm5 s2_idx ltac:(vm_compute; discriminate))
              (Hm4 s2_idx ltac:(vm_compute; discriminate))
              (Hm3 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s2_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h9 m9 (mword_of_int 0x6a6) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6a6 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv γt γd γs γfd h10 m10 (mword_of_int 0x6a8) a0_idx
              s2_idx (mword_of_int ps) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6a8 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x6aa  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h11 m11 (mword_of_int 0x6aa)
              (mword_of_int 2096542 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x6ae) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6aa with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x6ae : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x6ae).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x6ae : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_12 : m12 !!! Regidx a2_idx = mword_of_int ushp_T_pipe).
    { rewrite (Hm12 a2_idx ltac:(vm_compute; discriminate))
              (Hm11 a2_idx ltac:(vm_compute; discriminate))
              (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_pipe : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h12 m12 dq dw true DfracDiscarded ps s0
              ushp_T_pipe len len 1 f (ushp_lit ushp_T_pipe)
              (mword_of_int (s0 + Z.of_nat len)) (30 + nn)
              Ha0_12 Ha1_12 Ha2_12 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_pipe; lia)
              ltac:(unfold ushp_T_pipe, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_pipe 1 DfracDiscarded
                ushp_T_pipe_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h13 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12 Elen0.
    rewrite (ushp_peek_res_sym len f (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_pipe Hnosym ushp_T_pipe_sym) in Ha0_13.
    (* ---- 0x6ae  c.bnez a0 -- NOT taken: there is no pipe ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h13 m13 (mword_of_int 0x6ae)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x6c2) (16 + (24 + nn))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_6ae with "Hcode"). }
    iIntros (h14) "Hrun".
    (* ---- 0x6b0  c.mv a0,s3 ---- *)
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m6 (Regidx s3_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h14 m13 (mword_of_int 0x6b0) a0_idx
              s3_idx (mword_of_int p) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_13; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_6b0 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m13).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* the whole body, as one preservation fact *)
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3 Hq4.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm7 q Hq3) (Hcs56 q Hq)
              (Hm5 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q Hq1) (Hm3 q Hq4) (Hm2 q Hq2) (HmA q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs56 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact HspA. }
    (* ---- 0x6b2..0x6c0  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x6b2 | 1%nat => 0x6b4
                              | 2%nat => 0x6b6 | 3%nat => 0x6b8
                              | 4%nat => 0x6ba | 5%nat => 0x6bc
                              | _ => 0x6be end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 6)) vals
              (16 + (24 + nn)) h15 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    vm_compute; discriminate)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_6b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6bc with "Hcode") | done ]. }
    { iApply (uis_shp_6be with "Hcode"). }
    { iApply (uis_shp_6c0 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! p with "[] Hnode Hcur Hstr Hws Hsy [] [] Hrun").
    - iPureIntro. exact Hpsz.
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6) eq_refl)
                 (Hmiss 5%nat s4_idx (mword_of_int 0 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m13 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ---- parseline, the same shape with TWO refuted guards -------------- *)
  Lemma wp_kshp_parseline (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps s0 : Z) (len off : nat) (f : nat -> bv 8) (w0 : mword 64)
      (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    ushp_tokens len f off toks ->
    (length toks < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parseline)
      (6 + (6 + (16 + (24 + nn)))) -∗
    (∀ p : Z,
       ⌜ p + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 p toks -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (6 + (16 + (24 + nn)))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy Hrun Hcont".
    rewrite shpp_parseline.
    assert (Elen0 : (len + ushp_skipws (len - len) len f)%nat = len)
      by (rewrite Nat.sub_diag; cbn [ushp_skipws]; lia).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x6e2..0x6f0  the prologue ---- *)
    iApply (wp_kshp_frame_pro 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] 0x6e2
              (fun i : nat => match i with
                              | 0%nat => 0x6e4 | 1%nat => 0x6e6
                              | 2%nat => 0x6e8 | 3%nat => 0x6ea
                              | 4%nat => 0x6ec | 5%nat => 0x6ee
                              | _ => 0x6f0 end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (6 + (16 + (24 + nn))) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_6e2 with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_6e4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6e6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6e8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ea with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ec with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ee with "Hcode") | done ]. }
    { iApply (uis_shp_6f0 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (mA := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (HmA : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    mA !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (HspA : mA !!! Regidx csp_rs1 = spn).
    { rewrite (HmA csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x6f2  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 mA (mword_of_int 0x6f2) s2_idx a0_idx
              (mword_of_int ps) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6f2 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> mA).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m2 !!! Regidx q = mA !!! Regidx q)
      by (intros q Hq; exact (upd_ne mA (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x6f4  c.mv s3,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h2 m2 (mword_of_int 0x6f4) s3_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (HmA a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6f4 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx s3_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x6f6  jal 682 <parsepipe> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h3 m3 (mword_of_int 0x6f6)
              (mword_of_int 2097036 : mword 21) ra_idx
              (mword_of_int 0x682) (mword_of_int 0x6fa)
              (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6f6 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6fa : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret4 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x6fa).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x6fa : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (HmA a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_4 : m4 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (HmA a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    rewrite <- shpp_parsepipe.
    iApply (wp_kshp_parsepipe h4 m4 dq dw dv ps s0 len off f w0 toks nn
              Ha0_4 Ha1_4 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy Hrun").
    iIntros (p) "%Hpsz Hnode Hcur Hstr Hws Hsy".
    iIntros (h5 m5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    (* ---- 0x6fa  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h5 m5 (mword_of_int 0x6fa) s1_idx a0_idx
              (mword_of_int p) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_6fa with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x6fc/0x700  the ampersand table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h6 m6 (mword_of_int 0x6fc)
              (mword_of_int 1 : mword 20) s4_idx
              (mword_of_int 0x16fc) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6fc with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 0x16fc : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s4_idx) (Regidx q) _ Hq)).
    assert (Hs4_7 : m7 !!! Regidx s4_idx = mword_of_int 0x16fc)
      by exact (upd_eq m6 (Regidx s4_idx)
                  (regval_into_reg (mword_of_int 0x16fc : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h7 m7 (mword_of_int 0x700)
              (mword_of_int 3116 : mword 12) s4_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_7; unfold ushp_T_back;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_700 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx s4_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_back : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s4_idx) (Regidx q) _ Hq)).
    assert (Hs4_8 : m8 !!! Regidx s4_idx = mword_of_int ushp_T_back)
      by exact (upd_eq m7 (Regidx s4_idx)
                  (regval_into_reg (mword_of_int ushp_T_back : mword 64))).
    (* the two values the guards read, once *)
    assert (Hs2_8 : m8 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate))
              (Hcs45 s2_idx ltac:(vm_compute; reflexivity))
              (Hm4 s2_idx ltac:(vm_compute; discriminate))
              (Hm3 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s2_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs3_8 : m8 !!! Regidx s3_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hcs45 s3_idx ltac:(vm_compute; reflexivity))
              (Hm4 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s3_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    (* ---- 0x704  c.j 0x71a -- into the backgrounding loop's GUARD ---- *)
    iApply (wp_uk_cj γt γd γs γfd h8 m8 (mword_of_int 0x704)
              (mword_of_int 11 : mword 11) (mword_of_int 0x71a)
              (6 + (16 + (24 + nn)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_704 with "Hcode"). }
    iIntros (h9) "Hrun".
    (* ---- 0x71a..0x71e  peek's three arguments ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h9 m8 (mword_of_int 0x71a) a2_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_8; symmetry;
                    exact (ushp_mv_val ushp_T_back))
              with "[] Hrun").
    { iApply (uis_shp_71a with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_back : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a2_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv γt γd γs γfd h10 m9 (mword_of_int 0x71c) a1_idx s3_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm9 s3_idx ltac:(vm_compute; discriminate))
                      Hs3_8; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_71c with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv γt γd γs γfd h11 m10 (mword_of_int 0x71e) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      (Hm9 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_8; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_71e with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x720  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h12 m11 (mword_of_int 0x720)
              (mword_of_int 2096424 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x724)
              (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_720 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x724 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x724).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x724 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_12 : m12 !!! Regidx a2_idx = mword_of_int ushp_T_back).
    { rewrite (Hm12 a2_idx ltac:(vm_compute; discriminate))
              (Hm11 a2_idx ltac:(vm_compute; discriminate))
              (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_back : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h13 m12 dq dw true DfracDiscarded ps s0
              ushp_T_back len len 1 f (ushp_lit ushp_T_back)
              (mword_of_int (s0 + Z.of_nat len)) (36 + nn)
              Ha0_12 Ha1_12 Ha2_12 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_back; lia)
              ltac:(unfold ushp_T_back, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_back 1 DfracDiscarded
                ushp_T_back_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h14 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12 Elen0.
    rewrite (ushp_peek_res_sym len f (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_back Hnosym ushp_T_back_sym) in Ha0_13.
    (* ---- 0x724  c.bnez a0 -- NOT taken: nothing is backgrounded ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h14 m13 (mword_of_int 0x724)
              (mword_of_int 241 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x706) (6 + (16 + (24 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_724 with "Hcode"). }
    iIntros (h15) "Hrun".
    (* ---- 0x726/0x72a  the semicolon table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h15 m13 (mword_of_int 0x726)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x1726) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_726 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m14 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 0x1726 : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_14 : m14 !!! Regidx a2_idx = mword_of_int 0x1726)
      by exact (upd_eq m13 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x1726 : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h16 m14 (mword_of_int 0x72a)
              (mword_of_int 3082 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_list) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_14; unfold ushp_T_list;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_72a with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m15 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_list : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x72e/0x730  the other two arguments again ---- *)
    assert (Hs3_15 : m15 !!! Regidx s3_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm15 s3_idx ltac:(vm_compute; discriminate))
              (Hm14 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_8. }
    assert (Hs2_15 : m15 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm15 s2_idx ltac:(vm_compute; discriminate))
              (Hm14 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s2_idx ltac:(vm_compute; reflexivity))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_8. }
    iApply (wp_uk_cmv γt γd γs γfd h17 m15 (mword_of_int 0x72e) a1_idx
              s3_idx (mword_of_int (s0 + Z.of_nat len))
              (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_15; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_72e with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m16 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv γt γd γs γfd h18 m16 (mword_of_int 0x730) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm16 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_15; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_730 with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m17 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m16).
    assert (Hm17 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m17 !!! Regidx q = m16 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m16 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x732  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h19 m17 (mword_of_int 0x732)
              (mword_of_int 2096406 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x736)
              (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_732 with "Hcode"). }
    iIntros (h20) "Hrun".
    set (m18 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x736 : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret18 : ret_pc (m18 !!! Regidx ra_idx) = mword_of_int 0x736).
    { rewrite (upd_eq m17 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x736 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_18 : m18 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm18 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m16 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_18 : m18 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm18 a1_idx ltac:(vm_compute; discriminate))
              (Hm17 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m15 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_18 : m18 !!! Regidx a2_idx = mword_of_int ushp_T_list).
    { rewrite (Hm18 a2_idx ltac:(vm_compute; discriminate))
              (Hm17 a2_idx ltac:(vm_compute; discriminate))
              (Hm16 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m14 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_list : mword 64))). }
    iApply (wp_kshp_peek h20 m18 dq dw true DfracDiscarded ps s0
              ushp_T_list len len 1 f (ushp_lit ushp_T_list)
              (mword_of_int (s0 + Z.of_nat len)) (36 + nn)
              Ha0_18 Ha1_18 Ha2_18 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_list; lia)
              ltac:(unfold ushp_T_list, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_list 1 DfracDiscarded
                ushp_T_list_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h21 m19) "%Hcs1819 %Ha0_19 Hrun".
    rewrite Eret18 Elen0.
    rewrite (ushp_peek_res_sym len f (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_list Hnosym ushp_T_list_sym) in Ha0_19.
    (* ---- 0x736  c.bnez a0 -- NOT taken: there is no list ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h21 m19 (mword_of_int 0x736)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x74a) (6 + (16 + (24 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_19; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_736 with "Hcode"). }
    iIntros (h22) "Hrun".
    (* ---- 0x738  c.mv a0,s1 ---- *)
    assert (Hs1_19 : m19 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcs1819 s1_idx ltac:(vm_compute; reflexivity))
              (Hm18 s1_idx ltac:(vm_compute; discriminate))
              (Hm17 s1_idx ltac:(vm_compute; discriminate))
              (Hm16 s1_idx ltac:(vm_compute; discriminate))
              (Hm15 s1_idx ltac:(vm_compute; discriminate))
              (Hm14 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate))
              (Hm9 s1_idx ltac:(vm_compute; discriminate))
              (Hm8 s1_idx ltac:(vm_compute; discriminate))
              (Hm7 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s1_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h22 m19 (mword_of_int 0x738) a0_idx
              s1_idx (mword_of_int p) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_19; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_738 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m19).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m19 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m19 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3 Hq4.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1819 q Hq)
              (Hm18 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm17 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm16 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q Hq4) (Hm7 q Hq4) (Hm6 q Hq1) (Hcs45 q Hq)
              (Hm4 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm3 q Hq3) (Hm2 q Hq2) (HmA q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1819 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm18 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm17 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm16 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact HspA. }
    (* ---- 0x73a..0x748  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x73a | 1%nat => 0x73c
                              | 2%nat => 0x73e | 3%nat => 0x740
                              | 4%nat => 0x742 | 5%nat => 0x744
                              | _ => 0x746 end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 6)) vals
              (6 + (16 + (24 + nn))) h23 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    vm_compute; discriminate)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_73a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_73c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_73e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_740 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_742 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_744 with "Hcode") | done ]. }
    { iApply (uis_shp_746 with "Hcode"). }
    { iApply (uis_shp_748 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! p with "[] Hnode Hcur Hstr Hws Hsy [] [] Hrun").
    - iPureIntro. exact Hpsz.
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6) eq_refl)
                 (Hmiss 5%nat s4_idx (mword_of_int 0 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m19 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* §13 nulterminate @0x7ee -- the jump table, and the ONE leaf this file  *)
  (*     could not build.                                                   *)
  (*                                                                       *)
  (*   struct cmd *nulterminate(struct cmd *cmd) {                          *)
  (*     if(cmd == 0) return 0;                                             *)
  (*     switch(cmd->type) {                                                *)
  (*     case EXEC: for(i = 0; ecmd->argv[i]; i++) *ecmd->eargv[i] = 0;      *)
  (*     ... }                                                              *)
  (*     return cmd; }                                                      *)
  (*                                                                       *)
  (* THIS IS WHERE THE TOKEN BOUNDARIES BECOME C STRINGS.  parseexec left   *)
  (* argv[i] and eargv[i] as two pointers INTO THE LINE; nulterminate       *)
  (* writes a NUL at every eargv[i], and after it the bytes from argv[i]    *)
  (* are the NUL-terminated argument [exec] observes.  The walk says        *)
  (* exactly that and no more: the node is unchanged and the line comes     *)
  (* back as [ushp_nulfold toks], the original bytes with a zero at each    *)
  (* token's END INDEX.                                                     *)
  (*                                                                       *)
  (* THE ONE HYPOTHESIS THIS FUNCTION FORCES.  The switch is a genuine      *)
  (* computed transfer through a table in .rodata, and .rodata is the TEXT  *)
  (* half, so the [c.lw a5,0(a5)] at 0x814 is a FOUR-BYTE LOAD OUT OF THE   *)
  (* TEXT HALF.  [UkRunMem.wp_uk_lbu_text] is one byte and                  *)
  (* [UkRunMem.wp_uk_clw] takes [ubytes γd].  The leaf EXISTS -- it is      *)
  (* [UkShRun.wp_uk_clw_text], built for runcmd's own jump table -- but it  *)
  (* is [Local] to that file, so this walk cannot name it.                  *)
  (* [ushp_clw_text_ok] below is its statement, VERBATIM, and the discharge *)
  (* is one [exact] the moment relocation ask 3 lands it in [UkRunMem.v].   *)
  (* Round 3 recorded this leaf as a BASE-encoding [lw]; the catalog says   *)
  (* [c.lw], so the ask is the compressed one and it is already written.    *)
  (* ===================================================================== *)

  Hypothesis ushp_clw_text_ok :
    forall (h : CpuId) (m : regfile) (pc : mword 64)
           (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (a : Z)
           (wv : mword 32) (avail : nat),
      unot_sp rd ->
      creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
      creg2reg_idx (Cregidx crd) = Regidx rd ->
      a = uint (m !!! Regidx rs1) + uoff_c4 uimm ->
      a mod 4 = 0 ->
      uint rd <> 0 ->
      uinstr_is γt pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) -∗
      ([∗ list] j ∈ seq 0 4, utext γt (a + Z.of_nat j) (nth_byte wv j)) -∗
      urun γt γd γs γfd h m pc avail -∗
      (∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx rd := regval_into_reg (sign_extend' 64 wv)]> m)
           (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).

  (* ---- the line, and what the loop does to it ------------------------- *)
  Definition ushp_setb (g : nat -> bv 8) (j : nat) (b : bv 8) : nat -> bv 8 :=
    fun i => if Nat.eqb i j then b else g i.

  Fixpoint ushp_nulfold (toks : list (nat * nat)) (g : nat -> bv 8)
    : nat -> bv 8 :=
    match toks with
    | [] => g
    | tk :: r => ushp_nulfold r (ushp_setb g (snd tk) ubyte0)
    end.

  Local Lemma ushp_bytes_upd (a : Z) (n : nat) (g : nat -> bv 8) (j : nat)
      (b : bv 8) :
    (j < n)%nat ->
    ubytes γd a n g -∗
    ubyte γd (a + Z.of_nat j) (g j) ∗
    (ubyte γd (a + Z.of_nat j) b -∗ ubytes γd a n (ushp_setb g j b)).
  Proof.
    intro Hj. iIntros "H".
    assert (Hjs : seq 0 n !! j = Some j) by (apply lookup_seq; lia).
    rewrite /ubytes /ubytesq.
    rewrite (big_sepL_delete
               (fun _ i : nat => ubyteq γd (DfracOwn 1) (a + Z.of_nat i) (g i))
               (seq 0 n) j j Hjs).
    iDestruct "H" as "[Hj Hrest]". iFrame "Hj". iIntros "Hj".
    rewrite (big_sepL_delete
               (fun _ i : nat =>
                  ubyteq γd (DfracOwn 1) (a + Z.of_nat i)
                    (ushp_setb g j b i))
               (seq 0 n) j j Hjs).
    iSplitL "Hj".
    { assert (Ehit : ushp_setb g j b j = b)
        by (rewrite /ushp_setb Nat.eqb_refl; reflexivity).
      rewrite Ehit. iExact "Hj". }
    iApply (big_sepL_mono with "Hrest").
    intros k y Hy. apply lookup_seq in Hy as [ -> Hlt ].
    rewrite Nat.add_0_l.
    destruct (decide (k = j)) as [ Ek | Ek ]; [ done | ].
    assert (Ese : ushp_setb g j b k = g k)
      by (rewrite /ushp_setb (proj2 (Nat.eqb_neq k j) Ek); reflexivity).
    rewrite Ese. done.
  Qed.

  (* ---- reading one slot of a FINISHED node ---------------------------- *)
  Local Lemma ushp_slot_read (t0 base : Z) (toks : list (nat * nat))
      (sel : nat * nat -> nat) (i : nat) :
    (i < 10)%nat ->
    ([∗ list] j ∈ seq 0 10, ushp_slot t0 base toks sel j) -∗
    ushp_slot t0 base toks sel i ∗
    (ushp_slot t0 base toks sel i -∗
     [∗ list] j ∈ seq 0 10, ushp_slot t0 base toks sel j).
  Proof.
    intro Hi. iIntros "H".
    iApply (big_sepL_lookup_acc _ (seq 0 10) i i
              ltac:(apply lookup_seq; lia) with "H").
  Qed.

  (* ---- one byte of the read-only image, by its address ---------------- *)
  Local Lemma ushp_ro_byte (a : Z) (b : bv 8) :
    shp_ro !! a = Some b -> shp_rodata γt -∗ utext γt a b.
  Proof.
    intro Ha. iIntros "#H". rewrite /shp_rodata /utext_img.
    iApply (big_sepM_lookup _ _ a b with "H"). exact Ha.
  Qed.

  (* ...and the FOUR that make the EXEC arm's jump-table entry.  The entry
     is a signed displacement from the table's own base, so 0x13b0 plus it
     is 0x81a -- which is checked by [vm_compute] below, not asserted. *)
  Local Lemma ushp_jrow_exec :
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4,
      utext γt (0x13b4 + Z.of_nat j)
        (nth_byte (mword_of_int 4294964330 : mword 32) j).
  Proof.
    iIntros "#H". rewrite !big_sepL_cons big_sepL_nil.
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 0%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 0%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 1%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 1%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 2%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 2%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 3%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 3%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | done ].
  Qed.

  (* ---- the EXEC arm's loop, 0x822..0x82e ------------------------------ *)
  Local Lemma wp_kshp_nul_loop (s0 p : Z) (len : nat) (nn : nat) :
    forall (rest : list (nat * nat)) (done : list (nat * nat))
           (tk : nat * nat) (toks : list (nat * nat)) (g : nat -> bv 8)
           (h : CpuId) (mc : regfile),
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    toks = done ++ tk :: rest ->
    (length toks < 10)%nat ->
    (forall (i : nat) (t : nat * nat), toks !! i = Some t ->
       (fst t <= len)%nat /\ (snd t <= len)%nat) ->
    mc !!! Regidx a5_idx
      = mword_of_int (p + 16 + 8 * Z.of_nat (length done)) ->
    shp_code γt -∗
    ushp_exec_at s0 p toks -∗
    ubytes γd s0 (S len) g -∗
    urun γt γd γs γfd h mc (mword_of_int 0x822) nn -∗
    (ushp_exec_at s0 p toks -∗
     ubytes γd s0 (S len) (ushp_nulfold (tk :: rest) g) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x83e) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro rest.
    induction rest as [| tk' rest IH ];
      intros done tk toks g h mc Hs0 Hs64 Hp0 Hp8 Hpsz Htoksd Htlen Hsnd Ha5;
      iIntros "#Hcode Hnode Hline Hrun Hcont".
    all: assert (Hlk : toks !! (length done) = Some tk)
      by (rewrite Htoksd; exact (ushp_lookup_app_mid' done tk _)).
    all: assert (Ht2 : (S (length done) <= length toks)%nat);
      [ rewrite Htoksd ushp_len_app_cons; lia | ].
    all: assert (Hdlen : (S (length done) < 10)%nat) by lia.
    all: assert (Hsndtk : (snd tk <= len)%nat)
      by exact (proj2 (Hsnd _ _ Hlk)).
    all: iDestruct "Hnode" as "(%Hnl & %Hnp & %Hna & Hty & Hav & Hev)".
    (* ---- 0x822  c.ld a4,72(a5) -- eargv[i] ---- *)
    all: iDestruct (ushp_slot_read s0 (p + 88) toks snd (length done)
                      ltac:(lia) with "Hev") as "[Hslot Hevc]".
    all: assert (Eslot : ushp_slot s0 (p + 88) toks snd (length done)
                         = uword γd (p + 88 + 8 * Z.of_nat (length done))
                             (mword_of_int (s0 + Z.of_nat (snd tk))))
      by (rewrite /ushp_slot Hlk; reflexivity).
    all: rewrite Eslot.
    all: iApply (wp_uk_cld γt γd γs γfd h mc (mword_of_int 0x822)
                   (mword_of_int 9 : mword 5) (mword_of_int 7 : mword 3)
                   (mword_of_int 6 : mword 3) a5_idx a4_idx
                   (p + 88 + 8 * Z.of_nat (length done))
                   (mword_of_int (s0 + Z.of_nat (snd tk))) nn
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   ltac:(rewrite Ha5
                           (uint_moi (p + 16 + 8 * Z.of_nat (length done))
                              ltac:(unfold Z64 in *; lia));
                         vm_compute uoff_c8; lia)
                   ltac:(exact (ushp_slot_al8 p 11 (length done) Hp8))
                   ltac:(vm_compute; discriminate)
                   with "[] Hslot Hrun");
      [ iApply (uis_shp_822 with "Hcode") | ].
    all: iIntros "Hslot" (h1) "Hrun".
    all: iDestruct ("Hevc" with "Hslot") as "Hev".
    all: set (n1 := <[Regidx a4_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat (snd tk))
                            : mword 64)]> mc).
    all: assert (Hn1 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                   n1 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc (Regidx a4_idx) (Regidx q) _ Hq)).
    all: assert (Ha4_1 : n1 !!! Regidx a4_idx
                         = mword_of_int (s0 + Z.of_nat (snd tk)))
      by exact (upd_eq mc (Regidx a4_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat (snd tk)) : mword 64))).
    (* ---- 0x824  sb zero,0(a4) -- THE NUL ---- *)
    all: iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    all: iDestruct (ushp_bytes_upd s0 (S len) g (snd tk) ubyte0
                      ltac:(lia) with "Hline") as "[Hb Hbc]".
    all: iApply (wp_uk_sb γt γd γs γfd h1 n1 (mword_of_int 0x824)
                   (mword_of_int 0 : mword 12) a4_idx x0_idx
                   (s0 + Z.of_nat (snd tk)) (g (snd tk)) nn
                   ltac:(rewrite Ha4_1
                           (uint_moi (s0 + Z.of_nat (snd tk))
                              ltac:(unfold Z64 in *; lia));
                         vm_compute uoff_i12; lia)
                   with "[] Hb Hrun");
      [ iApply (uis_shp_824 with "Hcode") | ].
    all: iIntros "Hb" (h2) "Hrun".
    all: rewrite Hx0.
    all: assert (Enb : nth_byte (zero_reg : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    all: rewrite Enb.
    all: iDestruct ("Hbc" with "Hb") as "Hline".
    (* ---- 0x828  c.addi a5,a5,8 ---- *)
    all: assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6)
                         : mword 64) = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    all: iApply (wp_uk_caddi γt γd γs γfd h2 n1 (mword_of_int 0x828)
                   (mword_of_int 8 : mword 6) a5_idx
                   (mword_of_int (p + 16 + 8 * Z.of_nat (length done) + 8)) nn
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hn1 a5_idx ltac:(vm_compute; discriminate))
                           Ha5 Esx8; symmetry; apply moi_add)
                   with "[] Hrun");
      [ iApply (uis_shp_828 with "Hcode") | ].
    all: iIntros (h3) "Hrun".
    all: set (n2 := <[Regidx a5_idx
                      := regval_into_reg
                           (mword_of_int
                              (p + 16 + 8 * Z.of_nat (length done) + 8)
                            : mword 64)]> n1).
    all: assert (Hn2 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                   n2 !!! Regidx q = n1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n1 (Regidx a5_idx) (Regidx q) _ Hq)).
    all: assert (Ha5_2 : n2 !!! Regidx a5_idx
                         = mword_of_int
                             (p + 16 + 8 * Z.of_nat (length done) + 8))
      by exact (upd_eq n1 (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int (p + 16 + 8 * Z.of_nat (length done) + 8)
                      : mword 64))).
    all: iDestruct (ushp_slot_read s0 (p + 8) toks fst
                      (S (length done)) ltac:(lia) with "Hav")
           as "[Hnx Havc]".
    - (* ======= the LAST token: argv[i+1] is the NULL cap ============== *)
      assert (Ecap : toks !! S (length done) = None)
        by (rewrite Htoksd ushp_lookup_app_past; reflexivity).
      assert (Ecl : (S (length done) = length toks)%nat).
      { rewrite Htoksd ushp_len_app_cons. cbn [length]. lia. }
      assert (Eslotn : ushp_slot s0 (p + 8) toks fst (S (length done))
                       = uword γd (p + 8 + 8 * Z.of_nat (S (length done)))
                           (mword_of_int 0)).
      { rewrite /ushp_slot Ecap (bool_decide_eq_true_2 _ Ecl). reflexivity. }
      rewrite Eslotn.
      (* ---- 0x82a  ld a4,-8(a5) ---- *)
      iApply (wp_uk_ld γt γd γs γfd h3 n2 (mword_of_int 0x82a)
                (mword_of_int 4088 : mword 12) a5_idx a4_idx (DfracOwn 1)
                (p + 8 + 8 * Z.of_nat (S (length done)))
                (mword_of_int 0) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha5_2
                        (uint_moi (p + 16 + 8 * Z.of_nat (length done) + 8)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (S (length done)) Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_82a with "Hcode"). }
      iIntros "Hnx" (h4) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (n3 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> n2).
      assert (Hn3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                 n3 !!! Regidx q = n2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n2 (Regidx a4_idx) (Regidx q) _ Hq)).
      assert (Ha4_3 : n3 !!! Regidx a4_idx = (mword_of_int 0 : mword 64))
        by exact (upd_eq n2 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 0 : mword 64))).
      (* ---- 0x82e  c.bnez a4 -- NOT taken: the vector is capped ---- *)
      iApply (wp_uk_cbnez γt γd γs γfd h4 n3 (mword_of_int 0x82e)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3)
                a4_idx false (mword_of_int 0x822) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha4_3; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_82e with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x830  c.j 0x83e ---- *)
      iApply (wp_uk_cj γt γd γs γfd h5 n3 (mword_of_int 0x830)
                (mword_of_int 7 : mword 11) (mword_of_int 0x83e) nn
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_830 with "Hcode"). }
      iIntros (h6) "Hrun".
      iApply ("Hcont" with "[Hty Hav Hev] Hline [] Hrun").
      + rewrite /ushp_exec_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty"; [ iExact "Hty" | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
      + iPureIntro. intros r Hr.
        rewrite (Hn3 r (ushp_cs_ne r a4_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hn2 r (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hn1 r (ushp_cs_ne r a4_idx Hr
                          ltac:(vm_compute; reflexivity))).
        reflexivity.
    - (* ======= ANOTHER token: argv[i+1] points into the line ========== *)
      assert (Enx : toks !! S (length done) = Some tk')
        by (rewrite Htoksd; exact (ushp_lookup_app_next done tk tk' rest)).
      assert (Eslotn : ushp_slot s0 (p + 8) toks fst (S (length done))
                       = uword γd (p + 8 + 8 * Z.of_nat (S (length done)))
                           (mword_of_int (s0 + Z.of_nat (fst tk'))))
        by (rewrite /ushp_slot Enx; reflexivity).
      rewrite Eslotn.
      assert (Hfst' : (fst tk' <= len)%nat)
        by exact (proj1 (Hsnd _ _ Enx)).
      (* ---- 0x82a  ld a4,-8(a5) ---- *)
      iApply (wp_uk_ld γt γd γs γfd h3 n2 (mword_of_int 0x82a)
                (mword_of_int 4088 : mword 12) a5_idx a4_idx (DfracOwn 1)
                (p + 8 + 8 * Z.of_nat (S (length done)))
                (mword_of_int (s0 + Z.of_nat (fst tk'))) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha5_2
                        (uint_moi (p + 16 + 8 * Z.of_nat (length done) + 8)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (S (length done)) Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_82a with "Hcode"). }
      iIntros "Hnx" (h4) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (n3 := <[Regidx a4_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat (fst tk'))
                         : mword 64)]> n2).
      assert (Hn3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                 n3 !!! Regidx q = n2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n2 (Regidx a4_idx) (Regidx q) _ Hq)).
      assert (Ha4_3 : n3 !!! Regidx a4_idx
                      = mword_of_int (s0 + Z.of_nat (fst tk')))
        by exact (upd_eq n2 (Regidx a4_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat (fst tk'))
                        : mword 64))).
      (* ---- 0x82e  c.bnez a4 -- TAKEN: the line's address is not 0 ---- *)
      iApply (wp_uk_cbnez γt γd γs γfd h4 n3 (mword_of_int 0x82e)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3)
                a4_idx true (mword_of_int 0x822) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha4_3;
                      assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Ezr;
                      rewrite (moi_neq_vec (s0 + Z.of_nat (fst tk')) 0
                                 ltac:(unfold Z64 in *; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hnz : (s0 + Z.of_nat (fst tk') =? 0) = false)
                        by (apply Z.eqb_neq; lia);
                      rewrite Hnz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_82e with "Hcode"). }
      iIntros (h5) "Hrun".
      iApply (IH (done ++ [tk]) tk' toks (ushp_setb g (snd tk) ubyte0) h5 n3
                Hs0 Hs64 Hp0 Hp8 Hpsz
                ltac:(rewrite Htoksd; symmetry; apply ushp_app_cons)
                Htlen Hsnd
                ltac:(rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate))
                        Ha5_2 ushp_len_app1; f_equal;
                      rewrite Nat2Z.inj_succ; lia)
                with "Hcode [Hty Hav Hev] Hline Hrun").
      { rewrite /ushp_exec_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty"; [ iExact "Hty" | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
      iIntros "Hnode Hline" (hf mf) "%Hpres Hrun".
      iApply ("Hcont" with "Hnode Hline [] Hrun").
      iPureIntro. intros r Hr.
      rewrite (Hpres r Hr)
              (Hn3 r (ushp_cs_ne r a4_idx Hr ltac:(vm_compute; reflexivity)))
              (Hn2 r (ushp_cs_ne r a5_idx Hr ltac:(vm_compute; reflexivity)))
              (Hn1 r (ushp_cs_ne r a4_idx Hr ltac:(vm_compute; reflexivity))).
      reflexivity.
  Qed.


  (* ---- the common landing, 0x83e..0x848 -------------------------------- *)
  (* Both ways out of the switch -- the empty argument vector and the loop's
     exit -- arrive here, so the [c.mv a0,s1] and the epilogue are one
     lemma rather than two copies. *)
  Local Lemma wp_kshp_nul_fin (sp0 spl : mword 64) (vals : nat -> mword 64)
      (p : Z) (nn : nat) (h : CpuId) (me : regfile) :
    uint sp0 mod 8 = 0 -> 32 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 24 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)) ->
    me !!! Regidx s1_idx = mword_of_int p ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 1 -∗
    urun γt γd γs γfd h me (mword_of_int 0x83e) nn -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals
               (<[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> me)))
         (ret_pc (vals 0%nat)) (4 + nn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hal8 Hlo Hhi Hsplu Hsp Hs1.
    iIntros "#Hcode Hsl Hloc Hrun Hcont".
    iApply (wp_uk_cmv γt γd γs γfd h me (mword_of_int 0x83e) a0_idx s1_idx
              (mword_of_int p) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_83e with "Hcode"). }
    iIntros (h1) "Hrun".
    set (mz := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> me).
    assert (Hspz : mz !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne me (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp. }
    iApply (wp_kshp_frame_epi 4 1 [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] (mword_of_int 3 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x840 | 1%nat => 0x842
                              | 2%nat => 0x844 | _ => 0x846 end)
              (mword_of_int 2 : mword 6) sp0 spl vals nn h1 mz
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(cbn [length]; lia)
              Hspz
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| i ]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| i ]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(intros i r u Hi;
                    destruct i as [| [| i ]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    vm_compute; discriminate)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_840 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_842 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_844 with "Hcode") | done ]. }
    { iApply (uis_shp_846 with "Hcode"). }
    { iApply (uis_shp_848 with "Hcode"). }
    iIntros (hf) "Hrun". iApply ("Hcont" $! hf with "Hrun").
  Qed.

  (* ---- nulterminate, the whole function -------------------------------- *)
  (* TAINT: [ushp_clw_text_ok], and nothing else -- it allocates nothing. *)
  Lemma wp_kshp_nulterminate (h : CpuId) (m : regfile) (s0 p : Z) (len : nat)
      (g : nat -> bv 8) (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int p ->
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (length toks < 10)%nat ->
    (forall (i : nat) (t : nat * nat), toks !! i = Some t ->
       (fst t <= len)%nat /\ (snd t <= len)%nat) ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_exec_at s0 p toks -∗
    ubytes γd s0 (S len) g -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.nulterminate) (4 + nn) -∗
    (ushp_exec_at s0 p toks -∗
     ubytes γd s0 (S len) (ushp_nulfold toks g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hs0 Hs64 Hp0 Hp8 Hpsz Htlen Hsnd.
    iIntros "#Hcode #Hro Hnode Hline Hrun Hcont".
    rewrite shpp_nulterminate.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | _ => m !!! Regidx s1_idx end).
    (* ---- 0x7ee  c.addi sp,sp,-32 ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x7ee)
              (mword_of_int 32 : mword 6) 4 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7ee with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
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
    set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 24)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 1 [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    (* ---- 0x7f0..0x7f4  the three spills ---- *)
    iApply (wp_kshp_spill spn nn [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x7f0 | 1%nat => 0x7f2
                              | 2%nat => 0x7f4 | _ => 0x7f6 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| [| i ]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| i ]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_7f0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7f2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7f4 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x7f6  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_kshp_fp h2 m1 0x7f6 (mword_of_int 8 : mword 8) nn
              with "[] Hrun").
    { iApply (uis_shp_7f6 with "Hcode"). }
    iIntros (h3 v) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x7f8  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x7f8) s1_idx a0_idx
              (mword_of_int p) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_7f8 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Hs1_3 : m3 !!! Regidx s1_idx = mword_of_int p)
      by exact (upd_eq m2 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hsp3 : m3 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x7fa  c.beqz a0 -- NOT taken: the node is not null ---- *)
    iApply (wp_uk_cbeqz γt γd γs γfd h4 m3 (mword_of_int 0x7fa)
              (mword_of_int 34 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x83e) nn
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3;
                    assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ezr;
                    rewrite (moi_eq_vec p 0 ltac:(unfold Z64 in *; lia)
                               ltac:(unfold Z64; lia));
                    assert (Hnz : (p =? 0) = false)
                      by (apply Z.eqb_neq; lia);
                    rewrite Hnz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7fa with "Hcode"). }
    iIntros (h5) "Hrun".
    (* ---- the node's type word, read twice ---- *)
    iDestruct "Hnode" as "(%Hnl & %Hnp & %Hna & Hty & Hav & Hev)".
    iDestruct "Hty" as "[Hty4 Hpad]".
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    (* ---- 0x7fc  c.lw a4,0(a0) ---- *)
    iApply (wp_uk_clw γt γd γs γfd h5 m3 (mword_of_int 0x7fc)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx p
              (mword_of_int 1 : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c4; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_7fc with "Hcode"). }
    iIntros "Hty4" (h6) "Hrun".
    set (m4 := <[Regidx a4_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 32)
                       : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_4 : m4 !!! Regidx a4_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_eq m3 (Regidx a4_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x7fe  c.li a5,5 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h6 m4 (mword_of_int 0x7fe)
              (mword_of_int 5 : mword 6) a5_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7fe with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m5 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 5 : mword 6)
                       : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_5 : m5 !!! Regidx a5_idx = (mword_of_int 5 : mword 64)).
    { rewrite (upd_eq m4 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 5 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int 1 : mword 64)).
    { rewrite (Hm5 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_4. }
    (* ---- 0x800  bltu a5,a4 -- NOT taken: EXEC is in range ---- *)
    iApply (wp_uk_btype γt γd γs γfd h7 m5 (mword_of_int 0x800)
              (mword_of_int 62 : mword 13) a4_idx a5_idx BLTU false
              (mword_of_int 0x83e) nn
              ltac:(cbn [uv_btaken]; rewrite Ha5_5 Ha4_5;
                    rewrite (moi_lt_u 5 1 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia)); reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_800 with "Hcode"). }
    iIntros (h8) "Hrun".
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_3. }
    (* ---- 0x804  lwu a5,0(a0) ---- *)
    iApply (wp_uk_lwu γt γd γs γfd h8 m5 (mword_of_int 0x804)
              (mword_of_int 0 : mword 12) a0_idx a5_idx p
              (mword_of_int 1 : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_5 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_804 with "Hcode"). }
    iIntros "Hty4" (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (zero_extend' 64 (mword_of_int 1 : mword 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_eq m5 (Regidx a5_idx)
                 (regval_into_reg
                    (zero_extend' 64 (mword_of_int 1 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x808  c.slli a5,a5,0x2 ---- *)
    iApply (wp_uk_cslli γt γd γs γfd h9 m6 (mword_of_int 0x808)
              (mword_of_int 2 : mword 6) a5_idx (mword_of_int 4) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_6 (moi_shl 1 2 ltac:(lia)); f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_808 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 4 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_7 : m7 !!! Regidx a5_idx = (mword_of_int 4 : mword 64))
      by exact (upd_eq m6 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 4 : mword 64))).
    (* ---- 0x80a/0x80e  the jump table's base ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h10 m7 (mword_of_int 0x80a)
              (mword_of_int 1 : mword 20) a4_idx
              (mword_of_int 0x180a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_80a with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x180a : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int 0x180a)
      by exact (upd_eq m7 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x180a : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h11 m8 (mword_of_int 0x80e)
              (mword_of_int 2982 : mword 12) a4_idx a4_idx
              (mword_of_int 0x13b0) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_8; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_80e with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x13b0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = mword_of_int 0x13b0)
      by exact (upd_eq m8 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x13b0 : mword 64))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = (mword_of_int 4 : mword 64)).
    { rewrite (Hm9 a5_idx ltac:(vm_compute; discriminate))
              (Hm8 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0x812  c.add a5,a5,a4 -- the row's address ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h12 m9 (mword_of_int 0x812) a5_idx
              a4_idx (mword_of_int 0x13b4) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_9 Ha4_9; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_812 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x13b4 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_10 : m10 !!! Regidx a5_idx = mword_of_int 0x13b4)
      by exact (upd_eq m9 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 0x13b4 : mword 64))).
    (* ---- 0x814  c.lw a5,0(a5) -- THE TEXT-HALF LOAD (the Hypothesis) ---- *)
    iApply (ushp_clw_text_ok h13 m10 (mword_of_int 0x814)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx 0x13b4
              (mword_of_int 4294964330 : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_10;
                    rewrite (uint_moi 0x13b4 ltac:(unfold Z64; lia));
                    vm_compute uoff_c4; lia)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] [] Hrun").
    { iApply (uis_shp_814 with "Hcode"). }
    { iApply (ushp_jrow_exec with "Hro"). }
    iIntros (h14) "Hrun".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64
                          (mword_of_int 4294964330 : mword 32)
                        : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha4_11 : m11 !!! Regidx a4_idx = mword_of_int 0x13b0).
    { rewrite (Hm11 a4_idx ltac:(vm_compute; discriminate))
              (Hm10 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_9. }
    (* ---- 0x816  c.add a5,a5,a4 -- the arm's pc ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h14 m11 (mword_of_int 0x816) a5_idx
              a4_idx (mword_of_int 0x81a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_11
                      (upd_eq m10 (Regidx a5_idx)
                         (regval_into_reg
                            (sign_extend' 64
                               (mword_of_int 4294964330 : mword 32)
                             : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_816 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x81a : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a5_idx) (Regidx q) _ Hq)).
    (* ---- 0x818  c.jr a5 -- the switch ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h15 m12 (mword_of_int 0x818) a5_idx
              (mword_of_int 0x81a) nn
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m11 (Regidx a5_idx)
                               (regval_into_reg
                                  (mword_of_int 0x81a : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_818 with "Hcode"). }
    iIntros (h16) "Hrun".
    (* ---- 0x81a  c.ld a5,8(a0) -- argv[0] ---- *)
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate))
              (Hm11 a0_idx ltac:(vm_compute; discriminate))
              (Hm10 a0_idx ltac:(vm_compute; discriminate))
              (Hm9 a0_idx ltac:(vm_compute; discriminate))
              (Hm8 a0_idx ltac:(vm_compute; discriminate))
              (Hm7 a0_idx ltac:(vm_compute; discriminate))
              (Hm6 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_5. }
    assert (Hkeep12 : forall q : mword 5, ucallee_saved_idx q = true ->
              m12 !!! Regidx q = m3 !!! Regidx q).
    { intros q Hq.
      rewrite (Hm12 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm7 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm5 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity))).
      reflexivity. }
    iDestruct (ushp_slot_read s0 (p + 8) toks fst 0%nat ltac:(lia)
                 with "Hav") as "[Hnx Havc]".
    destruct toks as [| tk rest ].
    - (* ======= NO ARGUMENTS: argv[0] is the cap ======================= *)
      assert (Eslot0 : ushp_slot s0 (p + 8) [] fst 0%nat
                       = uword γd (p + 8 + 8 * Z.of_nat 0)
                           (mword_of_int 0))
        by reflexivity.
      rewrite Eslot0.
      iApply (wp_uk_cld γt γd γs γfd h16 m12 (mword_of_int 0x81a)
                (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 7 : mword 3) a0_idx a5_idx
                (p + 8 + 8 * Z.of_nat 0) (mword_of_int 0) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_12
                        (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(exact (ushp_slot_al8 p 1 0%nat Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_81a with "Hcode"). }
      iIntros "Hnx" (h17) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (m13 := <[Regidx a5_idx
                    := regval_into_reg (mword_of_int 0 : mword 64)]> m12).
      assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                       m13 !!! Regidx q = m12 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m12 (Regidx a5_idx) (Regidx q) _ Hq)).
      assert (Ha5_13 : m13 !!! Regidx a5_idx = (mword_of_int 0 : mword 64))
        by exact (upd_eq m12 (Regidx a5_idx)
                    (regval_into_reg (mword_of_int 0 : mword 64))).
      (* ---- 0x81c  c.beqz a5 -- TAKEN: nothing to nul-terminate ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h17 m13 (mword_of_int 0x81c)
                (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0x83e) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha5_13; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_81c with "Hcode"). }
      iIntros (h18) "Hrun".
      iApply (wp_kshp_nul_fin sp0 spl vals p nn h18 m13
                Hal8 Hlo ltac:(lia) Hsplu
                ltac:(rewrite (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hkeep12 csp_rs1 ltac:(vm_compute; reflexivity));
                      exact Hsp3)
                ltac:(rewrite (Hm13 s1_idx ltac:(vm_compute; discriminate))
                        (Hkeep12 s1_idx ltac:(vm_compute; reflexivity));
                      exact Hs1_3)
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with "[Hty4 Hpad Hav Hev] Hline [] [] Hrun").
      + rewrite /ushp_exec_at /ushp_type_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                 iExact "Hpad" ] | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
      + iPureIntro.
        apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals m
                 (<[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> m13)
                 sp0 eq_refl).
        * intros i r u Hi.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate;
            injection Hi as Hr Hu0; subst; reflexivity.
        * intros q Hq Hqsp Hmiss.
          rewrite (upd_ne m13 (Regidx a0_idx) (Regidx q) _
                     (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
                  (Hm13 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hkeep12 q Hq)
                  (Hm3 q (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6)
                            eq_refl))
                  (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6)
                            eq_refl))
                  (Hm1 q Hqsp).
          reflexivity.
      + iPureIntro.
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        apply ushp_spillback_eq.
        * intros _.
          exact (upd_eq m13 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))).
        * intros i r u Hi He.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate;
            injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
    - (* ======= AT LEAST ONE ARGUMENT: into the loop =================== *)
      assert (Eslot0 : ushp_slot s0 (p + 8) (tk :: rest) fst 0%nat
                       = uword γd (p + 8 + 8 * Z.of_nat 0)
                           (mword_of_int (s0 + Z.of_nat (fst tk))))
        by reflexivity.
      rewrite Eslot0.
      assert (Hfst0 : (fst tk <= len)%nat)
        by exact (proj1 (Hsnd 0%nat tk eq_refl)).
      iApply (wp_uk_cld γt γd γs γfd h16 m12 (mword_of_int 0x81a)
                (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 7 : mword 3) a0_idx a5_idx
                (p + 8 + 8 * Z.of_nat 0)
                (mword_of_int (s0 + Z.of_nat (fst tk))) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_12
                        (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(exact (ushp_slot_al8 p 1 0%nat Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_81a with "Hcode"). }
      iIntros "Hnx" (h17) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (m13 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat (fst tk))
                          : mword 64)]> m12).
      assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                       m13 !!! Regidx q = m12 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m12 (Regidx a5_idx) (Regidx q) _ Hq)).
      assert (Ha5_13 : m13 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat (fst tk)))
        by exact (upd_eq m12 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat (fst tk)) : mword 64))).
      (* ---- 0x81c  c.beqz a5 -- NOT taken ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h17 m13 (mword_of_int 0x81c)
                (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx false (mword_of_int 0x83e) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha5_13;
                      assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Ezr;
                      rewrite (moi_eq_vec (s0 + Z.of_nat (fst tk)) 0
                                 ltac:(unfold Z64 in *; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hnz : (s0 + Z.of_nat (fst tk) =? 0) = false)
                        by (apply Z.eqb_neq; lia);
                      rewrite Hnz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_81c with "Hcode"). }
      iIntros (h18) "Hrun".
      (* ---- 0x81e  addi a5,a0,16 ---- *)
      assert (Ha0_13 : m13 !!! Regidx a0_idx = mword_of_int p).
      { rewrite (Hm13 a0_idx ltac:(vm_compute; discriminate)).
        exact Ha0_12. }
      iApply (wp_uk_addi γt γd γs γfd h18 m13 (mword_of_int 0x81e)
                (mword_of_int 16 : mword 12) a0_idx a5_idx
                (mword_of_int (p + 16)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_13;
                      assert (Ei : (sign_extend' 64
                                      (mword_of_int 16 : mword 12)
                                    : mword 64) = mword_of_int 16)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Ei; symmetry; apply moi_add)
                with "[] Hrun").
      { iApply (uis_shp_81e with "Hcode"). }
      iIntros (h19) "Hrun".
      set (m14 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (p + 16) : mword 64)]> m13).
      assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                       m14 !!! Regidx q = m13 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m13 (Regidx a5_idx) (Regidx q) _ Hq)).
      iApply (wp_kshp_nul_loop s0 p len nn rest (@nil (nat * nat)) tk
                (tk :: rest) g h19 m14
                Hs0 Hs64 Hp0 Hp8 Hpsz eq_refl Htlen Hsnd
                ltac:(assert (Ep16 : p + 16
                                     + 8 * Z.of_nat
                                             (length (@nil (nat * nat)))
                                     = p + 16)
                        by (cbn [length]; lia);
                      rewrite Ep16;
                      exact (upd_eq m13 (Regidx a5_idx)
                               (regval_into_reg
                                  (mword_of_int (p + 16) : mword 64))))
                with "Hcode [Hty4 Hpad Hav Hev] Hline Hrun").
      { rewrite /ushp_exec_at /ushp_type_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                 iExact "Hpad" ] | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
      iIntros "Hnode Hline" (h20 mf) "%Hpresf Hrun".
      iApply (wp_kshp_nul_fin sp0 spl vals p nn h20 mf
                Hal8 Hlo ltac:(lia) Hsplu
                ltac:(rewrite (Hpresf csp_rs1
                                 ltac:(vm_compute; reflexivity))
                        (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hkeep12 csp_rs1 ltac:(vm_compute; reflexivity));
                      exact Hsp3)
                ltac:(rewrite (Hpresf s1_idx
                                 ltac:(vm_compute; reflexivity))
                        (Hm14 s1_idx ltac:(vm_compute; discriminate))
                        (Hm13 s1_idx ltac:(vm_compute; discriminate))
                        (Hkeep12 s1_idx ltac:(vm_compute; reflexivity));
                      exact Hs1_3)
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with "Hnode Hline [] [] Hrun").
      + iPureIntro.
        apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals m
                 (<[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> mf)
                 sp0 eq_refl).
        * intros i r u Hi.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate;
            injection Hi as Hr Hu0; subst; reflexivity.
        * intros q Hq Hqsp Hmiss.
          rewrite (upd_ne mf (Regidx a0_idx) (Regidx q) _
                     (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
                  (Hpresf q Hq)
                  (Hm14 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hm13 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hkeep12 q Hq)
                  (Hm3 q (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6)
                            eq_refl))
                  (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6)
                            eq_refl))
                  (Hm1 q Hqsp).
          reflexivity.
      + iPureIntro.
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        apply ushp_spillback_eq.
        * intros _.
          exact (upd_eq mf (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))).
        * intros i r u Hi He.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate;
            injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* §14 parsecmd @0x86e -- the parser's front door, and the THEOREM.       *)
  (*                                                                       *)
  (*   struct cmd *parsecmd(char *s) {                                      *)
  (*     es = s + strlen(s);                                                *)
  (*     cmd = parseline(&s, es);                                           *)
  (*     peek(&s, es, "");                                                  *)
  (*     if(s != es) { fprintf(2, "leftovers: %s\n", s); panic("syntax"); }  *)
  (*     nulterminate(cmd);                                                 *)
  (*     return cmd; }                                                      *)
  (*                                                                       *)
  (* THE LEFTOVERS ARM IS REFUTED, which is the last of the five.  parseexec *)
  (* leaves the cursor at the end of the line -- its loop exits exactly when *)
  (* gettoken runs out -- and neither parsepipe nor parseline moves it       *)
  (* further, so [s == es] and the [fprintf]/[panic] pair is never fetched.  *)
  (* That is why the diagnostic subtree does not appear in this file at all. *)
  (*                                                                       *)
  (* THE CURSOR IS parsecmd's OWN LOCAL.  [&s] is a stack slot of this       *)
  (* frame, so the [uword] every function below has been threading is a      *)
  (* word of the frame the prologue just cut -- which is why the walk needs  *)
  (* the frame pointer's VALUE (it is [sp0]) and not the [∀ v] that          *)
  (* [wp_kshp_fp] hands out.                                                *)
  (* ===================================================================== *)

  (* the line as a byte run: [len] body bytes and the terminator *)
  Definition ushp_ext (len : nat) (f : nat -> bv 8) : nat -> bv 8 :=
    fun j => if bool_decide (j < len)%nat then f j else ubyte0.

  Local Lemma ushp_ustr_bytes (a : Z) (len : nat) (f : nat -> bv 8) :
    ustr γd (DfracOwn 1) a len f -∗ ubytes γd a (S len) (ushp_ext len f).
  Proof.
    iIntros "(_ & _ & Hbs & Hnul)".
    assert (ES : S len = (len + 1)%nat) by lia.
    rewrite ES (ubytes_app γd a len 1 (ushp_ext len f)).
    iSplitL "Hbs".
    - iApply (ushp_ubytes_ext a len f (ushp_ext len f) with "Hbs").
      intros j Hj. rewrite /ushp_ext (bool_decide_eq_true_2 _ Hj).
      reflexivity.
    - rewrite /ubytes /ubytesq. cbn [seq].
      rewrite big_sepL_cons big_sepL_nil.
      iSplitL; [ | done ].
      assert (Ez : a + Z.of_nat len + Z.of_nat 0 = a + Z.of_nat len) by lia.
      rewrite Ez.
      assert (Eh : ushp_ext len f (len + 0)%nat = ubyte0).
      { rewrite /ushp_ext
          (bool_decide_eq_false_2 (len + 0 < len)%nat ltac:(lia)).
        reflexivity. }
      rewrite Eh. iExact "Hnul".
  Qed.

  (* ---- parsecmd, the whole function ------------------------------------ *)
  (* TAINT: [ushp_malloc_ok] (through execcmd) and [ushp_clw_text_ok]
     (through nulterminate).  Nothing else. *)
  Lemma wp_kshp_parsecmd (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0%nat toks ->
    (length toks < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parsecmd)
      (8 + (6 + (6 + (16 + (24 + nn))))) -∗
    (∀ p : Z,
       ushp_exec_at s0 p toks -∗
       ubytes γd s0 (S len) (ushp_nulfold toks (ushp_ext len f)) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (8 + (6 + (6 + (16 + (24 + nn))))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hnosym Htoks Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy Hrun Hcont".
    rewrite shpp_parsecmd.
    iDestruct (ustr_len with "Hstr") as %Hlen31.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    assert (Elen0 : (len + ushp_skipws (len - len) len f)%nat = len)
      by (rewrite Nat.sub_diag; cbn [ushp_skipws]; lia).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | _ => m !!! Regidx s3_idx end).
    (* ---- 0x86e  c.addi16sp sp,sp,-64 ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x86e)
              (mword_of_int 60 : mword 6) 8 (52 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_86e with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
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
    set (spl := (mword_of_int (uint sp0 - 40) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 40)
      by (unfold spl; apply uint_moi; lia).
    set (sp3 := (mword_of_int (uint sp0 - 64) : mword 64)).
    assert (Hsp3u : uint sp3 = uint sp0 - 64)
      by (unfold sp3; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 3 [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    iDestruct (ushp_frame_split spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hloc") as "[Hlc Hbot]".
    rewrite !big_sepL_cons big_sepL_nil.
    iDestruct "Hlc" as "([%wl0 L0] & [%wcur Lcur] & [%wl2 L2] & _)".
    assert (E0 : uint sp0 - 40 - 8 * (Z.of_nat 0 + 1) = uint sp0 - 48)
      by lia.
    assert (E1 : uint sp0 - 40 - 8 * (Z.of_nat 1 + 1) = uint sp0 - 56)
      by lia.
    assert (E2 : uint sp0 - 40 - 8 * (Z.of_nat 2 + 1) = uint sp0 - 64)
      by lia.
    rewrite Hsplu E0 E1 E2.
    (* ---- 0x870..0x878  the five spills ---- *)
    iApply (wp_kshp_spill spn (52 + nn) [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x870 | 1%nat => 0x872
                              | 2%nat => 0x874 | 3%nat => 0x876
                              | 4%nat => 0x878 | _ => 0x87a end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_870 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_872 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_874 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_876 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_878 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x87a  c.addi4spn s0,sp,64 -- and its VALUE matters here ---- *)
    assert (Hup : add_vec_int spn (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 8) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    assert (Efp : add_vec spn
                    (sign_extend' 64
                       (caddi4spn_imm (mword_of_int 16 : mword 8))) = sp0).
    { assert (Ei : (sign_extend' 64
                      (caddi4spn_imm (mword_of_int 16 : mword 8)) : mword 64)
                   = mword_of_int (8 * Z.of_nat 8))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ei. exact Hup. }
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 m1 (mword_of_int 0x87a)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              sp0 (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1; symmetry; exact Efp)
              with "[] Hrun").
    { iApply (uis_shp_87a with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hs0_2 : m2 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
      symmetry. exact (moi_of_uint sp0). }
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int s0).
    { rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x87c  sd a0,-56(s0) -- the cursor cell is initialised ---- *)
    assert (Hcur0 : 0 < uint sp0 - 56) by lia.
    assert (Hcur8 : (uint sp0 - 56) mod 8 = 0).
    { rewrite Zminus_mod Hal8. reflexivity. }
    assert (Hcurz : uint sp0 - 56 + 8 < Z64) by lia.
    iApply (wp_uk_sd γt γd γs γfd h3 m2 (mword_of_int 0x87c)
              (mword_of_int 4040 : mword 12) s0_idx a0_idx
              (uint sp0 - 56) wcur (52 + nn)
              ltac:(rewrite Hs0_2 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              with "[] Lcur Hrun").
    { iApply (uis_shp_87c with "Hcode"). }
    iIntros "Lcur" (h4) "Hrun".
    rewrite Ha0_2.
    (* ---- 0x880  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m2 (mword_of_int 0x880) s1_idx a0_idx
              (mword_of_int s0) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2; symmetry; exact (ushp_mv_val s0))
              with "[] Hrun").
    { iApply (uis_shp_880 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int s0 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x882  jal a30 <strlen> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h5 m3 (mword_of_int 0x882)
              (mword_of_int 430 : mword 21) ra_idx
              (mword_of_int 0xa30) (mword_of_int 0x886) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_882 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x886 : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret4 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x886).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x886 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int s0).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_2. }
    rewrite <- shpp_strlen.
    iApply (wp_kshp_strlen h6 m4 (DfracOwn 1) s0 len f (50 + nn)
              Ha0_4 ltac:(lia) ltac:(lia) with "Hcode Hstr Hrun").
    iIntros "Hstr" (h7 m5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    (* ---- 0x886/0x888  the 32-bit zero extension ---- *)
    assert (E32 : (2:Z) ^ 32 = 4294967296) by (vm_compute; reflexivity).
    iApply (wp_uk_cslli γt γd γs γfd h7 m5 (mword_of_int 0x886)
              (mword_of_int 32 : mword 6) a0_idx
              (mword_of_int (Z.of_nat len * 2 ^ 32)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry;
                    exact (moi_shl (Z.of_nat len) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_886 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m6 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat len * 2 ^ 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat len * 2 ^ 32))
      by exact (upd_eq m5 (Regidx a0_idx)
                  (regval_into_reg
                     (mword_of_int (Z.of_nat len * 2 ^ 32) : mword 64))).
    iApply (wp_uk_csrli γt γd γs γfd h8 m6 (mword_of_int 0x888)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 3) a0_idx
              (mword_of_int (Z.of_nat len)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6
                      (moi_shr (Z.of_nat len * 2 ^ 32) 32 ltac:(lia)
                         ltac:(rewrite E32; unfold Z64; lia));
                    f_equal; symmetry; apply Z.div_mul; lia)
              with "[] Hrun").
    { iApply (uis_shp_888 with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m7 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat len) : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_7 : m7 !!! Regidx a0_idx = mword_of_int (Z.of_nat len))
      by exact (upd_eq m6 (Regidx a0_idx)
                  (regval_into_reg
                     (mword_of_int (Z.of_nat len) : mword 64))).
    (* ---- 0x88a  c.add s1,s1,a0 -- es = s + len ---- *)
    assert (Hs1_7 : m7 !!! Regidx s1_idx = mword_of_int s0).
    { rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hm6 s1_idx ltac:(vm_compute; discriminate))
              (Hcs45 s1_idx ltac:(vm_compute; reflexivity))
              (Hm4 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s1_idx)
               (regval_into_reg (mword_of_int s0 : mword 64))). }
    iApply (wp_uk_cadd γt γd γs γfd h9 m7 (mword_of_int 0x88a) s1_idx
              a0_idx (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_7 Ha0_7; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_88a with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m8 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_8 : m8 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len))
      by exact (upd_eq m7 (Regidx s1_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat len) : mword 64))).
    (* ---- 0x88c  addi s2,s0,-56 -- &s ---- *)
    assert (Hs0_8 : m8 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm8 s0_idx ltac:(vm_compute; discriminate))
              (Hm7 s0_idx ltac:(vm_compute; discriminate))
              (Hm6 s0_idx ltac:(vm_compute; discriminate))
              (Hcs45 s0_idx ltac:(vm_compute; reflexivity))
              (Hm4 s0_idx ltac:(vm_compute; discriminate))
              (Hm3 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_2. }
    iApply (wp_uk_addi γt γd γs γfd h10 m8 (mword_of_int 0x88c)
              (mword_of_int 4040 : mword 12) s0_idx s2_idx
              (mword_of_int (uint sp0 - 56)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_8;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 4040 : mword 12)
                                  : mword 64) = mword_of_int (-56))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_88c with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m9 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (uint sp0 - 56) : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s2_idx) (Regidx q) _ Hq)).
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int (uint sp0 - 56))
      by exact (upd_eq m8 (Regidx s2_idx)
                  (regval_into_reg
                     (mword_of_int (uint sp0 - 56) : mword 64))).
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_8. }
    (* ---- 0x890/0x892  parseline(&s, es) ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h11 m9 (mword_of_int 0x890) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_890 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv γt γd γs γfd h12 m10 (mword_of_int 0x892) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_892 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x894  jal 6e2 <parseline> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h13 m11 (mword_of_int 0x894)
              (mword_of_int 2096718 : mword 21) ra_idx
              (mword_of_int 0x6e2) (mword_of_int 0x898) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_894 with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x898 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x898).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x898 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 56) : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    rewrite <- shpp_parseline.
    iApply (wp_kshp_parseline h14 m12 (DfracOwn 1) dw dv
              (uint sp0 - 56) s0 len 0%nat f (mword_of_int s0) toks nn
              Ha0_12 Ha1_12 ltac:(lia)
              ltac:(f_equal; lia)
              Hnosym Htoks Htlen ltac:(lia) ltac:(lia)
              Hcur0 Hcur8 Hcurz
              with "Hcode Hro Lcur Hstr Hws Hsy Hrun").
    iIntros (p) "%Hpsz Hnode Lcur Hstr Hws Hsy".
    iIntros (h15 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12.
    iDestruct "Hnode" as "(%Hnl & %Hp0 & %Hp8 & Hty & Hav & Hev)".
    iAssert (ushp_exec_at s0 p toks) with "[Hty Hav Hev]" as "Hnode".
    { rewrite /ushp_exec_at.
      iSplitR; [ iPureIntro; exact Hnl | ].
      iSplitR; [ iPureIntro; exact Hp0 | ].
      iSplitR; [ iPureIntro; exact Hp8 | ].
      iSplitL "Hty"; [ iExact "Hty" | ].
      iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
    (* ---- 0x898  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h15 m13 (mword_of_int 0x898) s3_idx
              a0_idx (mword_of_int p) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_13; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_898 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m14 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx s3_idx) (Regidx q) _ Hq)).
    assert (Hs3_14 : m14 !!! Regidx s3_idx = mword_of_int p)
      by exact (upd_eq m13 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hs1_14 : m14 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm14 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_9. }
    assert (Hs2_14 : m14 !!! Regidx s2_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm14 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s2_idx ltac:(vm_compute; reflexivity))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_9. }
    assert (Hs0_14 : m14 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm14 s0_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s0_idx ltac:(vm_compute; reflexivity))
              (Hm12 s0_idx ltac:(vm_compute; discriminate))
              (Hm11 s0_idx ltac:(vm_compute; discriminate))
              (Hm10 s0_idx ltac:(vm_compute; discriminate))
              (Hm9 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_8. }
    (* ---- 0x89a/0x89e  the EMPTY token table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h16 m14 (mword_of_int 0x89a)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x189a) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_89a with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m15 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 0x189a : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_15 : m15 !!! Regidx a2_idx = mword_of_int 0x189a)
      by exact (upd_eq m14 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x189a : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h17 m15 (mword_of_int 0x89e)
              (mword_of_int 2542 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_none) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_15; unfold ushp_T_none;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_89e with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m16 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_none : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x8a2/0x8a4  peek(&s, es, "") ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h18 m16 (mword_of_int 0x8a2) a1_idx
              s1_idx (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm16 s1_idx ltac:(vm_compute; discriminate))
                      (Hm15 s1_idx ltac:(vm_compute; discriminate))
                      Hs1_14; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_8a2 with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m17 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m16).
    assert (Hm17 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m17 !!! Regidx q = m16 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m16 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv γt γd γs γfd h19 m17 (mword_of_int 0x8a4) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm17 s2_idx ltac:(vm_compute; discriminate))
                      (Hm16 s2_idx ltac:(vm_compute; discriminate))
                      (Hm15 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_14; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_8a4 with "Hcode"). }
    iIntros (h20) "Hrun".
    set (m18 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x8a6  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h20 m18 (mword_of_int 0x8a6)
              (mword_of_int 2096034 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x8aa) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_8a6 with "Hcode"). }
    iIntros (h21) "Hrun".
    set (m19 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8aa : mword 64)]> m18).
    assert (Hm19 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m19 !!! Regidx q = m18 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m18 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret19 : ret_pc (m19 !!! Regidx ra_idx) = mword_of_int 0x8aa).
    { rewrite (upd_eq m18 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x8aa : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_19 : m19 !!! Regidx a0_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm19 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m17 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 56) : mword 64))). }
    assert (Ha1_19 : m19 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm19 a1_idx ltac:(vm_compute; discriminate))
              (Hm18 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m16 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_19 : m19 !!! Regidx a2_idx = mword_of_int ushp_T_none).
    { rewrite (Hm19 a2_idx ltac:(vm_compute; discriminate))
              (Hm18 a2_idx ltac:(vm_compute; discriminate))
              (Hm17 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m15 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_none : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h21 m19 (DfracOwn 1) dw true DfracDiscarded
              (uint sp0 - 56) s0 ushp_T_none len len 0 f
              (ushp_lit ushp_T_none)
              (mword_of_int (s0 + Z.of_nat len)) (42 + nn)
              Ha0_19 Ha1_19 Ha2_19 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)
              ltac:(unfold ushp_T_none; lia)
              ltac:(unfold ushp_T_none, Z64; lia) Hcur0 Hcur8 Hcurz
              with "Hcode Lcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_none 0 DfracDiscarded
                ushp_T_none_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Lcur Hstr Hws _" (h22 m20) "%Hcs1920 %Ha0_20 Hrun".
    rewrite Eret19 Elen0.
    (* ---- 0x8aa  ld a2,-56(s0) -- the cursor, read back ---- *)
    assert (Hs0_19 : m19 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm19 s0_idx ltac:(vm_compute; discriminate))
              (Hm18 s0_idx ltac:(vm_compute; discriminate))
              (Hm17 s0_idx ltac:(vm_compute; discriminate))
              (Hm16 s0_idx ltac:(vm_compute; discriminate))
              (Hm15 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_14. }
    assert (Hs0_20 : m20 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hcs1920 s0_idx ltac:(vm_compute; reflexivity)).
      exact Hs0_19. }
    iApply (wp_uk_ld γt γd γs γfd h22 m20 (mword_of_int 0x8aa)
              (mword_of_int 4040 : mword 12) s0_idx a2_idx (DfracOwn 1)
              (uint sp0 - 56) (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_20 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              ltac:(vm_compute; discriminate)
              with "[] Lcur Hrun").
    { iApply (uis_shp_8aa with "Hcode"). }
    iIntros "Lcur" (h23) "Hrun".
    set (m21 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m20).
    assert (Hm21 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m21 !!! Regidx q = m20 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m20 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_21 : m21 !!! Regidx a2_idx
                     = mword_of_int (s0 + Z.of_nat len))
      by exact (upd_eq m20 (Regidx a2_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat len) : mword 64))).
    assert (Hs1_21 : m21 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm21 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1920 s1_idx ltac:(vm_compute; reflexivity))
              (Hm19 s1_idx ltac:(vm_compute; discriminate))
              (Hm18 s1_idx ltac:(vm_compute; discriminate))
              (Hm17 s1_idx ltac:(vm_compute; discriminate))
              (Hm16 s1_idx ltac:(vm_compute; discriminate))
              (Hm15 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_14. }
    (* ---- 0x8ae  bne a2,s1 -- NOT taken: there are no leftovers ---- *)
    iApply (wp_uk_btype γt γd γs γfd h23 m21 (mword_of_int 0x8ae)
              (mword_of_int 26 : mword 13) s1_idx a2_idx BNE false
              (mword_of_int 0x8c8) (52 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha2_21 Hs1_21;
                    rewrite (moi_neq_vec (s0 + Z.of_nat len)
                               (s0 + Z.of_nat len)
                               ltac:(unfold Z64 in *; lia)
                               ltac:(unfold Z64 in *; lia));
                    rewrite Z.eqb_refl; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_8ae with "Hcode"). }
    iIntros (h24) "Hrun".
    (* ---- 0x8b2  c.mv a0,s3 ---- *)
    assert (Hs3_21 : m21 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hm21 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1920 s3_idx ltac:(vm_compute; reflexivity))
              (Hm19 s3_idx ltac:(vm_compute; discriminate))
              (Hm18 s3_idx ltac:(vm_compute; discriminate))
              (Hm17 s3_idx ltac:(vm_compute; discriminate))
              (Hm16 s3_idx ltac:(vm_compute; discriminate))
              (Hm15 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_14. }
    iApply (wp_uk_cmv γt γd γs γfd h24 m21 (mword_of_int 0x8b2) a0_idx
              s3_idx (mword_of_int p) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_21; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_8b2 with "Hcode"). }
    iIntros (h25) "Hrun".
    set (m22 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m21).
    assert (Hm22 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m22 !!! Regidx q = m21 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m21 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x8b4  jal 7ee <nulterminate> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h25 m22 (mword_of_int 0x8b4)
              (mword_of_int 2096954 : mword 21) ra_idx
              (mword_of_int 0x7ee) (mword_of_int 0x8b8) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_8b4 with "Hcode"). }
    iIntros (h26) "Hrun".
    set (m23 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8b8 : mword 64)]> m22).
    assert (Hm23 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m23 !!! Regidx q = m22 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m22 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret23 : ret_pc (m23 !!! Regidx ra_idx) = mword_of_int 0x8b8).
    { rewrite (upd_eq m22 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x8b8 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_23 : m23 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm23 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m21 (Regidx a0_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iDestruct (ushp_ustr_bytes s0 len f with "Hstr") as "Hline".
    rewrite <- shpp_nulterminate.
    iApply (wp_kshp_nulterminate h26 m23 s0 p len (ushp_ext len f) toks
              (48 + nn) Ha0_23 ltac:(lia) ltac:(lia) Hp0 Hp8
              Hpsz Htlen
              ltac:(intros i t Hi;
                    destruct (ushp_tokens_in len f 0%nat toks Htoks
                                ltac:(lia) i t Hi) as [ Hlo0 Hhi0 ];
                    split; lia)
              with "Hcode Hro Hnode Hline Hrun").
    iIntros "Hnode Hline" (h27 m24) "%Hcs2324 %Ha0_24 Hrun".
    rewrite Eret23.
    (* ---- 0x8b8  c.mv a0,s3 ---- *)
    assert (Hs3_24 : m24 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs2324 s3_idx ltac:(vm_compute; reflexivity))
              (Hm23 s3_idx ltac:(vm_compute; discriminate))
              (Hm22 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_21. }
    iApply (wp_uk_cmv γt γd γs γfd h27 m24 (mword_of_int 0x8b8) a0_idx
              s3_idx (mword_of_int p) (52 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_24; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_8b8 with "Hcode"). }
    iIntros (h28) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m24).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m24 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m24 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* the whole body, as one preservation fact *)
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs2324 q Hq)
              (Hm23 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm22 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm21 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1920 q Hq)
              (Hm19 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm18 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm17 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm16 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q Hq3) (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q Hq2) (Hm8 q Hq1)
              (Hm7 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs45 q Hq)
              (Hm4 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm3 q Hq1) (Hm2 q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs2324 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm23 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm22 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm21 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1920 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm19 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm18 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm17 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm16 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x8ba..0x8c6  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 8 3 [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)] (mword_of_int 7 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x8ba | 1%nat => 0x8bc
                              | 2%nat => 0x8be | 3%nat => 0x8c0
                              | 4%nat => 0x8c2 | _ => 0x8c4 end)
              (mword_of_int 4 : mword 6) sp0 spl vals (52 + nn) h28 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) ltac:(lia)
              ltac:(cbn [length]; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| i ]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    vm_compute; discriminate)
              with "Hcode [] [] [] Hsl [L0 Lcur L2 Hbot] Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_8ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8c2 with "Hcode") | done ]. }
    { iApply (uis_shp_8c4 with "Hcode"). }
    { iApply (uis_shp_8c6 with "Hcode"). }
    { iApply (ushp_frame_join spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                (fun i : nat => match i with
                                | 0%nat => wl0
                                | 1%nat => mword_of_int (s0 + Z.of_nat len)
                                | _ => wl2 end)
                ltac:(cbn [length]; lia) with "[L0 Lcur L2] Hbot").
      rewrite !big_sepL_cons big_sepL_nil Hsplu E0 E1 E2.
      iSplitL "L0"; [ iExact "L0" | ].
      iSplitL "Lcur"; [ iExact "Lcur" | ].
      iSplitL "L2"; [ iExact "L2" | done ]. }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! p with "Hnode Hline Hws Hsy [] [] Hrun").
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 6 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 5 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 3 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m24 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* §15 THE PARSER THEOREM.                                                *)
  (*                                                                       *)
  (* Everything above is a walk of one function; this is the statement the  *)
  (* lane owed, and it is a two-line corollary of [wp_kshp_parsecmd]        *)
  (* because the walks were stated in the vocabulary stages 5-6 read:       *)
  (*                                                                       *)
  (*   GIVEN a NUL-terminated command line at [s0] with no symbol byte in   *)
  (*   it, whose tokens (in the ported [ushp_tokens] sense) are [toks] and  *)
  (*   number fewer than MAXARGS, and sh's two static tables,               *)
  (*                                                                       *)
  (*   sh's [parsecmd] RETURNS a node [p] with [ushp_tree s0 p              *)
  (*   (UshpExec toks)] -- the deliverable interface of §5 -- with the line *)
  (*   NUL-CUT at every token's end index, with the callee-saved file       *)
  (*   intact, and at the return address.                                   *)
  (*                                                                       *)
  (* WHAT IT IS NOT.  It is not parametric in the SHAPE of the command: a   *)
  (* line with a symbol byte in it reaches parseblock, redircmd, pipecmd,   *)
  (* listcmd or backcmd, none of which is catalogued, and the [panic] arms  *)
  (* are refuted only under [ushp_no_symbols].  That premise is the scope   *)
  (* stage 4 was given and it is the scope this theorem keeps.              *)
  (*                                                                       *)
  (* AUDIT.  Two Hypotheses reach it and no others: [ushp_malloc_ok]        *)
  (* (stage 3's allocator, through execcmd) and [ushp_clw_text_ok]          *)
  (* (the four-byte TEXT-half load, through nulterminate's jump table --    *)
  (* which is [UkShRun.wp_uk_clw_text] and needs only to be un-Local'd).    *)
  (* Everything else is the standing three.                                 *)
  (* ===================================================================== *)

  (* the NUL-cut, as a fact about the bytes: every write the loop makes is a
     zero, so a byte it has zeroed stays zero *)
  Lemma ushp_nulfold_keep (toks : list (nat * nat)) (g : nat -> bv 8)
      (j : nat) :
    g j = ubyte0 -> ushp_nulfold toks g j = ubyte0.
  Proof.
    revert g. induction toks as [| tk r IH ]; intros g Hg;
      cbn [ushp_nulfold]; [ exact Hg | ].
    apply IH. rewrite /ushp_setb.
    destruct (Nat.eqb j (snd tk)); [ reflexivity | exact Hg ].
  Qed.

  Lemma ushp_nulfold_hit (toks : list (nat * nat)) (g : nat -> bv 8)
      (i : nat) (tk : nat * nat) :
    toks !! i = Some tk -> ushp_nulfold toks g (snd tk) = ubyte0.
  Proof.
    revert g i. induction toks as [| t r IH ]; intros g i Hi;
      [ rewrite lookup_nil in Hi; discriminate | ].
    destruct i as [| i ]; cbn in Hi.
    - injection Hi as <-. cbn [ushp_nulfold]. apply ushp_nulfold_keep.
      rewrite /ushp_setb Nat.eqb_refl. reflexivity.
    - cbn [ushp_nulfold]. exact (IH _ i Hi).
  Qed.

  Theorem wp_kshp_parser (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0%nat toks ->
    (length toks < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parsecmd) (60 + nn) -∗
    (∀ p : Z,
       ⌜ ushp_parses s0 len f p (UshpExec toks) ⌝ -∗
       ushp_tree s0 p (UshpExec toks) -∗
       ubytes γd s0 (S len) (ushp_nulfold toks (ushp_ext len f)) -∗
       ⌜ forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
           ushp_nulfold toks (ushp_ext len f) (snd tk) = ubyte0 ⌝ -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (60 + nn) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hnosym Htoks Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy Hrun Hcont".
    iApply (wp_kshp_parsecmd h m dw dv s0 len f toks nn
              Ha0 Hnosym Htoks Htlen Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy Hrun").
    iIntros (p) "Hnode Hline Hws Hsy".
    iApply ("Hcont" $! p with "[] Hnode Hline [] Hws Hsy").
    - iPureIntro. exists toks. split; [ exact Htoks | ].
      split; [ exact Htlen | reflexivity ].
    - iPureIntro. intros i tk Hi.
      exact (ushp_nulfold_hit toks (ushp_ext len f) i tk Hi).
  Qed.

End UkShParse.
