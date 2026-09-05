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
(* SPLIT INTO SIX FILES (2026-09-05), and the reason is ITERATION COST.    *)
(* The monolith was 14 900 lines and ~2 min 30 s to compile, which every    *)
(* one-line edit anywhere in the parser paid in full.  The pieces are cut   *)
(* at the CALL GRAPH's own joints, so each is a function or two:            *)
(*                                                                        *)
(*   UkShParse.v       the BASE -- the pure vocabulary, the byte/register  *)
(*                     algebra, [ushp_sstr], strchr, strlen, the frame     *)
(*                     runs, the TREE PREDICATE, and [ushp_malloc_ty]      *)
(*   UkShParseLex.v    peek, the seven token tables, execcmd               *)
(*   UkShParseTok.v    gettoken                                            *)
(*   UkShParseRedir.v  parseredirs                                         *)
(*   UkShParseExec.v   parseexec -- the argument loop                      *)
(*   UkShParseCmd.v    parsepipe, parseline, nulterminate, parsecmd, and   *)
(*                     THE PARSER THEOREM                                  *)
(*                                                                        *)
(* WHAT A SPLIT COSTS, and it is worth knowing before splitting anything    *)
(* else this way.  A Section's [Context] variables are DISCHARGED at [End], *)
(* so every lemma a later file calls now takes [γt γd γs γfd] (and, past    *)
(* UkShParseLex.v, [UMalloc UMalloc' ushp_malloc_ok]) as explicit leading   *)
(* arguments -- which would mean editing every call site.  It does not,     *)
(* because each downstream file opens with a block of                       *)
(*                                                                        *)
(*     Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek γt γd γs γfd). *)
(*                                                                        *)
(* one per name it uses, so the bodies are unchanged text.  The aliases     *)
(* also carry [rewrite /X] and [unfold X] through, which is why the         *)
(* PREDICATES can cross the same way.  The other cost is real and paid per  *)
(* file: ~20 s of prelude (UCodeShP.vo is 564 instructions of catalog), so  *)
(* the SUM of the six is longer than the monolith was -- and the WORST      *)
(* single file is 1 min 52 s (parseexec) instead of 2 min 30 s, with four   *)
(* of the six under 30 s.  That trade is the point.                        *)
(*                                                                        *)
(* WHAT IS HERE, ACROSS ALL SIX.                                            *)
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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UserBits.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
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
  Lemma shpp_strchr : ShSyms.strchr = 0xa82.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&_&_&_&H). exact H. Qed.
  Lemma shpp_strlen : ShSyms.strlen = 0xa30.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Lemma shpp_execcmd : ShSyms.execcmd = 0x1d2.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&_&H&_&_). exact H. Qed.
  Lemma shpp_gettoken : ShSyms.gettoken = 0x310.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&_&H&_&_&_). exact H. Qed.
  Lemma shpp_peek : ShSyms.peek = 0x448.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&_&H&_&_&_&_). exact H. Qed.
  Lemma shpp_nulterminate : ShSyms.nulterminate = 0x7ee.
  Proof. destruct shp_syms_pins as (_&_&_&_&_&H&_&_&_&_&_). exact H. Qed.
  Lemma shpp_parseredirs : ShSyms.parseredirs = 0x4ac.
  Proof. destruct shp_syms_pins as (_&_&_&_&H&_&_&_&_&_&_). exact H. Qed.
  Lemma shpp_parseexec : ShSyms.parseexec = 0x590.
  Proof. destruct shp_syms_pins as (_&_&_&H&_&_&_&_&_&_&_). exact H. Qed.
  Lemma shpp_parsepipe : ShSyms.parsepipe = 0x682.
  Proof. destruct shp_syms_pins as (_&_&H&_&_&_&_&_&_&_&_). exact H. Qed.
  Lemma shpp_parseline : ShSyms.parseline = 0x6e2.
  Proof. destruct shp_syms_pins as (_&H&_&_&_&_&_&_&_&_&_). exact H. Qed.
  Lemma shpp_parsecmd : ShSyms.parsecmd = 0x86e.
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

  Lemma ushp_ridx_eq (r q : mword 5) : uint r = uint q -> Regidx r = Regidx q.
  Proof.
    intro H. f_equal. apply bv_eq. rewrite <- !(uint_unsigned_n 5). exact H.
  Qed.

  Lemma ushp_ridx_ne (r q : mword 5) : uint r <> uint q -> Regidx r <> Regidx q.
  Proof.
    intros H He. apply H.
    assert (Hrq : r = q) by (injection He; trivial). rewrite Hrq. reflexivity.
  Qed.

  Lemma ushp_cs_ne (r q : mword 5) :
    ucallee_saved_idx r = true -> ucallee_saved_idx q = false ->
    Regidx r <> Regidx q.
  Proof.
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  (* a byte's numeric value is in range *)
  Lemma ushp_byte_rng (b : bv 8) : 0 <= bv_unsigned b < 256.
  Proof.
    pose proof (bv_unsigned_in_range 8 b) as Hr8.
    assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite Em8 in Hr8. exact Hr8.
  Qed.

  (* two bytes are equal exactly when their zero-extended words are.  This
     is the whole content of strchr's comparison: [beq a1,a5] runs on the
     64-bit registers, and both were filled by an [lbu]. *)
  Lemma ushp_zext_eq (b c : bv 8) :
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
  Lemma ushp_zext_nul (b : bv 8) :
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
  Lemma urun_x0 (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat) :
    urun γt γd γs γfd h m pc avail -∗
    ⌜ m !!! Regidx x0_idx = zero_reg ⌝ ∗ urun γt γd γs γfd h m pc avail.
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw)
      "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv, cw.
    iFrame "Hheap Hstk Hufd Hb".
    iPureIntro. split_and!; [ exact Hlo | exact Hpm | exact HRut ].
  Qed.

  (* ...and what that instruction WRITES: 1 exactly when its operand is
     nonzero, which is how peek turns a strchr result into a C boolean. *)
  Lemma ushp_snez_val (v : Z) :
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
  Lemma wp_ushp_lbu (tx : bool) (dq : dfrac) (h : CpuId) (m : regfile)
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
  Lemma ushp_pc_step (x d : Z) :
    add_vec_int (mword_of_int x : mword 64) d = mword_of_int (x + d).
  Proof. unfold add_vec_int. apply moi_add. Qed.

  (* ...and the same with the DESTINATION named, so a walk never carries a
     [mword_of_int (0x420 + 4)] a later [rewrite] then fails to match. *)
  Lemma ushp_pc_step' (x d y : Z) :
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
  Lemma wp_kshp_fp (h : CpuId) (m : regfile) (p : Z) (nz : mword 8)
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
  Lemma wp_kshp_pro2 (h : CpuId) (m : regfile)
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
  Lemma wp_kshp_epi2 (h : CpuId) (me : regfile)
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
  Lemma wp_kshp_strchr_loop (tx : bool) (dq : dfrac) (s : Z) (len : nat)
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
  Lemma ushp_mv_val (v : Z) :
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
  Lemma wp_kshp_strlen_loop (dq : dfrac) (s : Z) (len : nat)
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
  Lemma ushp_moi_neq (x y : Z) :
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
  Lemma ushp_sepL_seq {A : Type} (l : list A) (Φ : nat -> iProp Σ) :
    ([∗ list] i ∈ seq 0 (length l), Φ i) ⊣⊢ ([∗ list] i ↦ _ ∈ l, Φ i).
  Proof.
    revert Φ. induction l as [| x l IH ]; intros Φ; [ reflexivity | ].
    cbn [length seq]. rewrite !big_sepL_cons.
    rewrite <- (seq_shift (length l) 0), big_sepL_fmap.
    rewrite (IH (fun i => Φ (S i))). reflexivity.
  Qed.

  (* a slot of an 8-aligned frame is itself 8-aligned *)
  Lemma ushp_slot_al (sp : Z) (i : nat) :
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
  Lemma ushp_slot_al8 (p c : Z) (k : nat) :
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
  Lemma ushp_frame_split (sp0 sp1 : mword 64) (n : nat)
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
  Lemma ushp_frame_join (sp0 sp1 : mword 64) (n : nat)
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
  Lemma wp_kshp_spill (spn : mword 64) (nn : nat) :
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
  Lemma wp_kshp_restore (spn : mword 64) (nn : nat) :
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

  Lemma wp_kshp_frame_pro (k n : nat) (rs : list (mword 5 * mword 6))
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
  Lemma wp_kshp_frame_epi (k n : nat) (rs : list (mword 5 * mword 6))
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
  Lemma ushp_ubytes_ext (a : Z) (n : nat) (f g : nat -> bv 8) :
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
  Lemma ushp_peel (a b : Z) (k n : nat) (f : nat -> bv 8) :
    b = a + Z.of_nat k ->
    ubytes γd a (k + n) f -∗
      ubytes γd a k f ∗ ubytes γd b n (fun j => f (k + j)%nat).
  Proof.
    intros Hb. rewrite (ubytes_app γd a k n f) Hb. iIntros "$".
  Qed.

  (* ...and the same at the ZEROED run [memset] hands back, where keeping
     the content function literally constant is what lets a call site name
     it in the next lemma's arguments *)
  Lemma ushp_peel0 (a b : Z) (k n : nat) :
    b = a + Z.of_nat k ->
    ubytes γd a (k + n) (fun _ : nat => ubyte0) -∗
      ubytes γd a k (fun _ : nat => ubyte0) ∗
      ubytes γd b n (fun _ : nat => ubyte0).
  Proof.
    intros Hb. rewrite (ubytes_app γd a k n (fun _ : nat => ubyte0)) Hb.
    iIntros "$".
  Qed.

  Lemma ushp_nth_byte_zero (j : nat) :
    (j < 8)%nat -> nth_byte (mword_of_int 0 : mword 64) j = ubyte0.
  Proof.
    intro Hj. destruct j as [| [| [| [| [| [| [| [| j ]]]]]]]];
      try (vm_compute; reflexivity). lia.
  Qed.

  (* the ten argv (or eargv) slots of a FRESH node.  memset zeroed all
     eighty bytes, so slot 0 is exactly the NULL cap [ushp_slot] asks for at
     [|toks| = 0] and the nine above it are its unconstrained cells. *)
  Lemma ushp_slots_nil (t0 base : Z) (sel : nat * nat -> nat)
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

  Lemma ushp_slots_weaken (s0 base : Z) (toks : list (nat * nat))
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
  Lemma ushp_slots_nil0 (t0 base : Z) (sel : nat * nat -> nat)
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
  Lemma ushp_lookup_app_ne (done : list (nat * nat)) (tk : nat * nat)
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

  Lemma ushp_lookup_app_mid (done : list (nat * nat)) (tk : nat * nat) :
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
  Lemma ushp_slots_cap (s0 base : Z) (toks : list (nat * nat))
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
  Lemma ushp_slots_upd (s0 base : Z) (done : list (nat * nat))
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
  (* THE ALLOCATOR'S CONTRACT, AS A NAMED TYPE.                             *)
  (*                                                                        *)
  (* Stage 4's one Hypothesis is carried by four files, so its STATEMENT     *)
  (* lives here once and each of them writes                                *)
  (* [Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'].  Same    *)
  (* device as [UkShDiag.ushd_clw_text_ty], and for the same reason: a       *)
  (* Hypothesis re-typed by hand in four places is four chances to say       *)
  (* something slightly different, and the difference would surface as a     *)
  (* unification failure a thousand lines away.                             *)
  (*                                                                        *)
  (* THE ALLOCATOR'S STATE IS A ONE-SHOT RESOURCE, IN AND OUT.  The parser   *)
  (* calls [malloc] exactly ONCE per line -- [execcmd] is the only           *)
  (* constructor a symbol-free line reaches -- so what crosses is [UM] in    *)
  (* and [UM'] out, and no lemma of the parser needs to know what either is. *)
  (* Naming them rather than baking a free-list predicate into the parser's  *)
  (* statements is what lets stage 3 pick the scope of its own theorem (see  *)
  (* iris/UkShMalloc.v: what discharges this is FIRST-CALL, [freep == 0])    *)
  (* without stage 4 having an opinion about it.                            *)
  (* ===================================================================== *)
  Definition ushp_malloc_ty (UM UM' : iProp Σ) : Prop :=
    forall (h : CpuId) (m : regfile) (nbytes : Z) (avail : nat),
      m !!! Regidx a0_idx = mword_of_int nbytes ->
      0 < nbytes -> nbytes <= 65504 ->
      shp_code γt -∗
      UM -∗
      urun γt γd γs γfd h m (mword_of_int ShSyms.malloc) (10 + avail) -∗
      (∀ (h' : CpuId) (m' : regfile) (p : Z) (g : nat -> bv 8),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         ⌜ 0 < p /\ p mod 16 = 0 /\ p + nbytes < 2 ^ 38 ⌝ -∗
         ubytes γd p (Z.to_nat nbytes) g -∗
         UM' -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + avail) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).

End UkShParse.
