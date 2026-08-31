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
(* THAT REUSE IS BLOCKED TODAY, AND THE BLOCK IS A CONTRACT, NOT A PROOF.  *)
(* [UkSh.wp_ksh_memset]'s postcondition is [∃ g, ubytes γd a N g] -- the   *)
(* buffer comes back OWNED but with UNKNOWN CONTENTS.  That is enough for  *)
(* stage 2 (getcmd only needs the buffer back) and NOT enough for stage 4: *)
(* [execcmd] is [malloc(168); memset(cmd, 0, 168); cmd->type = EXEC], and  *)
(* the only reason [cmd->argv[0] == 0] -- the NULL cap the tree predicate  *)
(* and [nulterminate]'s loop both turn on -- is that the memset ZEROED it. *)
(* The fact is present in stage 2's proof (its loop stores                 *)
(* [nth_byte (mc !!! a1) 0] at every index) and absent from its statement. *)
(* ASK: strengthen [wp_ksh_memset] to hand back                            *)
(* [ubytes γd a N (fun _ => nth_byte (m !!! a1_idx) 0)]; the existential    *)
(* form is then one [iExists] away, so no stage-2 call site moves.  Until  *)
(* it lands, [execcmd] cannot be walked and the constructor chain above it *)
(* cannot start.                                                           *)
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

Section UkShParse.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

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
  (* WHAT IT TAINTS: nothing yet.  Stage 4 landed the lexer's bottom        *)
  (* ([wp_kshp_strchr]) and the vocabulary above, and neither calls a       *)
  (* constructor -- every lemma in this file is unconditional.  The moment  *)
  (* [wp_kshp_execcmd] lands it becomes the first tainted lemma, and        *)
  (* [parseexec], [parsepipe], [parseline] and [parsecmd] follow it, each   *)
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

End UkShParse.
