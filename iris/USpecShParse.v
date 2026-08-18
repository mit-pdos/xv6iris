(* USpecShParse.v -- the contracts of `sh''s LEXER and RECURSIVE-DESCENT
   PARSER, on the input this development is about
   (claude-notes/projects/user-sh.md).

   Split out of USpecSh.v because it needs a vocabulary of its own: a
   TOKENIZATION model.  Everything here is stated over a command buffer
   [bs] at address [s0], NUL-terminated -- which is what [gets] leaves
   behind -- and a parse position given as an OFFSET into it, which is how
   the code carries it (a `char **ps' cell the callee advances).

   WHAT IS AND IS NOT GENERAL.  [peek] and [gettoken] are stated generally,
   over arbitrary buffer contents: they are called eight times between them
   and a general contract pays for itself.  [gettoken] does exclude the
   SYMBOL arms of its switch by a premise -- the input has no `<|>&;()' --
   so it covers exactly the word and end-of-input cases, which is what
   `sh_is_sym b = false' says.  The four parse* functions are stated at the
   shape the input actually has (a whitespace-separated list of word tokens,
   no redirections, no pipe, no list) (no block); [parseblock], [redircmd],
   [pipecmd], [listcmd] and [backcmd] are not reached and are not even in
   the code catalog. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeIo.
Require Import UCodeSh USpecSh.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

Section USpecShParse.
  Context `{!riscvGS Σ} `{!uioG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).
  Local Notation UVG m M := (uv_cap_gpr C pt Psh M m).

  (* ------------------------------------------------------------------- *)
  (* §1 The tokenization model.                                            *)
  (*                                                                       *)
  (* [sh_tokens bs off toks] : scanning [bs] from offset [off], the maximal *)
  (* non-whitespace runs are exactly [toks], as (start, end) OFFSETS.  It   *)
  (* is defined inductively in the shape the arg loop of [parseexec] runs   *)
  (* in, so the loop's invariant is literally one constructor.             *)
  (* ------------------------------------------------------------------- *)

  Inductive sh_tokens (bs : list (bv 8)) : nat -> list (nat * nat) -> Prop :=
  | ShTokNil (off : nat) :
      (off + sh_skipws (drop off bs) = length bs)%nat ->
      sh_tokens bs off []
  | ShTokCons (off : nat) (toks : list (nat * nat)) :
      let k := sh_skipws (drop off bs) in
      let n := sh_toklen (drop (off + k) bs) in
      (0 < n)%nat ->
      sh_tokens bs (off + k + n)%nat toks ->
      sh_tokens bs off ((off + k, off + k + n)%nat :: toks).

  (* the bytes of the i-th token *)
  Definition sh_tok_bytes (bs : list (bv 8)) (t : nat * nat) : list (bv 8) :=
    take (snd t - fst t)%nat (drop (fst t) bs).

  (* no symbol byte anywhere in the buffer -- what keeps [gettoken] in its
     default arm and [parseredirs] / [parsepipe] / [parseline] out of their
     loops.  True of `echo Hello world!', and the reason this development
     needs neither [parseblock] nor the four other cmd constructors. *)
  Definition sh_no_symbols (bs : list (bv 8)) : Prop :=
    forall (j : nat) (b : bv 8), bs !! j = Some b -> sh_is_sym b = false.

  (* ... and the buffer is a genuine C string with no interior NUL *)
  Definition sh_buf_ok (M : gmap Z (bv 8)) (s0 : Z) (bs : list (bv 8)) : Prop :=
    ustr_at M s0 bs /\
    (forall (j : nat) (b : bv 8), bs !! j = Some b -> b <> ubyte0).

  (* the premises every lexer/parser contract shares: the buffer, the two
     static tables, the image and the layout *)
  Definition sh_parse_pre (M : gmap Z (bv 8)) (s0 : Z) (bs : list (bv 8))
      (sp0 : mword 64) (n : Z) : Prop :=
    sh_layout pt hbase hlen /\ sh_img_sub M /\ sh_tables_ok M /\
    sh_buf_ok M s0 bs /\ sh_no_symbols bs /\
    uv_rd pt M s0 (Z.of_nat (length bs) + 1) /\
    uv_wr pt M s0 (Z.of_nat (length bs) + 1) /\
    (* ABOVE THE LOADED IMAGE, not merely positive.  Every function here
       WRITES the buffer, and [sh_layout] gives the text pages Fetch+Load
       without ever denying Store -- so [uv_wr pt M s0 …] at a text address
       is perfectly consistent, and a buffer there would destroy
       [sh_text_sub]/[sh_data_sub] and with them every [ui_sh_*] fact.
       8208 = SH_FREEP is the sharp bound: it clears the text (8192) AND
       the two static tables at 0x2000..0x2010, which the lexer reads on
       every token.  [wp_sh_getcmd_body] already carries the analogue. *)
    8208 <= s0 /\ s0 + Z.of_nat (length bs) + 1 <= 2 ^ 38 /\
    (* the frame misses the program image and the heap ... *)
    sh_frame_ok hbase hlen sp0 n /\
    (* ... and the command buffer misses the frame *)
    s0 + Z.of_nat (length bs) + 1 <= uint sp0 - n.

  (* [a,a+n) and [b,b+k) do not overlap. *)
  Definition sh_disj (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

  (* The command buffer misses the two allocator statics and the heap.
     Without it NO caller can carry [sh_buf_ok] across a [parse*] call:
     those are exactly the windows the run's single [malloc] disturbs, and
     a postcondition that does not exclude them leaves the buffer's bytes
     unknown -- which is fatal, because [nulterminate] and then the [exec]
     arm both read the buffer AFTER the allocation.  True of `buf.0' at
     0x2020: it sits BETWEEN freep (0x2010) and base (0x2088). *)
  Definition sh_buf_clear (s0 len : Z) : Prop :=
    sh_disj s0 len SH_FREEP 8 /\ sh_disj s0 len SH_BASE 16 /\
    (* BELOW the heap, not merely disjoint from it.  As a [sh_disj] this
       admitted the other arm, [hbase + 65536 <= s0], which leaves the argv
       strings unbounded above and makes [sh_exec_below]'s [p + |bs_i| < B]
       unprovable at [parsecmd].  The buffer really is below: `buf.0' is at
       0x2020 and [shl_hlo] puts [hbase] at 0x3000 or above. *)
    s0 + len <= hbase.

  (* A `char **' cell a caller passes down.  The code LOADS through it
     (`s = *ps'), so a store-permitting leaf is not enough; it is 8-aligned
     and it is a caller LOCAL, hence at or above the callee's entry sp. *)
  Definition sh_ptr_cell (M : gmap Z (bv 8)) (a v : Z) (sp0 : mword 64) : Prop :=
    uM_bytes M a 8 (mword_of_int v : mword 64) /\
    uv_rd pt M a 8 /\ uv_wr pt M a 8 /\
    a mod 8 = 0 /\ uint sp0 <= a /\ a + 8 <= 2 ^ 38.

  (* ------------------------------------------------------------------- *)
  (* §2 peek(ps, es, toks).                                                *)
  (*                                                                       *)
  (* Skips whitespace, writes the new position back through [ps], and       *)
  (* returns whether the byte it stopped on is one of [toks].  It reads     *)
  (* *s even when s == es, which is why the buffer's NUL matters.           *)
  (* ------------------------------------------------------------------- *)

  Definition sh_peek_ret (bs : list (bv 8)) (off : nat)
      (tbs : list (bv 8)) : Z :=
    let k := sh_skipws (drop off bs) in
    match (drop (off + k) bs) !! 0%nat with
    | Some b => if bool_decide (b ∈ tbs) then 1 else 0
    | None => 0
    end.

  Definition wp_sh_peek_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr s0 : Z) (bs : list (bv 8)) (off : nat)
      (toks : Z) (tbs : list (bv 8)) :=
    forall (Hpre : sh_parse_pre M s0 bs sp0 80)      (* own 64 + strchr 16 *)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 80)
      (Hps : m !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a1_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Htoksr : m !!! Regidx a2_idx = (mword_of_int toks : mword 64))
      (Hcell : sh_ptr_cell M psaddr (s0 + Z.of_nat off) sp0)
      (Hoff : (off <= length bs)%nat)
      (* the token table: a real, non-NULL, NUL-terminated string that misses
         the frame.  [0 < toks] is not decoration -- with toks = 0 the code's
         [strchr(0, *s)] returns 0 and peek returns 0 while [sh_peek_ret]
         says 1, so the postcondition would be FALSE. *)
      (Htnn : 0 < toks)
      (Htbs : ustr_at M toks tbs)
      (Htnz : forall (j : nat) (b : bv 8), tbs !! j = Some b -> b <> ubyte0)
      (Htrd : uv_rd pt M toks (Z.of_nat (length tbs) + 1))
      (Uthi : toks + Z.of_nat (length tbs) + 1 <= uint sp0 - 80)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.peek) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (sh_peek_ret bs off tbs) : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (off + sh_skipws (drop off bs)))
           : mword 64)⌝ -∗
       (* peek disturbs the [ps] cell AND its own frame (plus strchr's) --
          naming either alone would be wrong, not weak *)
       ⌜uM_only_in M M' [sh_win (psaddr) (8); sh_win (uint sp0 - 80) (80)]⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §3 gettoken(ps, es, q, eq).                                           *)
  (*                                                                       *)
  (* ONE contract covers both reachable arms.  With                         *)
  (*   k  = leading whitespace, n = the token's length,                     *)
  (*   k2 = whitespace after it,                                            *)
  (* the word arm has n > 0 and returns 'a' = 97, and the end-of-input arm  *)
  (* has off+k = |bs|, hence n = k2 = 0, and returns 0 -- and then *q, *eq  *)
  (* and *ps all coincide, exactly as the code leaves them.                 *)
  (* ------------------------------------------------------------------- *)

  Definition wp_sh_gettoken_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr qaddr eqaddr s0 : Z) (bs : list (bv 8))
      (off : nat) :=
    forall (Hpre : sh_parse_pre M s0 bs sp0 80)      (* own 64 + strchr 16 *)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 80)
      (Hps : m !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a1_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Hq : m !!! Regidx a2_idx = (mword_of_int qaddr : mword 64))
      (Heq : m !!! Regidx a3_idx = (mword_of_int eqaddr : mword 64))
      (Hcell : sh_ptr_cell M psaddr (s0 + Z.of_nat off) sp0)
      (* [q] and [eq] may be NULL: parseredirs and parseline call
         gettoken(ps, es, 0, 0).  They are written, never read. *)
      (Hqw : qaddr = 0 \/ (uv_wr pt M qaddr 8 /\ qaddr mod 8 = 0 /\
                           uint sp0 <= qaddr /\ qaddr + 8 <= 2 ^ 38))
      (Heqw : eqaddr = 0 \/ (uv_wr pt M eqaddr 8 /\ eqaddr mod 8 = 0 /\
                             uint sp0 <= eqaddr /\ eqaddr + 8 <= 2 ^ 38))
      (* the three cells are written in turn and the postcondition asserts
         all three AT ONCE, so any aliasing would make it false *)
      (Hdis1 : qaddr = 0 \/ qaddr + 8 <= psaddr \/ psaddr + 8 <= qaddr)
      (Hdis2 : eqaddr = 0 \/ eqaddr + 8 <= psaddr \/ psaddr + 8 <= eqaddr)
      (Hdis3 : qaddr = 0 \/ eqaddr = 0 \/
               qaddr + 8 <= eqaddr \/ eqaddr + 8 <= qaddr)
      (Hoff : (off <= length bs)%nat)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.gettoken) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       let k  := sh_skipws (drop off bs) in
       let n  := sh_toklen (drop (off + k) bs) in
       let k2 := sh_skipws (drop (off + k + n) bs) in
       ⌜ucallee_saved m m'⌝ -∗
       (* 'a' for a word, 0 at end of input *)
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (if bool_decide ((off + k)%nat = length bs)
                           then 0 else 97) : mword 64)⌝ -∗
       ⌜qaddr <> 0 ->
          uM_bytes M' qaddr 8 (mword_of_int (s0 + Z.of_nat (off + k)) : mword 64)⌝ -∗
       ⌜eqaddr <> 0 ->
          uM_bytes M' eqaddr 8
            (mword_of_int (s0 + Z.of_nat (off + k + n)) : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (off + k + n + k2)) : mword 64)⌝ -∗
       (* WITHOUT this the caller cannot carry anything at all across a
          gettoken call -- not the command buffer, not the execcmd node,
          not the heap.  Claiming (0,8) for a NULL pointer is a harmless
          weakening of the window list. *)
       ⌜uM_only_in M M' [sh_win (psaddr) (8); sh_win (qaddr) (8); sh_win (eqaddr) (8);
                         sh_win (uint sp0 - 80) (80)]⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §4 The parser.                                                        *)
  (*                                                                       *)
  (* [parseredirs], [parsepipe] and [parseline] each guard a loop or a      *)
  (* branch with a [peek] for a symbol that [sh_no_symbols] excludes, so    *)
  (* all three reduce to "advance past whitespace and return the argument   *)
  (* untouched" / "delegate".  Only [parseexec] does work.                  *)
  (* ------------------------------------------------------------------- *)

  (* parseredirs(cmd, ps, es): the loop never runs. *)
  Definition wp_sh_parseredirs_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (cmd psaddr s0 : Z) (bs : list (bv 8)) (off : nat) :=
    forall (Hpre : sh_parse_pre M s0 bs sp0 (112 + 64 + 16))
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (112 + 64 + 16))
      (Hcmd : m !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      (Hps : m !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a2_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Hcell : sh_ptr_cell M psaddr (s0 + Z.of_nat off) sp0)
      (Hoff : (off <= length bs)%nat)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.parseredirs) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int cmd : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (off + sh_skipws (drop off bs)))
           : mword 64)⌝ -∗
       (* it advances [ps] and spills into its own frame (and peek's), and
          nothing else -- in particular the execcmd node its caller just
          allocated, and the command buffer, both survive it *)
       ⌜uM_only_in M M' [sh_win (psaddr) (8);
                         sh_win (uint sp0 - (112 + 64 + 16)) (112 + 64 + 16)]⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* parseexec(ps, es): allocate an execcmd, then the arg loop.  [toks] is
     the tokenization of what is left, and the postcondition is that the
     execcmd's argv/eargv are exactly those token boundaries, NULL-capped. *)
  Definition sh_execcmd_argv (M : gmap Z (bv 8)) (cmd s0 : Z)
      (toks : list (nat * nat)) : Prop :=
    (forall (i : nat) (t : nat * nat), toks !! i = Some t ->
       uM_bytes M (cmd + 8 + 8 * Z.of_nat i) 8
         (mword_of_int (s0 + Z.of_nat (fst t)) : mword 64) /\
       uM_bytes M (cmd + 88 + 8 * Z.of_nat i) 8
         (mword_of_int (s0 + Z.of_nat (snd t)) : mword 64)) /\
    uM_bytes M (cmd + 8 + 8 * Z.of_nat (length toks)) 8
      (mword_of_int 0 : mword 64) /\
    uM_bytes M (cmd + 88 + 8 * Z.of_nat (length toks)) 8
      (mword_of_int 0 : mword 64).

  (* parseexec, parsepipe and parseline share ONE postcondition: the two
     upper levels delegate and then guard their own construction with a
     [peek] for `|', `&' or `;', all excluded by [sh_no_symbols].  So the
     contract is parameterised by the entry pc and the stack budget rather
     than written out three times. *)
  Definition wp_sh_parse_body (entry budget : Z)
      (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr s0 : Z) (bs : list (bv 8)) (off : nat)
      (toks : list (nat * nat)) :=
    forall (Hpre : sh_parse_pre M s0 bs sp0 budget)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 budget)
      (Hps : m !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a1_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Hcell : sh_ptr_cell M psaddr (s0 + Z.of_nat off) sp0)
      (Hbufc : sh_buf_clear s0 (Z.of_nat (length bs) + 1))
      (Hoff : (off <= length bs)%nat)
      (Htoks : sh_tokens bs off toks)
      (Hmax : (length toks < 10)%nat)                (* MAXARGS *)
      (* the heap is untouched: this is the run's single malloc.  BOTH
         windows are needed -- [freep == 0] alone is what sends malloc down
         the [morecore] path, but the rescan afterwards reads [base.s.size]
         as eight bytes, four of which are union padding no instruction
         writes. *)
      (Hfreep0  : sh_zeroed M SH_FREEP 0 8)
      (Hbasesz0 : sh_zeroed M (SH_BASE + 8) 0 8)
      (Hbssw : uv_wr pt M SH_FREEP 0x88)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    ubrk gbrk hbase -∗
    pc_is (mword_of_int entry) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)) (cmd : Z),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int cmd : mword 64)⌝ -∗
       ⌜cmd = hbase + 65536 - 16 * (sh_nunits SH_EXECCMD_SZ - 1)⌝ -∗
       ⌜uM_bytes M' cmd 4 (mword_of_int 1 : mword 32)⌝ -∗
       ⌜sh_execcmd_argv M' cmd s0 toks⌝ -∗
       (* WHERE THE PARSE LEFT [*ps].  Without this the contract says
          nothing about the cell it was handed, and every caller is stuck at
          its very next [peek]: [wp_sh_peek_body] wants
          [sh_ptr_cell M psaddr (s0 + Z.of_nat off) sp0], and [uM_only_in]
          gives only that the cell's BYTES still exist, never their value.
          It blocked parsepipe, parseline and parsecmd alike.
          The value is exact, not a weakening: on a buffer with no symbol
          bytes the parse always consumes to the end -- the arg loop exits
          on [sh_tokens bs off []], i.e. [off + sh_skipws (drop off bs) =
          length bs], and the [gettoken] that reported end-of-input has
          already advanced [*ps] there. *)
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)⌝ -∗
       ⌜uv_rd pt M' cmd SH_EXECCMD_SZ⌝ -∗
       (* THE conjunct that lets a caller carry anything across the parse:
          the heap (which the single malloc carves), the two allocator
          statics, the [ps] cell and the frame are disturbed, and NOTHING
          else -- so the text, the static tables and, with [sh_buf_clear],
          the command buffer all survive.  This was once written as
          [⌜uM_only ... \/ True⌝], which [right; exact I] discharges: a
          false economy that says nothing at all. *)
       ⌜uM_only_in M M' [sh_win hbase 65536; sh_win SH_FREEP 8;
                         sh_win SH_BASE 16; sh_win (psaddr) (8);
                         sh_win (uint sp0 - budget) (budget)]⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  Definition wp_sh_parseexec_body := wp_sh_parse_body ShSyms.parseexec (128 + 112 + 64 + 16).
  Definition wp_sh_parsepipe_body := wp_sh_parse_body ShSyms.parsepipe (48 + 128 + 112 + 64 + 16).
  Definition wp_sh_parseline_body := wp_sh_parse_body ShSyms.parseline (48 + 48 + 128 + 112 + 64 + 16).

  (* nulterminate(cmd): for an EXEC cmd, writes a NUL at each eargv[i], so
     each token becomes a C string in place.  This is what turns the token
     BOUNDARIES parseexec recorded into the argv vector exec observes. *)
  Definition wp_sh_nulterminate_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (cmd s0 : Z) (bs : list (bv 8)) (off : nat)
      (toks : list (nat * nat)) :=
    forall (Hpre : sh_parse_pre M s0 bs sp0 32)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 32)
      (Hcmd : m !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      (Htype : uM_bytes M cmd 4 (mword_of_int 1 : mword 32))
      (Hargv : sh_execcmd_argv M cmd s0 toks)
      (Hrd : uv_rd pt M cmd SH_EXECCMD_SZ)
      (* THE NODE IS MALLOC'S, and saying so once settles three separate
         needs: [cmd <> 0] (with cmd = 0 the [c.beqz a0] at 0x7fa returns
         immediately and the [ustr_at] postcondition is FALSE for every
         non-final token), 8-alignment for the [lwu]/[c.ld] at 0x804/0x81a/
         0x822/0x82a, and node-vs-frame disjointness.  It is exactly the
         conjunct [wp_sh_parse_body] already produces. *)
      (Hnode : cmd = hbase + 65536 - 16 * (sh_nunits SH_EXECCMD_SZ - 1))
      (* ... and the buffer misses the node, or the NUL stores corrupt
         argv/eargv and [sh_execcmd_argv M' cmd s0 toks] is FALSE. *)
      (Hbufc : sh_buf_clear s0 (Z.of_nat (length bs) + 1))
      (Hmax : (length toks < 10)%nat)          (* MAXARGS; eargv[i] is at
                                                  cmd + 88 + 8i and must
                                                  stay inside the node *)
      (* NOT [Hsep].  That premise said only that each token is a non-empty
         range inside [bs], which ADMITS OVERLAPPING TOKENS: at
         [toks = [(0,5); (2,3)]] the loop writes a NUL at [s0+3] while the
         postcondition demands [bs !! 3] there and [sh_buf_ok] says every
         byte of [bs] is non-NUL.  The contract was FALSE, not merely
         unprovable.  [sh_tokens] is the real invariant, and it implies both
         [Hsep] and the separation the loop needs -- strictly, and only
         because [sh_no_symbols] forces a token to stop on whitespace, so
         the next scan skips at least one byte. *)
      (Hoff : (off <= length bs)%nat)
      (Htoks : sh_tokens bs off toks)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.nulterminate) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       (* every token is now a NUL-terminated string at its own address *)
       ⌜forall (i : nat) (t : nat * nat), toks !! i = Some t ->
          ustr_at M' (s0 + Z.of_nat (fst t)) (sh_tok_bytes bs t)⌝ -∗
       ⌜sh_execcmd_argv M' cmd s0 toks⌝ -∗
       (* it writes NULs into the BUFFER, and spills into its own frame;
          the execcmd node and the image are untouched *)
       ⌜uM_only_in M M' [sh_win s0 (Z.of_nat (length bs) + 1);
                         sh_win (uint sp0 - 32) (32)]⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* parsecmd(s): strlen, parseline, a trailing peek, nulterminate.  Its
     postcondition is exactly what [runcmd] needs and what the protocol's
     exec arm will observe -- [uexec_args] at (argv[0], &argv[0]). *)
  Definition wp_sh_parsecmd_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s0 : Z) (bs : list (bv 8))
      (toks : list (nat * nat)) :=
    forall (Hpre : sh_parse_pre M s0 bs sp0 (64 + 48 + 48 + 128 + 112 + 64 + 16))
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (64 + 48 + 48 + 128 + 112 + 64 + 16))
      (Hs : m !!! Regidx a0_idx = (mword_of_int s0 : mword 64))
      (Hbufc : sh_buf_clear s0 (Z.of_nat (length bs) + 1))
      (Htoks : sh_tokens bs 0%nat toks)
      (Hne : (0 < length toks < 10)%nat)
      (Hlen : Z.of_nat (length bs) < 2 ^ 31)
      (Hfreep0  : sh_zeroed M SH_FREEP 0 8)
      (Hbasesz0 : sh_zeroed M (SH_BASE + 8) 0 8)
      (Hbssw : uv_wr pt M SH_FREEP 0x88)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    ubrk gbrk hbase -∗
    pc_is (mword_of_int ShSyms.parsecmd) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)) (cmd p0 : Z),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int cmd : mword 64)⌝ -∗
       ⌜cmd = hbase + 65536 - 16 * (sh_nunits SH_EXECCMD_SZ - 1)⌝ -∗
       ⌜uM_bytes M' cmd 4 (mword_of_int 1 : mword 32)⌝ -∗
       ⌜uM_bytes M' (cmd + 8) 8 (mword_of_int p0 : mword 64)⌝ -∗
       ⌜p0 <> 0⌝ -∗
       (* THE handoff to runcmd, and thence to the exec arm -- in the
          BOUNDED form (USpecSh.v §0c).  [uexec_args] alone cannot be
          carried across runcmd's prologue, because its string pointers are
          existential; parsecmd CAN prove the bounded form, because it
          knows where every string is (element [i] is at [s0 + fst t]). *)
       ⌜sh_exec_below M' p0 (cmd + 8)
           (sh_tok_bytes bs (default (0%nat, 0%nat) (toks !! 0%nat)))
           (sh_tok_bytes bs <$> toks) (hbase + hlen)⌝ -∗
       ⌜uv_rd pt M' cmd SH_EXECCMD_SZ⌝ -∗
       (* and what [main] needs to keep: the text and the static tables. *)
       ⌜uM_only_in M M' [sh_win hbase 65536; sh_win SH_FREEP 8;
                         sh_win SH_BASE 16;
                         sh_win s0 (Z.of_nat (length bs) + 1);
                         sh_win (uint sp0 - (64 + 48 + 48 + 128 + 112 + 64 + 16))
                                (64 + 48 + 48 + 128 + 112 + 64 + 16)]⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

End USpecShParse.
