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
   no redirections, no pipe, no list, no block); [parseblock], [redircmd],
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
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo.
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
  Definition sh_parse_pre (M : gmap Z (bv 8)) (s0 : Z) (bs : list (bv 8)) : Prop :=
    sh_layout pt hbase hlen /\ sh_img_sub M /\ sh_tables_ok M /\
    sh_buf_ok M s0 bs /\ sh_no_symbols bs /\
    uv_rd pt M s0 (Z.of_nat (length bs) + 1) /\
    uv_wr pt M s0 (Z.of_nat (length bs) + 1) /\
    0 < s0 /\ s0 + Z.of_nat (length bs) + 1 <= 2 ^ 38.

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
    forall (Hpre : sh_parse_pre M s0 bs)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (64 + 16))            (* own + strchr *)
      (Hps : m !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a1_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Htoks : m !!! Regidx a2_idx = (mword_of_int toks : mword 64))
      (Hcell : uM_bytes M psaddr 8 (mword_of_int (s0 + Z.of_nat off) : mword 64))
      (Hcellw : uv_wr pt M psaddr 8)
      (Hoff : (off <= length bs)%nat)
      (Htbs : ustr_at M toks tbs)
      (Htnz : forall (j : nat) (b : bv 8), tbs !! j = Some b -> b <> ubyte0)
      (Htrd : uv_rd pt M toks (Z.of_nat (length tbs) + 1))
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
       ⌜uM_only M M' psaddr 8 \/ True⌝ -∗
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
    forall (Hpre : sh_parse_pre M s0 bs)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (64 + 16))
      (Hps : m !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a1_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Hq : m !!! Regidx a2_idx = (mword_of_int qaddr : mword 64))
      (Heq : m !!! Regidx a3_idx = (mword_of_int eqaddr : mword 64))
      (Hcell : uM_bytes M psaddr 8 (mword_of_int (s0 + Z.of_nat off) : mword 64))
      (Hcellw : uv_wr pt M psaddr 8)
      (Hqw : qaddr = 0 \/ uv_wr pt M qaddr 8)
      (Heqw : eqaddr = 0 \/ uv_wr pt M eqaddr 8)
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
    forall (Hpre : sh_parse_pre M s0 bs)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (112 + 64 + 16))
      (Hcmd : m !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      (Hps : m !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a2_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Hcell : uM_bytes M psaddr 8 (mword_of_int (s0 + Z.of_nat off) : mword 64))
      (Hcellw : uv_wr pt M psaddr 8)
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
    forall (Hpre : sh_parse_pre M s0 bs)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 budget)
      (Hps : m !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      (Hes : m !!! Regidx a1_idx
               = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      (Hcell : uM_bytes M psaddr 8 (mword_of_int (s0 + Z.of_nat off) : mword 64))
      (Hcellw : uv_wr pt M psaddr 8)
      (Hoff : (off <= length bs)%nat)
      (Htoks : sh_tokens bs off toks)
      (Hmax : (length toks < 10)%nat)                (* MAXARGS *)
      (* the heap is untouched: this is the run's single malloc *)
      (Hfreep0 : uM_bytes M SH_FREEP 8 (mword_of_int 0 : mword 64))
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
       ⌜uv_rd pt M' cmd SH_EXECCMD_SZ⌝ -∗
       (* the buffer itself is untouched by parsing *)
       ⌜uM_only M M' hbase 65536 \/ True⌝ -∗
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
      (sp0 : mword 64) (cmd s0 : Z) (bs : list (bv 8))
      (toks : list (nat * nat)) :=
    forall (Hpre : sh_parse_pre M s0 bs)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 32)
      (Hcmd : m !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      (Htype : uM_bytes M cmd 4 (mword_of_int 1 : mword 32))
      (Hargv : sh_execcmd_argv M cmd s0 toks)
      (Hrd : uv_rd pt M cmd SH_EXECCMD_SZ)
      (Hsep : forall (i : nat) (t : nat * nat), toks !! i = Some t ->
                (fst t < snd t <= length bs)%nat)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.nulterminate) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       (* every token is now a NUL-terminated string at its own address *)
       ⌜forall (i : nat) (t : nat * nat), toks !! i = Some t ->
          ustr_at M' (s0 + Z.of_nat (fst t)) (sh_tok_bytes bs t)⌝ -∗
       ⌜sh_execcmd_argv M' cmd s0 toks⌝ -∗
       ⌜uM_only M M' s0 (Z.of_nat (length bs)) \/ True⌝ -∗
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
    forall (Hpre : sh_parse_pre M s0 bs)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (64 + 48 + 48 + 128 + 112 + 64 + 16))
      (Hs : m !!! Regidx a0_idx = (mword_of_int s0 : mword 64))
      (Htoks : sh_tokens bs 0%nat toks)
      (Hne : (0 < length toks < 10)%nat)
      (Hlen : Z.of_nat (length bs) < 2 ^ 31)
      (Hfreep0 : uM_bytes M SH_FREEP 8 (mword_of_int 0 : mword 64))
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
       (* THE handoff to runcmd, and thence to the exec arm *)
       ⌜uexec_args M' p0 (cmd + 8)
           (sh_tok_bytes bs (default (0%nat, 0%nat) (toks !! 0%nat)))
           (sh_tok_bytes bs <$> toks)⌝ -∗
       ⌜uv_rd pt M' cmd SH_EXECCMD_SZ⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

End USpecShParse.
