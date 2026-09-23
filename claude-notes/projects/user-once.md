# Worklist: user-once — the parser as a refinement, `fd_stream`, the program-generic exec

Design of record: [`../design/user-once.md`](../design/user-once.md)
(PROPOSAL 2026-09-23; awaiting the owner's ruling).  Nothing built yet.
Sits UNDER [`app-both.md`](app-both.md): A and C are independent of it, B's
console instance waits for its M3.

## Rules

- As app-both's: every landing keeps the three theorems closed and the four
  audits unmoved (system 13, tree 13, file 14, pipe 14); a landed statement
  a consumer computes on is recovered by conversion or a one-line
  corollary, never restated; whole-tree gate before every landing.
- A touches only `UkSh*` files, C only the `USh*Pay`/`UShEcho`/`UShCat`/
  `UkShEcho`/`UkShCat` files — disjoint from app-both's M2c/M3 files, so
  the two campaigns do not race.  B1 touches `UEcho*`/`UCat*`.
- Every refinement lemma is stated with the reference's equation as its
  ONLY shape premise; a lemma that needs a per-shape fact beside it is the
  design being wrong, not a premise to add.

## A. The parser

- [ ] **A1 `RefParse.v`** (pure; after `UkShParse`'s vocabulary or
  replacing it): `ref_skipws`, `ref_gettoken`, `ref_peek`,
  `ref_parseredirs`, `ref_parseexec`, `ref_parsepipe`, `ref_parseline`,
  `ref_parsecmd`, `ref_nulcut`, `ushp_cat`, `ushp_room`, `ushp_nodes`;
  the bridge lemmas (`ushp_tokens ∧ ushp_no_symbols ⟺ ref_parseexec = Some
  (UshpExec toks, _)`, the `ushs_toks` one at the redirect, the pipe's
  left command); the three line-shape facts on `wl_line`; anti-vacuity by
  `vm_compute` on the three literal lines.  Exit: `UkShParseSym`'s and
  `UkShPipeLex`'s pure models are corollaries.
- [ ] **A2a** `wp_ref_gettoken`, `wp_ref_peek` (re-statements of
  `UkShParseTok`/`UkShParseLex`'s at the reference; `UkShPipeTok.
  wp_kshp_gettoken_syms` and `UkShRedirGtk` fold in as the symbol cases).
- [ ] **A2b** `wp_ref_parseredirs` (induction on the redirects consumed;
  `wp_kshp_parseredirs_ns`/`_gtn`/`_miss` are its cases).
- [ ] **A2c** `wp_ref_parseexec` (the token-list induction; the turn hands
  back REDIR + exec node as `UkShRedirEx` does; `ushp_room`/`ushp_nodes`
  replace the per-shape constants).  MEASURE against `UkShParseExec`'s
  1 min 52 s — the frame's `big_sepL` cost is the same, the statement is
  not; if the generic statement is slower, split as `UkShParse` was.
- [ ] **A2d** `wp_ref_parsepipe`/`parseline`/`parsecmd`/`nulterminate`;
  the parser theorem at `ref_parsecmd … = Some t ∧ ushp_cat t`.  Exit:
  `wp_kshp_parser` is the symbol-free corollary.
- [ ] **A3** the consumers: `ushf_child_law_at`'s `Lp` at `ref_parsecmd
  … = Some t` (SLOT-WS paid); `UkShRedirBody`/`UkShRedirChild`/
  `UkShPipeRound`'s children at the general theorem; DELETE `UkShRedir
  {Lex,Tok,Pr,Pc,Ex,Pex,Cm,Cmd,Gtk,Nul,Seam,Paid,Line,Ans}` and `UkShPipe
  {Lex,Tok,Pr,Ex,Ex2,Pex,Cm,Cmd,Parse,Right,Seam,Paid}`.  Exit: three
  theorems closed, audits unmoved, ~30k lines gone.

## C. The program-generic exec (alongside A2)

- [ ] **C1** `image_geom E frame` (from `UShEcho` §1-§2); `UShEcho`'s and
  `UShCat`'s rows as instances.
- [ ] **C2** `cmd_spec` and `sh_exec_arm C` (from `UkShEcho`; the three
  differences `UkShCat.v`'s header lists are the fields); echo's and cat's
  arms as instances; `cat_line_premises_absurd` becomes the note on why
  `line_ok` is not a field.
- [ ] **C3** `exec_sup P S` (from `UShEchoPay`); `UShEchoPipePay`,
  `UShRedirPay`, `UShCatPay` as instances.  Exit: one supply lemma, four
  one-line instances.

## B. `fd_stream`

- [ ] **B1** the record (`UkFdStream.v`, after `UkRun`); the INODE
  instance (`Hold p`, `kcat_r_of_deed_at`, `ef_pay`'s `uoff` + deed) and
  the PIPE instance (`pcat_hold`, `pipe_rpay_of_inv`/`pipe_wpay_of_inv`,
  `ro_shot` as `fs_shut`); `echo_entry S`; `UEchoFile`/`UEchoPipe` as
  instances.
- [ ] **B2** (after app-both M3) the CONSOLE instance over `GenOut`'s
  chain (the block-first byte is the instance's law); `UEchoOut` as an
  instance; `cat_round Sin Sout`; `UCatKernel`/`UCatPipe`/
  `UShPipeCatRound` as instances.  Exit: one echo entry, one cat round,
  three instance files each.

## RESUME HERE

Not started.  First: the owner's ruling on the design (route, order, and
whether A starts before app-both's M2c lands — the files are disjoint, so
it can).
