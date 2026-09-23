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

- [x] **A1 `RefParse.v`** (landed on branch `user-once/A`, `eee474d4c`; the
  bridge file `RefParseBridge.v` is stated and being proved) -- (pure; after `UkShParse`'s vocabulary or
  replacing it): `ref_skipws`, `ref_gettoken`, `ref_peek`,
  `ref_parseredirs`, `ref_parseexec`, `ref_parsepipe`, `ref_parseline`,
  `ref_parsecmd`, `ref_nulcut`, `ushp_cat`, `ushp_room`, `ushp_nodes`;
  the bridge lemmas (`ushp_tokens ∧ ushp_no_symbols ⟺ ref_parseexec = Some
  (UshpExec toks, _)`, the `ushs_toks` one at the redirect, the pipe's
  left command); the three line-shape facts on `wl_line`; anti-vacuity by
  `vm_compute` on the three literal lines.  Exit: `UkShParseSym`'s and
  `UkShPipeLex`'s pure models are corollaries.
- [x] **A2a** `wp_ref_gettoken`, `wp_ref_peek` -- LANDED (`iris/UkShGettoken.v`,
  `iris/RefParseSym.v`; `UkShRedirTok.v` deleted, `UkShRedirGtk.v`/`UkShPipeTok.v`
  reduced to one-line corollaries; net -540 lines; the general file compiles in
  the time of one of the three it replaces).  As read off the tree
  (2026-09-23): the three gettoken walks (`UkShParseTok.wp_kshp_gettoken`
  under `ushp_no_symbols`, `UkShRedirGtk.wp_kshp_gettoken_sym` under
  `ushs_gt_ok`, `UkShPipeTok.wp_kshp_gettoken_syms` under `ushq_sym_ok`)
  are ONE statement with the premise and the three pure functions
  (`ushp_/ushs_gettok_{res,end,fin}`) changed, and each is the same full
  walk over a different DISPATCH lemma for the switch
  (`wp_kshp_gtk_disp` / `_disp_ns` + `UkShRedirTok.wp_kshp_gtk_disp_gt` /
  `_disp_bar` + `_disp_sym`).  `wp_kshp_peek` is already general (no shape
  premise; result `ushp_peek_res`).  So A2a is: (i) the symbol scope
  `ushq_sym_ok` and `ushq_bar` move down to `RefParse` (as
  `ref_sym_scope`); (ii) the pure bridge `ref_gettoken len f off =
  (ushs_gettok_res, k, ushs_gettok_end, ushs_gettok_fin)` at `k = off +
  skipws` under `ref_sym_scope ∧ ref_nonnul`, and `ref_peek` vs
  `ushp_peek_res`; (iii) the arm dispatch lemmas move into `UkShParseTok`
  and ONE dispatch over `ref_sym_scope` replaces the four; (iv)
  `wp_ref_gettoken` stated at `let '(ret,q,e,fin) := ref_gettoken len f
  off in …` with `ref_nonnul` READ OFF `ustr`'s pure conjunct (no new
  premise), proved as the widest landed walk rewritten; `wp_kshp_gettoken`
  kept as its corollary (consumers: `UkShParseExec`, `UkShParseRedir`);
  `UkShRedirTok`/`UkShRedirGtk`/`UkShPipeTok` reduced to corollaries until
  A3 deletes them with their consumers.
- [x] **A2b** `wp_ref_parseredirs` -- LANDED (`iris/UkShRedirs.v`, placed BEFORE
  `UkShRedirPr` so gtn/ns are corollaries in place; `UkShRedirPr.v` 2542->352,
  `UkShPipePr.v` 683->129 lines; net -740; the general file compiles in half
  the time of the two it replaces).  AS LANDED: the turn's extras (symbol
  table, `Pex`, scope, eight words) are GUARDED by `rs <> []` /
  `ushp_redirs_res rs` so the zero-turn landed statements come back exact;
  `wp_ref_parseredirs_full` is the unconditional shape parseexec consumes;
  `Forall (mode = gt /\ fd = 1)` is derived from `ref_sym_scope`, not a
  premise; `ushp_malloc_chain` lives there until `UkShParse` is next edited.
  As read off the tree (2026-09-23): four
  walks -- `UkShParseRedir.wp_kshp_parseredirs` (zero turns under
  `ushp_no_symbols`), `UkShRedirPr.wp_kshp_parseredirs_ns` (zero turns,
  the byte at the cursor no symbol), `UkShPipePr.wp_kshp_parseredirs_miss`
  (zero turns at the WEAKEST premise: peek's table at `ushp_T_redir` does
  not contain the byte -- this is the general miss), `UkShRedirPr.
  wp_kshp_parseredirs_gtn` (ONE turn on `ushs_redir`, 1,600 lines: the
  '>' gettoken, the file-name gettoken, the switch, `redircmd`, the second
  peek).  The general lemma is by induction on the redirect list
  `ref_redirs len f n off [] = Some (rs, fin)`: the miss case is `_miss`,
  the turn case is `_gtn`'s body at an arbitrary continuation (its second
  peek IS the induction hypothesis), and the answer is the node chain
  `ushp_redir_node` folded over `rs` around `cmd` (`ushp_redir_close`
  closes each).  THE ALLOCATOR: today each walk threads its allocations as
  a chain of section hypotheses (`UM0 UM1 UM2`, `ushp_malloc_ok0/1` in
  `UkShRedirPex`); a walk over an arbitrary tree needs the chain as a
  PREDICATE -- `ushp_malloc_chain k UM UM'` (`k` `ushp_malloc_ty` steps;
  `ushp_malloc_ty_le 168` is what makes it close, `UkShMalloc` §7) -- at
  `k = length rs` here and `k = ushp_nodes t` at the parser theorem.
  Define it in `UkShParse` beside `ushp_malloc_ty_le`.
- [x] **A2c** `wp_ref_pex_loop`, `wp_ref_parseexec` -- LANDED (`iris/UkShArgs.v`,
  2,983 lines, before `UkShRedirEx`; the five twins reduced to corollaries in
  place, statements byte-identical; net -4,800 lines; 44 s vs the 97 s of the
  five it replaces).  AS LANDED: `wp_ref_parseexec`'s answer is OPEN (the
  exec node + `ushp_redirs_at` chain, with `t = ref_wrap (UshpExec toks)
  rs` a pure fact) because `ushp_tree`'s REDIR case drops the `p+168`/`t+40`
  bounds the landed `_gt` statement carries, so no inverse of
  `ushp_redir_close` exists; `wp_ref_parseexec_tree` is the closed form.
  `ushp_cat t` is NOT a premise anywhere below nulterminate: under
  `ref_sym_scope` it is implied.  The exit round `wp_ref_pex_exit` and the
  loop guard their extras (`ushp_pex_gtk_in/out stop`, `ushp_pex_res rs`) as
  A2b did.  As read off the tree
  (2026-09-23): the argument loop is walked THREE times with the same
  register invariant (s0..s11 pinned; `ushp_exec_pre s0 p done`, the
  cursor cell at `cur`, the q/eq cells at `fp-120`/`fp-128`; entry 0x622,
  exit 0x662) -- `UkShParseExec.wp_kshp_pex_loop` (`ushp_tokens`, ends at
  `len`, s1 = p), `UkShRedirEx.wp_kshp_pex_loop_gt` (`ushs_toks` at the
  '>', ends at `len` with s1 = the REDIR node `t` over `p`, one
  allocation), `UkShPipeEx2.wp_kshp_pex_loop_bar` (`ushs_toks` at the '|',
  ends AT the '|' with s1 = p) -- plus two exit rounds
  (`UkShRedirEx.wp_kshp_pex_end`: cursor at `len`; `UkShPipeEx.
  wp_kshp_pex_bar`: the byte is '|') and three whole-function forms
  (`wp_kshp_parseexec`, `_gt` with `UM0 UM1 UM2`, `_bar` with `UM0 UM1`).
  The general loop is stated at `ref_args len f n cur done rs0 = Some
  (toks, rs, fin)`: invariant `ushp_exec_pre s0 p done ∗ ushp_redirs_at s0
  t0 p rs0` with s1 = `t0`; post `∀ t, ushp_exec_pre s0 p toks ∗
  ushp_redirs_at s0 t p rs`, cursor `fin`, s1 = `t`, `ushp_malloc_chain
  (length rs - length rs0) UM UM'`; premise `ref_sym_scope`.  Both exits
  come out of the equation (a stop-set byte: `_bar`'s round; NUL: `_end`'s
  round), and each turn is `ref_args_step` (RefParseBridge) -- the
  gettoken via `wp_ref_gettoken`, the two stores, the `parseredirs` via
  A2b's `wp_ref_parseredirs` at the redirects it consumes.  The whole
  function `wp_ref_parseexec` at `ref_parseexec len f n off = Some (t,
  fin) ∧ ushp_cat t`: the '(' peek misses (from `ushp_cat`), `execcmd`,
  the leading `parseredirs` (A2b), the loop, then the WRAP: `ushp_tree s0
  root t` by `ushp_exec_pre_at` and `ushp_redir_close` folded along
  `ref_wrap`; allocations `ushp_malloc_chain (ushp_nodes t) UM UM'`.  The
  eight landed lemmas are corollaries.  MEASURE against `UkShParseExec`'s
  1 min 52 s: the frame's `big_sepL` cost is the same and the statement
  is not; if slower, split the loop turn from the loop as `UkShParse` was
  split.
- [ ] **A2d** `wp_ref_parsepipe`/`parseline`/`parsecmd`/`nulterminate`;
  the parser theorem.  READ OFF THE TREE (2026-09-23): the top of the
  parser is walked three times -- `UkShParseCmd` (parsepipe, parseline,
  nulterminate, parsecmd, `wp_kshp_parser`; `UMalloc UMalloc'`),
  `UkShRedirCm` + `UkShRedirPc` + `UkShRedirNul` (`_gt` of each, `UM0..UM2`,
  `wp_kshp_parser_redir`), `UkShPipeCm` + `UkShPipeCmd` + `UkShPipeParse` +
  `UkShPipeRight` (`_bar` of each, `UM0..UM3`, `wp_kshp_parser_pipe`).  The
  only real TURN above parseexec is parsepipe's (`UkShPipeCm.
  wp_kshp_parsepipe_bar`: the '|' gettoken, `pipecmd` -- one allocation,
  `UkShPipeCmd` -- and the recursive parsepipe on the SUFFIX, which
  `UkShPipeRight.wp_kshp_parsepipe_right` feeds the landed symbol-free
  walk through `ustr_split` + `ushp_exec_at_rebase`); parseline never
  turns in any landed shape (`&`/`;` are out of `ushp_cat`), parsecmd is
  parseline + the leftovers peek + nulterminate, and nulterminate is a
  RECURSION over the tree (`wp_kshp_nul_loop` at EXEC, `_redir` and
  `_pipe` each one level, the jump-table row per constructor
  `ushp_jrow_exec/redir/pipe`).  General statements: `wp_ref_parsepipe` at
  `ref_parsepipe len f n i = Some (t, fin)` by induction on `t`'s pipe
  spine (the '|' turn recurses at the suffix -- state the recursive call at
  the reference on the SAME `(len, f)` with cursor `s2`, not on a re-based
  string: `ref_parsepipe` is already cursor-indexed, so `ustr_split` and
  `ushp_exec_at_rebase` become unnecessary -- check that `wp_ref_parseexec`
  at cursor `s2` is what the recursive call needs); `wp_ref_parseline` at
  `ref_parseline` (the `&`/`;` peeks miss from `ushp_cat`); `wp_ref_
  nulterminate` by induction on `t` with `ref_nulcut t` the cut (the three
  jump-table rows are its three cases; `ushp_nulfold` generalised to a fold
  over `ref_nulcut`); `wp_ref_parsecmd` = THE PARSER THEOREM at
  `ref_parsecmd len f = Some t ∧ ushp_cat t` answering `ushp_tree s0 p t`,
  the line cut at `ref_nulcut t`, `ushp_malloc_chain (ushp_nodes t) UM
  UM'`, room `ushp_room t`.  Corollaries: `wp_kshp_parser`,
  `wp_kshp_parser_redir`, `wp_kshp_parser_pipe` exact; the `_gt`/`_bar`
  twins reduced in place; `UkShPipeRight` retired (its finding -- the
  suffix IS a `ustr` -- is what the cursor-indexed reference makes
  automatic).  The seams (`UkShRedirSeam`, `UkShPipeSeam`: `ushp_tree` to
  `UkShRun.ush_cmd`, and the child walks living in `UkShRedirSeam`) are
  A3's.  Exit: `wp_kshp_parser` is the symbol-free corollary.
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

## RESUME HERE (2026-09-23)

RULED by the owner: A starts now.  Branch `user-once/A` off `main` at
`08033db62`.  A1's `RefParse.v` landed there (`eee474d4c`, seven
`vm_compute` demos); `RefParseBridge.v` (18 statements: the fuel
monotonicity, the symbol-free bridge both ways, the redirect and pipe
bridges, the three line-shape facts on `ush_line_is`/`ushs_line_is`/
`ushq_line_is`) is stated and elaborates; its proofs are with a subagent.
A1 and A2a-c are on `main`.  NEXT: A2d as read off above (branch `user-once/A2d`).
