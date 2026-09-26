# Worklist: seccomp -- `seccomp x` in the union theorem

Design of record: [`../design/seccomp.md`](../design/seccomp.md) (§9 and
§10 are the owner's rulings and WIN over §3-§7 where they differ).
Opened 2026-09-25.  The bump itself (checkpoint 1) is DONE and archived in
[`../completed/xv6-bump-7b2c1b1.md`](../completed/xv6-bump-7b2c1b1.md).

## RESUME HERE  (written for a FRESH agent; the session that started this may have died)

CHECKPOINT 1 LANDED (2026-09-25): `main` = `origin/main` = f347775c7 (+ the
owner's notes commits) is the kernel bump to upstream 7b2c1b1 with the
mask in the contracts (design §4) merged with the filenames W2/W3/W4
work; whole tree green on the VM, audits system 13 / union 14 / tree 13
textually at the baseline, `check-decode` clean, `gen-ucode` unchanged,
`vtest-check-ci` 77 cases, `xv6-rev-check` ok.  The seccomp binary is
dumped and catalogued (`UCodeSeccomp.v`, inum 23) but NOT verified and
not in the union app.

CHECKPOINT 2 IS THE THEOREM, cut as S0 -> S1 || S2 -> S3 -> S4 (below).
Lanes run as Opus subagents in their own worktrees under
`/shared/xv6iris-3-lanes/`, each with a VM mirror
`/mnt/rocq/trees/_shared_xv6iris-3-lanes_<name>` seeded by copying an
idle built mirror of its base (`cp -a /mnt/rocq/trees/_shared_… …`),
then `run-on-gcp -q bash -c '<vmbuild.sh's commands at the mirror path>'`
FROM the worktree.  Every lane: commit by explicit path (`WIP:` prefix
while red), no `Admitted`, `Proof using` everywhere, the three audits
textually at the baseline before it reports, one status paragraph under
its own heading in THIS file (on a rebase conflict in this file keep
main's text and re-add your paragraph).

WHERE THINGS ARE (trust `git log`/`git worktree list` over this text):
- `/shared/xv6iris-3`: `secc/bump` = main plus the owner's notes commits.
  The owner (top-level agent) works here: design, briefs, merges to main.
- `secc/model`, worktree `secc-model`: lane M, the pure model (§3, §9),
  DONE and rebased onto main: tip 79c00bfef, green, audits at the
  baseline.  Owner's answer to its question: the words after `seccomp`
  ALSO accept file-name words (`fn_wf`, so `seccomp rm a.txt` is a
  line); S4 widens `secc_ok`.
- `secc/s0`, worktree `secc-s0`: lane S0 (below), in flight, off main.
- `secc/s1`, worktree `secc-s1`: lane S1 (below), in flight, off main;
  merges `secc/s0` for its minter.
- `secc/s2`, worktree `secc-s2`: lane S2 (below), off 79c00bfef; merges
  `secc/s0` for its items 1, 5, 6.
- Then: S3 off S1 + S2 (+ the model); S4 off S3.
- Origin: every `secc/*` branch is pushed as a safety copy when it
  reports; `main` moves only at green checkpoints.

## Lane M -- the pure model (design §3, §9)

Landed at the old pin (e8728827e), rebased onto W3, W4 and main
(79c00bfef): `LSecc`, `US`, the line-indexed `lm_merge`, the knob `ulm
adm adm_s` / `ulmG := ulm adm_u_g adm_s_off`, `RSExec`, the knob-generic
decider, the demos (`echo hi > a.txt`, `seccomp rm a`, power cycle, `cat
a.txt` prints `hi`; `demo_secc_nodot`; `demo_secc_d4`).  Its detailed
status (conflicts at each rebase, deviations from §3 -- now accepted as
§9) is in the `secc/model` branch's copy of this file.

## S0 -- the wild credential's plumbing (design §6, §9, §10.1-10.2)

Branch `secc/s0` off main.  Small, cross-cutting, ahead of S1 and S2.

1. `RiscvPtsto.app_iface` += `ai_wild : nat -> iProp Σ` (persistent,
   timeless) and `ai_wild_lic : forall k, ai_wild k ⊢ □ ∀ h H ev,
   ⌜wild_ev ev⌝ -∗ ⌜cons_hist_ok H⌝ -∗ ⌜cons_ev_ok H ev⌝ -∗ ai_cons k h H
   ==∗ ai_cons k h (cons_step H ev)` with `wild_ev` true at `EvOut`/`EvRead`
   only; `riscv_wild := ai_wild riscvF_app_iface`.  The three
   `MkAppIface` instances at `fun _ => False`.
2. `WpUart.cons_licence_at k` (same statement), `cons_licence_at_of_licence`,
   `cons_licence_at_of_wild`; `out_link_of_licence_at`, `cons_read_pay_triv_at`
   as the general lemmas with the old names as corollaries.
3. `AppInv.app_rdcred := app_sup ∨ riscv_wild (S gen_id)` under a `GenId`
   binder; every `cons_dirty_cred app_sup` / `cons_acc _ app_sup _` site
   (ProofMain's escrow allocation, SpecFileread, SpecSysRead,
   ProofFileread, FsAbsInvFire, UkReadCons, UShLine) at `app_rdcred`; the
   generic reader pays `iLeft`.
4. The shell tier keeps `ush_rd_ret`'s two arms; the read lemmas that turn
   the dirty credential into `lk_T L` gain the premise `(⊢ riscv_wild (S
   gen_id) -∗ lk_T L)` (or the one premise `(⊢ app_rdcred -∗ lk_T L)`),
   discharged at the union and at echo from the `False` instance.  S2
   replaces that discharge by `iRight` of `lk_T := UT ∨ secc_tok`.
5. Green; audits 13/14/13; status paragraph; report.

STATUS (lane S0, `secc/s0`): landed, tree green, audits 13/14/13
textually the baseline.  `ConsLog.wild_ev`; `ai_wild`/`ai_wild_lic`
under `⌜wild_ev ev⌝ -∗ ⌜cons_ev_ok H ev⌝` (no `cons_hist_ok`, owner's
ruling) with every instance at `RiscvPtsto.wild_none`;
`WpUart.cons_licence_at` (+ `_of_licence`, `_of_wild`),
`out_link_of_licence_at` and `cons_read_pay_triv_at` (old names are
corollaries).  Item 4 took the SEPARATE premise `(⊢ riscv_wild (S gen_id)
-∗ lk_T L)` on the eight `UShLine` read lemmas, discharged in
`UInitUnionCC.union_cc_holds` from `Hwild : riscv_wild = wild_none`
(read off `union_ifc` in `UInitUnionBoot`); echo has no discharge site in
the tree (its `UShLine` instances only pass the premise on).

## S1 -- the universe: the generic slot without the taint (design §5, §9)

Branch `secc/s1` off main; merges `secc/s0` before item 5.  New file
`iris/UexecSecc.v` after `UexecExecMint.v`.  Nothing about the claim,
the model or sh is touched.

1. Pure: `secc_B := [6;15;17;18;19;20]`, `secc_masked m`,
   `usys_eff_masked`, `secc_masked_and`.
2. `wild_pipe γp := inv seccN (∃ s, pipe_qfrag (pn_queue γp) s)`;
   `secc_row` (inode `False`, pipe `wild_pipe`, device/closed `True`);
   `secc_key W := ⌜secc_masked (uvis_secc W)⌝ ∗ [∗ list] st ∈ uvis_fd W,
   secc_row st`; preservation along `usys_fd_ok` (pipe adds two pipe
   rows, dup copies, close clears, the rest keep), `usys_secc_ok`, the
   fork child's key, an exec'd key.
3. The links out of `wild_pipe` at the trivial protocol (`pipe_clink`,
   `pipe_rchain`, `pipe_wchain`; `PipeProto.pipe_reg_of_inv`'s mould);
   the deposit rows the universe pays out of them: `fileread_in` /
   `filewrite_in` / `fileclose_cpay` at a pipe row; console rows via the
   era licence and `app_rdcred`; inode rows refuted.
4. `ExecEntry.image_entry_taint T Q X` GENERALISED to take `sts secc` and
   the pins `⌜uvis_fd W' = sts⌝ -∗ ⌜uvis_secc W' = secc⌝` (~25 sites
   ignore them).
5. `useccomp_mint : riscv_wild (S gen_id) -∗ □ uexec_wp -∗ □ (∀ W, □
   secc_key W -∗ my_pay (uvis_gen W) (fun _ => True) -∗ uslot W)` by Löb
   on `uexec_dep_F_of_supply` / `uslot_mint_all`'s mould: blocked numbers
   never reached (`usys_eff_masked`), read/write/close/exit from item 3,
   chdir from `fsabs_chdir_pre`, exec by the taint-shaped walk at `T :=
   riscv_wild` with the generalised entry answered from the Löb
   hypothesis, fork's child from the hypothesis, pipe's `wild_pipe`
   allocated under the slot's WP, the kill arm at `ukill_cred_at`'s right
   disjunct (`kill_owed` free at the trivial payload).
6. Green; audits unchanged; `Print Assumptions useccomp_mint` at the
   baseline; status paragraph; report.

STATUS (lane S1, `secc/s1`): items 1-6 landed, tree green (VM log
s1-r4: EXIT=0, no `Error`, second pass 0 compiles), audits system 13 /
union 14 / tree 13 textually the baseline, `Print Assumptions
UexecSecc.useccomp_mint` = `functional_extensionality_dep`,
`resv_matches`, `resv_is_valid`.  `iris/UexecSecc.v`: `secc_B`,
`secc_masked`, `usys_eff_masked(_notin)`, `secc_masked_and`;
`wild_pipe`/`secc_row`/`secc_rows`/`secc_key` (persistent, NOT timeless --
`wild_pipe` is an invariant) with preservation along `usys_fd_ok` (every
number but open and pipe; pipe's two rows given `wild_pipe`; pipe's
failure arm), `usys_secc_ok`, fork's child key, exec's two pins; the
wild-pipe links (`wild_clink` hence `wild_reg`, `wild_rchain`,
`wild_wchain`) and the deposit rows; `secc_cons_pay` (the console rows),
paid by `secc_cons_pay_of_wild`; `useccomp_mint_of_cons` (the Löb, at
`secc_fam` = the point at the trivial payload) and `useccomp_mint`;
`useccomp_image_entry_taint` (the minter answers the generalised taint
entry at a table in the universe and a masked mask -- what S3's exec
hands `exec_bundle_of`).  Two deviations from the brief: the universe's
OWN exec deposit (`secc_sbundle_exec`) is the closed generic bundle
(`fsabs_exec_half` + `ax_hops_triv`, `xv6_sbundle_of_supply`'s exec
branch) with both slot wands from the recursion, not the taint-shaped
walk -- it needs no credential at all; and an entry carried where no key
is in scope is `∀ sts, image_entry_taint T sts secc_all Q X` (the U-tier
rules) or `∀ sts secc, …` (sh's entry, which `image_entry_taint_all_elim`
turns back into the unpinned wand its generic slot is).

## S2 -- the claim's terminal arm (design §10; §6 where §10 is silent)

Branch `secc/s2` off lane M's tip 79c00bfef; merges `secc/s0` for items
1, 5, 6.  The knob stays OFF: `ush_line_union` is `False` at `LSecc`; the
transition (§10.4) is a lemma that fires only at an admitted `LSecc`.
Order: 2, 3, 4 first (they need nothing from S0), then merge S0 for 1,
5, 6, 7.

1. §10.1: `ep_secc` in `era_pins`, `era_full`, `secc_flag`, `secc_tok`
   (carrying `inp_lb v I0` and `cs_frozen_at v (nlines I0 - 1)`), the
   absurdity lemma; `ai_wild := secc_tok` at the union's `union_ifc`.
2. §10.4's generic-tier change: `GenOutHist.gin_pure` += `forall e, e ∈
   pops -> lm_disc M (le_hist e)`, maintained at `EvClose` from
   `garm_era`; the echo/pipe instances follow for free.
3. §10.3: `ucl` redefined under its name (`UT ∨ (UPIN ∗ secc_flag v 0 ∗
   peclV …) ∨ usecc`); `usecc` as listed; `union_era_split` at `secc_flag v
   0`; `ucl_taint`; every `ucl_*` lemma, `pblkU_ecl_holds`,
   `pwc_blkU_file*` re-proved with the third arm closed by REFUTING the
   presenter off the turn (the pure lemmas about `lm_proc_before` /
   `lm_proc_stream` this needs go in `LineModel.v` or a sibling; if one
   refutation is underivable, use §10.3's escape fallback and say so).
4. The read wrapper's TRANSITION (§10.4) and what the reader gets
   (`secc_tok`); `ucl_drain` at the third arm (§10.3 last bullet); the
   echo law at the third arm (refute `lm_disc U h` by D4, or `UT`).
5. `union_cons_lic` from `UT` unchanged; the wild licence from `secc_tok`
   (`ai_wild_lic` at the union: third arm closed under `EvOut`/`EvRead`,
   middle arm refuted by the flag, first arm rebuilt).
6. §10.5: `lk_T := UT ∨ secc_tok (S gen_id)` at the union's LinkRec and
   the families/lease that follow; `useccomp_shape`; `uWcu`'s fourth arm,
   `uWbf`'s wild arm; `uWcu_taint` at `T'`; the wild-arm cases of
   `uWcu_read` (vacuous through `cs_frozen_at_lb_absurd`), `uWcu_inp`,
   `uHwbl_u`, `ush_prompt_law_u`, `uHpanic`, `ush_kill_law_u`; the
   `ush_read_pay_era_at` premises discharged at `T'` (S0's `False`
   discharge removed).
7. `UInitUnionCC` / `UInitUnionBoot` / `UShUPipes` / `UkUnionEntries` /
   `UnionLinks` / `UShURound` follow `Hcons` and the new shapes; the
   knob-off proof of `union_adequacy_closed` unchanged in statement.
8. Green; audits 13/14/13; status paragraph; report every refutation
   lemma by name and any escape you had to take.

STATUS (lane S2, `secc/s2`, under design 10.10): items 1-8 landed, tree
green (VM log s2-f3: EXIT=0, no `Error`, second `make -n` pass 0
compiles), audits system 13 / union 14 / tree 13 textually the S1
baseline.  Item 2: `GenOutHist.gin_pure`'s last conjunct records `lm_disc
(le_hist e) /\ trace_shape (le_hist e) true` for every pop.  Pure lemmas
(`iris/GenOutWild.v`): `lm_wild`, `lm_d4_wild`, `lm_disc_wild_last`,
`lm_proc_before_pos`, `lm_blk_stage_inp`, `lm_pro_stage_inp`,
`lm_alts_pre_snoc_w`, `lm_good_out_wild`, `lm_rd_wild_stage`, the
`wild_prefix_*` helpers.  The claim (`iris/PipeOutW.v`, the union's
`UnionOut.ucl := pwclV … uwild`): `secc_flag`, `secc_tok`, `secc_tok_at`
(the token AT its line, with `lm_disc_input`), `wildV`, `pwclV`; the third
arm is REFUTED at every presenter: `pwclV_step_write_first`
(`lm_proc_before_pos`), `pwclV_step_write` (`lm_write_stage_byte`),
`pwclV_step_write_pro` (`lm_pro_stage_inp`), `pwclV_step_write_blk`
(`lm_blk_stage_inp` against the premise `WL line = false`),
`pwclV_open` (D4, `lm_disc_wild_last`), `pwclV_blk_file` /
`pwclV_ecl_holds` (`wild_cur_refute`: pext's whole `cur_half`),
`pwclV_blk_file_empty` / `pwclV_ecl_holds` (`wild_blk_refute`); the
middle arm by `secc_tok_flag0`.  NO ESCAPE: the block-first byte at the
wild line is refused by premise -- `pwclV_step_write_blk`,
`UnionOut.ucl_step_write_blk`, `UnionLinks.union_write_link_blk` take
`uwild (line) = false` first, `GenLinksLine.gl_blk` takes `⌜¬ gwild P I0⌝`
(new last field `gwild` of `gen_params`: `fun _ => False` at the file,
`uwild (lm_line_at U I) = true` at the union), and LinkRec's new
`lk_wild` gates `lk_prompt_dollar(_ban/_post/_line)`, `lk_blk_step`,
hence `lk_lpr_step`, `lk_panic_step`, with `(⌜¬ lk_wild I⌝ ∨ lk_T) -∗`
first.  CONSEQUENCE FOR S4: sh's round at an `LSecc` line must never
present a block-first byte; its prompt and diagnostics there go through
the licence (`union_write_link_wild`), as `uHpanic` / `ush_prompt_law_u`
do at the wild arm.  The transition is `pwclV_step_read` (receipt
`rd_retW`: `⌜rd_wild CH ws⌝ -∗ secc_tok_at k (snd <$> (dl ++ ws)) ∨ T`),
through `UnionLinks.uread_ret` and `UnionReadInst.uri_arms` into the
residue `urresw v I`'s new conjunct `⌜uwild_at I⌝ → usecc_tok_at (S
gen_id) I ∨ UT`.  `lk_T` stays `UT`; the era-pinned taint laws from the
T' attempt (`gl_taint` taking `PIN k v`, `gl_taint_at`, `rk_rd_taint` at
`S gen_id`, `GenLinksGl.gcl_gl_taint_at`) are green but UNUSED by the
token -- S4 must not build on them.  Reader side: `ai_rdwild` /
`riscv_rdwild` = `wild_none` at every instance, `app_rdcred := app_sup ∨
riscv_rdwild`; `UexecSecc`: `secc_B := [5;6;15;17;18;19;20]` (pending
the owner's mask decision), `secc_cons_pay` the write row only,
`secc_cons_rd_of_wild` deleted.  The shell tier
(`UShURoundDefs`): `useccomp_shape I := usecc_tok_at (S gen_id) I ∗
⌜uwild (ul I) = true⌝` (DEVIATION: the token is tied to the shape's own
line, which is what makes the read after it vacuous by `uterm_read_law`'s
argument); `uWcu`'s fourth arm, `uWbf`'s wild arm; the deed
`ush_deed_at` carries `⌜uwild (ul I) = false⌝` (the fact the gated laws
need, `ush_deed_nw` / `ush_pre_nw`); `uWcu_3` now returns the wild arm
too, `uWcu_3_nw` refutes it at a known line kind; the wild-arm cases:
`uWcu_read` (landing: `umid_wild`; vacuous after: `uwild_read_absurd`),
`uWcu_inp` / `uWbf_inp` (`ushape_inp`), `uHwbl_u`, `uHwbwc_u`,
`ush_prompt_law_u` and `uHpanic` (through the licence, via the new
generic `UShPanic.ksh_w1_of_step`); `ush_kill_law_u` unchanged (from
`UT`).  ONE KNOB-OFF DISCHARGE: `UInitUnionCC.union_wbn_to` (init's
banner reading of sh's exit payload) refutes `uWbf`'s wild arm by
`UShURoundDefs.uwild_disc_off` (no disciplined input ends in a seccomp
line while `adm_s_off`); S4 replaces it with init's licence path.  Not
done: 10.9's two-taint / tprompt sweep -- moot under 10.10 (`lk_T = UT`
still pays `sh_deps`).

STATUS (lane S2k, `secc/s2k`, design 10.12's KERNEL bullet): landed,
tree green, audits at the baseline.  The console read's marked
(credential) arm now carries where each delivered byte came from.  New
pure vocabulary in `ConsoleInv.v`: `cons_placed l lo d hs` (`length hs =
d` and every `j < d` has a position `p >= lo` with `hs !! j = Some h`,
`obs_ends_in Uart0 h b`, `l !! p = Some (h, b)`), with `cons_placed_0`,
`_of_window`, `_prefix`, `_snoc`.  Shapes: `SpecConsoleread`'s receipt
right arm is `cons_dirty_cred Wd ∗ ⌜cons_chain sl⌝ ∗ ⌜cons_placed sl cur d
hs⌝` (`sl` the receipt's own `cons_stored_lb` bound, `cur` the start it
reports); `SpecFileread.console_receipt`'s is the same at `app_rdcred`
(`console_receipt_of_dirty` takes the two facts); `UkReadCons.
uread_cons_ans`'s is `cons_dirty_cred app_rdcred ∗ ∃ sl, ucons_stored_lb
sl ∗ ⌜cons_chain sl⌝ ∗ ⌜cons_placed sl cur dd hs⌝`.  THE POSITION TIE:
`ConsoleInv.cons_out`'s marked disjunct is now `cons_dirty_cred Wd ∗
⌜cur = nrd⌝` -- the kernel always answered a holder at its own `nrd`,
but a holder's `Rd` could not learn it on that arm, so the placed facts
(at or after `cur`) would have been useless to it; with the tie a lease
holder's `Rd` can relay `cur = n` on the marked arm too (S4/union: this
is what `ush_rd_ret`'s right arm should keep).  Kernel side: `cr_racc` /
`cr_rout`'s tokenless arm and the holder's marked arm carry `∃ sl,
cons_stored_lb sl ∗ ⌜cons_chain sl⌝ ∗ ⌜cons_placed sl lo d hs⌝` (`lo = 0`
resp. `n0`); each pop places its byte at the cursor `cur >= nrd`
(`nrd = n0 + d` for the holder) and moves the bound to the ring's `st`.
NOT GIVEN: the positions are not promised to INCREASE in `j` -- the ring
keeps no monotone witness of its cursor across a release (it is a pure
existential in `cons_res`), so two pops separated by a sleep cannot be
compared; that would need a `mono_nat` for `cur` in `cons_res`.  The
holder does get `p_j >= n0 + j` per pop, but only `>= n0` is stated.
UShLine: pattern-only (`[#Hdirty _]` at the cons_out and receipt
disjuncts).

S2k FOLLOW-UP (the era of a placed byte, for S5b's
`GenOutWild.lm_placed_wild_undisc`): STOPPED -- the ring keeps NO
per-entry era.  `cons_res` (ConsoleInv.v) is not era-aware at all (its
section has no `GenId`); its entries are `(h, b)` under `cons_stored` /
`cons_pend` / `cons_chain` / `cons_below` / `cons_log_ok`, none naming
`obs_boots`.  `cons_logged` ties each entry to an entry of the log `L0`,
but the port invariant keeps the era of the log's TOP only
(`WpUart.cons_log_ins`, `uart_col_ok`'s `ht` clause).  Where the era IS,
closest to the receipt: (1) the uart's rx queue, per queued byte (the
receive column's `⌜obs_boots h = S gen_id⌝` row in `WpUart.v`), relayed
at the POP beside `riscv_rx_tag h`, in hand at consoleintr's push
(`ProofConsoleintr.v` ~823/1294/1573) and dropped when the byte is
filed into the ring; (2) the application's tag, minted at that same push
under the premise `obs_boots h = S gen_id` (`AppUnionRec.union_al_rx`;
the era survives `h ++ [ObsUartIn i b]` by `obs_boots_app` /
`obs_boots_io`, as at `WpUart.v:4073`) and ALREADY relayed by every
receipt arm, the dirty one included (`[∗ list] h ∈ hs, riscv_rx_tag h`).
The cheap route is (2): `UnionOut.utag` carries an era-keyed persistent
witness the reader compares with its own era (`ai_tag` is era-agnostic,
so a bare `⌜obs_boots h = S gen_id⌝` cannot be written in it).  The
kernel route is a new `cons_res` clause `⌜∀ p, p ∈ st ++ pd -> obs_boots
p.1 = S gen_id⌝`: `GenId` into ConsoleInv's section (every statement
naming `cons_res`/`is_conslock`/`console_inv` then needs an ambient era),
maintained by consoleintr's store arm, vacuous at the boot allocation,
carried by `cr_ghost`/`cr_racc` into `cons_placed`'s per-byte clause.

S2k ERA (the owner's ruling on the follow-up above, `secc/s2k2`): DONE,
kernel side, the era in the NAMES.  `UartNames.cons_names` gains `cn_era
: nat`; `ConsoleInv.cons_era l k := ∀ p, p ∈ l -> obs_boots p.1 = k`
(with `_nil`, `_prefix`, `_snoc`, `_lookup`), and `cons_res` /
`cons_res_at` / `cr_ghost` / `ct_gh` carry `⌜cons_era (st ++ pd) (cn_era
cn)⌝` after `cons_below`.  `cons_ghosts_alloc γu k` returns `⌜cn_era cn =
k⌝`; BootShared calls it at `S gen_id` and exports `⌜cn_era cnm = S
gen_id⌝` beside `cn_uart cnm = γd`, threaded through SystemAdequacy,
`BootChain.boot_hart_primary`, `SpecMain`, `ProofMain` (and
`mn_grp_printk`) as a premise `cn_era cn = S gen_id`.  The CAPS FACTS:
`SpecConsoleintr.console_caps` gains `⌜cn_era cn = S gen_id⌝` (after
`cn_uart cn = γu`), which consoleintr's store arm (`ct_cr`, `ct_store`,
`ct_dflt`, `ct_gh_push`) spends against the byte's own `obs_boots hb = S
gen_id`; on the reader side `SpecFileread.console_ready_app` and
`fileread_dev_caps` gain `⌜cn_era fsc_cons = S gen_id⌝` (readers
`console_ready_app_era`, `fileread_dev_caps_era`), and `SpecSysRead`
takes it as a premise from `ProofSyscall`.  `cons_placed l lo k d hs`'s
per-byte clause is now `(lo <= p) /\ hs !! j = Some h /\ obs_ends_in
Uart0 h b /\ l !! p = Some (h, b) /\ obs_boots h = k`; consoleread's
receipt states it at `k := cn_era cn`, fileread converts it to `S
gen_id` (`cons_placed_era` off `fileread_dev_caps_era`), so
`console_receipt` and `UkReadCons.uread_cons_ans` state it at `S gen_id`
-- S5b reads the era straight off the receipt, no caps fact needed at
the U tier.  `GenOutWild.lm_placed_wild_undisc` takes the extra era
argument (its proof drops the new conjunct).

STATUS (lane S5a, `secc/s5a` off main aa793e35c, design 10.12's UNION
bullet, the claim/pure half): landed, tree green (VM log s5a-3: EXIT=0, no
`Error`, second pass 0 compiles), audits system 13 / union 14 / tree 13
textually the baseline.  `PipeOutW.secc_tok_at k I0` gains a LAST conjunct
`∃ D h0, dl_list_lb v D ∗ ⌜snd <$> D = I0 /\ last D = Some (h0, wl_nl) /\
ins (open_seg h0) = I0 /\ obs_boots h0 = k /\ trace_shape h0 true⌝` -- the
STRONG form (equality, no flush-lost slack), proved at the transition in
`pwclV_step_read` from the new pure `GenOutWild.lm_rd_last_hist` (read_ok's
`hist_chain`, `E_index`, the pops' boots and shapes from `gin_pure`); it
travels unchanged through `rd_retW` / `uread_ret` / `uri_arms` / `urresw`
(they carry `secc_tok_at` whole).  The chain lemma
`GenOutWild.lm_placed_wild_undisc`: `cons_chain sl -> sl !! n0 = Some (h0,
c0) -> n0 < lo -> cons_placed sl lo d hs -> j < d -> I0 `prefix_of` ins
(open_seg h0) -> I0 <> [] -> rest_of I0 = [] -> lm_wild M (lm_line_at M I0)
-> trace_shape (hs !!! j) true -> obs_boots (hs !!! j) = obs_boots h0 -> ¬
lm_disc M (hs !!! j)`.  ITS BOOTS PREMISE IS NOT GIVEN BY THE RING: a push
trace past a power cycle need not extend the old era's input, and
`cons_placed` says nothing about eras; the tag (`utag`) gives the shape
only, so the read leaf (S5b) needs `obs_boots (hs !!! j) = S gen_id` from
the kernel side (the UART layer knows it: `WpUart`'s `obs_boots h = S
gen_id` clauses) or from a widened `cons_placed`.  Also for S5b: tying the
token's `dl_list_lb v D` to the kernel's `sl` (index `n0 = length I0 - 1`)
is the read leaf's job.  One shell-tier touch: `UShURoundLaws.
uwild_read_absurd`'s destruct pattern gains `& _` for the new conjunct.

## S3 -- the seccomp program (design §7, §9) -- brief written when S1 and S2 land

`UCodeSeccomp.v` is generated.  sh-style proof (fork, wait): the child's
`seccomp(mask)` at row 23, `exec(argv[1], argv+1)` through the
taint-shaped walk at `T := secc_tok k` with the generalised
`image_entry_taint` answered by `useccomp_mint` and the child's
`secc_key` (the one place the literal mask enters: `secc_masked` of the
binary's mask, true at upstream 7b2c1b1); the `fprintf` diagnostic and
`exit(1)`; the parent's `wait(0)`, `exit(0)`; an entry `secc_image_entry`
whose `Pay` carries `secc_tok k`; `FsSeccPin.v` on `FsGrepPin.v`'s mould.

## S4 -- the round and the knob (design §7, §10.6) -- brief written when S3 lands

`ush_line_union` at `LSecc`; sh's round law at the wild shape (fork twin;
the exec resolution (W) of `/seccomp`; wait; prompt through the licence);
init's wild arm on the panic path; `secc_ok` widened to file-name words;
the knob `adm_s := fun ws => bool_decide (ws <> [])`; the top theorem's
statement changes only through the model; audits; the completed note.
