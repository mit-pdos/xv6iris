# Project: SIE-agnostic S-mode execution lemmas (the interrupt sweep)


GOAL: every S-mode execution lemma — leaf instructions upward — holds whether
interrupts are enabled or disabled, discharging "no interrupt dispatched"
either from SIE=0 (as today) or by absorbing pending interrupts through
`intr_inv`/`wp_exec_step_intr`.  Migrate ADDITIVELY (new definitions beside
old, call sites flipped file-by-file, old variants deleted last) so `make
proofs` is green at every commit; validate the interface on a VERTICAL PILOT
before any mechanical sweep.

1. **DONE — SIE=1 instruction engine (WpSmodeIntr.v)**: `wp_instr_s_intr`
   over `wp_exec_step_intr` + `tlb_inv_pt_fetch`, plus the RVC and base
   gpr-write engines `wp_gpr_write_s_intr{,_base}` (see the WpSmodeIntr
   bullet in design/interrupts.md for the interface).
2. **DONE — Pilot**: `wp_addi_s_intr` / `wp_cli_s_intr` + the 3-instruction
   straight-line `wp_intr_pilot3` (mixed widths, arbitrary interrupts
   absorbed, `intr_frame`/`stack_own` threaded).  No interface fixes were
   needed; the stage-1 callback shape held up.
3. **DONE — the v2 bundle** (`sconf` + `sie_cap` + conversions, IntrDefs.v;
   see the v2-bundle bullet in design/interrupts.md).  The
   smode_config DELETION still happens at the end of the sweep (item 5).
4. **DONE — engine agnosticization**: the funnel `wp_instr_s_sconf` + the
   gpr-write engines `wp_gpr_write_s_sconf{,_base}` (WpSmodeIntr.v),
   case-splitting on `sie_cap` by ghost agreement and delegating each arm
   to its existing engine (no fetch-drive duplication); validated by the
   SIE-agnostic `wp_sconf_pilot3`.  The raw-cell
   `wp_instr_s_config_tlbinv_pt` STAYS (it is the '0' arm's body and the
   mycpu fraction-island's entry).
5. **Leaf sweep (mechanical, file-by-file; IN PROGRESS):** the live pt
   leaf layer — WpSmodePtLeaves/Alu/Btype/Ctl/Mem/MemWrap/Lock/Uart —
   plus VCgen and the whole-function proofs above them: swap
   `smode_config γ dq` + `tlb_inv_pt` threading for `sconf γ` +
   hart_state + `sie_cap γ root m` + `tlb_inv_pt` over the
   `wp_instr_s_sconf`/`wp_gpr_write_s_sconf*` engines.
   - DONE: **WpSconfAlu.v** (all of WpSmodePtAlu's ops except auipc; the
     raw-cell/_scfg pair collapses to ONE lemma per op; new premise
     `rd <> csp_rs1` everywhere; value-hyp discharges copy VERBATIM —
     use it as the family template).  Exemplars `wp_addi_s_sconf`/
     `wp_cli_s_sconf` live in WpSmodeIntr.v §4.
   - DONE: **WpSconfMem.v** — the width-8 RVC LOAD/STORE twins
     (`wp_cld_s_sconf`/`wp_csd_s_sconf`): `sconf` is destructured INSIDE
     the funnel's σf-callback for the translate side conditions,
     `tlb_inv_pt_translateAddr_load/store` runs as today, the bundle is
     reassembled in the continuation.  Spec deltas: the ea/a8/pa alias
     lets collapse to one `pa`; stores carry NO rd premises and no
     retarget.  Remaining Mem widths (4/1, base) are mechanical repeats.
   - DONE: **WpSconfBtype.v** — beq/bne/bge_x0/cbeqz/cbnez fall-throughs
     (bundle passes through untouched — a fall leaf never opens `sconf`)
     and beq/bne/cbeqz/cbnez taken.  Spec deltas: ALL taken leaves hand
     the step's later out (uniform Löb-ready back-edge shape; the
     base-width originals absorbed it) and go through the Zca jump
     helper, so only bit-0 target alignment is demanded (the bit-1
     premise is gone).  The BTYPE cmp/exec helpers are Local copies (as
     in WpSmodePtBtype).
   - DONE: WpSconfMem.v also has the width-8 base pair (`wp_ld/sd_s_sconf`,
     text-transform of the RVC pair) and the width-4 quartet
     (`wp_clw/csw/lw/sw_s_sconf`; towers LOAD_4/STORE_4, window identity
     `data2_id_4`, storeval `trunc32`); Local helper copies as in
     WpSmodePtMem.  DONE: the pc-reading engine
     `wp_gpr_write_s_sconf_base_pc` + `wp_auipc_s_sconf` (WpSconfAlu.v).
   - DONE: **WpSconfCtl.v** — fence / c.j / jal / c.ret over the funnel
     (c.j hands the later out — an unconditional backward jump is a loop
     back edge; jal carries rd ≠ sp; c.ret opens the bundle only for the
     LPE/priv/misa side conditions).  Csr/Sret deliberately NOT here:
     sret runs in kernelvec's SIE=0 body, csrci/csrsi ARE the stage-7
     flips.
   - DONE: the c.ldsp/c.sdsp sp-relative bridges and release's
     `wp_sd_zero_s_sconf` (WpSconfMem.v).
   - DONE: **WpSconfLock.v** — the acquire/release triple over the
     funnel: `wp_clw_lockinv_s_sconf` (poll read), `wp_sw_zero_lockinv_
     s_sconf` (unlock store), `wp_amoswap_lockinv_s_sconf` (the CAS;
     old-word disjunct out, nonzero mark reseals).  The lock invariant
     opens around the funnel callback's own step — lockN is disjoint
     from minstretN AND intrN, so the open is arm-blind.
   - DONE: the SP-MOVERS (WpSconfAlu.v): the cap engine
     `wp_gpr_write_s_sconf_cap` takes a caller-supplied TRANSFORMER
     `(sie_cap γ root m -∗ sie_cap γ root m')` instead of the rd ≠ sp
     retarget premise; `wp_caddi_sp_s_sconf` / `wp_caddi16sp_s_sconf`
     on top.  `sie_cap_recarve` (IntrDefs.v) builds the transformer
     from pure stack splitting ('0' arm is m-blind, only the '1' arm's
     ≥32-slot bound at the new sp is owed — where function proofs do
     their stack bookkeeping anyway).
   - DONE: `wp_sb_s_sconf` (WpSconfMem.v — width-1 RAM byte store, no
     alignment premise; stored byte is the new `trunc8` of rs2; local
     width-1 helper copies incl. `nth_byte0_id`) and
     `wp_clw_lockinv_locked_s_sconf` (WpSconfLock.v — read while
     holding; the free branch refuted by `locked_exclusive`, token
     rides through, invariant reseals on the nonzero branch).
   - DONE: **WpSconfUart.v** — the accessor-form device leaves
     `wp_sb_uart_s_sconf` / `wp_lb_uart_s_sconf` over the funnel:
     `dev_inv` opens across the funnel callback's own step (devN
     disjoint from minstretN AND intrN — arm-blind, like the lock
     leaves), the uart ghost step runs through the caller's accessor
     wand while the invariant is open, and the translate side reuses
     the REGIME machinery instantiated at `kpt_regime`
     (`sr_inv (kpt_regime root)` IS `tlb_inv_pt root` definitionally,
     so `sr_transform`/`sr_absorb_dev` consume the bundle's invariant
     directly — no PMP peel/reseal needed, the grant facts come out of
     the absorption).  This "regime-at-kpt inside the sconf funnel"
     shortcut is the template for any future sconf device leaf.
   The stage-5 leaf sweep is COMPLETE.  Function proofs (item 8) still
   pending; sp-MOVING instructions have their dedicated re-carving
   leaves (WpSconfAlu.v).
   Watch the import direction: leaf files must import
   IntrDefs/WpSmodeIntr — WpIntrInv no longer imports any leaf file, but
   WpKernelvecSpec does; keep the kernelvec cap on top.  Delete the old
   smode_config at the END of the sweep, not before.  Keep per-file
   compile times within ~10% (the optimization.md perf rules apply; sie_cap
   adds one iDestruct per instruction).
6. **DONE (sp-free fragment) — VCgen over sconf (WpSconfVc.v):**
   `wp_vc_block_s_sconf{,_aux}` re-derive the block-executor recursion
   over the sconf leaves, guarded by `vblock_no_sp prog = true` (no
   VScaddi16sp, no rd = sp write): an sp-move re-carves `sie_cap`'s
   stack bound, so function proofs SPLIT their blocks at sp-moves and
   use the WpSconfAlu sp-mover leaves between blocks (matching existing
   prologue/epilogue composition).  The `_den` layer and the vheap/
   `gpr_matches` plumbing are reused from VcGenS unchanged; a `_den`
   sconf wrapper lands with the first converted function.
7. **DONE — SIE flips (push_off/pop_off leaves; WpSconfCsr.v + WpSieFlipBits.v):**
   - DONE: `wp_csrr_sstatus_s_sconf` (push_off's intr_get) — works at
     either arm; the continuation receives the capability DESTRUCTED
     into its arm PAIRED with ⌜SIE ms = arm-bit⌝ (ghost agreement taken
     while the tied half is in hand — the `iAssert` in the proof is the
     pattern).  `exec_execute_csrr_sstatus` is imported from WpPopOff
     (the WpSmodePtCtl copy is Local) — relocate to a shared csr base
     when convenient.
   - NOTE (stage-8 refactor): with the factored exact-32 `sie_cap`, the
     csrr payload hoists the stack slice out of the arm disjunct, the
     csrci continuation returns a WHOLE `sie_cap` at the '0' arm (not a
     bare quarter) with a stack-free '1' payload, and the csrsi restore
     lost its separate ∃n stack premise (the cap carries the carve).
   - DONE — the csrci ('1'→'0') FLIP leaf `wp_csrci_sstatus_s_sconf`
     (WpSconfCsr.v, premise-FREE): the funnel callback flips mstatus via the new
     non-collapse `exec_execute_csrrci_sstatus_gen`, opens intrN,
     `sie_ghost_flip`s all three pieces to '0', reseals `intr_inv` at
     b:='0' (vacuous handler guard), and hands the caller the freed
     '1'-arm payload; the '0' arm is the idempotent write via
     `legalize_sie_clear_idem`.  The continuation returns the bare '0'
     quarter + the old-bit report disjunct.
   - DONE — the csrsi ('0'→'1') restore leaf `wp_csrsi_sstatus_s_sconf`
     (WpSconfCsr.v): consumes the saved payload (which now carries
     `▷ intr_handler_spec`, extracted by the csrci flip from the
     invariant's guard via quarter-quarter agreement) to re-arm
     `sie_cap`-'1'; the invariant reseals at b:='1' with that spec; the
     already-enabled `sie_cap` branch is refuted by sepc-cell
     exclusivity (`reg_pointsto_excl`).  The dual exec fact
     `exec_execute_csrsi_sstatus_gen` is local there;
     `sstatus_write_set_val` lives in WpSieFlipBits.v.
   - DONE — the two pure SIE-flip characterizations (`csrci_sie_flip` /
     `csrsi_sie_flip`, WpSieFlipBits.v): for
     `ms' := legalize_sstatus_val ms (sstatus_write_val ms 2)` (and the
     csrsi `sstatus_write_set_val` dual), SIE ms' = 0 (resp. 1) and
     every `sconf_ms_facts` bit is preserved ms→ms'.  Both leaves
     instantiate them internally — NO flip premise remains in any leaf
     statement.  The MONOLITHIC route (unfold legalize/lift/lower + one
     tb1-chase) does NOT terminate (the ~18-setter tower product hits
     the super-linear rewrite blowup); the working proof is the LAYERED
     per-field ladder, the reusable recipe for any future
     legalize/lift-tower fact:
       generated `qX_uY` get-over-update rows (each `_get_Mstatus_X`
          against each `_update_Mstatus_Y` in the legalize tower —
          `quu` unfolds getter+setter+subrange prims, then
          `qu_disj`/`qu_same` close by disjoint/same-slice);
       L4 `mstatus_legalized_X'` (getter of the legalized value = getter
          of the input, by exactly the two rows the tower crosses);
       L3 `lift_X` (getter after `lift_sstatus` = S-view field of the
          written value, M-only fields from ms);
       L2 mask lemmas `sX_and2`/`sX_or2` (`_get_Sstatus_X` of
          `and_vec w ~2` / `or_vec w 2`: SIE forced 0/1, other fields
          untouched — via `and_vec_testbit`/`or_vec_testbit` +
          `schase_and`/`schase_or` with k pinned per field width);
       L1 `sX_lower` (imported from WpGprCsrwC);
     assembled by the shared `flip_core` (field agreements in, SIE bit +
     `sconf_ms_facts` out; ending `cbn match. repeat split;
     first [ assumption | vm_compute; reflexivity ].`).
     Still open for stage 8: pop_off's csrsi restore consumes the csrr
     leaf's '1'-payload (trap CSRs + stack bound + intr_inv copy) to
     build the new sie_cap-'1'; the handler spec is already stored
     unconditionally in `intr_inv`, so flips never re-prove it.
8. **Whole functions + boot (IN PROGRESS):** groundwork DONE — the
   exact-32 arm-factored `sie_cap` (see the v2-bundle bullet): sp-move
   re-carving is deterministic via `sie_cap_move_down`/`_up`, so a
   function's stack accounting is: precondition threads
   `stack_own (pa_stk sp0 kv_frame_slots) k` (k = its frame depth, DEEP
   slots adjacent below the cap's carve) + `sie_cap`; the prologue
   sp-move trades them for the frame region above the new sp; the
   epilogue trades back.  The csrci/csrsi leaves now return/consume a
   WHOLE `sie_cap` (see the stage-7 NOTE), so an interrupts-off region
   simply keeps threading the cap.  REMAINING, in order:
   - DONE — `wp_mycpu_sconf` (WpSconfMycpu.v): the first whole function
     on the exact-32 accounting, leaf-by-leaf (the old den blocks
     contain the sp-moves, which the sconf VCgen guard forbids).  Spec:
     sconf + sie_cap thread end-to-end at either arm; the caller
     supplies `stack_own (pa_stk sp0 kv_frame_slots) 2` (DEEP slots)
     instead of a top-of-stack frame; prologue/epilogue movers trade
     through `sie_cap_move_down`/`_up` 2 (transformer P := the released
     frame / the returned deep custody); post = ∀m' with callee_saved +
     a0 = mycpu_ret, cap and deep slots intact.  Axiom-clean, ~2s worst
     sentence.  GOTCHAS for the next conversions: (a) keep frame-cell
     ADDRESSES in `pa_stk` spelling between leaves — passing an
     insert-chain-map spelling (mK !!! sp) into `stack_own_2_intro`
     diverges in unification (re-spell with the HpaK bridges before the
     epilogue mover); (b) spell value-chain constants exactly as the
     final pure definition does (m6's auipc base = `add_vec_int
     (mword_of_int mycpu) 14`, matching mycpu_ret) and respell the pc
     with a closed bv_eq assert before that leaf — the final a0
     conjunct then closes by plain reflexivity (NEVER vm_compute: the
     value contains the symbolic m0!!!tp).
   - DONE — `wp_push_off_suffix_sconf` (WpSconfPushOff.v): push_off's
     shared tail (PO+0x18: 2nd mycpu call, noff increment, epilogue
     frame-trade, c.ret), transformed from wp_push_off_suffix_r.  The
     epilogue c.addi16sp,+32 is the mover: the three restored frame
     cells + a caller-supplied GAP slot (`spm ↦₈ vgap`) rebuild
     `stack_own sp0up 4`, traded via `sie_cap_move_up` for the deep-4
     custody returned in the post; `po_up_cancel` is the closed-offset
     re-anchor cancel (proved via `pa_stk_off2` + a vm'd wrap-to-zero
     + `avi0` — the recipe for any +K/-K sp cancel).  The cap returns
     packed inside the ∃mfin.  GOTCHA: rewrite bridges must use
     EXPLICIT spellings, not let-bound names (a `rewrite -H` whose RHS
     is a let-local like `a8_p24` finds no occurrence — the round-trip
     through a leaf re-spells cells in the leaf's own let-forms).
   - DONE — `wp_push_off_sconf` MAIN (same file, axiom-clean at
     baseline 5 + funext): prologue mover k:=4
     (deep-6 input: top 4 feed `sie_cap_move_down`, deeper 2 ride for
     the mycpu calls at `pa_stk sp' kv_frame_slots`) + 3 csdsp saves +
     caddi4spn + the FUSED `csrrci a5,sstatus,2` at 0x0a =
     `wp_csrci_sstatus_s_sconf` (rd=a5; continuation returns the WHOLE
     cap at '0' + the report/payload disjunct — thread the payload
     OPAQUELY through everything after) + c.mv s1,a5 + 1st mycpu call +
     clw noff + cbeqz (WpSconfBtype taken/fall) + intena arm (0x2c 3rd
     mycpu call, 0x30 srli4 a5,s1,1, 0x34 candi a5,1, 0x36 csw
     124(a0), 0x38 c.j back) + `wp_push_off_suffix_sconf` on both arms.
     Post: ∀ms mfin with callee_saved + noff+1 + intena :=
     `po_intena_val ms` (the operational SIE-bit spelling) + the flip
     payload disjunct tied to ⌜SIE ms⌝; deep-6 custody back (recombined
     from the epilogue's deep-4 + mycpu's deep-2 via
     `stack_own_split_2`).  GOTCHA: the branch/jump leaves hand the
     step's ▷ out and the absorbing `iNext` strips a later from EVERY
     hypothesis — the csrci payload's `▷ intr_handler_spec` loses its
     later on the taken arm, so that arm re-introduces it (`iExists h;
     iFrame; iNext`) when discharging the continuation's payload.
   - DONE — the INTERRUPTS-OFF TOKEN (IntrDefs.v): `sie_cap`'s '0' arm
     holds an EIGHTH (spelled `(1/4/2)%Qp` — a bare `1/8` literal does
     not parse in Qp scope); the other eighth is `intr_off_tok γ`,
     minted ONLY by the genuine csrci flip (`sie_ghost_flip_off`) into
     the '1' payload and consumed by the csrsi restore
     (`sie_ghost_flip_on`; NOTE iCombine auto-normalizes Qp sums, so no
     fraction rewrite is needed on the combine side).  Any fraction of
     '0' pins the arm by agreement — code holding the token or the
     payload refutes interrupts-enabled cases WITHOUT a panic axiom.
     push_off's payload carries the token through to its caller.
   - DONE — `wp_pop_off_sconf` (WpSconfPushOff.v, axiom-clean): leaf-by-leaf (the old
     wp_pop_off_r's VCgen blocks contain the sp-moves).  INPUT: the
     paired push_off report/payload disjunct
     `(⌜SIE ms=0⌝ ∗ intr_off_tok γ) ∨ (⌜SIE ms=1⌝ ∗ full payload)`
     (nested callers BORROW the outer region's token for the left case)
     with intenav = po_intena_val ms; deep-4 custody (2 frame + 2
     mycpu).  Body: 2-slot prologue trade, mycpu, csrr sstatus + candi
     2 + c.bnez (the intr-must-be-off check: LEFT case refuted by
     token/half agreement, RIGHT by the payload's sepc vs the cap-'1'
     sepc — both arms of the csrr report force the fall-through), clw
     noff + bge-x0 fall (premise noff ≥ 1) + addiw -1 + csw, c.bnez
     (noff-1 ≠ 0 → epilogue, payload returned) / c.lw intena + c.beqz
     (intena = 0 → epilogue) / the RESTORE: csrsi consumes payload +
     token (`wp_csrsi_sstatus_s_sconf`), cap re-arms '1'.  POST: plain
     `sie_cap γ root mfin` (arm hidden covers both) ∗ (if the restore
     ran — noffv=1 ∧ intena≠0, pure — then True else the input
     disjunct back); noff-1 stored; callee_saved.  PREREQUISITES DONE:
     `ppi_24`/`ppdec_24` (WpSconfPushOff.v; the csrsi at PP+0x24 is
     0x10016073 = csrrsi x0,sstatus,2 — rd is X0) and the x0 leaf
     `wp_csrsi_sstatus_x0_s_sconf` + `exec_execute_csrsi_sstatus_x0`
     (WpSconfCsr.v; no register write, map unchanged, no rd premises).
     ALL THREE runtime paths proven (early-noff / intena=0 / the
     RESTORE, which consumes payload + token through the x0 leaf and
     re-arms the cap); the shared epilogue is the factored
     `wp_pop_off_epi_sconf` (returns the mf INSERT-CHAIN EQUATION so
     each path does its own callee_saved pin-chase); the post's
     conditional payload is `if (negb (neq nv1 0) && neq (sext intena)
     0) then emp else input-back` — destruct-with-eqn on the branch
     scrutinees reduces it per path (the intena `neq` needs an explicit
     unfold-rewrite: destructing `eq_vec` does not reduce a `neq_vec`
     spelling).  The intena-bit fact is DONE:
     `po_intena_val_sie` + case forms `po_intena_val_zero/_one`
     (WpIntenaBits.v, iris-FREE — the testbit chase needs vanilla
     rewrite scope; under the iris imports the ssr rewrite's
     all-occurrences semantics breaks the capture-assert scripts).
     Recipe used there (reusable): capture closed subterms FROM the
     goal via match-assert + vm (never hand-spell deep MachineWord
     terms — elaboration mismatch hangs); value-level wrap/swrap
     removal via vm'd modulus literals + abstract b2z bounds (the
     zify-hooked `lia` "Cannot find witness" trap applies — use
     compute/congruence and explicit Z.le/lt_trans); `Z.land y 1` via
     a local ones-based helper.
   - DONE — `wp_holding_lockinv_s_sconf` + `_locked_s_sconf`
     (WpSconfHolding.v, axiom-clean): the not-mine form (returns 0 —
     acquire's check; fast path when the lock is free, slow path
     through the k:=4 frame trade + mycpu + the seqz chain) and the
     locked/mine form (the caller's lock token refutes the fast path
     via the locked clw leaf, returns 1 — release's check).  GOTCHA
     (recurring): define each sp-write map (`set (S0 := ...)`) with
     the LEAF's exact value spelling (`add_vec (Hprev !!! csp) ...`),
     NOT a pre-folded let — a proved gmap-lookup equation is not
     conversion, so iExact/iFrame across the transformer bracket fails
     otherwise; and remember the leaf ROUND-TRIP re-spells cells at
     ITS map's lookups (bridge goal-side with -HcspSx rewrites).
   - DONE — `wp_release_sconf` (WpSconfRelease.v, axiom-clean): the
     FIRST end-to-end payload composition — holding-locked (the token
     forces a0=1), lk->cpu := 0, fence, the lock-word clear (locked ∗ R
     re-enter the invariant), then pop_off with the intenav-keyed
     input threaded straight through; the conditional payload flows
     back out in release's post, and pop_off's restore is genuinely
     reachable.  Deep-10 custody: 4 for release's frame, 6 riding for
     holding, of which 4 re-lent to pop_off (split_1/split_2 around
     the call).  jal-calls are INLINE (jal leaf + callee spec at the
     ra-inserted map + a closed pc-normalization assert — no wrapper
     lemma needed).  The old spec's intena=0 pin and the
     `ghost_var γc (1/2) b` rider are GONE.
   - REMAINING spinlock layer:
     ALL DONE — `wp_holding_lockinv{,_locked}_s_sconf`
     (WpSconfHolding.v), `wp_release_sconf` (WpSconfRelease.v), and
     `wp_acquire_sconf` + `wp_acquire_lock_loop_sconf`
     (WpSconfAcquire.v), all axiom-clean.  Acquire's push_off flip
     opens the interrupts-off region (its ∀ms payload rides framed to
     the post alongside locked ∗ R); release's pop_off may genuinely
     restore, with the conditional payload flowing back out; the
     old intena=0 pins and ghost riders are gone.  Löb-loop gotchas:
     generalize the CAP alongside the file in the iLöb (both keyed on
     the loop register), and seed with `insert_id` +
     `lookup_lookup_total_dom` on BOTH.  Composition between
     acquire's ⌜SIE ms⌝-keyed post and release's intenav-keyed input
     uses `po_intena_val_zero/_one` (WpIntenaBits.v).  THE SPINLOCK
     LAYER IS COMPLETE.  NEXT: the kalloc cone — BLOCKED on
     the NESTING-EVIDENCE design decision below.
   - RESOLVED — the COUNTING TOKEN (IntrDefs §6b, all pushed
     axiom-clean): the SIE ghost's spare quarter splits into TWO
     eighths — one in `sie_cap` (per-instruction arm witness), one in
     `intr_count γ root n` (the per-function counting token mirroring
     noff nesting).  Both agree with the mstatus-tied half, so the flip
     (`sie_ghost_flip_off`/`_on`) gathers half + cap-eighth +
     count-eighth + inv-quarter.  `intr_count 0` = eighth-'1' ∨
     (eighth-'0' ∗ restore); n≥1 = eighth-'0' ∗ restore.  `n>0 ⇒ off`
     (`intr_count_pos_off`); level-0 ↔ raw SIE token
     (`intr_count_init`).  The exclusive trap CSRs MOVE between
     sie_cap's '1' arm and intr_count at each flip (persistent
     intr_inv/handler-spec duplicate freely; the ▷ on the spec is
     re-added via `intr_restore_intro` after a branch's iNext).
     push_off: `intr_count n` → `intr_count (S n)` (csrci: real flip at
     n=0 arm-'1', idempotent otherwise; the leaf refutes impossible
     arms by agreement, `intr_count_get_on/_off`).  pop_off:
     `intr_count (S n)` → `intr_count n`, with the COUPLING premise
     `neq_vec nv1 zero_reg = false ↔ n = 0` tying the runtime
     noff-1==0 branch to the token level (so the restore path, csrsi
     1→0, coincides with the outermost pop).  acquire passes the token
     with an INCREMENT (push_off inside), release with a DECREMENT
     (pop_off inside).  csrr keeps its arm-report (pop_off refutes the
     '1' arm via its count eighth); csrsi flips only 1→0.

   - KALLOC + KFREE DONE (both Qed, axiom-clean, registered).  kalloc
     (WpSconfKalloc.v) is the branchy one: acquire (n→S n) → ld freelist
     head → c.beqz → EMPTY arm (reclose kmem_res, release S n→n, c.j,
     return null / kalloc_post=Left) OR NONEMPTY arm (pop: ld nxt, sd
     kmem.freelist:=nxt, reassemble page_own; release S n→n; memset(p,5,
     4096) via wp_memset_page_sconf; return page / kalloc_post=Right).
     THE ONE KALLOC-SPECIFIC GOTCHA: the c.beqz-TAKEN leaf hands the
     step's later out, and the following iNext strips the ▷ from the
     *reducible* `intr_count (S n)`'s inner (persistent) handler-spec, so
     it must be re-folded before the release via `intr_restore_intro` +
     `intr_count_pack_S` (destruct the stripped token, re-add the later).
     The RETURNED `intr_count n` (symbolic n = a STUCK match) is NOT
     stripped by iNext, so it needs no re-fold; and the NONEMPTY arm's
     c.beqz-FALL leaf has a plain continuation (no iNext), so its release
     needs no re-fold at all.  Padding-slot gotcha: kalloc's 4-slot frame
     saves only ra/s0/s1 (3), leaving slot-0 padding `Hg4` never loaded —
     rewrite HspR1 into it too before the epilogue rebundle (the loaded
     cells got it via the cldsp round-trip, the padding didn't).  The
     noff-cancel + memset-deep-2 + acquire/release-deep-10 patterns are
     exactly kfree's.
   - WAKEUP — FULLY PORTED to sconf (Qed, axiom-clean).  `wp_myproc_sconf`
     (axiom) + `wp_wakeup_prologue_sconf`/`wp_wakeup_epilogue_sconf` live in
     WpSconfWakeup.v; `wp_wakeup_loop_sconf` (the 796-line loop) +
     `wp_wakeup_sconf` (= prologue → loop → epilogue) in WpSconfWakeupLoop.v.
     Two design decisions worth remembering: (a) `wk_res_sconf` holds the
     intena cell EXISTENTIALLY (`∃ iv, wk_intena_addr a0f ↦₄ iv`) — this
     sidesteps the smode's intena≡0-under-SIE=0 assumption, since acquire
     rewrites intena only when noff==0 and release passes it through, so the
     ∃ absorbs both cases with no `ms` dependence; (b) the proc-lock resource
     is threaded OPAQUELY (params `Rreg/γc/bsie/dq`) — wakeup relays parked
     contexts but never resumes them, so the smode `proc_lock_res` (whose
     `proc_ctx` embeds a smode `valid_context`) rides along untouched and
     ports later with the scheduler.  release's coupling premise reduces to
     the entry coupling `neq_vec (sext noffv) zero = false ↔ lvl=0` via
     `wk_release_nv1_cancel` (reuses `kfree_nv1_cancel_pure`).  The compose
     needs K≥18 (prologue carves 8 for the frame, loop borrows deep-10).
   - (historical) KALLOC CONE (kfree/kalloc/wakeup, unblocked by the counting token).
     Each is acquire → critical section → release, so the SPEC threads
     `intr_count γ root n` NET-ZERO: `intr_count n` in and out (acquire
     increments to S n inside the disabled region, release decrements
     back).  Follow WpSconfRelease/WpSconfAcquire (new files
     WpSconfKfree.v etc.): prologue frame trade, the freelist load/store
     leaves over the funnel, `wp_acquire_sconf` (n→S n) around the
     section, `wp_release_sconf` (S n→n), epilogue.
     KFREE DONE — `wp_kfree_sconf` (WpSconfKfree.v, registered, Qed,
     axiom-clean at baseline 5 + funext).  The FIRST full kalloc-cone
     function over sconf.  End-to-end: prologue (frame trade
     sie_cap_move_down 4), panic-check ALU (pure sconf leaf swaps —
     register-map lets transcribe VERBATIM from WpKfree), the memset call
     (wp_memset_page_sconf, deep-2 lent), the acquire call
     (wp_acquire_sconf, intr_count n→S n, deep-10), the freelist push
     (ld/csd/sd_s_sconf + kmem_res_push), the release call
     (wp_release_sconf, S n→n), the epilogue (4 c.ldsp + c.addi16sp
     move_up 4 + c.ret), and callee_saved.  The deep-custody
     split/recombine around each sub-call and the intr_count net-zero
     threading all work.  THE NOFF-CANCEL LEMMA `kfree_nv1_cancel_pure`
     (top-level, iris-free): release's nv1 (from acquire's incremented
     po_noff_store) = `sign_extend' 64 noffv`, so release's coupling
     premise IS the clean entry premise `noff==0 ↔ intr_count level==0`.
     THE CLEAN PROOF (reusable recipe for any acquire/release noff
     composition): use VcGen's trunc32 algebra — `trunc32_subrange`
     (subrange..31 0 = trunc32), `trunc32_add` (distributes over add_vec),
     `trunc32_sext` (trunc32 ∘ sign_extend' 64 = id), `trunc32_mword_of_int`.
     They collapse store to `noffv+1` and nv1_inner to
     `(noffv+1)+(-1)`; the final `add_vec (add_vec noffv 1) (-1) = noffv`
     is one bv_wrap-add-modulus step (63:mword6 = -1, so sext12/sext64 of
     it = -1, trunc32 = the mword-32 all-ones = bv_modulus 32 - 1).  Do
     NOT hand-roll subrange-unsigned lemmas — the trunc32 layer already
     has them.  NEXT in the cone: kalloc, wakeup (same shape; kalloc's
     memset is AFTER release, so it threads the same way with the call
     order swapped).  GOTCHAS from the kfree build (all in the proof):
     the `repeat rewrite lookup_total_insert_ne` delta-sees-through `set`
     vars to `m` — use EXPLICIT per-map `rewrite /RK lookup_total_insert_ne`
     peels for map-lookup asserts that must stop at an intermediate map;
     a composition assert like `Hpc2` needs explicit `: mword 64` width
     annotations or vm_compute diverges inferring the width from the iris
     context; imports need `SRegime SmodeCore` for the gmap `!!!`
     instance and must NOT trailing-`Import Defs`/`Require Riscv.rv64d`
     (shadows `!!!`).  Historical detail (spec/prologue):
       - SPEC decided.  Threads `sconf γ + hart_state + sie_cap γ root m +
         intr_count γ root n + tlb_inv_pt` and a DEEP-`K` custody
         `stack_own (pa_stk sp0 kv_frame_slots) K` with `14 <= K` (its own
         4-slot frame + the 10 the deepest sub-call, acquire/release,
         wants).  The lock is `is_lock γl lk (kmem_res fl)`; the cpu-struct
         cells `a_cpu`/`a_noff`/`a_int` are threaded (acquire/release read
         and write them).  The acquire/release coupling `neq nv1 zero <->
         level=0` is stated cleanly as the ENTRY premise
         `neq_vec (sign_extend' 64 noffv) zero_reg = false <-> n = 0` — the
         natural lockstep between the hardware noff counter and the ghost
         token level (NOT ad-hoc: it IS the counting token's meaning).
       - PROLOGUE done: the c.addi16sp sp,-32 is `wp_caddi_sp_s_sconf` fed
         a `sie_cap_move_down 4` transformer; split the deep-K via
         `stack_own_split_1 (pa_stk sp0 32) 4 K` (top-4 → move_down, rest
         `stack_own (pa_stk sp' 32) (K-4)` = the sub-call custody at sp'),
         four `wp_csdsp_s_sconf` saves into the freed frame cells,
         `wp_caddi4spn_s_sconf`.  Gotcha: Hsp1's `apply f_equal` needs an
         explicit `unfold regval_into_reg` first (lookup_total_insert
         leaves the identity wrapper on).  Import gotcha: needs
         `SRegime SmodeCore` for the gmap `!!!` Inhabited/LookupTotal
         instance (else the whole statement is UNDEFINED EVARS), and must
         NOT do a trailing `Import Defs`/`Require Import Riscv.rv64d`
         (shadows the `!!!` instance — WpKfree has neither).
       - REMAINING: the panic-check ALU (0x0c..0x30, pure sconf leaf swaps
         — auipc/addi4/sltu/cli/cslli/caddi/cor/cbnez_fall/cmv/slli/clui,
         all exist as `_s_sconf`, `wp_slli_s_sconf` just added to
         WpSconfAlu), then `wp_memset_page_sconf` (lend deep-2, split from
         the deep-(K-4)), the acquire setup + `wp_acquire_sconf` (lend
         deep-10, n→S n), the freelist push (ld/csd/sd_s_sconf +
         `kmem_res_push`), `wp_release_sconf` (deep-10, S n→n), the
         epilogue (4 c.ldsp + c.addi16sp +32 via `sie_cap_move_up 4` +
         c.ret), and callee_saved.  The register-map lets (R1..R14, Mms,
         S1..S3, Kacq, Rld, Rae, Rrel, Q54..Q5c) transcribe VERBATIM from
         WpKfree; only the resource threading + leaf names change (each
         sconf leaf: `γ root Φ pc … m` + `rd≠0`,`rd≠csp` + value hyp,
         thread `Hsc Hhs Hcap Htlbinv Hpc Hfile Hi [-]`, cont
         `Hhs Hsc Hcap Htlbinv Hpc Hfile`).
   - MEMSET over sconf — DONE, axiom-clean (baseline 5 + funext).
     memset runs OUTSIDE the interrupt-disabled region (kfree: before
     acquire; kalloc: after release), at the caller's ambient SIE level
     (possibly ENABLED), so the SIE=0-pinned `smode_config` engine is
     UNSOUND (an interrupt can fire mid-fill) and the sconf<->smode_config
     BRIDGE idea is wrong for this call site.  The whole memset thus runs
     over the funnel (`wp_instr_s_sconf`), threading `sconf + hart_state +
     sie_cap + tlb_inv_pt` (NO intr_count — memset never touches the
     disable nesting):
       - `wp_memset_loop_sconf` (WpSconfMemset.v): the byte-fill loop,
         fuel induction, sie_cap arm-blind retargeted across the a5
         increment; the bne-taken back edge hands the step's later out
         (stripped by iNext against the fuel IH); two local bridges align
         the sb leaf's [add_vec cur (sext 0)]/[trunc8 v] byte shape with
         the buffer's [ms_pa cur]/[nth_byte .. 0].
       - `wp_memset_prefix_sconf` / `wp_memset_suffix_sconf`
         (WpSconfMemset.v): the 2-slot save-frame alloc/dealloc.  Unlike
         the loop (a5 only), these MOVE sp, so they do the DEEP-CUSTODY
         FRAME TRADE — the prefix's c.addi sp,-16 is `wp_caddi_sp_s_sconf`
         fed a `sie_cap_move_down 2` transformer (deep-2 in → memset's own
         2 frame cells [sp',sp'+16) out, FULL slots — NOT the old
         dqm-fractional caller cells); the two c.sdsp save ra/s0 into them;
         the suffix mirrors it with two c.ldsp + `sie_cap_move_up 2` (frame
         cells packed back → deep-2 returned).  The suffix is the
         `wp_pop_off_epi_sconf` shape at memset's concrete PCs.
       - `wp_memset_page_sconf` (WpSconfMemsetPage.v): composes prefix +
         loop + suffix at N = 4096, threads
         `stack_own (pa_stk sp0 kv_frame_slots) 2` (deep-2 custody,
         net-zero) + page_own, bridges page_own to the per-byte buffer,
         assembles callee_saved.  kfree/kalloc call this directly, lending
         the deep-2 from the stack region they already own.
     Gotcha kept: a whole-function-composition assert like `Hpc2 :
     add_vec_int (add_vec_int (mword_of_int (MS+0x14)) 6) 4 =
     mword_of_int (MS+0x1e)` MUST carry explicit `: mword 64` annotations
     — without them the width evar is inferred from the huge iris context
     and the `vm_compute` diverges (the isolated goal is instant).  The
     N=0 empty path is NOT ported (memset_page always fills 4096); if ever
     needed, clone the prologue+taken-cbeqz→suffix shape.  (The SIE=0
     `wp_memset_page` stays for any caller genuinely holding smode_config;
     the sconf version is a parallel funnel-based derivation.)
   - BOOT WIRING — bigger than "just allocate + plumb"; there is a real
     execution gap.  Current state (mapped): `wp_kernel` (WpKernelNew.v:36)
     composes `_entry`→`start()` and STOPS at `<main>` (0x80000e82,
     Supervisor) handing back RAW cells (hart_state, cur_privilege,
     mstatus, mie, mideleg, menvcfg, satp, stack_own …) — NO γ, NO bundle,
     NO stvec install.  The stvec handler is installed by `csrw stvec,a5`
     inside `trapinithart` (0x80002436, KernelInstrs.v:12708), reached via
     `main`→`trapinithart`.  So the boot wiring needs, IN ORDER:
     (1) a NEW `csrw stvec` WP leaf (none exists; the general CSR-write
         engines are WpGprCsrwA/B/C.v — model on those; it turns
         `stvec ↦ᵣ v0` into `stvec ↦ᵣ kernelvec` over the raw S-mode cells);
     (2) drive the `main`→`trapinithart` body to that csrw (an unproven
         whole-function stretch — the biggest chunk);
     (3) at the install point: `sie_ghost_alloc 'b0` → fresh γ with
         1/2+1/4+1/4, re-split one 1/4 into two 1/4/2 eighths; build
         `sconf γ` from the raw cells (SmodeCore.v:1086 `smode_config_rebuild`
         or IntrDefs.v:350 direct); `intr_inv_alloc_off ⊤ γ kernelvec
         root_ppn MENVCFG_S` (IntrDefs.v:328, uses `kernelvec_tv_direct`/
         `kernelvec_stvec_base`, WpKernelvecSpec.v:41) → `intr_inv`; assemble
         `sie_cap` (sie_arm left 'b0 arm + a 32-slot `stack_own` carve) and
         `intr_count γ root 0` via `intr_count_init` (IntrDefs.v:495, needs
         intr_off_tok = the 2nd eighth + `intr_restore` from
         `intr_restore_intro` IntrDefs.v:544);
     (4) enter the kernel body with sconf/sie_cap/intr_count.
     ADEQUACY: `riscv_system_adequacy` (RiscvAdequacy.v:201) is at the raw-
     resource/`WP Loop` level and says NOTHING about smode_config; the boot
     assembly goes inside its `={⊤}=∗` (where the device ghosts are already
     alloc'd, lines 230-231).  `sconf`/`smode_config` are INDEPENDENT (no
     bridge lemma, intentionally).  DELETE `smode_config` at the very end.

