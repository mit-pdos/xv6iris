# M6 W3 — adequacy-export reconnaissance (2026-08-11)

Read-only recon of how the weak-memory write log is threaded through the
Iris state interpretation and what `weak_system_adequacy` can export, run
before designing W3 (Layer 2).  Line numbers are against branch
`weak-memory` @ `04dd2597`.  The DECISIONS this induced are D-M6-6 and the
rewritten W3 stage in [`weak-memory-m6.md`](weak-memory-m6.md); this file
keeps the evidence and the file:line map for the implementer.

## Executive summary

1. **No per-message ghost state exists today.** The log's authority is one
   `mono_list` over `wmsg` (`iris/WeakGhost.v:86`, `:316`) with a single
   append-only update lemma (`:336`).  `wm_tid` is documented as inert,
   existing only for the M6 statements (`iris/WeakInterp.v:443-449`) — the
   precedent for adding another inert field.
2. **Log appends are NOT at a chokepoint**: each store leaf calls
   `wlog_update` itself (six sites: `WeakLeafSd8.v:569`, `WeakLeafSw4.v:473`,
   `WeakLeafSdspOff.v:431`, `WeakLeafTor.v:984`, `WeakLeafAmo4Leaf.v:789`,
   `WeakKpt.v:1497`), because `wlog_auth` is a conjunct of `wmstate_norg`
   (`WeakFunnel.v:515`).  A natural chokepoint exists one level up
   (`WeakInstr.wp_winstr:524` / `WeakFunnel.wwp_instr:615`), which already
   knows the append fact `∃ l, wm_log σ' = wm_log σ ++ l`
   (`WeakInstr.v:501`).  Emitting there would let the six leaf calls be
   DELETED rather than grown.
3. **A pure per-reachable-state export is nearly free**: the final
   continuation of `weak_system_adequacy` binds the state interpretation at
   `g2` and discards it (`WeakAdequacy.v:225-227`); a
   `weak_state_interp_export : weak_state_interp g -∗ ⌜φ g⌝` slots in with a
   three-line change.  `φ` may also mention the step count `n` (the interp
   receives it and currently drops it, `WeakGhost.v:501`).
4. **A trace property is NOT expressible by choosing φ** —
   `wp_strong_adequacy` quantifies only the endpoints; the installed Iris
   has no trace-indexed variant.
5. **THE CENTRAL FINDING — trace coherence is a QUANTIFIER problem, not a
   ghost-algebra problem.**  `rtc erased_step` is prefix-closed, so a
   per-state φ quantified over all reachable `(t2, g2)` already covers every
   intermediate state of every execution — PROVIDED φ takes no
   existentially-quantified tagging.  Export `∃ τ, φ (g2, τ)` and the
   witnesses at two reachable states are unrelated (two independent
   adequacy instantiations); Layer 1 cannot consume that.  Kill the ∃ —
   make the tagging a FUNCTION of the state — and the current adequacy
   shape suffices verbatim; keep it and a ~200-line in-tree analog of
   `wptp_postconditions`/`wp_strong_adequacy_gen` is needed.
6. **Making the tagging a state function is possible, piecewise:**
   - *The log/history*: genuinely recoverable — the log is append-only and
     per-index immutable at both levels (`WeakInstr.v:501`,
     `WeakExec.v:223-226`, DMA arm `WeakExec.v:162-165`, ghost `:336`), so
     "the final log's length-k prefix IS the log after the k-th append" is
     a pure meta-lemma.
   - *The class (owned/fenced/excl)*: recoverable IF made a function of the
     message — add `wm_ak : akinfo` (or two bools) to `wmsg`
     (`WeakMem.v:48`).  The access kind is already present at every layer
     that builds the message (`classify`, `WeakInterp.v:248`; `wwrite_post`
     `:473-481`) and is a PARAMETER of every pure store certificate
     (`WeakCert.wcert_store:1307`, `WeakEff.wcert_store_gen:544`,
     `WeakEffSkel.v:811`), so the sweep is mechanical.  ⚠ Syntax only:
     "plain store" ≠ "owned store" — the SEMANTIC content of SCowned must
     come from the Iris proof (see blast-radius §, ownership reflection).
   - *Publication (owned→published)*: NOT recoverable as a ghost bit (a
     final "published" cannot say WHEN it flipped, and the violation is
     temporal).  Neither existing view component works: `w_vwNew`
     over-approximates (raised by acquire loads and non-release fences);
     `w_vRel` under-approximates (bare `fence rw,w` — exactly the M6
     release idiom — does not touch it, and raising it would STRENGTHEN
     the machine, unsound direction, since `load_vpre` consumes it,
     `WeakMem.v:464`).  The fix: an INERT `w_pub : nat` watermark in
     `wstate`, raised by release fences and `rl` stores, read by NO rule —
     the `wstate` analog of `wm_tid`.  Then
     `published g m := ts m ≤ w_pub (wgws g (author m))` is a monotone
     total function of the state.
7. **There is no fence leaf to emit a ghost flip at anyway**:
   `WeakFence.v` is pure view arithmetic; the fence's WP surface is generic
   write-free certificates + `wQ_fence` (`WeakInstr.v:638`), no dedicated
   leaf file.  A state-derived publication needs no emission site at all —
   this independently forces the same design as (6).
8. **The under-budgeted real cost of Layer 2: the ownership reflection.**
   A bare "every message is tagged" export rules out nothing; the useful φ
   is VIOLATION-FREEDOM ("no foreign agent's floor has reached an
   owned-unpublished message"), and to prove φ inductively the state
   interpretation must know who owns which byte — today it does not
   (`wlat_interp` is an agreement, not a domain/owner equation,
   `WeakGhost.v:197-199`).  Maintaining φ needs a per-byte owner/hazard
   reflection minted from the exclusive `↦w{1}` at store time and consulted
   at read time — and the racy-load rules (`WeakRacy.v:1120`, `:1207`,
   `WkStartedLoad.v:283`) are exactly where the obligation must be
   DISCHARGED, not just threaded.

## The emission path (for the implementer)

Store-leaf chain, outermost first: `WeakExec.wp_wrun_step:183` (the only
hart-side place `weak_state_interp` is closed; per-hart focus at
`:201-203`, reassembly `:239-245`) → `WeakExec.wp_wexec_step:252` →
`WeakInstr.wp_winstr:524` (gets `wstep_post`, `WeakInstr.v:495-503`) →
`WeakFunnel.wwp_cb:585`/`wwp_instr:615` (hands the leaf `wlat_interp`,
`reg_interp`, `wmstate_norg`; takes them back at σ') → leaf ghost updates
(`WeakLeafSd8.v:567-575`: `wlat8_store_prim`, `wlog_update`,
`hart_ws_update`).  The message-identity fact rides `wQ_store_w`
(`WeakInstr.v:648`) / `wQ_amo_aq_w` (`:659`) / width instances
(`WeakWord8.v:493-520`).  Rules that reassemble `wmstate_interp` and would
thread any new conjunct: `WeakExec.v:201,239-245,303,330,364`,
`WeakInstr.v:543`, `WeakRacy.v:1144,1236`, `WeakBranch.v:83-93`,
`WkStartedLoad.v:283-294`.  Disk agent: `wp_wdisk_step`
(`WeakExec.v:349-375`) makes the DMA append a caller obligation at one
rule (no code yet — M5), in scope per D-M6-4.

Boot side: ghost allocation at `WeakAdequacy.v:146-162`, initial interp
`:194-217` (log conjunct `:208-209`), final continuation `:225-227`.

If the `w_pub` watermark lands in `wstate`: record literals at
`WeakMem.v:252,515-521,529-537,540-549,899`, `ws_le:581-583`,
`ws_bounded:874-875`, `WeakInterp.barrier_post:263-278`, and
`WeakViewMono.v:54,63,102,363` (the five `mono_nat`s).

The release/acquire semantic hook already in the tree (align `published`
with it, do not invent a parallel notion): the release DEPOSIT at the
store's own timestamp — `WeakInstr.wwp_release_deposit:743`,
`WeakFence.release_deposit:281`, consumed via
`release_acquire_transfer:391` / `release_fence_transfer:403`; the `sd`
leaf threads the payload `R` (`WeakLeafSd8.v:470-481`, `:561`); the
acquire-AMO leaf is `WeakLeafAmo4Leaf.v` (append at `:789`).  The walker
CAS (`WeakUpdEff.v` header): both halves classify `AkInfo false true
false`, so the syntactic class picks the SCexcl arm out automatically.
