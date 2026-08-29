# AMENDMENT 7 (2026-08-29) — the T-leg's post-r37 vocabulary: what main's port must fix and what it can land next

**Written by:** the TSO lock-lane coordinator (branches `tso`, `tso-flip`),
after reviewing main's port through Amendment 6 (`21214bdc0`).
**Reference tree for every line number below:** `tso-flip` at snapshot
`2f220f707` (round r48, 1183/1298, zero admits); working copy
`/shared/xv6iris-3-fliptree/iris/`.  Design record: `tso-machine-flip.md`
A6.119–A6.126 and rulings §0.38′–§0.41′ in `tso-port.md` (branch `tso`).

**Review verdict (context, not work):** the port is architecturally right —
the seal plus one quarantined shim whose imports are the cutover worklist;
the M2 threading at the M-leg's sites; the two stub sites (forked child,
secondary harts) honestly quarantined and matching where the T-leg itself is
still open; the cherry-picks from the T-leg (`lock_pay_intro` with
`ctx_deposit` and the paid creator cascade, no `caps_fam`, `ctx_floor`,
`lk_floor`, `lock_finisher`) are the right ones.  What it missed is only
that its T-leg reference predates A6.119: everything the T-leg changed or
added after r37 is STATEMENT-level vocabulary with a trivial SC body, i.e.
above the seal, and four of those changes REFUTE shapes main now carries.

---------------------------------------------------------------------------

# >>> START HERE: the work of this amendment (Slice 5), in order <<<

Each step leaves main FULLY GREEN (the brief's ground rules apply: full
build + `audit-only` at the sanctioned thirteen, zero `Admitted`, no new
`Axiom`, sentinel-backed numbers).  "SC body" below always means: the
sealed definition's body on main is `True` (or the existing trivial body),
exactly as `hart_view_lb_def` / `log_lb_def` already are.  Copy the
STATEMENTS from the reference tree verbatim; do not derive.

## 5.1  `lk_floor`'s right arm is the context's own dirty-write witness (FIX)

Main: `WpLock.lk_floor xi lo := ctx_floor xi lo ∨ log_lb lo` (`log_lb` is a
name main coined, Amendment 4.3 item 1).  The T-leg refuted the
install-receipt arm in A6.120: it does not transport, and it forced
`lock_openable_c` to be threaded through ~40 `SpecAcquire` callers before
the arm was replaced.  The T-leg's arm:

    WpLock.v:1077   Definition lk_floor (ξ : CtxId) (lo : nat) : iProp Σ :=
                      (ctx_floor ξ lo ∨ ∃ a : Arch.pa, ctx_wrote ξ lo a)%I.
    TsoCtx.v:2889   Definition ctx_wrote (ξ : CtxId) (t : nat) (a : Arch.pa) : iProp Σ
                    -- persistent; "context ξ wrote address a at position t"
                       (T-leg body: the discarded element of the token's dirty map)
    TsoCtx.v:2905   own_context_expose_w   (+ own_context_w, own_context_w_fold)
    TsoCtx.v:2923   ctx_wrote_register     -- the STORE registers its position
    TsoCtx.v:2960   own_context_wrote_vis  -- cash the witness against the running token
    TsoCtx.v:2989   ctx_dom_wrote_floor    -- the witness becomes the receiver's floor
                                              across domination (why it transports)
    WpLock.v:1086   lk_floor_of_ctx, 1089 lk_floor_of_wrote
    WpLock.v:1097   Instance lk_floor_morph : CtxMorph (λ ξ, lk_floor ξ lo)
    WpLock.v:1113   lk_floor_vis  -- own_context ξ -∗ lk_floor ξ lo -∗
                                     own_context ξ ∗ ∃ K, view_lb … K ∗ ledger_vis … K lo
                     (on main: state it with the sealed receipt pair the
                      T-leg's `ledger_vis` reduces to above the seal — the
                      `hart_view_lb K ∗ ⌜lo ≤ K⌝`-or-authorship disjunction —
                      SC body trivial)

Do: add `ctx_wrote` (sealed, SC body `True`), `own_context_w`/`expose_w`/
`ctx_wrote_register`/`own_context_wrote_vis`/`ctx_dom_wrote_floor` with the
T-leg's statements; redefine `lk_floor` with the witness arm; add
`lk_floor_of_wrote`, `lk_floor_morph`, `lk_floor_vis`; delete `log_lb`
(`TsoCtx.v:256` on main) and `log_lb_any` from the shim.  Creators that
minted the floor by `log_lb_any` now register their mint store
(`ctx_wrote_register` at the store leaf — on main the registration is a
ghost step with a trivial body; the T-leg's precedent is
`WpSconfMem.wp_sd_zero_wpay_s_sconf`, A6.120 §6).  Amendment 4.3 item 1's
"swaps into `llb loglen_name` at leg C" is withdrawn: nothing swaps there.

## 5.2  Delete the SC-only re-indexers; the floor moves by its morph (FIX)

`WpLock.is_lock_reindex` / `lock_inv_reindex` (Amendment 5.3) re-mint the
floor from `log_lb_any` to move a lock handle across contexts.  With 5.1 the
floor transports by `lk_floor_morph` (and the persistent handle by the
existing `is_lock` context law); the re-indexers and their `ConsoleInv`
morph clients (`console_inv_morph`/`console_ready_morph` via
`is_lock_reindex`) are re-proved through the morph.  These were false-at-TSO
seams that need not exist.

## 5.3  `locked` / `locked_pre` carry the holder's floor (FIX)

    WpLock.v:147    Definition locked (γ : gname) (i : CPU) : iProp Σ :=
                      (∃ B : nat, lock_frag_at γ (Some (i, true)) B ∗ ctx_floor cur_ctx B)%I.
    WpLock.v:154    locked_pre likewise (Some (i, false))

A holder's context is at or above the winning AMO's position (A6.119 shape
4).  On main `lock_frag_at γ st B` is `lock_frag γ st` with the stamp
exposed (the ghost cell's value carries `B`; the T-leg's
`WpLock.lock_frag_at` is the reference).  Every `locked` destructuring site
gains the `(%B & Hfrag & #Hfl)` pattern; SpecAcquire/SpecRelease/SpecHolding
statements do not change shape (they name `locked`).

## 5.4  `lock_finisher` is two-part (FIX)

    WpLock.v:1683   lock_finisher_body γ lk s R D Out E Pay
    WpLock.v:1701   Definition lock_finisher `{CID} γ lk s R D Out E :=
                      (∃ Pay, (own_context cur_ctx -∗ R cur_ctx ==∗ own_context cur_ctx ∗ Pay)
                              ∗ lock_finisher_body γ lk s R D Out E Pay)%I.
    WpLock.v:1712   lock_finisher_close `{!CtxMorph R}
    WpLock.v:1739   lock_finisher_destroy  (Out = lock_word_fresh lk ∗ lk_cpu_ready lk ∗ Out)

The prelude runs at release's ENTRY (it is where the payload's own
obligations are paid against the running token), the body at the store;
this is what closed `ProofRelease`'s cancel path (A6.120 item 1) and gives
`lock_finisher_destroy` its `lk_cpu_ready` output (consumed by
`PipeInv.pipe_bytes_page_own`).  Main's one-part form (`WpLock.v:671` on
main) is the pre-A6.120 shape.  `SpecRelease.v:95` and `ProofRelease.v:551`
on the reference tree show the call shape.

## 5.5  The acquire-side laws main lists as "T-leg only" are above the seal (LAND)

All statements, SC bodies trivial:

    TsoCtx.v:442    ctx_bound_raise   (main has it; keep)
    TsoCtx.v:1677   ctx_parked_llb
    TsoCtx.v:1692   hart_view_lb_get  -- the honest producer of the acquire-side
                                         receipt at an AMO (main's five
                                         `hart_view_lb_any` sites are its debt;
                                         list them beside it)
    TsoCtxAbsorbLb.v:65   ctx_dom_of_parked_lb
    TsoCtxAbsorbLb.v:105  ctx_absorb_lb  -- absorb a parked record against the
                                            stable pair (hart_view_lb K ∗ ⌜T ≤ K⌝)
                                            with NO interp; the file is 118 lines
    WpLock.v:1256   Definition lock_pay_won (R) -- the record PLUS the acquirer's
                                                  floor at the record's stamp;
                                                  the AMO leaf posts it
                                                  (WpSconfLock.v:2017) and
                                                  ProofAcquire.v:118 absorbs it
                                                  by ctx_absorb_lb

Do: land `TsoCtxAbsorbLb.v` (statements verbatim, bodies trivial), add
`lock_pay_won` and re-cut `ProofAcquire`'s absorb to `ctx_absorb_lb` on it
(replacing the `hart_view_lb_any T0` receipt of Amendment 6.1's acquire
row with the AMO's `hart_view_lb_get`).  Amendment 6.5's row "`TsoCtxAbsorbLb`
absent" is thereby closed; it was never below the seal.

## 5.6  The λ-payload conversion and the morph tactic (LAND)

Main is on the `<{ R }>` const-payload idiom in 176 files (the T-leg: 84).
The T-leg found `const_pay` cannot carry a payload with ξ-dependent facts
and converted the three payloads that have them (A6.121, 197 sites, zero
consumer proof edits):

    TicksInv.v:51    ticks_res_at (ξ)            + Instance ticks_res_at_morph
    ConsoleInv.v:224 cons_data_at / 227 cons_res_at (+ cons_res_at_cur)
    DiskInv.v:917    disk_res_at γ pd pav pu := λ ξ, disk_res (XI := ξ) …
                     920 Instance disk_res_at_morph (closed with the component
                         instances by name)
    CtxMorphTac.v    (53 lines) ctx_morph_solve / ctx_morph_leaf / ctx_morph_leaf_syn

and every `<{ P args }>` site of those three became `(P_at args)`.  Land
`CtxMorphTac.v` and the three twins, then the rename (the T-leg did it by
script; a second pass caught `<{ DiskInv.disk_res … }>` spellings).  This
also answers Amendment 6.2's "priority 0 not honoured at lemma-argument
sites — recorded, not understood": the T-leg's rule is to never rely on
typeclass search for a composite `CtxMorph` — `ctx_morph_solve` applies the
structural instances by name and stops at leaves the caller closes.  Two
gotchas the T-leg paid for, both recorded in `tso-machine-flip.md`:
(i) keep the structural steps BEFORE the `apply`-leaves — a leaf-first order
makes `apply` unify against a whole payload conjunction and diverges
(`DiskInv`, `ConsoleInv` hung >10 min); (ii) an ∃-shaped leaf must be
dispatched by a syntactic `lazymatch` (both `ξ` and `@cur_ctx ξ`
spellings), because `apply ctx_morph_exist` unfolds it and strands its arm.
`ctx_morph_const_pay` keeps its priority-0 fix for the sites that still
write `<{ }>`.

## 5.7  Bookkeeping in the shim and the notes

- Amendment 6.3's two stub sites: name the T-leg items they correspond to —
  the forked child's record is §0.27′ (open on both trees); the secondary
  harts are K15d's started deposit carrying `ctx_parked ξ_pt T` absorbed by
  `ctx_absorb_lb` (`tso-kpt-lane.md`, steps 2–5).
- `hart_view_lb_any` sites: annotate each with "producer at cutover:
  `hart_view_lb_get` at the AMO of …".
- `TsoCtxShim`: after 5.1 it exports `ctx_wrote`-free `log_lb` no more;
  after 5.5 the acquire receipt no longer needs `hart_view_lb_any` at
  `ProofAcquire`.  Re-run the audit that stands in for the seal
  (`grep -l TsoCtxShim`, `proj2_sig .*_aux` outside `TsoCtx.v`).

## 5.8  Gate

Full `-k` build `MAKEEXIT=0`, `audit-only` at the sanctioned thirteen,
dumps unchanged, zero `Admitted`.  Record the slice as Amendment 8 in
`main-tso-readiness.md` with the same tables (landed / SC-only added /
deferred).

# >>> END OF THE WORK <<<

---------------------------------------------------------------------------

## What is deliberately NOT in this slice (and why)

- **A6.124/A6.125 payload shapes** (`DiskAvail.avail_half` in `disk_res`,
  the pin's half ctx cells `hcell_map` in `flight_res`/`parked_res`,
  `keep_map`): statement-level, but they name sealed ledger predicates
  (`phys_ledger_at`, `pin_offer`) and A6.126 is still moving beside them.
  Land later, as sealed names, once the virtio side is closed on the T-leg.
- **A6.126, the release arm** (`ts_rel`, `rel_ok1`, `rel_read`, the
  `_exv_v` leaf, the device's rel store gate): below the seal, T-leg only.
  Its one above-seal residue — a floor beside `disk_done_lb nr` in
  `disk_res` — lands with the item above.
- **§0.27′ / §0.39′ / the U tier (§0.37′)**: unchanged; the stubs stay.

## How the review was done (for the record)

Diffed `origin/main` against `origin/tso-flip` for the context vocabulary
(`ctx_wrote`, `ctx_floor`, `ctx_bound_raise`, `ctx_absorb_lb`,
`hart_view_lb_get`, `own_context_expose_w`, `ctx_dom_wrote_floor`,
`lk_floor_vis`, `lk_floor_morph`, `lock_pay_won`, `lock_finisher_*`,
`lock_openable_c`, `CtxMorphTac.v`, `TsoCtxAbsorbLb.v`, `<{ }>` site
counts) and read Amendments 1–6, `TsoCtxShim.v`, `CtxRecord.v`,
`SieCapCtx.v` and the M2 commit's `TsoCtx.v` diff.  Main's copies of the
M-leg laws are the M-leg's statements verbatim (checked against
`origin/tso`); the deltas above are all T-leg additions after r37.
