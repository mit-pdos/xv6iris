# tso-cutover ENDGAME — PLAN OF RECORD (consolidated 2026-09-02 at 10de366d1)

This file is the current law, the current state and the current order for
landing the TSO proofs on `main`.  It was consolidated from the original
plan and 27 rounds of review, which are kept verbatim in
[`tso-cutover-endgame-log.md`](tso-cutover-endgame-log.md) (cited below as
"log §…").  Nothing here is new: every statement is either in the tree or
in a ruling recorded in the log.  Edit THIS file in place (process rule 6);
append new review rounds to §8/§9 here, not to the log.

**Reading order for a fresh agent.**  `claude-notes/durable-notes.md`; this
file top to bottom; `main-tso-readiness.md` A12 (the round-by-round record
of what landed, with measured counts); then, only when touching the box or
its instances, `iris/CtxBox.v`'s Section box (the statements ARE the law)
and, on `origin/tso-flip`, `claude-notes/design/tso-escrow-endgame.md` §1
(allowed forms), §2 (the box), §5 (process rules and tripwires).  The
owner rulings the whole port runs under are `tso-port.md` §0.x′ on
`origin/tso` (§0.23′ main moves once; §0.24′ the U tier deferred; §0.25′
the three-case gate; §0.26′ visibility-free free pages).

---------------------------------------------------------------------------

## 0. Status

- Branch `tso-cutover` (off `main`; worktree `/shared/xv6iris-2-main`, VM
  tree `_shared_xv6iris-2-main`) is the ONLY vehicle.  `tso-flip` is
  finished (handoff `tso-machine-flip.md` A6.163 on that branch) and is a
  read-only source of proof text.  No WIP side branches.
- Every green boundary is banked on `tso-cutover` as a numbered round;
  `main` is merged INTO the branch at every bank; `main` moves ONCE at the
  end.
- Rounds banked: r1–r13 (machine, ctx, lock, page, proc, kernel proofs,
  U tier, virtio), r14 (bcache over the box), r15–r18 (icache reference
  tier, IcacheInv per-slot fusion), r19a–r19i (IcacheEscrow/IcacheBoot
  over the box, the two CtxBox edits, the read arm), r20a (inode specs),
  r20b-1..5 (ProofIunlock, ProofIunlockput, ProofIdup, ProofIlock,
  ProofIreclaim green over the box), r20b-6 (ProofIget, 8cb002042),
  r20b-7 (ProofIput; `IcacheCover.v` = item 2).  In flight: the full
  measure after r20b-7, then r20c (the hook slot-in) and r21.

---------------------------------------------------------------------------

## 1. Where the tree stands

### 1.1 The honest measure (never `ls *.vo`; recipe in §10.2, tool `tools/cone.py`)

| build | roots | blocked | green | of |
|---|---|---|---|---|
| ic8 (0f3c7a5d0, start of this plan) | 13 | 361 | 1132 | 1506 |
| after r19a (ProcInv root closed; cone re-enumerated) | 29 | 272 | 1205 | 1506 |
| after r20a (specs stitched) | 33 | 138 | 1335 | 1506 |
| after F38/F39 (5beee236b; root SET unchanged) | 33 | 138 | 1336 | 1507 |

The rule from log §6¹⁰: after every sweep re-run the measure; the green
count must not drop, and for every file taken from flip `git diff main --
<file>` is scanned for REMOVED conjuncts that never reappear.

### 1.2 The roots, by class (the r19a re-enumeration; see A12.6)

| class | what | lane |
|---|---|---|
| the inode proofs and the FS-cone consumers of the new reference/box forms | ProofIget, ProofIput, FsCollectAll (`ic_slot_cover`), the `*AU*` and era files that spell descriptors | icache r20b/r21 |
| shim bridges (`TsoCtxShim.`) in the ProcInv cone | ProofArgfd, ProofSysPause, ProofSysKill, ProofForkretParts, and the 26 files of §6 L2 | L2 |
| name drifts vs flip | SpecProcinit (`lk_cpu_ready_intro`), ProofSysSbrk, ProofSysExec | L2 |
| the pipe proofs | `page_own_pipe_raw` gone | L3 |
| RiscvAdequacy | the era allocation's type error | L4 |

Pre-existing `Admitted` on main, OUTSIDE the port's gate: `FsShPin`,
`ProofKexecA/B/PinnedA`, `ProofIalloc`, `ProofKforkMain`, `ProofSyscall`
(4), `ProofVirtioDiskRwF`, `UkShParse`.  The port's OWN Admitted inventory
today: `OffBox.v` (14, the R4b skeleton, §6 L6) — nothing else.

---------------------------------------------------------------------------

## 2. The law (inherited; the two additions from this lane are marked NEW)

1. **THE STITCH RULE** (owner, 2026-09-01).  tso-flip for the PHYSICAL
   words of memory (ownership, bounds, contexts, floors, stamps, the transit
   box for cross-lock cells); main for the GHOST state of the durable disk
   (descriptors and the `ln_tx` shares they park, the arm-keyed registry,
   corpse/transit ledgers, the pool partition, freeze receipts).  Stitched
   at the boundary = CtxBox's parameter list.
2. **Copy flip, invent nothing.**  Where flip has a proof of the same
   statement, take its text; record residual differences.  SC-only lemmas
   added on this branch are flagged (§9 item v).
3. **The allowed-forms law** (flip endgame §1): a physical cell is T1
   (running context, exact), T2 (parked at a stamped context inside a
   box/lock record) or T3 (ledger pin above a floor; racy reads).  Inv
   bodies hold only ξ-free ghost, T2 custody with ξb ∃-packed, or T3 pins.
   Lock payloads are context-λs.  Floors only by the llb-tier acquire
   posts (R1) and payload floor rows folded at release (R2).  `cred_floor`
   is never a substitute for `ctx_floor`.
4. **Two spellings per resource** (holder / parked); references have ONE
   ghost-only spelling.  No interim wrappers; one sweep to the final form.
5. **The box is law** (§3).  A box lemma appeals to nothing beyond the
   declared parameters.  Tripwires (flip endgame §5.7) apply: a new
   transition, a fourth arm shape, a second reference form, a per-site
   floor, a stamp agreement between holders, anything ξ-indexed in a
   residue, a new box ghost.
6. **Site-map first**: no box client is coded before its site table (lock
   context, transition letter, the row that discharges its cover) is
   written and vetted.  §5 is that table for the icache.
7. **Main moves once** (§0.23′): the branch lands as one merge when the
   full `-B` build is green, `make audit` is at baseline and the port's
   own Admitted count is zero.
8. **§0.24′** deferred the U tier on flip; here it is ordinary work,
   already green except behind ProcInv's cone.
9. **NEW — THE RESIDUE TRIPWIRE** (log §6¹³/§6¹⁷): every arm of a residue
   must be SELECTABLE by every party that receives that residue back or
   discharges a wand over it, from what that party holds alone; and
   READABLE with its identity tied to the slot's, or REFUTABLE, by a viewer
   that holds no register — on EVERY state the box's rows admit, not only
   the states the program reaches ("no site produces that state" is
   prose; reachability is not a resource).  Residues are indexed by arm
   (and, at OUT_L1, by count) so the first clause can be met at all.
10. **NEW — THE HOOK CONVENTION** (log §6²⁶/§6²⁷, ruled recommended):
   every transition that moves a header takes ONE client hook
   `Qc ∗ <arm content> ={E∖↑N}=∗ <arm content'> ∗ Q'` run at the
   transition's own step; a new client need is met by the hook of the
   transition it belongs to, never by a per-lemma variant.  Plain forms
   are corollaries at the identity hook.  The consolidating edit is
   scheduled (§7, before r21).

---------------------------------------------------------------------------

## 3. The box as it stands (`iris/CtxBox.v` Section box; 0 Admitted)

### 3.1 Parameters and arms

| parameter | meaning |
|---|---|
| `P_hdr : id → X → CtxId → iProp` | the header: identity-bearing cells + the client's IN-arm ghost (CtxMorph, Timeless) |
| `P_rest : X → CtxId → iProp` | the rest of the bundle (stays IN the box during OUT_L1) |
| `Q1 : nat → iProp` | the OUT_L1 residue, indexed by the body's COUNT (stable across a window: (c)/(d) need win = false) |
| `Q2 : iProp` | the OUT_L2 (checkout) residue |

No token, no `P_hdr_excl`/`P_rest_excl`: the arm is SELECTED by the two
register halves (log §6⁶(A)).  `box_arm γ T ξb m c r s` is PUBLIC:

| (lr_hold s, sr_win r) | arm | content |
|---|---|---|
| (None, false) | IN | `∃ x, P_hdr (sr_ident r) x ξb ∗ P_rest x ξb` |
| (None, true) | OUT_L1 | `hdr_out γ m ∗ (∃ x, ⌜sr_x r = Some (x,T)⌝ ∗ P_rest x ξb) ∗ Q1 c` |
| (Some (i, mh), _) | OUT_L2 | `⌜sr_win r = false⌝ ∗ ⌜mh ≠ ∅⌝ ∗ ⌜keyed mh i⌝ ∗ stamps_frag γ mh ∗ Q2` |

The four pure rows `box_rows` (Σ, I, C, D) are unchanged from flip's v2.
The box owns exactly: the parked context, stamps, cnt, slot_d, slot_p.

### 3.2 The statements (fifteen at HEAD; one drafted)

| letter | lemma | hook / residue | status |
|---|---|---|---|
| (a) | `box_withdraw_L1` | takes `Q1 c` | landed |
| (b′) | `box_deposit_L1_shape` | x0 → x1 entailment on `P_rest`; returns `Q1 c`; mints the unit at `max 1 c` | landed |
| (b) | `box_deposit_L1` | instance x1 := x0 | landed |
| (b″) | `box_deposit_L1_join` | `Qc`, `P_hdr'`, view-shift join `∀ ξ', Qc ∗ Q1 c ∗ P_hdr' i' x1 ξ' ={E∖↑N}=∗ P_hdr i' x1 ξ' ∗ Q'`; (b′) is its instance | ruled ACCEPT (log §6²⁵/§6²⁶/§6²⁷); BUILT side-by-side as `CtxBoxHooked.box_deposit_L1_hook`, with F14's x0 → x1 folded into the same hook (§3.2b) |
| (c) | `box_ref_incr` | needs win = false | landed |
| (d) | `box_ref_decr` | needs win = false | landed |
| (e′) | `box_checkout_split` | `Qc`, `P_hdr'`, view-shift split `∀ x ξ', Qc ∗ P_hdr i x ξ' ={E∖↑N}=∗ P_hdr' i x ξ' ∗ Q2` at ξb before the absorb | landed |
| (e) | `box_checkout` | instance Qc := Q2, P_hdr' := P_hdr | landed |
| (f′) | `box_park_join` | `Qc'`, `P_hdr'`, join `∀ x ξ', Qc' ∗ P_hdr' i x ξ' ∗ Q2 ⊢ P_hdr i x ξ' ∗ Q'` (pure) | landed |
| (f) | `box_park` | instance Qc' := emp | landed |
| (g) | `box_l1_to_l2` | takes `Q2`, returns `Q1 1` | landed |
| accessor | `box_q_update` | under the L2 half: `Q2 ={E∖↑N}=∗ Q2 ∗ R`, returns `l2_hold ∗ R` | landed |
| accessor | `box_q1_update` | under the L1 half at win = true and the cnt half: `Q1 c ={E∖↑N}=∗ Q1 c ∗ R` | ruled ACCEPT; BUILT side-by-side as `CtxBoxHooked.box_q1_update` (§3.2b) |
| view | `box_view` | opens the inv for a non-owner: rows + `box_arm` + closing wand | landed |
| boot | `box_alloc`, `box_alloc_at`, `box_alloc_at_halves` | born IN at T_boot | landed |

**The scheduled consolidation (law 10; §7 r20c).**  The hooked forms become
THE statements — (a), (b), (e), (f), (g) each with the hook — and the plain
forms become corollaries; `box_q_update`/`box_q1_update`/`box_view`
unchanged.  Blast radius: the direct callers of `CtxBox.box_*` are
`BioInv`, `FsCfgKits`, `IcacheRef`, `IcacheBoot`, `IcacheEscrow`, `OffBox`;
no inode proof calls a box lemma.  bcache and off instantiate every hook
with the identity.

### 3.2b The consolidated box, BUILT side-by-side (`iris/CtxBoxHooked.v`, 2026-09-02) — SLOTTED INTO CtxBox.v at r20c (A12.18); the side file is gone, the names below live in CtxBox

At the owner's instruction the consolidation is built now, beside
`CtxBox.v` and not in its place, so it is ready the moment a wrapper needs
another extension or the cleanup pass (r20c) is scheduled.  The file is in
`_CoqProject` after `CtxBox.v`; it imports CtxBox and REUSES its ghosts,
arms, rows, body, `is_box` (the SAME predicate, so one box may be driven by
both files' lemmas), the reference kit, (c)/(d), `box_q_update`, `box_view`
and boot unchanged.  It adds:

| lemma | hook (all at the box's mask `E ∖ ↑N`, the box open) |
|---|---|
| (a) `box_withdraw_L1_hook` | `∀ x ξ', Qc ∗ P_hdr i x ξ' ={E∖↑N}=∗ P_hdr' i x ξ' ∗ Q1 c` at ξb before the absorb (§6¹³'s "(a′)", now present) |
| (b) `box_deposit_L1_hook` | `∀ ξb, Qc ∗ Q1 c ∗ P_hdr' i' x1 ξ ∗ P_rest x0 ξb ={E∖↑N}=∗ P_hdr i' x1 ξ ∗ P_rest x1 ξb ∗ Q'` before the deposit -- (b″) with F14's shape change inside the hook |
| (e) `box_checkout_hook` | = `box_checkout_split` as landed |
| (f) `box_park_hook` | `box_park_join`'s join as a view shift |
| (g) `box_l1_to_l2_hook` | `Qc ∗ Q1 1 ={E∖↑N}=∗ Q2 ∗ Q'` at ξ, on the residues only |
| accessor `box_q1_update` | under the L1 half at win = true and the cnt half: `Q1 c ={E∖↑N}=∗ Q1 c ∗ R` |
| corollaries | `box_withdraw_L1`, `box_deposit_L1_shape`, `box_deposit_L1`, `box_checkout_split`, `box_checkout`, `box_park_join`, `box_park`, `box_l1_to_l2` -- CtxBox's names, CtxBox's statements |

No hook sees a register, a stamp, the count or a row.  Each hooked proof
is CtxBox's proof of the plain form with one `iMod (Hhook …)` where that
proof read the client content; the corollaries are one-line identity
instantiations.

VERIFIED on the VM at 10de366d1: compiles by `coqc` and through
`CoqMakefile` (5.8 s), no Admitted, `Print Assumptions` of the hooked
deposit closed under the global context, and each of the eight corollaries
type-checks AT CtxBox's exact type (`(@CtxBoxHooked.<name> : type of
@CtxBox.<name>)`), so a client switches `CtxBox.<name>` →
`CtxBoxHooked.<name>` with no other change.

USE NOW: a wrapper that needs a hook calls `CtxBoxHooked.<name>_hook` with
CtxBox's leading arguments (`P_hdr P_rest Q1 Q2 N γ …`); everything else
stays on CtxBox.  Open item 1 (the recycle) can take `box_deposit_L1_hook`
and `box_q1_update` from here instead of landing (b″) in CtxBox.v.

SLOT-IN (r20c, one edit, F30 precedent): move the five `_hook` lemmas and
`box_q1_update` into CtxBox.v's Section box; make CtxBox's
`box_withdraw_L1`, `box_deposit_L1_shape`, `box_checkout`,
`box_park_join`, `box_l1_to_l2` the one-line corollaries this file has (the
other three already are); delete `CtxBoxHooked.v` and its `_CoqProject`
line.  The six direct callers do not change.

### 3.3 Instances

| instance | file | id | X | P_hdr | Q1 | Q2 | namespace |
|---|---|---|---|---|---|---|---|
| bcache | `BioInv` | (dev, blockno) | — | the buffer's cells | `λ _, emp` | `emp` | `bioxN .@ k` |
| icache | `IcacheEscrow` | `ic_bid = option (dev*inum)` | `ic_x = IcRaw / IcUnloaded g / IcLoaded g dn bm` | `ic_hdr` (§4) | `ic_q1` (§4.3) | `ic_q2` (§4.3) | `icBoxN .@ k` |
| off (R4b) | `OffBox` | the file slot k | unit | `off_hdr` (the one `off` cell) | `λ _, emp` | `emp` | `offBoxN .@ k` |

Per-slot namespaces because the commit's collection opens all fifty
icache boxes inside one fupd (log §6″ P1).

---------------------------------------------------------------------------

## 4. The icache instance as landed (`IcacheEscrow.v`, `IcacheInv.v`, `IcacheBoot.v`; 0 Admitted)

### 4.1 Who owns what (the stitch, per object)

| concern | from | objects |
|---|---|---|
| the count word `i_ref`, its racy reads and stores | flip | `iref_pin_rows` (four `phys_ledger_pinw` bytes), `pinw_slot`, `icfg_istmp k` stamp halves, `iref_load_pinw_au`, the `*_store_pinw_au` family; each cutover accessor = flip's WINDOW + main's REGION STEP (`ireg_icnt_*_acc`, `frz_*`) at the same instruction (table in log §3.3) |
| identity/valid/nlink/dinode cells across itable.lock ↔ ip->lock | flip | the box: `P_hdr = ic_hdr`, `P_rest = ic_rest`, `X = ic_x`, L1 row `ic_slot_row`, L2 λ payload `ic_slp` |
| liveness and its epoch | flip | `live_genlo`, `live_fracc`, `cred_floor lo tl`, `ic_ref_stamps`; `inode_ref := iref_frag ∗ live_fracc ∗ slh_tok ∗ inode_ident ∗ ic_ref_stamps` |
| lock tiers | flip | `is_sleeplock_genl` over `ic_slp`; `wp_acquiresleep_nb_genl_llb_sconf` at Tl := 0 for iput's free path |
| durable-disk descriptors | main | `ic_dep = DepNone \| DepTx s dev inum g t q lo \| DepRd … \| DepFrz q dev inum t qt` (`DepRef` DELETED, F39); `ic_deposit cn k d := ghost_var (icn_dep cn k) ½ d` (its own client ghost, NOT the box's token); `ic_dep_neutral` = the whole at DepNone |
| the reader's quarters, freeze pins | main | `ic_out_rd`/`ic_rd_arm`, `ic_pin_tx`/`ic_pin_rest`, `hpn_h`, `frzidx`/`frz_mir`/`runit` |
| inum-keyed ledgers and the pool | main | `ipool_inv` (`ipoolN`), `ipool_transit`/`ipool_corpse`, `ic_id` quarters, `ic_live_inums`, `ipool_cover_inum` |
| what the commit reads at quiescence | main | `FsCollect`/`FsCollectAll`: `ic_slot_cover` (to be re-stated over `box_arm`, §5 last row) |

### 4.2 Placement of main's ghost (the decided layout)

- **Identification `ic_id cn k q b dev inum`** (a `ghost_var`; a flip needs
  every fraction in one hand): the TABLE row keeps ½ (`islot2` live,
  `islot_empty` dead); the box HEADER carries ¼ (`ic_hdr (Some (dev,inum))
  x` at `true`; `ic_hdr None IcRaw` at `false` with ∃-bound values); the
  POOL invariant ¼.  Boot splits 1 → ½ + ¼ + ¼.  `sr_ident` and `ic_id`
  agree by the header's definition (one identity truth, P3).  During
  OUT_L2 the header's quarter rides `Q2` (moved by (e′), back by (f′)) so
  the viewer can tie a `DepRd` arm's leg to the slot's inum (F40); the
  held header `ic_hdr_held … (rd : bool)` is the header minus the quarter,
  arm-aware (at `rd = true` the payload keeps only the reader's quarter
  leg).
- **The resting pin `ic_pin_rest k = hpn_full k None`** rides the TABLE ROW
  (dead row `islot_empty`; live row's `frz_park` OFF arm), NOT the header
  (F42: the guard must produce its `Q1 1` before (a) opens the box).  While
  a window is open the row carries no pin (the guard's row rides the
  window as `ProofIput.ip_row_open`; the frozen park's ON arm has none,
  F42′): ONE half of the pin cell is in an invariant-visible place -- the
  guard's `Q1 1`, then `Q2`'s `DepFrz` side, then the frozen alternative
  (`frzsel … ∗ ic_pin_tx`), then the last close's `Q1 1` -- and the OTHER,
  the NAME-half, never leaves iput's hand: the last close's (a) is the
  HOOKED form (`ic_evict_withdraw_frz`), whose hook moves the frozen
  alternative's own pin into `Q1 1`, never the hand's (Q10, §9 item 9;
  condition (3) corrected here).
- **Descriptor halves**: the holder's half rides the handle
  `ic_handle cn k d := ic_deposit2 k d ∗ ic_pay_live k d ∗ ic_deposit cn k d
  ∗ ic_tok cn k` (the sleeplock token rides the handle across the hold and
  `ic_slp` while free); the arm's half rides `Q2`.  Two things were named
  `ic_deposit`: on this branch it is main's HALF; flip's proofs use the
  name for the HANDLE — `sed 's/\bic_deposit\b/ic_handle/g'` on the flip
  copy BEFORE any 3-way merge (log §6¹⁰).
- **`DepFrz` kept** (main's freeze window parks a `(t, qt)` share, durable
  ghost) and `ic_dep_id (DepFrz …) = Some (dev,inum)` (needed by `Q2`'s
  identity tie at (g); safe because `ic_body` at DepFrz is `False`, so no
  checkout/park is callable on it).
- **`ic_park` rejoins the descriptor halves inside the wrapper** and
  returns `ic_dep_neutral cn k ∗ ic_park_side d` (`emp` at DepRd: the three
  quarters went home through the join; the tx share otherwise).  Only the
  shrink/grow updates (`box_q_update`, output residue R) ever see the
  halves apart.
- **No empty arm**: an evicted slot is IN at `None` with `X = IcRaw`.
- **`ipool_inv`** stays a separate invariant, opened beside the box in the
  same step where main did.

### 4.3 The residues

```
ic_q1 cn k 0     := ic_q_recycle cn k                (∃ dev inum, ic_id cn k ¼ false dev inum)   -- F38/F44
ic_q1 cn k (S _) := ic_pin_tx k                      (the guard's hpn half + tx share)
ic_q2 cn … k     := ∃ d dev inum, ⌜ic_dep_id d = Some (dev,inum)⌝ ∗ ic_deposit cn k d
                    ∗ ic_q_side … k d ∗ ic_id cn k ¼ true dev inum                                 -- F40
ic_q_side d      := DepTx ↦ tx_pin t q | DepRd ↦ ic_rd_arm inum (the 3/4 leg)
                    | DepFrz ↦ iref_frag k qf ∗ frzsel k ¼ true ∗ tx_pin t qt | DepNone ↦ False
```

PENDING (ruled, not landed — §9 item 1): `Q1 0` becomes TWO-ARMED,
`(∃ dev inum, ic_id ¼ false dev inum) ∨ (∃ dev inum, ic_id ¼ true dev inum
∗ ipool_shape_np … inum)` — main's MID arm re-homed in the residue, for the
recycle window between the pool take (+0x72) and the deposit (+0x7c).

Viewer check (law 9), state by state, from `box_view` + the pool's quarter
+ the empty `ln_tx` authority: IN — read `ic_hdr`'s ghost leg, identity by
the quarter; OUT_L1 c = 0 dead arm — read dead / refuted if the pool says
live; OUT_L1 c = 0 live arm — read as an unloaded live slot, identity
tied; OUT_L1 c ≥ 1 — the pin's tx share refuted at quiescence; OUT_L2 —
DepTx/DepFrz refuted by their shares, DepRd read with the identity tied.

### 4.4 The wrappers (client lemmas over the box; all in `IcacheEscrow.v`)

| wrapper | box lemma | notes |
|---|---|---|
| `ic_hit_incr` | (c) | iget scan hit, `ref++` |
| `ic_recycle_withdraw` | (a) at c = 0, `sr_ident = None` | takes `ic_q_recycle`; returns the dead header |
| `ic_recycle_flip` | `CtxBoxHooked.box_q1_update` at c = 0 | `ipool_take_lend` inside, the four-quarter flip, `Q1 0` back in its live arm (Q8/Q9) |
| `ic_recycle_deposit` | `CtxBoxHooked.box_deposit_L1_hook` at c = 0 to `IcUnloaded g` | the join: `ic_hdr_bare` + the payload ghost + the residue's live arm; `Q'` = the table's ½ |
| `ic_checkout` | (e′), pure split | write arm and any non-read descriptor (`ic_dep_rd d = false`); returns the HELD header |
| `ic_checkout_rd` | (e′), view-shift split | premises `itable_inv`, `ity_shot g ty`, `↑icacheN ⊆ E`, `k < NINODE`; refutes the frozen alternative by `frz_slot_kill_pinw`, the unloaded shape by the one-shot, sheds the leg into `Q2` |
| `ic_park_hold` / `ic_park` | (f′) with `Qc' := ic_deposit cn k d` | returns `ic_dep_neutral ∗ ic_park_side d` |
| `ic_guard_withdraw` | (a) at c = 1 with the unit | takes `ic_pin_tx k` (produced from the table row before the call) |
| `ic_guard_deposit` / `_gen` | (b) at c = 1, no bump | returns `ic_pin_tx k` |
| `ic_evict_deposit` | (b′) at c = 1 to `None`/`IcRaw` | the identity flip (table ½ + header ¼ + the pool's lent ¼) happens BEFORE the call, `ipool_inv` open; the unit is re-minted at `(None, T')` |
| `ic_free_take` | (g) | takes `ic_q2` (a `DepFrz` residue), returns `ic_pin_tx k` and the L2 hold |
| `ic_park_frz` | (f′) at the frozen alternative, `P_hdr' := ic_hdr_bare` | the join builds the alternative from `Q2`'s selector quarter and the re-entered pin |
| `ic_evict_withdraw_frz` | `CtxBoxHooked.box_withdraw_L1_hook` at c = 1 | Q10 option B: the hook decides the frozen arm (`ifreeze_excl`) and moves its pin into `Q1 1`; returns `ic_hdr_frz` (cells, `frzsel ¼`, quarter, `ifreeze_pre`) |
| `ic_box_alloc_at` | boot | fifty boxes at `icBoxN .@ k`, stamps at 0 |
| (r20/r21) shrink/grow | `box_q_update` | main's `ic_shrink_tx`/`ic_grow_tx` re-stated over the accessor |

---------------------------------------------------------------------------

## 5. The site map (current; supersedes log §3.4.3)

| site | lock | box step(s) | main's ghost step kept |
|---|---|---|---|
| iget scan hit, `ref++` | itable | `ic_hit_incr` | `ireg_icnt_acc` |
| iget recycle: `ref := 1` at +0x78, valid/dev/inum stores, (b) at +0x7c | itable | `ic_recycle_withdraw` (a); at +0x72 `box_q1_update`: `ipool_take_lend` with the pool open at the box's mask, the four-quarter flip (table ¼ + header ¼ + `Q1 0`'s ¼ + the lent ¼), the lend closed with ½ at the new identity, `Q1 0` put back in its LIVE arm with the taken `ipool_shape_np`, the ledger pair out for +0x78; at +0x7c (b″): the join receives `Q1 0`, selects the live arm by agreement with the table quarter in `Qc`, rebuilds the header at `IcUnloaded g`, `Q'` = the table's ½ | `ipool_take_lend`, `ic_id` flip, `ic_mk_unloaded`'s ghost leg |
| ilock checkout (write) | ip->lock | genl_llb acquire at Tl := the share's stamp; `ic_checkout` | mint `DepTx`, park the `ln_tx` share into `Q2` |
| ilock checkout (read) | ip->lock | `ic_checkout_rd` | `DepRd`: the 3/4 leg into `Q2`, the holder keeps the quarter |
| ilock's `valid == 0` load | ip->lock | on the held bundle | `ic_mk_loaded` |
| iunlock park | ip->lock | `ic_park` / `ic_park_hold`; `_in` releasesleep re-floors the row | halves rejoined to `DepNone` |
| shrink/grow under two write locks (create, unlink) | ip->lock ×2 | `box_q_update` with R | `ic_shrink_tx` / `ic_grow_tx` |
| iput non-last close | itable | (d) | `ireg_icnt_acc` |
| iput `ref == 1` guard (valid, nlink reads) | itable | pin taken from the table row → `ic_guard_withdraw`; reads off the header in hand; Exit A: `ic_guard_deposit` | `hpn_h`, `ic_pin_tx` |
| iput free path | itable then ip->lock | acquiresleep NB at Tl := 0; `ic_free_take` (g) with a `DepFrz` residue; itrunc/iupdate on the bundle; park through `ic_park_hold` | `frz_slot_freeze`, `frz_rcpt`, the corpse/transit ledgers |
| iput last close / eviction | itable | flip `ic_id` to false with the pool open; `ic_evict_deposit` (b′) to `None`; (d) at the count store, whose region step yields `icnt_half 0` for the pool insert | `ireg_icnt_lic_acc` / `_frz_acc`, `ipool_evict_lend` |
| the commit's collection at quiescence (`FsCollect`, `FsCollectAll`) | none | `box_view` on all fifty boxes in one fupd; `ic_slot_cover` stated over `box_arm` by the §4.3 case table | `ipool_cover_inum` unchanged |
| fileread/filewrite/filestat share-holders | ip->lock via ilock | as ilock/iunlock with the share's mass | `DepTx`/`DepRd` |

Two tripwires to set before r21 (log §6²⁷): state `ic_slot_cover` over
`box_arm` now, type-checked, before ProofIget/ProofIput finish; and give
the recycle wrapper ALL of `ipool_take_lend`'s mask premises (`ipoolN`,
`iregN`, `escAN inum` inside the box's mask), as `ic_checkout_rd` states
`icacheN`.

---------------------------------------------------------------------------

## 6. The lanes after the icache

L1. **ProcInv keystone — CLOSED** (r19a): flip's shim-free proofs of
    `tf_word_phys_to_mem` (A6.58/A6.69) replaced the shim; the cone
    re-enumerated (§1.2).

L2. **The shim sweep** — the 26 blocked files + `ProofSysKill`; heaviest:
    `BootCarveMain` (67 mentions), `BootShared` (38), `ProofKexecTail`
    (11), `ProofSysRead`/`ProofSysWrite` (10 each), the `*AU*` main-only
    four (`ProofSysReadAU`, `ProofSysWriteAU`, `ProofSysWriteConsAU`,
    `UkStep`: same treatment their non-AU twins got).  Per file: flip's
    twin via `tools/takeflip.sh` / `tools/merge3.sh`; `ProofForkretPark`
    stays red at its `park_globals` bullet until L8.  INDEPENDENT OF THE
    BOX; run in parallel now (§7).

L3. **`ProofPipealloc`** — restate the pipe page at `page_named` /
    `page_filled` as `ProofPipeclose` does.  Independent; parallel.

L4. **`RiscvAdequacy`** — the era allocation's type error, then the 17
    files behind it.  Independent; parallel.

L5. **R4a `inode_pay`'s cinv** (`FileInvDefs`): ghost identity for the
    parked ident cell fractions; park the ξ-free `inode_shr_genlo_bare`;
    the credential stays on the borrower; parked shares in the F21 form
    (`∃ m, ◯ m ∗ llb …`) from the FIRST sweep.  The cinv becomes
    ghost+pure ⇒ `is_ftable`'s λ-flip stops recursing into it.

L7. **The const-payload class**: `is_ftable`'s `<{ ftable_res γ }>` → a λ
    with a FLOOR SLOT (R4b needs `ctx_floor ξ Kd` from ftable's payload
    row, and every ftable release at filealloc/filedup/fileclose becomes an
    `_in` release — F36, which is why L7 precedes L6); `LogInv`'s
    `<{ log_res }>` (run the `ctx_move_const` test first); `IcacheInv`'s
    dead `<{ itable_res }>` (delete).

L6. **R4b: THE OFF BOX** (`OffBox.v`, skeleton type-checked, 14 Admitted).
    Mandatory: main's off ledger put `a_foff k ↦₄ v` at the ambient context
    in a ξ-bodied invariant and parks the inode's `valid` cell as a marker,
    both unlawful under the box.  The design, as ruled:
    - born at FILEALLOC under ftable.lock (`box_alloc_at` with the free-slot
      row's cell, then (c) minting the exclusive unit at T_boot); identity
      = the file slot k, never changes (no (b)/(b′) ever); the L1 half stays
      in ftable's payload (`off_l1_row`) for the box's whole life;
    - PUBLISH = an L2 operation under ip->lock in sys_open: (e) with the
      owner-held L2 half (cover (C)-left through the unit's birth stamp;
      the ilock presents Tl := max of the inode share's stamp and the off
      box's birth stamp), write `f->off = 0` on the cell in hand, (f), then
      APPEND the row to the inode payload's set;
    - the inode payload `ic_slp` gains a per-slot APPEND-ONLY set
      `own (γset i) (● L)`, `L : gset box_names` (Countable derived; F35),
      with `[∗ set] γ ∈ L, ∃ s, off_l2_row γ s ξ ∗ llb (lr_tp s)`; the fd
      row's FD_INODE arm carries `is_box γ ∗ off_member (◯ {[γ]})`, so a
      fileread holder selects ITS row by membership and puts it back; the
      `_in` releasesleep folds every row at tl := the maximum; stale rows
      (dead γ) stay forever, bounded by the publishes to that inode;
    - fileread/filewrite: (e)/(f) through membership; filedup (c) and
      non-last fileclose (d) under ftable.lock; last-ref fileclose: (a) at
      c = 1 with the gathered unit (mass 1 per counted reference, the
      share's fraction for a share, the lending parent the complement —
      F34), the cell back to the free-slot row, the box abandoned;
    - `Q1 := λ _, emp`, `Q2 := emp` (the collection never looks at
      `f->off`); no token (§3.1).
    Client shapes implied (F37): fslot's allocated arm carries `off_l1_row`
    + the L1 floor row; the free arm the cell and no box; a big-op CtxMorph
    lemma and a big-op llb-max lemma (`off_rows_morph`, provable now).
    COST WARNING (log §6²⁷): L5, L6 and L7 touch the SAME six proofs
    (filealloc, filedup, fileclose, sys_open, fileread, filewrite) and L6
    changes `ic_slp`'s release fold at every iunlock (10 files, the seven
    inode proofs among them).  Decide the three final shapes (`inode_pay`,
    `ftable_res`, `ic_slp`) together and sweep the file layer ONCE; fix
    `ic_slp`'s final shape (the off-row conjunct + one fold lemma) before
    r21's consumer sweep so the inode proofs are not reopened.

L8. **R5**: the recorded reverts on flip (`is_ftable` λ-flip consumer
    re-spells, `park_globals_move`), `bio_ctx`'s λ-flip if any remains, and
    `ProofForkretPark`'s `park_globals`/`proc_priv` bullets (the A6.141 §3
    unfold tower; the child twin is born dominating its parker).

L9. **R6 bucket C**: `LinkForkretParkPaid` → `LinkUserinit` → `LinkMain`
    → `BootChain`/`BootShared` → `SystemAdequacy`.  First honest compile of
    text written while unbuildable; budget a fallout tail.

L10. **Loose ends from flip** (A6.163): `IcacheBox.v` stub — not carried;
    flip's tracked `*.aux` and `ZZ*` — never; `tso-flip-umode` r1 — take
    only what r12's U-tier wave lacks.

---------------------------------------------------------------------------

## 7. Order, gates, banking

| round | content | gate |
|---|---|---|
| r20b (in flight) | ProofIget (with (b″) + `box_q1_update` + the two-armed `Q1 0`, §9 item 1), ProofIput; `ic_slot_cover` STATED over `box_arm` | the seven inode proofs green |
| r20c | THE HOOK CONSOLIDATION (law 10): hooked forms become the statements for (a), (b), (e), (f), (g); plain forms as corollaries; the six wrapper files retargeted | CtxBox/BioInv/IcacheEscrow/OffBox green, 0 Admitted in CtxBox |
| r21 | the FS-cone consumer sweep incl. FsCollect/FsCollectAll (the acceptance test); `ic_slp`'s final shape; merge `main` | THE ICACHE BANK: honest green ≥ 1336 + the icache cone; zero new admits |
| PARALLEL, starting now (a second agent) | L2 shim sweep, L3 pipe, L4 RiscvAdequacy | no `TsoCtxShim.` outside comments; RiscvAdequacy green; measure re-run after each sweep, green never drops |
| r25 | the file layer as ONE sweep: L5 + L7 (the `is_ftable` λ-flip with the floor slot FIRST) + L6 (OffBox's 14 proofs) | no ξ-bodied cinv left; OffBox 0 Admitted |
| r26 | L8 | ProofForkretPark green |
| r27 | L9 | SystemAdequacy green |
| r28 | forced `-B` certification, `make audit`, admit inventory, delete `ctx_word4_claim` / the TsoCtxShim tombstone / dead `itable_res`; final `main` merge-in | zero red, audit at baseline |
| land | one merge `tso-cutover` → `main` (§0.23′) | owner |

Every round: `git pull` first (main and any sibling agent on
`tso-cutover`), build on the VM, record the honest measure in the round's
Amendment (`main-tso-readiness.md`), commit with explicit paths, push.

---------------------------------------------------------------------------

## 8. Rulings table (what was decided, one line each; the argument is in the log)

| id | ruling | status |
|---|---|---|
| F31 | the read checkout's 3/4 leg cannot be a premise of (e): (e′) with a client split wand | landed |
| F32 | the collection must see the guard's pin: an OUT_L1 residue | landed (as Q1) |
| P1 | per-slot box namespaces (`icBoxN .@ k`, `bioxN .@ k`) | landed |
| P2 | the collection's read is ATOMIC (inside one fupd); no lent-fraction shape | decided |
| P3 | one identity truth: the `ic_id` quarter rides the header (½ / ¼ / ¼) | landed |
| P4 | the off box: born at filealloc, publish = (e)/(f) under ip->lock, identity = the file slot, append-only set keyed by `box_names` with a membership witness | skeleton landed |
| P5 | parked shares in the F21 form from the first sweep | for L5 |
| §6⁶(A) | arms selected by the two registers; no tok / `_excl` | landed |
| §6⁶(B) | (f′) `box_park_join` beside (e′) | landed |
| F33 | (e′) takes a caller residue `Qc` | landed |
| F34 | the off box's mass rule: 1 per counted reference | in the skeleton |
| F35 | the off set keyed by the whole `box_names` record | in the skeleton |
| F36 | R4b depends on the `is_ftable` λ-flip + a floor slot: L7 before L6 | in §7 |
| F37 | the off box's implied client shapes | recorded at L6 |
| Q1–Q3 (§6⁷) | quarters ½/¼/¼; the recycle arm's content (superseded by F38); the dead header's ghost | landed |
| Q4 | `box_q_update` as a non-transition accessor (with the output residue R) | landed |
| Q5 | `box_view`; `ic_slot_cover` over `box_arm`, never over the body's layout | landed (statement pending) |
| F38 | `Q1 0` is not `emp`: the recycler deposits a false identity quarter | landed |
| F39 | `DepRef` deleted | landed |
| F40 | `Q2` ties its descriptor's identity to the slot's (the quarter rides Q2) | landed |
| F41 | residues indexed by ARM (Q1/Q2), then by COUNT at OUT_L1 (`Q1 : nat → iProp`) | landed |
| F42 | the resting pin rides the table row, not the header | landed |
| F42′ | the row is without the pin while the freeze bit is up | landed |
| F43 | (f′) takes a caller residue `Qc'` | landed |
| F44 | `Q1 0 := emp` is unsound: the viewer discharges over rows-admitted states | landed (F38's quarter kept) |
| Q6 | (e′)'s split wand is a VIEW SHIFT at the box's mask (`frz_slot_kill_pinw` opens `itable_inv`) | landed |
| Q7 | `ic_park` returns the neutral descriptor | landed |
| departures | `ic_dep_id DepFrz = Some`; halves rejoined inside `ic_park` | landed, confirmed |
| Q8 | (b″) `box_deposit_L1_join` + `box_q1_update` | ACCEPTED, not landed |
| Q9 | the two-armed `Q1 0` (main's MID arm re-homed) | ACCEPTED, not landed |
| §6²⁶/§6²⁷ | the hook convention as law; consolidate before r21; hook (a)/(g) too | RECOMMENDED to the owner |
| §3.2b | the consolidated box BUILT side-by-side (`iris/CtxBoxHooked.v`): hooks on (a)/(b)/(e)/(f)/(g), `box_q1_update`, eight verbatim-typed corollaries; green on the VM, assumptions closed | landed side-by-side (commit ded0fa1de); slot-in = r20c |
| Q10 | the last close's (a) must not consume iput's pin name-half: the hooked (a) moves the frozen alternative's own pin into `Q1 1` (option B); no ghost change; `ic_hdr_frz` carries `ifreeze_pre` out and needs a `CtxMorph` instance | RULED B by reviewer 1, confirmed by the box's designer (item 9); to land in ProofIput |
| §6²⁷ | run L2/L3/L4 in parallel now; sweep the file layer once; two tripwires before r21 | RECOMMENDED to the owner |
| item 16 | r25's "shapes final" = FOUR shapes (`inode_pay`, `fslot` with the off rows, `ftable_res_at` with the floor row, `ic_slp ∗ off_rows`) landed on OffBox's statements; the two L8 `CtxMorph` instances stated as skeletons on day one; log lock λ-only (no floor row); tripwires T1-T4 | RECOMMENDED by the box's designer |
| R4a Q1 | `inode_pay`: the cinv parks KEYED GHOST ONLY (`iref_frag`, `ic_lent_stamps`, `runit_any`); the reference's cells, `live_genlo`, `slh_tok` ride the fractional payload as `inode_ref_side` at the parked fraction; pin that fraction to `Q` by lending HALF at sys_open (no arity change), fallback `fp_iqi` | RULED by reviewer 1 (item 15) |
| R4a Q2 | NO re-mint, NO llb, NO `own_context` at cancel: the share's `cred_floor` is in the canceller's hand (morphed with the payload) and `live_genlo_agree` pins the parked `lo`; `inode_pay_cancel`'s statement unchanged | RULED by reviewer 1 (item 15) |
| R4a Q3/Q5 | ONE file-layer sweep with all three shapes final (`inode_pay`, `ftable_res_at` WITH the floor row + `_in` releases, `ic_slp ∗ off_rows`); L5 + full `ftable_res_at` first, then L8/L9 and the OffBox consumers as the two lanes INSIDE r25 | RULED by reviewer 1 (item 15); the two-sweep order reviewer 1 gave earlier is WITHDRAWN (L6 is on L8's path) |
| R4a Q4 | raise the twin's parked floor AFTER the last deposit (`ctx_parked_raise` takes only `llb T'`) | no objection (item 15) |
| R4a Q6 | `cwd_ref` (class D) needs NO ruling and NO floor-free form: `live_fracc` morphs by re-choosing `tl := lo` in the wrote case (the `lk_floor_morph` proof) -- so `inode_held` morphs structurally; class D is class A | RULED by reviewer 1 (item 15) |
| R4a Q7 | `first_fsinit`: classify by `About`; indexed cells morph structurally, raw cells need no crossing; do not restructure userinit/forkret for it | reviewer 1 (item 15) |
| FLOORS | a floored bundle that ∃-binds its `tl` MORPHS (floor case: `ctx_floor_dom` keeps `tl`; wrote case: `ctx_dom_wrote_floor` gives `ctx_floor ξ' lo`, re-choose `tl := lo`); the F21 llb form is for shares whose OWNER IS GONE (parked in the box), not for a credential whose owner crosses with it | law note (item 15) |

Tripwires added by this lane, beyond flip endgame §5.7: law 9 (residues)
and law 10 (hooks).

---------------------------------------------------------------------------

## 9. Open items (append new rounds here)

1. **DONE (r20b-6/7, A12.12/A12.13) — Land the recycle over (b″) + `box_q1_update` + the two-armed `Q1 0`**
   (Q8/Q9, ruled): the wrappers call `CtxBoxHooked` (the build agent's own CtxBox.v draft was withdrawn).  Original text: both box statements are BUILT and green in
   `CtxBoxHooked.v` (§3.2b: `box_deposit_L1_hook`, `box_q1_update`); the
   build agent may call them from there (same `is_box`) or land its own
   draft in CtxBox.v -- one or the other, not both.  `ic_recycle_deposit`
   becomes the hooked form; the recycle wrapper states the pool's mask
   premises (`ipoolN`, `iregN`, `escAN inum`).  Then ProofIget's recycle
   arm.
2. **DONE (A12.13/A12.16) — State `ic_slot_cover` over `box_arm`**: `IcacheCover.v` -- the arm-level `ic_arm_cover` + viewer clause, and main's surface (`ic_escrow_body := box_body`, `ic_lend`, the three-alternative `ic_slot_cover` at the header quarter, `ic_escrow_body_cover`) so FsCollectAll compiles with one import.
3. **DONE (A12.18, owner's go-ahead 2026-09-02) — The hook consolidation** (r20c): slotted into CtxBox.v as one edit, `CtxBoxHooked.v` deleted, no client change.  Was: BUILT side-by-side in
   `CtxBoxHooked.v` (§3.2b); what remains is the slot-in edit to CtxBox.v
   at the first quiet point after r20b, one commit, no client change.
4. **A second agent for L2/L3/L4** — DONE (2026-09-02; three rounds on tso-cutover, A12.14–A12.16 of the readiness record): L2 closed but ProofForkretPark (L8) and IcacheRef's dead `Require TsoCtxShim`; L3, L4 closed; BootShared/BootChain/SystemAdequacy textual behind ProofMain (L9, mine).
5. **`ic_slp`'s final shape** (the off-row conjunct + one fold lemma) --
   r21's consumers are fused against the CURRENT shape (`is_sleeplock_genl … (ic_slp fsc_ic k)`), so any later change is a wrapper-internal edit; was: before r21's consumer sweep; `off_rows_morph` and the llb-max lemma
   provable now.
6. (v) **SC-only readers still live**: `ctx_word4_claim` (WpSconfMem, 8
   users) and the r12 UkStepGen threading; fate: replaced by
   `CtxPinw.wordw_claim`, deleted at r28.
7. (vi) The pre-existing main Admitted set is outside the gate — confirmed
   by both reviewers; (vii) merge-main cadence every bank, one landing —
   confirmed.
8. **The port's Admitted inventory** — CLOSED (2026-09-02): OffBox.v's 14
    are proved (background agent, same day); `grep Admitted iris/*.v` finds
    no code-line admit in the tree.  Three skeleton statements were
    corrected to be provable, each flagged `STATEMENT CHANGE` in the file:
    `off_filealloc` (the cell at ξ, not the ambient; the `↑(offBoxN.@k) ⊆ E`
    mask for the birth unit's `box_ref_incr`; the count ghost pinned to
    `kalloc_count_inG` as BioInv/IcacheEscrow do), `off_dup` and `off_close`
    (`sr_ident r = k`, which `off_l1_row` already carries).  One helper
    added (`off_rows_insert_row`, the park's form of the append).  Original
    text: "must list OffBox's 14 until r25".

---------------------------------------------------------------------------

14. **L8 IS BLOCKED ON L5 + L7's λ PART — design out for review (2026-09-02).**
    Building the honest forkret park showed the chain the ordering encodes:
    the park's second crossing deposits `park_globals` into the child's
    twin (`ctx_deposit`, `CtxMorph`); every row morphs except `is_ftable`,
    whose `<{ ftable_res γ }>` payload is at the handle's context
    (`Print is_ftable`: `<{ @ftable_res … XI γ }>`) — L7's λ-flip; the
    λ-flip needs `CtxMorph (λ ξ, ftable_res (XI := ξ) γ)`, which
    `inode_pay`'s `cinv fileipN γx (inode_held_short v Q)` blocks (its body
    holds `cred_floor` via `live_fracc` and the two `inode_ident` cells) —
    L5.  The L5 entry above is under-specified against the code (the
    `inode_shr_genlo_bare` it says to park CONTAINS the cells; the cells'
    destination and cancel's re-assembly of `inode_held` are unsaid; its
    "§4.3" pointer has no target).  The design and four questions:
    `claude-notes/projects/inode-pay-r4a.md`.  The L8 edits (ten files,
    complete up to `is_ftable_morph`) are saved as a patch outside the tree
    (`/shared/xv6iris-2-l8-park.patch`), the worktree is clean.  Owner's
    stated order once ruled: L5 + minimal L7 first, then L8/L9 in parallel
    with the real L7 (floor slot, `_in` releases) + L6.  L6 CHECKED the
    same day (note §7): main has not dissolved `f->off` (still in
    `ioff_escrow` on main HEAD; fd-row-pilot rules no offset carrier), so
    L6 is the box; `ic_slp` has no off-row set yet (mitigation (1) was not
    taken); F36's floor slot is `∃ Kd, ctx_floor ξ Kd` in `ftable_res_at`
    with `_in` releases.  OffBox.v's 14 proofs STARTED in parallel (no
    consumer touched).  Q5 asks the reviewers to fix all three final shapes
    in one round.  AUDIT (note §8, same day): all 81 environment rows
    classified by `About`; unlawful shapes are exactly L5, L6, L7 plus a
    fourth, `cwd_ref` = a FLOORED inode reference inside `proc_priv` (Q6).
    CORRECTION: L6 IS on L8's path (`ioff_escrows` is `fs_ready`'s last
    row; `fs_ready` rides in `first_tok` inside `proc_priv`, which the park
    deposits).  The honest order is the plan's: r25 then r26; parallelism
    is inside r25.  Q7 (`first_fsinit`) RESOLVED the same evening:
    structural; `FirstTok.first_fsinit_morph` landed.  In flight: OffBox's
    14 proofs (main worktree) and ONE agent in an isolated worktree for
    the log lock λ-flip, the sleep-lock handle morph and the class-A
    wrapper instances (`EnvMorph.v`).  OffBox DONE (item 8).
15. **REVIEWER 1 ON ITEM 14 AND `inode-pay-r4a.md` §1–§8 (2026-09-02).**  Read
    against the code: `inode_pay`, `inode_held_short`, `inode_ref_short`,
    `live_fracc`, `cred_floor`, `inode_shr_held_gen`, `lk_floor` and its
    morph, `live_genlo` (frac-agree on `(g, lo)`), `ctx_floor_dom`,
    `ctx_dom_wrote_floor`, `ctx_parked_raise`, `fslot`/`file_rest`/`file_pay`/
    `file_core_noff`/`file_core_off`/`file_ref`, `is_pipe`, `ftable_res`, the
    eleven `<{ ftable_res γ }>` sites, `so_publish`.
    - **THE DIAGNOSIS IS RIGHT; THE PROBLEM IS SMALLER THAN THE NOTE MAKES IT.**
      Every conjunct of `ftable_res` morphs structurally except three:
      the cinv (its body names the ambient context), `inode_shr_held_gen`
      (carries `cred_floor`) and `is_pipe` (carries `lk_floor`).  The last
      two are not blockers: `lk_floor ξ lo := ctx_floor ξ lo ∨ ∃ a, ctx_wrote
      ξ lo a` already has `lk_floor_morph` (from `ctx_floor_dom` and
      `ctx_dom_wrote_floor`), and `cred_floor lo tl` is the same shape with
      two epochs.  The same proof carries it, re-choosing `tl := lo` in the
      wrote case; `inode_shr_held_gen` and `live_fracc` both ∃-bind `tl`, so
      each gets a five-line hand instance.  `is_pipe` is `∃ lo, inv(const) ∗
      lk_floor`, one structural line.  The ONLY genuine defect is that the
      cinv parks cell fractions and a credential inside an invariant.
    - **THE PARKED EPOCH IS PINNED BY AGREEMENT.**  `live_genlo` is fractional
      agreement on `(g, lo)`; the file's parked reference and its fd share
      come from one reference, so at cancel their `lo` is provably equal
      and the share's credential serves the reference.  D1(c)'s `∃ lo,
      live_genlo ∗ llb lo` and the re-mint are unnecessary.
    - **THE SHAPE (D1 revised):**
        inode_pay γx Q g inum v fdty wr q :=
          cinv fileipN γx (inode_core v Q inum) ∗ cinv_own γx q ∗
          inode_ref_side v (q*Q) g inum ∗ inode_shr_held_gen v (q*Q) g inum ∗
          ∃ ty, ity_shot g ty ∗ ⌜…⌝
        inode_core v Q inum := ∃ k, ⌜v = ientry k⌝ ∗ bounds ∗
          iref_frag k (Q+Q) ∗ ic_lent_stamps k (Q+Q) Q icfg_dev inum ∗ runit_any inum   (ghost only)
        inode_ref_side v s g inum := ∃ k lo, ⌜v = ientry k⌝ ∗
          inode_ident k (DfracOwn s) icfg_dev inum ∗ live_genlo k s g lo ∗ slh_tok (icfg_isl k) s
      Split law: everything fractional or persistent.  Morph: cells + ghost
      + the one hand instance.  Cancel: `cinv_cancel` + join the side (Q)
      with the share (Q) → `inode_ref k (Q+Q)` with `live_fracc` from the
      share's `cred_floor`; `inode_pay_cancel`'s statement UNCHANGED, so
      ProofFileclose does not move.  Arity UNCHANGED, so fourteen of the
      eighteen files that mention `inode_pay` do not move; the unfolding
      sites (SpecFileread/Filestat/Filewrite, sys_open's alloc, fileclose's
      cancel) frame one conjunct.
    - **R4a Q1:** cells outside the cinv in the fractional payload (the slot
      row IS the payload's remainder).  Pin the parked fraction to `Q` by
      construction: sys_open lends exactly HALF of the incoming reference's
      share fraction (`so_publish` takes `qi` and `s` as parameters, so the
      halving is one site upstream in ProofSysOpen).  Fallback if that
      fraction is spec-fixed: `fp_iqi` in `fpnames` (6 `MkFPNames` sites,
      mechanical insertions at the 18 files).
    - **R4a Q2:** neither option -- no `own_context` premise, no llb; see the
      agreement point.  The canceller's `inode_pay … 1` is at its own
      context (its fd's fraction is private; the table's came in under
      ftable.lock), so the share's `cred_floor` is already where it is
      needed.
    - **R4a Q3 and Q5, together, with a CORRECTION of my own:** earlier
      today I recommended two sweeps (L5 + λ-only L7 first to unblock L8).
      §8's audit is right that `ioff_escrows` is a row of `fs_ready`,
      which rides in `first_tok` inside `proc_priv`, which the park
      deposits -- so L6 IS on L8's path and the two-sweep order is
      WITHDRAWN.  Q5: yes -- fix all three shapes now and sweep the file
      layer ONCE (r25): `inode_pay` as above; `ftable_res_at γ ξ` WITH the
      floor row (`∃ Kd, ctx_floor ξ Kd`, every allocated slot's `tl ≤ Kd`)
      and the eight `_in` releases; `ic_slp cn k ξ := … ∗ off_rows on k ξ`
      with the fold's llb maximum.  Order inside r25: L5 + the full
      `ftable_res_at` first (one pass over the lock sites), then two lanes:
      L8/L9 (the saved patch) on one, `ic_slp ∗ off_rows` + the OffBox
      consumers on the other.  Nothing in the first pass is removed by the
      second: `ftable_res_at` is the final name, the floor row is final,
      `inode_pay` is final (L6 does not touch it).
    - **R4a Q4:** no objection.  `ctx_parked_raise` takes only `llb T'` and
      yields the twin's floor at `T'`; raise AFTER the last deposit (a raise
      before one is overtaken).
    - **R4a Q6 (class D, `cwd_ref`):** needs no ruling.  `inode_held v` =
      `inode_refp` = `inode_ref` ∗ `runit`; `inode_ref` = `iref_frag` ∗
      `live_fracc` ∗ `slh_tok` ∗ `inode_ident` ∗ `ic_ref_stamps` -- ghost,
      cells, and `live_fracc`, which morphs by the `tl := lo` re-choice.
      So `inode_held_morph` is structural + that one instance; class D IS
      class A.  Neither (i) (floor-free park form + re-mint) nor (ii) (drop
      the credential) -- both would re-spell every cwd consumer for a
      problem the morph instance solves in five lines.
    - **R4a Q7 (`first_fsinit`):** classify by `About` as §8 did the rest;
      indexed cells morph structurally, raw cells need no crossing; do not
      restructure userinit/forkret for it.
    - **THE OFF CELL (the owner's question): the invariant is NOT too
      strong.**  The dead phase is already the weak form (`foff_dead k q`, a
      plain cell in ftable's payload).  The live phase forces custody:
      `f->off` is written under `ip->lock` by any holder of the file, on a
      cell that belongs to a file slot, and the last closer must recover it
      holding only ftable.lock while excluding a mid-checkout reader --
      only a COUNTED custody proves that, and a raw pointsto would need the
      same deposit stamps to be absorbed by the next writer at another
      context.  The box, at `Q1 := λ _, emp`, `Q2 := emp`, is the minimal
      such mechanism; L6 stands as ruled.
    - **PITFALLS, written down before r25 starts:** (1) do NOT import the F21
      llb machinery into `inode_pay` or `cwd_ref` -- it is for shares whose
      owner is gone (parked in the box); here the owner crosses with the
      credential; (2) the cinv body must not mention the ambient context
      syntactically -- define `inode_core` where no `CurCtx` is in scope or
      check with `Print` that it took no `XI`, else `ctx_morph_const` will
      not unify; (3) keep `inode_pay`'s arity -- every unfolding site is a
      re-spiral risk, opaque sites are free; (4) the sleep-lock HANDLE morph
      (§8 class A) is the same shape as `is_lock`'s: `∃ lo, inv(const) ∗
      lk_floor` -- one instance, not a design; (5) measure after L5 +
      `ftable_res_at`, after L8, and after the OffBox consumers separately,
      so a regression names its cause; (6) `ftable_res_morph` must be a
      Global Instance so `SpecAcquire`/`SpecRelease`'s `CtxMorph R` resolve
      at the eleven sites and ProofMain's `newlock`.

## 10. Process and tooling (measured facts)

### 10.1 Build
From `/shared/xv6iris-2-main`:
```
./gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- sh -c \
  'cd iris && timeout 3300 make -f CoqMakefile -j16 -k 2>&1 | grep -v "^COQC\|^COQDEP\|^ROCQ\|Warning"'
```
The VM is shared (no flock; other agents build concurrently in their own
subdirs); it can be preempted — a rerun resumes.  Background runs log to
the session scratchpad.  Builds go to the VM, never local.

### 10.2 The honest measure
`make -k` leaves a FAILED file's old `.vo` in place, so dependents compare
against a stale timestamp and are skipped.  Roots = `File "./X.v", line N`
lines followed within a few lines by `Error`; deps = the `X.vo: … Y.vo`
lines of `iris/.CoqMakefile.d` on the VM; blocked = the transitive reverse
closure of the roots; green = total − roots − blocked.  `tools/cone.py`
computes it from a full `make -k` log.  `make -B` on a lane's file set is
the only way to certify a green claim involving files that were once red.

### 10.3 Merging
`tools/merge3.sh` / `git merge-file --diff3` with base `e1292b382`
(merge-base main / tso-flip); `tools/takeflip.sh` when main has no unique
declaration names; take a file WHOLE where flip deleted sections, but
first check `git log base..main -- file` for main's non-TSO edits (the
bcache lesson); `tools/bupdfix.py` for morph piles.  Flip's CtxMorph is
`==∗`: every `iDestruct (ctx_morph …)` on main-side text becomes `iMod`.
Main seals `word_pointsto`/`hreg_frame` opaque: flip text that destructs
them needs `iEval (rewrite /name)` first.  Section appendixes must re-bind
the original section variables.  Before merging a flip inode proof:
`sed 's/\bic_deposit\b/ic_handle/g'` on the flip copy.

### 10.4 Notes discipline
This file is the plan of record and is edited in place; the log file is
history and is not edited.  Each round adds an Amendment to
`main-tso-readiness.md` (what landed, departures from flip's text, measured
counts, deferred).  Design law is read from `origin/tso-flip`'s
`tso-escrow-endgame.md`; a change to a `CtxBox.v` statement is made on this
branch and recorded in §3.2 and §8 here.

16. **THE BOX'S DESIGNER ON ITEMS 14/15 AND `inode-pay-r4a.md` (2026-09-02):
    the rulings hold against the code; the sweep is safe ONLY if "shapes
    final" includes `fslot` and `ic_slp`; three corrections, four tripwires.**
    Read: `inode_pay`/`_split`/`_cancel`/`_alloc` (FileInvDefs.v:1094-1184),
    `inode_ref`/`_short`/`_refp`/`inode_held`/`_held_short`/`inode_shr_held_gen`
    (IcacheRef.v), `live_fracc`/`cred_floor`/`live_genlo_agree`, `lk_floor_morph`
    (WpLock.v:1095) and its two TsoCtx lemmas, `ctx_parked_raise`, `ftable_res`,
    `fslot`, `file_core_noff`, `is_pipe`, `so_publish` (ProofSysOpenParts.v:891),
    `ic_slp`/`ic_slp_dep`/`ic_slp_fold` (IcacheEscrow.v:4612-4633) and their
    consumers, `off_rows`/`off_l1_row`/`off_reclaim` (OffBox.v), `is_sleeplock_genl`,
    `proc_priv_core` (ProcInv.v:1199), the `<{ log_res }>` sites (20 in 6 files),
    the `<{ ftable_res }>` sites (11 in 5 files).
    - **D1 REVISED IS RIGHT, AND THE ARITHMETIC CLOSES.**  The published
      reference is `inode_refp k qt` with `qt = qi + Q`; pinning `qi := Q`
      makes `qt = Q + Q` and the cinv parks `iref_frag k (Q+Q) ∗
      ic_lent_stamps k (Q+Q) Q ∗ runit_any`, all context-free
      (`ic_lent_stamps` is `CtxBox.reference`: `own ∗ llb`).  Outside, at
      `q*Q`: the side (`inode_ident`, `live_genlo`, `slh_tok`) and the
      travelling share.  At `q = 1` the cancel joins side + share:
      `inode_ident 2Q`, `live_genlo 2Q g lo` (`live_genlo_agree` forces one
      `lo`), `slh_tok 2Q`, `ic_ref_stamps 1` from `ic_lent_stamps` + the
      share's stamps, and `live_fracc 2Q` from the share's `cred_floor` --
      which IS at the canceller's context: the table's fraction arrived
      through the acquire's morph, the fd's fraction is the process's own
      (morphed at a park by the instance below).  `inode_pay_cancel`'s
      statement unchanged, as reviewer 1 says.  `so_publish` takes `qi` and
      `s` as parameters (:891), so the halving is one site; `fp_iqi` is not
      needed.
    - **THE FLOORS LAW IS RIGHT, and it is the load-bearing observation of
      this round.**  In `live_fracc` and `inode_shr_held_gen` the epoch `tl`
      occurs ONLY in `⌜lo ≤ tl⌝ ∗ cred_floor lo tl`; `lk_floor_morph`'s
      proof (floor arm: `ctx_floor_dom` keeps `tl`; wrote arm:
      `ctx_dom_wrote_floor` yields `ctx_floor ξ' lo`, choose `tl := lo`)
      carries over verbatim, and every consumer cashes the credential at
      `lo` (`cred_floor_vis`), so the minimal `tl` loses nothing.  Hence
      `inode_held` morphs structurally and `cwd_ref` (class D) needs no
      design.  Nothing here requires an absorb capability or `own_context`.
    - **CORRECTION 1 -- "shapes final" must include `fslot` and `ic_slp`,
      or the sweep is two sweeps.**  The floor row's obligation ("every
      allocated slot's `tl ≤ Kd`") quantifies over `off_l1_row γ k c tl` IN
      `fslot`'s allocated arm; it cannot be stated finally with `fslot` at
      today's shape.  So pass 1 of r25 lands FOUR final shapes, not three:
      `inode_pay` (D1), `fslot` (F37: `off_l1_row` + `off_fd_row` in the
      allocated arm, the cell alone in the free arm), `ftable_res_at γ ξ`
      (the floor row), `ic_slp cn k ξ := … ∗ off_rows on k ξ`.  This needs
      only OffBox's STATEMENTS (its 14 Admitted are being proved in
      parallel; rule 0 says statements suffice for a sweep).  Then
      filealloc's mint, filedup's (c), fileclose's (d)/`off_reclaim` are
      pass-1 content too (F34: mass = one per counted reference, and
      fileclose's arm must produce the floor for `off_reclaim` from the row
      it just designed); what remains for the OffBox lane is the publish
      side only (fileread/filewrite's checkout/park under `ip->lock`).
      Anything else re-touches the six file proofs.
    - **CORRECTION 2 -- item 5 overstates `ic_slp`'s wrapper-internality.**
      The seven inode proofs consume `ic_slp` at both ends: the acquire's
      output is destructed into the row, the token and the neutral
      descriptor, and the two `_in` releases `rewrite /ic_slp_dep` and frame
      its three conjuncts (ProofIunlock.v:605, ProofIput.v:3232) after
      presenting `llb Tp` with `Tp = lr_tp`.  With `off_rows` added, each
      site gains ONE conjunct to thread, and the llb presented must be the
      COMBINED maximum (the L2 register's `lr_tp` cannot be raised at
      release -- the box holds its other half -- so the fold takes
      `ctx_floor ξ T` for any `T ≥ max (lr_tp, off max)` and weakens by
      floor monotonicity).  Give `ic_slp_dep cn k T` the off rows and
      `⌜stamps ≤ T⌝`, one lemma `ic_slp_dep_llb`, and `ic_slp_fold`'s
      statement stays.  Seven proofs, a few lines each, mechanical -- but
      list them in the lane, do not discover them.
    - **CORRECTION 3 -- the λ-flip is cheap; the floor row is the cost;
      the log gets no floor row.**  `<{ R }>` → `(λ ξ, R (XI := ξ))` changes
      nothing an acquire hands out at `cur_ctx`, so the 20 log-lock sites
      change only through the handle's definition and one structural
      instance (`log_res` = cells + ghost maps).  The eleven ftable sites
      change because of the floor row and the eight `_in` releases, and
      ONLY because `off_reclaim` needs `ctx_floor ξ Kd` under ftable.lock.
      No consumer reads a log field racily; a floor row there would be
      symmetry, not need.  Write that down so nobody adds one.
    - **Q4, Q7 agreed.**  `ctx_parked_raise` takes `llb T'` alone and yields
      the twin's floor; after the last deposit.  `first_fsinit`: `About`,
      then morph or nothing.
    - **THE SPIRAL RISK, NAMED.**  It is not any one shape; it is
      discovering a missing `CtxMorph` instance AFTER the file proofs are
      reopened.  L8's two deposits need exactly two instances,
      `park_globals` and `proc_priv`, assembled from the rows.  Rule 0
      applies: state BOTH as `Global Instance` skeletons on day one of r25
      (row instances Admitted where the row is not yet final), so that a
      row that cannot cross is a type error before any proof moves.  The
      hand instances are the `match`/`if` bodies: `fslot`, `file_core_noff`,
      `file_pay_st`; `cinv … inode_core` and `cinv_own` are constants;
      `is_pipe` and the sleep-lock handle are `∃ lo, inv(const) ∗ lk_floor`
      (`is_sleeplock_genl` is `sl_name ∗ is_lock … (sl_pay γ slk R H)`, so
      its instance is `is_lock`'s at a λ payload).
    - **TRIPWIRES for r25** (added to §8's list):
      (T1) no shape lands twice -- a second edit to `inode_pay`, `fslot`,
           `ftable_res_at` or `ic_slp` inside r25 stops the lane and comes
           back here;
      (T2) no floor row without a named consumer that needs it (ftable:
           `off_reclaim`; `ic_slp`: the off L2 rows; log: none);
      (T3) no `llb`/F21 form on a credential whose owner crosses with it
           (reviewer 1's pitfall 1) -- `cred_floor` morphs, it is not
           re-minted;
      (T4) a `CtxMorph` instance is a statement before any proof that
           depends on it is reopened; `About` (not reading) decides whether
           a body takes `XI`.
    - **ORDER, as I would run it:** day one: the four shapes + the two
      instance skeletons + `inode_pay_alloc`/`so_publish` at `qt = Q+Q`.
      Pass 1: the eleven ftable sites (`_in` releases), filealloc/filedup/
      fileclose's box steps, sys_open's alloc, the three spec unfolds;
      measure.  Then three lanes: (i) L8/L9 from the saved patch; (ii) the
      seven inode proofs' one conjunct + fileread/filewrite's off
      checkout/park; (iii) OffBox's 14 proofs, the log λ-flip, the
      sleep-lock handle instance.  Measure per lane (pitfall 5).  Nothing
      in a lane changes a shape.

10. **The AU proofs are PARKED (owner, 2026-09-02).**  Every `Proof*AU*` /
    `Link*AU*` row of `iris/_CoqProject` is commented out for the cutover;
    the `Spec*AU` rows stay (live dependents).  Un-parking is a future round
    with its own d3 pass (ProofSysMknodAU, ProofSysOpenAU*, ProofFilewriteAU,
    ProofSysUnlinkAU*, ProofCreateAU*, ProofSysDupAU*, ProofSys{Read,Write}AU*).
11. **r21 rule for the file layer (A12.16):** the fs env records
    (SpecFileread / SpecFilewrite / SpecFilestat) carry `IcacheInv.iref_claims`
    after `itable_inv`, flip's row; every syscall shell supplies it from
    `is_itable2_claims`.  Consumers of the inode contracts keep main's
    `_tx_sconf`/`_dep_sconf` spellings and take flip's `lo tl` epoch indices,
    `cred_floor`, `iref_claims` premises and the floored forgets -- the
    "main's names, flip's shapes" blend, recipe in A12.16.

12. **`ic_grow_tx` / `ic_shrink_tx` OVER THE BOX (r21 round 2, 2026-09-02).**
    Main's two two-lock moves (the parked `ln_tx` share of a `DepTx`
    descriptor grows / shrinks while the holder keeps the lock; sys_unlink's
    `dp`, create's parent and child) are stated on the cutover with main's
    arity plus the epoch `lo`, over the holder's `ic_handle`, and PROVED
    THROUGH `CtxBox.box_q_update` (the L2 holder's Q2 rewrite, ruled §6⁸ Q4)
    -- no CtxBox.v / CtxBoxHooked.v change: the descriptor variable's two
    halves move together (`ghost_var_update_halves`), `ic_q_side` at DepTx
    (= `tx_pin`) takes or gives exactly the crossing share, `ic_deposit2` /
    `ic_pay_live` do not read `q`.  In `IcacheEscrow.v` beside `ic_slp`.
    Reviewers: this is the note at CtxBox.v's `box_q_update` made concrete.

13. **What r21 leaves red (2026-09-02, end of round 2):** `ProofForkretPark`
    only (L8: A6.129 `own_context_twin`, `park_globals`; needs
    SpecForkretParkPaid at flip's shape too -- the plan's r26 lane, untouched
    by both agents), plus whatever the boot chain (BootShared / BootChain /
    SystemAdequacy, textual from the L-lane) shows at its first honest
    compile behind ProofMain.  Every FS-cone consumer is fused.  The edit loop
    on the large files ran under `rocq-warm` (`claude-notes/rocq-warm.md`);
    `make -k` stays the measure.
