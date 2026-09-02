# tso-cutover ENDGAME PLAN — landing the TSO proofs on main (2026-09-02)

**Status.**  `tso-cutover` (off `main`, worktree `/shared/xv6iris-2-main`, VM
tree `_shared_xv6iris-2-main`) is the ONLY vehicle left: the `tso-flip` lane
has finished (its handoff is `tso-machine-flip.md` A6.163 on that branch) and
the owner has handed the remainder to this lane (2026-09-02: "that branch is
completely yours").  No WIP side branches; every green boundary is banked
on `tso-cutover` as a numbered round, `main` is merged in at each bank, and
`main` moves ONCE at the end (tso-port.md §0.23′).  This file is the plan;
it is edited in place (process rule 6), and `main-tso-readiness.md`'s
Amendments remain the round-by-round log.

Reading order for a fresh agent: `claude-notes/durable-notes.md`; this file;
`main-tso-readiness.md` Amendments 11–12 (what the bcache/icache rounds
landed); then, on `origin/tso-flip`, `claude-notes/design/tso-escrow-endgame.md`
(the box law: §1 allowed forms, §2 the box, §3.5 "the statements are
`iris/CtxBox.v`", §4.2 the icache round R3 with rulings F1–F30, §4.3–§4.5
R4–R6, §5 process rules and tripwires) and `tso-machine-flip.md` A6.163
(merge hazards).  The owner rulings the whole port runs under are
`tso-port.md` §0.x′ on `origin/tso` (§0.23′ main moves once; §0.24′ the
specific-binary U tier deferred; §0.25′ the three-case gate; §0.26′
visibility-free free pages).

---------------------------------------------------------------------------

## 1. Where the tree stands (measured 2026-09-02, build `ic8` at 0f3c7a5d0)

### 1.1 Rounds banked on `tso-cutover` (20 commits over main)

| round | commit | what |
|---|---|---|
| r1–r3 | 49b970365, d1db8ae4c, 047d03a69 | machine tier (RiscvLang/Exec/Ptsto + engines under Ztso), the real ctx tier (TsoCtx/Move/Park/AbsorbLb, satellites), StartedInv barrier |
| r4–r7 | 28fd70eb7 … ff303cf30 | M4 lock kit + kpt/pt tier, S-mode regime + boot carve + device invariants, byte/page kit + kfree memset + sleeplock mints, proc/pt/pipe/umode tier |
| r8–r12 | 6540c0f7d … 18601527e | SchedCtx/WpSconf composition, the kernel function-proof wave, S-payer through umode_fetch, local breaks, the U-tier running-token wave |
| r13 | 255a00e3a | virtio under TSO: the pop model on THE ROW DESIGN (`virtio-tso-port.md`) |
| merges | c128e4815, a1dcf7324 | `main` merged in (through cb1415c53) |
| r14 | 9a272a65b | tso-flip's bcache over `CtxBox` (Amendment 11) |
| r15–r16 | f8688d4e6, bc71760b0 | icache stage 1: IcacheRef shim removal, modal transports, IcacheBoot token threading (Amendment 12.1) |
| r17 | 6f0c00faf | device-conformance vtests under Ztso (another agent; finding 24 closed) |
| checkpoint | 0f3c7a5d0 | icache stage 2: IcacheRef merged under the stitch rule (Amendment 12.4) |
| r18 | (this commit) | IcacheInv per-slot fusion (§3.3): flip's pinw body and `*_store_pinw_au` accessors with main's region steps (`ireg_reg`, `frzidx`, no freeze receipt); `TsoCtx.ledger_read_pinw_vis` and `WpLockIn.lock_finisher_close_in_llb` brought over verbatim from flip; IcacheInv/IcachePinwObl/InodeRegion/WpLockIn green |

`main` is one commit ahead (cacbc4aa1, the nightly dead-import sweep); it
merges in at the next bank.

### 1.2 The honest measure (and why `ls *.vo` lies)

`make -k` leaves a FAILED file's old `.vo` in place, so its dependents
compare against a stale timestamp and are skipped as "up to date": the VM
tree shows 1480 `.vo` of 1496 targets while a third of the tree is
unbuildable.  The honest measure is: red ROOTS = the `File … Error` pairs
in the `make -k` log; BLOCKED = their transitive dependents in
`iris/.CoqMakefile.d`; GREEN = the rest.  (Recipe in §7.2; the script is
`scratchpad/cone.txt`'s producer, to be checked in as `tools/cone.py`.)

| | count |
|---|---|
| targets in `_CoqProject` | 1506 |
| red roots | 13 |
| blocked behind them | 361 |
| honest green | 1132 |

### 1.3 The 13 roots, classified

| root (line) | blocks | class | lane (§4) |
|---|---|---|---|
| `ProcInv.v:1013` | 350 | `TsoCtxShim.ctx_phys_word_shim`: the trapframe words' PHYSICAL-tier context axis; the keystone of the whole kernel/syscall/adequacy cone | L1 |
| `ProofIunlock:576`, `ProofIlock:2499`, `ProofIput:1029`, `ProofIget:1725`, `ProofIdup:385`, `ProofIunlockput:283`, `ProofIreclaim:1698` | 64/63/60/58/52/50/24 | the inode proofs read the pre-stitch `inode_shr_gen` triple / `live_frac`; they are re-taken from flip over the box (§3.5) | icache |
| `IcachePinwObl:73` | 0 | needs flip's `iref_pin_rows` (IcacheInv, §3.3) | icache |
| `FsCfgSnap:906` | 17 | boot: `icfg_alloc`'s post order changed by the IcacheRef merge (`icfg_hpn` boot map vs `icfg_lk` auth); a one-site fix | icache |
| `ProofSysKill:102` | 26 | `TsoCtxShim.ctx_word_to_mem` bridge | L2 |
| `ProofPipealloc:1379` | 27 | `page_own_pipe_raw` gone (pipe page tier at the A6.87 filled page) | L3 |
| `RiscvAdequacy:846` | 17 | the era allocation in the machine adequacy statement (type error at `ghost_var_alloc` of the disk mirror) | L4 |

Behind the roots, the shim wall (Amendment 12.3) is now measured exactly:
of the 40 files whose text mentions `TsoCtxShim.`, 12 are green (mentions
in comments only), 2 are roots (ProcInv, ProofSysKill) and 26 are blocked
(`BootBridge`, `BootCarveMain`, `BootShared`, `ProofArgfd`, `ProofAllocproc`,
`ProofCreateParts`, `ProofForkretParts`, `ProofForkretPark`, `ProofKexit`,
`ProofKwait`, `ProofKexecD`, `ProofKexecTail`, `ProofKforkB5`,
`ProofMainSecondary`, `ProofSysRead`, `ProofSysWrite`, `ProofSysClose`,
`ProofSysExit`, `ProofSysPause`, `ProofSysUnlinkParts`, `ProofUservec`,
`SystemAdequacy`, and the four MAIN-ONLY `ProofSysReadAU`/`ProofSysWriteAU`/
`ProofSysWriteConsAU`/`UkStep`).  Every blocked one except the main-only
four has a shim-free twin at flip HEAD (`origin/tso-flip` a90cc05e8).

The adequacy chain (`LinkForkretParkPaid` → `LinkUserinit` → `LinkMain` →
`BootChain`/`BootShared` → `SystemAdequacy`, plus `ProofMain`, `ProofForkretPark`)
is entirely inside ProcInv's cone.

Pre-existing `Admitted` on main, NOT part of this port and not counted in
its gate: `FsShPin`, `ProofKexecA/B/PinnedA`, `ProofIalloc`, `ProofKforkMain`,
`ProofSyscall` (4), `ProofVirtioDiskRwF`, `UkShParse` (flip carries the same
set minus the U-shell ones).  `CtxBox.v`'s single hit is the word in a
comment.

---------------------------------------------------------------------------

## 2. The law this lane works under (inherited; nothing here is new)

1. **THE STITCH RULE (owner, 2026-09-01).**  tso-flip's approach for the
   PHYSICAL words of memory — ownership, bounds, contexts, floors, stamps,
   the transit box for cross-lock cells (the tricky bits: icache, bcache) —
   and main's approach for the GHOST state of the durable disk — the
   descriptors and the `ln_tx` shares they park, the arm-keyed registry,
   the corpse/transit ledgers, the pool partition, freeze receipts.  Ghost
   is unaffected by TSO.  Stitched at the boundary, which is CtxBox's
   parameter list (§3.4).
2. **Copy flip, invent nothing** (tso-port.md, `main-tso-readiness.md`
   §4.2): where flip has a proof of the same statement, take its text; a
   residual difference is recorded, not improvised.  SC-only lemmas added
   on this branch are flagged (Amendment §5.3 class) — the current list is
   §6 item (v).
3. **The allowed-forms law** (endgame §1): a physical cell is T1 (running
   context, exact), T2 (parked at a stamped context inside a box/lock
   record) or T3 (ledger pin above a floor; racy reads).  Inv/cinv bodies
   hold only ξ-free ghost, T2 custody with ξb ∃-packed, or T3 pins.  Lock
   payloads are context-λs.  Floors are delivered ONLY by the llb-tier
   acquire posts (R1) and lock-payload floor rows folded at release (R2).
   `cred_floor` (holder-side, for T3 racy reads) is never a substitute for
   `ctx_floor` (what withdraws consume).
4. **Two spellings per resource** (holder / parked); references have ONE
   ghost-only spelling.  No interim wrappers; one sweep to the final form.
5. **The box is law** (endgame §2, §3.5): seven lemmas —
   `box_withdraw_L1` (a), `box_deposit_L1` (b) / `box_deposit_L1_shape` (b′),
   `box_ref_incr` (c), `box_ref_decr` (d), `box_checkout` (e), `box_park` (f),
   `box_l1_to_l2` (g) — plus `box_alloc`/`box_alloc_at`.  A box lemma may
   appeal to nothing beyond the declared `P_hdr`/`P_rest`, `Q` and the L2
   token.  The tripwires of endgame §5.7 apply verbatim (an eighth lemma, a
   fourth arm shape, a second reference form, a per-site floor, a stamp
   agreement between holders, anything ξ-indexed in Q, a new box ghost).
6. **Site-map first** (process rule 5): before any box client is coded,
   the table of every inv-open site with its lock context, its (a)…(g)
   letter and the row that discharges its cover is written and vetted.
   §3.4.3 is that table for the stitched icache.
7. **Main moves once** (§0.23′): this branch lands on `main` as one merge
   when the full `-B` build is green, `make audit` is at baseline and the
   port's own Admitted count is zero.  Until then `main` is merged INTO
   `tso-cutover` at every bank so the final merge is trivial.
8. **§0.24′** deferred the specific-binary U tier on the flip tree.  This
   branch cannot descope it (main's `UkStep`/`UkRun` import that machinery;
   r8's "mapped wall"), so it is ported here as ordinary work — it is
   already green at r12 except where it sits behind ProcInv.

---------------------------------------------------------------------------

## 3. THE STITCH — the icache under both designs, in detail

### 3.1 Who owns what

| concern | taken from | the objects |
|---|---|---|
| the count word `i_ref`, its racy reads and stores | flip (A6.145) | `iref_pin_rows` (four `phys_ledger_pinw` bytes under `TsPinw … iref_set`), `pinw_slot`, `icfg_istmp k` stamp halves, `pinw_slot_acc_upd`, `iref_load_pinw_au`, the `*_store_pinw_au` family |
| the identity/valid/nlink/dinode CELLS across itable.lock ↔ ip->lock | flip (R3) | `ic_escrow` IS the box: `P_hdr` = `ic_hdr` (ident, valid, nlink + the payload arm keyed by inum), `P_rest` = `ic_rest` (the in-memory dinode fields), `X := ic_x` (Raw / Unloaded / Loaded dn bm), `tok := ic_tok`, L1 row `ic_slot_row`, L2 λ payload `ic_slp` |
| liveness and its epoch | flip | `live_genlo k s g lo`, `live_fracc`, `cred_floor lo tl`, `ic_ref_stamps`/`ic_stamps`, `inode_ref := iref_frag ∗ live_fracc ∗ slh_tok ∗ inode_ident ∗ ic_ref_stamps` |
| the lock tiers | flip (M-6) | `is_sleeplock_genl` over `ic_slp`; `wp_acquiresleep_nb_genl_llb_sconf` at Tl := 0 for iput's free path (F22) |
| the durable-disk descriptors | main | `ic_dep` = `DepNone | DepTx s dev inum g t q | DepRd … | DepFrz q dev inum t qt` (Xv6Cameras.v:739); `ic_deposit` as a `ghost_var` HALF pinning the arm's `(t, q)` to the holder's; `ic_dep_side d = tx_pin_o icfg_log (ic_dep_side_tx d)` — the parked `ln_tx` share |
| the reader's quarters, the freeze pins | main | `ic_out_rd` (3/4 bundle stays inside on a read checkout), `ic_pin_tx`/`ic_pin_rest`, `hpn_h`, `frzidx`/`frz_mir`/`runit` |
| the inum-keyed ledgers and the pool | main | `ipool_inv` (`ipoolN`), `ipool_transit`/`ipool_corpse` (`icfg_ptrn`/`icfg_pcrp`), `ipool_key/xkey/tkey/ckey`, `ic_id` quarters, `ic_live_inums`, `ipool_cover_inum` |
| the region step at each count move | main | `ireg_icnt_acc`/`ireg_icnt_frz_acc`/`ireg_icnt_lic_acc`/`ireg_icnt_mir_acc`, `frz_close ph`, `frz_slot_freeze/kill` |
| what the commit reads at quiescence | main | `FsCollect`/`FsCollectAll`: the collection opens the escrow and refutes a write arm against an EMPTY `ln_tx` authority (`ic_out_no_write_arm`), reads the reader's quarters, `ic_slot_cover`, `ipool_cover_inum` |

### 3.2 The reference tier — LANDED (0f3c7a5d0), decisions taken

- `iliveUR` payload is `leibnizO (gname * nat)` (flip A6.145).
- `inode_shr_held_gen v s g inum` keeps main's NAMED inum (sys_open records
  it in `fp_inum`) and gains flip's floors (`∃ k lo tl, ⌜lo ≤ tl⌝ ∗
  cred_floor lo tl ∗ inode_shr_genlo …`).
- Floored bundles have NO `CtxMorph` (a `cred_floor` is about the holder's
  own context); `FileInvDefs`'s parked shares therefore go the R4a way
  (§4 L5): park floor-free, re-mint under the lock.
- `ic_dep` is still main's; it gains flip's `lo` field on the
  credential-bearing arms (`DepTx`, `DepRd`) when IcacheEscrow lands
  (`ic_dep_lo`), so the holder's `live_genlo` and the deposit agree on the
  epoch.  `DepFrz` is KEPT (see §3.4.2) — flip deleted it because its
  receipt was a payload-arm alternative; on main it also carries the
  parked `(t, q)` share of iput's freeze window, which is durable-disk
  ghost and stays.
- `ctx_word4_claim` (WpSconfMem.v:207, main's claim readers used by 8
  files) is an SC-era reader flip does not have; flagged (§6 v) — the
  stitched inode proofs are expected to stop using it in favour of
  `CtxPinw.wordw_claim`, after which it is deleted.

### 3.3 `IcacheInv` — the per-slot fusion (r18, LANDED)

Flip's body (IcacheInv.v.flip:1588) is
`∃ M, itable_half M ∗ ⌜icM_wf M⌝ ∗ [∗ list] k ∈ seq 0 NINODE, pinw_slot M k`,
and `pinw_slot M k` (:1573) FOLDS cutover's two conjuncts for slot k:
`iref_cells M`'s word becomes `iref_pin_rows k (iref_word M k) lo tst` beside
`mono_nat_auth_own (icfg_istmp k) ½ tst`, and `live_pool M`'s arm for k is
genlo-ized at the slot's `(g, lo)`; a free slot keeps only the liveness unit
(its count word rides itable.lock's payload — the motion rule).  The
stitch:

- take flip's `iref_set`, `iref_claims`, `iref_pin_rows`, `pinw_slot`,
  `itable_body`/`itable_inv` (and the `_pinw` aliases so flip's consumer text
  compiles unchanged), `pinw_slot_acc`/`_acc_upd`/`_slice`, `pinw_store_post`,
  `pinw_arm_split/join/alloc`, `iref_tok_genlo`, `iref_lookup_genlo`,
  `frz_mass_absurd`, `frz_slot_quarters`, `frz_evict_mass`, `frz_rcpt*`
  VERBATIM;
- inside the per-slot arm keep cutover's `live_norm`/`live_frzn` shapes as
  main has them (the `frzidx` freeze selector `frzsel`, `runit`, and
  `ireg_reg`'s coupling) — flip's own arms are main-derived and differ only
  by the genlo epoch, so this is a merge of the binder, not a redesign;
- every accessor is flip's WINDOW + main's REGION STEP at the same
  instruction.  The table, one row per cutover accessor:

| cutover accessor | flip twin (window) | main's ghost step kept |
|---|---|---|
| `iref_incr_store_au` | `iref_incr_store_pinw_au` | `ireg_icnt_acc` |
| `iref_dup_store_au` | `iref_dup_store_pinw_au` + `iref_dup_step_genlo` | `ireg_icnt_acc` |
| `iref_upgrade_mir_store_au` | `iref_upgrade_mir_store_pinw_au` | `ireg_icnt_mir_acc`, `frz_mir_step` |
| `iref_close_store_au` | `iref_close_store_pinw_au` + `iref_close_step_noarm` | `ireg_icnt_acc` |
| `iref_close_last_store_au` | `iref_close_last_store_pinw_au` + `_step_noarm` | `ireg_icnt_lic_acc`, `frz_park_lic_off` |
| `iref_close_last_freeze_store_au` | `iref_close_last_frz_store_pinw_au` | `ireg_icnt_frz_acc` at `frz_close ph`, `frz_slot_freeze` |
| `iref_alloc_store_au` | `iref_alloc_pinw_install` + `iref_alloc_step_noarm` + `pinw_arm_alloc` | `ireg_icnt_acc` (the recycle's region step) |
| `iref_load_locked_au`, `iref_live_load_au`, `iref_live_gen_load_au` | `iref_load_locked_pinw_au`, `iref_load_pinw_au` (racy, cred_floor) | — (pure reads) |
| `iref_share_lookup_au`, `live_slot_regen`, `frz_slot_freeze/kill` | `_pinw` twins | unchanged ghost |

Gate for r18: `IcacheInv`, `IcachePinwObl`, `InodeRegion` green; the inode
proofs still red (they change again in r19/r20).

### 3.4 `IcacheEscrow` — the box for the cells, main's ghost beside (r19)

#### 3.4.1 The instance
Start from flip's file (3171 lines; `ic_escrow` IS the box, M-1..M-6) and
re-add main's ghost DEFINITIONS unchanged (`ic_deposit`'s `ghost_var` half
and `ic_dep_*`, `ic_pin_tx/rest`, `ic_out_rd`/`ic_rd_arm`, `ipool_*` rows and
`ipool_inv`, `ic_id` quarters, `ic_live_inums`, `ci_inums`/`region_inums`).
Flip's `ic_deposit cn k d := ic_deposit2 k d ∗ ic_pay_live k d` (name and
arity kept for ~70 opaque takers) becomes
`ic_deposit2 k d ∗ ic_pay_live k d ∗ ic_dep_half cn k d` — the holder's
half of main's descriptor rides the holder's handle.

#### 3.4.1b The descriptor variable and the box token (decided at r18, for r19)
The box's L2 token is `ic_tok cn k = ghost_var (icn_esc cn k) 1 DepNone`
(flip and main agree on the definition), and the box holds it WHOLE during
OUT_L2 — so main's descriptor halves (`ic_deposit cn k d`, the `ghost_var`
at `d` split between the arm and the holder, whose agreement at the park is
what hands back exactly the `(t, q)` share the checkout parked) cannot live
in the same variable.  They move to their own client ghost: `ic_names` gains
`icn_dep : nat -> gname`; `ic_deposit cn k d := ghost_var (icn_dep cn k) ½ d`
keeps main's name, arity and every lemma (`ic_dep_checkout`, `ic_dep_park`,
`ic_deposit_agree`); its neutral whole `ghost_var (icn_dep cn k) 1 DepNone`
rides the L2 payload λ beside the box's `l2_row` (so the acquiresleep winner
holds it, exactly as main's winner held `ic_tok`).  `icn_mid` (main's recycle
token) is retired — the window flag `sr_win` is that token — and `icn_id`
(main's live/identity agreement, which `ipool_body`'s `ic_ids` reads) stays.
`Q := ∃ d, ic_deposit cn k d ∗ ic_q_side k d` with `ic_q_side` = the parked
`ln_tx` share at `DepTx`, `ic_out_rd` at `DepRd`, the freeze window's share,
selector quarter and count fragment at `DepFrz`, `False` at `DepNone`.

#### 3.4.2 Where main's ghost lives, arm by arm (the placement rule)
Main's five-arm body (`ic_parked ∨ ic_out ∨ ic_mid_arm ∨ ic_empty_arm ∨
ic_held`, IcacheEscrow.v:2040) is replaced by the box body; each arm's
GHOST content moves to the one ξ-free slot the box law allows for it:

| main arm (state) | box state | main's ghost content | goes to |
|---|---|---|---|
| `ic_parked` (in, unlocked) | IN at `sr_ident = Some (dev,inum)`, `X = Loaded/Unloaded` | the payload's ghost leg (`ic_inode_leg`, `ic_loaded_ghost`), the frozen alternative's receipt | the payload arm `X` (client-defined, CtxMorph because ghost is trivially morphable) — already how flip's `ic_payload_arm_frz` is shaped |
| `ic_out` (checked out under ip->lock) | OUT_L2 | `∃ d, ic_deposit½ d ∗ (ic_dep_res k d ∨ ic_out_frz) ∗ ic_out_rd …` = the descriptor's other half, the parked `ln_tx` share (`ic_dep_side d`), the reader's 3/4 bundle | **`Q`** — "the client's ξ-free ghost residue during an L2 checkout" (endgame §2); ξ-free by construction (ghost_var, tx_pin_o, fractions of ghost) |
| `ic_held` (iput's guard window) | OUT_L1 (`sr_win = true`: `hdr_out ∗ P_rest ξb`) | `ic_pin_tx k` (the authority-side pin), `hpn_h` | the L1 payload row `ic_slot_row` (the window is open only while itable.lock is held — BONUS RULE: L1 cannot be released mid-window), so the row carries the pin for exactly the window's extent; at (g) `box_l1_to_l2` it moves into `Q` as `DepFrz`'s content |
| `ic_mid_arm` (recycle between stores) | OUT_L1 at c = 0 during iget's three plain stores | `ic_unloaded`'s inum key, `ic_id ½ true` | the L1 row (`sr_ident` is what (b) re-identifies at) and `ipool_inv` for the inum ledgers |
| `ic_empty_arm` | M-1: NO EMPTY ARM — an evicted slot is IN at its last identity with `X = Raw` | `inode_raw`, `ic_id ½ false` | `X = Raw` carries the raw cells (flip: `ic_rest_raw_unloaded`, `ic_hdr_dead_raw`); the `ic_id` quarter rides `itable_res2`'s dead row (`islot_free_at`) |
| inum-keyed ledgers (`ipool_transit`, `ipool_corpse`, `ic_live_inums`) | any | pure ghost | `ipool_inv` stays as on main, opened beside the box in the same step |

Nothing here is a new box ghost, a new arm, or a box lemma appealing to a
client ghost: `Q` and `X` are the client's declared parameters, the L1 row
is the client's payload, `ipool_inv` is a separate invariant.  If the site
map (§3.4.3) finds a piece of ghost that fits none of these four slots,
that is a §5.4 stop — update this file and get the ruling; do not add a
conjunct to the box.

#### 3.4.3 The R3′ site map for the stitched icache (to VET before r19 code)
Flip's R3 site map (endgame §4.2) plus main's ghost step per site.  "Ghost
step" is the `==∗` main's arm lemma performed, now stated on `Q`/`X`/row.

| site | lock | box lemma(s) | main's ghost step (kept) | main lemma it replaces |
|---|---|---|---|---|
| iget scan hit, `ref++` | itable | (c) `box_ref_incr` at `sr_ident` | `ireg_icnt_acc`; `ipool` unchanged | — (no escrow touch on main either) |
| iget recycle: dev/inum/valid stores, `ref := 1` | itable | (a) at c = 0 → three plain stores on the header in hand → (b′) `box_deposit_L1_shape` at the new identity, `X := Unloaded` | `ipool_take_lend`/`ipool_id_lend` (the inum leaves the pool's free partition), `ic_id` flips to `true` (`ic_id_flip`), `ic_mk_unloaded`'s ghost leg | `ic_open_empty_dev/free`, `ic_close_mid`, `ic_open_mid`, `ic_close_mid_to_parked` |
| ilock checkout (write) | ip->lock (L2) | genl_llb acquire at Tl := the share's stamp; (e) `box_checkout` with the holder's fragment (mass s) | mint `DepTx s dev inum g t q lo`, park the `ln_tx` share `(t,q)` into `Q` (`ic_dep_side`), give the holder `ic_deposit½` | `ic_swap_checkout(_gen)` |
| ilock checkout (read) | L2 | (e) | `DepRd`: 3/4 of the bundle stays as `ic_out_rd` in `Q`, holder carries the quarter | `ic_swap_checkout_rd` |
| iunlock park | L2 | (f) `box_park`; `_in` releasesleep re-floors the row | agree the two `ic_deposit` halves (the pin re-identifies `(t,q)`), take the share back, `DepNone` | `ic_swap_park_arm`, `ic_swap_park_dep`, `ic_open_out` (the borrow — GONE: the holder's own slice rides its row) |
| iput non-last close | itable | (d) `box_ref_decr` | `ireg_icnt_acc` | — |
| iput `ref == 1` guard (valid, nlink reads) | itable | (a) at c = 1 with its own unit; reads off the header in hand | `ic_pin_tx` enters the L1 row (`ic_pin_enter`), `hpn_h` | `ic_open_auth_ref`, `ic_open_auth_frz` |
| iput free path: freeze window (+0x5e..+0x70), acquiresleep NB at Tl := 0, itrunc/iupdate | both, then L2 | (g) `box_l1_to_l2` (F30); then L2 work on the bundle in hand | `DepFrz q dev inum t qt`: the parked share moves from the row into `Q` (`ic_out_frz`); `frz_slot_freeze`, `frz_rcpt`; the corpse/transit ledgers (`ipool_put_corpse`, `ipool_deposit_corpse`, `ipool_put_ord`) | `ic_close_held`, `ic_close_out_frz`, `ic_swap_park_frz` |
| iput last close after free / after plain park | itable | (b) at c = 1, NO bump (F28), or (b′) to `X := Raw`/`Unloaded` at the same identity | `ireg_icnt_lic_acc` / `ireg_icnt_frz_acc` at `frz_close ph`, `frz_park_lic_off`, `ipool_evict_lend` | `ic_close_to_empty_late`, `ic_close_to_empty_frz`, `ic_close_parked` |
| ilock's `valid == 0` load path (bread + copy) | L2 | on the bundle in hand (`P_rest` is exact at the holder) | `ic_loaded_open`/`ic_mk_loaded` (the payload ghost leg), `ic_inode_leg_shed_to` | `ic_mk_loaded` (kept) |
| the commit's collection at quiescence (`FsCollect`, `FsCollectAll`) | none (log.lock; every arm refuted or read as ghost) | open the box inv; by the refutation table: IN → read `X`'s ghost leg; OUT_L2 → `Q`'s `ic_dep_side` refutes a write arm against the empty `ln_tx` authority (`ic_out_no_write_arm`), or reads `ic_out_rd`; OUT_L1 → the L1 row's `ic_pin_tx` | `ic_slot_cover` re-stated over the box body: the three shapes × the ghost in each slot; `ipool_cover_inum` unchanged | `ic_lend`, `ic_escrow_body_cover`, `ic_slot_cover`, `ic_loaded_lend_owned`, `ic_rd_arm_lend_owned` |
| `filestat`, `fileread`/`filewrite` share-holders | L2 via ilock | as ilock/iunlock with `DepShr`-shaped mass (flip: the share carries its stamps `◯ m`) | `DepTx`/`DepRd` as above | `SpecIlock`/`SpecIunlock` rows |

The collection row is the one that needs the most care and is the one
place a ruling might be needed (§6 i): main's `ic_lend` borrowed the
whole five-arm body; over the box the collection reads GHOST ONLY (`X`'s
leg, `Q`, the row) and never a cell value, which is exactly what the law
allows a non-owner to see.  If any collection lemma turns out to need a
CELL (e.g. `valid`), the design is wrong and this is a stop.

Gate for r19: `IcacheEscrow`, `EscrowDeposit`, `TxPin`, `IcacheBoot`
(flip's `box_alloc_at` per slot + main's ghost allocation, stamps at 0)
green; `FsCfgSnap:906` fixed.

### 3.5 The inode proofs, their specs, and the consumers (r20–r21)

- `ProofIget/Ilock/Iunlock/Iput/Idup/Iunlockput/Ireclaim` + `SpecIlock/Iput/
  Iunlock/Iunlockput/Iget/Idup`: flip's proofs over the box (they are
  complete at flip HEAD, `ip_free_locked` included since F30) with main's
  ghost rows re-added in the spec posts exactly where the site map puts
  them.  3-way merge per file (base e1292b382), resolving to FLIP for every
  cell/box/floor step and to MAIN for every `ic_dep`/`ireg`/`ipool` step.
- The M-5 reference sweep in the FS cone: 76 files mention `inode_ref`, 46
  `inode_shr`, 20 `ic_deposit`, 25 `DepTx`/`DepRd`.  Of these the 34
  MAIN-ONLY files (the `*AU*`, `FsCollect*`, `ProofNparEra`/`NamexEra`,
  `ProofSysUnlinkAU*`, `ProofCreateAU*`, `TxPin`, `FsCfgKits`) have no flip
  twin and are adapted by hand using the same fix-table classes
  (destructure the new reference bundle; `iMod` the modal transports;
  `ic_ref_stamps_split` beside `live_gen_split`).  Most take the reference
  opaquely and need nothing.
- The collection (`FsCollect`, `FsCollectAll`) is re-proven against the box
  body per §3.4.3's last row; it is the acceptance test of the stitch.

Gate for r21 (the ICACHE BANK): everything in the icache lane and the FS
cone that does not sit behind ProcInv is green; zero new admits; `main`
merged in.

---------------------------------------------------------------------------

## 4. The lanes after the icache (everything else that is red or owed)

L1. **ProcInv — the keystone (350 files).**  `tf_word_phys_to_mem`/
    `ctx_phys_word_shim`: main's trapframe words are stated on a PHYSICAL
    tier that at TSO has no bridge to the context tier.  Flip's ProcInv is
    shim-free (its one mention is a comment); take flip's `proc_priv`/
    trapframe shapes (A6.141's parked-record idiom, the twin-born-
    dominating fork argument) and keep main's fd-row / park-era API by
    3-way.  Where main's shapes have no flip counterpart (main's fd rows
    postdate the fork) it is new work under the same law: physical words
    of the trapframe are T1 at the running hart or T2 in the proc's parked
    record; never a phys↔ctx equivalence.  Owner input if a main shape
    fits neither (process law 4).  Gate: ProcInv green; the cone
    re-enumerates (expect the r10-class fallout: `iMod` on morphs, opaque
    seals, arity of the obs-tier destructs).

L2. **The shim sweep** — the 26 blocked files + `ProofSysKill`.  Per file,
    flip's twin via `tools/takeflip.sh`/`tools/merge3.sh` (22 files); the
    four main-only ones (`ProofSysReadAU`, `ProofSysWriteAU`,
    `ProofSysWriteConsAU`, `UkStep`) get the same treatment their non-AU
    twins got.  `ProofForkretPark` is taken from flip and expected RED at
    its bracketed `park_globals` bullet until L8.

L3. **`ProofPipealloc:1379`** — `page_own_pipe_raw` is gone (r7 moved
    pipe pages to the A6.87 FILLED page form); restate the pipe page at
    `page_named`/`page_filled` as `ProofPipeclose` already does.

L4. **`RiscvAdequacy:846`** — the machine adequacy statement's era
    allocation (the disk mirror `ghost_var` at the reset machine, r13's row
    design); a local type fix in the allocation block, then the 17 files
    behind it.

L5. **R4a `inode_pay`'s cinv** (endgame §4.3; `FileInvDefs`).  Replace the
    parked ident CELL fractions with ghost identity (agree tier); park the
    ξ-free `inode_shr_genlo_bare`; the credential stays on the borrower
    side (fileread/filewrite hold the floored form).  The cinv body becomes
    ghost+pure ⇒ `is_ftable`'s λ-flip stops recursing into it.  Main's
    `fp_inum` bookkeeping is untouched.

L6. **R4b `off_hold`'s cinv** (endgame §4.4) — COORDINATE WITH MAIN.  Main's
    recent fd-row work (e0bfa5d4e "the u-tier's descriptor view…",
    `FdRowMint`/`FdRowPilot`, `fd-row-pilot.md`) may already dissolve the
    `off` cell into ip->lock's payload; if so take that.  Otherwise: a
    third tiny instance of the SAME box (bundle = the one `off` cell;
    guards ftable.lock / ip->sleeplock).  No bespoke third mechanism.

L7. **The const-payload class** (endgame §4.4b): `LogInv`'s `<{ log_res }>`
    (l_out/l_cmt/l_ncommit as ambient cells; expected a plain λ-flip — run
    the `ctx_move_const` test first), `FileInv`'s `ftable_res` (the
    recorded revert), `IcacheInv`'s dead `<{ itable_res }>` (delete).

L8. **R5**: the recorded reverts (`is_ftable` λ-flip + `ftable_res_at` + the
    consumer re-spells + `park_globals_move`, all in comments at their
    sites on flip), `bio_ctx`'s λ-flip if any remains, and
    `ProofForkretPark`'s `park_globals`/`proc_priv` bullets (the A6.141 §3
    unfold tower; the child twin is born dominating its parker).  Gate:
    ProofForkretPark green.

L9. **R6 bucket C**: `LinkForkretParkPaid` → `LinkUserinit` → `LinkMain` →
    `BootChain`/`BootShared` → `SystemAdequacy` (main has no `FsAdequacyImg`;
    its FS adequacy is the `FsAbs*`/`FsFlushed` tier, already main-side).
    First honest compile of text written while unbuildable; budget a
    fallout tail.  Gate: full `-B` build zero red; port-introduced admits
    zero; `make audit` at baseline.

L10. **Loose ends to carry or refuse from flip** (A6.163): `IcacheBox.v`
    stub — NOT carried (nothing on main requires it); the 1316 tracked
    `iris/*.aux` and the `ZZ*` scratch files — never; `tso-flip-umode` r1
    (the §0.37′ U-mode cone: `utf_translate` token-threaded, `Rut_ctx`
    accessor, `UptWalkTramp` split) — compare against r12's U-tier wave
    and take only what cutover lacks; `SpecAcquire`'s
    `wp_acquire_llb_fresh_sconf` and `SpecAcquiresleep`'s NB λ twin are
    already here (r14/r15).

---------------------------------------------------------------------------

## 5. Order, gates, banking

| round | content | gate |
|---|---|---|
| r18 | IcacheInv per-slot fusion (§3.3), IcachePinwObl, InodeRegion | those files green |
| r19 | site map §3.4.3 vetted (reviewers), then IcacheEscrow + EscrowDeposit + TxPin + IcacheBoot; FsCfgSnap fix | escrow files green; `ic_slot_cover` re-stated |
| r20 | the seven inode proofs + six specs from flip, main's ghost rows in the posts | inode proofs green |
| r21 | the FS-cone consumer sweep incl. FsCollect/FsCollectAll; merge `main` | THE ICACHE BANK: honest-green count ≥ 1132 + the icache cone; zero new admits |
| r22 | L1 ProcInv keystone | ProcInv green; cone re-enumerated and recorded |
| r23–r24 | L2 shim sweep, L3 pipe, L4 RiscvAdequacy | no `TsoCtxShim.` outside comments; RiscvAdequacy green |
| r25 | L5 R4a, L7 const-payload class, L6 R4b (after checking main's fd-row state) | FileInvDefs/FileInv/LogInv λ-shaped; no ξ-bodied cinv left |
| r26 | L8 R5 | ProofForkretPark green |
| r27 | L9 bucket C | SystemAdequacy green |
| r28 | forced `-B` certification, `make audit`, admit inventory, delete `ctx_word4_claim`/TsoCtxShim tombstone/dead `itable_res`; final `main` merge-in | zero red, audit at baseline |
| land | one merge `tso-cutover` → `main` (§0.23′) | owner |

Every round: `git pull` first (main and any sibling agent on `tso-cutover`),
build on the VM, record the honest measure (§1.2) in the round's Amendment,
commit with explicit paths, push.  Rounds r18–r21 are the stitch proper
and are where a reviewer's objection is cheapest to absorb; r19 waits for
the site-map vetting if it arrives in time and proceeds under this file's
table otherwise, recording any deviation in place.

---------------------------------------------------------------------------

## 6. Items that may need an owner ruling (raised now, so they can be pre-empted)

(i)   The collection reads the box (§3.4.3 last row).  Claim: it needs only
      ghost (`X`'s leg, `Q`, the L1 row) — no cell.  If `FsCollectAll`
      turns out to read `valid`/`nlink`, a T3 pin on those two header
      bytes (immutable-while-armed, the same form `iref_set` uses) is the
      lawful answer, not a box change; that would be a new pin site and
      hence a ruling.
(ii)  `DepFrz` kept (§3.2) against flip's deletion: on main it carries the
      freeze window's parked `(t, q)`, which is durable-disk ghost.  Under
      the placement rule it rides the L1 row during OUT_L1 and `Q` after
      (g).  Confirm this is the intended stitch rather than folding the
      share into `DepTx`.
(iii) R4b `off_hold`: which of main's fd-row refactor and the box instance
      wins (L6).
(iv)  ProcInv shapes with no flip counterpart (L1), if any surface.
(v)   SC-only readers added on this branch and still live: `ctx_word4_claim`
      (WpSconfMem.v:207, 8 users) and the r12 UkStepGen threading (recorded
      in Amendment 12); intended fate: replaced by `CtxPinw.wordw_claim`
      and deleted at r28.
(vi)  The pre-existing main Admitted set (§1.3) is outside the port's gate
      — confirm.
(vii) The merge-main cadence (every bank) and the final one-merge landing
      (§0.23′) — confirm nothing else is expected on `main` before then.

---------------------------------------------------------------------------

## 7. Process and tooling (measured facts, not preferences)

### 7.1 Build
From `/shared/xv6iris-2-main`:
```
./gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- sh -c \
  'cd iris && timeout 3300 make -f CoqMakefile -j16 -k 2>&1 | grep -v "^COQC\|^COQDEP\|^ROCQ\|Warning"'
```
The VM is shared (no flock; other agents build concurrently in their own
subdirs); it can be preempted — a rerun resumes.  Background runs log to the
session scratchpad.

### 7.2 The honest measure
Roots = `File "./X.v", line N` lines followed within a few lines by
`Error`; deps = the `X.vo: … Y.vo` lines of `iris/.CoqMakefile.d` on the VM
(fetch them with `grep "^[A-Za-z0-9_]*\.vo " …`); blocked = the transitive
reverse closure of the roots; green = total − roots − blocked.  Never
report `ls *.vo`.  `make -B` on a lane's file set is the only way to
certify a green claim that involves files that were once red.

### 7.3 Merging
`tools/merge3.sh` / `git merge-file --diff3` with base `e1292b382`
(merge-base main / tso-flip); `tools/takeflip.sh` when main has no unique
declaration names; take a file WHOLE where flip deleted sections (the
3-way cannot see deletions); `tools/bupdfix.py` for morph piles.  Flip's
CtxMorph is `==∗`: every `iDestruct (ctx_morph …)` on main-side text becomes
`iMod`.  Main seals `word_pointsto`/`hreg_frame` opaque: flip text that
destructs them needs `iEval (rewrite /name)` first.  Section appendixes must
re-bind the original section variables.

### 7.4 Notes discipline
This file is edited in place and is the plan of record.  Each round adds an
Amendment to `main-tso-readiness.md` (what landed, departures from flip's
text, measured counts, deferred).  `virtio-tso-port.md` is closed.
Design law is read from `origin/tso-flip`'s `tso-escrow-endgame.md` and is
NOT copied here; if the stitch changes a statement in `CtxBox.v`, that file
is edited on this branch and the change recorded in the endgame doc's
changelog on this branch (a copy is brought over at r19 for that purpose).
