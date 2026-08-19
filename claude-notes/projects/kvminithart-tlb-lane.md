# CHECKPOINT: the kvminithart TLB lane (handoff, 2026-08-19)

Branch `hart-node-port`, clean at **`9466bad8`**, nothing pushed.
Baseline: **8 red roots**, unchanged all session —
`ProofKvminithart`, `ProofMain`, `ProofMainSecondary`, `ProofUser`,
`UserretPt`, `UservecExitPt`, `UserretEntryPt`, `WpUmodeStep`.

Read [`main-cycle-port.md`](main-cycle-port.md) — "THE KVMINITHART LANE: THE
SETTLED ANSWER" and "THE FIFTEEN DATA-LEAF SITES" — before this file. This
file is the *state*; that one is the *design*.

---

## 1. THE QUESTION THAT WAS SETTLED, AND MUST NOT BE RE-OPENED

**`bare_inv` must NOT own the `tlb` cell.** Commit `6b5d1eb2` put it there;
that is the disease, and "ruling 1" (drop the cell from kvminithart's
precondition) is CANCELLED — it was a symptom.

The pre-port proof worked for an ARBITRARY `tlbvec0` because it kept the cell
**in kvminithart's own hand**: `ProofKvminithart` +0x08 does
`iMod (reg_update _ tlb _ tlbz1 with "Hreg Htlb")` and keeps `Htlb` *and*
`Hnone1`; +0x0c..+0x1a run on `Hcg` alone; +0x1c consumes both. Nothing is
remembered *through* a resealed invariant, because the cell never enters one.

Three traps, all of which cost real time this session:

* "the funnel is arm-blind at `strans_regime`, so there is one frame set" —
  WRONG. It confuses a lemma's *statement* with its *proof*; `strans_inv` is a
  disjunction and can be case-split inside a proof.
* splitting the arm at each of the fifteen data-leaf sites — prove ONE lemma
  that absorbs the split instead.
* a fractional/half `tlb` points-to at Bare — a different frame POSITION or
  FRACTION at the two arms forces the fifteen-way split just as deleting the
  cell does.

**A port must not need a hypothesis the original did not.** An attempt to add
a 17th `RiscvLang.reset_regs` conjunct ("the TLB is empty at power-on") was
written, built green, and REVERTED for this reason. Do not re-introduce it.

---

## 2. WHAT LANDED (all verified green; tree regression-free at each step)

| commit | what |
|---|---|
| `c9cdcb70` | worklist: the tlb question settled; both earlier answers cancelled *in place* |
| `fdb57641` | `HartSFrame`: `s_Drwb` (= `s_Drw` minus `tlb`), the `s_frame_ok` record + both instances; `SmodeCorePt`'s dispatch section and `spt_tr_obl_of_regime_D` generic in the write set. **Also: build 438 s → 20.3 s** |
| `3e5bfe8d` | `WpIntrInv`: `swp_run_hart_active_instr_S_res_D`, `i_Db_in_gen`, `s_cells_b` / `s_frames_cells_b` |
| `f7a839e7` | `sda_Drwb = ∅` (a Bare *data* frame is `emp`), `sda_translate_D`, the `sda_in_*_D` family |
| `6395e5f3` | `sda_frames_b`, `strans_swp_side_bare`, `sda_tr_obl` |
| `e494ebcf`, `c7d645c9` | **`sda_slot_acc`** — the one lemma that absorbs the split on the data side, in accessor form |
| `553d1630`, `c694f217`, `25812c05` | **all nine data-leaf sites migrated** onto it |
| `ce93d5cc` | `sie_cap_frame_acc` — the instruction-side twin; `s_tlb_at`, `s_arm_ok`, `strans_side_of_arm`, `s_cells_D` / `s_frames_cells_D` |
| `25fe4ca9` | `sie_cap_cells_at` — re-opening the slot after a leaf that FLIPS THE ARM; `strans_kpt_on`, `s_kpt_wit`, `s_rw_ext_D` |
| `11eb3a09` | `Global Opaque s_tlb_at` |
| `ba32b71e` | revert of the funnel wiring (see §3) |
| `9466bad8` | **`swp_run_hart_active_instr_S_res_b`** and the `iApply` diagnosis (see §3) |

The nine data sites (`WpSconfLock` 1, `WpSconfMem` 2, `WpPlic` 2,
`WpVirtioDev` 2, `ProofUart` 2) now keep the translation slot FOLDED exactly
as their pre-port proofs did, take an ABSTRACT write set from `sda_slot_acc`,
and get their translation obligation already discharged at it. **No leaf
statement changed and every site is shorter than before.**

---

## 3. THE PERFORMANCE BUG — read this before touching the funnel

Measured in `WpSmodeIntr.v`, everything else identical:

```
iApply (swp_run_hart_active_instr_S_res  ...)                 13.5 s, green
iApply (swp_run_hart_active_instr_S_res_D s_Drw
          s_frame_ok_Drw ...)                                 DIVERGES
```

Same instantiation, same arguments. The only difference is that the second
lemma has the **write set in a PARAMETER position**, so `iApply`'s unification
against the cycle's WP goal must work through it and does not terminate. A
plain build ran **112 minutes** without finishing.

Did NOT help: dropping the `s_regime` parameter; `Opaque` on `s_tlb_at`;
splitting the funnel into two CONCRETE branches. All three still went through
that one `iApply`.

**The fix, verified:** generalise the *proof*, keep the call site's
*statement* concrete. `WpIntrInv.swp_run_hart_active_instr_S_res_b` states the
Bare instance outright and discharges it by applying the generic lemma **at the
term level**, where there is nothing to unify — 41 s, no admits. Its premise is
`bare_satp_ok` (not the `strans` disjunction), since that instance IS the Bare
arm and it is what `strans_swp_side_bare` needs.

**Bisecting this class of bug:** wrap the suspect tactic in `Timeout n` — it
turned a 30-minute experiment into a 4-minute one. `rocq compile -time` shows
every other command in the file under 0.4 s with the last one never returning.

Related, same session: one `set_solver` in a tower-carrying context cost 417 of
`SmodeCorePt`'s 438 seconds. `set_solver` normalises the WHOLE context; use
`elem_of_union_l` / `_r` / `elem_of_subseteq` by name there.
(`FastSetSolver` does NOT cure this — see `durable-notes.md`.)

---

## 4. WHAT IS LEFT, IN ORDER

### 4a. Finish the SIE=0 funnel (unblocked; est. small now)

`WpSmodeIntr.wp_instr_s_sconf_off_clock` is at its ORIGINAL committed form.
To convert it:

1. open with `sie_cap_frame_acc` → `(SD satp0 tlbv pcfg paddr)` plus
   `%Harm`, `#Hwitk`, and the closer;
2. `destruct (s_arm_cells _ _ Harm) as [-> | ->]` immediately, so both
   branches are CONCRETE (this is what §3 requires);
3. in each branch use the concrete engine —
   `swp_run_hart_active_instr_S_res` at `s_Drw`,
   `swp_run_hart_active_instr_S_res_b` at `s_Drwb` — plus
   `s_frames_cells_D … SD Hcellsok` and the `sf_*` memberships;
4. hand the leaf its capability through the closer, and re-open with
   `sie_cap_cells_at SD` (which absorbs a leaf that flipped the arm);
5. `WpSmodeWfi` has one more `sie_cap_to_cells` site, same treatment.

The two-branch text was written once and is recoverable from the reflog /
`ba32b71e^`; only the engine calls need to become the concrete pair.

### 4b. Then, and only then, flip `bare_inv`

* restrict `sie_cap_to_cells` / `_of_cells` to `b = true` (the SIE=1 engine is
  KPT-only via `IntrDefs.sie_cap_on_kpt`), so they survive the flip;
* add `sr_walks : bool` to `s_regime` and guard `sr_swp_open` / `sr_swp_close`
  on it (`bare_regime`, `strans_regime` := false; `kpt_share_regime` := true).
  Checked: every user of `wp_instr_s_config_sr` / `wp_instr_s_sr`
  (`WpSmodePt{Mem,Btype,Leaves,Ctl}`) is instantiated at `kpt_share_regime`,
  so they pass `eq_refl`;
* drop `tlb ↦ᵣ tlbv` from `SRegime.bare_inv`; revert `52f89133`'s
  BootBridge / SpecMain routing; keep kvminithart's `tlb ↦ᵣ tlbvec0` premise.

### 4c. kvminithart itself (closes 3 roots)

Port `ProofKvminithart`'s three raw blocks (+0x08, +0x1c, +0x20) onto
`WpSconfSfence.wp_sfence_vma_s_sconf` (cell-premise, already landed) plus a
`csrw satp` switch leaf whose composer half is landed
(`WpSconfCsr.swp_write_CSR_satp_S`). The switch leaf takes the `tlb` cell as a
caller argument and takes only satp/pmp from `strans_inv_acc_bare`. Then fix
`ProofMain` / `ProofMainSecondary`'s `iDestruct "Hhart"` over-destructure.

**NOTE for 4c:** the satp switch FLIPS THE ARM inside its own `execute`. That
is why `sie_cap_cells_at` exists; do not be surprised by it.

### 4d. The other four roots — independent, and none of them small

* `UserretPt`, `UservecExitPt`, `UserretEntryPt` need **`wp_instr_u_pt`** and
  **`wp_instr_ktramp_pt_share`**, which **do not exist anywhere in the tree**
  (`grep` finds only uses). A per-node trampoline instruction engine has to be
  written. `TrampStepPt` provides only `wp_instr_tramp_pt`.
* `WpUmodeStep` references `minstret_inv_body`, which no longer exists —
  `MinstretInv.minstret_inv` is `emp` post-port. Needs porting to the trivial
  form.
* `ProofUser` needs P7 §5 assembly plus the last two memory arms
  (`arm_STORECON_u`, `arm_AMO_u`), blocked on `u_sc_pure` covering only the
  reservation-held outcome. See `user-tier-port.md` §16.

---

## 5. BUILD RECIPES

```
whole tree:  ./gcp-rocq/run-on-gcp make -k -j36 proofs
one file:    ./gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- \
               make -C iris -f CoqMakefile -j36 X.vo
profile:     ... TIMING=1 X.vo   then, with --no-sync, read iris/X.v.timing
             (artifacts are NOT synced back from the VM)
```

Always run these from the repo root — a `cd` into `iris/` earlier in the same
shell makes `./gcp-rocq/run-on-gcp` vanish. **Check `$?`, not grep output:** a
grep-filtered build log produced several FALSE GREENS this session.

Standing rules: no caller-visible leaf/spec change without the user; every
address claim from `mem_pointsto_claim` / `wordw_claim_of`; per-file build over
5 min is a bug; commit by explicit path; never `git stash` / `reset` /
`commit --amend`, never leave anything staged. **Do not leave runaway compiles
on the VM** — four accumulated this session and had to be killed by PID with
the user's permission.
