/-
Weak: **the EVENT-GRANULAR weak-memory language** (spike S1).

Rocq: `iris/WeakEvLang.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

Design: `claude-notes/design/weak-memory-event-granular.md` (the REVISED 2026-08-14
"expression-resident monad" section); worklist `claude-notes/projects/weak-memory-event-lang.md`
(deliverable S1).

`WeakLang.wprimStep`'s hart arm runs a WHOLE INSTRUCTION (`wrun (riscvStep tick)`) in one
language step.  THIS language's hart arm runs ONE EVENT of the Sail interaction monad, without
oracles: the device fabric is σ's and the residual monad is the EXPRESSION's.

THE PLACEMENT RULE.  Control state goes in the EXPRESSION exactly where control flow is
MODEL-DEFINED, and in σ where it is MEMORY-DEFINED.  INTER-instruction control flow is
memory-defined (the next instruction comes from a fetch), so the boundary stays a boring token
`ELoop`.  INTRA-instruction control flow is model-defined (the continuation IS the Sail monad
value `riscvStep tick` hands out), so it rides in `ECycle`, is consumed monotonically, and
WP-of-an-instruction becomes proof by SYNTACTIC DESCENT on that argument.  The disk carries its
whole operation state, a RESIDUAL DEVICE PROGRAM (M5, `VirtioProg.DM`), exactly as a hart does.

  σ                = `WeakLang.WGState` VERBATIM (no new fields);
  `ELoop g c`      = hart `c` at an instruction boundary;
  `ECycle g c m fn` = hart `c` executing one instruction, `m` the residual monad and `fn` the
                     parked second fence;
  `EDisk g dp dws` = the disk agent: the residual device program (`none` between bursts) and
                     its own view;
  `EDev g d tid m` / `EPower` = the other devices and the power thread (deviation 2).

RECORDED DECISIONS (Rocq D1–D5):
(D1) THE DEVICE ACCESSORS ARE THE PARTIAL ONES (`devRead`/`devWrite`): a bad width or an
     undecoded offset inside a device window is a STUCK node ("stuck-is-fine").
(D2) THE STORE ARM COMPUTES THE MESSAGE CLASS (`wmClassOf ak ws`), so there is no free class
     binder; the conditional write gets `WCexcl` (`wmClassOf` returns it exactly at `akLatest`).
(D3) THE RMW IS SPLIT: an exclusive read is ONE event (`LExLoad`-shaped: ordinary read semantics
     plus the agent-local reservation), a conditional write ANOTHER (`LExStore`-shaped: ordinary
     write semantics plus the per-byte window check); a dangling exclusive read is a legal
     trace; the conditional-write node carries a silent RETRY self-loop.
(D4) INTERRUPT DELIVERY IS ONLY THE PLIC THREAD'S (Lean: the PLIC device program's `setPin`).
(D5) THE PARKED FENCE GATES EVERYTHING: while `fn` is `some _` the ONLY move of
     `ECycle g c m fn` is to fire it, and `ECycle _ _ (pure ()) fn` pops to the boundary only at
     `fn = none`.

## Deviations from Rocq

1. NAMES: the tree's camelCase (name map below).  `eexpr` ↦ `EExpr` with constructors `Sail`,
   `EDev`, `EDisk`, `EPower`; `wgstate` fields are WeakLang's (`σ.wgregs c`, …).
2. DEVICES (forced by Lean's device model, `Weak/WeakLang.lean` deviation 2).  Rocq's `EUart g` /
   `EPlic g` ran `RiscvLang.uart_step` / `plic_step`, which have no Lean counterpart: Lean's
   devices are PROGRAMS of `MachCSL.Dev.DevLang`.  So both become ONE arm, `EDev gen d tid m`,
   stepped by WeakLang's own `wdevStep` (its forks re-embedded by `ofWExpr`).  `epowerFork`
   forks the two UARTs and the PLIC as `EDev` root threads, and the disk ONLY as the M5 agent
   `EDisk gen none wsInit` (no flat-DMA virtio thread exists in this language; `EDev` is not
   guarded against `.virtio`, but nothing creates such a thread).  Consequences:
   - `euart_step`, `eplic_step` are not defined; their uses are `wdevStep`.
   - The disk's PLIC LATCH arm (Rocq's eighth `edisk_step` disjunct, `plic_latch` on
     `dev_irq_level virtio_irq_id`) is DROPPED: in Lean the PLIC program itself `sample`s every
     source's level (`devLevel`, which for the disk is `(devSig .virtio).irq`) and latches it,
     so the latch is a step of the `EDev .plic` thread (the disk arms: deviation 14).
   - `eprim_step_{uart,plic}_inv` ↦ `eprimStepDevInv`; `eprim_step_{uart,plic}_dead` ↦
     `eprimStepDevDead`; `eprim_step_uart_idle` ↦ `eprimStepDevLive` (a live device thread
     always steps, `wdevStepTotal`); `eprim_step_plic_wire` ↦ `eprimStepDevSetPin` (the wire
     write is the `setPin` primitive); `euart_step_ws`/`eplic_step_ws` ↦ `edevStepWs`.
   - THE DISK'S FABRIC: Rocq `dvirtio (wgdev σ)` / `set_dvirtio` are the Lean-only
     `dvirtio σ.wgdev := σ.wgdev.st .virtio` / `setDvirtio ds v := ds.set .virtio v` over
     `MachCSL.VirtioState` (`Weak/VirtioProg.lean` deviation 1).
3. `eprimStep` is a `match` on the expression (as `WeakLang.wprimStep`, its deviation 3) rather
   than a five-way disjunction; each arm's body is Rocq's.  `ELoop`/`ECycle` are `abbrev`s
   (Rocq: transparent definitions).  `eval`/`eobs` are `Empty` in the `Language` instance
   `weakEvLang` (Rocq `weak_ev_lang`; `weak_ev_lang_mixin` ↦ `weakEvLangMixin`, its `val_stuck`).
4. THE MONAD (`Weak/WeakInterp.lean` deviation 4): `M unit` ↦ `SailM Unit`; one arm per lean-sail
   `Outcome` constructor.  A model `.error` node and the legacy `readRam`/`writeRam` are stuck
   (Rocq: `GenericFail`/`Discard`/the Sail exception); read answers are `.Ok (w, none)`, write
   answers `.Ok (some true)`, as MachCSL's `evStep` (WeakInterp deviation 5); `tlbi` is
   Rocq `TlbOp`; `GetCycleCount` answers `0`; `choose` branches.  A RAM/MMIO write whose
   request carries `value = none` is stuck (WeakInterp deviation 6).
5. O2 — THE READ ARM (`notes/weak-port-o2-design.md` §1.4, owner decisions O2/D2/D3/D4).  Rocq's
   RAM-read arm was guarded by `ak_coh (classify …) = false` (a fetch, being `AK_ifetch` in the
   Lean model, would have been STUCK).  It is now a TOTAL three-way split on `classify`:
   - `akIfetch = true`: THE I-CACHE READ.  `∃ w tvs`, the byte list of `w`, admissible by
     `ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) (paZ pa) tvs` at the hart's instruction view
     (Stage B, D2), `σ' = σ` (view-silent: no `readOk`, no `loadPostRun`, no address sources);
   - `akIfetch = false`, then Rocq's plain (`akLatest = false`) / exclusive (`akLatest = true`)
     disjunction verbatim.
   The design's Stage-A text (`ifetchOk … 0 …`) is superseded by D2: the language uses the
   hart's own `wgitv`.  (`WeakPromise.wpstep.WPIFetch` still checks at view 0; that is the
   promise machine's sound over-approximation, `Weak/WeakInterp.lean` B5.)
6. O2 STAGE B — THE BARRIER ARM.  Rocq: `σ' = ewg_ws σ c (efence_apply ws0 (ebar_now b))`.
   Lean: `σ' = ewgBar σ c (efenceApply ws0 (ebarNow b)) (itvPost ws0 (σ.wgitv c) b)` (new
   σ-shape `ewgBar` = `ewgWs` plus the hart's `wgitv`): `fence.i` raises the instruction view to
   `max itv (max ws.wVrNew ws.wVwOld)` exactly as `WeakInterp.wbarrierPost`; every other barrier
   leaves it (`itvPostNotI`).  The data views are Rocq's.
7. SYMBOLIC ANNOUNCES (`notes/symbolic-model.md`): Rocq's `InstrAnnounce ob` (a `bvn`) is Lean's
   `.instrAnnounce n w` (`w : BitVec n`); `ib_of_bvn o := Z_to_bv 32 (bvn_unsigned o)` ↦
   `ibOfBvn w := BitVec.ofNat 32 w.toNat` (the same zero-extension).  The arm is Rocq's: bank
   `ibAnn (ibOfBvn w)` and apply `instrPost`.  `.branchAnnounce n pc` is silent, as Rocq's.
   Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a)): at an SFENCE.VMA announce
   (`sfAnnB n w`, the opcode test) the program half labels the node with the sfence MARKER
   `LFence false false false false` (`annLabel`, a graph event) instead of `LInstr`, so the
   language applies the marker's identity instead of `instrPost` there (`annPost`); the reset
   still happens at the instruction boundary.
8. REGISTER NAMES.  Lean's `Register` is a flat enumeration (Rocq: `R_bitvector_64 rb` etc.), so
   `ereg_gpr_num` is an explicit `x1 ↦ 1 … x31 ↦ 31` table (Rocq: `num_of_register_bitvector_64`
   in `[16, 46]` minus 15 — the same map), and `ereg_csr_num` matches `.satp`, …, `.mcounteren`,
   `.pmpaddr_n`, `.pmpcfg_n` directly.  `register_beq r nextPC` is `decide (r = .nextPC)`;
   `register_lookup r rs` is `rs r`, `register_set r v rs` is `rs.set r v`.
9. `ewg_rw`'s `ERWnone` split (Rocq: no functional extensionality) is kept verbatim, although
   Lean has `funext`.
10. LISTS: `tvs.*1`/`tvs.*2` ↦ `tvs.map Prod.fst`/`Prod.snd`; `l !! j` ↦ `l[j]?`; `remove_dups` ↦
   `MachCSL.Stdpp.removeDups` (stdpp's, keeps last occurrences); `⊆` on lists is `List.Subset`;
   `S (length lg0)` ↦ `lg0.length + 1`; `fin_to_nat c` ↦ `c.val`; `N.to_nat n` ↦ `n`.
   `wbytes n v` is `WeakInterpProj.wbytes` (the hart-side one, as in Rocq's `Require` order).
11. The Rocq `Example`s are named `theorem`s, `vm_compute. reflexivity.` ↦ `decide +kernel`
   (`Weak/WeakDeps.lean` recipe).
12. `eboot_shape`'s device clause `dvirtio σ' = virtio_reset (dvirtio σ)` is the whole-fabric
   `σ'.wgdev = σ.wgdev.reset` (`WeakLang.wbootShape`, WeakLang deviation 5); `ebootShape` is
   stated with WeakLang's clauses.
13. The power-off successor `WGState … (S gen) false …` is `{ σ with wggen := σ.wggen + 1,
   wgpow := false }` (keeps WeakLang's Lean-only `wgitv`/`wgrt`).
14. W-DISK (plan `notes/weak-allocproc-plan.md` §C "W-DISK", [OWN.29]–[OWN.32]): the disk runs the
   program ALIGNED to MachCSL's `Virtio.serve` (`Weak/VirtioProg.lean`), so `ediskStep`'s arms are
   START, `DRead`, `DFence`, the three outcomes of a `DWriteDev` (STORE: the log append AND the
   fabric move `setDvirtio σ.wgdev s'` in one step, under `ramBytes` of the footprint; OWN-GUARD
   SKIP and ABORT: silent, the fabric becomes the folded state), the two of a `DPop` (refused;
   the pop `VirtioProg.popState`), the stall self-loop and `DIdle`.  Rocq's COMMIT arm (`DDone`)
   and its malformed-chain arm with the arbitrary store chain `dm_wild_chain` /
   `dm_wild_chain_wf` are RETIRED (not ported any more); `ediskStepWf`, `ediskStepWs` and
   `eprimStepDiskReducible` are re-proved over the new arms.  Lean-only `setDvirtioSelf`.

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Rocq → Lean name map.**  `eexpr` `EExpr` (`Sail` `EExpr.Sail`, `EDisk` `EExpr.EDisk`,
`EPower` `EExpr.EPower`, `EUart`/`EPlic` `EExpr.EDev`), `ELoop` `ELoop`, `ECycle` `ECycle`,
`eval`/`eobs`/`eof_val`/`eto_val` the instance's `Empty`/`ofVal`/`toVal`, `epower_fork`
`epowerFork`, `ewg_reg` `ewgReg`, `ewg_dev` `ewgDev`, `ewg_ws` `ewgWs`, `ewg_store` `ewgStore`,
`ewg_regwslog` `ewgRegwslog`, `ewg_log` `ewgLog`, `oib32` `Ibch`, `ib_of_bvn` `ibOfBvn`,
`ewg_ib` `ewgIb`, `ewg_ib_regs/log/ws/dev/img/at/ne` `ewgIbRegs/Log/Ws/Dev/Img/At/Ne`,
`ewg_regws` `ewgRegws`, `ewg_ibws` `ewgIbws`, `erw_kind` `ErwKind`, `ereg_gpr_num`
`eregGprNum`, `ereg_csr_num` `eregCsrNum`, `ereg_num` `eregNum`, `has_ldres` `hasLdres`,
`has_ldres_intro` `hasLdresIntro`, `erw_srcs` `erwSrcs`, `erw_srcs_ldres` `erwSrcsLdres`,
`erw_srcs_reg` `erwSrcsReg`, `erw_srcs_covers` `erwSrcsCovers`, `erw_srcs_mono`
`erwSrcsMono`, `ib_rd` `ibRd`, `ib_rd_bits` `ibRdBits`, `erw_dest` `erwDest`, `erw_of` `erwOf`,
`erw_label` `erwLabel`, `erw_ws` `erwWs`, `erw_ws_depmove` `erwWsDepmove`, `ewg_rw` `ewgRw`,
`ewg_rw_img/log/dev/pow/gen/ib/ws/ws_ne/regs` `ewgRwImg/Log/Dev/Pow/Gen/Ib/Ws/WsNe/Regs`, every
test `erw_of_<x>` `erwOf<X>` (e.g. `erw_of_lw_rd` `erwOfLwRd`, `erw_of_csrrci_sstatus_gpr`
`erwOfCsrrciSstatusGpr`), `edeps` `edeps`, `erds` `erds`, `ebar_now` `ebarNow`, `ebar_park`
`ebarPark`, `efence_apply` `efenceApply`, `efence_barrier_post` `efenceBarrierPost`,
`efence_apply_le` `efenceApplyLe`, `emonad_step` `emonadStep`, `ecycle_step` `ecycleStep`,
`ddev_ak` `ddevAk`, `ddev_class` `ddevClass`, `ddev_class_eq` `ddevClassEq`, `ddev_ak_plain`
`ddevAkPlain`, `edisk_step` `ediskStep` (re-stated by W-DISK, deviation 14), `edp_wf` `edpWf`, `edp_wf_none`
`edpWfNone`, `eboot_shape` `ebootShape`, `ethread_live` `ethreadLive`,
`ethread_live_wthread_live` `ethreadLiveWthreadLive`, `eprim_step` `eprimStep`,
`weak_ev_lang_mixin` `weakEvLangMixin`, `weak_ev_lang` `weakEvLang`, `eprim_step_loop_inv`
`eprimStepLoopInv`, `eprim_step_cycle_inv` `eprimStepCycleInv`, `eprim_step_disk_inv`
`eprimStepDiskInv`, `eprim_step_power_inv` `eprimStepPowerInv`, `ecycle_step_img`
`ecycleStepImg`, `ecycle_step_era` `ecycleStepEra`, `ecycle_step_shape` `ecycleStepShape`,
`ecycle_step_log_app` `ecycleStepLogApp`, `ecycle_step_ws_other` `ecycleStepWsOther`,
`ecycle_step_ws_le` `ecycleStepWsLe`, `edisk_step_ws` `ediskStepWs`, `eprim_step_loop_dead`
`eprimStepLoopDead`, `eprim_step_loop_live` `eprimStepLoopLive`, `eprim_step_cycle_dead`
`eprimStepCycleDead`, `eprim_step_disk_dead` `eprimStepDiskDead`, `eprim_step_power_off`
`eprimStepPowerOff`, `edisk_step_wf` `ediskStepWf`, `eprim_step_disk_reducible`
`eprimStepDiskReducible`; the device lemmas as in deviation 2.
Lean-only: `ewgBar` (+ `ewgBarWs`, `ewgBarItv`), `ofWExpr`, `dvirtio`, `setDvirtio`,
`ecycFrameSt` and its shape lemmas, `ecycleStepFrame` (the one case analysis the six
`ecycle_step_*` lemmas are read off), `ecycleStepItvLe`, `edevStepWs`; Q7 (deviation 7):
`sfAnnB`, `annLabel`, `annPost` (+ `annLabelSf/Not/Or`, `annPostSf/Not/Le/Depmove/Bounded`),
`WeakEvLang.noSfAnn` (the path premise of the generic admin-run lemmas, AxFetch1).

**Not ported:** `euart_step`, `eplic_step` and the disk's PLIC-latch arm (deviation 2: Lean's
devices are programs; uses checked: only this file's own `eprim_step`/inversion/`_ws` lemmas,
which are re-stated over `wdevStep`).

**Statements checked** (by hand, against Rocq): all; the changed ones are the deviations above
(`emonadStep`'s MemRead and Barrier arms, deviations 5–6; the device lemmas, deviation 2).
-/
import Weak.WeakLang
import Weak.WeakDeps
import Weak.WeakInterpProj
import Weak.VirtioProg

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 1. The expressions -/

/-- The event language's expressions (deviation 2): a hart with its residual monad and parked
fence; a non-disk device task (Rocq `EUart`/`EPlic`); the disk agent with its residual program
and own view; the power thread. -/
inductive EExpr where
  | Sail (gen : Nat) (cpu : CPU) (m : SailM Unit) (fn : Option (Bool × Bool × Bool × Bool))
  | EDev (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d)
  | EDisk (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate)
  | EPower

/-- THE BOUNDARY VALUE: the hart sitting at the monad's own terminal value. -/
abbrev ELoop (gen : Nat) (cpu : CPU) : EExpr := .Sail gen cpu (FreeM.pure ()) none

abbrev ECycle (gen : Nat) (cpu : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) : EExpr := .Sail gen cpu m fn

/-- The thread pool a fresh era forks: one hart thread per CPU, the UARTs and the PLIC as
device programs, and the disk agent with the EMPTY burst and a FRESH view. -/
def epowerFork (gen : Nat) : List EExpr :=
  cpus.map (ELoop gen) ++
    [.EDev gen (.uart .uart0) rootTask (.pure ()), .EDev gen (.uart .uart1) rootTask (.pure ()),
     .EDisk gen none wsInit, .EDev gen .plic rootTask (.pure ())]

/-- The re-embedding of a WeakLang thread (what `wdevStep`'s forks spawn) (Lean-only). -/
def ofWExpr : WExpr → EExpr
  | .loop gen cpu => ELoop gen cpu
  | .dev gen d tid m => .EDev gen d tid m
  | .power => .EPower

/-! ## 2. σ-updates -/

def ewgReg (σ : WGState) (c : CPU) (rs : RegFile) : WGState :=
  { σ with wgregs := updCpu σ.wgregs c rs }

def ewgDev (σ : WGState) (d : DevStates) : WGState := { σ with wgdev := d }

def ewgWs (σ : WGState) (c : CPU) (ws : Wstate) : WGState :=
  { σ with wgws := updCpu σ.wgws c ws }

def ewgStore (σ : WGState) (c : CPU) (ws : Wstate) (lg : List Wmsg) : WGState :=
  { σ with wglog := lg, wgws := updCpu σ.wgws c ws }

/-- THE REGS + VIEW + LOG SHAPE (the hart-side state-interpretation accessor needs it). -/
def ewgRegwslog (σ : WGState) (c : CPU) (rs : RegFile) (ws : Wstate) (lg : List Wmsg) : WGState :=
  { σ with wgregs := updCpu σ.wgregs c rs, wglog := lg, wgws := updCpu σ.wgws c ws }

def ewgLog (σ : WGState) (lg : List Wmsg) : WGState := { σ with wglog := lg }

/-! ### D3: the instruction-bits field -/

/-- The announced word, ZERO-EXTENDED to 32 bits (lossless: an RVC halfword has
`bits[1:0] ≠ 0b11`). -/
def ibOfBvn {n : Nat} (w : BitVec n) : BitVec 32 := BitVec.ofNat 32 w.toNat

/-- The hart's instruction channel moves, and NOTHING ELSE does. -/
def ewgIb (σ : WGState) (c : CPU) (v : Ibch) : WGState :=
  { σ with wgib := updCpu σ.wgib c v }

theorem ewgIbRegs (σ : WGState) (c : CPU) (v : Ibch) : (ewgIb σ c v).wgregs = σ.wgregs := rfl
theorem ewgIbLog (σ : WGState) (c : CPU) (v : Ibch) : (ewgIb σ c v).wglog = σ.wglog := rfl
theorem ewgIbWs (σ : WGState) (c : CPU) (v : Ibch) : (ewgIb σ c v).wgws = σ.wgws := rfl
theorem ewgIbDev (σ : WGState) (c : CPU) (v : Ibch) : (ewgIb σ c v).wgdev = σ.wgdev := rfl
theorem ewgIbImg (σ : WGState) (c : CPU) (v : Ibch) : (ewgIb σ c v).wgimg = σ.wgimg := rfl
theorem ewgIbAt (σ : WGState) (c : CPU) (v : Ibch) : (ewgIb σ c v).wgib c = v :=
  gibInsertEq _ _ _
theorem ewgIbNe (σ : WGState) (c : CPU) (v : Ibch) (c' : CPU) :
    c' ≠ c → (ewgIb σ c v).wgib c' = σ.wgib c' :=
  gibInsertNe _ _ _ _

/-! ### D3-2: the combined shapes -/

def ewgRegws (σ : WGState) (c : CPU) (rs : RegFile) (ws : Wstate) : WGState :=
  { σ with wgregs := updCpu σ.wgregs c rs, wgws := updCpu σ.wgws c ws }

def ewgIbws (σ : WGState) (c : CPU) (v : Ibch) (ws : Wstate) : WGState :=
  { σ with wgws := updCpu σ.wgws c ws, wgib := updCpu σ.wgib c v }

/-- O2 STAGE B (deviation 6, Lean-only): the barrier shape, the data view AND the hart's
instruction view. -/
def ewgBar (σ : WGState) (c : CPU) (ws : Wstate) (itv : Nat) : WGState :=
  { σ with wgws := updCpu σ.wgws c ws, wgitv := updCpu σ.wgitv c itv }

theorem ewgBarWs (σ : WGState) (c : CPU) (ws : Wstate) (itv : Nat) :
    (ewgBar σ c ws itv).wgws c = ws := gwsInsertEq _ _ _
theorem ewgBarItv (σ : WGState) (c : CPU) (ws : Wstate) (itv : Nat) :
    (ewgBar σ c ws itv).wgitv c = itv := by
  simp [ewgBar, updCpu]

/-! ## 2b. D3-2: which register write carries a dependency -/

/-- THREE KINDS, and the classification is TOTAL. -/
inductive ErwKind where
  | ERWnone
  | ERWreg (rd : Nat) (srcs : List Dsrc)
  | ERWctrl (srcs : List Dsrc)
  deriving DecidableEq, Inhabited

open ErwKind

/-- The architectural number of a GPR register (`x0` has no register; deviation 8). -/
def eregGprNum (r : Register) : Option Nat :=
  match r with
  | .x1 => some 1 | .x2 => some 2 | .x3 => some 3 | .x4 => some 4 | .x5 => some 5
  | .x6 => some 6 | .x7 => some 7 | .x8 => some 8 | .x9 => some 9 | .x10 => some 10
  | .x11 => some 11 | .x12 => some 12 | .x13 => some 13 | .x14 => some 14 | .x15 => some 15
  | .x16 => some 16 | .x17 => some 17 | .x18 => some 18 | .x19 => some 19 | .x20 => some 20
  | .x21 => some 21 | .x22 => some 22 | .x23 => some 23 | .x24 => some 24 | .x25 => some 25
  | .x26 => some 26 | .x27 => some 27 | .x28 => some 28 | .x29 => some 29 | .x30 => some 30
  | .x31 => some 31
  | _ => none

/-- ... AND THE NON-GPR DESTINATIONS THE DEPENDENCY TRACK KNOWS: `WeakDeps`' CSR
pseudo-registers (DEC-6).  `sstatus`/`sie`/`sip` are views of `mstatus`/`mie`/`mip`. -/
def eregCsrNum (r : Register) : Option Nat :=
  match r with
  | .satp => some (wcsr SATP)
  | .sepc => some (wcsr SEPC)
  | .mepc => some (wcsr MEPC)
  | .sscratch => some (wcsr SSCRATCH)
  | .mscratch => some (wcsr MSCRATCH)
  | .stvec => some (wcsr STVEC)
  | .mtvec => some (wcsr MTVEC)
  | .mstatus => some (wcsr MSTATUS)
  | .mie => some (wcsr MIE)
  | .mip => some (wcsr MIP)
  | .medeleg => some (wcsr MEDELEG)
  | .mideleg => some (wcsr MIDELEG)
  | .menvcfg => some (wcsr MENVCFG)
  | .mhartid => some (wcsr MHARTID)
  | .mtime => some (wcsr TIME)
  | .scause => some (wcsr SCAUSE)
  | .stval => some (wcsr STVAL)
  | .stimecmp => some (wcsr STIMECMP)
  | .mcounteren => some (wcsr MCOUNTEREN)
  | .pmpaddr_n => some (wcsr PMPADDR0)
  | .pmpcfg_n => some (wcsr PMPCFG0)
  | _ => none

def eregNum (r : Register) : Option Nat :=
  match eregCsrNum r with
  | some n => some n
  | none => eregGprNum r

/-- Does the decoded source list carry the load result? -/
def hasLdres : List Dsrc → Bool
  | [] => false
  | .DLdRes :: _ => true
  | _ :: t => hasLdres t

theorem hasLdresIntro (l : List Dsrc) : Dsrc.DLdRes ∈ l → hasLdres l = true := by
  induction l with
  | nil => intro h; cases h
  | cons a l ih =>
    intro h
    cases a with
    | DLdRes => rfl
    | DReg r =>
      rcases List.mem_cons.1 h with h | h
      · cases h
      · exact ih h

/-- THE DYNAMIC SOURCE LIST (DEC-7): the decoded list's `DLdRes` flag, then one `DReg` per
DISTINCT register the instruction has read so far. -/
def erwSrcs (dec : List Dsrc) (rds : List Nat) : List Dsrc :=
  (if hasLdres dec then [.DLdRes] else []) ++ (removeDups rds).map Dsrc.DReg

theorem erwSrcsLdres (dec : List Dsrc) (rds : List Nat) :
    Dsrc.DLdRes ∈ dec → Dsrc.DLdRes ∈ erwSrcs dec rds := by
  intro hin
  simp [erwSrcs, hasLdresIntro dec hin]

theorem erwSrcsReg (dec : List Dsrc) (rds : List Nat) (r : Nat) :
    r ∈ rds → Dsrc.DReg r ∈ erwSrcs dec rds := by
  intro hin
  unfold erwSrcs
  refine List.mem_append_right _ (List.mem_map.2 ⟨r, ?_, rfl⟩)
  exact elem_of_remove_dups.2 hin

/-- THE COVERAGE TEST: every DECODED source is a DYNAMIC source as soon as the run has read
the register it names. -/
theorem erwSrcsCovers (dec : List Dsrc) (rds : List Nat) (s : Dsrc) :
    s ∈ dec → (∀ r : Nat, s = .DReg r → r ∈ rds) → s ∈ erwSrcs dec rds := by
  intro hin hr
  cases s with
  | DReg r => exact erwSrcsReg dec rds r (hr r rfl)
  | DLdRes => exact erwSrcsLdres dec rds hin

/-- ... and the read set only ever grows, so the source list does not shrink. -/
theorem erwSrcsMono (dec : List Dsrc) (rds rds' : List Nat) (s : Dsrc) :
    rds ⊆ rds' → s ∈ erwSrcs dec rds → s ∈ erwSrcs dec rds' := by
  intro hsub hs
  rcases List.mem_append.1 hs with hs | hs
  · exact List.mem_append_left _ hs
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    exact erwSrcsReg dec rds' r (hsub (elem_of_remove_dups.1 hr))

/-- THE ACCUMULATOR at a `regRead` node. -/
def ibRd (i : Ibch) (r : Register) : Ibch := ibRead i (eregNum r)

theorem ibRdBits (i : Ibch) (r : Register) : (ibRd i r).ibBits = i.ibBits := ibReadBits _ _

/-- One node, one candidate destination. -/
def erwDest (rds : List Nat) (r : Register) (d : Option (Nat × List Dsrc)) : ErwKind :=
  match d with
  | some (rd, srcs) =>
      match eregNum r with
      | some n => if n = rd then .ERWreg rd (erwSrcs srcs rds) else .ERWnone
      | none => .ERWnone
  | none => .ERWnone

/-- DEC-6: a Zicsr access has two destinations, tried in order. -/
def erwOf (role : OpRoles) (rds : List Nat) (r : Register) : ErwKind :=
  if r = .nextPC then
    .ERWctrl (match depsCtrl role with
              | [] => []
              | dec => erwSrcs dec rds)
  else
    match erwDest rds r (depsRd role) with
    | .ERWnone => erwDest rds r (depsRd2 role)
    | k => k

def erwLabel (k : ErwKind) : Wlabel :=
  match k with
  | .ERWnone => .LSilent
  | .ERWreg rd srcs => .LRegW rd srcs
  | .ERWctrl srcs => .LCtrl srcs

/-- Q7 (owner ruling, Lean-only; deviation 7): the SFENCE.VMA opcode test on an announced
word — `sfence.vma rs1, rs2` for any `rs1`/`rs2` (funct7 `0001001`, `rd = 0`, funct3 `000`,
opcode `SYSTEM`). -/
def sfAnnB (n : Nat) (w : BitVec n) : Bool :=
  n == 32 && (w.toNat &&& 0xFE007FFF) == 0x12000073

/-- Q7: the announce's label — the sfence.vma MARKER (`LFence false false false false`, a
graph event) at an sfence announce, the instruction start `LInstr` otherwise. -/
def annLabel (n : Nat) (w : BitVec n) : Wlabel :=
  if sfAnnB n w then .LFence false false false false else .LInstr

/-- Q7: the announce's view update — the identity at an sfence announce (the marker's
`fencePost … false false false false`), the second reset `instrPost` otherwise. -/
def annPost (n : Nat) (w : BitVec n) (ws : Wstate) : Wstate :=
  if sfAnnB n w then ws else instrPost ws

theorem annLabelSf {n : Nat} {w : BitVec n} (h : sfAnnB n w = true) :
    annLabel n w = .LFence false false false false := by
  simp only [annLabel, h, ↓reduceIte]

theorem annLabelNot {n : Nat} {w : BitVec n} (h : sfAnnB n w = false) :
    annLabel n w = .LInstr := by
  simp only [annLabel, h, Bool.false_eq_true, ↓reduceIte]

theorem annPostSf {n : Nat} {w : BitVec n} (h : sfAnnB n w = true) (ws : Wstate) :
    annPost n w ws = ws := by
  simp only [annPost, h, ↓reduceIte]

theorem annPostNot {n : Nat} {w : BitVec n} (h : sfAnnB n w = false) (ws : Wstate) :
    annPost n w ws = instrPost ws := by
  simp only [annPost, h, Bool.false_eq_true, ↓reduceIte]

theorem annLabelOr (n : Nat) (w : BitVec n) :
    annLabel n w = .LInstr ∨ annLabel n w = .LFence false false false false := by
  cases h : sfAnnB n w
  · exact Or.inl (annLabelNot h)
  · exact Or.inr (annLabelSf h)

theorem annPostLe (n : Nat) (w : BitVec n) (ws : Wstate) :
    wsLe ws (annPost n w ws) := by
  unfold annPost
  split
  · exact wsLeRefl ws
  · exact instrPostLe ws

theorem annPostDepmove (n : Nat) (w : BitVec n) (ws : Wstate) :
    wsDepmove ws (annPost n w ws) := by
  unfold annPost
  split
  · exact wsDepmoveRefl ws
  · exact instrPostDepmove ws

theorem annPostBounded (n : Nat) (w : BitVec n) (ws : Wstate) (b : Nat) :
    wsBounded ws b → wsBounded (annPost n w ws) b := by
  intro h
  unfold annPost
  split
  · exact h
  · exact instrPostBounded ws b h

/-- Q7 (Lean-only): ALONG `WeakCert.execEff`'s path from `s` (arm for arm), no announce is an
SFENCE.VMA word — the premise of the generic "a register-only run is a position-keeping admin
run" lemmas (`afAdminRunToMemread` & co.): a run that announces an sfence emits the marker, a
graph event.  A stuck node ends the path (`True`). -/
def WeakEvLang.noSfAnn {X : Type} : SailM X → ExecSt → Prop
  | .pure _, _ => True
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => WeakEvLang.noSfAnn (k (s.regs r)) s
    | .regWrite r v, k => WeakEvLang.noSfAnn (k PUnit.unit) (s.setReg r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        match devRead s.dev req.pa n with
        | some (w, d') => WeakEvLang.noSfAnn (k (.Ok (w, none))) (s.setDev d')
        | none => True
      else
        match bmRead s.mem req.pa n with
        | some w => WeakEvLang.noSfAnn (k (.Ok (w, none))) s
        | none => True
    | .memWrite n _ req, k =>
      match req.value with
      | none => True
      | some w =>
        if mmioAcc req.pa n then
          match devWrite s.dev req.pa n w with
          | some d' => WeakEvLang.noSfAnn (k (.Ok (some true))) (s.setDev d')
          | none => True
        else
          WeakEvLang.noSfAnn (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n w))
    | .barrier _, k => WeakEvLang.noSfAnn (k ()) s
    | .cacheOp _, k => WeakEvLang.noSfAnn (k ()) s
    | .tlbi _, k => WeakEvLang.noSfAnn (k ()) s
    | .translationStart _, k => WeakEvLang.noSfAnn (k ()) s
    | .translationEnd _, k => WeakEvLang.noSfAnn (k ()) s
    | .takeException _, k => WeakEvLang.noSfAnn (k ()) s
    | .returnException _, k => WeakEvLang.noSfAnn (k ()) s
    | .cycleCount, k => WeakEvLang.noSfAnn (k ()) s
    | .getCycleCount, k => WeakEvLang.noSfAnn (k (0 : Nat)) s
    | .message _, k => WeakEvLang.noSfAnn (k ()) s
    | .instrAnnounce n w, k => sfAnnB n w = false ∧ WeakEvLang.noSfAnn (k ()) s
    | .branchAnnounce _ _, k => WeakEvLang.noSfAnn (k ()) s
    | .choose _, _ => True
    | .readRam .., _ => True
    | .writeRam .., _ => True

def erwWs (ws : Wstate) (k : ErwKind) : Wstate :=
  match k with
  | .ERWnone => ws
  | .ERWreg rd srcs => regwPost ws rd (srcsView ws srcs)
  | .ERWctrl srcs => ctrlPost ws (srcsView ws srcs)

theorem erwWsDepmove (ws : Wstate) (k : ErwKind) : wsDepmove ws (erwWs ws k) := by
  cases k with
  | ERWnone => exact wsDepmoveRefl _
  | ERWreg rd srcs => exact regwPostDepmove _ _ _
  | ERWctrl srcs => exact ctrlPostDepmove _ _

/-- THE σ-EFFECT of a register write (the explicit `ERWnone` split, deviation 9). -/
def ewgRw (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) : WGState :=
  match k with
  | .ERWnone => ewgReg σ c rs
  | _ => ewgRegws σ c rs (erwWs (σ.wgws c) k)

theorem ewgRwImg (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wgimg = σ.wgimg := by cases k <;> rfl
theorem ewgRwLog (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wglog = σ.wglog := by cases k <;> rfl
theorem ewgRwDev (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wgdev = σ.wgdev := by cases k <;> rfl
theorem ewgRwPow (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wgpow = σ.wgpow := by cases k <;> rfl
theorem ewgRwGen (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wggen = σ.wggen := by cases k <;> rfl
theorem ewgRwIb (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wgib = σ.wgib := by cases k <;> rfl
theorem ewgRwWs (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wgws c = erwWs (σ.wgws c) k := by
  cases k with
  | ERWnone => rfl
  | ERWreg rd srcs => exact gwsInsertEq _ _ _
  | ERWctrl srcs => exact gwsInsertEq _ _ _
theorem ewgRwWsNe (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) (c' : CPU) :
    c' ≠ c → (ewgRw σ c rs k).wgws c' = σ.wgws c' := by
  intro hne
  cases k with
  | ERWnone => rfl
  | ERWreg rd srcs => exact gwsInsertNe _ _ _ _ hne
  | ERWctrl srcs => exact gwsInsertNe _ _ _ _ hne
theorem ewgRwRegs (σ : WGState) (c : CPU) (rs : RegFile) (k : ErwKind) :
    (ewgRw σ c rs k).wgregs = updCpu σ.wgregs c rs := by cases k <;> rfl

/-! ### Non-vacuity, by `decide +kernel` on real encodings -/

-- [lw a5,0(a5)]: the write of x15 IS the destination, inheriting the load result and rs1
theorem erwOfLwRd :
    erwOf (depsOfBits (dbits 0x0007a783)) [15] .x15 = .ERWreg 15 [.DLdRes, .DReg 15] := by
  decide +kernel

theorem erwOfLdRd :
    erwOf (depsOfBits (dbits 0x0007b703)) [15] .x14 = .ERWreg 14 [.DLdRes, .DReg 15] := by
  decide +kernel

-- ... and a write of any OTHER GPR in the same instruction is silent
theorem erwOfLwOther : erwOf (depsOfBits (dbits 0x0007a783)) [15] .x14 = .ERWnone := by
  decide +kernel

-- a CSR write is silent, whatever the instruction (D-4)
theorem erwOfCsr : erwOf (depsOfBits (dbits 0x0007a783)) [15] .mstatus = .ERWnone := by
  decide +kernel

-- DEC-5: [csrw satp,a5]
theorem erwOfCsrwSatp :
    erwOf (depsOfBits (dbits 0x18079073)) [15] .satp = .ERWreg wsatp [.DReg 15] := by
  decide +kernel

-- [csrr a4,satp]
theorem erwOfCsrrSatp :
    erwOf (depsOfBits (dbits 0x18002773)) [wsatp] .x14 = .ERWreg 14 [.DReg wsatp] := by
  decide +kernel

theorem erwOfSatpOtherInstr : erwOf (depsOfBits (dbits 0x0007a783)) [15] .satp = .ERWnone := by
  decide +kernel

theorem erwOfCsrwSatpGpr : erwOf (depsOfBits (dbits 0x18079073)) [15] .x15 = .ERWnone := by
  decide +kernel

-- DEC-6: [csrw sstatus,a5] writes the model's mstatus node
theorem erwOfCsrwSstatus :
    erwOf (depsOfBits (dbits 0x10079073)) [15] .mstatus = .ERWreg (wcsr MSTATUS) [.DReg 15] := by
  decide +kernel

theorem erwOfCsrwSepc :
    erwOf (depsOfBits (dbits 0x14179073)) [15] .sepc = .ERWreg (wcsr SEPC) [.DReg 15] := by
  decide +kernel

theorem erwOfCsrwMepc :
    erwOf (depsOfBits (dbits 0x34179073)) [15] .mepc = .ERWreg (wcsr MEPC) [.DReg 15] := by
  decide +kernel

-- [csrw sscratch,a0] (uservec's first instruction)
theorem erwOfCsrwSscratch :
    erwOf (depsOfBits (dbits 0x14051073)) [10] .sscratch = .ERWreg (wcsr SSCRATCH) [.DReg 10] := by
  decide +kernel

theorem erwOfCsrwStvec :
    erwOf (depsOfBits (dbits 0x10579073)) [15] .stvec = .ERWreg (wcsr STVEC) [.DReg 15] := by
  decide +kernel

theorem erwOfCsrwStimecmp :
    erwOf (depsOfBits (dbits 0x14d79073)) [15] .stimecmp = .ERWreg (wcsr STIMECMP) [.DReg 15] := by
  decide +kernel

theorem erwOfCsrwPmpaddr0 :
    erwOf (depsOfBits (dbits 0x3b079073)) [15] .pmpaddr_n = .ERWreg (wcsr PMPADDR0) [.DReg 15] := by
  decide +kernel

theorem erwOfCsrwPmpcfg0 :
    erwOf (depsOfBits (dbits 0x3a079073)) [15] .pmpcfg_n = .ERWreg (wcsr PMPCFG0) [.DReg 15] := by
  decide +kernel

-- [csrw mcounteren,a5] (a 32-bit model register)
theorem erwOfCsrwMcounteren :
    erwOf (depsOfBits (dbits 0x30679073)) [15] .mcounteren =
      .ERWreg (wcsr MCOUNTEREN) [.DReg 15] := by
  decide +kernel

-- a PURE read transfers the CSR's provenance into the GPR
theorem erwOfCsrrSepc :
    erwOf (depsOfBits (dbits 0x14102773)) [wcsr SEPC] .x14 = .ERWreg 14 [.DReg (wcsr SEPC)] := by
  decide +kernel

theorem erwOfCsrrSepcCsrnode :
    erwOf (depsOfBits (dbits 0x14102773)) [wcsr SEPC] .sepc = .ERWnone := by
  decide +kernel

-- THE TWO-DESTINATION FORM (DEC-6): [csrrci a5,sstatus,2]
theorem erwOfCsrrciSstatusCsr :
    erwOf (depsOfBits (dbits 0x100177f3)) [wcsr MSTATUS] .mstatus =
      .ERWreg (wcsr MSTATUS) [.DReg (wcsr MSTATUS)] := by
  decide +kernel

theorem erwOfCsrrciSstatusGpr :
    erwOf (depsOfBits (dbits 0x100177f3)) [wcsr MSTATUS] .x15 = .ERWreg 15 [.DReg (wcsr MSTATUS)] := by
  decide +kernel

theorem erwOfCsrrciSstatusOther :
    erwOf (depsOfBits (dbits 0x100177f3)) [wcsr MSTATUS] .x14 = .ERWnone := by
  decide +kernel

-- [sret] / [mret]: the CONTROL node carries the resumption-PC CSR's provenance
theorem erwOfSretNextpc :
    erwOf (depsOfBits (dbits 0x10200073)) [wcsr SEPC] .nextPC = .ERWctrl [.DReg (wcsr SEPC)] := by
  decide +kernel

theorem erwOfMretNextpc :
    erwOf (depsOfBits (dbits 0x30200073)) [wcsr MEPC] .nextPC = .ERWctrl [.DReg (wcsr MEPC)] := by
  decide +kernel

theorem erwOfSretSepc : erwOf (depsOfBits (dbits 0x10200073)) [wcsr SEPC] .sepc = .ERWnone := by
  decide +kernel

-- D-4 survives outside the table: [csrw fcsr,a5]
theorem erwOfCsrwFcsr : erwOf (depsOfBits (dbits 0x00379073)) [15] .fcsr = .ERWnone := by
  decide +kernel

-- [beq a5,zero,.]: nextPC carries the CONTROL view (D-9)
theorem erwOfBeqNextpc :
    erwOf (depsOfBits (dbits 0x00078063)) [15] .nextPC = .ERWctrl [.DReg 15] := by
  decide +kernel

-- an ALU instruction's nextPC write carries NO control source
theorem erwOfAddiNextpc : erwOf (depsOfBits (dbits 0x00178793)) [15] .nextPC = .ERWctrl [] := by
  decide +kernel

-- [addi a5,a5,1]: the destination inherits its ALU source
theorem erwOfAddiRd : erwOf (depsOfBits (dbits 0x00178793)) [15] .x15 = .ERWreg 15 [.DReg 15] := by
  decide +kernel

/-! ### DEC-7's own witnesses -/

-- THE HONEST STRICT SUPERSET
theorem erwOfLdRdDynamic :
    erwOf (depsOfBits (dbits 0x0007b703)) [15, wsatp, wcsr MSTATUS] .x14 =
      .ERWreg 14 [.DLdRes, .DReg 15, .DReg wsatp, .DReg (wcsr MSTATUS)] := by
  decide +kernel

theorem erwOfLdRdSuperset :
    ∀ s : Dsrc, s ∈ [Dsrc.DLdRes, .DReg 15] →
      match erwOf (depsOfBits (dbits 0x0007b703)) [15, wsatp, wcsr MSTATUS] .x14 with
      | .ERWreg _ srcs => s ∈ srcs
      | _ => False := by
  intro s hs
  rw [erwOfLdRdDynamic]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  rcases hs with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

-- A REPEATED READ COSTS NOTHING
theorem erwOfAddiRdDedup :
    erwOf (depsOfBits (dbits 0x00178793)) [15, 15, 15] .x15 = .ERWreg 15 [.DReg 15] := by
  decide +kernel

-- THE CONTROL GATE (DEC-7)
theorem erwOfAddiNextpcGated :
    erwOf (depsOfBits (dbits 0x00178793)) [15, wsatp, wcsr MSTATUS] .nextPC = .ERWctrl [] := by
  decide +kernel

theorem erwOfBeqNextpcDynamic :
    erwOf (depsOfBits (dbits 0x00078063)) [15, wcsr MSTATUS] .nextPC =
      .ERWctrl [.DReg 15, .DReg (wcsr MSTATUS)] := by
  decide +kernel

/-- THE OPERAND LISTS a memory node carries, from the announced bits (D-8: a plain load
carries no address sources). -/
def edeps (σ : WGState) (c : CPU) : OpRoles := depsOfIb (σ.wgib c).ibBits

/-- DEC-7: the registers this hart's current instruction has read so far. -/
def erds (σ : WGState) (c : CPU) : List Nat := (σ.wgib c).ibRds

/-! ## 3. The barrier table -/

def ebarNow (b : barrier_kind) : Option (Bool × Bool × Bool × Bool) :=
  match b with
  | .Barrier_RISCV_rw_rw => some (true, true, true, true)
  | .Barrier_RISCV_r_rw => some (true, false, true, true)
  | .Barrier_RISCV_r_r => some (true, false, true, false)
  | .Barrier_RISCV_rw_w => some (true, true, false, true)
  | .Barrier_RISCV_w_w => some (false, true, false, true)
  | .Barrier_RISCV_w_rw => some (false, true, true, true)
  | .Barrier_RISCV_rw_r => some (true, true, true, false)
  | .Barrier_RISCV_r_w => some (true, false, false, true)
  | .Barrier_RISCV_w_r => some (false, true, true, false)
  | .Barrier_RISCV_tso => some (true, false, true, false)
  | .Barrier_RISCV_i => none

def ebarPark (b : barrier_kind) : Option (Bool × Bool × Bool × Bool) :=
  match b with
  | .Barrier_RISCV_tso => some (true, true, false, true)
  | _ => none

def efenceApply (ws : Wstate) (o : Option (Bool × Bool × Bool × Bool)) : Wstate :=
  match o with
  | some (pr, pw, sr, sw) => Weak.fencePost ws pr pw sr sw
  | none => ws

theorem efenceBarrierPost (ws : Wstate) (b : barrier_kind) :
    efenceApply (efenceApply ws (ebarNow b)) (ebarPark b) = barrierPost ws b := by
  cases b <;> rfl

theorem efenceApplyLe (ws : Wstate) (o : Option (Bool × Bool × Bool × Bool)) :
    wsLe ws (efenceApply ws o) := by
  match o with
  | some (pr, pw, sr, sw) => exact fencePostLe _ _ _ _ _
  | none => exact wsLeRefl _

/-! ## 4. The hart's per-event step -/

/-- The monad-node dispatch (one arm per `Outcome` constructor, deviation 4).  RAM READ is
LABEL-FREE: the timestamps/values it takes are chosen here and constrained against the SHARED
log and this hart's own view (O2: a three-way split on `classify`, deviation 5).  RAM WRITE
COMPUTES its class (D2) and splits plain / conditional / retry (D3). -/
def emonadStep (gen : Nat) (σ : WGState) (c : CPU) : SailM Unit → EExpr → WGState → Prop
  | .pure _, e', σ' =>
      -- THE RESTART: the boundary fetches a fresh instruction; it clears the announced bits
      -- and is a reset point (`instrPost`, W2b condition 1).
      ∃ tick : Bool, e' = .Sail gen c (riscvStep tick) none ∧
        σ' = ewgIbws σ c ibNone (instrPost (σ.wgws c))
  | .impure (.error _) _, _, _ => False
  | .impure (.ok o) k, e', σ' =>
    match o, k with
    -- DEC-7: THE READ SET ACCUMULATES HERE (the σ-write is `wgib` alone)
    | .regRead r, k =>
        e' = ECycle gen c (k (σ.wgregs c r)) none ∧ σ' = ewgIb σ c (ibRd (σ.wgib c) r)
    -- D3-2: a register write MAY carry a dependency
    | .regWrite r v, k =>
        e' = ECycle gen c (k PUnit.unit) none ∧
        σ' = ewgRw σ c ((σ.wgregs c).set r v) (erwOf (edeps σ c) (erds σ c) r)
    | .memRead n _va req, k =>
        if devAddr req.pa then
          -- MMIO: the SHARED fabric answers, partially (D1)
          ∃ (w : BitVec (8 * n)) (d' : DevStates),
            devRead σ.wgdev req.pa n = some (w, d') ∧
            e' = ECycle gen c (k (.Ok (w, none))) none ∧ σ' = ewgDev σ d'
        else
          -- O2: THE I-CACHE READ (view-silent; at the hart's instruction view, Stage B)
          ((classify req.access_kind).akIfetch = true ∧
            ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
              tvs.length = n ∧
              (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
              ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) (paZ req.pa) tvs ∧
              e' = ECycle gen c (k (.Ok (w, none))) none ∧ σ' = σ)
          ∨
          ((classify req.access_kind).akIfetch = false ∧
            (-- THE PLAIN RAM READ
             ((classify req.access_kind).akLatest = false ∧
               ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
                 tvs.length = n ∧
                 (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
                 readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) (classify req.access_kind).akSync false
                   (paZ req.pa) tvs ∧
                 e' = ECycle gen c (k (.Ok (w, none))) none ∧
                 σ' = ewgWs σ c (loadPostRun (σ.wgws c) (classify req.access_kind).akSync
                        (paZ req.pa) (tvs.map Prod.fst)))
             ∨
             -- THE EXCLUSIVE READ (RMW split): the plain read plus the reservation
             ((classify req.access_kind).akLatest = true ∧
               ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
                 tvs.length = n ∧
                 (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
                 readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) (classify req.access_kind).akSync false
                   (paZ req.pa) tvs ∧
                 e' = ECycle gen c (k (.Ok (w, none))) none ∧
                 σ' = ewgWs σ c (exloadPostRunD (σ.wgws c) (classify req.access_kind).akSync
                        (srcsView (σ.wgws c) (depsAsrc (edeps σ c)))
                        (paZ req.pa) (tvs.map Prod.fst)))))
    | .memWrite n va req, k =>
        if devAddr req.pa then
          match req.value with
          | some v =>
              ∃ d' : DevStates, devWrite σ.wgdev req.pa n v = some d' ∧
                e' = ECycle gen c (k (.Ok (some true))) none ∧ σ' = ewgDev σ d'
          | none => False
        else
          match req.value with
          | some v =>
              n ≠ 0 ∧
              (-- THE PLAIN RAM WRITE, guarded by exclusivity
               ((classify req.access_kind).akLatest = false ∧
                 e' = ECycle gen c (k (.Ok (some true))) none ∧
                 σ' = ewgStore σ c
                        (storePostRunD (σ.wgws c) (classify req.access_kind).akSync
                           (srcsView (σ.wgws c) (depsAsrc (edeps σ c)))
                           (srcsView (σ.wgws c) (depsVsrc (edeps σ c)))
                           (paZ req.pa) n (σ.wglog.length + 1))
                        (σ.wglog ++ [⟨paZ req.pa, WeakInterpProj.wbytes n v, some c.val,
                                      wmClassOf (classify req.access_kind) (σ.wgws c)⟩]))
               ∨
               ((classify req.access_kind).akLatest = true ∧
                 (-- THE CONDITIONAL WRITE: the window must still be clean
                  (exwinOk σ.wglog c.val (σ.wgws c) (paZ req.pa) n (σ.wglog.length + 1) ∧
                    e' = ECycle gen c (k (.Ok (some true))) none ∧
                    σ' = ewgStore σ c
                           (storePostRunD (σ.wgws c) (classify req.access_kind).akSync
                              (srcsView (σ.wgws c) (depsAsrc (edeps σ c)))
                              (srcsView (σ.wgws c) (depsVsrc (edeps σ c)))
                              (paZ req.pa) n (σ.wglog.length + 1))
                           (σ.wglog ++ [⟨paZ req.pa, WeakInterpProj.wbytes n v, some c.val,
                                         wmClassOf (classify req.access_kind) (σ.wgws c)⟩]))
                  ∨
                  -- THE RETRY SELF-LOOP (unguarded, silent, σ-preserving)
                  (e' = ECycle gen c (.impure (.ok (.memWrite n va req)) k) none ∧ σ' = σ))))
          | none => False
    -- FENCE: fire the first half now, park the second; Stage B moves the instruction view
    | .barrier b, k =>
        e' = ECycle gen c (k ()) (ebarPark b) ∧
        σ' = ewgBar σ c (efenceApply (σ.wgws c) (ebarNow b)) (itvPost (σ.wgws c) (σ.wgitv c) b)
    -- D3: THE ANNOUNCE NODE banks the instruction bits and resets the load-result bank
    -- Q7: at an sfence.vma announce the reset is replaced by the marker's identity (`annPost`)
    | .instrAnnounce n w, k =>
        e' = ECycle gen c (k ()) none ∧ σ' = ewgIbws σ c (ibAnn (ibOfBvn w)) (annPost n w (σ.wgws c))
    -- the branch announcement stays silent (the control view rides the nextPC write)
    | .branchAnnounce _ _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .cacheOp _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .tlbi _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .takeException _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .returnException _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .translationStart _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .translationEnd _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .cycleCount, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .message _, k => e' = ECycle gen c (k ()) none ∧ σ' = σ
    | .getCycleCount, k => e' = ECycle gen c (k (0 : Nat)) none ∧ σ' = σ
    | .choose _, k => ∃ ch, e' = ECycle gen c (k ch) none ∧ σ' = σ
    -- the legacy direct-RAM events: STUCK
    | .readRam .., _ => False
    | .writeRam .., _ => False

/-- THE CYCLE EVENT.  The parked fence gates everything (D5). -/
def ecycleStep (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) : Prop :=
  match fn with
  | some (pr, pw, sr, sw) =>
      e' = ECycle gen c m none ∧ σ' = ewgWs σ c (Weak.fencePost (σ.wgws c) pr pw sr sw)
  | none => emonadStep gen σ c m e' σ'

/-! ## 5. The device threads -/

/-- The disk's view of the fabric (Lean-only, deviation 2). -/
def dvirtio (ds : DevStates) : VirtioState := ds.st .virtio

def setDvirtio (ds : DevStates) (v : VirtioState) : DevStates := ds.set .virtio v

/-- THE CLASS THE DEVICE'S STORES CARRY: a plain explicit store. -/
def ddevAk : AkInfo := ⟨false, false, false⟩

def ddevClass (ws : Wstate) : WmClass := wmClassOf ddevAk ws

theorem ddevClassEq (ws : Wstate) : ddevClass ws = if ws.wRelp then .WCrel else .WCplain := by
  cases h : ws.wRelp <;> simp [ddevClass, wmClassOf, ddevAk, h]

theorem ddevAkPlain : ddevAk = classify (.AK_explicit ⟨.AV_plain, .AS_normal⟩) := rfl

/-- The fabric write-back of the disk's own state is the identity (Lean-only). -/
theorem setDvirtioSelf (ds : DevStates) : setDvirtio ds (dvirtio ds) = ds := by
  cases ds with
  | mk st =>
    simp only [setDvirtio, dvirtio, DevStates.set, DevStates.mk.injEq]
    funext d'
    split
    · next h => subst h; rfl
    · rfl

/-- THE DISK'S STEP (W-DISK): one arm per node of the residual program -- START, `DRead`,
`DFence`, the three outcomes of a `DWriteDev` (store / own-guard skip / abort), the two of a
`DPop` (refused / pop), the stall self-loop and the idle end (`Weak/VirtioProg.lean` header);
the PLIC latch is the PLIC program's (deviation 2).  Every `DWriteDev` / `DPop` arm reads the
CURRENT fabric `dvirtio σ.wgdev`; a store sets BOTH the log and the fabric. -/
def ediskStep (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState) (e' : EExpr)
    (σ' : WGState) : Prop :=
  -- START: read the fabric's virtio state and elaborate the program (FABRIC-TOUCHING)
  (dp = none ∧ e' = .EDisk gen (some (virtioProg (dvirtio σ.wgdev))) dws ∧ σ' = σ)
  ∨
  -- DRead: EXACTLY the hart's plain RAM-read arm, at `dws`
  (∃ (pa : PAddr) (n : Nat) (aq : Bool) (k : List (BitVec 8) → DM Dres)
      (tvs : List (Nat × BitVec 8)),
     dp = some (DRead pa n aq k) ∧ tvs.length = n ∧
     readOk (imgZ σ.wgimg) σ.wglog dws aq false (paZ pa) tvs ∧
     e' = .EDisk gen (some (k (tvs.map Prod.snd))) (loadPostRun dws aq (paZ pa) (tvs.map Prod.fst)) ∧
     σ' = σ)
  ∨
  -- DFence: the device-side write barrier, `fence rw,rw`
  (∃ k : DM Dres,
     dp = some (DFence k) ∧ e' = .EDisk gen (some k) (Weak.fencePost dws true true true true) ∧
     σ' = σ)
  ∨
  -- DWriteDev, THE STORE: the folded part passes, the own guard answers, the footprint is DRAM;
  -- the hart's RAM-write arm at `dws` (tid `some nDisk`, class `ddevClass`) AND the fabric move
  (∃ (pre : VirtioState → VirtioState × Bool) (g : VirtioState → Option VirtioState)
      (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM Dres)
      (s s' : VirtioState),
     dp = some (DWriteDev pre g pa bs k) ∧ pre (dvirtio σ.wgdev) = (s, true) ∧ g s = some s' ∧
     ramBytes (pa s) (bs s).length ∧ bs s ≠ [] ∧
     e' = .EDisk gen (some (k s)) (storePostRun dws false (paZ (pa s)) (bs s).length (σ.wglog.length + 1)) ∧
     σ' = ewgDev (ewgLog σ (σ.wglog ++ [⟨paZ (pa s), bs s, some nDisk, ddevClass dws⟩]))
       (setDvirtio σ.wgdev s'))
  ∨
  -- DWriteDev, THE OWN-GUARD SKIP: the folded moves stay, nothing is written, the program goes on
  (∃ (pre : VirtioState → VirtioState × Bool) (g : VirtioState → Option VirtioState)
      (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM Dres)
      (s : VirtioState),
     dp = some (DWriteDev pre g pa bs k) ∧ pre (dvirtio σ.wgdev) = (s, true) ∧
     (g s = none ∨ ¬ ramBytes (pa s) (bs s).length) ∧
     e' = .EDisk gen (some (k s)) dws ∧ σ' = ewgDev σ (setDvirtio σ.wgdev s))
  ∨
  -- DWriteDev, THE ABORT: a folded guard fails, the burst ends with the moves made before it
  (∃ (pre : VirtioState → VirtioState × Bool) (g : VirtioState → Option VirtioState)
      (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM Dres)
      (s : VirtioState),
     dp = some (DWriteDev pre g pa bs k) ∧ pre (dvirtio σ.wgdev) = (s, false) ∧
     e' = .EDisk gen none dws ∧ σ' = ewgDev σ (setDvirtio σ.wgdev s))
  ∨
  -- DPop, REFUSED: the head is already in flight; back to the start (FABRIC-TOUCHING)
  (∃ (h : BitVec 16) (k : VirtioState → DM Dres),
     dp = some (DPop h k) ∧ (Virtio.phase (dvirtio σ.wgdev) h).isSome = true ∧
     e' = .EDisk gen none dws ∧ σ' = σ)
  ∨
  -- DPop: the head goes in flight, `seen + 1` (FABRIC-MOVING)
  (∃ (h : BitVec 16) (k : VirtioState → DM Dres),
     dp = some (DPop h k) ∧ (Virtio.phase (dvirtio σ.wgdev) h).isSome = false ∧
     e' = .EDisk gen (some (k (VirtioProg.popState (dvirtio σ.wgdev) h))) dws ∧
     σ' = ewgDev σ (setDvirtio σ.wgdev (VirtioProg.popState (dvirtio σ.wgdev) h)))
  ∨
  -- the stalled request: a silent self-loop
  (dp = some (DRet DStall) ∧ e' = .EDisk gen (some (DRet DStall)) dws ∧ σ' = σ)
  ∨
  -- nothing (more) to do
  (dp = some (DRet DIdle) ∧ e' = .EDisk gen none dws ∧ σ' = σ)

/-- THE RESIDUAL PROGRAM'S WELL-FORMEDNESS. -/
def edpWf (dp : Option (DM Dres)) : Prop :=
  match dp with
  | some p => DmWf p
  | none => True

theorem edpWfNone : edpWf none := trivial

/-! ## 6. Boot / crash reset -/

def ebootShape (σ σ' : WGState) : Prop :=
  σ'.wggen = σ.wggen ∧ σ'.wgdev = σ.wgdev.reset ∧ wbootFacts σ'

/-! ## 7. `eprimStep` -/

def ethreadLive (σ : WGState) (gen : Nat) : Prop := σ.wgpow = true ∧ σ.wggen = gen

theorem ethreadLiveWthreadLive (σ : WGState) (gen : Nat) : ethreadLive σ gen ↔ wthreadLive σ gen :=
  Iff.rfl

/-- The primitive step (deviation 3): one event of a hart (the boundary IS the `pure ()` node),
one step of a device program, one node of the disk agent, the power thread.  Every arm of a dead
generation is a corpse self-loop. -/
def eprimStep : EExpr → WGState → List Empty → EExpr → WGState → List EExpr → Prop
  | .Sail gen cpu m fn, σ, κ, e', σ', efs =>
    κ = [] ∧ efs = [] ∧
    ((ethreadLive σ gen ∧ ecycleStep gen σ cpu m fn e' σ') ∨
     (¬ ethreadLive σ gen ∧ e' = .Sail gen cpu m fn ∧ σ' = σ))
  | .EDev gen d tid m, σ, κ, e', σ', efs =>
    κ = [] ∧
    ((ethreadLive σ gen ∧ ∃ (m' : DevProg d) (efs0 : List WExpr),
        e' = .EDev gen d tid m' ∧ wdevStep gen d tid m σ m' σ' efs0 ∧ efs = efs0.map ofWExpr) ∨
     (¬ ethreadLive σ gen ∧ efs = [] ∧ e' = .EDev gen d tid m ∧ σ' = σ))
  | .EDisk gen dp dws, σ, κ, e', σ', efs =>
    κ = [] ∧ efs = [] ∧
    ((ethreadLive σ gen ∧ ediskStep gen dp dws σ e' σ') ∨
     (¬ ethreadLive σ gen ∧ e' = .EDisk gen dp dws ∧ σ' = σ))
  | .EPower, σ, κ, e', σ', efs =>
    e' = .EPower ∧ κ = [] ∧
    ((σ.wgpow = true ∧ efs = [] ∧ σ' = { σ with wggen := σ.wggen + 1, wgpow := false }) ∨
     (σ.wgpow = false ∧ efs = epowerFork σ.wggen ∧ ebootShape σ σ'))

open Iris.ProgramLogic in
/-- Rocq `weak_ev_lang`. -/
instance weakEvLang : Language EExpr WGState Empty Empty where
  primStep c κ c' := eprimStep c.1 c.2 κ c'.1 c'.2.1 c'.2.2
  toVal _ := none
  ofVal v := nomatch v
  coe_of_toVal_eq_some h := nomatch h
  toVal_coe v := nomatch v
  val_stuck _ := rfl

open Iris.ProgramLogic in
/-- Rocq `weak_ev_lang_mixin` (its one non-vacuous field, `val_stuck`). -/
theorem weakEvLangMixin (e : EExpr) (σ : WGState) (κ : List Empty) (e' : EExpr) (σ' : WGState)
    (efs : List EExpr) : eprimStep e σ κ e' σ' efs → ToVal.toVal (Val := Empty) e = none :=
  fun _ => rfl

/-! ## 8. Per-arm inversion -/

theorem eprimStepLoopInv (gen : Nat) (cpu : CPU) (σ : WGState) (κ : List Empty) (e' : EExpr)
    (σ' : WGState) (efs : List EExpr) :
    eprimStep (ELoop gen cpu) σ κ e' σ' efs →
    κ = [] ∧ efs = [] ∧
    ((ethreadLive σ gen ∧ σ' = ewgIbws σ cpu ibNone (instrPost (σ.wgws cpu)) ∧
      ∃ tick : Bool, e' = ECycle gen cpu (riscvStep tick) none) ∨
     (¬ ethreadLive σ gen ∧ e' = ELoop gen cpu ∧ σ' = σ)) := by
  intro h
  obtain ⟨hk, hf, ⟨hl, tick, he, hs⟩ | ⟨hd, he, hs⟩⟩ := h
  · exact ⟨hk, hf, Or.inl ⟨hl, hs, tick, he⟩⟩
  · exact ⟨hk, hf, Or.inr ⟨hd, he, hs⟩⟩

theorem eprimStepCycleInv (gen : Nat) (cpu : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (σ : WGState) (κ : List Empty) (e' : EExpr)
    (σ' : WGState) (efs : List EExpr) :
    eprimStep (ECycle gen cpu m fn) σ κ e' σ' efs →
    κ = [] ∧ efs = [] ∧
    ((ethreadLive σ gen ∧ ecycleStep gen σ cpu m fn e' σ') ∨
     (¬ ethreadLive σ gen ∧ e' = ECycle gen cpu m fn ∧ σ' = σ)) := id

theorem eprimStepDevInv (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (σ : WGState)
    (κ : List Empty) (e' : EExpr) (σ' : WGState) (efs : List EExpr) :
    eprimStep (.EDev gen d tid m) σ κ e' σ' efs →
    κ = [] ∧
    ((ethreadLive σ gen ∧ ∃ (m' : DevProg d) (efs0 : List WExpr),
        e' = .EDev gen d tid m' ∧ wdevStep gen d tid m σ m' σ' efs0 ∧ efs = efs0.map ofWExpr) ∨
     (¬ ethreadLive σ gen ∧ efs = [] ∧ e' = .EDev gen d tid m ∧ σ' = σ)) := id

theorem eprimStepDiskInv (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState)
    (κ : List Empty) (e' : EExpr) (σ' : WGState) (efs : List EExpr) :
    eprimStep (.EDisk gen dp dws) σ κ e' σ' efs →
    κ = [] ∧ efs = [] ∧
    ((ethreadLive σ gen ∧ ediskStep gen dp dws σ e' σ') ∨
     (¬ ethreadLive σ gen ∧ e' = .EDisk gen dp dws ∧ σ' = σ)) := id

theorem eprimStepPowerInv (σ : WGState) (κ : List Empty) (e' : EExpr) (σ' : WGState)
    (efs : List EExpr) :
    eprimStep .EPower σ κ e' σ' efs →
    e' = .EPower ∧ κ = [] ∧
    ((σ.wgpow = true ∧ efs = [] ∧ σ' = { σ with wggen := σ.wggen + 1, wgpow := false }) ∨
     (σ.wgpow = false ∧ efs = epowerFork σ.wggen ∧ ebootShape σ σ')) := id

/-! ## 9. Cross-arm sanity lemmas -/

/-- What a hart's cycle step leaves alone (Lean-only): the image and the era, the log only
grows, the other harts' views are untouched, and the stepping hart's only rise. -/
def ecycFrameSt (σ : WGState) (c : CPU) (σ' : WGState) : Prop :=
  σ'.wgimg = σ.wgimg ∧ σ'.wgpow = σ.wgpow ∧ σ'.wggen = σ.wggen ∧
  (∃ ms, σ'.wglog = σ.wglog ++ ms) ∧ (∀ c', c' ≠ c → σ'.wgws c' = σ.wgws c') ∧
  wsLe (σ.wgws c) (σ'.wgws c)

theorem ecycFrameSame (σ σ' : WGState) (c : CPU) (himg : σ'.wgimg = σ.wgimg)
    (hpow : σ'.wgpow = σ.wgpow) (hgen : σ'.wggen = σ.wggen) (hlog : σ'.wglog = σ.wglog)
    (hws : σ'.wgws = σ.wgws) : ecycFrameSt σ c σ' :=
  ⟨himg, hpow, hgen, ⟨[], by rw [hlog, List.append_nil]⟩, fun _ _ => by rw [hws],
    by rw [hws]; exact wsLeRefl _⟩

theorem ecycFrameUpd (σ σ' : WGState) (c : CPU) (ws : Wstate) (ms : List Wmsg)
    (himg : σ'.wgimg = σ.wgimg) (hpow : σ'.wgpow = σ.wgpow) (hgen : σ'.wggen = σ.wggen)
    (hlog : σ'.wglog = σ.wglog ++ ms) (hws : σ'.wgws = updCpu σ.wgws c ws)
    (hle : wsLe (σ.wgws c) ws) : ecycFrameSt σ c σ' :=
  ⟨himg, hpow, hgen, ⟨ms, hlog⟩, fun c' h => by rw [hws]; exact gwsInsertNe _ _ _ _ h,
    by rw [hws, gwsInsertEq]; exact hle⟩

theorem ecycleStepFrame (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' →
    (e' = ELoop gen c ∨ ∃ m' fn', e' = ECycle gen c m' fn') ∧ ecycFrameSt σ c σ' := by
  intro h
  have hsame : ecycFrameSt σ c σ := ecycFrameSame σ σ c rfl rfl rfl rfl rfl
  match fn, h with
  | some (pr, pw, sr, sw), h =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Or.inr ⟨_, _, rfl⟩,
      ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl (fencePostLe _ _ _ _ _)⟩
  | none, h =>
    match m, h with
    | .pure _, h =>
      obtain ⟨tick, rfl, rfl⟩ := h
      exact ⟨Or.inr ⟨_, _, rfl⟩,
        ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl (instrPostLe _)⟩
    | .impure (.error _) _, h => exact h.elim
    | .impure (.ok o) k, h =>
      cases o with
      | regRead r =>
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Or.inr ⟨_, _, rfl⟩, ecycFrameSame σ _ c rfl rfl rfl rfl rfl⟩
      | regWrite r v =>
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨Or.inr ⟨_, _, rfl⟩, ?_⟩
        generalize erwOf (edeps σ c) (erds σ c) r = kk
        cases kk with
        | ERWnone => exact ecycFrameSame σ _ c rfl rfl rfl rfl rfl
        | ERWreg rd srcs =>
          exact ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl
            (wsDepmoveLe _ _ (erwWsDepmove _ _))
        | ERWctrl srcs =>
          exact ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl
            (wsDepmoveLe _ _ (erwWsDepmove _ _))
      | memRead n va req =>
        simp only [emonadStep, ecycleStep] at h
        split at h
        · obtain ⟨w, d', -, rfl, rfl⟩ := h
          exact ⟨Or.inr ⟨_, _, rfl⟩, ecycFrameSame σ _ c rfl rfl rfl rfl rfl⟩
        · rcases h with ⟨-, w, tvs, -, -, -, rfl, rfl⟩ |
            ⟨-, ⟨-, w, tvs, -, -, -, rfl, rfl⟩ | ⟨-, w, tvs, -, -, -, rfl, rfl⟩⟩
          · exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
          · exact ⟨Or.inr ⟨_, _, rfl⟩,
              ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl
                (loadPostRunLe _ _ _ _)⟩
          · exact ⟨Or.inr ⟨_, _, rfl⟩,
              ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl
                (exloadPostRunDLe _ _ _ _ _)⟩
      | memWrite n va req =>
        simp only [emonadStep, ecycleStep] at h
        split at h
        · split at h
          · obtain ⟨d', -, rfl, rfl⟩ := h
            exact ⟨Or.inr ⟨_, _, rfl⟩, ecycFrameSame σ _ c rfl rfl rfl rfl rfl⟩
          · exact h.elim
        · split at h
          · rcases h with ⟨-, ⟨-, rfl, rfl⟩ | ⟨-, ⟨-, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩⟩
            · exact ⟨Or.inr ⟨_, _, rfl⟩,
                ecycFrameUpd σ _ c _ _ rfl rfl rfl rfl rfl (storePostRunDLe _ _ _ _ _ _ _)⟩
            · exact ⟨Or.inr ⟨_, _, rfl⟩,
                ecycFrameUpd σ _ c _ _ rfl rfl rfl rfl rfl (storePostRunDLe _ _ _ _ _ _ _)⟩
            · exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
          · exact h.elim
      | barrier b =>
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Or.inr ⟨_, _, rfl⟩,
          ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl (efenceApplyLe _ _)⟩
      | instrAnnounce n w =>
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Or.inr ⟨_, _, rfl⟩,
          ecycFrameUpd σ _ c _ [] rfl rfl rfl (List.append_nil _).symm rfl (annPostLe _ _ _)⟩
      | branchAnnounce _ _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | cacheOp _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | tlbi _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | takeException _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | returnException _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | translationStart _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | translationEnd _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | cycleCount => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | message _ => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | getCycleCount => obtain ⟨rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | choose p => obtain ⟨ch, rfl, rfl⟩ := h; exact ⟨Or.inr ⟨_, _, rfl⟩, hsame⟩
      | readRam _ _ _ => exact h.elim
      | writeRam _ _ _ _ => exact h.elim

theorem ecycleStepImg (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' → σ'.wgimg = σ.wgimg :=
  fun h => (ecycleStepFrame gen σ c m fn e' σ' h).2.1

theorem ecycleStepEra (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' → σ'.wgpow = σ.wgpow ∧ σ'.wggen = σ.wggen :=
  fun h => ⟨(ecycleStepFrame gen σ c m fn e' σ' h).2.2.1,
    (ecycleStepFrame gen σ c m fn e' σ' h).2.2.2.1⟩

/-- ... and its successor is always a hart expression of the SAME generation and hart. -/
theorem ecycleStepShape (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' → e' = ELoop gen c ∨ ∃ m' fn', e' = ECycle gen c m' fn' :=
  fun h => (ecycleStepFrame gen σ c m fn e' σ' h).1

theorem ecycleStepLogApp (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' → ∃ ms, σ'.wglog = σ.wglog ++ ms :=
  fun h => (ecycleStepFrame gen σ c m fn e' σ' h).2.2.2.2.1

theorem ecycleStepWsOther (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) (c' : CPU) :
    ecycleStep gen σ c m fn e' σ' → c' ≠ c → σ'.wgws c' = σ.wgws c' :=
  fun h hne => (ecycleStepFrame gen σ c m fn e' σ' h).2.2.2.2.2.1 c' hne

theorem ecycleStepWsLe (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' → wsLe (σ.wgws c) (σ'.wgws c) :=
  fun h => (ecycleStepFrame gen σ c m fn e' σ' h).2.2.2.2.2.2

/-- STAGE B (Lean-only): a hart's instruction views only rise, and only its own moves. -/
theorem ecycleStepItvLe (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) (c' : CPU) :
    ecycleStep gen σ c m fn e' σ' → σ.wgitv c' ≤ σ'.wgitv c' := by
  intro h
  match fn, h with
  | some (pr, pw, sr, sw), h =>
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  | none, h =>
    match m, h with
    | .pure _, h =>
      obtain ⟨tick, -, rfl⟩ := h
      exact Nat.le_refl _
    | .impure (.error _) _, h => exact h.elim
    | .impure (.ok o) k, h =>
      cases o with
      | regRead r => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | regWrite r v =>
        obtain ⟨-, rfl⟩ := h
        generalize erwOf (edeps σ c) (erds σ c) r = kk
        cases kk <;> exact Nat.le_refl _
      | memRead n va req =>
        simp only [emonadStep, ecycleStep] at h
        split at h
        · obtain ⟨w, d', -, -, rfl⟩ := h
          exact Nat.le_refl _
        · rcases h with ⟨-, w, tvs, -, -, -, -, rfl⟩ |
            ⟨-, ⟨-, w, tvs, -, -, -, -, rfl⟩ | ⟨-, w, tvs, -, -, -, -, rfl⟩⟩ <;>
          exact Nat.le_refl _
      | memWrite n va req =>
        simp only [emonadStep, ecycleStep] at h
        split at h
        · split at h
          · obtain ⟨d', -, -, rfl⟩ := h
            exact Nat.le_refl _
          · exact h.elim
        · split at h
          · rcases h with ⟨-, ⟨-, -, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩⟩ <;> exact Nat.le_refl _
          · exact h.elim
      | barrier b =>
        obtain ⟨-, rfl⟩ := h
        by_cases hc : c' = c
        · subst hc
          rw [ewgBarItv]
          exact itvPostLe _ _ _
        · simp [ewgBar, updCpu, hc]
      | instrAnnounce n w => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | branchAnnounce _ _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | cacheOp _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | tlbi _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | takeException _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | returnException _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | translationStart _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | translationEnd _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | cycleCount => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | message _ => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | getCycleCount => obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
      | choose p => obtain ⟨ch, -, rfl⟩ := h; exact Nat.le_refl _
      | readRam _ _ _ => exact h.elim
      | writeRam _ _ _ _ => exact h.elim

/-- The non-disk device threads move NO hart's view (Rocq `euart_step_ws`/`eplic_step_ws`). -/
theorem edevStepWs (gen : Nat) (d : DevId) (tid : TaskId) (m m' : DevProg d) (σ σ' : WGState)
    (efs : List WExpr) : wdevStep gen d tid m σ m' σ' efs → σ'.wgws = σ.wgws :=
  fun h => (wdevStepFrame h).2.1

theorem ediskStepWs (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState)
    (e' : EExpr) (σ' : WGState) : ediskStep gen dp dws σ e' σ' → σ'.wgws = σ.wgws := by
  rintro (⟨-, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ |
    ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, rfl⟩ | ⟨_, _, _, _, _, _, -, -, -, -, rfl⟩ |
    ⟨_, _, _, _, _, _, -, -, -, rfl⟩ | ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, -, rfl⟩ |
    ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩) <;> rfl

/-! ## 10. Reducibility helpers -/

theorem eprimStepLoopDead (gen : Nat) (cpu : CPU) (σ : WGState) :
    ¬ ethreadLive σ gen → eprimStep (ELoop gen cpu) σ [] (ELoop gen cpu) σ [] :=
  fun hd => ⟨rfl, rfl, Or.inr ⟨hd, rfl, rfl⟩⟩

theorem eprimStepLoopLive (gen : Nat) (cpu : CPU) (σ : WGState) (tick : Bool) :
    ethreadLive σ gen →
    eprimStep (ELoop gen cpu) σ [] (ECycle gen cpu (riscvStep tick) none)
      (ewgIbws σ cpu ibNone (instrPost (σ.wgws cpu))) [] :=
  fun hl => ⟨rfl, rfl, Or.inl ⟨hl, tick, rfl, rfl⟩⟩

theorem eprimStepCycleDead (gen : Nat) (cpu : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (σ : WGState) :
    ¬ ethreadLive σ gen → eprimStep (ECycle gen cpu m fn) σ [] (ECycle gen cpu m fn) σ [] :=
  fun hd => ⟨rfl, rfl, Or.inr ⟨hd, rfl, rfl⟩⟩

theorem eprimStepDevDead (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (σ : WGState) :
    ¬ ethreadLive σ gen → eprimStep (.EDev gen d tid m) σ [] (.EDev gen d tid m) σ [] :=
  fun hd => ⟨rfl, Or.inr ⟨hd, rfl, rfl, rfl⟩⟩

theorem eprimStepDiskDead (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState) :
    ¬ ethreadLive σ gen → eprimStep (.EDisk gen dp dws) σ [] (.EDisk gen dp dws) σ [] :=
  fun hd => ⟨rfl, rfl, Or.inr ⟨hd, rfl, rfl⟩⟩

theorem eprimStepPowerOff (σ : WGState) :
    σ.wgpow = true →
    eprimStep .EPower σ [] .EPower { σ with wggen := σ.wggen + 1, wgpow := false } [] :=
  fun hon => ⟨rfl, rfl, Or.inl ⟨hon, rfl, rfl⟩⟩

/-- A LIVE device thread always steps (Rocq `eprim_step_uart_idle`, deviation 2). -/
theorem eprimStepDevLive (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (σ : WGState) :
    ethreadLive σ gen → ∃ e' σ' efs, eprimStep (.EDev gen d tid m) σ [] e' σ' efs := by
  intro hl
  obtain ⟨m', σ', efs0, hs⟩ := wdevStepTotal gen d tid m σ
  exact ⟨.EDev gen d tid m', σ', efs0.map ofWExpr, rfl, Or.inl ⟨hl, m', efs0, rfl, hs, rfl⟩⟩

/-- THE WIRE WRITE (Rocq `eprim_step_plic_wire`, deviation 2): a device's `setPin`. -/
theorem eprimStepDevSetPin (gen : Nat) (d : DevId) (tid : TaskId) (cpu : CPU) (mmode b : Bool)
    (k : Unit → DevProg d) (σ : WGState) :
    ethreadLive σ gen →
    eprimStep (.EDev gen d tid (.op (.setPin cpu mmode b) k)) σ [] (.EDev gen d tid (k ()))
      (if mmode then σ.setReg cpu .sig_meip (if b then 1#1 else 0#1)
       else σ.setReg cpu .sig_seip (if b then 1#1 else 0#1)) [] :=
  fun hl => ⟨rfl, Or.inl ⟨hl, k (), [], rfl, Or.inl ⟨(), rfl, rfl, rfl⟩, rfl⟩⟩

/-- THE RESIDUAL-PROGRAM INVARIANT: the disk's step preserves `edpWf`. -/
theorem ediskStepWf (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState)
    (e' : EExpr) (σ' : WGState) :
    edpWf dp → ediskStep gen dp dws σ e' σ' →
    ∃ dp' dws', e' = .EDisk gen dp' dws' ∧ edpWf dp' := by
  intro hwf h
  rcases h with ⟨-, rfl, -⟩ | ⟨pa, n, aq, k, tvs, rfl, -, -, rfl, -⟩ | ⟨k, rfl, rfl, -⟩ |
    ⟨pre, g, pa, bs, k, s, s', rfl, -, -, -, -, rfl, -⟩ |
    ⟨pre, g, pa, bs, k, s, rfl, -, -, rfl, -⟩ | ⟨pre, g, pa, bs, k, s, rfl, -, rfl, -⟩ |
    ⟨h, k, rfl, -, rfl, -⟩ | ⟨h, k, rfl, -, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨-, rfl, -⟩
  · exact ⟨_, _, rfl, virtioProgWf _⟩
  · have hw : DmWf (DRead pa n aq k) := hwf
    cases hw with
    | read _ _ _ _ _ hk => exact ⟨_, _, rfl, hk _⟩
  · have hw : DmWf (DFence k) := hwf
    cases hw with
    | fence _ hk => exact ⟨_, _, rfl, hk⟩
  · have hw : DmWf (DWriteDev pre g pa bs k) := hwf
    cases hw with
    | writeDev _ _ _ _ _ _ _ _ hk => exact ⟨_, _, rfl, hk _⟩
  · have hw : DmWf (DWriteDev pre g pa bs k) := hwf
    cases hw with
    | writeDev _ _ _ _ _ _ _ _ hk => exact ⟨_, _, rfl, hk _⟩
  · exact ⟨_, _, rfl, trivial⟩
  · exact ⟨_, _, rfl, trivial⟩
  · have hw : DmWf (DPop h k) := hwf
    cases hw with
    | pop _ _ hk => exact ⟨_, _, rfl, hk _⟩
  · exact ⟨_, _, rfl, DmWf.ret _⟩
  · exact ⟨_, _, rfl, trivial⟩

/-- THE DISK IS REDUCIBLE except at a `DRead` (whose answerability is the driver's
obligation, not a property of the language): a `DWriteDev` always takes one of its three
outcomes, a `DPop` one of its two, a stall loops. -/
theorem eprimStepDiskReducible (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState) :
    ethreadLive σ gen → edpWf dp →
    (∀ pa n aq k, dp ≠ some (DRead pa n aq k)) →
    ∃ e' σ', eprimStep (.EDisk gen dp dws) σ [] e' σ' [] := by
  intro hl hwf hnr
  have hstep : ∀ e' σ', ediskStep gen dp dws σ e' σ' →
      ∃ e0 σ0, eprimStep (.EDisk gen dp dws) σ [] e0 σ0 [] :=
    fun e' σ' hs => ⟨e', σ', rfl, rfl, Or.inl ⟨hl, hs⟩⟩
  match dp, hwf, hnr, hstep with
  | none, _, _, hstep => exact hstep _ _ (Or.inl ⟨rfl, rfl, rfl⟩)
  | some (DRet DIdle), _, _, hstep =>
    exact hstep _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, rfl, rfl⟩)))))))))
  | some (DRet DStall), _, _, hstep =>
    exact hstep _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, rfl, rfl⟩)))))))))
  | some (DRead pa n aq k), _, hnr, _ => exact absurd rfl (hnr pa n aq k)
  | some (DFence k), _, _, hstep =>
    exact hstep _ _ (Or.inr (Or.inr (Or.inl ⟨k, rfl, rfl, rfl⟩)))
  | some (DWriteDev pre g pa bs k), hwf, _, hstep =>
    have hw : DmWf (DWriteDev pre g pa bs k) := hwf
    cases hw with
    | writeDev _ _ _ _ _ n hn hlen _ =>
      rcases hpre : pre (dvirtio σ.wgdev) with ⟨s, b⟩
      cases b with
      | false =>
        exact hstep _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨pre, g, pa, bs, k, s, rfl, hpre, rfl, rfl⟩))))))
      | true =>
        by_cases hw : (∃ s', g s = some s') ∧ ramBytes (pa s) (bs s).length
        · obtain ⟨⟨s', hg⟩, hram⟩ := hw
          have hne : bs s ≠ [] := by
            intro he
            have := hlen s
            rw [he] at this
            exact hn this.symm
          exact hstep _ _ (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨pre, g, pa, bs, k, s, s', rfl, hpre, hg, hram, hne, rfl, rfl⟩))))
        · have hor : g s = none ∨ ¬ ramBytes (pa s) (bs s).length := by
            by_cases hram : ramBytes (pa s) (bs s).length
            · left
              cases hg : g s with
              | none => rfl
              | some s' => exact absurd ⟨⟨s', hg⟩, hram⟩ hw
            · exact Or.inr hram
          exact hstep _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨pre, g, pa, bs, k, s, rfl, hpre, hor, rfl, rfl⟩)))))
  | some (DPop h k), _, _, hstep =>
    by_cases hph : (Virtio.phase (dvirtio σ.wgdev) h).isSome = true
    · exact hstep _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h, k, rfl, hph, rfl, rfl⟩)))))))
    · exact hstep _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h, k, rfl, by simpa using hph, rfl, rfl⟩))))))))

end Weak
