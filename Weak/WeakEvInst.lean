/-
Weak: **the PROGRAM/MEMORY FACTORIZATION of the event language's step** (Phase B, part 1).

Rocq: `iris/WeakEvInst.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

Worklist `claude-notes/projects/weak-memory-soundness.md` (Phase B, items B2/B3, phase 1 = the
LANGUAGE-SIDE half); design `claude-notes/design/weak-memory-event-granular.md`.

Layer 1's promise-free machine is parametric in a PROGRAM STEP `P → D → Wlabel → P → D → Prop`
which is LOG-BLIND and WSTATE-BLIND: everything the machine does to the log and to the views it does
FROM THE LABEL alone.  `WeakEvLang`'s step relation is not written that way — each arm does its own
σ-update inline.  This file FACTORS every arm of `WeakEvLang.ecycleStep` / `ediskStep` (and the
device threads) into
  * a PROGRAM half (`pstepNode` / `pstepPlic` / `pstepDisk`), which sees only the agent's own
    program state and the device fabric, and
  * a MEMORY half (`elabOk` + `elabApply`, and `edlabOk` + `edlabApply` + `edlabWs` for the disk
    agent), which is a FUNCTION OF THE LABEL,
and proves the two halves recompose to the language's own step, in BOTH directions (§5).  Nothing
here mentions Layer 1's machine; §6–§9 prove the program half's Layer-1 side conditions
(lat-freedom, timestamp-obliviousness, the fabric marker `pdevOk`, the load-dependency pin, the two
class premises) and T2 for the event instance.

THE PLACEMENT RULE: the program half owns what the language reads out of the EXPRESSION (the
hart's residual monad and parked fence, the disk's residual device program) plus the two
σ-components that are agent-private or fabric-shared but label-invisible — the hart's REGISTERS
and the DEVICE FABRIC.  The memory half owns the log and the `Wstate`s.

THE FABRIC MARKER `LDev` (M5): every arm that READS OR MOVES the device fabric carries `LDev`,
whose memory half is `LSilent`'s verbatim (hart side: the MMIO read/write and the PLIC wire; disk
side: START, COMMIT and the device threads).  `pdevEv` reads the marker off the label alone, and
`pdevEvOk` discharges `WeakPromiseFact.pdevOk`.  The `DWild` arm is `LSilent`, NOT `LDev` (it reads
and moves nothing; marking it would put a spurious device event into the replay's device order).

THE DISK IS AN ORDINARY AGENT (M5): `DRead` is a plain RAM read (`LLoad aq false`), `DWrite` a RAM
write (`LStore false`), `DFence` a `fence rw,rw` (`LFence true true true true`); `pclsEv` at the
disk is `WeakEvLang.ddevClass ws`.

TWO RECORDED DEVIATIONS FROM THE COMMISSIONED SHAPE (Rocq (D1)/(D2)):
(D1) the register update is an `Option RegFile` (`none` = unchanged), so every §5 equation is a
     LITERAL equality of `WGState`s (Rocq: no functional extensionality); the bits field is the
     same (`Option Ibch`, D3).
(D2) `fence.i` carries the INERT label `LFence false false false false`, not `LSilent`: the
     language's barrier arm always re-inserts the hart's `Wstate`; `fencePost ws false false false
     false = ws` (`fencePostId`).

THE TWO `LInstr`s (W2b condition 1): the BOUNDARY (`pure`, the fresh `riscvStep`) is a reset point
and clears the announced bits; the `instrAnnounce` node is the second reset and BANKS the
announced bits (`oib = some (ibAnn (ibOfBvn w))`, D3).  Both are needed: the boundary's, because
the model announces AFTER the fetch (a reset riding the announce alone would let the fetch consume
the previous instruction's data-read bank through `wTbank`); the announce's, because otherwise the
FETCH's own read view would sit in `wLdv` for the whole instruction and leak into every
`DLdRes`-carrying register write.  The registers' dependency roles are decoded from the banked
bits by `WeakDeps.depsOfIb` (`edeps`).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  `M unit` ↦ `SailM Unit`; `regstate` ↦ `RegFile`;
   `dev_state` ↦ `DevStates`; `oib32` ↦ `Ibch`; `default x o` ↦ `o.getD x`; `fin_to_nat c` ↦
   `c.val`; `tvs.*1`/`.*2` ↦ `tvs.map Prod.fst`/`Prod.snd`; `S (length lg)` ↦ `lg.length + 1`;
   `wgstate` updates are `{ σ with … }` (WeakLang's record has the Lean-only `wgitv`/`wgrt`, which
   `elabApply`/`edlabApply` carry).  One arm per lean-sail `Outcome` constructor
   (`Weak/WeakEvLang.lean` deviation 4): a model `.error` node and `readRam`/`writeRam` are stuck;
   a RAM/MMIO write whose request carries `value = none` is stuck; `tlbi` is Rocq `TlbOp`.
2. O2 — THE READ ARM (`notes/weak-port-o2-design.md` §1.4; owner decisions O2/D3/D4).  Rocq's
   `pnode_step` RAM-read arm was guarded by `ak_coh (classify …) = false` (a Lean-model fetch,
   `AK_ifetch`, would have been STUCK).  It is now the TOTAL three-way split of
   `WeakEvLang.emonadStep` on `classify`:
   - `akIfetch = true`: the I-CACHE READ, label `LIFetch (paZ pa) tvs` — NO `aq`, NO `lat`, NO
     address sources (a fetch has no address dependency in RVWMO; this also removes the review's
     Q2 hazard);
   - `akIfetch = false`: Rocq's plain (`LLoad`) / exclusive (`LExLoad`) disjunction verbatim.
   Consequences: `elabOk (LIFetch base tvs)` = `ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base
   tvs` at the hart's own instruction view (Stage B, D2), and the memory half of a fetch is the
   IDENTITY on log and views (`elabWs`/`elabLog` of `LIFetch` = σ's).  So the fetch's read view
   never enters `wLdv`/`wTbank` (the second-`LInstr` reset stays, and now has nothing of the
   fetch's to reset).  `edlabOk (LIFetch ..)` is `False` (the disk never fetches,
   `pstepDiskNoFetch`).  `elabApplyFetch` is the Lean-only σ-shape lemma (`σ' = σ`).
3. SYMBOLIC ANNOUNCES (`notes/symbolic-model.md`): Rocq's `InstrAnnounce ob` is Lean's
   `.instrAnnounce n w`; the bits banked are `ibAnn (ibOfBvn w)` (WeakEvLang deviation 7).
   `.branchAnnounce` is silent, as in Rocq.
4. O2 STAGE B — THE INSTRUCTION VIEW.  The language's barrier arm also moves the hart's
   `wgitv` (`WeakEvLang.ewgBar`, its deviation 6): `fence.i` raises it to `itvPost`.  The memory
   half cannot read the barrier kind off the inert label (D2's `LFence false false false false`
   is also what an arbitrary PARKED fence `fn = some (false, false, false, false)` emits, which
   leaves `wgitv` alone), so — exactly as (D1) for the registers — the program half reports the
   barrier it executed: every program-half relation gains a final argument
   `obar : Option barrier_kind` (`none` everywhere but the barrier node, where it is `some b`), and
   `elabApply` takes it and applies `eitvApply σ c obar` (Lean-only).  `pstepEv` quantifies it
   existentially beside `ors`/`oib` (Layer 1 has no instruction view: `WeakPromise.wpstep.WPIFetch`
   checks at view 0).  `elabApplyBarrier` is stated with `ewgBar`.
5. DEVICES (forced by Lean's device model, `Weak/WeakEvLang.lean` deviation 2; owner decision Q1,
   `notes/weak-port-architecture.md`).  Lean's UARTs and PLIC are device PROGRAMS (`EExpr.EDev`,
   stepped by `WeakLang.wdevStep`), not Rocq's stateless threads, and the program half steps them
   EXACTLY: THE FABRIC TYPE is `Efab` (`WeakEvPf` deviation 9: `DevStates` plus the residual
   programs `efU0`/`efU1`/`efPlic`), not `DevStates` (Rocq `dev_state`).  So `pstepEv`,
   `pstepHart`, `pstepDisk`, `pstepPlic`, `pdiskUart` and every lemma about them are stated at
   `Efab`; `pnodeStep`/`pstepNode`/`pdiskProg` keep `DevStates` and are lifted (`pstepHart`'s
   node arm and `pstepDisk`'s program arm read `d.efDev` and move only it:
   `d' = { d with efDev := d'.efDev }`).
   - `fdevStep dv m ds m' ds'` (Lean-only): `wdevStep` at the root task, verbatim, over the
     device states alone, at the `devOpPlain false` nodes (`step`, `get`, `choose`, `sample`, and
     `pure`, which restarts the body); the bus-master `dmaRead`/`dmaWrite` (they read/move the
     LOG), `join` (it reads the task bookkeeping), `fork` and the wire write are STUCK there.
   - `pstep_plic` ↦ `pstepPlic`: the PLIC program sits at `setPin cpu mm b` (Rocq: the S pin at
     `dev_seip d cpu`, a function of the fabric); hart `cpu` takes it, `ors = some (pinSet rs mm
     b)`, and the PLIC program advances to `k ()`.  `obar = none`.
   - `pdisk_uart` ↦ `pdiskUart`: one `fdevStep` of a UART program or of the PLIC program (the
     gateway), at the disk agent (Rocq: `uart_step d d'`).
   - `pdisk_prog` has SEVEN arms: the PLIC latch is a step of the PLIC program (WeakEvLang
     deviation 2), so it is a `pdiskUart` move.
   - `eplic_step_factor` ↦ `eplicStepFactor`, an iff at the WIRE PRIMITIVE (`wdevOpStep … (.setPin
     c mm b)`); `euart_step_factor` ↦ `euartStepFactor`, an iff (as Rocq) between a root,
     non-forking device step at a plain pin-free node (`devNodePlain false m`) and `fdevStep` with
     σ-shape `edlabApply σ LDev .WCplain d'`.  `eplic_step_pstep_hart` ↦ `eplicStepPstepHart` (at
     a `setPin` node of `F.efPlic`), `euart_step_pstep_disk` ↦ `euartStepPstepDisk` (per
     `UartId`), Lean-only `eplicGateStepPstepDisk` (the PLIC off a wire write);
     `ecycleStepPstepHart`/`ediskStepPstepDisk` take the fabric `F` with `F.efDev = σ.wgdev`.
   - PLAINNESS (Lean-only): `devOpPlain pin`, the inductive `DevPlain pin` (every node plain),
     `devNodePlain`, `devPlainNode`, `devPlainStep` (kept by a device step whose body is plain),
     `devPlainBind`/`devPlainLift`/`devPlainChooseLt`, and THE BOARD'S BODIES: `uartBodyPlain`
     (`DevPlain false`), `plicBodyPlain` (`DevPlain true`: its one other node is the wire write).
     The ⇐ direction of `WeakEvCapstone` reads them off a pool invariant.
   Lean-only helpers `pinSet`, `pstepPlicPin`, `wdevStepNoPin`, `wgEqDevRt`, `wdevOfFdevStep`,
   `fdevStepOfWdev`.
6. THE OPERAND LISTS: the Lean language's store / exclusive-read arms carry
   `depsAsrc`/`depsVsrc (edeps σ c)`, which is `depsOfIb (σ.wgib c).ibBits` — the program half's
   `depsOfIb ib.ibBits` at `ib = σ.wgib c`, by conversion (as Rocq).
7. T2 (`t2Ev`).  Stage C (owner ruling Q-C3): the bridge treats a fetch as a stutter, so `t2Ev`
   is Rocq's statement again, through `WeakRefuse.t2Bridge` (Stage B's fetch → plain-load
   premise on the re-fused runs is deleted).
8. Lean-only O2 facts for the robustness tower (`WeakRobustSim.tsOblivious`'s fourth, fetch
   clause, its deviation 4): `pnodeStepTsIfetch`, `pstepNodeTsIfetch`, `pstepDiskTsIfetch`,
   `pstepEvTsIfetch`; and `pstepDiskNoFetch`.  Lean-only `pnodeStepCases` (the label shapes of
   the program half, from which lat-freedom, `noRmw` and `ldepfree` are read off),
   `erwLabelCases`, `ebarLabelFence`, `elabOkErwLabel`, `elabOkEbarLabel`, `lenOfSnd`,
   `eitvApply`.
9. PROOFS: per-arm case analysis on the `Outcome` constructor (Rocq: `destruct oc; try
   esil_case; try estuck_case`); the Rocq Ltacs `efac4`/`esil_case`/`estuck_case` are the local
   macros `esil_case`/`estuck_case` (plus `edev_sil` for `pnodeStepDevFree`).

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Rocq → Lean name map.**  `pnode_wclass` `pnodeWclass`, `pcls_ev` `pclsEv`,
`pcls_ev_exstore_excl` `pclsEvExstoreExcl`, `pcls_ev_silent` `pclsEvSilent`, `pcls_ev_ldev`
`pclsEvLdev`, `pcls_ev_fence` `pclsEvFence`, `pnode_wclass_relp` `pnodeWclassRelp`,
`pcls_ev_erasable` `pclsEvErasable`, `ebar_label` `ebarLabel`, `pnode_step` `pnodeStep`,
`pstep_node` `pstepNode`, `pstep_plic` `pstepPlic`, `pstep_hart` `pstepHart`, `pdisk_prog`
`pdiskProg`, `pdisk_uart` `pdiskUart`, `pstep_disk` `pstepDisk`, `pstep_ev` `pstepEv`, `pdev_ev`
`pdevEv`, `elab_ok` `elabOk`, `eregs_apply` `eregsApply`, `elab_ws` `elabWs`, `elab_log`
`elabLog`, `eib_apply` `eibApply`, `elab_apply` `elabApply`, `edlab_ok` `edlabOk`, `edlab_ws`
`edlabWs`, `edlab_log` `edlabLog`, `edlab_apply` `edlabApply`, `elab_apply_silent`
`elabApplySilent`, `elab_apply_dev` `elabApplyDev`, `elab_apply_ldev` `elabApplyLdev`,
`elab_apply_ldev_reg` `elabApplyLdevReg`, `elab_apply_reg` `elabApplyReg`, `elab_apply_load`
`elabApplyLoad`, `elab_apply_fence` `elabApplyFence`, `elab_apply_store` `elabApplyStore`,
`elab_apply_exload` `elabApplyExload`, `elab_apply_exstore` `elabApplyExstore`, `elab_apply_rw`
`elabApplyRw`, `elab_apply_instr` `elabApplyInstr`, `elab_apply_ib` `elabApplyIb`,
`elab_apply_barrier` `elabApplyBarrier`, `edlab_apply_silent` `edlabApplySilent`,
`edlab_apply_ldev_id` `edlabApplyLdevId`, `edlab_apply_load_id` `edlabApplyLoadId`,
`edlab_apply_fence_id` `edlabApplyFenceId`, `edlab_apply_dev` `edlabApplyDev`,
`edlab_apply_ldev` `edlabApplyLdev`, `edlab_apply_store` `edlabApplyStore`, `ecycle_step_factor`
`ecycleStepFactor`, `eplic_step_factor` `eplicStepFactor`, `euart_step_factor`
`euartStepFactor`, `edisk_step_factor` `ediskStepFactor`, `edisk_step_pstep_disk`
`ediskStepPstepDisk`, `euart_step_pstep_disk` `euartStepPstepDisk`, `ecycle_step_pstep_hart`
`ecycleStepPstepHart`, `eplic_step_pstep_hart` `eplicStepPstepHart`, `pnode_step_lat_free`
`pnodeStepLatFree`, `pstep_node_lat_free` `pstepNodeLatFree`, `pstep_hart_lat_free`
`pstepHartLatFree`, `pdisk_prog_lat_free` `pdiskProgLatFree`, `pstep_disk_lat_free`
`pstepDiskLatFree`, `pstep_disk_no_rmw` `pstepDiskNoRmw`, `pdisk_prog_ts_load`
`pdiskProgTsLoad`, `pstep_disk_ts_load` `pstepDiskTsLoad`, `pstep_ev_lat_free`
`pstepEvLatFree`, `pnode_step_ts_load` `pnodeStepTsLoad`, `pnode_step_no_rmw` `pnodeStepNoRmw`,
`pstep_node_ts_load` `pstepNodeTsLoad`, `pstep_hart_no_rmw` `pstepHartNoRmw`, `pstep_ev_ts_load`
`pstepEvTsLoad`, `pstep_ev_no_rmw` `pstepEvNoRmw`, `pstep_ev_ts_rmw` `pstepEvTsRmw`,
`pnode_step_dev_free` `pnodeStepDevFree`, `pstep_node_dev_free` `pstepNodeDevFree`,
`pdisk_prog_dev_free` `pdiskProgDevFree`, `pstep_disk_dev_free` `pstepDiskDevFree`,
`pdev_ev_ok` `pdevEvOk`, `pnode_step_ldepfree` `pnodeStepLdepfree`, `pstep_node_ldepfree`
`pstepNodeLdepfree`, `pstep_plic_ldepfree` `pstepPlicLdepfree`, `pstep_hart_ldepfree`
`pstepHartLdepfree`, `pstep_disk_depfree` `pstepDiskDepfree`, `pstep_ev_ldepfree`
`pstepEvLdepfree`, `pstep_disk_no_ex` `pstepDiskNoEx`, `pnode_step_ts_exload`
`pnodeStepTsExload`, `pstep_node_ts_exload` `pstepNodeTsExload`, `pstep_disk_ts_exload`
`pstepDiskTsExload`, `pstep_ev_ts_exload` `pstepEvTsExload`, `pnode_step_exstore_excl`
`pnodeStepExstoreExcl`, `pstep_node_exstore_excl` `pstepNodeExstoreExcl`,
`pstep_hart_exstore_excl` `pstepHartExstoreExcl`, `pcls_ev_fusable` `pclsEvFusable`, `t2_ev`
`t2Ev`.  Lean-only: see deviations 2, 4, 5 and 8 (deviation 5: `fdevStep`, `devOpPlain`,
`DevPlain`, `devNodePlain`, `devPlainNode`, `wdevOfFdevStep`, `fdevStepOfWdev`, `devPlainStep`,
`devPlainBind`, `devPlainLift`, `devPlainChooseLt`, `uartBodyPlain`, `plicBodyPlain`,
`eplicGateStepPstepDisk`).

**Not ported:** nothing (the Rocq Ltacs are local macros, deviation 9).

**Statements checked** (by hand, against Rocq): all; the changed ones are the deviations above
(the `obar` argument everywhere, the RAM-read arm and `elabOk`/`edlabOk`'s `LIFetch` clauses,
the `Efab` fabric of `pstepEv` & co., `pstepPlic`/`pdiskUart`/`pdiskProg`, the device
factorizations and their corollaries).
-/
import Weak.WeakEvPf
import Weak.WeakRefuse

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 1. The program state and the class it writes -/

/-- The class off the `memWrite` node the hart is sitting at. -/
def pnodeWclass (m : SailM Unit) (ws : Wstate) : WmClass :=
  match m with
  | .impure (.ok (.memWrite _ _ req)) _ => wmClassOf (classify req.access_kind) ws
  | _ => .WCplain

def pclsEv (p : Pexv6) (l : Wlabel) (ws : Wstate) : WmClass :=
  match l with
  | LRmw .. => .WCexcl
  | LStore .. =>
      match p with
      | .PHart _ m _ _ _ => pnodeWclass m ws
      | .PDisk _ => ddevClass ws
  | LExStore .. =>
      match p with
      | .PHart _ m _ _ _ => pnodeWclass m ws
      | .PDisk _ => ddevClass ws
  | LSilent | LLoad .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExLoad ..
  | LIFetch .. => .WCplain

/-- THE CLASS DID NOT MOVE (RMW split S3). -/
theorem pclsEvExstoreExcl (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) K (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (ws : Wstate) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    (classify req.access_kind).akLatest = true →
    pclsEv (.PHart cpu (.impure (.ok (.memWrite n va req)) K) rs fn ib)
      (LExStore rl base data asrc vsrc) ws = .WCexcl := by
  intro hlat
  simp [pclsEv, pnodeWclass, wmClassOf, hlat]

theorem pclsEvSilent (p : Pexv6) (ws : Wstate) : pclsEv p LSilent ws = .WCplain := rfl

theorem pclsEvLdev (p : Pexv6) (ws : Wstate) : pclsEv p LDev ws = .WCplain := rfl

theorem pclsEvFence (p : Pexv6) (ws : Wstate) (pr pw sr sw : Bool) :
    pclsEv p (LFence pr pw sr sw) ws = .WCplain := rfl

/-- THE ERASURE'S CLASS PREMISE: the class reads the access kind and `wRelp` only. -/
theorem pnodeWclassRelp (m : SailM Unit) (we wi : Wstate) :
    we.wRelp = wi.wRelp → pnodeWclass m we = pnodeWclass m wi := by
  intro h
  cases m with
  | pure a => rfl
  | impure e k =>
    cases e with
    | error _ => rfl
    | ok o => cases o <;> first | rfl | simp only [pnodeWclass, wmClassOf, h]

theorem pclsEvErasable : pclsErasable pclsEv := by
  intro p l we wi hrelp
  cases l <;> simp only [eraseLbl, pclsEv] <;>
    first
    | rfl
    | (cases p with
        | PHart _ m _ _ _ => exact pnodeWclassRelp m we wi hrelp
        | PDisk _ => simp only [ddevClass, wmClassOf, hrelp])

/-! ## 2. The program half -/

/-- The inert-fence-inclusive barrier label (deviation (D2)). -/
def ebarLabel (b : barrier_kind) : Wlabel :=
  match ebarNow b with
  | some (pr, pw, sr, sw) => LFence pr pw sr sw
  | none => LFence false false false false

/-- THE MONAD-NODE DISPATCH.  `ors` is the register write (D1), `oib` the bits write (D3), `obar`
the barrier executed (deviation 4). -/
def pnodeStep (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) : Prop :=
  match m with
  | .pure _ =>
      -- THE BOUNDARY: the reset point (`LInstr`); it clears the announced bits (D3, DEC-7)
      ∃ tick : Bool,
        l = LInstr ∧ m' = riscvStep tick ∧ ors = none ∧ fn' = none ∧ d' = d ∧
        oib = some ibNone ∧ obar = none
  | .impure (.error _) _ => False
  | .impure (.ok o) k =>
    match o, k with
    -- DEC-7: THE READ SET ACCUMULATES HERE
    | .regRead r, k =>
        l = LSilent ∧ m' = k (rs r) ∧ ors = none ∧ fn' = none ∧ d' = d ∧
        oib = some (ibRd ib r) ∧ obar = none
    -- D3-2: the classification's label
    | .regWrite r v, k =>
        l = erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r) ∧ m' = k PUnit.unit ∧
        ors = some (rs.set r v) ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .memRead n _va req, k =>
        if devAddr req.pa then
          -- MMIO READ — FABRIC-TOUCHING, hence `LDev`
          ∃ w : BitVec (8 * n),
            devRead d req.pa n = some (w, d') ∧ l = LDev ∧ m' = k (.Ok (w, none)) ∧
            ors = none ∧ fn' = none ∧ oib = none ∧ obar = none
        else
          -- O2: THE I-CACHE READ (no aq, no lat, no address sources)
          ((classify req.access_kind).akIfetch = true ∧
            ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
              tvs.length = n ∧
              (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
              l = LIFetch (paZ req.pa) tvs ∧ m' = k (.Ok (w, none)) ∧ ors = none ∧
              fn' = none ∧ d' = d ∧ oib = none ∧ obar = none)
          ∨
          ((classify req.access_kind).akIfetch = false ∧
            (-- the PLAIN RAM read; no `readOk` here — that is `elabOk` of the label
             ((classify req.access_kind).akLatest = false ∧
               ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
                 tvs.length = n ∧
                 (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
                 l = LLoad (classify req.access_kind).akSync false (paZ req.pa) tvs [] ∧
                 m' = k (.Ok (w, none)) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
                 obar = none)
             ∨
             -- THE EXCLUSIVE READ (RMW split S3)
             ((classify req.access_kind).akLatest = true ∧
               ∃ (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
                 tvs.length = n ∧
                 (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
                 l = LExLoad (classify req.access_kind).akSync (paZ req.pa) tvs
                       (depsAsrc (depsOfIb ib.ibBits)) ∧
                 m' = k (.Ok (w, none)) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
                 obar = none)))
    | .memWrite n va req, k =>
        if devAddr req.pa then
          -- MMIO WRITE — FABRIC-TOUCHING, hence `LDev`
          match req.value with
          | some v =>
              devWrite d req.pa n v = some d' ∧ l = LDev ∧ m' = k (.Ok (some true)) ∧
              ors = none ∧ fn' = none ∧ oib = none ∧ obar = none
          | none => False
        else
          match req.value with
          | some v =>
              n ≠ 0 ∧
              (((classify req.access_kind).akLatest = false ∧
                 l = LStore (classify req.access_kind).akSync (paZ req.pa)
                       (WeakInterpProj.wbytes n v) (depsAsrc (depsOfIb ib.ibBits))
                       (depsVsrc (depsOfIb ib.ibBits)) ∧
                 m' = k (.Ok (some true)) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
                 obar = none)
               ∨
               ((classify req.access_kind).akLatest = true ∧
                 (-- THE CONDITIONAL WRITE (RMW split S3)
                  (l = LExStore (classify req.access_kind).akSync (paZ req.pa)
                         (WeakInterpProj.wbytes n v) (depsAsrc (depsOfIb ib.ibBits))
                         (depsVsrc (depsOfIb ib.ibBits)) ∧
                    m' = k (.Ok (some true)) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
                    obar = none)
                  ∨
                  -- THE RETRY SELF-LOOP (memory-blind)
                  (l = LSilent ∧ m' = .impure (.ok (.memWrite n va req)) k ∧ ors = none ∧
                    fn' = none ∧ d' = d ∧ oib = none ∧ obar = none))))
          | none => False
    | .barrier b, k =>
        l = ebarLabel b ∧ m' = k () ∧ ors = none ∧ fn' = ebarPark b ∧ d' = d ∧ oib = none ∧
        obar = some b
    -- D3: THE ANNOUNCE banks the bits; D3-2: it is the instruction start (`LInstr`)
    | .instrAnnounce _ w, k =>
        l = LInstr ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧
        oib = some (ibAnn (ibOfBvn w)) ∧ obar = none
    | .branchAnnounce _ _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .cacheOp _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .tlbi _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .takeException _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .returnException _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .translationStart _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .translationEnd _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .cycleCount, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .message _, k =>
        l = LSilent ∧ m' = k () ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none
    | .getCycleCount, k =>
        l = LSilent ∧ m' = k (0 : Nat) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
        obar = none
    | .choose _, k =>
        ∃ ch, l = LSilent ∧ m' = k ch ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
          obar = none
    -- the legacy direct-RAM events: STUCK
    | .readRam .., _ => False
    | .writeRam .., _ => False

/-- THE HART'S OWN STEP, parked fence and all (`cpu` unused, kept for `pstepPlic`'s signature). -/
def pstepNode (_cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) : Prop :=
  match fn with
  | some (pr, pw, sr, sw) =>
      -- THE PARKED FENCE GATES EVERYTHING (WeakEvLang D5)
      l = LFence pr pw sr sw ∧ m' = m ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
      obar = none
  | none => pnodeStep m rs ib d l m' ors fn' d' oib obar

/-! ### The residual device programs (deviation 5, owner decision Q1) -/

/-- The primitives the program half steps (Lean-only): the local-state primitives, and the wire
write when `pin`.  Bus-master reads/writes read or move the LOG and `join` reads the task
bookkeeping, neither of which Layer 1's program half sees; the board's UART/PLIC never use them
(`uartBodyPlain`, `plicBodyPlain`). -/
def devOpPlain {S T : Type} (pin : Bool) : DevOp S T → Prop
  | .step _ => True
  | .get => True
  | .choose => True
  | .sample _ => True
  | .setPin _ _ _ => pin = true
  | .dmaRead _ _ => False
  | .dmaWrite _ _ _ _ => False
  | .fork _ => False
  | .join _ => False

/-- A device program made of plain primitives only (Lean-only). -/
inductive DevPlain {S T α : Type} (pin : Bool) : DevM S T α → Prop where
  | pure (a : α) : DevPlain pin (.pure a)
  | op (o : DevOp S T) (k : o.ret → DevM S T α) :
      devOpPlain pin o → (∀ v, DevPlain pin (k v)) → DevPlain pin (.op o k)

/-- THE DEVICE PROGRAM'S OWN STEP, over the fabric alone (Lean-only, deviation 5): `wdevStep` at
the root task, verbatim, at every node but the wire write (`pstepPlic`) and the primitives
`devOpPlain` excludes (stuck here). -/
def fdevStep (dv : DevId) (m : DevProg dv) (ds : DevStates) (m' : DevProg dv)
    (ds' : DevStates) : Prop :=
  match m with
  | .pure _ => m' = (devSig dv).body ∧ ds' = ds
  | .op o k =>
    match o, k with
    | .step f, k =>
        (∃ s' os, f (ds.st dv) = some (s', os) ∧ devObsOk dv (ds.st dv) s' os ∧ m' = k () ∧
           ds' = ds.set dv s') ∨
        ((∀ s' os, f (ds.st dv) = some (s', os) → ¬ devObsOk dv (ds.st dv) s' os) ∧
           m' = .op (.step f) k ∧ ds' = ds)
    | .get, k => m' = k (ds.st dv) ∧ ds' = ds
    | .choose, k => ∃ n, m' = k n ∧ ds' = ds
    | .sample src, k => m' = k (devLevel ds src) ∧ ds' = ds
    | _, _ => False

/-- The pin write of the PLIC wire (Lean-only, deviation 5). -/
def pinSet (rs : RegFile) (mm b : Bool) : RegFile :=
  if mm then rs.set .sig_meip (if b then 1#1 else 0#1) else rs.set .sig_seip (if b then 1#1 else 0#1)

/-- THE PLIC WIRE (deviation 5): when the PLIC PROGRAM (in the fabric) sits at a wire write to
hart `cpu`, that hart takes it — the pin the program names, the value it names — moving neither
its monad nor its parked fence; the PLIC program advances. -/
def pstepPlic (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (_ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) : Prop :=
  ∃ (mm b : Bool) (k : Unit → DevProg .plic),
    d.efPlic = .op (.setPin cpu mm b) k ∧
    l = LDev ∧ m' = m ∧ fn' = fn ∧ d' = { d with efPlic := k () } ∧ oib = none ∧ obar = none ∧
    ors = some (pinSet rs mm b)

/-- The hart's own step moves only the device STATES of the fabric (deviation 5). -/
def pstepHart (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) : Prop :=
  (pstepNode cpu m rs fn ib d.efDev l m' ors fn' d'.efDev oib obar ∧
    d' = { d with efDev := d'.efDev }) ∨
  pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar

/-- THE DISK AGENT (M5): one disjunct per node of the residual device program plus the two
fabric arms (seven arms, deviation 5). -/
def pdiskProg (dp : Option (DM Dres)) (d : DevStates) (l : Wlabel) (dp' : Option (DM Dres))
    (d' : DevStates) : Prop :=
  -- START — reads the fabric
  (dp = none ∧ l = LDev ∧ dp' = some (virtioProg (dvirtio d)) ∧ d' = d)
  ∨
  -- DRead — a hart's plain RAM read
  (∃ (pa : PAddr) (n : Nat) (aq : Bool) (k : List (BitVec 8) → DM Dres)
      (tvs : List (Nat × BitVec 8)),
     dp = some (DRead pa n aq k) ∧ tvs.length = n ∧ l = LLoad aq false (paZ pa) tvs [] ∧
     dp' = some (k (tvs.map Prod.snd)) ∧ d' = d)
  ∨
  -- DWrite — a hart's RAM write
  (∃ (pa : PAddr) (bs : List (BitVec 8)) (k : DM Dres),
     dp = some (DWrite pa bs k) ∧ bs ≠ [] ∧ l = LStore false (paZ pa) bs [] [] ∧
     dp' = some k ∧ d' = d)
  ∨
  -- DFence — the device-side write barrier
  (∃ k : DM Dres, dp = some (DFence k) ∧ l = LFence true true true true ∧ dp' = some k ∧ d' = d)
  ∨
  -- COMMIT — moves the fabric
  (∃ delta : VirtioState → VirtioState,
     dp = some (DRet (DDone delta)) ∧ l = LDev ∧ dp' = none ∧
     d' = setDvirtio d (delta (dvirtio d)))
  ∨
  -- the malformed chain (`LSilent`, not `LDev`)
  (∃ prog' : DM Dres,
     dp = some (DRet DWild) ∧ DmWildChain prog' ∧ l = LSilent ∧ dp' = some prog' ∧ d' = d)
  ∨
  -- nothing pending
  (dp = some (DRet DIdle) ∧ l = LSilent ∧ dp' = none ∧ d' = d)

/-- THE DEVICE THREADS' FABRIC MOVE (Rocq: the UART thread; deviation 5): one `fdevStep` of a
UART program or of the PLIC program off a wire write, at the disk agent. -/
def pdiskUart (dp : Option (DM Dres)) (d : Efab) (l : Wlabel) (dp' : Option (DM Dres))
    (d' : Efab) : Prop :=
  dp' = dp ∧ l = LDev ∧
  ((∃ (i : UartId) (m' : DevProg (.uart i)) (ds' : DevStates),
      fdevStep (.uart i) (efU d i) d.efDev m' ds' ∧ d' = efUset { d with efDev := ds' } i m') ∨
   (∃ (m' : DevProg .plic) (ds' : DevStates),
      fdevStep .plic d.efPlic d.efDev m' ds' ∧ d' = { d with efDev := ds', efPlic := m' }))

def pstepDisk (dp : Option (DM Dres)) (d : Efab) (l : Wlabel) (dp' : Option (DM Dres))
    (d' : Efab) : Prop :=
  (pdiskProg dp d.efDev l dp' d'.efDev ∧ d' = { d with efDev := d'.efDev }) ∨
  pdiskUart dp d l dp' d'

/-- THE PROGRAM STEP, at Layer 1's type (fabric `Efab`, deviation 5).  Mismatched constructors
are `False`. -/
def pstepEv (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) : Prop :=
  match p, p' with
  | .PHart cpu m rs fn ib, .PHart cpu' m' rs' fn' ib' =>
      cpu' = cpu ∧
      ∃ (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind),
        rs' = ors.getD rs ∧ ib' = oib.getD ib ∧
        pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar
  | .PDisk dp, .PDisk dp' => pstepDisk dp d l dp' d'
  | _, _ => False

/-- THE FABRIC MARKER, a function of the LABEL alone. -/
def pdevEv (_p : Pexv6) (l : Wlabel) (_p' : Pexv6) : Bool :=
  match l with
  | LDev => true
  | _ => false

/-! ## 3. The memory half -/

def elabOk (σ : WGState) (c : CPU) (l : Wlabel) : Prop :=
  match l with
  | LSilent => True
  | LLoad aq lat base tvs asrc =>
      asrc = [] ∧ readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) aq lat base tvs
  | LStore _ _ data _ _ => data ≠ []
  | LRmw aq _ base tvs data _ _ =>
      data ≠ [] ∧ tvs.length = data.length ∧
      readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) aq false base tvs ∧
      exclOk σ.wglog c.val base tvs (σ.wglog.length + 1)
  | LFence .. => True
  | LDev => True
  | LRegW .. | LCtrl _ | LInstr => True
  | LExLoad aq base tvs _ => readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) aq false base tvs
  | LExStore _ base data _ _ =>
      data ≠ [] ∧ exwinOk σ.wglog c.val (σ.wgws c) base data.length (σ.wglog.length + 1)
  -- O2 (deviation 2): the i-cache read, at the hart's instruction view
  | LIFetch base tvs => ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs

def eregsApply (σ : WGState) (c : CPU) (ors : Option RegFile) : CPU → RegFile :=
  match ors with
  | some rs' => updCpu σ.wgregs c rs'
  | none => σ.wgregs

def elabWs (σ : WGState) (c : CPU) (l : Wlabel) : CPU → Wstate :=
  match l with
  | LSilent => σ.wgws
  | LLoad aq _ base tvs _ => updCpu σ.wgws c (loadPostRun (σ.wgws c) aq base (tvs.map Prod.fst))
  | LStore rl base data asrc vsrc =>
      updCpu σ.wgws c (storePostRunD (σ.wgws c) rl (srcsView (σ.wgws c) asrc)
        (srcsView (σ.wgws c) vsrc) base data.length (σ.wglog.length + 1))
  | LRmw aq rl base tvs data asrc vsrc =>
      updCpu σ.wgws c (storePostRunD
        (loadPostRunD (σ.wgws c) aq (srcsView (σ.wgws c) asrc) base (tvs.map Prod.fst))
        rl (srcsView (σ.wgws c) asrc) (srcsView (σ.wgws c) vsrc) base data.length
        (σ.wglog.length + 1))
  | LFence pr pw sr sw => updCpu σ.wgws c (fencePost (σ.wgws c) pr pw sr sw)
  | LDev => σ.wgws
  | LRegW rd srcs => updCpu σ.wgws c (regwPost (σ.wgws c) rd (srcsView (σ.wgws c) srcs))
  | LCtrl srcs => updCpu σ.wgws c (ctrlPost (σ.wgws c) (srcsView (σ.wgws c) srcs))
  | LInstr => updCpu σ.wgws c (instrPost (σ.wgws c))
  | LExLoad aq base tvs asrc =>
      updCpu σ.wgws c (exloadPostRunD (σ.wgws c) aq (srcsView (σ.wgws c) asrc) base
        (tvs.map Prod.fst))
  | LExStore rl base data asrc vsrc =>
      updCpu σ.wgws c (storePostRunD (σ.wgws c) rl (srcsView (σ.wgws c) asrc)
        (srcsView (σ.wgws c) vsrc) base data.length (σ.wglog.length + 1))
  -- O2: the fetch is view-silent
  | LIFetch .. => σ.wgws

def elabLog (σ : WGState) (c : CPU) (l : Wlabel) (k : WmClass) : List Wmsg :=
  match l with
  | LStore _ base data _ _ => σ.wglog ++ [⟨base, data, some c.val, k⟩]
  | LRmw _ _ base _ data _ _ => σ.wglog ++ [⟨base, data, some c.val, k⟩]
  | LExStore _ base data _ _ => σ.wglog ++ [⟨base, data, some c.val, k⟩]
  | LSilent | LLoad .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExLoad ..
  | LIFetch .. => σ.wglog

/-- D3: the `eregsApply` twin for the announced bits. -/
def eibApply (σ : WGState) (c : CPU) (oib : Option Ibch) : CPU → Ibch :=
  match oib with
  | some v => updCpu σ.wgib c v
  | none => σ.wgib

/-- O2 Stage B (deviation 4, Lean-only): the instruction view, moved by the barrier executed. -/
def eitvApply (σ : WGState) (c : CPU) (obar : Option barrier_kind) : CPU → Nat :=
  match obar with
  | some b => updCpu σ.wgitv c (itvPost (σ.wgws c) (σ.wgitv c) b)
  | none => σ.wgitv

def elabApply (σ : WGState) (c : CPU) (l : Wlabel) (k : WmClass) (ors : Option RegFile)
    (oib : Option Ibch) (obar : Option barrier_kind) (d' : DevStates) : WGState :=
  { σ with wgregs := eregsApply σ c ors, wglog := elabLog σ c l k, wgws := elabWs σ c l,
           wgdev := d', wgib := eibApply σ c oib, wgitv := eitvApply σ c obar }

/-- THE DISK AGENT'S VERSION (its `Wstate` lives in the expression). -/
def edlabOk (σ : WGState) (dws : Wstate) (l : Wlabel) : Prop :=
  match l with
  | LSilent => True
  | LLoad aq lat base tvs asrc => asrc = [] ∧ readOk (imgZ σ.wgimg) σ.wglog dws aq lat base tvs
  | LStore _ _ data asrc vsrc => asrc = [] ∧ vsrc = [] ∧ data ≠ []
  | LFence .. => True
  | LDev => True
  | LRmw .. => False
  | LRegW .. | LCtrl _ | LInstr => True
  | LExLoad .. | LExStore .. => False
  -- O2: the disk never fetches
  | LIFetch .. => False

def edlabWs (σ : WGState) (dws : Wstate) (l : Wlabel) : Wstate :=
  match l with
  | LSilent => dws
  | LLoad aq _ base tvs _ => loadPostRun dws aq base (tvs.map Prod.fst)
  | LStore rl base data _ _ => storePostRun dws rl base data.length (σ.wglog.length + 1)
  | LRmw aq rl base tvs data _ _ =>
      storePostRun (loadPostRun dws aq base (tvs.map Prod.fst)) rl base data.length
        (σ.wglog.length + 1)
  | LFence pr pw sr sw => fencePost dws pr pw sr sw
  | LDev => dws
  | LRegW rd srcs => regwPost dws rd (srcsView dws srcs)
  | LCtrl srcs => ctrlPost dws (srcsView dws srcs)
  | LInstr => instrPost dws
  | LExLoad aq base tvs _ => loadPostRun dws aq base (tvs.map Prod.fst)
  | LExStore rl base data _ _ => storePostRun dws rl base data.length (σ.wglog.length + 1)
  | LIFetch .. => dws

def edlabLog (σ : WGState) (l : Wlabel) (k : WmClass) : List Wmsg :=
  match l with
  | LStore _ base data _ _ => σ.wglog ++ [⟨base, data, some nDisk, k⟩]
  | LRmw _ _ base _ data _ _ => σ.wglog ++ [⟨base, data, some nDisk, k⟩]
  | LExStore _ base data _ _ => σ.wglog ++ [⟨base, data, some nDisk, k⟩]
  | LSilent | LLoad .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExLoad ..
  | LIFetch .. => σ.wglog

def edlabApply (σ : WGState) (l : Wlabel) (k : WmClass) (d' : DevStates) : WGState :=
  { σ with wglog := edlabLog σ l k, wgdev := d' }

/-! ## 4. `elabApply` IS the language's named σ-updater -/

theorem elabApplySilent (σ : WGState) (c : CPU) (k : WmClass) :
    elabApply σ c LSilent k none none none σ.wgdev = σ := rfl

theorem elabApplyDev (σ : WGState) (c : CPU) (k : WmClass) (d' : DevStates) :
    elabApply σ c LSilent k none none none d' = ewgDev σ d' := rfl

theorem elabApplyLdev (σ : WGState) (c : CPU) (k : WmClass) (d' : DevStates) :
    elabApply σ c LDev k none none none d' = ewgDev σ d' := rfl

theorem elabApplyLdevReg (σ : WGState) (c : CPU) (k : WmClass) (rs' : RegFile) :
    elabApply σ c LDev k (some rs') none none σ.wgdev = ewgReg σ c rs' := rfl

theorem elabApplyReg (σ : WGState) (c : CPU) (k : WmClass) (rs' : RegFile) :
    elabApply σ c LSilent k (some rs') none none σ.wgdev = ewgReg σ c rs' := rfl

theorem elabApplyLoad (σ : WGState) (c : CPU) (k : WmClass) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    elabApply σ c (LLoad aq lat base tvs []) k none none none σ.wgdev
      = ewgWs σ c (loadPostRun (σ.wgws c) aq base (tvs.map Prod.fst)) := rfl

theorem elabApplyFence (σ : WGState) (c : CPU) (k : WmClass) (pr pw sr sw : Bool) :
    elabApply σ c (LFence pr pw sr sw) k none none none σ.wgdev
      = ewgWs σ c (fencePost (σ.wgws c) pr pw sr sw) := rfl

theorem elabApplyStore (σ : WGState) (c : CPU) (k : WmClass) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    elabApply σ c (LStore rl base data asrc vsrc) k none none none σ.wgdev
      = ewgStore σ c
          (storePostRunD (σ.wgws c) rl (srcsView (σ.wgws c) asrc) (srcsView (σ.wgws c) vsrc)
             base data.length (σ.wglog.length + 1))
          (σ.wglog ++ [⟨base, data, some c.val, k⟩]) := rfl

theorem elabApplyExload (σ : WGState) (c : CPU) (k : WmClass) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) :
    elabApply σ c (LExLoad aq base tvs asrc) k none none none σ.wgdev
      = ewgWs σ c (exloadPostRunD (σ.wgws c) aq (srcsView (σ.wgws c) asrc) base
          (tvs.map Prod.fst)) := rfl

theorem elabApplyExstore (σ : WGState) (c : CPU) (k : WmClass) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    elabApply σ c (LExStore rl base data asrc vsrc) k none none none σ.wgdev
      = ewgStore σ c
          (storePostRunD (σ.wgws c) rl (srcsView (σ.wgws c) asrc) (srcsView (σ.wgws c) vsrc)
             base data.length (σ.wglog.length + 1))
          (σ.wglog ++ [⟨base, data, some c.val, k⟩]) := rfl

/-- O2 (deviation 2, Lean-only): the fetch's σ-shape is the identity. -/
theorem elabApplyFetch (σ : WGState) (c : CPU) (k : WmClass) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    elabApply σ c (LIFetch base tvs) k none none none σ.wgdev = σ := rfl

/-- D3-2: the register write, all three kinds at once. -/
theorem elabApplyRw (σ : WGState) (c : CPU) (k : WmClass) (rs' : RegFile) (w : ErwKind) :
    elabApply σ c (erwLabel w) k (some rs') none none σ.wgdev = ewgRw σ c rs' w := by
  cases w <;> rfl

/-- ... the announce AND the boundary. -/
theorem elabApplyInstr (σ : WGState) (c : CPU) (k : WmClass) (v : Ibch) :
    elabApply σ c LInstr k none (some v) none σ.wgdev = ewgIbws σ c v (instrPost (σ.wgws c)) :=
  rfl

/-- DEC-7: the read-set accumulation. -/
theorem elabApplyIb (σ : WGState) (c : CPU) (k : WmClass) (v : Ibch) :
    elabApply σ c LSilent k none (some v) none σ.wgdev = ewgIb σ c v := rfl

/-- The barrier arm (deviations (D2) and 4: Stage B's `ewgBar`). -/
theorem elabApplyBarrier (σ : WGState) (c : CPU) (k : WmClass) (b : barrier_kind) :
    elabApply σ c (ebarLabel b) k none none (some b) σ.wgdev
      = ewgBar σ c (efenceApply (σ.wgws c) (ebarNow b)) (itvPost (σ.wgws c) (σ.wgitv c) b) := by
  cases b <;> first
    | rfl
    | simp only [elabApply, elabWs, ebarLabel, ebarNow, efenceApply, fencePostId, ewgBar]

theorem edlabApplySilent (σ : WGState) (k : WmClass) : edlabApply σ LSilent k σ.wgdev = σ := rfl

theorem edlabApplyLdevId (σ : WGState) (k : WmClass) : edlabApply σ LDev k σ.wgdev = σ := rfl

theorem edlabApplyLoadId (σ : WGState) (k : WmClass) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) : edlabApply σ (LLoad aq lat base tvs []) k σ.wgdev = σ := rfl

theorem edlabApplyFenceId (σ : WGState) (k : WmClass) (pr pw sr sw : Bool) :
    edlabApply σ (LFence pr pw sr sw) k σ.wgdev = σ := rfl

theorem edlabApplyDev (σ : WGState) (k : WmClass) (d' : DevStates) :
    edlabApply σ LSilent k d' = ewgDev σ d' := rfl

theorem edlabApplyLdev (σ : WGState) (k : WmClass) (d' : DevStates) :
    edlabApply σ LDev k d' = ewgDev σ d' := rfl

theorem edlabApplyStore (σ : WGState) (k : WmClass) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) :
    edlabApply σ (LStore rl base data [] []) k σ.wgdev
      = ewgLog σ (σ.wglog ++ [⟨base, data, some nDisk, k⟩]) := rfl

/-! ### Label-shape helpers (Lean-only, deviation 8) -/

theorem erwLabelCases (w : ErwKind) :
    erwLabel w = LSilent ∨ (∃ rd srcs, erwLabel w = LRegW rd srcs) ∨
      (∃ srcs, erwLabel w = LCtrl srcs) := by
  cases w with
  | ERWnone => exact Or.inl rfl
  | ERWreg rd srcs => exact Or.inr (Or.inl ⟨rd, srcs, rfl⟩)
  | ERWctrl srcs => exact Or.inr (Or.inr ⟨srcs, rfl⟩)

theorem ebarLabelFence (b : barrier_kind) : ∃ pr pw sr sw, ebarLabel b = LFence pr pw sr sw := by
  unfold ebarLabel
  split
  · exact ⟨_, _, _, _, rfl⟩
  · exact ⟨_, _, _, _, rfl⟩

theorem elabOkErwLabel (σ : WGState) (c : CPU) (w : ErwKind) : elabOk σ c (erwLabel w) := by
  cases w <;> trivial

theorem elabOkEbarLabel (σ : WGState) (c : CPU) (b : barrier_kind) : elabOk σ c (ebarLabel b) := by
  obtain ⟨pr, pw, sr, sw, h⟩ := ebarLabelFence b
  rw [h]; trivial

/-! ## 5. THE FACTORIZATION THEOREMS -/

-- A silent node: the label is fixed, the σ-shape is `elabApply`'s at the given updates.
set_option hygiene false in
local macro "esil_case" : tactic =>
  `(tactic| (constructor;
             (rintro ⟨rfl, rfl⟩;
              exact ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, rfl⟩);
             (rintro ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩;
              exact ⟨rfl, rfl⟩)))

set_option hygiene false in
local macro "estuck_case" : tactic =>
  `(tactic| (constructor;
             (intro h; exact h.elim);
             (rintro ⟨_, _, _, _, _, _, _, _, h, _⟩; exact h.elim)))

theorem ecycleStepFactor (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' ↔
    ∃ (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
      (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
      (obar : Option barrier_kind),
      e' = .Sail gen c m' fn' ∧
      pstepNode c m (σ.wgregs c) fn (σ.wgib c) σ.wgdev l m' ors fn' d' oib obar ∧
      elabOk σ c l ∧
      σ' = elabApply σ c l (pclsEv (.PHart c m (σ.wgregs c) fn (σ.wgib c)) l (σ.wgws c))
             ors oib obar d' := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · match m with
    | .pure y =>
      -- THE BOUNDARY, the reset point
      constructor
      · rintro ⟨tick, rfl, rfl⟩
        exact ⟨_, _, _, _, _, _, _, rfl, ⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, rfl⟩
      · rintro ⟨_, _, _, _, _, _, _, rfl, ⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩
        exact ⟨tick, rfl, rfl⟩
    | .impure (.error _) k => estuck_case
    | .impure (.ok o) k =>
      cases o with
      | regRead r => esil_case
      | regWrite r v =>
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
            elabOkErwLabel _ _ _, (elabApplyRw _ _ _ _ _).symm⟩
        · rintro ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩
          exact ⟨rfl, elabApplyRw _ _ _ _ _⟩
      | memRead n va req =>
        dsimp only [ecycleStep, emonadStep, pstepNode, pnodeStep]
        cases hd : devAddr req.pa
        · simp only [Bool.false_eq_true, ↓reduceIte]
          constructor
          · rintro (⟨hif, w, tvs, hlen, hby, hok, rfl, rfl⟩ |
              ⟨hif, ⟨hlat, w, tvs, hlen, hby, hrd, rfl, rfl⟩ | ⟨hlat, w, tvs, hlen, hby, hrd, rfl, rfl⟩⟩)
            · exact ⟨_, _, _, _, _, _, _, rfl,
                Or.inl ⟨hif, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hok, rfl⟩
            · exact ⟨_, _, _, _, _, _, _, rfl,
                Or.inr ⟨hif, Or.inl ⟨hlat, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩,
                ⟨rfl, hrd⟩, rfl⟩
            · exact ⟨_, _, _, _, _, _, _, rfl,
                Or.inr ⟨hif, Or.inr ⟨hlat, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩,
                hrd, rfl⟩
          · rintro ⟨_, _, _, _, _, _, _, rfl,
              (⟨hif, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
               ⟨hif, ⟨hlat, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                 ⟨hlat, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩), hok, rfl⟩
            · exact Or.inl ⟨hif, w, tvs, hlen, hby, hok, rfl, rfl⟩
            · exact Or.inr ⟨hif, Or.inl ⟨hlat, w, tvs, hlen, hby, hok.2, rfl, rfl⟩⟩
            · exact Or.inr ⟨hif, Or.inr ⟨hlat, w, tvs, hlen, hby, hok, rfl, rfl⟩⟩
        · simp only [↓reduceIte]
          constructor
          · rintro ⟨w, d', hrd, rfl, rfl⟩
            exact ⟨_, _, _, _, _, _, _, rfl, ⟨w, hrd, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, rfl⟩
          · rintro ⟨_, _, _, _, d', _, _, rfl, ⟨w, hrd, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩
            exact ⟨w, d', hrd, rfl, rfl⟩
      | memWrite n va req =>
        dsimp only [ecycleStep, emonadStep, pstepNode, pnodeStep]
        cases hd : devAddr req.pa
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hv : req.value with _ | v
          · estuck_case
          · try dsimp only
            constructor
            · rintro ⟨hn, ⟨hlat, rfl, rfl⟩ | ⟨hlat, ⟨hex, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩⟩
              · exact ⟨_, _, _, _, _, _, _, rfl,
                  ⟨hn, Or.inl ⟨hlat, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, wbytesNonnil n v hn,
                  by rw [elabApplyStore, wbytesLength]; rfl⟩
              · exact ⟨_, _, _, _, _, _, _, rfl,
                  ⟨hn, Or.inr ⟨hlat, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩,
                  ⟨wbytesNonnil n v hn, by rw [wbytesLength]; exact hex⟩,
                  by rw [elabApplyExstore, wbytesLength]; rfl⟩
              · exact ⟨_, _, _, _, _, _, _, rfl,
                  ⟨hn, Or.inr ⟨hlat, Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩, trivial, rfl⟩
            · rintro ⟨_, _, _, _, _, _, _, rfl,
                ⟨hn, ⟨hlat, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                  ⟨hlat, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩,
                hok, rfl⟩
              · refine ⟨hn, Or.inl ⟨hlat, rfl, ?_⟩⟩
                rw [elabApplyStore, wbytesLength]; rfl
              · have hex := hok.2
                rw [wbytesLength] at hex
                refine ⟨hn, Or.inr ⟨hlat, Or.inl ⟨hex, rfl, ?_⟩⟩⟩
                rw [elabApplyExstore, wbytesLength]; rfl
              · exact ⟨hn, Or.inr ⟨hlat, Or.inr ⟨rfl, rfl⟩⟩⟩
        · simp only [↓reduceIte]
          rcases hv : req.value with _ | v
          · estuck_case
          · try dsimp only
            constructor
            · rintro ⟨d', hwr, rfl, rfl⟩
              exact ⟨_, _, _, _, _, _, _, rfl, ⟨hwr, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, rfl⟩
            · rintro ⟨_, _, _, _, d', _, _, rfl, ⟨hwr, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩
              exact ⟨d', hwr, rfl, rfl⟩
      | readRam => estuck_case
      | writeRam => estuck_case
      | barrier b =>
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
            elabOkEbarLabel _ _ _, (elabApplyBarrier _ _ _ _).symm⟩
        · rintro ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩
          exact ⟨rfl, elabApplyBarrier _ _ _ _⟩
      | cacheOp => esil_case
      | tlbi => esil_case
      | translationStart => esil_case
      | translationEnd => esil_case
      | takeException => esil_case
      | returnException => esil_case
      | cycleCount => esil_case
      | getCycleCount => esil_case
      | message => esil_case
      | choose p =>
        constructor
        · rintro ⟨ch, rfl, rfl⟩
          exact ⟨_, _, _, _, _, _, _, rfl, ⟨ch, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, rfl⟩
        · rintro ⟨_, _, _, _, _, _, _, rfl, ⟨ch, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩
          exact ⟨ch, rfl, rfl⟩
      | instrAnnounce n w => esil_case
      | branchAnnounce => esil_case
  · -- THE PARKED FENCE gates everything
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, rfl⟩
    · rintro ⟨_, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -, rfl⟩
      exact ⟨rfl, rfl⟩

/-- THE PLIC WIRE (deviation 5): at the wire primitive, the step IS `elabApply` of `LDev` at the
pin write. -/
theorem eplicStepFactor (gen : Nat) {dv : DevId} (c : CPU) (mm b : Bool) (σ σ' : WGState)
    (efs : List WExpr) :
    wdevOpStep gen dv (.setPin c mm b) σ () σ' efs ↔
    efs = [] ∧ σ' = elabApply σ c LDev .WCplain (some (pinSet (σ.wgregs c) mm b)) none none σ.wgdev := by
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    cases mm <;> rfl
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    cases mm <;> rfl

/-- ... and the program half holds of that pin write, at every hart state, when the PLIC PROGRAM
sits at it (deviation 5). -/
theorem pstepPlicPin (c : CPU) (mm b : Bool) (k : Unit → DevProg .plic) (rs : RegFile)
    (d : Efab) :
    d.efPlic = .op (.setPin c mm b) k →
    ∀ (m : SailM Unit) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
      pstepPlic c m rs fn ib d LDev m (some (pinSet rs mm b)) fn { d with efPlic := k () } none
        none :=
  fun hd _ _ _ => ⟨mm, b, k, hd, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two `WGState`s agreeing off the fabric and the task bookkeeping (Lean-only). -/
theorem wgEqDevRt (σ σ' : WGState) :
    σ'.wgregs = σ.wgregs → σ'.wgimg = σ.wgimg → σ'.wglog = σ.wglog → σ'.wgws = σ.wgws →
    σ'.wggen = σ.wggen → σ'.wgpow = σ.wgpow → σ'.wgib = σ.wgib → σ'.wgitv = σ.wgitv →
    σ' = { σ with wgdev := σ'.wgdev, wgrt := σ'.wgrt } := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  cases σ; cases σ'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

/-- A device step off a `setPin` node moves no register and no bits, and the fabric only at its
own device (Lean-only). -/
theorem wdevStepNoPin {gen : Nat} {dv : DevId} {tid : TaskId} {m m' : DevProg dv}
    {σ σ' : WGState} {efs : List WExpr} :
    wdevStep gen dv tid m σ m' σ' efs →
    (∀ (c : CPU) (mm b : Bool) (k : Unit → DevProg dv), m ≠ .op (.setPin c mm b) k) →
    σ'.wgregs = σ.wgregs ∧ σ'.wgib = σ.wgib ∧
      (σ'.wgdev = σ.wgdev ∨ ∃ s : DevSt dv, σ'.wgdev = σ.wgdev.set dv s) := by
  intro h hnp
  cases m with
  | pure a =>
    obtain ⟨-, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact ⟨rfl, rfl, Or.inl rfl⟩
    · split <;> exact ⟨rfl, rfl, Or.inl rfl⟩
  | op o k =>
    rcases h with ⟨v, -, h⟩ | ⟨-, -, rfl, -⟩
    · cases o with
      | step f =>
        obtain ⟨s', os, -, -, rfl, -⟩ := h
        exact ⟨rfl, rfl, Or.inr ⟨s', rfl⟩⟩
      | get => obtain ⟨-, rfl, -⟩ := h; exact ⟨rfl, rfl, Or.inl rfl⟩
      | choose => obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, Or.inl rfl⟩
      | dmaRead pa n => obtain ⟨-, rfl, -⟩ := h; exact ⟨rfl, rfl, Or.inl rfl⟩
      | dmaWrite f pa n w =>
        obtain ⟨-, ⟨s', -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := h
        · exact ⟨rfl, rfl, Or.inr ⟨s', rfl⟩⟩
        · exact ⟨rfl, rfl, Or.inl rfl⟩
      | sample src => obtain ⟨-, rfl, -⟩ := h; exact ⟨rfl, rfl, Or.inl rfl⟩
      | setPin c mm b => exact absurd rfl (hnp c mm b k)
      | fork t => obtain ⟨-, rfl, -⟩ := h; exact ⟨rfl, rfl, Or.inl rfl⟩
      | join j => obtain ⟨-, rfl, -⟩ := h; exact ⟨rfl, rfl, Or.inl rfl⟩
    · exact ⟨rfl, rfl, Or.inl rfl⟩

/-- A device program's NODE is plain (Lean-only): `pure`, or a `devOpPlain pin` primitive. -/
def devNodePlain {dv : DevId} (pin : Bool) (m : DevProg dv) : Prop :=
  match m with
  | .pure _ => True
  | .op o _ => devOpPlain pin o

theorem devPlainNode {dv : DevId} {pin : Bool} {m : DevProg dv} : DevPlain pin m → devNodePlain pin m
  | .pure _ => trivial
  | .op _ _ ho _ => ho

/-- `fdevStep` IS a root, non-forking device step of the language, σ-shape `ewgDev` (Lean-only). -/
theorem wdevOfFdevStep (gen : Nat) {dv : DevId} (m m' : DevProg dv) (σ : WGState)
    (ds' : DevStates) :
    fdevStep dv m σ.wgdev m' ds' → wdevStep gen dv rootTask m σ m' (ewgDev σ ds') [] := by
  intro h
  cases m with
  | pure a =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | op o k =>
    cases o with
    | step f =>
      rcases h with ⟨s', os, hf, hok, rfl, rfl⟩ | ⟨hb, rfl, rfl⟩
      · exact Or.inl ⟨(), rfl, s', os, hf, hok, rfl, rfl⟩
      · exact Or.inr ⟨hb, rfl, rfl, rfl⟩
    | get => obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
    | choose => obtain ⟨n, rfl, rfl⟩ := h; exact Or.inl ⟨n, rfl, rfl, rfl⟩
    | sample src => obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
    | dmaRead => exact h.elim
    | dmaWrite => exact h.elim
    | setPin => exact h.elim
    | fork => exact h.elim
    | join => exact h.elim

/-- ... and conversely at a plain, pin-free node (Lean-only). -/
theorem fdevStepOfWdev (gen : Nat) {dv : DevId} (m m' : DevProg dv) (σ σ' : WGState) :
    devNodePlain false m → wdevStep gen dv rootTask m σ m' σ' [] →
    fdevStep dv m σ.wgdev m' σ'.wgdev ∧ σ' = ewgDev σ σ'.wgdev := by
  intro hp h
  cases m with
  | pure a =>
    obtain ⟨-, ⟨-, rfl, rfl⟩ | ⟨hne, -, -⟩⟩ := h
    · exact ⟨⟨rfl, rfl⟩, rfl⟩
    · exact absurd rfl hne
  | op o k =>
    cases o with
    | step f =>
      rcases h with ⟨⟨⟩, rfl, s', os, hf, hok, rfl, -⟩ | ⟨hb, rfl, rfl, -⟩
      · exact ⟨Or.inl ⟨s', os, hf, hok, rfl, rfl⟩, rfl⟩
      · exact ⟨Or.inr ⟨hb, rfl, rfl⟩, rfl⟩
    | get =>
      rcases h with ⟨v, rfl, rfl, rfl, -⟩ | ⟨hb, -⟩
      · exact ⟨⟨rfl, rfl⟩, rfl⟩
      · exact hb.elim
    | choose =>
      rcases h with ⟨v, rfl, rfl, -⟩ | ⟨hb, -⟩
      · exact ⟨⟨v, rfl, rfl⟩, rfl⟩
      · exact hb.elim
    | sample src =>
      rcases h with ⟨v, rfl, rfl, rfl, -⟩ | ⟨hb, -⟩
      · exact ⟨⟨rfl, rfl⟩, rfl⟩
      · exact hb.elim
    | dmaRead => exact hp.elim
    | dmaWrite => exact hp.elim
    | setPin => exact absurd hp Bool.false_ne_true
    | fork => exact hp.elim
    | join => exact hp.elim

/-- THE DEVICE THREADS' FABRIC MOVES (Rocq `euart_step_factor`; deviation 5): at a plain node off
the wire write, a root device step IS `fdevStep`, σ-shape `edlabApply` of `LDev`. -/
theorem euartStepFactor (gen : Nat) {dv : DevId} (m m' : DevProg dv) (σ σ' : WGState) :
    devNodePlain false m →
    (wdevStep gen dv rootTask m σ m' σ' [] ↔
      ∃ d' : DevStates, fdevStep dv m σ.wgdev m' d' ∧ σ' = edlabApply σ LDev .WCplain d') := by
  intro hp
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := fdevStepOfWdev gen m m' σ σ' hp h
    exact ⟨_, h1, h2⟩
  · rintro ⟨d', h, rfl⟩
    exact wdevOfFdevStep gen m m' σ d' h

/-- A plain program stays plain across a device step, if the body it restarts at is plain
(Lean-only). -/
theorem devPlainStep {dv : DevId} {pin : Bool} {gen : Nat} {tid : TaskId} {m m' : DevProg dv}
    {σ σ' : WGState} {efs : List WExpr} :
    DevPlain pin (devSig dv).body → DevPlain pin m → wdevStep gen dv tid m σ m' σ' efs →
    DevPlain pin m' := by
  intro hb hm h
  cases hm with
  | pure a =>
    obtain ⟨-, ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩⟩ := h
    · exact hb
    · exact .pure _
  | op o k ho hk =>
    rcases h with ⟨v, rfl, -⟩ | ⟨-, rfl, -, -⟩
    · exact hk v
    · exact .op o k ho hk

theorem devPlainBind {S T α β : Type} {pin : Bool} {m : DevM S T α} {f : α → DevM S T β} :
    DevPlain pin m → (∀ a, DevPlain pin (f a)) → DevPlain pin (m >>= f) := by
  intro hm hf
  induction hm with
  | pure a => exact hf a
  | op o k ho _ ih => exact .op o _ ho ih

theorem devPlainLift {S T : Type} {pin : Bool} (o : DevOp S T) :
    devOpPlain pin o → DevPlain pin (DevM.lift o) :=
  fun h => .op o _ h (fun v => .pure v)

theorem devPlainChooseLt {S T : Type} {pin : Bool} (n : Nat) :
    DevPlain pin (DevM.chooseLt n : DevM S T Nat) :=
  devPlainBind (devPlainLift .choose trivial) (fun _ => .pure _)

/-- THE BOARD'S UART BODY IS PLAIN AND PIN-FREE (Lean-only, deviation 5). -/
theorem uartBodyPlain (i : UartId) : DevPlain false (devSig (.uart i)).body := by
  show DevPlain false (Uart.body i)
  unfold Uart.body
  refine devPlainBind (devPlainChooseLt 3) (fun k => ?_)
  split
  · exact devPlainLift _ trivial
  · split
    · exact devPlainBind (devPlainBind (devPlainLift .choose trivial) (fun _ => .pure _))
        (fun _ => devPlainLift _ trivial)
    · exact .pure _

/-- THE BOARD'S PLIC BODY IS PLAIN (its one non-plain-for-`false` node is the wire write). -/
theorem plicBodyPlain : DevPlain true (devSig .plic).body := by
  show DevPlain true Plic.body
  unfold Plic.body
  refine devPlainBind (devPlainChooseLt 2) (fun k => ?_)
  split
  · refine devPlainBind (devPlainChooseLt _) (fun src => ?_)
    refine devPlainBind (devPlainLift (.sample src) trivial) (fun lvl => ?_)
    split
    · exact devPlainLift _ trivial
    · exact .pure _
  · refine devPlainBind (devPlainChooseLt _) (fun c => ?_)
    refine devPlainBind (devPlainBind (devPlainLift .choose trivial) (fun _ => .pure _))
      (fun mm => ?_)
    refine devPlainBind (devPlainLift .get trivial) (fun p => ?_)
    exact devPlainLift _ rfl

/-- THE DISK THREAD (M5), arm for arm. -/
theorem ediskStepFactor (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState)
    (e' : EExpr) (σ' : WGState) :
    ediskStep gen dp dws σ e' σ' ↔
    ∃ (l : Wlabel) (dp' : Option (DM Dres)) (d' : DevStates),
      e' = .EDisk gen dp' (edlabWs σ dws l) ∧
      pdiskProg dp σ.wgdev l dp' d' ∧
      edlabOk σ dws l ∧
      σ' = edlabApply σ l (pclsEv (.PDisk dp) l dws) d' := by
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨pa, n, aq, k, tvs, rfl, hlen, hrd, rfl, rfl⟩ |
      ⟨pa, bs, k, rfl, hne, rfl, rfl⟩ | ⟨k, rfl, rfl, rfl⟩ | ⟨delta, rfl, rfl, rfl⟩ |
      ⟨prog', rfl, hch, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact ⟨LDev, _, _, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩, trivial, rfl⟩
    · exact ⟨LLoad aq false (paZ pa) tvs [], _, _, rfl,
        Or.inr (Or.inl ⟨pa, n, aq, k, tvs, rfl, hlen, rfl, rfl, rfl⟩), ⟨rfl, hrd⟩, rfl⟩
    · exact ⟨LStore false (paZ pa) bs [] [], _, _, rfl,
        Or.inr (Or.inr (Or.inl ⟨pa, bs, k, rfl, hne, rfl, rfl, rfl⟩)), ⟨rfl, rfl, hne⟩, rfl⟩
    · exact ⟨LFence true true true true, _, _, rfl,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨k, rfl, rfl, rfl, rfl⟩))), trivial, rfl⟩
    · exact ⟨LDev, none, _, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨delta, rfl, rfl, rfl, rfl⟩)))), trivial, rfl⟩
    · exact ⟨LSilent, _, _, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨prog', rfl, hch, rfl, rfl, rfl⟩))))),
        trivial, rfl⟩
    · exact ⟨LSilent, none, _, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))))), trivial, rfl⟩
  · rintro ⟨l, dp', d', rfl,
      (⟨rfl, rfl, rfl, rfl⟩ | ⟨pa, n, aq, k, tvs, rfl, hlen, rfl, rfl, rfl⟩ |
       ⟨pa, bs, k, rfl, hne, rfl, rfl, rfl⟩ | ⟨k, rfl, rfl, rfl, rfl⟩ |
       ⟨delta, rfl, rfl, rfl, rfl⟩ | ⟨prog', rfl, hch, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩),
      hok, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨pa, n, aq, k, tvs, rfl, hlen, hok.2, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨pa, bs, k, rfl, hne, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨delta, rfl, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨prog', rfl, hch, rfl, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))

/-- The disk relation at the `pstepDisk` shape (at any fabric over σ's device states). -/
theorem ediskStepPstepDisk (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState)
    (e' : EExpr) (σ' : WGState) (F : Efab) :
    F.efDev = σ.wgdev →
    ediskStep gen dp dws σ e' σ' →
    ∃ (l : Wlabel) (dp' : Option (DM Dres)) (d' : DevStates),
      e' = .EDisk gen dp' (edlabWs σ dws l) ∧
      pstepDisk dp F l dp' { F with efDev := d' } ∧
      edlabOk σ dws l ∧
      σ' = edlabApply σ l (pclsEv (.PDisk dp) l dws) d' := by
  intro hF h
  obtain ⟨l, dp', d', he, hd, hok, hs⟩ := (ediskStepFactor gen dp dws σ e' σ').1 h
  exact ⟨l, dp', d', he, Or.inl ⟨by rw [hF]; exact hd, rfl⟩, hok, hs⟩

/-- A UART's moves at the `pstepDisk` shape (deviation 5). -/
theorem euartStepPstepDisk (gen : Nat) (i : UartId) (F : Efab) (m' : DevProg (.uart i))
    (dp : Option (DM Dres)) (dws : Wstate) (σ σ' : WGState) :
    F.efDev = σ.wgdev → devNodePlain false (efU F i) →
    wdevStep gen (.uart i) rootTask (efU F i) σ m' σ' [] →
    ∃ d' : DevStates,
      pstepDisk dp F LDev dp (efUset { F with efDev := d' } i m') ∧ edlabWs σ dws LDev = dws ∧
      edlabOk σ dws LDev ∧ σ' = edlabApply σ LDev (pclsEv (.PDisk dp) LDev dws) d' := by
  intro hF hp h
  obtain ⟨d', hf, hs⟩ := (euartStepFactor gen _ m' σ σ' hp).1 h
  rw [← hF] at hf
  exact ⟨d', Or.inr ⟨rfl, rfl, Or.inl ⟨i, m', d', hf, rfl⟩⟩, rfl, trivial, hs⟩

/-- The PLIC GATEWAY (every PLIC node but the wire write) at the `pstepDisk` shape (Lean-only,
deviation 5). -/
theorem eplicGateStepPstepDisk (gen : Nat) (F : Efab) (m' : DevProg .plic)
    (dp : Option (DM Dres)) (dws : Wstate) (σ σ' : WGState) :
    F.efDev = σ.wgdev → devNodePlain false F.efPlic →
    wdevStep gen .plic rootTask F.efPlic σ m' σ' [] →
    ∃ d' : DevStates,
      pstepDisk dp F LDev dp { F with efDev := d', efPlic := m' } ∧ edlabWs σ dws LDev = dws ∧
      edlabOk σ dws LDev ∧ σ' = edlabApply σ LDev (pclsEv (.PDisk dp) LDev dws) d' := by
  intro hF hp h
  obtain ⟨d', hf, hs⟩ := (euartStepFactor gen _ m' σ σ' hp).1 h
  rw [← hF] at hf
  exact ⟨d', Or.inr ⟨rfl, rfl, Or.inr ⟨m', d', hf, rfl⟩⟩, rfl, trivial, hs⟩

/-- THE HART ARMS AT THE `pstepHart` SHAPE (at any fabric over σ's device states). -/
theorem ecycleStepPstepHart (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) (F : Efab) :
    F.efDev = σ.wgdev →
    ecycleStep gen σ c m fn e' σ' →
    ∃ (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
      (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
      (obar : Option barrier_kind),
      e' = .Sail gen c m' fn' ∧
      pstepHart c m (σ.wgregs c) fn (σ.wgib c) F l m' ors fn' { F with efDev := d' } oib obar ∧
      elabOk σ c l ∧
      σ' = elabApply σ c l (pclsEv (.PHart c m (σ.wgregs c) fn (σ.wgib c)) l (σ.wgws c))
             ors oib obar d' := by
  intro hF h
  obtain ⟨l, m', ors, fn', d', oib, obar, he, hp, hok, hs⟩ :=
    (ecycleStepFactor gen σ c m fn e' σ').1 h
  exact ⟨l, m', ors, fn', d', oib, obar, he, Or.inl ⟨by rw [hF]; exact hp, rfl⟩, hok, hs⟩

/-- THE PLIC WIRE at the `pstepHart` shape (deviation 5: the PLIC program at a `setPin` node). -/
theorem eplicStepPstepHart (gen : Nat) (tid : TaskId) (c : CPU) (mm b : Bool)
    (k : Unit → DevProg .plic) (F : Efab) (m' : DevProg .plic) (σ σ' : WGState)
    (efs : List WExpr) :
    F.efPlic = .op (.setPin c mm b) k →
    wdevStep gen .plic tid F.efPlic σ m' σ' efs →
    m' = k () ∧ efs = [] ∧
      (∀ (m : SailM Unit) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
        pstepHart c m (σ.wgregs c) fn ib F LDev m (some (pinSet (σ.wgregs c) mm b)) fn
          { F with efPlic := k () } none none) ∧
      elabOk σ c LDev ∧
      σ' = elabApply σ c LDev .WCplain (some (pinSet (σ.wgregs c) mm b)) none none σ.wgdev := by
  intro hF h
  rw [hF] at h
  rcases h with ⟨v, rfl, h⟩ | ⟨hb, -, -, -⟩
  · obtain ⟨hefs, hs⟩ := (eplicStepFactor gen c mm b σ σ' efs).1 h
    exact ⟨rfl, hefs, fun m fn ib => Or.inr (pstepPlicPin c mm b k _ F hF m fn ib), trivial, hs⟩
  · exact hb.elim

/-! ## 6. Two properties of the program half alone -/

/-- Equal value lists have equal lengths (Lean-only helper). -/
theorem lenOfSnd {tvs tvs' : List (Nat × BitVec 8)} (h : tvs'.map Prod.snd = tvs.map Prod.snd) :
    tvs'.length = tvs.length := by
  simpa using congrArg List.length h

/-- THE LABEL SHAPES of the program half (Lean-only, deviation 8). -/
theorem pnodeStepCases (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar →
    l = LSilent ∨ l = LInstr ∨ l = LDev ∨ (∃ w, l = erwLabel w) ∨ (∃ b, l = ebarLabel b) ∨
      (∃ base tvs, l = LIFetch base tvs) ∨ (∃ aq base tvs, l = LLoad aq false base tvs []) ∨
      (∃ aq base tvs asrc, l = LExLoad aq base tvs asrc) ∨
      (∃ rl base data asrc vsrc, l = LStore rl base data asrc vsrc) ∨
      (∃ rl base data asrc vsrc, l = LExStore rl base data asrc vsrc) := by
  intro h
  match m, h with
  | .pure _, h => obtain ⟨_, rfl, _⟩ := h; exact Or.inr (Or.inl rfl)
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | regWrite r v => obtain ⟨rfl, _⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, rfl, _⟩ := h; exact Or.inr (Or.inr (Or.inl rfl))
      · rcases h with ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨_, _, _, _, rfl⟩)))))))
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, rfl, _⟩ := h; exact Or.inr (Or.inr (Or.inl rfl))
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨_, rfl, _⟩ | ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨_, _, _, _, _, rfl⟩))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨_, _, _, _, _, rfl⟩))))))))
          · exact Or.inl rfl
        · exact h.elim
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | barrier b => obtain ⟨rfl, _⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))))
    | cacheOp => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | tlbi => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | translationStart => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | translationEnd => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | takeException => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | returnException => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | cycleCount => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | getCycleCount => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | message => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl
    | choose p => obtain ⟨_, rfl, _⟩ := h; exact Or.inl rfl
    | instrAnnounce n w => obtain ⟨rfl, _⟩ := h; exact Or.inr (Or.inl rfl)
    | branchAnnounce => obtain ⟨rfl, _⟩ := h; exact Or.inl rfl

theorem pnodeStepLatFree (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (aq : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    ¬ pnodeStep m rs ib d (LLoad aq true base tvs []) m' ors fn' d' oib obar := by
  intro h
  rcases pnodeStepCases _ _ _ _ _ _ _ _ _ _ _ h with h | h | h | ⟨w, h⟩ | ⟨b, h⟩ |
    ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  all_goals first
    | (cases h; done)
    | (rcases erwLabelCases w with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> rw [h'] at h <;> cases h)
    | (obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b; rw [h'] at h; cases h)

theorem pstepNodeLatFree (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    ¬ pstepNode cpu m rs fn ib d (LLoad aq true base tvs []) m' ors fn' d' oib obar := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · exact pnodeStepLatFree m rs ib d aq base tvs m' ors fn' d' oib obar
  · intro h; exact nomatch h.1

theorem pstepHartLatFree (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    ¬ pstepHart cpu m rs fn ib d (LLoad aq true base tvs []) m' ors fn' d' oib obar := by
  rintro (⟨h, -⟩ | ⟨_, _, _, _, h, _⟩)
  · exact pstepNodeLatFree cpu m rs fn ib _ aq base tvs m' ors fn' _ oib obar h
  · exact nomatch h

/-- The disk loads since M5 — but never with `lat = true`. -/
theorem pdiskProgLatFree (dp : Option (DM Dres)) (d : DevStates) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (dp' : Option (DM Dres)) (d' : DevStates) :
    ¬ pdiskProg dp d (LLoad aq true base tvs []) dp' d' := by
  rintro (⟨_, h, _⟩ | ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ | ⟨_, h, _⟩)
  all_goals (cases h; done)

theorem pstepDiskLatFree (dp : Option (DM Dres)) (d : Efab) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (dp' : Option (DM Dres)) (d' : Efab) :
    ¬ pstepDisk dp d (LLoad aq true base tvs []) dp' d' := by
  rintro (⟨h, -⟩ | ⟨_, h, _⟩)
  · exact pdiskProgLatFree dp _ aq base tvs dp' _ h
  · exact nomatch h

/-- ... and no disk arm ever emits an `LRmw`. -/
theorem pstepDiskNoRmw (dp : Option (DM Dres)) (d : Efab) (aq rl : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (dp' : Option (DM Dres)) (d' : Efab) :
    ¬ pstepDisk dp d (LRmw aq rl base tvs data asrc vsrc) dp' d' := by
  rintro (⟨(⟨_, h, _⟩ | ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ | ⟨_, h, _⟩), -⟩ | ⟨_, h, _⟩) <;> exact nomatch h

/-- THE TIMESTAMP-OBLIVIOUSNESS of the disk's own load. -/
theorem pdiskProgTsLoad (dp : Option (DM Dres)) (d : DevStates) (aq : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (dp' : Option (DM Dres)) (d' : DevStates) :
    pdiskProg dp d (LLoad aq false base tvs []) dp' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pdiskProg dp d (LLoad aq false base tvs' []) dp' d' := by
  rintro (⟨_, h, _⟩ | ⟨pa, n, aq0, k, tvs0, hdp, hlen, h, hdp', hd⟩ | ⟨_, _, _, _, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ | ⟨_, h, _⟩) hts
  all_goals try (cases h; done)
  have hlen' : tvs'.length = tvs.length := lenOfSnd hts
  injection h with h1 _ h3 h4
  subst h1 h3 h4
  exact Or.inr (Or.inl ⟨pa, n, _, k, tvs', hdp, hlen'.trans hlen, rfl, by rw [hdp', hts], hd⟩)

theorem pstepDiskTsLoad (dp : Option (DM Dres)) (d : Efab) (aq : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (dp' : Option (DM Dres)) (d' : Efab) :
    pstepDisk dp d (LLoad aq false base tvs []) dp' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepDisk dp d (LLoad aq false base tvs' []) dp' d' := by
  rintro (⟨h, hd⟩ | ⟨_, h, _⟩) hts
  · exact Or.inl ⟨pdiskProgTsLoad dp _ aq base tvs tvs' dp' _ h hts, hd⟩
  · exact nomatch h

theorem pstepEvLatFree (p : Pexv6) (d : Efab) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (p' : Pexv6) (d' : Efab) :
    ¬ pstepEv p d (LLoad aq true base tvs []) p' d' := by
  cases p <;> cases p' <;> simp only [pstepEv, not_false_eq_true]
  · rintro ⟨_, _, _, _, _, _, h⟩
    exact pstepHartLatFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · exact pstepDiskLatFree _ _ _ _ _ _ _

/-- The read arm, inverted at a given label (Lean-only helper for §6–§7): the RAM-read
disjunction of `pnodeStep` at a non-device address. -/
theorem pnodeStepTsLoad (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (aq : Bool)
    (base : Int) (tvs tvs' : List (Nat × BitVec 8)) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep m rs ib d (LLoad aq false base tvs []) m' ors fn' d' oib obar →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pnodeStep m rs ib d (LLoad aq false base tvs' []) m' ors fn' d' oib obar := by
  intro h hts
  have hlen' : tvs'.length = tvs.length := lenOfSnd hts
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h ⊢
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rcases h with ⟨_, _, _, _, _, h, _⟩ | ⟨hif, ⟨hlat, w, tvs0, hlen, hby, h, hrest⟩ |
          ⟨_, _, _, _, _, h, _⟩⟩
        · exact nomatch h
        · injection h with h1 _ h3 h4
          subst h1 h3 h4
          refine Or.inr ⟨hif, Or.inl ⟨hlat, w, tvs', hlen'.trans hlen, ?_, rfl, hrest⟩⟩
          rw [hts]; exact hby
        · exact nomatch h
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨_, h, _⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩⟩ <;> exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce => exact nomatch h.1
    | branchAnnounce => exact nomatch h.1

/-- THE RMW SPLIT (S3): NO HART ARM EMITS THE FUSED LABEL. -/
theorem pnodeStepNoRmw (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (aq rl : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    ¬ pnodeStep m rs ib d (LRmw aq rl base tvs data asrc vsrc) m' ors fn' d' oib obar := by
  intro h
  rcases pnodeStepCases _ _ _ _ _ _ _ _ _ _ _ h with h | h | h | ⟨w, h⟩ | ⟨b, h⟩ |
    ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  all_goals first
    | (cases h; done)
    | (rcases erwLabelCases w with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> rw [h'] at h <;> cases h)
    | (obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b; rw [h'] at h; cases h)

theorem pstepNodeTsLoad (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (aq : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepNode cpu m rs fn ib d (LLoad aq false base tvs []) m' ors fn' d' oib obar →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepNode cpu m rs fn ib d (LLoad aq false base tvs' []) m' ors fn' d' oib obar := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · exact pnodeStepTsLoad m rs ib d aq base tvs tvs' m' ors fn' d' oib obar
  · intro h; exact nomatch h.1

theorem pstepHartNoRmw (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (aq rl : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    ¬ pstepHart cpu m rs fn ib d (LRmw aq rl base tvs data asrc vsrc) m' ors fn' d' oib obar := by
  rintro (⟨h, -⟩ | ⟨_, _, _, _, h, _⟩)
  · rcases fn with _ | ⟨pr, pw, sr, sw⟩
    · exact pnodeStepNoRmw m rs ib _ aq rl base tvs data asrc vsrc m' ors fn' _ oib obar h
    · exact nomatch h.1
  · exact nomatch h

theorem pstepEvTsLoad (p : Pexv6) (d : Efab) (aq : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (p' : Pexv6) (d' : Efab) :
    pstepEv p d (LLoad aq false base tvs []) p' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepEv p d (LLoad aq false base tvs' []) p' d' := by
  cases p <;> cases p' <;> simp only [pstepEv, false_implies]
  · rintro ⟨rfl, ors, oib, obar, rfl, rfl, ⟨h, hd⟩ | ⟨_, _, _, _, h, _⟩⟩ hts
    · exact ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl ⟨pstepNodeTsLoad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ h hts, hd⟩⟩
    · exact nomatch h
  · exact pstepDiskTsLoad _ _ _ _ _ _ _ _

theorem pstepEvNoRmw (p : Pexv6) (d : Efab) (aq rl : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (p' : Pexv6)
    (d' : Efab) :
    ¬ pstepEv p d (LRmw aq rl base tvs data asrc vsrc) p' d' := by
  cases p <;> cases p' <;> simp only [pstepEv, not_false_eq_true]
  · rintro ⟨_, _, _, _, _, _, h⟩
    exact pstepHartNoRmw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · exact pstepDiskNoRmw _ _ _ _ _ _ _ _ _ _ _

theorem pstepEvTsRmw (p : Pexv6) (d : Efab) (aq rl : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (p' : Pexv6) (d' : Efab) :
    pstepEv p d (LRmw aq rl base tvs data asrc vsrc) p' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepEv p d (LRmw aq rl base tvs' data asrc vsrc) p' d' :=
  fun h => absurd h (pstepEvNoRmw p d aq rl base tvs data asrc vsrc p' d')

/-! ## 7. THE FABRIC MARKER IS SOUND (`WeakPromiseFact.pdevOk`) -/

-- The silent-arm pattern of `pnodeStepDevFree`.
set_option hygiene false in
local macro "edev_sil" h:ident : tactic =>
  `(tactic| (obtain ⟨hl, h1, h2, h3, rfl, h5, h6⟩ := $h;
             exact fun _ => ⟨rfl, fun _ => ⟨hl, h1, h2, h3, rfl, h5, h6⟩⟩))

theorem pnodeStepDevFree (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar → l ≠ LDev →
    d' = d ∧ ∀ d0, pnodeStep m rs ib d0 l m' ors fn' d0 oib obar := by
  intro h
  match m, h with
  | .pure _, h =>
    obtain ⟨tick, hl, h1, h2, h3, rfl, h5, h6⟩ := h
    exact fun _ => ⟨rfl, fun _ => ⟨tick, hl, h1, h2, h3, rfl, h5, h6⟩⟩
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r => edev_sil h
    | regWrite r v => edev_sil h
    | memRead n va req =>
      intro hne
      simp only [pnodeStep] at h ⊢
      split at h
      · obtain ⟨_, _, hl, _⟩ := h; exact absurd hl hne
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, fun d0 => ?_⟩
        · rcases h with ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ |
            ⟨_, ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩⟩ <;> rfl
        · rcases h with ⟨hif, w, tvs, hlen, hby, hl, h1, h2, h3, rfl, h5, h6⟩ |
            ⟨hif, ⟨hlat, w, tvs, hlen, hby, hl, h1, h2, h3, rfl, h5, h6⟩ |
              ⟨hlat, w, tvs, hlen, hby, hl, h1, h2, h3, rfl, h5, h6⟩⟩
          · exact Or.inl ⟨hif, w, tvs, hlen, hby, hl, h1, h2, h3, by trivial, h5, h6⟩
          · exact Or.inr ⟨hif, Or.inl ⟨hlat, w, tvs, hlen, hby, hl, h1, h2, h3, by trivial, h5, h6⟩⟩
          · exact Or.inr ⟨hif, Or.inr ⟨hlat, w, tvs, hlen, hby, hl, h1, h2, h3, by trivial, h5, h6⟩⟩
    | memWrite n va req =>
      intro hne
      simp only [pnodeStep] at h ⊢
      split at h
      · split at h
        · obtain ⟨_, hl, _⟩ := h; exact absurd hl hne
        · exact h.elim
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        split at h
        · rename_i v hv
          try simp only [hv]
          rcases h with ⟨hn, ⟨hlat, hl, h1, h2, h3, rfl, h5, h6⟩ |
            ⟨hlat, ⟨hl, h1, h2, h3, rfl, h5, h6⟩ | ⟨hl, h1, h2, h3, rfl, h5, h6⟩⟩⟩
          · exact ⟨rfl, fun _ => ⟨hn, Or.inl ⟨hlat, hl, h1, h2, h3, by trivial, h5, h6⟩⟩⟩
          · exact ⟨rfl, fun _ => ⟨hn, Or.inr ⟨hlat, Or.inl ⟨hl, h1, h2, h3, by trivial, h5, h6⟩⟩⟩⟩
          · exact ⟨rfl, fun _ => ⟨hn, Or.inr ⟨hlat, Or.inr ⟨hl, h1, h2, h3, by trivial, h5, h6⟩⟩⟩⟩
        · exact h.elim
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | barrier b => edev_sil h
    | cacheOp => edev_sil h
    | tlbi => edev_sil h
    | translationStart => edev_sil h
    | translationEnd => edev_sil h
    | takeException => edev_sil h
    | returnException => edev_sil h
    | cycleCount => edev_sil h
    | getCycleCount => edev_sil h
    | message => edev_sil h
    | choose p =>
      obtain ⟨ch, hl, h1, h2, h3, rfl, h5, h6⟩ := h
      exact fun _ => ⟨rfl, fun _ => ⟨ch, hl, h1, h2, h3, rfl, h5, h6⟩⟩
    | instrAnnounce n w => edev_sil h
    | branchAnnounce => edev_sil h

theorem pstepNodeDevFree (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepNode cpu m rs fn ib d l m' ors fn' d' oib obar → l ≠ LDev →
    d' = d ∧ ∀ d0, pstepNode cpu m rs fn ib d0 l m' ors fn' d0 oib obar := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · exact pnodeStepDevFree m rs ib d l m' ors fn' d' oib obar
  · intro h; edev_sil h

theorem pdiskProgDevFree (dp : Option (DM Dres)) (d : DevStates) (l : Wlabel)
    (dp' : Option (DM Dres)) (d' : DevStates) :
    pdiskProg dp d l dp' d' → l ≠ LDev → d' = d ∧ ∀ d0, pdiskProg dp d0 l dp' d0 := by
  rintro (⟨_, hl, _⟩ | ⟨pa, n, aq, k, tvs, hdp, hlen, hl, hdp', rfl⟩ |
    ⟨pa, bs, k, hdp, hbs, hl, hdp', rfl⟩ | ⟨k, hdp, hl, hdp', rfl⟩ | ⟨_, _, hl, _⟩ |
    ⟨prog', hdp, hch, hl, hdp', rfl⟩ | ⟨hdp, hl, hdp', rfl⟩) hne
  · exact absurd hl hne
  · exact ⟨rfl, fun _ => Or.inr (Or.inl ⟨pa, n, aq, k, tvs, hdp, hlen, hl, hdp', rfl⟩)⟩
  · exact ⟨rfl, fun _ => Or.inr (Or.inr (Or.inl ⟨pa, bs, k, hdp, hbs, hl, hdp', rfl⟩))⟩
  · exact ⟨rfl, fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hdp, hl, hdp', rfl⟩)))⟩
  · exact absurd hl hne
  · exact ⟨rfl, fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨prog', hdp, hch, hl, hdp', rfl⟩)))))⟩
  · exact ⟨rfl, fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hdp, hl, hdp', rfl⟩)))))⟩

theorem pstepDiskDevFree (dp : Option (DM Dres)) (d : Efab) (l : Wlabel)
    (dp' : Option (DM Dres)) (d' : Efab) :
    pstepDisk dp d l dp' d' → l ≠ LDev → d' = d ∧ ∀ d0, pstepDisk dp d0 l dp' d0 := by
  rintro (⟨h, hd⟩ | ⟨_, hl, _⟩) hne
  · obtain ⟨he, hall⟩ := pdiskProgDevFree dp _ l dp' _ h hne
    exact ⟨by rw [hd, he], fun d0 => Or.inl ⟨hall d0.efDev, rfl⟩⟩
  · exact absurd hl hne

theorem pdevEvOk : pdevOk pstepEv pdevEv := by
  intro p d l p' d' hs hm
  have hne : l ≠ LDev := by
    rintro rfl
    exact absurd hm (by simp [pdevEv])
  cases p <;> cases p' <;> simp only [pstepEv] at hs ⊢
  · obtain ⟨rfl, ors, oib, obar, rfl, rfl, ⟨hn, hd⟩ | ⟨_, _, _, _, hl, _⟩⟩ := hs
    · obtain ⟨he, hall⟩ := pstepNodeDevFree _ _ _ _ _ _ _ _ _ _ _ _ _ hn hne
      exact ⟨by rw [hd, he], fun d0 => ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl ⟨hall d0.efDev, rfl⟩⟩⟩
    · exact absurd hl hne
  · exact pstepDiskDevFree _ _ _ _ _ hs hne

/-- D3-2: THE LOAD-DEPENDENCY-FREEDOM OF THE INSTANCE (deviation D-8 of the Rocq tree). -/
theorem pnodeStepLdepfree (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar → lbLdepfree l := by
  intro h
  rcases pnodeStepCases _ _ _ _ _ _ _ _ _ _ _ h with rfl | rfl | rfl | ⟨w, rfl⟩ | ⟨b, rfl⟩ |
    ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
  all_goals first
    | trivial
    | rfl
    | (rcases erwLabelCases w with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> rw [h'] <;> trivial)
    | (obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b; rw [h']; trivial)

theorem pstepNodeLdepfree (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepNode cpu m rs fn ib d l m' ors fn' d' oib obar → lbLdepfree l := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · exact pnodeStepLdepfree m rs ib d l m' ors fn' d' oib obar
  · rintro ⟨rfl, _⟩; trivial

theorem pstepPlicLdepfree (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar → lbLdepfree l := by
  rintro ⟨_, _, _, _, rfl, _⟩; trivial

theorem pstepHartLdepfree (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar → lbLdepfree l := by
  rintro (⟨h, -⟩ | h)
  · exact pstepNodeLdepfree cpu m rs fn ib _ l m' ors fn' _ oib obar h
  · exact pstepPlicLdepfree cpu m rs fn ib d l m' ors fn' d' oib obar h

theorem pstepDiskDepfree (dp : Option (DM Dres)) (d : Efab) (l : Wlabel)
    (dp' : Option (DM Dres)) (d' : Efab) : pstepDisk dp d l dp' d' → lbDepfree l := by
  rintro (⟨(⟨_, rfl, _⟩ | ⟨_, _, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ |
    ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, rfl, _⟩), -⟩ | ⟨_, rfl, _⟩) <;>
    first | trivial | rfl | exact ⟨rfl, rfl⟩

theorem pstepEvLdepfree (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv p d l p' d' → lbLdepfree l := by
  cases p <;> cases p' <;> simp only [pstepEv, false_implies]
  · rintro ⟨_, _, _, _, _, _, h⟩
    exact pstepHartLdepfree _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · intro h
    exact lbDepfreeLdepfree _ (pstepDiskDepfree _ _ _ _ _ h)

/-- THE RMW SPLIT: the device program has no exclusive access at all. -/
theorem pstepDiskNoEx (dp : Option (DM Dres)) (d : Efab) (l : Wlabel)
    (dp' : Option (DM Dres)) (d' : Efab) : pstepDisk dp d l dp' d' → lbFused l := by
  rintro (⟨(⟨_, rfl, _⟩ | ⟨_, _, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ |
    ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, rfl, _⟩), -⟩ | ⟨_, rfl, _⟩) <;> trivial

/-- O2 (Lean-only, deviation 8): ... and never fetches. -/
theorem pstepDiskNoFetch (dp : Option (DM Dres)) (d : Efab) (base : Int)
    (tvs : List (Nat × BitVec 8)) (dp' : Option (DM Dres)) (d' : Efab) :
    ¬ pstepDisk dp d (LIFetch base tvs) dp' d' := by
  rintro (⟨(⟨_, h, _⟩ | ⟨_, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ | ⟨_, h, _⟩), -⟩ | ⟨_, h, _⟩) <;> exact nomatch h

/-! ### THE RMW SPLIT (S4): timestamp-obliviousness of the exclusive read -/

theorem pnodeStepTsExload (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (aq : Bool)
    (base : Int) (tvs tvs' : List (Nat × BitVec 8)) (asrc : List Dsrc) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d (LExLoad aq base tvs asrc) m' ors fn' d' oib obar →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pnodeStep m rs ib d (LExLoad aq base tvs' asrc) m' ors fn' d' oib obar := by
  intro h hts
  have hlen' : tvs'.length = tvs.length := lenOfSnd hts
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h ⊢
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rcases h with ⟨_, _, _, _, _, h, _⟩ | ⟨hif, ⟨_, _, _, _, _, h, _⟩ |
          ⟨hlat, w, tvs0, hlen, hby, h, hrest⟩⟩
        · exact nomatch h
        · exact nomatch h
        · injection h with h1 h2 h3 h4
          subst h1 h2 h3 h4
          refine Or.inr ⟨hif, Or.inr ⟨hlat, w, tvs', hlen'.trans hlen, ?_, rfl, hrest⟩⟩
          rw [hts]; exact hby
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨_, h, _⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩⟩ <;> exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce => exact nomatch h.1
    | branchAnnounce => exact nomatch h.1

theorem pstepNodeTsExload (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (aq : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (asrc : List Dsrc) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepNode cpu m rs fn ib d (LExLoad aq base tvs asrc) m' ors fn' d' oib obar →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepNode cpu m rs fn ib d (LExLoad aq base tvs' asrc) m' ors fn' d' oib obar := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · exact pnodeStepTsExload m rs ib d aq base tvs tvs' asrc m' ors fn' d' oib obar
  · intro h; exact nomatch h.1

theorem pstepDiskTsExload (dp : Option (DM Dres)) (d : Efab) (aq : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (asrc : List Dsrc) (dp' : Option (DM Dres))
    (d' : Efab) :
    pstepDisk dp d (LExLoad aq base tvs asrc) dp' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepDisk dp d (LExLoad aq base tvs' asrc) dp' d' :=
  fun h => (pstepDiskNoEx _ _ _ _ _ h).elim

theorem pstepEvTsExload (p : Pexv6) (d : Efab) (aq : Bool) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (asrc : List Dsrc) (p' : Pexv6) (d' : Efab) :
    pstepEv p d (LExLoad aq base tvs asrc) p' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepEv p d (LExLoad aq base tvs' asrc) p' d' := by
  cases p <;> cases p' <;> simp only [pstepEv, false_implies]
  · rintro ⟨rfl, ors, oib, obar, rfl, rfl, ⟨h, hd⟩ | ⟨_, _, _, _, h, _⟩⟩ hts
    · exact ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl ⟨pstepNodeTsExload _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ h hts, hd⟩⟩
    · exact nomatch h
  · exact pstepDiskTsExload _ _ _ _ _ _ _ _ _

/-! ### O2 (Lean-only, deviation 8): timestamp-obliviousness of the fetch -/

theorem pnodeStepTsIfetch (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (base : Int) (tvs tvs' : List (Nat × BitVec 8)) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep m rs ib d (LIFetch base tvs) m' ors fn' d' oib obar →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pnodeStep m rs ib d (LIFetch base tvs') m' ors fn' d' oib obar := by
  intro h hts
  have hlen' : tvs'.length = tvs.length := lenOfSnd hts
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h ⊢
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rcases h with ⟨hif, w, tvs0, hlen, hby, h, hrest⟩ | ⟨_, ⟨_, _, _, _, _, h, _⟩ |
          ⟨_, _, _, _, _, h, _⟩⟩
        · injection h with h1 h2
          subst h1 h2
          refine Or.inl ⟨hif, w, tvs', hlen'.trans hlen, ?_, rfl, hrest⟩
          rw [hts]; exact hby
        · exact nomatch h
        · exact nomatch h
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨_, h, _⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩⟩ <;> exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce => exact nomatch h.1
    | branchAnnounce => exact nomatch h.1

theorem pstepNodeTsIfetch (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepNode cpu m rs fn ib d (LIFetch base tvs) m' ors fn' d' oib obar →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepNode cpu m rs fn ib d (LIFetch base tvs') m' ors fn' d' oib obar := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · exact pnodeStepTsIfetch m rs ib d base tvs tvs' m' ors fn' d' oib obar
  · intro h; exact nomatch h.1

theorem pstepDiskTsIfetch (dp : Option (DM Dres)) (d : Efab) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (dp' : Option (DM Dres)) (d' : Efab) :
    pstepDisk dp d (LIFetch base tvs) dp' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepDisk dp d (LIFetch base tvs') dp' d' :=
  fun h => absurd h (pstepDiskNoFetch dp d base tvs dp' d')

theorem pstepEvTsIfetch (p : Pexv6) (d : Efab) (base : Int)
    (tvs tvs' : List (Nat × BitVec 8)) (p' : Pexv6) (d' : Efab) :
    pstepEv p d (LIFetch base tvs) p' d' →
    tvs'.map Prod.snd = tvs.map Prod.snd →
    pstepEv p d (LIFetch base tvs') p' d' := by
  cases p <;> cases p' <;> simp only [pstepEv, false_implies]
  · rintro ⟨rfl, ors, oib, obar, rfl, rfl, ⟨h, hd⟩ | ⟨_, _, _, _, h, _⟩⟩ hts
    · exact ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl ⟨pstepNodeTsIfetch _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ h hts, hd⟩⟩
    · exact nomatch h
  · exact pstepDiskTsIfetch _ _ _ _ _ _ _

/-! ### THE RE-FUSION'S CLASS PREMISE (`WeakRefuse.pclsFusable`) -/

theorem pnodeStepExstoreExcl (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (ws : Wstate) :
    pnodeStep m rs ib d (LExStore rl base data asrc vsrc) m' ors fn' d' oib obar →
    pnodeWclass m ws = .WCexcl := by
  intro h
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rcases h with ⟨_, _, _, _, _, h, _⟩ | ⟨_, ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩⟩ <;>
          exact nomatch h
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨_, h, _⟩ | ⟨ht, ⟨_, _⟩ | ⟨h, _⟩⟩⟩
          · exact nomatch h
          · simp only [pnodeWclass, wmClassOf, ht, ↓reduceIte]
          · exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce => exact nomatch h.1
    | branchAnnounce => exact nomatch h.1

theorem pstepNodeExstoreExcl (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : DevStates) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (ws : Wstate) :
    pstepNode cpu m rs fn ib d (LExStore rl base data asrc vsrc) m' ors fn' d' oib obar →
    pnodeWclass m ws = .WCexcl := by
  rcases fn with _ | ⟨pr, pw, sr, sw⟩
  · exact pnodeStepExstoreExcl m rs ib d rl base data asrc vsrc m' ors fn' d' oib obar ws
  · intro h; exact nomatch h.1

theorem pstepHartExstoreExcl (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (ws : Wstate) :
    pstepHart cpu m rs fn ib d (LExStore rl base data asrc vsrc) m' ors fn' d' oib obar →
    pnodeWclass m ws = .WCexcl := by
  rintro (⟨h, -⟩ | ⟨_, _, _, _, h, _⟩)
  · exact pstepNodeExstoreExcl cpu m rs fn ib _ rl base data asrc vsrc m' ors fn' _ oib obar ws h
  · exact nomatch h

theorem pclsEvFusable : pclsFusable pstepEv pclsEv := by
  intro p d rl base data asrc vsrc p' d' aq tvs wF wS hs _
  cases p <;> cases p' <;> simp only [pstepEv] at hs
  · obtain ⟨_, _, _, _, _, _, h⟩ := hs
    exact (pstepHartExstoreExcl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wS h).symm
  · exact (pstepDiskNoEx _ _ _ _ _ hs).elim

/-! ## 9. THE INSTANCE T2 -/

theorem t2Ev (img : Image) (d0 : Efab) (ps : List Pexv6) (c : Wpcfg Pexv6 Efab) :
    rtc (wpPfRun pstepEv pclsEv) (wpInit img d0 ps) c →
    ∃ E, execWf E ∧ exImg E = img ∧ exLog E = c.pcLog :=
  t2Bridge pstepEv pclsEv img d0 ps c pclsEvErasable pclsEvFusable

end Weak
