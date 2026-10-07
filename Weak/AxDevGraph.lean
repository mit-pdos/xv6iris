/-
Weak: **devices (UARTs, PLIC, virtio disk) as GRAPH AGENTS with real state** (K2 / C11, design
and first slice).  Pure (no Iris).

Rocq: `iris/AxDevGraph.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Nothing existing is changed: `Gdexec` / `rvwmoCatConsistent` / `AxOpsem` are used as they are;
the device layer is a WRAPPER record.  In `AxOpsem` devices are ERASED (every opax constructor
quantifies the device state existentially — the `LDev` "oracle": at an MMIO node `reducible`
holds iff SOME device state serves the access, and an MMIO read value is free); the graph has
no device event.  RVWMO has no I/O events and `LFence` only r/w bits, so every I/O-ordering
fact here is a DECLARED hardware clause (`dcPo`, `dcIo`), litmus-falsifiable and xv6-free.

THE MODEL (§1–§2).  `Dlbl`: device events — hart-issued MMIO read (with the value the hart
RECEIVED) / write and the PLIC wire delivery; device-agent-issued UART transmit / receive, the
PLIC gateway latch, the disk's START and COMMIT.  DMA is NOT a `Dlbl`: it stays RAM events of
the device agent's RAM row.  `AxDevGraph.dstep d l`: ONE transaction of the SC device model;
reads / the wire are defined only if the device answers the recorded value.  `dreplay`: the
device STATE INTERPRETATION.  `GdexecDev` = the RAM graph, per-agent device rows (each item with
its INSERTION position into the agent's RAM row), the device order `gvDord` (one total order:
the fabric is a single serialization point) and the device agent `gvDev`.  `DevConsistent`:
`dcNodup`/`dcMem` (dord enumerates exactly the device events), `dcPo` (STRONGLY-ORDERED I/O),
`dcIns` (insertion positions monotone, in range), `dcKind` (device-side labels exactly on
`gvDev`), `dcReplay` (dord replays from power-on), `dcIo` (RAM→fence→I/O→dord→I/O→fence→RAM ⇒
gmo).  `gdvConsistent` := `rvwmoCatConsistent ∧ DevConsistent`.

RESULTS (§3–§6).  `dordProj`: dord restricted to agent `i` IS `i`'s device row in order;
`drowSublistDord`.  `dreplayUartAcc` / `gdvUartTrace`: under the UART discipline and no tx-FIFO
overflow the console's accepted trace after the replay is EXACTLY the THR bytes in device order,
and each agent's THR bytes, in ITS program order, are a subsequence of it.  NON-VACUITY: `witGV`
(2 harts each write a console byte, the device agent transmits one) satisfies `gdvConsistent`
and every premise of `gdvUartTrace` (`witUartSat`); `witBadInconsistent`: the same rows in the
other device order are NOT consistent — the device state is load-bearing (caveat: RAM rows are
empty, `dcIo` is vacuous there).  `AxDevGraph.devReducible` (TARGET SHAPE): opax `reducibleGd` ∧
at an MMIO node the step exists at EVERY `devFrontier` state (`devFrontierFinal`: never empty).
Proved for the UART (`uartDevReducibleWrite`/`Read`); not trivial (`plicByteWriteStuck`).

§D (the advisor's main risk: DMA rows are foreign writes into kernel buffers; DMA must be
owned-write-shaped, the token travelling on the QueueNotify / COMMIT annotations) and the
RESIDUALS (a)–(f) of the Rocq header are design notes; they carry over unchanged.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  `Arch.pa` ↦ `PAddr`; `N` ↦ `Nat`; `bv n` ↦
   `BitVec n`; `l !! k` ↦ `l[k]?`; `omap` ↦ `List.filterMap`; `f <$> l` ↦ `List.map`;
   `default [] o` ↦ `o.getD []`; `is_Some o` ↦ `o.isSome = true`; `StronglySorted` ↦
   `List.Pairwise`; `sublist_of` ↦ `List.Sublist`; `seq a n` ↦ `List.range' a n` (`seq 0 n` ↦
   `List.range n`); `Forall P l` ↦ `∀ x ∈ l, P x`; `option_list` ↦ `Option.toList`; `filter` on
   a decidable `P` ↦ `List.filter (fun x => decide (P x))`; `dev_state` ↦ `DevStates`;
   `dev0_state` ↦ the Lean-only `AxDevGraph.dev0State` (= `OpaxWit.wtD0.efDev`).
   File-qualified (duplicated Rocq names): `AxDevGraph.dstep`, `AxDevGraph.devReducible`,
   `AxDevGraph.inUartOff`.
2. THE DEVICE MODEL is Lean's (`MachCSL/Dev/*`), not Rocq's `DevModel`:
   - TWO UARTs: `DUartTx`/`DUartRx` carry the port `UartId`; the step is `Uart.txPop` (Rocq
     `uart_tx_pop`; under LOOP the byte goes back into the port's receiver) and `Uart.accept`
     when the receive FIFO has room (Rocq `uart_rx_push`, `None` when full; Lean's `rxArm`
     refuses a byte silently, which needs no event).  The UART results are stated PER PORT `pt`:
     `uartOk pt`, `dlblThr pt`, `dstepUart pt`, `dreplayUartAcc pt`, `gdvUartTrace pt`,
     `dev0Uart pt`; Rocq's `uart_dlab`/`u_tx`/`u_out`/`uart_acc`/`uart_fifo_depth` ↦
     `Uart.dlab`/`.tx`/`.out`/`Uart.acc`/`Uart.fifoDepth` of `d.st (.uart pt)`.
   - "in the UART window" (`in_uart (uint pa)`) ↦ `devDecode pa = some (.uart pt, off)`; the THR
     is offset `0`.  `uartOk pt` restricts port `pt`'s window writes to 1-byte THR writes (as
     Rocq); `bv8Of n v` is `v.extractLsb' 0 8` at `n = 1` (the byte `Uart.writeN` stores; Rocq
     `v` itself).
   - THE WIRE: `DWire h mm b` delivers level `b` to hart `h`'s M (`mm`) or S context:
     `Plic.eip (d.st .plic) (ctx)` — exactly the PLIC program's wire arm (`Plic.body`'s
     `setPin`); Rocq `DWire h b` with `dev_seip d h` (S only).  `h : CPU` (Rocq `nat`).
   - THE LATCH: `DLatch src` = the PLIC gateway step of `Plic.body`: defined iff the source's
     level `devLevel d src` is high, then `Plic.latch`, which is TOTAL in Lean (a pending or
     claimed source is left unchanged); Rocq's `plic_latch` was `None` there.  This is a PURE
     function of `DevStates`; no Iris resource (`devFragAt .plic`/`plicInv`) is involved.
   - `DDiskCommit delta` takes `delta : VirtioState → VirtioState`.
   - MMIO: `devRead`/`devWrite` (Lean's UART answers 1/2/4/8-byte accesses, narrowed; the PLIC
     only 4-byte ones).
3. `AxDevGraph.devReducible` / `mmioStepAt`: the program half (`pstepProg`) is stated at the
   event instance's fabric `Efab` (`WeakEvInst` deviation 5), so `mmioStepAt F p` takes an
   `F : Efab` and the frontier clause reads `∀ F : Efab, devFrontier GV i F.efDev → mmioStepAt F
   p` (a hart's MMIO step reads and moves only `F.efDev`; Rocq quantified `d : dev_state`).
   `atMmio`'s requests are lean-sail records indexed by the va width (`va` bound too).  The UART
   MMIO step lemmas take the port window `devDecode req.pa = some (.uart pt, off)` and, for a
   write, `req.value = some v` (lean-sail write values are `Option`).
4. `dlblDevside`, `fullFenceAt`, `devIoCausal`, `DevConsistent` verbatim modulo 1.
5. Lean-only helpers (file-qualified): `AxDevGraph.dev0State`, `AxDevGraph.uartReadStable`,
   `AxDevGraph.uartWriteTotal`, `AxDevGraph.uartReadTotal`, `AxDevGraph.uartPostFrame`,
   `AxDevGraph.uartNe`, `AxDevGraph.filterMapCons`, `AxDevGraph.uartDecodeBounds`,
   `AxDevGraph.witLbls`.
6. Rocq's §7 `Print Assumptions` audit is not reproduced (the lint bans axioms tree-wide).

**Rocq → Lean name map.**  `dlbl` `Dlbl` (`DMmioR/DMmioW/DWire/DUartTx/DUartRx/DLatch/
DDiskStart/DDiskCommit`), `dlbl_devside` `dlblDevside`, `dstep` `AxDevGraph.dstep`, `dreplay`
`dreplay`, `dreplay_app` `dreplayApp`, `gdexec_dev`/`GDDev` `GdexecDev`/`GdexecDev.mk`
(`gv_gd/gv_drows/gv_dord/gv_dev` `gvGd/gvDrows/gvDord/gvDev`), `gv_ditem` `gvDitem`, `gv_dlbl`
`gvDlbl`, `gv_dins` `gvDins`, `gv_drow` `gvDrow`, `gv_ram` `gvRam`, `gv_dord_lbls` `gvDordLbls`,
`full_fence_at` `fullFenceAt`, `dev_io_causal` `devIoCausal`, `dev_consistent` `DevConsistent`
(`dc_nodup/dc_mem/dc_po/dc_ins/dc_kind/dc_replay/dc_io` `dcNodup/dcMem/dcPo/dcIns/dcKind/
dcReplay/dcIo`), `gdv_consistent` `gdvConsistent`, `filter_strongly_sorted`
`filterStronglySorted`, `ag_rel` `agRel`, `seq_ag_sorted` `seqAgSorted`, `dord_proj` `dordProj`,
`bv8_of` `bv8Of`, `dlbl_thr` `dlblThr`, `uart_ok` `uartOk`, `uart_acc_tx` `uartAccTx`,
`dstep_uart` `dstepUart`, `dreplay_uart_acc` `dreplayUartAcc`, `sublist_omap` `sublistOmap`,
`sublist_filter_self` `sublistFilterSelf`, `omap_fmap_comp` `omapFmapComp`, `omap_seq_lookup`
`omapSeqLookup`, `drow_sublist_dord` `drowSublistDord`, `dev0_uart` `dev0Uart`,
`gdv_uart_trace` `gdvUartTrace`, `uart_thr_pa` `uartThrPa`, `byte_a` `byteA`, `byte_b` `byteB`,
`wit_gd` `witGd`, `wit_rows` `witRows`, `wit_GV` `witGV`, `wit_bad` `witBad`, `wit_gd_cat`
`witGdCat`, `wit_dev_consistent` `witDevConsistent`, `wit_gdv_consistent` `witGdvConsistent`,
`wit_uart_sat` `witUartSat`, `wit_bad_inconsistent` `witBadInconsistent`, `at_mmio` `atMmio`,
`mmio_step_at` `mmioStepAt`, `dev_frontier` `devFrontier`, `dev_reducible`
`AxDevGraph.devReducible`, `uart_addr_dev` `uartAddrDev`, `in_uart_off` `AxDevGraph.inUartOff`,
`uart_mmio_write_step` `uartMmioWriteStep`, `uart_mmio_read_step` `uartMmioReadStep`,
`uart_dev_reducible_write` `uartDevReducibleWrite`, `uart_dev_reducible_read`
`uartDevReducibleRead`, `plic_pa` `plicPa`, `dv_wreq` `dvWreq`, `plic_byte_write_stuck`
`plicByteWriteStuck`, `uart_thr_in_uart` `uartThrInUart`, `dev_frontier_final`
`devFrontierFinal`.  The Ltac `wit_dev_consistent` is inlined into `witDevConsistent`.

**Not ported:** nothing.
-/
import Weak.AxOpsem
import Weak.AxGraphDec

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 1. Device events -/

/-- A device-fabric transaction (deviation 2: ports, the M/S wire). -/
inductive Dlbl where
  | DMmioR (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
  | DMmioW (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
  | DWire (h : CPU) (mm b : Bool)
  | DUartTx (i : UartId) (b : BitVec 8)
  | DUartRx (i : UartId) (b : BitVec 8)
  | DLatch (src : IrqSrc)
  | DDiskStart
  | DDiskCommit (delta : VirtioState → VirtioState)

open Dlbl

/-- The agent KIND a label belongs to: `true` = issued by the device agent. -/
def dlblDevside : Dlbl → Bool
  | .DMmioR .. | .DMmioW .. | .DWire .. => false
  | _ => true

/-- ONE device transaction against the SC device model. -/
def AxDevGraph.dstep (d : DevStates) : Dlbl → Option DevStates
  | .DMmioR pa n v =>
      match devRead d pa n with
      | some (w, d') => if w = v then some d' else none
      | none => none
  | .DMmioW pa n v => devWrite d pa n v
  | .DWire h mm b =>
      if Plic.eip (d.st .plic) (if mm then Plic.mctx h.val else Plic.sctx h.val) = b then some d
      else none
  | .DUartTx i b =>
      match Uart.txPop (d.st (.uart i)) with
      | some (b', u') => if b' = b then some (d.set (.uart i) u') else none
      | none => none
  | .DUartRx i b =>
      if (d.st (.uart i)).rx.length < Uart.fifoDepth then
        some (d.set (.uart i) (Uart.accept (d.st (.uart i)) b))
      else none
  | .DLatch src =>
      if devLevel d src then some (d.set .plic (Plic.latch (d.st .plic) src)) else none
  | .DDiskStart => some d
  | .DDiskCommit delta => some (d.set .virtio (delta (d.st .virtio)))

/-- The device STATE INTERPRETATION: replay a device order from a state. -/
def dreplay (d : DevStates) : List Dlbl → Option DevStates
  | [] => some d
  | l :: ls => (AxDevGraph.dstep d l).bind (fun d' => dreplay d' ls)

theorem dreplayApp (d : DevStates) (ls1 ls2 : List Dlbl) :
    dreplay d (ls1 ++ ls2) = (dreplay d ls1).bind (fun d' => dreplay d' ls2) := by
  induction ls1 generalizing d with
  | nil => rfl
  | cons l ls1 ih =>
    simp only [List.cons_append, dreplay]
    cases AxDevGraph.dstep d l with
    | none => rfl
    | some d' => exact ih d'

/-- Power-on (Rocq `dev0_state`; Lean-only name). -/
def AxDevGraph.dev0State : DevStates := ⟨fun _ => default⟩

/-! ## 2. The graph extension -/

structure GdexecDev where
  gvGd : Gdexec
  gvDrows : List (List (Nat × Dlbl))
  gvDord : List Geid
  gvDev : Nat

def gvDitem (GV : GdexecDev) (e : Geid) : Option (Nat × Dlbl) :=
  (GV.gvDrows[e.1]?).bind (fun r => r[e.2]?)
def gvDlbl (GV : GdexecDev) (e : Geid) : Option Dlbl := (gvDitem GV e).map Prod.snd
def gvDins (GV : GdexecDev) (e : Geid) : Option Nat := (gvDitem GV e).map Prod.fst
def gvDrow (GV : GdexecDev) (i : Nat) : List (Nat × Dlbl) := (GV.gvDrows[i]?).getD []
def gvRam (GV : GdexecDev) : Gexec := GV.gvGd.gdG

/-- The labels of the device order. -/
def gvDordLbls (GV : GdexecDev) : List Dlbl := GV.gvDord.filterMap (gvDlbl GV)

def fullFenceAt (G : Gexec) (a k : Nat) : Prop :=
  gxLbl G (a, k) = some (.LFence true true true true)

/-- THE I/O-CAUSALITY RULE (declared hardware clause). -/
def devIoCausal (GV : GdexecDev) : Prop :=
  ∀ a b kx kf1 j1 k1 j2 k2 kf2 ky p1 p2 : Nat,
    gmem (gvRam GV) (a, kx) →
    fullFenceAt (gvRam GV) a kf1 → kx < kf1 →
    gvDins GV (a, j1) = some k1 → kf1 < k1 →
    GV.gvDord[p1]? = some (a, j1) → GV.gvDord[p2]? = some (b, j2) → p1 ≤ p2 →
    gvDins GV (b, j2) = some k2 → k2 ≤ kf2 →
    fullFenceAt (gvRam GV) b kf2 → kf2 < ky →
    gmem (gvRam GV) (b, ky) →
    gmoLt (gvRam GV) (a, kx) (b, ky)

/-- DEVICE CONSISTENCY. -/
structure DevConsistent (GV : GdexecDev) : Prop where
  dcNodup : GV.gvDord.Nodup
  dcMem : ∀ e, e ∈ GV.gvDord ↔ (gvDitem GV e).isSome = true
  dcPo : ∀ p1 p2 i j1 j2 : Nat, p1 < p2 →
    GV.gvDord[p1]? = some (i, j1) → GV.gvDord[p2]? = some (i, j2) → j1 < j2
  dcIns : ∀ i j1 j2 k1 k2 : Nat, j1 ≤ j2 →
    gvDins GV (i, j1) = some k1 → gvDins GV (i, j2) = some k2 →
    k1 ≤ k2 ∧ k2 ≤ (((gvRam GV).gxProg[i]?).getD []).length
  dcKind : ∀ e l, gvDlbl GV e = some l → (dlblDevside l = true ↔ e.1 = GV.gvDev)
  dcReplay : (dreplay AxDevGraph.dev0State (gvDordLbls GV)).isSome = true
  dcIo : devIoCausal GV

def gdvConsistent (GV : GdexecDev) : Prop :=
  rvwmoCatConsistent GV.gvGd ∧ DevConsistent GV

/-! ## 3. SC reduction of the device order: per-agent projection -/

theorem filterStronglySorted {A : Type} (P : A → Prop) [DecidablePred P] (R : A → A → Prop)
    (l : List A) :
    (∀ (p1 p2 : Nat) (x y : A), p1 < p2 → l[p1]? = some x → l[p2]? = some y → P x → P y → R x y) →
    (l.filter (fun x => decide (P x))).Pairwise R := by
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a l ih =>
    intro H
    have ih' := ih (fun p1 p2 x y hp h1 h2 => H (p1 + 1) (p2 + 1) x y (by omega) h1 h2)
    rw [List.filter_cons]
    by_cases hPa : P a
    · simp only [hPa, decide_true, ↓reduceIte]
      refine List.Pairwise.cons ?_ ih'
      intro y hy
      obtain ⟨hy, hPy⟩ := List.mem_filter.1 hy
      obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hy
      exact H 0 (p + 1) a y (by omega) rfl hp hPa (of_decide_eq_true hPy)
    · simp only [hPa, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih'

def agRel (i : Nat) : Geid → Geid → Prop := fun e1 e2 => e1.1 = i ∧ e2.1 = i ∧ e1.2 ≤ e2.2

theorem seqAgSorted (i a n : Nat) : ((List.range' a n).map (fun j => (i, j))).Pairwise (agRel i) := by
  induction n generalizing a with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range'_succ, List.map_cons]
    refine List.Pairwise.cons ?_ (ih (a + 1))
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have := List.mem_range'_1.1 hj
    exact ⟨rfl, rfl, by simp only []; omega⟩

/-- THE PROJECTION THEOREM. -/
theorem dordProj (GV : GdexecDev) (i : Nat) :
    DevConsistent GV →
    GV.gvDord.filter (fun e : Geid => decide (e.1 = i)) =
      (List.range (gvDrow GV i).length).map (fun j => (i, j)) := by
  intro Hc
  rw [List.range_eq_range']
  apply List.Perm.eq_of_pairwise (le := agRel i)
  · intro x1 x2 _ _ h12 h21
    obtain ⟨a1, b1⟩ := x1
    obtain ⟨a2, b2⟩ := x2
    obtain ⟨h1, h2, hle⟩ := h12
    obtain ⟨_, _, hge⟩ := h21
    simp only [] at h1 h2 hle hge
    subst h1 h2
    have : b1 = b2 := by omega
    subst this; rfl
  · apply filterStronglySorted
    intro p1 p2 x y hp h1 h2 hx hy
    obtain ⟨i1, j1⟩ := x
    obtain ⟨i2, j2⟩ := y
    simp only [] at hx hy
    subst hx hy
    have := Hc.dcPo p1 p2 _ j1 j2 hp h1 h2
    exact ⟨rfl, rfl, by simp only []; omega⟩
  · exact seqAgSorted i 0 _
  · rw [List.perm_ext_iff_of_nodup (List.Pairwise.filter _ Hc.dcNodup)]
    · intro e
      obtain ⟨i', j⟩ := e
      rw [List.mem_filter, Hc.dcMem, List.mem_map]
      simp only [gvDitem, gvDrow, decide_eq_true_eq]
      constructor
      · rintro ⟨hs, rfl⟩
        refine ⟨j, ?_, rfl⟩
        rw [List.mem_range'_1]
        cases hr : GV.gvDrows[i']? with
        | none => simp [hr] at hs
        | some r =>
          simp only [hr, Option.bind_some, Option.getD_some] at hs ⊢
          simp at hs
          omega
      · rintro ⟨j', hj, he⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, rfl⟩
        rw [List.mem_range'_1] at hj
        cases hr : GV.gvDrows[i]? with
        | none => simp [hr] at hj
        | some r =>
          simp only [hr, Option.bind_some, Option.getD_some] at hj ⊢
          simp only [List.getElem?_eq_getElem (by omega : j' < r.length), Option.isSome_some]
    · refine List.Pairwise.map _ ?_ List.nodup_range'
      intro a b hab h
      simp only [Prod.mk.injEq] at h
      exact hab h.2

/-! ## 4. The UART as a graph agent -/

/-- The byte of a 1-byte write (deviation 2). -/
def bv8Of (n : Nat) (v : BitVec (8 * n)) : Option (BitVec 8) :=
  if n = 1 then some (v.extractLsb' 0 8) else none

/-- The byte of a THR write to port `pt`. -/
def dlblThr (pt : UartId) : Dlbl → Option (BitVec 8)
  | .DMmioW pa n v => if devDecode pa = some (.uart pt, 0) then bv8Of n v else none
  | _ => none

/-- The UART discipline: port `pt`'s window writes are 1-byte THR writes. -/
def uartOk (pt : UartId) : Dlbl → Prop
  | .DMmioW pa n _ => ∀ off, devDecode pa = some (.uart pt, off) → off = 0 ∧ n = 1
  | _ => True

theorem uartAccTx (u u' : UartState) : Uart.acc u' = Uart.acc u → u'.out = u.out → u'.tx = u.tx := by
  intro h ho
  simp only [Uart.acc, ho] at h
  exact List.append_cancel_left h

theorem AxDevGraph.uartReadStable (u u' : UartState) (off : Nat) (b : BitVec 8) :
    Uart.read u off = some (b, u') → u'.tx = u.tx ∧ u'.out = u.out ∧ u'.lcr = u.lcr := by
  intro h
  unfold Uart.read at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h;
       exact ⟨rfl, rfl, rfl⟩)
    | exact absurd h (by simp)

/-- The post-condition frame: a step that leaves the port's trace, FIFO bound and DLAB alone and
carries no THR byte. -/
theorem AxDevGraph.uartPostFrame (u u' : UartState) (thr : Option (BitVec 8)) :
    Uart.dlab u = false → Uart.dlab u' = Uart.dlab u → Uart.acc u' = Uart.acc u →
    u'.tx.length ≤ u.tx.length → thr = none →
    Uart.dlab u' = false ∧
    (thr = none ∨ u.tx.length < Uart.fifoDepth → Uart.acc u' = Uart.acc u ++ thr.toList) ∧
    u'.tx.length ≤ u.tx.length + thr.toList.length := by
  intro hd hd' ha hl ht
  subst ht
  exact ⟨hd'.trans hd, fun _ => by simp [ha], by simp; omega⟩

theorem AxDevGraph.uartNe (pt : UartId) (dv : DevId) : dv ≠ .uart pt → DevId.uart pt ≠ dv :=
  fun h e => h e.symm

/-- ONE device step, seen from port `pt`'s accepted-byte trace. -/
theorem dstepUart (pt : UartId) (d : DevStates) (l : Dlbl) (d' : DevStates) :
    AxDevGraph.dstep d l = some d' → uartOk pt l → Uart.dlab (d.st (.uart pt)) = false →
    Uart.dlab (d'.st (.uart pt)) = false ∧
    (dlblThr pt l = none ∨ (d.st (.uart pt)).tx.length < Uart.fifoDepth →
      Uart.acc (d'.st (.uart pt)) = Uart.acc (d.st (.uart pt)) ++ (dlblThr pt l).toList) ∧
    (d'.st (.uart pt)).tx.length ≤
      (d.st (.uart pt)).tx.length + (dlblThr pt l).toList.length := by
  intro hs hok hdl
  have frame : d'.st (.uart pt) = d.st (.uart pt) → dlblThr pt l = none →
      Uart.dlab (d'.st (.uart pt)) = false ∧
      (dlblThr pt l = none ∨ (d.st (.uart pt)).tx.length < Uart.fifoDepth →
        Uart.acc (d'.st (.uart pt)) = Uart.acc (d.st (.uart pt)) ++ (dlblThr pt l).toList) ∧
      (d'.st (.uart pt)).tx.length ≤
        (d.st (.uart pt)).tx.length + (dlblThr pt l).toList.length := by
    intro he ht
    rw [he]
    exact AxDevGraph.uartPostFrame _ _ _ hdl rfl rfl (Nat.le_refl _) ht
  cases l with
  | DMmioR pa n v =>
    simp only [AxDevGraph.dstep] at hs
    have hthr : dlblThr pt (.DMmioR pa n v) = none := rfl
    cases hr : devRead d pa n with
    | none => simp [hr] at hs
    | some p =>
      obtain ⟨w, d1⟩ := p
      simp only [hr] at hs
      by_cases hw : w = v
      · simp only [hw, ↓reduceIte, Option.some.injEq] at hs
        subst hs
        simp only [devRead] at hr
        cases hdec : devDecode pa with
        | none => simp [hdec] at hr
        | some q =>
          obtain ⟨dv, off⟩ := q
          simp only [hdec, Option.map_eq_some_iff] at hr
          obtain ⟨⟨w', s'⟩, hrd, he⟩ := hr
          simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          by_cases hdv : dv = .uart pt
          · subst hdv
            rw [DevStates.set_same, hthr]
            simp only [devSig, Uart.sig, Uart.readN] at hrd
            split at hrd
            · simp only [Option.map_eq_some_iff] at hrd
              obtain ⟨⟨b, u1⟩, hrd, he⟩ := hrd
              simp only [Prod.mk.injEq] at he
              obtain ⟨-, rfl⟩ := he
              obtain ⟨htx, hout, hlcr⟩ := AxDevGraph.uartReadStable _ _ _ _ hrd
              refine AxDevGraph.uartPostFrame _ _ _ hdl ?_ ?_ (Nat.le_of_eq (by rw [htx])) rfl
              · simp only [Uart.dlab, hlcr]
              · simp only [Uart.acc, htx, hout]
            · simp at hrd
          · exact frame (DevStates.set_other _ _ _ _ (AxDevGraph.uartNe pt dv hdv)) hthr
      · simp [hw] at hs
  | DMmioW pa n v =>
    simp only [AxDevGraph.dstep, devWrite] at hs
    cases hdec : devDecode pa with
    | none => simp [hdec] at hs
    | some q =>
      obtain ⟨dv, off⟩ := q
      simp only [hdec, Option.map_eq_some_iff] at hs
      obtain ⟨s', hwr, rfl⟩ := hs
      by_cases hdv : dv = .uart pt
      · subst hdv
        obtain ⟨rfl, rfl⟩ := hok off hdec
        have hthr : dlblThr pt (.DMmioW pa 1 v) = some (v.extractLsb' 0 8) := by
          simp [dlblThr, hdec, bv8Of]
        rw [DevStates.set_same, hthr]
        simp only [devSig, Uart.sig, Uart.writeN] at hwr
        simp only [true_or, ↓reduceIte, Uart.write] at hwr
        simp only [hdl, Bool.false_eq_true, ↓reduceIte] at hwr
        by_cases hroom : (d.st (.uart pt)).tx.length < Uart.fifoDepth
        · simp only [hroom, ↓reduceIte] at hwr
          obtain rfl := Option.some.inj hwr
          refine ⟨hdl, fun _ => ?_, ?_⟩
          · simp [Uart.acc]
          · simp
        · simp only [hroom, ↓reduceIte] at hwr
          obtain rfl := Option.some.inj hwr
          refine ⟨hdl, fun h => ?_, ?_⟩
          · rcases h with h | h
            · exact absurd h (by simp)
            · exact absurd h hroom
          · simp
      · have hthr : dlblThr pt (.DMmioW pa n v) = none := by
          simp only [dlblThr, hdec, Option.some.injEq, Prod.mk.injEq, hdv, false_and,
            ↓reduceIte]
        exact frame (DevStates.set_other _ _ _ _ (AxDevGraph.uartNe pt dv hdv)) hthr
  | DWire h mm b =>
    simp only [AxDevGraph.dstep, Option.ite_none_right_eq_some] at hs
    obtain ⟨-, hs⟩ := hs
    obtain rfl := Option.some.inj hs
    exact frame rfl rfl
  | DUartTx j b =>
    simp only [AxDevGraph.dstep] at hs
    have hthr : dlblThr pt (.DUartTx j b) = none := rfl
    cases hp : Uart.txPop (d.st (.uart j)) with
    | none => simp [hp] at hs
    | some q =>
      obtain ⟨b', u'⟩ := q
      simp only [hp] at hs
      by_cases hb : b' = b
      · simp only [hb, ↓reduceIte, Option.some.injEq] at hs
        subst hs
        by_cases hj : j = pt
        · subst hj
          rw [DevStates.set_same, hthr]
          unfold Uart.txPop at hp
          split at hp
          · simp at hp
          · rename_i b0 tx' htx
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨-, rfl⟩ := hp
            refine AxDevGraph.uartPostFrame _ _ _ hdl ?_ ?_ ?_ rfl
            · split <;> rfl
            · split <;> simp [Uart.acc, Uart.recv, htx]
            · split <;> simp [Uart.recv, htx]
        · have hne : DevId.uart pt ≠ DevId.uart j := fun e => hj (by cases e; rfl)
          exact frame (DevStates.set_other _ _ _ _ hne) hthr
      · simp [hb] at hs
  | DUartRx j b =>
    simp only [AxDevGraph.dstep] at hs
    have hthr : dlblThr pt (.DUartRx j b) = none := rfl
    simp only [Option.ite_none_right_eq_some] at hs
    obtain ⟨-, hs⟩ := hs
    obtain rfl := Option.some.inj hs
    · by_cases hj : j = pt
      · subst hj
        rw [DevStates.set_same, hthr]
        exact AxDevGraph.uartPostFrame _ _ _ hdl rfl rfl (Nat.le_refl _) rfl
      · have hne : DevId.uart pt ≠ DevId.uart j := fun e => hj (by cases e; rfl)
        exact frame (DevStates.set_other _ _ _ _ hne) hthr
  | DLatch src =>
    simp only [AxDevGraph.dstep, Option.ite_none_right_eq_some] at hs
    obtain ⟨-, hs⟩ := hs
    obtain rfl := Option.some.inj hs
    exact frame (DevStates.set_other _ _ _ _ (by intro e; cases e)) rfl
  | DDiskStart =>
    simp only [AxDevGraph.dstep, Option.some.injEq] at hs
    subst hs
    exact frame rfl rfl
  | DDiskCommit delta =>
    simp only [AxDevGraph.dstep, Option.some.injEq] at hs
    subst hs
    exact frame (DevStates.set_other _ _ _ _ (by intro e; cases e)) rfl

theorem AxDevGraph.filterMapCons {A B : Type} (f : A → Option B) (x : A) (l : List A) :
    (x :: l).filterMap f = (f x).toList ++ l.filterMap f := by
  cases h : f x <;> simp [h]

/-- THE UART REPLAY THEOREM (per port). -/
theorem dreplayUartAcc (pt : UartId) (d : DevStates) (ls : List Dlbl) (d' : DevStates) :
    dreplay d ls = some d' → (∀ l ∈ ls, uartOk pt l) → Uart.dlab (d.st (.uart pt)) = false →
    (d.st (.uart pt)).tx.length + (ls.filterMap (dlblThr pt)).length ≤ Uart.fifoDepth →
    Uart.acc (d'.st (.uart pt)) = Uart.acc (d.st (.uart pt)) ++ ls.filterMap (dlblThr pt) ∧
    Uart.dlab (d'.st (.uart pt)) = false := by
  induction ls generalizing d with
  | nil =>
    intro hr _ hdl _
    simp only [dreplay, Option.some.injEq] at hr
    subst hr
    exact ⟨by simp, hdl⟩
  | cons l ls ih =>
    intro hr hok hdl hroom
    rw [AxDevGraph.filterMapCons] at hroom ⊢
    rw [List.length_append] at hroom
    simp only [dreplay] at hr
    cases hs : AxDevGraph.dstep d l with
    | none => simp [hs] at hr
    | some d1 =>
      simp only [hs, Option.bind_some] at hr
      obtain ⟨hdl1, hacc, hlen⟩ :=
        dstepUart pt d l d1 hs (hok l (List.mem_cons_self ..)) hdl
      have hacc1 : Uart.acc (d1.st (.uart pt)) =
          Uart.acc (d.st (.uart pt)) ++ (dlblThr pt l).toList := by
        apply hacc
        cases h : dlblThr pt l with
        | none => exact .inl rfl
        | some b => right; simp only [h, Option.toList_some, List.length_singleton] at hroom; omega
      obtain ⟨iha, ihd⟩ := ih d1 hr (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hdl1
        (by omega)
      exact ⟨by rw [iha, hacc1, List.append_assoc], ihd⟩

/-! ### 4.1 Lifted to the graph -/

theorem sublistOmap {A B : Type} (f : A → Option B) (l1 l2 : List A) :
    l1.Sublist l2 → (l1.filterMap f).Sublist (l2.filterMap f) :=
  List.Sublist.filterMap f

theorem sublistFilterSelf {A : Type} (P : A → Prop) [DecidablePred P] (l : List A) :
    (l.filter (fun x => decide (P x))).Sublist l :=
  List.filter_sublist

theorem omapFmapComp {A B C : Type} (f : B → Option C) (g : A → B) (l : List A) :
    (l.map g).filterMap f = l.filterMap (f ∘ g) :=
  List.filterMap_map

theorem omapSeqLookup {A B : Type} (h : A → B) (r : List A) :
    (List.range r.length).filterMap (fun j => r[j]?.map h) = r.map h := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    simp only [List.getElem?_cons_zero, Option.map_some, List.map_cons]
    congr 1

/-- Agent `i`'s device labels, in its program order, are a SUBSEQUENCE of the device order's. -/
theorem drowSublistDord (GV : GdexecDev) (i : Nat) :
    DevConsistent GV → ((gvDrow GV i).map Prod.snd).Sublist (gvDordLbls GV) := by
  intro Hc
  unfold gvDordLbls
  have hsub := sublistOmap (gvDlbl GV) _ _ (sublistFilterSelf (fun e : Geid => e.1 = i) GV.gvDord)
  suffices heq : (gvDrow GV i).map Prod.snd =
      (GV.gvDord.filter (fun e : Geid => decide (e.1 = i))).filterMap (gvDlbl GV) by
    rw [heq]; exact hsub
  rw [dordProj GV i Hc, omapFmapComp]
  unfold gvDrow
  cases hr : GV.gvDrows[i]? with
  | none => rfl
  | some r =>
    simp only [Option.getD_some]
    rw [← omapSeqLookup Prod.snd r]
    congr 1
    funext j
    simp only [Function.comp, gvDlbl, gvDitem, hr, Option.bind_some]

theorem dev0Uart (pt : UartId) :
    Uart.dlab (AxDevGraph.dev0State.st (.uart pt)) = false ∧
    (AxDevGraph.dev0State.st (.uart pt)).tx = [] ∧
    Uart.acc (AxDevGraph.dev0State.st (.uart pt)) = [] := by
  cases pt <;> exact ⟨rfl, rfl, rfl⟩

/-- THE UART AS A GRAPH AGENT (per port). -/
theorem gdvUartTrace (pt : UartId) (GV : GdexecDev) :
    DevConsistent GV →
    (∀ l ∈ gvDordLbls GV, uartOk pt l) →
    ((gvDordLbls GV).filterMap (dlblThr pt)).length ≤ Uart.fifoDepth →
    ∃ d', dreplay AxDevGraph.dev0State (gvDordLbls GV) = some d' ∧
      Uart.acc (d'.st (.uart pt)) = (gvDordLbls GV).filterMap (dlblThr pt) ∧
      ∀ i, ((gvDrow GV i).filterMap (dlblThr pt ∘ Prod.snd)).Sublist
        (Uart.acc (d'.st (.uart pt))) := by
  intro Hc hok hroom
  obtain ⟨d', hr⟩ := Option.isSome_iff_exists.1 Hc.dcReplay
  obtain ⟨hdl, htx, hacc0⟩ := dev0Uart pt
  obtain ⟨hacc, -⟩ := dreplayUartAcc pt _ _ _ hr hok hdl (by rw [htx]; simpa using hroom)
  rw [hacc0, List.nil_append] at hacc
  refine ⟨d', hr, hacc, fun i => ?_⟩
  rw [hacc, ← omapFmapComp]
  exact sublistOmap _ _ _ (drowSublistDord GV i Hc)

/-! ## 5. Non-vacuity -/

def uartThrPa : PAddr := BitVec.ofNat 64 0x10000000
def byteA : BitVec 8 := BitVec.ofNat 8 97
def byteB : BitVec 8 := BitVec.ofNat 8 98

/-- Two harts (agents 0, 1) each write one console byte; the device agent (2) transmits one.
RAM rows are empty. -/
def witGd : Gdexec := ⟨⟨fun _ => none, [[], [], []], []⟩, []⟩

def witRows : List (List (Nat × Dlbl)) :=
  [[(0, .DMmioW uartThrPa 1 byteA)],
   [(0, .DMmioW uartThrPa 1 byteB)],
   [(0, .DUartTx .uart0 byteB)]]

def witGV : GdexecDev := ⟨witGd, witRows, [(1, 0), (0, 0), (2, 0)], 2⟩
def witBad : GdexecDev := ⟨witGd, witRows, [(0, 0), (1, 0), (2, 0)], 2⟩

theorem witGdCat : rvwmoCatConsistent witGd := catConsistentBSound _ (by decide +kernel)

theorem AxDevGraph.witLbls :
    gvDordLbls witGV =
      [.DMmioW uartThrPa 1 byteB, .DMmioW uartThrPa 1 byteA, .DUartTx .uart0 byteB] := rfl

theorem witDevConsistent : DevConsistent witGV where
  dcNodup := by decide
  dcMem := by
    intro e
    obtain ⟨a, j⟩ := e
    rcases a with _ | _ | _ | a <;> rcases j with _ | j <;>
      simp [gvDitem, witGV, witRows]
  dcPo := by
    intro p1 p2 i j1 j2 hp h1 h2
    rcases p1 with _ | _ | _ | p1 <;> rcases p2 with _ | _ | _ | p2 <;>
      simp [witGV] at h1 h2 hp <;> omega
  dcIns := by
    intro i j1 j2 k1 k2 _ h1 h2
    rcases i with _ | _ | _ | i <;> rcases j1 with _ | j1 <;> rcases j2 with _ | j2 <;>
      simp [gvDins, gvDitem, witGV, witRows] at h1 h2 <;> subst h1 h2 <;>
      simp [gvRam, witGV, witGd]
  dcKind := by
    intro e l hl
    obtain ⟨a, j⟩ := e
    rcases a with _ | _ | _ | a <;> rcases j with _ | j <;>
      simp [gvDlbl, gvDitem, witGV, witRows] at hl <;> subst hl <;> simp [dlblDevside, witGV]
  dcReplay := by rw [AxDevGraph.witLbls]; decide +kernel
  dcIo := by
    intro a b kx _ _ _ _ _ _ _ _ _ hm
    obtain ⟨l, hl, _⟩ := hm
    rcases a with _ | _ | _ | a <;> simp [gxLbl, gvRam, witGV, witGd] at hl

theorem witGdvConsistent : gdvConsistent witGV := ⟨witGdCat, witDevConsistent⟩

theorem witUartSat :
    gdvConsistent witGV ∧
    (∀ l ∈ gvDordLbls witGV, uartOk .uart0 l) ∧
    ((gvDordLbls witGV).filterMap (dlblThr .uart0)).length ≤ Uart.fifoDepth ∧
    ∃ d', dreplay AxDevGraph.dev0State (gvDordLbls witGV) = some d' ∧
      Uart.acc (d'.st (.uart .uart0)) = [byteB, byteA] ∧
      (d'.st (.uart .uart0)).out = [byteB] := by
  have hd : devDecode uartThrPa = some (.uart .uart0, 0) := by decide +kernel
  refine ⟨witGdvConsistent, ?_, ?_, ?_⟩
  · rw [AxDevGraph.witLbls]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · intro off h; rw [hd] at h; cases h; exact ⟨rfl, rfl⟩
    · intro off h; rw [hd] at h; cases h; exact ⟨rfl, rfl⟩
    · trivial
  · rw [AxDevGraph.witLbls]; decide +kernel
  · rw [AxDevGraph.witLbls]
    have h1 : (dreplay AxDevGraph.dev0State
        [.DMmioW uartThrPa 1 byteB, .DMmioW uartThrPa 1 byteA, .DUartTx .uart0 byteB]).map
        (fun d => (Uart.acc (d.st (.uart .uart0)), (d.st (.uart .uart0)).out)) =
        some ([byteB, byteA], [byteB]) := by decide +kernel
    obtain ⟨d', hd', he⟩ := Option.map_eq_some_iff.1 h1
    simp only [Prod.mk.injEq] at he
    exact ⟨d', hd', he.1, he.2⟩

/-- THE DEVICE STATE IS LOAD-BEARING. -/
theorem witBadInconsistent : ¬ DevConsistent witBad := by
  intro Hc
  have h := Hc.dcReplay
  have hl : gvDordLbls witBad =
      [.DMmioW uartThrPa 1 byteA, .DMmioW uartThrPa 1 byteB, .DUartTx .uart0 byteB] := rfl
  rw [hl] at h
  revert h
  decide +kernel

/-! ## 6. The target `devReducible` and its UART instance -/

/-- A hart sitting at an MMIO node (no parked fence). -/
def atMmio (p : Pexv6) : Prop :=
  (∃ (cpu : CPU) (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
     (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
     (ib : Ibch),
     p = .PHart cpu (.impure (.ok (.memRead n va req)) k) rs none ib ∧ devAddr req.pa = true) ∨
  (∃ (cpu : CPU) (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
     (k : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch),
     p = .PHart cpu (.impure (.ok (.memWrite n va req)) k) rs none ib ∧ devAddr req.pa = true)

/-- The program's MMIO step AT A PINNED fabric (deviation 3). -/
def mmioStepAt (F : Efab) (p : Pexv6) : Prop := ∃ p' F', pstepProg p F LDev p' F'

/-- The device states at which agent `i`'s NEXT device event may be performed. -/
def devFrontier (GV : GdexecDev) (i : Nat) (d : DevStates) : Prop :=
  ∃ p, (∀ q e, GV.gvDord[q]? = some e → e.1 = i → q < p) ∧
    dreplay AxDevGraph.dev0State ((GV.gvDord.take p).filterMap (gvDlbl GV)) = some d

/-- THE TARGET SHAPE (C11). -/
def AxDevGraph.devReducible (GV : GdexecDev) (T : Int → Prop) (img : Int → Option (BitVec 8))
    (i : Nat) (s : Athread) : Prop :=
  reducibleGd GV.gvGd i T img s ∧
  (atMmio s.atP → ∀ F : Efab, devFrontier GV i F.efDev → mmioStepAt F s.atP)

theorem AxDevGraph.uartDecodeBounds (pa : PAddr) (pt : UartId) (off : Nat) :
    devDecode pa = some (.uart pt, off) → off < uartSize ∧ pa.toNat < devBound := by
  intro h
  unfold devDecode at h
  simp only [uartBase, uartSize, plicBase, plicSize] at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       simp only [uartSize, devBound]; omega)
    | (simp at h)

theorem uartAddrDev (pa : PAddr) (pt : UartId) (off : Nat) :
    devDecode pa = some (.uart pt, off) → devAddr pa = true := by
  intro h
  simp only [devAddr, decide_eq_true_eq]
  exact (AxDevGraph.uartDecodeBounds pa pt off h).2

theorem AxDevGraph.inUartOff (pa : PAddr) (pt : UartId) (off : Nat) :
    devDecode pa = some (.uart pt, off) → off < uartSize :=
  fun h => (AxDevGraph.uartDecodeBounds pa pt off h).1

theorem AxDevGraph.uartWriteTotal (u : UartState) (off : Nat) (b : BitVec 8) :
    off < uartSize → ∃ u', Uart.write u off b = some u' := by
  intro hoff
  simp only [uartSize] at hoff
  unfold Uart.write
  repeat' split
  all_goals first | exact ⟨_, rfl⟩ | omega

theorem AxDevGraph.uartReadTotal (u : UartState) (off : Nat) :
    off < uartSize → ∃ b u', Uart.read u off = some (b, u') := by
  intro hoff
  simp only [uartSize] at hoff
  unfold Uart.read
  repeat' split
  all_goals first | exact ⟨_, _, rfl⟩ | omega

/-- The UART never blocks a 1-byte MMIO WRITE, at ANY fabric. -/
theorem uartMmioWriteStep (F : Efab) (cpu : CPU) (va : Nat)
    (req : Mem_write_request 1 va Arch.pa Arch.translation Arch.arch_ak) (v : BitVec (8 * 1))
    (k : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch)
    (pt : UartId) (off : Nat) :
    devDecode req.pa = some (.uart pt, off) → req.value = some v →
    mmioStepAt F (.PHart cpu (.impure (.ok (.memWrite 1 va req)) k) rs none ib) := by
  intro hdec hval
  obtain ⟨u', hw⟩ := AxDevGraph.uartWriteTotal (F.efDev.st (.uart pt)) off (v.extractLsb' 0 8)
    (AxDevGraph.inUartOff _ _ _ hdec)
  have hdev := uartAddrDev _ _ _ hdec
  refine ⟨.PHart cpu (k (.Ok (some true))) rs none ib,
    { F with efDev := F.efDev.set (.uart pt) u' }, rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  simp only [pstepNode, pnodeStep, hdev, hval, ↓reduceIte, and_true]
  simp only [devWrite, hdec, devSig, Uart.sig, Uart.writeN]
  simp only [true_or, ↓reduceIte, hw]
  rfl

/-- ... nor a 1-byte MMIO READ. -/
theorem uartMmioReadStep (F : Efab) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 1 va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (pt : UartId) (off : Nat) :
    devDecode req.pa = some (.uart pt, off) →
    mmioStepAt F (.PHart cpu (.impure (.ok (.memRead 1 va req)) k) rs none ib) := by
  intro hdec
  obtain ⟨b, u', hr⟩ := AxDevGraph.uartReadTotal (F.efDev.st (.uart pt)) off
    (AxDevGraph.inUartOff _ _ _ hdec)
  have hdev := uartAddrDev _ _ _ hdec
  refine ⟨.PHart cpu (k (.Ok (BitVec.setWidth (8 * 1) b, none))) rs none ib,
    { F with efDev := F.efDev.set (.uart pt) u' }, rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  simp only [pstepNode, pnodeStep, hdev, ↓reduceIte, and_true]
  refine ⟨BitVec.setWidth (8 * 1) b, ?_⟩
  simp only [devRead, hdec, devSig, Uart.sig, Uart.readN]
  simp only [true_or, ↓reduceIte, hr]
  simp

/-- THE UART INSTANCE OF `devReducible` (write). -/
theorem uartDevReducibleWrite (GV : GdexecDev) (T : Int → Prop) (img : Int → Option (BitVec 8))
    (i : Nat) (cpu : CPU) (va : Nat)
    (req : Mem_write_request 1 va Arch.pa Arch.translation Arch.arch_ak) (v : BitVec (8 * 1))
    (k : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (kk : Nat)
    (pt : UartId) (off : Nat) :
    devDecode req.pa = some (.uart pt, off) → req.value = some v →
    AxDevGraph.devReducible GV T img i
      ⟨.PHart cpu (.impure (.ok (.memWrite 1 va req)) k) rs none ib, kk⟩ := by
  intro hdec hval
  refine ⟨?_, fun _ F _ => uartMmioWriteStep F cpu va req v k rs ib pt off hdec hval⟩
  obtain ⟨p', d', hs⟩ := uartMmioWriteStep OpaxWit.wtD0 cpu va req v k rs ib pt off hdec hval
  exact ⟨[], ⟨p', kk⟩, .inl ⟨LDev, .AStepAdmin _ kk _ _ _ _ trivial hs⟩⟩

/-- THE UART INSTANCE OF `devReducible` (read). -/
theorem uartDevReducibleRead (GV : GdexecDev) (T : Int → Prop) (img : Int → Option (BitVec 8))
    (i : Nat) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 1 va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (kk : Nat) (pt : UartId) (off : Nat) :
    devDecode req.pa = some (.uart pt, off) →
    AxDevGraph.devReducible GV T img i
      ⟨.PHart cpu (.impure (.ok (.memRead 1 va req)) k) rs none ib, kk⟩ := by
  intro hdec
  refine ⟨?_, fun _ F _ => uartMmioReadStep F cpu va req k rs ib pt off hdec⟩
  obtain ⟨p', d', hs⟩ := uartMmioReadStep OpaxWit.wtD0 cpu va req k rs ib pt off hdec
  exact ⟨[], ⟨p', kk⟩, .inl ⟨LDev, .AStepAdmin _ kk _ _ _ _ trivial hs⟩⟩

/-! ### 6.1 The pinned clause is NOT trivial -/

def plicPa : PAddr := BitVec.ofNat 64 0xc000000

def dvWreq (pa : PAddr) (v : BitVec 8) : Mem_write_request 1 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := OpaxWit.wtAk, va := none, pa := pa, translation := (), size := 1,
    value := some v, tag := none }

theorem plicByteWriteStuck (F : Efab) (cpu : CPU) (v : BitVec 8)
    (k : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) :
    ¬ mmioStepAt F (.PHart cpu (.impure (.ok (.memWrite 1 64 (dvWreq plicPa v))) k) rs none ib) := by
  rintro ⟨p', F', h⟩
  cases p' with
  | PDisk _ => exact h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨_, ors, oib, obar, _, _, hn, _⟩ := h
    have hdev : devAddr (dvWreq plicPa v).pa = true := (by decide +kernel : devAddr plicPa = true)
    have hval : (dvWreq plicPa v).value = some v := rfl
    have hdec : devDecode (dvWreq plicPa v).pa = some (.plic, 0) :=
      (by decide +kernel : devDecode plicPa = some (.plic, 0))
    simp only [pstepNode, pnodeStep, hdev, hval, ↓reduceIte] at hn
    have hw := hn.1
    simp only [devWrite, hdec, devSig, Plic.sig, Plic.writeN] at hw
    simp at hw

/-- ... while the UART premise is satisfiable (the THR address). -/
theorem uartThrInUart (v : BitVec 8) :
    devDecode (dvWreq uartThrPa v).pa = some (.uart .uart0, 0) :=
  (by decide +kernel : devDecode uartThrPa = some (.uart .uart0, 0))

/-- The frontier quantifier of `devReducible` is never empty on a device-consistent graph. -/
theorem devFrontierFinal (GV : GdexecDev) (i : Nat) :
    DevConsistent GV → ∃ d, devFrontier GV i d := by
  intro Hc
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 Hc.dcReplay
  refine ⟨d, GV.gvDord.length, fun q e he _ => ?_, ?_⟩
  · exact (List.getElem?_eq_some_iff.1 he).1
  · rw [List.take_length]; exact hd

end Weak
