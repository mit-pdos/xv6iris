/-
Weak: **device REDUCIBILITY on the graph side and a concrete device-consistent WITNESS**
(K2 / C11; the non-vacuity certificate for `AxDevGraph`).  Pure (no Iris).

Rocq: `iris/AxDevGraphWit.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `devStateReducible` / `AxDevGraphWit.devReducible` — the graph analog of the SC pool's
device REDUCIBILITY: at EVERY prefix state of the device order (i) the device agent has an
enabled device-side step (TRIVIAL by design: the `DDiskStart` stutter mirrors the SC UART idle
step) and (ii) every 1-byte UART MMIO read is realizable by SOME received value and every 1-byte
UART MMIO write is absorbed (the real content: `uartMmioReadReducible` /
`uartMmioWriteReducible`, offset arithmetic + the UART totality lemmas).
`devConsistentReducible`: `DevConsistent GV → devReducible GV`.  PLIC (4-byte window) and virtio
are NOT covered by (ii) — RESIDUAL.

§2 `gvw` — hart 0 writes RAM byte 0, fences rw,rw, then writes THR (1-byte MMIO write of `b1`
inserted after the fence, position 2); the device agent (index 1, empty RAM row) transmits `b1`
(`DUartTx`).  Device order = [THR write; transmit].  PROVED: `gvwCat`, `gvwDev` (every
`DevConsistent` clause; `dcIo` exercised with a real fence in the row), `gvwConsistent`,
`gvwHasDeviceEvent`, `gvwConsole` (via `dreplayUartAcc`: the console trace is exactly `[b1]`),
`gvwUartTrace` (the same for `gdvUartTrace`).

DESIGN NOTE (DMA rows are FOREIGN writes into kernel buffers; tokens must flow kernel → disk
along the submit chain and back along the completion chain, over the `dcIo` edges; open points
(a) the disk agent runs no WPd — a device invariant must discharge its owned-write obligations,
(b) DMA writes need the `owned_write`/`gload_value` treatment, (c) `DWire` must be placed by the
hart's row emitter at the trap boundary) — carries over unchanged.

## Deviations from Rocq

1. NAMES: camelCase (map below); `Arch.pa` ↦ `PAddr`; `bv 8` ↦ `BitVec (8 * 1)` in the MMIO
   labels (`Dlbl.DMmioR/W pa n` carry `BitVec (8 * n)`); `is_Some` ↦ `isSome = true`;
   `dev0_state` ↦ `AxDevGraph.dev0State`.  File-qualified (duplicated Rocq names):
   `AxDevGraphWit.inUartOff`, `AxDevGraphWit.devReducible`, `AxDevGraphWit.imgw`.
2. THE DEVICE MODEL is Lean's two-UART fabric (`AxDevGraph` deviation 2): "in the UART window"
   (`in_uart (uint pa) = true`) ↦ `devDecode pa = some (.uart pt, off)` (any port, any offset);
   `devStateReducible`'s clause (ii) quantifies `pa pt off` with that premise.
   `AxDevGraphWit.inUartOff` concludes `off < uartSize` (Rocq `0 ≤ a - uart_base < uart_size`)
   and is `AxDevGraph.inUartOff`.  The witness's console is port `.uart0`; `Uart.acc`/`.out` of
   `d.st (.uart .uart0)` stand for Rocq `uart_acc (duart d)`.
3. `thr_pa := Z_to_bv 64 uart_base` ↦ `thrPa := BitVec.ofNat 64 0x10000000`; `thr_pa_uint`
   ↦ `thrPaUint : thrPa.toNat = uartBase .uart0`, plus the Lean-only decode fact
   `AxDevGraphWit.thrPaDecode : devDecode thrPa = some (.uart .uart0, 0)`.
4. `gvw_room`: Rocq `length (omap dlbl_thr …) ≤ uart_fifo_depth` ↦ the same with
   `dlblThr .uart0` and `Uart.fifoDepth`; `gvw_uart_ok` ↦ `∀ l ∈ …, uartOk .uart0 l`.
5. `vm_compute` ↦ `decide +kernel`.

**Rocq → Lean name map.**  `in_uart_off` `AxDevGraphWit.inUartOff`, `uart_mmio_read_reducible`
`uartMmioReadReducible`, `uart_mmio_write_reducible` `uartMmioWriteReducible`,
`dev_state_reducible` `devStateReducible`, `dev_state_reducible_all` `devStateReducibleAll`,
`dev_reducible` `AxDevGraphWit.devReducible`, `dreplay_take` `dreplayTake`,
`dev_consistent_reducible` `devConsistentReducible`, `imgw` `AxDevGraphWit.imgw`, `thr_pa`
`thrPa`, `thr_pa_uint` `thrPaUint`, `gvw_gd` `gvwGd`, `gvw` `gvw`, `gvw_cat` `gvwCat`,
`gvw_replay` `gvwReplay`, `gvw_dev` `gvwDev`, `gvw_consistent` `gvwConsistent`,
`gvw_has_device_event` `gvwHasDeviceEvent`, `gvw_uart_ok` `gvwUartOk`, `gvw_room` `gvwRoom`,
`gvw_console` `gvwConsole`, `gvw_uart_trace` `gvwUartTrace`.  Lean-only:
`AxDevGraphWit.thrPaDecode`, `AxDevGraphWit.gvwLbls`.

**Not ported:** nothing.
-/
import Weak.AxDevGraph

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! ## 1. Device reducibility -/

/-- The UART window decodes exactly the offsets `[0, uartSize)` (deviation 2). -/
theorem AxDevGraphWit.inUartOff (pa : PAddr) (pt : UartId) (off : Nat) :
    devDecode pa = some (.uart pt, off) → off < uartSize :=
  AxDevGraph.inUartOff pa pt off

/-- A 1-byte MMIO read in the UART window is realizable by SOME received value. -/
theorem uartMmioReadReducible (d : DevStates) (pa : PAddr) (pt : UartId) (off : Nat) :
    devDecode pa = some (.uart pt, off) →
    ∃ (v : BitVec (8 * 1)) (d' : DevStates), AxDevGraph.dstep d (.DMmioR pa 1 v) = some d' := by
  intro hdec
  obtain ⟨b, u', hr⟩ := AxDevGraph.uartReadTotal (d.st (.uart pt)) off
    (AxDevGraphWit.inUartOff _ _ _ hdec)
  refine ⟨BitVec.setWidth (8 * 1) b, d.set (.uart pt) u', ?_⟩
  simp only [AxDevGraph.dstep, devRead, hdec, devSig, Uart.sig, Uart.readN]
  simp only [true_or, ↓reduceIte, hr]
  simp

/-- A 1-byte MMIO write in the UART window is always absorbed. -/
theorem uartMmioWriteReducible (d : DevStates) (pa : PAddr) (b : BitVec (8 * 1)) (pt : UartId)
    (off : Nat) :
    devDecode pa = some (.uart pt, off) →
    ∃ d' : DevStates, AxDevGraph.dstep d (.DMmioW pa 1 b) = some d' := by
  intro hdec
  obtain ⟨u', hw⟩ := AxDevGraph.uartWriteTotal (d.st (.uart pt)) off (b.extractLsb' 0 8)
    (AxDevGraphWit.inUartOff _ _ _ hdec)
  refine ⟨d.set (.uart pt) u', ?_⟩
  simp only [AxDevGraph.dstep, devWrite, hdec, devSig, Uart.sig, Uart.writeN]
  simp only [true_or, ↓reduceIte, hw]
  rfl

/-- REDUCIBILITY OF A DEVICE STATE: (i) an enabled device-side step; (ii) the UART-window MMIO
arms of every hart are realizable. -/
def devStateReducible (d : DevStates) : Prop :=
  (∃ l, dlblDevside l = true ∧ (AxDevGraph.dstep d l).isSome = true) ∧
  (∀ (pa : PAddr) (pt : UartId) (off : Nat), devDecode pa = some (.uart pt, off) →
     (∃ (v : BitVec (8 * 1)) (d' : DevStates), AxDevGraph.dstep d (.DMmioR pa 1 v) = some d') ∧
     (∀ b : BitVec (8 * 1), ∃ d' : DevStates, AxDevGraph.dstep d (.DMmioW pa 1 b) = some d'))

theorem devStateReducibleAll (d : DevStates) : devStateReducible d :=
  ⟨⟨.DDiskStart, rfl, rfl⟩, fun pa pt off hdec =>
    ⟨uartMmioReadReducible d pa pt off hdec,
     fun b => uartMmioWriteReducible d pa b pt off hdec⟩⟩

/-- DEVICE REDUCIBILITY OF A GRAPH: every prefix of the device order replays from power-on to a
reducible state. -/
def AxDevGraphWit.devReducible (GV : GdexecDev) : Prop :=
  ∀ p, p ≤ GV.gvDord.length →
    ∃ d, dreplay AxDevGraph.dev0State ((gvDordLbls GV).take p) = some d ∧ devStateReducible d

theorem dreplayTake (d : DevStates) (ls : List Dlbl) (d' : DevStates) (p : Nat) :
    dreplay d ls = some d' → ∃ dp, dreplay d (ls.take p) = some dp := by
  intro hr
  rw [← List.take_append_drop p ls, dreplayApp] at hr
  cases h : dreplay d (ls.take p) with
  | some dp => exact ⟨dp, rfl⟩
  | none => rw [h] at hr; exact absurd hr (by simp)

theorem devConsistentReducible (GV : GdexecDev) :
    DevConsistent GV → AxDevGraphWit.devReducible GV := by
  intro Hc p _
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 Hc.dcReplay
  obtain ⟨dp, hp⟩ := dreplayTake _ _ _ p hd
  exact ⟨dp, hp, devStateReducibleAll dp⟩

/-! ## 2. The witness: one THR write, one transmit -/

def AxDevGraphWit.imgw : Image := fun _ => some b0

/-- The UART THR address (port `.uart0`, offset 0). -/
def thrPa : PAddr := BitVec.ofNat 64 0x10000000

theorem thrPaUint : thrPa.toNat = uartBase .uart0 := by decide +kernel

theorem AxDevGraphWit.thrPaDecode : devDecode thrPa = some (.uart .uart0, 0) := by
  decide +kernel

/-- RAM graph: hart 0 = `[W 0:=b1; fence rw,rw]`, agent 1 (the device) has an empty RAM row;
gmo = the one write. -/
def gvwGd : Gdexec :=
  ⟨⟨AxDevGraphWit.imgw, [[LStore false 0 [b1] .WCplain, LFence true true true true], []],
    [(0, 0)]⟩, [], []⟩

def gvw : GdexecDev :=
  ⟨gvwGd, [[(2, .DMmioW thrPa 1 b1)], [(0, .DUartTx .uart0 b1)]], [(0, 0), (1, 0)], 1⟩

theorem gvwCat : rvwmoCatConsistent gvwGd := catConsistentBSound _ (by decide +kernel)

theorem AxDevGraphWit.gvwLbls : gvDordLbls gvw = [.DMmioW thrPa 1 b1, .DUartTx .uart0 b1] := rfl

/-- The device order replays: the THR write pushes `b1` onto the tx FIFO, the transmit pops it. -/
theorem gvwReplay : (dreplay AxDevGraph.dev0State (gvDordLbls gvw)).isSome = true := by
  rw [AxDevGraphWit.gvwLbls]; decide +kernel

theorem gvwDev : DevConsistent gvw where
  dcNodup := by decide
  dcMem := by
    intro e
    obtain ⟨a, j⟩ := e
    rcases a with _ | _ | a <;> rcases j with _ | j <;>
      simp [gvDitem, gvw]
  dcPo := by
    intro p1 p2 i j1 j2 hp h1 h2
    rcases p1 with _ | _ | p1 <;> rcases p2 with _ | _ | p2 <;>
      simp [gvw] at h1 h2 hp <;> omega
  dcIns := by
    intro i j1 j2 k1 k2 _ h1 h2
    rcases i with _ | _ | i <;> rcases j1 with _ | j1 <;> rcases j2 with _ | j2 <;>
      simp [gvDins, gvDitem, gvw] at h1 h2 <;> subst h1 h2 <;>
      simp [gvRam, gvw, gvwGd]
  dcKind := by
    intro e l hl
    obtain ⟨a, j⟩ := e
    rcases a with _ | _ | a <;> rcases j with _ | j <;>
      simp [gvDlbl, gvDitem, gvw] at hl <;> subst hl <;> simp [dlblDevside, gvw]
  dcReplay := gvwReplay
  dcIo := by
    -- the device agent has no fence, so `b` is hart 0, whose only fence is at position 1, and
    -- its THR write is inserted at 2 > 1
    intro a b kx kf1 j1 k1 j2 k2 kf2 ky p1 p2 _ _ _ _ _ _ _ _ hi2 hle2 hf2 _ _
    exfalso
    rcases b with _ | _ | b <;> rcases kf2 with _ | _ | kf2 <;>
      simp [fullFenceAt, gxLbl, gvRam, gvw, gvwGd] at hf2
    rcases j2 with _ | j2 <;> simp [gvDins, gvDitem, gvw] at hi2
    omega

theorem gvwConsistent : gdvConsistent gvw := ⟨gvwCat, gvwDev⟩

/-- NON-DEGENERACY: the device order contains a DEVICE-SIDE event, on the device agent. -/
theorem gvwHasDeviceEvent :
    gvDordLbls gvw = [.DMmioW thrPa 1 b1, .DUartTx .uart0 b1] ∧
    gvDlbl gvw (gvw.gvDev, 0) = some (.DUartTx .uart0 b1) ∧
    dlblDevside (.DUartTx .uart0 b1) = true :=
  ⟨rfl, rfl, rfl⟩

/-- The witness obeys the UART discipline and cannot overflow the FIFO. -/
theorem gvwUartOk : ∀ l ∈ gvDordLbls gvw, uartOk .uart0 l := by
  rw [AxDevGraphWit.gvwLbls]
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · intro off h; rw [AxDevGraphWit.thrPaDecode] at h; cases h; exact ⟨rfl, rfl⟩
  · trivial

theorem gvwRoom : ((gvDordLbls gvw).filterMap (dlblThr .uart0)).length ≤ Uart.fifoDepth := by
  rw [AxDevGraphWit.gvwLbls]; decide +kernel

/-- THE CONSOLE TRACE, via the UART replay theorem. -/
theorem gvwConsole (d : DevStates) :
    dreplay AxDevGraph.dev0State (gvDordLbls gvw) = some d →
    Uart.acc (d.st (.uart .uart0)) = [b1] := by
  intro hd
  obtain ⟨hdl, htx, hacc0⟩ := dev0Uart .uart0
  have hroom : (AxDevGraph.dev0State.st (.uart .uart0)).tx.length +
      ((gvDordLbls gvw).filterMap (dlblThr .uart0)).length ≤ Uart.fifoDepth := by
    rw [htx]; simpa using gvwRoom
  obtain ⟨hacc, -⟩ := dreplayUartAcc .uart0 _ _ _ hd gvwUartOk hdl hroom
  rw [hacc, hacc0, List.nil_append, AxDevGraphWit.gvwLbls]
  decide +kernel

/-- SATISFIABILITY CERTIFICATE for `gdvUartTrace`: its conclusion on `gvw` is the concrete
console trace `[b1]`, of which hart 0's own THR bytes are a subsequence. -/
theorem gvwUartTrace :
    ∃ d', dreplay AxDevGraph.dev0State (gvDordLbls gvw) = some d' ∧
      Uart.acc (d'.st (.uart .uart0)) = [b1] ∧
      ((gvDrow gvw 0).filterMap (dlblThr .uart0 ∘ Prod.snd)).Sublist
        (Uart.acc (d'.st (.uart .uart0))) := by
  obtain ⟨d', hr, hacc, hsub⟩ := gdvUartTrace .uart0 gvw gvwDev gvwUartOk gvwRoom
  refine ⟨d', hr, ?_, hsub 0⟩
  rw [hacc, AxDevGraphWit.gvwLbls]
  decide +kernel

end Weak
