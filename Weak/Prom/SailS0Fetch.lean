/-
Weak/Prom: **spike S-0, the fetch-doom kill** (`~/dev/weak-orch/promising/SailS0_prompt.txt` item (5);
`~/dev/weak-orch/promising/SailScope.md` §1 L3 (b), §4 R4; owner rulings [OWN.P20], [OWN.P21]).

SailScope §1 L3 (b) proposed the fetch rule for never-written text as a FROZEN-TEXT invariant: an Iris invariant holds
`pend t` for every message `t` overlapping the text; a fetch that returns a non-image byte takes that `pend` and DOOMS
it (`OA.doom`/`OA.doomD`), and the doom box (`OA.doomInv`) is sound because "in a valid run every `t` is fulfilled,
hence shot, so the box cannot hold any `pend s`" (OwnAWp.lean header).  That soundness argument needs the witness
`s` never to be fulfilled after the doom.  A doomed hart keeps running the code it fetched, and machine v2 lets that
code fulfil `s`: the fetch arm (Machine.lean `memStep.fetch`, `fetchByteOk`) reads ANY message of the current log —
also an outstanding promise of the fetching hart itself — and orders nothing after it except the current
instruction's own accesses (`wIfv`, PA-1f), which `LInstr` resets (`memStep.instr`); register writes and control
labels carry only their SYNTACTIC sources (Emit.lean `regSrcs`, `depsCtrl`), never the fetch view.

`fetch_own_then_fulfil` is the memory-half core of that cycle, from a hart's initial state: it fetches the bytes of
its OWN OUTSTANDING promise `t`, retires the instruction, and in a later instruction fulfils `t` with a plain store
(COH and EXT hold: nothing the fetch did reaches the store's pre-view).  So "the fetched value is the image's, or the
run is invalid" is false in machine v2, and the fetch-doom rule is unprovable.  For the assembled `mpFF` this gives
a VALID run with hart 1's forbidden outcome (PROGRESS-SailS0.md, "The counterexample run"), so `sail_mpFF` as briefed
is false.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.Machine

namespace Weak.Prom.SailS0

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image)
open Weak.Prom
open PLabel

/-- The answers of a fetch that reads every byte of the message at `t`. -/
def tvsAt (t : Nat) (data : List (BitVec 8)) : List (Nat × BitVec 8) := data.map (fun b => (t, b))

/-- A message's bytes are what memory holds at its timestamp. -/
theorem memByte_msg {img : Image} {log : List PMsg} {t : Nat} {m : PMsg} (ht : 1 ≤ t)
    (hm : log[t - 1]? = some m) (j : Nat) (hj : j < m.data.length) :
    memByte img log t (m.pa + j) = some m.data[j] := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hm
  simp only [memByte, hm, Option.bind_some, PMsg.byteAt]
  rw [if_pos (by omega)]
  have : (m.pa + (j : Int) - m.pa).toNat = j := by omega
  rw [this, List.getElem?_eq_getElem hj]

/-- With no FENCE.I floor (`wIfl = 0`), a fetch may return the bytes of any message of the log. -/
theorem fetch_msg_ok {img : Image} {log : List PMsg} {ws : PState} (hfl : ws.wIfl = 0) (t : Nat) :
    ∀ (l : List (BitVec 8)) (a : Int), (∀ j (hj : j < l.length), memByte img log t (a + j) = some l[j]) →
      bytesAll (fetchByteOk img log ws) a (tvsAt t l)
  | [], _, _ => trivial
  | b :: l, a, h => by
    have h0 := h 0 (by simp)
    rw [List.getElem_cons_zero, Int.natCast_zero, Int.add_zero] at h0
    refine ⟨⟨h0, ?_⟩, ?_⟩
    · rw [hfl]; rintro ⟨t', h1, h2, _⟩; omega
    · refine fetch_msg_ok hfl t l (a + 1) (fun j hj => ?_)
      have := h (j + 1) (by simp; omega)
      rw [show a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) by omega]
      simpa using this

/-- Nothing was written at an address whose coherence floor is the initial one. -/
theorem cohBelow_empty (ws : PState) (hc : ws.wCoh = ∅) (t : Nat) (ht : 1 ≤ t) :
    ∀ (n : Nat) (a : Int), cohBelow ws a n t
  | 0, _ => trivial
  | n + 1, a => ⟨by unfold coh; rw [hc, lookupEmpty]; simp; omega, cohBelow_empty ws hc t ht n (a + 1)⟩

/-- **THE THIN-AIR FETCH CYCLE, memory half** (the fetch-doom kill of spike S-0).  Agent `i` in its initial state,
holding the outstanding promise `t` of a plain write `m`, may (1) FETCH `m`'s bytes from `t` (`LIFetch`), (2) end
the instruction (`LInstr`), and (3) in a later instruction FULFIL `t` with a plain store of the same bytes (`LStore`
with no address/data source, e.g. a register written by the fetched instruction itself: Emit.lean's `LRegW`
sources are syntactic, so they never carry the fetch view).  The store's EXT (`stPreA … < t`) and COH hold: the
fetch raised only `wIfr`/`wIfv`, and `LInstr` reset `wIfv`.  So a hart may execute code it fetched from a message
that it writes only later, in a computation steered by that very code. -/
theorem fetch_own_then_fulfil (img : Image) (log : List PMsg) (i t : Nat) (prom : GSet Nat) (m : PMsg)
    (ht : 1 ≤ t) (hm : log[t - 1]? = some m) (hmk : m = ⟨m.pa, m.data, some i, .plain⟩) (htp : t ∈ prom) :
    let ws1 : PState := { psInit with
      wIfr := max psInit.wIfr (bytesMax (fun _ t => t) m.pa (tvsAt t m.data))
      wIfv := max psInit.wIfv (fetchView log i prom m.pa (tvsAt t m.data)) }
    let ws2 : PState := { ws1 with wLdv := 0, wRmw := none, wIfv := 0 }
    memStep img log i prom psInit (LIFetch m.pa (tvsAt t m.data)) none ws1 prom ∧
    memStep img log i prom ws1 LInstr none ws2 prom ∧
    memStep img log i prom ws2 (LStore false false m.pa m.data [] []) (some t)
      (acqPost (storeRun ws2 false (srcsView ws2 []) (max (srcsView ws2 []) (srcsView ws2 [])) m.pa
        m.data.length t) false t) (prom \ {t}) := by
  intro ws1 ws2
  refine ⟨memStep.fetch prom psInit m.pa _ ?_, memStep.instr prom ws1, ?_⟩
  · exact fetch_msg_ok rfl t m.data m.pa (fun j hj => memByte_msg ht hm j hj)
  · refine memStep.store prom ws2 false false m.pa m.data [] [] t htp ?_ (cohBelow_empty ws2 rfl t ht _ _) ?_
    · rw [hm]; exact congrArg some hmk
    · show max (max 0 (max 0 (max 0 (max psInit.wVcap (max psInit.wVwNew 0))))) 0 < t
      simp [psInit]; omega

/-- The instance at the assembled `mpFF`'s first text word (`codeBase 0 = 0x80400000`, MachSail.lean:43): hart 0
promises `addi x5,x5,1` (`0x00128293`, little-endian) there, fetches it, and later stores it back — the step the
counterexample run of PROGRESS-SailS0.md repeats for each of its text messages. -/
example (img : Image) (prom : GSet Nat) (htp : 1 ∈ prom) :
    let m : PMsg := ⟨0x80400000, [0x93#8, 0x82#8, 0x12#8, 0x00#8], some 0, .plain⟩
    memStep img [m] 0 prom psInit (LIFetch m.pa (tvsAt 1 m.data)) none
      { psInit with
        wIfr := max psInit.wIfr (bytesMax (fun _ t => t) m.pa (tvsAt 1 m.data))
        wIfv := max psInit.wIfv (fetchView [m] 0 prom m.pa (tvsAt 1 m.data)) } prom := by
  intro m
  exact (fetch_own_then_fulfil img [m] 0 1 prom m (by omega) rfl rfl htp).1

end Weak.Prom.SailS0

#print axioms Weak.Prom.SailS0.fetch_own_then_fulfil
