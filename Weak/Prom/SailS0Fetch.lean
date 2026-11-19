/-
Weak/Prom: **spike S-0, the fetch-doom kill** (`~/dev/weak-orch/promising/SailS0_prompt.txt` item (5);
`~/dev/weak-orch/promising/SailScope.md` §1 L3 (b), §4 R4; owner rulings [OWN.P20], [OWN.P21]) — [MachZiccid]
REPLACED BY ITS IMPOSSIBILITY ([OWN.P22] "Ziccid rule now").

The S-0 finding (PROGRESS-SailS0.md): machine v2's Zifencei-only fetch arm read ANY message of the current log —
also an outstanding promise of the fetching hart — and ordered nothing after the fetch except the current
instruction's own accesses (`wIfv`, reset at `LInstr`).  Its lemma `fetch_own_then_fulfil` showed the memory half
of the thin-air cycle: from `psInit`, fetch the bytes of the hart's own outstanding promise `t`, retire (`LInstr`),
fulfil `t` with a plain store in a later instruction.

[MachZiccid] Under the Ziccid fetch arm (Machine.lean `memStep.fetch`) that lemma is NOT provable: a fetch at fetch
view `vf` returns bytes at `t ≤ vf` and sets `wIfv := vf`; `LInstr` keeps `wIfv`; every fulfil has `wIfv < ts`
(Ziccid_fetch_before_access with the monotone view).  `fetch_own_then_fulfil_impossible` below is the replaced
lemma's exact shape (fetch `tvsAt t m.data`, `LInstr`, a write fulfilling `t`) with `False` as conclusion, for ANY
start state and ANY write label; the run-level forms (any interleaving, any distance, two cooperating harts) are
MachZiccidCyc.lean `no_fetch_own_then_fulfil` / `no_fetch_cross`.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachZiccidCyc

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

/-- **[MachZiccid] THE THIN-AIR FETCH CYCLE IS IMPOSSIBLE, memory half** (replaces `fetch_own_then_fulfil`).  Agent
`i`, from ANY state, fetches the bytes of a non-empty message at timestamp `t` (its own outstanding promise or any
other), ends the instruction, and then no write step of `i` (store, SC, AMO, CMO — any label) can fulfil `t`:
the fetch puts `t ≤ vf = wIfv`, `LInstr` keeps `wIfv`, and the fulfil needs `wIfv < t`. -/
theorem fetch_own_then_fulfil_impossible {img : Image} {log : List PMsg} {i t : Nat} {m : PMsg}
    (hne : m.data ≠ []) {ws0 ws1 ws2 ws3 : PState} {prom0 prom1 prom2 prom3 : GSet Nat} {l : PLabel}
    (h1 : memStep img log i prom0 ws0 (LIFetch m.pa (tvsAt t m.data)) none ws1 prom1)
    (h2 : memStep img log i prom1 ws1 LInstr none ws2 prom2)
    (h3 : memStep img log i prom2 ws2 l (some t) ws3 prom3) : False := by
  have hsrc := Ziccid.memStep_fetch_src h1
  have hmono := Ziccid.memStep_ifv_mono h2
  have hgt := Ziccid.memStep_fulfil_gt h3
  obtain ⟨b, bs, e⟩ : ∃ b bs, m.data = b :: bs := by
    cases hd : m.data with
    | nil => exact absurd hd hne
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [e] at hsrc
  have : t ≤ ws1.wIfv := hsrc.1
  omega

/-- The instance at the assembled `mpFF`'s first text word (`codeBase 0 = 0x80400000`, MachSail.lean:43): hart 0's
promise of `addi x5,x5,1` (`0x00128293`, little-endian) there, once fetched, can never be fulfilled by hart 0 —
the first step of PROGRESS-SailS0.md's counterexample run is gone. -/
example (img : Image) (log : List PMsg) (ws0 ws1 ws2 ws3 : PState) (p0 p1 p2 p3 : GSet Nat) (l : PLabel) :
    let m : PMsg := ⟨0x80400000, [0x93#8, 0x82#8, 0x12#8, 0x00#8], some 0, .plain⟩
    memStep img log 0 p0 ws0 (LIFetch m.pa (tvsAt 1 m.data)) none ws1 p1 →
    memStep img log 0 p1 ws1 LInstr none ws2 p2 →
    ¬ memStep img log 0 p2 ws2 l (some 1) ws3 p3 := by
  intro m h1 h2 h3
  exact fetch_own_then_fulfil_impossible (m := m) (by simp [m]) h1 h2 h3

end Weak.Prom.SailS0

#print axioms Weak.Prom.SailS0.fetch_own_then_fulfil_impossible
