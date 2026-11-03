/-
Weak/Prom: **trace-invariant shapes for the litmus rows** (stage S2; plan rev 7 §2 "Ψ chosen by the proof").

A litmus hart's Ψ is stated over its memory entries (`memEv`, CoreKit.lean) as a prefix-closed pattern: `q1`, `q2`,
`q3`, `q4` say "the memory entries so far are a prefix of `e0, e1, …` with these facts", where each fact may mention
the earlier entries (the EXT / coherence / fence chains of the hart, stated as timestamp orders or as the absence
of a write in a window, plan §2 (P3)).  Entry shapes `isLd`, `isSt`, `isRmw` pin the label (address, data, sources)
and leave the memory's answers free; `src0`, `val0`, `tsOf` read byte 0's source and value, and the fulfil
timestamp.  `obsLoad_memEv` reads an outcome off the memory entries (plan §0 [R6.2] `run.obsLoad`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreKitV

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

/-! ## 1. Prefix patterns -/

/-- At most one memory entry, with `P0`. -/
def q1 (P0 : PEv → Prop) : Trace → Prop
  | [] => True
  | [e0] => P0 e0
  | _ => False

/-- At most two memory entries: `P0 e0`, then `P1 e0 e1`. -/
def q2 (P0 : PEv → Prop) (P1 : PEv → PEv → Prop) : Trace → Prop
  | [] => True
  | [e0] => P0 e0
  | [e0, e1] => P0 e0 ∧ P1 e0 e1
  | _ => False

/-- At most three memory entries. -/
def q3 (P0 : PEv → Prop) (P1 : PEv → PEv → Prop) (P2 : PEv → PEv → PEv → Prop) : Trace → Prop
  | [] => True
  | [e0] => P0 e0
  | [e0, e1] => P0 e0 ∧ P1 e0 e1
  | [e0, e1, e2] => P0 e0 ∧ P1 e0 e1 ∧ P2 e0 e1 e2
  | _ => False

/-- At most four memory entries. -/
def q4 (P0 : PEv → Prop) (P1 : PEv → PEv → Prop) (P2 : PEv → PEv → PEv → Prop)
    (P3 : PEv → PEv → PEv → PEv → Prop) : Trace → Prop
  | [] => True
  | [e0] => P0 e0
  | [e0, e1] => P0 e0 ∧ P1 e0 e1
  | [e0, e1, e2] => P0 e0 ∧ P1 e0 e1 ∧ P2 e0 e1 e2
  | [e0, e1, e2, e3] => P0 e0 ∧ P1 e0 e1 ∧ P2 e0 e1 e2 ∧ P3 e0 e1 e2 e3
  | _ => False

/-- No memory entry (a hart outside the domain). -/
def q0 : Trace → Prop := fun ev => ev = []

/-! ## 2. Entry shapes and accessors -/

/-- The answers of an entry. -/
def tvsOf (e : PEv) : List (Nat × BitVec 8) := readsOf e.1

/-- Byte 0's source timestamp. -/
def src0 (e : PEv) : Nat := ((tvsOf e).head?.map Prod.fst).getD 0

/-- Byte 0's value. -/
def val0 (e : PEv) : Nat := ((tvsOf e).head?.map (fun tv => tv.2.toNat)).getD 0

/-- The fulfil timestamp. -/
def tsOf (e : PEv) : Nat := e.2.getD 0

/-- A plain `n`-byte load at `a` with address sources `asrc`. -/
def isLd (a : Int) (n : Nat) (asrc : List Dsrc) (e : PEv) : Prop :=
  ∃ tvs, e = (LLoad false false a tvs asrc, none) ∧ tvs.length = n

/-- A plain store of `d` at `a`. -/
def isSt (a : Int) (d : List (BitVec 8)) (asrc vsrc : List Dsrc) (e : PEv) : Prop :=
  ∃ t, 0 < t ∧ e = (LStore false false a d asrc vsrc, some t)

/-- A fused AMO at `a` (`n` bytes) writing `dat tvs`. -/
def isRmw (aq rl : Bool) (a : Int) (n : Nat) (dat : List (Nat × BitVec 8) → List (BitVec 8)) (asrc vsrc : List Dsrc)
    (e : PEv) : Prop :=
  ∃ tvs t, 0 < t ∧ e = (LRmw aq rl a tvs (dat tvs) asrc vsrc, some t) ∧ tvs.length = n

theorem isLd_mk (a : Int) (asrc : List Dsrc) (tvs : List (Nat × BitVec 8)) :
    isLd a tvs.length asrc (LLoad false false a tvs asrc, none) := ⟨tvs, rfl, rfl⟩

theorem src0_ld {aq rl : Bool} {a : Int} {t : Nat} {v : BitVec 8} {r : List (Nat × BitVec 8)} {asrc : List Dsrc}
    {o : Option Nat} : src0 (LLoad aq rl a ((t, v) :: r) asrc, o) = t := rfl

theorem src0_rmw {aq rl : Bool} {a : Int} {t : Nat} {v : BitVec 8} {r : List (Nat × BitVec 8)} {d : List (BitVec 8)}
    {asrc vsrc : List Dsrc} {o : Option Nat} : src0 (LRmw aq rl a ((t, v) :: r) d asrc vsrc, o) = t := rfl

theorem tsOf_some {l : PLabel} {t : Nat} : tsOf (l, some t) = t := rfl

/-! ## 3. Reading the patterns back -/

theorem q1_cases {P0 : PEv → Prop} {ev : Trace} (h : q1 P0 ev) : ev = [] ∨ ∃ e0, ev = [e0] ∧ P0 e0 := by
  match ev, h with
  | [], _ => exact .inl rfl
  | [e0], h => exact .inr ⟨e0, rfl, h⟩

theorem q2_cases {P0 : PEv → Prop} {P1 : PEv → PEv → Prop} {ev : Trace} (h : q2 P0 P1 ev) :
    ev = [] ∨ (∃ e0, ev = [e0] ∧ P0 e0) ∨ ∃ e0 e1, ev = [e0, e1] ∧ P0 e0 ∧ P1 e0 e1 := by
  match ev, h with
  | [], _ => exact .inl rfl
  | [e0], h => exact .inr (.inl ⟨e0, rfl, h⟩)
  | [e0, e1], h => exact .inr (.inr ⟨e0, e1, rfl, h⟩)

theorem q3_cases {P0 : PEv → Prop} {P1 : PEv → PEv → Prop} {P2 : PEv → PEv → PEv → Prop} {ev : Trace}
    (h : q3 P0 P1 P2 ev) :
    ev = [] ∨ (∃ e0, ev = [e0] ∧ P0 e0) ∨ (∃ e0 e1, ev = [e0, e1] ∧ P0 e0 ∧ P1 e0 e1) ∨
      ∃ e0 e1 e2, ev = [e0, e1, e2] ∧ P0 e0 ∧ P1 e0 e1 ∧ P2 e0 e1 e2 := by
  match ev, h with
  | [], _ => exact .inl rfl
  | [e0], h => exact .inr (.inl ⟨e0, rfl, h⟩)
  | [e0, e1], h => exact .inr (.inr (.inl ⟨e0, e1, rfl, h⟩))
  | [e0, e1, e2], h => exact .inr (.inr (.inr ⟨e0, e1, e2, rfl, h⟩))

theorem q4_cases {P0 : PEv → Prop} {P1 : PEv → PEv → Prop} {P2 : PEv → PEv → PEv → Prop}
    {P3 : PEv → PEv → PEv → PEv → Prop} {ev : Trace} (h : q4 P0 P1 P2 P3 ev) :
    ev = [] ∨ (∃ e0, ev = [e0] ∧ P0 e0) ∨ (∃ e0 e1, ev = [e0, e1] ∧ P0 e0 ∧ P1 e0 e1) ∨
      (∃ e0 e1 e2, ev = [e0, e1, e2] ∧ P0 e0 ∧ P1 e0 e1 ∧ P2 e0 e1 e2) ∨
      ∃ e0 e1 e2 e3, ev = [e0, e1, e2, e3] ∧ P0 e0 ∧ P1 e0 e1 ∧ P2 e0 e1 e2 ∧ P3 e0 e1 e2 e3 := by
  match ev, h with
  | [], _ => exact .inl rfl
  | [e0], h => exact .inr (.inl ⟨e0, rfl, h⟩)
  | [e0, e1], h => exact .inr (.inr (.inl ⟨e0, e1, rfl, h⟩))
  | [e0, e1, e2], h => exact .inr (.inr (.inr (.inl ⟨e0, e1, e2, rfl, h⟩)))
  | [e0, e1, e2, e3], h => exact .inr (.inr (.inr (.inr ⟨e0, e1, e2, e3, rfl, h⟩)))

/-- An outcome read off the memory entries. -/
theorem obsLoad_memEv {P D : Type} (run : PFRun P D) (h k : Nat) :
    run.obsLoad h k = ((loadsOf (memEv (run.trace h)))[k]?).map obsOf := by
  unfold PFRun.obsLoad; rw [loadsOf_memEv]

/-- The value of a load answer, byte 0. -/
theorem obsOf_b0 {tv : Nat × BitVec 8} {r : List (Nat × BitVec 8)} {n : Nat} (h : obsOf (tv :: r) = n) :
    tv.2.toNat = n % 256 := by
  simp only [obsOf, List.foldr_cons] at h
  have := tv.2.isLt
  omega

/-- The byte a message writes, from its base and data (for `decide` on concrete labels). -/
theorem byteAt_pd {m : PMsg} {b : Int} {d : List (BitVec 8)} (hpa : m.pa = b) (hd : m.data = d) (a : Int) :
    m.byteAt a = if b ≤ a then d[(a - b).toNat]? else none := by
  rw [byteAt_eq, hpa, hd]

/-- A message with data writes its base byte. -/
theorem byteAt_base_isSome (m : PMsg) (h : 0 < m.data.length) : (m.byteAt m.pa).isSome = true := by
  rw [byteAt_base]; rw [List.getElem?_eq_getElem h]; rfl

/-- A message that does not write `a` (decided on its base and data). -/
theorem byteAt_none_of {m : PMsg} {b : Int} {d : List (BitVec 8)} {a : Int} (hpa : m.pa = b) (hd : m.data = d)
    (h : (if b ≤ a then d[(a - b).toNat]? else none) = none) : m.byteAt a = none := by
  rw [byteAt_pd hpa hd]; exact h

/-- A message that writes `v` at `a` (decided on its base and data). -/
theorem byteAt_some_of {m : PMsg} {b : Int} {d : List (BitVec 8)} {a : Int} {v : BitVec 8} (hpa : m.pa = b)
    (hd : m.data = d) (h : (if b ≤ a then d[(a - b).toNat]? else none) = some v) : m.byteAt a = some v := by
  rw [byteAt_pd hpa hd]; exact h

/-- A load answer byte whose value differs from the image's is a message's byte. -/
theorem src_of_val {img : Image} {M : List PMsg} {t : Nat} {a : Int} {v b : BitVec 8}
    (hb : memByte img M t a = some v) (hi : img a = some b) (hne : v ≠ b) :
    ∃ k m, t = k + 1 ∧ M[k]? = some m ∧ m.byteAt a = some v := src_msg hb hi hne

/-- A load entry's answers, byte 0 first. -/
theorem isLd_cons {a : Int} {n : Nat} {asrc : List Dsrc} {e : PEv} (h : isLd a n asrc e) (hn : 0 < n) :
    ∃ t v r, e = (LLoad false false a ((t, v) :: r) asrc, none) ∧ r.length + 1 = n := by
  obtain ⟨tvs, rfl, hl⟩ := h
  cases tvs with
  | nil => simp at hl; omega
  | cons tv r => exact ⟨tv.1, tv.2, r, rfl, by simpa using hl⟩

/-- A load entry's byte 0 is the memory's (A0 (v)). -/
theorem kit_read0 {P D : Type} {run : PFRun P D} {M : List PMsg} (hwf : run.traceWf M) {h : Nat} {e : PEv}
    (he : e ∈ memEv (run.trace h)) {aq rl : Bool} {a : Int} {t : Nat} {v : BitVec 8} {r : List (Nat × BitVec 8)}
    {asrc : List Dsrc} {o : Option Nat} (hl : e = (LLoad aq rl a ((t, v) :: r) asrc, o)) :
    memByte run.cfg.pcImg M t a = some v := by
  subst hl; exact (kit_read hwf he rfl).1

/-- A store entry's message (A0 (v)). -/
theorem kit_msg {P D : Type} {run : PFRun P D} {M : List PMsg} (hwf : run.traceWf M) {h : Nat} {e : PEv}
    (he : e ∈ memEv (run.trace h)) {t : Nat} (ht : e.2 = some t) {b : Int} {d : List (BitVec 8)}
    (hw : labelWrite e.1 = some (b, d)) : ∃ m, M[t - 1]? = some m ∧ m.pa = b ∧ m.data = d :=
  write_msg hwf (mem_of_memEv he) ht hw

/-- The message at a timestamp `k + 1` holding byte `v` at `a`. -/
theorem memByte_succ {img : Image} {M : List PMsg} {k : Nat} {a : Int} {v : BitVec 8}
    (h : memByte img M (k + 1) a = some v) : ∃ m, M[k]? = some m ∧ m.byteAt a = some v := by
  simp only [memByte] at h
  exact Option.bind_eq_some_iff.1 h

/-! ## 4. Program states -/

theorem LPstep_prog {s s' : LP} {pc rd v : Nat} (h : LPstep s s' pc rd v) : s'.prog = s.prog := h.1
theorem LPstep_pc {s s' : LP} {pc rd v : Nat} (h : LPstep s s' pc rd v) : s'.pc = pc := h.2.1
theorem LPstep_q {s s' : LP} {pc rd v : Nat} (h : LPstep s s' pc rd v) : s'.q = [] := h.2.2.1
theorem LPstep_len {s s' : LP} {pc rd v : Nat} (h : LPstep s s' pc rd v) : s'.regs.length = s.regs.length := h.2.2.2.1

theorem LPstep_rd {s s' : LP} {pc rd v : Nat} (h : LPstep s s' pc rd v) (r : Nat) (hr : r ≠ rd ∨ rd = 0) :
    s'.rd r = s.rd r := by
  rw [h.2.2.2.2 r]; rw [if_neg (by omega)]

theorem LPstep_rd_eq {s s' : LP} {pc rd v : Nat} (h : LPstep s s' pc rd v) (h0 : rd ≠ 0) (hl : rd < s.regs.length) :
    s'.rd rd = v % two64 := by
  rw [h.2.2.2.2 rd]; rw [if_pos ⟨rfl, h0, hl⟩]

/-- Chaining `LPstep`: the next state's program, pc and queue. -/
theorem LPstep_at {s s' : LP} {pc rd v : Nat} {P : List Instr} {k : Nat} (h : LPstep s s' pc rd v)
    (hp : s.prog = P) (hc : pc = k) : s'.prog = P ∧ s'.pc = k ∧ s'.q = [] :=
  ⟨h.1.trans hp, h.2.1.trans hc, h.2.2.1⟩

/-- `li rd, v` writes `v`. -/
theorem li_val {s s' : LP} {pc rd v : Nat} (h : LPstep s s' pc rd (aluOp .add (s.rd 0) v)) (h0 : rd ≠ 0)
    (hl : rd < s.regs.length) (hv : v < two64) : s'.rd rd = v := by
  rw [LPstep_rd_eq h h0 hl]; simp [LP.rd, aluOp, Nat.mod_eq_of_lt hv]

/-- A swap AMO writes `rs2`'s value. -/
theorem amoD_swap (b : Nat) (tvs : List (Nat × BitVec 8)) : amoD .swap 4 b tvs = toBytes (b % 2 ^ 32) 4 := by
  simp [amoD, amoOp]

/-- The initial program state of hart `h` of a test. -/
theorem progs_get {T : Test} {h : Nat} {p : LP} (hp : (progs T)[h]? = some p) :
    p.prog = T.prog h ∧ p.pc = 0 ∧ p.q = [] ∧ p.regs.length = 32 ∧
    ∀ r, 0 < r → r < 32 → p.rd r = ((((T.regs0[h]?).getD []).lookup r).getD 0) % two64 := by
  unfold progs at hp
  rw [List.getElem?_map] at hp
  by_cases hh : h < T.harts.length
  · rw [List.getElem?_range hh] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    subst hp
    refine ⟨rfl, rfl, rfl, by simp, fun r h0 h32 => ?_⟩
    unfold LP.rd
    rw [if_neg (by omega)]
    simp only
    rw [List.getElem?_map, List.getElem?_range h32]
    rfl
  · rw [List.getElem?_eq_none (by simpa using hh)] at hp
    cases hp

end Weak.Prom.PF
