/-
Weak: **W9a (B) B5 r2 part (C), the part cycRun does not own — `tvB` ALONG THE HART'S REAL STEPS**
(plan rev 52 §D Q-B5-FETCH (r2-a), `PROGRESS-r2.md`).  Lean-only.

`tvPhrun`: along a hart run (`phrun`, no boundary / announce step) from a tree satisfying `tvB c P`
with a register file whose every register is `tvRk`-admitted (`tvRkAll`: `satp = kSatp b`,
`tlbIdOk`, boot-admitted), if every load / exclusive-load / i-cache label of the run carries bytes
the PTE filter admits (`labAnsOk`; a device read is never a walk slot when the walk's pages are RAM),
the run ends at a tree still satisfying `tvB c P` with a register file still `tvRkAll` (the tree's
writes are `tvRk`-admitted; the PLIC wire writes touch neither `satp` nor `tlb`).  The two run
premises are what cycRun (`tvRkAll` at the fetch, kept across the cycle) and the graph (`labAnsOk`
from `Xv6.kptTextAt` through W11's realization) owe.  Mirrors `PinFetchVal` §8.  Every helper is
`Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaAddr
import Weak.PinFetchVal

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinFetchPa
open SailCycleOrderK PinFetchPaFp

/-- The PTE filter on a label's address and bytes. -/
def tvAnsL (c : TCfg) (a : Int) (bs : List (BitVec 8)) : Prop :=
  ∀ (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)), paZ pa = a →
    bs = (List.range n).map (fun j => nthByte w j) → tvAns c pa n w

/-- **The run's read-answer premise**: every RAM read label carries filter-admitted bytes. -/
def labAnsOk (c : TCfg) : Wlabel → Prop
  | .LLoad _ _ a tvs _ => tvAnsL c a (tvs.map Prod.snd)
  | .LExLoad _ a tvs _ => tvAnsL c a (tvs.map Prod.snd)
  | .LIFetch a tvs => tvAnsL c a (tvs.map Prod.snd)
  | _ => True

/-- **The register file's premise**: every register `tvRk`-admitted. -/
def tvRkAll (c : TCfg) (rs : RegFile) : Prop := ∀ r, tvRk c r (rs r)

theorem tvRkAllSet {c : TCfg} (rs : RegFile) (r : Register) (v : RegisterType r) (h : tvRkAll c rs)
    (hv : tvRk c r v) : tvRkAll c (rs.set r v) := by
  intro r'
  by_cases e : r' = r
  · subst e; rw [RegFile.set_same]; exact hv
  · rw [RegFile.set_other _ _ _ _ e]; exact h r'

/-- A device read is never a walk slot (the walk's pages are RAM). -/
theorem tvAnsDev {c : TCfg} (hr : c.ram) (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n))
    (hd : devAddr pa = true) : tvAns c pa n w := by
  have hlt : pa.toNat < 0x80000000 := by simpa [devAddr, devBound] using hd
  have h2 := (pteAddrRam c.b (vpnIdx c.vpn 2) hr.1).1
  have h1 := (pteAddrRam c.b1 (vpnIdx c.vpn 1) hr.2.1).1
  have h0 := (pteAddrRam c.b0 (vpnIdx c.vpn 0) hr.2.2).1
  intro _
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> (subst e; omega)

/-- A label's bytes in the `tvAnsL` form. -/
theorem tvAnsOfLab {c : TCfg} (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n))
    (tvs : List (Nat × BitVec 8)) (hl : tvs.length = n)
    (hb : ∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j))
    (h : tvAnsL c (paZ pa) (tvs.map Prod.snd)) : tvAns c pa n w :=
  h pa n w rfl (PinFetchVal.tvsView w tvs hl hb)

set_option maxHeartbeats 4000000 in
/-- **One Sail node.** -/
theorem tvNodeStep {c : TCfg} (hr : c.ram) (P : Unit → Prop) (m : SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind)
    (hstep : pnodeStep m rs ib d l m' ors fn' d' oib obar) (hann : ibnAnn m = false)
    (hf : tvB c P m) (hrb : tvRkAll c rs) (hl : labAnsOk c l) :
    tvB c P m' ∧ tvRkAll c (ors.getD rs) := by
  match m, hstep with
  | .pure _, _ => simp [ibnAnn] at hann
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf (rs r) (hrb r), hrb⟩
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf.2 (), tvRkAllSet rs r v hrb hf.1⟩
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · rename_i hd
        obtain ⟨w, -, rfl, rfl, rfl, -, rfl, -⟩ := h
        exact ⟨hf w (tvAnsDev hr _ n w hd), hrb⟩
      · rcases h with ⟨-, w, tvs, hln, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
          ⟨-, ⟨-, w, tvs, hln, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, w, tvs, hln, hb, rfl, rfl, rfl, -, -, rfl, -⟩⟩
        · exact ⟨hf w (tvAnsOfLab _ n w tvs hln hb hl), hrb⟩
        · exact ⟨hf w (tvAnsOfLab _ n w tvs hln hb hl), hrb⟩
        · exact ⟨hf w (tvAnsOfLab _ n w tvs hln hb hl), hrb⟩
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨-, rfl, rfl, rfl, -, rfl, -⟩ := h
          exact ⟨hf _, hrb⟩
        · exact h.elim
      · split at h
        · obtain ⟨-, h⟩ := h
          rcases h with ⟨-, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, ⟨rfl, rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, rfl, -, -, rfl, -⟩⟩
          · exact ⟨hf _, hrb⟩
          · exact ⟨hf _, hrb⟩
          · exact ⟨hf, hrb⟩
        · exact h.elim
    | barrier b =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf (), hrb⟩
    | instrAnnounce n w => simp [ibnAnn] at hann
    | choose s =>
      obtain ⟨ch, rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf ch, hrb⟩
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | branchAnnounce =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | cacheOp =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | tlbi =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | takeException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | returnException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | translationStart =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | translationEnd =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | cycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩
    | message =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact ⟨hf _, hrb⟩

/-- **One hart step**: a node, a parked fence, or a PLIC wire write. -/
theorem tvHwStep {c : TCfg} (hr : c.ram) (P : Unit → Prop) (cpu : CPU) (m : SailM Unit)
    (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind)
    (hstep : pstepHw cpu m rs fn ib d l rds ws false m' ors fn' d' oib obar)
    (hf : tvB c P m) (hrb : tvRkAll c rs) (hl : labAnsOk c l) :
    tvB c P m' ∧ tvRkAll c (ors.getD rs) := by
  rcases hstep with ⟨-, ⟨H, -⟩, -, -, hann⟩ | ⟨pr, pw, sr, sw, rfl, ⟨H, -⟩, -, -, -⟩ | ⟨H, -, -, -⟩
  · exact tvNodeStep hr P m rs ib _ l m' ors fn' _ oib obar H hann.symm hf hrb hl
  · obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := H
    exact ⟨hf, hrb⟩
  · obtain ⟨mm, b, k, -, rfl, rfl, -, -, rfl, -, rfl⟩ := H
    refine ⟨hf, ?_⟩
    unfold pinSet
    split
    · exact tvRkAllSet rs _ _ hrb ⟨trivial, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
    · exact tvRkAllSet rs _ _ hrb ⟨trivial, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩

/-- **(C), THE RUN (header).** -/
theorem tvPhrun {c : TCfg} (hr : c.ram) (P : Unit → Prop) (cpu : CPU) (ls : List Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' → ann = false →
    tvB c P m → tvRkAll c rs → (∀ l ∈ ls, labAnsOk c l) → tvB c P m' ∧ tvRkAll c rs' := by
  intro h
  induction h with
  | nil m rs fn ib d => intro _ hf hrb _; exact ⟨hf, hrb⟩
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    intro hann hf hrb hls
    rw [Bool.or_eq_false_iff] at hann
    obtain ⟨ha1, ha2⟩ := hann
    subst ha1
    obtain ⟨hf1, hrb1⟩ := tvHwStep hr P cpu m rs fn ib d l rds ws m1 ors fn1 d1 oib obar hstep hf hrb
      (hls l List.mem_cons_self)
    exact ih ha2 hf1 hrb1 (fun l' h' => hls l' (List.mem_cons_of_mem _ h'))

end PinFetchPa
end Weak
