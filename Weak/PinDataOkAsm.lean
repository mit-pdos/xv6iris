/-
Weak: **`dataOkR` (4e) — THE ASSEMBLY: `dataRealized` ⇒ the walk loads/stores take no synchronous
exception** (`PROGRESS-dataOk.md`).  Lean-only.

`dataOkRFOf`: at a walk load/store pc, from the interface `dataRealized` (and the cycle's facts
w1's `cycRunOfHartConf*` already takes: the decoded instruction, `fetchCyR1`, `execCyAt`, the role's
`dfNwRole`, `kFetchText`, the admin fetch items, `fetchOkR2`), along every partial run of a walk
cycle that starts at the walk boundary's FIRST `LInstr` no exception's cause write is reached
(`dataOkRF`).  The proof: the cycle's register file is the boundary's off the wires (`pureSplit`),
so the filtered cycle `cyDSailOf` holds at its start; its run soundness `cyDRun` with the
interface's per-read / per-label premises gives a matched `cyDB` state at every reached exception
cause write, whose stop post says "not yet announced" — against `fetchOkR2` (ii) ("an exception's
cause write comes after the announce").

**Deviation (spec, FAITHFUL for the use):** `dataOkRF` (now defined in `PinCycRunAsm.lean`, next to
`dataOkR`, so that `cycWalk` consumes it; r2 is taken in its restated form `fetchOkRF`) is cycRun's
`dataOkR` with the premise
`LInstr ∉ ls0` (the boundary labels before the cycle's `LInstr` contain no other `LInstr`).
`dataOkR` as stated also quantifies over `cycStart`s whose `ls0` runs WHOLE further cycles (the run
then starts a cycle at a later pc, about which the walk pc's access says nothing); its only use,
`PinCycRun.cycWalk` (`PinCycRunAsm.lean:668`), builds `ls0` by `pureSplit` at the FIRST `LInstr`,
which is `LInstr`-free.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkSail

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef

namespace PinDataOk
open SailCycleOrderK PinCycRun PinDataflow

/-- The last element splits uniquely off a list it does not occur in. -/
theorem splitLast {α : Type} (x : α) : ∀ (a b c : List α), x ∉ a → a ++ [x] = b ++ x :: c → b = a ∧ c = [] := by
  intro a
  induction a with
  | nil =>
    intro b c _ h
    cases b with
    | nil => simp only [List.nil_append, List.cons.injEq] at h; exact ⟨rfl, h.2.symm⟩
    | cons y b' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.2.symm (by simp)
  | cons y a ih =>
    intro b c hx h
    cases b with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hx
    | cons z b' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨e1, e2⟩ := ih b' c (fun hm => hx (List.mem_cons_of_mem _ hm)) h2
      exact ⟨by rw [e1], e2⟩

theorem pevrunNil {p : Pexv6} {d : Efab} {p' : Pexv6} {d' : Efab} (h : pevrun [] p d p' d') :
    p' = p ∧ d' = d := by
  cases h; exact ⟨rfl, rfl⟩

/-- A device read is never a walk slot (the walk's pages are RAM). -/
theorem dAnsDev (c : DCfg) (hr : c.ram) (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n))
    (hd : devAddr pa = true) : dAns c pa n w := by
  have hlt : pa.toNat < 0x80000000 := by simpa [devAddr, devBound] using hd
  have h2 := (slotRam c.b (vpnIdx c.vpn 2) hr.1).1
  have h1 := (slotRam c.b1 (vpnIdx c.vpn 1) hr.2.1).1
  have h0 := (slotRam c.b0 (vpnIdx c.vpn 0) hr.2.2.1).1
  intro _
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> (subst e; omega)

/-- A prefix of the cycle's labels is in the cycle. -/
theorem cycInOfPrefix (em : Hemission) (pfx : List Eitem) (ls0 ls1 ls1a : List Wlabel)
    (h : cycIn em pfx ls0 ls1) (hp : ls1a <+: ls1) : cycIn em pfx ls0 ls1a := by
  obtain ⟨rest, hes, hq⟩ := h
  refine ⟨rest, hes, List.IsPrefix.trans ?_ hq⟩
  obtain ⟨t, rfl⟩ := hp
  exact ⟨t, by simp⟩

theorem cycInPrefix (em : Hemission) (pfx : List Eitem) (ls0 ls1 ls1a ls2 : List Wlabel) (l : Wlabel)
    (h : cycIn em pfx ls0 ls1) (e : ls1 = ls1a ++ l :: ls2) : cycIn em pfx ls0 ls1a := by
  obtain ⟨rest, hes, hp⟩ := h
  refine ⟨rest, hes, List.IsPrefix.trans ?_ hp⟩
  rw [e]
  exact ⟨l :: ls2, by simp⟩

set_option maxHeartbeats 4000000 in
/-- **(4) `dataOkRF` FROM THE INTERFACE** (header). -/
theorem dataOkRFOf (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction) (hdec : PinWalkTab.decS pc = some a)
    (hfetch1 : fetchCyR1 pc) (hexec : execCyAt pc) (hnw : dfNwRole (krole pc)) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfetch : fetchOkRF p0 d0 em pc) (hreal : dataRealized p0 d0 em pc) : dataOkRF p0 d0 em pc := by
  intro hmem pfx ls0 q d1 ls1 pm dm hni hcs hcin hir hac
  obtain ⟨c, hr, hacc, hruns⟩ := hreal hmem pfx ls0 q d1 hcs
  have hcs0 := hcs
  obtain ⟨p, d, hbd, hrun0, cpu, tick, rs', rfl⟩ := hcs
  obtain ⟨-, -, cpu0, rs, fn, ib, rfl, hkinv⟩ := hbd
  rcases pureSplit _ _ _ _ _ hrun0 cpu0 rs fn ib rfl hkinv.2.2 with hni' |
    ⟨ls0', ls1', rs'', tick', d1'', hls, -, -, hr0, hr1, hag, hrb'⟩
  · exact hni' (List.mem_append_right _ List.mem_cons_self)
  obtain ⟨hs1, hs2⟩ := splitLast LInstr ls0 ls0' ls1' hni hls
  subst ls0'
  subst ls1'
  obtain ⟨hq, hd1⟩ := pevrunNil hr1
  subst d1''
  rw [hq] at hir hcs0 hruns
  clear hq
  have hkinv' : kInv pc rs'' := PinCycRun.kInvAgree pc rs rs'' hag hrb' hkinv
  let st0 : CySt := ⟨rs'', [], false, ⟨OpRoles.ORnone, [], 0, true⟩⟩
  have hcy0 := cyDSailOf pc htext a hdec hfetch1 hexec hnw c hr hacc tick' st0 ⟨hkinv', rfl, rfl, rfl⟩
  have hm0 : cyMatch st0 rs'' ibNone := ⟨fun _ _ => rfl, hrb', hrb', rfl, rfl, rfl⟩
  have hlabs := (hruns ls1 pm dm hcin hir).2
  obtain ⟨rest, hes, hpre⟩ := hcin
  have hsub : ∀ l', l' ∈ ls1 → l' ∈ em.emItems.map Prod.fst := by
    intro l' hl'
    obtain ⟨t, ht⟩ := hpre
    rw [hes, List.map_append]
    refine List.mem_append_right _ ?_
    rw [← ht]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ hl'))
  have hP : ∀ ls1a l ls2 pmm dmm, ls1 = ls1a ++ l :: ls2 →
      irun ls1a (.PHart cpu0 (riscvStep tick') rs'' none ibNone) d1 pmm dmm →
      runPrem (dG c) (dAns c) kA (kAa pc) st0.fe.length pmm ls1a l := by
    intro ls1a l ls2 pmm dmm e hira
    refine ⟨(hruns ls1a pmm dmm (cycInPrefix em pfx ls0 ls1 ls1a ls2 l ⟨rest, hes, hpre⟩ e) hira).1,
      labDOfAnsOk c l (hlabs l (by rw [e]; simp)), ?_⟩
    intro a' tvs hl'
    subst hl'
    refine ⟨?_, PinCycRun.kAOfText em hft hfeN a' tvs (hsub _ (by rw [e]; simp))⟩
    show a' = pc + 2 * ((0 + (feLabs ls1a).length : Nat) : Int)
    rw [Nat.zero_add]
    have hir' : irun ((ls1a ++ [LIFetch a' tvs]) ++ ls2)
        (.PHart cpu0 (riscvStep tick') rs'' none ibNone) d1 pm dm := by
      rw [e] at hir; simpa using hir
    obtain ⟨pm', dm', hira'⟩ := PinCycRun.irunPrefix _ ls2 _ _ _ _ hir'
    exact hfetch.1 pfx ls0 _ d1 ls1a pm' dm' a' tvs hni hcs0
      ⟨rest, hes, List.IsPrefix.trans ⟨ls2, by rw [e]; simp⟩ hpre⟩ hira'
  rcases cyDRun ls1 _ d1 pm dm hir cpu0 (riscvStep tick') rs'' none ibNone st0 rfl hcy0 hm0 hP (dAnsDev c hr) with
    ⟨la, lb, m1, rs1, fn1, ib1, dd, st1, hl, hira, ⟨r, v, k, rfl, hsr, hcb, hT⟩, hm1⟩ |
    ⟨m1, rs1, fn1, ib1, st1, rfl, hc, hm1⟩
  · have hac1 : atCause false (.PHart cpu0 (.impure (.ok (.regWrite r v)) k) rs1 fn1 ib1) :=
      ⟨cpu0, r, v, k, rs1, fn1, ib1, rfl, hsr, hcb⟩
    obtain ⟨_, _, _, _, _, e, hib⟩ := hfetch.2 pfx ls0 _ d1 la _ dd hni hcs0
      (cycInOfPrefix em pfx ls0 ls1 la ⟨rest, hes, hpre⟩ ⟨lb, hl.symm⟩) hira hac1
    cases e
    have h1 : st1.an = true := by rw [hm1.2.2.2.2.2]; exact hib
    have h2 : st1.an = false := hT
    rw [h1] at h2; cases h2
  · obtain ⟨_, _, _, _, _, e, hib⟩ := hfetch.2 pfx ls0 _ d1 ls1 _ dm hni hcs0 ⟨rest, hes, hpre⟩ hir hac
    cases e
    obtain ⟨cpuX, r, v, k, rsX, fnX, ibX, hpm, hsr, hcb⟩ := hac
    injection hpm with e1 e2 e3 e4 e5
    subst e2
    have h1 : st1.an = true := by rw [hm1.2.2.2.2.2]; exact hib
    have h2 : st1.an = false := hc.1 hsr hcb
    rw [h1] at h2; cases h2

end PinDataOk
end Weak
