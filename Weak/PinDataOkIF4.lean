/-
Weak: **r2 glue (ii) — THE ASSEMBLY: `fetchOkRealized` ⇒ a walk cycle's exception comes after
its announce** (`fetchOkRF` (ii); `PROGRESS-r2glue.md`).  Lean-only.

`fetchOkRealized` is the fetch twin of `dataRealized` for the no-fault half (W11-F's obligation):
at every walk cycle at `pc` (from its boundary's FIRST `LInstr`) there are fetch configurations
`c1` / `c2` (`fCfgOk`: identity `R|X` leaves for `PC` / `PC + 2`, pages in RAM) such that along
every partial run of the cycle every register read is admitted by both `dG`s (`eG`) and every
RAM-read label by both `dAns` (`labAnsOkD`).  The fetch labels' addresses come from (i)
(`fetchOkRFi`), their bytes from `kFetchText`.

`fetchOkRFii` is cycRun's `fetchOkR2` (ii) with `LInstr ∉ ls0` (as `dataOkRF`).  The run lemma
`cyERun` follows the ACTUAL run to its end: either still under `cyDB`, or past an exception's cause
write whose stop post says "announced" — and the announce persists along an in-cycle run
(`irunAnn`).  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkIF3
import Weak.PinDataOkAsm
import Weak.PinFetchPaAsm

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef

namespace PinDataOk
open SailCycleOrderK PinCycRun PinDataflow

/-! ## 1. The announce persists along an in-cycle run -/

set_option maxHeartbeats 4000000 in
theorem ibAnnNode (m : SailM Unit) (rs : RegFile) (ib : Ibch) (dd : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (dd' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (hpure : ∀ x, m ≠ .pure x)
    (hstep : pnodeStep m rs ib dd l m' ors fn' dd' oib obar) (h : ib.ibBits.isSome = true) :
    (oib.getD ib).ibBits.isSome = true := by
  match m, hstep with
  | .pure x, _ => exact absurd rfl (hpure x)
  | .impure (.error _) _, h' => exact h'.elim
  | .impure (.ok o) k, h' =>
    cases o with
    | regRead r =>
      obtain ⟨-, -, -, -, -, rfl, -⟩ := h'
      show (ibRd ib r).ibBits.isSome = true
      rw [ibRdBits]; exact h
    | memRead n va req =>
      simp only [pnodeStep] at h'
      split at h'
      · obtain ⟨w, -, -, -, -, -, rfl, -⟩ := h'; exact h
      · rcases h' with ⟨-, w, tvs, -, -, -, -, -, -, -, rfl, -⟩ |
          ⟨-, ⟨-, w, tvs, -, -, -, -, -, -, -, rfl, -⟩ | ⟨-, w, tvs, -, -, -, -, -, -, -, rfl, -⟩⟩ <;> exact h
    | memWrite n va req =>
      simp only [pnodeStep] at h'
      split at h'
      · split at h'
        · obtain ⟨-, -, -, -, -, rfl, -⟩ := h'; exact h
        · exact h'.elim
      · split at h'
        · obtain ⟨-, h'⟩ := h'
          rcases h' with ⟨-, -, -, -, -, -, rfl, -⟩ |
            ⟨-, ⟨-, -, -, -, -, rfl, -⟩ | ⟨-, -, -, -, -, rfl, -⟩⟩ <;> exact h
        · exact h'.elim
    | instrAnnounce n w =>
      obtain ⟨-, -, -, -, -, rfl, -⟩ := h'
      rfl
    | choose s =>
      obtain ⟨ch, -, -, -, -, -, rfl, -⟩ := h'; exact h
    | readRam => exact h'.elim
    | writeRam => exact h'.elim
    | _ => obtain ⟨-, -, -, -, -, rfl, -⟩ := h'; exact h

theorem ibAnnHart (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (hpure : ∀ x, m ≠ .pure x)
    (hstep : pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar) (h : ib.ibBits.isSome = true) :
    (oib.getD ib).ibBits.isSome = true := by
  rcases hstep with ⟨H, -⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨-, -, -, -, -, rfl, -⟩ := H
      exact h
    | none => exact ibAnnNode m rs ib d.efDev l m' ors fn' d'.efDev oib obar hpure H h
  · obtain ⟨mm, b, k, -, -, -, -, -, rfl, -, -⟩ := H
    exact h

/-- **The announce persists** along an in-cycle run. -/
theorem irunAnn : ∀ (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab), irun ls p d p' d' →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
      p = .PHart cpu m rs fn ib → ib.ibBits.isSome = true → atAnn p' := by
  intro ls p d p' d' h
  induction h with
  | nil p d =>
    intro cpu m rs fn ib hp hb
    exact ⟨cpu, m, rs, fn, ib, hp, hb⟩
  | @more l ls cpu c k rs fn ib d p1 d1 p2 d2 hstep hrest ih =>
    intro cpu' m rs' fn' ib' hp hb
    injection hp with e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    cases p1 with
    | PDisk dp => exact (show False from hstep).elim
    | PHart cpu1 m1 rs1 fn1 ib1 =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := hstep
    exact ih cpu1 m1 _ fn1 _ rfl (ibAnnHart cpu1 _ rs fn ib d l m1 ors fn1 d1 oib obar
      (fun x e => by cases e) hh hb)

/-- An in-cycle run splits at any prefix of its labels. -/
theorem irunSplit : ∀ (xs ys : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab),
    irun (xs ++ ys) p d p' d' → ∃ p'' d'', irun xs p d p'' d'' ∧ irun ys p'' d'' p' d' := by
  intro xs
  induction xs with
  | nil => intro ys p d p' d' h; exact ⟨p, d, .nil _ _, h⟩
  | cons x xs ih =>
    intro ys p d p' d' h
    cases h with
    | more hs hr =>
      obtain ⟨p'', d'', h1, h2⟩ := ih ys _ _ p' d' hr
      exact ⟨p'', d'', .more hs h1, h2⟩

/-! ## 2. The run, to its actual end -/

section run
variable {G : (r : Register) → RegisterType r → Prop} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop}
  {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {P : Unit → CySt → Prop}

/-- **THE RUN, to its end** (header): from a `cyDB` tree whose stop post says "announced", an
in-cycle run ends under `cyDB` at a matched state, or announced. -/
theorem cyERun :
    ∀ (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab), irun ls p d p' d' →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch) (st : CySt), p = .PHart cpu m rs fn ib → cyDB G D A Aa eStopPost P m st →
      cyMatch st rs ib →
      (∀ ls1 l ls2 pm dm, ls = ls1 ++ l :: ls2 → irun ls1 p d pm dm → runPrem G D A Aa st.fe.length pm ls1 l) →
      (∀ pa n w, devAddr pa = true → D pa n w) →
      (∃ (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch) (st1 : CySt),
        p' = .PHart cpu m1 rs1 fn1 ib1 ∧ cyDB G D A Aa eStopPost P m1 st1 ∧ cyMatch st1 rs1 ib1) ∨
      atAnn p' := by
  intro ls p d p' d' h
  induction h with
  | nil p d =>
    intro cpu m rs fn ib st hp hcy hm _ _
    subst hp
    exact Or.inl ⟨m, rs, fn, ib, st, rfl, hcy, hm⟩
  | @more l ls cpu c k rs fn ib d p1 d1 p2 d2 hstep hrest ih =>
    intro cpu' m rs' fn' ib' st hp hcy hm hP hdev
    injection hp with e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    cases p1 with
    | PDisk dp => exact (show False from hstep).elim
    | PHart cpu1 m1 rs1 fn1 ib1 =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := hstep
    have hst : pstepEv (.PHart cpu1 (.impure c k) rs fn ib) d l
        (.PHart cpu1 m1 (ors.getD rs) fn1 (oib.getD ib)) d1 :=
      ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩
    obtain ⟨hG0, hL0, hA0⟩ := hP [] l ls _ d rfl (irun.nil _ _)
    have hA0' : feAdm A Aa st.fe.length l := by simpa [feLabs] using hA0
    rcases cyDHartStep cpu1 _ rs fn ib d l m1 ors fn1 d1 oib obar st hh (fun x e => by cases e) hcy hm hA0'
        (fun r k' e => hG0 cpu1 r k' rs fn ib (by rw [e])) hL0 hdev with
      ⟨r, v, k', hk, -, -, hT⟩ | ⟨st', hcy', hm', hlen⟩
    · right
      have hb : ib.ibBits.isSome = true := by rw [← hm.2.2.2.2.2]; exact hT
      exact irunAnn _ _ _ _ _ (.more hst hrest) cpu1 _ rs fn ib rfl hb
    · exact ih cpu1 m1 (ors.getD rs) fn1 (oib.getD ib) st' rfl hcy' hm'
          (fun ls1 l' ls2 pm dm e hir1 => by
            obtain ⟨g1, g2, g3⟩ := hP (l :: ls1) l' ls2 pm dm (by rw [e]; rfl) (irun.more hst hir1)
            refine ⟨g1, g2, ?_⟩
            rw [hlen, Nat.add_assoc, ← List.length_append]
            have e2 : feLabs [l] ++ feLabs ls1 = feLabs (l :: ls1) := by
              simp only [feLabs, List.filter_cons, List.filter_nil]
              split <;> rfl
            rw [e2]; exact g3) hdev

end run

/-! ## 3. The interface and the assembly -/

/-- **THE FETCH'S NO-FAULT HALF, REALIZED (INTERFACE, header; W11-F's obligation).** -/
def fetchOkRealized (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 →
    ∃ c1 c2 : DCfg, fCfgOk pc c1 c2 ∧
      ∀ (ls1 : List Wlabel) (pm : Pexv6) (dm : Efab), cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
        atRegRead pm (eG c1 c2) ∧ ∀ l ∈ ls1, labAnsOkD c1 l ∧ labAnsOkD c2 l

/-- **`fetchOkR2` (ii), restated** (header). -/
def fetchOkRFii (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
    atCause false pm → atAnn pm

theorem labDOfAnsOkD2 (c1 c2 : DCfg) (l : Wlabel) (h1 : labAnsOkD c1 l) (h2 : labAnsOkD c2 l) :
    labD (eD c1 c2) l := by
  cases l <;> first
    | exact fun pa n w ha hb => ⟨h1 pa n w ha hb, h2 pa n w ha hb⟩
    | trivial

set_option maxHeartbeats 4000000 in
/-- **`fetchOkRF` (ii) FROM THE INTERFACE** (header). -/
theorem fetchOkRFiiOf (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (htext : textLo ≤ pc ∧ pc + 3 < textHi) (hev : pc % 2 = 0) (a : instruction)
    (hdec : PinWalkTab.decS pc = some a) (hfetch1 : fetchCyR1 pc) (hexec : execCyAt pc)
    (hnw : dfNwRole (krole pc)) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfi : PinFetchPa.fetchOkRFi p0 d0 em pc) (hreal : fetchOkRealized p0 d0 em pc) :
    fetchOkRFii p0 d0 em pc := by
  intro pfx ls0 q d1 ls1 pm dm hni hcs hcin hir hac
  obtain ⟨c1, c2, hc, hruns⟩ := hreal pfx ls0 q d1 hni hcs
  have hcs0 := hcs
  obtain ⟨p, d, hbd, hrun0, -⟩ := hcs
  obtain ⟨-, -, cpu0, rs, fn, ib, rfl, hkinv⟩ := hbd
  rcases pureSplit _ _ _ _ _ hrun0 cpu0 rs fn ib rfl hkinv.2.2 with hni' |
    ⟨ls0', ls1', rs'', tick', d1'', hls, -, -, hr0, hr1, hag, hrb'⟩
  · exact absurd (List.mem_append_right _ List.mem_cons_self) hni'
  obtain ⟨hs1, hs2⟩ := splitLast LInstr ls0 ls0' ls1' hni hls
  subst ls0'
  subst ls1'
  obtain ⟨hq, hd1⟩ := pevrunNil hr1
  subst d1''
  subst hq
  have hkinv' : kInv pc rs'' := PinCycRun.kInvAgree pc rs rs'' hag hrb' hkinv
  let st0 : CySt := ⟨rs'', [], false, ⟨OpRoles.ORnone, [], 0, true⟩⟩
  have hcy0 := cyESailOf pc htext hev a hdec hfetch1 hexec hnw c1 c2 hc tick' st0 ⟨hkinv', rfl, rfl, rfl⟩
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
      runPrem (eG c1 c2) (eD c1 c2) kA (kAa pc) st0.fe.length pmm ls1a l := by
    intro ls1a l ls2 pmm dmm e hira
    refine ⟨(hruns ls1a pmm dmm (cycInPrefix em pfx ls0 ls1 ls1a ls2 l ⟨rest, hes, hpre⟩ e) hira).1,
      labDOfAnsOkD2 c1 c2 l (hlabs l (by rw [e]; simp)).1 (hlabs l (by rw [e]; simp)).2, ?_⟩
    intro a' tvs hl'
    subst hl'
    refine ⟨?_, PinCycRun.kAOfText em hft hfeN a' tvs (hsub _ (by rw [e]; simp))⟩
    show a' = pc + 2 * ((0 + (feLabs ls1a).length : Nat) : Int)
    rw [Nat.zero_add]
    have hir' : irun ((ls1a ++ [LIFetch a' tvs]) ++ ls2) (.PHart cpu0 (riscvStep tick') rs'' none ibNone) d1 pm dm := by
      rw [List.append_assoc]; simpa [e] using hir
    obtain ⟨p'', d'', hpre1, -⟩ := irunSplit _ _ _ _ _ _ hir'
    exact hfi pfx ls0 _ d1 ls1a p'' d'' a' tvs hni hcs0
      ⟨rest, hes, List.IsPrefix.trans ⟨ls2, by rw [e]; simp⟩ hpre⟩ hpre1
  rcases cyERun ls1 _ d1 pm dm hir cpu0 (riscvStep tick') rs'' none ibNone st0 rfl hcy0 hm0 hP
      (fun pa n w hd => ⟨dAnsDev c1 hc.1 pa n w hd, dAnsDev c2 hc.2.2.2.1 pa n w hd⟩) with
    ⟨m1, rs1, fn1, ib1, st1, rfl, hcyc, hm1⟩ | hann
  · obtain ⟨cpuX, r, v, k, rsX, fnX, ibX, hpm, hsr, hcb⟩ := hac
    injection hpm with e1 e2 e3 e4 e5
    subst e2 e4 e5
    have h2 : st1.an = true := hcyc.1 hsr hcb
    exact ⟨cpu0, _, rs1, fn1, ib1, rfl, by rw [← hm1.2.2.2.2.2]; exact h2⟩
  · exact hann

/-- **r2 feeds the cycle walk**: the two restated halves ARE cycRun's `fetchOkRF`
(`PinCycRunAsm.lean`), the form `cycWalk` consumes. -/
theorem fetchOkRFOfParts (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (hi : PinFetchPa.fetchOkRFi p0 d0 em pc) (hii : fetchOkRFii p0 d0 em pc) :
    PinCycRun.fetchOkRF p0 d0 em pc :=
  ⟨hi, hii⟩

end PinDataOk
end Weak
