/-
Weak: **the S-mode racy WP rule of a fetch-walking step** (walk-bridge §8, 6b: the WP layer above
`Weak/WkStepPeel.lean`).

Rocq: `iris/WkWalkRule.v` @ xxvzwolszwmp (461 lines; one Lean file).

The Rocq header, in substance.  `WkStepPeel` delivers, in pure form, the three halves of a whole
instruction step whose FETCH walks the page table and whose EXECUTE phase is window-free: the PEEL
(`wstepPeelFetchwalk`), the step-level FAMILY at the stale mirror (`wstepFamilyFetchwalk`) and the
Q-half (`wexecOutcomeOfPeel`).  This file lifts that triple to ONE weakest-precondition step rule,
`wpWwalkStep`, in the shape of `WeakRacy.wpWracyLoad` (same `wpWrunStep` plumbing, same
σ-callback, same ▷-continuation discipline), with the walk's structural deltas: the certificate is
at `wDAny` / `W := True` (a walking step WRITES the A/D bits back, so the peel cannot be taken at
the racy rules' write-refusing instance); the continuation is handed an `execStale` equation at
ONE admissible leaf word plus the §10 preservation conjuncts (`wlogWf`, `latestTs` unmoved off the
trace's writes, and the LOG-IDENTITY equation `σ'.wmLog = σ.wmLog ++ wtraceMsgs …`), not a
patched-`exec` one.  §4 computes the projection on the walk's six trace shapes: `[]` on the four
read-only ones and the single `WCexcl` message on the two write-back ones, which is the tail
`WeakKptStale.wtlbResPtTranslateAddrStaleAt`'s appended-log arm hands out.

THE φ-UPGRADE OBLIGATION HERE IS THE CLEAN-WINDOW ARM, NOT `syncWin` (recorded decision, Rocq
header): a translation is not a racy-window consumer; the PTE bytes are clean fragments, and the
witness is the absorption theorem's own `nvFree` export for the eight PTE bytes of `la`.  So this
rule has NO `syncWin` premise; a caller owes, at the resource level, the clean/published state of
the eight PTE bytes (the fact `wtlbResPtTranslateAddrStaleAt` exports), not a sync token.  Wiring
that into φ's preservation is the φ-mechanization's item (WeakGhost), not this file's.

No graph-tier fact is used: the file lives at `wrun` / `wexec` / `execStale`.

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WkStepPeel.lean` deviation 1 (`σ.wmRegs r`, `wflatSt`, `wflatMem`,
   `pa + BitVec.ofNat 64 j`, `nthByte`, `(bmRead m a n).isSome = true` for `is_Some (read_bytes …)`,
   `region.attributes`, `.HART_ACTIVE ()`, `WExpr.loop gen cpu` / `wwpTriv ⊤` for `WWP Loop`, the
   generation as an explicit `gen` with `gen = 0` as WeakRacy); `AkInfo false true false` is the
   literal `⟨false, true, false⟩` (= `wakExcl`), as WeakKptStale states its shapes.  Statement-level
   `let vpn`/`let la` kept.
2. The certificate's text-pin hypothesis on the PC window is `pinnedRead ∧ fetchPinned`, exactly
   as Lean `WeakRacy.wracyCert` / `wpWracyLoad` (cross-file fact "text pin `pinnedRead ∧
   fetchPinned`"); `wpWwalkStep`'s σ-callback returns the same conjunction.
3. O2 (WkStepPeel deviation 5): the `wwalkSite` "text bytes pinned" conjunct is the FETCH pin
   `fetchPinned σ (WeakInterp.accAddr pa j)` (Rocq `pinned_read`), which is what
   `wstepPeelFetchwalk` demands.
4. Rocq's `(N.of_nat j < 4)%N` byte premise is `j < 4`.
5. Rocq §5's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `wwalk_cert` `wwalkCert`, `wp_wwalk_step` `wpWwalkStep`, `wwalk_site`
`wwalkSite`, `wp_wwalk_step_cert_of_peel` `wpWwalkStepCertOfPeel`, `wwalk_site_adm_filter`
`wwalkSiteAdmFilter`, `wtrace_msgs_walk_ro` `wtraceMsgsWalkRo`, `wm_log_of_msgs_nil`
`wmLogOfMsgsNil`, `wtrace_msgs_walk_wb` `wtraceMsgsWalkWb`, `wm_log_of_walk_wb` `wmLogOfWalkWb`
(none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing.  9 Rocq declarations (`Definition`/`Lemma`): 9 Lean declarations.

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 1–4.
-/
import Weak.WkStepPeel

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE CERTIFICATE -/

/-- Rocq `wwalk_cert`: `wracyCert` with (a) the peel at the walk's leaf window `(la, 8)`,
`wakPlain`, `wDAny` / `True`; (b) the step-level family at the stale mirror, exactly as
`wexecOutcomeOfPeel` consumes it; (c) the Q-half. -/
def wwalkCert (cid : Nat) (pc : BitVec 64) (la : PAddr) (Φ : (Nat → BitVec 8) → Prop)
    (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) : Prop :=
  ∀ (σ : Wmstate) (tick : Bool),
    σ.wmRegs .PC = pc →
    accWf pc 4 →
    (∀ j : Nat, j < 4 →
      pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)) →
    P σ →
    -- (a) the peel of the whole step, at the leaf window
    wstepOkRacy (some cid) la 8 wakPlain Φ wDAny True true (riscvStep tick) σ ∧
    -- (b) the step-level family at the stale mirror
    ((∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
        ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
          execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
          traceStale wakPlain la 8 es) ∨
      (∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
        ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
          execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
          traceOffWin la 8 es)) ∧
    -- (c) the Q-half
    (∀ χ σ' χ', wexec (some cid) (riscvStep tick) χ σ = some ((), σ', χ') → Q σ σ')

/-! ## 2. THE RULE -/

section rule
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wp_wwalk_step`: THE S-MODE RACY STEP RULE.  `wpWracyLoad` with the window fixed to the
walk's leaf slot `(la, 8)` at `wakPlain`, NO `syncWin` premise (see the header), and an
`execStale` equation plus the §10 preservation conjuncts in the continuation. -/
theorem wpWwalkStep (gen : Nat) (cpu : CPU) (pc : BitVec 64) (la : PAddr)
    (Φ : (Nat → BitVec 8) → Prop) (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) :
    gen = 0 → accWf pc 4 → accWf la 8 → wwalkCert cpu.val pc la Φ P Q →
    (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜P σ⌝ ∗
      ⌜wadmFilter σ wakPlain la 8 Φ⌝ ∗
      ⌜(bmRead (wflatMem σ.wmImg σ.wmLog) la 8).isSome = true⌝ ∗
      (∃ t0 : ExecSt, ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝) ∗
      ▷ (∀ (tick : Bool) (σ' : Wmstate) (u : BitVec (8 * 8)) (es : List Weff),
          ⌜wadm σ wakPlain la 8 u⌝ -∗
          ⌜Φ (fun j : Nat => nthByte u j)⌝ -∗
          ⌜execStale la 8 u (riscvStep tick) (wflatSt σ) = some ((), wflatSt σ', es)⌝ -∗
          ⌜∀ a : PAddr,
            wtraceWonly (fun (pa : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
            latestTs σ'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)⌝ -∗
          ⌜σ'.wmLog = σ.wmLog ++ wtraceMsgs (some cpu.val) σ.wmWs.wRelp es⌝ -∗
          ⌜wstepPostRacy σ σ'⌝ -∗
          ⌜Q σ σ'⌝ ={∅,⊤}=∗
            wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacc hcert
  iintro H
  iapply wpWrunStep gen cpu hgen
  iintro %σ Hσ
  icases wmstateInterpFacts cpu σ $$ Hσ with ⟨%hfacts, Hσ⟩
  obtain ⟨hbnd, hwf⟩ := hfacts
  imod H $$ %σ Hσ with ⟨%hpc, %htext, %hP, %hΦ, %hrd, ⟨%t0, %hex0⟩, Hk⟩
  have hc := fun tick => hcert σ tick hpc haccpc htext hP
  imodintro
  isplitr
  · ipureintro
    obtain ⟨χ, σ0, χ', hw, _⟩ := wexecOfExecRacy (some cpu.val) la 8 wakPlain Φ wDAny True
      (riscvStep false) hacc true σ (hc false).1 hwf (fun _ => hΦ) () t0 hex0
    exact ⟨χ, σ0, χ', hw⟩
  inext
  iintro %tick %σ' %hrun
  obtain ⟨χ, χ', hwex⟩ := wrunWexecRacy (some cpu.val) la 8 wakPlain Φ wDAny True
    (riscvStep tick) true σ (hc tick).1 (fun _ => hΦ) () σ' hrun
  obtain ⟨u, es, hadm, hΦu, hex, hwf', hlat, hlog⟩ := wexecOutcomeOfPeel (some cpu.val) σ la Φ tick
    hacc hwf hrd (hc tick).1 hΦ (hc tick).2.1 χ () σ' χ' hwex
  have hpost : wstepPostRacy σ σ' :=
    ⟨wrunImg _ _ _ _ _ hrun, wrunLogApp _ _ _ _ _ hrun, wrunWsLe _ _ _ _ _ hrun, hwf',
      wrunWsBounded _ _ _ _ _ hrun hbnd⟩
  iapply Hk $$ %tick %σ' %u %es
  · ipureintro; exact hadm
  · ipureintro; exact hΦu
  · ipureintro; exact hex
  · ipureintro; exact hlat
  · ipureintro; exact hlog
  · ipureintro; exact hpost
  · ipureintro; exact (hc tick).2.2 χ σ' χ' hwex

end rule

/-! ## 3. THE CERTIFICATE IS INHABITED BY THE LANDED LAYER -/

/-- Rocq `wwalk_site`: the σ-dependent premise bundle of `WkStepPeel` §§4–5 (the PC lookup
comes from the certificate's hypothesis). -/
def wwalkSite (tid : Option Nat) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (region : PMA_Region) (w : BitVec 32) (σ : Wmstate) (tick : Bool) : Prop :=
  let vpn := WeakKpt.svpnOf va
  let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
  -- the step's own register gates
  σ.wmRegs .cur_privilege = .Supervisor ∧
  σ.wmRegs .hart_state = .HART_ACTIVE () ∧
  (∀ bmi : Bool, execEff (dispatchInterrupt .Supervisor) (wflatSt (wmi σ bmi)) =
    some (none, wflatSt (wmi σ bmi), [])) ∧
  -- the walk exports and the fetch's gates, at the post-write states
  (∀ bmi : Bool, wfetchReady tid (wmi σ bmi) root va pa p2 p1 w0 lw region) ∧
  -- the text window
  is_aligned_vaddr (.Virtaddr va) 4 = true ∧
  isRVC (Sail.BitVec.extractLsb w 15 0) = false ∧
  raccDisj la 8 pa 4 ∧
  accWf pa 4 ∧
  (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) ∧
  (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) ∧
  (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) ∧
  is_aligned_paddr (.Physaddr pa) 4 = true ∧
  (override_PMA region.attributes .PBMT_PMA).executable = true ∧
  devAddr pa = false ∧
  -- the tails, on both sides of the bridge
  (∀ bmi : Bool, wexecTail tid (wmi σ bmi)) ∧
  (∀ bmi : Bool, wstepPostTail tid (wmi σ bmi)) ∧
  wstepTickTail tid σ tick ∧
  wstepFamilyReady tid σ la va pa w0 lw w tick

/-- Rocq `wp_wwalk_step_cert_of_peel`: THE INHABITATION. -/
theorem wpWwalkStepCertOfPeel (cid : Nat) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (region : PMA_Region) (w : BitVec 32) (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    (∀ (σ : Wmstate) (tick : Bool), P σ → wwalkSite (some cid) root va pa p2 p1 w0 lw region w σ tick) →
    (∀ (σ : Wmstate) (tick : Bool) (χ : List (List Nat)) (σ' : Wmstate) (χ' : List (List Nat)),
      P σ → wexec (some cid) (riscvStep tick) χ σ = some ((), σ', χ') → Q σ σ') →
    wwalkCert cid va la (wwalkFilter w0 lw) P Q := by
  intro vpn la hsite hQ σ tick hpc _haccpc _hpinpc hP
  obtain ⟨hpriv, hhart, hdisp, hready, hal, hnotRVC, hdisj, haccp, hW0, hpin, hbytes, halign, hexecp,
    hdev, hexec, hpost, htick, hfam⟩ := hsite σ tick hP
  refine ⟨?_, ?_, ?_⟩
  · exact (wstepPeelFetchwalk (some cid) σ root va pa p2 p1 w0 lw region w tick hpriv hhart hpc hdisp
      hready hal hdisj haccp hW0 hpin hbytes halign hexecp hdev hexec hpost htick).1
  · exact wstepFamilyFetchwalk (some cid) σ root va pa p2 p1 w0 lw w tick hpriv hhart hpc hdisp
      (fun bmi => (hready bmi).1) hal hnotRVC haccp hdisj hfam
  · intro χ σ' χ' hwex
    exact hQ σ tick χ σ' χ' hP hwex

/-- Rocq `wwalk_site_adm_filter`: the `wadmFilter` half of the σ-callback comes from the same
bundle (`wstepPeelFetchwalk`'s second conjunct). -/
theorem wwalkSiteAdmFilter (cid : Nat) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (region : PMA_Region) (w : BitVec 32) (σ : Wmstate) (tick : Bool) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    σ.wmRegs .PC = va →
    wwalkSite (some cid) root va pa p2 p1 w0 lw region w σ tick →
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hpc hsite
  obtain ⟨hpriv, hhart, hdisp, hready, hal, _hnotRVC, hdisj, haccp, hW0, hpin, hbytes, halign, hexecp,
    hdev, hexec, hpost, htick, _hfam⟩ := hsite
  exact (wstepPeelFetchwalk (some cid) σ root va pa p2 p1 w0 lw region w tick hpriv hhart hpc hdisp
    hready hal hdisj haccp hW0 hpin hbytes halign hexecp hdev hexec hpost htick).2

/-! ## 4. THE LOG-IDENTITY CONJUNCT, ON THE WALK'S SIX TRACE SHAPES

The walk's write-back event is `.WEwrite ⟨false, true, false⟩ la 8 lw'` (`akLatest = true`), and
`wmClassRp` sends every `akLatest` write to `WCexcl` regardless of the pending-release flag
(`wmClassRpLatest`), so the projection names `wwriteMsg tid .WCexcl la 8 lw'` -- exactly what
`wtlbResPtTranslateAddrStaleAt`'s appended-log arm carries. -/

/-- Rocq `wtrace_msgs_walk_ro`: (a) the four read-only shapes append nothing. -/
theorem wtraceMsgsWalkRo (tid : Option Nat) (rp : Bool) (a2 a1 la : PAddr) (es : List Weff) :
    (es = [] ∨
     es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8] ∨
     es = [.WEread ⟨false, true, false⟩ la 8] ∨
     es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
           .WEread ⟨false, true, false⟩ la 8]) →
    wtraceMsgs tid rp es = [] := by
  intro h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Rocq `wm_log_of_msgs_nil`: the successor's log IS the pre-log. -/
theorem wmLogOfMsgsNil (tid : Option Nat) (rp : Bool) (σ σ' : Wmstate) (es : List Weff) :
    wtraceMsgs tid rp es = [] →
    σ'.wmLog = σ.wmLog ++ wtraceMsgs tid rp es →
    σ'.wmLog = σ.wmLog := by
  intro hnil h
  rw [h, hnil, List.append_nil]

/-- Rocq `wtrace_msgs_walk_wb`: (b) the two write-back shapes append exactly the `WCexcl`
message. -/
theorem wtraceMsgsWalkWb (tid : Option Nat) (rp : Bool) (a2 a1 la : PAddr) (lw' : BitVec 64)
    (wtr : Bool) (es : List Weff) :
    es = (if wtr then
            [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
             .WEread ⟨false, true, false⟩ la 8, .WEwrite ⟨false, true, false⟩ la 8 lw']
          else
            [.WEread ⟨false, true, false⟩ la 8, .WEwrite ⟨false, true, false⟩ la 8 lw']) →
    wtraceMsgs tid rp es = [wwriteMsg tid .WCexcl la 8 lw'] := by
  intro h
  subst h
  cases wtr <;> rfl

/-- Rocq `wm_log_of_walk_wb`: the successor's log is the pre-log plus that message. -/
theorem wmLogOfWalkWb (tid : Option Nat) (rp : Bool) (a2 a1 la : PAddr) (lw' : BitVec 64)
    (wtr : Bool) (σ σ' : Wmstate) (es : List Weff) :
    es = (if wtr then
            [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
             .WEread ⟨false, true, false⟩ la 8, .WEwrite ⟨false, true, false⟩ la 8 lw']
          else
            [.WEread ⟨false, true, false⟩ la 8, .WEwrite ⟨false, true, false⟩ la 8 lw']) →
    σ'.wmLog = σ.wmLog ++ wtraceMsgs tid rp es →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid .WCexcl la 8 lw'] := by
  intro hes h
  rw [h, wtraceMsgsWalkWb tid rp a2 a1 la lw' wtr es hes]

end Weak
