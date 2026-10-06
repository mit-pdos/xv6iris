/-
Weak: **the volatile registers** (M4-1, first slice, stage (ii)): the wire invariant, the PLIC
thread's whole WP, a hart's read of a register it does not own, and the BRANCHING certificate
`ewrun` with the funnel `ewpInstr` that keeps `sig_seip`/`sig_meip` OUT of the owned footprint.

Rocq: `iris/WeakEvWire.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE PROBLEM.  The PLIC writes `sig_seip` (and `sig_meip`) of ANY hart at ANY time, mid-instruction
included, and EVERY instruction READS both (`getPendingSet` → `read_mip`), before the
`mstatus.MIE` test.  So a certificate stated at one fixed register file cannot describe the run,
and the funnel's frame cannot contain the two cells.

* §1 `WeakEvWire.wireInv` — one invariant owning `regPointsTo c r (own 1) v` for every hart `c`
  and every `r ∈ wireregs = [sig_seip, sig_meip]`, its boot allocation `wireInvAlloc` (in the
  shape the adequacy package hands out register points-tos) and the one-cell accessor.
* §2 `ewpPlicStep` / `ewpPlic` — the PLIC thread's one-step rule and its WHOLE WP, by Löb.
* §3 `ewpEvRegReadFree` / `ewpEvRegReadInv` — a hart's `regRead` of a register it does NOT own,
  without and with an invariant.
* §4 `ewrun` — the BRANCHING certificate — with `erunEwrun` (every wire-free `erun` mirror is
  one), the walk `ewpEwrunNil`, the one-fetch rule `ewpEwrunFetch`, and `ewpInstr`:
  `WeakEvFunnel`'s funnel with the wires out of the frame.

FINDING 1 (Rocq): THE WIRE READ IS FREE — a `regRead` of an unowned register needs no resource
(`ewpEvRegReadFree`): the certificate covers every value.  `wireInv` is needed by the PLIC thread
(it writes the cells) and by clients that RELATE the value to the PLIC state (MIE-on code);
`ewpEvRegReadInv` is that rule over an arbitrary payload `P`.
FINDING 2 (Rocq): THE CERTIFICATE MUST BRANCH AT THE NODE (`ewrunWire`), not up front: the two
cells are read at different times and the PLIC may write in between.
STAGE (ii) needed (a) the relational certificate, (b) a Löb-closed PLIC WP, (c) the disjointness
side condition (the hart owns nothing at a wire), which keeps the frame through `setReg` at a
wire node (`eregFrSetNe`).

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below), as `WeakEvFunnel` deviation 1: `gset register` ↦
   `List Register`, `M unit` ↦ `SailM Unit`, `mstate` ↦ `ExecSt`, `set_reg` ↦ `ExecSt.setReg`,
   `register_lookup r rs` ↦ `rs r`, `read_bytes` ↦ `bmRead`, `reg_pointsto_at` ↦ `regPointsTo`,
   `[∗ set] c ∈ fin_to_set CPU` ↦ `[∗list] c ∈ cpus`, `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`,
   `EWP e @ ⊤` ↦ `ewpTriv ⊤ e`, `Ret y` ↦ `FreeM.pure y`.  `W ## Dr` (gset disjointness) ↦
   `∀ r, r ∈ W → r ∉ Dr`.
2. FILE-QUALIFIED (clash with `MachCSL.WireInv`'s `wireN`/`wireInv`, both reachable under
   `open MachCSL`): `WeakEvWire.wireN`, `WeakEvWire.wireInv`, `WeakEvWire.wireInv_persistent`.
3. lean-sail's `regRead r` carries no `direct` flag: `ewpEvRegReadFree`/`Inv`/`ewpEvWireRead` and
   `ewrunWire` drop Rocq's `direct` binder.  `ewrunRead` also binds the request's VA width `va`
   (`WeakEvFunnel` deviation 3).
4. THE PLIC IS A PROGRAM (forced by `Weak/WeakEvLang.lean` deviation 2): Rocq's stateless
   `EPlic gen` (whose only move is the wire write) is `.EDev gen .plic rootTask m`, a residual
   program of `MachCSL.Plic.body` stepped by `wdevStep`; the thread `epowerFork` forks is the
   one at `m = .pure ()`.  Consequences:
   - `ewpPlicStep` is the core lifting rule at ANY PLIC program `m`: the continuation is
     quantified over every `wdevStep` successor `(m', σ', efs)` and owes `efs = []` (Rocq: over
     the hart the wire write targets).  It is the instance of the Lean-only generic rule
     `WeakEvWire.ewpEdev`.  Its reducibility is free (`eprimStepDevLive`).
   - The PLIC program also MOVES ITS OWN STATE (the gateway's latch, a `step`), which
     `weakStateInterp` mirrors in `devInterpAt`.  So `ewpPlic` needs, besides `wireInv`, the
     PLIC's device fragment: the Lean-only invariant `WeakEvWire.plicInv`
     (`∃ p, devFragAt era .plic p`, namespace `WeakEvWire.plicN`), allocated from the fragment
     the adequacy package hands out (`WeakEvWire.plicInvAlloc`).  Rocq: `wire_inv` alone.
   - `ewpPlic` is proven through the Lean-only `WeakEvWire.ewpPlicProg`: every PLIC program
     with no bus-master write (`WeakEvWire.DevNoDma`, closed under the step; `Plic.body` is one,
     `WeakEvWire.plicBodyNoDma`) has a WP, by Löb.  A `dmaWrite` would append to the log, which
     the board's PLIC never does.  The fork arm is impossible (`DevTask .plic = Empty`).
5. O2 — THE FETCH (`WeakEvLift` deviation 2, `WeakEvFunnel` deviation 2): `ewpEwrunFetch` and
   `ewpInstr` take `ak.akIfetch = true` (Rocq: `ak_coh ak = false ∧ ak_latest ak = false`); the
   fetch moves no view, so Rocq's `efetch_ws`/`efetch_ws_le` steps vanish (the continuation still
   gets some `ws' ⊒ ws`).
6. `wireInvAlloc` takes `rs : CPU → RegFile` (Rocq `regstate`) and the cells
   `regPointsTo c r (own 1) (rs c r)`.

**Rocq → Lean name map.**  `wireN` `WeakEvWire.wireN`, `wireregs` `wireregs`, `sig_seip_wire`
`sigSeipWire`, `sig_meip_wire` `sigMeipWire`, `wire_cell` `wireCell`, `wire_bodies`
`wireBodies`, `wire_inv` `WeakEvWire.wireInv`, `wire_inv_persistent`
`WeakEvWire.wireInv_persistent`, `wire_inv_alloc` `wireInvAlloc`, `wire_bodies_acc`
`wireBodiesAcc`, `ewp_plic_step` `ewpPlicStep`, `ewp_plic` `ewpPlic`, `ewp_ev_reg_read_free`
`ewpEvRegReadFree`, `ewp_ev_reg_read_inv` `ewpEvRegReadInv`, `ewp_ev_wire_read`
`ewpEvWireRead`, `eset_regs` `esetRegs`, `ewrun` `ewrun` (`ewrun_stop/node/wire/read`
`ewrun.ewrunStop/ewrunNode/ewrunWire/ewrunRead`), `erun_ewrun` `erunEwrun`, `ewp_ewrun_nil`
`ewpEwrunNil`, `ewp_ewrun_fetch` `ewpEwrunFetch`, `ewp_instr` `ewpInstr`.
Lean-only (file-qualified): `WeakEvWire.plicN`, `WeakEvWire.plicInv` (+ `_persistent`),
`WeakEvWire.plicInvAlloc`, `WeakEvWire.isDma`, `WeakEvWire.DevNoDma`, `WeakEvWire.devNoDmaBind`,
`WeakEvWire.devNoDmaLift`, `WeakEvWire.plicBodyNoDma`, `WeakEvWire.ewpEdev`,
`WeakEvWire.wireWrite`, `WeakEvWire.wireSetPin`, `WeakEvWire.ewpPlicSilent`,
`WeakEvWire.ewpPlicProg`.

**Dropped:** nothing (19 Rocq `Definition`/`Lemma`/`Theorem`/`Inductive`/`Instance`s, all
ported; + 14 Lean-only).

**Statements checked** (by hand, against Rocq): all; the changed ones are the deviations above.
-/
import Weak.WeakEvFunnel
import Weak.WeakEvDisk

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.ProgramLogic
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE WIRE INVARIANT -/

def WeakEvWire.wireN : Namespace := ndot nroot "weakwire"

/-- The two registers the PLIC thread and the hart SHARE. -/
def wireregs : List Register := [.sig_seip, .sig_meip]

theorem sigSeipWire : Register.sig_seip ∈ wireregs := by simp [wireregs]
theorem sigMeipWire : Register.sig_meip ∈ wireregs := by simp [wireregs]

section wire

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

abbrev wireCell (c : CPU) (r : Register) : IProp GF :=
  iprop(∃ v : RegisterType r, regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) v)

abbrev wireBodies : IProp GF :=
  iprop([∗list] c ∈ cpus, [∗list] r ∈ wireregs, wireCell (hlc := hlc) (GF := GF) c r)

def WeakEvWire.wireInv : IProp GF :=
  inv WeakEvWire.wireN (wireBodies (hlc := hlc) (GF := GF))

instance WeakEvWire.wireInv_persistent :
    Persistent (WeakEvWire.wireInv (hlc := hlc) (GF := GF)) := by
  unfold WeakEvWire.wireInv; infer_instance

/-- ESTABLISHED AT BOOT, from the register points-tos of the WP package (deviation 6). -/
theorem wireInvAlloc (rs : CPU → RegFile) (E : CoPset) :
    ([∗list] c ∈ cpus, [∗list] r ∈ wireregs,
        regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) (rs c r)) ⊢
      |={E}=> WeakEvWire.wireInv (hlc := hlc) (GF := GF) := by
  have hb : ([∗list] c ∈ cpus, [∗list] r ∈ wireregs,
        regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) (rs c r)) ⊢
      wireBodies (hlc := hlc) (GF := GF) :=
    BigSepL.bigSepL_mono fun {_ c} _ => BigSepL.bigSepL_mono fun {_ r} _ =>
      exists_intro (Ψ := fun v : RegisterType r =>
        regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) v) (rs c r)
  iintro H
  ihave Hb := hb $$ H
  imod inv_alloc WeakEvWire.wireN E (wireBodies (hlc := hlc) (GF := GF)) $$ [Hb] with #Hinv
  · iapply later_intro
    iexact Hb
  imodintro
  unfold WeakEvWire.wireInv
  iexact Hinv

/-- Access to ONE hart's ONE wire cell. -/
theorem wireBodiesAcc (c : CPU) (r : Register) :
    r ∈ wireregs →
    wireBodies (hlc := hlc) (GF := GF) ⊢
      wireCell (hlc := hlc) (GF := GF) c r ∗
        (wireCell (hlc := hlc) (GF := GF) c r -∗ wireBodies (hlc := hlc) (GF := GF)) := by
  intro hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
  iintro H
  icases BigSepL.bigSepL_lookup_acc_impl
      (Φ := fun _ c => iprop([∗list] r ∈ wireregs, wireCell (hlc := hlc) (GF := GF) c r))
      (cpus_get? c) $$ H with ⟨Hc, Hclose⟩
  icases BigSepL.bigSepL_lookup_acc_impl
      (Φ := fun _ r => wireCell (hlc := hlc) (GF := GF) c r) hi $$ Hc with ⟨Hcell, Hclose2⟩
  iframe Hcell
  iintro Hcell
  iapply Hclose $$ %(fun _ c => iprop([∗list] r ∈ wireregs, wireCell (hlc := hlc) (GF := GF) c r))
  · imodintro
    iintro %k %y %_ %_ Hy
    iexact Hy
  · iapply Hclose2 $$ %(fun _ r => wireCell (hlc := hlc) (GF := GF) c r)
    · imodintro
      iintro %k %y %_ %_ Hy
      iexact Hy
    · iexact Hcell

end wire

/-! ## 2. THE PLIC THREAD'S RULE (deviation 4) -/

/-- The PLIC's own state, shared with every agent that moves it (Lean-only). -/
def WeakEvWire.plicN : Namespace := ndot nroot "weakplicstate"

/-- Is the primitive a bus-master write (Lean-only). -/
def WeakEvWire.isDma {S T : Type} : DevOp S T → Bool
  | .dmaWrite .. => true
  | _ => false

/-- A device program with no bus-master write anywhere (Lean-only). -/
inductive WeakEvWire.DevNoDma {S T α : Type} : DevM S T α → Prop where
  | pure (a : α) : WeakEvWire.DevNoDma (.pure a)
  | op (o : DevOp S T) (k : o.ret → DevM S T α) :
      WeakEvWire.isDma o = false → (∀ v, WeakEvWire.DevNoDma (k v)) →
      WeakEvWire.DevNoDma (.op o k)

theorem WeakEvWire.devNoDmaBind {S T α β : Type} {m : DevM S T α} {f : α → DevM S T β}
    (hm : WeakEvWire.DevNoDma m) (hf : ∀ a, WeakEvWire.DevNoDma (f a)) :
    WeakEvWire.DevNoDma (m >>= f) := by
  induction hm with
  | pure a => exact hf a
  | op o k ho _ ih => exact WeakEvWire.DevNoDma.op o (fun r => k r >>= f) ho ih

theorem WeakEvWire.devNoDmaLift {S T : Type} (o : DevOp S T) (ho : WeakEvWire.isDma o = false) :
    WeakEvWire.DevNoDma (DevM.lift o) :=
  WeakEvWire.DevNoDma.op o _ ho fun v => WeakEvWire.DevNoDma.pure v

theorem WeakEvWire.plicBodyNoDma : WeakEvWire.DevNoDma Plic.body := by
  unfold Plic.body DevM.chooseLt DevM.chooseBool DevM.sample DevM.modify DevM.step DevM.get
    DevM.setPin DevM.choose
  repeat
    first
    | exact WeakEvWire.devNoDmaLift _ rfl
    | exact WeakEvWire.DevNoDma.pure _
    | apply WeakEvWire.devNoDmaBind
    | intro _
    | split

section plic

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

def WeakEvWire.plicInv : IProp GF :=
  inv WeakEvWire.plicN
    iprop(∃ p : PlicState, devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p)

instance WeakEvWire.plicInv_persistent :
    Persistent (WeakEvWire.plicInv (hlc := hlc) (GF := GF)) := by
  unfold WeakEvWire.plicInv; infer_instance

theorem WeakEvWire.plicInvAlloc (p : PlicState) (E : CoPset) :
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ⊢
      |={E}=> WeakEvWire.plicInv (hlc := hlc) (GF := GF) := by
  iintro H
  imod inv_alloc WeakEvWire.plicN E
    iprop(∃ p : PlicState, devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p)
    $$ [H] with #Hinv
  · iapply later_intro
    iexists p
    iexact H
  imodintro
  unfold WeakEvWire.plicInv
  iexact Hinv

/-- THE CORE LIFTING RULE for a device thread (Lean-only; reducibility is free). -/
theorem WeakEvWire.ewpEdev (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) :
    gen = 0 →
    (∀ σ : WGState, weakStateInterp (hlc := hlc) (GF := GF) σ ={⊤,∅}=∗
      ▷ (∀ (m' : DevProg d) (σ' : WGState) (efs0 : List WExpr),
          ⌜wdevStep gen d tid m σ m' σ' efs0⌝ ={∅,⊤}=∗
          ⌜efs0 = []⌝ ∗ weakStateInterp (hlc := hlc) (GF := GF) σ' ∗
            ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen d tid m'))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen d tid m) := by
  intro hgen
  iintro H
  unfold ewpTriv
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  rw [weakStateInterpEq]
  icases weakStateInterpPin σ $$ Hσ with ⟨%Hpin, Hσ⟩
  have hlive : ethreadLive σ gen := ⟨Hpin.1, by rw [hgen]; exact Hpin.2⟩
  imod H $$ %σ Hσ with Hk
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', σ', efs, hs⟩ := eprimStepDevLive gen d tid m σ hlive
    exact ⟨[], e', σ', efs, hs⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨_, harm⟩ := eprimStepDevInv gen d tid m σ obs e₂ σ₂ eₜ Hstep
  rcases harm with ⟨_, m', efs0, rfl, hst, rfl⟩ | ⟨hnl, _⟩
  case inr => exact absurd hlive hnl
  imod Hk $$ %m' %σ₂ %efs0 %hst with ⟨%hnil, Hσ', HWP⟩
  subst hnil
  imodintro
  rw [weakStateInterpEq]
  isplitl [Hσ']
  · iexact Hσ'
  isplitl [HWP]
  · iexact HWP
  · exact BigSepL.bigSepL_nil_intro

/-- Rocq `ewp_plic_step` (deviation 4): the one-step rule of the PLIC program. -/
theorem ewpPlicStep (gen : Nat) (m : DevProg .plic) :
    gen = 0 →
    (∀ σ : WGState, weakStateInterp (hlc := hlc) (GF := GF) σ ={⊤,∅}=∗
      ▷ (∀ (m' : DevProg .plic) (σ' : WGState) (efs0 : List WExpr),
          ⌜wdevStep gen .plic rootTask m σ m' σ' efs0⌝ ={∅,⊤}=∗
          ⌜efs0 = []⌝ ∗ weakStateInterp (hlc := hlc) (GF := GF) σ' ∗
            ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen .plic rootTask m'))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen .plic rootTask m) :=
  fun hgen => WeakEvWire.ewpEdev gen .plic rootTask m hgen

/-- THE WIRE WRITE on the interpretation, through the wire bodies (Lean-only). -/
theorem WeakEvWire.wireWrite (σ : WGState) (cpu : CPU) (r : Register) (hr : r ∈ wireregs)
    (v : RegisterType r) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ∗ wireBodies (hlc := hlc) (GF := GF) ⊢
      |==> (weakStateInterp (hlc := hlc) (GF := GF) (σ.setReg cpu r v) ∗
        wireBodies (hlc := hlc) (GF := GF)) := by
  iintro ⟨Hσ, Hb⟩
  icases wireBodiesAcc (hlc := hlc) (GF := GF) cpu r hr $$ Hb with ⟨⟨%v0, Hr⟩, Hcb⟩
  icases weakStateInterpRegs σ cpu $$ Hσ with ⟨Hri, Hcl⟩
  imod reg_update cpu (σ.wgregs cpu) r v0 v $$ [$Hri $Hr] with ⟨Hri, Hr⟩
  imodintro
  isplitl [Hcl Hri]
  · iapply (show weakStateInterp (hlc := hlc) (GF := GF) (ewgReg σ cpu ((σ.wgregs cpu).set r v)) ⊢
        weakStateInterp (hlc := hlc) (GF := GF) (σ.setReg cpu r v) from .rfl)
    iapply Hcl $$ %((σ.wgregs cpu).set r v) Hri
  · iapply Hcb
    iexists v
    iexact Hr

theorem WeakEvWire.wireSetPin (gen : Nat) (cpu : CPU) (mm b : Bool) (σ σ' : WGState) (v : Unit)
    (efs : List WExpr) :
    wdevOpStep gen .plic (.setPin cpu mm b) σ v σ' efs →
    weakStateInterp (hlc := hlc) (GF := GF) σ ∗ wireBodies (hlc := hlc) (GF := GF) ⊢
      |==> (weakStateInterp (hlc := hlc) (GF := GF) σ' ∗ wireBodies (hlc := hlc) (GF := GF)) := by
  intro h
  obtain ⟨-, rfl⟩ := h
  cases mm
  · exact WeakEvWire.wireWrite σ cpu .sig_seip sigSeipWire _
  · exact WeakEvWire.wireWrite σ cpu .sig_meip sigMeipWire _

/-- A PLIC primitive that moves nothing (Lean-only). -/
theorem WeakEvWire.ewpPlicSilent (gen : Nat) (o : DevOp (DevSt .plic) (DevTask .plic))
    (k : o.ret → DevProg .plic) :
    gen = 0 →
    (∀ σ v σ' efs, wdevOpStep gen .plic o σ v σ' efs → σ' = σ ∧ efs = []) →
    ▷ (∀ m' : DevProg .plic, ⌜m' = .op o k ∨ ∃ v, m' = k v⌝ -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen .plic rootTask m')) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen .plic rootTask (.op o k)) := by
  intro hgen hsil
  iintro H
  iapply WeakEvWire.ewpEdev gen .plic rootTask _ hgen
  iintro %σ Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  inext
  iintro %m' %σ' %efs0 %hst
  imod Hmask
  rcases hst with ⟨v, rfl, hop⟩ | ⟨-, rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hsil _ _ _ _ hop
    imodintro
    isplitr
    · ipureintro; rfl
    iframe Hσ
    iapply H $$ %(k v) %(Or.inr ⟨v, rfl⟩)
  · imodintro
    isplitr
    · ipureintro; rfl
    iframe Hσ
    iapply H $$ %_ %(Or.inl rfl)

/-- EVERY dma-free PLIC program has a WP, from the two invariants (Lean-only). -/
theorem WeakEvWire.ewpPlicProg (gen : Nat) :
    gen = 0 →
    WeakEvWire.wireInv (hlc := hlc) (GF := GF) ∗ WeakEvWire.plicInv (hlc := hlc) (GF := GF) ⊢
      ∀ m : DevProg .plic, ⌜WeakEvWire.DevNoDma m⌝ -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen .plic rootTask m) := by
  intro hgen
  iintro ⟨#Hw, #Hp⟩
  iloeb as IH
  iintro %m %hm
  have hm0 := hm
  cases hm with
  | pure a =>
    iapply WeakEvWire.ewpEdev gen .plic rootTask _ hgen
    iintro %σ Hσ
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hmask
    inext
    iintro %m' %σ' %efs0 %hst
    imod Hmask
    obtain ⟨rfl, ⟨-, rfl, rfl⟩ | ⟨hne, -⟩⟩ := hst
    case inr => exact absurd rfl hne
    imodintro
    isplitr
    · ipureintro; rfl
    iframe Hσ
    iapply IH $$ %((devSig .plic).body) %WeakEvWire.plicBodyNoDma
  | op o k ho hk =>
    cases o with
    | step f =>
      iapply WeakEvWire.ewpEdev gen .plic rootTask _ hgen
      iintro %σ Hσ
      unfold WeakEvWire.plicInv
      imod (inv_acc (E := ⊤) (N := WeakEvWire.plicN)
        (P := iprop(∃ p : PlicState,
          devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p))
        CoPset.subseteq_top) $$ Hp with ⟨HI, Hclose⟩
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hmask
      inext
      iintro %m' %σ' %efs0 %hst
      imod Hmask
      icases HI with ⟨%p, Hf⟩
      rcases hst with ⟨v, rfl, s', os, -, -, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
      · icases weakStateInterpDev σ $$ Hσ with ⟨Hdev, Hcl⟩
        icases ediskDevAcc σ.wgdev .plic $$ Hdev with ⟨Ha, Hcla⟩
        imod devUpdateAt (MachGS.era (hlc := hlc) (GF := GF)) .plic _ p s' $$ [$Ha $Hf]
          with ⟨Ha, Hf⟩
        imod Hclose $$ [Hf]
        · inext
          iexists s'
          iexact Hf
        imodintro
        isplitr
        · ipureintro; rfl
        isplitl [Hcl Hcla Ha]
        · iapply (show weakStateInterp (hlc := hlc) (GF := GF) (ewgDev σ (σ.wgdev.set .plic s')) ⊢
            weakStateInterp (hlc := hlc) (GF := GF) (σ.setDev .plic s') from .rfl)
          iapply Hcl $$ %(σ.wgdev.set .plic s')
          iapply Hcla $$ %s' Ha
        · iapply IH $$ %(k v) %(hk v)
      · imod Hclose $$ [Hf]
        · inext
          iexists p
          iexact Hf
        imodintro
        isplitr
        · ipureintro; rfl
        iframe Hσ
        iapply IH $$ %_ %hm0
    | setPin cpu mm b =>
      iapply WeakEvWire.ewpEdev gen .plic rootTask _ hgen
      iintro %σ Hσ
      unfold WeakEvWire.wireInv
      imod (inv_acc (E := ⊤) (N := WeakEvWire.wireN) (P := wireBodies (hlc := hlc) (GF := GF))
        CoPset.subseteq_top) $$ Hw with ⟨HI, Hclose⟩
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hmask
      inext
      iintro %m' %σ' %efs0 %hst
      imod Hmask
      rcases hst with ⟨v, rfl, hop⟩ | ⟨hbl, -⟩
      case inr => exact hbl.elim
      have hnil : efs0 = [] := hop.1
      subst hnil
      imod WeakEvWire.wireSetPin gen cpu mm b σ σ' v [] hop $$ [$Hσ $HI] with ⟨Hσ, HI⟩
      imod Hclose $$ [HI]
      · inext
        iexact HI
      imodintro
      isplitr
      · ipureintro; rfl
      iframe Hσ
      iapply IH $$ %(k v) %(hk v)
    | dmaWrite g pa n w => simp [WeakEvWire.isDma] at ho
    | fork t => exact t.elim
    | get =>
      iapply WeakEvWire.ewpPlicSilent gen _ k hgen
        (fun σ v σ' efs h => by obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      inext
      iintro %m' %hm'
      iapply IH $$ %m' %(by rcases hm' with rfl | ⟨v, rfl⟩ <;> first | exact hm0 | exact hk _)
    | choose =>
      iapply WeakEvWire.ewpPlicSilent gen _ k hgen
        (fun σ v σ' efs h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      inext
      iintro %m' %hm'
      iapply IH $$ %m' %(by rcases hm' with rfl | ⟨v, rfl⟩ <;> first | exact hm0 | exact hk _)
    | dmaRead pa n =>
      iapply WeakEvWire.ewpPlicSilent gen _ k hgen
        (fun σ v σ' efs h => by obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      inext
      iintro %m' %hm'
      iapply IH $$ %m' %(by rcases hm' with rfl | ⟨v, rfl⟩ <;> first | exact hm0 | exact hk _)
    | sample src =>
      iapply WeakEvWire.ewpPlicSilent gen _ k hgen
        (fun σ v σ' efs h => by obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      inext
      iintro %m' %hm'
      iapply IH $$ %m' %(by rcases hm' with rfl | ⟨v, rfl⟩ <;> first | exact hm0 | exact hk _)
    | join tid =>
      iapply WeakEvWire.ewpPlicSilent gen _ k hgen
        (fun σ v σ' efs h => by obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      inext
      iintro %m' %hm'
      iapply IH $$ %m' %(by rcases hm' with rfl | ⟨v, rfl⟩ <;> first | exact hm0 | exact hk _)

/-- THE PLIC THREAD'S WP, discharged once and for all (deviation 4: with `plicInv`). -/
theorem ewpPlic (gen : Nat) :
    gen = 0 →
    WeakEvWire.wireInv (hlc := hlc) (GF := GF) ∗ WeakEvWire.plicInv (hlc := hlc) (GF := GF) ⊢
      ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDev gen .plic rootTask (.pure ())) := by
  intro hgen
  iintro H
  iapply WeakEvWire.ewpPlicProg gen hgen $$ H %(.pure ()) %(WeakEvWire.DevNoDma.pure ())

end plic

/-! ## 3. A HART'S READ OF A REGISTER IT DOES NOT OWN -/

section read

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- THE FREE FORM: a `regRead` of an unowned register needs NO resource at all. -/
theorem ewpEvRegReadFree (gen : Nat) (c : CPU) (r : Register) (k : RegisterType r → SailM Unit) :
    gen = 0 →
    ▷ (∀ v : RegisterType r, ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (k v) none)) ⊢
      ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.regRead r)) k) none) := by
  intro hgen
  iintro H
  iapply ewpEcycle gen c _ none hgen
  iintro %σ Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    exact ⟨_, _, rfl, rfl⟩
  inext
  iintro %e' %σ' %hcy
  obtain ⟨rfl, rfl⟩ := hcy
  imod Hmask
  imodintro
  rw [weakStateInterpIb]
  iframe Hσ
  iapply H

/-- THE INVARIANT FORM: the live value is read THROUGH an invariant owning the cell. -/
theorem ewpEvRegReadInv (gen : Nat) (c : CPU) (r : Register) (N : Namespace)
    (P : RegisterType r → IProp GF) (k : RegisterType r → SailM Unit) :
    gen = 0 →
    inv N iprop(∃ v : RegisterType r, regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) v ∗ P v) ∗
      ▷ (∀ v : RegisterType r,
          P v -∗ P v ∗ ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (k v) none)) ⊢
      ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.regRead r)) k) none) := by
  intro hgen
  iintro ⟨#Hinv, H⟩
  iapply ewpEcycle gen c _ none hgen
  iintro %σ Hσ
  imod (inv_acc (E := ⊤) (N := N)
    (P := iprop(∃ v : RegisterType r, regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) v ∗ P v))
    CoPset.subseteq_top) $$ Hinv with ⟨Hb, Hclose⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    exact ⟨_, _, rfl, rfl⟩
  inext
  iintro %e' %σ' %hcy
  obtain ⟨rfl, rfl⟩ := hcy
  imod Hmask
  icases Hb with ⟨%v, Hr, HP⟩
  icases weakStateInterpRegs σ c $$ Hσ with ⟨Hri, Hcl⟩
  ihave ⟨%hlk, Hri, Hr⟩ := persistent_entails_right
    (reg_valid c (σ.wgregs c) r (DFrac.own 1) v) $$ [Hri Hr]
  · iframe Hri Hr
  icases H $$ %v HP with ⟨HP, H⟩
  imod Hclose $$ [Hr HP]
  · inext
    iexists v
    iframe Hr HP
  imodintro
  rw [weakStateInterpIb, hlk]
  isplitl [Hri Hcl]
  · iapply weakStateInterpRegId σ c
    iapply Hcl $$ %(σ.wgregs c) Hri
  · iexact H

/-- ... at the wire invariant itself. -/
theorem ewpEvWireRead (gen : Nat) (c : CPU) (r : Register) (k : RegisterType r → SailM Unit) :
    gen = 0 → r ∈ wireregs →
    WeakEvWire.wireInv (hlc := hlc) (GF := GF) ∗
      ▷ (∀ v : RegisterType r, ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (k v) none)) ⊢
      ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (.impure (.ok (.regRead r)) k) none) := by
  intro hgen _
  iintro ⟨-, H⟩
  iapply ewpEvRegReadFree gen c r k hgen $$ H

end read

/-! ## 4. THE BRANCHING CERTIFICATE, AND THE FUNNEL WITH THE WIRES OUT -/

def esetRegs (t : ExecSt) (rs : RegFile) : ExecSt := { t with regs := rs }

@[simp] theorem esetRegs_regs (t : ExecSt) (rs : RegFile) : (esetRegs t rs).regs = rs := rfl

/-- `WeakEvFunnel.erun` as a RELATION, with the volatile arm `ewrunWire`. -/
inductive ewrun (Dr Dw W : List Register) :
    SailM Unit → ExecSt → SailM Unit → ExecSt → List Weff → Prop where
  | ewrunStop (m : SailM Unit) (t : ExecSt) : ewrun Dr Dw W m t m t []
  | ewrunNode (m m' mf : SailM Unit) (t tf : ExecSt) (rs' : RegFile) (es : List Weff) :
      esilNode2 Dr Dw t.regs m = some (rs', m') →
      ewrun Dr Dw W m' (esetRegs t rs') mf tf es →
      ewrun Dr Dw W m t mf tf es
  | ewrunWire (r : Register) (k : RegisterType r → SailM Unit) (t : ExecSt) (mf : SailM Unit)
      (tf : ExecSt) (es : List Weff) :
      r ∈ W →
      (∀ v : RegisterType r, ewrun Dr Dw W (k v) (t.setReg r v) mf tf es) →
      ewrun Dr Dw W (.impure (.ok (.regRead r)) k) t mf tf es
  | ewrunRead (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (K : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit)
      (t : ExecSt) (w : BitVec (8 * n)) (mf : SailM Unit) (tf : ExecSt) (es : List Weff) :
      devAddr req.pa = false →
      bmRead t.mem req.pa n = some w →
      ewrun Dr Dw W (K (.Ok (w, none))) t mf tf es →
      ewrun Dr Dw W (.impure (.ok (.memRead n va req)) K) t mf tf
        (.WEread (classify req.access_kind) req.pa n :: es)

/-- A WIRE-FREE certificate is one of these. -/
theorem erunEwrun (Dr Dw W : List Register) (m : SailM Unit) :
    ∀ t y t' es, erun Dr Dw m t = some (y, t', es) → ewrun Dr Dw W m t (FreeM.pure y) t' es := by
  induction m with
  | pure y0 =>
    intro t y t' es h
    simp only [erun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    cases y0; cases y
    exact .ewrunStop _ _
  | impure call k ih =>
    intro t y t' es h
    cases call with
    | error e => simp [erun] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ Dr
        · simp only [erun, hr, ↓reduceIte] at h
          exact .ewrunNode _ (k (t.regs r)) _ t _ t.regs _ (by simp [esilNode2, hr])
            (ih _ _ _ _ _ h)
        · simp [erun, hr] at h
      case regWrite r v =>
        by_cases hr : r ∈ Dw
        · simp only [erun, hr, ↓reduceIte] at h
          exact .ewrunNode _ (k PUnit.unit) _ t _ (t.regs.set r v) _ (by simp [esilNode2, hr])
            (ih _ _ _ _ _ h)
        · simp [erun, hr] at h
      case memRead n va req =>
        by_cases hd : devAddr req.pa = true
        · simp [erun, hd] at h
        · cases hrb : bmRead t.mem req.pa n with
          | none => simp [erun, hd, hrb] at h
          | some w =>
            simp only [erun, hd, hrb, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            exact .ewrunRead n va req k t w _ _ _ (by simpa using hd) hrb (ih _ _ _ _ _ h0)
      all_goals first
        | (simp [erun] at h; done)
        | (simp only [erun] at h
           exact .ewrunNode _ _ _ t _ t.regs _ (by simp [esilNode2]) (ih _ _ _ _ _ h))

section wrun

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- THE WIRE-CROSSING WALK. -/
theorem ewpEwrunNil (gen : Nat) (c : CPU) (Dr Dw W : List Register) (q : Register → DFrac)
    (m mf : SailM Unit) (t tf : ExecSt) (es : List Weff) (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    (∀ r, r ∈ W → r ∉ Dr) → es = [] →
    ewrun Dr Dw W m t mf tf es →
    hartWs (GF := GF) c ws ∗ eregFr (hlc := hlc) (GF := GF) c t.regs Dr q ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
        eregFr (hlc := hlc) (GF := GF) c tf.regs Dr q -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c mf none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hsub hq hdisj hes hrun
  revert hes
  induction hrun generalizing ws with
  | ewrunStop m t =>
    intro _
    iintro ⟨Hws, Hrf, H⟩
    iapply H $$ %ws %(wsDepmoveRefl ws) Hws Hrf
  | ewrunNode m m' mf t tf rs' es hnode _ ih =>
    intro hes
    iintro ⟨Hws, Hrf, H⟩
    iapply ewpEvNode2 gen c Dr Dw q t.regs m m' rs' ws hgen hsub hq hnode
    iframe Hws Hrf
    inext
    iintro %ws1 %hd1 Hws Hrf
    iapply ih ws1 hes
    rw [esetRegs_regs]
    iframe Hws Hrf
    iintro %ws2 %hd2 Hws Hrf
    iapply H $$ %ws2 %(wsDepmoveTrans hd1 hd2) Hws Hrf
  | ewrunWire r k t mf tf es hr _ ih =>
    intro hes
    iintro ⟨Hws, Hrf, H⟩
    iapply ewpEvRegReadFree gen c r k hgen
    inext
    iintro %v
    iapply ih v ws hes
    rw [ExecSt.setReg_regs]
    iframe Hws H
    iapply (eregFrSetNe (hlc := hlc) (GF := GF) c t.regs Dr q r v (hdisj r hr)).2 $$ Hrf
  | ewrunRead => intro hes; simp at hes

/-- ... and the one-fetch form (deviation 5: the fetch is an i-cache read). -/
theorem ewpEwrunFetch (gen : Nat) (c : CPU) (Dr Dw W : List Register) (q : Register → DFrac)
    (m mf : SailM Unit) (t tf : ExecSt) (es : List Weff) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    (∀ r, r ∈ W → r ∉ Dr) → es = [.WEread ak pa n] →
    ak.akIfetch = true →
    ewrun Dr Dw W m t mf tf es →
    bmRead t.mem pa n = some w →
    etextWord (GF := GF) (paZ pa) n w ∗ eregFr (hlc := hlc) (GF := GF) c t.regs Dr q ∗
      hartWs (GF := GF) c ws ∗
      (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗
        eregFr (hlc := hlc) (GF := GF) c tf.regs Dr q -∗ hartWs (GF := GF) c ws' -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c mf none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hsub hq hdisj hes hif hrun
  revert hes
  induction hrun generalizing ws with
  | ewrunStop m t => intro hes; simp at hes
  | ewrunNode m m' mf t tf rs' es hnode _ ih =>
    intro hes hw
    iintro ⟨#Ht, Hrf, Hws, H⟩
    iapply ewpEvNode2 gen c Dr Dw q t.regs m m' rs' ws hgen hsub hq hnode
    iframe Hws Hrf
    inext
    iintro %ws1 %hd1 Hws Hrf
    iapply ih ws1 hes hw
    rw [esetRegs_regs]
    iframe Ht Hrf Hws
    iintro %ws2 %hle2 Hrf Hws
    iapply H $$ %ws2 %(wsLeTrans (wsDepmoveLe _ _ hd1) hle2) Hrf Hws
  | ewrunWire r k t mf tf es hr _ ih =>
    intro hes hw
    iintro ⟨#Ht, Hrf, Hws, H⟩
    iapply ewpEvRegReadFree gen c r k hgen
    inext
    iintro %v
    iapply ih v ws hes hw
    rw [ExecSt.setReg_regs]
    iframe Ht Hws H
    iapply (eregFrSetNe (hlc := hlc) (GF := GF) c t.regs Dr q r v (hdisj r hr)).2 $$ Hrf
  | ewrunRead n0 va req K t w0 mf tf es hdev hrd hrun0 _ =>
    intro hes hw
    simp only [List.cons.injEq, Weff.WEread.injEq] at hes
    obtain ⟨⟨hak, hpa, rfl⟩, hes0⟩ := hes
    subst hak
    subst hpa
    have hww : w0 = w := by
      rw [hw] at hrd
      exact (Option.some.inj hrd).symm
    subst hww
    iintro ⟨#Ht, Hrf, Hws, H⟩
    iapply ewpEvFetch gen c n0 va req K w0 ws hgen hdev hif
    iframe Ht Hws
    inext
    iintro Hws
    iapply ewpEwrunNil gen c Dr Dw W q (K (.Ok (w0, none))) mf t tf es ws hgen hsub hq hdisj hes0
      hrun0
    iframe Hws Hrf
    iintro %ws3 %hd3 Hws Hrf
    iapply H $$ %ws3 %(wsDepmoveLe _ _ hd3) Hrf Hws

/-- THE FUNNEL, WITH THE WIRES OUT OF THE FOOTPRINT. -/
theorem ewpInstr (gen : Nat) (c : CPU) (Dr Dw : List Register) (q : Register → DFrac)
    (t : ExecSt) (tp : Bool → ExecSt) (ak : AkInfo) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    (∀ r, r ∈ wireregs → r ∉ Dr) →
    (∀ tick : Bool,
      ewrun Dr Dw wireregs (riscvStep tick) t (FreeM.pure ()) (tp tick) [.WEread ak pa n]) →
    bmRead t.mem pa n = some w →
    ak.akIfetch = true →
    etextWord (GF := GF) (paZ pa) n w ∗ eregFr (hlc := hlc) (GF := GF) c t.regs Dr q ∗
      hartWs (GF := GF) c ws ∗
      ▷ (∀ (tick : Bool) (ws' : Wstate), ⌜wsLe ws ws'⌝ -∗
          eregFr (hlc := hlc) (GF := GF) c (tp tick).regs Dr q -∗ hartWs (GF := GF) c ws' -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c) := by
  intro hgen hsub hq hdisj hcert hw hif
  iintro ⟨#Ht, Hrf, Hws, H⟩
  iapply ewpEloop gen c ws hgen
  isplitl [Hws]
  · iexact Hws
  inext
  iintro %tick Hws
  iapply ewpEwrunFetch gen c Dr Dw wireregs q (riscvStep tick) (FreeM.pure ()) t (tp tick)
    [.WEread ak pa n] ak pa n w (instrPost ws) hgen hsub hq hdisj rfl hif (hcert tick) hw
  iframe Ht Hrf Hws
  iintro %ws' %hle Hrf Hws
  iapply ewpEvRet gen c () hgen
  iapply H $$ %tick %ws' %(wsLeTrans (instrPostLe ws) hle) Hrf Hws

end wrun

end Weak
