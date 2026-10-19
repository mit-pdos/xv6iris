/-
MachCSL: THE POWER THREAD AND ITS ADEQUACY, RECORDING THE READ-ONLY WINDOW
(weak-allocproc plan §C Stage 0, item W3, option (A); PROGRESS-W3.md).

Twins of `MachCSL.wp_power` (`MachCSL/Power.lean`) and
`MachCSL.riscvPowerAdequacy` (`MachCSL/Adequacy.lean`), parametric in an
address window `[lo, hi)`; every existing statement is unchanged [OWN.9].
What changes, at `PowerOn` only:

* the trace invariant, opened for the client's power hook `Hobs`, STAYS OPEN
  while the fresh era is minted: its predicate is left at a client-chosen
  pending content `Pon h` (the on-arm), which no other party ever sees;
* once the era is registered at its generation, the power thread PERSISTS
  the window's byte histories itself (`memCells_win`: the fully owned cells
  of `[lo, hi)` become discarded points-to, `winRoAt`) and runs the new
  TRACE HOOK `HtextRec`, which restores the predicate from the pending
  content, the era's registry element and the persisted window; only then
  is the invariant closed (no other invariant is opened in between: the
  crash hooks run after, as in `wp_power`);
* the boot client gets the window PERSISTED and the rest of the memory
  cells owned (`powerBootResT`: `memCells E σ.mem` split as
  `winRoAt E.mem σ.mem lo hi ∗ memCellsOut E σ.mem lo hi`).

Why the record cannot be made through `wp_power` (PROGRESS-W3.md): there,
`Hobs` closes the invariant before the era exists, so the predicate would
have to admit a "powered on, not yet recorded" content that the final hook
`Hphi` (holding only `powerInterp`) cannot rule out.  Here that content
lives only inside one atomic step, with the invariant open.

Machine semantics, assumptions and the client's other obligations are
`wp_power`'s / `riscvPowerAdequacy`'s verbatim (the bodies are near-copies);
the trace slot `Pt`/`Pon` of the adequacy twin is also given the registry's
gname, so that a slot can name the era a generation runs.
-/
import MachCSL.Adequacy

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Language.Notation PrimStep

/-! ## The window -/

section window
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The address window `[lo, hi)`, as a filter on byte histories. -/
def winIn (lo hi : Nat) : PAddr → Hist → Bool := fun a _ => decide (lo ≤ a.toNat ∧ a.toNat < hi)

/-- The histories of `m` in `[lo, hi)`. -/
def winMem (m : MemF Hist) (lo hi : Nat) : MemF Hist := PartialMap.filter (winIn lo hi) m

/-- The window of `m`, PERSISTED, in the heap `G`. -/
def winRoAt (G : genHeapGS PAddr Hist GF MemF) (m : MemF Hist) (lo hi : Nat) : IProp GF := iprop%
  [∗map] a ↦ H ∈ winMem m lo hi, pointsTo (G := G) a DFrac.discard H

instance winRoAt_persistent (G : genHeapGS PAddr Hist GF MemF) (m : MemF Hist) (lo hi : Nat) :
    Persistent (winRoAt G m lo hi) := by
  unfold winRoAt; infer_instance

instance winRoAt_timeless (G : genHeapGS PAddr Hist GF MemF) (m : MemF Hist) (lo hi : Nat) :
    Timeless (winRoAt G m lo hi) := by
  unfold winRoAt
  exact BigSepM.bigSepM_timeless (fun _ => by unfold pointsTo; infer_instance)

end window

section fixed
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- Every byte history of `m` OUTSIDE `[lo, hi)`, fully owned, in era `E`'s
heap (`memCells` less the window). -/
def memCellsOut (E : EraGS) (m : MemF Hist) (lo hi : Nat) : IProp GF := iprop%
  [∗map] a ↦ H ∈ m, if winIn lo hi a H then iprop(emp) else pointsTo (G := E.mem) a (DFrac.own 1) H

/-- **Persist the window**: the era's memory cells are the window, persisted,
and the cells outside it. -/
theorem memCells_win (E : EraGS) (m : MemF Hist) (lo hi : Nat) :
    memCells (GF := GF) E m ⊢ |==> (winRoAt E.mem m lo hi ∗ memCellsOut E m lo hi) := by
  have h1 : memCells (GF := GF) E m ⊢ [∗map] a ↦ H ∈ m,
      iprop((if winIn lo hi a H then pointsTo (G := E.mem) a (DFrac.own 1) H else iprop(emp)) ∗
        (if winIn lo hi a H then iprop(emp) else pointsTo (G := E.mem) a (DFrac.own 1) H)) := by
    unfold memCells
    apply BigSepM.bigSepM_mono_of_forall
    intro a H
    cases hw : winIn lo hi a H
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact emp_sep.2
    · simp only [↓reduceIte]
      exact sep_emp.2
  refine h1.trans ?_
  rw [BigSepM.bigSepM_sep_eq, ← BigSepM.bigSepM_filter_cond]
  unfold winRoAt memCellsOut winMem
  iintro ⟨Hw, Ho⟩
  ihave Hw := ((BigSepM.bigSepM_mono_of_forall (fun {a H} => (show
      pointsTo (G := E.mem) a (DFrac.own 1) H ⊢@{IProp GF} |==> pointsTo (G := E.mem) a DFrac.discard H from by
        letI : genHeapGS PAddr Hist GF MemF := E.mem
        iintro Hp
        imod (pointsTo_persist (l := a) (dq := DFrac.own 1) (v := H)) $$ Hp with #Hp
        imodintro
        iexact Hp))).trans (BigSepM.bigSepM_bupd _)) $$ Hw
  imod Hw with Hw
  imodintro
  iframe Hw Ho


/-- **What a `PowerOn` hands the boot client, the window persisted**:
`powerBootRes` with its memory row `memCells E σ.mem` split as the window
`[lo, hi)`, PERSISTED (`winRoAt`; the power thread recorded it in the trace
slot), and the cells outside it, fully owned.  Every other row verbatim. -/
def powerBootResT [KernelMap] [KernelRsv] (lo hi : Nat) (Mof : (Nat → BitVec 8) → LogMirror)
    (Rb : Nat → (Nat → BitVec 8) → IProp GF) (Tn : Nat → IProp GF) (E : EraGS) (gen : Nat)
    (σ : MState) : IProp GF := iprop%
  -- THE RESERVED REGIONS (W8-β′, `powerBootRes`'s rows): which list was reserved...
  ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static ∧
    (MachFixedGS.kptOk (hlc := hlc) (GF := GF) = KernelRsv.kptOk ∧
      MachFixedGS.relPcs (hlc := hlc) (GF := GF) = KernelRsv.relPcs)⌝ ∗
  (∃ r : BitVec 44, E.kptRootName ↪VAR r) ∗
  genCertAt gen E ∗
  ([∗list] cpu ∈ cpus, regCellsNoPins (E.regName cpu) (σ.regs cpu)) ∗
  -- ...the window, the cells of every other unreserved byte, the client's
  -- halves of the reserved ones
  (winRoAt E.mem σ.mem lo hi ∗ memCellsOut E (rsvErase KernelRsv.static σ.mem) lo hi) ∗
  rsvHalvesC E KernelRsv.static σ.mem ∗
  ([∗list] cpu ∈ cpus, ∃ ξ : CtxId, ctxTokAt E cpu ξ) ∗
  ([∗list] cpu ∈ cpus, lockSetAt E cpu []) ∗
  (E.kmapName ↪●MAP KernelMap.static) ∗ kmapStaticAt E ∗
  wireInvAt E ∗
  ([∗list] d ∈ DevId.all, devFragAt E d (σ.devs.st d)) ∗
  MachFixedGS.consRes (hlc := hlc) (GF := GF) (gen + 1) [] ⟨[], [], [], none⟩ ∗
  Tn (gen + 1) ∗
  -- THE ERA'S ORIGIN TICKET (NI M2-W2d): the power-on's third yield, the
  -- record's `uClaimO` (initproc's one-shot origin claim), on to `<init>`'s park
  MachFixedGS.uClaimO (hlc := hlc) (GF := GF) ∗
  -- THE ERA'S REGISTRATION TICKET (NI M2-X1, finding F1): the record's
  -- `uEraTok` at the era's number, which the era's boot shoots at its names
  MachFixedGS.uEraTok (hlc := hlc) (GF := GF) (gen + 1) ∗
  (E.mirrorName ↪VAR{.own (1 : Qp).half} (Mof (diskOf σ.devs))) ∗
  swapLb (gen + 1) ∗ Rb gen (diskOf σ.devs) ∗ crashInv

/-- **THE POWER THREAD, RECORDING THE WINDOW** (`wp_power`'s twin; the file
header).  `Hobs`'s power-on arm leaves the client's trace predicate at
`Pon h` with the trace invariant open; after the fresh era is registered and
its window `[lo, hi)` persisted, `HtextRec` restores the predicate from
them and the invariant closes; the boot client gets `powerBootResT`.  Every
other hook and step is `wp_power`'s. -/
theorem wp_powerT [KernelMap] [KernelRsv] (lo hi : Nat)
    (hrsv : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (hkpt : (MachFixedGS.kptOk (hlc := hlc) (GF := GF) = KernelRsv.kptOk ∧
      MachFixedGS.relPcs (hlc := hlc) (GF := GF) = KernelRsv.relPcs))
    (hwin : ∀ a ∈ rsvBytes KernelRsv.static, ¬ (lo ≤ a.toNat ∧ a.toNat < hi))
    (Ppure : (Nat → BitVec 8) → Prop)
    (Hproj : ∀ dk : Nat → BitVec 8,
      diskFixedAuth dk ∗ ▷ MachFixedGS.crashPred (hlc := hlc) (GF := GF) ⊢@{IProp GF}
        ◇ (diskFixedAuth dk ∗ ▷ MachFixedGS.crashPred (hlc := hlc) (GF := GF) ∗ ⌜Ppure dk⌝))
    (Mof : (Nat → BitVec 8) → LogMirror)
    (Rb : Nat → (Nat → BitVec 8) → IProp GF)
    -- THE ERA'S TURN IN THREE STAGES (Rocq sync SY3-A1): `Tn` is what `Hobs`'s
    -- on-arm yields; `Hswap` is LENT it and hands on `Tn'`; the RETURN PATH
    -- `Hback` (the trace slot once more, at the same history) makes `Tn''` of
    -- it, which `powerBootRes` carries to the boot
    (Tn Tn' Tn'' : Nat → IProp GF)
    (Hswap : ∀ (E : EraGS) (gen : Nat) (dk : Nat → BitVec 8),
      eraRegistered gen E ∗ genStarted gen ∗ startAuth (gen + 1) ∗ diskFixedAuth dk ∗
        (E.mirrorName ↪VAR (Mof dk)) ∗ ▷ MachFixedGS.crashPred (hlc := hlc) (GF := GF) ∗
        Tn (gen + 1)
      ⊢@{IProp GF} |==> ◇ (startAuth (gen + 1) ∗ diskFixedAuth dk ∗
        ▷ MachFixedGS.crashPred (hlc := hlc) (GF := GF) ∗
        (E.mirrorName ↪VAR{.own (1 : Qp).half} (Mof dk)) ∗ swapLb (gen + 1) ∗ Rb gen dk ∗
        Tn' (gen + 1)))
    -- THE TRACE STEP: at a power-on the client's predicate is left at its
    -- pending content `Pon h` (the invariant stays open), at a power loss it
    -- is restored
    (Pon : List Obs → IProp GF)
    (Hobs : ∀ (h : List Obs) (on : Bool) (dk : Nat → BitVec 8), traceShape h on →
      diskFixedAuth dk ∗ ▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf h ⊢@{IProp GF}
        |==> ◇ (diskFixedAuth dk ∗
          (if on then iprop(▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF)) else iprop(▷ Pon h)) ∗
          obsHalf (h ++ [powerEv on]) ∗ powerYield Tn on h))
    -- THE TEXT RECORD: the fresh era, registered at the generation it runs,
    -- and its persisted window `[lo, hi)` restore the predicate
    (HtextRec : ∀ (h : List Obs) (E : EraGS),
      ▷ Pon h ∗ obsHalf (h ++ [Obs.powerOn]) ∗ eraRegistered (obsBoots h) E ∗
          winRoAt E.mem (imgFlat bootImage) lo hi ⊢@{IProp GF}
        |==> ◇ (▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf (h ++ [Obs.powerOn])))
    (Hback : ∀ h : List Obs,
      ▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf (h ++ [Obs.powerOn]) ∗
          Tn' (obsBoots h + 1) ⊢@{IProp GF}
        |==> ◇ (▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf (h ++ [Obs.powerOn]) ∗
          Tn'' (obsBoots h + 1)))
    -- THE USER-EVENT HOOKS (NI M2-W1, split by M2-W2a): the client's trace
    -- predicate accepts a hart's user exit, and a user entry given its
    -- justification (`MachFixedGS.uFit`) and that the cited receipt's
    -- position holds the cited exit; the permit built from them is sealed
    -- into the wire invariant at every power-on (`hartObsPermit_of_hook`)
    -- (NI M2-W2d: the exit hook MINTS the exit's one-shot claims at its
    -- position `h.length`; the entry hook is handed the claim it spends;
    -- NI M2-X1: and the entry's evidence `uEvid ox e`)
    (HuserExit : ∀ (h : List Obs) (e : Obs), isUExit e = true →
      ▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf h ⊢@{IProp GF}
        |==> ◇ (▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf (h ++ [e]) ∗
          MachFixedGS.uClaimR (hlc := hlc) (GF := GF) h.length ∗
          MachFixedGS.uClaimX (hlc := hlc) (GF := GF) h.length e))
    (HuserEnter : ∀ (h : List Obs) (e : Obs) (ox : Option (Nat × Obs)), isUEnter e = true →
      MachFixedGS.uFit (hlc := hlc) (GF := GF) ox e →
      (∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) →
      uClaimFor (hlc := hlc) (GF := GF) ox ∗ MachFixedGS.uEvid (hlc := hlc) (GF := GF) ox e ∗
      ▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf h ⊢@{IProp GF}
        |==> ◇ (▷ MachFixedGS.obsPred (hlc := hlc) (GF := GF) ∗ obsHalf (h ++ [e])))
    (Hboot : ∀ (E : EraGS) (gen : Nat) (σ : MState),
      bootFacts σ →
      (∃ ds0 : DevStates, σ.devs = ds0.reset) →
      Ppure (diskOf σ.devs) →
      obsInv ∗ powerBootResT lo hi Mof Rb Tn'' E gen σ ⊢@{IProp GF} |={⊤}=>
        ([∗list] cpu ∈ cpus, hartWP gen cpu (pure ())) ∗
        ([∗list] d ∈ DevId.all, devWP gen d rootTask (pure ()))) :
    crashInv ∗ obsInv ⊢@{IProp GF} WP Expr.power @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  unfold obsInv crashInv
  iintro ⟨#Hcinv, #Hoinv⟩
  iloeb as IH
  iapply wp_lift_step rfl
  iintro %g %ns %obs %obs' %nt Hσ
  rw [stateInterp_eq]
  icases Hσ with ⟨Hσ, Hobsi⟩
  unfold powerInterp
  icases Hσ with ⟨Hgen, Hstart, ⟨%R, HR, %Hok, Hcur⟩, Hdisk⟩
  unfold diskFixedInterp
  -- THE TRACE STEP, FIRST: a power event is observed, and the client's trace
  -- predicate authorises it.  Run at ⊤, before the step's mask shrink.
  unfold obsInterp
  icases Hobsi with ⟨%h, %htot, %hwf, Ha⟩
  unfold obsAuth
  icases Ha with ⟨Hhalf, Hhist⟩
  imod (inv_acc (E := ⊤) (N := obsN) (P := MachFixedGS.obsPred (hlc := hlc) (GF := GF))
    CoPset.subseteq_top) $$ Hoinv with ⟨HP, Hoclose⟩
  imod Hobs h g.pow (diskOf g.m.devs) hwf.1 $$ [Hdisk HP Hhalf] with >⟨Hdisk, HP, Hhalf, Hyield⟩
  · iframe Hdisk HP Hhalf
  imod obsHistAuth_step h (h ++ [powerEv g.pow]) (List.prefix_append _ _) $$ Hhist with Hhist
  have hbt := hwf.2.1
  cases hpow : g.pow
  · -- powered off: `PowerOn` -- THE TRACE INVARIANT STAYS OPEN until the
    -- fresh era's window is recorded
    unfold powerEv powerYield
    simp only [Bool.false_eq_true, ↓reduceIte]
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    -- THE ERA THE YIELD IS AT, MATCHED TO THE ERA THE BOOT MINTS: the machine
    -- is powered OFF here, so `obsWf`'s boot count reads `obsBoots h = gen`
    have hbt' : obsBoots h = g.gen := by rw [hpow] at hbt; simpa using hbt
    rw [hbt']
    rw [eraCur_false hpow]
    have hcount : startCount g = g.gen := by simp [startCount, hpow]
    rw [hcount] at Hok
    rw [hcount]
    isplit
    · ipureintro
      exact ⟨[.powerOn], .power, bootWitness g, powerFork g.gen,
        primStep_power_on hpow (bootShape_bootWitness g)⟩
    inext
    iintro %e₂ %g₂ %eₜ %Hstep _
    obtain ⟨rfl, h⟩ := primStep_power_inv Hstep
    rcases h with ⟨hp, _, _, _⟩ | ⟨_, rfl, rfl, hgen, hpow', hbf, hdevs⟩
    · rw [hpow] at hp
      exact absurd hp (by decide)
    imod Hclose
    -- the new era's ghosts
    have hbf' := hbf
    obtain ⟨hmem0, hlog0, hhart0, _⟩ := hbf'
    imod (regs_alloc g₂.m.regs) with ⟨%names, Hri, Hrc⟩
    imod (genHeap_init_names (L := PAddr) (V := Hist) (H := MemF) g₂.m.mem) with ⟨%γh, %γm, Hheap, Hpts, _⟩
    imod (names_alloc (fun γ _ => iprop(MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0) ∗
      MonoNat.lb_own γ (.ofNat 0))) (fun _ => mono0_alloc)) with ⟨%vn, Hv⟩
    imod (names_alloc (fun γ _ => MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0)) (fun _ => mono0_alloc'))
      with ⟨%ivn, Hiv⟩
    imod (names_alloc (fun γ _ => MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0)) (fun _ => mono0_alloc'))
      with ⟨%rvn, Hrv⟩
    imod (MonoNat.own_alloc (.ofNat 0)) with ⟨%γtop, Htop, _⟩
    imod (ghost_map_alloc_empty (K := Nat) (V := Agent) (H := RegMapF)) with ⟨%γauth, Hauth⟩
    imod (ghost_map_alloc (resvMap g₂.m)) with ⟨%γresv, Hresv, Hfrags⟩
    imod (names_alloc (fun γ _ => γ ↪●MAP (∅ : StrMapF Unit))
      (fun _ => ghost_map_alloc_empty (K := String) (V := Unit) (H := StrMapF))) with ⟨%lsn, Hls⟩
    imod (ghost_map_alloc (K := Nat) (V := BitVec 64) (H := RegMapF) KernelMap.static) with ⟨%γkmap, Hkmap, Hkfrags⟩
    imod (ghost_var_alloc (A := BitVec 44) 0#44) with ⟨%γkroot, Hkroot⟩
    imod (devs_alloc g₂.m.devs) with ⟨%dn, Hda, Hdf⟩
    -- the era's durable-disk mirror, BORN TRUE at the client's picture of the
    -- disk this era boots on (a device reset keeps the image)
    have hdk : diskOf g₂.m.devs = diskOf g.m.devs := by rw [hdevs]; rfl
    imod (ghost_var_alloc (A := LogMirror) (Mof (diskOf g.m.devs))) with ⟨%γmir, Hmir⟩
    -- THE RESERVED REGIONS (W8-β′): the registry over the static list
    imod (ghost_map_alloc (K := Nat) (V := Agent) (H := RegMapF)
      (rsvRegMap (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)))) with ⟨%γrsv, HrG, -⟩
    -- THE CHAIN CERTIFICATES (W8 (f2-ctx)): none issued yet
    imod (ghost_map_alloc_empty (K := Nat) (V := Agent) (H := RegMapF)) with ⟨%γch, HcG⟩
    have hrwf := MachFixedGS.rsvStatic_wf (hlc := hlc) (GF := GF)
    imod (kmapStatic_persist ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩) $$ Hkfrags with Hkst
    icases BigSepL.bigSepL_sep_eqv.1 $$ Hv with ⟨Hva, Hvlb⟩
    imod (ctxs_boot ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩) $$ Hvlb with Hctx
    imod registry_insert R g.gen ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ (registryOk_none Hok)
      $$ HR with ⟨HR, #Hreg⟩
    -- THE WINDOW, PERSISTED, AND RECORDED: the trace slot is restored and
    -- the trace invariant closed
    ihave Hpts : memCells (GF := GF) ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩
      g₂.m.mem $$ [Hpts]
    · unfold memCells; iexact Hpts
    imod (memCells_win ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩
      g₂.m.mem lo hi) $$ Hpts with ⟨#Hwin, Hpts⟩
    -- ...and every reserved byte's cell, outside the window, split in two halves
    have hin : ∀ a ∈ rsvBytes (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)), (get? (M := MemF) g₂.m.mem a).isSome := by
      intro a ha
      rw [hmem0]
      exact rsvWf_img hrwf ha
    ihave Hpts := (show memCellsOut (GF := GF) ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap,
        γkroot, dn, γmir, γrsv, γch⟩ g₂.m.mem lo hi ⊢
      memCellsOut ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩
          (rsvErase (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) g₂.m.mem) lo hi ∗
        rsvHalvesAt ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩
          (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) ∗
        rsvHalvesC ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩
          (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) g₂.m.mem from by
        unfold memCellsOut
        refine memCellsRaw_rsv_split _ _ g₂.m.mem _ hrwf.1 hin (fun a ha => ?_)
        have hw : winIn lo hi a ((get? (M := MemF) g₂.m.mem a).getD []) = false := by
          unfold winIn
          simp only [decide_eq_false_iff_not]
          exact hwin a (hrsv ▸ ha)
        rw [hw]
        exact .rfl) $$ Hpts
    icases Hpts with ⟨Hpts, HrH, HrC⟩
    ihave #Hwin' := (show winRoAt (GF := GF) (EraGS.mem ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn,
        γkmap, γkroot, dn, γmir, γrsv, γch⟩) g₂.m.mem lo hi ⊢
      winRoAt (EraGS.mem ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩)
        (imgFlat bootImage) lo hi from by rw [hmem0]; try exact .rfl) $$ Hwin
    have hrec := HtextRec h ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩
    rw [hbt'] at hrec
    imod hrec $$ [HP Hhalf] with >⟨HP, Hhalf⟩
    · iframe Hhalf Hreg Hwin'
      inext
      iexact HP
    imod Hoclose $$ HP
    imod startAuth_bump _ $$ Hstart with ⟨Hstart, #Hstarted⟩
    ihave #Hborn := genAuth_get_born _ $$ Hgen
    -- THE CRASH HOOKS, with the crash invariant open and the durable
    -- authority in hand: the projection, then the custody swap
    imod (inv_acc (E := ⊤) (N := crashN) (P := MachFixedGS.crashPred (hlc := hlc) (GF := GF))
      CoPset.subseteq_top) $$ Hcinv with ⟨HPc, Hcclose⟩
    imod (Hproj (diskOf g.m.devs)) $$ [Hdisk HPc] with ⟨Hdisk, HPc, %hpure⟩
    · iframe Hdisk HPc
    icases Hyield with ⟨Hyield, Hturn, Huo, Huet⟩
    -- THE SWAP, LENT THE ERA'S TURN (Rocq sync SY3-A1)
    imod (Hswap ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ g.gen
      (diskOf g.m.devs)) $$ [Hreg Hstarted Hstart Hdisk Hmir HPc Hturn]
      with >⟨Hstart, Hdisk, HPc, Hmir, #Hswlb, HRb, Hturn⟩
    · iframe Hstart Hdisk Hmir HPc Hturn
      unfold genStarted
      isplit
      · iexact Hreg
      · iexact Hstarted
    imod Hcclose $$ HPc
    -- THE RETURN PATH (Rocq sync SY3-A1 re-cut): the trace slot once more, at
    -- the history the on-arm left, turning the swap's yield into the boot's
    imod (inv_acc (E := ⊤) (N := obsN) (P := MachFixedGS.obsPred (hlc := hlc) (GF := GF))
      CoPset.subseteq_top) $$ Hoinv with ⟨HP2, Hoclose2⟩
    have hback := Hback h
    rw [hbt'] at hback
    imod hback $$ [HP2 Hhalf Hturn] with >⟨HP2, Hhalf, Hturn⟩
    · iframe HP2 Hhalf Hturn
    imod Hoclose2 $$ HP2
    -- the reservation fragments, one per hart
    ihave Hfrags' := bigSepM_cpus (fun k v => γresv ↪◯MAP[k] v)
      (fun c => (g₂.m.resv c, (g₂.m.hr c).acq)) cpus (resvMap g₂.m) (List.nodup_finRange NCPU)
      (fun c _ => resvMap_get? g₂.m c) $$ Hfrags
    have hfrag : ∀ c : CPU, (γresv ↪◯MAP[c.val] ((g₂.m.resv c, (g₂.m.hr c).acq) : ResvVal)) ⊢@{IProp GF}
        resvFragAt ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ c none false := by
      intro c
      unfold resvFragAt
      rw [(hhart0 c).2.2.2, (hhart0 c).2.2.1]
      show (γresv ↪◯MAP[c.val] ((none, false) : ResvVal)) ⊢ γresv ↪◯MAP[c.val] ((none, false) : ResvVal)
      iintro H
      iexact H
    -- the boot client
    ihave Hdf := (show ([∗list] d ∈ DevId.all, devFragN (GF := GF) dn d (g₂.m.devs.st d)) ⊢
        [∗list] d ∈ DevId.all, devFragAt ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ d (g₂.m.devs.st d)
        from by unfold devFragAt devFragN; iintro H; iexact H) $$ Hdf
    ihave Hda := (show ([∗list] d ∈ DevId.all, devAuthN (GF := GF) dn d (g₂.m.devs.st d)) ⊢
        [∗list] d ∈ DevId.all, devAuthAt ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ d (g₂.m.devs.st d)
        from by unfold devAuthAt devAuthN; iintro H; iexact H) $$ Hda
    -- the two interrupt pins of every hart leave the client's frame: they are
    -- sealed into the wire invariant, which the PLIC's wire step drives
    ihave Hrc := BigSepL.bigSepL_mono
      (fun {_ c} _ => regCells_split_pins (names c) (g₂.m.regs c)) $$ Hrc
    icases BigSepL.bigSepL_sep_eqv.1 $$ Hrc with ⟨Hpins, Hrc⟩
    -- ...beside the user-boundary permit (NI M2-W1), out of the trace
    -- invariant and the client's user-event hook
    ihave #Hhp : hartObsPermit (hlc := hlc) (GF := GF) $$ [Hoinv]
    · iapply hartObsPermit_of_hook HuserExit HuserEnter
      unfold obsInv
      iexact Hoinv
    imod (wireInvAt_alloc ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ ⊤
      (fun c => g₂.m.regs c Register.sig_seip) (fun c => g₂.m.regs c Register.sig_meip))
      $$ [Hhp Hpins] with #Hwire
    · iframe Hhp Hpins
    ihave Hres : powerBootResT lo hi Mof Rb Tn'' ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ g.gen g₂.m $$ [Hrc Hpts HrC Hctx Hfrags' Hls Hkmap Hkst Hkroot Hdf Hyield Hturn Huo Huet Hmir HRb]
    · unfold powerBootResT genCertAt kmapStaticAt crashInv
      rw [hdk, ← hrsv]
      isplitr
      · ipureintro; exact ⟨rfl, hkpt⟩
      iframe Hmir HRb Hswlb Hcinv HrC
      isplitl [Hkroot]
      · iexists 0#44
        iexact Hkroot
      iframe Hrc Hwin Hpts Hkmap Hkst Hwire Hdf Hyield Hturn Huo Huet
      isplitr [Hctx Hfrags' Hls]
      · isplit
        · iexact Hborn
        isplit
        · iexact Hstarted
        · iexact Hreg
      · isplitl [Hctx Hfrags']
        · iapply BigSepL.bigSepL_mono (fun {_ c} _ => ctxTok_boot_elem _ c)
          iapply BigSepL.bigSepL_sep_eqv.2
          iframe Hctx
          iapply BigSepL.bigSepL_mono (fun {_ c} _ => hfrag c) $$ Hfrags'
        · unfold lockSetAt locksMap
          iexact Hls
    imod (Hboot ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ g.gen g₂.m hbf
      ⟨g.m.devs, hdevs⟩ (by rw [hdk]; exact hpure)) $$ [Hres] with ⟨Hwps, Hdwps⟩
    · isplitl []
      · unfold obsInv; iexact Hoinv
      · iexact Hres
    imodintro
    -- the trace conjunct, at the extended history
    ihave Hobsi := obsInterp_close _ _ _ _ _ _ h obs' Hstep hwf htot $$ [Hhalf Hhist]
    · unfold obsAuth; iframe Hhalf Hhist
    -- the state interpretation at the booted state
    rw [stateInterp_eq]
    unfold powerInterp
    iframe Hobsi
    rw [hgen, show startCount g₂ = g.gen + 1 by simp [startCount, hgen, hpow']]
    iframe Hgen Hstart
    unfold diskFixedInterp
    rw [hdk]
    iframe Hdisk
    isplitl [HR Hheap Hri Hva Hiv Hrv Htop Hauth Hresv Hda HrG HrH HcG]
    · iexists (insert R g.gen ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩)
      iframe HR
      isplit
      · ipureintro
        exact registryOk_insert Hok _
      rw [eraCur_true hpow', hgen]
      iexists ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩
      isplit
      · ipureintro
        exact get?_insert_eq rfl
      ihave Huep : iprop(uepModelAt (GF := GF) ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ g₂.m) $$ []
      · iapply uepModelAt_boot
        exact fun c => (bootFacts_resetRegsRun hbf c).1 Register.cur_privilege Privilege.Machine rfl
      unfold eraInterp memModelAt devInterpAt
      iframe Hheap Hri Hresv Hda Huep
      rw [show g₂.m.top = 0 by simp [MState.top, hlog0], hlog0, authMap_nil]
      iframe Htop Hauth
      isplitl [Hva Hiv Hrv]
      · rw [BigSepL.bigSepL_eq (Φ := fun _ c => hartViewsAt ⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir, γrsv, γch⟩ g₂.m c)
          (Ψ := fun _ c => iprop(MonoNat.auth_own (vn c) (DFrac.own 1) (.ofNat 0) ∗
            MonoNat.auth_own (ivn c) (DFrac.own 1) (.ofNat 0) ∗
            MonoNat.auth_own (rvn c) (DFrac.own 1) (.ofNat 0)))
          (fun {_ c} _ => by
            unfold hartViewsAt
            obtain ⟨h1, h2, h3, _⟩ := hhart0 c
            simp only [h1, h2, h3]
            rfl)]
        iapply BigSepL.bigSepL_sep_eqv.2
        iframe Hva
        iapply BigSepL.bigSepL_sep_eqv.2
        iframe Hiv Hrv
      · isplit
        · ipureintro
          exact mmOk_boot g₂.m hbf
        · unfold rsvModelAt chainModelAt
          iframe HrH
          isplitl [HrG]
          · iexists (rsvRegMap (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)))
            iframe HrG
            isplit
            · ipureintro
              refine ⟨rsvRegMap_staticIn hrwf.2.2, rsvRegMap_exact _, reservedOk_of_all (rsvRegMap_exact _) ?_,
                relPcOk_img g₂.m bootImage hmem0⟩
              rw [hmem0]
              exact rsvAllOk_boot hrwf
            · unfold kptModelAt
              iexists 0, [], []
              isplit
              · ipureintro
                exact ⟨rsvRegMap_kptLinked _, by rw [hmem0]; exact dmaOkAt_img _ _ _ _, Or.inl ⟨rfl, by rw [hmem0]; exact pubClean_boot hrwf, rfl,
                  rsvRegMap_ksPre _⟩⟩
              · isplit
                · exact BigSepL.bigSepL_nil_intro
                isplit
                · exact BigSepL.bigSepL_nil_intro
                · iapply ksRcptsAll_none
                  intro q hq
                  have := rsvRegMap_ksPre _ _ _ hq
                  unfold ksKey at this
                  omega
          · isplit
            · ipureintro
              exact loadsChained_zero _ _ (fun j a => by
                show (g₂.m.hr j).coh a = 0
                rw [(hhart0 j).2.2.1]; rfl)
            iexists ∅
            iframe HcG
            isplit
            · ipureintro
              exact ⟨certsOk_empty _, pcKeysOk_empty _⟩
            · unfold chainElemsAt
              imodintro
              iintro %k %v %hk
              simp [LawfulPartialMap.get?_empty] at hk
    isplitr [Hwps Hdwps]
    · iexact IH
    · unfold powerFork
      iapply BigSepL.bigSepL_append.2
      isplitl [Hwps]
      · rw [BigSepL.bigSepL_map, BigSepL.bigSepL_eq (fun _ => (hartWP_loop g.gen _).symm)]
        iexact Hwps
      · rw [BigSepL.bigSepL_map, BigSepL.bigSepL_eq (fun _ => (devWP_loop g.gen _).symm)]
        iexact Hdwps
  · -- powered on: `PowerOff`: the predicate is back, the invariant closes
    unfold powerEv powerYield
    simp only [↓reduceIte]
    imod Hoclose $$ HP
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    rw [eraCur_true hpow]
    have hcount : startCount g = g.gen + 1 := by simp [startCount, hpow]
    rw [hcount] at Hok
    isplit
    · ipureintro
      exact ⟨[.powerOff], .power, _, [], primStep_power_off hpow⟩
    inext
    iintro %e₂ %g₂ %eₜ %Hstep _
    obtain ⟨rfl, h⟩ := primStep_power_inv Hstep
    rcases h with ⟨_, rfl, rfl, rfl⟩ | ⟨hp, _, _, _⟩
    · imod Hclose
      imod genAuth_bump _ $$ Hgen with Hgen
      imodintro
      ihave Hobsi := obsInterp_close _ _ _ _ _ _ h obs' Hstep hwf htot $$ [Hhalf Hhist]
      · unfold obsAuth; iframe Hhalf Hhist
      rw [stateInterp_eq]
      unfold powerInterp
      iframe Hobsi
      rw [show startCount { g with gen := g.gen + 1, pow := false } = g.gen + 1 by
        simp [startCount], hcount]
      iframe Hgen Hstart
      unfold diskFixedInterp
      iframe Hdisk
      isplitl [HR]
      · iexists R
        iframe HR
        isplit
        · ipureintro
          exact Hok
        rw [eraCur_false (g := { g with gen := g.gen + 1, pow := false }) rfl]
        ipureintro
        trivial
      isplit
      · iexact IH
      · exact BigSepL.bigSepL_nil_intro
    · rw [hpow] at hp
      exact absurd hp (by decide)

end fixed

section pre
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The window, persisted, in era `E`'s heap at the pre-structure's functors
(`winRoAt E.mem` at the record literal `bootFixedGS`). -/
def winRoPre [MachGpreS hlc GF] (E : EraGS) (m : MemF Hist) (lo hi : Nat) : IProp GF :=
  winRoAt (⟨E.heapName, E.metaName⟩ : genHeapGS PAddr Hist GF MemF) m lo hi

instance winRoPre_persistent [MachGpreS hlc GF] (E : EraGS) (m : MemF Hist) (lo hi : Nat) :
    Persistent (winRoPre (hlc := hlc) (GF := GF) E m lo hi) := by
  unfold winRoPre; infer_instance

instance winRoPre_timeless [MachGpreS hlc GF] (E : EraGS) (m : MemF Hist) (lo hi : Nat) :
    Timeless (winRoPre (hlc := hlc) (GF := GF) E m lo hi) := by
  unfold winRoPre; infer_instance

/-- **THE POWER ADEQUACY, RECORDING THE WINDOW** (`riscvPowerAdequacy`'s
twin, over `wp_powerT`; the file header).  The trace slot `Pt`/`Pon` is
also at the registry's gname `γreg`; `Hobs` leaves `Pon` at a power-on,
`HtextRec` restores `Pt` from the era's registry element and its persisted
window; `Hboot` is handed `powerBootResT`.  Every other parameter is
`riscvPowerAdequacy`'s. -/
theorem riscvPowerAdequacyT [MachGpreS hlc GF] [KernelMap] [KernelRsv] (lo hi : Nat)
    (hwin : ∀ a ∈ rsvBytes KernelRsv.static, ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) (ndisk : Nat) (g : GState)
    -- THE BIRTH, its yield split between the two slots (Rocq sync SY3-A1):
    -- `Cls c` to the crash slot's birth (`HPc`), `Clt c` to the trace slot's
    -- (`HPt`); handed the machine's four fixed gnames, `Born` what it says of
    -- where it kept them (told to every boot, `Hboot`, and to the swap)
    (CT : Type) (Cls Clt : CT → IProp GF)
    (Born : GName → GName → GName → GName → CT → Prop)
    (Hbirth : ∀ γdisk γsw γreg γst : GName,
      ⊢@{IProp GF} |==> ∃ c : CT, ⌜Born γdisk γsw γreg γst c⌝ ∗ Cls c ∗ Clt c)
    (Pc : GName → GName → GName → GName → CT → IProp GF)
    (HPc : ∀ (γdisk γsw γreg γst : GName) (c : CT),
      Cls c ∗ diskImgBytes γdisk 0 (Virtio.diskRead (diskOf g.m.devs) 0 ndisk) ∗
        MonoNat.auth_own γsw (DFrac.own 1) (.ofNat 0) ⊢@{IProp GF} |==> Pc γdisk γsw γreg γst c)
    -- THE TWO SYNC SLOTS, at the fixed part alone (Rocq SY3-A1 re-cut: the
    -- birth is handed the gnames, so the fixed part can name them)
    (Tk : CT → Nat → IProp GF)
    (Hk : CT → Nat → IProp GF → IProp GF)
    (Ppure : (Nat → BitVec 8) → Prop)
    (Hproj : ∀ (γdisk γsw γreg γst : GName) (c : CT) (dk : Nat → BitVec 8),
      diskImgAuthSized γdisk ndisk dk ∗ ▷ Pc γdisk γsw γreg γst c ⊢@{IProp GF}
        ◇ (diskImgAuthSized γdisk ndisk dk ∗ ▷ Pc γdisk γsw γreg γst c ∗ ⌜Ppure dk⌝))
    (Mof : (Nat → BitVec 8) → LogMirror)
    (Rb : CT → Nat → (Nat → BitVec 8) → IProp GF)
    -- THE ERA'S TURN (Rocq SY3-A1): `Tn` as `Hobs` yields it, `Tn'` as the
    -- swap hands it on, `Tn''` as the return path `Hback` makes of that
    (Tn Tn' Tn'' : CT → Nat → IProp GF)
    -- ...the swap at a fixed part born at these names, LENT the turn
    (Hswap : ∀ (γdisk γsw γreg γst : GName) (c : CT), Born γdisk γsw γreg γst c →
      ∀ (E : EraGS) (gen : Nat) (dk : Nat → BitVec 8),
      (γreg ↪◯MAP[gen]{.discard} E) ∗ MonoNat.lb_own γst (.ofNat (gen + 1)) ∗
        MonoNat.auth_own γst (DFrac.own 1) (.ofNat (gen + 1)) ∗ diskImgAuthSized γdisk ndisk dk ∗
        (E.mirrorName ↪VAR (Mof dk)) ∗ ▷ Pc γdisk γsw γreg γst c ∗ Tn c (gen + 1) ⊢@{IProp GF}
      |==> ◇ (MonoNat.auth_own γst (DFrac.own 1) (.ofNat (gen + 1)) ∗
        diskImgAuthSized γdisk ndisk dk ∗ ▷ Pc γdisk γsw γreg γst c ∗
        (E.mirrorName ↪VAR{.own (1 : Qp).half} (Mof dk)) ∗
        MonoNat.lb_own γsw (.ofNat (gen + 1)) ∗ Rb c gen dk ∗ Tn' c (gen + 1)))
    -- THE TRACE SLOT, at the registry's name too (the text record names the
    -- era a generation runs), and its power-on content before the record
    (Pt : GName → GName → CT → IProp GF) (Pon : GName → GName → CT → List Obs → IProp GF)
    (Tg : CT → List Obs → IProp GF) (HTg : ∀ c h, Persistent (Tg c h))
    (HTgt : ∀ c h, Timeless (Tg c h))
    (Kc : CT → IProp GF) (HKc : ∀ c, Persistent (Kc c)) (HKct : ∀ c, Timeless (Kc c))
    (Cres : CT → Nat → List Obs → ConsHist → IProp GF)
    (HCrest : ∀ c k h H, Timeless (Cres c k h H))
    (Wd : CT → Nat → IProp GF) (HWd : ∀ c k, Persistent (Wd c k))
    (HWdt : ∀ c k, Timeless (Wd c k))
    (Rw : CT → Nat → IProp GF) (HRw : ∀ c k, Persistent (Rw c k))
    (HRwt : ∀ c k, Timeless (Rw c k))
    -- THE ENTER'S JUSTIFICATION (NI M2-W2a): the record's `uFit`
    (Uf : Option (Nat × Obs) → Obs → Prop)
    -- THE ONE-SHOT FILING CLAIMS (NI M2-W2d): the record's `uClaimR`/`uClaimX`
    -- (what an exit at a position mints), `uClaimO` (the origin ticket a
    -- power-on mints)
    (Ucr : CT → Nat → IProp GF) (Ucx : CT → Nat → Obs → IProp GF) (Uco : CT → IProp GF)
    -- THE ENTRY'S EVIDENCE AND THE ERA'S REGISTRATION (NI M2-X1): the
    -- record's `uEvid` (persistent; handed to the entry hook), `uEraTok` (the
    -- registration ticket a power-on mints) and `uEraAnchor` (persistent)
    (Ue : CT → Option (Nat × Obs) → Obs → IProp GF) (HUe : ∀ c ox e, Persistent (Ue c ox e))
    (Uet : CT → Nat → IProp GF) (Uea : CT → Nat → List GName → IProp GF)
    (HUea : ∀ c k ns, Persistent (Uea c k ns))
    (HPt : ∀ (γreg γobs : GName) (c : CT),
      Clt c ∗ (γobs ↪VAR{.own (1 : Qp).half} ([] : List Obs)) ⊢@{IProp GF} |==> Pt γreg γobs c)
    (Hobs : ∀ (γdisk γreg γobs : GName) (c : CT) (h : List Obs) (on : Bool) (dk : Nat → BitVec 8),
      traceShape h on →
      diskImgAuthSized γdisk ndisk dk ∗ ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
        |==> ◇ (diskImgAuthSized γdisk ndisk dk ∗
          (if on then iprop(▷ Pt γreg γobs c) else iprop(▷ Pon γreg γobs c h)) ∗
          (γobs ↪VAR{.own (1 : Qp).half} (h ++ [powerEv on])) ∗
          (if on then iprop(emp)
           else iprop(Cres c (obsBoots h + 1) [] ⟨[], [], [], none⟩ ∗ Tn c (obsBoots h + 1) ∗
             Uco c ∗ Uet c (obsBoots h + 1)))))
    -- THE TEXT RECORD (weak-allocproc W3): at the power-on, with the trace
    -- invariant still open since `Hobs`, the slot records the new era's
    -- persisted window `[lo, hi)` at the generation it runs
    (HtextRec : ∀ (γreg γobs : GName) (c : CT) (h : List Obs) (E : EraGS),
      ▷ Pon γreg γobs c h ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])) ∗
          (γreg ↪◯MAP[obsBoots h]{.discard} E) ∗ winRoPre E (imgFlat bootImage) lo hi ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn]))))
    -- THE RETURN PATH (Rocq SY3-A1 re-cut): the trace slot's second step at
    -- the power-on, at the history the on-arm left, after the crash slot's swap
    (Hback : ∀ (γreg γobs : GName) (c : CT) (h : List Obs),
      ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])) ∗
          Tn' c (obsBoots h + 1) ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])) ∗
          Tn'' c (obsBoots h + 1)))
    -- THE USER-EVENT HOOKS (NI M2-W1, split by M2-W2a): the trace slot
    -- accepts a hart's user exit, and a user entry given its justification
    -- `Uf ox e` and the cited receipt's pure reading (`wp_power`'s
    -- `HuserExit`/`HuserEnter`, sealed into the wire invariant as the hart's
    -- permit)
    -- (NI M2-W2d: the exit hook mints the exit's claims at `h.length`, the
    -- entry hook is handed the claim the entry spends; NI M2-X1: and the
    -- entry's evidence `Ue c ox e`)
    (HuserExit : ∀ (γreg γobs : GName) (c : CT) (h : List Obs) (e : Obs), isUExit e = true →
      ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [e])) ∗
          Ucr c h.length ∗ Ucx c h.length e))
    (HuserEnter : ∀ (γreg γobs : GName) (c : CT) (h : List Obs) (e : Obs) (ox : Option (Nat × Obs)),
      isUEnter e = true → Uf ox e → (∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) →
      uClaimForRaw (Ucr c) (Uco c) ox ∗ Ue c ox e ∗
      ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [e]))))
    (phi : GState → List Obs → Prop)
    (Hphi : ∀ (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γdisk γswap γobs γhist : GName) (c : CT)
        (T : List Obs) (g' : GState) (h : List Obs),
      @powerInterp hlc GF (bootFixedGS Hinv γgen γstart γreg γdisk ndisk γswap
          (Pc γdisk γswap γreg γstart c)
          (Tk c) (Hk c) γobs T (Pt γreg γobs c) γhist
          (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)
          (Wd c) (HWd c) (HWdt c) (Rw c) (HRw c) (HRwt c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c)) g' ∗
        (γobs ↪VAR{.own (1 : Qp).half} h) ∗ ⌜obsWf h g'⌝ ∗
        ▷ Pc γdisk γswap γreg γstart c ∗ ▷ Pt γreg γobs c ⊢@{IProp GF} ◇ ⌜phi g' h⌝)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false)
    (Hboot : ∀ [F : MachFixedGS hlc GF] (Hinv : InvGS_gen hlc GF)
        (γgen γstart γreg γdisk γswap γobs γhist : GName) (c : CT) (T : List Obs),
      F = bootFixedGS Hinv γgen γstart γreg γdisk ndisk γswap (Pc γdisk γswap γreg γstart c)
          (Tk c) (Hk c)
          γobs T (Pt γreg γobs c) γhist
          (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)
          (Wd c) (HWd c) (HWdt c) (Rw c) (HRw c) (HRwt c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c) →
      Born γdisk γswap γreg γstart c →
      ∀ (E : EraGS) (gen : Nat) (σ : MState), bootFacts σ →
        (∃ ds0 : DevStates, σ.devs = ds0.reset) →
        Ppure (diskOf σ.devs) →
        obsInv ∗ powerBootResT lo hi Mof (Rb c) (Tn'' c) E gen σ ⊢@{IProp GF} |={⊤}=>
          ([∗list] cpu ∈ cpus, hartWP gen cpu (pure ())) ∗
          ([∗list] d ∈ DevId.all, devWP gen d rootTask (pure ())))
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ phi g2 κs := by
  refine powerAdequacyCore (hlc := hlc) (GF := GF) g phi ?_ n κs t2 g2 hsteps
  intro Hinv T
  -- THE DURABLE DISK, FIRST: its full fragments establish the crash predicate
  imod (diskImgSized_alloc (GF := GF) (diskOf g.m.devs) ndisk) with ⟨%γdisk, Hdauth, Hdfr⟩
  imod (MonoNat.own_alloc (GF := GF) (.ofNat g.gen)) with ⟨%γgen, Hgauth, _⟩
  imod (MonoNat.own_alloc (GF := GF) (.ofNat (startCount g))) with ⟨%γstart, Hsauth, _⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := EraGS) (H := RegMapF)) with ⟨%γreg, HRauth⟩
  imod (MonoNat.own_alloc (GF := GF) (.ofNat 0)) with ⟨%γswap, Hswap0, _⟩
  imod (Hbirth γdisk γswap γreg γstart) with ⟨%c, %hborn, Hcls, Hcl⟩
  imod (HPc γdisk γswap γreg γstart c) $$ [Hcls Hdfr Hswap0] with HPc0
  · iframe Hcls Hdfr Hswap0
  imod (inv_alloc crashN ⊤ (Pc γdisk γswap γreg γstart c)) $$ [HPc0] with #Hcinv
  · inext; iexact HPc0
  imod (ghost_var_alloc (GF := GF) ([] : List Obs)) with ⟨%γobs, Hob⟩
  have hsplit := (ghost_var_fractional (GF := GF) γobs ([] : List Obs)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hsplit
  icases hsplit.1 $$ Hob with ⟨HobA, HobF⟩
  imod (MonoList.own_alloc (GF := GF) ([] : List Obs)) with ⟨%γhist, HobH, _⟩
  imod (HPt γreg γobs c) $$ [Hcl HobF] with HPt0
  · iframe Hcl HobF
  imod (inv_alloc obsN ⊤ (Pt γreg γobs c)) $$ [HPt0] with #Hoinv
  · inext; iexact HPt0
  imodintro
  iexists (bootFixedGS Hinv γgen γstart γreg γdisk ndisk γswap (Pc γdisk γswap γreg γstart c)
    (Tk c) (Hk c)
    γobs T (Pt γreg γobs c) γhist
    (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)
          (Wd c) (HWd c) (HWdt c) (Rw c) (HRw c) (HRwt c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c))
  unfold adeqBirth
  isplitr
  · ipureintro; rfl
  isplitl [Hgauth Hsauth HRauth HobA HobH Hdauth]
  · isplitl [Hgauth Hsauth HRauth Hdauth]
    · unfold powerInterp genAuth startAuth eraCur diskFixedInterp diskFixedAuth
      iframe Hgauth Hsauth Hdauth
      iexists ∅
      iframe HRauth
      rw [Hpow]
      isplit
      · ipureintro
        intro k
        simp [LawfulPartialMap.get?_empty, startCount, Hpow, Hgen0]
      · ipureintro; trivial
    · unfold obsInterp obsAuth obsHalf obsHistAuth
      iexists []
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact obsWf_init g Hpow Hgen0
      iframe HobA HobH
  isplitl []
  · iapply (@wp_powerT hlc GF ((bootFixedGS Hinv γgen γstart γreg γdisk ndisk γswap
      (Pc γdisk γswap γreg γstart c)
          (Tk c) (Hk c) γobs T (Pt γreg γobs c) γhist
      (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)
          (Wd c) (HWd c) (HWdt c) (Rw c) (HRw c) (HRwt c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c)).withInv Hinv) _ _ lo hi rfl ⟨rfl, rfl⟩ hwin
      Ppure (fun dk => Hproj γdisk γswap γreg γstart c dk)
      Mof (Rb c) (Tn c) (Tn' c) (Tn'' c) (fun E gen dk => Hswap γdisk γswap γreg γstart c hborn E gen dk)
      (Pon γreg γobs c)
      (fun h on dk hs => Hobs γdisk γreg γobs c h on dk hs)
      (fun h E => HtextRec γreg γobs c h E)
      (fun h => Hback γreg γobs c h)
      (fun h e he => HuserExit γreg γobs c h e he)
      (fun h e ox he hf hv => HuserEnter γreg γobs c h e ox he hf hv)
      (fun E gen σ hbf hdv hpp => @Hboot ((bootFixedGS Hinv γgen γstart γreg γdisk ndisk γswap
        (Pc γdisk γswap γreg γstart c)
          (Tk c) (Hk c) γobs T (Pt γreg γobs c) γhist
        (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)
          (Wd c) (HWd c) (HWdt c) (Rw c) (HRw c) (HRwt c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c)).withInv Hinv)
        Hinv γgen γstart γreg γdisk γswap γobs γhist c T rfl hborn E gen σ hbf hdv hpp))
    unfold obsInv crashInv
    iframe Hcinv Hoinv
  unfold obsHalf
  iintro %g2' %h Hpi Hhalf %hwf
  imod (inv_acc (E := ⊤) (N := crashN) (P := Pc γdisk γswap γreg γstart c) CoPset.subseteq_top)
    $$ Hcinv with ⟨HP, _⟩
  imod (inv_acc (E := ⊤ \ ↑crashN) (N := obsN) (P := Pt γreg γobs c) crashN_obsN)
    $$ Hoinv with ⟨HPt, _⟩
  imod (Hphi Hinv γgen γstart γreg γdisk γswap γobs γhist c T g2' h) $$ [Hpi Hhalf HP HPt] with %hphi
  · iframe Hpi Hhalf HP HPt
    ipureintro; exact hwf
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro; exact hphi

end pre

end MachCSL
