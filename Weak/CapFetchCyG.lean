/-
Weak: **Q1-c [OWN.144] (E2), part 2 — THE FETCH-HEAD CYCLE PREDICATE `cyGB` and its run**
(`PROGRESS-W11F.md` §14).  Lean-only, no Rocq twin.

`cyGB Ag P m st` is r2's `PinFetchPa.cyFB` (`Weak/PinFetchPaCy.lean`) with its fetch obligation
read at the WHOLE tracked state: a RAM instruction-fetch read OWES `Ag st (paZ pa)` (`cyFB` owes
`Aa |st.fe| (paZ pa)`), and no answer filter.  The instance `kAg pc`: the read is one of the
cycle's two (`|fe| < 2`), at its granule's page offset (`≡ pc + 2|fe| (mod 4096)`), and the
mirror is at `PC = pc` in Supervisor mode — what the MachCSL fetch guard ([OWN.144],
`MachCSL.MState.fetchPa_of_reducible`) needs to know of the hart at the read.
* §1 the predicate and its kit; §2 the lifts (W-SCO's `fp`: no fetch read; w1's `pf`: the
  protected mirror kept); §3 the fetch: the product of w1's frame `pfFetch` and the offset walk
  `CapFetchOfs.foFetch`; §4 **`cyGSailOf`** — every cycle `riscvStep tick` from `PC = pc`,
  Supervisor mode, `Rboot`, an empty log satisfies `cyGB (kAg pc)` (`PinFetchPa.cyFSailOf`'s
  walk, with no translation configuration); §5 **`cyGRun`** — along an in-cycle run (`irun`) every
  fetch label's PRE-state is matched by a mirror owing `Ag`, and the hart's head there is that
  fetch read (`fH`).

Spec: FAITHFUL (a theorem about the Sail text and the hart's own steps).  Every helper is
`Weak.CapFetchCyG.*`.
-/
import Weak.CapFetchOfs
import Weak.PinFetchPaRunF

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace CapFetchCyG
open SailCycleOrderK PinCycRun PinDataflow
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)
open PinFetchPa (fpKeep fpKeepTrans pfPreludeT pfDispatchT fpLpadExpected fpTrapLpad fetchPostF)

/-! ## 1. The predicate -/

/-- **THE FETCH-HEAD CYCLE PREDICATE** (header). -/
def cyGB {X : Type} (Ag : CySt → Int → Prop) (P : X → CySt → Prop) : SailM X → CySt → Prop
  | .pure x, st => P x st
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, st =>
    match o, k with
    | .regRead r, k => ∀ v, PinCycRun.rdOk st r v → cyGB Ag P (k v) (cyRd st r)
    | .regWrite r v, k => Rboot r v ∧ ∀ u, cyGB Ag P (k u) (cyWr st r v)
    | .memRead n _ req, k =>
        (devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
          Ag st (paZ req.pa) ∧
          ∀ w : BitVec (8 * n), cyGB Ag P (k (.Ok (w, none))) (cyFe st (paZ req.pa) n w)) ∧
        ((devAddr req.pa = false → (classify req.access_kind).akIfetch = false) →
          ∀ w : BitVec (8 * n), cyGB Ag P (k (.Ok (w, none))) st)
    | .instrAnnounce n w, k => st.an = false ∧ ∀ u, cyGB Ag P (k u) (cyAnn st n w)
    | .memWrite .., k => cyGB Ag P (k (.Ok (some true))) st
    | .getCycleCount, k => cyGB Ag P (k (0 : Nat)) st
    | .barrier _, k => ∀ v, cyGB Ag P (k v) st
    | .branchAnnounce .., k => ∀ v, cyGB Ag P (k v) st
    | .cacheOp _, k => ∀ v, cyGB Ag P (k v) st
    | .tlbi _, k => ∀ v, cyGB Ag P (k v) st
    | .takeException _, k => ∀ v, cyGB Ag P (k v) st
    | .returnException _, k => ∀ v, cyGB Ag P (k v) st
    | .translationStart _, k => ∀ v, cyGB Ag P (k v) st
    | .translationEnd _, k => ∀ v, cyGB Ag P (k v) st
    | .cycleCount, k => ∀ v, cyGB Ag P (k v) st
    | .message _, k => ∀ v, cyGB Ag P (k v) st
    | .choose _, k => ∀ v, cyGB Ag P (k v) st
    | .readRam .., k => ∀ v, cyGB Ag P (k v) st
    | .writeRam .., k => ∀ v, cyGB Ag P (k v) st

/-- **The fetch obligation at `pc`** (header): the read is one of the cycle's two, at its
granule's page offset, and the mirror is at `PC = pc` in Supervisor mode. -/
def kAg (pc : Int) (st : CySt) (a : Int) : Prop :=
  st.fe.length < 2 ∧ a % 4096 = (pc + 2 * (st.fe.length : Int)) % 4096 ∧
  st.rv .PC = BitVec.ofInt 64 pc ∧ st.rv .cur_privilege = Privilege.Supervisor

/-! ## 2. The kit -/

section kit
variable {Ag : CySt → Int → Prop}

theorem cyGBind {X Y : Type} (Q : X → CySt → Prop) (P : Y → CySt → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ st, cyGB Ag Q m st → (∀ x st', Q x st' → cyGB Ag P (f x) st') → cyGB Ag P (m >>= f) st := by
  induction m with
  | pure y => intro st hm hf; exact hf y st hm
  | impure call k ih =>
    intro st hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show cyGB Ag P (FreeM.impure (.ok o) (fun v => k v >>= f)) st
      cases o
      case regRead => exact fun v hv => ih v _ (hm v hv) hf
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      case memRead =>
        exact ⟨fun h1 h2 => ⟨(hm.1 h1 h2).1, fun w => ih _ _ ((hm.1 h1 h2).2 w) hf⟩,
          fun h w => ih _ _ (hm.2 h w) hf⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      case memWrite => exact ih _ _ hm hf
      case getCycleCount => exact ih _ _ hm hf
      all_goals exact fun v => ih v _ (hm v) hf

theorem cyGMono {X : Type} (P P' : X → CySt → Prop) (hP : ∀ x st, P x st → P' x st) :
    ∀ (m : SailM X) st, cyGB Ag P m st → cyGB Ag P' m st := by
  intro m
  induction m with
  | pure y => exact fun st h => hP y st h
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv => ih v _ (hm v hv)
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case memRead =>
        exact ⟨fun h1 h2 => ⟨(hm.1 h1 h2).1, fun w => ih _ _ ((hm.1 h1 h2).2 w)⟩,
          fun h w => ih _ _ (hm.2 h w)⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case memWrite => exact ih _ _ hm
      case getCycleCount => exact ih _ _ hm
      all_goals exact fun v => ih v _ (hm v)

theorem cyGReadBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (f : RegisterType r → SailM Y)
    (st : CySt) (h : ∀ v, PinCycRun.rdOk st r v → cyGB Ag Q (f v) (cyRd st r)) :
    cyGB Ag Q (readReg r >>= f) st := h

theorem cyGWriteBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (v : RegisterType r)
    (f : PUnit → SailM Y) (st : CySt) (hb : Rboot r v) (h : cyGB Ag Q (f ()) (cyWr st r v)) :
    cyGB Ag Q (writeReg r v >>= f) st :=
  ⟨hb, fun u => by cases u; exact h⟩

theorem cyGAnnBind {Y : Type} (Q : Y → CySt → Prop) {n : Nat} (w : BitVec n) (f : Unit → SailM Y)
    (st : CySt) (han : st.an = false) (h : cyGB Ag Q (f ()) (cyAnn st n w)) :
    cyGB Ag Q (instr_announce w >>= f) st :=
  ⟨han, fun u => by cases u; exact h⟩

end kit

/-! ## 3. The lifts -/

section lift
variable {Ag : CySt → Int → Prop}

/-- **THE `fp` LIFT**: a W-SCO strict footprint (no fetch read, no announce) owes nothing and
keeps the log, the flag, the mirror `Rboot`-admitted. -/
theorem cyGOfFp {X : Type} (S : X → Prop) :
    ∀ (m : SailM X) (st : CySt), SailCycleOrderFp.fp S m → RbootAll st.rv →
      cyGB Ag (fun x st' => S x ∧ fpKeep st st') m st := by
  intro m
  induction m with
  | pure x => intro st hp hrb; exact ⟨hp, rfl, rfl, hrb⟩
  | impure call k ih =>
    intro st hp hrb
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        exact cyGMono _ _ (fun x s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩) _ _
          (ih v (cyRd st r) (hp v (PinCycRun.rdRboot st r v hrb hv)) hrb)
      case regWrite r v =>
        obtain ⟨hb, hk⟩ := hp
        refine ⟨hb, fun u => ?_⟩
        exact cyGMono _ _ (fun x s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩) _ _
          (ih u (cyWr st r v) (hk u) (rbootAllSet _ r v hrb hb))
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun _ h2 => ?_, fun _ w => ih _ st (hk _) hrb⟩
        exact absurd h2 (by simp only [SailCycleOrderFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hp.elim
      case barrier b => exact fun v => ih v st hp.2 hrb
      case memWrite => exact ih _ st (hp _) hrb
      case getCycleCount => exact ih _ st (hp _) hrb
      all_goals exact fun v => ih v st (hp v) hrb

theorem cyGFpBind {X Y : Type} (S : X → Prop) (P : Y → CySt → Prop) (m : SailM X) (f : X → SailM Y)
    (st : CySt) (hm : SailCycleOrderFp.fp S m) (hrb : RbootAll st.rv)
    (hf : ∀ x st', S x → fpKeep st st' → cyGB Ag P (f x) st') : cyGB Ag P (m >>= f) st :=
  cyGBind _ P m f st (cyGOfFp S m st hm hrb) (fun x st' h => hf x st' h.1 h.2)

/-- What a `pf` stretch keeps: `fpKeep` and the protected mirror. -/
def pkKeep (st st' : CySt) : Prop := fpKeep st st' ∧ ∀ r, pfProt r = true → st'.rv r = st.rv r

theorem pkKeepRefl (st : CySt) (h : RbootAll st.rv) : pkKeep st st := ⟨⟨rfl, rfl, h⟩, fun _ _ => rfl⟩

theorem pkKeepTrans (s1 s2 s3 : CySt) (h1 : pkKeep s1 s2) (h2 : pkKeep s2 s3) : pkKeep s1 s3 :=
  ⟨fpKeepTrans _ _ _ h1.1 h2.1, fun r hr => (h2.2 r hr).trans (h1.2 r hr)⟩

/-- **THE `pf` LIFT**: a w1 strict footprint (no protected write) keeps the protected mirror. -/
theorem cyGOfPf {X : Type} (S : X → Prop) :
    ∀ (m : SailM X) (st : CySt), pfB false S m → RbootAll st.rv →
      cyGB Ag (fun x st' => S x ∧ pkKeep st st') m st := by
  intro m
  induction m with
  | pure x => intro st hp hrb; exact ⟨hp, pkKeepRefl st hrb⟩
  | impure call k ih =>
    intro st hp hrb
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        have hb := PinCycRun.rdRboot st r v hrb hv
        exact cyGMono _ _ (fun x s' h => ⟨h.1, pkKeepTrans _ _ _ (pkKeepRefl st hrb) h.2⟩) _ _
          (ih v (cyRd st r) (hp v hb) hrb)
      case regWrite r v =>
        obtain ⟨⟨hb, hok⟩, hk⟩ := hp
        refine ⟨hb, fun u => ?_⟩
        have hrb' : RbootAll (cyWr st r v).rv := rbootAllSet _ r v hrb hb
        have hkp : pkKeep st (cyWr st r v) := by
          refine ⟨⟨rfl, rfl, hrb'⟩, fun r' hr' => ?_⟩
          have e : r' ≠ r := by
            rintro rfl
            simp [pfRegOk, hr'] at hok
          exact RegFile.set_other _ _ _ _ e
        exact cyGMono _ _ (fun x s' h => ⟨h.1, pkKeepTrans _ _ _ hkp h.2⟩) _ _
          (ih u (cyWr st r v) (hk u) hrb')
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun _ h2 => ?_, fun _ w => ih _ st (hk _) hrb⟩
        exact absurd h2 (by simp only [PinCycRunFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hp.elim
      case barrier b => exact fun v => ih v st hp.2 hrb
      case memWrite => exact ih _ st (hp _) hrb
      case getCycleCount => exact ih _ st (hp _) hrb
      all_goals exact fun v => ih v st (hp v) hrb

end lift

/-! ## 4. The fetch: w1's frame × the offset walk -/

/-- The fetch's mirror invariant relative to its start `st0`, at count `i`. -/
def gxInv (pc : Int) (st0 st : CySt) (i : Nat) : Prop :=
  (∀ r, pfProt r = true → st.rv r = st0.rv r) ∧ RbootAll st.rv ∧ st.fe.length = i ∧
  st.an = st0.an ∧ st.rv .PC = BitVec.ofInt 64 pc

set_option maxHeartbeats 4000000 in
/-- **THE PRODUCT** (header): along w1's frame (`pfB true`) and the offset walk (`foB`), from a
Supervisor-mode start, every RAM fetch read meets `kAg pc`. -/
theorem cyGOfPfFo (pc : Int) (st0 : CySt) (hS0 : st0.rv .cur_privilege = Privilege.Supervisor)
    {X : Type} (P : X → Nat → Prop) (S : X → Prop) (Q : X → CySt → Prop) :
    ∀ (m : SailM X) (st : CySt) (i : Nat), pfB true S m → CapFetchOfs.foB pc P m i →
      gxInv pc st0 st i → (∀ x st' i', P x i' → S x → gxInv pc st0 st' i' → Q x st') →
      cyGB (kAg pc) Q m st := by
  intro m
  induction m with
  | pure x => intro st i hp hq hi hk; exact hk x st i hq hp hi
  | impure call k ih =>
    intro st i hp hq hi hk
    obtain ⟨hpr, hrb, hlen, han, hpc⟩ := hi
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        have hb : Rboot r v := PinCycRun.rdRboot st r v hrb hv
        have hP : ∀ h : r = .PC, cast (congrArg RegisterType h) v = BitVec.ofInt 64 pc := by
          intro h
          subst h
          rw [hv (by decide)]
          exact hpc
        exact ih v (cyRd st r) i (hp v hb) (hq v hb hP) ⟨hpr, hrb, hlen, han, hpc⟩ hk
      case regWrite r v =>
        obtain ⟨⟨hb, hok⟩, hkp⟩ := hp
        obtain ⟨-, hkq⟩ := hq
        have hpf : pfProt r = false := by simpa [pfRegOk] using hok
        refine ⟨hb, fun u => ih u (cyWr st r v) i (hkp u) (hkq u) ⟨fun r' h' => ?_,
          rbootAllSet _ r v hrb hb, hlen, han, ?_⟩ hk⟩
        · have e : r' ≠ r := by rintro rfl; rw [hpf] at h'; cases h'
          show (st.rv.set r v) r' = _
          rw [RegFile.set_other _ _ _ _ e]; exact hpr r' h'
        · have e : Register.PC ≠ r := by rintro rfl; cases hpf
          show (st.rv.set r v) .PC = _
          rw [RegFile.set_other _ _ _ _ e]; exact hpc
      case memRead n va req =>
        refine ⟨fun _ hif => ?_, fun h w => ?_⟩
        · obtain ⟨-, ⟨hi2, ha⟩, hkq⟩ := hq.1 hif
          refine ⟨⟨by rw [hlen]; exact hi2, by rw [hlen]; exact ha, hpc, ?_⟩,
            fun w => ih _ (cyFe st (paZ req.pa) n w) (i + 1) (hp.2 _) (hkq w)
              ⟨hpr, hrb, ?_, han, hpc⟩ hk⟩
          · rw [hpr .cur_privilege (by decide)]; exact hS0
          · simp [cyFe, hlen]
        · cases hif : (classify req.access_kind).akIfetch with
          | false => exact ih _ st i (hp.2 _) (hq.2 hif w) ⟨hpr, hrb, hlen, han, hpc⟩ hk
          | true =>
            have := h (hq.1 hif).1
            rw [hif] at this; cases this
      case instrAnnounce => exact hq.elim
      case barrier b => exact fun v => ih v st i hp.2 (hq v) ⟨hpr, hrb, hlen, han, hpc⟩ hk
      case memWrite => exact ih _ st i (hp _) (hq _) ⟨hpr, hrb, hlen, han, hpc⟩ hk
      case getCycleCount => exact ih _ st i (hp _) (hq _) ⟨hpr, hrb, hlen, han, hpc⟩ hk
      all_goals exact fun v => ih v st i (hp v) (hq v) ⟨hpr, hrb, hlen, han, hpc⟩ hk

/-- **THE FETCH IN THE CYCLE** (header): from an empty log at `PC = pc` in Supervisor mode,
`fetch ()` satisfies `cyGB (kAg pc)`, with r2's post `fetchPostF`. -/
theorem cyGFetch (pc : Int) (h0 : 0 ≤ pc) (hlt : pc + 2 < 2 ^ 64) (st : CySt) (hfe : st.fe = [])
    (hpc : st.rv .PC = BitVec.ofInt 64 pc) (hS : st.rv .cur_privilege = Privilege.Supervisor)
    (hrb : RbootAll st.rv) :
    cyGB (kAg pc) (fetchPostF st) (fetch ()) st :=
  cyGOfPfFo pc st hS (fun _ _ => True) _ _ (fetch ()) st 0 PinCycRunFp.PinCycRunFetch.pfFetch
    (CapFetchOfs.foFetch pc h0 hlt) ⟨fun _ _ => rfl, hrb, by rw [hfe]; rfl, rfl, hpc⟩
    (fun fr st' _ _ hok hi => ⟨hok, hi.1, hi.2.2.2.1, hi.2.1⟩)

/-! ## 5. The cycle -/

section nofetch
variable {Ag : CySt → Int → Prop}

/-- `execute` of ANY instruction makes no fetch read. -/
theorem cyGExec (i : instruction) (st : CySt) (hrb : RbootAll st.rv) :
    cyGB Ag (fun _ st' => fpKeep st st') (execute i) st := by
  cases h : SailCycleOrderFp.isFI i
  · exact cyGMono _ _ (fun _ _ h => h.2) _ _ (cyGOfFp _ _ st (SailCycleOrderFp.fpExecNotFI i h) hrb)
  · obtain ⟨p, rfl⟩ : ∃ p, i = .FENCEI p := by
      cases i <;> first | exact ⟨_, rfl⟩ | (exfalso; revert h; simp only [SailCycleOrderFp.isFI]; decide)
    obtain ⟨imm, rs, rd⟩ := p
    simp only [execute, execute_FENCEI, PreSail.sail_barrier, PreSail.emit, bind_assoc, pure_bind]
    exact fun _ => ⟨rfl, rfl, hrb⟩

/-- `uxaExecAs`: `execute` and its one redirect. -/
theorem cyGExecAs (i : instruction) (st : CySt) (hrb : RbootAll st.rv) :
    cyGB Ag (fun _ st' => fpKeep st st') (uxaExecAs i) st := by
  unfold uxaExecAs
  refine cyGBind _ _ _ _ st (cyGExec i st hrb) (fun r st' h => ?_)
  cases r with
  | ExecuteAs j => exact cyGMono _ _ (fun _ s h' => fpKeepTrans _ _ _ h h') _ _ (cyGExec j st' h.2.2)
  | _ => exact h

/-- `ucFinish`, then the optional tick. -/
theorem cyGFinish (s : Step) (tick : Bool) (st : CySt) (hrb : RbootAll st.rv) :
    cyGB Ag (fun _ _ => True) (ucFinish s >>= fun _ => if tick then tick_clock () else pure ()) st := by
  refine cyGFpBind _ _ _ _ st (SailCycleOrderFp.fpFinish s) hrb (fun _ st' _ hk => ?_)
  split
  · exact cyGMono _ _ (fun _ _ _ => trivial) _ _ (cyGOfFp _ _ st' SailCycleOrderFp.fpTickClock hk.2.2)
  · exact trivial

end nofetch

set_option maxHeartbeats 40000000 in
/-- **THE FETCH-HEAD CYCLE** (header): every cycle `riscvStep tick` from an empty log, no
announce, `PC = pc`, Supervisor mode, every register `Rboot`-admitted satisfies `cyGB (kAg pc)`
— whatever word is fetched and executed (`PinFetchPa.cyFSailOf`'s walk, the fetch by
`cyGFetch`). -/
theorem cyGSailOf (pc : Int) (h0 : 0 ≤ pc) (hlt : pc + 2 < 2 ^ 64) (tick : Bool) (st : CySt)
    (hfe : st.fe = []) (han : st.an = false) (hpc : st.rv .PC = BitVec.ofInt 64 pc)
    (hS : st.rv .cur_privilege = Privilege.Supervisor) (hrb : RbootAll st.rv) :
    cyGB (kAg pc) (fun _ _ => True) (riscvStep tick) st := by
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  refine cyGBind _ _ _ _ st (cyGOfPf _ ucPrelude st pfPreludeT hrb) (fun hs st1 h1 => ?_)
  have hk1 := h1.2
  cases hs with
  | HART_WAITING p =>
    obtain ⟨wr, ib⟩ := p
    simp only [ucBody]
    exact cyGFpBind _ _ _ _ st1 (SailCycleOrderFp.fpWaiting wr ib) hk1.1.2.2
      (fun s st2 _ hk2 => cyGFinish s tick st2 hk2.2.2)
  | HART_ACTIVE u =>
    simp only [ucBody]
    rw [uc_runHartActive_eq]
    simp only [bind_assoc]
    refine cyGBind _ _ _ _ st1 (cyGOfPf _ ucDispatch st1 pfDispatchT hk1.1.2.2)
      (fun o st2 h2 => ?_)
    have hk2 := pkKeepTrans _ _ _ hk1 h2.2
    cases o with
    | some ip =>
      simp only [pure_bind]
      exact cyGFinish _ tick st2 hk2.1.2.2
    | none =>
      simp only [bind_assoc]
      have hfe2 : st2.fe = [] := hk2.1.1.trans hfe
      have hpc2 : st2.rv .PC = BitVec.ofInt 64 pc := (hk2.2 .PC (by decide)).trans hpc
      have hS2 : st2.rv .cur_privilege = Privilege.Supervisor :=
        (hk2.2 .cur_privilege (by decide)).trans hS
      refine cyGBind _ _ _ _ st2 (cyGFetch pc h0 hlt st2 hfe2 hpc2 hS2 hk2.1.2.2)
        (fun fr st3 h3 => ?_)
      obtain ⟨hok, -, han3, hrb3⟩ := h3
      have han3' : st3.an = false := han3.trans (hk2.1.2.1.trans han)
      cases fr with
      | F_Ext_Error e => exact hok.elim
      | F_Error p =>
        obtain ⟨e, addr⟩ := p
        simp only [ucAfterFetch, ext_fetch_hook, pure_bind]
        exact cyGFinish _ tick st3 hrb3
      | F_RVC h =>
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        refine cyGAnnBind _ h _ st3 han3' ?_
        refine cyGFpBind _ _ _ _ _ (SailCycleOrderFp.fpDecodeC h) hrb3 (fun i st5 _ hk5 => ?_)
        refine cyGFpBind _ _ _ _ _ fpLpadExpected hk5.2.2 (fun b st6 _ hk6 => ?_)
        refine cyGBind (fun _ st' => RbootAll st'.rv) _ _ _ st6 ?_ (fun s st7 h7 => cyGFinish s tick st7 h7)
        split
        · exact cyGFpBind _ _ _ _ _ fpTrapLpad hk6.2.2 (fun r st7 _ hk7 => hk7.2.2)
        · refine cyGFpBind _ _ _ _ _ (SailCycleOrderFp.fpCurrentlyEnabled _) hk6.2.2 (fun z st7 _ hk7 => ?_)
          split
          · refine cyGReadBind _ _ _ _ (fun v _ => ?_)
            refine cyGWriteBind _ _ _ _ _ trivial ?_
            exact cyGBind _ _ _ _ _ (cyGExecAs i _ (rbootAllSet _ _ _ hk7.2.2 trivial)) (fun r st8 h8 => h8.2.2)
          · exact hk7.2.2
      | F_Base w =>
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        refine cyGAnnBind _ w _ st3 han3' ?_
        refine cyGFpBind _ _ _ _ _ (SailCycleOrderFp.fpDecodeS w) hrb3 (fun i st5 _ hk5 => ?_)
        refine cyGFpBind _ _ _ _ _ fpLpadExpected hk5.2.2 (fun b st6 _ hk6 => ?_)
        refine cyGBind (fun _ st' => RbootAll st'.rv) _ _ _ st6 ?_ (fun s st7 h7 => cyGFinish s tick st7 h7)
        split
        · exact cyGFpBind _ _ _ _ _ fpTrapLpad hk6.2.2 (fun r st7 _ hk7 => hk7.2.2)
        · refine cyGReadBind _ _ _ _ (fun v _ => ?_)
          refine cyGWriteBind _ _ _ _ _ trivial ?_
          exact cyGBind _ _ _ _ _ (cyGExecAs i _ (rbootAllSet _ _ _ hk6.2.2 trivial)) (fun r st8 h8 => h8.2.2)

/-! ## 6. The run -/

/-- The hart's head is a RAM instruction-fetch read at `a`. -/
def fH (m : SailM Unit) (a : Int) : Prop :=
  ∃ (n va : Nat) (req : _) (k : _), m = .impure (.ok (Outcome.memRead n va req)) k ∧
    akIfetch req.access_kind = true ∧ devAddr req.pa = false ∧ paZ req.pa = a

section run
variable {Ag : CySt → Int → Prop} {P : Unit → CySt → Prop}

/-- One step's conclusion: at a fetch label, the obligation at the PRE-state and the head; a
matched state for the new tree. -/
def cyGStepOk (Ag : CySt → Int → Prop) (P : Unit → CySt → Prop) (st : CySt) (m : SailM Unit)
    (l : Wlabel) (m' : SailM Unit) (ib' : Ibch) (rs' : RegFile) : Prop :=
  (∀ a tvs, l = LIFetch a tvs → Ag st a ∧ fH m a) ∧
  ∃ st', cyGB Ag P m' st' ∧ cyMatch st' rs' ib' ∧ st'.fe.length = st.fe.length + (feLabs [l]).length

theorem cyGStay (st : CySt) (m : SailM Unit) (l : Wlabel) (m' : SailM Unit) (ib : Ibch) (rs : RegFile)
    (hcy : cyGB Ag P m' st) (hm : cyMatch st rs ib) (hfe : isFeLab l = false) :
    cyGStepOk Ag P st m l m' ib rs :=
  ⟨fun a tvs e => (by subst e; cases hfe), st, hcy, hm, by simp [feLabs, hfe]⟩

set_option maxHeartbeats 4000000 in
/-- **One Sail node.** -/
theorem cyGNodeStep (m : SailM Unit) (rs : RegFile) (ib : Ibch) (dd : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (dd' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (st : CySt)
    (hstep : pnodeStep m rs ib dd l m' ors fn' dd' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyGB Ag P m st) (hm : cyMatch st rs ib) :
    cyGStepOk Ag P st m l m' (oib.getD ib) (ors.getD rs) := by
  obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
  match m, hstep with
  | .pure x, _ => exact absurd rfl (hpure x)
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      have hv : PinCycRun.rdOk st r (rs r) := fun hw => hag r hw
      refine ⟨fun a tvs e => (by cases e), cyRd st r, hcy (rs r) hv, ⟨hag, hrb, hrbv, ?_, ?_, ?_⟩,
        by simp [feLabs, isFeLab, cyRd]⟩
      · show st.d.ro = depsOfIb (ibRd ib r).ibBits
        rw [ibRdBits]; exact hro
      · show dfRdsAdd st.d.rds (eregNum r) = (ibRd ib r).ibRds
        rw [hrds]; exact (dfRdsAddIb ib (eregNum r)).symm
      · show st.an = (ibRd ib r).ibBits.isSome
        rw [ibRdBits]; exact han
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      obtain ⟨hrv, hk⟩ := hcy
      have hfl : isFeLab (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) = false := by
        unfold erwLabel; split <;> rfl
      refine ⟨fun a tvs e => (by rw [e] at hfl; cases hfl), cyWr st r v, hk (),
        ⟨PinCycRun.agreeSet rs st.rv r v hag, rbootAllSet rs r v hrb hrv,
          rbootAllSet st.rv r v hrbv hrv, hro, hrds, han⟩, ?_⟩
      simp [feLabs, hfl, cyWr]
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · rename_i hdv
        obtain ⟨w, -, rfl, rfl, rfl, -, rfl, -⟩ := h
        exact cyGStay st _ _ _ ib rs
          (hcy.2 (fun h' => absurd (hdv.symm.trans h') (by decide)) _)
          ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
      · rename_i hdv
        have hdev' : devAddr req.pa = false := by simpa using hdv
        rcases h with ⟨hif, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
          ⟨hif, ⟨-, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩⟩
        · obtain ⟨ha, hk⟩ := hcy.1 hdev' hif
          refine ⟨fun a tvs' e => ?_, cyFe st (paZ req.pa) n w, hk w,
            ⟨hag, hrb, hrbv, hro, hrds, han⟩, by simp [feLabs, isFeLab, cyFe]⟩
          injection e with e
          rw [← e]
          exact ⟨ha, n, va, req, k, rfl, hif, hdev', rfl⟩
        · exact cyGStay st _ _ _ ib rs (hcy.2 (fun _ => hif) _)
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact cyGStay st _ _ _ ib rs (hcy.2 (fun _ => hif) _)
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨-, rfl, rfl, rfl, -, rfl, -⟩ := h
          exact cyGStay st _ _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact h.elim
      · split at h
        · obtain ⟨-, h⟩ := h
          rcases h with ⟨-, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, ⟨rfl, rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, rfl, -, -, rfl, -⟩⟩
          · exact cyGStay st _ _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
          · exact cyGStay st _ _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
          · exact cyGStay st _ _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact h.elim
    | barrier b =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      refine cyGStay st _ _ _ ib rs (hcy ()) ⟨hag, hrb, hrbv, hro, hrds, han⟩ ?_
      unfold ebarLabel
      split <;> rfl
    | instrAnnounce n w =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      obtain ⟨han0, hk⟩ := hcy
      have hfl : isFeLab (annLabel n w) = false := by unfold annLabel; split <;> rfl
      refine ⟨fun a tvs e => (by rw [e] at hfl; cases hfl), cyAnn st n w, hk (),
        ⟨hag, hrb, hrbv, rfl, rfl, rfl⟩, ?_⟩
      simp [feLabs, hfl, cyAnn]
    | choose s =>
      obtain ⟨ch, rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy ch) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | branchAnnounce =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | cacheOp =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | tlbi =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | takeException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | returnException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | translationStart =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | translationEnd =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | cycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | message =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyGStay st _ _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl

/-- **One hart step**: a Sail node, a parked fence firing, or a PLIC wire write. -/
theorem cyGHartStep (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : CySt)
    (hstep : pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyGB Ag P m st) (hm : cyMatch st rs ib) :
    cyGStepOk Ag P st m l m' (oib.getD ib) (ors.getD rs) := by
  rcases hstep with ⟨H, hd⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := H
      exact cyGStay st _ _ _ ib rs hcy hm rfl
    | none => exact cyGNodeStep m rs ib d.efDev l m' ors fn' d'.efDev oib obar st H hpure hcy hm
  · obtain ⟨mm, b, k, -, rfl, rfl, -, -, rfl, -, rfl⟩ := H
    obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
    refine cyGStay st _ _ _ ib _ hcy ⟨?_, ?_, hrbv, hro, hrds, han⟩ rfl
    · show ∀ r, wireReg r = false → (pinSet rs mm b) r = st.rv r
      unfold pinSet
      split
      · exact PinCycRun.agreeSetWire rs st.rv _ _ rfl hag
      · exact PinCycRun.agreeSetWire rs st.rv _ _ rfl hag
    · show RbootAll (pinSet rs mm b)
      unfold pinSet
      split
      · exact rbootAllSet rs _ _ hrb trivial
      · exact rbootAllSet rs _ _ hrb trivial

/-- **THE RUN** (header): every fetch label of an in-cycle run is made from a pre-state the run
reaches, whose head is that fetch read and whose mirror owes the obligation. -/
theorem cyGRun :
    ∀ (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab), irun ls p d p' d' →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch) (st : CySt), p = .PHart cpu m rs fn ib → cyGB Ag P m st → cyMatch st rs ib →
      ∀ (ls1 : List Wlabel) (a : Int) (tvs : List (Nat × BitVec 8)) (ls2 : List Wlabel),
        ls = ls1 ++ LIFetch a tvs :: ls2 →
        ∃ (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch)
          (d1 : Efab) (st1 : CySt),
          irun ls1 p d (.PHart cpu m1 rs1 fn1 ib1) d1 ∧ cyMatch st1 rs1 ib1 ∧
          st1.fe.length = st.fe.length + (feLabs ls1).length ∧ Ag st1 a ∧ fH m1 a := by
  intro ls p d p' d' h
  induction h with
  | nil p d =>
    intro _ _ _ _ _ _ _ _ _ ls1 a tvs ls2 e
    cases ls1 <;> cases e
  | @more l ls cpu c k rs fn ib d p1 d1 p2 d2 hstep hrest ih =>
    intro cpu' m rs' fn' ib' st hp hcy hm ls1 a tvs ls2 e
    injection hp with e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    cases p1 with
    | PDisk dp => exact (show False from hstep).elim
    | PHart cpu1 m1 rs1 fn1 ib1 =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := hstep
    have hst : pstepEv (.PHart cpu1 (.impure c k) rs fn ib) d l
        (.PHart cpu1 m1 (ors.getD rs) fn1 (oib.getD ib)) d1 :=
      ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩
    obtain ⟨hA, st', hcy', hm', hlen⟩ := cyGHartStep cpu1 _ rs fn ib d l m1 ors fn1 d1 oib obar st hh
      (fun x e => by cases e) hcy hm
    cases ls1 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      obtain ⟨hag, hf⟩ := hA a tvs rfl
      exact ⟨_, rs, fn, ib, d, st, irun.nil _ _, hm, by simp [feLabs], hag, hf⟩
    | cons l' ls1' =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      obtain ⟨mm, rr, ff, ii, dd, st1, hir, hmm, hlen1, hag, hf⟩ :=
        ih cpu1 m1 (ors.getD rs) fn1 (oib.getD ib) st' rfl hcy' hm' ls1' a tvs ls2 e
      refine ⟨mm, rr, ff, ii, dd, st1, irun.more hst hir, hmm, ?_, hag, hf⟩
      rw [hlen1, hlen, Nat.add_assoc, ← List.length_append]
      have e2 : feLabs [l] ++ feLabs ls1' = feLabs (l :: ls1') := by
        simp only [feLabs, List.filter_cons, List.filter_nil]
        split <;> rfl
      rw [e2]
  | @jump ls p d e p2 d2 _ ih =>
    intro cpu m rs fn ib st hp hcy hm ls1 a tvs ls2 he
    obtain ⟨mm, rr, ff, ii, dd, st1, hir, hmm, hlen1, hag, hf⟩ := ih cpu m rs fn ib st hp hcy hm ls1 a tvs ls2 he
    exact ⟨mm, rr, ff, ii, dd, st1, .jump hir, hmm, hlen1, hag, hf⟩

end run

end CapFetchCyG
end Weak
