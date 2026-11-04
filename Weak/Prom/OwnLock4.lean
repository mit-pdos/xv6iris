/-
Weak/Prom: **G4 target (4), a lock born by a plain store over junk and published, PROVED on track (b)** (stage S4b
part 3, tag S4b3; plan rev 7 §4 "Gate G4" (4), §3 "Lock birth and deferred deposits").  Test, protocol and steps:
OwnLock4Defs.lean, OwnLock4Steps.lean.

The Iris layer: R (the counter's points-to) is a ghost-variable half `hv c (.r rec)` whose NAME `c` IS ALLOCATED AT
RUNTIME, at H0's birth store (`initlock`), and recorded in the protocol state (`S4.γ`) and in H0's phase ghost.  The
state interpretation holds the other half once `c` exists, and R itself while it is DEPOSITED (place 1, from the
publish on) — the deferred deposit of the birth store at H0's next release-class write; H1's acquire, which read the
born cell, TAKES it (place 2).  No saved-proposition slot and no pre-allocated invariant are needed on track (b): the
deposit is in place, and the state interpretation can name ghost state allocated later (plan [R3.6]'s concern is
track (a)'s pre-allocated invariants).
`g4_lockBirth`: in every valid machine-v2 run of `lk4T`, if H1 saw the publication (x5 ≠ 0) and acquired (x6 = 0), it
read 42 (x8 = 42).  0 named inputs; PO-fetch and `invalFree` by OwnLitSide.lean; finite runs.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLock4Steps
import Weak.Prom.OwnLitSide
import Weak.Prom.CoreKitQ
import Weak.Prom.OwnMPL
import Weak.Prom.OwnLock
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth

namespace Weak.Prom.Own.L4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au wrA_of_memByte relClass_store0)
open Weak.Prom.Own.MPL (XRec loadOk_byte val8 val8_42 rd_regs fwdView_psInit bytesAll_get relClass_fW xMsg
  map_snd_of)
open Weak.Prom.Own.Lk (amo_x5 cohBelow_get pend)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq ldVal instrR amoD)
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Pure machine facts -/

theorem loadBytes_aqle (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    ws.wVrOld ≤ ws.wVwNew → (loadBytes true vpre ws a tvs).wVrOld ≤ (loadBytes true vpre ws a tvs).wVwNew
  | _, _, [], h => h
  | ws, a, (t, _) :: r, h => by
    simp only [loadBytes]
    exact loadBytes_aqle vpre _ (a + 1) r (by simp only [loadByte, if_true]; omega)

/-- An acquire AMO of a hart with no earlier write, after `fence r,rw`, is release-class (plan §3): in place. -/
theorem relClass_aq1 (ws : PState) (rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (d : List (BitVec 8))
    (asrc vsrc : List Dsrc) (h0 : ws.wVwOld = 0) (h1 : ws.wVrOld ≤ ws.wVwNew) :
    relClass ws (LRmw true rl base tvs d asrc vsrc) := by
  refine ⟨_, rfl, ?_⟩
  have e1 := loadBytes_aqle (ldPre ws true false (srcsView ws asrc)) ws base tvs h1
  have e2 := (loadRun_keep ws true false (srcsView ws asrc) base tvs).2.1
  simp only [wrState, stPre] at *
  show max (loadRun ws true false (srcsView ws asrc) base tvs).wVrOld
    (loadRun ws true false (srcsView ws asrc) base tvs).wVwOld ≤ _
  rw [e2, h0]
  have : (loadRun ws true false (srcsView ws asrc) base tvs).wVrOld ≤
      (loadRun ws true false (srcsView ws asrc) base tvs).wVwNew := e1
  omega

theorem ofBytes8_of_zero {tvs : List (Nat × BitVec 8)} (hl : tvs.length = 8)
    (h : ∀ (j t : Nat) (b : BitVec 8), tvs[j]? = some (t, b) → b = 0) : val8 tvs = 0 := by
  match tvs, hl with
  | [(t0, b0), (t1, b1), (t2, b2), (t3, b3), (t4, b4), (t5, b5), (t6, b6), (t7, b7)], _ =>
    have h0 := h 0 t0 b0 rfl; have h1 := h 1 t1 b1 rfl; have h2 := h 2 t2 b2 rfl; have h3 := h 3 t3 b3 rfl
    have h4 := h 4 t4 b4 rfl; have h5 := h 5 t5 b5 rfl; have h6 := h 6 t6 b6 rfl; have h7 := h 7 t7 b7 rfl
    subst h0 h1 h2 h3 h4 h5 h6 h7
    rfl

/-! ## 2. Ghost state -/

inductive MG4 where
  | r (x : XRec)
  | h0 (p ti tc : Nat) (γ : Option Nat)
  | h1 (p a1 : Nat) (b1 : Option Nat) (bd : Bool)

section gf
open Iris COFE Auth HeapView

noncomputable def lk4GF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF MG4, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS lk4GF where
  inv := { τ := 0, transp := by unfold lk4GF; rfl }
  enabled := { τ := 1, transp := by unfold lk4GF; rfl }
  disabled := { τ := 2, transp := by unfold lk4GF; rfl }

instance : LcGpreS lk4GF where
  lc_elem := { τ := 3, transp := by unfold lk4GF; rfl }

instance : InvGpreS lk4GF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG lk4GF MG4 where
  elemG := { τ := 4, transp := by unfold lk4GF; rfl }

end gf

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF MG4]

def hv (γ : GName) (m : MG4) : IProp GF := ghost_var γ (.own (1 : Qp).half) m

def P0 (g : S4) : MG4 := .h0 g.p0 g.ti g.tc g.γ
def P1 (g : S4) : MG4 := .h1 g.p1 g.a1 g.b1 g.bd1

/-- R's halves held by the state interpretation: one once the name exists; both while DEPOSITED. -/
def Rc (g : S4) : IProp GF :=
  match g.γ with
  | none => iprop(True)
  | some c => iprop(hv c (.r (rec4 g)) ∗ (if g.rp = 1 then hv c (.r (rec4 g)) else iprop(True)))

/-- THE STATE INTERPRETATION. -/
abbrev X4 (M : List PMsg) (γ0 γ1 : GName) (σ : OSt (List Nat)) : IProp GF :=
  iprop(∃ g : S4, hv γ0 (P0 g) ∗ hv γ1 (P1 g) ∗ ⌜I4 lk4Img M σ g⌝ ∗ Rc g)

theorem r_inj {a b : XRec} (h : MG4.r a = MG4.r b) : a = b := by cases h; rfl
theorem h0_inj {a b c d a' b' c' d'} (h : MG4.h0 a b c d = MG4.h0 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩
theorem h1_inj {a b c d a' b' c' d'} (h : MG4.h1 a b c d = MG4.h1 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

/-- Facts of a hart state of a text. -/
structure HS (P : List Instr) (s : LP) (p : Nat) : Prop where
  prog : s.prog = P
  pc : s.pc = p
  q : s.q = []
  len : s.regs.length = 32

theorem HS.succ {P : List Instr} {s s' : LP} {p rd v : Nat} (h : HS P s p) (hs : LPstep s s' (s.pc + 1) rd v) :
    HS P s' (p + 1) :=
  ⟨(LPstep_at hs h.prog (by rw [h.pc])).1, (LPstep_at hs h.prog (by rw [h.pc])).2.1,
    (LPstep_at hs h.prog (by rw [h.pc])).2.2, by rw [hs.2.2.2.1, h.len]⟩

/-! ## 3. H0, the allocator -/

section h0

variable [InvGS_gen hlc GF] (M : List PMsg) (γ0 γ1 : GName)

abbrev W0 (s : LP) (ws : PState) : IProp GF :=
  wpT (hlc := hlc) (X4 M γ0 γ1) lk4Img M 0 s ws (fun _ => iprop(True))

theorem g0End (s : LP) (ws : PState) (hP : s.prog.length ≤ s.pc) (hq : s.q = []) :
    ⊢ W0 (hlc := hlc) (GF := GF) M γ0 γ1 s ws := by
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  imodintro
  isplitl
  · iexists g; iframe; ipureintro; exact i4_fin (h := 0) (gg := s.regs) hok (fun e => absurd e (by decide))
  · ipureintro; trivial

/-- **THE PUBLISH** `sd x7,(x12)` (release-class after `fence rw,w`: in place) — THE DEFERRED DEPOSIT. -/
theorem g0Pub (s : LP) (ws : PState) (hs : HS h0Prog s 4) (h12 : s.rd 12 = Weak.Prom.Ref.Lit.Z)
    (h7 : s.rd 7 = 1) (hrc : ∀ a d asrc vsrc, relClass ws (LStore false false a d asrc vsrc)) (ti tc c : Nat)
    (hv1 : ti ≤ ws.wVwNew ∧ tc ≤ ws.wVwNew) :
    hv (GF := GF) γ0 (.h0 3 ti tc (some c)) ∗ hv c (.r ⟨none, 0, tc, 42⟩) ⊢ W0 M γ0 γ1 s ws := by
  iintro ⟨Hm, HR⟩
  iapply (wpT_sd (sz := 8) (rs2 := 7) (rs1 := 12) (off := 0) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [h12]; decide))
  inext
  iintro %σ %ts %σ' %hful %hmsg %_ %hext HX _
  have hM : M[ts - 1]? = some flagMsg := by
    have := (take_msg hmsg).1
    have hb : (((s.rd 12 + 0) % two64 : Nat) : Int) = F := by rw [h12]; decide
    rw [hb, h7] at this; exact this
  have hlt : ws.wVwNew < ts := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 12)) (srcsView ws (srcR 7))).2.2.2.1; omega
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  unfold hv
  ihave %e := ghost_var_agree γ0 _ _ _ _ $$ Hm H0
  obtain ⟨e1, e2, e3, e4⟩ := h0_inj e
  have hok' := h0_pub hok e1.symm (hrc _ _ _ _) hful hM (by rw [← e2]; omega) (by rw [← e3]; omega)
  have hrec : rec4 { g with p0 := 4, tf := ts, rp := 1 } = ⟨none, 0, tc, 42⟩ := by
    simp [rec4, e3]
  have hrc0 : g.rp = 0 := hok.rp_ok.2.1.2 (by omega)
  imod ghost_var_update_halves (MG4.h0 4 ti tc (some c)) γ0 _ _ $$ Hm H0 with ⟨Hm, H0⟩
  imodintro
  isplitl [H0 H1 Hr HR]
  · iexists { g with p0 := 4, tf := ts, rp := 1 }
    have eP0 : P0 { g with p0 := 4, tf := ts, rp := 1 } = MG4.h0 4 ti tc (some c) := by
      simp [P0, ← e2, ← e3, ← e4]
    have eP1 : P1 { g with p0 := 4, tf := ts, rp := 1 } = P1 g := rfl
    have eR : Rc (GF := GF) g = iprop(hv c (.r ⟨none, 0, tc, 42⟩) ∗ True) := by
      simp [Rc, ← e4, hrc0, rec4, ← e1, e3]
    have eR' : Rc (GF := GF) { g with p0 := 4, tf := ts, rp := 1 } =
        iprop(hv c (.r ⟨none, 0, tc, 42⟩) ∗ hv c (.r ⟨none, 0, tc, 42⟩)) := by
      simp [Rc, ← e4, rec4, ← e3]
    rw [eP0, eP1, eR']
    rw [eR]
    unfold hv
    icases Hr with ⟨Hr, -⟩
    iframe; ipureintro; exact hok'
  iintro %s' %hs'
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hs.prog (by rw [hs.pc])
  iapply (g0End M γ0 γ1 s' _ (by rw [hP', hc']; decide) hq')

/-- `fence rw,w`. -/
theorem g0Fence (s : LP) (ws : PState) (hs : HS h0Prog s 3) (h12 : s.rd 12 = Weak.Prom.Ref.Lit.Z)
    (h7 : s.rd 7 = 1) (ti tc c : Nat) (hv1 : ti ≤ ws.wVwOld ∧ tc ≤ ws.wVwOld) :
    hv (GF := GF) γ0 (.h0 3 ti tc (some c)) ∗ hv c (.r ⟨none, 0, tc, 42⟩) ⊢ W0 M γ0 γ1 s ws := by
  iintro H
  iapply (wpT_fence (f := ⟨true, true, false, false, false, true, false, false⟩) hs.q (by rw [hs.prog, hs.pc]; rfl))
  iintro %s' %hs'
  have hv2 : ti ≤ (instrR (fencePost ws true true false true)).wVwNew ∧
      tc ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR, fencePost, if_true, if_false]; omega
  iapply (g0Pub M γ0 γ1 s' _ (hs.succ hs') (by rw [LPstep_rd hs' 12 (.inr rfl), h12])
    (by rw [LPstep_rd hs' 7 (.inr rfl), h7]) (fun a d asrc vsrc => relClass_fW ws _ _ _ _ rfl rfl rfl a d asrc vsrc)
    ti tc c hv2)
  iexact H

/-- **THE DATA STORE** `sd x5,(x11)` (c := 42): R's record follows (both halves). -/
theorem g0Cnt (s : LP) (ws : PState) (hs : HS h0Prog s 2) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (h12 : s.rd 12 = Weak.Prom.Ref.Lit.Z) (h5 : s.rd 5 = 42) (h7 : s.rd 7 = 1) (ti tc0 c : Nat)
    (hv1 : ti ≤ ws.wVwOld) :
    hv (GF := GF) γ0 (.h0 2 ti tc0 (some c)) ∗ hv c (.r ⟨none, 0, 0, 0⟩) ⊢ W0 M γ0 γ1 s ws := by
  iintro ⟨Hm, HR⟩
  iapply (wpT_sd (sz := 8) (rs2 := 5) (rs1 := 11) (off := 0) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [h11]; decide))
  inext
  iintro %σ %ts %σ' %hful %hmsg %_ %_ HX _
  have hM : M[ts - 1]? = some xMsg := by
    have := (take_msg hmsg).1
    have hb : (((s.rd 11 + 0) % two64 : Nat) : Int) = Weak.Prom.Own.MPL.X := by rw [h11]; decide
    rw [hb, h5] at this; exact this
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  unfold hv
  ihave %e := ghost_var_agree γ0 _ _ _ _ $$ Hm H0
  obtain ⟨e1, e2, e3, e4⟩ := h0_inj e
  have hok' := h0_cnt hok e1.symm hful hM
  let g' : S4 := { g with p0 := 3, tc := ts, Dd := fun t => g.Dd t ∨ (pend M σ' t ∧ M[t - 1]? = some xMsg) }
  have hrp : g.rp = 0 := hok.rp_ok.2.1.2 (by omega)
  have eR : Rc (GF := GF) g = iprop(hv c (.r ⟨none, 0, 0, 0⟩) ∗ True) := by
    simp [Rc, ← e4, hrp, rec4, ← e1]
  have eR' : Rc (GF := GF) g' = iprop(hv c (.r ⟨none, 0, ts, 42⟩) ∗ True) := by
    simp [g', Rc, ← e4, hrp, rec4]
  rw [eR]
  icases Hr with ⟨Hr, -⟩
  unfold hv
  imod ghost_var_update_halves (MG4.r ⟨none, 0, ts, 42⟩) c _ _ $$ HR Hr with ⟨HR, Hr⟩
  imod ghost_var_update_halves (MG4.h0 3 ti ts (some c)) γ0 _ _ $$ Hm H0 with ⟨Hm, H0⟩
  imodintro
  isplitl [H0 H1 Hr]
  · iexists g'
    have eP0 : P0 g' = MG4.h0 3 ti ts (some c) := by simp [g', P0, ← e2, ← e4]
    have eP1 : P1 g' = P1 g := rfl
    rw [eP0, eP1, eR']
    unfold hv
    iframe; ipureintro; exact hok'
  iintro %s' %hs'
  have hv2 : ti ≤ (instrR (storeRun ws false (srcsView ws (srcR 11)) (max (srcsView ws (srcR 11))
      (srcsView ws (srcR 5))) (((s.rd 11 + 0) % two64 : Nat) : Int) (toBytes (s.rd 5) 8).length ts)).wVwOld ∧
      ts ≤ (instrR (storeRun ws false (srcsView ws (srcR 11)) (max (srcsView ws (srcR 11))
      (srcsView ws (srcR 5))) (((s.rd 11 + 0) % two64 : Nat) : Int) (toBytes (s.rd 5) 8).length ts)).wVwOld := by
    have := (storeBytes_keep ws (((s.rd 11 + 0) % two64 : Nat) : Int) (toBytes (s.rd 5) 8).length ts
      (max (srcsView ws (srcR 11)) (srcsView ws (srcR 5)))).2.1
    simp only [instrR, storeRun]; omega
  iapply (g0Fence M γ0 γ1 s' _ (hs.succ hs') (by rw [LPstep_rd hs' 12 (.inr rfl), h12])
    (by rw [LPstep_rd hs' 7 (.inr rfl), h7]) ti ts c hv2)
  unfold hv
  iframe

/-- **THE BIRTH STORE** `sw x0,0(x10)` (initlock, plain): THE LOCK IS BORN, and R's ghost name is ALLOCATED HERE
(at runtime). -/
theorem g0Init (s : LP) (ws : PState) (hs : HS h0Prog s 1) (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y)
    (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X) (h12 : s.rd 12 = Weak.Prom.Ref.Lit.Z) (h5 : s.rd 5 = 42)
    (h7 : s.rd 7 = 1) (a b : Nat) :
    hv (GF := GF) γ0 (.h0 1 a b none) ⊢ W0 M γ0 γ1 s ws := by
  iintro Hm
  iapply (wpT_sd (sz := 4) (rs2 := 0) (rs1 := 10) (off := 0) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [h10]; decide))
  inext
  iintro %σ %ts %σ' %hful %hmsg %_ %_ HX _
  have hM : M[ts - 1]? = some initMsg := by
    have := (take_msg hmsg).1
    have hb : (((s.rd 10 + 0) % two64 : Nat) : Int) = Weak.Prom.Own.MPL.Y := by rw [h10]; decide
    rw [hb] at this; exact this
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  unfold hv
  ihave %e := ghost_var_agree γ0 _ _ _ _ $$ Hm H0
  obtain ⟨e1, e2, e3, e4⟩ := h0_inj e
  -- THE RUNTIME ALLOCATION of R's ghost name
  imod ghost_var_alloc (GF := GF) (MG4.r ⟨none, 0, 0, 0⟩) with ⟨%c, Hc⟩
  have sp := ghost_var_split (GF := GF) c (MG4.r ⟨none, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at sp
  ihave ⟨Hc1, Hc2⟩ := sp $$ Hc
  have hok' := h0_init hok e1.symm hful hM c
  let g' : S4 := { g with p0 := 2, ti := ts, γ := some c,
                          Dd := fun t => g.Dd t ∨ (pend M σ' t ∧ M[t - 1]? = some initMsg) }
  have hrp : g.rp = 0 := hok.rp_ok.2.1.2 (by omega)
  have eR' : Rc (GF := GF) g' = iprop(hv c (.r ⟨none, 0, 0, 0⟩) ∗ True) := by
    simp [g', Rc, hrp, rec4]
  imod ghost_var_update_halves (MG4.h0 2 ts g.tc (some c)) γ0 _ _ $$ Hm H0 with ⟨Hm, H0⟩
  imodintro
  isplitl [H0 H1 Hc1]
  · iexists g'
    have eP0 : P0 g' = MG4.h0 2 ts g.tc (some c) := by simp [g', P0]
    have eP1 : P1 g' = P1 g := rfl
    rw [eP0, eP1, eR']
    unfold hv
    iframe; ipureintro; exact hok'
  iintro %s' %hs'
  have hv1 : ts ≤ (instrR (storeRun ws false (srcsView ws (srcR 10)) (max (srcsView ws (srcR 10))
      (srcsView ws (srcR 0))) (((s.rd 10 + 0) % two64 : Nat) : Int) (toBytes (s.rd 0) 4).length ts)).wVwOld := by
    simp only [instrR, storeRun]; omega
  iapply (g0Cnt M γ0 γ1 s' _ (hs.succ hs') (by rw [LPstep_rd hs' 11 (.inr rfl), h11])
    (by rw [LPstep_rd hs' 12 (.inr rfl), h12]) (by rw [LPstep_rd hs' 5 (.inr rfl), h5])
    (by rw [LPstep_rd hs' 7 (.inr rfl), h7]) ts g.tc c hv1)
  unfold hv
  iframe

/-- **THE JUNK STORE** `sw x6,0(x10)` (kalloc junk, H0's first write: in place). -/
theorem g0Junk (s : LP) (hs : HS h0Prog s 0) (h6 : s.rd 6 = 5) (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y)
    (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X) (h12 : s.rd 12 = Weak.Prom.Ref.Lit.Z) (h5 : s.rd 5 = 42)
    (h7 : s.rd 7 = 1) :
    hv (GF := GF) γ0 (.h0 0 0 0 none) ⊢ W0 M γ0 γ1 s psInit := by
  iintro Hm
  iapply (wpT_sd (sz := 4) (rs2 := 6) (rs1 := 10) (off := 0) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [h10]; decide))
  inext
  iintro %σ %ts %σ' %hful %hmsg %_ %_ HX _
  have hM : M[ts - 1]? = some junkMsg := by
    have := (take_msg hmsg).1
    have hb : (((s.rd 10 + 0) % two64 : Nat) : Int) = Weak.Prom.Own.MPL.Y := by rw [h10]; decide
    rw [hb, h6] at this; exact this
  have hrc := relClass_store0 (ws := psInit) rfl rfl false false (((s.rd 10 + 0) % two64 : Nat) : Int)
    (toBytes (s.rd 6) 4) (srcR 10) (srcR 6)
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  unfold hv
  ihave %e := ghost_var_agree γ0 _ _ _ _ $$ Hm H0
  obtain ⟨e1, e2, e3, e4⟩ := h0_inj e
  have hok' := h0_junk hok e1.symm hrc hful hM
  imod ghost_var_update_halves (MG4.h0 1 g.ti g.tc g.γ) γ0 _ _ $$ Hm H0 with ⟨Hm, H0⟩
  imodintro
  isplitl [H0 H1 Hr]
  · iexists { g with p0 := 1, tj := ts }
    have eP0 : P0 { g with p0 := 1, tj := ts } = MG4.h0 1 g.ti g.tc g.γ := rfl
    have eP1 : P1 { g with p0 := 1, tj := ts } = P1 g := rfl
    have eR : Rc (GF := GF) { g with p0 := 1, tj := ts } = Rc g := by simp [Rc, rec4, ← e1, ← e4]
    rw [eP0, eP1, eR]
    unfold hv
    iframe; ipureintro; exact hok'
  iintro %s' %hs'
  rw [← e4]
  iapply (g0Init M γ0 γ1 s' _ (hs.succ hs') (by rw [LPstep_rd hs' 10 (.inr rfl), h10])
    (by rw [LPstep_rd hs' 11 (.inr rfl), h11]) (by rw [LPstep_rd hs' 12 (.inr rfl), h12])
    (by rw [LPstep_rd hs' 5 (.inr rfl), h5]) (by rw [LPstep_rd hs' 7 (.inr rfl), h7]) g.ti g.tc)
  unfold hv
  iframe

end h0

/-! ## 4. H1, the user -/

theorem loadBytes_vwNew_ge (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    ws.wVwNew ≤ (loadBytes aq vpre ws a tvs).wVwNew
  | _, _, [] => Nat.le_refl _
  | ws, a, (t, _) :: r => by
    simp only [loadBytes]
    exact Nat.le_trans (by simp only [loadByte]; split <;> omega) (loadBytes_vwNew_ge aq vpre _ (a + 1) r)

section h1

variable [InvGS_gen hlc GF] (M : List PMsg) (γ0 γ1 : GName)

abbrev W1 (s : LP) (ws : PState) : IProp GF :=
  wpT (hlc := hlc) (X4 M γ0 γ1) lk4Img M 1 s ws (fun _ => iprop(True))

/-- H1's knowledge at its end. -/
def KG1 (x5 x6 x8 : Nat) : IProp GF :=
  iprop(∃ p a b bd, hv γ1 (.h1 p a b bd) ∗ ⌜bd = true ∨ x5 = 0 ∨ x6 ≠ 0 ∨ x8 = 42⌝)

theorem g1End (s : LP) (ws : PState) (hP : s.prog.length ≤ s.pc) (hq : s.q = []) :
    KG1 (GF := GF) γ1 (s.rd 5) (s.rd 6) (s.rd 8) ⊢ W1 (hlc := hlc) M γ0 γ1 s ws := by
  iintro H
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  unfold KG1
  icases H with ⟨%p, %a, %b, %bd, Hm, %hk⟩
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  unfold hv
  ihave %e := ghost_var_agree γ1 _ _ _ _ $$ Hm H1
  obtain ⟨_, _, _, e4⟩ := h1_inj e
  have hspec : spec4 s.regs ∨ g.bad = true := by
    rcases hk with h | h | h | h
    · exact .inr (hok.bd1 (by show g.bd1 = true; rw [← e4, h]))
    · left; intro h5; exact absurd (by rw [rd_regs s 5 (by omega)]; exact h) h5
    · left; intro _ h6; rw [rd_regs s 6 (by omega)] at h6; exact absurd h6 h
    · left; intro _ _; rw [rd_regs s 8 (by omega)]; exact h
  imodintro
  isplitl
  · iexists g; unfold hv; iframe; ipureintro; exact i4_fin (h := 1) hok (fun _ => hspec)
  · ipureintro; trivial

/-- Before the critical section's read: R taken (and the publication's `tf` below the floor), or `bad`. -/
def KR (ws : PState) : IProp GF :=
  iprop((∃ tf c x, hv γ1 (.h1 2 tf (some c) false) ∗ hv c (.r x) ∗ ⌜tf ≤ ws.wVrNew⌝) ∨
    (∃ p a b, hv γ1 (.h1 p a b true)))

theorem KR_congr {ws ws' : PState} (h : ws.wVrNew ≤ ws'.wVrNew) : KR (GF := GF) γ1 ws ⊢ KR γ1 ws' := by
  unfold KR
  iintro (⟨%tf, %c, %x, Hm, HR, %htf⟩ | H)
  · ileft; iexists tf, c, x; iframe; ipureintro; omega
  · iright; iexact H

/-- **THE CRITICAL SECTION'S READ** `ld x8,(x11)` (`h1_cread`): 42, or a dead message. -/
theorem g1Read (hinv : invalFree M) (s : LP) (ws : PState) (hs : HS h1Prog s 5)
    (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X) :
    KR (GF := GF) γ1 ws ⊢ W1 (hlc := hlc) M γ0 γ1 s ws := by
  iintro H
  iapply (wpT_ld (sz := 8) (sgn := true) (rd := 8) (rs1 := 11) (off := 0) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [h11]; decide))
  inext
  iintro %σ %tvs %hl8 %hlo HX _
  have hb : (((s.rd 11 + 0) % two64 : Nat) : Int) = Weak.Prom.Own.MPL.X := by rw [h11]; decide
  rw [hb] at hlo ⊢
  have hP : ws.wVrNew ≤ ldPre ws false false (srcsView ws (srcR 11)) := (PF.ldPre_ge ws false false _).2.1
  have cont : ∀ s3, LPstep s s3 (s.pc + 1) 8 (ldVal true 8 tvs) →
      KG1 (GF := GF) γ1 (s3.rd 5) (s3.rd 6) (s3.rd 8) ⊢ W1 (hlc := hlc) M γ0 γ1 s3
        (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) Weak.Prom.Own.MPL.X tvs)
          (regWL 8 [.DLdRes] ++ [LInstr])) := by
    intro s3 hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hs.prog (by rw [hs.pc])
    exact g1End M γ0 γ1 s3 _ (by rw [hP3, hc3]; decide) hq3
  have e8 : ∀ s3, LPstep s s3 (s.pc + 1) 8 (ldVal true 8 tvs) → s3.rd 8 = val8 tvs :=
    fun s3 hs3 => LPstep_rd_eq hs3 (by decide) (by rw [hs.len]; decide)
  unfold KR
  icases H with (⟨%tf, %c, %x, Hm, HR, %htf⟩ | ⟨%p, %a, %b, Hm⟩)
  · icases HX with ⟨%g, H0, H1, %hok, Hr⟩
    unfold hv
    ihave %e := ghost_var_agree γ1 _ _ _ _ $$ Hm H1
    obtain ⟨e1, e2, _, _⟩ := h1_inj e
    obtain ⟨hp0, ha1⟩ := hok.p1a (.inr e1.symm)
    have htc : g.tc < g.tf := (hok.h0f (by omega)).2.2.2.2
    have hPc : g.tc ≤ ldPre ws false false (srcsView ws (srcR 11)) := by
      have : g.tf = tf := by rw [← ha1, ← e2]
      omega
    by_cases hall : ∀ (j t : Nat) (b : BitVec 8), tvs[j]? = some (t, b) → (toBytes 42 8)[j]? = some b
    · have h42 : val8 tvs = 42 := val8_42 (map_snd_of (by rw [hl8]; rfl) (fun j _ t b htb => hall j t b htb))
      imodintro
      isplitl [H0 H1 Hr]
      · iexists g; unfold hv; iframe; ipureintro; exact hok
      iintro %s3 %hs3
      iapply (cont s3 hs3)
      unfold KG1 hv
      iexists 2, tf, some c, false; iframe Hm; ipureintro
      right; right; right; rw [e8 s3 hs3]; exact h42
    · obtain ⟨j, t, b, htb, hne⟩ : ∃ (j t : Nat) (b : BitVec 8), tvs[j]? = some (t, b) ∧ ¬ (toBytes 42 8)[j]? = some b := by
        refine Classical.byContradiction fun hno => hall fun j t b htb => ?_
        exact Classical.byContradiction fun h => hno ⟨j, t, b, htb, h⟩
      have hj : j < 8 := by have := (List.getElem?_eq_some_iff.1 htb).1; omega
      obtain ⟨hmb, htn, hnw⟩ := loadOk_byte (j := j) hinv hlo htb
      rcases h1_cread hok hp0 hPc hj hmb htn hnw with h | hd
      · exact absurd h hne
      have hok1 := i4_setBad hok hd
      imod ghost_var_update_halves (MG4.h1 2 tf (some c) true) γ1 _ _ $$ Hm H1 with ⟨Hm, H1⟩
      imodintro
      isplitl [H0 H1 Hr]
      · iexists { g with bad := true, bd1 := true }
        have eP1 : P1 { g with bad := true, bd1 := true } = MG4.h1 2 tf (some c) true := by
          simp [P1, ← e1, ← e2, ← (h1_inj e).2.2.1]
        have eP0 : P0 { g with bad := true, bd1 := true } = P0 g := rfl
        have eR : Rc (GF := GF) { g with bad := true, bd1 := true } = Rc g := by simp [Rc, rec4]
        rw [eP0, eP1, eR]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s3 %hs3
      iapply (cont s3 hs3)
      unfold KG1 hv
      iexists 2, tf, some c, true; iframe Hm; ipureintro; left; rfl
  · imodintro
    iframe HX
    iintro %s3 %hs3
    iapply (cont s3 hs3)
    unfold KG1 hv
    iexists p, a, b, true; iframe Hm; ipureintro; left; rfl

/-- After the acquire. -/
def KA (x6 : Nat) (ws : PState) : IProp GF :=
  iprop((⌜x6 ≠ 0⌝ ∗ ∃ p a b bd, hv γ1 (.h1 p a b bd)) ∨ KR γ1 ws)

/-- `bne x6,x0,END`. -/
theorem g1Bne (hinv : invalFree M) (s : LP) (ws : PState) (hs : HS h1Prog s 4)
    (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X) :
    KA (GF := GF) γ1 (s.rd 6) ws ⊢ W1 (hlc := hlc) M γ0 γ1 s ws := by
  iintro H
  iapply (wpT_br (c := .ne) (rs1 := 6) (rs2 := 0) (tgt := 6) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [hs.pc, hs.prog]; decide))
  iintro %s2 %hs2
  have h0 : s.rd 0 = 0 := rfl
  by_cases hx : s.rd 6 = 0
  · have hbr : Weak.Prom.Ref.brEval .ne (s.rd 6) (s.rd 0) = false := by rw [h0, hx]; rfl
    have hp2 : s2.pc = 5 := by rw [hs2.2.1, hbr, hs.pc]; rfl
    obtain ⟨hP2, _, hq2⟩ := LPstep_at hs2 hs.prog rfl
    iapply (g1Read M γ0 γ1 hinv s2 (instrR (PF.ctrlP ws (srcR 6 ++ srcR 0))) ⟨hP2, hp2, hq2, by rw [hs2.2.2.2.1, hs.len]⟩
      (by rw [LPstep_rd hs2 11 (.inr rfl), h11]))
    unfold KA
    icases H with (⟨%h, -⟩ | H)
    · exact absurd hx h
    · iapply (KR_congr γ1 (ws := ws) (ws' := instrR (PF.ctrlP ws (srcR 6 ++ srcR 0))) (Nat.le_refl _))
      iexact H
  · have hbr : Weak.Prom.Ref.brEval .ne (s.rd 6) (s.rd 0) = true := by simp [Weak.Prom.Ref.brEval, h0, hx]
    have hp2 : s2.pc = 6 := by rw [hs2.2.1, hbr]; rfl
    obtain ⟨hP2, _, hq2⟩ := LPstep_at hs2 hs.prog rfl
    have e6 : s2.rd 6 = s.rd 6 := LPstep_rd hs2 6 (.inr rfl)
    iapply (g1End M γ0 γ1 s2 _ (by rw [hP2, hp2]; decide) hq2)
    unfold KA KR KG1
    icases H with (⟨-, %p, %a, %b, %bd, Hm⟩ | (⟨%tf, %c, %x, Hm, -, -⟩ | ⟨%p, %a, %b, Hm⟩))
    · iexists p, a, b, bd; iframe Hm; ipureintro; right; right; left; rw [e6]; exact hx
    · iexists 2, tf, some c, false; iframe Hm; ipureintro; right; right; left; rw [e6]; exact hx
    · iexists p, a, b, true; iframe Hm; ipureintro; left; rfl

/-- Before the acquire. -/
def KF1 (ws : PState) : IProp GF :=
  iprop((∃ tf, hv γ1 (.h1 1 tf none false) ∗ ⌜tf ≤ ws.wVwNew ∧ tf ≤ ws.wVrNew⌝) ∨
    (∃ p a b, hv γ1 (.h1 p a b true) ∗ ⌜p ≤ 1⌝))

/-- **THE ACQUIRE** `amoswap.w.aq x6,x7,(x10)` (in place: `relClass_aq1`): it reads the born cell and TAKES R
(`h1_src`, `h1_take`), or not. -/
theorem g1Amo (hinv : invalFree M) (s : LP) (ws : PState) (hs : HS h1Prog s 3)
    (h7 : s.rd 7 = 1) (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (hw0 : ws.wVwOld = 0) (hrw : ws.wVrOld ≤ ws.wVwNew) :
    KF1 (GF := GF) γ1 ws ⊢ W1 (hlc := hlc) M γ0 γ1 s ws := by
  iintro H
  iapply (wpT_amo (op := .swap) (sz := 4) (aq := true) (rl := false) (rd := 6) (rs2 := 7) (rs1 := 10) hs.q
    (by rw [hs.prog, hs.pc]; rfl) (by rw [h10]; decide))
  inext
  iintro %σ %tvs %ts %σ' %hl4 %hful %hrmw HX _
  have hrc := relClass_aq1 ws false ((s.rd 10 : Nat) : Int) tvs (amoD .swap 4 (s.rd 7) tvs) (srcR 10) (srcR 7)
    hw0 hrw
  have hb : ((s.rd 10 : Nat) : Int) = Weak.Prom.Own.MPL.Y := by rw [h10]; rfl
  have hd : amoD .swap 4 (s.rd 7) tvs = toBytes 1 4 := by rw [PF.amoD_swap, h7]
  rw [hb, hd] at hrmw hful hrc
  rw [hb, hd]
  obtain ⟨_, hmsg, hlo, hex, hcoh, hext⟩ := hrmw
  have hM : M[ts - 1]? = some acq1 := (take_msg hmsg).1
  obtain ⟨⟨t0, b0⟩, rest, rfl⟩ : ∃ tb r, tvs = tb :: r := by
    cases tvs with
    | nil => simp at hl4
    | cons tb r => exact ⟨tb, r, rfl⟩
  have hl3 : rest.length = 3 := by simp at hl4; omega
  obtain ⟨hmb, ht0n, _⟩ := loadOk_byte (j := 0) hinv hlo rfl
  have hmb' : memByte lk4Img M t0 Weak.Prom.Own.MPL.Y = some b0 := by simpa using hmb
  have htsn := (take_msg hmsg).2
  have hwin : ∀ t, t0 < t → t < ts → wrL M t → au M t = some 1 := by
    intro t h1 h2 hw
    obtain ⟨m, hm, hbm⟩ := hw
    have hex0 : ¬ writesInBy (M.take σ'.n) (fun tid => tid ≠ some 1) Weak.Prom.Own.MPL.Y t0 (ts - 1) := hex.1
    have hau : au M t = m.tid := by simp [au, hm]
    rw [hau]
    exact Classical.byContradiction fun hne => hex0 ⟨t, h1, by omega, m,
      by rw [List.getElem?_take, if_pos (by omega)]; exact hm, hbm, hne⟩
  have hvw : ws.wVwNew < ts := by
    have h1 : ws.wVwNew ≤ (loadRun ws true false (srcsView ws (srcR 10)) Weak.Prom.Own.MPL.Y ((t0, b0) :: rest)).wVwNew :=
      loadBytes_vwNew_ge true (ldPre ws true false (srcsView ws (srcR 10))) ws Weak.Prom.Own.MPL.Y ((t0, b0) :: rest)
    have h2 : (loadRun ws true false (srcsView ws (srcR 10)) Weak.Prom.Own.MPL.Y ((t0, b0) :: rest)).wVwNew ≤
        stPre (loadRun ws true false (srcsView ws (srcR 10)) Weak.Prom.Own.MPL.Y ((t0, b0) :: rest)) false
          (srcsView ws (srcR 10)) (srcsView ws (srcR 7)) := by
      unfold stPre; omega
    omega
  have hts : ts = σ.n + 1 := by
    rcases hful with ⟨hnr, _, _⟩ | ⟨_, _, _, ets, _⟩
    · exact absurd hrc hnr
    · exact ets
  have ht0 : t0 < ts := by
    have h1 := (PF.loadRun_b0 ws true false (srcsView ws (srcR 10)) Weak.Prom.Own.MPL.Y t0 b0 rest).2.2.2.1
    have h2 := PF.cohBelow_b0 hcoh (by simp [toBytes, Weak.Prom.Ref.byteList])
    omega
  have ht0n' : t0 ≤ σ.n := by omega
  let ws1 := PF.qPosts (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 10)) Weak.Prom.Own.MPL.Y
    ((t0, b0) :: rest)) false (srcsView ws (srcR 10)) ts Weak.Prom.Own.MPL.Y (toBytes 1 4).length ts) true ts)
    (regWL 6 [.DLdRes] ++ [LInstr])
  have hv1 : ts ≤ ws1.wVrNew := by
    show ts ≤ (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 10)) Weak.Prom.Own.MPL.Y
      ((t0, b0) :: rest)) false (srcsView ws (srcR 10)) ts Weak.Prom.Own.MPL.Y (toBytes 1 4).length ts) true ts).wVrNew
    simp only [amoPost, if_true]; omega
  have cont : ∀ s', LPstep s s' (s.pc + 1) 6 (Weak.Prom.Ref.sext 4 (ofBytes (((t0, b0) :: rest).map Prod.snd))) →
      KA (GF := GF) γ1 (s'.rd 6) ws1 ⊢ W1 (hlc := hlc) M γ0 γ1 s' ws1 := by
    intro s' hs'
    exact g1Bne M γ0 γ1 hinv s' ws1 (hs.succ hs') (by rw [LPstep_rd hs' 11 (.inl (by decide)), h11])
  have hx6 : ∀ s', LPstep s s' (s.pc + 1) 6 (Weak.Prom.Ref.sext 4 (ofBytes (((t0, b0) :: rest).map Prod.snd))) →
      b0 ≠ 0 → s'.rd 6 ≠ 0 := by
    intro s' hs' hb0 h0
    rw [LPstep_rd_eq hs' (by decide) (by rw [hs.len]; decide)] at h0
    exact hb0 (amo_x5 hl3 h0)
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  unfold KF1 hv
  icases H with (⟨%tf, Hm, %htf⟩ | ⟨%p, %a, %b, Hm, %hp⟩)
  · ihave %e := ghost_var_agree γ1 _ _ _ _ $$ Hm H1
    obtain ⟨e1, e2, e3, e4⟩ := h1_inj e
    obtain ⟨hp0, ha1⟩ := hok.p1a (.inl e1.symm)
    have htf' : g.tf < ts := by rw [← ha1, ← e2]; omega
    by_cases hb0 : b0 = 0
    · rcases h1_src hok lk4Img_zero e1.symm htf' hmb' ht0n' hb0 hwin with hti | hd
      · -- THE TAKE: R moves from the born cell to H1
        obtain ⟨hok', hrp⟩ := h1_take hok e1.symm hrc hful hM
        obtain ⟨c, hc⟩ : ∃ c, g.γ = some c := by
          cases h : g.γ with
          | none => have := hok.γ_ok.1 h; omega
          | some c => exact ⟨c, rfl⟩
        have eR : Rc (GF := GF) g = iprop(hv c (.r (rec4 g)) ∗ hv c (.r (rec4 g))) := by simp [Rc, hc, hrp]
        have eR' : Rc (GF := GF) { g with p1 := 2, ta := ts, rp := 2, b1 := g.γ } =
            iprop(hv c (.r (rec4 g)) ∗ True) := by simp [Rc, hc, rec4]
        have eP1 : P1 { g with p1 := 2, ta := ts, rp := 2, b1 := g.γ } = MG4.h1 2 tf (some c) false := by
          simp [P1, hc, ← e2, ← e4]
        rw [eR]
        icases Hr with ⟨Hr, HRt⟩
        imod ghost_var_update_halves (MG4.h1 2 tf (some c) false) γ1 _ _ $$ Hm H1 with ⟨Hm, H1⟩
        imodintro
        isplitl [H0 H1 Hr]
        · iexists { g with p1 := 2, ta := ts, rp := 2, b1 := g.γ }
          have eP0 : P0 { g with p1 := 2, ta := ts, rp := 2, b1 := g.γ } = P0 g := rfl
          rw [eP0, eP1, eR']
          unfold hv
          iframe; ipureintro; exact hok'
        iintro %s' %hs'
        iapply (cont s' hs')
        unfold KA KR hv
        by_cases hz : s'.rd 6 = 0
        · iright; ileft; iexists tf, c, rec4 g; iframe Hm HRt; ipureintro; omega
        · ileft; isplitr
          · ipureintro; exact hz
          · iexists 2, tf, some c, false; iexact Hm
      · -- a dead source: `bad`
        have hok1 := h1_fail (i4_setBad hok hd) (by simp; omega) hrc hful hM
        imod ghost_var_update_halves (MG4.h1 3 tf none true) γ1 _ _ $$ Hm H1 with ⟨Hm, H1⟩
        imodintro
        isplitl [H0 H1 Hr]
        · iexists { ({ g with bad := true, bd1 := true } : S4) with p1 := 3, ta := ts }
          have eP1 : P1 { ({ g with bad := true, bd1 := true } : S4) with p1 := 3, ta := ts } =
              MG4.h1 3 tf none true := by simp [P1, ← e2, ← e3]
          have eP0 : P0 { ({ g with bad := true, bd1 := true } : S4) with p1 := 3, ta := ts } = P0 g := rfl
          have eR : Rc (GF := GF) { ({ g with bad := true, bd1 := true } : S4) with p1 := 3, ta := ts } = Rc g := by
            simp [Rc, rec4]
          rw [eP0, eP1, eR]
          unfold hv
          iframe; ipureintro; exact hok1
        iintro %s' %hs'
        iapply (cont s' hs')
        unfold KA KR hv
        by_cases hz : s'.rd 6 = 0
        · iright; iright; iexists 3, tf, none; iexact Hm
        · ileft; isplitr
          · ipureintro; exact hz
          · iexists 3, tf, none, true; iexact Hm
    · -- a nonzero answer: R not taken
      have hok1 := h1_fail hok (by omega) hrc hful hM
      imod ghost_var_update_halves (MG4.h1 3 tf none false) γ1 _ _ $$ Hm H1 with ⟨Hm, H1⟩
      imodintro
      isplitl [H0 H1 Hr]
      · iexists { g with p1 := 3, ta := ts }
        have eP1 : P1 { g with p1 := 3, ta := ts } = MG4.h1 3 tf none false := by simp [P1, ← e2, ← e3, ← e4]
        have eP0 : P0 { g with p1 := 3, ta := ts } = P0 g := rfl
        have eR : Rc (GF := GF) { g with p1 := 3, ta := ts } = Rc g := by simp [Rc, rec4]
        rw [eP0, eP1, eR]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s' %hs'
      iapply (cont s' hs')
      unfold KA hv
      ileft; isplitr
      · ipureintro; exact hx6 s' hs' hb0
      · iexists 3, tf, none, false; iexact Hm
  · -- `bad` already
    ihave %e := ghost_var_agree γ1 _ _ _ _ $$ Hm H1
    obtain ⟨e1, e2, e3, e4⟩ := h1_inj e
    have hok1 := h1_fail hok (by omega) hrc hful hM
    imod ghost_var_update_halves (MG4.h1 3 a b true) γ1 _ _ $$ Hm H1 with ⟨Hm, H1⟩
    imodintro
    isplitl [H0 H1 Hr]
    · iexists { g with p1 := 3, ta := ts }
      have eP1 : P1 { g with p1 := 3, ta := ts } = MG4.h1 3 a b true := by simp [P1, ← e2, ← e3, ← e4]
      have eP0 : P0 { g with p1 := 3, ta := ts } = P0 g := rfl
      have eR : Rc (GF := GF) { g with p1 := 3, ta := ts } = Rc g := by simp [Rc, rec4]
      rw [eP0, eP1, eR]
      unfold hv
      iframe; ipureintro; exact hok1
    iintro %s' %hs'
    iapply (cont s' hs')
    unfold KA KR hv
    by_cases hz : s'.rd 6 = 0
    · iright; iright; iexists 3, a, b; iexact Hm
    · ileft; isplitr
      · ipureintro; exact hz
      · iexists 3, a, b, true; iexact Hm

/-- After the flag read and `fence r,rw`. -/
def KF2 (x5 : Nat) (ws : PState) : IProp GF :=
  iprop((⌜x5 = 0⌝ ∗ hv γ1 (.h1 0 0 none false)) ∨ KF1 γ1 ws)

theorem KF1_congr {ws ws' : PState} (h1 : ws.wVwNew ≤ ws'.wVwNew) (h2 : ws.wVrNew ≤ ws'.wVrNew) :
    KF1 (GF := GF) γ1 ws ⊢ KF1 γ1 ws' := by
  unfold KF1
  iintro (⟨%tf, Hm, %htf⟩ | H)
  · ileft; iexists tf; iframe; ipureintro; omega
  · iright; iexact H

/-- `beq x5,x0,END` (the publication not seen: give up). -/
theorem g1Beq (hinv : invalFree M) (s : LP) (ws : PState) (hs : HS h1Prog s 2) (h7 : s.rd 7 = 1)
    (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (hw0 : ws.wVwOld = 0) (hrw : ws.wVrOld ≤ ws.wVwNew) :
    KF2 (GF := GF) γ1 (s.rd 5) ws ⊢ W1 (hlc := hlc) M γ0 γ1 s ws := by
  iintro H
  iapply (wpT_br (c := .eq) (rs1 := 5) (rs2 := 0) (tgt := 6) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [hs.pc, hs.prog]; decide))
  iintro %s2 %hs2
  have h0 : s.rd 0 = 0 := rfl
  have e5 : s2.rd 5 = s.rd 5 := LPstep_rd hs2 5 (.inr rfl)
  by_cases hx : s.rd 5 = 0
  · have hbr : Weak.Prom.Ref.brEval .eq (s.rd 5) (s.rd 0) = true := by rw [h0, hx]; rfl
    have hp2 : s2.pc = 6 := by rw [hs2.2.1, hbr]; rfl
    obtain ⟨hP2, _, hq2⟩ := LPstep_at hs2 hs.prog rfl
    iapply (g1End M γ0 γ1 s2 _ (by rw [hP2, hp2]; decide) hq2)
    unfold KF2 KF1 KG1
    icases H with (⟨-, Hm⟩ | (⟨%tf, Hm, -⟩ | ⟨%p, %a, %b, Hm, -⟩))
    · iexists 0, 0, none, false; iframe Hm; ipureintro; right; left; rw [e5]; exact hx
    · iexists 1, tf, none, false; iframe Hm; ipureintro; right; left; rw [e5]; exact hx
    · iexists p, a, b, true; iframe Hm; ipureintro; left; rfl
  · have hbr : Weak.Prom.Ref.brEval .eq (s.rd 5) (s.rd 0) = false := by simp [Weak.Prom.Ref.brEval, h0, hx]
    have hp2 : s2.pc = 3 := by rw [hs2.2.1, hbr, hs.pc]; rfl
    obtain ⟨hP2, _, hq2⟩ := LPstep_at hs2 hs.prog rfl
    iapply (g1Amo M γ0 γ1 hinv s2 (instrR (PF.ctrlP ws (srcR 5 ++ srcR 0))) ⟨hP2, hp2, hq2, by rw [hs2.2.2.2.1, hs.len]⟩
      (by rw [LPstep_rd hs2 7 (.inr rfl), h7]) (by rw [LPstep_rd hs2 10 (.inr rfl), h10])
      (by rw [LPstep_rd hs2 11 (.inr rfl), h11]) hw0 hrw)
    unfold KF2
    icases H with (⟨%h, -⟩ | H)
    · exact absurd h hx
    · iapply (KF1_congr γ1 (ws := ws) (ws' := instrR (PF.ctrlP ws (srcR 5 ++ srcR 0))) (Nat.le_refl _)
        (Nat.le_refl _))
      iexact H

/-- After the flag read. -/
def KF0 (x5 : Nat) (ws : PState) : IProp GF :=
  iprop((⌜x5 = 0⌝ ∗ hv γ1 (.h1 0 0 none false)) ∨ (∃ tf, hv γ1 (.h1 1 tf none false) ∗ ⌜tf ≤ ws.wVrOld⌝) ∨
    (∃ p a b, hv γ1 (.h1 p a b true) ∗ ⌜p ≤ 1⌝))

/-- `fence r,rw`. -/
theorem g1Fence (hinv : invalFree M) (s : LP) (ws : PState) (hs : HS h1Prog s 1) (h7 : s.rd 7 = 1)
    (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X) (hw0 : ws.wVwOld = 0) :
    KF0 (GF := GF) γ1 (s.rd 5) ws ⊢ W1 (hlc := hlc) M γ0 γ1 s ws := by
  iintro H
  iapply (wpT_fence (f := ⟨true, false, false, false, true, true, false, false⟩) hs.q (by rw [hs.prog, hs.pc]; rfl))
  iintro %s' %hs'
  have e5 : s'.rd 5 = s.rd 5 := LPstep_rd hs' 5 (.inr rfl)
  iapply (g1Beq M γ0 γ1 hinv s' (instrR (fencePost ws true false true true)) (hs.succ hs')
    (by rw [LPstep_rd hs' 7 (.inr rfl), h7])
    (by rw [LPstep_rd hs' 10 (.inr rfl), h10]) (by rw [LPstep_rd hs' 11 (.inr rfl), h11]) hw0
    (by simp only [instrR, fencePost, if_true, if_false]; omega))
  unfold KF0 KF2 KF1
  rw [e5]
  icases H with (H | (⟨%tf, Hm, %htf⟩ | ⟨%p, %a, %b, Hm, %hp⟩))
  · ileft; iexact H
  · iright; ileft; iexists tf; iframe Hm; ipureintro
    simp only [instrR, fencePost, if_true, if_false]; omega
  · iright; iright; iexists p, a, b; iframe Hm; ipureintro; exact hp

/-- **THE FLAG READ** `ld x5,(x12)` (`h1_flag`): the publication (deposited), or a dead message. -/
theorem g1Flag (hinv : invalFree M) (s : LP) (hs : HS h1Prog s 0) (h7 : s.rd 7 = 1)
    (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (h12 : s.rd 12 = Weak.Prom.Ref.Lit.Z) :
    hv (GF := GF) γ1 (.h1 0 0 none false) ⊢ W1 (hlc := hlc) M γ0 γ1 s psInit := by
  iintro Hm
  iapply (wpT_ld (sz := 8) (sgn := true) (rd := 5) (rs1 := 12) (off := 0) hs.q (by rw [hs.prog, hs.pc]; rfl)
    (by rw [h12]; decide))
  inext
  iintro %σ %tvs %hl8 %hlo HX _
  have hb : (((s.rd 12 + 0) % two64 : Nat) : Int) = F := by rw [h12]; decide
  rw [hb] at hlo ⊢
  let ws1 := PF.qPosts (loadRun psInit false false (srcsView psInit (srcR 12)) F tvs) (regWL 5 [.DLdRes] ++ [LInstr])
  have hw1 : ws1.wVwOld = 0 := (loadRun_keep psInit false false (srcsView psInit (srcR 12)) F tvs).2.1
  have cont : ∀ s3, LPstep s s3 (s.pc + 1) 5 (ldVal true 8 tvs) →
      KF0 (GF := GF) γ1 (s3.rd 5) ws1 ⊢ W1 (hlc := hlc) M γ0 γ1 s3 ws1 := by
    intro s3 hs3
    exact g1Fence M γ0 γ1 hinv s3 ws1 (hs.succ hs3) (by rw [LPstep_rd hs3 7 (.inl (by decide)), h7])
      (by rw [LPstep_rd hs3 10 (.inl (by decide)), h10]) (by rw [LPstep_rd hs3 11 (.inl (by decide)), h11]) hw1
  have e5 : ∀ s3, LPstep s s3 (s.pc + 1) 5 (ldVal true 8 tvs) → s3.rd 5 = val8 tvs :=
    fun s3 hs3 => LPstep_rd_eq hs3 (by decide) (by rw [hs.len]; decide)
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  unfold hv
  ihave %e := ghost_var_agree γ1 _ _ _ _ $$ Hm H1
  obtain ⟨e1, e2, e3, e4⟩ := h1_inj e
  by_cases hz : val8 tvs = 0
  · imodintro
    isplitl [H0 H1 Hr]
    · iexists g; unfold hv; iframe; ipureintro; exact hok
    iintro %s3 %hs3
    iapply (cont s3 hs3)
    unfold KF0 hv
    ileft; isplitr
    · ipureintro; rw [e5 s3 hs3]; exact hz
    · iexact Hm
  · obtain ⟨j, t, b, htb, hb0⟩ : ∃ (j t : Nat) (b : BitVec 8), tvs[j]? = some (t, b) ∧ b ≠ 0 := by
      refine Classical.byContradiction fun hno => hz (ofBytes8_of_zero hl8 fun j t b htb => ?_)
      exact Classical.byContradiction fun h => hno ⟨j, t, b, htb, h⟩
    have hj : j < 8 := by have := (List.getElem?_eq_some_iff.1 htb).1; omega
    obtain ⟨hmb, htn, _⟩ := loadOk_byte (j := j) hinv hlo htb
    have hvr : t ≤ ws1.wVrOld := by
      have h1 := bytesAll_get (loadRun_keep psInit false false (srcsView psInit (srcR 12)) F tvs).2.2.2.2 j htb
      rw [fwdView_psInit] at h1
      exact h1
    rcases h1_flag hok lk4Img_zero hj hmb htn hb0 with ⟨hp0, rfl⟩ | hd
    · have hok1 := h1_saw hok e1.symm hp0
      imod ghost_var_update_halves (MG4.h1 1 g.tf none false) γ1 _ _ $$ Hm H1 with ⟨Hm, H1⟩
      imodintro
      isplitl [H0 H1 Hr]
      · iexists { g with p1 := 1, a1 := g.tf }
        have eP1 : P1 { g with p1 := 1, a1 := g.tf } = MG4.h1 1 g.tf none false := by simp [P1, ← e3, ← e4]
        have eP0 : P0 { g with p1 := 1, a1 := g.tf } = P0 g := rfl
        have eR : Rc (GF := GF) { g with p1 := 1, a1 := g.tf } = Rc g := by simp [Rc, rec4]
        rw [eP0, eP1, eR]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s3 %hs3
      iapply (cont s3 hs3)
      unfold KF0 hv
      iright; ileft; iexists g.tf; iframe Hm; ipureintro; exact hvr
    · have hok1 := i4_setBad hok hd
      imod ghost_var_update_halves (MG4.h1 0 0 none true) γ1 _ _ $$ Hm H1 with ⟨Hm, H1⟩
      imodintro
      isplitl [H0 H1 Hr]
      · iexists { g with bad := true, bd1 := true }
        have eP1 : P1 { g with bad := true, bd1 := true } = MG4.h1 0 0 none true := by
          simp [P1, ← e1, ← e2, ← e3]
        have eP0 : P0 { g with bad := true, bd1 := true } = P0 g := rfl
        have eR : Rc (GF := GF) { g with bad := true, bd1 := true } = Rc g := by simp [Rc, rec4]
        rw [eP0, eP1, eR]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s3 %hs3
      iapply (cont s3 hs3)
      unfold KF0 hv
      iright; iright; iexists 0, 0, none; iframe Hm; ipureintro; omega

end h1

/-! ## 5. The agent, the end, the verdict -/

section top

variable [InvGS_gen hlc GF] (M : List PMsg) (γ0 γ1 : GName)

/-- THE PROMISE AGENT (plan §4 "its wp is the invariant"): candidates kept, everything else dead. -/
theorem i4_agentI :
    ⊢ □ (∀ σ σ', ⌜agentStep (litOW lk4Img M) σ σ'⌝ -∗ X4 (GF := GF) M γ0 γ1 σ -∗ |={⊤}=> X4 M γ0 γ1 σ') := by
  imodintro
  iintro %σ %σ' %ha HX
  icases HX with ⟨%g, H0, H1, %hok, Hr⟩
  obtain ⟨g', hok', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := i4_agent hok ha
  have eP0 : P0 g' = P0 g := by simp [P0, e1, e2, e3, e4]
  have eP1 : P1 g' = P1 g := by simp [P1, e6, e7, e8, e9]
  have eR : Rc (GF := GF) g' = Rc g := by simp [Rc, rec4, e1, e3, e4, e5]
  imodintro
  iexists g'
  rw [eP0, eP1, eR]
  iframe; ipureintro; exact hok'

theorem i4_finalI :
    ⊢ ∀ σ, ⌜σ.n = (litOW lk4Img M).M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ X4 (GF := GF) M γ0 γ1 σ -∗
      |={⊤,∅}=> ⌜∀ r1, σ.done 1 = some r1 → spec4 r1⌝ := by
  iintro %σ %hfin HX
  icases HX with ⟨%g, -, -, %hok, -⟩
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact i4_final hok hfin.2

end top

def q40 : LP := ⟨h0Prog, 0, (List.range 32).map (fun r => ((h0Regs.lookup r).getD 0) % two64), []⟩
def q41 : LP := ⟨h1Prog, 0, (List.range 32).map (fun r => ((h1Regs.lookup r).getD 0) % two64), []⟩

theorem progs_lk4T : progs lk4T = [q40, q41] := rfl

/-- **G4 TARGET (4) ON TRACK (b): A LOCK BORN BY A PLAIN STORE OVER JUNK, PUBLISHED, ITS RESOURCE DEPOSITED LATE
AND NAMED AT RUNTIME** (the pipealloc shape; header of OwnLock4Defs.lean).  In every valid machine-v2 run of `lk4T`,
if the user H1 saw the publication (x5 ≠ 0) and acquired the born lock (x6 = 0), its critical section read the
allocator's 42 (x8 = 42). -/
theorem g4_lockBirth {evs : List PEvt} {cfg : PCfg LP Unit} (hvr : validRun litStep lk4Img () (progs lk4T) evs cfg)
    {r1 : List Nat} (h1 : doneOf (litOW lk4Img cfg.pcLog) (progs lk4T).length cfg 1 = some r1) : spec4 r1 := by
  have hps : ∀ p ∈ progs lk4T, p.q = [] := by
    rw [progs_lk4T]; intro p hp; simp at hp; rcases hp with rfl | rfl <;> rfl
  have hinv := lit_invalFree hvr hps
  have key := ownAdequacy (hlc := HasLC.hasLC) (GF := lk4GF) (w := litOW lk4Img cfg.pcLog) (ps := progs lk4T)
    (fun done => ∀ r1, done 1 = some r1 → spec4 r1) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG4.h0 0 0 0 none) with ⟨%γ0, H0⟩
      imod ghost_var_alloc (MG4.h1 0 0 none false) with ⟨%γ1, H1⟩
      have s1 := ghost_var_split (GF := lk4GF) γ0 (MG4.h0 0 0 0 none) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := lk4GF) γ1 (MG4.h1 0 0 none false) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2
      ihave ⟨H01, H02⟩ := s1 $$ H0
      ihave ⟨H11, H12⟩ := s2 $$ H1
      imodintro
      iexists X4 cfg.pcLog γ0 γ1
      isplitl [H01 H11]
      · iexists g0
        have e0 : P0 g0 = MG4.h0 0 0 0 none := rfl
        have e1 : P1 g0 = MG4.h1 0 0 none false := rfl
        have eR : Rc (GF := lk4GF) g0 = iprop(True) := rfl
        rw [e0, e1, eR]
        unfold hv
        iframe
        ipureintro; exact ⟨i4_init, trivial⟩
      isplitr
      · iapply i4_agentI
      isplitl [H02 H12]
      · rw [progs_lk4T]
        simp only [hartsFrom]
        iapply BigSepL.bigSepL_cons.2
        isplitl [H02]
        · ihave H := g0Junk (hlc := HasLC.hasLC) cfg.pcLog γ0 γ1 q40 ⟨rfl, rfl, rfl, by decide⟩ (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) $$ [H02]
          · unfold hv; iexact H02
          iapply H
        iapply BigSepL.bigSepL_cons.2
        isplitl [H12]
        · ihave H := g1Flag (hlc := HasLC.hasLC) cfg.pcLog γ0 γ1 hinv q41 ⟨rfl, rfl, rfl, by decide⟩ (by decide)
            (by decide) (by decide) (by decide) $$ [H12]
          · unfold hv; iexact H12
          iapply H
        exact BigSepL.bigSepL_nil_intro
      · iapply i4_finalI) hvr rfl (lit_fetchBounded hvr hps) hinv
  exact key r1 h1

/-- **G4 (4), on the final configuration.** -/
theorem g4_lockBirth_regs {evs : List PEvt} {cfg : PCfg LP Unit}
    (hvr : validRun litStep lk4Img () (progs lk4T) evs cfg) {a1 : PAgent LP} (ha1 : cfg.pcAgs[1]? = some a1)
    (hd1 : a1.paSt.q = [] ∧ a1.paSt.prog.length ≤ a1.paSt.pc) :
    a1.paSt.rd 5 ≠ 0 → a1.paSt.rd 6 = 0 → a1.paSt.rd 8 = 42 := by
  have h := g4_lockBirth hvr (r1 := a1.paSt.regs)
    (by simp only [doneOf, show (1 : Nat) < (progs lk4T).length by rw [progs_lk4T]; decide, if_true, ha1,
      Option.bind_some]; exact litDoneR_end hd1.1 hd1.2)
  unfold spec4 at h
  rw [rd_regs _ 5 (by omega), rd_regs _ 6 (by omega), rd_regs _ 8 (by omega)] at h
  exact h

end Weak.Prom.Own.L4
