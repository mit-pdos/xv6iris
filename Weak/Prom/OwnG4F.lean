/-
Weak/Prom: **E-b — G4 verdicts re-derived from the fetch-premise-free adequacy** (G4 deciding experiment E-b, owner
ruling [OWN.P11]; G4-review.md §6).  `g4_lock1cF` (G4 (1c)+(3), xv6's exact acquire/release text, OwnLock1c.lean
`g4_lock1c`) and `g4_mpOwnLF` (G4 (2), OwnMPL.lean `g4_mpOwnL`): the SAME statements, the SAME client proofs (state
interpretation, agent obligation, hart wps, final extraction — now over the language with the prophecy-fed fetch
constructor `hstepO.fetch`, OwnLang.lean [E-b]), through `ownAdequacyF` (OwnWpF.lean), which takes NO
`fetchBounded` premise (the per-program discharges `x_fetchBounded` / `lit_fetchBounded` are no longer used).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnWpF
import Weak.Prom.OwnLock1c
import Weak.Prom.OwnMPL

namespace Weak.Prom.Own.X.L1c

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Nfr (invalFree relClass)
open Weak.Prom.Own (OSt OW fulO litOW litDoneR litDoneR_end take_msg upd upd_eq upd_ne agentStep doneOf σ0
  hartsFrom ownAdequacy ownAdequacyF)
open Weak.Prom.OA (XI xOf xStep addiwV)
open Weak.Prom.Own.Lk (MG hv Pg Rbox lkGF xr_inj pr_inj Pg_other upd_other Rg lkImg lkImg_zero C Lw LSt LkS
  cohBelow_get loadRun_coh_j val8_small)
open Weak.Prom.Own.Lk1c
open Weak.Prom.Own.MP (wrA au wrA_of_memByte)
open Weak.Prom.Own.MPL (XRec loadOk_byte val8 rd_regs relClass_fW wrX)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq ldVal instrR amoD)
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode


/-- [E-b] RE-DERIVED FROM `ownAdequacyF` (no (P2)).  **G4 TARGETS (1c) AND (3) ON TRACK (b): XV6'S EXACT ACQUIRE/RELEASE TEXT** (`li a4,1; again: mv a5,a4;
amoswap.w.aq a5,a5,(s1); sext.w a5,a5; bnez a5,again; sd a0,16(s1)` … `sd zero,16(s1); fence rw,w; sw zero,0(s1)`,
with release's `holding()` read `lw a3,0(s1); beqz a3,panic` inlined) around a counter (`ld; addi; sd`).  In every
valid machine-v2 run of `lk1cT` (loop front end), if both harts finished, their final x7 (counter value + 1) differ
— mutual exclusion — and both `holding()` reads returned nonzero (x13 ≠ 0: `panic` is never reached). -/
theorem g4_lock1cF {evs : List PEvt} {cfg : PCfg LP Unit}
    (hvr : validRun (xStep lk1cXs) (testImg lk1cT) () (progs lk1cT) evs cfg)
    {r0 r1 : List Nat} (h0 : doneOf (xOW lk1cXs lkImg cfg.pcLog) (progs lk1cT).length cfg 0 = some r0)
    (h1 : doneOf (xOW lk1cXs lkImg cfg.pcLog) (progs lk1cT).length cfg 1 = some r1) : lkSpec r0 r1 := by
  rw [lk1cImg] at hvr
  have hps : ∀ p ∈ progs lk1cT, p.q = [] := by
    rw [progs_lk1cT]; intro p hp; simp at hp; rcases hp with rfl | rfl <;> rfl
  have hinv := x_invalFree hvr hps
  have key := ownAdequacyF (hlc := HasLC.hasLC) (GF := lkGF) (w := xOW lk1cXs lkImg cfg.pcLog) (ps := progs lk1cT)
    (fun done => ∀ r0 r1, done 0 = some r0 → done 1 = some r1 → lkSpec r0 r1) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG.xr ⟨none, 0, 0, 0⟩) with ⟨%γc, Hc⟩
      imod ghost_var_alloc (MG.pr 0 none none) with ⟨%γ0, H0⟩
      imod ghost_var_alloc (MG.pr 0 none none) with ⟨%γ1, H1⟩
      have s1 := ghost_var_split (GF := lkGF) γc (MG.xr ⟨none, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := lkGF) γ0 (MG.pr 0 none none) (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := lkGF) γ1 (MG.pr 0 none none) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨Hc1, Hc2⟩ := s1 $$ Hc
      ihave ⟨H01, H02⟩ := s2 $$ H0
      ihave ⟨H11, H12⟩ := s3 $$ H1
      imodintro
      iexists Xl cfg.pcLog γc γ0 γ1
      isplitl [Hc1 Hc2 H01 H11]
      · iexists g0
        have eR : Rbox (GF := lkGF) γc g0.spoil g0.ls g0.cr = hv γc (.xr ⟨none, 0, 0, 0⟩) := rfl
        have ec : (g0.cr : XRec) = ⟨none, 0, 0, 0⟩ := rfl
        have ep : ∀ j, Pg g0 j = MG.pr 0 none none := fun _ => rfl
        rw [eR, ep 0, ep 1, ec]
        unfold hv
        iframe
        ipureintro; exact lk_init (M := cfg.pcLog) lkImg_zero
      isplitr
      · iapply lk_agentI
      isplitl [H02 H12]
      · rw [progs_lk1cT]
        simp only [hartsFrom]
        iapply BigSepL.bigSepL_cons.2
        isplitl [H02]
        · ihave H := hStart (hlc := HasLC.hasLC) cfg.pcLog γc γ0 γ1 0 1 (Xl cfg.pcLog γc γ0 γ1) hinv
            (fun σ => ⟨.rfl, .rfl⟩) (by decide) (by decide) (q1c 1)
            ⟨rfl, rfl, rfl, by decide, by decide, by decide⟩ $$ [H02]
          · unfold hv; iexact H02
          iapply H
        iapply BigSepL.bigSepL_cons.2
        isplitl [H12]
        · ihave H := hStart (hlc := HasLC.hasLC) cfg.pcLog γc γ1 γ0 1 0 (Xl cfg.pcLog γc γ0 γ1) hinv
            (fun σ => ⟨(Xl_swap cfg.pcLog γc γ0 γ1 σ).1, (Xl_swap cfg.pcLog γc γ0 γ1 σ).2⟩) (by decide) (by decide)
            (q1c 2) ⟨rfl, rfl, rfl, by decide, by decide, by decide⟩ $$ [H12]
          · unfold hv; iexact H12
          iapply H
        exact BigSepL.bigSepL_nil_intro
      · iapply lk_finalI) hvr rfl   -- [E-b] `ownAdequacyF`: no fetch-boundedness premise
  exact key r0 r1 h0 h1

end Weak.Prom.Own.X.L1c

namespace Weak.Prom.Own.MPL

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au wrA_of_memByte)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq ldVal instrR)
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- [E-b] RE-DERIVED FROM `ownAdequacyF` (no (P2)).  **G4 TARGET (2) ON TRACK (b), REAL FRONT END.**  In every valid machine-v2 run of `mpT` (litmus program half,
8-byte accesses, the test's image), if H1 finished with registers `g`, then `g[5] = 1 → g[7] = 42`.  Proved in
track (b)'s logic: x's points-to moves from H0 to H1 through flag's in-place release (header). -/
theorem g4_mpOwnLF {evs : List PEvt} {cfg : PCfg LP Unit} (hvr : validRun litStep mpImg () (progs mpT) evs cfg)
    {g : List Nat} (hg : doneOf (litOW mpImg cfg.pcLog) (progs mpT).length cfg 1 = some g) : mpSpec g := by
  have hps : ∀ p ∈ progs mpT, p.q = [] := by
    rw [progs_mpT]; intro p hp; simp at hp; rcases hp with rfl | rfl <;> rfl
  have hinv := lit_invalFree hvr hps
  have key := ownAdequacyF (hlc := HasLC.hasLC) (GF := mplGF) (w := litOW mpImg cfg.pcLog) (ps := progs mpT)
    (fun done => ∀ g, done 1 = some g → mpSpec g) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG.xr ⟨some 0, 0, 0, 0⟩) with ⟨%γx, Hx⟩
      imod ghost_var_alloc (MG.fl none) with ⟨%γf, Hf⟩
      imod ghost_var_alloc (MG.bd false) with ⟨%γb, Hb⟩
      imod token_alloc with ⟨%γc, Htok⟩
      have s1 := ghost_var_split (GF := mplGF) γx (MG.xr ⟨some 0, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := mplGF) γf (MG.fl none) (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := mplGF) γb (MG.bd false) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨Hx1, Hx2⟩ := s1 $$ Hx
      ihave ⟨Hf1, Hf2⟩ := s2 $$ Hf
      ihave ⟨Hb1, Hb2⟩ := s3 $$ Hb
      imodintro
      iexists Xm cfg.pcLog γx γf γb γc
      isplitl [Hx1 Hf1 Hb1]
      · iexists (fun _ => False), ⟨some 0, 0, 0, 0⟩, none, false
        unfold hv depP
        iframe Hx1 Hf1 Hb1
        ipureintro; exact ⟨mpOk_init mpImg_zero, trivial⟩
      isplitr
      · iapply mp_agent
      isplitl [Hx2 Hf2 Hb2 Htok]
      · rw [progs_mpT]
        simp only [hartsFrom]
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hx2 Hf2]
        · ihave H := mp_h0 (hlc := HasLC.hasLC) cfg.pcLog γx γf γb γc p0 rfl rfl rfl (by decide) (by decide)
            (by decide) (by decide) $$ [Hx2 Hf2]
          · unfold hv; iframe Hx2 Hf2
          iapply H
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hb2 Htok]
        · ihave H := mp_h1 (hlc := HasLC.hasLC) cfg.pcLog γx γf γb γc hinv p1 rfl rfl rfl (by decide) (by decide)
            (by decide) $$ [Hb2 Htok]
          · unfold hv; iframe Hb2 Htok
          iapply H
        exact BigSepL.bigSepL_nil_intro
      · iapply mp_final) hvr rfl   -- [E-b] `ownAdequacyF`: no fetch-boundedness premise
  exact key g hg

end Weak.Prom.Own.MPL
