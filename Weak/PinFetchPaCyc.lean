/-
Weak: **r2 glue (C) — THE FETCH-ADDRESS CYCLE: `cyFB` over the whole of `riscvStep`**
(`PROGRESS-r2glue.md`).  Lean-only.

`cyFSailOf`: every cycle `riscvStep tick` started with an empty fetch log, no announce, `PC = pc`
and every register `tvRk c`-admitted (the fetch translation's filter) satisfies `cyFB` with the
obligation `kAa pc` — whatever word is fetched and executed:
* the prelude and the interrupt dispatch keep `PC`, `satp`, `tlb` (w1's `pf` × our `xf`);
* the fetch is `cyFFetch` (its reads at `pc`, `pc + 2`);
* everything else — a parked hart's wait, an interrupt's or a fetch fault's trap, the announce's
  decode, the landing-pad check, `execute` of ANY instruction (`fpExecNotFI`; `fence.i`'s one
  barrier by hand), `ucFinish`, `tick_clock` — makes no instruction-fetch read (W-SCO's `fp`).
Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaCyF
import Weak.PinCycRunCyc
import Weak.SailCycleOrderStretch
import Weak.SailCycleOrderAllExec
import Weak.SailCycleOrderAllDecode

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinCycRun PinDataflow
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)

/-! ## 1. The pre-fetch stretches keep `PC`, `satp`, `tlb` -/

set_option maxHeartbeats 40000000 in
theorem pfPreludeT : pfT ucPrelude := by
  unfold ucPrelude
  pf_walk

set_option maxHeartbeats 40000000 in
theorem xfPreludeT : PinFetchPaFp.xfT ucPrelude := by
  unfold ucPrelude
  xf_walk

set_option maxHeartbeats 40000000 in
theorem pfDispatchT : pfT ucDispatch := by
  unfold ucDispatch
  pf_walk

set_option maxHeartbeats 40000000 in
theorem xfDispatchT : PinFetchPaFp.xfT ucDispatch := by
  unfold ucDispatch
  xf_walk

/-- A register file kept at `satp`/`tlb` from a `tvRk c`-admitted one, `Rboot`-admitted, is
`tvRk c`-admitted. -/
theorem tvRkAllKeep (c : TCfg) (rv rv' : RegFile) (h : tvRkAll c rv) (hrb : RbootAll rv')
    (hk : ∀ r, PinFetchPaFp.xfProt r = true → rv' r = rv r) : tvRkAll c rv' := by
  intro r
  refine ⟨hrb r, ?_, ?_⟩
  · intro e
    subst e
    rw [hk .satp (by decide)]; exact (h .satp).2.1 rfl
  · intro e
    subst e
    rw [hk .tlb (by decide)]; exact (h .tlb).2.2 rfl

theorem fpKeepTrans (s1 s2 s3 : CySt) (h1 : fpKeep s1 s2) (h2 : fpKeep s2 s3) : fpKeep s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2⟩

/-! ## 2. The no-fetch stretches -/

section nofetch
variable {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop} {Aa : Nat → Int → Prop}

/-- `execute` of ANY instruction makes no fetch read. -/
theorem cyFExec (i : instruction) (st : CySt) (hrb : RbootAll st.rv) :
    cyFB D Aa (fun _ st' => fpKeep st st') (execute i) st := by
  cases h : SailCycleOrderFp.isFI i
  · exact cyFMono _ _ (fun _ _ h => h.2) _ _ (cyFOfFp _ _ st (SailCycleOrderFp.fpExecNotFI i h) hrb)
  · obtain ⟨p, rfl⟩ : ∃ p, i = .FENCEI p := by
      cases i <;> first | exact ⟨_, rfl⟩ | (exfalso; revert h; simp only [SailCycleOrderFp.isFI]; decide)
    obtain ⟨imm, rs, rd⟩ := p
    simp only [execute, execute_FENCEI, PreSail.sail_barrier, PreSail.emit, bind_assoc, pure_bind]
    exact fun _ => ⟨rfl, rfl, hrb⟩

/-- `uxaExecAs`: `execute` and its one redirect. -/
theorem cyFExecAs (i : instruction) (st : CySt) (hrb : RbootAll st.rv) :
    cyFB D Aa (fun _ st' => fpKeep st st') (uxaExecAs i) st := by
  unfold uxaExecAs
  refine cyFBind _ _ _ _ st (cyFExec i st hrb) (fun r st' h => ?_)
  cases r with
  | ExecuteAs j => exact cyFMono _ _ (fun _ s h' => fpKeepTrans _ _ _ h h') _ _ (cyFExec j st' h.2.2)
  | _ => exact h

/-- `ucFinish`, then the optional tick. -/
theorem cyFFinish (s : Step) (tick : Bool) (st : CySt) (hrb : RbootAll st.rv) :
    cyFB D Aa (fun _ _ => True) (ucFinish s >>= fun _ => if tick then tick_clock () else pure ()) st := by
  refine cyFFpBind _ _ _ _ st (SailCycleOrderFp.fpFinish s) hrb (fun _ st' _ hk => ?_)
  split
  · exact cyFMono _ _ (fun _ _ _ => trivial) _ _ (cyFOfFp _ _ st' SailCycleOrderFp.fpTickClock hk.2.2)
  · exact trivial

end nofetch

/-! ## 3. The cycle -/

set_option maxHeartbeats 40000000 in
theorem fpLpadExpected : SailCycleOrderFp.fpT (is_landing_pad_expected ()) := by
  unfold is_landing_pad_expected
  fp_walk

set_option maxHeartbeats 40000000 in
theorem fpTrapLpad : SailCycleOrderFp.fpT (trap (make_landing_pad_exception ())) := by
  fp_walk

set_option maxHeartbeats 40000000 in
/-- **THE FETCH-ADDRESS CYCLE** (header). -/
theorem cyFSailOf (c : TCfg) (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (pc : Int)
    (h0 : 0 ≤ pc) (hlt : pc + 2 < 2 ^ 64) (c1 c2 : TCfg)
    (hc1 : fqCfg c D (BitVec.ofInt 64 pc) c1) (hc2 : fqCfg c D (BitVec.addInt (BitVec.ofInt 64 pc) 2) c2)
    (tick : Bool) (st : CySt) (hfe : st.fe = []) (han : st.an = false)
    (hpc : st.rv .PC = BitVec.ofInt 64 pc) (hall : tvRkAll c st.rv) :
    cyFB D (kAa pc) (fun _ _ => True) (riscvStep tick) st := by
  have hrb : RbootAll st.rv := fun r => (hall r).1
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  refine cyFBind _ _ _ _ st (cyFOfPfXf _ _ ucPrelude st pfPreludeT xfPreludeT hrb) (fun hs st1 h1 => ?_)
  have hk1 := h1.2
  cases hs with
  | HART_WAITING p =>
    obtain ⟨wr, ib⟩ := p
    simp only [ucBody]
    exact cyFFpBind _ _ _ _ st1 (SailCycleOrderFp.fpWaiting wr ib) hk1.1.2.2
      (fun s st2 _ hk2 => cyFFinish s tick st2 hk2.2.2)
  | HART_ACTIVE u =>
    simp only [ucBody]
    rw [uc_runHartActive_eq]
    simp only [bind_assoc]
    refine cyFBind _ _ _ _ st1 (cyFOfPfXf _ _ ucDispatch st1 pfDispatchT xfDispatchT hk1.1.2.2)
      (fun o st2 h2 => ?_)
    have hk2 := pxKeepTrans _ _ _ hk1 h2.2
    cases o with
    | some ip =>
      simp only [pure_bind]
      exact cyFFinish _ tick st2 hk2.1.2.2
    | none =>
      simp only [bind_assoc]
      have hfe2 : st2.fe = [] := hk2.1.1.trans hfe
      have hpc2 : st2.rv .PC = BitVec.ofInt 64 pc := (hk2.2 .PC (Or.inl rfl)).trans hpc
      have hall2 : tvRkAll c st2.rv :=
        tvRkAllKeep c st.rv st2.rv hall hk2.1.2.2 (fun r hr => hk2.2 r (Or.inr hr))
      refine cyFBind _ _ _ _ st2 (cyFFetch c D pc h0 hlt c1 c2 hc1 hc2 st2 hfe2 hpc2 hall2)
        (fun fr st3 h3 => ?_)
      obtain ⟨hok, -, han3, hrb3⟩ := h3
      have han3' : st3.an = false := han3.trans (hk2.1.2.1.trans han)
      cases fr with
      | F_Ext_Error e => exact hok.elim
      | F_Error p =>
        obtain ⟨e, addr⟩ := p
        simp only [ucAfterFetch, ext_fetch_hook, pure_bind]
        exact cyFFinish _ tick st3 hrb3
      | F_RVC h =>
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        refine cyFAnnBind _ h _ st3 han3' ?_
        refine cyFFpBind _ _ _ _ _ (SailCycleOrderFp.fpDecodeC h) hrb3 (fun i st5 _ hk5 => ?_)
        refine cyFFpBind _ _ _ _ _ fpLpadExpected hk5.2.2 (fun b st6 _ hk6 => ?_)
        refine cyFBind (fun _ st' => RbootAll st'.rv) _ _ _ st6 ?_ (fun s st7 h7 => cyFFinish s tick st7 h7)
        split
        · exact cyFFpBind _ _ _ _ _ fpTrapLpad hk6.2.2 (fun r st7 _ hk7 => hk7.2.2)
        · refine cyFFpBind _ _ _ _ _ (SailCycleOrderFp.fpCurrentlyEnabled _) hk6.2.2 (fun z st7 _ hk7 => ?_)
          split
          · refine cyFReadBind _ _ _ _ (fun v _ => ?_)
            refine cyFWriteBind _ _ _ _ _ trivial ?_
            exact cyFBind _ _ _ _ _ (cyFExecAs i _ (rbootAllSet _ _ _ hk7.2.2 trivial)) (fun r st8 h8 => h8.2.2)
          · exact hk7.2.2
      | F_Base w =>
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        refine cyFAnnBind _ w _ st3 han3' ?_
        refine cyFFpBind _ _ _ _ _ (SailCycleOrderFp.fpDecodeS w) hrb3 (fun i st5 _ hk5 => ?_)
        refine cyFFpBind _ _ _ _ _ fpLpadExpected hk5.2.2 (fun b st6 _ hk6 => ?_)
        refine cyFBind (fun _ st' => RbootAll st'.rv) _ _ _ st6 ?_ (fun s st7 h7 => cyFFinish s tick st7 h7)
        split
        · exact cyFFpBind _ _ _ _ _ fpTrapLpad hk6.2.2 (fun r st7 _ hk7 => hk7.2.2)
        · refine cyFReadBind _ _ _ _ (fun v _ => ?_)
          refine cyFWriteBind _ _ _ _ _ trivial ?_
          exact cyFBind _ _ _ _ _ (cyFExecAs i _ (rbootAllSet _ _ _ hk6.2.2 trivial)) (fun r st8 h8 => h8.2.2)

end PinFetchPa
end Weak
