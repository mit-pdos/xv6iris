/-
MachCSL: **the cycle's execute tail, up to discarded reads** (lane U3-Lsc,
over lane AND-ELIM's walker form `URunSc`, MachCSL/SailAndElim).

UCycleSwp's `swp_ucAfterFetch_base`/`_rvc` take the execute stretch as a
plain walk of the model's eager `uxaExecAs i`.  The execute classification is
stated up to discarded reads (`URunSc`: some short-circuit form of
`uxaExecAs i` walks), because the backend's eager `&&` in `check_CSR` reads
cells outside the user footprint.  This file pushes such a fact through the
tail:

* `ucAfterFetchX ex fr` -- `ucAfterFetch` with the execute program a
  parameter (`ucAfterFetchX uxaExecAs = ucAfterFetch`, by `rfl`), and its
  `SailStut` congruence `ucAfterFetchX_stut`;
* `uc_afterFetchX_base`/`_rvc` -- UCycle's tail walks, for any execute
  program;
* `uc_afterFetchSc_base`/`_rvc` -- the tail up to discards, from an execute
  fact up to discards (the short-circuit tail is the tail with the execute
  program replaced at the decoded instruction);
* `swp_ucWalkSc` (`swp_URunSc` with the landing named by a function of the
  oracle) and `swp_ucAfterFetchSc_base`/`_rvc`, the `URunSc` twins of
  `swp_ucAfterFetch_base`/`_rvc`.
-/
import MachCSL.UCycleSwp
import MachCSL.SailAndElim

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Register HartState Step ExecutionResult FetchResult ExceptionType

/-- `ucAfterFetch` with the execute program a parameter (the text of
`ucAfterFetch`, `uxaExecAs` abstracted). -/
noncomputable def ucAfterFetchX (ex : instruction → SailM ExecutionResult) (fr : FetchResult) :
    SailM Step := do
  match (ext_fetch_hook fr) with
  | .F_Ext_Error e => (pure (Step_Ext_Fetch_Failure e))
  | .F_Error (e, addr) => (pure (Step_Fetch_Failure ((virtaddr.Virtaddr addr), e)))
  | .F_RVC h =>
    (do
      let instbits : instbits := (zero_extend (m := 32) h)
      let instruction ← do (ext_decode_compressed h)
      if ((← (is_landing_pad_expected ())) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          (pure (Step_Execute (r, instbits))))
      else
        (do
          if ((← (currentlyEnabled extension.Ext_Zca)) : Bool)
          then
            (do
              writeReg nextPC (BitVec.addInt (← readReg PC) 2)
              let result ← ex instruction
              (pure (Step_Execute (result, instbits))))
          else (pure (Step_Execute ((Illegal_Instruction ()), instbits)))))
  | .F_Base w =>
    (do
      let instbits : instbits := (zero_extend (m := 32) w)
      let instruction ← do (ext_decode w)
      if (((← (is_landing_pad_expected ())) && (Functions.not (is_lpad_instruction instruction))) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          (pure (Step_Execute (r, instbits))))
      else
        (do
          writeReg nextPC (BitVec.addInt (← readReg PC) 4)
          let result ← ex instruction
          (pure (Step_Execute (result, instbits)))))

theorem ucAfterFetchX_uxa (fr : FetchResult) : ucAfterFetchX uxaExecAs fr = ucAfterFetch fr := rfl

/-- **Congruence**: discarded reads in the execute program are discarded
reads of the tail. -/
theorem ucAfterFetchX_stut {ex₀ ex : instruction → SailM ExecutionResult}
    (h : ∀ j, SailStut (ex₀ j) (ex j)) (fr : FetchResult) :
    SailStut (ucAfterFetchX ex₀ fr) (ucAfterFetchX ex fr) := by
  unfold ucAfterFetchX
  generalize ext_fetch_hook fr = fr'
  cases fr' with
  | F_Ext_Error e => exact .refl _
  | F_Error p => obtain ⟨e, a⟩ := p; exact .refl _
  | F_RVC hw =>
    refine SailStut.bind_right _ fun ins => SailStut.bind_right _ fun b => ?_
    refine SailStut.ite (fun _ => .refl _) (fun _ => SailStut.bind_right _ fun z => ?_)
    refine SailStut.ite (fun _ => SailStut.bind_right _ fun pc => SailStut.bind_right _ fun _ => ?_)
      (fun _ => .refl _)
    exact SailStut.bind (h ins) fun _ => .refl _
  | F_Base w =>
    refine SailStut.bind_right _ fun ins => SailStut.bind_right _ fun b => ?_
    refine SailStut.ite (fun _ => .refl _) (fun _ => SailStut.bind_right _ fun pc => SailStut.bind_right _ fun _ => ?_)
    exact SailStut.bind (h ins) fun _ => .refl _

variable {D : UFoot}

/-- **The base tail, any execute program** (UCycle's `uc_afterFetch_base`). -/
theorem uc_afterFetchX_base (hD : UcFoot D) (ex : instruction → SailM ExecutionResult) (orc orc2 : UOrc)
    (s s2 : UWSt) (w : BitVec 32) (i : instruction) (r : ExecutionResult) (hrd : D.Dr .elp = true)
    (hv : s.file .elp = 0#1) (hdec : runRW D orc s (ext_decode w) = some (i, s, orc))
    (hex : runRW D orc (ucNpcS s 4) (ex i) = some (r, s2, orc2)) :
    runRW D orc s (ucAfterFetchX ex (F_Base w)) =
      some (Step_Execute (r, zero_extend (m := 32) w), s2, orc2) := by
  simp only [ucAfterFetchX, ext_fetch_hook]
  rw [runRW_bind_some D _ _ orc orc s s i hdec, uc_lpad orc s hrd hv]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, ucRW_readReg D _ _ _ _ hD.rd_pc,
    ucRW_writeReg D _ _ _ _ _ hD.wr_npc]
  exact runRW_bind_some D _ _ orc orc2 _ s2 r hex

/-- **The compressed tail, any execute program** (UCycle's
`uc_afterFetch_rvc`). -/
theorem uc_afterFetchX_rvc (hD : UcFoot D) (ex : instruction → SailM ExecutionResult) (orc orc2 : UOrc)
    (s s2 : UWSt) (h : BitVec 16) (i : instruction) (r : ExecutionResult) (hrd : D.Dr .elp = true)
    (hv : s.file .elp = 0#1) (hm : UcMisa D s)
    (hdec : runRW D orc s (ext_decode_compressed h) = some (i, s, orc))
    (hex : runRW D orc (ucNpcS s 2) (ex i) = some (r, s2, orc2)) :
    runRW D orc s (ucAfterFetchX ex (F_RVC h)) =
      some (Step_Execute (r, zero_extend (m := 32) h), s2, orc2) := by
  simp only [ucAfterFetchX, ext_fetch_hook]
  rw [runRW_bind_some D _ _ orc orc s s i hdec, uc_lpad orc s hrd hv]
  simp only [Bool.false_eq_true, if_false, uc_currentlyEnabled_Zca hm, if_true,
    ucRW_readReg D _ _ _ _ hD.rd_pc, ucRW_writeReg D _ _ _ _ _ hD.wr_npc]
  exact runRW_bind_some D _ _ orc orc2 _ s2 r hex

/-- The execute program with a short-circuit form spliced in at `i`. -/
theorem ucAfterFetchX_splice {i : instruction} {e₀ : SailM ExecutionResult} (hS : SailStut e₀ (uxaExecAs i))
    [DecidableEq instruction] (fr : FetchResult) :
    SailStut (ucAfterFetchX (fun j => if j = i then e₀ else uxaExecAs j) fr) (ucAfterFetch fr) := by
  rw [← ucAfterFetchX_uxa]
  refine ucAfterFetchX_stut (fun j => ?_) fr
  by_cases hj : j = i
  · subst hj; rw [if_pos rfl]; exact hS
  · rw [if_neg hj]; exact .refl _

/-- **The base tail, up to discards.** -/
theorem uc_afterFetchSc_base (hD : UcFoot D) (s : UWSt) (w : BitVec 32) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1)
    (hdec : ∀ orc, runRW D orc s (ext_decode w) = some (i, s, orc))
    (E : UOrc → ExecutionResult × UWSt × UOrc)
    (hex : URunSc D (ucNpcS s 4) (uxaExecAs i) (fun orc => some (E orc))) :
    URunSc D s (ucAfterFetch (F_Base w))
      (fun orc => some (Step_Execute ((E orc).1, zero_extend (m := 32) w), (E orc).2.1, (E orc).2.2)) := by
  classical
  obtain ⟨e₀, hS, hw⟩ := hex
  refine URunSc.of_stut (ucAfterFetchX_splice hS _) fun orc => ?_
  refine uc_afterFetchX_base hD _ orc (E orc).2.2 s (E orc).2.1 w i (E orc).1 hrd hv (hdec orc) ?_
  rw [if_pos rfl]
  exact hw orc

/-- **The compressed tail, up to discards.** -/
theorem uc_afterFetchSc_rvc (hD : UcFoot D) (s : UWSt) (h : BitVec 16) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1) (hm : UcMisa D s)
    (hdec : ∀ orc, runRW D orc s (ext_decode_compressed h) = some (i, s, orc))
    (E : UOrc → ExecutionResult × UWSt × UOrc)
    (hex : URunSc D (ucNpcS s 2) (uxaExecAs i) (fun orc => some (E orc))) :
    URunSc D s (ucAfterFetch (F_RVC h))
      (fun orc => some (Step_Execute ((E orc).1, zero_extend (m := 32) h), (E orc).2.1, (E orc).2.2)) := by
  classical
  obtain ⟨e₀, hS, hw⟩ := hex
  refine URunSc.of_stut (ucAfterFetchX_splice hS _) fun orc => ?_
  refine uc_afterFetchX_rvc hD _ orc (E orc).2.2 s (E orc).2.1 h i (E orc).1 hrd hv hm (hdec orc) ?_
  rw [if_pos rfl]
  exact hw orc

section swp
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {cpu : CPU} {ξ : CtxId} (RF : URegFrame GF cpu D) (BF : UByteFrame GF ξ)

/-- **A walk up to discards, as `swp`** (`swp_URunSc` with the landing named
by a function of the oracle; UCycleSwp's `swp_ucWalk`). -/
theorem swp_ucWalkSc {X : Type} (m : SailM X) (s : UWSt) (L : UOrc → X × UWSt × UOrc)
    (hw : URunSc D s m (fun orc => some (L orc))) (Φ : X → IProp GF) :
    uFr RF BF s ∗ (∀ orc, uFr RF BF (L orc).2.1 -∗ Φ (L orc).1) ⊢ swp cpu m Φ := by
  iintro ⟨Hfr, HΦ⟩
  iapply swp_URunSc RF BF hw (fun _ => rfl) Φ
  iframe Hfr
  iintro %orc %x %s' %orc' %h HF HB Hc Hr
  ispecialize HΦ $$ %orc
  generalize L orc = t at h ⊢
  obtain ⟨x0, s0, o0⟩ := t
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, -⟩ := h
  iapply HΦ
  unfold uFr
  iframe

/-- **A fetched word's tail, execute up to discards** (`swp_ucAfterFetch_base`'s
twin). -/
theorem swp_ucAfterFetchSc_base (hD : UcFoot D) (s : UWSt) (w : BitVec 32) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1)
    (hdec : ∀ orc, runRW D orc s (ext_decode w) = some (i, s, orc))
    (E : UOrc → ExecutionResult × UWSt × UOrc)
    (hex : URunSc D (ucNpcS s 4) (uxaExecAs i) (fun orc => some (E orc))) (Ψ : Step → IProp GF) :
    uFr RF BF s ∗ (∀ orc, uFr RF BF (E orc).2.1 -∗ Ψ (Step_Execute ((E orc).1, zero_extend (m := 32) w)))
    ⊢ swp cpu (ucAfterFetch (F_Base w)) Ψ :=
  swp_ucWalkSc RF BF _ s (fun orc => (Step_Execute ((E orc).1, zero_extend (m := 32) w), (E orc).2.1, (E orc).2.2))
    (uc_afterFetchSc_base hD s w i hrd hv hdec E hex) Ψ

/-- **A fetched halfword's tail, execute up to discards**
(`swp_ucAfterFetch_rvc`'s twin). -/
theorem swp_ucAfterFetchSc_rvc (hD : UcFoot D) (s : UWSt) (h : BitVec 16) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1) (hm : UcMisa D s)
    (hdec : ∀ orc, runRW D orc s (ext_decode_compressed h) = some (i, s, orc))
    (E : UOrc → ExecutionResult × UWSt × UOrc)
    (hex : URunSc D (ucNpcS s 2) (uxaExecAs i) (fun orc => some (E orc))) (Ψ : Step → IProp GF) :
    uFr RF BF s ∗ (∀ orc, uFr RF BF (E orc).2.1 -∗ Ψ (Step_Execute ((E orc).1, zero_extend (m := 32) h)))
    ⊢ swp cpu (ucAfterFetch (F_RVC h)) Ψ :=
  swp_ucWalkSc RF BF _ s (fun orc => (Step_Execute ((E orc).1, zero_extend (m := 32) h), (E orc).2.1, (E orc).2.2))
    (uc_afterFetchSc_rvc hD s h i hrd hv hm hdec E hex) Ψ

end swp

end MachCSL
