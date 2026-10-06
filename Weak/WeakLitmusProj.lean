/-
Weak: **the litmus machine projects into the axiomatic LTS** (M6 W4,
"Projection lemmas").

Rocq: `iris/WeakLitmusProj.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: `WeakLitmus` is the tiny executable
hart-program machine (`Instr`, `Hart`, `Config`, `lstep`); `WeakAxiomatic` is
the canonical promise-free event-labelled LTS (`Mstate`/`mstep`, executions as
(state list, step list) pairs).  This file is the projection

    every `rtc lstep` run of the litmus machine from an initial configuration
    projects to an `execWf` execution of `WeakAxiomatic` with the same image,
    the same log and per-hart `Wstate`s that agree but for the control view.

It is `WeakPromiseBridge` one machine over, simplified:

- the litmus machine has NO silent arm, so the projection is total: one
  `lstep` is exactly one `mstep` (no stuttering, no `Option` in the step
  lemma);
- every litmus access is SINGLE-BYTE, so the four arms hit `mstep`'s
  run-shaped post-states at singleton lists.  Those collapse to `WeakMem`'s
  `loadPost` / `storePost` UP TO A RAISED CONTROL VIEW (`accAddr base 0 =
  base + 0`).  The control view is W-TV's consumption: a RUN-level access joins
  the entry state's translation bank into `wVcap` and the per-byte functions do
  not.  Hence `lcfgMatch` relates the per-hart `Wstate`s by `wsCtrlUp` ("equal
  but for a raised `wVcap`") rather than by equality.  Nothing on either side
  reads `wVcap`, so the slack is invisible to every side condition, and the
  projection theorem's payload (same image, same log) is untouched;
- the AMO's atomicity side condition in `lstep` IS `WeakMem.latest` unfolded,
  so `mstep`'s `rmwLatest` premise is immediate.

The state projection `lcfgMatch` is RELATIONAL (an `Mstate`'s `msWs` is a
function, a `Config`'s harts a list).  DELTAS from the W4 spec: (i) no
`Option` alternative in the step lemma (no `lstep` arm stutters); (ii) the
initial-configuration premise is `∀ h ∈ harts0, h.hWs = wsInit` over
`⟨img, [], harts0⟩`, the shape `WeakLitmus`'s litmus configurations have;
`lstepExecWfSb` checks that the theorem applies to them verbatim.

DEPENDENCY-FREE like its inputs: `WeakMem`, `WeakLitmus`, `WeakAxiomatic`
(+ `WeakAxiomatic2` for `execNil`/`execSnoc`, which the Lean port placed
there).

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.
2. VOCABULARY: as `WeakMem` deviation 2; `Forall P l` ↦ `∀ x ∈ l, P x`;
   `Cfg img log harts` ↦ `⟨img, log, harts⟩`; `MSt img log ws` ↦
   `⟨img, log, ws⟩`; `EStep i l` ↦ `⟨i, l⟩`; `Hart p r w` ↦ `⟨p, r, w⟩`.
3. IMPORT: Rocq imports `WeakAxiomatic` only; the Lean `execNil`/`execSnoc`
   live in `Weak/WeakAxiomatic2.lean`, so that file is imported too.
4. `lbridgeRun` is proved by `rtc_ind_l` (stdpp's head induction) with the
   execution generalised, as Rocq's `induction 1` on the head-style `rtc`.
5. Lean-only helper (no Rocq twin): `accAddrZero` (`accAddr a 0 = a`, Rocq's
   `rewrite /acc_addr Z.add_0_r`).

**Name map** (Rocq → Lean): `rd_ok_single` ↦ `rdOkSingle`,
`rd_ok_single_ctrl_up` ↦ `rdOkSingleCtrlUp`, `rmw_latest_single` ↦
`rmwLatestSingle`, `lcfg_match` ↦ `lcfgMatch`, `lproj_ws` ↦ `lprojWs`,
`lproj_st` ↦ `lprojSt`, `lcfg_match_proj` ↦ `lcfgMatchProj`,
`lcfg_match_log` ↦ `lcfgMatchLog`, `lcfg_match_upd_gen` ↦ `lcfgMatchUpdGen`,
`lstep_mstep` ↦ `lstepMstep`, `lbridge_step` ↦ `lbridgeStep`, `lbridge_run` ↦
`lbridgeRun`, `lstep_exec_wf` ↦ `lstepExecWf`, `lstep_exec_log` ↦
`lstepExecLog`, `lstep_exec_wf_sb` ↦ `lstepExecWfSb`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakAxiomatic2
import Weak.WeakLitmus

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! ## Singleton instances of the two read side conditions -/

theorem accAddrZero (a : Int) : accAddr a 0 = a := by simp [accAddr]

theorem rdOkSingle (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (a : Int) (t : Nat)
    (v : BitVec 8) :
    logByte img log t a = some v →
    readable img log ws (loadVpre ws aq) a t →
    rdOk img log ws aq a [t] [v] := by
  intro hb hr
  refine ⟨rfl, ?_⟩
  intro j t' v' ht hv
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hv
    subst ht hv
    rw [accAddrZero]
    exact ⟨hb, hr⟩
  | succ j => simp at ht

/-- The instance the arms below meet: the `Mstate`'s agent is the hart's state
with a RAISED CONTROL VIEW, and `readable` — hence `rdOk` — reads only `coh`
and `loadVpre`, neither of which sees `wVcap`. -/
theorem rdOkSingleCtrlUp (img : Image) (log : List Wmsg) (w1 w2 : Wstate) (aq : Bool) (a : Int)
    (t : Nat) (v : BitVec 8) :
    wsCtrlUp w1 w2 →
    logByte img log t a = some v →
    readable img log w1 (loadVpre w1 aq) a t →
    rdOk img log w2 aq a [t] [v] := by
  rintro ⟨x, rfl⟩ hb hr
  exact rdOkSingle img log (ctrlPost w1 x) aq a t v hb hr

/-- `WeakLitmus`'s AMO arm carries exactly `WeakMem.latest` unfolded. -/
theorem rmwLatestSingle (img : Image) (log : List Wmsg) (a : Int) (t : Nat) :
    (logByte img log t a).isSome →
    ¬ writesIn log a t log.length →
    rmwLatest img log a [t] := by
  intro hs hn j t' ht
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
    subst ht
    rw [accAddrZero]
    exact ⟨hs, hn⟩
  | succ j => simp at ht

/-! ## The state projection -/

/-- Same image, same log, and the `Mstate`'s view function agrees with the
hart list (up to a raised control view) where the latter is defined. -/
def lcfgMatch (c : Config) (σ : Mstate) : Prop :=
  σ.msImg = c.cImg ∧ σ.msLog = c.cLog ∧
  ∀ (i : Nat) (h : Hart), c.cHarts[i]? = some h → wsCtrlUp h.hWs (σ.msWs i)

/-- The functional projection, for consumers who want one: it matches. -/
def lprojWs (c : Config) : Nat → Wstate :=
  fun i => match c.cHarts[i]? with
    | some h => h.hWs
    | none => wsInit

def lprojSt (c : Config) : Mstate := ⟨c.cImg, c.cLog, lprojWs c⟩

theorem lcfgMatchProj (c : Config) : lcfgMatch c (lprojSt c) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i h hlk
  show wsCtrlUp h.hWs (lprojWs c i)
  simp only [lprojWs, hlk]
  exact wsCtrlUpRefl _

theorem lcfgMatchLog (c : Config) (σ : Mstate) : lcfgMatch c σ → σ.msLog = c.cLog :=
  fun h => h.2.1

/-- The one-hart-updated instance, shared by all four arms. -/
theorem lcfgMatchUpdGen (img : Image) (lg : List Wmsg) (hs : List Hart) (i : Nat) (h : Hart)
    (prog' : List Instr) (regs' : GMapF Nat (BitVec 8)) (w : Wstate) (f g : Nat → Wstate) :
    (∀ j hj, hs[j]? = some hj → wsCtrlUp hj.hWs (f j)) →
    hs[i]? = some h →
    wsCtrlUp w (g i) →
    (∀ j, j ≠ i → g j = f j) →
    lcfgMatch ⟨img, lg, hs.set i ⟨prog', regs', w⟩⟩ ⟨img, lg, g⟩ := by
  intro hf hlk hgi hgne
  refine ⟨rfl, rfl, ?_⟩
  intro j hj hJ
  dsimp only at hJ ⊢
  by_cases hji : j = i
  · subst hji
    rw [list_lookup_insert (lookup_lt_Some hlk)] at hJ
    cases hJ
    exact hgi
  · rw [list_lookup_insert_ne (Ne.symm hji)] at hJ
    rw [hgne j hji]
    exact hf j hj hJ

/-! ## The step lemma: one `lstep` is exactly one `mstep`

The four arms match 1:1 —
  `ILoad r a aq`       ↦ `LLoad aq a [t] [v]`                     (`MStepLoad`)
  `IStore a v`         ↦ `LStore false a [v] WCplain`             (`MStepStore`)
  `IFence pr pw sr sw` ↦ `LFence pr pw sr sw`                     (`MStepFence`)
  `IAmoSwapAq r a v`   ↦ `LRmw true false a [t] [vv] [v] WCexcl`  (`MStepRmw`).
The register file and the remaining program are simply forgotten. -/
theorem lstepMstep (c c' : Config) (σ : Mstate) :
    lstep c c' → lcfgMatch c σ →
    ∃ (i : Nat) (l : Lbl) (σ' : Mstate), mstep σ i l σ' ∧ lcfgMatch c' σ' := by
  obtain ⟨img, lg, f⟩ := σ
  obtain ⟨cimg, clog, chs⟩ := c
  obtain ⟨cimg', clog', chs'⟩ := c'
  rintro ⟨i, h, hlk, himg, harm⟩ ⟨hmi, hml, hmw⟩
  dsimp only at hlk himg harm hmi hml hmw
  subst cimg clog cimg'
  have hwi := hmw i h hlk
  split at harm
  · exact harm.elim
  · -- load
    rename_i r a aq rest _
    obtain ⟨t, v, hb, hr, rfl, rfl⟩ := harm
    refine ⟨i, LLoad aq a [t] [v], _,
      mstep.MStepLoad aq a [t] [v] (rdOkSingleCtrlUp _ _ h.hWs (f i) aq a t v hwi hb hr), ?_⟩
    refine lcfgMatchUpdGen _ _ chs i h _ _ _ f _ hmw hlk ?_ ?_
    · rw [updWsEq]; exact wsCtrlUpLoad _ _ _ _ _ hwi
    · intro j hne; exact updWsNe _ _ _ _ hne
  · -- store
    rename_i a v rest _
    obtain ⟨rfl, rfl⟩ := harm
    refine ⟨i, LStore false a [v] .WCplain,
      _,
      mstep.MStepStore false a [v] .WCplain (List.cons_ne_nil _ _), ?_⟩
    refine lcfgMatchUpdGen _ _ chs i h _ _ _ f _ hmw hlk ?_ ?_
    · rw [updWsEq]; exact wsCtrlUpStore _ _ _ _ _ hwi
    · intro j hne; exact updWsNe _ _ _ _ hne
  · -- fence
    rename_i pr pw sr sw rest _
    obtain ⟨rfl, rfl⟩ := harm
    refine ⟨i, LFence pr pw sr sw,
      _, mstep.MStepFence pr pw sr sw, ?_⟩
    refine lcfgMatchUpdGen _ _ chs i h _ _ _ f _ hmw hlk ?_ ?_
    · rw [updWsEq]; exact wsCtrlUpFence _ _ _ _ _ _ hwi
    · intro j hne; exact updWsNe _ _ _ _ hne
  · -- amoswap.aq: the atomicity conjunct IS `rmwLatest` at one byte
    rename_i r a v rest _
    obtain ⟨t, vv, hb, hnw, hr, rfl, rfl⟩ := harm
    refine ⟨i, LRmw true false a [t] [vv] [v] .WCexcl,
      _,
      mstep.MStepRmw true false a [t] [vv] [v] .WCexcl (List.cons_ne_nil _ _) rfl
        (rdOkSingleCtrlUp _ _ h.hWs (f i) true a t vv hwi hb hr)
        (rmwLatestSingle _ _ a t (by rw [hb]; rfl) hnw), ?_⟩
    refine lcfgMatchUpdGen _ _ chs i h _ _ _ f _ hmw hlk ?_ ?_
    · rw [updWsEq]; exact wsCtrlUpStore _ _ _ _ _ (wsCtrlUpLoad _ _ _ _ _ hwi)
    · intro j hne; exact updWsNe _ _ _ _ hne

/-! ## The bridge -/

/-- Extending the execution by one `lstep`. -/
theorem lbridgeStep (E : Exec) (c c' : Config) :
    execWf E → lcfgMatch c (stt E E.exTr.length) → lstep c c' →
    ∃ E', execWf E' ∧ exImg E' = exImg E ∧ lcfgMatch c' (stt E' E'.exTr.length) := by
  intro hE hm hstep
  obtain ⟨i, l, σ', hms, hm'⟩ := lstepMstep c c' _ hstep hm
  refine ⟨⟨E.exSt ++ [σ'], E.exTr ++ [⟨i, l⟩]⟩, ?_, ?_, ?_⟩
  · exact execSnoc E ⟨i, l⟩ σ' hE hms
  · have hlen := hE.1
    have hst0 : 0 < E.exSt.length := by omega
    simp only [exImg, eimg, stt]
    rw [lookup_app_l hst0]
  · have hlen := hE.1
    have : stt ⟨E.exSt ++ [σ'], E.exTr ++ [(⟨i, l⟩ : Estep)]⟩ (E.exTr ++ [(⟨i, l⟩ : Estep)]).length = σ' := by
      unfold stt
      simp only [List.length_append, List.length_singleton]
      rw [lookup_app_r (by omega)]
      simp [hlen]
    rw [this]
    exact hm'

theorem lbridgeRun (c c' : Config) :
    rtc lstep c c' →
    ∀ E, execWf E → lcfgMatch c (stt E E.exTr.length) →
    ∃ E', execWf E' ∧ exImg E' = exImg E ∧ lcfgMatch c' (stt E' E'.exTr.length) := by
  intro h
  refine rtc_ind_l (R := lstep)
    (fun x => ∀ E, execWf E → lcfgMatch x (stt E E.exTr.length) →
      ∃ E', execWf E' ∧ exImg E' = exImg E ∧ lcfgMatch c' (stt E' E'.exTr.length))
    c' ?_ ?_ c h
  · intro E hE hm
    exact ⟨E, hE, rfl, hm⟩
  · intro x y hs _ ih E hE hm
    obtain ⟨E1, hE1, himg1, hm1⟩ := lbridgeStep E x y hE hm hs
    obtain ⟨E2, hE2, himg2, hm2⟩ := ih E1 hE1 hm1
    exact ⟨E2, hE2, by rw [himg2, himg1], hm2⟩

/-- THE PROJECTION THEOREM (M6 W4).  Every reachable configuration of the
litmus machine, from an initial configuration (empty log, every hart at
`wsInit`), is matched by the final `Mstate` of an `execWf` execution over the
same image. -/
theorem lstepExecWf (img : Image) (harts0 : List Hart) (c : Config) :
    (∀ h ∈ harts0, h.hWs = wsInit) →
    rtc lstep ⟨img, [], harts0⟩ c →
    ∃ E, execWf E ∧ exImg E = img ∧ lcfgMatch c (stt E E.exTr.length) := by
  intro hinit hrun
  let σ0 : Mstate := ⟨img, [], fun _ => wsInit⟩
  have hE : execWf ⟨[σ0], []⟩ := execNil σ0 rfl (fun _ => rfl)
  have hm0 : lcfgMatch ⟨img, [], harts0⟩ (stt ⟨[σ0], []⟩ 0) := by
    refine ⟨rfl, rfl, ?_⟩
    intro i h hlk
    show wsCtrlUp h.hWs wsInit
    rw [hinit h (elem_of_list_lookup_2 hlk)]
    exact wsCtrlUpRefl _
  obtain ⟨E, hE', himg, hm⟩ := lbridgeRun _ _ hrun (⟨[σ0], []⟩ : Exec) hE hm0
  exact ⟨E, hE', himg, hm⟩

/-- SANITY (the `wp_pf_bridge_log` analogue): the projected execution's final
log IS the configuration's log. -/
theorem lstepExecLog (img : Image) (harts0 : List Hart) (c : Config) :
    (∀ h ∈ harts0, h.hWs = wsInit) →
    rtc lstep ⟨img, [], harts0⟩ c →
    ∃ E, execWf E ∧ exImg E = img ∧ exLog E = c.cLog := by
  intro hinit hrun
  obtain ⟨E, hE, himg, hm⟩ := lstepExecWf img harts0 c hinit hrun
  exact ⟨E, hE, himg, lcfgMatchLog _ _ hm⟩

/-- SANITY: the theorem applies verbatim to `WeakLitmus`'s own litmus
configurations — here SB, whose initial config is `⟨img0, [], [_, _]⟩` with
both harts at `wsInit`. -/
theorem lstepExecWfSb (c : Config) :
    reach sbC0 c →
    ∃ E, execWf E ∧ exImg E = img0 ∧ exLog E = c.cLog := by
  intro hrun
  exact lstepExecLog img0 [⟨sbProg0, ∅, wsInit⟩, ⟨sbProg1, ∅, wsInit⟩] c
    (by intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl <;> rfl) hrun

end Weak
