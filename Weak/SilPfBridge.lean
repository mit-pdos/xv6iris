/-
Weak: **(c) [OWN.100], increment 4b-ii — the twin pf machine to the twin fabric-shared machine**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

  §1  `SilPf.pnodeExStoreInv` (a node emitting `LExStore` IS an exclusive RAM `memWrite` node, with its
      label's fields), `SilPf.ecfgOfWs` (the configuration after a hart's views-only move);
  §2  **`SilPf.wpPfStepSEpfStepS`** — a twin pf step from an event configuration is a twin fabric-shared
      step (the registered case by `wpPfStepEpfStep`; the silent case builds `SilLang.silentWrite`), and
      the run form **`SilPf.wpPfRtcEpfRtcS`** (`wpPfRtcEpfRtc`'s twin, under the fetch-view premise along
      the twin runs).

Spec: FAITHFUL (proof organisation).
-/
import Weak.SilPf

namespace Weak

open MachCSL MachCSL.Stdpp
open LeanRV64D
open Wlabel

/-! # 1. Inversion and the configuration -/

theorem SilPf.pnodeExStoreInv (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d (LExStore rl base data asrc vsrc) m' ors fn' d' oib obar →
    ∃ n va req k, m = .impure (.ok (.memWrite n va req)) k ∧ devAddr req.pa = false ∧
      ∃ v, req.value = some v ∧ n ≠ 0 ∧ (classify req.access_kind).akLatest = true ∧
        rl = (classify req.access_kind).akSync ∧ base = paZ req.pa ∧
        data = WeakInterpProj.wbytes n v ∧ asrc = depsAsrc (depsOfIb ib.ibBits) ∧
        vsrc = depsVsrc (depsOfIb ib.ibBits) ∧ m' = k (.Ok (some true)) ∧ ors = none ∧
        fn' = none ∧ d' = d ∧ oib = none ∧ obar = none := by
  intro h
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rcases h with ⟨_, _, _, _, _, h, _⟩ | ⟨_, ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩⟩ <;>
          exact nomatch h
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · rename_i hdev
        split at h
        · rename_i v hv
          rcases h with ⟨hn, ⟨_, h, _⟩ | ⟨ht, ⟨hl, hm, ho, hf, hd, hib, hbar⟩ | ⟨h, _⟩⟩⟩
          · exact nomatch h
          · simp only [LExStore.injEq] at hl
            obtain ⟨h1, h2, h3, h4, h5⟩ := hl
            exact ⟨n, va, req, k, rfl, by simpa using hdev, v, hv, hn, ht, h1, h2, h3, h4, h5, hm, ho,
              hf, hd, hib, hbar⟩
          · exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce n w =>
      have h1 := h.1
      rcases annLabelOr n w with e | e <;> rw [e] at h1 <;> exact nomatch h1
    | branchAnnounce => exact nomatch h.1

/-- The configuration after a hart's views-only move to `h'`. -/
theorem SilPf.ecfgOfWs (P : Epool) (σ : WGState) (c : CPU) (h' : ehst) (ws' : Wstate) :
    ecfgOf (epHset P c h') (ewgWs σ c ws')
      = ⟨imgZ σ.wgimg, σ.wglog, efabOf P σ,
         (eags P σ).set c.val
           ⟨.PHart c (ehartM h') (σ.wgregs c) (ehartFn h') (σ.wgib c), ws', ∅⟩⟩ := by
  have hne : ∀ c', c' ≠ c → ehartAg (epHset P c h') (ewgWs σ c ws') c' = ehartAg P σ c' := by
    intro c' hc'
    simp only [ehartAg, epHset, ewgWs, if_neg hc']
  have hag : ehartAg (epHset P c h') (ewgWs σ c ws') c
      = ⟨.PHart c (ehartM h') (σ.wgregs c) (ehartFn h') (σ.wgib c), ws', ∅⟩ := by
    simp [ehartAg, epHset, ewgWs, gwsInsertEq]
  have heq := eagsUpdHart P (epHset P c h') σ (ewgWs σ c ws') c hne rfl
  unfold ecfgOf
  rw [heq, hag]
  rfl

/-! # 2. The bridge -/

theorem SilPf.wpPfStepSEpfStepS (i : Nat) (l : Wlabel) (P : Epool) (σ : WGState)
    (c' : Wpcfg Pexv6 Efab) :
    ethreadLive σ P.epGen → efetchItvOk P σ →
    SilPf.wpPfStepS pstepEv pclsEv i l (ecfgOf P σ) c' →
    ∃ P' σ', SilEpf.epfStepS i l (P, σ) (P', σ') ∧ ecfgOf P' σ' = c' := by
  intro hl hfetch hstep
  cases hstep with
  | old l _ _ h =>
    obtain ⟨P', σ', hs, he⟩ := wpPfStepEpfStep i l P σ _ hl hfetch h
    exact ⟨P', σ', .old _ _ _ _ hs, he⟩
  | exStoreSilent _ ag base data asrc vsrc R q st' d' hlk hps hne hR hb hlen hval hex hq hcoh hfv hox =>
    have hlk' : (eags P σ)[i]? = some ag := hlk
    rcases eagsLookupInv P σ i ag hlk' with ⟨c, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases st' with
      | PDisk dp' => exact (show False from hps).elim
      | PHart cpu' m' rs' fn' ib' =>
        obtain ⟨hc, ors, oib, obar, hrs, hib, hnode | hplic⟩ := hps
        · obtain ⟨hnode, hd⟩ := hnode
          have hfn : ehartFn (P.epH c) = none := by
            cases hf : ehartFn (P.epH c) with
            | none => rfl
            | some f =>
              obtain ⟨pr, pw, sr, sw⟩ := f
              simp only [pstepNode, hf] at hnode
              exact nomatch hnode.1
          simp only [pstepNode, hfn] at hnode
          obtain ⟨n, va, req, k, hm, hdev, v, hv, hn, hlat, hrl, hbase, hdata, hasrc, hvsrc, hm',
            hors, hfn', hd', hoib, hobar⟩ := SilPf.pnodeExStoreInv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode
          subst hors hoib hfn' hobar
          have hP : P.epH c = some (.impure (.ok (.memWrite n va req)) k, none) := by
            cases hh : P.epH c with
            | none => rw [hh] at hm; simp [ehartM] at hm
            | some p =>
              obtain ⟨m0, f0⟩ := p
              rw [hh] at hm hfn
              simp only [ehartM] at hm
              simp only [ehartFn] at hfn
              rw [hm, hfn]
          have hlen' : data.length = n := by rw [hdata, wbytesLength]
          refine ⟨epHset P c (some (k (.Ok (some true)), none)),
            ewgWs σ c (storePostRunD (SilCand.aqRaise (σ.wgws c) q) false
              (srcsView (σ.wgws c) asrc) (srcsView (σ.wgws c) vsrc) base data.length q),
            .silent c _ P σ _ (some (k (.Ok (some true)), none)) _ hl hP ?_, ?_⟩
          · refine ⟨rfl, n, va, req, k, rfl, v, q, R, hdev, hv, hn, hlat, hrl.symm, hR,
              by rw [hb, hbase], by rw [hlen, hlen'], fun j t hj => ?_, by rw [← hbase]; exact hex,
              hq, fun j hj => ?_, by rw [hasrc, hvsrc] at hfv; exact hfv, hox, rfl, ?_⟩
            · obtain ⟨h1, h2⟩ := hval j t hj
              refine ⟨h1, ?_⟩
              rw [← hbase, ← hdata]
              exact h2
            · rw [← hbase]; exact hcoh j (by rw [hlen']; exact hj)
            · rw [hasrc, hvsrc, hbase, hlen']
              rfl
          · rw [SilPf.ecfgOfWs]
            have hd2 : d' = efabOf P σ := by
              rw [hd, hd']
              rfl
            simp only [ehartM, ehartFn]
            rw [hd2, hc, hrs, hib, hm']
            rfl
        · obtain ⟨_, _, _, _, h, _⟩ := hplic
          exact nomatch h
    · cases st' with
      | PHart cpu' m' rs' fn' ib' => exact (show False from hps).elim
      | PDisk dp' => exact (pstepDiskNoEx _ _ _ _ _ hps).elim

theorem SilPf.stepLive (gen i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) :
    ethreadLive ρ.2 gen → ρ.1.epGen = gen → SilEpf.epfStepS i l ρ ρ' →
    ethreadLive ρ'.2 gen ∧ ρ'.1.epGen = gen := by
  intro hl hP h
  cases h with
  | old i l ρ ρ' h => exact epfStepLive gen i l _ _ hl hP h
  | silent c l P σ m h' σ' hl' hh hs =>
    obtain ⟨-, n, va, req, k, -, -, v, q, R, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hs
    exact ⟨hl, hP⟩

theorem SilPf.liveAlong (P : Epool) (σ : WGState) (P1 : Epool) (σ1 : WGState) :
    ethreadLive σ P.epGen → rtc SilEpf.epfRunS (P, σ) (P1, σ1) → ethreadLive σ1 P1.epGen := by
  intro hl hr
  have key : ∀ ρ, rtc SilEpf.epfRunS (P, σ) ρ → ethreadLive ρ.2 P.epGen ∧ ρ.1.epGen = P.epGen := by
    intro ρ h
    induction h with
    | refl => exact ⟨hl, rfl⟩
    | tail _ hs ih =>
      obtain ⟨i, l, hs⟩ := hs
      exact SilPf.stepLive P.epGen i l _ _ ih.1 ih.2 hs
  obtain ⟨h1, h2⟩ := key (P1, σ1) hr
  rw [← h2] at h1
  exact h1

/-- The run form, under the fetch-view premise along the twin runs. -/
theorem SilPf.wpPfRtcEpfRtcS (P : Epool) (σ : WGState) (c' : Wpcfg Pexv6 Efab) :
    ethreadLive σ P.epGen →
    (∀ ρ, rtc SilEpf.epfRunS (P, σ) ρ → efetchItvOk ρ.1 ρ.2) →
    rtc (SilPf.wpPfRunS pstepEv pclsEv) (ecfgOf P σ) c' →
    ∃ P' σ', rtc SilEpf.epfRunS (P, σ) (P', σ') ∧ ecfgOf P' σ' = c' := by
  intro hl hcov hrun
  induction hrun with
  | refl => exact ⟨P, σ, rtc_refl _, rfl⟩
  | tail _ hs ih =>
    obtain ⟨P1, σ1, hr1, rfl⟩ := ih
    obtain ⟨i, l, hst⟩ := hs
    have hl1 : ethreadLive σ1 P1.epGen := SilPf.liveAlong P σ P1 σ1 hl hr1
    obtain ⟨P2, σ2, hs2, rfl⟩ := SilPf.wpPfStepSEpfStepS i l P1 σ1 _ hl1 (hcov (P1, σ1) hr1) hst
    exact ⟨P2, σ2, rtc_r hr1 ⟨i, l, hs2⟩, rfl⟩

end Weak
