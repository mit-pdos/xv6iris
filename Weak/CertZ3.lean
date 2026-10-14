/-
Weak: **W10-2 [OWN.94] (N2′), increment 4 — the realized member, and (G-3) at a member from the
free walk** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

N2′ reads the realized member `GR` off the walk's final candidate (spike (1): "GR is chosen by the
policy").  This file:

  §1  **`CertZ3.member n c`** — the member graph of a candidate `c` with `n` rows: row `i` is hart
      `i`'s trace labels (`CertZ2.hartTr`), gmo is the trace's memory events in trace order (the
      `graphOfCand` order, `AxViolSubsume.cg`).  Its facts, for a consistent candidate whose agents
      are below `n`: `CertZ3.memberGwf`, `CertZ3.memberGwrowGmo` (each hart's writes in program
      order — the MACHINE's fact, never `GF`'s), `CertZ3.memberLogPfx` (its write order IS the
      candidate's log: `wlogPfx … (cdLogEnd c)`), and the rows (`CertZ3.forall₂Range`);
  §2  the ZERO-CUT WALK SUPPLY **`CatLin.walkSupplyCZ`** (THE NAMED PREMISE replacing the zero-cut
      use of `CatLin.tailPolicyCZ`: a walk invariant, its start, the walk policy `CertZ2.walkPolZ`
      over `GF`'s rows, and the lock-co agreement of the finished walk's member — W10-3/W10-4 and
      the walk-order lemma) and **`CatLin.certSupplyCZROfWalk`** (`walkSupplyCZ → certSupplyCZR`:
      the free walk from the empty candidate, the member, the agreement at `pi = id`);
  §3  the kill W11-F consumes at the zero cut: **`CatLin.cycleKillOfWalkSupCZRC`**.

Spec: `memberGwrowGmo` is a property of the candidate (each hart's steps are appended in program
order), not an assumption on `GF` (assuming `gwrowGmo GF` would be STRONGER than RVWMO); the rest is
proof organisation (FAITHFUL).  Lean-only helpers file-qualified (`CertZ3.*`).
-/
import Weak.CertZ2
import Weak.GraphFetchN2
import Weak.AxViolSubsume

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The member graph -/

/-- The member graph of `c` with `n` rows. -/
def CertZ3.member (n : Nat) (c : Cand) : Gexec :=
  ⟨c.cdImg, (List.range' 0 n).map (fun i => CertZ2.hartTr c.cdTr i), (cg (candExec c)).gxGmo⟩

/-- A filtered lookup comes from a position of the list. -/
theorem CertZ3.filterLookupInv {A : Type _} (p : A → Bool) :
    ∀ (l : List A) (j : Nat) (x : A), (l.filter p)[j]? = some x →
      ∃ k, l[k]? = some x ∧ p x = true ∧ ((l.take k).filter p).length = j := by
  intro l
  induction l with
  | nil => intro j x h; simp at h
  | cons y l ih =>
    intro j x h
    by_cases hy : p y = true
    · rw [List.filter_cons_of_pos hy] at h
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨0, rfl, hy, by simp⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨k, hk, hx, hlen⟩ := ih j x h
        refine ⟨k + 1, by simpa using hk, hx, ?_⟩
        simp [List.take_succ_cons, List.filter_cons_of_pos hy, hlen]
    · rw [List.filter_cons_of_neg hy] at h
      obtain ⟨k, hk, hx, hlen⟩ := ih j x h
      refine ⟨k + 1, by simpa using hk, hx, ?_⟩
      simp [List.take_succ_cons, List.filter_cons_of_neg hy, hlen]

theorem CertZ3.hartTrNil (tr : List Estep) (x : Nat) :
    (∀ s, s ∈ tr → s.esAg ≠ x) → CertZ2.hartTr tr x = [] := by
  intro h
  induction tr with
  | nil => rfl
  | cons s tr ih =>
    rw [CertZ2.hartTrCons, if_neg (h s (by simp))]
    exact ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))

theorem CertZ3.rowLookup (n i : Nat) (f : Nat → List Lbl) :
    ((List.range' 0 n).map f)[i]? = if i < n then some (f i) else none := by
  split
  · rename_i h
    rw [List.getElem?_map, lookup_seq_lt h, Nat.zero_add]
    rfl
  · rename_i h
    rw [List.getElem?_eq_none]
    simp
    omega

/-- A label of the member is the trace label of its hart's filtered position. -/
theorem CertZ3.memberLblHart (n : Nat) (c : Cand) (e : Geid) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) →
    gxLbl (CertZ3.member n c) e = (CertZ2.hartTr c.cdTr e.1)[e.2]? := by
  intro hag
  unfold gxLbl CertZ3.member
  dsimp only
  rw [CertZ3.rowLookup]
  split
  · rfl
  · rename_i h
    rw [CertZ3.hartTrNil c.cdTr e.1 (fun s hs he => h (he ▸ hag s hs))]
    rfl

/-- … and so is a label of `cg`. -/
theorem CertZ3.cgLblHart (c : Cand) (e : Geid) :
    gxLbl (cg (candExec c)) e = (CertZ2.hartTr c.cdTr e.1)[e.2]? := by
  show (((List.range' 0 ((c.cdTr.map Estep.esAg).foldr max 0 + 1)).map
      (fun i => (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb)))[e.1]?).bind
      (fun p => p[e.2]?) = _
  rw [CertZ3.rowLookup]
  split
  · rfl
  · rename_i h
    rw [CertZ3.hartTrNil c.cdTr e.1 (fun s hs he => h (by
      have := axViolSubsumeFoldrMaxLe _ _ (List.mem_map_of_mem (f := Estep.esAg) hs)
      omega))]
    rfl

theorem CertZ3.memberLbl (n : Nat) (c : Cand) (e : Geid) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) →
    gxLbl (CertZ3.member n c) e = gxLbl (cg (candExec c)) e := by
  intro hag
  rw [CertZ3.memberLblHart n c e hag, CertZ3.cgLblHart]

/-- The member's label lookup comes from a trace step. -/
theorem CertZ3.cgLblInv (c : Cand) (e : Geid) (l : Lbl) :
    gxLbl (cg (candExec c)) e = some l →
    ∃ k s, c.cdTr[k]? = some s ∧ ceid (candExec c) k = e ∧ s.esLb = l := by
  rw [CertZ3.cgLblHart]
  intro h
  unfold CertZ2.hartTr at h
  rw [List.getElem?_map] at h
  cases hf : (c.cdTr.filter (fun s => decide (s.esAg = e.1)))[e.2]? with
  | none => rw [hf] at h; cases h
  | some s =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨k, hk, hp, hlen⟩ := CertZ3.filterLookupInv _ _ _ _ hf
    have hag : s.esAg = e.1 := of_decide_eq_true hp
    refine ⟨k, s, hk, ?_, h⟩
    rw [ceidCf (candExec c) k s hk]
    show (s.esAg, ((c.cdTr.take k).filter (fun s' => decide (s'.esAg = s.esAg))).length) = e
    rw [hag, hlen]

theorem CertZ3.memberGisW (n : Nat) (c : Cand) (e : Geid) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) → gisW (CertZ3.member n c) e = gisW (cg (candExec c)) e := by
  intro hag
  unfold gisW
  rw [CertZ3.memberLbl n c e hag]

theorem CertZ3.memberGwrites (n : Nat) (c : Cand) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) → gwrites (CertZ3.member n c) = gwrites (cg (candExec c)) := by
  intro hag
  unfold gwrites
  show (cg (candExec c)).gxGmo.filter (gisW (CertZ3.member n c)) = _
  exact List.filter_congr (fun e _ => CertZ3.memberGisW n c e hag)

theorem CertZ3.memberGwix (n : Nat) (c : Cand) (e : Geid) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) → gwix (CertZ3.member n c) e = gwix (cg (candExec c)) e := by
  intro hag
  unfold gwix
  rw [CertZ3.memberGwrites n c hag]

/-- **THE MEMBER IS WELL-FORMED** (gmo duplicate-free and exactly the memory events; the label shapes
are the candidate's `candShape`). -/
theorem CertZ3.memberGwf (n : Nat) (c : Cand) :
    srvwmoConsistent c → (∀ s, s ∈ c.cdTr → s.esAg < n) → gwf (CertZ3.member n c) := by
  intro hcons hag
  have hsh := hcons.1
  refine ⟨cgNodup (candExec c), fun e => ?_, ?_⟩
  · constructor
    · intro he
      obtain ⟨k, s, hk, hm, rfl⟩ := cgSurj (candExec c) e he
      exact ⟨s.esLb, by rw [CertZ3.memberLbl n c _ hag]; exact (cgLbl _ k s hk).1, hm⟩
    · rintro ⟨l, hl, hm⟩
      rw [CertZ3.memberLbl n c _ hag] at hl
      obtain ⟨k, s, hk, rfl, rfl⟩ := CertZ3.cgLblInv c e l hl
      exact cgMem (candExec c) k s hk hm
  · intro i p k l hp hl
    have hlbl : gxLbl (CertZ3.member n c) (i, k) = some l := by
      unfold gxLbl; rw [hp]; exact hl
    rw [CertZ3.memberLbl n c _ hag] at hlbl
    obtain ⟨k', s, hk', -, rfl⟩ := CertZ3.cgLblInv c _ l hlbl
    exact hsh k' s hk'

/-- **EACH HART'S WRITES IN PROGRAM ORDER** — the member's `gwrowGmo` (the machine's fact). -/
theorem CertZ3.memberGwrowGmo (n : Nat) (c : Cand) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) → gwrowGmo (CertZ3.member n c) := by
  intro hag x j k hjk ⟨lj, hlj, hwj⟩ ⟨lk, hlk, hwk⟩
  rw [CertZ3.memberLbl n c _ hag] at hlj hlk
  obtain ⟨kj, sj, hkj, hej, rfl⟩ := CertZ3.cgLblInv c _ lj hlj
  obtain ⟨kk, sk, hkk, hek, rfl⟩ := CertZ3.cgLblInv c _ lk hlk
  rw [CertZ3.memberGwix n c _ hag, CertZ3.memberGwix n c _ hag, ← hej, ← hek]
  have hlt : kj < kk := by
    rw [ceidCf (candExec c) kj sj hkj] at hej
    rw [ceidCf (candExec c) kk sk hkk] at hek
    simp only [cf, Prod.mk.injEq] at hej hek
    obtain ⟨haj, hcj⟩ := hej
    obtain ⟨hak, hck⟩ := hek
    refine Nat.lt_of_not_le (fun hle => ?_)
    have := filterTakeMono' (fun s => decide (s.esAg = x)) c.cdTr kk kj hle
    change ((c.cdTr.take kj).filter (fun s' => decide (s'.esAg = sj.esAg))).length = j at hcj
    change ((c.cdTr.take kk).filter (fun s' => decide (s'.esAg = sk.esAg))).length = k at hck
    rw [haj] at hcj
    rw [hak] at hck
    omega
  have hmo := cgLt (candExec c) kj kk sj sk hkj hkk (lbIsWMem _ hwj) (lbIsWMem _ hwk) hlt
  have hmj : ceid (candExec c) kj ∈ gwrites (cg (candExec c)) :=
    (gwritesElemOf _ _).2 ⟨hmo.1, by unfold gisW; rw [(cgLbl _ kj sj hkj).1]; exact hwj⟩
  have hmk : ceid (candExec c) kk ∈ gwrites (cg (candExec c)) :=
    (gwritesElemOf _ _).2 ⟨hmo.2.1, by unfold gisW; rw [(cgLbl _ kk sk hkk).1]; exact hwk⟩
  exact (gwixGposLt _ _ _ (cgNodup _) hmj hmk).2 hmo.2.2

theorem CertZ3.lbWrOfW (l : Lbl) : lbIsW l = true → ∃ base vs, lbWr l = some (base, vs) := by
  cases l <;> simp [lbIsW, lbWr]

/-- **THE MEMBER'S WRITE ORDER IS THE CANDIDATE'S LOG.** -/
theorem CertZ3.memberLogPfx (n : Nat) (c : Cand) :
    srvwmoConsistent c → (∀ s, s ∈ c.cdTr → s.esAg < n) →
    wlogPfx (CertZ3.member n c) (gwrites (CertZ3.member n c)).length (cdLogEnd c) := by
  intro hcons hag
  obtain ⟨hwf, htrE, -⟩ := srvwmoRealizable c hcons
  have hlenE : (L (candExec c)).length = c.cdTr.length := by
    unfold L; rw [List.length_mapIdx]; rfl
  refine ⟨?_, ?_⟩
  · rw [CertZ3.memberGwrites n c hag, cgGwrites, List.length_map, cdLogEndFull, ← cdLogFull,
      ← candElog c _ (Nat.le_refl _),
      elogWrites (candExec c) _ hwf (by rw [htrE]; exact Nat.le_refl _),
      List.take_of_length_le (by rw [hlenE]; exact Nat.le_refl _)]
  · intro p w _ hw
    rw [show gwriteAt (CertZ3.member n c) (p + 1) = gwriteAt (cg (candExec c)) (p + 1) by
      show (gwrites _)[p]? = (gwrites _)[p]?; rw [CertZ3.memberGwrites n c hag]] at hw
    obtain ⟨hwm, hix⟩ := gwriteAtInv _ _ _ (cgNodup _) hw
    obtain ⟨hgmo, hisw⟩ := (gwritesElemOf _ _).1 hwm
    obtain ⟨k, s, hk, -, rfl⟩ := cgSurj (candExec c) w hgmo
    obtain ⟨hlbl, hagt⟩ := cgLbl (candExec c) k s hk
    have hW : lbIsW s.esLb = true := by unfold gisW at hisw; rw [hlbl] at hisw; exact hisw
    have hix' := cgWix (candExec c) k s hwf hk hW
    rw [hix, evTsAt, candElog c k (by have := lookup_lt_Some hk; rw [htrE] at this; omega)] at hix'
    obtain ⟨base, vs, hwr⟩ := CertZ3.lbWrOfW _ hW
    have hesm : esMsg s = [⟨base, vs, some s.esAg, lbCls s.esLb⟩] := by
      unfold esMsg; rw [hwr]
    obtain ⟨rest, hrest⟩ := cdLogSplit c (k + 1) c.cdTr.length (lookup_lt_Some hk)
    have hlog : cdLogEnd c = cdLog c k ++ ⟨base, vs, some s.esAg, lbCls s.esLb⟩ :: rest := by
      rw [cdLogEndFull, ← cdLogFull, hrest, cdLogS c k s hk, hesm]
      simp
    rw [hlog, show p = (cdLog c k).length by omega, list_lookup_middle rfl]
    unfold WeakRvwmoKillArms.gmsg
    rw [CertZ3.memberLbl n c _ hag, hlbl]
    simp only [hwr, hagt]

/-- `Forall₂` against a map over a range, from the pointwise fact. -/
theorem CertZ3.forall₂Range {α β : Type} (R : α → β → Prop) (f : Nat → β) :
    ∀ (rows : List α) (s : Nat),
      (∀ x a, rows[x]? = some a → R a (f (s + x))) →
      List.Forall₂ R rows ((List.range' s rows.length).map f) := by
  intro rows
  induction rows with
  | nil => intro _ _; exact .nil
  | cons a rows ih =>
    intro s h
    rw [List.length_cons, List.range'_succ, List.map_cons]
    refine .cons (by simpa using h 0 a rfl) (ih (s + 1) (fun x b hb => ?_))
    have := h (x + 1) b (by simpa using hb)
    rwa [show s + (x + 1) = s + 1 + x by omega] at this

/-! # 2. (G-3) at a member from the free walk, at the zero cut -/

namespace CatLin

/-- **THE ZERO-CUT WALK SUPPLY — THE NAMED PREMISE (W10-3/W10-4 and the walk-order lemma)**: on every
cyclic class graph with the residue facts, a walk invariant `Inv` holding at the empty start, the
walk policy over `GF`'s rows (the order IS po ∪ co_L, spike (1); the per-step obligations are the
site datum's, W10-4), and, at a finished walk, the lock-co agreement of the member with `GF`.
It refines `tailPolicyCZ` at the zero cut: the run, the member and the rows are DERIVED
(`certSupplyCZROfWalk`), only the policy and the final lock co are asked. -/
def walkSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ Inv : CertZ2.WInv,
      (∀ itvOf fiOf, CertZ.cstOkZW d0 (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf →
        Inv (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf (fun _ => 0)) ∧
      CertZ2.walkPolZ d0 GF.gfGd.gdG.gxProg Inv ∧
      (∀ Sf itvOf fiOf cntF, Inv Sf itvOf fiOf cntF → CertZ.cstOkZW d0 Sf itvOf fiOf →
        (∀ x, x < GF.gfGd.gdG.gxProg.length →
          (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x) →
        GraphFetchN2.lockCoAgree GF.gfGd.gdG
          (CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC) (GraphFetchN2.lockBytes P))

/-- **`certSupplyCZROfWalk`** — (G-3) AT A MEMBER FROM THE FREE WALK: the walk from the empty
candidate finishes every row; its member agrees with `GF` at `pi = id` (rows by the walk, writes
verbatim, lock co by the supply), is well-formed, in program write order, and its write order is
the run's log. -/
theorem certSupplyCZROfWalk (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    walkSupplyCZ boot d0 fab im N P → certSupplyCZR boot d0 fab im N P := by
  intro hws GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨Inv, hI0, hpol, hco⟩ := hws GF ad z ss him hc hconf hres hdr hne hch
  have hstart := wlkStartInvZ boot d0 N GF.gfGd.gdG
  obtain ⟨itv0, fi0, hok0⟩ := CertZ.cstOkZWOf d0 _ hstart.1
  obtain ⟨_, Sf, itvF, fiF, cntF, tradd, hrun, hokF, hinvF, hdone, -, htr, hf2, hagt, himg,
    hpst⟩ := CertZ2.walkRunZ d0 GF.gfGd.gdG.gxProg Inv hpol _ (wlkStart boot d0 N GF.gfGd.gdG) itv0 fi0 (fun _ => 0)
      (Nat.le_refl _) hok0 (hI0 itv0 fi0 hok0)
  have htr' : Sf.cstC.cdTr = tradd := by rw [htr]; rfl
  have hagS : ∀ s, s ∈ Sf.cstC.cdTr → s.esAg < GF.gfGd.gdG.gxProg.length := by
    rw [htr']; exact hagt
  have hcons := hokF.1
  refine ⟨Sf.cstC, Sf.cstPst, Sf.cstDv, CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC, fun t => t,
    runDataZOfCyc boot d0 N GF.gfGd.gdG Sf (CertZ.cstOkZOfW _ _ _ _ hokF) (by rw [himg]; rfl)
      (by rw [hpst]; rfl),
    ?_, CertZ3.memberGwf _ _ hcons hagS, ⟨show Sf.cstC.cdImg = _ by rw [himg]; rfl, ?_, hco Sf itvF fiF cntF hinvF hokF hdone⟩,
    CertZ3.memberGwrowGmo _ _ hagS⟩
  · have := CertZ3.memberLogPfx GF.gfGd.gdG.gxProg.length Sf.cstC hcons hagS
    exact logOfOfPfx _ _ this
  · show List.Forall₂ _ GF.gfGd.gdG.gxProg ((List.range' 0 GF.gfGd.gdG.gxProg.length).map _)
    refine CertZ3.forall₂Range _ _ GF.gfGd.gdG.gxProg 0 (fun x row hx => ?_)
    rw [Nat.zero_add, htr']
    have hfx := hf2 x
    have hlen : (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x := hdone x (lookup_lt_Some hx)
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some] at hfx hlen
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le hlen] at hfx
    have hre : List.Forall₂ (fun l l' => lblReidxW (lblRen (fun t => t) l) l') row
        (CertZ2.hartTr tradd x) := by
      refine List.Forall₂.imp (fun {l l'} h => ?_) hfx
      rw [lblRenId]; exact h
    exact hre

/-! # 3. The kill at the zero cut -/

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfWalkSupCZRC`** — WHAT W11-F CONSUMES AT THE ZERO CUT (N2′, W10-2): the class kill
from the WP package, the fetch-view premise, the ZERO-CUT WALK SUPPLY (`walkSupplyCZ`), the two xv6
facts and the L2′ claim at the member. -/
theorem cycleKillOfWalkSupCZRC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    walkSupplyCZ boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hws hAQ hRC hl2 =>
    cycleKillOfL2CZRC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZC boot d0 fab _) (certSupplyCZROfWalk boot d0 fab _ N P hws) hAQ hRC hl2

end glue

end CatLin

end Weak
