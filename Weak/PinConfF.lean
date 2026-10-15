/-
Weak: **W11-F [OWN.102], A13 (a) increment 2 — the STRUCTURAL facts of a `hartConff` emission**
(`PROGRESS-W11F.md` §2 A13).  Lean-only, no Rocq twin.

The B5 pin chain reads five structural facts off the single-fabric `hartConf`; none uses the runs,
only the item shapes and `hlblRealizes`.  Their `hemitf` twins (proofs transcribed from the `hemit`
ones; `GraphFabConf.hemitfTagLbl` already merged):
`hemitfFenceLbl`/`hartConffFenceLbl` (`PinTrap.hemitFenceLbl`), `hemitfPosGe`/`hemitfPosLt`/
`hartConffReadsBefore` (`PinTrap.hemitPosLt`), `hartConffTagLbl`/`hartConffRowDepsWf`
(`WeakRvwmoConf.hartConfTagLbl`/`hartConfRowDepsWf`); and `PinTrap` §5.6 over `hartConff`:
`PinTrap.texcFreeSoundF`, `PinTrap.forgetConfF`, `PinTrap.pinSegPinStoreFreeF`, `PinTrap.pinSegPinCtrlFreeF`.

Also the RUN of a `hartConff` emission (`hemitfPrunJ`/`hartConffPrunJ`: a jump run `prunJ` of its labels
from ANY start fabric) and its administrative fetch items (`hemitfFeNone`/`hartConffFeNone`).

Spec: FAITHFUL (proof organisation).  Names: the `hemit`/`hartConf` names with `f` (grepped: new).
-/
import Weak.PinTrap
import Weak.GraphFabConf
import Weak.PinRunJ

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef

theorem hemitfFenceLbl (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) (pr pw sr sw : Bool) (kf : Nat) :
    hemitf dvi dvo tq k ws row p es pfin → (Wlabel.LFence pr pw sr sw, some kf) ∈ es →
    k ≤ kf ∧ row[kf - k]? = some (Lbl.LFence pr pw sr sw) := by
  intro h
  induction h with
  | HFnil k ws p => intro hit; exact absurd hit List.not_mem_nil
  | HFone k ws lb row p ls pa da l p' es pfin _ _ hre _ _ _ ih =>
    intro hit
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp at e
    rcases List.mem_cons.1 hit with e | hit
    · simp only [Prod.mk.injEq, Option.some.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨_, _, _, hpr⟩ := hre
      simp only [projLbl, Option.some.injEq] at hpr
      subst hpr
      exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨hle, hlk⟩ := ih hit
      refine ⟨by omega, ?_⟩
      rw [show kf - k = (kf - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ _ _ hre _ _ _ _ _ ih =>
    intro hit
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp at e
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp at e
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    · obtain ⟨hle, hlk⟩ := ih hit
      refine ⟨by omega, ?_⟩
      rw [show kf - k = (kf - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk

theorem hartConffFenceLbl (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
    (em : Hemission) (pr pw sr sw : Bool) (kf : Nat) :
    hartConff i row p0 dvi dvo tq em → (Wlabel.LFence pr pw sr sw, some kf) ∈ em.emItems →
    row[kf]? = some (Lbl.LFence pr pw sr sw) := by
  intro hem hit
  have := (hemitfFenceLbl dvi dvo tq 0 wsInit row p0 _ _ pr pw sr sw kf hem hit).2
  rw [Nat.sub_zero] at this
  exact this

theorem hemitfPosGe (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → ∀ it, it ∈ es → ∀ j, it.2 = some j → k ≤ j := by
  intro h it hit j hj
  obtain ⟨_, hle, _⟩ := GraphFabConf.hemitfTagLbl dvi dvo tq k ws row p es pfin it j h hit hj
  exact hle

theorem hemitfPosLt (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k0 : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k0 ws row p es pfin →
    ∀ (pre : List Eitem) (l0 : Wlabel) (w : Nat) (post : List Eitem),
      es = pre ++ (l0, some w) :: post →
      (∀ rl b d a v, l0 ≠ Wlabel.LExStore rl b d a v) →
      ∀ it, it ∈ pre → ∀ j, it.2 = some j → j < w := by
  intro h
  induction h with
  | HFnil k ws p =>
    intro pre l0 w post hes
    simp at hes
  | HFone k ws lb row p ls pa da l p' es pfin _ _ _ _ _ hrest ih =>
    intro pre l0 w post hes hnot it hit j hj
    rcases List.append_eq_append_iff.mp hes with ⟨a', hpre, hb⟩ | ⟨c', ha, hd⟩
    · cases a' with
      | nil =>
        simp only [List.append_nil] at hpre
        subst hpre
        rw [PinTrap.eadmNone _ _ hit] at hj; cases hj
      | cons x a'' =>
        simp only [List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, hes'⟩ := hb
        have hmem : (l0, some w) ∈ es := by
          rw [hes']; exact List.mem_append_right _ (List.mem_cons_self ..)
        have hw : k + 1 ≤ w := hemitfPosGe _ _ _ _ _ _ _ _ _ hrest _ hmem w rfl
        subst hpre
        rcases List.mem_append.mp hit with hit | hit
        · rw [PinTrap.eadmNone _ _ hit] at hj; cases hj
        rcases List.mem_cons.mp hit with rfl | hit
        · simp only [Option.some.injEq] at hj; omega
        · exact ih a'' l0 w post hes' hnot it hit j hj
    · cases c' with
      | nil =>
        simp only [List.append_nil] at ha
        subst ha
        rw [PinTrap.eadmNone _ _ hit] at hj; cases hj
      | cons y c'' =>
        simp only [List.cons_append, List.cons.injEq] at hd
        obtain ⟨rfl, -⟩ := hd
        have hmem : (l0, some w) ∈ eadm ls := by
          rw [ha]; exact List.mem_append_right _ (List.mem_cons_self ..)
        have := PinTrap.eadmNone ls (l0, some w) hmem
        cases this
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ _ _ hre _ _ _ _ hrest ih =>
    intro pre l0 w post hes hnot it hit j hj
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    rcases List.append_eq_append_iff.mp hes with ⟨a', hpre, hb⟩ | ⟨c', ha, hd⟩
    · cases a' with
      | nil =>
        simp only [List.append_nil] at hpre
        subst hpre
        rw [PinTrap.eadmNone _ _ hit] at hj; cases hj
      | cons x a'' =>
        simp only [List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, hb2⟩ := hb
        subst hpre
        rcases List.append_eq_append_iff.mp hb2 with ⟨b', ha'', hb3⟩ | ⟨c'', ha2, hd2⟩
        · cases b' with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hb3
            obtain ⟨⟨rfl, -⟩, -⟩ := hb3
            exact absurd rfl (hnot rl base data asrc2 vsrc2)
          | cons z b'' =>
            simp only [List.cons_append, List.cons.injEq] at hb3
            obtain ⟨rfl, hes'⟩ := hb3
            have hmem : (l0, some w) ∈ es := by
              rw [hes']; exact List.mem_append_right _ (List.mem_cons_self ..)
            have hw : k + 1 ≤ w := hemitfPosGe _ _ _ _ _ _ _ _ _ hrest _ hmem w rfl
            subst ha''
            rcases List.mem_append.mp hit with hit | hit
            · rw [PinTrap.eadmNone _ _ hit] at hj; cases hj
            rcases List.mem_cons.mp hit with rfl | hit
            · simp only [Option.some.injEq] at hj; omega
            rcases List.mem_append.mp hit with hit | hit
            · rw [PinTrap.eadmNone _ _ hit] at hj; cases hj
            rcases List.mem_cons.mp hit with rfl | hit
            · simp only [Option.some.injEq] at hj; omega
            · exact ih b'' l0 w post hes' hnot it hit j hj
        · cases c'' with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hd2
            obtain ⟨⟨rfl, -⟩, -⟩ := hd2
            exact absurd rfl (hnot rl base data asrc2 vsrc2)
          | cons y c3 =>
            simp only [List.cons_append, List.cons.injEq] at hd2
            obtain ⟨rfl, -⟩ := hd2
            have hmem : (l0, some w) ∈ eadm ls2 := by
              rw [ha2]; exact List.mem_append_right _ (List.mem_cons_self ..)
            have := PinTrap.eadmNone ls2 (l0, some w) hmem
            cases this
    · cases c' with
      | nil =>
        simp only [List.append_nil] at ha
        subst ha
        rw [PinTrap.eadmNone _ _ hit] at hj; cases hj
      | cons y c'' =>
        simp only [List.cons_append, List.cons.injEq] at hd
        obtain ⟨rfl, -⟩ := hd
        have hmem : (l0, some w) ∈ eadm ls1 := by
          rw [ha]; exact List.mem_append_right _ (List.mem_cons_self ..)
        have := PinTrap.eadmNone ls1 (l0, some w) hmem
        cases this

theorem hartConffReadsBefore (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
    (em : Hemission) (pre post : List Eitem) (l : Wlabel) (w : Nat) :
    hartConff i row p0 dvi dvo tq em → em.emItems = pre ++ (l, some w) :: post →
    (∀ rl b d a v, l ≠ Wlabel.LExStore rl b d a v) →
    ereadOk (fun e => e < w) pre := by
  intro hcf hes hnot it k hit hk _
  exact hemitfPosLt dvi dvo tq 0 wsInit row p0 _ _ hcf pre l w post hes hnot it hit k hk

theorem hartConffTagLbl (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
    (em : Hemission) (it : Eitem) (j : Nat) :
    hartConff i row p0 dvi dvo tq em → it ∈ em.emItems → it.2 = some j →
    ∃ lb, row[j]? = some lb ∧
      (elbIsR it.1 = true → lbIsR lb = true) ∧ (elbIsW it.1 = true → lbIsW lb = true) := by
  intro hem hit hj
  obtain ⟨lb, _, hlk, hr, hw⟩ := GraphFabConf.hemitfTagLbl dvi dvo tq 0 wsInit row p0 _ _ it j hem hit hj
  rw [Nat.sub_zero] at hlk
  exact ⟨lb, hlk, hr, hw⟩

theorem hartConffRowDepsWf (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
    (em : Hemission) (jk : Nat × Nat) :
    hartConff i row p0 dvi dvo tq em → jk ∈ rowDeps em.emItems →
    jk.1 < jk.2 ∧
    (∃ lb, row[jk.1]? = some lb ∧ lbIsR lb = true) ∧
    (∃ lb, row[jk.2]? = some lb ∧ lbIsW lb = true) := by
  intro hem hjk
  refine ⟨rowDepsLt _ _ hjk, ?_, ?_⟩
  · obtain ⟨it, hit, hpos, hr⟩ := rowDepsSrc _ _ hjk
    obtain ⟨lb, hlk, hrr, _⟩ := hartConffTagLbl i row p0 dvi dvo tq em it jk.1 hem hit hpos
    exact ⟨lb, hlk, hrr hr⟩
  · obtain ⟨it, hit, hpos, hw⟩ := rowDepsTgt _ _ hjk
    obtain ⟨lb, hlk, _, hww⟩ := hartConffTagLbl i row p0 dvi dvo tq em it jk.2 hem hit hpos
    exact ⟨lb, hlk, hww hw⟩

/-! ## Runs and fetch items of a `hartConff` emission -/

open Wlabel
theorem PinRunJ.prunJOfAdmRunT (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) (b : Bool) : WeakRvwmoFab.admRunT instr p d ls p' d' b → prunJ ls p d p' d' := by
  intro h
  induction h with
  | ATnil p d => exact .nil p d
  | ATcons p d l p1 d1 ls p' d' b _ hs _ ih => exact .more hs ih

theorem PinRunJ.eadmFst (ls : List Wlabel) : (eadm ls).map Prod.fst = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [eadm, List.map_cons] at ih ⊢; rw [ih]

/-- **A `hemitf` emission is a jump run of its labels, from ANY start fabric** (header). -/
theorem hemitfPrunJ (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → ∀ d, ∃ d', prunJ (es.map Prod.fst) p d pfin d' := by
  intro h
  induction h with
  | HFnil k ws p => exact fun d => ⟨d, .nil p d⟩
  | HFone k ws lb row p ls pa da l p' es pfin b har _ hst _ _ ih =>
    intro d
    obtain ⟨d', hr⟩ := ih (dvo k)
    refine ⟨d', ?_⟩
    rw [List.map_append, PinRunJ.eadmFst, List.map_cons]
    exact .jump (PinRunJ.prunJApp (PinRunJ.prunJOfAdmRunT _ _ _ _ _ _ _ har) (.more hst hr))
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 _ hst1 har2 hst2
      _ _ ih =>
    intro d
    obtain ⟨d', hr⟩ := ih (dvo k)
    refine ⟨d', ?_⟩
    rw [List.map_append, PinRunJ.eadmFst, List.map_cons, List.map_append, PinRunJ.eadmFst,
      List.map_cons]
    exact .jump (PinRunJ.prunJApp (PinRunJ.prunJOfAdmRunT _ _ _ _ _ _ _ har1)
      (.more hst1 (PinRunJ.prunJApp (PinRunJ.prunJOfAdmRunT _ _ _ _ _ _ _ har2) (.more hst2 hr))))

theorem hartConffPrunJ (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (tq : Nat → Bool) (em : Hemission) :
    hartConff i row p0 dvi dvo tq em →
    ∀ d, ∃ d', prunJ (em.emItems.map Prod.fst) p0 d em.emFin d' :=
  hemitfPrunJ dvi dvo tq 0 wsInit row p0 em.emItems em.emFin

/-- A fetch label is never a row label: its item is administrative (`hemitFeNone`'s twin). -/
theorem hemitfFeNone (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → ∀ a tvs t, (LIFetch a tvs, t) ∈ es → t = none := by
  intro h
  induction h with
  | HFnil k ws p => intro a tvs t hit; exact absurd hit List.not_mem_nil
  | HFone k ws lb row p ls pa da l p' es pfin b _ hre _ _ _ ih =>
    intro a tvs t hit
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp only [Prod.mk.injEq] at e
      exact e.2.symm
    rcases List.mem_cons.1 hit with e | hit
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, -⟩ := e
      obtain ⟨_, _, _, hpr⟩ := hre
      simp [projLbl] at hpr
    · exact ih a tvs t hit
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 _ hre _ _ _ _ _ ih =>
    intro a tvs t hit
    obtain ⟨aq, rl, base, tvs0, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp only [Prod.mk.injEq] at e
      exact e.2.symm
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, e⟩ := hit
      simp only [Prod.mk.injEq] at e
      exact e.2.symm
    rcases List.mem_cons.1 hit with e | hit
    · simp at e
    · exact ih a tvs t hit

theorem hartConffFeNone (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (tq : Nat → Bool) (em : Hemission) :
    hartConff i row p0 dvi dvo tq em → ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none :=
  hemitfFeNone dvi dvo tq 0 wsInit row p0 em.emItems em.emFin


/-! ## The B5 pin certificates' structural core over `hartConff` (`PinTrap` §5.6 transcribed) -/

open WeakRvwmoConf (Dstate dstep)
open CatLin
open PinTrapSites

namespace PinTrap

/-- **THE REAL EXCURSION IS CERTIFIED (header)**: for the hart's conformant emission (`hartConf`,
the tagged dependency clause), `texcFree` is sound for the load's entries: the walk's taint
survives every fence-free trap excursion, through `hopEnt` at each spill/restore pair. -/
theorem texcFreeSoundF (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
    (em : Hemission) (j : Nat) :
    GT.gtG.gxProg[i]? = some row → hartConff i row p0 dvi dvo tq em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    xSound (texcFree GT.gtG i em) (tEnt (forget GT) (gtAd GT.gtG GT.gtDeps) i j) := by
  intro hrow hcf hconfT pfx t gx hx hinv
  have hmono : ∀ (pre post : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8))
      (asrc vsrc : List Dsrc) (w : Nat),
      em.emItems = pre ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: post →
      ereadOk (fun e => e < w) pre :=
    fun pre post _ _ _ _ _ w hes' =>
      hartConffReadsBefore i row p0 dvi dvo tq em pre post _ w hcf hes' (fun _ _ _ _ _ h => by cases h)
  obtain ⟨hpres, gi, gk, gs, rest, S0, rfl, hes, hgi, hgs, hrun⟩ := hx
  let Ent := tEnt (forget GT) (gtAd GT.gtG GT.gtDeps) i j
  let FR := fun w k => WeakRvwmoAcyc.grf GT.gtG (i, w) (i, k)
  let Hop := fun w => ∀ k, FR w k → Ent k
  have hFR : ∀ w k, Hop w → FR w k → Ent k := fun w k h hf => h k hf
  -- the row kinds of the emission's positioned items
  have hkind : ∀ it, it ∈ em.emItems → ∀ x, it.2 = some x →
      (elbIsR it.1 = true → gisRd GT.gtG (i, x) = true) ∧
      (elbIsW it.1 = true → gisW GT.gtG (i, x) = true) := by
    intro it hit x hx
    obtain ⟨lb, hlk, hr, hw⟩ := hartConffTagLbl i row p0 dvi dvo tq em it x hcf hit hx
    have hg : gxLbl GT.gtG (i, x) = some lb := by
      show (GT.gtG.gxProg[i]?).bind (fun p => p[x]?) = _
      rw [hrow]; exact hlk
    exact ⟨fun h => by simp [gisRd, hg, hr h], fun h => by simp [gisW, hg, hw h]⟩
  have hspill : ∀ (pre post : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8))
      (asrc vsrc : List Dsrc) (w x e : Nat),
      em.emItems = pre ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: post →
      Dsrc.DReg x ∈ vsrc → e ∈ dprov (dsRun dsInit pre) x → Ent e → Hop w := by
    intro pre post rl a v asrc vsrc w x e hes' hx he hent k hfr
    have hlt : e < w :=
      (dsRunWithin (fun e => e < w) dsInit pre (dsWithinInit _) (hmono _ _ _ _ _ _ _ _ hes')).1
        x e he
    have hrd : gisRd GT.gtG (i, e) = true := by
      have hw := dsRunWithin (fun e => ∃ it, it ∈ em.emItems ∧ it.2 = some e ∧
          elbIsR it.1 = true) dsInit pre (dsWithinInit _)
        (fun it k hin hpos hr => ⟨it, by rw [hes']; exact List.mem_append_left _ hin, hpos, hr⟩)
      obtain ⟨it, hit, hpos, hr⟩ := hw.1 x e he
      exact (hkind it hit e hpos).1 hr
    have hwr : gisW GT.gtG (i, w) = true :=
      (hkind _ (by rw [hes']; exact List.mem_append_right _ (List.mem_cons_self ..)) w rfl).2 rfl
    exact hopEnt GT i j em pre post rl a v asrc vsrc w k x e hconfT hes' hx he hlt hrd hwr hfr hent
  -- the start
  have hstart : invOkS Ent (dsRun dsInit (pfx ++ gi)) t := by
    rw [dsRunApp]; exact invNeutralRunS _ _ _ _ hgi hinv
  obtain ⟨n0, hr0, hle0⟩ : ∃ n0, rowOf tStart = some (0, n0) ∧ cmLe (mapOf n0) cmId = true := by
    have h := flowStart
    revert h
    cases rowOf tStart with
    | none => intro h; simp at h
    | some pn =>
      obtain ⟨sp, n⟩ := pn
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨n, by rw [h.1], h.2⟩
  have hc0 : cInv Ent Hop t (dsRun dsInit (pfx ++ gi)) S0 (mapOf n0) := by
    obtain ⟨l1, l2⟩ := cmLeSound _ _ hle0
    refine ⟨fun x r hr ht => ?_, fun o r hr _ => (cmIdCs o r (l2 o r hr)).elim⟩
    have := cmIdCr x r (l1 x r hr)
    subst this
    exact hstart r ht
  have hes2 : em.emItems = (pfx ++ gi) ++ gk ++ (gs ++ rest) := by
    rw [hes]; simp only [List.append_assoc]
  obtain ⟨S'', sp'', n'', hr'', hc''⟩ :=
    cInvRun Ent Hop FR hFR em hspill t tStart S0 gk tEnd hrun (pfx ++ gi) (gs ++ rest) 0 n0 hes2
      (rtc_refl _) (rtc_refl _) hr0 hc0
  -- the end: every preserved register carries itself
  have hend : ∀ x, x ∈ presRegs → x ∈ cr (mapOf n'').cmR x := by
    have h := flowEnd
    rw [hr''] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    intro x hx
    exact List.contains_iff_mem.mp (h.2 x hx)
  intro r ht
  obtain ⟨e, he, hent⟩ := hc''.1 r r (hend r (hpres r ht)) ht
  refine ⟨e, ?_, hent⟩
  rw [show pfx ++ (gi ++ (gk ++ gs)) = (pfx ++ gi ++ gk) ++ gs by simp only [List.append_assoc],
    dsRunApp, dprovNeutralRun _ _ _ hgs]
  exact he


/-! ### 5.8 The certifying classes through fence-free trap excursions -/

/-- The untagged dependency clause on `forget`, from the tagged one (`gdexecQconfTForget`). -/
theorem forgetConfF (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
    (em : Hemission) :
    GT.gtG.gxProg[i]? = some row → hartConff i row p0 dvi dvo tq em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    ∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ (forget GT).gdDeps := by
  intro hrow hcf hdeps jk hjk
  obtain ⟨tg, htg, -⟩ := rowDepsSubT em.emItems jk.1 jk.2 hjk
  obtain ⟨-, ⟨lr, hlr, hr⟩, lb, hlb, hw⟩ := hartConffRowDepsWf i row p0 dvi dvo tq em jk hcf hjk
  refine (elemOfForgetDeps GT.gtG GT.gtDeps (i, jk.1) (i, jk.2)).2 ⟨tg, hdeps _ htg, ?_, ?_⟩
  · simp [gisRd, gxLbl, hrow, hlr, hr]
  · simp [gisW, gxLbl, hrow, hlb, hw]

/-- **PDep THROUGH FENCE-FREE TRAP EXCURSIONS (header)**: the any-path PDep certificate with the
site oracle `psitesT (texcFree …)` — trap excursions allowed at any walk state, each certified
by its census alignment and the frame fact — in the published quantifier (`forget GT`,
`ad := gtAd`). -/
theorem pinSegPinStoreFreeF (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (em : Hemission) (sg : Seg) (pcL : Int) (j k : Nat) (own : Bool)
    (base pre g0 post : List Eitem) (s : PState) (rl : Bool) (a : Int) (v : List (BitVec 8))
    (asrc vsrc : List Dsrc) :
    GT.gtG.gxProg[i]? = some row → hartConff i row p0 dvi dvo tq em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    psitesT (texcFree GT.gtG i em) pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    (srcsTainted s.psT (depsAddr (krole s.psPc))
      || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hes hsite hg0 hca hcv htn
  exact pinSegPinStoreT _ (forget GT) (gtAd GT.gtG GT.gtDeps) i em sg pcL j k own base pre g0
    post s rl a v asrc vsrc (texcFreeSoundF GT i row p0 dvi dvo tq em j hrow hcf hdeps)
    (forgetConfF GT i row p0 dvi dvo tq em hrow hcf hdeps) he hx hbase hes hsite hg0
    (hartConffReadsBefore i row p0 dvi dvo tq em (pre ++ g0) post _ k hcf hes
      (fun _ _ _ _ _ h => by cases h)) hca hcv htn

/-- **PCtrl THROUGH FENCE-FREE TRAP EXCURSIONS (header).** -/
theorem pinSegPinCtrlFreeF (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (em : Hemission) (sg : Seg) (pcL : Int) (j k : Nat) (own : Bool)
    (base pre g0 mid post : List Eitem) (s : PState) (srcs : List Dsrc) (kc : Option Nat)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    GT.gtG.gxProg[i]? = some row → hartConff i row p0 dvi dvo tq em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    psitesT (texcFree GT.gtG i em) pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    srcsTainted s.psT (depsCtrl (krole s.psPc)) = true →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hes hsite hg0 hcov htn
  have hes' : em.emItems = (pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid) ++
      (Wlabel.LStore rl a v asrc vsrc, some k) :: post := by
    rw [hes]; simp only [List.append_assoc, List.cons_append]
  have hrb := hartConffReadsBefore i row p0 dvi dvo tq em _ post _ k hcf hes'
    (fun _ _ _ _ _ h => by cases h)
  refine pinSegPinCtrlT _ (forget GT) (gtAd GT.gtG GT.gtDeps) i em sg pcL j k own base pre g0 mid
    post s srcs kc rl a v asrc vsrc (texcFreeSoundF GT i row p0 dvi dvo tq em j hrow hcf hdeps)
    (forgetConfF GT i row p0 dvi dvo tq em hrow hcf hdeps) he hx hbase hes hsite hg0
    (fun it k' hit hk hr => hrb it k' (List.mem_append_left _ hit) hk hr)
    hcov htn


end PinTrap

end Weak
