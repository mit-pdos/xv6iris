/-
Weak: **(c) [OWN.100], increment 2 — the twin candidate and its MEMBER GRAPH** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

  §1  wf-FREE member facts for any candidate (`SilMember.cdLogLenW`, `cgWixC`, `memberLogC`,
      `memberGwfC`): the candidate member's write order is its trace's, its log `cdLog`, no consistency
      needed — the registered `CertZ3.memberLogPfx`/`memberGwf` took `srvwmoConsistent` only for that;
  §2  the TWIN CANDIDATE `SilCand.CandS` (a trace with, per step, `none` or the silent position `some q`),
      its replay `SilCand.stAt` (`SilCand.nextS`: the twin step's post-state), validity `SilCand.validS`;
  §3  the PROJECTION `SilCand.proj` (a silent AMO becomes the LOAD of its read: `projLbl`) — a registered
      `Cand`, as data — whose log is the twin run's (`projLog`), and the twin member
      `CertZ3.member n (proj c)`: **`SilMember.twinLogOf`**, **`twinGwf`**, **`twinGwrowGmo`**,
      **`twinRmwLatest`** (every RMW left is a non-silent one, which read the latest bytes).

Spec: FAITHFUL (proof organisation).
-/
import Weak.SilCandLit

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. wf-free member facts -/

theorem SilMember.esMsgLen (s : Estep) :
    (esMsg s).length = if lbIsW s.esLb then 1 else 0 := by
  unfold esMsg
  cases hw : lbIsW s.esLb with
  | true =>
    obtain ⟨base, vs, hwr⟩ := lbIsWWr _ hw
    rw [hwr]; rfl
  | false => rw [CertZ22.wrNone _ hw]; rfl

theorem SilMember.cdLogLenW (c : Cand) : ∀ k, k ≤ c.cdTr.length →
    (cdLog c k).length = (((L (candExec c)).take k).filter AxViolSubsume.wp).length := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ : ∃ s, c.cdTr[k]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hL : (L (candExec c))[k]? = some (k, s) := by rw [LLookup]; rw [show (candExec c).exTr = c.cdTr from rfl, hs]; rfl
    rw [take_S_r hL, List.filter_append, List.length_append, ← ih (by omega), cdLogS c k s hs,
      List.length_append, SilMember.esMsgLen]
    cases hw : lbIsW s.esLb <;> simp [AxViolSubsume.wp, hw]

theorem SilMember.cgWixC (c : Cand) (k : Nat) (s : Estep) :
    c.cdTr[k]? = some s → lbIsW s.esLb = true →
    gwix (cg (candExec c)) (ceid (candExec c) k) = (cdLog c k).length + 1 := by
  intro hk hw
  have hlt := lookup_lt_Some hk
  rw [SilMember.cdLogLenW c k (by omega)]
  apply gwixOfLookup _ _ _ (cgNodup _)
  rw [cgGwrites, List.getElem?_map, ceidCf _ k s hk,
    filterTakeLookup AxViolSubsume.wp (L (candExec c)) k (k, s)
      (by rw [LLookup, show (candExec c).exTr = c.cdTr from rfl, hk]; rfl) hw]
  rfl

/-- **THE MEMBER'S WRITE ORDER IS THE CANDIDATE'S LOG**, for ANY candidate. -/
theorem SilMember.memberLogC (n : Nat) (c : Cand) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) →
    logOf (CertZ3.member n c) (cdLog c c.cdTr.length) := by
  intro hag
  have hlenE : (L (candExec c)).length = c.cdTr.length := by
    unfold L; rw [List.length_mapIdx]; rfl
  refine logOfOfPfx _ _ ⟨?_, ?_⟩
  · rw [CertZ3.memberGwrites n c hag, cgGwrites, List.length_map,
      SilMember.cdLogLenW c _ (Nat.le_refl _),
      List.take_of_length_le (by rw [hlenE]; exact Nat.le_refl _)]
  · intro p w _ hw
    rw [show gwriteAt (CertZ3.member n c) (p + 1) = gwriteAt (cg (candExec c)) (p + 1) by
      show (gwrites _)[p]? = (gwrites _)[p]?; rw [CertZ3.memberGwrites n c hag]] at hw
    obtain ⟨hwm, hix⟩ := gwriteAtInv _ _ _ (cgNodup _) hw
    obtain ⟨hgmo, hisw⟩ := (gwritesElemOf _ _).1 hwm
    obtain ⟨k, s, hk, -, rfl⟩ := cgSurj (candExec c) w hgmo
    obtain ⟨hlbl, hagt⟩ := cgLbl (candExec c) k s hk
    have hW : lbIsW s.esLb = true := by unfold gisW at hisw; rw [hlbl] at hisw; exact hisw
    have hix' := SilMember.cgWixC c k s hk hW
    rw [hix] at hix'
    obtain ⟨base, vs, hwr⟩ := CertZ3.lbWrOfW _ hW
    have hesm : esMsg s = [⟨base, vs, some s.esAg, lbCls s.esLb⟩] := by
      unfold esMsg; rw [hwr]
    obtain ⟨rest, hrest⟩ := cdLogSplit c (k + 1) c.cdTr.length (lookup_lt_Some hk)
    have hlog : cdLog c c.cdTr.length = cdLog c k ++ ⟨base, vs, some s.esAg, lbCls s.esLb⟩ :: rest := by
      rw [hrest, cdLogS c k s hk, hesm]
      simp
    rw [hlog, show p = (cdLog c k).length by omega, list_lookup_middle rfl]
    unfold WeakRvwmoKillArms.gmsg
    rw [CertZ3.memberLbl n c _ hag, hlbl]
    simp only [hwr, hagt]

/-- The member is well-formed given only the label shapes. -/
theorem SilMember.memberGwfC (n : Nat) (c : Cand) :
    candShape c → (∀ s, s ∈ c.cdTr → s.esAg < n) → gwf (CertZ3.member n c) := by
  intro hsh hag
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

/-! # 2. The twin candidate -/

/-- A twin candidate: a trace and, per step, `none` (an ordinary step) or `some q` (a silent AMO at
`q`). -/
structure SilCand.CandS where
  img : Image
  tr : List Estep
  sil : List (Option Nat)

def SilCand.initS (img : Image) : Mstate := ⟨img, [], fun _ => wsInit⟩

/-- The twin step's post-state. -/
def SilCand.nextS (S : Mstate) (s : Estep) (o : Option Nat) : Mstate :=
  match o, s.esLb with
  | some q, .LRmw aq _ base ts _ wvs _ => SilCand.silentNext S s.esAg aq base ts wvs q
  | _, _ => mnext S s.esAg s.esLb

/-- The twin candidate's states. -/
def SilCand.stAt (c : SilCand.CandS) : Nat → Mstate
  | 0 => SilCand.initS c.img
  | k + 1 =>
    match c.tr[k]? with
    | some s => SilCand.nextS (SilCand.stAt c k) s (c.sil.getD k none)
    | none => SilCand.stAt c k

/-- **TWIN VALIDITY**: every ordinary step is the registered machine's, every silent step a silent AMO
(not `rl`) meeting `silentOk`. -/
def SilCand.validS (c : SilCand.CandS) : Prop :=
  ∀ k s, c.tr[k]? = some s →
    (c.sil.getD k none = none → mstepOk (SilCand.stAt c k) s.esAg s.esLb) ∧
    (∀ q, c.sil.getD k none = some q →
      ∃ aq base ts rvs wvs kc, s.esLb = .LRmw aq false base ts rvs wvs kc ∧
        SilCand.silentOk (SilCand.stAt c k) s.esAg aq base ts rvs wvs q)

/-- A silent AMO's projected label: the load of its read. -/
def SilCand.projLbl (l : Lbl) : Lbl :=
  match l with
  | .LRmw aq _ base ts rvs _ _ => .LLoad aq base ts rvs
  | l => l

/-- The projected step. -/
def SilCand.projStep (s : Estep) (o : Option Nat) : Estep :=
  match o with
  | some _ => ⟨s.esAg, SilCand.projLbl s.esLb⟩
  | none => s

/-- **THE PROJECTION**: the registered candidate (as data) of the twin run. -/
def SilCand.proj (c : SilCand.CandS) : Cand :=
  ⟨c.img, c.tr.mapIdx (fun k s => SilCand.projStep s (c.sil.getD k none))⟩

theorem SilCand.projTr (c : SilCand.CandS) (k : Nat) :
    (SilCand.proj c).cdTr[k]? = (c.tr[k]?).map (fun s => SilCand.projStep s (c.sil.getD k none)) := by
  unfold SilCand.proj
  simp only [List.getElem?_mapIdx]

theorem SilCand.projLen (c : SilCand.CandS) : (SilCand.proj c).cdTr.length = c.tr.length := by
  unfold SilCand.proj; simp

/-! # 3. The projection's log and member -/

theorem SilCand.mnextLog (σ : Mstate) (i : Nat) (l : Lbl) :
    (mnext σ i l).msLog = σ.msLog ++ esMsg ⟨i, l⟩ ∧ (mnext σ i l).msImg = σ.msImg := by
  cases l <;> simp [mnext, esMsg, lbWr, lbCls]

theorem SilCand.nextSLog (S : Mstate) (s : Estep) (o : Option Nat) :
    (SilCand.nextS S s o).msLog = S.msLog ++ esMsg (SilCand.projStep s o) ∧
    (SilCand.nextS S s o).msImg = S.msImg := by
  unfold SilCand.nextS SilCand.projStep
  cases o with
  | none =>
    dsimp only
    obtain ⟨h1, h2⟩ := SilCand.mnextLog S s.esAg s.esLb
    exact ⟨h1, h2⟩
  | some q =>
    cases hl : s.esLb with
    | LRmw aq rl base ts rvs wvs kc =>
      simp [SilCand.projLbl, SilCand.silentNext, esMsg, lbWr]
    | _ =>
      dsimp only
      obtain ⟨h1, h2⟩ := SilCand.mnextLog S s.esAg s.esLb
      rw [hl] at h1 h2
      refine ⟨?_, h2⟩
      rw [h1]
      simp [SilCand.projLbl, esMsg]

/-- **THE PROJECTION'S LOG IS THE TWIN RUN'S.** -/
theorem SilCand.projLog (c : SilCand.CandS) : ∀ k, k ≤ c.tr.length →
    cdLog (SilCand.proj c) k = (SilCand.stAt c k).msLog ∧
    (SilCand.stAt c k).msImg = c.img := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ : ∃ s, c.tr[k]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hps : (SilCand.proj c).cdTr[k]? = some (SilCand.projStep s (c.sil.getD k none)) := by
      rw [SilCand.projTr, hs]; rfl
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hst : SilCand.stAt c (k + 1) = SilCand.nextS (SilCand.stAt c k) s (c.sil.getD k none) := by
      show (match c.tr[k]? with
        | some s => SilCand.nextS (SilCand.stAt c k) s (c.sil.getD k none)
        | none => SilCand.stAt c k) = _
      rw [hs]
    obtain ⟨h1, h2⟩ := SilCand.nextSLog (SilCand.stAt c k) s (c.sil.getD k none)
    rw [hst, h1, h2, cdLogS _ k _ hps, ih1]
    exact ⟨rfl, ih2⟩

theorem SilCand.projAg (c : SilCand.CandS) (n : Nat) :
    (∀ s, s ∈ c.tr → s.esAg < n) → ∀ s, s ∈ (SilCand.proj c).cdTr → s.esAg < n := by
  intro h s hs
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hs
  rw [SilCand.projTr] at hk
  cases hk' : c.tr[k]? with
  | none => rw [hk'] at hk; cases hk
  | some s0 =>
    rw [hk'] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    subst hk
    have := h s0 (List.mem_of_getElem? hk')
    unfold SilCand.projStep
    split <;> exact this

/-- The projection's label shapes, from twin validity. -/
theorem SilCand.projShape (c : SilCand.CandS) : SilCand.validS c → candShape (SilCand.proj c) := by
  intro hv k s hk
  rw [SilCand.projTr] at hk
  cases hk' : c.tr[k]? with
  | none => rw [hk'] at hk; cases hk
  | some s0 =>
    rw [hk'] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    subst hk
    obtain ⟨hold, hsil⟩ := hv k s0 hk'
    cases ho : c.sil.getD k none with
    | none =>
      have hok := hold ho
      simp only [SilCand.projStep]
      revert hok
      cases s0.esLb with
      | LLoad aq base ts vs => intro hok; exact hok.1
      | LStore rl base vs kc => intro hok; exact hok
      | LFence => intro _; trivial
      | LRmw aq rl base ts rvs wvs kc => intro hok; exact ⟨hok.1, hok.2.1, by rw [hok.2.2.1.1]⟩
      | LIo => intro _; trivial
    | some q =>
      obtain ⟨aq, base, ts, rvs, wvs, kc, hl, hok⟩ := hsil q ho
      simp only [SilCand.projStep, hl, SilCand.projLbl]
      exact hok.2.2.2.1.1

/-! ## The twin member -/

theorem SilMember.twinLogOf (n : Nat) (c : SilCand.CandS) :
    (∀ s, s ∈ c.tr → s.esAg < n) →
    logOf (CertZ3.member n (SilCand.proj c)) (cdLog (SilCand.proj c) (SilCand.proj c).cdTr.length) :=
  fun h => SilMember.memberLogC n _ (SilCand.projAg c n h)

theorem SilMember.twinGwf (n : Nat) (c : SilCand.CandS) :
    SilCand.validS c → (∀ s, s ∈ c.tr → s.esAg < n) → gwf (CertZ3.member n (SilCand.proj c)) :=
  fun hv h => SilMember.memberGwfC n _ (SilCand.projShape c hv) (SilCand.projAg c n h)

theorem SilMember.twinGwrowGmo (n : Nat) (c : SilCand.CandS) :
    (∀ s, s ∈ c.tr → s.esAg < n) → gwrowGmo (CertZ3.member n (SilCand.proj c)) :=
  fun h => CertZ3.memberGwrowGmo n _ (SilCand.projAg c n h)

/-- **THE TWIN MEMBER'S RMW ATOMICITY**: every RMW left in the projection is a non-silent one, which read
the latest bytes of the log before it. -/
theorem SilMember.twinRmwLatest (n : Nat) (c : SilCand.CandS) :
    SilCand.validS c → (∀ s, s ∈ c.tr → s.esAg < n) →
    CertZ18.rmwLatest (CertZ3.member n (SilCand.proj c))
      (cdLog (SilCand.proj c) (SilCand.proj c).cdTr.length) := by
  intro hv hag e a t v ⟨l, hl, hW⟩ ⟨l0, base, ts, vs, j, hl0, hrd, ht, hv0, ha⟩
  rw [hl, Option.some.injEq] at hl0
  subst hl0
  have hagP := SilCand.projAg c n hag
  rw [CertZ3.memberLbl n _ e hagP] at hl
  obtain ⟨k, sp, hk, hce, hsl⟩ := CertZ3.cgLblInv _ e l hl
  subst hsl
  have hkl : k < (SilCand.proj c).cdTr.length := lookup_lt_Some hk
  rw [SilCand.projTr] at hk
  cases hk' : c.tr[k]? with
  | none => rw [hk'] at hk; cases hk
  | some s0 =>
    rw [hk'] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    obtain ⟨hold, hsil⟩ := hv k s0 hk'
    -- the projected step is a write and reads: it is a non-silent RMW
    cases ho : c.sil.getD k none with
    | some q =>
      exfalso
      obtain ⟨aq, base', ts', rvs', wvs', kc, hls, -⟩ := hsil q ho
      rw [ho] at hk
      subst hk
      simp [SilCand.projStep, hls, SilCand.projLbl, lbIsW] at hW
    | none =>
      rw [ho] at hk
      subst hk
      simp only [SilCand.projStep] at hW hrd ⊢
      have hok := hold ho
      have hkk : k ≤ c.tr.length := by rw [← SilCand.projLen]; omega
      obtain ⟨hlog, himg⟩ := SilCand.projLog c k hkk
      -- the gwix of the event: its log prefix
      have hix : gwix (CertZ3.member n (SilCand.proj c)) e - 1 = (cdLog (SilCand.proj c) k).length := by
        have hsk : (SilCand.proj c).cdTr[k]? = some s0 := by
          rw [SilCand.projTr, hk', ho]; rfl
        rw [CertZ3.memberGwix n _ e hagP, ← hce, SilMember.cgWixC _ k s0 hsk hW, Nat.add_sub_cancel]
      have hpfx : (cdLog (SilCand.proj c) (SilCand.proj c).cdTr.length).take
          (gwix (CertZ3.member n (SilCand.proj c)) e - 1) = cdLog (SilCand.proj c) k := by
        obtain ⟨rest, hrest⟩ := cdLogSplit (SilCand.proj c) k _ (Nat.le_of_lt hkl)
        rw [hix, hrest, List.take_left]
      rw [hpfx, show (CertZ3.member n (SilCand.proj c)).gxImg = c.img from rfl, hlog, ← himg]
      revert hok hrd hW
      cases s0.esLb with
      | LRmw aq rl b0 ts0 rvs wvs kc =>
        intro _ hrd hok
        simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
        obtain ⟨rfl, rfl, rfl⟩ := hrd
        obtain ⟨-, -, ⟨-, hrd2⟩, hlat⟩ := hok
        rw [← ha]
        exact ⟨hlat j t ht, (hrd2 j t v ht hv0).1⟩
      | LLoad => intro hW; simp [lbIsW] at hW
      | LStore => intro _ hrd; simp [lbRd] at hrd
      | LFence => intro _ hrd; simp [lbRd] at hrd
      | LIo => intro _ hrd; simp [lbRd] at hrd

end Weak
