/-
Weak/Prom: **completeness S3b — the read of an annotated load, an LR or an AMO** (AtoP.v's read case, with
rules 5–7 and the AMO's single op, M0).

Generalisations of S3a's read lemmas (Weak/Prom/CmpSimL.lean, CmpSimLd.lean) from a plain `ld` to any LOAD
OPERATION `e` (`ld`, `lr`, `amo`; rvwmo.adoc:73–74 "an AMO … is both a load operation and a store operation") with
any annotation, each with a STRICT form when `e` is also a store (an AMO: its single op is at its write timestamp
`vo X e`, so its read point must lie strictly below it):
* `ldPre_le` — the pre-view `ldPre ws aq rl va` is below `e`'s view: the address view by rule 9, `vrNew` by the
  invariant (rules 4, 5), the release view `wVRel` (an acquire) by rule 7 through `ExtraInv.vrel`, `vrOld ⊔ vwOld`
  (a release load) by rule 6;
* `fwdView_leG` — a byte's forwarded view is below `e`'s view (rule 12 / rule 3 through the forward bank);
* `loadOk_refG` — the machine read answering the load value axiom's store is admissible;
* `kts_lt_storeG` — the answer is strictly below every later own store to the byte (rule 1);
* `loadBytes_uniG` — the byte fold with an acquire bit.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpInvB

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

/-! ## 1. Bounds through gmo -/

/-- A view dominated by events gmo-before `e` is below `e`'s view, strictly when `e` is a store. -/
theorem domF_gB {P : Nat → Prop} {v : Nat} {e : EvId} (hv : domF (fun j => vo X (h, j)) P v)
    (hg : ∀ j, P j → gB X.gmo (h, j) e = true) (he : e ∈ X.gmo) :
    v ≤ vo X e ∧ ((X.sk e).kind.isStore = true → v < vo X e) := by
  refine ⟨domF_bound hv (fun j hj => vo_le_of_gB (hg j hj)), fun hs => ?_⟩
  have := voG_st_pos X X.gmo e he hs
  exact domF_lt hv (fun j hj => vo_lt_of_gB (hg j hj) hs) (by unfold vo; omega)

/-- `vo a ≤ vo b`, strictly when `b` is a store, from `gB a b`. -/
theorem vo_of_gB {a b : EvId} (hg : gB X.gmo a b = true) :
    vo X a ≤ vo X b ∧ ((X.sk b).kind.isStore = true → vo X a < vo X b) :=
  ⟨vo_le_of_gB hg, fun hs => vo_lt_of_gB hg hs⟩

section read

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- A past event of the hart is po-before the current one. -/
theorem past_po (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {se : SEv}
    (hm : sf.evs[s.evs.length]? = some se) (hii : se.sk.ii = s.ii) {j : Nat} (hj : j < s.evs.length) :
    (h, j) ∈ X.ids ∧ poX X (h, j) (h, s.evs.length) = true := by
  obtain ⟨se', hse', hii'⟩ := past_ii hinv.wf hinv.fut hj
  exact ⟨c.id hse', c.po_of hse' hm (by omega)⟩

/-- THE PRE-VIEW OF A LOAD OPERATION IS BELOW ITS VIEW (strictly for an AMO). -/
theorem ldPre_le (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom)
    (hx : ExtraInv X h s.evs.length ws.wVRel ws.wRes) {rs1 : Nat} (hrs : rs1 < 32) {se : SEv}
    (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind.isLoad = true) (hii : se.sk.ii = s.ii)
    (hadep : se.sk.adep = (s.rd rs1).2) (aq rl : Bool) (haq : aq = true → se.sk.aqSc = true)
    (hrl : rl = true → se.sk.rlSc = true) :
    ldPre ws aq rl (srcsView ws (srcR rs1)) ≤ vo X (h, s.evs.length) ∧
      (se.sk.kind.isStore = true → ldPre ws aq rl (srcsView ws (srcR rs1)) < vo X (h, s.evs.length)) := by
  have hl := List.getElem?_eq_some_iff.1 hm
  have hsk := c.sk hm
  have hem : (X.sk (h, s.evs.length)).kind.isMem = true := by rw [hsk]; exact Kind.isMem_of_isLoad _ hld
  have heg := c.gmo_of hm (by rw [← hsk]; exact hem)
  have hst : se.sk.kind.isStore = true → (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; exact id
  -- the address view (rule 9)
  have hva := domF_gB (P := (· ∈ (s.rd rs1).2)) (domF_srcR hinv.regv hrs) (fun d hd => by
    obtain ⟨hid, hmem, hpo⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint rs1 d hd) (Nat.le_refl _) hl.1
    exact gB_of_ppo c.ref c.io hid (c.id hm) (ppo_r9 hmem hem hpo (by rw [hsk, hadep]; exact hd))) heg
  -- vrNew
  have hrn := hinv.vrNew s.evs.length (Nat.le_refl _) hl.1 (by rw [hsk]; exact hld)
  -- the release view (rule 7)
  have hvrel : (if aq then ws.wVRel else 0) ≤ vo X (h, s.evs.length) ∧
      ((X.sk (h, s.evs.length)).kind.isStore = true → (if aq then ws.wVRel else 0) < vo X (h, s.evs.length)) := by
    cases haq' : aq
    · refine ⟨Nat.zero_le _, fun hs => ?_⟩
      have := voG_st_pos X X.gmo _ heg hs; unfold vo; simp only [Bool.false_eq_true, if_false]; omega
    · simp only [if_true]
      exact domF_gB hx.vrel (fun j ⟨hj, hjm, hjr⟩ => by
        obtain ⟨hid, hpo⟩ := past_po c hinv hm hii hj
        exact gB_of_ppo c.ref c.io hid (c.id hm)
          (ppo_r7 c.io hjm hem hpo hjr (by rw [hsk]; exact haq haq'))) heg
  -- vrOld ⊔ vwOld (rule 6)
  have hold : (if rl then max ws.wVrOld ws.wVwOld else 0) ≤ vo X (h, s.evs.length) ∧
      ((X.sk (h, s.evs.length)).kind.isStore = true →
        (if rl then max ws.wVrOld ws.wVwOld else 0) < vo X (h, s.evs.length)) := by
    cases hrl' : rl
    · refine ⟨Nat.zero_le _, fun hs => ?_⟩
      have := voG_st_pos X X.gmo _ heg hs; unfold vo; simp only [Bool.false_eq_true, if_false]; omega
    · simp only [if_true]
      have hr6 : ∀ j, j < s.evs.length → (X.sk (h, j)).kind.isMem = true → gB X.gmo (h, j) (h, s.evs.length) = true :=
        fun j hj hjm => by
          obtain ⟨hid, hpo⟩ := past_po c hinv hm hii hj
          exact gB_of_ppo c.ref c.io hid (c.id hm) (ppo_r6 c.io hjm hem hpo (by rw [hsk]; exact hrl hrl'))
      have e1 := domF_gB hinv.vrOld (fun j ⟨hj, hjl⟩ => hr6 j hj (Kind.isMem_of_isLoad _ hjl)) heg
      have e2 := domF_gB hinv.vwOld (fun j ⟨hj, hjl⟩ => hr6 j hj (Kind.isMem_of_isStore _ hjl)) heg
      exact ⟨by omega, fun hs => by have := e1.2 hs; have := e2.2 hs; omega⟩
  have hifv := hinv.ifv
  unfold ldPre
  refine ⟨by omega, fun hs => ?_⟩
  have a1 := hva.2 (hst hs); have a2 := hrn.2 (hst hs); have a3 := hvrel.2 (hst hs); have a4 := hold.2 (hst hs)
  omega

/-- THE FORWARDED VIEW OF A LOAD OPERATION'S BYTE IS BELOW ITS VIEW (strictly for an AMO). -/
theorem fwdView_leG (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {se : SEv}
    (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind.isLoad = true) (hii : se.sk.ii = s.ii) (aq : Bool)
    {x : Nat} (htx : touches (X.ev (h, s.evs.length)) x = true) :
    fwdView ws aq (x : Int) (kts X (rfSrc X (h, s.evs.length) x)) ≤ vo X (h, s.evs.length) ∧
      (se.sk.kind.isStore = true →
        fwdView ws aq (x : Int) (kts X (rfSrc X (h, s.evs.length) x)) < vo X (h, s.evs.length)) := by
  have hl := List.getElem?_eq_some_iff.1 hm
  have hsl : s.evs.length ≤ sf.evs.length := hinv.fut.evs.length_le
  have hsk := c.sk hm
  have hrl : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [hsk]; exact hld
  have heg := c.gmo_of hm (Kind.isMem_of_isLoad _ hld)
  have hst : se.sk.kind.isStore = true → (X.sk (h, s.evs.length)).kind.isStore = true := by rw [hsk]; exact id
  have hpos : se.sk.kind.isStore = true → 0 < vo X (h, s.evs.length) := fun hs => by
    have := voG_st_pos X X.gmo _ heg (hst hs); unfold vo; omega
  -- the store is gmo-before the load, or it is an own po-earlier store not gmo-before it
  have hG : (kts X (rfSrc X (h, s.evs.length) x) ≤ vo X (h, s.evs.length) ∧
      (se.sk.kind.isStore = true → kts X (rfSrc X (h, s.evs.length) x) < vo X (h, s.evs.length))) ∨
      ∃ s0, rfSrc X (h, s.evs.length) x = some s0 ∧ gB X.gmo s0 (h, s.evs.length) = false := by
    cases hs0 : rfSrc X (h, s.evs.length) x with
    | none => exact .inl ⟨Nat.zero_le _, hpos⟩
    | some s0 =>
      cases hg : gB X.gmo s0 (h, s.evs.length)
      · exact .inr ⟨s0, rfl, hg⟩
      · exact .inl ⟨vo_le_of_gB hg, fun hs => vo_lt_of_gB hg (hst hs)⟩
  have hown : ∀ s0, rfSrc X (h, s.evs.length) x = some s0 → gB X.gmo s0 (h, s.evs.length) = false →
      s0.1 = h ∧ s0.2 < s.evs.length ∧ (X.sk s0).kind.isStore = true ∧ touches (X.ev s0) x = true ∧
      ∀ w ∈ X.ids, poX X s0 w = true → poX X w (h, s.evs.length) = true → writesB (X.ev w) x = false := by
    intro s0 hs0 hg
    obtain ⟨hpo, hno⟩ := srcFwd c.ref c.io hs0 hg
    obtain ⟨hsg, hsw, _⟩ := rfSrc_spec hs0
    obtain ⟨h1, h2⟩ := idx_lt_of_po c hinv (ids_of_gmo hsg c.ref) hm hii hpo
    exact ⟨h1, h2, writesB_store hsw, writesB_touches hsw, hno⟩
  have hfo := hinv.fwd x
  unfold fwdView
  revert hfo
  cases hf : get? ws.wFwd (x : Int) with
  | none =>
    intro hfo
    simp only
    rcases hG with hG | ⟨s0, hs0, hg⟩
    · exact hG
    · exfalso
      obtain ⟨h1, h2, h3, h4, _⟩ := hown s0 hs0 hg
      obtain ⟨a1, a2⟩ := s0
      simp only at h1 h2; subst a1
      rw [hfo a2 h2 h3] at h4; cases h4
  | some p =>
    obtain ⟨tf, vf⟩ := p
    rintro ⟨j0, hj0, hs0st, ht0, hlat, htf, hv⟩
    simp only
    split
    · rename_i heq
      have hj0e : sf.evs[j0]? = some sf.evs[j0] := List.getElem?_eq_getElem (by omega)
      have hj0g : (h, j0) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨c.id hj0e, Kind.isMem_of_isStore _ hs0st⟩
      have hpos0 := voG_st_pos X X.gmo (h, j0) hj0g hs0st
      have hsrc : rfSrc X (h, s.evs.length) x = some (h, j0) := by
        cases hs0 : rfSrc X (h, s.evs.length) x with
        | none => rw [hs0] at heq; simp only [kts] at heq; unfold vo at htf; omega
        | some s0 =>
          rw [hs0] at heq
          simp only [kts] at heq
          obtain ⟨hsg, hsw, _⟩ := rfSrc_spec hs0
          rw [voG_inj X X.gmo s0 (h, j0) hsg hj0g (writesB_store hsw) hs0st (by unfold vo at heq htf; omega)]
      have := hv s.evs.length (Nat.le_refl _) hl.1 hrl htx hsrc
      exact ⟨this.1, fun hs => this.2 (hst hs)⟩
    · rename_i hne
      rcases hG with hG | ⟨s0, hs0, hg⟩
      · exact hG
      · exfalso
        obtain ⟨h1, h2, h3, h4, hno⟩ := hown s0 hs0 hg
        obtain ⟨a1, js⟩ := s0
        simp only at h1 h2; subst a1
        rcases Nat.lt_trichotomy js j0 with hlt | heq | hgt
        · have hj0e : sf.evs[j0]? = some sf.evs[j0] := List.getElem?_eq_getElem (by omega)
          have hjss : s.evs[js]? = some s.evs[js] := List.getElem?_eq_getElem (by omega)
          have hj0s : s.evs[j0]? = some s.evs[j0] := List.getElem?_eq_getElem (by omega)
          have hmono := hinv.wf.iiMono js j0 _ _ hlt hjss hj0s
          have hmemjs : s.evs[js].sk.kind.isMem = true := by
            have e2 := c.sk (prefix_get hinv.fut.evs hjss)
            rw [← e2]; exact Kind.isMem_of_isStore _ h3
          have hp1 : poX X (h, js) (h, j0) = true := by
            rw [c.po (prefix_get hinv.fut.evs hjss) (prefix_get hinv.fut.evs hj0s)]
            simpa using hmono.2 hmemjs
          have hp2 : poX X (h, j0) (h, s.evs.length) = true := by
            rw [c.po (prefix_get hinv.fut.evs hj0s) hm]
            simpa [hii] using hinv.wf.iiLt j0 _ hj0s
          have hw1 := hno (h, j0) (c.id hj0e) hp1 hp2
          have hw2 : writesB (X.ev (h, j0)) x = true := by
            simp only [writesB, Bool.and_eq_true]; exact ⟨hs0st, ht0⟩
          rw [hw1] at hw2; cases hw2
        · subst heq
          apply hne
          simp only [kts, hs0, htf]
        · rw [hlat js hgt h2 h3] at h4; cases h4

/-- A LOAD OPERATION's answer is strictly below every later own store to the byte, and so is the operation
(rule 1). -/
theorem kts_lt_storeG (c : HCtx T trs ν X h sf) {se : SEv} (hm : sf.evs[s.evs.length]? = some se)
    (hld : se.sk.kind.isLoad = true) {x : Nat} (htx : touches (X.ev (h, s.evs.length)) x = true) {j : Nat}
    (hjl : j < sf.evs.length) (hjst : (X.sk (h, j)).kind.isStore = true) (hjx : touches (X.ev (h, j)) x = true)
    (hpo : poX X (h, s.evs.length) (h, j) = true) :
    kts X (rfSrc X (h, s.evs.length) x) < vo X (h, j) ∧ vo X (h, s.evs.length) < vo X (h, j) := by
  obtain ⟨hjid, hjsk, _⟩ := fut_ev c hjl
  have hrmem : (X.sk (h, s.evs.length)).kind.isMem = true := by rw [c.sk hm]; exact Kind.isMem_of_isLoad _ hld
  have hrj : gB X.gmo (h, s.evs.length) (h, j) = true :=
    gB_of_ppo c.ref c.io (c.id hm) hjid (ppo_r1 hrmem hjst hpo (overlap_of_touch htx hjx))
  have hrlt := vo_lt_of_gB hrj hjst
  refine ⟨?_, hrlt⟩
  cases hs0 : rfSrc X (h, s.evs.length) x with
  | none =>
    simp only [kts]
    have := voG_st_pos X X.gmo (h, j) (c.gmo_of (List.getElem?_eq_getElem hjl)
      (by rw [← hjsk]; exact Kind.isMem_of_isStore _ hjst)) hjst
    unfold vo; omega
  | some s0 =>
    simp only [kts]
    obtain ⟨hsg, hsw, hso⟩ := rfSrc_spec hs0
    cases hg : gB X.gmo s0 (h, s.evs.length)
    · obtain ⟨hpo0, _⟩ := srcFwd c.ref c.io hs0 hg
      have h1 : gB X.gmo s0 (h, j) = true := gB_of_ppo c.ref c.io (ids_of_gmo hsg c.ref) hjid
        (ppo_r1 (Kind.isMem_of_isStore _ (writesB_store hsw)) hjst (poX_trans hpo0 hpo)
          (overlap_of_touch (writesB_touches hsw) hjx))
      exact vo_lt_of_gB h1 hjst
    · have := vo_le_of_gB hg; omega

/-- THE MACHINE READ OF A LOAD OPERATION IS ADMISSIBLE at any pre-view below its view (strictly below, for an
AMO): every byte answered with the load value axiom's store. -/
theorem loadOk_refG (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {se : SEv}
    (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind.isLoad = true) (hpos : 0 < se.sk.sz) {vpre : Nat}
    (hpre : vpre ≤ vo X (h, s.evs.length)) (hpreS : se.sk.kind.isStore = true → vpre < vo X (h, s.evs.length)) :
    loadOk (testImg T) (memOf X) ws vpre ((X.ev (h, s.evs.length)).pa : Int)
      (uniTvs (kts X (rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa))
        ((X.ev (h, s.evs.length)).rdat.map bv8)) := by
  have hl := List.getElem?_eq_some_iff.1 hm
  have hid := c.id hm
  have hsk := c.sk hm
  have hrl : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [hsk]; exact hld
  have hrm := Kind.isMem_of_isLoad _ hrl
  have hlen := c.rdat_len hid hrl
  unfold loadOk
  apply bytesAll_uni
  intro k v hv
  rw [List.getElem?_map] at hv
  cases hk : (X.ev (h, s.evs.length)).rdat[k]? with
  | none => rw [hk] at hv; cases hv
  | some b =>
    rw [hk] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    subst hv
    have hkl : k < (X.sk (h, s.evs.length)).sz := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨x, hx⟩ : ∃ x, x = (X.ev (h, s.evs.length)).pa + k := ⟨_, rfl⟩
    have hcast : ((X.ev (h, s.evs.length)).pa : Int) + (k : Int) = (x : Int) := by rw [hx]; push_cast; rfl
    rw [hcast]
    have htx : touches (X.ev (h, s.evs.length)) x = true := by
      rw [touches_iff]; unfold Exec.sk at hkl; omega
    have htp : touches (X.ev (h, s.evs.length)) (X.ev (h, s.evs.length)).pa = true := by
      rw [touches_iff]; unfold Exec.sk at hkl; omega
    have hsrc : rfSrc X (h, s.evs.length) (X.ev (h, s.evs.length)).pa = rfSrc X (h, s.evs.length) x :=
      rfSrc_bytes c.ref c.ss hid hrm htp htx
    rw [hsrc]
    have hval := ldVal c.ref c.io hid hrl hkl
    rw [hk, ← hx] at hval
    cases hval
    refine ⟨?_, .inl ?_⟩
    · unfold lvVal
      cases hs0 : rfSrc X (h, s.evs.length) x with
      | none =>
        simp only [kts, memByte, testImg, Int.toNat_natCast]
        rw [c.img]
      | some w =>
        obtain ⟨hwg, hww, _⟩ := rfSrc_spec hs0
        simp only [kts]
        exact memByte_st c.ref _ hwg (writesB_store hww) (writesB_touches hww)
    · intro hwr
      obtain ⟨w, hwg, hws, hww, hlo, hhi⟩ := writesIn_memOf c.ref hwr
      have hnf := nonFwdMax_uni_le ws (kts X (rfSrc X (h, s.evs.length) x))
        ((X.ev (h, s.evs.length)).rdat.map bv8) ((X.ev (h, s.evs.length)).pa : Int)
      have hcases : vo X w ≤ coh ws x ∨ vo X w ≤ vpre ∨ vo X w ≤ kts X (rfSrc X (h, s.evs.length) x) := by
        revert hhi
        split <;> intro hhi <;> omega
      rcases hcases with h1 | h1 | h1
      · have := hinv.coh2 x s.evs.length (Nat.le_refl _) hl.1 hrl htx w hwg hww h1
        omega
      · by_cases hwe : w = (h, s.evs.length)
        · subst hwe
          have := hpreS (by rw [← hsk]; exact hws)
          omega
        · have hgB : gB X.gmo w (h, s.evs.length) = true :=
            gB_of_voG_le X X.gmo w _ hwg hws (c.gmo_of hm (Kind.isMem_of_isLoad _ hld)) (by unfold vo at hpre h1; omega)
              hwe
          have := kts_ge c.ref hwg hww (.inl hgB)
          omega
      · omega

end read

/-! ## 2. The byte fold with an acquire bit -/

theorem loadBytes_uniG (aq : Bool) (vpre t : Nat) :
    ∀ (vs : List (BitVec 8)) (ws : PState) (a : Int),
      (loadBytes aq vpre ws a (uniTvs t vs)).wFwd = ws.wFwd ∧
      (loadBytes aq vpre ws a (uniTvs t vs)).wRegv = ws.wRegv ∧
      (loadBytes aq vpre ws a (uniTvs t vs)).wVcap = ws.wVcap ∧
      (loadBytes aq vpre ws a (uniTvs t vs)).wVRel = ws.wVRel ∧
      (loadBytes aq vpre ws a (uniTvs t vs)).wVwOld = ws.wVwOld ∧
      (loadBytes aq vpre ws a (uniTvs t vs)).wIfv = ws.wIfv ∧
      (loadBytes aq vpre ws a (uniTvs t vs)).wRes = ws.wRes ∧
      (∀ B, (∀ k, k < vs.length → max vpre (fwdView ws aq (a + k) t) ≤ B) →
        (loadBytes aq vpre ws a (uniTvs t vs)).wVrOld ≤ max ws.wVrOld B ∧
        (loadBytes aq vpre ws a (uniTvs t vs)).wLdv ≤ max ws.wLdv B ∧
        (loadBytes aq vpre ws a (uniTvs t vs)).wVrNew ≤ max ws.wVrNew (if aq then B else 0) ∧
        (loadBytes aq vpre ws a (uniTvs t vs)).wVwNew ≤ max ws.wVwNew (if aq then B else 0)) ∧
      (∀ b : Int, coh (loadBytes aq vpre ws a (uniTvs t vs)) b = coh ws b ∨
        ∃ k, k < vs.length ∧ b = a + k ∧
          coh (loadBytes aq vpre ws a (uniTvs t vs)) b = max (coh ws b) (max (max vpre (fwdView ws aq b t)) t))
  | [], ws, a => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun B _ => ⟨by simp [uniTvs, loadBytes]; omega,
      by simp [uniTvs, loadBytes]; omega, by simp [uniTvs, loadBytes]; omega, by simp [uniTvs, loadBytes]; omega⟩,
      fun b => .inl rfl⟩
  | v :: vs, ws, a => by
    have hcons : loadBytes aq vpre ws a (uniTvs t (v :: vs)) =
        loadBytes aq vpre (loadByte ws aq vpre a t) (a + 1) (uniTvs t vs) := rfl
    obtain ⟨i1, i2, i3, i4, i5, i8, iR, i9, i10⟩ := loadBytes_uniG aq vpre t vs (loadByte ws aq vpre a t) (a + 1)
    have hfv : ∀ b, fwdView (loadByte ws aq vpre a t) aq b t = fwdView ws aq b t := fun b => rfl
    rw [hcons]
    refine ⟨i1, i2, i3, i4, i5, i8, iR, fun B hB => ?_, fun b => ?_⟩
    · have h0 := hB 0 (by simp)
      rw [show a + ((0 : Nat) : Int) = a by omega] at h0
      obtain ⟨j1, j2, j3, j4⟩ := i9 B (fun k hk => by
        rw [hfv]
        have := hB (k + 1) (by simp; omega)
        rwa [show a + ((k + 1 : Nat) : Int) = a + 1 + (k : Int) by push_cast; omega] at this)
      have e1 : (loadByte ws aq vpre a t).wVrOld = max ws.wVrOld (max vpre (fwdView ws aq a t)) := rfl
      have e2 : (loadByte ws aq vpre a t).wLdv = max ws.wLdv (max vpre (fwdView ws aq a t)) := rfl
      have e3 : (loadByte ws aq vpre a t).wVrNew =
          if aq then max ws.wVrNew (max vpre (fwdView ws aq a t)) else ws.wVrNew := rfl
      have e4 : (loadByte ws aq vpre a t).wVwNew =
          if aq then max ws.wVwNew (max vpre (fwdView ws aq a t)) else ws.wVwNew := rfl
      rw [e1] at j1; rw [e2] at j2; rw [e3] at j3; rw [e4] at j4
      cases aq
      · simp only [Bool.false_eq_true, if_false] at j3 j4 ⊢
        exact ⟨by omega, by omega, by omega, by omega⟩
      · simp only [if_true] at j3 j4 ⊢
        exact ⟨by omega, by omega, by omega, by omega⟩
    · have hc1 : coh (loadByte ws aq vpre a t) b =
          if a = b then max (coh ws a) (max (max vpre (fwdView ws aq a t)) t) else coh ws b :=
        coh_insert ws a b _
      rcases i10 b with h | ⟨k, hk, hb, hc⟩
      · rw [h, hc1]
        by_cases hab : a = b
        · subst hab; rw [if_pos rfl]
          exact .inr ⟨0, by simp, by simp, rfl⟩
        · rw [if_neg hab]; exact .inl rfl
      · have hab : a ≠ b := by omega
        rw [hc, hc1, if_neg hab, hfv]
        exact .inr ⟨k + 1, by simp; omega, by rw [hb]; push_cast; omega, rfl⟩

end Weak.Prom.Cmp
