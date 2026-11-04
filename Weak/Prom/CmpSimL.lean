/-
Weak/Prom: **completeness S3a — simulating a plain load** (AtoP.v's read case).

The machine load answers every byte with the timestamp of the store the load value axiom selects (`kts (rfSrc …)`;
NA-6 makes it the same store for every byte) and the reference's byte.  The read is admissible (`loadOk_ref`): a
write between the answer and the read floor would be a candidate of the load value axiom later in gmo than its
store — below the coherence floor by `coh2`, below the pre-view because the pre-view is below the load's view
(`load_pre_le`: rules 4, 9 through `vrNew` and the address taint).  The post-view is below the load's view
(`fwdView_le_vo`: a forwarded byte through the forward bank's rule-12 bound, a non-forwarded one because its store is
gmo-before the load, `srcFwd`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSimF

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

/-! ## 1. Arithmetic of loaded values -/

theorem bytesVal_lt : ∀ (l : List Nat), (∀ b ∈ l, b < 256) → bytesVal l < 2 ^ (8 * l.length)
  | [], _ => by simp [bytesVal]
  | b :: l, h => by
    have hb := h b (List.mem_cons_self ..)
    have ih := bytesVal_lt l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hbv : bytesVal (b :: l) = b + 256 * bytesVal l := rfl
    rw [hbv, List.length_cons, show 8 * (l.length + 1) = 8 * l.length + 8 by omega, Nat.pow_add]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]
    have h1 : 256 * bytesVal l ≤ 256 * (2 ^ (8 * l.length) - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : 256 * (2 ^ (8 * l.length) - 1) = 2 ^ (8 * l.length) * 256 - 256 := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    omega

theorem pow_le_two64 {sz : Nat} (h : sz ≤ 8) : 2 ^ (8 * sz) ≤ two64 := by
  have : two64 = 2 ^ 64 := rfl
  rw [this]; exact Nat.pow_le_pow_right (by decide) (by omega)

theorem sext_lt {sz v : Nat} (hsz : sz ≤ 8) (hv : v < 2 ^ (8 * sz)) : sext sz v < two64 := by
  have hp := pow_le_two64 hsz
  unfold sext
  split <;> omega

theorem bv8_toNat (b : Nat) (hb : b < 256) : (bv8 b).toNat = b := by
  simp [bv8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem map_bv8_toNat : ∀ (l : List Nat), (∀ b ∈ l, b < 256) → (l.map bv8).map BitVec.toNat = l
  | [], _ => rfl
  | b :: l, h => by
    simp only [List.map_cons]
    rw [bv8_toNat b (h b (List.mem_cons_self ..)), map_bv8_toNat l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem szOk_le {sz : Nat} (h : szOk sz = true) : 0 < sz ∧ sz ≤ 8 := by
  simp only [szOk, Bool.or_eq_true, beq_iff_eq] at h
  omega

/-- The register value of a load, machine side = reference side. -/
theorem ldVal_eq {rdat : List Nat} {sz : Nat} (hl : rdat.length = sz) (hb : ∀ b ∈ rdat, b < 256) (hsz : sz ≤ 8)
    (sgn : Bool) (e : EvId) (ν : Val) (hν : ν e = rdat) :
    (if sgn then sext sz (ofBytes (rdat.map bv8)) else ofBytes (rdat.map bv8)) % two64 = (Ex.ld e sz sgn).eval ν ∧
    (Ex.ld e sz sgn).eval ν < two64 := by
  have hof : ofBytes (rdat.map bv8) = bytesVal rdat := by unfold ofBytes; rw [map_bv8_toNat rdat hb]
  have hlt : bytesVal rdat < 2 ^ (8 * sz) := hl ▸ bytesVal_lt rdat hb
  have hev : (Ex.ld e sz sgn).eval ν = if sgn then sext sz (bytesVal rdat) else bytesVal rdat := by
    simp only [Ex.eval, hν, ← hl, List.take_length]
    rw [Nat.mod_eq_of_lt (hl ▸ hlt)]
  have hlt64 : bytesVal rdat < two64 := Nat.lt_of_lt_of_le hlt (pow_le_two64 hsz)
  rw [hof, hev]
  cases sgn
  · simp only [Bool.false_eq_true, if_false]; exact ⟨Nat.mod_eq_of_lt hlt64, hlt64⟩
  · simp only [if_true]; exact ⟨Nat.mod_eq_of_lt (sext_lt hsz hlt), sext_lt hsz hlt⟩

/-! ## 2. The read -/

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

section load

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

/-- An event of `X`'s hart `h` that is po-before the event at index `n` (the current one) has a smaller index. -/
theorem idx_lt_of_po (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {e : EvId}
    (he : e ∈ X.ids) {se : SEv} (hm : sf.evs[s.evs.length]? = some se) (hii : se.sk.ii = s.ii)
    (hpo : poX X e (h, s.evs.length) = true) : e.1 = h ∧ e.2 < s.evs.length := by
  have he1 : e.1 = h := by simp only [poX, poS, Bool.and_eq_true, beq_iff_eq] at hpo; exact hpo.1
  refine ⟨he1, ?_⟩
  obtain ⟨e1, e2⟩ := e
  simp only at he1; subst he1
  rcases Nat.lt_or_ge e2 s.evs.length with hl | hl
  · exact hl
  · exfalso
    rw [c.xc, conc_ids] at he
    obtain ⟨l, hl1, hl2⟩ := (mem_idsOf _ _).1 he
    simp only [List.getElem?_map, c.tr, Option.map_some, Option.some.injEq] at hl1
    subst hl1
    have hse2 : sf.evs[e2]? = some sf.evs[e2] := List.getElem?_eq_getElem hl2
    have hlat := (hinv.fut.later e2 _ hl hse2).1
    rw [c.po hse2 hm] at hpo
    simp at hpo
    omega

/-- THE LOAD'S PRE-VIEW IS BELOW ITS VIEW (rules 4 through `vrNew`, 9 through the address taint). -/
theorem load_pre_le (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {rs1 : Nat} (hrs : rs1 < 32)
    {se : SEv} (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind = .ld) (hadep : se.sk.adep = (s.rd rs1).2) :
    ldPre ws false false (srcsView ws (srcR rs1)) ≤ vo X (h, s.evs.length) := by
  have hl := List.getElem?_eq_some_iff.1 hm
  have hva : srcsView ws (srcR rs1) ≤ vo X (h, s.evs.length) := by
    refine domF_bound (domF_srcR hinv.regv hrs) (fun d hd => ?_)
    obtain ⟨hid, hmem, hpo⟩ := pf_po c hinv.wf hinv.fut (hinv.wf.taint rs1 d hd) (Nat.le_refl _) hl.1
    have hd' : d ∈ (X.sk (h, s.evs.length)).adep := by rw [c.sk hm, hadep]; exact hd
    exact vo_le_of_gB (gB_of_ppo c.ref c.io hid (c.id hm)
      (ppo_r9 hmem (by rw [c.sk hm, hld]; rfl) hpo hd'))
  have hrn := (hinv.vrNew s.evs.length (Nat.le_refl _) hl.1 (by rw [c.sk hm, hld]; rfl)).1  -- S3b: `.1`
  have hifv := hinv.ifv
  simp only [ldPre, Bool.false_eq_true, if_false]
  omega

/-- THE FORWARDED VIEW OF A LOAD'S BYTE IS BELOW ITS VIEW (rule 12 through the forward bank; otherwise the store
is gmo-before the load, `srcFwd`). -/
theorem fwdView_le_vo (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {se : SEv}
    (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind = .ld) (hii : se.sk.ii = s.ii) {x : Nat}
    (htx : touches (X.ev (h, s.evs.length)) x = true) :
    fwdView ws false (x : Int) (kts X (rfSrc X (h, s.evs.length) x)) ≤ vo X (h, s.evs.length) := by
  have hl := List.getElem?_eq_some_iff.1 hm
  have hsl : s.evs.length ≤ sf.evs.length := hinv.fut.evs.length_le
  have hrl : (X.sk (h, s.evs.length)).kind.isLoad = true := by rw [c.sk hm, hld]; rfl
  -- the store is gmo-before the load, or it is an own po-earlier store not gmo-before it
  have hG : kts X (rfSrc X (h, s.evs.length) x) ≤ vo X (h, s.evs.length) ∨
      ∃ s0, rfSrc X (h, s.evs.length) x = some s0 ∧ gB X.gmo s0 (h, s.evs.length) = false := by
    cases hs0 : rfSrc X (h, s.evs.length) x with
    | none => exact .inl (Nat.zero_le _)
    | some s0 =>
      cases hg : gB X.gmo s0 (h, s.evs.length)
      · exact .inr ⟨s0, rfl, hg⟩
      · exact .inl (vo_le_of_gB hg)
  -- facts of such an own store
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
      -- the load reads the bank's store
      have hj0e : sf.evs[j0]? = some sf.evs[j0] := List.getElem?_eq_getElem (by omega)
      have hj0g : (h, j0) ∈ X.gmo := (mem_gmo c.ref _).2 ⟨c.id hj0e, Kind.isMem_of_isStore _ hs0st⟩
      have hpos := voG_st_pos X X.gmo (h, j0) hj0g hs0st
      have hsrc : rfSrc X (h, s.evs.length) x = some (h, j0) := by
        cases hs0 : rfSrc X (h, s.evs.length) x with
        | none => rw [hs0] at heq; simp only [kts] at heq; unfold vo at htf; omega
        | some s0 =>
          rw [hs0] at heq
          simp only [kts] at heq
          obtain ⟨hsg, hsw, _⟩ := rfSrc_spec hs0
          rw [voG_inj X X.gmo s0 (h, j0) hsg hj0g (writesB_store hsw) hs0st (by unfold vo at heq htf; omega)]
      exact (hv s.evs.length (Nat.le_refl _) hl.1 hrl htx hsrc).1  -- S3b: `.1`
    · rename_i hne
      rcases hG with hG | ⟨s0, hs0, hg⟩
      · exact hG
      · exfalso
        obtain ⟨h1, h2, h3, h4, hno⟩ := hown s0 hs0 hg
        obtain ⟨a1, js⟩ := s0
        simp only at h1 h2; subst a1
        rcases Nat.lt_trichotomy js j0 with hlt | heq | hgt
        · -- the bank's store is po-between
          have hjse : sf.evs[js]? = some sf.evs[js] := List.getElem?_eq_getElem (by omega)
          have hj0e : sf.evs[j0]? = some sf.evs[j0] := List.getElem?_eq_getElem (by omega)
          obtain ⟨sej, hsej, hiij⟩ := past_ii hinv.wf hinv.fut hj0
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

/-- A load's store is strictly below every later store to the byte (rule 1; for an own source, rule 1 between the
two stores). -/
theorem kts_lt_store (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {se : SEv}
    (hm : sf.evs[s.evs.length]? = some se) (hld : se.sk.kind = .ld) (hii : se.sk.ii = s.ii) {x : Nat}
    (htx : touches (X.ev (h, s.evs.length)) x = true) {j : Nat} (hj : s.evs.length < j) (hjl : j < sf.evs.length)
    (hjst : (X.sk (h, j)).kind.isStore = true) (hjx : touches (X.ev (h, j)) x = true)
    (hjii : s.ii < sf.evs[j].sk.ii) :
    kts X (rfSrc X (h, s.evs.length) x) < vo X (h, j) ∧ vo X (h, s.evs.length) < vo X (h, j) := by
  obtain ⟨hjid, hjsk, _⟩ := fut_ev c hjl
  have hpo : poX X (h, s.evs.length) (h, j) = true := c.po_of hm (List.getElem?_eq_getElem hjl) (by omega)
  have hrmem : (X.sk (h, s.evs.length)).kind.isMem = true := by rw [c.sk hm, hld]; rfl
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

end load

end Weak.Prom.Cmp
