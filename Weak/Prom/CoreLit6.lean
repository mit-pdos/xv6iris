/-
Weak/Prom: **row 6, OOTA-42, proved IN THE LOGIC through a ⟦·⟧ protocol** (stage S2; plan rev 7 §5 row 6,
§2 "What ⟦·⟧ is for", §8 S2 "row 6 proved through a ⟦·⟧ protocol (not M-facts)").

Row 2's code (`Lit.oota42` = `Lit.lbdd` with the outcome `a0 = a1 = 42`, Promising'17's out-of-thin-air example).
The proof uses NO trace invariant (Ψ = `True`) and no M-fact: only the protocol family
  `πZero`: every message's bytes are 0 (`okMsg`), and the image is 0 everywhere (`okImg`)
— "x, y ∈ {0}" (the only locations the program writes are x and y).
* Each hart proves the FULFIL obligation `⟦pv⟧ proto(data)` modularly: its load's bytes `(t_j, v_j)` have
  `t_j ≤ wLdv ≤ regv a0 ≤ vd ≤ pv` ((X4)–(X6)), so under `Valid(pv)` every `v_j` is 0 (the image's or a valid
  message's byte), hence the stored value is 0.  This is OOTA-safe exactly because the dependency is syntactic: the
  guard index is the store's own pre-view (plan §2: "That knowledge can justify a write only if the write's
  pre-view is at least s").
* A0 (iv) gives `Valid πZero img M |M|`, A0 (v) `traceWf`; so every load-like answer of every valid run is 0, and
  `run.obsLoad 0 0 = some 42` is impossible.  Exports used: (iv), (v).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLit5

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- THE PROTOCOL of row 6: every stored byte is 0, and the image is 0. -/
def πZero : Proto := ⟨fun m => ∀ b ∈ m.data, b = 0, fun img => ∀ a, img a = some 0⟩

theorem byteAt_mem {m : PMsg} {a : Int} {b : BitVec 8} (h : m.byteAt a = some b) : b ∈ m.data := by
  unfold PMsg.byteAt at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

/-- Under `Valid πZero … V`, every byte at a timestamp `≤ V` is 0. -/
theorem valid_byte {img : Image} {M : List PMsg} {V t : Nat} {a : Int} {v : BitVec 8}
    (hv : Valid πZero img M V) (ht : t ≤ V) (hb : memByte img M t a = some v) : v = 0 := by
  cases t with
  | zero =>
    simp only [memByte] at hb
    have := hv.1 a
    rw [hb] at this
    exact Option.some.inj this
  | succ k =>
    simp only [memByte] at hb
    obtain ⟨m, hm, hmb⟩ := Option.bind_eq_some_iff.1 hb
    have hk : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
    exact hv.2 (k + 1) (by omega) (by omega) m hm v (byteAt_mem hmb)

theorem bytesAll_and' {P Q : Int → Nat → BitVec 8 → Prop} :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll P a l → bytesAll Q a l →
      bytesAll (fun a t v => P a t v ∧ Q a t v) a l
  | _, [], _, _ => trivial
  | a, (t, v) :: r, ⟨h1, h2⟩, ⟨k1, k2⟩ => ⟨⟨h1, k1⟩, bytesAll_and' (a + 1) r h2 k2⟩

theorem bytesAll_vals {P : Int → Nat → BitVec 8 → Prop} (hP : ∀ a t v, P a t v → v = 0) :
    ∀ (a : Int) (l : List (Nat × BitVec 8)), bytesAll P a l → ∀ tv ∈ l, tv.2 = 0
  | _, [], _, tv, h => by cases h
  | a, (t, v) :: r, ⟨h1, h2⟩, tv, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hP a t v h1
    · exact bytesAll_vals hP (a + 1) r h2 tv h

theorem ofBytes_zero : ∀ (l : List (Nat × BitVec 8)), (∀ tv ∈ l, tv.2 = 0) → ofBytes (l.map Prod.snd) = 0
  | [], _ => rfl
  | tv :: r, h => by
    have h0 := h tv (List.mem_cons_self ..)
    have ih := ofBytes_zero r (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [ofBytes, bytesVal, List.map_cons, List.foldr_cons] at ih ⊢
    rw [h0, ih]; rfl

theorem obsOf_zero_all : ∀ (l : List (Nat × BitVec 8)), (∀ tv ∈ l, tv.2 = 0) → obsOf l = 0
  | [], _ => rfl
  | tv :: r, h => by
    have h0 := h tv (List.mem_cons_self ..)
    have ih := obsOf_zero_all r (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [obsOf, List.foldr_cons] at ih ⊢
    rw [h0, ih]; rfl

theorem loadLike_reads {l : PLabel} {tvs : List (Nat × BitVec 8)} (h : loadLikeTvs l = some tvs) :
    ∃ base, labelReads l = some (base, tvs) := by
  cases l <;> simp [loadLikeTvs] at h <;> subst h <;> exact ⟨_, rfl⟩

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **The OOTA-42 hart in the logic**: `lw a0,(x); sw a0,(y)` against the protocol "every byte is 0"; the store's
obligation `⟦pv⟧ (data = 0)` is discharged at the store's own pre-view, which covers every byte the load read. -/
theorem oota_hart (s0 : LP) (x y : Nat) (img : Image) (M : List PMsg) (h : Nat)
    (hprog : s0.prog = [.load 4 true 5 6 0, .store 4 5 8 0]) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : 5 < s0.regs.length)
    (hx : s0.rd 6 = x) (hy : s0.rd 8 = y) (hxa : x % 4 = 0) (hya : y % 4 = 0) (hxl : x < two64)
    (hyl : y < two64) :
    ⊢@{IProp GF} wpPF πZero ⟨litStep, litDone, img, M, h⟩ (fun _ => True) s0
      (fun _ => iprop(⌜∃ V, grd πZero img M V True⌝)) := by
  unfold wpPF
  iintro %γ %P0 %_ Hst
  have hxa' : aligned ((s0.rd 6 + 0) % two64) 4 = true := by
    rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]; simp [aligned, hxa]
  have hxx : (((s0.rd 6 + 0) % two64 : Nat) : Int) = (x : Int) := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  iapply (wpH_load (s := s0) (aq := false) (rl := false) (base := (x : Int)) (asrc := [.DReg 6])
    (k := ldS1 s0 5) (C := fun tvs => tvs.length = 4) (litDone_pc (by rw [hprog, hpc]; decide))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq (by rw [hprog, hpc]; rfl) hxa' (anyFab_lit.1 hs)
      exact ⟨tvs, by rw [h1, hxx]; rfl, h2, h3⟩))
  iframe Hst
  inext
  iintro %tvs %_ %hlo _
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro trivial⟩
  iintro Hst
  have hq1 : (ldS1 s0 5 tvs).q = LRegW 5 [.DLdRes] :: [LInstr] := by simp [regWL]
  iapply (wpH_regw (s := ldS1 s0 5 tvs) (rd := 5) (srcs := [.DLdRes]) (litDone_q (by rw [hq1]; simp))
    (fun l s' hs => litNext_q hq1 (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro trivial⟩
  iintro Hst
  iapply (wpH_instr (s := { ldS1 s0 5 tvs with q := [LInstr] })
    (litDone_q (s := { ldS1 s0 5 tvs with q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro trivial⟩
  iintro Hst
  have hy3 : ({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 8 = y := by
    rw [← hy]; exact lp_rd_wr (r := 8) (r' := 5) (by decide)
  have hya' : aligned ((({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 8 + 0) % two64) 4 = true := by
    rw [hy3, Nat.add_zero, Nat.mod_eq_of_lt hyl]; simp [aligned, hya]
  have hyy : (((({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 8 + 0) % two64 : Nat) : Int)
      = (y : Int) := by rw [hy3, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  have hr5 : ({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 5 =
      (if true then sext 4 (ofBytes (tvs.map Prod.snd)) else ofBytes (tvs.map Prod.snd)) % two64 :=
    lp_rd_wr_self (s := s0) (by decide) hlen
  iapply (wpH_store (s := { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] }) (aq := false) (rl := false)
    (base := (y : Int)) (data := toBytes (({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 5) 4)
    (asrc := [.DReg 8]) (vsrc := [.DReg 5])
    (k := { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with pc := s0.pc + 1 + 1, q := [LInstr] })
    (litDone_pc (s := { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] }) (by simp [ldS1, hprog, hpc]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store (s := { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] })
        (sz := 4) (rs2 := 5) (rs1 := 8) (off := 0) rfl (by simp [ldS1, hprog, hpc]) hya' (anyFab_lit.1 hs)
      exact ⟨by rw [h1, hyy]; rfl, h2⟩))
  iframe Hst
  inext
  iintro %ts %_ %_ %_ %_ _
  -- THE ⟦pv⟧ OBLIGATION: under `Valid(pv)` every byte the load read is 0, so the stored value is 0
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro trivial⟩
  isplitr
  · ipureintro
    intro hv
    have hv' : Valid πZero img M (loadRun psInit false false (srcsView psInit [.DReg 6]) (x : Int) tvs).wLdv := by
      refine hv.mono ?_
      refine Nat.le_trans ?_ (store_ext _ _ _ _ _)
      refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      simp only [srcsView, List.foldr, dsrcView, regv, lookupInsert, Option.getD_some]
      omega
    have hbnd : ∀ a t (v : BitVec 8), fwdView psInit false a t ≤
        (loadRun psInit false false (srcsView psInit [.DReg 6]) (x : Int) tvs).wLdv →
        memByte img M t a = some v → v = 0 := by
      intro a t v hle hm
      rw [fwdView_of_not (fwdHit_empty lookupEmpty)] at hle
      exact valid_byte hv' hle hm
    have hall := bytesAll_vals (fun a t v (h : _ ∧ _) => hbnd a t v h.1 h.2.1) (x : Int) tvs
      (bytesAll_and' _ _ (loadRun_ldv psInit false false (srcsView psInit [.DReg 6]) (x : Int) tvs) hlo)
    have h0 : ({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 5 = 0 := by
      rw [hr5, ofBytes_zero tvs hall]; decide
    intro b hb
    change b ∈ toBytes (({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 5) 4 at hb
    rw [h0] at hb
    have hz : ∀ b ∈ toBytes 0 4, b = 0 := by decide
    exact hz b hb
  iintro Hst
  iapply (wpH_instr (s := { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with
      pc := s0.pc + 1 + 1, q := [LInstr] })
    (litDone_q (s := { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with
      pc := s0.pc + 1 + 1, q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro trivial⟩
  iintro Hst
  iapply (wpH_done (v := ()) (s := { { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with
      pc := s0.pc + 1 + 1, q := [LInstr] } with q := [] }) (by simp [litDone, ldS1, hprog, hpc])
    (fun l s' hs => by
      rw [anyFab_lit, litNext_end rfl (by simp [ldS1, hprog, hpc])] at hs; cases hs))
  iframe Hst
  iintro _
  imodintro
  ipureintro
  exact ⟨0, grd_intro trivial⟩

end hart

open Weak.Prom.Ref.Lit (X Y)

/-- **ROW 6, OOTA-42: FORBIDDEN, in the logic, through the ⟦·⟧ protocol "every byte is 0"** (no trace invariant,
no M-fact).  Over every final memory and every valid run of machine v2: neither hart's 0th load returns 42. -/
theorem lit_oota42 : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.oota42) () (progs Weak.Prom.Ref.Lit.oota42) M run →
    ¬ (run.obsLoad 0 0 = some 42 ∧ run.obsLoad 1 0 = some 42) := by
  intro M run hrun
  have hlen : (progs Weak.Prom.Ref.Lit.oota42).length = 2 := rfl
  obtain ⟨_, _, _, _, hValid, hwf, _⟩ := adequacy (hlc := HasLC.hasLC) (GF := pfGF) (pdone := litDone)
    πZero (fun _ _ => True) (fun _ _ => True) (fun _ => rfl) (PO_ad_all _ _ _) (fun _ => trivial) (devFree_lit _)
    (fun h p hp _ => by
      match h, hp with
      | 0, hp =>
        rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
        cases hp
        exact oota_hart _ X Y _ M 0 rfl rfl rfl (Nat.lt_of_lt_of_le (by decide : 5 < 32) (Nat.le_of_eq rfl))
          rfl rfl (by decide) (by decide) (by decide) (by decide)
      | 1, hp =>
        rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
        cases hp
        exact oota_hart _ Y X _ M 1 rfl rfl rfl (Nat.lt_of_lt_of_le (by decide : 5 < 32) (Nat.le_of_eq rfl))
          rfl rfl (by decide) (by decide) (by decide) (by decide)
      | n + 2, hp =>
        rw [List.getElem?_eq_none (by rw [hlen]; omega)] at hp
        cases hp) hrun
  rintro ⟨ho0, _⟩
  obtain ⟨tvs, htvs, hval⟩ := Option.map_eq_some_iff.1 ho0
  obtain ⟨e, he, hel⟩ := List.mem_filterMap.1 (List.mem_of_getElem? htvs)
  obtain ⟨base, hrd⟩ := loadLike_reads hel
  have hb := (hwf 0 e he).1 base tvs hrd
  rw [validRun_img hrun.1] at hb
  have hall := bytesAll_vals (fun a t v hm => valid_byte hValid (memByte_le hm) hm) base tvs hb
  rw [obsOf_zero_all tvs hall] at hval
  cases hval

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_oota42
