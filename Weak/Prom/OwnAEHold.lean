/-
Weak/Prom: **E-a: a RACY NON-HOLDER READ through the core's ⟦t⟧-guarded protocol facts, with the dead set empty**
(stage E-a; G4-review.md §5 A-1 "non-owner racy reads via the core's ⟦t⟧ protocol facts (never exercised at G4)",
§6 condition 1 "a row-1 racy read via the ⟦t⟧ route"; plan rev 7 §2 "Rules for ⟦·⟧", LOAD "each byte j comes with
… the protocol fact ⟦t_j⟧ proto(v_j)", §3 "The xv6 sites that need this are racy reads that drive a branch").

The test is G4 (3)'s (OwnAHold.lean, reused: `t3`, hart 0 = xv6's lock operations writing the lock word and the
cpu field; hart 1 = acquire's `holding()` panic test, a NON-HOLDER reading both racily).  `own_holdE` proves
`own_hold`'s statement — hart 1 never stores to the panic marker — with:
* NO DEAD SET (`Dd := fun _ => False`) and NO CONTENT CLASSIFICATION of the read: the bytes hart 1 reads are
  OWNED BY HART 0 (it holds their `pend`s), so hart 1 can neither doom nor see them as resources;
* THE PROTOCOL `π3` (plan §0 `Proto`, "protocol_{loc}(val)"): a message touching the cpu field is an 8-byte
  message at the field holding `0` or `0x3000` (hart 0's `mycpu()`).  Hart 0 PROVES it at each of its fulfils
  (`stepOk`'s `⟦pv⟧ proto(M[t])`), outright;
* THE RACY READ (`pc_readE`): each byte `j` of hart 1's cpu-field load, read from `t_j`, comes with
  `⟦t_j⟧ proto(M[t_j])` (`grd_self`), so the loaded value is `⟦|M|⟧ (0 ∨ 0x3000)`.  The branch is then taken on
  the ACTUAL value: if it is `0x3100` (hart 1's cpu) hart 1 runs the panic store holding `⟦|M|⟧ False`, which
  discharges its trace invariant (guarded, plan §2 [R2.6]) while it still fulfils the store from its own marker
  bag; `adequacyA` removes the guard with `Valid(|M|)` at the end.  Nothing is doomed; no frontier is needed.
0 named inputs; loop-free.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEBase

namespace Weak.Prom.OA.EH

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.OA.C (Pc wpKA_alu alg_pc base_pc msgAt_of)
open Weak.Prom.OA.H (Fp p3o p3h b3o b3h t3 xs3 p3o_at p3h_at w3 mA mC1 mC0 mR noF qs3 noF_nil noF_snoc
  noF_of_memEv okB ld_nonF q0 bS bF bS_take bF_take shp shp_of shp_ne shp_F progs_3)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The protocol -/

/-- **THE PROTOCOL of the cpu field**: a message touching it is an 8-byte message at it holding `0` or `0x3000`. -/
def π3 : Proto :=
  ⟨fun m => tchB m Pc 8 = true → m.pa = Pc ∧ (m.data = toBytes 0 8 ∨ m.data = toBytes 0x3000 8), fun _ => True⟩

theorem ok3_pcv {v : Nat} {tid : Option Nat} {c : PClass} (hv : v = 0 ∨ v = 0x3000) :
    π3.okMsg ⟨Pc, toBytes v 8, tid, c⟩ := fun _ => ⟨rfl, by rcases hv with rfl | rfl <;> simp⟩

theorem ok3_lk {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length ≤ 16) :
    π3.okMsg ⟨Lk, d, tid, c⟩ := fun ht => by
  rw [tchB_far (.inl (by simp only [Pc]; omega))] at ht; cases ht

theorem ok3_fp {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} : π3.okMsg ⟨Fp, d, tid, c⟩ := fun ht => by
  rw [tchB_far (.inr (by simp [Pc, Lk, Fp, X]))] at ht; cases ht

/-! ## 2. The racy read, guarded (plan §2 LOAD) -/

/-- One byte of the cpu field from `t`: `⟦|M|⟧ okB` (the image is 0; a message's byte meets `π3` under the guard). -/
theorem pc_byteE {M : List PMsg} {t j : Nat} {v : BitVec 8} (hj : j < 8)
    (hb : memByte imgL M t (Pc + j) = some v) : grd π3 imgL M M.length (okB j v) := by
  cases t with
  | zero =>
    refine grd_intro (.inl ?_)
    simp only [memByte, imgL_zero, Option.some.injEq] at hb
    subst hb
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  | succ k =>
    obtain ⟨m, hm, hba⟩ := memByte_succ hb
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
    refine grd_mono (msgAt_le hmt).2 (grd_imp (fun hok => ?_) (grd_self hmt))
    obtain ⟨hp, hd⟩ := hok (tchB_of hj (by rw [hba]; rfl))
    rw [← hp, byteAt_off rfl] at hba
    unfold okB
    rcases hd with hd | hd <;> rw [hd] at hba
    · exact .inl hba.symm
    · exact .inr hba.symm

/-- **THE RACY READ OF THE CPU FIELD, GUARDED**: `⟦|M|⟧ (value = 0 ∨ value = 0x3000)`. -/
theorem pc_readE {M : List PMsg} {tvs : List (Nat × BitVec 8)} (hl : tvs.length = 8)
    (hw : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → memByte imgL M t (Pc + j) = some v) :
    grd π3 imgL M M.length (ldVal true 8 tvs = 0 ∨ ldVal true 8 tvs = 0x3000) := by
  intro hV
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, t4, v4, t5, v5, t6, v6, t7, v7, rfl⟩ :
      ∃ t0 v0 t1 v1 t2 v2 t3 v3 t4 v4 t5 v5 t6 v6 t7 v7,
        tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3), (t4, v4), (t5, v5), (t6, v6), (t7, v7)] := by
    match tvs, hl with
    | [(a0, b0), (a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)], _ =>
      exact ⟨a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, rfl⟩
  have k0 := pc_byteE (j := 0) (by decide) (hw 0 _ _ rfl) hV
  have k1 := pc_byteE (j := 1) (by decide) (hw 1 _ _ rfl) hV
  have k2 := pc_byteE (j := 2) (by decide) (hw 2 _ _ rfl) hV
  have k3 := pc_byteE (j := 3) (by decide) (hw 3 _ _ rfl) hV
  have k4 := pc_byteE (j := 4) (by decide) (hw 4 _ _ rfl) hV
  have k5 := pc_byteE (j := 5) (by decide) (hw 5 _ _ rfl) hV
  have k6 := pc_byteE (j := 6) (by decide) (hw 6 _ _ rfl) hV
  have k7 := pc_byteE (j := 7) (by decide) (hw 7 _ _ rfl) hV
  have e0 : toBytes 0 8 = [0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have e3 : toBytes 0x3000 8 = [0, 0x30, 0, 0, 0, 0, 0, 0] := by decide
  unfold okB at k0 k1 k2 k3 k4 k5 k6 k7
  rw [e0, e3] at k0 k1 k2 k3 k4 k5 k6 k7
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, or_self] at k0 k1 k2 k3 k4 k5 k6 k7
  subst k0 k2 k3 k4 k5 k6 k7
  have hmap : [(t0, (0 : BitVec 8)), (t1, v1), (t2, 0), (t3, 0), (t4, 0), (t5, 0), (t6, 0), (t7, 0)].map Prod.snd =
      [0, v1, 0, 0, 0, 0, 0, 0] := rfl
  unfold ldVal
  rw [if_pos rfl, hmap]
  rcases k1 with rfl | rfl
  · left; decide
  · right; decide

/-! ## 3. The setup: per-byte owners (no dead set) -/

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **THE SETUP** (plan R-a5): hart 0 is the boot owner of the lock word, the cpu field and everything but the
marker — its `pend`s are its bags (split by the store that will write each; the rest it keeps, unused); hart 1 owns
the marker's.  Nothing is dead, nothing is shared. -/
theorem setup3E (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢
      (bS g M mA ∗ bS g M mC1 ∗ bS g M mC0 ∗ bS g M mR) ∗ bF g M := by
  iintro Hp
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  have hFs : ∀ (m0 : PMsg) t, m0.pa ≠ Fp → H.isF M t = true → shp M m0 t = false := fun m0 t hp hF => by
    cases h : shp M m0 t
    · rfl
    · rw [shp_F hp h] at hF; cases hF
  ihave ⟨HA, Hp⟩ := bsl_filter_split (pend (GF := GF) g) (shp M mA) (rng M) $$ Hp
  ihave ⟨HC1, Hp⟩ := bsl_peel (pend (GF := GF) g) (shp M mC1) (fun t => !shp M mA t)
    (fun t h => by simp [shp_ne (m2 := mA) (by decide) h]) (rng M) $$ Hp
  ihave ⟨HC0, Hp⟩ := bsl_peel (pend (GF := GF) g) (shp M mC0) (fun t => !shp M mA t && !shp M mC1 t)
    (fun t h => by simp [shp_ne (m2 := mA) (by decide) h, shp_ne (m2 := mC1) (by decide) h]) (rng M) $$ Hp
  ihave ⟨HR, Hp⟩ := bsl_peel (pend (GF := GF) g) (shp M mR)
    (fun t => !shp M mA t && !shp M mC1 t && !shp M mC0 t)
    (fun t h => by simp [shp_ne (m2 := mA) (by decide) h, shp_ne (m2 := mC1) (by decide) h,
      shp_ne (m2 := mC0) (by decide) h]) (rng M) $$ Hp
  ihave ⟨HF, -⟩ := bsl_peel (pend (GF := GF) g) (H.isF M)
    (fun t => !shp M mA t && !shp M mC1 t && !shp M mC0 t && !shp M mR t)
    (fun t h => by simp [hFs mA t (by decide) h, hFs mC1 t (by decide) h, hFs mC0 t (by decide) h,
      hFs mR t (by decide) h]) (rng M) $$ Hp
  unfold bS bF
  iframe HA HC1 HC0 HR HF

end res

/-! ## 4. Hart 0: the lock operations, proving `π3` at each fulfil -/

section hart0

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

abbrev Φ3E (g : AGN) (M : List PMsg) : Unit → IProp GF := fun _ => iprop(⌜∃ V, grd π3 imgL M V True⌝ ∨ dshot g)

/-- Hart 0's text from `pc = k` on: every fulfil takes its `pend` from the bag of its shape. -/
theorem h0_runE (g : AGN) (M : List PMsg) (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b3o) (hpc : s0.pc = 0)
    (hq : s0.q = []) (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h10 : s0.rd 10 = 0x3000)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    (bS (GF := GF) g M mA ∗ bS g M mC1 ∗ bS g M mC0 ∗ bS g M mR) ∗
      lhA g π3 (w3 M 0) (qs3 0) psInit P0 [] ⊢ wpKA g π3 (w3 M 0) qs3 s0 (Φ3E g M) := by
  have hw := litW_x xs3 imgL M 0
  iintro ⟨⟨HA, HC1, HC0, HR⟩, Hl⟩
  -- `li a4,1`
  iapply (wpKA_alui hw (litAg_x hq (p3o_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e10 : s1.rd 10 = 0x3000 := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  have e14 : s1.rd 14 = 1 := li_val hs1 (by decide) (by omega) (by decide)
  -- `amoswap.w.aq a5,a4,(s1)`
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq1 (p3o_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
    (by rw [e9]; decide) (by rw [e9]))
  iframe Hl
  inext
  iintro %tvs %ts %_ %_ %hmsg %_ %_ %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s1.rd 14) tvs = toBytes 1 4 := by rw [amoD_swap, e14]
  rw [hd1] at hmsg hcoh
  have hts1 : 1 ≤ ts := by
    have := cohBelow_at (j := 0) hcoh (by decide); omega
  ihave Hp := bS_take g M mA hts1 hmsg $$ HA
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro (ok3_lk (by rw [amoD_swap, toBytes_length]; decide))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f9 : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inl (by decide)), e9]
  have f10 : s2.rd 10 = 0x3000 := by rw [LPstep_rd hs2 10 (.inl (by decide)), e10]
  -- `sd a0,16(s1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq2 (p3o_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl) (alg_pc f9) (base_pc f9))
  iframe Hl
  inext
  iintro %t1 %_ %hmsg1 %hcoh1 %_ _ _
  rw [f10] at hmsg1
  have ht1 : 1 ≤ t1 := by have := cohBelow_at (j := 0) hcoh1 (by rw [toBytes_length]; decide); omega
  ihave Hp := bS_take g M mC1 ht1 hmsg1 $$ HC1
  imod shoot $$ Hp with #Hsh1
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro (ok3_pcv (.inr f10))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh1
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have g9 : s3.rd 9 = X := by rw [LPstep_rd hs3 9 (.inr rfl), f9]
  -- `sd zero,16(s1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq3 (p3o_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl) (alg_pc g9) (base_pc g9))
  iframe Hl
  inext
  iintro %t2 %_ %hmsg2 %hcoh2 %_ _ _
  have ht2 : 1 ≤ t2 := by have := cohBelow_at (j := 0) hcoh2 (by rw [toBytes_length]; decide); omega
  ihave Hp := bS_take g M mC0 ht2 hmsg2 $$ HC0
  imod shoot $$ Hp with #Hsh2
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro (ok3_pcv (.inl rfl))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh2
  iintro %s4 %hs4 _ _
  imodintro
  iintro Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have k9 : s4.rd 9 = X := by rw [LPstep_rd hs4 9 (.inr rfl), g9]
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq4 (p3o_at hP4) (by rw [hc4]; rfl) rfl) hq4 (by rw [hP4, hc4]; rfl))
  iframe Hl
  inext
  iintro %s5 %hs5 _ _
  imodintro
  iintro Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have l9 : s5.rd 9 = X := by rw [LPstep_rd hs5 9 (.inr rfl), k9]
  -- `sw zero,0(s1)`
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq5 (p3o_at hP5) (by rw [hc5]; rfl) rfl) hq5 (by rw [hP5, hc5]; rfl)
    (alg_of l9 (by decide) (by decide)) (base_of l9 (by decide)))
  iframe Hl
  inext
  iintro %t3 %_ %hmsg3 %hcoh3 %_ _ _
  have ht3 : 1 ≤ t3 := by have := cohBelow_at (j := 0) hcoh3 (by rw [toBytes_length]; decide); omega
  ihave Hp := bS_take g M mR ht3 hmsg3 $$ HR
  imod shoot $$ Hp with #Hsh3
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro (q0 _)⟩, grd_intro (ok3_lk (by rw [toBytes_length]; decide))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh3
  iintro %s6 %hs6 _ _
  imodintro
  iintro Hl
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 (by rw [hc5])
  have hend : s6.prog.length ≤ s6.pc := by rw [hP6, hc6]; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq6 (fun x hx => by rw [p3o_at hP6, hc6] at hx; cases hx)) hq6 hend
    (by show litDone s6 = some (); unfold litDone; rw [if_pos ⟨hq6, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩


end hart0

/-! ## 5. Hart 1: `holding()` and the panic test, a NON-HOLDER's racy reads -/

section hart1

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- `pc = 7`: the end. -/
theorem h1_endE (g : AGN) (M : List PMsg) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hprog : s.prog = b3h) (hq : s.q = []) (hpc : s.pc = 7) :
    lhA (GF := GF) g π3 (w3 M 1) (qs3 1) ws pr ev ⊢ wpKA g π3 (w3 M 1) qs3 s (Φ3E g M) := by
  iintro Hl
  have hend : s.prog.length ≤ s.pc := by rw [hprog, hpc]; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq (fun x hx => by rw [p3h_at hprog, hpc] at hx; cases hx)) hq hend
    (by show litDone s = some (); unfold litDone; rw [if_pos ⟨hq, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 3..7` HOLDING `⟦|M|⟧ False` (the racy read returned a value the protocol excludes): the rest of the text,
the marker store fulfilled from hart 1's own bag, its trace obligation discharged by the guard. -/
theorem h1_grdE (g : AGN) (M : List PMsg) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hprog : s.prog = b3h) (hq : s.q = []) (hpc : s.pc = 3) (h12 : s.rd 12 = 0x4000)
    (hg : grd π3 imgL M M.length False) :
    bF (GF := GF) g M ∗ lhA g π3 (w3 M 1) (qs3 1) ws pr ev ⊢ wpKA g π3 (w3 M 1) qs3 s (Φ3E g M) := by
  have hw := litW_x xs3 imgL M 1
  iintro ⟨HF, Hl⟩
  iapply (wpKA_alu hw (litAg_x hq (p3h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpKA_alui hw (litAg_x hq1 (p3h_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e12 : s2.rd 12 = 0x4000 := by
    rw [LPstep_rd hs2 12 (.inl (by decide)), LPstep_rd hs1 12 (.inl (by decide)), h12]
  iapply (wpKA_brx (Xs := xs3) hw (xAg_x xs3 imgL M 1 s2) hq2 (p3h_at hP2) (by rw [hc2]; rfl)
    (by rw [hP2]; decide))
  iframe Hl
  inext
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  by_cases hb : Weak.Prom.Ref.brEval .eq (s2.rd 13) (s2.rd 0) = true
  · rw [if_pos hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    iapply (h1_endE g M s3 _ _ _ hP3 hq3 hc3)
    iexact Hl
  · rw [if_neg hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
    have f12 : s3.rd 12 = 0x4000 := by rw [LPstep_rd hs3 12 (.inr rfl), e12]
    -- the marker store: hart 1's own `pend`; the trace obligation under the guard
    iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 12) (off := 0) (base := Fp) hw
      (litAg_x hq3 (p3h_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl)
      (alg_of f12 (by decide) (by decide)) (base_of f12 (by decide)))
    iframe Hl
    inext
    iintro %tf %_ %hmsg %hcoh %_ _ _
    rw [toBytes_length] at hcoh
    have htf : 1 ≤ tf := by have := cohBelow_at (j := 0) hcoh (by decide); omega
    ihave Hp := bF_take g M (toBytes_length _ _) htf hmsg $$ HF
    imod shoot $$ Hp with #Hsh
    imodintro
    isplitr
    · ileft; ipureintro; exact ⟨⟨M.length, fun hv => (hg hv).elim⟩, grd_intro ok3_fp⟩
    isplitr
    · unfold fulT; ileft; iexact Hsh
    iintro %s4 %hs4 _ _
    imodintro
    iintro Hl
    obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
    iapply (h1_endE g M s4 _ _ _ hP4 hq4 hc4)
    iexact Hl

/-- **HART 1** (a non-holder): `holding()` reads the lock word and the cpu field racily. -/
theorem h1_runE (g : AGN) (M : List PMsg) (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b3h)
    (hpc : s0.pc = 0) (hq : s0.q = []) (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X)
    (h10 : s0.rd 10 = 0x3100) (h12 : s0.rd 12 = 0x4000) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    bF (GF := GF) g M ∗ lhA g π3 (w3 M 1) (qs3 1) psInit P0 [] ⊢ wpKA g π3 (w3 M 1) qs3 s0 (Φ3E g M) := by
  have hw := litW_x xs3 imgL M 1
  iintro ⟨HF, Hl⟩
  -- `lw a5,0(s1)`: the racy read of the lock word (any value)
  iapply (wpKA_ld (sz := 4) (sgn := true) (rd := 15) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq (p3h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (alg_of h9 (by decide) (by decide)) (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %_ %_ _ _
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨0, grd_intro (fun _ => noF_snoc noF_nil (ld_nonF _ _ _))⟩
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e10 : s1.rd 10 = 0x3100 := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  have e12 : s1.rd 12 = 0x4000 := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  -- `beqz a5,7`: the first branch on a racy value
  iapply (wpKA_brx (Xs := xs3) hw (xAg_x xs3 imgL M 1 s1) hq1 (p3h_at hP1) (by rw [hc1]; rfl)
    (by rw [hP1]; decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  by_cases hb : Weak.Prom.Ref.brEval .eq (s1.rd 15) (s1.rd 0) = true
  · rw [if_pos hb] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    iapply (h1_endE g M s2 _ _ _ hP2 hq2 hc2)
    iexact Hl
  rw [if_neg hb] at hs2
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f9 : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inr rfl), e9]
  have f10 : s2.rd 10 = 0x3100 := by rw [LPstep_rd hs2 10 (.inr rfl), e10]
  have f12 : s2.rd 12 = 0x4000 := by rw [LPstep_rd hs2 12 (.inr rfl), e12]
  have hlen2 : s2.regs.length = 32 := hs2.2.2.2.1.trans hlen1
  -- `ld a5,16(s1)`: THE RACY READ OF THE CPU FIELD (bytes hart 0 owns): `⟦|M|⟧ (0 ∨ 0x3000)`
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 15) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq2 (p3h_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl) (alg_pc f9) (base_pc f9))
  iframe Hl
  inext
  iintro %tvs %hl8 %hlo _ _
  have hrd := pc_readE hl8 (fun j t v hg => (bytesAll_get (loadOk_weak hlo) hg).1)
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨0, grd_intro (fun _ => noF_snoc (noF_snoc noF_nil (ld_nonF _ _ _)) (ld_nonF _ _ _))⟩
  iintro %s3 %hs3 _ _
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have g12 : s3.rd 12 = 0x4000 := by rw [LPstep_rd hs3 12 (.inl (by decide)), f12]
  have g10 : s3.rd 10 = 0x3100 := by rw [LPstep_rd hs3 10 (.inl (by decide)), f10]
  have g15 := LPstep_rd_eq hs3 (by decide) (by omega)
  have hlen3 : s3.regs.length = 32 := hs3.2.2.2.1.trans hlen2
  imodintro
  iintro Hl
  by_cases hv : ldVal true 8 tvs = 0 ∨ ldVal true 8 tvs = 0x3000
  rotate_left
  · -- the value the protocol excludes: hart 1 carries `⟦|M|⟧ False` (no doom, no resource lost)
    iapply (h1_grdE g M s3 _ _ _ hP3 hq3 hc3 g12 (fun hV => hv (hrd hV)))
    iframe HF Hl
  -- the value is `0` or `0x3000`: `sub`, `seqz` give `0`, `beqz` skips the panic
  have v15 : s3.rd 15 = 0 ∨ s3.rd 15 = 0x3000 := by
    rw [g15]; rcases hv with h | h <;> rw [h] <;> decide
  iapply (wpKA_alu hw (litAg_x hq3 (p3h_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s4 %hs4 _ _
  imodintro
  iintro Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have v13 : s4.rd 13 ≠ 0 := by
    rw [LPstep_rd_eq hs4 (by decide) (by omega), g10]
    rcases v15 with h | h <;> rw [h] <;> decide
  have hlen4 : s4.regs.length = 32 := hs4.2.2.2.1.trans hlen3
  iapply (wpKA_alui hw (litAg_x hq4 (p3h_at hP4) (by rw [hc4]; rfl) rfl) hq4 (by rw [hP4, hc4]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s5 %hs5 _ _
  imodintro
  iintro Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have v13' : s5.rd 13 = 0 := by
    rw [LPstep_rd_eq hs5 (by decide) (by omega)]
    simp only [aluOp]
    rw [if_neg (by omega)]; rfl
  iapply (wpKA_brx (Xs := xs3) hw (xAg_x xs3 imgL M 1 s5) hq5 (p3h_at hP5) (by rw [hc5]; rfl)
    (by rw [hP5]; decide))
  iframe Hl
  inext
  iintro %s6 %hs6 _ _
  imodintro
  iintro Hl
  have hbr : (if Weak.Prom.Ref.brEval .eq (s5.rd 13) (s5.rd 0) then 7 else s5.pc + 1) = 7 := by
    rw [v13']; rfl
  rw [hbr] at hs6
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 rfl
  iapply (h1_endE g M s6 _ _ _ hP6 hq6 hc6)
  iexact Hl

end hart1

/-! ## 6. The verdict -/

theorem premise3E (M : List PMsg) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    wpPremise .hasLC ownGF (xStep xs3) litDone imgL M (progs t3) π3 (fun _ _ => True)
      (fun h => ΨK M (qs3 h)) (fun _ => False) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_3
  have hg0 : (progs t3)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs t3)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  ihave ⟨Hb0, HF⟩ := setup3E g M hm $$ Hp
  have k0 := h0_runE (GF := ownGF) g M p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 9 (by decide) (by decide)]; rfl) (by rw [hrd0 10 (by decide) (by decide)]; rfl) hnoinv
  have k1 := h1_runE (GF := ownGF) g M p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 9 (by decide) (by decide)]; rfl) (by rw [hrd1 10 (by decide) (by decide)]; rfl)
    (by rw [hrd1 12 (by decide) (by decide)]; rfl) hnoinv
  have k0' : (bS (GF := ownGF) g M mA ∗ bS g M mC1 ∗ bS g M mC0 ∗ bS g M mR) ∗
      lhA g π3 (w3 M 0) (qs3 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g π3 (hw (xStep xs3) litDone imgL M 0) (fun h => ΨK M (qs3 h)) p0
        (fun v => iprop(⌜∃ V, grd π3 imgL M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : bF (GF := ownGF) g M ∗ lhA g π3 (w3 M 1) (qs3 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g π3 (hw (xStep xs3) litDone imgL M (0 + 1)) (fun h => ΨK M (qs3 h)) p1
        (fun v => iprop(⌜∃ V, grd π3 imgL M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF) (g := g) (π := π3) (w := w3 M 0) (Qs := qs3) (P0 := P0 0) (q0 [])
  have s1 := lhA_start (GF := ownGF) (g := g) (π := π3) (w := w3 M 1) (Qs := qs3) (P0 := P0 (0 + 1))
    (fun _ => noF_nil)
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hb0]
  · iapply k0'
    iframe Hb0
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 HF]
  · iapply k1'
    iframe HF
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **E-a: A RACY NON-HOLDER READ THROUGH ⟦t⟧, WITH THE DEAD SET EMPTY** — the statement of `own_hold`
(OwnAHold.lean): hart 1 (not holding the lock) never executes acquire's panic store, whatever hart 0 writes; proved
through `adequacyA` at `Dd := fun _ => False`, protocol `π3`, no content classification of the read. -/
theorem own_holdE (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs3) imgL () (progs t3) M run) : noF (run.trace 1) := by
  have hnoinv := x_noInvalT hrun
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) π3 (fun _ _ => True)
    (fun h => ΨK M (qs3 h)) (fun _ => False) trivial (fun h => ⟨fun _ => noF_nil, wrOk_nil M⟩)
    (premise3E M hnoinv) hrun
  have hq := (hΨ 1 (run.trace 1).length).1
  rw [List.take_length] at hq
  exact noF_of_memEv (hq rfl)

#print axioms own_holdE

end Weak.Prom.OA.EH
