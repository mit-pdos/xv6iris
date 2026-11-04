/-
Weak/Prom: **E-a3: THE TENURE-DEPENDENT RACY READ, PROVED** (stage E-a3; owner ruling [OWN.P13]; G4-review2.md §6
A-1′ "Test: re-prove (3) where hart 1 acquires, releases, then runs the panic test"; plan rev 7 §4 G4 (3)).

`own_e3`: in every valid run of `t6` (OwnAE3Defs.lean: both harts run xv6's acquire, `sd a0,16(s1)`, release,
then the next acquire's `holding()` panic test), NO hart ever stores to the panic marker — in particular hart 1,
whose own cpu WAS in the field during its tenure (`own_e3_h1`, the brief's statement).  Proved through `adequacyA`
at `Dd := fun _ => False` (no free mode, no dead set), protocol `π6`.
The argument at the racy `ld a5,16(s1)` of hart `h` (after its own `sd zero,16(s1)` at `t2`):
* COHERENCE OVER ITS OWN WRITE: the store raised the field's 8 coherence floors to `t2` and nothing lowers them
  (`cohP`), so every byte's source is `t2` or above (`src_ge_lw`) — its own `sd a0` (below `t2`) is invisible;
* a source above `t2` AUTHORED BY `h`: its `pend` is in `h`'s own bag (per-author owners from boot): `h` DOOMS
  with it (plan R-a1: the owner dooms; it keeps every other resource; no valid run lets `h` read a message it will
  itself write later);
* a source by the OTHER hart: the core's guard `⟦t⟧ π6.okMsg` (`grd_self`) gives `0` or the other hart's cpu.
So the value is `⟦|M|⟧ (0 ∨ cpuOf (1 - h))`, never `cpuOf h`: `sub; seqz; beqz` skips the panic.  The protocol is
AUTHOR-AWARE and TIMESTAMP-BLIND (no tenure in it); the tenure is handled by coherence + own bag.
0 named inputs; finite runs (the prefix lemma S3d is separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE3Defs

namespace Weak.Prom.OA.E3

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.OA.C (Pc wpKA_alu alg_pc base_pc msgAt_of)
open Weak.Prom.OA.H (Fp noF noF_nil noF_snoc noF_of_memEv ld_nonF shp shp_of bS bS_take)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Pure helpers -/

/-- The registers every step keeps: `s1 = Lk`, `a0 = mycpu()`, `a2 = Fp`. -/
def regs6 (h : Nat) (s : LP) : Prop :=
  s.rd 9 = X ∧ s.rd 10 = cpuOf h ∧ s.rd 12 = 0x4000 ∧ s.regs.length = 32

theorem regs6_step {h : Nat} {s s' : LP} {pc rd v : Nat} (hs : LPstep s s' pc rd v)
    (hrd : rd = 0 ∨ (rd ≠ 9 ∧ rd ≠ 10 ∧ rd ≠ 12)) (hr : regs6 h s) : regs6 h s' := by
  obtain ⟨h9, h10, h12, hl⟩ := hr
  refine ⟨?_, ?_, ?_, hs.2.2.2.1.trans hl⟩
  · rw [LPstep_rd hs 9 (by omega), h9]
  · rw [LPstep_rd hs 10 (by omega), h10]
  · rw [LPstep_rd hs 12 (by omega), h12]

/-- The loop head `again:` (pc 1). -/
def lhS6 (h : Nat) (s : LP) : Prop := s.prog = b6 ∧ s.q = [] ∧ s.pc = 1 ∧ s.rd 14 = 1 ∧ regs6 h s

theorem pc_ne_fp : Pc ≠ Fp := by simp [Pc, Lk, Fp, X]
theorem lk_ne_fp : Lk ≠ Fp := by simp [Lk, Fp, X]

theorem st_nonF6 {b : Int} (hb : b ≠ Fp) {d : List (BitVec 8)} {a c : List Dsrc} {ts : Nat} :
    ∀ d' a' b' ts', ((LStore false false b d a c, some ts) : PEv) ≠ (LStore false false Fp d' a' b', some ts') :=
  fun _ _ _ _ he => hb (by cases he; rfl)

theorem rmw_nonF6 (aq rl : Bool) (b : Int) (tvs : List (Nat × BitVec 8)) (d : List (BitVec 8)) (a c : List Dsrc)
    (ts : Nat) :
    ∀ d' a' b' ts', ((LRmw aq rl b tvs d a c, some ts) : PEv) ≠ (LStore false false Fp d' a' b', some ts') :=
  fun _ _ _ _ he => by cases he

theorem isP6_pc {M : List PMsg} {h t v : Nat} (hm : msgAt M t = some ⟨Pc, toBytes v 8, some h, .plain⟩) :
    isP6 M h t = true := by
  rw [isP6, clsB_of hm]
  refine decide_eq_true ⟨rfl, tchB_of (j := 0) (by decide) ?_⟩
  rw [byteAt_off rfl, List.getElem?_eq_getElem (by rw [toBytes_length]; decide)]; rfl

/-! Coherence, backwards along the kit's post-states (each step keeps or raises `coh`). -/

theorem cohP_instrR {t : Nat} {ws : PState} (h : cohP t ws) : cohP t (instrR ws) := h
theorem cohP_ctrlP {t : Nat} {ws : PState} {s : List Dsrc} (h : cohP t ws) : cohP t (ctrlP ws s) := h
theorem cohP_acqPost {t ts : Nat} {ws : PState} {aq : Bool} (h : cohP t ws) : cohP t (acqPost ws aq ts) := h
theorem cohP_fence {t : Nat} {ws : PState} {a b c d : Bool} (h : cohP t ws) : cohP t (fencePost ws a b c d) := h

theorem cohP_regW {t : Nat} {ws : PState} (h : cohP t ws) : cohP t (qPosts ws (regWL 15 [.DLdRes] ++ [LInstr])) :=
  fun j hj => by rw [coh_qPosts_regW]; exact h j hj

theorem cohP_ld {t : Nat} {ws : PState} {aq rl : Bool} {va : Nat} {base : Int} {tvs : List (Nat × BitVec 8)}
    (h : cohP t ws) : cohP t (loadRun ws aq rl va base tvs) :=
  cohP_mono (loadRun_mono ws aq rl va base tvs).2.2.2.2.2.2.2.2.2.2.1 h

theorem cohP_st {t : Nat} {ws : PState} {rl : Bool} {va fv n ts : Nat} {base : Int} (h : cohP t ws) :
    cohP t (storeRun ws rl va fv base n ts) :=
  cohP_mono (storeRun_mono ws rl va fv base n ts).2.2.2.2.2.2.2.2.2.1 h

/-- An own 8-byte store at the field raises its floors to its timestamp. -/
theorem cohP_st6 {ws : PState} {rl : Bool} {va fv n ts : Nat} (hn : 8 ≤ n) :
    cohP ts (instrR (acqPost (storeRun ws rl va fv Pc n ts) false ts)) :=
  fun j hj => (storeRun_mono ws rl va fv Pc n ts).2.2.2.2.2.2.2.2.2.2.1 j (by omega)

theorem st_floor {ws : PState} {rl : Bool} {va fv n ts : Nat} {base : Int} (hn : 0 < n) :
    ts ≤ coh (instrR (acqPost (storeRun ws rl va fv base n ts) false ts)) base :=
  storeRun_coh0 ws rl va fv base n ts hn

theorem lt_of_coh {W : PState} {t1 t2 : Nat} (h1 : t1 ≤ coh W Pc) (h2 : cohBelow W Pc 8 t2) : t1 < t2 := by
  have h0 : coh W Pc < t2 := by simpa using cohBelow_at (j := 0) h2 (by decide)
  omega

/-! ## 2. The tails -/

section tails

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

abbrev Φ6 (g : AGN) (M : List PMsg) : Unit → IProp GF := fun _ => iprop(⌜∃ V, grd π6 imgL M V True⌝ ∨ dshot g)

/-- The BAD mode after the racy read: doomed (the reader surrendered its own `pend`), or `⟦|M|⟧ False`. -/
def bad6 (g : AGN) (M : List PMsg) : IProp GF := iprop(dshot g ∨ ⌜grd π6 imgL M M.length False⌝)

instance (g : AGN) (M : List PMsg) : Persistent (bad6 (GF := GF) g M) := by unfold bad6; infer_instance

/-- `pc = 16`: the end. -/
theorem h_end6 (g : AGN) (M : List PMsg) (h : Nat) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hprog : s.prog = b6) (hq : s.q = []) (hpc : s.pc = 16) :
    lhA (GF := GF) g π6 (w6 M h) (qs6 h) ws pr ev ⊢ wpKA g π6 (w6 M h) qs6 s (Φ6 g M) := by
  iintro Hl
  have hend : s.prog.length ≤ s.pc := by rw [hprog, hpc]; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq (fun x hx => by rw [p6_at hprog, hpc] at hx; cases hx)) hq hend
    (by show litDone s = some (); unfold litDone; rw [if_pos ⟨hq, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 12..16` in the BAD mode: the rest of the text, the panic store fulfilled from `h`'s own marker bag, its
trace obligation discharged by doom or by the guard. -/
theorem h_bad6 (g : AGN) (M : List PMsg) (h : Nat) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hprog : s.prog = b6) (hq : s.q = []) (hpc : s.pc = 12) (hr : regs6 h s) :
    bad6 (GF := GF) g M ∗ bS g M (mF6 h) ∗ lhA g π6 (w6 M h) (qs6 h) ws pr ev ⊢
      wpKA g π6 (w6 M h) qs6 s (Φ6 g M) := by
  have hw := litW_x xs6 imgL M h
  iintro ⟨#Hb, HF, Hl⟩
  iapply (wpKA_alu hw (litAg_x hq (p6_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hr1 := regs6_step hs1 (.inr ⟨by decide, by decide, by decide⟩) hr
  iapply (wpKA_alui hw (litAg_x hq1 (p6_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hr2 := regs6_step hs2 (.inr ⟨by decide, by decide, by decide⟩) hr1
  iapply (wpKA_brx (Xs := xs6) hw (xAg_x xs6 imgL M h s2) hq2 (p6_at hP2) (by rw [hc2]; rfl)
    (by rw [hP2]; decide))
  iframe Hl
  inext
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  by_cases hb : Weak.Prom.Ref.brEval .eq (s2.rd 13) (s2.rd 0) = true
  · rw [if_pos hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    iapply (h_end6 g M h s3 _ _ _ hP3 hq3 hc3)
    iexact Hl
  · rw [if_neg hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
    have hr3 := regs6_step hs3 (.inl rfl) hr2
    -- the panic store: `h`'s own marker `pend`; the trace obligation by doom or the guard
    iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 12) (off := 0) (base := Fp) hw
      (litAg_x hq3 (p6_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl)
      (alg_of hr3.2.2.1 (by decide) (by decide)) (base_of hr3.2.2.1 (by decide)))
    iframe Hl
    inext
    iintro %tf %_ %hmsg %hcoh %_ _ _
    rw [toBytes_length] at hcoh
    have htf : 1 ≤ tf := by have := cohBelow_at (j := 0) hcoh (by decide); omega
    rw [hr3.2.1] at hmsg
    ihave Hp := bS_take g M (mF6 h) htf hmsg $$ HF
    imod shoot $$ Hp with #Hsh
    imodintro
    isplitr
    · unfold bad6
      icases Hb with (#Hd | %hg)
      · iright; iexact Hd
      · ileft; ipureintro; exact ⟨⟨M.length, fun hv => (hg hv).elim⟩, grd_intro ok6_fp⟩
    isplitr
    · unfold fulT; ileft; iexact Hsh
    iintro %s4 %hs4 _ _
    imodintro
    iintro Hl
    obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
    iapply (h_end6 g M h s4 _ _ _ hP4 hq4 hc4)
    iexact Hl

/-- **THE TENURE AND THE NEXT `holding()`** (`pc = 5..16`): `sd a0,16(s1)` (hart `h`'s cpu in the field), the
release, the next acquire's racy reads and panic test. -/
theorem h_rel6 (g : AGN) (M : List PMsg) (h : Nat) (hh : h < 2) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a)
    (s0 : LP) (ws0 : PState) (pr0 : GSet Nat) (ev0 : Trace) (hprog : s0.prog = b6) (hq : s0.q = [])
    (hpc : s0.pc = 5) (hr0 : regs6 h s0) (hnoF : noF ev0) :
    doomInv (GF := GF) g M ∗ lbB g M (isP6 M h) 0 ∗ bS g M (mR6 h) ∗ bS g M (mF6 h) ∗
      lhA g π6 (w6 M h) (qs6 h) ws0 pr0 ev0 ⊢ wpKA g π6 (w6 M h) qs6 s0 (Φ6 g M) := by
  have hw := litW_x xs6 imgL M h
  iintro ⟨#Hdoom, HbP, HbR, HbF, Hl⟩
  -- `sd a0,16(s1)`: hart `h`'s TENURE — its cpu in the field
  iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq (p6_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc hr0.1) (base_pc hr0.1))
  iframe Hl
  inext
  iintro %t1 %_ %hmsg1 %hcoh1 %_ _ _
  rw [hr0.2.1] at hmsg1
  have ht1 : 1 ≤ t1 := by have := cohBelow_at (j := 0) hcoh1 (by rw [toBytes_length]; decide); omega
  have hm1 := msgAt_of ht1 hmsg1
  ihave ⟨Hp, HbP⟩ := lbB_take g M (isP6 M h) (by omega : 0 < t1) (isP6_pc (h := h) hm1) (msgAt_le hm1) $$ HbP
  imod shoot $$ Hp with #Hsh1
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (noF_snoc hnoF (st_nonF6 pc_ne_fp))⟩, grd_intro (ok6_pc hh (.inr hr0.2.1))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh1
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hr1 := regs6_step hs1 (.inl rfl) hr0
  -- `sd zero,16(s1)` (release): hart `h`'s own write at `t2`, the coherence floor of the reads to come
  iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq1 (p6_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl) (alg_pc hr1.1) (base_pc hr1.1))
  iframe Hl
  inext
  iintro %t2 %_ %hmsg2 %hcoh2 %_ _ _
  rw [toBytes_length] at hcoh2
  have ht12 : t1 < t2 := lt_of_coh (st_floor (by simp)) hcoh2
  have hm2 : msgAt M t2 = some ⟨Pc, toBytes 0 8, some h, .plain⟩ := msgAt_of (by omega) hmsg2
  ihave ⟨Hp, HbP⟩ := lbB_take g M (isP6 M h) ht12 (isP6_pc hm2) (msgAt_le hm2) $$ HbP
  imod shoot $$ Hp with #Hsh2
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (noF_snoc (noF_snoc hnoF (st_nonF6 pc_ne_fp)) (st_nonF6 pc_ne_fp))⟩,
      grd_intro (ok6_pc hh (.inl rfl))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh2
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hr2 := regs6_step hs2 (.inl rfl) hr1
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq2 (p6_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl))
  iframe Hl
  inext
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hr3 := regs6_step hs3 (.inl rfl) hr2
  -- `sw zero,0(s1)`: the release word
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq3 (p6_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl)
    (alg_of hr3.1 (by decide) (by decide)) (base_of hr3.1 (by decide)))
  iframe Hl
  inext
  iintro %t3 %_ %hmsg3 %hcoh3 %_ _ _
  have ht3 : 1 ≤ t3 := by have := cohBelow_at (j := 0) hcoh3 (by rw [toBytes_length]; decide); omega
  ihave Hp := bS_take g M (mR6 h) ht3 hmsg3 $$ HbR
  imod shoot $$ Hp with #Hsh3
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (noF_snoc (noF_snoc (noF_snoc hnoF (st_nonF6 pc_ne_fp)) (st_nonF6 pc_ne_fp))
      (st_nonF6 lk_ne_fp))⟩, grd_intro (ok6_lk (by rw [toBytes_length]; decide))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh3
  iintro %s4 %hs4 _ _
  imodintro
  iintro Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have hr4 := regs6_step hs4 (.inl rfl) hr3
  -- the next acquire's `holding()`: `lw a5,0(s1)` (racy, any value)
  iapply (wpKA_ld (sz := 4) (sgn := true) (rd := 15) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq4 (p6_at hP4) (by rw [hc4]; rfl) rfl) hq4 (by rw [hP4, hc4]; rfl)
    (alg_of hr4.1 (by decide) (by decide)) (base_of hr4.1 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %_ %_ _ _
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨0, grd_intro (noF_snoc (noF_snoc (noF_snoc (noF_snoc hnoF (st_nonF6 pc_ne_fp)) (st_nonF6 pc_ne_fp))
      (st_nonF6 lk_ne_fp)) (ld_nonF _ _ _))⟩
  iintro %s5 %hs5 _ _
  imodintro
  iintro Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have hr5 := regs6_step hs5 (.inr ⟨by decide, by decide, by decide⟩) hr4
  -- `beqz a5,16`
  iapply (wpKA_brx (Xs := xs6) hw (xAg_x xs6 imgL M h s5) hq5 (p6_at hP5) (by rw [hc5]; rfl)
    (by rw [hP5]; decide))
  iframe Hl
  inext
  iintro %s6 %hs6 _ _
  imodintro
  iintro Hl
  by_cases hb : Weak.Prom.Ref.brEval .eq (s5.rd 15) (s5.rd 0) = true
  · rw [if_pos hb] at hs6
    obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 rfl
    iapply (h_end6 g M h s6 _ _ _ hP6 hq6 hc6)
    iexact Hl
  rw [if_neg hb] at hs6
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 (by rw [hc5])
  have hr6 := regs6_step hs6 (.inl rfl) hr5
  have hl6 := hr6.2.2.2
  -- `ld a5,16(s1)`: THE TENURE-DEPENDENT RACY READ
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 15) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq6 (p6_at hP6) (by rw [hc6]; rfl) rfl) hq6 (by rw [hP6, hc6]; rfl) (alg_pc hr6.1) (base_pc hr6.1))
  iframe Hl
  inext
  iintro %tvs %hl8 %hlo _ _
  have hrd := pc_read6 hh hl8 hnoinv hm2 (loadOk_cohP hlo (by
    apply cohP_instrR; apply cohP_ctrlP; apply cohP_regW; apply cohP_ld; apply cohP_instrR
    apply cohP_acqPost; apply cohP_st; apply cohP_instrR; apply cohP_fence
    exact cohP_st6 (by simp [toBytes_length])) hl8)
  rcases hrd with ⟨tx, htx, hPx⟩ | hgv
  · -- DOOM (plan R-a1): a message of `h`'s OWN above its `sd zero`, whose `pend` `h` holds
    obtain ⟨mx, hmx, _⟩ := clsB_iff.1 hPx
    ihave ⟨Hp, -⟩ := lbB_take g M (isP6 M h) htx hPx (msgAt_le hmx) $$ HbP
    imod doom (E := ⊤) CoPset.subseteq_top g M tx (msgAt_le hmx) $$ [Hdoom Hp] with #Hd
    · iframe Hdoom Hp
    imodintro
    isplitr
    · iright; iexact Hd
    iintro %s7 %hs7 _ _
    obtain ⟨hP7, hc7, hq7⟩ := LPstep_at hs7 hP6 (by rw [hc6])
    have hr7 := regs6_step hs7 (.inr ⟨by decide, by decide, by decide⟩) hr6
    imodintro
    iintro Hl
    iapply (h_bad6 g M h s7 _ _ _ hP7 hq7 hc7 hr7)
    iframe HbF Hl
    unfold bad6; ileft; iexact Hd
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨0, grd_intro (noF_snoc (noF_snoc (noF_snoc (noF_snoc (noF_snoc hnoF (st_nonF6 pc_ne_fp))
      (st_nonF6 pc_ne_fp)) (st_nonF6 lk_ne_fp)) (ld_nonF _ _ _)) (ld_nonF _ _ _))⟩
  iintro %s7 %hs7 _ _
  obtain ⟨hP7, hc7, hq7⟩ := LPstep_at hs7 hP6 (by rw [hc6])
  have hr7 := regs6_step hs7 (.inr ⟨by decide, by decide, by decide⟩) hr6
  have g15 := LPstep_rd_eq hs7 (by decide) (by omega)
  imodintro
  iintro Hl
  by_cases hv : ldVal true 8 tvs = 0 ∨ ldVal true 8 tvs = cpuOf (1 - h)
  rotate_left
  · -- a value the protocol excludes: `⟦|M|⟧ False` (no doom, no resource lost)
    iapply (h_bad6 g M h s7 _ _ _ hP7 hq7 hc7 hr7)
    iframe HbF Hl
    unfold bad6; iright; ipureintro; exact fun hV => hv (hgv hV)
  -- the value is `0` or the OTHER hart's cpu: `sub`, `seqz` give `0`, `beqz` skips the panic
  have h01 : h = 0 ∨ h = 1 := by omega
  have v15 : s7.rd 15 = 0 ∨ s7.rd 15 = cpuOf (1 - h) := by
    rw [g15]
    rcases hv with e | e <;> rw [e]
    · left; rfl
    · right; rcases h01 with rfl | rfl <;> decide
  have hl7 := hr7.2.2.2
  iapply (wpKA_alu hw (litAg_x hq7 (p6_at hP7) (by rw [hc7]; rfl) rfl) hq7 (by rw [hP7, hc7]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s8 %hs8 _ _
  imodintro
  iintro Hl
  obtain ⟨hP8, hc8, hq8⟩ := LPstep_at hs8 hP7 (by rw [hc7])
  have v13 : s8.rd 13 ≠ 0 := by
    rw [LPstep_rd_eq hs8 (by decide) (by omega), hr7.2.1]
    rcases h01 with rfl | rfl <;> rcases v15 with e | e <;> rw [e] <;> decide
  have hl8' : s8.regs.length = 32 := hs8.2.2.2.1.trans hl7
  iapply (wpKA_alui hw (litAg_x hq8 (p6_at hP8) (by rw [hc8]; rfl) rfl) hq8 (by rw [hP8, hc8]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s9 %hs9 _ _
  imodintro
  iintro Hl
  obtain ⟨hP9, hc9, hq9⟩ := LPstep_at hs9 hP8 (by rw [hc8])
  have v13' : s9.rd 13 = 0 := by
    rw [LPstep_rd_eq hs9 (by decide) (by omega)]
    simp only [aluOp]
    rw [if_neg (by omega)]; rfl
  iapply (wpKA_brx (Xs := xs6) hw (xAg_x xs6 imgL M h s9) hq9 (p6_at hP9) (by rw [hc9]; rfl)
    (by rw [hP9]; decide))
  iframe Hl
  inext
  iintro %s10 %hs10 _ _
  imodintro
  iintro Hl
  have hbr : (if Weak.Prom.Ref.brEval .eq (s9.rd 13) (s9.rd 0) then 16 else s9.pc + 1) = 16 := by
    rw [v13']; rfl
  rw [hbr] at hs10
  obtain ⟨hP10, hc10, hq10⟩ := LPstep_at hs10 hP9 rfl
  iapply (h_end6 g M h s10 _ _ _ hP10 hq10 hc10)
  iexact Hl

end tails

/-! ## 3. The spin loop, the hart -/

section loop

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **THE SPIN LOOP** (Löb induction at `again:`): `mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5;
bnez a5,again`; each AMO's `pend` from the hart's own bag above its coherence floor at `Lk`. -/
theorem loop6 (g : AGN) (M : List PMsg) (h : Nat) (hh : h < 2) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS6 h s⌝ -∗
      ⌜lo ≤ coh ws Lk ∧ noF ev⌝ -∗ doomInv (GF := GF) g M -∗ lbB g M (shp M (mA6 h)) lo -∗
      lbB g M (isP6 M h) 0 -∗ bS g M (mR6 h) -∗ bS g M (mF6 h) -∗
      lhA g π6 (w6 M h) (qs6 h) ws pr ev -∗ wpKA g π6 (w6 M h) qs6 s (Φ6 g M) := by
  have hw := litW_x xs6 imgL M h
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %lo %hs %hl0 #Hdoom HbA HbP HbR HbF Hl
  obtain ⟨hprog0, hq0, hpc0, h14, hr0⟩ := hs
  obtain ⟨hlo0, hnoF⟩ := hl0
  have hl0 := hr0.2.2.2
  -- `mv a5,a4`
  iapply (wpKA_alu hw (litAg_x hq0 (p6_at hprog0) (by rw [hpc0]; rfl) rfl) hq0 (by rw [hprog0, hpc0]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s %hsA _ _
  imodintro
  iintro Hl
  obtain ⟨hprog, hpc, hq⟩ := LPstep_at hsA hprog0 (by rw [hpc0])
  have hr := regs6_step hsA (.inr ⟨by decide, by decide, by decide⟩) hr0
  have h14' : s.rd 14 = 1 := by rw [LPstep_rd hsA 14 (.inl (by decide)), h14]
  have h15 : s.rd 15 = 1 := by
    have e := LPstep_rd_eq hsA (by decide) (by omega)
    have h0 : s0.rd 0 = 0 := rfl
    rw [e, h0, h14]; decide
  have hlo : lo ≤ coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) Lk := hlo0
  -- `amoswap.w.aq a5,a5,(s1)`
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq (p6_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by rw [hr.1]; decide) (by rw [hr.1]))
  iframe Hl
  inext
  iintro %tvs %ts %_ %_ %hmsg %_ %_ %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s.rd 15) tvs = toBytes 1 4 := by rw [amoD_swap, h15]
  have hlenD : (amoD .swap 4 (s.rd 15) tvs).length = 4 := by rw [hd1]; rfl
  rw [hd1] at hmsg
  rw [hlenD] at hcoh
  have hc0 : coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) Lk < ts := by
    simpa using cohBelow_at (j := 0) hcoh (by decide)
  have hcm := (loadRun_mono (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs).2.2.2.2.2.2.2.2.2.2.1 Lk
  have hts1 : 1 ≤ ts := by omega
  have hmt := msgAt_of hts1 hmsg
  have hlots : lo < ts := by omega
  ihave ⟨Hp, HbA⟩ := lbB_take g M (shp M (mA6 h)) hlots (shp_of (m0 := mA6 h) hts1 hmsg) (msgAt_le hmt) $$ HbA
  imod shoot $$ Hp with #Hsh
  have hnoF1 : noF (ev ++ [(LRmw true false Lk tvs (amoD .swap 4 (s.rd 15) tvs) (srcR 9) (srcR 15), some ts)]) :=
    noF_snoc hnoF (rmw_nonF6 _ _ _ _ _ _ _ _)
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro hnoF1⟩, grd_intro (ok6_lk (by rw [hlenD]; decide))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hr1 := regs6_step hs1 (.inr ⟨by decide, by decide, by decide⟩) hr
  have e14 : s1.rd 14 = 1 := by rw [LPstep_rd hs1 14 (.inl (by decide)), h14']
  have hcs0 := storeRun_coh0 (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))
    ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts (by rw [hlenD]; decide)
  have hcs : ts ≤ coh (instrR (ctrlP (instrR (regWP (qPosts (amoPost (storeRun (loadRun
      (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts)
      true ts) (regWL 15 [.DLdRes] ++ [LInstr])) 15 (srcR 15))) (srcR 15 ++ srcR 0))) Lk := hcs0
  -- `sext.w a5,a5`
  iapply (wpKA_addiw (Xs := xs6) hw (xAg_x xs6 imgL M h s1) hq1 (p6_at hP1) (by rw [hc1]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hr2 := regs6_step hs2 (.inr ⟨by decide, by decide, by decide⟩) hr1
  have f14 : s2.rd 14 = 1 := by rw [LPstep_rd hs2 14 (.inl (by decide)), e14]
  -- `bnez a5,again`
  iapply (wpKA_brx (Xs := xs6) hw (xAg_x xs6 imgL M h s2) hq2 (p6_at hP2) (by rw [hc2]; rfl)
    (by rw [hP2]; decide))
  iframe Hl
  inext
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  by_cases hb : Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) = true
  · -- held: back to `again:`
    rw [if_pos hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hls : lhS6 h s3 := ⟨hP3, hq3, hc3, by rw [LPstep_rd hs3 14 (.inr rfl), f14],
      regs6_step hs3 (.inl rfl) hr2⟩
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨hcs, hnoF1⟩ Hdoom HbA HbP HbR HbF Hl
  · -- acquired: on to `sd a0,16(s1)`
    rw [if_neg hb] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
    iapply (h_rel6 g M h hh hnoinv s3 _ _ _ hP3 hq3 hc3 (regs6_step hs3 (.inl rfl) hr2) hnoF1)
    iframe Hdoom HbP HbR HbF Hl

/-- **A HART**: `li a4,1`, then the spin loop. -/
theorem hart6 (g : AGN) (M : List PMsg) (h : Nat) (hh : h < 2) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b6) (hpc : s0.pc = 0) (hq : s0.q = []) (hr : regs6 h s0) :
    doomInv (GF := GF) g M ∗ bags g M h ∗ lhA g π6 (w6 M h) (qs6 h) psInit P0 [] ⊢
      wpKA g π6 (w6 M h) qs6 s0 (Φ6 g M) := by
  have hw := litW_x xs6 imgL M h
  have hl := hr.2.2.2
  iintro ⟨#Hdoom, Hb, Hl⟩
  unfold bags
  icases Hb with ⟨HbA, HbP, HbR, HbF⟩
  iapply (wpKA_alui hw (litAg_x hq (p6_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hls : lhS6 h s1 := ⟨hP1, hq1, hc1, li_val hs1 (by decide) (by omega) (by decide),
    regs6_step hs1 (.inr ⟨by decide, by decide, by decide⟩) hr⟩
  ihave Hloop := loop6 (GF := GF) g M h hh hnoinv
  iapply Hloop $$ %s1 %_ %_ %_ %0 %hls %⟨Nat.zero_le _, noF_nil⟩ Hdoom HbA HbP HbR HbF Hl

end loop

/-! ## 4. The verdict -/

/-- THE ADEQUACY PREMISE at `Dd := fun _ => False` (no dead set). -/
theorem premise6 (M : List PMsg) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    wpPremise .hasLC ownGF (xStep xs6) litDone imgL M (progs t6) π6 (fun _ _ => True)
      (fun h => ΨK M (qs6 h)) (fun _ => False) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_6
  have hg0 : (progs t6)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs t6)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  ihave ⟨Hb0, Hb1⟩ := setup6 g M hm $$ Hp
  have k0 := hart6 (GF := ownGF) g M 0 (by decide) hnoinv p0 (P0 := P0 0) hpr0 hpc0 hq0
    ⟨by rw [hrd0 9 (by decide) (by decide)]; rfl, by rw [hrd0 10 (by decide) (by decide)]; rfl,
      by rw [hrd0 12 (by decide) (by decide)]; rfl, hl0⟩
  have k1 := hart6 (GF := ownGF) g M 1 (by decide) hnoinv p1 (P0 := P0 1) hpr1 hpc1 hq1
    ⟨by rw [hrd1 9 (by decide) (by decide)]; rfl, by rw [hrd1 10 (by decide) (by decide)]; rfl,
      by rw [hrd1 12 (by decide) (by decide)]; rfl, hl1⟩
  have k0' : doomInv (GF := ownGF) g M ∗ bags g M 0 ∗ lhA g π6 (w6 M 0) (qs6 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g π6 (hw (xStep xs6) litDone imgL M 0) (fun h => ΨK M (qs6 h)) p0
        (fun v => iprop(⌜∃ V, grd π6 imgL M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : doomInv (GF := ownGF) g M ∗ bags g M 1 ∗ lhA g π6 (w6 M 1) (qs6 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g π6 (hw (xStep xs6) litDone imgL M (0 + 1)) (fun h => ΨK M (qs6 h)) p1
        (fun v => iprop(⌜∃ V, grd π6 imgL M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF) (g := g) (π := π6) (w := w6 M 0) (Qs := qs6) (P0 := P0 0) noF_nil
  have s1 := lhA_start (GF := ownGF) (g := g) (π := π6) (w := w6 M 1) (Qs := qs6) (P0 := P0 (0 + 1)) noF_nil
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hb0]
  · iapply k0'
    iframe Hdoom Hb0
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 Hb1]
  · iapply k1'
    iframe Hdoom Hb1
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **E-a3: THE TENURE-DEPENDENT RACY READ** — in every valid run of `t6`, NO hart (each of which acquired, wrote
its cpu into the lock's cpu field, and released) panics in the next acquire's `holding()` test.  Through
`adequacyA` at `Dd := fun _ => False`, protocol `π6` (author-aware, timestamp-blind).  0 named inputs. -/
theorem own_e3 (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs6) imgL () (progs t6) M run) : ∀ h, noF (run.trace h) := by
  have hnoinv := x_noInvalT hrun
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) π6 (fun _ _ => True)
    (fun h => ΨK M (qs6 h)) (fun _ => False) trivial (fun _ => ⟨noF_nil, wrOk_nil M⟩)
    (premise6 M hnoinv) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact noF_of_memEv hq

/-- The brief's statement: hart 1 (which held the lock before) never panics. -/
theorem own_e3_h1 (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs6) imgL () (progs t6) M run) : noF (run.trace 1) :=
  own_e3 M run hrun 1

#print axioms own_e3
#print axioms own_e3_h1

end Weak.Prom.OA.E3
