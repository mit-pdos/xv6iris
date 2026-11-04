/-
Weak/Prom: **row 8, MP+fences, proved IN THE LOGIC** (stage S2; plan rev 7 §5 row 8, §2 "Leaf rules" FENCE, §8 S2).

Programs (RefTests.lean, `x = 0x1000`, `y = 0x2000`): `Lit.mpFF` = repo `SAFE/MP+fence.w.w+fence.r.rw` and `Lit.mpFFrr`
(the plan's `fence r,r` reader):  H0 `sw x5,(x); fence w,w; sw x5,(y)` (x5 = 1) ‖ H1 `lw x5,(y); fence r,rw|r,r;
lw x7,(x)`.  Outcome `x5 = 1 ∧ x7 = 0` of H1: FORBIDDEN (rule 4, cat).

The derivation (plan §2 shape: Ψ proved step by step, contradiction from A0's exports (ii), (iii), (v) only):
* H0's Ψ (`qWW`): its memory entries are a prefix of `st x @tx, st y @ty` with `tx < ty`.  View facts: FULFIL of
  `sw x` gives `vwOld ≥ tx` (`storeRun`); `fence w,w` (rule 4, `fencePost`) raises the store floor `vwNew ≥ vwOld`;
  EXT of `sw y` gives `vwNew ≤ pv < ty`.
* H1's Ψ (`qRR`): a prefix of `ld y` (byte-0 source `s0`), `ld x` (source `s1`) with "no write to x in
  `(s1, s0]`" (under `noCmo`).  View facts: LOAD (X4) gives `vrOld ≥ s0`; `fence r,·` raises the load floor
  `vrNew ≥ vrOld`; the second load's pre-view contains `vrNew`, and its `loadOk` excludes writes in `(s1, pre]`.
* Contradiction (`mp_contra`): `x5 = 1` makes `s0` a message (traceWf), written by H0's `st y` (partition +
  Ψ: the only write of 1 to y), so `s0 = ty`; `x7 = 0` makes `s1 = 0` (every write to x writes 1); H0's `st x` at
  `tx < ty = s0` is a write to x in `(0, s0]`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitH

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The contradiction -/

section contra

/-- **THE MP CORE** (plan §2 steps 1–6 for row 8): the reader's first answer is a message holding 1 at `y`, the
second holds 0 at `x` with no write to `x` in `(s1, s0]`; every message holding 1 at `y` has a write to `x`
strictly below it, and no message holds 0 at `x`; the image holds 0 at `x` and `y`. -/
theorem mp_core {img : Image} {M : List PMsg} {x y : Int} {s0 s1 : Nat} {b0 b1 : BitVec 8} (hnc : noCmo M)
    (hx : img x = some 0) (hy : img y = some 0)
    (hr0 : memByte img M s0 y = some b0) (hv0 : b0 ≠ 0) (hr1 : memByte img M s1 x = some b1) (hv1 : b1 = 0)
    (hord : noCmo M → ¬ writesIn M x s1 s0)
    (hW1 : ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.byteAt y = some b0 →
      ∃ (k' : Nat) (m' : PMsg), M[k']? = some m' ∧ (m'.byteAt x).isSome ∧ k' < k)
    (hW2 : ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.byteAt x ≠ some 0) : False := by
  obtain ⟨k0, m0, rfl, hm0, hb0⟩ := src_of_val hr0 hy hv0
  obtain ⟨k', m', hm', hx', hk'⟩ := hW1 k0 m0 hm0 hb0
  cases s1 with
  | zero => exact hord hnc (writesIn_of hm' hx' (by omega) (by omega))
  | succ k1 =>
    obtain ⟨m1, hm1, hb1⟩ := memByte_succ hr1
    exact hW2 k1 m1 hm1 (by rw [hb1, hv1])

end contra

/-! ## 4. The verdicts -/

/-- Ψ of the MP rows: H0 the writer (`qWW` at x, y), H1 the reader (`qRR` at y, x), nothing else. -/
def QsMP (M : List PMsg) (rb : Nat) : Nat → Trace → Prop
  | 0 => qWW (X : Int) (Y : Int) (toBytes 1 4) (toBytes 1 4) [.DReg 6] [.DReg 5] [.DReg 7] [.DReg 5]
  | 1 => qRR M (Y : Int) (X : Int) 4 [.DReg 6] [.DReg rb]
  | _ => q0

theorem QsMP_nil (M : List PMsg) (rb : Nat) : ∀ h, QsMP M rb h []
  | 0 => trivial
  | 1 => trivial
  | _ + 2 => rfl

/-- **The MP contradiction** (plan §2 steps 1–6, from A0's exports (ii), (iii), (v)). -/
theorem mp_glue {run : PFRun LP Unit} {M : List PMsg} {img : Image} {rb : Nat} (himg : run.cfg.pcImg = img)
    (hx : img (X : Int) = some 0) (hy : img (Y : Int) = some 0) (hQ : ∀ h, QsMP M rb h (memEv (run.trace h)))
    (hnc : noCmo M) (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) : ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  rintro ⟨ho0, ho1⟩
  obtain ⟨s0, s1, b0, b1, hr0, hv0, hr1, hv1, hord⟩ := qRR_out hwf (by decide) (hQ 1) ho0 ho1
  rw [himg] at hr0 hr1
  have hW : ∀ (k : Nat) (m : PMsg), M[k]? = some m → ∃ e, e ∈ memEv (run.trace 0) ∧ e.2 = some (k + 1) ∧
      labelWrite e.1 = some (m.pa, m.data) := by
    intro k m hm
    obtain ⟨h, e, he, het, hlw⟩ := kit_writer hpart hwf hm
    match h, he with
    | 0, he => exact ⟨e, he, het, hlw⟩
    | 1, he => rw [qRR_nots (hQ 1) he] at het; cases het
    | n + 2, he =>
      have h0 : memEv (run.trace (n + 2)) = [] := hQ (n + 2)
      rw [h0] at he; cases he
  refine mp_core hnc hx hy hr0 ?_ hr1 ?_ hord ?_ ?_
  · intro h; rw [h] at hv0; cases hv0
  · apply BitVec.eq_of_toNat_eq; rw [hv1]; rfl
  · intro k m hm hb
    obtain ⟨e, he, het, hlw⟩ := hW k m hm
    rcases qWW_writer (hQ 0) he het with rfl | ⟨rfl, t0, ht0, hin, hlt⟩
    · simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      rw [byteAt_none_of hlw.1.symm hlw.2.symm (by decide)] at hb; cases hb
    · obtain ⟨m', hm', hpa', hd'⟩ := kit_msg hwf hin rfl rfl
      exact ⟨t0 - 1, m', hm', by rw [byteAt_some_of hpa' hd' (v := 1) (by decide)]; rfl, by omega⟩
  · intro k m hm hb
    obtain ⟨e, he, het, hlw⟩ := hW k m hm
    rcases qWW_writer (hQ 0) he het with rfl | ⟨rfl, _⟩
    · simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      rw [byteAt_some_of hlw.1.symm hlw.2.symm (v := 1) (by decide)] at hb; cases hb
    · simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      rw [byteAt_none_of hlw.1.symm hlw.2.symm (by decide)] at hb; cases hb

/-- A0 for the MP rows, given the two harts' fences. -/
theorem mp_verdict {T : Test} {M : List PMsg} {run : PFRun LP Unit} (pw sw : Bool) (rb : Nat)
    (hT0 : T.prog 0 = [.store 4 5 6 0, .fence ⟨false, true, false, false, false, true, false, false⟩, .store 4 5 7 0])
    (hT1 : T.prog 1 = [.load 4 true 5 6 0, .fence ⟨true, pw, false, false, true, sw, false, false⟩, .load 4 true 7 rb 0])
    (hn : T.harts.length = 2) (hrb : rb ≠ 0 ∧ rb ≠ 5 ∧ rb < 32)
    (hr0 : ((T.regs0[0]?).getD []).lookup 5 = some 1 ∧ ((T.regs0[0]?).getD []).lookup 6 = some X ∧
      ((T.regs0[0]?).getD []).lookup 7 = some Y)
    (hr1 : ((T.regs0[1]?).getD []).lookup 6 = some Y ∧ ((T.regs0[1]?).getD []).lookup rb = some X)
    (hx : testImg T (X : Int) = some 0) (hy : testImg T (Y : Int) = some 0)
    (hrun : validRun litStep (testImg T) () (progs T) M run) :
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  have hnoinv := Own.lit_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (T := T) (QsMP M rb)
    (fun h _ => match h with | 0 => wwDone M 0 (X : Int) (Y : Int) (toBytes 1 4) (toBytes 1 4) | _ => True) trivial
    (QsMP_nil M rb)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWW_hart _ M 0 p 4 X Y 1 1 6 7 5 5 false false (by rw [hpr, hT0]) hpc hq (by decide)
          (by rw [hrd 5 (by decide) (by decide), hr0.1]; rfl) (by rw [hrd 5 (by decide) (by decide), hr0.1]; rfl)
          (by rw [hrd 6 (by decide) (by decide), hr0.2.1]; rfl) (by rw [hrd 7 (by decide) (by decide), hr0.2.2]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hRR_hart _ M 1 p 4 Y X 6 rb 5 7 true pw sw (by rw [hpr, hT1]) hpc hq ⟨by decide, hrb.1, hrb.2.1⟩
          (by decide) (by decide) (by rw [hrd 6 (by decide) (by decide), hr1.1]; rfl)
          (by rw [hrd rb (by omega) hrb.2.2, hr1.2]; rfl) (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have : (progs T).length = 2 := by simp [progs, hn]
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  exact mp_glue himg (by rw [hx]) (by rw [hy]) hQ hnc hpart hwf

/-- **ROW 8, MP+fence.w.w+fence.r.rw (repo `SAFE/MP+fence.w.w+fence.r.rw`): FORBIDDEN, in the logic** (plan §5 row 8,
rule 4).  Over every final memory and every valid run of machine v2: not (H1's `x5 = 1` and `x7 = 0`). -/
theorem lit_mpFF : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mpFF) () (progs Weak.Prom.Ref.Lit.mpFF) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) :=
  fun _ _ hrun => mp_verdict false true 8 rfl rfl rfl (by decide) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl hrun

/-- **ROW 8′, MP+fence.w.w+fence.r.r (the plan's reader): FORBIDDEN, in the logic** (plan §5 row 8, rule 4). -/
theorem lit_mpFFrr : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mpFFrr) () (progs Weak.Prom.Ref.Lit.mpFFrr) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) :=
  fun _ _ hrun => mp_verdict false false 8 rfl rfl rfl (by decide) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl hrun


/-! ## 5. Row 9, MP+fence.w.w+addr -/

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **The address-dependent reader in the logic**: `ld d0,(p0); xor t,d0,d0; add q,pb,t; ld d1,(q)` proves `qRR`
(rule 9): `xor` gives `regv t = regv d0 ≥ s0` although `t = 0` (a syntactic dependency, §rvwmo "Most non-memory
instructions carry a dependency from each of their source registers to each of their destination registers"),
`add` passes it to the address register, and the second load's pre-view contains its address view. -/
theorem hRaddr_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a0 a1 p0 pb d0 t q d1 : Nat) (sg : Bool)
    (hprog : s0.prog = [.load n sg d0 p0 0, .alu .xor t d0 d0, .alu .add q pb t, .load n sg d1 q 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p0 ≠ 0 ∧ d0 ≠ 0 ∧ t ≠ 0 ∧ q ≠ 0 ∧ pb ≠ d0 ∧ pb ≠ t ∧ t ≠ d0)
    (hlen : s0.regs.length = 32) (hr : t < 32 ∧ q < 32) (hn : 0 < n) (hpb : pb ≠ 0)
    (ha0 : s0.rd p0 = a0) (ha1 : s0.rd pb = a1) (hal0 : a0 < two64) (hal1 : a1 < two64)
    (hA0 : aligned a0 n = true) (hA1 : aligned a1 n = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qRR M a0 a1 n [.DReg p0] [.DReg q])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d0) (rs1 := p0) (off := 0) (base := (a0 : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha0 hal0 hA0) (base_of ha0 hal0))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpK_alu hw (hag s1) hq1 (by rw [hP1, hc1]; rfl) hnz.2.2.1)
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_alu hw (hag s2) hq2 (by rw [hP2, hc2]; rfl) hnz.2.2.2.1)
  iframe Hl
  inext
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  -- the address register holds `a1 + (v xor v) = a1`
  have e2 : s2.rd t = 0 := by
    rw [LPstep_rd_eq hs2 hnz.2.2.1 (by rw [LPstep_len hs1, hlen]; exact hr.1)]
    simp [aluOp]
  have e2b : s2.rd pb = a1 := by
    rw [LPstep_rd hs2 pb (.inl hnz.2.2.2.2.2.1), LPstep_rd hs1 pb (.inl hnz.2.2.2.2.1), ha1]
  have e3 : s3.rd q = a1 := by
    rw [LPstep_rd_eq hs3 hnz.2.2.2.1 (by rw [LPstep_len hs2, LPstep_len hs1, hlen]; exact hr.2), e2b, e2]
    simp [aluOp, Nat.mod_eq_of_lt hal1]
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d1) (rs1 := q) (off := 0) (base := (a1 : Int)) hw (hag s3) hq3
    (by rw [hP3, hc3]; rfl) (alg_of e3 hal1 hA1) (base_of e3 hal1))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M a1 (src0 (LLoad false false (a1 : Int) tvs1 (srcR q), none))
      (src0 (LLoad false false (a0 : Int) tvs0 (srcR p0), none)) := by
    intro hnc
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 hn
    obtain ⟨t1, v1, r1, rfl⟩ := tvs_cons hl1 hn
    have hw1 := (loadOk_b0nc hnc hlo1).2
    have hb0 := (loadRun_b0 psInit false false (srcsView psInit (srcR p0)) (a0 : Int) t0 v0 r0).1
    rw [fwdView_empty rfl] at hb0
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show t0 ≤ _
    simp [ldPre, regWL, hnz.1, hnz.2.1, hnz.2.2.1, hnz.2.2.2.1, hnz.2.2.2.2.1, hnz.2.2.2.2.2.1,
      hnz.2.2.2.2.2.2, hpb] at hb0 ⊢
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩, ⟨tvs1, by rw [srcR_pos hnz.2.2.2.1], hl1⟩, hord⟩⟩
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  iapply (wpK_fin hq4 (by rw [hP4, hc4]; simp))
  iexact Hl

end harts

/-- **ROW 9, MP+fence.w.w+addr (repo `SAFE/MP+fence.w.w+addr`): FORBIDDEN, in the logic** (plan §5 row 9, rules
4, 9). -/
theorem lit_mpFAddr : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mpFAddr) () (progs Weak.Prom.Ref.Lit.mpFAddr) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  intro M run hrun
  have hnoinv := Own.lit_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsMP M 10)
    (fun h _ => match h with | 0 => wwDone M 0 (X : Int) (Y : Int) (toBytes 1 4) (toBytes 1 4) | _ => True) trivial
    (QsMP_nil M 10)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWW_hart _ M 0 p 4 X Y 1 1 6 7 5 5 false false (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 5 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 7 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hRaddr_hart _ M 1 p 4 Y X 6 9 5 7 10 8 true (by rw [hpr]; rfl) hpc hq (by decide) hlen (by decide)
          (by decide) (by decide) (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.mpFAddr).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  exact mp_glue himg rfl rfl hQ hnc hpart hwf

#print axioms Weak.Prom.PF.lit_mpFAddr

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_mpFF
#print axioms Weak.Prom.PF.lit_mpFFrr
