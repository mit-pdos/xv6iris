/-
Weak/Prom: **E-a3: the TENURE-DEPENDENT RACY READ on track (a) — definitions** (stage E-a3; owner ruling [OWN.P13];
G4-review2.md §1 note 1 "xv6's `holding()` inside `acquire` on a hart that previously held the lock cannot be
settled by a value protocol … What is needed there is author-indexed (`PMsg.tid` …) plus the reader's own coherence
over its own earlier writes", §6 A-1′, §8 item 8 "author-aware"; plan rev 7 §4 G4 (3)).

The test (`t6`): BOTH harts run the same xv6 text — acquire (Xv6/KernelImage.lean acquire+0x16..+0x28: `li a4,1;
mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5; bnez a5,again; sd a0,16(s1)`), release (release+0x12..+0x1a:
`sd zero,16(s1); fence rw,w; sw zero,0(s1)`), then the NEXT acquire's `holding()` panic test (holding+0x0..+0x1e
folded as in G4 (3), OwnAHold.lean: `lw a5,0(s1); beqz a5,end; ld a5,16(s1); sub a3,a5,a0; seqz a3,a3;
beqz a3,end; sd a0,0(a2)`, the panic being a store to the marker `Fp`).  `s1 = x9 = Lk`, `a0 = x10 = mycpu()`
(`cpuOf h`), `a2 = x12 = Fp`:
`0: li a4,1  1: mv a5,a4  2: amoswap.w.aq a5,a5,(s1)  3: sext.w a5,a5  4: bnez a5,1  5: sd a0,16(s1)
 6: sd zero,16(s1)  7: fence rw,w  8: sw zero,0(s1)  9: lw a5,0(s1)  10: beqz a5,16  11: ld a5,16(s1)
 12: sub a3,a5,a0  13: sltiu a3,a3,1  14: beqz a3,16  15: sd a0,0(a2)`.
Each hart's cpu WAS in the field during its own tenure, so no value protocol settles the read.

What this file provides:
* THE PROTOCOL `π6` — AUTHOR-AWARE, timestamp-blind (plan §0 `Proto`; `PMsg.tid`, Machine.lean:76): a message
  touching the cpu field is an 8-byte message at it, by a hart `h < 2`, holding `0` or `cpuOf h` (its author's
  `mycpu()`).  The field's xv6 invariant "only `mycpu()` or 0 is ever written by a hart" — no tenure in it;
* per-author classes and the lower-bounded bags `lbB` (acquire AMOs, cpu-field messages of the author);
* THE RACY READ (`pc_read6`, pure): a hart `h` whose coherence floor on the field's 8 bytes covers its OWN
  `sd zero` at `t2` reads each byte from `t2` (value 0), from a message ABOVE `t2` that `h` itself authored
  (a member of `h`'s own bag: the caller dooms with its `pend`), or from the other hart's message, whose byte meets
  `π6` under the core's guard `⟦t⟧` (`grd_self`): value `0` or the OTHER hart's cpu.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEBase

namespace Weak.Prom.OA.E3

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.OA.C (Pc msgAt_of)
open Weak.Prom.OA.H (Fp noF shp bS)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The text, the test -/

/-- The text (see the header). -/
def p6 : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 14 1), .i (.alu .add 15 0 14), .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9),
   .addiw 15 15 0, .i (.br .ne 15 0 1), .i (Weak.Prom.Ref.Lit.sd 10 9 16),
   .i (Weak.Prom.Ref.Lit.sd 0 9 16), .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 9 0),
   .i (Weak.Prom.Ref.Lit.lw 15 9), .i (.br .eq 15 0 16), .i (Weak.Prom.Ref.Lit.ld 15 9 16),
   .i (.alu .sub 13 15 10), .i (.alui .sltu 13 13 1), .i (.br .eq 13 0 16), .i (Weak.Prom.Ref.Lit.sd 10 12)]

abbrev b6 : List Instr := p6.map XI.base

/-- `mycpu()` of hart `h`. -/
def cpuOf (h : Nat) : Nat := 0x3000 + 0x100 * h

/-- The test: two harts run `p6`; `a0 = mycpu()` differs per hart; image all zero. -/
def t6 : Test :=
  { harts := [b6, b6]
    regs0 := [[(9, X), (10, 0x3000), (12, 0x4000)], [(9, X), (10, 0x3100), (12, 0x4000)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev xs6 : List (List XI) := [p6]

theorem xOf_6 : xOf xs6 b6 = some p6 := by decide

theorem p6_at {s : LP} (h : s.prog = b6) : xOf xs6 s.prog = some p6 := by rw [h]; exact xOf_6

abbrev w6 (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs6 imgL M h

/-- The trace invariant of every hart: no panic store. -/
def qs6 : Nat → Trace → Prop := fun _ ev => noF ev

theorem progs_6 : ∃ p0 p1 : LP, progs t6 = [p0, p1] := ⟨_, _, rfl⟩

/-! ## 2. The protocol (author-aware) -/

/-- **THE PROTOCOL of the cpu field**: a message touching it is an 8-byte message at it, by a hart `h < 2`, holding
`0` or `cpuOf h`. -/
def π6 : Proto :=
  ⟨fun m => tchB m Pc 8 = true → m.pa = Pc ∧ ∃ h, h < 2 ∧ m.tid = some h ∧
      (m.data = toBytes 0 8 ∨ m.data = toBytes (cpuOf h) 8), fun _ => True⟩

theorem ok6_pc {h v : Nat} {c : PClass} (hh : h < 2) (hv : v = 0 ∨ v = cpuOf h) :
    π6.okMsg ⟨Pc, toBytes v 8, some h, c⟩ := fun _ => ⟨rfl, h, hh, rfl, by rcases hv with rfl | rfl <;> simp⟩

theorem ok6_lk {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length ≤ 16) :
    π6.okMsg ⟨Lk, d, tid, c⟩ := fun ht => by
  rw [tchB_far (.inl (by simp only [Pc]; omega))] at ht; cases ht

theorem ok6_fp {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} : π6.okMsg ⟨Fp, d, tid, c⟩ := fun ht => by
  rw [tchB_far (.inr (by simp [Pc, Lk, Fp, X]))] at ht; cases ht

/-! ## 3. Classes (per author) -/

/-- Hart `h`'s acquire AMO write. -/
def mA6 (h : Nat) : PMsg := ⟨Lk, toBytes 1 4, some h, .excl⟩
/-- Hart `h`'s release word. -/
def mR6 (h : Nat) : PMsg := ⟨Lk, toBytes 0 4, some h, .plain⟩
/-- Hart `h`'s panic marker. -/
def mF6 (h : Nat) : PMsg := ⟨Fp, toBytes (cpuOf h) 8, some h, .plain⟩

/-- A message by `h` touching the cpu field (ANY shape or content). -/
def pcP (h : Nat) (m : PMsg) : Prop := m.tid = some h ∧ tchB m Pc 8 = true
instance (h : Nat) : DecidablePred (pcP h) := fun m => by unfold pcP; infer_instance

def isP6 (M : List PMsg) (h t : Nat) : Bool := clsB (pcP h) M t

/-- Authored by `h`. -/
def byA (M : List PMsg) (h t : Nat) : Bool := clsB (fun m => m.tid = some h) M t

theorem mA6_tid (h : Nat) : (mA6 h).tid = some h := rfl
theorem mR6_tid (h : Nat) : (mR6 h).tid = some h := rfl
theorem mF6_tid (h : Nat) : (mF6 h).tid = some h := rfl

theorem tch_A (h : Nat) : tchB (mA6 h) Pc 8 = false := tchB_far (.inl (by simp only [mA6, Pc, toBytes_length]; omega))
theorem tch_R (h : Nat) : tchB (mR6 h) Pc 8 = false := tchB_far (.inl (by simp only [mR6, Pc, toBytes_length]; omega))
theorem tch_F (h : Nat) : tchB (mF6 h) Pc 8 = false := tchB_far (.inr (by simp [mF6, Pc, Lk, Fp, X]))

theorem mA_R (h : Nat) : mR6 h ≠ mA6 h := fun e => absurd (congrArg PMsg.data e) (by simp [mA6, mR6]; decide)
theorem mA_F (h : Nat) : mF6 h ≠ mA6 h := fun e => absurd (congrArg PMsg.pa e) (by simp [mA6, mF6, Lk, Fp, X])
theorem mR_F (h : Nat) : mF6 h ≠ mR6 h := fun e => absurd (congrArg PMsg.pa e) (by simp [mR6, mF6, Lk, Fp, X])

theorem shp_msg {M : List PMsg} {m0 : PMsg} {t : Nat} (h : shp M m0 t = true) : msgAt M t = some m0 :=
  of_decide_eq_true h

/-! ## 4. The racy read of the cpu field (pure) -/

/-- A byte of the cpu field: `0`'s or `cpuOf o`'s. -/
def okB6 (o j : Nat) (v : BitVec 8) : Prop := some v = (toBytes 0 8)[j]? ∨ some v = (toBytes (cpuOf o) 8)[j]?

theorem msg_byte {img : Image} {M : List PMsg} {t : Nat} {m : PMsg} {a : Int} {v : BitVec 8}
    (hmt : msgAt M t = some m) (hb : memByte img M t a = some v) : m.byteAt a = some v := by
  cases t with
  | zero => cases hmt
  | succ k =>
    obtain ⟨m', hm', hba⟩ := memByte_succ hb
    simp only [msgAt] at hmt
    rw [hmt] at hm'; cases hm'; exact hba

/-- ONE BYTE of hart `h`'s cpu-field load, with its floor covering `h`'s OWN `sd zero` at `t2`: the byte of `t2`
(`0`), a message of `h`'s own above `t2`, or — under `⟦|M|⟧` — a byte of the other hart's `0` or `cpuOf`. -/
theorem pc_byte6 {M : List PMsg} {h t2 t j fl : Nat} {v : BitVec 8} (hh : h < 2) (hj : j < 8)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (hm2 : msgAt M t2 = some ⟨Pc, toBytes 0 8, some h, .plain⟩)
    (hfl : t2 ≤ fl) (hb : memByte imgL M t (Pc + j) = some v)
    (hr : ¬ writesIn M (Pc + j) t fl ∨ invalRead M (Pc + j) t fl) :
    (t2 < t ∧ isP6 M h t = true) ∨ grd π6 imgL M M.length (okB6 (1 - h) j v) := by
  have hwa : ((⟨Pc, toBytes 0 8, some h, .plain⟩ : PMsg).byteAt (Pc + j)).isSome = true := by
    rw [byteAt_off rfl, List.getElem?_eq_getElem (by rw [toBytes_length]; omega)]; rfl
  rcases src_ge_lw (.inr ⟨_, hm2, hwa, rfl⟩) hfl hb hr with heq | ⟨hlt, m, hmt, hba⟩ | ⟨ti, _, hc⟩
  · -- the own `sd zero`
    rw [heq] at hb
    have hb2 := msg_byte hm2 hb
    rw [byteAt_off rfl] at hb2
    exact .inr (grd_intro (.inl hb2.symm))
  · by_cases ht : m.tid = some h
    · left; refine ⟨hlt, ?_⟩; rw [isP6, clsB_of hmt]; exact decide_eq_true ⟨ht, tchB_of hj hba⟩
    · right
      refine grd_mono (msgAt_le hmt).2 (grd_imp (fun hok => ?_) (grd_self hmt))
      obtain ⟨hp, h', hh', htid, hd⟩ := hok (tchB_of hj hba)
      have ho : h' = 1 - h := by
        have : h' ≠ h := fun e => ht (by rw [htid, e])
        omega
      subst ho
      have hb' := msg_byte hmt hb
      rw [← hp, byteAt_off rfl] at hb'
      unfold okB6
      rcases hd with hd | hd <;> rw [hd] at hb'
      · exact .inl hb'.symm
      · exact .inr hb'.symm
  · exact absurd hc (hnoinv _ _)

theorem cpu_bytes {o : Nat} (ho : o < 2) :
    toBytes (cpuOf o) 8 = [0, BitVec.ofNat 8 (0x30 + o), 0, 0, 0, 0, 0, 0] := by
  rcases (by omega : o = 0 ∨ o = 1) with rfl | rfl <;> decide

/-- **THE TENURE-DEPENDENT RACY READ** (pure): hart `h`'s load of the cpu field, every byte's floor covering its OWN
`sd zero` at `t2`, read one of `h`'s own messages above `t2` (doom), or its value is `⟦|M|⟧ (0 ∨ cpuOf (1 - h))`. -/
theorem pc_read6 {M : List PMsg} {h t2 : Nat} {tvs : List (Nat × BitVec 8)} (hh : h < 2) (hl : tvs.length = 8)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (hm2 : msgAt M t2 = some ⟨Pc, toBytes 0 8, some h, .plain⟩)
    (hw : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → memByte imgL M t (Pc + j) = some v ∧
      ∃ fl, t2 ≤ fl ∧ (¬ writesIn M (Pc + j) t fl ∨ invalRead M (Pc + j) t fl)) :
    (∃ t, t2 < t ∧ isP6 M h t = true) ∨
      grd π6 imgL M M.length (ldVal true 8 tvs = 0 ∨ ldVal true 8 tvs = cpuOf (1 - h)) := by
  by_cases hd : ∃ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) ∧ t2 < t ∧ isP6 M h t = true
  · obtain ⟨_, t, _, _, h1, h2⟩ := hd; exact .inl ⟨t, h1, h2⟩
  right
  have kb : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → j < 8 →
      grd π6 imgL M M.length (okB6 (1 - h) j v) := by
    intro j t v hj hj8
    obtain ⟨hb, fl, hfl, hr⟩ := hw j t v hj
    rcases pc_byte6 hh hj8 hnoinv hm2 hfl hb hr with hx | hx
    · exact absurd ⟨j, t, v, hj, hx⟩ hd
    · exact hx
  intro hV
  obtain ⟨t0, v0, t1, v1, t2', v2, t3, v3, t4, v4, t5, v5, t6, v6, t7, v7, rfl⟩ :
      ∃ t0 v0 t1 v1 t2 v2 t3 v3 t4 v4 t5 v5 t6 v6 t7 v7,
        tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3), (t4, v4), (t5, v5), (t6, v6), (t7, v7)] := by
    match tvs, hl with
    | [(a0, b0), (a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)], _ =>
      exact ⟨a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, rfl⟩
  have k0 := kb 0 _ _ rfl (by decide) hV
  have k1 := kb 1 _ _ rfl (by decide) hV
  have k2 := kb 2 _ _ rfl (by decide) hV
  have k3 := kb 3 _ _ rfl (by decide) hV
  have k4 := kb 4 _ _ rfl (by decide) hV
  have k5 := kb 5 _ _ rfl (by decide) hV
  have k6 := kb 6 _ _ rfl (by decide) hV
  have k7 := kb 7 _ _ rfl (by decide) hV
  have e0 : toBytes 0 8 = [0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have ho : 1 - h < 2 := by omega
  unfold okB6 at k0 k1 k2 k3 k4 k5 k6 k7
  rw [e0, cpu_bytes ho] at k0 k1 k2 k3 k4 k5 k6 k7
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, or_self] at k0 k1 k2 k3 k4 k5 k6 k7
  subst k0 k2 k3 k4 k5 k6 k7
  have hmap : [(t0, (0 : BitVec 8)), (t1, v1), (t2', 0), (t3, 0), (t4, 0), (t5, 0), (t6, 0), (t7, 0)].map
      Prod.snd = [0, v1, 0, 0, 0, 0, 0, 0] := rfl
  unfold ldVal
  rw [if_pos rfl, hmap]
  rcases k1 with rfl | rfl
  · left; decide
  · right
    rcases (by omega : 1 - h = 0 ∨ 1 - h = 1) with e | e <;> rw [e] <;> decide

/-! ## 5. Coherence over the hart's own write -/

/-- The coherence floor of the cpu field's 8 bytes covers `t2`. -/
def cohP (t2 : Nat) (ws : PState) : Prop := ∀ j : Nat, j < 8 → t2 ≤ coh ws (Pc + j)

theorem cohP_mono {t2 : Nat} {ws ws' : PState} (h : ∀ x, coh ws x ≤ coh ws' x) (hc : cohP t2 ws) :
    cohP t2 ws' := fun j hj => Nat.le_trans (hc j hj) (h _)

/-- A load whose pre-state's floor covers `t2` (`loadOk`'s floors are at least `coh`). -/
theorem loadOk_cohP {M : List PMsg} {ws : PState} {vpre t2 : Nat} {tvs : List (Nat × BitVec 8)}
    (hlo : loadOk imgL M ws vpre Pc tvs) (hc : cohP t2 ws) (hl : tvs.length = 8) :
    ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → memByte imgL M t (Pc + j) = some v ∧
      ∃ fl, t2 ≤ fl ∧ (¬ writesIn M (Pc + j) t fl ∨ invalRead M (Pc + j) t fl) := by
  intro j t v hj
  have hj8 : j < 8 := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hj).1
  unfold loadOk at hlo
  obtain ⟨hb, hr⟩ := bytesAll_get hlo hj
  refine ⟨hb, ?_⟩
  rcases hr with hr | hr
  · exact ⟨_, Nat.le_trans (hc j hj8) (Nat.le_max_right _ _), .inl hr⟩
  · exact ⟨_, Nat.le_trans (hc j hj8) (Nat.le_max_right _ _), .inr hr⟩

theorem coh_qPosts_regW (ws : PState) (x : Int) :
    coh (qPosts ws (regWL 15 [.DLdRes] ++ [LInstr])) x = coh ws x := by
  simp only [regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost]; rfl

/-! ## 6. Bags (per author, lower-bounded) -/

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The `pend`s of the messages of class `c` above `lo`. -/
def lbB (g : AGN) (M : List PMsg) (c : Nat → Bool) (lo : Nat) : IProp GF :=
  iprop([∗list] t ∈ (rng M).filter (fun t => decide (lo < t) && c t), pend g t)

theorem lbB_take (g : AGN) (M : List PMsg) (c : Nat → Bool) {lo ts : Nat} (hlt : lo < ts) (hc : c ts = true)
    (hM : 1 ≤ ts ∧ ts ≤ M.length) : lbB (GF := GF) g M c lo ⊢ pend g ts ∗ lbB g M c ts := by
  unfold lbB
  exact bsl_filter_take (pend g) (fun t => decide (lo < t) && c t) (fun t => decide (ts < t) && c t) ts
    (by simp [hc, hlt])
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 hM) (nodup_rng M)

/-- Hart `h`'s boot resources: its acquire AMOs, its cpu-field messages, its release words, its markers. -/
def bags (g : AGN) (M : List PMsg) (h : Nat) : IProp GF :=
  iprop(lbB g M (shp M (mA6 h)) 0 ∗ lbB g M (isP6 M h) 0 ∗ bS g M (mR6 h) ∗ bS g M (mF6 h))

/-- One author's messages to its bags. -/
theorem split_h (g : AGN) (M : List PMsg) (h : Nat) :
    ([∗list] t ∈ (rng M).filter (byA M h), pend (GF := GF) g t) ⊢ bags g M h := by
  iintro H
  ihave ⟨HA, H⟩ := bsl_peel (pend (GF := GF) g) (shp M (mA6 h)) (byA M h)
    (fun t ht => by simp [byA, clsB_of (shp_msg ht), mA6_tid]) (rng M) $$ H
  ihave ⟨HP, H⟩ := bsl_peel (pend (GF := GF) g) (isP6 M h) (fun t => byA M h t && !shp M (mA6 h) t)
    (fun t ht => by
      obtain ⟨m, hm, ht1, htch⟩ := clsB_iff.1 ht
      have hne : m ≠ mA6 h := fun e => by rw [e, tch_A] at htch; cases htch
      simp [byA, shp, clsB_of hm, hm, ht1, hne]) (rng M) $$ H
  ihave ⟨HR, H⟩ := bsl_peel (pend (GF := GF) g) (shp M (mR6 h))
    (fun t => byA M h t && !shp M (mA6 h) t && !isP6 M h t)
    (fun t ht => by
      have hm := shp_msg ht
      simp [byA, isP6, shp, clsB_of hm, hm, pcP, mR6_tid, tch_R, mA_R]) (rng M) $$ H
  ihave ⟨HF, -⟩ := bsl_peel (pend (GF := GF) g) (shp M (mF6 h))
    (fun t => byA M h t && !shp M (mA6 h) t && !isP6 M h t && !shp M (mR6 h) t)
    (fun t ht => by
      have hm := shp_msg ht
      simp [byA, isP6, shp, clsB_of hm, hm, pcP, mF6_tid, tch_F, mA_F, mR_F]) (rng M) $$ H
  unfold bags lbB bS
  iframe HR HF
  isplitl [HA]
  · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
      simp only [Bool.and_eq_true] at ht; exact ht.2) (rng M) $$ HA
  · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
      simp only [Bool.and_eq_true] at ht; exact ht.2) (rng M) $$ HP

/-- **THE SETUP** (plan R-a5, per-author owners from boot): hart `h` owns the `pend` of every message it authors
(the rest stays with the boot owner, unused).  Nothing is dead, nothing is shared. -/
theorem setup6 (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ bags g M 0 ∗ bags g M 1 := by
  iintro Hp
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  ihave ⟨H0, Hp⟩ := bsl_filter_split (pend (GF := GF) g) (byA M 0) (rng M) $$ Hp
  ihave ⟨H1, -⟩ := bsl_peel (pend (GF := GF) g) (byA M 1) (fun t => !byA M 0 t)
    (fun t ht => by
      obtain ⟨m, hm, ht1⟩ := clsB_iff.1 ht
      rw [byA, clsB_of hm]; simp [ht1]) (rng M) $$ Hp
  isplitl [H0]
  · iapply split_h; iexact H0
  · iapply split_h; iexact H1

end res

end Weak.Prom.OA.E3
