/-
Weak/Prom: **row 23, Par-Inc (atomicity), proved IN THE LOGIC** (stage S2; plan rev 7 §5 row 23 "FORBIDDEN
(atomicity) — `exclOk`", §8 S2).

`Lit.parInc`: `li t,1; amoadd.w a0,t,(x)` ‖ the same; FORBIDDEN: `x = 1` finally (both harts finished).
* Each hart's Ψ (`qPI`): its one memory entry is its AMO, whose byte-0 source is below its timestamp (COH) and whose
  ATOMICITY window holds (`exclOk`, the AMO arm's premise; rvwmo.adoc Atomicity Axiom "there can be no store from
  a hart other than h to byte x following s and preceding w in the global memory order"): no other hart writes x
  between the source and the AMO.  Its postcondition (A0 (i)): its AMO's message is in `M`.
* Contradiction: let `ta < tb` be the two AMOs (the other order is symmetric, `parInc_case`).  B's window excludes
  A's write from `(s_B, t_B)`, so `s_B ≥ t_A`, and the only writes to x are the two AMOs, so `s_B = t_A`: B read A's
  result.  A read below `t_A < t_B`, so it read the image's 0.  Byte 0: A writes `0 + 1 = 1`, B writes `1 + 1 = 2`,
  and B is the last write to x: the final value is not 1.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitAd

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet AmoOp)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- An AMO hart's Ψ: one AMO at `a`, its byte-0 source below its timestamp, no other hart's write to byte 0 in
between. -/
def qPI (M : List PMsg) (h : Nat) (a : Int) (p r : Nat) : Trace → Prop :=
  q1 (fun e => isRmw false false a 4 (amoD .add 4 1) [.DReg p] [.DReg r] e ∧ src0 e < tsOf e ∧
    ¬ writesInBy M (fun tid => tid ≠ some h) a (src0 e) (tsOf e - 1))

/-- An AMO hart's postcondition: its AMO's message is in `M`. -/
def piDone (M : List PMsg) (h : Nat) (a : Int) : Prop :=
  ∃ t d, 0 < t ∧ M[t - 1]? = some ⟨a, d, some h, .excl⟩

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **The Par-Inc hart in the logic**: `li r,1; amoadd.w rd,r,(p)` proves `qPI` (COH, `exclOk`). -/
theorem hPI_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a r rd p : Nat)
    (hprog : s0.prog = [.alui .add r 0 1, .amo .add 4 false false rd r p]) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hnz : r ≠ 0 ∧ p ≠ 0 ∧ p ≠ r) (hlen : r < s0.regs.length) (ha : s0.rd p = a) (hal : a < two64)
    (hA : aligned a 4 = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qPI M h a p r)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V (piDone M h a)⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r = 1 := li_val hs1 hnz.1 hlen (by decide)
  have e1a : s1.rd p = a := by rw [LPstep_rd hs1 p (.inl hnz.2.2), ha]
  iapply (wpK_amo (base := (a : Int)) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl) (by rw [e1a]; exact hA) (by rw [e1a]))
  iframe Hl
  inext
  iintro %tvs %ts %hl %_ %hmsg %_ %hex %hcoh %hext
  obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl (by decide)
  have hsrc : t0 < ts := by
    have hb0 := loadRun_coh0 (instrR (regWP psInit r (srcR 0))) false false
      (srcsView (instrR (regWP psInit r (srcR 0))) (srcR p)) (a : Int) t0 v0 r0
    have h1 := cohBelow_b0 hcoh (by rw [amoD, toBytes_length]; decide)
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨_, ts, by omega, by simp only [e1, srcR_pos hnz.2.1, srcR_pos hnz.1], hl⟩, hsrc, hex.1⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_finP hq2 (by rw [hP2, hc2]; simp) ⟨ts, _, by omega, hmsg⟩)
  iexact Hl

end hart

/-! ## The contradiction -/

/-- `amoadd` of 1, byte 0: the read byte plus one. -/
theorem amoAdd_b0 (t : Nat) (v : BitVec 8) (r : List (Nat × BitVec 8)) :
    (amoD .add 4 1 ((t, v) :: r))[0]? = some (BitVec.ofNat 8 ((v.toNat + 1) % 256)) := by
  simp only [amoD, amoOp, toBytes, byteList, List.range, List.range.loop, List.map, List.getElem?_cons_zero,
    Option.some.injEq, bv8, Nat.shiftRight_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  simp only [ofBytes, bytesVal, List.map, List.foldr_cons]
  rw [Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 32)]
  omega

/-- The writer of a message among the two Par-Inc harts, with its author: hart `h`'s AMO entry. -/
theorem pi_writer {run : PFRun LP Unit} {M : List PMsg}
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) (hQ : ∀ h, h < 2 → qPI M h (X : Int) 6 5 (memEv (run.trace h)))
    (hout : ∀ h, 2 ≤ h → memEv (run.trace h) = []) {k : Nat} {m : PMsg} (hm : M[k]? = some m) :
    ∃ h, h < 2 ∧ m.tid = some h ∧ ∃ tvs, (LRmw false false (X : Int) tvs (amoD .add 4 1 tvs) [.DReg 6] [.DReg 5],
      some (k + 1)) ∈ memEv (run.trace h) ∧ tvs.length = 4 ∧ m.pa = (X : Int) ∧ m.data = amoD .add 4 1 tvs ∧
      src0 (LRmw false false (X : Int) tvs (amoD .add 4 1 tvs) [.DReg 6] [.DReg 5], some (k + 1)) < k + 1 ∧
      ¬ writesInBy M (fun tid => tid ≠ some h) (X : Int)
        (src0 (LRmw false false (X : Int) tvs (amoD .add 4 1 tvs) [.DReg 6] [.DReg 5], some (k + 1))) k := by
  have hkl : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
  obtain ⟨h, ⟨hin, htid⟩, _⟩ := hpart (k + 1) (by omega) (by omega)
  unfold PFRun.fulfils fulfilsOf at hin
  obtain ⟨e, he, het⟩ := List.mem_filterMap.1 hin
  have hme : e ∈ memEv (run.trace h) := memEv_of_ts (τ := run.trace h) he het
  have hh : h < 2 := by
    by_cases hh : h < 2
    · exact hh
    · rw [hout h (by omega)] at hme; cases hme
  have htid' : m.tid = some h := by simpa [tidAt, msgAt, hm] using htid
  rcases q1_cases (hQ h hh) with hev | ⟨e0, hev, ⟨tvs, t0, _, rfl, hl⟩, hsrc, hex⟩
  · rw [hev] at hme; cases hme
  · rw [hev, List.mem_singleton] at hme
    subst hme
    cases het
    obtain ⟨m', hm', hpa, hd⟩ := kit_msg hwf (e := (LRmw false false (X : Int) tvs (amoD .add 4 1 tvs) [.DReg 6]
      [.DReg 5], some (k + 1))) (by rw [hev]; simp) rfl rfl
    simp only [Nat.add_sub_cancel] at hm'
    rw [hm] at hm'; cases hm'
    exact ⟨h, hh, htid', tvs, by rw [hev]; simp, hl, hpa, hd, hsrc, by simpa [tsOf] using hex⟩

/-- A one-entry pattern: two members are equal. -/
theorem q1_mem_uniq {P0 : PEv → Prop} {ev : Trace} {e e' : PEv} (hQ : q1 P0 ev) (he : e ∈ ev) (he' : e' ∈ ev) :
    e = e' := by
  rcases q1_cases hQ with rfl | ⟨e0, rfl, _⟩
  · cases he
  · rw [List.mem_singleton] at he he'; rw [he, he']

/-- **The Par-Inc contradiction, for one order of the two AMOs** (`ta < tb`, A by hart `i`, B by hart `j ≠ i`). -/
theorem parInc_case {run : PFRun LP Unit} {M : List PMsg} {img : Image} (himg : run.cfg.pcImg = img)
    (hx : img (X : Int) = some 0)
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) (hQ : ∀ h, h < 2 → qPI M h (X : Int) 6 5 (memEv (run.trace h)))
    (hout : ∀ h, 2 ≤ h → memEv (run.trace h) = []) {i j : Nat} (hij : i ≠ j) {ka kb : Nat} {ma mb : PMsg}
    (hma : M[ka]? = some ma) (hmb : M[kb]? = some mb) (hta : ma.tid = some i) (htb : mb.tid = some j)
    (hlt : ka < kb) (hfin : lastByte img M (X : Int) = 1) : False := by
  obtain ⟨ia, _, hia, tvsA, hinA, hlA, hpaA, hdA, hsA, _⟩ := pi_writer hpart hwf hQ hout hma
  obtain ⟨ib, _, hib, tvsB, hinB, hlB, hpaB, hdB, hsB, hexB⟩ := pi_writer hpart hwf hQ hout hmb
  rw [hta] at hia; cases hia
  rw [htb] at hib; cases hib
  obtain ⟨uA, vA, rA, rfl⟩ := tvs_cons hlA (by decide)
  obtain ⟨uB, vB, rB, rfl⟩ := tvs_cons hlB (by decide)
  simp only [src0_rmw] at hsA hsB hexB
  have hrA := (kit_read hwf hinA rfl).1
  have hrB := (kit_read hwf hinB rfl).1
  rw [himg] at hrA hrB
  have hcovA : ma.byteAt (X : Int) = some (BitVec.ofNat 8 ((vA.toNat + 1) % 256)) := by
    rw [← hpaA, byteAt_base, hdA, amoAdd_b0]
  have hcovB : mb.byteAt (X : Int) = some (BitVec.ofNat 8 ((vB.toNat + 1) % 256)) := by
    rw [← hpaB, byteAt_base, hdB, amoAdd_b0]
  -- a message writing x is one of the two AMOs (each hart has one memory entry)
  have hwr : ∀ (k : Nat) (m : PMsg), M[k]? = some m → k = ka ∨ k = kb := by
    intro k m hm
    obtain ⟨h, hh, htid, tvs, hin, _⟩ := pi_writer hpart hwf hQ hout hm
    have hij2 : h = i ∨ h = j := by
      have hi2 : i < 2 := by
        obtain ⟨h', hh', ht', _⟩ := pi_writer hpart hwf hQ hout hma; rw [hta] at ht'; cases ht'; exact hh'
      have hj2 : j < 2 := by
        obtain ⟨h', hh', ht', _⟩ := pi_writer hpart hwf hQ hout hmb; rw [htb] at ht'; cases ht'; exact hh'
      omega
    rcases hij2 with rfl | rfl
    · have := q1_mem_uniq (hQ h hh) hin hinA; cases this; exact .inl rfl
    · have := q1_mem_uniq (hQ h hh) hin hinB; cases this; exact .inr rfl
  -- B's atomicity window excludes A's write: B read at or above A
  have hgeB : ka + 1 ≤ uB := by
    rcases Nat.lt_or_ge uB (ka + 1) with h | h
    · exact absurd ⟨ka + 1, h, by omega, ma, by simpa using hma, by rw [hcovA]; rfl, by rw [hta]; simpa using hij⟩ hexB
    · exact h
  -- so B read A's result
  obtain ⟨kB', rfl⟩ : ∃ k', uB = k' + 1 := ⟨uB - 1, by omega⟩
  obtain ⟨mB', hmB', hbB'⟩ := memByte_succ hrB
  have hkB : kB' = ka := by
    rcases hwr kB' mB' hmB' with h | h
    · exact h
    · omega
  subst hkB
  rw [hma] at hmB'; cases hmB'
  rw [hcovA] at hbB'; cases hbB'
  -- A read the image
  have hA0 : uA = 0 := by
    cases uA with
    | zero => rfl
    | succ k'' =>
      exfalso
      obtain ⟨mA', hmA', _⟩ := memByte_succ hrA
      rcases hwr k'' mA' hmA' with h | h <;> omega
  subst hA0
  simp only [memByte] at hrA
  rw [hx] at hrA; cases hrA
  -- B is the last write to x, and it wrote 2
  have hl := lastByte_eq_of (img := img) hmb (by rw [hcovB]; rfl) (fun k m' hk hm' => by
    rcases hwr k m' hm' with h | h <;> omega)
  rw [hfin, hcovB] at hl
  simp at hl

/-- **ROW 23, Par-Inc: FORBIDDEN, in the logic** (plan §5 row 23, atomicity `exclOk`): in every valid run in which
both harts finished, the final value of x is not 1. -/
theorem lit_parInc : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.parInc) () (progs Weak.Prom.Ref.Lit.parInc) M run →
    run.done litDone 0 () → run.done litDone 1 () → finalMem (testImg Weak.Prom.Ref.Lit.parInc) M X 4 ≠ 1 := by
  intro M run hrun hd0 hd1 hf
  have hnoinv := Own.lit_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨hi, hQ, _, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv)
    (fun h => match h with | 0 => qPI M 0 (X : Int) 6 5 | 1 => qPI M 1 (X : Int) 6 5 | _ => q0)
    (fun h _ => match h with | 0 => piDone M 0 (X : Int) | 1 => piDone M 1 (X : Int) | _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hPI_hart _ M 0 p X 5 10 6 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | 1 =>
        exact hPI_hart _ M 1 p X 5 10 6 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.parInc).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  have hQ' : ∀ h, h < 2 → qPI M h (X : Int) 6 5 (memEv (run.trace h)) := fun h hh => by
    match h, hh with
    | 0, _ => exact hQ 0
    | 1, _ => exact hQ 1
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2)
  obtain ⟨ta, da, hta, hma⟩ := hi 0 () hd0
  obtain ⟨tb, db, htb, hmb⟩ := hi 1 () hd1
  have hl : lastByte (testImg Weak.Prom.Ref.Lit.parInc) M (X : Int) = 1 := (finalMem_b0 hf (by decide)).trans rfl
  rcases Nat.lt_trichotomy (ta - 1) (tb - 1) with h | h | h
  · exact parInc_case himg rfl hpart hwf hQ' hout (by decide : (0 : Nat) ≠ 1) hma hmb rfl rfl h hl
  · rw [h] at hma; rw [hma] at hmb; cases hmb
  · exact parInc_case himg rfl hpart hwf hQ' hout (by decide : (1 : Nat) ≠ 0) hmb hma rfl rfl h hl

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_parInc
