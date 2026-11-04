/-
Weak/Prom: **G4 target (2′) on track (a): MP-OWNERSHIP, THE RECEIVER WRITES x** (stage S4a part 2; plan rev 7 §4 G4
(2′): "MP-ownership in which the receiver *writes* x after the hand-off (`ld flag; fence r,rw; sd 2,(x)`).  This
tests … on (a), R-a1").

Program (litmus front end, `x = X`, `flag = Y`, image all zero): H0 `sd x5,(x6); fence rw,w; sd x7,(x8)` (x5 = 42,
x6 = x, x7 = 1, x8 = flag) ‖ H1 `ld x5,(x6); fence r,rw; sd x7,(x8)` (x6 = flag, x7 = 2, x8 = x).
`own_mp2`: in every valid run, if H1's flag load returned 1, H1's write to x is COHERENCE-AFTER H0's (every
message holding H0's x-write lies below H1's write timestamp): the receiver's write lands after the hand-off.

The protocol is MP's (OwnAMPDefs.lean: x's points-to `xPts`, the flag slots holding `fR`, H0's proof unchanged),
plus H1's OWN messages (`isW`: its `sd 2,(x)` message) whose `pend`s H1 holds from the start — H1 writes x whether
or not it read the flag, so its write cannot need the hand-off; what the hand-off gives is the ORDER: after the
claim, x's latest write `lw` is `≤ vwNew` (`fence r,rw` raises `vwNew` to `vrOld ≥` the flag message), so H1's
write `ts > pv ≥ vwNew ≥ lw` (THE WRITE FLOOR); any x-message above `lw` is still in the points-to's bag (R-a1:
H1 dooms the branch with it).
0 named inputs; the runs are finite (loop-free test).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAMP
import Weak.Prom.OwnALockLib

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The test, the classes, the trace invariant -/

/-- (2′). -/
def mpW : Test :=
  { harts := [[Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8],
              [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.sd 7 8]]
    regs0 := [[(5, 42), (6, X), (7, 1), (8, Y)], [(6, Y), (7, 2), (8, X)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

/-- H1's `sd 2,(x)` message. -/
def x2Msg : PMsg := ⟨(X : Int), toBytes 2 8, some 1, .plain⟩

def isW (M : List PMsg) (t : Nat) : Bool := decide (msgAt M t = some x2Msg)
def isD2 (M : List PMsg) (t : Nat) : Bool := !isX M t && !isF M t && !isW M t

theorem x2Msg_byte_Y : x2Msg.byteAt (Y : Int) = none := by decide

abbrev imgMW : Image := testImg mpW

theorem imgMW_Y : imgMW (Y : Int) = some 0 := by decide

abbrev wMW (M : List PMsg) (h : Nat) : HW LP Unit Unit := ⟨litStep, litDone, imgMW, M, h⟩

/-- H1's invariant: if its flag load returned 1, every write it fulfils lies above every message holding H0's
x-write. -/
def q1MW (M : List PMsg) (ev : Trace) : Prop :=
  ∀ a, (loadsOf ev)[0]? = some a → obsOf a = 1 → ∀ e ∈ ev, ∀ ts, e.2 = some ts →
    ∀ t, msgAt M t = some xMsg → t < ts

def qsMW (M : List PMsg) : Nat → Trace → Prop
  | 1 => q1MW M
  | _ => fun _ => True

theorem qsMW_nil (M : List PMsg) : ∀ h, qsMW M h [] := by
  intro h
  match h with
  | 1 => intro a ha; cases ha
  | 0 => trivial
  | _ + 2 => trivial

theorem q1w_one (M : List PMsg) (tvs : List (Nat × BitVec 8)) (l : PLabel) :
    q1MW M [(l, none)] := by
  intro _ _ _ e he ts hts
  rw [List.mem_singleton] at he; subst he; cases hts

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- THE PROTOCOL'S PERSISTENT PART: the doom box, the flag slots (as MP), the dead messages. -/
def mwCtx (g : AGN) (M : List PMsg) (γc : GName) : IProp GF :=
  iprop(doomInv g M ∗ ([∗list] t ∈ (rng M).filter (isF M), slotInv g t (fR g M t) γc) ∗
    ([∗list] t ∈ (rng M).filter (isD2 M), deadInv g t))

instance (g : AGN) (M : List PMsg) (γc : GName) : Persistent (mwCtx (GF := GF) g M γc) := by
  unfold mwCtx; infer_instance

theorem x2_ne : x2Msg ≠ xMsg ∧ x2Msg ≠ fMsg := by decide

/-- THE SETUP: x-messages to x's points-to, flag messages to slots, H1's messages to H1, the rest dead. -/
theorem mw_setup (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ γc, mwCtx g M γc ∗ xPts g M 0 ∗ token γc ∗ [∗list] t ∈ (rng M).filter (isW M), pend g t := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  have h1 := bsl_filter_split (pend (GF := GF) g) (isX M) (rng M)
  rw [split_X] at h1
  have h2 := bsl_filter_split (pend (GF := GF) g) (isF M) ((rng M).filter (fun t => !isX M t))
  rw [split_F] at h2
  rw [filter_filter_of (r := fun t => !isX M t && !isF M t) (fun t => rfl)] at h2
  have h3 := bsl_filter_split (pend (GF := GF) g) (isW M) ((rng M).filter (fun t => !isX M t && !isF M t))
  rw [filter_filter_of (r := isW M) (fun t => by
      cases hW : isW M t
      · simp
      · have hm' : msgAt M t = some x2Msg := of_decide_eq_true hW
        have hX : isX M t = false := by simp [isX, hm', x2_ne.1]
        have hF : isF M t = false := by simp [isF, hm', x2_ne.2]
        rw [hX, hF]; rfl)] at h3
  rw [filter_filter_of (r := isD2 M) (fun t => rfl)] at h3
  ihave ⟨Hx, Hr⟩ := h1 $$ Hp
  ihave ⟨Hf, Hr⟩ := h2 $$ Hr
  ihave ⟨Hw, Hd⟩ := h3 $$ Hr
  imod token_alloc with ⟨%γc, Ht⟩
  imod bsl_fupd (G := fun t => slotInv g t (fR g M t) γc) (fun t => slot_alloc g t _ γc) _ $$ Hf with #Hs
  imod bsl_fupd (G := fun t => deadInv g t) (fun t => dead_alloc g t) _ $$ Hd with #Hdd
  imodintro
  iexists γc
  iframe Ht Hw
  isplitl []
  · unfold mwCtx
    iframe Hdoom Hs Hdd
  · unfold xPts
    iframe Hx
    ipureintro; intro h; omega

end res

/-! ## 2. The harts -/

section harts

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **H0, the writer** (as in MP): deposits x's points-to into the flag message's slot. -/
theorem mw_h0 (g : AGN) (M : List PMsg) (γc : GName) (s0 : LP) {P0 : GSet Nat}
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h5 : s0.rd 5 = 42) (h6 : s0.rd 6 = X) (h7 : s0.rd 7 = 1)
    (h8 : s0.rd 8 = Y) :
    mwCtx (GF := GF) g M γc ∗ xPts g M 0 ∗ lhA g Proto.triv (wMW M 0) (qsMW M 0) psInit P0 [] ⊢
      wpKA g Proto.triv (wMW M 0) (qsMW M) s0
        (fun _ => iprop(⌜∃ V, grd Proto.triv imgMW M V True⌝ ∨ dshot g)) := by
  have hw := litW_lit imgMW M 0
  have hag := litAg_lit (V := Unit) litDone imgMW M 0
  iintro ⟨#Hctx, Hx, Hl⟩
  -- `sd x5,(x6)`
  iapply (wpKA_sw (sz := 8) (rs2 := 5) (rs1 := 6) (off := 0) (base := (X : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of h6 (by decide) (by decide)) (base_of h6 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %_ %hext _ _
  rw [h5] at hmsg
  have hts1 : 1 ≤ ts := by omega
  have hmx : msgAt M ts = some xMsg := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt, xMsg] using hmsg
  have htsM : ts ≤ M.length := (msgAt_le hmx).2
  unfold xPts
  icases Hx with ⟨_, Hbag⟩
  icases xBag_take (pend g) M hmx (by omega : 0 < ts) $$ Hbag with ⟨Hp, Hbag⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro trivial⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  -- `fence rw,w`
  iapply (wpKA_fence (f := ⟨true, true, false, false, false, true, false, false⟩) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e7 : s2.rd 7 = 1 := by rw [LPstep_rd hs2 7 (.inr rfl), LPstep_rd hs1 7 (.inr rfl), h7]
  have e8 : s2.rd 8 = Y := by rw [LPstep_rd hs2 8 (.inr rfl), LPstep_rd hs1 8 (.inr rfl), h8]
  -- `sd x7,(x8)`: the release-class flag store deposits x's points-to
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 8) (off := 0) (base := (Y : Int)) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl) (alg_of e8 (by decide) (by decide)) (base_of e8 (by decide)))
  iframe Hl
  inext
  iintro %tf %_ %hmsgf %_ %hextf _ Hc
  rw [e7] at hmsgf
  have htf1 : 1 ≤ tf := by omega
  have hmf : msgAt M tf = some fMsg := by
    obtain ⟨k, rfl⟩ : ∃ k, tf = k + 1 := ⟨tf - 1, by omega⟩
    simpa [msgAt, fMsg] using hmsgf
  have htfM : tf ≤ M.length := (msgAt_le hmf).2
  -- EXT: the flag message is above the x message (`fence rw,w` raised `vwNew` to `vwOld ≥ ts`)
  have hlt : ts < tf := by
    have key : ∀ ws : PState, ts ≤ ws.wVwNew →
        stPreA ws false false (srcsView ws (srcR 8)) (srcsView ws (srcR 7)) < tf → ts < tf :=
      fun ws h1 h2 => by have := (PF.stPreA_ge ws false false (srcsView ws (srcR 8)) (srcsView ws (srcR 7))).2.2.2.1; omega
    refine key _ ?_ hextf
    have hvo := (storeRun_mono psInit false (srcsView psInit (srcR 6))
      (max (srcsView psInit (srcR 6)) (srcsView psInit (srcR 5))) (X : Int) (toBytes (s0.rd 5) 8).length ts).2.2.1
    dsimp only
    simp only [instrR_vwNew, fence_vwNew, instrR_vwOld, instrR_vrOld, acqPost_false, hvo, ite_true]
    omega
  ihave #Hslot : slotInv g tf (fR g M tf) γc $$ []
  · unfold mwCtx
    icases Hctx with ⟨_, Hs, _⟩
    iapply bsl_mem (F := fun t => slotInv g t (fR g M t) γc)
      (List.mem_filter.2 ⟨mem_rng.2 ⟨htf1, htfM⟩, by simp [isF, hmf]⟩) $$ Hs
  imod slot_deposit g tf (fR g M tf) γc $$ [Hslot Hbag Hc] with #Hshf
  · iframe Hslot Hc
    unfold fR xPts
    iexists ts
    iframe Hbag
    ipureintro; exact ⟨⟨hts1, hlt⟩, fun _ => hmx⟩
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro trivial⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hshf
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hend : s3.prog.length ≤ s3.pc := by rw [hP3, hc3]; simp
  iapply (wpKA_end (v := ()) (hag s3) hq3 hend
    (by show litDone s3 = some (); unfold litDone; rw [if_pos ⟨hq3, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩


/-- **H1's tail** (`sd 2,(x)`, then the end): its own message's `pend`; the order from the claimed points-to. -/
theorem mw_h1_tail (g : AGN) (M : List PMsg) (γc : GName) (s2 : LP) (ws : PState) {pr : GSet Nat}
    (tvs0 : List (Nat × BitVec 8)) (hprog : s2.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW,
      Weak.Prom.Ref.Lit.sd 7 8]) (hpc : s2.pc = 2) (hq : s2.q = []) (h7 : s2.rd 7 = 2) (h8 : s2.rd 8 = X) :
    mwCtx (GF := GF) g M γc ∗
      (⌜obsOf tvs0 ≠ 1⌝ ∨ dshot g ∨ ∃ lw, ⌜1 ≤ lw ∧ lw ≤ ws.wVwNew⌝ ∗ xPts g M lw) ∗
      ([∗list] t ∈ (rng M).filter (isW M), pend g t) ∗
      lhA g Proto.triv (wMW M 1) (qsMW M 1) ws pr [(LLoad false false (Y : Int) tvs0 (srcR 6), none)] ⊢
      wpKA g Proto.triv (wMW M 1) (qsMW M) s2 (fun _ => iprop(⌜∃ V, grd Proto.triv imgMW M V True⌝ ∨ dshot g)) := by
  have hw := litW_lit imgMW M 1
  have hag := litAg_lit (V := Unit) litDone imgMW M 1
  iintro ⟨#Hctx, HG, HW, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 8) (off := 0) (base := (X : Int)) hw (hag s2) hq
    (by rw [hprog, hpc]; rfl) (alg_of h8 (by decide) (by decide)) (base_of h8 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %_ %hext _ _
  rw [h7] at hmsg
  have hts1 : 1 ≤ ts := by omega
  have hmw : msgAt M ts = some x2Msg := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt, x2Msg] using hmsg
  icases bsl_filter_take (pend g) (isW M) (fun _ => false) ts (by simp [isW, hmw]) (fun _ h => by cases h)
    (rng M) (mem_rng.2 (msgAt_le hmw)) (nodup_rng M) $$ HW with ⟨Hp, -⟩
  imod shoot $$ Hp with #Hsh
  -- THE WRITE FLOOR: `ts > pv ≥ vwNew`
  have hpv : ws.wVwNew < ts := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 8)) (srcsView ws (srcR 7))).2.2.2.1; omega
  ihave HQ : |={⊤}=> (⌜q1MW M ([(LLoad false false (Y : Int) tvs0 (srcR 6), none)] ++
      [(LStore false false (X : Int) (toBytes (s2.rd 7) 8) (srcR 8) (srcR 7), some ts)])⌝ ∨ dshot g) $$ [HG]
  · icases HG with (%hne | #Hd | ⟨%lw, %hlw, Hx⟩)
    · imodintro; ileft; ipureintro
      intro a ha h1
      simp [loadsOf, loadLikeTvs] at ha
      rw [← ha] at h1; exact absurd h1 hne
    · imodintro; iright; iexact Hd
    · by_cases hg : ∃ t, msgAt M t = some xMsg ∧ lw < t
      · obtain ⟨t, ht, hlt⟩ := hg
        unfold xPts
        icases Hx with ⟨_, Hbag⟩
        icases xBag_take (pend g) M ht hlt $$ Hbag with ⟨Hp, -⟩
        unfold mwCtx
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M t (msgAt_le ht) $$ [Hdoom Hp] with #Hd
        · iframe Hdoom Hp
        imodintro; iright; iexact Hd
      · imodintro; ileft; ipureintro
        intro _ _ _ e he ts' hts' t ht
        rcases List.mem_append.1 he with he | he
        · rw [List.mem_singleton] at he; subst he; cases hts'
        · rw [List.mem_singleton] at he; subst he
          simp only [Option.some.injEq] at hts'; subst hts'
          have : ¬ lw < t := fun h => hg ⟨t, ht, h⟩
          omega
  imod HQ with #HQ
  imodintro
  isplitr
  · icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨⟨0, grd_intro hQ⟩, grd_intro trivial⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
  have hend : s3.prog.length ≤ s3.pc := by rw [hP3, hc3]; simp
  iapply (wpKA_end (v := ()) (hag s3) hq3 hend
    (by show litDone s3 = some (); unfold litDone; rw [if_pos ⟨hq3, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- **H1, the reader**: claims x's points-to from the flag message's slot, then reads x. -/
theorem mw_h1 (g : AGN) (M : List PMsg) (γc : GName) (s0 : LP) {P0 : GSet Nat}
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.sd 7 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h6 : s0.rd 6 = Y) (h7 : s0.rd 7 = 2) (h8 : s0.rd 8 = X)
    (hdd : ∀ t, isD2 M t = true → g.dd t)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    mwCtx (GF := GF) g M γc ∗ token γc ∗ ([∗list] t ∈ (rng M).filter (isW M), pend g t) ∗
      lhA g Proto.triv (wMW M 1) (qsMW M 1) psInit P0 [] ⊢
      wpKA g Proto.triv (wMW M 1) (qsMW M) s0 (fun _ => iprop(⌜∃ V, grd Proto.triv imgMW M V True⌝ ∨ dshot g)) := by
  have hw := litW_lit imgMW M 1
  have hag := litAg_lit (V := Unit) litDone imgMW M 1
  iintro ⟨#Hctx, Htok, HW, Hl⟩
  -- `ld x5,(x6)` (the flag)
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 5) (rs1 := 6) (off := 0) (base := (Y : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of h6 (by decide) (by decide)) (base_of h6 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %hlo0 _ _
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨0, grd_intro (q1w_one M tvs0 _)⟩
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  -- `fence r,rw`: at the next step, the frontier covers the flag message read
  iapply (wpKA_fence (f := ⟨true, false, false, false, true, true, false, false⟩) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 #Hfr Hc
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e8 : s2.rd 8 = X := by rw [LPstep_rd hs2 8 (.inr rfl), LPstep_rd hs1 8 (.inl (by decide)), h8]
  have e7 : s2.rd 7 = 2 := by rw [LPstep_rd hs2 7 (.inr rfl), LPstep_rd hs1 7 (.inl (by decide)), h7]
  ihave HG : |={⊤}=> (⌜obsOf tvs0 ≠ 1⌝ ∨ dshot g ∨ ∃ lw, ⌜1 ≤ lw ∧ lw ≤ (instrR (fencePost
      (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int) tvs0) (regWL 5 [.DLdRes] ++ [LInstr]))
      true false true true)).wVwNew⌝ ∗ xPts g M lw) $$ [Htok Hc]
  · by_cases hv : obsOf tvs0 = 1
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 (by decide)
      have hv0 := obs_one hv
      have hb := (loadOk_b0 hlo0).1
      obtain ⟨k, m, ht0, hmk, hby⟩ := src_of_val hb imgMW_Y (by rw [hv0]; decide)
      have hmt : msgAt M t0 = some m := by rw [ht0]; exact hmk
      -- `vrOld ≥ t0` after the load (X4); `fence r,rw` raises both floors to it
      have hro : t0 ≤ (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int) ((t0, v0) :: r0))
          (regWL 5 [.DLdRes] ++ [LInstr])).wVrOld := by
        have := (loadRun_b0 psInit false false (srcsView psInit (srcR 6)) (Y : Int) t0 v0 r0).2.1
        rw [fwdView_empty rfl] at this
        simp only [regWL, qPosts, qPost, regWP_vrOld, instrR_vrOld, show (5 : Nat) ≠ 0 by decide, if_false,
          List.singleton_append]
        omega
      have hfl : t0 ≤ wfr (fencePost (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int)
          ((t0, v0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true) := by
        refine Nat.le_trans ?_ (wfr_ge_vwNew _)
        simp only [fence_vwNew, ite_true]
        omega
      have hvr : t0 ≤ (instrR (fencePost (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int)
          ((t0, v0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true)).wVwNew := by
        simp only [instrR_vwNew, fence_vwNew, ite_true]
        omega
      ihave #Hfs := frontA_get t0 $$ Hfr %⟨(msgAt_le hmt).1, (msgAt_le hmt).2, hfl⟩
      unfold mwCtx
      icases Hctx with ⟨Hdoom, Hs, Hdd⟩
      unfold fulT
      icases Hfs with (#Hsh | ⟨#Hfr, _⟩)
      rotate_left
      · imod dfree_dshot (E := ⊤) CoPset.subseteq_top g M $$ [] with #Hd
        · iframe Hdoom Hfr
        imodintro
        iright; ileft; iexact Hd
      by_cases hf : m = fMsg
      · -- a flag message: claim the slot
        subst hf
        ihave #Hslot := bsl_mem (F := fun t => slotInv g t (fR g M t) γc)
          (List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hmt), by simp [isF, hmt]⟩) $$ Hs
        imod slot_claim g t0 (fR g M t0) γc $$ [Hslot Hsh Htok Hc] with HR
        · iframe Hslot Hsh Htok Hc
        unfold fR
        icases HR with ⟨%lw, %hlw, Hx⟩
        imodintro
        iright; iright
        iexists lw
        iframe Hx
        ipureintro; exact ⟨hlw.1, by omega⟩
      · -- any other message holding 1 at the flag is dead: doom
        have hmX : m ≠ xMsg := by intro e; subst e; rw [xMsg_byte_Y] at hby; cases hby
        have hmW : m ≠ x2Msg := by intro e; subst e; rw [x2Msg_byte_Y] at hby; cases hby
        have hD : isD2 M t0 = true := by simp [isD2, isX, isF, isW, hmt, hmX, hf, hmW]
        ihave #Hds := bsl_mem (F := fun t => deadInv g t)
          (List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hmt), hD⟩) $$ Hdd
        imod dead_shot g M t0 $$ [Hds Hsh] with ⟨_, #Hd⟩
        · iframe Hdoom Hds; unfold fulT; ileft; iexact Hsh
        imodintro
        iright; ileft; iexact Hd
    · imodintro; ileft; ipureintro; exact hv
  imod HG with HG
  imodintro
  dsimp only [List.nil_append]
  iintro Hl
  iapply (mw_h1_tail g M γc s2 _ tvs0 hP2 hc2 hq2 e7 e8)
  iframe Hctx HG HW
  iexact Hl

end harts

/-! ## 3. The verdict -/

theorem progs_mpW : ∃ p0 p1 : LP, progs mpW = [p0, p1] := ⟨_, _, rfl⟩

/-- THE ADEQUACY PREMISE for (2′). -/
theorem mw_premise (M : List PMsg)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    wpPremise .hasLC ownGF litStep litDone imgMW M (progs mpW) Proto.triv (fun _ _ => True)
      (fun h => ΨK M (qsMW M h)) (fun t => isD2 M t = true) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_mpW
  have hg0 : (progs mpW)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs mpW)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, _, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, _, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod mw_setup g M hm $$ [Hp] with ⟨%γc, #Hctx, Hx, Htok, HW⟩
  · iframe Hdoom Hp
  have k0 := mw_h0 (GF := ownGF) g M γc p0 (P0 := P0 0) hpr0 hpc0 hq0
    (by rw [hrd0 5 (by decide) (by decide)]; rfl) (by rw [hrd0 6 (by decide) (by decide)]; rfl)
    (by rw [hrd0 7 (by decide) (by decide)]; rfl) (by rw [hrd0 8 (by decide) (by decide)]; rfl)
  have k1 := mw_h1 (GF := ownGF) g M γc p1 (P0 := P0 1) hpr1 hpc1 hq1
    (by rw [hrd1 6 (by decide) (by decide)]; rfl) (by rw [hrd1 7 (by decide) (by decide)]; rfl)
    (by rw [hrd1 8 (by decide) (by decide)]; rfl) (fun t ht => by rw [hdd]; exact ht)
  have k0' : mwCtx (GF := ownGF) g M γc ∗ xPts g M 0 ∗
      lhA g Proto.triv (wMW M 0) (qsMW M 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw litStep litDone imgMW M 0) (fun h => ΨK M (qsMW M h)) p0
        (fun v => iprop(⌜∃ V, grd Proto.triv imgMW M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : mwCtx (GF := ownGF) g M γc ∗ token γc ∗ ([∗list] t ∈ (rng M).filter (isW M), pend g t) ∗
      lhA g Proto.triv (wMW M 1) (qsMW M 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw litStep litDone imgMW M (0 + 1)) (fun h => ΨK M (qsMW M h)) p1
        (fun v => iprop(⌜∃ V, grd Proto.triv imgMW M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  have s0 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wMW M 0) (Qs := qsMW M) (P0 := P0 0)
    (qsMW_nil M 0)
  have s1 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wMW M 1) (Qs := qsMW M) (P0 := P0 (0 + 1))
    (qsMW_nil M 1)
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  iapply (BigSepL.bigSepL_cons).2
  isplitl [Hx H0]
  · iapply k0'
    iframe Hctx Hx
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [Htok HW H1]
  · iapply k1'
    iframe Hctx Htok HW
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **G4 TARGET (2′) ON TRACK (a): MP-OWNERSHIP, THE RECEIVER WRITES x** (plan §4 G4 (2′)).  Over every final memory
and every valid run of machine v2 of `mpW` (`sd x; fence rw,w; sd flag` ‖ `ld flag; fence r,rw; sd 2,(x)`): if H1's
flag load returned 1, every write H1 fulfils lies above (in coherence = timestamp order) every message holding H0's
x-write.  Proved in the logic by the hand-off of x's points-to (MP's protocol) and the write floor; 0 named inputs. -/
theorem own_mp2 (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun litStep imgMW () (progs mpW) M run) :
    run.obsLoad 1 0 = some 1 → ∀ e ∈ run.trace 1, ∀ ts, e.2 = some ts →
      ∀ t, msgAt M t = some xMsg → t < ts := by
  have hnoinv := Own.lit_noInvalT hrun   -- MachFix-R-b5: litmus programs issue no CMO (`vi = 0`)
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) Proto.triv (fun _ _ => True)
    (fun h => ΨK M (qsMW M h)) (fun t => isD2 M t = true) trivial (fun h => ⟨qsMW_nil M h, wrOk_nil M⟩)
    (mw_premise M) hrun
  intro h0 e he ts hts
  have hq := (hΨ 1 (run.trace 1).length).1
  rw [List.take_length] at hq
  unfold PFRun.obsLoad at h0
  rw [← loadsOf_memEv] at h0
  obtain ⟨a, ha, ha1⟩ := Option.map_eq_some_iff.1 h0
  exact hq a ha ha1 e (List.mem_filter.2 ⟨he, by simp [keepE, hts]⟩) ts hts

#print axioms own_mp2

end Weak.Prom.OA
