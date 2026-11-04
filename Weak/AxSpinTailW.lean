/-
Weak: **THEOREM 2 / P4, step 2: THE WALK PAST THE ROW END** — from the instruction boundary
right after the terminal store `c.sw a5,24(s1)` (`allocproc + 0x9c`, row position `k = LEN`) a
hart runs `jal ra,kalloc` and kalloc's `c.addi sp,sp,-32` (register-only, `AxSpinRowEnd.XxRegEnd`)
and then stops at kalloc's `c.sdsp ra,24(sp)` (a store with no row item: stuck,
`AxSpinRowEnd.XxStEnd`).  None of the three writes `a3` (x13), so at EVERY state of the walk at
which the WPd owes its post (the three boundaries; mid-instruction states are the caller's
`HΨmid`) `a3` still holds the value `v` it had at `+0x9c` (`notes/weak-lb-thm2-p4.md` §A.5–A.6,
§B, §C F5; Q-P4-3: the walk stops at `kalloc + 2`).

Lean-only (no Rocq source).

## What this file proves

§1 THE `jal` AT `allocproc + 0x9c` (0xf71fe0ef, 4 bytes at a 2-mod-4 address, `textAt4S`):
   `AxSpinTailW.ap9c` (`.JAL (2092912#21, ra)`: offset −0x1090, target `kalloc` = 0x80000b7e),
   the decode walks `walk9cM`/`walk9cS` (kernel `kernel_rfl` on the word, which also confirms the
   AST), `dec9c`, `rfFDec9c`, the token `atok9c` (`tokB`), `rfFAp9c`.  kalloc's two halfwords
   reuse AxSpinPOt1's `tw1101` / `twEc06` (push_off's prologue is the same two words).
§2 `AxSpinTailW.gprOfRetX` — every state of an instruction boundary `RetX cpu rs k` has
   `gprOf · r = some (gprVal rs r)` (GPRs are not pinned registers).
   `AxSpinTailW.postAnnBig` / `postAnn2` — owned annotations of hart `i` give `postLifting Φ i s`
   for a post that follows from their contents (the row-end branch of `AxSpinApA.wpdEndAnn`
   factored out; `postAnn2` is the two-annotation instance as `AxSpinApA.wpdEnd2`).
§3 **`AxSpinTailW.walk`** — at Ixv6, for ANY post `Ψ` whose mid-states are free (`HΨmid`) and
   ANY resource `R` that proves the post at every boundary state whose `a3` is `v`
   (`HRb : ∀ s1, gprOf s1 13 = some v → R ⊢ postLifting Ψ i s1`):
   `R -∗ WPd ⟨PHart cpu (pure ()) rs none ib, LEN⟩ Ψ`, given `rs` at `+0x9c` with `a3 = v`,
   `sp = S`, the TLB hits for the three pcs and the slot `S − 8`, and that slot's store
   translation (`dataAtS`).

## Pins / honesty

* No pins.  Text: `AxSpinApA.tailText2` (the three words; certified on the capstone image by
  `AxSpinTail2X.tailText2X`).  The slot `S − 8` = kalloc's `ra` spill (`sp − 32 + 24`); its store
  translation and TLB hit are premises the caller discharges from `MapOk` / `Warm` (the slot is
  in `Rng` / `t2Touch`'s stack window `[S − 80, S)`).
* The walk proves nothing past `kalloc + 2`: the store there has no row item, so every run of
  the hart stops at that store's write node (`AxCert2.wpdStuckWriteM` via `XxStEnd`).

Reused: `AxSpinRowEnd.XxRegEnd` / `XxStEnd`, `retxShape` (AxEpiChainSdLd),
`AxSymEngine2.uxaXgetAgree`, `annotAgreeBig` (AxWp), `AxSpinProt7.readbackBig`, `tokB`
(AxSpinE7), `tw1101`/`twEc06` (AxSpinPOt1), `certJAL` (AxSymCtl2), `certAddi` (AxSpinE7),
`AxSpinAp6.rfFJal`, `rf0Addi`, `stepRegs`/`gbPc`/`gbTlb`/`gbCtrl` (AxSpinE8), `hitWAgree`,
`WkEntryNew.execAnyCfg`, `vw8` (AxSpinE6).
Names: all Lean-only and file-qualified `AxSpinTailW.*` (grepped absent).
-/
import Weak.AxSpinRowEnd
import Weak.AxSpinTail2
import Weak.AxSpinApA

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The `jal kalloc` at `allocproc + 0x9c` -/

/-- `allocproc + 0x9c`: `jal ra, kalloc` (offset −0x1090). -/
def AxSpinTailW.ap9c : instruction := .JAL (2092912#21, .Regidx 1#5)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `wJal`. -/
theorem AxSpinTailW.rfFDec9c : rfF (ext_decode AxSpinTail2.wJal) := by
  unfold AxSpinTail2.wJal ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

/-- Decode walk of `wJal`, machine reference map (confirms the AST). -/
theorem AxSpinTailW.walk9cM :
    runRead drefM (ext_decode AxSpinTail2.wJal) = some (AxSpinTailW.ap9c, false) := by kernel_rfl

/-- Decode walk of `wJal`, supervisor reference map. -/
theorem AxSpinTailW.walk9cS :
    runRead WkEntryNew.drefS0 (ext_decode AxSpinTail2.wJal) = some (AxSpinTailW.ap9c, false) := by
  kernel_rfl

/-- The decode of `wJal`. -/
theorem AxSpinTailW.dec9c (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode AxSpinTail2.wJal) s = some (AxSpinTailW.ap9c, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinTailW.walk9cM AxSpinTailW.walk9cS s

theorem AxSpinTailW.atok9c (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (H : AxSpinApA.tailText2 σi T) : textOkB σi T satp0 (pca 0x9c) false AxSpinTailW.ap9c :=
  tokB σi T satp0 _ _ _ H.1 (by decide) AxSpinTailW.rfFDec9c AxSpinTailW.dec9c

theorem AxSpinTailW.rfFAp9c : rfF (execute AxSpinTailW.ap9c) := AxSpinAp6.rfFJal _ _

/-! # 2. Boundary registers; posts from owned annotations -/

theorem AxSpinTailW.gprOfRetX (cpu : CPU) (rs : RegFile) (k : Nat) (s : Athread) (r : BitVec 5)
    (h : RetX cpu rs k s) : AxSpinT2a.gprOf s r = some (gprVal rs r) := by
  obtain ⟨rs1, ib1, rfl, Hag⟩ := retxShape cpu rs k s h
  show some (gprVal rs1 r) = some (gprVal rs r)
  unfold gprVal
  rw [AxSymEngine2.uxaXgetAgree _ _ Hag r]

section posts
open Iris.Std.PartialMap
variable {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxSpinX.Xv6G GF]

/-- Owned annotations of hart `i` give the post under `postLifting` (the row-end branch of
`AxSpinApA.wpdEndAnn`). -/
theorem AxSpinTailW.postAnnBig (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (m : Mea GF)
    (Hm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i) (Φ : Athread → IProp GF)
    (s : Athread) (HRQ : ([∗map] R ∈ m, R) ⊢ Φ s) :
    ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Φ i s := by
  unfold postLifting
  iintro Hp %na Hna
  ihave ⟨%Hdomi, #Hw⟩ := annotAgreeBig na m $$ Hna Hp
  imodintro
  isplitl [Hna]
  · iexact Hna
  iintro Hbig
  ihave HR := AxSpinProt7.readbackBig na m i Hdomi Hm $$ Hbig Hw
  inext
  imodintro
  iapply HRQ $$ HR

/-- `postAnnBig` for two annotations at distinct events of hart `i` (as `AxSpinApA.wpdEnd2`). -/
theorem AxSpinTailW.postAnn2 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (e1 e2 : Geid)
    (h1 : e1.1 = i) (h2 : e2.1 = i) (hne : e1 ≠ e2) (P1 P2 : IProp GF) (Φ : Athread → IProp GF)
    (s : Athread) (HRQ : iprop(P2 ∗ P1) ⊢ Φ s) :
    AxAnnot.annotOwn e1 P1 ∗ AxAnnot.annotOwn e2 P2 ⊢
      @postLifting GF (AxSpinX2.xG L GT nm) Φ i s := by
  have hn1 : get? (∅ : Mea GF) e1 = none := lookupEmpty
  have hn2 : get? (insert (∅ : Mea GF) e1 P1) e2 = none := by
    rw [lookupInsertNe hne]; exact lookupEmpty
  have Hm : ∀ e, e ∈ (FiniteMap.dom_set (insert (insert (∅ : Mea GF) e1 P1) e2 P2) : GSet Geid) →
      e.1 = i := by
    intro e he
    rw [domInsert, domInsert, domEmpty] at he
    rcases elemOfUnion.1 he with h | h
    · rw [elemOfSingleton.1 h]; exact h2
    · rcases elemOfUnion.1 h with h | h
      · rw [elemOfSingleton.1 h]; exact h1
      · exact absurd h (fun h' => (elemOfEmpty (S := GSet Geid)).1 h')
  have HR : ([∗map] R ∈ insert (insert (∅ : Mea GF) e1 P1) e2 P2, R) ⊢ Φ s := by
    iintro Hb
    icases (BigSepM.bigSepM_insert hn2).1 $$ Hb with ⟨H2, Hb⟩
    icases (BigSepM.bigSepM_insert hn1).1 $$ Hb with ⟨H1, -⟩
    iapply HRQ
    isplitl [H2]
    · iexact H2
    · iexact H1
  iintro ⟨A1, A2⟩
  iapply (AxSpinTailW.postAnnBig L GT nm i _ Hm Φ s HR)
  iapply (BigSepM.bigSepM_insert hn2).2
  isplitl [A2]
  · iexact A2
  iapply (BigSepM.bigSepM_insert hn1).2
  isplitl [A1]
  · iexact A1
  iapply BigSepM.bigSepM_empty.2
  iempintro

end posts

/-! # 3. THE WALK: `+0x9c` → `kalloc + 0` → `kalloc + 2` (stuck) -/

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_tailw_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

section walk
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

theorem AxSpinTailW.vaS8 (S : Int) :
    BitVec.ofInt 64 S + sign_extend (m := 64) (sign_extend (m := 12) (32#6)) +
      sign_extend (m := 64) AxSpinPO3.imm24 = BitVec.ofInt 64 (S - 8) := by
  have h1 : sign_extend (m := 64) (sign_extend (m := 12) (32#6)) = BitVec.ofInt 64 (-32) := by
    decide
  have h2 : sign_extend (m := 64) AxSpinPO3.imm24 = BitVec.ofInt 64 24 := by decide
  rw [h1, h2, ← BitVec.ofInt_add, ← BitVec.ofInt_add]
  congr 1
  omega

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- **THE WALK PAST THE ROW END.**  From the boundary at `allocproc + 0x9c` at row position
`k = LEN` with `a3 = v`: `jal kalloc`, `c.addi sp,sp,-32` (register-only, at the row end) and the
stuck `c.sdsp ra,24(sp)`.  Every boundary's post comes from `R` at `a3 = v` (`HRb`). -/
theorem AxSpinTailW.walk (S : Int) (R : IProp GF) (v : BitVec 64) (rs : RegFile) (ib : Ibch)
    (k : Nat) (Htx : AxSpinApA.tailText2 σi T)
    (Hc : ctrlOkSW T satp0 rs) (HPC : rs .PC = pca 0x9c) (H13 : gprVal rs 13#5 = v)
    (Hsp : gprVal rs 2#5 = BitVec.ofInt 64 S)
    (Hh9c : hitW rs (pca 0x9c)) (Hh0 : hitW rs (AxSpinTail2.pka 0))
    (Hh2 : hitW rs (AxSpinTail2.pka 2)) (Hhs : hitW rs (BitVec.ofInt 64 (S - 8)))
    (Hda : dataAtS σi T (.Store .Data) (BitVec.ofInt 64 (S - 8)) 8 (BitVec.ofInt 64 (S - 8)))
    (Hk : k = (AxOpsem.grow (gtAdGd GT) i).length)
    (HRb : ∀ s1, AxSpinT2a.gprOf s1 13#5 = some v →
      R ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s1) :
    ⊢ R -∗ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs none ib, k⟩ Ψ := by
  have XR := AxSpinRowEnd.XxRegEnd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := AxSpinRowEnd.XxStEnd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  -- ---- allocproc + 0x9c: jal ra,kalloc ----
  have Hcj : CertC (ctrlOkSW T satp0) rs (pca 0x9c) false AxSpinTailW.ap9c
      (some (AxSpinTail2.pka 0)) (some (1#5, BitVec.addInt (pca 0x9c) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs (pca 0x9c)
      false 2092912#21 1#5 (by decide)
    rw [show pca 0x9c + sign_extend (m := 64) 2092912#21 = AxSpinTail2.pka 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (pca 0x9c) (incr false)) =
      some (1#5, BitVec.addInt (pca 0x9c) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iintro HR
  iapply (XR _ rs k (pca 0x9c) false AxSpinTailW.ap9c (some (AxSpinTail2.pka 0))
    (some (1#5, BitVec.addInt (pca 0x9c) (incr false))) R
    (retxRefl cpu rs k ib) Hc HPC Hh9c (AxSpinTailW.atok9c σi T satp0 Htx)
    (AxSpinE8.owOkSome 1#5 _ (by decide)) AxSpinTailW.rfFAp9c Hcj Hk
    (fun s1 H1 => HRb s1 (by rw [AxSpinTailW.gprOfRetX cpu rs k s1 13#5 H1, H13]))) $$ HR
  iintro HR %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = AxSpinTail2.pka 0 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; rfl
  have Htl1 : rs1 .tlb = rs .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  have E131 : gprVal rs1 13#5 = v := by rw [HF1]; ax_spin_tailw_zsimp; exact H13
  have Esp1 : gprVal rs1 2#5 = BitVec.ofInt 64 S := by rw [HF1]; ax_spin_tailw_zsimp; exact Hsp
  -- ---- kalloc + 0: c.addi sp,sp,-32 ----
  iapply (XR _ rs1 k (AxSpinTail2.pka 0) true q00 none
    (some (2#5, gprVal rs1 2#5 + sign_extend (m := 64) (sign_extend (m := 12) (32#6)))) R
    (retxRefl cpu rs1 k ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWAgree rs rs1 _ Htl1 Hh0) (tw1101 σi T satp0 _ Htx.2.1)
    (AxSpinE8.owOkSome 2#5 _ (by decide)) (rfFOfRf0 _ (rf0Addi _ _ _))
    (certAddi _ rs1 (AxSpinTail2.pka 0) true 2#5 2#5 _ (by decide)) Hk
    (fun s1 H1 => HRb s1 (by rw [AxSpinTailW.gprOfRetX cpu rs1 k s1 13#5 H1, E131]))) $$ HR
  iintro HR %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 (fun _ => rfl) HG2
  have HPC2 : rs2 .PC = AxSpinTail2.pka 2 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  have E132 : gprVal rs2 13#5 = v := by rw [HF2]; ax_spin_tailw_zsimp; exact E131
  have Esp2 : gprVal rs2 2#5 =
      BitVec.ofInt 64 S + sign_extend (m := 64) (sign_extend (m := 12) (32#6)) := by
    rw [HF2]; ax_spin_tailw_zsimp; rw [Esp1]
  -- ---- kalloc + 2: c.sdsp ra,24(sp) — a store at the row end: STUCK ----
  iapply (XS _ rs2 k (AxSpinTail2.pka 2) true AxSpinPO3.imm24 1#5 2#5 8
    (BitVec.ofInt 64 (S - 8)) (BitVec.ofInt 64 (S - 8)) R
    (retxRefl cpu rs2 k ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWAgree rs rs2 _ Htl2 Hh2) (twEc06 σi T satp0 _ Htx.2.2) vw8 (by decide) (by decide)
    (by rw [Esp2, AxSpinTailW.vaS8]) Hda (hitWAgree rs rs2 _ Htl2 Hhs) Hk
    (fun s1 H1 => HRb s1 (by rw [AxSpinTailW.gprOfRetX cpu rs2 k s1 13#5 H1, E132]))) $$ HR

end walk

end Weak
