/-
Weak: **xv6's `release` replayed at SURFACE v3 (`AxCondM3`) with the THREE LOCK-WORD
INSTRUCTIONS AS REAL WPd LEAVES** (AxSL tier):

  release+0x12  sd zero,16(s1)   (lk->cpu = 0)       `wSdlk3`
  release+0x16  fence rw,w                          `wFence3`
  release+0x1a  sw zero,0(s1)    (lk->locked = 0)    `wSwfin3`

Rocq: `iris/AxCondM4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`releaseWpd3` is `AxLeafS5.wpReleaseGen` (the replayed release proof text over the abstract
interface) instantiated with `Goal` := `goal3` (ambient hart), the register/stack context :=
`sieCap3` (+ the kernel text), `pcIs` := `pcIs3 armedR`, `instr` := `instr3 armedR` and these
three slots.  `armedR pc := pc = release+0x1a`: the release flag is threaded through the PC ghost,
and the `sw`'s certificate is started ARMED — its class is `wcls akPlain true = WCrel` — because
the `fence rw,w` leaf left the ghost armed at `pc+4 = release+0x1a` (`pcIs3`'s invariant).  The
protocol's RELEASE rule `swlkRule` is therefore only ever applied at class `WCrel` (it takes
`c = WCrel` as a premise): the store that hands the lock over is the release store, at the WPd
level.  THE PROTOCOL RULES (section premises — the WPd lock protocol, D2): `sdlkRule` (the
owner's plain store to `lk->cpu`: locked ⇒ locked-pre) and `swlkRule` (the RELEASE store to
`lk->locked` at class `WCrel`), both with a mono-closed output (`Pd` ⊆ the stored bytes).  STILL
λ-BOUND (premised) in `releaseWpd3`: the frame / register leaves, the control leaves, the callees
(holding, pop_off), `kctx_wf`, `locked_cases`, the text lemma and the resources.  Instance-level
premises: the bridge's (`Htext` `Hflow` `Hloc` `HG`), the data regions (`Hdmap`), `CondGate3` —
DISCHARGED at `Cond := AxCondM.condP` (`releaseWpd3P`).

## Deviations from Rocq

1. THE INTERFACE IS AxLeafS5's LEAN ONE (AxLeafS5 deviation 1: the replayed text is the Lean
   tree's `Xv6.release_gen_proof`, over `kctx` / `KCtx`, `lockOpenable γ lk s R D` with a payload
   type `Pay`, the credential `Tc` refuting the dead branch `D`, `lockedCore` / `lockedPre` /
   `lockCtxHeld`, `payAt` / `payOk`).  So the three fillers are stated in THAT slot shape
   (later-free, AxLeafS5 deviation 3), not in Rocq's:
   - Rocq `capW3 CID0 m n b p` ↦ `kctxW3 γm γn held kt c k := sieCap3 γm γn c k.regs k.avail
     k.sie k.proc ∗ held c k.locks ∗ kt` (as AxLeafS5's `kctxW`, plus `held`, below);
   - `sd`: the slot hands `lockOpenable` ∗ `Tc` ∗ `lockedCore` (Rocq: `lock_openable` ∗
     `locked`) and wants `lockedPre ∗ Tc` back; `sdlkRule` is Rocq's `sdlk_rule` with `locked`
     ↦ `lockedCore` (the held token's core, after the text's `locked_cases`), `lock_openable γl
     lk R Dc` ↦ `lockOpenable γl lk s R Dc`, `lock_cpu lk` ↦ `lk + 16#64` (=
     `AxRelease3.lockCpu lk` by `rfl`); `Tc` is framed around the store (not handed to the rule);
   - `sw`: Lean's word clear has no `lock_finisher` / `Out` (AxLeafS5 deviation 1): the slot hands
     `lockOpenable` ∗ `Tc` ∗ `lockedPre` ∗ `lockCtxHeld` ∗ `payAt R` and wants the context with
     `s` removed from `k.locks`, `⌜s ∈ k.locks⌝` and `Tc` back.  The surface forgets `k.locks`,
     so the held-lock set is carried by a new abstract resource `held c ks` in `kctxW3` (the Lean
     SC leaf's `lockSet cpu k.locks`), and `swlkRule` is Rocq's `swlk_rule` with `R` ↦ `payAt R`
     (+ `payOk R`), `lock_finisher γl lk R Dc Out E` ↦ `lockCtxHeld ∗ held c ks`, and `Out` ↦
     `held c (ks.filter (· ≠ s)) ∗ ⌜s ∈ ks⌝` (exactly the Lean SC leaf's lockSet pre/post).
     CONSEQUENCE: AxRelease3's Rocq-shaped `rlSwlkRule` (finisher := Out) does not instantiate
     `swlkRule` as is; `rlSdlkRule` instantiates `sdlkRule` (`lockedCore` := `rlLocked`, `Pay` :=
     `IProp GF`, `lockOpenable γ lk _ R D` := `rlLockOpenable γb γ lk R D`).
2. THE SLOTS ARE GENERIC IN `is_rvc` (the Lean SC leaves are; Rocq's slots are at `false`), and
   `instr3`'s compressed arm carries no decode fact, so `instrW3` adds one pure conjunct to
   Rocq's `instr3 armedR`: a `x0`-store or `fence rw,w` is a 4-byte instruction
   (`AxCondM4.zeroStOrFence ins → is_rvc = false`).  It only strengthens the λ-bound text lemma
   (`textInstr`), where it holds at the real text (the three words are 4-byte).
3. TYPES / SPELLING as AxCondM3 deviation 2: Rocq's `CpuId` contexts ↦ the explicit SC hart `cid`
   (the resuming hart `c` of the slots), `GenId` dropped, `rget m r` ↦ `rget cid m r`; the base
   register ≠ `tp` (from `instr3`'s `baseOk3`) moves `rget` between harts
   (`AxCondM4.rgetCpu`); `release + 0x1a` ↦ `Xv6.releaseAddr + 0x1a#64`; `⊤ ∖ ↑minstretN` has no
   counterpart (Q3: no MinstretInv).  The iProp-valued Rocq premises are `⊢` entailments.
4. The kernel-text projection slot (`kctx_kernelText`, Lean-only in AxLeafS5) is filled REAL
   (`AxCondM4.kctxW3Kt`), as AxLeafS5's `kctxWKt`.  `Hlo` (persistence of `lockOpenable`) is
   passed as AxLeafS5's explicit `hlo`.
5. `releaseWpd3` / `releaseWpd3P` are theorems stated by `type_of%` of the partial application
   (Rocq `Definition … := λ …`), the remaining slots being binders of their types.
   `CondP_gate3_wpd` (Rocq section `atP`) sits in the main section, before `releaseWpd3P`.

**Rocq → Lean name map.**  `ArmedR` `armedR`, `GoalW3` `goalW3`, `capW3` `kctxW3` (deviation 1),
`pcW3` `pcW3`, `instrW3` `instrW3` (deviation 2), `w_sdlk3` `wSdlk3`, `w_fence3` `wFence3`,
`w_swfin3` `wSwfin3`, `release_wpd3` `releaseWpd3`, `CondP_gate3_wpd` `condPGate3Wpd`,
`release_wpd3_P` `releaseWpd3P`; section parameters `sdlk_rule` `sdlkRule`, `swlk_rule`
`swlkRule`, `locked_pre` `lockedPre`, `lock_openable` `lockOpenable`, `Hlo` `hlo`; `locked` ↦
`lockedCore` (in the rules; `locked` itself stays λ-bound), `lock_finisher` ↦ none (deviation 1).
None is in the duplicated-name table.  Lean-only (file-qualified): `AxCondM4.zeroStOrFence`,
`AxCondM4.rgetCpu`, `AxCondM4.kctxW3Kt`; new section parameter `held`.

**Dropped:** nothing (Rocq 11 definitions/lemmas; Lean 11 + 3 Lean-only).  **Not ported:** the
`Notation STORE_LEAF` (inlined), the `Check` / `Print Assumptions` lines (the lint's axiom check
covers them).
-/
import Weak.AxCondM
import Weak.AxCondM3
import Weak.AxLeafS5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `ArmedR`: the release flag is set exactly at release's `sw zero,0(s1)`. -/
def armedR (pc : BitVec 64) : Prop := pc = Xv6.releaseAddr + 0x1a#64

/-- (Lean-only, deviation 2) a store of `x0` or `fence rw,w`: never compressed in the text. -/
def AxCondM4.zeroStOrFence (ins : instruction) : Prop :=
  (∃ (imm : BitVec 12) (rs1 : BitVec 5) (wd : Nat),
    ins = .STORE (imm, .Regidx 0#5, .Regidx rs1, wd)) ∨ ins = fenceRwWIns

/-- (Lean-only) `rget` does not depend on the hart away from `tp`. -/
theorem AxCondM4.rgetCpu (c1 c2 : CPU) (m : RegMap) (r : BitVec 5) (h : r ≠ 4#5) :
    rget c1 m r = rget c2 m r := by
  by_cases h0 : r = 0#5
  · subst h0; simp
  · rw [rget_ne c1 m r h0 h, rget_ne c2 m r h0 h]

section WPdRelease3
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat]
variable (i : Agent) (cid cpu : CPU) (γm γp γn : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Cond : Prop → IProp GF)
variable (CondGate3 : ∀ s C, gateAt3 cpu σi T satp0 s →
  ⊢ Cond C -∗ (⌜C⌝ -∗ Cond C -∗ wpd .MaybeStuck i s (Φ0 (GF := GF))) -∗
    wpd .MaybeStuck i s (Φ0 (GF := GF)))
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (dreg damo : Int → Nat → Prop)
variable (Hdmap : ∀ (acc : MemoryAccessType mem_payload) (va : BitVec 64) (w : Nat),
  dreg (paZ va) w ∨ damo (paZ va) w → dataAtS σi T acc va w va)

/- the lock resources (abstract, AxLeafS5's interface) and the WPd lock protocol's two store
rules (deviation 1) -/
variable {Pay : Type _} (payAt : Pay → IProp GF) (payOk : Pay → Prop)
variable (lockOpenable : GName → BitVec 64 → String → Pay → IProp GF → IProp GF)
  (hlo : ∀ γ lk s R D, Persistent (lockOpenable γ lk s R D))
variable (lockedCore lockedPre : GName → CPU → IProp GF) (lockCtxHeld : IProp GF)
/- the hart's held-lock set (Lean's `lockSet cpu k.locks`; deviation 1) -/
variable (held : CPU → List String → IProp GF)
variable (sdlkRule : ∀ (c0 : CPU) (_cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String)
    (R : Pay) (Dc : IProp GF) (Pd : List (BitVec 8) → Prop),
  (∀ data, Pd data → data = stBytes 8 0#64) →
  ⊢ lockOpenable γl lk s R Dc -∗ lockedCore γl c0 -∗
    ⌜dreg (paZ (lk + 16#64)) 8⌝ ∗
    FstM rvwmoCatConsistent (dk3 (paZ (lk + 16#64)) 8) i
      (fun _ data => iprop(⌜Pd data⌝ -∗ lockedPre γl c0)))
variable (swlkRule : ∀ (c0 : CPU) (cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String)
    (R : Pay) (Dc : IProp GF) (ks : List String) (Pd : List (BitVec 8) → Prop),
  (∀ data, Pd data → data = stBytes 4 0#64) → cl = .WCrel → payOk R →
  ⊢ lockOpenable γl lk s R Dc -∗ lockedPre γl c0 -∗ payAt R -∗ lockCtxHeld -∗ held c0 ks -∗
    ⌜dreg (paZ lk) 4⌝ ∗
    FstM rvwmoCatConsistent (dk3 (paZ lk) 4) i
      (fun _ data => iprop(⌜Pd data⌝ -∗ held c0 (ks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ ks⌝)))
variable (kt : IProp GF) [Persistent kt]

/-- Rocq `GoalW3`: the ambient hart's `goal3`. -/
def goalW3 (_c : CPU) : IProp GF := goal3 i cid cpu γm γp γn T satp0 Cond

/-- Rocq `capW3`, at the Lean interface's `kctx` (deviation 1). -/
def kctxW3 (c : CPU) (k : KCtx) : IProp GF :=
  iprop(sieCap3 (GF := GF) γm γn c k.regs k.avail k.sie k.proc ∗ held c k.locks ∗ kt)

/-- Rocq `pcW3`. -/
def pcW3 (_c : CPU) (pc : BitVec 64) : IProp GF := pcIs3 (GF := GF) γp armedR pc

/-- Rocq `instrW3` (+ deviation 2). -/
def instrW3 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(instr3 (GF := GF) σi T satp0 armedR pc is_rvc ins ∗
    ⌜AxCondM4.zeroStOrFence ins → is_rvc = false⌝)

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF (BitVec 64 × Bool)] in
/-- (Lean-only) The kernel text sits in the context (the `kctx_kernelText` slot, REAL). -/
theorem AxCondM4.kctxW3Kt (c : CPU) (k : KCtx) :
    kctxW3 γm γn held kt c k ⊢ kt ∗ kctxW3 γm γn held kt c k := by
  unfold kctxW3
  iintro ⟨Hs, Hh, #Hkt⟩
  isplitl []
  · iexact Hkt
  · isplitl [Hs]
    · iexact Hs
    · isplitl [Hh]
      · iexact Hh
      · iexact Hkt

include hmode hasid hppn CondGate3 Htext Hflow Hloc HG Hdmap sdlkRule in
/-- Rocq `w_sdlk3`: release+0x12, `sd zero,16(s1)` — the owner clears `lk->cpu` (the
`wp_s_sd_zero_lkcpu_release_gen` slot). -/
theorem wSdlk3 (c : CPU) (k : KCtx) (_hsie : k.sie = false) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 : BitVec 5) (γ : GName) (lk : BitVec 64) (s : String) (R : Pay)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (haddr : k.rget c rs1 + BitVec.signExtend 64 imm = lk + 16#64) :
    instrW3 σi T satp0 pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) ∗
      kctxW3 γm γn held kt c k ∗ pcW3 γp c pc ∗ lockOpenable γ lk s R D ∗ Tc ∗ lockedCore γ c ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(kctxW3 γm γn held kt cpu' k -∗ pcW3 γp cpu' (pc + instrLen is_rvc) -∗
          (lockedPre γ c ∗ Tc) -∗ goalW3 i cid cpu γm γp γn T satp0 Cond cpu'))
      ⊢ goalW3 i cid cpu γm γp γn T satp0 Cond c := by
  cases is_rvc
  · dsimp only [instrLen]
    unfold instrW3 kctxW3 pcW3 goalW3 sieCap3 pcIs3
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hlo, HT, Hlc, Hcont⟩
    ihave %Hi3 := instr3Nrvc σi T satp0 armedR pc _ $$ Hi
    have Hi' : ⊢ instr3 (GF := GF) σi T satp0 armedR pc false
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) := by
      unfold instr3
      exact pure_intro ⟨.inl ⟨rfl, Hi3.1, Hi3.2.1⟩, Hi3.2.2.1, Hi3.2.2.2⟩
    have hb : rs1 ≠ 4#5 := fun h => Hi3.2.2.2 imm 0#5 rs1 8 rfl (by rw [h])
    have hpa : rget cid k.regs rs1 + sign_extend (m := 64) imm = lk + 16#64 := by
      rw [AxCondM4.rgetCpu cid c k.regs rs1 hb]; exact haddr
    have Hrule : ∀ cl : WmClass, ⊢ ⌜armedR pc → cl = .WCrel⌝ -∗
        iprop(lockOpenable γ lk s R D ∗ lockedCore γ c) -∗
        ⌜dreg (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 8⌝ ∗
        FstM rvwmoCatConsistent (dk3 (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 8) i
          (fun _ data => iprop(⌜data = stBytes 8 (rget cid k.regs 0#5) ∧
            ((0#5 : BitVec 5).toNat = 0 → data = stBytes 8 0#64)⌝ -∗ lockedPre γ c)) := by
      intro cl
      rw [hpa]
      iintro _ ⟨Hlo, Hlc⟩
      iapply (sdlkRule c cl γ lk s R D
        (fun data => data = stBytes 8 (rget cid k.regs 0#5) ∧
          ((0#5 : BitVec 5).toNat = 0 → data = stBytes 8 0#64))
        (fun _ h => h.2 rfl)) $$ Hlo Hlc
    have HS := wpStoreC3 (GF := GF) i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Cond
      CondGate3 Htext Hflow Hloc G HG dreg damo Hdmap pc 0#5 rs1 imm 8 k.regs k.avail k.sie
      k.proc iprop(lockOpenable γ lk s R D ∗ lockedCore γ c) (lockedPre γ c)
      (Or.inr (Or.inr (Or.inr rfl))) ⟨by decide, by decide⟩ Hrule
    unfold sieCap3 pcIs3 at HS
    ihave Hi := Hi'
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HS $$ Hs Hp Hi [Hlo Hlc]
    · isplitl [Hlo]
      · iexact Hlo
      · iexact Hlc
    iapply wpNext_intro_pin
    iintro %c' %_ Hs' Hp' Hpost
    iapply Hk $$ [Hs' Hheld] Hp' [Hpost HT]
    · isplitl [Hs']
      · iexact Hs'
      · isplitl [Hheld]
        · iexact Hheld
        · iexact Hkt
    · isplitl [Hpost]
      · iexact Hpost
      · iexact HT
  · unfold instrW3
    iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw (Or.inl ⟨imm, rs1, 8, rfl⟩)) (by decide)

include hmode hasid hppn Htext Hflow Hloc HG in
/-- Rocq `w_fence3`: release+0x16, `fence rw,w` — arms the flag (the `wp_s_fence_rw_w`
slot). -/
theorem wFence3 (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) :
    instrW3 σi T satp0 pc is_rvc
        (instruction.FENCE (0#4, 3#4, 1#4, regidx.Regidx 0#5, regidx.Regidx 0#5)) ∗
      kctxW3 γm γn held kt c k ∗ pcW3 γp c pc ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(kctxW3 γm γn held kt cpu' k -∗ pcW3 γp cpu' (pc + instrLen is_rvc) -∗
          goalW3 i cid cpu γm γp γn T satp0 Cond cpu'))
      ⊢ goalW3 i cid cpu γm γp γn T satp0 Cond c := by
  cases is_rvc
  · dsimp only [instrLen]
    have HF := wpFenceC3 (GF := GF) i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Cond
      Htext Hflow Hloc G HG pc k.regs k.avail k.sie k.proc
    unfold sieCap3 pcIs3 fenceRwWIns at HF
    unfold instrW3 kctxW3 pcW3 goalW3 sieCap3 pcIs3
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hcont⟩
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HF $$ Hs Hp Hi
    iapply wpNext_intro_pin
    iintro %c' %_ Hs' Hp'
    iapply Hk $$ [Hs' Hheld] Hp'
    isplitl [Hs']
    · iexact Hs'
    · isplitl [Hheld]
      · iexact Hheld
      · iexact Hkt
  · unfold instrW3
    iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw (Or.inr rfl)) (by decide)

include hmode hasid hppn CondGate3 Htext Hflow Hloc HG Hdmap swlkRule in
/-- Rocq `w_swfin3`: release+0x1a, `sw zero,0(s1)` — THE RELEASE STORE (class `WCrel`; the
`wp_s_sw_zero_release_gen` slot). -/
theorem wSwfin3 (c : CPU) (k : KCtx) (_hsie : k.sie = false) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 : BitVec 5) (γ : GName) (lk : BitVec 64) (s : String) (R : Pay)
    (hR : payOk R) (D : IProp GF) [Timeless D] (Tc : IProp GF)
    (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (haddr : k.rget c rs1 + BitVec.signExtend 64 imm = lk) :
    instrW3 σi T satp0 pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
      kctxW3 γm γn held kt c k ∗ pcW3 γp c pc ∗ lockOpenable γ lk s R D ∗ Tc ∗ lockedPre γ c ∗
      lockCtxHeld ∗ payAt R ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(kctxW3 γm γn held kt cpu' (k.withLocks (k.locks.filter (fun x => x ≠ s))) -∗
          pcW3 γp cpu' (pc + instrLen is_rvc) -∗ ⌜s ∈ k.locks⌝ -∗ Tc -∗
          goalW3 i cid cpu γm γp γn T satp0 Cond cpu'))
      ⊢ goalW3 i cid cpu γm γp γn T satp0 Cond c := by
  cases is_rvc
  · dsimp only [instrLen]
    unfold instrW3 kctxW3 pcW3 goalW3 sieCap3 pcIs3
    dsimp only [KCtx.withLocks]
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hlo, HT, Hlp, Hctx, HR, Hcont⟩
    ihave %Hi3 := instr3Nrvc σi T satp0 armedR pc _ $$ Hi
    have Hi' : ⊢ instr3 (GF := GF) σi T satp0 armedR pc false
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) := by
      unfold instr3
      exact pure_intro ⟨.inl ⟨rfl, Hi3.1, Hi3.2.1⟩, Hi3.2.2.1, Hi3.2.2.2⟩
    have hb : rs1 ≠ 4#5 := fun h => Hi3.2.2.2 imm 0#5 rs1 4 rfl (by rw [h])
    have Harm : armedR pc := Hi3.2.2.1 ⟨imm, rs1, rfl⟩
    have hpa : rget cid k.regs rs1 + sign_extend (m := 64) imm = lk := by
      rw [AxCondM4.rgetCpu cid c k.regs rs1 hb]; exact haddr
    have Hrule : ∀ cl : WmClass, ⊢ ⌜armedR pc → cl = .WCrel⌝ -∗
        iprop(lockOpenable γ lk s R D ∗ lockedPre γ c ∗ payAt R ∗ lockCtxHeld ∗ held c k.locks) -∗
        ⌜dreg (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 4⌝ ∗
        FstM rvwmoCatConsistent (dk3 (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 4) i
          (fun _ data => iprop(⌜data = stBytes 4 (rget cid k.regs 0#5) ∧
            ((0#5 : BitVec 5).toNat = 0 → data = stBytes 4 0#64)⌝ -∗
            held c (k.locks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ k.locks⌝)) := by
      intro cl
      rw [hpa]
      iintro %Hc ⟨Hlo, Hlp, HR, Hctx, Hh⟩
      iapply (swlkRule c cl γ lk s R D k.locks
        (fun data => data = stBytes 4 (rget cid k.regs 0#5) ∧
          ((0#5 : BitVec 5).toNat = 0 → data = stBytes 4 0#64))
        (fun _ h => h.2 rfl) (Hc Harm) hR) $$ Hlo Hlp HR Hctx Hh
    have HS := wpStoreC3 (GF := GF) i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Cond
      CondGate3 Htext Hflow Hloc G HG dreg damo Hdmap pc 0#5 rs1 imm 4 k.regs k.avail k.sie
      k.proc iprop(lockOpenable γ lk s R D ∗ lockedPre γ c ∗ payAt R ∗ lockCtxHeld ∗ held c k.locks)
      iprop(held c (k.locks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ k.locks⌝)
      (Or.inr (Or.inr (Or.inl rfl))) ⟨by decide, by decide⟩ Hrule
    unfold sieCap3 pcIs3 at HS
    ihave Hi := Hi'
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HS $$ Hs Hp Hi [Hlo Hlp HR Hctx Hheld]
    · isplitl [Hlo]
      · iexact Hlo
      · isplitl [Hlp]
        · iexact Hlp
        · isplitl [HR]
          · iexact HR
          · isplitl [Hctx]
            · iexact Hctx
            · iexact Hheld
    iapply wpNext_intro_pin
    iintro %c' %_ Hs' Hp' ⟨Hh', %hmem⟩
    iapply Hk $$ [Hs' Hh'] Hp' [] HT
    · isplitl [Hs']
      · iexact Hs'
      · isplitl [Hh']
        · iexact Hh'
        · iexact Hkt
    · ipureintro
      exact hmem
  · unfold instrW3
    iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw (Or.inl ⟨imm, rs1, 4, rfl⟩)) (by decide)

include hmode hasid hppn CondGate3 Htext Hflow Hloc HG Hdmap hlo sdlkRule swlkRule in
/-- **THE REPLAY with the three lock-word slots REAL** (Rocq `release_wpd3`): AxLeafS5's
`wpReleaseGen` at surface v3, the `sd` / `fence` / `sw` slots and the kernel-text projection
filled, every other slot and resource λ-bound (the binders of this type). -/
theorem releaseWpd3 :
    type_of% (AxLeafS5.wpReleaseGen (GF := GF) (Pay := Pay)
      (Goal := goalW3 i cid cpu γm γp γn T satp0 Cond)
      (kctx := kctxW3 γm γn held kt) (pcIs := pcW3 γp) (instr := instrW3 σi T satp0)
      (kernelText := kt) (hkt := inferInstance)
      (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable) (hlo := hlo)
      (lockedCore := lockedCore) (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld)
      (kctx_kernelText := AxCondM4.kctxW3Kt γm γn held kt)
      (wp_s_sd_zero_lkcpu_release_gen := wSdlk3 i cid cpu γm γp γn σi T satp0 hmode hasid hppn
        Cond CondGate3 Htext Hflow Hloc G HG dreg damo Hdmap lockOpenable lockedCore lockedPre
        held sdlkRule kt)
      (wp_s_fence_rw_w := wFence3 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Cond
        Htext Hflow Hloc G HG held kt)
      (wp_s_sw_zero_release_gen := AxLeafS5.relLeafOfFree (wSwfin3 i cid cpu γm γp γn σi T satp0 hmode hasid hppn
        Cond CondGate3 Htext Hflow Hloc G HG dreg damo Hdmap payAt payOk lockOpenable lockedPre
        lockCtxHeld held swlkRule kt))) :=
  AxLeafS5.wpReleaseGen (GF := GF) (Pay := Pay)
    (Goal := goalW3 i cid cpu γm γp γn T satp0 Cond)
    (kctx := kctxW3 γm γn held kt) (pcIs := pcW3 γp) (instr := instrW3 σi T satp0)
    (kernelText := kt) (hkt := inferInstance)
    (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable) (hlo := hlo)
    (lockedCore := lockedCore) (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld)
    (kctx_kernelText := AxCondM4.kctxW3Kt γm γn held kt)
    (wp_s_sd_zero_lkcpu_release_gen := wSdlk3 i cid cpu γm γp γn σi T satp0 hmode hasid hppn
      Cond CondGate3 Htext Hflow Hloc G HG dreg damo Hdmap lockOpenable lockedCore lockedPre
      held sdlkRule kt)
    (wp_s_fence_rw_w := wFence3 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Cond
      Htext Hflow Hloc G HG held kt)
    (wp_s_sw_zero_release_gen := AxLeafS5.relLeafOfFree (wSwfin3 i cid cpu γm γp γn σi T satp0 hmode hasid hppn
      Cond CondGate3 Htext Hflow Hloc G HG dreg damo Hdmap payAt payOk lockOpenable lockedPre
      lockCtxHeld held swlkRule kt))

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
/-- Rocq `CondP_gate3_wpd`: `CondGate3` DISCHARGED at the pure model. -/
theorem condPGate3Wpd : ∀ s C, gateAt3 cpu σi T satp0 s →
    ⊢ AxCondM.condP (GF := GF) C -∗
      (⌜C⌝ -∗ AxCondM.condP C -∗ wpd .MaybeStuck i s (Φ0 (GF := GF))) -∗
      wpd .MaybeStuck i s (Φ0 (GF := GF)) :=
  fun _ C _ => condPGate3 C _

include hmode hasid hppn Htext Hflow Hloc HG Hdmap hlo sdlkRule swlkRule in
/-- Rocq `release_wpd3_P`: `releaseWpd3` at `Cond := AxCondM.condP`, its gate discharged. -/
theorem releaseWpd3P :
    type_of% (releaseWpd3 (GF := GF) (Pay := Pay) (Cond := AxCondM.condP)
      (CondGate3 := condPGate3Wpd i cpu σi T satp0) i cid cpu γm γp γn σi T satp0 hmode hasid
      hppn Htext Hflow Hloc G HG dreg damo Hdmap payAt payOk lockOpenable hlo lockedCore lockedPre
      lockCtxHeld held sdlkRule swlkRule kt) :=
  releaseWpd3 (GF := GF) (Pay := Pay) (Cond := AxCondM.condP)
    (CondGate3 := condPGate3Wpd i cpu σi T satp0) i cid cpu γm γp γn σi T satp0 hmode hasid
    hppn Htext Hflow Hloc G HG dreg damo Hdmap payAt payOk lockOpenable hlo lockedCore lockedPre
    lockCtxHeld held sdlkRule swlkRule kt

end WPdRelease3

end Weak
