/-
Weak/Prom: **track (a), the LOOP FRONT END and the rest of the instruction kit** (stage S4a part 2; plan rev 7 §4
"Gate G4" (1): spinlocks — the manual's Examples 1, 2 (mm-explanatory.adoc:700–741) and xv6's exact acquire/release
text (Xv6/KernelImage.lean:2265–2274, :2359–2364) — need BACKWARD branches and `sext.w` = `addiw rd, rs1, 0`).

The litmus front end (MachCert.lean `litNext`) is loop-free (`instrNext`'s `.br`/`.jmp` arms refuse `tgt ≤ pc`) and
has no 32-bit ALU op.  Rather than edit `Instr` (matched exhaustively in 14 files of the shared tree), this file adds
a NEW program half over the same program state `LP`:
* `XI` — a front-end instruction: a litmus `Instr`, or `addiw rd, rs1, imm` (RV64I, unpriv rv64.adoc: "ADDIW is an
  RV64I instruction that adds the sign-extended 12-bit immediate to register rs1 and produces the proper sign
  extension of a 32-bit result in rd.  Overflows are ignored and the result is the low 32 bits of the result
  sign-extended to 64 bits"; `sext.w rd, rs1` is `addiw rd, rs1, 0`).  Its register labels are those of the other
  ALU-immediate instructions (`regWL rd (srcR rs1) ++ [LInstr]`, MachLitmus.lean's table: rs1 is the source).
* `XI.base` — the `Instr` stored in `LP.prog` (`addiw` is stored as `.nop`, a placeholder that is never executed:
  `xNext` reads the hart's `XI` text instead).
* `xNext Xs` — the label-level step: queued labels as `litNext`; at an instruction, the hart's `XI` text is the first
  `X ∈ Xs` with `X.map XI.base = prog` (`xOf`); `addiw` as above; `.br`/`.jmp` with ANY target `≤ |prog|` (backward
  allowed, same labels as `litNext`'s forward arm: `LCtrl (rs1 ++ rs2)` (rule 11), `LInstr`); everything else is
  `litNext`.  A hart whose text is not in `Xs` runs `litNext`.
* `xStep Xs` — the program half (no device fabric), `xW` its worlds; `xW` is a `LitW` world (queued labels and
  `pdone` as the litmus half), and at every plain instruction it agrees with `litNext` (`litAg_x`), so every kit rule
  of OwnAKit.lean applies unchanged.
New kit rules (any `LitW` world): `wpKA_alui`, `wpKA_rmw1`, `wpKA_amo`; over `xW`: `wpKA_brx` (any target),
`wpKA_addiw`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALib

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The loop front end -/

/-- A front-end instruction: a litmus instruction, or `addiw rd, rs1, imm`. -/
inductive XI where
  | i (ins : Instr)
  | addiw (rd rs1 imm : Nat)
  deriving DecidableEq

/-- The instruction stored in `LP.prog` (`addiw` as the placeholder `.nop`). -/
def XI.base : XI → Instr
  | .i ins => ins
  | .addiw .. => .nop

/-- `addiw`'s result: the low 32 bits of `a + imm`, sign-extended to 64 bits. -/
def addiwV (a imm : Nat) : Nat := sext 4 ((a + imm) % 2 ^ 32)

/-- The hart's `XI` text: the first `X ∈ Xs` whose base is the program. -/
def xOf (Xs : List (List XI)) (prog : List Instr) : Option (List XI) :=
  Xs.find? (fun X => decide (X.map XI.base = prog))

/-- THE LOOP FRONT END's label step (see the header). -/
def xNext (Xs : List (List XI)) (s : LP) (l : PLabel) : Option LP :=
  match s.q with
  | _ :: _ => litNext s l
  | [] =>
    match (xOf Xs s.prog).bind (fun X => X[s.pc]?) with
    | some (.addiw rd rs1 imm) =>
        go1 s (s.wr rd (addiwV (s.rd rs1) imm)) (s.pc + 1) (regWL rd (srcR rs1) ++ [LInstr]) l
    | some (.i (.br c rs1 rs2 tgt)) =>
        if s.prog.length < tgt then none else
        go1 s s.regs (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1)
          [LCtrl (srcR rs1 ++ srcR rs2), LInstr] l
    | some (.i (.jmp tgt)) => if s.prog.length < tgt then none else go1 s s.regs tgt [LInstr] l
    | _ => litNext s l

/-- THE PROGRAM HALF of the loop front end (no device fabric). -/
def xStep (Xs : List (List XI)) (s : LP) (_ : Unit) (l : PLabel) (s' : LP) (_ : Unit) : Prop :=
  xNext Xs s l = some s'

/-- A world of the loop front end. -/
abbrev xW (Xs : List (List XI)) (img : Image) (M : List PMsg) (h : Nat) : HW LP Unit Unit :=
  ⟨xStep Xs, litDone, img, M, h⟩

/-- A PLAIN instruction: `xNext` runs it as `litNext` does. -/
def XI.plain : XI → Bool
  | .i (.br ..) => false
  | .i (.jmp ..) => false
  | .i _ => true
  | .addiw .. => false

theorem anyFab_x {Xs : List (List XI)} {s : LP} {l : PLabel} {s' : LP} :
    anyFab (xStep Xs) s () l s' () ↔ xNext Xs s l = some s' :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(), (), h⟩⟩

theorem xNext_q {Xs : List (List XI)} {s : LP} (hq : s.q ≠ []) (l : PLabel) : xNext Xs s l = litNext s l := by
  unfold xNext
  cases h : s.q with
  | nil => exact absurd h hq
  | cons _ _ => rfl

theorem xNext_plain {Xs : List (List XI)} {s : LP} (hq : s.q = [])
    (hp : ∀ x, (xOf Xs s.prog).bind (fun X => X[s.pc]?) = some x → x.plain = true) (l : PLabel) :
    xNext Xs s l = litNext s l := by
  unfold xNext
  rw [hq]
  simp only
  split
  · next h => have := hp _ h; simp [XI.plain] at this
  · next h => have := hp _ h; simp [XI.plain] at this
  · next h => have := hp _ h; simp [XI.plain] at this
  · rfl

/-- The loop front end's worlds are litmus worlds. -/
theorem litW_x (Xs : List (List XI)) (img : Image) (M : List PMsg) (h : Nat) : LitW (xW Xs img M h) := by
  refine ⟨fun s hs l s' => ?_, fun s hs => ?_⟩
  · show anyFab (xStep Xs) s () l s' () ↔ litNext s l = some s'
    rw [anyFab_x, xNext_q hs]
  · rcases hs with hs | hs
    · exact litDone_q hs
    · exact litDone_pc hs

/-- At a plain instruction the loop front end agrees with `litNext`. -/
theorem litAg_x {Xs : List (List XI)} {img : Image} {M : List PMsg} {h : Nat} {s : LP} {X : List XI} {x : XI}
    (hq : s.q = []) (hX : xOf Xs s.prog = some X) (hx : X[s.pc]? = some x) (hpl : x.plain = true) :
    LitAg (xW Xs img M h) s := by
  intro l s'
  show anyFab (xStep Xs) s () l s' () ↔ litNext s l = some s'
  rw [anyFab_x, xNext_plain hq (fun y hy => by rw [hX] at hy; simp only [Option.bind_some, hx] at hy; cases hy; exact hpl)]

/-- Where the text has no extension instruction (or none at all), the loop front end agrees with `litNext`. -/
theorem litAg_xn {Xs : List (List XI)} {img : Image} {M : List PMsg} {h : Nat} {s : LP} (hq : s.q = [])
    (hp : ∀ x, (xOf Xs s.prog).bind (fun X => X[s.pc]?) = some x → x.plain = true) :
    LitAg (xW Xs img M h) s := by
  intro l s'
  show anyFab (xStep Xs) s () l s' () ↔ litNext s l = some s'
  rw [anyFab_x, xNext_plain hq hp]

/-- The program of a hart whose text is the first of `Xs` with its base. -/
theorem xOf_self {Xs : List (List XI)} {X : List XI} (h : xOf Xs (X.map XI.base) = some X) :
    xOf Xs (X.map XI.base) = some X := h

/-- The base program has the text's length. -/
theorem base_len {X : List XI} {prog : List Instr} (h : X.map XI.base = prog) : X.length = prog.length := by
  rw [← h, List.length_map]

/-- The base program's instruction at `pc` is the base of the text's. -/
theorem base_at {X : List XI} {prog : List Instr} (h : X.map XI.base = prog) {pc : Nat} {x : XI}
    (hx : X[pc]? = some x) : prog[pc]? = some x.base := by
  rw [← h, List.getElem?_map, hx]; rfl

theorem xOf_spec {Xs : List (List XI)} {prog : List Instr} {X : List XI} (h : xOf Xs prog = some X) :
    X.map XI.base = prog := by
  have := List.find?_some h
  simpa using this

theorem xNext_br {Xs : List (List XI)} {s : LP} {X : List XI} {c : Weak.Prom.Ref.BrC} {rs1 rs2 tgt : Nat}
    (hq : s.q = []) (hX : xOf Xs s.prog = some X) (hx : X[s.pc]? = some (.i (.br c rs1 rs2 tgt)))
    (ht : tgt ≤ s.prog.length) {l : PLabel} {s' : LP} (h : xNext Xs s l = some s') :
    l = LCtrl (srcR rs1 ++ srcR rs2) ∧
      s' = { s with regs := s.regs, pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1, q := [LInstr] } := by
  unfold xNext at h
  rw [hq] at h
  simp only [hX, Option.bind_some, hx, show ¬ s.prog.length < tgt by omega, if_false, go1] at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

theorem xNext_addiw {Xs : List (List XI)} {s : LP} {X : List XI} {rd rs1 imm : Nat}
    (hq : s.q = []) (hX : xOf Xs s.prog = some X) (hx : X[s.pc]? = some (.addiw rd rs1 imm)) (hrd : rd ≠ 0)
    {l : PLabel} {s' : LP} (h : xNext Xs s l = some s') :
    l = LRegW rd (srcR rs1) ∧
      s' = { s with regs := s.wr rd (addiwV (s.rd rs1) imm), pc := s.pc + 1, q := [LInstr] } := by
  unfold xNext at h
  rw [hq] at h
  simp only [hX, Option.bind_some, hx, go1, regWL, hrd, if_false, List.singleton_append] at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

/-! ## 2. The rest of the kit -/

section kit

variable {V : Type} {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF]
variable {g : AGN} {π : Proto} {w : HW LP Unit V} {Qs : Nat → Trace → Prop} {Φ : V → IProp GF}

/-- **ALU-immediate instruction** `op rd, rs1, imm` (`rd ≠ x0`; `li`, `mv`): `LRegW rd rs1`, `LInstr` (the last
with a fupd at its pre-state's frontier). -/
theorem wpKA_alui (hw : LitW w) {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 imm : Nat} {ws : PState} {pr : GSet Nat}
    {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.alui op rd rs1 imm)) (hrd : rd ≠ 0) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) imm)⌝ -∗ frontA g π w.img w.M (regWP ws rd (srcR rs1)) -∗
        £ 1 -∗ |={⊤}=> (lhA g π w (Qs w.h) (instrR (regWP ws rd (srcR rs1))) pr ev -∗ wpKA g π w Qs s' Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_q1 (k := { s with regs := s.wr rd (aluOp op (s.rd rs1) imm), pc := s.pc + 1, q := [LInstr] })
    (l0 := LRegW rd (srcR rs1)) (ws1 := regWP ws rd (srcR rs1)) rfl (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => litNext_alui hq hp hrd ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro _ _
  imodintro
  iintro Hl
  iapply (wpKA_drainA hw [LInstr] _ { s with regs := s.wr rd (aluOp op (s.rd rs1) imm), pc := s.pc + 1, q := [] }
    _ (by simp) (by simp [quietL]) rfl rfl)
  iframe Hl
  inext
  simp only [List.dropLast, qPosts, qPost]
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hf Hc

/-- ONE FUSED AMO LABEL (M0): the client hands back `fulT g ts`. -/
theorem wpKA_rmw1 {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {asrc vsrc : List Dsrc} {dat : List (Nat × BitVec 8) → List (BitVec 8)} {k : List (Nat × BitVec 8) → LP}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LRmw aq rl base tvs (dat tvs) asrc vsrc ∧ s' = k tvs ∧
      C tvs)
    (hnoinv : ∀ t a, ¬ cmoAt w.M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ tvs ts, ⌜C tvs⌝ -∗ ⌜tvs.length = (dat tvs).length⌝ -∗ ⌜ts ∈ pr⌝ -∗
        ⌜w.M[ts - 1]? = some ⟨base, dat tvs, some w.h, .excl⟩⌝ -∗
        ⌜loadOk w.img w.M ws (ldPre ws aq false (srcsView ws asrc)) base tvs⌝ -∗
        ⌜exclOk w.M w.h base (tvs.map Prod.fst) ts⌝ -∗
        ⌜cohBelow (loadRun ws aq false (srcsView ws asrc) base tvs) base (dat tvs).length ts⌝ -∗
        ⌜stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) (srcsView ws vsrc) < ts⌝ -∗
        frontA g π w.img w.M ws -∗ £ 1 -∗
        |={⊤}=> (⌜(∃ V, grd π w.img w.M V (Qs w.h (ev ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]))) ∧
            grd π w.img w.M (stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
              (srcsView ws vsrc)) (π.okMsg ⟨base, dat tvs, some w.h, .excl⟩)⌝ ∨ dshot g) ∗ fulT g ts ∗
          (lhA g π w (Qs w.h) (amoPost (storeRun (loadRun ws aq false (srcsView ws asrc) base tvs) rl
              (srcsView ws asrc) ts base (dat tvs).length ts) aq ts) (pr \ {ts})
              (ev ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]) -∗
            wpKA g π w Qs (k tvs) Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv, _⟩, Hk⟩
  obtain ⟨he, hw⟩ := hinv
  iapply wpA_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr'' %hp %hm Hf Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | rmw _ _ _ _ _ _ _ ts hlen hts hmsg hlo hex hcoh hext vi hci _ =>
    obtain rfl := invalCite_vi0 hnoinv hci
    rw [loadRunV_zero]
    imod Hk $$ %tvs %ts %hC %hlen %hts %hmsg %hlo %hex %hcoh %hext Hf Hc with ⟨#Hr, #Hsh, Hk⟩
    have hw' : wrOk w.M (τ ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]) :=
      wrOk_snoc_some hw hmsg (by omega) rfl
    imodintro
    isplitr
    · icases Hr with (%hQ | #Hd)
      · obtain ⟨⟨V', hg⟩, hpv⟩ := hQ
        ileft; ipureintro
        refine ⟨⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, hw'⟩⟩, fun t ht m hm => ?_⟩
        cases ht
        obtain ⟨k', rfl⟩ : ∃ k', ts = k' + 1 := ⟨ts - 1, by omega⟩
        simp only [msgAt] at hm
        simp only [Nat.add_sub_cancel] at hmsg
        rw [hmsg] at hm; cases hm
        exact hpv
      · iright; iexact Hd
    isplitr
    · iintro %t %ht; cases ht; iexact Hsh
    · iintro Hst
      iapply Hk
      unfold lhA
      iexists τ ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]
      iframe Hst
      isplitr
      · ipureintro; exact ⟨by rw [memEv_snoc _ _ rfl, he], hw'⟩
      · icases Hr with (%hQ | #Hd)
        · ileft; ipureintro; exact hQ.1
        · iright; iexact Hd

/-- **AMO instruction** `amo<op>.<sz>[.aq][.rl] rd, rs2, (rs1)` (fused, M0): `LRmw` (FULFIL; hand back `fulT`),
`LRegW rd [DLdRes]` (unless `rd = x0`), `LInstr` (the last with a fupd at its pre-state's frontier). -/
theorem wpKA_amo (hw : LitW w) {s : LP} {op : Weak.Prom.Ref.AmoOp} {sz : Nat} {aq rl : Bool} {rd rs2 rs1 : Nat}
    {base : Int} {ws : PState} {pr : GSet Nat} {ev : Trace} (hag : LitAg w s) (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.amo op sz aq rl rd rs2 rs1)) (ha : aligned (s.rd rs1) sz = true)
    (hb : ((s.rd rs1 : Nat) : Int) = base)
    (hnoinv : ∀ t a, ¬ cmoAt w.M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ tvs ts, ⌜tvs.length = sz⌝ -∗ ⌜ts ∈ pr⌝ -∗
        ⌜w.M[ts - 1]? = some ⟨base, amoD op sz (s.rd rs2) tvs, some w.h, .excl⟩⌝ -∗
        ⌜loadOk w.img w.M ws (ldPre ws aq false (srcsView ws (srcR rs1))) base tvs⌝ -∗
        ⌜exclOk w.M w.h base (tvs.map Prod.fst) ts⌝ -∗
        ⌜cohBelow (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) base (amoD op sz (s.rd rs2) tvs).length ts⌝ -∗
        ⌜stPre (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) rl (srcsView ws (srcR rs1))
          (srcsView ws (srcR rs2)) < ts⌝ -∗
        frontA g π w.img w.M ws -∗ £ 1 -∗
        |={⊤}=> (⌜(∃ V, grd π w.img w.M V
            (Qs w.h (ev ++ [(LRmw aq rl base tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1) (srcR rs2), some ts)]))) ∧
          grd π w.img w.M (stPre (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) rl (srcsView ws (srcR rs1))
            (srcsView ws (srcR rs2))) (π.okMsg ⟨base, amoD op sz (s.rd rs2) tvs, some w.h, .excl⟩)⌝ ∨ dshot g) ∗
          fulT g ts ∗
          (∀ s', ⌜LPstep s s' (s.pc + 1) rd (sext sz (ofBytes (tvs.map Prod.snd)))⌝ -∗
            frontA g π w.img w.M (qPosts (amoPost (storeRun (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) rl
                (srcsView ws (srcR rs1)) ts base (amoD op sz (s.rd rs2) tvs).length ts) aq ts)
                (regWL rd [.DLdRes] ++ [LInstr]).dropLast) -∗ £ 1 -∗
            |={⊤}=> (lhA g π w (Qs w.h) (qPosts (amoPost (storeRun (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) rl
                (srcsView ws (srcR rs1)) ts base (amoD op sz (s.rd rs2) tvs).length ts) aq ts)
                (regWL rd [.DLdRes] ++ [LInstr])) (pr \ {ts})
              (ev ++ [(LRmw aq rl base tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1) (srcR rs2), some ts)]) -∗
            wpKA g π w Qs s' Φ)))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_rmw1 (dat := amoD op sz (s.rd rs2))
    (k := fun tvs =>
      { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] })
    (C := fun tvs => tvs.length = sz) (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_amo hq hp ha ((hag l s').1 hs)
      exact ⟨tvs, by rw [h1, hb], h2, h3⟩))
  iframe Hl
  inext
  iintro %tvs %ts %hC %_ %hts %hmsg %hlo %hex %hcoh %hext Hf Hc
  imod Hk $$ %tvs %ts %hC %hts %hmsg %hlo %hex %hcoh %hext Hf Hc with ⟨Hr, Hsh, Hk⟩
  imodintro
  iframe Hr Hsh
  iintro Hl
  iapply (wpKA_drainA hw (regWL rd [.DLdRes] ++ [LInstr]) _
    { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1, q := [] } _ (by simp)
    (quiet_regWL rd _ (by simp [quietL])) rfl rfl)
  iframe Hl
  inext
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hf Hc

/-- The loop front end at a state: its program half is `xNext`. -/
def XAg (Xs : List (List XI)) (w : HW LP Unit V) (s : LP) : Prop :=
  ∀ l s', anyFab w.pstep s () l s' () ↔ xNext Xs s l = some s'

theorem xAg_x (Xs : List (List XI)) (img : Image) (M : List PMsg) (h : Nat) (s : LP) :
    XAg Xs (xW Xs img M h) s := fun _ _ => anyFab_x

theorem pc_lt_x {Xs : List (List XI)} {s : LP} {X : List XI} {x : XI} (hX : xOf Xs s.prog = some X)
    (hx : X[s.pc]? = some x) : s.pc < s.prog.length := by
  rw [← base_len (xOf_spec hX)]; exact (List.getElem?_eq_some_iff.1 hx).1

/-- **BRANCH instruction, any target** (loop front end): `LCtrl (rs1 ++ rs2)` (rule 11), `LInstr` (the last with a
fupd at its pre-state's frontier). -/
theorem wpKA_brx {Xs : List (List XI)} (hw : LitW w) {s : LP} {X : List XI} {c : Weak.Prom.Ref.BrC}
    {rs1 rs2 tgt : Nat} {ws : PState} {pr : GSet Nat} {ev : Trace} (hag : XAg Xs w s) (hq : s.q = [])
    (hX : xOf Xs s.prog = some X) (hx : X[s.pc]? = some (.i (.br c rs1 rs2 tgt))) (ht : tgt ≤ s.prog.length) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1) 0 0⌝ -∗
        frontA g π w.img w.M (ctrlP ws (srcR rs1 ++ srcR rs2)) -∗ £ 1 -∗
        |={⊤}=> (lhA g π w (Qs w.h) (instrR (ctrlP ws (srcR rs1 ++ srcR rs2))) pr ev -∗ wpKA g π w Qs s' Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_q1
    (k := { s with regs := s.regs, pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1, q := [LInstr] })
    (l0 := LCtrl (srcR rs1 ++ srcR rs2)) (ws1 := ctrlP ws (srcR rs1 ++ srcR rs2)) rfl
    (hw.2 s (.inr (pc_lt_x hX hx)))
    (fun l s' hs => xNext_br hq hX hx ht ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro _ _
  imodintro
  iintro Hl
  iapply (wpKA_drainA hw [LInstr] _
    { s with pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1, q := [] } _ (by simp) (by simp [quietL])
    rfl rfl)
  iframe Hl
  inext
  simp only [List.dropLast, qPosts, qPost]
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_same s _) Hf Hc

/-- **`addiw rd, rs1, imm`** (`sext.w` = `addiw rd, rs1, 0`; loop front end, `rd ≠ x0`): `LRegW rd rs1`, `LInstr`. -/
theorem wpKA_addiw {Xs : List (List XI)} (hw : LitW w) {s : LP} {X : List XI} {rd rs1 imm : Nat} {ws : PState}
    {pr : GSet Nat} {ev : Trace} (hag : XAg Xs w s) (hq : s.q = []) (hX : xOf Xs s.prog = some X)
    (hx : X[s.pc]? = some (.addiw rd rs1 imm)) (hrd : rd ≠ 0) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (s.pc + 1) rd (addiwV (s.rd rs1) imm)⌝ -∗ frontA g π w.img w.M (regWP ws rd (srcR rs1)) -∗
        £ 1 -∗ |={⊤}=> (lhA g π w (Qs w.h) (instrR (regWP ws rd (srcR rs1))) pr ev -∗ wpKA g π w Qs s' Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_q1 (k := { s with regs := s.wr rd (addiwV (s.rd rs1) imm), pc := s.pc + 1, q := [LInstr] })
    (l0 := LRegW rd (srcR rs1)) (ws1 := regWP ws rd (srcR rs1)) rfl (hw.2 s (.inr (pc_lt_x hX hx)))
    (fun l s' hs => xNext_addiw hq hX hx hrd ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro _ _
  imodintro
  iintro Hl
  iapply (wpKA_drainA hw [LInstr] _ { s with regs := s.wr rd (addiwV (s.rd rs1) imm), pc := s.pc + 1, q := [] }
    _ (by simp) (by simp [quietL]) rfl rfl)
  iframe Hl
  inext
  simp only [List.dropLast, qPosts, qPost]
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hf Hc

end kit

/-! ## MachFix-R-b5: the loop front end issues no cache-block operation -/

theorem go1_qnc {s s' : LP} {regs : List Nat} {pc : Nat} {labs : List PLabel} {l : PLabel}
    (h : go1 s regs pc labs l = some s') (hq : qOk labs.tail)
    (hnc : ∀ x ∈ labs, ∀ k b len asrc, x ≠ LCmo k b len asrc) :
    qOk s'.q ∧ ∀ k b len asrc, l ≠ LCmo k b len asrc := by
  obtain ⟨rest, rfl, rfl⟩ := go1_eq h
  exact ⟨hq, hnc _ (List.mem_cons_self ..)⟩

theorem qOk_noCmo {q : List PLabel} (h : qOk q) : ∀ x ∈ q, ∀ k b len asrc, x ≠ LCmo k b len asrc := by
  intro x hx k b len asrc he
  subst he
  have := h.1 _ hx
  simp [qLab] at this

theorem qOk_tl {q : List PLabel} (h : qOk q) : qOk q.tail := by
  cases q with
  | nil => exact qOk_nil
  | cons l r => exact qOk_tail h

/-- Every valid run of the loop front end has no invalidate-class message (its labels are `litNext`'s or
answer-free; LitNoCmo.lean `noInval_of_noCmoLab`), so machine v2's load-like arms take `vi = 0` there. -/
theorem x_noInvalT {Xs : List (List XI)} {T : Test} {img : Image} {M : List PMsg} {run : PFRun LP Unit}
    (hv : PF.validRun (xStep Xs) img () (progs T) M run) : ∀ t a, ¬ cmoAt M isInvalK t a := by
  rw [← hv.2]
  refine Own.noInval_of_noCmoLab (fun s => qOk s.q) (fun p hp => by rw [Own.progs_q T p hp]; exact qOk_nil)
    (fun s l s' hq hs => ?_) hv.1
  have hs' : xNext Xs s l = some s' := hs
  unfold xNext at hs'
  split at hs'
  · exact ⟨Mach.litNext_q hq hs', (Own.litNext_nf hq hs').2⟩
  · split at hs'
    · exact go1_qnc hs' (qOk_tl (qOk_regWL1 _ _)) (qOk_noCmo (qOk_regWL1 _ _))
    · split at hs'
      · cases hs'
      · refine go1_qnc hs' (by simp [qOk, qLab, isRegW]) (fun x hx => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> intro _ _ _ _ h <;> cases h
    · split at hs'
      · cases hs'
      · refine go1_qnc hs' (by simp [qOk, qLab, isRegW]) (fun x hx => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx; intro _ _ _ _ h; cases h
    · exact ⟨Mach.litNext_q hq hs', (Own.litNext_nf hq hs').2⟩

end Weak.Prom.OA
