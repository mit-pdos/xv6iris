/-
Weak/Prom: **completeness S3a — the simulation invariant** (plan rev 7 §6 "Step each hart in po with a
simulation `sim_state`/`sim_view`/`sim_local` (AtoP.v:150–316). Each Wstate view is the gmo position of the latest
relevant event (`view_of_eid`, :61)").

`SimInv T X ν h sf s lp ws prom` relates hart `h`'s symbolic state `s` (on its way to the final state `sf`) to the
machine's program state `lp`, agent state `ws` and promise set `prom`, with `n = |s.evs|` events done:
* `lp` is at `s`'s pc with `s`'s register VALUES (`regEq`);
* Pulte's `sim_view`, in two forms.  PAST form (`domF`): every register view is below the view of an event its
  taint names (`regv`); `vrOld` (`vwOld`) below a past load's (store's) view.  FUTURE form (the consequence the next
  steps need, maintained through a ppo rule each): `vrNew` below every future load's view (rule 4), `vwNew` and the
  capture view `vcap` strictly below every future store's (rules 4, 11, 13), the coherence floor of a byte strictly
  below every future store to it (rule 1), and every store at or below the floor is at or below the store each future
  load of the byte reads (`coh2`: rules 1, 2 + the load value axiom);
* the forward bank holds, per byte, the hart's po-latest store to it, with its timestamp and a forward view below
  every future load that reads it (`fwdOk`, rule 12);
* the promise set is exactly the hart's future stores' timestamps (AtoP's `PROMISES`).
`inv_nomem` transports the invariant over a step that emits no memory operation.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpCtx

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

/-! ## 1. The invariant -/

/-- THE FORWARD BANK'S ENTRY for byte `x` after `n` events (Pulte AtoP's `FWDBANK`). -/
def fwdOk (X : Exec) (h nF n x : Nat) : Option (Nat × Nat) → Prop
  | none => ∀ j, j < n → (X.sk (h, j)).kind.isStore = true → touches (X.ev (h, j)) x = false
  | some (tf, vf) => ∃ j, j < n ∧ (X.sk (h, j)).kind.isStore = true ∧ touches (X.ev (h, j)) x = true ∧
      (∀ j2, j < j2 → j2 < n → (X.sk (h, j2)).kind.isStore = true → touches (X.ev (h, j2)) x = false) ∧
      tf = vo X (h, j) ∧
      ∀ j', n ≤ j' → j' < nF → (X.sk (h, j')).kind.isLoad = true → touches (X.ev (h, j')) x = true →
        rfSrc X (h, j') x = some (h, j) → vf ≤ vo X (h, j')

/-- THE SIMULATION INVARIANT (see the file header). -/
structure SimInv (T : Test) (X : Exec) (ν : Val) (h : Nat) (sf : SSt) (s : SSt) (lp : LP) (ws : PState)
    (prom : GSet Nat) : Prop where
  wf : SymWf s
  fut : Future s sf
  prog : lp.prog = T.prog h
  pc : lp.pc = s.pc
  q : lp.q = []
  lpLen : lp.regs.length = 32
  regEq : ∀ r, lp.rd r = (s.rd r).1.eval ν
  regLt : ∀ r, (s.rd r).1.eval ν < two64
  regv : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j)) (· ∈ (s.rd r).2) (regv ws r)
  vrOld : domF (fun j => vo X (h, j)) (fun j => j < s.evs.length ∧ (X.sk (h, j)).kind.isLoad = true) ws.wVrOld
  vwOld : domF (fun j => vo X (h, j)) (fun j => j < s.evs.length ∧ (X.sk (h, j)).kind.isStore = true) ws.wVwOld
  vrNew : ∀ j, s.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isLoad = true →
    ws.wVrNew ≤ vo X (h, j)
  vwNew : ∀ j, s.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isStore = true →
    ws.wVwNew < vo X (h, j)
  vcap : ∀ j, s.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isStore = true →
    ws.wVcap < vo X (h, j)
  coh1 : ∀ (x : Nat) j, s.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isStore = true →
    touches (X.ev (h, j)) x = true → coh ws x < vo X (h, j)
  coh2 : ∀ (x : Nat) j, s.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isLoad = true →
    touches (X.ev (h, j)) x = true → ∀ w ∈ X.gmo, writesB (X.ev w) x = true → vo X w ≤ coh ws x →
      vo X w ≤ kts X (rfSrc X (h, j) x)
  fwd : ∀ x : Nat, fwdOk X h sf.evs.length s.evs.length x (get? ws.wFwd (x : Int))
  ldv : ws.wLdv = 0
  ifv : ws.wIfv = 0
  prom : ∀ t, t ∈ prom ↔ ∃ j, s.evs.length ≤ j ∧ j < sf.evs.length ∧ (X.sk (h, j)).kind.isStore = true ∧
    vo X (h, j) = t

/-- The reference row segment of hart `h`'s events `n … m-1`. -/
def rowSeg (X : Exec) (h n m : Nat) : List (List Nat) :=
  ((List.range' n (m - n)).filter (fun j => (X.sk (h, j)).kind.isLoad)).map (fun j => (X.ev (h, j)).rdat)

/-- ONE INSTRUCTION SIMULATED: machine steps from `(lp, ws, prom)` whose loads answer the reference's new loads,
reaching a state related to `s'`. -/
def StepOk (T : Test) (X : Exec) (ν : Val) (h : Nat) (sf s : SSt) (lp : LP) (ws : PState) (prom : GSet Nat)
    (s' : SSt) : Prop :=
  ∃ tr lp' ws' prom', soloSteps litStep (testImg T) (memOf X) h (lp, ws, prom) tr (lp', ws', prom') ∧
    machRow tr = rowSeg X h s.evs.length s'.evs.length ∧ SimInv T X ν h sf s' lp' ws' prom'

theorem rowSeg_self (X : Exec) (h n : Nat) : rowSeg X h n n = [] := by simp [rowSeg]

theorem rowSeg_append (X : Exec) (h n m p : Nat) (h1 : n ≤ m) (h2 : m ≤ p) :
    rowSeg X h n m ++ rowSeg X h m p = rowSeg X h n p := by
  unfold rowSeg
  rw [← List.map_append, ← List.filter_append]
  congr 2
  have := @List.range'_append n (m - n) (p - m) 1
  simp only [Nat.one_mul] at this
  rw [show n + (m - n) = m by omega, show m - n + (p - m) = p - n by omega] at this
  exact this

theorem rowSeg_one (X : Exec) (h n : Nat) :
    rowSeg X h n (n + 1) = if (X.sk (h, n)).kind.isLoad then [(X.ev (h, n)).rdat] else [] := by
  unfold rowSeg
  simp only [Nat.add_sub_cancel_left, List.range'_one]
  split <;> simp_all

/-! ## 2. Registers -/

theorem aluOp_lt (op : Alu) {a b : Nat} (ha : a < two64) (hb : b < two64) : aluOp op a b < two64 := by
  have h64 : two64 = 2 ^ 64 := rfl
  cases op with
  | add => exact Nat.mod_lt _ (by decide)
  | sub => exact Nat.mod_lt _ (by decide)
  | xor => simp only [aluOp]; rw [h64] at *; exact Nat.xor_lt_two_pow ha hb
  | or => simp only [aluOp]; rw [h64] at *; exact Nat.or_lt_two_pow ha hb
  | and => simp only [aluOp]; rw [h64] at *; exact Nat.and_lt_two_pow _ hb
  | sll => exact Nat.mod_lt _ (by decide)
  | srl => simp only [aluOp]; exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
  | sra =>
    simp only [aluOp]
    split
    · exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
    · rw [h64] at *
      apply Nat.or_lt_two_pow (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha)
      have : 0 < 2 ^ (64 - b % 64) := Nat.two_pow_pos _
      have h2 : (2 : Nat) ^ 64 = two64 := rfl
      omega
  | slt => simp only [aluOp]; split <;> decide
  | sltu => simp only [aluOp]; split <;> decide
  | mul => exact Nat.mod_lt _ (by decide)

theorem LP.rd_set (lp : LP) (regs : List Nat) (pc : Nat) (q : List PLabel) (r : Nat) :
    ({ lp with regs := regs, pc := pc, q := q } : LP).rd r = if r = 0 then 0 else (regs[r]?).getD 0 := rfl

theorem LP.wr_rd (lp : LP) (rd v r : Nat) :
    (if r = 0 then 0 else ((lp.wr rd v)[r]?).getD 0) =
      if rd ≠ 0 ∧ r = rd ∧ rd < lp.regs.length then v % two64 else lp.rd r := by
  unfold LP.wr LP.rd
  by_cases h0 : rd = 0
  · simp [h0]
  · rw [if_neg h0]
    by_cases hr0 : r = 0
    · simp only [hr0, if_true]
      split
      · rename_i hh; exact absurd hh.2.1.symm h0
      · rfl
    · simp only [hr0, if_false]
      by_cases hrr : r = rd
      · subst hrr
        by_cases hl : r < lp.regs.length
        · simp [h0, hl]
        · simp [h0, hl]
      · simp [hrr, List.getElem?_set_ne (Ne.symm hrr)]

theorem LP.wr_len (lp : LP) (rd v : Nat) : (lp.wr rd v).length = lp.regs.length := by
  unfold LP.wr; split <;> simp

/-- The register file after `wr`, on both sides. -/
theorem regs_wr {lp : LP} {s : SSt} {ν : Val} (hl1 : lp.regs.length = 32) (hl2 : s.regs.length = 32)
    (heq : ∀ r, lp.rd r = (s.rd r).1.eval ν) (rd v : Nat) (e : Ex × List Nat) (hv : v % two64 = e.1.eval ν) :
    ∀ r, (if r = 0 then 0 else ((lp.wr rd v)[r]?).getD 0) = ((s.wr rd e).rd r).1.eval ν := by
  intro r
  rw [LP.wr_rd, SSt.rd_wr, hl1, hl2]
  split
  · exact hv
  · exact heq r

theorem regsLt_wr {s : SSt} {ν : Val} (hlt : ∀ r, (s.rd r).1.eval ν < two64) (rd : Nat) (e : Ex × List Nat)
    (he : e.1.eval ν < two64) : ∀ r, ((s.wr rd e).rd r).1.eval ν < two64 := by
  intro r; rw [SSt.rd_wr]; split
  · exact he
  · exact hlt r

theorem eval_c_lt (v : Nat) (ν : Val) : (Ex.c v).eval ν < two64 := Nat.mod_lt _ (by decide)

/-! ## 3. Views of sources -/

theorem srcsView_nil (ws : PState) : srcsView ws [] = 0 := rfl

theorem srcsView_append (ws : PState) (a b : List Dsrc) :
    srcsView ws (a ++ b) = max (srcsView ws a) (srcsView ws b) := by
  induction a with
  | nil => simp [srcsView]
  | cons x t ih =>
    simp only [List.cons_append, srcsView, List.foldr_cons] at ih ⊢
    rw [ih]; omega

theorem srcsView_srcR (ws : PState) (r : Nat) : srcsView ws (srcR r) = if r = 0 then 0 else regv ws r := by
  unfold srcR
  split
  · rfl
  · simp [srcsView, dsrcView]

theorem srcsView_ld (ws : PState) : srcsView ws [Dsrc.DLdRes] = ws.wLdv := by
  simp [srcsView, dsrcView]

/-- A source register's view is dominated by its taint. -/
theorem domF_srcR {X : Exec} {h : Nat} {s : SSt} {ws : PState}
    (hregv : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j)) (· ∈ (s.rd r).2) (regv ws r))
    {r : Nat} (hr : r < 32) : domF (fun j => vo X (h, j)) (· ∈ (s.rd r).2) (srcsView ws (srcR r)) := by
  rw [srcsView_srcR]
  split
  · exact domF_zero _ _
  · exact hregv r (by omega) hr

/-! ## 4. The register-write and boundary labels -/

/-- The memory effect of `regWL rd srcs ++ [LInstr]`. -/
def regWE (ws : PState) (rd : Nat) (srcs : List Dsrc) : PState :=
  if rd = 0 then ws else { ws with wRegv := insert ws.wRegv rd (srcsView ws srcs) }

def instrE (ws : PState) : PState := { ws with wLdv := 0, wRmw := none, wIfv := 0 }

theorem foldl_regWL (ws : PState) (rd : Nat) (srcs : List Dsrc) :
    (regWL rd srcs ++ [LInstr]).foldl afEff ws = instrE (regWE ws rd srcs) := by
  unfold regWL regWE
  by_cases h : rd = 0
  · simp [h, afEff, instrE]
  · simp [h, afEff, instrE]

theorem regWL_af (rd : Nat) (srcs : List Dsrc) : ∀ l ∈ regWL rd srcs ++ [LInstr], afOk l = true := by
  intro l hl
  unfold regWL at hl
  split at hl <;> simp at hl <;> rcases hl with rfl | rfl <;> rfl

theorem regWL_ne (rd : Nat) (srcs : List Dsrc) : regWL rd srcs ++ [LInstr] ≠ [] := by simp

theorem regv_regWE (ws : PState) (rd : Nat) (srcs : List Dsrc) (r : Nat) :
    regv (regWE ws rd srcs) r = if rd ≠ 0 ∧ r = rd then srcsView ws srcs else regv ws r := by
  unfold regWE regv
  by_cases h0 : rd = 0
  · simp [h0]
  · simp only [h0, if_false, ne_eq, not_false_eq_true, true_and]
    by_cases hr : r = rd
    · subst hr; simp [lookupInsert]
    · rw [if_neg hr]; simp only [lookupInsertNe (Ne.symm hr)]

theorem regWE_fields (ws : PState) (rd : Nat) (srcs : List Dsrc) :
    (regWE ws rd srcs).wVrOld = ws.wVrOld ∧ (regWE ws rd srcs).wVwOld = ws.wVwOld ∧
    (regWE ws rd srcs).wVrNew = ws.wVrNew ∧ (regWE ws rd srcs).wVwNew = ws.wVwNew ∧
    (regWE ws rd srcs).wVcap = ws.wVcap ∧ (regWE ws rd srcs).wFwd = ws.wFwd ∧
    (∀ x, coh (regWE ws rd srcs) x = coh ws x) ∧ (regWE ws rd srcs).wLdv = ws.wLdv := by
  unfold regWE; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩

/-- An instruction whose labels are all answer-free, over any non-empty label list. -/
theorem solo_go1' (img : Image) (M : List PMsg) (i : Nat) (lp : LP) (ws : PState) (prom : GSet Nat)
    (ins : Instr) (regs' : List Nat) (pc' : Nat) (labs : List PLabel) (hne : labs ≠ [])
    (hq : lp.q = []) (hi : lp.prog[lp.pc]? = some ins)
    (hn : ∀ l, instrNext lp.prog.length lp ins l = go1 lp regs' pc' labs l)
    (hok : ∀ l ∈ labs, afOk l = true) :
    soloSteps litStep img M i (lp, ws, prom) (labs.map (fun l => (l, none)))
      ({ lp with regs := regs', pc := pc', q := [] }, labs.foldl afEff ws, prom) := by
  cases labs with
  | nil => exact absurd rfl hne
  | cons l0 rest => exact solo_go1 img M i lp ws prom ins regs' pc' l0 rest hq hi (hn l0) hok

/-! ## 5. Transport over a step without memory operations -/

theorem fwdOk_mono {X : Exec} {h nF n n' x : Nat} {o : Option (Nat × Nat)} (hfo : fwdOk X h nF n x o)
    (hnn : n ≤ n')
    (hns : ∀ j, n ≤ j → j < n' → (X.sk (h, j)).kind.isStore = true → touches (X.ev (h, j)) x = false) :
    fwdOk X h nF n' x o := by
  match o, hfo with
  | none, hfo =>
    intro j hj hs
    rcases Nat.lt_or_ge j n with h1 | h1
    · exact hfo j h1 hs
    · exact hns j h1 hj hs
  | some (tf, vf), ⟨j, hj, hs, ht, hl, htf, hv⟩ =>
    refine ⟨j, by omega, hs, ht, fun j2 h1 h2 hs2 => ?_, htf,
      fun j' h1 h2 hl' htj hr => hv j' (by omega) h2 hl' htj hr⟩
    rcases Nat.lt_or_ge j2 n with h3 | h3
    · exact hl j2 h1 h3 hs2
    · exact hns j2 h3 h2 hs2

/-- Transport of `SimInv` over a step that emits no memory operation. -/
theorem inv_nomem {T : Test} {X : Exec} {ν : Val} {h : Nat} {sf s s' : SSt} {lp lp' : LP} {ws ws' : PState}
    {prom : GSet Nat} (hinv : SimInv T X ν h sf s lp ws prom)
    (hwf : SymWf s') (hfut : Future s' sf) (hn : s.evs.length ≤ s'.evs.length)
    (hnm : ∀ j, s.evs.length ≤ j → j < s'.evs.length → (X.sk (h, j)).kind.isMem = false)
    (hprog : lp'.prog = T.prog h) (hpc : lp'.pc = s'.pc) (hq : lp'.q = []) (hlen : lp'.regs.length = 32)
    (hregEq : ∀ r, lp'.rd r = (s'.rd r).1.eval ν) (hregLt : ∀ r, (s'.rd r).1.eval ν < two64)
    (hregv : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j)) (· ∈ (s'.rd r).2) (regv ws' r))
    (hvro : ws'.wVrOld = ws.wVrOld) (hvwo : ws'.wVwOld = ws.wVwOld)
    (hvrn : ∀ j, s'.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isLoad = true →
      ws'.wVrNew ≤ vo X (h, j))
    (hvwn : ∀ j, s'.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isStore = true →
      ws'.wVwNew < vo X (h, j))
    (hvcap : ∀ j, s'.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isStore = true →
      ws'.wVcap < vo X (h, j))
    (hcoh : ∀ x : Int, coh ws' x = coh ws x) (hfwd : ws'.wFwd = ws.wFwd) (hldv : ws'.wLdv = 0)
    (hifv : ws'.wIfv = 0) : SimInv T X ν h sf s' lp' ws' prom := by
  have hst : ∀ j, s.evs.length ≤ j → j < s'.evs.length → (X.sk (h, j)).kind.isStore = false := by
    intro j h1 h2
    cases hs : (X.sk (h, j)).kind.isStore
    · rfl
    · have := Kind.isMem_of_isStore _ hs; rw [hnm j h1 h2] at this; cases this
  refine ⟨hwf, hfut, hprog, hpc, hq, hlen, hregEq, hregLt, hregv, ?_, ?_, hvrn, hvwn, hvcap, ?_, ?_, ?_, hldv,
    hifv, ?_⟩
  · rw [hvro]; exact domF_mono hinv.vrOld (fun j hj => ⟨by omega, hj.2⟩)
  · rw [hvwo]; exact domF_mono hinv.vwOld (fun j hj => ⟨by omega, hj.2⟩)
  · intro x j h1 h2 h3 h4; rw [hcoh]; exact hinv.coh1 x j (by omega) h2 h3 h4
  · intro x j h1 h2 h3 h4 w hw hww hle; rw [hcoh] at hle; exact hinv.coh2 x j (by omega) h2 h3 h4 w hw hww hle
  · intro x; rw [hfwd]
    exact fwdOk_mono (hinv.fwd x) hn (fun j h1 h2 hs => by rw [hst j h1 h2] at hs; cases hs)
  · intro t
    rw [hinv.prom t]
    constructor
    · rintro ⟨j, h1, h2, h3, h4⟩
      refine ⟨j, ?_, h2, h3, h4⟩
      rcases Nat.lt_or_ge j s'.evs.length with h5 | h5
      · rw [hst j h1 h5] at h3; cases h3
      · exact h5
    · rintro ⟨j, h1, h2, h3, h4⟩
      exact ⟨j, by omega, h2, h3, h4⟩

end Weak.Prom.Cmp
