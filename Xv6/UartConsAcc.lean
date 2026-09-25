/-
The console boundary's three EVENT ACCESSORS on the port's claim, with the
console port's invariant opened here (the Rocq `WpUart.uart_inv_cons_open`,
`uart_inv_cons_close`, `uart_inv_cons_read`, redesign R2).  The port's body
is timeless, so each is one `|={⊤}=>` with no machine step: the form
consoleintr uses to open and close an arm (holding the arm's and the log
mark's halves off the PLIC payload) and consoleread uses at its final
release (holding the delivered and log-mirror halves off the console ring).

* `uartInv_consOpen` -- `evOpen h c cs`: the kernel proves the event's
  premises from its OWN state -- "no arm is in progress" off its arm half,
  the order fact off the log's mark and `logOk`'s chain, the wire rider off
  the transmitted-prefix bound -- fires the application's link, and the two
  arm halves advance with the history;
* `uartInv_consClose` -- `evClose`: the entry filed is what actually went
  out (`take j cs`), the log's mark, mirror and mono-list move, the arm
  halves return to `none`, and the order fact comes back for the console's
  own log;
* `uartInv_consRead` -- `evRead ws`: the delivered sequence moves.
-/
import Xv6.UartInv

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

theorem uartLogm_agree (γ : UartNames) (q1 q2 : Qp) (L1 L2 : List LogEntry) :
    uartLogm (GF := GF) γ q1 L1 ∗ uartLogm γ q2 L2 ⊢ ⌜L1 = L2⌝ ∗ uartLogm γ q1 L1 ∗ uartLogm γ q2 L2 := by
  unfold uartLogm
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ.logm _ _ _ _ $$ H1 H2
  iframe H1 H2
  ipureintro; exact h

theorem uartLogm_update (γ : UartNames) (L1 L2 L' : List LogEntry) :
    uartLogm (GF := GF) γ (1 : Qp).half L1 ∗ uartLogm γ (1 : Qp).half L2 ⊢
      |==> (uartLogm γ (1 : Qp).half L' ∗ uartLogm γ (1 : Qp).half L') := by
  unfold uartLogm
  iintro ⟨H1, H2⟩
  iapply ghost_var_update_halves L' γ.logm L1 L2 $$ H1 H2

theorem uartDeliv_agree (γ : UartNames) (q1 q2 : Qp) (d1 d2 : List (List Obs × BitVec 8)) :
    uartDeliv (GF := GF) γ q1 d1 ∗ uartDeliv γ q2 d2 ⊢ ⌜d1 = d2⌝ ∗ uartDeliv γ q1 d1 ∗ uartDeliv γ q2 d2 := by
  unfold uartDeliv
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ.deliv _ _ _ _ $$ H1 H2
  iframe H1 H2
  ipureintro; exact h

theorem uartDeliv_update (γ : UartNames) (d1 d2 d' : List (List Obs × BitVec 8)) :
    uartDeliv (GF := GF) γ (1 : Qp).half d1 ∗ uartDeliv γ (1 : Qp).half d2 ⊢
      |==> (uartDeliv γ (1 : Qp).half d' ∗ uartDeliv γ (1 : Qp).half d') := by
  unfold uartDeliv
  iintro ⟨H1, H2⟩
  iapply ghost_var_update_halves d' γ.deliv d1 d2 $$ H1 H2

/-- The log's top after an append is the appended entry's history. -/
theorem logTop_snoc (L : List LogEntry) (e : LogEntry) : logTop (L ++ [e]) = some (leHist e) := by
  unfold logTop; rw [clTop_snoc]; rfl

/-- OPENING AN ARM (Rocq `uart_inv_cons_open`). -/
theorem uartInv_consOpen (γ : UartNames) (h : List Obs) (c : BitVec 8) (cs : List (BitVec 8))
    (hg : Option (List Obs)) (Φ : IProp GF)
    (hx : ohistExt hg h) (hends : obsEndsIn .uart0 h c) (hecho : consEcho c cs) :
    uartInv .uart0 γ ∗ outLb γ (obsWire .uart0 (openSeg h)) ∗ logHi γ (1 : Qp).half hg ∗
      uartArm γ (1 : Qp).half none ∗ consLink .uart0 (genId (hlc := hlc) (GF := GF) + 1) (.evOpen h c cs) Φ ⊢
      |={⊤}=> logHi γ (1 : Qp).half hg ∗ uartArm γ (1 : Qp).half (some ((h, c, cs), 0)) ∗ Φ := by
  unfold uartInv devInvR
  iintro ⟨#Hinv, #Hwlb, Hhi, Hmine, HΨ⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HB⟩
  icases uartBody_parts .uart0 γ u $$ HB with ⟨Hsent, Hout, Htx, Hdlab, Hcol, Hcl⟩
  unfold consClaimAt
  icases Hcl with ⟨%o, %H, #Hlb, Hres, Hhi0, Hdv, Hau, Hlm0, Harm, %hacc0, %hok⟩
  -- the log's mark: the caller's half names the claim's own top
  icases logHi_agree γ _ _ _ _ $$ [Hhi Hhi0] with ⟨%hagr, Hhi, Hhi0⟩
  · iframe Hhi Hhi0
  -- no arm is in progress: the caller's half says so
  icases uartArm_agree γ _ _ _ _ $$ [Hmine Harm] with ⟨%hnone0, Hmine, Harm⟩
  · iframe Hmine Harm
  have hnone : H.chArm = none := hnone0.symm
  -- the order fact, off the mark and the log's chain
  have hbelow : ∀ e, e ∈ H.chLog → histExt (leHist e) h := by
    refine clLogOk_last_ext _ h hok.1 (fun el hel => ?_)
    rw [hagr] at hx
    unfold logTop at hx
    rw [hel] at hx
    exact hx
  -- the wire rider, off the transmitted-prefix bound
  icases outLb_prefix γ u _ $$ [Hout Hwlb] with ⟨%hpre, Hout⟩
  · iframe Hout Hwlb
  have hwire : obsWire .uart0 (openSeg h) <+: H.chAcc := by
    rw [hacc0]; unfold Uart.acc; exact hpre.trans (List.prefix_append _ _)
  have hev : consEvOk H (.evOpen h c cs) := ⟨hnone, hends, hecho, hbelow, hwire⟩
  -- fire the event
  unfold consLink
  imod HΨ $$ %o %H Hlb Hres %hok %hev with ⟨%o', #Hlb', Hres', HΦ⟩
  -- and move both halves with the history
  imod (uartArm_update γ _ _ (some ((h, c, cs), 0))) $$ [Hmine Harm] with ⟨Hmine, Harm⟩
  · iframe Hmine Harm
  have hok' := consHistOk_step H (.evOpen h c cs) hok hev
  ihave Hc := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol Hlb' Hres' Hhi0 Hdv Hau Hlm0 Harm]
  case' _ =>
    inext
    iexists u
    iframe Hfrag
    iapply uartBody_intro .uart0 γ u
    iframe Hsent Hout Htx Hdlab Hcol
    unfold consClaimAt
    iexists o', consStep H (.evOpen h c cs)
    simp only [consStep] at hok' ⊢
    iframe Hlb' Hres' Hhi0 Hdv Hau Hlm0 Harm
    ipureintro; exact ⟨hacc0, hok'⟩
  imod Hc
  imodintro
  iframe Hhi Hmine HΦ

/-- CLOSING THE ARM (Rocq `uart_inv_cons_close`): what is filed is what
actually went out. -/
theorem uartInv_consClose (γ : UartNames) (h : List Obs) (c : BitVec 8) (cs : List (BitVec 8))
    (j : Nat) (hg : Option (List Obs)) (L : List LogEntry) (Φ : IProp GF)
    (hecho : consEcho c (cs.take j)) :
    uartInv .uart0 γ ∗ logHi γ (1 : Qp).half hg ∗ uartLogm γ (1 : Qp).half L ∗
      uartArm γ (1 : Qp).half (some ((h, c, cs), j)) ∗
      consLink .uart0 (genId (hlc := hlc) (GF := GF) + 1) .evClose Φ ⊢
      |={⊤}=> logHi γ (1 : Qp).half (some h) ∗ uartLogm γ (1 : Qp).half (L ++ [(h, c, cs.take j)]) ∗
        ⌜∀ e, e ∈ L → histExt (leHist e) h⌝ ∗ uartArm γ (1 : Qp).half none ∗ Φ := by
  unfold uartInv devInvR
  iintro ⟨#Hinv, Hhi, Hlm, Hmine, HΨ⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HB⟩
  icases uartBody_parts .uart0 γ u $$ HB with ⟨Hsent, Hout, Htx, Hdlab, Hcol, Hcl⟩
  unfold consClaimAt
  icases Hcl with ⟨%o, %H, #Hlb, Hres, Hhi0, Hdv, Hau, Hlm0, Harm, %hacc0, %hok⟩
  icases uartLogm_agree γ _ _ _ _ $$ [Hlm Hlm0] with ⟨%hL, Hlm, Hlm0⟩
  · iframe Hlm Hlm0
  subst hL
  icases uartArm_agree γ _ _ _ _ $$ [Hmine Harm] with ⟨%harm0, Hmine, Harm⟩
  · iframe Hmine Harm
  have harm : H.chArm = some ((h, c, cs), j) := harm0.symm
  have hev : consEvOk H .evClose := ⟨((h, c, cs), j), harm, hecho⟩
  -- the order fact the console's own log needs, carried by the arm
  have hbelow : ∀ e, e ∈ H.chLog → histExt (leHist e) h := by
    have := hok.2
    rw [harm] at this
    exact this.2.2.2.1
  unfold consLink
  imod HΨ $$ %o %H Hlb Hres %hok %hev with ⟨%o', #Hlb', Hres', HΦ⟩
  imod (logHi_update γ _ _ (some h)) $$ [Hhi Hhi0] with ⟨Hhi, Hhi0⟩
  · iframe Hhi Hhi0
  imod (inLogAuth_snoc γ H.chLog (h, c, cs.take j)) $$ Hau with Hau
  imod (uartLogm_update γ _ _ (H.chLog ++ [(h, c, cs.take j)])) $$ [Hlm Hlm0] with ⟨Hlm, Hlm0⟩
  · iframe Hlm Hlm0
  imod (uartArm_update γ _ _ none) $$ [Hmine Harm] with ⟨Hmine, Harm⟩
  · iframe Hmine Harm
  have hok' := consHistOk_step H .evClose hok hev
  have hstep : consStep H .evClose = ⟨H.chAcc, H.chLog ++ [(h, c, cs.take j)], H.chDl, none⟩ := by
    simp only [consStep, harm]
  rw [hstep] at hok'
  ihave Hc := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol Hlb' Hres' Hhi0 Hdv Hau Hlm0 Harm]
  case' _ =>
    inext
    iexists u
    iframe Hfrag
    iapply uartBody_intro .uart0 γ u
    iframe Hsent Hout Htx Hdlab Hcol
    unfold consClaimAt
    iexists o', consStep H .evClose
    rw [hstep]
    simp only [logTop_snoc, leHist]
    iframe Hlb' Hres' Hhi0 Hdv Hau Hlm0 Harm
    ipureintro; exact ⟨hacc0, hok'⟩
  imod Hc
  imodintro
  iframe Hhi Hlm Hmine HΦ
  ipureintro; exact hbelow

/-- THE READ (Rocq `uart_inv_cons_read`): the delivered sequence moves by the
window the read consumed. -/
theorem uartInv_consRead (γ : UartNames) (dv ws : List (List Obs × BitVec 8)) (L : List LogEntry)
    (Φ : IProp GF) (hread : readOk L dv ws) :
    uartInv .uart0 γ ∗ uartDeliv γ (1 : Qp).half dv ∗ uartLogm γ (1 : Qp).half L ∗
      consLink .uart0 (genId (hlc := hlc) (GF := GF) + 1) (.evRead ws) Φ ⊢
      |={⊤}=> uartDeliv γ (1 : Qp).half (dv ++ ws) ∗ uartLogm γ (1 : Qp).half L ∗ Φ := by
  unfold uartInv devInvR
  iintro ⟨#Hinv, Hdv, Hlm, HΨ⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HB⟩
  icases uartBody_parts .uart0 γ u $$ HB with ⟨Hsent, Hout, Htx, Hdlab, Hcol, Hcl⟩
  unfold consClaimAt
  icases Hcl with ⟨%o, %H, #Hlb, Hres, Hhi0, Hdv0, Hau, Hlm0, Harm, %hacc0, %hok⟩
  icases uartLogm_agree γ _ _ _ _ $$ [Hlm Hlm0] with ⟨%hL, Hlm, Hlm0⟩
  · iframe Hlm Hlm0
  subst hL
  icases uartDeliv_agree γ _ _ _ _ $$ [Hdv Hdv0] with ⟨%hD, Hdv, Hdv0⟩
  · iframe Hdv Hdv0
  subst hD
  have hev : consEvOk H (.evRead ws) := hread
  unfold consLink
  imod HΨ $$ %o %H Hlb Hres %hok %hev with ⟨%o', #Hlb', Hres', HΦ⟩
  imod (uartDeliv_update γ _ _ (H.chDl ++ ws)) $$ [Hdv Hdv0] with ⟨Hdv, Hdv0⟩
  · iframe Hdv Hdv0
  have hok' := consHistOk_step H (.evRead ws) hok hev
  ihave Hc := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol Hlb' Hres' Hhi0 Hdv0 Hau Hlm0 Harm]
  case' _ =>
    inext
    iexists u
    iframe Hfrag
    iapply uartBody_intro .uart0 γ u
    iframe Hsent Hout Htx Hdlab Hcol
    unfold consClaimAt
    iexists o', consStep H (.evRead ws)
    simp only [consStep] at hok' ⊢
    iframe Hlb' Hres' Hhi0 Hdv0 Hau Hlm0 Harm
    ipureintro; exact ⟨hacc0, hok'⟩
  imod Hc
  imodintro
  iframe Hdv Hlm HΦ

end

end Xv6
