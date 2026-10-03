/-
**THE TRACE-LEVEL NONINTERFERENCE THEOREM, at a generic application** (NI
M2-W4; design of record `claude-notes/projects/noninterference.md`, "M2-W2
design (2026-10-02)" §1/§4, rulings O2/O4/O6, "M2-W2c as landed", "M2-W2d as
landed").

* §1 `xv6NiPhi g h := ∃ F, niOk h F ∧ niOneShot h F ∧ ∀ q, NiClassLaw q
  (utrace q h F)` (O6: the filing is part of the run's witness; `niOneShot`,
  W2d's fact, is what makes an origin filing honest: every filing spent a
  distinct claim minted in `h` before its enter -- a round's at the exit it
  cites, an origin's at a fork exit or a power-on -- so a round's resume
  cannot be re-filed as a fresh origin without a minted origin claim).
* §2 THE NI LEDGER beside the application's: `niLedgerR A c γ h := A.R c h ∗
  niR γ h` (W2c's composition, at W2d's claim authority `γ`), and its laws --
  the power step (a power-on mints initproc's claim, `niR_powerOn`, yielded
  as the era's origin ticket), the return path, the two UART permits, and
  THE TWO HOOK DISCHARGES (`niLedger_exit`: an exit mints its round claim
  and, at a fork, the child's origin claim, `niR_exit`; `niLedger_enter`: an
  enter is FILED spending its claim, `niR_enter`).
* §3 **`xv6NiAppAdequacy`**: `SystemAdequacy.xv6PowerAdequacyGenU` at THE NI
  RECORD -- the fixed part `A.fixed × GName` (the application's, and the
  claim authority's name, born by `niR_alloc` beside the application's
  birth: `niBirth`), `uFit := niFit` (`hUf := fun _ _ h => h`), the claim
  slots `roundClaim γ`/`niExitMint γ`/`niOriginTicket γ` (fork law
  `niExitMint_fork`), the trace slot `obsLedgerAt (niLedgerR A c γ)`,
  `phi := xv6NiPhi` (`Hphi` from `obsLedgerAt_phi`, `niR_pure` and
  `NiTrace.niOk_classLaw`).  (NI M2-X1) The record's evidence slot is
  BLIND for now -- `uEvid := ⌜∃ c, niFitEv ox e c⌝`, dropped by the entry
  hook (`uenterHook_dropEv`) -- and the registration `emp` (the power hook
  yields an empty ticket); M2-X1 interim: X3 puts the ledger's `niEvid γe`
  / `niEraTok γe` / `niEraAnchor γe` there.

The closed instance (`USER` discharged: `ProofUser`) and the two corollaries
are `LinkNiAdequacy` (only a `Link` file may import a `Proof` file).

## Honest scope (see `NiTrace`'s header for the trace side)

1. The class is {exit, getpid, uptime}; every other ecall's enter is free.
2. Origins are honest by W2d's one-shot claims (`niOneShot` in the
   conclusion): the filing's origin claims are fork exits' or power-ons',
   each spent once.  That an origin's FIRST KEY is the forked child's is not
   stated (the claim names the parent's fork exit, not the child's key).
3. The syscall mask is carried per filing (`NiTrace` scope 3); getpid's
   answer is the incarnation's pid (W2d's pid row); the uptime reading IS
   the tick (O5).
-/
import Xv6.NiTrace
import Xv6.AppLaws

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL
open Iris.ProgramLogic Language.Notation PrimStep

set_option linter.unusedSectionVars false

/-! ## §1 THE CONCLUSION (ruling O6) -/

/-- **THE NI CONCLUSION** of a run ending at history `h`: the ledger's filing
of `h` exists, it is one-shot (W2d), and every incarnation's trace obeys the
class law. -/
def xv6NiPhi (_ : GState) (h : List Obs) : Prop :=
  ∃ F, niOk h F ∧ niOneShot h F ∧ ∀ q, NiClassLaw q (utrace q h F)

/-- The ledger's facts give the conclusion (`NiTrace.niOk_classLaw`). -/
theorem xv6NiPhi_of {g : GState} {h : List Obs} {F : List NiEntry} (hF : niOk h F)
    (h1 : niOneShot h F) : xv6NiPhi g h :=
  ⟨F, hF, h1, niOk_classLaw hF⟩

/-! ## §2 THE NI LEDGER beside the application's -/

section ledger
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF] [Xv6G GF] [WchGpre GF]
  [CtokG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF]
  [IcboxG GF] [SleepLockG GF] [BcacheG GF] [OffboxG GF] [OffboxBoxG GF] [FileG GF]

/-- **The trace slot's ledger**: the application's and the NI filing (at the
claim authority `γ`), side by side (W2 design §1: a second conjunct,
`AppLaws` byte-identical). -/
def niLedgerR (A : Xv6App GF) (c : A.fixed) (γ : GName) (h : List Obs) : IProp GF :=
  iprop(A.R c h ∗ niR γ h)

instance niLedgerR_timeless (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] (c : A.fixed) (γ : GName)
    (h : List Obs) : Timeless (niLedgerR A c γ h) := by
  unfold niLedgerR; infer_instance

theorem isUEnter_of_uexit {e : Obs} (he : isUExit e = true) : isUEnter e = false := by
  cases e <;> simp_all [isUExit, isUEnter]

/-- **THE BIRTH**: the application's, and the claim authority's name
(`niR_alloc`), kept in the fixed part; the ledger's empty history goes to the
trace slot's part. -/
theorem niBirth (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] (γd γsw γreg γst : GName) :
    ⊢@{IProp GF} |==> ∃ p : A.fixed × GName, ⌜A.born γd γsw γreg γst p.1⌝ ∗ A.cls p.1 ∗
      iprop(A.cl p.1 ∗ niR p.2 []) := by
  imod AL.al_birth γd γsw γreg γst with ⟨%c, %hb, Hs, Hc⟩
  imod niR_alloc (GF := GF) with ⟨%γ, Hn⟩
  imodintro
  iexists (c, γ)
  isplitr
  · ipureintro; exact hb
  iframe Hs Hc Hn

/-- The ledger at the empty history, out of the birth's trace-slot part. -/
theorem niLedger_R0 (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] (c : A.fixed) (γ : GName) :
    iprop(A.cl c ∗ niR γ []) ⊢@{IProp GF} |==> niLedgerR A c γ [] := by
  unfold niLedgerR
  iintro ⟨Hc, Hn⟩
  imod AL.al_R0 c $$ Hc with HR
  imodintro
  iframe HR Hn

/-- The power step: the application's; the filing blind at a power loss, and
at a power-on minting initproc's claim, yielded as the era's origin ticket
beside the application's turn. -/
theorem niLedger_pow (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] (c : A.fixed) (γ : GName)
    (h : List Obs) (on : Bool) (dk : Nat → BitVec 8) (hs : traceShape h on) :
    niLedgerR A c γ h ⊢@{IProp GF} |==> (niLedgerR A c γ (h ++ [powerEv on]) ∗
      (if on then iprop(emp)
       else iprop(A.cons c (obsBoots h + 1) [] ⟨[], [], [], none⟩ ∗
         -- M2-X1 interim: X3 mints the era's registration ticket here (`emp`)
         iprop(A.turn c (obsBoots h + 1) ∗ niOriginTicket γ ∗ emp)))) := by
  unfold niLedgerR
  have hp := AL.al_pow c h on dk hs
  cases on
  · simp only [Bool.false_eq_true, ↓reduceIte, powerEv] at hp ⊢
    iintro ⟨HR, Hn⟩
    imod hp $$ HR with ⟨HR, Hcons, Hturn⟩
    imod niR_powerOn γ h $$ Hn with ⟨Hn, Hi⟩
    imodintro
    iframe HR Hn Hcons Hturn
    isplitl [Hi]
    · iapply initClaim_ticket $$ Hi
    · iempintro
  · simp only [↓reduceIte, powerEv] at hp ⊢
    iintro ⟨HR, Hn⟩
    imod hp $$ HR with ⟨HR, -⟩
    imodintro
    isplitl [HR Hn]
    · iframe HR
      iapply niR_snoc γ h .powerOff rfl $$ Hn
    · iempintro

/-- The return path: the application's own step, the filing framed. -/
theorem niLedger_back (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] (c : A.fixed) (γ : GName)
    (h : List Obs) :
    ⊢@{IProp GF} niLedgerR A c γ (h ++ [Obs.powerOn]) -∗ A.turn' c (obsBoots h + 1) ==∗
      niLedgerR A c γ (h ++ [Obs.powerOn]) ∗ A.turn'' c (obsBoots h + 1) := by
  unfold niLedgerR
  iintro ⟨HR, Hn⟩ Ht
  imod AL.al_back c h $$ HR Ht with ⟨HR, Ht⟩
  imodintro
  iframe HR Hn Ht

/-- **THE EXIT HOOK'S DISCHARGE, THE MINT**: a user exit steps the
application's ledger (`al_user`) and mints the exit's round claim and, at a
fork, the child's origin claim (`niR_exit`). -/
theorem niLedger_exit (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] (c : A.fixed) (γ : GName)
    (h : List Obs) (e : Obs) (he : isUExit e = true) :
    niLedgerR A c γ h ⊢@{IProp GF}
      |==> (niLedgerR A c γ (h ++ [e]) ∗ roundClaim γ h.length ∗ niExitMint γ h.length e) := by
  unfold niLedgerR
  iintro ⟨HR, Hn⟩
  imod AL.al_user c h e (isUser_of_uexit he) $$ HR with HR
  imod niR_exit γ h e he $$ Hn with ⟨Hn, Hr, Hx⟩
  imodintro
  iframe HR Hn Hr Hx

/-- **THE ENTER HOOK'S DISCHARGE, THE FILING**: a user enter with the
kernel's evidence (`niFit`), the cited receipt's reading and the claim it
spends (`niSpend`: the cited exit's round claim, or an origin ticket) is
filed (`niR_enter`); the application's ledger steps by `al_user`. -/
theorem niLedger_enter (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] (c : A.fixed) (γ : GName)
    (h : List Obs) (e : Obs) (ox : Option (Nat × Obs)) (he : isUEnter e = true) (hf : niFit ox e)
    (hv : ∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) :
    uClaimForRaw (roundClaim γ) (niOriginTicket γ) ox ∗ niLedgerR A c γ h ⊢@{IProp GF}
      |==> niLedgerR A c γ (h ++ [e]) := by
  unfold niLedgerR
  iintro ⟨Hcl, HR, Hn⟩
  imod AL.al_user c h e (isUser_of_uenter he) $$ HR with HR
  imod niR_enter γ h e ox he hf hv $$ [Hcl Hn] with Hn
  · unfold niSpend; iframe Hcl Hn
  imodintro
  iframe HR Hn

/-- The drain at a port: the application's, the filing blind. -/
theorem niLedger_tx (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] [MachGS hlc GF] [Fscfg]
    (c : A.fixed) (γn : GName) (i : UartId) (γ : UartNames)
    (hm : MachFixedGS.mono (hlc := hlc) (GF := GF) = MachGpreS.mono_pre (hlc := hlc))
    (hu : i = .uart0 → fscUart = γ) :
    ⊢@{IProp GF} iprop(□ ∀ (h : List Obs) (b : BitVec 8) (u u' : UartState) (ho : List Obs)
        (H : ConsHist),
      ⌜Uart.txPop u = some (b, u') ∧ Uart.loopback u = false ∧ traceShape h true ∧
        obsWire i (openSeg h) = u.wire ∧ u.wire = u.out ∧
        obsBoots h = genId (hlc := hlc) (GF := GF) + 1 ∧
        ho <+: h ∧ H.chAcc = Uart.acc u⌝ -∗
      cresAt (A.cons c) i (genId (hlc := hlc) (GF := GF) + 1) ho H -∗ uartGhosts γ u' -∗
        niLedgerR A c γn h
        ={(⊤ \ ↑(uartN i)) \ ↑obsN}=∗
      cresAt (A.cons c) i (genId (hlc := hlc) (GF := GF) + 1) ho H ∗ uartGhosts γ u' ∗
        niLedgerR A c γn (h ++ [Obs.dev (.uartOut i b)])) := by
  have Htx := AL.al_tx c i γ hm hu
  unfold niLedgerR
  ihave #Ht := Htx
  imodintro
  iintro %h %b %u %u' %ho %H %hp Hc HG ⟨HR, Hn⟩
  imod Ht $$ %h %b %u %u' %ho %H %hp Hc HG HR with ⟨Hc, HG, HR⟩
  imodintro
  iframe Hc HG HR
  iapply niR_snoc γn h _ rfl $$ Hn

/-- The arrival at a port: the application's, the filing blind. -/
theorem niLedger_rx (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A] [MachGS hlc GF] [Fscfg]
    (c : A.fixed) (γn : GName) (i : UartId) (γ : UartNames)
    (hm : MachFixedGS.mono (hlc := hlc) (GF := GF) = MachGpreS.mono_pre (hlc := hlc))
    (hu : i = .uart0 → fscUart = γ) :
    ⊢@{IProp GF} iprop(□ ∀ (h : List Obs) (b : BitVec 8) (u u' : UartState),
      ⌜u.rx.length < Uart.fifoDepth ∧ u' = Uart.accept u b ∧ traceShape h true ∧
        obsBoots h = genId (hlc := hlc) (GF := GF) + 1⌝ -∗
      uartGhosts γ u' -∗ niLedgerR A c γn h ={(⊤ \ ↑(uartN i)) \ ↑obsN}=∗
      uartGhosts γ u' ∗ niLedgerR A c γn (h ++ [Obs.dev (.uartIn i b)]) ∗
        A.tag c (h ++ [Obs.dev (.uartIn i b)])) := by
  have Hrx := AL.al_rx c i γ hm hu
  unfold niLedgerR
  ihave #Hr := Hrx
  imodintro
  iintro %h %b %u %u' %hp HG ⟨HR, Hn⟩
  imod Hr $$ %h %b %u %u' %hp HG HR with ⟨HG, HR, Ht⟩
  imodintro
  iframe HG HR Ht
  iapply niR_snoc γn h _ rfl $$ Hn

end ledger

/-! ## §3 THE NI THEOREM, at a generic application -/

section gen
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF] [Xv6G GF] [WchGpre GF]
  [CtokG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF]
  [IcboxG GF] [SleepLockG GF] [BcacheG GF] [OffboxG GF] [OffboxBoxG GF] [FileG GF]

/-- **THE NI APPLICATION THEOREM**: an application with its laws, its claim
at the boot image, from a powered-off, never-booted machine with a
well-formed image -- every reachable configuration is reducible, and the
run's trace is filed by the NI ledger, one-shot, with every incarnation's
trace obeying the class law.  `xv6AppAdequacy`'s proof at THE NI RECORD
(fixed part `A.fixed × GName`, `uFit := niFit`, the ledger's claims, the
trace slot `obsLedgerAt (niLedgerR A c γ)`). -/
theorem xv6NiAppAdequacy (g : GState) (sb : FsSb) (nib : Nat) (cov : ExtTreeSet Nat compare)
    (A : Xv6App GF) [AL : Xv6AppLaws (hlc := hlc) A]
    (Happ_init : ∀ c : A.fixed, A.cls c ⊢@{IProp GF} |==> ∃ r : A.names, ⌜A.okc c r⌝ ∗
      A.pred c r (absView (imgState (fsBlocks (diskOf g.m.devs)) sb nib).fssInodes))
    (Hgen0 : g.gen = 0) (Hpow0 : g.pow = false)
    (Himg : fsBootImageWf (diskOf g.m.devs) XV6_DISK_BYTES sb nib cov)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ xv6NiPhi g2 κs := by
  refine xv6PowerAdequacyGenU (hlc := hlc) (GF := GF) g sb nib cov
    -- THE FIXED PART: the application's, and the claim authority's name
    (A.fixed × GName) (fun p => A.cls p.1) (fun p => iprop(A.cl p.1 ∗ niR p.2 []))
    (fun γd γsw γreg γst p => A.born γd γsw γreg γst p.1) (niBirth A)
    A.names (fun p => A.pred p.1) (fun p => A.boot p.1) (fun p => A.okc p.1) (fun p => A.ifc p.1)
    (fun p => A.turn p.1) (fun p => A.turn' p.1) (fun p => A.turn'' p.1) (fun p => A.iturn p.1)
    (fun p => A.tk p.1) (fun p => A.hk p.1) (fun p k => AL.al_found p.1 k)
    (fun p => A.ok p.1) (fun p k r => AL.al_boot_ok p.1 k r)
    (fun p k hm hb => AL.al_merge p.1 k hm hb)
    (fun p k => AL.al_sync_run p.1 k)
    (fun p gen γd γsw γreg γst hb => AL.al_xfer p.1 gen γd γsw γreg γst hb) (fun p => Happ_init p.1)
    -- THE NI RECORD: the enter's justification is the filing's evidence, the
    -- claim slots the ledger's
    niFit (fun _ _ h => h)
    (fun p => roundClaim p.2) (fun p => niExitMint p.2) (fun p => niOriginTicket p.2)
    (fun p i x h => niExitMint_fork p.2 i x h)
    -- THE NI RECORD'S EVIDENCE AND REGISTRATION, BLIND (NI M2-X1 interim: X3
    -- replaces them by the ledger's `niEvid γe` / `niEraTok γe` /
    -- `niEraAnchor γe`): the evidence is the pure fit at some citation, the
    -- registration `emp`
    (fun _ ox e => iprop(⌜∃ cc, niFitEv ox e cc⌝)) (fun _ _ _ => inferInstance)
    (fun _ _ => iprop(emp)) (fun _ _ _ => iprop(emp)) (fun _ _ _ => inferInstance)
    (fun _ _ _ => BIUpdate.intro)
    (fun _ _ _ _ cc h => BI.pure_intro ⟨cc, h⟩)
    (fun _ _ h => BI.pure_intro ⟨none, rfl, h⟩)
    (fun γobs p => obsLedgerAt (niLedgerR A p.1 p.2) γobs)
    ?_
    ?_
    (fun γobs p => obsLedgerAt_alloc_cl (niLedgerR A p.1 p.2) γobs _ (niLedger_R0 A p.1 p.2))
    (fun γd γobs p h on dk hs =>
      obsLedgerAt_step (niLedgerR A p.1 p.2) (A.cons p.1)
        (fun k => iprop(A.turn p.1 k ∗ niOriginTicket p.2 ∗ emp)) (niLedger_pow A p.1 p.2) XV6_DISK_BYTES
        γd γobs h on dk hs)
    (fun γobs p h => obsLedgerAt_back (niLedgerR A p.1 p.2) _ _ (h ++ [Obs.powerOn])
      (niLedger_back A p.1 p.2 h) γobs)
    -- THE TWO HOOKS: the exit MINTS its claims, the enter is FILED spending one
    (fun γobs p h e he => obsLedgerAt_uexitM (niLedgerR A p.1 p.2) (roundClaim p.2) (niExitMint p.2)
      (niLedger_exit A p.1 p.2) γobs h e he)
    (fun γobs p h e ox he hf hv => uenterHook_dropEv _ _ _ _ _
      (obsLedgerAt_uenterS (niLedgerR A p.1 p.2) niFit (roundClaim p.2)
        (niOriginTicket p.2) (niLedger_enter A p.1 p.2) γobs h e ox he hf hv))
    ?_
    xv6NiPhi
    ?_
    Hgen0 Hpow0 Himg n κs t2 g2 hsteps
  · intro Hinv γgen γstart γreg γd γsw γobs γhist p T
    have H := AL.al_programs (F := xv6FixedGSU A.names (fun p => A.pred p.1) (fun p => A.okc p.1) cov
        sb.sbLogstart (A.ifc p.1) Hinv γgen γstart γreg γd γsw γobs γhist p T
        (obsLedgerAt (niLedgerR A p.1 p.2) γobs) (A.tk p.1) (A.hk p.1) niFit (roundClaim p.2)
        (niExitMint p.2) (niOriginTicket p.2)
        (fun ox e => iprop(⌜∃ cc, niFitEv ox e cc⌝)) (fun _ _ => inferInstance) (fun _ => iprop(emp))
        (fun _ _ => iprop(emp)) (fun _ _ => inferInstance))
        p.1 rfl rfl rfl rfl rfl rfl rfl
    intro E gen cP cI _ _ _ _ _ _ r
    exact H E gen cP cI r
  · intro Hinv γgen γstart γreg γd γsw γobs γhist p T
    have H := AL.al_echo (F := xv6FixedGSU A.names (fun p => A.pred p.1) (fun p => A.okc p.1) cov
        sb.sbLogstart (A.ifc p.1) Hinv γgen γstart γreg γd γsw γobs γhist p T
        (obsLedgerAt (niLedgerR A p.1 p.2) γobs) (A.tk p.1) (A.hk p.1) niFit (roundClaim p.2)
        (niExitMint p.2) (niOriginTicket p.2)
        (fun ox e => iprop(⌜∃ cc, niFitEv ox e cc⌝)) (fun _ _ => inferInstance) (fun _ => iprop(emp))
        (fun _ _ => iprop(emp)) (fun _ _ => inferInstance))
        p.1 rfl rfl rfl rfl rfl rfl
    intro E gen cP cI
    exact H E gen cP cI
  · intro Hinv γgen γstart γreg γd γsw γobs γhist p T
    letI : MachFixedGS hlc GF := xv6FixedGSU A.names (fun p => A.pred p.1) (fun p => A.okc p.1) cov
        sb.sbLogstart (A.ifc p.1) Hinv γgen γstart γreg γd γsw γobs γhist p T
        (obsLedgerAt (niLedgerR A p.1 p.2) γobs) (A.tk p.1) (A.hk p.1) niFit (roundClaim p.2)
        (niExitMint p.2) (niOriginTicket p.2)
        (fun ox e => iprop(⌜∃ cc, niFitEv ox e cc⌝)) (fun _ _ => inferInstance) (fun _ => iprop(emp))
        (fun _ _ => iprop(emp)) (fun _ _ => inferInstance)
    intro E gen cP cI Fc i γ hu
    letI : MachGS hlc GF := MachGS.ofEra E gen cP cI
    exact uartObsPermit_ledger i (niLedgerR A p.1 p.2) (A.tag p.1) (A.cons p.1) γ rfl rfl rfl
      (niLedger_tx A p.1 p.2 i γ rfl hu) (niLedger_rx A p.1 p.2 i γ rfl hu)
  · intro Hinv γgen γstart γreg γd γsw γobs γhist p T g' h
    iintro ⟨-, Ha, -, -, HP⟩
    iapply obsLedgerAt_phi (niLedgerR A p.1 p.2) (xv6NiPhi g') (fun h => by
      unfold niLedgerR
      iintro ⟨-, Hn⟩
      ihave %hF := niR_pure p.2 h $$ Hn
      ipureintro
      obtain ⟨F, hF, h1⟩ := hF
      exact xv6NiPhi_of hF h1) γobs h
    iframe Ha HP

end gen

end Xv6
