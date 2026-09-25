/-
The UART invariant (the Rocq `WpUart.uart_inv_body`, the subset the Lean
port carries): per port, the device's mirror (`WpDev.devFrag`) beside the
ghost state the driver proofs reason with --

* `sentAuth`: a mono-list over the ACCEPTED trace `Uart.acc u` (what
  `UartTrace.uartSent` bounds);
* `outAuth`: a mono-list over `u.out`, the transmitted prefix -- the bound a
  token holder mints when it sees THRE, so that its byte provably lands
  (`tx_nil_of_out_prefix`);
* `txAuth`/`txOwn`: ghost-var halves over the accepted trace, the TRANSMIT
  TOKEN (`tx_lock`'s payload);
* `dlabAuth`/`dlabOwn`/`dlabOff`: the divisor latch, a ghost var frozen to a
  persistent `false` once `uartinit` is done;
* the receive column `rxCol`: the bytes that ever entered the FIFO
  (mono-list `rxInAuth`) and the popped count (`rxPopAuth`/`rxTok`, the
  interrupt handler's token); the FIFO is the unpopped suffix.

The chip's own steps (`UartModel.uartRel`) preserve all of it, which is
what lets the device thread run under the invariant (`wpDev_uart_inv`,
from `WpDev.wpDev_localR`).  The driver's MMIO accesses go through the
accessors of `MachCSL.WpSmodeDev`, built here from the invariant
(`lsr_read_au`, `thr_write_au`, ...): each opens the invariant, applies
the register semantics of `UartModel` and re-establishes the ghosts.
-/
import MachCSL.WpSmodeDev
import Xv6.UartTrace
import Xv6.UartModel

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-! ## The ports -/

/-- The MMIO base of port `i` (`UART0`, `UART1` of `kernel/memlayout.h`). -/
def uartBaseAddr (i : UartId) : BitVec 64 := BitVec.ofNat 64 (uartBase i)

/-- `&uarts[i]` (`struct uart` is 40 bytes: `base`, `rx`, `tx_lock`). -/
def uartElt (i : UartId) : BitVec 64 := KA.«uarts» + BitVec.ofNat 64 (40 * i.idx)

/-- `uarts[i].rx`: the console's input hook on port 0, none on port 1. -/
def uartRxHook : UartId → BitVec 64
  | .uart0 => KA.«consoleintr»
  | .uart1 => 0#64

theorem uartDecode (i : UartId) (off : Nat) (hoff : off < 8) :
    devDecode (uartBaseAddr i + BitVec.ofNat 64 off) = some (.uart i, off) := by
  cases i <;> (rcases off with _ | _ | _ | _ | _ | _ | _ | _ | off <;> first | decide | omega)

theorem uartByteOk (i : UartId) (off : Nat) (hoff : off < 8) :
    devByteOk (uartBaseAddr i + BitVec.ofNat 64 off) := by
  cases i <;> (rcases off with _ | _ | _ | _ | _ | _ | _ | _ | off <;> first | decide | omega)

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- `uarts[i].base`, read-only after boot: the port's MMIO base. -/
def uartBaseWord [CurCtx] (i : UartId) : IProp GF :=
  wordPointsTo (uartElt i) 8 DFrac.discard (uartBaseAddr i)

/-- `uarts[i].rx`, read-only after boot. -/
def uartRxWord [CurCtx] (i : UartId) : IProp GF :=
  wordPointsTo (uartElt i + 8#64) 8 DFrac.discard (uartRxHook i)

instance uartBaseWord_persistent [CurCtx] (i : UartId) : Persistent (uartBaseWord (GF := GF) i) := by
  unfold uartBaseWord; infer_instance

instance uartRxWord_persistent [CurCtx] (i : UartId) : Persistent (uartRxWord (GF := GF) i) := by
  unfold uartRxWord; infer_instance

/-! ## The ghost state beside the mirror -/

def sentAuth (γ : UartNames) (u : UartState) : IProp GF := γ.acc ↪●ML (Uart.acc u)
def outAuth (γ : UartNames) (u : UartState) : IProp GF := γ.out ↪●ML u.out
/-- `l` is a prefix of what the transmitter has finished with (persistent). -/
def outLb (γ : UartNames) (l : List (BitVec 8)) : IProp GF := γ.out ↪◯ML l
def txAuth (γ : UartNames) (u : UartState) : IProp GF := γ.tx ↪VAR{.own (1 : Qp).half} (Uart.acc u)
/-- The transmit token: the holder knows the accepted trace is `l`. -/
def txOwn (γ : UartNames) (l : List (BitVec 8)) : IProp GF := γ.tx ↪VAR{.own (1 : Qp).half} l
/-- The invariant's half of the divisor latch.  The driver's half (`dlabOwn`)
is persisted once `uartinit` leaves the latch off (`dlabOwn_freeze`): after
that no update is possible (it would need the whole variable), so the latch
is off for good. -/
def dlabAuth (γ : UartNames) (u : UartState) : IProp GF := γ.dlab ↪VAR{.own (1 : Qp).half} (Uart.dlab u)
/-- The driver's half of the divisor latch, before it is frozen. -/
def dlabOwn (γ : UartNames) (b : Bool) : IProp GF := γ.dlab ↪VAR{.own (1 : Qp).half} b
/-- The divisor latch is off for good (persistent). -/
def dlabOff (γ : UartNames) : IProp GF := γ.dlab ↪VAR{.discard} false
def rxInAuth (γ : UartNames) (ins : List (BitVec 8)) : IProp GF := γ.rxin ↪●ML ins
/-- `l` is a prefix of the bytes that entered the receive FIFO (persistent). -/
def rxInLb (γ : UartNames) (l : List (BitVec 8)) : IProp GF := γ.rxin ↪◯ML l
def rxPopAuth (γ : UartNames) (k : Nat) : IProp GF := γ.rxpop ↪VAR{.own (1 : Qp).half} k
/-- The receive token: `k` bytes have been popped from the FIFO. -/
def rxTok (γ : UartNames) (k : Nat) : IProp GF := γ.rxpop ↪VAR{.own (1 : Qp).half} k

/-- The receive column: the FIFO is the unpopped suffix of what entered. -/
def rxCol (γ : UartNames) (u : UartState) : IProp GF := iprop%
  ∃ (ins : List (BitVec 8)) (k : Nat), rxInAuth γ ins ∗ rxPopAuth γ k ∗ ⌜k ≤ ins.length ∧ u.rx = ins.drop k⌝

def uartGhosts (γ : UartNames) (u : UartState) : IProp GF := iprop%
  sentAuth γ u ∗ outAuth γ u ∗ txAuth γ u ∗ dlabAuth γ u ∗ rxCol γ u ∗ ⌜Uart.loopback u = false⌝

instance outLb_persistent (γ : UartNames) (l : List (BitVec 8)) : Persistent (outLb (GF := GF) γ l) := by
  unfold outLb; infer_instance
instance dlabOff_persistent (γ : UartNames) : Persistent (dlabOff (GF := GF) γ) := by
  unfold dlabOff; infer_instance
instance rxInLb_persistent (γ : UartNames) (l : List (BitVec 8)) : Persistent (rxInLb (GF := GF) γ l) := by
  unfold rxInLb; infer_instance
instance uartGhosts_timeless (γ : UartNames) (u : UartState) : Timeless (uartGhosts (GF := GF) γ u) := by
  unfold uartGhosts sentAuth outAuth txAuth dlabAuth rxCol rxInAuth rxPopAuth; infer_instance

/-- Ghost state stated on the fields a register access keeps is unchanged
by it (the record updates reduce). -/
theorem uartGhosts_thri (γ : UartNames) (u : UartState) (f : Bool) :
    uartGhosts (GF := GF) γ { u with thri := f } = uartGhosts γ u := rfl
theorem uartGhosts_ier (γ : UartNames) (u : UartState) (x : BitVec 8) (f : Bool) :
    uartGhosts (GF := GF) γ { u with ier := x, thri := f } = uartGhosts γ u := rfl
theorem uartGhosts_dll (γ : UartNames) (u : UartState) (x : BitVec 8) :
    uartGhosts (GF := GF) γ { u with dll := x } = uartGhosts γ u := rfl
theorem uartGhosts_dlm (γ : UartNames) (u : UartState) (x : BitVec 8) :
    uartGhosts (GF := GF) γ { u with dlm := x } = uartGhosts γ u := rfl
theorem sentAuth_rx (γ : UartNames) (u : UartState) (r : List (BitVec 8)) :
    sentAuth (GF := GF) γ { u with rx := r } = sentAuth γ u := rfl
theorem outAuth_rx (γ : UartNames) (u : UartState) (r : List (BitVec 8)) :
    outAuth (GF := GF) γ { u with rx := r } = outAuth γ u := rfl
theorem txAuth_rx (γ : UartNames) (u : UartState) (r : List (BitVec 8)) :
    txAuth (GF := GF) γ { u with rx := r } = txAuth γ u := rfl
theorem dlabAuth_rx (γ : UartNames) (u : UartState) (r : List (BitVec 8)) :
    dlabAuth (GF := GF) γ { u with rx := r } = dlabAuth γ u := rfl
theorem sentAuth_thri (γ : UartNames) (u : UartState) (f : Bool) :
    sentAuth (GF := GF) γ { u with thri := f } = sentAuth γ u := rfl
theorem outAuth_thri (γ : UartNames) (u : UartState) (f : Bool) :
    outAuth (GF := GF) γ { u with thri := f } = outAuth γ u := rfl
theorem txAuth_thri (γ : UartNames) (u : UartState) (f : Bool) :
    txAuth (GF := GF) γ { u with thri := f } = txAuth γ u := rfl
theorem dlabAuth_thri (γ : UartNames) (u : UartState) (f : Bool) :
    dlabAuth (GF := GF) γ { u with thri := f } = dlabAuth γ u := rfl
theorem rxCol_thri (γ : UartNames) (u : UartState) (f : Bool) :
    rxCol (GF := GF) γ { u with thri := f } = rxCol γ u := rfl
theorem sentAuth_ier (γ : UartNames) (u : UartState) (x : BitVec 8) (f : Bool) :
    sentAuth (GF := GF) γ { u with ier := x, thri := f } = sentAuth γ u := rfl
theorem outAuth_ier (γ : UartNames) (u : UartState) (x : BitVec 8) (f : Bool) :
    outAuth (GF := GF) γ { u with ier := x, thri := f } = outAuth γ u := rfl
theorem txAuth_ier (γ : UartNames) (u : UartState) (x : BitVec 8) (f : Bool) :
    txAuth (GF := GF) γ { u with ier := x, thri := f } = txAuth γ u := rfl
theorem dlabAuth_ier (γ : UartNames) (u : UartState) (x : BitVec 8) (f : Bool) :
    dlabAuth (GF := GF) γ { u with ier := x, thri := f } = dlabAuth γ u := rfl
theorem rxCol_ier (γ : UartNames) (u : UartState) (x : BitVec 8) (f : Bool) :
    rxCol (GF := GF) γ { u with ier := x, thri := f } = rxCol γ u := rfl
theorem sentAuth_dll (γ : UartNames) (u : UartState) (x : BitVec 8) :
    sentAuth (GF := GF) γ { u with dll := x } = sentAuth γ u := rfl
theorem outAuth_dll (γ : UartNames) (u : UartState) (x : BitVec 8) :
    outAuth (GF := GF) γ { u with dll := x } = outAuth γ u := rfl
theorem txAuth_dll (γ : UartNames) (u : UartState) (x : BitVec 8) :
    txAuth (GF := GF) γ { u with dll := x } = txAuth γ u := rfl
theorem dlabAuth_dll (γ : UartNames) (u : UartState) (x : BitVec 8) :
    dlabAuth (GF := GF) γ { u with dll := x } = dlabAuth γ u := rfl
theorem rxCol_dll (γ : UartNames) (u : UartState) (x : BitVec 8) :
    rxCol (GF := GF) γ { u with dll := x } = rxCol γ u := rfl
theorem sentAuth_dlm (γ : UartNames) (u : UartState) (x : BitVec 8) :
    sentAuth (GF := GF) γ { u with dlm := x } = sentAuth γ u := rfl
theorem outAuth_dlm (γ : UartNames) (u : UartState) (x : BitVec 8) :
    outAuth (GF := GF) γ { u with dlm := x } = outAuth γ u := rfl
theorem txAuth_dlm (γ : UartNames) (u : UartState) (x : BitVec 8) :
    txAuth (GF := GF) γ { u with dlm := x } = txAuth γ u := rfl
theorem dlabAuth_dlm (γ : UartNames) (u : UartState) (x : BitVec 8) :
    dlabAuth (GF := GF) γ { u with dlm := x } = dlabAuth γ u := rfl
theorem rxCol_dlm (γ : UartNames) (u : UartState) (x : BitVec 8) :
    rxCol (GF := GF) γ { u with dlm := x } = rxCol γ u := rfl
theorem outAuth_fcr (γ : UartNames) (u : UartState) (r t : List (BitVec 8)) (x : BitVec 8) (f : Bool) :
    outAuth (GF := GF) γ { u with rx := r, tx := t, fcr := x, thri := f } = outAuth γ u := rfl
theorem dlabAuth_fcr (γ : UartNames) (u : UartState) (r t : List (BitVec 8)) (x : BitVec 8) (f : Bool) :
    dlabAuth (GF := GF) γ { u with rx := r, tx := t, fcr := x, thri := f } = dlabAuth γ u := rfl
theorem sentAuth_lcr (γ : UartNames) (u : UartState) (x : BitVec 8) :
    sentAuth (GF := GF) γ { u with lcr := x } = sentAuth γ u := rfl
theorem outAuth_lcr (γ : UartNames) (u : UartState) (x : BitVec 8) :
    outAuth (GF := GF) γ { u with lcr := x } = outAuth γ u := rfl
theorem txAuth_lcr (γ : UartNames) (u : UartState) (x : BitVec 8) :
    txAuth (GF := GF) γ { u with lcr := x } = txAuth γ u := rfl
theorem rxCol_lcr (γ : UartNames) (u : UartState) (x : BitVec 8) :
    rxCol (GF := GF) γ { u with lcr := x } = rxCol γ u := rfl

/-! ## The invariant -/

def uartN : UartId → Namespace
  | .uart0 => ndot nroot "xv6uart0"
  | .uart1 => ndot nroot "xv6uart1"

/-- The port's invariant: the mirror beside the ghosts. -/
def uartInv (i : UartId) (γ : UartNames) : IProp GF :=
  devInvR (uartN i) (.uart i) (fun u => uartGhosts γ u)

instance uartInv_persistent (i : UartId) (γ : UartNames) : Persistent (uartInv (GF := GF) i γ) := by
  unfold uartInv devInvR; infer_instance

/-! ## The chip's steps preserve the ghosts -/

theorem uart_localR (i : UartId) : DevSig.LocalR (.uart i) uartRel := by
  refine ⟨?_, fun t => nomatch t⟩
  show DevM.LocalR uartRel (Uart.body i)
  unfold Uart.body DevM.chooseLt DevM.chooseByte DevM.choose DevM.step DevM.lift
  simp only [bind, DevM.bind, Pure.pure]
  refine DevM.LocalR.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun) (fun _ h => nomatch h) fun r => ?_
  split
  · exact DevM.LocalR.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun)
      (fun g h s s' os hg => by cases h; exact uartRel_txArm i s s' os hg) fun _ => DevM.LocalR.pure ()
  split
  · refine DevM.LocalR.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun) (fun _ h => nomatch h) fun b => ?_
    exact DevM.LocalR.op _ _ (fun _ _ _ _ => nofun) (fun _ _ _ => nofun)
      (fun g h s s' os hg => by cases h; exact uartRel_rxArm i b s s' os hg) fun _ => DevM.LocalR.pure ()
  · exact DevM.LocalR.pure ()

theorem uartGhosts_step (γ : UartNames) (u u' : UartState) (h : uartRel u u') :
    uartGhosts (GF := GF) γ u ⊢ |==> uartGhosts γ u' := by
  obtain ⟨hacc, hout, hmcr, hlcr, hier, hfcr, hrx⟩ := h
  unfold uartGhosts sentAuth outAuth txAuth dlabAuth rxCol rxInAuth rxPopAuth
  iintro ⟨Hsent, Hout, Htx, Hdlab, ⟨%ins, %k, Hin, Hpop, %⟨hk, hfifo⟩⟩, %hloop⟩
  have hdl : Uart.dlab u' = Uart.dlab u := by unfold Uart.dlab; rw [hlcr]
  have hlb : Uart.loopback u' = Uart.loopback u := by unfold Uart.loopback; rw [hmcr]
  ihave Hout' := MonoList.auth_own_update γ.out u'.out hout $$ Hout
  imod Hout' with ⟨Hout, _⟩
  rw [hacc, hdl]
  rcases hrx with hrx | ⟨b, hrx⟩
  · imodintro
    iframe Hsent Hout Htx Hdlab
    isplitl [Hin Hpop]
    · iexists ins, k
      iframe Hin Hpop
      ipureintro; exact ⟨hk, by rw [hrx, hfifo]⟩
    · ipureintro; rw [hlb]; exact hloop
  · ihave Hin' := MonoList.auth_own_update_app γ.rxin [b] $$ Hin
    imod Hin' with ⟨Hin, _⟩
    imodintro
    iframe Hsent Hout Htx Hdlab
    isplitl [Hin Hpop]
    · iexists ins ++ [b], k
      iframe Hin Hpop
      ipureintro
      refine ⟨by simp; omega, ?_⟩
      rw [hrx, hfifo, List.drop_append_of_le_length hk]
    · ipureintro; rw [hlb]; exact hloop

/-- **The port's thread is safe under its invariant**, given the client's
trace permit for the port (the Rocq `WpUart.wp_uart_loop`'s
`uart_obs_permit i γ`): the port's tx/rx arms are OBSERVED, and the history
ghost moves only with the client's consent. -/
theorem wpDev_uart_inv (i : UartId) (γ : UartNames) :
    uartInv i γ ∗ devObsPermit (uartN i) (.uart i) (fun u => uartGhosts γ u) ∗ genCert ⊢@{IProp GF}
      devWP (genId (hlc := hlc) (GF := GF)) (.uart i) rootTask (DevM.pure ()) := by
  unfold uartInv
  iintro H
  iapply wpDev_localR (uartN i) (.uart i) uartRel (fun u => uartGhosts γ u) (uart_localR i)
    (fun u u' h => uartGhosts_step γ u u' h) $$ H %rootTask %(DevM.pure ()) %(DevM.LocalR.pure ())

/-- The trace namespace is not a port's. -/
theorem uart_obsN_mask (i : UartId) : (↑obsN : CoPset) ⊆ ⊤ \ ↑(uartN i) := by
  have hd : (↑obsN : CoPset) ## ↑(uartN i) := by
    cases i
    · exact ndot_ne_disjoint nroot (by decide)
    · exact ndot_ne_disjoint nroot (by decide)
  intro p hp
  rw [CoPset.in_diff]
  exact ⟨CoPset.subseteq_top p hp, fun hc => hd p ⟨hp, hc⟩⟩

/-- ...and at the TRIVIAL trace predicate the permit is free (Rocq
`uart_obs_permit_triv`), so the thread needs only the trace invariant. -/
theorem wpDev_uart_inv_triv (i : UartId) (γ : UartNames)
    (heq : MachFixedGS.obsPred (hlc := hlc) (GF := GF) = obsPredTriv) :
    uartInv i γ ∗ obsInv ∗ genCert ⊢@{IProp GF}
      devWP (genId (hlc := hlc) (GF := GF)) (.uart i) rootTask (DevM.pure ()) := by
  iintro ⟨Hinv, #Hoinv, Hcert⟩
  ihave #Hperm := devObsPermit_triv (uartN i) (.uart i) (fun u => uartGhosts γ u)
    (uart_obsN_mask i) heq $$ Hoinv
  iapply wpDev_uart_inv i γ
  iframe Hinv Hperm Hcert

/-! ## Facts the accessors rest on -/

theorem txOwn_agree (γ : UartNames) (u : UartState) (l : List (BitVec 8)) :
    txAuth (GF := GF) γ u ∗ txOwn γ l ⊢ ⌜Uart.acc u = l⌝ ∗ txAuth γ u ∗ txOwn γ l := by
  unfold txAuth txOwn
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ.tx _ _ _ _ $$ H1 H2
  iframe H1 H2
  ipureintro; exact h

theorem txOwn_update (γ : UartNames) (u : UartState) (l l' : List (BitVec 8)) (hacc : Uart.acc u = l) :
    txAuth (GF := GF) γ u ∗ txOwn γ l ⊢ |==> ∀ u' : UartState, ⌜Uart.acc u' = l'⌝ → txAuth γ u' ∗ txOwn γ l' := by
  unfold txAuth txOwn
  iintro ⟨H1, H2⟩
  rw [hacc]
  imod (ghost_var_update_halves l' γ.tx l l) $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iintro %u' %h
  rw [h]
  iframe H1 H2

theorem outLb_prefix (γ : UartNames) (u : UartState) (l : List (BitVec 8)) :
    outAuth (GF := GF) γ u ∗ outLb γ l ⊢ ⌜l <+: u.out⌝ ∗ outAuth γ u := by
  unfold outAuth outLb
  iintro ⟨H1, #H2⟩
  ihave %h := MonoList.auth_lb_own_valid γ.out _ u.out l $$ H1 H2
  iframe H1
  ipureintro; exact h.2

theorem outLb_get (γ : UartNames) (u : UartState) : outAuth (GF := GF) γ u ⊢ outAuth γ u ∗ outLb γ u.out := by
  unfold outAuth outLb
  iintro H
  ihave #H' := MonoList.lb_own_get γ.out _ u.out $$ H
  iframe H H'

theorem dlabOff_agree (γ : UartNames) (u : UartState) :
    dlabAuth (GF := GF) γ u ∗ dlabOff γ ⊢ ⌜Uart.dlab u = false⌝ ∗ dlabAuth γ u := by
  unfold dlabAuth dlabOff
  iintro ⟨H1, #H2⟩
  ihave %h := ghost_var_agree γ.dlab _ _ _ _ $$ H1 H2
  iframe H1
  ipureintro; exact h

theorem dlabOwn_agree (γ : UartNames) (u : UartState) (b : Bool) :
    dlabAuth (GF := GF) γ u ∗ dlabOwn γ b ⊢ ⌜Uart.dlab u = b⌝ ∗ dlabAuth γ u ∗ dlabOwn γ b := by
  unfold dlabAuth dlabOwn
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ.dlab _ _ _ _ $$ H1 H2
  iframe H1 H2
  ipureintro; exact h

/-- Moving the latch: both halves. -/
theorem dlabOwn_update (γ : UartNames) (u : UartState) (b b' : Bool) (hb : Uart.dlab u = b) :
    dlabAuth (GF := GF) γ u ∗ dlabOwn γ b ⊢ |==> ∀ u' : UartState, ⌜Uart.dlab u' = b'⌝ → dlabAuth γ u' ∗ dlabOwn γ b' := by
  unfold dlabAuth dlabOwn
  iintro ⟨H1, H2⟩
  rw [hb]
  imod (ghost_var_update_halves b' γ.dlab b b) $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iintro %u' %h
  rw [h]
  iframe H1 H2

/-- The freeze: the driver's half, at `false`, becomes the persistent `dlabOff`. -/
theorem dlabOwn_freeze (γ : UartNames) : dlabOwn (GF := GF) γ false ⊢ |==> dlabOff γ := by
  unfold dlabOwn dlabOff
  iintro H
  iapply ghost_var_persist $$ H

theorem rxTok_agree (γ : UartNames) (k k' : Nat) :
    rxPopAuth (GF := GF) γ k' ∗ rxTok γ k ⊢ ⌜k' = k⌝ ∗ rxPopAuth γ k' ∗ rxTok γ k := by
  unfold rxPopAuth rxTok
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ.rxpop _ _ _ _ $$ H1 H2
  iframe H1 H2
  ipureintro; exact h

theorem rxTok_update (γ : UartNames) (k k' : Nat) :
    rxPopAuth (GF := GF) γ k ∗ rxTok γ k ⊢ |==> (rxPopAuth γ k' ∗ rxTok γ k') := by
  unfold rxPopAuth rxTok
  iintro ⟨H1, H2⟩
  imod (ghost_var_update_halves k' γ.rxpop k k) $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iframe H1 H2

theorem rxInLb_prefix (γ : UartNames) (ins l : List (BitVec 8)) :
    rxInAuth (GF := GF) γ ins ∗ rxInLb γ l ⊢ ⌜l <+: ins⌝ ∗ rxInAuth γ ins := by
  unfold rxInAuth rxInLb
  iintro ⟨H1, #H2⟩
  ihave %h := MonoList.auth_lb_own_valid γ.rxin _ ins l $$ H1 H2
  iframe H1
  ipureintro; exact h.2

theorem rxInLb_get (γ : UartNames) (ins : List (BitVec 8)) :
    rxInAuth (GF := GF) γ ins ⊢ rxInAuth γ ins ∗ rxInLb γ ins := by
  unfold rxInAuth rxInLb
  iintro H
  ihave #H' := MonoList.lb_own_get γ.rxin _ ins $$ H
  iframe H H'

/-- What a caller's sublist witness says against the trace: it is a sublist
of the current accepted trace. -/
theorem uartSentSub_sub (γ : UartNames) (u : UartState) (bs : List (BitVec 8)) :
    sentAuth (GF := GF) γ u ∗ uartSentSub γ bs ⊢ ⌜bs.Sublist (Uart.acc u)⌝ ∗ sentAuth γ u := by
  unfold sentAuth uartSentSub uartSent
  iintro ⟨H1, ⟨%tr, #H2, %hsub⟩⟩
  ihave %h := MonoList.auth_lb_own_valid γ.acc _ (Uart.acc u) tr $$ H1 H2
  iframe H1
  ipureintro; exact hsub.trans h.2.sublist

theorem sentAuth_append (γ : UartNames) (u u' : UartState) (b : BitVec 8) (h : Uart.acc u' = Uart.acc u ++ [b]) :
    sentAuth (GF := GF) γ u ⊢ |==> (sentAuth γ u' ∗ uartSent γ (Uart.acc u')) := by
  unfold sentAuth uartSent
  iintro H
  ihave H' := MonoList.auth_own_update_app γ.acc [b] $$ H
  imod H' with ⟨H1, H2⟩
  imodintro
  rw [h]
  iframe H1 H2

/-- A THR write moves only the transmit FIFO and the latch: the other
ghosts are stated on fields it keeps. -/
theorem outAuth_thr (γ : UartNames) (u : UartState) (t : List (BitVec 8)) (f : Bool) :
    outAuth (GF := GF) γ { u with tx := t, thri := f } = outAuth γ u := rfl
theorem dlabAuth_thr (γ : UartNames) (u : UartState) (t : List (BitVec 8)) (f : Bool) :
    dlabAuth (GF := GF) γ { u with tx := t, thri := f } = dlabAuth γ u := rfl
theorem rxCol_thr (γ : UartNames) (u : UartState) (t : List (BitVec 8)) (f : Bool) :
    rxCol (GF := GF) γ { u with tx := t, thri := f } = rxCol γ u := rfl

/-! ## The accessors

Each opens the port's invariant (mask `⊤ → ⊤ ∖ N`, then `→ ∅` for the
leaf), agrees the mirror with the invariant's copy, and hands the leaf the
register access; the continuation gets the successor mirror back and
re-establishes the ghosts.  The Rocq `WpSconfUartAccess` leaves. -/

/-- Reading LSR while holding the transmit token: the value is the LSR of
some state whose accepted trace is `l`; the transmitted prefix of that
state is bounded (with THRE seen, it is exactly `l`). -/
theorem lsr_read_au (i : UartId) (γ : UartNames) (l : List (BitVec 8)) :
    uartInv i γ ∗ txOwn γ l ⊢@{IProp GF} devReadAU (.uart i) 5 1 (fun b =>
      iprop(txOwn γ l ∗ ∃ u : UartState, ⌜b = Uart.lsr u ∧ Uart.acc u = l⌝ ∗ outLb γ u.out)) := by
  unfold uartInv devInvR devReadAU
  iintro ⟨#Hinv, Htok⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact readN_one_isSome u 5 (by decide)
  inext
  iintro %w %u' %hrd Hfrag
  have hrd' : Uart.readN u 5 1 = some (w, u') := hrd
  rw [read_lsr] at hrd'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrd')
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  icases txOwn_agree γ u l $$ [Htx Htok] with ⟨%hacc, Htx, Htok⟩
  · iframe
  icases outLb_get γ u $$ Hout with ⟨Hout, #Hlb⟩
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
  case' _ =>
    inext
    iexists u
    iframe Hfrag Hsent Hout Htx Hdlab Hcol
    ipureintro; exact hloop
  imod Hcl
  imodintro
  iframe Htok
  iexists u
  iframe Hlb
  ipureintro; exact ⟨rfl, hacc⟩

/-- Writing THR with the token, the bound at the token's trace, and the
latch off: the byte is accepted, the trace grows by it. -/
theorem thr_write_au (i : UartId) (γ : UartNames) (l bs : List (BitVec 8)) (b : BitVec 8) :
    uartInv i γ ∗ txOwn γ l ∗ outLb γ l ∗ dlabOff γ ∗ uartSentSub γ bs ⊢@{IProp GF}
      devWriteAU (.uart i) 0 1 b iprop(txOwn γ (l ++ [b]) ∗ uartSent γ (l ++ [b]) ∗ uartSentSub γ (bs ++ [b])) := by
  unfold uartInv devInvR devWriteAU
  iintro ⟨#Hinv, Htok, #Hlb, #Hoff, #Hsub⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  icases txOwn_agree γ u l $$ [Htx Htok] with ⟨%hacc, Htx, Htok⟩
  · iframe
  icases uartSentSub_sub γ u bs $$ [Hsent Hsub] with ⟨%hbs, Hsent⟩
  · iframe Hsent; iexact Hsub
  icases outLb_prefix γ u l $$ [Hout Hlb] with ⟨%hpre, Hout⟩
  · iframe Hout; iexact Hlb
  icases dlabOff_agree γ u $$ [Hdlab Hoff] with ⟨%hdlab, Hdlab⟩
  · iframe Hdlab; iexact Hoff
  have htx : u.tx = [] := tx_nil_of_out_prefix u l hacc hpre
  have hroom : u.tx.length < Uart.fifoDepth := by rw [htx]; decide
  have hwr := write_thr u b hdlab hroom
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact Option.isSome_iff_exists.2 ⟨_, hwr⟩
  inext
  iintro %u' %hwr' Hfrag
  have hwr'' : Uart.writeN u 0 1 b = some u' := hwr'
  rw [hwr] at hwr''
  obtain rfl := Option.some.inj hwr''
  have hacc' := acc_thr u b
  rw [hacc] at hacc'
  imod (sentAuth_append γ u _ b (acc_thr u b)) $$ Hsent with ⟨Hsent, #Hsentlb⟩
  imod (txOwn_update γ u l (l ++ [b]) hacc) $$ [Htx Htok] with Hup
  · iframe
  icases Hup $$ %_ %hacc' with ⟨Htx, Htok⟩
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
  case' _ =>
    inext
    iexists { u with tx := u.tx ++ [b], thri := false }
    rw [outAuth_thr, dlabAuth_thr, rxCol_thr]
    iframe Hfrag Hsent Htx Hout Hdlab Hcol
    ipureintro; exact hloop
  imod Hcl
  imodintro
  rw [hacc']
  iframe Htok
  isplit
  · iexact Hsentlb
  unfold uartSentSub
  iexists (l ++ [b])
  isplit
  · iexact Hsentlb
  ipureintro
  rw [hacc] at hbs
  exact hbs.append_right [b]

/-- Reading ISR: nothing the ghosts track moves (the transmit latch may drop). -/
theorem isr_read_au (i : UartId) (γ : UartNames) :
    uartInv i γ ⊢@{IProp GF} devReadAU (.uart i) 2 1 (fun _ => emp) := by
  unfold uartInv devInvR devReadAU
  iintro #Hinv
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact readN_one_isSome u 2 (by decide)
  inext
  iintro %w %u' %hrd Hfrag
  have hrd' : Uart.readN u 2 1 = some (w, u') := hrd
  rw [read_isr] at hrd'
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  by_cases hth : Uart.isrThri u = true
  · rw [if_pos hth] at hrd'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrd')
    imod Hmask
    ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
    case' _ =>
      inext
      iexists { u with thri := false }
      rw [sentAuth_thri, outAuth_thri, txAuth_thri, dlabAuth_thri, rxCol_thri]
      iframe Hfrag Hsent Hout Htx Hdlab Hcol
      ipureintro; exact hloop
    imod Hcl
    imodintro
    iempintro
  · rw [if_neg hth] at hrd'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrd')
    imod Hmask
    ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
    case' _ =>
      inext
      iexists u
      iframe Hfrag Hsent Hout Htx Hdlab Hcol
      ipureintro; exact hloop
    imod Hcl
    imodintro
    iempintro

/-- Reading LSR with the receive token: the FIFO is the unpopped suffix of
a bounded list of arrivals. -/
theorem lsr_read_rx_au (i : UartId) (γ : UartNames) (k : Nat) :
    uartInv i γ ∗ rxTok γ k ⊢@{IProp GF} devReadAU (.uart i) 5 1 (fun b =>
      iprop(rxTok γ k ∗ ∃ (u : UartState) (ins : List (BitVec 8)),
        ⌜b = Uart.lsr u ∧ k ≤ ins.length ∧ u.rx = ins.drop k⌝ ∗ rxInLb γ ins)) := by
  unfold uartInv devInvR devReadAU
  iintro ⟨#Hinv, Htok⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact readN_one_isSome u 5 (by decide)
  inext
  iintro %w %u' %hrd Hfrag
  have hrd' : Uart.readN u 5 1 = some (w, u') := hrd
  rw [read_lsr] at hrd'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrd')
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  unfold rxCol
  icases Hcol with ⟨%ins, %k', Hin, Hpop, %⟨hk, hfifo⟩⟩
  icases rxTok_agree γ k k' $$ [Hpop Htok] with ⟨%hkk, Hpop, Htok⟩
  · iframe
  subst k'
  icases rxInLb_get γ ins $$ Hin with ⟨Hin, #Hlb⟩
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hin Hpop]
  case' _ =>
    inext
    iexists u
    iframe Hfrag Hsent Hout Htx Hdlab
    isplitl [Hin Hpop]
    · iexists ins, k
      iframe Hin Hpop
      ipureintro; exact ⟨hk, hfifo⟩
    · ipureintro; exact hloop
  imod Hcl
  imodintro
  iframe Htok
  iexists u, ins
  iframe Hlb
  ipureintro; exact ⟨rfl, hk, hfifo⟩

/-- Reading RHR with the token, a bound past the popped count and the latch
off: the FIFO's head pops, and it is the `k`-th arrival. -/
theorem rhr_read_au (i : UartId) (γ : UartNames) (k : Nat) (ins : List (BitVec 8)) (hk : k < ins.length) :
    uartInv i γ ∗ rxTok γ k ∗ rxInLb γ ins ∗ dlabOff γ ⊢@{IProp GF}
      devReadAU (.uart i) 0 1 (fun b => iprop(rxTok γ (k + 1) ∗ ⌜ins[k]? = some b⌝)) := by
  unfold uartInv devInvR devReadAU
  iintro ⟨#Hinv, Htok, #Hlb, #Hoff⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  unfold rxCol
  icases Hcol with ⟨%ins', %k', Hin, Hpop, %⟨hk', hfifo⟩⟩
  icases rxTok_agree γ k k' $$ [Hpop Htok] with ⟨%hkk, Hpop, Htok⟩
  · iframe
  subst k'
  icases rxInLb_prefix γ ins' ins $$ [Hin Hlb] with ⟨%hpre, Hin⟩
  · iframe Hin; iexact Hlb
  icases dlabOff_agree γ u $$ [Hdlab Hoff] with ⟨%hdlab, Hdlab⟩
  · iframe Hdlab; iexact Hoff
  have hklt : k < ins'.length := lt_of_lt_of_le hk hpre.length_le
  have hrx : u.rx = ins'[k] :: ins'.drop (k + 1) := by rw [hfifo, List.drop_eq_getElem_cons hklt]
  have hget : ins[k]? = some ins'[k] := by
    obtain ⟨t, rfl⟩ := hpre
    rw [List.getElem_append_left hk, List.getElem?_eq_getElem hk]
  have hrd := read_rhr u ins'[k] (ins'.drop (k + 1)) hdlab hrx
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact Option.isSome_iff_exists.2 ⟨_, hrd⟩
  inext
  iintro %w %u' %hrd' Hfrag
  have hrd'' : Uart.readN u 0 1 = some (w, u') := hrd'
  rw [hrd] at hrd''
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrd'')
  imod (rxTok_update γ k (k + 1)) $$ [Hpop Htok] with ⟨Hpop, Htok⟩
  · iframe
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hin Hpop]
  case' _ =>
    inext
    iexists { u with rx := ins'.drop (k + 1) }
    rw [sentAuth_rx, outAuth_rx, txAuth_rx, dlabAuth_rx]
    iframe Hfrag Hsent Hout Htx Hdlab
    isplitl [Hin Hpop]
    · iexists ins', k + 1
      iframe Hin Hpop
      ipureintro; exact ⟨hklt, rfl⟩
    · ipureintro; exact hloop
  imod Hcl
  imodintro
  iframe Htok
  ipureintro; exact hget

/-- Writing IER with the latch known off (the driver's half at `false`). -/
theorem ier_write_au (i : UartId) (γ : UartNames) (b : BitVec 8) :
    uartInv i γ ∗ dlabOwn γ false ⊢@{IProp GF} devWriteAU (.uart i) 1 1 b (dlabOwn γ false) := by
  unfold uartInv devInvR devWriteAU
  iintro ⟨#Hinv, Hown⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  icases dlabOwn_agree γ u false $$ [Hdlab Hown] with ⟨%hdlab, Hdlab, Hown⟩
  · iframe
  have hwr := write_ier u b hdlab
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact Option.isSome_iff_exists.2 ⟨_, hwr⟩
  inext
  iintro %u' %hwr' Hfrag
  have hwr'' : Uart.writeN u 1 1 b = some u' := hwr'
  rw [hwr] at hwr''
  obtain rfl := Option.some.inj hwr''
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
  case' _ =>
    inext
    iexists { u with ier := (b &&& 0x0f#8), thri := (u.thri || ((b &&& 0x0f#8).getLsbD 1 && Uart.thre u)) }
    rw [sentAuth_ier, outAuth_ier, txAuth_ier, dlabAuth_ier, rxCol_ier]
    iframe Hfrag Hsent Hout Htx Hdlab Hcol
    ipureintro; exact hloop
  imod Hcl
  imodintro
  iexact Hown

/-- Writing LCR: the latch follows bit 7 of the value. -/
theorem lcr_write_au (i : UartId) (γ : UartNames) (b0 : Bool) (b : BitVec 8) :
    uartInv i γ ∗ dlabOwn γ b0 ⊢@{IProp GF} devWriteAU (.uart i) 3 1 b (dlabOwn γ (b.getLsbD 7)) := by
  unfold uartInv devInvR devWriteAU
  iintro ⟨#Hinv, Hown⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  icases dlabOwn_agree γ u b0 $$ [Hdlab Hown] with ⟨%hdlab, Hdlab, Hown⟩
  · iframe
  have hwr := write_lcr u b
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact Option.isSome_iff_exists.2 ⟨_, hwr⟩
  inext
  iintro %u' %hwr' Hfrag
  have hwr'' : Uart.writeN u 3 1 b = some u' := hwr'
  rw [hwr] at hwr''
  obtain rfl := Option.some.inj hwr''
  imod (dlabOwn_update γ u b0 (b.getLsbD 7) hdlab) $$ [Hdlab Hown] with Hup
  · iframe
  icases Hup $$ %({ u with lcr := b }) %rfl with ⟨Hdlab, Hown⟩
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
  case' _ =>
    inext
    iexists { u with lcr := b }
    rw [sentAuth_lcr, outAuth_lcr, txAuth_lcr, rxCol_lcr]
    iframe Hfrag Hsent Hout Htx Hdlab Hcol
    ipureintro; exact hloop
  imod Hcl
  imodintro
  iexact Hown

/-- Writing DLL (offset 0 with the latch on). -/
theorem dll_write_au (i : UartId) (γ : UartNames) (b : BitVec 8) :
    uartInv i γ ∗ dlabOwn γ true ⊢@{IProp GF} devWriteAU (.uart i) 0 1 b (dlabOwn γ true) := by
  unfold uartInv devInvR devWriteAU
  iintro ⟨#Hinv, Hown⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  icases dlabOwn_agree γ u true $$ [Hdlab Hown] with ⟨%hdlab, Hdlab, Hown⟩
  · iframe
  have hwr := write_dll u b hdlab
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact Option.isSome_iff_exists.2 ⟨_, hwr⟩
  inext
  iintro %u' %hwr' Hfrag
  have hwr'' : Uart.writeN u 0 1 b = some u' := hwr'
  rw [hwr] at hwr''
  obtain rfl := Option.some.inj hwr''
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
  case' _ =>
    inext
    iexists { u with dll := b }
    rw [sentAuth_dll, outAuth_dll, txAuth_dll, dlabAuth_dll, rxCol_dll]
    iframe Hfrag Hsent Hout Htx Hdlab Hcol
    ipureintro; exact hloop
  imod Hcl
  imodintro
  iexact Hown

/-- Writing DLM (offset 1 with the latch on). -/
theorem dlm_write_au (i : UartId) (γ : UartNames) (b : BitVec 8) :
    uartInv i γ ∗ dlabOwn γ true ⊢@{IProp GF} devWriteAU (.uart i) 1 1 b (dlabOwn γ true) := by
  unfold uartInv devInvR devWriteAU
  iintro ⟨#Hinv, Hown⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  icases dlabOwn_agree γ u true $$ [Hdlab Hown] with ⟨%hdlab, Hdlab, Hown⟩
  · iframe
  have hwr := write_dlm u b hdlab
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact Option.isSome_iff_exists.2 ⟨_, hwr⟩
  inext
  iintro %u' %hwr' Hfrag
  have hwr'' : Uart.writeN u 1 1 b = some u' := hwr'
  rw [hwr] at hwr''
  obtain rfl := Option.some.inj hwr''
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hcol]
  case' _ =>
    inext
    iexists { u with dlm := b }
    rw [sentAuth_dlm, outAuth_dlm, txAuth_dlm, dlabAuth_dlm, rxCol_dlm]
    iframe Hfrag Hsent Hout Htx Hdlab Hcol
    ipureintro; exact hloop
  imod Hcl
  imodintro
  iexact Hown

/-- Writing FCR with the transmit token at a trace the transmitter has
finished (so the FIFO clear drops nothing accepted) and the receive token
(the FIFO clear pops everything). -/
theorem fcr_write_au (i : UartId) (γ : UartNames) (l : List (BitVec 8)) (k : Nat) (b : BitVec 8) :
    uartInv i γ ∗ txOwn γ l ∗ outLb γ l ∗ rxTok γ k ⊢@{IProp GF}
      devWriteAU (.uart i) 2 1 b iprop(txOwn γ l ∗ ∃ k' : Nat, rxTok γ k') := by
  unfold uartInv devInvR devWriteAU
  iintro ⟨#Hinv, Htok, #Hlb, Hrx⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%u, >Hfrag, >HG⟩
  unfold uartGhosts
  icases HG with ⟨Hsent, Hout, Htx, Hdlab, Hcol, %hloop⟩
  icases txOwn_agree γ u l $$ [Htx Htok] with ⟨%hacc, Htx, Htok⟩
  · iframe
  icases outLb_prefix γ u l $$ [Hout Hlb] with ⟨%hpre, Hout⟩
  · iframe Hout; iexact Hlb
  have htx : u.tx = [] := tx_nil_of_out_prefix u l hacc hpre
  unfold rxCol
  icases Hcol with ⟨%ins, %k', Hin, Hpop, %⟨hk, hfifo⟩⟩
  icases rxTok_agree γ k k' $$ [Hpop Hrx] with ⟨%hkk, Hpop, Hrx⟩
  · iframe
  subst k'
  have hwr := write_fcr u b
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists u
  iframe Hfrag
  isplit
  · ipureintro; exact Option.isSome_iff_exists.2 ⟨_, hwr⟩
  inext
  iintro %u' %hwr' Hfrag
  have hwr'' : Uart.writeN u 2 1 b = some u' := hwr'
  rw [hwr] at hwr''
  obtain rfl := Option.some.inj hwr''
  -- the popped count after the write: everything, if the FIFO was cleared
  imod (rxTok_update γ k (if fcrClrRx u b then ins.length else k)) $$ [Hpop Hrx] with ⟨Hpop, Hrx⟩
  · iframe
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hsent Hout Htx Hdlab Hin Hpop]
  case' _ =>
    inext
    iexists { u with rx := if fcrClrRx u b then [] else u.rx, tx := if fcrClrTx u b then [] else u.tx, fcr := b &&& 0xc9#8, thri := u.thri || fcrClrTx u b }
    have hacc' : Uart.acc { u with rx := if fcrClrRx u b then [] else u.rx, tx := if fcrClrTx u b then [] else u.tx, fcr := b &&& 0xc9#8, thri := u.thri || fcrClrTx u b } = Uart.acc u := by
      simp [Uart.acc, htx]
    unfold sentAuth txAuth
    rw [hacc', outAuth_fcr, dlabAuth_fcr]
    iframe Hfrag Hsent Hout Htx Hdlab
    isplitl [Hin Hpop]
    · iexists ins, (if fcrClrRx u b then ins.length else k)
      iframe Hin Hpop
      ipureintro
      split
      · exact ⟨le_refl _, by simp⟩
      · exact ⟨hk, hfifo⟩
    · ipureintro; exact hloop
  imod Hcl
  imodintro
  iframe Htok
  iexists (if fcrClrRx u b then ins.length else k)
  iexact Hrx

end

/-! ## The persistent bundle a transmitter needs

What `uartputc_sync` (and everything above it: `consputc`, `prputc`,
`printk`) carries about port `i`: the invariant, the transmit-lock
credential, the frozen divisor latch and the port's base word.  All
persistent, so one copy serves every caller. -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

def uartPort [CurCtx] (i : UartId) (γl : GName) (γ : UartNames) : IProp GF := iprop%
  uartInv i γ ∗ isTxLockAt i γl γ ∗ dlabOff γ ∗ uartBaseWord i

instance uartPort_persistent [CurCtx] (i : UartId) (γl : GName) (γ : UartNames) :
    Persistent (uartPort (GF := GF) i γl γ) := by
  unfold uartPort; infer_instance

/-- The KERNEL port's bundle: what `printk`'s cone holds (`prputc` writes
`uarts[1]`). -/
def isTxLock [CurCtx] (γl : GName) (γ : UartNames) : IProp GF := uartPort .uart1 γl γ

instance isTxLock_persistent [CurCtx] (γl : GName) (γ : UartNames) : Persistent (isTxLock (GF := GF) γl γ) := by
  unfold isTxLock; infer_instance

end

/-! ## The port's ONE-SHOT

`Xv6.PlicInv` allocates the PLIC's invariant at POWER-ON, when no port has
been initialised and there is no `rxTok` anywhere; the slot of a PLIC
source may therefore be in one of two regimes, and `UartNames.init` is the
ghost that says which:

* `uartPreinit γ` -- the whole ghost variable at `false`: the port has not
  been through `uartinit`, so the PLIC slot of its source carries nothing;
* `uartInited γ` -- the SAME variable, persistently at `true`: `uartinit`
  has run, so the slot carries the port's receive token whenever the source
  is pending and unclaimed.

The two are contradictory (`uartPreinit_inited_False`), and the boot client
flips the regime once, irreversibly, with `uartPreinit_deposit`.  Nothing
in the `uartinit` cone mentions either: the flip happens beside it. -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- Port `γ`'s one-shot, unfired: an EXCLUSIVE whole (the boot client's). -/
def uartPreinit (γ : UartNames) : IProp GF := γ.init ↪VAR{.own 1} false

/-- Port `γ`'s one-shot, fired: persistent, and freely duplicated by every
client of the PLIC's slots. -/
def uartInited (γ : UartNames) : IProp GF := γ.init ↪VAR{.discard} true

instance uartInited_persistent (γ : UartNames) : Persistent (uartInited (GF := GF) γ) := by
  unfold uartInited; infer_instance

instance uartPreinit_timeless (γ : UartNames) : Timeless (uartPreinit (GF := GF) γ) := by
  unfold uartPreinit; infer_instance

instance uartInited_timeless (γ : UartNames) : Timeless (uartInited (GF := GF) γ) := by
  unfold uartInited; infer_instance

/-- The two regimes exclude each other: the ghost variable cannot be both
`false` and `true`. -/
theorem uartPreinit_inited_False (γ : UartNames) :
    uartPreinit (GF := GF) γ ∗ uartInited γ ⊢ False := by
  unfold uartPreinit uartInited
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ.init false (.own 1) true .discard $$ H1 H2
  exact absurd h (by decide)

/-- **The flip**: the boot client spends the whole variable and mints the
persistent marker.  One-way: after this no update is possible. -/
theorem uartPreinit_deposit (γ : UartNames) :
    uartPreinit (GF := GF) γ ⊢ |==> uartInited γ := by
  unfold uartPreinit uartInited
  iintro H
  imod (ghost_var_update true γ.init false) $$ H with H
  iapply ghost_var_persist γ.init (.own 1) true $$ H

end

end Xv6
