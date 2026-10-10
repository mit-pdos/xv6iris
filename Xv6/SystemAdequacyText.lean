/-
**THE SYSTEM THEOREM, THE KERNEL'S READ-ONLY WINDOW PRISTINE** (weak-allocproc
plan §C Stage 0, item W3, option (A); PROGRESS-W3.md).

* §1 **`xv6PowerAdequacyGenUT`**: `SystemAdequacy.xv6PowerAdequacyGenU`'s
  twin over `MachCSL.riscvPowerAdequacyT` at the window `[bcRoLo, bcRoHi)`
  (`.text`, `.rodata`, `.eh_frame`) and `SystemBootEraText.xv6BootEraT`:
  the trace slot `Pt`/`Pon` is also at the registry's gname, `Hobs` leaves
  `Pon` at a power-on and the new hook `HtextRec` restores `Pt`.  A
  near-copy.
* §2 THE TEXT LEDGER: the trace slot of the text theorem is the ledger
  `obsLedgerAt (textRecR γreg) γobs` (`textPt`), whose record at a history
  `h` with `k + 1 = obsBoots h` boots is `textRecK γreg (k + 1)`: the era
  generation `k` runs, registered, with its window persisted
  (`winRoPre E (imgFlat bootImage) bcRoLo bcRoHi`, which is `textRo E` at
  the record literal).  Its hooks: the power step `textLedger_step` (at a
  power-on the record is dropped, `textPon`), the record `textLedger_rec`,
  the user and device events keep the boot count (`textRecR_snoc`, the
  ledger permit `xv6TextTriv_perm`), and the final hook `textLedger_phi`:
  with the power on, `obsWf` says the history has `g.gen + 1` boots, so the
  record names the era `powerInterp` runs and `powerInterp_textPristine`
  gives `textPristine g`.
* §3 **`xv6TextAdequacy`** (the unit application, as `xv6PowerAdequacy`,
  with `phi g := g.pow = true → textPristine g`), `xv6TextAdequacyImg` (at
  the literal mkfs image) and **`xv6TextAdequacy_xv6GF`** (at the concrete
  functor list); the closed root is `LinkTextAdequacy.xv6TextAdequacy_closed`.

Every existing statement is unchanged [OWN.9]; the machine semantics and
the trusted assumptions are `xv6FsAdequacy_xv6GF`'s.
-/
import Xv6.SystemAdequacy
import Xv6.SystemBootEraText
import Xv6.TextPristine

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL
open Iris.ProgramLogic Language.Notation PrimStep

/-! ## §1 THE SYSTEM THEOREM, the window recorded, at a generic application -/

section gen
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF] [Xv6G GF] [WchGpre GF]
  [CtokG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF]
  [IcboxG GF] [SleepLockG GF] [BcacheG GF] [OffboxG GF] [OffboxBoxG GF] [FileG GF]

/-- **THE SYSTEM THEOREM, THE READ-ONLY WINDOW RECORDED**
(`xv6PowerAdequacyGenU`'s twin, over `MachCSL.riscvPowerAdequacyT` at
`[bcRoLo, bcRoHi)` and `xv6BootEraT`): the trace slot `Pt`/`Pon` is at the
registry's gname too, `Hobs` leaves `Pon` at a power-on and `HtextRec`
restores `Pt` from the era's registry element and its persisted window.
Every other parameter is `xv6PowerAdequacyGenU`'s. -/
theorem xv6PowerAdequacyGenUT (g : GState) (sb : FsSb) (nib : Nat) (cov : ExtTreeSet Nat compare)
    -- THE BIRTH (Rocq SY3-A1): its yield split between the crash slot's era-0
    -- copy (`Cls`) and the trace slot (`Clt`); handed the machine's four fixed
    -- gnames, `Born` what it says of where it kept them
    (CT : Type) (Cls Clt : CT → IProp GF)
    (Born : GName → GName → GName → GName → CT → Prop)
    (Hbirth : ∀ γd γsw γreg γst : GName,
      ⊢@{IProp GF} |==> ∃ c : CT, ⌜Born γd γsw γreg γst c⌝ ∗ Cls c ∗ Clt c)
    (N : Type) (appFs : CT → N → Aview → IProp GF)
    (appBoot : CT → Nat → N → IProp GF)
    -- THE DURABLE-COPY PREDICATE (Rocq `app_okc`, SY3-A3b)
    (appOkc : CT → N → Prop)
    (Ai : CT → AppIface GF)
    -- THE ERA'S TURN IN FOUR STAGES (Rocq SY3-A1): the power-on step's yield
    -- `Tnn`, the swap's `Tnn'`, the return path's `Tnn''`, `<init>`'s `TnnInit`
    (Tnn Tnn' Tnn'' TnnInit : CT → Nat → IProp GF)
    -- THE TWO SYNC SLOTS (Rocq sync K3-2), at the fixed part alone
    (Tk : CT → Nat → IProp GF) (Hk : CT → Nat → IProp GF → IProp GF)
    -- THE FOUNDING (Rocq `Hfound`, SY3-A1)
    (Hfound : ∀ (c : CT) (k : Nat),
      ⊢@{IProp GF} Tnn'' c (k + 1) -∗ |==> (Tk c k ∗ TnnInit c (k + 1)))
    -- THE ERA'S RECORD PREDICATE (Rocq `Ok`/`Hboot_ok`, SY3-A1 re-cut)
    (Ok : CT → Nat → N → Prop)
    (Hboot_ok : ∀ (c : CT) (k : Nat) (r : N), appBoot c k r ⊢@{IProp GF} ⌜Ok c k r⌝)
    -- THE MERGE (Rocq `Happ_merge`, SY3-K2 / SY3-A1): at any machine record
    -- whose generation counter is the pre-structure's, at a fixed part born at
    -- that record's own four gnames
    (Happ_merge : ∀ [F : MachFixedGS hlc GF] (c : CT) (k : Nat),
      MachFixedGS.mono (hlc := hlc) (GF := GF) = MachGpreS.mono_pre (hlc := hlc) →
      Born (MachFixedGS.diskName (hlc := hlc) (GF := GF)) (MachFixedGS.swapName (hlc := hlc) (GF := GF))
        (MachFixedGS.registryName (hlc := hlc) (GF := GF))
        (MachFixedGS.startName (hlc := hlc) (GF := GF)) c →
      ⊢@{IProp GF} appMergeRaw (hlc := hlc) (appFs c) (Ok c (k + 1)) (appOkc c) (Tk c k) k)
    -- THE SYNC RUNNER (Rocq `Happ_sync_run`, K3-3), at any machine record
    (Happ_sync_run : ∀ [F : MachFixedGS hlc GF] (c : CT) (k : Nat),
      ⊢@{IProp GF} appSyncRunRaw (hlc := hlc) (appFs c) (Ok c (k + 1)) (appOkc c) (Tk c k) (Hk c k))
    -- THE POWER-ON TRANSPORT (Rocq `Happ_boot`, SY3-A1 / SY3-A3bc)
    (Happ_boot : ∀ (c : CT) (gen : Nat) (γd γsw γreg γst : GName), Born γd γsw γreg γst c →
      ⊢@{IProp GF} appXferBootRaw (MachGpreS.mono_pre (hlc := hlc)) (appFs c) (appOkc c)
        (appBoot c (gen + 1)) (Tnn c (gen + 1)) (Tnn' c (gen + 1)) γst gen)
    -- ERA 0, out of the birth's crash-slot part (Rocq SY3-A1)
    (Happ_init : ∀ c : CT, Cls c ⊢@{IProp GF} |==> ∃ r : N, ⌜appOkc c r⌝ ∗
      appFs c r (absView (imgState (fsBlocks (diskOf g.m.devs)) sb nib).fssInodes))
    -- THE RECORD'S ENTER JUSTIFICATION AND FILING CLAIMS (NI M2-W4)
    (Uf : Option (Nat × Obs) → Obs → Prop) (hUf : ∀ ox e, niFit ox e → Uf ox e)
    (Ucr : CT → Nat → IProp GF) (Ucx : CT → Nat → Obs → IProp GF) (Uco : CT → IProp GF)
    (hUfork : ∀ (c : CT) (i : Nat) (x : Obs), niForkExit x = true → Ucx c i x ⊢@{IProp GF} Uco c)
    -- THE RECORD'S EVIDENCE AND REGISTRATION (NI M2-X1): `uEvid` (built from
    -- a citation, `hUevid`, or an origin's fit, `hUevidNone`), `uEraTok` (the
    -- power-on's registration ticket, shot by `hUreg`) and `uEraAnchor`
    (Ue : CT → Option (Nat × Obs) → Obs → IProp GF) (HUe : ∀ c ox e, Persistent (Ue c ox e))
    (Uet : CT → Nat → IProp GF) (Uea : CT → Nat → List GName → IProp GF)
    (HUea : ∀ c k ns, Persistent (Uea c k ns))
    (hUreg : ∀ (c : CT) (k : Nat) (ns : List GName), Uet c k ⊢@{IProp GF} |==> Uea c k ns)
    (hUevid : ∀ (c : CT) (i : Nat) (x e : Obs) (cc : Option (Nat × UIota)) (u : NiUh),
      niFitEv (some (i, x)) e cc u → niCiteResRaw (Uea c) cc ∗ niUhRes u ⊢@{IProp GF} Ue c (some (i, x)) e)
    (hUevidNone : ∀ (c : CT) (e : Obs) (u : NiUh), niFitEv none e none u → niUhRes u ⊢@{IProp GF} Ue c none e)
    -- THE TRACE SLOT at the registry's name too, and its power-on content
    -- before the text record (`MachCSL.riscvPowerAdequacyT`)
    (Pt : GName → GName → CT → IProp GF) (Pon : GName → GName → CT → List Obs → IProp GF)
    (Hinit_boot : ∀ (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : CT)
        (T : List Obs),
      letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart (Ai c) Hinv γgen
        γstart γreg γd γsw γobs γhist c T (Pt γreg γobs c) (Tk c) (Hk c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c))
      EraInitBoot (hlc := hlc) N appFs appBoot TnnInit c)
    (Happ_echo : ∀ (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : CT)
        (T : List Obs),
      letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart (Ai c) Hinv γgen
        γstart γreg γd γsw γobs γhist c T (Pt γreg γobs c) (Tk c) (Hk c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c))
      EraEcho (hlc := hlc) (GF := GF))
    (HPt : ∀ (γreg γobs : GName) (c : CT),
      Clt c ∗ (γobs ↪VAR{.own (1 : Qp).half} ([] : List Obs)) ⊢@{IProp GF} |==> Pt γreg γobs c)
    (Hobs : ∀ (γd γreg γobs : GName) (c : CT) (h : List Obs) (on : Bool) (dk : Nat → BitVec 8),
      traceShape h on →
      diskImgAuthSized γd XV6_DISK_BYTES dk ∗ ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} h)
        ⊢@{IProp GF} |==> ◇ (diskImgAuthSized γd XV6_DISK_BYTES dk ∗
          (if on then iprop(▷ Pt γreg γobs c) else iprop(▷ Pon γreg γobs c h)) ∗
          (γobs ↪VAR{.own (1 : Qp).half} (h ++ [powerEv on])) ∗
          (if on then iprop(emp)
           else iprop((Ai c).cons (obsBoots h + 1) [] ⟨[], [], [], none⟩ ∗
             Tnn c (obsBoots h + 1) ∗ Uco c ∗ Uet c (obsBoots h + 1)))))
    -- THE TEXT RECORD (weak-allocproc W3): the era's registry element and its
    -- persisted read-only window restore the slot
    (HtextRec : ∀ (γreg γobs : GName) (c : CT) (h : List Obs) (E : EraGS),
      ▷ Pon γreg γobs c h ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])) ∗
          (γreg ↪◯MAP[obsBoots h]{.discard} E) ∗ winRoPre E (imgFlat bootImage) bcRoLo bcRoHi ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn]))))
    -- THE RETURN PATH (Rocq `Hback`, SY3-A1 re-cut)
    (Hback : ∀ (γreg γobs : GName) (c : CT) (h : List Obs),
      ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])) ∗
          Tnn' c (obsBoots h + 1) ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])) ∗
          Tnn'' c (obsBoots h + 1)))
    -- THE USER-EVENT HOOKS (NI M2-W1, split by M2-W2a): the trace slot
    -- accepts a hart's user exit, and a user entry with the cited receipt's
    -- reading (`MachCSL.riscvPowerAdequacy`'s `HuserExit`/`HuserEnter`; the
    -- system record's `uFit` is blind -- the kernel files its evidence
    -- against it through `NiFitIs` (NI M2-W2c) -- so the entry hook is handed
    -- no justification)
    (HuserExit : ∀ (γreg γobs : GName) (c : CT) (h : List Obs) (e : Obs), isUExit e = true →
      ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [e])) ∗
          Ucr c h.length ∗ Ucx c h.length e))
    (HuserEnter : ∀ (γreg γobs : GName) (c : CT) (h : List Obs) (e : Obs) (ox : Option (Nat × Obs)),
      isUEnter e = true → Uf ox e → (∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) →
      uClaimForRaw (Ucr c) (Uco c) ox ∗ Ue c ox e ∗ ▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
        |==> ◇ (▷ Pt γreg γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [e]))))
    (Hperm : ∀ (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : CT)
        (T : List Obs),
      letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart (Ai c) Hinv γgen
        γstart γreg γd γsw γobs γhist c T (Pt γreg γobs c) (Tk c) (Hk c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c))
      EraPerm (hlc := hlc) (GF := GF))
    (phi : GState → List Obs → Prop)
    (Hphi : ∀ (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : CT)
        (T : List Obs) (g' : GState) (h : List Obs),
      @powerInterp hlc GF (xv6FixedGSU N appFs appOkc cov sb.sbLogstart (Ai c) Hinv γgen γstart γreg
          γd γsw γobs γhist c T (Pt γreg γobs c) (Tk c) (Hk c) Uf (Ucr c) (Ucx c) (Uco c)
          (Ue c) (HUe c) (Uet c) (Uea c) (HUea c)) g' ∗
        (γobs ↪VAR{.own (1 : Qp).half} h) ∗ ⌜obsWf h g'⌝ ∗
        ▷ xv6Slot N appFs appOkc cov sb.sbLogstart γd γsw γreg γstart c ∗ ▷ Pt γreg γobs c ⊢@{IProp GF}
        ◇ ⌜phi g' h⌝)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false)
    (Himg : fsBootImageWf (diskOf g.m.devs) XV6_DISK_BYTES sb nib cov)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ phi g2 κs := by
  obtain ⟨hcovin, hlogsub, hls2⟩ := covFacts_ofImage _ _ sb nib cov Himg
  refine riscvPowerAdequacyT (hlc := hlc) (GF := GF) bcRoLo bcRoHi XV6_DISK_BYTES g CT Cls Clt Born Hbirth
    (fun γd γsw γreg γst c => xv6Slot N appFs appOkc cov sb.sbLogstart γd γsw γreg γst c)
    (xv6Slot_alloc N appFs appOkc Cls (diskOf g.m.devs) sb nib cov Himg Happ_init)
    Tk Hk
    (fsBootPure cov sb.sbLogstart)
    (xv6Slot_project N appFs appOkc cov sb.sbLogstart)
    (fun dk => mirrorOf (fsBlocks dk))
    (fun c gen dk => xv6Lend N appFs appBoot cov sb.sbLogstart c gen dk)
    Tnn Tnn' Tnn''
    (xv6Slot_swap N appFs appOkc appBoot cov sb.sbLogstart Born Tnn Tnn' Happ_boot)
    Pt Pon (fun c => (Ai c).tag) (fun c h => (Ai c).tag_persistent h) (fun c h => (Ai c).tag_timeless h)
    (fun c => (Ai c).kill) (fun c => (Ai c).kill_persistent) (fun c => (Ai c).kill_timeless)
    (fun c => (Ai c).cons) (fun c k h H => (Ai c).cons_timeless k h H)
    (fun c => (Ai c).wild) (fun c k => (Ai c).wild_persistent k) (fun c k => (Ai c).wild_timeless k)
    (fun c => (Ai c).rdwild) (fun c k => (Ai c).rdwild_persistent k)
    (fun c k => (Ai c).rdwild_timeless k)
    Uf Ucr Ucx Uco Ue HUe Uet Uea HUea HPt Hobs HtextRec Hback HuserExit HuserEnter
    phi Hphi Hgen0 Hpow ?_ n κs t2 g2 hsteps
  intro F Hinv γgen γstart γreg γd γsw γobs γhist c T hF hborn E gen σ hbf hdv hpp
  -- the merge and the runner at the record literal, read off the equations
  -- the literal satisfies by `rfl` (Rocq's `Hmergefix`/`Hrunfix`)
  have hmerge := fun k => @Happ_merge F c k (by rw [hF]) (by rw [hF]; exact hborn)
  have hrun := fun k => @Happ_sync_run F c k
  subst hF
  exact xv6BootEraT N appFs appBoot Tnn'' TnnInit sb cov (Ai c) Hinv γgen γstart γreg γd γsw γobs
    γhist c T (Pt γreg γobs c) (Tk c) (Hk c) Uf hUf (Ucr c) (Ucx c) (Uco c) (hUfork c)
    (Ue c) (HUe c) (Uet c) (Uea c) (HUea c) (hUreg c) (hUevid c) (hUevidNone c)
    (Ok c) (Hboot_ok c) appOkc hmerge (Hfound c) hrun
    (Hinit_boot Hinv γgen γstart γreg γd γsw γobs γhist c T)
    (Happ_echo Hinv γgen γstart γreg γd γsw γobs γhist c T)
    (Hperm Hinv γgen γstart γreg γd γsw γobs γhist c T)
    E gen σ hbf hdv hpp hcovin hlogsub hls2

end gen

/-! ## §2 THE TEXT LEDGER -/

section ledger
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF]

/-- The text record at `k` boots: none before the first; after `k + 1`, the
era generation `k` runs, registered at `γreg`, with its read-only window
persisted. -/
def textRecK (γreg : GName) : Nat → IProp GF
  | 0 => iprop(emp)
  | k + 1 => iprop(∃ E : EraGS, (γreg ↪◯MAP[k]{.discard} E) ∗ winRoPre E (imgFlat bootImage) bcRoLo bcRoHi)

instance textRecK_persistent (γreg : GName) (k : Nat) : Persistent (textRecK (GF := GF) γreg k) := by
  cases k <;> simp only [textRecK] <;> infer_instance

instance textRecK_timeless (γreg : GName) (k : Nat) : Timeless (textRecK (GF := GF) γreg k) := by
  cases k <;> simp only [textRecK] <;> infer_instance

/-- The text record at a history: at its boot count. -/
def textRecR (γreg : GName) (h : List Obs) : IProp GF := textRecK γreg (obsBoots h)

instance textRecR_persistent (γreg : GName) (h : List Obs) : Persistent (textRecR (GF := GF) γreg h) := by
  unfold textRecR; infer_instance

instance textRecR_timeless (γreg : GName) (h : List Obs) : Timeless (textRecR (GF := GF) γreg h) := by
  unfold textRecR; infer_instance

/-- The text theorem's trace slot: the ledger of the text record. -/
def textPt (γreg γobs : GName) : IProp GF := obsLedgerAt (textRecR γreg) γobs

/-- ...and its pending content at a power-on, before the record: the slot's
half at the extended history, the record dropped. -/
def textPon (γobs : GName) (h : List Obs) : IProp GF :=
  γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])

theorem textRecR_nil (γreg : GName) : textRecR (GF := GF) γreg [] = iprop(emp) := rfl

/-- An event other than a power-on keeps the record. -/
theorem textRecR_snoc (γreg : GName) (h : List Obs) (e : Obs) (he : e ≠ Obs.powerOn) :
    textRecR (GF := GF) γreg (h ++ [e]) = textRecR γreg h := by
  unfold textRecR
  rw [obsBoots_app]
  cases e <;> simp_all [obsBoots]

theorem textRecR_on (γreg : GName) (h : List Obs) :
    textRecR (GF := GF) γreg (h ++ [Obs.powerOn]) = textRecK γreg (obsBoots h + 1) := by
  unfold textRecR
  rw [obsBoots_app]
  rfl

theorem textRecR_up (γreg : GName) (h : List Obs) (e : Obs) (he : e ≠ Obs.powerOn) :
    textRecR (GF := GF) γreg h ⊢ |==> textRecR γreg (h ++ [e]) := by
  rw [textRecR_snoc γreg h e he]
  exact BIUpdate.intro

theorem textRec_ne_uexit {e : Obs} (he : isUExit e = true) : e ≠ Obs.powerOn := by
  rintro rfl; simp [isUExit] at he

theorem textRec_ne_uenter {e : Obs} (he : isUEnter e = true) : e ≠ Obs.powerOn := by
  rintro rfl; simp [isUEnter] at he

/-- The slot at birth: the empty history has no record. -/
theorem textPt_alloc (γreg γobs : GName) :
    iprop(True) ∗ (γobs ↪VAR{.own (1 : Qp).half} ([] : List Obs)) ⊢@{IProp GF} |==> textPt γreg γobs :=
  obsLedgerAt_alloc_cl (textRecR γreg) γobs iprop(True) (by
    rw [textRecR_nil]
    iintro _
    imodintro
    iempintro)

/-- **THE POWER STEP** (`Hobs`, at the unit application's yields): at a power
loss the ledger moves and keeps the record; at a power-on it is left
pending (`textPon`). -/
theorem textLedger_step (γd γreg γobs : GName) (h : List Obs) (on : Bool) (dk : Nat → BitVec 8) :
    diskImgAuthSized γd XV6_DISK_BYTES dk ∗ ▷ textPt (GF := GF) γreg γobs ∗ (γobs ↪VAR{.own (1 : Qp).half} h)
      ⊢@{IProp GF} |==> ◇ (diskImgAuthSized γd XV6_DISK_BYTES dk ∗
        (if on then iprop(▷ textPt γreg γobs) else iprop(▷ textPon γobs h)) ∗
        (γobs ↪VAR{.own (1 : Qp).half} (h ++ [powerEv on])) ∗
        (if on then iprop(emp)
         else iprop(consResTriv (GF := GF) (obsBoots h + 1) [] ⟨[], [], [], none⟩ ∗
           iprop(emp) ∗ iprop(emp) ∗ iprop(emp)))) := by
  unfold textPt obsLedgerAt
  iintro ⟨Hdk, ⟨%h', >Hfrag, >#HR⟩, Hauth⟩
  ihave %he := ghost_var_agree γobs h' _ h _ $$ Hfrag Hauth
  subst he
  imod ghost_var_update_halves (h' ++ [powerEv on]) γobs h' h' $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
  imodintro
  imodintro
  iframe Hdk
  cases on
  · simp only [powerEv, Bool.false_eq_true, ↓reduceIte]
    isplitl [Hfrag]
    · inext
      unfold textPon
      iexact Hfrag
    isplitl [Hauth]
    · iexact Hauth
    isplitl []
    · iapply (show ⊢@{IProp GF} consResTriv (GF := GF) (obsBoots h' + 1) [] ⟨[], [], [], none⟩ from .rfl)
    isplitl []
    · iempintro
    isplitl []
    · iempintro
    iempintro
  · simp only [powerEv, ↓reduceIte]
    isplitl [Hfrag]
    · inext
      iexists (h' ++ [Obs.powerOff])
      iframe Hfrag
      rw [textRecR_snoc γreg h' Obs.powerOff (by simp)]
      iexact HR
    isplitl [Hauth]
    · iexact Hauth
    iempintro

/-- **THE TEXT RECORD** (`HtextRec`): the pending slot, the era's registry
element at the history's boot count and its persisted window are the slot
at the extended history. -/
theorem textLedger_rec (γreg γobs : GName) (h : List Obs) (E : EraGS) :
    ▷ textPon (GF := GF) γobs h ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn])) ∗
        (γreg ↪◯MAP[obsBoots h]{.discard} E) ∗ winRoPre E (imgFlat bootImage) bcRoLo bcRoHi ⊢@{IProp GF}
      |==> ◇ (▷ textPt γreg γobs ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [Obs.powerOn]))) := by
  iintro ⟨Hp, Hh, #Hreg, #Hw⟩
  imodintro
  imodintro
  isplitl [Hp]
  · inext
    unfold textPt obsLedgerAt textPon
    iexists (h ++ [Obs.powerOn])
    iframe Hp
    rw [textRecR_on]
    simp only [textRecK]
    iexists E
    iframe Hreg Hw
  · iexact Hh

end ledger

/-! ## §3 THE UNIT INSTANCE, the window pristine -/

section unit
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF] [Xv6G GF] [WchGpre GF]
  [CtokG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF]
  [IcboxG GF] [SleepLockG GF] [BcacheG GF] [OffboxG GF] [OffboxBoxG GF] [FileG GF]

/-- `xv6Triv_initBoot` at any trace slot `Ptp` (its proof never reads the slot). -/
theorem xv6TrivP_initBoot (US : USER) (cov : ExtTreeSet Nat compare) (ls : Nat) (Ptp : IProp GF)
    (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : Unit) (T : List Obs) :
    letI : MachFixedGS hlc GF := (xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
      Hinv γgen γstart γreg γd γsw γobs γhist c T Ptp
      (appTrivTk c) (appTrivHk c))
    EraInitBoot (hlc := hlc) (GF := GF) Unit (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(emp))
      (fun _ _ => iprop(emp)) c := by
  intro E gen cP cI W HFd HBs HIr I Fc r
  letI : MachFixedGS hlc GF := xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
      Hinv γgen γstart γreg γd γsw γobs γhist c T Ptp
      (appTrivTk c) (appTrivHk c)
  letI : MachGS hlc GF := MachGS.ofEra E gen cP cI
  letI : Appcfg GF := ⟨Unit, fun _ _ => iprop(True), r⟩
  have hsup : ⊢@{IProp GF} appSup := appSup_of_triv (fun _ _ => .rfl)
  have hkc : ⊢@{IProp GF} uKillCred (hlc := hlc) := by
    show ⊢@{IProp GF} iprop(True)
    exact BI.true_intro
  have hlic : ⊢@{IProp GF} consLicence (hlc := hlc) := consLicence_triv rfl
  have hgen : ⊢@{IProp GF} □ uexecWp (hlc := hlc) (GF := GF) := (UexecGen US).uexec_wp_gen
  iintro _ _ _
  ihave #Hs := hsup
  ihave #Hk := hkc
  ihave #Hl := hlic
  ihave #Hg := hgen
  imodintro
  iapply initBootBundle_of_mint (hlc := hlc) (GF := GF) ROOTINO ROOTINO seccAll (List.replicate NOFILE FdState.closed)
    $$ Hs Hk Hl Hg

/-- `xv6Triv_echo` at any trace slot `Ptp`. -/
theorem xv6TrivP_echo (cov : ExtTreeSet Nat compare) (ls : Nat) (Ptp : IProp GF)
    (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : Unit) (T : List Obs) :
    letI : MachFixedGS hlc GF := (xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
      Hinv γgen γstart γreg γd γsw γobs γhist c T Ptp
      (appTrivTk c) (appTrivHk c))
    EraEcho (hlc := hlc) (GF := GF) := by
  intro E gen cP cI
  letI : MachFixedGS hlc GF := xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
      Hinv γgen γstart γreg γd γsw γobs γhist c T Ptp
      (appTrivTk c) (appTrivHk c)
  letI : MachGS hlc GF := MachGS.ofEra E gen cP cI
  exact consEchoShift_triv rfl


/-- The text ledger's port permits (`xv6Triv_perm`'s twin, through
`uartObsPermit_ledger`): a device event keeps the boot count, so the record. -/
theorem xv6TextTriv_perm (cov : ExtTreeSet Nat compare) (ls : Nat)
    (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : Unit) (T : List Obs) :
    letI : MachFixedGS hlc GF := (xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
      Hinv γgen γstart γreg γd γsw γobs γhist c T (textPt γreg γobs)
      (appTrivTk c) (appTrivHk c))
    EraPerm (hlc := hlc) (GF := GF) := by
  intro E gen cP cI Fc i γ _
  letI : MachFixedGS hlc GF := xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
      Hinv γgen γstart γreg γd γsw γobs γhist c T (textPt γreg γobs)
      (appTrivTk c) (appTrivHk c)
  letI : MachGS hlc GF := MachGS.ofEra E gen cP cI
  refine uartObsPermit_ledger i (textRecR γreg) rxTagTriv consResTriv γ rfl rfl rfl ?_ ?_
  · iintro !> %h %b %u %u' %ho %H %_ Hc Hg HR
    imodintro
    rw [textRecR_snoc γreg h _ (by simp)]
    iframe Hc Hg HR
  · iintro !> %h %b %u %u' %_ Hg HR
    imodintro
    rw [textRecR_snoc γreg h _ (by simp)]
    iframe Hg HR
    unfold rxTagTriv
    itrivial

/-- The ledger, with the power on, records the era registered at the
current generation (`obsWf`: the history has `g'.gen + 1` boots). -/
theorem textLedger_open (γreg γobs : GName) (h : List Obs) (g' : GState) (hwf : obsWf h g')
    (hpw : g'.pow = true) :
    ▷ textPt (GF := GF) γreg γobs ∗ (γobs ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
      ◇ ∃ E : EraGS, (γreg ↪◯MAP[g'.gen]{.discard} E) ∗ winRoPre E (imgFlat bootImage) bcRoLo bcRoHi := by
  have hb : obsBoots h = g'.gen + 1 := by
    have := hwf.2.1; rw [hpw] at this; simpa using this
  unfold textPt obsLedgerAt
  iintro ⟨⟨%h', >Hfrag, >#HR⟩, Hh⟩
  ihave %he := ghost_var_agree γobs h' _ h _ $$ Hfrag Hh
  subst he
  rw [textRecR, hb]
  simp only [textRecK]
  imodintro
  iexact HR

/-- `powerInterp_textPristine` at the text theorem's record literal, its
registry element and window spelled at the raw gname. -/
theorem textLedger_core (cov : ExtTreeSet Nat compare) (ls : Nat)
    (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : Unit) (T : List Obs)
    (g' : GState) (E : EraGS) :
    @powerInterp hlc GF (xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
        Hinv γgen γstart γreg γd γsw γobs γhist c T (textPt γreg γobs) (appTrivTk c) (appTrivHk c)) g' ∗
      (γreg ↪◯MAP[g'.gen]{.discard} E) ∗ winRoPre E (imgFlat bootImage) bcRoLo bcRoHi ⊢@{IProp GF}
      ⌜g'.pow = true → textPristine g'⌝ :=
  sep_assoc.2.trans ((sep_mono_left (wand_elim (@powerInterp_textPristine hlc GF
    (xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
      Hinv γgen γstart γreg γd γsw γobs γhist c T (textPt γreg γobs) (appTrivTk c) (appTrivHk c)) g' E))).trans
    wand_elim_left)

/-- **THE FINAL HOOK**: with the power on, the history has `g'.gen + 1` boots
(`obsWf`), so the ledger's record names the era registered at the current
generation, with its window persisted; `powerInterp_textPristine`. -/
theorem textLedger_phi (cov : ExtTreeSet Nat compare) (ls : Nat)
    (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName) (c : Unit) (T : List Obs)
    (g' : GState) (h : List Obs) :
    @powerInterp hlc GF (xv6FixedGS Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls (appIfaceTriv GF)
        Hinv γgen γstart γreg γd γsw γobs γhist c T (textPt γreg γobs) (appTrivTk c) (appTrivHk c)) g' ∗
      (γobs ↪VAR{.own (1 : Qp).half} h) ∗ ⌜obsWf h g'⌝ ∗
      ▷ xv6Slot Unit (fun _ _ _ => iprop(True)) appTrivOkc cov ls γd γsw γreg γstart c ∗
      ▷ textPt γreg γobs ⊢@{IProp GF}
      ◇ ⌜g'.pow = true → textPristine g'⌝ := by
  iintro ⟨Hsi, Hh, %hwf, -, HP⟩
  cases hpw : g'.pow
  · imodintro
    ipureintro
    intro hc; cases hc
  · imod textLedger_open γreg γobs h g' hwf hpw $$ [HP Hh] with ⟨%E, #Hreg, #Hw⟩
    · iframe HP Hh
    ihave %ht := textLedger_core cov ls Hinv γgen γstart γreg γd γsw γobs γhist c T g' E $$ [Hsi]
    · iframe Hsi Hreg Hw
    imodintro
    ipureintro
    exact fun _ => ht hpw

include hlc GF in
/-- **THE SYSTEM THEOREM, THE KERNEL'S READ-ONLY WINDOW PRISTINE** (the unit
application, as `xv6PowerAdequacy`, at the text ledger): from a powered-off,
never-booted machine whose disk holds a well-formed file system image,
under ANY schedule, every reachable configuration has only reducible
threads, and whenever the power is on every byte of `[bcRoLo, bcRoHi)` has
the fresh era's history, the boot image's byte at timestamp 0
(`textPristine`).  `USER` is the only assumed interface. -/
theorem xv6TextAdequacy (US : USER) (g : GState) (sb : FsSb) (nib : Nat)
    (cov : ExtTreeSet Nat compare)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false)
    (Himg : fsBootImageWf (diskOf g.m.devs) XV6_DISK_BYTES sb nib cov)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → textPristine g2) :=
  xv6PowerAdequacyGenUT (hlc := hlc) (GF := GF) g sb nib cov
    Unit appTrivCls (fun _ => iprop(True)) appTrivBorn
    (fun _ _ _ _ => by
      imodintro
      iexists ()
      isplitr
      · ipureintro; trivial
      isplitl [] <;> itrivial)
    Unit (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(emp)) appTrivOkc (fun _ => appIfaceTriv GF)
    (fun _ _ => iprop(emp)) (fun _ _ => iprop(emp)) (fun _ _ => iprop(emp)) (fun _ _ => iprop(emp))
    appTrivTk appTrivHk
    (fun c k => appTriv_found c k _)
    appTrivOk (fun _ _ _ => by iintro _; ipureintro; trivial)
    (fun c k _ _ => appMergeRaw_ofXfer _ _ _ _ _ (fun _ => trivial) (fun _ => trivial)
      (appXferRaw_triv _ (fun _ _ => .rfl)))
    (fun c k => appTriv_syncRun _ _ _ c k)
    (fun _ _ _ _ _ _ _ => appXferBootRaw_triv _ _ _ _ _ _ (fun _ _ => .rfl))
    (fun _ => by
      iintro _
      imodintro
      iexists ()
      isplitr
      · ipureintro; trivial
      itrivial)
    -- the system record is blind and mints no filing claims (NI M2-W2d), and
    -- carries no evidence and no registration (NI M2-X1), as `xv6PowerAdequacyGen`
    (fun _ _ => True) (fun _ _ _ => trivial)
    (fun _ _ => iprop(emp)) (fun _ _ _ => iprop(emp)) (fun _ => iprop(emp)) (fun _ _ _ _ => .rfl)
    (fun _ _ _ => iprop(emp)) (fun _ _ _ => inferInstance) (fun _ _ => iprop(emp))
    (fun _ _ _ => iprop(emp)) (fun _ _ _ => inferInstance) (fun _ _ _ => BIUpdate.intro)
    (fun _ _ _ _ _ _ _ => Affine.affine) (fun _ _ _ _ => Affine.affine)
    -- THE TEXT LEDGER
    (fun γreg γobs _ => textPt γreg γobs) (fun _ γobs _ h => textPon γobs h)
    (fun Hinv γgen γstart γreg γd γsw γobs γhist c T =>
      xv6TrivP_initBoot US cov sb.sbLogstart (textPt γreg γobs) Hinv γgen γstart γreg γd γsw γobs γhist c T)
    (fun Hinv γgen γstart γreg γd γsw γobs γhist c T =>
      xv6TrivP_echo cov sb.sbLogstart (textPt γreg γobs) Hinv γgen γstart γreg γd γsw γobs γhist c T)
    (fun γreg γobs _ => textPt_alloc γreg γobs)
    (fun γd γreg γobs _ h on dk _ => textLedger_step γd γreg γobs h on dk)
    (fun γreg γobs _ h E => textLedger_rec γreg γobs h E)
    (fun _ _ _ _ => backId _ _ _)
    (fun γreg γobs _ h e he => uexitHook_emp _ _ _
      (obsLedgerAt_uexit (textRecR γreg) (fun h e he => textRecR_up γreg h e (textRec_ne_uexit he))
        γobs h e he))
    (fun γreg γobs _ h e _ he _ _ => uenterHook_drop _ _ _ _ _
      (obsLedgerAt_userP (textRecR γreg) (fun _ e => isUEnter e = true)
        (fun h e he => textRecR_up γreg h e (textRec_ne_uenter he)) γobs h e he))
    (fun Hinv γgen γstart γreg γd γsw γobs γhist c T =>
      xv6TextTriv_perm cov sb.sbLogstart Hinv γgen γstart γreg γd γsw γobs γhist c T)
    (fun g' _ => g'.pow = true → textPristine g')
    (fun Hinv γgen γstart γreg γd γsw γobs γhist c T g' h =>
      textLedger_phi cov sb.sbLogstart Hinv γgen γstart γreg γd γsw γobs γhist c T g' h)
    Hgen0 Hpow Himg n κs t2 g2 hsteps

include hlc GF in
/-- **AT THE LITERAL MKFS IMAGE** (`xv6FsAdequacyImg`'s twin). -/
theorem xv6TextAdequacyImg (US : USER) (g : GState)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → textPristine g2) :=
  xv6TextAdequacy (hlc := hlc) (GF := GF) US g fsimgSb fsimgNib fsimgCov Hgen0 Hpow
    (fsimgHimg g Hdisk) n κs t2 g2 hsteps

end unit

/-- **AT THE CONCRETE FUNCTOR LIST** (`xv6FsAdequacy_xv6GF`'s twin): no
ghost-state class assumed, the literal mkfs image.  Premises: `USER`, the
machine off and never booted, `fs.img` on its disk. -/
theorem xv6TextAdequacy_xv6GF {hlc : HasLC} (US : USER) (g : GState)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → textPristine g2) :=
  letI : MachGpreS hlc xv6GF := xv6GF_machGpreS hlc 0
  xv6TextAdequacyImg (hlc := hlc) (GF := xv6GF) US g Hgen0 Hpow Hdisk n κs t2 g2 hsteps

end Xv6
