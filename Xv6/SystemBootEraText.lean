/-
**ONE ERA OF THE SYSTEM, THE WINDOW PERSISTED BY THE POWER THREAD**
(weak-allocproc plan §C Stage 0, item W3, option (A); PROGRESS-W3.md).

`xv6BootEraT`: `SystemBootEra.xv6BootEra` at `MachCSL.powerBootResT bcRoLo
bcRoHi` (`MachCSL/PowerText.lean`), through `BootSharedText`'s
`powerBootResT_unpack` and `bootSharedAllocT`.  A near-copy; the statement
differs from `xv6BootEra`'s only in that row.  Every existing statement is
unchanged [OWN.9].
-/
import Xv6.SystemBootEra
import Xv6.BootSharedText

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL

section era
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF] [Xv6G GF] [WchGpre GF]
  [CtokG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF]
  [IcboxG GF] [SleepLockG GF] [BcacheG GF] [OffboxG GF] [OffboxBoxG GF] [FileG GF]

set_option maxHeartbeats 800000 in
/-- **ONE ERA, THE WINDOW PERSISTED BY THE POWER THREAD** (`xv6BootEra`'s
twin): what `MachCSL.riscvPowerAdequacyT`'s `Hboot` owes, out of the trace
invariant and `powerBootResT bcRoLo bcRoHi`.  The unpack is
`powerBootResT_unpack`, the shared allocation `bootSharedAllocT`; every
other step verbatim. -/
theorem xv6BootEraT {CT : Type} (N : Type) (appFs : CT → N → Aview → IProp GF)
    (appBoot : CT → Nat → N → IProp GF)
    -- THE ERA'S TURN (Rocq `Tn`/`Tn_init`, sync SY3-A1): what the power arm
    -- carried here (the slot's swap's yield through the return path), and what
    -- the founding `Hfound` leaves of it for `<init>`
    (Tn TnInit : CT → Nat → IProp GF) (sb : FsSb)
    (cov : ExtTreeSet Nat compare) (Ai : AppIface GF) (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γd γsw γobs γhist : GName)
    (c : CT) (T : List Obs) (Ptp : IProp GF)
    -- THE TWO SYNC SLOTS of the record (Rocq sync K3-2)
    (Tkp : Nat → IProp GF) (Hkp : Nat → IProp GF → IProp GF)
    -- THE RECORD'S ENTER JUSTIFICATION AND FILING CLAIMS (NI M2-W4): any
    -- justification that accepts the NI filing's evidence, any claims whose
    -- fork mint is an origin ticket (`True`/`emp` for the system theorem,
    -- `niFit` and the ledger's claims for the NI one)
    (Uf : Option (Nat × Obs) → Obs → Prop) (hUf : ∀ ox e, niFit ox e → Uf ox e)
    (Ucr : Nat → IProp GF) (Ucx : Nat → Obs → IProp GF) (Uco : IProp GF)
    (hUfork : ∀ (i : Nat) (x : Obs), niForkExit x = true → Ucx i x ⊢@{IProp GF} Uco)
    -- THE RECORD'S EVIDENCE AND REGISTRATION (NI M2-X1): any evidence a
    -- citation and an origin's fit build, any registration the ticket shoots
    -- (`emp` for the system theorem; the NI ledger's for the NI one)
    (Ue : Option (Nat × Obs) → Obs → IProp GF) (HUe : ∀ ox e, Persistent (Ue ox e))
    (Uet : Nat → IProp GF) (Uea : Nat → List GName → IProp GF) (HUea : ∀ k ns, Persistent (Uea k ns))
    (hUreg : ∀ (k : Nat) (ns : List GName), Uet k ⊢@{IProp GF} |==> Uea k ns)
    (hUevid : ∀ (i : Nat) (x e : Obs) (cc : Option (Nat × UIota)) (u : NiUh), niFitEv (some (i, x)) e cc u →
      niCiteResRaw Uea cc ∗ niUhRes u ⊢@{IProp GF} Ue (some (i, x)) e)
    (hUevidNone : ∀ (e : Obs) (u : NiUh), niFitEv none e none u → niUhRes u ⊢@{IProp GF} Ue none e)
    -- THE ERA'S RECORD PREDICATE (Rocq `Ok`/`Hbok`, SY3-A1 re-cut), read off
    -- the boot resource, at the era's number
    (Ok : Nat → N → Prop) (Hbok : ∀ (k : Nat) (r : N), appBoot c k r ⊢@{IProp GF} ⌜Ok k r⌝)
    -- THE DURABLE-COPY PREDICATE (Rocq `Okc`, SY3-A3b)
    (appOkc : CT → N → Prop)
    -- THE MERGE (Rocq `Happ_merge`, SY3-K2; its wand lent the started auth at
    -- the era's `gen + 1`, SY3-A1), at the record literal
    (Happ_merge : letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart Ai Hinv
      γgen γstart γreg γd γsw γobs γhist c T Ptp Tkp Hkp Uf Ucr Ucx Uco
      Ue HUe Uet Uea HUea)
      ∀ k : Nat, ⊢@{IProp GF} appMergeRaw (hlc := hlc) (appFs c) (Ok (k + 1)) (appOkc c) (Tkp k) k)
    -- THE FOUNDING (Rocq `Hfound`, SY3-A1): the era's sync token out of the
    -- turn, the rest for `<init>`
    (Hfound : ∀ k : Nat, ⊢@{IProp GF} Tn c (k + 1) -∗ |==> (Tkp k ∗ TnInit c (k + 1)))
    -- THE SYNC RUNNER (Rocq `Happ_sync_run`, K3-3), at the record's slots
    (Happ_sync_run : letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart Ai Hinv
      γgen γstart γreg γd γsw γobs γhist c T Ptp Tkp Hkp Uf Ucr Ucx Uco
      Ue HUe Uet Uea HUea)
      ∀ k : Nat, ⊢@{IProp GF} appSyncRunRaw (hlc := hlc) (appFs c) (Ok (k + 1)) (appOkc c) (Tkp k)
        (Hkp k))
    (Hinit_boot : letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart Ai Hinv γgen
      γstart γreg γd γsw γobs γhist c T Ptp Tkp Hkp Uf Ucr Ucx Uco
      Ue HUe Uet Uea HUea)
      EraInitBoot (hlc := hlc) N appFs appBoot TnInit c)
    (Hecho : letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart Ai Hinv γgen γstart
      γreg γd γsw γobs γhist c T Ptp Tkp Hkp Uf Ucr Ucx Uco
      Ue HUe Uet Uea HUea)
      EraEcho (hlc := hlc) (GF := GF))
    (Hperm : letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart Ai Hinv γgen γstart
      γreg γd γsw γobs γhist c T Ptp Tkp Hkp Uf Ucr Ucx Uco
      Ue HUe Uet Uea HUea)
      EraPerm (hlc := hlc) (GF := GF))
    (E : EraGS) (gen : Nat) (σ : MState) (hbf : bootFacts σ)
    (hdv : ∃ ds0 : DevStates, σ.devs = ds0.reset)
    (hpure : fsBootPure cov sb.sbLogstart (diskOf σ.devs))
    (hcovin : fsCovIn cov XV6_DISK_BYTES)
    (hlogsub : ∀ b, logRegion sb.sbLogstart b = true → b ∈ cov) (hls2 : sb.sbLogstart = 2) :
    letI : MachFixedGS hlc GF := (xv6FixedGSU N appFs appOkc cov sb.sbLogstart Ai Hinv γgen γstart γreg γd
      γsw γobs γhist c T Ptp Tkp Hkp Uf Ucr Ucx Uco
      Ue HUe Uet Uea HUea)
    obsInv ∗ powerBootResT bcRoLo bcRoHi (fun dk => mirrorOf (fsBlocks dk))
        (xv6Lend N appFs appBoot cov sb.sbLogstart c) (Tn c) E gen σ ⊢@{IProp GF} |={⊤}=>
      ([∗list] cpu ∈ cpus, hartWP gen cpu (pure ())) ∗
      ([∗list] d ∈ DevId.all, devWP gen d rootTask (pure ())) := by
  letI F : MachFixedGS hlc GF := xv6FixedGSU N appFs appOkc cov sb.sbLogstart Ai Hinv γgen γstart γreg γd
    γsw γobs γhist c T Ptp Tkp Hkp Uf Ucr Ucx Uco Ue HUe Uet Uea HUea
  obtain ⟨-, D, hrec, hhwf, -⟩ := hpure
  obtain ⟨ds0, hds⟩ := hdv
  iintro ⟨#Hoinv, Hres⟩
  icases powerBootResT_unpack (fun dk => mirrorOf (fsBlocks dk))
    (xv6Lend N appFs appBoot cov sb.sbLogstart c) (Tn c) E gen (fun _ _ => iprop(True))
    (fun _ => BI.true_intro) σ $$ Hres
    with ⟨Hrows, Hlend, Hturn, Huo, Hetok⟩
  imod xv6Era_lend N appFs appBoot c cov sb.sbLogstart gen (diskOf σ.devs) D hrec hhwf hcovin hlogsub
    hls2 $$ Hlend with ⟨%r, %gt, %gsn, %gln, %S, %⟨hlseq, hwf⟩, Hok, Hsnap, Hbres⟩
  -- the seam at the era's superblock, off the slot's value (the literal)
  have hseam := xv6Era_seam (hlc := hlc) (GF := GF) (appFs c) (appOkc c) cov S.fssSb.sbLogstart
    (by rw [hlseq]; rfl)
  -- THE SHARED ALLOCATION, at the provisional instance, under the era's record
  have hA := (letI : MachGS hlc GF := eraM0 E gen; letI : Appcfg GF := ⟨N, appFs c, r⟩;
    bootSharedAllocT (hlc := hlc) (GF := GF) σ hbf ds0 hds XV6_DISK_BYTES S S.fssSb (fsNib S) cov
      gsn gln gt (fsRecView (fsBlocks (diskOf σ.devs)) D) hwf)
  -- THE FOUNDING (Rocq `Hfound`, SY3-A1): the era's sync token out of the
  -- turn the power arm carried, handed to the mint, which puts it into the
  -- log's free bundle; the rest goes to `<init>`
  imod (Hfound gen) $$ Hturn with ⟨Hstok, Hturn⟩
  -- THE ERA'S RECORD PREDICATE at the running instance, off its boot
  -- resource (Rocq `Hbok`, SY3-A1 re-cut)
  ihave ⟨%hokr, Hbres⟩ := fsDurKeep (Hbok (gen + 1) r) $$ Hbres
  imod hA $$ [Hrows Hok Hsnap Hstok] with ⟨%ξ0, %Γ, %W, %HFd, %HBs, %HIr, %γc, %γl0, %γl1, %γt,
    %γ0, %γ1, %cn, %γd, %I, %Fc, %ξd, %hW, Hout⟩
  · iframe Hrows Hok Hsnap
    -- THE DURABLE SIDE (Rocq `app_dur_laws`, SY3-A3b): the seam at the guest
    -- and the merge package, at the durable-copy predicate `appOkc c`; the
    -- package at the era's record predicate `Ok (gen + 1)`, which the running
    -- record `r` satisfies (its boot resource says so), at the era's token,
    -- hook family and generation `gen` (the ambient `genId` at `eraM0 E gen`)
    isplitl []
    · unfold appDurLaws
      iexists (appOkc c)
      isplitl []
      · unfold appGuest
        iapply hseam
      unfold appMerge
      iexists (Ok (gen + 1))
      isplitr
      · ipureintro; exact hokr
      unfold eraSyncTok eraSyncHook genId
      isplitl []
      · iapply (Happ_merge gen)
      · iapply (Happ_sync_run gen)
    unfold eraSyncTok genId
    iexact Hstok
  -- THE FINAL INSTANCE: the claim is the proc table's
  letI : Appcfg GF := ⟨N, appFs c, r⟩
  let M1 : MachGS hlc GF := MachGS.ofEra E gen (procClaim Γ) (fun cpu => procClaim_idle Γ cpu)
  have hClaim : @ClaimIs hlc GF M1 _ Γ := @ClaimIs.mk hlc GF M1 _ Γ (fun _ _ => rfl)
  -- ...and the record accepts the NI filing's evidence (NI M2-W2c) and its
  -- fork mint is an origin ticket (NI M2-W2d): `hUf`/`hUfork` (the system
  -- record's `True`/`emp` by `trivial`/`.rfl`, the NI record's by `id` and
  -- `niExitMint_fork`; NI M2-W4)
  -- (NI M2-X2) at the minted instance's cameras, which are the ambient ones
  -- (`bootSharedAlloc`'s `hW`): the lower bounds a citation shows are where
  -- `hUevid` reads them
  have hNi : @NiFitIs hlc GF M1 _ W.toWchGpre := by
    rw [hW]; exact @NiFitIs.mk hlc GF M1 _ _ hUf hUfork hUreg hUevid hUevidNone
  ihave Hout := bootSharedOut_ofEra E gen (fun _ _ => iprop(True)) (procClaim Γ)
    (fun _ => BI.true_intro) (fun cpu => procClaim_idle Γ cpu) σ ξ0 Γ γ0 γ1 γc γl0 γl1 γt cn γd ξd (diskOf σ.devs) S.fssSb (fsNib S)
    cov (fsRecView (fsBlocks (diskOf σ.devs)) D) (snapSpent S (fsNib S)) $$ Hout
  -- the first process's exec bundle, at the era's record, over the lent boot
  -- resource and the era's turn
  have hI := Hinit_boot E gen (procClaim Γ) (fun cpu => procClaim_idle Γ cpu) r
  have hR := (letI : MachGS hlc GF := M1; letI : Appcfg GF := ⟨N, appFs c, r⟩;
    haveI := hClaim; haveI := hNi;
    xv6Era_run (hlc := hlc) (GF := GF) σ ξ0 Γ γ0 γ1 γc γl0 γl1 γt cn γd ξd (diskOf σ.devs) S.fssSb
      (fsNib S) cov XV6_DISK_BYTES S (fsRecView (fsBlocks (diskOf σ.devs)) D) (snapSpent S (fsNib S))
      hwf (fun i γ hu => Hperm E gen (procClaim Γ) (fun cpu => procClaim_idle Γ cpu) i γ hu)
      iprop(appBoot c (gen + 1) r ∗ TnInit c (gen + 1)) (by
        iintro Hai ⟨Hb, Ht⟩
        iapply hI $$ Hai Hb Ht) (gen + 1))
  imod hR $$ Hoinv [] [Hbres Hturn] Huo Hetok Hout with ⟨Hharts, Hdevs, #Hcert⟩
  · iapply (Hecho E gen (procClaim Γ) (fun cpu => procClaim_idle Γ cpu))
  · isplitl [Hbres]
    · iexact Hbres
    · iexact Hturn
  have hc : @genCert hlc GF M1 ⊢ genCertAt gen E := .rfl
  have hd : ([∗list] d ∈ DevId.all, devWP (@genId hlc GF M1) d rootTask (pure ())) ⊢@{IProp GF}
      [∗list] d ∈ DevId.all, devWP gen d rootTask (pure ()) := .rfl
  ihave #Hc := hc $$ Hcert
  imodintro
  isplitl [Hharts]
  · iapply BigSepL.bigSepL_impl $$ Hharts
    imodintro
    iintro %k %cpu %_ Hw
    iapply wpLoop_ofEra E gen (procClaim Γ) (fun cpu => procClaim_idle Γ cpu) cpu
    iframe Hc Hw
  · iapply hd $$ Hdevs


end era

end Xv6
