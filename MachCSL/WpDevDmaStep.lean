/-
MachCSL: bus-mastering device threads with a LINEAR knowledge context.

`MachCSL.WpDevDma`'s `DevM.Lease` threads a PERSISTENT context `C` down a
device program: at a `.get` the derivation may extend `C` by a persistent
consequence of the invariant, and every later obligation may use it.  That
is enough whenever what one step learned about the state is MONOTONE --
"this chain was armed at that generation", "the configuration is frozen".
It is not enough for the disk.

THE GAP.  `Virtio.serve h` reads the descriptors of head `h` at one state
and INSTALLS the request it parsed several steps later.  The install is
sound only because the chain armed at `h` cannot have moved in between:
re-arming a head needs the driver to reclaim it, which needs the request
to have completed, which only the serving task itself can do.  "Nothing
has happened at `h` since I looked" is not a monotone fact, so NO
persistent context can carry it -- and `DevM.Lease`'s obligations are
quantified over EVERY state, so the derivation must also cope with the
state in which the head has meanwhile completed, been reclaimed and been
re-armed with a different chain.  There, the install genuinely breaks the
invariant.  (Adding `C` to the `.step` obligation -- the `stepC` arm --
does not help: the offending state satisfies `C ∗ R s` for every
persistent `C` the earlier `.get` could have produced.)

WHAT THIS FILE ADDS.  `DevM.LeaseL`, the same derivation with the context
threaded LINEARLY: `wpDev_dmaL` hands the task `C` rather than `□ C`, so a
task may hold an exclusive ghost resource -- the half of a ghost
var/ghost-map element whose other half the invariant keeps -- and then
"nothing has happened since" IS available, as agreement against that half
at every later state.  Three further generalisations come for free and are
what the disk needs:

* the `.step` arm's obligation is `C ∗ R s ⊢ |==> (R s' ∗ C')` -- the
  update may use the context (the `stepC` the disk wanted) and may produce
  a new context, so a step that changes the state may MINT a token;
* the `.get` arm's obligation is `C ∗ R s ⊢ |==> (R s ∗ ∃ x, C' s x)` --
  the derivation may take a resource out of the invariant and put a marker
  back in its place (the state does not move, but `R s` is a proposition,
  not a heap: taking one disjunct and leaving another re-establishes it),
  and the continuation is checked for each `x` separately, so the CHAIN a
  task read may be a Lean-level parameter of the rest of the derivation;
* the `.fork` arm splits the context, giving the new task `Lt t` -- so the
  resource a step minted can be handed to the task it forked.

Nothing here changes `MachCSL/WpDevDma.lean`: `DevM.Lease` and
`wpDev_dma` are untouched, and `leaseL_of_lease` embeds the old
derivations into the new loop lemma, so a client may move over one
program at a time.
-/
import MachCSL.WpDevDma

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-! ## Framing a context through the two DMA obligations -/

theorem dmaReadPin_frame (pa : PAddr) (n : Nat) (Q : BitVec (8 * n) → Prop) (P C : IProp GF) :
    dmaReadPin pa n Q P ∗ C ⊢ dmaReadPin pa n Q (iprop(P ∗ C)) := by
  unfold dmaReadPin
  iintro ⟨Hpin, HC⟩
  icases Hpin with ⟨⟨%hall, HP⟩ | ⟨%dqs, %Hs, %w, Hb, %hh, %hQ, Hback⟩⟩
  · ileft
    iframe HP HC
    ipureintro
    exact hall
  · iright
    iexists dqs, Hs, w
    iframe Hb
    isplit
    · ipureintro; exact hh
    isplit
    · ipureintro; exact hQ
    iintro Hb2
    iframe HC
    iapply Hback $$ Hb2

theorem dmaWriteLease_frame (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (P C : IProp GF) :
    dmaWriteLease pa n w P ∗ C ⊢ dmaWriteLease pa n w (iprop(P ∗ C)) := by
  unfold dmaWriteLease
  iintro ⟨⟨%Hs, Hb, Hback⟩, HC⟩
  iexists Hs
  iframe Hb
  iintro %t Hb2 Hau Htop
  iframe HC
  iapply Hback $$ %t Hb2 Hau Htop

/-! ## The derivation -/

/-- A device program whose DMA writes are covered by a lease out of `R`,
whose DMA reads are pinned, and whose own updates carry the invariant
along, with the knowledge context `C` threaded LINEARLY.  `Lt t` is what a
forked task of name `t` starts from; the root loop starts from `True`.
`.setPin` is excluded exactly as in `DevM.Lease`. -/
inductive DevM.LeaseL {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] {S T : Type}
    (R : S → IProp GF) (Lt : T → IProp GF) : IProp GF → DevM S T Unit → Prop
  | pure (C : IProp GF) (a : Unit) : LeaseL R Lt C (.pure a)
  /-- `choose`, `sample`, `join`: no state moves, no bus transaction. -/
  | op (C : IProp GF) (o : DevOp S T) (k : o.ret → DevM S T Unit)
      (hw : ∀ g pa n w, o ≠ .dmaWrite g pa n w)
      (hr : ∀ pa n, o ≠ .dmaRead pa n)
      (hg : o ≠ .get)
      (hst : ∀ g, o ≠ .step g)
      (hfk : ∀ t, o ≠ .fork t)
      (hp : ∀ c mm b, o ≠ .setPin c mm b)
      (hk : ∀ r, LeaseL R Lt C (k r)) : LeaseL R Lt C (.op o k)
  /-- The guarded update: the invariant moves with the state, USING the
  context, and the step may mint a new one. -/
  | step (C C' : IProp GF) (g : S → Option (S × List DevObs)) (k : Unit → DevM S T Unit)
      (hs : ∀ s s' os, g s = some (s', os) → iprop(C ∗ R s) ⊢ |==> (R s' ∗ C'))
      (hk : LeaseL R Lt C' (k ())) : LeaseL R Lt C (.op (.step g) k)
  /-- Reading the state: the derivation learns `C' s x` for an `x` of its
  own choosing, and the continuation is checked for each `x`. -/
  | get (C : IProp GF) {X : Type} (C' : S → X → IProp GF) (k : S → DevM S T Unit)
      (hknow : ∀ s, iprop(C ∗ R s) ⊢ |==> (R s ∗ ∃ x, C' s x))
      (hk : ∀ s x, LeaseL R Lt (C' s x) (k s)) : LeaseL R Lt C (.op .get k)
  | dmaRead (C : IProp GF) (pa : PAddr) (n : Nat) (Q : S → BitVec (8 * n) → Prop)
      (k : BitVec (8 * n) → DevM S T Unit)
      (hpin : ∀ s, iprop(C ∗ R s) ⊢ dmaReadPin pa n (Q s) (iprop(R s ∗ C)))
      (hk : ∀ v, (∃ s, Q s v) → LeaseL R Lt C (k v)) :
      LeaseL R Lt C (.op (.dmaRead pa n) k)
  | dmaWrite (C : IProp GF) (g : S → Bool) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
      (k : Unit → DevM S T Unit)
      (hlease : ∀ s, g s = true → (iprop(C ∗ R s) ⊢ dmaWriteLease pa n w (iprop(R s ∗ C))))
      (hk : LeaseL R Lt C (k ())) : LeaseL R Lt C (.op (.dmaWrite g pa n w) k)
  /-- Forking: the context splits, and the new task gets `Lt t`. -/
  | fork (C C' : IProp GF) (t : T) (k : TaskId → DevM S T Unit)
      (hsplit : C ⊢ iprop(C' ∗ Lt t))
      (hk : ∀ tid, LeaseL R Lt C' (k tid)) : LeaseL R Lt C (.op (.fork t) k)

/-- A device whose root loop is derivable from no knowledge and whose every
task is derivable from the resource its forker hands it. -/
def DevSig.LeaseL (d : DevId) (R : DevSt d → IProp GF) (Lt : DevTask d → IProp GF) : Prop :=
  DevM.LeaseL R Lt iprop(True) (devSig d).body ∧
  ∀ t, DevM.LeaseL R Lt (Lt t) ((devSig d).task t)

/-! ## A plain primitive moves nothing -/

/-- `choose`, `sample` and `join` are the only primitives left once the
six the derivation gives an arm of its own are excluded, and none of them
moves the machine. -/
theorem devOpStep_plain (gen : Nat) (d : DevId) (o : DevOp (DevSt d) (DevTask d)) (σ : MState)
    (v : o.ret) (σ' : MState) (obs : List Obs) (efs : List Expr)
    (hw : ∀ g pa n w, o ≠ .dmaWrite g pa n w) (hr : ∀ pa n, o ≠ .dmaRead pa n)
    (hg : o ≠ .get) (hst : ∀ g, o ≠ .step g) (hfk : ∀ t, o ≠ .fork t)
    (hp : ∀ c mm b, o ≠ .setPin c mm b) (hop : devOpStep gen d o σ v σ' obs efs) :
    σ' = σ ∧ efs = [] := by
  cases o with
  | step g => exact absurd rfl (hst g)
  | get => obtain ⟨_, rfl, _, rfl⟩ := hop; exact ⟨rfl, rfl⟩
  | choose => obtain ⟨rfl, _, rfl⟩ := hop; exact ⟨rfl, rfl⟩
  | dmaRead pa n => exact absurd rfl (hr pa n)
  | dmaWrite g pa n w => exact absurd rfl (hw g pa n w)
  | sample src => obtain ⟨_, rfl, _, rfl⟩ := hop; exact ⟨rfl, rfl⟩
  | setPin c mm b => exact absurd rfl (hp c mm b)
  | fork t => exact absurd rfl (hfk t)
  | join tid => obtain ⟨_, rfl, _, rfl⟩ := hop; exact ⟨rfl, rfl⟩

/-! ## The loop lemma -/

set_option maxHeartbeats 4000000 in
/-- **Every task of a bus-mastering device is safe**, with the knowledge
context threaded linearly.  The shape of the proof is `wpDev_dma`'s; the
only difference is that the context is handed over rather than duplicated,
which is what lets a task hold an exclusive resource across its steps. -/
theorem wpDev_dmaL (N : Namespace) (d : DevId) (R : DevSt d → IProp GF) [∀ s, Timeless (R s)]
    (Lt : DevTask d → IProp GF) (hloc : DevSig.LeaseL d R Lt) :
    devInvR N d R ∗ genCert ⊢@{IProp GF}
      ∀ (tid : TaskId) (m : DevProg d) (C : IProp GF), ⌜DevM.LeaseL R Lt C m⌝ →
        C -∗ devWP (genId (hlc := hlc) (GF := GF)) d tid m := by
  unfold devInvR
  iintro ⟨#Hinv, #Hcert⟩
  iloeb as IH
  iintro %tid %m %C %hm HC
  iapply wpDev_elim d tid m
  iframe Hcert
  iapply wpDev_lift d tid m
  iintro %σ Hσ
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%s, >Hfrag, >HR⟩
  icases machInterp_acc_dev σ d $$ Hσ with ⟨Hauth, Hσclose⟩
  ihave %hs := devAgreeAt _ d (σ.devs.st d) s $$ [Hauth Hfrag]
  case' _ => iframe
  subst hs
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    exact devStep_total _ d tid m σ
  inext
  iintro %obs %m' %σ' %efs %hstep Hcred
  imod Hmask
  have hmk : ∀ (m'' : DevProg d) (C'' : IProp GF), DevM.LeaseL R Lt C'' m'' →
      ⊢@{IProp GF} (∀ (tid : TaskId) (m : DevProg d) (C : IProp GF), ⌜DevM.LeaseL R Lt C m⌝ →
        C -∗ devWP (genId (hlc := hlc) (GF := GF)) d tid m) -∗
      C'' -∗ wpDev d tid m'' := by
    intro m'' C'' hm''
    iintro IH' HC''
    unfold wpDev
    iintro _
    iapply IH' $$ %tid %m'' %C'' %hm'' HC''
  cases m with
  | pure a =>
    obtain ⟨rfl, rfl, h⟩ := hstep
    ihave Hcl := Hclose $$ [Hfrag HR]
    case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
    imod Hcl
    imodintro
    ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
    case' _ => iframe
    rcases h with ⟨_, rfl, rfl⟩ | ⟨_, rfl, hσ'⟩
    · iframe Hσ
      isplitl []
      · iapply hmk _ iprop(True) hloc.1 $$ IH
        itrivial
      · exact BigSepL.bigSepL_nil_intro
    · rw [hσ']
      isplitl [Hσ]
      · split
        · iexact Hσ
        · rw [machInterp_setRt]; iexact Hσ
      isplitl []
      · iapply hmk _ iprop(True) (DevM.LeaseL.pure _ ()) $$ IH
        itrivial
      · exact BigSepL.bigSepL_nil_intro
  | op o k =>
    have hm' := hm
    cases hm with
    | op _ _ _ hw hr hg hst hfk hp hk =>
      rcases hstep with ⟨v, rfl, hop⟩ | ⟨hb, rfl, hσ, rfl, rfl⟩
      · obtain ⟨hσ, rfl⟩ := devOpStep_plain _ d o σ v σ' obs efs hw hr hg hst hfk hp hop
        rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ (hk v) $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
      · rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ hm' $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
    | step _ C' g _ hs hk =>
      rcases hstep with ⟨v, rfl, hop⟩ | ⟨hb, rfl, hσ, rfl, rfl⟩
      · obtain ⟨s', os, hgg, rfl, _, rfl⟩ := hop
        imod (devUpdateAt _ d (σ.devs.st d) (σ.devs.st d) s') $$ [Hauth Hfrag] with ⟨Hauth, Hfrag⟩
        · iframe
        imod (hs _ _ _ hgg) $$ [HC HR] with ⟨HR, HC⟩
        · iframe HC HR
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists s'; iframe Hfrag HR
        imod Hcl
        imodintro
        isplitl [Hauth Hσclose]
        · iapply Hσclose $$ %s' Hauth
        isplitl [HC]
        · iapply hmk _ _ hk $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
      · rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ hm' $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
    | get _ C' _ hknow hk =>
      rcases hstep with ⟨v, rfl, hop⟩ | ⟨hb, rfl, hσ, rfl, rfl⟩
      · obtain ⟨rfl, hσg, rfl, rfl⟩ := hop
        rw [hσg]
        imod (hknow (σ.devs.st d)) $$ [HC HR] with ⟨HR, Hx⟩
        · iframe HC HR
        icases Hx with ⟨%x, HC⟩
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ (hk (σ.devs.st d) x) $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
      · rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ hm' $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
    | dmaRead _ pa n Q _ hpin hk =>
      rcases hstep with ⟨v, rfl, hop⟩ | ⟨hb, rfl, hσ, rfl, rfl⟩
      · obtain ⟨hview, hσr, rfl, rfl⟩ := hop
        rw [hσr]
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        ihave Hpin : dmaReadPin pa n (Q (σ.devs.st d)) iprop(R (σ.devs.st d) ∗ C) $$ [HC HR]
        · iapply hpin (σ.devs.st d) $$ [HC HR]
          iframe HC HR
        icases dmaReadPin_view σ pa n (Q (σ.devs.st d)) iprop(R (σ.devs.st d) ∗ C) $$ [$Hσ $Hpin]
          with ⟨%hq, Hσ, HR, HC⟩
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ (hk v ⟨σ.devs.st d, hq v hview⟩) $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
      · rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ hm' $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
    | dmaWrite _ g pa n w _ hlease hk =>
      rcases hstep with ⟨v, rfl, hop⟩ | ⟨hb, rfl, hσ, rfl, rfl⟩
      · obtain ⟨rfl, rfl, hcase⟩ := hop
        cases v
        rcases hcase with ⟨hgt, hram, hnr, rfl⟩ | ⟨_, hσn⟩
        · ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
          case' _ => iframe
          ihave Hl : dmaWriteLease pa n w iprop(R (σ.devs.st d) ∗ C) $$ [HC HR]
          · iapply hlease (σ.devs.st d) hgt $$ [HC HR]
            iframe HC HR
          icases dmaWriteLease_cases pa n w iprop(R (σ.devs.st d) ∗ C) $$ Hl with ⟨%Hs, Hb, Hback⟩
          imod machInterp_storeDma σ pa n Hs w hnr $$ [$Hσ $Hb] with ⟨Hσ, Hb, #Hau, #Htop⟩
          ihave Hrc := Hback $$ %(σ.top + 1) Hb Hau Htop
          icases Hrc with ⟨HR, HC⟩
          ihave Hcl := Hclose $$ [Hfrag HR]
          case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
          imod Hcl
          imodintro
          iframe Hσ
          isplitl [HC]
          · iapply hmk _ _ hk $$ IH HC
          · exact BigSepL.bigSepL_nil_intro
        · rw [hσn]
          ihave Hcl := Hclose $$ [Hfrag HR]
          case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
          imod Hcl
          imodintro
          ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
          case' _ => iframe
          iframe Hσ
          isplitl [HC]
          · iapply hmk _ _ hk $$ IH HC
          · exact BigSepL.bigSepL_nil_intro
      · rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ hm' $$ IH HC
        · exact BigSepL.bigSepL_nil_intro
    | fork _ C' t _ hsplit hk =>
      rcases hstep with ⟨v, rfl, hop⟩ | ⟨hb, rfl, hσ, rfl, rfl⟩
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hop
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        icases hsplit $$ HC with ⟨HC, HLt⟩
        isplitl [Hσ]
        · rw [machInterp_setRt]; iexact Hσ
        isplitl [HC]
        · iapply hmk _ _ (hk _) $$ IH HC
        · iapply BigSepL.bigSepL_singleton.2
          unfold devWP
          iapply IH $$ %((σ.devrt d).next) %((devSig d).task t) %(Lt t) %(hloc.2 t) HLt
      · rw [hσ]
        ihave Hcl := Hclose $$ [Hfrag HR]
        case' _ => inext; iexists (σ.devs.st d); iframe Hfrag HR
        imod Hcl
        imodintro
        ihave Hσ := machInterp_acc_dev_self σ d $$ [Hσclose Hauth]
        case' _ => iframe
        iframe Hσ
        isplitl [HC]
        · iapply hmk _ _ hm' $$ IH HC
        · exact BigSepL.bigSepL_nil_intro

/-- The root thread of a bus-mastering device, as the power thread forks it. -/
theorem wpDev_dmaL_root (N : Namespace) (d : DevId) (R : DevSt d → IProp GF)
    [∀ s, Timeless (R s)] (Lt : DevTask d → IProp GF) (hloc : DevSig.LeaseL d R Lt) :
    devInvR N d R ∗ genCert ⊢@{IProp GF}
      devWP (genId (hlc := hlc) (GF := GF)) d rootTask (DevM.pure ()) := by
  iintro H
  iapply wpDev_dmaL N d R Lt hloc $$ H %rootTask %(DevM.pure ()) %iprop(True)
    %(DevM.LeaseL.pure _ ())
  itrivial

/-! ## `DevM.Lease` embeds

An old derivation with the persistent context `C` is a new one with any
context equivalent to `□ C`, provided the client's `hR` is available for
the `.step` arm and every task starts from something derivable. -/

theorem leaseL_of_lease {S T : Type} (rel : S → S → Prop) (R : S → IProp GF)
    (hR : ∀ s s', rel s s' → R s ⊢@{IProp GF} |==> R s')
    (Lt : T → IProp GF) (hLt : ∀ t, ⊢@{IProp GF} Lt t)
    (C : IProp GF) (m : DevM S T Unit) (hm : DevM.Lease rel R C m) :
    ∀ D : IProp GF, (D ⊢ iprop(□ C)) → (iprop(□ C) ⊢ D) → DevM.LeaseL R Lt D m := by
  induction hm with
  | pure C a => exact fun D _ _ => .pure _ ()
  | @op C o k hw hr hg hp hs hk ih =>
    intro D hD1 hD2
    match o with
    | .step g =>
      refine DevM.LeaseL.step _ _ g _ (fun s s' os hgs => ?_) (ih () D hD1 hD2)
      have hrel := hs g rfl s s' os hgs
      iintro ⟨HD, HRs⟩
      ihave #HC := hD1 $$ HD
      imod (hR s s' hrel) $$ HRs with HRs
      imodintro
      iframe HRs
      iapply hD2
      iexact HC
    | .get => exact absurd rfl hg
    | .choose =>
      exact DevM.LeaseL.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
        (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun r => ih r D hD1 hD2)
    | .sample src =>
      exact DevM.LeaseL.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
        (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun r => ih r D hD1 hD2)
    | .join tid =>
      exact DevM.LeaseL.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
        (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun r => ih r D hD1 hD2)
    | .dmaRead pa n => exact absurd rfl (hr pa n)
    | .dmaWrite g pa n w => exact absurd rfl (hw g pa n w)
    | .fork t =>
      refine DevM.LeaseL.fork _ D t _ ?_ (fun r => ih r D hD1 hD2)
      iintro HD
      ihave #HC := hD1 $$ HD
      isplitr []
      · iapply hD2
        iexact HC
      · iapply hLt t
    | .setPin c mm b => exact absurd rfl (hp c mm b)
  | @get C P hPers k hknow hk ih =>
    intro D hD1 hD2
    refine DevM.LeaseL.get _ (X := Unit) (fun s _ => iprop(□ (C ∗ P s))) _ (fun s => ?_)
      (fun s _ => ih s _ (by iintro H; iexact H) (by iintro H; iexact H))
    haveI := hPers s
    iintro ⟨HD, HRs⟩
    ihave #HC := hD1 $$ HD
    ihave Hkn : iprop(R s ∗ P s) $$ [HRs]
    · iapply hknow s $$ [HC HRs]
      isplitr [HRs]
      · iexact HC
      · iexact HRs
    icases Hkn with ⟨HRs, #HP⟩
    imodintro
    iframe HRs
    iexists ()
    imodintro
    isplit
    · iexact HC
    · iexact HP
  | @dmaRead C pa n Q k hpin hk ih =>
    intro D hD1 hD2
    refine DevM.LeaseL.dmaRead _ pa n Q _ (fun s => ?_) (fun v => ?_)
    · iintro ⟨HD, HRs⟩
      ihave #HC := hD1 $$ HD
      iapply dmaReadPin_frame pa n (Q s) (R s) D
      isplitl [HRs]
      · iapply hpin s $$ [HC HRs]
        isplitr [HRs]
        · iexact HC
        · iexact HRs
      · iapply hD2
        iexact HC
    · intro hqv
      refine ih v _ ?_ ?_
      · iintro HD
        ihave #HC := hD1 $$ HD
        imodintro
        isplit
        · iexact HC
        · ipureintro; exact hqv
      · iintro #HCq
        icases HCq with ⟨#HC, %_⟩
        iapply hD2
        imodintro
        iexact HC
  | @dmaWrite C g pa n w k hlease hk ih =>
    intro D hD1 hD2
    refine DevM.LeaseL.dmaWrite _ g pa n w _ (fun s hgs => ?_) (ih D hD1 hD2)
    iintro ⟨HD, HRs⟩
    ihave #HC := hD1 $$ HD
    iapply dmaWriteLease_frame pa n w (R s) D
    isplitl [HRs]
    · iapply hlease s hgs $$ [HC HRs]
      isplitr [HRs]
      · iexact HC
      · iexact HRs
    · iapply hD2
      iexact HC

end MachCSL
