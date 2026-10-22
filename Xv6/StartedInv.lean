/-
**The invariant on xv6's `started` flag** (Rocq `StartedInv.v`): the one
channel by which the boot hart's initialisation reaches the other harts.

    volatile static int started = 0;             // main.c, KA.«started»

    main() {
      if (cpuid() == 0) { ...all the init...; __sync_synchronize(); started = 1; }
      else              { while (started == 0) ; __sync_synchronize(); ...per-hart init...; }
      scheduler();
    }

THE SHAPE.  `started` is a plain global written once by hart 0 and read
racily by every other hart, so its word cannot be owned by any hart: it
lives in an invariant, as a WORD CELL (`MachCSL.WordHist`), and the
invariant is where the boot hart's output is PARKED -- a one-shot escrow:

* UNARMED: the never-written window (`wordCell … 0 0 []`), the other half of
  the primary's token at `0`, and the record context `ξd` stamped at some
  `T0`, empty;
* ARMED: the window holding exactly the primary's one store `⟨t, hart 0, 1⟩`,
  the store's position `t` frozen in a persistent ghost (`startedIdx`), `ξd`
  stamped at `T ≤ t` and carrying the primary's deposit `P ξd`.

A secondary that READS `1` saw the store: it is not hart 0, so the entry
was visible only at `t ≤ tvn`, and the read leaves `rviewLb cpu tvn`
(`started_readAUr`); its `__sync_synchronize()` turns that into
`viewLb cpu t` (`MachCSL.wp_s_fence_iorw_iorw_floor`), and a second opening
ABSORBS the deposit into its own context (`started_absorb`,
`MachCSL.ctxAbsorbLb`), leaving `ξd` stamped where it was so every hart can
do the same.  THE DEPOSIT MUST BE PERSISTENT (`∀ ξ, Persistent (P ξ)`): up
to `NCPU - 1` harts take it, and the invariant keeps it.

The primary opens the unarmed arm, deposits `P` into `ξd`
(`started_deposit`, `MachCSL.ctxDeposit`) and, after its store at `t`, arms
the invariant (`started_writeAUT`).

This is main's `__sync_synchronize(); started = 1;` edge and the other
harts' spin.  (The disk's `DiskAcc.DISK_INIT_WM`, once said to stand for
it, is retired differently: the used index's base is a KEY, cashed at the
handler's own fence -- `DiskInvDefs.diskPayFl`.)

## Deviations from Rocq

1. **The deposit is not position-indexed**: `P : CtxId → IProp`, not
   Rocq's `nat → CtxId → iProp` (A6.138).  Rocq indexes it by the flag
   store's log position for ONE row, `∃ B, kpt_bound B ∗ B ≤ pos`, and the
   Lean kernel page table has no log bound (no `kptBound` in the tree).  So
   the deposit can be made BEFORE the store, which is what lets its stamp be
   named to the store (item 3).
2. **The window is a `WordHist` cell** (`wordCell startedAddr 4 0 0 W`), not
   Rocq's physical-ledger window with a release payload (`phys_ledger_rpay`,
   `TsRel`): the Lean TSO model keeps per-byte histories (memory:
   lean-tso-memory-model).  Rocq's `started_img` (the era image holds 0) is
   the cell's tail (`tailOk 4 0 0`); Rocq's two machine-level obligations
   (`started_read_obl`, `started_store_obl`) are the accessor lemma
   `started_readAUr` and the resource steps around `writeAU`.
3. **THE STORE NEEDS AN ORDERING RECEIPT MachCSL DOES NOT YET GIVE.**  The
   armed arm needs `T ≤ t` (the deposit's stamp at or below the flag store's
   position), which Rocq read off the model's log length
   (`tso_interp_llb_valid`).  `MachCSL.writeAU`'s continuation gets
   `authoredBy t` and `topLb t` but no order against an earlier `topLb T`;
   `MachCSL.exclWriteAU` has exactly that field (`T ≤ t`) and
   `MachCSL/WpDevDma`'s disk store has `Kb < t`.  The plain-store rule that
   supplies it is `MachCSL.WpStoreOrd` (`writeAUT` / `wp_s_sw_auT`, the
   ordered store), and main's store runs it through `started_writeAUT` (two
   openings, below).
4. The ghost is a `ghost_var` over `Nat` (the existing `Xv6G.gvNatG`
   capacity: one instance per camera), `0` unarmed and `t + 1` armed,
   frozen at the store; Rocq's `dset_auth`/`dset_in` set camera is not
   ported.
5. Rocq's `started_claim`/`started_inv_claim` (the window's address claim)
   are dropped: a Lean S-mode access takes `kmapId a`, out of the
   persistent `kmapStatic`.
6. Rocq's `started_clear_sext`/`started_sext_nonzero` (the `sext.w; beqz`
   reading) and `agent_zero_cid`/`cid_zero_agent` are the spin loop's
   stage facts, not the invariant's; the reader's side is stated at
   `cpu ≠ startedPrimary`.
7. **(W8 (f2-ctx), Q-F2-BOOTGATE (a) as amended by [R35.2]) `started` is a
   RESERVED one-shot PUBLICATION word** (`Xv6.xv6StartedR`,
   `MachCSL.RsvKind.pub`): the invariant holds HALF of its four bytes at the
   image history (`startedWin`; the state interpretation holds the other
   half and keeps `MachCSL.oneShotOk`), main's store is the ordered store's
   RESERVED arm with the history-aware obligation (`started_rsvStoreOk`),
   and a secondary's read of the set value is the BOOT GATE: the read's
   issue request (`MachCSL.rdIn`) hands it `MachCSL.gatePassed cpu`
   (`startedSeen`), issued inside the load's atomic step.
-/
import MachCSL.CtxBox
import MachCSL.ReadAUr
import Xv6.UartTrace
import MachCSL.WpStoreOrd
import Xv6.KernelRsv

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std MachCSL

/-- The flag's namespace. -/
def startedN : Namespace := ndot nroot "started"

/-- The flag's address (identity-mapped). -/
def startedAddr : PAddr := KA.«started»

/-- The two values the flag ever holds. -/
def startedClear : BitVec (8 * 4) := 0
def startedSet : BitVec (8 * 4) := 1

/-- The hart that writes it: `cpuid() == 0`. -/
def startedPrimary : CPU := ⟨0, by decide⟩

/-- The flag's image history: a never-written `.bss` word (four zero bytes at
timestamp 0). -/
def startedImg : Nat → Hist := fun _ => [⟨0, 0, 0#8⟩]

theorem startedImg_tail : tailOk 4 0 startedClear startedImg :=
  fun j _ => ⟨_, _, rfl, by simp [startedClear, nthByte], rfl⟩

/-- `started`'s region is xv6's ONLY publication word (W8 (f2-ctx)). -/
theorem xv6Pub_only (f : PAddr) (w : CPU) (h : (⟨f, .pub w⟩ : RsvRegion) ∈ xv6RsvStatic) :
    f = startedAddr ∧ w = startedPrimary := by
  have hall : xv6RsvStatic.all (fun R => match R.kind with
      | .pub w' => decide (R.base = startedAddr) && decide (w' = startedPrimary)
      | _ => true) = true := by decide +kernel
  have := List.all_eq_true.1 hall _ h
  simpa using this

theorem xv6Started_mem : xv6StartedR ∈ xv6RsvStatic := xv6RsvStatic_mem_pre (by simp [xv6PreLockRegions])

theorem xv6Started_idx : xv6RsvStatic[2]? = some xv6StartedR := by
  unfold xv6RsvStatic xv6PreLockRegions; rfl

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- THE PRIMARY'S TOKEN at the deposit's issue watermark `W` (route P): half of the position
ghost, at an EVEN code ("not yet stored"; the armed codes are odd). -/
def startedPrimW (γ : GName) (W : Nat) : IProp GF := ghost_var γ (.own (1 : Qp).half) (2 * W)

/-- THE PRIMARY'S TOKEN, at some watermark. -/
def startedPrim (γ : GName) : IProp GF := iprop(∃ W : Nat, startedPrimW γ W)

/-- The armed code of the position ghost: the store's issue stamp `t`, the record's stamp `T` (a
landing position, route P) and (W8 (f2-ctx)) the record's chain bound, frozen together (odd). -/
def startedCode (t T : Nat) (a : ChainVG) : Nat := 2 * chainPair (chainPair t T) (vgCode a) + 1

theorem startedCode_inj {t T t' T' : Nat} {a a' : ChainVG} (h : startedCode t T a = startedCode t' T' a') :
    t = t' ∧ T = T' ∧ a = a' := by
  unfold startedCode at h
  obtain ⟨h1, h2⟩ := chainPair_inj (show chainPair (chainPair t T) (vgCode a) =
    chainPair (chainPair t' T') (vgCode a') by omega)
  obtain ⟨h3, h4⟩ := chainPair_inj h1
  exact ⟨h3, h4, vgCode_inj h2⟩

/-- The readers' agreement handle on the store's stamp `t`, the record's stamp `T` and the
record's bound `a` (frozen at `startedCode t T a`). -/
def startedIdx (γ : GName) (t T : Nat) (a : ChainVG) : IProp GF := ghost_var γ .discard (startedCode t T a)

instance startedIdx_persistent (γ : GName) (t T : Nat) (a : ChainVG) :
    Persistent (startedIdx (GF := GF) γ t T a) := by
  unfold startedIdx; infer_instance

instance startedIdx_timeless (γ : GName) (t T : Nat) (a : ChainVG) : Timeless (startedIdx (GF := GF) γ t T a) := by
  unfold startedIdx; infer_instance

/-- The certificates hart 0 holds, at the store's position `t`, for a chain
bound's vector (W8 (f2-ctx), F-B: what the boot hop carries). -/
def startedCerts (a : ChainVG) (t : Nat) : IProp GF :=
  iprop([∗list] p ∈ cpus.map (fun h => (h, a.1 h)), chainLb p.1 p.2 startedPrimary t)

instance startedCerts_persistent (a : ChainVG) (t : Nat) : Persistent (startedCerts (GF := GF) a t) := by
  unfold startedCerts; infer_instance

instance startedCerts_timeless (a : ChainVG) (t : Nat) : Timeless (startedCerts (GF := GF) a t) := by
  unfold startedCerts chainLb chainLbAt chainCertAt; infer_instance

/-- **The primary's landing cover** for the record's bound (route P, design D9): every other
hart's store under the bound landed at or below `K0`, which the flag store lands above
(`landsAboveAt`), and the primary's own stores under the bound are below its epoch fence's top
`s < t` -- what the publication read cashes into the reader's cover (`MachCSL.rdIn`). -/
def startedCov (a : ChainVG) (t K0 : Nat) : IProp GF := iprop%
  landCovAt (MachGS.era (hlc := hlc) (GF := GF)) a.1 startedPrimary K0 ∗ landsAboveAt t K0 ∗
    ∃ k s : Nat, epochAtE (MachGS.era (hlc := hlc) (GF := GF)) startedPrimary k s ∗
      ⌜a.1 startedPrimary ≤ s ∧ s < t⌝

instance startedCov_persistent (a : ChainVG) (t K0 : Nat) : Persistent (startedCov (GF := GF) a t K0) := by
  unfold startedCov; infer_instance

instance startedCov_timeless (a : ChainVG) (t K0 : Nat) : Timeless (startedCov (GF := GF) a t K0) := by
  unfold startedCov landCovAt landsAboveAt landsAboveAtE epochAtE; infer_instance

/-- **THE WINDOW** (W8 (f2-ctx) [R35.2]): `started` is a reserved word, so the
invariant holds HALF of its bytes, over the image history; `W` lists the
stores on top (none, or main's one). -/
def startedWin (W : WordHist 4) : IProp GF :=
  histBytes startedAddr 4 (fun _ => DFrac.own (1 : Qp).half) (W.hist startedImg)

instance startedWin_timeless (W : WordHist 4) : Timeless (startedWin (GF := GF) W) := by
  unfold startedWin histBytes; infer_instance

/-- The ARMED arm: the one store at `t`, its stamp frozen with the record's stamp `T` and (W8
(f2-ctx)) bound `a`, hart 0's certificates for `a` at `t`; route P: the record's stamp under a
position `K0` the store lands above, the primary's landing cover there (`startedCov`). -/
def startedArmed (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) : IProp GF := iprop%
  ∃ (t T K0 : Nat) (a : ChainVG), startedWin [⟨t, hartAgent startedPrimary, startedSet⟩] ∗
    startedIdx γ t T a ∗ ⌜0 < t ∧ T ≤ K0⌝ ∗ ctxStamped ξd T a.1 a.2 ∗ P ξd ∗ startedCerts a t ∗
    startedCov a t K0

/-- The UNARMED arm (W8 (f2-ctx): with hart 0's certificates for the
record's bound; route P: the record's bound under the watermark `W` the primary's token records). -/
def startedUnarmed (γ : GName) (ξd : CtxId) : IProp GF := iprop%
  startedWin [] ∗ ∃ (W T0 : Nat) (a0 : ChainVG), ghost_var γ (.own (1 : Qp).half) (2 * W) ∗
    ctxStamped ξd T0 a0.1 a0.2 ∗ vecCertsAt (MachGS.era (hlc := hlc) (GF := GF)) a0.1 a0.2 startedPrimary ∗
    ⌜∀ h, a0.1 h ≤ W⌝

/-- The invariant's body (Rocq `started_body`). -/
def startedBody (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) : IProp GF :=
  iprop(startedUnarmed γ ξd ∨ startedArmed γ ξd P)

/-- **THE INVARIANT** (Rocq `started_inv`), with the era's reserved list
named (so the flag's region is the ambient record's). -/
def startedInv (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) : IProp GF :=
  iprop(⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static⌝ ∗ inv startedN (startedBody γ ξd P))

instance startedInv_persistent (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) :
    Persistent (startedInv (GF := GF) γ ξd P) := by
  unfold startedInv; infer_instance

/-- **The handover cell** as the boot carve hands it out (W8 (f2-ctx)): the
never-written window's half, and which list the era reserved. -/
def startedCell : IProp GF := iprop(startedWin [] ∗ ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static⌝)

/-- **Allocation** (Rocq `started_alloc`): the never-written window out of
the boot carve and a stamped record context; the primary keeps half the
position ghost. -/
theorem started_alloc (E : CoPset) (ξd : CtxId) (P : CtxId → IProp GF) (T0 : Nat) :
    startedCell ∗ ctxStamped ξd T0 (fun _ => 0) 0 ⊢
      |={E}=> ∃ γ : GName, startedInv γ ξd P ∗ startedPrim γ := by
  unfold startedCell
  iintro ⟨⟨Hw, %hrsv⟩, Hst⟩
  ihave #Hc0 := vecCertsAt_zero (MachGS.era (hlc := hlc) (GF := GF)) startedPrimary
  imod ghost_var_alloc (GF := GF) (2 * 0 : Nat) with ⟨%γ, Hg⟩
  rw [show (DFrac.own 1 : DFrac) = .own ((1 : Qp).half + (1 : Qp).half) by rw [Qp.half_add_half]]
  icases ghost_var_split γ (2 * 0 : Nat) (1 : Qp).half (1 : Qp).half $$ Hg with ⟨Hg1, Hg2⟩
  imod inv_alloc startedN E (startedBody γ ξd P) $$ [Hw Hst Hg1] with #Hinv
  · inext
    unfold startedBody
    ileft
    unfold startedUnarmed
    iframe Hw
    iexists 0, T0, ((fun _ => 0), 0)
    iframe Hg1 Hst Hc0
    ipureintro; intro h; exact Nat.le_refl _
  imodintro
  iexists γ
  isplitr [Hg2]
  · unfold startedInv
    iframe Hinv
    ipureintro; exact hrsv
  · unfold startedPrim startedPrimW; iexists 0; iexact Hg2

/-- The primary's token refutes the armed arm. -/
theorem startedPrim_idx (γ : GName) (t T : Nat) (a : ChainVG) :
    startedPrim (GF := GF) γ ⊢ startedIdx γ t T a -∗ False := by
  unfold startedPrim startedPrimW startedIdx startedCode
  iintro ⟨%W, Hp⟩ Hi
  ihave %h := ghost_var_agree γ _ _ _ _ $$ Hp Hi
  omega

/-- The unarmed arm's half refutes the armed one. -/
theorem started_unarmed_idx (γ : GName) (W t T : Nat) (a : ChainVG) :
    ghost_var (GF := GF) γ (.own (1 : Qp).half) (2 * W) ⊢ startedIdx γ t T a -∗ False := by
  unfold startedIdx startedCode
  iintro Hp Hi
  ihave %h := ghost_var_agree γ _ _ _ _ $$ Hp Hi
  omega

omit [Xv6G GF] in
/-- Hart 0 is past the boot gate: it writes every publication word. -/
theorem started_gatePrim (hrsv : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    ⊢@{IProp GF} gatePassed startedPrimary := by
  unfold gatePassed gatePassedAt
  iintro
  ileft
  ipureintro
  intro f w hp
  rw [hrsv] at hp
  exact (xv6Pub_only f w hp).2

omit [Xv6G GF] in
/-- A stamped record's issue watermark (route P, design D9: the bound's components are issue
stamps under it). -/
theorem started_stampedWm (ξ : CtxId) (T : Nat) (V : CPU → Nat) (g : Nat) :
    ctxStamped (GF := GF) ξ T V g ⊢ ∃ W : Nat, itopLb W ∗ ⌜∀ h, V h ≤ W⌝ ∗ ctxStamped ξ T V g := by
  iintro H
  icases ctxStamped_cases ξ T V g $$ H with ⟨%D, %W, Hat, #HT, #HW, %hD, #Hels, Hv, %⟨hDV, hVW⟩⟩
  iexists W
  iframe HW
  isplit
  · ipureintro; exact hVW
  iapply ctxStamped_intro ξ T V g D W
  iframe Hat Hv HT HW Hels
  ipureintro; exact ⟨hD, hDV, hVW⟩

omit [Xv6G GF] in
/-- **THE DEPOSIT** (Rocq `started_store_obl`'s `ctx_deposit`), by hart 0:
hart 0 absorbs its certificates for the record's bound, the payload moves
from the running context into the record, and hart 0's certificates for the
record's new bound come out (W8 (f2-ctx)); route P: with the new record's issue watermark (what
the primary's epoch fence must pass, `started_writeAUT`). -/
theorem started_deposit [CurCtx] (ξd : CtxId) (P : CtxId → IProp GF) [CtxMorph P]
    (hrsv : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    ownCtx startedPrimary curCtx ∗ (∃ (T0 : Nat) (a0 : ChainVG), ctxStamped ξd T0 a0.1 a0.2 ∗
      vecCertsAt (MachGS.era (hlc := hlc) (GF := GF)) a0.1 a0.2 startedPrimary) ∗ P curCtx ⊢
      |==> (ownCtx startedPrimary curCtx ∗ ∃ (T W : Nat) (a : ChainVG), ctxStamped ξd T a.1 a.2 ∗
        vecCertsAt (MachGS.era (hlc := hlc) (GF := GF)) a.1 a.2 startedPrimary ∗ itopLb W ∗
        ⌜∀ h, a.1 h ≤ W⌝ ∗ P ξd) := by
  iintro ⟨Hrun, ⟨%T0, %a0, Hst, #Hc0⟩, HP⟩
  icases started_stampedWm ξd T0 a0.1 a0.2 $$ Hst with ⟨%W0, #HW0, %hVW0, Hst⟩
  imod ctx_vecAbsorb startedPrimary curCtx a0.1 a0.2 W0 hVW0 $$ [Hrun] with ⟨Hrun, #Hvf, #Hg⟩
  · iframe Hrun
    isplit
    · iexact Hc0
    · iexact HW0
  imod ctxDeposit P startedPrimary curCtx ξd T0 a0.1 a0.2 $$ [Hrun Hst HP] with
    ⟨Hrun, ⟨%T, %a, -, -, Hst, #Ha, HP⟩⟩
  · iframe Hrun Hst HP
    unfold vgFloors
    iframe Hvf Hg
  icases started_stampedWm ξd T a.1 a.2 $$ Hst with ⟨%W, #HW, %hVW, Hst⟩
  unfold vgFloors
  icases Ha with ⟨#Hav, _⟩
  icases ownCtx_vecCerts startedPrimary curCtx a.1 $$ [Hrun Hav] with ⟨Hrun, #Hca⟩
  · iframe Hrun Hav
  ihave #Hgp := started_gatePrim (hlc := hlc) (GF := GF) hrsv
  imodintro
  iframe Hrun
  iexists T, W, a
  iframe Hst HW HP
  isplitl []
  · iapply vecCertsAt_gate a.1 a.2 0 startedPrimary
    iframe Hca Hgp
  · ipureintro; exact hVW

omit [Xv6G GF] in
/-- The read watermark receipt is downward closed. -/
theorem startedRviewLb_le (cpu : CPU) (K K' : Nat) (h : K' ≤ K) :
    rviewLb (GF := GF) cpu K ⊢ rviewLb cpu K' := by
  unfold rviewLb rviewLbAt
  iintro ⟨Hv, Ht⟩
  isplitl [Hv]
  · iapply MonoNat.lb_own_le _ _ _ (by simp only [MaxNat.le_toNat]; omega) $$ Hv
  · iapply topLbAt_le _ K K' h $$ Ht

/-- What a secondary's read of the set flag certifies (route P, design D9): hart 0's chain
certificates for the record's bound, carried over, and the reader's LANDING COVER for it at its
read view (minted by the publication read, `MachCSL.rdOut`). -/
def startedRdCerts (a : ChainVG) (t : Nat) (cpu : CPU) (K : Nat) : IProp GF := iprop%
  ([∗list] p ∈ cpus.map (fun h => (h, a.1 h, t)), chainLb p.1 p.2.1 cpu 0) ∗
    landCovAt (MachGS.era (hlc := hlc) (GF := GF)) a.1 cpu K

instance startedRdCerts_persistent (a : ChainVG) (t : Nat) (cpu : CPU) (K : Nat) :
    Persistent (startedRdCerts (GF := GF) a t cpu K) := by
  unfold startedRdCerts; infer_instance

/-- What a secondary's read of the flag leaves (Rocq `started_W`): the
cleared value, or the set value with the store's handle, a read receipt past the record's stamp
(route P: a landing position), the deposit as the record holds it, and (W8 (f2-ctx)) the reader's
BOOT GATE and certificates. -/
def startedSeen (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) (cpu : CPU)
    (w : BitVec (8 * 4)) : IProp GF := iprop%
  ⌜w = startedClear⌝ ∨ ∃ (t T K : Nat) (a : ChainVG), ⌜w = startedSet ∧ T ≤ K⌝ ∗ startedIdx γ t T a ∗
    rviewLb cpu K ∗ P ξd ∗ gatePassed cpu ∗ startedRdCerts a t cpu K

/-- The pure half of the read, armed: the cleared or the set value. -/
theorem started_read_armed (Hold : Nat → Hist) (lp : LandPos) (h : Agent) (t tvn : Nat) (w : BitVec (8 * 4))
    (htail : tailOk 4 0 startedClear Hold) (hlp : lp 0 = some 0)
    (hrd : readsAreP lp h tvn (WordHist.hist [⟨t, hartAgent startedPrimary, startedSet⟩] Hold) 4 w) :
    w = startedClear ∨ w = startedSet := by
  rcases WordHist.read_cases_floorP _ Hold lp h tvn 0 0 startedClear w htail hlp (Nat.zero_le _) hrd
    with ⟨W1, e, W2, hW, -, -, rfl⟩ | ⟨-, rfl⟩
  · right
    cases W1 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hW
      obtain ⟨rfl, -⟩ := hW
      rfl
    | cons x W1 => simp at hW
  · left; rfl

/-- The pure half of the read, unarmed: the cleared value. -/
theorem started_read_unarmed (Hold : Nat → Hist) (lp : LandPos) (h : Agent) (tvn : Nat) (w : BitVec (8 * 4))
    (htail : tailOk 4 0 startedClear Hold) (hlp : lp 0 = some 0)
    (hrd : readsAreP lp h tvn (WordHist.hist ([] : WordHist 4) Hold) 4 w) : w = startedClear := by
  rcases WordHist.read_cases_floorP _ Hold lp h tvn 0 0 startedClear w htail hlp (Nat.zero_le _) hrd
    with ⟨W1, e, W2, hW, -, -, -⟩ | ⟨-, h⟩
  · simp at hW
  · exact h

/-- The read's issue request (W8 (f2-ctx)): `started` is the only publication
word, hart 0's, and in the armed window the only nonzero entry is main's
store; hart 0's certificates for the record's bound, at the store's position,
are carried over (F-B); route P: with hart 0's landing cover at `K0` (`startedCov`). -/
theorem started_rdIn (cpu : CPU) (hcpu : cpu ≠ startedPrimary) (W : WordHist 4) (a : ChainVG) (t K0 : Nat)
    (hrsv : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (hW : ∀ e ∈ W, e.tid = hartAgent startedPrimary ∧ e.t = t ∧ 0 < t) :
    startedCerts (GF := GF) a t ∗ startedCov a t K0 ⊢ rdIn cpu startedAddr 4 (W.hist startedImg)
      (some (startedPrimary, [], cpus.map (fun h => (h, a.1 h, t)), fun v => decide (v ≠ 0), a.1, K0)) := by
  simp only [rdIn]
  unfold startedCerts startedCov
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
  iintro ⟨#HC, #Hcov, #Hla, %k, %s, #Hep, %⟨hs1, hs2⟩⟩
  have hacc : ∀ e ∈ W.hist startedImg 0, decide (e.v ≠ 0) = true →
      e.tid = hartAgent startedPrimary ∧ e.t = t ∧ 0 < t := by
    intro e he hv
    unfold WordHist.hist at he
    rcases List.mem_append.1 he with he | he
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      exact hW x hx
    · simp only [startedImg, List.mem_singleton] at he
      subst he
      simp at hv
  isplitr
  · ipureintro
    refine ⟨by omega, Ne.symm hcpu, ?_, ?_, ?_, ?_⟩
    · unfold pubByteIn; rw [hrsv]; exact xv6Started_mem
    · intro f w' hp
      rw [hrsv] at hp
      exact (xv6Pub_only f w' hp).2
    · intro f w' hp hne
      rw [hrsv] at hp
      exact xv6Pub_only f w' hp
    · intro e he hv
      obtain ⟨h1, h2, h3⟩ := hacc e he hv
      refine ⟨h1, by omega, fun _ h => by simp at h, fun p hp => ?_⟩
      obtain ⟨h, -, rfl⟩ := List.mem_map.1 hp
      simp only; omega
  isplitr
  · iexact HC
  iexists t, k, s
  iframe Hcov Hla Hep
  ipureintro
  exact ⟨hs1, hs2, fun e he hv => (hacc e he hv).2.1⟩

/-- The reader's certificates for the record's bound, at a view past its cover (route P,
design D9: the cover at the read view, the view receipt after the reader's fence). -/
theorem started_vecCerts (cpu : CPU) (a : ChainVG) (t K K' : Nat) (hKK : K ≤ K') :
    startedRdCerts (GF := GF) a t cpu K ∗ gatePassed cpu ∗ viewLb cpu K' ⊢@{IProp GF}
      vecCertsAt (MachGS.era (hlc := hlc) (GF := GF)) a.1 a.2 cpu := by
  unfold startedRdCerts
  rw [BigSepL.bigSepL_map]
  unfold vecCertsAt
  iintro ⟨⟨Hl, #Hcov⟩, #Hg, #HK⟩
  isplitl [Hl]
  · iapply BigSepL.bigSepL_mono ?_ $$ Hl
    intro _ c _
    iintro #H
    iexists 0
    iexact H
  isplitl []
  · iright; iexact Hg
  iexists K'
  isplitl []
  · iright; iexact HK
  iapply landCovAt_le _ a.1 a.1 cpu K K' (fun _ _ => Nat.le_refl _) hKK $$ Hcov

/-- **A read of the flag is certified** (W8 (f2-ctx) S3): its bytes are a
publication word's -- the lock layer's exemption, `lockPubByteIn`. -/
theorem started_certs (cpu : CPU) (K : Nat) (ls : List (Nat × Nat)) (Hs : Nat → Hist)
    (hrsv : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    ⊢@{IProp GF} readCertsAt cpu startedAddr 4 K [] ls Hs [] := by
  iapply readCertsAt_of cpu startedAddr 4 K [] ls Hs [] (fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ => trivial)
  imodintro
  iintro %j %e %⟨hj, _⟩
  ileft
  unfold srcCertAt
  ileft
  ipureintro
  have hm : xv6StartedR ∈ MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) := by
    rw [hrsv]; exact (by decide +kernel : xv6StartedR ∈ xv6RsvStatic)
  refine Or.inr (Or.inr (Or.inr ⟨xv6StartedR, hm, Or.inr ⟨_, rfl⟩, ?_⟩))
  simp only [RsvRegion.bytes, RsvRegion.words, xv6StartedR, wordBytes, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

/-- Every byte of the flag's window is readable at any view: by its image entry. -/
theorem started_readable (h : Agent) (K : Nat) (W : WordHist 4) :
    ∀ j, j < 4 → readableAt h K [] [] (W.hist startedImg j) := by
  intro j _
  refine ⟨⟨0, 0, 0#8⟩, ?_, Or.inl rfl⟩
  unfold WordHist.hist startedImg
  exact List.mem_append_right _ List.mem_cons_self

/-- **THE READ, a secondary's** (Rocq `started_read_open` +
`started_read_obl`): the invariant is the accessor of the racy `lw` of the
flag (at its half, W8 (f2-ctx)), and the load's continuation learns
`startedSeen` -- the set value with the reader's boot gate and (route P) its landing cover at
its read view, past the record's stamp. -/
theorem started_readAUr (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) [∀ ξ, Persistent (P ξ)]
    (cpu : CPU) (hcpu : cpu ≠ startedPrimary) (K : Nat) (pc : BitVec 64)
    (hpc : ((pc.toNat : Nat) : Int) ∈ MachFixedGS.pubLdPcs (hlc := hlc) (GF := GF)) :
    startedInv (GF := GF) γ ξd P ⊢ LeanRV64D.Register.PC ↦ᵣ[cpu] pc -∗
      readAUr cpu startedAddr 4 K [] (fun w => iprop(LeanRV64D.Register.PC ↦ᵣ[cpu] pc ∗ startedSeen γ ξd P cpu w)) := by
  unfold startedInv
  iintro ⟨%hrsv, #Hinv⟩ HPC
  unfold readAUr
  isplitl []
  · simp only [Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
  imod (inv_acc (E := ⊤) (N := startedN) (P := startedBody γ ξd P) (CoPset.subseteq_top)) $$ Hinv
    with ⟨Hbody, Hclose⟩
  unfold startedBody startedUnarmed startedArmed
  icases Hbody with (⟨>Hw, >Hrest⟩ | ⟨%t, %T, %K0, %a, >Hw, >Hidx, >%⟨ht0, hTK0⟩, >Hst, HP, >#HC, >#Hcov⟩)
  · iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hmask
    iexists (fun _ => DFrac.own (1 : Qp).half), WordHist.hist ([] : WordHist 4) startedImg, none, [], [], some pc
    unfold startedWin
    iframe Hw
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplit
    · ipureintro; exact started_readable (hartAgent cpu) K []
    isplitl [HPC]
    · unfold rsvPcCell; iexact HPC
    isplitl []
    · ipureintro; exact hpc
    isplitl []
    · simp only [rdIn]; iempintro
    isplitl []
    · iapply rdCompBytes_nil
    isplitl []
    · iapply started_certs cpu K [] _ hrsv
    inext
    iintro %w %tvn %lp %es %ps %hKt %⟨hla, hrd, _⟩ _ %hauth #Hrv _ Hb _ HPC
    imod Hmask
    imod Hclose $$ [Hb Hrest]
    · inext
      ileft
      iframe Hb Hrest
    imodintro
    isplitl [HPC]
    · iapply (show rsvPcCell (GF := GF) cpu (some pc) ⊢ LeanRV64D.Register.PC ↦ᵣ[cpu] pc from .rfl) $$ HPC
    try dsimp only
    unfold startedSeen
    ileft
    ipureintro
    exact started_read_unarmed startedImg lp (hartAgent cpu) tvn w startedImg_tail hla.1 hrd
  · icases Hidx with #Hidx
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hmask
    iexists (fun _ => DFrac.own (1 : Qp).half),
      WordHist.hist ([⟨t, hartAgent startedPrimary, startedSet⟩] : WordHist 4) startedImg,
      some (startedPrimary, [], cpus.map (fun h => (h, a.1 h, t)), fun v => decide (v ≠ 0), a.1, K0), [], [],
      some pc
    unfold startedWin
    iframe Hw
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplit
    · ipureintro; exact started_readable (hartAgent cpu) K _
    isplitl [HPC]
    · unfold rsvPcCell; iexact HPC
    isplitl []
    · ipureintro; exact hpc
    isplitl []
    · iapply started_rdIn cpu hcpu _ a t K0 hrsv
        (fun e he => by simp at he; subst he; exact ⟨rfl, rfl, ht0⟩)
      iframe HC Hcov
    isplitl []
    · iapply rdCompBytes_nil
    isplitl []
    · iapply started_certs cpu K [] _ hrsv
    inext
    icases HP with #HP
    iintro %w %tvn %lp %es %ps %hKt %⟨hla, hrd, _⟩ _ %hauth #Hrv Hout Hb _ HPC
    imod Hmask
    imod Hclose $$ [Hb Hst]
    · inext
      iright
      iexists t, T, K0, a
      iframe Hb Hidx Hst HP HC Hcov
      ipureintro; exact ⟨ht0, hTK0⟩
    imodintro
    isplitl [HPC]
    · iapply (show rsvPcCell (GF := GF) cpu (some pc) ⊢ LeanRV64D.Register.PC ↦ᵣ[cpu] pc from .rfl) $$ HPC
    try dsimp only
    unfold startedSeen
    rcases started_read_armed startedImg lp (hartAgent cpu) t tvn w startedImg_tail hla.1 hrd with hw | hw
    · ileft; ipureintro; exact hw
    · iright
      subst hw
      simp only [rdOut]
      rw [if_pos (by decide)]
      icases Hout with ⟨#Hgp, _, #HCr, #Hcr, %hK0⟩
      iexists t, T, tvn, a
      iframe Hidx HP Hgp Hrv
      isplitl []
      · ipureintro; refine ⟨?_, by omega⟩; first | rfl | trivial
      · unfold startedRdCerts
        iframe HCr Hcr

/-- **THE ABSORB**, at a second opening after the fence (Rocq
`started_absorb`): a reader whose floor has passed the record's stamp
takes the deposit into its own context; the record stays stamped where it
was, so every hart can.  (W8 (f2-ctx): the reader's certificates for the
record's bound, from its read (the boot hop, F-B), join its context first.) -/
theorem started_absorb [CurCtx] (E : CoPset) (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF)
    [CtxMorph P] [∀ ξ, Persistent (P ξ)] (cpu : CPU) (t T K : Nat) (a : ChainVG) (hTK : T ≤ K)
    (hE : (↑startedN : CoPset) ⊆ E) :
    startedInv γ ξd P ∗ startedIdx γ t T a ∗ viewLb cpu K ∗ ownCtx cpu curCtx ∗ P ξd ∗
      vecCertsAt (MachGS.era (hlc := hlc) (GF := GF)) a.1 a.2 cpu ⊢
      |={E}=> (ownCtx cpu curCtx ∗ P curCtx) := by
  unfold startedInv
  iintro ⟨⟨%hrsv, #Hinv⟩, #Hidx, #HK, Hrun, #HP, #Hvc⟩
  imod (inv_acc (E := E) (N := startedN) (P := startedBody γ ξd P) hE) $$ Hinv with ⟨Hbody, Hclose⟩
  unfold startedBody startedUnarmed startedArmed
  icases Hbody with (⟨>Hw, >⟨%W, %T0, %a0, Hg, Hrest⟩⟩ | ⟨%t', %T', %K0, %a', >Hw, >Hidx', >%hT, >Hst, HPd, >#HC, >#Hcov⟩)
  · iexfalso
    iapply started_unarmed_idx γ W t T a $$ Hg Hidx
  · icases Hidx' with #Hidx'
    unfold startedIdx
    ihave %h := ghost_var_agree γ _ _ _ _ $$ Hidx' Hidx
    obtain ⟨rfl, rfl, rfl⟩ := startedCode_inj h
    icases started_stampedWm ξd T' a'.1 a'.2 $$ Hst with ⟨%Wd, #HWd, %hVW, Hst⟩
    imod ctx_vecAbsorb cpu curCtx a'.1 a'.2 Wd hVW $$ [Hrun] with ⟨Hrun, #Hvf, #Hg⟩
    · iframe Hrun
      isplit
      · iexact Hvc
      · iexact HWd
    imod ctxAbsorbLb P cpu ξd curCtx T' K a'.1 a'.2 hTK $$ [Hrun Hst] with ⟨Hrun, Hst, HP'⟩
    · iframe Hrun Hst HP HK
      unfold vgFloors
      iframe Hvf Hg
    imod Hclose $$ [Hw Hst]
    · inext
      iright
      iexists t', T', K0, a'
      iframe Hw Hidx' Hst HP HC Hcov
      ipureintro; exact hT
    imodintro
    iframe Hrun HP'


/-! ## The primary's store (Rocq `started_store_obl`), in two openings

The deposit needs the running token, which the store's accessor does not
see, so it runs at a first opening, before the store: the payload is
deposited into `ξd` and the (unarmed) window closed again with the new
stamp and (route P) the new record's issue watermark `W` recorded in the primary's token.  The
primary's epoch-opening `fence rw,rw` then passes `W` (its epoch token's top `s ≥ W`).  The
store's accessor (`MachCSL.writeAUT`) is the second opening: it names the token's top as the
order bound, the record's stamp and the primary's cover position as the position the flag store
lands above, and arms the invariant (`started_writeAUT`). -/

/-- **The deposit**, at a first opening: the payload moves from the
primary's context into `ξd`, whose stamp advances; the window stays
unarmed (the payload is persistent and is kept outside); the primary's token records the new
record's issue watermark. -/
theorem started_deposit_open [CurCtx] (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) [CtxMorph P]
    [∀ ξ, Persistent (P ξ)] :
    startedInv γ ξd P ∗ startedPrim γ ∗ ownCtx startedPrimary curCtx ∗ P curCtx ⊢
      |={⊤}=> (ownCtx startedPrimary curCtx ∗ ∃ W : Nat, startedPrimW γ W ∗ itopLb W ∗ P ξd) := by
  unfold startedInv
  iintro ⟨⟨%hrsv, #Hinv⟩, Hprim, Hrun, HP⟩
  imod (inv_acc (E := ⊤) (N := startedN) (P := startedBody γ ξd P) CoPset.subseteq_top) $$ Hinv
    with ⟨Hbody, Hclose⟩
  unfold startedBody startedUnarmed startedArmed
  icases Hbody with (⟨>Hw, >⟨%W0, %T0, %a0, Hg, Hst, #Hc0, %hW0⟩⟩ | ⟨%t, %T, %K0, %a, >Hw, >Hidx, >%hT, >Hst, HPd, >HC, >Hcov⟩)
  · imod started_deposit ξd P hrsv $$ [Hrun Hst HP] with ⟨Hrun, %T, %W, %a, Hst, #Hca, #HW, %hVW, #HPd⟩
    · iframe Hrun HP
      iexists T0, a0
      iframe Hst Hc0
    unfold startedPrim startedPrimW
    icases Hprim with ⟨%W1, Hprim⟩
    imod ghost_var_update_halves (2 * W) γ (2 * W1) (2 * W0) $$ Hprim Hg with ⟨H1, H2⟩
    imod Hclose $$ [Hw H2 Hst]
    · inext
      ileft
      iframe Hw
      iexists W, T, a
      iframe H2 Hst Hca
      ipureintro; exact hVW
    imodintro
    iframe Hrun
    iexists W
    iframe H1 HW HPd
  · iexfalso
    iapply startedPrim_idx γ t T a $$ Hprim Hidx

/-- **No publication word is written while hart 0 holds its token** (W8
(f3-ptek) [OWN.66]: what the kernel table's seal needs, `MachCSL.kptOn_seal`'s
`pubClean`): `started` is xv6's only publication word, and until hart 0's
store its window is the image's. -/
theorem started_pubClean (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) :
    ⊢ startedInv γ ξd P -∗ startedPrim γ -∗ ∀ m : FlatMem, genHeapInterp m ={⊤}=∗
      genHeapInterp m ∗ ⌜pubClean (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) m⌝ ∗ startedPrim γ := by
  unfold startedInv
  iintro ⟨%hrsv, #Hinv⟩ Hprim %m Hmem
  imod (inv_acc (E := ⊤) (N := startedN) (P := startedBody γ ξd P) CoPset.subseteq_top) $$ Hinv
    with ⟨Hbody, Hclose⟩
  unfold startedBody startedUnarmed startedArmed
  icases Hbody with (⟨>Hw, >Hrest⟩ | ⟨%t, %T, %K0, %a, >Hw, >Hidx, >%hT, >Hst, HPd, >HC, >Hcov⟩)
  · ihave %hget := histBytes_valid m startedAddr 4 _ _ $$ [Hmem Hw]
    · unfold startedWin; iframe Hmem Hw
    imod Hclose $$ [Hw Hrest]
    · inext
      ileft
      iframe Hw Hrest
    imodintro
    iframe Hmem Hprim
    ipureintro
    intro f w hf a ha H hH e he
    rw [hrsv] at hf
    obtain ⟨rfl, rfl⟩ := xv6Pub_only f w hf
    simp only [RsvRegion.bytes, RsvRegion.words, wordBytes, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [hget j hj] at hH
    obtain rfl := Option.some.inj hH
    simp only [WordHist.hist, List.map_nil, List.nil_append, startedImg, List.mem_singleton] at he
    rw [he]
  · iexfalso
    iapply startedPrim_idx γ t T a $$ Hprim Hidx

/-- **The flag store's obligation, history-aware** (W8 (f2-ctx) [R35.2]): the
first post-power-on store of hart 0 into the never-written window keeps the
publication region's discipline -- every post-power-on entry is hart 0's, at
one timestamp.  (The history-free `MachCSL.rsvWordOk` cannot say this.) -/
theorem started_rsvStoreOk (hrsv : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    rsvStoreOkP (hlc := hlc) (GF := GF) startedPrimary startedAddr 4 startedSet startedImg [] := by
  refine ⟨2, 0, xv6StartedR, by rw [hrsv]; exact xv6Started_idx, rfl, fun m t ht hget _ _ => ?_⟩
  have hbytes : ∀ a ∈ xv6StartedR.bytes, ∃ j, j < 4 ∧ a = startedAddr + BitVec.ofNat 64 j := by
    intro a ha
    simp only [xv6StartedR, RsvRegion.bytes, RsvRegion.words, wordBytes, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨j, hj, rfl⟩
  have hnew : ∀ j, j < 4 → (m.writeBytes startedAddr 4 startedSet t (hartAgent startedPrimary))[startedAddr +
      BitVec.ofNat 64 j]? = some [⟨t, hartAgent startedPrimary, nthByte startedSet j⟩, ⟨0, 0, 0#8⟩] := by
    intro j hj
    rw [writeBytes_at m startedAddr startedSet t _ (by decide) hj (startedImg j) (hget j hj)]
    rfl
  unfold regionOk
  simp only [xv6StartedR]
  refine ⟨fun a ha H hH e he he0 => ?_, fun a ha H hH e he e' he' he0 he0' => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := hbytes a ha
    rw [hnew j hj] at hH
    cases hH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rfl
    · exact absurd rfl he0
  · obtain ⟨j, hj, rfl⟩ := hbytes a ha
    rw [hnew j hj] at hH
    cases hH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he he'
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;> simp_all


omit [Xv6G GF] in
/-- Two position receipts give one at their max. -/
theorem started_topLb_max (K1 K2 : Nat) : topLb (GF := GF) K1 ∗ topLb K2 ⊢ topLb (max K1 K2) := by
  iintro ⟨#H1, #H2⟩
  rcases Nat.le_total K1 K2 with h | h
  · rw [Nat.max_eq_right h]; iexact H2
  · rw [Nat.max_eq_left h]; iexact H1

/-- **The store's accessor**, at a second opening: the window's histories
(the reserved half, W8 (f2-ctx)), the history-aware obligation, the arming, and (mcslrec (2)
[OWN.82] (a1)) the store's own pc, a release site, read off the lent `PC` cell.  Route P: the
order bound is the primary's epoch-fence token's top `s` (which passed the deposit's watermark
`W`, so the record's own component is under it); the flag store's lands-above position is the
record's stamp and the primary's cover position, joined. -/
theorem started_writeAUT (γ : GName) (ξd : CtxId) (P : CtxId → IProp GF) [∀ ξ, Persistent (P ξ)]
    (pc : BitVec 64) (hrel : ((pc.toNat : Nat) : Int) ∈ MachFixedGS.relPcs (hlc := hlc) (GF := GF))
    (W k s S0 L0 : Nat) (hWs : W ≤ s) (hS0 : S0 ≤ s) :
    startedInv (GF := GF) γ ξd P ∗ startedPrimW γ W ∗ P ξd ∗
      kptSealedAt (MachGS.era (hlc := hlc) (GF := GF)) S0 L0 ∗ topLb L0 ∗
      epochAtE (MachGS.era (hlc := hlc) (GF := GF)) startedPrimary k s ∗ itopLb s ⊢
      LeanRV64D.Register.PC ↦ᵣ[startedPrimary] pc -∗
      writeAUT startedPrimary startedAddr 4 startedSet iprop(LeanRV64D.Register.PC ↦ᵣ[startedPrimary] pc ∗ emp) := by
  unfold startedInv
  iintro ⟨⟨%hrsv, #Hinv⟩, Hprim, #HP, #Hsl, #HL0, #Hep, #Hs⟩ HPC
  unfold writeAUT
  imod (inv_acc (E := ⊤) (N := startedN) (P := startedBody γ ξd P) CoPset.subseteq_top) $$ Hinv
    with ⟨Hbody, Hclose⟩
  unfold startedBody startedUnarmed startedArmed
  icases Hbody with (⟨>Hw, >⟨%W0, %T0, %a0, Hg, Hst, #Hc0, %hW0⟩⟩ | ⟨%t, %T, %K0, %a, >Hw, >Hidx, >%hT, >Hst, HPd, >HC, >Hcov⟩)
  · unfold startedPrimW
    ihave %hW := ghost_var_agree γ _ _ _ _ $$ Hprim Hg
    have hW0s : ∀ h, a0.1 h ≤ s := fun h => by have := hW0 h; omega
    icases ctxStamped_topLb ξd T0 a0.1 a0.2 $$ Hst with ⟨#HT, Hst⟩
    icases ctxStamped_rtList ξd T0 a0.1 a0.2 startedPrimary $$ [Hst Hc0] with ⟨Hst, HL⟩
    · iframe Hst Hc0
    -- the primary's cover position
    unfold vecCertsAt
    icases Hc0 with ⟨_, _, %Kc, #HKc, #Hcov⟩
    ihave #HKc' : topLb Kc $$ []
    · icases HKc with (%h0 | #HKc)
      · rw [h0]; iapply topLbAt_0
      · iapply viewLb_topLb startedPrimary Kc $$ HKc
    ihave #HK0 := started_topLb_max T0 Kc $$ [HT HKc']
    · iframe HT HKc'
    ihave #HK1 := started_topLb_max (max T0 Kc) L0 $$ [HK0 HL0]
    · iframe HK0 HL0
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hmask
    iright
    iexists WordHist.hist ([] : WordHist 4) startedImg, s, max (max T0 Kc) L0, [], some (cpus.map (fun h => (h, a0.1 h))),
      some pc
    unfold startedWin
    iframe Hw Hs HK1
    isplitr
    · unfold compBytes; iempintro
    isplitr
    · ipureintro
      rw [WordHist.hist_nil]
      exact started_rsvStoreOk hrsv
    isplitr
    · unfold pubDepIn
      iexists k, S0, L0
      iframe Hep Hsl
      ipureintro; exact ⟨hS0, Nat.le_max_right _ _⟩
    isplitl [HL]
    · unfold rtIn; iexact HL
    isplitl [HPC]
    · unfold rsvPcCell; iexact HPC
    isplitr
    · ipureintro; exact hrel
    inext
    iintro %t %hst %ht0 Hb _ HPC _ _ #Hla Hout
    ihave #Hla := landsAboveAtE_le _ t _ (max T0 Kc) (Nat.le_max_left _ _) $$ Hla
    rw [WordHist.hist_push] at *
    imod Hmask
    imod ghost_var_update_halves (startedCode t T0 a0) γ (2 * W) (2 * W0) $$ Hprim Hg with ⟨H1, -⟩
    imod ghost_var_persist γ _ (startedCode t T0 a0) $$ H1 with #H1
    imod Hclose $$ [Hb Hst Hout]
    · inext
      iright
      iexists t, T0, max T0 Kc, a0
      iframe Hb Hst HP
      isplit
      · unfold startedIdx; iexact H1
      isplit
      · ipureintro; exact ⟨ht0, Nat.le_max_left _ _⟩
      isplitl [Hout]
      · unfold rtOut startedCerts; iexact Hout
      · unfold startedCov
        isplitl []
        · iapply landCovAt_le _ a0.1 a0.1 startedPrimary Kc (max T0 Kc) (fun _ _ => Nat.le_refl _)
            (Nat.le_max_right _ _) $$ Hcov
        iframe Hla
        iexists k, s
        iframe Hep
        ipureintro; exact ⟨hW0s startedPrimary, hst⟩
    imodintro
    isplitl [HPC]
    · iapply (show rsvPcCell (GF := GF) startedPrimary (some pc) ⊢
        LeanRV64D.Register.PC ↦ᵣ[startedPrimary] pc from .rfl) $$ HPC
    · iempintro
  · iexfalso
    iapply startedPrim_idx γ t T a $$ [Hprim] Hidx
    unfold startedPrim
    iexists W
    iexact Hprim

end

end Xv6
