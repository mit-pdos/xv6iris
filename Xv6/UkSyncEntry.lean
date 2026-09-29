/-
**/sync's ENTRY THEOREM, PROVED** (Rocq `UkSyncEntry.v`, as landed by
b23e6791f -- drift SY2).

Rocq's header, in short: the mould is `UkSeccEntry`'s at a status-independent
payload; the persistent premise `□ syncPay P (Q (-1))` is what /sync spends
AFTER `sync()` returned (`wp_syncMain`).  The union's round lends the round's
credential and pays PEND at RAN (`UshURoundSync.uHchild_sync`).  The program
reads neither its argv nor its table, so the entry takes no row about either:
its ledger, working directory, children and pid are dropped.

## Deviations from Rocq

1. **Pre-hook** (`UkSyncDefs` deviation 2): b23e6791f's statement.  Rocq
   main's `ksync_leaf_xv6`, the hook riding the lend (`Pay := P ∗ hook_opt
   gen_id oQ`) and `sync_pay P (Q_opt oQ) (Q (-1))` are the durability lanes'.
2. **Two images** (as `UkSeccEntry` deviation 2): the node at the key image
   `M : ElfMem`, the argument reading at the page view `Mv`, `imgAgrees M Mv`
   between them.
3. `wp_ksync_start` is `SYNC_START` (DU10): the entry is proved at a
   `GS : SYNC_START` and closed at the engine by `syncImageEntry_of_leaves UL`
   (`LinkSync.sync_linked`, `UkSysPHolds.ukSysP_holds`).
4. **DU3**: `sync_code_of_text` is `ukCode γt User.Sync.code.byte`, read off
   `utextAll` by `UserHeap.utextAll_img` at the code segment's rows
   (`syncCode_rows`, NEW, `UkSeccEntry.seccCode_rows`' twin at `0xd54` bytes).
5. Rocq's `ukn_const_of_eq N Q Hpayeq HQc` is `ukn_const_of_eq`; the budget
   is Rocq's 38 + 4 = the key's 42 words.
-/
import Xv6.ExecEntry
import Xv6.ElfUser
import Xv6.UshEchoArgs
import Xv6.UshSync
import Xv6.LinkSync
import Xv6.UkSysPHolds

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Iris.Std.PartialMap
open Std (ExtTreeSet)

set_option linter.unusedSectionVars false

/-- NEW (deviation 4): the code-segment readings `utextAll_img` asks for, at
a key whose page 0 is X-and-not-W. -/
theorem syncCode_rows (M : ElfMem) (π : Nat → Option UPerm) (hsub : uimgSub User.Sync.code.byte M)
    (hx : ∀ a, a < 4096 → uxAddr π a ∧ ¬ uwAddr π a) :
    ∀ a b, User.Sync.code.byte a = some b → M a = some b ∧ uxAddr π a ∧ ¬ uwAddr π a ∧ a < uCap := by
  intro a b hab
  have hv : User.Sync.code.vaddr = 0 := rfl
  have hs : User.Sync.code.size = 0xd54 := rfl
  have ha : a < 0xd54 := by
    unfold User.USeg.byte at hab
    split at hab
    · omega
    · cases hab
  exact ⟨hsub a b hab, (hx a (by omega)).1, (hx a (by omega)).2, by unfold uCap; omega⟩

section UkSyncEntry
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FsTopG GF] [OffboxG GF]
  [Appcfg GF] [FsBytesG GF] [CtokG GF] [Fscfg] [Icfg] [PS : UprogSG GF]
  [GhostMapG GF Nat (BitVec 8) RegMapF] [GhostVarG GF Nat] [GhostMapG GF (Option Nat) UfdCell UfdMapF]
  [GhostVarG GF (ExtTreeSet GName compare)] [GhostVarG GF Int]

/-- **Rocq `UkSyncEntry.sync_image_entry`'s statement** (deviations 1-2). -/
def SyncImageEntry : Prop :=
  ∀ (ws : List (List (BitVec 8))) (M : ElfMem) (Mv : Nat → List (BitVec 8)) (sv t : Nat)
    (gn : Nat → BitVec 8) (sts : List FdState) (cw : Nat) (cs : ExtTreeSet GName compare)
    (pidv : BitVec 32) (Q : Int → IProp GF) (P : IProp GF),
    (∀ k : Int, freeNum k → UprogSG.psok (GF := GF) k) → (∀ x y : Int, Q x = Q y) → execOk ws →
    echoNodeImg ws M sv t gn → imgAgrees M Mv → ushEchoArgvBytes ws gn → sts.length = NOFILE →
    ⊢ □ syncPay P (Q (-1)) -∗ urunNopipe (hlc := hlc) sts -∗ udep (hlc := hlc) -∗
      imageEntry User.Sync.elf Mv (BitVec.ofNat 64 (t + 8)) sts cw seccAll cs pidv Q P (uslot (hlc := hlc))

/-- **Rocq `UkSyncEntry.sync_image_entry`**: THE ENTRY (deviations 3-5). -/
theorem syncImageEntry_holds (GS : SYNC_START) : SyncImageEntry (hlc := hlc) (GF := GF) := by
  intro ws M Mv sv t gn sts cw cs pidv Q P hps hQc hok himg hag hbytes hfdl
  iintro #Hpay #Hnpw #Hdep
  iapply imageEntry_of_at
  imodintro
  iintro %na %alen %afun %hargs
  -- the caller's reading is the node's words
  obtain ⟨hna, halen, -⟩ := echoArgsDetX_holds ws hok M Mv sv t gn na alen afun himg hbytes hag hargs
  have hroom := syncRoom_of_det_x ws na alen hok hna halen
  unfold imageEntryAt
  imodintro
  iintro %W' %hokk %hcwv %hlzf %hscf - - Hmp HP
  -- the key's geometry
  obtain ⟨hpc, hsub, hx, -, hwr, hrp⟩ := syncKexecPages na alen afun sts W' hokk
  obtain ⟨hroom336, hal8, -, hstkrow, -, -, -, hfdlen, hstop⟩ :=
    syncKexecEntryRows na alen afun sts W' hokk hroom hfdl hwr hrp
  have hfd : W'.fd = sts := kexecImageOk_fd hokk
  have hcode := syncCode_rows W'.M W'.perm hsub hx
  ihave #Hnpw' : urunNopipe (hlc := hlc) W'.fd $$ []
  · rw [hfd]; iexact Hnpw
  -- the slot; sync makes no descriptor call, no chdir, no fork and no getpid,
  -- so its ledger, its working directory, its children and its pid are
  -- dropped here
  iapply uslot_of_urun W' 42 Q hal8 (show 8 * 42 ≤ (uvisSp W').toNat by omega) hstkrow
    hfdlen hstop hlzf hscf $$ Hdep Hnpw' Hmp
  rw [hpc]
  iintro %N' %h %hpayeq - - Ht - - - - Hrun
  ihave Hcode := utextAll_img N'.t W'.M W'.perm User.Sync.code.byte hcode $$ Ht
  -- the program
  iapply GS.wp_syncStart hps N' h (tfResumeGpr0 W'.tf) 42 P (ukn_const_of_eq N' Q hpayeq hQc) (by decide)
    $$ Hcode HP []
  · rw [hpayeq]; iexact Hpay
  · iexact Hrun

/-- `SyncImageEntry` at the engine: sync's `start` from the landed link
(`LinkSync.sync_linked`, the row leaves `UkSysPHolds.ukSysP_holds`). -/
theorem syncImageEntry_of_leaves (UL : UK_LEAVES) : SyncImageEntry (hlc := hlc) (GF := GF) :=
  syncImageEntry_holds (sync_linked UL (ukSysP_holds UL)).2

end UkSyncEntry

end Xv6
