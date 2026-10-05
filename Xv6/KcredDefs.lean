/-
**The page credits** (NI M3 quotas Q-1; design
`claude-notes/projects/noninterference.md` "M3 quotas design", R7).

A page credit is a reservation against the allocator's free pool: the
holder of `pageCredit n` may `kalloc` `n` pages and is never told "no".
The AUTHORITY (`credAuth c`, the total `c` of credits outstanding) lives
in `kmem.lock`'s payload, where the allocator ties it to the free count
(`KallocDefs.kmemCnt`: `c ≤ n` once the count is sealed), so a credited
`kalloc` finds the free list nonempty (`SpecKalloc.wp_kalloc_cred`) and a
credited `kfree` mints the credit back (`SpecKfree.wp_kfree_cred`).

The camera is `Auth (Option UFrac)` -- `IrefSlots`' and the tracked
sleeplock's, the shared `Xv6G.authUfracG` -- at the canonical name
`WchG.wkcName` (SlotGen deviation 14), counted in whole units by
`IrefSlots.natUfrac`.  The credits are minted ONCE, at power-on
(`WaitInvTies.childrenRes_alloc`): `credAuth credTotal ∗ pageCredit
credTotal`; the authority goes to the allocator, the fragments to the 64
proc slots (`slotShare` each) and the pipe lock (`NPIPE`).

THE PIPE TICKETS (`npTicket` / `npTicketAuth`, at `WchG.wnpName`, the same
camera): `npipelock`'s payload counts the live pipe buffers `npipe` as a
ticket authority, every live pipe holds one ticket, so `pipeclose`'s
`npipe--` never drops the counter below zero.

## Deviations from the design

1. `kCredit γk n` is `pageCredit n`: the credit is not keyed by the
   allocator's names (`KmemNames`), whose `fsReadyKmem` spelling needs
   `[Fscfg]` in the page table's, the slot's and the pipe lock's contexts;
   the canonical `WchG` name serves every allocator a proof may name (a
   payload `kmemRes γk` holds the authority at that name).
2. The pipe tickets are new: the design's `NPIPE - npipe` credits alone do
   not bound the counter from below at `pipeclose`'s decrement.

Imports only definitional files.
-/
import Xv6.SlotGen
import Xv6.IrefSlots
import Xv6.QuotaDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

/-- The credits' camera: `IrefSlots.IrefslotRF`'s functor. -/
abbrev KcredRF : COFE.OFunctorPre := constOF (Auth (Option UFrac))

/-! ## Whole units: the local updates -/

theorem natUfrac_succ (k : Nat) : natUfrac (k + 1) = some (⟨natQp k⟩ : UFrac) := rfl

/-- Returning `k` of `c` units. -/
theorem natUfrac_lu_spend (c k : Nat) (h : k ≤ c) :
    (natUfrac c, natUfrac k) ~l~> (natUfrac (c - k), natUfrac 0) := by
  obtain ⟨r, rfl⟩ : ∃ r, c = k + r := ⟨c - k, by omega⟩
  rw [show k + r - k = r by omega]
  cases k with
  | zero =>
    rw [Nat.zero_add]
  | succ k =>
    cases r with
    | zero =>
      rw [Nat.add_zero, natUfrac_succ]
      exact LocalUpdate.delete_option_cancelable (some (⟨natQp k⟩ : UFrac))
    | succ r =>
      have hc := LocalUpdate.cancel (some (⟨natQp k⟩ : UFrac)) (natUfrac (r + 1)) (none : Option UFrac)
      rw [← natUfrac_succ, ← natUfrac_op] at hc
      exact hc

/-- Minting `k` more units. -/
theorem natUfrac_lu_mint (c k : Nat) :
    (natUfrac c, natUfrac 0) ~l~> (natUfrac (c + k), natUfrac k) := by
  cases k with
  | zero => exact fun _ _ vx e => ⟨vx, e⟩
  | succ k =>
    cases c with
    | zero =>
      rw [Nat.zero_add, natUfrac_succ]
      exact LocalUpdate.alloc_option (natUfrac 0) trivial
    | succ c =>
      have h := LocalUpdate.op_discrete (natUfrac (c + 1)) (natUfrac 0) (natUfrac (k + 1))
        (fun _ => by
          rw [← natUfrac_op, show k + 1 + (c + 1) = (k + c + 1) + 1 by omega, natUfrac_succ]; trivial)
      rw [← natUfrac_op, ← natUfrac_op, Nat.add_zero, Nat.add_comm (k + 1)] at h
      exact h

section
variable {GF : BundledGFunctors} [Xv6G GF] [WchG GF]

/-! ## The credits -/

/-- **`n` page credits**: `n` pages of the free pool reserved for the holder. -/
def pageCredit (n : Nat) : IProp GF :=
  iOwn (F := KcredRF) (WchG.wkcName GF) (◯ natUfrac n)

/-- **The credit authority**: `c` credits are outstanding.  It lives in
`kmem.lock`'s payload (`KallocDefs.kmemCnt`). -/
def credAuth (c : Nat) : IProp GF :=
  iOwn (F := KcredRF) (WchG.wkcName GF) (● natUfrac c)

instance pageCredit_timeless (n : Nat) : Timeless (pageCredit (GF := GF) n) := by
  unfold pageCredit; infer_instance

instance credAuth_timeless (c : Nat) : Timeless (credAuth (GF := GF) c) := by
  unfold credAuth; infer_instance

/-- Credits split and join. -/
theorem pageCredit_op (a b : Nat) :
    pageCredit (GF := GF) (a + b) ⊣⊢ pageCredit a ∗ pageCredit b := by
  unfold pageCredit
  rw [natUfrac_op, Auth.frag_op]
  exact iOwn_op

theorem pageCredit_split (a b : Nat) :
    pageCredit (GF := GF) (a + b) ⊢ pageCredit a ∗ pageCredit b := (pageCredit_op a b).1

theorem pageCredit_join (a b : Nat) :
    pageCredit (GF := GF) a ∗ pageCredit b ⊢ pageCredit (a + b) := (pageCredit_op a b).2

/-- Taking `k ≤ n` of `n` credits. -/
theorem pageCredit_take (n k : Nat) (h : k ≤ n) :
    pageCredit (GF := GF) n ⊢ pageCredit k ∗ pageCredit (n - k) := by
  have e : n = k + (n - k) := by omega
  refine .trans (.of_eq (congrArg _ e)) ?_
  exact pageCredit_split k (n - k)

/-- Moving `n = m` (the credits are a number). -/
theorem pageCredit_congr (n m : Nat) (h : n = m) :
    pageCredit (GF := GF) n ⊢ pageCredit m := by subst h; exact .rfl

/-- No credits: nothing to hold. -/
theorem pageCredit_zero : ⊢ |==> pageCredit (GF := GF) 0 := by
  unfold pageCredit
  have e : (◯ natUfrac 0 : Auth (Option UFrac)) = (UCMRA.unit : Auth (Option UFrac)) := rfl
  rw [e]
  exact iOwn_unit

/-- Credits are bounded by the authority. -/
theorem credAuth_bound (c k : Nat) :
    credAuth (GF := GF) c ∗ pageCredit k ⊢ ⌜k ≤ c⌝ := by
  unfold credAuth pageCredit
  iintro ⟨Ha, Hf⟩
  icombine Ha Hf gives %Hv
  ipureintro
  exact natUfrac_incl k c (Auth.auth_both_valid_discrete.mp Hv).1

/-- **Spending credits**: the authority goes down by what comes back. -/
theorem credAuth_spend (c k : Nat) :
    credAuth (GF := GF) c ∗ pageCredit k ⊢ |==> (⌜k ≤ c⌝ ∗ credAuth (c - k)) := by
  unfold credAuth pageCredit
  iintro ⟨Ha, Hf⟩
  icombine Ha Hf gives %Hv
  have hk := natUfrac_incl k c (Auth.auth_both_valid_discrete.mp Hv).1
  imod iOwn_update_op (a' := (● natUfrac (c - k) : Auth (Option UFrac))) $$ [$Ha $Hf] with Ha
  · exact Auth.auth_update_dealloc (natUfrac_lu_spend c k hk)
  imodintro
  isplitr
  · ipureintro; exact hk
  iexact Ha

/-- **Minting credits**: the authority goes up by what is handed out. -/
theorem credAuth_mint (c k : Nat) :
    credAuth (GF := GF) c ⊢ |==> (credAuth (c + k) ∗ pageCredit k) := by
  unfold credAuth pageCredit
  iintro Ha
  imod iOwn_update (a' := ((● natUfrac (c + k) : Auth (Option UFrac)) • ◯ natUfrac k)) $$ Ha with H
  · exact Auth.auth_update_alloc (natUfrac_lu_mint c k)
  icases iOwn_op $$ H with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf

/-! ## The pipe tickets -/

/-- `n` pipe tickets: `n` buffers counted in `npipe`. -/
def npTicket (n : Nat) : IProp GF :=
  iOwn (F := KcredRF) (WchG.wnpName GF) (◯ natUfrac n)

/-- The ticket authority: `c` buffers counted (`npipelock`'s payload). -/
def npTicketAuth (c : Nat) : IProp GF :=
  iOwn (F := KcredRF) (WchG.wnpName GF) (● natUfrac c)

instance npTicket_timeless (n : Nat) : Timeless (npTicket (GF := GF) n) := by
  unfold npTicket; infer_instance

instance npTicketAuth_timeless (c : Nat) : Timeless (npTicketAuth (GF := GF) c) := by
  unfold npTicketAuth; infer_instance

/-- A ticket says the count is positive, and comes back. -/
theorem npTicket_return (c : Nat) :
    npTicketAuth (GF := GF) c ∗ npTicket 1 ⊢ |==> (⌜1 ≤ c⌝ ∗ npTicketAuth (c - 1)) := by
  iintro ⟨Ha, Hf⟩
  unfold npTicketAuth npTicket
  icombine Ha Hf gives %Hv
  have hk := natUfrac_incl 1 c (Auth.auth_both_valid_discrete.mp Hv).1
  imod iOwn_update_op (a' := (● natUfrac (c - 1) : Auth (Option UFrac))) $$ [$Ha $Hf] with Ha
  · exact Auth.auth_update_dealloc (natUfrac_lu_spend c 1 hk)
  imodintro
  isplitr
  · ipureintro; exact hk
  iexact Ha

/-- Counting a buffer hands out its ticket. -/
theorem npTicket_mint (c : Nat) :
    npTicketAuth (GF := GF) c ⊢ |==> (npTicketAuth (c + 1) ∗ npTicket 1) := by
  unfold npTicketAuth npTicket
  iintro Ha
  imod iOwn_update (a' := ((● natUfrac (c + 1) : Auth (Option UFrac)) • ◯ natUfrac 1)) $$ Ha with H
  · exact Auth.auth_update_alloc (natUfrac_lu_mint c 1)
  icases iOwn_op $$ H with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf

/-- **The power-on credits** (`WaitInvTies.childrenRes_alloc`): the
authority and every credit at `credTotal`, the ticket authority at `0`.  The
boot routes them: the authority to the allocator's payload
(`KmemGhost.kmemGhost_alloc`), `slotShare` credits to every proc slot's
UNUSED block (`ProcDefs.procDormantPrestk`), `NPIPE` credits and the ticket
authority to `npipelock`'s payload (`NpipeDefs.npipeShare_boot`). -/
def credBoot : IProp GF := iprop%
  credAuth credTotal ∗ pageCredit credTotal ∗ npTicketAuth 0

end

/-! ## The power-on mint (`WaitInvTies.childrenRes_alloc`) -/

/-- **The credit supply at power-on**: at a fresh name, the authority and
all `credTotal` credits. -/
theorem credSupply_alloc {GF : BundledGFunctors} [Xv6G GF] :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      iOwn (F := KcredRF) γ (● natUfrac credTotal) ∗ iOwn (F := KcredRF) γ (◯ natUfrac credTotal) := by
  imod iOwn_alloc (F := KcredRF) (GF := GF)
      ((● natUfrac credTotal : Auth (Option UFrac)) • ◯ natUfrac credTotal) with ⟨%γ, H⟩
  · exact Auth.auth_both_valid_discrete.mpr ⟨CMRA.inc_refl _, by simp [credTotal, natUfrac]; trivial⟩
  imodintro
  iexists γ
  icases iOwn_op $$ H with ⟨Ha, Hf⟩
  iframe Ha Hf

/-- **The ticket authority at power-on**: no buffer counted. -/
theorem npTickets_alloc {GF : BundledGFunctors} [Xv6G GF] :
    ⊢@{IProp GF} |==> ∃ γ : GName, iOwn (F := KcredRF) γ (● natUfrac 0) := by
  imod iOwn_alloc (F := KcredRF) (GF := GF) (● natUfrac 0 : Auth (Option UFrac)) with ⟨%γ, H⟩
  · exact Auth.auth_valid.mpr trivial
  imodintro
  iexists γ
  iexact H

end Xv6
