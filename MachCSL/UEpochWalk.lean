/-
MachCSL: **the supervisor-mode walk of an open epoch's user table** (W8
(f3-utext) [OWN.89] (W-R)): userret's trampoline after its `csrw satp` and
uservec's before its own run under the hart's user table while the epoch is
open, the table's slots three quarters the hart's (`Xv6.uptSlot`), a quarter
the interpretation's.  The walk reads the slots at three quarters
(`swp_pt_walk_own` at any fraction); the A/D write-back of the leaf goes
through the epoch's arm (`MachCSL.swp_sail_mem_write_excl_upt`), with the
walk's two pointer slots, the hart's `satp`/privilege cells and the
open-epoch witness (the kernel root's ghost and the root being another).

Twins of `WpPtWalkOwn`'s `swp_checked_mem_write_pte8_cond_S_ctx`,
`swp_write_pte_conditional_ctx`, `swp_update_and_write_pte_own`,
`swp_translate_TLB_hit_own`, `swp_translate_TLB_miss_own`,
`swp_translateAddr_own`, the leaf at three quarters.
-/
import MachCSL.UEpochArm

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- The hart's share of a slot of its open epoch's table. -/
abbrev dqUpt : DFrac := DFrac.own Qp.threeQuarters

theorem uepLeafB_kLeaf (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1) : uepLeafB (kLeaf ppn perm a d) = true := by
  have h := kLeaf_valid ppn perm a d
  unfold uepLeafB
  simp only [h.1, Bool.true_and, bne_iff_ne, ne_eq]
  exact h.2

theorem uepAD_kLeaf (ppn : BitVec 44) (perm : KPerm) (a d a' d' : BitVec 1) :
    uepAD (kLeaf ppn perm a d) (kLeaf ppn perm a' d') :=
  ⟨a', d', by unfold kLeaf; rw [pteSetAD_pteSetAD]⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- The conditional physical write of a leaf of the open epoch's table,
after the exclusive read. -/
theorem swp_checked_mem_write_pte8_cond_S_upt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (w0 w data : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0)
    (hleaf : uepLeafB w = true) (had : uepAD w data)
    (root : BitVec 44) (hs : satpTable c.satp = some root) (a2 a1 : PAddr) (v2 v1 : BitVec 64) (dq2 dq1 : DFrac)
    (hpath : uptPathOk root a2 v2 a1 v1 pa)
    (Φ : Result Bool (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ownCtx cpu curCtx ∗ resvFrag cpu (some (snapOf pa 8 w0)) false ∗
    bytesPointsTo pa 8 dqUpt w ∗ bytesPointsTo a2 8 dq2 v2 ∗ bytesPointsTo a1 8 dq1 v1 ∗
    uptOpenWit root Privilege.Supervisor ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗ resvFrag cpu none false -∗
        bytesPointsTo pa 8 dqUpt data -∗ bytesPointsTo a2 8 dq2 v2 -∗ bytesPointsTo a1 8 dq1 v1 -∗ Φ (.Ok true))
    ⊢ swp cpu (checked_mem_write (physaddr.Physaddr pa) 8 data (MemoryAccessType.Store mem_payload.PageTableEntry)
        page_based_mem_type.PBMT_PMA Privilege.Supervisor () false false true) Φ := by
  iintro ⟨HmConf, Hctx, Hfrag, Hb, H2, H1, #Hw, HΦ⟩
  unfold checked_mem_write
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  iapply (swp_sail_mem_write_excl_upt cpu _ curCtx (some (snapOf pa 8 w0)) w data rfl rfl hleaf had root c.satp hs
    Privilege.Supervisor dq dq dq2 dq1 a2 a1 v2 v1 hpath)
  ihave Hfrag := resvFragAny_of cpu (some (snapOf pa 8 w0)) false $$ Hfrag
  iframe Hctx Hfrag Hb H2 H1 Hsatp Hcur_privilege Hw
  inext
  iintro Hctx Hfrag Hb H2 H1 Hsatp Hcur_privilege
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf Hctx Hfrag Hb H2 H1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- `write_pte_conditional` on a leaf of the open epoch's table. -/
theorem swp_write_pte_conditional_upt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (w0 w data : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0)
    (hleaf : uepLeafB w = true) (had : uepAD w data)
    (root : BitVec 44) (hs : satpTable c.satp = some root) (a2 a1 : PAddr) (v2 v1 : BitVec 64) (dq2 dq1 : DFrac)
    (hpath : uptPathOk root a2 v2 a1 v1 pa)
    (Φ : Result Bool (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ownCtx cpu curCtx ∗ resvFrag cpu (some (snapOf pa 8 w0)) false ∗
    bytesPointsTo pa 8 dqUpt w ∗ bytesPointsTo a2 8 dq2 v2 ∗ bytesPointsTo a1 8 dq1 v1 ∗
    uptOpenWit root Privilege.Supervisor ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗ resvFrag cpu none false -∗
        bytesPointsTo pa 8 dqUpt data -∗ bytesPointsTo a2 8 dq2 v2 -∗ bytesPointsTo a1 8 dq1 v1 -∗ Φ (.Ok true))
    ⊢ swp cpu (write_pte_conditional (physaddr.Physaddr pa) 8 data) Φ := by
  iintro ⟨HmConf, Hctx, Hfrag, Hb, H2, H1, #Hw, HΦ⟩
  unfold write_pte_conditional mem_write_value_priv mem_write_value_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_write_pte8_cond_S_upt cpu dq c sie hok pa w0 w data hram hal hleaf had root hs a2 a1 v2 v1
    dq2 dq1 hpath)
  iframe HmConf Hctx Hfrag Hb H2 H1 Hw
  inext
  iintro HmConf Hctx Hfrag Hb H2 H1
  swp_run 20
  iapply HΦ $$ HmConf Hctx Hfrag Hb H2 H1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **`update_and_write_pte` on a leaf of the open epoch's table** (the twin
of `swp_update_and_write_pte_own`, the leaf at three quarters, the write
through the arm). -/
theorem swp_update_and_write_pte_upt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (addr : BitVec 64) (haddr : pteAddrOk addr) (ppn : BitVec 44) (perm : KPerm) (ac dc a d : BitVec 1)
    (hperm : perm.allows acc = true) (u : Unit)
    (root : BitVec 44) (hs : satpTable c.satp = some root) (a2 a1 : PAddr) (v2 v1 : BitVec 64) (dq2 dq1 : DFrac)
    (hpath : uptPathOk root a2 v2 a1 v1 addr)
    (Φ : Result (Option (BitVec 64) × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ctxTok cpu curCtx ∗
    bytesPointsTo addr 8 dqUpt (kLeaf ppn perm a d) ∗ bytesPointsTo a2 8 dq2 v2 ∗ bytesPointsTo a1 8 dq1 v1 ∗
    uptOpenWit root Privilege.Supervisor ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗
        bytesPointsTo a2 8 dq2 v2 -∗ bytesPointsTo a1 8 dq1 v1 -∗
        ∀ (p : Option (BitVec 64)) (a' d' : BitVec 1), ⌜pteUpd ppn perm a d p a' d'⌝ -∗
        bytesPointsTo addr 8 dqUpt (kLeaf ppn perm a' d') -∗ Φ (.Ok (p, u)))
    ⊢ swp cpu (update_and_write_pte39 vpn (physaddr.Physaddr addr) (kLeaf ppn perm ac dc) 0 acc
        Privilege.Supervisor mxr do_sum u) Φ := by
  iintro ⟨HmConf, Htok, Hb, H2, H1, #Hw, HΦ⟩
  have hpl : accPlain acc := kernelAccess_plain acc hacc
  unfold update_and_write_pte39 update_and_write_pte
  reduce_closed_widths
  cases hupd : update_PTE_Bits (kLeaf ppn perm ac dc) acc with
  | none =>
    swp_run 40
    iapply HΦ $$ HmConf Htok H2 H1 %none %a %d [] Hb
    ipureintro; exact Or.inl ⟨rfl, rfl, rfl⟩
  | some p =>
    icases ctxTok_cases cpu curCtx $$ Htok with ⟨Hctx, %r0, Hfrag⟩
    conf_cases HmConf
    swp_run 60
    conf_intro HmConf
    iapply swp_bind
    iapply (swp_read_pte_exclusive_ctx cpu dq c sie hok addr haddr.1 haddr.2 r0 dqUpt (kLeaf ppn perm a d))
    iframe HmConf Hctx Hfrag Hb
    inext
    iintro HmConf Hctx Hfrag Hb
    swp_run 40
    rw [check_leaf_pte39_eq]
    iapply swp_bind
    iapply (swp_check_leaf_pte_kLeaf cpu dq c vpn acc hacc mxr do_sum ppn perm a d hperm addr u)
    iframe HmConf
    inext
    iintro HmConf
    cases hupd2 : update_PTE_Bits (kLeaf ppn perm a d) acc with
    | none =>
      swp_run 40
      iapply HΦ $$ HmConf [Hctx Hfrag] H2 H1 %(some (kLeaf ppn perm a d)) %a %d [] Hb
      · iapply ctxTok_introB cpu curCtx _ false; iframe Hctx Hfrag
      · ipureintro; exact Or.inr rfl
    | some p2 =>
      have hp2 : ∃ a2 d2, p2 = kLeaf ppn perm a2 d2 := by
        rw [kLeaf, update_PTE_Bits_pteSetAD _ _ _ _ hpl] at hupd2
        split at hupd2
        · exact ⟨_, _, (Option.some.inj hupd2).symm⟩
        · exact absurd hupd2 (by simp)
      obtain ⟨a2', d2', rfl⟩ := hp2
      swp_run 40
      iapply swp_bind
      iapply (swp_write_pte_conditional_upt cpu dq c sie hok addr (kLeaf ppn perm a d) (kLeaf ppn perm a d)
        (kLeaf ppn perm a2' d2') haddr.1 haddr.2 (uepLeafB_kLeaf ppn perm a d) (uepAD_kLeaf ppn perm a d a2' d2')
        root hs a2 a1 v2 v1 dq2 dq1 hpath)
      iframe HmConf Hctx Hfrag Hb H2 H1 Hw
      inext
      iintro HmConf Hctx Hfrag Hb H2 H1
      swp_run 40
      iapply HΦ $$ HmConf [Hctx Hfrag] H2 H1 %(some (kLeaf ppn perm a2' d2')) %a2' %d2' [] Hb
      · iapply ctxTok_introB cpu curCtx none false; iframe Hctx Hfrag
      · ipureintro; exact Or.inr rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **A TLB hit on an entry caching a leaf of the open epoch's table.** -/
theorem swp_translate_TLB_hit_upt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (tlb : Tlb) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (i : Nat) (ent : TLB_Entry) (hi : i = tlbHash vpn) (hget : tlb[tlbHash vpn]'(tlbHash_lt vpn) = some ent)
    (addr : BitVec 64) (haddr : pteAddrOk addr) (ppn : BitVec 44) (perm : KPerm) (ac dc a d : BitVec 1)
    (hent : ent = tlbEntryOf 0#16 vpn ppn (kLeaf ppn perm ac dc) addr)
    (hperm : perm.allows acc = true) (u : Unit)
    (root : BitVec 44) (hs : satpTable c.satp = some root) (a2 a1 : PAddr) (v2 v1 : BitVec 64) (dq2 dq1 : DFrac)
    (hpath : uptPathOk root a2 v2 a1 v1 addr)
    (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ctxTok cpu curCtx ∗
    bytesPointsTo addr 8 dqUpt (kLeaf ppn perm a d) ∗ bytesPointsTo a2 8 dq2 v2 ∗ bytesPointsTo a1 8 dq1 v1 ∗
    uptOpenWit root Privilege.Supervisor ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗
        bytesPointsTo a2 8 dq2 v2 -∗ bytesPointsTo a1 8 dq1 v1 -∗
        ∀ (a' d' : BitVec 1), bytesPointsTo addr 8 dqUpt (kLeaf ppn perm a' d') -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbAfter tlb tlb' vpn ppn perm a' d' addr⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_hit39 0#16 vpn acc Privilege.Supervisor mxr do_sum u i ent) Φ := by
  iintro ⟨HmConf, Htok, Hb, H2, H1, #Hw, Htlb, HΦ⟩
  subst hent hi
  unfold translate_TLB_hit39 translate_TLB_hit
  reduce_closed_widths
  swp_run 20
  rw [tlb_get_pte_tlbEntryOf]
  simp only [ext_of_kLeaf]
  iapply swp_bind
  iapply (swp_check_PTE_permission_kLeaf cpu acc hacc mxr do_sum ppn perm ac dc hperm)
  swp_run 20
  rw [pteAddr_tlbEntryOf, tlb_get_level_tlbEntryOf, update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_upt cpu dq c sie hok hadue vpn acc hacc mxr do_sum addr haddr ppn perm
    ac dc a d hperm u root hs a2 a1 v2 v1 dq2 dq1 hpath)
  iframe HmConf Htok Hb H2 H1 Hw
  iintro HmConf Htok H2 H1 %p %a' %d' %hp Hb
  rw [tlb_get_ppn_tlbEntryOf, tlb_get_pbmt_kLeaf]
  cases p with
  | none =>
    swp_run 20
    iapply HΦ $$ HmConf Htok H2 H1 %a' %d' Hb %tlb Htlb
    ipureintro; exact Or.inl rfl
  | some p =>
    have hp' : p = kLeaf ppn perm a' d' := by
      rcases hp with ⟨h, _⟩ | h
      · cases h
      · exact Option.some.inj h
    subst hp'
    swp_run 20
    iapply HΦ $$ HmConf Htok H2 H1 %a' %d' Hb %_ Htlb
    ipureintro
    right
    rw [tlb_set_pte_tlbEntryOf]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **A TLB miss walking the open epoch's table.** -/
theorem swp_translate_TLB_miss_upt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (tlb : Tlb) (root b1 b0 : BitVec 44) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1) (hperm : perm.allows acc = true) (u : Unit)
    (dq2 dq1 : DFrac) (hs : satpTable c.satp = some root)
    (h2 : pteAddrOk (pteAddr root (vpnIdx vpn 2))) (h1 : pteAddrOk (pteAddr b1 (vpnIdx vpn 1)))
    (h0 : pteAddrOk (pteAddr b0 (vpnIdx vpn 0)))
    (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ctxTok cpu curCtx ∗
    bytesPointsTo (pteAddr root (vpnIdx vpn 2)) 8 dq2 (kPtr b1) ∗
    bytesPointsTo (pteAddr b1 (vpnIdx vpn 1)) 8 dq1 (kPtr b0) ∗
    bytesPointsTo (pteAddr b0 (vpnIdx vpn 0)) 8 dqUpt (kLeaf ppn perm a d) ∗
    uptOpenWit root Privilege.Supervisor ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗
        bytesPointsTo (pteAddr root (vpnIdx vpn 2)) 8 dq2 (kPtr b1) -∗
        bytesPointsTo (pteAddr b1 (vpnIdx vpn 1)) 8 dq1 (kPtr b0) -∗
        ∀ (a' d' : BitVec 1), bytesPointsTo (pteAddr b0 (vpnIdx vpn 0)) 8 dqUpt (kLeaf ppn perm a' d') -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗
        ⌜tlbAfter tlb tlb' vpn ppn perm a' d' (pteAddr b0 (vpnIdx vpn 0))⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_miss39 0#16 root vpn acc Privilege.Supervisor mxr do_sum u) Φ := by
  iintro ⟨HmConf, Htok, H2, H1, H0, #Hw, Htlb, HΦ⟩
  unfold translate_TLB_miss39 translate_TLB_miss
  reduce_closed_widths
  swp_run 20
  rw [pt_walk39_eq]
  iapply swp_bind
  iapply (swp_pt_walk_own cpu dq c sie hok root b1 b0 vpn acc hacc mxr do_sum ppn perm a d hperm u
    dq2 dq1 dqUpt h2 h1 h0)
  iframe HmConf Htok H2 H1 H0
  inext
  iintro HmConf Htok H2 H1 H0
  unfold kptWalkOut
  swp_run 20
  rw [update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_upt cpu dq c sie hok hadue vpn acc hacc mxr do_sum _ h0 ppn perm
    a d a d hperm u root hs _ _ _ _ dq2 dq1 (uptPath_of root b1 b0 vpn))
  iframe HmConf Htok H0 H2 H1 Hw
  iintro HmConf Htok H2 H1 %p %a' %d' %hp H0
  cases p with
  | none =>
    obtain ⟨-, rfl, rfl⟩ : (none : Option (BitVec 64)) = none ∧ a' = a ∧ d' = d := by
      rcases hp with h | h
      · exact h
      · cases h
    swp_run 20
    rw [add_to_TLB39_eq]
    iapply swp_bind
    iapply (swp_add_to_TLB_kpt cpu tlb vpn ppn (kLeaf ppn perm a' d') _)
    iframe Htlb
    inext
    iintro Htlb
    swp_run 20
    iapply HΦ $$ HmConf Htok H2 H1 %a' %d' H0 %_ Htlb
    ipureintro; exact Or.inr rfl
  | some p =>
    have hp' : p = kLeaf ppn perm a' d' := by
      rcases hp with ⟨h, _⟩ | h
      · cases h
      · exact Option.some.inj h
    subst hp'
    swp_run 20
    rw [add_to_TLB39_eq]
    iapply swp_bind
    iapply (swp_add_to_TLB_kpt cpu tlb vpn ppn (kLeaf ppn perm a' d') _)
    iframe Htlb
    inext
    iintro Htlb
    swp_run 20
    iapply HΦ $$ HmConf Htok H2 H1 %a' %d' H0 %_ Htlb
    ipureintro; exact Or.inr rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`translateAddr` over the open epoch's table** (the twin of
`swp_translateAddr_own`). -/
theorem swp_translateAddr_upt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool) (root : BitVec 44)
    (hok : SConfKpt (GF := GF) c root sie) (b1 b0 : BitVec 44) (tlb : Tlb) (va : BitVec 64)
    (hcanon : BitVec.signExtend 64 (BitVec.extractLsb' 0 39 va) = va)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc)
    (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1) (hperm : perm.allows acc = true) (dq2 dq1 : DFrac)
    (h2 : pteAddrOk (pteAddr root (vpnIdx (vpnOf va) 2))) (h1 : pteAddrOk (pteAddr b1 (vpnIdx (vpnOf va) 1)))
    (h0 : pteAddrOk (pteAddr b0 (vpnIdx (vpnOf va) 0)))
    (htlb : tlbVpnOk tlb (vpnOf va) ppn perm (pteAddr b0 (vpnIdx (vpnOf va) 0)))
    (Φ : Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ctxTok cpu curCtx ∗
    bytesPointsTo (pteAddr root (vpnIdx (vpnOf va) 2)) 8 dq2 (kPtr b1) ∗
    bytesPointsTo (pteAddr b1 (vpnIdx (vpnOf va) 1)) 8 dq1 (kPtr b0) ∗
    bytesPointsTo (pteAddr b0 (vpnIdx (vpnOf va) 0)) 8 dqUpt (kLeaf ppn perm a d) ∗
    uptOpenWit root Privilege.Supervisor ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗
        bytesPointsTo (pteAddr root (vpnIdx (vpnOf va) 2)) 8 dq2 (kPtr b1) -∗
        bytesPointsTo (pteAddr b1 (vpnIdx (vpnOf va) 1)) 8 dq1 (kPtr b0) -∗
        ∀ (a' d' : BitVec 1),
        bytesPointsTo (pteAddr b0 (vpnIdx (vpnOf va) 0)) 8 dqUpt (kLeaf ppn perm a' d') -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗
        ⌜tlbAfter tlb tlb' (vpnOf va) ppn perm a' d' (pteAddr b0 (vpnIdx (vpnOf va) 0))⌝ -∗
        Φ (.Ok (physaddr.Physaddr (BitVec.setWidth 64 (ppn ++ BitVec.extractLsb' 0 12 va)),
          page_based_mem_type.PBMT_PMA, ())))
    ⊢ swp cpu (translateAddr (virtaddr.Virtaddr va) acc) Φ := by
  iintro ⟨HmConf, Htok, H2, H1, H0, #Hw, Htlb, HΦ⟩
  have hs : satpTable c.satp = some root := by
    unfold satpTable; rw [if_pos hok.2.1, hok.2.2.2.1]
  conf_cases HmConf
  have hok0 := hok
  obtain ⟨⟨hpmp, hms, hpmm, hlpe⟩, hmode, hasid, hroot, hadue⟩ := hok
  obtain ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩ := hms
  have hok' : SConfPhys (GF := GF) c sie :=
    ⟨hpmp, ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩, hpmm, hlpe⟩
  unfold translateAddr
  rw [is_shadow_stack_access_kernel acc hacc]
  swp_run 40
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_translationMode_kpt cpu dq c sie root hok0)
  iframe HmConf
  inext
  iintro HmConf
  conf_cases HmConf
  swp_run 120
  reduce_closed_widths
  rw [extract_vpnOf, satp_to_asid_of c.satp hasid, satp_to_ppn_of c.satp root hroot]
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_lookup_TLB_gen cpu tlb (vpnOf va))
  iframe Htlb
  inext
  iintro Htlb %r %hres
  cases r with
  | none =>
    swp_run 10
    rw [translate_TLB_miss39_eq]
    iapply swp_bind
    iapply (swp_translate_TLB_miss_upt cpu dq c sie hok' hadue tlb root b1 b0 (vpnOf va) acc hacc _ _
      ppn perm a d hperm _ dq2 dq1 hs h2 h1 h0)
    iframe HmConf Htok H2 H1 H0 Hw Htlb
    iintro HmConf Htok H2 H1 %a' %d' H0 %tlb' Htlb %htlb'
    swp_run 20
    iapply HΦ $$ HmConf Htok H2 H1 %a' %d' H0 %tlb' Htlb
    ipureintro; exact htlb'
  | some ie =>
    obtain ⟨i, ent⟩ := ie
    obtain ⟨hi, hget, hm⟩ := hres
    obtain ⟨ac, dc, hent⟩ := htlb ent hget hm
    swp_run 10
    rw [translate_TLB_hit39_eq]
    iapply swp_bind
    iapply (swp_translate_TLB_hit_upt cpu dq c sie hok' hadue tlb (vpnOf va) acc hacc _ _ i ent hi hget
      _ h0 ppn perm ac dc a d hent hperm _ root hs _ _ _ _ dq2 dq1 (uptPath_of root b1 b0 (vpnOf va)))
    iframe HmConf Htok H0 H2 H1 Hw Htlb
    iintro HmConf Htok H2 H1 %a' %d' H0 %tlb' Htlb %htlb'
    swp_run 20
    iapply HΦ $$ HmConf Htok H2 H1 %a' %d' H0 %tlb' Htlb
    ipureintro; exact htlb'

end MachCSL
