(* ====================================================================== *)
(* BootHart.v -- ONE HART'S BOOT VOCABULARY: the geometry, the reset          *)
(* residue, the per-hart bundle.                                            *)
(*                                                                        *)
(* The part of the boot chain that is stated over ONE hart's registers and  *)
(* the image alone, and that BOTH the chain (BootChain.v) and the shared     *)
(* allocation (BootShared.v) consume:                                       *)
(*                                                                        *)
(*   §1 THE BOOT GEOMETRY -- the concrete addresses the chain runs on:      *)
(*      [_entry]'s GOT slot and the &stack0 word in it, and this hart's     *)
(*      [sp0 = &stack0 + 4096*(mhartid+1)] with every bound the M-mode      *)
(*      contract and the bridge ask about it.  All of it is CLOSED          *)
(*      arithmetic once the hart index is: [v_stack0] is the image's own    *)
(*      word and [mhartid] is pinned to the hart index by                  *)
(*      [RiscvLang.reset_regs], so each fact is eight [vm_compute]s and     *)
(*      needs no [lia] at all (which is what keeps it out of the           *)
(*      [bitvector.tactics] zify hook's way).                              *)
(*   §2 THE M-MODE PRECONDITION -- [boot_entry_pre]: one hart's reset       *)
(*      register cells become [SpecEntry.wp_entry_boot]'s inputs.           *)
(*   §3 THE PER-HART BUNDLE -- [boot_hart_res], what one hart's chain runs  *)
(*      on, minted once for all eight harts by BootShared.                  *)
(*                                                                        *)
(* WHY A SEPARATE FILE.  BootChain.v composes the three PROVEN contracts,   *)
(* so it imports LinkMain -- the last link of the whole kernel -- and       *)
(* cannot start until every whole-function proof has landed.  Nothing here  *)
(* needs a Link file, and BootShared (13 s, eight harts' allocation) needs   *)
(* only this: with its own file it compiles hundreds of seconds earlier,    *)
(* beside the proofs, instead of after them on the build's serial tail.     *)
(* Keep it that way: no [Link*] import belongs in this file.                *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto MinstretInv.
Require Import RegFile HartTp InstrBytes WpGpr.
Require Import KMap.
Require Import StackOwn.
Require Import KernelText KernelDataInv.
Require Import MbootVocab.
Require Import MstatusFacts.
Require Import KptPt.
Require Import IntrDefs.
Require Import WireInv.   (* [wire_inv] *)
Require Import ProcGeom CpuOwn SchedCtx.
Require Import SpecMain.
Require Import BootConfig BootBridge PowerBoot.
Require Import SpecMainSecondary.
Require Import StartedInv DevModel.
Require Import WpUart DiskPtsto.
Require Import KallocInv FdSlots.
Require Import LockSet.
Require Import FileInvDefs.
Require Import KptGhost VirtioProto VirtioModel SpecFreerange KvmSpec.
Require Import TimerCap.
From Kernel Require KernelData.
From Kernel Require KernelSyms.
Require Import KernelConsts.
Require Import ProcAvail.
(* [fs_boot_supply] / [iref_slots_auth] -- the file system's boot-era mint
   and the iref-slot authority, both threaded from [BootShared] into
   [SpecMain]'s boot arm (fs-cfg-boot.md stage (e)). *)
Require Import FsCfgBoot IrefSlots LogDefs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Require Import TsoCtx.

(* ====================================================================== *)
(* §1  THE BOOT GEOMETRY.                                                  *)
(* ====================================================================== *)

(* [_entry]'s `la sp, stack0` is an auipc/ld pair, so the value it loads is a
   WORD OF THE IMAGE, at the pc-relative slot [entry_got]; and the word there
   is &stack0.  [MbootVocab.mb_ld_ea] is the address the WP computes; these
   two lemmas are the only place the tree says what it IS. *)
(* COMPUTED from that auipc/ld pair by tools/gen_consts.py.  It moves
   whenever the data segment does, and a stale literal failed inside
   [entry_ld_ea_addr]'s [vm_compute] with two addresses and no hint as to
   which one was wrong. *)
Definition entry_got : Z := KernelConsts.entry_got.

Definition v_stack0 : mword 64 := mword_of_int KernelSyms.stack0.

Lemma entry_ld_ea_addr : mb_ld_ea = pa_of_z entry_got.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* the eight image bytes at the slot ARE &stack0's, little-endian: exactly
   [BootCarve.kernel_data_phys_word]'s one obligation. *)
Lemma entry_got_bytes (j : nat) :
  (j < 8)%nat ->
  KernelData.kernel_data !! (entry_got + Z.of_nat j) = Some (nth_byte v_stack0 j).
Proof.
  intro Hj.
  (* [vm_compute; reflexivity] does NOT close these: the two sides are
     [Some <the same bv literal>] with DIFFERENT [BvWf] proofs, and print
     identically (durable-notes' [bv_eq] trap, one [option] layer up). *)
  destruct j as [|[|[|[|[|[|[|[|j']]]]]]]]; [.. | cbn in Hj; lia];
    vm_compute; apply (f_equal Some), bv_eq; reflexivity.
Qed.

(* THE PER-HART STACK POINTER.  [_entry] computes sp = &stack0 + 4096*(hart+1)
   ([sp_of] below), and [RiscvLang.reset_regs] pins mhartid to the hart index,
   so for a concrete hart every fact about it is closed arithmetic. *)
Definition sp_of (n : nat) : Z := KernelSyms.stack0 + 4096 * (Z.of_nat n + 1).

(* the depth of the carve below sp0: the hart's own 4096-byte [stack0] slice
   is exactly [uint sp0 - 8*512, uint sp0), which is what makes the ONE range
   serve both [wp_entry_boot]'s [4 <= n] and the bridge's
   [boot_stack_slots K_main = 180 <= n]. *)
Notation boot_stack_depth := (512%nat) (only parsing).
Lemma boot_stack_depth_entry : (4 <= boot_stack_depth)%nat.
Proof. lia. Qed.

Lemma boot_stack_depth_bridge : (boot_stack_slots K_main <= boot_stack_depth)%nat.
Proof. rewrite boot_stack_slots_main. lia. Qed.

(* [_entry]'s computed sp, at this image's [stack0] and a concrete hart id.
   This is what [SpecEntry.wp_entry_boot]'s defining premise for [sp0] wants,
   and supplying it is what puts every occurrence of sp0 in the contract at
   the concrete address below. *)
Lemma sp0_val (n : nat) :
  (n < NCPU)%nat ->
  mb_entry_sp v_stack0 (boot_w64 (Z.of_nat n))
  = (mword_of_int (sp_of n) : mword 64).
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp0_uint (n : nat) :
  (n < NCPU)%nat -> uint (mword_of_int (sp_of n) : mword 64) = sp_of n.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; reflexivity.
Qed.

(* timerinit's two frame slots sit inside the TOR region start() opened
   ([0, 0xfffffffffffffc)) -- [wp_entry_boot]'s two stack-geometry premises. *)
Lemma ti_ea_ra_bound (n : nat) :
  (n < NCPU)%nat ->
  uint (mb_ti_ra (mword_of_int (sp_of n) : mword 64)) + 8
  <= 0xfffffffffffffc.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

Lemma ti_ea_s0_bound (n : nat) :
  (n < NCPU)%nat ->
  uint (mb_ti_s0 (mword_of_int (sp_of n) : mword 64)) + 8
  <= 0xfffffffffffffc.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

(* the bridge's two stack-location bounds, at [K := K_main] *)
Lemma sp_of_lo (n : nat) :
  (n < NCPU)%nat ->
  text_end + 8 * Z.of_nat (boot_stack_slots K_main) <= sp_of n.
Proof.
  unfold NCPU. intro Hn. rewrite boot_stack_slots_main.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

Lemma sp_of_hi (n : nat) : (n < NCPU)%nat -> sp_of n <= ram_base + ram_size.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

(* THE tp/cid CONVENTION, at any hart: start()'s `mv tp, a1` writes mhartid,
   and [HartTp.cid_word_of] IS [mword_of_int (Z.of_nat (fin_to_nat c))]. *)
Lemma st_tpv_of_nat (n : nat) :
  (n < NCPU)%nat ->
  mb_tpv (boot_w64 (Z.of_nat n)) = (mword_of_int (Z.of_nat n) : mword 64).
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* THE HART INDEX AS A WORD, at a SECONDARY hart: nonzero (which is what picks
   main's spin-loop arm) and inside the PLIC's per-hart bank count. *)
Lemma cid_word_of_nz (n : nat) :
  (n < NCPU)%nat -> (n <> 0)%nat ->
  (mword_of_int (Z.of_nat n) : mword 64) <> zero_reg.
Proof.
  unfold NCPU. intros Hn Hnz.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [congruence | .. | lia];
    intro He; apply (f_equal bv_unsigned) in He; vm_compute in He;
    discriminate He.
Qed.

Lemma cid_word_of_lt_dev (n : nat) :
  (n < NCPU)%nat ->
  (bv_unsigned (mword_of_int (Z.of_nat n) : mword 64) < Z.of_nat dev_ncpu)%Z.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; reflexivity.
Qed.

(* the secondary arm's stack budget is inside the one the bridge hands out.
   The bridge's index is [kv_frame_slots + K_main] -- it names the trap
   reserve, because that is the depth it physically carves ([BootBridge.v]) --
   so BOTH arms' budget premises are stated against that sum here rather than
   against [K_main] alone.  Nothing is retuned: [kv_frame_slots] only ever
   makes the available budget LARGER. *)
Lemma K_main_secondary_le : (K_main_secondary <= kv_frame_slots + K_main)%nat.
Proof. lia. Qed.

(* the boot arm's, likewise: it used to be [le_n K_main] at the call site. *)
Lemma K_main_boot_le : (K_main <= kv_frame_slots + K_main)%nat.
Proof. lia. Qed.

(* ...and at the BOOT hart: the id word IS [zero_reg], which is what makes
   main's [beqz a0] take the boot path. *)
Lemma cid_word_of_zero (n : nat) :
  (n = 0)%nat -> (mword_of_int (Z.of_nat n) : mword 64) = zero_reg.
Proof. intros ->. apply bv_eq. vm_compute. reflexivity. Qed.

(* the boot menvcfg has the Zicfilp landing-pad enable clear *)
Lemma menvcfg_boot_lpe : _get_MEnvcfg_LPE (boot_w64 0) = ('b"0").
Proof. vm_compute. reflexivity. Qed.

(* ====================================================================== *)
(* §2  THE M-MODE PRECONDITION, out of one hart's reset residue.           *)
(*                                                                        *)
(* [boot_entry_pre] is the whole register side of the chain: this hart's    *)
(* [boot_D] cells (at the values [reset_regs] pins them to) plus the        *)
(* persisted static claims plus the generation certificate become EXACTLY   *)
(* what [SpecEntry.wp_entry_boot] asks for -- [mmode_config] included,      *)
(* which means freezing this hart's [hw_config] cells on the way, and       *)
(* [pc_is], which means forming its [minstret_res] / [clock_res] out of the *)
(* counter and clock cells and taking in its reservation mirror             *)
(* -- together with the five S-mode registers                               *)
(* the M-mode contract never touches and [BootBridge.boot_bridge] wants,    *)
(* and the two PLIC wire pins the device client asks for.                   *)
(*                                                                        *)
(* Everything below the register layer (the image, the stack slice, this    *)
(* hart's cpus[] cells) is the CARVE's, and is not this lemma's business.   *)
(* ====================================================================== *)

Require Import UserFd.   (* [ufdG] -- must precede any `{!ufdG Σ} binder *)
Section BootEntryPre.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma boot_entry_pre (E : coPset) (rs : regstate) :
    reset_regs cpu_id rs ->
    kmap_static_claims -∗
    gen_cert -∗
    (* this hart's RESERVATION MIRROR, at [None] -- adequacy mints one per
       hart and the boot chain is what threads it into [pc_is]
       (claude-notes/projects/main-cycle-port.md §3a).  A hart that has
       executed nothing holds no reservation. *)
    resv_frag cpu_id None -∗
    boot_reg_res rs
    ={E}=∗
      (* --- [wp_entry_boot]'s own inputs --- *)
      mmode_config (DfracOwn 1) ∗
      (* pmpcfg comes out at WHATEVER the reset left, not at a pinned value:
         [reset_regs]' clause is [pmp_all_off] of it, which is what
         [wp_entry_boot] takes (at a quantified [pmpcfg0]). *)
      pmpcfg_n ↦ᵣ register_lookup pmpcfg_n rs ∗
      pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs ∗
      pc_is (mword_of_int KernelSyms._entry) ∗
      gpr_file (boot_regfile rs) ∗
      mhartid ↦ᵣ boot_w64 (Z.of_nat (fin_to_nat cpu_id)) ∗
      mepc ↦ᵣ register_lookup mepc rs ∗
      satp ↦ᵣ register_lookup satp rs ∗
      medeleg ↦ᵣ register_lookup medeleg rs ∗
      mideleg ↦ᵣ register_lookup mideleg rs ∗
      mie ↦ᵣ register_lookup mie rs ∗
      menvcfg ↦ᵣ boot_w64 0 ∗
      mcounteren ↦ᵣ register_lookup mcounteren rs ∗
      stimecmp ↦ᵣ register_lookup stimecmp rs ∗
      (* --- the S-mode cells the M-mode boot never touches: [boot_bridge]'s
             per-hart register inputs --- *)
      tlb ↦ᵣ register_lookup tlb rs ∗
      (∃ v : mword 64, stvec ↦ᵣ v) ∗
      (∃ v : mword 64, sepc ↦ᵣ v) ∗
      (∃ v : mword 64, scause ↦ᵣ v) ∗
      (∃ v : mword 64, stval ↦ᵣ v) ∗
      (* --- the three [IntrDefs.hart_csrs] cells: no boot code writes them,
             they go straight into this hart's [cpu_own] --- *)
      (∃ v : mword 64, sscratch ↦ᵣ v) ∗
      mstateen0 ↦ᵣ (mword_of_int 0 : mword 64) ∗
      sstateen0 ↦ᵣ (mword_of_int 0 : mword 32) ∗
      (* --- the PLIC wire pins ([WireInv.wire_inv]'s, allocated across all
             harts by the client) --- *)
      sig_seip ↦ᵣ register_lookup sig_seip rs ∗
      sig_meip ↦ᵣ register_lookup sig_meip rs.
  Proof.
    intros (Hpc0 & Hnpc0 & Hpv0 & Hhs0 & Hmh0 & Hms0 & Hmisa0 & Hsec0 & Hmenv0 &
            Hhtif0 & Help0 & Hpma0 & _ & _ & _ & Hsenv0 & Hmse0 & Hsse0).
    iIntros "#Hcl #Hcert Hresv Hregs".
    iDestruct (boot_reg_split rs with "Hregs") as
      "(HPC & HnPC & Hpriv & Hhs & Hmh & Hms & Hmisa & Hsec & Hmenv & Hhtif & Help &
        Hpma & Hpmpc & Hpmpa & Hmepc & Hsatp & Hmede & Hmdl & Hmie & Hmcen & Hstc &
        Hmst & Hminc & Hmcy & Hmt & Hmip & Hseip & Hmeip & Htlb & Hstvec &
        Hsepc & Hscause & Hstval & Hsenv & Hssc & Hmse & Hsse & Hscen & Hhpm &
        Hmci & Hmicfg & Hgprs)".
    (* the pinned cells, at their pinned values *)
    iEval (rewrite Hpc0 boot_pc_entry) in "HPC".
    iEval (rewrite Hnpc0 boot_pc_entry) in "HnPC".
    iEval (rewrite Hpv0) in "Hpriv".
    iEval (rewrite Hhs0) in "Hhs".
    iEval (rewrite Hmh0) in "Hmh".
    iEval (rewrite Hms0) in "Hms".
    iEval (rewrite Hmisa0) in "Hmisa".
    iEval (rewrite Hsec0) in "Hsec".
    iEval (rewrite Hmenv0) in "Hmenv".
    iEval (rewrite Hhtif0) in "Hhtif".
    iEval (rewrite Help0) in "Help".
    iEval (rewrite Hpma0) in "Hpma".
    iEval (rewrite Hsenv0) in "Hsenv".
    (* the two counter-inhibit cells, FROZEN: nothing in the kernel or the
       tree writes either, and [MinstretInv.minstret_res] holds them
       persistently.  [minstret_inv] itself is [emp] now (see MinstretInv.v's
       header): the counter facts are OWNED resources riding in [pc_is], so
       there is no invariant left to allocate here. *)
    iMod (reg_pointsto_persist with "Hmci") as "#Hmci'".
    iMod (reg_pointsto_persist with "Hmicfg") as "#Hmicfg'".
    iMod (hw_config_intro _ _ with "Hmisa Hsec Hpma Hhtif Help Hsenv Hscen Hhpm
                                    Hcl Hcert") as "#Hhw".
    iModIntro.
    iSplitL "Hhs Hpriv Hms".
    { iApply (mmode_config_intro (DfracOwn 1) with "Hhw Hhs Hpriv Hms"). }
    iFrame "Hpmpc Hpmpa".
    (* [pc_is] is the per-cycle bundle: PC/nextPC, the counter and clock
       cells, and this hart's reservation mirror. *)
    iSplitL "HPC HnPC Hmst Hminc Hmcy Hmt Hmip Hresv".
    { rewrite /pc_is. iFrame "HPC HnPC".
      iSplitL "Hmst Hminc".
      { iApply (minstret_res_intro with "Hmst Hminc Hmci' Hmicfg'"). }
      iSplitL "Hmcy Hmt Hmip".
      { iApply (clock_res_intro with "Hmcy Hmt Hmip"). }
      iApply (resv_any_intro with "Hresv"). }
    iSplitL "Hgprs". { iApply (boot_gpr_file rs with "Hgprs"). }
    iFrame "Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen Hstc Htlb".
    iSplitL "Hstvec". { iExists (register_lookup stvec rs). iExact "Hstvec". }
    iSplitL "Hsepc". { iExists (register_lookup sepc rs). iExact "Hsepc". }
    iSplitL "Hscause". { iExists (register_lookup scause rs). iExact "Hscause". }
    iSplitL "Hstval". { iExists (register_lookup stval rs). iExact "Hstval". }
    iSplitL "Hssc". { iExists (register_lookup sscratch rs). iExact "Hssc". }
    iEval (rewrite Hmse0) in "Hmse".
    iEval (rewrite Hsse0) in "Hsse".
    iFrame "Hmse Hsse Hseip Hmeip".
  Qed.

End BootEntryPre.

(* ====================================================================== *)
(* §3  THE PER-HART BUNDLE.                                                *)
(* ====================================================================== *)

Section BootHartRes.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ONE BUNDLE for what one hart's boot chain runs on, so §3 and §4 state it
     once: [boot_entry_pre]'s output MINUS the two PLIC wire pins, plus the
     image and this hart's stack slice (the CARVE's outputs), plus the bridge's
     adequacy-minted and .bss inputs.  The pins are excluded because
     [WireInv.wire_inv_alloc] wants ALL EIGHT harts' at once and must run before
     any hart's WP -- see the section header. *)
  Definition boot_hart_res (rs : regstate) (iv : mword 32) (dq : dfrac)
      : iProp Σ :=
    (
     (* --- [boot_entry_pre]'s output, minus the two wire pins --- *)
     mmode_config (DfracOwn 1) ∗
     pmpcfg_n ↦ᵣ register_lookup pmpcfg_n rs ∗
     pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs ∗
     pc_is (mword_of_int KernelSyms._entry) ∗
     gpr_file (boot_regfile rs) ∗
     mhartid ↦ᵣ boot_w64 (Z.of_nat (fin_to_nat cpu_id)) ∗
     mepc ↦ᵣ register_lookup mepc rs ∗
     satp ↦ᵣ register_lookup satp rs ∗
     medeleg ↦ᵣ register_lookup medeleg rs ∗
     mideleg ↦ᵣ register_lookup mideleg rs ∗
     mie ↦ᵣ register_lookup mie rs ∗
     menvcfg ↦ᵣ boot_w64 0 ∗
     mcounteren ↦ᵣ register_lookup mcounteren rs ∗
     stimecmp ↦ᵣ register_lookup stimecmp rs ∗
     tlb ↦ᵣ register_lookup tlb rs ∗
     (∃ v : mword 64, stvec ↦ᵣ v) ∗
     (∃ v : mword 64, sepc ↦ᵣ v) ∗
     (∃ v : mword 64, scause ↦ᵣ v) ∗
     (∃ v : mword 64, stval ↦ᵣ v) ∗
     (∃ v : mword 64, sscratch ↦ᵣ v) ∗
     mstateen0 ↦ᵣ (mword_of_int 0 : mword 64) ∗
     sstateen0 ↦ᵣ (mword_of_int 0 : mword 32) ∗
     (* --- this hart's slice of the image and of the stack --- *)
     mb_ld_ea ↦ₚ₈{ dq } v_stack0 ∗
     (* ...and the window it sits in is PRISTINE -- nobody writes the GOT --
        which is what [SpecEntry.wp_entry_boot]'s raw load reads through
        (TsoCtx.pristine_read); minted once by [BootShared] beside the word *)
     TsoCtx.pristine_win mb_ld_ea 8 ∗
     (* CONTEXT-FREE (item 38, checklist line four): this bundle is minted
        ONCE for all eight harts, so its context-indexed cells are [∀ ξ] --
        exclusive and timestamp-zero -- and the hart's own chain instantiates
        them at its own ξ ([boot_entry_bridge], below).  Spelled exactly as
        [BootShared.boot_hart_bss]'s rows so the carve's frames go through
        syntactically. *)
     (∀ ξ : CtxId,
        stack_own_phys (XI := ξ) (mword_of_int (sp_of (fin_to_nat cpu_id)))
          boot_stack_depth) ∗
     (* --- the bridge's adequacy-minted and .bss inputs --- *)
     strans_pending ∗
     strans_pending ∗
     ghost_var sie_gname (1/2) ('b"0" : mword 1) ∗
     ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
     ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
     (* BOTH halves of the SPP mirror.  Adequacy mints them at an arbitrary
        value; the M->S bridge is what ties them to the mstatus it installs,
        so nothing here depends on which value that is. *)
     sret_bits ('b"0" : mword 1) ('b"0" : mword 1) ∗
     sret_bits ('b"0" : mword 1) ('b"0" : mword 1) ∗
     (∀ ξ : CtxId,
        ctx_word4_pointsto ξ (a_cpu_noff cid_word) (DfracOwn 1) (noff_val 0)) ∗
     (∀ ξ : CtxId,
        ctx_word4_pointsto ξ (a_cpu_int cid_word) (DfracOwn 1) iv) ∗
     (* the WHOLE [cpus[cid].proc] cell -- see [BootShared.boot_hart_bss].
        It is private to this hart and goes into [IntrDefs.cpu_cells]. *)
     (∀ ξ : CtxId, cur_proc (XI := ξ) zero_reg) ∗
     (* this hart's HELD-LOCK AUTHORITY at the empty set (LockSet.v), minted
        by adequacy beside the other per-hart ghosts.  It goes straight into
        [IntrDefs.cpu_priv] at the M->S bridge and is never named again. *)
     lk_auth cpu_id ∅ ∗
     cpu_ctx_free ∗
     True)%I.

End BootHartRes.
