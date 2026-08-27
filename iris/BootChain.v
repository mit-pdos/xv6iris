(* ====================================================================== *)
(* BootChain.v -- THE PER-HART BOOT CHAIN.                                 *)
(*                                                                        *)
(* One hart's whole life, from the residue a power-on hands it to the       *)
(* [WP (LoopE gen c)] adequacy asks for, composed out of the three proven   *)
(* contracts:                                                             *)
(*                                                                        *)
(*   [SpecEntry.wp_entry_boot]  ([LinkEntry.Entry])   -- reset -> <main>    *)
(*   [BootBridge.boot_bridge]                         -- M-mode -> sconf    *)
(*   [SpecMain.wp_main_boot_sconf] / [SpecMainSecondary.                    *)
(*    wp_main_secondary_sconf]                        -- <main> -> forever  *)
(*                                                                        *)
(* NOTHING HERE IS ABOUT MORE THAN ONE HART.  Every statement is at the     *)
(* AMBIENT [CpuId], so the client (adequacy) applies it once per hart with  *)
(* [CID := c]; the resources it takes are exactly that hart's share of the  *)
(* client bundle plus the SHARED persistents, and never another hart's      *)
(* anything.                                                              *)
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
(*   §2 THE M-MODE HALF, COMPOSED -- [boot_entry_bridge]: this hart's       *)
(*      reset register cells plus the image plus its own .bss become        *)
(*      main's per-hart precondition ([sie_cap_gpr] + [cpu_own] + the SIE   *)
(*      spare quarter + [main_hart_raw]) and [pc_is <main>].  The memory    *)
(*      side enters as premises in the CARVE's vocabulary (BootCarve /      *)
(*      BootCarveMain produce every one of them), so the remaining boot     *)
(*      client is the cut chain plus the ghost allocations.                 *)
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
Require Import LinkEntry.
Require Import SpecMainSecondary LinkMainSecondary.
Require Import StartedInv DevModel.
Require Import WpUart DiskPtsto.
Require Import KallocInv FdSlots.
Require Import LockSet.
Require Import FileInvDefs.
Require Import KptGhost VirtioProto VirtioModel SpecFreerange KvmSpec.
Require Import LinkMain.
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
Require Import CtxRecord.   (* [ctx_parked_inv]: the deposit record's token *)
Local Open Scope Z_scope.

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

Section BootChain.
  Context `{!riscvGS Σ}.
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

End BootChain.

(* ====================================================================== *)
(* §3  THE M-MODE HALF, RUN AND BRIDGED.                                   *)
(*                                                                        *)
(* [boot_entry_bridge] takes [boot_entry_pre]'s output (minus the two PLIC *)
(* wire pins -- see below), runs [SpecEntry.wp_entry_boot] over §1's        *)
(* geometry, and applies [BootBridge.boot_bridge] to its postcondition, so  *)
(* what reaches the continuation is EXACTLY the per-hart half of either     *)
(* main arm's precondition plus [pc_is <main>].                            *)
(*                                                                        *)
(* THE WIRE PINS ARE NOT TAKEN HERE, and that is forced by the control      *)
(* flow, exactly as the [cpus[h].proc] split was (M6c (2a)):                *)
(* [WireInv.wire_inv_alloc] wants ALL EIGHT harts' [sig_seip]/[sig_meip]    *)
(* cells at once, and it must run before any hart's WP -- so the client     *)
(* calls [boot_entry_pre] for every hart inside its own [={⊤}=∗], keeps the *)
(* sixteen pins for the wire invariant, and hands each hart the rest here.  *)
(* That is why [boot_entry_pre] is a separate fupd rather than folded in.   *)
(*                                                                        *)
(* THE ENTRY mstatus IS NEVER SEEN.  The contract's post hands back          *)
(* [mstatus_kernel_facts] of the FINAL mstatus (M6c (2b)), which is both of  *)
(* the bridge's mstatus premises one lemma apart, so the client never learns *)
(* the entry value -- which it could not, since [mmode_config] hides it.     *)
(* ====================================================================== *)

Section BootRun.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
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
     stack_own_phys (mword_of_int (sp_of (fin_to_nat cpu_id))) boot_stack_depth ∗
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
     (* THE cpus[cid] noff/intena CELLS, AT A ∀-QUANTIFIED CONTEXT, for
        EXACTLY the [proc] row's reason below and by the SAME ruling.  They
        were raw ([↦₄] over [RiscvPtsto]) until M1 stage 2 flipped the 4-byte
        family (tso-port.md §0.19′); the flip would otherwise have made this
        whole bundle ξ-INDEXED again and re-opened the eight-hart adequacy
        trap -- [BootShared.boot_shared_alloc] carves all eight bundles under
        ONE ambient while the harts run at eight distinct
        [own_context_boot] identities, so a pinned bundle serves at most one
        of them (it failed exactly there, at [SystemAdequacy]'s
        [boot_hart_secondary], and it failed by CRAWLING).  The ∀ is sound
        here for the [proc] row's two reasons: both cells are EXCLUSIVE (so
        the ∀ is not duplicable -- it is not under a [□]) and both are
        TIMESTAMP-0 boot-image cells, §0.4 item 6's one sanctioned case. *)
     (∀ ξ : CtxId,
        ctx_word4_pointsto ξ (a_cpu_noff cid_word) (DfracOwn 1) (noff_val 0)) ∗
     (∀ ξ : CtxId,
        ctx_word4_pointsto ξ (a_cpu_int cid_word) (DfracOwn 1) iv) ∗
     (* the WHOLE [cpus[cid].proc] cell -- see [BootShared.boot_hart_bss].
        It is private to this hart and goes into [IntrDefs.cpu_cells].

        AT A ∀-QUANTIFIED CONTEXT, which is what makes this whole bundle
        ξ-FREE (tso-port.md §0.16′).  It was the ONE ξ-indexed row here, and
        the header of [boot_entry_bridge] below already says why that could
        not stand: the carve runs ONCE, under one ambient, while the eight
        harts run at eight DISTINCT [own_context_boot] identities, so a bundle
        pinned at the carve's ξ can serve at most one of them.  The ∀ is sound
        exactly here -- the cell is EXCLUSIVE (so the ∀ is not duplicable; it
        is not under a [□]) and it is a TIMESTAMP-0 boot-image cell, §0.4
        item 6's one sanctioned case.  [BootShared.boot_hart_pre] proves it by
        doing the phys→ctx mint under the ∀; [boot_entry_bridge] instantiates
        it at its own ambient. *)
     (∀ ξ : CtxId, cur_proc (XI := ξ) zero_reg) ∗
     (* this hart's HELD-LOCK AUTHORITY at the empty set (LockSet.v), minted
        by adequacy beside the other per-hart ghosts.  It goes straight into
        [IntrDefs.cpu_priv] at the M->S bridge and is never named again. *)
     lk_auth cpu_id ∅ ∗
     cpu_ctx_free ∗
     True)%I.

  Lemma boot_entry_bridge (rs : regstate)
      (iv : mword 32) (dq : dfrac) :
    (* [reset_regs] alone: the mie / mideleg facts [boot_bridge] needs ("no
       non-delegated interrupt is enabled") are now PINS of the reset machine
       rather than premises here, read off by name with
       [reset_regs_{mie,mideleg}].  They are necessary: at a nonzero entry
       [mie] the bridge's premise is FALSE, since start()'s `csrs sie` does not
       clear an M-mode enable it finds set while [legalize_mideleg] forces the
       matching delegation bit to 0.  satp needs nothing -- writing 0 selects
       Bare whatever the old value was. *)
    reset_regs cpu_id rs ->
    (* the image, PERSISTENT and shared by every hart, so it is not part of
       the per-hart bundle *)
    kernel_text -∗
    boot_hart_res rs iv dq -∗
    (* THIS HART'S THREAD OF CONTROL (tso-port leg M2), at the AMBIENT [XI]:
       taken, not minted, exactly as [BootBridge.boot_bridge] takes it, so
       that main's whole cone runs at the caller's [XI] with no explicit
       context anywhere.  It is NOT folded into [boot_hart_res] because
       [own_context] is EXCLUSIVE and the eight harts need eight DISTINCT
       contexts: [BootShared.boot_shared_alloc] hands its per-hart bundle out
       under one ambient [XI], so a token inside it would have to carry its
       own [∃ ξ] and re-instantiate the bundle hart by hart.  Keeping it a
       separate premise lets [SystemAdequacy] mint one token per hart and
       instantiate THIS lemma at that hart's [ξ]. *)
    own_context cur_ctx -∗
    (* --- and what main's arm then wants of this hart --- *)
    (* THE avail INDEX IS [kv_frame_slots + K_main], NOT [K_main]: it is what
       [BootBridge.boot_bridge] hands back, and what it hands back is the
       carve it actually takes off [sp0] ([boot_stack_slots K] =
       [2 + (kv_frame_slots + K)]).  See that file's header for why holding
       it at [K_main] would be a silent 78-slot leak that leaves main unable
       to fund a trap. *)
    (∀ mf : regfile,
       sie_cap_gpr KT0 mf (kv_frame_slots + K_main)%nat false zero_reg -∗
       cpu_ctx_free -∗
       cpu_own 0 false zero_reg false ∅ -∗
       ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
       main_hart_raw (register_lookup tlb rs) -∗
       (* THE TIMER CAPABILITY, allocated HERE rather than in main: it is
          PERSISTENT and PER-HART, and this is the one place that holds the
          two cells it is made of -- [mcounteren] (persisted into
          [sstc_enabled]) and [stimecmp] (sealed into [stimecmp_inv]).  Both
          used to be dropped at this seam. *)
       timer_cap -∗
       pc_is (mword_of_int KernelSyms.main) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hreset.
    pose proof (reset_regs_mie _ _ Hreset) as Hmie0.
    pose proof (reset_regs_mideleg _ _ Hreset) as Hmdl0.
    (* the PMP fact, by name: [reset_regs] gives [pmp_all_off] of the reset
       value, which is exactly what both callees take. *)
    pose proof (reset_regs_pmpcfg _ _ Hreset) as Hpmpc0.
    iIntros "#Htext (Hmm & Hpmpc & Hpmpa & Hpc & Hfile & Hmh & Hmepc & Hsatp &
              Hmede & Hmdl & Hmie & Hmenv & Hmcen & Hstc & Htlb & Hstvec &
              Hsepc & Hscause & Hstval & Hssc & Hmse & Hsse & Hgot & Hstk & Hbit & Hbit2 & Hg2 &
              Hg4a & Hg4b & Hspp1 & Hspp2 & Hnoff & Hint & Hproc & Hlks & Hctx & _) Hthr Hcont".
    (* the [proc] cell arrives ∀-CONTEXT (see [boot_hart_res]) -- this hart
       takes it at its own ambient, which is the identity its [own_context]
       names *)
    iSpecialize ("Hproc" $! cur_ctx).
    (* ...and so do the two [cpus[cid]] words, since M1 stage 2 *)
    iSpecialize ("Hnoff" $! cur_ctx).
    iSpecialize ("Hint" $! cur_ctx).
    pose proof (fin_to_nat_lt cpu_id) as Hn.
    (* the two persistent halves of the config bundle, kept for the bridge *)
    iDestruct (mmode_config_persist with "Hmm") as "[[#Hhw #Hmin] Hmm]".
    (* The contract takes sp0 as a PARAMETER, so it runs at §1's concrete
       address throughout and there is no rewriting to do on either side. *)
    iApply (Entry.wp_entry_boot (boot_regfile rs) v_stack0
              (boot_w64 (Z.of_nat (fin_to_nat cpu_id)))
              (register_lookup mepc rs) (register_lookup satp rs)
              (register_lookup medeleg rs) (register_lookup mideleg rs)
              (register_lookup mie rs) (boot_w64 0)
              (register_lookup stimecmp rs) (register_lookup mcounteren rs)
              (register_lookup pmpcfg_n rs) (register_lookup pmpaddr_n rs)
              (mword_of_int (sp_of (fin_to_nat cpu_id)))
              boot_stack_depth
              (sp0_val _ Hn) boot_stack_depth_entry Hpmpc0
              eq_refl Hmie0 Hmdl0
              (ti_ea_ra_bound _ Hn) (ti_ea_s0_bound _ Hn)
              with "Hmm Hpmpc Hpmpa Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie
                    Hmenv Hmcen Hstc Hgot Hstk Htext").
    (* Everything the M-mode side computed arrives ABSTRACT, with the eight
       facts the bridge wants (the eighth is [mief = MIE_S], the pin
       [IntrDefs.sconf] needs -- see claude-notes/completed/kerneltrap.md);
       the two mstatus premises are one lemma each off the exported
       [mstatus_kernel_facts]. *)
    iIntros (Mf msf satpf medelegf midelegf mief menvcfgf stimecmpf mcounterenf
             pmpcfgf pmpaddrf)
      "(%Hsp & %Htpf & %Hkf & %Hmenvl & %Hmiez & %Hmiev & %Hsatpm & %Hpmpo & %HmcenTM
        & %Hmedv)
       Hhs Hpriv Hmst Hpmpc Hpmpa Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie
       Hmenv Hmcen Hstc Hgot Hstk".
    (* the two stack-location bounds: [sp0_uint] rewrites only at ITS OWN
       elaboration of [uint]'s width index, so the facts are asserted here at
       §1's form and handed to the bridge by [exact] (conversion sees through
       [Z_idx 64] vs [64%N] where [rewrite] does not). *)
    assert (Hlo : text_end + 8 * Z.of_nat (boot_stack_slots K_main)
                  <= uint (mword_of_int (sp_of (fin_to_nat cpu_id)) : mword 64))
      by (rewrite (sp0_uint _ Hn); exact (sp_of_lo _ Hn)).
    assert (Hhi : uint (mword_of_int (sp_of (fin_to_nat cpu_id)) : mword 64)
                  <= ram_base + ram_size)
      by (rewrite (sp0_uint _ Hn); exact (sp_of_hi _ Hn)).
    iEval (rewrite Hmedv) in "Hmede".
    (* THE TIMER CAPABILITY IS MINTED BEFORE THE BRIDGE, because the bridge
       is what puts it inside [sie_cap] (see the note at [IntrDefs.sie_cap]).
       The two cells it is made of -- [mcounteren], persisted into
       [sstc_enabled], and [stimecmp], sealed into [stimecmp_inv] -- are
       exactly what timerinit wrote and what this seam used to drop.  The
       fupd goes in front of a [WP (Loop)] goal, so peel it with [fupd_wp]
       first; the [iModIntro] goes back after the bridge. *)
    iApply fupd_wp.
    iMod (timer_cap_intro ⊤ (DfracOwn 1) mcounterenf stimecmpf HmcenTM
            with "Hmcen Hstc") as "#Htimc".
    iMod (boot_bridge K_main boot_stack_depth Mf
              (mword_of_int (sp_of (fin_to_nat cpu_id)))
              msf satpf midelegf mief menvcfgf
              (mb_tpv (boot_w64 (Z.of_nat (fin_to_nat cpu_id))))
              pmpcfgf pmpaddrf (register_lookup tlb rs)
              (noff_val 0) iv zero_reg _ _ _ _
              Hsp Htpf (mstatus_kernel_SIE _ Hkf) (sconf_ms_facts_of_kernel _ Hkf)
              Hmenvl Hmiez Hmiev Hsatpm Hpmpo
              ltac:(exact (st_tpv_of_nat _ Hn))
              boot_stack_depth_bridge
              Hlo Hhi
              eq_refl
              with "Hhw Hmin Htimc Hhs Hpriv Hmst Hpmpc Hpmpa Hfile Hsatp Hmdl Hmie
                    Hmenv Hstk Hthr Hbit Hbit2 Hg2 Hg4a Hg4b Htlb Hsepc Hscause
                    Hstval Hspp1 Hspp2 Hstvec Hnoff Hint Hproc Hlks
                    Hssc Hmede Hmse Hsse Hctx")
      as (mf) "(Hcap & Hctx & Hcpu & Hg & Hraw)".
    iModIntro.
    iApply ("Hcont" $! mf with "Hcap Hctx Hcpu Hg Hraw Htimc Hpc").
  Qed.

End BootRun.

(* ====================================================================== *)
(* §4  A SECONDARY HART'S WHOLE CHAIN.                                     *)
(*                                                                        *)
(* [boot_hart_secondary]: for a hart with [fin_to_nat c <> 0], §3 composed  *)
(* with [SpecMainSecondary.wp_main_secondary_sconf] -- reset residue to      *)
(* "spins forever, never stuck", with NOTHING left over.  Seven of the eight *)
(* harts need only this; the boot hart's arm additionally consumes the whole *)
(* boot supply and is where the shared allocation lands.                     *)
(*                                                                        *)
(* The three inputs beside the per-hart bundle are all PERSISTENT and all    *)
(* SHARED: the image ([kernel_text] / [kernel_data]) and                     *)
(* the handover channel [started_inv (main_deposit γd γv Φ)] -- which the    *)
(* client allocates ONCE, at that concrete payload, and hands to all eight   *)
(* harts (main-boot's outstanding [P] choice, settled).                      *)
(* ====================================================================== *)

Section BootSecondary.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma boot_hart_secondary (rs : regstate)
      (iv : mword 32) (dq : dfrac) (xid : CtxId)
      (γd : uart_names) (γv : disk_names) :
    reset_regs cpu_id rs ->
    (* a SECONDARY hart: this is what makes main's [beqz a0] fall through *)
    (fin_to_nat cpu_id <> 0)%nat ->
    kernel_text -∗
    kernel_data -∗
    boot_hart_res rs iv dq -∗
    (* this hart's thread of control -- see [boot_entry_bridge] for why it is
       a premise and why it is not inside [boot_hart_res] *)
    own_context cur_ctx -∗
    started_inv (main_deposit xid γd γv) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hreset Hnz.
    pose proof (fin_to_nat_lt cpu_id) as Hn.
    iIntros "#Htext #Hdata Hres Hthr #Hstarted".
    iApply (boot_entry_bridge rs iv dq Hreset with "Htext Hres Hthr").
    iIntros (mf) "Hcap Hctx Hcpu Hg Hraw #Htimc Hpc".
    iApply (MainSecondary.wp_main_secondary_sconf mf (kv_frame_slots + K_main)%nat zero_reg xid γd γv
              (register_lookup tlb rs)
              (cid_word_of_nz _ Hn Hnz)
              (cid_word_of_lt_dev _ Hn)
              K_main_secondary_le eq_refl
              with "Hcap Hctx Hcpu Hg Htext Hdata Hpc Hstarted Htimc Hraw").
  Qed.

End BootSecondary.

(* ====================================================================== *)
(* §5  THE BOOT HART'S WHOLE CHAIN.                                        *)
(*                                                                        *)
(* [boot_hart_primary]: for the hart with [fin_to_nat c = 0], §3 composed   *)
(* with [Main.wp_main_boot_sconf] -- the same shape as §4, but this arm      *)
(* consumes the WHOLE BOOT SUPPLY (the carved .bss bundles, the hart tags,   *)
(* the proc-state variables, the device tokens, the two global one-shots,    *)
(* the free-page run), so the supply is what the statement is               *)
(* mostly made of.                                                        *)
(*                                                                        *)
(* THE DEPOSIT WAND IS DISCHARGED HERE, not taken.  [SpecMain]'s boot arm    *)
(* asks for [□ (∀ γpr γs γk pd pav pu root pas, <nine facts> -∗ P)] and this *)
(* chain instantiates [P := SpecMainSecondary.main_deposit γd γv Φ] -- whose *)
(* body IS those nine facts under an existential over exactly those eight    *)
(* names.  So the wand is [iIntros] + [iExists] + [iFrame], and THAT is what *)
(* ties the two arms together: the boot hart deposits precisely what a       *)
(* secondary hart's [started_inv] withdrawal (§4) consumes.                 *)
(* ====================================================================== *)

Section BootPrimary.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma boot_hart_primary (rs : regstate)
      (iv : mword 32) (dq : dfrac) (xid : CtxId)
      (γd : uart_names) (γv : disk_names)
      (ps : list (mword 64)) (l0 : list (bv 8)) (b0 : bool) (c0 : virtio_cfg)
      (* the file system's boot-era mint, at the era's own disk: threaded
         straight through to [SpecMain]'s boot arm (fs-cfg-boot.md stage
         (e)).  This chain neither reads nor opens it. *)
      (dk : Z -> bv 8) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (ndisk : nat) :
    reset_regs cpu_id rs ->
    (* the BOOT hart: this is what makes main's [beqz a0] take the boot path *)
    (fin_to_nat cpu_id = 0)%nat ->
    (* kinit's free-page run, and enough pages for kvmmake + the 64 kstacks
       + the disk's 3.  [kmem_lo] IS the dumped `end` symbol (see [SpecMain]'s
       premise), so the cursor is PGROUNDUP(end) + PGSIZE and tracks the
       image. *)
    prun (mword_of_int 0x88000000 : mword 64)
      (add_vec (and_vec (add_vec (mword_of_int kmem_lo : mword 64)
         (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv) ps ->
    (K_kvmmake + 64 + 3 < length ps)%nat ->
    (* the disk's protocol is in its not-live arm at boot *)
    virtio_live c0 = false ->
    (* THE IMAGE HYPOTHESIS, forwarded whole (fs-cfg-boot.md stage (f)).
       This chain still neither reads nor opens it; [ProofMain] is what
       turns it into [FsReady.fs_geom_ok] and
       [FirstTok.first_fsinit_pures]. *)
    fs_boot_image_wf dk ndisk sb nib cov ->
    kernel_text -∗
    kernel_data -∗
    boot_hart_res rs iv dq -∗
    (* this hart's thread of control -- see [boot_entry_bridge] for why it is
       a premise and why it is not inside [boot_hart_res] *)
    own_context cur_ctx -∗
    started_inv (main_deposit xid γd γv) -∗
    (* THE DEPOSIT RECORD'S OWN TOKEN: main deposits its three ξ-indexed
       rows into [xid] at the [started = 1] store, which raises the stamp
       (tso-absorb-memo.md §5). *)
    ctx_parked_inv xid -∗
    (* --- the boot supply --- *)
    main_locks_raw -∗
    main_globals_raw -∗
    (* the image's writable initialized globals -- main spends [nextpid] on
       the pid lock, see [SpecMain]'s own row.  Spelled out rather than named
       as [BootShared.main_data_raw]: that file sits ABOVE this one, so the
       name is not in scope here either; [SystemAdequacy] splits the pair. *)
    (* PINNED, not existential: forkret's branch is decided by this cell,
       so a holder of the existential cannot tell which arm it is in.
       [BootShared.main_data_raw] carries the same shape. *)
    ((mword_of_int KernelSyms.first_1 : mword 64) ↦₄ (mword_of_int 1 : mword 32)) -∗
    (∃ w : mword 32, (mword_of_int KernelSyms.nextpid : mword 64) ↦₄ w) -∗
    ([∗ list] i ∈ seq 0 NPROC, hart_full i (0%fin : CPU)) -∗
    ([∗ list] i ∈ seq 0 NPROC, pstate_full i UNUSED) -∗
    (* the proc table's counted regime, straight through from
       [BootShared.boot_shared_alloc] to main -- see [SpecMain]'s own row *)
    procs_avail (Some NPROC) -∗
    (* the file system's boot-era mint and the iref-slot authority, both out
       of [BootShared.boot_shared_alloc] and both spent in
       [ProofMain.mn_grp_fs] -- see [SpecMain]'s own rows *)
    fs_boot_supply _ _ dk sb nib cov γd γv -∗
    (* rows (B) and (C) of the fsinit bundle -- see [SpecMain]'s own rows.
       Row (B) is VALUE-BEARING since durable-disk 1a: the era's mirror half
       at the picture of the disk it boots on, plus the swap receipt. *)
    log_mirror_born (FsCrash.mirror_of (FsCrash.fs_blocks dk)) -∗
    iref_slots 2 -∗
    iref_slots_auth -∗
    (* ---- STAGE (f): ROWS 7 AND 8 OF [FirstTok.first_boot_persist] ----
       [gen_cert] is [BootShared.boot_shared_alloc]'s own persistent output
       and used to stop at [SystemAdequacy]; [FsCrash.fs_crash_seam] is the
       adequacy-level premise [SystemAdequacy.xv6_boot_era] takes (its
       header says why it cannot be produced inside an era).  Both are
       PERSISTENT, this chain neither reads nor spends either, and main
       parks them in [FirstTok.first_boot_persist] at +0x9e.  The seam is
       spelled at the ERA's [cov]/[sb], not at the ambient [fscfg] fields:
       [FsCfgBoot.fs_boot_supply]'s ties are what connect the two, and
       [ProofMain] is where they are spent. ---- *)
    gen_cert -∗
    FsCrash.fs_crash_seam cov (FsImg.sb_logstart sb) -∗
    dev_inv γd γv -∗
    wire_inv -∗
    uart_tx_own γd l0 -∗ uart_sent γd l0 -∗ uart_out_lb γd l0 -∗
    uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
    disk_cfg_is γv (DfracOwn (1/2)) c0 -∗
    ghost_map_auth (dn_claim γv) 1 (∅ : gmap nat dclaim) -∗
    disk_done_lb γv 0%nat -∗
    kpt_unset -∗
    kmap_auth kmap_M0 -∗
    ([∗ list] p ∈ ps, page_own p) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hreset Hz Hprun Hlen Hlive Himg.
    iIntros "#Htext #Hdata Hres Hthr #Hstarted #Hpkinv Hlk Hgl Hfirst Hnext Hpark Hpst Hpav
             Hfs Hmir Hirslot Hirauth #Hcert #Hseam
             #Hdev #Hwire Htx Hsent Hlb Hdlab Hcfg Hclaim #Hdone Hkpt Hkmap Hpages".
    iApply (boot_entry_bridge rs iv dq Hreset with "Htext Hres Hthr").
    iIntros (mf) "Hcap Hctx Hcpu Hg Hraw #Htimc Hpc".
    iApply (Main.wp_main_boot_sconf mf (kv_frame_slots + K_main)%nat zero_reg ps
              (add_vec (and_vec (add_vec (mword_of_int kmem_lo : mword 64)
                 (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv)
              (mword_of_int 0x88000000 : mword 64) γd γv l0 b0 c0
              dk sb nib cov ndisk
              (register_lookup tlb rs) xid (main_deposit xid γd γv)
              (cid_word_of_zero _ Hz) K_main_boot_le eq_refl eq_refl Hprun Hlen
              Hlive Himg eq_refl
              with "Hcap Hctx Hcpu Hg Htext Hdata Hpc Hstarted Hpkinv [] Hlk Hgl
                    Hfirst Hnext Hpark Hpst Hpav Hfs Hmir Hirslot Hirauth
                    Hcert Hseam
                    Hdev Hwire Htx Hsent Hlb Hdlab
                    Hcfg Hclaim Hdone Htimc Hraw Hkpt Hkmap Hpages").
    (* THE DEPOSIT WAND: main's boot arm hands over exactly
       [main_deposit_rows]' nine conjuncts at exactly its eight existential
       witnesses, so the wand is intro + exists + frame and nothing else.
       IT IS PURE PACKING, and it has to be: it sits under a [□], and
       [TsoCtx.ctx_deposit] consumes an [own_context], which nothing under a
       [□] can do.  So the rows arrive ALREADY AT [xid] -- [ProofMain]'s
       [mn_grp_started] does the deposit, at the one point on main's boot arm
       that still holds its [sie_cap_gpr] -- and the record's own token
       invariant is framed in from this chain's premise. *)
    iModIntro.
    iIntros (γpr γs γk pd pav pu root pas)
      "Hpr Hpi Hcc Hdl Hgeom Hkpti Hroot Htramp Hkst".
    rewrite /main_deposit /main_deposit_rows.
    iSplitR; [iExact "Hpkinv" |].
    iExists γpr, γk, γs, pd, pav, pu, root, pas.
    iFrame "Hpr Hpi Hcc Hdl Hgeom Hkpti Hroot Htramp Hkst".
  Qed.

End BootPrimary.
