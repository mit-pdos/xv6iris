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
(*   §1 THE BOOT GEOMETRY and the reset-residue lemma [boot_entry_pre]     *)
(*      live in BootHart.v, together with the per-hart bundle              *)
(*      [boot_hart_res]: everything one hart's chain and BootShared share.   *)
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
Require Import BootHart.   (* §1 geometry, [boot_entry_pre], [boot_hart_res] *)
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
Local Open Scope Z_scope.
Require Import TsoCtx.

(* §1 THE BOOT GEOMETRY and §2 [boot_entry_pre] are in BootHart.v (read its
   header): shared with BootShared.v, which must not wait for LinkMain. *)


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

Require Import UserFd.   (* [ufdG] -- must be IMPORTED here, not reached through BootHart: a
   capacity class reached by a transitive Require has inert field instances
   (durable-notes, "incomplete proof at Qed") *)
Section BootRun.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

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
              Hsepc & Hscause & Hstval & Hssc & Hmse & Hsse & Hgot & #Hpr & Hstk & Hbit & Hbit2 & Hg2 &
              Hg4a & Hg4b & Hspp1 & Hspp2 & Hnoff & Hint & Hproc & Hlks & Hctx & _) Hthr Hcont".
    (* the bundle's [∀ ξ] cells, instantiated ONCE at THIS hart's own context
       (item 38): eight bundles, eight contexts, never the minter's. *)
    iSpecialize ("Hstk" $! cur_ctx).
    iSpecialize ("Hnoff" $! cur_ctx).
    iSpecialize ("Hint" $! cur_ctx).
    iSpecialize ("Hproc" $! cur_ctx).
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
                    Hmenv Hmcen Hstc Hgot Hpr Hstk Hthr Htext").
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
       Hmenv Hmcen Hstc Hgot Hstk Hthr".
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
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma boot_hart_secondary (rs : regstate)
      (iv : mword 32) (dq : dfrac) (γd : uart_names) (γv : disk_names)
      (γi : gname) (ξd : CtxId) :
    reset_regs cpu_id rs ->
    (* a SECONDARY hart: this is what makes main's [beqz a0] fall through *)
    (fin_to_nat cpu_id <> 0)%nat ->
    kernel_text -∗
    kernel_data -∗
    boot_hart_res rs iv dq -∗
    (* this hart's thread of control -- see [boot_entry_bridge] for why it is
       a premise and why it is not inside [boot_hart_res] *)
    own_context cur_ctx -∗
    started_inv γi ξd (main_dep γd γv) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hreset Hnz.
    pose proof (fin_to_nat_lt cpu_id) as Hn.
    iIntros "#Htext #Hdata Hres Hthr #Hstarted".
    iApply (boot_entry_bridge rs iv dq Hreset with "Htext Hres Hthr").
    iIntros (mf) "Hcap Hctx Hcpu Hg Hraw #Htimc Hpc".
    iApply (MainSecondary.wp_main_secondary_sconf mf (kv_frame_slots + K_main)%nat zero_reg γi ξd γd γv
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
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma boot_hart_primary (rs : regstate)
      (iv : mword 32) (dq : dfrac) (γd : uart_names) (γv : disk_names)
      (γi : gname) (ξd : CtxId)
      (ps : list (mword 64)) (l0 : list (bv 8)) (b0 : bool) (c0 : virtio_cfg)
      (* the file system's boot-era mint, at the era's own disk: threaded
         straight through to [SpecMain]'s boot arm (fs-cfg-boot.md stage
         (e)).  This chain neither reads nor opens it. *)
      (dk : Z -> bv 8) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (ndisk : nat)
      (* ...and the durable snapshot the era was minted from (durable-disk
         lane E-himg), threaded the same way *)
      (S : FsState.fs_state_rec) (Pb : Z -> list (bv 8)) (Rspent : gset Z) :
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
    (* THE SNAPSHOT HYPOTHESIS, forwarded whole (fs-cfg-boot.md stage (f);
       durable-disk lane E-himg).  This chain still neither reads nor opens
       it; [ProofMain] is what turns it into [FsReady.fs_geom_ok] and
       [FirstTok.first_fsinit_pures]. *)
    fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
    kernel_text -∗
    kernel_data -∗
    boot_hart_res rs iv dq -∗
    (* this hart's thread of control -- see [boot_entry_bridge] for why it is
       a premise and why it is not inside [boot_hart_res] *)
    own_context cur_ctx -∗
    started_inv γi ξd (main_dep γd γv) -∗ started_prim γi -∗
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
    fs_boot_supply _ _ _ dk sb nib cov γd γv Rspent Pb
      (FsCrash.hdr_wset (FsCrash.fs_blocks dk) (FsImg.sb_logstart sb)) -∗
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
    ([∗ map] i ↦ st ∈ gset_to_gmap HInactive (set_seq 0 8 : gset nat),
       i ↪[dn_head γv] st) -∗
    (* ...the CLAIM MAP's authority, empty (nothing has been published)... *)
    ghost_map_auth (dn_claim γv) 1 (∅ : gmap nat dclaim) -∗
    disk_done_lb γv 0%nat -∗
    kpt_unset -∗
    (* A6.71: ...and the pin bound's one-shot beside it -- [kpt_inv_alloc]
       takes both, and both are minted once at adequacy (A6.70 finding 1). *)
    kptb_unset -∗
    kmap_auth kmap_M0 -∗
    ([∗ list] p ∈ ps, page_own p) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hreset Hz Hprun Hlen Hlive Himg.
    iIntros "#Htext #Hdata Hres Hthr #Hstarted Hprim Hlk Hgl Hfirst Hnext Hpark Hpst Hpav
             Hfs Hmir Hirslot Hirauth #Hcert #Hseam
             #Hdev #Hwire Htx Hsent Hlb Hdlab Hcfg Hclaim Hcmauth #Hdone Hkpt Hkptb Hkmap Hpages".
    iApply (boot_entry_bridge rs iv dq Hreset with "Htext Hres Hthr").
    iIntros (mf) "Hcap Hctx Hcpu Hg Hraw #Htimc Hpc".
    iApply (Main.wp_main_boot_sconf mf (kv_frame_slots + K_main)%nat zero_reg ps
              (add_vec (and_vec (add_vec (mword_of_int kmem_lo : mword 64)
                 (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv)
              (mword_of_int 0x88000000 : mword 64) γd γv l0 b0 c0
              dk sb nib cov ndisk S Pb Rspent
              (register_lookup tlb rs) γi ξd (main_dep γd γv)
              (cid_word_of_zero _ Hz) K_main_boot_le eq_refl eq_refl Hprun Hlen
              Hlive Himg eq_refl
              with "Hcap Hctx Hcpu Hg Htext Hdata Hpc Hstarted Hprim [] Hlk Hgl
                    Hfirst Hnext Hpark Hpst Hpav Hfs Hmir Hirslot Hirauth
                    Hcert Hseam
                    Hdev Hwire Htx Hsent Hlb Hdlab
                    Hcfg Hclaim Hcmauth Hdone Htimc Hraw Hkpt Hkptb Hkmap Hpages").
    (* THE DEPOSIT WAND: main's boot arm hands over exactly [main_deposit]'s
       nine conjuncts at exactly its eight existential witnesses, plus
       (A6.138) the position-indexed bound tie the store site supplies. *)
    iModIntro.
    iIntros (pos γpr γs γk pd pav pu root pas)
      "Hpr Hpi Hcc Hdl Hgeom Hkpti Hroot Htramp Hkst Hbnd".
    rewrite /main_dep /main_deposit.
    iSplitR "Hbnd"; last iExact "Hbnd".
    iExists γpr, γk, γs, pd, pav, pu, root, pas.
    iFrame "Hpr Hpi Hcc Hdl Hgeom Hkpti Hroot Htramp Hkst".
  Qed.

End BootPrimary.
