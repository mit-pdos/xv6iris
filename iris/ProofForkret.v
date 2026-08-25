(* ProofForkret.v -- forkret(), proved: the 24 instructions of the
   already-booted path, ending in the CLOSED trap loop.

   A functor over its three callees' interfaces (myproc, release,
   prepare_return) and over [USERRET_CLOSED], because forkret's last
   instruction is not a return: the [c.jalr a5] at +0x8e enters userret and
   the machine never comes back.

   THREE THINGS THAT ARE NOT PLUMBING.

   * THE INDEX CHANGES AT THE release, NOT BEFORE.  forkret is entered
     holding p->lock, so everything up to +0x10 runs at [b = false];
     [release]'s pop_off restores the base enable, so from +0x14 on the index
     is the caller's [eb] and every step may rebind the hart.  The three
     resources that cross that stretch -- the per-cpu bundle and the two
     [_ext] halves of the arm -- are transported ONCE, at the point of use
     (before the [jal prepare_return]), with [wp_next_chain] chaining the
     whole run of binders.

   * THE FRAME GOES BACK INTO THE FREE-STACK CLAIM.  forkret never runs its
     epilogue, so the six slots it pushed at +0x00 are still carved out at
     the [c.jalr] -- and the residue that parks across user mode claims the
     kernel stack WHOLE ([UsertrapRes.ut_stack ksp av], anchored at the top,
     which is what uservec reloads sp to on the next trap).  So the walk
     rebundles the three saved words and the three scratch slots and merges
     them back ([stack_own_app]); the frame's contents are dead by then, and
     nothing ever returns to it.

   * THE EXIT IS [ut_ret2]'s, RE-USED.  What prepare_return hands back is
     what the trap-side residue is made of, and the derivation is the same
     one usertrap's tail performs: the sret-ready mstatus is DERIVED
     ([UsertrapRes.ut_exit_ms_ok]) from the loose SIE quarter's agreement
     with [sconf]'s half and the travelling sret mirror's with [sconf]'s
     tie.  Here it is assembled into [ut_trap] and immediately reopened by
     [ut_trap_tlb_open], which is what hands userret its [tlb_res_pt] and
     leaves the PARKED residue the caller's wand turns into [URes]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvModelBytes.   (* [pa_add] -- how kexec indexes its byte runs *)
Require Import PageGeom.
Require Import InstrBytes WireInv.   (* [wire_inv] -- named by [fkr_tail]'s statement *)
Require Import KernelText.           (* [kernel_text] *)
Require Import KptExecMap.           (* [kmap_at] / [tramp_vpn] / [KP_rx] *)
Require Import WpLock.               (* [is_lock] / [locked] *)
Require Import RegFile HartTp WpNext CpuOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import KernelRvcDecode.
Require Import WpGprCsrwA.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.   (* [wp_cli_s_sconf] *)
Require Import WpKvminithart.      (* [kvi_satp_word] and its three facts *)
Require Import IntrDefs.
Require Import KptShare UserretDefs.
Require Import TrampPt.  (* [tf_pa] -- the trapframe word addresses *)
Require Import KptTree.  (* [pt_node_claim_from_static] -- phys trapframe words as memory *)
Require Import UserPtTree.  (* [trap_mstatus_ok] *)
Require Import ProcGeom.
Require Import ProcPtOwn.
Require Import FdSlots FileInvDefs.
Require Import ProcInv.
Require Import FirstTok.  (* [first_tok] -- the resource the [if (first)] branch reads *)
Require Import SchedCtx.  (* [procs_inv] / [proc_lock_res] *)
Require Import FsCfg KallocInv.  (* [fsc_kpages] / [kalloc_avail], the token's allocator row *)
Require Import WpUart LogInv.
Require Import IrefSlots ProcAvail.
Require Import CodeForkret.
Require Import SpecMyproc SpecRelease SpecPrepareReturn.
(* the boot arm's three callees.  [FSINIT] and [KEXEC] became callable from
   here only once their contracts stopped demanding [eb = true]: this arm
   runs with interrupts OFF (see [SpecForkret.v]'s header). *)
Require Import SpecFsinit SpecKexec SpecPanic.
Require Import PrintkArgs.  (* [PkAStr] / [pk_desc_res] -- panic's message shape *)
Require Import FsReady.
Require Import SpecUserretClosed.
Require Import ParkCap.   (* [park_token] *)
Require Import UsertrapRes.
Require Import SpecForkret ProofForkretParts ProofPrepareReturnParts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

Module ForkretProof (MP : MYPROC) (RL : RELEASE) (PR : PREPARE_RETURN)
                    (FS : FSINIT) (KX : KEXEC) (PN : PANIC)
                    (UC : USERRET_CLOSED) : FORKRET.

(* register indices and the two scripts, at MODULE level: an [Ltac] defined
   inside a section is discharged over its variables and unusable in the
   next one. *)
Notation Rra := (mword_of_int 1  : mword 5).
Notation Rs0 := (mword_of_int 8  : mword 5).
Notation Rs1 := (mword_of_int 9  : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

(* the closed arithmetic side conditions kexec's contract asks for: a
   [Z]/[nat] bound on a literal, sometimes behind a [Definition]. *)
Ltac kxarith :=
  first [ lia | vm_compute; lia | vm_compute; reflexivity | done ].

Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Section Res.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the residue is the closed loop's, re-exported unchanged *)
  Definition usertrap_res := UC.usertrap_res.
  Definition usertrap_res_parked := UC.usertrap_res_parked.
  Definition usertrap_res_tlb_close := UC.usertrap_res_tlb_close.
  Definition usertrap_res_tlb_open := UC.usertrap_res_tlb_open.
  Definition usertrap_res_bare := UC.usertrap_res_bare.
  Definition usertrap_res_pt_close := UC.usertrap_res_pt_close.
  Definition usertrap_res_pt_open := UC.usertrap_res_pt_open.
  Definition usertrap_res_bare_norm := UC.usertrap_res_bare_norm.
  Definition usertrap_res_csrs_open := UC.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := UC.usertrap_res_sstc.
  Definition usertrap_res_tf_csrs_open := UC.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tf_open := UC.usertrap_res_tf_open.
  (* ...and the park's one producer-side entry, threaded like the rest.
     A file that merely passes the residue through has nothing to say about
     it; the entry exists so that whoever PARKS a never-run process can
     build one (UsertrapRes.v, "THE PARK'S CHANNEL THROUGH THE MODULE
     TYPES"). *)
  Definition usertrap_res_bare_park
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (N : ut_names) (av : nat)
    : ut_park_intro_body
        (fun (h : CpuId) (Xc : CurCtx) => UC.usertrap_res_bare (CID := h) (XI := Xc))
        (park_token (un_s N)) N av
    := UC.usertrap_res_bare_park N av.

  (* the kernel table's invariant, read off the translation residue without
     spending it -- [wp_userret_closed] takes both, and the root has to be
     the same one, which only this projection can guarantee (nothing else
     in forkret names the kernel root; see SpecForkret.v's header). *)
  Lemma fkr_kpt_of_res (r : mword 44) :
    tlb_res_pt r -∗ kpt_inv r ∗ tlb_res_pt r.
  Proof.
    iIntros "H".
    iDestruct "H" as (s0 tv) "(Hsatp & %A & %B & %C & Htlb & Hsnap & Hpmp & #Hk)".
    iFrame "Hk". iExists s0, tv. iFrame "Hsatp".
    iSplitR; [iPureIntro; exact A |].
    iSplitR; [iPureIntro; exact B |].
    iSplitR; [iPureIntro; exact C |].
    iFrame "Htlb Hsnap Hpmp Hk".
  Qed.

End Res.


(* ===================================================================== *)
(*  THE TAIL: +0x64 to the [c.jalr a5] that enters userret.               *)
(* ===================================================================== *)
(* SPLIT OUT BECAUSE BOTH ARMS OF [if (first)] REACH IT, and they reach it
   with different register maps and (after kexec) a different address
   space.  Everything it needs of the map is the two callee-saved words the
   [if] cannot have touched: sp, still at the frame, and s1 = p, which
   myproc put there at +0x0e.

   It is stated at [proc_priv], not at the split block: whichever arm ran,
   the token is back inside by the time control reaches +0x64 -- the steady
   arm never spent it, and the boot arm rebuilt it from
   [FirstTok.first_tok_of_done] after persisting the store. *)
Lemma fkr_tail
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (W : iProp Σ) (j : nat) (γf : gname)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (mt : regfile) (av av2 : nat) (eb : bool) :
  let p   : mword 64 := proc_addr j in
  let ksp : mword 64 := add_vec ks (mword_of_int 4096) in
  (j < NPROC)%nat ->
  (K_prepare_return <= av2)%nat ->
  av = (6 + (trap_res eb + av2))%nat ->
  mt !!! Regidx csp_rs1 = pa_stk ksp 6 ->
  mt !!! Regidx Rs1 = p ->
  kernel_text -∗
  wire_inv -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  pc_is (mword_of_int (FR + 0x64) : mword 64) -∗
  sie_cap_gpr KT1 mt av2 eb p -∗
  cpu_own 0%nat eb p eb ∅ -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb p -∗
  is_kstack p ks -∗
  (* THE FRAME, WHOLE.  forkret never runs its epilogue, so the six slots
     pushed at +0x00 are still carved out here and go back into the
     free-stack claim the residue parks with ([stack_own_app]).  The tail
     does not read them -- what was saved in them is dead by now -- so it
     takes the run rather than the four words. *)
  stack_own (KTR := KT1) ksp 6 -∗
  proc_priv γf p pid V -∗
  (* THE FILE SYSTEM AND THE SEALED [first] CELL, ON EITHER ARM.  +0x64 is
     where the two arms meet and it is the first point at which
     [first_done] is available on BOTH: the steady arm read it out of
     [first_tok]'s persistent steady disjunct at +0x24, the boot arm minted
     it at the release store at +0x38.  The tail does not use it -- it
     hands it straight to the closer, which is the party that cannot have
     it (SpecForkret.v's last header section). *)
  FirstTok.first_done -∗
  W -∗
  (* THE RESIDUE CLOSER, by name: [SpecForkret.forkret_closer] is the wand
     this used to spell out.  It is ~13 % of the Iris context of every step
     of this walk, and a proofmode step's term carries the whole context
     twice -- see that definition's header. *)
  forkret_closer (fun (h : CpuId) (Xc : CurCtx) => usertrap_res_bare (CID := h) (XI := Xc))
                 W γf p ksp pid av -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros p ksp Hjlt Hpr Havsum Hmtsp Hmts1.
  iIntros "#Htext #Hwire #Hclaimmap Hpc Hcg Hcpu Hext Hcx #Hks Hf16 Hpv #Hdone HW Hyield".
  (*  +0x64: jal ra, prepare_return.                                     *)
  (* ================================================================== *)
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x64)) Rra
            (mword_of_int 2806 : mword 21) mt av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc []").
  { iApply (fkr_64 with "Htext"). }
  iIntros (CID7 Hk7) "Hcg Hpc".
  set (T5 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x64) : mword 64) 4)]> mt).
  assert (HT5ra : T5 !!! Regidx Rra = mword_of_int (FR + 0x68))
    by (rewrite /T5 upd_eq; pcw).
  assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /T5 upd_ne; [exact Hmtsp | reg_neq]).
  assert (Hprep : add_vec (mword_of_int (FR + 0x64) : mword 64)
                    (sign_extend' 64 (mword_of_int 2806 : mword 21))
                  = mword_of_int KernelSyms.prepare_return) by pcw.
  iEval (rewrite Hprep) in "Hpc".
  (* the three hart-indexed carriers, moved to the current binder in one
     step -- [wp_next_chain] chains the whole run of [Hk*]. *)
  iDestruct (cpu_own_transport CID CID7 0%nat eb p eb
               ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
  iDestruct (trap_csrs_ext_transport CID CID7 eb p
               ltac:(wp_next_chain) with "Hext") as "Hext".
  iDestruct (cpu_claim_ext_transport CID CID7 eb p
               ltac:(wp_next_chain) with "Hcx") as "Hcx".
  iDestruct (ut_epc_exists with "Hpv") as %[epc Hepc].
  iDestruct (ut_tf_length with "Hpv") as %Htflen0.
  iApply (PR.wp_prepare_return_sconf γf ks pid V T5 av2 p epc eb ∅
            Hpr Hepc with "Hcg Hcpu Hext Htext Hpc Hks Hpv").
  iIntros (CIDf Hkf mf ksat kroot0 vb)
    "%Hcsf %HksatM %Hksata %Hksatp #Hkinv0 Hcg Hcpu Hcpay Hsepc Hscause Hstval
     Hsret Hstvec Hq4 Hkptr Hpv Hpc".
  assert (Hpc68 : ret_pc (T5 !!! Regidx Rra) = mword_of_int (FR + 0x68))
    by (rewrite HT5ra; pcw).
  iEval (rewrite Hpc68) in "Hpc".
  assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup Hcsf csp_rs1 ltac:(vm_compute; reflexivity)); exact HT5sp).
  assert (Hmfs1 : mf !!! Regidx Rs1 = p)
    by (rewrite (callee_saved_lookup Hcsf Rs1 ltac:(vm_compute; reflexivity)); exact Hmts1).
  (* the running claim, whole again -- AT THE RESUMING HART.
     prepare_return parks, so the [_ext] half the caller has been carrying
     is at the pre-call hart and the [_pay] half prepare_return returns is
     at the post-call one; the two print identically and do not unify. *)
  iDestruct (cpu_claim_ext_transport CID7 CIDf eb p
               ltac:(wp_next_chain) with "Hcx") as "Hcx".
  iAssert (cpu_claim p) with "[Hcpay Hcx]" as "Hclaim".
  { iApply (bi.equiv_entails_1_1 _ _ (cpu_claim_ext_split eb p)).
    iSplitL "Hcpay"; [iExact "Hcpay" | iExact "Hcx"]. }
  (* ================================================================== *)
  (*  +0x68 .. +0x6a: MAKE_SATP(p->pagetable), first half.                *)
  (* ================================================================== *)
  (* THE MOVED RECORD IS NEVER SPELLED.  prepare_return hands the block
     back at [upd_tf V (prepare_return_tf ... cid_word)], whose [cid_word]
     names the RESUMING hart -- so writing the term out would pin it to the
     section's hart.  All the walk needs of it is [pv_upt], which [upd_tf]
     does not touch. *)
  (* ... except for the one thing the residue STATES about it: the four
     kernel words are [tf_kernel_words_ok] at the root the satp read gave,
     at this hart ([UsertrapRes.ut_tfk]).  Built here, where the facts are,
     and carried beside the hidden record. *)
  iAssert (∃ V' : pprivate, ⌜pv_upt V' = pv_upt V⌝ ∗
             UsertrapRes.ut_tfk (CID := CIDf) ksp V' ∗ proc_priv γf p pid V')%I
    with "[Hpv]" as (V') "(%HuptV' & #Htfk & Hpv)".
  { iExists (upd_tf V (prepare_return_tf (pv_tf V) ksat ksp (cid_word (CID := CIDf)))).
    iFrame "Hpv". iSplitR; [iPureIntro; reflexivity |].
    iApply (ut_tfk_intro (CID := CIDf) ksp
              (upd_tf V (prepare_return_tf (pv_tf V) ksat ksp (cid_word (CID := CIDf))))
              kroot0
              (prepare_return_tf_kernel_words_ok (CID := CIDf) (pv_tf V) ksat
                 ksp kroot0 Htflen0 HksatM Hksata Hksatp) with "Hkinv0"). }
  iDestruct (proc_priv_copy with "Hpv") as "(Hsz & Hpgt & Hppt & Hpvback)".
  assert (Hc0 : creg2reg_idx (Cregidx (mword_of_int 0)) = Regidx Rs0)
    by (vm_compute; reflexivity).
  assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
    by (vm_compute; reflexivity).
  assert (Hc5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3)
    by (vm_compute; reflexivity).
  assert (Hc6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx Ra4)
    by (vm_compute; reflexivity).
  assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
    by (vm_compute; reflexivity).
  assert (Haddrpg : add_vec (rget mf Rs1)
                      (sign_extend' 64 (mword_of_int 80 : mword 12))
                    = p_pagetable p)
    by (rgne; rewrite Hmfs1; reflexivity).
  iEval (rewrite -Haddrpg) in "Hpgt".
  (* ---- +0x68: c.ld a0,80(s1) ---- *)
  iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x68)) Ra0 Rs1
            (mword_of_int 80 : mword 12) mf (trap_res eb + av2)%nat
            (page_base (ud_root (pv_upt V'))) false
            ltac:(vm_compute; discriminate) ltac:(rdok)
            with "Hcg Hpc [] Hpgt").
  { iApply (fkr_68 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hpgt".
  set (S0 := <[Regidx Ra0 := regval_into_reg
                 (page_base (ud_root (pv_upt V')))]> mf).
  assert (Hp6a : add_vec_int (mword_of_int (FR + 0x68) : mword 64) 2
                 = mword_of_int (FR + 0x6a)) by pcw.
  iEval (rewrite Hp6a) in "Hpc".
  (* ---- +0x6a: srli a0,a0,0xc ---- *)
  iApply (wp_csrli_s_sconf (mword_of_int (FR + 0x6a)) (Cregidx (mword_of_int 2))
            Ra0 (mword_of_int 12 : mword 6) S0 (trap_res eb + av2)%nat false
            Hc2 ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iEval (rewrite -Hc2). iApply (fkr_6a with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S1 := <[Regidx Ra0 := regval_into_reg
                 (shift_bits_right (rget S0 Ra0)
                    (subrange_vec_dec (mword_of_int 12 : mword 6)
                       (Z.sub log2_xlen 1) 0))]> S0).
  assert (Hp6c : add_vec_int (mword_of_int (FR + 0x6a) : mword 64) 2
                 = mword_of_int (FR + 0x6c)) by pcw.
  iEval (rewrite Hp6c) in "Hpc".
  (* ================================================================== *)
  (*  +0x6c .. +0x86: TRAMPOLINE + (userret - trampoline).                *)
  (* ================================================================== *)
  (* ---- +0x6c: lui a4,0x4000 ---- *)
  iApply (wp_lui_s_sconf (mword_of_int (FR + 0x6c)) Ra4
            (mword_of_int 16384 : mword 20) (mword_of_int 0x4000000 : mword 64)
            S1 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) prr_lui_a4
            with "Hcg Hpc []").
  { iApply (fkr_6c with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S2 := <[Regidx Ra4 := regval_into_reg (mword_of_int 0x4000000 : mword 64)]> S1).
  assert (Hp70 : add_vec_int (mword_of_int (FR + 0x6c) : mword 64) 4
                 = mword_of_int (FR + 0x70)) by pcw.
  iEval (rewrite Hp70) in "Hpc".
  (* ---- +0x70: c.addi a4,a4,-1 ---- *)
  iApply (wp_caddi_s_sconf (mword_of_int (FR + 0x70)) Ra4
            (mword_of_int 63 : mword 6) S2 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_70 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S3 := <[Regidx Ra4 := regval_into_reg
                 (add_vec (rget S2 Ra4)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> S2).
  assert (Hp72 : add_vec_int (mword_of_int (FR + 0x70) : mword 64) 2
                 = mword_of_int (FR + 0x72)) by pcw.
  iEval (rewrite Hp72) in "Hpc".
  (* ---- +0x72: c.slli a4,a4,0xc -- a4 = TRAMPOLINE ---- *)
  iApply (wp_cslli_s_sconf (mword_of_int (FR + 0x72)) (Regidx Ra4) Ra4
            (mword_of_int 12 : mword 6) S3 (trap_res eb + av2)%nat false
            eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_72 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S4 := <[Regidx Ra4 := regval_into_reg
                 (shift_bits_left (rget S3 Ra4)
                    (subrange_vec_dec (mword_of_int 12 : mword 6)
                       (Z.sub log2_xlen 1) 0))]> S3).
  assert (HS4a4 : rget S4 Ra4 = uservec_tvec).
  { rgne. rewrite /S4 upd_eq. rgne. rewrite /S3 upd_eq. rgne.
    rewrite /S2 upd_eq. rewrite prr_addi_a4. exact prr_slli_a4. }
  assert (Hp74 : add_vec_int (mword_of_int (FR + 0x72) : mword 64) 2
                 = mword_of_int (FR + 0x74)) by pcw.
  iEval (rewrite Hp74) in "Hpc".
  (* ---- +0x74/+0x78: a5 = &userret ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x74)) Ra5
            (mword_of_int 4 : mword 20) S4 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_74 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S5 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x74) : mword 64)
                    (auipc_off (mword_of_int 4 : mword 20)))]> S4).
  assert (Hp78 : add_vec_int (mword_of_int (FR + 0x74) : mword 64) 4
                 = mword_of_int (FR + 0x78)) by pcw.
  iEval (rewrite Hp78) in "Hpc".
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x78)) Ra5 Ra5
            (mword_of_int 1820 : mword 12) S5 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_78 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S6 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget S5 Ra5)
                    (sign_extend' 64 (mword_of_int 1820 : mword 12)))]> S5).
  assert (HS6a5 : rget S6 Ra5 = (mword_of_int KernelSyms.userret : mword 64)).
  { rgne. rewrite /S6 upd_eq. rgne. rewrite /S5 upd_eq. exact fkr_userret_addr. }
  assert (Hp7c : add_vec_int (mword_of_int (FR + 0x78) : mword 64) 4
                 = mword_of_int (FR + 0x7c)) by pcw.
  iEval (rewrite Hp7c) in "Hpc".
  (* ---- +0x7c/+0x80: a3 = &_trampoline ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x7c)) Ra3
            (mword_of_int 4 : mword 20) S6 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_7c with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S7 := <[Regidx Ra3 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x7c) : mword 64)
                    (auipc_off (mword_of_int 4 : mword 20)))]> S6).
  assert (Hp80 : add_vec_int (mword_of_int (FR + 0x7c) : mword 64) 4
                 = mword_of_int (FR + 0x80)) by pcw.
  iEval (rewrite Hp80) in "Hpc".
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x80)) Ra3 Ra3
            (mword_of_int 1656 : mword 12) S7 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_80 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S8 := <[Regidx Ra3 := regval_into_reg
                 (add_vec (rget S7 Ra3)
                    (sign_extend' 64 (mword_of_int 1656 : mword 12)))]> S7).
  assert (HS8a3 : rget S8 Ra3 = (mword_of_int KernelSyms.trampoline : mword 64)).
  { rgne. rewrite /S8 upd_eq. rgne. rewrite /S7 upd_eq. exact fkr_trampoline_addr. }
  assert (HS8a5 : rget S8 Ra5 = (mword_of_int KernelSyms.userret : mword 64)).
  { rgne. rewrite /S8 upd_ne; [| reg_neq]. rewrite -HS6a5. rgne. reflexivity. }
  assert (Hp84 : add_vec_int (mword_of_int (FR + 0x80) : mword 64) 4
                 = mword_of_int (FR + 0x84)) by pcw.
  iEval (rewrite Hp84) in "Hpc".
  (* ---- +0x84: c.sub a5,a5,a3 -- the offset, 0x9c ---- *)
  iApply (wp_csub_s_sconf (mword_of_int (FR + 0x84)) Ra5 Ra3
            S8 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iEval (rewrite -Hc5 -Hc7). iApply (fkr_84 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (S9 := <[Regidx Ra5 := regval_into_reg
                 (sub_vec (rget S8 Ra5) (rget S8 Ra3))]> S8).
  assert (HS9a5 : rget S9 Ra5 = (mword_of_int 0x9c : mword 64)).
  { rgne. rewrite /S9 upd_eq. rewrite HS8a5 HS8a3. exact fkr_userret_off. }
  assert (HS9a4 : rget S9 Ra4 = uservec_tvec).
  { rgne. rewrite /S9 upd_ne; [| reg_neq]. rewrite -HS4a4. rgne.
    rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
    rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
    reflexivity. }
  assert (Hp86 : add_vec_int (mword_of_int (FR + 0x84) : mword 64) 2
                 = mword_of_int (FR + 0x86)) by pcw.
  iEval (rewrite Hp86) in "Hpc".
  (* ---- +0x86: c.add a5,a5,a4 -- a5 = TRAMPOLINE + 0x9c ---- *)
  iApply (wp_cadd_s_sconf (mword_of_int (FR + 0x86)) Ra5 Ra4
            S9 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_86 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SA := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget S9 Ra5) (rget S9 Ra4))]> S9).
  assert (HSAa5 : rget SA Ra5 = uva 0x9c).
  { rgne. rewrite /SA upd_eq. rewrite HS9a5 HS9a4. exact fkr_tramp_userret. }
  assert (Hp88 : add_vec_int (mword_of_int (FR + 0x86) : mword 64) 2
                 = mword_of_int (FR + 0x88)) by pcw.
  iEval (rewrite Hp88) in "Hpc".
  (* ================================================================== *)
  (*  +0x88 .. +0x8c: MAKE_SATP's high bits.  THE WORD IS kvminithart's.  *)
  (* ================================================================== *)
  (* ---- +0x88: c.li a4,-1 ---- *)
  iApply (wp_cli_s_sconf (mword_of_int (FR + 0x88)) Ra4 (mword_of_int 63 : mword 6)
            (add_vec zero_reg (sign_extend' 64
               (sign_extend' 12 (mword_of_int 63 : mword 6))))
            SA (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl with "Hcg Hpc []").
  { iApply (fkr_88 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SB := <[Regidx Ra4 := regval_into_reg
                 (add_vec zero_reg (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))]> SA).
  assert (Hp8a : add_vec_int (mword_of_int (FR + 0x88) : mword 64) 2
                 = mword_of_int (FR + 0x8a)) by pcw.
  iEval (rewrite Hp8a) in "Hpc".
  (* ---- +0x8a: c.slli a4,a4,0x3f ---- *)
  iApply (wp_cslli_s_sconf (mword_of_int (FR + 0x8a)) (Regidx Ra4) Ra4
            (mword_of_int 63 : mword 6) SB (trap_res eb + av2)%nat false
            eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_8a with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SC := <[Regidx Ra4 := regval_into_reg
                 (shift_bits_left (rget SB Ra4)
                    (subrange_vec_dec (mword_of_int 63 : mword 6)
                       (Z.sub log2_xlen 1) 0))]> SB).
  assert (Hp8c : add_vec_int (mword_of_int (FR + 0x8a) : mword 64) 2
                 = mword_of_int (FR + 0x8c)) by pcw.
  iEval (rewrite Hp8c) in "Hpc".
  (* ---- +0x8c: c.or a0,a0,a4 -- MAKE_SATP, kvminithart's own word ---- *)
  assert (Hor : or_vec (rget SC Ra0) (rget SC Ra4)
                = kvi_satp_word (ud_root (pv_upt V'))).
  { assert (HSCa0 : rget SC Ra0
              = shift_bits_right
                  (zero_extend' 64 (concat_vec (ud_root (pv_upt V'))
                                      (zeros' 12 : mword 12)))
                  (subrange_vec_dec (mword_of_int 12 : mword 6)
                     (Z.sub log2_xlen 1) 0)).
    { rgne. rewrite /SC upd_ne; [| reg_neq]. rewrite /SB upd_ne; [| reg_neq].
      rewrite /SA upd_ne; [| reg_neq]. rewrite /S9 upd_ne; [| reg_neq].
      rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
      rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
      rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_eq. rgne.
      rewrite /S0 upd_eq. reflexivity. }
    assert (HSCa4 : rget SC Ra4
              = shift_bits_left
                  (add_vec zero_reg (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 63 : mword 6))))
                  (subrange_vec_dec (mword_of_int 63 : mword 6)
                     (Z.sub log2_xlen 1) 0)).
    { rgne. rewrite /SC upd_eq. rgne. rewrite /SB upd_eq. reflexivity. }
    rewrite HSCa0 HSCa4. unfold kvi_satp_word. reflexivity. }
  iApply (wp_cor_s_sconf (mword_of_int (FR + 0x8c)) Ra0 Ra0 Ra4
            (kvi_satp_word (ud_root (pv_upt V'))) SC (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) Hor with "Hcg Hpc []").
  { iEval (rewrite -Hc2 -Hc6). iApply (fkr_8c with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SD := <[Regidx Ra0 := regval_into_reg
                 (kvi_satp_word (ud_root (pv_upt V')))]> SC).
  assert (Hp8e : add_vec_int (mword_of_int (FR + 0x8c) : mword 64) 2
                 = mword_of_int (FR + 0x8e)) by pcw.
  iEval (rewrite Hp8e) in "Hpc".
  (* the process block, back in one piece *)
  iEval (rewrite Haddrpg) in "Hpgt".
  iDestruct ("Hpvback" $! (pv_upt V') ltac:(apply uptd_ext_sz_refl)
               with "Hsz Hpgt Hppt") as "Hpv".
  rewrite upd_upt_id.
  (* ================================================================== *)
  (*  +0x8e: c.jalr a5 -- into userret, and never back.                   *)
  (* ================================================================== *)
  assert (HSDa5 : rget SD Ra5 = uva 0x9c).
  { rgne. rewrite /SD upd_ne; [| reg_neq]. rewrite /SC upd_ne; [| reg_neq].
    rewrite /SB upd_ne; [| reg_neq]. rewrite -HSAa5. rgne. reflexivity. }
  iApply (wp_cjalr_s_sconf (mword_of_int (FR + 0x8e)) Ra5 Rra
            SD (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
            ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_8e with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (SE := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x8e) : mword 64) 2)]> SD).
  iEval (rewrite HSDa5 fkr_ret_pc) in "Hpc".
  (* ================================================================== *)
  (*  THE EXIT: the bundle taken apart into the loop's own premises.      *)
  (* ================================================================== *)
  iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
  (* [sconf] is destructured DIRECTLY, not through [sconf_priv_open]: the
     loop wants [mie]/[mideleg]/[menvcfg]/[cur_privilege] as loose cells,
     which the closer would re-park. *)
  iDestruct "Hsc" as "(#Hhw & #Hmin & Hprivc & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (msg) "(Hms & Hhalf & Htie & %Hmsg)".
  (* CLASS 1 + the park's half of the token exchange (tso-port leg M2):
     [Hctx] is bound out of the capability here and goes straight into the
     [ut_trap] this proof builds below -- forkret is the new thread's FIRST
     descent into the trap loop, so the residue it parks is its own, at its
     own (ambient) context.  See [UsertrapRes.ut_trap]'s note. *)
  iDestruct "Hcap" as "(Hstk & Hstr & Harm & Hctx & #Htc & #Hwit)".
  (* THE QUARTER'S VALUE IS NOT A DEGREE OF FREEDOM.  prepare_return leaves
     it existential because it never reads it; the arm it also hands back is
     at [false], and [sie_arm_half_agree] reads the live SIE off that index,
     so the half / quarter agreement pins it -- which is what makes the sret
     legal ([ut_exit_ms_ok]). *)
  iDestruct (sie_arm_half_agree false p msg with "Hhalf Harm") as %Hsie0.
  iDestruct (ghost_var_agree with "Hhalf Hq4") as %Hvb.
  rewrite Hsie0 in Hvb. rewrite -Hvb.
  iDestruct (sret_bits_agree _ _ _ _ with "Htie Hsret") as %[Hspp2 Hspie2].
  iAssert (sconf_msown msg) with "[Hms Hhalf Htie]" as "Hmsown".
  { rewrite /sconf_msown. iSplitL "Hms"; [iExact "Hms"|].
    iSplitL "Hhalf"; [iExact "Hhalf"|].
    iSplitL "Htie"; [iExact "Htie"|]. iPureIntro. exact Hmsg. }
  iDestruct (ut_exit_ms_ok msg with "Hmsown Hsret Hq4") as %Hretms.
  iDestruct "Hmsown" as "(Hms & Hhalf & Htie & _)".
  rewrite /sret_tie Hspp2 Hspie2.
  rewrite Hsie0.
  iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmask)".
  iDestruct "Hmenvx" as (menvcfg0') "(Hmenv & _ & _ & _ & _ & %Hmeq)".
  subst menvcfg0'.
  iDestruct "Hscause" as (scv) "Hscause".
  iDestruct "Hstval" as (stv) "Hstval".
  (* the three persistent per-hart pins the loop wants, copied out of the
     per-cpu bundle and put straight back *)
  iDestruct (cpu_own_csrs_open with "Hcpu") as "[Hcsrs Hcsback]".
  iDestruct "Hcsrs" as "(Hsscr & #Hmedlc & #Hmsec & #Hssec)".
  iDestruct ("Hcsback" with "[Hsscr]") as "Hcpu".
  { iFrame "Hmedlc Hmsec Hssec". iExact "Hsscr". }
  iPoseProof (hw_config_senvcfg with "Hhw") as "#Hsenvc".
  (* ---- the stack: the dead frame merges back into the free claim ---- *)
  assert (HSEsp : SE !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /SE upd_ne; [| reg_neq]. rewrite /SD upd_ne; [| reg_neq].
    rewrite /SC upd_ne; [| reg_neq]. rewrite /SB upd_ne; [| reg_neq].
    rewrite /SA upd_ne; [| reg_neq]. rewrite /S9 upd_ne; [| reg_neq].
    rewrite /S8 upd_ne; [| reg_neq]. rewrite /S7 upd_ne; [| reg_neq].
    rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
    rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
    rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq].
    rewrite /S0 upd_ne; [| reg_neq]. exact Hmfsp. }
  iEval (rewrite HSEsp) in "Hstk".
  iAssert (stack_own (KTR := KT1) ksp av) with "[Hstk Hf16]" as "Hstack".
  { rewrite Havsum.
    iApply (bi.equiv_entails_1_2 _ _ (stack_own_app (KTR := KT1) ksp 6 (trap_res eb + av2))).
    iSplitL "Hf16"; [iExact "Hf16" | iExact "Hstk"]. }
  (* ---- the trap-side residue, and the table it hands userret ---- *)
  iAssert (ut_trap p ksp av ∅)
    with "[Hstack Hstr Harm Hctx Hkptr Hhalf Hq4 Htie Hsret Hcpu Hclaim]" as "Htrap".
  { rewrite /ut_trap /ut_stack /ut_ghosts.
    iSplitL "Hstack". { iExact "Hstack". }
    iSplitL "Hstr". { iExact "Hstr". }
    iSplitL "Harm". { iExact "Harm". }
    iSplitL "Hctx". { iExact "Hctx". }
    iSplitL "Hkptr". { iExact "Hkptr". }
    iSplitL "Hhalf Hq4 Htie Hsret".
    { iSplitL "Hhalf". { iExact "Hhalf". }
      iSplitL "Hq4". { iExact "Hq4". }
      iSplitL "Htie". { iExact "Htie". }
      iExact "Hsret". }
    iSplitL "Hcpu". { iExact "Hcpu". }
    iExact "Hclaim". }
  iDestruct (ut_trap_tlb_open with "Htrap") as (kroot) "[Hkres Hparked]".
  iDestruct (fkr_kpt_of_res with "Hkres") as "[#Hkptinv Hkres]".
  (* ---- the address space, split off the block for the user tier ---- *)
  (* THE DESCRIPTOR IS RENORMALISED HERE, and it is the same move every
     round of the trap loop makes ([UsertrapRes.usertrap_res_bare_norm],
     [ProofUservec]'s exit).  [SpecUserretClosed.loop_ok] wants
     [ud_data = ud_pas], which nothing this side can say about a descriptor
     a caller (or, on the boot arm, kexec) chose -- and nothing this side
     READS it: [ProcPtOwn.proc_pt_norm] and [ProcInv.proc_priv_nopt_upt_irrel]
     are both [⊣⊢].  So the block and the table are re-keyed on [ud_norm]
     once, and the equation is [ud_norm_pas] rather than a premise. *)
  iEval (rewrite proc_priv_split_pt) in "Hpv".
  iDestruct "Hpv" as "[Hpnopt Hpt]".
  iEval (rewrite HuptV') in "Hpt".
  iEval (rewrite proc_pt_norm) in "Hpt".
  (* the three side conditions are [f_equal] on [HuptV'] up to the iota step
     [ud_root (ud_norm P) = ud_root P]; supplied as terms rather than as
     tactics so nothing depends on how [set] below folds them. *)
  iEval (rewrite (proc_priv_nopt_upt_irrel γf p pid V' (ud_norm (pv_upt V))
                    (f_equal ud_root HuptV') (f_equal ud_tfp HuptV')
                    (f_equal ud_um HuptV'))) in "Hpnopt".
  set (pt := ud_norm (pv_upt V)).
  iEval (rewrite proc_pt_split) in "Hpt".
  iDestruct "Hpt" as "[[%Hptwf Hufr] Hdata]".
  assert (Hnorm : ud_data pt = ud_pas pt) by exact (ud_norm_pas (pv_upt V)).
  destruct Hptwf as (Hmapwf & Haccwf & Hpv1 & Hpv2 & Hpv3).
  assert (Hptwf : proc_pt_wf pt)
    by exact (conj Hmapwf (conj Haccwf (conj Hpv1 (conj Hpv2 Hpv3)))).
  (* the pages, RE-KEYED by user virtual address: the same [↦ₚ] cells the
     kernel held page-indexed, which is what the user tier now takes *)
  iEval (rewrite (proc_pt_own_umem pt Hmapwf Hpv2)) in "Hdata".
  assert (Hcov : uva_pa_inj pt) by exact (uva_pa_inj_of_wf pt Hmapwf Hpv2).
  (* ---- and the residue, handed to the caller's wand ---- *)
  iAssert (forkret_yield (CID := CIDf) γf p ksp pid av (upd_upt V' pt))
    with "[Hparked Hpnopt]" as "Hyld".
  { rewrite /forkret_yield.
    iSplitL "Hparked"; [iExact "Hparked" | iExact "Hpnopt"]. }
  iDestruct (ut_tfk_upd_upt (CID := CIDf) ksp V' pt with "Htfk") as "#Htfk'".
  iDestruct ("Hyield" $! CIDf XI pt (upd_upt V' pt)
               with "[%] [%] [%] Htfk' Hdone HW Htc Hyld")
    as "Hures"; [reflexivity | exact Hnorm | exact Hptwf |].
  (* ---- the config record for this round ---- *)
  assert (HSEa0 : tp_pin SE !!! Regidx (mword_of_int 10)
                  = kvi_satp_word (ud_root pt)).
  { rewrite /tp_pin upd_ne; [| reg_neq]. rewrite /SE upd_ne; [| reg_neq].
    rewrite /SD upd_eq HuptV'. reflexivity. }
  iApply (UC.wp_userret_closed (CID := CIDf)
            (loop_ucfg mdv0 Hmask) pt kroot j ksp (tp_pin SE)
            (kvi_satp_word (ud_root pt)) msg (mepc_val epc) scv stv
            (loop_ok_loop_ucfg mdv0 Hmask pt Hnorm Hptwf)
            Hjlt
            Hretms Hmapwf HSEa0
            (conj (kvi_satp_mode _) (conj (kvi_satp_asid _) (kvi_satp_ppn _)))
            Hcov Haccwf
            with "Htext Hhw Hmin Hwire Hclaimmap Hkptinv Hhs Hprivc Hms Hmie
                 Hmdl Hmenv Hsenvc Hsepc Hscause Hstval Hstvec Hmedlc Hmsec
                 Hssec Hkres Hufr Hdata Hpc Hfile Hures").
Qed.

(* ===================================================================== *)
(*  THE BOOT ARM: +0x14 to +0x62, i.e. all of [if (first)].               *)
(* ===================================================================== *)
(* NOT PROVED YET, and the obstruction is NOT in this file.

     fsinit(ROOTDEV);
     __atomic_store_n(&first, 0, __ATOMIC_RELEASE);
     p->trapframe->a0 = kexec("/init", (char *[]){"/init", 0});
     if (p->trapframe->a0 == -1) panic("exec");

   Every resource the arm spends is already here -- that is what the four
   [FirstTok] rows below are, and [FirstTok.first_fsinit_open] hands them
   out in [SpecFsinit]'s own premise order.  What is missing is that
   forkret reaches fsinit WITH INTERRUPTS OFF.  This revision's scheduler
   runs [intr_on(); intr_off();] before [acquire(&p->lock)], so push_off
   records [intena = 0] and forkret's own [release] at +0x10 does not
   re-enable; the arm therefore runs at [eb = false] and at [b = false].
   [SpecFsinit], [SpecInitlog], [SpecIreclaim], [SpecKexec], [SpecNamei],
   [SpecNamex] and [SpecDirlookup] all still carry [eb = true ->] --
   exactly the ~25 contracts claude-notes/completed/eb-generic-sweep.md's
   closing section lists as "reached from a syscall or from boot with an
   enabled base", on the strength of an assumption this arm refutes.

   So the prerequisite is one more round of that sweep over those seven
   functions -- drop the premise, thread [trap_csrs_ext eb] /
   [cpu_claim_ext eb pj] in and out -- and that file is the recipe.  This
   contract already holds the complement (it is [Hext] / [Hcx] below, the
   [_ext] halves [IntrDefs.arm_pay_ext_split] produced at the release), so
   nothing here or in [SpecForkret.v] changes when the sweep lands.

   The statement is exactly the goal at +0x14 on the arm the token's boot
   disjunct selects, so proving it is a matter of writing the walk. *)
(* ---- the trapframe page is a real page: the fact [pt_node_claim_from_static]
       needs before the physical trapframe words can be read as MEMORY.  It
       rides inside the descriptor's well-formedness, so [proc_priv] has it.
       ([ProofSyscall.sysc_tfp_valid] is the same lemma; restated here so the
       forkret cone does not depend on the syscall proof.) ---- *)
Lemma fkr_tfp_valid
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
  proc_priv γf pa pid V -∗ ⌜page_valid (page_base (ud_tfp (pv_upt V)))⌝.
Proof.
  iIntros "[(_ & _ & _ & _ & Hpt & _) _]".
  rewrite /proc_pt_at. iDestruct "Hpt" as "(_ & _ & Hptt)".
  iDestruct (proc_pt_wf_get with "Hptt") as "%Hwf".
  iPureIntro. exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
Qed.

(* ---- [112(a5)] with a5 = p->trapframe is trapframe word 14, which is
       [tf_arg_idx 0] -- the a0 slot.  Same displacement syscall's
       [sd a0,112(s2)] uses, and the same lemma. ---- *)
Lemma fkr_tf_addr_112 (tfp : mword 44) :
  add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 112 : mword 12))
  = tf_pa tfp (8 * Z.of_nat (tf_arg_idx 0)).
Proof.
  assert (Hse : (sign_extend' 64 (mword_of_int 112 : mword 12) : mword 64)
                = (mword_of_int 112 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hse.
  rewrite (tf_pa_eq_pa_add8 tfp (tf_arg_idx 0) ltac:(vm_compute; lia)).
  rewrite /pa_add /tf_arg_idx. f_equal.
Qed.

Lemma fkr_boot
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (W : iProp Σ) (j : nat) (γs : list gname) (γl γf : gname)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (mr : regfile) (av av2 : nat) (eb : bool) :
  let p   : mword 64 := proc_addr j in
  let ksp : mword 64 := add_vec ks (mword_of_int 4096) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_kexec <= av2)%nat ->
  av = (6 + (trap_res eb + av2))%nat ->
  mr !!! Regidx csp_rs1 = pa_stk ksp 6 ->
  (* the frame pointer: the argv vector goes into this frame's bottom two
     slots, at -48(s0) and -40(s0) *)
  mr !!! Regidx Rs0 = ksp ->
  mr !!! Regidx Rs1 = p ->
  kernel_text -∗
  wire_inv -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  pc_is (mword_of_int (FR + 0x14) : mword 64) -∗
  procs_inv γs -∗
  sie_cap_gpr KT1 mr av2 eb p -∗
  cpu_own 0%nat eb p eb ∅ -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb p -∗
  is_kstack p ks -∗
  (* the frame, whole -- handed straight on to [fkr_tail]; the boot arm
     WRITES two of its slots (the argv vector kexec is passed) *)
  stack_own (KTR := KT1) ksp 6 -∗
  (* the block WITHOUT its token: the boot arm spends the token's contents
     and rebuilds it, at the steady arm, out of what fsinit returns *)
  proc_priv_nocwd γf p pid V -∗
  cwd_ref (pv_cwd V) -∗
  (* ...and the token's boot disjunct, opened *)
  first_addr ↦₄ (mword_of_int 1 : mword 32) -∗
  first_boot_persist -∗
  kalloc_avail fsc_kpages None -∗
  first_fsinit -∗
  (* the closer takes [first_done] and THIS ARM MINTS BOTH ITS HALVES at the
     release store at +0x38: the [c.sw] discards [first_addr ↦₄ 1] to
     [↦₄□ 0], and [fs_ready_establish] seals the file system.  So unlike
     [fkr_tail], the boot arm does not take it as a premise -- it produces
     the thing it owes. *)
  W -∗
  (* THE RESIDUE CLOSER, by name: [SpecForkret.forkret_closer] is the wand
     this used to spell out.  It is ~13 % of the Iris context of every step
     of this walk, and a proofmode step's term carries the whole context
     twice -- see that definition's header. *)
  forkret_closer (fun (h : CpuId) (Xc : CurCtx) => usertrap_res_bare (CID := h) (XI := Xc))
                 W γf p ksp pid av -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros p ksp Hjlt Hgl Hkx Havsum Hmrsp Hmrs0 Hmrs1.
  pose proof Hkx as Hkx'.
  (* fsinit's 88 sits under kexec's 184, which is what this arm is budgeted
     at; both are [Notation]s for literals, so [lia] sees them directly. *)
  assert (Hav2fs : (K_fsinit <= av2)%nat) by lia.
  iIntros "#Htext #Hwire #Hclaimmap Hpc #Hpinv Hcg Hcpu Hextc Hclmc #Hks
           Hf16 Hpnc Hcwd Hf1 #Hbp Hka Hfsi HW Hyield".
  iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hebb.
  (* ================================================================== *)
  (*  +0x14 .. +0x24: [if (first)] -- TAKEN, because the token is the      *)
  (*  exclusive arm and the cell reads 1.                                  *)
  (* ================================================================== *)
  (* ---- +0x14: auipc a5,0x9 ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x14)) Ra5
            (mword_of_int 9 : mword 20) mr av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_14 with "Htext"). }
  iIntros (CIDb1 Hkb1) "Hcg Hpc".
  set (B1 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x14) : mword 64)
                    (auipc_off (mword_of_int 9 : mword 20)))]> mr).
  assert (Hbp18 : add_vec_int (mword_of_int (FR + 0x14) : mword 64) 4
                  = mword_of_int (FR + 0x18)) by pcw.
  iEval (rewrite Hbp18) in "Hpc".
  (* ---- +0x18: addi a5,a5,-1712 -- a5 = &first ---- *)
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x18)) Ra5 Ra5
            (mword_of_int 2384 : mword 12) B1 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_18 with "Htext"). }
  iIntros (CIDb2 Hkb2) "Hcg Hpc".
  set (B2 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget B1 Ra5)
                    (sign_extend' 64 (mword_of_int 2384 : mword 12)))]> B1).
  assert (HB2a5 : rget B2 Ra5 = first_addr).
  { rgne. rewrite /B2 upd_eq. rgne. rewrite /B1 upd_eq. exact fkr_first_addr. }
  assert (Hbp1c : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 4
                  = mword_of_int (FR + 0x1c)) by pcw.
  iEval (rewrite Hbp1c) in "Hpc".
  (* ---- +0x1c: c.lw a5,0(a5) -- the read that decides the branch.  The
         token's arm says 1, so the [c.beqz] below FALLS THROUGH. ---- *)
  assert (Hbfaddr : add_vec (rget B2 Ra5)
                      (sign_extend' 64 (mword_of_int 0 : mword 12)) = first_addr)
    by (rewrite HB2a5; apply addv_sext0).
  iEval (rewrite -Hbfaddr) in "Hf1".
  iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x1c)) Ra5 Ra5
            (mword_of_int 0 : mword 12) B2 av2 (mword_of_int 1 : mword 32) eb
            ltac:(vm_compute; discriminate) ltac:(rdok)
            with "Hcg Hpc [] Hf1").
  { iApply (fkr_1c with "Htext"). }
  iIntros (CIDb3 Hkb3) "Hcg Hpc Hf1".
  iEval (rewrite Hbfaddr) in "Hf1".
  set (B3 := <[Regidx Ra5 := regval_into_reg
                 (sign_extend' 64 (mword_of_int 1 : mword 32))]> B2).
  assert (Hbp1e : add_vec_int (mword_of_int (FR + 0x1c) : mword 64) 2
                  = mword_of_int (FR + 0x1e)) by pcw.
  iEval (rewrite Hbp1e) in "Hpc".
  (* ---- +0x1e: fence r,rw -- the acquire barrier, state-preserving ---- *)
  iApply (wp_fence_gen_s_sconf (mword_of_int (FR + 0x1e))
            (mword_of_int 0 : mword 4) (mword_of_int 2 : mword 4)
            (mword_of_int 3 : mword 4) zreg zreg B3 av2 eb
            with "Hcg Hpc []").
  { iApply (fkr_1e with "Htext"). }
  iIntros (CIDb4 Hkb4) "Hcg Hpc".
  assert (Hbp22 : add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 4
                  = mword_of_int (FR + 0x22)) by pcw.
  iEval (rewrite Hbp22) in "Hpc".
  (* ---- +0x22: sext.w a5,a5 ---- *)
  iApply (wp_caddiw_s_sconf (mword_of_int (FR + 0x22)) Ra5
            (mword_of_int 0 : mword 6) B3 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_22 with "Htext"). }
  iIntros (CIDb5 Hkb5) "Hcg Hpc".
  set (B4 := <[Regidx Ra5 := regval_into_reg
                 (sign_extend' 64 (subrange_vec_dec
                    (add_vec (rget B3 Ra5)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B3).
  assert (HB4a5 : eq_vec (rget B4 Ra5) zero_reg = false).
  { rgne. rewrite /B4 upd_eq. rgne. rewrite /B3 upd_eq.
    vm_compute. reflexivity. }
  assert (Hbp24 : add_vec_int (mword_of_int (FR + 0x22) : mword 64) 2
                  = mword_of_int (FR + 0x24)) by pcw.
  iEval (rewrite Hbp24) in "Hpc".
  (* ---- +0x24: c.beqz a5, +0x64 -- NOT taken: the arm is live ---- *)
  iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FR + 0x24))
            (mword_of_int 32 : mword 8) (Cregidx (mword_of_int 7)) Ra5
            B4 av2 eb ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; discriminate) HB4a5
            with "Hcg Hpc []").
  { iApply (fkr_24 with "Htext"). }
  iIntros (CIDb6 Hkb6) "Hcg Hpc".
  assert (Hbp26 : add_vec_int (mword_of_int (FR + 0x24) : mword 64) 2
                  = mword_of_int (FR + 0x26)) by pcw.
  iEval (rewrite Hbp26) in "Hpc".
  (* ================================================================== *)
  (*  +0x26 .. +0x28: fsinit(ROOTDEV).                                   *)
  (* ================================================================== *)
  (* the token's persistent half, opened once: seventeen rows, and every
     one of them is a premise of fsinit, of kexec, or of the seal. *)
  iEval (rewrite /first_boot_persist) in "Hbp".
  iDestruct "Hbp" as "(_ & #Hkdata & #Hpenv & %Hpkc & #Hbio & #Hseam & #Hgen &
                       #Hdevi & #Hdisk & #Hitb2 & #Hitbl & #Hesc & #Hslks &
                       #Hireg & #Hbits & #Hkmem & %Hgeom)".
  iDestruct "Hdisk" as (pd pav pu) "[#Hdgeom #Hdlock]".
  (* fsinit's (c)/(d)/(e)/(f) and its log geometry are all projections of
     [FsReady.fs_geom_ok], which is why the token carries the record and not
     eleven loose hypotheses. *)
  pose proof (fgo_rootdev Hgeom) as Hdev.
  pose proof (fgo_nib_pos Hgeom) as Hnib0.
  pose proof (fgo_loggeom Hgeom) as Hlg.
  pose proof (fgo_ist_nn Hgeom) as Hist0.
  pose proof (fgo_covbelow Hgeom) as Hcovb.
  pose proof (fgo_iblocks Hgeom) as Hiregb.
  pose proof (fgo_nin_lo Hgeom) as Hn1.
  pose proof (fgo_nin_hi Hgeom) as Hnnib.
  pose proof (fgo_nin_31 Hgeom) as Hn31.
  pose proof (fgo_size Hgeom) as Hsize.
  pose proof (fgo_bm_nn Hgeom) as Hbm0.
  pose proof (fgo_bm_cov Hgeom) as Hbmcov.
  pose proof (fgo_bm_out Hgeom) as Hbmlog.
  (* the exclusive half, in fsinit's own premise order *)
  iDestruct (first_fsinit_open with "Hfsi") as (dk sb vlock v_start v_dev v_nc v_n
                                                vname vcpu sb_old)
    "(%Hpures & Hmirf & Hlfree & Hb1 & Hsbraw & _ & Hboot & _ &
      Hlock0 & Hlname & Hlcpu & Hlstart & Hldev & Hlout & Hlcmt & Hlnc & Hlhn &
      Hlhblk & Hauths & Hdirty & Hhdr & Hlslots & Hsl35 & Hirs2 & Hrem)".
  destruct Hpures as [[v_magic [v_nblocks [v_nlog [Himg Hmagic]]]]
                      [Hhdr0 [H1cov H1log]]].
  (* the era's two readings of one image (durable-disk 1a): the boot mint
     built [L] from the era's disk, which is the same disk the era's mirror
     was born at.  Threaded straight through fsinit into initlog. *)
  iDestruct "Hauths" as (L D) "(%HLdk & HauthL & HauthD)".
  (* fsinit borrows one reference unit and gives it back; kexec wants two,
     which is why the token carries two. *)
  iDestruct (iref_slots_split 1 1 with "Hirs2") as "[Hirs1 Hirs1b]".
  (* the process block, minus the file layer, is what the fs cone takes *)
  iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
  iDestruct "Hpnc" as "[Hpbare Hofiles]".
  (* ---- +0x26: c.li a0,1 -- ROOTDEV ---- *)
  iApply (wp_cli_s_sconf (mword_of_int (FR + 0x26)) Ra0
            (mword_of_int 1 : mword 6)
            (sign_extend' 64 (mword_of_int 1 : mword 32)) B4 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) fkr_rootdev
            with "Hcg Hpc []").
  { iApply (fkr_26 with "Htext"). }
  iIntros (CIDb7 Hkb7) "Hcg Hpc".
  set (B5 := <[Regidx Ra0 := regval_into_reg
                 (sign_extend' 64 (mword_of_int 1 : mword 32))]> B4).
  assert (Hbp28 : add_vec_int (mword_of_int (FR + 0x26) : mword 64) 2
                  = mword_of_int (FR + 0x28)) by pcw.
  iEval (rewrite Hbp28) in "Hpc".
  (* ---- +0x28: jal ra, fsinit ---- *)
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x28)) Rra
            (mword_of_int 7182 : mword 21) B5 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc []").
  { iApply (fkr_28 with "Htext"). }
  iIntros (CIDb8 Hkb8) "Hcg Hpc".
  set (B6 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x28) : mword 64) 4)]> B5).
  assert (HB6ra : B6 !!! Regidx Rra = mword_of_int (FR + 0x2c))
    by (rewrite /B6 upd_eq; pcw).
  assert (HB6a0 : B6 !!! Regidx Ra0 = (sign_extend' 64 icfg_dev : mword 64)).
  { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_eq. rewrite Hdev.
    reflexivity. }
  assert (HB6sp : B6 !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
    rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
    rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq].
    exact Hmrsp. }
  assert (HB6s1 : B6 !!! Regidx Rs1 = p).
  { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
    rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
    rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq].
    exact Hmrs1. }
  (* the frame pointer, carried across the same six updates: the argv
     vector two calls from here is written at -48(s0) / -40(s0). *)
  assert (HB6s0 : B6 !!! Regidx Rs0 = ksp).
  { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
    rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
    rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq].
    exact Hmrs0. }
  iEval (rewrite fkr_fsinit_tgt) in "Hpc".
  iDestruct (cpu_own_transport CID CIDb8 0%nat eb p eb
               ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
  iDestruct (trap_csrs_ext_transport CID CIDb8 eb p
               ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
  iDestruct (cpu_claim_ext_transport CID CIDb8 eb p
               ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
  iApply (FS.wp_fsinit_sconf γs j γl fsc_uart fsc_disk fsc_dlock pd pav pu
            fsc_bio fsc_fs fsc_ireg fsc_ic fsc_itlock fsc_printk
            fsc_cov fsc_logst fsc_bmapstart icfg_ist fsc_ninodes icfg_nib
            fsc_size icfg_dev
            v_magic (mword_of_int fsc_size) v_nblocks
            (mword_of_int fsc_ninodes) v_nlog (mword_of_int fsc_logst)
            (mword_of_int icfg_ist) (mword_of_int fsc_bmapstart)
            (FsCrash.fs_blocks dk 1) sb_old
            (FsCrash.fs_blocks dk (log_hdr_bno fsc_logst))
            (FsCrash.mirror_of (FsCrash.fs_blocks dk)) L D
            vlock vname vcpu v_start v_dev v_nc v_n
            pid (DfracOwn 1) B6 av2 eb eb ∅ V
            Hav2fs Hlg H1cov H1log Himg Hmagic eq_refl eq_refl eq_refl eq_refl
            Hn1 Hnnib Hn31 eq_refl eq_refl Hdev Hnib0
            Hist0 Hiregb Hsize Hbm0 Hbmcov Hbmlog Hcovb Hhdr0 HLdk Hpkc Hjlt Hgl
            HB6a0 ltac:(lkbelow)
            with "Hcg Hcpu Hextc Hclmc Htext Hkdata Hpc Hpenv Hbio Hseam Hgen
                  Hmirf Hlfree Hb1 Hsbraw Hireg Hboot Hitb2 Hitbl Hesc Hslks
                  Hbits Hlock0 Hlname Hlcpu Hlstart Hldev Hlout Hlcmt Hlnc
                  Hlhn Hlhblk HauthL HauthD Hdirty Hhdr Hlslots Hpbare Hpinv
                  Hdevi Hdgeom Hdlock Hsl35 Hirs1").
  all: try lkbelow.
  iIntros (CIDf1 Hkf1 mf1)
    "%Hcsf1 Hcg Hcpu Hextc Hclmc Hpc Hpbare Hmg Hsz Hnb Hni Hnl Hls Hist Hbms
     Hb1 #Hlctx Hsl3 Hirs1 Hboot".
  assert (Hpcf1 : ret_pc (B6 !!! Regidx Rra : mword 64)
                  = mword_of_int (FR + 0x2c)) by (rewrite HB6ra; pcw).
  iEval (rewrite Hpcf1) in "Hpc".
  assert (Hf1sp : mf1 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup Hcsf1 csp_rs1 ltac:(vm_compute; reflexivity));
        exact HB6sp).
  assert (Hf1s1 : mf1 !!! Regidx Rs1 = p)
    by (rewrite (callee_saved_lookup Hcsf1 Rs1 ltac:(vm_compute; reflexivity));
        exact HB6s1).
  assert (Hf1s0 : mf1 !!! Regidx Rs0 = ksp)
    by (rewrite (callee_saved_lookup Hcsf1 Rs0 ltac:(vm_compute; reflexivity));
        exact HB6s0).
  (* ================================================================== *)
  (*  +0x2c .. +0x38: [first = 0], with release ordering.                *)
  (* ================================================================== *)
  (* ---- +0x2c: auipc a5,0x9 -- a5 was clobbered by the call ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x2c)) Ra5
            (mword_of_int 9 : mword 20) mf1 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_2c with "Htext"). }
  iIntros (CIDb9 Hkb9) "Hcg Hpc".
  set (C1 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x2c) : mword 64)
                    (auipc_off (mword_of_int 9 : mword 20)))]> mf1).
  assert (Hcp30 : add_vec_int (mword_of_int (FR + 0x2c) : mword 64) 4
                  = mword_of_int (FR + 0x30)) by pcw.
  iEval (rewrite Hcp30) in "Hpc".
  (* ---- +0x30: addi a5,a5,-1736 -- a5 = &first ---- *)
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x30)) Ra5 Ra5
            (mword_of_int 2360 : mword 12) C1 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_30 with "Htext"). }
  iIntros (CIDb10 Hkb10) "Hcg Hpc".
  set (C2 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget C1 Ra5)
                    (sign_extend' 64 (mword_of_int 2360 : mword 12)))]> C1).
  assert (HC2a5 : rget C2 Ra5 = first_addr).
  { rgne. rewrite /C2 upd_eq. rgne. rewrite /C1 upd_eq. exact fkr_first_addr2. }
  assert (Hcp34 : add_vec_int (mword_of_int (FR + 0x30) : mword 64) 4
                  = mword_of_int (FR + 0x34)) by pcw.
  iEval (rewrite Hcp34) in "Hpc".
  (* ---- +0x34: fence rw,w -- the release barrier ---- *)
  iApply (wp_fence_gen_s_sconf (mword_of_int (FR + 0x34))
            (mword_of_int 0 : mword 4) (mword_of_int 3 : mword 4)
            (mword_of_int 1 : mword 4) zreg zreg C2 av2 eb
            with "Hcg Hpc []").
  { iApply (fkr_34 with "Htext"). }
  iIntros (CIDb11 Hkb11) "Hcg Hpc".
  assert (Hcp38 : add_vec_int (mword_of_int (FR + 0x34) : mword 64) 4
                  = mword_of_int (FR + 0x38)) by pcw.
  iEval (rewrite Hcp38) in "Hpc".
  (* ---- +0x38: sw zero,0(a5) -- the one-shot is spent ---- *)
  assert (Hcfaddr : add_vec (rget C2 Ra5)
                      (sign_extend' 64 (mword_of_int 0 : mword 12)) = first_addr)
    by (rewrite addv_sext0; exact HC2a5).
  iEval (rewrite -Hcfaddr) in "Hf1".
  iApply (wp_sw_zero_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x38)) Ra5
            (mword_of_int 0 : mword 12) C2 av2 (mword_of_int 1 : mword 32) eb
            with "Hcg Hpc [] Hf1").
  { iApply (fkr_38 with "Htext"). }
  iIntros (CIDb12 Hkb12) "Hcg Hpc Hf1".
  iEval (rewrite Hcfaddr) in "Hf1".
  (* PERSIST IMMEDIATELY, not on the way out.  [FirstTok]'s steady arm is
     [first_addr ↦₄□ 0], and every later reader -- including this very
     process, on its next trip through forkret -- needs the DISCARDED form.
     Discarding here is also what makes the two arms of the token provably
     exclusive from now on ([first_tok_boot_excl]). *)
  iMod (word4_pointsto_persist with "Hf1") as "#Hfirst0".
  assert (Hcp3c : add_vec_int (mword_of_int (FR + 0x38) : mword 64) 4
                  = mword_of_int (FR + 0x3c)) by pcw.
  iEval (rewrite Hcp3c) in "Hpc".
  (* ================================================================== *)
  (*  THE SEAL: the file system exists, and the token's steady arm with it. *)
  (* ================================================================== *)
  (* the four cells [FsReady.fs_sb_cells] wants are DISCARDED, not owned:
     they are read-only for the lifetime of the boot, and kexec takes its
     two at whatever fraction the caller has. *)
  iMod (word4_pointsto_persist with "Hni") as "#Hni".
  iMod (word4_pointsto_persist with "Hist") as "#Hist".
  iMod (word4_pointsto_persist with "Hsz") as "#Hsz".
  iMod (word4_pointsto_persist with "Hbms") as "#Hbms".
  iAssert (fs_sb_cells) as "#Hsbc".
  { rewrite /fs_sb_cells. iFrame "Hni Hist Hsz Hbms". }
  iDestruct (first_persist_pre with "[] Hka Hlctx Hsbc") as "Hpre".
  (* THE BUNDLE IS BUILT ROW BY ROW, NOT FRAMED (claude-notes/optimization.md,
     "when every conjunct is definition-valued").  A named [iFrame] over these
     seventeen rows still searches the GOAL once per name, and the goal's rows
     are [bio_ctx], [ic_escrows], [is_lock] over [disk_res]/[kmem_res] -- each
     match attempt a conversion over a big resource.  Measured 62.7 s here;
     the [iSplitR]/[iExact] chain in the bundle's own conjunct order is a
     syntactic check per row.  The assert has an EMPTY spatial context (the
     ["[]"] above), so every row is [iSplitR]. *)
  { rewrite /first_boot_persist.
    iSplitR; [iExact "Htext" |].
    iSplitR; [iExact "Hkdata" |].
    iSplitR; [iExact "Hpenv" |].
    iSplitR; [iPureIntro; exact Hpkc |].
    iSplitR; [iExact "Hbio" |].
    iSplitR; [iExact "Hseam" |].
    iSplitR; [iExact "Hgen" |].
    iSplitR; [iExact "Hdevi" |].
    iSplitR; [iExists pd, pav, pu;
              iSplitR; [iExact "Hdgeom" | iExact "Hdlock"] |].
    iSplitR; [iExact "Hitb2" |].
    iSplitR; [iExact "Hitbl" |].
    iSplitR; [iExact "Hesc" |].
    iSplitR; [iExact "Hslks" |].
    iSplitR; [iExact "Hireg" |].
    iSplitR; [iExact "Hbits" |].
    iSplitR; [iExact "Hkmem" |].
    iPureIntro; exact Hgeom. }
  iMod (fs_ready_establish with "Hpre Hboot") as "#Hfsr".
  (* the token, rebuilt at its steady arm -- and with it the whole process
     block, which every later step (kexec, prepare_return, the residue) takes
     as [proc_priv]. *)
  iAssert (first_done) as "#Hdone".
  { rewrite /first_done. iFrame "Hfirst0 Hfsr". }
  iDestruct (first_tok_of_done with "Hdone") as "#Hftok".
  (* ================================================================== *)
  (*  +0x3c .. +0x52: kexec("/init", (char *[]){"/init", 0}).            *)
  (*                                                                     *)
  (*  The argv vector is a COMPOUND LITERAL, so gcc materialises it in    *)
  (*  forkret's OWN frame -- at -48(s0) and -40(s0), the bottom two of    *)
  (*  the six slots the prologue carved out.  Those two are dead          *)
  (*  otherwise (ra/s0/s1 take three), so the arm spends them and still   *)
  (*  hands [fkr_tail] the run whole.                                     *)
  (* ================================================================== *)
  (* ---- +0x3c: auipc a5,0x6 ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x3c)) Ra5
            (mword_of_int 6 : mword 20) C2 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_3c with "Htext"). }
  iIntros (CIDb13 Hkb13) "Hcg Hpc".
  set (D1 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x3c) : mword 64)
                    (auipc_off (mword_of_int 6 : mword 20)))]> C2).
  assert (Hdp40 : add_vec_int (mword_of_int (FR + 0x3c) : mword 64) 4
                  = mword_of_int (FR + 0x40)) by pcw.
  iEval (rewrite Hdp40) in "Hpc".
  (* ---- +0x40: addi a5,a5,2104 -- a5 = the "/init" literal ---- *)
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x40)) Ra5 Ra5
            (mword_of_int 2104 : mword 12) D1 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_40 with "Htext"). }
  iIntros (CIDb14 Hkb14) "Hcg Hpc".
  set (D2 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget D1 Ra5)
                    (sign_extend' 64 (mword_of_int 2104 : mword 12)))]> D1).
  assert (HD2a5 : rget D2 Ra5 = (mword_of_int fkr_init_path : mword 64)).
  { rgne. rewrite /D2 upd_eq. rgne. rewrite /D1 upd_eq. exact fkr_init_path_addr. }
  assert (HD2s0 : rget D2 Rs0 = ksp).
  { rgne. rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq].
    rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [| reg_neq].
    exact Hf1s0. }
  assert (HD2sp : D2 !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq].
    rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [| reg_neq].
    exact Hf1sp. }
  assert (HD2s1 : D2 !!! Regidx Rs1 = p).
  { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq].
    rewrite /C2 upd_ne; [| reg_neq]. rewrite /C1 upd_ne; [| reg_neq].
    exact Hf1s1. }
  assert (Hdp44 : add_vec_int (mword_of_int (FR + 0x40) : mword 64) 4
                  = mword_of_int (FR + 0x44)) by pcw.
  iEval (rewrite Hdp44) in "Hpc".
  (* ---- the two slots the vector goes into, carved off the frame ---- *)
  iDestruct (stack_own_split_1 (KTR := KT1) ksp 4 6 ltac:(lia) with "Hf16") as "[Hf14 Hf2]".
  iEval (change (6 - 4)%nat with 2%nat) in "Hf2".
  iDestruct (stack_own_2_elim (KTR := KT1) (pa_stk ksp 4) with "Hf2") as (wA wB) "[HwA HwB]".
  assert (Hslot5 : pa_stk (pa_stk ksp 4) 1 = pa_stk ksp 5)
    by (rewrite pa_stk_assoc; reflexivity).
  assert (Hslot6 : pa_stk (pa_stk ksp 4) 2 = pa_stk ksp 6)
    by (rewrite pa_stk_assoc; reflexivity).
  iEval (rewrite Hslot5) in "HwA".
  iEval (rewrite Hslot6) in "HwB".
  assert (Hsd0 : add_vec (rget D2 Rs0) (sign_extend' 64 (mword_of_int 4048 : mword 12))
                 = pa_stk ksp 6)
    by (rewrite HD2s0; exact (fkr_argv0_slot ksp)).
  assert (Hsd1 : add_vec (rget D2 Rs0) (sign_extend' 64 (mword_of_int 4056 : mword 12))
                 = pa_stk ksp 5)
    by (rewrite HD2s0; exact (fkr_argv1_slot ksp)).
  (* ---- +0x44: sd a5,-48(s0) -- argv[0] = "/init" ---- *)
  iEval (rewrite -Hsd0) in "HwB".
  iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (FR + 0x44)) Ra5 Rs0
            (mword_of_int 4048 : mword 12) D2 av2 wB eb with "Hcg Hpc [] HwB").
  { iApply (fkr_44 with "Htext"). }
  iIntros (CIDb15 Hkb15) "Hcg Hpc HwB".
  iEval (rewrite Hsd0 HD2a5) in "HwB".
  assert (Hdp48 : add_vec_int (mword_of_int (FR + 0x44) : mword 64) 4
                  = mword_of_int (FR + 0x48)) by pcw.
  iEval (rewrite Hdp48) in "Hpc".
  (* ---- +0x48: sd zero,-40(s0) -- argv[1] = 0, the terminator ---- *)
  iEval (rewrite -Hsd1) in "HwA".
  iApply (wp_sd_zero_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (FR + 0x48)) Rs0
            (mword_of_int 4056 : mword 12) D2 av2 wA eb with "Hcg Hpc [] HwA").
  { iApply (fkr_48 with "Htext"). }
  iIntros (CIDb16 Hkb16) "Hcg Hpc HwA".
  iEval (rewrite Hsd1) in "HwA".
  assert (Hzr : (zero_reg : mword 64) = (mword_of_int 0 : mword 64)) by pcw.
  iEval (rewrite Hzr) in "HwA".
  assert (Hdp4c : add_vec_int (mword_of_int (FR + 0x48) : mword 64) 4
                  = mword_of_int (FR + 0x4c)) by pcw.
  iEval (rewrite Hdp4c) in "Hpc".
  (* ---- +0x4c: addi a1,s0,-48 -- a1 = &argv[0] ---- *)
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x4c)) Ra1 Rs0
            (mword_of_int 4048 : mword 12) D2 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_4c with "Htext"). }
  iIntros (CIDb17 Hkb17) "Hcg Hpc".
  set (D3 := <[Regidx Ra1 := regval_into_reg
                 (add_vec (rget D2 Rs0)
                    (sign_extend' 64 (mword_of_int 4048 : mword 12)))]> D2).
  assert (Hdp50 : add_vec_int (mword_of_int (FR + 0x4c) : mword 64) 4
                  = mword_of_int (FR + 0x50)) by pcw.
  iEval (rewrite Hdp50) in "Hpc".
  (* ---- +0x50: c.mv a0,a5 -- a0 = the path ---- *)
  iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x50)) Ra0 Ra5 D3 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_50 with "Htext"). }
  iIntros (CIDb18 Hkb18) "Hcg Hpc".
  set (D4 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget D3 Ra5))]> D3).
  assert (HD4a0 : D4 !!! Regidx Ra0 = (mword_of_int fkr_init_path : mword 64)).
  { rewrite /D4 upd_eq. rewrite add_vec_zero_l. rgne.
    rewrite /D3 upd_ne; [| reg_neq]. rewrite -HD2a5. by rgne. }
  assert (HD4a1 : D4 !!! Regidx Ra1 = pa_stk ksp 6).
  { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_eq. exact Hsd0. }
  assert (HD4sp : D4 !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
    exact HD2sp. }
  assert (HD4s1 : D4 !!! Regidx Rs1 = p).
  { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_ne; [| reg_neq].
    exact HD2s1. }
  assert (Hdp52 : add_vec_int (mword_of_int (FR + 0x50) : mword 64) 2
                  = mword_of_int (FR + 0x52)) by pcw.
  iEval (rewrite Hdp52) in "Hpc".
  (* ---- +0x52: jal ra, kexec ---- *)
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x52)) Rra
            (mword_of_int 11878 : mword 21) D4 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc []").
  { iApply (fkr_52 with "Htext"). }
  iIntros (CIDb19 Hkb19) "Hcg Hpc".
  set (D5 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x52) : mword 64) 4)]> D4).
  assert (HD5ra : D5 !!! Regidx Rra = mword_of_int (FR + 0x56))
    by (rewrite /D5 upd_eq; pcw).
  assert (HD5a0 : D5 !!! Regidx Ra0 = (mword_of_int fkr_init_path : mword 64))
    by (rewrite /D5 upd_ne; [exact HD4a0 | reg_neq]).
  assert (HD5a1 : D5 !!! Regidx Ra1 = pa_stk ksp 6)
    by (rewrite /D5 upd_ne; [exact HD4a1 | reg_neq]).
  assert (HD5sp : D5 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /D5 upd_ne; [exact HD4sp | reg_neq]).
  assert (HD5s1 : D5 !!! Regidx Rs1 = p)
    by (rewrite /D5 upd_ne; [exact HD4s1 | reg_neq]).
  iEval (rewrite fkr_kexec_tgt) in "Hpc".
  (* ---- the fabric, out of the seal we just minted ---- *)
  iDestruct (fs_ready_panic with "Hfsr") as "#Hpenv2".
  iDestruct (fs_ready_region with "Hfsr") as "[_ #Hropen]".
  iDestruct (fs_ready_kalloc with "Hfsr") as "#Hkaenv".
  iAssert (fs_fabric γs fsc_uart fsc_disk fsc_dlock pd pav pu fsc_bio icfg_log
             fsc_fs fsc_ireg fsc_ic fsc_itlock fsc_cov fsc_logst icfg_ist
             icfg_nib icfg_dev) as "#Hfab".
  (* ...and the same row-by-row build, for the same measured reason: this
     named [iFrame] over the fabric's sixteen definition-valued rows was
     61.0 s. *)
  { rewrite /fs_fabric.
    iSplitR; [iExact "Hkdata" |].
    iSplitR; [iExact "Hpenv2" |].
    iSplitR; [iExact "Hbio" |].
    iSplitR; [iExact "Hlctx" |].
    iSplitR; [iExact "Hseam" |].
    iSplitR; [iExact "Hgen" |].
    iSplitR; [iExact "Hitb2" |].
    iSplitR; [iExact "Hitbl" |].
    iSplitR; [iExact "Hesc" |].
    iSplitR; [iExact "Hslks" |].
    iSplitR; [iExact "Hireg" |].
    iSplitR; [iExact "Hropen" |].
    iSplitR; [iExact "Hpinv" |].
    iSplitR; [iExact "Hdevi" |].
    iSplitR; [iExact "Hdgeom" |].
    iExact "Hdlock". }
  (* ---- the process block, put back together: the token is the steady
         arm now, so this is [proc_priv] again rather than the deficit ---- *)
  iAssert (proc_priv γf p pid V) with "[Hpbare Hcwd Hofiles]" as "Hpriv".
  { rewrite /proc_priv proc_priv_core_bare.
    iFrame "Hpbare Hcwd Hftok Hofiles". }
  (* ---- the path, at a0 ---- *)
  iPoseProof (fkr_init_path_run with "Hkdata") as "Hpath".
  iEval (rewrite -HD5a0) in "Hpath".
  (* ---- the argument strings: the SAME literal, at the ambient tier and
         at [DfracDiscarded].  This is exactly the aliasing kexec's
         dfrac-generic path/argument premises were written for. ---- *)
  iPoseProof (fkr_init_path_run0 with "Hkdata") as "Hargs1".
  iAssert ([∗ list] i ∈ seq 0 1,
             [∗ list] jj ∈ seq 0 6,
               pa_add (fkr_argv i) jj ↦ₘ{DfracDiscarded} fkr_init_bytes jj)%I
    with "[Hargs1]" as "Hargs".
  { change (seq 0 1) with [0%nat]. rewrite big_sepL_singleton.
    iExact "Hargs1". }
  (* ---- the argv vector, in the frame's bottom two slots ---- *)
  iAssert ([∗ list] i ∈ seq 0 2,
             pa_add (pa_stk ksp 6) (8 * i) ↦₈[KT1]{DfracOwn 1} fkr_argv i)%I
    with "[HwA HwB]" as "Hargv".
  { change (seq 0 2) with [0%nat; 1%nat].
    rewrite big_sepL_cons big_sepL_singleton.
    rewrite fkr_argv_here fkr_argv_next.
    iSplitL "HwB"; [iExact "HwB" | iExact "HwA"]. }
  iEval (rewrite -HD5a1) in "Hargv".
  (* ---- the two inode-reference slots kexec spends ---- *)
  iEval (rewrite /iref_slot) in "Hirs1".
  iDestruct (iref_slots_combine 1 1 with "Hirs1b Hirs1") as "Hirs2".
  (* the three hart-indexed rows came back from fsinit at [CIDf1], and the
     eleven crossings since are all non-parking, so the chain runs from
     THERE -- not from [CID], which fsinit's [wp_next true] cut off. *)
  iDestruct (cpu_own_transport CIDf1 CIDb19 0%nat eb p eb
               ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
  iDestruct (trap_csrs_ext_transport CIDf1 CIDb19 eb p
               ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
  iDestruct (cpu_claim_ext_transport CIDf1 CIDb19 eb p
               ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
  iApply (KX.wp_kexec_sconf γs j γl fsc_uart fsc_disk fsc_dlock pd pav pu
            fsc_bio icfg_log fsc_fs fsc_ireg fsc_ic fsc_itlock
            fsc_kalloc γf fsc_cov fsc_logst fsc_bmapstart icfg_ist icfg_nib
            fsc_size icfg_dev
            5%nat fkr_init_bytes 1%nat fkr_argv
            (fun _ => 5%nat) (fun _ => 6%nat) (fun _ => fkr_init_bytes)
            pid V
            DfracDiscarded DfracDiscarded (DfracOwn 1) DfracDiscarded DfracDiscarded
            D5 av2 eb eb ∅
            Hkx eq_refl eq_refl eq_refl eq_refl Hdev Hnib0 Hlg Hsize Hbm0
            Hbmcov Hbmlog Hist0 Hcovb Hiregb
            fkr_init_path_cstr ltac:(kxarith)
            fkr_argv_nonnull fkr_argv_null ltac:(kxarith)
            ltac:(intros; kxarith) ltac:(intros; exact fkr_init_path_cstr)
            ltac:(intros; kxarith)
            Hjlt Hgl
            with "Hcg Hcpu Hextc Hclmc Htext Hpc Hfab Hkaenv Hbms Hist Hbits
                  Hpriv Hpath Hargv Hargs Hsl3 Hirs2").
  (* ================================================================== *)
  (*  +0x56 .. +0x60: [p->trapframe->a0 = kexec(...)], then the test.     *)
  (* ================================================================== *)
  iIntros (CIDk Hkk mf V' entry spv szv')
    "%Hcsk %Hkok Hcg Hcpu Hextc Hclmc Hpc Hbms2 Hist2 Hka2 Hpriv
     Hpath2 Hargv Hargs2 Hsl3 Hirs2".
  assert (Hpck : ret_pc (D5 !!! Regidx Rra : mword 64) = mword_of_int (FR + 0x56))
    by (rewrite HD5ra; pcw).
  iEval (rewrite Hpck) in "Hpc".
  assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup Hcsk csp_rs1 ltac:(vm_compute; reflexivity));
        exact HD5sp).
  assert (Hmfs1 : mf !!! Regidx Rs1 = p)
    by (rewrite (callee_saved_lookup Hcsk Rs1 ltac:(vm_compute; reflexivity));
        exact HD5s1).
  (* the trapframe page, opened for WRITING out of the block *)
  set (tfp := ud_tfp (pv_upt V')).
  iDestruct (fkr_tfp_valid with "Hpriv") as "%Hpvk".
  iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
  iPoseProof (pt_node_claim_from_static tfp Hpvk with "Hkm") as "#Hptc".
  iDestruct (proc_priv_tf_upd with "Hpriv") as "(Htfc & Htfp & Hpvback)".
  iDestruct (tf_page_length with "Htfp") as "%Htflen".
  assert (Hidx : (tf_arg_idx 0 < length (pv_tf V'))%nat)
    by (rewrite Htflen; unfold TFWORDS, tf_arg_idx; lia).
  destruct (lookup_lt_is_Some_2 (pv_tf V') (tf_arg_idx 0) Hidx) as [w0 Hw0].
  iDestruct (tf_page_word_upd_mem tfp (pv_tf V') (tf_arg_idx 0) w0
               ltac:(vm_compute; lia) Hw0 with "Hptc Htfp") as "(Hcell & Hcback)".
  (* ---- +0x56: c.ld a5,88(s1) -- a5 = p->trapframe ---- *)
  assert (Hld88 : add_vec (rget mf Rs1) (sign_extend' 64 (mword_of_int 88 : mword 12))
                  = p_trapframe p)
    by (rgne; rewrite Hmfs1; exact (prr_p_trapframe p)).
  iEval (rewrite -Hld88) in "Htfc".
  iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x56)) Ra5 Rs1
            (mword_of_int 88 : mword 12) mf av2 (page_base tfp) eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc [] Htfc").
  { iApply (fkr_56 with "Htext"). }
  iIntros (CIDk1 Hkk1) "Hcg Hpc Htfc".
  iEval (rewrite Hld88) in "Htfc".
  set (E1 := <[Regidx Ra5 := regval_into_reg (page_base tfp)]> mf).
  assert (HE1a5 : rget E1 Ra5 = page_base tfp) by (rgne; rewrite /E1 upd_eq; reflexivity).
  assert (Hkp58 : add_vec_int (mword_of_int (FR + 0x56) : mword 64) 2
                  = mword_of_int (FR + 0x58)) by pcw.
  iEval (rewrite Hkp58) in "Hpc".
  (* ---- +0x58: c.sd a0,112(a5) -- the a0 slot, word 14 ---- *)
  assert (Hat112 : add_vec (rget E1 Ra5) (sign_extend' 64 (mword_of_int 112 : mword 12))
                   = tf_pa tfp (8 * Z.of_nat (tf_arg_idx 0)))
    by (rewrite HE1a5; exact (fkr_tf_addr_112 tfp)).
  iEval (rewrite -Hat112) in "Hcell".
  iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x58)) Ra0 Ra5
            (mword_of_int 112 : mword 12) E1 av2 w0 eb with "Hcg Hpc [] Hcell").
  { iApply (fkr_58 with "Htext"). }
  iIntros (CIDk2 Hkk2) "Hcg Hpc Hcell".
  iEval (rewrite Hat112) in "Hcell".
  assert (HE1a0 : rget E1 Ra0 = (mf !!! Regidx Ra0 : mword 64)).
  { rgne. rewrite /E1 upd_ne; [reflexivity | reg_neq]. }
  assert (Hkp5a : add_vec_int (mword_of_int (FR + 0x58) : mword 64) 2
                  = mword_of_int (FR + 0x5a)) by pcw.
  iEval (rewrite Hkp5a) in "Hpc".
  (* ---- +0x5a: c.ld a5,88(s1) -- reloaded, same value ---- *)
  assert (Hld88b : add_vec (rget E1 Rs1) (sign_extend' 64 (mword_of_int 88 : mword 12))
                   = p_trapframe p).
  { rgne. rewrite /E1 upd_ne; [| reg_neq]. rewrite Hmfs1. exact (prr_p_trapframe p). }
  iEval (rewrite -Hld88b) in "Htfc".
  iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x5a)) Ra5 Rs1
            (mword_of_int 88 : mword 12) E1 av2 (page_base tfp) eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc [] Htfc").
  { iApply (fkr_5a with "Htext"). }
  iIntros (CIDk3 Hkk3) "Hcg Hpc Htfc".
  iEval (rewrite Hld88b) in "Htfc".
  set (E2 := <[Regidx Ra5 := regval_into_reg (page_base tfp)]> E1).
  assert (HE2a5 : rget E2 Ra5 = page_base tfp) by (rgne; rewrite /E2 upd_eq; reflexivity).
  assert (Hkp5c : add_vec_int (mword_of_int (FR + 0x5a) : mword 64) 2
                  = mword_of_int (FR + 0x5c)) by pcw.
  iEval (rewrite Hkp5c) in "Hpc".
  (* ---- +0x5c: c.ld a4,112(a5) -- read the word back ---- *)
  assert (Hat112b : add_vec (rget E2 Ra5) (sign_extend' 64 (mword_of_int 112 : mword 12))
                    = tf_pa tfp (8 * Z.of_nat (tf_arg_idx 0)))
    by (rewrite HE2a5; exact (fkr_tf_addr_112 tfp)).
  iEval (rewrite -Hat112b) in "Hcell".
  iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x5c)) Ra4 Ra5
            (mword_of_int 112 : mword 12) E2 av2 (rget E1 Ra0) eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc [] Hcell").
  { iApply (fkr_5c with "Htext"). }
  iIntros (CIDk4 Hkk4) "Hcg Hpc Hcell".
  iEval (rewrite Hat112b) in "Hcell".
  (* ...and the block goes back together, with the new trapframe word in it *)
  iDestruct ("Hcback" $! (rget E1 Ra0) with "Hcell") as "Htfp".
  iDestruct ("Hpvback" $! (<[tf_arg_idx 0 := rget E1 Ra0]> (pv_tf V'))
               with "Htfc Htfp") as "Hpriv".
  set (E3 := <[Regidx Ra4 := regval_into_reg (rget E1 Ra0)]> E2).
  assert (Hkp5e : add_vec_int (mword_of_int (FR + 0x5c) : mword 64) 2
                  = mword_of_int (FR + 0x5e)) by pcw.
  iEval (rewrite Hkp5e) in "Hpc".
  (* ---- +0x5e: c.li a5,-1 ---- *)
  iApply (wp_cli_s_sconf (mword_of_int (FR + 0x5e)) Ra5
            (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) E3 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) fkr_minus_one
            with "Hcg Hpc []").
  { iApply (fkr_5e with "Htext"). }
  iIntros (CIDk5 Hkk5) "Hcg Hpc".
  set (E4 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> E3).
  assert (HE4a4 : rget E4 Ra4 = (mf !!! Regidx Ra0 : mword 64)).
  { rgne. rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq. exact HE1a0. }
  assert (HE4a5 : rget E4 Ra5 = (mword_of_int (-1) : mword 64))
    by (rgne; rewrite /E4 upd_eq; reflexivity).
  assert (HE4sp : E4 !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
    rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq].
    exact Hmfsp. }
  assert (HE4s1 : E4 !!! Regidx Rs1 = p).
  { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
    rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq].
    exact Hmfs1. }
  (* ================================================================== *)
  (*  +0x60: [if (p->trapframe->a0 == -1)].  BOTH ARMS ARE LIVE -- kexec  *)
  (*  has eight [bad:] exits, and its contract's failure disjunct is what  *)
  (*  the branch is testing for.                                          *)
  (* ================================================================== *)
  destruct Hkok as [[Hr1 _] | Hok].
  - (* ---- kexec FAILED: a0 = -1, the branch is taken, panic("exec") ---- *)
    iApply (wp_beq_taken_s_sconf (mword_of_int (FR + 0x60))
              (mword_of_int 58 : mword 13) Ra5 Ra4 E4 av2 eb
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HE4a4 HE4a5 Hr1; vm_compute; reflexivity)
              fkr_beq_align with "Hcg Hpc []").
    { iApply (fkr_60 with "Htext"). }
    iApply bi.later_intro. iIntros (CIDk6 Hkk6) "Hcg Hpc".
    iEval (rewrite fkr_beq_tgt) in "Hpc".
    (* ---- +0x9a: auipc a0,0x5 ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x9a)) Ra0
              (mword_of_int 5 : mword 20) E4 av2 eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fkr_9a with "Htext"). }
    iIntros (CIDk7 Hkk7) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (mword_of_int (FR + 0x9a) : mword 64)
                      (auipc_off (mword_of_int 5 : mword 20)))]> E4).
    assert (Hpp9e : add_vec_int (mword_of_int (FR + 0x9a) : mword 64) 4
                    = mword_of_int (FR + 0x9e)) by pcw.
    iEval (rewrite Hpp9e) in "Hpc".
    (* ---- +0x9e: addi a0,a0,2018 -- a0 = the "exec" literal ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x9e)) Ra0 Ra0
              (mword_of_int 2018 : mword 12) P1 av2 eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fkr_9e with "Htext"). }
    iIntros (CIDk8 Hkk8) "Hcg Hpc".
    set (P2 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (rget P1 Ra0)
                      (sign_extend' 64 (mword_of_int 2018 : mword 12)))]> P1).
    assert (HP2a0 : P2 !!! Regidx Ra0 = (mword_of_int fkr_exec_msg : mword 64)).
    { rewrite /P2 upd_eq. rgne. rewrite /P1 upd_eq. exact fkr_exec_msg_addr. }
    assert (Hppa2 : add_vec_int (mword_of_int (FR + 0x9e) : mword 64) 4
                    = mword_of_int (FR + 0xa2)) by pcw.
    iEval (rewrite Hppa2) in "Hpc".
    (* ---- +0xa2: jal ra, panic -- and forkret ends here ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (FR + 0xa2)) Rra
              (mword_of_int 2092646 : mword 21) P2 av2 eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fkr_a2 with "Htext"). }
    iIntros (CIDk9 Hkk9) "Hcg Hpc".
    set (P3 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (FR + 0xa2) : mword 64) 4)]> P2).
    assert (HP3a0 : P3 !!! Regidx Ra0 = (mword_of_int fkr_exec_msg : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a0 | reg_neq]).
    iEval (rewrite fkr_panic_tgt) in "Hpc".
    iDestruct (cpu_own_transport CIDk CIDk9 0%nat eb p eb
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iPoseProof (fkr_exec_msg_res with "Hkdata") as "Hmsg".
    iEval (rewrite -HP3a0) in "Hmsg".
    iApply (PN.wp_panic_sconf KT1 P3 av2 0%nat eb eb p
              (PkAStr DfracDiscarded "exec"%string) ∅
              ltac:(kxarith) ltac:(reflexivity) ltac:(kxarith) ltac:(lkbelow)
              with "Hcg Hcpu Htext Hkdata Hpc Hpenv2 Hmsg").
  - (* ---- kexec SUCCEEDED: a0 = argc = 1, the branch falls through ---- *)
    destruct Hok as (Hr & _).
    iApply (wp_beq_fall_s_sconf (mword_of_int (FR + 0x60))
              (mword_of_int 58 : mword 13) Ra5 Ra4 E4 av2 eb
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HE4a4 HE4a5 Hr; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fkr_60 with "Htext"). }
    iIntros (CIDk6 Hkk6) "Hcg Hpc".
    assert (Hkp64 : add_vec_int (mword_of_int (FR + 0x60) : mword 64) 4
                    = mword_of_int (FR + 0x64)) by pcw.
    iEval (rewrite Hkp64) in "Hpc".
    (* THE FRAME, BACK WHOLE.  The two slots the compound literal occupied
       come home: kexec only READ the vector, so it hands the row back at
       the fraction it took, and the row IS the two stack words. *)
    iEval (rewrite HD5a1) in "Hargv".
    iEval (change (seq 0 2) with [0%nat; 1%nat]) in "Hargv".
    iEval (rewrite big_sepL_cons big_sepL_singleton
                  fkr_argv_here fkr_argv_next) in "Hargv".
    iDestruct "Hargv" as "[HwB HwA]".
    iEval (rewrite -Hslot5) in "HwA".
    iEval (rewrite -Hslot6) in "HwB".
    iDestruct (stack_own_2_intro (KTR := KT1) (pa_stk ksp 4)
                 (fkr_argv 1) (fkr_argv 0) with "HwA HwB") as "Hf2".
    iAssert (stack_own (KTR := KT1) ksp 6) with "[Hf14 Hf2]" as "Hf16".
    { iApply (stack_own_split_2 (KTR := KT1) ksp 4 6 ltac:(lia)).
      change (6 - 4)%nat with 2%nat. iFrame "Hf14 Hf2". }
    iDestruct (cpu_own_transport CIDk CIDk6 0%nat eb p eb
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iDestruct (trap_csrs_ext_transport CIDk CIDk6 eb p
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDk CIDk6 eb p
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    (* ...and the two arms MEET at +0x64, which is [fkr_tail]. *)
    iApply (fkr_tail W j γf pid
              (upd_tf V' (<[tf_arg_idx 0 := rget E1 Ra0]> (pv_tf V')))
              ks E4 av av2 eb Hjlt ltac:(kxarith) Havsum HE4sp HE4s1
              with "Htext Hwire Hclaimmap Hpc Hcg Hcpu Hextc Hclmc Hks Hf16
                    Hpriv Hdone HW Hyield").
Qed.

Theorem wp_forkret
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (W : iProp Σ) (j : nat) (γs : list gname) (γl γf : gname)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) :
    wp_forkret_gen_body (fun (h : CpuId) (Xc : CurCtx) => usertrap_res_bare (CID := h) (XI := Xc)) W
      j γs γl γf pid V ks m av av2 eb.
Proof.
  cbv beta delta [wp_forkret_gen_body].
  intros pcE p ksp Hjlt Hgl Hav2 Hkx Hut Hsp.
  (* the tail's own budget: prepare_return's 12 is under kexec's 184 *)
  assert (Hpr : (K_prepare_return <= av2)%nat) by lia.
  (* the budget in numbers [lia] can see *)
  pose proof Hut as Hut'.
  
  pose proof Hpr as Hpr'.
  
  (* the frame's six slots come off the top and go back on at the exit *)
  assert (Havsum : av = (6 + (trap_res eb + av2))%nat) by lia.
  iIntros "#Htext #Hwire #Hclaimmap Hpc #Hpinv Hcg Hcpu Htc Hclm
           Hlocked HR #Hks Hpv HW Hyield".
  (* p->lock IS the process table's slot [j] -- which is why this contract
     takes [procs_inv] and no longer takes an [is_lock] of its own. *)
  iDestruct (procs_inv_lookup γs j γl Hgl with "Hpinv") as "#Hislock".
  (* ================================================================== *)
  (*  +0x00 .. +0x08: the 48-byte frame, at [b = false].                 *)
  (* ================================================================== *)
  assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                  = pa_stk (m !!! Regidx csp_rs1) 6)
    by (apply (stk_push _ _ 6); pcw).
  iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 false
            ltac:(lia) Hpush with "Hcg Hpc []").
  { iApply (fkr_00 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hframe Hpc".
  set (M1 := <[Regidx csp_rs1 := regval_into_reg
                 (add_vec (m !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
  iEval (rewrite Hsp) in "Hframe".
  iEval (rewrite -Hav2) in "Hcg".
  assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M1 upd_eq Hpush Hsp; reflexivity).
  assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FR + 0x02)) by pcw.
  iEval (rewrite Hp02) in "Hpc".
  (* the frame: three saved words, three scratch slots *)
  iDestruct (stack_own_split_1 (KTR := KT1) ksp 4 6 ltac:(lia) with "Hframe") as "[Hf14 Hf56]".
  iDestruct (stack_own_4_elim with "Hf14") as (vra vs0 vs1 vsc) "(Hbra & Hbs0 & Hbs1 & Hbsc)".
  assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                   (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                 = pa_stk ksp 1)
    by (rewrite HM1sp; apply stk_frm; pcw).
  assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                   (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                 = pa_stk ksp 2)
    by (rewrite HM1sp; apply stk_frm; pcw).
  assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                   (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                 = pa_stk ksp 3)
    by (rewrite HM1sp; apply stk_frm; pcw).
  iEval (rewrite -Hpa1) in "Hbra".
  iEval (rewrite -Hpa2) in "Hbs0".
  iEval (rewrite -Hpa3) in "Hbs1".
  (* ---- +0x02: c.sdsp ra,40(sp) ---- *)
  iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x02)) (mword_of_int 5 : mword 6)
            Rra M1 (trap_res eb + av2)%nat vra false with "Hcg Hpc [] Hbra").
  { iApply (fkr_02 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hbra".
  iEval (rewrite Hpa1) in "Hbra".
  assert (Hp04 : add_vec_int (mword_of_int (FR + 0x02) : mword 64) 2
                 = mword_of_int (FR + 0x04)) by pcw.
  iEval (rewrite Hp04) in "Hpc".
  (* ---- +0x04: c.sdsp s0,32(sp) ---- *)
  iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x04)) (mword_of_int 4 : mword 6)
            Rs0 M1 (trap_res eb + av2)%nat vs0 false with "Hcg Hpc [] Hbs0").
  { iApply (fkr_04 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs0".
  iEval (rewrite Hpa2) in "Hbs0".
  assert (Hp06 : add_vec_int (mword_of_int (FR + 0x04) : mword 64) 2
                 = mword_of_int (FR + 0x06)) by pcw.
  iEval (rewrite Hp06) in "Hpc".
  (* ---- +0x06: c.sdsp s1,24(sp) ---- *)
  iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x06)) (mword_of_int 3 : mword 6)
            Rs1 M1 (trap_res eb + av2)%nat vs1 false with "Hcg Hpc [] Hbs1").
  { iApply (fkr_06 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs1".
  iEval (rewrite Hpa3) in "Hbs1".
  assert (Hp08 : add_vec_int (mword_of_int (FR + 0x06) : mword 64) 2
                 = mword_of_int (FR + 0x08)) by pcw.
  iEval (rewrite Hp08) in "Hpc".
  (* the frame goes back to being one run: the three saved words are dead
     from here on, and both arms of the [if] merely carry it to the tail *)
  iAssert (stack_own (KTR := KT1) ksp 4) with "[Hbra Hbs0 Hbs1 Hbsc]" as "Hf14".
  { iApply (stack_own_4_intro (KTR := KT1) ksp with "Hbra Hbs0 Hbs1 Hbsc"). }
  iAssert (stack_own (KTR := KT1) ksp 6) with "[Hf14 Hf56]" as "Hf16".
  { iApply (stack_own_split_2 (KTR := KT1) ksp 4 6 ltac:(lia)).
    iSplitL "Hf14"; [iExact "Hf14" | iExact "Hf56"]. }
  (* ---- +0x08: c.addi4spn s0,sp,48 ---- *)
  iApply (wp_caddi4spn_s_sconf (mword_of_int (FR + 0x08)) (Cregidx (mword_of_int 0))
            (mword_of_int 12 : mword 8) Rs0 M1 (trap_res eb + av2)%nat false
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
            with "Hcg Hpc []").
  { iApply (fkr_08 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M2 := <[Regidx Rs0 := regval_into_reg
                 (add_vec (M1 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
  assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
  (* THE FRAME POINTER, NAMED.  s0 = sp + 48 = the kernel-stack top, and the
     boot arm needs it: the argv vector kexec is handed is written at
     -48(s0) / -40(s0), i.e. into this frame's own bottom two slots. *)
  assert (HM2s0 : M2 !!! Regidx Rs0 = ksp).
  { rewrite /M2 upd_eq. rewrite HM1sp. exact (stk_fp_48 ksp). }
  assert (Hp0a : add_vec_int (mword_of_int (FR + 0x08) : mword 64) 2
                 = mword_of_int (FR + 0x0a)) by pcw.
  iEval (rewrite Hp0a) in "Hpc".
  (* ================================================================== *)
  (*  +0x0a: jal ra, myproc -- a0 = p.                                   *)
  (* ================================================================== *)
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x0a)) Rra
            (mword_of_int 2097092 : mword 21) M2 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc []").
  { iApply (fkr_0a with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M3 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x0a) : mword 64) 4)]> M2).
  assert (HM3sp : M3 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M3 upd_ne; [exact HM2sp | reg_neq]).
  assert (HM3s0 : M3 !!! Regidx Rs0 = ksp)
    by (rewrite /M3 upd_ne; [exact HM2s0 | reg_neq]).
  assert (HM3ra : M3 !!! Regidx Rra = mword_of_int (FR + 0x0e))
    by (rewrite /M3 upd_eq; pcw).
  assert (Hmyproc : add_vec (mword_of_int (FR + 0x0a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2097092 : mword 21))
                    = mword_of_int KernelSyms.myproc) by pcw.
  iEval (rewrite Hmyproc) in "Hpc".
  iApply (MP.wp_myproc_sconf M3 (trap_res eb + av2)%nat 1%nat eb p false {["proc"%string]}
            fkr_n1 ltac:(lia) with "Hcg Hcpu Htext Hpc").
  iApply wp_next_off_intro. iIntros (msq A) "%Hmsq Hcg Hcpu Hpc %HcsA".
  destruct HcsA as [HcsA HAa0].
  assert (Hpc0e : ret_pc (M3 !!! Regidx Rra) = mword_of_int (FR + 0x0e))
    by (rewrite HM3ra; pcw).
  iEval (rewrite Hpc0e) in "Hpc".
  assert (HAsp : A !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM3sp).
  assert (HAs0 : A !!! Regidx Rs0 = ksp)
    by (rewrite (callee_saved_lookup HcsA Rs0 ltac:(vm_compute; reflexivity)); exact HM3s0).
  (* ---- +0x0e: c.mv s1,a0 ---- *)
  iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x0e)) Rs1 Ra0
            A (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_0e with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M4 := <[Regidx Rs1 := regval_into_reg
                 (add_vec zero_reg (rget A Ra0))]> A).
  assert (HM4s1 : M4 !!! Regidx Rs1 = p).
  { rewrite /M4 upd_eq. rgne. rewrite HAa0. apply add_vec_zero_l. }
  assert (HM4a0 : M4 !!! Regidx Ra0 = p)
    by (rewrite /M4 upd_ne; [exact HAa0 | reg_neq]).
  assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M4 upd_ne; [exact HAsp | reg_neq]).
  assert (HM4s0 : M4 !!! Regidx Rs0 = ksp)
    by (rewrite /M4 upd_ne; [exact HAs0 | reg_neq]).
  assert (Hp10 : add_vec_int (mword_of_int (FR + 0x0e) : mword 64) 2
                 = mword_of_int (FR + 0x10)) by pcw.
  iEval (rewrite Hp10) in "Hpc".
  (* ================================================================== *)
  (*  +0x10: jal ra, release -- p->lock goes.  THE INDEX BECOMES [eb].    *)
  (* ================================================================== *)
  iApply (wp_jal_s_sconf (mword_of_int (FR + 0x10)) Rra
            (mword_of_int 2093862 : mword 21) M4 (trap_res eb + av2)%nat false
            ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc []").
  { iApply (fkr_10 with "Htext"). }
  iApply wp_next_off_intro. iIntros "Hcg Hpc".
  set (M5 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (FR + 0x10) : mword 64) 4)]> M4).
  assert (HM5a0 : M5 !!! Regidx Ra0 = p)
    by (rewrite /M5 upd_ne; [exact HM4a0 | reg_neq]).
  assert (HM5s1 : M5 !!! Regidx Rs1 = p)
    by (rewrite /M5 upd_ne; [exact HM4s1 | reg_neq]).
  assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite /M5 upd_ne; [exact HM4sp | reg_neq]).
  assert (HM5s0 : M5 !!! Regidx Rs0 = ksp)
    by (rewrite /M5 upd_ne; [exact HM4s0 | reg_neq]).
  assert (HM5ra : M5 !!! Regidx Rra = mword_of_int (FR + 0x14))
    by (rewrite /M5 upd_eq; pcw).
  assert (Hrelease : add_vec (mword_of_int (FR + 0x10) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093862 : mword 21))
                     = mword_of_int KernelSyms.release) by pcw.
  iEval (rewrite Hrelease) in "Hpc".
  assert (Hlka : add_vec (M5 !!! Regidx Ra0)
                   (sign_extend' 64 (mword_of_int 0 : mword 12)) = p)
    by (rewrite HM5a0; apply addv_sext0).
  (* the arm splits: what release wants and what prepare_return will *)
  iDestruct (arm_pay_ext_split eb p with "Htc Hclm") as "[Hpay [Hext Hcx]]".
  iApply (RL.wp_release_sconf KT1 γl p "proc"%string
            (proc_lock_res γs γl p) M5 0%nat eb p av2 {["proc"%string]}
            Hlka ltac:(lia) with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
  iIntros (CIDr Hkr mr) "Hcg Hpc %Hcsr Hcpu".
  assert (Hpc14 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (FR + 0x14))
    by (rewrite HM5ra; pcw).
  iEval (rewrite Hpc14) in "Hpc".
  (* the released set collapses; [cpu_own] at depth 0 says so itself *)
  iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlks Hcpu]".
  iEval (rewrite Hlks) in "Hcpu".
  assert (Hmrs1 : mr !!! Regidx Rs1 = p)
    by (rewrite (callee_saved_lookup Hcsr Rs1 ltac:(vm_compute; reflexivity)); exact HM5s1).
  assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk ksp 6)
    by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
  assert (Hmrs0 : mr !!! Regidx Rs0 = ksp)
    by (rewrite (callee_saved_lookup Hcsr Rs0 ltac:(vm_compute; reflexivity)); exact HM5s0).
  (* ================================================================== *)
  (*  THE BRANCH IS DECIDED HERE, BEFORE A SINGLE INSTRUCTION OF IT RUNS. *)
  (* ================================================================== *)
  (* [FirstTok.first_tok] rides inside the block, and it is the WHOLE of
     the argument: the boot arm's [first_addr ↦₄ 1] is exclusive, so a
     process holding it is the one process entitled to build the file
     system, and a process holding the steady arm's discarded 0 reads 0 and
     is not.  No invariant, no mask, no atomicity claim -- the two arms are
     incompatible at one address ([FirstTok.first_tok_boot_excl]).

     The token comes out at [proc_priv_split_cwd]'s three-way seam, which is
     where it joined the block; [cwd_ref] comes with it and goes straight
     back on the arm that continues here. *)
  iEval (rewrite proc_priv_split_cwd) in "Hpv".
  iDestruct "Hpv" as "(Hpnc & Hcwd & Hftok)".
  iDestruct (first_tok_open with "Hftok") as "[Hboot | #Hdone]".
  { (* ---------------- THE BOOT ARM: fsinit / first = 0 / kexec -------- *)
    iDestruct "Hboot" as "(Hf1 & #Hbp & #Hka & Hfsi)".
    (* the two [_ext] halves are still at the entry hart; the release moved
       the binder, so they come across before the arm is entered *)
    iDestruct (trap_csrs_ext_transport CID CIDr eb p
                 ltac:(wp_next_chain) with "Hext") as "Hext".
    iDestruct (cpu_claim_ext_transport CID CIDr eb p
                 ltac:(wp_next_chain) with "Hcx") as "Hcx".
    iApply (fkr_boot (CID := CIDr) W j γs γl γf pid V ks mr av av2 eb
              Hjlt Hgl Hkx Havsum Hmrsp Hmrs0 Hmrs1
            with "Htext Hwire Hclaimmap Hpc Hpinv Hcg Hcpu Hext Hcx Hks
                  Hf16 Hpnc Hcwd Hf1 Hbp Hka Hfsi HW Hyield"). }
  (* ---------------- THE STEADY ARM: [first] is 0, the boot arm is dead -- *)
  iDestruct (first_tok_of_done with "Hdone") as "#Hftok".
  (* the token's steady disjunct IS [first_done]; keep the bundled form for
     the closer and take the cell out for the [c.lw] at +0x1c. *)
  iAssert (first_done) as "#Hdone2"; [iExact "Hdone"|].
  iDestruct "Hdone" as "#[Hfirst Hfsready]".
  iAssert (proc_priv γf p pid V) with "[Hpnc Hcwd]" as "Hpv".
  { iApply (bi.equiv_entails_1_2 _ _ (proc_priv_split_cwd γf p pid V)).
    iSplitL "Hpnc"; [iExact "Hpnc" |].
    iSplitL "Hcwd"; [iExact "Hcwd" |]. iExact "Hftok". }
  (* ================================================================== *)
  (*  +0x14 .. +0x24: [if (first)] -- refuted by the discarded cell.      *)
  (* ================================================================== *)
  (* ---- +0x14: auipc a5,0x9 ---- *)
  iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x14)) Ra5
            (mword_of_int 9 : mword 20) mr av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_14 with "Htext"). }
  iIntros (CID1 Hk1) "Hcg Hpc".
  set (T1 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (mword_of_int (FR + 0x14) : mword 64)
                    (auipc_off (mword_of_int 9 : mword 20)))]> mr).
  assert (Hp18 : add_vec_int (mword_of_int (FR + 0x14) : mword 64) 4
                 = mword_of_int (FR + 0x18)) by pcw.
  iEval (rewrite Hp18) in "Hpc".
  (* ---- +0x18: addi a5,a5,-1712 -- a5 = &first ---- *)
  iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x18)) Ra5 Ra5
            (mword_of_int 2384 : mword 12) T1 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_18 with "Htext"). }
  iIntros (CID2 Hk2) "Hcg Hpc".
  set (T2 := <[Regidx Ra5 := regval_into_reg
                 (add_vec (rget T1 Ra5)
                    (sign_extend' 64 (mword_of_int 2384 : mword 12)))]> T1).
  assert (HT2a5 : rget T2 Ra5 = first_addr).
  { rgne. rewrite /T2 upd_eq. rgne. rewrite /T1 upd_eq. exact fkr_first_addr. }
  assert (Hp1c : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 4
                 = mword_of_int (FR + 0x1c)) by pcw.
  iEval (rewrite Hp1c) in "Hpc".
  (* ---- +0x1c: c.lw a5,0(a5) -- the read that decides the branch ---- *)
  assert (Hfaddr : add_vec (rget T2 Ra5)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = first_addr)
    by (rewrite HT2a5; apply addv_sext0).
  iEval (rewrite -Hfaddr) in "Hfirst".
  iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x1c)) Ra5 Ra5
            (mword_of_int 0 : mword 12) T2 av2 (mword_of_int 0 : mword 32) eb
            ltac:(vm_compute; discriminate) ltac:(rdok)
            with "Hcg Hpc [] Hfirst").
  { iApply (fkr_1c with "Htext"). }
  iIntros (CID3 Hk3) "Hcg Hpc _".
  set (T3 := <[Regidx Ra5 := regval_into_reg
                 (sign_extend' 64 (mword_of_int 0 : mword 32))]> T2).
  assert (Hp1e : add_vec_int (mword_of_int (FR + 0x1c) : mword 64) 2
                 = mword_of_int (FR + 0x1e)) by pcw.
  iEval (rewrite Hp1e) in "Hpc".
  (* ---- +0x1e: fence r,rw -- the acquire barrier, state-preserving ---- *)
  iApply (wp_fence_gen_s_sconf (mword_of_int (FR + 0x1e))
            (mword_of_int 0 : mword 4) (mword_of_int 2 : mword 4)
            (mword_of_int 3 : mword 4) zreg zreg T3 av2 eb
            with "Hcg Hpc []").
  { iApply (fkr_1e with "Htext"). }
  iIntros (CID4 Hk4) "Hcg Hpc".
  assert (Hp22 : add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 4
                 = mword_of_int (FR + 0x22)) by pcw.
  iEval (rewrite Hp22) in "Hpc".
  (* ---- +0x22: sext.w a5,a5 ---- *)
  iApply (wp_caddiw_s_sconf (mword_of_int (FR + 0x22)) Ra5
            (mword_of_int 0 : mword 6) T3 av2 eb
            ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
  { iApply (fkr_22 with "Htext"). }
  iIntros (CID5 Hk5) "Hcg Hpc".
  set (T4 := <[Regidx Ra5 := regval_into_reg
                 (sign_extend' 64 (subrange_vec_dec
                    (add_vec (rget T3 Ra5)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> T3).
  assert (HT4a5 : eq_vec (rget T4 Ra5) zero_reg = true).
  { rgne. rewrite /T4 upd_eq. rgne. rewrite /T3 upd_eq.
    vm_compute. reflexivity. }
  assert (Hp24 : add_vec_int (mword_of_int (FR + 0x22) : mword 64) 2
                 = mword_of_int (FR + 0x24)) by pcw.
  iEval (rewrite Hp24) in "Hpc".
  (* ---- +0x24: c.beqz a5, +0x64 -- TAKEN, so the boot arm is dead ---- *)
  iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FR + 0x24))
            (mword_of_int 32 : mword 8) (Cregidx (mword_of_int 7)) Ra5
            T4 av2 eb ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; discriminate) HT4a5 fkr_beqz_align
            with "Hcg Hpc []").
  { iApply (fkr_24 with "Htext"). }
  iNext. iIntros (CID6 Hk6) "Hcg Hpc".
  iEval (rewrite fkr_beqz_tgt) in "Hpc".
  
  assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk ksp 6).
  { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_ne; [| reg_neq].
    rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_ne; [| reg_neq].
    exact Hmrsp. }
  assert (HT4s1 : T4 !!! Regidx Rs1 = p).
  { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_ne; [| reg_neq].
    rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_ne; [| reg_neq].
    exact Hmrs1. }

  (* ================================================================== *)
  (*  ...and into the tail, which the boot arm reaches too.              *)
  (* ================================================================== *)
  (* the three hart-indexed carriers, moved to the current binder in one
     step -- [wp_next_chain] chains the whole run of [Hk*]. *)
  iDestruct (cpu_own_transport CIDr CID6 0%nat eb p eb
               ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
  iDestruct (trap_csrs_ext_transport CID CID6 eb p
               ltac:(wp_next_chain) with "Hext") as "Hext".
  iDestruct (cpu_claim_ext_transport CID CID6 eb p
               ltac:(wp_next_chain) with "Hcx") as "Hcx".
  (* the steady arm's [first_done] IS [first_tok]'s persistent steady
     disjunct, read at +0x24; it goes straight to the tail. *)
  iApply (fkr_tail (CID := CID6) W j γf pid V ks T4 av av2 eb
            Hjlt Hpr Havsum HT4sp HT4s1
          with "Htext Hwire Hclaimmap Hpc Hcg Hcpu Hext Hcx Hks Hf16 Hpv
                Hdone2 HW Hyield").
Qed.

End ForkretProof.
