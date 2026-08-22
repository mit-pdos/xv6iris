(* ===================================================================== *)
(*  ProofKexecPinned.v -- kexec("/init") AT THE IMAGE'S BYTES              *)
(*  (claude-notes/projects/namei-pinned-lookup.md §13, stage N-5.2B)       *)
(* ===================================================================== *)

(*  [SpecKexecPinned.wp_kexec_pinned], assembled.  Almost nothing here is
    new: §13.3 made the whole cone generic in the exit relation and §13.4
    made phase A's exit opaque and its header claim conditional, so this
    file is [ProofKexec.v]'s plumbing with phase A swapped for the pinned
    one and ONE case split added -- on the verdict phase A publishes.

    THE CASE SPLIT IS THE CONTRACT.  On the arm where both lends survived,
    the walk ran at [Q := kxp_entry_ok] and the commit block's
    [ld a4,-408(s0)] is discharged from the header claim by
    [KexecOkQ.kxq_entry_of_hdr] -- so the caller learns that
    [trapframe->epc] holds /init's own ELF entry point.  On the arm where
    either lend was cancelled the walk runs at [Q := fun _ => True], which
    is the landed relation, and the caller gets the persistent receipt
    instead.  Nothing else differs between the two: the SAME landed blocks
    run below +0x090 on both.                                             *)

(* ProofKexec.v -- kexec() WHOLE: the four phases composed into
   SpecKexec.wp_kexec_sconf_body, and the only place they meet.

   Every instruction of kexec is proven elsewhere; this file does the
   plumbing and nothing else.  The chain, and where each seam is stated:

     entry            SpecKexec.wp_kexec_sconf_body      pc = kexec + 0
       PA.kxc_phaseA                                     .. +0x090
     +0x090           the eight-conjunct register block A publishes
       PB.kxc_b1                                         .. +0x0cc / +0x1a2
     +0x1a2 / +0x12c  ProofKexecSeam.kxc_at_1a2 / kxc_at_12c
       PB3.kxc_b2z / PB3.kxc_b2                          .. +0x1ae
     +0x1ae           ProofKexecSeam.kxc_at_1ae
       PC.kxc_c_setup                                    .. +0x21a / +0x272
     +0x21a           ProofKexecSeam.kxc_at_21a
       PC.kxc_argv_loop                                  .. +0x272
     +0x272           ProofKexecSeam.kxc_at_272
       PC.kxc_c_close                                    .. +0x2a6
     +0x2a6           ProofKexecSeam.kxc_at_2a6
       PD.kxd_phaseD                                     .. ret

   THE ONE THING THAT MAKES THE COMPOSITION WORK IS THAT EVERY SEAM HANDS
   THE CALLER'S EXIT BACK.  A [wp_next] continuation is LINEAR, so a block
   that owns a [bad:] path and also publishes a successor state would
   consume the single exit the caller has and leave the successor with
   none; each phase lemma therefore takes the exit once and returns it
   inside its own output (durable-notes' "CHAINING TWO HALVES").  Reading
   an [iApply] below: the exit travels as [Hcont] through every step and is
   spent exactly once, by whichever block actually returns.

   TWO PLUMBING FACTS ARE NOT FREE, and they are all this file has to
   prove for itself.  (There used to be a third: the free-pool set SHRANK
   across the phases, each block stated its exit's bitmap clause against
   the CURRENT set, and a local [kxc_exit_weaken] transported the exit from
   one set to the next.  With the bitmap living in the persistent
   [BitmapInv.bitmap_inv] no contract names a set at all, so the exit is
   the SAME proposition everywhere and the transport is gone.)

   - THE ARGV LOOP IS ENTERED ONLY AT [c < na].  Its own measure argument
     needs that, and the loop head cannot say it: what says it is the head's
     [avf c <> 0] against the contract's [avf na = 0].
   - [oldsz] AND THE 8192 BOUND COME OUT OF PHASE C'S SETUP, not out of the
     contract, which is why [kxc_c_setup]'s output publishes both.

   The functor arguments are kexec's sixteen callees.  [PPT] is the
   GENERAL [PROC_PAGETABLE_GEN], not [PROC_PAGETABLE]: kexec runs at
   [kalloc_env ga None] and tests proc_pagetable's result against 0, so it
   is the caller that can use the uncounted arm (projects/kexec.md, "What
   is NOT blocked"). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks.
Require Import LogDefs.
Require Import BitmapInv.
Require Import InodeInv.
Require Import KvmSpec.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import FileInvDefs.
Require Import SpecKexec.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecNamei.
Require Import SpecNameiTr.
Require Import SpecProcFreepagetable.
Require Import SpecProcPagetable.
Require Import SpecWalkaddr.
Require Import SpecFlags2perm.
Require Import SpecUvmalloc.
Require Import SpecUvmclear.
Require Import SpecStrlen.
Require Import SpecCopyout.
Require Import SpecSafestrcpy.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import ProofKexecB.
Require Import SpecPanic.
Require Import ProofKexecB2.
Require Import ProofKexecB3.
Require Import ProofKexecC.
Require Import ProofKexecD.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KX := KernelSyms.kexec (only parsing).

Require Import ProofKexecPinnedA.
Require Import SpecKexecPinned.
Require Import KexecOkQ.
Require Import DirViewLend.
Require Import IcacheRef.


(* ===================================================================== *)
(*  THE UNFOLDING WAND (N-5.2B §13.4).                                    *)
(*                                                                        *)
(*  The pinned continuation, opened into the landed-shaped exit the cone   *)
(*  relays.  ONE lemma, because the only thing that varies between the     *)
(*  walk's two arms is which disjunct of the pinned post the opener can    *)
(*  pay: on the intact arm the LEFT one, purely, at [Q := kxp_entry_ok];   *)
(*  on the receipt arm the RIGHT one, at [Q := fun _ => True], funded by   *)
(*  the persistent [kxp_lost].  That choice is the [□] premise.            *)
(*                                                                        *)
(*  Both bodies are SPELLED OUT rather than abstracted behind a            *)
(*  [T : regfile -> pprivate -> iProp]: the tail contains [proc_priv],     *)
(*  and higher-order unification against its 4096-conjunct trapframe       *)
(*  big-op is durable-notes' measured non-terminating case (§13.3).        *)
(* ===================================================================== *)
Section KexecPinnedWand.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma kxp_body_wand (Q : mword 64 -> Prop)
      (jp : nat) (ga gf : gname) (bmapstart inodestart : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (ra0 pv av : mword 64) :
    □ (∀ (V' : pprivate) (r entry spv szv' : mword 64),
         ⌜kexec_ok_q Q V V' r entry spv szv' na alen⌝ -∗
         (⌜kexec_ok_q kxp_entry_ok V V' r entry spv szv' na alen⌝
          ∨ (⌜kexec_ok V V' r entry spv szv' na alen⌝ ∗ kxp_lost))) -∗
    □ (∀ CX : CpuId,
      (
    ∀ (mf : regfile) (V' : pprivate)
      (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        (* THE INTACT ARM IS PURE, AND DELIBERATELY SO (§13.4, RULING 2).
           It used to hand [fv_pin] back as well.  It cannot: the exit
           continuation is built ONCE, before the walk knows whether the
           contents lend survived, and a linear resource in that closure is
           exactly what stops the two branches from sharing it.  Dropping it
           costs the caller nothing it had -- boot drops the pin anyway --
           and it mirrors [NameiInitPinned.wp_namei_init_pinned], whose ok
           arm does not return the dv pin either.  The receipt arm keeps
           [kxp_lost], which is PERSISTENT and therefore free to duplicate
           into the closure. *)
        (⌜kexec_ok_q kxp_entry_ok V V'
             (mf !!! Regidx (mword_of_int 10 : mword 5))
             entry spv szv' na alen⌝
         ∨ (⌜kexec_ok V V' (mf !!! Regidx (mword_of_int 10 : mword 5))
                      entry spv szv' na alen⌝ ∗ kxp_lost)) -∗
        sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jp) -∗
        pc_is (ret_pc ra0) -∗
        BitmapInv.sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        InodeInv.sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
        bslots 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)
      )
       -∗
      (
    ∀ (mf : regfile) (V' : pprivate) (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jp) -∗
        pc_is (ret_pc ra0) -∗
        BitmapInv.sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        InodeInv.sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
        bslots 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)
      )).
  Proof.
    iIntros "#Hrel". iModIntro. iIntros (CX) "Hk".
    iIntros (mf V' entry spv szv') "%Hcs %Hok Hsie Hcnt Htc Hcl Hpc Hbm Hin
             Hka Hpriv Hpath Hargv Hargs Hbs Hirs".
    iApply ("Hk" $! mf V' entry spv szv' with
             "[%] [Hrel] Hsie Hcnt Htc Hcl Hpc Hbm Hin Hka Hpriv Hpath Hargv
              Hargs Hbs Hirs"); [exact Hcs |].
    iApply ("Hrel" $! V' (mf !!! Regidx Ra0) entry spv szv'). by iPureIntro.
  Qed.

End KexecPinnedWand.

Module KexecPinnedProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                  (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                  (EndOp : END_OP) (PPT : PROC_PAGETABLE_GEN)
                  (PFP : PROC_FREEPAGETABLE) (Walkaddr : WALKADDR)
                  (Flags2perm : FLAGS2PERM) (Uvmalloc : UVMALLOC)
                  (Uvmclear : UVMCLEAR) (Strlen : STRLEN) (Copyout : COPYOUT)
                  (SS : SAFESTRCPY) (PN : PANIC) (NT : NAMEI_TR)
                  : KEXEC_PINNED.

(* [NT] is threaded straight through to phase A, the only phase that uses the
   pinned walk.  See [ProofKexecPinnedA.v] for why it is a parameter. *)
Module PA := ProofKexecPinnedA.KexecPinnedAProof Myproc BeginOp Namei Ilock
                                                 Readi Iunlockput EndOp NT.
Module PB := ProofKexecB.KexecBProof Myproc BeginOp Namei Ilock Readi
                                     Iunlockput EndOp PPT.
Module PB2 := ProofKexecB2.KexecB2Proof Myproc BeginOp Namei Ilock Readi
                                        Iunlockput EndOp PFP Walkaddr PN.
Module PB3 := ProofKexecB3.KexecB3Proof Myproc BeginOp Namei Ilock Readi
                                        Iunlockput EndOp PFP Walkaddr
                                        Flags2perm Uvmalloc PB2.
Module PC := ProofKexecC.KexecCProof Myproc BeginOp Namei Ilock Readi
                                     Iunlockput EndOp PFP Walkaddr Flags2perm
                                     Uvmalloc Uvmclear Strlen Copyout.
Module PD := ProofKexecD.KexecDProof PFP SS.

(* ===================================================================== *)
(*  PHASES C AND D, as one lemma over phase B's output state.             *)
(*                                                                        *)
(*  Its own section, and [CID0] a LEMMA binder rather than a section       *)
(*  variable: phase B's two paths reach +0x1ae at two different harts, a   *)
(*  dozen [wp_next]s past the entry one, and a [Local Lemma] declared      *)
(*  under a section [Context `{CID0 : CpuId}] bakes THAT hart into its own *)
(*  statement (projects/kexec.md's note at [kxc_c_exit_m1]).               *)
(* ===================================================================== *)
Section KexecTail.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  (* ------------------------------------------------------------------ *)
  (*  +0x272 .. ret -- the closing copyout and the commit.                *)
  (*  Both of the argv loop's entries land here (the loop's natural exit  *)
  (*  and the [argv[0] = NULL] skip), so it is a lemma rather than two    *)
  (*  copies of the same two [iApply]s.                                   *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_d_tail `{CID0 : CpuId}
      (Q : mword 64 -> Prop)
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (sz1 : mword 64) (c : nat) :
    (* the ENTRY-POINT OBLIGATION, and the only site in the cone that
       pays it: the commit block's [ld a4,-408(s0)] loads exactly
       [kxq_entry ef], so what [kexec_ok_q Q]'s success arm asks for is a
       fact about the ELF HEADER THIS WALK READ.  Every [bad:] tail is
       generic for free and takes no such premise. *)
    Q (kxq_entry ef) ->
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (na < MAXARG)%nat ->
    (8192 <= uint sz1)%Z ->
    (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    kernel_text -∗
    kxc_at_272 jp bn gfs ga gf cov logstart bmapstart inodestart size
               plen pfun na avf alen aslen afun pidv V eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P (pv_sz V) sz1 c -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) eb ∅ -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jp) -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13.
    iIntros "#Htext Hst Hcont".
    iApply (PC.kxc_c_close (CID0 := CID0) Q jp bn gfs ga gf cov logstart
              bmapstart inodestart size plen pfun na avf alen aslen afun
              pidv V eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P (pv_sz V) sz1 c
              HK Hsz1ge Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
              with "Htext Hst Hcont []").
    iIntros (CIDd) "%Hsd". iIntros (Md Pd) "Hst2a6 Hcont".
    iApply (PD.kxd_phaseD (CID0 := CIDd) Q jp bn gfs ga gf cov logstart
              bmapstart inodestart size plen pfun na avf alen aslen afun
              pidv V eb dqb dqs dqa dqpv dqas m Md K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef Pd sz1 c
              HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
              with "Htext Hst2a6 Hcont").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  +0x1ae .. ret -- PHASES C AND D, over phase B's output state.       *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_cd `{CID0 : CpuId}
      (Q : mword 64 -> Prop)
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (szv : mword 64) :
    (* the ENTRY-POINT OBLIGATION, and the only site in the cone that
       pays it: the commit block's [ld a4,-408(s0)] loads exactly
       [kxq_entry ef], so what [kexec_ok_q Q]'s success arm asks for is a
       fact about the ELF HEADER THIS WALK READ.  Every [bad:] tail is
       generic for free and takes no such premise. *)
    Q (kxq_entry ef) ->
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (na < MAXARG)%nat ->
    (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
    avf na = (mword_of_int 0 : mword 64) ->
    (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
    (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
    (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    kernel_text -∗
    kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
               plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) eb ∅ -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jp) -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HQe HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
           Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13.
    iIntros "#Htext Hst Hcont".
    (* the two pure facts the blocks past [kxc_c_setup] take as PREMISES --
       the bitmap-set inclusion and the ustack's eight-alignment -- are
       conjuncts of the entry state, so read them off and put the state
       back together.  No [iFrame]: at this altitude it does not terminate
       (projects/kexec.md). *)
    rewrite /kxc_at_1ae.
    iDestruct "Hst" as "(%Hregs & %Hal & %Hpure3 & Hrest)".
    iAssert (kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
               plen pfun na avf aslen afun pidv V eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv)
      with "[Hrest]" as "Hst".
    { rewrite /kxc_at_1ae.
      iSplitR; [iPureIntro; exact Hregs |].
      iSplitR; [iPureIntro; exact Hal |].
      iSplitR; [iPureIntro; exact Hpure3 |].
      iExact "Hrest". }
    iApply (PC.kxc_c_setup (CID0 := CID0) Q jp bn gfs ga gf cov logstart
              bmapstart inodestart size plen pfun na avf alen aslen
              afun pidv V eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv
              HK Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
              Halen_b Halen_c Halen_4 Havf_na
              with "Htext Hst Hcont []").
    iIntros (CID1) "%Hs1". iIntros (M1 P1 sz1) "%Hsz1ge Hdisj Hcont".
    iDestruct "Hdisj" as "[Hloop | Hskip]".
    - (* argv[0] <> NULL: run the loop from c = 0 *)
      (* [0 < na] is not a conjunct of the head and cannot be: what says it
         is the head's own [avf 0 <> 0] against the contract's [avf na = 0]. *)
      rewrite /kxc_at_21a.
      iDestruct "Hloop" as "(%Hq1 & %Hq2 & %Hq3 & Hrest2)".
      assert (H0na : (0 < na)%nat).
      { destruct Hq2 as (_ & _ & Hnz & _).
        destruct (Nat.eq_dec 0 na) as [Heq | Hne];
          [ exfalso; apply Hnz; rewrite Heq; exact Havf_na | lia ]. }
      iAssert (kxc_at_21a jp bn gfs ga gf cov logstart bmapstart inodestart
                 size plen pfun na avf alen aslen afun pidv V eb dqb dqs dqa dqpv dqas
                 M1 K sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P1 (pv_sz V) sz1 0)
        with "[Hrest2]" as "Hloop".
      { rewrite /kxc_at_21a.
        iSplitR; [iPureIntro; exact Hq1 |].
        iSplitR; [iPureIntro; exact Hq2 |].
        iSplitR; [iPureIntro; exact Hq3 |].
        iExact "Hrest2". }
      iApply (PC.kxc_argv_loop (CID0 := CID1) Q jp bn gfs ga gf cov logstart
                bmapstart inodestart size plen pfun na avf alen aslen
                afun pidv V eb dqb dqs dqa dqpv dqas m K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef (pv_sz V) sz1
                HK Halen_b Halen_c Halen_4 Havf_na Hsz1ge Hnamax Hal
                Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                na M1 P1 0%nat H0na ltac:(lia)
                with "Htext Hloop Hcont []").
      iIntros (CID2) "%Hs2". iIntros (M2 P2 c2) "Hst272 Hcont".
      iApply (kxc_d_tail (CID0 := CID2) Q jp bn gfs ga gf cov logstart bmapstart
                inodestart size plen pfun na avf alen aslen afun pidv V eb
                dqb dqs dqa dqpv dqas m M2 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P2 sz1 c2
                HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                with "Htext Hst272 Hcont").
    - (* argv[0] = NULL: the loop is skipped, and c = 0 *)
      iApply (kxc_d_tail (CID0 := CID1) Q jp bn gfs ga gf cov logstart bmapstart
                inodestart size plen pfun na avf alen aslen afun pidv V eb
                dqb dqs dqa dqpv dqas m M1 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P1 sz1 0
                HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                with "Htext Hskip Hcont").
  Qed.

End KexecTail.
Section KexecPinnedMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  (* the vacuous plug: the landed contract IS the cone at this [Q]. *)
  Notation QT := (fun _ : mword 64 => True) (only parsing).

  Lemma wp_kexec_pinned
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_kexec_pinned_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
                        ga gf cov logstart bmapstart inodestart nib
                        size dev plen pfun na avf alen aslen afun
                        pidv V dqb dqs dqa dqpv dqas m K eb b lks.
  Proof.
    rewrite /wp_kexec_pinned_body.
    intros HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0
           Hcovb Hiregb Hcstr Hplen Hslash Hpelem Havf_nz Havf_na Hnamax
           Halen_b Halen_c Halen_4 Hjp Hgs.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hdvpin Hfvpin Hcont".
    (* THE INDEX IS NO LONGER PINNED BY A PREMISE.  The deleted [b = true ->]
       used to make [b] and [eb] both the literal; what is honest instead is
       that at level 0 they AGREE ([kxc_sie_b_agree]), so [b] is substituted
       away and the whole cone runs at [eb]. *)
    iDestruct (kxc_sie_b_agree m 0%nat K eb b (proc_addr jp) lks
                 with "Hcg Hcnt") as %Houtb.
    cbn in Houtb. subst b.
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 pins the held-lock set empty, which is what every seam past
       phase A spells as the literal [∅]. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlk Hcnt]". subst lks.
    (* ---- PHASE A: +0x000 .. +0x090, and two of the eight [bad:] tails ---- *)
    (* the relation-weakening for the INTACT plug: at [Q := kxp_entry_ok]
       the pinned post's LEFT disjunct is exactly the hypothesis, and it is
       pure -- no resource enters the closure, which is what lets phase A
       hand the exit back unspent. *)
    iAssert (□ (∀ (V' : pprivate) (r entry spv szv' : mword 64),
                  ⌜kexec_ok_q kxp_entry_ok V V' r entry spv szv' na alen⌝ -∗
                  (⌜kexec_ok_q kxp_entry_ok V V' r entry spv szv' na alen⌝
                   ∨ (⌜kexec_ok V V' r entry spv szv' na alen⌝ ∗ kxp_lost))))%I
      as "#Hrelp".
    { iModIntro. iIntros (V' r entry spv szv') "%Hok". by iLeft. }
    iApply (PA.kxc_phaseAp (CID0 := CID0) kxp_entry_ok gs jp gl gu gd gk pd pav pu bn g gfs
              gi cn gtl ga gf cov logstart bmapstart inodestart nib size dev
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas
              m K eb eb ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1)
              (Some init_ef) (fv_cancelled 7 init_bytes) _
              HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml
              Hins0 Hcovb Hiregb Hcstr Hplen Hslash Hpelem Hjp Hgs
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab [Hfvpin] Hka Hbm Hins Hbits Hpriv
                    Hpath Hargv Hargs Hbs Hirs Hdvpin Hcont [] []").
    (* ---- THE CONTENTS ORACLE, at inode 7 ([SpecKexecPinned.kxp_fv_read]):
       the pin is redeemed against the ride the payload carries, the ride
       goes back untouched, and what comes out is either the file's bytes
       (hence the header) or the unforgeable contents receipt. ---- *)
    { iIntros (dn data) "Hride".
      iDestruct "Hfab" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hireg & _)".
      iMod (kxp_fv_read ⊤ gi gfs inodestart nib 7 init_bytes dn data
              ltac:(solve_ndisj) with "Hireg Hfvpin Hride") as "[Hride Hout]".
      iModIntro. iSplitL "Hride"; [iExact "Hride" |].
      iDestruct "Hout" as "[[%Heq _] | #Hc]".
      - iModIntro. iLeft. iPureIntro. cbn. intros j Hj.
        (* [exact], not [rewrite]: the equation closes the goal outright, and
           a [rewrite] would first abstract the occurrence and build a motive
           over the whole [file_byte]/[fv_of] term for conversion to carry --
           5.5 s against nothing.  claude-notes/optimization.md, "[rewrite]
           ABSTRACTS, [exact] only UNIFIES". *)
        exact (fv_of_file_byte dn data init_bytes j Heq
                 ltac:(pose proof init_hdr_len; lia)).
      - iModIntro. iRight. iExact "Hc". }
    (* ...and the unfolding wand at the same [Q]. *)
    { iApply (kxp_body_wand kxp_entry_ok jp ga gf bmapstart inodestart plen pfun
                na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m K eb eb ∅
                (m !!! Regidx Rra) (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                with "Hrelp"). }
    iIntros (CIDa) "%Hsa".
    iIntros (M90 kf qf sf inumf dnf bmf gilf gislf gyf n2 ef intact)
            "%Hregs90 %Hn2 Hpc Hcg Hcnt Hextc Hclmc Hslk Hslked Hdep Hidev Hiinum
             Hival Hloaded Hity Hfrz Hiref Hru Hlog Hirs Hbm Hins Hbits Hbs #Hka2
             Hpriv
             Hpath Hargv Hargs #Hverd Hframe Hcont".
    (* ---- THE VERDICT, NORMALISED.  Three ways in, two ways on. ---- *)
    iAssert (⌜kxq_hdr_ok (Some init_ef) ef⌝ ∨ kxp_lost)%I as "#Hv".
    { destruct intact.
      - iDestruct "Hverd" as "[%Hh | Hc]";
          [by iLeft | iRight; iRight; iExact "Hc"].
      - iRight. iLeft. iExact "Hverd". }
    iDestruct "Hv" as "[%Hhdrok | #Hlost]".
    { (* ---- BOTH LENDS SURVIVED.  The header the walk read is /init's, so
         the commit block's entry load is [init_entry] and the cone runs at
         [Q := kxp_entry_ok]. ---- *)
      iDestruct (kxc_exit_open (proc_addr jp) _ _
                   with "[] Hcont") as "Hcont".
      { iApply (kxp_body_wand kxp_entry_ok jp ga gf bmapstart inodestart plen pfun
                  na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m K eb eb ∅
                  (m !!! Regidx Rra) (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                  with "Hrelp"). }
    destruct Hregs90 as (HM90sp & HM90s0 & HM90s1 & HM90s2 & HM90s4 & Hkf &
                         Hinumf & HM90thr).
    (* the nine resources phase B threads whole and never looks inside *)
    iAssert (kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf
                      bmf gilf gislf)
      with "[Hslk Hslked Hdep Hidev Hiinum Hival Hloaded Hity Hfrz
             Hiref Hru]"
      as "Hopen".
    { rewrite /kxc_open.
      iSplitL "Hslk"; [iExact "Hslk" |].
      iSplitL "Hslked"; [iExact "Hslked" |].

      iSplitL "Hdep"; [iExact "Hdep" |].
      iSplitL "Hidev"; [iExact "Hidev" |].
      iSplitL "Hiinum"; [iExact "Hiinum" |].
      iSplitL "Hival"; [iExact "Hival" |].
      iSplitL "Hloaded"; [iExact "Hloaded" |].
      iSplitL "Hity"; [iExact "Hity" |].
      iSplitL "Hfrz"; [iExact "Hfrz" |].
      iSplitL "Hiref"; [iExact "Hiref" | iExact "Hru"]. }
    (* ---- PHASE B1: +0x090 .. +0x0cc, plus the +0x31c tail ---- *)
    iApply (PB.kxc_b1 (CID0 := CIDa) kxp_entry_ok gs jp gl gu gd gk pd pav pu bn g gfs gi cn
              gtl ga gf cov logstart bmapstart inodestart nib size dev
              kf qf sf gyf inumf dnf bmf gilf gislf n2
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas
              m M90 K eb eb ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1) ef
              HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
              Hkf Hinumf Hn2 eq_refl eq_refl eq_refl eq_refl eq_refl
              HM90sp HM90s0 HM90s1 HM90s2 HM90s4 HM90thr
              with "Htext Hfab Hpc Hcg Hcnt Hextc Hclmc Hopen Hlog Hirs Hbm Hins
                    Hbits Hbs Hka2 Hpriv Hpath Hargv Hargs Hframe Hcont [] []").
    - (* ---- OUTPUT 1: elf.phnum = 0, the phdr loop is skipped ---- *)
      iIntros (CIDz) "%Hsz1". iIntros (Mz Pz w67z) "Hst1a2 Hcont".
      iApply (PB3.kxc_b2z (CID0 := CIDz) gs jp gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gilf gislf ga gf cov logstart bmapstart inodestart
                nib size dev kf qf sf gyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv V eb dqb dqs dqa dqpv dqas
                m Mz K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1) w67z ef Pz
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
                with "Htext Hfab Hst1a2 [Hcont]").
      iIntros (CIDy) "%Hsy". iIntros (My) "Hst1ae".
      iDestruct (wp_next_retarget CIDz CIDy true (proc_addr jp) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (kxc_cd (CID0 := CIDy) kxp_entry_ok jp bn gfs ga gf cov logstart bmapstart
                inodestart size plen pfun na avf alen aslen afun
                pidv V eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                w67z ef Pz (mword_of_int 0 : mword 64)
                (kxq_entry_of_hdr init_ef ef Hhdrok : kxp_entry_ok (kxq_entry ef)) HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
    - (* ---- OUTPUT 2: the phdr loop's body, entered at i = 0, sz = 0 ---- *)
      iIntros (CIDl) "%Hsl". iIntros (Ml Pl) "Hst12c Hcont".
      iApply (PB3.kxc_b2 (CID0 := CIDl) kxp_entry_ok gs jp gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gilf gislf ga gf cov logstart bmapstart inodestart
                nib size dev kf qf sf gyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv V eb dqb dqs dqa dqpv dqas
                m Ml K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (mword_of_int 4095 : mword 64) ef Pl 0%nat
                (mword_of_int 0 : mword 64)
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdev
                eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hfab Hst12c Hcont []").
      iIntros (CIDy) "%Hsy". iIntros (My Py szvy) "Hst1ae Hcont".
      iApply (kxc_cd (CID0 := CIDy) kxp_entry_ok jp bn gfs ga gf cov logstart bmapstart
                inodestart size plen pfun na avf alen aslen afun
                pidv V eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                (mword_of_int 4095 : mword 64) ef Py szvy
                (kxq_entry_of_hdr init_ef ef Hhdrok : kxp_entry_ok (kxq_entry ef)) HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
    }
    { (* ---- A LEND WAS CANCELLED.  Nothing is claimed about the contents;
         the cone runs at the LANDED relation and the caller gets the
         persistent receipt. ---- *)
      iAssert (□ (∀ (V' : pprivate) (r entry spv szv' : mword 64),
                    ⌜kexec_ok_q QT V V' r entry spv szv' na alen⌝ -∗
                    (⌜kexec_ok_q kxp_entry_ok V V' r entry spv szv' na alen⌝
                     ∨ (⌜kexec_ok V V' r entry spv szv' na alen⌝ ∗ kxp_lost))))%I
        as "#Hrell".
      { iModIntro. iIntros (V' r entry spv szv') "%Hok". iRight.
        iSplitR; [iPureIntro; exact (kexec_ok_q_weaken _ _ _ _ _ _ _ _ _ Hok) |].
        iExact "Hlost". }
      iDestruct (kxc_exit_open (proc_addr jp) _ _
                   with "[] Hcont") as "Hcont".
      { iApply (kxp_body_wand QT jp ga gf bmapstart inodestart plen pfun
                  na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas m K eb eb ∅
                  (m !!! Regidx Rra) (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                  with "Hrell"). }
    destruct Hregs90 as (HM90sp & HM90s0 & HM90s1 & HM90s2 & HM90s4 & Hkf &
                         Hinumf & HM90thr).
    (* the nine resources phase B threads whole and never looks inside *)
    iAssert (kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf
                      bmf gilf gislf)
      with "[Hslk Hslked Hdep Hidev Hiinum Hival Hloaded Hity Hfrz
             Hiref Hru]"
      as "Hopen".
    { rewrite /kxc_open.
      iSplitL "Hslk"; [iExact "Hslk" |].
      iSplitL "Hslked"; [iExact "Hslked" |].

      iSplitL "Hdep"; [iExact "Hdep" |].
      iSplitL "Hidev"; [iExact "Hidev" |].
      iSplitL "Hiinum"; [iExact "Hiinum" |].
      iSplitL "Hival"; [iExact "Hival" |].
      iSplitL "Hloaded"; [iExact "Hloaded" |].
      iSplitL "Hity"; [iExact "Hity" |].
      iSplitL "Hfrz"; [iExact "Hfrz" |].
      iSplitL "Hiref"; [iExact "Hiref" | iExact "Hru"]. }
    (* ---- PHASE B1: +0x090 .. +0x0cc, plus the +0x31c tail ---- *)
    iApply (PB.kxc_b1 (CID0 := CIDa) QT gs jp gl gu gd gk pd pav pu bn g gfs gi cn
              gtl ga gf cov logstart bmapstart inodestart nib size dev
              kf qf sf gyf inumf dnf bmf gilf gislf n2
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa dqpv dqas
              m M90 K eb eb ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1) ef
              HK Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
              Hkf Hinumf Hn2 eq_refl eq_refl eq_refl eq_refl eq_refl
              HM90sp HM90s0 HM90s1 HM90s2 HM90s4 HM90thr
              with "Htext Hfab Hpc Hcg Hcnt Hextc Hclmc Hopen Hlog Hirs Hbm Hins
                    Hbits Hbs Hka2 Hpriv Hpath Hargv Hargs Hframe Hcont [] []").
    - (* ---- OUTPUT 1: elf.phnum = 0, the phdr loop is skipped ---- *)
      iIntros (CIDz) "%Hsz1". iIntros (Mz Pz w67z) "Hst1a2 Hcont".
      iApply (PB3.kxc_b2z (CID0 := CIDz) gs jp gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gilf gislf ga gf cov logstart bmapstart inodestart
                nib size dev kf qf sf gyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv V eb dqb dqs dqa dqpv dqas
                m Mz K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1) w67z ef Pz
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
                with "Htext Hfab Hst1a2 [Hcont]").
      iIntros (CIDy) "%Hsy". iIntros (My) "Hst1ae".
      iDestruct (wp_next_retarget CIDz CIDy true (proc_addr jp) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (kxc_cd (CID0 := CIDy) QT jp bn gfs ga gf cov logstart bmapstart
                inodestart size plen pfun na avf alen aslen afun
                pidv V eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                w67z ef Pz (mword_of_int 0 : mword 64)
                I HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
    - (* ---- OUTPUT 2: the phdr loop's body, entered at i = 0, sz = 0 ---- *)
      iIntros (CIDl) "%Hsl". iIntros (Ml Pl) "Hst12c Hcont".
      iApply (PB3.kxc_b2 (CID0 := CIDl) QT gs jp gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gilf gislf ga gf cov logstart bmapstart inodestart
                nib size dev kf qf sf gyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv V eb dqb dqs dqa dqpv dqas
                m Ml K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (mword_of_int 4095 : mword 64) ef Pl 0%nat
                (mword_of_int 0 : mword 64)
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs Hdev
                eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hfab Hst12c Hcont []").
      iIntros (CIDy) "%Hsy". iIntros (My Py szvy) "Hst1ae Hcont".
      iApply (kxc_cd (CID0 := CIDy) QT jp bn gfs ga gf cov logstart bmapstart
                inodestart size plen pfun na avf alen aslen afun
                pidv V eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                (mword_of_int 4095 : mword 64) ef Py szvy
                I HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
    }
  Qed.

End KexecPinnedMain.
End KexecPinnedProof.
