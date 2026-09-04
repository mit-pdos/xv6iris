(* ===================================================================== *)
(*  ProofKexecPin.v -- kexec AT A PINNED PATH, ASSEMBLED.                 *)
(*  (fs-syscall-specs, PINNED-EXEC PROVER lane; SpecKexecPin.v sect. 8)   *)
(* ===================================================================== *)

(*  [ProofKexec.wp_kexec_sconf]'s composition run at [Q := Q_pin pb], which
    is what sect. 8 says it is: the cone has been generic in [Q] since the
    exit-generic sweep, so phases B / B2 / B3 / C / D and all eight [bad:]
    tails apply UNCHANGED, and the file below is [ProofKexec.v]'s two
    sections with four differences and no fifth:

      (1) THE ONE PAYING SITE.  [kxc_cd] takes [Q (kxq_entry ef)]; the
          landed run discharges it with [I] and this one with
          [SpecKexecPin.Q_pin_of_hdr pb ef Hhp], where [Hhp] is the header
          claim phase A published -- [HD := Some (kxp_ef pb)],
          [XCH := ⌜False⌝], exactly sect. 8 (1).

      (2) PHASE A IS THE PINNED ONE ([ProofKexecPinA.kxc_phaseAp]), which
          takes the pin where the landed block takes a header oracle, and
          answers the oracle itself.  That is the ONLY block that is not
          the landed one.

      (3) NO [kxc_exit_qgen].  The landed contract's caller hands a
          [kexec_ok]-shaped continuation; this contract's hands
          [kexec_closer (Q_pin pb)], which IS the cone's own continuation
          at that [Q] -- so the exit travels down unconverted and the
          thirty-one relays carry it with no restatement whatever.

      (4) THE PREMISE IS THE CHAIN PIN, not [SpecKexecPin.kxp_view_pin] --
          see [ProofKexecPinTrace]'s header for WHY (the endpoint pin does
          not survive a multi-hop walk, and the counterexample is written
          out there).  The contract carries that repair: [kxp_run_pin] is
          [SpecKexecPin.wp_kexec_pinned_body]'s premise, so the general
          sentence is TRUE at every path length and this functor is sealed
          to [KEXEC_PIN] like any other.  The endpoint premise survives as

              [wp_kexec_pinned_1hop]

          -- the Module Type's second export -- which follows for every
          ONE-ELEMENT path, i.e. for both era-0 instances
          ([FsInitPin.init_path = ["init"]], [FsShPin.sh_path = ["sh"]])
          and hence for everything /init and forkret actually ask for.  *)
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
Require Import KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import ByteBuf.
Require Import ProcGeom.
Require Import ProcInv.
Require Import Xv6Cameras.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import FileInvDefs.
Require Import SpecKexec.
Require Import KexecBuilt.   (* the argument block's algebra + [kexec_built] *)
Require Import KexecOkQ.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecNamei.
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
(* ---- and the names [SpecKexecPin]'s body is written in that the landed
   assembly never had to spell (it only ever UNFOLDED its contract).
   [SpecKexecPin]'s own order, so the fs-abs stack's shadowing rule is
   respected; [FsAbs] itself is NOT imported -- nothing here names
   [astate] or [aview], those live behind [kxp_run_pin]. ---- *)
Require Import InstrBytes.     (* [pc_is]                            *)
Require Import LogInv.
Require Import LogDefs.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import BioDefs.
Require Import InodeInv.       (* [ROOTDEV], [MAXFILE]               *)
Require Import PathElems.      (* [SLASH], [path_elems]              *)

Require Import DirentEnc.      (* [bview]                            *)
Require Import FsTree.         (* [fname]                            *)
Require Import SpecNameiEra.   (* [NAMEI_ERA]: the functor argument  *)
Require Import SpecKexecPin.   (* THE CONTRACT                       *)
Require Import ProofKexecPinTrace.
Require Import ProofKexecPinA. (* the pinned phase A                 *)
Require FsBytesGamma.          (* [FsBytesGamma.fs_gamma_L]          *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.  (* [fscfg]: the fs configuration is AMBIENT *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.


Notation KX := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  THE CONTRACT'S BODY AT THE HONEST PREMISE.                            *)
(*                                                                        *)
(*  [SpecKexecPin.wp_kexec_pinned_body] VERBATIM with its ONE resource     *)
(*  premise replaced by the chain-carrying reader.  Stated here rather     *)
(*  than in the statement file because R10 freezes what is landed: this    *)
(*  is the drop-in the statement lane can lift, and until it does, the     *)
(*  landed body follows from it on every one-element path                  *)
(*  ([wp_kexec_pinned_1hop]).                                             *)
(* ===================================================================== *)
Definition wp_kexec_pinned_run_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (pb : kx_pin) (ds : list Z)
    (gs : list gname) (jp : nat) (gl : gname)           (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (gf : gname)                                        (* file table          *)
    (plen : nat) (pfun : nat -> bv 8)                   (* the path buffer     *)
    (na : nat) (avf : nat -> mword 64)                  (* argv[0 .. na]       *)
    (alen : nat -> nat) (aslen : nat -> nat)            (* strlen / owned len  *)
    (afun : nat -> nat -> bv 8)                         (* the argument bytes  *)
    (pidv : mword 32) (U : ustate)
    (dqb dqs dqa dqpv dqas : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kexec in
  let pj := proc_addr jp in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let av := m !!! Regidx (mword_of_int 11 : mword 5) in   (* a1 = argv *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kexec <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* ---- the path ---- *)
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ---- AND THE PATH IS THE PINNED ONE ----
     absolute (the pins are stated from the root; the relative twin is
     the recorded [FsAbsStart]-shaped parallel form) and spelling exactly
     the pinned elements.  A caller holding the .rodata literal
     discharges both by computation, as the dead contract's callers did. *)
  pfun 0%nat = SLASH ->
  path_elems (bview plen pfun) = kxp_path pb ->
  (* ---- and the pinned file has a whole ELF header: without this the
     oracle's verdict about the first 64 bytes would be unprovable (a
     shorter pinned file makes the header readi short -- a run the
     machine sends to [bad:], but the verdict is produced before the
     length test).  [pin_init_hdr_len]/[pin_sh_hdr_len] discharge it. *)
  (64 <= length (kxp_bytes pb))%nat ->
  (* ---- the argument vector: [na] non-null pointers then a NULL ---- *)
  (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
  avf na = (mword_of_int 0 : mword 64) ->
  (na < MAXARG)%nat ->
  (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
  (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
  (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
  (* ---- the running process ---- *)
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  fs_fabric gs pd pav pu -∗
  kalloc_env fsc_kalloc None -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  proc_priv gf pj pidv U -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
  ([∗ list] i ∈ seq 0 na,
     [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  (* ==== THE PIN: one persistent reader (section 4).  Persistent, so it
     costs the caller nothing to duplicate into the walk. ==== *)
  kxp_run_pin (FsBytesGamma.fs_gamma_L fsc_fs) pb ds -∗
  (* ==== the moved image, at the PINNED relation.  [kexec_closer
     (Q_pin pb) ...] unfolds to the landed continuation verbatim with
     [kexec_ok_q (Q_pin pb)] in the pure slot: the [-1] arm is the landed
     failure arm character for character, and the success arm carries
     [entry = kxp_entry pb] in front ([kexec_ok_pin_read]). ==== *)
  wp_next true pj (fun (CID : CpuId) =>
    kexec_closer (kxp_entry_ok pb) gf fsc_kalloc pj pidv U m ret_tgt K b eb
                 lks dqb dqs fsc_bmapstart na alen plen pv dqpv pfun
                 av dqa avf aslen dqas afun) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE PROOF.  [ProofKexec.KexecProof]'s functor with ONE extra argument  *)
(*  ([NAMEI_ERA], the era-traced namei the pinned walk calls) and the      *)
(*  pinned phase A in place of the landed one; every other callee, and     *)
(*  every other block, is the landed one at the pinned [Q].                *)
(*                                                                        *)
(*  SEALED TO [KEXEC_PIN]: its two Parameters are [wp_kexec_pinned] and    *)
(*  [wp_kexec_pinned_1hop] below; everything else here is internal.        *)
(* ===================================================================== *)
Module KexecPinProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                     (NE : NAMEI_ERA)
                     (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                     (EndOp : END_OP) (PPT : PROC_PAGETABLE_GEN)
                     (PFP : PROC_FREEPAGETABLE) (Walkaddr : WALKADDR)
                     (Flags2perm : FLAGS2PERM) (Uvmalloc : UVMALLOC)
                     (Uvmclear : UVMCLEAR) (Strlen : STRLEN) (Copyout : COPYOUT)
                     (SS : SAFESTRCPY) (PN : PANIC) : KEXEC_PIN.

Module PA := ProofKexecPinA.KexecPinAProof Myproc BeginOp Namei NE Ilock Readi
                                           Iunlockput EndOp.
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
Section KexecPinTail.
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
  Local Lemma kxc_d_tail `{CID0 : CpuId} `{XI : CurCtx}
      (Q : mword 64 -> ustate -> Prop)
      (jp : nat) (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (Mi : gmap Z (bv 8)) (sz1 : mword 64) (c : nat) :
    (* the ENTRY-POINT OBLIGATION, and the only site in the cone that
       pays it: the commit block's [ld a4,-408(s0)] loads exactly
       [kxq_entry ef], so what [kexec_ok_q Q]'s success arm asks for is a
       fact about the ELF HEADER THIS WALK READ.  Every [bad:] tail is
       generic for free and takes no such premise.

       THE PREMISE IS GUARDED BY WHAT THE RUN BUILT (S3), exactly as
       [ProofKexec.kxc_d_tail]'s is; [Q_pin] ignores the state, so the pin's
       own instantiation just drops the guard. *)
    (forall U' : ustate, kexec_built sz1 na alen afun U' -> Q (kxq_entry ef) U') ->
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
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 ->
    kernel_text -∗
    kxc_at_272 jp gf
               plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P Mi (pv_sz (us_V U)) sz1 (m !!! Regidx Rs11) c -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      KexecOkQ.kexec_closer Q gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K
           eb eb ∅ dqb dqs fsc_bmapstart na alen plen pv dqpv
           pfun av dqa avf aslen dqas afun) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12.
    iIntros "#Htext Hst Hcont".
    iApply (PC.kxc_c_close (CID0 := CID0) Q jp gf
 plen pfun na avf alen aslen afun
              pidv U eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P Mi (pv_sz (us_V U)) sz1 c
              HK Hsz1ge Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
              with "Htext Hst Hcont []").
    iIntros (CIDd) "%Hsd". iIntros (Md Pd Mid) "Hst2a6 Hcont".
    iApply (PD.kxd_phaseD (CID0 := CIDd) Q jp gf
 plen pfun na avf alen aslen afun
              pidv U eb dqb dqs dqa dqpv dqas m Md K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef Pd Mid sz1 c
              HQe HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
              with "Htext Hst2a6 Hcont").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  +0x1ae .. ret -- PHASES C AND D, over phase B's output state.       *)
  (* ------------------------------------------------------------------ *)
  Local Lemma kxc_cd `{CID0 : CpuId} `{XI : CurCtx}
      (Q : mword 64 -> ustate -> Prop)
      (jp : nat) (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate) (eb : bool) (dqb dqs dqa dqpv dqas : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (Mi : gmap Z (bv 8)) (szv : mword 64) :
    (* the ENTRY-POINT OBLIGATION, and the only site in the cone that
       pays it: the commit block's [ld a4,-408(s0)] loads exactly
       [kxq_entry ef], so what [kexec_ok_q Q]'s success arm asks for is a
       fact about the ELF HEADER THIS WALK READ.  Every [bad:] tail is
       generic for free and takes no such premise.

       THE PREMISE IS GUARDED BY WHAT THE RUN BUILT (S3), with the stack
       top still ∀-bound here -- [kxc_c_setup]'s uvmalloc picks it. *)
    (forall (szg : mword 64) (U' : ustate),
       kexec_built szg na alen afun U' -> Q (kxq_entry ef) U') ->
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
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 ->
    kernel_text -∗
    kxc_at_1ae jp gf
               plen pfun na avf aslen afun pidv U eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P Mi szv (m !!! Regidx Rs11) -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      KexecOkQ.kexec_closer Q gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K
           eb eb ∅ dqb dqs fsc_bmapstart na alen plen pv dqpv
           pfun av dqa avf aslen dqas afun) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HQe HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
           Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12.
    iIntros "#Htext Hst Hcont".
    (* the two pure facts the blocks past [kxc_c_setup] take as PREMISES --
       the bitmap-set inclusion and the ustack's eight-alignment -- are
       conjuncts of the entry state, so read them off and put the state
       back together.  No [iFrame]: at this altitude it does not terminate
       (projects/kexec.md). *)
    rewrite /kxc_at_1ae.
    iDestruct "Hst" as "(%Hregs & %Hal & %Hpure3 & Hrest)".
    iAssert (kxc_at_1ae jp gf
               plen pfun na avf aslen afun pidv U eb dqb dqs dqa dqpv dqas
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P Mi szv (m !!! Regidx Rs11))
      with "[Hrest]" as "Hst".
    { rewrite /kxc_at_1ae.
      iSplitR; [iPureIntro; exact Hregs |].
      iSplitR; [iPureIntro; exact Hal |].
      iSplitR; [iPureIntro; exact Hpure3 |].
      iExact "Hrest". }
    iApply (PC.kxc_c_setup (CID0 := CID0) Q jp gf
 plen pfun na avf alen aslen
              afun pidv U eb dqb dqs dqa dqpv dqas m M K sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P Mi szv
              HK Hmsp Hmra Hms0 Hms1 Hms2
              Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
              Halen_b Halen_c Halen_4 Havf_na
              with "Htext Hst Hcont []").
    iIntros (CID1) "%Hs1". iIntros (M1 P1 Mim1 sz1) "%Hsz1ge Hdisj Hcont".
    iDestruct "Hdisj" as "[Hloop | Hskip]".
    - (* argv[0] <> NULL: run the loop from c = 0 *)
      (* [0 < na] is not a conjunct of the head and cannot be: what says it
         is the head's own [avf 0 <> 0] against the contract's [avf na = 0]. *)
      rewrite /kxc_at_21a.
      iDestruct "Hloop" as "(%Hq1 & %Hq2 & %Hq3 & %Hq4 & Hrest2)".
      assert (H0na : (0 < na)%nat).
      { destruct Hq2 as (_ & _ & Hnz & _).
        destruct (Nat.eq_dec 0 na) as [Heq | Hne];
          [ exfalso; apply Hnz; rewrite Heq; exact Havf_na | lia ]. }
      iAssert (kxc_at_21a jp gf
 plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
                 M1 K sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P1 Mim1 (pv_sz (us_V U)) sz1 (m !!! Regidx Rs11) 0)
        with "[Hrest2]" as "Hloop".
      { rewrite /kxc_at_21a.
        iSplitR; [iPureIntro; exact Hq1 |].
        iSplitR; [iPureIntro; exact Hq2 |].
        iSplitR; [iPureIntro; exact Hq3 |].
        iSplitR; [iPureIntro; exact Hq4 |].
        iExact "Hrest2". }
      iApply (PC.kxc_argv_loop (CID0 := CID1) Q jp gf
 plen pfun na avf alen aslen
                afun pidv U eb dqb dqs dqa dqpv dqas m K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef (pv_sz (us_V U)) sz1
                HK Halen_b Halen_c Halen_4 Havf_na Hsz1ge Hnamax Hal
                Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
                na M1 P1 Mim1 0%nat H0na ltac:(lia)
                with "Htext Hloop Hcont []").
      iIntros (CID2) "%Hs2". iIntros (M2 P2 Mim2 c2) "Hst272 Hcont".
      iApply (kxc_d_tail (CID0 := CID2) Q jp gf
 plen pfun na avf alen aslen afun pidv U eb
                dqb dqs dqa dqpv dqas m M2 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P2 Mim2 sz1 c2
                (HQe sz1) HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
                with "Htext Hst272 Hcont").
    - (* argv[0] = NULL: the loop is skipped, and c = 0 *)
      iApply (kxc_d_tail (CID0 := CID1) Q jp gf
 plen pfun na avf alen aslen afun pidv U eb
                dqb dqs dqa dqpv dqas m M1 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P1 Mim1 sz1 0
                (HQe sz1) HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12
                with "Htext Hskip Hcont").
  Qed.

End KexecPinTail.

Section KexecPinMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

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

  (* WHERE [ProofKexec] WRITES [QT] THIS FILE WRITES [kxp_entry_ok pb], and
     that substitution -- plus the one paying site's premise -- is the whole
     of the difference through phases B / B2 / B3 / C / D. *)

  Lemma wp_kexec_pinned_run
      (pb : kx_pin) (ds : list Z)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
 (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_kexec_pinned_run_body pb ds gs jp gl pd pav pu
 gf
 plen pfun na avf alen aslen afun
                        pidv U dqb dqs dqa dqpv dqas m K eb b lks.
  Proof.
    rewrite /wp_kexec_pinned_run_body.
    intros HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0
           Hcovb Hiregb Hcstr Hplen Hslash Hpl Hhlen Havf_nz Havf_na Hnamax
           Halen_b Halen_c Halen_4 Hjp Hgs.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs #Hrp Hcont".
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
    (* ---- NO [kxc_exit_qgen] HERE.  The landed contract's caller hands a
       [kexec_ok]-shaped continuation and that step moves it to the generic
       relation; THIS contract's caller already hands [kexec_closer
       (Q_pin pb)] -- which IS the cone's own continuation shape at that
       [Q] (KexecOkQ sect. 1a, transparent).  So the exit travels down
       unconverted and the thirty-one relays carry it unrestated. ---- *)
    (* ---- PHASE A: +0x000 .. +0x090, and two of the eight [bad:] tails ---- *)
    iApply (PA.kxc_phaseAp (CID0 := CID0) (kxp_entry_ok pb) pb ds
              gs jp gl pd pav pu
 gf
              plen pfun na avf alen aslen afun pidv U dqb dqs dqa dqpv dqas
              m K eb eb ∅
              (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) (m !!! Regidx Rs2)
              (m !!! Regidx Ra0) (m !!! Regidx Ra1) _
              HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml
              Hins0 Hcovb Hiregb Hcstr Hplen Hjp Hgs Hpl Hslash Hhlen
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab Hrp Hka Hbm Hins Hbits Hpriv
                    Hpath Hargv Hargs Hbs Hirs Hcont []").
    (* NO ORACLE BRACKET: the pinned phase A owns its verdict (it takes the
       pin where the landed block takes an oracle).  What is left is the
       exit's unfolding wand, and it is the identity -- [KEX] IS this
       contract's own continuation. *)
    { iModIntro. iIntros (CX) "H". iExact "H". }
    iIntros (CIDa) "%Hsa".
    iIntros (M90 kf qf sf inumf dnf bmf gilf gislf gyf loyf tlyf n2 ef)
            "%Hregs90 %Hn2 Hpc Hcg Hcnt Hextc Hclmc Hslk Hslked %Hle90 #Hfl90 #Hclaims90 Hdep Hoffr Hidev Hiinum
             Hival Hloaded Hity Hfrz Hiref Hru Hlog Hirs Hbm Hins Hbits Hbs #Hka2
             Hpriv
             Hpath Hargv Hargs #Hhdr Hframe Hcont".
    (* ---- THE ONE PAYING SITE'S INPUT.  Phase A published the pinned
       header claim; [XCH] is [⌜False⌝] here, so the right disjunct is
       refuted rather than carried, and what survives is exactly the
       premise [Q_pin_of_hdr] wants. ---- *)
    iDestruct "Hhdr" as "[%Hhp | %Hfalse]"; [| done].
    destruct Hregs90 as (HM90sp & HM90s0 & HM90s1 & HM90s2 & HM90s4 & Hkf &
                         Hinumf & HM90thr).
    (* the nine resources phase B threads whole and never looks inside *)
    iAssert (kxc_open pidv kf qf sf gyf loyf tlyf inumf dnf
                      bmf gilf gislf)
      with "[Hslk Hslked Hdep Hoffr Hidev Hiinum Hival Hloaded Hity Hfrz
             Hiref Hru]"
      as "Hopen".
    { rewrite /kxc_open.
      iSplitL "Hslk"; [iExact "Hslk" |].
      iSplitL "Hslked"; [iExact "Hslked" |].
      iSplitR; [iPureIntro; exact Hle90 |].
      iSplitR; [iExact "Hfl90" |].
      iSplitR; [iExact "Hclaims90" |].

      iSplitL "Hdep"; [iExact "Hdep" |].
      iSplitL "Hoffr"; [iExact "Hoffr" |].
      iSplitL "Hidev"; [iExact "Hidev" |].
      iSplitL "Hiinum"; [iExact "Hiinum" |].
      iSplitL "Hival"; [iExact "Hival" |].
      iSplitL "Hloaded"; [iExact "Hloaded" |].
      iSplitL "Hity"; [iExact "Hity" |].
      iSplitL "Hfrz"; [iExact "Hfrz" |].
      iSplitL "Hiref"; [iExact "Hiref" | iExact "Hru"]. }
    (* ---- PHASE B1: +0x090 .. +0x0cc, plus the +0x31c tail ---- *)
    iApply (PB.kxc_b1 (CID0 := CIDa) (kxp_entry_ok pb) gs jp gl pd pav pu
 gf
              kf qf sf gyf loyf tlyf inumf dnf bmf gilf gislf n2
              plen pfun na avf alen aslen afun pidv U dqb dqs dqa dqpv dqas
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
      iIntros (CIDz) "%Hsz1". iIntros (Mz Pz Miz w13z w67z) "Hst1a2 Hcont".
      iApply (PB3.kxc_b2z (CID0 := CIDz) gs jp gl pd pav pu
                gilf gislf gf
 kf qf sf gyf loyf tlyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
                m Mz K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1) w13z w67z ef Pz Miz
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
                with "Htext Hfab Hst1a2 [Hcont]").
      iIntros (CIDy) "%Hsy". iIntros (My) "Hst1ae".
      iDestruct (wp_next_retarget CIDz CIDy true (proc_addr jp) _
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (kxc_cd (CID0 := CIDy) (kxp_entry_ok pb) jp gf
 plen pfun na avf alen aslen afun
                pidv U eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) w13z
                w67z ef Pz Miz (mword_of_int 0 : mword 64)
                (fun _ U' _ => Q_pin_of_hdr pb ef Hhp U') HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
    - (* ---- OUTPUT 2: the phdr loop's body, entered at i = 0, sz = 0 ---- *)
      iIntros (CIDl) "%Hsl". iIntros (Ml Pl Mil) "Hst12c Hcont".
      iApply (PB3.kxc_b2 (CID0 := CIDl) (kxp_entry_ok pb) gs jp gl pd pav pu
                gilf gislf gf
 kf qf sf gyf loyf tlyf inumf dnf bmf n2
                plen pfun na avf alen aslen afun pidv U eb dqb dqs dqa dqpv dqas
                m Ml K (m !!! Regidx csp_rs1) (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (mword_of_int 4095 : mword 64) ef Pl Mil 0%nat
                (mword_of_int 0 : mword 64)
                HK Hkf Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hjp Hgs
                eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hfab Hst12c Hcont []").
      iIntros (CIDy) "%Hsy". iIntros (My Py Miy szvy) "Hst1ae Hcont".
      iApply (kxc_cd (CID0 := CIDy) (kxp_entry_ok pb) jp gf
 plen pfun na avf alen aslen afun
                pidv U eb dqb dqs dqa dqpv dqas m My K
                (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2)
                (m !!! Regidx Ra0) (m !!! Regidx Ra1)
                (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                (mword_of_int 4095 : mword 64) ef Py Miy szvy
                (fun _ U' _ => Q_pin_of_hdr pb ef Hhp U') HK Hcstr Hnamax Havf_nz Havf_na Halen_b Halen_c Halen_4
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                with "Htext Hst1ae Hcont").
  Qed.

  (*  THE SEALED NAME: [SpecKexecPin.wp_kexec_pinned_body] is the run body
      lifted into the contract (the chain repair), so the Parameter's
      sentence IS [wp_kexec_pinned_run]'s, definitionally. *)
  Lemma wp_kexec_pinned
      (pb : kx_pin) (ds : list Z)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    SpecKexecPin.wp_kexec_pinned_body pb ds gs jp gl pd pav pu gf plen pfun
                        na avf alen aslen afun
                        pidv U dqb dqs dqa dqpv dqas m K eb b lks.
  Proof.
    exact (wp_kexec_pinned_run pb ds gs jp gl pd pav pu gf plen pfun na avf
             alen aslen afun pidv U dqb dqs dqa dqpv dqas m K eb b lks).
  Qed.
  (* =================================================================== *)
  (*  THE RECEIPT: THE LANDED BODY, ON A ONE-ELEMENT PATH.                *)
  (*                                                                      *)
  (*  [SpecKexecPin.wp_kexec_pinned_body] quoted verbatim -- the Module    *)
  (*  Type's own sentence -- under the one side condition that makes its   *)
  (*  premise honest.  Both era-0 instances satisfy it by [reflexivity]:   *)
  (*  [kxp_path pin_init = FsInitPin.init_path = ["init"]] and             *)
  (*  [kxp_path (pin_sh FsShPin.sh_path i) = ["sh"]].                      *)
  (* =================================================================== *)
  Lemma wp_kexec_pinned_1hop
      (pb : kx_pin) (s : fname)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    kxp_path pb = [s] ->
    wp_kexec_pinned_view_body pb gs jp gl pd pav pu gf plen pfun na avf
                         alen aslen afun pidv U dqb dqs dqa dqpv dqas m K eb b lks.
  Proof.
    intros Hps. rewrite /wp_kexec_pinned_view_body.
    intros HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hcstr
           Hplen Hslash Hpl Hhlen Havf_nz Havf_na Hnamax Halen_b Halen_c
           Halen_4 Hjp Hgs.
    iIntros "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs #Hpin Hcont".
    (* the landed premise IS the chain premise here (one hop) *)
    iDestruct (kxp_run_pin_of_view (FsBytesGamma.fs_gamma_L fsc_fs) pb s Hps
                 with "Hpin") as "#Hrp".
    iApply (wp_kexec_pinned_run pb [FsImg.ROOTINO; kxp_ino pb]
              gs jp gl pd pav pu gf plen pfun na avf alen aslen afun pidv U
              dqb dqs dqa dqpv dqas m K eb b lks
              HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hcstr
              Hplen Hslash Hpl Hhlen Havf_nz Havf_na Hnamax Halen_b Halen_c
              Halen_4 Hjp Hgs
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab Hka Hbm Hins Hbits
                    Hpriv Hpath Hargv Hargs Hbs Hirs Hrp Hcont").
  Qed.

  (* The two era-0 instances of the side condition are pure facts about the
     pins, so they live beside them: [SpecKexecPin.pin_init_one_hop] and
     [SpecKexecPin.pin_sh_one_hop]. *)

End KexecPinMain.

End KexecPinProof.
