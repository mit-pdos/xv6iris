(* ===================================================================== *)
(*  ProofKexecPinA.v -- PHASE A OF kexec, AT A PINNED PATH.               *)
(*  (fs-syscall-specs, PINNED-EXEC PROVER lane; SpecKexecPin.v sect. 8)   *)
(* ===================================================================== *)

(*  ProofKexecA's [kxc_a1] and [kxc_phaseA] with ONE CALL SWAPPED and ONE
    PREMISE ADDED, which is the whole of what "the pinned walk" costs:

      * [kxc_a1p] calls [SpecNameiEra.wp_namei_era] instead of
        [SpecNamei.wp_namei_gen].  The two contracts are the same sentence
        ([SpecNameiEra]'s header: "[SpecNamei.wp_namei_gen_body] + the
        trace"), so the call's argument list, its ledger, its fractions and
        its register bookkeeping are UNCHANGED; what the era post adds is
        the walked inum and the cursor at the last hop, and what the seam
        at +0x032 then publishes is [zi = kxp_ino pb].

      * [kxc_phaseAp] does not RELAY a header oracle -- it ANSWERS one.
        [ProofKexecA.kxc_a2] is applied unchanged, at
        [HD := Some (kxp_ef pb)] and [XCH := ⌜False⌝] (there is no lost arm:
        SpecKexecPin sect. 4's premise is not a cancellable resource), and
        the oracle's body is [ProofKexecPinTrace.kxt_hdr_verdict] at the
        inum [kxc_a1p] just identified.

    EVERYTHING ELSE IS ProofKexecA's, INCLUDING BOTH [-1] TAILS: the
    namei-null tail at +0x088 lives inside [kxc_a1p] exactly as it lives
    inside [kxc_a1], and the +0x064 one is [kxc_a2]'s and is not copied at
    all.  The landed blocks are opened as [LA] below and instantiated, not
    duplicated (the copy-adapt discipline of ProofSysMknodAU /
    ProofCreateAUF: copy the WALK, never the block).

    WHY [kxc_a1] CANNOT SIMPLY BE REUSED.  Its post says [inode_held ipv] --
    an inode, no inum -- because [SpecNamei]'s does; the pinned walk needs
    the inum, and no reading of the landed post exposes it.  That is the
    same reason the deleted [ProofKexecPinnedA] existed, and it is why this
    file is +500 lines of the SAME proof rather than a wrapper.

    THE TWO SECTIONS ARE ProofKexecA's TWO SECTIONS, and they have to be:
    [kxc_phaseAp] applies [kxc_a2] AT THE SEAM'S HART, and a sibling lemma
    in a still-open [Context `{CID0 : CpuId}] bakes the section hart into
    its own statement (ProofKexecA's header, durable-notes).             *)
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
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.   (* [is_sleeplock]: the nightly dead-import sweep re-pointed the chain that used to carry it *)
Require Import WpLock.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import ProcGeom.
Require Import Xv6Cameras.
Require Import BioDefs.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY").
   QUALIFIED, NOT IMPORTED (pinned-exec prover lane, 2026-08-29): the
   oracle's widened row is the only place in this file that names them, so
   [Require] without [Import] buys the three names and the collision this
   comment warns about does not arise at all. *)
Require FsBytesGamma.   (* [FsBytesGamma.fs_gamma_L]                       *)
Require Import LogInv.
Require Import BitmapInv.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KvmSpec.
(* Names the nightly dead-import sweep stopped delivering transitively. *)
Require Import DinodeEnc.
Require Import InodeLock.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecIput.
Require Import SpecKexec.
Require Import KexecOkQ.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamei.
(* [SpecNamex] for [walk_need]/[walk_spend]: the SET form's ledger clause is
   namex's, and phase A prices its namei call through it. *)
Require Import SpecNamex.
Require Import ProofKexecTail.
Require Import CodeKexec.
Require Import SpecNameiTr.    (* [inode_held_at] and its readings   *)
Require Import SpecNameiEra.   (* THE ERA WALK: the one call swapped *)
Require Import FsAbsEra.     (* [bview_head_slash_intro]           *)
Require Import SpecKexecPin.   (* the contract this lane serves      *)
Require Import ProofKexecPinTrace.  (* [kxp_run_pin], the trace, the
                                       header verdict               *)
Require Import ProofKexecA.    (* the LANDED blocks, opened as [LA]  *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import TsoCtx.
Require Import OffBox.   (* [off_rows]: the inode's off rows (items 35/36) *)
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.


Notation KXA := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  THE PINNED PHASE A.                                                   *)
(* ===================================================================== *)
Module KexecPinAProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                      (NE : NAMEI_ERA)
                      (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                      (EndOp : END_OP).

(* the shared bottom blocks ([T.kxc_exit_m1] closes [kxc_a1p]'s -1 tail) and
   THE LANDED PHASE A, whose second half ([LA.kxc_a2]) this file applies
   unchanged -- the copy stops at the namei call. *)
Module T := ProofKexecTail.KexecTailProof Myproc BeginOp Namei Ilock Readi
                                          Iunlockput EndOp.
Module LA := ProofKexecA.KexecAProof Myproc BeginOp Namei Ilock Readi
                                     Iunlockput EndOp.

Section KexecPinABody.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* the pinned twin of [IcacheRef.inode_held_ne_zero]: the era post hands
     back the package AT ITS INUM, and the [beqz a0] at +0x030 needs the
     register non-zero either way. *)
  Lemma inode_held_at_ne_zero (v : mword 64) (z : Z) :
    inode_held_at v z -∗ ⌜v <> (zero_reg : mword 64)⌝.
  Proof.
    iIntros "H". iApply inode_held_ne_zero. by iApply inode_held_at_held.
  Qed.

  Lemma kxc_a1p
      (Q : mword 64 -> ustate -> Prop)
      (pb : kx_pin) (ds : list Z)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
 (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (* the exit, opaque -- see the premise below *)
      (KEX : CpuId -> iProp Σ) :
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
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    (* ---- THE PINNED SCOPE.  The buffer spells the pinned path, and
       the path is ABSOLUTE: the chain is stated from the root, and
       [FsAbsStart.ex_start]'s tie fires at [ROOTINO] only for a
       buffer whose head is SLASH ([SpecKexecPin] sect. 7 (ii)). ---- *)
    path_elems (bview plen pfun) = kxp_path pb ->
    pfun 0%nat = SLASH ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Ra0 = pv ->
    m !!! Regidx Ra1 = av ->
    sie_cap_gpr KT1 m K b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jp) -∗
    kernel_text -∗ pc_is (mword_of_int KXA : mword 64) -∗
    fs_fabric gs pd pav pu
 -∗
    kalloc_env fsc_kalloc None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    proc_priv gf (proc_addr jp) pidv U -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
    bslots 3 -∗
    iref_slots 2 -∗
    (* ==== THE PIN, with the chain ([ProofKexecPinTrace]'s header on
       why the endpoint pin alone is not enough).  Persistent, so the
       walk's trace and the header oracle both read it. ==== *)
    kxp_run_pin (FsBytesGamma.fs_gamma_L fsc_fs) pb ds -∗
    (* ---- kexec's OWN continuation: the +0x088 tail closes the -1 arm ---- *)
    (* ---- kexec's OWN continuation, AS AN OPAQUE RESOURCE (N-5.2B,
       §13.4).  Phase A cannot commit to [Q]: the contents verdict is
       learned at the redeem instant INSIDE [kxc_a2], i.e. AFTER the
       point at which a [kexec_ok_q Q]-shaped exit would have fixed
       it -- and the two branches need different [Q]s (the only
       common one is [True], which the pinned post cannot supply
       without a receipt already in hand).  So the exit travels as
       [KEX]; phase A only ever UNFOLDS it, at its own [-1] tails,
       through this persistent wand, and the caller specialises what
       is left at +0x090 where the verdict IS known.  A landed caller
       passes its exit and the identity wand. ---- *)
    wp_next true (proc_addr jp) KEX -∗
    □ (∀ CX : CpuId, KEX CX -∗
      KexecOkQ.kexec_closer Q gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K b
           eb lks dqb dqs fsc_bmapstart na alen plen pv dqpv pfun
           av dqa avf aslen dqas afun) -∗
    (* ---- and the FALL-THROUGH: the state at +0x032.
           IT HANDS THE EXIT BACK.  [Hcont] above is linear and phase A's
           SECOND half owns a [-1] tail of its own (the +0x064 one), so a
           chaining caller cannot keep a copy: exactly [B6.kfk_prologue]'s
           idiom (ProofKforkMain.v's capstone comment) -- the single exit is
           supplied ONCE and whichever continuation runs RECEIVES it.
           [(CID0 := CID)] is mandatory: written bare inside this binder,
           instance resolution would anchor the handed-back [wp_next] at the
           innermost [CpuId] and the guard would degrade to a tautology
           (WpNext.v's note on [wp_next_at]). ---- *)
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M32 : regfile) (ipv : mword 64) (zi : Z) (n1 : nat),
        (* ---- AND THE ONE NEW WORD AT THE SEAM: the inum the walk
           landed on IS the pinned one.  Everything else at +0x032 is
           [kxc_at_a2] unchanged. ---- *)
        ⌜zi = kxp_ino pb⌝ -∗
        kxc_at_a2 jp gf
                  plen pfun na avf aslen afun pidv U dqb dqs dqa dqpv dqas
                  m M32 K eb b lks sp0 ra0 s00 s10 s20 pv av ipv zi n1 -∗
        wp_next (CID0 := CID) true (proc_addr jp) KEX -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hcstr Hplen Hjp Hgs Hpl Hslash Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hka Hbm Hins #Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs #Hrp Hcont #Hkw Hcont32".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* ---- b = eb = true (see the header) ---- *)
    iDestruct (kxc_sie_b_agree m 0%nat K eb b (proc_addr jp) lks with "Hcg Hcnt") as %Houtb.
    cbn in Houtb. subst b.
    (* depth 0 forces the held set empty, so begin_op's order premise ("log",
       3) needs no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct (SpecKexec.fs_fabric_all with "Hfab") as "(#Hkd & #Hpenv & #Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hropen & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock)".
    (* ---- open the process's private block ONCE (convention 2) ---- *)
    (* the BLOCK and the cwd reference: [p->cwd] is one of the block's own
       cells now, so namei borrows it for its own load and nothing here has
       to carry it. *)
    iDestruct (proc_priv_bare_cref gf (proc_addr jp) pidv U with "Hpriv")
      as "(Hppid & Hcref & Hpvbk)".
    (* ---- +0x000 .. +0x01c ---- *)
    iApply (kxc_prologue m K eb (proc_addr jp) sp0 ra0 s00 s10 s20 pv av
              ltac:(lia) Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1 with "Hcg Htext Hpc").
    iIntros (CIDp Hsp1 M1) "%HM1 Hcg Hpc Hframe".
    destruct HM1 as (HM1sp & HM1s0 & HM1s2 & HM1a0 & HM1a1 & HM1thr).
    (* ---- +0x020: jal ra,myproc ---- *)
    assert (Htmp : add_vec (mword_of_int (KXA + 0x020) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085110 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x020)) Rra
              (mword_of_int 2085110 : mword 21) M1 (K - 68)%nat eb
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htmp; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_020 with "Htext"). }
    iIntros (CIDj1 Hsj1) "Hcg Hpc". iEval (rewrite Htmp) in "Hpc".
    set (N1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x020) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x020) : mword 64) 4)]> M1) with N1.
    assert (HN1ra : N1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x020) : mword 64) 4)
      by (rewrite /N1; apply upd_eq).
    iDestruct (cpu_own_transport CID0 CIDj1 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDj1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDj1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (Myproc.wp_myproc_sconf N1 (K - 68)%nat 0%nat eb (proc_addr jp) eb lks
              ltac:(vm_compute; reflexivity) ltac:(lia)
              with "Hcg Hcnt Htext Hpc").
    iIntros (CIDm Hsm ms M2) "%Hmsf Hcg Hcnt Hpc %Hmp".
    destruct Hmp as (Hcsm & Hm2a0).
    assert (Hpc24 : ret_pc (N1 !!! Regidx Rra) = mword_of_int (KXA + 0x024))
      by (rewrite HN1ra; pcw).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- +0x024: c.mv s1,a0 -- s1 := p ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x024)) Rs1 Ra0
              M2 (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_024 with "Htext"). }
    iIntros (CIDv1 Hsv1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2).
    assert (HN2s1 : N2 !!! Regidx Rs1 = (proc_addr jp)).
    { rewrite /N2 upd_eq Hm2a0. apply add_vec_zero_l. }
    assert (Hpp026 : add_vec_int (mword_of_int (KXA + 0x024) : mword 64) 2
                     = mword_of_int (KXA + 0x026)) by pcw.
    iEval (rewrite Hpp026) in "Hpc".
    (* ---- +0x026: jal ra,begin_op ---- *)
    assert (Htbo : add_vec (mword_of_int (KXA + 0x026) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094214 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x026)) Rra
              (mword_of_int 2094214 : mword 21) N2 (K - 68)%nat eb
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htbo; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_026 with "Htext"). }
    iIntros (CIDj2 Hsj2) "Hcg Hpc". iEval (rewrite Htbo) in "Hpc".
    set (N3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x026) : mword 64) 4)]> N2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x026) : mword 64) 4)]> N2) with N3.
    assert (HN3ra : N3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x026) : mword 64) 4)
      by (rewrite /N3; apply upd_eq).
    assert (HN3s1 : N3 !!! Regidx Rs1 = (proc_addr jp))
      by (rewrite /N3 upd_ne; [exact HN2s1 | nz]).
    iDestruct (cpu_own_transport CIDm CIDj2 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDj1 CIDj2 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDj1 CIDj2 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (BeginOp.wp_begin_op_sconf gs jp gl fsc_bio icfg_log fsc_fs fsc_cov fsc_logst icfg_dev
              pidv (DfracOwn (1/4)) N3 (K - 68)%nat eb eb lks
              U ltac:(lia) Hjp Hgs
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hlogc Hppid Hprocs").
    all: try lkbelow.
    iIntros (CIDb Hsb M3) "%Hcsb Hcg Hcnt Hextc Hclmc Hpc Hppid Hlog".
    assert (Hpc2a : ret_pc (N3 !!! Regidx Rra) = mword_of_int (KXA + 0x02a))
      by (rewrite HN3ra; pcw).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- +0x02a: c.mv a0,s2 -- a0 := path ---- *)
    assert (HM3s2 : M3 !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcsb Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsm Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N1 upd_ne; [exact HM1s2 | nz]. }
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x02a)) Ra0 Rs2
              M3 (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_02a with "Htext"). }
    iIntros (CIDv2 Hsv2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M3 !!! Regidx Rs2))]> M3).
    assert (HN4a0 : N4 !!! Regidx Ra0 = pv).
    { rewrite /N4 upd_eq HM3s2. apply add_vec_zero_l. }
    assert (Hpp02c : add_vec_int (mword_of_int (KXA + 0x02a) : mword 64) 2
                     = mword_of_int (KXA + 0x02c)) by pcw.
    iEval (rewrite Hpp02c) in "Hpc".
    (* ---- +0x02c: jal ra,namei ---- *)
    assert (Htnm : add_vec (mword_of_int (KXA + 0x02c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093730 : mword 21))
                   = mword_of_int KernelSyms.namei) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x02c)) Rra
              (mword_of_int 2093730 : mword 21) N4 (K - 68)%nat eb
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htnm; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_02c with "Htext"). }
    iIntros (CIDj3 Hsj3) "Hcg Hpc". iEval (rewrite Htnm) in "Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x02c) : mword 64) 4)]> N4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x02c) : mword 64) 4)]> N4) with N5.
    assert (HN5ra : N5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x02c) : mword 64) 4)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a0 : N5 !!! Regidx Ra0 = pv)
      by (rewrite /N5 upd_ne; [exact HN4a0 | nz]).
    iDestruct (cpu_own_transport CIDb CIDj3 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb CIDj3 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb CIDj3 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iEval (rewrite /cwd_ref) in "Hcref".
    (* namei names the path buffer by ITS OWN a0; ours is [pv]. *)
    iEval (rewrite -HN5a0) in "Hpath".
    (* ---- THE SET FORM, NOT THE COUNTED ONE, AND THAT IS WHAT LIFTS
       KEXEC'S PATH-LENGTH CAP.  The counted contract prices the walk at
       [(L+1) * iput_units] and spends the same, so at [L = 2] it hands back
       one unit where the closing iunlockput needs three -- which is why
       [SpecKexec] used to carry a premise admitting only one path element.
       [wp_namei_gen] prices it at [SpecNamex.walk_need L <= 4] REGARDLESS OF
       DEPTH and spends at most two, leaving eight.  [log_op] is literally
       [∃ Sb, log_opS], so entering the set form is one [iDestruct] and
       leaving it is [LogInv.log_opS_op]; nothing else in the phase moves.
       (sys_chdir did this first -- SpecSysChdir.v's ledger section.) ---- *)
    iDestruct (log_op_openS with "Hlog") as (Sb0) "[Hlog Htx]".
    (* ---- THE TRACE, BUILT FROM THE PIN.  [ftop_inv] rides in on the
       fabric's own [ireg_inv] ([InodeRegion.ireg_inv_ftop]); the start's
       SLASH side condition is the contract's [pfun 0 = SLASH] through
       [FsAbsStart.bview_head_slash_intro]. ---- *)
    iDestruct (ireg_inv_ftop with "Hireg") as "#Hftop".
    iDestruct (kxt_start fsc_fs pb ds (bview plen pfun) Hpl
                 (bview_head_slash_intro plen pfun Hcstr Hslash)
                 with "Hftop Hrp") as "Hstart".
    iApply (NE.wp_namei_era gs jp gl pd pav pu
 gf
              plen pfun MAXOPBLOCKS Sb0 (kxt_P ds) (kxt_P ds)
              pidv (DfracOwn (1/4)) dqb dqs dqpv
              N5 (K - 68)%nat eb eb lks
              U ltac:(lia) Hroot Hnib0 Hlg Hsz Hbm0
              Hbmc Hbml Hins0 Hcovb Hiregb Hcstr Hplen
              ltac:(unfold walk_need, iput_units, MAXOPBLOCKS;
                    destruct (length (path_elems (bview plen pfun))); lia)
              Hjp Hgs
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hka Hitab Hitinv Hesc
                    Hslks Hireg Hropen Hprocs Hdevi Hdgeom Hdlock Hbm Hins Hbits Hppid
                    Hcref Hpath Hbs Hirs [$Hlog $Htx] Hstart").
    (* namei is eb-generic now; kexec is still at [eb = true]. *)
    iIntros (CIDn Hsn M4 n1 Sb1 ok ipv w) "%Hcsn Hcg Hcnt Hextc Hclmc Hpc Hbm Hins
             Hppid Hcref Hpath Hbs %HSbsub %Hwbm %Hn1 [Hlog Htx] Harm".
    iDestruct (log_opS_op with "Hlog Htx") as "Hlog".
    (* what the seam actually carries: the closing iunlockput's three units.
       The walk spent at most two of the ten. *)
    assert (Hiu1 : (iput_units <= n1)%nat).
    { unfold walk_spend, iput_units, MAXOPBLOCKS in *. destruct w, ok; lia. }
    iEval (rewrite HN5a0) in "Hpath".
    assert (Hpc30 : ret_pc (N5 !!! Regidx Rra) = mword_of_int (KXA + 0x030))
      by (rewrite HN5ra; pcw).
    iEval (rewrite Hpc30) in "Hpc".
    (* ---- the register facts that survive to +0x030 ---- *)
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsn csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsb csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsm csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N1 upd_ne; [exact HM1sp | nz]. }
    assert (HM4s0 : M4 !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcsn Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsb Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsm Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /N1 upd_ne; [exact HM1s0 | nz]. }
    assert (HM4s1 : M4 !!! Regidx Rs1 = (proc_addr jp)).
    { rewrite (callee_saved_lookup Hcsn Rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsb Rs1 ltac:(vm_compute; reflexivity)).
      exact HN3s1. }
    assert (HM4s2 : M4 !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcsn Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz]. exact HM3s2. }
    assert (HM4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> M4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2.
      rewrite (callee_saved_lookup Hcsn r Hr).
      rewrite /N5 upd_ne; [| regne]. rewrite /N4 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcsb r Hr).
      rewrite /N3 upd_ne; [| regne]. rewrite /N2 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcsm r Hr).
      rewrite /N1 upd_ne; [| regne].
      exact (HM1thr r Hr Nsp Ns0 Ns2). }
    destruct ok.
    - (* ============ namei SUCCEEDED: fall through to +0x032 ============ *)
      (* the era contract publishes the inum ITSELF -- no [inode_held_zi]
         re-introduction -- together with the cursor at the last hop. *)
      iDestruct "Harm" as (zi) "(%HM4a0 & Hheld & HP & Hirs)".
      iDestruct (inode_held_at_ne_zero with "Hheld") as %Hipvnz.
      (* AND THE VERDICT: the cursor's far end is the pinned inum. *)
      iDestruct (kxt_answer fsc_fs pb ds (bview plen pfun) zi Hpl
                   with "Hrp HP") as %Hzi.
      assert (Hcmp : eq_vec (rget M4 Ra0) (zero_reg : mword 64) = false).
      { rewrite (rget_ne M4 Ra0 ltac:(nz)) HM4a0.
        destruct (eq_vec ipv (zero_reg : mword 64)) eqn:E; [| reflexivity].
        exfalso. apply Hipvnz. by apply eq_vec_true_iff in E. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXA + 0x030))
                (mword_of_int 44 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M4 (K - 68)%nat eb
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                with "Hcg Hpc []").
      { iApply (kxc_030 with "Htext"). }
      iIntros (CIDz Hsz1) "Hcg Hpc".
      assert (Hpp032 : add_vec_int (mword_of_int (KXA + 0x030) : mword 64) 2
                       = mword_of_int (KXA + 0x032)) by pcw.
      iEval (rewrite Hpp032) in "Hpc".
      (* close the private block back up, at the cwd it lent out *)
      iDestruct ("Hpvbk" with "Hppid [Hcref]") as "Hpriv".
      { iEval (rewrite /cwd_ref). iExact "Hcref". }
      iDestruct (cpu_own_transport CIDn CIDz 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDn CIDz eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDn CIDz eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iSpecialize ("Hcont32" $! CIDz with "[%]"); [wp_next_chain |].
      (* hand the exit back, re-anchored at [CIDz] (the crossing fact by NAME,
         never as an inline [ltac:] in argument position -- durable-notes) *)
      assert (Hcrz : true = false \/ proc_addr jp = zero_reg ->
                     (CIDz : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CIDz true (proc_addr jp) _ Hcrz
                   with "Hcont") as "Hcont".
      iApply ("Hcont32" $! M4 ipv zi n1 with "[//] [-Hcont] Hcont").
      (* NO [iFrame] HERE.  The goal mentions [proc_priv], and framing into
         it sends the search through sixteen [ofile_slot]s and a 4096-byte
         trapframe page (durable-notes.md); measured: it does not come back.
         Nineteen [iSplitL]/[iExact]s instead, in the conjunct order. *)
      rewrite /kxc_at_a2.
      iSplitR.
      { iPureIntro. split_and!;
          [exact HM4sp | exact HM4s0 | exact HM4s1 | exact HM4s2
          | exact HM4a0 | exact Hipvnz | exact HM4thr]. }
      iSplitL "Hpc"; [iExact "Hpc" |].
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcnt"; [iExact "Hcnt" |].
      iSplitL "Hextc"; [iExact "Hextc" |].
      iSplitL "Hclmc"; [iExact "Hclmc" |].
      iSplitR; [iPureIntro; exact Hiu1 |].
      iSplitL "Hlog"; [iExact "Hlog" |].
      iSplitL "Hheld"; [iExact "Hheld" |].
      iSplitL "Hirs"; [iExact "Hirs" |].
      iSplitR; [iExact "Hbits" |].
      iSplitL "Hbs"; [iExact "Hbs" |].
      iSplitL "Hbm"; [iExact "Hbm" |].
      iSplitL "Hins"; [iExact "Hins" |].
      iSplitR; [iExact "Hka" |].
      iSplitL "Hpriv"; [iExact "Hpriv" |].
      iSplitL "Hpath"; [iExact "Hpath" |].
      iSplitL "Hargv"; [iExact "Hargv" |].
      iSplitL "Hargs"; [iExact "Hargs" |].
      iExact "Hframe".
    - (* ============ namei FAILED: the +0x088 tail ============ *)
      (* the era failure arm carries the death index and the unfired
         suffix beside the landed pair; kexec's [-1] tail wants neither. *)
      iDestruct "Harm" as "(%HM4a0 & Hirs & _)".
      assert (Hcmp : eq_vec (rget M4 Ra0) (zero_reg : mword 64) = true).
      { rewrite (rget_ne M4 Ra0 ltac:(nz)) HM4a0.
        apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity. }
      assert (Htgt88 : add_vec (mword_of_int (KXA + 0x030) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 44 : mword 8) ('b"0"))))
              = mword_of_int (KXA + 0x088)) by pcw.
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXA + 0x030))
                (mword_of_int 44 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M4 (K - 68)%nat eb
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                ltac:(rewrite Htgt88; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_030 with "Htext"). }
      iIntros (CIDz Hsz1). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt88) in "Hpc".
      (* ---- +0x088: jal ra,end_op ---- *)
      assert (Hteo : add_vec (mword_of_int (KXA + 0x088) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094256 : mword 21))
                     = mword_of_int KernelSyms.end_op) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x088)) Rra
                (mword_of_int 2094256 : mword 21) M4 (K - 68)%nat eb
                ltac:(nz) ltac:(rdok)
                ltac:(rewrite Hteo; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_088 with "Htext"). }
      iIntros (CIDj4 Hsj4) "Hcg Hpc". iEval (rewrite Hteo) in "Hpc".
      set (P1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KXA + 0x088) : mword 64) 4)]> M4).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KXA + 0x088) : mword 64) 4)]> M4) with P1.
      assert (HP1ra : P1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KXA + 0x088) : mword 64) 4)
        by (rewrite /P1; apply upd_eq).
      iDestruct (cpu_own_transport CIDn CIDj4 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDn CIDj4 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDn CIDj4 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iApply (EndOp.wp_end_op_sconf gs jp gl fsc_uart fsc_disk fsc_dlock pd pav pu fsc_bio icfg_log fsc_fs
                fsc_cov fsc_logst icfg_dev n1 pidv (DfracOwn (1/4)) P1 (K - 68)%nat
                eb eb lks U ltac:(lia) Hlg Hjp Hgs
                with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hcrash Hcert
                      Hppid Hprocs Hdevi Hdgeom Hdlock Hlog").
      all: try lkbelow.
      iIntros (CIDe1 Hse1 M5) "%Hcse Hcg Hcnt Hextc Hclmc Hpc Hppid".
      assert (Hpc8c : ret_pc (P1 !!! Regidx Rra) = mword_of_int (KXA + 0x08c))
        by (rewrite HP1ra; pcw).
      iEval (rewrite Hpc8c) in "Hpc".
      (* ---- +0x08c: c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KXA + 0x08c)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                M5 (K - 68)%nat eb ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_08c with "Htext"). }
      iIntros (CIDl1 Hsl1) "Hcg Hpc".
      set (P2 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> M5).
      assert (HP2a0 : P2 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /P2; apply upd_eq).
      assert (Hpp08e : add_vec_int (mword_of_int (KXA + 0x08c) : mword 64) 2
                       = mword_of_int (KXA + 0x08e)) by pcw.
      iEval (rewrite Hpp08e) in "Hpc".
      (* ---- +0x08e: c.j -28 -> +0x072 ---- *)
      assert (Htj72 : add_vec (mword_of_int (KXA + 0x08e) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
              = mword_of_int (KXA + 0x072)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KXA + 0x08e))
                (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                P2 (K - 68)%nat eb
                ltac:(rewrite Htj72; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kxc_08e with "Htext"). }
      iIntros (CIDz2 Hsz2). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htj72) in "Hpc".
      (* ---- close the private block and take the shared exit ---- *)
      iDestruct ("Hpvbk" with "Hppid [Hcref]") as "Hpriv".
      { iEval (rewrite /cwd_ref). iExact "Hcref". }
      iDestruct (cpu_own_transport CIDe1 CIDz2 0%nat eb (proc_addr jp) eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDe1 CIDz2 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDe1 CIDz2 eb (proc_addr jp)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      (* the register facts at +0x072 *)
      assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 68).
      { rewrite /P2 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcse csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /P1 upd_ne; [exact HM4sp | nz]. }
      assert (HP2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
                P2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp Ns0 Ns1 Ns2.
        rewrite /P2 upd_ne; [| regne].
        rewrite (callee_saved_lookup Hcse r Hr).
        rewrite /P1 upd_ne; [| regne].
        exact (HM4thr r Hr Nsp Ns0 Ns1 Ns2). }
      iApply (T.kxc_exit_m1 Q (proc_addr jp) gf
                plen pfun na avf alen aslen afun pidv U
                dqb dqs dqa dqpv dqas m P2 K eb eb lks sp0 ra0 s00 s10 s20 pv av
                ltac:(lia) Hsp Hra Hs0 Hs1 Hs2 HP2sp HP2a0 HP2thr
                with "Hcg Hcnt Hextc Hclmc Htext Hpc [Hframe] Hbm Hins Hka Hpriv
                      Hpath Hargv Hargs Hbs Hirs").
      { iApply (kxc_frameA_epi with "Hframe"). }
      iIntros (CIDf Hsf mf U' entry spv szv') "%Hcs2 %Hok Hcg Hcnt Hextc Hclmc Hpc
               Hbm Hins Hka2 Hpriv Hpath Hargv Hargs Hbs Hirs".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iDestruct ("Hkw" $! CIDf with "Hcont") as "Hcont".
      iApply ("Hcont" $! mf U' entry spv szv'
                with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc Hbm Hins Hka2 Hpriv
                      Hpath Hargv Hargs Hbs Hirs").
      + exact Hcs2.
      + exact Hok.
  Qed.
End KexecPinABody.

(* ===================================================================== *)
(*  PHASE A, WHOLE -- IN A FRESH SECTION, for [ProofKexecA.kxc_phaseA]'s   *)
(*  reason exactly (the chain applies [kxc_a2] at the SEAM's hart).        *)
(* ===================================================================== *)
Section KexecPinAMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Lemma kxc_phaseAp
      (Q : mword 64 -> ustate -> Prop)
      (pb : kx_pin) (ds : list Z)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
 (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (* NO [HD]/[XCH] PARAMETERS.  The pinned phase A does not relay a
         header oracle -- it OWNS one: [HD := Some (kxp_ef pb)] and
         [XCH := ⌜False⌝], the latter because [SpecKexecPin] sect. 4's
         premise is not a cancellable resource and there is no lost arm
         to escape to.  What the caller gets at +0x090 is therefore the
         header claim itself. *)
      (* the exit, opaque -- see the premise below *)
      (KEX : CpuId -> iProp Σ) :
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
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    (* the pinned scope, and the pinned file's whole header -- the
       verdict the oracle below produces is about its first 64 bytes
       ([SpecKexecPin] sect. 7's third pure premise). *)
    path_elems (bview plen pfun) = kxp_path pb ->
    pfun 0%nat = SLASH ->
    (64 <= length (kxp_bytes pb))%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Ra0 = pv ->
    m !!! Regidx Ra1 = av ->
    sie_cap_gpr KT1 m K b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jp) -∗
    kernel_text -∗ pc_is (mword_of_int KXA : mword 64) -∗
    fs_fabric gs pd pav pu
 -∗
    (* ==== THE PIN, IN PLACE OF THE ORACLE.  The landed phase A relays a
       header oracle it cannot answer; the pinned one ANSWERS it, from
       this premise and nothing else ([ProofKexecPinTrace.kxt_hdr_verdict]
       at the inum [kxc_a1p] just identified). ==== *)
    kxp_run_pin (FsBytesGamma.fs_gamma_L fsc_fs) pb ds -∗
    kalloc_env fsc_kalloc None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    proc_priv gf (proc_addr jp) pidv U -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
    bslots 3 -∗
    iref_slots 2 -∗
    (* ---- kexec's OWN continuation: BOTH [-1] tails close through it ---- *)
    (* ---- kexec's OWN continuation, AS AN OPAQUE RESOURCE (N-5.2B,
       §13.4).  Phase A cannot commit to [Q]: the contents verdict is
       learned at the redeem instant INSIDE [kxc_a2], i.e. AFTER the
       point at which a [kexec_ok_q Q]-shaped exit would have fixed
       it -- and the two branches need different [Q]s (the only
       common one is [True], which the pinned post cannot supply
       without a receipt already in hand).  So the exit travels as
       [KEX]; phase A only ever UNFOLDS it, at its own [-1] tails,
       through this persistent wand, and the caller specialises what
       is left at +0x090 where the verdict IS known.  A landed caller
       passes its exit and the identity wand. ---- *)
    wp_next true (proc_addr jp) KEX -∗
    □ (∀ CX : CpuId, KEX CX -∗
      KexecOkQ.kexec_closer Q gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K b
           eb lks dqb dqs fsc_bmapstart na alen plen pv dqpv pfun
           av dqa avf aslen dqas afun) -∗
    (* ---- and the FALL-THROUGH: phase B's entry at +0x090 ---- *)
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M90 : regfile) (kf : nat) (qf sf : Qp) (inumf : mword 32)
        (dnf : dinode) (bmf : blkmap) (gilf gislf gyf : gname)
        (loyf tlyf : nat)
        (n2 : nat) (ef : nat -> bv 8) (datl : nat -> list (bv 8)),
        ⌜ M90 !!! Regidx csp_rs1 = pa_stk sp0 68 /\
          M90 !!! Regidx Rs0 = sp0 /\
          M90 !!! Regidx Rs1 = proc_addr jp /\
          M90 !!! Regidx Rs2 = pv /\
          M90 !!! Regidx Rs4 = ientry kf /\
          (kf < NINODE)%nat /\
          bv_unsigned inumf < 16 * Z.of_nat icfg_nib /\
          (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
             r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
             M90 !!! Regidx r = m !!! Regidx r) ⌝ -∗
        ⌜ (iput_units <= n2)%nat ⌝ -∗
        (* the header IS the file's first 64 bytes (S3b) -- ProofKexecA's
           own exit row, relayed verbatim. *)
        ⌜ forall j, (j < 64)%nat -> ef j = file_byte datl j ⌝ -∗
        pc_is (mword_of_int (KXA + 0x090) : mword 64) -∗
        sie_cap_gpr KT1 M90 (K - 68)%nat b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jp) -∗
        is_sleeplock_genl gilf gislf (i_lock (ientry kf)) "inode"%string
                     (ic_slp fsc_ic kf) (slh_tok (icfg_isl kf)) -∗
        sleeplocked_q gislf sf (i_lock (ientry kf)) pidv -∗
        ⌜(loyf <= tlyf)%nat⌝ -∗
        IcacheRef.cred_floor loyf tlyf -∗
        IcacheInv.iref_claims -∗
        ic_tx_dep fsc_ic kf sf icfg_dev inumf gyf loyf -∗
        off_rows off_cfg kf cur_ctx -∗
        i_dev (ientry kf) ↦₄{DfracOwn (1/2)} icfg_dev -∗
        i_inum (ientry kf) ↦₄{DfracOwn (1/2)} inumf -∗
        i_valid (ientry kf) ↦₄ valid_word true -∗
        kxc_ldat kf inumf dnf bmf datl -∗
        (* SpecIlock v5's additive type witness, at the generation the
           share names -- what SpecIunlockput now needs at +0x064. *)
        ity_shot gyf (di_type dnf) -∗
        (* the payload's freeze token (§3.9, RULING A-prime) *)
        ifreeze_off (bv_unsigned inumf) -∗
        inode_ref_short kf (qf + sf)%Qp qf icfg_dev inumf -∗
        (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
        runit_any (bv_unsigned inumf) -∗
        log_opb icfg_log n2 -∗
        iref_slots 1 -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
        bslots 3 -∗
        kalloc_env fsc_kalloc None -∗
        proc_priv gf (proc_addr jp) pidv U -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
        (* the ELF HEADER, NAMED (N-5.2B): the eight slots readi just wrote
           cross the seam carrying their bytes instead of being re-carved
           out of an existential [stack_own] by phase B. *)
        □ (⌜kxq_hdr_ok (Some (kxp_ef pb)) ef⌝ ∨ ⌜False⌝) -∗
        kxc_frameA6x sp0 ra0 s00 s10 s20 pv av (m !!! Regidx Rs4) ef -∗
        (* THE EXIT, HANDED BACK.  Phase A's two [-1] tails own one copy of
           the caller's exit and a [wp_next] continuation is LINEAR, so
           without this phase B would have none.  durable-notes' "CHAINING
           TWO HALVES" -- the shape [kxc_a1] already uses internally, now on
           phase A's own interface, because [ProofKexec.v] composes across it. *)
        wp_next (CID0 := CID) true (proc_addr jp) KEX -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hcstr Hplen Hjp Hgs Hpl Hslash Hhlen Hsp Hra Hs0 Hs1 Hs2
           Ha0 Ha1.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hrp #Hka Hbm Hins #Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hcont #Hkw Hcont90".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* the region invariant carries [ftop_inv]; the oracle below opens it *)
    iDestruct (SpecKexec.fs_fabric_all with "Hfab")
      as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hireg & _)".
    iDestruct (ireg_inv_ftop with "Hireg") as "#Hftop".
    iApply (kxc_a1p (CID0 := CID0) Q pb ds gs jp gl pd pav pu gf

              plen pfun na avf alen aslen afun pidv U dqb dqs dqa dqpv dqas
              m K eb b lks sp0 ra0 s00 s10 s20 pv av KEX
              HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
              Hiregb Hcstr Hplen Hjp Hgs Hpl Hslash Hsp Hra Hs0 Hs1 Hs2
              Ha0 Ha1
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab Hka Hbm Hins Hbits Hpriv
                    Hpath Hargv Hargs Hbs Hirs Hrp Hcont Hkw [Hcont90]").
    (* ---- the seam at +0x032: [kxc_a2] takes it verbatim ---- *)
    iIntros (CIDs Hss M32 ipv zi n1) "%Hzi Hseam Hexit".
    iDestruct (wp_next_retarget CID0 CIDs true (proc_addr jp) _ Hss
                 with "Hcont90") as "Hcont90".
    iApply (LA.kxc_a2 (CID0 := CIDs) Q gs jp gl pd pav pu gf

              plen pfun na avf alen aslen afun pidv U dqb dqs dqa dqpv dqas
              m M32 K eb b lks sp0 ra0 s00 s10 s20 pv av ipv zi n1
              (Some (kxp_ef pb)) (⌜False⌝)%I KEX
              HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
              Hiregb Hjp Hgs Hsp Hra Hs0 Hs1 Hs2
              with "Htext Hfab [] Hseam Hexit Hkw Hcont90").
    (* ---- THE ORACLE, ANSWERED.  [kxc_a1p] identified the walk's inum as
       the pinned one, so the payload the redeem instant hands over is the
       PINNED file's, and its bytes are read off the authority through the
       era leg the widened row carries. ---- *)
    { rewrite Hzi. iIntros (dn bm data) "%Hok Hpay".
      iApply (kxt_hdr_verdict fsc_fs pb ds dn bm data Hok Hhlen
                with "Hftop Hrp Hpay"). }
  Qed.

End KexecPinAMain.

End KexecPinAProof.
