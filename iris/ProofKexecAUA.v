(* ===================================================================== *)
(*  ProofKexecAUA.v -- PHASE A OF kexec, AT THE ATOMIC-UPDATE CONTRACT.   *)
(*  (fs-syscall-specs, exec AU lane, stage S4a; SpecKexecAU.v sect. 2)    *)
(* ===================================================================== *)

(*  [ProofKexecPinA] REPLAYED AT THE CALLER'S OWN WALK PREMISE AND THE
    CALLER'S OWN OBSERVATION, which is the whole of what the AU contract
    costs phase A:

      * [kxc_a1_au] is [kxc_a1p] with the pin removed: the era walk fires
        [SpecSysOpenAU.open_walk_pre_era] -- the caller's one-shot,
        specialised to the string in the path buffer by
        [FsAbsOpenFire.opf_start_of_open] -- and the +0x032 seam publishes
        the walk's CURSOR [P L zi] instead of an inum equation.  The
        +0x088 tail hands the era DEATH RECEIPT out (it IS
        [open_walk_dead_era] by conversion, [FsAbsEra.ex_hops_is_ax_hops])
        rather than dropping it, which is [exec_post_fail]'s arm (ii).
        Because there is no pin, there is no absolute-path premise either:
        [ex_start] carries the [SLASH] tie itself.

      * [kxc_phaseA_au] does not RELAY a header oracle and does not ANSWER
        one: it SPENDS the caller's [aopen_commit_at] at the very instant
        [ProofKexecA]'s oracle is fired -- ilock's payload open, readi not
        yet run -- through [FsAbsOpenFire.opf_open_fire] off the payload's
        own era leg, and what comes back is the caller's LINEAR receipt
        [Φo av zi (abs_of (era_node dn bm data))].  A persistent claim
        cannot carry a linear receipt, which is why [ProofKexecA] grew
        [kxc_a2_r] (the oracle's payout generic in [R]) and why the landed
        [kxc_a2] is now that lemma's corollary at the header claim.

    EVERYTHING ELSE IS ProofKexecA's.  The landed blocks are opened as [LA]
    and instantiated, never duplicated; the copy stops at the namei call
    exactly as ProofKexecPinA's does.                                     *)
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
(* NOT [SpecKexecPin]: that file's own chain reaches the boot composition
   (FsInitPin -> ... -> LinkKexec), and a phase-A leaf must not.  Its one
   pure lemma this file wants ([fn_file_bytes_era_ok]) is nine lines and is
   restated below as [kxa_file_bytes_ok]. *)
Require Import ProofKexecA.    (* the LANDED blocks, opened as [LA]  *)
(* THE ELF SIDE: [elf_wf] / [elf_magic_ok] / [elf_le_at] (ElfFile) and the
   readi-window bridge [le_at_of_file_bytes] plus [elf_parse_ehdr_fields]
   (ElfBridge).  Needed only by the two [bad:] tails' honesty argument. *)
Require Import ElfFile.
Require Import ElfBridge.
(* THE ABSTRACT SIDE.  [FsAbsInv] for the commit mask [fsabsE] and [FsAbs]
   for [anode] / [aview] / [abs_of]; per [FsAbs]'s own rule they go LAST of
   the two, and this file names none of the [FsState*] twins they shadow
   ([fs_view], [byte_range]). *)
Require Import FsAbsInv.
Require Import FsAbs.
(* THE AU LEAVES, QUALIFIED: their statements are all this file wants and a
   fourth import of the abstract stack buys nothing. *)
Require SpecSysOpenAU.   (* [open_walk_pre_era] / [open_walk_dead_era]
                            / [aopen_commit_at]                      *)
Require FsAbsOpenFire.   (* [opf_start_of_open], [opf_open_fire],
                            [opf_era_file_row]                       *)
Require SpecKexecAU.     (* the contract this lane serves            *)
Require UexecSlot.       (* [uvis] -- the slot predicate's key type  *)
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
(*  PHASE A AT THE AU CONTRACT.                                           *)
(* ===================================================================== *)
Module KexecAUAProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
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

Section KexecAUABody.
  (* [!ufdG Σ] beside ProofKexecPinA's list: [SpecKexecAU.exec_slot_pre]
     names [UexecRet.uslot], whose key's descriptor leg lives there. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ,
            !pavG Σ, !ufdG Σ}.
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

  Lemma kxc_a1_au
      (Q : mword 64 -> ustate -> Prop)
      (QF : KexecOkQ.kxf_cause -> Prop)
      (* the caller's walk one-shot, its miss receipt, the REST of the AU
         bundle (opaque -- phase A only threads or refunds it) and the
         refund shape the [-1] tail owes. *)
      (P Pmiss : nat -> Z -> iProp Σ) (AU FAIL : iProp Σ)
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
    (* the failure-side plug's cause (S5), relayed: the pinned run's own
       two [bad:] tails are phase A's, and it plugs the hole vacuously. *)
    (exists c : KexecOkQ.kxf_cause, QF c) ->
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
    (* NO SCOPE PREMISE: [ex_start] carries the [SLASH] tie itself. *)
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
    (* ==== THE AU BUNDLE, IN PLACE OF THE PIN.  The one-shot is handed
       DOWN unfired -- the walk picks the start inum and fires it there
       ([FsAbsOpenFire.opf_start_of_open]) -- and [AU] is whatever else the
       caller wants back on the dead arm. ==== *)
    SpecSysOpenAU.open_walk_pre_era fsc_fs (pv_cwi (us_V U)) P Pmiss -∗
    AU -∗
    ((SpecSysOpenAU.open_walk_dead_era fsc_fs P Pmiss (bview plen pfun) ∗ AU)
       -∗ FAIL) -∗
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
    □ (∀ CX : CpuId, KEX CX -∗ FAIL -∗
      KexecOkQ.kexec_closer Q QF gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K b
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
        (* ---- AND THE TWO NEW ROWS AT THE SEAM: the walk's CURSOR at the
           inum it landed on, and the rest of the bundle.  Everything else
           at +0x032 is [kxc_at_a2] unchanged. ---- *)
        P (length (path_elems (bview plen pfun))) zi -∗
        AU -∗
        kxc_at_a2 jp gf
                  plen pfun na avf aslen afun pidv U dqb dqs dqa dqpv dqas
                  m M32 K eb b lks sp0 ra0 s00 s10 s20 pv av ipv zi n1 -∗
        wp_next (CID0 := CID) true (proc_addr jp) KEX -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hqf HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hcstr Hplen Hjp Hgs Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hka Hbm Hins #Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hwp Hau Hwd Hcont #Hkw Hcont32".
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
    iEval (rewrite /cwd_ref_at) in "Hcref".
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
    (* ---- THE TRACE, THE CALLER'S OWN ONE-SHOT AT THE FETCHED STRING.
       Nothing is fired here: the WALK picks the start inum and fires it
       there ([ProofSysOpenAUWalk]'s own idiom). ---- *)
    iDestruct (FsAbsOpenFire.opf_start_of_open fsc_fs (pv_cwi (us_V U)) P Pmiss
                 (bview plen pfun) with "Hwp") as "Hstart".
    iApply (NE.wp_namei_era gs jp gl pd pav pu
 gf
              plen pfun MAXOPBLOCKS Sb0 P Pmiss
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
      (* the dead-arm refund is not needed on this side *)
      iClear "Hwd".
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
      { iEval (rewrite /cwd_ref_at). iExact "Hcref". }
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
      iApply ("Hcont32" $! M4 ipv zi n1 with "HP Hau [-Hcont] Hcont").
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
      (* ...and kexec's AU caller wants exactly that suffix back: the era
         arm IS [open_walk_dead_era] by conversion
         ([FsAbsEra.ex_hops_is_ax_hops]). *)
      iDestruct "Harm" as "(%HM4a0 & Hirs & Hdead)".
      iDestruct ("Hwd" with "[Hdead Hau]") as "Hfail".
      { (* [ex_hops_from] IS [ax_hops_from .. (path_elems pl)], but only by
           conversion, so the two halves go in by [iExact]. *)
        iSplitL "Hdead"; [iExact "Hdead" | iExact "Hau"]. }
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
      { iEval (rewrite /cwd_ref_at). iExact "Hcref". }
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
      iApply (T.kxc_exit_m1 Q QF (proc_addr jp) gf
                plen pfun na avf alen aslen afun pidv U
                dqb dqs dqa dqpv dqas m P2 K eb eb lks sp0 ra0 s00 s10 s20 pv av
                Hqf ltac:(lia) Hsp Hra Hs0 Hs1 Hs2 HP2sp HP2a0 HP2thr
                with "Hcg Hcnt Hextc Hclmc Htext Hpc [Hframe] Hbm Hins Hka Hpriv
                      Hpath Hargv Hargs Hbs Hirs").
      { iApply (kxc_frameA_epi with "Hframe"). }
      iIntros (CIDf Hsf mf U' entry spv szv') "%Hcs2 %Hok Hcg Hcnt Hextc Hclmc Hpc
               Hbm Hins Hka2 Hpriv Hpath Hargv Hargs Hbs Hirs".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iDestruct ("Hkw" $! CIDf with "Hcont Hfail") as "Hcont".
      iApply ("Hcont" $! mf U' entry spv szv'
                with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc Hbm Hins Hka2 Hpriv
                      Hpath Hargv Hargs Hbs Hirs").
      + exact Hcs2.
      + exact Hok.
  Qed.
End KexecAUABody.

(* ===================================================================== *)
(*  PHASE A, WHOLE, AT THE AU CONTRACT -- IN A FRESH SECTION, for         *)
(*  [ProofKexecA.kxc_phaseA]'s reason exactly (the chain applies          *)
(*  [kxc_a2_r] at the SEAM's hart).                                       *)
(* ===================================================================== *)
Section KexecAUAMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ,
            !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Notation ΓL := (FsBytesGamma.fs_gamma_L fsc_fs).

  (* =================================================================== *)
  (*  THE RECEIPT PHASE A BUYS AT THE ORACLE'S INSTANT.                   *)
  (*                                                                      *)
  (*  [ProofKexecA]'s oracle is fired with ilock's payload open and readi  *)
  (*  not yet run, and it is handed the payload's OWN era leg at the inum  *)
  (*  the walk landed on.  [FsAbsOpenFire.opf_open_fire] turns that leg    *)
  (*  plus the caller's [aopen_commit_at] into the caller's receipt for    *)
  (*  the WHOLE abstract node -- which is exactly [SpecSysOpenAU]'s        *)
  (*  terminal observation, at kexec's lock window instead of open's.      *)
  (*                                                                      *)
  (*  THE PURE ROW rides beside it because the oracle's own premise is     *)
  (*  where [inode_ok] is in scope: below +0x090 nothing re-derives        *)
  (*  [fn_file_bytes (era_node ..) = file_bytes data ..], and the arms are *)
  (*  keyed on [MkAnode (AFile f) nl].  It is CONDITIONAL on the type      *)
  (*  because kexec does not test it: a directory whose first sixty-four   *)
  (*  bytes parsed as an ELF header would reach +0x090 too.                *)
  (* =================================================================== *)
  Definition kxa_receipt (Sl : UexecSlot.uvis -> iProp Σ) (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (L : nat) (zi : Z)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) : iProp Σ :=
    (∃ av : aview,
       ⌜av !! zi = Some (abs_of (FsStateEra.era_node dn bm data))⌝ ∗
       ⌜bv_unsigned (di_type dn) = FsImg.T_FILE_z ->
          abs_of (FsStateEra.era_node dn bm data)
          = MkAnode (AFile (FsTree.file_bytes data
                              (Z.to_nat (bv_unsigned (di_size dn)))))
                    (fn_nlink (FsStateEra.era_node dn bm data))⌝ ∗
       Φo av zi (abs_of (FsStateEra.era_node dn bm data)) ∗
       P L zi ∗
       SpecKexecAU.exec_slot_pre Sl Φo na alen afun sts)%I.

  (* the +0x090 row, and the [bad:] tails' row, are the same receipt: the
     buffer [ef] plays no part in it (the header claim was the only thing
     that had to be re-read at the buffer). *)
  Definition kxa_receipt_x (Sl : UexecSlot.uvis -> iProp Σ) (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (L : nat) (zi : Z)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (ef : nat -> bv 8)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) : iProp Σ :=
    kxa_receipt Sl P Φo L zi na alen afun sts dn bm data.

  (* ---- the two refund shapes, assembled ------------------------------ *)

  (* arm (ii): the walk died, nothing was observed, both the commit and the
     slot premise come home beside the era refund. *)
  Lemma kxa_fail_dead (Sl : UexecSlot.uvis -> iProp Σ)
      (γ : FsBlocks.fs_names) (cw : Z) (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (pl : list (bv 8)) :
    SpecSysOpenAU.open_walk_dead_era γ P Pmiss pl
      ∗ (SpecSysOpenAU.aopen_commit_at (FsBytesGamma.fs_gamma_L γ) fsabsE Φo
         ∗ SpecKexecAU.exec_slot_pre Sl Φo na alen afun sts) -∗
    SpecKexecAU.exec_post_fail Sl (FsBytesGamma.fs_gamma_L γ) γ cw P Pmiss Φo na alen afun sts.
  Proof.
    iIntros "(Hd & Hoc & Hsl)". rewrite /SpecKexecAU.exec_post_fail.
    iRight. iExists pl. iLeft. iFrame "Hd Hoc Hsl".
  Qed.

  (* ---- THE TWO TAILS' HONESTY (2026-09-04) --------------------------
     [SpecKexecAU.exec_fail_ok]'s [EfNoMem] now DEMANDS the magic passed, so
     phase A -- which allocates nothing -- can never take that cause: both
     [bad:] tails must produce [EfNotLoadable], i.e. refute
     [anode_loadable].  Everything below is pure. ---- *)

  Lemma kxa_file_bytes_length (data : nat -> list (bv 8)) (n : nat) :
    length (FsTree.file_bytes data n) = n.
  Proof. rewrite /FsTree.file_bytes length_fmap length_seq. reflexivity. Qed.

  (* a one-byte [elf_le_at] IS the byte *)
  Lemma kxa_elf_le_at_1 (f : elf_bytes) (k : nat) :
    elf_le_at f k 1 = bv_unsigned (f !!! k).
  Proof. unfold elf_le_at. simpl. rewrite Nat.add_0_r. lia. Qed.

  Lemma kxa_byte_is_val (f : elf_bytes) (o v : Z) :
    elf_byte_is f o v = true -> bv_unsigned (f !!! Z.to_nat o) = v.
  Proof.
    unfold elf_byte_is, elf_read_u8.
    destruct (elf_read f o 1) as [b |] eqn:E; [| discriminate].
    intros Hb. apply Z.eqb_eq in Hb. subst v.
    pose proof (proj1 (elf_read_Some f o 1 b ltac:(lia)) E) as (_ & _ & Hv).
    rewrite Hv. symmetry. apply kxa_elf_le_at_1.
  Qed.

  (* the four-byte magic word the kernel compares, off a well-formed file *)
  Lemma kxa_magic_le_at (f : elf_bytes) :
    elf_magic_ok f = true -> elf_le_at f 0 4 = 1179403647.
  Proof.
    unfold elf_magic_ok. intros H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2].
    apply andb_prop in H as [H0 H1].
    apply kxa_byte_is_val in H0. apply kxa_byte_is_val in H1.
    apply kxa_byte_is_val in H2. apply kxa_byte_is_val in H3.
    cbn in H0, H1, H2, H3. unfold elf_le_at. cbn.
    rewrite H0 H1 H2 H3. lia.
  Qed.

  Lemma kxa_magic_bad_wf (f : elf_bytes) :
    elf_le_at f 0 4 <> 1179403647 -> elf_wf f = false.
  Proof.
    intros Hne. unfold elf_wf.
    destruct (elf_parse_ehdr f) as [e |]; [| destruct (elf_phdrs f); reflexivity].
    destruct (elf_phdrs f) as [ps |]; [| reflexivity].
    destruct (elf_magic_ok f) eqn:Hm; [| reflexivity].
    exfalso. exact (Hne (kxa_magic_le_at f Hm)).
  Qed.

  (* a file shorter than a header cannot even be parsed
     ([ElfBridge.elf_parse_ehdr_fields]'s length conjunct) *)
  Lemma kxa_short_bad_wf (f : elf_bytes) :
    (length f < 64)%nat -> elf_wf f = false.
  Proof.
    intros Hlen. unfold elf_wf.
    destruct (elf_parse_ehdr f) as [e |] eqn:E;
      [| destruct (elf_phdrs f); reflexivity].
    destruct (elf_parse_ehdr_fields f e E) as (Hl & _). exfalso. lia.
  Qed.

  (* AND THE COMPOSITE: whichever tail was taken, the node kexec observed is
     not a loadable file. *)
  (* [Hrow] is the receipt's own conditional file row -- which is where
     [inode_ok] was already spent, at the oracle's instant. *)
  Lemma kxa_not_loadable (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) (ef : nat -> bv 8) :
    (bv_unsigned (di_type dn) = FsImg.T_FILE_z ->
       abs_of (FsStateEra.era_node dn bm data)
       = MkAnode (AFile (FsTree.file_bytes data
                           (Z.to_nat (bv_unsigned (di_size dn)))))
                 (fn_nlink (FsStateEra.era_node dn bm data))) ->
    LA.kxc_bad_cause dn ef data ->
    ~ SpecKexecAU.anode_loadable (abs_of (FsStateEra.era_node dn bm data)).
  Proof.
    intros Hrow Hbad (f & nl & Heq & Hload).
    (* first: the row IS a file row, or [Heq] is already absurd *)
    assert (Hf : f = FsTree.file_bytes data
                       (Z.to_nat (bv_unsigned (di_size dn)))).
    { destruct (decide (bv_unsigned (di_type dn) = DirView.T_DIR_z)) as [Hd | Hd].
      - rewrite (FsAbsOpenFire.opf_era_dir_row dn bm data Hd) in Heq.
        injection Heq as Hn _. discriminate Hn.
      - destruct (decide (bv_unsigned (di_type dn) = FsImg.T_FILE_z))
          as [Ht | Ht].
        + rewrite (Hrow Ht) in Heq.
          injection Heq as Hn _. by rewrite Hn.
        + rewrite (FsAbsOpenFire.opf_era_dev_row dn bm data Hd Ht) in Heq.
          injection Heq as Hn _. discriminate Hn. }
    destruct Hload as (Hwf & _).
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hnn.
    destruct Hbad as [Hshort | (Hsz & Hgb & Hmag)].
    - (* too short to hold a header *)
      rewrite (kxa_short_bad_wf f) in Hwf; [discriminate |].
      rewrite Hf kxa_file_bytes_length. lia.
    - (* the magic word does not match *)
      rewrite (kxa_magic_bad_wf f) in Hwf; [discriminate |].
      rewrite Hf.
      rewrite -(le_at_of_file_bytes ef data
                  (Z.to_nat (bv_unsigned (di_size dn))) 0 0 4).
      + exact Hmag.
      + intros j Hj. rewrite Nat.add_0_l. apply Hgb. lia.
      + lia.
  Qed.

  (* arm (iii): the observation HAPPENED and exec failed past the lock, and
     the cause is [EfNotLoadable] on the nose. *)
  Lemma kxa_fail_obs (Sl : UexecSlot.uvis -> iProp Σ)
      (γ : FsBlocks.fs_names) (cw : Z) (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (L : nat) (zi : Z)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (pl : list (bv 8))
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (ef : nat -> bv 8) :
    L = length (path_elems pl) ->
    LA.kxc_bad_cause dn ef data ->
    kxa_receipt Sl P Φo L zi na alen afun sts dn bm data -∗
    SpecKexecAU.exec_post_fail Sl (FsBytesGamma.fs_gamma_L γ) γ cw P Pmiss Φo na alen afun sts.
  Proof.
    intros HL Hbad. iIntros "H". rewrite /kxa_receipt.
    iDestruct "H" as (av) "(%Hav & %Hrow & HΦ & HP & Hsl)".
    rewrite /SpecKexecAU.exec_post_fail. iRight. iExists pl. iRight.
    iExists zi, av, (abs_of (FsStateEra.era_node dn bm data)),
            SpecKexecAU.EfNotLoadable.
    rewrite -HL.
    iSplitL "HP"; [iExact "HP" |].
    iSplitR; [iPureIntro; exact Hav |].
    iSplitL "HΦ"; [iExact "HΦ" |].
    iSplitR; [iPureIntro; exact (kxa_not_loadable dn bm data ef Hrow Hbad) |].
    iExact "Hsl".
  Qed.

  (* ---- the pure row the receipt carries ----------------------------- *)
  (* [SpecKexecPin.fn_file_bytes_era_ok], restated (see the import note):
     on an ilock payload's node the byte reading IS the record's own
     [FsTree.file_bytes] of the payload's bytes. *)
  Lemma kxa_file_bytes_ok (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    inode_ok fsc_cov fsc_logst dn bm data ->
    fn_file_bytes (FsStateEra.era_node dn bm data)
    = FsTree.file_bytes data (Z.to_nat (bv_unsigned (di_size dn))).
  Proof.
    intros (_ & _ & _ & _ & Hsz & Hh & _).
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as H0.
    assert (Hcap : (Z.to_nat (bv_unsigned (di_size dn)) <= MAXFILE * BSIZE)%nat).
    { apply Nat2Z.inj_le. rewrite (Z2Nat.id _ H0) Nat2Z.inj_mul. exact Hsz. }
    rewrite /fn_file_bytes /fn_size FsStateEra.era_node_rec /FsTree.file_bytes.
    apply list_eq. intros k. rewrite !list_lookup_fmap.
    destruct (seq 0 (Z.to_nat (bv_unsigned (di_size dn))) !! k) as [x |] eqn:E;
      [| reflexivity].
    apply lookup_seq in E as [-> Hlt]. simpl. f_equal.
    rewrite /file_byte. f_equal.
    apply FsStateEra.era_node_data; [exact Hh |].
    apply Nat.Div0.div_lt_upper_bound. lia.
  Qed.

  Lemma kxa_file_row (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    inode_ok fsc_cov fsc_logst dn bm data ->
    bv_unsigned (di_type dn) = FsImg.T_FILE_z ->
    abs_of (FsStateEra.era_node dn bm data)
    = MkAnode (AFile (FsTree.file_bytes data (Z.to_nat (bv_unsigned (di_size dn)))))
              (fn_nlink (FsStateEra.era_node dn bm data)).
  Proof.
    intros Hok Hty.
    rewrite (FsAbsOpenFire.opf_era_file_row dn bm data Hty).
    by rewrite (kxa_file_bytes_ok dn bm data Hok).
  Qed.

  Lemma kxc_phaseA_au
      (Sl : UexecSlot.uvis -> iProp Σ)
      (Q : mword 64 -> ustate -> Prop)
      (QF : KexecOkQ.kxf_cause -> Prop)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate) (sts : list fdstate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (* THE AU BUNDLE'S PARAMETERS (SpecKexecAU sect. 2): the walk's
         cursor and miss receipt, and the observation's receipt shape. *)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (* the exit, opaque -- see the premise below *)
      (KEX : CpuId -> iProp Σ) :
    (* the failure-side plug's cause (S5), relayed: the pinned run's own
       two [bad:] tails are phase A's, and it plugs the hole vacuously. *)
    (exists c : KexecOkQ.kxf_cause, QF c) ->
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
    (* ==== THE AU BUNDLE, IN PLACE OF THE HEADER ORACLE.  The landed
       phase A relays an oracle it cannot answer; the pinned one answers it
       from a pin; this one SPENDS the caller's commit at that instant and
       hands the caller's receipt out. ==== *)
    SpecSysOpenAU.open_walk_pre_era fsc_fs (pv_cwi (us_V U)) P Pmiss -∗
    SpecSysOpenAU.aopen_commit_at ΓL fsabsE Φo -∗
    SpecKexecAU.exec_slot_pre Sl Φo na alen afun sts -∗
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
    (* ---- kexec's OWN continuation: BOTH [-1] tails close through it,
       AND BOTH OWE A REFUND -- which is why the wand takes one. ---- *)
    wp_next true (proc_addr jp) KEX -∗
    □ (∀ CX : CpuId,
       KEX CX -∗
       SpecKexecAU.exec_post_fail Sl ΓL fsc_fs (pv_cwi (us_V U)) P Pmiss Φo na alen afun sts -∗
      KexecOkQ.kexec_closer Q QF gf fsc_kalloc (proc_addr jp) pidv U m (ret_pc ra0) K b
           eb lks dqb dqs fsc_bmapstart na alen plen pv dqpv pfun
           av dqa avf aslen dqas afun) -∗
    (* ---- and the FALL-THROUGH: phase B's entry at +0x090, [kxc_phaseA]'s
       own row for row, with the receipt and the walk's cursor added. ---- *)
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
        ity_shot gyf (di_type dnf) -∗
        ifreeze_off (bv_unsigned inumf) -∗
        inode_ref_short kf (qf + sf)%Qp qf icfg_dev inumf -∗
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
        (* ==== THE ONE ROW THAT IS NOT [kxc_phaseA]'s: the caller's OWN
           receipt for the node the header was read from, at the inum the
           walk landed on, with the walk's cursor and the slot premise.
           [zi] is existential here for the same reason the landed exit's
           [kf] is: phase A found it, nothing above named it. ==== *)
        (∃ zi : Z,
           kxa_receipt Sl P Φo (length (path_elems (bview plen pfun))) zi
                       na alen afun sts dnf bmf datl) -∗
        kxc_frameA6x sp0 ra0 s00 s10 s20 pv av (m !!! Regidx Rs4) ef -∗
        wp_next (CID0 := CID) true (proc_addr jp) KEX -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hqf HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hcstr Hplen Hjp Hgs Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab Hwp Hoc Hsl #Hka Hbm Hins
             #Hbits Hpriv Hpath Hargv Hargs Hbs Hirs Hcont #Hkw Hcont90".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* the region invariant carries [ftop_inv]; the fire below opens it *)
    iDestruct (SpecKexec.fs_fabric_all with "Hfab")
      as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hireg & _)".
    iDestruct (ireg_inv_ftop with "Hireg") as "#Hftop".
    iApply (kxc_a1_au (CID0 := CID0) Q QF P Pmiss
              (SpecSysOpenAU.aopen_commit_at ΓL fsabsE Φo
                 ∗ SpecKexecAU.exec_slot_pre Sl Φo na alen afun sts)%I
              (SpecKexecAU.exec_post_fail Sl ΓL fsc_fs (pv_cwi (us_V U)) P Pmiss Φo na alen afun sts)
              gs jp gl pd pav pu gf
              plen pfun na avf alen aslen afun pidv U dqb dqs dqa dqpv dqas
              m K eb b lks sp0 ra0 s00 s10 s20 pv av KEX
              Hqf HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
              Hiregb Hcstr Hplen Hjp Hgs Hsp Hra Hs0 Hs1 Hs2
              Ha0 Ha1
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfab Hka Hbm Hins Hbits Hpriv
                    Hpath Hargv Hargs Hbs Hirs Hwp [$Hoc $Hsl] [] Hcont Hkw
                    [Hcont90]").
    { (* arm (ii) *)
      iIntros "H". iApply (kxa_fail_dead Sl fsc_fs (pv_cwi (us_V U)) P Pmiss Φo
                             na alen afun sts (bview plen pfun) with "H"). }
    (* ---- the seam at +0x032: [kxc_a2_r] takes it, at the receipt ---- *)
    iIntros (CIDs Hss M32 ipv zi n1) "HP [Hoc Hsl] Hseam Hexit".
    iDestruct (wp_next_retarget CID0 CIDs true (proc_addr jp) _ Hss
                 with "Hcont90") as "Hcont90".
    iApply (LA.kxc_a2_r (CID0 := CIDs) Q QF gs jp gl pd pav pu gf
              plen pfun na avf alen aslen afun pidv U dqb dqs dqa dqpv dqas
              m M32 K eb b lks sp0 ra0 s00 s10 s20 pv av ipv zi n1
              (kxa_receipt Sl P Φo (length (path_elems (bview plen pfun))) zi
                           na alen afun sts)
              (kxa_receipt_x Sl P Φo (length (path_elems (bview plen pfun))) zi
                             na alen afun sts)
              KEX
              Hqf HK Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
              Hiregb Hjp Hgs Hsp Hra Hs0 Hs1 Hs2
              with "Htext Hfab [HP Hoc Hsl] [] Hseam Hexit [] [Hcont90]").
    { (* ==== THE ORACLE'S INSTANT: the caller's commit, spent off the
         payload's own era leg.  [opf_open_fire] gives the leg straight
         back (an intact redeem is a READ), so the re-pack below is at the
         very same [data]. ==== *)
      iIntros (dn bm data) "%Hok Hpay".
      rewrite FsState.top_frag_1.
      iMod (FsAbsOpenFire.opf_open_fire fsc_fs ⊤ (DfracOwn 1) Φo zi
              (FsStateEra.era_node dn bm data) ltac:(solve_ndisj)
              with "Hftop Hoc Hpay") as "[Hpay Hobs]".
      iDestruct "Hobs" as (av0) "[%Hav HΦ]".
      iModIntro. rewrite -FsState.top_frag_1. iFrame "Hpay".
      rewrite /kxa_receipt. iExists av0.
      iSplitR; [iPureIntro; exact Hav |].
      iSplitR; [iPureIntro; exact (kxa_file_row dn bm data Hok) |].
      iFrame "HΦ HP Hsl". }
    { (* the buffer plays no part in the receipt *)
      iIntros (ef dn bm data) "_ H". rewrite /kxa_receipt_x. iExact "H". }
    { (* arm (iii), at the two [bad:] tails: the cause is [EfNotLoadable],
         discharged from the tail's own pure fact and the receipt's row. *)
      iIntros "!>" (CX dn bm data ef) "%Hbad HK HR".
      iApply ("Hkw" $! CX with "HK").
      iApply (kxa_fail_obs Sl fsc_fs (pv_cwi (us_V U)) P Pmiss Φo _ zi na alen afun sts
                (bview plen pfun) dn bm data ef ltac:(reflexivity) Hbad
                with "HR"). }
    (* ---- and the +0x090 exit: [kxc_phaseA]'s rows, plus the receipt ---- *)
    { iEval (rewrite /wp_next). iIntros (CIDx) "%Hqx".
      iSpecialize ("Hcont90" $! CIDx with "[%]"); [exact Hqx |].
      rewrite /LA.kxc_a2_exit1_r.
      iIntros (M90 kf qf sf inumf dnf bmf gilf gislf gyf loyf tlyf n2 ef datl).
      iIntros "%Hregs %Hn2 %Hgb Hpc Hcg Hcnt Hextc Hclmc Hslk Hslkd %Hly Hfly
               Hclaims Hdep Hoffr Hidev Hiinum Hivalid Hload Hity Hfrz Href Hru
               Hlog Hirs2 Hbm2 Hins2 Hbits2 Hbs2 Hka2 Hpriv2 Hpath2 Hargv2 Hargs2
               HR Hframe Hexit".
      iApply ("Hcont90" $! M90 kf qf sf inumf dnf bmf gilf gislf gyf loyf tlyf
                n2 ef datl
                with "[%] [%] [%] Hpc Hcg Hcnt Hextc Hclmc Hslk Hslkd [%] Hfly
                      Hclaims Hdep Hoffr Hidev Hiinum Hivalid Hload Hity Hfrz
                      Href Hru Hlog Hirs2 Hbm2 Hins2 Hbits2 Hbs2 Hka2 Hpriv2
                      Hpath2 Hargv2 Hargs2 [HR] Hframe Hexit").
      - exact Hregs.
      - exact Hn2.
      - exact Hgb.
      - exact Hly.
      - rewrite /kxa_receipt_x. iExists zi. iExact "HR". }
  Qed.

End KexecAUAMain.

End KexecAUAProof.
