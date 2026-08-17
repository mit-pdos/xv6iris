(* ProofKexecA.v -- PHASE A of kexec: [kexec+0x000] .. [kexec+0x08e], i.e.
   the prologue, myproc / begin_op / namei / ilock / readi, the ELF magic
   test, and the two [bad:] tails that are reachable from them.

     +0x000  addi sp,sp,-544          } BASE-encoded: 544 is past c.addi16sp's
     +0x004  sd   ra,536(sp)          } +-512 and 536 past c.sdsp's 504 --
     +0x008  sd   s0,528(sp)          } kexec is the only function in the tree
     +0x00c  sd   s1,520(sp)          } of which that is true (kexec.md).
     +0x010  sd   s2,512(sp)          } slots 1,2,3,4 = ra,s0,s1,s2
     +0x014  addi s0,sp,544           s0 = sp0
     +0x016  mv   s2,a0               s2 = path
     +0x018  sd   a0,-528(s0)         spill path  -> slot 66
     +0x01c  sd   a1,-512(s0)         spill argv  -> slot 64
     +0x020  jal  myproc              -> a0 = pj
     +0x024  mv   s1,a0
     +0x026  jal  begin_op            -> log_op g MAXOPBLOCKS
     +0x02a  mv   a0,s2
     +0x02c  jal  namei               -> a0 = ip, or 0
     +0x030  beqz a0, +0x88           namei failed
     +0x032  sd   s4,496(sp)          LAZY spill of s4 -> slot 6
     +0x034  mv   s4,a0               s4 = ip
     +0x036  jal  ilock
     +0x03a  li   a4,64               n    = 64
     +0x03e  li   a3,0                off  = 0
     +0x040  addi a2,s0,-432          dst  = &elf = pa_stk sp0 54
     +0x044  li   a1,0                user = 0     <- readi's KERNEL arm
     +0x046  mv   a0,s4
     +0x048  jal  readi
     +0x04c  li   a5,64
     +0x050  bne  a0,a5, +0x64        short read -> bad
     +0x054  lw   a4,-432(s0)         elf.magic
     +0x058  lui  a5,0x464c4
     +0x05c  addi a5,a5,1407          a5 = 0x464c457f = ELF_MAGIC
     +0x060  beq  a4,a5, +0x90        magic ok -> PHASE B
     [+0x064 bad:]  mv a0,s4 ; jal iunlockput ; jal end_op ; li a0,-1 ;
                    ld s4,496(sp) ; fall into the epilogue
     [+0x072 epilogue -- ProofKexecParts.kxc_epi_frame]
     [+0x088 namei-null tail:]  jal end_op ; li a0,-1 ; j +0x72

   ---- STATUS -----------------------------------------------------------

   PROVEN HERE: the frame algebra, [kxc_prologue] (+0x000..+0x01c),
   [kxc_exit_m1] (the shared -1 exit at +0x072), the seam [kxc_at_a2], and
   [kxc_a1] -- +0x000 .. +0x030 INCLUDING the namei-null tail at +0x088,
   which closes kexec's own failure arm.  No [admit] / [Admitted] / [Axiom].

   NOT YET WRITTEN: [kxc_a2] (+0x032 .. +0x08e, owning the +0x064 tail) and
   [kxc_phaseA].  Everything they need that is not mechanical is proved
   below: [kxc_slot6_sp] (496(sp), for the s4 spill and its reload),
   [kxc_elf_acc] (the elf buffer borrowed as 64 NAMED bytes for readi and
   given back), [kxc_word4_of_named] / [kxc_named_of_word4] (the [lw] at
   +0x054), [kxc_seq_split_4], and [kxc_exit_m1] itself.

   TWO THINGS THAT MAKE [kxc_a2] SMALLER THAN IT LOOKS, and both are worth
   knowing before writing it:

   * NEITHER COMPARISON NEEDS BIT-LEVEL REASONING.  The [bne a0,64] at
     +0x050 and the [beq a4,a5] at +0x060 are BLIND case splits: both arms
     are handled (fall through to +0x090, or take the +0x064 tail), and
     neither seam has to say WHY.  In particular the +0x090 state does NOT
     need [ElfEnc.eh_magic_ok] -- kexec's contract says nothing about the
     file being a valid ELF, so nothing downstream consumes it -- and it
     does not need [tot = 64] either, because the buffer's contents are
     existential at every seam anyway.  Splitting on
     [destruct (eq_vec ...) eqn:E] and using the fall/taken leaf pair is the
     whole of it.
   * THE OPEN INODE TRAVELS AS ONE BUNDLE (kexec.md convention 4): what
     ilock produces and iunlockput consumes is [sleeplocked], [sl_pid],
     [ic_deposit], the two 1/2 identity cells, [i_valid], [ic_loaded] and
     the retained [inode_ref_short].  readi peels [ic_loaded] into
     [inode_meta] / [inode_map] / [inode_blocks] and hands them back
     LITERALLY unchanged, so the re-assembly re-uses the pure conjuncts
     verbatim (ProofFileread.v ~:1995).

   ---- WHAT TO DO FIRST IN EVERY PHASE LEMMA (adopted; B, C and D too) ----

   PIN [b = eb = true] BEFORE ANYTHING ELSE, with [kxc_sie_b_agree] below
   (ProofFileclose's / ProofIput's [sie_b_agree], verbatim):

       iDestruct (kxc_sie_b_agree m 0%nat K eb b pj C with "Hcg Hcnt") as %Ho.
       subst eb. cbn in Ho. subst b.

   [sie_cap_gpr]'s SIE eighth and [cpu_own]'s [cpu_hart] are two
   presentations of the same bit, so at [n = 0] this reads [b = eb] straight
   off the precondition and kexec's [eb = true] premise then pins it.  It is
   not a convenience: every parking callee (namei, ilock, readi, end_op)
   publishes [wp_next TRUE], and [WpNext.wp_next_chain] cannot produce the
   [pj = zero_reg] disjunct from a SYMBOLIC [b] -- so without this step the
   very first [cpu_own_transport] after namei is unprovable, and
   [wp_kexec_sconf_body]'s own [wp_next b pj] could never be closed.

   ---- ESCALATION: [ProcInv.cwd_ref] AND [SpecNamei] ARE AT DIFFERENT
        [icacheG] INSTANCES ------------------------------------------------

   [FileInvDefs.fileG] BUNDLES [icacheG] and [icfg] as field instances
   ([file_icacheG ::], [file_icfg ::]).  So a context that binds BOTH
   [!fileG Σ] and a standalone [!icacheG Σ] / [ICFG : icfg] -- which is
   exactly what SpecNamei.v:90-93 does, and what SpecKexec.v copied -- has
   TWO [icacheG]s, and durable-notes.md's second typeclass trap is live:

     * [ProcInv.cwd_ref] (ProcInv.v:613) elaborates its [inode_held] through
       [fileG] (ProcInv's own Context has no standalone [icacheG]);
     * [SpecNamei]'s [inode_held cwdv] premise elaborates through the
       standalone one.

   The two print IDENTICALLY and do not unify: machine-checked, the wand
   [cwd_ref v -∗ inode_held v] fails with "iFrame: cannot frame (cwd_ref v)"
   in a context binding both, and closes by [iIntros "$"] in a context
   binding only [fileG].  kexec is the FIRST caller to hand a process's
   working-directory reference to namei, which is why this has never fired.

   THE FIX IS SpecNamei.v's (and then SpecNamex / SpecNameiparent /
   SpecKexec, and any Spec in that chain that binds both): DROP the
   standalone [ICFG : icfg, !icacheG Σ] and let [!fileG Σ] supply them --
   durable-notes' recorded remedy, and the same edit the kfork chain and
   fileread already took.  It changes the [Module Type] binder lists, so it
   is a Spec-level change and not this file's to make.

   WHAT THIS FILE DOES INSTEAD, and why it is exactly the post-fix shape:
   the two proof Sections below bind [!fileG Σ] and NOT [!icacheG Σ] /
   [ICFG].  Every [icacheG] in sight is then [file_icacheG], [cwd_ref]
   matches [inode_held], and the callee contracts (whose Module Type
   Parameters quantify over ALL [icacheG]) are instantiated at that one.
   So [kxc_a1] is proved TODAY and will need no edit once the Specs are
   fixed.  What CANNOT be built until they are is the capstone: discharging
   [KEXEC]'s Parameter requires the body at an ARBITRARY standalone
   [icacheG], and at a mismatched one [wp_kexec_sconf_body] is not merely
   unprovable but incoherent -- it asks for FS invariants at one icache and
   a process whose cwd reference is at another.

   ---- THE SEAM, AND HOW IT DIFFERS FROM THE BRIEF ------------------------

   [kxc_at_a2] carries the frame's slots 14..63 as ONE [stack_own] chunk
   rather than as the three pre-made [bytes_own] carves.  That is a
   deliberate simplification and it is the better currency at a block
   boundary: the epilogue ([ProofKexecParts.kxc_epi_frame], through
   [kxc_frame]) wants [stack_own (pa_stk sp0 13) 55] BACK, so a seam stated
   in bytes would have to be re-slotted at every exit -- and re-slotting
   needs the per-slot alignment facts, which a byte run does not carry.
   Whichever half wants a buffer carves it itself, at the one place it is
   used, with [ProofKexecParts.kxc_slots_elf] / [kxc_slots_ph] /
   [kxc_slots_ustack] over [kxc_slots_asc] below.  Nothing is lost: the
   chunk determines the three carves and they do not determine it.

   ---- WHAT MOVED OUT ---------------------------------------------------

   The frame/seam algebra and the two shared bottom blocks ([kxc_exit_m1],
   [kxc_bad64], and the icache accessors they use) now live in
   ProofKexecTail.v, because ProofKexecB.v needs them and requiring THIS file
   to get them put the two proofs in series in the build.  Phase A opens that
   functor as [T] below and is otherwise unchanged.  See ProofKexecTail.v's
   header. *)
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
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.   (* [is_sleeplock]: the nightly dead-import sweep re-pointed the chain that used to carry it *)
Require Import WpLock.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import ElfEnc.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import ProcInv.
Require Import FileInvDefs.
(* Names the nightly dead-import sweep stopped delivering transitively. *)
Require Import DinodeEnc.
Require Import InodeLock.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecIput.
Require Import SpecKexec.
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
Require Import ProofKexecParts.
Require Import ProofKexecTail.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXA := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  PHASE A's TWO HALVES.                                                 *)
(* ===================================================================== *)
Module KexecAProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                   (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                   (EndOp : END_OP).


(* The shared bottom blocks, at phase A's own seven modules.  [T.kxc_bad64] is
   the +0x064 tail both of [kxc_a2]'s tests fall into; [T.kxc_exit_m1] is the
   [-1] return underneath it. *)
Module T := ProofKexecTail.KexecTailProof Myproc BeginOp Namei Ilock Readi
                                          Iunlockput EndOp.

(* A SEPARATE SECTION FROM THE ONE [T.kxc_exit_m1] IS PROVED IN, and it has
   to be: that lemma is applied at the hart the [c.j] at +0x08e (resp. the
   fall-through at +0x070) resumed on, not at the section hart.  A SIBLING
   lemma in the same Section resolves its [CpuId] through the section variable
   BY NAME, so [sie_cap_gpr] in its premise would mean the ENTRY hart and the
   application fails with "cannot instantiate (P -* Q) with P" printing the
   SAME TERM TWICE (durable-notes.md).  Closing the section first generalises
   it, and the application then resolves [CID] from the caller's own
   hypotheses.  The file split now enforces this for free -- [T.kxc_exit_m1]
   and [T.kxc_bad64] live in ProofKexecTail.v -- but the constraint is on the
   SECTION, not on the file, so it is recorded here where the application is:
   moving either lemma back beside its caller would reintroduce it. *)
Section KexecABody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.  (* NB: icacheG + icfg come from
              [fileG] -- see the header.  A standalone [!icacheG Σ] beside
              [!fileG Σ] is a SECOND instance and [ProcInv.cwd_ref] then does
              not match [SpecNamei]'s [inode_held]. *)
  Context `{GEN : GenId} `{CID0 : CpuId}.

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

  (* =================================================================== *)
  (*  +0x000 .. +0x030, PLUS the namei-null tail at +0x088.               *)
  (* =================================================================== *)
  Lemma kxc_a1
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    (K_kexec <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    (* the inode region's two ambient ties, threaded to namei (fs-log.md
       §G.25) *)
    g = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    eb = true ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Ra0 = pv ->
    m !!! Regidx Ra1 = av ->
    sie_cap_gpr KT1 m K b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    kernel_text -∗ pc_is (mword_of_int KXA : mword 64) -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kalloc_env ga None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
    bslots bn 3 -∗
    iref_slots 2 -∗
    (* ---- kexec's OWN continuation: the +0x088 tail closes the -1 arm ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) b lks -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
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
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M32 : regfile) (used1 : gset Z) (ipv : mword 64) (n1 : nat),
        kxc_at_a2 jp bn g gfs ga gf cov logstart bmapstart inodestart size
                  used used1 plen pfun na avf aslen afun pidv V dqb dqs dqa
                  m M32 K eb b lks sp0 ra0 s00 s10 s20 pv av ipv n1 -∗
        wp_next (CID0 := CID) b (proc_addr jp) (fun (CIDx : CpuId) =>
          ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
            (entry spv szv' : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
              sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
              cpu_own 0 eb (proc_addr jp) b lks -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              ⌜used' ⊆ used⌝ -∗
              bitmap_res gfs bmapstart cov logstart size used' -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
              ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
              ([∗ list] i ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
              bslots bn 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hcstr Hplen Hjp Hgs Heb Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    
    iIntros "Hcg Hcnt #Htext Hpc #Hfab #Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hcont Hcont32".
    (* ---- b = eb = true (see the header) ---- *)
    iDestruct (kxc_sie_b_agree m 0%nat K eb b (proc_addr jp) lks with "Hcg Hcnt") as %Houtb.
    subst eb. cbn in Houtb. subst b.
    (* depth 0 forces the held set empty, so begin_op's order premise ("log",
       3) needs no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct "Hfab" as "(#Hkd & #Hpenv & #Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock)".
    (* ---- open the process's private block ONCE (convention 2) ---- *)
    iDestruct (proc_priv_cwd_pid gf (proc_addr jp) pidv V with "Hpriv")
      as "(Hcwd & Hcref & Hppid & Hpvbk)".
    (* ---- +0x000 .. +0x01c ---- *)
    iApply (kxc_prologue m K true (proc_addr jp) sp0 ra0 s00 s10 s20 pv av
              ltac:(lia) Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1 with "Hcg Htext Hpc").
    iIntros (CIDp Hsp1 M1) "%HM1 Hcg Hpc Hframe".
    destruct HM1 as (HM1sp & HM1s0 & HM1s2 & HM1a0 & HM1a1 & HM1thr).
    (* ---- +0x020: jal ra,myproc ---- *)
    iPoseProof (kxc_020 with "Htext") as "Hi020".
    assert (Htmp : add_vec (mword_of_int (KXA + 0x20) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085218 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x20)) Rra
              (mword_of_int 2085218 : mword 21) M1 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htmp; vm_compute; reflexivity)
              with "Hcg Hpc Hi020").
    iIntros (CIDj1 Hsj1) "Hcg Hpc". iEval (rewrite Htmp) in "Hpc".
    set (N1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x20) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x20) : mword 64) 4)]> M1) with N1.
    assert (HN1ra : N1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x20) : mword 64) 4)
      by (rewrite /N1; apply upd_eq).
    iDestruct (cpu_own_transport CID0 CIDj1 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Myproc.wp_myproc_sconf N1 (K - 68)%nat 0%nat true (proc_addr jp) true lks
              ltac:(vm_compute; reflexivity) ltac:(lia)
              with "Hcg Hcnt Htext Hpc").
    iIntros (CIDm Hsm ms M2) "%Hmsf Hcg Hcnt Hpc %Hmp".
    destruct Hmp as (Hcsm & Hm2a0).
    assert (Hpc24 : ret_pc (N1 !!! Regidx Rra) = mword_of_int (KXA + 0x24))
      by (rewrite HN1ra; pcw).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- +0x024: c.mv s1,a0 -- s1 := p ---- *)
    iPoseProof (kxc_024 with "Htext") as "Hi024".
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x24)) Rs1 Ra0
              M2 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi024").
    iIntros (CIDv1 Hsv1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2).
    assert (HN2s1 : N2 !!! Regidx Rs1 = (proc_addr jp)).
    { rewrite /N2 upd_eq Hm2a0. apply add_vec_zero_l. }
    assert (Hpp026 : add_vec_int (mword_of_int (KXA + 0x24) : mword 64) 2
                     = mword_of_int (KXA + 0x26)) by pcw.
    iEval (rewrite Hpp026) in "Hpc".
    (* ---- +0x026: jal ra,begin_op ---- *)
    iPoseProof (kxc_026 with "Htext") as "Hi026".
    assert (Htbo : add_vec (mword_of_int (KXA + 0x26) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094234 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x26)) Rra
              (mword_of_int 2094234 : mword 21) N2 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htbo; vm_compute; reflexivity)
              with "Hcg Hpc Hi026").
    iIntros (CIDj2 Hsj2) "Hcg Hpc". iEval (rewrite Htbo) in "Hpc".
    set (N3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x26) : mword 64) 4)]> N2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x26) : mword 64) 4)]> N2) with N3.
    assert (HN3ra : N3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x26) : mword 64) 4)
      by (rewrite /N3; apply upd_eq).
    assert (HN3s1 : N3 !!! Regidx Rs1 = (proc_addr jp))
      by (rewrite /N3 upd_ne; [exact HN2s1 | nz]).
    iDestruct (cpu_own_transport CIDm CIDj2 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (BeginOp.wp_begin_op_sconf gs jp gl bn g gfs cov logstart dev
              pidv (DfracOwn (1/4)) N3 (K - 68)%nat true true lks
              ltac:(lia) Hjp Hgs
              with "Hcg Hcnt [] [] Htext Hpc Hlogc Hppid Hprocs").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CIDb Hsb M3) "%Hcsb Hcg Hcnt _ _ Hpc Hppid Hlog".
    assert (Hpc2a : ret_pc (N3 !!! Regidx Rra) = mword_of_int (KXA + 0x2a))
      by (rewrite HN3ra; pcw).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- +0x02a: c.mv a0,s2 -- a0 := path ---- *)
    iPoseProof (kxc_02a with "Htext") as "Hi02a".
    assert (HM3s2 : M3 !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcsb Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsm Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N1 upd_ne; [exact HM1s2 | nz]. }
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x2a)) Ra0 Rs2
              M3 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi02a").
    iIntros (CIDv2 Hsv2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M3 !!! Regidx Rs2))]> M3).
    assert (HN4a0 : N4 !!! Regidx Ra0 = pv).
    { rewrite /N4 upd_eq HM3s2. apply add_vec_zero_l. }
    assert (Hpp02c : add_vec_int (mword_of_int (KXA + 0x2a) : mword 64) 2
                     = mword_of_int (KXA + 0x2c)) by pcw.
    iEval (rewrite Hpp02c) in "Hpc".
    (* ---- +0x02c: jal ra,namei ---- *)
    iPoseProof (kxc_02c with "Htext") as "Hi02c".
    assert (Htnm : add_vec (mword_of_int (KXA + 0x2c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093750 : mword 21))
                   = mword_of_int KernelSyms.namei) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x2c)) Rra
              (mword_of_int 2093750 : mword 21) N4 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htnm; vm_compute; reflexivity)
              with "Hcg Hpc Hi02c").
    iIntros (CIDj3 Hsj3) "Hcg Hpc". iEval (rewrite Htnm) in "Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x2c) : mword 64) 4)]> N4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x2c) : mword 64) 4)]> N4) with N5.
    assert (HN5ra : N5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x2c) : mword 64) 4)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a0 : N5 !!! Regidx Ra0 = pv)
      by (rewrite /N5 upd_ne; [exact HN4a0 | nz]).
    iDestruct (cpu_own_transport CIDb CIDj3 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
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
    iDestruct "Hlog" as (Sb0) "Hlog".
    iApply (Namei.wp_namei_gen gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
              ga gf cov logstart bmapstart inodestart nib size dev used
              (pv_cwd V) plen pfun MAXOPBLOCKS Sb0 pidv (DfracOwn (1/4)) dqb dqs
              (DfracOwn 1) N5 (K - 68)%nat true true lks
              ltac:(lia) Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0
              Hbmc Hbml Hins0 Hcovb Hiregb Hcstr Hplen
              ltac:(unfold walk_need, iput_units, MAXOPBLOCKS;
                    destruct (length (path_elems (bview plen pfun))); lia)
              Hjp Hgs eq_refl
              with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hka Hitab Hitinv Hesc
                    Hslks Hireg Hprocs Hdevi Hdgeom Hdlock Hbm Hins Hbits Hppid
                    Hcwd Hcref Hpath Hbs Hirs Hlog").
    iIntros (CIDn Hsn M4 n1 used1 Sb1 ok ipv w) "%Hcsn Hcg Hcnt Hpc Hbm Hins %Hused1
             Hbits Hppid Hcwd Hcref Hpath Hbs %HSbsub %Hwbm %Hn1 Hlog Harm".
    iDestruct (log_opS_op with "Hlog") as "Hlog".
    (* what the seam actually carries: the closing iunlockput's three units.
       The walk spent at most two of the ten. *)
    assert (Hiu1 : (iput_units <= n1)%nat).
    { unfold walk_spend, iput_units, MAXOPBLOCKS in *. destruct w, ok; lia. }
    iEval (rewrite HN5a0) in "Hpath".
    assert (Hpc30 : ret_pc (N5 !!! Regidx Rra) = mword_of_int (KXA + 0x30))
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
    iPoseProof (kxc_030 with "Htext") as "Hi030".
    destruct ok.
    - (* ============ namei SUCCEEDED: fall through to +0x032 ============ *)
      iDestruct "Harm" as "(%HM4a0 & Hheld & Hirs)".
      iDestruct (inode_held_ne_zero with "Hheld") as %Hipvnz.
      assert (Hcmp : eq_vec (rget M4 Ra0) (zero_reg : mword 64) = false).
      { rewrite (rget_ne M4 Ra0 ltac:(nz)) HM4a0.
        destruct (eq_vec ipv (zero_reg : mword 64)) eqn:E; [| reflexivity].
        exfalso. apply Hipvnz. by apply eq_vec_true_iff in E. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXA + 0x30))
                (mword_of_int 44 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M4 (K - 68)%nat true
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                with "Hcg Hpc Hi030").
      iIntros (CIDz Hsz1) "Hcg Hpc".
      assert (Hpp032 : add_vec_int (mword_of_int (KXA + 0x30) : mword 64) 2
                       = mword_of_int (KXA + 0x32)) by pcw.
      iEval (rewrite Hpp032) in "Hpc".
      (* close the private block back up, at the cwd it lent out *)
      iDestruct ("Hpvbk" $! (pv_cwd V) with "Hcwd [Hcref] Hppid") as "Hpriv".
      { iEval (rewrite /cwd_ref). iExact "Hcref". }
      rewrite kxc_upd_cwd_id.
      iDestruct (cpu_own_transport CIDn CIDz 0%nat true (proc_addr jp) true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont32" $! CIDz with "[%]"); [wp_next_chain |].
      (* hand the exit back, re-anchored at [CIDz] (the crossing fact by NAME,
         never as an inline [ltac:] in argument position -- durable-notes) *)
      assert (Hcrz : true = false \/ proc_addr jp = zero_reg ->
                     (CIDz : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CIDz true (proc_addr jp) _ Hcrz
                   with "Hcont") as "Hcont".
      iApply ("Hcont32" $! M4 used1 ipv n1 with "[-Hcont] Hcont").
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
      iSplitR; [iPureIntro; exact Hiu1 |].
      iSplitL "Hlog"; [iExact "Hlog" |].
      iSplitL "Hheld"; [iExact "Hheld" |].
      iSplitL "Hirs"; [iExact "Hirs" |].
      iSplitR; [iPureIntro; exact Hused1 |].
      iSplitL "Hbits"; [iExact "Hbits" |].
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
      iDestruct "Harm" as "(%HM4a0 & Hirs)".
      assert (Hcmp : eq_vec (rget M4 Ra0) (zero_reg : mword 64) = true).
      { rewrite (rget_ne M4 Ra0 ltac:(nz)) HM4a0.
        apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity. }
      assert (Htgt88 : add_vec (mword_of_int (KXA + 0x30) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 44 : mword 8) ('b"0"))))
              = mword_of_int (KXA + 0x88)) by pcw.
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXA + 0x30))
                (mword_of_int 44 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M4 (K - 68)%nat true
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                ltac:(rewrite Htgt88; vm_compute; reflexivity)
                with "Hcg Hpc Hi030").
      iIntros (CIDz Hsz1). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt88) in "Hpc".
      (* ---- +0x088: jal ra,end_op ---- *)
      iPoseProof (kxc_088 with "Htext") as "Hi088".
      iPoseProof (kxc_08c with "Htext") as "Hi08c".
      iPoseProof (kxc_08e with "Htext") as "Hi08e".
      assert (Hteo : add_vec (mword_of_int (KXA + 0x88) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094276 : mword 21))
                     = mword_of_int KernelSyms.end_op) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x88)) Rra
                (mword_of_int 2094276 : mword 21) M4 (K - 68)%nat true
                ltac:(nz) ltac:(rdok)
                ltac:(rewrite Hteo; vm_compute; reflexivity)
                with "Hcg Hpc Hi088").
      iIntros (CIDj4 Hsj4) "Hcg Hpc". iEval (rewrite Hteo) in "Hpc".
      set (P1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KXA + 0x88) : mword 64) 4)]> M4).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KXA + 0x88) : mword 64) 4)]> M4) with P1.
      assert (HP1ra : P1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KXA + 0x88) : mword 64) 4)
        by (rewrite /P1; apply upd_eq).
      iDestruct (cpu_own_transport CIDn CIDj4 0%nat true (proc_addr jp) true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (EndOp.wp_end_op_sconf gs jp gl gu gd gk pd pav pu bn g gfs
                cov logstart dev n1 pidv (DfracOwn (1/4)) P1 (K - 68)%nat
                true true lks ltac:(lia) Hlg Hjp Hgs
                with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hcrash Hcert
                      Hppid Hprocs Hdevi Hdgeom Hdlock Hlog").
      all: try lkbelow.
      { rewrite /trap_csrs_ext. done. }
      { rewrite /cpu_claim_ext. done. }
      iIntros (CIDe1 Hse1 M5) "%Hcse Hcg Hcnt _ _ Hpc Hppid".
      assert (Hpc8c : ret_pc (P1 !!! Regidx Rra) = mword_of_int (KXA + 0x8c))
        by (rewrite HP1ra; pcw).
      iEval (rewrite Hpc8c) in "Hpc".
      (* ---- +0x08c: c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KXA + 0x8c)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                M5 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi08c").
      iIntros (CIDl1 Hsl1) "Hcg Hpc".
      set (P2 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> M5).
      assert (HP2a0 : P2 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /P2; apply upd_eq).
      assert (Hpp08e : add_vec_int (mword_of_int (KXA + 0x8c) : mword 64) 2
                       = mword_of_int (KXA + 0x8e)) by pcw.
      iEval (rewrite Hpp08e) in "Hpc".
      (* ---- +0x08e: c.j -28 -> +0x072 ---- *)
      assert (Htj72 : add_vec (mword_of_int (KXA + 0x8e) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
              = mword_of_int (KXA + 0x72)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KXA + 0x8e))
                (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                P2 (K - 68)%nat true
                ltac:(rewrite Htj72; vm_compute; reflexivity)
                with "Hcg Hpc Hi08e").
      iIntros (CIDz2 Hsz2). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htj72) in "Hpc".
      (* ---- close the private block and take the shared exit ---- *)
      iDestruct ("Hpvbk" $! (pv_cwd V) with "Hcwd [Hcref] Hppid") as "Hpriv".
      { iEval (rewrite /cwd_ref). iExact "Hcref". }
      rewrite kxc_upd_cwd_id.
      iDestruct (cpu_own_transport CIDe1 CIDz2 0%nat true (proc_addr jp) true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
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
      iApply (T.kxc_exit_m1 (proc_addr jp) bn gfs ga gf cov logstart bmapstart inodestart
                size used used1 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m P2 K true true lks sp0 ra0 s00 s10 s20 pv av
                ltac:(lia) Hused1 Hsp Hra Hs0 Hs1 Hs2 HP2sp HP2a0 HP2thr
                with "Hcg Hcnt Htext Hpc [Hframe] Hbm Hins Hbits Hka Hpriv
                      Hpath Hargv Hargs Hbs Hirs").
      { iApply (kxc_frameA_epi with "Hframe"). }
      iIntros (CIDf Hsf mf used2 V' entry spv szv') "%Hcs2 %Hok Hcg Hcnt Hpc
               Hbm Hins %Hu2 Hbits Hka2 Hpriv Hpath Hargv Hargs Hbs Hirs".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf used2 V' entry spv szv'
                with "[%] [%] Hcg Hcnt Hpc Hbm Hins [%] Hbits Hka2 Hpriv
                      Hpath Hargv Hargs Hbs Hirs").
      + exact Hcs2.
      + exact Hok.
      + exact Hu2.
  Qed.

  (* =================================================================== *)
  (*  +0x032 .. +0x08e, PLUS the short-read / bad-magic tail at +0x064.   *)
  (*                                                                      *)
  (*  Both comparisons are BLIND case splits: the [bne a0,64] at +0x050    *)
  (*  and the [beq a4,a5] at +0x060 each have both arms handled, and       *)
  (*  neither seam has to say why.  In particular +0x090 carries NEITHER   *)
  (*  [eh_magic_ok] NOR [tot = 64] -- kexec's contract says nothing about  *)
  (*  the file being a valid ELF, and the buffer's contents are            *)
  (*  existential at every seam anyway.                                    *)
  (*                                                                      *)
  (*  THE ELF BUFFER GOES BACK INTO THE FRAME at +0x090, with its          *)
  (*  per-slot alignment facts beside it: phase B re-carves with           *)
  (*  [kxc_elf_acc] at the one place it reads a field.  Handing out NAMED  *)
  (*  bytes instead would buy nothing -- the naming function is            *)
  (*  existential either way -- and would cost a third frame shape.        *)
  (* =================================================================== *)
  Lemma kxc_a2
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used used1 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa : dfrac)
      (m M32 : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av ipv : mword 64) (n1 : nat) :
    (K_kexec <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    (* the inode region's two ambient ties, threaded to namei (fs-log.md
       §G.25) *)
    g = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    eb = true ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    kernel_text -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kxc_at_a2 jp bn g gfs ga gf cov logstart bmapstart inodestart size
              used used1 plen pfun na avf aslen afun pidv V dqb dqs dqa
              m M32 K eb b lks sp0 ra0 s00 s10 s20 pv av ipv n1 -∗
    (* ---- kexec's OWN continuation: the +0x064 tail closes the -1 arm ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) b lks -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    (* ---- and the FALL-THROUGH: the state at +0x090, phase B's entry ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M90 : regfile) (kf : nat) (qf sf : Qp) (inumf : mword 32)
        (dnf : dinode) (bmf : blkmap) (gilf gislf gyf : gname)
        (n2 : nat) (used2 : gset Z),
        ⌜ M90 !!! Regidx csp_rs1 = pa_stk sp0 68 /\
          M90 !!! Regidx Rs0 = sp0 /\
          M90 !!! Regidx Rs1 = proc_addr jp /\
          M90 !!! Regidx Rs2 = pv /\
          M90 !!! Regidx Rs4 = ientry kf /\
          (kf < NINODE)%nat /\
          bv_unsigned inumf < 16 * Z.of_nat nib /\
          (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
             r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
             M90 !!! Regidx r = m !!! Regidx r) ⌝ -∗
        ⌜ (iput_units <= n2)%nat /\ used2 ⊆ used ⌝ -∗
        pc_is (mword_of_int (KXA + 0x90) : mword 64) -∗
        sie_cap_gpr KT1 M90 (K - 68)%nat b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        is_sleeplock_gen gilf gislf (i_lock (ientry kf)) "inode"%string
                     (ic_tok cn kf) (slh_tok (icfg_isl kf)) -∗
        sleeplocked_q gislf sf -∗
        sl_pid (i_lock (ientry kf)) ↦₄ pidv -∗
        ic_deposit cn kf (DepShr sf dev inumf gyf) -∗
        i_dev (ientry kf) ↦₄{DfracOwn (1/2)} dev -∗
        i_inum (ientry kf) ↦₄{DfracOwn (1/2)} inumf -∗
        i_valid (ientry kf) ↦₄ valid_word true -∗
        ic_loaded gfs gi cov logstart kf inumf dnf bmf -∗
        (* SpecIlock v5's additive type witness, at the generation the
           share names -- what SpecIunlockput now needs at +0x064. *)
        ity_shot gyf (di_type dnf) -∗
        inode_ref_short kf (qf + sf)%Qp qf dev inumf -∗
        log_op g n2 -∗
        iref_slots 1 -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used2 -∗
        bslots bn 3 -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        kxc_frameA6 sp0 ra0 s00 s10 s20 pv av (m !!! Regidx Rs4) -∗
        (* THE EXIT, HANDED BACK -- see [kxc_phaseA]'s copy below. *)
        wp_next (CID0 := CID) b (proc_addr jp) (fun (CIDy : CpuId) =>
          ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
            (entry spv szv' : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
              sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
              cpu_own 0 eb (proc_addr jp) b lks -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              ⌜used' ⊆ used⌝ -∗
              bitmap_res gfs bmapstart cov logstart size used' -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
              ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
              ([∗ list] i ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
              bslots bn 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hjp Hgs Heb Hsp Hra Hs0 Hs1 Hs2.
    pose proof HK as HK'. 
    iIntros "#Htext #Hfab Hseam Hcont Hcont90".
    rewrite /kxc_at_a2.
    iDestruct "Hseam" as "(%Hregs & Hpc & Hcg & Hcnt & %Hn1 & Hlog & Hheld &
                           Hirs & %Hused1 & Hbits & Hbs & Hbm & Hins & #Hka &
                           Hpriv & Hpath & Hargv & Hargs & Hframe)".
    destruct Hregs as (HM32sp & HM32s0 & HM32s1 & HM32s2 & HM32a0 & Hipvnz &
                       HM32thr).
    iDestruct (kxc_sie_b_agree M32 0%nat (K - 68)%nat eb b (proc_addr jp) lks
                 with "Hcg Hcnt") as %Houtb.
    subst eb. cbn in Houtb. subst b.
    (* depth 0 forces the held set empty, so the ilock/end_op order premises
       need no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct "Hfab" as "(#Hkd & #Hpenv & #Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock)".
    (* ---- the inode: slot, share, and the region facts ---- *)
    iDestruct "Hheld" as (k q inum) "(%Hie & %Hk & %Hib & Href)".
    iEval (rewrite -Hdev) in "Href".
    rewrite inode_ref_shed. iDestruct "Href" as "[Hkeep Hshr]".
    (* SpecIlock v5 takes the share at a NAMED generation
       ([IcacheRef.inode_shr_gen]); the conversion is the one every existing
       caller does ([inode_shr_gen_intro] -- SpecIlock's own porting note). *)
    iEval (rewrite inode_shr_gen_intro) in "Hshr".
    iDestruct "Hshr" as (gy) "Hshr".
    assert (Hib' : bv_unsigned inum < 16 * Z.of_nat nib)
      by (rewrite Hnib; exact Hib).
    destruct (Hiregb inum Hib') as [Hibc Hibl].
    iDestruct (T.kxa_esc_acc cn gfs gi cov logstart k Hk with "Hesc") as "#Hesck".
    iDestruct (T.kxa_slk_acc cn k Hk with "Hslks") as (gilk gislk) "#Hslkk".
    iDestruct (T.kxa_bs3_split bn with "Hbs") as "[Hbs1 Hbs2]".
    (* ---- open the process for the pid quarter ---- *)
    iDestruct (proc_priv_cwd_pid gf (proc_addr jp) pidv V with "Hpriv")
      as "(Hcwd & Hcref & Hppid & Hpvbk)".
    (* ---- the frame: slot 6, and the elf slots ---- *)
    rewrite /kxc_frameA.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & (%w6 & Hf6) & Hf7 &
                            Hf8 & Hf9 & Hf10 & Hf11 & Hf12 & Hf13 & Hmid &
                            Hf64 & Hf65 & Hf66 & Hf67 & Hf68)".
    iDestruct (kxc_mid_split sp0 with "Hmid") as "(Hust & Helf & Hph)".
    iPoseProof (kxc_032 with "Htext") as "Hi032".
    iPoseProof (kxc_034 with "Htext") as "Hi034".
    iPoseProof (kxc_036 with "Htext") as "Hi036".
    iPoseProof (kxc_03a with "Htext") as "Hi03a".
    iPoseProof (kxc_03e with "Htext") as "Hi03e".
    iPoseProof (kxc_040 with "Htext") as "Hi040".
    iPoseProof (kxc_044 with "Htext") as "Hi044".
    iPoseProof (kxc_046 with "Htext") as "Hi046".
    iPoseProof (kxc_048 with "Htext") as "Hi048".
    iPoseProof (kxc_04c with "Htext") as "Hi04c".
    iPoseProof (kxc_050 with "Htext") as "Hi050".
    iPoseProof (kxc_054 with "Htext") as "Hi054".
    iPoseProof (kxc_058 with "Htext") as "Hi058".
    iPoseProof (kxc_05c with "Htext") as "Hi05c".
    iPoseProof (kxc_060 with "Htext") as "Hi060".
    (* ---- +0x032: c.sdsp s4,496(sp) -- the LAZY spill of s4 ---- *)
    assert (Hpa6 : add_vec (M32 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 62 : mword 6)
                                                  ('b"000")))
                   = pa_stk sp0 6) by (rewrite HM32sp; apply kxc_slot6_sp).
    assert (Hs4v : rget M32 Rs4 = M32 !!! Regidx Rs4) by (apply rget_ne; nz).
    assert (HM32s4 : M32 !!! Regidx Rs4 = m !!! Regidx Rs4)
      by exact (HM32thr Rs4 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                        ltac:(nz) ltac:(nz)).
    iEval (rewrite -Hpa6) in "Hf6".
    iApply (wp_csdsp_s_sconf (mword_of_int (KXA + 0x32))
              (mword_of_int 62 : mword 6) Rs4 M32 (K - 68)%nat w6 true
              with "Hcg Hpc Hi032 Hf6").
    iIntros (CID1 Hsq1) "Hcg Hpc Hf6".
    iEval (rewrite Hpa6 Hs4v HM32s4) in "Hf6".
    assert (Hpp034 : add_vec_int (mword_of_int (KXA + 0x32) : mword 64) 2
                     = mword_of_int (KXA + 0x34)) by pcw.
    iEval (rewrite Hpp034) in "Hpc".
    (* ---- +0x034: c.mv s4,a0 -- s4 := ip ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x34)) Rs4 Ra0
              M32 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi034").
    iIntros (CID2 Hsq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q1 := <[Regidx Rs4 := regval_into_reg
                  (add_vec zero_reg (M32 !!! Regidx Ra0))]> M32).
    assert (HQ1s4 : Q1 !!! Regidx Rs4 = ientry k).
    { rewrite /Q1 upd_eq HM32a0 Hie. apply add_vec_zero_l. }
    assert (HQ1sp : Q1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /Q1 upd_ne; [exact HM32sp | nz]).
    assert (HQ1s0 : Q1 !!! Regidx Rs0 = sp0)
      by (rewrite /Q1 upd_ne; [exact HM32s0 | nz]).
    assert (HQ1s1 : Q1 !!! Regidx Rs1 = proc_addr jp)
      by (rewrite /Q1 upd_ne; [exact HM32s1 | nz]).
    assert (HQ1s2 : Q1 !!! Regidx Rs2 = pv)
      by (rewrite /Q1 upd_ne; [exact HM32s2 | nz]).
    assert (HQ1a0 : Q1 !!! Regidx Ra0 = ientry k)
      by (rewrite /Q1 upd_ne; [rewrite HM32a0 Hie; reflexivity | nz]).
    assert (HQ1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              Q1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite /Q1 upd_ne; [| congruence]. exact (HM32thr r Hr Nsp Ns0 Ns1 Ns2). }
    assert (Hpp036 : add_vec_int (mword_of_int (KXA + 0x34) : mword 64) 2
                     = mword_of_int (KXA + 0x36)) by pcw.
    iEval (rewrite Hpp036) in "Hpc".
    (* ---- +0x036: jal ra,ilock ---- *)
    assert (Htil : add_vec (mword_of_int (KXA + 0x36) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091624 : mword 21))
                   = mword_of_int KernelSyms.ilock) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x36)) Rra
              (mword_of_int 2091624 : mword 21) Q1 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htil; vm_compute; reflexivity)
              with "Hcg Hpc Hi036").
    iIntros (CID3 Hsq3) "Hcg Hpc". iEval (rewrite Htil) in "Hpc".
    set (Q2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x36) : mword 64) 4)]> Q1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x36) : mword 64) 4)]> Q1) with Q2.
    assert (HQ2ra : Q2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x36) : mword 64) 4)
      by (rewrite /Q2; apply upd_eq).
    assert (HQ2a0 : Q2 !!! Regidx Ra0 = ientry k)
      by (rewrite /Q2 upd_ne; [exact HQ1a0 | nz]).
    iDestruct (cpu_own_transport CID0 CID3 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Ilock.wp_ilock_sconf gs jp gl gu gd gk pd pav pu bn gfs gi cn
              gilk gislk cov logstart inodestart nib k (q/2)%Qp gy dev inum
              pidv (DfracOwn (1/4)) dqs Q2 (K - 68)%nat true true lks
              ltac:(lia) Hk Hlg Hins0 Hibc Hib' Hjp Hgs HQ2a0
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitinv Hesck Hireg Hslkk
                    Hshr Hins Hppid Hprocs Hdevi Hdgeom Hdlock Hbs1").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CIDil Hsil M1 dnl bml fl_) "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hins Hbs1
             Hslkd Hslpid Hdep Hidev Hiinum Hivalid Hload Hity %Hfr_".
    assert (Hpc3a : ret_pc (Q2 !!! Regidx Rra) = mword_of_int (KXA + 0x3a))
      by (rewrite HQ2ra; pcw).
    iEval (rewrite Hpc3a) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsil csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Q2 upd_ne; [exact HQ1sp | nz]. }
    assert (HM1s0 : M1 !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcsil Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /Q2 upd_ne; [exact HQ1s0 | nz]. }
    assert (HM1s1 : M1 !!! Regidx Rs1 = proc_addr jp).
    { rewrite (callee_saved_lookup Hcsil Rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Q2 upd_ne; [exact HQ1s1 | nz]. }
    assert (HM1s2 : M1 !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcsil Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /Q2 upd_ne; [exact HQ1s2 | nz]. }
    assert (HM1s4 : M1 !!! Regidx Rs4 = ientry k).
    { rewrite (callee_saved_lookup Hcsil Rs4 ltac:(vm_compute; reflexivity)).
      rewrite /Q2 upd_ne; [exact HQ1s4 | nz]. }
    assert (HM1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              M1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite (callee_saved_lookup Hcsil r Hr).
      rewrite /Q2 upd_ne; [| regne]. exact (HQ1thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    (* ---- peel the loaded content for readi ---- *)
    iDestruct "Hload" as (datl)
      "(%Hiok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdiat & Hmeta & Haddrs & Hindres
       & Hblocks)".
    destruct Hiok as (Hbmwf & Hbmcov & Hdaddr & Hdty & Hszb & Hholes & Hsized).
    iAssert (inode_map gfs (ientry k) bml) with "[Haddrs Hindres]" as "Hmap".
    { rewrite /inode_map. iSplitL "Haddrs"; [iExact "Haddrs" | iExact "Hindres"]. }
    (* ---- the elf buffer, as 64 NAMED bytes ---- *)
    iDestruct (kxc_elf_slots_of_stack sp0 with "Helf") as "Helf".
    iDestruct (kxc_slots_elf sp0 with "Helf") as "[%Hal Helfb]".
    iEval (rewrite /bytes_own) in "Helfb".
    iDestruct (bb_any_named (pa_stk sp0 54) 64 with "Helfb") as (fb) "Helfb".
    (* ---- +0x03a: li a4,64 ---- *)
    iApply (wp_li4_s_sconf (mword_of_int (KXA + 0x3a)) Ra4
              (mword_of_int 64 : mword 12)
              (mword_of_int (Z.of_nat 64) : mword 64) M1 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi03a").
    iIntros (CID4 Hsq4) "Hcg Hpc".
    set (Q3 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int (Z.of_nat 64) : mword 64)]> M1).
    assert (Hpp03e : add_vec_int (mword_of_int (KXA + 0x3a) : mword 64) 4
                     = mword_of_int (KXA + 0x3e)) by pcw.
    iEval (rewrite Hpp03e) in "Hpc".
    (* ---- +0x03e: c.li a3,0 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KXA + 0x3e)) Ra3
              (mword_of_int 0 : mword 6) (mword_of_int (Z.of_nat 0) : mword 64)
              Q3 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi03e").
    iIntros (CID5 Hsq5) "Hcg Hpc".
    set (Q4 := <[Regidx Ra3 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> Q3).
    assert (Hpp040 : add_vec_int (mword_of_int (KXA + 0x3e) : mword 64) 2
                     = mword_of_int (KXA + 0x40)) by pcw.
    iEval (rewrite Hpp040) in "Hpc".
    (* ---- +0x040: addi a2,s0,-432 -- a2 := &elf ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KXA + 0x40)) Ra2 Rs0
              (mword_of_int 3664 : mword 12) Q4 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi040").
    iIntros (CID6 Hsq6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q5 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (Q4 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3664 : mword 12)))]> Q4).
    assert (HQ4s0 : Q4 !!! Regidx Rs0 = sp0).
    { rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [exact HM1s0 | nz]. }
    assert (HQ5a2 : Q5 !!! Regidx Ra2 = pa_stk sp0 54).
    { rewrite /Q5 upd_eq HQ4s0. apply kxc_elf_base. }
    assert (Hpp044 : add_vec_int (mword_of_int (KXA + 0x40) : mword 64) 4
                     = mword_of_int (KXA + 0x44)) by pcw.
    iEval (rewrite Hpp044) in "Hpc".
    (* ---- +0x044: c.li a1,0 -- THE KERNEL ARM of readi ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KXA + 0x44)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              Q5 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi044").
    iIntros (CID7 Hsq7) "Hcg Hpc".
    set (Q6 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> Q5).
    assert (Hpp046 : add_vec_int (mword_of_int (KXA + 0x44) : mword 64) 2
                     = mword_of_int (KXA + 0x46)) by pcw.
    iEval (rewrite Hpp046) in "Hpc".
    (* ---- +0x046: c.mv a0,s4 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x46)) Ra0 Rs4
              Q6 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi046").
    iIntros (CID8 Hsq8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q7 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (Q6 !!! Regidx Rs4))]> Q6).
    assert (HQ6s4 : Q6 !!! Regidx Rs4 = ientry k).
    { rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [exact HM1s4 | nz]. }
    assert (Hpp048 : add_vec_int (mword_of_int (KXA + 0x46) : mword 64) 2
                     = mword_of_int (KXA + 0x48)) by pcw.
    iEval (rewrite Hpp048) in "Hpc".
    (* ---- +0x048: jal ra,readi ---- *)
    assert (Htrd : add_vec (mword_of_int (KXA + 0x48) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092520 : mword 21))
                   = mword_of_int KernelSyms.readi) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x48)) Rra
              (mword_of_int 2092520 : mword 21) Q7 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htrd; vm_compute; reflexivity)
              with "Hcg Hpc Hi048").
    iIntros (CID9 Hsq9) "Hcg Hpc". iEval (rewrite Htrd) in "Hpc".
    set (Q8 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x48) : mword 64) 4)]> Q7).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x48) : mword 64) 4)]> Q7) with Q8.
    assert (HQ8ra : Q8 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x48) : mword 64) 4)
      by (rewrite /Q8; apply upd_eq).
    assert (HQ8a0 : Q8 !!! Regidx Ra0 = ientry k).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_eq HQ6s4.
      apply add_vec_zero_l. }
    assert (HQ8a1 : Q8 !!! Regidx Ra1 = (mword_of_int 0 : mword 64)).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6; apply upd_eq. }
    assert (HQ8a2 : Q8 !!! Regidx Ra2 = pa_stk sp0 54).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6 upd_ne; [exact HQ5a2 | nz]. }
    assert (HQ8a3 : Q8 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat 0) : mword 64)).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4; apply upd_eq. }
    assert (HQ8a4 : Q8 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat 64) : mword 64)).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3; apply upd_eq. }
    (* readi takes its two uints in the ABI's sign-extended form; the ELF
       header read is at off 0 for 64 bytes, where that is the identity *)
    assert (HQ8a3' : Q8 !!! Regidx Ra3
                     = sign_extend' 64 (mword_of_int (Z.of_nat 0) : mword 32))
      by (rewrite HQ8a3; apply rd_arg32_small; lia).
    assert (HQ8a4' : Q8 !!! Regidx Ra4
                     = sign_extend' 64 (mword_of_int (Z.of_nat 64) : mword 32))
      by (rewrite HQ8a4; apply rd_arg32_small; lia).
    assert (HQ8sp : Q8 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [exact HM1sp | nz]. }
    assert (HQ8s0 : Q8 !!! Regidx Rs0 = sp0).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [exact HQ4s0 | nz]. }
    assert (HQ8s1 : Q8 !!! Regidx Rs1 = proc_addr jp).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [exact HM1s1 | nz]. }
    assert (HQ8s2 : Q8 !!! Regidx Rs2 = pv).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [exact HM1s2 | nz]. }
    assert (HQ8s4 : Q8 !!! Regidx Rs4 = ientry k).
    { rewrite /Q8 upd_ne; [| nz]. rewrite /Q7 upd_ne; [| nz].
      exact HQ6s4. }
    assert (HQ8thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              Q8 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite /Q8 upd_ne; [| regne]. rewrite /Q7 upd_ne; [| regne].
      rewrite /Q6 upd_ne; [| regne]. rewrite /Q5 upd_ne; [| regne].
      rewrite /Q4 upd_ne; [| regne]. rewrite /Q3 upd_ne; [| regne].
      exact (HM1thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    iEval (rewrite -HQ8a2) in "Helfb".
    iDestruct (cpu_own_transport CIDil CID9 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Readi.wp_readi_sconf KT1 gs jp gl gu gd gk pd pav pu bn gfs ga gf
              cov logstart dev (ientry k) bml datl dnl false 0%nat 64%nat fb V
              pidv (DfracOwn (1/4)) (DfracOwn (1/2)) Q8 (K - 68)%nat true true lks
              ltac:(lia) Hlg Hbmwf Hbmcov Hszb
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity) Hjp Hgs HQ8a0
              ltac:(rewrite HQ8a1; vm_compute; reflexivity) HQ8a3' HQ8a4'
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hka Hidev Hmeta Hmap Hblocks
                    [Helfb Hppid] Hprocs Hdevi Hdgeom Hdlock Hbs1").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    { iSplitL "Helfb"; [iExact "Helfb" | iExact "Hppid"]. }
    iIntros (CIDrd Hsrd M2 tot P') "%Hcsrd %Hupt %Htotb %Hret Hcg Hcnt _ _ Hpc
             Hidev Hmeta Hmap Hblocks [Helfb Hppid] Hbs1".
    assert (Hpc4c : ret_pc (Q8 !!! Regidx Rra) = mword_of_int (KXA + 0x4c))
      by (rewrite HQ8ra; pcw).
    iEval (rewrite Hpc4c) in "Hpc".
    iEval (rewrite HQ8a2) in "Helfb".
    set (gb := rd_delivered datl fb 0 tot).
    (* the register facts after readi *)
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsrd csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQ8sp. }
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcsrd Rs0 ltac:(vm_compute; reflexivity)).
      exact HQ8s0. }
    assert (HM2s1 : M2 !!! Regidx Rs1 = proc_addr jp).
    { rewrite (callee_saved_lookup Hcsrd Rs1 ltac:(vm_compute; reflexivity)).
      exact HQ8s1. }
    assert (HM2s2 : M2 !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcsrd Rs2 ltac:(vm_compute; reflexivity)).
      exact HQ8s2. }
    assert (HM2s4 : M2 !!! Regidx Rs4 = ientry k).
    { rewrite (callee_saved_lookup Hcsrd Rs4 ltac:(vm_compute; reflexivity)).
      exact HQ8s4. }
    assert (HM2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              M2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite (callee_saved_lookup Hcsrd r Hr).
      exact (HQ8thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    (* ---- +0x04c: li a5,64 ---- *)
    iApply (wp_li4_s_sconf (mword_of_int (KXA + 0x4c)) Ra5
              (mword_of_int 64 : mword 12)
              (mword_of_int (Z.of_nat 64) : mword 64) M2 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi04c").
    iIntros (CID10 Hsq10) "Hcg Hpc".
    set (Q9 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (Z.of_nat 64) : mword 64)]> M2).
    assert (HQ9sp : Q9 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /Q9 upd_ne; [exact HM2sp | nz]).
    assert (HQ9s0 : Q9 !!! Regidx Rs0 = sp0)
      by (rewrite /Q9 upd_ne; [exact HM2s0 | nz]).
    assert (HQ9s1 : Q9 !!! Regidx Rs1 = proc_addr jp)
      by (rewrite /Q9 upd_ne; [exact HM2s1 | nz]).
    assert (HQ9s2 : Q9 !!! Regidx Rs2 = pv)
      by (rewrite /Q9 upd_ne; [exact HM2s2 | nz]).
    assert (HQ9s4 : Q9 !!! Regidx Rs4 = ientry k)
      by (rewrite /Q9 upd_ne; [exact HM2s4 | nz]).
    assert (HQ9thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              Q9 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      rewrite /Q9 upd_ne; [| regne]. exact (HM2thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    assert (Hpp050 : add_vec_int (mword_of_int (KXA + 0x4c) : mword 64) 4
                     = mword_of_int (KXA + 0x50)) by pcw.
    iEval (rewrite Hpp050) in "Hpc".
    (* ---- the budget both exits need: the seam carries it outright now,
       rather than as an interval this block has to do arithmetic on ---- *)
    assert (Hiu : (iput_units <= n1)%nat) by exact Hn1.
    (* ---- +0x050: bne a0,a5 -- a BLIND split ---- *)
    destruct (eq_vec (rget Q9 Ra0) (rget Q9 Ra5)) eqn:Ecmp.
    - (* the read was the full 64 bytes: fall through *)
      iApply (wp_bne_fall_s_sconf (mword_of_int (KXA + 0x50))
                (mword_of_int 20 : mword 13) Ra5 Ra0 Q9 (K - 68)%nat true
                ltac:(nz) ltac:(nz)
                ltac:(unfold neq_vec; rewrite Ecmp; reflexivity)
                with "Hcg Hpc Hi050").
      iIntros (CID11 Hsq11) "Hcg Hpc".
      assert (Hpp054 : add_vec_int (mword_of_int (KXA + 0x50) : mword 64) 4
                       = mword_of_int (KXA + 0x54)) by pcw.
      iEval (rewrite Hpp054) in "Hpc".
      (* ---- +0x054: lw a4,-432(s0) -- elf.magic ---- *)
      iDestruct (kxc_named_split4 (pa_stk sp0 54) gb 64 ltac:(lia) with "Helfb")
        as "[Helf4 Helfr]".
      assert (Hal4 : is_aligned_paddr (Physaddr (pa_stk sp0 54)) 4 = true).
      { apply aligned8_aligned4.
        pose proof (Hal 0%nat ltac:(lia)) as Ha0'. cbn in Ha0'. exact Ha0'. }
      iDestruct (kxc_word4_of_named (pa_stk sp0 54) gb Hal4 with "Helf4") as "Hw4".
      assert (Hpa54 : add_vec (rget Q9 Rs0)
                        (sign_extend' 64 (mword_of_int 3664 : mword 12))
                      = pa_stk sp0 54).
      { rewrite (rget_ne Q9 Rs0 ltac:(nz)) HQ9s0. apply kxc_elf_base. }
      iEval (rewrite -Hpa54) in "Hw4".
      iApply (wp_lw_s_sconf (mword_of_int (KXA + 0x54)) Ra4 Rs0
                (mword_of_int 3664 : mword 12) Q9 (K - 68)%nat
                (Z_to_bv 32 (le_at gb 0 4) : mword 32) true (dqm := DfracOwn 1)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi054 Hw4").
      iIntros (CID12 Hsq12) "Hcg Hpc Hw4". iEval (rewrite Hpa54) in "Hw4".
      set (Q10 := <[Regidx Ra4 := regval_into_reg
                     (sign_extend' 64
                        (Z_to_bv 32 (le_at gb 0 4) : mword 32))]> Q9).
      assert (Hpp058 : add_vec_int (mword_of_int (KXA + 0x54) : mword 64) 4
                       = mword_of_int (KXA + 0x58)) by pcw.
      iEval (rewrite Hpp058) in "Hpc".
      (* ---- +0x058: lui a5,0x464c4 ---- *)
      iApply (wp_lui_s_sconf (mword_of_int (KXA + 0x58)) Ra5
                (mword_of_int 287940 : mword 20)
                (luival (mword_of_int 287940 : mword 20)) Q10 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) eq_refl with "Hcg Hpc Hi058").
      iIntros (CID13 Hsq13) "Hcg Hpc".
      set (Q11 := <[Regidx Ra5 := regval_into_reg
                     (luival (mword_of_int 287940 : mword 20))]> Q10).
      assert (Hpp05c : add_vec_int (mword_of_int (KXA + 0x58) : mword 64) 4
                       = mword_of_int (KXA + 0x5c)) by pcw.
      iEval (rewrite Hpp05c) in "Hpc".
      (* ---- +0x05c: addi a5,a5,1407 -- a5 := ELF_MAGIC ---- *)
      iApply (wp_addi4_s_sconf (mword_of_int (KXA + 0x5c)) Ra5 Ra5
                (mword_of_int 1407 : mword 12) Q11 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi05c").
      iIntros (CID14 Hsq14) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (Q12 := <[Regidx Ra5 := regval_into_reg
                     (add_vec (Q11 !!! Regidx Ra5)
                        (sign_extend' 64 (mword_of_int 1407 : mword 12)))]> Q11).
      assert (Hpp060 : add_vec_int (mword_of_int (KXA + 0x5c) : mword 64) 4
                       = mword_of_int (KXA + 0x60)) by pcw.
      iEval (rewrite Hpp060) in "Hpc".
      assert (HQ12sp : Q12 !!! Regidx csp_rs1 = pa_stk sp0 68).
      { rewrite /Q12 upd_ne; [| nz]. rewrite /Q11 upd_ne; [| nz].
        rewrite /Q10 upd_ne; [exact HQ9sp | nz]. }
      assert (HQ12s0 : Q12 !!! Regidx Rs0 = sp0).
      { rewrite /Q12 upd_ne; [| nz]. rewrite /Q11 upd_ne; [| nz].
        rewrite /Q10 upd_ne; [exact HQ9s0 | nz]. }
      assert (HQ12s1 : Q12 !!! Regidx Rs1 = proc_addr jp).
      { rewrite /Q12 upd_ne; [| nz]. rewrite /Q11 upd_ne; [| nz].
        rewrite /Q10 upd_ne; [exact HQ9s1 | nz]. }
      assert (HQ12s2 : Q12 !!! Regidx Rs2 = pv).
      { rewrite /Q12 upd_ne; [| nz]. rewrite /Q11 upd_ne; [| nz].
        rewrite /Q10 upd_ne; [exact HQ9s2 | nz]. }
      assert (HQ12s4 : Q12 !!! Regidx Rs4 = ientry k).
      { rewrite /Q12 upd_ne; [| nz]. rewrite /Q11 upd_ne; [| nz].
        rewrite /Q10 upd_ne; [exact HQ9s4 | nz]. }
      assert (HQ12thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
                Q12 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
        rewrite /Q12 upd_ne; [| regne]. rewrite /Q11 upd_ne; [| regne].
        rewrite /Q10 upd_ne; [| regne]. exact (HQ9thr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
      (* ---- give the magic word back and re-form the elf buffer ---- *)
      iDestruct (kxc_named_of_word4 (pa_stk sp0 54) gb with "Hw4") as "Helf4".
      iAssert ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ[KT1] gb j)%I
        with "[Helf4 Helfr]" as "Helfb".
      { iApply (kxc_named_join4 (pa_stk sp0 54) gb 64 ltac:(lia)
                  with "Helf4 Helfr"). }
      iAssert (stack_own (KTR := KT1) (pa_stk sp0 46) 8) with "[Helfb]" as "Helf".
      { iApply kxc_stack_of_elf_slots. iApply (kxc_bytes_elf sp0 Hal).
        rewrite /bytes_own. iApply (bb_named_any with "Helfb"). }
      (* ---- +0x060: beq a4,a5 -- the second BLIND split ---- *)
      destruct (eq_vec (rget Q12 Ra4) (rget Q12 Ra5)) eqn:Emag.
      + (* the magic matched: on to PHASE B at +0x090 *)
        assert (Htgt90 : add_vec (mword_of_int (KXA + 0x60) : mword 64)
                  (sign_extend' 64 (mword_of_int 48 : mword 13))
                = mword_of_int (KXA + 0x90)) by pcw.
        iApply (wp_beq_taken_s_sconf (mword_of_int (KXA + 0x60))
                  (mword_of_int 48 : mword 13) Ra5 Ra4 Q12 (K - 68)%nat true
                  ltac:(nz) ltac:(nz) Emag
                  ltac:(rewrite Htgt90; vm_compute; reflexivity)
                  with "Hcg Hpc Hi060").
        iIntros (CID15 Hsq15). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgt90) in "Hpc".
        iDestruct ("Hpvbk" $! (pv_cwd V) with "Hcwd Hcref Hppid") as "Hpriv".
        rewrite kxc_upd_cwd_id.
        iDestruct (cpu_own_transport CIDrd CID15 0%nat true (proc_addr jp) true
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iAssert (ic_loaded gfs gi cov logstart k inum dnl bml)
          with "[Hdiat Hmeta Hmap Hblocks Hdlk]" as "Hload".
        { rewrite /ic_loaded /inode_map. iExists datl.
          iSplitR; [iPureIntro; split_and!;
            [exact Hbmwf | exact Hbmcov | exact Hdaddr | exact Hdty
            | exact Hszb | exact Hholes | exact Hsized] |].
          iSplitR; [iPureIntro; exact Hdok |].
          iSplitR; [iPureIntro; exact Hddix |].
          iSplitR; [iPureIntro; exact Hdoc |].
          iSplitR; [iPureIntro; exact Hduq |].
          iSplitL "Hdlk"; [iExact "Hdlk" |].
          iDestruct "Hmap" as "[Haddrs Hindres]".
          iSplitL "Hdiat"; [iExact "Hdiat" |].
          iSplitL "Hmeta"; [iExact "Hmeta" |].
          iSplitL "Haddrs"; [iExact "Haddrs" |].
          iSplitL "Hindres"; [iExact "Hindres" | iExact "Hblocks"]. }
        iDestruct (T.kxa_bs3_join bn with "Hbs1 Hbs2") as "Hbs".
        iSpecialize ("Hcont90" $! CID15 with "[%]"); [wp_next_chain |].
        (* [b] is gone by here -- [kxc_sie_b_agree] pinned it and the proof
           [subst]ed it, so the retarget names the literal. *)
        iDestruct (wp_next_retarget CID0 CID15 true (proc_addr jp) _
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply ("Hcont90" $! Q12 k (q/2)%Qp (q/2)%Qp inum dnl bml gilk gislk gy
                  n1 used1 with "[%] [%] Hpc Hcg Hcnt Hslkk Hslkd Hslpid Hdep
                  Hidev Hiinum Hivalid Hload Hity Hkeep Hlog Hirs Hbm Hins Hbits
                  Hbs Hka Hpriv Hpath Hargv Hargs [-Hcont] Hcont").
        * split_and!; [exact HQ12sp | exact HQ12s0 | exact HQ12s1 | exact HQ12s2
                      | exact HQ12s4 | exact Hk | exact Hib' | exact HQ12thr].
        * split; [exact Hiu | exact Hused1].
        * rewrite /kxc_frameA6.
          iDestruct (kxc_mid_join sp0 with "Hust Helf Hph") as "Hmid".
          iSplitL "Hf1"; [iExact "Hf1" |].
          iSplitL "Hf2"; [iExact "Hf2" |].
          iSplitL "Hf3"; [iExact "Hf3" |].
          iSplitL "Hf4"; [iExact "Hf4" |].
          iSplitL "Hf5"; [iExact "Hf5" |].
          iSplitL "Hf6"; [iExact "Hf6" |].
          iSplitL "Hf7"; [iExact "Hf7" |].
          iSplitL "Hf8"; [iExact "Hf8" |].
          iSplitL "Hf9"; [iExact "Hf9" |].
          iSplitL "Hf10"; [iExact "Hf10" |].
          iSplitL "Hf11"; [iExact "Hf11" |].
          iSplitL "Hf12"; [iExact "Hf12" |].
          iSplitL "Hf13"; [iExact "Hf13" |].
          iSplitL "Hmid"; [iExact "Hmid" |].
          iSplitL "Hf64"; [iExact "Hf64" |].
          iSplitL "Hf65"; [iExact "Hf65" |].
          iSplitL "Hf66"; [iExact "Hf66" |].
          iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"].
      + (* bad magic: the +0x064 tail *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (KXA + 0x60))
                  (mword_of_int 48 : mword 13) Ra5 Ra4 Q12 (K - 68)%nat true
                  ltac:(nz) ltac:(nz) Emag with "Hcg Hpc Hi060").
        iIntros (CID15 Hsq15) "Hcg Hpc".
        assert (Hpp064 : add_vec_int (mword_of_int (KXA + 0x60) : mword 64) 4
                         = mword_of_int (KXA + 0x64)) by pcw.
        iEval (rewrite Hpp064) in "Hpc".
        iDestruct ("Hpvbk" $! (pv_cwd V) with "Hcwd Hcref Hppid") as "Hpriv".
        rewrite kxc_upd_cwd_id.
        iDestruct (cpu_own_transport CIDrd CID15 0%nat true (proc_addr jp) true
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iAssert (ic_loaded gfs gi cov logstart k inum dnl bml)
          with "[Hdiat Hmeta Hmap Hblocks Hdlk]" as "Hload".
        { rewrite /ic_loaded /inode_map. iExists datl.
          iSplitR; [iPureIntro; split_and!;
            [exact Hbmwf | exact Hbmcov | exact Hdaddr | exact Hdty
            | exact Hszb | exact Hholes | exact Hsized] |].
          iSplitR; [iPureIntro; exact Hdok |].
          iSplitR; [iPureIntro; exact Hddix |].
          iSplitR; [iPureIntro; exact Hdoc |].
          iSplitR; [iPureIntro; exact Hduq |].
          iSplitL "Hdlk"; [iExact "Hdlk" |].
          iDestruct "Hmap" as "[Haddrs Hindres]".
          iSplitL "Hdiat"; [iExact "Hdiat" |].
          iSplitL "Hmeta"; [iExact "Hmeta" |].
          iSplitL "Haddrs"; [iExact "Haddrs" |].
          iSplitL "Hindres"; [iExact "Hindres" | iExact "Hblocks"]. }
        iDestruct (T.kxa_bs3_join bn with "Hbs1 Hbs2") as "Hbs".
        (* [T.kxc_bad64] is applied AT [CID15] (its [sie_cap_gpr] premise pins
           its own [CID0] from "Hcg"), so kexec's exit -- which we still hold
           anchored at the section's [CID0] -- has to be re-anchored there.
           The crossing fact goes by NAME: as an inline [ltac:] in argument
           position its expected type is still an evar (durable-notes). *)
        assert (Hcr15 : true = false \/ proc_addr jp = zero_reg ->
                        (CID15 : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_retarget CID0 CID15 true (proc_addr jp) _ Hcr15
                     with "Hcont") as "Hcont".
        iApply (T.kxc_bad64 gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
                  gilk gislk ga gf cov logstart bmapstart inodestart nib size
                  dev used used1 k (q/2)%Qp (q/2)%Qp gy inum dnl bml n1
                  plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                  m Q12 K lks sp0 ra0 s00 s10 s20 pv av
                  HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hibc Hibl Hib' Hcovb Hiu
                  Hjp Hgs Hused1 Hsp Hra Hs0 Hs1 Hs2 HQ12sp HQ12s4 HQ12thr
                  with "Hcg Hcnt Htext Hpc [] Hslkk Hslkd Hslpid Hdep
                        Hidev Hiinum Hivalid Hload Hity Hkeep Hbm Hins Hbits Hka
                        Hpriv Hpath Hargv Hargs Hbs Hirs Hlog [-Hcont] Hcont").
        { iApply (T.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv Hesc
                                       Hslks Hireg Hprocs Hdevi Hdgeom Hdlock"). }
        rewrite /kxc_frameA6.
        iDestruct (kxc_mid_join sp0 with "Hust Helf Hph") as "Hmid".
        iSplitL "Hf1"; [iExact "Hf1" |].
        iSplitL "Hf2"; [iExact "Hf2" |].
        iSplitL "Hf3"; [iExact "Hf3" |].
        iSplitL "Hf4"; [iExact "Hf4" |].
        iSplitL "Hf5"; [iExact "Hf5" |].
        iSplitL "Hf6"; [iExact "Hf6" |].
        iSplitL "Hf7"; [iExact "Hf7" |].
        iSplitL "Hf8"; [iExact "Hf8" |].
        iSplitL "Hf9"; [iExact "Hf9" |].
        iSplitL "Hf10"; [iExact "Hf10" |].
        iSplitL "Hf11"; [iExact "Hf11" |].
        iSplitL "Hf12"; [iExact "Hf12" |].
        iSplitL "Hf13"; [iExact "Hf13" |].
        iSplitL "Hmid"; [iExact "Hmid" |].
        iSplitL "Hf64"; [iExact "Hf64" |].
        iSplitL "Hf65"; [iExact "Hf65" |].
        iSplitL "Hf66"; [iExact "Hf66" |].
        iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"].
    - (* short read: the +0x064 tail *)
      assert (Htgt64 : add_vec (mword_of_int (KXA + 0x50) : mword 64)
                (sign_extend' 64 (mword_of_int 20 : mword 13))
              = mword_of_int (KXA + 0x64)) by pcw.
      iApply (wp_bne_taken_s_sconf (mword_of_int (KXA + 0x50))
                (mword_of_int 20 : mword 13) Ra5 Ra0 Q9 (K - 68)%nat true
                ltac:(nz) ltac:(nz)
                ltac:(unfold neq_vec; rewrite Ecmp; reflexivity)
                ltac:(rewrite Htgt64; vm_compute; reflexivity)
                with "Hcg Hpc Hi050").
      iIntros (CID11 Hsq11). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt64) in "Hpc".
      iDestruct ("Hpvbk" $! (pv_cwd V) with "Hcwd Hcref Hppid") as "Hpriv".
      rewrite kxc_upd_cwd_id.
      iDestruct (cpu_own_transport CIDrd CID11 0%nat true (proc_addr jp) true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iAssert (ic_loaded gfs gi cov logstart k inum dnl bml)
        with "[Hdiat Hmeta Hmap Hblocks Hdlk]" as "Hload".
      { rewrite /ic_loaded /inode_map. iExists datl.
        iSplitR; [iPureIntro; split_and!;
          [exact Hbmwf | exact Hbmcov | exact Hdaddr | exact Hdty
          | exact Hszb | exact Hholes | exact Hsized] |].
        iSplitR; [iPureIntro; exact Hdok |].
        iSplitR; [iPureIntro; exact Hddix |].
        iSplitR; [iPureIntro; exact Hdoc |].
        iSplitR; [iPureIntro; exact Hduq |].
        iSplitL "Hdlk"; [iExact "Hdlk" |].
        iDestruct "Hmap" as "[Haddrs Hindres]".
        iSplitL "Hdiat"; [iExact "Hdiat" |].
        iSplitL "Hmeta"; [iExact "Hmeta" |].
        iSplitL "Haddrs"; [iExact "Haddrs" |].
        iSplitL "Hindres"; [iExact "Hindres" | iExact "Hblocks"]. }
      iDestruct (T.kxa_bs3_join bn with "Hbs1 Hbs2") as "Hbs".
      iAssert (stack_own (KTR := KT1) (pa_stk sp0 46) 8) with "[Helfb]" as "Helf".
      { iApply kxc_stack_of_elf_slots. iApply (kxc_bytes_elf sp0 Hal).
        rewrite /bytes_own. iApply (bb_named_any with "Helfb"). }
      (* same re-anchoring as the bad-magic tail: [T.kxc_bad64] runs at [CID11] *)
      assert (Hcr11 : true = false \/ proc_addr jp = zero_reg ->
                      (CID11 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID11 true (proc_addr jp) _ Hcr11
                   with "Hcont") as "Hcont".
      iApply (T.kxc_bad64 gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
                gilk gislk ga gf cov logstart bmapstart inodestart nib size
                dev used used1 k (q/2)%Qp (q/2)%Qp gy inum dnl bml n1
                plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                m Q9 K lks sp0 ra0 s00 s10 s20 pv av
                HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hibc Hibl Hib' Hcovb Hiu
                Hjp Hgs Hused1 Hsp Hra Hs0 Hs1 Hs2 HQ9sp HQ9s4 HQ9thr
                with "Hcg Hcnt Htext Hpc [] Hslkk Hslkd Hslpid Hdep
                      Hidev Hiinum Hivalid Hload Hity Hkeep Hbm Hins Hbits Hka
                      Hpriv Hpath Hargv Hargs Hbs Hirs Hlog [-Hcont] Hcont").
      { iApply (T.fs_fabric_mk with "Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv Hesc
                                     Hslks Hireg Hprocs Hdevi Hdgeom Hdlock"). }
      rewrite /kxc_frameA6.
      iDestruct (kxc_mid_join sp0 with "Hust Helf Hph") as "Hmid".
      iSplitL "Hf1"; [iExact "Hf1" |].
      iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |].
      iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [iExact "Hf5" |].
      iSplitL "Hf6"; [iExact "Hf6" |].
      iSplitL "Hf7"; [iExact "Hf7" |].
      iSplitL "Hf8"; [iExact "Hf8" |].
      iSplitL "Hf9"; [iExact "Hf9" |].
      iSplitL "Hf10"; [iExact "Hf10" |].
      iSplitL "Hf11"; [iExact "Hf11" |].
      iSplitL "Hf12"; [iExact "Hf12" |].
      iSplitL "Hf13"; [iExact "Hf13" |].
      iSplitL "Hmid"; [iExact "Hmid" |].
      iSplitL "Hf64"; [iExact "Hf64" |].
      iSplitL "Hf65"; [iExact "Hf65" |].
      iSplitL "Hf66"; [iExact "Hf66" |].
      iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"].
  Qed.

End KexecABody.

(* ===================================================================== *)
(*  PHASE A's CAPSTONE, IN A FRESH SECTION -- for [ProofKforkMain]'s      *)
(*  reason exactly: the chain applies [kxc_a2] AT THE SEAM'S HART, and a  *)
(*  still-open section's [Context CID0] is one fixed shared variable, not *)
(*  a per-use argument, so the override is rejected with a Wrong-argument- *)
(*  name-CID0 error -- and without it [kxc_a2]'s [kxc_at_a2] premise      *)
(*  sits at the ENTRY hart while the seam delivers it at the rebound one, *)
(*  which prints as the same term twice (durable-notes).                  *)
(* ===================================================================== *)
Section KexecAMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  PHASE A, WHOLE: +0x000 .. +0x08e, with BOTH [-1] tails inside.     *)
  (*                                                                      *)
  (*  [kxc_a1]'s fall-through seam is literally [kxc_a2]'s precondition,   *)
  (*  so the chain is one [iApply] per half and no seam bookkeeping        *)
  (*  survives into the statement: what comes out is kexec's entry state   *)
  (*  in, phase B's entry at +0x090 out, and ONE exit -- which is the      *)
  (*  point, since both halves own a [-1] tail and the exit is linear.     *)
  (*                                                                      *)
  (*  THE ONLY STEP THAT IS NOT A COPY OF [kxc_a1]'s PREMISE LIST is the   *)
  (*  hart: the seam rebinds it, [kxc_a1] therefore hands the exit back    *)
  (*  already anchored there, and phase B's entry -- which the caller      *)
  (*  gives us at the section's [CID0] -- is retargeted with the seam      *)
  (*  binder's own crossing fact ([WpNext.wp_next_retarget]).              *)
  (* =================================================================== *)
  Lemma kxc_phaseA
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    (K_kexec <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    (* the inode region's two ambient ties, threaded to namei (fs-log.md
       §G.25) *)
    g = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    eb = true ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Ra0 = pv ->
    m !!! Regidx Ra1 = av ->
    sie_cap_gpr KT1 m K b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    kernel_text -∗ pc_is (mword_of_int KXA : mword 64) -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kalloc_env ga None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
    bslots bn 3 -∗
    iref_slots 2 -∗
    (* ---- kexec's OWN continuation: BOTH [-1] tails close through it ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) b lks -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    (* ---- and the FALL-THROUGH: phase B's entry at +0x090 ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M90 : regfile) (kf : nat) (qf sf : Qp) (inumf : mword 32)
        (dnf : dinode) (bmf : blkmap) (gilf gislf gyf : gname)
        (n2 : nat) (used2 : gset Z),
        ⌜ M90 !!! Regidx csp_rs1 = pa_stk sp0 68 /\
          M90 !!! Regidx Rs0 = sp0 /\
          M90 !!! Regidx Rs1 = proc_addr jp /\
          M90 !!! Regidx Rs2 = pv /\
          M90 !!! Regidx Rs4 = ientry kf /\
          (kf < NINODE)%nat /\
          bv_unsigned inumf < 16 * Z.of_nat nib /\
          (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
             r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
             M90 !!! Regidx r = m !!! Regidx r) ⌝ -∗
        ⌜ (iput_units <= n2)%nat /\ used2 ⊆ used ⌝ -∗
        pc_is (mword_of_int (KXA + 0x90) : mword 64) -∗
        sie_cap_gpr KT1 M90 (K - 68)%nat b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        is_sleeplock_gen gilf gislf (i_lock (ientry kf)) "inode"%string
                     (ic_tok cn kf) (slh_tok (icfg_isl kf)) -∗
        sleeplocked_q gislf sf -∗
        sl_pid (i_lock (ientry kf)) ↦₄ pidv -∗
        ic_deposit cn kf (DepShr sf dev inumf gyf) -∗
        i_dev (ientry kf) ↦₄{DfracOwn (1/2)} dev -∗
        i_inum (ientry kf) ↦₄{DfracOwn (1/2)} inumf -∗
        i_valid (ientry kf) ↦₄ valid_word true -∗
        ic_loaded gfs gi cov logstart kf inumf dnf bmf -∗
        (* SpecIlock v5's additive type witness, at the generation the
           share names -- what SpecIunlockput now needs at +0x064. *)
        ity_shot gyf (di_type dnf) -∗
        inode_ref_short kf (qf + sf)%Qp qf dev inumf -∗
        log_op g n2 -∗
        iref_slots 1 -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used2 -∗
        bslots bn 3 -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        kxc_frameA6 sp0 ra0 s00 s10 s20 pv av (m !!! Regidx Rs4) -∗
        (* THE EXIT, HANDED BACK.  Phase A's two [-1] tails own one copy of
           the caller's exit and a [wp_next] continuation is LINEAR, so
           without this phase B would have none.  durable-notes' "CHAINING
           TWO HALVES" -- the shape [kxc_a1] already uses internally, now on
           phase A's own interface, because [ProofKexec.v] composes across it. *)
        wp_next (CID0 := CID) b (proc_addr jp) (fun (CIDy : CpuId) =>
          ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
            (entry spv szv' : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
              sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
              cpu_own 0 eb (proc_addr jp) b lks -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              ⌜used' ⊆ used⌝ -∗
              bitmap_res gfs bmapstart cov logstart size used' -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
              ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
              ([∗ list] i ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
              bslots bn 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hcstr Hplen Hjp Hgs Heb Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    iIntros "Hcg Hcnt #Htext Hpc #Hfab #Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hcont Hcont90".
    iApply (kxc_a1 (CID0 := CID0) gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl ga gf
              cov logstart bmapstart inodestart nib size dev used
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa
              m K eb b lks sp0 ra0 s00 s10 s20 pv av
              HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
              Hiregb Hcstr Hplen Hjp Hgs Heb Hsp Hra Hs0 Hs1 Hs2
              Ha0 Ha1
              with "Hcg Hcnt Htext Hpc Hfab Hka Hbm Hins Hbits Hpriv
                    Hpath Hargv Hargs Hbs Hirs Hcont [Hcont90]").
    (* ---- the seam at +0x032: [kxc_a2] takes it verbatim ---- *)
    iIntros (CIDs Hss M32 used1 ipv n1) "Hseam Hexit".
    iDestruct (wp_next_retarget CID0 CIDs b (proc_addr jp) _ Hss
                 with "Hcont90") as "Hcont90".
    iApply (kxc_a2 (CID0 := CIDs) gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl ga gf
              cov logstart bmapstart inodestart nib size dev used used1
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa
              m M32 K eb b lks sp0 ra0 s00 s10 s20 pv av ipv n1
              HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
              Hiregb Hjp Hgs Heb Hsp Hra Hs0 Hs1 Hs2
              with "Htext Hfab Hseam Hexit Hcont90").
  Qed.

End KexecAMain.
End KexecAProof.
