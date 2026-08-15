(* ProofVirtioDiskRw.v -- virtio_disk_rw(b, write) over the sconf world.

   virtio_disk_rw @ 0x800057b0 is the driver's request path: it allocates a
   three-descriptor chain under [disk.vdisk_lock] (sleeping until three are
   free), formats the chain, publishes it by bumping [avail->idx], kicks the
   device, sleeps until [virtio_disk_intr] sets [b->disk = 0], collects the
   payoff, frees the chain and releases the lock.

   The proof is a sequence of Qed-SEALED PHASE lemmas, each stating the next
   one's precondition as its postcondition.  The seams are spelled as named
   [Definition]s (below) rather than inline, so a phase can be re-proved --
   or written -- without disturbing its neighbours:

     P1  prologue (12-slot frame, ten callee saves) + [b->blockno] load +
         the sector doubling + [acquire(&disk.vdisk_lock)]      +0x000..+0x036
     P2  the alloc3 machinery: the eight-way free-cell scan, the middle
         three-iteration loop, the outer sleep-retry iLöb       +0x036..+0x0c4
     P3  descriptor / header / status / info.b formatting       +0x0c4..+0x176
     P4  ring write, fence, and THE PUBLISH                     +0x176..+0x19a
     P5  QUEUE_NOTIFY + the completion-wait iLöb                +0x19a..+0x1d2
     P6  payoff withdrawal, free_chain, release, epilogue       +0x1d2..+0x232

   P1/P2.1/P2.2 live here; P2.3 in the B file, P3 in C, P4 in D, P5 in E,
   P6 in F.
   The whole function is composed and sealed in ProofVirtioDiskRwF.v
   ([Module VirtioDiskRwProof … : VIRTIODISKRW]) and instantiated in
   LinkVirtioDiskRw.v.  Everything here is Qed-closed.

   A functor over ACQUIRE / RELEASE / SLEEP / FREEDESC. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import CpuOwn FdSlots.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpUart.
Require Import VirtioModel DiskPtsto DiskInv.
Require Import PanicStub.
Require Import SpecAcquire SpecRelease SpecSleep SpecFreeDesc.
Require Import CodeVirtioDiskRw.
Require Import SpecVirtioDiskRw.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal; away
   from tp the two are the same lookup and every index here is a literal. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).
Require Import VirtioDiskRwDefs.

Module VirtioDiskRwPhases (Acquire : ACQUIRE) (Release : RELEASE)
                          (Sleep : SLEEP) (FreeDesc : FREEDESC).

Section ProofVirtioDiskRw.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Notation Rra := (mword_of_int 1  : mword 5).
  Notation Rtp := (mword_of_int 4  : mword 5).
  Notation Rs0 := (mword_of_int 8  : mword 5).
  Notation Rs1 := (mword_of_int 9  : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).

  (* the register-index disequality discharge of optimization.md: [unify]
     settles convertible-or-not cheaply, so [discriminate] only ever runs on
     a genuine miss and a HIT fails FAST instead of hunting a discriminating
     position in two equal [mword] records. *)
  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* the same, for a SYMBOLIC callee-saved register (an [is_cs_idx r = true]
     must be in context) *)
  (* [congruence] LAST: ahead of the named lemma it builds a congruence
     closure over the whole whole-function context on every peel layer
     (optimization.md / CalleeSaved.reg_ne_side). *)
  Local Ltac regne :=
    first [ apply vdrw_cs_ne; [ assumption | vm_compute; reflexivity ]
          | congruence ].

  (* =================================================================== *)
  (* P1: +0x000 .. +0x036                                                *)
  (*                                                                     *)
  (*   c.addi16sp sp,-96 ; ten c.sdsp saves ; c.addi4spn s0,sp,96        *)
  (*   c.mv s3,a0 ; c.mv s6,a1                                           *)
  (*   lw s7,12(a0) ; slliw s7,s7,1 ; c.slli s7,32 ; srli s7,32          *)
  (*   auipc/addi a0,&disk.vdisk_lock ; jal acquire                      *)
  (*                                                                     *)
  (* Lands at +0x036 holding the lock and its resource, with the frame    *)
  (* laid out and the register discipline established.                    *)
  (* =================================================================== *)
  Lemma wp_vdrw_p1
      (γd : disk_names) (γk : gname) (pd pav pu : mword 64)
      (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
      (bno : mword 32) (lks : gset string) :
    let sp0 : Arch.pa := m !!! Regidx csp_rs1 in
    let bp  : Arch.pa := m !!! Regidx Ra0 in
    let wr  : mword 64 := m !!! Regidx Ra1 in
    (K_virtio_disk_rw <= K)%nat ->
    (* acquire's order premise: every lock this hart already holds ranks
       below "virtio_disk"'s -- see the postcondition below for why this
       phase's OWN [lks] is not enough, it must also reach P6's release. *)
    locks_below lks "virtio_disk" ->
    sie_cap_gpr m K eb pj -∗
    cpu_own 0 eb pj eb lks -∗
    (* NOT USED HERE: [wp_vdrw_p1] is pure prologue-plus-acquire, so the
       complement just RIDES ALONG, transported to the acquire-return hart
       exactly like [cpu_own] below, and handed to the continuation
       untouched -- the interior sleep it is for lives two phases down. *)
    trap_csrs_ext eb -∗
    cpu_claim_ext eb pj -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x000) : mword 64) -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    b_blockno bp ↦₄{DfracOwn (1/2)} bno -∗
    wp_next (CID0 := CID) true pj (fun (CID : CpuId) =>
      ∀ M : regfile,
        ⌜vdrw_regs M sp0 bp wr (vdrw_sector_raw bno) /\ vdrw_hi M m⌝ -∗
        sie_cap_gpr M (trap_res eb + (K - 12))%nat false pj -∗
        (* RESOLVED (was UNSURE): wp_vdrw_p1 acquires "virtio_disk" (rank 9,
           LockRank.v) via Acquire.wp_acquire_sconf and does not release it
           before this postcondition ("Lands at +0x036 holding the lock",
           above) -- SpecAcquire.v now confirms the held-lock set here is
           [{["virtio_disk"]} ∪ lks], NOT [lks] unchanged.  This is
           a LOCK-RETURNING phase, not a balanced one.  NOTE FOR THE NEXT
           READER: P2..P6 (ProofVirtioDiskRwB/C/D/E/F.v, none in this sweep's
           file list) continue this phase chain and almost certainly still
           thread the OLD bare [lks] through their own "holding the lock"
           cpu_own occurrences -- they need the matching fix, unverified here. *)
        cpu_own 1 eb pj false ({["virtio_disk"]} ∪ lks) -∗
        arm_pay 0 eb pj -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb pj -∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x036) : mword 64) -∗
        locked γk cpu_id -∗
        disk_res γd pd pav pu -∗
        vdrw_saved sp0 m -∗
        vdrw_scratch sp0 -∗
        b_blockno bp ↦₄{DfracOwn (1/2)} bno -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 bp wr HK Hfresh.
    iIntros "Hcg Hown Hextc Hextm #Htext Hpc #Hlk Hbno Hcont".
    (* ---- the instruction facts ---- *)
    (* ---- +0x000  c.addi16sp sp,-96 : push the 12-slot frame ---- *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 12).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (rwi_000 with "Htext") as "Hi000".
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x000) : mword 64)
              (mword_of_int 58 : mword 6) m K 12 eb ltac:(pose proof (vdrw_K12 K HK); lia) Hpush
              with "Hcg Hpc Hi000").
    iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc". rgall.
    iClear "Hi000".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /R1 upd_eq; exact Hpush).
    (* peel the twelve slots *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & _)".
    iDestruct "S1"  as (u1)  "Hk1".  iDestruct "S2"  as (u2)  "Hk2".
    iDestruct "S3"  as (u3)  "Hk3".  iDestruct "S4"  as (u4)  "Hk4".
    iDestruct "S5"  as (u5)  "Hk5".  iDestruct "S6"  as (u6)  "Hk6".
    iDestruct "S7"  as (u7)  "Hk7".  iDestruct "S8"  as (u8)  "Hk8".
    iDestruct "S9"  as (u9)  "Hk9".  iDestruct "S10" as (u10) "Hk10".
    iDestruct "S11" as (u11) "Hk11". iDestruct "S12" as (u12) "Hk12".
    (* each [c.sdsp] offset, as the matching [pa_stk] slot: slot k sits at
       new-sp + 8*(12-k). *)
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb9 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb10 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 10).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb11 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 11).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb12 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 12).
    { rewrite HspR1. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hb1)  in "Hk1".  iEval (rewrite -Hb2)  in "Hk2".
    iEval (rewrite -Hb3)  in "Hk3".  iEval (rewrite -Hb4)  in "Hk4".
    iEval (rewrite -Hb5)  in "Hk5".  iEval (rewrite -Hb6)  in "Hk6".
    iEval (rewrite -Hb7)  in "Hk7".  iEval (rewrite -Hb8)  in "Hk8".
    iEval (rewrite -Hb9)  in "Hk9".  iEval (rewrite -Hb10) in "Hk10".
    assert (Hp002 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x000) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x002)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp002) in "Hpc".
    iPoseProof (rwi_002 with "Htext") as "Hi002".
    (* ---- the ten saves ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x002) : mword 64)
              (mword_of_int 11 : mword 6) Rra R1 (K - 12)%nat u1 eb
              with "Hcg Hpc Hi002 Hk1").
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hk1". rgall.
    iClear "Hi002".
    assert (Hp004 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x002) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x004)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp004) in "Hpc".
    iPoseProof (rwi_004 with "Htext") as "Hi004".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x004) : mword 64)
              (mword_of_int 10 : mword 6) Rs0 R1 (K - 12)%nat u2 eb
              with "Hcg Hpc Hi004 Hk2").
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hk2". rgall.
    iClear "Hi004".
    assert (Hp006 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x004) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x006)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp006) in "Hpc".
    iPoseProof (rwi_006 with "Htext") as "Hi006".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x006) : mword 64)
              (mword_of_int 9 : mword 6) Rs1 R1 (K - 12)%nat u3 eb
              with "Hcg Hpc Hi006 Hk3").
    iIntros (CIDp4 Hsp4) "Hcg Hpc Hk3". rgall.
    iClear "Hi006".
    assert (Hp008 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x006) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x008)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp008) in "Hpc".
    iPoseProof (rwi_008 with "Htext") as "Hi008".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x008) : mword 64)
              (mword_of_int 8 : mword 6) Rs2 R1 (K - 12)%nat u4 eb
              with "Hcg Hpc Hi008 Hk4").
    iIntros (CIDp5 Hsp5) "Hcg Hpc Hk4". rgall.
    iClear "Hi008".
    assert (Hp00a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x008) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x00a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp00a) in "Hpc".
    iPoseProof (rwi_00a with "Htext") as "Hi00a".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x00a) : mword 64)
              (mword_of_int 7 : mword 6) Rs3 R1 (K - 12)%nat u5 eb
              with "Hcg Hpc Hi00a Hk5").
    iIntros (CIDp6 Hsp6) "Hcg Hpc Hk5". rgall.
    iClear "Hi00a".
    assert (Hp00c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x00a) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x00c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp00c) in "Hpc".
    iPoseProof (rwi_00c with "Htext") as "Hi00c".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x00c) : mword 64)
              (mword_of_int 6 : mword 6) Rs4 R1 (K - 12)%nat u6 eb
              with "Hcg Hpc Hi00c Hk6").
    iIntros (CIDp7 Hsp7) "Hcg Hpc Hk6". rgall.
    iClear "Hi00c".
    assert (Hp00e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x00c) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x00e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp00e) in "Hpc".
    iPoseProof (rwi_00e with "Htext") as "Hi00e".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x00e) : mword 64)
              (mword_of_int 5 : mword 6) Rs5 R1 (K - 12)%nat u7 eb
              with "Hcg Hpc Hi00e Hk7").
    iIntros (CIDp8 Hsp8) "Hcg Hpc Hk7". rgall.
    iClear "Hi00e".
    assert (Hp010 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x00e) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x010)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp010) in "Hpc".
    iPoseProof (rwi_010 with "Htext") as "Hi010".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x010) : mword 64)
              (mword_of_int 4 : mword 6) Rs6 R1 (K - 12)%nat u8 eb
              with "Hcg Hpc Hi010 Hk8").
    iIntros (CIDp9 Hsp9) "Hcg Hpc Hk8". rgall.
    iClear "Hi010".
    assert (Hp012 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x010) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x012)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp012) in "Hpc".
    iPoseProof (rwi_012 with "Htext") as "Hi012".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x012) : mword 64)
              (mword_of_int 3 : mword 6) Rs7 R1 (K - 12)%nat u9 eb
              with "Hcg Hpc Hi012 Hk9").
    iIntros (CIDp10 Hsp10) "Hcg Hpc Hk9". rgall.
    iClear "Hi012".
    assert (Hp014 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x012) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x014)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp014) in "Hpc".
    iPoseProof (rwi_014 with "Htext") as "Hi014".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x014) : mword 64)
              (mword_of_int 2 : mword 6) Rs8 R1 (K - 12)%nat u10 eb
              with "Hcg Hpc Hi014 Hk10").
    iIntros (CIDp11 Hsp11) "Hcg Hpc Hk10". rgall.
    iClear "Hi014".
    assert (Hp016 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x014) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x016)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp016) in "Hpc".
    iPoseProof (rwi_016 with "Htext") as "Hi016".
    (* ---- +0x016  c.addi4spn s0,sp,96 : the frame pointer ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x016) : mword 64)
              (Cregidx (mword_of_int 0)) (mword_of_int 24 : mword 8) Rs0 R1 (K - 12)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi016").
    iIntros (CIDp12 Hsp12) "Hcg Hpc". rgall.
    iClear "Hi016".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1) with R2.
    assert (Hspn : sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                   = (mword_of_int 96 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HR2s0 : R2 !!! Regidx Rs0 = (sp0 : mword 64)).
    { rewrite /R2 upd_eq HspR1 Hspn.
      unfold regval_into_reg, pa_stk, add_vec_int.
      rewrite vdrw_av2. apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hp018 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x016) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x018)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp018) in "Hpc".
    iPoseProof (rwi_018 with "Htext") as "Hi018".
    (* ---- +0x018  c.mv s3,a0 ; +0x01a  c.mv s6,a1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x018) : mword 64) Rs3 Ra0
              R2 (K - 12)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi018").
    iIntros (CIDp13 Hsp13) "Hcg Hpc". rgall.
    iClear "Hi018".
    set (R3 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2) with R3.
    assert (HR2a0 : R2 !!! Regidx Ra0 = (bp : mword 64)).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. reflexivity. }
    assert (HR3s3 : R3 !!! Regidx Rs3 = (bp : mword 64))
      by (rewrite /R3 upd_eq HR2a0; apply add_vec_zero_l).
    assert (Hp01a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x018) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x01a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp01a) in "Hpc".
    iPoseProof (rwi_01a with "Htext") as "Hi01a".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x01a) : mword 64) Rs6 Ra1
              R3 (K - 12)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi01a").
    iIntros (CIDp14 Hsp14) "Hcg Hpc". rgall.
    iClear "Hi01a".
    set (R4 := <[Regidx Rs6 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    change (<[Regidx Rs6 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3) with R4.
    assert (HR3a1 : R3 !!! Regidx Ra1 = wr).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [| reg_neq]. reflexivity. }
    assert (HR4s6 : R4 !!! Regidx Rs6 = wr)
      by (rewrite /R4 upd_eq HR3a1; apply add_vec_zero_l).
    assert (Hp01c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x01a) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x01c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp01c) in "Hpc".
    (* ---- +0x01c  lw s7,12(a0) : bp->blockno ---- *)
    assert (HR4a0 : R4 !!! Regidx Ra0 = (bp : mword 64)).
    { rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq]. exact HR2a0. }
    assert (Hbnoa : add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 12 : mword 12))
                    = (b_blockno bp : mword 64)).
    { rewrite HR4a0 vdrw_sext_12. unfold b_blockno. reflexivity. }
    iPoseProof (rwi_01c with "Htext") as "Hi01c".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x01c) : mword 64) Rs7 Ra0
              (mword_of_int 12 : mword 12) R4 (K - 12)%nat bno eb (dqm := DfracOwn (1/2))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi01c [Hbno]").
    { rgall. iEval (rewrite Hbnoa). iExact "Hbno". }
    iIntros (CIDp15 Hsp15) "Hcg Hpc Hbno". rgall.
    iClear "Hi01c".
    iEval (rewrite Hbnoa) in "Hbno".
    set (R5 := <[Regidx Rs7 := regval_into_reg (sign_extend' 64 bno)]> R4).
    change (<[Regidx Rs7 := regval_into_reg (sign_extend' 64 bno)]> R4) with R5.
    assert (HR5s7 : R5 !!! Regidx Rs7 = sign_extend' 64 bno) by (rewrite /R5; apply upd_eq).
    assert (Hp020 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x01c) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x020)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp020) in "Hpc".
    iPoseProof (rwi_020 with "Htext") as "Hi020".
    (* ---- +0x020  slliw s7,s7,1 ---- *)
    iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x020) : mword 64) Rs7 Rs7
              (mword_of_int 1 : mword 5)
              (sign_extend' 64 (shift_bits_left
                 (subrange_vec_dec (R5 !!! Regidx Rs7) 31 0 : mword 32)
                 (mword_of_int 1 : mword 5)))
              R5 (K - 12)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(reflexivity)
              with "Hcg Hpc Hi020").
    iIntros (CIDp16 Hsp16) "Hcg Hpc". rgall.
    iClear "Hi020".
    set (R6 := <[Regidx Rs7 := regval_into_reg
                  (sign_extend' 64 (shift_bits_left
                     (subrange_vec_dec (R5 !!! Regidx Rs7) 31 0 : mword 32)
                     (mword_of_int 1 : mword 5)))]> R5).
    change (<[Regidx Rs7 := regval_into_reg
                  (sign_extend' 64 (shift_bits_left
                     (subrange_vec_dec (R5 !!! Regidx Rs7) 31 0 : mword 32)
                     (mword_of_int 1 : mword 5)))]> R5) with R6.
    assert (Hp024 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x020) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x024)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp024) in "Hpc".
    iPoseProof (rwi_024 with "Htext") as "Hi024".
    (* ---- +0x024  c.slli s7,s7,0x20 ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x024) : mword 64) (Regidx Rs7) Rs7
              vdrw_sh32 R6 (K - 12)%nat eb
              ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi024").
    iIntros (CIDp17 Hsp17) "Hcg Hpc". rgall.
    iClear "Hi024".
    set (R7 := <[Regidx Rs7 := regval_into_reg
                  (shift_bits_left (R6 !!! Regidx Rs7)
                     (subrange_vec_dec vdrw_sh32 (Z.sub log2_xlen 1) 0))]> R6).
    change (<[Regidx Rs7 := regval_into_reg
                  (shift_bits_left (R6 !!! Regidx Rs7)
                     (subrange_vec_dec vdrw_sh32 (Z.sub log2_xlen 1) 0))]> R6) with R7.
    assert (Hp026 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x024) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x026)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp026) in "Hpc".
    iPoseProof (rwi_026 with "Htext") as "Hi026".
    (* ---- +0x026  srli s7,s7,0x20 ---- *)
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x026) : mword 64) Rs7 Rs7
              vdrw_sh32 R7 (K - 12)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi026").
    iIntros (CIDp18 Hsp18) "Hcg Hpc". rgall.
    iClear "Hi026".
    set (R8 := <[Regidx Rs7 := regval_into_reg
                  (shift_bits_right (R7 !!! Regidx Rs7)
                     (subrange_vec_dec vdrw_sh32 (Z.sub log2_xlen 1) 0))]> R7).
    change (<[Regidx Rs7 := regval_into_reg
                  (shift_bits_right (R7 !!! Regidx Rs7)
                     (subrange_vec_dec vdrw_sh32 (Z.sub log2_xlen 1) 0))]> R7) with R8.
    assert (HR8s7 : R8 !!! Regidx Rs7 = vdrw_sector_raw bno).
    { rewrite /R8 upd_eq /R7 upd_eq /R6 upd_eq HR5s7. reflexivity. }
    assert (Hp02a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x026) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x02a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02a) in "Hpc".
    iPoseProof (rwi_02a with "Htext") as "Hi02a".
    (* ---- +0x02a/+0x02e  a0 := &disk.vdisk_lock ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x02a) : mword 64) Ra0
              (mword_of_int 30 : mword 20) R8 (K - 12)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi02a").
    iIntros (CIDp19 Hsp19) "Hcg Hpc". rgall.
    iClear "Hi02a".
    set (R9 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x02a) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> R8).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x02a) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> R8) with R9.
    assert (Hp02e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x02a) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x02e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02e) in "Hpc".
    iPoseProof (rwi_02e with "Htext") as "Hi02e".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x02e) : mword 64) Ra0 Ra0
              (mword_of_int 3382 : mword 12) R9 (K - 12)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi02e").
    iIntros (CIDp20 Hsp20) "Hcg Hpc". rgall.
    iClear "Hi02e".
    set (R10 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R9 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 3382 : mword 12)))]> R9).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (R9 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 3382 : mword 12)))]> R9) with R10.
    assert (HR10a0 : R10 !!! Regidx Ra0 = (d_lock : mword 64)).
    { rewrite /R10 upd_eq /R9 upd_eq.
      unfold d_lock, disk_base, pa_add, add_vec_int.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp032 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x02e) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x032)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp032) in "Hpc".
    iPoseProof (rwi_032 with "Htext") as "Hi032".
    (* ---- +0x032  jal acquire ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x032) : mword 64) Rra
              (mword_of_int 2077496 : mword 21) R10 (K - 12)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi032").
    iIntros (CIDp21 Hsp21) "Hcg Hpc". rgall.
    iClear "Hi032".
    set (R11 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x032) : mword 64) 4)]> R10).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x032) : mword 64) 4)]> R10) with R11.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x032) : mword 64)
                      (sign_extend' 64 (mword_of_int 2077496 : mword 21))
                    = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    (* register facts entering acquire *)
    assert (HR11a0 : R11 !!! Regidx Ra0 = (d_lock : mword 64)).
    { rewrite /R11 upd_ne; [| reg_neq]. exact HR10a0. }
    assert (HR11ra : R11 !!! Regidx Rra
                     = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x032) : mword 64) 4)
      by (rewrite /R11; apply upd_eq).
    iDestruct (cpu_own_transport CID CIDp21 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf γk "virtio_disk"%string
              (disk_res γd pd pav pu) R11 0%nat eb pj (K - 12)%nat eb lks
              vdrw_noff0 ltac:(pose proof (vdrw_K10 K HK); lia) Hfresh
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { rgall. iEval (rewrite HR11a0). iExact "Hlk". }
    iIntros (CIDaq Hsaq ms M) "_ Hcg Hpc %HcsM Htok HR Hown Hpay".
    (* THE COMPLEMENT RIDES ALONG, UNTOUCHED, THROUGH THE WHOLE PROLOGUE --
       transport it to the acquire-return hart in ONE step, using exactly the
       chain of per-instruction guards [cpu_own_transport] above already
       drew on (plus acquire's own [Hsaq]).  Nothing here needs to look at
       it: the interior sleep it is for lives two phases down, and it is
       handed to the continuation exactly as it arrived. *)
    iDestruct (trap_csrs_ext_transport CID CIDaq eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDaq eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    assert (Hret : ret_pc (R11 !!! Regidx Rra) = mword_of_int (KernelSyms.virtio_disk_rw + 0x036))
      by (rewrite HR11ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hret) in "Hpc".
    (* ---- hand the phase over ---- *)
    (* the register discipline, read off R11 and transported through acquire *)
    assert (HR11 : vdrw_regs R11 sp0 bp wr (vdrw_sector_raw bno)).
    { unfold vdrw_regs. split_and!.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
        rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
        exact HspR1.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
        rewrite /R3 upd_ne; [| reg_neq]. exact HR2s0.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
        exact HR3s3.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
        rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
        rewrite /R5 upd_ne; [| reg_neq]. exact HR4s6.
      - rewrite /R11 upd_ne; [| reg_neq]. rewrite /R10 upd_ne; [| reg_neq].
        rewrite /R9 upd_ne; [| reg_neq]. exact HR8s7. }
    (* NB: [callee_saved m M] is NOT available here and must not be claimed --
       rw's prologue CLOBBERS s0..s8 and only the epilogue (P6) restores them
       out of [vdrw_saved].  What travels is the frame, not the registers. *)
    assert (HR11hi : vdrw_hi R11 m).
    { vdrw_hi_peel. apply vdrw_hi_refl. }
    iSpecialize ("Hcont" $! CIDaq with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! M with "[%] Hcg Hown Hpay Hextc Hextm Hpc Htok HR [Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10] [Hk11 Hk12] Hbno").
    - split.
      + exact (vdrw_regs_cs R11 M sp0 bp wr (vdrw_sector_raw bno) HcsM HR11).
      + exact (vdrw_hi_cs R11 M m HcsM HR11hi).
    - rewrite /vdrw_saved.
      (* the ten cells come back at the RAW sp-relative address the leaf
         computes; fold each into its [pa_stk] slot *)
      iEval (rewrite Hb1) in "Hk1".
      iEval (rewrite Hb2) in "Hk2".
      iEval (rewrite Hb3) in "Hk3".
      iEval (rewrite Hb4) in "Hk4".
      iEval (rewrite Hb5) in "Hk5".
      iEval (rewrite Hb6) in "Hk6".
      iEval (rewrite Hb7) in "Hk7".
      iEval (rewrite Hb8) in "Hk8".
      iEval (rewrite Hb9) in "Hk9".
      iEval (rewrite Hb10) in "Hk10".
      (* each save stored the ENTRY value of its register: [R1] differs from
         [m] only at sp, which none of the ten saves names *)
      assert (E1 : R1 !!! Regidx Rra = m !!! Regidx Rra)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E2 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E3 : R1 !!! Regidx Rs1 = m !!! Regidx Rs1)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E4 : R1 !!! Regidx Rs2 = m !!! Regidx Rs2)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E5 : R1 !!! Regidx Rs3 = m !!! Regidx Rs3)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E6 : R1 !!! Regidx Rs4 = m !!! Regidx Rs4)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E7 : R1 !!! Regidx Rs5 = m !!! Regidx Rs5)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E8 : R1 !!! Regidx Rs6 = m !!! Regidx Rs6)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E9 : R1 !!! Regidx Rs7 = m !!! Regidx Rs7)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      assert (E10 : R1 !!! Regidx Rs8 = m !!! Regidx Rs8)
        by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
      iEval (rewrite E1) in "Hk1".
      iEval (rewrite E2) in "Hk2".
      iEval (rewrite E3) in "Hk3".
      iEval (rewrite E4) in "Hk4".
      iEval (rewrite E5) in "Hk5".
      iEval (rewrite E6) in "Hk6".
      iEval (rewrite E7) in "Hk7".
      iEval (rewrite E8) in "Hk8".
      iEval (rewrite E9) in "Hk9".
      iEval (rewrite E10) in "Hk10".
      iFrame "Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10".
    - rewrite /vdrw_scratch. iExists u11, u12. iFrame "Hk11 Hk12".
  Qed.


  (* =================================================================== *)
  (* P2.1: the inner eight-way scan, +0x068 .. +0x072.                    *)
  (*                                                                     *)
  (*     0x068  lbu   a3,24(a4)      -- disk.free[a5]                     *)
  (*     0x06c  c.bnez a3,-0x26      -- set?  -> +0x046 (FOUND)           *)
  (*     0x06e  c.addiw a5,a5,1                                          *)
  (*     0x070  c.addi  a4,a4,1                                          *)
  (*     0x072  bne   a5,s1,-0x0a    -- a5 <> 8 -> back to +0x068         *)
  (*            (falls through to +0x076: NOT FOUND)                      *)
  (*                                                                     *)
  (* Proved by induction on the number of cells still to look at, so the   *)
  (* five-instruction body is threaded ONCE rather than eight times.  The  *)
  (* scan only READS: the cells come back untouched (the found one is      *)
  (* cleared later, at +0x04a, by the caller).                            *)
  (*                                                                     *)
  (* ONE continuation, taking the outcome as a DISJUNCTION: the two exits  *)
  (* would otherwise be two separate wands, and a loop lemma cannot hand   *)
  (* the same cells to both (they are alternatives, not a partition).      *)
  (* =================================================================== *)
  Definition vdrw_scan_out (fr : nat -> bool) (k : nat) (M' : regfile) : iProp Σ :=
    ((∃ j : nat,
        ⌜(k <= j < 8)%nat /\ fr j = true
         /\ (forall i, (k <= i < j)%nat -> fr i = false)
         /\ M' !!! Regidx Ra5 = (mword_of_int (Z.of_nat j) : mword 64)⌝ ∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x046) : mword 64))
     ∨ (⌜forall i, (k <= i < 8)%nat -> fr i = false⌝ ∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x076) : mword 64)))%I.

  Lemma wp_vdrw_scan (pme : Arch.pa)
      (pd : Arch.pa) (fr : nat -> bool) (av : nat) :
    forall (n k : nat) (M : regfile),
    (k + S n = 8)%nat ->
    M !!! Regidx Ra5 = (mword_of_int (Z.of_nat k) : mword 64) ->
    M !!! Regidx Ra4 = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat k)) ->
    M !!! Regidx Rs1 = (mword_of_int 8 : mword 64) ->
    sie_cap_gpr M av false pme -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x068) : mword 64) -∗
    ([∗ list] i ∈ seq k (S n), free_cell_res pd fr i) -∗
    ( ∀ M' : regfile,
        ⌜forall r : mword 5, r <> Ra3 -> r <> Ra4 -> r <> Ra5 ->
           M' !!! Regidx r = M !!! Regidx r⌝ -∗
        ([∗ list] i ∈ seq k (S n), free_cell_res pd fr i) -∗
        sie_cap_gpr M' av false pme -∗
        vdrw_scan_out fr k M' -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    induction n as [|n IH]; intros k M Hkn Ha5 Ha4 Hs1;
      iIntros "Hcg #Htext Hpc Hcells Hcont".
    all: assert (Hk8 : (k < 8)%nat) by (clear -Hkn; lia).
    all: iPoseProof (rwi_068 with "Htext") as "Hi068".
    all: iPoseProof (rwi_06c with "Htext") as "Hi06c".
    all: iPoseProof (rwi_06e with "Htext") as "Hi06e".
    all: iPoseProof (rwi_070 with "Htext") as "Hi070".
    all: iPoseProof (rwi_072 with "Htext") as "Hi072".
    all: iEval (cbn [seq]) in "Hcells".
    all: iDestruct "Hcells" as "[Hc Hrest]".
    all: rewrite /free_cell_res.
    all: iDestruct "Hc" as "[Hcell Hbun]".
    all: assert (Hlbu : add_vec (M !!! Regidx Ra4)
                          (sign_extend' 64 (mword_of_int 24 : mword 12))
                        = (d_free_cell k : mword 64))
           by (rewrite Ha4; apply vdrw_free_addr).
    all: iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x068) : mword 64) Ra3 Ra4
                   (mword_of_int 24 : mword 12) M av
                   (if fr k then Z_to_bv 8 1 else byte_zero) false
                   ltac:(vm_compute; discriminate) ltac:(rdok)
                   with "Hcg Hpc Hi068 [Hcell]").
    1,3: iEval (rewrite Hlbu); iExact "Hcell".
    all: iApply wp_next_off_intro.
    all: iIntros "Hcg Hpc Hcell". all: rgall.
    all: iEval (rewrite Hlbu) in "Hcell".
    all: set (N1 := <[Regidx Ra3 := regval_into_reg
                     (zero_extend' 64 ((if fr k then Z_to_bv 8 1 else byte_zero) : mword 8))]> M).
    all: change (<[Regidx Ra3 := regval_into_reg
                     (zero_extend' 64 ((if fr k then Z_to_bv 8 1 else byte_zero) : mword 8))]> M)
           with N1.
    all: assert (HN1a3 : N1 !!! Regidx Ra3
                   = zero_extend' 64 ((if fr k then Z_to_bv 8 1 else byte_zero) : mword 8))
           by (rewrite /N1; apply upd_eq).
    all: assert (HN1a5 : N1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat k) : mword 64))
           by (rewrite /N1 upd_ne; [exact Ha5 | reg_neq]).
    all: assert (HN1ag : forall r : mword 5, r <> Ra3 -> r <> Ra4 -> r <> Ra5 ->
                   N1 !!! Regidx r = M !!! Regidx r)
           by (intros r Hr3 Hr4 Hr5; rewrite /N1 upd_ne; [reflexivity | congruence]).
    all: assert (Hp06c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x068) : mword 64) 4
                         = mword_of_int (KernelSyms.virtio_disk_rw + 0x06c))
           by (apply bv_eq; vm_compute; reflexivity).
    all: iEval (rewrite Hp06c) in "Hpc".
    all: destruct (fr k) eqn:Hfrk.
    (* ---------- FOUND at k (both induction cases are identical) ---------- *)
    1,3: iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x06c) : mword 64)
                   (mword_of_int 237 : mword 8) (Cregidx (mword_of_int 5)) Ra3 N1 av false
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                   ltac:(rgall; rewrite HN1a3; exact vdrw_bnez_set)
                   ltac:(vm_compute; reflexivity)
                   with "Hcg Hpc Hi06c [Hcell Hbun Hrest Hcont]");
         [ iNext; rewrite wp_next_off; iIntros "Hcg Hpc"; rgall;
           assert (Hbk : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x06c) : mword 64)
                           (sign_extend' 64 (sign_extend' 13
                              (concat_vec (mword_of_int 237 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.virtio_disk_rw + 0x046))
             by (apply bv_eq; vm_compute; reflexivity);
           iEval (rewrite Hbk) in "Hpc";
           iApply ("Hcont" $! N1 with "[%] [Hcell Hbun Hrest] Hcg [Hpc]");
           [ exact HN1ag
           | iEval (cbn [seq]);
             iSplitL "Hcell Hbun";
               [ rewrite /free_cell_res Hfrk; iFrame "Hcell Hbun" | iExact "Hrest" ]
           | rewrite /vdrw_scan_out; iLeft; iExists k; iFrame "Hpc"; iPureIntro;
             split_and!;
               [ clear -Hk8; lia | clear -Hk8; lia | exact Hfrk
               | intros i Hi; exfalso; clear -Hi; lia
               | rewrite HN1a5; reflexivity ] ] ].
    (* ---------- clear at k: advance ---------- *)
    all: iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x06c) : mword 64)
                   (mword_of_int 237 : mword 8) (Cregidx (mword_of_int 5)) Ra3 N1 av false
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                   ltac:(rgall; rewrite HN1a3; exact vdrw_bnez_clear)
                   with "Hcg Hpc Hi06c").
    all: iApply wp_next_off_intro.
    all: iIntros "Hcg Hpc". all: rgall.
    all: assert (Hp06e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x06c) : mword 64) 2
                         = mword_of_int (KernelSyms.virtio_disk_rw + 0x06e))
           by (apply bv_eq; vm_compute; reflexivity).
    all: iEval (rewrite Hp06e) in "Hpc".
    all: iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x06e) : mword 64) Ra5
                   (mword_of_int 1 : mword 6) N1 av false
                   ltac:(vm_compute; discriminate) ltac:(rdok)
                   with "Hcg Hpc Hi06e").
    all: iApply wp_next_off_intro.
    all: iIntros "Hcg Hpc". all: rgall.
    all: set (N2 := <[Regidx Ra5 := regval_into_reg
                     (sign_extend' 64 (subrange_vec_dec
                        (add_vec (N1 !!! Regidx Ra5)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> N1).
    all: change (<[Regidx Ra5 := regval_into_reg
                     (sign_extend' 64 (subrange_vec_dec
                        (add_vec (N1 !!! Regidx Ra5)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> N1)
           with N2.
    all: assert (HN2a5 : N2 !!! Regidx Ra5 = (mword_of_int (Z.of_nat (S k)) : mword 64))
           by (rewrite /N2 upd_eq HN1a5; exact (vdrw_addiw_succ k Hk8)).
    all: assert (Hp070 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x06e) : mword 64) 2
                         = mword_of_int (KernelSyms.virtio_disk_rw + 0x070))
           by (apply bv_eq; vm_compute; reflexivity).
    all: iEval (rewrite Hp070) in "Hpc".
    all: iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x070) : mword 64) Ra4
                   (mword_of_int 1 : mword 6) N2 av false
                   ltac:(vm_compute; discriminate) ltac:(rdok)
                   with "Hcg Hpc Hi070").
    all: iApply wp_next_off_intro.
    all: iIntros "Hcg Hpc". all: rgall.
    all: set (N3 := <[Regidx Ra4 := regval_into_reg
                     (add_vec (N2 !!! Regidx Ra4)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N2).
    all: change (<[Regidx Ra4 := regval_into_reg
                     (add_vec (N2 !!! Regidx Ra4)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N2)
           with N3.
    all: assert (HN2a4 : N2 !!! Regidx Ra4
                   = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat k)))
           by (rewrite /N2 upd_ne; [| reg_neq]; rewrite /N1 upd_ne; [| reg_neq]; exact Ha4).
    all: assert (HN3a4 : N3 !!! Regidx Ra4
                   = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat (S k))))
           by (rewrite /N3 upd_eq HN2a4; exact (vdrw_addr_succ k)).
    all: assert (HN3a5 : N3 !!! Regidx Ra5 = (mword_of_int (Z.of_nat (S k)) : mword 64))
           by (rewrite /N3 upd_ne; [exact HN2a5 | reg_neq]).
    all: assert (HN3s1 : N3 !!! Regidx Rs1 = (mword_of_int 8 : mword 64)).
    1,3: rewrite /N3 upd_ne; [| reg_neq]; rewrite /N2 upd_ne; [| reg_neq];
         rewrite /N1 upd_ne; [| reg_neq]; exact Hs1.
    all: assert (HN3ag : forall r : mword 5, r <> Ra3 -> r <> Ra4 -> r <> Ra5 ->
                   N3 !!! Regidx r = M !!! Regidx r).
    1,3: intros r Hr3 Hr4 Hr5;
         rewrite /N3 upd_ne; [| congruence]; rewrite /N2 upd_ne; [| congruence];
         rewrite /N1 upd_ne; [reflexivity | congruence].
    all: assert (Hp072 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x070) : mword 64) 2
                         = mword_of_int (KernelSyms.virtio_disk_rw + 0x072))
           by (apply bv_eq; vm_compute; reflexivity).
    all: iEval (rewrite Hp072) in "Hpc".
    (* ---------- base case: k + 2 = 8, the [bne] falls through ---------- *)
    - assert (Hk7 : k = 7%nat) by (clear -Hkn; lia).
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x072) : mword 64)
                (mword_of_int 8182 : mword 13) Rs1 Ra5 N3 av false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgall; rewrite HN3a5 HN3s1 Hk7; exact vdrw_neq8_eq)
                with "Hcg Hpc Hi072").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hp076 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x072) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x076))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp076) in "Hpc".
      iApply ("Hcont" $! N3 with "[%] [Hcell Hbun Hrest] Hcg [Hpc]").
      { exact HN3ag. }
      { iEval (cbn [seq]).
        iSplitL "Hcell Hbun";
          [ rewrite /free_cell_res Hfrk; iFrame "Hcell Hbun" | iExact "Hrest" ]. }
      { rewrite /vdrw_scan_out. iRight. iFrame "Hpc". iPureIntro.
        intros i Hi. assert (i = k) by (clear -Hi Hk7; lia). subst i. exact Hfrk. }
    (* ---------- step case: retry at k+1 ---------- *)
    - assert (HSk8 : (S k < 8)%nat) by (clear -Hkn; lia).
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x072) : mword 64)
                (mword_of_int 8182 : mword 13) Rs1 Ra5 N3 av false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgall; rewrite HN3a5 HN3s1; exact (vdrw_neq8_lt (S k) HSk8))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi072 [Hcell Hbun Hrest Hcont]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hbk2 : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x072) : mword 64)
                       (sign_extend' 64 (mword_of_int 8182 : mword 13))
                     = mword_of_int (KernelSyms.virtio_disk_rw + 0x068))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk2) in "Hpc".
      iApply (IH (S k) N3 ltac:(clear -Hkn; lia) HN3a5 HN3a4 HN3s1
                with "Hcg Htext Hpc Hrest [Hcell Hbun Hcont]").
      iIntros (M'') "%Hag Hrest Hcg Hor".
      iApply ("Hcont" $! M'' with "[%] [Hcell Hbun Hrest] Hcg [Hor]").
      { intros r Hr3 Hr4 Hr5. rewrite (Hag r Hr3 Hr4 Hr5). exact (HN3ag r Hr3 Hr4 Hr5). }
      { iEval (cbn [seq]).
        iSplitL "Hcell Hbun";
          [ rewrite /free_cell_res Hfrk; iFrame "Hcell Hbun" | iExact "Hrest" ]. }
      { rewrite /vdrw_scan_out. iDestruct "Hor" as "[Hf|Hn]".
        - iDestruct "Hf" as (j) "[%Hj Hpc]". iLeft. iExists j. iFrame "Hpc".
          iPureIntro. destruct Hj as (Hj1 & Hj2 & Hj3 & Hj4).
          split_and!; [ clear -Hj1; lia | clear -Hj1; lia | exact Hj2 | | exact Hj4 ].
          intros i Hi. destruct (decide (i = k)) as [->|Hne];
            [ exact Hfrk | apply Hj3; clear -Hi Hne; lia ].
        - iDestruct "Hn" as "[%Hall Hpc]". iRight. iFrame "Hpc". iPureIntro.
          intros i Hi. destruct (decide (i = k)) as [->|Hne];
            [ exact Hfrk | apply Hall; clear -Hi Hne; lia ]. }
  Qed.


  (* =================================================================== *)
  (* P2.2a: ONE iteration of the middle three-times loop, +0x05c..+0x056. *)
  (*                                                                     *)
  (*     0x05c  c.mv  a1,a2          -- a1 = &idx[i]                      *)
  (*     0x05e  auipc a4,0x1e                                            *)
  (*     0x062  addi  a4,a4,-918     -- a4 = &disk                        *)
  (*     0x066  c.li  a5,0                                               *)
  (*     0x068..0x072                -- THE SCAN (wp_vdrw_scan)           *)
  (*   found:                                                            *)
  (*     0x046  add   a4,s5,a5       -- a4 = &disk + j                    *)
  (*     0x04a  sb    zero,24(a4)    -- disk.free[j] = 0                  *)
  (*     0x04e  c.sw  a5,0(a1)       -- idx[i] = j                        *)
  (*     0x050  blt   a5,x0,+42      -- DEAD: j < 8                       *)
  (*     0x054  c.addiw s2,s2,1                                          *)
  (*     0x056  c.addi  a2,a2,4      -- -> +0x058 (the driver's [beq])     *)
  (*   not found:                                                        *)
  (*     0x076  sw    s8,0(a1)       -- idx[i] = -1  -> +0x07a            *)
  (*                                                                     *)
  (* The [beq] at +0x058 belongs to the DRIVER, so this lemma is generic  *)
  (* in the iteration index.  Clearing the found cell is the whole        *)
  (* resource move: [free_bundles_split] peels slot j out, the [sb]       *)
  (* rewrites its cell, and [free_bundles_but_upd] re-closes the rest at  *)
  (* [fr_upd fr j false] -- the descriptor bundle walks out with us.      *)
  (* =================================================================== *)
  Definition vdrw_iter_ag (M M' : regfile) : Prop :=
    forall r : mword 5, r <> Ra1 -> r <> Ra2 -> r <> Ra3 -> r <> Ra4 ->
      r <> Ra5 -> r <> Rs2 -> M' !!! Regidx r = M !!! Regidx r.

  Definition vdrw_iter_out (pd : Arch.pa) (fr : nat -> bool) (idxa : Arch.pa)
      (i : nat) (M M' : regfile) : iProp Σ :=
    ((∃ j : nat,
        ⌜(j < 8)%nat /\ fr j = true
         /\ M' !!! Regidx Rs2 = (mword_of_int (Z.of_nat (S i)) : mword 64)
         /\ M' !!! Regidx Ra2 = add_vec (M !!! Regidx Ra2) (mword_of_int 4)⌝ ∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x058) : mword 64) ∗
        idxa ↦₄ (mword_of_int (Z.of_nat j) : mword 32) ∗
        free_slot_res pd j ∗
        free_bundles pd (fr_upd fr j false))
     ∨ (⌜(forall k, (k < 8)%nat -> fr k = false)
         /\ M' !!! Regidx Rs2 = M !!! Regidx Rs2
         /\ M' !!! Regidx Ra2 = M !!! Regidx Ra2⌝ ∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64) ∗
        (∃ v : mword 32, idxa ↦₄ v) ∗
        free_bundles pd fr))%I.

  Lemma wp_vdrw_iter (pme : Arch.pa)
      (pd : Arch.pa) (fr : nat -> bool) (av : nat)
      (i : nat) (idxa : Arch.pa) (M : regfile) :
    (i < 8)%nat ->
    M !!! Regidx Ra2 = (idxa : mword 64) ->
    M !!! Regidx Rs5 = (disk_base : mword 64) ->
    M !!! Regidx Rs1 = (mword_of_int 8 : mword 64) ->
    M !!! Regidx Rs2 = (mword_of_int (Z.of_nat i) : mword 64) ->
    sie_cap_gpr M av false pme -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x05c) : mword 64) -∗
    free_bundles pd fr -∗
    (∃ v : mword 32, idxa ↦₄ v) -∗
    ( ∀ M' : regfile,
        ⌜vdrw_iter_ag M M'⌝ -∗
        sie_cap_gpr M' av false pme -∗
        vdrw_iter_out pd fr idxa i M M' -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hi8 Ha2 Hs5 Hs1 Hs2.
    iIntros "Hcg #Htext Hpc Hcells Hidx Hcont".
    iPoseProof (rwi_05c with "Htext") as "Hi05c".
    (* ---- +0x05c  c.mv a1,a2 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x05c) : mword 64) Ra1 Ra2
              M av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi05c").
              iClear "Hi05c".
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (Q1 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (M !!! Regidx Ra2))]> M).
    change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (M !!! Regidx Ra2))]> M) with Q1.
    assert (HQ1a1 : Q1 !!! Regidx Ra1 = (idxa : mword 64))
      by (rewrite /Q1 upd_eq Ha2; apply add_vec_zero_l).
    assert (Hp05e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x05c) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x05e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp05e) in "Hpc".
    iPoseProof (rwi_05e with "Htext") as "Hi05e".
    (* ---- +0x05e / +0x062  a4 := &disk ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x05e) : mword 64) Ra4
              (mword_of_int 30 : mword 20) Q1 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi05e").
              iClear "Hi05e".
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (Q2 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x05e) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> Q1).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x05e) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> Q1) with Q2.
    assert (Hp062 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x05e) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x062)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp062) in "Hpc".
    iPoseProof (rwi_062 with "Htext") as "Hi062".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x062) : mword 64) Ra4 Ra4
              (mword_of_int 3034 : mword 12) Q2 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi062").
              iClear "Hi062".
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (Q3 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (Q2 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 3034 : mword 12)))]> Q2).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (Q2 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 3034 : mword 12)))]> Q2) with Q3.
    assert (HQ3a4 : Q3 !!! Regidx Ra4
                    = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat 0))).
    { rewrite /Q3 upd_eq /Q2 upd_eq.
      unfold disk_base. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp066 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x062) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x066)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp066) in "Hpc".
    iPoseProof (rwi_066 with "Htext") as "Hi066".
    (* ---- +0x066  c.li a5,0 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x066) : mword 64) Ra5
              (mword_of_int 0 : mword 6) (mword_of_int (Z.of_nat 0) : mword 64) Q3 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi066").
              iClear "Hi066".
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (Q4 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> Q3).
    change (<[Regidx Ra5 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> Q3) with Q4.
    assert (HQ4a5 : Q4 !!! Regidx Ra5 = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /Q4; apply upd_eq).
    assert (HQ4a4 : Q4 !!! Regidx Ra4
                    = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat 0)))
      by (rewrite /Q4 upd_ne; [exact HQ3a4 | reg_neq]).
    assert (HQ4s1 : Q4 !!! Regidx Rs1 = (mword_of_int 8 : mword 64)).
    { rewrite /Q4 upd_ne; [| reg_neq]. rewrite /Q3 upd_ne; [| reg_neq].
      rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [| reg_neq]. exact Hs1. }
    (* the registers the scan does not touch, back at [M] *)
    assert (HQ4ag : forall r : mword 5, r <> Ra1 -> r <> Ra3 -> r <> Ra4 -> r <> Ra5 ->
              Q4 !!! Regidx r = M !!! Regidx r).
    { intros r H1 H3 H4 H5.
      rewrite /Q4 upd_ne; [| congruence]. rewrite /Q3 upd_ne; [| congruence].
      rewrite /Q2 upd_ne; [| congruence]. rewrite /Q1 upd_ne; [reflexivity | congruence]. }
    assert (Hp068 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x066) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x068)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp068) in "Hpc".
    (* ---- +0x068 .. +0x072  THE SCAN ---- *)
    iApply (wp_vdrw_scan pme pd fr av 7 0 Q4 ltac:(reflexivity) HQ4a5 HQ4a4 HQ4s1
              with "Hcg Htext Hpc Hcells").
    iIntros (Q5) "%Hag5 Hcells Hcg Hor".
    rewrite /vdrw_scan_out.
    (* the scan hands the cells back in [big_sepL] form; [free_bundles] is
       that very term, so fold it once for the surgery below *)
    iAssert (free_bundles pd fr) with "[Hcells]" as "Hcells".
    { iExact "Hcells". }
    assert (HQ5a1 : Q5 !!! Regidx Ra1 = (idxa : mword 64))
      by (rewrite (Hag5 Ra1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HQ1a1).
    assert (HQ5s5 : Q5 !!! Regidx Rs5 = (disk_base : mword 64)).
    { rewrite (Hag5 Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      rewrite (HQ4ag Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      exact Hs5. }
    assert (HQ5s2 : Q5 !!! Regidx Rs2 = (mword_of_int (Z.of_nat i) : mword 64)).
    { rewrite (Hag5 Rs2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      rewrite (HQ4ag Rs2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      exact Hs2. }
    assert (HQ5a2 : Q5 !!! Regidx Ra2 = (idxa : mword 64)).
    { rewrite (Hag5 Ra2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      rewrite (HQ4ag Ra2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      exact Ha2. }
    assert (HQ5ag : forall r : mword 5, r <> Ra1 -> r <> Ra3 -> r <> Ra4 -> r <> Ra5 ->
              Q5 !!! Regidx r = M !!! Regidx r).
    { intros r H1 H3 H4 H5.
      rewrite (Hag5 r H3 H4 H5). exact (HQ4ag r H1 H3 H4 H5). }
    iDestruct "Hor" as "[Hf|Hn]".
    - (* ============ FOUND: clear the cell, record the index ============ *)
      iDestruct "Hf" as (j) "[%Hj Hpc]".
      destruct Hj as (Hj80 & Hfrj & _ & HQ5a5).
      assert (Hj8 : (j < 8)%nat) by (clear -Hj80; lia).
      iPoseProof (rwi_046 with "Htext") as "Hi046".
      (* +0x046  add a4,s5,a5 *)
      iApply (wp_add_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x046) : mword 64) Ra4 Rs5 Ra5
                (add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat j))) Q5 av false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rgall; rewrite HQ5s5 HQ5a5; reflexivity)
                with "Hcg Hpc Hi046").
                iClear "Hi046".
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (Q6 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat j)))]> Q5).
      change (<[Regidx Ra4 := regval_into_reg
                    (add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat j)))]> Q5) with Q6.
      assert (HQ6a4 : Q6 !!! Regidx Ra4
                      = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat j)))
        by (rewrite /Q6; apply upd_eq).
      assert (Hp04a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x046) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x04a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp04a) in "Hpc".
      (* peel slot j out of the free bundle *)
      iEval (rewrite (free_bundles_split pd fr j Hj8)) in "Hcells".
      iDestruct "Hcells" as "[[Hcell Hbun] Hrest]".
      iEval (rewrite Hfrj) in "Hcell". iEval (rewrite Hfrj) in "Hbun".
      (* +0x04a  sb zero,24(a4) *)
      iDestruct (sie_cap_gpr_x0 Q6 av false pme (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0 Hcg]".
      assert (Hsba : add_vec (Q6 !!! Regidx Ra4)
                       (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = (d_free_cell j : mword 64))
        by (rewrite HQ6a4; apply vdrw_free_addr).
      assert (Hz8 : trunc8 (Q6 !!! Regidx (mword_of_int 0 : mword 5)) = byte_zero)
        by (rewrite Hz0; apply bv_eq; vm_compute; reflexivity).
      iPoseProof (rwi_04a with "Htext") as "Hi04a".
      iApply (wp_sb_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x04a) : mword 64)
                (mword_of_int 0 : mword 5) Ra4 (mword_of_int 24 : mword 12) Q6 av
                (Z_to_bv 8 1) false with "Hcg Hpc Hi04a [Hcell]").
                iClear "Hi04a".
      { rgall. iEval (rewrite Hsba). iExact "Hcell". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell". rgall.
      iEval (rewrite Hsba Hz8) in "Hcell".
      assert (Hp04e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x04a) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x04e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp04e) in "Hpc".
      (* +0x04e  c.sw a5,0(a1) *)
      iDestruct "Hidx" as (v0) "Hidx".
      assert (HQ6a1 : Q6 !!! Regidx Ra1 = (idxa : mword 64))
        by (rewrite /Q6 upd_ne; [exact HQ5a1 | reg_neq]).
      assert (HQ6a5 : Q6 !!! Regidx Ra5 = (mword_of_int (Z.of_nat j) : mword 64))
        by (rewrite /Q6 upd_ne; [exact HQ5a5 | reg_neq]).
      assert (Hswa : add_vec (Q6 !!! Regidx Ra1)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = (idxa : mword 64))
        by (rewrite HQ6a1; apply vdrw_addv_sext0).
      iPoseProof (rwi_04e with "Htext") as "Hi04e".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x04e) : mword 64) Ra5 Ra1
                (mword_of_int 0 : mword 12) Q6 av v0 false with "Hcg Hpc Hi04e [Hidx]").
                iClear "Hi04e".
      { rgall. iEval (rewrite Hswa). iExact "Hidx". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hidx". rgall.
      iEval (rewrite Hswa HQ6a5 (vdrw_trunc32_small j Hj8)) in "Hidx".
      assert (Hp050 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x04e) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x050)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp050) in "Hpc".
      iPoseProof (rwi_050 with "Htext") as "Hi050".
      (* +0x050  blt a5,x0 : DEAD, j >= 0 *)
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x050) : mword 64)
                (mword_of_int 42 : mword 13) Ra5 Q6 av false
                ltac:(vm_compute; discriminate)
                ltac:(rgall; rewrite HQ6a5; exact (vdrw_notneg j Hj8))
                with "Hcg Hpc Hi050").
                iClear "Hi050".
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hp054 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x050) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x054)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp054) in "Hpc".
      iPoseProof (rwi_054 with "Htext") as "Hi054".
      (* +0x054  c.addiw s2,s2,1 *)
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x054) : mword 64) Rs2
                (mword_of_int 1 : mword 6) Q6 av false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi054").
                iClear "Hi054".
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (Q7 := <[Regidx Rs2 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (Q6 !!! Regidx Rs2)
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> Q6).
      change (<[Regidx Rs2 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (Q6 !!! Regidx Rs2)
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> Q6)
        with Q7.
      assert (HQ6s2 : Q6 !!! Regidx Rs2 = (mword_of_int (Z.of_nat i) : mword 64))
        by (rewrite /Q6 upd_ne; [exact HQ5s2 | reg_neq]).
      assert (HQ7s2 : Q7 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (S i)) : mword 64))
        by (rewrite /Q7 upd_eq HQ6s2; exact (vdrw_addiw_succ i Hi8)).
      assert (Hp056 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x054) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x056)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp056) in "Hpc".
      iPoseProof (rwi_056 with "Htext") as "Hi056".
      (* +0x056  c.addi a2,a2,4 *)
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x056) : mword 64) Ra2
                (mword_of_int 4 : mword 6) Q7 av false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi056").
                iClear "Hi056".
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (Q8 := <[Regidx Ra2 := regval_into_reg
                    (add_vec (Q7 !!! Regidx Ra2)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> Q7).
      change (<[Regidx Ra2 := regval_into_reg
                    (add_vec (Q7 !!! Regidx Ra2)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> Q7) with Q8.
      assert (HQ7a2 : Q7 !!! Regidx Ra2 = (idxa : mword 64)).
      { rewrite /Q7 upd_ne; [| reg_neq]. rewrite /Q6 upd_ne; [| reg_neq]. exact HQ5a2. }
      assert (HQ8a2 : Q8 !!! Regidx Ra2
                      = add_vec (M !!! Regidx Ra2) (mword_of_int 4)).
      { rewrite /Q8 upd_eq HQ7a2 vdrw_sext_4 Ha2. reflexivity. }
      assert (HQ8s2 : Q8 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (S i)) : mword 64))
        by (rewrite /Q8 upd_ne; [exact HQ7s2 | reg_neq]).
      assert (Hp058 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x056) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x058)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp058) in "Hpc".
      iApply ("Hcont" $! Q8 with "[%] Hcg [Hpc Hidx Hbun Hcell Hrest]").
      { intros r H1 H2 H3 H4 H5 Hs.
        rewrite /Q8 upd_ne; [| congruence]. rewrite /Q7 upd_ne; [| congruence].
        rewrite /Q6 upd_ne; [| congruence]. exact (HQ5ag r H1 H3 H4 H5). }
      rewrite /vdrw_iter_out. iLeft. iExists j.
      iSplitR; [ iPureIntro; split_and!;
                 [ exact Hj8 | exact Hfrj | exact HQ8s2 | exact HQ8a2 ] |].
      iFrame "Hpc Hidx Hbun".
      (* re-close the free bundle at [fr] with slot j cleared *)
      rewrite (free_bundles_split pd (fr_upd fr j false) j Hj8).
      rewrite fr_upd_eq. rewrite -(free_bundles_but_upd pd fr j false).
      iFrame "Hrest". iSplitL "Hcell"; [ iExact "Hcell" | done ].
    - (* ============ NOT FOUND: idx[i] = -1, on to the failure path ==== *)
      iDestruct "Hn" as "[%Hall Hpc]".
      iDestruct "Hidx" as (v0) "Hidx".
      assert (Hswa : add_vec (Q5 !!! Regidx Ra1)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = (idxa : mword 64))
        by (rewrite HQ5a1; apply vdrw_addv_sext0).
      iPoseProof (rwi_076 with "Htext") as "Hi076".
      iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x076) : mword 64) Rs8 Ra1
                (mword_of_int 0 : mword 12) Q5 av v0 false with "Hcg Hpc Hi076 [Hidx]").
                iClear "Hi076".
      { rgall. iEval (rewrite Hswa). iExact "Hidx". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hidx". rgall.
      iEval (rewrite Hswa) in "Hidx".
      assert (Hp07a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x076) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x07a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp07a) in "Hpc".
      iApply ("Hcont" $! Q5 with "[%] Hcg [Hpc Hidx Hcells]").
      { intros r H1 H2 H3 H4 H5 Hs. exact (HQ5ag r H1 H3 H4 H5). }
      rewrite /vdrw_iter_out. iRight.
      iSplitR; [ iPureIntro; split_and!;
                 [ intros k Hk; apply Hall; clear -Hk; lia
                 | rewrite HQ5s2 Hs2; reflexivity
                 | rewrite HQ5a2 Ha2; reflexivity ] |].
      iFrame "Hpc Hcells". iExists _. iExact "Hidx".
  Qed.


  (* =================================================================== *)
  (* P2.2b: the middle three-times loop, +0x0bc .. (+0x0c4 | +0x07a).     *)
  (*                                                                     *)
  (*     0x0bc  addi  a2,s0,-96      -- a2 = &idx[0]                      *)
  (*     0x0c0  c.li  s2,0                                               *)
  (*     0x0c2  c.j   -> +0x05c                                          *)
  (*   then three times: [wp_vdrw_iter] and                              *)
  (*     0x058  beq   s2,s4,+88      -- i = 3 -> +0x0c4 (all three won)   *)
  (*                                                                     *)
  (* The trip count is a literal 3, so the loop is UNROLLED: there is no  *)
  (* invariant to find, and each unrolling differs only in which [idx[]]  *)
  (* cell it targets.  The failure exits are kept apart by iteration      *)
  (* count because that is exactly what the failure path at +0x07a tests  *)
  (* ([blez s2] / [bge a5,s2]) to decide how many descriptors to give     *)
  (* back.                                                               *)
  (*                                                                     *)
  (* [idx[3]] straddles two frame slots -- idx[0],idx[1] are the halves   *)
  (* of slot 12 and idx[2] is the low half of slot 11 -- so the entry     *)
  (* [vdrw_scratch] is split with [word_pointsto_split4], taking the      *)
  (* 8-alignment out FIRST (the halves no longer carry it, and the        *)
  (* epilogue's [stack_own] rebuild needs it back).                       *)
  (* =================================================================== *)

  Lemma vdrw_scratch_split (sp0 : Arch.pa) :
    vdrw_scratch sp0 -∗
    ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
     /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ ∗
    (∃ v0 v1 v2 vp : mword 32,
       pa_stk sp0 12 ↦₄ v0 ∗ pa_add (pa_stk sp0 12) 4 ↦₄ v1 ∗
       pa_stk sp0 11 ↦₄ v2 ∗ pa_add (pa_stk sp0 11) 4 ↦₄ vp).
  Proof.
    iIntros "H". iDestruct "H" as (w11 w12) "[H11 H12]".
    iDestruct (word_pointsto_aligned_p with "H11") as %Hal11.
    iDestruct (word_pointsto_aligned_p with "H12") as %Hal12.
    iSplitR; [ iPureIntro; split; [exact Hal11 | exact Hal12] |].
    rewrite !word_pointsto_split4.
    iDestruct "H11" as "[H11lo H11hi]". iDestruct "H12" as "[H12lo H12hi]".
    iExists (word_lo w12), (word_hi w12), (word_lo w11), (word_hi w11).
    iFrame "H12lo H12hi H11lo H11hi".
  Qed.

  (* [fr_upd] only ever clears, so a later "still free" fact is a fact
     about the ORIGINAL map, at a necessarily different index *)
  Lemma fr_upd_true_inv (fr : nat -> bool) (h m : nat) :
    fr_upd fr h false m = true -> m <> h /\ fr m = true.
  Proof.
    intro H. destruct (Nat.eq_dec m h) as [He|Hne].
    - subst m. rewrite fr_upd_eq in H. exfalso. discriminate H.
    - rewrite (fr_upd_ne fr h m false Hne) in H. split; [exact Hne | exact H].
  Qed.

  Definition vdrw_alloc_fail (pd sp0 : Arch.pa) (fr : nat -> bool)
      (M' : regfile) : iProp Σ :=
    (( ⌜M' !!! Regidx Rs2 = (mword_of_int (Z.of_nat 0) : mword 64)⌝ ∗
       free_bundles pd fr ∗
       (∃ v0 v1 v2 : mword 32, vdrw_idx sp0 v0 v1 v2))
     ∨ (∃ h : nat,
          ⌜(h < 8)%nat /\ fr h = true
           /\ M' !!! Regidx Rs2 = (mword_of_int (Z.of_nat 1) : mword 64)⌝ ∗
          free_bundles pd (fr_upd fr h false) ∗ free_slot_res pd h ∗
          (∃ v1 v2 : mword 32,
             vdrw_idx sp0 (mword_of_int (Z.of_nat h)) v1 v2))
     ∨ (∃ h m2 : nat,
          ⌜(h < 8)%nat /\ (m2 < 8)%nat /\ h <> m2
           /\ fr h = true /\ fr m2 = true
           /\ M' !!! Regidx Rs2 = (mword_of_int (Z.of_nat 2) : mword 64)⌝ ∗
          free_bundles pd (fr_upd (fr_upd fr h false) m2 false) ∗
          free_slot_res pd h ∗ free_slot_res pd m2 ∗
          (∃ v2 : mword 32,
             vdrw_idx sp0 (mword_of_int (Z.of_nat h))
                          (mword_of_int (Z.of_nat m2)) v2)))%I.

  Definition vdrw_alloc_out (pd sp0 : Arch.pa) (fr : nat -> bool)
      (M' : regfile) : iProp Σ :=
    ((∃ h m2 t : nat,
        ⌜(h < 8)%nat /\ (m2 < 8)%nat /\ (t < 8)%nat
         /\ h <> m2 /\ h <> t /\ m2 <> t
         /\ fr h = true /\ fr m2 = true /\ fr t = true⌝ ∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x0c4) : mword 64) ∗
        vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                     (mword_of_int (Z.of_nat t)) ∗
        free_slot_res pd h ∗ free_slot_res pd m2 ∗ free_slot_res pd t ∗
        free_bundles pd (fr_upd (fr_upd (fr_upd fr h false) m2 false) t false))
     ∨ (pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64) ∗
        vdrw_alloc_fail pd sp0 fr M'))%I.

  Lemma wp_vdrw_alloc3 (pme : Arch.pa)
      (pd sp0 : Arch.pa) (fr : nat -> bool) (av : nat) (M : regfile) :
    M !!! Regidx Rs0 = (sp0 : mword 64) ->
    M !!! Regidx Rs5 = (disk_base : mword 64) ->
    M !!! Regidx Rs1 = (mword_of_int 8 : mword 64) ->
    M !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64) ->
    sie_cap_gpr M av false pme -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x0bc) : mword 64) -∗
    free_bundles pd fr -∗
    vdrw_scratch sp0 -∗
    (* the continuation is UNDER A LATER: the driver's outer sleep-retry
       iLoeb closes its back edge through this call, and the [c.j] at
       +0x0c2 -- the first instruction this lemma runs after the loop head --
       is where that later is paid.  (The parenthesised [▷] is what lets a
       caller [iNext] and strip the Loeb hypothesis's own later.) *)
    ( ▷ ( ∀ M' : regfile,
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
           M' !!! Regidx r = M !!! Regidx r⌝ -∗
        ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
         /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
        sie_cap_gpr M' av false pme -∗
        vdrw_alloc_out pd sp0 fr M' -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs0 Hs5 Hs1 Hs4.
    iIntros "Hcg #Htext Hpc Hcells Hscr Hcont".
    iDestruct (vdrw_scratch_split with "Hscr") as "[%Hal Hidx]".
    iDestruct "Hidx" as (u0 u1 u2 up) "(Hx0 & Hx1 & Hx2 & Hxp)".
    iPoseProof (rwi_0bc with "Htext") as "Hi0a8".
    (* ---- +0x0bc  addi a2,s0,-96 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0bc) : mword 64) Ra2 Rs0
              (mword_of_int 4000 : mword 12) M av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a8").
              iClear "Hi0a8".
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D1 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (M !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4000 : mword 12)))]> M).
    change (<[Regidx Ra2 := regval_into_reg
                  (add_vec (M !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4000 : mword 12)))]> M) with D1.
    assert (HD1a2 : D1 !!! Regidx Ra2 = (pa_stk sp0 12 : mword 64))
      by (rewrite /D1 upd_eq Hs0; apply vdrw_idx0_addr).
    assert (Hp0ac : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0bc) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x0c0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0ac) in "Hpc".
    iPoseProof (rwi_0c0 with "Htext") as "Hi0ac".
    (* ---- +0x0c0  c.li s2,0 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0c0) : mword 64) Rs2
              (mword_of_int 0 : mword 6) (mword_of_int (Z.of_nat 0) : mword 64) D1 av false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0ac").
              iClear "Hi0ac".
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (D2 := <[Regidx Rs2 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> D1).
    change (<[Regidx Rs2 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> D1) with D2.
    assert (Hp0ae : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0c0) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x0c2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0ae) in "Hpc".
    iPoseProof (rwi_0c2 with "Htext") as "Hi0ae".
    (* ---- +0x0c2  c.j -> +0x05c ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0c2) : mword 64)
              (sign_extend' 21 (concat_vec (mword_of_int 1997 : mword 11) ('b"0")))
              D2 av false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0ae").
              iClear "Hi0ae".
    iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc". rgall.
    assert (Hj05c : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0c2) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 1997 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x05c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hj05c) in "Hpc".
    (* the four loop-invariant registers, at D2 *)
    assert (HD2s2 : D2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /D2; apply upd_eq).
    assert (HD2a2 : D2 !!! Regidx Ra2 = (pa_stk sp0 12 : mword 64))
      by (rewrite /D2 upd_ne; [exact HD1a2 | reg_neq]).
    assert (HD2s5 : D2 !!! Regidx Rs5 = (disk_base : mword 64)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact Hs5. }
    assert (HD2s1 : D2 !!! Regidx Rs1 = (mword_of_int 8 : mword 64)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact Hs1. }
    assert (HD2s4 : D2 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64)).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact Hs4. }
    assert (HD2cs : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
              D2 !!! Regidx r = M !!! Regidx r).
    { intros r Hcs Hne. rewrite /D2 upd_ne; [| congruence].
      rewrite /D1 upd_ne; [reflexivity |].
      apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hcs]. }
    (* ============================ ITERATION 0 ======================== *)
    iApply (wp_vdrw_iter pme pd fr av 0 (pa_stk sp0 12) D2
              ltac:(clear; lia) HD2a2 HD2s5 HD2s1 HD2s2
              with "Hcg Htext Hpc Hcells [Hx0]").
    { iExists u0. iExact "Hx0". }
    iIntros (E0) "%Hag0 Hcg Hout0".
    rewrite /vdrw_iter_out. iDestruct "Hout0" as "[Hf0|Hn0]"; last first.
    { (* --- failure at i = 0 --- *)
      iDestruct "Hn0" as "[%Hp0 [Hpc [Hx0 Hcells]]]".
      destruct Hp0 as (Hall & Hs2e & _).
      iApply ("Hcont" $! E0 with "[%] [%] Hcg [Hpc Hcells Hx0 Hx1 Hx2 Hxp]").
      { intros r Hcs Hne. rewrite (Hag0 r ltac:(regne) ltac:(regne) ltac:(regne)
          ltac:(regne) ltac:(regne) Hne). exact (HD2cs r Hcs Hne). }
      { exact Hal. }
      rewrite /vdrw_alloc_out. iRight. iFrame "Hpc".
      rewrite /vdrw_alloc_fail. iLeft.
      iSplitR; [ iPureIntro; rewrite Hs2e; exact HD2s2 |].
      iFrame "Hcells". iDestruct "Hx0" as (vv) "Hx0".
      iExists vv, u1, u2. rewrite /vdrw_idx.
      iFrame "Hx0 Hx1 Hx2". iExists up. iExact "Hxp". }
    iDestruct "Hf0" as (h) "[%Hh [Hpc [Hx0 [Hbh Hcells]]]]".
    destruct Hh as (Hh8 & Hfrh & HE0s2 & HE0a2).
    (* +0x058: s2 = 1 <> 3, fall through *)
    assert (HE0s4 : E0 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64))
      by (rewrite (Hag0 Rs4 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HD2s4).
    iPoseProof (rwi_058 with "Htext") as "Hi058".
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x058) : mword 64)
              (mword_of_int 108 : mword 13) Rs4 Rs2 E0 av false
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgall; rewrite HE0s2 HE0s4; vm_compute; reflexivity)
              with "Hcg Hpc Hi058").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp05c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x058) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x05c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp05c) in "Hpc".
    assert (HE0a2' : E0 !!! Regidx Ra2 = (pa_add (pa_stk sp0 12) 4 : mword 64))
      by (rewrite HE0a2 HD2a2; apply vdrw_idx1_addr).
    assert (HE0s5 : E0 !!! Regidx Rs5 = (disk_base : mword 64))
      by (rewrite (Hag0 Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HD2s5).
    assert (HE0s1 : E0 !!! Regidx Rs1 = (mword_of_int 8 : mword 64))
      by (rewrite (Hag0 Rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HD2s1).
    assert (HE0cs : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
              E0 !!! Regidx r = M !!! Regidx r).
    { intros r Hcs Hne. rewrite (Hag0 r ltac:(regne) ltac:(regne) ltac:(regne)
        ltac:(regne) ltac:(regne) Hne). exact (HD2cs r Hcs Hne). }
    (* ============================ ITERATION 1 ======================== *)
    iApply (wp_vdrw_iter pme pd (fr_upd fr h false) av 1
              (pa_add (pa_stk sp0 12) 4) E0
              ltac:(clear; lia) HE0a2' HE0s5 HE0s1 HE0s2
              with "Hcg Htext Hpc Hcells [Hx1]").
    { iExists u1. iExact "Hx1". }
    iIntros (E1) "%Hag1 Hcg Hout1".
    rewrite /vdrw_iter_out. iDestruct "Hout1" as "[Hf1|Hn1]"; last first.
    { (* --- failure at i = 1 --- *)
      iDestruct "Hn1" as "[%Hp1 [Hpc [Hx1 Hcells]]]".
      destruct Hp1 as (Hall & Hs2e & _).
      iApply ("Hcont" $! E1 with "[%] [%] Hcg [Hpc Hcells Hbh Hx0 Hx1 Hx2 Hxp]").
      { intros r Hcs Hne. rewrite (Hag1 r ltac:(regne) ltac:(regne) ltac:(regne)
          ltac:(regne) ltac:(regne) Hne). exact (HE0cs r Hcs Hne). }
      { exact Hal. }
      rewrite /vdrw_alloc_out. iRight. iFrame "Hpc".
      rewrite /vdrw_alloc_fail. iRight. iLeft. iExists h.
      iSplitR; [ iPureIntro; split_and!;
                 [ exact Hh8 | exact Hfrh | rewrite Hs2e; exact HE0s2 ] |].
      iFrame "Hcells Hbh". iDestruct "Hx1" as (vv) "Hx1".
      iExists vv, u2. rewrite /vdrw_idx.
      iFrame "Hx0 Hx1 Hx2". iExists up. iExact "Hxp". }
    iDestruct "Hf1" as (m2) "[%Hm [Hpc [Hx1 [Hbm Hcells]]]]".
    destruct Hm as (Hm8 & Hfrm0 & HE1s2 & HE1a2).
    destruct (fr_upd_true_inv fr h m2 Hfrm0) as (Hmh & Hfrm).
    assert (HE1s4 : E1 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64))
      by (rewrite (Hag1 Rs4 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HE0s4).
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x058) : mword 64)
              (mword_of_int 108 : mword 13) Rs4 Rs2 E1 av false
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgall; rewrite HE1s2 HE1s4; vm_compute; reflexivity)
              with "Hcg Hpc Hi058").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hp05c) in "Hpc".
    assert (HE1a2' : E1 !!! Regidx Ra2 = (pa_stk sp0 11 : mword 64))
      by (rewrite HE1a2 HE0a2' -vdrw_idx1_addr; apply vdrw_idx2_addr).
    assert (HE1s5 : E1 !!! Regidx Rs5 = (disk_base : mword 64))
      by (rewrite (Hag1 Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HE0s5).
    assert (HE1s1 : E1 !!! Regidx Rs1 = (mword_of_int 8 : mword 64))
      by (rewrite (Hag1 Rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HE0s1).
    assert (HE1cs : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 ->
              E1 !!! Regidx r = M !!! Regidx r).
    { intros r Hcs Hne. rewrite (Hag1 r ltac:(regne) ltac:(regne) ltac:(regne)
        ltac:(regne) ltac:(regne) Hne). exact (HE0cs r Hcs Hne). }
    (* ============================ ITERATION 2 ======================== *)
    iApply (wp_vdrw_iter pme pd (fr_upd (fr_upd fr h false) m2 false) av 2
              (pa_stk sp0 11) E1
              ltac:(clear; lia) HE1a2' HE1s5 HE1s1 HE1s2
              with "Hcg Htext Hpc Hcells [Hx2]").
    { iExists u2. iExact "Hx2". }
    iIntros (E2) "%Hag2 Hcg Hout2".
    rewrite /vdrw_iter_out. iDestruct "Hout2" as "[Hf2|Hn2]"; last first.
    { (* --- failure at i = 2 --- *)
      iDestruct "Hn2" as "[%Hp2 [Hpc [Hx2 Hcells]]]".
      destruct Hp2 as (Hall & Hs2e & _).
      iApply ("Hcont" $! E2 with "[%] [%] Hcg [Hpc Hcells Hbh Hbm Hx0 Hx1 Hx2 Hxp]").
      { intros r Hcs Hne. rewrite (Hag2 r ltac:(regne) ltac:(regne) ltac:(regne)
          ltac:(regne) ltac:(regne) Hne). exact (HE1cs r Hcs Hne). }
      { exact Hal. }
      rewrite /vdrw_alloc_out. iRight. iFrame "Hpc".
      rewrite /vdrw_alloc_fail. iRight. iRight. iExists h, m2.
      iSplitR; [ iPureIntro; split_and!;
                 [ exact Hh8 | exact Hm8 | (clear -Hmh; congruence)
                 | exact Hfrh | exact Hfrm | rewrite Hs2e; exact HE1s2 ] |].
      iFrame "Hcells Hbh Hbm". iDestruct "Hx2" as (vv) "Hx2".
      iExists vv. rewrite /vdrw_idx.
      iFrame "Hx0 Hx1 Hx2". iExists up. iExact "Hxp". }
    iDestruct "Hf2" as (t) "[%Ht [Hpc [Hx2 [Hbt Hcells]]]]".
    destruct Ht as (Ht8 & Hfrt0 & HE2s2 & _).
    destruct (fr_upd_true_inv (fr_upd fr h false) m2 t Hfrt0) as (Htm & Hfrt1).
    destruct (fr_upd_true_inv fr h t Hfrt1) as (Hth & Hfrt).
    (* +0x058: s2 = 3 = s4, TAKEN to +0x0c4 *)
    assert (HE2s4 : E2 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64))
      by (rewrite (Hag2 Rs4 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HE1s4).
    iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x058) : mword 64)
              (mword_of_int 108 : mword 13) Rs4 Rs2 E2 av false
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgall; rewrite HE2s2 HE2s4; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi058 [Hcells Hbh Hbm Hbt Hx0 Hx1 Hx2 Hxp Hcont]").
              iClear "Hi058".
    iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj0b0 : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x058) : mword 64)
                      (sign_extend' 64 (mword_of_int 108 : mword 13))
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x0c4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hj0b0) in "Hpc".
    iApply ("Hcont" $! E2 with "[%] [%] Hcg [Hpc Hcells Hbh Hbm Hbt Hx0 Hx1 Hx2 Hxp]").
    { intros r Hcs Hne. rewrite (Hag2 r ltac:(regne) ltac:(regne) ltac:(regne)
        ltac:(regne) ltac:(regne) Hne). exact (HE1cs r Hcs Hne). }
    { exact Hal. }
    rewrite /vdrw_alloc_out. iLeft. iExists h, m2, t.
    iSplitR; [ iPureIntro; split_and!;
               [ exact Hh8 | exact Hm8 | exact Ht8
               | (clear -Hmh; congruence) | (clear -Hth; congruence)
               | (clear -Htm; congruence)
               | exact Hfrh | exact Hfrm | exact Hfrt ] |].
    iFrame "Hpc Hbh Hbm Hbt Hcells".
    rewrite /vdrw_idx. iFrame "Hx0 Hx1 Hx2". iExists up. iExact "Hxp".
  Qed.

End ProofVirtioDiskRw.
End VirtioDiskRwPhases.

