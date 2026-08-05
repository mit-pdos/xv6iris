(* ProofVirtioDiskIntr.v -- virtio_disk_intr() over the SIE-agnostic sconf
   world.

   virtio_disk_intr @ 0x80005962 is virtio_disk.c's completion handler:

     acquire(&disk.vdisk_lock);
     *R(INTERRUPT_ACK) = *R(INTERRUPT_STATUS) & 0x3;
     __sync_synchronize();
     while (disk.used_idx != disk.used->idx) {
       __sync_synchronize();
       int id = disk.used->ring[disk.used_idx % NUM].id;
       if (disk.info[id].status != 0) panic("virtio_disk_intr status");
       struct buf *b = disk.info[id].b;
       b->disk = 0;
       wakeup(b);
       disk.used_idx += 1;
     }
     release(&disk.vdisk_lock);

   The frame is the standard 32-byte / ra,s0,s1 shape (byte-identical to
   sys_uptime's), and the ISR read/ack pair runs on the [dev_inv]-borrowing
   virtio MMIO leaves of WpVirtioDev.v.

   A functor over ACQUIRE / RELEASE / WAKEUP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import WpGpr RegFile.
Require Import KptPt.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import CodeMycpu ProcGeom.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn SchedCtx FdSlots.
Require Import KernelRvcDecode WpAuipc.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import MinstretInv.
Require Import WpSmodeHalf.
Require Import VirtioModel VirtioQueue DiskPtsto VirtioProto DiskInv.
Require Import VirtioModel.
Require Import WpVirtioDev.
Require Import WpUart.
Require Import PermInv.
Require Import SpecPanic SpecWakeup SpecAcquire SpecRelease.
Require Import CodeVirtioDiskIntr.
Require Import SpecVirtioDiskIntr.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* a whole-function goal over the disk invariant prints enormous; see
   claude-notes/durable-notes.md ("A FAILING TACTIC ... LOOKS LIKE A HANG") *)
Set Printing Depth 40.

(* ===================================================================== *)
(* §0  The virtio-mmio window geometry, per concrete register address.    *)
(*     (The [vdi_geom] of ProofVirtioDiskInit.v -- that file's copy is    *)
(*     behind its own module seal, and the predicate is four vm_compute   *)
(*     facts, so it is re-stated rather than promoted.)                   *)
(* ===================================================================== *)

Definition vt_geom (a : mword 64) : Prop :=
  (virtio_base <= uint a < virtio_base + virtio_size)%Z
  /\ is_aligned_vaddr (Virtaddr a) 4 = true
  /\ neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false
  /\ kpt_dev_vpn (svpn_of a).

Local Ltac zrange_vm := split; [ apply Z.leb_le | apply Z.ltb_lt ]; vm_compute; reflexivity.
Local Ltac vgeom := unfold vt_geom; split; [zrange_vm|];
              split; [vm_compute; reflexivity|];
              split; [vm_compute; reflexivity|];
              unfold kpt_dev_vpn; zrange_vm.

(* INTERRUPT_STATUS and INTERRUPT_ACK, the only two registers intr names *)
Lemma vg_060 : vt_geom (mword_of_int 0x10001060). Proof. vgeom. Qed.
Lemma vg_064 : vt_geom (mword_of_int 0x10001064). Proof. vgeom. Qed.


(* the width-4 load's post value, collapsed to a plain sign-extension *)
Lemma vt_ldval (w : mword 32) :
  extend_value false (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) w)
  = sign_extend' 64 w.
Proof. rewrite <- (data2_ext_4 w). rewrite autocast_id. reflexivity. Qed.

Section VtLeaves.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).
  Notation a4_idx := (mword_of_int 14 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ---- the two dev_inv-borrowing virtio leaves, at a CONCRETE address ---- *)

  Lemma wp_vt_lw_dev (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ)
      (pc : mword 64) (rvc : bool) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (a : mword 64) (off : Z) (P : bv 32 -> Prop)
      (p : mword 64) :
    add_vec (rget m rs1) (sign_extend' 64 imm) = a ->
    vt_geom a ->
    (uint a - virtio_base)%Z = off ->
    uint rd <> 0 -> rd_ok rd ->
    (forall v : virtio_state, virtio_isr_ok v ->
       exists w : bv 32, virtio_read v off = Some w /\ P w) ->
    sie_cap_gpr m n false p -∗
    pc_is pc -∗ instr pc rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    dev_inv γu γd -∗
    ( ∀ w : bv 32, ⌜ P w ⌝ -∗
      sie_cap_gpr (<[Regidx rd := regval_into_reg (sign_extend' 64 (w : mword 32))]> m) n false p -∗
      pc_is (add_vec_int pc (if rvc then 2 else 4)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hea Hg Hoff Hrd Hrdok Hread. destruct Hg as (Hr & Hal & Hcan & Hdv).
    assert (Ha8 : sign_extend' 64 (subrange_vec_dec
                    (add_vec (rget m rs1) (sign_extend' 64 imm)) (xlen - 0 - 1) 0) = a).
    { rewrite subrange_id. rewrite sign_extend'_id. exact Hea. }
    iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
    iApply (wp_lw_virtio_dev_s_sconf (CID:=CID) γu γd Φ pc rvc false rd rs1 imm m n P false
              ltac:(rewrite Ha8; exact Hr)
              ltac:(rewrite Ha8; exact Hal)
              ltac:(rewrite Ha8; exact Hcan)
              ltac:(rewrite Ha8; exact Hdv)
              Hrd Hrdok
              ltac:(rewrite Ha8; rewrite Hoff; exact Hread)
              with "Hcg Hpc Hinstr Hdinv [-]").
    iApply wp_next_off_intro.
    iIntros (w) "%HPw Hcg Hpc". iEval (rewrite vt_ldval) in "Hcg".
    iApply ("Hcont" $! w with "[%] Hcg Hpc"). exact HPw.
  Qed.

  Lemma wp_vt_sw_dev (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ)
      (pc : mword 64) (rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (a : mword 64) (off : Z) (sw : mword 32)
      (p : mword 64) :
    add_vec (rget m rs1) (sign_extend' 64 imm) = a ->
    vt_geom a ->
    (uint a - virtio_base)%Z = off ->
    trunc32 (rget m rs2) = sw ->
    (forall v : virtio_state, virtio_isr_ok v ->
       exists v' : virtio_state,
         virtio_write v off sw = Some v'
         /\ virtio_isr_ok v'
         /\ v_cfg v' = v_cfg v /\ v_seen v' = v_seen v
         /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v) ->
    sie_cap_gpr m n false p -∗
    pc_is pc -∗ instr pc rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    dev_inv γu γd -∗
    ( sie_cap_gpr m n false p -∗
      pc_is (add_vec_int pc (if rvc then 2 else 4)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hea Hg Hoff Hsw Hwr. destruct Hg as (Hr & Hal & Hcan & Hdv).
    assert (Hsw' : (autocast (T := mword)
                      (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = sw)
      by exact Hsw.
    assert (Ha8 : sign_extend' 64 (subrange_vec_dec
                    (add_vec (rget m rs1) (sign_extend' 64 imm)) (xlen - 0 - 1) 0) = a).
    { rewrite subrange_id. rewrite sign_extend'_id. exact Hea. }
    iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
    iApply (wp_sw_virtio_dev_s_sconf (CID:=CID) γu γd Φ pc rvc rs2 rs1 imm m n false
              ltac:(rewrite Ha8; exact Hr)
              ltac:(rewrite Ha8; exact Hal)
              ltac:(rewrite Ha8; exact Hcan)
              ltac:(rewrite Ha8; exact Hdv)
              ltac:(rewrite Ha8; rewrite Hoff; rewrite Hsw'; exact Hwr)
              with "Hcg Hpc Hinstr Hdinv [-]").
    iApply wp_next_off_intro. iExact "Hcont".
  Qed.

  (* ================================================================== *)
  (* THE ISR ACKNOWLEDGEMENT (VDT+0x1e .. VDT+0x30):                     *)
  (*   *R(INTERRUPT_ACK) = *R(INTERRUPT_STATUS) & 0x3;                   *)
  (*   __sync_synchronize();                                            *)
  (* Five instructions, all under [dev_inv] and nothing else -- the      *)
  (* lock's resource is untouched, so this is a self-contained chunk.    *)
  (* Only a4 and a5 are clobbered.                                      *)
  (* ================================================================== *)
  Lemma wp_vt_isr (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ) (M : regfile) (n : nat) (p : mword 64) :
    sie_cap_gpr M n false p -∗
    kernel_text -∗ pc_is (mword_of_int (VDT + 0x1e) : mword 64) -∗
    dev_inv γu γd -∗
    ( ∀ M' : regfile,
        ⌜ forall r : mword 5, r <> a4_idx -> r <> a5_idx ->
            M' !!! Regidx r = M !!! Regidx r ⌝ -∗
        sie_cap_gpr M' n false p -∗
        pc_is (mword_of_int (VDT + 0x30) : mword 64) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hcg #Htext Hpc #Hdinv Hcont".
    (* ---- +0x1e: lui a5,0x10001 ---- *)
    iPoseProof (vti_1e with "Htext") as "Hi1e".
    iApply (wp_lui_s_sconf Φ (mword_of_int (VDT + 0x1e)) a5_idx
              (mword_of_int 65537 : mword 20) (mword_of_int 0x10001000 : mword 64) M n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B0 := <[Regidx a5_idx := regval_into_reg (mword_of_int 0x10001000 : mword 64)]> M).
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 0x10001000 : mword 64)]> M) with B0.
    assert (Hp22 : add_vec_int (mword_of_int (VDT + 0x1e) : mword 64) 4 = mword_of_int (VDT + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    assert (HB0a5 : B0 !!! Regidx a5_idx = (mword_of_int 0x10001000 : mword 64))
      by (rewrite /B0 upd_eq; reflexivity).
    (* ---- +0x22: c.lw a5,96(a5) -- *R(INTERRUPT_STATUS) ---- *)
    assert (Hea60 : add_vec (rget B0 a5_idx) (sign_extend' 64 (mword_of_int 96 : mword 12))
                    = (mword_of_int 0x10001060 : mword 64)).
    { rgne. rewrite HB0a5. apply bv_eq; vm_compute; reflexivity. }
    assert (Hoff60 : (uint (mword_of_int 0x10001060 : mword 64) - virtio_base)%Z
                     = vio_off_interrupt_status)
      by (vm_compute; reflexivity).
    assert (Hrd60 : forall v : virtio_state, virtio_isr_ok v ->
              exists w : bv 32, virtio_read v vio_off_interrupt_status = Some w /\ True).
    { intros v _. exists (v_isr v). split; [reflexivity | exact I]. }
    iPoseProof (vti_22 with "Htext") as "Hi22".
    iApply (wp_vt_lw_dev γu γd Φ (mword_of_int (VDT + 0x22)) true a5_idx a5_idx
              (mword_of_int 96 : mword 12) B0 n
              (mword_of_int 0x10001060 : mword 64) vio_off_interrupt_status (fun _ => True) p
              Hea60 vg_060 Hoff60
              ltac:(vm_compute; discriminate) ltac:(rdok)
              Hrd60
              with "Hcg Hpc Hi22 Hdinv [-]").
    iIntros (w) "_ Hcg Hpc".
    set (B1 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 (w : mword 32))]> B0).
    change (<[Regidx a5_idx := regval_into_reg (sign_extend' 64 (w : mword 32))]> B0) with B1.
    assert (Hp24 : add_vec_int (mword_of_int (VDT + 0x22) : mword 64) 2 = mword_of_int (VDT + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* ---- +0x24: c.andi a5,3 ---- *)
    iPoseProof (vti_24 with "Htext") as "Hi24".
    iApply (wp_candi_s_sconf Φ (mword_of_int (VDT + 0x24)) a5_idx (mword_of_int 3 : mword 6)
              B1 n false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B2 := <[Regidx a5_idx := regval_into_reg
        (and_vec (B1 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> B1).
    change (<[Regidx a5_idx := regval_into_reg
        (and_vec (B1 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> B1) with B2.
    assert (Hp26 : add_vec_int (mword_of_int (VDT + 0x24) : mword 64) 2 = mword_of_int (VDT + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* ---- +0x26: lui a4,0x10001 ---- *)
    iPoseProof (vti_26 with "Htext") as "Hi26".
    iApply (wp_lui_s_sconf Φ (mword_of_int (VDT + 0x26)) a4_idx
              (mword_of_int 65537 : mword 20) (mword_of_int 0x10001000 : mword 64) B2 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi26 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx a4_idx := regval_into_reg (mword_of_int 0x10001000 : mword 64)]> B2).
    change (<[Regidx a4_idx := regval_into_reg (mword_of_int 0x10001000 : mword 64)]> B2) with B3.
    assert (Hp2a : add_vec_int (mword_of_int (VDT + 0x26) : mword 64) 4 = mword_of_int (VDT + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    assert (HB3a4 : B3 !!! Regidx a4_idx = (mword_of_int 0x10001000 : mword 64))
      by (rewrite /B3 upd_eq; reflexivity).
    (* ---- +0x2a: c.sw a5,100(a4) -- *R(INTERRUPT_ACK) ---- *)
    assert (Hea64 : add_vec (rget B3 a4_idx) (sign_extend' 64 (mword_of_int 100 : mword 12))
                    = (mword_of_int 0x10001064 : mword 64)).
    { rgne. rewrite HB3a4. apply bv_eq; vm_compute; reflexivity. }
    assert (Hoff64 : (uint (mword_of_int 0x10001064 : mword 64) - virtio_base)%Z
                     = vio_off_interrupt_ack)
      by (vm_compute; reflexivity).
    assert (Hwr64 : forall v : virtio_state, virtio_isr_ok v ->
              exists v' : virtio_state,
                virtio_write v vio_off_interrupt_ack (trunc32 (rget B3 a5_idx)) = Some v'
                /\ virtio_isr_ok v'
                /\ v_cfg v' = v_cfg v /\ v_seen v' = v_seen v
                /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v).
    { intros v Hv. exact (virtio_ack_write_ok v _ Hv). }
    iPoseProof (vti_2a with "Htext") as "Hi2a".
    iApply (wp_vt_sw_dev γu γd Φ (mword_of_int (VDT + 0x2a)) true a5_idx a4_idx
              (mword_of_int 100 : mword 12) B3 n
              (mword_of_int 0x10001064 : mword 64) vio_off_interrupt_ack
              (trunc32 (rget B3 a5_idx)) p
              Hea64 vg_064 Hoff64 eq_refl Hwr64
              with "Hcg Hpc Hi2a Hdinv [-]").
    iIntros "Hcg Hpc".
    assert (Hp2c : add_vec_int (mword_of_int (VDT + 0x2a) : mword 64) 2 = mword_of_int (VDT + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* ---- +0x2c: fence rw,rw ---- *)
    iPoseProof (vti_2c with "Htext") as "Hi2c".
    iApply (wp_fence_gen_s_sconf Φ (mword_of_int (VDT + 0x2c))
              (mword_of_int 0) (mword_of_int 3) (mword_of_int 3)
              (Regidx (mword_of_int 0)) (Regidx (mword_of_int 0)) B3 n false
              with "Hcg Hpc Hi2c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hp30 : add_vec_int (mword_of_int (VDT + 0x2c) : mword 64) 4 = mword_of_int (VDT + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    (* ---- the frame: only a4/a5 moved ---- *)
    iApply ("Hcont" $! B3 with "[%] Hcg Hpc").
    intros r N4 N5.
    rewrite /B3 upd_ne; [| congruence].
    rewrite /B2 upd_ne; [| congruence].
    rewrite /B1 upd_ne; [| congruence].
    rewrite /B0 upd_ne; [| congruence]. reflexivity.
  Qed.

End VtLeaves.

(* ===================================================================== *)
(* §1  The prologue and the acquire call (VDT+0x00 .. VDT+0x1e).          *)
(*                                                                        *)
(*     A functor over ACQUIRE only: the 32-byte frame (ra/s0/s1) is the   *)
(*     byte-identical twin of sys_uptime's, then s1 := &disk and          *)
(*     a0 := &disk.vdisk_lock are each materialized by an auipc/addi      *)
(*     pair and [acquire] is called.  What comes out is the whole         *)
(*     critical section's environment: the lock token, [disk_res], the    *)
(*     raised [cpu_own] and its [trap_csrs_pay], the four frame slots     *)
(*     (so the epilogue can restore ra/s0/s1), and the register facts     *)
(*     the body needs (s1 = &disk, sp = the pushed frame, tp = cid, and   *)
(*     every OTHER callee-saved register still holding its entry value).  *)
(* ===================================================================== *)
Module VtPrologue (Acquire : ACQUIRE).
Section VtPrologue.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).

  Lemma wp_vt_prologue (γk : gname) (γd : disk_names) (Φ : mval -> iProp Σ)
      (pd pav pu : mword 64) (m : regfile) (av n : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (b : bool) :
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    (22 <= av)%nat ->
    sie_cap_gpr m av b pme -∗
    cpu_own n eb pme C b -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.virtio_disk_intr : mword 64) -∗
    panic_wp_any -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ (MA : regfile) (sp0 : mword 64),
        ⌜ sp0 = m !!! Regidx csp_rs1
          /\ MA !!! Regidx csp_rs1 = add_vec sp0
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
          /\ MA !!! Regidx s1_idx = (disk_base : mword 64)
          /\ (forall r : mword 5, is_cs_idx r = true ->
                r <> csp_rs1 -> r <> s0_idx -> r <> s1_idx ->
                MA !!! Regidx r = m !!! Regidx r) ⌝ -∗
        sie_cap_gpr MA (av - 4)%nat false pme -∗
        pc_is (mword_of_int (VDT + 0x1e) : mword 64) -∗
        locked γk cpu_id -∗ disk_res γd pd pav pu -∗
        cpu_own (S n) eb pme C false -∗ trap_csrs_pay n eb -∗
        (* the frame: ra/s0/s1's entry values and the unused fourth slot *)
        pa_stk sp0 1 ↦₈ (m !!! Regidx ra_idx) -∗
        pa_stk sp0 2 ↦₈ (m !!! Regidx s0_idx) -∗
        pa_stk sp0 3 ↦₈ (m !!! Regidx s1_idx) -∗
        (∃ vg : mword 64, pa_stk sp0 4 ↦₈ vg) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hn Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hlk Hcont".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    iPoseProof (vti_00 with "Htext") as "Hi00".
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf Φ (mword_of_int KernelSyms.virtio_disk_intr)
              (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (mword_of_int KernelSyms.virtio_disk_intr : mword 64) 2 = mword_of_int (VDT + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02/+0x04/+0x06: c.sdsp ra/s0/s1 *)
    iPoseProof (vti_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VDT + 0x02)) (mword_of_int 3 : mword 6) ra_idx
              A0 (av - 4)%nat vr24 b
              with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (VDT + 0x02) : mword 64) 2 = mword_of_int (VDT + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (vti_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VDT + 0x04)) (mword_of_int 2 : mword 6) s0_idx
              A0 (av - 4)%nat vr16 b
              with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (VDT + 0x04) : mword 64) 2 = mword_of_int (VDT + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (vti_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VDT + 0x06)) (mword_of_int 1 : mword 6) s1_idx
              A0 (av - 4)%nat vr8 b
              with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (VDT + 0x06) : mword 64) 2 = mword_of_int (VDT + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (vti_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (VDT + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) s0_idx A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (VDT + 0x08) : mword 64) 2 = mword_of_int (VDT + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ===================== s1 := &disk ===================== *)
    iPoseProof (vti_0a with "Htext") as "Hi0a".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (VDT + 0x0a)) s1_idx (mword_of_int 30 : mword 20)
              A1 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A2 := <[Regidx s1_idx := regval_into_reg
        (add_vec (mword_of_int (VDT + 0x0a) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> A1).
    change (<[Regidx s1_idx := regval_into_reg
        (add_vec (mword_of_int (VDT + 0x0a) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> A1) with A2.
    assert (Hpc0e : add_vec_int (mword_of_int (VDT + 0x0a) : mword 64) 4 = mword_of_int (VDT + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    iPoseProof (vti_0e with "Htext") as "Hi0e".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (VDT + 0x0e)) s1_idx s1_idx
              (mword_of_int 0xaac : mword 12) A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A3 := <[Regidx s1_idx := regval_into_reg
        (add_vec (A2 !!! Regidx s1_idx) (sign_extend' 64 (mword_of_int 0xaac : mword 12)))]> A2).
    change (<[Regidx s1_idx := regval_into_reg
        (add_vec (A2 !!! Regidx s1_idx) (sign_extend' 64 (mword_of_int 0xaac : mword 12)))]> A2) with A3.
    assert (Hpc12 : add_vec_int (mword_of_int (VDT + 0x0e) : mword 64) 4 = mword_of_int (VDT + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HA3s1 : A3 !!! Regidx s1_idx = (disk_base : mword 64)).
    { rewrite /A3 upd_eq. rewrite /A2 upd_eq.
      unfold disk_base. apply bv_eq; vm_compute; reflexivity. }
    (* ===================== a0 := &disk.vdisk_lock ===================== *)
    iPoseProof (vti_12 with "Htext") as "Hi12".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (VDT + 0x12)) a0_idx (mword_of_int 30 : mword 20)
              A3 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (A4 := <[Regidx a0_idx := regval_into_reg
        (add_vec (mword_of_int (VDT + 0x12) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> A3).
    change (<[Regidx a0_idx := regval_into_reg
        (add_vec (mword_of_int (VDT + 0x12) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> A3) with A4.
    assert (Hpc16 : add_vec_int (mword_of_int (VDT + 0x12) : mword 64) 4 = mword_of_int (VDT + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    iPoseProof (vti_16 with "Htext") as "Hi16".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (VDT + 0x16)) a0_idx a0_idx
              (mword_of_int 0xbcc : mword 12) A4 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A5 := <[Regidx a0_idx := regval_into_reg
        (add_vec (A4 !!! Regidx a0_idx) (sign_extend' 64 (mword_of_int 0xbcc : mword 12)))]> A4).
    change (<[Regidx a0_idx := regval_into_reg
        (add_vec (A4 !!! Regidx a0_idx) (sign_extend' 64 (mword_of_int 0xbcc : mword 12)))]> A4) with A5.
    assert (Hpc1a : add_vec_int (mword_of_int (VDT + 0x16) : mword 64) 4 = mword_of_int (VDT + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ===================== jal acquire ===================== *)
    iPoseProof (vti_1a with "Htext") as "Hi1a".
    iApply (wp_jal_s_sconf Φ (mword_of_int (VDT + 0x1a)) ra_idx (mword_of_int 2077324 : mword 21)
              A5 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (A6 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (VDT + 0x1a) : mword 64) 4)]> A5).
    change (<[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (VDT + 0x1a) : mword 64) 4)]> A5) with A6.
    assert (Hjacq : add_vec (mword_of_int (VDT + 0x1a) : mword 64) (sign_extend' 64 (mword_of_int 2077324 : mword 21))
                    = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    assert (HA6ra : A6 !!! Regidx ra_idx = add_vec_int (mword_of_int (VDT + 0x1a) : mword 64) 4)
      by (rewrite /A6 upd_eq; reflexivity).
    assert (HA6a0 : A6 !!! Regidx a0_idx = (d_lock : mword 64)).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_eq. rewrite /A4 upd_eq.
      unfold d_lock, disk_base. apply bv_eq; vm_compute; reflexivity. }
    assert (HA6csp : A6 !!! Regidx csp_rs1 = spd).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspA0. }
    assert (HA6s1 : A6 !!! Regidx s1_idx = (disk_base : mword 64)).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate]. exact HA3s1. }
    iDestruct (cpu_own_transport CID CID10 n eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf Φ γk "virtio_disk"%string (disk_res γd pd pav pu) A6
              n eb pme C (av - 4)%nat b ltac:(exact Hn) ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlk] Hpanic [-]").
    { iEval (rewrite HA6a0). iExact "Hlk". }
    iIntros (CID11 Hs11 ms MA) "%Hms Hcg Hpc %HcsA Htok HR Hcnt Hpay".
    assert (Hpc1e : ret_pc (A6 !!! Regidx ra_idx) = mword_of_int (VDT + 0x1e))
      by (rewrite HA6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* the register facts the body/epilogue need *)
    assert (HMAcsp : MA !!! Regidx csp_rs1 = spd)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HA6csp).
    assert (HMAs1 : MA !!! Regidx s1_idx = (disk_base : mword 64))
      by (rewrite (callee_saved_lookup HcsA s1_idx ltac:(vm_compute; reflexivity)); exact HA6s1).
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> s0_idx -> r <> s1_idx ->
                     MA !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> ra_idx) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> a0_idx) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /A6 upd_ne; [| congruence].
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    (* hand the frame slots back at their ENTRY values *)
    assert (HraA0 : A0 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx s1_idx = m !!! Regidx s1_idx)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne) in "Hr24". iEval (rewrite HcspA0 HraA0 -Hb1) in "Hr24".
    iEval (rgne) in "Hr16". iEval (rewrite HcspA0 Hs0A0 -Hb2) in "Hr16".
    iEval (rgne) in "Hr8".  iEval (rewrite HcspA0 Hs1A0 -Hb3) in "Hr8".
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! MA sp0 with "[%] Hcg Hpc Htok HR Hcnt Hpay Hr24 Hr16 Hr8 [Hgap]").
    { split_and!; [ reflexivity | exact HMAcsp | exact HMAs1 | exact Hthr ]. }
    { iExists vgap. iEval (rewrite Hspd4 -HcspA0). iExact "Hgap". }
  Qed.

End VtPrologue.
End VtPrologue.

(* ===================================================================== *)
(* §2  The release call and the epilogue (VDT+0x8a .. VDT+0x9e).          *)
(*                                                                        *)
(*     A functor over RELEASE.  a0 := &disk.vdisk_lock again, release,    *)
(*     restore ra/s0/s1, pop the frame, return.  The postcondition is     *)
(*     the whole function's: [callee_saved m MF] and the return pc.       *)
(* ===================================================================== *)
Module VtEpilogue (Release : RELEASE).
Section VtEpilogue.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).

  Lemma wp_vt_epilogue (γk : gname) (γd : disk_names) (Φ : mval -> iProp Σ)
      (pd pav pu : mword 64) (m MB : regfile) (av n : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (sp0 : mword 64) (b : bool) :
    sp0 = m !!! Regidx csp_rs1 ->
    MB !!! Regidx csp_rs1
      = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> s0_idx -> r <> s1_idx ->
       MB !!! Regidx r = m !!! Regidx r) ->
    (22 <= av)%nat ->
    (* release's own exit index; the caller derives it from its entry
       resources ([CpuOwn.cpu_own] / [sie_arm] ghost agreement). *)
    (match n with O => eb | S _ => false end) = b ->
    sie_cap_gpr MB (av - 4)%nat false pme -∗
    kernel_text -∗ pc_is (mword_of_int (VDT + 0x8a) : mword 64) -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    locked γk cpu_id -∗ disk_res γd pd pav pu -∗
    cpu_own (S n) eb pme C false -∗ trap_csrs_pay n eb -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx ra_idx) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx s0_idx) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx s1_idx) -∗
    (∃ vg : mword 64, pa_stk sp0 4 ↦₈ vg) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ MF : regfile,
        ⌜ callee_saved m MF ⌝ -∗
        sie_cap_gpr MF av b pme -∗
        cpu_own n eb pme C b -∗
        pc_is (ret_pc (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hsp0 HMBcsp HMBthr Hav Hbeq.
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg #Htext Hpc #Hlk Htok HR Hcnt Hpay Hr24 Hr16 Hr8 Hgap Hcont".
    iDestruct "Hgap" as (vgap) "Hgap".
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x8a/+0x8e: a0 := &disk.vdisk_lock ---- *)
    iPoseProof (vti_8a with "Htext") as "Hi8a".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (VDT + 0x8a)) a0_idx (mword_of_int 30 : mword 20)
              MB (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E0 := <[Regidx a0_idx := regval_into_reg
        (add_vec (mword_of_int (VDT + 0x8a) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> MB).
    change (<[Regidx a0_idx := regval_into_reg
        (add_vec (mword_of_int (VDT + 0x8a) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> MB) with E0.
    assert (Hpc8e : add_vec_int (mword_of_int (VDT + 0x8a) : mword 64) 4 = mword_of_int (VDT + 0x8e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc8e) in "Hpc".
    iPoseProof (vti_8e with "Htext") as "Hi8e".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (VDT + 0x8e)) a0_idx a0_idx
              (mword_of_int 0xb54 : mword 12) E0 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (E1 := <[Regidx a0_idx := regval_into_reg
        (add_vec (E0 !!! Regidx a0_idx) (sign_extend' 64 (mword_of_int 0xb54 : mword 12)))]> E0).
    change (<[Regidx a0_idx := regval_into_reg
        (add_vec (E0 !!! Regidx a0_idx) (sign_extend' 64 (mword_of_int 0xb54 : mword 12)))]> E0) with E1.
    assert (Hpc92 : add_vec_int (mword_of_int (VDT + 0x8e) : mword 64) 4 = mword_of_int (VDT + 0x92))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc92) in "Hpc".
    (* ---- +0x92: jal ra,release ---- *)
    iPoseProof (vti_92 with "Htext") as "Hi92".
    iApply (wp_jal_s_sconf Φ (mword_of_int (VDT + 0x92)) ra_idx (mword_of_int 2077340 : mword 21)
              E1 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi92 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E2 := <[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (VDT + 0x92) : mword 64) 4)]> E1).
    change (<[Regidx ra_idx := regval_into_reg (add_vec_int (mword_of_int (VDT + 0x92) : mword 64) 4)]> E1) with E2.
    assert (Hjrel : add_vec (mword_of_int (VDT + 0x92) : mword 64) (sign_extend' 64 (mword_of_int 2077340 : mword 21))
                    = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HE2ra : E2 !!! Regidx ra_idx = add_vec_int (mword_of_int (VDT + 0x92) : mword 64) 4)
      by (rewrite /E2 upd_eq; reflexivity).
    assert (HE2a0 : E2 !!! Regidx a0_idx = (d_lock : mword 64)).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq. rewrite /E0 upd_eq.
      unfold d_lock, disk_base. apply bv_eq; vm_compute; reflexivity. }
    assert (HE2csp : E2 !!! Regidx csp_rs1 = spd).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate]. exact HMBcsp. }
    iApply (Release.wp_release_sconf Φ γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) E2
              n eb pme C (av - 4)%nat
              ltac:(rewrite HE2a0; apply addv_sext0) ltac:(lia)
              with "Hcg Htext Hpc [Hlk] [Htok] [HR] Hcnt Hpay [-]").
    { iExact "Hlk". }
    { iExact "Htok". }
    { iExact "HR". }
    iIntros (CID1 Hs1 MR) "Hcg Hpc %HcsR Hcnt".
    rewrite Hbeq in Hs1.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcnt".
    assert (Hpc96 : ret_pc (E2 !!! Regidx ra_idx) = mword_of_int (VDT + 0x96))
      by (rewrite HE2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc96) in "Hpc".
    assert (HMRcsp : MR !!! Regidx csp_rs1 = spd)
      by (rewrite (callee_saved_lookup HcsR csp_rs1 ltac:(vm_compute; reflexivity)); exact HE2csp).
    (* ---- +0x96/+0x98/+0x9a: restore ra/s0/s1 ---- *)
    iPoseProof (vti_96 with "Htext") as "Hi96".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (VDT + 0x96)) (mword_of_int 3 : mword 6) ra_idx
              MR (av - 4)%nat (m !!! Regidx ra_idx) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi96 [Hr24] [-]").
    { iEval (rewrite HMRcsp -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    set (E3 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> MR).
    change (<[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> MR) with E3.
    assert (Hpc98 : add_vec_int (mword_of_int (VDT + 0x96) : mword 64) 2 = mword_of_int (VDT + 0x98))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc98) in "Hpc".
    assert (HE3csp : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HMRcsp | vm_compute; discriminate]).
    iPoseProof (vti_98 with "Htext") as "Hi98".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (VDT + 0x98)) (mword_of_int 2 : mword 6) s0_idx
              E3 (av - 4)%nat (m !!! Regidx s0_idx) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi98 [Hr16] [-]").
    { iEval (rewrite HE3csp -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    set (E4 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> E3).
    change (<[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> E3) with E4.
    assert (Hpc9a : add_vec_int (mword_of_int (VDT + 0x98) : mword 64) 2 = mword_of_int (VDT + 0x9a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc9a) in "Hpc".
    assert (HE4csp : E4 !!! Regidx csp_rs1 = spd)
      by (rewrite /E4 upd_ne; [exact HE3csp | vm_compute; discriminate]).
    iPoseProof (vti_9a with "Htext") as "Hi9a".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (VDT + 0x9a)) (mword_of_int 1 : mword 6) s1_idx
              E4 (av - 4)%nat (m !!! Regidx s1_idx) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9a [Hr8] [-]").
    { iEval (rewrite HE4csp -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    set (E5 := <[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]> E4).
    change (<[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]> E4) with E5.
    assert (Hpc9c : add_vec_int (mword_of_int (VDT + 0x9a) : mword 64) 2 = mword_of_int (VDT + 0x9c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc9c) in "Hpc".
    (* ---- +0x9c: c.addi16sp sp,32 -- the frame pop ---- *)
    assert (HE5csp : E5 !!! Regidx csp_rs1 = spd)
      by (rewrite /E5 upd_ne; [exact HE4csp | vm_compute; discriminate]).
    set (E6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E5).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spd po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (Hwv : add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE5csp. exact Hsp0up. }
    assert (HE6sp : E6 !!! Regidx csp_rs1 = sp0).
    { rewrite /E6 upd_eq. exact Hwv. }
    assert (Hpop : E5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE5csp. symmetry. exact Hspd4. }
    iPoseProof (vti_9c with "Htext") as "Hi9c".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HE3csp). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HE4csp). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HE5csp). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (VDT + 0x9c)) (mword_of_int 2 : mword 6)
              E5 (av - 4)%nat 4 b Hpop with "Hcg Hpc Hi9c Hframe4 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E5) with E6.
    assert (Hpc9e : add_vec_int (mword_of_int (VDT + 0x9c) : mword 64) 2 = mword_of_int (VDT + 0x9e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc9e) in "Hpc".
    (* ---- +0x9e: c.ret ---- *)
    assert (HE6ra : E6 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3. apply upd_eq. }
    iPoseProof (vti_9e with "Htext") as "Hi9e".
    iApply (wp_cret_s_sconf Φ (mword_of_int (VDT + 0x9e)) ra_idx E6 av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi9e [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hpc". iEval (rewrite HE6ra) in "Hpc".
    (* ---- the callee-saved postcondition ---- *)
    assert (HE6s0 : E6 !!! Regidx s0_idx = m !!! Regidx s0_idx).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4. apply upd_eq. }
    assert (HE6s1 : E6 !!! Regidx s1_idx = m !!! Regidx s1_idx).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5. apply upd_eq. }
    assert (HE6csp : E6 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite HE6sp Hsp0; reflexivity).
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> s0_idx -> r <> s1_idx ->
                     E6 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> ra_idx) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> a0_idx) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E6 upd_ne; [| congruence].
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsR r Hr).
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      exact (HMBthr r Hr Ncsp N8 N9). }
    iDestruct (cpu_own_transport CID1 CID6 n eb pme C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E6 with "[%] Hcg Hcnt Hpc").
    unfold callee_saved.
    split; [exact HE6csp|].
    split; [exact HE6s0|].
    split; [exact HE6s1|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End VtEpilogue.
End VtEpilogue.

(* ===================================================================== *)
(* §3  Seams for the LOOP region (+0x30 .. +0x86), which is not yet       *)
(*     proved.  Two things the loop needs that nothing else provides:     *)
(*                                                                        *)
(*  (a) [disk_res_at] -- [DiskInv.disk_res] with its six existentials     *)
(*      NAMED.  The loop carries the destructured form across iterations  *)
(*      (its [nr] moves, its [fl]/[pk] move one position from flight to   *)
(*      parked), so the invariant cannot be the packed [disk_res].        *)
(*      Kept HERE, not in DiskInv.v, because virtio_disk_rw owns that     *)
(*      file; if rw ends up wanting the same split, promote it there.     *)
(*                                                                        *)
(*  (b) the queue pages' word-alignment, which is what turns the          *)
(*      protocol's byte-granular [phys_word2]/[phys_word4] back into the  *)
(*      [↦₂]/[↦₄] the memory leaves consume ([DiskInv.phys_to_word2] /    *)
(*      [phys_to_word4] take it as a premise).  It is a consequence of    *)
(*      [virtio_pages_aligned] alone, stated mword-free so [lia] works    *)
(*      (durable-notes' zify gotcha).                                     *)
(* ===================================================================== *)

(* RESTATEMENTS of [DiskInv]'s family (it moved there: the queue pages'
   geometry, cloned by three files).  Local names kept, so no call site
   below changed. *)

Lemma vt_wrap_off (x k : Z) :
  0 <= x -> x < 18446744073709551616 -> x mod 4096 = 0 ->
  0 <= k -> k < 4096 ->
  (x + k) mod 18446744073709551616 = x + k.
Proof. exact (pa_wrap_in_page x k). Qed.

Lemma vt_rem_off (x k d : Z) :
  0 <= x -> x < 18446744073709551616 -> x mod 4096 = 0 ->
  0 <= k -> k < 4096 -> 0 < d -> 4096 mod d = 0 -> k mod d = 0 ->
  Z.rem ((x + k) mod 18446744073709551616) d = 0.
Proof. exact (pa_rem_in_page x k d). Qed.

(* an offset [k] into a 4096-aligned page is [d]-aligned whenever [d] divides
   4096 and [k]: exactly the premise [phys_to_word2]/[phys_to_word4] want. *)
Lemma vt_aligned_off (p : Arch.pa) (k : nat) (d : Z) :
  bv_unsigned (p : SailStdpp.Values.mword 64) `mod` 4096 = 0 ->
  (Z.of_nat k < 4096)%Z -> (0 < d)%Z -> (4096 mod d = 0)%Z ->
  (Z.of_nat k mod d = 0)%Z ->
  is_aligned_paddr (Physaddr (pa_add p k)) d = true.
Proof. exact (pa_add_aligned_in_page p k d). Qed.

Section VtLoopSeam.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  (* [DiskInv.disk_res]'s body with the six existentials named. *)
  Definition disk_res_at (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64)
      (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) : iProp Σ :=
    (⌜dom fl = set_seq nr (np - nr)⌝ ∗
     ⌜forall p, p ∈ dom pk -> (p < nr)%nat⌝ ∗
     ⌜dom tr = dom fl ∪ dom pk⌝ ∗
     ⌜forall p v, (fl ∪ pk) !! p = Some v -> tr !! p = Some (dc_tri v)⌝ ∗
     ⌜forall p T, tr !! p = Some T -> tri_ok T⌝ ∗
     ⌜forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
        tri_set Tp ## tri_set Tq⌝ ∗
     ⌜forall p T i, tr !! p = Some T -> i ∈ tri_set T -> fr i = false⌝ ∗
     disk_pub γ np ∗
     disk_done_lb γ nr ∗
     ghost_map_auth (dn_claim γ) 1 (fl ∪ pk) ∗
     d_used_idx ↦₂ wrap16 nr ∗
     ([∗ map] p ↦ v ∈ fl, flight_res γ p v) ∗
     ([∗ map] p ↦ v ∈ pk, parked_res γ pav p v) ∗
     free_bundles pd fr ∗
     ring_slots_res pav (mod8 (dom fl)))%I.

  Lemma disk_res_at_elim (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64) :
    disk_res γ pd pav pu -∗
    ∃ (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool),
      disk_res_at γ pd pav pu np nr fl pk tr fr.
  Proof.
    iIntros "H". rewrite /disk_res.
    iDestruct "H" as (np nr fl pk tr fr) "H".
    iExists np, nr, fl, pk, tr, fr. rewrite /disk_res_at /free_bundles. iExact "H".
  Qed.

  Lemma disk_res_at_intro (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64)
      (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) :
    disk_res_at γ pd pav pu np nr fl pk tr fr -∗ disk_res γ pd pav pu.
  Proof.
    iIntros "H". rewrite /disk_res.
    iEval (rewrite /disk_res_at /free_bundles) in "H".
    iExists np, nr, fl, pk, tr, fr. iExact "H".
  Qed.

  (* THE loop invariant's ghost content, at the loop head VDT+0x3e: the
     destructured lock resource plus the observation that carried the thread
     into the body -- the device is provably PAST the driver's [nr], which is
     [VirtioProto.virtio_proto_reclaim_acc]'s premise at [p := nr]. *)
  Definition vt_loop_state (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64)
    : iProp Σ :=
    (∃ (np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) (c : nat),
       ⌜(nr < c)%nat /\ (c <= np)%nat⌝ ∗ disk_done_lb γ c ∗
       disk_res_at γ pd pav pu np nr fl pk tr fr)%I.

  Lemma vt_loop_state_close (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64) :
    vt_loop_state γ pd pav pu -∗ disk_res γ pd pav pu.
  Proof.
    iIntros "H". iDestruct "H" as (np nr fl pk tr fr c) "(_ & _ & H)".
    iApply (disk_res_at_intro with "H").
  Qed.

  (* the flight entry the body consumes: [nr] is in the window whenever the
     device is ahead of it, because [dom fl] is exactly [nr, np). *)
  Lemma vt_flight_at_nr {A : Type} (np nr c : nat) (fl : gmap nat A) :
    dom fl = set_seq nr (np - nr) ->
    (nr < c)%nat -> (c <= np)%nat ->
    exists v : A, fl !! nr = Some v.
  Proof.
    intros Hdom Hlt Hle.
    assert (Hin : nr ∈ dom fl).
    { rewrite Hdom. apply elem_of_set_seq. lia. }
    apply elem_of_dom in Hin. destruct Hin as [b Hb]. exists b. exact Hb.
  Qed.

End VtLoopSeam.

(* ===================================================================== *)
(* §4  The two dev_inv-OPENING RAM leaves of the loop.                    *)
(*                                                                        *)
(*     The used ring lives in the DMA lease, so its bytes are reachable   *)
(*     only through [VirtioProto]'s accessors, which run inside the       *)
(*     device invariant.  Both loads are therefore ATOMIC-UPDATE leaves   *)
(*     ([WpSconfMem.wp_load_s_sconf_au], the [WpSconfLock] pattern) that  *)
(*     open [dev_inv] across the one memory step, and both have to cross  *)
(*     the tier boundary twice: the accessor hands out [phys_word2] /     *)
(*     [phys_word4] (byte-granular, PHYSICAL) and the leaf consumes       *)
(*     [wordw_pointsto] (aligned, VA tier), so [DiskInv.phys_to_word*] /  *)
(*     [word*_to_phys] bracket the access.  The alignment premise comes   *)
(*     from [virtio_pages_aligned] via [vt_aligned_off]; the static/      *)
(*     canonical premises from [disk_geom_static]/[_canonical]; and the   *)
(*     claims bundle off the threaded [sie_cap_gpr]                       *)
(*     ([IntrDefs.sie_cap_gpr_kmap_claims]).                              *)
(*                                                                        *)
(*     [disk_cfg_agree] is what makes the accessor's address the one the  *)
(*     CODE computes: it pins [v_cfg v = virtio_init_cfg pd pav pu], so   *)
(*     [used_idx_pa (v_cfg v)] IS [pa_add pu 2].                          *)
(* ===================================================================== *)

(* the byte offset of used-ring element [p] inside the used page: the
   accessors' [used_elem_pa] with the config's [vc_used] peeled off. *)
Definition vt_uoff (p : nat) : nat :=
  Z.to_nat (vq_used_ring_off + vq_used_elem_size * (Z.of_nat p `mod` 8)).

Lemma vt_uoff_z (p : nat) :
  Z.of_nat (vt_uoff p) = (4 + 8 * (Z.of_nat p `mod` 8))%Z.
Proof.
  unfold vt_uoff, vq_used_ring_off, vq_used_elem_size.
  rewrite Z2Nat.id; [reflexivity|].
  pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)). lia.
Qed.

Lemma vt_uoff_le (p : nat) : (vt_uoff p <= 60)%nat.
Proof.
  pose proof (vt_uoff_z p) as Hz.
  pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)). lia.
Qed.

Lemma vt_uoff_lt (p : nat) : (vt_uoff p < 4096)%nat.
Proof. pose proof (vt_uoff_le p). lia. Qed.

Lemma vt_uoff_lt_z (p : nat) : (Z.of_nat (vt_uoff p) < 4096)%Z.
Proof. pose proof (vt_uoff_lt p). lia. Qed.

Lemma vt_uoff_add_lt (p j : nat) : (j < 4)%nat -> (vt_uoff p + j < 4096)%nat.
Proof. intro Hj. pose proof (vt_uoff_le p). lia. Qed.

Lemma vt_two_add_lt (j : nat) : (j < 2)%nat -> (2 + j < 4096)%nat.
Proof. intro Hj. lia. Qed.

Lemma vt_zero_lt_4096 : (0 < 4096)%nat.
Proof. lia. Qed.

Lemma vt_uoff_mod4 (p : nat) : (Z.of_nat (vt_uoff p) mod 4 = 0)%Z.
Proof.
  rewrite vt_uoff_z.
  replace (4 + 8 * (Z.of_nat p `mod` 8))%Z with ((1 + 2 * (Z.of_nat p `mod` 8)) * 4)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Section VtDevRam.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the used-ring INDEX read: [lhu a5,2(a5)] at +0x36 and [lhu a4,2(a4)]
     at +0x82.  Drives [virtio_proto_used_idx_acc]; the value is the
     device's completed count, and what survives is the pair of bounds
     [nr <= nc <= np] plus the persistent lower bound at [nc] -- which is
     exactly the evidence the reclaim accessor wants. *)
  Lemma wp_vt_lhu_used_idx (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ) (pd pav pu : mword 64)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (np nr : nat) (p : mword 64) :
    add_vec (rget m rs1) (sign_extend' 64 imm) = (pa_add pu 2%nat : mword 64) ->
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n false p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 2)) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    disk_pub γd np -∗ disk_done_lb γd nr -∗
    ( ∀ nc : nat,
        ⌜(nr <= nc)%nat /\ (nc <= np)%nat⌝ -∗
        disk_done_lb γd nc -∗ disk_pub γd np -∗
        sie_cap_gpr (<[Regidx rd := regval_into_reg (zero_extend' 64 (wrap16 nc : SailStdpp.Values.mword 16))]> m) n false p -∗
        pc_is (add_vec_int pc 4) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hea Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr #Hdinv #Hgeom Hpub #Hlb0 Hcont".
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    iDestruct (disk_geom_static with "Hgeom") as %(_ & _ & Hstu).
    iDestruct (disk_geom_canonical with "Hgeom") as %(_ & _ & Hcanu).
    iDestruct "Hgeom" as "(_ & _ & _ & %Hal0 & #Hcfg0 & _ & _ & _)".
    destruct Hal0 as (_ & _ & Halu).
    (* the two constant side conditions of the tier bridge at [pu + 2] *)
    assert (Halign : is_aligned_paddr (Physaddr (pa_add pu 2%nat)) 2 = true).
    { apply (vt_aligned_off pu 2%nat 2 Halu);
        [ reflexivity | reflexivity | reflexivity | reflexivity ]. }
    assert (Hst2 : forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add (pa_add pu 2%nat) j)) KP_rw).
    { intros j Hj. rewrite pa_add_add. exact (Hstu (2 + j)%nat (vt_two_add_lt j Hj)). }
    assert (Hcan2 : forall j, (j < 2)%nat ->
              (uint (pa_add (pa_add pu 2%nat) j : SailStdpp.Values.mword 64) < 274877906944)%Z).
    { intros j Hj. rewrite pa_add_add. exact (Hcanu (2 + j)%nat (vt_two_add_lt j Hj)). }
    iApply (wp_load_s_sconf_au (CID:=CID) 2 false true Φ pc rd rs1 imm m n
              (fun w => zero_extend' 64 w)
              (fun w => (∃ nc : nat, ⌜w = wrap16 nc⌝ ∗
                          ⌜(nr <= nc)%nat /\ (nc <= np)%nat⌝ ∗
                          disk_done_lb γd nc ∗ disk_pub γd np)%I)
              (⊤ ∖ ↑minstretN ∖ ↑diskN) false (dqm := DfracOwn 1)
              ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_2 data2_ext_2_unsigned Hrd Hrdok
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [Hpub] [Hcont]").
    { (* ---- the atomic update: open dev_inv, run the accessor ---- *)
      iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
      iInv "Hvinv" as ">Hdbody" "Hdclose".
      iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
      iDestruct (virtio_proto_used_idx_acc γd vst np nr with "Hproto Hpub Hlb0")
        as (nc) "(%Hnrnc & %Hncnp & #Hcfgv & %Halv & #Hlbc & Hw2 & Hback)".
      iDestruct (disk_cfg_agree with "Hcfgv Hcfg0") as %Hceq.
      assert (Haddr : used_idx_pa (v_cfg vst) = pa_add pu 2%nat)
        by (rewrite Hceq; reflexivity).
      iEval (rewrite Haddr) in "Hw2".
      iDestruct (phys_to_word2 (pa_add pu 2%nat) (wrap16 nc) Halign Hst2 Hcan2
                   with "Hkm Hw2") as "Hcell".
      iModIntro. iExists (wrap16 nc : SailStdpp.Values.mword 16).
      iSplitL "Hcell".
      { rewrite Hea. iExact "Hcell". }
      iIntros "Hcell". iEval (rewrite Hea) in "Hcell".
      iDestruct (word2_to_phys (pa_add pu 2%nat) (wrap16 nc) Hst2 with "Hkm Hcell") as "Hw2".
      iEval (rewrite -Haddr) in "Hw2".
      iDestruct ("Hback" with "Hw2") as "[Hproto Hpub]".
      iMod ("Hdclose" with "[Hvf Hproto]") as "_".
      { iNext. iExists vst. iFrame. iPureIntro. exact Hvok. }
      iModIntro. iExists nc. iFrame "Hlbc Hpub".
      iSplitR; [done|]. iPureIntro. split; [exact Hnrnc | exact Hncnp]. }
    iIntros (w). iApply wp_next_off_intro. iIntros "Hcg Hpc Hpost".
    iDestruct "Hpost" as (nc) "(-> & %Hb & #Hlbc & Hpub)".
    iApply ("Hcont" $! nc with "[%] Hlbc Hpub Hcg Hpc"). exact Hb.
  Qed.


  (* the used-ring ELEMENT read: [c.lw a5,4(a5)] at +0x4e.  Drives
     [virtio_proto_reclaim_acc] at [p := nr]: the receipt plus the lower
     bound [p < c] buy the loaded id (= the chain's head descriptor) AND the
     whole payoff -- the pin bytes back, the status byte pinned at 0 (which
     is what refutes the status panic two instructions later), the buffer and
     the disk fragments.

     [virtio_proto_reclaim_acc] exports the [disk_cfg] witness, so
     [disk_cfg_agree] against [disk_geom]'s copy pins [v_cfg v] and makes
     [used_elem_pa (v_cfg v) p] the very address the code computes off
     [disk.used]. *)
  Lemma wp_vt_lw_used_elem (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ) (pd pav pu : mword 64)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (np c p : nat) (sl : vslot) (pin : _)
      (pp : mword 64) :
    (p < c)%nat ->
    add_vec (rget m rs1) (sign_extend' 64 imm)
      = (pa_add pu (vt_uoff p) : SailStdpp.Values.mword 64) ->
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n false pp -∗ pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    disk_pub γd np -∗ disk_receipt γd p sl pin -∗ disk_done_lb γd c -∗
    ( ⌜ slot_pin_ok (virtio_init_cfg pd pav pu) p sl pin ⌝ -∗
      sie_cap_gpr (<[Regidx rd := regval_into_reg
          (sign_extend' 64 (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))
                            : SailStdpp.Values.mword 32))]> m) n false pp -∗
      pc_is (add_vec_int pc 2) -∗
      disk_pub γd np -∗ disk_done_lb γd (S p) -∗
      phys_map pin -∗
      phys_pointsto (vr_status (vs_req sl)) (DfracOwn 1) byte_zero -∗
      (* the SPENT crash permit's token rides WITH the payoff, on its way
         from the completed slot to [DiskInv.parked_res] (PermInv.v) *)
      (perm_done (dn_perm γd) (vs_perm sl) ∗
       ∃ bs : list (bv 8),
         ⌜length bs = vs_len sl⌝ ∗
         ⌜bs = vs_data sl⌝ ∗
         disk_bytes γd (vs_sector_off sl) bs ∗
         (if vs_is_out sl then emp else phys_list (vr_buf (vs_req sl)) bs)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hpc0 Hea Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr #Hdinv #Hgeom Hpub Hrcpt #Hlbc Hcont".
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    iDestruct (disk_geom_static with "Hgeom") as %(_ & _ & Hstu).
    iDestruct (disk_geom_canonical with "Hgeom") as %(_ & _ & Hcanu).
    iDestruct "Hgeom" as "(_ & _ & _ & %Hal0 & #Hcfg0 & _ & _ & _)".
    destruct Hal0 as (_ & _ & Halu).
    assert (Halign : is_aligned_paddr (Physaddr (pa_add pu (vt_uoff p))) 4 = true).
    { apply (vt_aligned_off pu (vt_uoff p) 4 Halu);
        [ exact (vt_uoff_lt_z p) | reflexivity | reflexivity | exact (vt_uoff_mod4 p) ]. }
    assert (Hst4 : forall j, (j < 4)%nat ->
              kmap_static (svpn_of (pa_add (pa_add pu (vt_uoff p)) j)) KP_rw).
    { intros j Hj. rewrite pa_add_add.
      exact (Hstu (vt_uoff p + j)%nat (vt_uoff_add_lt p j Hj)). }
    assert (Hcan4 : forall j, (j < 4)%nat ->
              (uint (pa_add (pa_add pu (vt_uoff p)) j : SailStdpp.Values.mword 64) < 274877906944)%Z).
    { intros j Hj. rewrite pa_add_add.
      exact (Hcanu (vt_uoff p + j)%nat (vt_uoff_add_lt p j Hj)). }
    iApply (wp_load_s_sconf_au (CID:=CID) 4 true false Φ pc rd rs1 imm m n
              (fun w => sign_extend' 64 w)
              (fun w => (⌜w = (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))
                               : SailStdpp.Values.mword 32)⌝ ∗
                         ⌜slot_pin_ok (virtio_init_cfg pd pav pu) p sl pin⌝ ∗
                         disk_pub γd np ∗ disk_done_lb γd (S p) ∗
                         phys_map pin ∗
                         phys_pointsto (vr_status (vs_req sl)) (DfracOwn 1) byte_zero ∗
                         (perm_done (dn_perm γd) (vs_perm sl) ∗
                          ∃ bs : list (bv 8),
                            ⌜length bs = vs_len sl⌝ ∗
                            ⌜bs = vs_data sl⌝ ∗
                            disk_bytes γd (vs_sector_off sl) bs ∗
                            (if vs_is_out sl then emp
                             else phys_list (vr_buf (vs_req sl)) bs)))%I)
              (⊤ ∖ ↑minstretN ∖ ↑diskN) false (dqm := DfracOwn 1)
              ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [Hpub Hrcpt] [Hcont]").
    { iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
      iInv "Hvinv" as ">Hdbody" "Hdclose".
      iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
      iDestruct (virtio_proto_reclaim_acc γd vst np c p sl pin Hpc0
                   with "Hproto Hpub Hrcpt Hlbc")
        as "(_ & #Hcfgv & _ & %Hspo & Hw4 & Hback)".
      iDestruct (disk_cfg_agree with "Hcfgv Hcfg0") as %Hceq.
      assert (Haddr : (pa_add pu (vt_uoff p) : Arch.pa) = used_elem_pa (v_cfg vst) p).
      { rewrite Hceq. reflexivity. }
      rewrite Haddr in Halign Hst4 Hcan4.
      iDestruct (phys_to_word4 (used_elem_pa (v_cfg vst) p)
                   (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl))))
                   Halign Hst4 Hcan4 with "Hkm Hw4") as "Hcell".
      iModIntro.
      iExists (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl))) : SailStdpp.Values.mword 32).
      iSplitL "Hcell". { rewrite Hea Haddr. iExact "Hcell". }
      iIntros "Hcell". iEval (rewrite Hea Haddr) in "Hcell".
      iDestruct (word4_to_phys (used_elem_pa (v_cfg vst) p)
                   (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) Hst4
                   with "Hkm Hcell") as "Hw4".
      iMod ("Hback" with "Hw4") as "(Hproto & Hpub & #Hlbs & Hpin & Hstat & Hrest)".
      iMod ("Hdclose" with "[Hvf Hproto]") as "_".
      { iNext. iExists vst. iFrame. iPureIntro. exact Hvok. }
      iModIntro. iFrame "Hpub Hlbs Hpin Hstat Hrest".
      iSplitR; [done|]. iPureIntro. rewrite -Hceq. exact Hspo. }
    iIntros (w). iApply wp_next_off_intro.
    iIntros "Hcg Hpc (-> & %Hspo & Hpub & #Hlbs & Hpin & Hstat & Hrest)".
    iApply ("Hcont" with "[%] Hcg Hpc Hpub Hlbs Hpin Hstat Hrest"). exact Hspo.
  Qed.


  (* the two 12-bit displacements the loop head uses, as plain 64-bit words *)
  Lemma vt_sext_2  : sign_extend' 64 (mword_of_int 2 : mword 12) = (mword_of_int 2 : mword 64).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma vt_sext_16 : sign_extend' 64 (mword_of_int 16 : mword 12) = (mword_of_int 16 : mword 64).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma vt_sext_32 : sign_extend' 64 (mword_of_int 32 : mword 12) = (mword_of_int 32 : mword 64).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma vt_zext16_unsigned (x : SailStdpp.Values.mword 16) :
    bv_unsigned (zero_extend' 64 x : SailStdpp.Values.mword 64) = bv_unsigned x.
  Proof.
    cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
         Values.to_word get_word MachineWord.MachineWord.zero_extend].
    rewrite bv_zero_extend_unsigned. reflexivity.
    first [ lia | vm_compute; discriminate | done ].
  Qed.

  (* the loop test compares two ZERO-EXTENDED 16-bit counters, so a
     disequality of the counters is a disequality of the registers.  (Only
     this direction is ever needed: on EQUAL registers the loop simply
     exits, which is sound at any pair of counters -- a missed completion is
     a liveness loss the spec promises nothing about.) *)
  Lemma vt_zext16_inj (a b : SailStdpp.Values.mword 16) :
    (zero_extend' 64 a : SailStdpp.Values.mword 64) = zero_extend' 64 b -> a = b.
  Proof.
    intro He. apply bv_eq.
    rewrite <- (vt_zext16_unsigned a), <- (vt_zext16_unsigned b), He. reflexivity.
  Qed.

  (* ================================================================== *)
  (* (a) THE LOOP-ENTRY TEST (VDT+0x30 .. VDT+0x3a):                     *)
  (*       while (disk.used_idx != disk.used->idx)                       *)
  (*     Reads [disk.used] (the persistent geometry cell), the driver's  *)
  (*     [disk.used_idx] (a plain owned halfword out of [disk_res]) and  *)
  (*     the device's [used->idx] (the dev_inv-opening leaf), then       *)
  (*     branches.  The two arms are offered as an ADDITIVE conjunction  *)
  (*     so both see the same resources; the ENTER arm additionally      *)
  (*     learns [nr < nc], which is [virtio_proto_reclaim_acc]'s premise *)
  (*     at [p := nr]:  [nr <= nc] comes from the accessor and [nc <> nr] *)
  (*     from the branch, by plain congruence on [wrap16].               *)
  (* ================================================================== *)
  Lemma wp_vt_entry_test (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ) (pd pav pu : mword 64) (M : regfile) (n : nat)
      (np nr : nat) (p : mword 64) :
    (M !!! Regidx (mword_of_int 9 : mword 5) : mword 64) = (disk_base : mword 64) ->
    sie_cap_gpr M n false p -∗
    kernel_text -∗ pc_is (mword_of_int (VDT + 0x30) : mword 64) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    disk_pub γd np -∗ disk_done_lb γd nr -∗ d_used_idx ↦₂ wrap16 nr -∗
    ( ( ∀ M' : regfile,
          ⌜ forall r : mword 5, r <> mword_of_int 14 -> r <> mword_of_int 15 ->
              M' !!! Regidx r = M !!! Regidx r ⌝ -∗
          sie_cap_gpr M' n false p -∗
          pc_is (mword_of_int (VDT + 0x8a) : mword 64) -∗
          disk_pub γd np -∗ d_used_idx ↦₂ wrap16 nr -∗
          WP (Loop : expr riscv_lang) {{ Φ }})
      ∧ ( ∀ (M' : regfile) (nc : nat),
          ⌜ forall r : mword 5, r <> mword_of_int 14 -> r <> mword_of_int 15 ->
              M' !!! Regidx r = M !!! Regidx r ⌝ -∗
          ⌜ (nr < nc)%nat /\ (nc <= np)%nat ⌝ -∗
          disk_done_lb γd nc -∗
          sie_cap_gpr M' n false p -∗
          pc_is (mword_of_int (VDT + 0x3e) : mword 64) -∗
          disk_pub γd np -∗ d_used_idx ↦₂ wrap16 nr -∗
          WP (Loop : expr riscv_lang) {{ Φ }}) ) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HMs1.
    iIntros "Hcg #Htext Hpc #Hdinv #Hgeom Hpub #Hlb0 Hidx Hcont".
    iDestruct "Hgeom" as "#Hgeomc". iPoseProof "Hgeomc" as "(_ & _ & #Hup & _)".
    (* ---- +0x30: c.ld a5,16(s1) -- a5 := disk.used ---- *)
    assert (Hup : add_vec (rget M (mword_of_int 9 : mword 5))
                    (sign_extend' 64 (mword_of_int 16 : mword 12)) = (d_used_ptr : mword 64)).
    { rgne. rewrite HMs1 vt_sext_16. reflexivity. }
    iPoseProof (vti_30 with "Htext") as "Hi30".
    iApply (wp_cld_s_sconf Φ (mword_of_int (VDT + 0x30)) (mword_of_int 15 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 16 : mword 12) M n pu false
              (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [] [-]").
    { iEval (rewrite Hup). iExact "Hup". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (C0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg pu]> M).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg pu]> M) with C0.
    assert (Hp32 : add_vec_int (mword_of_int (VDT + 0x30) : mword 64) 2 = mword_of_int (VDT + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    assert (HC0s1 : C0 !!! Regidx (mword_of_int 9 : mword 5) = (disk_base : mword 64))
      by (rewrite /C0 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    (* ---- +0x32: lhu a4,32(s1) -- a4 := disk.used_idx ---- *)
    assert (Huidx : add_vec (rget C0 (mword_of_int 9 : mword 5))
                      (sign_extend' 64 (mword_of_int 32 : mword 12)) = (d_used_idx : mword 64)).
    { rgne. rewrite HC0s1 vt_sext_32. reflexivity. }
    iPoseProof (vti_32 with "Htext") as "Hi32".
    iApply (wp_lhu_s_sconf Φ (mword_of_int (VDT + 0x32)) (mword_of_int 14 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 32 : mword 12) C0 n (wrap16 nr) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [Hidx] [-]").
    { iEval (rewrite Huidx). iExact "Hidx". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hidx". iEval (rewrite Huidx) in "Hidx".
    set (C1 := <[Regidx (mword_of_int 14 : mword 5) :=
        regval_into_reg (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))]> C0).
    change (<[Regidx (mword_of_int 14 : mword 5) :=
        regval_into_reg (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))]> C0) with C1.
    assert (Hp36 : add_vec_int (mword_of_int (VDT + 0x32) : mword 64) 4 = mword_of_int (VDT + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    assert (HC1a5 : C1 !!! Regidx (mword_of_int 15 : mword 5) = pu).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0. apply upd_eq. }
    (* ---- +0x36: lhu a5,2(a5) -- a5 := disk.used->idx ---- *)
    assert (Hued : add_vec (rget C1 (mword_of_int 15 : mword 5))
                     (sign_extend' 64 (mword_of_int 2 : mword 12))
                   = (pa_add pu 2%nat : SailStdpp.Values.mword 64)).
    { rgne. rewrite HC1a5 vt_sext_2. reflexivity. }
    iPoseProof (vti_36 with "Htext") as "Hi36".
    iApply (wp_vt_lhu_used_idx γu γd Φ pd pav pu (mword_of_int (VDT + 0x36))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 2 : mword 12) C1 n np nr p Hued
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 Hdinv Hgeomc Hpub Hlb0 [-]").
    iIntros (nc) "%Hbnd #Hlbc Hpub Hcg Hpc".
    set (C2 := <[Regidx (mword_of_int 15 : mword 5) :=
        regval_into_reg (zero_extend' 64 (wrap16 nc : SailStdpp.Values.mword 16))]> C1).
    change (<[Regidx (mword_of_int 15 : mword 5) :=
        regval_into_reg (zero_extend' 64 (wrap16 nc : SailStdpp.Values.mword 16))]> C1) with C2.
    assert (Hp3a : add_vec_int (mword_of_int (VDT + 0x36) : mword 64) 4 = mword_of_int (VDT + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    assert (HC2a4 : C2 !!! Regidx (mword_of_int 14 : mword 5)
                    = zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16)).
    { rewrite /C2 upd_ne; [| vm_compute; discriminate]. rewrite /C1. apply upd_eq. }
    assert (HC2a5 : C2 !!! Regidx (mword_of_int 15 : mword 5)
                    = zero_extend' 64 (wrap16 nc : SailStdpp.Values.mword 16))
      by (rewrite /C2; apply upd_eq).
    assert (HC2thr : forall r : mword 5, r <> mword_of_int 14 -> r <> mword_of_int 15 ->
                       C2 !!! Regidx r = M !!! Regidx r).
    { intros r N4 N5.
      rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence].
      rewrite /C0 upd_ne; [| congruence]. reflexivity. }
    (* ---- +0x3a: beq a4,a5 -- the loop test ---- *)
    iPoseProof (vti_3a with "Htext") as "Hi3a".
    destruct (decide ((wrap16 nc : SailStdpp.Values.mword 16) = wrap16 nr)) as [Heq|Hne].
    - (* the wraps agree: EXIT (sound at any counters -- see vt_zext16_inj) *)
      iDestruct "Hcont" as "[Hexit _]".
      assert (Hcmp : eq_vec (rget C2 (mword_of_int 14 : mword 5))
                            (rget C2 (mword_of_int 15 : mword 5)) = true).
      { rgne. rgne. rewrite HC2a4 HC2a5 Heq. apply eq_vec_true_iff. reflexivity. }
      iApply (wp_beq_taken_s_sconf Φ (mword_of_int (VDT + 0x3a))
                (mword_of_int 80 : mword 13) (mword_of_int 15 : mword 5)
                (mword_of_int 14 : mword 5) C2 n false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp8a : add_vec (mword_of_int (VDT + 0x3a) : mword 64)
                       (sign_extend' 64 (mword_of_int 80 : mword 13)) = mword_of_int (VDT + 0x8a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp8a) in "Hpc".
      iApply ("Hexit" $! C2 with "[%] Hcg Hpc Hpub Hidx"). exact HC2thr.
    - (* the wraps differ: ENTER, with nr < nc *)
      iDestruct "Hcont" as "[_ Henter]".
      assert (Hnrnc : (nr < nc)%nat).
      { destruct Hbnd as [Hle _].
        destruct (decide (nr = nc)) as [->|Hne2]; [ exfalso; apply Hne; reflexivity |].
        lia. }
      assert (Hcmp : eq_vec (rget C2 (mword_of_int 14 : mword 5))
                            (rget C2 (mword_of_int 15 : mword 5)) = false).
      { rgne. rgne. rewrite HC2a4 HC2a5.
        apply not_true_is_false; intro Hc;
        apply eq_vec_true_iff in Hc;
        exact (Hne (vt_zext16_inj _ _ (eq_sym Hc))). }
      iApply (wp_beq_fall_s_sconf Φ (mword_of_int (VDT + 0x3a))
                (mword_of_int 80 : mword 13) (mword_of_int 15 : mword 5)
                (mword_of_int 14 : mword 5) C2 n false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp
                with "Hcg Hpc Hi3a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp3e : add_vec_int (mword_of_int (VDT + 0x3a) : mword 64) 4
                     = mword_of_int (VDT + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3e) in "Hpc".
      iApply ("Henter" $! C2 nc with "[%] [%] Hlbc Hcg Hpc Hpub Hidx").
      { exact HC2thr. }
      { split; [exact Hnrnc | exact (proj2 Hbnd)]. }
  Qed.

End VtDevRam.

(* ===================================================================== *)
(* §5  The loop body's PURE arithmetic.                                   *)
(*                                                                        *)
(*     Everything [lia] touches is factored into mword-free helpers (the  *)
(*     zify hook of durable-notes makes [lia] unreliable next to          *)
(*     [bv_unsigned]); the mword-level facts are then closed by           *)
(*     [vm_compute] at a CONCRETE index, via the eight-way [destruct]     *)
(*     idiom [ProofFreeDesc.fd_shl4] uses.                                *)
(* ===================================================================== *)

(* ---- plain-Z helpers (no mword anywhere) ---- *)

Lemma vt_mod8_bound_z (nr : nat) : (0 <= Z.of_nat (nr `mod` 8) < 8)%Z.
Proof. pose proof (Nat.mod_upper_bound nr 8 ltac:(lia)). lia. Qed.

Lemma vt_mod8_z (nr : nat) : (Z.of_nat nr `mod` 8)%Z = Z.of_nat (nr `mod` 8)%nat.
Proof. rewrite Nat2Z.inj_mod. reflexivity. Qed.

Lemma vt_small_wrap64 (k : Z) : (0 <= k)%Z -> (k < 4096)%Z -> bv_wrap 64 k = k.
Proof.
  intros H0 H1. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
  apply Z.mod_small. change (2 ^ 64)%Z with 18446744073709551616%Z. lia.
Qed.

Lemma vt_land7_z (x : Z) : Z.land x 7 = (x `mod` 8)%Z.
Proof.
  change 7%Z with (Z.ones 3).
  rewrite (Z.land_ones x 3 ltac:(lia)). reflexivity.
Qed.

(* (a mod 2^32) mod 2^16 = a mod 2^16, and its 2^64 twin *)
Lemma vt_mod_32_16 (a : Z) : ((a `mod` 4294967296) `mod` 65536)%Z = (a `mod` 65536)%Z.
Proof.
  rewrite (Z.mod_mod_divide a 4294967296 65536); [reflexivity|].
  exists 65536%Z. reflexivity.
Qed.

Lemma vt_mod_64_16 (a : Z) : ((a `mod` 18446744073709551616) `mod` 65536)%Z = (a `mod` 65536)%Z.
Proof.
  rewrite (Z.mod_mod_divide a 18446744073709551616 65536); [reflexivity|].
  exists 281474976710656%Z. reflexivity.
Qed.

Lemma vt_shift48_z (u : Z) :
  ((u * 281474976710656) `mod` 18446744073709551616 / 281474976710656)%Z
  = (u `mod` 65536)%Z.
Proof.
  replace 18446744073709551616%Z with (281474976710656 * 65536)%Z by reflexivity.
  rewrite (Z.mul_comm u 281474976710656).
  rewrite (Z.mul_mod_distr_l u 65536 281474976710656 ltac:(lia) ltac:(lia)).
  rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

Lemma vt_uoff_q (nr : nat) : vt_uoff nr = (4 + 8 * (nr `mod` 8))%nat.
Proof.
  unfold vt_uoff, vq_used_ring_off, vq_used_elem_size.
  rewrite vt_mod8_z. lia.
Qed.

(* ---- mword-level structural helpers ---- *)


Lemma vt_and_vec_unsigned (a b : mword 64) :
  bv_unsigned (and_vec a b) = Z.land (bv_unsigned a) (bv_unsigned b).
Proof.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word SailStdpp.Values.to_word SailStdpp.Values.get_word].
  unfold MachineWord.MachineWord.and. apply bv_and_unsigned.
Qed.

(* [add_vec (X + p) Y] with X, Y closed: reassociate onto the symbolic base *)
Lemma vt_addv_pa (p : mword 64) (X Y : mword 64) (k : nat) :
  add_vec X Y = (mword_of_int (Z.of_nat k) : mword 64) ->
  add_vec (add_vec X p) Y = (pa_add p k : SailStdpp.Values.mword 64).
Proof.
  intro H. rewrite (add_vec64_comm X p) po_addv_assoc H.
  unfold pa_add, add_vec_int. reflexivity.
Qed.

(* ---- the ring index [disk.used_idx & 7] ---- *)

Lemma vt_ring_idx (nr : nat) :
  and_vec (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6)))
  = (mword_of_int (Z.of_nat (nr `mod` 8)) : mword 64).
Proof.
  apply bv_eq. rewrite vt_and_vec_unsigned vq_moi_unsigned.
  replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6)) : mword 64))
    with 7%Z by (vm_compute; reflexivity).
  rewrite vt_zext16_unsigned vt_land7_z wrap16_mod8 vt_mod8_z.
  pose proof (vt_mod8_bound_z nr) as Hb.
  rewrite (vt_small_wrap64 _ (proj1 Hb) ltac:(lia)). reflexivity.
Qed.

(* ---- shifts ---- *)

Lemma vt_shl3 (q : nat) : (q < 8)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat q) : mword 64)
    (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (8 * Z.of_nat q) : mword 64).
Proof. intro H. do 8 (destruct q as [|q]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

Lemma vt_shl4 (h : nat) : (h < 8)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat h) : mword 64)
    (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (16 * Z.of_nat h) : mword 64).
Proof. intro H. do 8 (destruct h as [|h]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

Lemma vt_id_word (h : nat) : (h < 8)%nat ->
  sign_extend' 64 (Z_to_bv 32 (Z.of_nat h) : SailStdpp.Values.mword 32)
  = (mword_of_int (Z.of_nat h) : mword 64).
Proof. intro H. do 8 (destruct h as [|h]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

(* ---- addresses ---- *)

Lemma vt_uelem_off (q : nat) : (q < 8)%nat ->
  add_vec (mword_of_int (8 * Z.of_nat q) : mword 64)
          (sign_extend' 64 (mword_of_int 4 : mword 12))
  = (mword_of_int (Z.of_nat (4 + 8 * q)) : mword 64).
Proof. intro H. do 8 (destruct q as [|q]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

Lemma vt_status_addr (h : nat) : (h < 8)%nat ->
  add_vec (add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                            (sign_extend' 64 (mword_of_int 32 : mword 12)))
                   (disk_base : SailStdpp.Values.mword 64))
          (sign_extend' 64 (mword_of_int 16 : mword 12))
  = (d_info_status h : SailStdpp.Values.mword 64).
Proof. intro H. do 8 (destruct h as [|h]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

Lemma vt_infob_addr (h : nat) : (h < 8)%nat ->
  add_vec (add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                            (sign_extend' 64 (mword_of_int 32 : mword 12)))
                   (disk_base : SailStdpp.Values.mword 64))
          (sign_extend' 64 (mword_of_int 8 : mword 12))
  = (d_info_b h : SailStdpp.Values.mword 64).
Proof. intro H. do 8 (destruct h as [|h]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

Lemma vt_ring_off_nat (nr : nat) :
  Z.to_nat (4 + 2 * Z.of_nat (nr `mod` 8))%Z = (4 + 2 * (nr `mod` 8))%nat.
Proof. lia. Qed.

Lemma vt_ring_addr (pd pav pu : SailStdpp.Values.mword 64) (nr : nat) :
  ring_entry_pa (virtio_init_cfg pd pav pu) nr = d_ring pav (nr `mod` 8).
Proof.
  unfold ring_entry_pa, d_ring, pa_off, vq_avail_ring_off, virtio_init_cfg.
  cbn [vc_avail]. rewrite vt_mod8_z vt_ring_off_nat. reflexivity.
Qed.

(* ---- the 16-bit wrap: c.addiw a5,1 ; c.slli a5,0x30 ; c.srli a5,0x30 ---- *)

Lemma vt_trunc16_subrange (w : mword 64) : trunc16 w = subrange_vec_dec w 15 0.
Proof.
  unfold trunc16.
  change (Z.sub (Z.mul 2 8) 1) with 15%Z.
  change (15 - 0 + 1)%Z with 16%Z.
  apply autocast_id.
Qed.

Lemma vt_trunc16_unsigned (w : mword 64) :
  bv_unsigned (trunc16 w) = bv_wrap 16 (bv_unsigned w).
Proof.
  rewrite vt_trunc16_subrange.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, SailStdpp.Values.to_word.
  rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold SailStdpp.Values.get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (15 - 0 + 1)) with 16%N.
  reflexivity.
Qed.

Lemma vt_wrap16_z (a : Z) : bv_wrap 16 a = (a `mod` 65536)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 16) with 16%Z. reflexivity. Qed.

Lemma vt_wrap32_z (a : Z) : bv_wrap 32 a = (a `mod` 4294967296)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32%Z. reflexivity. Qed.

Lemma vt_wrap64_z (a : Z) : bv_wrap 64 a = (a `mod` 18446744073709551616)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. reflexivity. Qed.

(* a sign extension keeps the low 16 bits *)
Lemma vt_sext32_mod16 (w : SailStdpp.Values.mword 32) :
  ((bv_unsigned (sign_extend' 64 w : mword 64)) `mod` 65536)%Z
  = (bv_unsigned w `mod` 65536)%Z.
Proof.
  pose proof (f_equal bv_unsigned (trunc32_sext w)) as He.
  rewrite trunc32_unsigned vt_wrap32_z in He.
  rewrite <- vt_mod_32_16. rewrite He. reflexivity.
Qed.

Lemma vt_sub32_unsigned (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 31 0 : SailStdpp.Values.mword 32)
  = (bv_unsigned x `mod` 4294967296)%Z.
Proof. rewrite <- trunc32_subrange. rewrite trunc32_unsigned. apply vt_wrap32_z. Qed.

(* the shift pair is a zero-extended 16-bit truncation *)
Lemma vt_shl48_unsigned (x : mword 64) :
  bv_unsigned (shift_bits_left x (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
  = ((bv_unsigned x * 281474976710656) `mod` 18446744073709551616)%Z.
Proof.
  assert (Hn : shift_bits_left x (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl x 48).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hn.
  unfold shiftl, SailStdpp.Values.with_word, SailStdpp.Values.get_word,
    MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 48)) = 48%Z)
    by (vm_compute; reflexivity).
  rewrite Hsh vt_wrap64_z Z.shiftl_mul_pow2; [| lia].
  change (2 ^ 48)%Z with 281474976710656%Z. reflexivity.
Qed.

Lemma vt_shr48_unsigned (x : mword 64) :
  bv_unsigned (shift_bits_right x (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
  = (bv_unsigned x / 281474976710656)%Z.
Proof.
  assert (Hn : shift_bits_right x (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftr x 48).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hn.
  unfold shiftr, SailStdpp.Values.with_word, SailStdpp.Values.get_word,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 48)) = 48%Z)
    by (vm_compute; reflexivity).
  rewrite Hsh Z.shiftr_div_pow2; [| lia].
  change (2 ^ 48)%Z with 281474976710656%Z. reflexivity.
Qed.

(* THE store value at +0x7c and the register value the back-edge test sees *)
Lemma vt_used_idx_next (nr : nat) :
  shift_bits_right
    (shift_bits_left
       (sign_extend' 64 (subrange_vec_dec
          (add_vec (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
       (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
  = (zero_extend' 64 (wrap16 (S nr) : SailStdpp.Values.mword 16) : mword 64).
Proof.
  apply bv_eq.
  rewrite vt_shr48_unsigned vt_shl48_unsigned vt_shift48_z.
  rewrite vt_zext16_unsigned.
  rewrite vt_sext32_mod16 vt_sub32_unsigned vt_mod_32_16.
  rewrite vq_add_vec_unsigned vt_wrap64_z vt_mod_64_16.
  rewrite vt_zext16_unsigned.
  replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64))
    with 1%Z by (vm_compute; reflexivity).
  unfold wrap16. rewrite !Z_to_bv_unsigned !vt_wrap16_z.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* ---- the static [struct disk] is kernel DATA (the status byte's tier) ---- *)

Lemma vt_disk_kdata_z (k : Z) :
  (0 <= k)%Z -> (k < 4096)%Z ->
  (2147512320 <= (2147628056 + k) `mod` 18446744073709551616 < 2281701376)%Z.
Proof.
  intros H0 H1. rewrite Z.mod_small; lia.
Qed.

Lemma vt_disk_kdata (k : nat) : (k < 4096)%nat -> addr_is_kdata (pa_add disk_base k).
Proof.
  intro Hk. unfold addr_is_kdata, text_end, ram_base, ram_size.
  rewrite uint_unsigned pa_add_unsigned vt_wrap64_z.
  replace (bv_unsigned (disk_base : SailStdpp.Values.mword 64)) with 2147628056%Z
    by (vm_compute; reflexivity).
  change (0x80007000)%Z with 2147512320%Z.
  change (0x80000000 + 0x8000000)%Z with 2281701376%Z.
  apply vt_disk_kdata_z; [ exact (Nat2Z.is_nonneg k) | lia ].
Qed.

(* ===================================================================== *)
(* §6  The [disk_res] SURGERY the loop body performs: position [nr] moves *)
(*     from the flight map to the parked map, its avail-ring cell comes   *)
(*     back out of the reclaimed pin, and the used_idx counter advances.  *)
(* ===================================================================== *)

Lemma vt_dom_delete_seq {A : Type} (nr np : nat) (fl : gmap nat A) :
  dom fl = set_seq nr (np - nr) -> (nr < np)%nat ->
  dom (delete nr fl) = set_seq (S nr) (np - S nr).
Proof.
  intros Hd Hlt. rewrite dom_delete_L Hd.
  apply leibniz_equiv, set_equiv. intro x.
  rewrite elem_of_difference !elem_of_set_seq elem_of_singleton. lia.
Qed.

Lemma vt_union_move {A : Type} (nr : nat) (fl pk : gmap nat A) (b : A) :
  fl !! nr = Some b -> pk !! nr = None ->
  delete nr fl ∪ <[nr := b]> pk = fl ∪ pk.
Proof.
  intros Hfl Hpk. apply map_eq. intro k. rewrite !lookup_union.
  destruct (decide (k = nr)) as [->|Hne].
  - rewrite lookup_delete lookup_insert Hfl Hpk. reflexivity.
  - rewrite lookup_delete_ne; [| exact (not_eq_sym Hne)].
    rewrite lookup_insert_ne; [| exact (not_eq_sym Hne)]. reflexivity.
Qed.

Lemma vt_dom_tr_stable {A : Type} (nr : nat) (fl pk : gmap nat A) (b : A) :
  nr ∈ dom fl ->
  dom (delete nr fl) ∪ dom (<[nr := b]> pk) = dom fl ∪ dom pk.
Proof.
  intro Hin. rewrite dom_delete_L dom_insert_L.
  apply leibniz_equiv, set_equiv. intro x.
  rewrite !elem_of_union elem_of_difference !elem_of_singleton.
  split.
  - intros [[H1 _]|[->|H1]]; [ left; exact H1 | left; exact Hin | right; exact H1 ].
  - intros [H1|H1].
    + destruct (decide (x = nr)) as [->|Hne];
        [ right; left; reflexivity | left; split; [exact H1 | exact Hne] ].
    + right; right; exact H1.
Qed.

Lemma vt_mod8_split {A : Type} (nr : nat) (fl : gmap nat A) :
  nr ∈ dom fl ->
  mod8 (dom fl) = mod8 (dom (delete nr fl)) ∪ {[ (nr `mod` 8)%nat ]}.
Proof.
  intro Hin. rewrite dom_delete_L.
  apply leibniz_equiv, set_equiv. intro x.
  rewrite elem_of_union elem_of_singleton. unfold mod8. rewrite !elem_of_map.
  split.
  - intros (p & -> & Hp). destruct (decide (p = nr)) as [->|Hne]; [right; reflexivity|].
    left. exists p. split; [reflexivity|].
    apply elem_of_difference. split; [exact Hp|]. rewrite elem_of_singleton. exact Hne.
  - intros [(p & -> & Hp)| ->].
    + exists p. split; [reflexivity|]. apply elem_of_difference in Hp as [Hp _]. exact Hp.
    + exists nr. split; [reflexivity | exact Hin].
Qed.

Lemma vt_mod8_head_fresh (nr np : nat) :
  (np - S nr <= 1)%nat -> (nr `mod` 8)%nat ∉ mod8 (set_seq (S nr) (np - S nr)).
Proof.
  intro Hw. unfold mod8. intro Hin.
  apply elem_of_map in Hin as (p & Hp & Hpin).
  apply elem_of_set_seq in Hpin.
  assert (Hpe : p = S nr) by lia. subst p. symmetry in Hp.
  assert (Hb : (nr `mod` 8 < 8)%nat) by (apply Nat.mod_upper_bound; lia).
  replace (S nr) with (nr + 1)%nat in Hp by lia.
  rewrite <- Nat.Div0.add_mod_idemp_l in Hp.
  destruct (Nat.eq_dec (nr `mod` 8)%nat 7%nat) as [Hr|Hr].
  - rewrite Hr in Hp. cbn in Hp. lia.
  - rewrite (Nat.mod_small (nr `mod` 8 + 1)%nat 8) in Hp; lia.
Qed.

(* the live window is at most two positions wide (three descriptors each,
   eight in all), so after [nr] is reclaimed at most one remains *)
Lemma vt_window_le {A : Type} (np nr : nat) (fl pk : gmap nat A)
    (tr : gmap nat (nat * nat * nat)) :
  dom fl = set_seq nr (np - nr) ->
  dom tr = dom fl ∪ dom pk ->
  (forall p T, tr !! p = Some T -> tri_ok T) ->
  (forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
     tri_set Tp ## tri_set Tq) ->
  (np - nr <= 2)%nat.
Proof.
  intros Hfl Htr Hok Hdisj.
  pose proof (tri_card_8 tr Hok Hdisj) as Hsz.
  assert (Hdom : (size (dom fl) <= size (dom tr))%nat).
  { apply subseteq_size. rewrite Htr. apply union_subseteq_l. }
  rewrite Hfl size_set_seq size_dom in Hdom. lia.
Qed.

Section VtSurgery.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  (* the two avail-ring bytes come back OUT of the reclaimed pin: the pin
     pins them ([slot_pin_ok]'s [spo_ring]), so they are a sub-map of it and
     what is left is provably disjoint from the ring slot -- which is exactly
     [parked_res]'s side condition. *)
  Lemma vt_pin_ring_split (A : Arch.pa) (w : bv 16) (pin : _) :
    read_bytes pin A 2 = Some w ->
    phys_map pin -∗
    phys_word2 A w ∗ phys_map (pin ∖ range_map A 2 (nth_byte w)).
  Proof.
    intro Hr.
    set (rm := range_map A 2 (nth_byte w)).
    assert (Hsub : rm ⊆ pin).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec pin A 2 w Hr j). lia. }
    assert (Hd : rm ∪ (pin ∖ rm) = pin) by (apply map_difference_union; exact Hsub).
    assert (Hdj : rm ##ₘ pin ∖ rm)
      by (apply (map_disjoint_difference_r pin rm rm); reflexivity).
    assert (Heq : phys_map pin ⊣⊢ phys_map rm ∗ phys_map (pin ∖ rm)).
    { rewrite -(phys_map_union rm (pin ∖ rm) Hdj) Hd. reflexivity. }
    iIntros "Hpin". iEval (rewrite Heq) in "Hpin".
    iDestruct "Hpin" as "[Hring Hrest]".
    iSplitL "Hring".
    { iEval (rewrite -(phys_word2_map A w)) in "Hring". iExact "Hring". }
    iExact "Hrest".
  Qed.

End VtSurgery.

(* ===================================================================== *)
(* §7  The LOOP BODY, in five Qed-sealed chunks (optimization.md: a       *)
(*     monolithic threading proof grows super-linearly in #instructions). *)
(*     Every chunk states its register effect as a FRAME condition over   *)
(*     an abstract output map, so the chain never carries a [set]-tower.  *)
(* ===================================================================== *)

Section VtBody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).
  Notation a4_idx := (mword_of_int 14 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  (* the reclaim payoff, as one bundle *)
  Definition vt_payoff (γd : disk_names) (sl : vslot) (pin : _) : iProp Σ :=
    (phys_map pin ∗
     phys_pointsto (vr_status (vs_req sl)) (DfracOwn 1) byte_zero ∗
     (* the SPENT crash permit's token, on its way to [DiskInv.parked_res] *)
     perm_done (dn_perm γd) (vs_perm sl) ∗
     (∃ bs : list (bv 8),
        ⌜length bs = vs_len sl⌝ ∗
        ⌜bs = vs_data sl⌝ ∗
        disk_bytes γd (vs_sector_off sl) bs ∗
        (if vs_is_out sl then emp else phys_list (vr_buf (vs_req sl)) bs)))%I.

  (* ---- CHUNK A (+0x3e .. +0x4e): the fence, the ring-slot address     *)
  (*      computation and the used-element load that RECLAIMS position   *)
  (*      [nr].  Only a4/a5 move; a5 ends holding the chain head [h].    *)
  Lemma wp_vt_reclaim (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ) (pd pav pu : mword 64) (M : regfile) (n : nat)
      (np c nr h : nat) (sl : vslot) (pin : _) (pp : mword 64) :
    (M !!! Regidx s1_idx : mword 64) = (disk_base : mword 64) ->
    (nr < c)%nat -> (h < 8)%nat ->
    bv_unsigned (vr_head (vs_req sl)) = Z.of_nat h ->
    sie_cap_gpr M n false pp -∗
    kernel_text -∗ pc_is (mword_of_int (VDT + 0x3e) : mword 64) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    disk_pub γd np -∗ disk_receipt γd nr sl pin -∗ disk_done_lb γd c -∗
    d_used_idx ↦₂ wrap16 nr -∗
    ( ∀ M' : regfile,
        ⌜ M' !!! Regidx a5_idx = (mword_of_int (Z.of_nat h) : mword 64)
          /\ (forall r : mword 5, r <> a4_idx -> r <> a5_idx ->
                M' !!! Regidx r = M !!! Regidx r) ⌝ -∗
        ⌜ slot_pin_ok (virtio_init_cfg pd pav pu) nr sl pin ⌝ -∗
        sie_cap_gpr M' n false pp -∗
        pc_is (mword_of_int (VDT + 0x50) : mword 64) -∗
        d_used_idx ↦₂ wrap16 nr -∗
        disk_pub γd np -∗ disk_done_lb γd (S nr) -∗
        vt_payoff γd sl pin -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HMs1 Hnrc Hh8 Hhead.
    iIntros "Hcg #Htext Hpc #Hdinv #Hgeom Hpub Hrcpt #Hlbc Hidx Hcont".
    iPoseProof "Hgeom" as "(_ & _ & #Hup & _)".
    (* ---- +0x3e: fence rw,rw ---- *)
    iPoseProof (vti_3e with "Htext") as "Hi3e".
    iApply (wp_fence_gen_s_sconf Φ (mword_of_int (VDT + 0x3e))
              (mword_of_int 0) (mword_of_int 3) (mword_of_int 3)
              (Regidx (mword_of_int 0)) (Regidx (mword_of_int 0)) M n false
              with "Hcg Hpc Hi3e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hp42 : add_vec_int (mword_of_int (VDT + 0x3e) : mword 64) 4 = mword_of_int (VDT + 0x42))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp42) in "Hpc".
    (* ---- +0x42: c.ld a4,16(s1) -- a4 := disk.used ---- *)
    assert (Hup : add_vec (rget M s1_idx) (sign_extend' 64 (mword_of_int 16 : mword 12))
                  = (d_used_ptr : mword 64)).
    { rgne. rewrite HMs1 vt_sext_16. reflexivity. }
    iPoseProof (vti_42 with "Htext") as "Hi42".
    iApply (wp_cld_s_sconf Φ (mword_of_int (VDT + 0x42)) a4_idx s1_idx
              (mword_of_int 16 : mword 12) M n pu false (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [] [-]").
    { iEval (rewrite Hup). iExact "Hup". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (K0 := <[Regidx a4_idx := regval_into_reg pu]> M).
    change (<[Regidx a4_idx := regval_into_reg pu]> M) with K0.
    assert (Hp44 : add_vec_int (mword_of_int (VDT + 0x42) : mword 64) 2 = mword_of_int (VDT + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    assert (HK0s1 : K0 !!! Regidx s1_idx = (disk_base : mword 64))
      by (rewrite /K0 upd_ne; [exact HMs1 | reg_neq]).
    (* ---- +0x44: lhu a5,32(s1) -- a5 := disk.used_idx ---- *)
    assert (Huidx : add_vec (rget K0 s1_idx) (sign_extend' 64 (mword_of_int 32 : mword 12))
                    = (d_used_idx : mword 64)).
    { rgne. rewrite HK0s1 vt_sext_32. reflexivity. }
    iPoseProof (vti_44 with "Htext") as "Hi44".
    iApply (wp_lhu_s_sconf Φ (mword_of_int (VDT + 0x44)) a5_idx s1_idx
              (mword_of_int 32 : mword 12) K0 n (wrap16 nr) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 [Hidx] [-]").
    { iEval (rewrite Huidx). iExact "Hidx". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hidx". iEval (rewrite Huidx) in "Hidx".
    set (K1 := <[Regidx a5_idx := regval_into_reg
        (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))]> K0).
    change (<[Regidx a5_idx := regval_into_reg
        (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))]> K0) with K1.
    assert (Hp48 : add_vec_int (mword_of_int (VDT + 0x44) : mword 64) 4 = mword_of_int (VDT + 0x48))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp48) in "Hpc".
    (* ---- +0x48: c.andi a5,7 -- a5 := used_idx % NUM ---- *)
    assert (HK1a5 : K1 !!! Regidx a5_idx
                    = zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))
      by (rewrite /K1; apply upd_eq).
    iPoseProof (vti_48 with "Htext") as "Hi48".
    iApply (wp_candi_s_sconf Φ (mword_of_int (VDT + 0x48)) a5_idx (mword_of_int 7 : mword 6)
              K1 n false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (HK2v : and_vec (rget K1 a5_idx)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6)))
                   = (mword_of_int (Z.of_nat (nr `mod` 8)) : mword 64)).
    { rgne. rewrite HK1a5. apply vt_ring_idx. }
    set (K2 := <[Regidx a5_idx := regval_into_reg
        (mword_of_int (Z.of_nat (nr `mod` 8)) : mword 64)]> K1).
    iEval (rewrite HK2v) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (mword_of_int (Z.of_nat (nr `mod` 8)) : mword 64)]> K1) with K2.
    assert (Hp4a : add_vec_int (mword_of_int (VDT + 0x48) : mword 64) 2 = mword_of_int (VDT + 0x4a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4a) in "Hpc".
    (* ---- +0x4a: c.slli a5,3 -- * sizeof(used elem) ---- *)
    assert (Hq8 : (nr `mod` 8 < 8)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (HK2a5 : K2 !!! Regidx a5_idx = (mword_of_int (Z.of_nat (nr `mod` 8)) : mword 64))
      by (rewrite /K2; apply upd_eq).
    iPoseProof (vti_4a with "Htext") as "Hi4a".
    iApply (wp_cslli_s_sconf Φ (mword_of_int (VDT + 0x4a)) (Regidx a5_idx) a5_idx
              (mword_of_int 3 : mword 6) K2 n false eq_refl
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (HK3v : shift_bits_left (rget K2 a5_idx)
                     (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
                   = (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64)).
    { rgne. rewrite HK2a5. apply vt_shl3. exact Hq8. }
    set (K3 := <[Regidx a5_idx := regval_into_reg
        (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64)]> K2).
    iEval (rewrite HK3v) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64)]> K2) with K3.
    assert (Hp4c : add_vec_int (mword_of_int (VDT + 0x4a) : mword 64) 2 = mword_of_int (VDT + 0x4c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4c) in "Hpc".
    (* ---- +0x4c: c.add a5,a5,a4 -- &used->ring[nr % NUM] ---- *)
    assert (HK3a4 : K3 !!! Regidx a4_idx = pu).
    { rewrite /K3 upd_ne; [| reg_neq]. rewrite /K2 upd_ne; [| reg_neq].
      rewrite /K1 upd_ne; [| reg_neq]. rewrite /K0. apply upd_eq. }
    assert (HK3a5 : K3 !!! Regidx a5_idx = (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64))
      by (rewrite /K3; apply upd_eq).
    iPoseProof (vti_4c with "Htext") as "Hi4c".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (VDT + 0x4c)) a5_idx a4_idx K3 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (K4 := <[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64) pu)]> K3).
    assert (HK4v : add_vec (rget K3 a5_idx) (rget K3 a4_idx)
                   = add_vec (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64) pu).
    { rgne. rgne. rewrite HK3a4 HK3a5. reflexivity. }
    iEval (rewrite HK4v) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64) pu)]> K3) with K4.
    assert (Hp4e : add_vec_int (mword_of_int (VDT + 0x4c) : mword 64) 2 = mword_of_int (VDT + 0x4e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4e) in "Hpc".
    (* ---- +0x4e: c.lw a5,4(a5) -- the RECLAIM ---- *)
    assert (HK4a5 : K4 !!! Regidx a5_idx
                    = add_vec (mword_of_int (8 * Z.of_nat (nr `mod` 8)) : mword 64) pu)
      by (rewrite /K4; apply upd_eq).
    assert (Hea : add_vec (rget K4 a5_idx) (sign_extend' 64 (mword_of_int 4 : mword 12))
                  = (pa_add pu (vt_uoff nr) : SailStdpp.Values.mword 64)).
    { rgne. rewrite HK4a5 vt_uoff_q.
      apply (vt_addv_pa pu _ _ (4 + 8 * (nr `mod` 8))%nat).
      apply vt_uelem_off. exact Hq8. }
    iPoseProof (vti_4e with "Htext") as "Hi4e".
    iApply (wp_vt_lw_used_elem γu γd Φ pd pav pu (mword_of_int (VDT + 0x4e))
              a5_idx a5_idx (mword_of_int 4 : mword 12) K4 n np c nr sl pin pp
              Hnrc Hea ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e Hdinv Hgeom Hpub Hrcpt Hlbc [-]").
    iIntros "%Hspo Hcg Hpc Hpub #Hlbs Hpin Hstat Hrest".
    assert (Hidv : sign_extend' 64 (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))
                                    : SailStdpp.Values.mword 32)
                   = (mword_of_int (Z.of_nat h) : mword 64))
      by (rewrite Hhead; apply vt_id_word; exact Hh8).
    iEval (rewrite Hidv) in "Hcg".
    set (K5 := <[Regidx a5_idx := regval_into_reg (mword_of_int (Z.of_nat h) : mword 64)]> K4).
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int (Z.of_nat h) : mword 64)]> K4) with K5.
    assert (Hp50 : add_vec_int (mword_of_int (VDT + 0x4e) : mword 64) 2 = mword_of_int (VDT + 0x50))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp50) in "Hpc".
    iApply ("Hcont" $! K5 with "[%] [%] Hcg Hpc Hidx Hpub Hlbs [Hpin Hstat Hrest]").
    { split.
      - rewrite /K5. apply upd_eq.
      - intros r N4 N5.
        rewrite /K5 upd_ne; [| congruence].
        rewrite /K4 upd_ne; [| congruence].
        rewrite /K3 upd_ne; [| congruence].
        rewrite /K2 upd_ne; [| congruence].
        rewrite /K1 upd_ne; [| congruence].
        rewrite /K0 upd_ne; [| congruence]. reflexivity. }
    { exact Hspo. }
    { rewrite /vt_payoff. iFrame "Hpin Hstat Hrest". }
  Qed.

  (* ---- the [struct disk] byte tier: the status cell is kernel DATA ---- *)
  Lemma vt_kdata_canon (a : Arch.pa) :
    addr_is_kdata a -> (uint (a : SailStdpp.Values.mword 64) < 274877906944)%Z.
  Proof.
    intro Hka. unfold addr_is_kdata, ram_base, ram_size, text_end in Hka.
    first [ lia
          | (assert (Heq : (uint (a : SailStdpp.Values.mword 64) = uint a)%Z)
               by reflexivity; rewrite Heq; lia) ].
  Qed.

  Lemma vt_status_kdata (h : nat) : (h < 8)%nat -> addr_is_kdata (d_info_status h).
  Proof. intro H. unfold d_info_status. apply vt_disk_kdata. lia. Qed.

  Lemma vt_infob_kdata (h : nat) : (h < 8)%nat -> addr_is_kdata (d_info_b h).
  Proof. intro H. unfold d_info_b. apply vt_disk_kdata. lia. Qed.

  Lemma vt_sext_4 : sign_extend' 64 (mword_of_int 4 : mword 12) = (mword_of_int 4 : mword 64).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma vt_bdisk_addr (b : Arch.pa) :
    add_vec (b : SailStdpp.Values.mword 64) (sign_extend' 64 (mword_of_int 4 : mword 12))
    = (b_disk b : SailStdpp.Values.mword 64).
  Proof. rewrite vt_sext_4. unfold b_disk, pa_add, add_vec_int. reflexivity. Qed.

  (* ---- CHUNK B (+0x50 .. +0x5e): &disk.info[id].status, the load, and  *)
  (*      the REFUTED panic branch (the byte is pinned at 0).             *)
  Lemma wp_vt_status (γd : disk_names)
      (Φ : mval -> iProp Σ) (pd pav pu : mword 64) (M : regfile) (n h : nat)
      (pp : mword 64) :
    (M !!! Regidx s1_idx : mword 64) = (disk_base : mword 64) ->
    (M !!! Regidx a5_idx : mword 64) = (mword_of_int (Z.of_nat h) : mword 64) ->
    (h < 8)%nat ->
    sie_cap_gpr M n false pp -∗
    kernel_text -∗ pc_is (mword_of_int (VDT + 0x50) : mword 64) -∗
    disk_geom γd pd pav pu -∗
    phys_pointsto (d_info_status h) (DfracOwn 1) byte_zero -∗
    ( ∀ M' : regfile,
        ⌜ M' !!! Regidx a5_idx = (mword_of_int (Z.of_nat h) : mword 64)
          /\ (forall r : mword 5, r <> a4_idx -> r <> a5_idx ->
                M' !!! Regidx r = M !!! Regidx r) ⌝ -∗
        sie_cap_gpr M' n false pp -∗
        pc_is (mword_of_int (VDT + 0x60) : mword 64) -∗
        phys_pointsto (d_info_status h) (DfracOwn 1) byte_zero -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HMs1 HMa5 Hh8.
    iIntros "Hcg #Htext Hpc #Hgeom Hstat Hcont".
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    pose proof (kdata_svpn_class _ (vt_status_kdata h Hh8)) as Hstk.
    pose proof (vt_kdata_canon _ (vt_status_kdata h Hh8)) as Hstc.
    iDestruct (phys_to_byte (d_info_status h) byte_zero Hstk Hstc with "Hkm Hstat") as "Hstat".
    (* ---- +0x50: slli a4,a5,0x4 ---- *)
    iPoseProof (vti_50 with "Htext") as "Hi50".
    assert (Hsh4 : shift_bits_left (rget M a5_idx)
                     (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
                   = (mword_of_int (16 * Z.of_nat h) : mword 64)).
    { rgne. rewrite HMa5. apply vt_shl4. exact Hh8. }
    iApply (wp_slli_s_sconf Φ (mword_of_int (VDT + 0x50)) a4_idx a5_idx
              (mword_of_int 4 : mword 6) (mword_of_int (16 * Z.of_nat h) : mword 64) M n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              Hsh4
              with "Hcg Hpc Hi50 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B0 := <[Regidx a4_idx := regval_into_reg
        (mword_of_int (16 * Z.of_nat h) : mword 64)]> M).
    change (<[Regidx a4_idx := regval_into_reg
        (mword_of_int (16 * Z.of_nat h) : mword 64)]> M) with B0.
    assert (Hp54 : add_vec_int (mword_of_int (VDT + 0x50) : mword 64) 4 = mword_of_int (VDT + 0x54))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp54) in "Hpc".
    (* ---- +0x54: addi a4,a4,32 ---- *)
    iPoseProof (vti_54 with "Htext") as "Hi54".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (VDT + 0x54)) a4_idx a4_idx
              (mword_of_int 32 : mword 12) B0 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (HB0a4 : B0 !!! Regidx a4_idx = (mword_of_int (16 * Z.of_nat h) : mword 64))
      by (rewrite /B0; apply upd_eq).
    set (B1 := <[Regidx a4_idx := regval_into_reg
        (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                 (sign_extend' 64 (mword_of_int 32 : mword 12)))]> B0).
    iEval (rgne) in "Hcg". iEval (rewrite HB0a4) in "Hcg".
    change (<[Regidx a4_idx := regval_into_reg
        (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                 (sign_extend' 64 (mword_of_int 32 : mword 12)))]> B0) with B1.
    assert (Hp58 : add_vec_int (mword_of_int (VDT + 0x54) : mword 64) 4 = mword_of_int (VDT + 0x58))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp58) in "Hpc".
    (* ---- +0x58: c.add a4,a4,s1 -- &disk.info[id] - 16 ---- *)
    assert (HB1a4 : B1 !!! Regidx a4_idx
                    = add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                              (sign_extend' 64 (mword_of_int 32 : mword 12)))
      by (rewrite /B1; apply upd_eq).
    assert (HB1s1 : B1 !!! Regidx s1_idx = (disk_base : mword 64)).
    { rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq]. exact HMs1. }
    iPoseProof (vti_58 with "Htext") as "Hi58".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (VDT + 0x58)) a4_idx s1_idx B1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx a4_idx := regval_into_reg
        (add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                          (sign_extend' 64 (mword_of_int 32 : mword 12)))
                 (disk_base : SailStdpp.Values.mword 64))]> B1).
    assert (HB2v : add_vec (rget B1 a4_idx) (rget B1 s1_idx)
                   = add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                                      (sign_extend' 64 (mword_of_int 32 : mword 12)))
                             (disk_base : SailStdpp.Values.mword 64)).
    { rgne. rgne. rewrite HB1a4 HB1s1. reflexivity. }
    iEval (rewrite HB2v) in "Hcg".
    change (<[Regidx a4_idx := regval_into_reg
        (add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                          (sign_extend' 64 (mword_of_int 32 : mword 12)))
                 (disk_base : SailStdpp.Values.mword 64))]> B1) with B2.
    assert (Hp5a : add_vec_int (mword_of_int (VDT + 0x58) : mword 64) 2 = mword_of_int (VDT + 0x5a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    (* ---- +0x5a: lbu a4,16(a4) -- disk.info[id].status ---- *)
    assert (HB2a4 : B2 !!! Regidx a4_idx
                    = add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                                       (sign_extend' 64 (mword_of_int 32 : mword 12)))
                              (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /B2; apply upd_eq).
    assert (Hsa : add_vec (rget B2 a4_idx) (sign_extend' 64 (mword_of_int 16 : mword 12))
                  = (d_info_status h : SailStdpp.Values.mword 64)).
    { rgne. rewrite HB2a4. apply vt_status_addr. exact Hh8. }
    iPoseProof (vti_5a with "Htext") as "Hi5a".
    iApply (wp_lbu_s_sconf Φ (mword_of_int (VDT + 0x5a)) a4_idx a4_idx
              (mword_of_int 16 : mword 12) B2 n byte_zero false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a [Hstat] [-]").
    { iEval (rewrite Hsa). iExact "Hstat". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hstat". iEval (rewrite Hsa) in "Hstat".
    set (B3 := <[Regidx a4_idx := regval_into_reg
        (zero_extend' 64 (byte_zero : SailStdpp.Values.mword 8))]> B2).
    change (<[Regidx a4_idx := regval_into_reg
        (zero_extend' 64 (byte_zero : SailStdpp.Values.mword 8))]> B2) with B3.
    assert (Hp5e : add_vec_int (mword_of_int (VDT + 0x5a) : mword 64) 4 = mword_of_int (VDT + 0x5e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    (* ---- +0x5e: c.bnez a4 -- the status panic, REFUTED ---- *)
    assert (HB3a4 : B3 !!! Regidx a4_idx
                    = zero_extend' 64 (byte_zero : SailStdpp.Values.mword 8))
      by (rewrite /B3; apply upd_eq).
    iPoseProof (vti_5e with "Htext") as "Hi5e".
    assert (Hnz5e : neq_vec (rget B3 a4_idx) zero_reg = false).
    { rgne. rewrite HB3a4. vm_compute. reflexivity. }
    iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (VDT + 0x5e)) (mword_of_int 33 : mword 8)
              (Cregidx (mword_of_int 6)) a4_idx B3 n false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Hnz5e
              with "Hcg Hpc Hi5e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hp60 : add_vec_int (mword_of_int (VDT + 0x5e) : mword 64) 2 = mword_of_int (VDT + 0x60))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    iDestruct (byte_to_phys (d_info_status h) byte_zero Hstk with "Hkm Hstat") as "Hstat".
    iApply ("Hcont" $! B3 with "[%] Hcg Hpc Hstat").
    split.
    - rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq].
      rewrite /B1 upd_ne; [| reg_neq].
      rewrite /B0 upd_ne; [| reg_neq]. exact HMa5.
    - intros r N4 N5.
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      rewrite /B0 upd_ne; [| congruence]. reflexivity.
  Qed.

  (* ---- CHUNK C (+0x60 .. +0x6a): b = disk.info[id].b ; b->disk = 0 ---- *)
  Lemma wp_vt_clear_disk (Φ : mval -> iProp Σ) (M : regfile) (n h : nat)
      (b : Arch.pa) (pp : mword 64) :
    (M !!! Regidx s1_idx : mword 64) = (disk_base : mword 64) ->
    (M !!! Regidx a5_idx : mword 64) = (mword_of_int (Z.of_nat h) : mword 64) ->
    (h < 8)%nat ->
    sie_cap_gpr M n false pp -∗
    kernel_text -∗ pc_is (mword_of_int (VDT + 0x60) : mword 64) -∗
    d_info_b h ↦₈ (b : SailStdpp.Values.mword 64) -∗
    b_disk b ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) -∗
    ( ∀ M' : regfile,
        ⌜ M' !!! Regidx a0_idx = (b : SailStdpp.Values.mword 64)
          /\ (forall r : mword 5, r <> a0_idx -> r <> a5_idx ->
                M' !!! Regidx r = M !!! Regidx r) ⌝ -∗
        sie_cap_gpr M' n false pp -∗
        pc_is (mword_of_int (VDT + 0x6e) : mword 64) -∗
        d_info_b h ↦₈ (b : SailStdpp.Values.mword 64) -∗
        b_disk b ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 0) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HMs1 HMa5 Hh8.
    iIntros "Hcg #Htext Hpc Hib Hbd Hcont".
    (* ---- +0x60: c.slli a5,4 ---- *)
    iPoseProof (vti_60 with "Htext") as "Hi60".
    iApply (wp_cslli_s_sconf Φ (mword_of_int (VDT + 0x60)) (Regidx a5_idx) a5_idx
              (mword_of_int 4 : mword 6) M n false eq_refl
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (HC0v : shift_bits_left (rget M a5_idx)
                     (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
                   = (mword_of_int (16 * Z.of_nat h) : mword 64)).
    { rgne. rewrite HMa5. apply vt_shl4. exact Hh8. }
    set (C0 := <[Regidx a5_idx := regval_into_reg
        (mword_of_int (16 * Z.of_nat h) : mword 64)]> M).
    iEval (rewrite HC0v) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (mword_of_int (16 * Z.of_nat h) : mword 64)]> M) with C0.
    assert (Hp62 : add_vec_int (mword_of_int (VDT + 0x60) : mword 64) 2 = mword_of_int (VDT + 0x62))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    (* ---- +0x62: addi a5,a5,32 ---- *)
    assert (HC0a5 : C0 !!! Regidx a5_idx = (mword_of_int (16 * Z.of_nat h) : mword 64))
      by (rewrite /C0; apply upd_eq).
    iPoseProof (vti_62 with "Htext") as "Hi62".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (VDT + 0x62)) a5_idx a5_idx
              (mword_of_int 32 : mword 12) C0 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                 (sign_extend' 64 (mword_of_int 32 : mword 12)))]> C0).
    iEval (rgne) in "Hcg". iEval (rewrite HC0a5) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                 (sign_extend' 64 (mword_of_int 32 : mword 12)))]> C0) with C1.
    assert (Hp66 : add_vec_int (mword_of_int (VDT + 0x62) : mword 64) 4 = mword_of_int (VDT + 0x66))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    (* ---- +0x66: c.add a5,a5,s1 ---- *)
    assert (HC1a5 : C1 !!! Regidx a5_idx
                    = add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                              (sign_extend' 64 (mword_of_int 32 : mword 12)))
      by (rewrite /C1; apply upd_eq).
    assert (HC1s1 : C1 !!! Regidx s1_idx = (disk_base : mword 64)).
    { rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_ne; [| reg_neq]. exact HMs1. }
    iPoseProof (vti_66 with "Htext") as "Hi66".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (VDT + 0x66)) a5_idx s1_idx C1 n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C2 := <[Regidx a5_idx := regval_into_reg
        (add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                          (sign_extend' 64 (mword_of_int 32 : mword 12)))
                 (disk_base : SailStdpp.Values.mword 64))]> C1).
    assert (HC2v : add_vec (rget C1 a5_idx) (rget C1 s1_idx)
                   = add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                                      (sign_extend' 64 (mword_of_int 32 : mword 12)))
                             (disk_base : SailStdpp.Values.mword 64)).
    { rgne. rgne. rewrite HC1a5 HC1s1. reflexivity. }
    iEval (rewrite HC2v) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                          (sign_extend' 64 (mword_of_int 32 : mword 12)))
                 (disk_base : SailStdpp.Values.mword 64))]> C1) with C2.
    assert (Hp68 : add_vec_int (mword_of_int (VDT + 0x66) : mword 64) 2 = mword_of_int (VDT + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* ---- +0x68: c.ld a0,8(a5) -- b = disk.info[id].b ---- *)
    assert (HC2a5 : C2 !!! Regidx a5_idx
                    = add_vec (add_vec (mword_of_int (16 * Z.of_nat h) : mword 64)
                                       (sign_extend' 64 (mword_of_int 32 : mword 12)))
                              (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /C2; apply upd_eq).
    assert (Hba : add_vec (rget C2 a5_idx) (sign_extend' 64 (mword_of_int 8 : mword 12))
                  = (d_info_b h : SailStdpp.Values.mword 64)).
    { rgne. rewrite HC2a5. apply vt_infob_addr. exact Hh8. }
    iPoseProof (vti_68 with "Htext") as "Hi68".
    iApply (wp_cld_s_sconf Φ (mword_of_int (VDT + 0x68)) a0_idx a5_idx
              (mword_of_int 8 : mword 12) C2 n (b : SailStdpp.Values.mword 64) false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68 [Hib] [-]").
    { iEval (rewrite Hba). iExact "Hib". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hib". iEval (rewrite Hba) in "Hib".
    set (C3 := <[Regidx a0_idx := regval_into_reg (b : SailStdpp.Values.mword 64)]> C2).
    change (<[Regidx a0_idx := regval_into_reg (b : SailStdpp.Values.mword 64)]> C2) with C3.
    assert (Hp6a : add_vec_int (mword_of_int (VDT + 0x68) : mword 64) 2 = mword_of_int (VDT + 0x6a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    (* ---- +0x6a: sw zero,4(a0) -- b->disk = 0 ---- *)
    assert (HC3a0 : C3 !!! Regidx a0_idx = (b : SailStdpp.Values.mword 64))
      by (rewrite /C3; apply upd_eq).
    assert (Hbda : add_vec (rget C3 a0_idx) (sign_extend' 64 (mword_of_int 4 : mword 12))
                   = (b_disk b : SailStdpp.Values.mword 64)).
    { rgne. rewrite HC3a0. apply vt_bdisk_addr. }
    iPoseProof (vti_6a with "Htext") as "Hi6a".
    iApply (wp_sw_zero_s_sconf Φ (mword_of_int (VDT + 0x6a)) a0_idx
              (mword_of_int 4 : mword 12) C3 n
              (SailStdpp.Values.mword_of_int (len := 32) 1) false
              with "Hcg Hpc Hi6a [Hbd] [-]").
    { iEval (rewrite Hbda). iExact "Hbd". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbd". iEval (rewrite Hbda) in "Hbd".
    assert (Hp6e : add_vec_int (mword_of_int (VDT + 0x6a) : mword 64) 4 = mword_of_int (VDT + 0x6e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    iApply ("Hcont" $! C3 with "[%] Hcg Hpc Hib Hbd").
    split; [exact HC3a0|].
    intros r N0 N5.
    rewrite /C3 upd_ne; [| congruence].
    rewrite /C2 upd_ne; [| congruence].
    rewrite /C1 upd_ne; [| congruence].
    rewrite /C0 upd_ne; [| congruence]. reflexivity.
  Qed.

  Lemma vt_trunc16_zext (x : SailStdpp.Values.mword 16) :
    trunc16 (zero_extend' 64 (x : SailStdpp.Values.mword 16) : mword 64) = x.
  Proof.
    apply bv_eq. rewrite vt_trunc16_unsigned vt_zext16_unsigned.
    apply bv_wrap_bv_unsigned.
  Qed.

  (* ---- CHUNK E (+0x72 .. +0x82): disk.used_idx += 1 (16-bit wrap) and  *)
  (*      the back-edge re-read of the device's used->idx.                *)
  Lemma wp_vt_advance (γu : uart_names) (γd : disk_names)
      (Φ : mval -> iProp Σ) (pd pav pu : mword 64) (M : regfile) (n : nat)
      (np nr : nat) (pp : mword 64) :
    (M !!! Regidx s1_idx : mword 64) = (disk_base : mword 64) ->
    sie_cap_gpr M n false pp -∗
    kernel_text -∗ pc_is (mword_of_int (VDT + 0x72) : mword 64) -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    disk_pub γd np -∗ disk_done_lb γd (S nr) -∗
    d_used_idx ↦₂ wrap16 nr -∗
    ( ∀ (M' : regfile) (nc : nat),
        ⌜ M' !!! Regidx a5_idx
            = (zero_extend' 64 (wrap16 (S nr) : SailStdpp.Values.mword 16) : mword 64)
          /\ M' !!! Regidx a4_idx
            = (zero_extend' 64 (wrap16 nc : SailStdpp.Values.mword 16) : mword 64)
          /\ (forall r : mword 5, r <> a4_idx -> r <> a5_idx ->
                M' !!! Regidx r = M !!! Regidx r) ⌝ -∗
        ⌜ (S nr <= nc)%nat /\ (nc <= np)%nat ⌝ -∗
        disk_done_lb γd nc -∗
        sie_cap_gpr M' n false pp -∗
        pc_is (mword_of_int (VDT + 0x86) : mword 64) -∗
        disk_pub γd np -∗ d_used_idx ↦₂ wrap16 (S nr) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HMs1.
    iIntros "Hcg #Htext Hpc #Hdinv #Hgeom Hpub #Hlbs Hidx Hcont".
    iPoseProof "Hgeom" as "(_ & _ & #Hup & _)".
    (* ---- +0x72: lhu a5,32(s1) ---- *)
    assert (Huidx : add_vec (rget M s1_idx) (sign_extend' 64 (mword_of_int 32 : mword 12))
                    = (d_used_idx : mword 64)).
    { rgne. rewrite HMs1 vt_sext_32. reflexivity. }
    iPoseProof (vti_72 with "Htext") as "Hi72".
    iApply (wp_lhu_s_sconf Φ (mword_of_int (VDT + 0x72)) a5_idx s1_idx
              (mword_of_int 32 : mword 12) M n (wrap16 nr) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi72 [Hidx] [-]").
    { iEval (rewrite Huidx). iExact "Hidx". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hidx". iEval (rewrite Huidx) in "Hidx".
    set (D0 := <[Regidx a5_idx := regval_into_reg
        (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))]> M).
    change (<[Regidx a5_idx := regval_into_reg
        (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))]> M) with D0.
    assert (Hp76 : add_vec_int (mword_of_int (VDT + 0x72) : mword 64) 4 = mword_of_int (VDT + 0x76))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp76) in "Hpc".
    assert (HD0a5 : D0 !!! Regidx a5_idx
                    = zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))
      by (rewrite /D0; apply upd_eq).
    (* ---- +0x76: c.addiw a5,1 ---- *)
    iPoseProof (vti_76 with "Htext") as "Hi76".
    iApply (wp_caddiw_s_sconf Φ (mword_of_int (VDT + 0x76)) a5_idx (mword_of_int 1 : mword 6)
              D0 n false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi76 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx a5_idx := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D0).
    iEval (rgne) in "Hcg". iEval (rewrite HD0a5) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D0) with D1.
    assert (Hp78 : add_vec_int (mword_of_int (VDT + 0x76) : mword 64) 2 = mword_of_int (VDT + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp78) in "Hpc".
    assert (HD1a5 : D1 !!! Regidx a5_idx
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec (zero_extend' 64 (wrap16 nr : SailStdpp.Values.mword 16))
                                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
      by (rewrite /D1; apply upd_eq).
    (* ---- +0x78: c.slli a5,0x30 ---- *)
    iPoseProof (vti_78 with "Htext") as "Hi78".
    iApply (wp_cslli_s_sconf Φ (mword_of_int (VDT + 0x78)) (Regidx a5_idx) a5_idx
              (mword_of_int 48 : mword 6) D1 n false eq_refl
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx a5_idx := regval_into_reg
        (shift_bits_left (D1 !!! Regidx a5_idx)
           (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))]> D1).
    change (<[Regidx a5_idx := regval_into_reg
        (shift_bits_left (D1 !!! Regidx a5_idx)
           (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))]> D1) with D2.
    assert (Hp7a : add_vec_int (mword_of_int (VDT + 0x78) : mword 64) 2 = mword_of_int (VDT + 0x7a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7a) in "Hpc".
    assert (HD2a5 : D2 !!! Regidx a5_idx
                    = shift_bits_left (D1 !!! Regidx a5_idx)
                        (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
      by (rewrite /D2; apply upd_eq).
    (* ---- +0x7a: c.srli a5,0x30 -- the 16-bit wrap ---- *)
    assert (Hcv : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx a5_idx)
      by (vm_compute; reflexivity).
    iPoseProof (vti_7a with "Htext") as "Hi7a".
    iEval (rewrite Hcv) in "Hi7a".
    iApply (wp_csrli_s_sconf Φ (mword_of_int (VDT + 0x7a)) (Cregidx (mword_of_int 7)) a5_idx
              (mword_of_int 48 : mword 6) D2 n false Hcv
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (HD3v : shift_bits_right (rget D2 a5_idx)
                     (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
                   = (zero_extend' 64 (wrap16 (S nr) : SailStdpp.Values.mword 16) : mword 64)).
    { rgne. rewrite HD2a5 HD1a5. apply vt_used_idx_next. }
    set (D3 := <[Regidx a5_idx := regval_into_reg
        (zero_extend' 64 (wrap16 (S nr) : SailStdpp.Values.mword 16) : mword 64)]> D2).
    iEval (rewrite HD3v) in "Hcg".
    change (<[Regidx a5_idx := regval_into_reg
        (zero_extend' 64 (wrap16 (S nr) : SailStdpp.Values.mword 16) : mword 64)]> D2) with D3.
    assert (Hp7c : add_vec_int (mword_of_int (VDT + 0x7a) : mword 64) 2 = mword_of_int (VDT + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    assert (HD3a5 : D3 !!! Regidx a5_idx
                    = (zero_extend' 64 (wrap16 (S nr) : SailStdpp.Values.mword 16) : mword 64))
      by (rewrite /D3; apply upd_eq).
    assert (HD3s1 : D3 !!! Regidx s1_idx = (disk_base : mword 64)).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
      rewrite /D1 upd_ne; [| reg_neq]. rewrite /D0 upd_ne; [| reg_neq]. exact HMs1. }
    (* ---- +0x7c: sh a5,32(s1) -- disk.used_idx = nr+1 ---- *)
    assert (Huidx3 : add_vec (rget D3 s1_idx) (sign_extend' 64 (mword_of_int 32 : mword 12))
                     = (d_used_idx : mword 64)).
    { rgne. rewrite HD3s1 vt_sext_32. reflexivity. }
    iPoseProof (vti_7c with "Htext") as "Hi7c".
    iApply (wp_sh_s_sconf Φ (mword_of_int (VDT + 0x7c)) a5_idx s1_idx
              (mword_of_int 32 : mword 12) D3 n (wrap16 nr) false
              with "Hcg Hpc Hi7c [Hidx] [-]").
    { iEval (rewrite Huidx3). iExact "Hidx". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hidx".
    iEval (rewrite Huidx3) in "Hidx". iEval (rgne) in "Hidx".
    iEval (rewrite HD3a5 vt_trunc16_zext) in "Hidx".
    assert (Hp80 : add_vec_int (mword_of_int (VDT + 0x7c) : mword 64) 4 = mword_of_int (VDT + 0x80))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp80) in "Hpc".
    (* ---- +0x80: c.ld a4,16(s1) ---- *)
    assert (Hup : add_vec (rget D3 s1_idx) (sign_extend' 64 (mword_of_int 16 : mword 12))
                  = (d_used_ptr : mword 64)).
    { rgne. rewrite HD3s1 vt_sext_16. reflexivity. }
    iPoseProof (vti_80 with "Htext") as "Hi80".
    iApply (wp_cld_s_sconf Φ (mword_of_int (VDT + 0x80)) a4_idx s1_idx
              (mword_of_int 16 : mword 12) D3 n pu false (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi80 [] [-]").
    { iEval (rewrite Hup). iExact "Hup". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc _".
    set (D4 := <[Regidx a4_idx := regval_into_reg pu]> D3).
    change (<[Regidx a4_idx := regval_into_reg pu]> D3) with D4.
    assert (Hp82 : add_vec_int (mword_of_int (VDT + 0x80) : mword 64) 2 = mword_of_int (VDT + 0x82))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp82) in "Hpc".
    (* ---- +0x82: lhu a4,2(a4) -- the device's used->idx ---- *)
    assert (HD4a4 : D4 !!! Regidx a4_idx = pu) by (rewrite /D4; apply upd_eq).
    assert (Hued : add_vec (rget D4 a4_idx) (sign_extend' 64 (mword_of_int 2 : mword 12))
                   = (pa_add pu 2%nat : SailStdpp.Values.mword 64)).
    { rgne. rewrite HD4a4 vt_sext_2. reflexivity. }
    iPoseProof (vti_82 with "Htext") as "Hi82".
    iApply (wp_vt_lhu_used_idx γu γd Φ pd pav pu (mword_of_int (VDT + 0x82))
              a4_idx a4_idx (mword_of_int 2 : mword 12) D4 n np (S nr) pp Hued
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 Hdinv Hgeom Hpub Hlbs [-]").
    iIntros (nc) "%Hbnd #Hlbc Hpub Hcg Hpc".
    set (D5 := <[Regidx a4_idx := regval_into_reg
        (zero_extend' 64 (wrap16 nc : SailStdpp.Values.mword 16))]> D4).
    change (<[Regidx a4_idx := regval_into_reg
        (zero_extend' 64 (wrap16 nc : SailStdpp.Values.mword 16))]> D4) with D5.
    assert (Hp86 : add_vec_int (mword_of_int (VDT + 0x82) : mword 64) 4 = mword_of_int (VDT + 0x86))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp86) in "Hpc".
    iApply ("Hcont" $! D5 nc with "[%] [%] Hlbc Hcg Hpc Hpub Hidx").
    { split_and!.
      - rewrite /D5 upd_ne; [| reg_neq]. exact HD3a5.
      - rewrite /D5. apply upd_eq.
      - intros r N4 N5.
        rewrite /D5 upd_ne; [| congruence].
        rewrite /D4 upd_ne; [| congruence].
        rewrite /D3 upd_ne; [| congruence].
        rewrite /D2 upd_ne; [| congruence].
        rewrite /D1 upd_ne; [| congruence].
        rewrite /D0 upd_ne; [| congruence]. reflexivity. }
    { exact Hbnd. }
  Qed.

End VtBody.

(* ===================================================================== *)
(* §8  The loop's register invariant, its exit continuation, and the      *)
(*     Löb-quantified loop proposition.                                   *)
(* ===================================================================== *)

(* NOTE: no tp conjunct.  The register file PINS tp (HartTp.v), so a
   statement about the map's tp slot says nothing observable. *)
Definition vt_regs_ok (m MB : regfile) (sp0 : mword 64) : Prop :=
  MB !!! Regidx csp_rs1
    = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
  /\ MB !!! Regidx (mword_of_int 9 : mword 5) = (disk_base : mword 64)
  /\ (forall r : mword 5, is_cs_idx r = true ->
        r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
        MB !!! Regidx r = m !!! Regidx r).

Section VtLoopDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition vt_exit (Φ : mval -> iProp Σ) (γd : disk_names)
      (pd pav pu : mword 64) (m : regfile) (av lvl : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (sp0 : mword 64) : iProp Σ :=
    (∀ MB : regfile,
       ⌜ vt_regs_ok m MB sp0 ⌝ -∗
       sie_cap_gpr MB (av - 4)%nat false pme -∗
       pc_is (mword_of_int (VDT + 0x8a) : mword 64) -∗
       cpu_own (S lvl) eb pme C false -∗
       disk_res γd pd pav pu -∗
       WP (Loop : expr riscv_lang) {{ Φ }})%I.

  Definition vt_loop (Φ : mval -> iProp Σ) (γd : disk_names)
      (pd pav pu : mword 64) (m : regfile) (av lvl : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (sp0 : mword 64) : iProp Σ :=
    (∀ MB : regfile,
       ⌜ vt_regs_ok m MB sp0 ⌝ -∗
       sie_cap_gpr MB (av - 4)%nat false pme -∗
       pc_is (mword_of_int (VDT + 0x3e) : mword 64) -∗
       cpu_own (S lvl) eb pme C false -∗
       vt_loop_state γd pd pav pu -∗
       vt_exit Φ γd pd pav pu m av lvl eb pme C sp0 -∗
       WP (Loop : expr riscv_lang) {{ Φ }})%I.

End VtLoopDefs.

(* small pure side conditions of the avail-ring cell's tier bridge *)
Lemma vt_ring_off_lt (q : nat) : (q < 8)%nat -> (Z.of_nat (4 + 2 * q) < 4096)%Z.
Proof. intro H. lia. Qed.

Lemma vt_ring_off_mod2 (q : nat) : (Z.of_nat (4 + 2 * q) `mod` 2 = 0)%Z.
Proof.
  replace (Z.of_nat (4 + 2 * q))%Z with ((2 + Z.of_nat q) * 2)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma vt_ring_off_add_lt (q j : nat) : (q < 8)%nat -> (j < 2)%nat -> (4 + 2 * q + j < 4096)%nat.
Proof. intros Hq Hj. lia. Qed.

Lemma vt_neq_vec_refl (x : mword 64) : neq_vec x x = false.
Proof.
  unfold neq_vec. rewrite (proj2 (eq_vec_true_iff x x) eq_refl). reflexivity.
Qed.

Lemma vt_neq_vec_true (x y : mword 64) : x <> y -> neq_vec x y = true.
Proof.
  intro H. unfold neq_vec. destruct (eq_vec x y) eqn:E; [| reflexivity].
  exfalso. apply H. apply eq_vec_true_iff. exact E.
Qed.

(* ===================================================================== *)
(* §9  THE LOOP (VDT+0x3e .. VDT+0x86), by Löb induction.                 *)
(*                                                                        *)
(*     One iteration: reclaim position [nr] out of the DMA lease, refute  *)
(*     the status panic, clear [b->disk], wake the sleeper, bump          *)
(*     [disk.used_idx], and re-read the device's used index.  The         *)
(*     [disk_res] surgery moves [nr] from the flight map to the parked    *)
(*     map and returns its avail-ring cell to the free ring pool.         *)
(* ===================================================================== *)
Module VtLoopProof (Wakeup : WAKEUP).
Section VtLoopProof.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).
  Notation a4_idx := (mword_of_int 14 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Lemma wp_vt_loop (Φ : mval -> iProp Σ) (γs : list gname)
      (γu : uart_names) (γd : disk_names) (pd pav pu : mword 64)
      (m : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (sp0 : mword 64) :
    (22 <= av)%nat -> length γs = NPROC -> (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    kernel_text -∗ panic_wp_any -∗ procs_inv Φ γs -∗
    dev_inv γu γd -∗ disk_geom γd pd pav pu -∗
    vt_loop Φ γd pd pav pu m av lvl eb pme C sp0.
  Proof.
    intros Hav Hlen Hlvl.
    iIntros "#Htext #Hpanic #Hpi #Hdinv #Hgeom".
    iLöb as "IH". rewrite {2}/vt_loop.
    iIntros (MB) "%Hregs Hcg Hpc Hown Hst Hexit".
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs1 & Hthr).
    iDestruct "Hst" as (np nr fl pk tr fr c) "(%Hbnd & #Hlbc & Hres)".
    destruct Hbnd as [Hnrc Hcnp].
    rewrite /disk_res_at.
    iDestruct "Hres" as "(%Hdomfl & %Hpkb & %Hdomtr & %Hcoh & %Htriok & %Htridisj & %Hfrfree &
                          Hpub & #Hlbnr & Hauth & Hidx & Hfl & Hpk & Hfree & Hring)".
    destruct (vt_flight_at_nr np nr c fl Hdomfl Hnrc Hcnp) as [vv Hb].
    iDestruct (big_sepM_delete _ fl nr vv Hb with "Hfl") as "[Hflb Hfl]".
    set (b := dc_buf vv). set (sl := dc_slot vv). set (pin := dc_pin vv).
    iDestruct "Hflb" as "(%Hlink & Hrcpt & Hbdisk & Hinfob)".
    pose proof Hlink as Hlink2.
    destruct Hlink2 as (h & Hh8 & Hhead & Hstatus & Hbufeq & Hlen1024).
    assert (Hslh : sl_head sl = h)
      by (unfold sl_head; rewrite Hhead; apply Nat2Z.id).
    iEval (rewrite Hslh) in "Hinfob".
    (* ================= CHUNK A: +0x3e .. +0x4e ================= *)
    iApply (wp_vt_reclaim γu γd Φ pd pav pu MB (av - 4)%nat np c nr h sl pin pme
              Hs1 Hnrc Hh8 Hhead
              with "Hcg Htext Hpc Hdinv Hgeom Hpub Hrcpt Hlbc Hidx [-]").
    iIntros (M1) "%Hfr1 %Hspo Hcg Hpc Hidx Hpub #Hlbs Hpay".
    destruct Hfr1 as [HM1a5 HM1thr].
    iDestruct "Hpay" as "(Hpin & Hstat & Hrest)".
    (* ================= CHUNK B: +0x50 .. +0x5e ================= *)
    assert (HM1s1 : M1 !!! Regidx s1_idx = (disk_base : mword 64))
      by (rewrite (HM1thr s1_idx ltac:(reg_neq) ltac:(reg_neq)); exact Hs1).
    iEval (rewrite Hstatus) in "Hstat".
    iApply (wp_vt_status γd Φ pd pav pu M1 (av - 4)%nat h pme HM1s1 HM1a5 Hh8
              with "Hcg Htext Hpc Hgeom Hstat [-]").
    iIntros (M2) "%Hfr2 Hcg Hpc Hstat".
    destruct Hfr2 as [HM2a5 HM2thr].
    (* ================= CHUNK C: +0x60 .. +0x6a ================= *)
    assert (HM2s1 : M2 !!! Regidx s1_idx = (disk_base : mword 64))
      by (rewrite (HM2thr s1_idx ltac:(reg_neq) ltac:(reg_neq)); exact HM1s1).
    iApply (wp_vt_clear_disk Φ M2 (av - 4)%nat h b pme HM2s1 HM2a5 Hh8
              with "Hcg Htext Hpc Hinfob Hbdisk [-]").
    iIntros (M3) "%Hfr3 Hcg Hpc Hinfob Hbdisk".
    destruct Hfr3 as [HM3a0 HM3thr].
    (* ================= +0x6e: jal ra,wakeup ================= *)
    iPoseProof (vti_6e with "Htext") as "Hi6e".
    iApply (wp_jal_s_sconf Φ (mword_of_int (VDT + 0x6e)) ra_idx
              (mword_of_int 2082178 : mword 21) M3 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W := <[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (VDT + 0x6e) : mword 64) 4)]> M3).
    change (<[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (VDT + 0x6e) : mword 64) 4)]> M3) with W.
    assert (Hjwk : add_vec (mword_of_int (VDT + 0x6e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2082178 : mword 21))
                   = mword_of_int KernelSyms.wakeup)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjwk) in "Hpc".
    (* every premise pre-asserted (optimization.md: never inline [ltac:] at
       [wp_wakeup_sconf], whose statement is a [let]-chain) *)
    assert (HWra : W !!! Regidx ra_idx
                   = add_vec_int (mword_of_int (VDT + 0x6e) : mword 64) 4)
      by (rewrite /W; apply upd_eq).
    assert (HWdom : forall r : regidx, r ∈ dom (rf_to_gmap W))
      by (intro r; apply rf_to_gmap_dom).
    assert (HWmc : mycpu_ret (rget W Rtp) = mycpu_ret cid_word)
      by (rewrite rget_tp; reflexivity).
    assert (HWnz : eq_vec (zero_reg : mword 64) (mycpu_ret (rget W Rtp)) = false)
      by (rewrite rget_tp; exact (mycpu_ret_nonzero cid_word tp_ok_cid)).
    assert (HwK : (18 <= av - 4)%nat) by lia.
    assert (Hwlvl : (Z.of_nat (S lvl) + 1 < 2 ^ 31)%Z) by lia.
    iApply (Wakeup.wp_wakeup_sconf Φ W γs (mycpu_ret cid_word) pme (S lvl)
              (av - 4)%nat eb C false HwK HWdom Hlen HWmc HWnz Hwlvl
              with "Hcg Hown Htext Hpc Hpanic Hpi [-]").
    iApply wp_next_off_intro.
    iIntros (MW) "[%HcsW %HdomW] Hcg Hown #Htext2 Hpc".
    assert (Hpc72 : ret_pc (W !!! Regidx ra_idx) = mword_of_int (VDT + 0x72))
      by (rewrite HWra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc72) in "Hpc".
    (* ================= CHUNK E: +0x72 .. +0x82 ================= *)
    assert (HMWs1 : MW !!! Regidx s1_idx = (disk_base : mword 64)).
    { rewrite (callee_saved_lookup HcsW s1_idx ltac:(vm_compute; reflexivity)).
      rewrite /W upd_ne; [| reg_neq].
      rewrite (HM3thr s1_idx ltac:(reg_neq) ltac:(reg_neq)). exact HM2s1. }
    iApply (wp_vt_advance γu γd Φ pd pav pu MW (av - 4)%nat np nr pme HMWs1
              with "Hcg Htext Hpc Hdinv Hgeom Hpub Hlbs Hidx [-]").
    iIntros (M5 nc) "%Hfr5 %Hbnd5 #Hlbc2 Hcg Hpc Hpub Hidx".
    destruct Hfr5 as (HM5a5 & HM5a4 & HM5thr).
    (* ---- the register invariant survives the whole body ---- *)
    assert (Hchain : forall r : mword 5, is_cs_idx r = true ->
                       M5 !!! Regidx r = MB !!! Regidx r).
    { intros r Hcs.
      assert (N0 : r <> a0_idx)
        by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      assert (N1 : r <> ra_idx)
        by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      assert (N4 : r <> a4_idx)
        by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      assert (N5 : r <> a5_idx)
        by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
      rewrite (HM5thr r N4 N5).
      rewrite (callee_saved_lookup HcsW r Hcs).
      rewrite /W upd_ne; [| congruence].
      rewrite (HM3thr r N0 N5).
      rewrite (HM2thr r N4 N5).
      rewrite (HM1thr r N4 N5). reflexivity. }
    assert (HregsM5 : vt_regs_ok m M5 sp0).
    { split_and!.
      - rewrite (Hchain csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - rewrite (Hchain s1_idx ltac:(vm_compute; reflexivity)). exact Hs1.
      - intros r Hcs Ncsp N8 N9.
        rewrite (Hchain r Hcs). exact (Hthr r Hcs Ncsp N8 N9). }
    (* ================= THE disk_res SURGERY ================= *)
    iPoseProof "Hgeom" as "Hgeomd".
    iDestruct (sie_cap_gpr_kmap_claims with "Hcg") as "[#Hkm Hcg]".
    iDestruct (disk_geom_static with "Hgeom") as %(_ & Hstav & _).
    iDestruct (disk_geom_canonical with "Hgeom") as %(_ & Hcanav & _).
    iDestruct "Hgeomd" as "(_ & _ & _ & %Hal0 & _ & _ & _ & _)".
    destruct Hal0 as (_ & Halav & _).
    assert (Hq8 : (nr `mod` 8 < 8)%nat) by (apply Nat.mod_upper_bound; lia).
    (* the avail-ring cell out of the pin *)
    pose proof (spo_ring _ _ _ _ Hspo) as Hspring.
    rewrite (vt_ring_addr pd pav pu nr) in Hspring.
    iDestruct (vt_pin_ring_split (d_ring pav (nr `mod` 8)) (vr_head (vs_req sl)) pin
                 Hspring with "Hpin") as "[Hw2 Hpinr]".
    assert (Hringal : is_aligned_paddr (Physaddr (d_ring pav (nr `mod` 8))) 2 = true).
    { unfold d_ring. apply (vt_aligned_off pav (4 + 2 * (nr `mod` 8))%nat 2 Halav);
        [ apply vt_ring_off_lt; exact Hq8 | reflexivity | reflexivity
        | apply vt_ring_off_mod2 ]. }
    assert (Hst2 : forall j, (j < 2)%nat ->
              kmap_static (svpn_of (pa_add (d_ring pav (nr `mod` 8)) j)) KP_rw).
    { intros j Hj. unfold d_ring. rewrite pa_add_add.
      apply Hstav. apply vt_ring_off_add_lt; [exact Hq8 | exact Hj]. }
    assert (Hcan2 : forall j, (j < 2)%nat ->
              (uint (pa_add (d_ring pav (nr `mod` 8)) j : SailStdpp.Values.mword 64)
               < 274877906944)%Z).
    { intros j Hj. unfold d_ring. rewrite pa_add_add.
      apply Hcanav. apply vt_ring_off_add_lt; [exact Hq8 | exact Hj]. }
    iDestruct (phys_to_word2 (d_ring pav (nr `mod` 8)) (vr_head (vs_req sl))
                 Hringal Hst2 Hcan2 with "Hkm Hw2") as "Hcell".
    (* the ring pool takes it back *)
    assert (Hnrin : nr ∈ dom fl) by (apply elem_of_dom; exists vv; exact Hb).
    assert (Hfl' : dom (delete nr fl) = set_seq (S nr) (np - S nr))
      by (apply vt_dom_delete_seq; [exact Hdomfl | lia]).
    assert (Hwin : (np - nr <= 2)%nat)
      by (apply (vt_window_le np nr fl pk tr); assumption).
    assert (Hfresh : (nr `mod` 8)%nat ∉ mod8 (dom (delete nr fl))).
    { rewrite Hfl'. apply vt_mod8_head_fresh. lia. }
    assert (Hmod8 : mod8 (dom fl) = mod8 (dom (delete nr fl)) ∪ {[ (nr `mod` 8)%nat ]})
      by (apply vt_mod8_split; exact Hnrin).
    iEval (rewrite Hmod8) in "Hring".
    iDestruct (ring_slots_put pav (mod8 (dom (delete nr fl))) (nr `mod` 8)%nat
                 Hq8 Hfresh with "[Hcell] Hring") as "Hring".
    { iExists (vr_head (vs_req sl)). iExact "Hcell". }
    (* the parked payoff *)
    iDestruct "Hrest" as "[Hperm Hrest]".
    iDestruct "Hrest" as (bs) "(%Hbslen & %Hbsout & Hbytes & Hbuf)".
    iAssert (parked_res γd pav nr vv)
      with "[Hbdisk Hinfob Hpinr Hstat Hbytes Hbuf Hperm]" as "Hparked".
    { iExists bs. iEval (rewrite -Hslh) in "Hinfob".
      iEval (rewrite -Hstatus) in "Hstat".
      rewrite /dc_pinr /dc_ring_map.
      iFrame "Hbdisk Hinfob Hpinr Hstat Hbytes Hperm Hbuf".
      iPureIntro. split_and!; [ exact Hlink | exact Hbslen | exact Hbsout ]. }
    (* the maps *)
    assert (Hpknr : pk !! nr = None).
    { apply not_elem_of_dom. intro Hc. pose proof (Hpkb nr Hc). lia. }
    iAssert ([∗ map] p ↦ v ∈ <[nr := vv]> pk, parked_res γd pav p v)%I
      with "[Hparked Hpk]" as "Hpk".
    { rewrite (big_sepM_insert (fun p v => parked_res γd pav p v) pk nr vv Hpknr).
      iFrame "Hparked Hpk". }
    assert (Hunion : delete nr fl ∪ <[nr := vv]> pk = fl ∪ pk)
      by (apply vt_union_move; [exact Hb | exact Hpknr]).
    iEval (rewrite -Hunion) in "Hauth".
    iAssert (disk_res_at γd pd pav pu np (S nr) (delete nr fl) (<[nr := vv]> pk) tr fr)
      with "[Hpub Hauth Hidx Hfl Hpk Hfree Hring]" as "Hres".
    { rewrite /disk_res_at.
      iFrame "Hpub Hlbs Hauth Hidx Hfl Hpk Hfree Hring".
      iPureIntro. split_and!.
      - exact Hfl'.
      - intros p Hp. rewrite dom_insert_L in Hp.
        apply elem_of_union in Hp as [Hp|Hp].
        + apply elem_of_singleton in Hp. lia.
        + pose proof (Hpkb p Hp). lia.
      - rewrite (vt_dom_tr_stable nr fl pk vv Hnrin). exact Hdomtr.
      - rewrite Hunion. exact Hcoh.
      - exact Htriok.
      - exact Htridisj.
      - exact Hfrfree. }
    (* ================= +0x86: bne a4,a5 ================= *)
    iPoseProof (vti_86 with "Htext") as "Hi86".
    destruct (decide ((wrap16 nc : SailStdpp.Values.mword 16) = wrap16 (S nr))) as [Heq|Hne].
    - (* EXIT: the driver has caught up with the device *)
      assert (Hcmp : neq_vec (rget M5 a4_idx) (rget M5 a5_idx) = false).
      { rgne. rgne. rewrite HM5a4 HM5a5 Heq. apply vt_neq_vec_refl. }
      iApply (wp_bne_fall_s_sconf Φ (mword_of_int (VDT + 0x86)) (mword_of_int 8120 : mword 13)
                a5_idx a4_idx M5 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp
                with "Hcg Hpc Hi86 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hp8a : add_vec_int (mword_of_int (VDT + 0x86) : mword 64) 4
                     = mword_of_int (VDT + 0x8a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp8a) in "Hpc".
      iApply ("Hexit" $! M5 with "[%] Hcg Hpc Hown [Hres]").
      { exact HregsM5. }
      { iApply (disk_res_at_intro with "Hres"). }
    - (* BACK EDGE: another completion is visible *)
      assert (Hnrnc : (S nr < nc)%nat).
      { destruct Hbnd5 as [Hle _].
        destruct (decide (nc = S nr)) as [->|Hne2]; [ exfalso; apply Hne; reflexivity |]. lia. }
      assert (Hcmp : neq_vec (rget M5 a4_idx) (rget M5 a5_idx) = true).
      { rgne. rgne. rewrite HM5a4 HM5a5. apply vt_neq_vec_true.
        intro Hc. apply Hne. exact (vt_zext16_inj _ _ Hc). }
      iApply (wp_bne_taken_s_sconf Φ (mword_of_int (VDT + 0x86)) (mword_of_int 8120 : mword 13)
                a5_idx a4_idx M5 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi86 [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hbk : add_vec (mword_of_int (VDT + 0x86) : mword 64)
                      (sign_extend' 64 (mword_of_int 8120 : mword 13))
                    = mword_of_int (VDT + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk) in "Hpc".
      iApply ("IH" $! M5 with "[%] Hcg Hpc Hown [Hres] Hexit").
      { exact HregsM5. }
      { rewrite /vt_loop_state.
        iExists np, (S nr), (delete nr fl), (<[nr := vv]> pk), tr, fr, nc.
        iFrame "Hlbc2 Hres". iPureIntro.
        split; [ exact Hnrnc | exact (proj2 Hbnd5) ]. }
  Qed.

End VtLoopProof.
End VtLoopProof.

(* ===================================================================== *)
(* §10  THE WHOLE FUNCTION: prologue, ISR ack, entry test, loop, release. *)
(* ===================================================================== *)

Lemma vt_lvl_weaken (lvl : nat) :
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z -> (Z.of_nat lvl + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

Module VirtioDiskIntrProof (Acquire : ACQUIRE) (Release : RELEASE) (Wakeup : WAKEUP)
  : VIRTIODISKINTR.

Module Pro := VtPrologue Acquire.
Module Epi := VtEpilogue Release.
Module Lp  := VtLoopProof Wakeup.

Section ProofVirtioDiskIntr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a4_idx := (mword_of_int 14 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.


  Lemma wp_virtio_disk_intr_sconf (Φ : mval -> iProp Σ) (γs : list gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (b : bool)
    : wp_virtio_disk_intr_sconf_body Φ γs γu γd γk pd pav pu m K lvl eb pme C b.
  Proof.
    cbv beta delta [wp_virtio_disk_intr_sconf_body].
    intros pcE ret_tgt HK Hdom Hlen Hlvl.
    assert (HKav : (22 <= K)%nat) by (unfold K_virtio_disk_intr in HK; exact HK).
    pose proof (vt_lvl_weaken lvl Hlvl) as Hlvl1.
    iIntros "Hcg Hown #Htext Hpc #Hpanic #Hpi #Hdinv #Hgeom #Hlk Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbeq.
    (* ===================== PROLOGUE + acquire ===================== *)
    iApply (Pro.wp_vt_prologue γk γd Φ pd pav pu m K lvl eb pme C b
              Hlvl1 HKav
              with "Hcg Hown Htext Hpc Hpanic Hlk [-]").
    iIntros (CIDa Hsa MA sp0) "%Hpro Hcg Hpc Htok HR Hown Hpay Hr24 Hr16 Hr8 Hgap".
    destruct Hpro as (Hsp0 & HMAcsp & HMAs1 & HMAthr).
    (* ===================== the ISR read/ack ===================== *)
    iApply (wp_vt_isr γu γd Φ MA (K - 4)%nat pme with "Hcg Htext Hpc Hdinv [-]").
    iIntros (MI) "%HMIthr Hcg Hpc".
    (* ---- the exit continuation, capturing the epilogue's resources ---- *)
    iAssert (vt_exit (CID:=CIDa) Φ γd pd pav pu m K lvl eb pme C sp0)
      with "[Hcont Htok Hpay Hr24 Hr16 Hr8 Hgap]" as "Hexit".
    { iIntros (MB) "%HregsB Hcg Hpc Hown HR".
      destruct HregsB as (HBcsp & HBs1 & HBthr).
      iApply (Epi.wp_vt_epilogue (CID:=CIDa) γk γd Φ pd pav pu m MB K lvl eb pme C sp0 b
                Hsp0 HBcsp HBthr HKav Hbeq
                with "Hcg Htext Hpc Hlk Htok HR Hown Hpay Hr24 Hr16 Hr8 Hgap [-]").
      iIntros (CIDz Hsz MF HcsF) "Hcg Hown Hpc".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! MF with "[%] Hcg Hown Htext Hpc").
      split; [exact HcsF | intro r; apply rf_to_gmap_dom]. }
    (* ===================== the loop-entry test ===================== *)
    assert (HMIs1 : MI !!! Regidx s1_idx = (disk_base : mword 64))
      by (rewrite (HMIthr s1_idx ltac:(reg_neq) ltac:(reg_neq)); exact HMAs1).
    iDestruct (disk_res_at_elim with "HR") as (np nr fl pk tr fr) "Hres".
    rewrite /disk_res_at.
    iDestruct "Hres" as "(%Hdomfl & %Hpkb & %Hdomtr & %Hcoh & %Htriok & %Htridisj & %Hfrfree &
                          Hpub & #Hlbnr & Hauth & Hidx & Hfl & Hpk & Hfree & Hring)".
    iApply (wp_vt_entry_test γu γd Φ pd pav pu MI (K - 4)%nat np nr pme HMIs1
              with "Hcg Htext Hpc Hdinv Hgeom Hpub Hlbnr Hidx [-]").
    iSplit.
    - (* ---- the loop is never entered: straight to release ---- *)
      iIntros (ME) "%HMEthr Hcg Hpc Hpub Hidx".
      iApply ("Hexit" $! ME with "[%] Hcg Hpc Hown [Hpub Hauth Hidx Hfl Hpk Hfree Hring]").
      { split_and!.
        - rewrite (HMEthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq)).
          rewrite (HMIthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq)). exact HMAcsp.
        - rewrite (HMEthr s1_idx ltac:(reg_neq) ltac:(reg_neq)). exact HMIs1.
        - intros r Hcs Ncsp N8 N9.
          assert (N4 : r <> a4_idx)
            by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
          assert (N5 : r <> a5_idx)
            by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
          rewrite (HMEthr r N4 N5). rewrite (HMIthr r N4 N5).
          exact (HMAthr r Hcs Ncsp N8 N9). }
      { iApply (disk_res_at_intro γd pd pav pu np nr fl pk tr fr). rewrite /disk_res_at.
        iFrame "Hpub Hlbnr Hauth Hidx Hfl Hpk Hfree Hring".
        iPureIntro. split_and!; assumption. }
    - (* ---- the loop is entered ---- *)
      iIntros (ME nc) "%HMEthr %Hbnd #Hlbc Hcg Hpc Hpub Hidx".
      iPoseProof (Lp.wp_vt_loop (CID:=CIDa) Φ γs γu γd pd pav pu m K lvl eb pme C sp0
                    HKav Hlen Hlvl
                    with "Htext Hpanic Hpi Hdinv Hgeom") as "Hloop".
      iApply ("Hloop" $! ME with "[%] Hcg Hpc Hown [Hpub Hauth Hidx Hfl Hpk Hfree Hring] Hexit").
      { split_and!.
        - rewrite (HMEthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq)).
          rewrite (HMIthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq)). exact HMAcsp.
        - rewrite (HMEthr s1_idx ltac:(reg_neq) ltac:(reg_neq)). exact HMIs1.
        - intros r Hcs Ncsp N8 N9.
          assert (N4 : r <> a4_idx)
            by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
          assert (N5 : r <> a5_idx)
            by (intro He; rewrite He in Hcs; vm_compute in Hcs; discriminate).
          rewrite (HMEthr r N4 N5). rewrite (HMIthr r N4 N5).
          exact (HMAthr r Hcs Ncsp N8 N9). }
      { rewrite /vt_loop_state.
        iExists np, nr, fl, pk, tr, fr, nc. iFrame "Hlbc".
        iSplitR; [iPureIntro; exact Hbnd|].
        rewrite /disk_res_at.
        iFrame "Hpub Hlbnr Hauth Hidx Hfl Hpk Hfree Hring".
        iPureIntro. split_and!; assumption. }
  Qed.

End ProofVirtioDiskIntr.
End VirtioDiskIntrProof.
