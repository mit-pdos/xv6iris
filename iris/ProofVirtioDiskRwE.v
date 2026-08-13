(* ProofVirtioDiskRwE.v -- virtio_disk_rw, phase P5: the device kick and the
   completion wait (+0x19a .. +0x1d2).

   The continuation of ProofVirtioDiskRwD.v, which proves P4 and leaves the
   seam [VirtioDiskRwRestD.vdrw_p4_exit] at +0x19a.

     0x19a lui  a5,0x10001
     0x19e sw   x0,80(a5)     *R(QUEUE_NOTIFY) = 0   -- kick the device
     0x1a2 lw   a5,4(s3)      a5 = b->disk
     0x1a6 auipc s1,0x1e ; 0x1aa addi s1,s1,3138     s1 = &disk.vdisk_lock
     0x1ae c.mv s2,a1         s2 = 1   (a1 has held 1 since +0x104)
     0x1b0 bne  a5,a1,+34     b->disk != 1 -> +0x1d2 (done)
     -- the completion-wait loop, head at +0x1b4 --
     0x1b4 c.mv a0,s3 ; 0x1b6 jal sleep_prepare(b)
     0x1ba c.mv a0,s1 ; 0x1bc jal release(&vdisk_lock)
     0x1c0 jal sleep()
     0x1c4 c.mv a0,s1 ; 0x1c6 jal acquire(&vdisk_lock)
     0x1ca lw   a5,4(s3)
     0x1ce beq  a5,s2,-26     still 1 -> back to +0x1b4

   THE SLEEP PROTOCOL IS SPLIT (SpecSleep.v's header): the caller drops and
   retakes [disk.vdisk_lock] itself, so this loop body is four calls rather
   than one, and the window between its release and its re-acquire is the
   one across which the exclusive claim fragment must survive.

   THE ONE INTERESTING STEP is the [b->disk] load.  That cell is not the
   caller's: it lives INSIDE the lock's resource, in the position's flight
   entry (value 1) or its parked entry (value 0), and which of the two it is
   is exactly the branch the code takes.  The publisher re-finds its own
   position with the CLAIM fragment ([DiskInv.disk_claim_agree] against the
   claim auth inside the body), borrows the cell out of the matching big-op
   with [big_sepM_lookup_acc], and puts it straight back -- the whole
   resource has to be closed again for [sleep], which takes it as the
   condition lock's [Rk].

   So the loop needs no invariant of its own beyond "the lock is held and
   the claim still names a live position": the branch condition is READ OFF
   the resource at each iteration, and the exit case is precisely the one in
   which the claim lands in [pk].  That pure fact -- [pk !! q = Some V] -- is
   what P5 hands P6, which then withdraws the parked payoff.

   P6 (+0x1d2 .. +0x234) follows in ProofVirtioDiskRwF.v.
   The whole function is composed and sealed in ProofVirtioDiskRwF.v
   ([Module VirtioDiskRwProof … : VIRTIODISKRW]) and instantiated in
   LinkVirtioDiskRw.v.  Everything here is Qed-closed.
 *)
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
Require Import WpGpr RegFile.
Require Import KptPt.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import ProcGeom.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn SchedCtx FdSlots.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import VirtioModel DiskPtsto VirtioProto DiskInv.
Require Import VirtioModel.
Require Import WpVirtioDev.
Require Import WpUart.
Require Import SpecPanic.
Require Import SpecAcquire SpecRelease SpecSleepPrepare SpecSleep SpecFreeDesc.
Require Import CodeVirtioDiskRw.
Require Import SpecVirtioDiskRw.
Require Import VirtioDiskRwDefs.
Require Import ProofVirtioDiskRwD ProofVirtioDiskRwDSeam.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).

(* ===================================================================== *)
(* §0  Pure helpers: the addresses and immediates of the nine             *)
(*     instructions, all closed [vm_compute]s.                            *)
(* ===================================================================== *)

Lemma vdrwe_addv_zero (x : SailStdpp.Values.mword 64) : add_vec zero_reg x = x.
Proof.
  rewrite (add_vec64_comm zero_reg x).
  apply bv_add_0_r. vm_compute. reflexivity.
Qed.

(* [lui a5,0x10001] *)
Lemma vdrwe_lui : luival (mword_of_int 65537 : mword 20)
                  = (mword_of_int 0x10001000 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the QUEUE_NOTIFY address, [80(a5)] *)
Lemma vdrwe_notify_addr :
  add_vec (mword_of_int 0x10001000 : SailStdpp.Values.mword 64)
          (sign_extend' 64 (mword_of_int 80 : mword 12))
  = (mword_of_int 0x10001050 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwe_notify_geom :
  (virtio_base <= uint (mword_of_int 0x10001050 : SailStdpp.Values.mword 64)
   < virtio_base + virtio_size)%Z
  /\ is_aligned_vaddr (Virtaddr (mword_of_int 0x10001050 : SailStdpp.Values.mword 64)) 4 = true
  /\ neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x10001050 : SailStdpp.Values.mword 64)))
       (sign_extend' 64 (subrange_vec_dec
          (bits_of_virtaddr (Virtaddr (mword_of_int 0x10001050 : SailStdpp.Values.mword 64)))
          (Z.sub 39 1) 0)) = false
  /\ kpt_dev_vpn (svpn_of (mword_of_int 0x10001050 : SailStdpp.Values.mword 64)).
Proof.
  split_and!.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Z.ltb_lt. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold kpt_dev_vpn. split.
    + apply Z.leb_le. vm_compute. reflexivity.
    + apply Z.ltb_lt. vm_compute. reflexivity.
Qed.

Lemma vdrwe_notify_off :
  (uint (mword_of_int 0x10001050 : SailStdpp.Values.mword 64) - virtio_base)%Z
  = vio_off_queue_notify.
Proof. vm_compute. reflexivity. Qed.

(* the [4(s3)] displacement onto [b->disk] *)
Lemma vdrwe_sext4 :
  sign_extend' 64 (mword_of_int 4 : mword 12) = (mword_of_int 4 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwe_bdisk_addr (b : Arch.pa) :
  add_vec (b : SailStdpp.Values.mword 64) (sign_extend' 64 (mword_of_int 4 : mword 12))
  = (b_disk b : SailStdpp.Values.mword 64).
Proof.
  rewrite vdrwe_sext4. unfold b_disk.
  rewrite (vdrw_pa_add_moi b 4). reflexivity.
Qed.

(* the two values [b->disk] can hold, normalised after the load's sign
   extension, and their comparison against [a1 = 1] *)
Lemma vdrwe_sext_one :
  sign_extend' 64 (SailStdpp.Values.mword_of_int (len := 32) 1)
  = (mword_of_int 1 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwe_sext_zero :
  sign_extend' 64 (SailStdpp.Values.mword_of_int (len := 32) 0)
  = (mword_of_int 0 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwe_eq_one :
  eq_vec (mword_of_int 1 : SailStdpp.Values.mword 64)
         (mword_of_int 1 : SailStdpp.Values.mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vdrwe_neq_zero_one :
  neq_vec (mword_of_int 0 : SailStdpp.Values.mword 64)
          (mword_of_int 1 : SailStdpp.Values.mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vdrwe_eq_zero_one :
  eq_vec (mword_of_int 0 : SailStdpp.Values.mword 64)
         (mword_of_int 1 : SailStdpp.Values.mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vdrwe_neq_one :
  neq_vec (mword_of_int 1 : SailStdpp.Values.mword 64)
          (mword_of_int 1 : SailStdpp.Values.mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* §1  P5 and the P4 -> P5 glue.                                          *)
(*                                                                       *)
(* P5 calls [sleep], so -- unlike P3/P4 -- the phase itself has to live   *)
(* inside the functor.                                                    *)
(* ===================================================================== *)

Module VirtioDiskRwRestE (Acquire : ACQUIRE) (Release : RELEASE)
                         (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) (FreeDesc : FREEDESC).

Module P4 := VirtioDiskRwRestD Acquire Release SleepPrepare Sleep FreeDesc.

Section ProofVirtioDiskRwE.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Notation Rra := (mword_of_int 1  : mword 5).
  Notation Rtp := (mword_of_int 4  : mword 5).
  Notation Rs0 := (mword_of_int 8  : mword 5).
  Notation Rs1 := (mword_of_int 9  : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  (* ------------------------------------------------------------------- *)
  (* THE P5/P6 SEAM at +0x1d2.                                            *)
  (*                                                                      *)
  (* Identical to [P4.vdrw_p4_exit] except that (a) the pc is +0x1d2 and   *)
  (* (b) it adds the pure fact the wait established: the claim's position  *)
  (* is PARKED, i.e. the interrupt handler has already deposited the       *)
  (* payoff.  P6 withdraws it from [pk] with nothing further to check.     *)
  (* Note that s1/s2 are NOT pinned: +0x1d2 reloads [idx[0]] into s2 and   *)
  (* P6 never reads s1 again.                                             *)
  (* ------------------------------------------------------------------- *)
  Definition vdrw_p5_exit (CID0 : CPU) (γk : gname) 
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (bs_buf bs_disk : list (bv 8)) (m0 : regfile)
      (kq : nat * positive) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (q np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) (h m2 t : nat) pin,
       ⌜vdrw_regs M sp0 b wr sector /\ vdrw_hi M m0⌝ -∗
       ⌜tri_ok (h, m2, t)⌝ -∗
       ⌜pk !! q = Some (DClaim b (vdrwd_slot kq b h wr sector
                                    (vdrwd_sldata wr bs_buf bs_disk))
                               (h, m2, t) pin)⌝ -∗
       ⌜pin ∖ range_map (d_ring pav (q `mod` 8)) 2
                (nth_byte (Z_to_bv 16 (Z.of_nat h)))
         = foldr union ∅ (vdrwd_pinr_regions pd b h m2 t wr sector
                            (vdrwd_bufwin b wr bs_buf))
        /\ pm_ok (vdrwd_pinr_regions pd b h m2 t wr sector
                    (vdrwd_bufwin b wr bs_buf))⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
        /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
       sie_cap_gpr M (trap_res eb + (K - 12))%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) C false -∗
       trap_csrs -∗
       cpu_claim (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x1d2) : mword 64) -∗
       locked γk cpu_id -∗
       vdrw_body γd pd pav np nr fl pk tr fr -∗
       disk_claim γd q (DClaim b (vdrwd_slot kq b h wr sector
                                    (vdrwd_sldata wr bs_buf bs_disk))
                               (h, m2, t) pin) -∗
       vdrw_slot_rest m2 -∗ vdrw_slot_rest t -∗
       vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       WP (Loop : expr riscv_lang)))%I.

  (* what the completion-wait loop head at +0x1b4 consumes.  The lock's
     resource is CLOSED here (sleep takes it as [Rk]); the only thing that
     survives an iteration besides the register discipline is the claim. *)
  Definition vdrw_p5_loop (CID0 : CPU) (γk : gname)
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (bs_buf bs_disk : list (bv 8)) (h m2 t : nat) (q : nat) (pin : _)
      (m0 : regfile) (kq : nat * positive) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ M : regfile,
       ⌜vdrw_regs M sp0 b wr sector
        /\ M !!! Regidx Rs1 = (d_lock : SailStdpp.Values.mword 64)
        /\ M !!! Regidx Rs2 = (mword_of_int 1 : SailStdpp.Values.mword 64)
        /\ vdrw_hi M m0⌝ -∗
       sie_cap_gpr M (trap_res eb + (K - 12))%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) C false -∗
       trap_csrs -∗
       cpu_claim (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b4) : mword 64) -∗
       locked γk cpu_id -∗
       disk_res γd pd pav pu -∗
       disk_claim γd q (DClaim b (vdrwd_slot kq b h wr sector
                                    (vdrwd_sldata wr bs_buf bs_disk))
                               (h, m2, t) pin) -∗
       vdrw_slot_rest m2 -∗ vdrw_slot_rest t -∗
       vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       ⌜tri_ok (h, m2, t)⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
        /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
       ⌜pin ∖ range_map (d_ring pav (q `mod` 8)) 2
                (nth_byte (Z_to_bv 16 (Z.of_nat h)))
         = foldr union ∅ (vdrwd_pinr_regions pd b h m2 t wr sector
                            (vdrwd_bufwin b wr bs_buf))
        /\ pm_ok (vdrwd_pinr_regions pd b h m2 t wr sector
                    (vdrwd_bufwin b wr bs_buf))⌝ -∗
       vdrw_p5_exit CID0 γk γs j γd pd pav pu K eb C sp0 b wr sector bs_buf bs_disk m0 kq -∗
       WP (Loop : expr riscv_lang)))%I.

  (* ------------------------------------------------------------------- *)
  (* Borrowing [b->disk] out of the lock's resource.                       *)
  (*                                                                      *)
  (* [disk_claim_agree] splits on where the claim lands; each side hands   *)
  (* back the cell at its known value together with the wand that puts     *)
  (* the whole body together again.  Only the PARKED side exports the      *)
  (* lookup fact -- that is what tells the branch it may leave.            *)
  (* ------------------------------------------------------------------- *)
  Lemma vdrw_p5_peek (γd : disk_names) (pd pav : SailStdpp.Values.mword 64)
      (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool)
      (q : nat) (V : dclaim) :
    vdrw_body γd pd pav np nr fl pk tr fr -∗
    disk_claim γd q V -∗
    ∃ dv : SailStdpp.Values.mword 32,
      ⌜dv = SailStdpp.Values.mword_of_int (len := 32) 1
       \/ (dv = SailStdpp.Values.mword_of_int (len := 32) 0 /\ pk !! q = Some V)⌝ ∗
      b_disk (dc_buf V) ↦₄ dv ∗
      (b_disk (dc_buf V) ↦₄ dv -∗
       vdrw_body γd pd pav np nr fl pk tr fr ∗ disk_claim γd q V).
  Proof.
    iIntros "Hbody Hclaim". rewrite /vdrw_body.
    iDestruct "Hbody" as "(%Hdfl & %Hpkb & %Hdtr & %Hcoh & %Htrok & %Htrdj & %Htrfr &
                           Hpub & Hlb & Hcl & Huidx & Hflm & Hpkm & Hfb & Hring)".
    iDestruct (disk_claim_agree γd q V fl pk with "Hcl Hclaim") as %[Hf | [_ Hp]].
    - (* IN FLIGHT: the cell reads 1 *)
      iDestruct (big_sepM_lookup_acc (fun p v => flight_res γd p v) fl q V Hf
                   with "Hflm") as "[Hfe Hback]".
      iDestruct "Hfe" as "(%Hlink & Hrcpt & Hbd & Hib)".
      iExists (SailStdpp.Values.mword_of_int (len := 32) 1).
      iSplitR; [iPureIntro; left; reflexivity|].
      iFrame "Hbd". iIntros "Hbd". iFrame "Hclaim".
      iSplitR; [iPureIntro; exact Hdfl|].
      iSplitR; [iPureIntro; exact Hpkb|].
      iSplitR; [iPureIntro; exact Hdtr|].
      iSplitR; [iPureIntro; exact Hcoh|].
      iSplitR; [iPureIntro; exact Htrok|].
      iSplitR; [iPureIntro; exact Htrdj|].
      iSplitR; [iPureIntro; exact Htrfr|].
      iFrame "Hpub Hlb Hcl Huidx Hpkm Hfb Hring".
      iApply "Hback". iFrame "Hrcpt Hbd Hib". iPureIntro. exact Hlink.
    - (* PARKED: the cell reads 0, and P6 may collect *)
      iDestruct (big_sepM_lookup_acc (fun p v => parked_res γd pav p v) pk q V Hp
                   with "Hpkm") as "[Hpe Hback]".
      rewrite /parked_res.
      iDestruct "Hpe" as (bs) "(%Hlink & %Hlen & %Hout & Hbd & Hib & Hpinr & Hstat & Hbytes & Hbuf)".
      iExists (SailStdpp.Values.mword_of_int (len := 32) 0).
      iSplitR; [iPureIntro; right; split; [reflexivity | exact Hp]|].
      iFrame "Hbd". iIntros "Hbd". iFrame "Hclaim".
      iSplitR; [iPureIntro; exact Hdfl|].
      iSplitR; [iPureIntro; exact Hpkb|].
      iSplitR; [iPureIntro; exact Hdtr|].
      iSplitR; [iPureIntro; exact Hcoh|].
      iSplitR; [iPureIntro; exact Htrok|].
      iSplitR; [iPureIntro; exact Htrdj|].
      iSplitR; [iPureIntro; exact Htrfr|].
      iFrame "Hpub Hlb Hcl Huidx Hflm Hfb Hring".
      iApply "Hback". iExists bs.
      iFrame "Hbd Hib Hpinr Hstat Hbytes Hbuf".
      iPureIntro. split_and!; assumption.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* P5, packaged as the wand P4 consumes.                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_vdrw_p5_seam (γk : gname)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (bs_buf bs_disk : list (bv 8)) (m0 : regfile) (kq : nat * positive) :
    (K_virtio_disk_rw <= K)%nat ->
    (j < NPROC)%nat -> γs !! j = Some γl ->
    (* THE BUFFER POINTER IS NON-NULL.  [sleep_prepare] panics on a zero
       channel, and the channel here IS [b].  The caller supplies this out of
       the spec's [addr_is_kdata (pa_add (b_data b) k)] premise
       ([ProofVirtioDiskRwF.vdrwf_bnz]); it is not derivable from anything
       this phase holds, because a points-to says nothing about the address. *)
    eq_vec (b : SailStdpp.Values.mword 64) (zero_reg : SailStdpp.Values.mword 64) = false ->
    kernel_text -∗
    panic_wp_any -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    vdrw_p5_exit CID γk γs j γd pd pav pu K eb C sp0 b wr sector bs_buf bs_disk
                 m0 kq -∗
    P4.vdrw_p4_exit CID γk γs j γd pd pav pu K eb C sp0 b wr sector bs_buf
                    bs_disk m0 kq.
  Proof.
    intros HK Hj Hjl Hbnz.
    iIntros "#Htext #Hpanic #Hpinv #Hdinv #Hlk Hexit".
    rewrite /P4.vdrw_p4_exit.
    iIntros (CIDx Hsx M q np nr fl pk tr fr h m2 t pin)
            "%Hrh %Ha1 %Hok %Hpinr %Hal Hcg Hown Htc Hclm Hpc Htok Hbody Hclaim Hrm Hrt Hidx".
    destruct Hrh as (Hregs & Hhi).
    set (V := DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk))
                     (h, m2, t) pin).
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
    iPoseProof (rwi_19a with "Htext") as "Hi186".
    iPoseProof (rwi_19e with "Htext") as "Hi18a".
    iPoseProof (rwi_1a2 with "Htext") as "Hi18e".
    iPoseProof (rwi_1a6 with "Htext") as "Hi192".
    iPoseProof (rwi_1aa with "Htext") as "Hi196".
    iPoseProof (rwi_1ae with "Htext") as "Hi19a".
    iPoseProof (rwi_1b0 with "Htext") as "Hi19c".
    (* ================= THE LOOP, first (it is used by both arms) ======= *)
    iAssert (vdrw_p5_loop CID γk γs j γd pd pav pu K eb C sp0 b wr sector
               bs_buf bs_disk h m2 t q pin m0 kq)%I with "[]" as "Hloop".
    { iLöb as "IH". rewrite {2}/vdrw_p5_loop.
      iIntros (CIDlp Hslp M') "%Hinv Hcg Hown Htc Hclm Hpc Htok HR Hclaim Hrm Hrt Hidx
                    %HokL %HalL %HpinrL HexitL".
      destruct Hinv as (HregsL & Hs1L & Hs2L & HhiL).
      pose proof HregsL as HregsL'.
      destruct HregsL' as (HspL & Hs0L & Hs3L & Hs6L & Hs7L).
      iPoseProof (rwi_1b4 with "Htext") as "Hi1b4".
      iPoseProof (rwi_1b6 with "Htext") as "Hi1b6".
      iPoseProof (rwi_1ba with "Htext") as "Hi1ba".
      iPoseProof (rwi_1bc with "Htext") as "Hi1bc".
      iPoseProof (rwi_1c0 with "Htext") as "Hi1c0".
      iPoseProof (rwi_1c4 with "Htext") as "Hi1c4".
      iPoseProof (rwi_1c6 with "Htext") as "Hi1c6".
      iPoseProof (rwi_1ca with "Htext") as "Hi1a8".
      iPoseProof (rwi_1ce with "Htext") as "Hi1ac".
      (* =============================================================== *)
      (* THE SLEEP PROTOCOL, IN FOUR CALLS -- see ProofVirtioDiskRwB.v.  *)
      (*   +0x1b4/+0x1b6  a0 := b;             sleep_prepare(a0)         *)
      (*   +0x1ba/+0x1bc  a0 := &vdisk_lock;   release(a0)               *)
      (*   +0x1c0                              sleep()                   *)
      (*   +0x1c4/+0x1c6  a0 := &vdisk_lock;   acquire(a0)               *)
      (* The pair is still CARRIED by the loop predicates; it is SPLIT    *)
      (* across the window ([arm_pay] into release's pop_off, the         *)
      (* complement into sleep) and rejoined out of acquire's push_off.   *)
      (* =============================================================== *)
      (* ---- +0x1b4  c.mv a0,s3 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b4) : mword 64) Ra0 Rs3 M'
                (trap_res eb + (K - 12))%nat false ltac:(vm_compute; discriminate)
                ltac:(rdok) with "Hcg Hpc Hi1b4").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (W1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (M' !!! Regidx Rs3))]> M').
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (M' !!! Regidx Rs3))]> M') with W1.
      assert (HW1a0 : W1 !!! Regidx Ra0 = (b : SailStdpp.Values.mword 64)).
      { rewrite /W1 upd_eq vdrwe_addv_zero. exact Hs3L. }
      assert (Hp1b6 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b4) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1b6)) by pcstep.
      iEval (rewrite Hp1b6) in "Hpc".
      (* ---- +0x1b6  jal ra,sleep_prepare ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b6) : mword 64) Rra
                (mword_of_int 2082076 : mword 21) W1 (trap_res eb + (K - 12))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1b6").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (W2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b6) : mword 64) 4)]> W1).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b6) : mword 64) 4)]> W1) with W2.
      assert (Hjsp : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b6) : mword 64)
                       (sign_extend' 64 (mword_of_int 2082076 : mword 21))
                     = mword_of_int KernelSyms.sleep_prepare) by pcstep.
      iEval (rewrite Hjsp) in "Hpc".
      assert (HW2ra : W2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b6) : mword 64) 4)
        by (rewrite /W2; apply upd_eq).
      assert (HW2a0 : W2 !!! Regidx Ra0 = (b : SailStdpp.Values.mword 64)).
      { rewrite /W2 upd_ne; [| reg_neq]. exact HW1a0. }
      assert (HcsW2 : callee_saved M' W2).
      { rewrite /W2 /W1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      (* ================= sleep_prepare(b) ================= *)
      iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γl W2
                (trap_res eb + (K - 12))%nat 1%nat eb C false
                Hj Hjl ltac:(rewrite HW2a0; exact Hbnz) vdrwb_lvl1
                ltac:(pose proof (vdrw_K22 K HK); lia)
                with "Hcg Hown Htext Hpc Hpinv Hpanic").
      iApply wp_next_off_intro. iIntros (mfp) "%Hpcs Hcg Hown Hpc". rgall.
      assert (Hr1ba : ret_pc (W2 !!! Regidx Rra)
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1ba))
        by (rewrite HW2ra; pcstep).
      iEval (rewrite Hr1ba) in "Hpc".
      assert (Hmfps1 : mfp !!! Regidx Rs1 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hpcs Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /W2 upd_ne; [| reg_neq]. rewrite /W1 upd_ne; [| reg_neq]. exact Hs1L. }
      (* ---- +0x1ba  c.mv a0,s1 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ba) : mword 64) Ra0 Rs1 mfp
                (trap_res eb + (K - 12))%nat false ltac:(vm_compute; discriminate)
                ltac:(rdok) with "Hcg Hpc Hi1ba").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (W3 := <[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (mfp !!! Regidx Rs1))]> mfp).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (mfp !!! Regidx Rs1))]> mfp) with W3.
      assert (HW3a0 : W3 !!! Regidx Ra0 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite /W3 upd_eq vdrwe_addv_zero. exact Hmfps1. }
      assert (Hp1bc : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ba) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1bc)) by pcstep.
      iEval (rewrite Hp1bc) in "Hpc".
      (* ---- +0x1bc  jal ra,release ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1bc) : mword 64) Rra
                (mword_of_int 2077300 : mword 21) W3 (trap_res eb + (K - 12))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1bc").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (W4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1bc) : mword 64) 4)]> W3).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1bc) : mword 64) 4)]> W3) with W4.
      assert (Hjrl : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1bc) : mword 64)
                       (sign_extend' 64 (mword_of_int 2077300 : mword 21))
                     = mword_of_int KernelSyms.release) by pcstep.
      iEval (rewrite Hjrl) in "Hpc".
      assert (HW4ra : W4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1bc) : mword 64) 4)
        by (rewrite /W4; apply upd_eq).
      assert (HW4a0 : add_vec (W4 !!! Regidx Ra0)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))
                      = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite /W4 upd_ne; [| reg_neq]. rewrite HW3a0. apply vdrw_addv_sext0. }
      assert (HcsW4 : callee_saved mfp W4).
      { rewrite /W4 /W3.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      iDestruct (arm_pay_ext_split eb (proc_addr j) with "Htc Hclm")
        as "[Hpay [Hextc Hextm]]".
      (* ================= release(&disk.vdisk_lock) ================= *)
      iApply (Release.wp_release_sconf γk d_lock "virtio_disk"%string
                (disk_res γd pd pav pu) W4 0%nat eb (proc_addr j) C (K - 12)%nat
                HW4a0 ltac:(pose proof (vdrw_K10 K HK); lia)
                with "Hcg Htext Hpc Hlk Htok HR Hown Hpay").
      iIntros (CIDrl Hsrl mfr) "Hcg Hpc %Hrcs Hown". rgall.
      assert (Hr1c0 : ret_pc (W4 !!! Regidx Rra)
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1c0))
        by (rewrite HW4ra; pcstep).
      iEval (rewrite Hr1c0) in "Hpc".
      (* ---- +0x1c0  jal ra,sleep ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c0) : mword 64) Rra
                (mword_of_int 2082126 : mword 21) mfr (K - 12)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1c0").
      iIntros (CIDjs Hsjs) "Hcg Hpc". rgall.
      set (W5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c0) : mword 64) 4)]> mfr).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c0) : mword 64) 4)]> mfr) with W5.
      assert (Hjsl : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c0) : mword 64)
                       (sign_extend' 64 (mword_of_int 2082126 : mword 21))
                     = mword_of_int KernelSyms.sleep) by pcstep.
      iEval (rewrite Hjsl) in "Hpc".
      assert (HW5ra : W5 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c0) : mword 64) 4)
        by (rewrite /W5; apply upd_eq).
      assert (HcsW5 : callee_saved mfr W5).
      { rewrite /W5. apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      (* ========================== sleep() ========================== *)
      iDestruct (cpu_own_transport CIDrl CIDjs 0 eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CIDlp CIDjs eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDlp CIDjs eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iApply (Sleep.wp_sleep_sconf γs j γl W5 (K - 12)%nat eb C
                Hj Hjl ltac:(pose proof (vdrw_K22 K HK); lia)
                with "Hcg Hown Htext Hpc Hpinv Hpanic Hextc Hextm").
      iIntros (CIDsl Hssl mfs) "%Hscs Hcg Hown Hpc Hextc Hextm". rgall.
      assert (Hr1c4 : ret_pc (W5 !!! Regidx Rra)
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1c4))
        by (rewrite HW5ra; pcstep).
      iEval (rewrite Hr1c4) in "Hpc".
      assert (Hmfss1 : mfs !!! Regidx Rs1 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hscs Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /W5 upd_ne; [| reg_neq].
        rewrite (callee_saved_lookup Hrcs Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /W4 upd_ne; [| reg_neq]. rewrite /W3 upd_ne; [| reg_neq].
        exact Hmfps1. }
      (* ---- +0x1c4  c.mv a0,s1 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c4) : mword 64) Ra0 Rs1 mfs
                (K - 12)%nat eb ltac:(vm_compute; discriminate)
                ltac:(rdok) with "Hcg Hpc Hi1c4").
      iIntros (CIDm Hsm) "Hcg Hpc". rgall.
      set (W6 := <[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (mfs !!! Regidx Rs1))]> mfs).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (mfs !!! Regidx Rs1))]> mfs) with W6.
      assert (HW6a0 : W6 !!! Regidx Ra0 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite /W6 upd_eq vdrwe_addv_zero. exact Hmfss1. }
      assert (Hp1c6 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c4) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1c6)) by pcstep.
      iEval (rewrite Hp1c6) in "Hpc".
      (* ---- +0x1c6  jal ra,acquire ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c6) : mword 64) Rra
                (mword_of_int 2077154 : mword 21) W6 (K - 12)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1c6").
      iIntros (CIDd3 Hsd3) "Hcg Hpc". rgall.
      set (W7 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c6) : mword 64) 4)]> W6).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c6) : mword 64) 4)]> W6) with W7.
      assert (Hjaq : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c6) : mword 64)
                       (sign_extend' 64 (mword_of_int 2077154 : mword 21))
                     = mword_of_int KernelSyms.acquire) by pcstep.
      iEval (rewrite Hjaq) in "Hpc".
      assert (HW7ra : W7 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1c6) : mword 64) 4)
        by (rewrite /W7; apply upd_eq).
      assert (HW7a0 : W7 !!! Regidx Ra0 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite /W7 upd_ne; [| reg_neq]. exact HW6a0. }
      assert (HcsW7 : callee_saved mfs W7).
      { rewrite /W7 /W6.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      (* ================= acquire(&disk.vdisk_lock) ================= *)
      iDestruct (cpu_own_transport CIDsl CIDd3 0 eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Acquire.wp_acquire_sconf γk "virtio_disk"%string
                (disk_res γd pd pav pu) W7 0%nat eb (proc_addr j) C (K - 12)%nat eb
                vdrw_noff0 ltac:(pose proof (vdrw_K10 K HK); lia)
                with "Hcg Hown Htext Hpc [] Hpanic").
      { iEval (rewrite HW7a0). iExact "Hlk". }
      iIntros (CIDaq Hsaq msA Mf) "_ Hcg Hpc %Hacs Htok HR Hown Hpay". rgall.
      assert (Hret : ret_pc (W7 !!! Regidx Rra) = mword_of_int (KernelSyms.virtio_disk_rw + 0x1ca))
        by (rewrite HW7ra; pcstep).
      iEval (rewrite Hret) in "Hpc".
      iDestruct (trap_csrs_ext_transport CIDsl CIDaq eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDsl CIDaq eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (arm_pay_ext_join eb (proc_addr j) with "Hpay [$Hextc $Hextm]")
        as "[Htc Hclm]".
      assert (Hcsf : callee_saved M' Mf).
      { eapply callee_saved_trans; [exact HcsW2|].
        eapply callee_saved_trans; [exact Hpcs|].
        eapply callee_saved_trans; [exact HcsW4|].
        eapply callee_saved_trans; [exact Hrcs|].
        eapply callee_saved_trans; [exact HcsW5|].
        eapply callee_saved_trans; [exact Hscs|].
        eapply callee_saved_trans; [exact HcsW7|].
        exact Hacs. }
      (* the register discipline survives the whole four-call window *)
      assert (HMfs3 : Mf !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hcsf Rs3 ltac:(vm_compute; reflexivity)). exact Hs3L. }
      assert (HMfs1 : Mf !!! Regidx Rs1 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hcsf Rs1 ltac:(vm_compute; reflexivity)). exact Hs1L. }
      assert (HMfs2 : Mf !!! Regidx Rs2 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hcsf Rs2 ltac:(vm_compute; reflexivity)). exact Hs2L. }
      assert (HMfregs : vdrw_regs Mf sp0 b wr sector).
      { unfold vdrw_regs. rewrite (proj1 Hcsf). split_and!.
        - exact HspL.
        - rewrite (callee_saved_lookup Hcsf Rs0 ltac:(vm_compute; reflexivity)). exact Hs0L.
        - exact HMfs3.
        - rewrite (callee_saved_lookup Hcsf Rs6 ltac:(vm_compute; reflexivity)). exact Hs6L.
        - rewrite (callee_saved_lookup Hcsf Rs7 ltac:(vm_compute; reflexivity)). exact Hs7L. }
      (* ---- +0x1ca  lw a5,4(s3) : re-read b->disk ---- *)
      iDestruct (vdrw_body_open γd pd pav pu with "HR") as (np' nr' fl' pk' tr' fr') "Hbody".
      iDestruct (vdrw_p5_peek γd pd pav np' nr' fl' pk' tr' fr' q V
                   with "Hbody Hclaim") as (dv) "(%Hdv & Hbd & Hclose)".
      assert (Haddr : add_vec (Mf !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 4 : mword 12))
                      = (b_disk b : SailStdpp.Values.mword 64))
        by (rewrite HMfs3; apply vdrwe_bdisk_addr).
      iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ca) : mword 64) Ra5 Rs3
                (mword_of_int 4 : mword 12) Mf (trap_res eb + (K - 12))%nat dv false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a8 [Hbd]").
      { rgall. iEval (rewrite Haddr). rewrite /V. cbn [dc_buf]. iExact "Hbd". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hbd". rgall.
      iEval (rewrite Haddr) in "Hbd".
      iDestruct ("Hclose" with "[Hbd]") as "[Hbody Hclaim]".
      { rewrite /V. cbn [dc_buf]. iExact "Hbd". }
      set (L4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> Mf).
      change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> Mf) with L4.
      assert (Hp1ac : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ca) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1ce)) by pcstep.
      iEval (rewrite Hp1ac) in "Hpc".
      assert (HL4s1 : L4 !!! Regidx Rs1 = (d_lock : SailStdpp.Values.mword 64))
        by (rewrite /L4 upd_ne; [| reg_neq]; exact HMfs1).
      assert (HL4s2 : L4 !!! Regidx Rs2 = (mword_of_int 1 : SailStdpp.Values.mword 64))
        by (rewrite /L4 upd_ne; [| reg_neq]; exact HMfs2).
      assert (HL4a5 : L4 !!! Regidx Ra5 = sign_extend' 64 dv)
        by (rewrite /L4; apply upd_eq).
      (* ---- +0x1ce  beq a5,s1 : still 1 -> loop ---- *)
      destruct Hdv as [-> | [-> Hpq] ].
      + (* still in flight: TAKEN, back to +0x1a0 *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ce) : mword 64)
                  (mword_of_int 8166 : mword 13) Rs2 Ra5 L4 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite HL4a5 HL4s2 vdrwe_sext_one; exact vdrwe_eq_one)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1ac").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hback : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ce) : mword 64)
                          (sign_extend' 64 (mword_of_int 8166 : mword 13))
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x1b4)) by pcstep.
        iEval (rewrite Hback) in "Hpc".
        iDestruct (vdrw_body_close γd pd pav pu with "Hbody") as "HR".
        iSpecialize ("IH" $! CIDaq with "[%]"); [wp_next_chain|].
        iApply ("IH" $! L4 with
                  "[%] Hcg Hown Htc Hclm Hpc Htok HR Hclaim Hrm Hrt Hidx
                   [%] [%] [%] HexitL").
        * split_and!; [| exact HL4s1 | |].
          -- unfold vdrw_regs. destruct HMfregs as (F1 & F2 & F3 & F4 & F5).
             split_and!;
               [ rewrite /L4 upd_ne; [exact F1 | reg_neq]
               | rewrite /L4 upd_ne; [exact F2 | reg_neq]
               | rewrite /L4 upd_ne; [exact F3 | reg_neq]
               | rewrite /L4 upd_ne; [exact F4 | reg_neq]
               | rewrite /L4 upd_ne; [exact F5 | reg_neq] ].
          -- rewrite /L4 upd_ne; [exact HMfs2 | reg_neq].
          -- vdrw_hi_peel. exact (vdrw_hi_cs M' Mf m0 Hcsf HhiL).
        * exact HokL.
        * exact HalL.
        * exact HpinrL.
      + (* parked: FALL THROUGH to +0x1d2 *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ce) : mword 64)
                  (mword_of_int 8166 : mword 13) Rs2 Ra5 L4 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite HL4a5 HL4s2 vdrwe_sext_zero; exact vdrwe_eq_zero_one)
                  with "Hcg Hpc Hi1ac").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hp1b0 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ce) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x1d2)) by pcstep.
        iEval (rewrite Hp1b0) in "Hpc".
        rewrite /vdrw_p5_exit.
        iSpecialize ("HexitL" $! CIDaq with "[%]"); [wp_next_chain|].
        iApply ("HexitL" $! L4 q np' nr' fl' pk' tr' fr' h m2 t pin with
                  "[%] [%] [%] [%] [%] Hcg Hown Htc Hclm Hpc Htok Hbody Hclaim
                   Hrm Hrt Hidx").
        * split; [| vdrw_hi_peel; exact (vdrw_hi_cs M' Mf m0 Hcsf HhiL)].
          unfold vdrw_regs. destruct HMfregs as (F1 & F2 & F3 & F4 & F5).
          split_and!;
            [ rewrite /L4 upd_ne; [exact F1 | reg_neq]
            | rewrite /L4 upd_ne; [exact F2 | reg_neq]
            | rewrite /L4 upd_ne; [exact F3 | reg_neq]
            | rewrite /L4 upd_ne; [exact F4 | reg_neq]
            | rewrite /L4 upd_ne; [exact F5 | reg_neq] ].
        * exact HokL.
        * exact Hpq.
        * exact HpinrL.
        * exact HalL. }
    (* ================= +0x19a .. +0x1b0, the entry ==================== *)
    (* ---- +0x19a  lui a5,0x10001 ---- *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x19a) : mword 64) Ra5
              (mword_of_int 65537 : mword 20)
              (mword_of_int 0x10001000 : SailStdpp.Values.mword 64) M (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              vdrwe_lui with "Hcg Hpc Hi186").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N1 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int 0x10001000 : SailStdpp.Values.mword 64)]> M).
    change (<[Regidx Ra5 := regval_into_reg
                  (mword_of_int 0x10001000 : SailStdpp.Values.mword 64)]> M) with N1.
    assert (HN1a5 : N1 !!! Regidx Ra5
                    = (mword_of_int 0x10001000 : SailStdpp.Values.mword 64))
      by (rewrite /N1; apply upd_eq).
    assert (Hp18a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x19a) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x19e)) by pcstep.
    iEval (rewrite Hp18a) in "Hpc".
    (* ---- +0x19e  sw x0,80(a5) : *R(QUEUE_NOTIFY) = 0 ---- *)
    iDestruct (sie_cap_gpr_x0 N1 (trap_res eb + (K - 12))%nat false (proc_addr j) (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    assert (Hnaddr : add_vec (N1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 80 : mword 12))
                     = (mword_of_int 0x10001050 : SailStdpp.Values.mword 64))
      by (rewrite HN1a5; apply vdrwe_notify_addr).
    assert (Ha8 : sign_extend' 64 (subrange_vec_dec
                    (add_vec (rget N1 Ra5) (sign_extend' 64 (mword_of_int 80 : mword 12)))
                    (xlen - 0 - 1) 0)
                  = (mword_of_int 0x10001050 : SailStdpp.Values.mword 64)).
    { rgall. rewrite subrange_id sign_extend'_id. exact Hnaddr. }
    pose proof vdrwe_notify_geom as (Hgr & Hga & Hgc & Hgd).
    assert (Hsw : (autocast (T := mword)
                     (subrange_vec_dec (N1 !!! Regidx (mword_of_int 0 : mword 5))
                        (Z.sub (Z.mul 4 8) 1) 0) : mword 32)
                  = (mword_of_int 0 : mword 32))
      by (rewrite Hx0; apply bv_eq; vm_compute; reflexivity).
    assert (Hwrite : forall v : virtio_state, virtio_isr_ok v ->
              exists v' : virtio_state,
                virtio_write v (uint (mword_of_int 0x10001050 : SailStdpp.Values.mword 64)
                                - virtio_base)%Z (mword_of_int 0 : mword 32) = Some v'
                /\ virtio_isr_ok v'
                /\ v_cfg v' = v_cfg v /\ v_seen v' = v_seen v
                /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v).
    { intros v Hvok. rewrite vdrwe_notify_off.
      apply (virtio_notify_write_ok v (mword_of_int 0 : mword 32));
        [ vm_compute; reflexivity | exact Hvok ]. }
    iApply (wp_sw_virtio_dev_s_sconf (CID := CIDx) (p := proc_addr j) γu γd (mword_of_int (KernelSyms.virtio_disk_rw + 0x19e) : mword 64)
              false (mword_of_int 0 : mword 5) Ra5 (mword_of_int 80 : mword 12)
              N1 (trap_res eb + (K - 12))%nat
              ltac:(rewrite Ha8; exact Hgr)
              ltac:(rewrite Ha8; exact Hga)
              ltac:(rewrite Ha8; exact Hgc)
              ltac:(rewrite Ha8; exact Hgd)
              ltac:(rewrite Ha8; rgall; rewrite Hsw; exact Hwrite)
              with "Hcg Hpc Hi18a Hdinv").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp18e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x19e) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1a2)) by pcstep.
    iEval (rewrite Hp18e) in "Hpc".
    (* ---- +0x1a2  lw a5,4(s3) : the first b->disk read ---- *)
    assert (HN1s3 : N1 !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64))
      by (rewrite /N1 upd_ne; [| reg_neq]; exact Hs3).
    iDestruct (vdrw_p5_peek γd pd pav np nr fl pk tr fr q V
                 with "Hbody Hclaim") as (dv) "(%Hdv & Hbd & Hclose)".
    assert (Haddr0 : add_vec (N1 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 4 : mword 12))
                     = (b_disk b : SailStdpp.Values.mword 64))
      by (rewrite HN1s3; apply vdrwe_bdisk_addr).
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a2) : mword 64) Ra5 Rs3
              (mword_of_int 4 : mword 12) N1 (trap_res eb + (K - 12))%nat dv false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18e [Hbd]").
    { rgall. iEval (rewrite Haddr0). rewrite /V. cbn [dc_buf]. iExact "Hbd". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbd". rgall.
    iEval (rewrite Haddr0) in "Hbd".
    iDestruct ("Hclose" with "[Hbd]") as "[Hbody Hclaim]".
    { rewrite /V. cbn [dc_buf]. iExact "Hbd". }
    set (N2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> N1).
    change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> N1) with N2.
    assert (Hp192 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a2) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1a6)) by pcstep.
    iEval (rewrite Hp192) in "Hpc".
    (* ---- +0x1a6 / +0x1aa  s1 := &disk.vdisk_lock ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a6) : mword 64) Rs1
              (mword_of_int 30 : mword 20) N2 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi192").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a6) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> N2).
    change (<[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a6) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> N2) with N3.
    assert (Hp196 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a6) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1aa)) by pcstep.
    iEval (rewrite Hp196) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1aa) : mword 64) Rs1 Rs1
              (mword_of_int 3058 : mword 12) N3 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi196").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N4 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (N3 !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 3058 : mword 12)))]> N3).
    change (<[Regidx Rs1 := regval_into_reg
                  (add_vec (N3 !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 3058 : mword 12)))]> N3) with N4.
    assert (HN4s1 : N4 !!! Regidx Rs1 = (d_lock : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_eq /N3 upd_eq.
      unfold d_lock, disk_base, pa_add, add_vec_int. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp19a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1aa) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1ae)) by pcstep.
    iEval (rewrite Hp19a) in "Hpc".
    (* ---- +0x1ae  c.mv s2,a1 ---- *)
    assert (HN4a1 : N4 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [| reg_neq]. exact Ha1. }
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ae) : mword 64) Rs2 Ra1 N4
              (trap_res eb + (K - 12))%nat false ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi19a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N5 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (N4 !!! Regidx Ra1))]> N4).
    change (<[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (N4 !!! Regidx Ra1))]> N4) with N5.
    assert (HN5s2 : N5 !!! Regidx Rs2 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
    { rewrite /N5 upd_eq vdrwe_addv_zero. exact HN4a1. }
    assert (HN5a1 : N5 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64))
      by (rewrite /N5 upd_ne; [| reg_neq]; exact HN4a1).
    assert (HN5a5 : N5 !!! Regidx Ra5 = sign_extend' 64 dv).
    { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
      rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2; apply upd_eq. }
    assert (HN5s1 : N5 !!! Regidx Rs1 = (d_lock : SailStdpp.Values.mword 64))
      by (rewrite /N5 upd_ne; [| reg_neq]; exact HN4s1).
    assert (HN5regs : vdrw_regs N5 sp0 b wr sector).
    { unfold vdrw_regs. split_and!.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
        rewrite /N1 upd_ne; [| reg_neq]. exact Hsp.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
        rewrite /N1 upd_ne; [| reg_neq]. exact Hs0.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
        rewrite /N1 upd_ne; [| reg_neq]. exact Hs3.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
        rewrite /N1 upd_ne; [| reg_neq]. exact Hs6.
      - rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
        rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
        rewrite /N1 upd_ne; [| reg_neq]. exact Hs7. }
    assert (Hp19c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ae) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0)) by pcstep.
    iEval (rewrite Hp19c) in "Hpc".
    (* ---- +0x1b0  bne a5,a1 ---- *)
    destruct Hdv as [-> | [-> Hpq] ].
    - (* IN FLIGHT: fall through into the wait loop *)
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0) : mword 64)
                (mword_of_int 34 : mword 13) Ra1 Ra5 N5 (trap_res eb + (K - 12))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgall; rewrite HN5a5 HN5a1 vdrwe_sext_one; exact vdrwe_neq_one)
                with "Hcg Hpc Hi19c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hp1a0 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1b4)) by pcstep.
      iEval (rewrite Hp1a0) in "Hpc".
      iDestruct (vdrw_body_close γd pd pav pu with "Hbody") as "HR".
      rewrite /vdrw_p5_loop.
      iSpecialize ("Hloop" $! CIDx with "[%]"); [wp_next_chain|].
      iApply ("Hloop" $! N5 with
                "[%] Hcg Hown Htc Hclm Hpc Htok HR Hclaim Hrm Hrt Hidx
                 [%] [%] [%] Hexit").
      + split_and!; [ exact HN5regs | exact HN5s1 | exact HN5s2
                    | vdrw_hi_peel; exact Hhi ].
      + exact Hok.
      + exact Hal.
      + exact Hpinr.
    - (* ALREADY PARKED: the branch is taken, straight to +0x1d2 *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0) : mword 64)
                (mword_of_int 34 : mword 13) Ra1 Ra5 N5 (trap_res eb + (K - 12))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgall; rewrite HN5a5 HN5a1 vdrwe_sext_zero; exact vdrwe_neq_zero_one)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi19c").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hb1b0 : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0) : mword 64)
                        (sign_extend' 64 (mword_of_int 34 : mword 13))
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1d2)) by pcstep.
      iEval (rewrite Hb1b0) in "Hpc".
      rewrite /vdrw_p5_exit.
      iSpecialize ("Hexit" $! CIDx with "[%]"); [wp_next_chain|].
      iApply ("Hexit" $! N5 q np nr fl pk tr fr h m2 t pin with
                "[%] [%] [%] [%] [%] Hcg Hown Htc Hclm Hpc Htok Hbody Hclaim
                 Hrm Hrt Hidx").
      + split; [exact HN5regs | vdrw_hi_peel; exact Hhi].
      + exact Hok.
      + exact Hpq.
      + exact Hpinr.
      + exact Hal.
  Qed.

End ProofVirtioDiskRwE.
End VirtioDiskRwRestE.
