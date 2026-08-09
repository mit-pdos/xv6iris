(* ProofVirtioDiskRwE.v -- virtio_disk_rw, phase P5: the device kick and the
   completion wait (+0x186 .. +0x1b0).

   The continuation of ProofVirtioDiskRwD.v, which proves P4 and leaves the
   seam [VirtioDiskRwRestD.vdrw_p4_exit] at +0x186.

     0x186 lui  a5,0x10001
     0x18a sw   x0,80(a5)     *R(QUEUE_NOTIFY) = 0   -- kick the device
     0x18e lw   a5,4(s3)      a5 = b->disk
     0x192 auipc s2,0x1e ; 0x196 addi s2,s2,3166     s2 = &disk.vdisk_lock
     0x19a c.mv s1,a1         s1 = 1   (a1 has held 1 since +0x0f0)
     0x19c bne  a5,a1,+20     b->disk != 1 -> +0x1b0 (done)
     -- the completion-wait loop, head at +0x1a0 --
     0x1a0 c.mv a1,s2 ; 0x1a2 c.mv a0,s3 ; 0x1a4 jal sleep(b, &vdisk_lock)
     0x1a8 lw   a5,4(s3)
     0x1ac beq  a5,s1,-12     still 1 -> back to +0x1a0

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

   P6 (+0x1b0 .. +0x212) follows in ProofVirtioDiskRwF.v.
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
Require Import SpecAcquire SpecRelease SpecSleep SpecFreeDesc.
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
                         (Sleep : SLEEP) (FreeDesc : FREEDESC).

Module P4 := VirtioDiskRwRestD Acquire Release Sleep FreeDesc.

Section ProofVirtioDiskRwE.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
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
  (* THE P5/P6 SEAM at +0x1b0.                                            *)
  (*                                                                      *)
  (* Identical to [P4.vdrw_p4_exit] except that (a) the pc is +0x1b0 and   *)
  (* (b) it adds the pure fact the wait established: the claim's position  *)
  (* is PARKED, i.e. the interrupt handler has already deposited the       *)
  (* payoff.  P6 withdraws it from [pk] with nothing further to check.     *)
  (* Note that s1/s2 are NOT pinned: +0x1b0 reloads [idx[0]] into s2 and   *)
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
       sie_cap_gpr M (K - 12)%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) C false -∗
       arm_pay 0 eb (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0) : mword 64) -∗
       locked γk cpu_id -∗
       vdrw_body γd pd pav np nr fl pk tr fr -∗
       disk_claim γd q (DClaim b (vdrwd_slot kq b h wr sector
                                    (vdrwd_sldata wr bs_buf bs_disk))
                               (h, m2, t) pin) -∗
       vdrw_slot_rest m2 -∗ vdrw_slot_rest t -∗
       vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       WP (Loop : expr riscv_lang)))%I.

  (* what the completion-wait loop head at +0x1a0 consumes.  The lock's
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
        /\ M !!! Regidx Rs1 = (mword_of_int 1 : SailStdpp.Values.mword 64)
        /\ M !!! Regidx Rs2 = (d_lock : SailStdpp.Values.mword 64)
        /\ vdrw_hi M m0⌝ -∗
       sie_cap_gpr M (K - 12)%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) C false -∗
       arm_pay 0 eb (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a0) : mword 64) -∗
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
    eb = true ->
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
    intros HK Hj Hjl Heb.
    iIntros "#Htext #Hpanic #Hpinv #Hscheds #Hdinv #Hlk Hexit".
    rewrite /P4.vdrw_p4_exit.
    iIntros (CIDx Hsx M q np nr fl pk tr fr h m2 t pin)
            "%Hrh %Ha1 %Hok %Hpinr %Hal Hcg Hown Hpay Hpc Hpark Htok Hbody Hclaim Hrm Hrt Hidx".
    destruct Hrh as (Hregs & Hhi).
    set (V := DClaim b (vdrwd_slot kq b h wr sector (vdrwd_sldata wr bs_buf bs_disk))
                     (h, m2, t) pin).
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
    iPoseProof (rwi_186 with "Htext") as "Hi186".
    iPoseProof (rwi_18a with "Htext") as "Hi18a".
    iPoseProof (rwi_18e with "Htext") as "Hi18e".
    iPoseProof (rwi_192 with "Htext") as "Hi192".
    iPoseProof (rwi_196 with "Htext") as "Hi196".
    iPoseProof (rwi_19a with "Htext") as "Hi19a".
    iPoseProof (rwi_19c with "Htext") as "Hi19c".
    (* ================= THE LOOP, first (it is used by both arms) ======= *)
    iAssert (vdrw_p5_loop CID γk γs j γd pd pav pu K eb C sp0 b wr sector
               bs_buf bs_disk h m2 t q pin m0 kq)%I with "[]" as "Hloop".
    { iLöb as "IH". rewrite {2}/vdrw_p5_loop.
      iIntros (CIDlp Hslp M') "%Hinv Hcg Hown Hpay Hpc Hpark Htok HR Hclaim Hrm Hrt Hidx
                    %HokL %HalL %HpinrL HexitL".
      destruct Hinv as (HregsL & Hs1L & Hs2L & HhiL).
      pose proof HregsL as HregsL'.
      destruct HregsL' as (HspL & Hs0L & Hs3L & Hs6L & Hs7L).
      iPoseProof (rwi_1a0 with "Htext") as "Hi1a0".
      iPoseProof (rwi_1a2 with "Htext") as "Hi1a2".
      iPoseProof (rwi_1a4 with "Htext") as "Hi1a4".
      iPoseProof (rwi_1a8 with "Htext") as "Hi1a8".
      iPoseProof (rwi_1ac with "Htext") as "Hi1ac".
      (* ---- +0x1a0  c.mv a1,s2 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a0) : mword 64) Ra1 Rs2 M'
                (K - 12)%nat false ltac:(vm_compute; discriminate)
                ltac:(rdok) with "Hcg Hpc Hi1a0 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (L1 := <[Regidx Ra1 := regval_into_reg
                    (add_vec zero_reg (M' !!! Regidx Rs2))]> M').
      change (<[Regidx Ra1 := regval_into_reg
                    (add_vec zero_reg (M' !!! Regidx Rs2))]> M') with L1.
      assert (HL1a1 : L1 !!! Regidx Ra1 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite /L1 upd_eq vdrwe_addv_zero. exact Hs2L. }
      assert (Hp1a2 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a0) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1a2)) by pcstep.
      iEval (rewrite Hp1a2) in "Hpc".
      (* ---- +0x1a2  c.mv a0,s3 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a2) : mword 64) Ra0 Rs3 L1
                (K - 12)%nat false ltac:(vm_compute; discriminate)
                ltac:(rdok) with "Hcg Hpc Hi1a2 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (L2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (L1 !!! Regidx Rs3))]> L1).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (L1 !!! Regidx Rs3))]> L1) with L2.
      assert (Hp1a4 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a2) : mword 64) 2
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1a4)) by pcstep.
      iEval (rewrite Hp1a4) in "Hpc".
      (* ---- +0x1a4  jal ra,sleep ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a4) : mword 64) Rra
                (mword_of_int 2082316 : mword 21) L2 (K - 12)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1a4 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (L3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a4) : mword 64) 4)]> L2).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a4) : mword 64) 4)]> L2) with L3.
      assert (Hjsl : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a4) : mword 64)
                       (sign_extend' 64 (mword_of_int 2082316 : mword 21))
                     = mword_of_int KernelSyms.sleep) by pcstep.
      iEval (rewrite Hjsl) in "Hpc".
      assert (HL3a1 : add_vec (L3 !!! Regidx Ra1)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))
                      = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
        rewrite HL1a1. apply vdrw_addv_sext0. }
      assert (HL3ra : L3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a4) : mword 64) 4)
        by (rewrite /L3; apply upd_eq).
      iApply (Sleep.wp_sleep_sconf γs j γl γk d_lock "virtio_disk"%string
                (disk_res γd pd pav pu) L3 (K - 12)%nat eb C
                Hj Hjl HL3a1 Heb (vdrw_K22 K HK)
                with "Hcg Hown Hpay Htext Hpc Hpinv Hscheds Hlk Htok HR Hpanic Hpark [-]").
      iIntros (CIDsl Hssl Mf) "%Hcsf Hcg Hown Hpay Hpc Htok HR Hpark". rgall.
      assert (Hret : ret_pc (L3 !!! Regidx Rra) = mword_of_int (KernelSyms.virtio_disk_rw + 0x1a8))
        by (rewrite HL3ra; pcstep).
      iEval (rewrite Hret) in "Hpc".
      (* the register discipline survives sleep *)
      assert (HMfs3 : Mf !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hcsf Rs3 ltac:(vm_compute; reflexivity)).
        rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
        rewrite /L1 upd_ne; [| reg_neq]. exact Hs3L. }
      assert (HMfs1 : Mf !!! Regidx Rs1 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hcsf Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
        rewrite /L1 upd_ne; [| reg_neq]. exact Hs1L. }
      assert (HMfs2 : Mf !!! Regidx Rs2 = (d_lock : SailStdpp.Values.mword 64)).
      { rewrite (callee_saved_lookup Hcsf Rs2 ltac:(vm_compute; reflexivity)).
        rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
        rewrite /L1 upd_ne; [| reg_neq]. exact Hs2L. }
      assert (HMfregs : vdrw_regs Mf sp0 b wr sector).
      { unfold vdrw_regs. rewrite (proj1 Hcsf). split_and!.
        - rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
          rewrite /L1 upd_ne; [| reg_neq]. exact HspL.
        - rewrite (callee_saved_lookup Hcsf Rs0 ltac:(vm_compute; reflexivity)).
          rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
          rewrite /L1 upd_ne; [| reg_neq]. exact Hs0L.
        - exact HMfs3.
        - rewrite (callee_saved_lookup Hcsf Rs6 ltac:(vm_compute; reflexivity)).
          rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
          rewrite /L1 upd_ne; [| reg_neq]. exact Hs6L.
        - rewrite (callee_saved_lookup Hcsf Rs7 ltac:(vm_compute; reflexivity)).
          rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
          rewrite /L1 upd_ne; [| reg_neq]. exact Hs7L. }
      (* ---- +0x1a8  lw a5,4(s3) : re-read b->disk ---- *)
      iDestruct (vdrw_body_open γd pd pav pu with "HR") as (np' nr' fl' pk' tr' fr') "Hbody".
      iDestruct (vdrw_p5_peek γd pd pav np' nr' fl' pk' tr' fr' q V
                   with "Hbody Hclaim") as (dv) "(%Hdv & Hbd & Hclose)".
      assert (Haddr : add_vec (Mf !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 4 : mword 12))
                      = (b_disk b : SailStdpp.Values.mword 64))
        by (rewrite HMfs3; apply vdrwe_bdisk_addr).
      iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a8) : mword 64) Ra5 Rs3
                (mword_of_int 4 : mword 12) Mf (K - 12)%nat dv false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a8 [Hbd] [-]").
      { rgall. iEval (rewrite Haddr). rewrite /V. cbn [dc_buf]. iExact "Hbd". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hbd". rgall.
      iEval (rewrite Haddr) in "Hbd".
      iDestruct ("Hclose" with "[Hbd]") as "[Hbody Hclaim]".
      { rewrite /V. cbn [dc_buf]. iExact "Hbd". }
      set (L4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> Mf).
      change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> Mf) with L4.
      assert (Hp1ac : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1a8) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1ac)) by pcstep.
      iEval (rewrite Hp1ac) in "Hpc".
      assert (HL4s1 : L4 !!! Regidx Rs1 = (mword_of_int 1 : SailStdpp.Values.mword 64))
        by (rewrite /L4 upd_ne; [| reg_neq]; exact HMfs1).
      assert (HL4a5 : L4 !!! Regidx Ra5 = sign_extend' 64 dv)
        by (rewrite /L4; apply upd_eq).
      (* ---- +0x1ac  beq a5,s1 : still 1 -> loop ---- *)
      destruct Hdv as [-> | [-> Hpq] ].
      + (* still in flight: TAKEN, back to +0x1a0 *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ac) : mword 64)
                  (mword_of_int 8180 : mword 13) Rs1 Ra5 L4 (K - 12)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite HL4a5 HL4s1 vdrwe_sext_one; exact vdrwe_eq_one)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1ac [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hback : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ac) : mword 64)
                          (sign_extend' 64 (mword_of_int 8180 : mword 13))
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x1a0)) by pcstep.
        iEval (rewrite Hback) in "Hpc".
        iDestruct (vdrw_body_close γd pd pav pu with "Hbody") as "HR".
        iSpecialize ("IH" $! CIDsl with "[%]"); [wp_next_chain|].
        iApply ("IH" $! L4 with
                  "[%] Hcg Hown Hpay Hpc Hpark Htok HR Hclaim Hrm Hrt Hidx
                   [%] [%] [%] HexitL").
        * assert (HhiL3 : vdrw_hi L3 m0) by (vdrw_hi_peel; exact HhiL).
          split_and!; [| exact HL4s1 | |].
          -- unfold vdrw_regs. destruct HMfregs as (F1 & F2 & F3 & F4 & F5).
             split_and!;
               [ rewrite /L4 upd_ne; [exact F1 | reg_neq]
               | rewrite /L4 upd_ne; [exact F2 | reg_neq]
               | rewrite /L4 upd_ne; [exact F3 | reg_neq]
               | rewrite /L4 upd_ne; [exact F4 | reg_neq]
               | rewrite /L4 upd_ne; [exact F5 | reg_neq] ].
          -- rewrite /L4 upd_ne; [exact HMfs2 | reg_neq].
          -- vdrw_hi_peel. exact (vdrw_hi_cs L3 Mf m0 Hcsf HhiL3).
        * exact HokL.
        * exact HalL.
        * exact HpinrL.
      + (* parked: FALL THROUGH to +0x1b0 *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ac) : mword 64)
                  (mword_of_int 8180 : mword 13) Rs1 Ra5 L4 (K - 12)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite HL4a5 HL4s1 vdrwe_sext_zero; exact vdrwe_eq_zero_one)
                  with "Hcg Hpc Hi1ac [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hp1b0 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x1ac) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0)) by pcstep.
        iEval (rewrite Hp1b0) in "Hpc".
        rewrite /vdrw_p5_exit.
        iSpecialize ("HexitL" $! CIDsl with "[%]"); [wp_next_chain|].
        iApply ("HexitL" $! L4 q np' nr' fl' pk' tr' fr' h m2 t pin with
                  "[%] [%] [%] [%] [%] Hcg Hown Hpay Hpc Hpark Htok Hbody Hclaim
                   Hrm Hrt Hidx").
        * split; [| vdrw_hi_peel; exact (vdrw_hi_cs L3 Mf m0 Hcsf
                       ltac:(vdrw_hi_peel; exact HhiL))].
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
    (* ================= +0x186 .. +0x19c, the entry ==================== *)
    (* ---- +0x186  lui a5,0x10001 ---- *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x186) : mword 64) Ra5
              (mword_of_int 65537 : mword 20)
              (mword_of_int 0x10001000 : SailStdpp.Values.mword 64) M (K - 12)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              vdrwe_lui with "Hcg Hpc Hi186 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N1 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int 0x10001000 : SailStdpp.Values.mword 64)]> M).
    change (<[Regidx Ra5 := regval_into_reg
                  (mword_of_int 0x10001000 : SailStdpp.Values.mword 64)]> M) with N1.
    assert (HN1a5 : N1 !!! Regidx Ra5
                    = (mword_of_int 0x10001000 : SailStdpp.Values.mword 64))
      by (rewrite /N1; apply upd_eq).
    assert (Hp18a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x186) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x18a)) by pcstep.
    iEval (rewrite Hp18a) in "Hpc".
    (* ---- +0x18a  sw x0,80(a5) : *R(QUEUE_NOTIFY) = 0 ---- *)
    iDestruct (sie_cap_gpr_x0 N1 (K - 12)%nat false (proc_addr j) (mword_of_int 0 : mword 5)
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
    iApply (wp_sw_virtio_dev_s_sconf (CID := CIDx) (p := proc_addr j) γu γd (mword_of_int (KernelSyms.virtio_disk_rw + 0x18a) : mword 64)
              false (mword_of_int 0 : mword 5) Ra5 (mword_of_int 80 : mword 12)
              N1 (K - 12)%nat false
              ltac:(rewrite Ha8; exact Hgr)
              ltac:(rewrite Ha8; exact Hga)
              ltac:(rewrite Ha8; exact Hgc)
              ltac:(rewrite Ha8; exact Hgd)
              ltac:(rewrite Ha8; rgall; rewrite Hsw; exact Hwrite)
              with "Hcg Hpc Hi18a Hdinv [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp18e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x18a) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x18e)) by pcstep.
    iEval (rewrite Hp18e) in "Hpc".
    (* ---- +0x18e  lw a5,4(s3) : the first b->disk read ---- *)
    assert (HN1s3 : N1 !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64))
      by (rewrite /N1 upd_ne; [| reg_neq]; exact Hs3).
    iDestruct (vdrw_p5_peek γd pd pav np nr fl pk tr fr q V
                 with "Hbody Hclaim") as (dv) "(%Hdv & Hbd & Hclose)".
    assert (Haddr0 : add_vec (N1 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 4 : mword 12))
                     = (b_disk b : SailStdpp.Values.mword 64))
      by (rewrite HN1s3; apply vdrwe_bdisk_addr).
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x18e) : mword 64) Ra5 Rs3
              (mword_of_int 4 : mword 12) N1 (K - 12)%nat dv false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18e [Hbd] [-]").
    { rgall. iEval (rewrite Haddr0). rewrite /V. cbn [dc_buf]. iExact "Hbd". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbd". rgall.
    iEval (rewrite Haddr0) in "Hbd".
    iDestruct ("Hclose" with "[Hbd]") as "[Hbody Hclaim]".
    { rewrite /V. cbn [dc_buf]. iExact "Hbd". }
    set (N2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> N1).
    change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 dv)]> N1) with N2.
    assert (Hp192 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x18e) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x192)) by pcstep.
    iEval (rewrite Hp192) in "Hpc".
    (* ---- +0x192 / +0x196  s2 := &disk.vdisk_lock ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x192) : mword 64) Rs2
              (mword_of_int 30 : mword 20) N2 (K - 12)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi192 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x192) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> N2).
    change (<[Regidx Rs2 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x192) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> N2) with N3.
    assert (Hp196 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x192) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x196)) by pcstep.
    iEval (rewrite Hp196) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x196) : mword 64) Rs2 Rs2
              (mword_of_int 3150 : mword 12) N3 (K - 12)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi196 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N4 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (N3 !!! Regidx Rs2)
                     (sign_extend' 64 (mword_of_int 3150 : mword 12)))]> N3).
    change (<[Regidx Rs2 := regval_into_reg
                  (add_vec (N3 !!! Regidx Rs2)
                     (sign_extend' 64 (mword_of_int 3150 : mword 12)))]> N3) with N4.
    assert (HN4s2 : N4 !!! Regidx Rs2 = (d_lock : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_eq /N3 upd_eq.
      unfold d_lock, disk_base, pa_add, add_vec_int. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp19a : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x196) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x19a)) by pcstep.
    iEval (rewrite Hp19a) in "Hpc".
    (* ---- +0x19a  c.mv s1,a1 ---- *)
    assert (HN4a1 : N4 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [| reg_neq]. exact Ha1. }
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x19a) : mword 64) Rs1 Ra1 N4
              (K - 12)%nat false ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi19a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N5 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (N4 !!! Regidx Ra1))]> N4).
    change (<[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (N4 !!! Regidx Ra1))]> N4) with N5.
    assert (HN5s1 : N5 !!! Regidx Rs1 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
    { rewrite /N5 upd_eq vdrwe_addv_zero. exact HN4a1. }
    assert (HN5a1 : N5 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64))
      by (rewrite /N5 upd_ne; [| reg_neq]; exact HN4a1).
    assert (HN5a5 : N5 !!! Regidx Ra5 = sign_extend' 64 dv).
    { rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
      rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2; apply upd_eq. }
    assert (HN5s2 : N5 !!! Regidx Rs2 = (d_lock : SailStdpp.Values.mword 64))
      by (rewrite /N5 upd_ne; [| reg_neq]; exact HN4s2).
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
    assert (Hp19c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x19a) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x19c)) by pcstep.
    iEval (rewrite Hp19c) in "Hpc".
    (* ---- +0x19c  bne a5,a1 ---- *)
    destruct Hdv as [-> | [-> Hpq] ].
    - (* IN FLIGHT: fall through into the wait loop *)
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x19c) : mword 64)
                (mword_of_int 20 : mword 13) Ra1 Ra5 N5 (K - 12)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgall; rewrite HN5a5 HN5a1 vdrwe_sext_one; exact vdrwe_neq_one)
                with "Hcg Hpc Hi19c [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hp1a0 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x19c) : mword 64) 4
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1a0)) by pcstep.
      iEval (rewrite Hp1a0) in "Hpc".
      iDestruct (vdrw_body_close γd pd pav pu with "Hbody") as "HR".
      rewrite /vdrw_p5_loop.
      iSpecialize ("Hloop" $! CIDx with "[%]"); [wp_next_chain|].
      iApply ("Hloop" $! N5 with
                "[%] Hcg Hown Hpay Hpc Hpark Htok HR Hclaim Hrm Hrt Hidx
                 [%] [%] [%] Hexit").
      + split_and!; [ exact HN5regs | exact HN5s1 | exact HN5s2
                    | vdrw_hi_peel; exact Hhi ].
      + exact Hok.
      + exact Hal.
      + exact Hpinr.
    - (* ALREADY PARKED: the branch is taken, straight to +0x1b0 *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x19c) : mword 64)
                (mword_of_int 20 : mword 13) Ra1 Ra5 N5 (K - 12)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgall; rewrite HN5a5 HN5a1 vdrwe_sext_zero; exact vdrwe_neq_zero_one)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi19c [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hb1b0 : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x19c) : mword 64)
                        (sign_extend' 64 (mword_of_int 20 : mword 13))
                      = mword_of_int (KernelSyms.virtio_disk_rw + 0x1b0)) by pcstep.
      iEval (rewrite Hb1b0) in "Hpc".
      rewrite /vdrw_p5_exit.
      iSpecialize ("Hexit" $! CIDx with "[%]"); [wp_next_chain|].
      iApply ("Hexit" $! N5 q np nr fl pk tr fr h m2 t pin with
                "[%] [%] [%] [%] [%] Hcg Hown Hpay Hpc Hpark Htok Hbody Hclaim
                 Hrm Hrt Hidx").
      + split; [exact HN5regs | vdrw_hi_peel; exact Hhi].
      + exact Hok.
      + exact Hpq.
      + exact Hpinr.
      + exact Hal.
  Qed.

End ProofVirtioDiskRwE.
End VirtioDiskRwRestE.
