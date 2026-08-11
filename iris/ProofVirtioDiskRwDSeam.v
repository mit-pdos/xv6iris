(* ProofVirtioDiskRwDSeam.v -- P4 packaged as the wand P3 consumes.

   Split off ProofVirtioDiskRwD.v for the same reason as
   ProofVirtioDiskRwCSeam.v: this glue is the only part of phase 4 that has to
   see phase 3's proof, while the 32 s of P4 itself needs nothing from it but
   VirtioDiskRwDefs.v.  Keeping them apart is what lets P4 compile alongside
   P1/P2/P3 rather than behind them. *)
(* ProofVirtioDiskRwD.v -- virtio_disk_rw, phase P4: the ring write and THE
   PUBLISH (+0x162 .. +0x186).

   The continuation of ProofVirtioDiskRwC.v, which proves P3 and leaves the
   seam [VirtioDiskRwRestC.vdrw_p3_exit] at +0x162.

     0x162 c.ld a3,8(a5)     a3 = disk.avail = pav
     0x164 lhu  a4,2(a3)     AU: read avail->idx      (= wrap16 np)
     0x168 c.andi a4,a4,7 ; 0x16a c.slli a4,a4,1 ; 0x16c c.add a3,a3,a4
     0x16e sh   a0,4(a3)     PLAIN store of the head into ring slot np mod 8
     0x172 fence rw,rw
     0x176 c.ld a4,8(a5) ; 0x178 lhu a5,2(a4)   the SAME np again
     0x17c c.addiw a5,a5,1
     0x17e sh   a5,2(a4)     THE PUBLISH (AU: avail->idx := wrap16 (S np))
     0x182 fence rw,rw

   A FOURTH file, purely for build latency (see the worklist).  Nothing in
   P4 calls a callee, so the phase itself lives in plain Sections; only the
   P3 -> P4 glue re-opens the functor.

   NOTE (the ProofVirtioDiskIntr helpers): a sibling owns that file, so the
   four small things P4 needs from it -- the [fence rw,rw] execution fact and
   its leaf, the page-offset alignment lemma, and the bitvector arithmetic of
   the 16-bit counter -- are CLONED here under [vdrwd_] names rather than
   imported.

   P5 follows in ProofVirtioDiskRwE.v and P6 in ProofVirtioDiskRwF.v.
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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn KernelText.
Require Import WpLock.
Require Import ProcGeom.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn FdSlots.
Require Import DiskPtsto VirtioProto DiskInv.
Require Import WpUart.
Require Import PermInv.
Require Import SpecAcquire SpecRelease SpecSleep SpecFreeDesc.
Require Import VirtioDiskRwDefs.
Require Import ProofVirtioDiskRwCSeam.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).
Require Import ProofVirtioDiskRwD.

Module VirtioDiskRwRestD (Acquire : ACQUIRE) (Release : RELEASE)
                         (Sleep : SLEEP) (FreeDesc : FREEDESC).

Module P3 := VirtioDiskRwRestC Acquire Release Sleep FreeDesc.

Section ProofVirtioDiskRwDSeam.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* THE P4/P5 SEAM at +0x186.  The published position is no longer named:  *)
  (* what the sleeper carries is the CLAIM fragment, from which P5 re-finds *)
  (* its [b->disk] cell inside the flight or parked entry.  The triple      *)
  (* (h,m2,t) and the [int idx[3]] local survive for P6's [free_chain];     *)
  (* the two untouched descriptor-slot remainders come back with them.      *)
  (* ------------------------------------------------------------------- *)
  Definition vdrw_p4_exit (CID0 : CPU) (γk : gname) 
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (bs_buf bs_disk : list (bv 8)) (m0 : regfile)
      (kq : nat * positive) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (q np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) (h m2 t : nat) pin,
       ⌜vdrw_regs M sp0 b wr sector /\ vdrw_hi M m0⌝ -∗
       ⌜M !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)⌝ -∗
       ⌜tri_ok (h, m2, t)⌝ -∗
       (* THE PIN'S STRUCTURE, for P6's [free_chain]: what the interrupt
          handler parks (the pin minus its avail-ring entry) is the fifteen
          formatted windows plus, for a write, the payload. *)
       ⌜pin ∖ range_map (d_ring pav (q `mod` 8)) 2
                (nth_byte (Z_to_bv 16 (Z.of_nat h)))
         = foldr union ∅ (vdrwd_pinr_regions pd b h m2 t wr sector
                            (vdrwd_bufwin b wr bs_buf))
        /\ pm_ok (vdrwd_pinr_regions pd b h m2 t wr sector
                    (vdrwd_bufwin b wr bs_buf))⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
        /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
       sie_cap_gpr M (trap_res true + (K - 12))%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) C false -∗
       arm_pay 0 eb (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x186) : mword 64) -∗
       locked γk cpu_id -∗
       vdrw_body γd pd pav np nr fl pk tr fr -∗
       disk_claim γd q (DClaim b (vdrwd_slot kq b h wr sector
                                    (vdrwd_sldata wr bs_buf bs_disk))
                                (h, m2, t) pin) -∗
       vdrw_slot_rest m2 -∗ vdrw_slot_rest t -∗
       vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       WP (Loop : expr riscv_lang)))%I.

  (* [P3.vdrw_p3_exit] plus the triple-disjointness conjunct (see above). *)
  Definition vdrw_p3_exit_x (CID0 : CPU) (γk : gname) 
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (m0 : regfile) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) (h m2 t : nat),
       ⌜vdrw_regs M sp0 b wr sector /\ vdrw_hi M m0⌝ -∗
       ⌜M !!! Regidx Ra0 = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64)
        /\ M !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)
        /\ M !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)⌝ -∗
       ⌜tri_ok (h, m2, t) /\ fr h = true /\ fr m2 = true /\ fr t = true⌝ -∗
       ⌜forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t)⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
        /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
       sie_cap_gpr M (trap_res true + (K - 12))%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) C false -∗
       arm_pay 0 eb (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x162) : mword 64) -∗
       locked γk cpu_id -∗
       vdrw_body γd pd pav np nr fl pk tr
         (fr_upd (fr_upd (fr_upd fr h false) m2 false) t false) -∗
       vdrw_chain pd b h m2 t wr sector -∗
       vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       WP (Loop : expr riscv_lang)))%I.

  (* P4, packaged as the wand P3 consumes. *)
  Lemma wp_vdrw_p4_seam (γk : gname)
      (γs : list gname) (jp : nat) (γu : uart_names) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr : SailStdpp.Values.mword 64)
      (bno : SailStdpp.Values.mword 32) (bs_buf bs_disk : list (bv 8))
      (m0 : regfile) (kq : nat * positive) :
    (uint bno < 2147483648)%Z ->
    length bs_buf = 1024%nat ->
    (forall k, (k < 1024)%nat -> addr_is_kdata (pa_add (b_data b) k)) ->
    kernel_text -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    ([∗ list] k ↦ x ∈ bs_buf, pa_add (b_data b) k ↦ₘ x) -∗
    disk_block γd (uint bno) bs_disk -∗
    (* the crash permit's token, on its way into the published slot, AT THIS
       REQUEST'S WRITE IDENTITY (phase C2a): [1024 * bno] is the byte offset
       the sector arithmetic lands on. *)
    perm_pend (dn_perm γd) kq (vdrwd_wr wr (1024 * uint bno)%Z bs_buf) -∗
    vdrw_p4_exit CID γk γs jp γd pd pav pu K eb C sp0 b wr (vdrw_sector_raw bno)
                 bs_buf bs_disk m0 kq -∗
    vdrw_p3_exit_x CID γk γs jp γd pd pav pu K eb C sp0 b wr (vdrw_sector_raw bno) m0.
  Proof.
    intros Hbno Hlenbuf Hbufkd.
    iIntros "#Htext #Hdinv #Hgeom Hbuf Hdisk Hpend Hexit".
    rewrite /vdrw_p3_exit_x.
    iIntros (CIDx Hsx M np nr fl pk tr fr h m2 t) "%Hrh %Hpin %Hfacts %Hdisj0 %Hal
             Hcg Hown Hpay Hpc Htok Hbody Hchain Hidx".
    destruct Hrh as (Hregs & Hhi).
    destruct Hpin as (Ha0 & Ha1 & Ha5).
    destruct Hfacts as (Hok & Hfrh & Hfrm & Hfrt).
    pose proof Hok as (Hhm & Hht & Hmt & Hh8 & Hm8 & Ht8). cbn in Hhm, Hht, Hmt.
    iDestruct "Hdisk" as "[%Hlendisk Hdisk]".
    (* the cleared free-map, at the publisher's own three descriptors *)
    assert (Hch : fr_upd (fr_upd (fr_upd fr h false) m2 false) t false h = false).
    { rewrite (fr_upd_ne _ t h false Hht) (fr_upd_ne _ m2 h false Hhm).
      apply fr_upd_eq. }
    assert (Hcm : fr_upd (fr_upd (fr_upd fr h false) m2 false) t false m2 = false).
    { rewrite (fr_upd_ne _ t m2 false Hmt). apply fr_upd_eq. }
    assert (Hct : fr_upd (fr_upd (fr_upd fr h false) m2 false) t false t = false)
      by apply fr_upd_eq.
    (* the sector arithmetic P1 deferred *)
    assert (Hoff : (bv_unsigned (vdrw_sector_raw bno) * 512)%Z = (1024 * uint bno)%Z).
    { rewrite (vdrwd_sector_raw_val bno Hbno). lia. }
    iApply (wp_vdrw_p4 (CID := CIDx) kq γu γd (proc_addr jp) M (trap_res true + (K - 12))%nat pd pav pu b wr (vdrw_sector_raw bno)
              np nr h m2 t fl pk tr
              (fr_upd (fr_upd (fr_upd fr h false) m2 false) t false)
              bs_buf bs_disk (1024 * uint bno)%Z
              Hok Hdisj0 Hch Hcm Hct Hlenbuf Hlendisk Hbufkd Hoff Ha0 Ha5
              with "Hcg Htext Hpc Hdinv Hgeom Hbody Hchain Hbuf Hdisk Hpend [-]").
    iIntros (M1 pin) "%F %Hpinr Hcg Hpc Hbody Hclaim Hrm Hrt".
    destruct F as (Hcs & H1a1).
    iSpecialize ("Hexit" $! CIDx with "[%]"); [wp_next_chain|].
    iApply ("Hexit" $! M1 np (S np) nr
              (<[ np := DClaim b (vdrwd_slot kq b h wr (vdrw_sector_raw bno)
                                    (vdrwd_sldata wr bs_buf bs_disk))
                               (h, m2, t) pin ]> fl) pk
              (<[ np := (h, m2, t) ]> tr)
              (fr_upd (fr_upd (fr_upd fr h false) m2 false) t false) h m2 t pin
              with "[%] [%] [%] [%] [%] Hcg Hown Hpay Hpc Htok Hbody
                    Hclaim Hrm Hrt Hidx").
    - split; [| exact (vdrw_hi_frame M M1 m0 Hcs Hhi)].
      destruct Hregs as (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
      unfold vdrw_regs. split_and!.
      + rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      + rewrite (Hcs (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs0.
      + rewrite (Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs3.
      + rewrite (Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs6.
      + rewrite (Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact Hs7.
    - rewrite H1a1. exact Ha1.
    - exact Hok.
    - exact Hpinr.
    - exact Hal.
  Qed.

End ProofVirtioDiskRwDSeam.
End VirtioDiskRwRestD.

