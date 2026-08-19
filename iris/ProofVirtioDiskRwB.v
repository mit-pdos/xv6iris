(* ProofVirtioDiskRwB.v -- virtio_disk_rw, phases P2.3 .. P6.

   The continuation of ProofVirtioDiskRw.v.  That file proves the four
   Qed-sealed phase lemmas up to and including [wp_vdrw_alloc3] (the
   three-iteration descriptor allocator); this file picks up the seams it
   leaves and carries the function to its return.

     P2.3 the s1/s4/s5/s8 set-up, the outer sleep-retry iLoeb, and the
          partial-free failure tail                        +0x036..+0x0c4
     P3   descriptor / header / status / info.b formatting  +0x0c4..+0x176
     P4   ring write, fence, and THE PUBLISH                +0x176..+0x19a
     P5   QUEUE_NOTIFY + the completion-wait iLoeb          +0x19a..+0x1d2
     P6   payoff withdrawal, free_chain, release, epilogue  +0x1d2..+0x234

   It is a SEPARATE FILE (rather than more of ProofVirtioDiskRw.v) purely
   for build latency: the parent file already costs ~6 minutes to check, and
   every phase added to it would re-pay that.  The functor is re-opened over
   the same four callee module types and instantiates the parent's functor
   internally, so the phase lemmas compose exactly as if they were one file.

   P3/P4/P5/P6 follow in the C/D/E/F files.
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
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import ProcGeom.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import CpuOwn SchedCtx FdSlots.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import SpecAcquire SpecRelease SpecSleepPrepare SpecSleep SpecFreeDesc.
Require Import CodeVirtioDiskRw.
Require Import SpecVirtioDiskRw.
Require Import ProofVirtioDiskRw.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).
Require Import VirtioDiskRwDefs.
Require Import ProcAvail.


Module VirtioDiskRwRest (Acquire : ACQUIRE) (Release : RELEASE)
                        (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) (FreeDesc : FREEDESC).

Module P1 := VirtioDiskRwPhases Acquire Release Sleep FreeDesc.


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

Section VdrwbFreeAt.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !uartGhostG Σ}.

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma wp_vdrw_free_at `{GEN : GenId} `{CID : CpuId}  (γs : list gname)
      (pd : mword 64) (i : nat) (fr : nat -> bool)
      (M : regfile) (av : nat) (eb : bool) (pme : mword 64)
      (idxa : Arch.pa) (off : Z) (imm : mword 12) (jimm : mword 21) (lks : gset string) :
    (K_free_desc <= av)%nat ->
    (i < 8)%nat ->
    fr i = false ->
    length γs = NPROC ->
    add_vec (M !!! Regidx Rs0) (sign_extend' 64 imm) = (idxa : mword 64) ->
    add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + off) : mword 64) 4
      = (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) ->
    add_vec (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) (sign_extend' 64 jimm)
      = mword_of_int KernelSyms.free_desc ->
    eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64)
                              (sign_extend' 64 jimm)) 0) ('b"0") = true ->
    ret_pc (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) 4)
      = (mword_of_int (KernelSyms.virtio_disk_rw + off + 8) : mword 64) ->
    locks_below lks "proc" ->
    sie_cap_gpr KT1 M av false pme -∗
    cpu_own 1 eb pme false lks -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + off) : mword 64) -∗
 procs_inv γs -∗
    d_desc_ptr ↦₈□ pd -∗
    instr (mword_of_int (KernelSyms.virtio_disk_rw + off) : mword 64) false
          (LOAD (imm, Regidx Rs0, Regidx Ra0, false, 4)) -∗
    instr (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) false (JAL (jimm, Regidx Rra)) -∗
    idxa ↦₄[KT1] (mword_of_int (Z.of_nat i) : mword 32) -∗
    free_bundles pd fr -∗ free_slot_res pd i -∗
    ( ∀ Mf : regfile,
        ⌜forall r : mword 5, is_cs_idx r = true -> Mf !!! Regidx r = M !!! Regidx r⌝ -∗
        sie_cap_gpr KT1 Mf av false pme -∗
        cpu_own 1 eb pme false lks -∗
        pc_is (mword_of_int (KernelSyms.virtio_disk_rw + off + 8) : mword 64) -∗
        idxa ↦₄[KT1] (mword_of_int (Z.of_nat i) : mword 32) -∗
        free_bundles pd (fr_upd fr i true) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hi8 Hfri Hlen Haddr Hp4 Hjt Hjal Hret Hlkbelow.
    iIntros "Hcg Hown #Htext Hpc #Hpinv #Hdp Hi0 Hi4 Hidx Hbun Hslot Hcont".
    (* ---- lw a0, imm(s0) ---- *)
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + off) : mword 64) Ra0 Rs0 imm M av
              (mword_of_int (Z.of_nat i) : mword 32) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0 [Hidx]").
    { rgall. iEval (rewrite Haddr). iExact "Hidx". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hidx". rgall.
    iEval (rewrite Haddr) in "Hidx".
    set (N1 := <[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32))]> M).
    change (<[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32))]> M) with N1.
    iEval (rewrite Hp4) in "Hpc".
    (* ---- jal ra, free_desc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) Rra jimm N1 av false
              ltac:(vm_compute; discriminate) ltac:(rdok) Hjal
              with "Hcg Hpc Hi4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (N2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) 4)]> N1).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) 4)]> N1) with N2.
    iEval (rewrite Hjt) in "Hpc".
    (* the register facts free_desc's spec wants *)
    assert (HN2a0 : uint (N2 !!! Regidx Ra0 : mword 64) = Z.of_nat i).
    { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_eq.
      exact (vdrwb_uint_small i Hi8). }
    assert (HN2ra : N2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + off + 4) : mword 64) 4)
      by (rewrite /N2; apply upd_eq).
    (* peel descriptor [i]'s (already cleared) free cell out of the bundle *)
    iEval (rewrite (free_bundles_split pd fr i Hi8)) in "Hbun".
    iDestruct "Hbun" as "[[Hcell _] Hrest]".
    iEval (rewrite Hfri) in "Hcell".
    (* take the slot apart: free_desc wants the four descriptor words *)
    iDestruct "Hslot" as "(Hde & Hops & Hst & Hib)".
    iDestruct "Hde" as (va vl vf vn) "(Hd0 & Hd8 & Hd12 & Hd14)".
    iApply (FreeDesc.wp_free_desc_sconf γs pd i N2 av 1%nat eb pme va vl vf vn false lks
              Hav Hi8 HN2a0 ltac:(intro r; apply rf_to_gmap_dom) Hlen vdrwb_lvl1
              with "Hcg Hown Htext Hpc Hpinv Hdp Hcell Hd0 Hd8 Hd12 Hd14").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (Mf) "%Hf Hcg Hown _ Hpc Hcell Hd0 Hd8 Hd12 Hd14". rgall.
    destruct Hf as (Hcs & _).
    iEval (rewrite HN2ra Hret) in "Hpc".
    iApply ("Hcont" $! Mf with "[%] Hcg Hown Hpc Hidx [Hcell Hrest Hops Hst Hib Hd0 Hd8 Hd12 Hd14]").
    { intros r Hr.
      rewrite (callee_saved_lookup Hcs r Hr).
      rewrite /N2 upd_ne; [| apply not_eq_sym, is_cs_idx_true_neq;
                             [vm_compute; reflexivity | exact Hr]].
      rewrite /N1 upd_ne; [reflexivity |].
      apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hr]. }
    rewrite (free_bundles_split pd (fr_upd fr i true) i Hi8).
    rewrite fr_upd_eq.
    rewrite -(free_bundles_but_upd pd fr i true).
    iFrame "Hrest Hcell Hops Hst Hib".
    iExists (zero_reg : mword 64), (mword_of_int 0 : mword 32),
            (mword_of_int 0 : mword 16), (mword_of_int 0 : mword 16).
    iFrame "Hd0 Hd8 Hd12 Hd14".
  Qed.
End VdrwbFreeAt.

Section ProofVirtioDiskRwB.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* [congruence] LAST: ahead of the named lemma it builds a congruence
     closure over the whole whole-function context on every peel layer
     (optimization.md / CalleeSaved.reg_ne_side). *)
  Local Ltac regne :=
    first [ apply vdrw_cs_ne; [ assumption | vm_compute; reflexivity ]
          | congruence ].

  (* =================================================================== *)
  (* P2.3a  ONE [free_desc] call of the partial-free tail.                *)
  (*                                                                     *)
  (*     off+0  lw   a0, imm(s0)      -- idx[k]                          *)
  (*     off+4  jal  ra, free_desc                                       *)
  (*                                                                     *)
  (* The bundle surgery is the whole content: [free_bundles_split] peels  *)
  (* descriptor [i]'s (cleared) cell out, [free_slot_res] is taken apart  *)
  (* so free_desc gets its four descriptor words, and the pieces it       *)
  (* returns -- the cell at 1 and the four zeroed words -- rebuild the    *)
  (* slot at [fr_upd fr i true].                                         *)
  (* =================================================================== *)

  (* =================================================================== *)
  (* P2.3b  The outer sleep-retry loop.                                  *)
  (* =================================================================== *)

  (* what the loop hands out when all three descriptors are in hand *)
  Definition vdrw_p2_exit (CID0 : CPU) (γk : gname)
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : mword 64) (K : nat) (eb : bool)
      (sp0 b : Arch.pa) (wr sector : mword 64) (m0 : regfile) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) (h m2 t : nat),
       ⌜vdrw_regs M sp0 b wr sector /\ vdrw_hi M m0⌝ -∗
       ⌜tri_ok (h, m2, t) /\ fr h = true /\ fr m2 = true /\ fr t = true⌝ -∗
       (* the publisher's own triple is disjoint from every RECORDED one.
          Only P2.3 can state this: it holds [disk_res] at the ORIGINAL [fr],
          where the three bits are still set, and the body's sixth conjunct
          ("every recorded triple member is not free") then refutes any
          overlap.  Downstream the body is exported at the CLEARED [fr], for
          which that conjunct says nothing at h/m2/t -- so the fact is no
          longer derivable and has to travel. *)
       ⌜forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t)⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
        /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
       sie_cap_gpr KT1 M (trap_res eb + (K - 12))%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) false ({["virtio_disk"]} ∪ lks) -∗
       trap_csrs KT1 -∗
       cpu_claim (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x0c4) : mword 64) -∗
       locked γk cpu_id -∗
       vdrw_body γd pd pav np nr fl pk tr
         (fr_upd (fr_upd (fr_upd fr h false) m2 false) t false) -∗
       free_slot_res pd h -∗ free_slot_res pd m2 -∗ free_slot_res pd t -∗
       vdrw_idx (KTR := KT1) sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       WP (Loop : expr riscv_lang)))%I.

  (* the loop head at +0x0bc *)
  Definition vdrw_p2_loop (CID0 : CPU) (γk : gname)
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : mword 64) (K : nat) (eb : bool)
      (sp0 b : Arch.pa) (wr sector : mword 64) (m0 : regfile) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ M : regfile,
       ⌜vdrw_regs M sp0 b wr sector
        /\ M !!! Regidx Rs1 = (mword_of_int 8 : mword 64)
        /\ M !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64)
        /\ M !!! Regidx Rs5 = (disk_base : mword 64)
        /\ vdrw_hi M m0⌝ -∗
       sie_cap_gpr KT1 M (trap_res eb + (K - 12))%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) false ({["virtio_disk"]} ∪ lks) -∗
       trap_csrs KT1 -∗
       cpu_claim (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x0bc) : mword 64) -∗
       locked γk cpu_id -∗
       disk_res γd pd pav pu -∗
       vdrw_scratch (KTR := KT1) sp0 -∗
       vdrw_p2_exit CID0 γk γs j γd pd pav pu K eb sp0 b wr sector m0 lks -∗
       WP (Loop : expr riscv_lang)))%I.

  Lemma wp_vdrw_p2 (γk : gname)
      (γs : list gname) (j : nat) (γl : gname) (γd : disk_names)
      (pd pav pu : mword 64) (M0 : regfile) (K : nat) (eb : bool)
      (sp0 b : Arch.pa) (wr sector : mword 64) (m0 : regfile) (lks : gset string) :
    (K_virtio_disk_rw <= K)%nat ->
    (j < NPROC)%nat -> γs !! j = Some γl -> length γs = NPROC ->
    vdrw_regs M0 sp0 b wr sector -> vdrw_hi M0 m0 ->
    (* THE LOWEST RANK IN THIS CONTINUATION'S CONE: "virtio_disk" (9), not
       "proc" (11).  [lks] is the held set BELOW the lock this function
       itself already holds (the outer P1 phase's acquire needed exactly
       this bound to take it), so it is what P2.3's retry loop needs again
       at its re-acquire ([Acquire] below) -- a DIRECT match, no widening.
       [locks_below_mono] (9 <= 11) lifts it to "proc" for the loop's
       [SleepPrepare]/[Sleep] calls, both of which run with the lock
       released, against this same [lks]. *)
    locks_below lks "virtio_disk" ->
    sie_cap_gpr KT1 M0 (trap_res eb + (K - 12))%nat false (proc_addr j) -∗
    cpu_own 1 eb (proc_addr j) false ({["virtio_disk"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim (proc_addr j) -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x036) : mword 64) -∗
 procs_inv γs -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    locked γk cpu_id -∗
    disk_res γd pd pav pu -∗
    vdrw_scratch (KTR := KT1) sp0 -∗
    vdrw_p2_exit CID γk γs j γd pd pav pu K eb sp0 b wr sector m0 lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hj Hjl Hlen Hregs Hhi0 Hbelow.
    iIntros "Hcg Hown Htc Hclm #Htext Hpc #Hpinv
             #Hgeom #Hlk Htok HR Hscr Hexit".
    iPoseProof (rwi_036 with "Htext") as "Hi036".
    iPoseProof (rwi_038 with "Htext") as "Hi038".
    iPoseProof (rwi_03c with "Htext") as "Hi03c".
    iPoseProof (rwi_040 with "Htext") as "Hi040".
    iPoseProof (rwi_042 with "Htext") as "Hi042".
    iPoseProof (rwi_044 with "Htext") as "Hi044".
    (* ---- +0x036  c.li s1,8 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x036) : mword 64) Rs1
              (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 64) M0 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              vdrwb_li8 with "Hcg Hpc Hi036").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A1 := <[Regidx Rs1 := regval_into_reg (mword_of_int 8 : mword 64)]> M0).
    change (<[Regidx Rs1 := regval_into_reg (mword_of_int 8 : mword 64)]> M0) with A1.
    assert (Hp038 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x036) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x038)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp038) in "Hpc".
    (* ---- +0x038 / +0x03c  s5 := &disk ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x038) : mword 64) Rs5
              (mword_of_int 30 : mword 20) A1 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi038").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A2 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x038) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> A1).
    change (<[Regidx Rs5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x038) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> A1) with A2.
    assert (Hp03c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x038) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x03c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp03c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x03c) : mword 64) Rs5 Rs5
              (mword_of_int 3008 : mword 12) A2 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi03c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A3 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (A2 !!! Regidx Rs5)
                     (sign_extend' 64 (mword_of_int 3008 : mword 12)))]> A2).
    change (<[Regidx Rs5 := regval_into_reg
                  (add_vec (A2 !!! Regidx Rs5)
                     (sign_extend' 64 (mword_of_int 3008 : mword 12)))]> A2) with A3.
    assert (HA3s5 : A3 !!! Regidx Rs5 = (disk_base : mword 64)).
    { rewrite /A3 upd_eq /A2 upd_eq.
      unfold disk_base. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp040 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x03c) : mword 64) 4
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x040)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp040) in "Hpc".
    (* ---- +0x040  c.li s4,3 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x040) : mword 64) Rs4
              (mword_of_int 3 : mword 6) (mword_of_int (Z.of_nat 3) : mword 64)
              A3 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              vdrwb_li3 with "Hcg Hpc Hi040").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A4 := <[Regidx Rs4 := regval_into_reg
                  (mword_of_int (Z.of_nat 3) : mword 64)]> A3).
    change (<[Regidx Rs4 := regval_into_reg
                  (mword_of_int (Z.of_nat 3) : mword 64)]> A3) with A4.
    assert (Hp042 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x040) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x042)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp042) in "Hpc".
    (* ---- +0x042  c.li s8,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x042) : mword 64) Rs8
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              A4 (trap_res eb + (K - 12))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              vdrwb_lim1 with "Hcg Hpc Hi042").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A5 := <[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> A4).
    change (<[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> A4) with A5.
    assert (Hp044 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x042) : mword 64) 2
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x044)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp044) in "Hpc".
    (* the four loop-invariant registers, at A5 *)
    assert (HA5s1 : A5 !!! Regidx Rs1 = (mword_of_int 8 : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1; apply upd_eq. }
    assert (HA5s4 : A5 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4; apply upd_eq. }
    assert (HA5s5 : A5 !!! Regidx Rs5 = (disk_base : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq]. exact HA3s5. }
    assert (HA5regs : vdrw_regs A5 sp0 b wr sector).
    { unfold vdrw_regs in Hregs |- *.
      destruct Hregs as (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
      split_and!.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hsp.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs0.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs3.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs6.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs7. }
    (* ================= THE LOOP (iLoeb) ================= *)
    iAssert (vdrw_p2_loop CID γk γs j γd pd pav pu K eb sp0 b wr sector m0 lks)
      with "[]" as "Hloop".
    { iLöb as "IH". rewrite /vdrw_p2_loop.
      iIntros (CIDlp Hslp M) "%Hinv Hcg Hown Htc Hclm Hpc Htok HR Hscr Hexit".
      destruct Hinv as (Hregs' & Hs1 & Hs4 & Hs5 & Hhi).
      iPoseProof (rwi_07a with "Htext") as "Hi07a".
      iPoseProof (rwi_07e with "Htext") as "Hi07e".
      iPoseProof (rwi_082 with "Htext") as "Hi082".
      iPoseProof (rwi_086 with "Htext") as "Hi086".
      iPoseProof (rwi_088 with "Htext") as "Hi088".
      iPoseProof (rwi_08c with "Htext") as "Hi08c".
      iPoseProof (rwi_090 with "Htext") as "Hi090".
      iPoseProof (rwi_094 with "Htext") as "Hi094".
      iPoseProof (rwi_098 with "Htext") as "Hi098".
      iPoseProof (rwi_09c with "Htext") as "Hi09c".
      iPoseProof (rwi_0a0 with "Htext") as "Hi0a0".
      iPoseProof (rwi_0a4 with "Htext") as "Hi0a4".
      iPoseProof (rwi_0a8 with "Htext") as "Hi0a8".
      iPoseProof (rwi_0ac with "Htext") as "Hi0ac".
      iPoseProof (rwi_0b0 with "Htext") as "Hi0b0".
      iPoseProof (rwi_0b4 with "Htext") as "Hi0b4".
      iPoseProof (rwi_0b8 with "Htext") as "Hi0b8".
      iDestruct "Hgeom" as "#Hgeom'".
      iDestruct "Hgeom'" as "(Hdp & _)".
      destruct Hregs' as (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
      (* open the lock's resource *)
      iDestruct (vdrw_body_open γd pd pav pu with "HR") as (np nr fl pk tr fr) "Hbody".
      iDestruct "Hbody" as "(%Hdfl & %Hdpk & %Hdtr & %Hcoh & %Htok1 & %Htok2 & %Htok3 &
                             Hpub & Hlb & Hcl & Huidx & Hflight & Hparked &
                             Hbun & Hring)".
      (* ---- the three-descriptor allocator ---- *)
      iApply (P1.wp_vdrw_alloc3 (proc_addr j) pd sp0 fr (trap_res eb + (K - 12))%nat M
                Hs0 Hs5 Hs1 Hs4 with "Hcg Htext Hpc Hbun Hscr").
      (* the [iNext] here is what pays the Loeb later: [wp_vdrw_alloc3]'s
         continuation is guarded, and stripping it also strips "IH". *)
      iNext.
      (* [cpu_own]/[trap_csrs_pay] are opaque Definitions, so only the
         scheduler valid-context needs re-wrapping. *)
      iIntros (M1) "%Hcs1 %Hal Hcg Hout".
      rewrite /P1.vdrw_alloc_out. iDestruct "Hout" as "[Hok|Hfail]".
      { (* ============ all three won: hand the seam to P3 ============ *)
        iDestruct "Hok" as (h m2 t) "[%Hfacts [Hpc [Hidx [Hbh [Hbm [Hbt Hbun]]]]]]".
        destruct Hfacts as (Hh8 & Hm8 & Ht8 & Hhm & Hht & Hmt & Hfrh & Hfrm & Hfrt).
        rewrite /vdrw_p2_exit.
        iSpecialize ("Hexit" $! CIDlp with "[%]"); [wp_next_chain|].
        iApply ("Hexit" $! M1 np nr fl pk tr fr h m2 t with
                  "[%] [%] [%] [%] Hcg Hown Htc Hclm Hpc Htok
                   [Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring] Hbh Hbm Hbt Hidx").
        - split;
            [| exact (vdrw_hi_frame1 M M1 m0 Rs2 ltac:(vm_compute; reflexivity) Hcs1 Hhi)].
          unfold vdrw_regs. split_and!.
          + rewrite (Hcs1 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hsp.
          + rewrite (Hcs1 Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs0.
          + rewrite (Hcs1 Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs3.
          + rewrite (Hcs1 Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs6.
          + rewrite (Hcs1 Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs7.
        - unfold tri_ok. cbn. split_and!; assumption.
        - exact (vdrwb_tri_disj fr tr h m2 t Htok3 Hfrh Hfrm Hfrt).
        - exact Hal.
        - rewrite /vdrw_body. iFrame "Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring".
          iPureIntro. split_and!; try assumption.
          intros p T i HpT Hi.
          apply fr_upd_false_pres, fr_upd_false_pres, fr_upd_false_pres.
          exact (Htok3 p T i HpT Hi). }
      (* ============ the partial-free failure tail ============ *)
      iDestruct "Hfail" as "[Hpc Hfail]".
      (* the register facts that survive the allocator *)
      assert (Hsp1 : M1 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite (Hcs1 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hsp).
      assert (Hs01 : M1 !!! Regidx Rs0 = (sp0 : mword 64))
        by (rewrite (Hcs1 Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs0).
      assert (Hs31 : M1 !!! Regidx Rs3 = (b : mword 64))
        by (rewrite (Hcs1 Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs3).
      assert (Hs61 : M1 !!! Regidx Rs6 = wr)
        by (rewrite (Hcs1 Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs6).
      assert (Hs71 : M1 !!! Regidx Rs7 = sector)
        by (rewrite (Hcs1 Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs7).
      assert (Hs11 : M1 !!! Regidx Rs1 = (mword_of_int 8 : mword 64))
        by (rewrite (Hcs1 Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs1).
      assert (Hs41 : M1 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64))
        by (rewrite (Hcs1 Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs4).
      assert (Hs51 : M1 !!! Regidx Rs5 = (disk_base : mword 64))
        by (rewrite (Hcs1 Rs5 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs5).
      destruct Hal as [Hal11 Hal12].
      (* the addresses of idx[0] and idx[1], off the frame pointer *)
      assert (Hidx0a : add_vec (M1 !!! Regidx Rs0)
                         (sign_extend' 64 (mword_of_int 4000 : mword 12))
                       = (pa_stk sp0 12 : mword 64))
        by (rewrite Hs01; apply vdrw_idx0_addr).
      assert (Hidx1s : add_vec (sp0 : mword 64)
                         (sign_extend' 64 (mword_of_int 4004 : mword 12))
                       = (pa_add (pa_stk sp0 12) 4 : mword 64)).
      { rewrite vdrwb_sext_4004 (vdrw_pa_add_moi (pa_stk sp0 12) 4).
        unfold pa_stk, add_vec_int. rewrite vdrw_av2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      (* the common continuation: after the frees, the bundle is whole again *)
      iAssert ( ∀ (Mz : regfile),
                  ⌜forall r : mword 5, is_cs_idx r = true ->
                     Mz !!! Regidx r = M1 !!! Regidx r⌝ -∗
                  sie_cap_gpr KT1 Mz (trap_res eb + (K - 12))%nat false (proc_addr j) -∗
                  cpu_own 1 eb (proc_addr j) false ({["virtio_disk"]} ∪ lks) -∗
                  trap_csrs KT1 -∗
                  cpu_claim (proc_addr j) -∗
                  pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x094) : mword 64) -∗
                  locked γk cpu_id -∗
                  free_bundles pd fr -∗
                  vdrw_scratch (KTR := KT1) sp0 -∗
                  vdrw_p2_exit CID γk γs j γd pd pav pu K eb sp0 b wr sector m0 lks -∗
                  WP (Loop : expr riscv_lang))%I
        with "[Hpub Hlb Hcl Huidx Hflight Hparked Hring IH]" as "Hsleep".
      { iIntros (Mz) "%Hcsz Hcg Hown Htc Hclm Hpc Htok Hbun Hscr Hexit".
        assert (Hhiz : vdrw_hi Mz m0)
          by (exact (vdrw_hi_frame M1 Mz m0 Hcsz
                       (vdrw_hi_frame1 M M1 m0 Rs2 ltac:(vm_compute; reflexivity)
                          Hcs1 Hhi))).
        (* the register facts at Mz *)
        assert (Hspz : Mz !!! Regidx csp_rs1 = pa_stk sp0 12)
          by (rewrite (Hcsz csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp1).
        assert (Hs0z : Mz !!! Regidx Rs0 = (sp0 : mword 64))
          by (rewrite (Hcsz Rs0 ltac:(vm_compute; reflexivity)); exact Hs01).
        assert (Hs3z : Mz !!! Regidx Rs3 = (b : mword 64))
          by (rewrite (Hcsz Rs3 ltac:(vm_compute; reflexivity)); exact Hs31).
        assert (Hs6z : Mz !!! Regidx Rs6 = wr)
          by (rewrite (Hcsz Rs6 ltac:(vm_compute; reflexivity)); exact Hs61).
        assert (Hs7z : Mz !!! Regidx Rs7 = sector)
          by (rewrite (Hcsz Rs7 ltac:(vm_compute; reflexivity)); exact Hs71).
        assert (Hs1z : Mz !!! Regidx Rs1 = (mword_of_int 8 : mword 64))
          by (rewrite (Hcsz Rs1 ltac:(vm_compute; reflexivity)); exact Hs11).
        assert (Hs4z : Mz !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64))
          by (rewrite (Hcsz Rs4 ltac:(vm_compute; reflexivity)); exact Hs41).
        assert (Hs5z : Mz !!! Regidx Rs5 = (disk_base : mword 64))
          by (rewrite (Hcsz Rs5 ltac:(vm_compute; reflexivity)); exact Hs51).
        (* =============================================================== *)
        (* THE SLEEP PROTOCOL, IN FOUR CALLS.                              *)
        (*                                                                 *)
        (*   +0x094/+0x098/+0x09c  a0 := &disk.free[0]; sleep_prepare(a0)  *)
        (*   +0x0a0/+0x0a4/+0x0a8  a0 := &disk.vdisk_lock; release(a0)     *)
        (*   +0x0ac               sleep()                                  *)
        (*   +0x0b0/+0x0b4/+0x0b8  a0 := &disk.vdisk_lock; acquire(a0)     *)
        (*                                                                 *)
        (* The condition lock is no longer sleep's business: the caller     *)
        (* drops and retakes it itself, so what used to be one call with a  *)
        (* [lock_openable] parameter is now three ordinary contracts around *)
        (* SpecYield's.  THE PAIR IS STILL CARRIED, NOT PAID -- the loop    *)
        (* predicates hold [trap_csrs] and [cpu_claim pj] index-free -- but *)
        (* it must now be SPLIT across the window: release's pop_off wants  *)
        (* [arm_pay 0 eb pj] (which at [eb = true] IS the pair), and sleep  *)
        (* wants the complement [trap_csrs_ext eb ∗ cpu_claim_ext eb pj].   *)
        (* acquire's push_off hands [arm_pay] back and the two rejoin.      *)
        (* =============================================================== *)
        (* ---- +0x094 / +0x098  a0 := &disk.free[0] ---- *)
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x094) : mword 64) Ra0
                  (mword_of_int 30 : mword 20) Mz (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi094").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (B1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x094) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> Mz).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x094) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> Mz) with B1.
        assert (Hp098 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x094) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x098))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp098) in "Hpc".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x098) : mword 64) Ra0 Ra0
                  (mword_of_int 2940 : mword 12) B1 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi098").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (B2 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (B1 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 2940 : mword 12)))]> B1).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (B1 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 2940 : mword 12)))]> B1) with B2.
        assert (HB2a0 : B2 !!! Regidx Ra0 = (pa_add disk_base 24 : mword 64)).
        { rewrite /B2 upd_eq /B1 upd_eq.
          unfold disk_base, pa_add, add_vec_int.
          apply bv_eq; vm_compute; reflexivity. }
        assert (Hp09c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x098) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x09c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp09c) in "Hpc".
        (* ---- +0x09c  jal sleep_prepare ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x09c) : mword 64) Rra
                  (mword_of_int 2082216 : mword 21) B2 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi09c").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (B3 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x09c) : mword 64) 4)]> B2).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x09c) : mword 64) 4)]> B2) with B3.
        assert (Hjsp : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x09c) : mword 64)
                         (sign_extend' 64 (mword_of_int 2082216 : mword 21))
                       = mword_of_int KernelSyms.sleep_prepare)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjsp) in "Hpc".
        assert (HB3ra : B3 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x09c) : mword 64) 4)
          by (rewrite /B3; apply upd_eq).
        assert (HB3a0 : B3 !!! Regidx Ra0 = (pa_add disk_base 24 : mword 64)).
        { rewrite /B3 upd_ne; [| reg_neq]. exact HB2a0. }
        assert (HcsB3 : callee_saved Mz B3).
        { rewrite /B3 /B2 /B1.
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        (* re-close the lock's resource: the bundle is whole again.  It has
           to be whole BEFORE the release, which is the only consumer. *)
        iAssert (disk_res γd pd pav pu)
          with "[Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring]" as "HR".
        { iApply (vdrw_body_close γd pd pav pu np nr fl pk tr fr).
          rewrite /vdrw_body.
          iFrame "Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring".
          iPureIntro. split_and!; assumption. }
        (* ============== sleep_prepare(&disk.free[0]) ==============
           Noff-balanced and index-generic: it neither parks nor touches the
           lock, so the condition lock and its resource just ride along. *)
        iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γl B3
                  (trap_res eb + (K - 12))%nat 1%nat eb false
                  ({["virtio_disk"]} ∪ lks)
                  Hj Hjl ltac:(rewrite HB3a0; vm_compute; reflexivity) vdrwb_lvl1
                  ltac:(pose proof (vdrw_K22 K HK); lia)
                  ltac:(lkbelow)
                  with "Hcg Hown Htext Hpc Hpinv").
        all: try lkbelow.
        iApply wp_next_off_intro. iIntros (mfp) "%Hpcs Hcg Hown Hpc". rgall.
        assert (Hr0a0 : ret_pc (B3 !!! Regidx Rra)
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0a0))
          by (rewrite HB3ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr0a0) in "Hpc".
        (* ---- +0x0a0 / +0x0a4  a0 := &disk.vdisk_lock ---- *)
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a0) : mword 64) Ra0
                  (mword_of_int 30 : mword 20) mfp (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi0a0").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (C1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a0) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> mfp).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a0) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> mfp) with C1.
        assert (Hp0a4 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a0) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0a4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp0a4) in "Hpc".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a4) : mword 64) Ra0 Ra0
                  (mword_of_int 3200 : mword 12) C1 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi0a4").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (C2 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (C1 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 3200 : mword 12)))]> C1).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (C1 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 3200 : mword 12)))]> C1) with C2.
        assert (HC2a0 : C2 !!! Regidx Ra0 = (d_lock : mword 64)).
        { rewrite /C2 upd_eq /C1 upd_eq.
          unfold d_lock, disk_base, pa_add, add_vec_int.
          apply bv_eq; vm_compute; reflexivity. }
        assert (Hp0a8 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a4) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0a8))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp0a8) in "Hpc".
        (* ---- +0x0a8  jal release ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a8) : mword 64) Rra
                  (mword_of_int 2077434 : mword 21) C2 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0a8").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (C3 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a8) : mword 64) 4)]> C2).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a8) : mword 64) 4)]> C2) with C3.
        assert (Hjrl : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a8) : mword 64)
                         (sign_extend' 64 (mword_of_int 2077434 : mword 21))
                       = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrl) in "Hpc".
        assert (HC3ra : C3 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0a8) : mword 64) 4)
          by (rewrite /C3; apply upd_eq).
        assert (HC3a0 : add_vec (C3 !!! Regidx Ra0)
                          (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = (d_lock : mword 64)).
        { rewrite /C3 upd_ne; [| reg_neq]. rewrite HC2a0. apply vdrw_addv_sext0. }
        assert (HcsC3 : callee_saved mfp C3).
        { rewrite /C3 /C2 /C1.
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        (* the pair splits HERE: [arm_pay] goes into release's pop_off, the
           complement travels to sleep, and acquire's push_off rejoins them *)
        iDestruct (arm_pay_ext_split eb (proc_addr j) with "Htc Hclm")
          as "[Hpay [Hextc Hextm]]".
        (* ==================== release(&disk.vdisk_lock) ==================== *)
        iApply (Release.wp_release_sconf KT1 γk d_lock "virtio_disk"%string
                  (disk_res γd pd pav pu) C3 0%nat eb (proc_addr j) (K - 12)%nat
                  ({["virtio_disk"]} ∪ lks)
                  HC3a0 ltac:(pose proof (vdrw_K10 K HK); lia)
                  with "Hcg Htext Hpc Hlk Htok HR Hown Hpay").
        iIntros (CIDrl Hsrl mfr) "Hcg Hpc %Hrcs Hown". rgall.
        (* the balanced acquire/release pair leaves the held set where P2.3
           started: cancel the release's [∪ ∖] back down to the bare [lks]
           the sleep/re-acquire steps below (and [IH]) expect. *)
        assert (Hsetback : ({["virtio_disk"]} ∪ lks) ∖ {["virtio_disk"]} = lks)
          by (apply locks_add_del_below; exact Hbelow).
        iEval (rewrite Hsetback) in "Hown".
        assert (Hr0ac : ret_pc (C3 !!! Regidx Rra)
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0ac))
          by (rewrite HC3ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr0ac) in "Hpc".
        (* ---- +0x0ac  jal sleep ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0ac) : mword 64) Rra
                  (mword_of_int 2082260 : mword 21) mfr (K - 12)%nat eb
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0ac").
        iIntros (CIDjs Hsjs) "Hcg Hpc". rgall.
        set (C4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0ac) : mword 64) 4)]> mfr).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0ac) : mword 64) 4)]> mfr) with C4.
        assert (Hjsl : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0ac) : mword 64)
                         (sign_extend' 64 (mword_of_int 2082260 : mword 21))
                       = mword_of_int KernelSyms.sleep)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjsl) in "Hpc".
        assert (HC4ra : C4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0ac) : mword 64) 4)
          by (rewrite /C4; apply upd_eq).
        assert (HcsC4 : callee_saved mfr C4).
        { rewrite /C4. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        (* ============================ sleep() ============================
           THE PARK.  No condition lock in the contract at all: the caller
           holds NOTHING here beyond its own frame and the complement pair. *)
        iDestruct (cpu_own_transport CIDrl CIDjs 0 eb (proc_addr j) eb
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iDestruct (trap_csrs_ext_transport CIDlp CIDjs eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDlp CIDjs eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextm") as "Hextm".
        iApply (Sleep.wp_sleep_sconf γs j γl C4 (K - 12)%nat eb lks
                  Hj Hjl ltac:(pose proof (vdrw_K22 K HK); lia)
                  ltac:(lkbelow)
                  with "Hcg Hown Htext Hpc Hpinv Hextc Hextm").
        all: try lkbelow.
        (* SLEEP RETURNS ON HART [CIDsl]. *)
        iIntros (CIDsl Hssl mfs) "%Hscs Hcg Hown Hpc Hextc Hextm". rgall.
        assert (Hr0b0 : ret_pc (C4 !!! Regidx Rra)
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0b0))
          by (rewrite HC4ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr0b0) in "Hpc".
        (* ---- +0x0b0 / +0x0b4  a0 := &disk.vdisk_lock ---- *)
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b0) : mword 64) Ra0
                  (mword_of_int 30 : mword 20) mfs (K - 12)%nat eb
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi0b0").
        iIntros (CIDd1 Hsd1) "Hcg Hpc". rgall.
        set (D1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b0) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> mfs).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b0) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> mfs) with D1.
        assert (Hp0b4 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b0) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0b4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp0b4) in "Hpc".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b4) : mword 64) Ra0 Ra0
                  (mword_of_int 3184 : mword 12) D1 (K - 12)%nat eb
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi0b4").
        iIntros (CIDd2 Hsd2) "Hcg Hpc". rgall.
        set (D2 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (D1 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 3184 : mword 12)))]> D1).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (D1 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 3184 : mword 12)))]> D1) with D2.
        assert (HD2a0 : D2 !!! Regidx Ra0 = (d_lock : mword 64)).
        { rewrite /D2 upd_eq /D1 upd_eq.
          unfold d_lock, disk_base, pa_add, add_vec_int.
          apply bv_eq; vm_compute; reflexivity. }
        assert (Hp0b8 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b4) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0b8))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp0b8) in "Hpc".
        (* ---- +0x0b8  jal acquire ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b8) : mword 64) Rra
                  (mword_of_int 2077282 : mword 21) D2 (K - 12)%nat eb
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0b8").
        iIntros (CIDd3 Hsd3) "Hcg Hpc". rgall.
        set (D3 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b8) : mword 64) 4)]> D2).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b8) : mword 64) 4)]> D2) with D3.
        assert (Hjaq : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b8) : mword 64)
                         (sign_extend' 64 (mword_of_int 2077282 : mword 21))
                       = mword_of_int KernelSyms.acquire)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjaq) in "Hpc".
        assert (HD3ra : D3 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x0b8) : mword 64) 4)
          by (rewrite /D3; apply upd_eq).
        assert (HD3a0 : D3 !!! Regidx Ra0 = (d_lock : mword 64)).
        { rewrite /D3 upd_ne; [| reg_neq]. exact HD2a0. }
        assert (HcsD3 : callee_saved mfs D3).
        { rewrite /D3 /D2 /D1.
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        (* ==================== acquire(&disk.vdisk_lock) ==================== *)
        iDestruct (cpu_own_transport CIDsl CIDd3 0 eb (proc_addr j) eb
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Acquire.wp_acquire_sconf KT1 γk "virtio_disk"%string
                  (disk_res γd pd pav pu) D3 0%nat eb (proc_addr j) (K - 12)%nat eb lks
                  vdrw_noff0 ltac:(pose proof (vdrw_K10 K HK); lia) Hbelow
                  with "Hcg Hown Htext Hpc []").
        all: try lkbelow.
        { iEval (rewrite HD3a0). iExact "Hlk". }
        iIntros (CIDaq Hsaq msA mfa) "_ Hcg Hpc %Hacs Htok HR Hown Hpay". rgall.
        assert (Hr0bc : ret_pc (D3 !!! Regidx Rra)
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x0bc))
          by (rewrite HD3ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr0bc) in "Hpc".
        (* the complement travelled the park; rejoin it with acquire's pay *)
        iDestruct (trap_csrs_ext_transport CIDsl CIDaq eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDsl CIDaq eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (arm_pay_ext_join eb (proc_addr j) with "Hpay [$Hextc $Hextm]")
          as "[Htc Hclm]".
        (* ---- the back edge ---- *)
        assert (Hcsf : callee_saved Mz mfa).
        { eapply callee_saved_trans; [exact HcsB3|].
          eapply callee_saved_trans; [exact Hpcs|].
          eapply callee_saved_trans; [exact HcsC3|].
          eapply callee_saved_trans; [exact Hrcs|].
          eapply callee_saved_trans; [exact HcsC4|].
          eapply callee_saved_trans; [exact Hscs|].
          eapply callee_saved_trans; [exact HcsD3|].
          exact Hacs. }
        iSpecialize ("IH" $! CIDaq with "[%]"); [wp_next_chain|].
        iApply ("IH" $! mfa with "[%] Hcg Hown Htc Hclm Hpc Htok HR Hscr Hexit").
        unfold vdrw_regs. split_and!.
        - rewrite (proj1 Hcsf). exact Hspz.
        - rewrite (callee_saved_lookup Hcsf Rs0 ltac:(vm_compute; reflexivity)). exact Hs0z.
        - rewrite (callee_saved_lookup Hcsf Rs3 ltac:(vm_compute; reflexivity)). exact Hs3z.
        - rewrite (callee_saved_lookup Hcsf Rs6 ltac:(vm_compute; reflexivity)). exact Hs6z.
        - rewrite (callee_saved_lookup Hcsf Rs7 ltac:(vm_compute; reflexivity)). exact Hs7z.
        - rewrite (callee_saved_lookup Hcsf Rs1 ltac:(vm_compute; reflexivity)). exact Hs1z.
        - rewrite (callee_saved_lookup Hcsf Rs4 ltac:(vm_compute; reflexivity)). exact Hs4z.
        - rewrite (callee_saved_lookup Hcsf Rs5 ltac:(vm_compute; reflexivity)). exact Hs5z.
        - exact (vdrw_hi_cs Mz mfa m0 Hcsf Hhiz). }
      (* ---- +0x07a  bge x0,s2 : nothing allocated? ---- *)
      rewrite /P1.vdrw_alloc_fail.
      iDestruct "Hfail" as "[H0|[H1|H2]]".
      - (* ---------------- s2 = 0: no descriptor to give back ------------- *)
        iDestruct "H0" as "(%Hs2 & Hbun & Hidx)".
        iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64)
                  (mword_of_int 26 : mword 13) Rs2 M1 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite Hs2; exact vdrwb_bge0)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi07a").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hb094 : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64)
                          (sign_extend' 64 (mword_of_int 26 : mword 13))
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x094))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hb094) in "Hpc".
        iDestruct "Hidx" as (v0 v1 v2) "Hidx".
        iApply ("Hsleep" $! M1 with
                  "[%] Hcg Hown Htc Hclm Hpc Htok Hbun
                   [Hidx] Hexit").
        { intros r Hr. reflexivity. }
        iApply (vdrw_idx_join (KTR := KT1) sp0 v0 v1 v2 Hal11 Hal12 with "Hidx").
      - (* ---------------- s2 = 1: one descriptor to give back ------------ *)
        iDestruct "H1" as (h) "(%Hh & Hbun & Hbh & Hidx)".
        destruct Hh as (Hh8 & Hfrh & Hs2).
        iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64)
                  (mword_of_int 26 : mword 13) Rs2 M1 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite Hs2; exact vdrwb_bge1)
                  with "Hcg Hpc Hi07a").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hp07e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x07e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp07e) in "Hpc".
        iDestruct "Hidx" as (v1 v2) "Hidx".
        iDestruct "Hidx" as "(Hx0 & Hx1 & Hx2 & Hxp)".
        iApply (wp_vdrw_free_at (CID := CIDlp)  γs pd h (fr_upd fr h false) M1 (trap_res eb + (K - 12))%nat
                  eb (proc_addr j) (pa_stk sp0 12) 0x07e
                  (mword_of_int 4000 : mword 12) (mword_of_int 2096448 : mword 21)
                  ({["virtio_disk"]} ∪ lks)
                  ltac:(pose proof (vdrwb_K20 K HK); lia) Hh8 (fr_upd_eq fr h false) Hlen Hidx0a
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(lkbelow)
                  with "Hcg Hown Htext Hpc Hpinv Hdp Hi07e Hi082 Hx0 Hbun Hbh").
        iIntros (M2) "%Hcs2 Hcg Hown Hpc Hx0 Hbun".
        (* +0x086  c.li a5,1 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x086) : mword 64) Ra5
                  (mword_of_int 1 : mword 6) (mword_of_int (Z.of_nat 1) : mword 64)
                  M2 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  vdrwb_li1 with "Hcg Hpc Hi086").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (F1 := <[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2).
        change (<[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2) with F1.
        assert (Hp088 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x086) : mword 64) 2
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x088))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp088) in "Hpc".
        assert (HF1a5 : F1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat 1) : mword 64))
          by (rewrite /F1; apply upd_eq).
        assert (HF1s2 : F1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat 1) : mword 64)).
        { rewrite /F1 upd_ne; [| reg_neq].
          rewrite (Hcs2 Rs2 ltac:(vm_compute; reflexivity)). exact Hs2. }
        (* +0x088  bge a5,s2 : 1 >= 1, TAKEN *)
        iApply (wp_bge_taken_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x088) : mword 64)
                  (mword_of_int 12 : mword 13) Rs2 Ra5 F1 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite HF1a5 HF1s2; exact vdrwb_bge11)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi088").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hb094' : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x088) : mword 64)
                           (sign_extend' 64 (mword_of_int 12 : mword 13))
                         = mword_of_int (KernelSyms.virtio_disk_rw + 0x094))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hb094') in "Hpc".
        iApply ("Hsleep" $! F1 with
                  "[%] Hcg Hown Htc Hclm Hpc Htok [Hbun] [Hx0 Hx1 Hx2 Hxp] Hexit").
        { intros r Hr. rewrite /F1 upd_ne;
            [| apply not_eq_sym, is_cs_idx_true_neq;
               [vm_compute; reflexivity | exact Hr]].
          exact (Hcs2 r Hr). }
        { iApply (free_bundles_ext pd (fr_upd (fr_upd fr h false) h true) fr).
          { intros i _. destruct (Nat.eq_dec i h) as [->|Hne].
            - rewrite fr_upd_eq. symmetry. exact Hfrh.
            - rewrite (fr_upd_ne _ h i true Hne) (fr_upd_ne _ h i false Hne). reflexivity. }
          iExact "Hbun". }
        iApply (vdrw_idx_join (KTR := KT1) sp0 (mword_of_int (Z.of_nat h)) v1 v2 Hal11 Hal12).
        rewrite /vdrw_idx. iFrame "Hx0 Hx1 Hx2 Hxp".
      - (* ---------------- s2 = 2: two descriptors to give back ----------- *)
        iDestruct "H2" as (h m2) "(%Hh & Hbun & Hbh & Hbm & Hidx)".
        destruct Hh as (Hh8 & Hm8 & Hhm & Hfrh & Hfrm & Hs2).
        iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64)
                  (mword_of_int 26 : mword 13) Rs2 M1 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite Hs2; exact vdrwb_bge2)
                  with "Hcg Hpc Hi07a").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hp07e : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x07a) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x07e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp07e) in "Hpc".
        iDestruct "Hidx" as (v2) "Hidx".
        iDestruct "Hidx" as "(Hx0 & Hx1 & Hx2 & Hxp)".
        (* the first free: descriptor h, whose cell the allocator cleared *)
        assert (Hfrh' : fr_upd (fr_upd fr h false) m2 false h = false)
          by (rewrite (fr_upd_ne _ m2 h false Hhm); apply fr_upd_eq).
        iApply (wp_vdrw_free_at (CID := CIDlp)  γs pd h
                  (fr_upd (fr_upd fr h false) m2 false) M1 (trap_res eb + (K - 12))%nat
                  eb (proc_addr j) (pa_stk sp0 12) 0x07e
                  (mword_of_int 4000 : mword 12) (mword_of_int 2096448 : mword 21)
                  ({["virtio_disk"]} ∪ lks)
                  ltac:(pose proof (vdrwb_K20 K HK); lia) Hh8 Hfrh' Hlen Hidx0a
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(lkbelow)
                  with "Hcg Hown Htext Hpc Hpinv Hdp Hi07e Hi082 Hx0 Hbun Hbh").
        iIntros (M2) "%Hcs2 Hcg Hown Hpc Hx0 Hbun".
        (* +0x086  c.li a5,1 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x086) : mword 64) Ra5
                  (mword_of_int 1 : mword 6) (mword_of_int (Z.of_nat 1) : mword 64)
                  M2 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  vdrwb_li1 with "Hcg Hpc Hi086").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        set (G1 := <[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2).
        change (<[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2) with G1.
        assert (Hp088 : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x086) : mword 64) 2
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x088))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp088) in "Hpc".
        assert (HG1a5 : G1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat 1) : mword 64))
          by (rewrite /G1; apply upd_eq).
        assert (HG1s2 : G1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat 2) : mword 64)).
        { rewrite /G1 upd_ne; [| reg_neq].
          rewrite (Hcs2 Rs2 ltac:(vm_compute; reflexivity)). exact Hs2. }
        assert (HG1s0 : G1 !!! Regidx Rs0 = (sp0 : mword 64)).
        { rewrite /G1 upd_ne; [| reg_neq].
          rewrite (Hcs2 Rs0 ltac:(vm_compute; reflexivity)). exact Hs01. }
        (* +0x088  bge a5,s2 : 1 >= 2 is false, FALL THROUGH *)
        iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x088) : mword 64)
                  (mword_of_int 12 : mword 13) Rs2 Ra5 G1 (trap_res eb + (K - 12))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgall; rewrite HG1a5 HG1s2; exact vdrwb_bge12)
                  with "Hcg Hpc Hi088").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hp08c : add_vec_int (mword_of_int (KernelSyms.virtio_disk_rw + 0x088) : mword 64) 4
                        = mword_of_int (KernelSyms.virtio_disk_rw + 0x08c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp08c) in "Hpc".
        (* the second free: descriptor m2 *)
        assert (Hidx1a' : add_vec (G1 !!! Regidx Rs0)
                            (sign_extend' 64 (mword_of_int 4004 : mword 12))
                          = (pa_add (pa_stk sp0 12) 4 : mword 64))
          by (rewrite HG1s0; exact Hidx1s).
        assert (Hfrm' : fr_upd (fr_upd (fr_upd fr h false) m2 false) h true m2 = false).
        { rewrite (fr_upd_ne _ h m2 true (not_eq_sym Hhm)). apply fr_upd_eq. }
        iApply (wp_vdrw_free_at (CID := CIDlp)  γs pd m2
                  (fr_upd (fr_upd (fr_upd fr h false) m2 false) h true) G1 (trap_res eb + (K - 12))%nat
                  eb (proc_addr j) (pa_add (pa_stk sp0 12) 4) 0x08c
                  (mword_of_int 4004 : mword 12) (mword_of_int 2096434 : mword 21)
                  ({["virtio_disk"]} ∪ lks)
                  ltac:(pose proof (vdrwb_K20 K HK); lia) Hm8 Hfrm' Hlen Hidx1a'
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(lkbelow)
                  with "Hcg Hown Htext Hpc Hpinv Hdp Hi08c Hi090 Hx1 Hbun Hbm").
        iIntros (M3) "%Hcs3 Hcg Hown Hpc Hx1 Hbun".
        iApply ("Hsleep" $! M3 with
                  "[%] Hcg Hown Htc Hclm Hpc Htok [Hbun] [Hx0 Hx1 Hx2 Hxp] Hexit").
        { intros r Hr. rewrite (Hcs3 r Hr).
          rewrite /G1 upd_ne;
            [| apply not_eq_sym, is_cs_idx_true_neq;
               [vm_compute; reflexivity | exact Hr]].
          exact (Hcs2 r Hr). }
        { iApply (free_bundles_ext pd
                    (fr_upd (fr_upd (fr_upd (fr_upd fr h false) m2 false) h true) m2 true)
                    fr).
          { intros i _. destruct (Nat.eq_dec i m2) as [->|Hnem].
            - rewrite fr_upd_eq. symmetry. exact Hfrm.
            - rewrite (fr_upd_ne _ m2 i true Hnem).
              destruct (Nat.eq_dec i h) as [->|Hneh].
              + rewrite fr_upd_eq. symmetry. exact Hfrh.
              + rewrite (fr_upd_ne _ h i true Hneh) (fr_upd_ne _ m2 i false Hnem)
                        (fr_upd_ne _ h i false Hneh). reflexivity. }
          iExact "Hbun". }
        iApply (vdrw_idx_join (KTR := KT1) sp0 (mword_of_int (Z.of_nat h))
                  (mword_of_int (Z.of_nat m2)) v2 Hal11 Hal12).
        rewrite /vdrw_idx. iFrame "Hx0 Hx1 Hx2 Hxp". }
    (* ---- +0x044  c.j -> +0x0bc : enter the loop ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.virtio_disk_rw + 0x044) : mword 64)
              (sign_extend' 21 (concat_vec (mword_of_int 60 : mword 11) ('b"0")))
              A5 (trap_res eb + (K - 12))%nat false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi044").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hj0a8 : add_vec (mword_of_int (KernelSyms.virtio_disk_rw + 0x044) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 60 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.virtio_disk_rw + 0x0bc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hj0a8) in "Hpc".
    rewrite /vdrw_p2_loop.
    iSpecialize ("Hloop" $! CID with "[%]"); [wp_next_chain|].
    iApply ("Hloop" $! A5 with "[%] Hcg Hown Htc Hclm Hpc Htok HR Hscr Hexit").
    split_and!; [ exact HA5regs | exact HA5s1 | exact HA5s4 | exact HA5s5
                | vdrw_hi_peel; exact Hhi0 ].
  Qed.

End ProofVirtioDiskRwB.
End VirtioDiskRwRest.

