(* Shared base for the S-mode per-decode-family leaf files (WpSmode<Family>.v).
   Holds the shared kernel-window instruction tactics and re-exports the M-mode
   leaf base. Primitives are Require Import (local, non-propagating) to avoid
   changing notation resolution in downstream files. *)
Require Import WpMmodeLeafBase.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras RiscvTryStep.
Require Import WpLeafCommon WpGpr MinstretInv InstrBytes RiscvModelBytes WpDecode.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From stdpp Require Import bitvector.definitions gmap.

Require Import SmodeCore WpSmodeGpr.
Require Import StackOwn CalleeSaved WpEntryNew.
From Kernel Require Import KernelInstrs KernelSyms.
Import Defs.
Local Open Scope Z_scope.

Ltac mk_rvc4 A h w pc ast decname expname :=
  let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
  let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
  let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
  assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
  assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
  assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
  assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
  assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
  assert (Hbytes : forall j, (j < 4)%nat ->
      KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
    by (intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
  iIntros "#Ht"; rewrite /instr;
  iSplitR; [iPureIntro; exact Hlpad|];
  iExists (F_RVC h);
  iSplitR; [iPureIntro; reflexivity|];
  iSplitL "";
  [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
    iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
  | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
    eexists; (split; [ apply decname; assumption
                     | split; [ vm_compute; reflexivity
                              | intro; apply expname ] ]) ].

Ltac mk_rvc2 A h pc ast decname expname :=
  let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
  let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
  let Hbytes := fresh "Hbytes" in
  assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
  assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
  assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
  assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
  assert (Hbytes : forall j, (j < 2)%nat ->
      KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
    by (intros j Hj;
        do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
  iIntros "#Ht"; rewrite /instr;
  iSplitR; [iPureIntro; exact Hlpad|];
  iExists (F_RVC h);
  iSplitR; [iPureIntro; reflexivity|];
  iSplitL "";
  [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
    iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
  | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
    eexists; (split; [ apply decname; assumption
                     | split; [ vm_compute; reflexivity
                              | intro; apply expname ] ]) ].

Ltac mk_base A w pc ast decname :=
  let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
  let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
  assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
  assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
  assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
  assert (Hbytes : forall j, (j < 4)%nat ->
      KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
    by (intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
  iIntros "#Ht"; rewrite /instr;
  iSplitR; [iPureIntro; exact Hlpad|];
  iExists (F_Base w);
  iSplitR; [iPureIntro; reflexivity|];
  iSplitL "";
  [ iApply (instr_bytes_base pc w H2al Hnrvc);
    iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
  | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].
