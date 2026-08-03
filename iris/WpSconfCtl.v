(* WpSconfCtl.v -- the SIE-AGNOSTIC control-flow leaf layer
   (interrupt-sweep stage 5): [sconf]+[sie_cap] twins of
   WpSmodePtCtl.v's fence / c.j / jal / c.ret leaves over the agnostic
   funnel [wp_instr_s_sconf].

   Spec cleanups made in this pass:
     - the config premises are gone as everywhere in the sweep;
     - [wp_cj_s_sconf] hands the step's later out: an unconditional
       backward jump is a loop back edge exactly like a taken branch
       (the `_pt` original absorbed it); jal/c.ret keep the later-free
       shape (call/return sites are straight-line);
     - jal carries the sweep's [rd_ok rd] premise (link-register
       write); c.j and c.ret write no register, so [sconf]/[sie_cap]
       pass through (c.j untouched, c.ret opened only for the
       LPE/priv/misa side conditions).
   The csrr/csrrci-sstatus and sret leaves are NOT here: sret runs in
   kernelvec's SIE=0 body and the csr flips are stage 7.               *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes WpDecode ExecCommon WpGpr WpGprCsrwCommon RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import WpSmodePtCtl.
Require Import WpMmodeLeafBase.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Import Defs.

(* ---- Local helpers (copies: the originals are Local in WpSmodePtCtl.v /
   ProofSpin.v; [exec_execute_FENCE_S] is exported and imported). ---- *)

Local Lemma exec_execute_JAL_zreg_zca (imm : mword 21) s :
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute_JAL imm zreg) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Halign Hzca.
    unfold execute_JAL, get_next_pc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
    cbn match.
    unfold zreg.
    rewrite (exec_bind0_Some _ _ _ _ _
      (exec_wX_bits_gpr (zero_extend' 5 ('b"00")) (register_lookup nextPC s.(sregs))
         (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))))).
    apply exec_returnm.
  Qed.

Local Lemma exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  match goal with |- context[Defs.bind0 ?wx _] =>
    assert (Hwx : exec wx (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  = Some (tt, set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                                (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (register_lookup nextPC s.(sregs)))))
  end.
  { rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs)) _).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.


Section WpSconfCtl.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ------------------------------------------------------------------- *)
  (* fence -- state-preserving at ANY pred/succ pair (the model's whole   *)
  (* dispatch is barriers, and a barrier is a no-op in the functional     *)
  (* interpreter); the config is opened only for the priv/menvcfg side    *)
  (* conditions.  gcc emits two of them in xv6: `fence rw,w` for          *)
  (* [__sync_lock_release] (release) and `fence rw,rw` for                *)
  (* [__sync_synchronize] (the virtio driver), and both are this leaf.    *)
  (* [wp_fence_s_sconf] below is the rw,w restatement (WRAPPER RECIPE).   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_fence_gen_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (fm pred succ : mword 4) (rs rd : regidx)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (FENCE (fm, pred, succ, rs, rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (FENCE (fm, pred, succ, rs, rd))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_FENCE_S menvcfg0 fm pred succ rs rd s_pc
               Lpriv_pc Lmenv_pc Hfiom). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert sconf with "[Hpriv Hmsx Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmsx Hmiex".
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: the funnel resumes on the SAME hart (fence is not a trap
       boundary), so the step's [wp_next] obligation is discharged here. *)
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* the rw,w instance -- [release]'s [__sync_lock_release] barrier.  A
     restatement of the generic leaf (WRAPPER RECIPE), so the existing call
     sites do not change. *)
  Lemma wp_fence_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                           Regidx (mword_of_int 0), Regidx (mword_of_int 0))) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    exact (wp_fence_gen_s_sconf Φ pc (mword_of_int 0) (mword_of_int 3) (mword_of_int 1)
             (Regidx (mword_of_int 0)) (Regidx (mword_of_int 0)) m n b).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* fence, LATER-EXPOSING.  Same statement as [wp_fence_gen_s_sconf]      *)
  (* except that the continuation is under a [▷] -- as [wp_cj_s_sconf]      *)
  (* below.  A fence IS a program step, so the later is there to be had;    *)
  (* the plain leaf just does not hand it out, and a caller that has         *)
  (* nothing to strip should keep using it.                                 *)
  (*                                                                        *)
  (* Who needs it: main()'s secondary arm.  Its spin loop EXITS through the  *)
  (* fall-through of [beqz a5], and the [started] invariant's payload        *)
  (* arrives under a [▷] (opening an invariant always yields its body that   *)
  (* way, and the payload is persistent but not timeless).  Every leaf the   *)
  (* arm then runs applies its continuation later-free, so without this one  *)
  (* the [▷ P] can never be stripped.  The fence is also the semantically    *)
  (* right place for it: [fence rw,rw] IS the acquire barrier, so the        *)
  (* reading the proof wants is that the fence is where [▷ P] becomes [P].   *)
  (* See claude-notes/projects/main-boot.md (G4).                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_fence_gen_later_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (fm pred succ : mword 4) (rs rd : regidx)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (FENCE (fm, pred, succ, rs, rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ▷ ( sie_cap_gpr m n b p -∗
        pc_is (add_vec_int pc 4) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (FENCE (fm, pred, succ, rs, rd))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_FENCE_S menvcfg0 fm pred succ rs rd s_pc
               Lpriv_pc Lmenv_pc Hfiom). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert sconf with "[Hpriv Hmsx Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmsx Hmiex".
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: same-hart resume -- pin [wp_next] at [cpu_id] first (the
       pure obligation is [eq_refl], closed by [//]), THEN [iNext] so it
       strips the later from the now-concrete continuation AND the goal
       together. *)
    iSpecialize ("Hcont" $! cpu_id with "[//]").
    iNext.
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.j -- unconditional jump; a backward jump is a loop back edge, so   *)
  (* the continuation is UNDER A LATER (straight-line callers [iNext]).   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cj_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (jimm : mword 21)
      (m : regfile) (n : nat) (b : bool) :
    let tgt := add_vec pc (sign_extend' 64 jimm) in
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc true (JAL (jimm, zreg)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ▷ ( sie_cap_gpr m n b p -∗
        pc_is tgt -∗
        WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros tgt Hal0.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc true (JAL (jimm, zreg))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (HzcaC : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
    assert (Halign_spc : eq_vec (access_vec_dec
              (add_vec (register_lookup PC s_pc.(sregs)) (sign_extend' 64 jimm)) 0) ('b"0") = true).
    { rewrite Hpcv. exact Hal0. }
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      change (execute (JAL (jimm, zreg))) with (execute_JAL jimm zreg).
      rewrite (exec_execute_JAL_zreg_zca jimm s_pc Halign_spc
                 (exec_currentlyEnabled_Zca s_pc HzcaC)).
      rewrite Hpcv. reflexivity. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert sconf with "[$Hhw $Hsc2]" as "Hsc".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: c.j resumes on the SAME hart (the absorbing engine already
       took/handled any pending traps before this callback runs). *)
    iSpecialize ("Hcont" $! cpu_id with "[//]").
    iNext.
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* jal rd -- link write + jump.                                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_jal_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (JAL (imm, Regidx rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok Hal0) "Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b Φ pc false (JAL (imm, Regidx rd))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Hlink : register_lookup nextPC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (Lmisa1 : register_lookup misa (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = misa0).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (add_vec_int pc 4))
                 with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                        nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr_zca imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd ltac:(rewrite Hpcv; exact Hal0)
                 (exec_currentlyEnabled_Zca (set_reg σ nextPC (add_vec_int pc 4)) ltac:(rewrite Lmisa1; exact HmisaC))).
      rewrite Hpcv. rewrite Hlink. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    (* the leaf's own write commutes with the tp pin *)
    tp_refold Hrdtp "Hfile".
    iDestruct (sie_cap_retarget m
                 (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) n b Hsp with "Hcap") as "Hcap".
    iAssert sconf with "[$Hhw $Hsc2]" as "Hsc".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: jal resumes on the SAME hart. *)
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ret (jalr x0, 0(ra)) -- no register write; the bundle is opened    *)
  (* for the LPE/priv/misa side conditions and reassembled.               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cret_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (ra : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let tgt := ret_pc (rget m ra) in
    uint ra <> 0 ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is tgt -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros tgt Hra.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc true (JALR (zeros' 12, Regidx ra, zreg))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx ra) with "Hfile") as "[Hrac Hfb]".
    iDestruct (gpr_pt_value ra (tp_pin m (Regidx ra)) s_pc with "Hreg Hrac") as %Lra.
    iDestruct ("Hfb" with "Hrac") as "Hfile".
    assert (Lra' : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs) = rget m ra).
    { pose proof Lra as H.
      replace (Z.eqb (uint ra) 0) with false in H by (symmetry; apply Z.eqb_neq; exact Hra).
      cbn match in H. exact H. }
    assert (Hpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Hmenv_spc : register_lookup menvcfg s_pc.(sregs) = menvcfg0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmenv | vm_compute; reflexivity ]. }
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc = Some (false, s_pc)).
    { apply exec_cE_zicfilp_false_S; [ exact Hpriv_spc | rewrite Hmenv_spc; exact Hlpe ]. }
    assert (Hmisa_spc : register_lookup misa s_pc.(sregs) = misa0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) s_pc = Some (true, s_pc)).
    { apply exec_currentlyEnabled_Zca. rewrite Hmisa_spc. exact HmisaC. }
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change (execute (JALR (zeros' 12, Regidx ra, zreg)))
        with (execute_JALR (zeros' 12) (Regidx ra) zreg).
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htgt : update_vec_dec (add_vec
                (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs))
                (sign_extend' 64 (zeros' 12))) 0 ('b"0") = tgt)
        by (rewrite Lra'; apply ret_pc_jalr).
      rewrite <- Htgt.
      apply (exec_execute_JALR_ret_zca (zeros' 12) ra (zero_extend' 5 ('b"00") : mword 5) s_pc
               Hra ltac:(vm_compute; reflexivity) Hzic Hzca).
      rewrite Htgt. apply ret_pc_aligned. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert sconf with "[Hpriv Hmsx Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmsx Hmiex".
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: c.ret resumes on the SAME hart. *)
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

End WpSconfCtl.
