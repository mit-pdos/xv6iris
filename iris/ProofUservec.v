(* ProofUservec.v -- THE USERVEC WP over the ptree invariants, sealed behind
   [SpecUservec.USERVEC]: all 44 trap-entry instructions of the trampoline
   page chained, from the trapped-out-of-user machine ([user_trap_frame],
   the USER table installed) through the [csrw sscratch] / [li a0,TRAPFRAME]
   prologue, the 31 register-save stores into the TRAPFRAME page, the four
   kernel-context loads, and the satp switch back to the KERNEL table --
   THEN, where the old (pre-chaining) version stopped, straight into
   [UT.wp_usertrap] and, once that returns, [UR.wp_userret_pt], discharging
   [uservec_post] at the far end.  A functor over both, per SpecUservec.v's
   header.

   THE TRAPFRAME OPENS TWICE.  [usertrap_res] is the one owner of the
   trapframe page, at the PHYSICAL tier natively (ProcInv.v) -- the SAME
   tier this file's own 44/31-instruction walks already use, so opening it
   (via [UT.usertrap_res_tf_open]) hands the walk its cells directly, no
   phys<->mem crossing.  Once for the SAVE walk below, resealed just before
   the call into usertrap; once more (a FRESH open, after usertrap hands a
   FRESH [usertrap_res] back, possibly on a different hart) for userret's
   own RESTORE walk, resealed again at the very end for [uservec_post]'s
   own leftover.  [tf_page_open36] (just below) is the reusable 36-word
   extraction both opens use. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import WpMmodeLeafBase WpMmodeSwpBase.
Require Import SmodeCore.
Require Import TrampPt UptTree.
Require Import UserretDefs UserretPt.
Require Import UservecDefs UservecPt UservecExitPt.
Require Import WpIntrCore.
Require Import UserPtTree UserExec UserKernelBridge.
Require Import ProcInv ProcGeom.
Require Import ProcPtOwn.
Require Import WpNext.
(* the classes [usertrap_res]'s own signature needs -- see SpecUservec.v's
   own note on the same trap (must Require directly, not just
   transitively, or unqualified names below auto-generalize as fresh,
   unrelated variables instead of resolving to the concrete classes). *)
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import LogInv.
Require Import IrefSlots.
Require Import IntrDefs.   (* [hart_csrs]: the residue's per-hart CSR bundle *)
Require Import SpecUsertrap.
Require Import SpecUserret.
Require Import SpecUservec.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import TfPage36.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Require Import ParkCap.   (* [park_token] *)
Require Import UsertrapRes UtResFits.  (* [ut_park_intro_body] -- the park's producer entry *)
Require Import TsoCtx.   (* [CurCtx]: the residue owns a thread token *)
Import Defs.

Module UservecProof (UT : UtResFits.USERTRAP_PARK) (UR : SpecUserret.USERRET) : USERVEC.

Section UservecAllPt.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Definition usertrap_res := UT.usertrap_res.
  Definition usertrap_res_parked := UT.usertrap_res_parked.
  Definition usertrap_res_bare := UT.usertrap_res_bare.
  Definition usertrap_res_tf_open := UT.usertrap_res_tf_open.
  (* ...and the park's one producer-side entry, threaded like the rest.
     A file that merely passes the residue through has nothing to say about
     it; the entry exists so that whoever PARKS a never-run process can
     build one (UsertrapRes.v, "THE PARK'S CHANNEL THROUGH THE MODULE
     TYPES"). *)
  Definition usertrap_res_bare_park
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{XI : CurCtx}
      (N : ut_names) (av : nat)
    : ut_park_intro_body
        (fun (h : CpuId) (Xc : CurCtx) => UT.usertrap_res_bare (CID := h) (XI := Xc))
        (park_token (un_s N)) N av
    := UT.usertrap_res_bare_park N av.
  Definition usertrap_res_csrs_open := UT.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := UT.usertrap_res_sstc.
  Definition usertrap_res_tf_csrs_open := UT.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tlb_close := UT.usertrap_res_tlb_close.
  Definition usertrap_res_tlb_open := UT.usertrap_res_tlb_open.
  Definition usertrap_res_pt_close := UT.usertrap_res_pt_close.
  Definition usertrap_res_pt_open := UT.usertrap_res_pt_open.
  Definition usertrap_res_bare_norm := UT.usertrap_res_bare_norm.

  (* the user invariant already carries the map well-formedness the exit
     switch needs *)
  Lemma uv_utlb_map_wf (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
    utlb_inv_pt uroot tfp um -∗ ⌜upt_map_wf um⌝.
  Proof.
    iIntros "H". iDestruct "H" as (usatp tlbvec t)
      "(_ & _ & _ & _ & _ & _ & _ & %Hwf & _ & _ & _)".
    iPureIntro. exact Hwf.
  Qed.


  Lemma wp_uservec_pt (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (j : nat) (vksp : mword 64) :
    (* [UT.]-qualified, not the section alias: inside a section that FIXES
       [CID], the alias has no [CID] implicit left to instantiate (section
       variables are discharged only at [End]).  The module-type parameter
       still does, and the two are convertible, so the [: USERVEC] check
       accepts it. *)
    wp_uservec_pt_body (fun h : CpuId => UT.usertrap_res_bare (CID := h))
      C pt Rut j vksp.
  Proof.
    cbv beta zeta delta [wp_uservec_pt_body].
    (* [tf_pa] deliberately NOT unfolded here: its 35 trapframe cells ride in
       the Iris context for every one of this proof's ~600 steps, and every
       step's proof term embeds the whole context twice, so an unfolded
       address (~260 nodes vs ~12) is 14 % of the proof TERM.  The leaves
       unify through the definition. See claude-notes/optimization.md. *)
    unfold uservec_gpr.
    intros Hstvec Hdqc Hmie Hjlt Hnorm Hptwf.
    iIntros "#Hkt #Hhw #Hinv #Hclaim Hframe Hures Hcont".
    (* ============ open the trapped machine ============ *)
    iDestruct (user_trap_frame_open C pt Rut with "Hframe") as (ms_v sc_v stval_v sepc_v g)
      "(%Hok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hfile &
        Hutlb & Hdata & %Hcov & %Hacc & Hstvec & Hmie & Hmdl & Hmedl &
        Hmenv & Hsenv & Hmse & Hsse & Hrut)".
    pose proof Hok as Hok2.
    destruct Hok2 as (HSXL & HMPRV & HMXR & HSPP & HSIE & HTVM & HTSR).
    pose proof (uc_mm C) as Hmm.
    assert (Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM MENVCFG_S) = PMM_Disabled)
      by (vm_compute; reflexivity).
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (Hmenvval0 : (MENVCFG_S : mword 64) = MENVCFG_S) by reflexivity.
    (* the config cells are owned outright at this join *)
    iEval (rewrite Hdqc) in "Hstvec".
    iEval (rewrite Hdqc) in "Hmie".
    iEval (rewrite Hdqc) in "Hmdl".
    iEval (rewrite Hdqc) in "Hmenv".
    (* [Hsenv] needs no [Hdqc] rewrite -- [user_cfg]'s senvcfg conjunct is
       already [↦ᵣ□], decoupled from [dqc] entirely (UserExec.v). *)
    (* the pc: stvec's direct base is the trampoline base *)
    assert (Hsb : stvec_base (uc_stvec C) = uva 0x00).
    { rewrite Hstvec. apply bv_eq; vm_compute; reflexivity. }
    (* [pc_is], one resource post-port (worklist 13.2), so ONE rewrite *)
    iEval (rewrite Hsb) in "Hpc".
    (* ============ open usertrap_res for the SAVE walk's own cells ======= *)
    (* the trapframe page AND [sscratch] come out of the residue together:
       the save walk and the sscratch swap overlap, and the residue is
       sealed, so one opener hands out both. *)
    (* ... and with them the KERNEL ROOT the residue's kernel_satp names,
       with its [kpt_inv]: this is the [kroot] the exit switch installs. *)
    iDestruct (usertrap_res_tf_csrs_open pt vksp with "Hures") as (kroot ws0)
      "(#Hkfr & %Hok0 & Htf0 & Hcsrs0 & Hclose0)".
    pose proof Hok0 as Hok0k.
    iDestruct "Hcsrs0" as "(Hssc0 & Hmdlc & Hmsec & Hssec)".
    iDestruct "Hssc0" as (sscr0) "Hsscr".
    iDestruct (tf_page_length with "Htf0") as %Hlen0.
    iDestruct (tf_page_open36 (ud_tfp pt) ws0 Hlen0 with "Htf0") as
      (vksat vksp0 vktr w3 vkhart
       w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160
       w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280)
      "(-> & Hk0 & Hk8 & Hk16 & Hk24 & Hk32 &
        Htf40 & Htf48 & Htf56 & Htf64 & Htf72 & Htf80 & Htf88 & Htf96 & Htf104 & Htf112 &
        Htf120 & Htf128 & Htf136 & Htf144 & Htf152 & Htf160 & Htf168 & Htf176 & Htf184 &
        Htf192 & Htf200 & Htf208 & Htf216 & Htf224 & Htf232 & Htf240 & Htf248 & Htf256 &
        Htf264 & Htf272 & Htf280 & Htail0)".
    cbn in Hok0.
    destruct Hok0 as ((ksat & Heq0 & HkMode & Hkasid & Hkppn) & Heq1 & Heq2 & Heq4).
    apply Some_inj in Heq0, Heq1, Heq2, Heq4.
    subst ksat vksp0.
    set (dqk := DfracOwn 1 : dfrac).
    (* ============ the 44 instruction resources ============ *)
    iPoseProof (uvi_csrw_sscratch with "Hkt") as "Hi_csrw_ss".
    (* ---- csrw sscratch, a0 @ 0x00 ---- *)
    iApply (wp_ucsrw_sscratch_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x00 false (mword_of_int 10) g sscr0
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc Hfile Hi_csrw_ss").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc Hfile".
    iClear "Hi_csrw_ss".
    assert (Hpcx_0x00 : add_vec_int (uva 0x00) (if false then 2 else 4) = uva 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x00) in "Hpc".
    iPoseProof (uvi_lui with "Hkt") as "Hi_lui".
    (* ---- lui a0, 0x2000 @ 0x04 ---- *)
    iApply (wp_ualu_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x04 false ai_lui g
              (mword_of_int 33554432 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_lui").
    { iIntros "#Hcert Hf".
      assert (Hluiv : luival (mword_of_int 0x2000 : mword 20)
                      = (mword_of_int 33554432 : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite -Hluiv.
      change (execute ai_lui)
        with (execute (UTYPE (mword_of_int 0x2000,
                              Regidx (mword_of_int 10 : mword 5), LUI))).
      iApply (swp_execute_pure_w (mword_of_int 10) g
                (execute (UTYPE (mword_of_int 0x2000,
                                 Regidx (mword_of_int 10 : mword 5), LUI)))
                RETIRE_SUCCESS (luival (mword_of_int 0x2000 : mword 20))
                eq_refl ltac:(vm_compute; lia) with "Hcert Hf"). }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile".
    iClear "Hi_lui".
    assert (Hpcx_0x04 : add_vec_int (uva 0x04) (if false then 2 else 4) = uva 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x04) in "Hpc".
    assert (Ha0_addiw : <[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g
                      !!! Regidx (mword_of_int 10)
                    = regval_into_reg (mword_of_int 33554432 : mword 64))
      by (apply upd_eq).
    iPoseProof (uvi_addiw with "Hkt") as "Hi_addiw".
    (* ---- c.addiw a0, -1 @ 0x08 ---- *)
    iApply (wp_ualu_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x08 true ai_addiw (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g)
              (mword_of_int 33554431 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_addiw").
    { iIntros "#Hcert Hf".
      assert (Haddiwv : sign_extend' 64 (subrange_vec_dec
                (add_vec ((<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g) !!! Regidx (mword_of_int 10 : mword 5))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
                31 0) = (mword_of_int 33554431 : mword 64))
        by (rewrite Ha0_addiw; apply bv_eq; vm_compute; reflexivity).
      rewrite -Haddiwv.
      change (execute ai_addiw)
        with (execute (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6),
                              Regidx (mword_of_int 10 : mword 5),
                              Regidx (mword_of_int 10 : mword 5)))).
      iApply (swp_execute_rw2 (mword_of_int 10) (mword_of_int 10) (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g)
                (execute (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6),
                                 Regidx (mword_of_int 10 : mword 5),
                                 Regidx (mword_of_int 10 : mword 5))))
                RETIRE_SUCCESS
                (fun a => sign_extend' 64 (subrange_vec_dec
                   (add_vec a (sign_extend' 64
                      (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
                eq_refl ltac:(vm_compute; lia) with "Hcert Hf"). }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile".
    iClear "Hi_addiw".
    assert (Hpcx_0x08 : add_vec_int (uva 0x08) (if true then 2 else 4) = uva 0x0a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x08) in "Hpc".
    assert (Ha0_slli : <[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g)
                      !!! Regidx (mword_of_int 10)
                    = regval_into_reg (mword_of_int 33554431 : mword 64))
      by (apply upd_eq).
    iPoseProof (uvi_slli with "Hkt") as "Hi_slli".
    (* ---- c.slli a0, 13 @ 0x0a ---- *)
    iApply (wp_ualu_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x0a true ai_slli (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g))
              (mword_of_int TRAPFRAME : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_slli").
    { iIntros "#Hcert Hf".
      assert (Hslliv : shift_bits_left
                ((<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g)) !!! Regidx (mword_of_int 10 : mword 5))
                (subrange_vec_dec (mword_of_int 13 : mword 6)
                   (Z.sub log2_xlen 1) 0)
              = (mword_of_int TRAPFRAME : mword 64))
        by (rewrite Ha0_slli; apply bv_eq; vm_compute; reflexivity).
      rewrite -Hslliv.
      change (execute ai_slli)
        with (execute (SHIFTIOP (mword_of_int 13,
                                 Regidx (mword_of_int 10 : mword 5),
                                 Regidx (mword_of_int 10 : mword 5), SLLI))).
      iApply (swp_execute_rw (mword_of_int 10) (mword_of_int 10) (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g))
                (execute (SHIFTIOP (mword_of_int 13,
                                    Regidx (mword_of_int 10 : mword 5),
                                    Regidx (mword_of_int 10 : mword 5), SLLI)))
                RETIRE_SUCCESS
                (fun a => shift_bits_left a
                   (subrange_vec_dec (mword_of_int 13 : mword 6)
                      (Z.sub log2_xlen 1) 0))
                eq_refl ltac:(vm_compute; lia) with "Hcert Hf"). }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile".
    iClear "Hi_slli".
    assert (Hpcx_0x0a : add_vec_int (uva 0x0a) (if true then 2 else 4) = uva 0x0c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x0a) in "Hpc".
    (* collapse the three a0 writes: a0 = TRAPFRAME *)
    iEval (rewrite upd_upd) in "Hfile".
    iEval (rewrite upd_upd) in "Hfile".
    assert (Hrir : regval_into_reg (mword_of_int TRAPFRAME : mword 64) = (mword_of_int TRAPFRAME : mword 64))
      by reflexivity.
    iEval (rewrite Hrir) in "Hfile".
    set (M2 := <[Regidx (mword_of_int 10) := mword_of_int TRAPFRAME]> g).
    assert (Ha0_2 : M2 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME)
      by (unfold M2; apply upd_eq).
    (* the 30 saved registers are untouched by the [li]: peel a0's insert *)
    assert (Hg1 : M2 !!! Regidx (mword_of_int 1) = (g !!! Regidx (mword_of_int 1) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg2 : M2 !!! Regidx (mword_of_int 2) = (g !!! Regidx (mword_of_int 2) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg3 : M2 !!! Regidx (mword_of_int 3) = (g !!! Regidx (mword_of_int 3) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg4 : M2 !!! Regidx (mword_of_int 4) = (g !!! Regidx (mword_of_int 4) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg5 : M2 !!! Regidx (mword_of_int 5) = (g !!! Regidx (mword_of_int 5) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg6 : M2 !!! Regidx (mword_of_int 6) = (g !!! Regidx (mword_of_int 6) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg7 : M2 !!! Regidx (mword_of_int 7) = (g !!! Regidx (mword_of_int 7) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg8 : M2 !!! Regidx (mword_of_int 8) = (g !!! Regidx (mword_of_int 8) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg9 : M2 !!! Regidx (mword_of_int 9) = (g !!! Regidx (mword_of_int 9) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg11 : M2 !!! Regidx (mword_of_int 11) = (g !!! Regidx (mword_of_int 11) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg12 : M2 !!! Regidx (mword_of_int 12) = (g !!! Regidx (mword_of_int 12) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg13 : M2 !!! Regidx (mword_of_int 13) = (g !!! Regidx (mword_of_int 13) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg14 : M2 !!! Regidx (mword_of_int 14) = (g !!! Regidx (mword_of_int 14) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg15 : M2 !!! Regidx (mword_of_int 15) = (g !!! Regidx (mword_of_int 15) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg16 : M2 !!! Regidx (mword_of_int 16) = (g !!! Regidx (mword_of_int 16) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg17 : M2 !!! Regidx (mword_of_int 17) = (g !!! Regidx (mword_of_int 17) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg18 : M2 !!! Regidx (mword_of_int 18) = (g !!! Regidx (mword_of_int 18) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg19 : M2 !!! Regidx (mword_of_int 19) = (g !!! Regidx (mword_of_int 19) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg20 : M2 !!! Regidx (mword_of_int 20) = (g !!! Regidx (mword_of_int 20) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg21 : M2 !!! Regidx (mword_of_int 21) = (g !!! Regidx (mword_of_int 21) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg22 : M2 !!! Regidx (mword_of_int 22) = (g !!! Regidx (mword_of_int 22) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg23 : M2 !!! Regidx (mword_of_int 23) = (g !!! Regidx (mword_of_int 23) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg24 : M2 !!! Regidx (mword_of_int 24) = (g !!! Regidx (mword_of_int 24) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg25 : M2 !!! Regidx (mword_of_int 25) = (g !!! Regidx (mword_of_int 25) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg26 : M2 !!! Regidx (mword_of_int 26) = (g !!! Regidx (mword_of_int 26) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg27 : M2 !!! Regidx (mword_of_int 27) = (g !!! Regidx (mword_of_int 27) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg28 : M2 !!! Regidx (mword_of_int 28) = (g !!! Regidx (mword_of_int 28) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg29 : M2 !!! Regidx (mword_of_int 29) = (g !!! Regidx (mword_of_int 29) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg30 : M2 !!! Regidx (mword_of_int 30) = (g !!! Regidx (mword_of_int 30) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg31 : M2 !!! Regidx (mword_of_int 31) = (g !!! Regidx (mword_of_int 31) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (uvi_sd_ra with "Hkt") as "Hi_sd_ra".
    (* ---- sd x1, 40(a0) @ 0x0c ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x0c 40 (mword_of_int 1) false M2 (w40 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_ra Htf40").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf40".
    iClear "Hi_sd_ra".
    iEval (rewrite Hg1) in "Htf40".
    assert (Hpcx_0x0c : add_vec_int (uva 0x0c) (if false then 2 else 4) = uva 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x0c) in "Hpc".
    iPoseProof (uvi_sd_sp with "Hkt") as "Hi_sd_sp".
    (* ---- sd x2, 48(a0) @ 0x10 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x10 48 (mword_of_int 2) false M2 (w48 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_sp Htf48").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf48".
    iClear "Hi_sd_sp".
    iEval (rewrite Hg2) in "Htf48".
    assert (Hpcx_0x10 : add_vec_int (uva 0x10) (if false then 2 else 4) = uva 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x10) in "Hpc".
    iPoseProof (uvi_sd_gp with "Hkt") as "Hi_sd_gp".
    (* ---- sd x3, 56(a0) @ 0x14 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x14 56 (mword_of_int 3) false M2 (w56 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_gp Htf56").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf56".
    iClear "Hi_sd_gp".
    iEval (rewrite Hg3) in "Htf56".
    assert (Hpcx_0x14 : add_vec_int (uva 0x14) (if false then 2 else 4) = uva 0x18)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x14) in "Hpc".
    iPoseProof (uvi_sd_tp with "Hkt") as "Hi_sd_tp".
    (* ---- sd x4, 64(a0) @ 0x18 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x18 64 (mword_of_int 4) false M2 (w64 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_tp Htf64").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf64".
    iClear "Hi_sd_tp".
    iEval (rewrite Hg4) in "Htf64".
    assert (Hpcx_0x18 : add_vec_int (uva 0x18) (if false then 2 else 4) = uva 0x1c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x18) in "Hpc".
    iPoseProof (uvi_sd_t0 with "Hkt") as "Hi_sd_t0".
    (* ---- sd x5, 72(a0) @ 0x1c ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x1c 72 (mword_of_int 5) false M2 (w72 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t0 Htf72").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf72".
    iClear "Hi_sd_t0".
    iEval (rewrite Hg5) in "Htf72".
    assert (Hpcx_0x1c : add_vec_int (uva 0x1c) (if false then 2 else 4) = uva 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x1c) in "Hpc".
    iPoseProof (uvi_sd_t1 with "Hkt") as "Hi_sd_t1".
    (* ---- sd x6, 80(a0) @ 0x20 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x20 80 (mword_of_int 6) false M2 (w80 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t1 Htf80").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf80".
    iClear "Hi_sd_t1".
    iEval (rewrite Hg6) in "Htf80".
    assert (Hpcx_0x20 : add_vec_int (uva 0x20) (if false then 2 else 4) = uva 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x20) in "Hpc".
    iPoseProof (uvi_sd_t2 with "Hkt") as "Hi_sd_t2".
    (* ---- sd x7, 88(a0) @ 0x24 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x24 88 (mword_of_int 7) false M2 (w88 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t2 Htf88").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf88".
    iClear "Hi_sd_t2".
    iEval (rewrite Hg7) in "Htf88".
    assert (Hpcx_0x24 : add_vec_int (uva 0x24) (if false then 2 else 4) = uva 0x28)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x24) in "Hpc".
    iPoseProof (uvi_csd_s0 with "Hkt") as "Hi_csd_s0".
    iEval (change (uvai_csd_tgt 0 12) with (uvai_sd 8 96)) in "Hi_csd_s0".
    (* ---- sd x8, 96(a0) @ 0x28 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x28 96 (mword_of_int 8) true M2 (w96 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_s0 Htf96").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf96".
    iClear "Hi_csd_s0".
    iEval (rewrite Hg8) in "Htf96".
    assert (Hpcx_0x28 : add_vec_int (uva 0x28) (if true then 2 else 4) = uva 0x2a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x28) in "Hpc".
    iPoseProof (uvi_csd_s1 with "Hkt") as "Hi_csd_s1".
    iEval (change (uvai_csd_tgt 1 13) with (uvai_sd 9 104)) in "Hi_csd_s1".
    (* ---- sd x9, 104(a0) @ 0x2a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x2a 104 (mword_of_int 9) true M2 (w104 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_s1 Htf104").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf104".
    iClear "Hi_csd_s1".
    iEval (rewrite Hg9) in "Htf104".
    assert (Hpcx_0x2a : add_vec_int (uva 0x2a) (if true then 2 else 4) = uva 0x2c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x2a) in "Hpc".
    iPoseProof (uvi_csd_a1 with "Hkt") as "Hi_csd_a1".
    iEval (change (uvai_csd_tgt 3 15) with (uvai_sd 11 120)) in "Hi_csd_a1".
    (* ---- sd x11, 120(a0) @ 0x2c ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x2c 120 (mword_of_int 11) true M2 (w120 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a1 Htf120").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf120".
    iClear "Hi_csd_a1".
    iEval (rewrite Hg11) in "Htf120".
    assert (Hpcx_0x2c : add_vec_int (uva 0x2c) (if true then 2 else 4) = uva 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x2c) in "Hpc".
    iPoseProof (uvi_csd_a2 with "Hkt") as "Hi_csd_a2".
    iEval (change (uvai_csd_tgt 4 16) with (uvai_sd 12 128)) in "Hi_csd_a2".
    (* ---- sd x12, 128(a0) @ 0x2e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x2e 128 (mword_of_int 12) true M2 (w128 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a2 Htf128").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf128".
    iClear "Hi_csd_a2".
    iEval (rewrite Hg12) in "Htf128".
    assert (Hpcx_0x2e : add_vec_int (uva 0x2e) (if true then 2 else 4) = uva 0x30)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x2e) in "Hpc".
    iPoseProof (uvi_csd_a3 with "Hkt") as "Hi_csd_a3".
    iEval (change (uvai_csd_tgt 5 17) with (uvai_sd 13 136)) in "Hi_csd_a3".
    (* ---- sd x13, 136(a0) @ 0x30 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x30 136 (mword_of_int 13) true M2 (w136 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a3 Htf136").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf136".
    iClear "Hi_csd_a3".
    iEval (rewrite Hg13) in "Htf136".
    assert (Hpcx_0x30 : add_vec_int (uva 0x30) (if true then 2 else 4) = uva 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x30) in "Hpc".
    iPoseProof (uvi_csd_a4 with "Hkt") as "Hi_csd_a4".
    iEval (change (uvai_csd_tgt 6 18) with (uvai_sd 14 144)) in "Hi_csd_a4".
    (* ---- sd x14, 144(a0) @ 0x32 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x32 144 (mword_of_int 14) true M2 (w144 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a4 Htf144").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf144".
    iClear "Hi_csd_a4".
    iEval (rewrite Hg14) in "Htf144".
    assert (Hpcx_0x32 : add_vec_int (uva 0x32) (if true then 2 else 4) = uva 0x34)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x32) in "Hpc".
    iPoseProof (uvi_csd_a5 with "Hkt") as "Hi_csd_a5".
    iEval (change (uvai_csd_tgt 7 19) with (uvai_sd 15 152)) in "Hi_csd_a5".
    (* ---- sd x15, 152(a0) @ 0x34 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x34 152 (mword_of_int 15) true M2 (w152 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a5 Htf152").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf152".
    iClear "Hi_csd_a5".
    iEval (rewrite Hg15) in "Htf152".
    assert (Hpcx_0x34 : add_vec_int (uva 0x34) (if true then 2 else 4) = uva 0x36)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x34) in "Hpc".
    iPoseProof (uvi_sd_a6 with "Hkt") as "Hi_sd_a6".
    (* ---- sd x16, 160(a0) @ 0x36 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x36 160 (mword_of_int 16) false M2 (w160 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_a6 Htf160").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf160".
    iClear "Hi_sd_a6".
    iEval (rewrite Hg16) in "Htf160".
    assert (Hpcx_0x36 : add_vec_int (uva 0x36) (if false then 2 else 4) = uva 0x3a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x36) in "Hpc".
    iPoseProof (uvi_sd_a7 with "Hkt") as "Hi_sd_a7".
    (* ---- sd x17, 168(a0) @ 0x3a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x3a 168 (mword_of_int 17) false M2 (w168 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_a7 Htf168").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf168".
    iClear "Hi_sd_a7".
    iEval (rewrite Hg17) in "Htf168".
    assert (Hpcx_0x3a : add_vec_int (uva 0x3a) (if false then 2 else 4) = uva 0x3e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x3a) in "Hpc".
    iPoseProof (uvi_sd_s2 with "Hkt") as "Hi_sd_s2".
    (* ---- sd x18, 176(a0) @ 0x3e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x3e 176 (mword_of_int 18) false M2 (w176 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s2 Htf176").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf176".
    iClear "Hi_sd_s2".
    iEval (rewrite Hg18) in "Htf176".
    assert (Hpcx_0x3e : add_vec_int (uva 0x3e) (if false then 2 else 4) = uva 0x42)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x3e) in "Hpc".
    iPoseProof (uvi_sd_s3 with "Hkt") as "Hi_sd_s3".
    (* ---- sd x19, 184(a0) @ 0x42 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x42 184 (mword_of_int 19) false M2 (w184 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s3 Htf184").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf184".
    iClear "Hi_sd_s3".
    iEval (rewrite Hg19) in "Htf184".
    assert (Hpcx_0x42 : add_vec_int (uva 0x42) (if false then 2 else 4) = uva 0x46)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x42) in "Hpc".
    iPoseProof (uvi_sd_s4 with "Hkt") as "Hi_sd_s4".
    (* ---- sd x20, 192(a0) @ 0x46 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x46 192 (mword_of_int 20) false M2 (w192 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s4 Htf192").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf192".
    iClear "Hi_sd_s4".
    iEval (rewrite Hg20) in "Htf192".
    assert (Hpcx_0x46 : add_vec_int (uva 0x46) (if false then 2 else 4) = uva 0x4a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x46) in "Hpc".
    iPoseProof (uvi_sd_s5 with "Hkt") as "Hi_sd_s5".
    (* ---- sd x21, 200(a0) @ 0x4a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x4a 200 (mword_of_int 21) false M2 (w200 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s5 Htf200").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf200".
    iClear "Hi_sd_s5".
    iEval (rewrite Hg21) in "Htf200".
    assert (Hpcx_0x4a : add_vec_int (uva 0x4a) (if false then 2 else 4) = uva 0x4e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x4a) in "Hpc".
    iPoseProof (uvi_sd_s6 with "Hkt") as "Hi_sd_s6".
    (* ---- sd x22, 208(a0) @ 0x4e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x4e 208 (mword_of_int 22) false M2 (w208 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s6 Htf208").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf208".
    iClear "Hi_sd_s6".
    iEval (rewrite Hg22) in "Htf208".
    assert (Hpcx_0x4e : add_vec_int (uva 0x4e) (if false then 2 else 4) = uva 0x52)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x4e) in "Hpc".
    iPoseProof (uvi_sd_s7 with "Hkt") as "Hi_sd_s7".
    (* ---- sd x23, 216(a0) @ 0x52 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x52 216 (mword_of_int 23) false M2 (w216 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s7 Htf216").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf216".
    iClear "Hi_sd_s7".
    iEval (rewrite Hg23) in "Htf216".
    assert (Hpcx_0x52 : add_vec_int (uva 0x52) (if false then 2 else 4) = uva 0x56)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x52) in "Hpc".
    iPoseProof (uvi_sd_s8 with "Hkt") as "Hi_sd_s8".
    (* ---- sd x24, 224(a0) @ 0x56 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x56 224 (mword_of_int 24) false M2 (w224 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s8 Htf224").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf224".
    iClear "Hi_sd_s8".
    iEval (rewrite Hg24) in "Htf224".
    assert (Hpcx_0x56 : add_vec_int (uva 0x56) (if false then 2 else 4) = uva 0x5a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x56) in "Hpc".
    iPoseProof (uvi_sd_s9 with "Hkt") as "Hi_sd_s9".
    (* ---- sd x25, 232(a0) @ 0x5a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x5a 232 (mword_of_int 25) false M2 (w232 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s9 Htf232").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf232".
    iClear "Hi_sd_s9".
    iEval (rewrite Hg25) in "Htf232".
    assert (Hpcx_0x5a : add_vec_int (uva 0x5a) (if false then 2 else 4) = uva 0x5e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x5a) in "Hpc".
    iPoseProof (uvi_sd_s10 with "Hkt") as "Hi_sd_s10".
    (* ---- sd x26, 240(a0) @ 0x5e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x5e 240 (mword_of_int 26) false M2 (w240 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s10 Htf240").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf240".
    iClear "Hi_sd_s10".
    iEval (rewrite Hg26) in "Htf240".
    assert (Hpcx_0x5e : add_vec_int (uva 0x5e) (if false then 2 else 4) = uva 0x62)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x5e) in "Hpc".
    iPoseProof (uvi_sd_s11 with "Hkt") as "Hi_sd_s11".
    (* ---- sd x27, 248(a0) @ 0x62 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x62 248 (mword_of_int 27) false M2 (w248 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s11 Htf248").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf248".
    iClear "Hi_sd_s11".
    iEval (rewrite Hg27) in "Htf248".
    assert (Hpcx_0x62 : add_vec_int (uva 0x62) (if false then 2 else 4) = uva 0x66)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x62) in "Hpc".
    iPoseProof (uvi_sd_t3 with "Hkt") as "Hi_sd_t3".
    (* ---- sd x28, 256(a0) @ 0x66 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x66 256 (mword_of_int 28) false M2 (w256 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t3 Htf256").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf256".
    iClear "Hi_sd_t3".
    iEval (rewrite Hg28) in "Htf256".
    assert (Hpcx_0x66 : add_vec_int (uva 0x66) (if false then 2 else 4) = uva 0x6a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x66) in "Hpc".
    iPoseProof (uvi_sd_t4 with "Hkt") as "Hi_sd_t4".
    (* ---- sd x29, 264(a0) @ 0x6a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x6a 264 (mword_of_int 29) false M2 (w264 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t4 Htf264").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf264".
    iClear "Hi_sd_t4".
    iEval (rewrite Hg29) in "Htf264".
    assert (Hpcx_0x6a : add_vec_int (uva 0x6a) (if false then 2 else 4) = uva 0x6e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x6a) in "Hpc".
    iPoseProof (uvi_sd_t5 with "Hkt") as "Hi_sd_t5".
    (* ---- sd x30, 272(a0) @ 0x6e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x6e 272 (mword_of_int 30) false M2 (w272 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t5 Htf272").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf272".
    iClear "Hi_sd_t5".
    iEval (rewrite Hg30) in "Htf272".
    assert (Hpcx_0x6e : add_vec_int (uva 0x6e) (if false then 2 else 4) = uva 0x72)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x6e) in "Hpc".
    iPoseProof (uvi_sd_t6 with "Hkt") as "Hi_sd_t6".
    (* ---- sd x31, 280(a0) @ 0x72 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x72 280 (mword_of_int 31) false M2 (w280 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t6 Htf280").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf280".
    iClear "Hi_sd_t6".
    iEval (rewrite Hg31) in "Htf280".
    assert (Hpcx_0x72 : add_vec_int (uva 0x72) (if false then 2 else 4) = uva 0x76)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x72) in "Hpc".
    iPoseProof (uvi_csrr_sscratch with "Hkt") as "Hi_csrr_ss".
    (* ---- csrr t0, sscratch @ 0x76 ---- *)
    iApply (wp_ucsrr_sscratch_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x76 false (mword_of_int 5) M2
              (g !!! Regidx (mword_of_int 10) : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              ltac:(vm_compute; lia)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc Hfile Hi_csrr_ss").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc Hfile".
    iClear "Hi_csrr_ss".
    assert (Hpcx_0x76 : add_vec_int (uva 0x76) (if false then 2 else 4) = uva 0x7a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x76) in "Hpc".
    set (M3 := <[Regidx (mword_of_int 5) := regval_into_reg (g !!! Regidx (mword_of_int 10) : mword 64)]> M2).
    assert (Ha0_3 : M3 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M3. rewrite upd_ne; [exact Ha0_2 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg112 : M3 !!! Regidx (mword_of_int 5) = (g !!! Regidx (mword_of_int 10) : mword 64)).
    { unfold M3. rewrite upd_eq. reflexivity. }
    iPoseProof (uvi_sd_a0 with "Hkt") as "Hi_sd_a0".
    (* ---- sd t0, 112(a0) @ 0x7a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x7a 112 (mword_of_int 5) false M3 (w112 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_3
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_a0 Htf112").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf112".
    iClear "Hi_sd_a0".
    iEval (rewrite Hg112) in "Htf112".
    assert (Hpcx_0x7a : add_vec_int (uva 0x7a) (if false then 2 else 4) = uva 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x7a) in "Hpc".
    iPoseProof (uvi_ld_sp with "Hkt") as "Hi_ld_sp".
    (* ---- ld x2, 8(a0) @ 0x7e ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x7e 8 (mword_of_int 2) false M3 vksp
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              ltac:(vm_compute; lia)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_3
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_sp Hk8").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk8".
    iClear "Hi_ld_sp".
    assert (Hpcx_0x7e : add_vec_int (uva 0x7e) (if false then 2 else 4) = uva 0x82)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x7e) in "Hpc".
    set (M4 := <[Regidx (mword_of_int 2) := regval_into_reg vksp]> M3).
    assert (Ha0_4 : M4 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M4. rewrite upd_ne; [exact Ha0_3 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (uvi_ld_tp with "Hkt") as "Hi_ld_tp".
    (* ---- ld x4, 32(a0) @ 0x82 ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x82 32 (mword_of_int 4) false M4 vkhart
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              ltac:(vm_compute; lia)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_4
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_tp Hk32").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk32".
    iClear "Hi_ld_tp".
    assert (Hpcx_0x82 : add_vec_int (uva 0x82) (if false then 2 else 4) = uva 0x86)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x82) in "Hpc".
    set (M5 := <[Regidx (mword_of_int 4) := regval_into_reg vkhart]> M4).
    assert (Ha0_5 : M5 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M5. rewrite upd_ne; [exact Ha0_4 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (uvi_ld_t0 with "Hkt") as "Hi_ld_t0".
    (* ---- ld x5, 16(a0) @ 0x86 ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x86 16 (mword_of_int 5) false M5 vktr
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              ltac:(vm_compute; lia)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_5
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_t0 Hk16").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk16".
    iClear "Hi_ld_t0".
    assert (Hpcx_0x86 : add_vec_int (uva 0x86) (if false then 2 else 4) = uva 0x8a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x86) in "Hpc".
    set (M6 := <[Regidx (mword_of_int 5) := regval_into_reg vktr]> M5).
    assert (Ha0_6 : M6 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M6. rewrite upd_ne; [exact Ha0_5 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (uvi_ld_t1 with "Hkt") as "Hi_ld_t1".
    (* ---- ld x6, 0(a0) @ 0x8a ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) 0x8a 0 (mword_of_int 6) false M6 vksat
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              ltac:(vm_compute; lia)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_6
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_t1 Hk0").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk0".
    iClear "Hi_ld_t1".
    assert (Hpcx_0x8a : add_vec_int (uva 0x8a) (if false then 2 else 4) = uva 0x8e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x8a) in "Hpc".
    set (M7 := <[Regidx (mword_of_int 6) := regval_into_reg vksat]> M6).
    (* ---- the exit switch: sfence / csrw satp,t1 / sfence / c.jalr t0 ---- *)
    assert (Ht1v : M7 !!! Regidx (mword_of_int 6) = (vksat : mword 64)).
    { unfold M7. rewrite upd_eq. reflexivity. }
    assert (Ht0v : M7 !!! Regidx (mword_of_int 5) = (vktr : mword 64)).
    { unfold M7. rewrite upd_ne.
      - unfold M6. rewrite upd_eq. reflexivity.
      - intro He. injection He as He2. vm_compute in He2. congruence. }
    iDestruct (uv_utlb_map_wf with "Hutlb") as %Hwfu.
    iPoseProof (uvi_sfence1 with "Hkt") as "Hi_sf1".
    iPoseProof (uvi_csrw_satp with "Hkt") as "Hi_csrw_satp".
    iPoseProof (uvi_sfence2 with "Hkt") as "Hi_sf2".
    iPoseProof (uvi_cjalr_t0 with "Hkt") as "Hi_cjalr".
    iApply (wp_uservec_exit_pt kroot (ud_root pt) (ud_tfp pt) (ud_um pt) M7
              (vksat : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              HSIE HMPRV HSXL HTVM Hmm HPBMTE Hmenvval0 Hwfu Ht1v HkMode Hkasid Hkppn
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hclaim Hutlb Hkfr Hpc Hfile
                    Hi_sf1 Hi_csrw_satp Hi_sf2 Hi_cjalr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hufr Hkres Hpc Hfile".
    iClear "Hi_sf1".
    iClear "Hi_csrw_satp".
    iClear "Hi_sf2".
    iClear "Hi_cjalr".
    (* ============ derive the usertrap call's own premises ============= *)
    iEval (rewrite Ht0v Heq2) in "Hpc".
    assert (Hpcu : ret_pc (mword_of_int KernelSyms.usertrap : mword 64) = mword_of_int KernelSyms.usertrap)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcu) in "Hpc".
    pose proof (usertrap_entry_ms_of_trap ms_v Hok) as Hums.
    assert (Hspv : M7 !!! Regidx (mword_of_int 2) = (vksp : mword 64)).
    { unfold M7. rewrite upd_ne; [| intro He; injection He as He2; vm_compute in He2; congruence].
      unfold M6. rewrite upd_ne; [| intro He; injection He as He2; vm_compute in He2; congruence].
      unfold M5. rewrite upd_ne; [| intro He; injection He as He2; vm_compute in He2; congruence].
      unfold M4. rewrite upd_eq. reflexivity. }
    assert (Htpv0 : M7 !!! Regidx (mword_of_int 4) = (vkhart : mword 64)).
    { unfold M7. rewrite upd_ne; [| intro He; injection He as He2; vm_compute in He2; congruence].
      unfold M6. rewrite upd_ne; [| intro He; injection He as He2; vm_compute in He2; congruence].
      unfold M5. rewrite upd_eq. reflexivity. }
    assert (Htpv : M7 !!! Regidx (mword_of_int 4) = cid_word) by (rewrite Htpv0 Heq4; reflexivity).
    (* the [ra := uva 0x9c] insert (the exit switch's own jalr-link write)
       does not touch sp/tp *)
    assert (Hspv' : (<[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]> M7)
                      !!! Regidx (mword_of_int 2) = (vksp : mword 64)).
    { rewrite upd_ne; [exact Hspv | intro He; injection He as He2; vm_compute in He2; congruence]. }
    assert (Htpv' : (<[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]> M7)
                      !!! Regidx (mword_of_int 4) = cid_word).
    { rewrite upd_ne; [exact Htpv | intro He; injection He as He2; vm_compute in He2; congruence]. }
    (* ============ reseal usertrap_res, then call usertrap =============== *)
    iDestruct (tf_page_close36 (ud_tfp pt) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 with "Hk0 Hk8 Hk16 Hk24 Hk32
                       Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf112
                       Htf120 Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184
                       Htf192 Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256
                       Htf264 Htf272 Htf280 Htail0") as "Htf0'".
    (* hand the page and the CSRs back before the residue goes to usertrap *)
    iAssert hart_csrs with "[Hsscr Hmdlc Hmsec Hssec]" as "Hcsrs0'".
    { iFrame "Hmdlc Hmsec Hssec". iExists _. iExact "Hsscr". }
    iDestruct ("Hclose0" with "[%] Htf0' Hcsrs0'") as "Hures'".
    { refine (tf_kernel_words_ok_tail _ _ _ _ _ _ _ _ _ Hok0k). }
    (* ---- THE ADDRESS SPACE CHANGES VIEW, then the two borrows close ----
       The exit switch just did the one thing that converts the views: it
       wrote the KERNEL root into satp, which turned the user table from the
       installed [utlb_inv_pt] into the parked [Hufr : pt_frame ...] and
       produced [Hkres : tlb_res_pt kroot] for the kernel one.  The user
       PAGES did not move at all -- [Hdata] is the same resource the kernel
       tier calls [proc_pt_own], page-indexed rather than keyed by user
       virtual address ([ProcPtOwn.proc_pt_own_umem]), which is why this
       costs a rewrite and not a conversion.
         So the whole user address space is now in the kernel's hands in the
       kernel's shape, and [proc_pt] is exactly the two of them: that is
       what the BARE residue is missing, and what makes it the residue that
       could park across user execution in the first place. *)
    assert (Hmwf0 : upt_map_wf (ud_um pt)) by (destruct Hptwf as (H1 & _); exact H1).
    assert (Hinj0 : um_inj (ud_um pt))
      by (destruct Hptwf as (_ & _ & _ & H4 & _); exact H4).
    iEval (rewrite -(proc_pt_own_umem pt Hmwf0 Hinj0)) in "Hdata".
    iAssert (proc_pt pt) with "[Hufr Hdata]" as "Hpt".
    { rewrite proc_pt_split. iFrame "Hdata". iSplitR; [iPureIntro; exact Hptwf|].
      iExact "Hufr". }
    iDestruct (usertrap_res_pt_close pt vksp with "Hures' Hpt") as "Hures'".
    (* THE TRANSLATION SLOT, INJECTED.  [Hkres] is the [tlb_res_pt kroot]
       the exit switch just produced by writing the kernel root into satp --
       and it is exactly the piece the PARKED residue is missing.  usertrap
       runs on the completed form (its own [ut_trap_open] pulls satp back
       out of it), which is why this is a close and not a frame: framing
       [Hkres] across the call would leave usertrap's own [sie_cap_gpr]
       without a translation slot on one side and double-own satp on the
       other. *)
    iDestruct (usertrap_res_tlb_close pt vksp kroot with "Hures' Hkres") as "Hures'".
    iEval (rewrite Hstvec) in "Hstvec".
    iApply (UT.wp_usertrap pt j (<[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]> M7)
              ms_v sc_v stval_v sepc_v vksp (uc_mie C) (uc_mideleg C) MENVCFG_S
              Hums Hjlt Hspv' Htpv' Hmie Hmm Hmenvval0
              with "Hkt Hpc Hhw Hinv Hhs Hpriv Hms Hsc Hstval Hsepc Hstvec Hmie Hmdl Hmenv Hfile Hures'").
    iApply wp_next_intro. iIntros (CID2).
    iEval (rewrite /usertrap_post).
    iIntros (pt' mf ms' usatp uepc sc' stval' mdv0)
      "%Hmask %Hpttf %Haccwf %Hmapwf %Hretms %Hsconf2 %Hcalleesaved %Htpcid %Ha0usatp %Hsatprooted
       Hhs2 Hpriv2 Hms2 Hsc2 Hstval2 Hsepc2 Hstvec2 Hpc2 Hfile2 Hmie3 Hmdl3 Hmenv3 #Hhw2 #Hmin2 Hures2".
    (* ============ open usertrap_res A SECOND TIME, for userret ========== *)
    (* userret's entry switch is about to install the USER table, so both
       borrows come back out, in the mirror order to the entry side: first
       the kernel table out of the translation slot, then the whole user
       address space out of the residue.
         THE TABLE USERRET INSTALLS IS pt', NOT pt.  usertrap may have
       replaced the address space wholesale (exec does), so the frame the
       entry switch parked is stale by now and is NOT what goes back in --
       it went into the residue before the call, and what comes out here is
       whatever usertrap left there.  That is the whole reason the residue
       carries the address space across the kernel excursion instead of
       uservec framing it. *)
    iDestruct (UT.usertrap_res_tlb_open (CID:=CID2) pt' vksp with "Hures2")
      as (kroot2) "[Hkres2 Hures2]".
    iDestruct (UT.usertrap_res_pt_open (CID:=CID2) pt' vksp with "Hures2")
      as "[Hpt' Hures2]".
    iEval (rewrite proc_pt_split) in "Hpt'".
    iDestruct "Hpt'" as "[(%Hptwf' & Hufr') Hdata']".
    iDestruct (UT.usertrap_res_tf_open (CID:=CID2) pt' vksp with "Hures2") as (kroot1 ws1)
      "(#Hinv1 & %Hok1 & Htf1 & Hclose1)".
    iDestruct (tf_page_length with "Htf1") as %Hlen1.
    iDestruct (tf_page_open36 (ud_tfp pt') ws1 Hlen1 with "Htf1") as
      (u0 u1 u2 u3 u4
       u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 u152 u160
       u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280)
      "(-> & Hu0 & Hu8 & Hu16 & Hu24 & Hu32 &
        Hutf40 & Hutf48 & Hutf56 & Hutf64 & Hutf72 & Hutf80 & Hutf88 & Hutf96 & Hutf104 & Hutf112 &
        Hutf120 & Hutf128 & Hutf136 & Hutf144 & Hutf152 & Hutf160 & Hutf168 & Hutf176 & Hutf184 &
        Hutf192 & Hutf200 & Hutf208 & Hutf216 & Hutf224 & Hutf232 & Hutf240 & Hutf248 & Hutf256 &
        Hutf264 & Hutf272 & Hutf280 & Htail1)".
    destruct Hsatprooted as (HuMode & Huasid & Huppn).
    pose proof Hretms as Hretms_keep.
    destruct Hretms as (HSIE2 & HMPRV2 & HSXL2 & HTVM2 & HMXR2 & HTSR2 & HFS2 & HVS2 & Hsretnp2 & _).
    iEval (rewrite Hmie) in "Hmie3".
    assert (Hra9c : (<[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]> M7)
                      !!! Regidx (mword_of_int 1) = uva 0x9c) by (rewrite upd_eq; reflexivity).
    assert (Hpc9c : ret_pc (uva 0x9c) = uva 0x9c) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hra9c Hpc9c) in "Hpc2".
    (* ============ call userret ============ *)
    rewrite Hmie in Hmask.
    (* [senvcfg]'s persistent fact, AT THE RESUMING HART -- [Hhw2] is
       [usertrap_post]'s own copy of [hw_config], which now carries senvcfg
       as one of its conjuncts (RiscvFetchExec.v). [Hwup]'s own senvcfg
       premise wants exactly this persistent form, not the stale entry-hart
       [Hsenv] the walk's own frame still holds (a full-ownership fact at
       the WRONG hart once usertrap migrates -- the earlier "Hsenv" plan
       this comment used to describe). A [iPoseProof] copy keeps [Hhw2]
       itself intact, whole, for [Hwup]'s own [hw_config] premise below. *)
    iPoseProof (hw_config_senvcfg with "Hhw2") as "#Hsenv2".
    iPoseProof (UR.wp_userret_pt kroot2 (ud_root pt') (ud_tfp pt') (ud_um pt') mf usatp
              ms' MIE_S mdv0 MENVCFG_S (mword_of_int 0 : mword 64) uepc
              (* THE a0 SLOT (offset 112) IS LAST, not tenth: [wp_userret_pt]
                 orders its 31 words the way the RESTORE WALK writes them,
                 and a0 is written last (it is the register the walk uses as
                 the trapframe base until then).  Every list below -- the
                 wand arguments, the returned cells, and [userret_gpr]'s own
                 arguments -- follows that order, NOT the numeric one; only
                 [tf_page_close36], which is this file's own lemma, is
                 numeric. *)
              u40 u48 u56 u64 u72 u80 u88 u96 u104 u120 u128 u136 u144 u152 u160
              u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280
              u112
              (DfracOwn 1)
              HSIE2 HMPRV2 HSXL2 HTVM2 HMXR2 Hmask Hpmm HPBMTE eq_refl eq_refl
              Hmapwf HTSR2 Hsretnp2 Ha0usatp HuMode Huasid Huppn) as "Hwup".
    (* [Hhw2]/[Hmin2]: THE RESUMING HART'S OWN copies, handed back by
       [usertrap_post] -- NOT the section's original [Hhw]/[Hinv], which
       name the ENTRY hart's resources and are a different (if
       identically-printed) proposition whenever usertrap crossed harts.
       See [SpecUsertrap.usertrap_post]'s comment. *)
    iApply ("Hwup" with "Hkt Hhw2 Hmin2 Hhs2 Hpriv2 Hms2 Hmie3 Hmdl3 Hmenv3 Hsenv2 Hsepc2 Hclaim Hkres2 Hufr' Hpc2 Hfile2
                    Hutf40 Hutf48 Hutf56 Hutf64 Hutf72 Hutf80 Hutf88 Hutf96 Hutf104
                    Hutf120 Hutf128 Hutf136 Hutf144 Hutf152 Hutf160 Hutf168 Hutf176 Hutf184
                    Hutf192 Hutf200 Hutf208 Hutf216 Hutf224 Hutf232 Hutf240 Hutf248 Hutf256
                    Hutf264 Hutf272 Hutf280 Hutf112").
    iIntros "Hhs3 Hpriv3 Hms3 Hmie4 Hmdl4 Hmenv4 Hsenv3 Hsepc3 Hutlb3 Hpc3 Hfile3
             Hutf40' Hutf48' Hutf56' Hutf64' Hutf72' Hutf80' Hutf88' Hutf96' Hutf104'
             Hutf120' Hutf128' Hutf136' Hutf144' Hutf152' Hutf160' Hutf168' Hutf176' Hutf184'
             Hutf192' Hutf200' Hutf208' Hutf216' Hutf224' Hutf232' Hutf240' Hutf248' Hutf256'
             Hutf264' Hutf272' Hutf280' Hutf112'".
    (* ============ reseal usertrap_res A SECOND TIME, discharge uservec_post *)
    iDestruct (tf_page_close36 (ud_tfp pt') u0 u1 u2 u3 u4
                 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 u152 u160
                 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280
                 with "Hu0 Hu8 Hu16 Hu24 Hu32
                       Hutf40' Hutf48' Hutf56' Hutf64' Hutf72' Hutf80' Hutf88' Hutf96' Hutf104' Hutf112'
                       Hutf120' Hutf128' Hutf136' Hutf144' Hutf152' Hutf160' Hutf168' Hutf176' Hutf184'
                       Hutf192' Hutf200' Hutf208' Hutf216' Hutf224' Hutf232' Hutf240' Hutf248' Hutf256'
                       Hutf264' Hutf272' Hutf280' Htail1") as "Htf1'".
    iDestruct ("Hclose1" with "[%] Htf1'") as "Hures3".
    { refine (tf_kernel_words_ok_tail _ _ _ _ _ _ _ _ _ Hok1). }
    (* ---- THE ADDRESS SPACE CHANGES VIEW BACK -------------------------
       userret's entry switch installed the user root, so [Hutlb3] is the
       tree live again; the pages ([Hdata'], still page-indexed since the
       open) rejoin it, and the pair IS [user_pt_inv].  The descriptor comes
       out RENORMALISED: [user_pt_inv] is the only reader of [ud_data], and
       at the derived footprint its coverage side condition holds by
       construction ([ProcPtOwn.ud_pas_cov]) -- which is the fact
       SpecUsertrap.v explains usertrap itself could never have supplied.
       The residue is re-keyed to match ([usertrap_res_bare_norm]); it reads
       the descriptor only through the three real fields, so that is free.
         After this the post holds the user address space EXACTLY ONCE, in
       the user's view, beside a residue that holds none of it. *)
    iDestruct (user_pt_inv_close pt' Hptwf' with "Hutlb3 Hdata'") as "Hupt3".
    iDestruct (UT.usertrap_res_bare_norm (CID:=CID2) pt' vksp with "Hures3") as "Hures3".
    (* THE CONTINUATION LANDS AT THE RESUMING HART.  [Hcont] is a [wp_next]
       over the hart usertrap came back on; at a real proc the pinning
       condition is refutable ([proc_addr j <> zero_reg] from [Hjlt]), so it
       specialises to [CID2] -- which is the hart every resource below this
       point lives at.  Specialising it to the SECTION's [CID] instead type-
       checks nowhere useful and fails with an [iSpecialize] whose two sides
       print identically. *)
    iSpecialize ("Hcont" $! CID2 with "[%]").
    { intros [Hf | Hz]; [discriminate Hf |].
      exfalso. exact (proc_addr_nonzero j Hjlt Hz). }
    iEval (rewrite /uservec_post) in "Hcont".
    iApply ("Hcont" $! (ud_norm pt') (userret_gpr mf u40 u48 u56 u64 u72 u80 u88 u96 u104 u120 u128
                              u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232
                              u240 u248 u256 u264 u272 u280 u112)
             ms' usatp uepc sc' stval' mdv0
             with "[%] [%] [%] [%] [%] [%] [%] [%] Hhs3 Hpriv3 Hms3 Hmie4 Hmdl4 Hmenv4 Hstvec2 Hsenv3 Hsc2 Hstval2 Hsepc3
                    Hupt3 Hpc3 Hfile3 Hures3 Hhw2 Hmin2").
    - exact Hpttf.
    - exact Hmapwf.
    - split; [| split]; [exact HuMode | exact Huasid | exact Huppn].
    - exact (ud_norm_pas pt').
    - exact Hptwf'.
    - exact Hmask.
    - exact Hretms_keep.
    - exact Haccwf.
  Qed.

End UservecAllPt.
End UservecProof.
