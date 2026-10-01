(* WpSwtchVc.v -- a whole-function WP for xv6's swtch(), via a small S-mode
   VCgen tailored to its instruction shapes.

   swtch (kernel/swtch.S) is a purely straight-line context switch:

       swtch:                          # a0 = old, a1 = new
         sd ra,0(a0)  ...  sd s11,104(a0)   # save 14 callee regs into *old
         ld ra,0(a1)  ...  ld s11,104(a1)   # load 14 callee regs from *new
         ret                                # jump to new->ra

   Two of the fourteen slots (s0,s1) compress to c.sd/c.ld (their registers and
   a0/a1 sit in x8..x15); the other twelve are full 4-byte sd/ld; the final
   [ret] is a c.ret (= jalr x0,0(x1)).  So the body is 28 general-base 8-byte
   loads/stores followed by a c.ret.

   The existing S-mode VCgen (VcGenS.v) only covers RVC value shapes and
   sp-relative 8-byte access; swtch needs general-base 8-byte sd/ld (both
   widths).  Rather than perturb [wp_vc_block_s_den] (used by mycpu/pop_off/
   kernelvec), this file grows a SELF-CONTAINED sibling VCgen -- reusing the
   shared symbolic machinery of VcGen.v (vstate / sval / vheap_own /
   vregs_den) -- whose two-constructor alphabet [swop] targets exactly the four
   leaf WPs of WpFreelistMem.v (wp_{sd,ld,csd,cld}_s_ram).

   [valid_context c] packages "the register set saved in the struct context at
   [c] admits a WP to run"; [wp_swtch] uses it to give swtch the natural
   context-switch spec: precondition [valid_context new]; the machine ends up
   running new's saved WP, handed [valid_context old] as its postcondition. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import KernelText.
Require Import VcGen VcGenS.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From transfinite.base_logic.lib Require Import invariants ghost_var.
Require Import SwtchCtx.
Require Import CodeSwtch.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* 1. Instruction DECODE facts for swtch's 29 instructions.                *)
(*    Base sd/ld: [swb_<word>]; compressed c.sd/c.ld: [swdc_<word>] +      *)
(*    clean ExecuteAs expansions [swx_<name>].  c.ret reuses podec/JR.     *)
(* ====================================================================== *)







(* ====================================================================== *)
(* 2. swtch's straight-line body as a program in the S-mode VCgen alphabet  *)
(*    [vop_s] (merged into VcGenS.v): 28 general-base 8-byte stores/loads    *)
(*    (VSsd/VSld).  Register indices: ra=1 sp=2 s0=8 s1=9 s2..s11=18..27,     *)
(*    a0=10 (old) a1=11 (new).                                              *)
(* ====================================================================== *)
Definition swtch_prog : list vop_s :=
  [ VSsd false (mword_of_int 0)   (mword_of_int 1)  (mword_of_int 10);
    VSsd false (mword_of_int 8)   (mword_of_int 2)  (mword_of_int 10);
    VSsd true  (mword_of_int 16)  (mword_of_int 8)  (mword_of_int 10);
    VSsd true  (mword_of_int 24)  (mword_of_int 9)  (mword_of_int 10);
    VSsd false (mword_of_int 32)  (mword_of_int 18) (mword_of_int 10);
    VSsd false (mword_of_int 40)  (mword_of_int 19) (mword_of_int 10);
    VSsd false (mword_of_int 48)  (mword_of_int 20) (mword_of_int 10);
    VSsd false (mword_of_int 56)  (mword_of_int 21) (mword_of_int 10);
    VSsd false (mword_of_int 64)  (mword_of_int 22) (mword_of_int 10);
    VSsd false (mword_of_int 72)  (mword_of_int 23) (mword_of_int 10);
    VSsd false (mword_of_int 80)  (mword_of_int 24) (mword_of_int 10);
    VSsd false (mword_of_int 88)  (mword_of_int 25) (mword_of_int 10);
    VSsd false (mword_of_int 96)  (mword_of_int 26) (mword_of_int 10);
    VSsd false (mword_of_int 104) (mword_of_int 27) (mword_of_int 10);
    VSld false (mword_of_int 0)   (mword_of_int 11) (mword_of_int 1);
    VSld false (mword_of_int 8)   (mword_of_int 11) (mword_of_int 2);
    VSld true  (mword_of_int 16)  (mword_of_int 11) (mword_of_int 8);
    VSld true  (mword_of_int 24)  (mword_of_int 11) (mword_of_int 9);
    VSld false (mword_of_int 32)  (mword_of_int 11) (mword_of_int 18);
    VSld false (mword_of_int 40)  (mword_of_int 11) (mword_of_int 19);
    VSld false (mword_of_int 48)  (mword_of_int 11) (mword_of_int 20);
    VSld false (mword_of_int 56)  (mword_of_int 11) (mword_of_int 21);
    VSld false (mword_of_int 64)  (mword_of_int 11) (mword_of_int 22);
    VSld false (mword_of_int 72)  (mword_of_int 11) (mword_of_int 23);
    VSld false (mword_of_int 80)  (mword_of_int 11) (mword_of_int 24);
    VSld false (mword_of_int 88)  (mword_of_int 11) (mword_of_int 25);
    VSld false (mword_of_int 96)  (mword_of_int 11) (mword_of_int 26);
    VSld false (mword_of_int 104) (mword_of_int 11) (mword_of_int 27) ].

(* struct-context field layout: field i (0..13) holds register [ctx_regs !! i]
   at byte offset 8*i -- ra sp s0 s1 s2 .. s11 ([ctx_regs] in SwtchCtx.v). *)
Definition ctx_regs_nat : list nat :=
  [ 1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27 ]%nat.

(* a struct-context-shaped segment of the symbolic 8-byte heap: base register
   [breg], one cell per value-register index in [ws], at offsets off, off+8,.... *)
Fixpoint seg_cells (breg : nat) (off : Z) (ws : list nat) : list (sval * sval) :=
  match ws with
  | [] => []
  | w :: rest => (SX breg off, SX w 0) :: seg_cells breg (off + 8) rest
  end.

(* initial heap: old's 14 cells (base a0 = SX 10) hold arbitrary values
   SX 46..59; new's 14 (base a1 = SX 11) hold the saved values SX 32..45. *)
Definition swtch_heap0 : list (sval * sval) :=
  seg_cells 10 0 [46;47;48;49;50;51;52;53;54;55;56;57;58;59]%nat
  ++ seg_cells 11 0 [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat.
(* post-block heap: old's cells now hold the current callee regs (ctx_regs_nat);
   new's cells are unchanged. *)
Definition swtch_heap1 : list (sval * sval) :=
  seg_cells 10 0 ctx_regs_nat
  ++ seg_cells 11 0 [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat.

(* post-block registers: ra sp s0..s11 now hold new's saved values SX 32..45,
   in struct-context field order; a0 = SX 10, a1 = SX 11 unchanged. *)
Definition swtch_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 27) := SX 45 0]>
  (<[Regidx (mword_of_int 26) := SX 44 0]>
  (<[Regidx (mword_of_int 25) := SX 43 0]>
  (<[Regidx (mword_of_int 24) := SX 42 0]>
  (<[Regidx (mword_of_int 23) := SX 41 0]>
  (<[Regidx (mword_of_int 22) := SX 40 0]>
  (<[Regidx (mword_of_int 21) := SX 39 0]>
  (<[Regidx (mword_of_int 20) := SX 38 0]>
  (<[Regidx (mword_of_int 19) := SX 37 0]>
  (<[Regidx (mword_of_int 18) := SX 36 0]>
  (<[Regidx (mword_of_int 9)  := SX 35 0]>
  (<[Regidx (mword_of_int 8)  := SX 34 0]>
  (<[Regidx (mword_of_int 2)  := SX 33 0]>
  (<[Regidx (mword_of_int 1)  := SX 32 0]> vregs_init))))))))))))).

Lemma swtch_run :
  vc_block_s (VSt KernelSyms.swtch vregs_init swtch_heap0 []) swtch_prog
  = Some (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 []).
Proof. vm_compute. reflexivity. Qed.

(* THE TAIL RUN.  ProofSwtch.v executes swtch's first instruction
   [sd ra,0(a0)] (+0x00) ON ITS OWN, through the ▷-continuation store leaf
   [wp_sd_s_r_t_later] at the end of this file, so that the step's own ▷
   strips the ▷ off the target record ([SpecSwtch]'s [▷ valid_context]) --
   no later credit, and no [later_exist] (which fails at limit step
   indices).  That store writes only OLD's cell 0 (new's cells are first
   read at +0x34), so the VCgen runs the remaining 27 instructions from the
   state it leaves: old's cell 0 now holds ra ([SX 1]); everything else is
   [swtch_heap0].  The end state is [swtch_run]'s, unchanged. *)
Definition swtch_heap0_t : list (sval * sval) :=
  seg_cells 10 0 [1;47;48;49;50;51;52;53;54;55;56;57;58;59]%nat
  ++ seg_cells 11 0 [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat.

Lemma swtch_run_t :
  vc_block_s (VSt (KernelSyms.swtch + 4) vregs_init swtch_heap0_t []) (tl swtch_prog)
  = Some (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 []).
Proof. vm_compute. reflexivity. Qed.

Section WpSwtchVc.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.




  (* the 28-instruction body's code resource, extracted from kernel_text. *)
  Lemma swtch_code : kernel_text -∗ block_instrs_s KernelSyms.swtch swtch_prog.
  Proof using .
    iIntros "#Ht".
    cbn [block_instrs_s swtch_prog vop_s_rvc vop_s_ast vop_s_w].
    iSplitR; [by iApply swi_00|].
    iSplitR; [by iApply swi_04|].
    iSplitR; [by iApply swi_08|].
    iSplitR; [by iApply swi_0a|].
    iSplitR; [by iApply swi_0c|].
    iSplitR; [by iApply swi_10|].
    iSplitR; [by iApply swi_14|].
    iSplitR; [by iApply swi_18|].
    iSplitR; [by iApply swi_1c|].
    iSplitR; [by iApply swi_20|].
    iSplitR; [by iApply swi_24|].
    iSplitR; [by iApply swi_28|].
    iSplitR; [by iApply swi_2c|].
    iSplitR; [by iApply swi_30|].
    iSplitR; [by iApply swi_34|].
    iSplitR; [by iApply swi_38|].
    iSplitR; [by iApply swi_3c|].
    iSplitR; [by iApply swi_3e|].
    iSplitR; [by iApply swi_40|].
    iSplitR; [by iApply swi_44|].
    iSplitR; [by iApply swi_48|].
    iSplitR; [by iApply swi_4c|].
    iSplitR; [by iApply swi_50|].
    iSplitR; [by iApply swi_54|].
    iSplitR; [by iApply swi_58|].
    iSplitR; [by iApply swi_5c|].
    iSplitR; [by iApply swi_60|].
    iSplitR; [by iApply swi_64|].
    done.
  Qed.

  (* the tail's code: [swtch_code] minus its head ([swi_00], which the
     separate first step consumes).  [block_instrs_s] is a Fixpoint, so the
     split is by conversion. *)
  Lemma swtch_code_tl : kernel_text -∗ block_instrs_s (KernelSyms.swtch + 4) (tl swtch_prog).
  Proof using .
    iIntros "#Ht".
    iPoseProof (swtch_code with "Ht") as "H".
    iAssert (InstrBytes.instr (mword_of_int KernelSyms.swtch) false
               (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 1),
                       Regidx (mword_of_int 10), 8)) ∗
             block_instrs_s (KernelSyms.swtch + 4) (tl swtch_prog))%I
      with "[H]" as "[_ Htl]"; [iExact "H"|].
    iExact "Htl".
  Qed.

  (* [ctx_cells] / [callee_img] / [ret_pc] live in SwtchCtx.v. *)

  (* a heap segment's denotation IS the ctx-cell ownership of its values. *)
  Lemma seg_cells_ctx (rho : nat -> mword 64) (breg : nat) (c : mword 64)
      (off : Z) (ws : list nat) :
    rho breg = c ->
    ([∗ list] j ∈ seg_cells breg off ws, sval_den rho j.1 ↦₈ sval_den rho j.2)
    ⊣⊢ ctx_cells_at c off (map (fun w => rho w) ws).
  Proof using .
    intro Hc. revert off. induction ws as [|w rest IH]; intro off.
    - reflexivity.
    - cbn [seg_cells map ctx_cells_at]. rewrite big_sepL_cons. cbn [fst snd].
      rewrite IH.
      assert (Ha : sval_den rho (SX breg off) = add_vec c (mword_of_int off))
        by (cbn [sval_den]; rewrite Hc; reflexivity).
      assert (Hv : sval_den rho (SX w 0) = rho w) by (apply sval_den_SX0).
      rewrite Ha Hv. reflexivity.
  Qed.

  (* a 14-element list equals its own [nth]-expansion. *)
  Lemma list14_nth (l : list (mword 64)) (d : mword 64) :
    length l = 14%nat ->
    [nth 0 l d; nth 1 l d; nth 2 l d; nth 3 l d; nth 4 l d; nth 5 l d; nth 6 l d;
     nth 7 l d; nth 8 l d; nth 9 l d; nth 10 l d; nth 11 l d; nth 12 l d; nth 13 l d]
    = l.
  Proof using .
    intro H.
    do 14 (destruct l as [|? l]; [simpl in H; lia|]).
    destruct l; [reflexivity | simpl in H; lia].
  Qed.

  (* [valid_context] and its fixpoint machinery live in SwtchCtx.v; the
     sconf-tier whole-function swtch spec lives in SpecSwtch.v /
     ProofSwtch.v. *)


End WpSwtchVc.

(* ====================================================================== *)
(* 3. THE ▷-CONTINUATION STORE LEAF, for swtch's first instruction.        *)
(*    [WpSmodePtMem.wp_sd_s_r_t] with its continuation premise under ▷:    *)
(*    the proof is that leaf's, line for line -- the leaf already consumes *)
(*    [wp_instr_s_config_folded]'s internal [▷ (∀ npc ms1 mdv1, …)] with   *)
(*    an [iNext], which now strips the premise's ▷ too.  ProofSwtch.v runs *)
(*    [sd ra,0(a0)] through it so that the step's ▷ pays for the target    *)
(*    record's [▷ valid_context] (see [swtch_run_t] above).  A LOCAL copy  *)
(*    rather than a generalization of WpSmodePtMem.v: only ProofSwtch.v    *)
(*    requires this file, so nothing else rebuilds.  The imports below are *)
(*    WpSmodePtMem.v's own, in its order, so the copied proof resolves     *)
(*    every name as it does there; they come after section 2 so nothing    *)
(*    above changes.                                                       *)
(* ====================================================================== *)
From transfinite.base_logic.lib Require Import gen_heap.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import RegFile.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodeCore WpSmodeGpr.
Require Import UserBits.
Require Import SmodeCorePt SRegime WpSmodePtLeaves WpSmodePtFetch.
Require Import HartLift HartSpan HartSwp HartSMem WpSmodePtEngine KptGoodb Ktier.
Require Import MemAccessGen.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.
Require Import TsoCtx.
Import Defs.

(* as in WpSmodePtMem.v: the leaf takes the ctx word apart byte by byte. *)
Local Typeclasses Transparent word_pointsto word4_pointsto.

Section WpSwtchSdLater.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_sd_s_r_t_later (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (vold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    sr_ktier_wit R kt -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    (* A6.58: THE STORE'S PRICE.  A store is one APPEND to the log
       ([HartSMem.Wobl_ram]'s [vstep] and its [PWMsg]), and every
       value-changing law in the kit moves [gen_heap_interp] and
       [tso_interp_at] TOGETHER against the writer's registered context.
       So the leaf holds the token across the write; threaded, not
       consumed. *)
    TsoCtx.own_context XI -∗
    pa ↦₈[kt'] vold -∗
    ▷ ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      TsoCtx.own_context XI -∗
      pa ↦₈[kt'] (m !!! Regidx rs2) -∗
      mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea in *. clear pa a8 ea.
    iIntros "#Hwit #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hrun Hbytes Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (ctx_word_pointsto_aligned_p (KTR := kt') with "Hbytes")
      as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr
              (Virtaddr (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) 8
              = true) by exact Hpalign4.
    pose proof (off_bound_div
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                  ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* the window's own claim, off byte 0, then the word refolded *)
    iDestruct (ctx_word_pointsto_bytes (KTR := kt') with "Hbytes") as "Hbytes".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes")
      as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    (* A6.55/A6.58: THE CLAIM IS READ STRAIGHT OFF THE CTX BYTE.  The SC
       text forgot to the raw [↦ₘ] and re-minted through the shim, which
       A6.9 forbids and the sealed tier does not need:
       [TsoCtx.ctx_pointsto_phys] exposes the ppn, the canonicality and the
       tier pin WITHOUT leaving the tier, and [ctx_phys_pointsto_ram] gives
       the RAM-ness beside them. *)
    iDestruct (TsoCtx.ctx_pointsto_phys (KTR := kt') with "Hb0")
      as (ppn) "(#Hk & %Hcan & %Hid & Hp0)".
    iDestruct (TsoCtx.ctx_phys_pointsto_ram with "Hp0") as %Hkd0.
    iAssert (TsoCtx.ctx_pointsto (KTR := kt') _ _ _ _) with "[Hp0]" as "Hb0".
    { rewrite (TsoCtx.ctx_pointsto_phys (KTR := kt')).
      iExists ppn. iFrame "Hk Hp0". iSplit; by iPureIntro. }
    iEval (rewrite -(pa_add_0
             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    iDestruct (ctx_word_pointsto_intro (KTR := kt') _ _ _ _ Hpalign4 with "Hbytes")
      as "Hword".
    iApply (wp_instr_s_config_folded R pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 4⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗
                 TsoCtx.own_context XI ∗
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                   ↦₈[kt'] (m !!! Regidx rs2))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr
                    [Hfile Hrun Hword] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      (* THE SLOT STAYS FOLDED.  [sda_slot_acc_R] is the one place the two
         translation arms are told apart: it hands out an ABSTRACT write set
         with its frames, the residue, and the arm's translation SIDE
         CONDITION already discharged -- the one thing a regime-generic leaf
         cannot produce for itself ([sr_swp_side_ok] demands [tlb ∈ Drw], and
         the Bare arm's write set is empty). *)
      iDestruct (sda_slot_acc_R R dq mstatus0 menvcfg0 pmar0
                   Hmenvval0 HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hslot")
        as (SD satp0 pcfg paddr tv')
           "(%Hdisj & %Hsub & %Hsok & %Hpok & %Hside & Hrw & Hro & HRes &
             Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      assert (Lmxr : eq_vec (_get_Mstatus_MXR
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) ('b"0") = true)
        by (rewrite sda_rs_mst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM
                (register_lookup menvcfg (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) = PMM_Disabled)
        by (rewrite sda_rs_menv; exact Hpmm).
      assert (Lsxl : _get_Mstatus_SXL
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) = 'b"10")
        by (rewrite sda_rs_mst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))) = Some (sr_swp_mode R satp0))
        by (rewrite sda_rs_satp; exact (sr_swp_mode_ok R satp0 Hsok)).
      assert (Lep : effectivePrivilege (Store Data)
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) Supervisor
              = returnM Supervisor)
        by (rewrite sda_rs_mst;
            exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
        with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hclose] [-]").
      2:{ iApply (swp_execute_STORE_ram_S8 SD sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs2 rs1 m
                    (pa_of ppn (add_vec (m !!! Regidx rs1)
                                  (sign_extend' 64 imm)))
                    (m !!! Regidx rs2) pmar0 pcfg paddr
                    (TsoCtx.own_context XI ∗
                     (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       ↦₈[kt'] (m !!! Regidx rs2))%I (sr_swp_res R) rr
                    (sr_swp_mode R satp0)
                    (store_data8 (m !!! Regidx rs2))
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    Lmxr
                    Lpmm
                    Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       (Store Data) (sr_swp_mode R satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr
                       Lpmm
                       Lsxl
                       Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (sr_swp_mode R satp0) (sda_in_mst_D SD) (sda_in_satp_D SD)
                       Lsxl
                       Lmd)
                    Lep
                    HA Hord HW Hcov (pma_all_ram Hpma_all) Hkd0
                    Halign4
                    (pa_aligned_div ppn
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                       ltac:(lia) ltac:(exists 512; lia) Halign4)
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hword Hrun]").
          - iIntros "Hfrag HRes Hrw Hro".
            iApply (sda_translate_D R SD kt kt' dq (Store Data) KP_rw mstatus0
                      menvcfg0 satp0 pmar0 pcfg paddr tv'
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn rr
                      (or_intror (or_intror (or_introl eq_refl))) eq_refl
                      Hmenvval0
                      HSXL HMPRV Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid Hdisj
                      (Hside (Store Data) KP_rw
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                         tv' (or_intror (or_intror (or_introl eq_refl))))
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - (* THE RAM WRITE NODE.  A6.33's rework, one tier over: the
               store is a LEDGER APPEND, so the node takes the interp
               bundle and the token and hands back the advanced pair.
               [word_pointsto_write_c]'s conclusion IS [Wobl_ram]'s post,
               modulo the arm's own naming of [tv]. *)
            iIntros (sigma img log tv V) "%Htv Hsi Htso".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (word_pointsto_write_c (KTR := kt') img sigma log V
                    (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                    vold (m !!! Regidx rs2) Hcan Hoff
                    with "Hk Hmem Htso Hrun Hword")
              as "(Hmem & Htso & Hrun & Hword)".
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
            subst tv.
            iFrame "Hreg Hmem Hdev Htso Hrun Hword". }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & [Hrun Hword] & Hfrag)".
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   SD ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 sr_swp_res_at R satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (register_set tlb tvx
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      iAssert (sr_swp_res R
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree R
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes")
        as "(Hms & Hpriv & Hmenv & _ & _ & _ & Hslot)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hfrag"; [| by iApply resv_any_intro].
      iExists mstatus0, mdv0, (add_vec_int pc 4).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hrun Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc
         (-> & -> & -> & Hfile & Hrun & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                            Hrun Hword").
  Qed.

End WpSwtchSdLater.
