(* WpSconfCtl.v -- the SIE-AGNOSTIC control-flow leaf layer
   (interrupt-sweep stage 5): [sconf]+[sie_cap] twins of
   WpSmodePtCtl.v's fence / c.j / jal / c.ret leaves over the agnostic
   funnel [wp_instr_s_sconf], plus the compressed indirect call c.jalr
   (the c.ret leaf with rd = ra, i.e. with the link write).  Since the
   per-node port they go through that funnel's GENERAL engine,
   [WpSconfEngine.wp_instr_s_gen], which hands the obligation [sconf]
   whole -- a fence reads cur_privilege + menvcfg, a jump reads misa.

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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes RegFile HartTp WpNext.
Require Import RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import HartSwp.
Require Import WpSconfEngine.
Require Import IntrDefs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

(* THE EXEC-SIDE BRIDGES ARE GONE, and with them the [WpSmodePtCtl] import.
   This file used to carry local copies of [exec_execute_JAL_{zreg,gpr}_zca]
   and to import [exec_execute_FENCE_S] / [exec_execute_FENCEI_S], because a
   leaf's obligation was an [exec] fact about the whole instruction.  Under
   per-node stepping the obligation is an [swp] one, discharged by
   [WpSconfEngine]'s general step engine [wp_instr_s_gen] over the S-mode
   node rules there ([swp_execute_FENCE_S], [swp_execute_FENCEI_s],
   [swp_execute_JAL_s] / [_zreg_s], [swp_execute_JALR_s] / [_ret_s]) -- so
   nothing consumed them and they are deleted rather than carried. *)

Section WpSconfCtl.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {kt : ktier}.
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
  Lemma wp_fence_gen_s_sconf
      (pc : mword 64) (fm pred succ : mword 4) (rs rd : regidx)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (FENCE (fm, pred, succ, rs, rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_gen pc (add_vec_int pc 4) false
              (FENCE (fm, pred, succ, rs, rd)) m m n n b emp%I
              with "[] [] Hcg Hpc Hinstr [Hcont]").
    - iIntros (CIDn) "Hsc Hf HPC HnPC".
      iDestruct (sconf_ctl_acc (CID := CIDn) with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      iApply (swp_mono (CID := CIDn) with "[Hf HPC HnPC Hback] [Hpriv Hmenv]");
        [| iApply (swp_execute_FENCE_S (CID := CIDn) fm pred succ rs rd MENVCFG_S
                     with "Hcert Hpriv Hmenv") ].
      iIntros (e) "(-> & Hpriv & Hmenv)". iSplitR; [done|].
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc". iFrame.
    - iIntros (CIDx) "Hcap". iSplitL; [ iExact "Hcap" | done ].
    - iNext. iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  Lemma wp_fencei_s_sconf
      (pc : mword 64) (imm : mword 12) (rs rd : regidx)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (FENCEI (imm, rs, rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_gen pc (add_vec_int pc 4) false
              (FENCEI (imm, rs, rd)) m m n n b emp%I
              with "[] [] Hcg Hpc Hinstr [Hcont]").
    - iIntros (CIDn) "Hsc Hf HPC HnPC".
      iDestruct (sconf_ctl_acc (CID := CIDn) with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc".
      iApply (swp_mono (CID := CIDn) with "[Hsc Hf HPC HnPC] []");
        [| iApply (swp_execute_FENCEI_s (CID := CIDn) imm rs rd with "Hcert") ].
      iIntros (e) "->". iSplitR; [done|]. iFrame.
    - iIntros (CIDx) "Hcap". iSplitL; [ iExact "Hcap" | done ].
    - iNext. iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* the rw,w instance -- [release]'s [__sync_lock_release] barrier.  A
     restatement of the generic leaf (WRAPPER RECIPE), so the existing call
     sites do not change. *)
  Lemma wp_fence_s_sconf
      (pc : mword 64) (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                           Regidx (mword_of_int 0), Regidx (mword_of_int 0))) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_fence_gen_s_sconf pc (mword_of_int 0) (mword_of_int 3) (mword_of_int 1)
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
  Lemma wp_fence_gen_later_s_sconf
      (pc : mword 64) (fm pred succ : mword 4) (rs rd : regidx)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (FENCE (fm, pred, succ, rs, rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ▷ ( sie_cap_gpr kt m n b p -∗
        pc_is (add_vec_int pc 4) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_gen pc (add_vec_int pc 4) false
              (FENCE (fm, pred, succ, rs, rd)) m m n n b emp%I
              with "[] [] Hcg Hpc Hinstr [Hcont]").
    - iIntros (CIDn) "Hsc Hf HPC HnPC".
      iDestruct (sconf_ctl_acc (CID := CIDn) with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      iApply (swp_mono (CID := CIDn) with "[Hf HPC HnPC Hback] [Hpriv Hmenv]");
        [| iApply (swp_execute_FENCE_S (CID := CIDn) fm pred succ rs rd MENVCFG_S
                     with "Hcert Hpriv Hmenv") ].
      iIntros (e) "(-> & Hpriv & Hmenv)". iSplitR; [done|].
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc". iFrame.
    - iIntros (CIDx) "Hcap". iSplitL; [ iExact "Hcap" | done ].
    - (* the later this leaf HANDS OUT is the step's own, and the funnel
         offers it outermost -- [wp_next_later] is the commutation. *)
      iApply wp_next_later. iIntros (CIDx Hs).
      iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hs|].
      iNext. iIntros "Hcg' _ Hpc'". iApply ("Hcont" with "Hcg' Hpc'").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.j -- unconditional jump; a backward jump is a loop back edge, so   *)
  (* the continuation is UNDER A LATER (straight-line callers [iNext]).   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cj_s_sconf
      (pc : mword 64) (jimm : mword 21)
      (m : regfile) (n : nat) (b : bool) :
    let tgt := add_vec pc (sign_extend' 64 jimm) in
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (JAL (jimm, zreg)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ▷ ( sie_cap_gpr kt m n b p -∗
        pc_is tgt -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros tgt Hal0.
    iIntros "Hcg Hpc Hinstr Hcont".
    assert (Hz : uint (zero_extend' 5 ('b"00") : mword 5) = 0)
      by (vm_compute; reflexivity).
    iApply (wp_instr_s_gen pc tgt true (JAL (jimm, zreg)) m m n n b emp%I
              with "[] [] Hcg Hpc Hinstr [Hcont]").
    - iIntros (CIDn) "Hsc Hf HPC HnPC".
      iDestruct (sconf_ctl_acc (CID := CIDn) with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc".
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      iApply (swp_mono (CID := CIDn) with "[Hsc] [Hf HPC HnPC]");
        [| iApply (swp_execute_JAL_zreg_s (CID := CIDn) jimm
                     (zero_extend' 5 ('b"00")) (tp_pin (CID := CIDn) m) pc
                     (add_vec_int pc 2) Hz Hal0
                     with "Hcert Hf HPC HnPC Hmisa") ].
      iIntros (e) "(-> & Hf & HPC & HnPC & _)". iSplitR; [done|]. iFrame.
    - iIntros (CIDx) "Hcap". iSplitL; [ iExact "Hcap" | done ].
    - iApply wp_next_later. iIntros (CIDx Hs).
      iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hs|].
      iNext. iIntros "Hcg' _ Hpc'". iApply ("Hcont" with "Hcg' Hpc'").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* jal rd -- link write + jump.                                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_jal_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (JAL (imm, Regidx rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Hal0) "Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m
                      !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_instr_s_gen pc (add_vec pc (sign_extend' 64 imm)) false
              (JAL (imm, Regidx rd)) m
              (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m)
              n n b emp%I
              with "[] [] Hcg Hpc Hinstr [Hcont]").
    - iIntros (CIDn) "Hsc Hf HPC HnPC".
      iDestruct (sconf_ctl_acc (CID := CIDn) with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc".
      iApply (swp_mono (CID := CIDn) with "[Hsc] [Hf HPC HnPC]");
        [| iApply (swp_execute_JAL_s (CID := CIDn) imm rd
                     (tp_pin (CID := CIDn) m) pc (add_vec_int pc 4) Hrd Hal0
                     with "Hcert Hf HPC HnPC Hmisa") ].
      iIntros (e) "(-> & Hf & HPC & HnPC & _)". iSplitR; [done|].
      iEval (rewrite (tp_pin_upd m rd (regval_into_reg (add_vec_int pc 4)) Hrdtp))
        in "Hf".
      iFrame.
    - iIntros (CIDx) "Hcap". iSplitL; [| done ].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) n b Hsp
                with "Hcap").
    - iNext. iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ret (jalr x0, 0(ra)) -- no register write; the bundle is opened    *)
  (* for the LPE/priv/misa side conditions and reassembled.               *)
  (* ------------------------------------------------------------------- *)
  (* THE SIDE CONDITION ARRIVES BY INSTANCE RESOLUTION, NOT AS A PREMISE --
     see [IntrDefs.SrcOk].  c.ret's whole observable effect is the TARGET
     [ret_pc (rget m ra)], and that is a read of [ra] in [tp_pin m], so as
     spelled here it depends on the ambient hart at exactly one register,
     ra = tp.  Once the funnel's σ-callback moves inside [wp_next] the
     conclusion's [pc_is tgt] is owed at the hart the trap returned TO while
     [tgt] was elaborated at the hart we came FROM, and the two agree only away
     from tp.  c.ret writes no register, so there is no [rd_ok]/[ops_ok] slot to
     widen here, and this leaf has ~150 references -- more than any other in
     this sweep -- so an ordinary premise would move all of them.  The implicit
     [`{!SrcOk ra}] occupies no positional slot, so no call site changes.

     NOT REACHABLE AT tp IN PRACTICE, which is why the unguarded class is the
     right shape: a [c.ret] through the thread pointer is not xv6 code (the
     return address lives in [ra] by the ABI), and the one register the pin
     makes hart-dependent is exactly the one a return must not use.  If a call
     site ever does pass tp here, resolution fails AT THAT SITE naming the
     lemma and the register -- see the probe in WpSconfBtype.v.

     THE STATEMENT STAYS SPELLED [rget m ra].  Respelling [tgt] hart-free as
     [ret_pc (m !!! Regidx ra)] was measured on [wp_csdsp_s_sconf] and rejected:
     callers discharge and normalise this with [rget]-shaped rewrites, which
     then have nothing to match (99 consumer files).  The class carries the side
     condition; the spelling does not move. *)
  Lemma wp_cret_s_sconf
      (pc : mword 64) (ra : mword 5) `{!SrcOk ra}
      (m : regfile) (n : nat) (b : bool) :
    let tgt := ret_pc (rget m ra) in
    uint ra <> 0 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is tgt -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros tgt Hra.
    (* THE CLASS, CONSUMED -- and this line is the leaf's WIRING CHECK, not
       decoration: it names [ra], the register the statement above reads, so
       attaching the class to any other parameter fails to typecheck here.
       [tgt] is the return target as computed at the ENTRY hart; the ALL-HARTS
       form says the same word is the target at whatever hart the σ-callback is
       instantiated at.  Today that is still the entry hart, so [Htgt_all
       cpu_id] is a conversion; the funnel change that moves the callback
       inside [wp_next] instantiates it at the rebound hart and nothing else in
       this proof moves.  (At a VARIABLE [ra] this is not a conversion: the
       pin's [bool_decide] cannot reduce, so without the class there is no
       proof of it at all.) *)
    assert (Htgt_all : forall hh : CpuId, ret_pc (rget (CID := hh) m ra) = tgt)
      by (intros hh; unfold tgt; by rewrite (src_ok_rget_indep m ra hh CID)).
    iIntros "Hcg Hpc Hinstr Hcont".
    assert (Hz : uint (zero_extend' 5 ('b"00") : mword 5) = 0)
      by (vm_compute; reflexivity).
    iApply (wp_instr_s_gen pc tgt true (JALR (zeros' 12, Regidx ra, zreg))
              m m n n b emp%I
              with "[] [] Hcg Hpc Hinstr [Hcont]").
    - iIntros (CIDn) "Hsc Hf HPC HnPC".
      iDestruct (sconf_ctl_acc (CID := CIDn) with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      iApply (swp_mono (CID := CIDn) with "[Hback HPC] [Hf HnPC Hpriv Hmenv]");
        [| iApply (swp_execute_JALR_ret_s (CID := CIDn) ra
                     (zero_extend' 5 ('b"00")) (tp_pin (CID := CIDn) m)
                     (add_vec_int pc 2) Hz
                     with "Hcert Hf HnPC Hpriv Hmenv Hmisa") ].
      iIntros (e) "(-> & Hf & HnPC & Hpriv & Hmenv & _)". iSplitR; [done|].
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc".
      rewrite (Htgt_all CIDn). iFrame.
    - iIntros (CIDx) "Hcap". iSplitL; [ iExact "Hcap" | done ].
    - iNext. iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.jalr rs1 (jalr ra, 0(rs1)) -- the compressed INDIRECT CALL: the    *)
  (* [c.ret] leaf above with rd = ra instead of x0, so the link write of  *)
  (* [wp_jal_s_sconf] rides on top of it.  Target is [ret_pc (rget m rs1)]*)
  (* -- the ISA clears bit 0 of the computed address, so the caller owes  *)
  (* NO alignment side condition -- and the link value is pc+2.           *)
  (* Who needs it: fileread's FD_DEVICE arm calls devsw[major].read.      *)
  (* ------------------------------------------------------------------- *)
  (* THE READ-SIDE SIDE CONDITION IS ON [rs1] ONLY, and it comes by instance
     resolution ([IntrDefs.SrcOk]) while the WRITE side keeps its existing
     [rd_ok rd] premise slot.  The asymmetry is the whole design: [rd_ok] is
     already a positional premise here, so widening it costs nothing, whereas
     the read of the target base [rs1] has no slot of its own -- and note this
     leaf must NOT state [ops_ok b rd rs1 rs1] instead, because [ops_ok]'s
     source conjunct is guarded on [b] and the target of a jump has to be
     hart-independent at [b = true] as well.  So: [rd_ok] premise for the write,
     [SrcOk] class for the read. *)
  Lemma wp_cjalr_s_sconf
      (pc : mword 64) (rs1 rd : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (b : bool) :
    let tgt := ret_pc (rget m rs1) in
    uint rs1 <> 0 ->
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (JALR (zeros' 12, Regidx rs1, Regidx rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (add_vec_int pc 2)]> m) n b p -∗
      pc_is tgt -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros tgt Hrs1 Hrd Hrdok.
    (* the class, consumed at [rs1] -- the leaf's wiring check, exactly as in
       [wp_cret_s_sconf] above.  The link write is [rd]'s business and is
       handled by [rd_ok]/[tp_refold] further down. *)
    assert (Htgt_all : forall hh : CpuId, ret_pc (rget (CID := hh) m rs1) = tgt)
      by (intros hh; unfold tgt; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (add_vec_int pc 2)]> m
                      !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_instr_s_gen pc tgt true (JALR (zeros' 12, Regidx rs1, Regidx rd))
              m (<[Regidx rd := regval_into_reg (add_vec_int pc 2)]> m)
              n n b emp%I
              with "[] [] Hcg Hpc Hinstr [Hcont]").
    - iIntros (CIDn) "Hsc Hf HPC HnPC".
      iDestruct (sconf_ctl_acc (CID := CIDn) with "Hsc")
        as "(#Hcert & #Hmisa & Hpriv & Hmenv & Hback)".
      assert (Halign : eq_vec (access_vec_dec
                (update_vec_dec
                   (add_vec (tp_pin (CID := CIDn) m !!! Regidx rs1)
                      (sign_extend' 64 (zeros' 12))) 0
                   (MachineWord.MachineWord.N_to_word
                      (MachineWord.MachineWord.Z_idx 1)
                      (BinaryString.Raw.to_N "0" 0%N))) 0)
                (MachineWord.MachineWord.N_to_word
                   (MachineWord.MachineWord.Z_idx 1)
                   (BinaryString.Raw.to_N "0" 0%N)) = true)
        by (rewrite ret_pc_jalr; apply ret_pc_aligned).
      iApply (swp_mono (CID := CIDn) with "[Hback HPC] [Hf HnPC Hpriv Hmenv]");
        [| iApply (swp_execute_JALR_s (CID := CIDn) (zeros' 12) rs1 rd
                     (tp_pin (CID := CIDn) m) (add_vec_int pc 2) Hrd Halign
                     with "Hcert Hf HnPC Hpriv Hmenv Hmisa") ].
      iIntros (e) "(-> & Hf & HnPC & Hpriv & Hmenv & _)". iSplitR; [done|].
      iDestruct ("Hback" with "Hpriv Hmenv") as "Hsc".
      rewrite ret_pc_jalr (Htgt_all CIDn).
      iEval (rewrite (tp_pin_upd m rd (regval_into_reg (add_vec_int pc 2)) Hrdtp))
        in "Hf".
      iFrame.
    - iIntros (CIDx) "Hcap". iSplitL; [| done ].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg (add_vec_int pc 2)]> m) n b Hsp
                with "Hcap").
    - iNext. iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block for why.        *)
  (* Resolution must SUCCEED at an ordinary register and FAIL at tp, HERE,*)
  (* in the file whose leaves depend on it: an unresolved [SrcOk] inside  *)
  (* an [iApply] is SHELVED, so a broken hint (or one this file does not  *)
  (* see, through an import change) would not surface until some          *)
  (* consumer's [Qed] said "Attempt to save an incomplete proof" with no  *)
  (* mention of the class, the register or the call site.  [ra] = x1 is   *)
  (* the register [wp_cret_s_sconf] is actually applied at.               *)
  (* ------------------------------------------------------------------- *)
  Definition ctl_srcok_pos : SrcOk (mword_of_int 1 : mword 5) := _.
  Fail Definition ctl_srcok_neg : SrcOk Rtp := _.

End WpSconfCtl.
