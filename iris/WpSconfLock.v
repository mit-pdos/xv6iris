(* WpSconfLock.v -- the SIE-agnostic lock-invariant instruction leaves: the
   four kinds of access xv6's spinlock code makes to a [struct spinlock],
   each opening [lock_inv] (WpLock.v) around exactly one step.  [lockN] is
   disjoint from [minstretN], so the open works in BOTH sie_cap
   arms -- in particular while the absorbing engine's interrupt invariant is
   closed.

   The LOCK WORD (+0):
     wp_clw_lockopen_s_sconf         -- holding's read (no evidence needed)
     wp_clw_lockopen_locked_s_sconf  -- the same while HOLDING: the word is
                                       provably nonzero (free branch refuted)
     wp_amoswap_lockopen_s_sconf     -- acquire's test-and-set: yields the
                                       holder token + R on success
     wp_sw_zero_lockfin_s_sconf      -- release's clear: the caller's
                                       [lock_finisher] decides whether the
                                       invariant closes or is destroyed
   The CPU WORD (+16) -- owned by the invariant, never by a caller:
     wp_cld_lkcpu_lockopen_s_sconf        -- holding's read with no evidence:
                                            the value is whatever it is
     wp_cld_lkcpu_lockopen_locked_s_sconf -- holding's read as the HOLDER:
                                            the value IS mycpu()
     wp_csd_lkcpu_lockopen_s_sconf        -- acquire's [lk->cpu = mycpu()]
     wp_sd_zero_lkcpu_lockopen_s_sconf    -- release's [lk->cpu = 0]

   All but the amoswap are short wrappers over the ATOMIC-UPDATE generic
   load/store leaves (WpSconfMem.wp_{load,store}_s_sconf_au), which is where
   the address-translation and byte-level work lives; only the amoswap has no
   generic twin and carries its own copy of that recipe.                    *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import RegFile HartTp WpNext.
Require Import MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import SmodeCorePt WpAmo.
Require Import HartLift HartSpan HartSwp HartSMem.
Require Import WpSmodePtEngine.
Require Import KptGoodb.
Require Import WpIntrInv.
Require Import HartMemRun.
Require Import MemAccessGen.
Require Import UserBits.
Require Import WpLock.
Require Import ProcGeom.
Require Import SRegime.
Require Import IntrDefs WpSmodeIntr.
Require Import WpSconfMem.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* helper copies (Local in WpSmodePtMem.v / WpSmodePtLock.v). *)
Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Local Lemma data2_id_4 (v : mword 32) :
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v = v.
  Proof.
    apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
    erewrite bv_concat_unsigned by (cbn; lia).
    erewrite bv_concat_unsigned by (cbn; lia).
    rewrite !bv_unsigned_N_0.
    rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
    reflexivity.
  Qed.

Section WpSconfLock.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ==================================================================== *)
  (* THE READ-SIDE SIDE CONDITION OF EVERY LEAF IN THIS SECTION.  Read once. *)
  (*                                                                       *)
  (* Each lock leaf reads its lock POINTER out of a caller-chosen register, *)
  (* as [rget m rs1], and the two cpu-word writers additionally read their  *)
  (* stored value as [rget m rs2].  [rget] is a lookup in [tp_pin m]        *)
  (* (HartTp.v), so those words depend on the ambient hart at exactly one   *)
  (* register, rs = tp.  They are computed from the ENTRY map and appear    *)
  (* again inside the [wp_next] lambda, where the resources are about the   *)
  (* hart we resume on; once the funnel's sigma-callback moves inside        *)
  (* [WpNext.wp_next] those two harts differ, and they agree only away from *)
  (* tp.  [IntrDefs.SrcOk] is that side condition, delivered by INSTANCE    *)
  (* RESOLUTION because these leaves have no premise slot to widen: the     *)
  (* stores write no register at all, and the loads' [rd_ok] slot is about  *)
  (* the DESTINATION, not the lock pointer.  An implicit instance argument  *)
  (* shifts no positional argument, so the family converts with ZERO        *)
  (* call-site churn; multi-source leaves take one class argument per        *)
  (* source and they resolve independently.                                 *)
  (*                                                                       *)
  (* The premises stay spelled [rget m rs] (respelling them hart-free was   *)
  (* measured and broke 99 consumer files), so the reconciliation happens   *)
  (* INSIDE each proof, in one line, via [IntrDefs.src_ok_rget_indep].      *)
  (* That line is also the leaf's WIRING CHECK -- it names the register the  *)
  (* premise reads, so a class attached to the wrong parameter fails here    *)
  (* rather than shelving silently at a consumer's [Qed].                    *)
  (* ==================================================================== *)

  (* ==================================================================== *)
  (* THE LOCK'S TWO ADDRESS CLAIMS, off ONE PEEK-OPEN.                      *)
  (*                                                                       *)
  (* Per node an access TRANSLATES before it touches memory, so the memory  *)
  (* engines need the window's claim -- its [ppn], canonicality, RAM-ness   *)
  (* and tier pin -- BEFORE the atomic update that names the value is       *)
  (* opened.  The claim is about the ADDRESS, not the value, and            *)
  (* [lock_openable] is PERSISTENT, so one open-peek-close delivers both    *)
  (* fields' claims and hands the caller's credential straight back.        *)
  (* ==================================================================== *)
  Lemma lock_claims (γl : gname) (lk : mword 64) (str : string)
      (R T Dc : iProp Σ) (E : coPset) :
    ↑lockN ⊆ E ->
    (⊢ T -∗ Dc -∗ False) ->
    lock_openable γl lk str R Dc -∗ T ={E}=∗
      wordw_claim (KTR := KT0) 4 lk ∗
      wordw_claim (KTR := KT0) 8 (lock_cpu lk) ∗ T.
  Proof.
    intros HE Href. iIntros "#Hlock HT".
    iMod ("Hlock" $! E T with "[%] [] HT")
      as "(Hbody & HT & [Hclose _])"; [ exact HE | iApply Href | ].
    iDestruct "Hbody" as (w st) "(>Hword & >Hcpu & >Hg & Hbr)".
    iDestruct (wordw_claim_of (KTR := KT0) 4 lk (DfracOwn 1) w ltac:(lia)
                 with "Hword") as "#Hc4".
    iEval (rewrite /lk_cpu_res) in "Hcpu". iDestruct "Hcpu" as "[Hcell Hfr]".
    iDestruct (wordw_claim_of (KTR := KT0) 8 (lock_cpu lk) (DfracOwn 1)
                 (lk_cpu_val st) ltac:(lia) with "Hcell") as "#Hc8".
    iMod ("Hclose" with "[Hword Hcell Hfr Hg Hbr]") as "_".
    { iNext. iExists w, st. iFrame "Hword Hg Hbr".
      rewrite /lk_cpu_res. iFrame "Hcell Hfr". }
    iModIntro. iFrame "Hc4 Hc8 HT".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The lock word at +0.                                                 *)
  (* ------------------------------------------------------------------- *)

  (* holding's [lw a5,0(a0)]: any value, no evidence in or out. *)
  Lemma wp_clw_lockopen_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Tc Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    pa = lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    (⊢ Tc -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    lock_openable γl lk s R Dc -∗
    Tc -∗
    ( ∀ v : mword 32,
      wp_next b p (fun (CID : CpuId) =>
        Tc -∗
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n b p -∗
        pc_is (add_vec_int pc 2) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hpalk Hrd Hrdok Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock HTc Hcont".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R Tc Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock HTc") as "(#Hc4 & #Hc8 & HTc)".
    iApply (wp_load_s_sconf_au (kt := kt) (ktd := KT0) 4 true false pc rd rs1 imm m n
              (fun w => sign_extend' 64 w) (fun _ => Tc)
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [] [HTc] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk). iExact "Hc4". }
    { iMod ("Hlock" $! (⊤ ∖ ↑minstretN) Tc with "[%] [] HTc")
        as "(Hbody & HTc & [Hclose _])"; [solve_ndisj| iApply Href |].
      iDestruct "Hbody" as (w st) "(>Hword & Hrest)".
      iModIntro. iExists w.
      iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
      iIntros "Hword".
      iMod ("Hclose" with "[Hword Hrest]") as "_".
      { iNext. iExists w, st.
        iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | iExact "Hrest" ]. }
      iModIntro. iExact "HTc". }
    iIntros (v). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc HTc".
    iApply ("Hcont" $! v CID1 with "[] HTc Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* [h0] is the ENTRY hart's identity, LET-BOUND OUTSIDE the [wp_next]
     lambda: the holder token describes who currently holds the lock, a
     fact fixed before this load even runs, so writing [cpu_id] literally
     inside the continuation would silently (and here, since [cpu_id]
     prints the same at every hart, INVISIBLY) rebind it to the hart the
     step resumes on. *)
  Lemma wp_clw_lockopen_locked_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    pa = lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    (⊢ locked γl h0 -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    lock_openable γl lk s R Dc -∗
    locked γl h0 -∗
    ( ∀ v : mword 32,
      wp_next b p (fun (CID : CpuId) =>
        ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ -∗
        locked γl h0 -∗
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n b p -∗
        pc_is (add_vec_int pc 2) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 Hpalk Hrd Hrdok Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R (locked γl h0) Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock Htok") as "(#Hc4 & #Hc8 & Htok)".
    iApply (wp_load_s_sconf_au (kt := kt) (ktd := KT0) 4 true false pc rd rs1 imm m n
              (fun w => sign_extend' 64 w)
              (fun w => (⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝ ∗ locked γl h0)%I)
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [] [Htok] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk). iExact "Hc4". }
    { iMod ("Hlock" $! (⊤ ∖ ↑minstretN) (locked γl h0) with "[%] [] Htok")
        as "(Hbody & Htok & [Hclose _])"; [solve_ndisj| iApply Href |].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpu & >Hg & Hbr)".
      iDestruct (locked_state with "Hg Htok") as %Hst.
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      iModIntro. iExists w.
      iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
      iIntros "Hword".
      iMod ("Hclose" with "[Hword Hcpu Hg]") as "_".
      { iNext. iExists w, st. iFrame "Hcpu Hg".
        iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
        iRight. iPureIntro. split; [ rewrite Hst; discriminate | exact Hwnz ]. }
      iModIntro. iFrame "Htok". iPureIntro. exact Hwnz. }
    iIntros (v). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc (%Hvnz & Htok)".
    iApply ("Hcont" $! v CID1 with "[] [] Htok Hcg Hpc").
    - iPureIntro. exact Hs1.
    - iPureIntro. exact Hvnz.
  Qed.

  (* The word clear with the fate of the invariant left to the CALLER.  At
     this instant the store has happened and [lock_give] has pinned the state
     to [None], so the zeroed lock word, the cleared cpu word, the ghost state
     and [R] are all in hand at once.  The finisher is handed the
     close-or-destroy choice and those pieces, and decides ([lock_finisher],
     WpLock.v; [lock_finisher_close] and [lock_finisher_destroy] are its two
     canonical instances).  Release is proved ONCE over this leaf and
     instantiated twice -- there is deliberately no close-only and no
     destroy-only twin of this lemma.

     The opening credential IS the holder token: at this instruction the
     caller holds [locked_pre], and that is what proves the lock is not
     already dead.  It could not be anything else -- an object's last
     reference has necessarily gone home by the time release runs. *)
  Lemma wp_sw_zero_lockfin_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Dc Out : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    pa = lk ->
    (⊢ locked_pre γl cpu_id -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    lock_openable γl lk s R Dc -∗
    locked_pre γl cpu_id -∗
    R -∗
    lock_finisher γl lk s R Dc Out (⊤ ∖ ↑minstretN) -∗
    wp_next b p (fun (CID : CpuId) =>
      Out -∗
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hpalk Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock Htok HRes Hfin Hcont".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R (locked_pre γl cpu_id) Dc ⊤
            ltac:(solve_ndisj) Href with "Hlock Htok")
      as "(#Hc4 & #Hc8 & Htok)".
    rewrite /lock_finisher.
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 (tp_pin m) (mword_of_int 0 : mword 5) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hz Hfile]".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    assert (Hzero : trunc32 (tp_pin m !!! Regidx (mword_of_int 0 : mword 5))
                    = (mword_of_int 0 : mword 32))
      by (rewrite Hz; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_store_s_sconf_au (kt := kt) (ktd := KT0) 4 false pc (mword_of_int 0 : mword 5) rs1 imm m n
              (trunc32 (tp_pin m !!! Regidx (mword_of_int 0 : mword 5)))
              Out
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (tp_pin m !!! Regidx (mword_of_int 0 : mword 5)))
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [] [Htok HRes Hfin] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk). iExact "Hc4". }
    { iMod ("Hlock" $! (⊤ ∖ ↑minstretN) (locked_pre γl cpu_id) with "[%] [] Htok")
        as "(Hbody & Htok & Hchoice)"; [solve_ndisj| iApply Href |].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpu & >Hg & Hbr)".
      iMod (lock_give γl st cpu_id with "Hg Htok") as "(%Hst & Hg & Hfrag)".
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      subst st.
      (* the lock is in release's window, so the cpu field is home WHOLE and
         at 0 -- the finisher's view of it is unchanged (WpLock.v). *)
      iEval (rewrite lk_cpu_res_win) in "Hcpu".
      iModIntro. iExists w.
      iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
      iIntros "Hword".
      iApply ("Hfin" with "Hchoice Hg Hfrag [Hword] Hcpu HRes").
      rewrite -Hzero -Hpalk. iExact "Hword". }
    iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc HOut".
    iApply ("Hcont" $! CID1 with "[] HOut Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The cpu word at +16.  It belongs to the invariant; what a caller     *)
  (* brings is the ghost evidence that decides what the word says.        *)
  (* ------------------------------------------------------------------- *)

  (* the generic read: the caller's evidence [T] (a ticket or the holder
     token) determines a fact [phi] about the recorded owner word. *)
  Lemma wp_ld_lkcpu_lockopen_gen (cmp : bool)
      (γl : gname) (lk : mword 64) (s : string) (R Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (T : iProp Σ) (phi : mword 64 -> Prop) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    (* THE VIEW PREMISE SEES THE HELD-SET FRAGMENT TOO, and that is what lets
       a NON-holder decide the word.  In the [Some (i, true)] state the
       invariant keeps [lk_in i s] beside the cell (WpLock.v's owner-field
       block), so a caller whose evidence [T] is its own hart's held-set
       authority can refute [i = cpu_id] and conclude the word is not this
       hart's [struct cpu] -- which is what kills acquire's
       [if(holding(lk)) panic] arm.  The premise does NOT hand the fragment
       back: its conclusion is pure, so the proof mode keeps every hypothesis
       it was given and the leaf puts the fragment straight back into the
       invariant. *)
    (forall st : lock_state, ⊢ lock_auth γl st -∗ lk_cpu_frag st s -∗ T -∗ ⌜phi (lk_cpu_val st)⌝) ->
    (⊢ T -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc cmp (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    lock_openable γl lk s R Dc -∗
    T -∗
    ( ∀ c : mword 64,
      wp_next b p (fun (CID : CpuId) =>
        ⌜phi c⌝ -∗
        T -∗
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg c]> m) n b p -∗
        pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hpacpu Hrd Hrdok Hview Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock HT Hcont".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R T Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock HT") as "(#Hc4 & #Hc8 & HT)".
    iApply (wp_load_s_sconf_au (kt := kt) (ktd := KT0) 8 cmp false pc rd rs1 imm m n
              (fun w => w) (fun c => (⌜phi c⌝ ∗ T)%I)
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 data2_ext_8 Hrd Hrdok
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [] [HT] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with (lock_cpu lk)
        by (symmetry; exact Hpacpu). iExact "Hc8". }
    { iMod ("Hlock" $! (⊤ ∖ ↑minstretN) T with "[%] [] HT")
        as "(Hbody & HT & [Hclose _])"; [solve_ndisj| iApply Href |].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpures & >Hg & Hbr)".
      (* the invariant owns the cell WHOLE in every state, so the AU's [dqm],
         chosen outside this fupd where [st] is still existential, is simply
         [DfracOwn 1] -- the state-blindness the fixed-half split used to buy
         (WpLock.v's owner-field block). *)
      iEval (rewrite /lk_cpu_res) in "Hcpures".
      iDestruct "Hcpures" as "[Hcpu Hrest]".
      iDestruct (Hview st with "Hg Hrest HT") as %Hphi.
      iModIntro. iExists (lk_cpu_val st).
      iSplitL "Hcpu"; [ rewrite -Hpacpu; iExact "Hcpu" | ].
      iIntros "Hcpu".
      iMod ("Hclose" with "[Hword Hcpu Hrest Hg Hbr]") as "_".
      { iNext. iExists w, st. iFrame "Hword Hg Hbr".
        rewrite /lk_cpu_res. iFrame "Hrest".
        rewrite -Hpacpu. iExact "Hcpu". }
      iModIntro. iFrame "HT". iPureIntro. exact Hphi. }
    iIntros (c). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc (%Hphi & HT)".
    iSpecialize ("Hcont" $! c CID1 with "[]"); [iPureIntro; exact Hs1|].
    iSpecialize ("Hcont" with "[]"); [iPureIntro; exact Hphi|].
    iApply ("Hcont" with "HT Hcg Hpc").
  Qed.

  (* holding's [ld a5,16(a0)] with NO evidence: the recorded owner word is
     whatever it is (a non-holder learns nothing about it -- which is why
     holding() may answer either way, and acquire's panic arm is real). *)
  Lemma wp_cld_lkcpu_lockopen_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Tc Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    (⊢ Tc -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    lock_openable γl lk s R Dc -∗
    Tc -∗
    ( ∀ c : mword 64,
      wp_next b p (fun (CID : CpuId) =>
        Tc -∗
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg c]> m) n b p -∗
        pc_is (add_vec_int pc 2) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hpacpu Hrd Hrdok Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock HTc Hcont".
    iApply (wp_ld_lkcpu_lockopen_gen true γl lk s R Dc pc rd rs1 imm m n
              Tc (fun _ => True) b
              Hpacpu Hrd Hrdok
              ltac:(intro st; iIntros "_ _ _"; done) Href
              with "Hcg Hpc Hinstr Hlock HTc [Hcont]").
    iIntros (c). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "_ HTc Hcg Hpc".
    iApply ("Hcont" $! c CID1 with "[] HTc Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* THE SAME READ, BY A HART THAT PROVABLY DOES NOT HOLD THE LOCK.  The
     evidence is this hart's held-set AUTHORITY plus [s ∉ lks]: were the lock
     held BY THIS HART, the invariant would be keeping [lk_in cpu_id s]
     beside the cell, which [cpu_locks_not_in] refutes.  So the recorded
     owner is some OTHER hart's [struct cpu] -- or 0, in the free state and
     in acquire's one-store window, and [cpus_ptr] is never 0 -- but never
     this hart's.  holding() therefore returns 0, which is what makes
     acquire's [if(holding(lk)) panic] arm DEAD CODE rather than something a
     panic credential has to absorb (WpLock.v's owner-field block states the
     theorem; this is where it is cashed).

     The authority is threaded in and back out: it is not persistent, and its
     owner -- [cpu_own] -- wants it back. *)
  Lemma wp_cld_lkcpu_lockopen_notheld_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Tc Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) (lks : gset string) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    (* THE ENTRY HART, let-bound OUTSIDE the [wp_next] lambda -- the held-set
       authority is about the hart that ran the read, and so is the [struct
       cpu] pointer the answer is compared against.  Written literally inside
       the continuation they would silently rebind to whichever hart the step
       resumes on. *)
    let h0 := cpu_id in
    let cpuv := mycpu_ret cid_word in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    s ∉ lks ->
    (⊢ Tc -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    lock_openable γl lk s R Dc -∗
    Tc -∗
    cpu_locks_at h0 lks -∗
    ( ∀ c : mword 64,
      wp_next b p (fun (CID : CpuId) =>
        ⌜c <> cpuv⌝ -∗
        Tc -∗
        cpu_locks_at h0 lks -∗
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg c]> m) n b p -∗
        pc_is (add_vec_int pc 2) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 cpuv Hpacpu Hrd Hrdok Hfresh Href.
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    (* the free / window states record 0, and no hart's [struct cpu] is 0 *)
    assert (Hz : forall i : CPU, (zero_reg : mword 64) <> cpus_ptr i)
      by (intro i; apply eq_vec_false_iff; apply cpus_ptr_nonzero).
    iIntros "Hcg Hpc Hinstr #Hlock HTc Hlks Hcont".
    iApply (wp_ld_lkcpu_lockopen_gen true γl lk s R Dc pc rd rs1 imm m n
              (Tc ∗ cpu_locks_at h0 lks)%I
              (fun c => c <> cpuv) b
              Hpacpu Hrd Hrdok
              ltac:(intro st; iIntros "Hg Hfrag [HTc Hlks]";
                    unfold cpuv; rewrite -cpus_ptr_cid;
                    destruct st as [[i []]|];
                    [ rewrite lk_cpu_val_held /lk_cpu_frag;
                      destruct (decide (i = h0)) as [Heqi|Hne];
                      [ subst i;
                        iDestruct (cpu_locks_not_in h0 lks s Hfresh with "Hlks Hfrag") as %[]
                      | iPureIntro; intro Heq; exact (Hne (cpus_ptr_inj _ _ Heq)) ]
                    | iPureIntro; exact (Hz h0)
                    | iPureIntro; exact (Hz h0) ])
              ltac:(iIntros "[HTc _]"; iApply Href; iExact "HTc")
              with "Hcg Hpc Hinstr Hlock [HTc Hlks] [Hcont]").
    { iFrame "HTc Hlks". }
    iIntros (c). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "%Hc [HTc Hlks] Hcg Hpc".
    iApply ("Hcont" $! c CID1 with "[] [%] HTc Hlks Hcg Hpc");
      [ iPureIntro; exact Hs1 | exact Hc ].
  Qed.

  (* the same read as the HOLDER: the token pins the word to mycpu(), so
     holding() returns 1. *)
  (* [h0]/[cpuv] are the ENTRY hart's identity, LET-BOUND OUTSIDE the
     [wp_next] lambda: they describe who the memory word [lk->cpu] was
     written for (a fact about the ENTRY hart, fixed before this load
     even runs), so writing them literally inside the continuation would
     silently rebind them to whichever hart the step resumes on. *)
  Lemma wp_cld_lkcpu_lockopen_locked_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    let cpuv := mycpu_ret cid_word in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    (⊢ locked γl h0 -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    lock_openable γl lk s R Dc -∗
    locked γl h0 -∗
    wp_next b p (fun (CID : CpuId) =>
      locked γl h0 -∗
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg cpuv]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 cpuv Hpacpu Hrd Hrdok Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iApply (wp_ld_lkcpu_lockopen_gen true γl lk s R Dc pc rd rs1 imm m n
              (locked γl h0)
              (fun c => c = cpuv) b
              Hpacpu Hrd Hrdok
              ltac:(intro st; iIntros "Hg _ Htok"; unfold cpuv; rewrite -cpus_ptr_cid;
                    iApply (locked_cpu_eq with "Hg Htok")) Href
              with "Hcg Hpc Hinstr Hlock Htok [Hcont]").
    iIntros (c). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "%Hc Htok Hcg Hpc". subst c.
    iApply ("Hcont" $! CID1 with "[] Htok Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* the generic write of the cpu word: the caller's evidence [T] becomes
     [T'] as the ghost state moves to [stn], whose recorded owner word is
     exactly what the instruction stores. *)
  Lemma wp_sd_lkcpu_lockopen_gen (cmp : bool)
      (γl : gname) (lk : mword 64) (s : string) (R Dc : iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (T T' : iProp Σ) (stn : lock_state) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    lk_cpu_val stn = rget m rs2 ->
    (* THE EXCHANGE, not just a ghost step: the cpu field is co-owned with
       the holding hart (WpLock.lk_cpu_res), so a store to it has to be
       licensed by whatever the caller brings.  The premise takes the
       invariant's share and produces (a) the WHOLE cell, which is what the
       store needs, and (b) a wand that takes the whole cell back at the new
       value and rebuilds the invariant's share.  acquire's instance splits
       the written cell and pays a half into its own held-lock set; release's
       instance redeems the set fragment to complete the cell in the first
       place. *)
    (forall st : lock_state,
       ⊢ lock_auth γl st -∗ lk_cpu_res st lk s -∗ T ==∗
         ⌜st <> None⌝ ∗ ⌜stn <> None⌝ ∗ lock_auth γl stn ∗
         lock_cpu lk ↦₈ lk_cpu_val st ∗
         (lock_cpu lk ↦₈ lk_cpu_val stn ==∗ lk_cpu_res stn lk s ∗ T')) ->
    (⊢ T -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc cmp (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    lock_openable γl lk s R Dc -∗
    T -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
      T' -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hpacpu Hsv Hupd Href.
    (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock HT Hcont".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R T Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock HT") as "(#Hc4 & #Hc8 & HT)".
    iApply (wp_store_s_sconf_au (kt := kt) (ktd := KT0) 8 cmp pc rs2 rs1 imm m n
              (rget m rs2) T' (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [] [HT] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with (lock_cpu lk)
        by (symmetry; exact Hpacpu). iExact "Hc8". }
    { iMod ("Hlock" $! (⊤ ∖ ↑minstretN) T with "[%] [] HT")
        as "(Hbody & HT & [Hclose _])"; [solve_ndisj| iApply Href |].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpures & >Hg & Hbr)".
      iMod (Hupd st with "Hg Hcpures HT")
        as "(%Hstne & %Hstnne & Hg & Hcpu & Hback)".
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      iModIntro. iExists (lk_cpu_val st).
      iSplitL "Hcpu"; [ rewrite -Hpacpu; iExact "Hcpu" | ].
      iIntros "Hcpu".
      iMod ("Hback" with "[Hcpu]") as "[Hcpures HT']".
      { rewrite Hsv -Hpacpu. iExact "Hcpu". }
      iMod ("Hclose" with "[Hword Hcpures Hg]") as "_".
      { iNext. iExists w, stn. iFrame "Hword Hg Hcpures".
        iRight. iPureIntro. split; [ exact Hstnne | exact Hwnz ]. }
      iModIntro. iFrame "HT'". }
    iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc HT'".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc HT'").
    iPureIntro. exact Hs1.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE TWO EXCHANGES, one per cpu-field store.  Each is the [Hupd]        *)
  (* premise of the generic store leaf above, named so the instance below   *)
  (* is a one-line application.                                             *)
  (* ------------------------------------------------------------------- *)

  (* acquire: the window closes.  [r ∉ S] is a PREMISE the caller supplies,
     not a fact derived from the cpu field -- which is what let the half-cell
     stake apparatus go (WpLock.v's owner-field block).  The cell is whole in
     both states, so the "exchange" is now an ordinary store and only the
     GHOST insert happens here.

     NON-MEMBERSHIP, not yet the lock ORDER.  [r ∉ S] is all either obligation
     needs: minting the fragment ([LockSet.cpu_locks_insert]) and killing
     acquire's [if(holding(lk)) panic] arm.  Deadlock-freedom wants the
     stronger [LockRank.locks_below S r], which implies this one
     ([locks_below_not_elem]) and lands later. *)
  Local Lemma lkcpu_take_exchange (γl : gname) (lk : mword 64) (r : string)
      (S : gset string) (Hfresh : r ∉ S) (st : lock_state) :
    ⊢ lock_auth γl st -∗ lk_cpu_res st lk r -∗
      (locked_pre γl cpu_id ∗ cpu_locks_at cpu_id S) ==∗
      ⌜st <> None⌝ ∗ ⌜Some (cpu_id, true) <> None⌝ ∗
      lock_auth γl (Some (cpu_id, true)) ∗
      lock_cpu lk ↦₈ lk_cpu_val st ∗
      (lock_cpu lk ↦₈ lk_cpu_val (Some (cpu_id, true)) ==∗
         lk_cpu_res (Some (cpu_id, true)) lk r ∗
         (locked γl cpu_id ∗ cpu_locks_at cpu_id ({[r]} ∪ S))).
  Proof.
    iIntros "Hg Hcpures [Htok Hcl]".
    iMod (lock_setcpu γl st cpu_id with "Hg Htok") as "(%Hst & Hg & Htok)".
    rewrite Hst.
    iEval (rewrite lk_cpu_res_win) in "Hcpures".
    iModIntro.
    iSplitR; [ iPureIntro; discriminate | ].
    iSplitR; [ iPureIntro; discriminate | ].
    iFrame "Hg".
    iSplitL "Hcpures"; [ iExact "Hcpures" | ].
    iIntros "Hcell".
    iMod (cpu_locks_insert cpu_id S r Hfresh with "Hcl") as "[Hcl Hin]".
    iModIntro. rewrite lk_cpu_res_held. iFrame "Hcell Hin Htok Hcl".
  Qed.

  (* release: the fragment the invariant kept is redeemed to retire the rank
     from the hart's set.  No premise: membership is DERIVED from the fragment
     ([cpu_locks_delete]), which is the direction that never needed the order. *)
  Local Lemma lkcpu_give_exchange (γl : gname) (lk : mword 64) (r : string)
      (S : gset string) (st : lock_state) :
    ⊢ lock_auth γl st -∗ lk_cpu_res st lk r -∗
      (locked γl cpu_id ∗ cpu_locks_at cpu_id S) ==∗
      ⌜st <> None⌝ ∗ ⌜Some (cpu_id, false) <> None⌝ ∗
      lock_auth γl (Some (cpu_id, false)) ∗
      lock_cpu lk ↦₈ lk_cpu_val st ∗
      (lock_cpu lk ↦₈ lk_cpu_val (Some (cpu_id, false)) ==∗
         lk_cpu_res (Some (cpu_id, false)) lk r ∗
         (locked_pre γl cpu_id ∗ cpu_locks_at cpu_id (S ∖ {[r]}) ∗ ⌜r ∈ S⌝)).
  Proof.
    iIntros "Hg Hcpures [Htok Hcl]".
    iMod (lock_clrcpu γl st cpu_id with "Hg Htok") as "(%Hst & Hg & Htok)".
    rewrite Hst.
    iEval (rewrite lk_cpu_res_held) in "Hcpures".
    iDestruct "Hcpures" as "[Hcell Hin]".
    iMod (cpu_locks_delete cpu_id S r with "Hcl Hin") as "(%Hin & Hcl)".
    iModIntro.
    iSplitR; [ iPureIntro; discriminate | ].
    iSplitR; [ iPureIntro; discriminate | ].
    iFrame "Hg".
    iSplitL "Hcell"; [ iExact "Hcell" | ].
    iIntros "Hcell".
    iModIntro. rewrite lk_cpu_res_win. iFrame "Hcell Htok Hcl".
    iPureIntro. exact Hin.
  Qed.

  (* acquire's [c.sd a0,16(lk)] -- lk->cpu := mycpu(): the acquire window
     closes and the caller gets THE holder token. *)
  (* THE ONE INSTRUCTION THAT ADDS TO THE HELD-LOCK SET.  It threads the
     hart's set ([LockSet.cpu_locks_at], out of [IntrDefs.cpu_hart]) and hands
     it back with this lock's RANK added.  THE FRESHNESS PREMISE LANDS HERE:
     the caller must show this lock's rank is not already held, which is what
     mints the set fragment.  The predecessor had no premise and instead
     derived [lk ∉ S] from the cpu field -- see WpLock.v's owner-field block
     for what that cost.  (The lock ORDER strengthens this to
     [LockRank.locks_below S s] in a later phase.) *)
  Lemma wp_csd_lkcpu_lockopen_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Dc : iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) (S : gset string) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    pa = lock_cpu lk ->
    rget m rs2 = mycpu_ret cid_word ->
    s ∉ S ->
    (⊢ locked_pre γl h0 -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    lock_openable γl lk s R Dc -∗
    locked_pre γl h0 -∗
    cpu_locks_at h0 S -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 2) -∗
      locked γl h0 -∗
      cpu_locks_at h0 ({[s]} ∪ S) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 Hpacpu Hmycpu Hfresh Href.
    (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    assert (Hsv : lk_cpu_val (Some (h0, true)) = rget m rs2).
    { rewrite lk_cpu_val_held cpus_ptr_cid. exact (eq_sym Hmycpu). }
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcl Hcont".
    iApply (wp_sd_lkcpu_lockopen_gen true γl lk s R Dc pc rs2 rs1 imm m n
              (locked_pre γl h0 ∗ cpu_locks_at h0 S)%I
              (locked γl h0 ∗ cpu_locks_at h0 ({[s]} ∪ S))%I
              (Some (h0, true)) b
              Hpacpu Hsv
              (lkcpu_take_exchange γl lk s S Hfresh)
              ltac:(iIntros "[Htok _]"; iApply Href; iExact "Htok")
              with "Hcg Hpc Hinstr Hlock [Htok Hcl] [Hcont]").
    { iFrame "Htok Hcl". }
    iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc [Htok Hcl]".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Htok Hcl").
    iPureIntro. exact Hs1.
  Qed.

  (* release's [sd zero,16(lk)] -- lk->cpu := 0: back into the window the
     word clear then closes. *)
  (* THE ONE INSTRUCTION THAT REMOVES FROM THE HELD-LOCK SET -- and it is
     not merely bookkeeping: while the lock is held the invariant owns only
     HALF of the cpu field, so this store is IMPOSSIBLE until the hart
     redeems its set fragment for the other half ([cpu_locks_delete]). *)
  Lemma wp_sd_zero_lkcpu_lockopen_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Dc : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) (S : gset string) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    pa = lock_cpu lk ->
    (⊢ locked γl h0 -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    lock_openable γl lk s R Dc -∗
    locked γl h0 -∗
    cpu_locks_at h0 S -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      locked_pre γl h0 -∗
      cpu_locks_at h0 (S ∖ {[s]}) -∗
      (* the rank WAS held -- so the caller knows the set strictly shrank,
         which is what pop_off's unwind premise needs. *)
      ⌜s ∈ S⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 Hpacpu Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcl Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 (tp_pin m) (mword_of_int 0 : mword 5) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hz Hfile]".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    assert (Hsv : lk_cpu_val (Some (h0, false))
                  = tp_pin m !!! Regidx (mword_of_int 0 : mword 5))
      by (rewrite lk_cpu_val_win Hz; reflexivity).
    iApply (wp_sd_lkcpu_lockopen_gen false γl lk s R Dc pc
              (mword_of_int 0 : mword 5) rs1 imm m n
              (locked γl h0 ∗ cpu_locks_at h0 S)%I
              (locked_pre γl h0 ∗ cpu_locks_at h0 (S ∖ {[s]}) ∗ ⌜s ∈ S⌝)%I
              (Some (h0, false)) b
              Hpacpu Hsv
              (lkcpu_give_exchange γl lk s S)
              ltac:(iIntros "[Htok _]"; iApply Href; iExact "Htok")
              with "Hcg Hpc Hinstr Hlock [Htok Hcl] [Hcont]").
    { iFrame "Htok Hcl". }
    iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc (Htok & Hcl & %Hin)".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Htok Hcl [%]"); [ | exact Hin ].
    iPureIntro. exact Hs1.
  Qed.

  (* acquire's test-and-set: on success (the word read 0) the caller gets the
     holder token in acquire's [lk->cpu]-not-yet-written window, plus R. *)
  (* [h0] is the ENTRY hart's identity, LET-BOUND OUTSIDE the [wp_next]
     lambda: the CAS itself (and the ghost step that takes the lock on
     success) happens entirely on the entry hart, before any migration
     the absorbing engine might introduce for the NEXT instruction, so
     the payload's holder token must name the entry hart -- writing
     [cpu_id] literally inside the continuation would silently rebind it
     to whichever hart the step resumes on. *)
  Lemma wp_amoswap_lockopen_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R Tc Dc : iProp Σ)
      (pc : mword 64) (rd rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (zeros' 64) in
    let h0 := cpu_id in
    pa = lk ->
    neq_vec (sign_extend' 64 (amoswap_stored (rget m rs2))) zero_reg = true ->
    uint rd <> 0 ->
    rd_ok rd ->
    (⊢ Tc -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)) -∗
    lock_openable γl lk s R Dc -∗
    Tc -∗
    ( ∀ w : mword 32,
      wp_next b p (fun (CID : CpuId) =>
        Tc -∗
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg (amoswap_loaded w)]> m) n b p -∗
        pc_is (add_vec_int pc 4) -∗
        (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked_pre γl h0 ∗ R
         ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 Hpalk Hstz Hrd Hrdok Href.
    rdok_split Hrdok.
    iIntros "Hcg Hpc #Hinstr #Hlock HTc Hcont".
    iApply (wp_instr_s_sconf m n b b pc false
              (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
              (fun (_CIDx : CpuId) npc _ms' m' n' =>
                 ∃ w : mword 32,
                   ⌜npc = add_vec_int pc 4⌝ ∗
                   ⌜m' = <[Regidx rd := regval_into_reg (amoswap_loaded w)]> m⌝ ∗
                   ⌜n' = n⌝ ∗ Tc ∗
                   (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked_pre γl h0 ∗ R
                    ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝))%I
              with "Hcg Hpc Hinstr [HTc Hcont]").
    iNext.
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HTc".
    - (* ---------------- THE INSTRUCTION ---------------- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
        by exact (src_ok_rget_indep m rs1 CID CID0).
      assert (Lpin_rs2 : tp_pin (CID := CID) m !!! Regidx rs2 = rget m rs2)
        by exact (src_ok_rget_indep m rs2 CID CID0).
      iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
          Hmdl & Hmenv)".
      pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                          HMPP & HTVM).
      (* THE SLOT STAYS FOLDED -- the pre-port shape.  The frame comes out of
         [WpIntrInv.sda_slot_acc] below, which is the one place the two
         translation arms are told apart. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      (* ---- PEEK: the lock word's own claim, then close again ---- *)
      iApply (swp_fupd (CID := CID)).
      iMod ("Hlock" $! ⊤ Tc with "[%] [] HTc")
        as "(Hbody & HTc & [Hclose _])"; [solve_ndisj | iApply Href |].
      iDestruct "Hbody" as (w0 st0) "(>Hw & Hcpu & Hg & Hbr)".
      iEval (rewrite /lock_word -Hpalk) in "Hw".
      iAssert (⌜is_aligned_paddr (Physaddr pa) 4 = true⌝)%I as %Hpalign4.
      { iDestruct "Hw" as "[$ _]". }
      iDestruct "Hw" as "[_ Hb]".
      iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hb") as "[Hb0 Hbcl]".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite pa_add_0) in "Hb0".
      iDestruct (mem_pointsto_acc with "Hb0")
        as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
      iDestruct ("Href0" with "Hp0") as "Hb0".
      iEval (rewrite -(pa_add_0 pa)) in "Hb0".
      iDestruct ("Hbcl" with "Hb0") as "Hb".
      iMod ("Hclose" with "[Hb Hcpu Hg Hbr]") as "_".
      { iNext. iExists w0, st0. iFrame "Hcpu Hg Hbr".
        rewrite /lock_word -Hpalk /word4_pointsto. iFrame "Hb".
        iPureIntro. exact Hpalign4. }
      iModIntro.
      assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true)
        by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
      pose proof (off_bound_div pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4)
        as Hoff.
      rewrite (uint_unsigned_n _) in Hoff.
      (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  The write set [SD] is
             abstract here: [sda_Drw] under the kernel table, the EMPTY
             set under Bare.  Nothing below looks inside it. ---- *)
      iDestruct (sda_slot_acc (CID := CID) kt (DfracOwn 1) mst0 MENVCFG_S
                   pmar0 eq_refl HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Htr Hms Hpriv Hmenv Hpma Hhtif Hmisa")
        as (SD satp0 tlbv pcfg paddr)
        "(%Hdisj & %Hsub & %Hsok & %Hpok & Htrobl & Hrw & Hro & HRes & Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      iAssert (sr_swp_res (strans_regime (CID := CID))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4,
                            Regidx rd)))
        with (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4
                (Regidx rd)).
      assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1) (zeros' 64)
                    = pa) by (rewrite Lpin_rs1; reflexivity).
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
      2:{ iApply (swp_execute_AMOSWAP_S_ex_mode (CID := CID)
                    SD sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    rs2 rs1 rd (tp_pin (CID := CID) m) (pa_of ppn pa)
                    pmar0 pcfg paddr
                    (fun _ => Tc)
                    (fun bytes => Tc ∗
                       (⌜bytes = (mword_of_int 0 : mword 32)⌝ ∗
                          locked_pre γl h0 ∗ R
                        ∨ ⌜neq_vec (sign_extend' 64 bytes) zero_reg = true⌝))%I
                    (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    ltac:(rewrite sda_rs_mst; exact HMXR)
                    ltac:(rewrite sda_rs_menv; vm_compute; reflexivity)
                    ltac:(rewrite sda_rs_mst; exact HSXL)
                    ltac:(rewrite sda_rs_satp;
                          exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok))
                    ltac:(rewrite sda_rs_mst;
                          exact (effectivePrivilege_mprv0
                                   (Atomic (AMOSWAP, true, false, Data, Data))
                                   _ Supervisor HMPRV))
                    HA Hord HR HW Hcov (pma_all_ram Hpma_all) Hkd0
                    ltac:(rewrite Hea; exact Halign4)
                    (pa_aligned_div ppn pa 4 ltac:(lia) ltac:(exists 1024; lia)
                       Halign4)
                    Hrd
                    with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HTc] []").
          - (* the data translation, ALREADY DISCHARGED at [SD] by the
               accessor -- this leaf never learns which arm it is on *)
            iIntros "Hfrag HRes Hrw Hro".
            rewrite Hea.
            iApply ("Htrobl" $! KT0 (Atomic (AMOSWAP, true, false, Data, Data))
                      KP_rw pa ppn rr with "[%] [%] [%] [%] [%] Hwit Hk Hcert
                      Hfrag HRes Hrw Hro").
            + apply _.
            + exact (or_intror (or_intror (or_intror
                       (ex_intro _ true (ex_intro _ false eq_refl))))).
            + exact eq_refl.
            + exact Hcan.
            + exact Hid.
          - (* the exclusive READ node: open the invariant, read, close *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod ("Hlock" $! ⊤ Tc with "[%] [] HTc")
              as "(Hbody & HTc & [Hcl _])"; [solve_ndisj | iApply Href |].
            iDestruct "Hbody" as (v1 st1) "(>Hw & Hcpu & Hg & Hbr)".
            iEval (rewrite /lock_word -Hpalk /word4_pointsto) in "Hw".
            iDestruct "Hw" as "[%Hal1 Hb]".
            iDestruct (s_mem_chunk sigma pa pa 0 4 4 (nth_byte v1) ppn
                         (DfracOwn 1) ltac:(lia) ltac:(lia) (fun k => eq_refl)
                         Hoff Hcan with "Hmem Hk Hb") as %(Hbf & _ & _ & _).
            iMod ("Hcl" with "[Hb Hcpu Hg Hbr]") as "_".
            { iNext. iExists v1, st1. iFrame "Hcpu Hg Hbr".
              rewrite /lock_word -Hpalk /word4_pointsto. iFrame "Hb".
              iPureIntro. exact Hal1. }
            iMod (fupd_mask_subseteq ∅) as "Hclm"; [set_solver|].
            iModIntro. iExists v1.
            iSplitR.
            { iPureIntro. intros j Hj. apply Hbf. exact Hj. }
            iNext. iMod "Hclm" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev HTc".
          - (* the conditional WRITE node *)
            iIntros (bytes) "HTc". iIntros (sigma) "%Hrb Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod ("Hlock" $! ⊤ Tc with "[%] [] HTc")
              as "(Hbody & HTc & [Hcl _])"; [solve_ndisj | iApply Href |].
            iDestruct "Hbody" as (v2 st2) "(>Hw & >Hcpu & >Hg & Hbr)".
            iEval (rewrite /lock_word -Hpalk /word4_pointsto) in "Hw".
            iDestruct "Hw" as "[%Hal2 Hb]".
            iDestruct (s_mem_chunk sigma pa pa 0 4 4 (nth_byte v2) ppn
                         (DfracOwn 1) ltac:(lia) ltac:(lia) (fun k => eq_refl)
                         Hoff Hcan with "Hmem Hk Hb") as %(Hbf2 & _ & _ & _).
            assert (Hv2 : v2 = bytes).
            { pose proof (read_bytes_of_bytes sigma.(mem) (pa_of ppn pa) 4 v2
                            Hbf2) as Hr2.
              rewrite Hr2 in Hrb. by injection Hrb. }
            subst v2.
            iDestruct (word4_pointsto_intro pa (DfracOwn 1) bytes Hal2
                         with "Hb") as "Hw".
            iMod (word4_pointsto_write_c sigma.(mem) pa ppn bytes
                    (amoswap_stored (rget m rs2)) Hcan Hoff
                    with "Hk Hmem Hw") as "[Hmem Hw]".
            iAssert (|={⊤ ∖ ↑lockN, ⊤}=>
                       (⌜bytes = (mword_of_int 0 : mword 32)⌝ ∗
                          locked_pre γl h0 ∗ ▷ R
                        ∨ ⌜neq_vec (sign_extend' 64 bytes) zero_reg = true⌝))%I
              with "[Hw Hcpu Hg Hbr Hcl]" as ">Hpay".
            { iDestruct "Hbr" as "[(>%Hnone & >%Hw0 & >Hfrag2 & HR) |
                                   (>%Hsome & >%Hwnz)]".
              - subst st2.
                iMod (lock_take γl h0 with "Hg Hfrag2") as "[Hg Hpre]".
                iMod ("Hcl" with "[Hw Hcpu Hg]") as "_".
                { iNext. iExists (amoswap_stored (rget m rs2)),
                                 (Some (h0, false)).
                  iFrame "Hg".
                  iSplitL "Hw";
                    [ rewrite /lock_word -Hpalk; iExact "Hw" | ].
                  iSplitL "Hcpu";
                    [ rewrite lk_cpu_res_win -lk_cpu_res_free; iExact "Hcpu" | ].
                  iRight. iPureIntro. split; [discriminate | exact Hstz]. }
                iModIntro. iLeft. iFrame "Hpre HR". iPureIntro. exact Hw0.
              - iMod ("Hcl" with "[Hw Hcpu Hg]") as "_".
                { iNext. iExists (amoswap_stored (rget m rs2)), st2.
                  iFrame "Hg Hcpu".
                  iSplitL "Hw";
                    [ rewrite /lock_word -Hpalk; iExact "Hw" | ].
                  iRight. iPureIntro. split; [exact Hsome | exact Hstz]. }
                iModIntro. iRight. iPureIntro. exact Hwnz. }
            iMod (fupd_mask_subseteq ∅) as "Hclm"; [set_solver|].
            iModIntro. iNext. iMod "Hclm" as "_". iModIntro.
            rewrite Lpin_rs2.
            iFrame "Hreg Hmem Hdev HTc Hpay". }
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (bytes) "(Hfile & Hland)".
      iDestruct "Hland" as (rsf)
        "(%Hshape & Hrw & Hro & HRes & HR2 & Hfrag)".
      iDestruct "HR2" as "[HTc Hpay]".
      iSplitR; [done|].
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (CID := CID)
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) SD ∗
                 hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 strans_res_at (CID := CID) satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tlbv. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                       pcfg paddr tlbv tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                       pcfg paddr tlbv tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                   (register_set tlb tvx
                      (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes") as
        "(Htr & Hms & Hpriv & Hmenv)".
      iExists (add_vec_int pc 4), mst0,
              (<[Regidx rd := regval_into_reg (amoswap_loaded bytes)]> m), n.
      iFrame "HPC HnPC".
      iSplitL "Hfrag"; [ iApply (resv_any_intro _ None with "Hfrag") | ].
      iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
        iPureIntro. split; assumption. }
      assert (Hsp : m !!! Regidx csp_rs1
                    = <[Regidx rd := regval_into_reg (amoswap_loaded bytes)]> m
                        !!! Regidx csp_rs1)
        by (symmetry; apply upd_ne; congruence).
      iSplitL "Htr Hstk Harm".
      { rewrite /sie_cap -Hsp. iFrame "Hstk Htr Harm Hwit". }
      iSplitL "Hfile".
      { iEval (rewrite (tp_pin_upd m rd
                          (regval_into_reg (amoswap_loaded bytes))
                          (rd_ok_tp _ Hrdok))) in "Hfile".
        iExact "Hfile". }
      iExists bytes. iFrame "HTc Hpay". iPureIntro. split_and!; reflexivity.
    - (* ---------------- THE CONTINUATION ---------------- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' Hpay".
      iDestruct "Hpay" as (w) "(-> & -> & -> & HTc & Hpay)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! w CID with "[%] HTc Hcg' Hpc' Hpay"). exact Hs.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block.  x10 (a0) is the *)
  (* register acquire/release actually hold the lock pointer in.            *)
  (* ------------------------------------------------------------------- *)
  Definition lock_srcok_pos_a0 : SrcOk (mword_of_int 10 : mword 5) := _.
  Fail Definition lock_srcok_neg : SrcOk Rtp := _.

End WpSconfLock.
