(* WpSconfMem.v -- the SIE-AGNOSTIC data-leaf layer (interrupt-sweep
   stage 5): the [sconf]+[sie_cap] twins of the width-8 RVC LOAD/STORE
   exemplars (WpSmodePtLeaves.v's [wp_cld_s_pt]/[wp_csd_s_pt]), over the
   agnostic funnel [wp_instr_s_sconf].

   The data-side translation runs through the regime-blind absorption
   [sr_absorb strans_regime] INSIDE the funnel's σf-callback: the
   callback threads the FOLDED translation slot [strans_inv] (as "Htr")
   through [strans_regime] with NO skolem-root open, effective-address
   transform comes from [sr_transform strans_regime], and the post-
   translate PMP/PMA facts come from [sr_absorb]'s [pmp_grant_facts]
   conclusion (mirroring the R-generic `_r` data leaves).  The config
   facts (MPRV/SXL/MXR/PMM) come from [sconf]'s bundled fact sets
   instead of eight per-call premises.  Spec cleanups made in this pass:
     - the redundant [let ea := .. let a8 := ea let pa := a8] alias
       chain collapses to a single binder -- named [ea], because it is
       the EFFECTIVE (pre-translation, VIRTUAL) address: the physical one
       is [pa_of ppn ea], formed separately inside the proof.  (Every leaf
       in this file that ABSORBS a translation now spells it [ea]; the
       thin wrappers below, and WpSconfLock.v's leaves, still say [pa] --
       same misnomer, renamed as they are next touched.  The binder is a
       [let] inside the statement, so the rename is invisible to callers.)
     - ALL config premises are gone (SIE is decided by the ghost, the
       rest ride in [sconf_ms_facts]/the menvcfg conjunct);
     - the STORE needs no rd-premises at all (it writes no register,
       so [sie_cap] is not even retargeted); the LOAD keeps
       [uint rd <> 0] and [rd_ok rd] (the latter replaces the old
       [rd <> csp_rs1] IN THE SAME SLOT: it also rules out tp, which the
       register file pins -- HartTp.v).
   The address / stored-value operands are read with [rget m rs]
   (correct at tp too) and stay OUTSIDE the [wp_next] lambda as [let]s:
   they are words computed from the ENTRY map, at the hart we came from,
   while every resource inside the lambda is about the hart we resume on.
   The remaining WpSmodePtMem widths (4/1, base widths) follow this
   template mechanically.                                                *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpLoad.
Require Import MinstretInv.
Require Import UserBits.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile HartTp WpNext.
Require Import RiscvExtras.
Require Import SmodeCorePt.
Require Import HartLift HartSpan HartSwp HartSMem.
Require Import WpSmodePtEngine.
Require Import KptGoodb.
Require Import WpIntrInv.
Require Import MemAccessGen.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import KptGhost.   (* kptN: the accessor-mask premise below *)
Require Import SRegime.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoMemPa.  (* [agent]/[pwmsg]/[bytemap]: the era log's vocabulary
                             (A6.58 -- the write node speaks it now) *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.


(* helper copies (Local in WpSmodePtMem.v). *)
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

Section WpSconfMem.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ------------------------------------------------------------------- *)
  (* c.ld rd, imm(rs1) -- width-8 RVC load.                               *)
  (* ------------------------------------------------------------------- *)
  Local Lemma avi0_mulw (width : Z) (a : mword 64) : add_vec_int a (0 * width) = a.
  Proof. change (0 * width)%Z with 0%Z. apply avi0. Qed.

  (* TIER-INDEXED through its bytes (sp-migration phase D): the [CurKtier]
     instance argument rides along, so every ambient spelling
     [wordw_pointsto width a dq w] is unchanged and an explicit-tier one is
     [wordw_pointsto (KTR := ktd) width a dq w]. *)
  (* LEDGER MEMBERS (tso-machine-flip.md §6 amendment A6.18, ratified): the
     rehearsal-era ruling made this window RAW because the only cost of a
     ctx datum was crossing a seal for nothing.  Post-flip the S-mode data
     nodes owe [Mobl_ram_plain] on a read and the append on a write, and
     NEITHER is payable from a flat cell -- so the datum carries its ledger
     residue.  THE CONTEXT IS THE SECTION'S AMBIENT [XI], so this is an
     invisible binder: every exported statement below is textually
     unchanged, and [own_context] arrives with the [sie_cap_gpr] they all
     already take (tso-port.md §0.13': it is a conjunct of
     [IntrDefs.sie_cap]). *)
  Definition wordw_pointsto `{KTR : !CurKtier} (width : Z) (a : Arch.pa) (dq : dfrac) (w : mword (8*width)) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     [∗ list] j ∈ seq 0 (Z.to_nat width),
        ctx_pointsto cur_ctx (pa_add a j) dq (nth_byte w j))%I.

  (* THE PAYOFF (A6.18): the 8-byte window simply IS the ↦₈ cell now -- no
     shim, no crossing, no continuation adapter.  Kept only so the wrappers
     that named it keep compiling; it is [reflexivity] up to [Z.to_nat]. *)
  Lemma wordw8_ctx `{KTR2 : !CurKtier} (a : Arch.pa)
      (dq : dfrac) (v : mword 64) :
    wordw_pointsto (KTR := KTR2) 8 a dq v
    ⊣⊢ ctx_word_pointsto (KTR := KTR2) cur_ctx a dq v.
  Proof.
    rewrite /wordw_pointsto ctx_word_pointsto_unfold.
    by change (Z.to_nat 8) with 8%nat.
  Qed.

  (* THE ADDRESS CLAIM, AND WHY THE ATOMIC-UPDATE FORMS TAKE IT.
     Per node, an access TRANSLATES before it reads, and the translation
     needs the window's claim -- its [ppn], canonicality, RAM-ness and tier
     pin -- while the atomic update is opened at the READ node, several
     nodes later.  A LINEAR atomic update cannot be peeked at and put back,
     so the claim (which is persistent, and says nothing about the VALUE)
     rides beside it.  Every caller has it: an owner of the window reads it
     off the points-to ([wordw_claim_of]), and an invariant-backed caller
     off one peek-open of its (persistent) accessor. *)
  (* THE BYTE'S CLAIM: [mem_pointsto] minus the physical ownership -- the
     mapping, canonicality, RAM-ness and the tier pin.  THE ONE LEMMA every
     translation side-condition is derived from ([mem_pointsto_claim]); the
     word form below is this at byte 0 plus the word's alignment. *)
  Definition mem_claim `{KTR : !CurKtier} (a : Arch.pa) : iProp Σ :=
    (∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗
       ⌜(uint a < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn a)⌝ ∗
       ⌜ktier_pin cur_ktier ppn a⌝)%I.

  Global Instance mem_claim_persistent `{KTR : !CurKtier} a :
    Persistent (mem_claim a).
  Proof. apply _. Qed.

  Lemma mem_pointsto_claim `{KTR : !CurKtier} (a : Arch.pa) (dq : dfrac) (b : bv 8) :
    a ↦ₘ{dq} b -∗ mem_claim a.
  Proof.
    iIntros "Hb".
    iDestruct (TsoCtx.ctx_pointsto_forget with "Hb") as "Hb".
    iDestruct (mem_pointsto_acc with "Hb")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & _ & _)".
    iExists ppn. iFrame "Hk". done.
  Qed.

  Definition wordw_claim `{KTR : !CurKtier} (width : Z) (a : Arch.pa) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗ mem_claim a)%I.

  Global Instance wordw_claim_persistent `{KTR : !CurKtier} width a :
    Persistent (wordw_claim width a).
  Proof. apply _. Qed.

  Lemma wordw_claim_of `{KTR : !CurKtier} (width : Z) (a : Arch.pa) (dq : dfrac)
      (w : mword (8*width)) :
    0 < width ->
    wordw_pointsto width a dq w -∗ wordw_claim width a.
  Proof.
    intros Hw0. iIntros "[%Hal Hb]".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hb") as "[Hb0 _]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iSplitR; [done|]. iApply (mem_pointsto_claim with "Hb0").
  Qed.

  Local Lemma write_bytes_1 (mm : _) (pa : Arch.pa) (v : bv 8) :
    write_bytes mm pa 1 v = <[pa := nth_byte v 0]> mm.
  Proof. unfold write_bytes. change (N.to_nat 1) with 1%nat. cbn [seq foldr]. rewrite pa_add_0. reflexivity. Qed.

  Local Lemma nth_byte0_id (v : bv 8) : nth_byte v 0 = v.
  Proof.
    apply bv_eq. rewrite nth_byte_unsigned.
    change (Z.of_N (8 * N.of_nat 0)) with 0%Z. rewrite Z.shiftr_0_r.
    apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ v) as Hr.
    unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 8)%Z with 256%Z in Hr. change (2 ^ 8)%Z with 256%Z. lia.
  Qed.

  (* claim-keyed generic window write (uniform-claims: replaces the old
     physical [wordw_pointsto_write]).  Given the base [KP_rw] claim of a
     non-straddling VA window it overwrites the ACTUAL translated physical
     bytes at [pa_of ppn a] in step with the heap.  Width-agnostic via
     [s_win_write]. *)
  (* A6.58: THE LEDGER APPEND, at the generic width.  Two things changed
     under this wrapper and neither is a repair:

       - [wordw_pointsto]'s bytes ARE the context-indexed bytes already
         (A6.18's payoff, the definition three screens up), so the shim
         crossings the SC text had around the write ([ctx_buf_of_mem] /
         [ctx_buf_to_mem]) were IDENTITIES at this site and are simply
         gone -- which is A6.57's "identities now" theory holding exactly
         where the tier already moved, and nowhere else;

       - [SmodeCorePt.s_win_write] is GONE (A6.33): a store is one APPEND,
         so no value-changing law may move [gen_heap_interp] without
         [tso_interp_of] and the writer's [own_context] beside it.  Its
         successor [wordw_win_store_c] has exactly this shape, and
         [HartSMem.Wobl_ram] is what HANDS the bundle to the write node,
         so nothing new is demanded of the leaf's caller. *)
  (* A6.63'' THE CpuId RE-PARK (tso-port.md §0.20′, found by the M-leg lane
     on main and back-ported here BEFORE this file next compiles).
     [own_context] is CpuId-INDEXED, and this helper's callers run INSIDE
     [rename CID into CID0; iIntros (CID Hs)] -- the instruction obligation
     binds a FRESH CpuId and the capability's token is at THAT one, while
     typeclass resolution inside the section silently finds the SECTION
     instance [CID].  A section variable cannot be instantiated from inside
     its own section, so the helper takes its own binder.
     POST-FLIP IT IS NEEDED TWICE: it names the token's hart AND the
     appended message's AUTHOR ([hart_agent cpu_id]).  The failure mode is
     [iExact] refusing two terms that PRINT IDENTICALLY; only
     [Local Set Printing All] shows [@own_context Σ _ CID …] vs [… CID0 …]. *)
  Local Lemma wordw_pointsto_write_c `{KTR : !CurKtier} {CIDw : CpuId}
      (width : Z)
      (img : bytemap) (σ : mstate) (log : list pwmsg)
      (V : agent -> nat) (a : mword 64)
      (ppn : mword 44) (vold vnew : mword (8*width)) :
    0 < width ->
    (uint a < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec a 11 0) + width <= 4096)%Z ->
    kmap_at (svpn_of a) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) σ.(mem) -∗
    tso_interp_of riscv_eraGS img σ.(mem) log V -∗
    TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
    wordw_pointsto width a (DfracOwn 1) vold ==∗
    gen_heap_interp (hG:=riscv_memGS)
      (write_bytes σ.(mem) (pa_of ppn a) (Z.to_N width) vnew) ∗
    tso_interp_of riscv_eraGS img
      (write_bytes σ.(mem) (pa_of ppn a) (Z.to_N width) vnew)
      (log ++ [PWMsg (snap_of (pa_of ppn a) (Z.to_N width) vnew)
                 (hart_agent (@cpu_id CIDw))])%list
      (vstep (hart_agent (@cpu_id CIDw)) (V (hart_agent (@cpu_id CIDw)))
         (log ++ [PWMsg (snap_of (pa_of ppn a) (Z.to_N width) vnew)
                    (hart_agent (@cpu_id CIDw))])%list V) ∗
    TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
    wordw_pointsto width a (DfracOwn 1) vnew.
  Proof.
    intros Hw0 Hcan Hoff. iIntros "#Hk Hm Htso Hrun Hw".
    rewrite /wordw_pointsto.
    iDestruct "Hw" as "(%Hal & Hb)".
    assert (Hwn : N.to_nat (Z.to_N width) = Z.to_nat width)
      by apply Z_N_nat.
    iEval (rewrite -Hwn) in "Hb".
    iMod (wordw_win_store_c (CID := CIDw) (Z.to_N width) img σ log V a ppn vold vnew
            ltac:(pose proof (bv_unsigned_in_range _
                    (subrange_vec_dec a 11 0)) as [Hlo0 _];
                  rewrite Hwn; lia) Hcan
            ltac:(rewrite Hwn; apply Forall_forall; intros j Hj;
                  apply elem_of_list_In, elem_of_seq in Hj;
                  destruct Hj as [_ Hjw];
                  assert (Hjz : Z.of_nat j < width) by
                    (rewrite <- (Z2Nat.id width) by lia;
                     apply Nat2Z.inj_lt; exact Hjw);
                  lia)
            with "Hk Hm Htso Hrun Hb") as "(Hm & Htso & Hrun & Hb)".
    iModIntro. iFrame "Hm Htso Hrun".
    iEval (rewrite Hwn) in "Hb". iFrame "Hb". iPureIntro. exact Hal.
  Qed.

  (* A6.58: THE READ TWIN.  A6.36's overruling made every S-mode LOAD the
     PLAIN arm, so what a leaf owes is [HartSMem.Mobl_ram]'s VIEW-INDEXED
     family and not a flat [read_bytes] -- which is why [s_mem_chunk] no
     longer pays it here.  [SmodeCorePt.wordw_win_load_c] does, off the
     same window, and its conclusion is PURE: the window, the token and the
     interp bundle all survive, which is what lets an ATOMIC-UPDATE leaf
     run it inside the update and still hand the cell back. *)
  (* A6.63'': same CpuId re-park as the write helper above. *)
  Local Lemma wordw_pointsto_load_c `{KTR : !CurKtier} {CIDw : CpuId}
      (width : Z)
      (img : bytemap) (σ : mstate) (log : list pwmsg)
      (V : agent -> nat) (a : mword 64) (ppn : mword 44)
      (v : mword (8*width)) (dq : dfrac) :
    0 < width ->
    (uint a < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec a 11 0) + width <= 4096)%Z ->
    kmap_at (svpn_of a) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) σ.(mem) -∗
    tso_interp_of riscv_eraGS img σ.(mem) log V -∗
    TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
    wordw_pointsto width a dq v -∗
    ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
       tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
         (pa_of ppn a) (Z.to_N width) v⌝.
  Proof.
    intros Hw0 Hcan Hoff. iIntros "#Hk Hm Htso Hrun Hw".
    rewrite /wordw_pointsto. iDestruct "Hw" as "(%Hal & Hb)".
    assert (Hwn : N.to_nat (Z.to_N width) = Z.to_nat width)
      by apply Z_N_nat.
    iEval (rewrite -Hwn) in "Hb".
    iApply (wordw_win_load_c (KTR := KTR) (CID := CIDw) (Z.to_N width) img σ log V a ppn v dq
              Hcan
              ltac:(rewrite Hwn; apply Forall_forall; intros j Hj;
                    apply elem_of_list_In, elem_of_seq in Hj;
                    destruct Hj as [_ Hjw];
                    assert (Hjz : Z.of_nat j < width) by
                      (rewrite <- (Z2Nat.id width) by lia;
                       apply Nat2Z.inj_lt; exact Hjw);
                    lia)
              with "Hk Hm Htso Hrun Hb").
  Qed.

  (* THE WIDTH-1 WRITE WRAPPER IS GONE (A6.58).  It had NO caller -- the
     byte leaves go through [wordw_pointsto_write_c] at [width := 1] like
     every other width -- and it was stated over [s_win_write], the
     gen_heap-only law A6.33 deleted.  Reviving it would have meant
     re-deriving the ledger append for a shape nothing asks for. *)

  (* ------------------------------------------------------------------- *)
  (* The width/RVC-generic load in ATOMIC-UPDATE form: the cell need NOT   *)
  (* be owned by the caller across the step -- it is produced, and handed  *)
  (* back, inside the engine callback's own mask.  That is what lets a     *)
  (* lock leaf open [is_lock] around exactly this step (WpSconfLock.v);    *)
  (* [wp_load_s_sconf_gen] below is the trivial instance in which the      *)
  (* caller already owns the cell.                                         *)
  (* The loaded word [v] is quantified OUTSIDE the [wp_next] hart binder:  *)
  (* it is a word, not a hart-indexed resource, so a consumer introduces   *)
  (* it first ([iIntros (v CID1 Hs1) "..."]) and the engine discharges     *)
  (* both quantifiers in one [iApply ... $! v cpu_id].                     *)
  (* ------------------------------------------------------------------- *)
  (* ==================================================================== *)
  (* THE READ-SIDE SIDE CONDITION OF EVERY LEAF IN THIS FILE, AND WHY IT   *)
  (* IS A CLASS AND NOT A PREMISE.  Read this once; the leaves below just  *)
  (* point back here.                                                     *)
  (*                                                                      *)
  (* Every memory leaf computes its effective address from a CALLER-CHOSEN *)
  (* base register, as [rget m rs1] -- a lookup in [tp_pin m] (HartTp.v),  *)
  (* so the address as spelled depends on the ambient hart at exactly one  *)
  (* register, rs1 = tp.  A store additionally reads its DATA register the *)
  (* same way, [rget m rs2].  Both words are computed from the ENTRY map,  *)
  (* at the hart we came from, and both appear again INSIDE the [wp_next]  *)
  (* lambda, where the resource is about the hart we resume on.  Today the *)
  (* funnel's σ-callback is instantiated at the entry hart so the two      *)
  (* coincide; once that callback moves inside [WpNext.wp_next] the        *)
  (* obligation arrives at the hart the trap returned TO and the two agree *)
  (* only away from tp.  [IntrDefs.SrcOk] is that side condition.          *)
  (*                                                                      *)
  (* WHY A CLASS: a store writes no register at all, so it has NO pure     *)
  (* premises and hence no [rd_ok]/[ops_ok] slot whose MEANING could be    *)
  (* widened for free; and a load's [rd_ok] slot is about the DESTINATION, *)
  (* not the base.  An ordinary premise would therefore change ARITY at    *)
  (* every one of these leaves' references (~640 for [wp_csdsp_s_sconf]    *)
  (* alone), each needing a positional [ltac:(...)] in the right place.    *)
  (* An implicit instance argument shifts no positional argument, so the   *)
  (* whole family converts with ZERO call-site churn.                      *)
  (*                                                                      *)
  (* WHY NOT [ops_ok]: [ops_ok]'s source conjuncts are [src_ok b rs], i.e. *)
  (* guarded on [b = true].  An address must be hart-independent at        *)
  (* [b = true] too, so the guard buys nothing here, and these leaves have *)
  (* no slot to put it in anyway.  The two shapes coexist deliberately.    *)
  (*                                                                      *)
  (* THE STATEMENTS STAY SPELLED [rget m rs]. Respelling them hart-free as *)
  (* [m !!! Regidx rs] -- the literal reading of: make the premise         *)
  (* hart-independent -- was MEASURED and rejected: it breaks 99 consumer  *)
  (* files, because callers normalise the address/value with [rget]-shaped *)
  (* rewrites ([rgne], [rewrite Hlk]) that then have nothing to match.  So *)
  (* the class carries the side condition and the SPELLING does not move;  *)
  (* the reconciliation happens INSIDE each proof, in one line, via        *)
  (* [IntrDefs.src_ok_rget_indep].                                         *)
  (*                                                                      *)
  (* THAT ONE LINE IS ALSO THE LEAF'S WIRING CHECK, so do not delete it as *)
  (* an unused hypothesis: it names the register the statement reads, so a *)
  (* class accidentally attached to the wrong parameter fails to typecheck *)
  (* HERE instead of shelving silently at some consumer's [Qed].  (The     *)
  (* [exact]-shaped one-line wrappers below need no such line: a direct    *)
  (* application reports an unresolvable instance immediately, and it is   *)
  (* only inside a tactic-driven [iApply] that the failure is shelved.)    *)
  (* ==================================================================== *)
  (* ==================================================================== *)
  (* THE TIER SHAPE OF EVERY LEAF IN THIS FILE (sp-migration design §4/§5). *)
  (* [ktd] is the DATUM's tier, the section's [kt] the ACCESSING HART's --  *)
  (* the hart's is the CAPABILITY's, because a leaf drives the access with  *)
  (* the [sie_cap_gpr kt] it already consumes.  [KtierLe ktd kt] is the     *)
  (* whole access condition, and it sits at the END of the binder telescope *)
  (* so nothing before it can over-constrain the datum's tier.  There is NO *)
  (* separate witness premise: [sie_cap]'s fourth conjunct IS               *)
  (* [sr_ktier_wit strans_regime kt], delivered by the funnel's σ-callback  *)
  (* AT THE REBOUND HART, so no hart-crossing step is needed either.  At    *)
  (* KT0 the datum's own identity pin discharges admissibility              *)
  (* ([sr_adm_id]); at KT1 the regime's all-claims witness does             *)
  (* ([sr_absorb_wit]); both go through [SRegime.sr_absorb_ktier].          *)
  (* TIER-PRESERVING: the datum comes back at [ktd].                        *)
  (*                                                                        *)
  (* WHAT [ktd] DEFAULTS TO AT A CALL SITE: [kt].  Nothing determines the   *)
  (* datum's tier when the datum premise is handed over as a BRACKET, so    *)
  (* instance search closes [KtierLe ?ktd kt] eagerly with [ktier_le_refl]  *)
  (* -- see the note on the instances in Ktier.v, which also records why    *)
  (* neither [Hint Mode] nor a pure premise is a workable alternative.      *)
  (* That default is the frame slots' tier, so a prologue/epilogue site     *)
  (* needs no annotation; a datum at a DIFFERENT tier (static image data    *)
  (* under a tier-generic hart) says so with [(ktd := cur_ktier)].          *)
  (* ==================================================================== *)
  (* ==================================================================== *)
  (* THE DATUM IS A PARAMETER (tso-machine-flip.md A6.74 §(3), as amended  *)
  (* by A6.77): the leaf below is [wp_load_s_sconf_au] with its datum      *)
  (* premise abstracted and the ONE obligation discharge it performs made  *)
  (* a premise.  It exists because M4's three lock reads discharge by      *)
  (* THREE different routes -- the holder by [ledger_vis_own], the         *)
  (* non-holder by the racy kit, the free path by image totality -- and    *)
  (* because a cell living in a SHARED invariant cannot be at the          *)
  (* reader's ambient ξ at all, which is what [WpLock.lk_cpu_res]'s ∃ is   *)
  (* the admission of.                                                     *)
  (*                                                                      *)
  (* IT IS A GENERALISATION IN PLACE, NOT A COPY.  A6.74 priced this as a  *)
  (* sibling leaf ("~250 lines of the hazard file"); the measurement that  *)
  (* replaces that estimate is that the whole ctx-specific content of the  *)
  (* proof is ONE [iAssert] (the [wordw_pointsto_load_c] call), so the     *)
  (* datum abstracts with one new binder, one new premise and one edited   *)
  (* tactic.  [wp_load_s_sconf_au] survives BELOW as a wrapper with its    *)
  (* statement character-identical, so none of its callers move.          *)
  (*                                                                      *)
  (* [Hload]'s conclusion is PURE, which is what lets it take the caller's *)
  (* [own_context] without consuming it (the proof mode keeps every        *)
  (* hypothesis handed to a pure assertion -- the same property            *)
  (* [WpSconfLock]'s evidence premises rely on).  A phys-datum instance    *)
  (* simply ignores that argument: the ledger tier needs no token.         *)
  (* ==================================================================== *)
  Lemma wp_load_s_sconf_au_dat {ktd : ktier} (width : Z) (c uns : bool) (pc : mword 64) (rd rs1 : mword 5)
      `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (ext : mword (8*width) -> mword 64)
      (* [dqm] is GONE from this one: the datum is [Dat] now, so a fraction
         would be an uninferrable implicit.  The wrapper below keeps it. *)
      (Ψ : mword (8*width) -> iProp Σ) (Em : coPset) (b : bool) `{!KtierLe ktd kt}
      (Dat : mword (8*width) -> iProp Σ) :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    (* the vmem level hands back the value itself now, not the split
       accumulator, so the caller's extension is just [extend_value] *)
    (forall v : mword (8*width), extend_value uns v = ext v) ->
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    (* [Em] is the caller's inner mask; the kernel-table accessor is opened
       inside the translation node's own mask now, so this premise is what a
       supplier already proves by [solve_ndisj] and nothing here needs. *)
    ↑kptN ⊆ Em ->
    (* THE LOAD OBLIGATION, AS A PREMISE.  One leaf, every route; nothing
       below [gstate] reaches the client, exactly as A6.72's barrier-leaf
       rule requires. *)
    (forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
            (V : agent -> nat) (ppn : mword 44) (v : mword (8*width)),
       (* the address facts the CLAIM yields inside the leaf, handed on so a
          supplier that needs them (the ctx tower's does) has them *)
       (uint ea < 274877906944)%Z ->
       (bv_unsigned (subrange_vec_dec ea 11 0) + width <= 4096)%Z ->
       kmap_at (svpn_of ea) ppn KP_rw -∗
       gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
       tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
       TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
       Dat v -∗
       ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
          tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
            (pa_of ppn ea) (Z.to_N width) v⌝) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, uns, width)) -∗
    wordw_claim (KTR := ktd) width ea -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ v : mword (8*width),
       Dat v ∗ (Dat v ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v)) -∗
    ( ∀ v : mword (8*width),
      wp_next b p (fun (CID : CpuId) =>
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ext v)]> m) n b p -∗
        pc_is (add_vec_int pc (if c then 2 else 4)) -∗
        Ψ v -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain Hext ea Hrd Hrdok HkptEm Hload.
    rdok_split Hrdok.
    iIntros "Hcg Hpc #Hinstr #Hclaim HAU Hcont".
    iDestruct "Hclaim" as "[%Hpalign Hcl2]".
    iDestruct "Hcl2" as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid)".
    assert (Halign : is_aligned_vaddr (Virtaddr ea) width = true) by exact Hpalign.
    pose proof (off_bound_div ea width Hw0 Hwdvd Halign) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    assert (Hoff' : (bv_unsigned (subrange_vec_dec ea 11 0) + Z.of_nat (Z.to_nat width) <= 4096)%Z)
      by (rewrite Z2Nat.id; [ exact Hoff | lia ]).
    iApply (wp_instr_s_sconf m n b b pc c
              (LOAD (imm, Regidx rs1, Regidx rd, uns, width))
              (fun (_CIDx : CpuId) npc _ms' m' n' =>
                 ∃ v : mword (8*width),
                   ⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                   ⌜m' = <[Regidx rd := regval_into_reg (ext v)]> m⌝ ∗
                   ⌜n' = n⌝ ∗ Ψ v)%I
              with "Hcg Hpc Hinstr [HAU Hcont]").
    iNext.
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HAU".
    - (* ---------------- THE INSTRUCTION ---------------- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
        by exact (src_ok_rget_indep m rs1 CID CID0).
      iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
          Hmdl & Hmenv)".
      pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                          HMPP & HTVM).
      (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
         [WpIntrInv.sda_slot_acc] below, the one place the two translation
         arms are told apart. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & Hctx & #Htc & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
             [SD] under the kernel table, the EMPTY set under Bare. ---- *)
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
      (* the tower's lookups, POSED: an [ltac:] in argument position runs
         before the application's implicits are solved (durable-notes). *)
      pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
      pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
      pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
      assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
              = true) by (rewrite Lmst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
              = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
      assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
              by (rewrite Lmst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
              = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
              by (rewrite Lsatp;
                  exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
      assert (Lep : effectivePrivilege (Load Data) (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
              = returnM Supervisor)
              by (rewrite Lmst;
                  exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
      change (execute (LOAD (imm, Regidx rs1, Regidx rd, uns, width)))
        with (execute_LOAD imm (Regidx rs1) (Regidx rd) uns width).
      assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                      (sign_extend' 64 imm) = ea)
        by (rewrite Lpin_rs1; reflexivity).
      (* A6.58: [Hctx] goes DOWN to the read node.  Even a plain LOAD is
         paid from the running context's own bound now
         ([wordw_pointsto_load_c]), so the token travels with the access
         and comes back inside the leaf's payload; [sie_cap] is rebuilt
         from it in the post exactly as before. *)
      (* A6.64 THIS SENTENCE ONCE DID NOT ELABORATE AT ALL.  KEEP THE
         THREE PAYLOAD SPELLINGS BELOW IN AGREEMENT.

         History, because the fix is not what it looks like: this [iApply]
         was killed at 35, 60 and 57 minutes across three sessions, while
         the 195 sentences before it cost 4.57 s in total.  Two diagnoses
         were wrong -- it is NOT that the payload was a duplicated lambda
         (naming it changed nothing), and NOT that the name had to be rigid
         ([clearbody] changed nothing; the RSS plateau matched the
         transparent run to 0.016%).

         THE ACTUAL CAUSE: the payload was spelled DIFFERENTLY at three
         positions of the same forty-argument application --
           * the leaf's [R]           : [Psic] (= own_context ∗ Ψ bs)
           * the obligation argument  : [Mobl_ram_ex … Psic]
           * the NODE argument        : [swp_read_ram_node_w_ex … Ψ]
         The node still handed the PRE-FLIP payload, so unification had to
         discover the relation between [Ψ] and [own_context ∗ Ψ] through
         forty arguments, and diverged.  With the three in agreement the
         application elaborates in 0.042 s and the file compiles in 4.74 s.

         THE RULE: when threading the token into a leaf, move the NODE
         argument too.  A6.58's recipe does not say so, so every S-mode
         leaf that took the token carries this hazard until its node is
         checked.

         The [set] below is kept because it makes the three spellings easy
         to compare by eye -- not because naming is the fix.  The
         [iPoseProof]/[iApply] split is kept for the same reason: it bills
         elaboration separately from goal unification, which is the only
         thing that localises this failure. *)
      (* A6.63'': the token in the leaf's payload is at the FRESH CpuId the
         obligation bound, not the section's -- see the helpers above. *)
      set (Psic := (fun bs => TsoCtx.own_context (CID := CID) TsoCtx.cur_ctx ∗ Ψ bs)%I).
      assert (HPsic : Psic
                = (fun bs => TsoCtx.own_context (CID := CID) TsoCtx.cur_ctx ∗ Ψ bs)%I)
        by reflexivity.
      clearbody Psic.
      (* A6.63''' THE SPLIT SAID *ELABORATION*, NOT GOAL UNIFICATION -- the
         [iPoseProof] alone, which never looks at the goal, is what runs
         forever.  So the remaining suspect is the OTHER computed argument:
         [Mobl_ram_ex] applied to [Psic].  Hoist it too, for the same
         rigid-head reason. *)
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
      2:{ (* A6.63' THE SPLIT EXPERIMENT (see the note above this proof).
             [iPoseProof] elaborates the forty-argument application;
             [iApply] then only has to unify an already-built term with
             the goal.  [-time] bills the two sentences separately, which
             is the one measurement that says which half is the cost. *)
          iPoseProof (swp_execute_LOAD_ram_Sw_ex (CID := CID) width Hvw Hwdvd Huintw
                    SD sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    imm rs1 rd uns (tp_pin (CID := CID) m) (pa_of ppn ea)
                    pmar0 pcfg paddr
                    Psic
                    (Mobl_ram_ex width (pa_of ppn ea) Psic)
                    (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                          (sign_extend' 64 imm))
                       (Load Data)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                    Lep
                    HA Hord HR Hcov (pma_all_ram Hpma_all) Hkd0
                    ltac:(rewrite Hea; exact Halign)
                    (pa_aligned_div ppn ea width Hw0 Hwdvd Halign)
                    Hrd
                    (swp_read_ram_node_w_ex (CID := CID) width (pa_of ppn ea) Psic
                       Hvw (addr_is_ram_not_dev _ Hkd0))
                    ) as "Hleaf".
          iApply ("Hleaf" with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HAU Hctx]").
          - (* the data translation *)
            iIntros "Hfrag HRes Hrw Hro".
            rewrite Hea.
            (* already discharged at [SD] by the accessor -- this leaf
               never learns which arm it is on *)
            iApply ("Htrobl" $! ktd (Load Data) KP_rw ea ppn rr
                      with "[%] [%] [%] [%] [%] Hwit Hk Hcert Hfrag HRes
                      Hrw Hro").
            + apply _.
            + exact (or_intror (or_introl eq_refl)).
            + exact I.
            + exact Hcan.
            + exact Hid.
          - (* the RAM read node: the caller's atomic update, opened HERE.
               A6.58: the node receives the era's log bundle and hands it
               back UNCHANGED (a plain load moves no view, so [V] returns
               as [V]), and the obligation is now the view-indexed family
               [wordw_pointsto_load_c] pays. *)
            iIntros (sigma img log tv V) "%Htv Hsi Htso".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (fupd_mask_subseteq (⊤ ∖ ↑minstretN)) as "Hb1"; [set_solver|].
            iMod "HAU" as (v) "[Hbw Hcl]".
            (* A6.63'': the read obligation is at the FRESH CpuId too --
               [wordw_pointsto_load_c] now concludes at [@cpu_id CID], and
               the ambient spelling here would print identically while
               failing to unify (tso-port.md §0.20′). *)
            iAssert (⌜forall tvr : nat, (V (hart_agent (@cpu_id CID)) <= tvr)%nat ->
                       tso_read_bytes img log (hart_agent (@cpu_id CID)) tvr
                         (pa_of ppn ea) (Z.to_N width) v⌝)%I as %Hrb.
            { iApply (Hload CID img sigma log V ppn v Hcan Hoff
                        with "Hk Hmem Htso Hctx Hbw"). }
            iMod ("Hcl" with "Hbw") as "HPsi".
            iMod "Hb1" as "_".
            iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
            iModIntro. iExists v.
            iSplitR.
            { iPureIntro. intros tvr Hlo _. rewrite -Htv in Hlo.
              exact (Hrb tvr Hlo). }
            iNext. iMod "Hb2" as "_". iModIntro.
            (* [Psic] is RIGID (clearbody), so the ∗-shape has to be given
               back explicitly before the frame *)
            rewrite HPsic. cbn beta.
            iFrame "Hreg Hmem Hdev Htso Hctx HPsi". }
      (* the node has closed, so the payload goes back to its ∗-shape for
         the post's [iDestruct] pattern *)
      rewrite HPsic. cbn beta.
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (v) "(Hfile & Hland)".
      iDestruct "Hland" as (rsf)
        "(%Hshape & Hrw & Hro & HRes & Hany & [Hctx HPsi])".
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
      iExists (add_vec_int pc (if c then 2 else 4)), mst0,
            (<[Regidx rd := regval_into_reg (ext v)]> m), n.
      iFrame "HPC HnPC Hany".
      iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
      iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      iPureIntro. split; assumption. }
      assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (ext v)]> m
                      !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
      iSplitL "Htr Hstk Harm Hctx".
      { rewrite /sie_cap -Hsp. iFrame "Hstk Htr Harm Hctx Htc Hwit". }
      iSplitL "Hfile".
      { rewrite (Hext v).
      iEval (rewrite (tp_pin_upd m rd (regval_into_reg (ext v))
                        (rd_ok_tp _ Hrdok))) in "Hfile".
      iExact "Hfile". }
      iExists v. iFrame "HPsi". iPureIntro. split_and!; reflexivity.
    - (* ---------------- THE CONTINUATION ---------------- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' Hpay".
      iDestruct "Hpay" as (v) "(-> & -> & -> & HPsi)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! v CID with "[%] Hcg' Hpc' HPsi"). exact Hs.
  Qed.

  (* THE ORIGINAL, character-identical, as an instance of the above at the
     ctx word tower.  Its ~15 in-file wrappers and every consumer are
     untouched: the abstraction cost nothing at the surface. *)
  Lemma wp_load_s_sconf_au {ktd : ktier} (width : Z) (c uns : bool) (pc : mword 64) (rd rs1 : mword 5)
      `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (ext : mword (8*width) -> mword 64)
      (Ψ : mword (8*width) -> iProp Σ) (Em : coPset) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    0 < width -> width <= 8 ->
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    (forall v : mword (8*width), extend_value uns v = ext v) ->
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    ↑kptN ⊆ Em ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, uns, width)) -∗
    wordw_claim (KTR := ktd) width ea -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ v : mword (8*width),
       wordw_pointsto (KTR := ktd) width ea dqm v ∗
       (wordw_pointsto (KTR := ktd) width ea dqm v ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v)) -∗
    ( ∀ v : mword (8*width),
      wp_next b p (fun (CID : CpuId) =>
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ext v)]> m) n b p -∗
        pc_is (add_vec_int pc (if c then 2 else 4)) -∗
        Ψ v -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain Hext ea Hrd Hrdok HkptEm.
    exact (wp_load_s_sconf_au_dat (ktd := ktd) width c uns pc rd rs1 imm m n ext Ψ Em b
             (wordw_pointsto (KTR := ktd) width ea dqm)
             Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain Hext Hrd Hrdok HkptEm
             (fun CIDw img sigma log V ppn v Hcan Hoff =>
                wordw_pointsto_load_c (KTR := ktd) (CIDw := CIDw) width img sigma
                  log V ea ppn v dqm Hw0 Hcan Hoff)).
  Qed.

  (* ==================================================================== *)
  (* THE VALUE-UNKNOWN LOAD (A6.78), the second of the datum-parametric   *)
  (* pair.                                                                *)
  (*                                                                     *)
  (* [wp_load_s_sconf_au_dat] NAMES the value: its atomic update hands    *)
  (* over [∃ v, Dat v ∗ …] and [Hload] then owes                          *)
  (* "the read returns THAT v at every reachable view".  For M4's two     *)
  (* racy lock reads -- [holding()]'s [lk->cpu] by a NON-holder, and the  *)
  (* free-path read of the lock word -- there is no such [v]: the AU is   *)
  (* built by the caller before the machine state is in sight, so a value *)
  (* chosen there cannot be the one a drain-free view returns.  A6.77     *)
  (* recorded that the [_dat] leaf serves "all three routes"; measured,   *)
  (* it serves the HOLDER route only, and the other two need this leaf.   *)
  (*                                                                     *)
  (* SO THE EXISTENTIAL MOVES INSIDE THE VIEW QUANTIFIER, exactly as      *)
  (* [HartSMem.Mobl_ram_exv] does one tier down (A6.74 §(1) built that    *)
  (* lane and it had no consumer until now): the client hands over a      *)
  (* value-INDEPENDENT resource [Res], owes a PREDICATE [P] good at every *)
  (* view, and the continuation learns [⌜P v⌝] about the word the machine *)
  (* actually returned.  [T] is likewise value-independent -- a           *)
  (* value-indexed post would have to be chosen before the step it is     *)
  (* about.                                                              *)
  (*                                                                     *)
  (* NO NEW ENGINE.  [swp_execute_LOAD_ram_Sw_ex] takes its [Rr] and its  *)
  (* obligation as ARGUMENTS, and [Mobl_ram_exv]'s node post is the [_ex] *)
  (* one at [Rr := fun bs => ⌜P bs⌝ ∗ R] -- the same term, since [∗]      *)
  (* associates right.  What changes here is three arguments and four     *)
  (* tactics; the other ~300 sentences are [_dat]'s verbatim.            *)
  (* ==================================================================== *)
  Lemma wp_load_s_sconf_au_exv {ktd : ktier} (width : Z) (c uns : bool) (pc : mword 64) (rd rs1 : mword 5)
      `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (ext : mword (8*width) -> mword 64)
      (* NO [dqm] and NO value-indexed [Ψ]: the datum is a value-INDEPENDENT
         resource [Res] and what the continuation learns about the word is a
         PREDICATE.  A fraction, or a [Ψ] chosen before the step, would be
         exactly the shape this leaf exists to avoid. *)
      (Em : coPset) (b : bool) `{!KtierLe ktd kt}
      (P : mword (8*width) -> Prop) (Res T : iProp Σ) :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    (* the vmem level hands back the value itself now, not the split
       accumulator, so the caller's extension is just [extend_value] *)
    (forall v : mword (8*width), extend_value uns v = ext v) ->
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    (* [Em] is the caller's inner mask; the kernel-table accessor is opened
       inside the translation node's own mask now, so this premise is what a
       supplier already proves by [solve_ndisj] and nothing here needs. *)
    ↑kptN ⊆ Em ->
    (* THE LOAD OBLIGATION, AS A PREMISE -- AND THE [∃ v] IS INSIDE THE
       [∀ tvr], which is the whole difference from [_dat].  A racy cell's
       reader cannot name the word: what it can name is a predicate the word
       satisfies at EVERY view the machine's drain may choose. *)
    (forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
            (V : agent -> nat) (ppn : mword 44),
       (* the address facts the CLAIM yields inside the leaf, handed on so a
          supplier that needs them (the ctx tower's does) has them *)
       (uint ea < 274877906944)%Z ->
       (bv_unsigned (subrange_vec_dec ea 11 0) + width <= 4096)%Z ->
       kmap_at (svpn_of ea) ppn KP_rw -∗
       gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
       tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
       TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
       Res -∗
       ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
          exists v : mword (8*width),
            tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
              (pa_of ppn ea) (Z.to_N width) v /\ P v⌝) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, uns, width)) -∗
    wordw_claim (KTR := ktd) width ea -∗
    (|={⊤ ∖ ↑minstretN, Em}=> Res ∗ (Res ={Em, ⊤ ∖ ↑minstretN}=∗ T)) -∗
    ( ∀ v : mword (8*width),
      wp_next b p (fun (CID : CpuId) =>
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ext v)]> m) n b p -∗
        pc_is (add_vec_int pc (if c then 2 else 4)) -∗
        ⌜P v⌝ -∗ T -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain Hext ea Hrd Hrdok HkptEm Hload.
    rdok_split Hrdok.
    iIntros "Hcg Hpc #Hinstr #Hclaim HAU Hcont".
    iDestruct "Hclaim" as "[%Hpalign Hcl2]".
    iDestruct "Hcl2" as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid)".
    assert (Halign : is_aligned_vaddr (Virtaddr ea) width = true) by exact Hpalign.
    pose proof (off_bound_div ea width Hw0 Hwdvd Halign) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    assert (Hoff' : (bv_unsigned (subrange_vec_dec ea 11 0) + Z.of_nat (Z.to_nat width) <= 4096)%Z)
      by (rewrite Z2Nat.id; [ exact Hoff | lia ]).
    iApply (wp_instr_s_sconf m n b b pc c
              (LOAD (imm, Regidx rs1, Regidx rd, uns, width))
              (fun (_CIDx : CpuId) npc _ms' m' n' =>
                 ∃ v : mword (8*width),
                   ⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                   ⌜m' = <[Regidx rd := regval_into_reg (ext v)]> m⌝ ∗
                   ⌜n' = n⌝ ∗ ⌜P v⌝ ∗ T)%I
              with "Hcg Hpc Hinstr [HAU Hcont]").
    iNext.
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HAU".
    - (* ---------------- THE INSTRUCTION ---------------- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
        by exact (src_ok_rget_indep m rs1 CID CID0).
      iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
          Hmdl & Hmenv)".
      pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                          HMPP & HTVM).
      (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
         [WpIntrInv.sda_slot_acc] below, the one place the two translation
         arms are told apart. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & Hctx & #Htc & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
             [SD] under the kernel table, the EMPTY set under Bare. ---- *)
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
      (* the tower's lookups, POSED: an [ltac:] in argument position runs
         before the application's implicits are solved (durable-notes). *)
      pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
      pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
      pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
      assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
              = true) by (rewrite Lmst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
              = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
      assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
              by (rewrite Lmst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
              = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
              by (rewrite Lsatp;
                  exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
      assert (Lep : effectivePrivilege (Load Data) (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
              = returnM Supervisor)
              by (rewrite Lmst;
                  exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
      change (execute (LOAD (imm, Regidx rs1, Regidx rd, uns, width)))
        with (execute_LOAD imm (Regidx rs1) (Regidx rd) uns width).
      assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                      (sign_extend' 64 imm) = ea)
        by (rewrite Lpin_rs1; reflexivity).
      (* A6.58: [Hctx] goes DOWN to the read node.  Even a plain LOAD is
         paid from the running context's own bound now
         ([wordw_pointsto_load_c]), so the token travels with the access
         and comes back inside the leaf's payload; [sie_cap] is rebuilt
         from it in the post exactly as before. *)
      (* A6.64's FORTY-ARGUMENT ELABORATION HAZARD LIVES IN THIS
         SENTENCE -- see [wp_load_s_sconf_au_dat] above for the full
         history and the measurement.  The rule it leaves is the one the
         next block obeys: keep the leaf's [Rr], the OBLIGATION argument
         and the NODE argument spelled in agreement, and move the node
         when the payload moves. *)
      (* A6.63's THREE-SPELLINGS RULE, at the exv shape: the engine's [Rr]
         is [fun bs => ⌜P bs⌝ ∗ Rex] and the node/obligation take [P] and
         [Rex] SEPARATELY, so what must be rigid is [Rex] -- making [Rr]
         itself rigid would stop the node's post from unifying with the
         engine's slot. *)
      set (Rex := (TsoCtx.own_context (CID := CID) TsoCtx.cur_ctx ∗ T)%I).
      assert (HRex : Rex
                = (TsoCtx.own_context (CID := CID) TsoCtx.cur_ctx ∗ T)%I)
        by reflexivity.
      clearbody Rex.
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
      2:{ (* A6.63' THE SPLIT EXPERIMENT (see the note above this proof).
             [iPoseProof] elaborates the forty-argument application;
             [iApply] then only has to unify an already-built term with
             the goal.  [-time] bills the two sentences separately, which
             is the one measurement that says which half is the cost. *)
          iPoseProof (swp_execute_LOAD_ram_Sw_ex (CID := CID) width Hvw Hwdvd Huintw
                    SD sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    imm rs1 rd uns (tp_pin (CID := CID) m) (pa_of ppn ea)
                    pmar0 pcfg paddr
                    (fun bs => (⌜P bs⌝ ∗ Rex)%I)
                    (Mobl_ram_exv width (pa_of ppn ea) P Rex)
                    (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                          (sign_extend' 64 imm))
                       (Load Data)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                    Lep
                    HA Hord HR Hcov (pma_all_ram Hpma_all) Hkd0
                    ltac:(rewrite Hea; exact Halign)
                    (pa_aligned_div ppn ea width Hw0 Hwdvd Halign)
                    Hrd
                    (swp_read_ram_node_w_exv (CID := CID) width (pa_of ppn ea) P Rex
                       Hvw (addr_is_ram_not_dev _ Hkd0))
                    ) as "Hleaf".
          iApply ("Hleaf" with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HAU Hctx]").
          - (* the data translation *)
            iIntros "Hfrag HRes Hrw Hro".
            rewrite Hea.
            (* already discharged at [SD] by the accessor -- this leaf
               never learns which arm it is on *)
            iApply ("Htrobl" $! ktd (Load Data) KP_rw ea ppn rr
                      with "[%] [%] [%] [%] [%] Hwit Hk Hcert Hfrag HRes
                      Hrw Hro").
            + apply _.
            + exact (or_intror (or_introl eq_refl)).
            + exact I.
            + exact Hcan.
            + exact Hid.
          - (* the RAM read node: the caller's atomic update, opened HERE.
               A6.58: the node receives the era's log bundle and hands it
               back UNCHANGED (a plain load moves no view, so [V] returns
               as [V]), and the obligation is now the view-indexed family
               [wordw_pointsto_load_c] pays. *)
            iIntros (sigma img log tv V) "%Htv Hsi Htso".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (fupd_mask_subseteq (⊤ ∖ ↑minstretN)) as "Hb1"; [set_solver|].
            iMod "HAU" as "[Hbw Hcl]".
            (* A6.63'': the read obligation is at the FRESH CpuId too --
               [wordw_pointsto_load_c] now concludes at [@cpu_id CID], and
               the ambient spelling here would print identically while
               failing to unify (tso-port.md §0.20′). *)
            iAssert (⌜forall tvr : nat, (V (hart_agent (@cpu_id CID)) <= tvr)%nat ->
                       exists v : mword (8*width),
                         tso_read_bytes img log (hart_agent (@cpu_id CID)) tvr
                           (pa_of ppn ea) (Z.to_N width) v /\ P v⌝)%I as %Hrb.
            { iApply (Hload CID img sigma log V ppn Hcan Hoff
                        with "Hk Hmem Htso Hctx Hbw"). }
            iMod ("Hcl" with "Hbw") as "HT".
            iMod "Hb1" as "_".
            iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
            iModIntro.
            iSplitR.
            { iPureIntro. intros tvr Hlo _. rewrite -Htv in Hlo.
              exact (Hrb tvr Hlo). }
            iNext. iMod "Hb2" as "_". iModIntro.
            (* [Rex] is RIGID (clearbody), so the ∗-shape has to be given
               back explicitly before the frame *)
            rewrite HRex.
            iFrame "Hreg Hmem Hdev Htso Hctx HT". }
      (* the node has closed, so the payload goes back to its ∗-shape for
         the post's [iDestruct] pattern.  [Rr] is a literal lambda here
         (see the note above the [set]), so the application still has to be
         beta-reduced before the pattern matches. *)
      rewrite HRex. cbn beta.
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (v) "(Hfile & Hland)".
      iDestruct "Hland" as (rsf)
        "(%Hshape & Hrw & Hro & HRes & Hany & %HPv & [Hctx HT])".
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
      iExists (add_vec_int pc (if c then 2 else 4)), mst0,
            (<[Regidx rd := regval_into_reg (ext v)]> m), n.
      iFrame "HPC HnPC Hany".
      iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
      iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      iPureIntro. split; assumption. }
      assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (ext v)]> m
                      !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
      iSplitL "Htr Hstk Harm Hctx".
      { rewrite /sie_cap -Hsp. iFrame "Hstk Htr Harm Hctx Htc Hwit". }
      iSplitL "Hfile".
      { rewrite (Hext v).
      iEval (rewrite (tp_pin_upd m rd (regval_into_reg (ext v))
                        (rd_ok_tp _ Hrdok))) in "Hfile".
      iExact "Hfile". }
      iExists v. iFrame "HT". iPureIntro. split_and!; try reflexivity.
      exact HPv.
    - (* ---------------- THE CONTINUATION ---------------- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' Hpay".
      iDestruct "Hpay" as (v) "(-> & -> & -> & %HPv & HT)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! v CID with "[%] Hcg' Hpc' [%] HT"); [exact Hs|exact HPv].
  Qed.
  (* The non-atomic instance: the caller owns the cell throughout.  Generic
     in BOTH the width and the extension flag [uns], so every RAM load leaf
     in the tree (lb/lbu/lh/lhu/lw/lwu/ld and the RVC twins) is one line off
     it.  [wp_load_s_sconf_gen] / [wp_load_s_sconf_ugen] below are its
     [uns = false] / [uns = true] restatements (WRAPPER RECIPE). *)
  (* [SrcOk rs1]: the base register's read, see the family note above. *)
  Lemma wp_load_s_sconf_gen_u {ktd : ktier} (width : Z) (c uns : bool) (pc : mword 64) (rd rs1 : mword 5)
      `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword (8*width)) (lv : mword 64) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    (* the vmem level hands back the value itself now *)
    extend_value uns v = lv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, uns, width)) -∗
    wordw_pointsto (KTR := ktd) width pa dqm v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg lv]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto (KTR := ktd) width pa dqm v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain Hlv pa Hrd Hrdok.
    (* the class, consumed at [rs1]: the wiring check for an [iApply]-shaped
       wrapper, whose own instance failure would otherwise be SHELVED.  See the
       family note above [wp_load_s_sconf_au]. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    (* the ADDRESS CLAIM the per-node form asks for: an owner of the window
       reads it straight off its own points-to. *)
    iDestruct (wordw_claim_of (KTR := ktd) width pa dqm v Hw0 with "Hbytes")
      as "#Hclaim".
    iApply (wp_load_s_sconf_au (ktd := ktd) width c uns pc rd rs1 imm m n
              (fun w => extend_value uns w)
              (fun w => (⌜w = v⌝ ∗ wordw_pointsto (KTR := ktd) width pa dqm v)%I) (⊤ ∖ ↑minstretN) b
              Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain (fun w => eq_refl) Hrd Hrdok
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr Hclaim [Hbytes]").
    { iModIntro. iExists v. iFrame "Hbytes". iIntros "Hb". iModIntro. by iFrame "Hb". }
    iIntros (w CID1 Hs1) "Hcg Hpc [-> Hbw]".
    iEval (rewrite Hlv) in "Hcg".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* the SIGNED restatement.  [SrcOk rs1] rides along; the [exact] below is a
     DIRECT application, so a class attached to the wrong parameter would be
     reported here ("Cannot infer the implicit parameter ... SrcOk ...") rather
     than shelved -- which is why these one-line wrappers need no consuming
     [assert] of their own. *)
  Lemma wp_load_s_sconf_gen {ktd : ktier} (width : Z) (c : bool) (pc : mword 64) (rd rs1 : mword 5)
      `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword (8*width)) (lv : mword 64) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    extend_value false v = lv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, false, width)) -∗
    wordw_pointsto (KTR := ktd) width pa dqm v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg lv]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto (KTR := ktd) width pa dqm v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_load_s_sconf_gen_u (ktd := ktd) width c false pc rd rs1 imm m n v lv b (dqm := dqm)).
  Qed.

  (* The UNSIGNED restatement.  [wp_load_s_sconf_gen_u] is generic in the
     extension ([uns]), so the two differ in exactly that flag -- which is why
     the width-1 [lbu] and the width-4 [lwu] are one-line instances of THIS
     rather than two hand-rolled copies of the same 190-line argument. *)
  (* [SrcOk rs1] as in the signed twin. *)
  Lemma wp_load_s_sconf_ugen {ktd : ktier} (width : Z) (c : bool) (pc : mword 64) (rd rs1 : mword 5)
      `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword (8*width)) (lv : mword 64) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    extend_value true v = lv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, true, width)) -∗
    wordw_pointsto (KTR := ktd) width pa dqm v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg lv]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto (KTR := ktd) width pa dqm v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_load_s_sconf_gen_u (ktd := ktd) width c true pc rd rs1 imm m n v lv b (dqm := dqm)).
  Qed.


  Local Lemma run_read_ram_plain_1 (addr : mword 64) (w : bv 8) s :
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < 1)%N ->
       s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    run (read_ram rv64d_types.Read_plain (Physaddr addr) 1 false) s
      (w, default_meta) s.
  Proof.
    intros Hdev Hbytes. unfold read_ram. cbn match.
    apply (proj2 (run_bind _ _ _ _ _)). eexists _, s.
    split; [apply run_returnM_fwd|]. cbn beta zeta.
    apply (proj2 (run_bind _ _ _ _ _)). unfold Defs.sail_mem_read. cbn beta zeta.
    eexists _, s. split.
    - eapply run_MemRead_ram_intro; [exact Hdev|intros j Hj; exact (Hbytes j Hj)|apply run_returnM_fwd].
    - cbn match beta. apply run_returnM_fwd.
  Qed.

  Local Lemma exec_read_ram_plain_1 (addr : mword 64) (w : bv 8) s :
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < 1)%N ->
       s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (read_ram rv64d_types.Read_plain (Physaddr addr) 1 false) s = Some ((w, default_meta), s).
  Proof.
    intros Hdev Hbytes.
    apply (run_to_exec _ _ _ _ (run_read_ram_plain_1 addr w s Hdev Hbytes)).
    unfold read_ram. cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
    unfold Defs.sail_mem_read. cbn beta zeta. unfold Defs.bind. cbn [Interface.iMon_bind].
    rewrite exec_MemRead; last exact Hdev. cbn [Interface.ReadReq.pa]. case_match eqn:Hrb.
    - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
    - exfalso. refine (read_bytes_ne (mem s) addr (Z.to_N 1) w _ Hrb).
      intros j Hj. change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
      change (RiscvModelBytes.nth_byte w j) with (nth_byte w j). exact (Hbytes j Hj).
  Qed.

  Local Lemma data2_ext_1_unsigned (v : mword 8) :
    extend_value true v = zero_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.
  (* lbu rd, imm(rs1) -- the width-1 UNSIGNED load, as an instance of
     [wp_load_s_sconf_ugen].  [dqm]-parametric: the byte may be owned outright
     (a stack buffer) or held at [DfracDiscarded] (a read-only image byte out
     of [kernel_data], which is how printint reads the [digits] table). *)
  (* [SrcOk rs1]: the base register's read, see the family note above
     [wp_load_s_sconf_au]. *)
  Lemma wp_lbu_s_sconf {ktd : ktier}
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 8) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    pa ↦ₘ[ktd]{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (zero_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦ₘ[ktd]{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbyte Hcont".
    iApply (wp_load_s_sconf_ugen (ktd := ktd) 1 false pc rd rs1 imm m n v (zero_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_1 (data2_ext_1_unsigned v) Hrd Hrdok
              with "Hcg Hpc Hinstr [Hbyte] [-]").
    { rewrite /wordw_pointsto.
      iSplit; [iPureIntro; change (is_aligned_vaddr (Virtaddr pa) 1 = true);
               unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity | ].
      change (Z.to_nat 1) with 1%nat.
      rewrite big_sepL_singleton pa_add_0 nth_byte0_id.
      (* A6.58: [wordw_pointsto]'s byte IS the ctx byte (A6.18), so the
         SC-era crossing here was already an identity.  Deleted, not
         replaced. *)
      iExact "Hbyte". }
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iEval (rewrite /wordw_pointsto) in "Hbw".
    iDestruct "Hbw" as "(_ & Hbw)".
    iEval (change (Z.to_nat 1) with 1%nat;
           rewrite big_sepL_singleton pa_add_0 nth_byte0_id) in "Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* the loaded-value facts: extend_value of the generic data2 = the
     per-width value written to rd. *)
  Lemma data2_ext_8 (v : mword 64) :
    extend_value false v = v.
  Proof. unfold extend_value. apply sign_extend'_id. Qed.

  Lemma data2_ext_4 (v : mword 32) :
    extend_value false v = sign_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.

  Lemma data2_ext_4_unsigned (v : mword 32) :
    extend_value true v = zero_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.

  (* lwu rd, imm(rs1) -- the width-4 UNSIGNED load (printk's %u and %x read
     their [uint32] argument with it).  One line off [wp_load_s_sconf_ugen],
     exactly as [wp_lw_s_sconf] is off the signed twin. *)
  (* [SrcOk rs1]: the base register's read, see the family note above
     [wp_load_s_sconf_au]. *)
  Lemma wp_lwu_s_sconf {ktd : ktier}
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) -∗ pa ↦₄[ktd]{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (zero_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄[ktd]{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_ugen (ktd := ktd) 4 false pc rd rs1 imm m n v (zero_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4_unsigned v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  (* [SrcOk rs1]: the base register's read, see the family note above
     [wp_load_s_sconf_au]. *)
  Lemma wp_cld_s_sconf {ktd : ktier}
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 64) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗ pa ↦₈[ktd]{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg v]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₈[ktd]{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iEval (rewrite -(wordw8_ctx (KTR2 := ktd))) in "Hbytes".
    iApply (wp_load_s_sconf_gen (ktd := ktd) 8 true pc rd rs1 imm m n v v b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes [Hcont]").
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iEval (rewrite (wordw8_ctx (KTR2 := ktd))) in "Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* [SrcOk rs1]: the base register's read, see the family note above
     [wp_load_s_sconf_au]. *)
  Lemma wp_ld_s_sconf {ktd : ktier}
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 64) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗ pa ↦₈[ktd]{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg v]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₈[ktd]{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iEval (rewrite -(wordw8_ctx (KTR2 := ktd))) in "Hbytes".
    iApply (wp_load_s_sconf_gen (ktd := ktd) 8 false pc rd rs1 imm m n v v b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes [Hcont]").
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iEval (rewrite (wordw8_ctx (KTR2 := ktd))) in "Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* [SrcOk rs1]: the base register's read, see the family note above
     [wp_load_s_sconf_au]. *)
  Lemma wp_clw_s_sconf {ktd : ktier}
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗ pa ↦₄[ktd]{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₄[ktd]{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen (ktd := ktd) 4 true pc rd rs1 imm m n v (sign_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  (* [SrcOk rs1]: the base register's read, see the family note above
     [wp_load_s_sconf_au]. *)
  Lemma wp_lw_s_sconf {ktd : ktier}
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗ pa ↦₄[ktd]{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄[ktd]{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen (ktd := ktd) 4 false pc rd rs1 imm m n v (sign_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* c.sd rs2, imm(rs1) -- width-8 RVC store.  No register write, so no   *)
  (* rd premises and no [sie_cap] retarget.                               *)
  (* ------------------------------------------------------------------- *)
  (* ------------------------------------------------------------------- *)
  (* The width/RVC-generic store in ATOMIC-UPDATE form (twin of           *)
  (* [wp_load_s_sconf_au]): the caller produces the cell inside the        *)
  (* engine callback's mask and takes the WRITTEN cell back there, so a    *)
  (* lock leaf can open [is_lock] around exactly this step.                *)
  (* ------------------------------------------------------------------- *)
  (* [SrcOk rs1] for the ADDRESS base and [SrcOk rs2] for the STORED VALUE:
     two independent instance arguments, resolved independently (no
     combinatorics).  See the family note above [wp_load_s_sconf_au]. *)
  (* ==================================================================== *)
  (* THE TIER SHAPE OF EVERY LEAF IN THIS FILE (sp-migration design §4/§5). *)
  (* [ktd] is the DATUM's tier, the section's [kt] the ACCESSING HART's --  *)
  (* the hart's is the CAPABILITY's, because a leaf drives the access with  *)
  (* the [sie_cap_gpr kt] it already consumes.  [KtierLe ktd kt] is the     *)
  (* whole access condition, and it sits at the END of the binder telescope *)
  (* so nothing before it can over-constrain the datum's tier.  There is NO *)
  (* separate witness premise: [sie_cap]'s fourth conjunct IS               *)
  (* [sr_ktier_wit strans_regime kt], delivered by the funnel's σ-callback  *)
  (* AT THE REBOUND HART, so no hart-crossing step is needed either.  At    *)
  (* KT0 the datum's own identity pin discharges admissibility              *)
  (* ([sr_adm_id]); at KT1 the regime's all-claims witness does             *)
  (* ([sr_absorb_wit]); both go through [SRegime.sr_absorb_ktier].          *)
  (* TIER-PRESERVING: the datum comes back at [ktd].                        *)
  (*                                                                        *)
  (* WHAT [ktd] DEFAULTS TO AT A CALL SITE: [kt].  Nothing determines the   *)
  (* datum's tier when the datum premise is handed over as a BRACKET, so    *)
  (* instance search closes [KtierLe ?ktd kt] eagerly with [ktier_le_refl]  *)
  (* -- see the note on the instances in Ktier.v, which also records why    *)
  (* neither [Hint Mode] nor a pure premise is a workable alternative.      *)
  (* That default is the frame slots' tier, so a prologue/epilogue site     *)
  (* needs no annotation; a datum at a DIFFERENT tier (static image data    *)
  (* under a tier-generic hart) says so with [(ktd := cur_ktier)].          *)
  (* ==================================================================== *)
  Lemma wp_store_s_sconf_au_dat {ktd : ktier} (width : Z) (c : bool) (pc : mword 64) (rs2 rs1 : mword 5)
      `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (sv : mword (8*width)) (Ψ : iProp Σ) (Em : coPset) (b : bool)
      `{!KtierLe ktd kt} (Res Post : iProp Σ) :
    0 < width -> width <= 8 -> vmem_width width ->
    (width | 4096) -> uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (data : mword (8*width)) s,
       dev_addr addr = false ->
       exec (write_ram rv64d_types.Write_plain (Physaddr addr) width data tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev))) ->
    (* the vmem level writes the value itself now, not the split projection *)
    (autocast (T := mword) (subrange_vec_dec (rget m rs2) (width*8-1) 0)
     : mword (8*width)) = sv ->
    (* see [wp_load_s_sconf_au] on [Em] *)
    ↑kptN ⊆ Em ->
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    (* THE WRITE OBLIGATION, which is [wordw_pointsto_write_c]'s statement at
       the CALLER's datum instead of at the ctx word tower.  It is the ONE
       ctx-specific step of the leaf below, so abstracting it here is what
       lets a store on a LEDGER cell (the lock's owner word, whose payload
       the ctx tower cannot carry) reuse the whole engine.

       THE MASK IS [==∗], NOT A MASK-CHANGING FUPD, and that is what makes
       the abstraction sound: the node has already closed to [∅], and the
       obligation runs entirely inside the caller's own atomic-update mask.
       So the caller may MINT here -- the interp is in hand, which is the
       one place in the tree it is (A6.71's rule read forwards).

       [CIDw] IS ∀-BOUND (A6.64): the token, the message's author and the
       view all name the hart the instruction obligation bound, not the
       section's, and the two spellings print identically. *)
    (forall (CIDw : CpuId) (img : bytemap) (sigma : mstate)
            (log : list pwmsg) (V : agent -> nat) (ppn : mword 44),
       (uint ea < 274877906944)%Z ->
       (bv_unsigned (subrange_vec_dec ea 11 0) + width <= 4096)%Z ->
       ktier_pin ktd ppn ea ->
       kmap_at (svpn_of ea) ppn KP_rw -∗
       gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
       tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
       TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
       Res ==∗
       gen_heap_interp (hG := riscv_memGS)
         (write_bytes sigma.(mem) (pa_of ppn ea) (Z.to_N width) sv) ∗
       tso_interp_of riscv_eraGS img
         (write_bytes sigma.(mem) (pa_of ppn ea) (Z.to_N width) sv)
         (log ++ [PWMsg (snap_of (pa_of ppn ea) (Z.to_N width) sv)
                    (hart_agent (@cpu_id CIDw))])%list
         (vstep (hart_agent (@cpu_id CIDw)) (V (hart_agent (@cpu_id CIDw)))
            (log ++ [PWMsg (snap_of (pa_of ppn ea) (Z.to_N width) sv)
                       (hart_agent (@cpu_id CIDw))])%list V) ∗
       TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
       Post) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (STORE (imm, Regidx rs2, Regidx rs1, width)) -∗
    wordw_claim (KTR := ktd) width ea -∗
    (|={⊤ ∖ ↑minstretN, Em}=> Res ∗ (Post ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      Ψ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv HkptEm ea Hwrite.
    iIntros "Hcg Hpc #Hinstr #Hclaim HAU Hcont".
    iDestruct "Hclaim" as "[%Hpalign Hcl2]".
    iDestruct "Hcl2" as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid)".
    assert (Halign : is_aligned_vaddr (Virtaddr ea) width = true) by exact Hpalign.
    pose proof (off_bound_div ea width Hw0 Hwdvd Halign) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iApply (wp_instr_s_sconf m n b b pc c
              (STORE (imm, Regidx rs2, Regidx rs1, width))
              (fun (_CIDx : CpuId) npc _ms' m' n' =>
                 (⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                  ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗ Ψ)%I)
              with "Hcg Hpc Hinstr [HAU Hcont]").
    iNext.
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HAU".
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
      (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
         [WpIntrInv.sda_slot_acc] below, the one place the two translation
         arms are told apart. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & Hctx & #Htc & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
             [SD] under the kernel table, the EMPTY set under Bare. ---- *)
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
      change (execute (STORE (imm, Regidx rs2, Regidx rs1, width)))
        with (execute_STORE imm (Regidx rs2) (Regidx rs1) width).
      assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                      (sign_extend' 64 imm) = ea)
        by (rewrite Lpin_rs1; reflexivity).
      pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
      pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
      pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
      assert (Lsv : autocast (T := mword)
                (subrange_vec_dec (tp_pin (CID := CID) m !!! Regidx rs2)
                   (Z.sub (Z.mul width 8) 1) 0) = sv)
        by (rewrite Lpin_rs2; exact Hsv).
      assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
              = true) by (rewrite Lmst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
              = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
      assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
              by (rewrite Lmst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
              = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
              by (rewrite Lsatp;
                  exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
      assert (Lep : effectivePrivilege (Store Data) (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
              = returnM Supervisor)
              by (rewrite Lmst;
                  exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
      (* A6.58: [Hctx] -- the thread-of-control token -- NO LONGER travels
         with the rest of the capability into the POST side.  A store is a
         LEDGER APPEND now, and every value-changing law takes the writer's
         own context ([wordw_pointsto_write_c] above), so the token goes
         DOWN to the write node and comes back inside the leaf's payload;
         [sie_cap] is rebuilt from it in the post exactly as before. *)
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
      2:{ iApply (swp_execute_STORE_ram_Sw (CID := CID) width Hvw Hwdvd Huintw
                    SD sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    imm rs2 rs1 (tp_pin (CID := CID) m) (pa_of ppn ea) sv
                    pmar0 pcfg paddr
                    (TsoCtx.own_context (CID := CID) TsoCtx.cur_ctx ∗ Ψ)%I
                    (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    Lsv
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                          (sign_extend' 64 imm))
                       (Store Data)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                    Lep
                    HA Hord HW Hcov (pma_all_ram Hpma_all) Hkd0
                    ltac:(rewrite Hea; exact Halign)
                    (pa_aligned_div ppn ea width Hw0 Hwdvd Halign)
                    with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HAU Hctx]").
          - (* the data translation *)
        iIntros "Hfrag HRes Hrw Hro".
        rewrite Hea.
        iApply ("Htrobl" $! ktd (Store Data) KP_rw ea ppn rr
                  with "[%] [%] [%] [%] [%] Hwit Hk Hcert Hfrag HRes Hrw Hro").
        + apply _.
        + exact (or_intror (or_intror (or_introl eq_refl))).
        + exact eq_refl.
        + exact Hcan.
        + exact Hid.
          - (* the RAM write node: the caller's atomic update, opened HERE.
               A6.58: the node now receives the era's log bundle beside the
               machine state and hands back the ADVANCED one -- the append
               this store IS.  §0.17' is respected: no deposit or absorb
               runs inside the update; the token is a plain resource
               threaded through it. *)
            iIntros (sigma img log tv V) "%Htv Hsi Htso".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (fupd_mask_subseteq (⊤ ∖ ↑minstretN)) as "Hb1"; [set_solver|].
            iMod "HAU" as "[Hres Hcl]".
            iMod (Hwrite CID img sigma log V ppn Hcan Hoff Hid
                with "Hk Hmem Htso Hctx Hres")
              as "(Hmem & Htso & Hctx & Hpost)".
            iMod ("Hcl" with "Hpost") as "HPsi".
            iMod "Hb1" as "_".
            iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
            iModIntro. iNext. iMod "Hb2" as "_". iModIntro.
            subst tv.
            iFrame "Hreg Hmem Hdev Htso Hctx HPsi". }
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf)
        "(%Hshape & Hrw & Hro & HRes & [Hctx HPsi] & Hfrag)".
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
      iExists (add_vec_int pc (if c then 2 else 4)), mst0, m, n.
      iFrame "HPC HnPC".
      iSplitL "Hfrag"; [ iApply (resv_any_intro _ None with "Hfrag") | ].
      iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
        iPureIntro. split; assumption. }
      iSplitL "Htr Hstk Harm Hctx".
      { rewrite /sie_cap. iFrame "Hstk Htr Harm Hctx Htc Hwit". }
      iFrame "Hfile HPsi". iPureIntro. split_and!; reflexivity.
    - (* ---------------- THE CONTINUATION ---------------- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & HPsi)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc' HPsi"). exact Hs.
  Qed.
  (* THE CTX-WORD INSTANCE, character-identical to what this leaf always was:
     [Res] is the cell before the store, [Post] the cell after it, and the
     write obligation is [wordw_pointsto_write_c].  Every consumer in the
     tree applies THIS one. *)
  Lemma wp_store_s_sconf_au {ktd : ktier} (width : Z) (c : bool) (pc : mword 64) (rs2 rs1 : mword 5)
      `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (sv : mword (8*width)) (Ψ : iProp Σ) (Em : coPset) (b : bool) `{!KtierLe ktd kt} :
    0 < width -> width <= 8 -> vmem_width width ->
    (width | 4096) -> uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (data : mword (8*width)) s,
       dev_addr addr = false ->
       exec (write_ram rv64d_types.Write_plain (Physaddr addr) width data tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev))) ->
    (autocast (T := mword) (subrange_vec_dec (rget m rs2) (width*8-1) 0)
     : mword (8*width)) = sv ->
    ↑kptN ⊆ Em ->
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (STORE (imm, Regidx rs2, Regidx rs1, width)) -∗
    wordw_claim (KTR := ktd) width ea -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ vold : mword (8*width),
       wordw_pointsto (KTR := ktd) width ea (DfracOwn 1) vold ∗
       (wordw_pointsto (KTR := ktd) width ea (DfracOwn 1) sv ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      Ψ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv HkptEm ea.
    iIntros "Hcg Hpc #Hinstr #Hclaim HAU Hcont".
    iApply (wp_store_s_sconf_au_dat (ktd := ktd) width c pc rs2 rs1 imm m n sv Ψ Em b
              (∃ vold : mword (8*width),
                 wordw_pointsto (KTR := ktd) width ea (DfracOwn 1) vold)%I
              (wordw_pointsto (KTR := ktd) width ea (DfracOwn 1) sv)
              Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv HkptEm
              with "Hcg Hpc Hinstr Hclaim [HAU] Hcont").
    { intros CIDw img sigma log V ppn Hcan Hoff Hid.
      iIntros "#Hk Hmem Htso Hctx [%vold Hbw]".
      iApply (wordw_pointsto_write_c (KTR := ktd) (CIDw := CIDw) width img sigma log V
                ea ppn vold sv Hw0 Hcan Hoff with "Hk Hmem Htso Hctx Hbw"). }
    iMod "HAU" as (vold) "[Hbw Hcl]". iModIntro. iFrame "Hcl". by iExists vold.
  Qed.

  (* the non-atomic instance: the caller owns the cell throughout. *)
  (* [SrcOk rs1] for the ADDRESS base and [SrcOk rs2] for the STORED VALUE:
     two independent instance arguments, resolved independently (no
     combinatorics).  See the family note above [wp_load_s_sconf_au]. *)
  Lemma wp_store_s_sconf_gen {ktd : ktier} (width : Z) (c : bool) (pc : mword 64) (rs2 rs1 : mword 5)
      `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (vold sv : mword (8*width)) (b : bool) `{!KtierLe ktd kt} :
    0 < width -> width <= 8 -> vmem_width width ->
    (width | 4096) -> uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (data : mword (8*width)) s,
       dev_addr addr = false ->
       exec (write_ram rv64d_types.Write_plain (Physaddr addr) width data tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev))) ->
    (* the vmem level writes the value itself now, not the split projection *)
    (autocast (T := mword) (subrange_vec_dec (rget m rs2) (width*8-1) 0)
     : mword (8*width)) = sv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c (STORE (imm, Regidx rs2, Regidx rs1, width)) -∗
    wordw_pointsto (KTR := ktd) width pa (DfracOwn 1) vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto (KTR := ktd) width pa (DfracOwn 1) sv -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv pa.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    (* ... and at [rs2]: the value this leaf promises to store is the same word
       at every hart, so the promise made at the entry hart still holds at the
       hart a trap returned to. *)
    assert (Hsv_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    (* the ADDRESS CLAIM the per-node form asks for: an owner of the window
       reads it straight off its own points-to. *)
    iDestruct (wordw_claim_of (KTR := ktd) width pa (DfracOwn 1) vold Hw0
                 with "Hbytes") as "#Hclaim".
    iApply (wp_store_s_sconf_au (ktd := ktd) width c pc rs2 rs1 imm m n sv
              (wordw_pointsto (KTR := ktd) width pa (DfracOwn 1) sv) (⊤ ∖ ↑minstretN) b
              Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr Hclaim [Hbytes]").
    { iModIntro. iExists vold. iFrame "Hbytes". iIntros "Hb". by iModIntro. }
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  Lemma store_ext_8 (r : mword 64) :
    (autocast (T := mword) (subrange_vec_dec r (8*8-1) 0) : mword (8*8)) = r.
  Proof. apply (subrange_full_gen_cast 64 r ltac:(lia)). Qed.

  Lemma autocast_subrange32_id (d : mword 32) :
    autocast (T := mword) (subrange_vec_dec d (8*(0+1)*4-1) (8*0*4)) = d.
  Proof.
    change (8*(0+1)*4-1) with 31. change (8*0*4) with 0.
    unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
    apply bv_eq. rewrite autocast_id.
    unfold to_word_idx, to_word, get_word, MachineWord.slice.
    rewrite MachineWord.cast_idx_refl.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned.
  Qed.

  Lemma store_ext_4 (r : mword 64) :
    (autocast (T := mword) (subrange_vec_dec r (4*8-1) 0) : mword (8*4)) = trunc32 r.
  Proof. unfold trunc32. reflexivity. Qed.

  (* [SrcOk rs1] for the ADDRESS base and [SrcOk rs2] for the STORED VALUE:
     two independent instance arguments, resolved independently (no
     combinatorics).  See the family note above [wp_load_s_sconf_au]. *)
  Lemma wp_csd_s_sconf {ktd : ktier}
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := rget m rs2 in
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗ pa ↦₈[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₈[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    (* ... and at [rs2]: the value this leaf promises to store is the same word
       at every hart, so the promise made at the entry hart still holds at the
       hart a trap returned to. *)
    assert (Hsv_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iEval (rewrite -(wordw8_ctx (KTR2 := ktd))) in "Hbytes".
    iApply (wp_store_s_sconf_gen (ktd := ktd) 8 true pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes [Hcont]").
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iEval (rewrite (wordw8_ctx (KTR2 := ktd))) in "Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.


  (* [SrcOk rs1] for the ADDRESS base and [SrcOk rs2] for the STORED VALUE:
     two independent instance arguments, resolved independently (no
     combinatorics).  See the family note above [wp_load_s_sconf_au]. *)
  Lemma wp_sd_s_sconf {ktd : ktier}
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := rget m rs2 in
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗ pa ↦₈[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₈[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    (* ... and at [rs2]: the value this leaf promises to store is the same word
       at every hart, so the promise made at the entry hart still holds at the
       hart a trap returned to. *)
    assert (Hsv_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iEval (rewrite -(wordw8_ctx (KTR2 := ktd))) in "Hbytes".
    iApply (wp_store_s_sconf_gen (ktd := ktd) 8 false pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes [Hcont]").
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iEval (rewrite (wordw8_ctx (KTR2 := ktd))) in "Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* [SrcOk rs1] for the ADDRESS base and [SrcOk rs2] for the STORED VALUE:
     two independent instance arguments, resolved independently (no
     combinatorics).  See the family note above [wp_load_s_sconf_au]. *)
  Lemma wp_csw_s_sconf {ktd : ktier}
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 32) (b : bool) `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (rget m rs2) in
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗ pa ↦₄[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₄[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    (* ... and at [rs2]: the value this leaf promises to store is the same word
       at every hart, so the promise made at the entry hart still holds at the
       hart a trap returned to. *)
    assert (Hsv_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen (ktd := ktd) 4 true pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  (* [SrcOk rs1] for the ADDRESS base and [SrcOk rs2] for the STORED VALUE:
     two independent instance arguments, resolved independently (no
     combinatorics).  See the family note above [wp_load_s_sconf_au]. *)
  Lemma wp_sw_s_sconf {ktd : ktier}
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 32) (b : bool) `{!KtierLe ktd kt} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (rget m rs2) in
    sie_cap_gpr kt m n b p -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗ pa ↦₄[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    (* ... and at [rs2]: the value this leaf promises to store is the same word
       at every hart, so the promise made at the entry hart still holds at the
       hart a trap returned to. *)
    assert (Hsv_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen (ktd := ktd) 4 false pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ld / sd -- the base-encoding width-8 pair: identical to the RVC      *)
  (* exemplars up to the fetch width (4-byte advance).                    *)
  (* ------------------------------------------------------------------- *)



  (* ------------------------------------------------------------------- *)
  (* c.lw / c.sw / lw / sw -- the width-4 quartet (lw sign-extends; the   *)
  (* stored word is trunc32 of rs2, definitionally the model's storeval). *)
  (* ------------------------------------------------------------------- *)










  (* ------------------------------------------------------------------- *)
  (* sb -- the width-1 RAM byte store (no alignment premise; the stored  *)
  (* byte is trunc8 of rs2, definitionally the model's storeval).        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma avi0_mul1 (a : mword 64) : add_vec_int a (0 * 1) = a.
  Proof. change (0 * 1)%Z with 0%Z. apply avi0. Qed.

  Local Lemma is_aligned_vaddr_1 (vaddr : virtaddr) : is_aligned_vaddr vaddr 1 = true.
  Proof. destruct vaddr as [addr]. unfold is_aligned_vaddr. rewrite Z.rem_1_r. reflexivity. Qed.

  Local Lemma is_aligned_paddr_1 (paddr : physaddr) : is_aligned_paddr paddr 1 = true.
  Proof. destruct paddr as [addr]. unfold is_aligned_paddr. rewrite Z.rem_1_r. reflexivity. Qed.

  Definition trunc8 (w : mword 64) : mword 8 :=
    autocast (T := mword) (subrange_vec_dec w (Z.sub (Z.mul 1 8) 1) 0).

  (* the byte an [sb] writes when its source register was filled by an [lbu]:
     the store leaf truncates to 8 bits what the load leaf zero-extended to
     64.  Every byte-copy loop needs this (memmove, copyinstr), so it lives
     next to [trunc8] rather than in each proof. *)
  Lemma trunc8_zext8 (b : mword 8) : trunc8 (zero_extend' 64 b) = b.
  Proof.
    apply bv_eq. unfold trunc8. rewrite autocast_id.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice.
    change (MachineWord.MachineWord.Z_idx 0) with 0%N.
    rewrite bv_extract_0_unsigned.
    cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec to_word get_word
         MachineWord.MachineWord.zero_extend].
    rewrite bv_zero_extend_unsigned; [| vm_compute; discriminate].
    change (MachineWord.Z_idx 8) with 8%N.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  Qed.

  (* ...and the byte it writes when its source register is x0: copyinstr's
     [sb zero,0(a5)], the store that plants the string terminator. *)
  Lemma trunc8_zero : trunc8 (zero_reg : mword 64) = (mword_of_int 0 : mword 8).
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.

  (* [SrcOk rs1] for the ADDRESS base and [SrcOk rs2] for the STORED VALUE:
     two independent instance arguments, resolved independently (no
     combinatorics).  See the family note above [wp_load_s_sconf_au]. *)
  (* ==================================================================== *)
  (* THE TIER SHAPE OF EVERY LEAF IN THIS FILE (sp-migration design §4/§5). *)
  (* [ktd] is the DATUM's tier, the section's [kt] the ACCESSING HART's --  *)
  (* the hart's is the CAPABILITY's, because a leaf drives the access with  *)
  (* the [sie_cap_gpr kt] it already consumes.  [KtierLe ktd kt] is the     *)
  (* whole access condition, and it sits at the END of the binder telescope *)
  (* so nothing before it can over-constrain the datum's tier.  There is NO *)
  (* separate witness premise: [sie_cap]'s fourth conjunct IS               *)
  (* [sr_ktier_wit strans_regime kt], delivered by the funnel's σ-callback  *)
  (* AT THE REBOUND HART, so no hart-crossing step is needed either.  At    *)
  (* KT0 the datum's own identity pin discharges admissibility              *)
  (* ([sr_adm_id]); at KT1 the regime's all-claims witness does             *)
  (* ([sr_absorb_wit]); both go through [SRegime.sr_absorb_ktier].          *)
  (* TIER-PRESERVING: the datum comes back at [ktd].                        *)
  (*                                                                        *)
  (* WHAT [ktd] DEFAULTS TO AT A CALL SITE: [kt].  Nothing determines the   *)
  (* datum's tier when the datum premise is handed over as a BRACKET, so    *)
  (* instance search closes [KtierLe ?ktd kt] eagerly with [ktier_le_refl]  *)
  (* -- see the note on the instances in Ktier.v, which also records why    *)
  (* neither [Hint Mode] nor a pure premise is a workable alternative.      *)
  (* That default is the frame slots' tier, so a prologue/epilogue site     *)
  (* needs no annotation; a datum at a DIFFERENT tier (static image data    *)
  (* under a tier-generic hart) says so with [(ktd := cur_ktier)].          *)
  (* ==================================================================== *)
  (* the width-1 window IS one byte: [wordw_pointsto 1]'s alignment conjunct
     is [Z.rem _ 1 = 0] and its list is the single byte at offset 0. *)


  Lemma wordw1_byte `{KTR : !CurKtier} (a : Arch.pa) (dq : dfrac)
      (w : mword (8*1)) :
    (* A6.63'': [wordw_pointsto] is built from [ctx_pointsto cur_ctx]
       (line 118), so the one-byte window IS the CONTEXT byte, not the raw
       [mem_pointsto].  Stating the raw one made this [⊣⊢] false in the
       return direction at TSO; at the ctx tower both directions are
       identities. *)
    wordw_pointsto 1 a dq w ⊣⊢ ctx_pointsto cur_ctx a dq w.
  Proof.
    rewrite /wordw_pointsto. change (Z.to_nat 1) with 1%nat.
    rewrite big_sepL_singleton pa_add_0 nth_byte0_id.
    iSplit; [ iIntros "[_ $]"
            | iIntros "$"; iPureIntro;
              unfold is_aligned_paddr, is_aligned_vaddr; cbn [bits_of_physaddr];
              rewrite Z.rem_1_r; reflexivity ].
  Qed.

  Lemma wp_sb_s_sconf {ktd : ktier}
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (vold : bv 8) (b : bool) `{!KtierLe ktd kt} :
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := trunc8 (rget m rs2) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    ea ↦ₘ[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      ea ↦ₘ[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea storeval.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
      by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    assert (Hsv_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbyte Hcont".
    iApply (wp_store_s_sconf_gen (ktd := ktd) 1 false pc rs2 rs1 imm m n vold
              storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia)
              ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_1 eq_refl
              with "Hcg Hpc Hinstr [Hbyte] [Hcont]").
    { iApply (wordw1_byte (KTR := ktd) ea (DfracOwn 1) vold). iExact "Hbyte". }
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iApply ("Hcont" $! CID1 with "[%] Hcg Hpc [Hbw]"); [ exact Hs1 | ].
    iEval (rewrite (wordw1_byte (KTR := ktd) ea (DfracOwn 1) storeval)) in "Hbw".
    iExact "Hbw".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ldsp / c.sdsp -- the sp-relative immediate forms, bridged onto     *)
  (* the c.ld / c.sd leaves by [sext9_12_64] (pure immediate rewrite).    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cldsp_s_sconf {ktd : ktier}
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : regfile) (n : nat) (v : mword 64) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈[ktd]{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg v]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      pa ↦₈[ktd]{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm pa Hrd Hrdok.
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_cld_s_sconf (ktd := ktd) pc rd csp_rs1 imm m n v b (dqm:=dqm) Hrd Hrdok).
  Qed.

  (* THE SIDE CONDITION ARRIVES BY INSTANCE RESOLUTION, NOT AS A PREMISE.
     [rget m rs2] is a lookup in [tp_pin m], so the stored value as spelled
     here depends on the ambient hart at exactly one register, rs2 = tp.  Once
     the funnel's σ-callback moves inside [wp_next] the obligation arrives at
     the hart the trap returned TO, while this statement was elaborated at the
     hart we came FROM, and the two agree only away from tp.  This leaf has no
     [rd_ok]/[ops_ok] slot to widen -- a c.sdsp writes no register, so it has
     no pure premises at all -- and it is referenced ~640 times, so an ordinary
     premise would move every one of those call sites.  [IntrDefs.SrcOk] is
     that same side condition delivered as an IMPLICIT class argument: it
     occupies no positional slot, so no call site changes.

     THE STORED VALUE STAYS SPELLED [rget m rs2], at the ENTRY hart, and that
     is deliberate -- see this file's header.  The tempting alternative, making
     the statement literally hart-free as [m !!! Regidx rs2], was MEASURED and
     rejected: it breaks 99 consumer files, because a caller normalises the
     value it gets back with an [iEval (rgne)] / [rewrite H] whose LHS is a
     [rget], and those have nothing to match once the [rget] is gone.  So the
     class carries the side condition and the SPELLING does not move.

     LANDED AHEAD OF ITS CONSUMER, exactly as [IntrDefs.src_ok] was, and for
     the same reason: nothing here needs the reconciliation until the funnel's
     σ-callback moves inside [wp_next] and the obligation starts arriving at
     the rebound hart.  What the class buys is proved, not asserted -- see
     [IntrDefs.src_ok_rget_all] / [src_ok_rget_indep] -- and the point of
     landing it now is that adding it costs ZERO of this leaf's 672 references,
     so the funnel change is not entangled with a 672-site sweep. *)
  Lemma wp_csdsp_s_sconf {ktd : ktier}
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5) `{!SrcOk rs2}
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) `{!KtierLe ktd kt} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let storeval := rget m rs2 in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 2) -∗
      pa ↦₈[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm pa storeval.
    (* WHAT THE CLASS WILL DO HERE, recorded as a proved fact rather than a
       comment: the value this leaf promises is hart-independent, so the
       promise made at the entry hart is still the promise at the hart a trap
       returned to.  That is the ONE step the funnel change needs, and
       [SrcOk rs2] is its whole content.  It is stated and not yet used because
       today's σ-callback is still instantiated at the entry hart -- the
       reconciliation has no gap to close until [wp_instr_s_sconf]'s callback
       moves inside [wp_next].  (At a VARIABLE [rs2] this is not a conversion:
       the pin's [bool_decide] cannot reduce, so without the class there is no
       proof of it at all.) *)
    assert (Hsv_all : forall hh : CpuId, rget (CID := hh) m rs2 = storeval)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_csd_s_sconf (ktd := ktd) pc rs2 csp_rs1 imm m n vold b).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* sd zero, imm(rs1) -- release's unconditional zero store.             *)
  (* ------------------------------------------------------------------- *)
  (* [SrcOk rs1]: the address base's read.  The stored value is x0, a
     literal, so it needs nothing.  See the family note above
     [wp_load_s_sconf_au]. *)
  (* ==================================================================== *)
  (* THE TIER SHAPE OF EVERY LEAF IN THIS FILE (sp-migration design §4/§5). *)
  (* [ktd] is the DATUM's tier, the section's [kt] the ACCESSING HART's --  *)
  (* the hart's is the CAPABILITY's, because a leaf drives the access with  *)
  (* the [sie_cap_gpr kt] it already consumes.  [KtierLe ktd kt] is the     *)
  (* whole access condition, and it sits at the END of the binder telescope *)
  (* so nothing before it can over-constrain the datum's tier.  There is NO *)
  (* separate witness premise: [sie_cap]'s fourth conjunct IS               *)
  (* [sr_ktier_wit strans_regime kt], delivered by the funnel's σ-callback  *)
  (* AT THE REBOUND HART, so no hart-crossing step is needed either.  At    *)
  (* KT0 the datum's own identity pin discharges admissibility              *)
  (* ([sr_adm_id]); at KT1 the regime's all-claims witness does             *)
  (* ([sr_absorb_wit]); both go through [SRegime.sr_absorb_ktier].          *)
  (* TIER-PRESERVING: the datum comes back at [ktd].                        *)
  (*                                                                        *)
  (* WHAT [ktd] DEFAULTS TO AT A CALL SITE: [kt].  Nothing determines the   *)
  (* datum's tier when the datum premise is handed over as a BRACKET, so    *)
  (* instance search closes [KtierLe ?ktd kt] eagerly with [ktier_le_refl]  *)
  (* -- see the note on the instances in Ktier.v, which also records why    *)
  (* neither [Hint Mode] nor a pure premise is a workable alternative.      *)
  (* That default is the frame slots' tier, so a prologue/epilogue site     *)
  (* needs no annotation; a datum at a DIFFERENT tier (static image data    *)
  (* under a tier-generic hart) says so with [(ktd := cur_ktier)].          *)
  (* ==================================================================== *)
  Lemma wp_sd_zero_s_sconf {ktd : ktier}
      (pc : mword 64) (rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) `{!KtierLe ktd kt} :
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := (zero_reg : mword 64) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    ea ↦₈[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      ea ↦₈[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea storeval.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
      by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    (* A PREMISE ABOUT AN x0 OPERAND CANNOT BE PURE: the stored word is
       [zero_reg] only because [gpr_file] says x0 is, so peel that fact off
       the capability's file and put the file straight back. *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 (tp_pin m) (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0 Hfile]".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    assert (Hsv : (autocast (T := mword)
              (subrange_vec_dec (rget m (mword_of_int 0 : mword 5)) (8*8-1) 0)
              : mword (8*8)) = storeval).
    { unfold storeval, rget. rewrite Hx0. exact (store_ext_8 zero_reg). }
    iEval (rewrite -(wordw8_ctx (KTR2 := ktd))) in "Hbytes".
    iApply (wp_store_s_sconf_gen (ktd := ktd) 8 false pc
              (mword_of_int 0 : mword 5) rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia)
              ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 Hsv
              with "Hcg Hpc Hinstr Hbytes [Hcont]").
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iEval (rewrite (wordw8_ctx (KTR2 := ktd))) in "Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* c.sw x0 store (width-4 sibling of wp_sd_zero_s_sconf); moved here from
     ProofInitlock.v -- a store leaf belongs in the leaf file. *)
  (* [SrcOk rs1]: the address base's read.  The stored value is x0, a
     literal, so it needs nothing.  See the family note above
     [wp_load_s_sconf_au]. *)
  (* ==================================================================== *)
  (* THE TIER SHAPE OF EVERY LEAF IN THIS FILE (sp-migration design §4/§5). *)
  (* [ktd] is the DATUM's tier, the section's [kt] the ACCESSING HART's --  *)
  (* the hart's is the CAPABILITY's, because a leaf drives the access with  *)
  (* the [sie_cap_gpr kt] it already consumes.  [KtierLe ktd kt] is the     *)
  (* whole access condition, and it sits at the END of the binder telescope *)
  (* so nothing before it can over-constrain the datum's tier.  There is NO *)
  (* separate witness premise: [sie_cap]'s fourth conjunct IS               *)
  (* [sr_ktier_wit strans_regime kt], delivered by the funnel's σ-callback  *)
  (* AT THE REBOUND HART, so no hart-crossing step is needed either.  At    *)
  (* KT0 the datum's own identity pin discharges admissibility              *)
  (* ([sr_adm_id]); at KT1 the regime's all-claims witness does             *)
  (* ([sr_absorb_wit]); both go through [SRegime.sr_absorb_ktier].          *)
  (* TIER-PRESERVING: the datum comes back at [ktd].                        *)
  (*                                                                        *)
  (* WHAT [ktd] DEFAULTS TO AT A CALL SITE: [kt].  Nothing determines the   *)
  (* datum's tier when the datum premise is handed over as a BRACKET, so    *)
  (* instance search closes [KtierLe ?ktd kt] eagerly with [ktier_le_refl]  *)
  (* -- see the note on the instances in Ktier.v, which also records why    *)
  (* neither [Hint Mode] nor a pure premise is a workable alternative.      *)
  (* That default is the frame slots' tier, so a prologue/epilogue site     *)
  (* needs no annotation; a datum at a DIFFERENT tier (static image data    *)
  (* under a tier-generic hart) says so with [(ktd := cur_ktier)].          *)
  (* ==================================================================== *)
  Lemma wp_sw_zero_s_sconf {ktd : ktier}
      (pc : mword 64) (rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (vold : bv 32) (b : bool) `{!KtierLe ktd kt} :
    let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := (mword_of_int 0 : mword 32) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    ea ↦₄[ktd] vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      ea ↦₄[ktd] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea storeval.
    (* the class, consumed at [rs1] -- the wiring check; see the family note. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
      by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    (* the x0 operand, peeled off the capability's file -- see
       [wp_sd_zero_s_sconf]. *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 (tp_pin m) (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0 Hfile]".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    assert (Hsv : (autocast (T := mword)
              (subrange_vec_dec (rget m (mword_of_int 0 : mword 5)) (4*8-1) 0)
              : mword (8*4)) = storeval).
    { unfold storeval, rget. rewrite Hx0. rewrite (store_ext_4 zero_reg).
      apply bv_eq. vm_compute. reflexivity. }
    iApply (wp_store_s_sconf_gen (ktd := ktd) 4 false pc
              (mword_of_int 0 : mword 5) rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia)
              ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 Hsv
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block for why this is  *)
  (* here and not only there.  An unresolved [SrcOk] inside an [iApply] is *)
  (* SHELVED, not reported, so a hint this file cannot see (an import      *)
  (* change, a reordered [Require]) would surface only as some consumer's  *)
  (* "Attempt to save an incomplete proof" hundreds of lines away.  These  *)
  (* two lines make that failure happen HERE.  x9/x15 (s1/a5) are the      *)
  (* base registers the load/store leaves above are actually applied at;   *)
  (* [csp_rs1] is the one [wp_c{ld,sd}sp_s_sconf] pass down internally.    *)
  (* ------------------------------------------------------------------- *)
  Definition mem_srcok_pos_s1 : SrcOk (mword_of_int 9 : mword 5) := _.
  Definition mem_srcok_pos_a5 : SrcOk (mword_of_int 15 : mword 5) := _.
  Definition mem_srcok_pos_sp : SrcOk csp_rs1 := _.
  Fail Definition mem_srcok_neg : SrcOk Rtp := _.

End WpSconfMem.
