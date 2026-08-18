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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import MinstretInv.
Require Import UserBits.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile HartTp WpNext.
Require Import SmodePte.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt.
Require Import HartLift HartSpan HartSpanChar HartSwp HartSFrame HartSMem.
Require Import WpSmodePtEngine WpSmodePtFetch.
Require Import KptShare KptGoodb KptPt.
Require Import WpIntrInv.
Require Import WpSmodeMemGen.
Require Import MemAccessGen.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import KptGhost.   (* kptN: the accessor-mask premise below *)
Require Import SRegime.
Require Import Riscv.rv64d_types Riscv.rv64d.
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
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
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
  Definition wordw_pointsto `{KTR : !CurKtier} (width : Z) (a : Arch.pa) (dq : dfrac) (w : mword (8*width)) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     [∗ list] j ∈ seq 0 (Z.to_nat width), mem_pointsto (pa_add a j) dq (nth_byte w j))%I.

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
  Local Lemma wordw_pointsto_write_c `{KTR : !CurKtier} (width : Z) (mm : _) (a : mword 64)
      (ppn : mword 44) (vold vnew : mword (8*width)) :
    0 < width ->
    (uint a < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec a 11 0) + width <= 4096)%Z ->
    kmap_at (svpn_of a) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ wordw_pointsto width a (DfracOwn 1) vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn a) (Z.to_N width) vnew) ∗
    wordw_pointsto width a (DfracOwn 1) vnew.
  Proof.
    intros Hw0 Hcan Hoff. iIntros "#Hk Hm Hw". rewrite /wordw_pointsto.
    iDestruct "Hw" as "(%Hal & Hb)".
    iMod (s_win_write a ppn (nth_byte vold) (nth_byte vnew) Hcan (seq 0 (Z.to_nat width))
            ltac:(apply Forall_forall; intros j Hj; apply elem_of_list_In, elem_of_seq in Hj;
                  destruct Hj as [_ Hjw];
                  assert (Hjz : Z.of_nat j < width) by
                    (rewrite <- (Z2Nat.id width) by lia; apply Nat2Z.inj_lt; exact Hjw);
                  lia)
            mm with "Hk Hm Hb") as "[Hm Hb]".
    iModIntro. iSplitL "Hm".
    - unfold write_bytes. replace (N.to_nat (Z.to_N width)) with (Z.to_nat width) by lia. iFrame "Hm".
    - iFrame "Hb". iPureIntro. exact Hal.
  Qed.

  (* claim-keyed single-byte write (width-1 store): writes at [pa_of ppn a]. *)
  Local Lemma mem_pointsto_write_c `{KTR : !CurKtier} (mm : _) (a : mword 64)
      (ppn : mword 44) (vold vnew : bv 8) :
    (uint a < 274877906944)%Z ->
    kmap_at (svpn_of a) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₘ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn a) 1 vnew) ∗ a ↦ₘ (nth_byte vnew 0).
  Proof.
    intros Hcan. iIntros "#Hk Hm Hw".
    assert (Hoff0 : (bv_unsigned (subrange_vec_dec a 11 0) + Z.of_nat 0 < 4096)%Z).
    { change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r.
      pose proof (off_bound_div a 1 ltac:(lia) ltac:(exists 4096; lia)
        ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)) as H1.
      rewrite (uint_unsigned_n _) in H1. lia. }
    iAssert ([∗ list] j ∈ (cons 0%nat nil), (pa_add a j) ↦ₘ (nth_byte vold j))%I with "[Hw]" as "Hw'".
    { iEval (rewrite big_sepL_singleton pa_add_0 nth_byte0_id). iExact "Hw". }
    iMod (s_win_write a ppn (nth_byte vold) (nth_byte vnew) Hcan (cons 0%nat nil)
            ltac:(constructor; [exact Hoff0 | constructor])
            mm with "Hk Hm Hw'") as "[Hm Hb]".
    iModIntro. iSplitL "Hm".
    - replace (write_bytes mm (pa_of ppn a) 1 vnew)
        with (foldr (fun j acc => <[pa_add (pa_of ppn a) j := nth_byte vnew j]> acc) mm (cons 0%nat nil)).
      2:{ cbn [foldr]. rewrite write_bytes_1 pa_add_0. reflexivity. }
      iExact "Hm".
    - iDestruct "Hb" as "[Hb _]". rewrite pa_add_0. iExact "Hb".
  Qed.

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
  Lemma wp_load_s_sconf_au {ktd : ktier} (width : Z) (c uns : bool) (pc : mword 64) (rd rs1 : mword 5)
      `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (ext : mword (8*width) -> mword 64)
      (Ψ : mword (8*width) -> iProp Σ) (Em : coPset) (b : bool) {dqm : dfrac} `{!KtierLe ktd kt} :
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
      iDestruct (sie_cap_to_cells (CID := CID) with "Hcap")
        as (satp0 tlbv pcfg paddr)
        "(%Hsok & %Hpok & Hsatp & Htlb & Hpcfg & Hpaddr & HRes & Hstk & Harm & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      iAssert (hreg_frame (CID := CID)
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) sda_Drw ∗
               hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) sda_Dro)%I
        with "[Htlb Hms Hpriv Hmenv Hsatp Hpcfg Hpaddr]" as "[Hrw Hro]".
      { rewrite sda_frames.
        iFrame "Htlb Hms Hpriv Hmenv Hsatp Hpcfg Hpaddr".
        iFrame "Hpma Hhtif Hmisa". }
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
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm] [-]").
      2:{ iApply (swp_execute_LOAD_ram_Sw_ex (CID := CID) width Hvw Hwdvd Huintw
                    sda_Drw sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    imm rs1 rd uns (tp_pin (CID := CID) m) (pa_of ppn ea)
                    pmar0 pcfg paddr
                    Ψ (Mobl_ram_ex width (pa_of ppn ea) Ψ)
                    (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    sda_disj sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                    sda_in_pma sda_in_pcfg sda_in_paddr sda_in_htif
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (sda_Drw ∪ sda_Dro) sda_Drw
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                          (sign_extend' 64 imm))
                       (Load Data)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (sda_Drw ∪ sda_Dro) sda_Drw
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       sda_in_mst sda_in_satp Lsxl Lmd)
                    Lep
                    HA Hord HR Hcov (pma_all_ram Hpma_all) Hkd0
                    ltac:(rewrite Hea; exact Halign)
                    (pa_aligned_div ppn ea width Hw0 Hwdvd Halign)
                    Hrd
                    (swp_read_ram_node_w_ex (CID := CID) width (pa_of ppn ea) Ψ
                       Hvw (addr_is_ram_not_dev _ Hkd0))
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [HAU]").
          - (* the data translation *)
            iIntros "Hfrag HRes Hrw Hro".
            rewrite Hea.
            iApply (sda_translate (CID := CID) (strans_regime (CID := CID))
                      kt ktd (DfracOwn 1) (Load Data) KP_rw mst0 MENVCFG_S
                      satp0 pmar0 pcfg paddr tlbv ea ppn rr
                      (or_intror (or_introl eq_refl)) I eq_refl HSXL HMPRV Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - (* the RAM read node: the caller's atomic update, opened HERE *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (fupd_mask_subseteq (⊤ ∖ ↑minstretN)) as "Hb1"; [set_solver|].
            iMod "HAU" as (v) "[Hbw Hcl]".
            iEval (rewrite /wordw_pointsto) in "Hbw".
            iDestruct "Hbw" as "[%Hal1 Hb]".
            iDestruct (s_mem_chunk (KTR := ktd) sigma ea ea 0 (Z.to_nat width)
                         (Z.to_nat width) (nth_byte v) ppn dqm
                         ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff' Hcan
                         with "Hmem Hk Hb") as %(Hbf & _ & _ & _).
            iMod ("Hcl" with "[Hb]") as "HPsi".
            { rewrite /wordw_pointsto. iFrame "Hb". iPureIntro. exact Hal1. }
            iMod "Hb1" as "_".
            iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
            iModIntro. iExists v.
            iSplitR.
            { iPureIntro. intros j Hj. apply Hbf. lia. }
            iNext. iMod "Hb2" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev HPsi". }
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (v) "(Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & HPsi)".
      iSplitR; [done|].
      iAssert (∃ tv2 : type_of_register tlb,
               hreg_frame (CID := CID)
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Drw ∗
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
        iDestruct (sda_rw_ext _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
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
      iCombine "Hrw Hro" as "Hrwro".
      iEval (rewrite sda_frames) in "Hrwro".
      iDestruct "Hrwro" as "(Htlb & Hms & Hpriv & Hmenv & Hsatp & _ & Hpcfg &
                          Hpaddr & _ & _)".
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
      iSplitL "Hsatp Htlb Hpcfg Hpaddr HRes Hstk Harm".
      { iApply (sie_cap_of_cells (CID := CID) kt
                (<[Regidx rd := regval_into_reg (ext v)]> m)
                n b p satp0 tv2 pcfg paddr Hsok
                ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                with "Hsatp Htlb Hpcfg Hpaddr HRes [Hstk Harm]").
      rewrite /sie_cap_rest -Hsp. iFrame "Hstk Harm Hwit". }
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
      rewrite big_sepL_singleton pa_add_0 nth_byte0_id. iExact "Hbyte". }
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
    iApply (wp_load_s_sconf_gen (ktd := ktd) 8 true pc rd rs1 imm m n v v b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
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
    iApply (wp_load_s_sconf_gen (ktd := ktd) 8 false pc rd rs1 imm m n v v b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
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
  Lemma wp_store_s_sconf_au {ktd : ktier} (width : Z) (c : bool) (pc : mword 64) (rs2 rs1 : mword 5)
      `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (sv : mword (8*width)) (Ψ : iProp Σ) (Em : coPset) (b : bool) `{!KtierLe ktd kt} :
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
      iDestruct (sie_cap_to_cells (CID := CID) with "Hcap")
        as (satp0 tlbv pcfg paddr)
        "(%Hsok & %Hpok & Hsatp & Htlb & Hpcfg & Hpaddr & HRes & Hstk & Harm & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      iAssert (hreg_frame (CID := CID)
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) sda_Drw ∗
               hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) sda_Dro)%I
        with "[Htlb Hms Hpriv Hmenv Hsatp Hpcfg Hpaddr]" as "[Hrw Hro]".
      { rewrite sda_frames.
        iFrame "Htlb Hms Hpriv Hmenv Hsatp Hpcfg Hpaddr".
        iFrame "Hpma Hhtif Hmisa". }
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
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm] [-]").
      2:{ iApply (swp_execute_STORE_ram_Sw (CID := CID) width Hvw Hwdvd Huintw
                    sda_Drw sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    imm rs2 rs1 (tp_pin (CID := CID) m) (pa_of ppn ea) sv
                    pmar0 pcfg paddr
                    Ψ (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    Lsv
                    sda_disj sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                    sda_in_pma sda_in_pcfg sda_in_paddr sda_in_htif
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (sda_Drw ∪ sda_Dro) sda_Drw
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                          (sign_extend' 64 imm))
                       (Store Data)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       sda_in_mst sda_in_priv sda_in_menv sda_in_satp
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (sda_Drw ∪ sda_Dro) sda_Drw
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       sda_in_mst sda_in_satp Lsxl Lmd)
                    Lep
                    HA Hord HW Hcov (pma_all_ram Hpma_all) Hkd0
                    ltac:(rewrite Hea; exact Halign)
                    (pa_aligned_div ppn ea width Hw0 Hwdvd Halign)
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [HAU]").
          - (* the data translation *)
        iIntros "Hfrag HRes Hrw Hro".
        rewrite Hea.
        iApply (sda_translate (CID := CID) (strans_regime (CID := CID))
                  kt ktd (DfracOwn 1) (Store Data) KP_rw mst0 MENVCFG_S
                  satp0 pmar0 pcfg paddr tlbv ea ppn rr
                  (or_intror (or_intror (or_introl eq_refl))) eq_refl eq_refl
                  HSXL HMPRV Hsok
                  ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                  (pma_all_ram Hpma_all) Hcan Hid
                  with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - (* the RAM write node: the caller's atomic update, opened HERE *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (fupd_mask_subseteq (⊤ ∖ ↑minstretN)) as "Hb1"; [set_solver|].
            iMod "HAU" as (vold) "[Hbw Hcl]".
            iMod (wordw_pointsto_write_c (KTR := ktd) width sigma.(mem) ea ppn
                vold sv Hw0 Hcan Hoff with "Hk Hmem Hbw") as "[Hmem Hbw]".
            iMod ("Hcl" with "Hbw") as "HPsi".
            iMod "Hb1" as "_".
            iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
            iModIntro. iNext. iMod "Hb2" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev HPsi". }
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & HPsi & Hfrag)".
      iSplitR; [done|].
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (CID := CID)
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Drw ∗
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
          iDestruct (sda_rw_ext _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
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
      iCombine "Hrw Hro" as "Hrwro".
      iEval (rewrite sda_frames) in "Hrwro".
      iDestruct "Hrwro" as "(Htlb & Hms & Hpriv & Hmenv & Hsatp & _ & Hpcfg &
                            Hpaddr & _ & _)".
      iExists (add_vec_int pc (if c then 2 else 4)), mst0, m, n.
      iFrame "HPC HnPC".
      iSplitL "Hfrag"; [ iApply (resv_any_intro _ None with "Hfrag") | ].
      iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
        iPureIntro. split; assumption. }
      iSplitL "Hsatp Htlb Hpcfg Hpaddr HRes Hstk Harm".
      { iApply (sie_cap_of_cells (CID := CID) kt m n b p satp0 tv2 pcfg paddr
                  Hsok ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                  with "Hsatp Htlb Hpcfg Hpaddr HRes [Hstk Harm]").
        rewrite /sie_cap_rest. iFrame "Hstk Harm Hwit". }
      iFrame "Hfile HPsi". iPureIntro. split_and!; reflexivity.
    - (* ---------------- THE CONTINUATION ---------------- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & HPsi)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc' HPsi"). exact Hs.
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
    iApply (wp_store_s_sconf_gen (ktd := ktd) 8 true pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
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
    iApply (wp_store_s_sconf_gen (ktd := ktd) 8 false pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
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
    wordw_pointsto 1 a dq w ⊣⊢ mem_pointsto a dq w.
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
    iApply (wordw1_byte (KTR := ktd) ea (DfracOwn 1) storeval). iExact "Hbw".
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
    iApply (wp_store_s_sconf_gen (ktd := ktd) 8 false pc
              (mword_of_int 0 : mword 5) rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia)
              ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 Hsv
              with "Hcg Hpc Hinstr Hbytes Hcont").
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
