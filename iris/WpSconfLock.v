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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import WpLoad.
Require Import RegFile HartTp WpNext.
Require Import MinstretInv InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
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
Require Import TsoMemPa.  (* A6.87: [pwmsg]/[agent]/[bytemap] -- the free-path
   word read is stated over the LOG, not over a cell *)
Require Import WpSconfMem.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
(* A6.86: [TsoCtxShim] is RETIRED -- its last live use died with the M4
   contract flip.  See its tombstone. *)
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
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
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
  (* A6.86: [lk_addr_claim] carries the PER-BYTE claims too (the free page's
     bytes are keyed by them), so it is no longer convertible with
     [wordw_claim] -- it is strictly stronger, and this is the projection. *)
  Local Lemma lk_addr_claim_wordw (a : Arch.pa) (w : Z) :
    WpLock.lk_addr_claim a w ⊢ wordw_claim (KTR := KT0) w a.
  Proof.
    rewrite /WpLock.lk_addr_claim /wordw_claim /mem_claim.
    iIntros "(%Hal & %ppn & #Hk & %Hc & %Hr & %Hp & _)".
    iSplitR; [done|]. iExists ppn. iFrame "Hk". by iPureIntro.
  Qed.

  Lemma lock_claims (γl : gname) (lk : mword 64) (str : string)
      (R : CtxId → iProp Σ) (T Dc : iProp Σ) (E : coPset) :
    ↑lockN ⊆ E ->
    (⊢ T -∗ Dc -∗ False) ->
    lock_openable γl lk str R Dc -∗ T ={E}=∗
      WpLock.lk_addr_claim lk 4 ∗
      WpLock.lk_addr_claim (lock_cpu lk) 8 ∗ T.
  (* A6.86: IT IS A PEEK NOW, AND NOTHING COMES OUT OF THE BODY.  A ledger
     cell carries no MAPPING, so after the M4 flip the invariant holds the
     two [lk_addr_claim]s explicitly -- persistent, about the ADDRESS -- and
     this lemma reads them off and closes with what it opened.  The old
     text had to FORGET the owner cell to a raw word to read a claim off it
     and then cross BACK through [TsoCtxShim.ctx_word_of_mem]; that was the
     shim's last live use in the tree, and it dies here. *)
  Proof.
    intros HE Href. iIntros "#Hlock HT".
    iDestruct (WpLock.lock_openable_parts with "Hlock") as (lo) "[#Hfl #Hopen]".
    iMod ("Hopen" $! E T with "[%] [] HT")
      as "(Hbody & HT & [Hclose _])"; [ exact HE | iApply Href | ].
    rewrite /lock_inv.
    iDestruct "Hbody" as "(Hcore & >#Hcl4 & >#Hcl8)".
    iMod ("Hclose" with "[Hcore]") as "_".
    { iNext. rewrite /lock_inv. iFrame "Hcore Hcl4 Hcl8". }
    iModIntro. iFrame "HT". iSplitL; [ iExact "Hcl4" | iExact "Hcl8" ].
  Qed.

  (* A6.119: THE DISCHARGE, at the word.  Release stores 0 and 0 is not in
     [{1}], so the pin CANNOT be carried across that store
     ([TsoCtx.ledger_store_win_pin_ok] wants the stored value in the set) --
     the lock is going free, and a free word is the plain ledger cell.  So the
     order is RETRACT THEN STORE, and the store afterwards is the ordinary one
     the free arm already uses.  The design confirming itself: the only place
     the pin cannot survive is the only place the lock stops being held. *)
  Local Lemma pin_drop_run (g : gstate) (a : Arch.pa) (n : nat)
      (f : nat -> bv 8) (B : nat) (Sf : nat -> TsoMemPa.byteset) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 n, ∃ t : nat,
       TsoCtx.phys_ledger_pin (pa_add a j) (DfracOwn 1) (f j) t B (Sf j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ seq 0 n,
       TsoCtx.phys_ledger (pa_add a j) (DfracOwn 1) (f j)).
  Proof.
    induction n as [|n IH].
    - iIntros "Hgh Hint _". iModIntro. iFrame "Hgh Hint". done.
    - rewrite seq_S !big_sepL_app /=.
      iIntros "Hgh Hint [Hb [(%t & Hlast) _]]".
      iMod (IH with "Hgh Hint Hb") as "(Hgh & Hint & Hb)".
      iMod (TsoCtx.ledger_pin_drop with "Hgh Hint Hlast")
        as "(Hgh & Hint & Hlast)".
      iModIntro. iFrame "Hgh Hint Hb".
      iSplitL; [ by iApply TsoCtx.phys_ledger_at_ledger | done ].
  Qed.

  (* A6.119: the mint's run, the twin of [pin_drop_run] one direction over. *)
  Local Lemma pin_mint_run (g : gstate) (a : Arch.pa) (n : nat)
      (f : nat -> bv 8) (t B : nat) (Sf : nat -> TsoMemPa.byteset) :
    (t <= B)%nat ->
    (forall j : nat, (j < n)%nat -> f j ∈ Sf j) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 n,
       TsoCtx.phys_ledger_at (pa_add a j) (DfracOwn 1) (f j) t) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ seq 0 n, ∃ t' : nat,
       TsoCtx.phys_ledger_pin (pa_add a j) (DfracOwn 1) (f j) t' B (Sf j)).
  Proof.
    intros HtB. induction n as [|n IH]; intros Hf.
    - iIntros "Hgh Hint _". iModIntro. iFrame "Hgh Hint". done.
    - rewrite seq_S !big_sepL_app /=.
      iIntros "Hgh Hint [Hb [Hlast _]]".
      iMod (IH ltac:(intros j Hj; apply Hf; lia) with "Hgh Hint Hb")
        as "(Hgh & Hint & Hb)".
      iMod (TsoCtx.ledger_pin_mint g (pa_add a n) (f n) t B (Sf n) HtB
              (Hf n ltac:(lia)) with "Hgh Hint Hlast")
        as "(Hgh & Hint & Hlast)".
      iModIntro. iFrame "Hgh Hint Hb".
      iSplitL; [ by iExists t | done ].
  Qed.

  Local Lemma lock_word_pin_drop (g : gstate) (B : nat) (lk : mword 64)
      (v : mword 32) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    WpLock.lock_word_pin B lk v ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    WpLock.lock_word lk v.
  Proof.
    iIntros "Hgh Hint [%Hal Hb]".
    iMod (pin_drop_run g lk 4 (nth_byte v) B WpLock.lkw_set
            with "Hgh Hint Hb") as "(Hgh & Hint & Hb)".
    iModIntro. iFrame "Hgh Hint".
    rewrite /WpLock.lock_word TsoCtx.phys_ledger_word4_unfold.
    iSplitR; [done|]. iExact "Hb".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The lock word at +0.                                                 *)
  (* ------------------------------------------------------------------- *)

  (* >>> A6.87: THE READ THAT CONCLUDES NOTHING ALSO OWNS NOTHING.
     A6.78 §(2) predicted this and the M4 flip is what makes it true.  At
     the ledger tier the lock word carries no context, so a read that
     promises its caller NOTHING about the value needs no resource from the
     invariant at all -- the obligation is discharged from RAM-ness (which
     the address claim now carries per byte, A6.87) and the interp, through
     [TsoCtx.ledger_read_any_word_ok].  The lock is never opened.

     STATED AS ITS OWN LEMMA because the AU's obligation is a Coq premise:
     an [_] for it is SHELVED, not a goal, so it has to be passed by name.
     [Hram] rides in front of the telescope the AU fixes. <<< *)
  Local Lemma lock_word_read_any (ea : mword 64) (b : bool)
      (Hram : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
           (V : agent -> nat) (ppn : mword 44),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 4 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (* A6.112: the racy load leaf's no-migration pin; this obligation does
         not need it (it concludes nothing about the value) but its shape
         must match the leaf's. *)
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      emp -∗
      ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
         exists v : mword (8*4),
           tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
             (pa_of ppn ea) (Z.to_N 4) v /\ True⌝.
  Proof.
    intros CIDw img sigma log V ppn Hcan Hoff Hid _.
    iIntros "#Hk Hmem Htso Hctx _".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    rewrite (ktier_pin_id ppn ea Hid).
    iDestruct (TsoCtx.ledger_read_any_word_ok (CID := CIDw)
                 (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
                 ea 4%nat 32 ltac:(lia) Hram with "Htso") as %Hrd4.
    iPureIntro. intros tvr _. destruct (Hrd4 tvr) as [w Hw].
    exists w. split; [exact Hw | done].
  Qed.

  (* holding's [lw a5,0(a0)]: any value, no evidence in or out. *)
  Lemma wp_clw_lockopen_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Tc Dc : iProp Σ)
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
    iDestruct (WpLock.lock_openable_parts with "Hlock") as (lo) "[#Hfl #Hopen]".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R Tc Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock HTc") as "(#Hc4 & #Hc8 & HTc)".
    (* >>> A6.87: THE READ THAT CONCLUDES NOTHING ALSO OWNS NOTHING.
       A6.78 §(2) predicted this and the M4 flip is what makes it true: at
       the ledger tier the lock word carries no context, so a read that
       promises the caller no information about the value needs NO RESOURCE
       FROM THE INVARIANT AT ALL.  The lock is never opened here -- the
       obligation is discharged from RAM-ness (which the address claim now
       carries per byte) and the interp, through
       [TsoCtx.ledger_read_any_word_ok].  The value-UNKNOWN AU ([_exv],
       A6.78) is the shape that lets the datum be a value-INDEPENDENT
       resource; here that resource is [emp].  <<< *)
    iDestruct (WpLock.lk_addr_claim_ram lk 4 with "Hc4") as %Hram.
    iApply (wp_load_s_sconf_au_exv (kt := kt) (ktd := KT0) 4 true false pc rd rs1 imm m n
              (fun w => sign_extend' 64 w)
              (⊤ ∖ ↑minstretN) b
              (fun _ => True) emp%I Tc
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok
              ltac:(solve_ndisj)
              (lock_word_read_any (add_vec (rget m rs1) (sign_extend' 64 imm)) b
                 ltac:(intros j Hj;
                       replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
                         by (symmetry; exact Hpalk);
                       exact (Hram j Hj)))
              with "Hcg Hpc Hinstr [] [HTc] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk).
      iApply (lk_addr_claim_wordw with "Hc4"). }
    { iModIntro. iFrame "HTc". iIntros "_". by iModIntro. }
    iIntros (v). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc _ HTc".
    iApply ("Hcont" $! v CID1 with "[] HTc Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* >>> A6.89: THE HOLDER'S EXACT READ, AND THE NO-MIGRATION FACT THAT
     PAYS FOR IT.  The invariant's held arm carries the acquire's own
     message fragment ([lock_word_ex (Some h0)] = [phys_ledger_word4_vis
     (hart_agent h0) 0]); [TsoCtx.ledger_read_word4_vis_ok] redeems such a
     receipt only for a reader that IS its author, so this obligation --
     discharged at the FRESH [CpuId] the instruction binds -- owes
     [(CIDw : CPU) = h0].

     THAT FACT IS NOT AN ASSUMPTION AND NOT NEW MACHINERY: it is
     [WpNext.wp_next]'s own promise, which the load leaf now threads into
     the obligation (A6.89, [WpSconfMem.wp_load_s_sconf_au_dat]).  At
     [b = false] -- interrupts off, which is exactly what [push_off] buys
     and the literal index [holding()]'s contract is stated at
     (SpecHolding.v) -- the step cannot change harts, so the holder reads
     the word it wrote.  A6.87 §(7) characterized this as a design class:
     at the ctx tower exactness was CONTEXT-relative and migration-safe;
     at the ledger tier with an author receipt it is HART-relative, and the
     kernel's reason it is sound (no migration while holding) had to become
     a stated premise.  This is that premise, and it is one line.

     STATED AS ITS OWN LEMMA for A6.87's reason: the AU's obligation is a
     COQ premise, so an [_] for it is SHELVED, not opened as a goal. <<< *)
  (* >>> A6.119: THE HOLDER'S WORD READ, ON THE VALUE-SET PIN -- §0.35′(iv)
     case 2 verbatim.  The authorship form it replaces was refuted by A6.92:
     `amoswap` writes unconditionally, so a spinner overwrites the word and no
     "this is MY write" claim survives.  What DOES survive is the VALUE: every
     write to a held word is a spinner's or the acquirer's 1, so the pin's set
     [{1}] is preserved by all of them, and a read that lands in [{1}] is
     nonzero -- which is all [holding()] needs.

     THE FLOOR is the acquire's own position, carried here by the holder token
     (§0.34′'s enrichment, A6.119) and discharged against [own_context]. *)
  Local Lemma lock_word_read_pin (ea : mword 64) (b : bool) (B : nat)
      (Hbp : b = false \/ p = zero_reg) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
           (V : agent -> nat) (ppn : mword 44),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 4 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      (TsoCtx.ctx_floor TsoCtx.cur_ctx B ∗
       ∃ v : mword 32, ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ ∗
         WpLock.lock_word_pin B ea v) -∗
      ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
         exists v : mword (8*4),
           tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
             (pa_of ppn ea) (Z.to_N 4) v /\
           neq_vec (sign_extend' 64 v) zero_reg = true⌝.
  Proof.
    intros CIDw img sigma log V ppn Hcan Hoff Hid Hsame.
    iIntros "#Hk Hmem Htso Hctx [#Hfl (%v & %Hvnz & %Hal & Hpin)]".
    iDestruct (TsoCtx.own_context_floor_view (CID := CIDw) TsoCtx.cur_ctx B
                 with "Hctx Hfl") as "[Hctx (%K & #HK & %HBK)]".
    iDestruct (TsoGhost.view_lb_le _ _ _ K B ltac:(lia) with "HK") as "#HB".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    rewrite (ktier_pin_id ppn ea Hid).
    iDestruct (TsoCtx.ledger_read_pin_bytes_ok (CID := CIDw)
                 (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
                 ea 4%nat (DfracOwn 1) (nth_byte v) B WpLock.lkw_set
                 with "Htso HB Hpin") as %Hrd.
    iPureIntro. intros tvr Htvr.
    exists WpLock.lkw_one. split.
    - intros j Hj.
      destruct (Hrd (hart_agent (@cpu_id CIDw)) tvr ltac:(cbn; lia) j
                  ltac:(lia)) as (bb & Hbb & Hin).
      rewrite Hbb. f_equal. symmetry.
      by apply TsoMemPa.elem_of_byteset_sing in Hin.
    - rewrite /WpLock.lkw_one. by vm_compute.
  Qed.

  Local Lemma lock_word_read_vis (ea : mword 64) (b : bool)
      (Hbp : b = false \/ p = zero_reg) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
           (V : agent -> nat) (ppn : mword 44) (v : mword (8*4)),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 4 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      TsoCtx.phys_ledger_word4_vis (hart_agent (@cpu_id CID)) 0 ea (DfracOwn 1) v -∗
      ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
         tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
           (pa_of ppn ea) (Z.to_N 4) v⌝.
  Proof.
    intros CIDw img sigma log V ppn v Hcan Hoff Hid Hsame.
    pose proof (Hsame Hbp) as Hcid.
    assert (Hcid' : (@cpu_id CIDw : CPU) = (@cpu_id CID : CPU)) by exact Hcid.
    assert (Hag : hart_agent (@cpu_id CIDw) = hart_agent (@cpu_id CID))
      by (rewrite Hcid'; reflexivity).
    iIntros "#Hk Hmem Htso Hctx Hw".
    iEval (rewrite -Hag) in "Hw".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    rewrite (ktier_pin_id ppn ea Hid).
    iDestruct (TsoCtx.ledger_read_word4_vis_ok (CID := CIDw)
                 (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
                 ea (DfracOwn 1) v with "Hmem Htso Hw") as %Hrd.
    iPureIntro. intros tvr Hle. exact (Hrd tvr Hle).
  Qed.

  (* >>> A6.92: THE LEDGER AMO GATE.  It is [lock_word_store_plain]'s
     script with the two differences the AMO makes, and both of them are in
     the MACHINE's own arms rather than invented here ([RiscvLang]'s
     [MemRead]/[MemWrite] cases):

     - the exclusive access takes this hart's view TO THE LOG TOP
       ([tv' = length log] on the read, [S (length log)] on the write),
       where an ordinary store leaves it alone.  That is what makes the
       acquire the one instruction in the system that drains, and the
       model says so in the comment on its own arm: *"the view-at-top is
       what mints the acquire receipt in the lock leaves"*;
     - the word that comes out carries the append's OWN MESSAGE FRAGMENT,
       so it is the HELD arm [lock_word_ex (Some h)] rather than the plain
       one -- [TsoCtx.phys_ledger_word4_vis_of_store], the mint A6.88 built
       and nothing had yet called.

     This is `t_rel`'s only producer (A6.91 §(1)). <<< *)
  Local Lemma lock_word_amo_keep (ea : mword 64) (vnew vold : mword 32)
      (B : nat)
      (CIDw : CpuId) (img : bytemap) (sigma : mstate)
      (log : list pwmsg) (V : agent -> nat) :
      (* A6.119: the stored value is 1 -- xv6's acquire is
         [__sync_lock_test_and_set(&lk->locked, 1)] and the 1 is in the
         source.  It is FORCED, not chosen: [byteset] is per-byte, so no
         value set can say "nonzero word", and {1} is the only set a
         spinner's store preserves. *)
      (forall j : nat, (j < 4)%nat ->
         nth_byte vnew j ∈ WpLock.lkw_set j) ->
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      WpLock.lock_word_pin B ea vold ==∗
      gen_heap_interp (hG := riscv_memGS)
        (write_bytes sigma.(mem) ea 4%N vnew) ∗
      tso_interp_of riscv_eraGS img (write_bytes sigma.(mem) ea 4%N vnew)
        (log ++ [PWMsg (snap_of ea 4%N vnew) (hart_agent (@cpu_id CIDw))])%list
        (vstep (hart_agent (@cpu_id CIDw)) (S (length log))
           (log ++ [PWMsg (snap_of ea 4%N vnew) (hart_agent (@cpu_id CIDw))])%list V) ∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
      (* the pin SURVIVES, at the position it already had: the spinner's
         store is 1 and 1 is in the set, which is the whole reason a
         value-shaped window works here where an author-shaped one cannot. *)
      (* NO EXPORT HERE, and that is the difference between the two gates:
         the export's justification is "the acquirer's own view IS the
         position", and a LOSING spinner is not the acquirer -- [B] is the
         incumbent holder's.  A loser leaves with nothing but the interp. *)
      WpLock.lock_word_pin B ea vnew.
  Proof.
    intros Hset. iIntros "Hm Htso Hctx [%Hal Hb]".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    iDestruct (tso_interp_of_bound with "Htso") as %Hbd.
    set (log' := (log ++ [PWMsg (snap_of ea 4%N vnew)
                            (hart_agent (@cpu_id CIDw))])%list).
    set (V' := vstep (hart_agent (@cpu_id CIDw)) (S (length log)) log' V).
    assert (Hlen' : length log' = S (length log))
      by (rewrite /log' length_app /=; lia).
    assert (Hpin' : forall h, (NCPU <= h)%nat -> V' h = length log').
    { intros h Hh. rewrite /V' /vstep. case_decide as Hd.
      - exfalso. subst h. pose proof (fin_to_nat_lt (@cpu_id CIDw)).
        rewrite /hart_agent in Hh. lia.
      - destruct (lt_dec h NCPU); [lia | reflexivity]. }
    assert (Htvmono : forall c : CPU, (V (hart_agent c) <= V' (hart_agent c))%nat).
    { intros c. rewrite /V' /vstep. case_decide as Hd.
      - have := Hbd (hart_agent c). lia.
      - destruct (lt_dec (hart_agent c) NCPU) as [|Hge]; first lia.
        exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hge. lia. }
    assert (Htvtop : forall c : CPU, (V' (hart_agent c) <= length log')%nat).
    { intros c. rewrite Hlen' /V' /vstep. case_decide as Hd; first lia.
      destruct (lt_dec (hart_agent c) NCPU) as [|Hge].
      - have := Hbd (hart_agent c). lia.
      - exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hge. lia. }
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    iMod (TsoCtx.ledger_store_win_pin_ok (CID := CIDw)
            (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
            (gs_of img (write_bytes sigma.(mem) ea 4%N vnew) log' V'
               sigma.(sregs) sigma.(mdev))
            ea 4%N vold vnew B WpLock.lkw_set
            (* the Sg premise, off [TsoCtx.tso_pa_off] -- the offset-from-
               address bridge the window laws already had and only [Local]
               kept from its first caller. *)
            (fun a => WpLock.lkw_set (TsoCtx.tso_pa_off ea a))
            ltac:(vm_compute; discriminate)
            ltac:(intros j Hj; cbn beta;
                  rewrite TsoCtx.tso_pa_off_add; [reflexivity|lia])
            Hset eq_refl eq_refl eq_refl Htvmono Htvtop
            with "Hm Htso Hb") as "(Hm & Htso & Hnew)".
    iModIntro. iFrame "Hm".
    iSplitL "Htso".
    { rewrite -(tso_interp_of_at_gs riscv_eraGS img
                  (write_bytes sigma.(mem) ea 4%N vnew) log' V'
                  sigma.(sregs) sigma.(mdev) Hpin').
      iExact "Htso". }
    iFrame "Hctx".
    rewrite /WpLock.lock_word_pin. iFrame "Hnew".
    iPureIntro. exact Hal.
  Qed.

  Local Lemma lock_word_amo_mint (ea : mword 64) (vnew : mword 32)
      (CIDw : CpuId) (img : bytemap) (sigma : mstate)
      (log : list pwmsg) (V : agent -> nat) :
      (* A6.119: the stored value is 1 -- xv6's acquire is
         [__sync_lock_test_and_set(&lk->locked, 1)] and the 1 is in the
         source.  It is FORCED, not chosen: [byteset] is per-byte, so no
         value set can say "nonzero word", and {1} is the only set a
         spinner's store preserves. *)
      (forall j : nat, (j < 4)%nat ->
         nth_byte vnew j ∈ WpLock.lkw_set j) ->
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      (∃ vold : mword 32, TsoCtx.phys_ledger_word4 ea (DfracOwn 1) vold) ==∗
      gen_heap_interp (hG := riscv_memGS)
        (write_bytes sigma.(mem) ea 4%N vnew) ∗
      tso_interp_of riscv_eraGS img (write_bytes sigma.(mem) ea 4%N vnew)
        (log ++ [PWMsg (snap_of ea 4%N vnew) (hart_agent (@cpu_id CIDw))])%list
        (vstep (hart_agent (@cpu_id CIDw)) (S (length log))
           (log ++ [PWMsg (snap_of ea 4%N vnew) (hart_agent (@cpu_id CIDw))])%list V) ∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
      (* the held arm's pin, floored at the position this AMO just took... *)
      WpLock.lock_word_pin (S (length log)) ea vnew ∗
      (* ...and the EXPORT: the acquirer's own view IS that position, so the
         absorb needs no [llb] here -- [hart_view_lb_now] gives the receipt
         free off the post-state and [ctx_bound_raise] turns it into the
         floor the holder token carries away (§0.38′'s agreed one form). *)
      TsoCtx.ctx_floor TsoCtx.cur_ctx (S (length log)).
  Proof.
    intros Hset. iIntros "Hm Htso Hctx (%vold & %Hal & Hb)".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    iDestruct (tso_interp_of_bound with "Htso") as %Hbd.
    set (log' := (log ++ [PWMsg (snap_of ea 4%N vnew)
                            (hart_agent (@cpu_id CIDw))])%list).
    set (V' := vstep (hart_agent (@cpu_id CIDw)) (S (length log)) log' V).
    assert (Hlen' : length log' = S (length log))
      by (rewrite /log' length_app /=; lia).
    assert (Hpin' : forall h, (NCPU <= h)%nat -> V' h = length log').
    { intros h Hh. rewrite /V' /vstep. case_decide as Hd.
      - exfalso. subst h. pose proof (fin_to_nat_lt (@cpu_id CIDw)).
        rewrite /hart_agent in Hh. lia.
      - destruct (lt_dec h NCPU); [lia | reflexivity]. }
    assert (Htvmono : forall c : CPU, (V (hart_agent c) <= V' (hart_agent c))%nat).
    { intros c. rewrite /V' /vstep. case_decide as Hd.
      - have := Hbd (hart_agent c). lia.
      - destruct (lt_dec (hart_agent c) NCPU) as [|Hge]; first lia.
        exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hge. lia. }
    assert (Htvtop : forall c : CPU, (V' (hart_agent c) <= length log')%nat).
    { intros c. rewrite Hlen' /V' /vstep. case_decide as Hd; first lia.
      destruct (lt_dec (hart_agent c) NCPU) as [|Hge].
      - have := Hbd (hart_agent c). lia.
      - exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hge. lia. }
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    iMod (TsoCtx.ledger_store_win_at_ok (CID := CIDw)
            (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
            (gs_of img (write_bytes sigma.(mem) ea 4%N vnew) log' V'
               sigma.(sregs) sigma.(mdev))
            ea 4%N vold vnew
            ltac:(vm_compute; discriminate) eq_refl eq_refl eq_refl
            Htvmono Htvtop with "Hm Htso Hb") as "(Hm & Htso & #Hmsg & Hnew)".
    (* the pin, at the store's own position *)
    iMod (pin_mint_run
            (gs_of img (write_bytes sigma.(mem) ea 4%N vnew) log' V'
               sigma.(sregs) sigma.(mdev))
            ea 4 (nth_byte vnew) (S (length log)) (S (length log))
            WpLock.lkw_set ltac:(lia) Hset with "Hm Htso Hnew")
      as "(Hm & Htso & Hpin)".
    (* the export.  [hart_view_lb_now] lives in the KPT lane's [CtxPinMint];
       [TsoCtx]'s own [hart_view_lb_get] gives the same receipt here without
       coupling the two lanes' files -- its log-top premise is exactly what an
       AMO establishes, and [T := 0] is free ([TsoGhost.llb_0]) because all we
       want back is the receipt. *)
    assert (HV'h : V' (hart_agent (@cpu_id CIDw)) = S (length log)).
    { rewrite /V' /vstep. case_decide as Hd;
        [ reflexivity | exfalso; by apply Hd ]. }
    assert (Htop : (length (gs_of img (write_bytes sigma.(mem) ea 4%N vnew)
                              log' V' sigma.(sregs) sigma.(mdev)).(glog)
                    <= (gs_of img (write_bytes sigma.(mem) ea 4%N vnew)
                          log' V' sigma.(sregs) sigma.(mdev)).(gtv)
                         (@cpu_id CIDw))%nat).
    { cbn [glog gtv gs_of]. rewrite Hlen' HV'h. lia. }
    iDestruct (TsoCtx.hart_view_lb_get (CID := CIDw) _ 0%nat Htop
                 with "Htso []") as "(Htso & #Hvlb & _)";
      [ iApply TsoGhost.llb_0 | ].
    iMod (TsoCtx.ctx_bound_raise (CID := CIDw) TsoCtx.cur_ctx
            (V' (hart_agent (@cpu_id CIDw))) with "Hctx Hvlb")
      as "[Hctx #Hfl]".
    iModIntro. iFrame "Hm".
    iSplitL "Htso".
    { rewrite -(tso_interp_of_at_gs riscv_eraGS img
                  (write_bytes sigma.(mem) ea 4%N vnew) log' V'
                  sigma.(sregs) sigma.(mdev) Hpin').
      iExact "Htso". }
    iFrame "Hctx".
    iSplitL "Hpin".
    { rewrite /WpLock.lock_word_pin. iFrame "Hpin".
      iPureIntro. exact Hal. }
    rewrite -HV'h. iExact "Hfl".
  Qed.

  (* [h0] is the ENTRY hart's identity, LET-BOUND OUTSIDE the [wp_next]
     lambda: the holder token describes who currently holds the lock, a
     fact fixed before this load even runs, so writing [cpu_id] literally
     inside the continuation would silently (and here, since [cpu_id]
     prints the same at every hart, INVISIBLY) rebind it to the hart the
     step resumes on. *)
  Lemma wp_clw_lockopen_locked_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    pa = lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    (* A6.89: PUSH_OFF'S PROMISE, AS A PREMISE.  [holding()] runs with
       interrupts off, so this step cannot change harts and the holder's
       own-write receipt is redeemable here; see [lock_word_read_vis].
       [holding]'s contract is already stated at the LITERAL [false]
       (SpecHolding.v), so its call site discharges this by [eq_refl]. *)
    (b = false \/ p = zero_reg) ->
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
    intros pa h0 Hpalk Hrd Hrdok Hbp Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iDestruct (WpLock.lock_openable_parts with "Hlock") as (lo) "[#Hfl #Hopen]".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R (locked γl h0) Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock Htok") as "(#Hc4 & #Hc8 & Htok)".
    (* >>> A6.119: THE DATUM IS THE VALUE-SET PIN, and the read is the RACY
       one (_exv), because the word is racy -- A6.92.  The token's own floor
       is destructured OUTSIDE the atomic update: [Res] and [Post] are fixed
       before the invariant opens, so the pin's [B] has to be a name in scope
       here, and the holder's token is where it lives (§0.34′'s enrichment).
       [lock_pos_agree], inside, is what says the token's [B] is the one the
       invariant minted. <<< *)
    iDestruct "Htok" as (Btok) "[Htok #Hflok]".
    iApply (wp_load_s_sconf_au_exv (kt := kt) (ktd := KT0) 4 true false pc rd rs1 imm m n
              (fun w => sign_extend' 64 w)
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              (fun w => neq_vec (sign_extend' 64 w) zero_reg = true)
              (TsoCtx.ctx_floor TsoCtx.cur_ctx Btok ∗
               ∃ v : mword 32, ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ ∗
                 WpLock.lock_word_pin Btok
                   (add_vec (rget m rs1) (sign_extend' 64 imm)) v)%I
              (lock_frag_at γl (Some (h0, true)) Btok)
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok
              ltac:(solve_ndisj)
              (lock_word_read_pin (add_vec (rget m rs1) (sign_extend' 64 imm))
                 b Btok Hbp)
              with "Hcg Hpc Hinstr [] [Htok] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk). iApply (lk_addr_claim_wordw with "Hc4"). }
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk).
      iMod ("Hopen" $! (⊤ ∖ ↑minstretN)
              (lock_frag_at γl (Some (h0, true)) Btok) with "[%] [] Htok")
        as "(Hbody & Htok & [Hclose _])";
        [solve_ndisj | iIntros "Ht"; iApply Href; iExists Btok; iFrame "Ht Hflok" |].
      iDestruct "Hbody" as "(Hbody & >#Hcl4 & >#Hcl8)".
      iDestruct "Hbody" as (w st B) "(>Hword & >Hcpu & >Hg & Hbr)".
      iDestruct (lock_pos_agree with "Hg Htok") as %[-> ->].
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      iModIntro.
      iSplitL "Hword".
      { iFrame "Hflok". iExists w. iSplitR; [done|]. iExact "Hword". }
      iIntros "[_ (%w' & %Hwnz' & Hword)]".
      iMod ("Hclose" with "[Hword Hcpu Hg]") as "_".
      { iNext. rewrite /lock_inv /lock_body. iFrame "Hcl4 Hcl8".
        iExists w', (Some (h0, true)), Btok. iFrame "Hcpu Hg Hword".
        iRight. iPureIntro. split; [ discriminate | exact Hwnz' ]. }
      iModIntro. iFrame "Htok". }
    iIntros (v). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc %Hvnz Htok".
    iApply ("Hcont" $! v CID1 with "[] [] [Htok] Hcg Hpc").
    - iPureIntro. exact Hs1.
    - iPureIntro. exact Hvnz.
    - iExists Btok. iFrame "Htok Hflok".
  Qed.

  (* >>> A6.92: THE LEDGER WORD, READ FLAT.  The AMO's exclusive read is
     "drain, then read memory" -- [RiscvLang]'s arm reads the FLAT cache and
     takes the view to the log top -- so what its node obligation wants is
     not a ledger fact at all but the four gen_heap cells.  A ledger byte
     carries one ([TsoCtx.phys_ledger_forget]), and [phys_valid] reads it
     off the interp.  This replaces the pre-flip [s_mem_chunk] call, which
     wanted the [mem_pointsto] tower the lock word left at the M4 flip. <<< *)
  (* A6.119: at EITHER arm.  The AMO's exclusive read wants the four
     gen_heap cells, and both the free word and the held arm's pin own a
     [phys_pointsto] per byte -- the pin is the same cells with the option arm
     set, which is why the read never had to know which arm it is on. *)
  Local Lemma lock_word_flat_bytes (st : lock_state) (B : nat) (a : Arch.pa)
      (v : mword 32) (mm : _) :
    gen_heap_interp (hG := riscv_memGS) mm -∗
    WpLock.lock_word_at st B a v -∗
    ⌜forall j : nat, (j < 4)%nat -> mm !! (pa_add a j) = Some (nth_byte v j)⌝.
  Proof.
    iIntros "Hm Hw".
    iAssert ([∗ list] j ∈ seq 0 4, phys_pointsto (pa_add a j) (DfracOwn 1)
               (nth_byte v j))%I with "[Hw]" as "Hb".
    { destruct st as [[i o]|].
      - rewrite /WpLock.lock_word_at /WpLock.lock_word_pin.
        iDestruct "Hw" as "[_ Hb]".
        iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "(%t & Hp & _)".
        iExact "Hp".
      - rewrite /WpLock.lock_word_at /WpLock.lock_word
                TsoCtx.phys_ledger_word4_unfold.
        iDestruct "Hw" as "[_ Hb]".
        iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "Hp".
        by iApply TsoCtx.phys_ledger_forget. }
    rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
    iDestruct (big_sepL_lookup _ (seq 0 4) j j with "Hb") as "Hbj".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iApply (phys_valid with "Hm Hbj").
  Qed.

  (* >>> A6.89: THE PLAIN WORD-4 LEDGER STORE, which is release's [sw x0].
     [word_pointsto_wpay_mint_c]'s shape (SmodeCorePt.v) at width 4 and
     WITHOUT the window payload: the lock WORD carries no [own] record --
     only the owner CELL does -- so the store gate is the bare
     [ledger_store_win_at_ok] and what comes out is the ordinary
     [phys_ledger_word4], which is [lock_word] and therefore
     [lock_word_ex None]: a free lock's word is nobody's own write. <<< *)
  Local Lemma lock_word_store_plain (ea : mword 64) (vnew : mword 32) (b : bool) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate)
           (log : list pwmsg) (V : agent -> nat) (ppn : mword 44),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 4 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      (* A6.119: the datum is the HELD arm's pin.  Release stores 0 and 0 is
         not in [{1}], so the pin cannot be carried across -- it is RETRACTED
         first ([lock_word_pin_drop]) and the store afterwards is the ordinary
         free-word one.  The only place the pin cannot survive is the only
         place the lock stops being held. *)
      (∃ (B : nat) (vold : mword 32), WpLock.lock_word_pin B ea vold) ==∗
      gen_heap_interp (hG := riscv_memGS)
        (write_bytes sigma.(mem) (pa_of ppn ea) (Z.to_N 4) vnew) ∗
      tso_interp_of riscv_eraGS img
        (write_bytes sigma.(mem) (pa_of ppn ea) (Z.to_N 4) vnew)
        (log ++ [PWMsg (snap_of (pa_of ppn ea) (Z.to_N 4) vnew)
                   (hart_agent (@cpu_id CIDw))])%list
        (vstep (hart_agent (@cpu_id CIDw)) (V (hart_agent (@cpu_id CIDw)))
           (log ++ [PWMsg (snap_of (pa_of ppn ea) (Z.to_N 4) vnew)
                      (hart_agent (@cpu_id CIDw))])%list V) ∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
      TsoCtx.phys_ledger_word4 ea (DfracOwn 1) vnew.
  Proof.
    intros CIDw img sigma log V ppn Hcan Hoff Hid _.
    rewrite (ktier_pin_id ppn ea Hid).
    iIntros "#Hk Hm Htso Hctx (%B0 & %vold & Hpin0)".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    iMod (lock_word_pin_drop
            (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
            B0 ea vold with "Hm Htso Hpin0") as "(Hm & Htso & Hw0)".
    rewrite -(tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
                sigma.(sregs) sigma.(mdev) Hpin).
    iDestruct "Hw0" as "[%Hal Hb]".
    iDestruct (tso_interp_of_bound with "Htso") as %Hbd.
    set (log' := (log ++ [PWMsg (snap_of ea (Z.to_N 4) vnew)
                            (hart_agent (@cpu_id CIDw))])%list).
    set (V' := vstep (hart_agent (@cpu_id CIDw))
                 (V (hart_agent (@cpu_id CIDw))) log' V).
    assert (Hpin' : forall h, (NCPU <= h)%nat -> V' h = length log').
    { intros h Hh. rewrite /V' /vstep. case_decide as Hd.
      - exfalso. subst h. pose proof (fin_to_nat_lt (@cpu_id CIDw)).
        rewrite /hart_agent in Hh. lia.
      - destruct (lt_dec h NCPU); [lia | reflexivity]. }
    assert (Htvc : forall c : CPU, V' (hart_agent c) = V (hart_agent c)).
    { intros c. rewrite /V' /vstep. case_decide as Hd.
      - by rewrite Hd.
      - destruct (lt_dec (hart_agent c) NCPU) as [|Hge]; first reflexivity.
        exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hge. lia. }
    assert (Htvmono : forall c : CPU, (V (hart_agent c) <= V' (hart_agent c))%nat)
      by (intros c; rewrite Htvc; lia).
    assert (Htvtop : forall c : CPU, (V' (hart_agent c) <= length log')%nat).
    { intros c. rewrite Htvc /log' length_app /=.
      have := Hbd (hart_agent c). lia. }
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    iMod (TsoCtx.ledger_store_win_at_ok (CID := CIDw)
            (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
            (gs_of img (write_bytes sigma.(mem) ea (Z.to_N 4) vnew) log' V'
               sigma.(sregs) sigma.(mdev))
            ea (Z.to_N 4) vold vnew
            ltac:(vm_compute; discriminate) eq_refl eq_refl eq_refl
            Htvmono Htvtop with "Hm Htso Hb") as "(Hm & Htso & _ & Hnew)".
    iModIntro. iFrame "Hm Hctx".
    iSplitL "Htso".
    { rewrite -(tso_interp_of_at_gs riscv_eraGS img
                  (write_bytes sigma.(mem) ea (Z.to_N 4) vnew) log' V'
                  sigma.(sregs) sigma.(mdev) Hpin').
      iExact "Htso". }
    rewrite /TsoCtx.phys_ledger_word4. iSplitR; [done|].
    iApply (big_sepL_impl with "Hnew"). iIntros "!>" (k j _) "H".
    by iApply TsoCtx.phys_ledger_at_ledger.
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
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Dc Out : iProp Σ)
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
    (* A6.89: the payload comes back DEPOSITED ([lock_pay], the parked
       record the free arm holds) rather than as a bare ∃ξ -- the M4 free
       arm is [lock_pay R] and the releaser is where [own_context] is, so
       the deposit belongs at the release call site ([lock_pay_intro]). *)
    lock_pay R -∗
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
    iDestruct (WpLock.lock_openable_parts with "Hlock") as (lo) "[#Hfl #Hopen]".
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
    (* >>> A6.89: THE DATUM IS THE LEDGER WORD, so the release store goes
       through [_dat] with [lock_word_store_plain] as its write gate. <<< *)
    iApply (wp_store_s_sconf_au_dat (kt := kt) (ktd := KT0) 4 false pc (mword_of_int 0 : mword 5) rs1 imm m n
              (trunc32 (tp_pin m !!! Regidx (mword_of_int 0 : mword 5)))
              Out
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              (∃ (B : nat) (vold : mword 32), WpLock.lock_word_pin B
                 (add_vec (rget m rs1) (sign_extend' 64 imm)) vold)%I
              (TsoCtx.phys_ledger_word4
                 (add_vec (rget m rs1) (sign_extend' 64 imm)) (DfracOwn 1)
                 (trunc32 (tp_pin m !!! Regidx (mword_of_int 0 : mword 5))))
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (tp_pin m !!! Regidx (mword_of_int 0 : mword 5)))
              ltac:(solve_ndisj)
              (lock_word_store_plain (add_vec (rget m rs1) (sign_extend' 64 imm))
                 (trunc32 (tp_pin m !!! Regidx (mword_of_int 0 : mword 5))) b)
              with "Hcg Hpc Hinstr [] [Htok HRes Hfin] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk). iApply (lk_addr_claim_wordw with "Hc4"). }
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with lk
        by (symmetry; exact Hpalk).
      iMod ("Hopen" $! (⊤ ∖ ↑minstretN) (locked_pre γl cpu_id) with "[%] [] Htok")
        as "(Hbody & Htok & Hchoice)"; [solve_ndisj| iApply Href |].
      (* A6.87: peel the M4 invariant's two address claims; hand them
         back at the close.  Everything between is the pre-flip text. *)
      iDestruct "Hbody" as "(Hbody & >#Hcl4 & >#Hcl8)".
      iDestruct "Hbody" as (w st B) "(>Hword & >Hcpu & >Hg & Hbr)".
      iMod (lock_give γl st B cpu_id with "Hg Htok") as "(%Hst & Hg & Hfrag)".
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      subst st.
      (* the lock is in release's window, so the cpu field is home WHOLE and
         at 0 -- the finisher's view of it is unchanged (WpLock.v). *)
      iEval (rewrite lk_cpu_res_win) in "Hcpu".
      iModIntro.
      (* A6.89: at [Some (i,false)] the word still carries the AMO's own
         receipt ([lk_wex]); the store gate wants the plain ledger word,
         and release is exactly where the receipt is spent. *)
      iSplitL "Hword"; [ iExists B, w; iExact "Hword" | ].
      iIntros "Hword".
      iApply ("Hfin" with "Hchoice Hg Hfrag [Hword] [Hcpu] HRes").
      { (* A6.89: the WORD slot is [lock_word_fresh] now -- the ledger word
           plus its address claim, the invariant's own, peeled at the open. *)
        rewrite /lock_word_fresh. iFrame "Hcl4".
        rewrite /lock_word -Hzero. iExact "Hword". }
      (* A6.89: the finisher takes the owner cell as [lk_cpu_fresh] -- the
         cell PLUS the address claim a ledger cell does not carry.  The
         claim is the invariant's own, peeled at the open. *)
      { rewrite /lk_cpu_fresh. iFrame "Hcl8". iExact "Hcpu". } }
    iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc HOut".
    iApply ("Hcont" $! CID1 with "[] HOut Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The cpu word at +16.  It belongs to the invariant; what a caller     *)
  (* brings is the ghost evidence that decides what the word says.        *)
  (* ------------------------------------------------------------------- *)

  (* >>> A6.89: THE OWNER CELL'S NO-EVIDENCE READ ALSO OWNS NOTHING, and it
     is [wp_clw_lockopen_s_sconf]'s argument one field over: at the ledger
     tier a read that promises its caller NOTHING about the value needs no
     resource from the invariant at all, so the lock is never opened.
     RAM-ness comes from the invariant's persistent 8-byte address claim,
     which [lock_claims] peeks out without opening the body. <<< *)
  Local Lemma lock_cell_read_any (ea : mword 64) (b : bool)
      (Hram : forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
           (V : agent -> nat) (ppn : mword 44),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 8 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (* A6.112: the racy load leaf's no-migration pin; this obligation does
         not need it (it concludes nothing about the value) but its shape
         must match the leaf's. *)
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      emp -∗
      ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
         exists v : mword (8*8),
           tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
             (pa_of ppn ea) (Z.to_N 8) v /\ True⌝.
  Proof.
    intros CIDw img sigma log V ppn Hcan Hoff Hid _.
    iIntros "#Hk Hmem Htso Hctx _".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    rewrite (ktier_pin_id ppn ea Hid).
    iDestruct (TsoCtx.ledger_read_any_word_ok (CID := CIDw)
                 (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
                 ea 8%nat 64 ltac:(lia) Hram with "Htso") as %Hrd8.
    iPureIntro. intros tvr _. destruct (Hrd8 tvr) as [w Hw].
    exists w. split; [exact Hw | done].
  Qed.

  (* holding's [ld a5,16(a0)] with NO evidence: the recorded owner word is
     whatever it is (a non-holder learns nothing about it -- which is why
     holding() may answer either way, and acquire's panic arm is real). *)
  Lemma wp_cld_lkcpu_lockopen_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Tc Dc : iProp Σ)
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
    iDestruct (WpLock.lock_openable_parts with "Hlock") as (lo) "[#Hfl #Hopen]".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R Tc Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock HTc") as "(#Hc4 & #Hc8 & HTc)".
    iDestruct (WpLock.lk_addr_claim_ram (lock_cpu lk) 8 with "Hc8") as %Hram.
    iApply (wp_load_s_sconf_au_exv (kt := kt) (ktd := KT0) 8 true false pc rd rs1 imm m n
              (fun w => w)
              (⊤ ∖ ↑minstretN) b
              (fun _ => True) emp%I Tc
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 data2_ext_8 Hrd Hrdok
              ltac:(solve_ndisj)
              (lock_cell_read_any (add_vec (rget m rs1) (sign_extend' 64 imm)) b
                 ltac:(intros j Hj;
                       replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with (lock_cpu lk)
                         by (symmetry; exact Hpacpu);
                       exact (Hram j Hj)))
              with "Hcg Hpc Hinstr [] [HTc] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with (lock_cpu lk)
        by (symmetry; exact Hpacpu).
      iApply (lk_addr_claim_wordw with "Hc8"). }
    { iModIntro. iFrame "HTc". iIntros "_". by iModIntro. }
    iIntros (v). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc _ HTc".
    iApply ("Hcont" $! v CID1 with "[] HTc Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* >>> A6.89: THE HOLDER'S EXACT READ OF THE OWNER CELL -- the SECOND
     field of A6.87 §(7)'s "one item, two fields", and it is the word
     leaf's argument verbatim.  [lk_cpu_pay_vis] (A6.84) is the held arm's
     author receipt; [TsoCtx.ledger_read_wpay_bytes_vis_ok] redeems it only
     for the reader that IS its author, and the no-migration pin the load
     leaf now threads is what identifies the two.  [B := 0] because the
     author arm is what pays ([TsoGhost.view_lb_0]). <<< *)
  Local Lemma lock_cell_read_vis (ea lk : mword 64) (b : bool) (lo : nat)
      (Hea : ea = lock_cpu lk)
      (Hbp : b = false \/ p = zero_reg) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
           (V : agent -> nat) (ppn : mword 44) (v : mword (8*8)),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 8 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      lk_cpu_cell_ex lo lk v (Some (@cpu_id CID)) -∗
      ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
         tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
           (pa_of ppn ea) (Z.to_N 8) v⌝.
  Proof.
    subst ea.
    intros CIDw img sigma log V ppn v Hcan Hoff Hid Hsame.
    pose proof (Hsame Hbp) as Hcid.
    assert (Hcid' : (@cpu_id CIDw : CPU) = (@cpu_id CID : CPU)) by exact Hcid.
    assert (Hag : hart_agent (@cpu_id CIDw) = hart_agent (@cpu_id CID))
      by (rewrite Hcid'; reflexivity).
    iIntros "#Hk Hmem Htso Hctx Hcell".
    iEval (rewrite /lk_cpu_cell_ex) in "Hcell".
    (* A6.115: the cell grew its per-agent anchor; the holder's exact read
       does not consume it (its exactness comes from the author fragment). *)
    iDestruct "Hcell" as (own) "(_ & _ & Hb)".
    iEval (simpl) in "Hb".
    iEval (rewrite -Hag) in "Hb".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    rewrite (ktier_pin_id ppn (lock_cpu lk) Hid).
    iDestruct (TsoCtx.ledger_read_wpay_bytes_vis_ok (CID := CIDw)
                 (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
                 (lock_cpu lk) 8%nat v (DfracOwn 1) 0
                 (fun j => TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo)
                 with "Hmem Htso [] [Hb]") as %Hrd.
    { iApply TsoGhost.view_lb_0. }
    { rewrite /lk_cpu_pay_vis. iExact "Hb". }
    iPureIntro. intros tvr Hle. exact (Hrd tvr Hle).
  Qed.

  (* >>> A6.119: THE [notheld] READ'S OBLIGATION, ON THE COMPLETED KIT.
     The pre-flip generic concluded a predicate about the loaded word from a
     pure premise about the GHOST state -- which A6.92 refuted: the read is
     racy and the word need not be [lk_cpu_val st] at all.  What survives is
     weaker and is all [holding()] needs: whatever the read lands on, it is
     not THIS hart's [struct cpu] pointer.

     THE THREE INPUTS, and each is now a landed piece:
       - the window and the per-agent record, out of the cell
         ([WpLock.lk_cpu_cell_ex_pay], [lk_own_ok_some] at a state this hart
         does not hold);
       - the ANCHOR, out of the cell's own invariant ([lk_own_anchored],
         A6.115) -- free, and for every hart rather than only the creator;
       - the FLOOR, [ctx_floor cur_ctx lo] against [own_context]
         ([TsoCtx.own_context_floor_view]), which is why this leaf takes
         [lock_openable_c] and not [lock_openable] (A6.112 §3b).
     Existence of a read value comes from [ledger_read_any_word_ok], exactly
     as the "no evidence" read does. <<< *)
  Local Lemma lock_cell_read_notheld (ea lk : mword 64) (b : bool) (lo : nat)
      (γl : gname) (s : string) (R : CtxId → iProp Σ)
      (Hea : ea = lock_cpu lk)
      (Hbp : b = false \/ p = zero_reg)
      (Hram : forall j : nat, (j < 8)%nat ->
                addr_is_ram (pa_add (lock_cpu lk) j)) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
           (V : agent -> nat) (ppn : mword 44),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 8 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      (* A6.119: the resource is the invariant's WHOLE BODY, not just the
         cell.  The atomic update hands [Res] over and takes [Res] back, so
         anything existential inside it comes back at FRESH witnesses -- and
         the close needs the body's own [v]/[st], not some other pair.
         Handing the body through is what keeps the two ends tied; the
         obligation itself reads only the cell out of it. *)
      (TsoCtx.ctx_floor TsoCtx.cur_ctx lo ∗
       ∃ (v : mword 32) (st : lock_state) (B : nat),
         ⌜lk_ex st <> Some (@cpu_id CID)⌝ ∗
         lock_word_at st B lk v ∗ lk_cpu_res lo st lk s ∗
         lock_auth_at γl st B ∗
         (* the branch stays UNDER A LATER: it holds [lock_pay R], and [R] is
            not timeless.  The obligation never looks at it. *)
         ▷ (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗
              lock_frag γl None ∗ lock_pay R
            ∨ ⌜st <> None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)) -∗
      ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
         exists w : mword (8*8),
           tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
             (pa_of ppn ea) (Z.to_N 8) w /\ w <> cpus_ptr (@cpu_id CID)⌝.
  Proof.
    subst ea.
    intros CIDw img sigma log V ppn Hcan Hoff Hid Hsame.
    pose proof (Hsame Hbp) as Hcid.
    assert (Hcid' : (@cpu_id CIDw : CPU) = (@cpu_id CID : CPU)) by exact Hcid.
    assert (Hag : hart_agent (@cpu_id CIDw) = hart_agent (@cpu_id CID))
      by (rewrite Hcid'; reflexivity).
    iIntros "#Hk Hmem Htso Hctx [#Hfl (%v & %st & %B & %Hne & _ & Hcpures & _ & _)]".
    iEval (rewrite /lk_cpu_res) in "Hcpures".
    iDestruct "Hcpures" as "[Hcell _]".
    (* the window, at either arm, plus the record and the anchor *)
    iDestruct (lk_cpu_cell_ex_pay with "Hcell") as (own) "(%Hok & #Han & Hb)".
    destruct (lk_own_ok_some (lk_ex st) own (@cpu_id CID) Hok Hne) as (t & Ht).
    (* the FLOOR, against this hart's own token *)
    iDestruct (TsoCtx.own_context_floor_view (CID := CIDw) TsoCtx.cur_ctx lo
                 with "Hctx Hfl") as "[Hctx (%K & #HK & %HloK)]".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    rewrite (ktier_pin_id ppn (lock_cpu lk) Hid).
    (* the two [ledger_vis]: the floor by the receipt, the anchor off the
       cell's invariant *)
    iAssert (TsoCtx.ledger_vis (hart_agent (@cpu_id CIDw)) K lo) as "#Hfv".
    { iApply TsoCtx.ledger_vis_below. lia. }
    iAssert (TsoCtx.ledger_vis (hart_agent (@cpu_id CIDw)) lo t) as "#Hav".
    { rewrite Hag. iApply ("Han" $! (hart_agent (@cpu_id CID)) t).
      iPureIntro. exact Ht. }
    iDestruct (lkcpu_read_not_mine (CID := CIDw)
                 (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
                 lk (DfracOwn 1) (fun j => nth_byte (lk_cpu_val st) j)
                 own lo t K ltac:(rewrite Hag; exact Ht)
                 with "Htso HK Hfv Hav [Hb]") as %Hne'.
    { rewrite /lk_cpu_pay. iExact "Hb". }
    iDestruct (TsoCtx.ledger_read_any_word_ok (CID := CIDw)
                 (gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev))
                 (lock_cpu lk) 8%nat 64 ltac:(lia) Hram with "Htso") as %Hrd.
    iPureIntro. intros tvr Htvr.
    destruct (Hrd tvr) as (w & Hw). exists w. split; [exact Hw|].
    rewrite -Hcid'. exact (Hne' tvr ltac:(cbn; lia) w Hw).
  Qed.

  (* the same read as the HOLDER: the token pins the word to mycpu(), so
     holding() returns 1. *)
  (* [h0]/[cpuv] are the ENTRY hart's identity, LET-BOUND OUTSIDE the
     [wp_next] lambda: they describe who the memory word [lk->cpu] was
     written for (a fact about the ENTRY hart, fixed before this load
     even runs), so writing them literally inside the continuation would
     silently rebind them to whichever hart the step resumes on. *)
  Lemma wp_cld_lkcpu_lockopen_locked_s_sconf
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    let cpuv := mycpu_ret cid_word in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    (* A6.89: push_off's promise, as a premise -- see [lock_cell_read_vis]
       and the word leaf's twin.  [holding()] is stated at the literal
       [false], so its call site discharges this by [eq_refl]. *)
    (b = false \/ p = zero_reg) ->
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
    intros pa h0 cpuv Hpacpu Hrd Hrdok Hbp Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iDestruct (WpLock.lock_openable_parts with "Hlock") as (lo) "[#Hfl #Hopen]".
    iApply fupd_wp.
    iMod (lock_claims γl lk s R (locked γl h0) Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock Htok") as "(#Hc4 & #Hc8 & Htok)".
    iApply (wp_load_s_sconf_au_dat (kt := kt) (ktd := KT0) 8 true false pc rd rs1 imm m n
              (fun w => w)
              (fun c => (⌜c = cpuv⌝ ∗ locked γl h0)%I)
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              (fun c => lk_cpu_cell_ex lo lk c (Some h0))
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 data2_ext_8 Hrd Hrdok
              ltac:(solve_ndisj)
              (lock_cell_read_vis (add_vec (rget m rs1) (sign_extend' 64 imm)) lk b lo Hpacpu Hbp)
              with "Hcg Hpc Hinstr [] [Htok] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with (lock_cpu lk)
        by (symmetry; exact Hpacpu).
      iApply (lk_addr_claim_wordw with "Hc8"). }
    { iMod ("Hopen" $! (⊤ ∖ ↑minstretN) (locked γl h0) with "[%] [] Htok")
        as "(Hbody & Htok & [Hclose _])"; [solve_ndisj| iApply Href |].
      iDestruct "Hbody" as "(Hbody & >#Hcl4 & >#Hcl8)".
      iDestruct "Hbody" as (w st B) "(>Hword & >Hcpures & >Hg & Hbr)".
      iDestruct (locked_state_at with "Hg Htok") as "[%Hst #HflB]".
      iEval (rewrite /lk_cpu_res) in "Hcpures".
      iDestruct "Hcpures" as "[Hcpu Hrest]".
      iModIntro. iExists (lk_cpu_val st).
      iSplitL "Hcpu"; [ rewrite Hst; iExact "Hcpu" | ].
      iIntros "Hcpu".
      iMod ("Hclose" with "[Hword Hcpu Hrest Hg Hbr]") as "_".
      { iNext. rewrite /lock_inv /lock_body. iFrame "Hcl4 Hcl8". iExists w, st, B. iFrame "Hword Hg Hbr".
        rewrite /lk_cpu_res. iFrame "Hrest". rewrite Hst. iExact "Hcpu". }
      iModIntro. iFrame "Htok". iPureIntro.
      rewrite Hst /cpuv -cpus_ptr_cid. reflexivity. }
    iIntros (c). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc (%Hc & Htok)".
    subst c.
    iApply ("Hcont" $! CID1 with "[] Htok Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  (* >>> A6.119: THE [notheld] LEAF, ON THE RACY KIT.

     WHAT WENT: the pre-flip generic took a caller premise
     [∀ st, lock_auth γl st -∗ lk_cpu_frag st s -∗ T -∗ ⌜phi (lk_cpu_val st)⌝]
     and concluded [phi] of the LOADED word.  A6.92 refuted exactly that step:
     after the M4 flip the owner cell is racy, so the value read need not be
     [lk_cpu_val st] for the [st] the invariant holds -- the ghost state does
     not determine the word.  The premise is retired here, with A6.92 cited,
     and nothing else in the tree wanted it.

     WHAT REPLACES IT is weaker and is all [holding()] needs: whatever the
     read lands on, it is not THIS hart's [struct cpu] pointer.  The evidence
     is [s ∉ lks] plus the hart's own held-set authority, exactly as before --
     [cpu_locks_not_in] refutes [ex = Some cpu_id] -- but it is now spent on
     the CELL's per-agent record rather than on the ghost state's value.

     THE FLOOR is why this takes [lock_openable_c] and not [lock_openable]
     (A6.112 §3b): the racy law wants [ctx_floor cur_ctx lo], which is
     [lk_floor]'s left arm, and only the crossing upgrade produces it. <<< *)
  Lemma wp_ld_lkcpu_notheld_gen (cmp : bool)
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Dc : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (T : iProp Σ) (b : bool) (lks : gset string) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd_ok rd ->
    s ∉ lks ->
    (b = false \/ p = zero_reg) ->
    (⊢ T -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc cmp (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    lock_openable_c γl lk s R Dc -∗
    T -∗
    cpu_locks_at h0 lks -∗
    ( ∀ c : mword 64,
      wp_next b p (fun (CID : CpuId) =>
        ⌜c <> cpus_ptr h0⌝ -∗
        T -∗
        cpu_locks_at h0 lks -∗
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg c]> m) n b p -∗
        pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 Hpacpu Hrd Hrdok Hfresh Hbp Href.
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlockc HT Hlks Hcont".
    iDestruct (WpLock.lock_openable_c_parts with "Hlockc") as (lo) "[#Hfl #Hopen]".
    iAssert (lock_openable γl lk s R Dc) as "#Hlock".
    { iApply WpLock.lock_openable_of_c. iExact "Hlockc". }
    iApply fupd_wp.
    iMod (lock_claims γl lk s R (T ∗ cpu_locks_at h0 lks)%I Dc ⊤
            ltac:(solve_ndisj) ltac:(iIntros "[HT _]"; iApply Href; iExact "HT")
            with "Hlock [$HT $Hlks]") as "(#Hc4 & #Hc8 & [HT Hlks])".
    iDestruct (WpLock.lk_addr_claim_ram (lock_cpu lk) 8 with "Hc8") as %Hram.
    iApply (wp_load_s_sconf_au_exv (kt := kt) (ktd := KT0) 8 cmp false pc rd rs1 imm m n
              (fun w => w)
              (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              (fun c => c <> cpus_ptr h0)
              (TsoCtx.ctx_floor TsoCtx.cur_ctx lo ∗
               ∃ (v : mword 32) (st : lock_state) (B : nat),
                 ⌜lk_ex st <> Some (@cpu_id CID)⌝ ∗
                 lock_word_at st B lk v ∗ lk_cpu_res lo st lk s ∗
                 lock_auth_at γl st B ∗
                 ▷ (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗
                      lock_frag γl None ∗ lock_pay R
                    ∨ ⌜st <> None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝))%I
              (T ∗ cpu_locks_at h0 lks)%I
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia)
              ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 data2_ext_8 Hrd Hrdok
              ltac:(solve_ndisj)
              (lock_cell_read_notheld (add_vec (rget m rs1) (sign_extend' 64 imm))
                 lk b lo γl s R Hpacpu Hbp
                 ltac:(intros j Hj; exact (Hram j Hj)))
              with "Hcg Hpc Hinstr [] [HT Hlks] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with (lock_cpu lk)
        by (symmetry; exact Hpacpu).
      iApply (lk_addr_claim_wordw with "Hc8"). }
    { (* the atomic update: open, hand the cell over, take it back, close *)
      iMod ("Hopen" $! (⊤ ∖ ↑minstretN) (T ∗ cpu_locks_at h0 lks)%I
              with "[%] [] [$HT $Hlks]")
        as "(Hbody & [HT Hlks] & [Hclose _])";
        [solve_ndisj | iIntros "[HT _]"; iApply Href; iExact "HT" |].
      iDestruct "Hbody" as "(Hbody & >#Hcl4 & >#Hcl8)".
      iDestruct "Hbody" as (w st B) "(>Hword & >Hcpures & >Hg & Hbr)".
      (* THIS HART IS NOT THE HOLDER, and that is the whole credential: were
         it, the invariant would be keeping [lk_in cpu_id s] beside the cell,
         which [cpu_locks_not_in] refutes against [s ∉ lks]. *)
      iAssert (⌜lk_ex st <> Some h0⌝)%I with "[Hcpures Hlks]" as %Hne.
      { destruct st as [[i []]|]; [| by iPureIntro | by iPureIntro ].
        rewrite /lk_cpu_res /=.
        iDestruct "Hcpures" as "[_ Hin]".
        destruct (decide (i = h0)) as [->|Hni].
        - iDestruct (cpu_locks_not_in h0 lks s Hfresh with "Hlks Hin") as %[].
        - iPureIntro. intros Heq. by injection Heq. }
      iModIntro. iFrame "Hfl".
      iSplitL "Hword Hcpures Hg Hbr".
      { iExists w, st, B. iFrame "Hword Hcpures Hg Hbr". by iPureIntro. }
      iIntros "[_ (%v' & %st' & %B' & _ & Hword' & Hcpures' & Hg' & Hbr')]".
      iMod ("Hclose" with "[Hword' Hcpures' Hg' Hbr']") as "_".
      { iNext. rewrite /lock_inv /lock_body. iFrame "Hcl4 Hcl8".
        iExists v', st', B'. iFrame "Hword' Hcpures' Hg' Hbr'". }
      iModIntro. iFrame "HT Hlks". }
    iIntros (c). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc %Hc [HT Hlks]".
    iApply ("Hcont" $! c CID1 with "[] [%] HT Hlks Hcg Hpc");
      [ iPureIntro; exact Hs1 | exact Hc ].
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
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Tc Dc : iProp Σ)
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
    (b = false \/ p = zero_reg) ->
    (⊢ Tc -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    (* A6.119: the ABSORBED opener -- the racy read needs [lk_floor]'s left
       arm, which only the crossing upgrade produces (A6.112 §3b). *)
    lock_openable_c γl lk s R Dc -∗
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
    intros pa h0 cpuv Hpacpu Hrd Hrdok Hfresh Hbp Href.
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    (* the free / window states record 0, and no hart's [struct cpu] is 0 *)
    assert (Hz : forall i : CPU, (zero_reg : mword 64) <> cpus_ptr i)
      by (intro i; apply eq_vec_false_iff; apply cpus_ptr_nonzero).
    iIntros "Hcg Hpc Hinstr #Hlockc HTc Hlks Hcont".
    iApply (wp_ld_lkcpu_notheld_gen true γl lk s R Dc pc rd rs1 imm m n
              Tc b lks
              Hpacpu Hrd Hrdok Hfresh Hbp
              ltac:(iIntros "HTc"; iApply Href; iExact "HTc")
              with "Hcg Hpc Hinstr Hlockc HTc Hlks [Hcont]").
    iIntros (c). iEval (rewrite /wp_next). iIntros (CID1 Hs1) "%Hc HTc Hlks Hcg Hpc".
    iApply ("Hcont" $! c CID1 with "[] [%] HTc Hlks Hcg Hpc");
      [ iPureIntro; exact Hs1
      | unfold cpuv; rewrite -cpus_ptr_cid; exact Hc ].
  Qed.

  (* >>> A6.119: THE CPU-FIELD STORE'S WRITE OBLIGATION, on the gate's two
     arms.  [WpSconfMem.word_wpay_frame_store_gen_c] does the machine half;
     everything here is the cell's bookkeeping across it -- [lk_own_ok] at the
     new face, and [lk_own_anchored] re-established from the store's own
     message fragment on the arm that installs a record.  Both are one lemma
     each, exactly as A6.114 §2 priced them. <<< *)
  Local Lemma lock_cell_store_frame (ea lk : mword 64) (b : bool) (lo : nat)
      (unew uval : mword 64) (exnew exold : option CPU) (uold : mword 64)
      (Hea : ea = lock_cpu lk)
      (* A6.119: the arm is stated at [uval] -- the GHOST state's face -- and
         tied to the STORED value by one equation.  The caller has that
         equation ([Hsv]) and would otherwise have to rewrite under two
         binders to use it; here the rewrite happens once, inside. *)
      (Hval : uval = unew)
      (Hbp : b = false \/ p = zero_reg)
      (Harm : forall CIDw : CpuId,
         (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
         ((forall j : nat, (j < 8)%nat -> nth_byte uval j = lkcpu_z j)
          /\ exnew = None /\ exold = Some (@cpu_id CIDw))
         \/ ((forall j : nat, (j < 8)%nat ->
                nth_byte uval j = lkcpu_cp (hart_agent (@cpu_id CIDw)) j)
             /\ exnew = Some (@cpu_id CIDw) /\ exold = None)) :
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate) (log : list pwmsg)
           (V : agent -> nat) (ppn : mword 44),
      (uint ea < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec ea 11 0) + 8 <= 4096)%Z ->
      ktier_pin KT0 ppn ea ->
      (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of ea) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      lk_cpu_cell_ex lo lk uold exold ==∗
      gen_heap_interp (hG := riscv_memGS)
        (write_bytes sigma.(mem) (pa_of ppn ea) (Z.to_N 8) unew) ∗
      tso_interp_of riscv_eraGS img
        (write_bytes sigma.(mem) (pa_of ppn ea) (Z.to_N 8) unew)
        (log ++ [PWMsg (snap_of (pa_of ppn ea) (Z.to_N 8) unew)
                   (hart_agent (@cpu_id CIDw))])%list
        (vstep (hart_agent (@cpu_id CIDw)) (V (hart_agent (@cpu_id CIDw)))
           (log ++ [PWMsg (snap_of (pa_of ppn ea) (Z.to_N 8) unew)
                      (hart_agent (@cpu_id CIDw))])%list V) ∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
      lk_cpu_cell_ex lo lk unew exnew.
  Proof.
    subst ea. subst uval.
    intros CIDw img sigma log V ppn Hcan Hoff Hid Hsame.
    pose proof (Harm CIDw Hsame) as Hcase.
    set (hw := hart_agent (@cpu_id CIDw)).
    iIntros "#Hk Hmem Htso Hctx Hcell".
    iDestruct (lk_cpu_cell_ex_pay with "Hcell") as (own) "(%Hok & #Han & Hb)".
    rewrite (ktier_pin_id ppn (lock_cpu lk) Hid).
    change (Z.to_N 8) with 8%N.
    (* the new own map, and which arm installs a record *)
    destruct Hcase as [(Hz & Hexn & Hexo) | (Hcp & Hexn & Hexo)].
    - (* LEFT: the clear word goes down and the writer's record is RESTORED *)
      set (own' := fun h => if decide (h = hw)
                            then Some (S (length log)) else own h).
      iMod (word_wpay_frame_store_gen_c (CIDw := CIDw) img sigma log V
              (lock_cpu lk) uold unew lkcpu_z lkcpu_cp own own' lo
              ltac:(left; split;
                    [ exact Hz | rewrite /own'; by rewrite decide_True ])
              ltac:(intros h Hne; rewrite /own'; by rewrite decide_False)
              with "Hmem Htso [Hb]") as "(Hmem & Htso & #Hmsg & Hnew)".
      { rewrite /lk_cpu_pay. iExact "Hb". }
      iModIntro. iFrame "Hmem Htso Hctx".
      iExists own'. iSplitR.
      { iPureIntro. rewrite Hexn. intros h Hh. rewrite /own' in Hh.
        case_decide as Hd; [ discriminate | ].
        destruct (Hok h Hh) as (i & Hexi & Hag). rewrite Hexo in Hexi.
        injection Hexi as <-. exfalso. by apply Hd. }
      iSplitR.
      { iIntros (h t) "%Ht". rewrite /own' in Ht. case_decide as Hd.
        - injection Ht as <-. subst h.
          iApply (TsoCtx.ledger_vis_own hw lo (length log)
                    (PWMsg (snap_of (lock_cpu lk) 8 unew) hw) eq_refl).
          iExact "Hmsg".
        - iApply ("Han" $! h t). by iPureIntro. }
      rewrite Hexn /lk_cpu_pay.
      iApply (big_sepL_impl with "Hnew"). iIntros "!>" (kk j _) "H".
      iExists (S (length log)). iExact "H".
    - (* RIGHT: the writer's own word goes down and its record is REVOKED *)
      set (own' := fun h => if decide (h = hw) then None else own h).
      iMod (word_wpay_frame_store_gen_c (CIDw := CIDw) img sigma log V
              (lock_cpu lk) uold unew lkcpu_z lkcpu_cp own own' lo
              ltac:(right; split;
                    [ exact Hcp | rewrite /own'; by rewrite decide_True ])
              ltac:(intros h Hne; rewrite /own'; by rewrite decide_False)
              with "Hmem Htso [Hb]") as "(Hmem & Htso & #Hmsg & Hnew)".
      { rewrite /lk_cpu_pay. iExact "Hb". }
      iModIntro. iFrame "Hmem Htso Hctx".
      iExists own'. iSplitR.
      { iPureIntro. rewrite Hexn. intros h Hh. rewrite /own' in Hh.
        case_decide as Hd.
        - exists (@cpu_id CIDw). split; [reflexivity | exact Hd].
        - destruct (Hok h Hh) as (i & Hexi & _). by rewrite Hexo in Hexi. }
      iSplitR.
      { iIntros (h t) "%Ht". rewrite /own' in Ht. case_decide as Hd;
          [ discriminate | ]. iApply ("Han" $! h t). by iPureIntro. }
      rewrite Hexn /lk_cpu_pay_vis.
      (* [big_sepL_impl], not [_mono]: the per-byte step needs [Hmsg], and
         [_mono]'s premise is a bare entailment with an EMPTY Iris context. *)
      iApply (big_sepL_impl with "Hnew"). iIntros "!>" (kk j _) "H".
      iExists (S (length log)). iSplitR; [| iExact "H" ].
      iApply (TsoCtx.ledger_vis_own hw 0 (length log)
                (PWMsg (snap_of (lock_cpu lk) 8 unew) hw) eq_refl).
      iExact "Hmsg".
  Qed.

  (* the generic write of the cpu word: the caller's evidence [T] becomes
     [T'] as the ghost state moves to [stn], whose recorded owner word is
     exactly what the instruction stores. *)
  Lemma wp_sd_lkcpu_lockopen_gen (cmp : bool)
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Dc : iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (T T' : iProp Σ) (stn : lock_state)
      (uold : mword 64) (exold : option CPU) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    lk_cpu_val stn = rget m rs2 ->
    (* A6.119: WHICH ARM of [ledger_store_win_wpay_ok] this store is, at the
       writing hart.  Release writes the clear word and RESTORES its own
       record (left); acquire writes its own [struct cpu] pointer -- the
       window's [cp] row -- and REVOKES it (right).  The no-migration pin is
       what lets the right arm name the writer at all. *)
    (forall CIDw : CpuId,
       (b = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
       ((forall j : nat, (j < 8)%nat ->
           nth_byte (lk_cpu_val stn) j = lkcpu_z j)
        /\ lk_ex stn = None /\ exold = Some (@cpu_id CIDw))
       \/ ((forall j : nat, (j < 8)%nat ->
              nth_byte (lk_cpu_val stn) j = lkcpu_cp (hart_agent (@cpu_id CIDw)) j)
           /\ lk_ex stn = Some (@cpu_id CIDw) /\ exold = None)) ->
    (b = false \/ p = zero_reg) ->
    (* THE EXCHANGE, not just a ghost step: the cpu field is co-owned with
       the holding hart (WpLock.lk_cpu_res), so a store to it has to be
       licensed by whatever the caller brings.  The premise takes the
       invariant's share and produces (a) the WHOLE cell, which is what the
       store needs, and (b) a wand that takes the whole cell back at the new
       value and rebuilds the invariant's share.  acquire's instance splits
       the written cell and pays a half into its own held-lock set; release's
       instance redeems the set fragment to complete the cell in the first
       place. *)
    (* A6.119: THE EXCHANGE TRADES CELLS, NOT CTX WORDS.  After the M4 flip
       the owner field is a racy window and there is no [↦₈] to hand over;
       what the store needs is the window itself, and what it gives back is
       the window at the new value.  [lo] is ∀-bound because the floor lives
       inside [lock_openable_c] and no caller can name it (A6.97's rule);
       both instances are floor-generic anyway -- they move only the ghost
       auth and the held-set fragment, and pass the cell straight through. *)
    (* ...and it PINS THE OLD STATE'S FACE.  The atomic update's [Res] and
       [Post] are fixed before the invariant is opened, so neither may mention
       the [st] found inside it (A6.119's AU rule, one level on from the
       [lo]-hoist).  Both instances know the old face from the new one -- the
       two cpu stores are each other's inverse -- so the exchange exhibits it
       and the leaf's telescope carries it. *)
    (forall (lo B : nat) (st : lock_state),
       ⊢ lock_auth_at γl st B -∗ lk_cpu_res lo st lk s -∗ T ==∗
         ⌜st <> None⌝ ∗ ⌜stn <> None⌝ ∗
         ⌜lk_cpu_val st = uold⌝ ∗ ⌜lk_ex st = exold⌝ ∗
         (* the LOCK WORD is untouched by a cpu-field store, and its author
            selector ([lk_wex], A6.89) does not move either: both stores keep
            the state's [Some i] and change only the bool. *)
         ⌜lk_wex st = lk_wex stn⌝ ∗
         lock_auth_at γl stn B ∗
         lk_cpu_cell_ex lo lk uold exold ∗
         (lk_cpu_cell_ex lo lk (lk_cpu_val stn) (lk_ex stn) ==∗
            lk_cpu_res lo stn lk s ∗ T')) ->
    (⊢ T -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc cmp (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    lock_openable_c γl lk s R Dc -∗
    T -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
      T' -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hpacpu Hsv Harm Hbp Hupd Href.
    (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlockc HT Hcont".
    iDestruct (WpLock.lock_openable_c_parts with "Hlockc") as (lo) "[#Hfl #Hopen]".
    iAssert (lock_openable γl lk s R Dc) as "#Hlock".
    { iApply WpLock.lock_openable_of_c. iExact "Hlockc". }
    iApply fupd_wp.
    iMod (lock_claims γl lk s R T Dc ⊤ ltac:(solve_ndisj) Href
            with "Hlock HT") as "(#Hc4 & #Hc8 & HT)".
    iApply (wp_store_s_sconf_au_dat (kt := kt) (ktd := KT0) 8 cmp pc rs2 rs1 imm m n
              (rget m rs2) T' (⊤ ∖ ↑minstretN ∖ ↑lockN) b
              (lk_cpu_cell_ex lo lk uold exold)
              (lk_cpu_cell_ex lo lk (rget m rs2) (lk_ex stn))
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia)
              ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              ltac:(solve_ndisj)
              (lock_cell_store_frame (add_vec (rget m rs1) (sign_extend' 64 imm))
                 lk b lo (rget m rs2) (lk_cpu_val stn) (lk_ex stn) exold uold
                 Hpacpu Hsv Hbp Harm)
              with "Hcg Hpc Hinstr [] [HT] [Hcont]").
    { replace (add_vec (rget m rs1) (sign_extend' 64 imm)) with (lock_cpu lk)
        by (symmetry; exact Hpacpu). iApply (lk_addr_claim_wordw with "Hc8"). }
    { iMod ("Hopen" $! (⊤ ∖ ↑minstretN) T with "[%] [] HT")
        as "(Hbody & HT & [Hclose _])"; [solve_ndisj| iApply Href |].
      iDestruct "Hbody" as "(Hbody & >#Hcl4 & >#Hcl8)".
      iDestruct "Hbody" as (w st B) "(>Hword & >Hcpures & >Hg & Hbr)".
      iMod (Hupd lo B st with "Hg Hcpures HT")
        as "(%Hstne & %Hstnne & %Huold & %Hexold & %Hwex & Hg & Hcpu & Hback)".
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      iModIntro. iFrame "Hcpu".
      iIntros "Hcpu".
      iEval (rewrite -Hsv) in "Hcpu".
      iMod ("Hback" with "Hcpu") as "[Hcpures HT']".
      iMod ("Hclose" with "[Hword Hcpures Hg]") as "_".
      { iNext. rewrite /lock_inv /lock_body. iFrame "Hcl4 Hcl8".
        iExists w, stn, B.
        destruct st as [[i o]|]; [| congruence ].
        destruct stn as [[i' o']|]; [| congruence ].
        iFrame "Hword Hg Hcpures".
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
      (S : gset string) (Hfresh : r ∉ S) (lo B : nat) (st : lock_state) :
    ⊢ lock_auth_at γl st B -∗ lk_cpu_res lo st lk r -∗
      (locked_pre γl cpu_id ∗ cpu_locks_at cpu_id S) ==∗
      ⌜st <> None⌝ ∗ ⌜Some (cpu_id, true) <> None⌝ ∗
      ⌜lk_cpu_val st = (zero_reg : mword 64)⌝ ∗ ⌜lk_ex st = None⌝ ∗
      ⌜lk_wex st = lk_wex (Some (cpu_id, true))⌝ ∗
      lock_auth_at γl (Some (cpu_id, true)) B ∗
      lk_cpu_cell_ex lo lk (zero_reg : mword 64) None ∗
      (lk_cpu_cell_ex lo lk (lk_cpu_val (Some (cpu_id, true)))
         (lk_ex (Some (cpu_id, true))) ==∗
         lk_cpu_res lo (Some (cpu_id, true)) lk r ∗
         (locked γl cpu_id ∗ cpu_locks_at cpu_id ({[r]} ∪ S))).
  Proof.
    iIntros "Hg Hcpures [Htok Hcl]".
    iMod (lock_setcpu γl st B cpu_id with "Hg Htok") as "(%Hst & Hg & Htok)".
    rewrite Hst.
    iEval (rewrite lk_cpu_res_win) in "Hcpures".
    iModIntro.
    iSplitR; [ iPureIntro; discriminate | ].
    iSplitR; [ iPureIntro; discriminate | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
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
      (S : gset string) (lo B : nat) (st : lock_state) :
    ⊢ lock_auth_at γl st B -∗ lk_cpu_res lo st lk r -∗
      (locked γl cpu_id ∗ cpu_locks_at cpu_id S) ==∗
      ⌜st <> None⌝ ∗ ⌜Some (cpu_id, false) <> None⌝ ∗
      ⌜lk_cpu_val st = cpus_ptr cpu_id⌝ ∗ ⌜lk_ex st = Some cpu_id⌝ ∗
      ⌜lk_wex st = lk_wex (Some (cpu_id, false))⌝ ∗
      lock_auth_at γl (Some (cpu_id, false)) B ∗
      lk_cpu_cell_ex lo lk (cpus_ptr cpu_id) (Some cpu_id) ∗
      (lk_cpu_cell_ex lo lk (lk_cpu_val (Some (cpu_id, false)))
         (lk_ex (Some (cpu_id, false))) ==∗
         lk_cpu_res lo (Some (cpu_id, false)) lk r ∗
         (locked_pre γl cpu_id ∗ cpu_locks_at cpu_id (S ∖ {[r]}) ∗ ⌜r ∈ S⌝)).
  Proof.
    iIntros "Hg Hcpures [Htok Hcl]".
    iMod (lock_clrcpu γl st B cpu_id with "Hg Htok") as "(%Hst & Hg & Htok)".
    rewrite Hst.
    iEval (rewrite lk_cpu_res_held) in "Hcpures".
    iDestruct "Hcpures" as "[Hcell Hin]".
    iMod (cpu_locks_delete cpu_id S r with "Hcl Hin") as "(%Hin & Hcl)".
    iModIntro.
    iSplitR; [ iPureIntro; discriminate | ].
    iSplitR; [ iPureIntro; discriminate | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
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
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Dc : iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) (S : gset string) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    pa = lock_cpu lk ->
    rget m rs2 = mycpu_ret cid_word ->
    s ∉ S ->
    (b = false \/ p = zero_reg) ->
    (⊢ locked_pre γl h0 -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    lock_openable_c γl lk s R Dc -∗
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
    intros pa h0 Hpacpu Hmycpu Hfresh Hbp Href.
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
    iIntros "Hcg Hpc Hinstr #Hlockc Htok Hcl Hcont".
    iApply (wp_sd_lkcpu_lockopen_gen true γl lk s R Dc pc rs2 rs1 imm m n
              (locked_pre γl h0 ∗ cpu_locks_at h0 S)%I
              (locked γl h0 ∗ cpu_locks_at h0 ({[s]} ∪ S))%I
              (Some (h0, true)) (zero_reg : mword 64) None b
              Hpacpu Hsv
              (* the RIGHT arm: acquire writes its own [struct cpu] pointer,
                 the window's [cp] row, and revokes its own record. *)
              ltac:(intros CIDw Hs; right; split_and!;
                    [ intros j Hj; rewrite lk_cpu_val_held /lkcpu_cp
                        (Hs Hbp) agent_cpus_ptr_hart; reflexivity
                    | by rewrite /lk_ex (Hs Hbp)
                    | reflexivity ])
              Hbp
              (lkcpu_take_exchange γl lk s S Hfresh)
              ltac:(iIntros "[Htok _]"; iApply Href; iExact "Htok")
              with "Hcg Hpc Hinstr Hlockc [Htok Hcl] [Hcont]").
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
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Dc : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) (S : gset string) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let h0 := cpu_id in
    pa = lock_cpu lk ->
    (b = false \/ p = zero_reg) ->
    (⊢ locked γl h0 -∗ Dc -∗ False) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    lock_openable_c γl lk s R Dc -∗
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
    intros pa h0 Hpacpu Hbp Href.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hlockc Htok Hcl Hcont".
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
              (Some (h0, false)) (cpus_ptr h0) (Some h0) b
              Hpacpu Hsv
              (* the LEFT arm: release writes the clear word and RESTORES its
                 own record. *)
              ltac:(intros CIDw Hs; left; split_and!;
                    [ intros j Hj; rewrite lk_cpu_val_win; reflexivity
                    | reflexivity
                    | by rewrite (Hs Hbp) ])
              Hbp
              (lkcpu_give_exchange γl lk s S)
              ltac:(iIntros "[Htok _]"; iApply Href; iExact "Htok")
              with "Hcg Hpc Hinstr Hlockc [Htok Hcl] [Hcont]").
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
      (γl : gname) (lk : mword 64) (s : string) (R : CtxId → iProp Σ) (Tc Dc : iProp Σ)
      (pc : mword 64) (rd rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (b : bool) :
    let pa := add_vec (rget m rs1) (zeros' 64) in
    let h0 := cpu_id in
    pa = lk ->
    (* A6.119: the stored value is 1 -- xv6's acquire is
       [__sync_lock_test_and_set(&lk->locked, 1)], and the value set {1} the
       held word's pin carries is FORCED, not chosen: [byteset] is per-byte,
       so no set can say "nonzero word".  The sole caller (ProofAcquire) pays
       this literally. *)
    rget m rs2 = (mword_of_int 1 : mword 64) ->
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
        (* >>> A6.119: THE WINNER RECEIVES THE WHOLE PARKED RECORD.  The
           invariant's free arm holds [lock_pay R] = [∃ ξ T, ctx_parked ξ T ∗
           R ξ]; this post used to promise only [∃ ξ, R ξ], i.e. to DROP
           [ctx_parked].  §0.18′/A6.66 puts the parked-record absorb AT
           ACQUIRE ([ctx_dom_of_parked] against the AMO's at-the-top
           evidence), so the leaf hands the record over and [SpecAcquire]
           absorbs it.  The old post was pre-flip residue, never checked
           because this file has been red upstream of it since the baseline.
           FORWARD PAYOFF: [ctx_parked ξ T] arriving at the winner is exactly
           what §0.27′'s resume tie will consume -- this is that ruling's
           prerequisite landing early, not incidental churn. <<< *)
        (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked_pre γl h0 ∗ WpLock.lock_pay R
         ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa h0 Hpalk Hone Hstz Hrd Hrdok Href.
    assert (Hzeroone : amoswap_stored (rget m rs2) = WpLock.lkw_one)
      by (rewrite Hone /amoswap_stored /WpLock.lkw_one;
          apply bv_eq; vm_compute; reflexivity).
    rdok_split Hrdok.
    iIntros "Hcg Hpc #Hinstr #Hlock HTc Hcont".
    iDestruct (WpLock.lock_openable_parts with "Hlock") as (lo) "[#Hfl #Hopen]".
    iApply (wp_instr_s_sconf m n b b pc false
              (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
              (fun (_CIDx : CpuId) npc _ms' m' n' =>
                 ∃ w : mword 32,
                   ⌜npc = add_vec_int pc 4⌝ ∗
                   ⌜m' = <[Regidx rd := regval_into_reg (amoswap_loaded w)]> m⌝ ∗
                   ⌜n' = n⌝ ∗ Tc ∗
                   (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked_pre γl h0 ∗ WpLock.lock_pay R
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
      iDestruct "Hcap" as "(Hstk & Htr & Harm & Hctx & #Htc & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      (* >>> A6.92: THE PEEK IS GONE, AND THAT IS THE M4 FLIP PAYING AGAIN.
         The pre-flip text opened the body, took the WORD APART to read a
         [mem_pointsto]'s mapping off byte 0, and put it back -- the same
         shim-shaped dance [lock_claims] used to do (A6.87 §(1) killed that
         one).  A6.87 put the two address claims INSIDE the invariant, so
         the [ppn], canonicality, RAM-ness and tier pin the three nodes
         below need come off [lk_addr_claim] with a PEEK-OPEN that never
         touches the cells -- which is also the only shape that survives
         the word becoming a ledger cell (it has no mapping to read). <<< *)
      iApply (swp_fupd (CID := CID)).
      iMod (lock_claims γl lk s R Tc Dc ⊤ ltac:(solve_ndisj) Href
              with "Hlock HTc") as "(#Hcl4 & #Hcl8 & HTc)".
      iAssert (WpLock.lk_addr_claim pa 4) as "#Hclp".
      { rewrite Hpalk. iExact "Hcl4". }
      iDestruct "Hclp" as "(%Hpalign4 & %ppn & #Hk & %Hcan & %Hkd0 & %Hid & _)".
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
                    (* A6.119: the RUNNING TOKEN RIDES OUT WITH THE RESULT.
                       [ctx_bound_raise] -- the AMO's export -- needs
                       [own_context], and the capability bundle hands it to
                       [swp_mono]'s continuation, not to the nodes.  The gates
                       thread it in and out, so the honest routing is to let
                       it escape the node inside [R bytes] and be picked up by
                       the continuation that rebuilds the capability. *)
                    (fun bytes => Tc ∗
                       TsoCtx.own_context (CID := CID) TsoCtx.cur_ctx ∗
                       (⌜bytes = (mword_of_int 0 : mword 32)⌝ ∗
                          locked_pre γl h0 ∗ WpLock.lock_pay R
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
                    with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HTc] [Hctx]").
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
          - (* the exclusive READ node: open the invariant, read FLAT, close.
               A6.92: the word never comes apart -- [lock_word_ex_forget]
               drops whichever arm the state selects to the plain ledger
               word, and [lock_word_flat_bytes] reads its four cells off the
               interp. *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod ("Hopen" $! ⊤ Tc with "[%] [] HTc")
              as "(Hbody & HTc & [Hcl _])"; [solve_ndisj | iApply Href |].
            iDestruct "Hbody" as "(Hbody & >#Hcl4' & >#Hcl8')".
            iDestruct "Hbody" as (v1 st1 B1) "(>Hw & Hcpu & Hg & Hbr)".
            iDestruct (lock_word_flat_bytes st1 B1 lk v1 sigma.(mem)
                         with "Hmem Hw") as %Hbf.
            iMod ("Hcl" with "[Hw Hcpu Hg Hbr]") as "_".
            { iNext. rewrite /lock_inv /lock_body. iFrame "Hcl4' Hcl8'". iExists v1, st1, B1.
              iFrame "Hw Hcpu Hg Hbr". }
            iMod (fupd_mask_subseteq ∅) as "Hclm"; [set_solver|].
            iModIntro. iExists v1.
            iSplitR.
            { iPureIntro. intros j Hj.
              rewrite (ktier_pin_id ppn pa Hid) Hpalk. apply Hbf. lia. }
            iNext. iMod "Hclm" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev HTc".
          - (* the conditional WRITE node *)
            (* >>> A6.119: THE AMO'S WRITE NODE, RE-CUT TO THE LEDGER TIER.
               This text had never been checked against the M4 flip -- the
               file has been red upstream of it since the baseline, and Coq
               stops at the first error -- so it still wrote a
               [word4_pointsto] through [word4_pointsto_write_c].  Post-flip
               the lock word is a ledger cell and the node's own obligation
               hands over the TSO interp beside the machine state
               ([HartSMem.swp_execute_AMOSWAP_S_ex_mode]), which is exactly
               what [lock_word_amo_mint] has wanted since A6.89 and never
               had a client for. <<< *)
            iIntros (bytes) "HTc".
            iIntros (sigma img log tv V) "%Hrb %Htv Hsi Htso".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod ("Hopen" $! ⊤ Tc with "[%] [] HTc")
              as "(Hbody & HTc & [Hcl _])"; [solve_ndisj | iApply Href |].
            iDestruct "Hbody" as "(Hbody & >#Hcl4w & >#Hcl8w)".
            iDestruct "Hbody" as (v2 st2 B2) "(>Hw & >Hcpu & >Hg & Hbr)".
            iDestruct (lock_word_flat_bytes st2 B2 lk v2 sigma.(mem)
                         with "Hmem Hw") as %Hbf2.
            assert (Hv2 : v2 = bytes).
            { pose proof (read_bytes_of_bytes sigma.(mem) (pa_of ppn pa) 4 v2
                            ltac:(intros j Hj;
                                  rewrite (ktier_pin_id ppn pa Hid) Hpalk;
                                  apply Hbf2; lia)) as Hr2.
              rewrite Hr2 in Hrb. by injection Hrb. }
            subst v2.
            (* A6.119: the value-set side condition, HOISTED out of
               application position.  An [ltac:] inside an [iMod (...)]
               elaborates against a goal whose arguments are not yet fixed, so
               [rewrite Hzeroone] finds nothing to match; written out here the
               goal is concrete.  Same precedent as [Harm'] one leaf over. *)
            assert (Hset1 : forall j : nat, (j < 4)%nat ->
                      nth_byte (amoswap_stored (rget m rs2)) j
                      ∈ WpLock.lkw_set j).
            { intros j Hj. rewrite Hzeroone /WpLock.lkw_set.
              apply TsoMemPa.byteset_sing_in. }
            (* >>> A6.119: THE BRANCH COMES BEFORE THE STORE, and it has to.
               A WINNING amoswap finds the word free (plain ledger cell) and
               MINTS the value-set pin at its own position; a LOSING one finds
               it held and must PRESERVE the pin at the position it already
               has -- re-minting at the spinner's position would move the
               invariant's [B] while the holder's token still carries the old
               one, and [lock_pos_agree] would break.  So the two arms take
               different gates, and the state decides which. <<< *)
            iAssert (|={⊤ ∖ ↑lockN, ⊤}=>
                       gen_heap_interp (hG := riscv_memGS)
                         (write_bytes sigma.(mem) pa 4%N (amoswap_stored (rget m rs2))) ∗
                       tso_interp_of riscv_eraGS img
                         (write_bytes sigma.(mem) pa 4%N (amoswap_stored (rget m rs2)))
                         (log ++ [PWMsg (snap_of pa 4%N (amoswap_stored (rget m rs2)))
                                    (hart_agent (@cpu_id CID))])%list
                         (vstep (hart_agent (@cpu_id CID)) (S (length log))
                            (log ++ [PWMsg (snap_of pa 4%N (amoswap_stored (rget m rs2)))
                                       (hart_agent (@cpu_id CID))])%list V) ∗
                       TsoCtx.own_context (CID := CID) TsoCtx.cur_ctx ∗
                       (⌜bytes = (mword_of_int 0 : mword 32)⌝ ∗
                          locked_pre γl h0 ∗ ▷ WpLock.lock_pay R
                        ∨ ⌜neq_vec (sign_extend' 64 bytes) zero_reg = true⌝))%I
              with "[Hw Hcpu Hg Hbr Hcl Hmem Htso Hctx]"
              as ">(Hmem & Htso & Hctx & Hpay)".
            { iDestruct "Hbr" as "[(>%Hnone & >%Hw0 & >Hfrag2 & HR) |
                                   (>%Hsome & >%Hwnz)]".
              - (* THE WINNER: free word, plain cell in, pin minted out *)
                subst st2.
                iMod (lock_word_amo_mint pa (amoswap_stored (rget m rs2)) CID img sigma log V
                        Hset1
                        with "Hmem Htso Hctx [Hw]")
                  as "(Hmem & Htso & Hctx & Hpin & #Hflw)".
                { iExists bytes. rewrite Hpalk. iExact "Hw". }
                iMod (lock_take γl h0 (S (length log))
                        with "Hflw [Hg] Hfrag2") as "[Hg Hpre]";
                  [ by iExists B2 | ].
                iMod ("Hcl" with "[Hpin Hcpu Hg]") as "_".
                { iNext. rewrite /lock_inv /lock_body. iFrame "Hcl4w Hcl8w".
                  iExists (amoswap_stored (rget m rs2)), (Some (h0, false)), (S (length log)).
                  iFrame "Hg".
                  iSplitL "Hpin"; [ rewrite -Hpalk; iExact "Hpin" | ].
                  iSplitL "Hcpu";
                    [ rewrite lk_cpu_res_win -lk_cpu_res_free; iExact "Hcpu" | ].
                  iRight. iPureIntro. split; [discriminate | exact Hstz]. }
                iModIntro. iFrame "Hmem Htso Hctx".
                iLeft. iFrame "Hpre HR". iPureIntro. exact Hw0.
              - (* THE LOSER: the pin survives, at the B it already had *)
                iMod (lock_word_amo_keep pa (amoswap_stored (rget m rs2)) bytes B2 CID img sigma log V
                        Hset1
                        with "Hmem Htso Hctx [Hw]")
                  as "(Hmem & Htso & Hctx & Hpin)".
                { destruct st2 as [[i o]|]; [| congruence ].
                  rewrite Hpalk. iExact "Hw". }
                iMod ("Hcl" with "[Hpin Hcpu Hg]") as "_".
                { iNext. rewrite /lock_inv /lock_body. iFrame "Hcl4w Hcl8w".
                  iExists (amoswap_stored (rget m rs2)), st2, B2. iFrame "Hg Hcpu".
                  iSplitL "Hpin".
                  { destruct st2 as [[i o]|]; [| congruence ].
                    rewrite -Hpalk. iExact "Hpin". }
                  iRight. iPureIntro. split; [exact Hsome | exact Hstz]. }
                iModIntro. iFrame "Hmem Htso Hctx".
                iRight. iPureIntro. exact Hwnz. }
            iMod (fupd_mask_subseteq ∅) as "Hclm"; [set_solver|].
            iModIntro. iNext. iMod "Hclm" as "_". iModIntro.
            rewrite Lpin_rs2.
            (* the node spells the stored value UNFOLDED ([sign_extend' …
               (trunc … _)]); the gates spell it [amoswap_stored].  Fold once
               so the two meet syntactically. *)
            rewrite -/(amoswap_stored (rget m rs2)).
            (* the node writes at the PHYSICAL address; the gates were given
               the virtual one, which the tier pin identifies with it. *)
            rewrite (ktier_pin_id ppn pa Hid).
            iFrame "Hreg Hmem Htso Hdev HTc Hctx Hpay". }
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (bytes) "(Hfile & Hland)".
      iDestruct "Hland" as (rsf)
        "(%Hshape & Hrw & Hro & HRes & HR2 & Hfrag)".
      iDestruct "HR2" as "(HTc & Hctx & Hpay)".
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
      iSplitL "Htr Hstk Harm Hctx".
      { rewrite /sie_cap -Hsp. iFrame "Hstk Htr Harm Hctx Htc Hwit". }
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
