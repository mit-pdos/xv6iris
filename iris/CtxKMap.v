(* CtxKMap.v -- [KMap.mem_ident_phys] AT THE CONTEXT TOWER (A6.68).

   [KMap.v] sits BELOW [TsoCtx.v], so its [↦ₘ] and [↦ₚ] are the RAW
   families and its identity disassembly ([mem_ident_phys], and the page
   fold [mem_page_to_phys] over it) drops the ledger residue on the floor:
   a caller that owns a page as CONTEXT bytes and wants it as CONTEXT
   physical bytes cannot route through it, because the return trip is the
   direction the flip makes false.

   The whole content of the crossing at the ctx tower is already in
   [TsoCtx.ctx_pointsto_phys], which is a [⊣⊢] -- the VA family IS the
   phys family under the kmap claim.  What the raw lemma adds, and what
   this file re-adds, is IDENTITY: for a statically classified kernel-data
   page the claim's ppn is [kpt_leaf_ppn] ([kmap_at_agree] against the
   static bundle) and [KptPt.pa_of_id] then says [pa_of ppn a = a].  So
   nothing here is new machinery -- it is the raw lemma's proof with the
   ledger residue carried through instead of forgotten.

   CONSUMERS: the two page-table roots that come out of [memset]
   ([ProofKvmmake], [ProofUvmcreate]) and the walk's node disassembly
   ([ProofWalk]) -- A6.62's "[ctx_phys] window" entry. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map gen_heap.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto.
Require Import KptPt.
Require Import KMap.
Require Import TsoCtx.
Local Open Scope Z_scope.

Section CtxKMap.
  Context `{!riscvGS Σ}.
  Context `{KTR : !CurKtier}.

  (* disassembly at the ctx tower: the byte a static kdata va owns IS the
     context's physical byte at [pa] -- same timestamp, same clean/dirty
     arm, only the mapping plumbing goes. *)
  Lemma ctx_mem_ident_phys (xi : CtxId) (pa : mword 64) (dq : dfrac) (b : bv 8) :
    kmap_static (svpn_of pa) KP_rw ->
    kmap_static_claims -∗
    ctx_pointsto xi pa dq b -∗ ctx_phys_pointsto xi pa dq b.
  Proof.
    iIntros (Hs) "#Hb H".
    iDestruct (kmap_static_claims_at (svpn_of pa) KP_rw Hs with "Hb") as "#Hk0".
    iEval (rewrite ctx_pointsto_phys) in "H".
    iDestruct "H" as (ppn) "(#Hk & %Hc & %Hp & Hph)".
    iDestruct (kmap_at_agree with "Hk Hk0") as %[-> _].
    by iEval (rewrite (pa_of_id pa Hc)) in "Hph".
  Qed.

  (* the page fold, [KMap.mem_page_to_phys]'s twin. *)
  Lemma ctx_mem_page_to_phys (xi : CtxId) (p : mword 64) (dq : dfrac) (b : bv 8) :
    (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add p j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 4096, ctx_pointsto xi (pa_add p j) dq b) -∗
    ([∗ list] j ∈ seq 0 4096, ctx_phys_pointsto xi (pa_add p j) dq b).
  Proof.
    iIntros (Hstat) "#Hb Hbytes".
    iApply (big_sepL_impl with "Hbytes").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    iApply (ctx_mem_ident_phys xi (pa_add p (0 + k)%nat) dq b
              (Hstat (0 + k)%nat ltac:(lia)) with "Hb H").
  Qed.

  (* ================================================================== *)
  (* A6.69 THE READ-ONLY MINT AT A STATIC KERNEL-DATA ADDRESS, and its   *)
  (* WORD and BUFFER folds -- the kit item the boot 26 needs.            *)
  (*                                                                    *)
  (* [TsoCtx.ctx_pointsto_of_ro] asks the caller for a [ppn] and its     *)
  (* [kmap_at], and holds the element at the PHYSICAL address            *)
  (* [pa_of ppn a].  Every boot-carve site has neither: it has           *)
  (* [kmap_static_claims] (persistent, ambient) and an address it knows  *)
  (* is kernel data, and its elements ([BootCarve.boot_led_ran]) are     *)
  (* keyed at the address itself.  At a STATIC kernel-data mapping those *)
  (* two coincide -- [KMap.kmap_static_claims_at] pins the ppn to        *)
  (* [kpt_leaf_ppn] and [KptPt.pa_of_id] says [pa_of ppn a = a] -- so    *)
  (* this is the same mint with the identity discharged once.            *)
  (* ================================================================== *)
  Lemma ctx_pointsto_of_ro_static (xi : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) :
    kmap_static (svpn_of a) KP_rw ->
    (uint a < 274877906944)%Z ->
    kmap_static_claims -∗ mem_pointsto a dq v -∗ ledger_elem0 a dq -∗
    ctx_pointsto xi a dq v.
  Proof.
    iIntros (Hs Hc) "#Hb Hm He".
    iDestruct (kmap_static_claims_at (svpn_of a) KP_rw Hs with "Hb") as "#Hk".
    iApply (ctx_pointsto_of_ro xi a (kpt_leaf_ppn (svpn_of a)) dq v
              with "Hk Hm").
    rewrite (pa_of_id a Hc). iExact "He".
  Qed.

  (* the BUFFER fold: a byte run, element for element. *)
  Lemma ctx_buf_of_ro_static (xi : CtxId) (a : Arch.pa) (n : nat)
      (f : nat -> bv 8) (dq : dfrac) :
    (forall j : nat, (j < n)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j : nat, (j < n)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 n, mem_pointsto (pa_add a j) dq (f j)) -∗
    ([∗ list] j ∈ seq 0 n, ledger_elem0 (pa_add a j) dq) -∗
    ([∗ list] j ∈ seq 0 n, ctx_pointsto xi (pa_add a j) dq (f j)).
  Proof.
    iIntros (Hs Hc) "#Hb Hm He".
    iDestruct (big_sepL_sep_2 with "Hm He") as "Hme".
    iApply (big_sepL_impl with "Hme").
    iIntros "!>" (k j Hkj) "[Hm He]".
    apply lookup_seq in Hkj. destruct Hkj as [-> Hlt].
    iApply (ctx_pointsto_of_ro_static xi (pa_add a (0 + k)%nat) dq (f (0 + k)%nat)
              (Hs (0 + k)%nat ltac:(lia)) (Hc (0 + k)%nat ltac:(lia))
              with "Hb Hm He").
  Qed.

  (* the WORD fold: [ctx_word_pointsto]'s body is the buffer at width 8. *)
  Lemma ctx_word_pointsto_of_ro_static (xi : CtxId) (a : Arch.pa) (dq : dfrac)
      (w : bv 64) :
    (forall j : nat, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j : nat, (j < 8)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ word_pointsto a dq w -∗
    ([∗ list] j ∈ seq 0 8, ledger_elem0 (pa_add a j) dq) -∗
    ctx_word_pointsto xi a dq w.
  Proof.
    iIntros (Hs Hc) "#Hb [%Hal Hm] He".
    iApply (ctx_word_pointsto_intro xi a dq w Hal).
    iApply (ctx_buf_of_ro_static xi a 8 (nth_byte w) dq Hs Hc with "Hb Hm He").
  Qed.

  (* THE RETURN LEG of [ctx_mem_ident_phys], at a static kernel-data
     address: the context's PHYSICAL byte re-enters the VA family.  Both
     directions are available here (and only here) because the ledger
     residue never moves -- only the mapping plumbing does
     ([TsoCtx.ctx_pointsto_phys] is a [⊣⊢]).  This is the direction that is
     FALSE for the raw towers, which is why [KMap.phys_ident_mem] is not a
     substitute. *)
  Lemma ctx_phys_ident_mem (xi : CtxId) (pa : mword 64) (dq : dfrac) (b : bv 8) :
    kmap_static (svpn_of pa) KP_rw ->
    (uint pa < 274877906944)%Z ->
    kmap_static_claims -∗
    ctx_phys_pointsto xi pa dq b -∗ ctx_pointsto xi pa dq b.
  Proof.
    iIntros (Hs Hc) "#Hb Hp".
    iDestruct (kmap_static_claims_at (svpn_of pa) KP_rw Hs with "Hb") as "#Hk".
    iApply (ctx_pointsto_of_phys xi (kpt_leaf_ppn (svpn_of pa)) pa dq b
              (pa_of_id pa Hc) Hc
              (ktier_pin_of_id _ _ _ (pa_of_id pa Hc)) with "Hk Hp").
  Qed.

  (* the WORD fold of the return leg -- [BootBridge.phys_word_to_word]'s
     honest successor. *)
  Lemma ctx_phys_word_ident_mem (xi : CtxId) (a : Arch.pa) (dq : dfrac)
      (w : bv 64) :
    (forall j : nat, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j : nat, (j < 8)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗
    TsoCtx.ctx_phys_word_pointsto xi a dq w -∗ ctx_word_pointsto xi a dq w.
  Proof.
    iIntros (Hs Hc) "#Hb Hw".
    iDestruct (TsoCtx.ctx_phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iApply (ctx_word_pointsto_intro xi a dq w Hal).
    iDestruct (TsoCtx.ctx_phys_word_pointsto_bytes with "Hw") as "Hbs".
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k j Hkj) "Hp".
    apply lookup_seq in Hkj. destruct Hkj as [-> Hlt].
    iApply (ctx_phys_ident_mem xi (pa_add a (0 + k)%nat) dq (nth_byte w (0 + k)%nat)
              (Hs (0 + k)%nat ltac:(lia)) (Hc (0 + k)%nat ltac:(lia)) with "Hb Hp").
  Qed.

End CtxKMap.
