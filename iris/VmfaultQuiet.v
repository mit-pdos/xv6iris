(* VmfaultQuiet.v -- the PURE fact that vmfault's success arm cannot fire
   for a process whose lazy flag is off.

   [SpecVmfault]'s success arm (the one that allocates a page and inserts
   it at [svpn_of va0], [va0 := PGROUNDDOWN va]) requires

       uint va < uint szv        and        ud_um P !! svpn_of va0 = None,

   under the contract's premise [uint szv <= 2 ^ 38].  A process with the
   lazy flag off carries [UserPerm.lazy_free (ud_um P) (uint (pv_sz V))]:
   every page below the rounded-up size is already mapped.  The rounded
   fault address's page is one of those live pages ([vmfault_vpn_live]),
   so the success arm is contradictory ([vmfault_quiet]): at [lazy_free]
   vmfault never reaches kalloc.

   This is the fault arm of the in-logic strong instance -- a quiet
   (non-syscall) round cannot allocate through vmfault.  No Iris, no
   ghost state.

   Design: claude-notes/design/ni-strong-instance.md (§0, §3 "The vmfault
   fact"). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import RiscvPtsto RiscvExtras.
Require Import UserPerm ProcPtOwn.
Local Open Scope Z_scope.

(* the rounded fault address's page is live below the size *)
Lemma vmfault_vpn_live (szv va : mword 64) :
  (uint szv <= 2 ^ 38)%Z ->
  (uint va < uint szv)%Z ->
  svpn_of (and_vec va (mword_of_int (-4096))) ∈ live_pages (uint szv).
Proof.
  intros Hsz Hva. rewrite (uint_unsigned szv) in Hsz, Hva |- *.
  rewrite (uint_unsigned va) in Hva.
  apply live_pages_mem.
  pose proof (svpn_of_pgd_below va szv Hsz Hva) as Hlt.
  pose proof (pgroundup_ge (bv_unsigned szv)
                (proj1 (bv_unsigned_in_range _ szv))) as Hge.
  lia.
Qed.

(* THE QUIET FACT: at lazy_free, vmfault's success arm is impossible *)
Lemma vmfault_quiet (um : gmap (mword 27) (mword 64)) (szv va : mword 64) :
  (uint szv <= 2 ^ 38)%Z ->
  lazy_free um (uint szv) ->
  (uint va < uint szv)%Z ->
  um !! svpn_of (and_vec va (mword_of_int (-4096))) = None ->
  False.
Proof.
  intros Hsz Hlf Hva Hnone.
  pose proof (Hlf _ (vmfault_vpn_live szv va Hsz Hva)) as Hdom.
  apply elem_of_dom in Hdom. rewrite Hnone in Hdom.
  by destruct Hdom.
Qed.
