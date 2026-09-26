(* ===================================================================== *)
(* UkHandler.v -- THE ENDPOINT INTERFACE AND THE ONCE-GLUE: a conforming   *)
(* tree is paid from its environment's resources, once, by coinduction.  *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.3-3.4c.  [ProgTree.    *)
(* conforms E t] is the pure half: every path of [t] writes a prefix of   *)
(* an alternative it chooses, reads any chunking of its input, is ready   *)
(* for either answer of an open, and exits drained; [safe_fds held t] is  *)
(* its descriptor discipline under ANY answer (closes only what it        *)
(* holds, reads at least a byte).  This file is the logic's half:         *)
(*                                                                        *)
(*   [ep_iface]   what an application provides -- a resource per binding  *)
(*                of descriptors to devices ([ei_fds fdm], a finite map;  *)
(*                the descriptors held are its domain), per device at     *)
(*                what it owes or has left ([ei_out], [ei_outh],           *)
(*                [ei_outm], [ei_halt], [ei_in], [ei_in_e], [ei_in_end],   *)
(*                and the filter device [ei_copy], [ei_copy_end],          *)
(*                [ei_copy_halt] -- design SS3.4f, grep-pipes.md SS1),     *)
(*                for the files it describes ([ei_files files paths]),    *)
(*                and the TAINT ([ei_taint held]: the application gave up  *)
(*                describing, the process keeps its handles) -- and its   *)
(*                LAWS AT THE HOLES of [UkTree].  Every law's continuation *)
(*                has a taint arm: a kernel leaf may hand the taint in     *)
(*                place of an answer; the taint then pays the rest of any *)
(*                tree with the discipline ([ei_taint_pays]).  A close of *)
(*                a device's LAST descriptor consumes the device (its     *)
(*                number may then be reused by an open); a shared one     *)
(*                (a dup) keeps it.                                       *)
(*   [env_res]    the environment's resources, one per device of a finite *)
(*                set that every bound descriptor's device belongs to.    *)
(*   [tree_pay_of_conforms]                                               *)
(*                conforms E t -> safe_fds (dom (pe_fd E)) t ->            *)
(*                env_res E ds -| tree_pay t.                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import ProcGeom.
Require Import FdSlots UserFd.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import ProgTree UkTree.
Local Open Scope Z_scope.
Import Defs.

(* descriptors to devices *)
Definition fdmap := gmap Z nat.

(* another descriptor of [fdm] names [d] *)
Definition fd_shared (fdm : fdmap) (fd : Z) (d : nat) : Prop :=
  set_Exists (fun fd' => fdm !! fd' = Some d) (dom (delete fd fdm)).

Global Instance fd_shared_dec (fdm : fdmap) (fd : Z) (d : nat) : Decision (fd_shared fdm fd d).
Proof. apply _. Defined.

(* no other descriptor names it: the descriptor is the device's last *)
Lemma fd_last_of_not_shared (fdm : fdmap) (fd : Z) (d : nat) :
  ~ fd_shared fdm fd d -> fd_last fdm fd d.
Proof.
  intros Hns fd' Hne Hfd'. apply Hns. exists fd'. split; [| exact Hfd'].
  apply elem_of_dom. rewrite lookup_delete_ne; [| congruence]. by eexists.
Qed.

(* THE PROTECTED DEVICES (design SS3.4e, lane D).  An instance whose exit
   payload is a wand over its final state (the file application's) cannot
   pay the exit after a close CONSUMED one of the devices it was entered
   with -- the console cursor the round is owed would be gone -- so the
   record carries a list [Dp] of device numbers whose last descriptor's
   close is a SHARED close (the device stays, its descriptor goes; the
   tree's exit rule asks every device drained, closed or not), which an
   open never mints again and which the exit finds among the drained
   devices.  The three premises below are Fixpoints on [Dp] so that at
   [Dp = []] each is DEFINITIONALLY the premise the landed instances were
   proved at; [ep_iface]/[MkEI] are the record at [[]]. *)
Fixpoint fd_shared_p (Dp : list nat) (fdm : fdmap) (fd : Z) (d : nat) : Prop :=
  match Dp with
  | [] => fd_shared fdm fd d
  | x :: r => d = x \/ fd_shared_p r fdm fd d
  end.

Fixpoint dev_fresh_p (Dp : list nat) (fdm : fdmap) (d : nat) : Prop :=
  match Dp with
  | [] => forall fd', fdm !! fd' <> Some d
  | x :: r => d <> x /\ dev_fresh_p r fdm d
  end.

Fixpoint dom_ok_p (Dp : list nat) (fdm : fdmap) (ds : gset nat) : Prop :=
  match Dp with
  | [] => forall fd d, fdm !! fd = Some d -> d ∈ ds
  | x :: r => x ∈ ds /\ dom_ok_p r fdm ds
  end.

Definition dp_in (Dp : list nat) (ds : gset nat) : Prop := forall d, d ∈ Dp -> d ∈ ds.

Lemma fd_shared_p_iff (Dp : list nat) (fdm : fdmap) (fd : Z) (d : nat) :
  fd_shared_p Dp fdm fd d <-> d ∈ Dp \/ fd_shared fdm fd d.
Proof.
  induction Dp as [| x r IH]; simpl.
  - split; [by right | intros [H | H]; [by apply elem_of_nil in H | exact H]].
  - rewrite IH elem_of_cons. tauto.
Qed.

Lemma dev_fresh_p_iff (Dp : list nat) (fdm : fdmap) (d : nat) :
  dev_fresh_p Dp fdm d <-> d ∉ Dp /\ forall fd', fdm !! fd' <> Some d.
Proof.
  induction Dp as [| x r IH]; simpl.
  - split; [intros H; split; [apply not_elem_of_nil | exact H] | tauto].
  - rewrite IH not_elem_of_cons. tauto.
Qed.

Lemma dom_ok_p_iff (Dp : list nat) (fdm : fdmap) (ds : gset nat) :
  dom_ok_p Dp fdm ds <-> dp_in Dp ds /\ forall fd d, fdm !! fd = Some d -> d ∈ ds.
Proof.
  unfold dp_in. induction Dp as [| x r IH]; simpl.
  - split; [intros H; split; [intros d Hd; by apply elem_of_nil in Hd | exact H] | tauto].
  - rewrite IH. split.
    + intros (Hx & Hr & H). split; [| exact H]. intros d Hd. apply elem_of_cons in Hd as [-> | Hd]; [exact Hx | by apply Hr].
    + intros (Hr & H). split; [apply Hr; by left |]. split; [| exact H]. intros d Hd. apply Hr. by right.
Qed.

Global Instance fd_shared_p_dec (Dp : list nat) (fdm : fdmap) (fd : Z) (d : nat) :
  Decision (fd_shared_p Dp fdm fd d).
Proof. induction Dp as [| x r IH]; simpl; apply _. Defined.

Section UkHandler.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* the protected devices (above); implicit, so that every constant of
     this section reads it off its record argument *)
  Context {Dp : list nat}.
  Context (N : uk_names Σ).
  Context (P : uprog Σ).

  (* ------------------------------------------------------------------- *)
  (*  1.  THE INTERFACE                                                   *)
  (* ------------------------------------------------------------------- *)

  (* the answer of an open, as the kernel gives it *)
  Definition open_held (fdm : fdmap) (x : Z) : gset Z :=
    if decide (0 <= x) then {[x]} ∪ dom fdm else dom fdm.

  Record ep_ifaceP := MkEIP {
    ei_fds : fdmap -> iProp Σ;
    ei_out : nat -> list bytes -> iProp Σ;
    ei_outh : nat -> list bytes -> iProp Σ;    (* an output that may halt *)
    ei_halt : nat -> iProp Σ;                  (* ...and has *)
    ei_outm : nat -> list bytes -> iProp Σ;    (* an output where a write may miss, owed as chunks *)
    ei_in : nat -> bytes -> iProp Σ;
    ei_in_e : nat -> bytes -> iProp Σ;         (* an input that may end early *)
    ei_in_end : nat -> iProp Σ;                (* ...and has *)
    (* the filter device (design SS3.4f, grep-pipes.md SS1): one number on
       both of a filter's descriptors; the filter, whether the sink may
       halt, the input read so far, the input still to come, and the
       output owed and not yet written *)
    ei_copy : nat -> pfilter -> bool -> bytes -> bytes -> bytes -> iProp Σ;
    ei_copy_end : nat -> pfilter -> bool -> bytes -> iProp Σ;   (* the writer closed *)
    (* the sink's reader went; the input still to come, or its end *)
    ei_copy_halt : nat -> option bytes -> iProp Σ;
    (* the producer device ([ProgTree.DProd], union.md C9d'): one number on
       a producer's output and its diagnostics; the output owes one of
       [outs], the diagnostics one of [ds] or a failure report of [xs] *)
    ei_prod : nat -> list bytes -> list bytes -> list bytes -> iProp Σ;
    ei_prod_halt : nat -> list bytes -> iProp Σ;     (* the output's reader went *)
    ei_files : (bytes -> option bytes) -> list bytes -> iProp Σ;
    (* THE TAINT at the descriptors the process holds: it pays the rest of
       any tree with the discipline *)
    ei_taint : gset Z -> iProp Σ;
    ei_taint_pays : forall (held : gset Z) (t : proc),
        safe_fds held t -> ei_taint held -∗ tree_pay N P t;
    (* a write of a chunk the chosen alternative begins with: the count
       comes back exactly, the device owes that alternative's rest *)
    ei_write : forall (fdm : fdmap) (fd : Z) (d : nat) (alts : list bytes)
                 (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_out d alts -∗
        ((ei_fds fdm -∗ ei_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* at a haltable device the payer answers the count, or -1 and halts *)
    ei_write_h : forall (fdm : fdmap) (fd : Z) (d : nat) (alts : list bytes)
                   (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_outh d alts -∗
        ((ei_fds fdm -∗ ei_outh d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (ei_fds fdm -∗ ei_halt d -∗ K (-1))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* at a device where a write may miss, owed as chunks: the next chunk
       whole, the count or -1, the device owing the rest either way *)
    ei_write_m : forall (fdm : fdmap) (fd : Z) (d : nat) (rest : list bytes)
                   (bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d ->
        ei_fds fdm -∗ ei_outm d (bs :: rest) -∗
        ((ei_fds fdm -∗ ei_outm d rest -∗ K (Z.of_nat (length bs)))
         ∧ (ei_fds fdm -∗ ei_outm d rest -∗ K (-1))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* ...at a count the kernel reads as a positive C int ([ProgTree.
       cf_write_halt]) *)
    ei_write_halt : forall (fdm : fdmap) (fd : Z) (d : nat) (bs : bytes)
                      (K : Z -> iProp Σ),
        bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fdm !! fd = Some d ->
        ei_fds fdm -∗ ei_halt d -∗
        ((ei_fds fdm -∗ ei_halt d -∗ K (-1)) ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* a zero-length write: 0 or -1, nothing moves (the device, whatever its
       kind, is lent and returned) *)
    ei_write_nil : forall (fdm : fdmap) (fd : Z) (d : nat) (x : dspec) (K : Z -> iProp Σ),
        fdm !! fd = Some d ->
        ei_fds fdm -∗
        (match x with
         | DOut alts => ei_out d alts | DOutH alts => ei_outh d alts
         | DOutM cs => ei_outm d cs | DHalt => ei_halt d
         | DIn Sin => ei_in d Sin | DInE Sin => ei_in_e d Sin | DInEnd => ei_in_end d
         | DCopy F h Rr Sin p => ei_copy d F h Rr Sin p | DCopyEnd F h p => ei_copy_end d F h p
         | DCopyHalt oS => ei_copy_halt d oS
         | DProd outs xs ds => ei_prod d outs xs ds | DProdHalt ds => ei_prod_halt d ds
         end) -∗
        ((ei_fds fdm -∗
          (match x with
           | DOut alts => ei_out d alts | DOutH alts => ei_outh d alts
           | DOutM cs => ei_outm d cs | DHalt => ei_halt d
           | DIn Sin => ei_in d Sin | DInE Sin => ei_in_e d Sin | DInEnd => ei_in_end d
           | DCopy F h Rr Sin p => ei_copy d F h Rr Sin p | DCopyEnd F h p => ei_copy_end d F h p
           | DCopyHalt oS => ei_copy_halt d oS
           | DProd outs xs ds => ei_prod d outs xs ds | DProdHalt ds => ei_prod_halt d ds
           end) -∗ K 0)
         ∧ (ei_fds fdm -∗
            (match x with
             | DOut alts => ei_out d alts | DOutH alts => ei_outh d alts
             | DOutM cs => ei_outm d cs | DHalt => ei_halt d
             | DIn Sin => ei_in d Sin | DInE Sin => ei_in_e d Sin | DInEnd => ei_in_end d
             | DCopy F h Rr Sin p => ei_copy d F h Rr Sin p | DCopyEnd F h p => ei_copy_end d F h p
             | DCopyHalt oS => ei_copy_halt d oS
             | DProd outs xs ds => ei_prod d outs xs ds | DProdHalt ds => ei_prod_halt d ds
             end) -∗ K (-1))
         ∧ (∀ y, ei_taint (dom fdm) -∗ K y)) -∗
        wr_obl N P fd [] K;
    (* a read of at least one byte: some chunk of what is left, empty only
       at end of file *)
    ei_read : forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : bytes) (n : nat)
                (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm !! fd = Some d ->
        ei_fds fdm -∗ ei_in d Sin -∗
        ((∀ (c S' : bytes), ⌜chunk_ok n Sin c S'⌝ -∗
            ei_fds fdm -∗ ei_in d S' -∗ K (RdBytes c))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        rd_obl N P fd n K;
    (* ...at an input that may end early: a chunk, or end of file *)
    ei_read_e : forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : bytes) (n : nat)
                  (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm !! fd = Some d ->
        ei_fds fdm -∗ ei_in_e d Sin -∗
        ((∀ (c S' : bytes), ⌜chunk_ok n Sin c S'⌝ -∗
            ei_fds fdm -∗ ei_in_e d S' -∗ K (RdBytes c))
         ∧ (ei_fds fdm -∗ ei_in_end d -∗ K (RdBytes []))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        rd_obl N P fd n K;
    ei_read_end : forall (fdm : fdmap) (fd : Z) (d : nat) (n : nat) (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm !! fd = Some d ->
        ei_fds fdm -∗ ei_in_end d -∗
        ((ei_fds fdm -∗ ei_in_end d -∗ K (RdBytes [])) ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        rd_obl N P fd n K;
    (* a read at the filter device, at the filter's input ([ProgTree.
       copy_in]): a NONEMPTY chunk of the input adds what it owes to what is
       pending, or the writer closed (end of file) *)
    ei_read_copy : forall (fdm : fdmap) (fd : Z) (d : nat) (F : pfilter) (h : bool)
                     (Rr Sin p : bytes) (n : nat) (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
        ei_fds fdm -∗ ei_copy d F h Rr Sin p -∗
        ((∀ (c S' : bytes), ⌜chunk_ok n Sin c S'⌝ -∗ ⌜c <> []⌝ -∗
            ei_fds fdm -∗ ei_copy d F h (Rr ++ c) S' (p ++ flt_new F Rr c) -∗ K (RdBytes c))
         ∧ (ei_fds fdm -∗ ei_copy_end d F h p -∗ K (RdBytes []))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        rd_obl N P fd n K;
    ei_read_copy_end : forall (fdm : fdmap) (fd : Z) (d : nat) (F : pfilter) (h : bool) (p : bytes)
                         (n : nat) (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
        ei_fds fdm -∗ ei_copy_end d F h p -∗
        ((ei_fds fdm -∗ ei_copy_end d F h p -∗ K (RdBytes [])) ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        rd_obl N P fd n K;
    (* ...at a HALTED one the input goes on ([ProgTree.cf_read_copy_halt]):
       a nonempty chunk, or end of file, after which reads answer 0 *)
    ei_read_copy_halt : forall (fdm : fdmap) (fd : Z) (d : nat) (Sin : bytes) (n : nat)
                          (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
        ei_fds fdm -∗ ei_copy_halt d (Some Sin) -∗
        ((∀ (c S' : bytes), ⌜chunk_ok n Sin c S'⌝ -∗ ⌜c <> []⌝ -∗
            ei_fds fdm -∗ ei_copy_halt d (Some S') -∗ K (RdBytes c))
         ∧ (ei_fds fdm -∗ ei_copy_halt d None -∗ K (RdBytes []))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        rd_obl N P fd n K;
    ei_read_copy_halt_end : forall (fdm : fdmap) (fd : Z) (d : nat) (n : nat) (K : rd_ans -> iProp Σ),
        (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
        ei_fds fdm -∗ ei_copy_halt d None -∗
        ((ei_fds fdm -∗ ei_copy_halt d None -∗ K (RdBytes [])) ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        rd_obl N P fd n K;
    (* a write at the filter device, at the filter's output ([ProgTree.
       copy_out]), drains a prefix of what is pending: the count comes back
       exactly; at a sink that may halt ([h = true]) the payer may instead
       answer -1 and halt the device, which keeps the input's rest *)
    ei_write_copy : forall (fdm : fdmap) (fd : Z) (d : nat) (F : pfilter) (Rr Sin p bs : bytes)
                      (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
        ei_fds fdm -∗ ei_copy d F false Rr Sin p -∗
        ((ei_fds fdm -∗ ei_copy d F false Rr Sin (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_copy_h : forall (fdm : fdmap) (fd : Z) (d : nat) (F : pfilter) (Rr Sin p bs : bytes)
                        (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
        ei_fds fdm -∗ ei_copy d F true Rr Sin p -∗
        ((ei_fds fdm -∗ ei_copy d F true Rr Sin (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
         ∧ (ei_fds fdm -∗ ei_copy_halt d (Some Sin) -∗ K (-1))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_copy_end : forall (fdm : fdmap) (fd : Z) (d : nat) (F : pfilter) (p bs : bytes)
                          (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
        ei_fds fdm -∗ ei_copy_end d F false p -∗
        ((ei_fds fdm -∗ ei_copy_end d F false (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_copy_end_h : forall (fdm : fdmap) (fd : Z) (d : nat) (F : pfilter) (p bs : bytes)
                            (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
        ei_fds fdm -∗ ei_copy_end d F true p -∗
        ((ei_fds fdm -∗ ei_copy_end d F true (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
         ∧ (ei_fds fdm -∗ ei_copy_halt d None -∗ K (-1))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_copy_halt : forall (fdm : fdmap) (fd : Z) (d : nat) (oS : option bytes) (bs : bytes)
                           (K : Z -> iProp Σ),
        bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fdm !! fd = Some d -> fd = copy_out ->
        ei_fds fdm -∗ ei_copy_halt d oS -∗
        ((ei_fds fdm -∗ ei_copy_halt d oS -∗ K (-1)) ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    (* an open of a described, present file: a descriptor the process did
       not hold, bound to a device of the glue's choosing at the content --
       or the kernel's -1; the taint arm at an answer the kernel can give *)
    ei_open : forall (fdm : fdmap) (files : bytes -> option bytes) (paths : list bytes)
                (path content : bytes) (K : Z -> iProp Σ),
        path ∈ paths -> files path = Some content ->
        ei_fds fdm -∗ ei_files files paths -∗
        ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm !! fd = None⌝ -∗
            (∀ d : nat, ⌜dev_fresh_p Dp fdm d⌝ -∗
               ei_fds (<[fd := d]> fdm) ∗ ei_in d content) -∗
            ei_files files paths -∗ K fd)
         ∧ (ei_fds fdm -∗ ei_files files paths -∗ K (-1))
         ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ ei_taint (open_held fdm x) -∗ K x)) -∗
        op_obl N P path 0 K;
    (* an open of a described, absent file, at a mode that does not create *)
    ei_open_absent : forall (fdm : fdmap) (files : bytes -> option bytes) (paths : list bytes)
                       (path : bytes) (m : Z) (K : Z -> iProp Σ),
        path ∈ paths -> ~ mode_create m -> files path = None ->
        ei_fds fdm -∗ ei_files files paths -∗
        ((ei_fds fdm -∗ ei_files files paths -∗ K (-1))
         ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ ei_taint (open_held fdm x) -∗ K x)) -∗
        op_obl N P path m K;
    (* a close of a device's last descriptor consumes the device (the files
       keep what it gives back, a deed's fraction); a copy device or a
       haltable output is drained there ([ProgTree.cf_close]) *)
    ei_close : forall (fdm : fdmap) (fd : Z) (d : nat) (x : dspec)
                 (files : bytes -> option bytes) (paths : list bytes) (K : Z -> iProp Σ),
        fdm !! fd = Some d -> ~ fd_shared_p Dp fdm fd d -> drained_at_close x ->
        ei_fds fdm -∗ ei_files files paths -∗
        (match x with
         | DOut alts => ei_out d alts | DOutH alts => ei_outh d alts
         | DOutM cs => ei_outm d cs | DHalt => ei_halt d
         | DIn Sin => ei_in d Sin | DInE Sin => ei_in_e d Sin | DInEnd => ei_in_end d
         | DCopy F h Rr Sin p => ei_copy d F h Rr Sin p | DCopyEnd F h p => ei_copy_end d F h p
         | DCopyHalt oS => ei_copy_halt d oS
         | DProd outs xs ds => ei_prod d outs xs ds | DProdHalt ds => ei_prod_halt d ds
         end) -∗
        ((ei_fds (delete fd fdm) -∗ ei_files files paths -∗ K 0)
         ∧ (∀ y, ei_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
        cl_obl N P fd K;
    (* ...of a shared one (a dup) keeps it *)
    ei_close_shared : forall (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ),
        fdm !! fd = Some d -> fd_shared_p Dp fdm fd d ->
        ei_fds fdm -∗
        ((ei_fds (delete fd fdm) -∗ K 0) ∧ (∀ y, ei_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
        cl_obl N P fd K;
    (* the exit, with every device drained: the instance receives the
       descriptors, the files and every device (the exit payload is built
       from them; design SS3.4e), and the fact that every bound device is
       among them *)
    ei_exit : forall (s : Z) (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
                     (paths : list (list (bv 8))) (dv : nat -> dspec) (ds : gset nat),
        (forall d, d ∈ ds -> drained (dv d)) ->
        dom_ok_p Dp fdm ds ->
        ei_fds fdm -∗ ei_files files paths -∗
        ([∗ set] d ∈ ds, match dv d with
                         | DOut alts => ei_out d alts | DOutH alts => ei_outh d alts
                         | DOutM cs => ei_outm d cs | DHalt => ei_halt d
                         | DIn Sin => ei_in d Sin | DInE Sin => ei_in_e d Sin | DInEnd => ei_in_end d
                         | DCopy F h Rr Sin p => ei_copy d F h Rr Sin p | DCopyEnd F h p => ei_copy_end d F h p
                         | DCopyHalt oS => ei_copy_halt d oS
                         | DProd outs xs ds => ei_prod d outs xs ds | DProdHalt ds => ei_prod_halt d ds
                         end) -∗
        ex_obl N P s;
    (* THE PRODUCER DEVICE'S LAWS ([ProgTree.cf_write_prod] and its four
       siblings): an output write, as at a haltable output, retiring the
       failure reports; a diagnostic write, as at the console, choosing a
       diagnostic or -- the output still able to owe nothing -- a failure
       report, after which the output owes nothing *)
    ei_write_prod : forall (fdm : fdmap) (fd : Z) (d : nat) (outs xs ds : list bytes)
                      (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = prod_out -> a ∈ outs -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_prod d outs xs ds -∗
        ((ei_fds fdm -∗ ei_prod d [drop (length bs) a] [] ds -∗ K (Z.of_nat (length bs)))
         ∧ (ei_fds fdm -∗ ei_prod_halt d ds -∗ K (-1))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_prod_halt : forall (fdm : fdmap) (fd : Z) (d : nat) (ds : list bytes)
                           (bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fdm !! fd = Some d -> fd = prod_out ->
        ei_fds fdm -∗ ei_prod_halt d ds -∗
        ((ei_fds fdm -∗ ei_prod_halt d ds -∗ K (-1)) ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_prod_err : forall (fdm : fdmap) (fd : Z) (d : nat) (outs xs ds : list bytes)
                          (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = prod_err -> a ∈ ds -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_prod d outs xs ds -∗
        ((ei_fds fdm -∗ ei_prod d outs [] [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_prod_fail : forall (fdm : fdmap) (fd : Z) (d : nat) (outs xs ds : list bytes)
                           (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = prod_err -> [] ∈ outs -> a ∈ xs ->
        bs `prefix_of` a ->
        ei_fds fdm -∗ ei_prod d outs xs ds -∗
        ((ei_fds fdm -∗ ei_prod d [[]] [] [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
    ei_write_prod_halt_err : forall (fdm : fdmap) (fd : Z) (d : nat) (ds : list bytes)
                               (a bs : bytes) (K : Z -> iProp Σ),
        bs <> [] -> fdm !! fd = Some d -> fd = prod_err -> a ∈ ds -> bs `prefix_of` a ->
        ei_fds fdm -∗ ei_prod_halt d ds -∗
        ((ei_fds fdm -∗ ei_prod_halt d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
         ∧ (∀ x, ei_taint (dom fdm) -∗ K x)) -∗
        wr_obl N P fd bs K;
  }.

  (* ------------------------------------------------------------------- *)
  (*  2.  THE ENVIRONMENT'S RESOURCES                                     *)
  (* ------------------------------------------------------------------- *)

  Definition dev_of (I : ep_ifaceP) (d : nat) (x : dspec) : iProp Σ :=
    match x with
    | DOut alts => ei_out I d alts | DOutH alts => ei_outh I d alts
    | DOutM cs => ei_outm I d cs | DHalt => ei_halt I d
    | DIn Sin => ei_in I d Sin | DInE Sin => ei_in_e I d Sin | DInEnd => ei_in_end I d
    | DCopy F h Rr Sin p => ei_copy I d F h Rr Sin p | DCopyEnd F h p => ei_copy_end I d F h p
    | DCopyHalt oS => ei_copy_halt I d oS
    | DProd outs xs ds => ei_prod I d outs xs ds | DProdHalt ds => ei_prod_halt I d ds
    end.

  Definition dev_res (I : ep_ifaceP) (dv : nat -> dspec) (ds : gset nat) : iProp Σ :=
    ([∗ set] d ∈ ds, dev_of I d (dv d))%I.

  Definition env_res (I : ep_ifaceP) (E : penv) (ds : gset nat) : iProp Σ :=
    (⌜forall fd d, pe_fd E !! fd = Some d -> d ∈ ds⌝
     ∗ ei_fds I (pe_fd E) ∗ ei_files I (pe_files E) (pe_paths E)
     ∗ dev_res I (pe_dev E) ds)%I.

  Lemma dev_res_take (I : ep_ifaceP) (dv : nat -> dspec) (ds : gset nat) (d : nat) :
    d ∈ ds ->
    dev_res I dv ds ⊣⊢ dev_of I d (dv d) ∗ dev_res I dv (ds ∖ {[d]}).
  Proof using . intros Hd. unfold dev_res. by apply (big_sepS_delete (fun d => dev_of I d (dv d)) ds d Hd). Qed.

  (* changing one device's spec changes nothing outside it *)
  Lemma dev_res_set (I : ep_ifaceP) (dv : nat -> dspec) (ds : gset nat) (d : nat)
      (x : dspec) :
    d ∉ ds ->
    dev_res I (fun d' => if decide (d' = d) then x else dv d') ds ⊣⊢ dev_res I dv ds.
  Proof using .
    intros Hd. unfold dev_res. apply big_sepS_proper. intros d' Hd'.
    rewrite decide_False; [reflexivity |]. intros ->. done.
  Qed.

  Lemma env_set_dev_pe_dev (E : penv) (d : nat) (x : dspec) :
    pe_dev (env_set_dev E d x) = fun d' => if decide (d' = d) then x else pe_dev E d'.
  Proof using . reflexivity. Qed.

  (* setting a device to what it already is changes nothing *)
  Lemma env_set_dev_id (E : penv) (d : nat) (x : dspec) :
    pe_dev E d = x -> env_set_dev E d x = E.
  Proof using .
    intros Hd. destruct E as [f g files paths]. unfold env_set_dev. simpl in *. f_equal.
    apply functional_extensionality. intros d'.
    destruct (decide (d' = d)) as [-> |]; [by rewrite Hd | reflexivity].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  THE ONCE-GLUE                                                   *)
  (* ------------------------------------------------------------------- *)

  (* the invariant: a conforming tree with the discipline at its
     environment, or a tree already paid *)
  Definition cf_inv (I : ep_ifaceP) (t : proc) : iProp Σ :=
    ((∃ (E : penv) (ds : gset nat),
        ⌜conforms E t⌝ ∗ ⌜safe_fds (dom (pe_fd E)) t⌝ ∗ ⌜dp_in Dp ds⌝ ∗ env_res I E ds)
     ∨ tree_pay N P t)%I.

  Lemma cf_inv_taint (I : ep_ifaceP) (held : gset Z) (t : proc) :
    safe_fds held t -> ei_taint I held -∗ cf_inv I t.
  Proof using . intros Hs. iIntros "Ht". iRight. iApply (ei_taint_pays I held t Hs with "Ht"). Qed.

  (* the invariant rebuilt after one device moved to a new spec, the rest
     of the environment unchanged *)
  Lemma cf_inv_move (I : ep_ifaceP) (E : penv) (ds : gset nat) (d : nat) (x : dspec) (t : proc) :
    d ∈ ds ->
    conforms (env_set_dev E d x) t -> safe_fds (dom (pe_fd E)) t -> dp_in Dp ds ->
    (forall fd d', pe_fd E !! fd = Some d' -> d' ∈ ds) ->
    ei_fds I (pe_fd E) -∗ ei_files I (pe_files E) (pe_paths E) -∗
    dev_of I d x -∗ dev_res I (pe_dev E) (ds ∖ {[d]}) -∗
    cf_inv I t.
  Proof using .
    intros Hin Hc Hs Hdp Hdom. iIntros "Hfds Hfiles Hx Hrest".
    iLeft. iExists (env_set_dev E d x), ds.
    iSplit; [done |]. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
    iFrame "Hfds Hfiles".
    rewrite (dev_res_take I _ ds d Hin). iSplitL "Hx".
    { rewrite env_set_dev_pe_dev decide_True; [| reflexivity]. iExact "Hx". }
    assert (Hnot : d ∉ ds ∖ {[d]}) by set_solver.
    rewrite env_set_dev_pe_dev (dev_res_set I (pe_dev E) (ds ∖ {[d]}) d _ Hnot).
    iExact "Hrest".
  Qed.

  (* ...and with nothing moved *)
  Lemma cf_inv_same (I : ep_ifaceP) (E : penv) (ds : gset nat) (t : proc) :
    conforms E t -> safe_fds (dom (pe_fd E)) t -> dp_in Dp ds ->
    (forall fd d', pe_fd E !! fd = Some d' -> d' ∈ ds) ->
    ei_fds I (pe_fd E) -∗ ei_files I (pe_files E) (pe_paths E) -∗
    dev_res I (pe_dev E) ds -∗ cf_inv I t.
  Proof using .
    intros Hc Hs Hdp Hdom. iIntros "Hfds Hfiles Hdev".
    iLeft. iExists E, ds. iFrame. done.
  Qed.

  Lemma cf_inv_step (I : ep_ifaceP) :
    ⊢ □ (∀ t, cf_inv I t -∗ tree_F N P (cf_inv I) t).
  Proof using .
    iIntros "!>" (t) "[(%E & %ds & %Hc & %Hs & %Hdp & %Hdom & Hfds & Hfiles & Hdev) | Hpay]"; last first.
    { (* already paid: unfold, and every subtree is paid *)
      rewrite tree_pay_unfold.
      iApply (tree_F_mono_law N P (tree_pay N P) (cf_inv I) with "[] Hpay").
      iIntros "!>" (t') "Ht'". iRight. iExact "Ht'". }
    apply conforms_unfold in Hc. apply safe_fds_unfold in Hs.
    destruct t as [v | t' | e k].
    - destruct v.
    - (* Tau *)
      simpl in Hc, Hs. simpl. iApply (cf_inv_same with "Hfds Hfiles Hdev"); done.
    - destruct e as [path mode | fd | fd n | fd bs | s]; simpl in Hc, Hs; simpl.
      + (* EOpen *)
        destruct Hs as [Hs_fd Hs_neg].
        assert (Htaint : forall x, x = -1 \/ 0 <= x -> safe_fds (open_held (pe_fd E) x) (k x)).
        { intros x [-> | Hx]; unfold open_held.
          - case_decide; [lia | exact Hs_neg].
          - case_decide; [by apply Hs_fd | lia]. }
        destruct Hc as (Hpath & [(-> & content & Hfile & Hk & Hk1) | (Hnc & Hfile & Hk1)]).
        * (* present *)
          iApply (ei_open I (pe_fd E) (pe_files E) (pe_paths E) path content
                    with "Hfds Hfiles"); [exact Hpath | exact Hfile |].
          iSplit; [| iSplit].
          { iIntros (fd) "%Hfd0 %Hnone Hbind Hfiles".
            (* a device no descriptor names *)
            set (d := fresh ds).
            assert (Hfr : forall fd', pe_fd E !! fd' <> Some d).
            { intros fd' Heq. apply Hdom in Heq. apply (is_fresh ds Heq). }
            iDestruct ("Hbind" $! d with "[%]") as "[Hfds Hin]".
            { apply dev_fresh_p_iff. split; [| exact Hfr].
              intros Hd. apply (is_fresh ds). apply Hdp. exact Hd. }
            iLeft. iExists (env_set_dev (env_bind E fd d) d (DIn content)), ({[d]} ∪ ds).
            iSplit.
            { iPureIntro. apply Hk; [lia | exact Hnone | exact Hfr]. }
            iSplit.
            { iPureIntro. cbv [env_set_dev env_bind pe_fd]. rewrite dom_insert_L.
              apply Hs_fd. lia. }
            iSplit.
            { iPureIntro. intros d' Hd'. apply elem_of_union. right. by apply Hdp. }
            iSplit.
            { iPureIntro. intros fd' d'. cbv [env_set_dev env_bind pe_fd].
              destruct (decide (fd' = fd)) as [-> | Hne].
              - rewrite lookup_insert. intros [= ->]. set_solver.
              - rewrite lookup_insert_ne; [| done]. intros Hin. apply Hdom in Hin. set_solver. }
            iFrame "Hfds Hfiles".
            assert (Hnot : d ∉ ds) by apply is_fresh.
            rewrite (dev_res_take I _ ({[d]} ∪ ds) d ltac:(set_solver)).
            iSplitL "Hin".
            { rewrite env_set_dev_pe_dev decide_True; [| reflexivity]. simpl. iExact "Hin". }
            assert (({[d]} ∪ ds) ∖ {[d]} = ds) as -> by set_solver.
            rewrite env_set_dev_pe_dev (dev_res_set I (pe_dev E) ds d _ Hnot).
            iExact "Hdev". }
          { iIntros "Hfds Hfiles". iApply (cf_inv_same with "Hfds Hfiles Hdev"); done. }
          { iIntros (x) "%Hx Ht". iApply (cf_inv_taint I _ with "Ht"). by apply Htaint. }
        * (* absent *)
          iApply (ei_open_absent I (pe_fd E) (pe_files E) (pe_paths E) path mode
                    with "Hfds Hfiles"); [exact Hpath | exact Hnc | exact Hfile |].
          iSplit.
          { iIntros "Hfds Hfiles". iApply (cf_inv_same with "Hfds Hfiles Hdev"); done. }
          { iIntros (x) "%Hx Ht". iApply (cf_inv_taint I _ with "Ht"). by apply Htaint. }
      + (* EClose *)
        destruct Hc as (d & Hfd & Hlast & Hk). destruct Hs as [Hheld_fd Hs].
        assert (Hin : d ∈ ds) by (apply (Hdom fd); exact Hfd).
        assert (Hdom' : forall fd' d', pe_fd (env_unbind E fd) !! fd' = Some d' -> d' ∈ ds).
        { intros fd' d'. cbv [env_unbind pe_fd].
          destruct (decide (fd' = fd)) as [-> | Hne]; [by rewrite lookup_delete |].
          rewrite lookup_delete_ne; [| done]. apply Hdom. }
        assert (Hsafe' : safe_fds (dom (pe_fd (env_unbind E fd))) (k 0)).
        { cbv [env_unbind pe_fd]. rewrite dom_delete_L. apply Hs. }
        destruct (decide (fd_shared_p Dp (pe_fd E) fd d)) as [Hsh | Hsh].
        * (* a dup, or a protected device: the device stays *)
          iApply (ei_close_shared I (pe_fd E) fd d with "Hfds"); [exact Hfd | exact Hsh |].
          iSplit.
          { iIntros "Hfds".
            iApply (cf_inv_same I (env_unbind E fd) ds with "Hfds Hfiles Hdev"); done. }
          { iIntros (y) "Ht". iApply (cf_inv_taint I _ with "Ht"). apply Hs. }
        * (* the last descriptor of an unprotected device: the device goes *)
          assert (Hnp : d ∉ Dp /\ ~ fd_shared (pe_fd E) fd d).
          { split; intros H; apply Hsh; apply fd_shared_p_iff; [by left | by right]. }
          destruct Hnp as [Hnp Hsh'].
          iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]".
          iApply (ei_close I (pe_fd E) fd d (pe_dev E d) (pe_files E) (pe_paths E)
                    with "Hfds Hfiles Hdr");
            [exact Hfd | exact Hsh | exact (Hlast (fd_last_of_not_shared _ _ _ Hsh')) |].
          iSplit.
          { iIntros "Hfds Hfiles".
            iLeft. iExists (env_unbind E fd), (ds ∖ {[d]}).
            iSplit; [done |]. iSplit; [done |].
            iSplit.
            { iPureIntro. intros d' Hd'. apply elem_of_difference.
              split; [by apply Hdp |]. apply not_elem_of_singleton. intros ->. done. }
            iSplit.
            { iPureIntro. intros fd' d' Hfd'. pose proof (Hdom' fd' d' Hfd') as Hin'.
              cbv [env_unbind pe_fd] in Hfd'.
              destruct (decide (fd' = fd)) as [-> | Hne]; [by rewrite lookup_delete in Hfd' |].
              assert (d' <> d) as Hne'.
              { intros ->. apply Hsh'. exists fd'. split.
                - rewrite dom_delete_L. rewrite lookup_delete_ne in Hfd'; [| done].
                  apply elem_of_difference. split; [by apply elem_of_dom | set_solver].
                - rewrite lookup_delete_ne in Hfd'; [exact Hfd' | done]. }
              set_solver. }
            iFrame "Hfds Hfiles". iExact "Hrest". }
          { iIntros (y) "Ht". iApply (cf_inv_taint I _ with "Ht"). apply Hs. }
      + (* ERead *)
        destruct Hc as (d & Hfd & Hn & Hc). destruct Hs as [_ Hs].
        assert (Hin : d ∈ ds) by (apply (Hdom fd); exact Hfd).
        iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]".
        destruct Hc as [(Sin & Hd & Hk) | [(Sin & Hd & Hk & Hke) | [(Hd & Hk)
                       | [(Hfd0 & F & h & Rr & Sin & p & Hd & Hk & Hke) | [(Hfd0 & F & h & p & Hd & Hk)
                       | [(Hfd0 & Sin & Hd & Hk & Hke) | (Hfd0 & Hd & Hk)]]]]]]; rewrite Hd.
        * iApply (ei_read I (pe_fd E) fd d Sin n with "Hfds Hdr"); [exact Hn | exact Hfd |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros (c S') "%Hchunk Hfds Hin'".
          iApply (cf_inv_move I E ds d (DIn S') with "Hfds Hfiles Hin' Hrest");
            [exact Hin | by apply Hk | apply Hs | exact Hdp | exact Hdom].
        * iApply (ei_read_e I (pe_fd E) fd d Sin n with "Hfds Hdr"); [exact Hn | exact Hfd |].
          iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
          { iIntros (c S') "%Hchunk Hfds Hin'".
            iApply (cf_inv_move I E ds d (DInE S') with "Hfds Hfiles Hin' Hrest");
              [exact Hin | by apply Hk | apply Hs | exact Hdp | exact Hdom]. }
          { iIntros "Hfds Hend".
            iApply (cf_inv_move I E ds d DInEnd with "Hfds Hfiles Hend Hrest");
              [exact Hin | exact Hke | apply Hs | exact Hdp | exact Hdom]. }
        * iApply (ei_read_end I (pe_fd E) fd d n with "Hfds Hdr"); [exact Hn | exact Hfd |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hend".
          iApply (cf_inv_move I E ds d DInEnd with "Hfds Hfiles Hend Hrest");
            [exact Hin | by rewrite (env_set_dev_id E d _ Hd) | apply Hs | exact Hdp | exact Hdom].
        * (* the filter device: a chunk adds what it owes, or the writer closed *)
          iApply (ei_read_copy I (pe_fd E) fd d F h Rr Sin p n with "Hfds Hdr");
            [exact Hn | exact Hfd | exact Hfd0 |].
          iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
          { iIntros (c S') "%Hchunk %Hne Hfds Hc".
            iApply (cf_inv_move I E ds d (DCopy F h (Rr ++ c) S' (p ++ flt_new F Rr c))
                      with "Hfds Hfiles Hc Hrest");
              [exact Hin | by apply Hk | apply Hs | exact Hdp | exact Hdom]. }
          { iIntros "Hfds Hend".
            iApply (cf_inv_move I E ds d (DCopyEnd F h p) with "Hfds Hfiles Hend Hrest");
              [exact Hin | exact Hke | apply Hs | exact Hdp | exact Hdom]. }
        * iApply (ei_read_copy_end I (pe_fd E) fd d F h p n with "Hfds Hdr");
            [exact Hn | exact Hfd | exact Hfd0 |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hend".
          iApply (cf_inv_move I E ds d (DCopyEnd F h p) with "Hfds Hfiles Hend Hrest");
            [exact Hin | by rewrite (env_set_dev_id E d _ Hd) | apply Hs | exact Hdp | exact Hdom].
        * (* the halted filter device: the input goes on *)
          iApply (ei_read_copy_halt I (pe_fd E) fd d Sin n with "Hfds Hdr");
            [exact Hn | exact Hfd | exact Hfd0 |].
          iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
          { iIntros (c S') "%Hchunk %Hne Hfds Hc".
            iApply (cf_inv_move I E ds d (DCopyHalt (Some S')) with "Hfds Hfiles Hc Hrest");
              [exact Hin | by apply Hk | apply Hs | exact Hdp | exact Hdom]. }
          { iIntros "Hfds Hend".
            iApply (cf_inv_move I E ds d (DCopyHalt None) with "Hfds Hfiles Hend Hrest");
              [exact Hin | exact Hke | apply Hs | exact Hdp | exact Hdom]. }
        * iApply (ei_read_copy_halt_end I (pe_fd E) fd d n with "Hfds Hdr");
            [exact Hn | exact Hfd | exact Hfd0 |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hend".
          iApply (cf_inv_move I E ds d (DCopyHalt None) with "Hfds Hfiles Hend Hrest");
            [exact Hin | by rewrite (env_set_dev_id E d _ Hd) | apply Hs | exact Hdp | exact Hdom].
      + (* EWrite *)
        destruct Hc as (d & Hfd & Hc).
        assert (Hin : d ∈ ds) by (apply (Hdom fd); exact Hfd).
        iDestruct (dev_res_take I _ ds d Hin with "Hdev") as "[Hdr Hrest]".
        destruct Hc as [(-> & Hk0 & Hk1)
                       | [(Hne & alts & a & Hd & Ha & Hpre & Hk)
                       | [(Hne & alts & a & Hd & Ha & Hpre & Hk & Hkh)
                       | [(Hne & rest & Hd & Hk & Hkm)
                       | [(Hne & Hbnd & Hd & Hk)
                       | [(Hne & Hfd1 & F & h & Rr & Sin & p & Hd & Hpre & Hk & Hkh)
                       | [(Hne & Hfd1 & F & h & p & Hd & Hpre & Hk & Hkh)
                       | [(Hne & Hbnd & Hfd1 & oS & Hd & Hk)
                       | [(Hne & Hfd1 & outs & xs & dss & a & Hd & Ha & Hpre & Hk & Hkh)
                       | [(Hne & Hbnd & Hfd1 & dss & Hd & Hk)
                       | [(Hne & Hfd1 & outs & xs & dss & a & Hd & Ha & Hpre & Hk)
                       | [(Hne & Hfd1 & outs & xs & dss & a & Hd & Hon & Ha & Hpre & Hk)
                       | (Hne & Hfd1 & dss & a & Hd & Ha & Hpre & Hk)]]]]]]]]]]]].
        * iApply (ei_write_nil I (pe_fd E) fd d (pe_dev E d) with "Hfds Hdr"); [exact Hfd |].
          iSplit; [| iSplit; [| iIntros (y) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
          { iIntros "Hfds Hdr".
            iApply (cf_inv_move I E ds d (pe_dev E d) with "Hfds Hfiles Hdr Hrest");
              [exact Hin | by rewrite (env_set_dev_id E d _ eq_refl) | apply Hs | exact Hdp | exact Hdom]. }
          { iIntros "Hfds Hdr".
            iApply (cf_inv_move I E ds d (pe_dev E d) with "Hfds Hfiles Hdr Hrest");
              [exact Hin | by rewrite (env_set_dev_id E d _ eq_refl) | apply Hs | exact Hdp | exact Hdom]. }
        * rewrite Hd.
          iApply (ei_write I (pe_fd E) fd d alts a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Ha | exact Hpre |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hout".
          iApply (cf_inv_move I E ds d (DOut [drop (length bs) a]) with "Hfds Hfiles Hout Hrest");
            [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom].
        * rewrite Hd.
          iApply (ei_write_h I (pe_fd E) fd d alts a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Ha | exact Hpre |].
          iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
          { iIntros "Hfds Hout".
            iApply (cf_inv_move I E ds d (DOutH [drop (length bs) a]) with "Hfds Hfiles Hout Hrest");
              [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom]. }
          { iIntros "Hfds Hh".
            iApply (cf_inv_move I E ds d DHalt with "Hfds Hfiles Hh Hrest");
              [exact Hin | exact Hkh | apply Hs | exact Hdp | exact Hdom]. }
        * rewrite Hd.
          iApply (ei_write_m I (pe_fd E) fd d rest bs with "Hfds Hdr");
            [exact Hne | exact Hfd |].
          iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
          { iIntros "Hfds Hout".
            iApply (cf_inv_move I E ds d (DOutM rest) with "Hfds Hfiles Hout Hrest");
              [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom]. }
          { iIntros "Hfds Hout".
            iApply (cf_inv_move I E ds d (DOutM rest) with "Hfds Hfiles Hout Hrest");
              [exact Hin | exact Hkm | apply Hs | exact Hdp | exact Hdom]. }
        * rewrite Hd.
          iApply (ei_write_halt I (pe_fd E) fd d bs with "Hfds Hdr");
            [exact Hne | exact Hbnd | exact Hfd |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hh".
          iApply (cf_inv_move I E ds d DHalt with "Hfds Hfiles Hh Hrest");
            [exact Hin | by rewrite (env_set_dev_id E d _ Hd) | apply Hs | exact Hdp | exact Hdom].
        * (* the copy device: the count, and at a sink that may halt, -1 *)
          rewrite Hd. destruct h.
          { iApply (ei_write_copy_h I (pe_fd E) fd d F Rr Sin p bs with "Hfds Hdr");
              [exact Hne | exact Hfd | exact Hfd1 | exact Hpre |].
            iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
            { iIntros "Hfds Hc".
              iApply (cf_inv_move I E ds d (DCopy F true Rr Sin (drop (length bs) p)) with "Hfds Hfiles Hc Hrest");
                [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom]. }
            { iIntros "Hfds Hh".
              iApply (cf_inv_move I E ds d (DCopyHalt (Some Sin)) with "Hfds Hfiles Hh Hrest");
                [exact Hin | exact (Hkh eq_refl) | apply Hs | exact Hdp | exact Hdom]. } }
          { iApply (ei_write_copy I (pe_fd E) fd d F Rr Sin p bs with "Hfds Hdr");
              [exact Hne | exact Hfd | exact Hfd1 | exact Hpre |].
            iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
            iIntros "Hfds Hc".
            iApply (cf_inv_move I E ds d (DCopy F false Rr Sin (drop (length bs) p)) with "Hfds Hfiles Hc Hrest");
              [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom]. }
        * rewrite Hd. destruct h.
          { iApply (ei_write_copy_end_h I (pe_fd E) fd d F p bs with "Hfds Hdr");
              [exact Hne | exact Hfd | exact Hfd1 | exact Hpre |].
            iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
            { iIntros "Hfds Hc".
              iApply (cf_inv_move I E ds d (DCopyEnd F true (drop (length bs) p)) with "Hfds Hfiles Hc Hrest");
                [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom]. }
            { iIntros "Hfds Hh".
              iApply (cf_inv_move I E ds d (DCopyHalt None) with "Hfds Hfiles Hh Hrest");
                [exact Hin | exact (Hkh eq_refl) | apply Hs | exact Hdp | exact Hdom]. } }
          { iApply (ei_write_copy_end I (pe_fd E) fd d F p bs with "Hfds Hdr");
              [exact Hne | exact Hfd | exact Hfd1 | exact Hpre |].
            iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
            iIntros "Hfds Hc".
            iApply (cf_inv_move I E ds d (DCopyEnd F false (drop (length bs) p)) with "Hfds Hfiles Hc Hrest");
              [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom]. }
        * rewrite Hd.
          iApply (ei_write_copy_halt I (pe_fd E) fd d oS bs with "Hfds Hdr");
            [exact Hne | exact Hbnd | exact Hfd | exact Hfd1 |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hh".
          iApply (cf_inv_move I E ds d (DCopyHalt oS) with "Hfds Hfiles Hh Hrest");
            [exact Hin | by rewrite (env_set_dev_id E d _ Hd) | apply Hs | exact Hdp | exact Hdom].
        * (* the producer device: an output write *)
          rewrite Hd.
          iApply (ei_write_prod I (pe_fd E) fd d outs xs dss a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Hfd1 | exact Ha | exact Hpre |].
          iSplit; [| iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs]].
          { iIntros "Hfds Hp".
            iApply (cf_inv_move I E ds d (DProd [drop (length bs) a] [] dss) with "Hfds Hfiles Hp Hrest");
              [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom]. }
          { iIntros "Hfds Hh".
            iApply (cf_inv_move I E ds d (DProdHalt dss) with "Hfds Hfiles Hh Hrest");
              [exact Hin | exact Hkh | apply Hs | exact Hdp | exact Hdom]. }
        * rewrite Hd.
          iApply (ei_write_prod_halt I (pe_fd E) fd d dss bs with "Hfds Hdr");
            [exact Hne | exact Hbnd | exact Hfd | exact Hfd1 |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hh".
          iApply (cf_inv_move I E ds d (DProdHalt dss) with "Hfds Hfiles Hh Hrest");
            [exact Hin | by rewrite (env_set_dev_id E d _ Hd) | apply Hs | exact Hdp | exact Hdom].
        * (* ...a diagnostic write *)
          rewrite Hd.
          iApply (ei_write_prod_err I (pe_fd E) fd d outs xs dss a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Hfd1 | exact Ha | exact Hpre |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hp".
          iApply (cf_inv_move I E ds d (DProd outs [] [drop (length bs) a]) with "Hfds Hfiles Hp Hrest");
            [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom].
        * (* ...a failure report *)
          rewrite Hd.
          iApply (ei_write_prod_fail I (pe_fd E) fd d outs xs dss a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Hfd1 | exact Hon | exact Ha | exact Hpre |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hp".
          iApply (cf_inv_move I E ds d (DProd [[]] [] [drop (length bs) a]) with "Hfds Hfiles Hp Hrest");
            [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom].
        * rewrite Hd.
          iApply (ei_write_prod_halt_err I (pe_fd E) fd d dss a bs with "Hfds Hdr");
            [exact Hne | exact Hfd | exact Hfd1 | exact Ha | exact Hpre |].
          iSplit; [| iIntros (x) "Ht"; iApply (cf_inv_taint I _ with "Ht"); apply Hs].
          iIntros "Hfds Hp".
          iApply (cf_inv_move I E ds d (DProdHalt [drop (length bs) a]) with "Hfds Hfiles Hp Hrest");
            [exact Hin | exact Hk | apply Hs | exact Hdp | exact Hdom].
      + (* EExit *)
        iApply (ei_exit I s (pe_fd E) (pe_files E) (pe_paths E) (pe_dev E) ds
                  with "Hfds Hfiles Hdev"); [| by apply dom_ok_p_iff].
        intros d _. exact (Hc d).
  Qed.

  (* the glue at the protected devices: every one of them is among the
     devices the environment holds *)
  Theorem tree_pay_of_conforms_p (I : ep_ifaceP) (E : penv) (ds : gset nat) (t : proc) :
    conforms E t -> safe_fds (dom (pe_fd E)) t -> dp_in Dp ds ->
    env_res I E ds -∗ tree_pay N P t.
  Proof using .
    intros Hc Hs Hdp. iIntros "Hres".
    iApply (tree_pay_coind N P (cf_inv I) with "[]").
    { iApply cf_inv_step. }
    iLeft. iExists E, ds. by iFrame.
  Qed.

End UkHandler.

(* THE RECORD AT NO PROTECTED DEVICE: the shape every landed instance and
   entry is stated at ([UkPipeIface], [UkTreeEntry]) *)
Notation ep_iface := (ep_ifaceP (Dp := [])).
Notation MkEI := (MkEIP (Dp := [])).

Section UkHandlerNil.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).
  Context (P : uprog Σ).

  Theorem tree_pay_of_conforms (I : ep_iface N P) (E : penv) (ds : gset nat) (t : proc) :
    conforms E t -> safe_fds (dom (pe_fd E)) t ->
    env_res N P I E ds -∗ tree_pay N P t.
  Proof using .
    intros Hc Hs. iApply (tree_pay_of_conforms_p N P I E ds t Hc Hs).
    intros d Hd. by apply elem_of_nil in Hd.
  Qed.
End UkHandlerNil.
