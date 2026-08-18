(* WpSconfEngine.v -- the S-MODE gpr-write ENGINES at the per-node layer,
   for the leaves whose written value is a FUNCTION OF THE SOURCE READS.

   WHY THIS FILE EXISTS.  [WpSmodeIntr.wp_gpr_write_s_sconf{,_base}]'s
   instruction obligation is HART-GENERIC -- it is [∀ CID, gen_cert -∗
   gpr_file (tp_pin m) -∗ swp (execute base) (... <[rd := wval]> (tp_pin m))]
   with [wval] fixed by the CALLER, at the caller's hart.  That is exactly
   right for a leaf whose value reads no caller-chosen register ([c.li],
   [lui]), and it is UNPROVABLE for one that does: the walk answers the read
   at the hart the σ-callback was instantiated at, while [wval] names the
   value at the entry hart, and the two differ at tp.  A leaf holding only
   [ops_ok b rd rsa rsb] cannot close that gap by itself -- [src_ok] is
   guarded on [b = true], and the guard that saves the [b = false] case is
   [WpNext.wp_next]'s, which the obligation does not carry.  (This is the
   "guarded route" IntrDefs' [SrcOk] note points at: a leaf whose caller has
   only [ops_ok] at a variable [b] belongs here and not on the class.)

   THE SHAPE THAT DISSOLVES IT.  Do not hand the obligation a value; hand it
   the FUNCTION.  The engines below take [f : mword 64 -> mword 64 -> mword 64]
   and a caller premise [f (rget m rsa) (rget m rsb) = wval], and their
   obligation is

     ∀ CID, gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base) (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
         gpr_file (<[Regidx rd := regval_into_reg
                       (f (tp_pin m !!! Regidx rsa)
                          (tp_pin m !!! Regidx rsb))]> (tp_pin m)))

   -- which mentions no hart-specific value at all and is, verbatim, what
   [WpMmodeSwpBase]'s node shapes ([swp_execute_rrw] / [_rw] / [_rw2] /
   [_rrw2] / [_pure_w]) conclude.  A converted leaf is therefore ONE [iApply]
   with no [swp_mono] and no rewriting.  The reconciliation between the two
   harts happens ONCE, here, out of [ops_ok] and the [wp_next] guard, by
   [IntrDefs.rget_next_ops_indep].

   A leaf reading NO caller-chosen register may still use these ([f] ignores
   its arguments) or stay on [WpSmodeIntr]'s value-shaped engines; both are
   proved from the same funnel.

   ADDITIVE: nothing here changes an existing statement.  The three engines
   that live in WpSconfAlu.v ([wp_gpr_write_s_sconf_base_pc], the two cap
   engines) are converted in place beside their leaves. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import HartSwp HartMFrame WpMmodeSwpBase.
Require Import IntrDefs WpSmodeIntr.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section WpSconfEngine.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  Context {p : mword 64}.

  (* [IntrDefs.tp_pin_sp] with the [rget] FOLDED, so a leaf reading sp can
     [rewrite] it: the engines' value premise is spelled [rget m rsa], and a
     leaf whose source is the concrete sp states its value at the plain map
     lookup.  The two are convertible; [rewrite] is syntactic. *)
  Lemma rget_sp (m : regfile) : rget m csp_rs1 = m !!! Regidx csp_rs1.
  Proof. exact (tp_pin_sp m). Qed.

  (* =================================================================== *)
  (* THE MASTER.  Encoding width [c] is a parameter; the capability moves  *)
  (* by a caller-supplied TRANSFORMER (so an sp-write is the same engine); *)
  (* and the PC cell the funnel lends is passed straight through to the    *)
  (* obligation (so AUIPC is the same engine too).  [ops_ok_sp] rather     *)
  (* than [ops_ok] -- rd MAY be sp here; the tp half and the whole read    *)
  (* side are identical.  Everything else in this file is an instance.     *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf_gen
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (* THE INSTRUCTION'S OWN OBLIGATION, hart-generic and value-free: the walk
       reads whatever this hart's pin holds and writes [f] of it.  This is
       exactly what [WpMmodeSwpBase]'s node shapes conclude. *)
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗ (R_bitvector_64 PC) ↦ᵣ pc -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)) ∗
            (R_bitvector_64 PC) ↦ᵣ pc)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hrecap Hcont".
    pose proof (ops_ok_sp_rd _ _ _ _ Hops) as Hrdtp.
    iApply (wp_instr_s_sconf m n b pc c base
              (fun npc m2 n2 => ⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                                ⌜m2 = <[Regidx rd := regval_into_reg wval]> m⌝ ∗
                                ⌜n2 = n'⌝ ∗ P)%I
              with "Hcg Hpc Hinstr [Hex Hrecap Hcont]").
    iNext.
    (* FREE THE NAME [CID] FOR THE REBOUND HART -- the statement never sees
       the rename, so callers naming this engine's hart keep working. *)
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "Hex Hrecap".
    - (* the instruction *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      (* THE ONE RECONCILIATION, and the reason this engine exists: the walk
         answers the two source reads at the REBOUND hart, while [Hwval] names
         them at the entry hart.  At [b = true] [ops_ok] says neither source is
         tp; at [b = false] the guard [Hs] pins the hart outright. *)
      pose proof (rget_next_indep (CID := CID0) b p CID m rsa Hs
                    (ops_ok_sp_s1 _ _ _ _ Hops)) as Hra.
      pose proof (rget_next_indep (CID := CID0) b p CID m rsb Hs
                    (ops_ok_sp_s2 _ _ _ _ Hops)) as Hrb.
      assert (Hval : f (tp_pin (CID := CID) m !!! Regidx rsa)
                       (tp_pin (CID := CID) m !!! Regidx rsb) = wval)
        by (unfold rget in Hra, Hrb; rewrite Hra Hrb; exact Hwval).
      iDestruct ("Hrecap" $! CID with "Hcap") as "[Hcap HP]".
      iDestruct ("Hex" $! CID with "Hcert Hfile HPC") as "Hexx".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap HnPC Hresv HP] [Hexx]");
        [| iExact "Hexx" ].
      iIntros (e) "(-> & Hfile & HPC)".
      iSplitR; [done|].
      iExists (add_vec_int pc (if c then 2 else 4)),
              (<[Regidx rd := regval_into_reg wval]> m), n'.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hsc". { iFrame "Hhw Hminv Hsc". }
      iSplitL "Hcap"; [ iExact "Hcap" |].
      iSplitL "Hfile".
      { iEval (rewrite Hval) in "Hfile".
        iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp))
          in "Hfile". iExact "Hfile". }
      iFrame "HP". done.
    - (* the continuation: the engine resumes on the hart [Hs] names *)
      iIntros (npc m2 n2) "Hcg' Hpc' (-> & -> & -> & HP)".
      iApply ("Hcont" $! CID with "[%] Hcg' HP Hpc'"). exact Hs.
  Qed.

  (* THE PC-FREE OBLIGATION, the shape 99 % of the leaves want: the cell is
     framed across the walk here instead of at every call site. *)
  Lemma wp_gpr_write_s_sconf_cap_val_w
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hrecap Hcont".
    iApply (wp_gpr_write_s_sconf_gen pc c rd rsa rsb base f wval m n n' P b
              Hrd Hops Hwval with "[Hex] Hcg Hpc Hinstr Hrecap Hcont").
    iIntros (CIDn) "Hcert Hf HPC".
    iApply (swp_mono (CID := CIDn) with "[HPC] [-]");
      [| iApply ("Hex" $! CIDn with "Hcert Hf") ].
    iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC".
  Qed.

  (* =================================================================== *)
  (* The ordinary (non-sp) engine: the capability is merely RETARGETED    *)
  (* across the write, which is what [rd_ok]'s sp conjunct buys.          *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf_val_w
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp _ (ops_ok_rd _ _ _ _ Hops)) as Hrdsp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_gpr_write_s_sconf_cap_val_w pc c rd rsa rsb base f wval m n n
              emp%I b Hrd (ops_ok_to_sp _ _ _ _ Hops) Hwval
              with "Hex Hcg Hpc Hinstr [] [Hcont]").
    - iIntros (CIDx) "Hcap". iSplitL; [| done].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap").
    - iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* the two width instances every leaf actually names *)
  Lemma wp_gpr_write_s_sconf_val
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_gpr_write_s_sconf_val_w pc true rd rsa rsb base f wval m n b). Qed.

  Lemma wp_gpr_write_s_sconf_val_base
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_gpr_write_s_sconf_val_w pc false rd rsa rsb base f wval m n b). Qed.

  (* the COMPRESSED cap engine -- the shape every sp-mover is built over *)
  Lemma wp_gpr_write_s_sconf_cap_val
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_gpr_write_s_sconf_cap_val_w pc true rd rsa rsb base f wval m n n' P b).
  Qed.

  (* THE PC-READING ENGINE (auipc): the funnel's own PC cell, lent to the
     obligation and taken back.  [f] ignores its arguments at every current
     call site -- the value is a function of [pc] -- but it is kept for
     uniformity with the rest of the family. *)
  Lemma wp_gpr_write_s_sconf_pc_val_base
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗ (R_bitvector_64 PC) ↦ᵣ pc -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)) ∗
            (R_bitvector_64 PC) ↦ᵣ pc)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp _ (ops_ok_rd _ _ _ _ Hops)) as Hrdsp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_gpr_write_s_sconf_gen pc false rd rsa rsb base f wval m n n
              emp%I b Hrd (ops_ok_to_sp _ _ _ _ Hops) Hwval
              with "Hex Hcg Hpc Hinstr [] [Hcont]").
    - iIntros (CIDx) "Hcap". iSplitL; [| done].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap").
    - iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

End WpSconfEngine.
