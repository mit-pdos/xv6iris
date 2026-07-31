(* WpSconfVc.v -- the SIE-AGNOSTIC VCgen block executor over
   [sconf]+[sie_cap], WITH sp-move support.

   The executor state [vsstate] extends VcGenS.v's [vstate] with the
   CONCRETE stack-depth accounting [vsu]/[vsx] (current / high-water
   pushed depth below the entry sp -- concrete so a block run
   [vm_compute]s even under a symbolic [sie_cap] count) and a FRAME
   LEDGER [vsf]: the addresses (svals) of stack slots freed by an sp
   push that no store has initialized yet.  Their contents are junk,
   so they cannot live in the vheap (whose cells denote through ρ); at
   the WP level the ledger denotes as [vframe_own] -- one
   existentially-valued [word_pointsto] per address.

   sp moves (c.addi16sp, and c.addi with rd = sp; byte offsets must be
   multiples of 8):
     - PUSH (sp -= 8k): the k freed slot addresses [sp', sp) enter the
       ledger; vsu += k (and vsx tracks the max).
     - POP (sp += 8k): requires k <= vsu (a block never pops above its
       entry sp); each slot address in [sp, sp+8k) is reclaimed from
       the ledger (still junk) or DELETED from the 8-byte vheap (an
       initialized frame slot); vsu -= k.
   8-byte STOREs whose address misses the vheap but hits the ledger
   initialize that slot: the address moves from ledger to a fresh vheap
   cell holding the stored value.  LOADs never read the ledger (junk).
   Everything else delegates to [vc_step_s] (rd = sp writes outside the
   two sp-movers are rejected).

   The WP lemma [wp_vc_block_s_sconf] takes a symbolic entry count [n],
   threads [sie_cap γ m (n - vsu st)] and [vframe_own ρ
   (vsf st)] through the block, and needs the ONE pure premise
   [vsx st' <= n] (every intermediate push fits since [vsx] is
   monotone); sp moves go through the push/pop leaves (WpSconfAlu.v),
   everything else through the same [sconf] leaves as before.          *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import RegFile HartTp WpNext.
Require Import VcGen VcGenS.
Require Import StackOwn.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem.
Local Open Scope Z_scope.
Import Defs.

Local Lemma neq_of_eq_vec_false (a b : mword 5) :
  eq_vec a b = false -> a <> b.
Proof.
  intros Hf He. subst.
  rewrite (proj2 (eq_vec_true_iff b b) eq_refl) in Hf. discriminate.
Qed.

(* ====================================================================== *)
(* 1. The sp-aware executor state and pure helpers.                        *)
(* ====================================================================== *)

(* The stack accounting is kept CONCRETE so a block run [vm_compute]s
   even though the surrounding [sie_cap] count is symbolic: [vsu] is the
   CURRENT pushed depth (slots below the entry sp; 0 at block entry) and
   [vsx] its high-water mark.  The WP lemma takes a symbolic entry count
   [n], threads [sie_cap _ _ _ (n - vsu st)], and needs only the single
   pure premise [vsx st' <= n] -- every intermediate push fits because
   [vsx] is monotone ([vc_block_sp_ux]).  Pops must not go above the
   entry sp (guard [k <= vsu]). *)
Record vsstate := VSS {
  vsb : vstate;        (* pc / regs / heaps, shared with VcGenS *)
  vsu : nat;           (* current pushed depth below the entry sp *)
  vsx : nat;           (* high-water mark of [vsu] *)
  vsf : list sval;     (* ledger: pushed-but-uninitialized slot addresses *)
}.

(* remove the (syntactically) matching address from the ledger *)
Fixpoint frame_remove (fr : list sval) (a : sval) : option (list sval) :=
  match fr with
  | nil => None
  | a' :: t => if sval_beq a' a then Some t
               else match frame_remove t a with
                    | Some t' => Some (a' :: t')
                    | None => None
                    end
  end.

(* POP absorption: reclaim slot [v + 8j] for each j, from the ledger or
   (deleting the cell) from the 8-byte heap. *)
Fixpoint pop_absorb (h : list (sval * sval)) (fr : list sval) (v : sval)
    (js : list nat) : option (list (sval * sval) * list sval) :=
  match js with
  | nil => Some (h, fr)
  | j :: rest =>
      let a := sval_addZ v (8 * Z.of_nat j) in
      match frame_remove fr a with
      | Some fr' => pop_absorb h fr' v rest
      | None =>
          match vheap_find h a with
          | Some (i, _) => pop_absorb (delete i h) fr v rest
          | None => None
          end
      end
  end.

(* zimm12 residues are unsigned 64-bit values: those at or above 2^63
   denote NEGATIVE (downward) sp moves. *)
Definition vsp_half : Z := 9223372036854775808.
Definition vsp_wrap : Z := 18446744073709551616.

Definition lift_base (st : vsstate) (r : option vstate) : option vsstate :=
  match r with
  | Some b' => Some (VSS b' (vsu st) (vsx st) (vsf st))
  | None => None
  end.

Definition vc_step_sp_move (st : vsstate) (pc' : Z) (d : Z) : option vsstate :=
  match (vsb st).(vregs) !! Regidx csp_rs1 with
  | Some v =>
      if negb (sval_is64 v) then None else
      if negb (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)) then None else
      if Z.eqb d 0 then None else
      let v' := sval_addZ v d in
      let vr' := <[Regidx csp_rs1 := v']> (vsb st).(vregs) in
      if Z.ltb d vsp_half then
        (* upward move (sp += d): POP d/8 slots (not above the entry sp) *)
        if negb (Z.eqb (Z.modulo d 8) 0) then None else
        let k := Z.to_nat (Z.div d 8) in
        if negb (Nat.leb k (vsu st)) then None else
        match pop_absorb (vsb st).(vheap) (vsf st) v (seq 0 k) with
        | Some (h', fr') =>
            Some (VSS (VSt pc' vr' h' (vsb st).(vheap4))
                      (vsu st - k)%nat (vsx st) fr')
        | None => None
        end
      else
        (* downward move (sp -= 2^64 - d): PUSH (2^64 - d)/8 slots *)
        if negb (Z.eqb (Z.modulo (vsp_wrap - d) 8) 0) then None else
        let k := Z.to_nat (Z.div (vsp_wrap - d) 8) in
        Some (VSS (VSt pc' vr' (vsb st).(vheap) (vsb st).(vheap4))
                  (vsu st + k)%nat (Nat.max (vsx st) (vsu st + k))
                  (((fun j => sval_addZ v' (8 * Z.of_nat j)) <$> seq 0 k)
                   ++ vsf st))
  | None => None
  end.

(* 8-byte store: overwrite an existing cell, or initialize a ledger slot
   (the address moves from the ledger to a fresh cell). *)
Definition vc_store8_sp (st : vsstate) (pc' : Z) (a : sval) (v2 : sval)
    : option vsstate :=
  match vheap_find (vsb st).(vheap) a with
  | Some (i, _) =>
      Some (VSS (VSt pc' (vsb st).(vregs)
                     (<[i := (a, v2)]> (vsb st).(vheap)) (vsb st).(vheap4))
                (vsu st) (vsx st) (vsf st))
  | None =>
      match frame_remove (vsf st) a with
      | Some fr' =>
          Some (VSS (VSt pc' (vsb st).(vregs)
                         ((vsb st).(vheap) ++ [(a, v2)]) (vsb st).(vheap4))
                    (vsu st) (vsx st) fr')
      | None => None
      end
  end.

(* [rd_tp_bad rd]: the executor's OWN gate against a generic write's two
   forbidden destinations, sp AND tp -- exactly [IntrDefs.rd_ok]'s two
   conjuncts negated, decided as a bool since every use here sits inside a
   plain (non-Iris) match.  [VcGenS.vc_step_s] only ever excluded
   [uint rd = 0]; tp becomes a second forbidden destination now that the
   register file PINS it (HartTp.v), so a leaf write to it would falsify
   the pin -- the guard has to reject that case here, at the executor,
   since [rd] is a symbolic block-local register with no other place to
   rule it out. *)
Definition rd_tp_bad (rd : mword 5) : bool :=
  orb (eq_vec rd csp_rs1) (eq_vec rd (mword_of_int 4 : mword 5)).

Local Lemma rd_tp_bad_false (rd : mword 5) : rd_tp_bad rd = false -> rd_ok rd.
Proof.
  unfold rd_tp_bad, rd_ok. intro H. apply orb_false_iff in H. destruct H as [H1 H2].
  pose proof (neq_of_eq_vec_false _ _ H1) as Hsp.
  pose proof (neq_of_eq_vec_false _ _ H2) as Htp.
  split; [exact Hsp | intro Heq; injection Heq as Heq2; exact (Htp Heq2)].
Qed.

(* [is_tp r]: the executor's gate against a generic READ source being tp.
   [gpr_matches] relates the block's symbolic register map to the PLAIN
   register file [m], not to [rget m _] -- so at [r = tp] the two can
   disagree (the plain slot is whatever the caller's [m] happens to carry,
   while the hardware always reads the pin). VcGenS.vc_step_s never guarded
   against this because tp did not exist as a distinguished slot before the
   pin; the guard has to reject it here for every opcode that reads a
   variable (non-sp) register, since [rd]/[rs1]/[rs2] are symbolic
   block-local registers with no other place to rule this out. *)
Definition is_tp (r : mword 5) : bool := eq_vec r (mword_of_int 4 : mword 5).

Local Lemma is_tp_false (r : mword 5) : is_tp r = false -> Regidx r <> Regidx Rtp.
Proof.
  unfold is_tp. intro H. pose proof (neq_of_eq_vec_false _ _ H) as Hne.
  intro Heq. injection Heq as Heq2. exact (Hne Heq2).
Qed.

Definition vc_step_sp_s (st : vsstate) (op : vop_s) : option vsstate :=
  let pc' := (vsb st).(vpc) + vop_s_w op in
  match op with
  | VScaddi imm rd =>
      if eq_vec rd csp_rs1
      then vc_step_sp_move st pc' (zimm12 (sign_extend' 12 imm))
      else if rd_tp_bad rd then None
      else lift_base st (vc_step_s (vsb st) op)
  | VScaddi16sp imm6 =>
      vc_step_sp_move st pc' (zimm12 (caddi16sp_imm imm6))
  | VScaddi4spn _ _ rd | VScldsp _ rd | VScaddiw _ rd =>
      if rd_tp_bad rd then None else lift_base st (vc_step_s (vsb st) op)
  | VSclw _ rs1 rd =>
      if orb (rd_tp_bad rd) (is_tp rs1) then None
      else lift_base st (vc_step_s (vsb st) op)
  | VSld _ _ rs1 rd =>
      if orb (rd_tp_bad rd) (is_tp rs1) then None
      else lift_base st (vc_step_s (vsb st) op)
  | VScsdsp uimm rs2 =>
      if is_tp rs2 then None else
      match (vsb st).(vregs) !! Regidx csp_rs1, (vsb st).(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          if negb (sval_is64 v1) then None
          else vc_store8_sp st pc' (sval_addZ v1 (zoff6 uimm)) v2
      | _, _ => None
      end
  | VSsd _ imm rs2 rs1 =>
      if orb (is_tp rs1) (is_tp rs2) then None else
      match (vsb st).(vregs) !! Regidx rs1, (vsb st).(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          if negb (sval_is64 v1) then None
          else vc_store8_sp st pc' (sval_addZ v1 (zimm12 imm)) v2
      | _, _ => None
      end
  | VScsw imm rs2 rs1 =>
      if orb (is_tp rs1) (is_tp rs2) then None
      else lift_base st (vc_step_s (vsb st) op)
  end.

Fixpoint vc_block_sp_s (st : vsstate) (prog : list vop_s) : option vsstate :=
  match prog with
  | nil => Some st
  | op :: rest =>
      match vc_step_sp_s st op with
      | Some st1 => vc_block_sp_s st1 rest
      | None => None
      end
  end.

(* ---- the depth accounting is well-formed and monotone ---- *)
Lemma vc_step_sp_move_ux (st : vsstate) (pc' d : Z) (st1 : vsstate) :
  vc_step_sp_move st pc' d = Some st1 ->
  (vsu st <= vsx st)%nat ->
  (vsu st1 <= vsx st1)%nat /\ (vsx st <= vsx st1)%nat.
Proof.
  unfold vc_step_sp_move.
  destruct (vregs (vsb st) !! Regidx csp_rs1) as [v|]; [|discriminate].
  destruct (sval_is64 v); [|discriminate].
  destruct (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)); [|discriminate].
  destruct (Z.eqb d 0); [discriminate|].
  cbn [negb].
  destruct (Z.ltb d vsp_half).
  - destruct (Z.eqb (d mod 8) 0); [|discriminate]. cbn [negb].
    destruct (Nat.leb (Z.to_nat (d / 8)) (vsu st)); [|discriminate]. cbn [negb].
    destruct (pop_absorb _ _ _ _) as [[h' fr']|]; [|discriminate].
    intros H Hux. injection H as <-. cbn [vsu vsx]. lia.
  - destruct (Z.eqb ((vsp_wrap - d) mod 8) 0); [|discriminate]. cbn [negb].
    intros H Hux. injection H as <-. cbn [vsu vsx]. lia.
Qed.

Lemma lift_base_ux (st : vsstate) (r : option vstate) (st1 : vsstate) :
  lift_base st r = Some st1 -> vsu st1 = vsu st /\ vsx st1 = vsx st.
Proof.
  destruct r as [b'|]; intro H; [injection H as <-; auto | discriminate].
Qed.

Lemma sp_move_inv (st : vsstate) (pc' d : Z) (st1 : vsstate) :
  vc_step_sp_move st pc' d = Some st1 ->
  exists v, (vsb st).(vregs) !! Regidx csp_rs1 = Some v /\ sval_is64 v = true /\
    (0 <= d) /\ (d < vsp_wrap) /\ d <> 0 /\
    (( d < vsp_half /\ d mod 8 = 0 /\ (Z.to_nat (d / 8) <= vsu st)%nat /\
       exists h' fr',
         pop_absorb (vsb st).(vheap) (vsf st) v (seq 0 (Z.to_nat (d / 8)))
           = Some (h', fr') /\
         st1 = VSS (VSt pc' (<[Regidx csp_rs1 := sval_addZ v d]> (vsb st).(vregs))
                            h' (vsb st).(vheap4))
                   (vsu st - Z.to_nat (d / 8))%nat (vsx st) fr' )
     \/
     ( vsp_half <= d /\ (vsp_wrap - d) mod 8 = 0 /\
         st1 = VSS (VSt pc' (<[Regidx csp_rs1 := sval_addZ v d]> (vsb st).(vregs))
                            (vsb st).(vheap) (vsb st).(vheap4))
                   (vsu st + Z.to_nat ((vsp_wrap - d) / 8))%nat
                   (Nat.max (vsx st) (vsu st + Z.to_nat ((vsp_wrap - d) / 8)))
                   (((fun j => sval_addZ (sval_addZ v d) (8 * Z.of_nat j))
                       <$> seq 0 (Z.to_nat ((vsp_wrap - d) / 8))) ++ vsf st) )).
Proof.
  unfold vc_step_sp_move.
  destruct ((vsb st).(vregs) !! Regidx csp_rs1) as [v|] eqn:Hrs1; [|discriminate].
  destruct (sval_is64 v) eqn:H64; cbn [negb]; [|discriminate].
  destruct (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)) eqn:Hrange; cbn [negb]; [|discriminate].
  apply andb_prop in Hrange; destruct Hrange as [Hd0 HdW].
  apply Z.leb_le in Hd0. apply Z.ltb_lt in HdW.
  destruct (Z.eqb d 0) eqn:Hdz; [discriminate|]. apply Z.eqb_neq in Hdz.
  destruct (Z.ltb d vsp_half) eqn:Hdir.
  - apply Z.ltb_lt in Hdir.
    destruct (Z.eqb (d mod 8) 0) eqn:Hmod; cbn [negb]; [|discriminate].
    apply Z.eqb_eq in Hmod.
    destruct (Nat.leb (Z.to_nat (d / 8)) (vsu st)) eqn:Hk; cbn [negb]; [|discriminate].
    apply Nat.leb_le in Hk.
    destruct (pop_absorb (vsb st).(vheap) (vsf st) v (seq 0 (Z.to_nat (d / 8))))
      as [[h' fr']|] eqn:Habs; [|discriminate].
    intro HS; injection HS as <-. exists v.
    split;[reflexivity|]. split;[exact H64|]. split;[exact Hd0|].
    split;[exact HdW|]. split;[exact Hdz|].
    left. split;[exact Hdir|]. split;[exact Hmod|]. split;[exact Hk|].
    exists h', fr'. split;[exact Habs|reflexivity].
  - apply Z.ltb_ge in Hdir.
    destruct (Z.eqb ((vsp_wrap - d) mod 8) 0) eqn:Hmod; cbn [negb]; [|discriminate].
    apply Z.eqb_eq in Hmod.
    intro HS; injection HS as <-. exists v.
    split;[reflexivity|]. split;[exact H64|]. split;[exact Hd0|].
    split;[exact HdW|]. split;[exact Hdz|].
    right. split;[exact Hdir|]. split;[exact Hmod|reflexivity].
Qed.

Lemma vc_store8_sp_ux (st : vsstate) (pc' : Z) (a v2 : sval) (st1 : vsstate) :
  vc_store8_sp st pc' a v2 = Some st1 -> vsu st1 = vsu st /\ vsx st1 = vsx st.
Proof.
  unfold vc_store8_sp.
  destruct (vheap_find _ _) as [[i ?]|].
  - intro H; injection H as <-; auto.
  - destruct (frame_remove _ _); intro H; [injection H as <-; auto | discriminate].
Qed.

Lemma vc_step_sp_ux (st : vsstate) (op : vop_s) (st1 : vsstate) :
  vc_step_sp_s st op = Some st1 ->
  (vsu st <= vsx st)%nat ->
  (vsu st1 <= vsx st1)%nat /\ (vsx st <= vsx st1)%nat.
Proof.
  intros H Hux.
  assert (Hlift : lift_base st (vc_step_s (vsb st) op) = Some st1 ->
            (vsu st1 <= vsx st1)%nat /\ (vsx st <= vsx st1)%nat).
  { intros Hr. destruct (lift_base_ux _ _ _ Hr) as [-> ->].
    split; [exact Hux | lia]. }
  destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd
                 |imm rs1 rd|imm rs2 rs1|imm rd
                 |rvc imm rs2 rs1|rvc imm rs1 rd|imm6];
    cbn [vc_step_sp_s] in H, Hlift.
  - destruct (eq_vec rd csp_rs1).
    + exact (vc_step_sp_move_ux _ _ _ _ H Hux).
    + destruct (rd_tp_bad rd); [discriminate|]. exact (Hlift H).
  - destruct (rd_tp_bad rd); [discriminate|]. exact (Hlift H).
  - destruct (is_tp rs2); [discriminate|].
    destruct (vregs (vsb st) !! Regidx csp_rs1) as [v1|]; [|discriminate].
    destruct (vregs (vsb st) !! Regidx rs2) as [v2|]; [|discriminate].
    destruct (negb (sval_is64 v1)); [discriminate|].
    destruct (vc_store8_sp_ux _ _ _ _ _ H) as [-> ->]. split; [exact Hux | lia].
  - destruct (rd_tp_bad rd); [discriminate|]. exact (Hlift H).
  - destruct (orb (rd_tp_bad rd) (is_tp rs1)); [discriminate|]. exact (Hlift H).
  - destruct (orb (is_tp rs1) (is_tp rs2)); [discriminate|]. exact (Hlift H).
  - destruct (rd_tp_bad rd); [discriminate|]. exact (Hlift H).
  - destruct (orb (is_tp rs1) (is_tp rs2)); [discriminate|].
    destruct (vregs (vsb st) !! Regidx rs1) as [v1|]; [|discriminate].
    destruct (vregs (vsb st) !! Regidx rs2) as [v2|]; [|discriminate].
    destruct (negb (sval_is64 v1)); [discriminate|].
    destruct (vc_store8_sp_ux _ _ _ _ _ H) as [-> ->]. split; [exact Hux | lia].
  - destruct (orb (rd_tp_bad rd) (is_tp rs1)); [discriminate|]. exact (Hlift H).
  - exact (vc_step_sp_move_ux _ _ _ _ H Hux).
Qed.

Lemma vc_block_sp_ux (prog : list vop_s) (st st' : vsstate) :
  vc_block_sp_s st prog = Some st' ->
  (vsu st <= vsx st)%nat ->
  (vsu st' <= vsx st')%nat /\ (vsx st <= vsx st')%nat.
Proof.
  revert st. induction prog as [|op rest IHp]; intros st H Hux; simpl in H.
  - injection H as <-. split; [exact Hux | lia].
  - destruct (vc_step_sp_s st op) as [st1|] eqn:Hs; [|discriminate].
    destruct (vc_step_sp_ux _ _ _ Hs Hux) as [H1 H2].
    destruct (IHp _ H H1) as [H3 H4]. split; [exact H3 | lia].
Qed.

(* ====================================================================== *)
(* 2. Pure arithmetic bridges: executor guards -> the push/pop leaves'     *)
(* address premises.                                                       *)
(* ====================================================================== *)

Lemma sval_addZ_is64 (v : sval) (d : Z) :
  sval_is64 v = true -> sval_is64 (sval_addZ v d) = true.
Proof. destruct v; simpl; auto. Qed.

Lemma sval_den_addZ_avi (ρ : nat -> mword 64) (v : sval) (d : Z) :
  sval_is64 v = true ->
  sval_den ρ (sval_addZ v d) = add_vec_int (sval_den ρ v) d.
Proof. intro H. rewrite (sval_den_addZ ρ v d H). reflexivity. Qed.

Lemma mword_of_int_mod64 (z1 z2 : Z) :
  (z1 - z2) mod vsp_wrap = 0 ->
  (mword_of_int z1 : mword 64) = mword_of_int z2.
Proof.
  intro H.
  rewrite -(stk_mword_of_int_wrap z1) -(stk_mword_of_int_wrap z2).
  f_equal.
  unfold bv_wrap.
  assert (Hm : bv_modulus 64 = vsp_wrap) by (vm_compute; reflexivity).
  rewrite Hm.
  unfold vsp_wrap in *.
  assert (He : z1 - z2 = 18446744073709551616 * ((z1 - z2) / 18446744073709551616))
    by (apply Z_div_exact_full_2; [lia | exact H]).
  replace z1
    with (z2 + (z1 - z2) / 18446744073709551616 * 18446744073709551616) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma push_addr_eq (sp0 imm64 : mword 64) (k : nat) :
  8 * Z.of_nat k = vsp_wrap - uint imm64 ->
  add_vec sp0 imm64 = pa_stk sp0 k.
Proof.
  intro He. unfold pa_stk, add_vec_int.
  rewrite -(stk_mword_of_int_uint imm64).
  apply f_equal.
  apply mword_of_int_mod64.
  unfold vsp_wrap in *.
  replace (uint imm64 - - (8 * Z.of_nat k)) with 18446744073709551616 by lia.
  apply Z_mod_same_full.
Qed.

Lemma pop_addr_eq (sp0 imm64 : mword 64) (k : nat) :
  8 * Z.of_nat k = uint imm64 ->
  sp0 = pa_stk (add_vec sp0 imm64) k.
Proof.
  intro He. unfold pa_stk.
  rewrite -(stk_mword_of_int_uint imm64).
  change (add_vec sp0 (mword_of_int (uint imm64)))
    with (add_vec_int sp0 (uint imm64)).
  rewrite avi_assoc.
  replace (uint imm64 + - (8 * Z.of_nat k)) with 0 by lia.
  symmetry. apply avi0.
Qed.

Lemma div8_exact (d : Z) :
  0 <= d -> d mod 8 = 0 -> 8 * Z.of_nat (Z.to_nat (d / 8)) = d.
Proof.
  intros Hd Hm.
  rewrite Z2Nat.id; [| apply Z.div_pos; lia].
  pose proof (Z_div_mod_eq_full d 8). lia.
Qed.

(* smoke test: the accounting is fully concrete, so a
   push -> store-into-fresh-frame -> load-back -> pop block runs by
   [vm_compute] even though nothing is known about the registers.
   (c.addi16sp sp,-16 ; c.sdsp ra,8(sp) ; c.ldsp ra,8(sp) ;
    c.addi16sp sp,16 -- net zero: heap, ledger and depth all return
    to the entry state; the high-water mark records the 2-slot frame.) *)

Section WpSconfVc.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ==================================================================== *)
  (* 3. The frame ledger's denotation + the resource algebra of the new    *)
  (* executor steps.                                                       *)
  (* ==================================================================== *)
  Definition vframe_own (ρ : nat -> mword 64) (fr : list sval) : iProp Σ :=
    ([∗ list] a ∈ fr, ∃ w : bv 64,
        word_pointsto (sval_den ρ a) (DfracOwn 1) w)%I.

  Lemma vframe_own_nil (ρ : nat -> mword 64) : ⊢ vframe_own ρ [].
  Proof. rewrite /vframe_own big_sepL_nil. done. Qed.

  Lemma vframe_own_app (ρ : nat -> mword 64) (f1 f2 : list sval) :
    vframe_own ρ (f1 ++ f2) ⊣⊢ vframe_own ρ f1 ∗ vframe_own ρ f2.
  Proof. by rewrite /vframe_own big_sepL_app. Qed.

  Lemma vframe_own_remove (ρ : nat -> mword 64) (fr : list sval) (a : sval)
      (fr' : list sval) :
    frame_remove fr a = Some fr' ->
    vframe_own ρ fr ⊣⊢
    (∃ w : bv 64, word_pointsto (sval_den ρ a) (DfracOwn 1) w) ∗ vframe_own ρ fr'.
  Proof.
    revert fr'. induction fr as [|a0 t IHt]; intros fr' H; simpl in H;
      [discriminate|].
    destruct (sval_beq a0 a) eqn:Hbeq.
    - injection H as <-. apply sval_beq_eq in Hbeq. subst a0.
      by rewrite /vframe_own big_sepL_cons.
    - destruct (frame_remove t a) as [t'|] eqn:Hrec; [|discriminate].
      injection H as <-.
      rewrite /vframe_own !big_sepL_cons.
      rewrite /vframe_own in IHt. rewrite (IHt t' eq_refl).
      iSplit.
      + iIntros "(H0 & Ha & Ht)". iFrame.
      + iIntros "(Ha & H0 & Ht)". iFrame.
  Qed.

  Lemma vheap_own_delete (ρ : nat -> mword 64) (h : list (sval * sval))
      (i : nat) (a v : sval) :
    h !! i = Some (a, v) ->
    vheap_own ρ h ⊣⊢
    ((sval_den ρ a) ↦₈ (sval_den ρ v) ∗ vheap_own ρ (delete i h))%I.
  Proof.
    intro Hi.
    rewrite /vheap_own.
    rewrite -{1}(take_drop_middle h i (a, v) Hi).
    rewrite delete_take_drop.
    rewrite !big_sepL_app big_sepL_cons /=.
    iSplit.
    - iIntros "(Ht & Hc & Hd)". iFrame.
    - iIntros "(Hc & Ht & Hd)". iFrame.
  Qed.

  Lemma vheap_own_snoc (ρ : nat -> mword 64) (h : list (sval * sval))
      (a v : sval) :
    vheap_own ρ (h ++ [(a, v)]) ⊣⊢
    vheap_own ρ h ∗ ((sval_den ρ a) ↦₈ (sval_den ρ v))%I.
  Proof. by rewrite /vheap_own big_sepL_app big_sepL_singleton. Qed.

  (* absorbing a pop's slots: the reclaimed region as base-anchored
     existential words, ready for [stack_own] reassembly. *)
  Lemma pop_absorb_sound (ρ : nat -> mword 64) (v : sval) (js : list nat)
      (h h' : list (sval * sval)) (fr fr' : list sval) :
    sval_is64 v = true ->
    pop_absorb h fr v js = Some (h', fr') ->
    vheap_own ρ h -∗ vframe_own ρ fr -∗
    vheap_own ρ h' ∗ vframe_own ρ fr' ∗
    ([∗ list] j ∈ js, ∃ w : bv 64,
       word_pointsto (add_vec_int (sval_den ρ v) (8 * Z.of_nat j)) (DfracOwn 1) w).
  Proof.
    intros Hv64. revert h fr.
    induction js as [|j rest IHjs]; intros h fr Habs; simpl in Habs.
    - injection Habs as <- <-.
      iIntros "Hh Hf". iFrame "Hh Hf". done.
    - destruct (frame_remove fr (sval_addZ v (8 * Z.of_nat j))) as [fr1|] eqn:Hfrm.
      + iIntros "Hh Hf".
        iEval (rewrite (vframe_own_remove ρ fr _ fr1 Hfrm)) in "Hf".
        iDestruct "Hf" as "[Hslot Hf]".
        iDestruct (IHjs _ _ Habs with "Hh Hf") as "(Hh & Hf & Hrest)".
        iFrame "Hh Hf".
        rewrite big_sepL_cons.
        iSplitL "Hslot"; [| iExact "Hrest"].
        iEval (rewrite (sval_den_addZ_avi ρ v _ Hv64)) in "Hslot".
        iExact "Hslot".
      + destruct (vheap_find h (sval_addZ v (8 * Z.of_nat j))) as [[i vold]|] eqn:Hfind;
          [|discriminate].
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hi.
        iIntros "Hh Hf".
        iEval (rewrite (vheap_own_delete ρ h i _ _ Hi)) in "Hh".
        iDestruct "Hh" as "[Hslot Hh]".
        iDestruct (IHjs _ _ Habs with "Hh Hf") as "(Hh & Hf & Hrest)".
        iFrame "Hh Hf".
        rewrite big_sepL_cons.
        iSplitL "Hslot"; [| iExact "Hrest"].
        iEval (rewrite (sval_den_addZ_avi ρ v _ Hv64)) in "Hslot".
        iExists (sval_den ρ vold). iExact "Hslot".
  Qed.

  (* a pushed frame region, as ledger entries *)
  Lemma vframe_own_of_stack (ρ : nat -> mword 64) (v' : sval) (sp0 : mword 64)
      (k : nat) :
    sval_is64 v' = true ->
    sval_den ρ v' = pa_stk sp0 k ->
    stack_own sp0 k ⊣⊢
    vframe_own ρ ((fun j => sval_addZ v' (8 * Z.of_nat j)) <$> seq 0 k).
  Proof.
    intros Hv64 Hbase.
    rewrite stack_own_base /vframe_own big_sepL_fmap.
    apply big_sepL_proper. intros i j _.
    rewrite (sval_den_addZ_avi ρ v' _ Hv64) Hbase. done.
  Qed.

  (* a pop's absorbed slots, reassembled below the NEW sp *)
  Lemma stack_of_absorbed (ρ : nat -> mword 64) (v : sval) (spN : mword 64)
      (k : nat) :
    sval_den ρ v = pa_stk spN k ->
    ([∗ list] j ∈ seq 0 k, ∃ w : bv 64,
       word_pointsto (add_vec_int (sval_den ρ v) (8 * Z.of_nat j)) (DfracOwn 1) w)
    ⊢ stack_own spN k.
  Proof. intro Hb. rewrite stack_own_base Hb. done. Qed.

  (* [wp_next_shift]: re-anchor a [wp_next] obligation from the hart it was
     stated at ([CID]) to a hart reached mid-block ([CID1]), given the
     conditional equality a leaf's own crossing produced.  This is what makes
     the [induction prog] proof below work: [IH], instantiated at the fresh
     hart a leaf's [wp_next] introduces, wants its OWN final continuation
     anchored there, while the caller's ["Hcont"] is still anchored at
     whatever hart THIS invocation started at.  Both are the SAME [K] (the
     block's final state [st']/[m0]/[n] never change across a step), so only
     the anchor needs to move -- exactly the composition [wp_next_trans]
     proves pointwise, here packaged as a proposition-level rewrite so it
     can be applied to a live "Hcont" resource with [iDestruct ... as]. *)
  Lemma wp_next_shift {K : CpuId -> iProp Σ} {b : bool} {CIDa CIDb : CpuId}
      (Hs : b = false -> (CIDb : CPU) = (CIDa : CPU)) :
    wp_next (CID0 := CIDa) b K -∗ wp_next (CID0 := CIDb) b K.
  Proof.
    iEval (rewrite /wp_next). iIntros "H" (CID2 Hs2).
    iEval (rewrite /wp_next) in "H". iApply "H". iPureIntro.
    intro Hb. specialize (Hs2 Hb). specialize (Hs Hb). congruence.
  Qed.

  (* ==================================================================== *)
  (* 4. THE block lemma: one symbolic run = one WP, sp moves included.     *)
  (* ==================================================================== *)
  Lemma wp_vc_block_s_sconf_aux
      (prog : list vop_s) (Φ : mval -> iProp Σ)
      (st st' : vsstate) (ρ : nat -> mword 64)
      (m m0 : regfile) (n : nat) (b : bool) :
    vc_block_sp_s st prog = Some st' ->
    (vsu st <= vsx st)%nat ->
    (vsx st' <= n)%nat ->
    gpr_matches ρ (vsb st).(vregs) m ->
    agree_off (vsb st).(vregs) m m0 ->
    sie_cap_gpr m (n - vsu st) b p -∗
    pc_is (mword_of_int (vsb st).(vpc)) -∗
    block_instrs_s (vsb st).(vpc) prog -∗
    vheap_own ρ (vsb st).(vheap) -∗
    vheap4_own ρ (vsb st).(vheap4) -∗
    vframe_own ρ (vsf st) -∗
    wp_next b (fun (CID : CpuId) =>
      (∀ mf : regfile,
      ⌜ gpr_matches ρ (vsb st').(vregs) mf ∧ agree_off (vsb st').(vregs) mf m0 ⌝ -∗
      sie_cap_gpr mf (n - vsu st') b p -∗
      pc_is (mword_of_int (vsb st').(vpc)) -∗
      vheap_own ρ (vsb st').(vheap) -∗
      vheap4_own ρ (vsb st').(vheap4) -∗
      vframe_own ρ (vsf st') -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    revert st m CID. induction prog as [|op rest IH]; intros st m CID Hblk Hux Hxn Hmatch Hao.
    - (* empty block *)
      simpl in Hblk. injection Hblk as <-.
      iIntros "Hcg Hpc _ Hheap Hheap4 Hfr Hcont".
      iSpecialize ("Hcont" $! CID with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! m with "[//] Hcg Hpc Hheap Hheap4 Hfr").
    - cbn [vc_block_sp_s] in Hblk.
      destruct (vc_step_sp_s st op) as [st1|] eqn:Hstep; [|discriminate].
      pose proof (vc_step_sp_ux _ _ _ Hstep Hux) as [Hux1 _].
      pose proof (proj2 (vc_block_sp_ux _ _ _ Hblk Hux1)) as Hxmono.
      destruct st as [vb u x fr].
      cbn [vsu vsx vsb vsf] in Hux |- *.
      iIntros "Hcg Hpc [Hi Hbi] Hheap Hheap4 Hfr Hcont".
      destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd
                     |imm rs1 rd|imm rs2 rs1|imm rd
                     |rvc imm rs2 rs1|rvc imm rs1 rd|imm6];
        cbn [vc_step_sp_s vsb vsu vsx vsf vop_s_w] in Hstep.
      + (* VScaddi : sp-move if rd = sp, else delegate *)
        destruct (eq_vec rd csp_rs1) eqn:Hrdsp0.
        * (* ---- c.addi sp, imm : an sp move ---- *)
          pose proof (proj1 (eq_vec_true_iff _ _) Hrdsp0) as Hrdeq. subst rd.
          unfold vc_step_sp_move in Hstep; cbn [vsb vsu vsx vsf] in Hstep.
          destruct (vregs vb !! Regidx csp_rs1) as [v|] eqn:Hrs1; [|discriminate].
          destruct (sval_is64 v) eqn:H64; cbn [negb] in Hstep; [|discriminate].
          set (d := zimm12 (sign_extend' 12 imm)) in *.
          destruct (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)) eqn:Hrange;
            cbn [negb] in Hstep; [|discriminate].
          apply andb_prop in Hrange; destruct Hrange as [Hd0 HdW].
          apply Z.leb_le in Hd0. apply Z.ltb_lt in HdW.
          destruct (Z.eqb d 0) eqn:Hdz; [discriminate|].
          pose proof (Hmatch _ _ Hrs1) as Hm1.
          assert (Hval : regval_into_reg
                      (add_vec (m !!! Regidx csp_rs1)
                               (sign_extend' 64 (sign_extend' 12 imm)))
                  = sval_den ρ (sval_addZ v d)).
          { unfold regval_into_reg.
            rewrite (sval_den_addZ ρ v d H64) Hm1.
            unfold d, zimm12. rewrite stk_mword_of_int_uint. reflexivity. }
          destruct (Z.ltb d vsp_half) eqn:Hdir.
          { (* POP: sp += d *)
            destruct (Z.eqb (d mod 8) 0) eqn:Hmod; cbn [negb] in Hstep;
              [|discriminate].
            apply Z.eqb_eq in Hmod.
            set (k := Z.to_nat (d / 8)) in *.
            destruct (Nat.leb k u) eqn:Hku0; cbn [negb] in Hstep; [|discriminate].
            apply Nat.leb_le in Hku0.
            destruct (pop_absorb (vheap vb) fr v (seq 0 k)) as [[h' fr']|] eqn:Habs;
              [|discriminate].
            injection Hstep as <-.
            cbn [vsu vsx] in Hux1, Hxmono.
            assert (Hek : 8 * Z.of_nat k = d)
              by (unfold k; apply div8_exact; [lia | exact Hmod]).
            assert (Hw : m !!! Regidx csp_rs1
                         = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                     (sign_extend' 64 (sign_extend' 12 imm))) k).
            { apply pop_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
            iDestruct (pop_absorb_sound ρ v (seq 0 k) (vheap vb) h' fr fr' H64 Habs
                         with "Hheap Hfr") as "(Hheap & Hfr & Hslots)".
            assert (Hb' : sval_den ρ v
                          = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                      (sign_extend' 64 (sign_extend' 12 imm))) k)
              by (rewrite -Hm1; exact Hw).
            iDestruct (stack_of_absorbed ρ v _ k Hb' with "Hslots") as "Hframe".
            iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (vpc vb)) imm
                      m (n - u) k b Hw
                      with "Hcg Hpc Hi Hframe").
            iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc".
            iEval (rewrite avi_mword) in "Hpc".
            assert (Hnk : ((n - u) + k)%nat = (n - (u - k))%nat) by lia.
            iEval (rewrite Hnk) in "Hcg".
            iDestruct (wp_next_shift Hs1 with "Hcont") as "Hcont".
            iApply (IH _ _ CID1 Hblk Hux1 Hxn
                      (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                      (agree_off_step Hao)
                      with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont"). }
          { (* PUSH: sp -= 2^64 - d *)
            apply Z.ltb_ge in Hdir.
            destruct (Z.eqb ((vsp_wrap - d) mod 8) 0) eqn:Hmod; cbn [negb] in Hstep;
              [|discriminate].
            apply Z.eqb_eq in Hmod.
            set (k := Z.to_nat ((vsp_wrap - d) / 8)) in *.
            injection Hstep as <-.
            cbn [vsu vsx] in Hux1, Hxmono.
            assert (Hkle0 : (k <= n - u)%nat) by lia.
            assert (Hek : 8 * Z.of_nat k = vsp_wrap - d)
              by (unfold k; apply div8_exact; [unfold vsp_wrap in *; lia | exact Hmod]).
            assert (Hw : add_vec (m !!! Regidx csp_rs1)
                                 (sign_extend' 64 (sign_extend' 12 imm))
                         = pa_stk (m !!! Regidx csp_rs1) k).
            { apply push_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
            iApply (wp_caddi_sp_push_s_sconf Φ (mword_of_int (vpc vb)) imm
                      m (n - u) k b Hkle0 Hw
                      with "Hcg Hpc Hi").
            iEval (rewrite /wp_next). iIntros (CID2 Hs2) "Hcg Hframe Hpc".
            iEval (rewrite avi_mword) in "Hpc".
            assert (Hnk : ((n - u) - k)%nat = (n - (u + k))%nat) by lia.
            iEval (rewrite Hnk) in "Hcg".
            assert (Hv'64 : sval_is64 (sval_addZ v d) = true)
              by (apply sval_addZ_is64; exact H64).
            assert (Hbase : sval_den ρ (sval_addZ v d)
                            = pa_stk (m !!! Regidx csp_rs1) k)
              by (rewrite -Hval; exact Hw).
            iEval (rewrite (vframe_own_of_stack ρ (sval_addZ v d) _ k Hv'64 Hbase))
              in "Hframe".
            iAssert (vframe_own ρ
                       (((fun j => sval_addZ (sval_addZ v d) (8 * Z.of_nat j))
                           <$> seq 0 k) ++ fr))
              with "[Hframe Hfr]" as "Hfr".
            { rewrite vframe_own_app. iFrame "Hframe Hfr". }
            iDestruct (wp_next_shift Hs2 with "Hcont") as "Hcont".
            iApply (IH _ _ CID2 Hblk Hux1 Hxn
                      (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                      (agree_off_step Hao)
                      with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont"). }
        * (* ---- ordinary c.addi rd, imm ---- *)
          destruct (rd_tp_bad rd) eqn:Hbad; [discriminate|].
          pose proof (rd_tp_bad_false _ Hbad) as Hrdok.
          unfold lift_base in Hstep; simpl in Hstep.
          destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
          apply Z.eqb_neq in Hrd0.
          destruct (vregs vb !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
          destruct (sval_is64 v1) eqn:H64; [|discriminate].
          injection Hstep as <-.
          pose proof (Hmatch _ _ Hrs1) as Hm1.
          assert (Hval : regval_into_reg
                      (add_vec (rget m rd) (sign_extend' 64 (sign_extend' 12 imm)))
                  = sval_den ρ (sval_addZ v1 (zimm12 (sign_extend' 12 imm)))).
          { unfold regval_into_reg.
            rewrite (rget_ne m rd (rd_ok_tp _ Hrdok)) Hm1
              (sval_den_add_imm ρ v1 (sign_extend' 12 imm) H64).
            reflexivity. }
          iApply (wp_caddi_s_sconf Φ (mword_of_int (vpc vb)) rd imm m (n - u) b
                    Hrd0 Hrdok
                    with "Hcg Hpc Hi").
          iEval (rewrite /wp_next). iIntros (CID3 Hs3) "Hcg Hpc".
          iEval (rewrite avi_mword) in "Hpc".
          iDestruct (wp_next_shift Hs3 with "Hcont") as "Hcont".
          epose proof (IH _ _ CID3 Hblk Hux1 Hxn
                      (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                      (agree_off_step Hao)) as IH1.
          cbn [vsu vsx vsb vsf vpc vregs vheap vheap4] in IH1.
          iApply (IH1 with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScaddi4spn *)
        destruct (rd_tp_bad rd) eqn:Hbad; [discriminate|].
        pose proof (rd_tp_bad_false _ Hbad) as Hrdok.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs vb !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (vpc vb))
                  rdc nzimm rd m (n - u) b Hrdc Hrd0 Hrdok
                  with "Hcg Hpc Hi").
        iEval (rewrite /wp_next). iIntros (CID4 Hs4) "Hcg Hpc".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
                = sval_den ρ (sval_addZ v1 (zimm12 (caddi4spn_imm nzimm)))).
        { unfold regval_into_reg.
          rewrite Hm1 (sval_den_add_imm ρ v1 (caddi4spn_imm nzimm) H64).
          reflexivity. }
        iDestruct (wp_next_shift Hs4 with "Hcont") as "Hcont".
        iApply (IH _ _ CID4 Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)
                  with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScsdsp : store, cell overwrite or ledger-slot initialization *)
        destruct (is_tp rs2) eqn:Hbad2; [discriminate|].
        pose proof (is_tp_false _ Hbad2) as Hrs2ok.
        destruct (vregs vb !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs vb !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        unfold vc_store8_sp in Hstep; cbn [vsb vsu vsx vsf] in Hstep.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        pose proof (rget_ne m rs2 Hrs2ok) as Hrget2.
        destruct (vheap_find (vheap vb) (sval_addZ v1 (zoff6 uimm)))
          as [[i vold]|] eqn:Hfind.
        * (* existing cell *)
          injection Hstep as <-.
          pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
          rewrite /vheap_own.
          iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
            as "[Hcell Hheapk]".
          iEval (cbn [fst snd]) in "Hcell".
          iEval (rewrite Hea) in "Hcell".
          iApply (wp_csdsp_s_sconf Φ (mword_of_int (vpc vb)) uimm rs2
                    m (n - u) (sval_den ρ vold) b
                    with "Hcg Hpc Hi Hcell").
          iEval (rewrite /wp_next). iIntros (CID5 Hs5) "Hcg Hpc Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hrget2 Hm2 -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iDestruct (wp_next_shift Hs5 with "Hcont") as "Hcont".
          iApply (IH _ _ CID5 Hblk Hux1 Hxn Hmatch Hao
                    with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
        * (* fresh ledger slot *)
          destruct (frame_remove fr (sval_addZ v1 (zoff6 uimm))) as [fr1|] eqn:Hfrm;
            [|discriminate].
          injection Hstep as <-.
          iEval (rewrite (vframe_own_remove ρ fr _ fr1 Hfrm)) in "Hfr".
          iDestruct "Hfr" as "[Hslot Hfr]".
          iDestruct "Hslot" as (wold) "Hslot".
          iEval (rewrite Hea) in "Hslot".
          iApply (wp_csdsp_s_sconf Φ (mword_of_int (vpc vb)) uimm rs2
                    m (n - u) wold b
                    with "Hcg Hpc Hi Hslot").
          iEval (rewrite /wp_next). iIntros (CID6 Hs6) "Hcg Hpc Hslot".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hrget2 Hm2 -Hea) in "Hslot".
          iAssert (vheap_own ρ (vheap vb ++ [(sval_addZ v1 (zoff6 uimm), v2)]))
            with "[Hheap Hslot]" as "Hheap".
          { rewrite vheap_own_snoc. iFrame "Hheap Hslot". }
          iDestruct (wp_next_shift Hs6 with "Hcont") as "Hcont".
          iApply (IH _ _ CID6 Hblk Hux1 Hxn Hmatch Hao
                    with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScldsp *)
        destruct (rd_tp_bad rd) eqn:Hbad; [discriminate|].
        pose proof (rd_tp_bad_false _ Hbad) as Hrdok.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs vb !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap vb) (sval_addZ v1 (zoff6 uimm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_cldsp_s_sconf Φ (mword_of_int (vpc vb)) uimm rd
                  m (n - u) (sval_den ρ vv) b (dqm:=DfracOwn 1) Hrd0 Hrdok
                  with "Hcg Hpc Hi Hcell").
        iEval (rewrite /wp_next). iIntros (CID7 Hs7) "Hcg Hpc Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv)
          by reflexivity.
        iDestruct (wp_next_shift Hs7 with "Hcont") as "Hcont".
        iApply (IH _ _ CID7 Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)
                  with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VSclw *)
        destruct (orb (rd_tp_bad rd) (is_tp rs1)) eqn:Hbad; [discriminate|].
        apply orb_false_iff in Hbad as [Hbadrd Hbadrs1].
        pose proof (rd_tp_bad_false _ Hbadrd) as Hrdok.
        pose proof (is_tp_false _ Hbadrs1) as Hrs1ok.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs vb !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 vb) (sval_addZ v1 (zimm12 imm)))
          as [[i w32]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (rget m rs1) (sign_extend' 64 imm)).
        { rewrite (rget_ne m rs1 Hrs1ok) (sval_den_add_imm ρ v1 imm H64) Hm1.
          reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_clw_s_sconf Φ (mword_of_int (vpc vb)) rd rs1 imm
                  m (n - u) (sval32_den ρ w32) b (dqm:=DfracOwn 1) Hrd0 Hrdok
                  with "Hcg Hpc Hi Hcell").
        iEval (rewrite /wp_next). iIntros (CID8 Hs8) "Hcg Hpc Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sign_extend' 64 (sval32_den ρ w32))
                       = sval_den ρ (S32 w32)) by reflexivity.
        iDestruct (wp_next_shift Hs8 with "Hcont") as "Hcont".
        iApply (IH _ _ CID8 Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)
                  with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScsw *)
        destruct (orb (is_tp rs1) (is_tp rs2)) eqn:Hbad; [discriminate|].
        apply orb_false_iff in Hbad as [Hbadrs1 Hbadrs2].
        pose proof (is_tp_false _ Hbadrs1) as Hrs1ok.
        pose proof (is_tp_false _ Hbadrs2) as Hrs2ok.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (vregs vb !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs vb !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 vb) (sval_addZ v1 (zimm12 imm)))
          as [[i wold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (rget m rs1) (sign_extend' 64 imm)).
        { rewrite (rget_ne m rs1 Hrs1ok) (sval_den_add_imm ρ v1 imm H64) Hm1.
          reflexivity. }
        assert (Hsv : trunc32 (rget m rs2) = sval32_den ρ (sval_trunc32 v2)).
        { rewrite (rget_ne m rs2 Hrs2ok) sval_trunc32_den Hm2. reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csw_s_sconf Φ (mword_of_int (vpc vb)) rs2 rs1 imm
                  m (n - u) (sval32_den ρ wold) b
                  with "Hcg Hpc Hi Hcell").
        iEval (rewrite /wp_next). iIntros (CID9 Hs9) "Hcg Hpc Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite Hsv -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), sval_trunc32 v2)
                     with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        iDestruct (wp_next_shift Hs9 with "Hcont") as "Hcont".
        iApply (IH _ _ CID9 Hblk Hux1 Hxn Hmatch Hao
                  with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScaddiw *)
        destruct (rd_tp_bad rd) eqn:Hbad; [discriminate|].
        pose proof (rd_tp_bad_false _ Hbad) as Hrdok.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs vb !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hval : regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (rget m rd)
                                (sign_extend' 64 (sign_extend' 12 imm))) 31 0))
                = sval_den ρ (S32 (sval32_addZ (sval_trunc32 v1) (zimm32 imm)))).
        { unfold regval_into_reg. rewrite (rget_ne m rd (rd_ok_tp _ Hrdok)) Hm1.
          cbn [sval_den].
          rewrite sval32_den_addZ.
          rewrite sval_trunc32_den.
          unfold zimm32. rewrite mword_of_int_uint32.
          rewrite -trunc32_add.
          rewrite trunc32_subrange. reflexivity. }
        iApply (wp_caddiw_s_sconf Φ (mword_of_int (vpc vb)) rd imm m (n - u) b
                  Hrd0 Hrdok
                  with "Hcg Hpc Hi").
        iEval (rewrite /wp_next). iIntros (CID10 Hs10) "Hcg Hpc".
        iEval (rewrite avi_mword) in "Hpc".
        iDestruct (wp_next_shift Hs10 with "Hcont") as "Hcont".
        epose proof (IH _ _ CID10 Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)) as IH1.
        cbn [vsu vsx vsb vsf vpc vregs vheap vheap4] in IH1.
        iApply (IH1 with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VSsd : store, cell overwrite or ledger-slot initialization *)
        destruct (orb (is_tp rs1) (is_tp rs2)) eqn:Hbad; [discriminate|].
        apply orb_false_iff in Hbad as [Hbadrs1 Hbadrs2].
        pose proof (is_tp_false _ Hbadrs1) as Hrs1ok.
        pose proof (is_tp_false _ Hbadrs2) as Hrs2ok.
        destruct (vregs vb !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs vb !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        unfold vc_store8_sp in Hstep; cbn [vsb vsu vsx vsf] in Hstep.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (rget m rs1) (sign_extend' 64 imm)).
        { rewrite (rget_ne m rs1 Hrs1ok) (sval_den_add_imm ρ v1 imm H64) Hm1.
          reflexivity. }
        assert (Hsv : rget m rs2 = sval_den ρ v2).
        { rewrite (rget_ne m rs2 Hrs2ok). exact Hm2. }
        destruct (vheap_find (vheap vb) (sval_addZ v1 (zimm12 imm)))
          as [[i vold]|] eqn:Hfind.
        * (* existing cell *)
          injection Hstep as <-.
          pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
          rewrite /vheap_own.
          iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
            as "[Hcell Hheapk]".
          iEval (cbn [fst snd]) in "Hcell".
          iEval (rewrite Hea) in "Hcell".
          destruct rvc.
          -- iApply (wp_csd_s_sconf Φ (mword_of_int (vpc vb)) rs2 rs1 imm
                       m (n - u) (sval_den ρ vold) b
                       with "Hcg Hpc Hi Hcell").
             iEval (rewrite /wp_next). iIntros (CID11 Hs11) "Hcg Hpc Hcell".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hsv -Hea) in "Hcell".
             iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
               as "Hheap"; [iExact "Hcell"|].
             iDestruct (wp_next_shift Hs11 with "Hcont") as "Hcont".
             iApply (IH _ _ CID11 Hblk Hux1 Hxn Hmatch Hao
                       with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
          -- iApply (wp_sd_s_sconf Φ (mword_of_int (vpc vb)) rs2 rs1 imm
                       m (n - u) (sval_den ρ vold) b
                       with "Hcg Hpc Hi Hcell").
             iEval (rewrite /wp_next). iIntros (CID12 Hs12) "Hcg Hpc Hcell".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hsv -Hea) in "Hcell".
             iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
               as "Hheap"; [iExact "Hcell"|].
             iDestruct (wp_next_shift Hs12 with "Hcont") as "Hcont".
             iApply (IH _ _ CID12 Hblk Hux1 Hxn Hmatch Hao
                       with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
        * (* fresh ledger slot *)
          destruct (frame_remove fr (sval_addZ v1 (zimm12 imm))) as [fr1|] eqn:Hfrm;
            [|discriminate].
          injection Hstep as <-.
          iEval (rewrite (vframe_own_remove ρ fr _ fr1 Hfrm)) in "Hfr".
          iDestruct "Hfr" as "[Hslot Hfr]".
          iDestruct "Hslot" as (wold) "Hslot".
          iEval (rewrite Hea) in "Hslot".
          destruct rvc.
          -- iApply (wp_csd_s_sconf Φ (mword_of_int (vpc vb)) rs2 rs1 imm
                       m (n - u) wold b
                       with "Hcg Hpc Hi Hslot").
             iEval (rewrite /wp_next). iIntros (CID13 Hs13) "Hcg Hpc Hslot".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hsv -Hea) in "Hslot".
             iAssert (vheap_own ρ (vheap vb ++ [(sval_addZ v1 (zimm12 imm), v2)]))
               with "[Hheap Hslot]" as "Hheap".
             { rewrite vheap_own_snoc. iFrame "Hheap Hslot". }
             iDestruct (wp_next_shift Hs13 with "Hcont") as "Hcont".
             iApply (IH _ _ CID13 Hblk Hux1 Hxn Hmatch Hao
                       with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
          -- iApply (wp_sd_s_sconf Φ (mword_of_int (vpc vb)) rs2 rs1 imm
                       m (n - u) wold b
                       with "Hcg Hpc Hi Hslot").
             iEval (rewrite /wp_next). iIntros (CID14 Hs14) "Hcg Hpc Hslot".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hsv -Hea) in "Hslot".
             iAssert (vheap_own ρ (vheap vb ++ [(sval_addZ v1 (zimm12 imm), v2)]))
               with "[Hheap Hslot]" as "Hheap".
             { rewrite vheap_own_snoc. iFrame "Hheap Hslot". }
             iDestruct (wp_next_shift Hs14 with "Hcont") as "Hcont".
             iApply (IH _ _ CID14 Hblk Hux1 Hxn Hmatch Hao
                       with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VSld *)
        destruct (orb (rd_tp_bad rd) (is_tp rs1)) eqn:Hbad; [discriminate|].
        apply orb_false_iff in Hbad as [Hbadrd Hbadrs1].
        pose proof (rd_tp_bad_false _ Hbadrd) as Hrdok.
        pose proof (is_tp_false _ Hbadrs1) as Hrs1ok.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs vb !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap vb) (sval_addZ v1 (zimm12 imm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (rget m rs1) (sign_extend' 64 imm)).
        { rewrite (rget_ne m rs1 Hrs1ok) (sval_den_add_imm ρ v1 imm H64) Hm1.
          reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv) by reflexivity.
        destruct rvc.
        * iApply (wp_cld_s_sconf Φ (mword_of_int (vpc vb)) rd rs1 imm
                    m (n - u) (sval_den ρ vv) b (dqm:=DfracOwn 1) Hrd0 Hrdok
                    with "Hcg Hpc Hi Hcell").
          iEval (rewrite /wp_next). iIntros (CID15 Hs15) "Hcg Hpc Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iDestruct (wp_next_shift Hs15 with "Hcont") as "Hcont".
          iApply (IH _ _ CID15 Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
        * iApply (wp_ld_s_sconf Φ (mword_of_int (vpc vb)) rd rs1 imm
                    m (n - u) (sval_den ρ vv) b (dqm:=DfracOwn 1) Hrd0 Hrdok
                    with "Hcg Hpc Hi Hcell").
          iEval (rewrite /wp_next). iIntros (CID16 Hs16) "Hcg Hpc Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iDestruct (wp_next_shift Hs16 with "Hcont") as "Hcont".
          iApply (IH _ _ CID16 Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScaddi16sp : an sp move -- invert over abstract d (sp_move_inv) *)
        set (d := zimm12 (caddi16sp_imm imm6)) in *.
        apply sp_move_inv in Hstep.
        cbn [vsb vsu vsx vsf] in Hstep.
        destruct Hstep as (v & Hrs1 & H64 & Hd0 & HdW & Hdz & Hcase).
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi16sp_imm imm6)))
                = sval_den ρ (sval_addZ v d)).
        { unfold regval_into_reg.
          rewrite (sval_den_addZ ρ v d H64) Hm1.
          unfold d, zimm12. rewrite stk_mword_of_int_uint. reflexivity. }
        destruct Hcase as [ (Hdir & Hmod & Hku0 & h' & fr' & Habs & ->)
                          | (Hdir & Hmod & ->) ].
        * (* POP: sp += d *)
          set (k := Z.to_nat (d / 8)) in *.
          cbn [vsu vsx] in Hux1, Hxmono.
          assert (Hek : 8 * Z.of_nat k = d)
            by (unfold k; apply div8_exact; [lia | exact Hmod]).
          assert (Hw : m !!! Regidx csp_rs1
                       = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                   (sign_extend' 64 (caddi16sp_imm imm6))) k).
          { apply pop_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
          iDestruct (pop_absorb_sound ρ v (seq 0 k) (vheap vb) h' fr fr' H64 Habs
                       with "Hheap Hfr") as "(Hheap & Hfr & Hslots)".
          assert (Hb' : sval_den ρ v
                        = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                    (sign_extend' 64 (caddi16sp_imm imm6))) k)
            by (rewrite -Hm1; exact Hw).
          iDestruct (stack_of_absorbed ρ v _ k Hb' with "Hslots") as "Hframe".
          iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (vpc vb)) imm6
                    m (n - u) k b Hw
                    with "Hcg Hpc Hi Hframe").
          iEval (rewrite /wp_next). iIntros (CID17 Hs17) "Hcg Hpc".
          iEval (rewrite avi_mword) in "Hpc".
          assert (Hnk : ((n - u) + k)%nat = (n - (u - k))%nat) by lia.
          iEval (rewrite Hnk) in "Hcg".
          iDestruct (wp_next_shift Hs17 with "Hcont") as "Hcont".
          iApply (IH _ _ CID17 Hblk Hux1 Hxn
                    (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
        * (* PUSH: sp -= 2^64 - d *)
          set (k := Z.to_nat ((vsp_wrap - d) / 8)) in *.
          cbn [vsu vsx] in Hux1, Hxmono.
          assert (Hkle0 : (k <= n - u)%nat) by lia.
          assert (Hek : 8 * Z.of_nat k = vsp_wrap - d)
            by (unfold k; apply div8_exact; [unfold vsp_wrap in *; lia | exact Hmod]).
          assert (Hw : add_vec (m !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm imm6))
                       = pa_stk (m !!! Regidx csp_rs1) k).
          { apply push_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
          iApply (wp_caddi16sp_push_s_sconf Φ (mword_of_int (vpc vb)) imm6
                    m (n - u) k b Hkle0 Hw
                    with "Hcg Hpc Hi").
          iEval (rewrite /wp_next). iIntros (CID18 Hs18) "Hcg Hframe Hpc".
          iEval (rewrite avi_mword) in "Hpc".
          assert (Hnk : ((n - u) - k)%nat = (n - (u + k))%nat) by lia.
          iEval (rewrite Hnk) in "Hcg".
          assert (Hv'64 : sval_is64 (sval_addZ v d) = true)
            by (apply sval_addZ_is64; exact H64).
          assert (Hbase : sval_den ρ (sval_addZ v d)
                          = pa_stk (m !!! Regidx csp_rs1) k)
            by (rewrite -Hval; exact Hw).
          iEval (rewrite (vframe_own_of_stack ρ (sval_addZ v d) _ k Hv'64 Hbase))
            in "Hframe".
          iAssert (vframe_own ρ
                     (((fun j => sval_addZ (sval_addZ v d) (8 * Z.of_nat j))
                         <$> seq 0 k) ++ fr))
            with "[Hframe Hfr]" as "Hfr".
          { rewrite vframe_own_app. iFrame "Hframe Hfr". }
          iDestruct (wp_next_shift Hs18 with "Hcont") as "Hcont".
          iApply (IH _ _ CID18 Hblk Hux1 Hxn
                    (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
  Qed.

  (* the [m0 := m] instantiation: entry agreement is reflexive.  The usual
     client shape: [st := VSS b 0 0 []] (block entry: no pushed depth, an
     empty ledger -- supply [vframe_own_nil]), premise [vsx st' <= n] a
     concrete literal vs the spec's stack bound, and [Nat.sub_0_r] to read
     [n - 0] back as [n]. *)
  Lemma wp_vc_block_s_sconf
      (prog : list vop_s) (Φ : mval -> iProp Σ)
      (st st' : vsstate) (ρ : nat -> mword 64)
      (m : regfile) (n : nat) (b : bool) :
    vc_block_sp_s st prog = Some st' ->
    (vsu st <= vsx st)%nat ->
    (vsx st' <= n)%nat ->
    gpr_matches ρ (vsb st).(vregs) m ->
    sie_cap_gpr m (n - vsu st) b p -∗
    pc_is (mword_of_int (vsb st).(vpc)) -∗
    block_instrs_s (vsb st).(vpc) prog -∗
    vheap_own ρ (vsb st).(vheap) -∗
    vheap4_own ρ (vsb st).(vheap4) -∗
    vframe_own ρ (vsf st) -∗
    wp_next b (fun (CID : CpuId) =>
      (∀ mf : regfile,
      ⌜ gpr_matches ρ (vsb st').(vregs) mf ∧ agree_off (vsb st').(vregs) mf m ⌝ -∗
      sie_cap_gpr mf (n - vsu st') b p -∗
      pc_is (mword_of_int (vsb st').(vpc)) -∗
      vheap_own ρ (vsb st').(vheap) -∗
      vheap4_own ρ (vsb st').(vheap4) -∗
      vframe_own ρ (vsf st') -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hblk Hux Hxn Hmatch.
    iIntros "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont".
    iApply (wp_vc_block_s_sconf_aux prog Φ st st' ρ m m n b
              Hblk Hux Hxn Hmatch (fun r _ => eq_refl)
              with "Hcg Hpc Hbi Hheap Hheap4 Hfr Hcont").
  Qed.

End WpSconfVc.
