(* HartMemAsm.v -- THE GENERAL-[mm] ASSEMBLY TOOLKIT for [HartMemRun.goodmb].

   [HartMemRun] section 4b gives the register-only twin's toolkit: the four
   [goodmb_*_empty] combinators, where [mm := ∅] collapses the [mm_after]
   argument of every bind equation and no map bookkeeping is ever needed.
   The MEMORY twins (the data-access and walk families) are stated at an
   ARBITRARY owned map, so that collapse is not available -- and writing
   [mm_after] into every intermediate goal would make each twin unreadable
   and would not match the [exec] proof it mirrors.

   THE ONE OBSERVATION THAT REMOVES ALL OF IT: [goodmb] consults the map
   only through [bytes_owned], i.e. only through its DOMAIN
   ([HartMemRun.goodmb_dom]), and a CERTIFIED stretch preserves that domain
   ([mm_after_dom] below -- every write it makes is inside the owned bytes,
   which is exactly what its own certificate says).  So the continuation's
   certificate may always be read back at the ORIGINAL map, and every bind
   equation below is [HartMemRun]'s with [mm_after m s mm] rewritten to
   [mm].  The result is that

     A MEMORY TWIN'S PROOF IS THE [exec] PROOF, NODE FOR NODE, with each
     [exec_X] replaced by the [gm_X] of the same shape and the head's
     [exec] fact PAIRED with the head's own certificate,

   which is the register-only rule of [HartMemRun] section 4b extended to a
   real byte map.  The names mirror the [exec] side one for one:

     exec_bind_Some      / exec_bind0_Some     -> gm_bind      / gm_bind0
     execR_bind_Some     / execR_bind0_Some    -> gm_bindR     / gm_bind0R
     execR_liftR_seq                           -> gm_liftR_seq / gm_liftR_seq0
     exec_and_boolM_Some / exec_or_boolM_Some  -> gm_and_boolM / gm_or_boolM

   plus the [catch_early_return] family ([gm_cer_*]), which a region that
   THROWS needs: [goodmb] refuses an [ExtraOutcome] node outright, so such a
   body has no certificate of its own and the wrapper must stay ON while the
   chain is peeled.  The walk ends at the thrown tail, where
   [catch_early_return (bind (early_return r) K) = Ret r] by CONVERSION
   ([mcer_early_return]) and the certificate is [reflexivity].

   And the LEFT-nested variants ([_nest]): Sail's [>>]/[>>=] are left
   associative, so a chain reads as [bind (bind m g) f] and the plain bind
   equation would ask for [exec] of the composite [bind m g], which no proof
   has -- it has the INNERMOST head's facts. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import HartMemRun.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. THE DOMAIN IS PRESERVED BY A CERTIFIED STRETCH.                       *)
(*                                                                         *)
(* Every memory WRITE the path makes is inside the owned bytes -- that is   *)
(* what the certificate's [bytes_owned] conjunct says -- and [write_bytes]  *)
(* at an owned footprint preserves the domain.  This is what lets every     *)
(* combinator below read the continuation's certificate back at the         *)
(* ORIGINAL map.                                                            *)
(* ---------------------------------------------------------------------- *)
Lemma mm_after_dom (Dr Dw : register -> bool) {E X} (m : Defs.monad E X) :
  forall (s : mstate) mm,
    goodmb Dr Dw m s mm = true -> dom (mm_after m s mm) = dom mm.
Proof.
  induction m as [y | T oc k IH]; intros s mm Hg; [reflexivity|].
  destruct oc as [ reg ak | reg ak regval | nb rreq | nb wreq | opc
                 | bsz bpa | bar | cop | tlbo | flt | rpa | tst | ten
                 | A ao | gmsg | | | cty | | msg ];
    cbn [goodmb mm_after] in Hg |- *; try discriminate Hg.
  { apply andb_prop in Hg as [_ Hg]. by apply (IH _ s mm). }
  { apply andb_prop in Hg as [_ Hg]. by apply (IH tt _ mm). }
  { apply andb_prop in Hg as [_ Hg2].
    destruct (read_bytes s.(mem) (Interface.ReadReq.pa rreq) nb) as [w|];
      [by apply (IH _ s mm)|reflexivity]. }
  { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [_ Hfp].
    rewrite (IH (inl None) _ _ Hg2). by apply write_bytes_dom. }
  all: first [ by apply (IH tt s mm) | by apply (IH 0%Z s mm) ].
Qed.

(* the one-line consequence every combinator below uses *)
Lemma goodmb_after_dom (Dr Dw : register -> bool) {E X} (m : Defs.monad E X)
    {E' Y} (n : Defs.monad E' Y) (s0 s : mstate) mm :
  goodmb Dr Dw m s0 mm = true ->
  goodmb Dr Dw n s (mm_after m s0 mm) = goodmb Dr Dw n s mm.
Proof.
  intros Hg. apply goodmb_dom. exact (mm_after_dom Dr Dw m s0 mm Hg).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE BIND FAMILY, at an arbitrary map.                                 *)
(* ---------------------------------------------------------------------- *)
Lemma gm_bind (Dr Dw : register -> bool) {X Y} (m : M X) (f : X -> M Y)
    (s s' : mstate) mm (x : X) :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (x, s') ->
  goodmb Dr Dw (Defs.bind m f) s mm = goodmb Dr Dw (f x) s' mm.
Proof.
  intros Hg He. rewrite (goodmb_bind Dr Dw m f s s' mm x Hg He).
  exact (goodmb_after_dom Dr Dw m (f x) s s' mm Hg).
Qed.

Lemma gm_bind0 (Dr Dw : register -> bool) {Y} (m : M unit) (n : M Y)
    (s s' : mstate) mm :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (tt, s') ->
  goodmb Dr Dw (Defs.bind0 m n) s mm = goodmb Dr Dw n s' mm.
Proof. intros Hg He. exact (gm_bind Dr Dw m (fun _ => n) s s' mm tt Hg He). Qed.

Lemma gm_bindR (Dr Dw : register -> bool) {R X Y : Type}
    (m : Defs.monadR R exception X) (f : X -> Defs.monadR R exception Y)
    (s s' : mstate) mm (x : X) :
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr x, s') ->
  goodmb Dr Dw (Defs.bind m f) s mm = goodmb Dr Dw (f x) s' mm.
Proof.
  intros Hg He. rewrite (goodmb_bindR Dr Dw m f s s' mm x Hg He).
  exact (goodmb_after_dom Dr Dw m (f x) s s' mm Hg).
Qed.

Lemma gm_bind0R (Dr Dw : register -> bool) {R Y : Type}
    (m : Defs.monadR R exception unit) (n : Defs.monadR R exception Y)
    (s s' : mstate) mm :
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr tt, s') ->
  goodmb Dr Dw (Defs.bind0 m n) s mm = goodmb Dr Dw n s' mm.
Proof. intros Hg He. exact (gm_bindR Dr Dw m (fun _ => n) s s' mm tt Hg He). Qed.

Lemma gm_bind_nest (Dr Dw : register -> bool) {X Y Z : Type}
    (m : M X) (g : X -> M Y) (f : Y -> M Z) (s s' : mstate) mm (x : X) :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (x, s') ->
  goodmb Dr Dw (Defs.bind (Defs.bind m g) f) s mm
  = goodmb Dr Dw (Defs.bind (g x) f) s' mm.
Proof.
  intros Hg He. rewrite (goodmb_bind_nest Dr Dw m g f s s' mm x Hg He).
  exact (goodmb_after_dom Dr Dw m (Defs.bind (g x) f) s s' mm Hg).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE [liftR] PREFIX, [execR_liftR_seq]'s twin: a lifted base           *)
(*    computation never early-returns, so its own certificate is the base   *)
(*    one ([goodmb_liftR]) and the walk continues at [exec]'s post state.   *)
(* ---------------------------------------------------------------------- *)
Lemma goodmb_liftR_execR {R X} (m : M X) (s s' : mstate) (x : X) :
  exec m s = Some (x, s') ->
  execR (Defs.liftR (R := R) m) s = Some (inr x, s').
Proof. intros He. rewrite execR_liftR. rewrite He. reflexivity. Qed.

Lemma gm_liftR_seq (Dr Dw : register -> bool) {R X Y}
    (m : M Y) (f : Y -> Defs.monadR R exception X)
    (s s' : mstate) mm (y : Y) :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (y, s') ->
  goodmb Dr Dw (Defs.bind (Defs.liftR m) f) s mm = goodmb Dr Dw (f y) s' mm.
Proof.
  intros Hg He.
  exact (gm_bindR Dr Dw (Defs.liftR m) f s s' mm y
           (goodmb_liftR Dr Dw m s mm Hg) (goodmb_liftR_execR m s s' y He)).
Qed.

Lemma gm_liftR_seq0 (Dr Dw : register -> bool) {R X}
    (m : M unit) (n : Defs.monadR R exception X) (s s' : mstate) mm :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (tt, s') ->
  goodmb Dr Dw (Defs.bind0 (Defs.liftR m) n) s mm = goodmb Dr Dw n s' mm.
Proof.
  intros Hg He. exact (gm_liftR_seq Dr Dw m (fun _ => n) s s' mm tt Hg He).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE TWO SHORT-CIRCUITING BOOLEAN CONNECTIVES.                         *)
(* ---------------------------------------------------------------------- *)
Lemma gm_and_boolM (Dr Dw : register -> bool) (l r : M bool)
    (s sl : mstate) mm (bl : bool) :
  goodmb Dr Dw l s mm = true ->
  exec l s = Some (bl, sl) ->
  goodmb Dr Dw (Defs.and_boolM l r) s mm
  = (if bl then goodmb Dr Dw r sl mm else true).
Proof.
  intros Hg He. unfold Defs.and_boolM.
  rewrite (gm_bind Dr Dw l _ s sl mm bl Hg He). by destruct bl.
Qed.

Lemma gm_or_boolM (Dr Dw : register -> bool) (l r : M bool)
    (s sl : mstate) mm (bl : bool) :
  goodmb Dr Dw l s mm = true ->
  exec l s = Some (bl, sl) ->
  goodmb Dr Dw (Defs.or_boolM l r) s mm
  = (if bl then true else goodmb Dr Dw r sl mm).
Proof.
  intros Hg He. unfold Defs.or_boolM.
  rewrite (gm_bind Dr Dw l _ s sl mm bl Hg He). by destruct bl.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE EARLY-RETURN REGION.  A body that THROWS has no certificate of    *)
(*    its own ([goodmb] refuses an [ExtraOutcome] node), so the wrapper     *)
(*    stays ON while the chain is peeled, and the walk ends at the thrown   *)
(*    tail where [mcer_early_return] is a CONVERSION.                       *)
(* ---------------------------------------------------------------------- *)
Lemma mcer_early_return {X Y : Type} (r : X)
    (K : Y -> Defs.monadR X exception X) :
  Defs.catch_early_return (Defs.bind (Defs.early_return r) K)
  = (Defs.returnm r : M X).
Proof. reflexivity. Qed.

Lemma mcer_early_return0 {X : Type} (r : X) (K : Defs.monadR X exception X) :
  Defs.catch_early_return (Defs.bind0 (Defs.early_return r) K)
  = (Defs.returnm r : M X).
Proof. reflexivity. Qed.

Lemma gm_cer_bind (Dr Dw : register -> bool) {X Y : Type}
    (m : Defs.monadR X exception Y) (f : Y -> Defs.monadR X exception X)
    (s s' : mstate) mm (x : Y) :
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr x, s') ->
  goodmb Dr Dw (Defs.catch_early_return (Defs.bind m f)) s mm
  = goodmb Dr Dw (Defs.catch_early_return (f x)) s' mm.
Proof.
  intros Hg He. rewrite (goodmb_cer_bind Dr Dw m f s s' mm x Hg He).
  exact (goodmb_after_dom Dr Dw m (Defs.catch_early_return (f x)) s s' mm Hg).
Qed.

Lemma gm_cer_bind0 (Dr Dw : register -> bool) {X : Type}
    (m : Defs.monadR X exception unit) (n : Defs.monadR X exception X)
    (s s' : mstate) mm :
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr tt, s') ->
  goodmb Dr Dw (Defs.catch_early_return (Defs.bind0 m n)) s mm
  = goodmb Dr Dw (Defs.catch_early_return n) s' mm.
Proof. intros Hg He. exact (gm_cer_bind Dr Dw m (fun _ => n) s s' mm tt Hg He). Qed.

Lemma gm_cer_bind_nest (Dr Dw : register -> bool) {X Y Z : Type}
    (m : Defs.monadR X exception Y) (g : Y -> Defs.monadR X exception Z)
    (f : Z -> Defs.monadR X exception X) (s s' : mstate) mm (y : Y) :
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr y, s') ->
  goodmb Dr Dw (Defs.catch_early_return (Defs.bind (Defs.bind m g) f)) s mm
  = goodmb Dr Dw (Defs.catch_early_return (Defs.bind (g y) f)) s' mm.
Proof.
  intros Hg He. rewrite (goodmb_cer_bind_nest Dr Dw m g f s s' mm y Hg He).
  exact (goodmb_after_dom Dr Dw m
           (Defs.catch_early_return (Defs.bind (g y) f)) s s' mm Hg).
Qed.

(* the [liftR] prefix inside an early-return region -- the shape almost
   every checked-access proof peels, since [checked_mem_read]'s body is a
   [catch_early_return] whose steps are all lifted base computations *)
Lemma gm_cer_liftR_seq (Dr Dw : register -> bool) {X Y : Type}
    (m : M Y) (f : Y -> Defs.monadR X exception X) (s s' : mstate) mm (y : Y) :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (y, s') ->
  goodmb Dr Dw (Defs.catch_early_return (Defs.bind (Defs.liftR m) f)) s mm
  = goodmb Dr Dw (Defs.catch_early_return (f y)) s' mm.
Proof.
  intros Hg He.
  exact (gm_cer_bind Dr Dw (Defs.liftR m) f s s' mm y
           (goodmb_liftR Dr Dw m s mm Hg) (goodmb_liftR_execR m s s' y He)).
Qed.

Lemma gm_cer_liftR_seq0 (Dr Dw : register -> bool) {X : Type}
    (m : M unit) (n : Defs.monadR X exception X) (s s' : mstate) mm :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (tt, s') ->
  goodmb Dr Dw (Defs.catch_early_return (Defs.bind0 (Defs.liftR m) n)) s mm
  = goodmb Dr Dw (Defs.catch_early_return n) s' mm.
Proof.
  intros Hg He. exact (gm_cer_liftR_seq Dr Dw m (fun _ => n) s s' mm tt Hg He).
Qed.

Lemma gm_cer_liftR_nest (Dr Dw : register -> bool) {X Y Z : Type}
    (m : M Y) (g : Y -> Defs.monadR X exception Z)
    (f : Z -> Defs.monadR X exception X) (s s' : mstate) mm (y : Y) :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (y, s') ->
  goodmb Dr Dw
    (Defs.catch_early_return (Defs.bind (Defs.bind (Defs.liftR m) g) f)) s mm
  = goodmb Dr Dw (Defs.catch_early_return (Defs.bind (g y) f)) s' mm.
Proof.
  intros Hg He.
  exact (gm_cer_bind_nest Dr Dw (Defs.liftR m) g f s s' mm y
           (goodmb_liftR Dr Dw m s mm Hg) (goodmb_liftR_execR m s s' y He)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. THE ASSEMBLY TACTICS, [HartMemRun]'s [gm_peel] family at a real map.  *)
(*    Each tries the shapes in the order a Sail chain presents them: the    *)
(*    plain bind, the [bind0], the [liftR] prefix, and the one-level-in     *)
(*    nest that LEFT associativity produces.                                *)
(* ---------------------------------------------------------------------- *)
Ltac gmm_peel Hg He :=
  first
    [ erewrite (gm_bind0 _ _ _ _ _ _ _ Hg He)
    | erewrite (gm_bind _ _ _ _ _ _ _ _ Hg He)
    | erewrite gm_bind0;  [ | exact Hg | exact He ]
    | erewrite gm_bind;   [ | exact Hg | exact He ]
    | erewrite gm_bind0R; [ | exact Hg | exact He ]
    | erewrite gm_bindR;  [ | exact Hg | exact He ]
    | ( unfold Defs.bind0;
        first [ erewrite gm_bind_nest; [ | exact Hg | exact He ]
              | erewrite gm_bind;      [ | exact Hg | exact He ] ] ) ].

Ltac gmm_lift Hg He :=
  first
    [ erewrite gm_liftR_seq0;    [ | exact Hg | exact He ]
    | erewrite gm_liftR_seq;     [ | exact Hg | exact He ]
    | erewrite gm_cer_liftR_seq0;[ | exact Hg | exact He ]
    | erewrite gm_cer_liftR_seq; [ | exact Hg | exact He ]
    | erewrite gm_cer_liftR_nest;[ | exact Hg | exact He ] ].

Ltac gmm_pure :=
  first [ erewrite gm_bind0; [ | apply goodmb_returnm | apply exec_returnm ]
        | erewrite gm_bind;  [ | apply goodmb_returnm | apply exec_returnm ] ].

Ltac gmm_rr r H :=
  first
    [ erewrite gm_bind;
        [ | etransitivity; [ apply goodmb_read_reg | exact H ]
          | apply (exec_read_reg r) ]
    | erewrite gm_bind0;
        [ | etransitivity; [ apply goodmb_read_reg | exact H ]
          | apply (exec_read_reg r) ]
    | erewrite gm_bind_nest;
        [ | etransitivity; [ apply goodmb_read_reg | exact H ]
          | apply (exec_read_reg r) ] ].

Ltac gmm_wr r H :=
  first
    [ erewrite gm_bind0;
        [ | etransitivity; [ apply goodmb_write_reg | exact H ]
          | apply (exec_write_reg r _) ]
    | erewrite gm_bind;
        [ | etransitivity; [ apply goodmb_write_reg | exact H ]
          | apply (exec_write_reg r _) ]
    | erewrite gm_bind_nest;
        [ | etransitivity; [ apply goodmb_write_reg | exact H ]
          | apply (exec_write_reg r _) ] ].

(* ---------------------------------------------------------------------- *)
(* 7. THE TWO MEMORY NODES, as reduction equations                          *)
(*    ([RiscvFetchExec.exec_MemRead] / [exec_MemWrite]'s twins), and the     *)
(*    two RAM bricks on top of them.                                        *)
(*                                                                         *)
(* The write equation reads its continuation's certificate back at the      *)
(* ORIGINAL map: the footprint is owned, so [write_bytes] does not move the *)
(* domain and [goodmb_dom] carries it.                                      *)
(* ---------------------------------------------------------------------- *)
Lemma gm_MemRead (Dr Dw : register -> bool) {X} (n : N)
    (req : Interface.ReadReq.t n)
    (k : (bv (8 * n) * option bool + Arch.abort)%type -> M X) s mm :
  dev_addr (Interface.ReadReq.pa req) = false ->
  bytes_owned mm (Interface.ReadReq.pa req) n = true ->
  goodmb Dr Dw (Interface.Next (Interface.MemRead n req) k) s mm
  = match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
    | Some w => goodmb Dr Dw (k (inl (w, None))) s mm
    | None => false
    end.
Proof.
  intros Hd Hfp. cbn [goodmb]. rewrite Hd. rewrite Hfp.
  cbn [negb andb]. reflexivity.
Qed.

Lemma gm_MemWrite (Dr Dw : register -> bool) {X} (n : N)
    (req : Interface.WriteReq.t n)
    (k : (option bool + Arch.abort)%type -> M X) s mm :
  dev_addr (Interface.WriteReq.pa req) = false ->
  bytes_owned mm (Interface.WriteReq.pa req) n = true ->
  goodmb Dr Dw (Interface.Next (Interface.MemWrite n req) k) s mm
  = goodmb Dr Dw (k (inl None))
      (MState s.(sregs)
         (write_bytes s.(mem) (Interface.WriteReq.pa req) n
            (Interface.WriteReq.value req)) s.(mdev)) mm.
Proof.
  intros Hd Hfp. cbn [goodmb]. rewrite Hd. rewrite Hfp.
  cbn [negb andb]. apply goodmb_dom. by apply write_bytes_dom.
Qed.

(* the read kinds and write kinds that reach a RAM node (the others are the
   model's [internal_error] placeholders for unused Sail access kinds) *)
(* [Read_ttw] IS GONE with the A6.7(B) Sail patch (RULING 1 overruled): the
   pinned model has no walk kind, and every read this tree performs -- fetch,
   page walk and data load alike -- arrives as [Read_plain] or one of the
   reserved kinds.  If the de-confliction project restores the patch, this
   list gets [Read_ttw] back, and note the hazard the wildcard creates:
   omitting it costs no error, just a walk silently classified as
   not-reaching-RAM. *)
Definition rk_ram_ok (rk : read_kind) : bool :=
  match rk with
  | Read_plain | Read_ifetch | Read_RISCV_reserved
  | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire => true
  | _ => false
  end.

Definition wk_ram_ok (wk : write_kind) : bool :=
  match wk with
  | Write_plain | Write_RISCV_conditional
  | Write_RISCV_conditional_release
  | Write_RISCV_conditional_strong_release => true
  | _ => false
  end.

Lemma goodmb_read_ram (Dr Dw : register -> bool) (rk : read_kind) (width : Z)
    (addr : SailStdpp.Values.mword 64) (meta : bool) s mm :
  rk_ram_ok rk = true ->
  dev_addr addr = false ->
  bytes_owned mm addr (Z.to_N width) = true ->
  read_bytes s.(mem) addr (Z.to_N width) <> None ->
  goodmb Dr Dw (read_ram rk (Physaddr addr) width meta) s mm = true.
Proof.
  intros Hrk Hdev Hfp Hrb.
  unfold read_ram. cbn match.
  destruct rk; try discriminate Hrk;
    (erewrite gm_bind; [ | apply goodmb_returnm | apply exec_returnm ];
     cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     erewrite gm_MemRead; [ | exact Hdev | exact Hfp ];
     match goal with
     | |- context[read_bytes ?m ?a ?n] =>
         destruct (read_bytes m a n) as [w|] eqn:Hr
     end;
     [ reflexivity | exfalso; exact (Hrb Hr) ]).
Qed.

(* THE SAME BRICK, KEYED ON THE READ'S OWN [exec] FACT.  [goodmb_read_ram]
   asks for [read_bytes <> None]; every caller holds the read's [exec] fact
   instead, and at a SYMBOLIC width the two are not interchangeable by hand --
   [read_bytes]' value index is [8 * Z.to_N width] and the model's is
   [MachineWord.Z_idx (8 * width)], the same number spelled two ways, and the
   error prints two types that look identical.  Reading the non-[None] out of
   the exec fact sidesteps the index entirely, so every width-generic reader
   (the data loads, the 2- and 4-byte fetches) goes through these two. *)
Lemma read_bytes_ne_of_exec_read_ram (rk : read_kind) (width : Z)
    (addr : SailStdpp.Values.mword 64) (meta : bool)
    (r : (SailStdpp.Values.mword (8 * width) * unit)%type) (s s' : mstate) :
  rk_ram_ok rk = true ->
  dev_addr addr = false ->
  exec (read_ram rk (Physaddr addr) width meta) s = Some (r, s') ->
  read_bytes s.(mem) addr (Z.to_N width) <> None.
Proof.
  intros Hrk Hdev He Hnone.
  unfold read_ram in He. cbn match in He.
  destruct rk; try discriminate Hrk;
    (rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)) in He;
     cbn beta zeta in He;
     unfold Defs.sail_mem_read in He; cbn beta zeta in He;
     unfold Defs.bind in He; cbn [Interface.iMon_bind] in He;
     erewrite exec_MemRead in He; [ | exact Hdev ];
     match type of He with
     | context [ read_bytes ?m ?a ?n ] =>
         replace (read_bytes m a n) with (@None (bv (8 * n))) in He
           by (symmetry; exact Hnone)
     end;
     cbn match in He; discriminate He).
Qed.

Lemma goodmb_read_ram_of_exec (Dr Dw : register -> bool) (rk : read_kind)
    (width : Z) (addr : SailStdpp.Values.mword 64) (meta : bool)
    (r : (SailStdpp.Values.mword (8 * width) * unit)%type) (s s' : mstate) mm :
  rk_ram_ok rk = true ->
  dev_addr addr = false ->
  bytes_owned mm addr (Z.to_N width) = true ->
  exec (read_ram rk (Physaddr addr) width meta) s = Some (r, s') ->
  goodmb Dr Dw (read_ram rk (Physaddr addr) width meta) s mm = true.
Proof.
  intros Hrk Hdev Hfp He.
  exact (goodmb_read_ram Dr Dw rk width addr meta s mm Hrk Hdev Hfp
           (read_bytes_ne_of_exec_read_ram rk width addr meta r s s' Hrk Hdev He)).
Qed.

Lemma goodmb_write_ram (Dr Dw : register -> bool) (wk : write_kind) (width : Z)
    (addr : SailStdpp.Values.mword 64)
    (data : SailStdpp.Values.mword (8 * width)) s mm :
  wk_ram_ok wk = true ->
  dev_addr addr = false ->
  bytes_owned mm addr (Z.to_N width) = true ->
  goodmb Dr Dw (write_ram wk (Physaddr addr) width data tt) s mm = true.
Proof.
  intros Hwk Hdev Hfp.
  unfold write_ram. cbn match.
  destruct wk; try discriminate Hwk;
    (erewrite gm_bind; [ | apply goodmb_returnm | apply exec_returnm ];
     cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     cbn [ConcurrencyInterfaceTypes.Mem_write_request_value];
     unfold Defs.bind; cbn [Interface.iMon_bind];
     erewrite gm_MemWrite; [ | exact Hdev | exact Hfp ];
     reflexivity).
Qed.

(* ---------------------------------------------------------------------- *)
(* 8. THE GENERAL BIND CONTEXT -- one lemma instead of a family indexed by  *)
(*    NESTING DEPTH.                                                       *)
(*                                                                         *)
(* Sail's [>>]/[>>=] are LEFT associative, so a straight-line region reads  *)
(* as [bind (bind (bind m g) h) f] and the depth GROWS as a walk descends   *)
(* into a branch's own chain.  A [_nest] lemma per depth is the wrong       *)
(* shape.  What every one of them really needs of its context is the two    *)
(* equations below -- [Phi] takes a [Ret] to the continuation and commutes  *)
(* with a [Next] node -- and EVERY composition of binds satisfies both by   *)
(* CONVERSION, at any depth, so each use discharges them with               *)
(* [reflexivity]:                                                          *)
(*                                                                         *)
(*   erewrite (gm_ctx (fun z => Defs.bind (Defs.bind z g) f) _              *)
(*              ltac:(reflexivity) ltac:(reflexivity) _ _ _ _ _ Hg He).     *)
(*                                                                         *)
(* Three variants, because the driver differs: [gm_ctx] over [exec] in the  *)
(* plain monad, [gm_ctxR] over [execR] in an early-return region, and       *)
(* [gm_cer_ctx] for a region wrapped in [catch_early_return] -- which is    *)
(* the one a THROWING body needs, since [goodmb] refuses an                 *)
(* [ExtraOutcome] node and the wrapper must stay on while the chain is      *)
(* peeled.                                                                 *)
(* ---------------------------------------------------------------------- *)
Lemma gm_ctx_after (Dr Dw : register -> bool) {Y Z : Type}
    (Phi : M Y -> M Z) (G : Y -> M Z)
    (Hret : forall y, Phi (Interface.Ret y) = G y)
    (Hnext : forall (T : Type) (oc : Interface.outcome _ T) (k : T -> M Y),
       Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t)))
    (m : M Y) :
  forall (s s' : mstate) mm (y : Y),
    goodmb Dr Dw m s mm = true ->
    exec m s = Some (y, s') ->
    goodmb Dr Dw (Phi m) s mm = goodmb Dr Dw (G y) s' (mm_after m s mm).
Proof.
  induction m as [y0 | T oc k IH]; intros s s' mm y Hg He.
  - cbn [exec] in He. injection He as <- <-. cbn [mm_after]. by rewrite Hret.
  - rewrite Hnext.
    destruct oc as [ reg ak | reg ak regval | nb rreq | nb wreq | opc
                   | bsz bpa | bar | cop | tlbo | flt | rpa | tst | ten
                   | A ao | gmsg | | | cty | | msg ];
      cbn [goodmb exec mm_after] in Hg, He |- *; try discriminate Hg.
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH _ s s' mm y). }
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH tt _ s' mm y). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He |- *.
      rewrite Hfp. cbn [negb andb].
      destruct (read_bytes s.(mem) (Interface.ReadReq.pa rreq) nb) as [w|];
        [|discriminate Hg2].
      cbn beta iota in He. by apply (IH _ s s' mm y). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He |- *. rewrite Hfp.
      cbn [negb andb]. cbn beta iota in He. by apply (IH (inl None) _ s' _ y). }
    all: first [ by apply (IH tt s s' mm y) | by apply (IH 0%Z s s' mm y) ].
Qed.

Lemma gm_ctxR_after (Dr Dw : register -> bool) {R Y Z : Type}
    (Phi : Defs.monadR R exception Y -> Defs.monadR R exception Z)
    (G : Y -> Defs.monadR R exception Z)
    (Hret : forall y, Phi (Interface.Ret y) = G y)
    (Hnext : forall (T : Type) (oc : Interface.outcome _ T)
                    (k : T -> Defs.monadR R exception Y),
       Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t)))
    (m : Defs.monadR R exception Y) :
  forall (s s' : mstate) mm (y : Y),
    goodmb Dr Dw m s mm = true ->
    execR m s = Some (inr y, s') ->
    goodmb Dr Dw (Phi m) s mm = goodmb Dr Dw (G y) s' (mm_after m s mm).
Proof.
  induction m as [y0 | T oc k IH]; intros s s' mm y Hg He.
  - cbn [execR] in He.
    assert (Hx : y = y0) by congruence. assert (Hs : s' = s) by congruence.
    subst y s'. cbn [mm_after]. by rewrite Hret.
  - rewrite Hnext.
    destruct oc as [ reg ak | reg ak regval | nb rreq | nb wreq | opc
                   | bsz bpa | bar | cop | tlbo | flt | rpa | tst | ten
                   | A ao | gmsg | | | cty | | msg ];
      cbn [goodmb execR mm_after] in Hg, He |- *; try discriminate Hg.
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH _ s s' mm y). }
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH tt _ s' mm y). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He |- *.
      rewrite Hfp. cbn [negb andb].
      destruct (read_bytes s.(mem) (Interface.ReadReq.pa rreq) nb) as [w|];
        [|discriminate Hg2].
      cbn beta iota in He. by apply (IH _ s s' mm y). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He |- *. rewrite Hfp.
      cbn [negb andb]. cbn beta iota in He. by apply (IH (inl None) _ s' _ y). }
    all: first [ by apply (IH tt s s' mm y) | by apply (IH 0%Z s s' mm y) ].
Qed.

Lemma gm_cer_ctx_after (Dr Dw : register -> bool) {R Y : Type}
    (Phi : Defs.monadR R exception Y -> Defs.monadR R exception R)
    (G : Y -> Defs.monadR R exception R)
    (Hret : forall y, Phi (Interface.Ret y) = G y)
    (Hnext : forall (T : Type) (oc : Interface.outcome _ T)
                    (k : T -> Defs.monadR R exception Y),
       Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t)))
    (m : Defs.monadR R exception Y) :
  forall (s s' : mstate) mm (y : Y),
    goodmb Dr Dw m s mm = true ->
    execR m s = Some (inr y, s') ->
    goodmb Dr Dw (Defs.catch_early_return (Phi m)) s mm
    = goodmb Dr Dw (Defs.catch_early_return (G y)) s' (mm_after m s mm).
Proof.
  induction m as [y0 | T oc k IH]; intros s s' mm y Hg He.
  - cbn [execR] in He.
    assert (Hx : y = y0) by congruence. assert (Hs : s' = s) by congruence.
    subst y s'. cbn [mm_after]. by rewrite Hret.
  - rewrite Hnext.
    destruct oc as [ reg ak | reg ak regval | nb rreq | nb wreq | opc
                   | bsz bpa | bar | cop | tlbo | flt | rpa | tst | ten
                   | A ao | gmsg | | | cty | | msg ];
      cbn [goodmb execR mm_after Defs.catch_early_return Defs.try_catch]
        in Hg, He |- *; try discriminate Hg.
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH _ s s' mm y). }
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH tt _ s' mm y). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He |- *.
      rewrite Hfp. cbn [negb andb].
      destruct (read_bytes s.(mem) (Interface.ReadReq.pa rreq) nb) as [w|];
        [|discriminate Hg2].
      cbn beta iota in He. by apply (IH _ s s' mm y). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He |- *. rewrite Hfp.
      cbn [negb andb]. cbn beta iota in He. by apply (IH (inl None) _ s' _ y). }
    all: first [ by apply (IH tt s s' mm y) | by apply (IH 0%Z s s' mm y) ].
Qed.

(* the same three with the map collapsed back to [mm], and with EVERY
   hypothesis a PREMISE rather than an argument: the two shape equations are
   discharged by [reflexivity] at a still-open [G], which only works if they
   are GOALS (an [ltac:(reflexivity)] in argument position runs while [G] is
   an evar -- the durable notes' diverging-[ltac:]-hole trap, and it does
   diverge here). *)
Lemma gm_ctx (Dr Dw : register -> bool) {Y Z : Type}
    (Phi : M Y -> M Z) (G : Y -> M Z)
    (m : M Y) (s s' : mstate) mm (y : Y) :
  (forall y0, Phi (Interface.Ret y0) = G y0) ->
  (forall (T : Type) (oc : Interface.outcome _ T) (k : T -> M Y),
     Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t))) ->
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (y, s') ->
  goodmb Dr Dw (Phi m) s mm = goodmb Dr Dw (G y) s' mm.
Proof.
  intros Hret Hnext Hg He.
  rewrite (gm_ctx_after Dr Dw Phi G Hret Hnext m s s' mm y Hg He).
  exact (goodmb_after_dom Dr Dw m (G y) s s' mm Hg).
Qed.

Lemma gm_ctxR (Dr Dw : register -> bool) {R Y Z : Type}
    (Phi : Defs.monadR R exception Y -> Defs.monadR R exception Z)
    (G : Y -> Defs.monadR R exception Z)
    (m : Defs.monadR R exception Y) (s s' : mstate) mm (y : Y) :
  (forall y0, Phi (Interface.Ret y0) = G y0) ->
  (forall (T : Type) (oc : Interface.outcome _ T)
          (k : T -> Defs.monadR R exception Y),
     Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t))) ->
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr y, s') ->
  goodmb Dr Dw (Phi m) s mm = goodmb Dr Dw (G y) s' mm.
Proof.
  intros Hret Hnext Hg He.
  rewrite (gm_ctxR_after Dr Dw Phi G Hret Hnext m s s' mm y Hg He).
  exact (goodmb_after_dom Dr Dw m (G y) s s' mm Hg).
Qed.

Lemma gm_cer_ctx (Dr Dw : register -> bool) {R Y : Type}
    (Phi : Defs.monadR R exception Y -> Defs.monadR R exception R)
    (G : Y -> Defs.monadR R exception R)
    (m : Defs.monadR R exception Y) (s s' : mstate) mm (y : Y) :
  (forall y0, Phi (Interface.Ret y0) = G y0) ->
  (forall (T : Type) (oc : Interface.outcome _ T)
          (k : T -> Defs.monadR R exception Y),
     Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t))) ->
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr y, s') ->
  goodmb Dr Dw (Defs.catch_early_return (Phi m)) s mm
  = goodmb Dr Dw (Defs.catch_early_return (G y)) s' mm.
Proof.
  intros Hret Hnext Hg He.
  rewrite (gm_cer_ctx_after Dr Dw Phi G Hret Hnext m s s' mm y Hg He).
  exact (goodmb_after_dom Dr Dw m (Defs.catch_early_return (G y)) s s' mm Hg).
Qed.

(* the [liftR] head inside a general context, the shape almost every
   checked-access region presents *)
Lemma gm_cer_ctx_lift (Dr Dw : register -> bool) {R Y : Type}
    (Phi : Defs.monadR R exception Y -> Defs.monadR R exception R)
    (G : Y -> Defs.monadR R exception R)
    (m : M Y) (s s' : mstate) mm (y : Y) :
  (forall y0, Phi (Interface.Ret y0) = G y0) ->
  (forall (T : Type) (oc : Interface.outcome _ T)
          (k : T -> Defs.monadR R exception Y),
     Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t))) ->
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (y, s') ->
  goodmb Dr Dw (Defs.catch_early_return (Phi (Defs.liftR m))) s mm
  = goodmb Dr Dw (Defs.catch_early_return (G y)) s' mm.
Proof.
  intros Hret Hnext Hg He.
  exact (gm_cer_ctx Dr Dw Phi G (Defs.liftR m) s s' mm y Hret Hnext
           (goodmb_liftR Dr Dw m s mm Hg) (goodmb_liftR_execR m s s' y He)).
Qed.

Lemma gm_ctx_lift (Dr Dw : register -> bool) {R Y Z : Type}
    (Phi : Defs.monadR R exception Y -> Defs.monadR R exception Z)
    (G : Y -> Defs.monadR R exception Z)
    (m : M Y) (s s' : mstate) mm (y : Y) :
  (forall y0, Phi (Interface.Ret y0) = G y0) ->
  (forall (T : Type) (oc : Interface.outcome _ T)
          (k : T -> Defs.monadR R exception Y),
     Phi (Interface.Next oc k) = Interface.Next oc (fun t => Phi (k t))) ->
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (y, s') ->
  goodmb Dr Dw (Phi (Defs.liftR m)) s mm = goodmb Dr Dw (G y) s' mm.
Proof.
  intros Hret Hnext Hg He.
  exact (gm_ctxR Dr Dw Phi G (Defs.liftR m) s s' mm y Hret Hnext
           (goodmb_liftR Dr Dw m s mm Hg) (goodmb_liftR_execR m s s' y He)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 8b. THE SHAPE OBLIGATIONS ARE DISCHARGED STRUCTURALLY, NEVER BY           *)
(*     [reflexivity].                                                       *)
(*                                                                         *)
(* [Phi (Next oc k) = Next oc (fun t => Phi (k t))] IS a conversion, and    *)
(* closing it with [reflexivity] does not come back: the context [Phi]      *)
(* carries the region's whole tail -- for [pmpCheck] that is a              *)
(* [foreach_ZM_up'] over 64 entries under an [Acc] guard -- and the         *)
(* conversion checker unfolds it rather than noticing the two sides differ  *)
(* only at the head.  (Measured: >30 s, killed, on the FIRST peel of        *)
(* [pmpCheck].)  The two node equations below are the same conversion at a  *)
(* GENERIC term, where it costs nothing, and [gm_shape] closes the          *)
(* obligation by rewriting with them instead -- syntactic matching, so the  *)
(* tail is never looked at.                                                 *)
(* ---------------------------------------------------------------------- *)
Lemma mbind_Ret {E X Y} (x : X) (f : X -> Defs.monad E Y) :
  Defs.bind (Interface.Ret x) f = f x.
Proof. reflexivity. Qed.

Lemma mbind_Next {E X Y} {T : Type} (oc : Interface.outcome _ T)
    (k : T -> Defs.monad E X) (f : X -> Defs.monad E Y) :
  Defs.bind (Interface.Next oc k) f
  = Interface.Next oc (fun t => Defs.bind (k t) f).
Proof. reflexivity. Qed.

Lemma mbind0_Ret {E Y} (x : unit) (n : Defs.monad E Y) :
  Defs.bind0 (Interface.Ret x) n = n.
Proof. by destruct x. Qed.

Lemma mbind0_Next {E Y} {T : Type} (oc : Interface.outcome _ T)
    (k : T -> Defs.monad E unit) (n : Defs.monad E Y) :
  Defs.bind0 (Interface.Next oc k) n
  = Interface.Next oc (fun t => Defs.bind0 (k t) n).
Proof. reflexivity. Qed.

Ltac gm_shape :=
  intros ? ? ?;
  repeat (progress (rewrite ?mbind_Ret; rewrite ?mbind0_Ret;
                    rewrite ?mbind_Next; rewrite ?mbind0_Next; cbn beta));
  reflexivity.

(* ---------------------------------------------------------------------- *)
(* 9. THE PEEL TACTICS over a general context.  Each takes the HEAD as an   *)
(*    argument (the [goodb]/[goodmb] habit: a bind equation must be GIVEN   *)
(*    its left operand, and a hand-retyped copy does not match -- so the    *)
(*    head is the one from the [exec] fact, and [pattern] abstracts THAT    *)
(*    occurrence out of the goal, at whatever nesting depth it sits).       *)
(*                                                                         *)
(*    [gmx h Hg He]   -- plain monad, [exec]-driven.                        *)
(*    [gmxR h Hg He]  -- early-return monad, [execR]-driven.                *)
(*    [gmxc h Hg He]  -- inside [catch_early_return], [execR]-driven.       *)
(*    [gmxl h Hg He]  -- ditto with the head under a [liftR], [exec]-driven *)
(*                       (the shape a checked-access region presents).      *)
(*    [gmxlR h Hg He] -- a [liftR] head in a plain early-return context.    *)
(* ---------------------------------------------------------------------- *)
Ltac gmx Hg He :=
  lazymatch type of Hg with
  | goodmb _ _ ?h _ _ = true =>
      lazymatch goal with
      | |- goodmb ?dr ?dw ?T ?s ?mm = _ =>
          let P := eval pattern h at 1 in T in
          lazymatch P with
          | ?F _ =>
              erewrite (gm_ctx dr dw F (fun y0 => F (Interface.Ret y0))
                          h s _ mm _);
                [ cbn beta | intros ?; reflexivity | gm_shape
                  | exact Hg | exact He ]
          end
      end
  end.

Ltac gmxR Hg He :=
  lazymatch type of Hg with
  | goodmb _ _ ?h _ _ = true =>
      lazymatch goal with
      | |- goodmb ?dr ?dw ?T ?s ?mm = _ =>
          let P := eval pattern h at 1 in T in
          lazymatch P with
          | ?F _ =>
              erewrite (gm_ctxR dr dw F (fun y0 => F (Interface.Ret y0))
                          h s _ mm _);
                [ cbn beta | intros ?; reflexivity | gm_shape
                  | exact Hg | exact He ]
          end
      end
  end.

Ltac gmxc Hg He :=
  lazymatch type of Hg with
  | goodmb _ _ ?h _ _ = true =>
      lazymatch goal with
      | |- goodmb ?dr ?dw (Defs.catch_early_return ?T) ?s ?mm = _ =>
          let P := eval pattern h at 1 in T in
          lazymatch P with
          | ?F _ =>
              erewrite (gm_cer_ctx dr dw F (fun y0 => F (Interface.Ret y0))
                          h s _ mm _);
                [ cbn beta | intros ?; reflexivity | gm_shape
                  | exact Hg | exact He ]
          end
      end
  end.

Ltac gmxl Hg He :=
  lazymatch type of Hg with
  | goodmb _ _ ?h _ _ = true =>
      lazymatch goal with
      | |- goodmb ?dr ?dw (Defs.catch_early_return ?T) ?s ?mm = _ =>
          lazymatch T with
          | context [ @Defs.liftR ?A ?R ?E h ] =>
              let P := eval pattern (@Defs.liftR A R E h) at 1 in T in
              lazymatch P with
              | ?F _ =>
                  erewrite (gm_cer_ctx_lift dr dw F
                              (fun y0 => F (Interface.Ret y0)) h s _ mm _);
                    [ cbn beta | intros ?; reflexivity
                      | gm_shape | exact Hg | exact He ]
              end
          end
      end
  end.

Ltac gmxlR Hg He :=
  lazymatch type of Hg with
  | goodmb _ _ ?h _ _ = true =>
      lazymatch goal with
      | |- goodmb ?dr ?dw ?T ?s ?mm = _ =>
          lazymatch T with
          | context [ @Defs.liftR ?A ?R ?E h ] =>
              let P := eval pattern (@Defs.liftR A R E h) at 1 in T in
              lazymatch P with
              | ?F _ =>
                  erewrite (gm_ctx_lift dr dw F
                              (fun y0 => F (Interface.Ret y0)) h s _ mm _);
                    [ cbn beta | intros ?; reflexivity
                      | gm_shape | exact Hg | exact He ]
              end
          end
      end
  end.
