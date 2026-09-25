(* ====================================================================== *)
(* PipeAssumptions.v -- THE ASSUMPTION AUDIT of the APPLICATION theorem.   *)
(*                                                                        *)
(* [Print Assumptions] on [UInitPipeAdequacy.pipe_adequacy_pipeSigma_final]: *)
(* safety of the whole machine plus the console trace property for the     *)
(* application of claude-notes/design/pipes-general.md -- the user types   *)
(* `echo w1 ... wn' and `echo w1 ... wn | cat | ... | cat' lines (any       *)
(* number of cats) at the console of an unmodified xv6, each line as a     *)
(* burst if they like, and nothing but the line and sh's own diagnostics   *)
(* ever reaches the console.  The claim is born at the N-stage line model  *)
(* [PipesDisc.pipes_lmE] (cut C8).                                         *)
(*                                                                        *)
(* WHY A SEPARATE FILE beside [SystemAssumptions.v], [TreeAssumptions.v]   *)
(* and [FileAssumptions.v]: no two of the cones contain each other.  The   *)
(* system theorem is the chain at the TRIVIAL application and names no     *)
(* user program; this one walks the whole [Uk*]/[USh*]/[UInit*]/[UEcho*]/  *)
(* [UCat*] program tier and the stage ([PipesDisc]/[PipeOutN]/[PipesOut]/  *)
(* [PipesLinks]/[AppPipe]).  A grep for [Axiom] and [Admitted] cannot see  *)
(* a sealed [Spec*] module [Parameter]; [Print Assumptions] is the check   *)
(* that does.                                                              *)
(*                                                                        *)
(* EXPECT EXACTLY FOURTEEN, and the split matters:                         *)
(*                                                                        *)
(*   1  [functional_extensionality_dep]                                    *)
(*   2  [xv6iris_extras.resv_matches] / [_is_valid] -- the LR/SC           *)
(*      reservation predicates, this project's own [Parameter]s            *)
(*  11  Rocq's [PrimString]/[PrimInt63] primitives                         *)
(*      ([PrimString.string]/[.get]/[.cat]/[.length], [PrimInt63.int]/     *)
(*      [.eqb]/[.sub]/[.lsl]/[.lsr]/[.land]/[.lor])                        *)
(*                                                                        *)
(* THAT IS THE SYSTEM THEOREM'S THIRTEEN PLUS [PrimString.length], the     *)
(* byte-count every hex-imported binary blob is decoded by                 *)
(* ([PStringBytes.pstring_hex_length]).  ANYTHING ELSE -- and in           *)
(* particular any [Spec*]/[Link*] module [Parameter] -- IS A REGRESSION.   *)
(* The theorem's binder list is the complementary check (a premise never   *)
(* appears here); it holds three hardware facts about the initial state    *)
(* and nothing else.                                                       *)
(*                                                                        *)
(* WHY IT IS OUT OF [iris/_CoqProject], same as its siblings: [Print       *)
(* Assumptions] re-cooks every opaque proof term in the transitive cone.   *)
(* Compiled by `make audit-pipe` / `make audit-pipe-only` and by CI; the   *)
(* commented row in [iris/_CoqProject] tells the coverage checker the file *)
(* is out of the build ON PURPOSE.  ONE print: consecutive calls share     *)
(* nothing.                                                                *)
(*                                                                        *)
(* THE OTHER HALF OF THE TRUSTED BASE -- what a reader must READ for the   *)
(* statement to MEAN what they think -- is [LineModel.v]'s [lm_disc] and   *)
(* [lm_good_out] and [PipesDisc.v]'s model [pipes_lmE] ([pl_of],           *)
(* [plalt_ok], [plcont], [line_blocks], [pl_merge]): they ARE the          *)
(* specification.                                                          *)
(* See tools/tcb/ and claude-notes/design/app-pipe.md.                     *)
(* ====================================================================== *)
Require Import UInitPipeAdequacy.

Print Assumptions pipe_adequacy_pipeΣ_final.

(* ---------------------------------------------------------------------- *)
(* FRONTIER (cut C9e-dec, design/union.md review S2): the union           *)
(* discipline's decider [UnionDecU.lm_disc_ulmU_dec], which the union     *)
(* ledger's taint counter will case on, is in no anchor's cone until the  *)
(* union application's switch (C9g).  Its print must show only axioms     *)
(* already counted above.  DELETE this block when the union anchor lands. *)
(* ---------------------------------------------------------------------- *)
Require Import UnionDecU.

Print Assumptions lm_disc_ulmU_dec.

(* ---------------------------------------------------------------------- *)
(* FRONTIER (cut C9e', design/union.md section 3): the union claim, its   *)
(* ledger and its link and read records -- [UnionOut.union_led_rx] /      *)
(* [_tx] / [_pow] / [_phi] (the ledger's steps, the counter casing on    *)
(* [lm_disc_ulmU_dec]), [UnionOut.pblkU_ecl_holds] (the N-writer family's *)
(* obligation at the claim) and [UnionReadInst.union_read_inst] (the read *)
(* record over [UnionLinkInst.union_link_inst] and [UnionLinks]) -- are  *)
(* in no anchor's cone until the switch (C9g).  ONE print over their      *)
(* tuple; it must show only axioms already counted above.  DELETE this    *)
(* block when the union anchor lands.                                     *)
(* ---------------------------------------------------------------------- *)
Require Import UnionOut UnionReadInst.

Definition union_c9e_frontier :=
  (@union_led_rx, @union_led_tx, @union_led_pow, @union_led_phi,
   @pblkU_ecl_holds, @union_read_inst).

Print Assumptions union_c9e_frontier.

(* ---------------------------------------------------------------------- *)
(* FRONTIER (cut C9f2, design/union.md section 3): the union's shell round *)
(* with NO premise -- [UShUPipes.sh_round_holds_union_closed], the file     *)
(* line shapes and echo with the pipelines at either producer ([echo ws |  *)
(* cat^n] and [cat f | cat^n], the deed through node 0) at the pipeline's  *)
(* own terminal and committed shapes -- is in no anchor's cone until the   *)
(* switch (C9g).  Its print must show only axioms already counted above.   *)
(* DELETE this block when the union anchor lands.                          *)
(* ---------------------------------------------------------------------- *)
Require Import UShUPipes.

Print Assumptions sh_round_holds_union_closed.
