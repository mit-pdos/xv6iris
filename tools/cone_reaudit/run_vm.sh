#!/bin/bash
# Kernel-term cone of the three Rocq top theorems (notes/cone_reaudit.md).
# Run from this repository's root, on a machine with the Rocq toolchain:
#   ROCQ_TREE=<built rocq-branch checkout> OUT=<dir> bash tools/cone_reaudit/run_vm.sh
# Needs the Rocq tree built (the audit used 1900b8a43).  Writes
# $OUT/cone_edges_{P,S,U}.txt, $OUT/cone_globidx.tsv and $OUT/cone_globreach.txt;
# copy them to scratch/cone/ (edges_X.txt, globidx.tsv, globreach.txt) and run
# the local analysis (see the note).
#
# The plugin `depdump` walks kernel terms (types AND bodies, opaque proofs
# forced, sealed modules read through their implementation as Print
# Assumptions does), so it sees every instance / canonical-structure / hint /
# obligation the elaborator put in a term -- what the glob walk cannot.
set -e
D=$PWD/tools/cone_reaudit
( cd "$D/depdump" && ocamlfind ocamlopt -rectypes -thread -package rocq-runtime.vernac -shared -o depdump.cmxs depdump.ml )
export OCAMLPATH=$D:$OCAMLPATH
R=${ROCQ_TREE:?set ROCQ_TREE to a built rocq-branch checkout}
OUT=${OUT:-$PWD}; export ROCQ_TREE OUT
cd $R/iris
run1() {
  mkdir -p /tmp/cone_$1 && cp $D/depsAll.v /tmp/cone_$1/
  DEPDUMP_ROOTS=$2 DEPDUMP_OUT=$OUT/cone_edges_$1.txt timeout 7200 \
    coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -R ../user-rocq User \
      -w -notation-overridden /tmp/cone_$1/depsAll.v
}
run1 P xv6iris.ProofUser.UserProof.wp_user_exec_closed &
run1 S xv6iris.SystemAdequacy.xv6_fs_adequacy_xv6Σ &
run1 U xv6iris.UInitUnion.union_adequacy_closed &
wait
python3 $D/globidx.py $OUT/cone_globidx.tsv
python3 $D/globreach.py
