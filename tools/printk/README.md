Generators for the repetitive parts of `Xv6/ProofPrintk.lean`: the twelve
simple directive arms (`gen_arms.py`), and the dispatch chain, the `%p`/`%s`
arms, the `%` turn, the walk and the entry (`gen_rest.py`).  Each writes Lean
text to the file named on the command line; the output was pasted into the
proof file once and is maintained there (the scripts document the shape).
