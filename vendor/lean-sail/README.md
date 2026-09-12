# vendored lean-sail (free-monad V1 interface)

Copy of https://github.com/rems-project/lean-sail at commit
`17f8a54a72276e2c8281300c49d2df94bc18b873` (2026-09-02), with:

- `lean-toolchain` bumped to v4.32.2 (the toolchain iris-lean needs);
- `Sail/ConcurrencyInterfaceV1.lean` rewritten so that `PreSailM` is a *free
  monad* over an explicit `Outcome` event type (register/memory/trace events)
  instead of an `EStateM` state monad -- see the header of that file.  The
  primitive surface used by Sail's Lean backend is unchanged;
- `Sail/Sail.lean`: `main_of_sail_main` runs the model through the new
  reference interpreter (`PreSailM.interp`) and takes a `PaToNat` instance.

Everything else is verbatim upstream.
