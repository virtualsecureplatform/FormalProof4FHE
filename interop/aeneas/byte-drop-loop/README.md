# Byte drop operation models and retained original loop

The separate [typed loop profile](../byte-loop-body/README.md) now interprets
the retained slice body with explicit backedge cleanup and proves its traversal
simulation. This primitive/retention profile retains its narrower scope.

This profile checks two Lean operation models and retains a fresh original
byte-slice drop probe. It does **not** yet interpret the original loop or prove
Rust lifetime or compiler correspondence. A successful gate establishes the
operation-model checks and source retention separately.

`NativeByteSliceIndex` checks a mutable slice's metadata against its resident
lease and resolves actual reference/raw registers by complete identity. It
checks bounds, computes the child address, executes a closed raw `withAddress`
operation and then a checked one-byte reborrow. A failed second operation keeps
the prepared raw register and its unchanged heap. Successful results identify
the fresh tag, exact child lease, parent, byte address and inherited provenance.
Raw-pointer recovery selects a complete existing pointer from the registers.

`NativeByteDropTraversal` composes the operations observed in a source iteration:
a whole-slice reborrow, byte indexing, raw-pointer recovery and explicit checked
temporary-lease cleanup. Its operational relation has stop, failed-iteration and
next-iteration rules. The evaluator and relation agree and are deterministic.
Termination uses the decreasing original slice extent minus cursor; `run` takes
no execution budget. Cursor bounds imply that the source-shaped wrapping usize
increment does not wrap. Every result projects to real reference-machine runs
and preserves the byte heap, including failure prefixes. A normally completed
traversal stops at the original extent. Physical deallocation remains a separate
checked operation, and the input parent lease remains resident.

The original probe has five retained structured bodies: the probe,
`core::ptr::slice_from_raw_parts_mut`, `core::ptr::drop_in_place`, a generated
`core::ptr::drop_glue` wrapper and slice drop glue. Charon marks the generated
wrapper `Foreign` despite retaining a structured body; that flag is retained,
not changed to `Transparent`. The full original declarations, types, traits,
files and compiler-evaluated byte layout constants are in `Retained.json`.

The source checker validates the original equality/break guard, mutable
whole-slice metadata binding, mutable byte `Index` intrinsic and its operands,
reference-to-raw dataflow, wrapping increment by one, continue target, and
initial metadata/zero counter. It compares complete retained source snapshots
and requires the existing finite source reifier to reject this unsupported
whole-body profile. It supplies no function-name replacement for drop glue.
The probe explicitly uses `-Cdebug-assertions=no`; its ordinary sysroot, precise
and desugared drops, retained allocator policy and target layout are checked.

Reproduce with the frozen tool receipt:

```sh
scripts/check-hasteboots-byte-drop-primitives \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The typed loop profile supplies a scoped local/control simulation for the
retained slice body. Rust lifetime/alias correspondence for its explicit
backedge cleanup, region/ABI/caller refinement, the pointer/drop wrappers,
whole `Vec` destructor and allocator path remain open. Compiler correctness,
native execution costs and the final security theorem remain unproved. No
physical-work law or cryptographic conclusion is supplied here.
