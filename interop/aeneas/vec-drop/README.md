# Original resident Vec destruction

This profile composes original `alloc::vec::Vec::drop_glue`, `alloc::vec::drop`,
foreign-classified retained `core::ptr::drop_glue`, the original mutable byte
loop, and the earlier RawVec destructor/deallocation chain. Entry selects an
existing exclusive 24-byte, alignment-eight Vec receiver. It supplies neither
pointer provenance nor a fresh reference tag. The by-value `release(Vec<u8>)`
fixture entry and native Vec construction are not interpreted here.

`NativeVecReference` validates the resident complete reference and pointer
identities, reads the data pointer from byte offset eight through pointer shadow,
and reads the length as an aligned word at offset sixteen. Field reads use the
exclusive parent directly; they do not copy its reference value. Whole-Vec and
RawVec-field mutable borrows execute address derivation and checked exclusive
loan issuance, with extents 24/16 and alignment eight. The RawVec field starts
at byte offset zero. Failed issuance retains its actual address prefix.

The aggregate interpreter now supports these operations, pointer/length parts
construction, and mutable byte-slice borrowing. Parts construction preserves the
complete pointer and adds only the evaluated length. The slice borrow executes
actual checked issuance over that byte extent. Uninitialized data, invalid
origins, conflicting loans and out-of-allocation extents reject.

`NativeRecordDropCalls` composes actual aggregate frames with the unbounded
`NativeByteLoopLLBC` execution relation. Callee arguments, moves, return slots,
unwind and rejected/unsupported prefixes are preserved. A translated call is
wrapped with explicit ghost cleanup covering argument preparation and that call;
normal continuation closes only loans born within that scope. It preserves
incoming loans and local slots. Terminal failure/unwind prefixes are retained.
The normal-return callee cleanup remains separate. These cleanup points are not
proved to coincide with Rust lifetime endings.

The source gate retains classifications, validates nominal projection owners,
receiver/layout geometry, metadata, regions, pointer cast, the parts intrinsic
and call signatures. The closed parts intrinsic's original UB edge is checked
and retained as data; it cannot unwind in this logical model. Both retained
abort causes reject in the model, while their original labels remain in the
source snapshot. Reference/fat-pointer extents are logical, not a native ABI
representation theorem.

Nine Vec-reference and seven composition theorems establish checked execution,
reachable states, minted-reference identity, borrow heap preservation and scope
projection. Three aggregate helper theorems extend the existing interpreter
projections. Fifty-one declaration guards and 28 model regressions cover these
operations and scope behavior. The source profile has fourteen loop theorems
(including universal execution simulation and agreement) and five composition
and classification theorems. The traversal is not truncated by fuel or a sample
length. The execution examples still cover only specific caller outcomes; a
universal complete destructor characterization remains open.

Eight source examples check a three-byte traversal followed by deallocation,
zero capacity preserving the heap, zero length with nonzero capacity still
freeing the buffer, an oversized slice rejecting before its data loan, wrong
entry selectors and retained foreign classification. Successful examples also
assert an actual unit return; the rejection example asserts an invalid outcome.
The three-byte execution retains only the incoming loan and removes one data
allocation. The rejected oversized slice preserves its earlier whole-Vec loan
and heap. Invalid-entry examples are defensive model checks, not evidence that
those inputs are valid Rust values.

Run:

```sh
scripts/check-hasteboots-vec-drop \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

Fresh extraction passed 341 dependency audits and 69 rejecting controls. Changing
the constructed byte-slice extent to zero changes generated code, retains the
free, and removes six iteration loans from the three-byte example. The original
RawVec drop and deallocation gates passed again with 290/294 audits and 44/24
rejection controls. See `regression.json` for final receipts and check results.

Next prove universal destructor outcomes and connect native construction,
carrier/reference/stack/layout/ABI, compiler and lifetime refinement. Retained
precondition helper bodies and the external allocator still require refinement.
Physical attacker work, the complete application reduction and the final
expected-work security theorem remain open. This profile supplies no native
constructor acceptance or physical-work certificate.
