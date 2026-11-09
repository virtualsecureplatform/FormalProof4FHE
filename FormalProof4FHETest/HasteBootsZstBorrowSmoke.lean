module
import FormalProof4FHE.HasteBoots.NativeRecordCallValues
import FormalProof4FHE.HasteBoots.NativeRecordIncomingReference
namespace FormalProof4FHETest.HasteBootsZstBorrowSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (world : NativeReferenceMachine.State) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) :
    NativeZstBorrow.issue world address =
      .value (.reference false ⟨world.nextTag⟩ 0) (NativeZstBorrow.granted world address) :=
  NativeZstBorrow.issue_complete world address nonzero

example (world : NativeReferenceMachine.State) :
    NativeZstBorrow.issue world 0 = .invalid (NativeZstBorrow.placed world 0) := NativeZstBorrow.issue_null world

example (world : NativeReferenceMachine.State) (address : NativeWord64Memory.Word) :
    (NativeZstBorrow.issue world address).world.pointers.heap = world.pointers.heap := NativeZstBorrow.issue_heap world address

example (world : NativeReferenceMachine.State) :
    NativeZstReference.decode (NativeZstBorrow.granted world 1) 0 =
      some (.reference false ⟨world.nextTag⟩ 0) := NativeZstBorrow.granted_decoded world 1

example : NativeReferenceMachine.Reachable (NativeZstBorrow.granted NativeReferenceMachine.empty 1) :=
  NativeZstBorrow.granted_reachable _ 1 (by decide) .empty

example (world : NativeReferenceMachine.State) :
    evalZstBorrow ⟨[.record 1 (.scalar .unit)],[.live (some (.record 1 (.scalar .unit)))],world⟩ 0 2 1 = .invalid world := by
  simp [evalZstBorrow,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

example (world : NativeReferenceMachine.State) :
    evalZstBorrow ⟨[.record 1 (.scalar .unit)],[.live (some .uninit)],world⟩ 0 1 1 = .invalid world := by
  simp [evalZstBorrow,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.complete]

example (world : NativeReferenceMachine.State) :
    evalZstBorrow ⟨[.record 1 (.scalar .unit)],[.live (some (.record 1 (.scalar .unit)))],world⟩ 0 1 0 =
      .invalid (NativeZstBorrow.placed world 0) := by
  simp [evalZstBorrow,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,NativeZstBorrow.issue_null]

example (world : NativeReferenceMachine.State) :
    evalZstBorrow ⟨[.record 1 (.scalar .unit)],[.live (some (.record 1 (.scalar .unit)))],world⟩ 0 1 1 =
      .value (.scalar (.reference false ⟨world.nextTag⟩ 0))
        ⟨[.record 1 (.scalar .unit)],[.live (some (.record 1 (.scalar .unit)))],NativeZstBorrow.granted world 1⟩ := by
  simp [evalZstBorrow,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,NativeZstBorrow.issue_complete _ 1 (by decide)]

example (frame : Frame) (index tag : Nat) (address : NativeWord64Memory.Word) :
    NativeHeapFrame.Runs frame.world (evalZstBorrow frame index tag address).world := evalZstBorrow_heap_projects frame index tag address

example (frame : Frame) (index tag : Nat) (address : NativeWord64Memory.Word) :
    NativeIncomingReference.Preserves frame.world (evalZstBorrow frame index tag address).world :=
  evalZstBorrow_incoming_projects frame index tag address
end FormalProof4FHETest.HasteBootsZstBorrowSmoke
