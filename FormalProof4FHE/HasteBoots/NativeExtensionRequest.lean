module

public import FormalProof4FHE.HasteBoots.NativeExtensionDescriptor
public import FormalProof4FHE.HasteBoots.NativeFieldAssembly
import all Init.Data.String.Defs

@[expose] public section

/-!
# Online native extension challenge requests

The successful native descriptor path appends the extension-kind frame and
the complete multiplication-table descriptor, then collects count*degree
canonical coefficients. Rejections and resumption use the existing online
collector and retain its raw receipt bytes. Pure typed assembly is separate.
The checked entry models degree/64-bit size prechecks. Rust field storage,
cache locking/failure behavior, and execution refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeExtensionRequest

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript appendBytes utf8)
open OracleProgram (Program run)
open NativeFieldVector (Status stateOf resume)

/-- This pure prelude binds the canonical binomial multiplication table. -/
def prepare (transcript : Transcript) (degree w : ℕ) : Transcript :=
  appendBytes (appendBytes transcript (utf8 "field challenge kind") (utf8 "extension vector"))
    (utf8 "extension basis") (NativeExtensionDescriptor.descriptor degree w)

/-- The successful prelude contributes two exact kind-1 frames, in native order. -/
theorem prepare_input (transcript : Transcript) (degree w : ℕ) :
    (prepare transcript degree w).input = transcript.input ++ TranscriptFrame.encodeMany
      [⟨1, utf8 "field challenge kind", utf8 "extension vector"⟩,
       ⟨1, utf8 "extension basis", NativeExtensionDescriptor.descriptor degree w⟩] := by
  simp only [prepare, appendBytes, NativeTranscript.absorb, TranscriptFrame.encodeMany,
    List.append_nil, List.append_assoc]

def request (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) : Program Status :=
  NativeFieldVector.request p fuel (prepare transcript degree w) label (count * degree)

/-- Native count arithmetic is 64-bit in the selected machine model.
Failure returns before any transcript mutation or oracle execution. -/
def checkedRequest (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) :
    Option (Program Status) :=
  if degree = 0 then none
  else if count * degree < TranscriptFrame.lengthLimit then
    some (request p degree w fuel transcript label count)
  else none

theorem checked_zero_degree (p w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) :
    checkedRequest p 0 w fuel transcript label count = none := by simp [checkedRequest]

theorem checked_overflow (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ)
    (overflow : TranscriptFrame.lengthLimit ≤ count * degree) :
    checkedRequest p degree w fuel transcript label count = none := by
  simp [checkedRequest, Nat.not_lt.mpr overflow]

theorem checked_valid (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ)
    (positive : 0 < degree) (fits : count * degree < TranscriptFrame.lengthLimit) :
    checkedRequest p degree w fuel transcript label count =
      some (request p degree w fuel transcript label count) := by
  simp [checkedRequest, Nat.ne_of_gt positive, fits]

theorem request_count (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) (world : World) :
    let result := stateOf (run (request p degree w fuel transcript label count) world).run.1
    result.remaining + result.values.length = count * degree :=
  NativeFieldVector.request_count p fuel (prepare transcript degree w) label (count * degree) world

theorem request_values_valid (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ)
    (world : World) :
    NativeFieldVector.ValuesValid p (stateOf (run (request p degree w fuel transcript label count) world).run.1) :=
  NativeFieldVector.request_values_valid p fuel (prepare transcript degree w) label (count * degree) world

theorem request_start (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ)
    (world : World) :
    (run (request p degree w fuel transcript label count) world).run.2.head? =
      some (.start (NativeTranscript.beginField (prepare transcript degree w) label p (count * degree)).run.1.pending.input) := by
  rw [request, NativeFieldVector.run_request]
  rfl

/-- Zero requested elements still bind the descriptor and emit the field's
start plus empty-prefix receipt. It is not an identity transcript operation. -/
theorem request_zero (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (world : World) :
    (run (request p degree w fuel transcript label 0) world).run =
      let phase := (NativeTranscript.beginField (prepare transcript degree w) label p 0).run.1
      let receipt := (NativeTranscript.finishField world phase).run
      (.finished (NativeFieldVector.initial phase 0) receipt.1, [.start phase.pending.input] ++ receipt.2) := by
  simpa only [request, zero_mul] using
    NativeFieldVector.request_zero p fuel (prepare transcript degree w) label world

/-- Finished native extension requests supply exactly the original canonical
coefficient at every typed basis coordinate. Pure assembly adds no queries. -/
theorem finished_coordinate {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel count : ℕ)
    (transcript : Transcript) (label : Input) (world : World)
    (state : NativeFieldVector.State) (result : Transcript)
    (finished : (run (request p degree w fuel transcript label count) world).run.1 = .finished state result)
    (element : Fin count) (coordinate : Fin degree) :
    let length := NativeFieldVector.request_finished_length p fuel (prepare transcript degree w) label
      (count * degree) world state result finished
    (basis.equivFun (NativeFieldAssembly.assemble basis count state.values length element) coordinate).val =
      state.values[(finProdFinEquiv (element, coordinate)).val]'(by
        have _length := NativeFieldVector.request_finished_length p fuel (prepare transcript degree w) label
          (count * degree) world state result finished
        omega) :=
  NativeFieldAssembly.finished_request_coordinate basis fuel count (prepare transcript degree w)
    label world state result finished element coordinate

/-- With the same prior transcript input, extension and prime requests cannot
alias, even if their labels, moduli and requested counts differ. This is not
a claim of freshness against arbitrary earlier oracle queries. -/
theorem prime_domain_separated (transcript : Transcript) (degree w p q count primeCount : ℕ)
    (label primeLabel : Input) :
    (NativeTranscript.beginField (prepare transcript degree w) label p (count * degree)).run.1.pending.input ≠
    (NativeTranscript.beginField
      (appendBytes transcript (utf8 "field challenge kind") (utf8 "prime vector")) primeLabel q primeCount).run.1.pending.input := by
  intro same
  let extensionFrame : TranscriptFrame.Frame := ⟨1, utf8 "field challenge kind", utf8 "extension vector"⟩
  let primeFrame : TranscriptFrame.Frame := ⟨1, utf8 "field challenge kind", utf8 "prime vector"⟩
  change (((transcript.input ++ TranscriptFrame.encode extensionFrame) ++
    TranscriptFrame.encode ⟨1, utf8 "extension basis", NativeExtensionDescriptor.descriptor degree w⟩) ++
    TranscriptFrame.encode ⟨4, label, TranscriptFrame.littleEndian 16 p ++ TranscriptFrame.littleEndian 8 (count * degree)⟩) =
    (transcript.input ++ TranscriptFrame.encode primeFrame) ++
    TranscriptFrame.encode ⟨4, primeLabel, TranscriptFrame.littleEndian 16 q ++ TranscriptFrame.littleEndian 8 primeCount⟩ at same
  simp only [List.append_assoc] at same
  have tailEq := List.append_cancel_left same
  have frameEq := (TranscriptFrame.boundary_unique extensionFrame primeFrame
    (by unfold TranscriptFrame.Valid; decide +kernel)
    (by unfold TranscriptFrame.Valid; decide +kernel) _ _ tailEq).1
  have different : extensionFrame.message ≠ primeFrame.message := by decide +kernel
  exact different (congrArg TranscriptFrame.Frame.message frameEq)

/-- Resumption does not repeat the descriptor prelude or a completed receipt. -/
theorem request_add (p degree w first extra : ℕ) (transcript : Transcript) (label : Input) (count : ℕ)
    (world : World) :
    (run (request p degree w (first + extra) transcript label count) world).run =
      let earlier := (run (request p degree w first transcript label count) world).run
      let later := (run (resume p extra earlier.1) world).run
      (later.1, earlier.2 ++ later.2) :=
  NativeFieldVector.request_add p first extra (prepare transcript degree w) label (count * degree) world

theorem request_replay (p degree w fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) :
    ObservationReplay.Replayable (run (request p degree w fuel transcript label count)) :=
  OracleProgram.run_replay _

/-- Selected native challenge extensions, separately from the PCS symbol fields. -/
def goldilocks (fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) : Option (Program Status) :=
  checkedRequest NativeFields.goldilocksModulus 3 7 fuel transcript label count

def babyBear (fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) : Option (Program Status) :=
  checkedRequest NativeFields.babyBearModulus 6 31 fuel transcript label count

end FormalProof4FHE.HasteBoots.NativeExtensionRequest
