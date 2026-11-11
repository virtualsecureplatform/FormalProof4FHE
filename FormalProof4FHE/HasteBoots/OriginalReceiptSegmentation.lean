module
public import FormalProof4FHE.HasteBoots.ReceiptLabelSegmentation
public import FormalProof4FHE.HasteBoots.LookupInitialReceipt
public import FormalProof4FHE.HasteBoots.OriginalLookupReceiptOrder
public import FormalProof4FHE.HasteBoots.OrderedReceiptMatching
@[expose] public section

/-! Native original execution produces a receipt view whose job groups and
EQ suffix are uniquely recoverable across equal prelude inputs. The initial
one-receipt count comes from the actual typed-child initializer. -/
namespace FormalProof4FHE.HasteBoots.OriginalReceiptSegmentation
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open ReceiptFrameView (frames frame)
noncomputable section

structure View where
  transcript : NativeTranscript.Transcript
  earlier : List Frame
  groups : List (List Frame)
  equality : List Frame
  sequence : frames transcript.input = earlier ++ groups.flatten ++ equality
  initialCount : earlier.length = 1
  groupLabels : ∀ group ∈ groups, ReceiptLabelSegmentation.Group group
  equalityLabels : ∀ entry ∈ equality, entry.label = NativeLookupEquality.pointLabel

private theorem flatten_map {α β : Type} (entries : List α) (f : α → List β) :
    (entries.map f).flatten = entries.flatMap f := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih]

open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open LookupExecutionOrigin (Origin childStart)
variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : NativeTranscript.Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : NativeSharedLookupBody.Bound}

def original (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit) : View where
  transcript := origin.ready.equality.transcript
  earlier := frames (childStart row registry helper parent requests proof world).input
  groups := (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
      (childStart row registry helper parent requests proof world)) world).1.completed.map
      (fun entry => entry.selection.draws.map (fun draw => frame world draw.coefficients.phase))
  equality := origin.ready.machine.draws.map (fun draw => frame world draw.coefficients.phase)
  sequence := by
    rw [flatten_map]
    exact OriginalLookupReceiptOrder.sequence origin rootsFit
  initialCount := (LookupInitialReceipt.start world
    (OracleProgram.run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities).2
  groupLabels := by
    have labels := LookupBatchReceiptLabels.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel _ world
      (LookupBatchReceiptLabels.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
        (childStart row registry helper parent requests proof world))
    intro group member
    obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
    exact ReceiptLabelSegmentation.native_group world _ (labels.2 entry present)
  equalityLabels := by
    have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
      proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
      (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
    obtain ⟨transcript,_,machine,_⟩ := contract.lookup
    have labels := EqualityReceiptLabels.request NativeExtensionFields.goldilocksBasis 7 origin.geometry.geometry.1.val equalityFuel transcript
      proof.values.roots proof.roots.property world
    rw [← machine] at labels
    intro entry member
    obtain ⟨draw,present,rfl⟩ := List.mem_map.mp member
    exact labels.2 draw present

/-- No initial-count, rejection-count or per-job boundary equality is supplied.
Both executions may have different underlying contexts and worlds. -/
theorem compare (left right : View) (same : left.transcript.input = right.transcript.input) :
    left.groups = right.groups ∧ left.equality = right.equality := by
  have whole : left.earlier ++ (left.groups.flatten ++ left.equality) = right.earlier ++ (right.groups.flatten ++ right.equality) := by
    simpa only [List.append_assoc] using left.sequence.symm.trans ((congrArg frames same).trans right.sequence)
  have suffix := OrderedReceiptMatching.suffix_equal left.earlier right.earlier _ _
    (left.initialCount.trans right.initialCount.symm) whole
  exact ReceiptLabelSegmentation.prelude_unique left.groups right.groups left.equality right.equality
    left.groupLabels right.groupLabels left.equalityLabels right.equalityLabels suffix

end
end FormalProof4FHE.HasteBoots.OriginalReceiptSegmentation
