module
public import FormalProof4FHE.HasteBoots.ReceiptCoefficientCandidates
public import FormalProof4FHE.HasteBoots.LookupProducerConsumed
@[expose] public section

/-! Earlier receipt keys give finite candidate covers of actual native lookup
values and equality points. The alternative of an unseen receipt stays explicit;
no digest authentication or counterfactual single-value equality is assumed. -/
namespace FormalProof4FHE.HasteBoots.LookupReceiptCandidates
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open scoped Classical
noncomputable section
variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K]

def scalars (basis : Module.Basis (Fin degree) (ZMod p) K) (history : List Observation) : Finset K :=
  (ReceiptCoefficientCandidates.candidates p history).image (TypedFieldRequest.scalarValue basis)

def points (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) (history : List Observation) : Finset (Fin count → K) :=
  (ReceiptCoefficientCandidates.candidates p history).image (TypedFieldVector.value basis count)

theorem scalars_card (basis : Module.Basis (Fin degree) (ZMod p) K) (history : List Observation) :
    (scalars basis history).card ≤ history.length :=
  Finset.card_image_le.trans (ReceiptCoefficientCandidates.card p history)

theorem points_card (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) (history : List Observation) :
    (points basis count history).card ≤ history.length :=
  Finset.card_image_le.trans (ReceiptCoefficientCandidates.card p history)

theorem scalar (basis : Module.Basis (Fin degree) (ZMod p) K)
    (positive : 0 < CanonicalByteSampler.byteCount p) (machine : NativeLookupChallenge.Machine K)
    (trace : LookupConsumedTrace.Lookup p machine) (valid : NativeLookupChallenge.MachineValid basis machine)
    (draw : NativeLookupChallenge.Draw K) (member : draw ∈ machine.draws) (history : List Observation)
    (seen : CausalStreamExposure.seen history (NativeFieldReceipt.input draw.coefficients.phase) = true) :
    draw.value ∈ scalars basis history := by
  apply Finset.mem_image.mpr
  exact ⟨draw.coefficients.values,ReceiptCoefficientCandidates.covered p positive _ (trace.2 draw member) history seen,
    (valid.2 draw member).2.2.symm⟩

theorem point (basis : Module.Basis (Fin degree) (ZMod p) K)
    (positive : 0 < CanonicalByteSampler.byteCount p) (machine : NativeLookupEquality.Machine count K)
    (trace : LookupConsumedTrace.Equality p machine) (valid : NativeLookupEquality.Valid basis machine)
    (draw : NativeLookupEquality.Draw count K) (member : draw ∈ machine.draws) (history : List Observation)
    (seen : CausalStreamExposure.seen history (NativeFieldReceipt.input draw.coefficients.phase) = true) :
    draw.point ∈ points basis count history := by
  apply Finset.mem_image.mpr
  exact ⟨draw.coefficients.values,ReceiptCoefficientCandidates.covered p positive _ (trace.2 draw member) history seen,
    (valid.2 draw member).2.2.symm⟩

theorem equality_request (basis : Module.Basis (Fin degree) (ZMod p) K) (positive : 0 < CanonicalByteSampler.byteCount p)
    (w count fuel : ℕ) (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) (draw : NativeLookupEquality.Draw count K)
    (member : draw ∈ (OracleProgram.run (NativeLookupEquality.request basis w count fuel transcript roots fits) world).run.1.draws)
    (history : List Observation) :
    draw.point ∈ points basis count history ∨
      CausalStreamExposure.seen history (NativeFieldReceipt.input draw.coefficients.phase) = false := by
  cases seen : CausalStreamExposure.seen history (NativeFieldReceipt.input draw.coefficients.phase) with
  | false => exact Or.inr rfl
  | true => exact Or.inl (point basis positive _ (LookupConsumedTrace.equality_request basis w count fuel transcript roots fits world)
      (NativeLookupEquality.request_valid basis w count fuel transcript roots fits world) draw member history seen)

section Original
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open LookupExecutionOrigin (Origin childStart)
variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : NativeTranscript.Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : NativeSharedLookupBody.Bound}

theorem producer_draw (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (draw : NativeLookupChallenge.Draw NativeExtensionFields.Goldilocks3) (member : draw ∈ job.view.producer.selection.draws)
    (history : List Observation) :
    draw.value ∈ scalars NativeExtensionFields.goldilocksBasis history ∨
      CausalStreamExposure.seen history (NativeFieldReceipt.input draw.coefficients.phase) = false := by
  cases seen : CausalStreamExposure.seen history (NativeFieldReceipt.input draw.coefficients.phase) with
  | false => exact Or.inr rfl
  | true =>
    have valid := NativeLookupBatch.execute_valid NativeExtensionFields.goldilocksBasis 7 lookupFuel _ world
      (NativeLookupBatch.initial_valid NativeExtensionFields.goldilocksBasis
        (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
        (childStart row registry helper parent requests proof world))
    exact Or.inl (scalar NativeExtensionFields.goldilocksBasis (by decide +kernel) _
      (LookupProducerConsumed.producer origin job) (valid.2 _ job.producerMember).1.1 draw member history seen)


theorem original_equality (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws) (history : List Observation) :
    draw.point ∈ points NativeExtensionFields.goldilocksBasis origin.geometry.geometry.1.val history ∨
      CausalStreamExposure.seen history (NativeFieldReceipt.input draw.coefficients.phase) = false := by
  have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
  obtain ⟨transcript,_,machine,_⟩ := contract.lookup
  rw [machine] at member
  exact equality_request NativeExtensionFields.goldilocksBasis (by decide +kernel) 7 _ equalityFuel transcript
    proof.values.roots proof.roots.property world draw member history

end Original
end
end FormalProof4FHE.HasteBoots.LookupReceiptCandidates
