module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchCausalCoverage
@[expose] public section

/-! Causal field and column events depend on the fixed public parameters,
not a future verifier's root, opening, parent transcript or scheduler. This
allows all accepted batches with those parameters to share one event charge. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchEventContext
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize)
open NativeRootMessage (Digest)
open NativeIndexExposureRisk (Packet)
open InputIndexedOracle (World)
noncomputable section

theorem field_event {S A : Type} (dummy : Digest) (first second : Context)
    (same : first.parameters = second.parameters)
    (firstPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue first.parameters.code.domainRoot) (2^(logSize first.parameters.code+1)))
    (secondPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue second.parameters.code.domainRoot) (2^(logSize second.parameters.code+1)))
    (radius : ℕ) (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) :
    NativeGoldBatchFieldProximity.event dummy first firstPrimitive radius profile step packet world ↔
      NativeGoldBatchFieldProximity.event dummy second secondPrimitive radius profile step packet world := by
  cases first
  cases second
  cases same
  rfl

theorem raw_heq (dummy : Digest) (first second : Context)
    (same : first.parameters = second.parameters) (decoded : NativeGoldBatchChallengeLink.View)
    (sourceLog : NativeRootFamilySourceSelection.Log) :
    HEq (NativeGoldBatchConcreteColumnFamily.raw dummy first decoded sourceLog)
      (NativeGoldBatchConcreteColumnFamily.raw dummy second decoded sourceLog) := by
  cases first
  cases second
  cases same
  apply heq_of_eq
  funext state test
  cases test <;> rfl

theorem claim_heq (first second : Context) (same : first.parameters = second.parameters)
    (firstPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue first.parameters.code.domainRoot) (2^(logSize first.parameters.code+1)))
    (secondPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue second.parameters.code.domainRoot) (2^(logSize second.parameters.code+1)))
    (decoded : NativeGoldBatchChallengeLink.View) :
    HEq (NativeGoldBatchConcreteColumnFamily.claim first firstPrimitive decoded)
      (NativeGoldBatchConcreteColumnFamily.claim second secondPrimitive decoded) := by
  cases first
  cases second
  cases same
  apply heq_of_eq
  funext state test
  cases test <;> rfl

theorem column_event {S A : Type} (dummy : Digest) (first second : Context)
    (same : first.parameters = second.parameters)
    (firstPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue first.parameters.code.domainRoot) (2^(logSize first.parameters.code+1)))
    (secondPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue second.parameters.code.domainRoot) (2^(logSize second.parameters.code+1)))
    (radius : ℕ) (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) :
    NativeGoldBatchConcreteColumnExposure.event dummy first firstPrimitive profile step packet radius world ↔
      NativeGoldBatchConcreteColumnExposure.event dummy second secondPrimitive profile step packet radius world := by
  have raw := fun decoded sourceLog => raw_heq dummy first second same decoded sourceLog
  have claim := fun decoded => claim_heq first second same firstPrimitive secondPrimitive decoded
  cases first
  cases second
  cases same
  simp only [heq_eq_eq] at raw claim
  unfold NativeGoldBatchConcreteColumnExposure.event NativeGoldBatchConcreteColumnBound.event
    NativeGoldBatchConcreteColumnBound.distance NativeGoldBatchFieldColumnLaw.event NativeGoldBatchWitnessedColumnBound.checked
  simp only [raw,claim]
  rfl
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchEventContext
