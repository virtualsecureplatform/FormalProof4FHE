module
public import FormalProof4FHE.HasteBoots.LookupProducerArithmetic
public import FormalProof4FHE.HasteBoots.SequencedInputPairedWork
@[expose] public section

/-! Native arithmetic violations reduce to the paired 128-bit work theorem
with the actual equality-miss event retained on the same input realization.
No adaptive equality probability bound is asserted here. -/
namespace FormalProof4FHE.HasteBoots.LookupInitialPairedWork
open scoped BigOperators
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open OracleProgram (Program)
open AllocatedFamilyFunctions (Allocation)
open InterpreterScalarLifetime (privateProgram)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

structure Witness {Memory A : Type} (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
    (program : Program A) (dummy : Digest) (world : World) where
  data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world
  inputs : SequencedCallerInputs.Inputs data
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  broken : ∃ counts, ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]? = some counts ∧
    ((∑ cell, LookupInitialArithmetic.helper data dummy cell) ≠ NativeFieldWire.goldExtensionValue
      (NativeGoldExtensionArithmetic.tableSum (data.origin.ready.jobs.get data.index).output.inverses counts) ∨
      ∃ cell, LookupInitialArithmetic.residual data dummy cell ≠ 0)

/-- Original public table/count shape and reciprocal nonpassing construct
the work witness without an initially-false-scalar or accepted-domain flag. -/
def ofNonpassing {Memory A : Type} {ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A}
    {world : InputIndexedOracle.World} {size : ℕ}
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : NativeRootMessage.Digest)
    (table : Fin size → Fin (data.origin.ready.jobs.get data.index).tag.request.columns → NativeFieldRepresentation.GoldWord)
    (counts : Fin size → NativeFieldRepresentation.GoldWord)
    (tableRows : (data.origin.ready.jobs.get data.index).tag.request.table = List.ofFn (fun i => List.ofFn (table i)))
    (atCounts : ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]? = some (List.ofFn counts))
    (inputs : SequencedCallerInputs.Inputs data)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (notPasses : ¬ReciprocalDetection.Passes
      (LookupReciprocalEnforcement.activeSource (Nat.add_sub_of_le data.job.view.enough) (LookupInitialArithmetic.source data dummy))
      (fun i => TupleHash.hash (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (fun j => NativeFieldRepresentation.goldValue (table i j)))
      (fun i => algebraMap NativeFields.Goldilocks NativeExtensionFields.Goldilocks3 (NativeFieldRepresentation.goldValue (counts i)))
      (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨data,inputs,before,bytes,valid,⟨List.ofFn counts,atCounts,
    LookupProducerArithmetic.job_obstruction data dummy table counts tableRows notPasses⟩⟩

theorem covered {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    Nonempty (SequencedInputPairedWork.Witness (Memory := Memory) ctx allocation program dummy world) ∨
      LookupInitialArithmetic.EqualityMiss witness.data dummy := by
  obtain ⟨counts,atCounts,broken⟩ := witness.broken
  rcases LookupInitialArithmetic.obstruction witness.data dummy counts atCounts broken with initial | missed
  · exact Or.inl ⟨⟨witness.data,witness.inputs,witness.before,witness.bytes,witness.valid,initial⟩⟩
  · exact Or.inr missed

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

def EqualityException (execution : Tape × World) : Prop :=
  ∃ fuel, ∃ witness : Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2,
    LookupInitialArithmetic.EqualityMiss witness.data dummy

theorem failure_covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    SequencedInputPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution ∨
      EqualityException Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  rcases covered witness with paired | missed
  · exact Or.inl ⟨fuel,paired⟩
  · exact Or.inr ⟨fuel,witness,missed⟩

theorem work_with_equality_exception (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData +
        (2 : ENNReal)^128 * (coins.prod law) {execution | EqualityException Memory ctx allocation code publicData privateData dummy execution} := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | SequencedInputPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution} ∪
      {execution | EqualityException Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact failure_covered Memory ctx allocation code publicData privateData dummy execution failed
  calc
    _ ≤ (2 : ENNReal)^128 * ((coins.prod law)
        {execution | SequencedInputPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution} +
        (coins.prod law) {execution | EqualityException Memory ctx allocation code publicData privateData dummy execution}) :=
      mul_le_mul' le_rfl ((measure_mono included).trans (measure_union_le _ _))
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add
        (SequencedInputPairedWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
          helperRole helperAdmitted sourceRole sourceAdmitted coins) le_rfl

end
end FormalProof4FHE.HasteBoots.LookupInitialPairedWork
