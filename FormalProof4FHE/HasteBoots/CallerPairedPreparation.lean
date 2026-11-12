module
public import FormalProof4FHE.HasteBoots.SeedOrderPairedWork
public import FormalProof4FHE.HasteBoots.SequencedCallerInputs
@[expose] public section

/-! Original sequenced inputs and native completion supply paired-security
preconditions independently of which original scalar equation is false. -/
namespace FormalProof4FHE.HasteBoots.CallerPairedPreparation
open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
open NativePrefixCodec (Vector)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

def sumTruth (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :=
  ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
    (NativeScalarQueryShape.laneBits (3+data.origin.padding)+data.lookup.body.sourceVariables)
    (LookupViewSumReduction.tables (CanonicalAllocatedTables.helpers allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)) []

def toCanonical (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (framed : NativeTranscriptFraming.Framed ctx.parent) : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world :=
  let registryFits := CallerSerializationOrigin.registry_fits data inputs.buffers
  let parent := CallerFramedAllocatedJob.toParent data helperWidth sourceWidths framed inputs.parent_domain registryFits
  DecodedAllocatedJob.toCanonical (ParentFramedAllocatedJob.toDecoded parent helperWidth framed inputs.parent_domain registryFits)

theorem truths (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (framed : NativeTranscriptFraming.Framed ctx.parent) (dummy : Digest) :
    AllocatedSumAlternatives.truth (toCanonical data inputs helperWidth sourceWidths framed) dummy = sumTruth data dummy ∧
      CanonicalAllocatedIdentity.truth (toCanonical data inputs helperWidth sourceWidths framed) dummy = CallerFramedAllocatedJob.truth data dummy :=
  ⟨rfl,rfl⟩

theorem round_domain (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra := by
  have nonempty := ScalarProofFraming.nonempty_of_finished _ _ _ _ _ _ data.origin.scalar
  let algebra : Vector InputIndexedOracle.Byte := ⟨ScalarProofFraming.proofCodec.encode ctx.proof.algebra,(CallerFramedAllocatedJob.domain data).algebraFits⟩
  exact ScalarProofFraming.roundDomain_of_bytes ctx.proof.algebra nonempty algebra (NativeExactCodec.read_encode _ _)

def framing (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) : AllocatedLookupReadStability.Framing ctx world :=
  Classical.choice (LookupFramingRecovery.job_framing (toCanonical data inputs helperWidth sourceWidths ⟨before,bytes,valid⟩)
    before bytes valid inputs.parent_domain (CallerSerializationOrigin.registry_fits data inputs.buffers)
    (CallerFramedAllocatedJob.domain data).groupedFits (CallerFramedAllocatedJob.domain data).flatFits)

end
end FormalProof4FHE.HasteBoots.CallerPairedPreparation
