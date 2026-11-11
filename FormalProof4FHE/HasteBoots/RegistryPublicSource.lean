module
public import FormalProof4FHE.HasteBoots.AllocatedCodeOrigin
public import FormalProof4FHE.HasteBoots.GoldHistoryPublicExtraction
public import FormalProof4FHE.HasteBoots.SourceOpeningLifetimeWitness
@[expose] public section

/-! Each original logical registry slot has a public extraction context and
the actual retained initializer provenance. Call-specific queries and response
records do not select a different reference source for that slot. -/
namespace FormalProof4FHE.HasteBoots.RegistryPublicSource
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldParameterStore (Entry Reference)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeRootFamilySourceSelection (Log)
noncomputable section

/-- Only the original registry parameters and root enter this reference.
The empty call payload is never executed as a verifier call. -/
def context (ctx : NativeGoldHelperVerification.Context (Vector Opening)) (slot : Fin ctx.registry.val.length) :
    NativeGoldBatchPcsProgram.Context :=
  ⟨ctx.tables,(ctx.registry.val.get slot).parameters,ctx.parent,(ctx.registry.val.get slot).root,
    ⟨[],by decide⟩,⟨[],by decide⟩,⟨⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩⟩,ctx.fieldFuel⟩

def origin (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (slot : Fin ctx.registry.val.length) : CacheBackedCodeOrigin.Origin (context ctx slot) :=
  AllocatedCodeOrigin.ofRegistry entries reachable references ctx.registry collected slot (context ctx slot) rfl

theorem origin_data (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (slot : Fin ctx.registry.val.length) :
    (origin ctx entries reachable references collected slot).request =
        (AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry collected slot).request ∧
      (origin ctx entries reachable references collected slot).config =
        (AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry collected slot).config := ⟨rfl,rfl⟩

/-- The native prepared geometry belongs to the full parameter record and
therefore transports to the original reference slot. -/
theorem geometry (candidate reference : NativeGoldBatchPcsProgram.Context)
    (parameters : candidate.parameters = reference.parameters) (world : InputIndexedOracle.World)
    (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram candidate) world).run.1 = .prepared work) :
    GoldHistorySourceTable.Geometry reference.parameters :=
  parameters ▸ BatchOpeningNativeObligation.dimensions candidate world work prepared

/-- A batch table is compatible with a fixed original registry reference for
all parsed nonce views, recovered logs and admitted radii. Exact log and
parsed digest/root identities are conclusions of the compatibility proof. -/
def Compatible (candidate reference : NativeGoldBatchPcsProgram.Context)
    (candidateOrigin : CacheBackedCodeOrigin.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (world : InputIndexedOracle.World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram candidate) world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) (sizes : GoldHistorySourceTable.Geometry reference.parameters) : Prop :=
  ∀ (radius : ℕ), 3*radius < reference.parameters.code.blocks.val-reference.parameters.code.messageBlocks.val+1 →
    ∀ (_ : NativeGoldBatchSourceRisk.Framed candidate)
      (_ : (NativeGoldBatchResponseBinding.payload candidate.opening).length < TranscriptFrame.lengthLimit)
      (decoded : NativeGoldBatchChallengeLink.View),
      NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input candidate work world) = some decoded →
      ∀ (sourceLog : Log), NativeGoldBatchFirstFieldSource.recover dummy history decoded.field = some sourceLog →
        HEq (BatchOpeningNativeObligation.source dummy candidate (candidateOrigin.primitiveAt candidate rfl)
          (candidateOrigin.capacityAt candidate rfl) world work prepared decoded radius sourceLog)
          (GoldHistoryPublicExtraction.cube reference dummy
            (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters)) reference.root history radius
            (referenceOrigin.capacityAt reference rfl) sizes)

theorem compatible (candidate reference : NativeGoldBatchPcsProgram.Context)
    (candidateOrigin : CacheBackedCodeOrigin.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (parameters : candidate.parameters = reference.parameters) (root : candidate.root = reference.root)
    (world : InputIndexedOracle.World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram candidate) world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) :
    Compatible candidate reference candidateOrigin referenceOrigin world work prepared dummy history
      (geometry candidate reference parameters world work prepared) := by
  intro radius small framed responseFits decoded parsed sourceLog recovered
  have candidateSmall : 3*radius < candidate.parameters.code.blocks.val-candidate.parameters.code.messageBlocks.val+1 := by
    rw [parameters]
    exact small
  have same := GoldHistoryPublicExtraction.batch_source_eq_public dummy candidate candidateOrigin world work prepared framed responseFits
    decoded parsed history sourceLog recovered radius candidateSmall
  apply HEq.trans (heq_of_eq same)
  have cubes := GoldHistoryPublicExtraction.cube_congr candidate reference parameters dummy
    (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters)) reference.root history radius
    (candidateOrigin.capacityAt candidate rfl) (referenceOrigin.capacityAt reference rfl)
    (BatchOpeningNativeObligation.dimensions candidate world work prepared) (geometry candidate reference parameters world work prepared)
  have digest := congrArg (fun parameters => InputIndexedOracle.sha512 world (GoldContextInput.bytes parameters)) parameters
  rw [digest,root]
  exact cubes

end
end FormalProof4FHE.HasteBoots.RegistryPublicSource
