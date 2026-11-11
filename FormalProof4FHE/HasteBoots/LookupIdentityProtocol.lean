module
public import FormalProof4FHE.HasteBoots.LookupIdentityCausalReduction
@[expose] public section

/-! Original protocol composition: operational preflight/prelude/scalar/guard
success supplies the view and both identity reductions at the original ordinal.
Only framing and fixed original table interpretations remain explicit here. -/
namespace FormalProof4FHE.HasteBoots.LookupIdentityProtocol
open NativeSharedLookupStatement (Request)
open NativeSharedLookupPrelude (Ready guardInputs)
open NativeSharedLookupGuard (Result)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupProofShape (Values)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeScalarQueryShape (laneBits)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (goldilocksBasis)
open LookupIdentityCausalReduction (partialTables fullTables Wrong)
noncomputable section

theorem reduce {count padding : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values)
    (shape : NativeSharedLookupProofShape.check registry (List.ofFn requests) geometry openingCount values = true)
    (width : geometry.geometry.2.val = 3+padding)
    (rootFits : values.roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (ready : Ready geometry.geometry.1.val)
    (prepared : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (proof : NativeScalarBatchPreflight.Proof) (fuel : ℕ) (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute ready.statement proof fuel
      (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof) world).1.control = .finished claims)
    (sourceVars : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard (guardInputs requests ready values.sources values.helpers)
      claims sourceVars geometry.geometry.2.val = some result) (index : Fin ready.jobs.length)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) :
    ∃ view : LookupIdentityView.View padding sourceVars geometry.geometry.1 (ready.jobs.get index) claims result index.val,
      view.producer ∈ (NativeLookupBatch.execute goldilocksBasis w lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed ∧
      view.producer.job = (ready.jobs.get index).tag.job ∧
      List.Forall₂ (fun slot value => values.sources[slot]? = some value)
        (ready.jobs.get index).tag.request.terminal.sourceSlots view.checked.values ∧
      (∃ draw, ready.machine.draws[index.val]? = some draw ∧ NativeGoldLookupEquality.DrawEvidence draw (List.ofFn view.eqPoint)) ∧
      ∀ (helperPadding : ℕ)
        (sources : Fin (ready.jobs.get index).tag.request.columns → MatrixFold.Cube sourceVars → Fin (3+padding) → NativeFields.Goldilocks)
        (helpers : MatrixFold.Cube (laneBits (3+padding)+sourceVars) → Fin (3+helperPadding) → NativeFields.Goldilocks),
        ((ready.jobs.get index).tag.request.terminal.logicalLength.val ≠ 2^geometry.geometry.1.val →
          ScalarChainHealing.value (2*index.val+1) ready.statement.claims.val ≠
            some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
              (laneBits (3+padding)+sourceVars) (partialTables view sources helpers) []) →
          ScalarFinishedSourceEvent.Event ready.equality.transcript ready.statement proof fuel world ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
            (laneBits (3+padding)+sourceVars) (partialTables view sources helpers) (2*index.val+1)
            (LookupScalarGrammar.identityInfo geometry.geometry.1 (ready.jobs.get index).tag.request) ∨ Wrong view sources helpers) ∧
        ((ready.jobs.get index).tag.request.terminal.logicalLength.val = 2^geometry.geometry.1.val →
          ScalarChainHealing.value (2*index.val+1) ready.statement.claims.val ≠
            some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
              (laneBits (3+padding)+sourceVars) (fullTables view sources helpers) []) →
          ScalarFinishedSourceEvent.Event ready.equality.transcript ready.statement proof fuel world ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
            (laneBits (3+padding)+sourceVars) (fullTables view sources helpers) (2*index.val+1)
            (LookupScalarGrammar.identityInfo geometry.geometry.1 (ready.jobs.get index).tag.request) ∨ Wrong view sources helpers) := by
  obtain ⟨view,producerMember,producerJob,related,draw⟩ := LookupIdentityView.recover fits requests registry helper geometry preflight
    openingCount values shape width rootFits w lookupFuel equalityFuel transcript world ready prepared proof fuel claims finished sourceVars result passed index
  have infoAt := (LookupScalarGrammar.protocol_pair fits requests geometry.geometry.1 values.multiplicities values.roots rootFits
    w lookupFuel equalityFuel transcript world ready prepared index.val index.isLt).2.1
  refine ⟨view,producerMember,producerJob,related,draw,?_⟩
  intro helperPadding sources helpers
  constructor
  · intro branch initial
    exact LookupIdentityCausalReduction.partial_event_or_wrong view ready.equality.transcript frames ready.statement proof decoded statementFits
      domain fuel world finished infoAt branch sources helpers initial
  · intro branch initial
    exact LookupIdentityCausalReduction.full_event_or_wrong view ready.equality.transcript frames ready.statement proof decoded statementFits
      domain fuel world finished infoAt branch sources helpers initial

end
end FormalProof4FHE.HasteBoots.LookupIdentityProtocol
