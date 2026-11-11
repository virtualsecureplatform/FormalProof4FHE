module
public import FormalProof4FHE.HasteBoots.LookupIdentityView
public import FormalProof4FHE.HasteBoots.LookupScalarGrammar
public import FormalProof4FHE.HasteBoots.ScalarFinishedSourceEvent
@[expose] public section

/-! Both native identity branches reduce false original scalar equations to
actual causal scalar events or wrong original source/helper openings. -/
namespace FormalProof4FHE.HasteBoots.LookupIdentityCausalReduction
open MatrixFold (Cube)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldRepresentation (goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeScalarQueryShape (laneBits)
open LookupIdentityView (View)
noncomputable section

variable {padding row : ℕ} {n : NativeUsizeMessage.Usize} {job : NativeSharedLookupStatement.Prepared}
  {claims : List NativeScalarBatchVerifier.SubClaim} {result : NativeSharedLookupGuard.Result} {ordinal : ℕ}

def Wrong {helperPadding : ℕ} (view : View padding row n job claims result ordinal)
    (sources : Fin job.tag.request.columns → Cube row → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks) : Prop :=
  (∃ i, (fun lane => goldValue (view.inputs i lane)) ≠
    (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ view.shape)
      (fun j => goldExtensionValue (view.point j))).query.fold (sources i)) ∨
    NativeHelperPacking.coefficients goldilocksBasis (3+helperPadding) (goldExtensionValue view.checked.helper) ≠
      (ExtensionQuery.coefficientsQuery goldilocksBasis (fun i => goldExtensionValue (view.point i))).query.fold helpers

def partialTables {helperPadding : ℕ} (view : View padding row n job claims result ordinal)
    (sources : Fin job.tag.request.columns → Cube row → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks) :=
  ExtensionLookupIdentity.factors (fun i => goldExtensionValue (view.eqPoint i)) (goldExtensionValue job.output.y)
    (fun column => LookupSourceFlattening.flatten (NativeScalarQueryShape.checked_power _ _ _ view.shape) (sources column))
    (fun cell => PaddedExtension.decode goldilocksBasis (helpers cell)) job.tag.request.terminal.logicalLength.val

def fullTables {helperPadding : ℕ} (view : View padding row n job claims result ordinal)
    (sources : Fin job.tag.request.columns → Cube row → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks) :=
  LookupPairArithmetic.fullTables (fun i => goldExtensionValue (view.eqPoint i)) (goldExtensionValue job.output.r) (goldExtensionValue job.output.y)
    (fun column => LookupSourceFlattening.flatten (NativeScalarQueryShape.checked_power _ _ _ view.shape) (sources column))
    (fun cell => PaddedExtension.decode goldilocksBasis (helpers cell))

theorem partial_event_or_wrong {helperPadding : ℕ}
    (view : View padding row n job claims result ordinal)
    (transcript : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (statement : NativeScalarBatchWire.Statement) (proof : NativeScalarBatchPreflight.Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (fuel : ℕ) (world : InputIndexedOracle.World)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims)
    (infoAt : statement.infos.val[2*ordinal+1]? = some (LookupScalarGrammar.identityInfo n job.tag.request))
    (branch : job.tag.request.terminal.logicalLength.val ≠ 2^n.val)
    (sources : Fin job.tag.request.columns → Cube row → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks)
    (initial : ScalarChainHealing.value (2*ordinal+1) statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue job.output.r)) ExtensionLookupIdentity.partialIndices
        (laneBits (3+padding)+row) (partialTables view sources helpers) [])) :
    ScalarFinishedSourceEvent.Event transcript statement proof fuel world ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue job.output.r)) ExtensionLookupIdentity.partialIndices
      (laneBits (3+padding)+row) (partialTables view sources helpers) (2*ordinal+1)
      (LookupScalarGrammar.identityInfo n job.tag.request) ∨ Wrong view sources helpers := by
  obtain ⟨bound,first,accepted,head⟩ := NativeSharedLookupBody.finished_preflight transcript statement proof fuel world claims finished
  have contract := NativeScalarBatchContract.finished_contract transcript bound statement proof first accepted head fuel world claims finished
  have output := NativeScalarBatchContract.contract_output statement proof first _ claims contract
  have claimLength := (output.2.2 view.checked.identityClaim (List.mem_of_getElem? view.claimAt)).2
  have dimension : first.numVariables.val = laneBits (3+padding)+row := by
    rw [view.claimPoint,List.length_ofFn] at claimLength
    exact claimLength.symm
  rcases LookupNativeTerminal.partial_or_wrong (padding := padding) (helperPadding := helperPadding) (row := row)
    view.eqPoint view.point view.shape job.tag.request.terminal.logicalLength view.shift view.enough
    job.tag.request.table view.producer.selection job.output view.produced view.inputs view.checked.helper view.checked.identityClaim.expected
    view.terminal sources helpers with truthful | wrong
  · apply Or.inl
    apply ScalarFinishedSourceEvent.of_claim transcript bound frames statement proof decoded accepted first head statementFits domain
      fuel world claims finished ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue job.output.r)) ExtensionLookupIdentity.partialIndices (laneBits (3+padding)+row) dimension
      (partialTables view sources helpers) (2*ordinal+1) (LookupScalarGrammar.identityInfo n job.tag.request) infoAt
      (LookupScalarGrammar.partial_arity n job.tag.request branch) initial view.checked.identityClaim view.claimAt
    rw [view.claimPoint]
    exact truthful
  · exact Or.inr wrong

theorem full_event_or_wrong {helperPadding : ℕ}
    (view : View padding row n job claims result ordinal)
    (transcript : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (statement : NativeScalarBatchWire.Statement) (proof : NativeScalarBatchPreflight.Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (fuel : ℕ) (world : InputIndexedOracle.World)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims)
    (infoAt : statement.infos.val[2*ordinal+1]? = some (LookupScalarGrammar.identityInfo n job.tag.request))
    (branch : job.tag.request.terminal.logicalLength.val = 2^n.val)
    (sources : Fin job.tag.request.columns → Cube row → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks)
    (initial : ScalarChainHealing.value (2*ordinal+1) statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
        (laneBits (3+padding)+row) (fullTables view sources helpers) [])) :
    ScalarFinishedSourceEvent.Event transcript statement proof fuel world ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (laneBits (3+padding)+row) (fullTables view sources helpers) (2*ordinal+1)
      (LookupScalarGrammar.identityInfo n job.tag.request) ∨ Wrong view sources helpers := by
  obtain ⟨bound,first,accepted,head⟩ := NativeSharedLookupBody.finished_preflight transcript statement proof fuel world claims finished
  have contract := NativeScalarBatchContract.finished_contract transcript bound statement proof first accepted head fuel world claims finished
  have output := NativeScalarBatchContract.contract_output statement proof first _ claims contract
  have claimLength := (output.2.2 view.checked.identityClaim (List.mem_of_getElem? view.claimAt)).2
  have dimension : first.numVariables.val = laneBits (3+padding)+row := by
    rw [view.claimPoint,List.length_ofFn] at claimLength
    exact claimLength.symm
  have fullLength : job.tag.request.terminal.logicalLength.val = 2^(laneBits (3+padding)+row) := by rwa [← view.dimension]
  rcases LookupNativeTerminal.full_or_wrong (padding := padding) (helperPadding := helperPadding) (row := row)
    view.eqPoint view.point view.shape job.tag.request.terminal.logicalLength view.shift fullLength
    job.tag.request.table view.producer.selection job.output view.produced view.inputs view.checked.helper view.checked.identityClaim.expected
    view.terminal sources helpers with truthful | wrong
  · apply Or.inl
    apply ScalarFinishedSourceEvent.of_claim transcript bound frames statement proof decoded accepted first head statementFits domain
      fuel world claims finished ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices (laneBits (3+padding)+row) dimension
      (fullTables view sources helpers) (2*ordinal+1) (LookupScalarGrammar.identityInfo n job.tag.request) infoAt
      (LookupScalarGrammar.full_arity n job.tag.request branch) initial view.checked.identityClaim view.claimAt
    rw [view.claimPoint]
    exact truthful
  · exact Or.inr wrong

end
end FormalProof4FHE.HasteBoots.LookupIdentityCausalReduction
