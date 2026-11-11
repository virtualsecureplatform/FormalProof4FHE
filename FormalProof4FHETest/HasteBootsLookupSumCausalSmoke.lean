module
import all FormalProof4FHE.HasteBoots.LookupSumCausalReduction
import all FormalProof4FHETest.HasteBootsScalarSourceCausalSmoke

namespace FormalProof4FHE.HasteBoots.LookupSumCausalSmoke
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeGoldExtensionArithmetic (Word)
open NativeFieldWire (goldExtensionValue)
open HasteBootsScalarFinishAncestrySmoke (usize message)
open HasteBootsSamplerAncestrySmoke (child worldZero)
open ScalarExecutionRecoverySmoke (before decoded)
open MatrixFold (Cube)
noncomputable section

def info : NativeScalarBatchWire.Info := ⟨usize 1,usize 2⟩
def statement : NativeScalarBatchWire.Statement := ⟨⟨[info,info],by decide⟩,⟨[NativeGoldLookup.zero,NativeGoldLookup.zero],by decide⟩⟩
def certificate : NativePrefixCodec.Vector NativeScalarBatchWire.Message := ⟨[message,message],by decide⟩
def proof : NativeScalarBatchPreflight.Proof := ⟨[certificate,certificate],by decide⟩
def execution := NativeScalarBatchVerifier.execute statement proof 9 (NativeScalarBatchVerifier.initial child statement proof) worldZero

def claims : List NativeScalarBatchVerifier.SubClaim := execution.1.state.expected.map (fun value => ⟨execution.1.state.point,value⟩)
theorem finished : execution.1.control = .finished claims := rfl

def data : NativeSharedLookupGuard.Inputs :=
  ⟨[⟨[],usize 0⟩],[⟨0,NativeGoldLookup.one,[]⟩],[[NativeGoldLookup.zero,NativeGoldLookup.zero]],[],[NativeGoldLookup.zero]⟩
def guarded? := NativeSharedLookupGuard.guard data claims 0 4
theorem guardPresent : guarded?.isSome = true := by decide +kernel
def result := guarded?.get guardPresent
theorem guarded : NativeSharedLookupGuard.guard data claims 0 4 = some result := (Option.some_get guardPresent).symm

def checked := result.checked[0]'(by decide +kernel)
theorem checkedMember : checked ∈ result.checked := List.getElem_mem _

def helpers (cell : Cube 2) : Fin 4 → NativeFields.Goldilocks :=
  PaddedExtension.encode (padding := 1) goldilocksBasis (ScalarSourceSmoke.jointTable () cell)

theorem initialTruth : ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
    2 (fun _ cell => PaddedExtension.decode (padding := 1) goldilocksBasis (helpers cell)) [] = 1 := by
  simp only [ScalarNativeSourceHealing.truth,List.map_nil,ScalarLookupExpression.sum_initial,helpers,PaddedExtension.decode_encode]
  have original := ScalarSourceSmoke.initial_truth
  simpa only [ScalarSourceSmoke.sourceTruth,ScalarNativeSourceHealing.truth,List.map_nil,ScalarSourcePolynomial.truth,
    ScalarSourceSmoke.single_expressionG] using original

theorem initiallyFalse : ScalarChainHealing.value (2*checked.ordinal) statement.claims.val ≠
    some (ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      2 (fun _ cell => PaddedExtension.decode (padding := 1) goldilocksBasis (helpers cell)) []) := by
  have ordinal : checked.ordinal = 0 := by decide +kernel
  have getter : statement.claims.val[0]? = some NativeGoldLookup.zero := rfl
  simp only [ordinal,Nat.mul_zero,ScalarChainHealing.value,getter,Option.map_some,initialTruth,NativeGoldLookup.zero_value,
    ne_eq,Option.some.injEq]
  exact zero_ne_one

theorem domain : NativeScalarTranscriptExtension.RoundDomain proof := by
  intro round packet source
  obtain ⟨round,bounded⟩ := round
  cases round with
  | zero =>
    have same : (⟨usize 0,⟨[message,message],by decide⟩⟩ : NativeScalarBatchWire.RoundPacket) = packet := Option.some.inj source
    rw [← same]
    decide +kernel
  | succ round =>
    cases round with
    | zero =>
      have same : (⟨usize 1,⟨[message,message],by decide⟩⟩ : NativeScalarBatchWire.RoundPacket) = packet := Option.some.inj source
      rw [← same]
      decide +kernel
    | succ round =>
      change none = some packet at source
      contradiction

/-- Actual two-equation completion and guard acceptance share the returned
point; no supplied common-point equality or healing witness is used. -/
example : execution.1.completed.length = 2 ∧ result.point = [NativeGoldLookup.zero,NativeGoldLookup.zero] ∧
    checked.ordinal = 0 := by decide +kernel

/-- The original false sum forces an actual completed-input causal event or
a wrong original helper opening at the derived native returned point. -/
theorem event_or_wrong :
    (∃ entry ∈ execution.1.completed, ∃ message, entry.packet.messages.val[2*checked.ordinal]? = some message ∧
      ∃ configuration : ScalarRecoveredReplay.Configuration,
        ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
        ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration child.profile
          (ScalarSourceChallengeBound.test (LookupScalarGrammar.sumInfo info.numVariables) message ScalarLookupExpression.sumArity
            ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices 2
            (fun _ cell => PaddedExtension.decode (padding := 1) goldilocksBasis (helpers cell))) worldZero) ∨
    ∃ point : Fin 2 → Word, List.ofFn point = result.point ∧
      NativeHelperPacking.coefficients goldilocksBasis 4 (goldExtensionValue checked.helper) ≠
        (ExtensionQuery.coefficientsQuery (padding := 1) goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold helpers := by
  have infoAt : statement.infos.val[2*checked.ordinal]? = some (LookupScalarGrammar.sumInfo info.numVariables) := by
    have ordinal : checked.ordinal = 0 := by decide +kernel
    rw [ordinal]
    rfl
  exact LookupSumCausalReduction.event_or_wrong (padding := 1) child (NativeScalarBatchWire.bindStatement child statement) before statement proof info
    decoded rfl rfl (by decide +kernel) domain 9 worldZero claims finished data 0 4 result guarded checked checkedMember helpers infoAt initiallyFalse

/-- Truth of the actual helper at the returned zero point rules out the
wrong-opening alternative, leaving a literal original causal scalar event. -/
example : ∃ entry ∈ execution.1.completed, ∃ message, entry.packet.messages.val[2*checked.ordinal]? = some message ∧
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
      ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration child.profile
        (ScalarSourceChallengeBound.test (LookupScalarGrammar.sumInfo info.numVariables) message ScalarLookupExpression.sumArity
          ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices 2
          (fun _ cell => PaddedExtension.decode (padding := 1) goldilocksBasis (helpers cell))) worldZero := by
  apply event_or_wrong.resolve_right
  rintro ⟨point,pointList,wrong⟩
  have actualPoint : result.point = List.ofFn (fun _ : Fin 2 => NativeGoldLookup.zero) := by decide +kernel
  have samePoint : point = fun _ => NativeGoldLookup.zero := List.ofFn_inj.mp (pointList.trans actualPoint)
  have helper : checked.helper = NativeGoldLookup.zero := by decide +kernel
  have folded : (ExtensionQuery.coefficientsQuery (padding := 1) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3))).query.fold helpers =
      PaddedExtension.encode (padding := 1) goldilocksBasis 0 := by
    have evaluated := ExtensionQuery.coefficients_evaluate (padding := 1) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3)) helpers
    change (ExtensionQuery.coefficientsQuery (padding := 1) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3))).query.fold helpers = _ at evaluated
    simpa [helpers,PaddedExtension.decode_encode,ExtensionQuery.evaluate,ScalarSourceSmoke.jointTable] using evaluated
  rw [samePoint,helper] at wrong
  simp only [NativeGoldLookup.zero_value] at wrong
  rw [NativeHelperPacking.coefficients_padded goldilocksBasis 1 (0 : Goldilocks3)] at wrong
  exact wrong folded.symm

end
end FormalProof4FHE.HasteBoots.LookupSumCausalSmoke
