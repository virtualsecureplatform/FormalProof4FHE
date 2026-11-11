module
public import FormalProof4FHE.HasteBoots.GoldScalarChallengeLaw
public import FormalProof4FHE.HasteBoots.NativeScalarBatchRoundMeaning
@[expose] public section

/-! The outer scalar round's actual typed request collects the same three
canonical coefficients used by the conditional extension-field law. The
bound round packet, retries, suspensions and receipt are left unchanged. -/
namespace FormalProof4FHE.HasteBoots.ScalarRoundChallengeMeaning
open NativeFields (goldilocksModulus)
open NativeFieldRepresentation (goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeScalarBatchWire (RoundPacket bindRound challengeLabel)
open NativeTranscript (Transcript FieldPhase)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def preparedTranscript (transcript : Transcript) (packet : RoundPacket) :=
  NativeExtensionRequest.prepare (TypedFieldRequest.prepare (bindRound transcript packet) .scalar) 3 7

def phase (transcript : Transcript) (packet : RoundPacket) : FieldPhase :=
  TypedFieldRequest.scalarPhase goldilocksModulus 3 7 (bindRound transcript packet) challengeLabel

def request (fuel : ℕ) (transcript : Transcript) (packet : RoundPacket) :=
  NativeFieldVector.request goldilocksModulus fuel (preparedTranscript transcript packet) challengeLabel 3

/-- The same primitive used by native scalar rounds, not an idealized sampler. -/
theorem request_eq_start_drive (fuel : ℕ) (transcript : Transcript) (packet : RoundPacket) (world : World) :
    (run (request fuel transcript packet) world).run =
      (run (OracleProgram.bind (TypedFieldRequest.beginScalar goldilocksModulus 3 7 (bindRound transcript packet) challengeLabel)
        (NativeFieldVector.drive goldilocksModulus fuel)) world).run :=
  (TypedFieldRequest.drive_scalar goldilocksModulus 3 7 fuel world (bindRound transcript packet) challengeLabel).symm

theorem decode_value (state : NativeFieldVector.State) (challenge : NativeGoldExtensionArithmetic.Word)
    (decoded : NativeGoldLookupProducer.decode state.values = some challenge) :
    TypedFieldRequest.scalarValue NativeExtensionFields.goldilocksBasis state.values = goldExtensionValue challenge := by
  unfold NativeGoldLookupProducer.decode at decoded
  split at decoded
  next complete =>
    split at decoded
    next valid =>
      cases Option.some.inj decoded
      exact (NativeGoldLookupCompleted.fromCoefficients_value _ complete valid).symm
    next => contradiction
  next => contradiction

/-- Completed requests identify the literal retained native challenge with
this law's value. No independent coefficient-assembly equality is supplied. -/
theorem finished_value (fuel : ℕ) (transcript : Transcript) (packet : RoundPacket) (world : World)
    (state : NativeFieldVector.State) (next : Transcript)
    (finished : (run (request fuel transcript packet) world).run.1 = .finished state next)
    (challenge : NativeGoldExtensionArithmetic.Word) (decoded : NativeGoldLookupProducer.decode state.values = some challenge) :
    GoldScalarChallengeLaw.values fuel (phase transcript packet) world = some (goldExtensionValue challenge) := by
  have native := NativeFieldVectorLaw.finished_values goldilocksModulus fuel 3 (preparedTranscript transcript packet) challengeLabel
    world state next finished
  change NativeFieldVectorLaw.values goldilocksModulus fuel 3 (phase transcript packet) world = _ at native
  unfold GoldScalarChallengeLaw.values
  rw [native]
  exact congrArg some (decode_value state challenge decoded)

/-- Successful native collection itself derives canonical decoding. -/
theorem finished_decodes (fuel : ℕ) (transcript : Transcript) (packet : RoundPacket) (world : World)
    (state : NativeFieldVector.State) (next : Transcript)
    (finished : (run (request fuel transcript packet) world).run.1 = .finished state next) :
    ∃ challenge : NativeGoldExtensionArithmetic.Word, NativeGoldLookupProducer.decode state.values = some challenge ∧
      GoldScalarChallengeLaw.values fuel (phase transcript packet) world = some (goldExtensionValue challenge) := by
  have length := NativeFieldVector.request_finished_length goldilocksModulus fuel (preparedTranscript transcript packet) challengeLabel 3 world state next finished
  have valid := NativeFieldVector.request_values_valid goldilocksModulus fuel (preparedTranscript transcript packet) challengeLabel 3 world
  change NativeFieldVector.ValuesValid goldilocksModulus (NativeFieldVector.stateOf (run (request fuel transcript packet) world).run.1) at valid
  rw [finished] at valid
  let challenge := NativeGoldLookupCompleted.fromCoefficients state.values length valid
  have decoded := NativeGoldLookupProducer.decode_complete state.values length valid
  exact ⟨challenge,decoded,finished_value fuel transcript packet world state next finished challenge decoded⟩

end
end FormalProof4FHE.HasteBoots.ScalarRoundChallengeMeaning
