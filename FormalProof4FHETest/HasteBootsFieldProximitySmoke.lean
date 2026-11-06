module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFieldProximityCoverage
import all FormalProof4FHETest.HasteBootsConcreteCoverageSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (World law)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsFieldProximitySmoke
noncomputable section
open HasteBootsBatchOrderedSmoke (ctx world work prepared)
open HasteBootsBatchMeaningSmoke (root usize)
open HasteBootsEarlyReceiptSmoke (view)
open HasteBootsRecoveredChallengeSmoke (parent parentValid batchFits responseFits)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
    (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)) := HasteBootsBatchMeaningSmoke.primitive
theorem count : view.field.count.val = NativeGoldBatchFieldMatrix.count ctx := by decide +kernel
example : NativeGoldBatchFieldMatrix.count ctx = 18 := by decide +kernel
example : ctx.parameters.width.val = 3 ∧ ctx.parameters.code.blockWidth.val = 4 := by decide +kernel

def numbered : Fin view.field.count.val → NativeFields.Goldilocks := fun index => index.val
-- Native lane-major layout: six source rows per lane, three lanes.
example : NativeGoldBatchFieldMatrix.reshape ctx view.field.count.val count numbered
    ⟨1,by decide +kernel⟩ (⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩) = 8 := by
  rw [NativeGoldBatchFieldMatrix.reshape_apply]
  decide +kernel
example : NativeGoldBatchFieldMatrix.reshape ctx view.field.count.val count numbered
    ⟨2,by decide +kernel⟩ (⟨1,by decide +kernel⟩,⟨0,by decide +kernel⟩) = 15 := by
  rw [NativeGoldBatchFieldMatrix.reshape_apply]
  decide +kernel
example (predicate : (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → NativeFields.Goldilocks) → Prop) :
    Pr{let vector ← $ᵗ (Fin view.field.count.val → NativeFields.Goldilocks)}[predicate (NativeGoldBatchFieldMatrix.reshape ctx view.field.count.val count vector)] =
      Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → NativeFields.Goldilocks)}[predicate matrix] :=
  NativeGoldBatchFieldMatrix.uniform_reshape ctx _ count predicate

def wrong : NativeGoldBatchFieldInputView.View := {view.field with count := usize 1}
theorem wrongCount : wrong.count.val ≠ NativeGoldBatchFieldMatrix.count ctx := by decide +kernel
example (vector : Fin wrong.count.val → NativeFields.Goldilocks) :
    ¬NativeGoldBatchFieldProximity.bad root ctx primitive 0 [] wrong vector := by
  simp only [NativeGoldBatchFieldProximity.bad,wrongCount,dite_false,not_false_eq_true]
example : NativeGoldBatchFieldProximity.score root ctx primitive 0 [] wrong = 0 := by
  simp only [NativeGoldBatchFieldProximity.score,wrongCount,false_and,ite_false]

theorem distance : Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
    ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) = 32 :=
  HasteBootsNativeRectangularSmoke.Probability.distance
-- The independent test width is the exponent of the whole quotient.
example : NativeGoldBatchFieldProximity.loss ctx primitive = (32 / (Fintype.card NativeFields.Goldilocks : ENNReal))^3 := by
  unfold NativeGoldBatchFieldProximity.loss
  rw [distance]
  rfl

def step (_ : Unit) : OracleMachine.Command Unit Unit := .read (NativeGoldBatchFirstFieldSource.input view.field) 999 1 (fun _ => ())
def packet : NativeIndexExposureRisk.Packet Unit Unit := (.inl (),[])
theorem first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchFirstFieldSource.input view.field) := by decide +kernel
def columnHistory : List NativeTranscript.Observation :=
  [.output (NativeGoldBatchFirstFieldSource.input view.field) 999 [0],.hash [77] (List.ofFn root)]
theorem recovered : NativeGoldBatchFirstFieldSource.recover root columnHistory view.field = some [] :=
  NativeGoldBatchFirstFieldSource.recover_at root [] [_] view.field 999 [0] rfl (by decide)

example (proximity : NativeGoldBatchConcreteCoverage.Proximity root ctx primitive view [] work.state 0) :
    NativeGoldBatchFieldProximity.event root ctx primitive 0 ctx.parent.profile step packet world :=
  NativeGoldBatchFieldProximityCoverage.later_proximity root ctx world work prepared HasteBootsFieldInputSmoke.parentFrames
    parent parentValid batchFits responseFits view HasteBootsFieldColumnSmoke.parsed primitive 0 step packet first columnHistory [] recovered
    999 [0] (by decide) [_] rfl proximity

example (history : List NativeTranscript.Observation) :
    Pr{let vector ← $ᵗ (Fin view.field.count.val → NativeFields.Goldilocks)}[
      NativeGoldBatchFieldProximity.bad root ctx primitive 0 history view.field vector] ≤
        NativeGoldBatchFieldProximity.score root ctx primitive 0 history view.field :=
  NativeGoldBatchFieldProximity.uniform_bound root ctx primitive 0 history view.field Fintype.card_pos (by rw [distance]; decide)

example {P S A : Type} {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (machine : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {other | ∃ fuel, NativeGoldBatchFieldProximity.event root ctx primitive 0 root machine
      (CausalExposureLifetime.history past initial machine fuel other).run other}) ≤
      law inherited + ∫⁻ other, NativeGoldBatchFieldProximity.totalCharge past initial root ctx primitive 0 machine other ∂law :=
  NativeGoldBatchFieldProximity.lifetime_le replay initial root ctx primitive 0 root machine inherited Fintype.card_pos (by rw [distance]; decide)
end
end HasteBootsFieldProximitySmoke
