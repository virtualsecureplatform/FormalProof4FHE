module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnWitness
import all FormalProof4FHETest.HasteBootsFirstFieldSourceSmoke
import all FormalProof4FHETest.HasteBootsFixedResponseSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (World law)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsConcreteColumnSmoke
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx world)
open HasteBootsBatchMeaningSmoke (root)
open HasteBootsEarlyReceiptSmoke (view step columnInput)
open HasteBootsFieldColumnSmoke (past replay first parsed)

theorem primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
    (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)) := HasteBootsBatchMeaningSmoke.primitive
local instance : NeZero ctx.parameters.code.blockWidth.val := ⟨by decide +kernel⟩
example : Fintype.card (NativeGoldBatchConcreteColumnFamily.Test ctx view) = 6 := by decide +kernel
example (state : NativeFieldVector.State) (test : NativeGoldBatchConcreteColumnFamily.Test ctx view) :
    NativeGoldBatchConcreteColumnFamily.claim ctx primitive view state test ∈
      BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :=
  NativeGoldBatchConcreteColumnFamily.coded ctx primitive view state test

theorem selected : NativeGoldBatchConcreteColumnExposure.select ctx step (past world).run = some view := by
  unfold NativeGoldBatchConcreteColumnExposure.select
  simp only [first,Option.bind_eq_bind,Option.bind_some,parsed]
  exact ite_eq_left (by decide +kernel)
theorem recovered : NativeGoldBatchFirstFieldSource.recover root (past world).run.2 view.field = some [] := by decide +kernel

theorem distanceZero : NativeGoldBatchConcreteColumnBound.distance ctx primitive 0 = 1 := by
  have codeDistance : Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) = 32 :=
    HasteBootsNativeRectangularSmoke.Probability.distance
  simp only [NativeGoldBatchConcreteColumnBound.distance,codeDistance,Nat.sub_zero,Nat.reduceAdd]
  decide

example : NativeGoldBatchConcreteColumnExposure.risk root ctx primitive step (past world).run 0 = ((31 : ENNReal)/32)^3 := by
  simp only [NativeGoldBatchConcreteColumnExposure.risk,selected,recovered]
  rw [distanceZero]
  have quota : view.column.index.count.val = 3 := by decide +kernel
  have bits : NativeGoldBlockCode.logSize ctx.parameters.code = 5 := by decide +kernel
  simp only [ColumnOpening.missBound,NativeGoldBatchConcreteColumnFamily.Position,Fintype.card_fin,quota,bits]
  rfl
example : (law[|{other | (past other).run = (past world).run}])
    {other | NativeGoldBatchConcreteColumnExposure.event root ctx primitive root step (past other).run 0 other} ≤
      NativeGoldBatchConcreteColumnExposure.risk root ctx primitive step (past world).run 0 :=
  NativeGoldBatchConcreteColumnExposure.conditional_bound replay root ctx primitive root step world 0

-- A source absent from the old history is left for early-receipt coverage.
example : NativeGoldBatchConcreteColumnExposure.risk root ctx primitive step (HasteBootsFreshReceiptSmoke.cleanPast world).run 0 = 0 := by
  have chosen : NativeGoldBatchConcreteColumnExposure.select ctx step (HasteBootsFreshReceiptSmoke.cleanPast world).run = some view := by
    unfold NativeGoldBatchConcreteColumnExposure.select
    have firstClean : CausalStreamExposure.firstRead step (HasteBootsFreshReceiptSmoke.cleanPast world).run = some columnInput := by decide +kernel
    simp only [firstClean,Option.bind_eq_bind,Option.bind_some,parsed]
    exact ite_eq_left (by decide +kernel)
  have unseen : NativeGoldBatchFirstFieldSource.recover root (HasteBootsFreshReceiptSmoke.cleanPast world).run.2 view.field = none :=
    (NativeGoldBatchFirstFieldSource.recover_none _ _ _).mpr rfl
  simp only [NativeGoldBatchConcreteColumnExposure.risk,chosen,unseen]

-- Repeating a positive read at a far offset cannot create a second charge.
def repeated := CausalExposureLifetime.history past (fun _ => ()) step 1 world
example : NativeGoldBatchConcreteColumnExposure.risk root ctx primitive step repeated.run 0 = 0 := by
  have absent : (NativeGoldBatchConcreteColumnExposure.select ctx step repeated.run).isNone = true := by decide +kernel
  cases chosen : NativeGoldBatchConcreteColumnExposure.select ctx step repeated.run with
  | none => simp only [NativeGoldBatchConcreteColumnExposure.risk,chosen]
  | some decoded => rw [chosen] at absent; contradiction

example (radius : ℕ) : ColumnOpening.missBound (NativeGoldBatchConcreteColumnFamily.Position ctx) view.column.index.count.val
    (NativeGoldBatchConcreteColumnBound.distance ctx primitive radius) =
      max (ColumnOpening.missBound (NativeGoldBatchConcreteColumnFamily.Position ctx) view.column.index.count.val
        (Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
          Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) - radius))
        (ColumnOpening.missBound (NativeGoldBatchConcreteColumnFamily.Position ctx) view.column.index.count.val (radius+1)) :=
  NativeGoldBatchConcreteColumnBound.miss_min ctx _ _ _

-- The source used by the concrete event is unchanged by any later suffix.
example (suffix : List NativeTranscript.Observation) (other : World) :
    NativeGoldBatchConcreteColumnBound.event root ctx primitive root view ((past world).run.2++suffix) 0 other ↔
      NativeGoldBatchConcreteColumnBound.event root ctx primitive root view (past world).run.2 0 other :=
  NativeGoldBatchConcreteColumnBound.event_append root ctx primitive root view _ suffix 0 other [] recovered

example {P S A : Type} {prelude : World → NativeTranscript.Execution P} (rp : ObservationReplay.Replayable prelude)
    (initial : P → S) (machine : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {other | ∃ fuel, NativeGoldBatchConcreteColumnExposure.event root ctx primitive root machine
      (CausalExposureLifetime.history prelude initial machine fuel other).run 0 other}) ≤
      law inherited + ∫⁻ other, NativeGoldBatchConcreteColumnExposure.totalCharge prelude initial root ctx primitive machine 0 other ∂law :=
  NativeGoldBatchConcreteColumnExposure.lifetime_le rp initial root ctx primitive root machine 0 inherited
end
end HasteBootsConcreteColumnSmoke
