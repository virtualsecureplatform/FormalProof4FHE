module
import all FormalProof4FHE.HasteBoots.NativeEarlyReceiptBound
import all FormalProof4FHETest.HasteBootsEarlyReceiptSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law bytes)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsFreshReceiptSmoke
noncomputable section
open scoped Classical
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx work world)
open HasteBootsBatchMeaningSmoke (root)
open HasteBootsEarlyReceiptSmoke (step columnInput)

def cleanPast (_ : World) : NativeTranscript.Execution (Unit ⊕ Unit) := pure (.inl ())
theorem cleanReplay : ObservationReplay.Replayable cleanPast := ObservationReplay.pure_replay _
def cleanOption := NativeEarlyReceiptPrefixRisk.select step (cleanPast world).run
theorem present : cleanOption.isSome = true := by decide +kernel
def view := cleanOption.get present
theorem selected : NativeEarlyReceiptPrefixRisk.select step (cleanPast world).run = some view := (Option.some_get present).symm

-- The receipt key depends on the newly collected bytes, and is still fresh.
example (oracle : World) : CausalStreamExposure.seen (NativeFreshReceiptDigest.extended cleanPast root 18 step oracle).run.2
    (NativeReceiptPrefixView.key (NativeFreshReceiptDigest.collected root 18 view oracle).1.phase.consumed) = false :=
  NativeFreshReceiptDigest.unseen_extended root 18 step cleanPast oracle view selected rfl

example : NativeFreshReceiptDigest.event root 18 step (cleanPast world).run world := by
  unfold NativeFreshReceiptDigest.event
  rw [NativeFreshReceiptDigest.run_some root 18 step (cleanPast world).run world view selected]
  unfold NativeFreshReceiptDigest.after
  decide +kernel
example : NativeEarlyReceiptBound.finiteEvent root 18 step (cleanPast world).run world := by
  unfold NativeEarlyReceiptBound.finiteEvent
  rw [NativeFreshReceiptDigest.run_some root 18 step (cleanPast world).run world view selected]
  unfold NativeEarlyReceiptBound.matching
  decide +kernel
example : NativeEarlyReceiptBound.event root step (cleanPast world).run world := by
  refine ⟨18,?_⟩
  unfold NativeEarlyReceiptBound.finiteEvent
  rw [NativeFreshReceiptDigest.run_some root 18 step (cleanPast world).run world view selected]
  unfold NativeEarlyReceiptBound.matching
  decide +kernel

example : (law[|{oracle | (cleanPast oracle).run = (cleanPast world).run}])
    {oracle | NativeFreshReceiptDigest.event root 18 step (cleanPast oracle).run oracle} ≤ 1/(2 : ENNReal)^512 :=
  NativeFreshReceiptDigest.conditional_bound cleanReplay root 18 step world
example : (law[|{oracle | (cleanPast oracle).run = (cleanPast world).run}])
    {oracle | NativeFreshReceiptLifetime.ever root step (cleanPast oracle).run oracle} ≤
      NativeFreshReceiptLifetime.risk step (cleanPast world).run :=
  NativeFreshReceiptLifetime.conditional_ever_bound cleanReplay root step world
example : NativeEarlyReceiptBound.risk step (cleanPast world).run = 1/(2 : ENNReal)^512 := by
  rw [NativeEarlyReceiptBound.risk_selected step (cleanPast world).run view selected]
  change ((NativeReceiptPrefixView.guesses 72 []).card : ENNReal)/(2 : ENNReal)^576 + 1/(2 : ENNReal)^512 = _
  simp only [NativeReceiptPrefixView.guesses,List.filterMap_nil,List.toFinset_nil,Finset.card_empty,Nat.cast_zero,ENNReal.zero_div,zero_add]

-- Previously known receipt bytes go into the prefix branch, not the fresh branch.
open HasteBootsEarlyReceiptSmoke (past replay)
example : NativeEarlyReceiptBound.finiteEvent root 18 step (past world).run world := by
  unfold NativeEarlyReceiptBound.finiteEvent
  rw [NativeFreshReceiptDigest.run_some root 18 step (past world).run world HasteBootsEarlyReceiptSmoke.view HasteBootsEarlyReceiptSmoke.selected]
  unfold NativeEarlyReceiptBound.matching
  decide +kernel
example : ¬ NativeFreshReceiptDigest.event root 18 step (past world).run world := by
  unfold NativeFreshReceiptDigest.event
  rw [NativeFreshReceiptDigest.run_some root 18 step (past world).run world HasteBootsEarlyReceiptSmoke.view HasteBootsEarlyReceiptSmoke.selected]
  unfold NativeFreshReceiptDigest.after
  decide +kernel
example : NativeEarlyReceiptBound.risk step (past world).run = 1/(2 : ENNReal)^576 + 1/(2 : ENNReal)^512 := by
  rw [NativeEarlyReceiptBound.risk_selected step (past world).run HasteBootsEarlyReceiptSmoke.view HasteBootsEarlyReceiptSmoke.selected,
    HasteBootsEarlyReceiptSmoke.singleGuess]
  simp only [Nat.cast_one]
example : (law[|{oracle | (past oracle).run = (past world).run}])
    {oracle | NativeEarlyReceiptBound.event root step (past oracle).run oracle} ≤ 1/(2 : ENNReal)^576 + 1/(2 : ENNReal)^512 := by
  have bound := NativeEarlyReceiptBound.conditional_bound replay root step world
  rw [NativeEarlyReceiptBound.risk_selected step (past world).run HasteBootsEarlyReceiptSmoke.view HasteBootsEarlyReceiptSmoke.selected,
    HasteBootsEarlyReceiptSmoke.singleGuess] at bound
  simpa only [Nat.cast_one] using bound

-- Completion is stable under arbitrarily larger analysis budgets.
example : NativeFreshReceiptDigest.event root 18 step (cleanPast world).run world →
    NativeFreshReceiptDigest.event root 1000 step (cleanPast world).run world := by
  intro member
  exact NativeFreshReceiptLifetime.event_monotone root step (cleanPast world).run (show 18 ≤ 1000 by decide) member

-- The scope lemma includes rejected candidates and excludes the receipt domain.
open HasteBootsEarlyReceiptSmoke (tinyPhase tinyWorld)
example : CausalStreamExposure.seen (NativeFieldVector.execute 3 3 (NativeFieldVector.initial tinyPhase 2) tinyWorld).2
    (NativeReceiptPrefixView.key [3,1,2]) = false :=
  NativeFieldObservationScope.other_unseen 3 3 (NativeFieldVector.initial tinyPhase 2) tinyWorld _ (by decide +kernel)

-- The full lifetime event uses both unbounded machine and collector budgets.
example (prelude : World → NativeTranscript.Execution Unit) (rp : ObservationReplay.Replayable prelude) :
    law {oracle | ∃ fuel, NativeEarlyReceiptBound.event root step
      (CausalExposureLifetime.history prelude id step fuel oracle).run oracle} ≤
        ∫⁻ oracle, NativeEarlyReceiptBound.totalCharge prelude id step oracle ∂law := by
  simpa only [Set.empty_union,measure_empty,zero_add] using NativeEarlyReceiptBound.lifetime_le rp id root step ∅

-- Later stages see the complete old selecting history, not just its state.
example (oracle : World) : (NativeFreshReceiptDigest.extended past root 18 step oracle).run.1.1 = (past oracle).run := rfl
end
end HasteBootsFreshReceiptSmoke
