module
public import FormalProof4FHE.HasteBoots.PrivateCoinClosedGoldRisk
@[expose] public section

/-! Joint events and expected-work bounds for countably valued finite private
initialization. Private coins and the oracle are sampled independently. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinInitialisation
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
noncomputable section

theorem event_measurable (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData)
    (event : (ClosedByteMachine.Tape → Input) → World → Prop)
    (sections : ∀ data, MeasurableSet {world | event data world}) :
    MeasurableSet {execution : Tape × World | event (privateData execution.1) execution.2} := by
  have equal : {execution : Tape × World | event (privateData execution.1) execution.2} =
      ⋃ data : ClosedByteMachine.Tape → Input, {tape | privateData tape = data} ×ˢ {world | event data world} := by
    ext execution
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod]
    constructor
    · exact fun yes => ⟨privateData execution.1, rfl, yes⟩
    · rintro ⟨data, same, yes⟩
      rwa [same]
  rw [equal]
  exact MeasurableSet.iUnion fun data =>
    (PrivateCoinClosedGoldRisk.data_fiber_measurable privateData finiteData data).prod (sections data)

/-- The conditional theorem must use the existing interpreter work on the
same private input; no success-conditioned work or new pricing is inserted. -/
theorem scaled_bound (coins : Measure Tape) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData)
    (event : (ClosedByteMachine.Tape → Input) → World → Prop)
    (sections : ∀ data, MeasurableSet {world | event data world})
    (scale : ENNReal) (finite : scale ≠ ⊤) (rate : ENNReal)
    (conditional : ∀ data, scale * law {world | event data world} ≤
      rate * ClosedByteMachineWork.expectedWork code publicData data) :
    scale * (coins.prod law) {execution : Tape × World | event (privateData execution.1) execution.2} ≤
      rate * PrivateCoinClosedWork.expectedWork coins code publicData privateData := by
  rw [Measure.prod_apply (event_measurable privateData finiteData event sections),
    ← lintegral_const_mul' scale _ finite]
  apply (lintegral_mono (fun tape => conditional (privateData tape))).trans_eq
  have meansMeasurable : Measurable (fun tape => ClosedByteMachineWork.expectedWork code publicData (privateData tape)) :=
    (PrivateCoinClosedWork.lifetimeWork_measurable code publicData privateData finiteData).lintegral_prod_right'
  rw [lintegral_const_mul _ meansMeasurable,
    ← PrivateCoinClosedWork.expectedWork_prod coins code publicData privateData finiteData]
end
end FormalProof4FHE.HasteBoots.PrivateCoinInitialisation
