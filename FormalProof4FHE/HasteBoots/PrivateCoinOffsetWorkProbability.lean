module
public import FormalProof4FHE.HasteBoots.OffsetLifetimeWork
public import FormalProof4FHE.HasteBoots.OffsetContinuation
public import FormalProof4FHE.HasteBoots.PrivateCoinProgramPrefix
public import FormalProof4FHE.HasteBoots.CountableCoinOuterBound
@[expose] public section

/-! Joint private-tape/oracle reciprocal lifetime work probabilities. Finite strategy
selection supplies measurable envelopes; the native existential events need
not be assumed measurable. All original tape mass is retained. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
noncomputable section

def Event (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  OffsetLifetimeWork.Event (privateProgram code publicData execution.1 privateData fuel) dummy execution.2

def Bad (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2

theorem prefix_safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (fuel : ℕ) :
    (coins.prod law) {execution | Event code publicData privateData dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * LookupStreamWorkRate.rate := by
  let sectionEvent := fun values : Fin fuel → InputIndexedOracle.Byte => {world |
    let program := privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel values) privateData fuel
    OffsetLifetimeWork.Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world}
  have same (tape : Tape) : privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel
      (PrivateCoinProgramPrefix.select fuel tape)) privateData fuel = privateProgram code publicData tape privateData fuel :=
    PrivateCoinProgramPrefix.selected_program code publicData privateData fuel tape
  have equal : {execution | Event code publicData privateData dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} =
      {execution : Tape × World | execution.2 ∈ sectionEvent (PrivateCoinProgramPrefix.select fuel execution.1)} := by
    ext execution
    simp only [sectionEvent,same,Event,Bad,Set.mem_ofPred_eq]
  rw [equal]
  apply (CountableCoinOuterBound.bound coins _ (PrivateCoinProgramPrefix.select_measurable fuel) sectionEvent
    (fun tape => ∫⁻ world, PrivateCoinByteWork.lifetimeWork code publicData privateData (tape,world)*LookupStreamWorkRate.rate ∂law) ?_).trans
  · calc
      _ = ∫⁻ execution, PrivateCoinByteWork.lifetimeWork code publicData privateData execution*LookupStreamWorkRate.rate ∂coins.prod law := by
        exact (lintegral_prod _ ((PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).mul_const LookupStreamWorkRate.rate).aemeasurable).symm
      _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * LookupStreamWorkRate.rate := lintegral_mul_const LookupStreamWorkRate.rate (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)
      _ ≤ _ := le_rfl
  · intro tape
    change law {world | OffsetLifetimeWork.Event _ dummy world ∧ ¬GlobalReferenceBad.Bad _ dummy world} ≤ _
    rw [same]
    have bounded := OffsetLifetimeWork.private_safe_probability code publicData tape privateData fuel dummy
    change _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * LookupStreamWorkRate.rate ∂law
    rw [lintegral_mul_const LookupStreamWorkRate.rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)]
    exact bounded

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * LookupStreamWorkRate.rate := by
  let events := fun fuel => {execution : Tape × World | Event code publicData privateData dummy fuel execution ∧
    ¬∃ horizon, Bad code publicData privateData dummy horizon execution}
  have monotone : Monotone events := by
    intro first later ordered execution occurred
    exact ⟨OffsetContinuation.private_monotone code publicData execution.1 privateData dummy ordered occurred.1,occurred.2⟩
  have union : {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} = ⋃ fuel, events fuel := by
    ext execution
    simp only [events,Set.mem_ofPred_eq,Set.mem_iUnion,exists_and_right]
  rw [union,monotone.measure_iUnion]
  apply iSup_le
  intro fuel
  apply (measure_mono (show events fuel ⊆ {execution | Event code publicData privateData dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} from ?_)).trans (prefix_safe_bound coins code publicData privateData dummy fuel)
  intro execution occurred
  exact ⟨occurred.1,fun bad => occurred.2 ⟨fuel,bad⟩⟩

theorem bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (coins.prod law) {execution | ∃ fuel, Event code publicData privateData dummy fuel execution} ≤
      (coins.prod law) {execution | ∃ fuel, Bad code publicData privateData dummy fuel execution} +
        PrivateCoinByteWork.expectedWork coins code publicData privateData * LookupStreamWorkRate.rate := by
  have included : {execution | ∃ fuel, Event code publicData privateData dummy fuel execution} ⊆
      {execution | ∃ fuel, Bad code publicData privateData dummy fuel execution} ∪
      {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, Bad code publicData privateData dummy fuel execution} := by
    intro execution occurred
    by_cases bad : ∃ fuel, Bad code publicData privateData dummy fuel execution
    · exact Or.inl bad
    · exact Or.inr ⟨occurred,bad⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (safe_bound coins code publicData privateData dummy)))

/-- The safe reciprocal branch, aggregated over all original inputs, jobs,
positions, retry budgets, private tapes and horizons, pays specified work. -/
theorem safe_work_132 (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (2 : ENNReal)^132 * (coins.prod law)
      {execution | (∃ fuel, Event code publicData privateData dummy fuel execution) ∧
        ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^132 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * LookupStreamWorkRate.rate) :=
      mul_le_mul' le_rfl (safe_bound coins code publicData privateData dummy)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^132*(1/(2 : ENNReal)^132)) := by
      rw [LookupStreamWorkRate.rate]
      ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.PrivateCoinOffsetWorkProbability
