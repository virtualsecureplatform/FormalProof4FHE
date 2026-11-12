module
public import FormalProof4FHE.HasteBoots.LookupScalarKernel
public import FormalProof4FHE.HasteBoots.LookupProducerOrdinal
@[expose] public section

/-! Original batch scheduling retains each job's initialized scalar collector
trace. Completed jobs and rejected offsets remain associated with their actual
prepared-job ordinal, with every raw read embedded in the batch history. -/
namespace FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace
open InputIndexedOracle (World)
open NativeTranscript (Observation Transcript)
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open LookupCollectorTrace (Traced)
noncomputable section

def Batch (world : World) (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (history : List Observation) : Prop :=
  (match machine.control with
  | .sampling _ _ selection => Traced selection world history
  | _ => True) ∧ ∀ entry ∈ machine.completed, Traced entry.selection world history

theorem after_sample (world : World) (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3)
    (job : NativeLookupBatch.Job goldilocksModulus) (todo : List (NativeLookupBatch.Action goldilocksModulus))
    (selection : NativeLookupChallenge.Machine Goldilocks3) (history : List Observation)
    (selected : Traced selection world history)
    (completed : ∀ entry ∈ machine.completed, Traced entry.selection world history) :
    Batch world (NativeLookupBatch.afterSample machine job todo selection) history := by
  cases control : selection.control <;> simp only [NativeLookupBatch.afterSample,control,Batch]
  · exact ⟨selected,completed⟩
  · exact ⟨selected,completed⟩
  · refine ⟨True.intro,?_⟩
    intro entry member
    rcases List.mem_append.mp member with earlier | added
    · exact completed entry earlier
    · cases List.mem_singleton.mp added
      exact selected

theorem tick (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (world : World)
    (history : List Observation) (valid : Batch world machine history) :
    Batch world (NativeLookupBatch.tickExecute goldilocksBasis 7 machine world).1
      (history++(NativeLookupBatch.tickExecute goldilocksBasis 7 machine world).2) := by
  cases control : machine.control with
  | finished transcript => simpa only [NativeLookupBatch.tickExecute,control,List.append_nil] using valid
  | ready todo transcript =>
    cases todo with
    | nil => simpa only [NativeLookupBatch.tickExecute,control,Batch,List.append_nil] using And.intro True.intro valid.2
    | cons action todo =>
      cases action with
      | request ordinal => simpa only [NativeLookupBatch.tickExecute,control,Batch,List.append_nil] using And.intro True.intro valid.2
      | sample job =>
        simp only [NativeLookupBatch.tickExecute,control,Batch]
        exact ⟨⟨LookupCollectorTrace.begin_source _ _ world _,by simp [NativeLookupChallenge.initialExecute]⟩,
          fun entry member => LookupCollectorTrace.traced_mono _ world history _ (valid.2 entry member) (List.sublist_append_left _ _)⟩
  | sampling job todo selection =>
    have active : Traced selection world history := by simpa only [control] using valid.1
    have selected := LookupCollectorTrace.tick job.request.width job.request.rows selection world history active
    simpa only [NativeLookupBatch.tickExecute,control] using after_sample world machine job todo _ _ selected
      (fun entry member => LookupCollectorTrace.traced_mono _ world history _ (valid.2 entry member) (List.sublist_append_left _ _))

theorem execute (fuel : ℕ) (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (world : World)
    (history : List Observation) (valid : Batch world machine history) :
    Batch world (NativeLookupBatch.execute goldilocksBasis 7 fuel machine world).1
      (history++(NativeLookupBatch.execute goldilocksBasis 7 fuel machine world).2) := by
  induction fuel generalizing machine history with
  | zero => simpa only [NativeLookupBatch.execute,List.append_nil] using valid
  | succ fuel ih =>
    simpa only [NativeLookupBatch.execute,List.append_assoc] using ih _ _ (tick machine world history valid)

theorem initialized (fuel : ℕ) (actions : List (NativeLookupBatch.Action goldilocksModulus))
    (transcript : Transcript) (world : World) :
    Batch world (NativeLookupBatch.execute goldilocksBasis 7 fuel (NativeLookupBatch.initial actions transcript) world).1
      (NativeLookupBatch.execute goldilocksBasis 7 fuel (NativeLookupBatch.initial actions transcript) world).2 := by
  simpa only [List.nil_append] using execute fuel (NativeLookupBatch.initial actions transcript) world []
    (show Batch world (NativeLookupBatch.initial actions transcript) [] from ⟨True.intro,by simp [NativeLookupBatch.initial]⟩)

end
end FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace
