module
public import FormalProof4FHE.HasteBoots.LookupReceiptLogs
@[expose] public section

/-! Active and completed original lookup jobs retain their actual receipt
reads in the ordered batch log across later jobs and arbitrary budgets. -/
namespace FormalProof4FHE.HasteBoots.LookupBatchReceiptLogs
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open LookupReceiptLogs (Reads)
noncomputable section

def Batch {p : ℕ} {K : Type} (world : World) (machine : NativeLookupBatch.Machine p K) (history : List Observation) : Prop :=
  (match machine.control with
  | .sampling _ _ selection => Reads world selection.draws history
  | _ => True) ∧ ∀ entry ∈ machine.completed, Reads world entry.selection.draws history

theorem mono {p : ℕ} {K : Type} (world : World) (machine : NativeLookupBatch.Machine p K)
    (earlier later : List Observation) (valid : Batch world machine earlier) (included : earlier.Sublist later) : Batch world machine later := by
  constructor
  · cases control : machine.control with
    | ready todo transcript => exact True.intro
    | finished transcript => exact True.intro
    | sampling job todo selection =>
      have active : Reads world selection.draws earlier := by simpa only [control] using valid.1
      simpa only [control] using LookupReceiptLogs.mono world selection.draws earlier later active included
  · exact fun entry member => LookupReceiptLogs.mono world _ earlier later (valid.2 entry member) included

theorem after_sample {p : ℕ} {K : Type} (world : World) (machine : NativeLookupBatch.Machine p K)
    (job : NativeLookupBatch.Job p) (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K)
    (history : List Observation) (selected : Reads world selection.draws history)
    (completed : ∀ entry ∈ machine.completed, Reads world entry.selection.draws history) :
    Batch world (NativeLookupBatch.afterSample machine job todo selection) history := by
  cases control : selection.control <;> simp only [NativeLookupBatch.afterSample,control,Batch]
  · exact ⟨selected,completed⟩
  · exact ⟨selected,completed⟩
  · refine ⟨True.intro,?_⟩
    intro entry member
    rcases List.mem_append.mp member with old | added
    · exact completed entry old
    · obtain rfl := List.mem_singleton.mp added
      exact selected

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (history : List Observation) (valid : Batch world machine history) :
    Batch world (NativeLookupBatch.tickExecute basis w machine world).1
      (history ++ (NativeLookupBatch.tickExecute basis w machine world).2) := by
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
        constructor
        · intro draw member
          cases member
        · exact fun entry member => LookupReceiptLogs.mono world _ history _ (valid.2 entry member) (List.sublist_append_left _ _)

  | sampling job todo selection =>
    have active : Reads world selection.draws history := by simpa only [control] using valid.1
    have selected := LookupReceiptLogs.tick basis w job.request.width job.request.rows selection world history active
    simpa only [NativeLookupBatch.tickExecute,control] using after_sample world machine job todo _ _ selected
      (fun entry member => LookupReceiptLogs.mono world _ history _ (valid.2 entry member) (List.sublist_append_left _ _))

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (history : List Observation) (valid : Batch world machine history) :
    Batch world (NativeLookupBatch.execute basis w fuel machine world).1
      (history ++ (NativeLookupBatch.execute basis w fuel machine world).2) := by
  induction fuel generalizing machine history with
  | zero => simpa only [NativeLookupBatch.execute,List.append_nil] using valid
  | succ fuel ih =>
    have later := ih _ _ (tick basis w machine world history valid)
    simpa only [NativeLookupBatch.execute,List.append_assoc] using later

theorem initialized (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) (world : World) :
    Batch world (NativeLookupBatch.execute basis w fuel (NativeLookupBatch.initial actions transcript) world).1
      (NativeLookupBatch.execute basis w fuel (NativeLookupBatch.initial actions transcript) world).2 := by
  simpa only [List.nil_append] using execute basis w fuel (NativeLookupBatch.initial actions transcript) world []
    ⟨True.intro,by simp [NativeLookupBatch.initial]⟩

end
end FormalProof4FHE.HasteBoots.LookupBatchReceiptLogs
