module
public import FormalProof4FHE.HasteBoots.LookupReceiptLabels
@[expose] public section

/-! Every completed native batch job supplies its compression-headed receipt
group. Repetitions and actual completion order are retained. -/
namespace FormalProof4FHE.HasteBoots.LookupBatchReceiptLabels
open InputIndexedOracle (World)
open LookupReceiptLabels (Labels Group)
noncomputable section

def Batch {p : ℕ} {K : Type} (machine : NativeLookupBatch.Machine p K) : Prop :=
  (match machine.control with
  | .sampling _ _ selection => Labels selection
  | _ => True) ∧ ∀ entry ∈ machine.completed, Group entry.selection.draws

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) :
    Batch (NativeLookupBatch.initial (K := K) actions transcript) := ⟨True.intro,by simp [NativeLookupBatch.initial]⟩

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem after_sample (machine : NativeLookupBatch.Machine p K) (job : NativeLookupBatch.Job p)
    (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K)
    (valid : Batch machine) (selected : Labels selection) :
    Batch (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control <;> simp only [NativeLookupBatch.afterSample,control,Batch]
  · exact ⟨selected,valid.2⟩
  · exact ⟨selected,valid.2⟩
  · refine ⟨True.intro,?_⟩
    intro entry member
    rcases List.mem_append.mp member with old | added
    · exact valid.2 entry old
    · obtain rfl := List.mem_singleton.mp added
      simpa only [Labels,control] using selected

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (valid : Batch machine) :
    Batch (NativeLookupBatch.tickExecute basis w machine world).1 := by
  cases control : machine.control with
  | finished transcript => simpa only [NativeLookupBatch.tickExecute,control] using valid
  | ready todo transcript =>
    cases todo with
    | nil => simpa only [NativeLookupBatch.tickExecute,control,Batch] using And.intro True.intro valid.2
    | cons action todo =>
      cases action with
      | request ordinal => simpa only [NativeLookupBatch.tickExecute,control,Batch] using And.intro True.intro valid.2
      | sample job =>
        simpa only [NativeLookupBatch.tickExecute,control,Batch] using
          And.intro (LookupReceiptLabels.initial p degree w transcript) valid.2
  | sampling job todo selection =>
    have active : Labels selection := by simpa only [control] using valid.1
    simpa only [NativeLookupBatch.tickExecute,control] using after_sample machine job todo _ valid
      (LookupReceiptLabels.tick basis w job.request.width job.request.rows selection world active)

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (valid : Batch machine) :
    Batch (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w machine world valid)

end
end FormalProof4FHE.HasteBoots.LookupBatchReceiptLabels
