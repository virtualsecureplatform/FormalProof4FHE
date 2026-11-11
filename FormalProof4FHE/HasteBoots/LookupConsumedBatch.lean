module
public import FormalProof4FHE.HasteBoots.LookupConsumedTrace
public import FormalProof4FHE.HasteBoots.NativeLookupBatch
@[expose] public section

/-! The complete consumed-byte invariant follows actual ordered batch jobs,
including repeated requests, active suspension and completed selections. -/
namespace FormalProof4FHE.HasteBoots.LookupConsumedBatch
open LookupConsumedTrace (Lookup)
open InputIndexedOracle (World)
noncomputable section
variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

def Traced (machine : NativeLookupBatch.Machine p K) : Prop :=
  (match machine.control with
    | .sampling _ _ selection => Lookup p selection
    | _ => True) ∧
    ∀ completed ∈ machine.completed, Lookup p completed.selection

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) :
    Traced (NativeLookupBatch.initial (K := K) actions transcript) :=
  ⟨True.intro,by simp [NativeLookupBatch.initial]⟩

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem after_sample (machine : NativeLookupBatch.Machine p K) (job : NativeLookupBatch.Job p)
    (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K)
    (valid : Traced machine) (selected : Lookup p selection) :
    Traced (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control <;>
    simp only [NativeLookupBatch.afterSample,control,Traced]
  · exact ⟨selected,valid.2⟩
  · exact ⟨selected,valid.2⟩
  · refine ⟨True.intro,?_⟩
    intro completed member
    rcases List.mem_append.mp member with old | added
    · exact valid.2 completed old
    · obtain rfl := List.mem_singleton.mp added
      exact selected

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (valid : Traced machine) :
    Traced (NativeLookupBatch.tickExecute basis w machine world).1 := by
  cases control : machine.control with
  | finished transcript => simpa only [NativeLookupBatch.tickExecute,control] using valid
  | ready todo transcript =>
    cases todo with
    | nil => simpa only [NativeLookupBatch.tickExecute,control,Traced] using And.intro True.intro valid.2
    | cons action todo =>
      cases action with
      | request ordinal => simpa only [NativeLookupBatch.tickExecute,control,Traced] using And.intro True.intro valid.2
      | sample job =>
        simpa only [NativeLookupBatch.tickExecute,control,Traced] using
          And.intro (LookupConsumedTrace.lookup_initial p degree w transcript) valid.2
  | sampling job todo selection =>
    have active : Lookup p selection := by simpa only [control] using valid.1
    simpa only [NativeLookupBatch.tickExecute,control] using
      after_sample machine job todo _ valid
        (LookupConsumedTrace.lookup_tick basis w job.request.width job.request.rows selection world active)

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (valid : Traced machine) :
    Traced (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w machine world valid)

theorem completed (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) (world : World)
    (entry : NativeLookupBatch.Completed p K)
    (member : entry ∈ (NativeLookupBatch.execute basis w fuel (NativeLookupBatch.initial actions transcript) world).1.completed) :
    Lookup p entry.selection :=
  (execute basis w fuel _ world (initial actions transcript)).2 entry member

end
end FormalProof4FHE.HasteBoots.LookupConsumedBatch
