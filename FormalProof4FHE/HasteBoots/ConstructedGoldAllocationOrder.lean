module
public import FormalProof4FHE.HasteBoots.ConstructedGoldObjectSetup
@[expose] public section

/-! Exact job identity and order in successful sequential parameter allocation.
No filtered successful-role list or independent handle association is assumed. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldAllocationOrder
open NativeGoldParameterStore (Entry)
open ConstructedGoldObjectSetup (Job allocate)

def entryJob (entry : Entry) : Job := ⟨entry.request,entry.header,entry.config⟩

theorem allocation_jobs (before : List Entry) (jobs : List Job) (after : List Entry)
    (executed : allocate before jobs = some (.ok after)) :
    after.map entryJob = before.map entryJob ++ jobs := by
  induction jobs generalizing before with
  | nil => cases executed; simp
  | cons job rest ih =>
    simp only [allocate] at executed
    cases allocated : NativeGoldParameterStore.allocate before job.request job.header job.config with
    | none => simp only [allocated] at executed; cases executed
    | some result =>
      cases result with
      | error error => simp only [allocated] at executed; cases executed
      | ok next =>
        simp only [allocated] at executed
        obtain ⟨_, _, _, shape⟩ := NativeGoldParameterStore.allocate_post before job.request job.header job.config next allocated
        have retained := ih next.entries executed
        rw [shape, List.map_append, List.map_singleton] at retained
        simpa only [entryJob, List.append_assoc, List.singleton_append] using retained

theorem initial_lookup (jobs : List Job) (after : List Entry) (executed : allocate [] jobs = some (.ok after))
    (position : ℕ) (job : Job) (selected : jobs[position]? = some job) :
    ∃ entry, after[position]? = some entry ∧ entryJob entry = job := by
  have retained := allocation_jobs [] jobs after executed
  simp only [List.map_nil, List.nil_append] at retained
  have found : (after[position]?).map entryJob = some job := by
    rw [← List.getElem?_map, retained]
    exact selected
  exact Option.map_eq_some_iff.mp found
end ConstructedGoldAllocationOrder
end FormalProof4FHE.HasteBoots
