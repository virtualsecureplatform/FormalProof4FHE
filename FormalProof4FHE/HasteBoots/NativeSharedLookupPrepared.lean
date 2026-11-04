module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupStatement

@[expose] public section

/-!
# Actual completed lookup producers feed shared statement jobs

Original request tags are paired with the actual completed sampler records.
The existing machine invariants discharge producer success and identify the
raw public table from the tag's original request. Neither raw challenge
words nor a row-identification/job-order certificate is supplied to the
initialized execution theorem. Full native child framing remains open.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupPrepared

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeSharedLookupStatement (Request Tagged Prepared tags)

noncomputable section

def prepare : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3) → List Tagged → Option (List Prepared)
  | [], [] => some []
  | completed :: tail, tag :: remaining =>
      (NativeGoldLookupProducer.produce completed.job.request.width tag.request.table completed.selection).bind
        (fun output => (prepare tail remaining).map (fun rest => ⟨tag, output⟩ :: rest))
  | _, _ => none

def guardJobs (prepared : List Prepared) : List NativeSharedLookupGuard.Job :=
  prepared.map (fun job => NativeSharedLookupGuard.Job.fromProduced job.tag.ordinal.val job.output)

private theorem one_success (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3)
    (valid : NativeLookupBatch.Valid goldilocksBasis machine) (roles : NativeLookupDrawHistory.BatchRoles machine)
    (completed : NativeLookupBatch.Completed goldilocksModulus Goldilocks3) (member : completed ∈ machine.completed)
    (tag : Tagged) (same : completed.job = tag.job) :
    ∃ output, NativeGoldLookupProducer.produce completed.job.request.width tag.request.table completed.selection = some output := by
  have terminal := (valid.2 completed member).2
  cases control : completed.selection.control with
  | compression field => simp only [NativeLookupBatch.Terminal, control] at terminal
  | reciprocal y weights table field => simp only [NativeLookupBatch.Terminal, control] at terminal
  | finished y r weights table transcript =>
    have rows : completed.job.request.rows = tag.request.table.map (List.map goldValue) := by rw [same]; rfl
    obtain ⟨output, done, _⟩ := NativeGoldLookupProducer.completed_success machine valid roles completed member y r weights table transcript
      control tag.request.table rows
    exact ⟨output, done⟩

theorem prepare_exists (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3)
    (valid : NativeLookupBatch.Valid goldilocksBasis machine) (roles : NativeLookupDrawHistory.BatchRoles machine)
    (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3))
    (contained : ∀ entry ∈ completed, entry ∈ machine.completed) (tagged : List Tagged)
    (aligned : completed.map (fun entry => entry.job) = tagged.map Tagged.job) : ∃ prepared, prepare completed tagged = some prepared := by
  induction completed generalizing tagged with
  | nil =>
    cases tagged with
    | nil => exact ⟨[], rfl⟩
    | cons tag tail => cases aligned
  | cons entry tail ih =>
    cases tagged with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at aligned
    | cons tag remaining =>
      have pair := List.cons.inj aligned
      obtain ⟨output, done⟩ := one_success machine valid roles entry (contained entry (List.mem_cons_self)) tag pair.1
      obtain ⟨rest, restDone⟩ := ih (fun entry member => contained entry (List.mem_cons_of_mem _ member)) remaining pair.2
      exact ⟨⟨tag, output⟩ :: rest, by rw [prepare, done, Option.bind_some, restDone, Option.map_some]⟩

/-- Successful preparation retains all original tags and each actual raw
producer call, in the completed sampler's order. -/
theorem prepare_spec (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3))
    (tagged : List Tagged) (prepared : List Prepared) (success : prepare completed tagged = some prepared) :
    prepared.map Prepared.tag = tagged ∧ List.Forall₂ (fun entry output =>
      NativeGoldLookupProducer.produce entry.job.request.width output.tag.request.table entry.selection = some output.output) completed prepared := by
  induction completed generalizing tagged prepared with
  | nil =>
    cases tagged with
    | nil => have same : [] = prepared := Option.some.inj success; subst prepared; exact ⟨rfl, .nil⟩
    | cons tag tail => contradiction
  | cons entry tail ih =>
    cases tagged with
    | nil => contradiction
    | cons tag remaining =>
      cases produced : NativeGoldLookupProducer.produce entry.job.request.width tag.request.table entry.selection with
      | none => simp only [prepare, produced, Option.bind_none] at success; contradiction
      | some output =>
        cases rest : prepare tail remaining with
        | none => simp only [prepare, produced, Option.bind_some, rest, Option.map_none] at success; contradiction
        | some outputs =>
          have same : Prepared.mk tag output :: outputs = prepared := Option.some.inj
            (by simpa only [prepare, produced, Option.bind_some, rest, Option.map_some] using success)
          rw [← same]
          have remainingSpec := ih remaining outputs rest
          exact ⟨by simpa only [List.map_cons] using congrArg (List.cons tag) remainingSpec.1,
            .cons produced remainingSpec.2⟩

/-- Initialized actual execution supplies success, ordering and every raw
producer/table identification; none is an independent input certificate. -/
theorem executed_prepare {count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request)
    (w fuel : ℕ) (transcript : NativeTranscript.Transcript) (world : InputIndexedOracle.World) (final : NativeTranscript.Transcript)
    (finished : (NativeLookupBatch.execute goldilocksBasis w fuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.control = .finished final) :
    ∃ prepared, prepare
      (NativeLookupBatch.execute goldilocksBasis w fuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed
      (tags fits requests) = some prepared ∧ prepared.map Prepared.tag = tags fits requests := by
  let actions := NativeLookupBatch.schedule fits (fun i => (requests i).sampling)
  let machine := (NativeLookupBatch.execute goldilocksBasis w fuel (NativeLookupBatch.initial actions transcript) world).1
  have valid := NativeLookupBatch.execute_valid goldilocksBasis w fuel _ world (NativeLookupBatch.initial_valid goldilocksBasis actions transcript)
  have roles := NativeLookupDrawHistory.execute_batch goldilocksBasis w fuel _ world (NativeLookupDrawHistory.initial_batch actions transcript)
  have order := NativeSharedLookupStatement.finished_jobs fits requests w fuel transcript world final finished
  obtain ⟨prepared, done⟩ := prepare_exists machine valid roles machine.completed (fun _ member => member) (tags fits requests) order
  exact ⟨prepared, done, (prepare_spec machine.completed (tags fits requests) prepared done).1⟩

theorem guard_requests (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3))
    (tagged : List Tagged) (prepared : List Prepared) (success : prepare completed tagged = some prepared) :
    (guardJobs prepared).map NativeSharedLookupGuard.Job.request = tagged.map (fun tag => tag.ordinal.val) := by
  have taggedEq := (prepare_spec completed tagged prepared success).1
  simp only [guardJobs, List.map_map, Function.comp_def, NativeSharedLookupGuard.Job.fromProduced]
  change prepared.map (fun job => job.tag.ordinal.val) = _
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun tag : Tagged => tag.ordinal.val)) taggedEq

/-- Actual prepared job tags align the independently constructed infos with
all table-sum/zero initial slots. Both native vectors keep their own bounds. -/
theorem build_dimensions {count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request)
    (n : NativeUsizeMessage.Usize) (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3))
    (prepared : List Prepared) (success : prepare completed (tags fits requests) = some prepared)
    (multiplicities : List (List GoldWord)) (statement : NativeScalarBatchWire.Statement)
    (built : NativeSharedLookupStatement.build n (List.ofFn requests) prepared multiplicities = some statement) :
    statement.infos.val.length = statement.claims.val.length ∧ statement.claims.val.length = 2 * prepared.length := by
  have spec := NativeSharedLookupStatement.build_spec n (List.ofFn requests) prepared multiplicities statement built
  have sums := NativeSharedLookupStatement.initialClaims_length multiplicities prepared statement.claims.val spec.2
  have tagLength := congrArg List.length ((prepare_spec completed (tags fits requests) prepared success).1)
  rw [List.length_map] at tagLength
  refine ⟨?_, sums⟩
  rw [spec.1, NativeSharedLookupStatement.infos_length_tags fits requests n, sums, tagLength]

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupPrepared
