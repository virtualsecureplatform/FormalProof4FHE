module

public import FormalProof4FHE.HasteBoots.NativeTupleLookupConfig

@[expose] public section

/-!
# Ordered canonical request rebuilding

The caller rebuilds every trusted configuration under the first source's
backend normalization and clones its original slots. Both policies retain
semantic tables, row count/order, logical lengths and repetition counts.
Only the canonicalizing policy changes raw table bytes. Those actual bytes
must be used by the later request/context transcript binding.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupConfig

open NativeFields NativeFieldRepresentation NativeFieldWire
open NativeSharedLookupValues (Policy)
open NativeSharedLookupStatement (Request)

abbrev Valid (requests : List Request) : Prop :=
  ∀ request ∈ requests, NativeTupleLookupConfig.Spec request.terminal.logicalLength request.repetitions request.table ∧
    request.columns = NativeTupleLookupConfig.columns request.table

def rebuild (policy : Policy) : List Request → Option (List Request)
  | [] => some []
  | request :: tail => (NativeTupleLookupConfig.rebuild policy request).bind (fun rebuilt =>
      (rebuild policy tail).map (fun remaining => rebuilt :: remaining))

theorem rebuild_calls (policy : Policy) (requests outputs : List Request) (success : rebuild policy requests = some outputs) :
    List.Forall₂ (fun request output => NativeTupleLookupConfig.rebuild policy request = some output) requests outputs := by
  induction requests generalizing outputs with
  | nil => have same : [] = outputs := Option.some.inj success; subst outputs; exact .nil
  | cons request tail ih =>
    cases built : NativeTupleLookupConfig.rebuild policy request with
    | none => simp only [rebuild,built,Option.bind_none] at success; contradiction
    | some output =>
      cases rest : rebuild policy tail with
      | none => simp only [rebuild,built,Option.bind_some,rest,Option.map_none] at success; contradiction
      | some remaining =>
        have same : output :: remaining = outputs := Option.some.inj
          (by simpa only [rebuild,built,Option.bind_some,rest,Option.map_some] using success)
        rw [← same]
        exact .cons built (ih remaining rest)

theorem rebuild_valid (policy : Policy) (requests outputs : List Request) (success : rebuild policy requests = some outputs) : Valid outputs := by
  have calls := rebuild_calls policy requests outputs success
  clear success
  induction calls with
  | nil => simp [Valid]
  | @cons request output tail remaining built calls ih =>
    intro entry member
    rcases List.mem_cons.mp member with same | rest
    · subst entry
      have spec := NativeTupleLookupConfig.rebuild_spec policy request output built
      refine ⟨spec.2.2.2.2,?_⟩
      rw [spec.1,NativeTupleLookupConfig.columns_normalize]
      exact spec.2.1
    · exact ih entry rest

/-- The complete ordered request list retains the same repetitions, slots
and semantic public table at every position; no normalization drops a row. -/
theorem rebuild_preserves (policy : Policy) (requests outputs : List Request) (success : rebuild policy requests = some outputs) :
    List.Forall₂ (fun request output => output.repetitions = request.repetitions ∧ output.terminal = request.terminal ∧
      output.table.map (List.map goldValue) = request.table.map (List.map goldValue)) requests outputs := by
  apply (rebuild_calls policy requests outputs success).imp
  intro request output built
  have spec := NativeTupleLookupConfig.rebuild_spec policy request output built
  refine ⟨spec.2.2.1,spec.2.2.2.1,?_⟩
  rw [spec.1]
  exact NativeTupleLookupConfig.normalizeTable_value policy request.table

/-- Semantic sampling actions agree when the original input is in the native
num_columns domain. This does not equate raw request transcript encodings. -/
theorem sampling_preserved (policy : Policy) (request output : Request)
    (success : NativeTupleLookupConfig.rebuild policy request = some output)
    (width : request.columns = NativeTupleLookupConfig.columns request.table) : output.sampling = request.sampling := by
  have spec := NativeTupleLookupConfig.rebuild_spec policy request output success
  unfold NativeSharedLookupStatement.Request.sampling
  rw [spec.2.1,← width,spec.2.2.1,spec.1,NativeTupleLookupConfig.normalizeTable_value]

/-- The constructor's nonzero repetitions remove the isolated preflight's
zero-job case, using the original computed repetition total. -/
theorem repetitions_positive (policy : Policy) (original requests : List Request)
    (rebuilt : rebuild policy original = some requests)
    (registry : List NativeLookupBindGeometry.Parameters) (helper : NativeLookupBindGeometry.Parameters)
    (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper requests = some geometry) : geometry.repetitions.val ≠ 0 := by
  have valid := rebuild_valid policy original requests rebuilt
  have accepted := NativeSharedLookupPreflight.preflight_spec registry helper requests geometry preflight
  cases requests with
  | nil => exact (accepted.dimensions.2.1 rfl).elim
  | cons request tail =>
    have positive := (valid request List.mem_cons_self).1.positiveRepetitions
    have total := accepted.repetitions
    simp only [List.map_cons,List.sum_cons] at total
    omega

end FormalProof4FHE.HasteBoots.NativeSharedLookupConfig
