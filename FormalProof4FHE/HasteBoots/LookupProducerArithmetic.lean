module
public import FormalProof4FHE.HasteBoots.LookupInitialArithmetic
@[expose] public section

/-! Successful raw production itself enforces the reciprocal domain and
identifies the literal public total. No scalar-acceptance or producer-value
certificate is required. Original ragged-row and zip semantics are retained. -/
namespace FormalProof4FHE.HasteBoots.LookupProducerArithmetic
open scoped BigOperators
open NativeGoldLookupProducer (Output produce)
open NativeGoldExtensionArithmetic (Word)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (Goldilocks3)
noncomputable section

theorem produced {width : ℕ} {rows : List (List GoldWord)}
    {selection : NativeLookupChallenge.Machine Goldilocks3} {output : Output}
    (success : produce width rows selection = some output) :
    output.table = NativeGoldLookup.tableAt rows width output.y ∧
      goldExtensionValue output.r ≠ 0 ∧
      (∀ value ∈ output.table.map goldExtensionValue, goldExtensionValue output.r + value ≠ 0) ∧
      output.inverses.map goldExtensionValue = NativeLookupReciprocals.inverses .individual
        (goldExtensionValue output.r) (output.table.map goldExtensionValue) := by
  unfold produce at success
  obtain ⟨sources,_,rest⟩ := Option.bind_eq_some_iff.mp success
  by_cases allowed : NativeGoldLookup.allowed (rows.map (NativeGoldLookup.compress
      (NativeGoldLookup.powerRun sources.1 width).1)) sources.2 = true
  · rw [ite_eq_left allowed] at rest
    obtain ⟨inverses,found,same⟩ := Option.map_eq_some_iff.mp rest
    subst output
    obtain ⟨correct,correctAt,related⟩ := NativeGoldLookup.accepted_reciprocals _ _ allowed
    have equal : inverses = correct := Option.some.inj (found.symm.trans correctAt)
    have domain := (NativeLookupChallenge.allowed_iff _ _).mp
      (by rw [← NativeGoldLookup.allowed_value]; exact allowed)
    exact ⟨rfl,domain.1,domain.2,by simpa only [equal] using related⟩
  · rw [ite_eq_right allowed] at rest
    contradiction

theorem public_total {width : ℕ} {rows : List (List GoldWord)}
    {selection : NativeLookupChallenge.Machine Goldilocks3} {output : Output}
    (success : produce width rows selection = some output) (counts : List GoldWord) :
    goldExtensionValue (NativeGoldExtensionArithmetic.tableSum output.inverses counts) =
      NativeLookupArithmetic.tableSum .individual (goldExtensionValue output.r)
        (NativeLookupChallenge.tableAt (rows.map (List.map goldValue)) width (goldExtensionValue output.y))
        (counts.map goldValue) := by
  have spec := produced success
  have total := NativeGoldLookup.tableSum_value (goldExtensionValue output.r)
    (output.table.map goldExtensionValue) output.inverses counts spec.2.2.2
  rw [spec.1,NativeGoldLookup.tableAt_value] at total
  exact total

/-- Rectangular original public rows and counts give the finite reciprocal
sum used by lookup soundness. Allowed-domain evidence comes from production. -/
theorem public_total_vectors {width size : ℕ}
    (table : Fin size → Fin width → GoldWord) (counts : Fin size → GoldWord)
    {selection : NativeLookupChallenge.Machine Goldilocks3} {output : Output}
    (success : produce width (List.ofFn (fun i => List.ofFn (table i))) selection = some output) :
    goldExtensionValue (NativeGoldExtensionArithmetic.tableSum output.inverses (List.ofFn counts)) =
      LookupPairArithmetic.tableSum (goldExtensionValue output.r) (goldExtensionValue output.y)
        (fun i j => goldValue (table i j)) (fun i => goldValue (counts i)) := by
  have spec := produced success
  have domain : NativeLookupChallenge.allowed
      (NativeLookupChallenge.tableAt
        (List.ofFn (fun i => List.ofFn (fun j => goldValue (table i j)))) width (goldExtensionValue output.y))
      (goldExtensionValue output.r) = true := by
    apply (NativeLookupChallenge.allowed_iff _ _).mpr
    constructor
    · exact spec.2.1
    · have poles := spec.2.2.1
      rw [spec.1,NativeGoldLookup.tableAt_value] at poles
      simpa only [List.map_ofFn,Function.comp_def] using poles
  have total := public_total success (List.ofFn counts)
  simp only [List.map_ofFn,Function.comp_def] at total
  exact total.trans (NativeLookupArithmetic.tableSum_eq .individual _ _ _ _ domain)

/-- A nonpassing reciprocal relation over the original rectangular public
rows forces a native arithmetic obstruction. Both nonzero r and the literal
public total are recovered from this job's raw producer success. -/
theorem job_obstruction {Memory A : Type} {ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A}
    {world : InputIndexedOracle.World} {size : ℕ}
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : NativeRootMessage.Digest)
    (table : Fin size → Fin (data.origin.ready.jobs.get data.index).tag.request.columns → GoldWord)
    (counts : Fin size → GoldWord)
    (tableRows : (data.origin.ready.jobs.get data.index).tag.request.table = List.ofFn (fun i => List.ofFn (table i)))
    (notPasses : ¬ReciprocalDetection.Passes
      (LookupReciprocalEnforcement.activeSource (Nat.add_sub_of_le data.job.view.enough) (LookupInitialArithmetic.source data dummy))
      (fun i => TupleHash.hash (goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (fun j => goldValue (table i j)))
      (fun i => algebraMap NativeFields.Goldilocks Goldilocks3 (goldValue (counts i)))
      (goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)) :
    (∑ cell, LookupInitialArithmetic.helper data dummy cell) ≠ goldExtensionValue
      (NativeGoldExtensionArithmetic.tableSum (data.origin.ready.jobs.get data.index).output.inverses (List.ofFn counts)) ∨
      ∃ cell, LookupInitialArithmetic.residual data dummy cell ≠ 0 := by
  have success := data.job.view.produced
  rw [tableRows] at success
  have total := public_total_vectors table counts success
  have bad := LookupReciprocalEnforcement.not_passes_obstruction
    (Nat.add_sub_of_le data.job.view.enough)
    (goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)
    (LookupInitialArithmetic.source data dummy) (LookupInitialArithmetic.helper data dummy)
    (fun i => TupleHash.hash (goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) (fun j => goldValue (table i j)))
    (fun i => algebraMap NativeFields.Goldilocks Goldilocks3 (goldValue (counts i)))
    (produced success).2.1 notPasses
  unfold LookupPairArithmetic.tableSum at total
  rw [← total] at bad
  exact bad

end
end FormalProof4FHE.HasteBoots.LookupProducerArithmetic
