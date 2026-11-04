module

public import FormalProof4FHE.HasteBoots.NativeGoldLookup

@[expose] public section

/-!
# Raw lookup arithmetic refines completed sampler jobs

A completed job supplies its accepted-domain invariant. Given related raw
source words, the literal producer succeeds and supplies the same ordered
mathematical inverses and public sum. Raw-source identification, helper
packing/commitment bytes, child bodies and Rust/work refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldLookupCompleted

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)

/-- Native `Goldilocks::new` retains each accepted canonical coefficient. -/
def fromCoefficients (values : List ℕ) (complete : values.length = 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) : Word := fun i =>
  ⟨values[i.val]'(by omega),
    (valid _ (List.getElem_mem (by omega))).trans (by decide)⟩

theorem fromCoefficients_canonical (values : List ℕ) (complete : values.length = 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) (i : Fin 3) :
    (fromCoefficients values complete valid i).val < goldilocksModulus :=
  valid _ (List.getElem_mem (by omega))

noncomputable section

theorem fromCoefficients_value (values : List ℕ) (complete : values.length = 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) :
    goldExtensionValue (fromCoefficients values complete valid) =
      TypedFieldRequest.scalarValue goldilocksBasis values := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp only [goldExtension_coordinate, TypedFieldRequest.scalarValue, LinearEquiv.apply_symm_apply]
  rw [List.getElem?_eq_getElem (by omega : i.val < values.length)]
  rfl

/-- Completed coefficient draws have an explicit canonical raw constructor;
the machine invariant supplies length, bounds and its mathematical value. -/
theorem draw_words (selection : NativeLookupChallenge.Machine Goldilocks3)
    (valid : NativeLookupChallenge.MachineValid goldilocksBasis selection)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ selection.draws) :
    ∃ raw : Word, goldExtensionValue raw = draw.value ∧
      ∀ i, (raw i).val = draw.coefficients.values[i.val]?.getD 0 ∧
        (raw i).val < goldilocksModulus := by
  have complete := valid.2 draw member
  have bounded := complete.2.1
  unfold NativeFieldVector.ValuesValid at bounded
  refine ⟨fromCoefficients draw.coefficients.values complete.1 bounded, ?_, ?_⟩
  · rw [fromCoefficients_value, complete.2.2]
  · intro i
    refine ⟨?_, fromCoefficients_canonical _ _ _ i⟩
    rw [List.getElem?_eq_getElem (by omega : i.val < draw.coefficients.values.length)]
    rfl

/-- The old compiled sampler fixes the actual table and accepted domain;
no independent nonzero-denominator certificate is supplied by the caller. -/
theorem reciprocals
    (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3)
    (valid : NativeLookupBatch.Valid goldilocksBasis machine)
    (completed : NativeLookupBatch.Completed goldilocksModulus Goldilocks3)
    (member : completed ∈ machine.completed)
    (y r : Goldilocks3) (weights table : List Goldilocks3) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript)
    (rawY rawR : Word) (rows : List (List GoldWord))
    (yMatches : goldExtensionValue rawY = y) (rMatches : goldExtensionValue rawR = r)
    (rowsMatch : completed.job.request.rows = rows.map (List.map goldValue)) :
    let rawTable := NativeGoldLookup.tableAt rows completed.job.request.width rawY
    (NativeGoldLookup.powers rawY completed.job.request.width).map goldExtensionValue = weights ∧
    rawTable.map goldExtensionValue = table ∧
    NativeGoldLookup.allowed rawTable rawR = true ∧
    ∃ output, NativeGoldLookup.reciprocals (NativeGoldLookup.denominators rawR rawTable) = some output ∧
      output.map goldExtensionValue = NativeLookupReciprocals.inverses .individual r table := by
  have selected := (valid.2 completed member).1.2.1
  unfold NativeLookupChallenge.SelectionValid at selected
  rw [finished] at selected
  have source : table = NativeLookupChallenge.tableAt completed.job.request.rows completed.job.request.width y := by
    rw [selected.2.1, selected.1]
    rfl
  have tableMatches : (NativeGoldLookup.tableAt rows completed.job.request.width rawY).map goldExtensionValue = table := by
    rw [NativeGoldLookup.tableAt_value, yMatches, ← rowsMatch, ← source]
  have rawAllowed : NativeGoldLookup.allowed
      (NativeGoldLookup.tableAt rows completed.job.request.width rawY) rawR = true := by
    rw [NativeGoldLookup.allowed_value, tableMatches, rMatches]
    exact selected.2.2
  obtain ⟨output, done, related⟩ := NativeGoldLookup.accepted_reciprocals _ _ rawAllowed
  refine ⟨?_, tableMatches, rawAllowed, output, done, ?_⟩
  · rw [NativeGoldLookup.powers_value, yMatches, selected.1]
  · simpa only [rMatches, tableMatches] using related

/-- Public table sums consume the exact successful raw reciprocal vector
returned by the producer. The old sampler discharges its arithmetic domain. -/
theorem tableSum
    (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3)
    (valid : NativeLookupBatch.Valid goldilocksBasis machine)
    (completed : NativeLookupBatch.Completed goldilocksModulus Goldilocks3)
    (member : completed ∈ machine.completed)
    (y r : Goldilocks3) (weights table : List Goldilocks3) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript)
    (rawY rawR : Word) (rows : List (List GoldWord)) (multiplicities : List GoldWord)
    (yMatches : goldExtensionValue rawY = y) (rMatches : goldExtensionValue rawR = r)
    (rowsMatch : completed.job.request.rows = rows.map (List.map goldValue)) :
    ∃ output, NativeGoldLookup.reciprocals (NativeGoldLookup.denominators rawR
        (NativeGoldLookup.tableAt rows completed.job.request.width rawY)) = some output ∧
      goldExtensionValue (NativeGoldExtensionArithmetic.tableSum output multiplicities) =
        NativeLookupArithmetic.tableSum .individual r table (multiplicities.map goldValue) := by
  obtain ⟨_, _, _, output, done, related⟩ := reciprocals machine valid completed member y r weights table transcript
    finished rawY rawR rows yMatches rMatches rowsMatch
  exact ⟨output, done, NativeGoldLookup.tableSum_value r table output multiplicities related⟩

end

end FormalProof4FHE.HasteBoots.NativeGoldLookupCompleted
