module

public import FormalProof4FHE.HasteBoots.NativeLookupDrawHistory
public import FormalProof4FHE.HasteBoots.NativeGoldLookupCompleted

@[expose] public section

/-!
# Raw Goldilocks lookup inputs from the actual retained draw positions

Decode the first compression draw and last accepted offset directly from
their stored coefficients. The existing sampler and history invariants
prove decoding and arithmetic success. No caller-provided raw y/r equality
or nonzero certificate is needed. Rust, helper commitments and the remaining
lookup child body are separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldLookupProducer

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)

def decode (values : List ℕ) : Option Word :=
  if complete : values.length = 3 then
    if valid : ∀ value ∈ values, value < goldilocksModulus then
      some (NativeGoldLookupCompleted.fromCoefficients values complete valid)
    else none
  else none

theorem decode_complete (values : List ℕ) (complete : values.length = 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) :
    decode values = some (NativeGoldLookupCompleted.fromCoefficients values complete valid) := by
  simp only [decode, dite_eq_left complete, dite_eq_left valid]

def sourceWords (selection : NativeLookupChallenge.Machine Goldilocks3) : Option (Word × Word) :=
  match selection.control with
  | .finished _ _ _ _ _ =>
      selection.draws.head?.bind (fun first => selection.draws.getLast?.bind (fun last =>
        (decode first.coefficients.values).bind (fun y =>
          (decode last.coefficients.values).map (fun r => (y, r)))))
  | _ => none

structure Output where
  y : Word
  r : Word
  powers : List Word
  nextPower : Word
  table : List Word
  inverses : List Word

def produce (width : ℕ) (rows : List (List GoldWord))
    (selection : NativeLookupChallenge.Machine Goldilocks3) : Option Output :=
  (sourceWords selection).bind (fun sources =>
    let powerState := NativeGoldLookup.powerRun sources.1 width
    let table := rows.map (NativeGoldLookup.compress powerState.1)
    if NativeGoldLookup.allowed table sources.2 then
      (NativeGoldLookup.reciprocals (NativeGoldLookup.denominators sources.2 table)).map
        (fun inverses => ⟨sources.1, sources.2, powerState.1, powerState.2, table, inverses⟩)
    else none)

noncomputable section

theorem sourceWords_success (selection : NativeLookupChallenge.Machine Goldilocks3)
    (valid : NativeLookupChallenge.MachineValid goldilocksBasis selection)
    (roles : NativeLookupDrawHistory.Roles selection)
    (y r : Goldilocks3) (weights table : List Goldilocks3) (transcript : NativeTranscript.Transcript)
    (finished : selection.control = .finished y r weights table transcript) :
    ∃ rawY rawR, sourceWords selection = some (rawY, rawR) ∧
      goldExtensionValue rawY = y ∧ goldExtensionValue rawR = r ∧
      ∀ i, selection.draws.head?.map (fun draw => draw.coefficients.values[i.val]?.getD 0) = some (rawY i).val ∧
        selection.draws.getLast?.map (fun draw => draw.coefficients.values[i.val]?.getD 0) = some (rawR i).val := by
  unfold NativeLookupDrawHistory.Roles at roles
  rw [finished] at roles
  obtain ⟨first, middle, last, history, firstValue, lastValue, _, _, _⟩ := roles
  have firstMember : first ∈ selection.draws := by simp [history]
  have lastMember : last ∈ selection.draws := by simp [history]
  have firstValid := valid.2 first firstMember
  have lastValid := valid.2 last lastMember
  have firstBounded := firstValid.2.1
  have lastBounded := lastValid.2.1
  unfold NativeFieldVector.ValuesValid at firstBounded lastBounded
  let rawY := NativeGoldLookupCompleted.fromCoefficients first.coefficients.values firstValid.1 firstBounded
  let rawR := NativeGoldLookupCompleted.fromCoefficients last.coefficients.values lastValid.1 lastBounded
  have firstGet : selection.draws.head? = some first := by rw [history]; rfl
  have lastGet : selection.draws.getLast? = some last := by
    rw [history]
    change ((first :: middle) ++ [last]).getLast? = some last
    rw [List.getLast?_append_of_ne_nil (first :: middle) (by simp)]
    rfl
  refine ⟨rawY, rawR, ?_, ?_, ?_, ?_⟩
  · rw [sourceWords, finished, firstGet, Option.bind_some, lastGet, Option.bind_some,
      decode_complete _ firstValid.1 firstBounded, Option.bind_some,
      decode_complete _ lastValid.1 lastBounded]
    rfl
  · rw [NativeGoldLookupCompleted.fromCoefficients_value, ← firstValid.2.2, firstValue]
  · rw [NativeGoldLookupCompleted.fromCoefficients_value, ← lastValid.2.2, lastValue]
  · intro i
    rw [firstGet, lastGet, Option.map_some, Option.map_some,
      List.getElem?_eq_getElem (by omega : i.val < first.coefficients.values.length),
      List.getElem?_eq_getElem (by omega : i.val < last.coefficients.values.length)]
    exact ⟨rfl, rfl⟩

/-- The producer reads its y/r words from the exact first/last coefficient
draws. All success premises follow from the existing operational invariants. -/
theorem completed_success
    (machine : NativeLookupBatch.Machine goldilocksModulus Goldilocks3)
    (valid : NativeLookupBatch.Valid goldilocksBasis machine)
    (roles : NativeLookupDrawHistory.BatchRoles machine)
    (completed : NativeLookupBatch.Completed goldilocksModulus Goldilocks3)
    (member : completed ∈ machine.completed)
    (y r : Goldilocks3) (weights table : List Goldilocks3) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript)
    (rows : List (List GoldWord)) (rowsMatch : completed.job.request.rows = rows.map (List.map goldValue)) :
    ∃ output, produce completed.job.request.width rows completed.selection = some output ∧
      goldExtensionValue output.y = y ∧ goldExtensionValue output.r = r ∧
      output.powers.map goldExtensionValue = weights ∧
      output.table.map goldExtensionValue = table ∧
      output.inverses.map goldExtensionValue = NativeLookupReciprocals.inverses .individual r table ∧
      goldExtensionValue output.nextPower = y ^ completed.job.request.width := by
  obtain ⟨rawY, rawR, decoded, yMatches, rMatches, _⟩ := sourceWords_success completed.selection
    (valid.2 completed member).1.1 (roles.2 completed member) y r weights table transcript finished
  obtain ⟨powersMatch, tableMatch, accepted, inverses, found, related⟩ :=
    NativeGoldLookupCompleted.reciprocals machine valid completed member y r weights table transcript
      finished rawY rawR rows yMatches rMatches rowsMatch
  refine ⟨⟨rawY, rawR, NativeGoldLookup.powers rawY completed.job.request.width,
    (NativeGoldLookup.powerRun rawY completed.job.request.width).2,
    NativeGoldLookup.tableAt rows completed.job.request.width rawY, inverses⟩,
    ?_, yMatches, rMatches, powersMatch, tableMatch, related, ?_⟩
  · rw [produce, decoded, Option.bind_some]
    change (if NativeGoldLookup.allowed (NativeGoldLookup.tableAt rows completed.job.request.width rawY) rawR
      then _ else _) = _
    rw [accepted, ite_eq_left (rfl : true = true)]
    change (NativeGoldLookup.reciprocals (NativeGoldLookup.denominators rawR
      (NativeGoldLookup.tableAt rows completed.job.request.width rawY))).map _ = _
    rw [found]
    rfl
  · have last := congrArg Prod.snd (NativeGoldLookup.powerRun_value rawY completed.job.request.width)
    change goldExtensionValue (NativeGoldLookup.powerRun rawY completed.job.request.width).2 = _ at last
    simpa only [yMatches] using last

/-- On a run from the actual batch initializer, both invariants used above
are proved from execution. Rejected draws and their reader/receipt records
remain in the original selection. -/
theorem executed_success (w fuel : ℕ) (actions : List (NativeLookupBatch.Action goldilocksModulus))
    (initialTranscript : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (completed : NativeLookupBatch.Completed goldilocksModulus Goldilocks3)
    (member : completed ∈ (NativeLookupBatch.execute goldilocksBasis w fuel
      (NativeLookupBatch.initial actions initialTranscript) world).1.completed)
    (y r : Goldilocks3) (weights table : List Goldilocks3) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript)
    (rows : List (List GoldWord)) (rowsMatch : completed.job.request.rows = rows.map (List.map goldValue)) :
    ∃ output, produce completed.job.request.width rows completed.selection = some output ∧
      goldExtensionValue output.y = y ∧ goldExtensionValue output.r = r ∧
      output.powers.map goldExtensionValue = weights ∧ output.table.map goldExtensionValue = table ∧
      output.inverses.map goldExtensionValue = NativeLookupReciprocals.inverses .individual r table ∧
      goldExtensionValue output.nextPower = y ^ completed.job.request.width := by
  apply completed_success _
    (NativeLookupBatch.execute_valid goldilocksBasis w fuel _ world
      (NativeLookupBatch.initial_valid goldilocksBasis actions initialTranscript))
    (NativeLookupDrawHistory.execute_batch goldilocksBasis w fuel _ world
      (NativeLookupDrawHistory.initial_batch actions initialTranscript))
    completed member y r weights table transcript finished rows rowsMatch

/-- The initialized execution supplies the raw public table-sum bytes' value
without supplied raw inputs or a reciprocal-value certificate. -/
theorem executed_tableSum (w fuel : ℕ) (actions : List (NativeLookupBatch.Action goldilocksModulus))
    (initialTranscript : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (completed : NativeLookupBatch.Completed goldilocksModulus Goldilocks3)
    (member : completed ∈ (NativeLookupBatch.execute goldilocksBasis w fuel
      (NativeLookupBatch.initial actions initialTranscript) world).1.completed)
    (y r : Goldilocks3) (weights table : List Goldilocks3) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript)
    (rows : List (List GoldWord)) (multiplicities : List GoldWord)
    (rowsMatch : completed.job.request.rows = rows.map (List.map goldValue)) :
    ∃ output, produce completed.job.request.width rows completed.selection = some output ∧
      goldExtensionValue (NativeGoldExtensionArithmetic.tableSum output.inverses multiplicities) =
        NativeLookupArithmetic.tableSum .individual r table (multiplicities.map goldValue) := by
  obtain ⟨output, done, _, _, _, _, related, _⟩ := executed_success w fuel actions initialTranscript world
    completed member y r weights table transcript finished rows rowsMatch
  exact ⟨output, done, NativeGoldLookup.tableSum_value r table output.inverses multiplicities related⟩

end

end FormalProof4FHE.HasteBoots.NativeGoldLookupProducer
