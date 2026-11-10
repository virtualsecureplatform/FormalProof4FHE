module
public import FormalProof4FHE.HasteBoots.RadixLookupSources
public import FormalProof4FHE.HasteBoots.SharedLookupOpeningFamily
public import FormalProof4FHE.HasteBoots.NativeSharedLookupGuard
@[expose] public section

/-! Original radix comparison sources in request-major/repetition-minor order.
The global registry omits only the decomposition input. Every job gathers its
literal digit/incoming-borrow/outgoing-borrow slots; repetitions reuse roots.
These structural facts do not identify unauthenticated claims with sources. -/
namespace FormalProof4FHE.HasteBoots.RadixSharedSourceSlots

variable {d repetitions : ℕ}

def slots (job : Fin (d * repetitions)) : Fin 3 → Fin (2*d+1) :=
  RadixLookupSources.comparisonSlots (finProdFinEquiv.symm job).1

theorem slots_job (limb : Fin d) (repetition : Fin repetitions) :
    slots (finProdFinEquiv (limb,repetition)) = RadixLookupSources.comparisonSlots limb := by
  simp only [slots,Equiv.symm_apply_apply]

/-- Every original comparison source is used, including the final borrow.
Positive limb/repetition counts are actual schedule preconditions. -/
theorem coverage (limbsPositive : 0 < d) (repetitionsPositive : 0 < repetitions)
    (source : Fin (2*d+1)) : ∃ job column, slots (d := d) (repetitions := repetitions) job column = source := by
  have used (limb : Fin d) (column : Fin 3)
      (equal : RadixLookupSources.comparisonSlots limb column = source) :
      ∃ job column, slots (d := d) (repetitions := repetitions) job column = source := by
    exact ⟨finProdFinEquiv (limb,⟨0,repetitionsPositive⟩),column,(congrFun (slots_job limb _) column).trans equal⟩
  by_cases digit : source.val < d
  · apply used ⟨source.val,digit⟩ 0
    apply Fin.ext
    rfl
  · by_cases incoming : source.val < 2*d
    · apply used ⟨source.val-d,by omega⟩ 1
      apply Fin.ext
      change d + (source.val-d) = source.val
      omega
    · apply used ⟨d-1,by omega⟩ 2
      apply Fin.ext
      change d + (d-1) + 1 = source.val
      have := source.isLt
      omega

/-- Exact checked list lookup for any finite original source-slot vector.
Order and aliases are retained, with no deduplication. -/
theorem gather_ofFn {count columns : ℕ}
    (values : Fin count → List NativeFieldRepresentation.GoldWord) (indices : Fin columns → Fin count) :
    NativeSharedLookupGuard.gather (List.ofFn values) (List.ofFn (fun i => (indices i).val)) =
      some (List.ofFn (fun i => values (indices i))) := by
  apply NativeSharedLookupGuard.gather_complete
  induction columns with
  | zero => exact .nil
  | succ columns ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    apply List.Forall₂.cons
    · simp only [List.getElem?_ofFn,(indices 0).isLt,↓reduceDIte]
    · exact ih (fun i => indices i.succ)

/-- The native shared guard gathers the original three comparison vectors
for this limb in the original registry order. -/
theorem gather_comparison (registry : Fin (2*d+2) → List NativeFieldRepresentation.GoldWord)
    (limb : Fin d) :
    NativeSharedLookupGuard.gather
      (List.ofFn (RadixLookupSources.comparisonRegistry registry))
      [limb.val,d+limb.val,d+limb.val+1] =
    some (List.ofFn (fun column => RadixLookupSources.comparisonRegistry registry
      (RadixLookupSources.comparisonSlots limb column))) := by
  have indices : List.ofFn (fun column => (RadixLookupSources.comparisonSlots limb column).val) =
      [limb.val,d+limb.val,d+limb.val+1] := rfl
  rw [← indices]
  exact gather_ofFn _ _

def request (limb : Fin d) (logicalLength : NativeUsizeMessage.Usize) : NativeSharedLookupGuard.Request :=
  ⟨[limb.val,d+limb.val,d+limb.val+1],logicalLength⟩

/-- Typed construction of the native guard's request/source fields. Jobs and
received helper/equality-point vectors remain the real supplied vectors. -/
def inputs (registry : Fin (2*d+2) → List NativeFieldRepresentation.GoldWord)
    (logicalLength : Fin d → NativeUsizeMessage.Usize) (jobs : List NativeSharedLookupGuard.Job)
    (equalityPoints : List (List NativeGoldExtensionArithmetic.Word))
    (helpers : List NativeGoldExtensionArithmetic.Word) : NativeSharedLookupGuard.Inputs :=
  ⟨List.ofFn (fun limb => request limb (logicalLength limb)),jobs,equalityPoints,
    List.ofFn (RadixLookupSources.comparisonRegistry registry),helpers⟩

/-- A successful native guard entry on the constructed registry contains
exactly the original ordered comparison vectors for its request index. This
uses the guard's actual checked gather, not an asserted tuple certificate. -/
theorem checked_values (registry : Fin (2*d+2) → List NativeFieldRepresentation.GoldWord)
    (logicalLength : Fin d → NativeUsizeMessage.Usize) (jobs : List NativeSharedLookupGuard.Job)
    (equalityPoints : List (List NativeGoldExtensionArithmetic.Word))
    (helpers : List NativeGoldExtensionArithmetic.Word)
    (claims : List NativeScalarBatchVerifier.SubClaim) (point : List NativeGoldExtensionArithmetic.Word)
    (pulled : NativeGoldCoefficientsQuery.Query) (width : ℕ) (checked : NativeSharedLookupGuard.Checked)
    (evidence : NativeSharedLookupGuard.Evidence (inputs registry logicalLength jobs equalityPoints helpers)
      claims point pulled width checked) (limb : Fin d) (requestIndex : checked.job.request = limb.val) :
    checked.values = List.ofFn (fun column => RadixLookupSources.comparisonRegistry registry
      (RadixLookupSources.comparisonSlots limb column)) := by
  have found : (inputs registry logicalLength jobs equalityPoints helpers).requests[checked.job.request]? =
      some (request limb (logicalLength limb)) := by
    simp only [inputs,requestIndex,List.getElem?_ofFn,limb.isLt,↓reduceDIte]
  have requestEq := Option.some.inj (evidence.request.symm.trans found)
  have gathered := evidence.values
  rw [requestEq] at gathered
  exact Option.some.inj (gathered.symm.trans (gather_comparison registry limb))

/-- The value association follows directly from a successful native guard
execution and membership in its returned trace. -/
theorem guard_values (registry : Fin (2*d+2) → List NativeFieldRepresentation.GoldWord)
    (logicalLength : Fin d → NativeUsizeMessage.Usize) (jobs : List NativeSharedLookupGuard.Job)
    (equalityPoints : List (List NativeGoldExtensionArithmetic.Word))
    (helpers : List NativeGoldExtensionArithmetic.Word) (claims : List NativeScalarBatchVerifier.SubClaim)
    (sourceVars width : ℕ) (result : NativeSharedLookupGuard.Result)
    (success : NativeSharedLookupGuard.guard (inputs registry logicalLength jobs equalityPoints helpers)
      claims sourceVars width = some result)
    (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ result.checked)
    (limb : Fin d) (requestIndex : checked.job.request = limb.val) :
    checked.values = List.ofFn (fun column => RadixLookupSources.comparisonRegistry registry
      (RadixLookupSources.comparisonSlots limb column)) :=
  checked_values registry logicalLength jobs equalityPoints helpers claims result.point result.pulled width checked
    ((NativeSharedLookupGuard.guard_spec _ _ _ _ _ success).checked checked member) limb requestIndex

end FormalProof4FHE.HasteBoots.RadixSharedSourceSlots
