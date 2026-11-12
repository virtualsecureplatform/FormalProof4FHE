module
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorReferences
@[expose] public section

/-! The monomial NTTs borrow accumulator objects 0/1 and two evaluation roots
under one retained evaluation-parameter allocation. The final public-plan
ZeroCheck opens those identical evaluation objects. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSMonomialReferences
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Reference)
noncomputable section

structure Evaluations where
  handle : ℕ
  roots : Bool → Digest

def coefficientSlot (side : Bool) : Fin 4 := if side then 1 else 0
def evaluationSlot (side : Bool) : Fin 2 := if side then 1 else 0

def coefficients (accumulators : Fin 4 → Reference) (side : Bool) : Digest :=
  (accumulators (coefficientSlot side)).root

def evaluationReference (evaluations : Evaluations) (side : Bool) : Reference :=
  ⟨evaluations.handle,evaluations.roots side⟩

def ntt (accumulators : Fin 4 → Reference) (evaluations : Evaluations) (side : Bool) : List Reference :=
  [accumulators (coefficientSlot side),evaluationReference evaluations side]

def publicZero (evaluations : Evaluations) : List Reference :=
  [evaluationReference evaluations false,evaluationReference evaluations true]

theorem ntt_coefficient (accumulators : Fin 4 → Reference) (evaluations : Evaluations) (side : Bool) :
    (ntt accumulators evaluations side)[0]? = some (accumulators (coefficientSlot side)) := rfl

theorem ntt_evaluation (accumulators : Fin 4 → Reference) (evaluations : Evaluations) (side : Bool) :
    (ntt accumulators evaluations side)[1]? = some (evaluationReference evaluations side) := rfl

theorem publicZero_slot (evaluations : Evaluations) (side : Bool) :
    (publicZero evaluations)[(evaluationSlot side).val]? = some (evaluationReference evaluations side) := by
  cases side <;> rfl

/-- An NTT coefficient input is the exact retained original accumulator object,
including its parameter allocation, rather than an equal-looking new geometry. -/
theorem collected_coefficient_alias {d : ℕ} (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference)
    (evaluations : Evaluations) (side : Bool) (entries : List NativeGoldParameterStore.Entry)
    (nttRegistry accumulatorRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : NativeGoldParameterStore.collect entries (ntt accumulators evaluations side) = some nttRegistry)
    (accumulatorCollected : NativeGoldParameterStore.collect entries (PackedPBSAccumulatorReferences.registry family inputs accumulators) = some accumulatorRegistry) :
    ∃ original, entries[(accumulators (coefficientSlot side)).handle]? = some original ∧
      nttRegistry[0]? = some ⟨original.initialized.parameters,(accumulators (coefficientSlot side)).root⟩ ∧
      accumulatorRegistry[(coefficientSlot side).val]? = some ⟨original.initialized.parameters,(accumulators (coefficientSlot side)).root⟩ := by
  have selected := PackedPBSAccumulatorReferences.registry_slot family inputs accumulators
    (Fin.castLE (by decide +kernel : 4 ≤ 7) (coefficientSlot side))
  rw [PackedPBSAccumulatorReferences.accumulator_reference] at selected
  exact PackedPBSOriginalReferences.collected_alias entries (ntt accumulators evaluations side)
    (PackedPBSAccumulatorReferences.registry family inputs accumulators) nttRegistry accumulatorRegistry nttCollected accumulatorCollected
    0 (coefficientSlot side).val (by simp [ntt])
    (by have := (coefficientSlot side).isLt; simp only [PackedPBSAccumulatorReferences.registry,List.length_ofFn]; omega)
    (accumulators (coefficientSlot side)) (ntt_coefficient accumulators evaluations side) selected

/-- The public-plan terminal uses the identical retained evaluation object
that the matching NTT established, including its actual parameter allocation. -/
theorem collected_evaluation_alias (accumulators : Fin 4 → Reference) (evaluations : Evaluations)
    (side : Bool) (entries : List NativeGoldParameterStore.Entry)
    (nttRegistry terminalRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : NativeGoldParameterStore.collect entries (ntt accumulators evaluations side) = some nttRegistry)
    (terminalCollected : NativeGoldParameterStore.collect entries (publicZero evaluations) = some terminalRegistry) :
    ∃ original, entries[evaluations.handle]? = some original ∧
      nttRegistry[1]? = some ⟨original.initialized.parameters,evaluations.roots side⟩ ∧
      terminalRegistry[(evaluationSlot side).val]? = some ⟨original.initialized.parameters,evaluations.roots side⟩ :=
  PackedPBSOriginalReferences.collected_alias entries (ntt accumulators evaluations side) (publicZero evaluations)
    nttRegistry terminalRegistry nttCollected terminalCollected 1 (evaluationSlot side).val
    (by simp [ntt]) (by simpa only [publicZero,List.length_cons,List.length_nil] using (evaluationSlot side).isLt)
    (evaluationReference evaluations side) (ntt_evaluation accumulators evaluations side) (publicZero_slot evaluations side)

end
end FormalProof4FHE.HasteBoots.PackedPBSMonomialReferences
