module
public import FormalProof4FHE.HasteBoots.NativeGoldParameterStore
public import FormalProof4FHE.HasteBoots.PBSHadamard
@[expose] public section

/-! Original coefficient/evaluation/key references in native complete-PBS
order. Every NTT evaluation source is the same borrowed object and root as
its Hadamard factor; geometry equality alone is never used as identity. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
open NativeGoldParameterStore (Entry Reference collect Reachable GoodEntry)
open NativeRootMessage (Digest)
noncomputable section

structure Family (count : ℕ) where
  coefficientHandle : ℕ
  evaluationHandle : ℕ
  keyHandle : ℕ
  coefficients : Fin (count+1) → Digest
  evaluations : Fin (count+1) → Digest
  keys : Fin count → Digest

variable {count : ℕ}

def evaluationFactor (slot : Fin (count+1)) : PBSHadamard.Factor count :=
  if bound : slot.val < count then .inl (⟨slot.val,bound⟩,false) else .inr ()

def roleReference (family : Family count) : PBSHadamard.Factor count → Reference
  | .inl (index,false) => ⟨family.evaluationHandle,family.evaluations (Fin.castSucc index)⟩
  | .inl (index,true) => ⟨family.keyHandle,family.keys index⟩
  | .inr _ => ⟨family.evaluationHandle,family.evaluations (Fin.last count)⟩

def roleEquiv (count : ℕ) : PBSHadamard.Factor count ≃ Fin (2*count+1) :=
  Equiv.ofBijective PBSHadamard.address PBSHadamard.address_bijective

/-- Native order is digit/key pairs, followed by the original result. -/
def hadamard (family : Family count) : List Reference :=
  List.ofFn (fun index => roleReference family ((roleEquiv count).symm index))

/-- A child NTT uses its original coefficient/evaluation pair, in that order. -/
def ntt (family : Family count) (slot : Fin (count+1)) : List Reference :=
  [⟨family.coefficientHandle,family.coefficients slot⟩,
   ⟨family.evaluationHandle,family.evaluations slot⟩]

theorem evaluation_reference (family : Family count) (slot : Fin (count+1)) :
    roleReference family (evaluationFactor slot) = ⟨family.evaluationHandle,family.evaluations slot⟩ := by
  unfold evaluationFactor
  split
  · rename_i bound
    have same : Fin.castSucc (⟨slot.val,bound⟩ : Fin count) = slot := Fin.ext rfl
    simp only [roleReference,same]
  · rename_i bound
    have same : Fin.last count = slot := Fin.ext (by simp only [Fin.val_last]; omega)
    simp only [roleReference,same]

theorem hadamard_slot (family : Family count) (factor : PBSHadamard.Factor count) :
    (hadamard family)[(PBSHadamard.address factor).val]? = some (roleReference family factor) := by
  simp only [hadamard,List.getElem?_ofFn]
  simp [roleEquiv]
  have bound := (PBSHadamard.address factor).isLt
  omega

theorem ntt_evaluation (family : Family count) (slot : Fin (count+1)) :
    (ntt family slot)[1]? = some (roleReference family (evaluationFactor slot)) := by
  rw [evaluation_reference]
  rfl

/-- Exact borrowed-reference equality forces equality of the original retained
parameter objects AND roots in successful native collections. -/
theorem collected_alias
    (entries : List Entry) (firstReferences secondReferences : List Reference)
    (firstRegistry secondRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (firstCollected : collect entries firstReferences = some firstRegistry)
    (secondCollected : collect entries secondReferences = some secondRegistry)
    (firstIndex secondIndex : ℕ) (firstBound : firstIndex < firstReferences.length)
    (secondBound : secondIndex < secondReferences.length) (reference : Reference)
    (firstSelected : firstReferences[firstIndex]? = some reference)
    (secondSelected : secondReferences[secondIndex]? = some reference) :
    ∃ entry, entries[reference.handle]? = some entry ∧
      firstRegistry[firstIndex]? = some ⟨entry.initialized.parameters,reference.root⟩ ∧
      secondRegistry[secondIndex]? = some ⟨entry.initialized.parameters,reference.root⟩ := by
  obtain ⟨firstReference,firstEntry,selectedFirst,storedFirst,oracleFirst⟩ :=
    NativeGoldParameterStore.collect_slot entries firstReferences firstRegistry firstCollected firstIndex firstBound
  obtain ⟨secondReference,secondEntry,selectedSecond,storedSecond,oracleSecond⟩ :=
    NativeGoldParameterStore.collect_slot entries secondReferences secondRegistry secondCollected secondIndex secondBound
  have firstSame := Option.some.inj (selectedFirst.symm.trans firstSelected)
  have secondSame := Option.some.inj (selectedSecond.symm.trans secondSelected)
  subst firstReference
  subst secondReference
  have entrySame := Option.some.inj (storedSecond.symm.trans storedFirst)
  subst secondEntry
  exact ⟨firstEntry,storedFirst,oracleFirst,oracleSecond⟩

/-- Every original NTT evaluation slot is identified with its Hadamard factor
through the actual parameter-store collector, including the final result slot. -/
theorem original_evaluation_alias
    (family : Family count) (slot : Fin (count+1))
    (entries : List Entry) (reachable : Reachable entries)
    (nttRegistry hadamardRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : collect entries (ntt family slot) = some nttRegistry)
    (hadamardCollected : collect entries (hadamard family) = some hadamardRegistry) :
    ∃ entry, entries[family.evaluationHandle]? = some entry ∧ GoodEntry entry ∧
      nttRegistry[1]? = some ⟨entry.initialized.parameters,family.evaluations slot⟩ ∧
      hadamardRegistry[(PBSHadamard.address (evaluationFactor slot)).val]? =
        some ⟨entry.initialized.parameters,family.evaluations slot⟩ := by
  obtain ⟨entry,stored,first,second⟩ := collected_alias entries (ntt family slot) (hadamard family)
    nttRegistry hadamardRegistry nttCollected hadamardCollected 1 (PBSHadamard.address (evaluationFactor slot)).val
    (by simp [ntt]) (by simpa only [hadamard,List.length_ofFn] using (PBSHadamard.address (evaluationFactor slot)).isLt)
    (roleReference family (evaluationFactor slot)) (ntt_evaluation family slot) (hadamard_slot family _)
  rw [evaluation_reference] at stored first second
  exact ⟨entry,stored,NativeGoldParameterStore.reachable_good entries reachable entry
    (List.mem_of_getElem? stored),first,second⟩

/-- Both selected oracles retain literally equal parameters and roots. -/
theorem collected_oracles_equal
    (family : Family count) (slot : Fin (count+1))
    (entries : List Entry) (reachable : Reachable entries)
    (nttRegistry hadamardRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : collect entries (ntt family slot) = some nttRegistry)
    (hadamardCollected : collect entries (hadamard family) = some hadamardRegistry) :
    nttRegistry[1]? = hadamardRegistry[(PBSHadamard.address (evaluationFactor slot)).val]? := by
  obtain ⟨entry,_,_,first,second⟩ := original_evaluation_alias family slot entries reachable nttRegistry hadamardRegistry nttCollected hadamardCollected
  exact first.trans second.symm

/-- Native context serialization uses the same original retained parameters,
including the full row-code description, rather than equal geometry alone. -/
theorem context_inputs_equal
    (family : Family count) (slot : Fin (count+1))
    (entries : List Entry) (reachable : Reachable entries)
    (nttRegistry hadamardRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : collect entries (ntt family slot) = some nttRegistry)
    (hadamardCollected : collect entries (hadamard family) = some hadamardRegistry) :
    (nttRegistry[1]?).bind (fun oracle => NativeBrakedownContext.input NativeGoldBlockCode.description.row oracle.parameters) =
      (hadamardRegistry[(PBSHadamard.address (evaluationFactor slot)).val]?).bind
        (fun oracle => NativeBrakedownContext.input NativeGoldBlockCode.description.row oracle.parameters) := by
  rw [collected_oracles_equal family slot entries reachable nttRegistry hadamardRegistry nttCollected hadamardCollected]

/-- Both callers execute the same native context-digest program. -/
theorem context_programs_equal
    (family : Family count) (slot : Fin (count+1))
    (entries : List Entry) (reachable : Reachable entries)
    (nttRegistry hadamardRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : collect entries (ntt family slot) = some nttRegistry)
    (hadamardCollected : collect entries (hadamard family) = some hadamardRegistry) :
    (nttRegistry[1]?).map (fun oracle => NativeBrakedownContext.context NativeGoldBlockCode.description.row oracle.parameters) =
      (hadamardRegistry[(PBSHadamard.address (evaluationFactor slot)).val]?).map
        (fun oracle => NativeBrakedownContext.context NativeGoldBlockCode.description.row oracle.parameters) := by
  rw [collected_oracles_equal family slot entries reachable nttRegistry hadamardRegistry nttCollected hadamardCollected]

end
end FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
