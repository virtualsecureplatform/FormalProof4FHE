module
public import FormalProof4FHE.HasteBoots.ParentSeedCollisionRisk
@[expose] public section

/-! First onset of a full parent-seed collision among recognized raw keys.
All actual naming observations are retained, including starts and empty reads. -/
namespace FormalProof4FHE.HasteBoots.ParentSeedCollisionOnset
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open ParentSeedCollisionRisk (Collision seed)
open scoped Classical
noncomputable section

theorem inputs_append (earlier later : List Observation) :
    ParentSeedCandidates.inputs (earlier++later) = ParentSeedCandidates.inputs earlier ∪ ParentSeedCandidates.inputs later := by
  simp only [ParentSeedCandidates.inputs,List.filterMap_append,List.toFinset_append]

theorem inputs_mono (earlier later : List Observation) (included : earlier.Sublist later) :
    ParentSeedCandidates.inputs earlier ⊆ ParentSeedCandidates.inputs later := by
  intro raw named
  obtain ⟨entry,member,parsed⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp named)
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨entry,included.subset member,parsed⟩)

theorem mono (earlier later : List Observation) (world : World) (included : earlier.Sublist later)
    (bad : Collision earlier world) : Collision later world := by
  obtain ⟨left,leftNamed,right,rightNamed,different,equal⟩ := bad
  exact ⟨left,inputs_mono earlier later included leftNamed,right,inputs_mono earlier later included rightNamed,different,equal⟩

theorem singleton (entry : Observation) (raw : Input) (named : ParentSeedCandidates.candidate entry = some raw) :
    ParentSeedCandidates.inputs [entry] = {raw} := by
  simp only [ParentSeedCandidates.inputs,List.filterMap_cons,named,List.filterMap_nil,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty]

theorem onset (history : List Observation) (entry : Observation) (world : World)
    (safe : ¬ Collision history world) (bad : Collision (history ++ [entry]) world) :
    ∃ raw, ParentSeedCandidates.candidate entry = some raw ∧ raw ∉ ParentSeedCandidates.inputs history ∧
      ∃ old ∈ ParentSeedCandidates.inputs history, seed world raw = seed world old := by
  cases named : ParentSeedCandidates.candidate entry with
  | none =>
    have unchanged : ParentSeedCandidates.inputs (history ++ [entry]) = ParentSeedCandidates.inputs history := by
      rw [inputs_append]
      have empty : ParentSeedCandidates.inputs [entry] = ∅ := by
        simp only [ParentSeedCandidates.inputs,List.filterMap_cons,named,List.filterMap_nil,List.toFinset_nil]
      rw [empty,Finset.union_empty]
    exact False.elim (safe (by simpa only [Collision,unchanged] using bad))
  | some raw =>
    have added : ParentSeedCandidates.inputs (history ++ [entry]) = ParentSeedCandidates.inputs history ∪ {raw} := by
      rw [inputs_append,singleton entry raw named]
    have fresh : raw ∉ ParentSeedCandidates.inputs history := by
      intro old
      have unchanged : ParentSeedCandidates.inputs (history ++ [entry]) = ParentSeedCandidates.inputs history := by
        rw [added,Finset.union_eq_left.mpr]
        exact Finset.singleton_subset_iff.mpr old
      exact safe (by simpa only [Collision,unchanged] using bad)
    refine ⟨raw,rfl,fresh,?_⟩
    obtain ⟨left,leftNamed,right,rightNamed,different,equal⟩ := bad
    rw [added,Finset.mem_union,Finset.mem_singleton] at leftNamed rightNamed
    rcases leftNamed with oldLeft | rfl
    · rcases rightNamed with oldRight | rfl
      · exact False.elim (safe ⟨left,oldLeft,right,oldRight,different,equal⟩)
      · exact ⟨left,oldLeft,equal.symm⟩
    · rcases rightNamed with oldRight | rfl
      · exact ⟨right,oldRight,equal⟩
      · exact False.elim (different rfl)

/-- Every final collision has a first actual naming observation. -/
theorem first (history : List Observation) (world : World) (bad : Collision history world) :
    ∃ position entry raw, history[position]? = some entry ∧
      ParentSeedCandidates.candidate entry = some raw ∧ raw ∉ ParentSeedCandidates.inputs (history.take position) ∧
      ∃ old ∈ ParentSeedCandidates.inputs (history.take position), seed world raw = seed world old := by
  have witness : ∃ n, Collision (history.take (n+1)) world := ⟨history.length,by rw [List.take_of_length_le (by omega)]; exact bad⟩
  let position := Nat.find witness
  have occurred := Nat.find_spec witness
  have before : ¬ Collision (history.take position) world := by
    cases equal : position with
    | zero => simp [Collision,ParentSeedCandidates.inputs]
    | succ previous =>
      have noEarlier := Nat.find_min witness (show previous < position by omega)
      simpa only [equal] using noEarlier
  have bounded : position < history.length := by
    by_contra outside
    have both : history.take (position+1) = history.take position := by
      rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
    rw [both] at occurred
    exact before occurred
  have split : history.take (position+1) = history.take position ++ history[position]?.toList := List.take_add_one
  have found : history[position]? = some history[position] := List.getElem?_eq_getElem bounded
  rw [List.getElem?_eq_getElem bounded] at split
  simp only [Option.toList_some] at split
  rw [split] at occurred
  obtain ⟨raw,named,new,old,oldNamed,equal⟩ := onset (history.take position) history[position] world before occurred
  exact ⟨position,history[position],raw,found,named,new,old,oldNamed,equal⟩

end
end FormalProof4FHE.HasteBoots.ParentSeedCollisionOnset
