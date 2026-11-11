module
public import FormalProof4FHE.HasteBoots.ReceiptCollisionRisk
@[expose] public section

/-! A collision among named receipt payloads is introduced by one new key.
This deterministic first-onset statement retains hash naming and empty-read
semantics and does not identify distinct raw keys through their digests. -/
namespace FormalProof4FHE.HasteBoots.ReceiptCollisionOnset
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open ReceiptDigestFixation (Collision)
open ReceiptCandidateCompletion (digest)
open scoped Classical
noncomputable section

theorem payloads_mono (earlier later : List Observation) (included : earlier.Sublist later) :
    ReceiptPayloadView.payloads earlier ⊆ ReceiptPayloadView.payloads later := by
  intro raw named
  obtain ⟨entry,member,parsed⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp named)
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨entry,included.subset member,parsed⟩)

theorem mono (earlier later : List Observation) (world : World) (included : earlier.Sublist later)
    (bad : Collision earlier world) : Collision later world := by
  obtain ⟨left,leftNamed,right,rightNamed,different,equal⟩ := bad
  exact ⟨left,payloads_mono earlier later included leftNamed,right,payloads_mono earlier later included rightNamed,different,equal⟩

theorem singleton (entry : Observation) (raw : Input) (named : ReceiptPayloadView.candidate entry = some raw) :
    ReceiptPayloadView.payloads [entry] = {raw} := by
  simp only [ReceiptPayloadView.payloads,List.filterMap_cons,named,List.filterMap_nil,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty]

theorem onset (history : List Observation) (entry : Observation) (world : World)
    (safe : ¬ Collision history world) (bad : Collision (history ++ [entry]) world) :
    ∃ raw, ReceiptPayloadView.candidate entry = some raw ∧ raw ∉ ReceiptPayloadView.payloads history ∧
      ∃ old ∈ ReceiptPayloadView.payloads history, digest world raw = digest world old := by
  cases named : ReceiptPayloadView.candidate entry with
  | none =>
    have unchanged : ReceiptPayloadView.payloads (history ++ [entry]) = ReceiptPayloadView.payloads history := by
      rw [ReceiptPayloadView.append]
      have empty : ReceiptPayloadView.payloads [entry] = ∅ := by
        simp only [ReceiptPayloadView.payloads,List.filterMap_cons,named,List.filterMap_nil,List.toFinset_nil]
      rw [empty,Finset.union_empty]
    exact False.elim (safe (by simpa only [Collision,unchanged] using bad))
  | some raw =>
    have added : ReceiptPayloadView.payloads (history ++ [entry]) = ReceiptPayloadView.payloads history ∪ {raw} := by
      rw [ReceiptPayloadView.append,singleton entry raw named]
    have fresh : raw ∉ ReceiptPayloadView.payloads history := by
      intro old
      have unchanged : ReceiptPayloadView.payloads (history ++ [entry]) = ReceiptPayloadView.payloads history := by
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
      ReceiptPayloadView.candidate entry = some raw ∧ raw ∉ ReceiptPayloadView.payloads (history.take position) ∧
      ∃ old ∈ ReceiptPayloadView.payloads (history.take position), digest world raw = digest world old := by
  have witness : ∃ n, Collision (history.take (n+1)) world := ⟨history.length,by rw [List.take_of_length_le (by omega)]; exact bad⟩
  let position := Nat.find witness
  have occurred := Nat.find_spec witness
  have before : ¬ Collision (history.take position) world := by
    cases equal : position with
    | zero => simp [Collision,ReceiptPayloadView.payloads]
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
end FormalProof4FHE.HasteBoots.ReceiptCollisionOnset
