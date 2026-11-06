module
public import FormalProof4FHE.HasteBoots.CausalStreamCoverage
@[expose] public section

/-! Recover the complete prefix before a stream's first positive read from
any later mixed log. Starts, hashes and empty reads are retained in the
prefix but do not count as exposure. No seed-window or lifetime cap is used. -/
namespace FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open CausalStreamExposure (seen touches)
open CausalStreamCoverage (locate)

def recover (input : Input) (history : List Observation) : Option (List Observation) :=
  (locate input history).map (history.take ·)

theorem recover_none (input : Input) (history : List Observation) :
    recover input history = none ↔ seen history input = false := by
  simp only [recover,Option.map_eq_none_iff,CausalStreamCoverage.locate_none]

theorem recover_at (input : Input) (before after : List Observation) (entry : Observation)
    (unseen : seen before input = false) (hit : touches input entry = true) :
    recover input (before++entry::after) = some before := by
  have first := (CausalStreamCoverage.locate_some input _ before.length).mpr ⟨before,entry,after,rfl,rfl,unseen,hit⟩
  simp only [recover,first,Option.map_some,List.take_left]

theorem recover_sound (input : Input) (history before : List Observation)
    (found : recover input history = some before) :
    seen before input = false ∧ ∃ offset values after,
      values ≠ [] ∧ history = before++ .output input offset values :: after := by
  obtain ⟨index,located,equal⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨initial,entry,after,split,length,unseen,hit⟩ := (CausalStreamCoverage.locate_some input history index).mp located
  have same : initial = before := by
    rw [split,← length,List.take_left] at equal
    exact equal
  subst initial
  refine ⟨unseen,?_⟩
  cases entry with
  | start key => simp [touches] at hit
  | hash key digest => simp [touches] at hit
  | output key offset values =>
    have info : key = input ∧ 0 < values.length := of_decide_eq_true hit
    rcases info with ⟨rfl,positive⟩
    exact ⟨offset,values,after,by simpa only [← List.length_pos_iff] using positive,split⟩

/-- Once found, the original complete prefix survives every suffix. -/
theorem recover_append (input : Input) (before after : List Observation) (prefixLog : List Observation)
    (found : recover input before = some prefixLog) : recover input (before++after) = some prefixLog := by
  obtain ⟨index,located,equal⟩ := Option.map_eq_some_iff.mp found
  have bound := CausalStreamCoverage.locate_lt input before index located
  simp only [recover,CausalStreamCoverage.locate_append,located,Option.map_some]
  rw [List.take_append_of_le_length (Nat.le_of_lt bound)]
  exact congrArg some equal
end FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
