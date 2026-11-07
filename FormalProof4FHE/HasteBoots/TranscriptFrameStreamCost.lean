module
public import FormalProof4FHE.HasteBoots.TranscriptFrameCost
@[expose] public section

/-! Complete native frame-stream decoding with a linear supplied-byte bound.
Recursion follows strictly consumed bytes, with no trial cap or length-based
runtime fee. Every malformed header/body/trailing byte rejects the stream.
Physical integer/compiler refinement and semantic label checks remain separate. -/
namespace FormalProof4FHE.HasteBoots.TranscriptFrameStreamCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)

def decodeAll (input : Input) : Run (Option (List Frame)) :=
  if input = [] then ⟨some [],1⟩
  else
    let first := TranscriptFrameCost.decode input
    match parsed : first.value with
    | none => ⟨none,first.cost+2⟩
    | some (frame,rest) =>
      let tail := decodeAll rest
      ⟨tail.value.map (frame::·),first.cost+tail.cost+3⟩
termination_by input.length
decreasing_by exact TranscriptFrameCost.decode_progress input frame rest parsed

theorem decodeAll_value (input : Input) :
    (decodeAll input).value = TranscriptFrame.decodeAll input := by
  induction input using (measure (fun xs : Input => xs.length)).wf.induction with
  | h input ih =>
    by_cases empty : input = []
    · subst input
      rw [decodeAll,ite_eq_left rfl,TranscriptFrame.decodeAll,ite_eq_left rfl]
    · rw [decodeAll,ite_eq_right empty,TranscriptFrame.decodeAll,ite_eq_right empty]
      dsimp only
      split
      · rename_i first
        split
        · rfl
        · rename_i frame rest native
          rw [← TranscriptFrameCost.decode_value,first] at native
          contradiction
      · rename_i frame rest first
        split
        · rename_i native
          rw [← TranscriptFrameCost.decode_value,first] at native
          contradiction
        · rename_i other suffix native
          rw [← TranscriptFrameCost.decode_value,first] at native
          have same := Option.some.inj native
          cases same
          exact congrArg (Option.map (frame::·)) (ih rest (TranscriptFrameCost.decode_progress input frame rest first))

theorem decodeAll_cost (input : Input) : (decodeAll input).cost ≤ 24*input.length+1 := by
  induction input using (measure (fun xs : Input => xs.length)).wf.induction with
  | h input ih =>
    by_cases empty : input = []
    · subst input
      rw [decodeAll,ite_eq_left rfl]
      simp
    · have positive : 0 < input.length := by
        cases input with
        | nil => contradiction
        | cons head tail => simp
      rw [decodeAll,ite_eq_right empty]
      dsimp only
      split
      · have first := TranscriptFrameCost.decode_cost input
        dsimp only
        omega
      · rename_i frame rest parsed
        have progress := TranscriptFrameCost.decode_progress input frame rest parsed
        have first := TranscriptFrameCost.decode_success_cost input frame rest parsed
        have tail := ih rest progress
        dsimp only
        omega

theorem decodeAll_sound (input : Input) (frames : List Frame)
    (found : (decodeAll input).value = some frames) :
    (∀ frame ∈ frames, TranscriptFrame.Valid frame) ∧ input = TranscriptFrame.encodeMany frames := by
  rw [decodeAll_value] at found
  exact TranscriptFrame.decodeAll_sound input frames found

theorem decodeAll_encode (frames : List Frame) (valid : ∀ frame ∈ frames, TranscriptFrame.Valid frame) :
    (decodeAll (TranscriptFrame.encodeMany frames)).value = some frames := by
  rw [decodeAll_value]
  exact TranscriptFrame.decodeAll_encodeMany frames valid
end FormalProof4FHE.HasteBoots.TranscriptFrameStreamCost
