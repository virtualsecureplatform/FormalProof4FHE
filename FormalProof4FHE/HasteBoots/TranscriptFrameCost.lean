module
public import FormalProof4FHE.HasteBoots.SizedFrameCost
@[expose] public section

/-! Measured structural native transcript-frame decoding. Kind and both u64
lengths are checked, and suffixes are preserved exactly. Physical integer and
compiler refinement and semantic stage/label checks remain separate. -/
namespace FormalProof4FHE.HasteBoots.TranscriptFrameCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)

def decode : Input → Run (Option (Frame × Input))
  | [] => ⟨none,1⟩
  | kind::tail =>
    if valid : kind.val < 9 then
      let first := SizedFrameCost.read tail
      match first.value with
      | none => ⟨none,first.cost+4⟩
      | some (label,afterLabel) =>
        let second := SizedFrameCost.read afterLabel
        match second.value with
        | none => ⟨none,first.cost+second.cost+6⟩
        | some (message,rest) =>
          ⟨some (⟨⟨kind.val,valid⟩,label,message⟩,rest),first.cost+second.cost+8⟩
    else ⟨none,4⟩

theorem decode_value (input : Input) : (decode input).value = TranscriptFrame.decode input := by
  cases input with
  | nil => rfl
  | cons kind tail =>
    by_cases valid : kind.val < 9
    · cases first : TranscriptFrame.readSized tail with
      | none => simp [decode,TranscriptFrame.decode,valid,SizedFrameCost.read_value,first]
      | some pair =>
        rcases pair with ⟨label,afterLabel⟩
        cases second : TranscriptFrame.readSized afterLabel <;>
          simp [decode,TranscriptFrame.decode,valid,SizedFrameCost.read_value,first,second]
    · simp only [decode,TranscriptFrame.decode,valid,dite_false]

theorem decode_cost (input : Input) : (decode input).cost ≤ 20*input.length+2 := by
  cases input with
  | nil => simp [decode]
  | cons kind tail =>
    have first := SizedFrameCost.read_cost tail
    simp only [decode,List.length_cons]
    split
    · split
      · dsimp only; omega
      · rename_i label afterLabel parsed
        have consumed := SizedFrameCost.read_remaining tail label afterLabel parsed
        have firstSuccess := SizedFrameCost.read_success_cost tail label afterLabel parsed
        have second := SizedFrameCost.read_cost afterLabel
        split <;> dsimp only <;> omega
    · dsimp only; omega

theorem decode_success_cost (input : Input) (frame : Frame) (rest : Input)
    (found : (decode input).value = some (frame,rest)) :
    (decode input).cost ≤ 20*(input.length-rest.length) := by
  have native := found
  rw [decode_value] at native
  have size := congrArg List.length (TranscriptFrame.decode_sound input frame rest native).2
  simp only [List.length_append,TranscriptFrame.encode_length] at size
  cases input with
  | nil => simp only [decode] at found; contradiction
  | cons kind tail =>
    simp only [List.length_cons] at size
    simp only [decode] at found ⊢
    split at found
    · rename_i valid
      simp only [dite_eq_left valid]
      split at found
      · contradiction
      · rename_i label afterLabel first
        split at found
        · contradiction
        · rename_i message suffix second
          have same := Option.some.inj found
          have ended : suffix = rest := congrArg Prod.snd same
          subst suffix
          have left := SizedFrameCost.read_success_cost tail label afterLabel first
          have right := SizedFrameCost.read_success_cost afterLabel message rest second
          have firstRemaining := SizedFrameCost.read_remaining tail label afterLabel first
          have secondRemaining := SizedFrameCost.read_remaining afterLabel message rest second
          dsimp only
          simp only [List.length_cons] at *
          omega
    · contradiction

theorem decode_progress (input : Input) (frame : Frame) (rest : Input)
    (found : (decode input).value = some (frame,rest)) : rest.length < input.length := by
  rw [decode_value] at found
  exact TranscriptFrame.decode_progress input frame rest found
end FormalProof4FHE.HasteBoots.TranscriptFrameCost
