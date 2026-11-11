module
public import FormalProof4FHE.HasteBoots.BatchFieldContextName
@[expose] public section

/-! A parameter preimage computed in the complete native execution is
already observed before the first read of an input naming its digest,
outside the existing late-context event. The new read cannot be a hash. -/
namespace FormalProof4FHE.HasteBoots.ContextAtFirstRead
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open OracleProgram (Program run runPrefix)
noncomputable section

theorem take_succ {T : Type} (values : List T) (position : ℕ) (value : T) (found : values[position]? = some value) :
    values.take (position+1) = values.take position ++ [value] := by
  induction position generalizing values with
  | zero => cases values <;> simp_all
  | succ position ih =>
    cases values with
    | nil => simp at found
    | cons head rest =>
      simp only [List.getElem?_cons_succ] at found
      simpa only [List.take_succ_cons,List.cons_append] using congrArg (List.cons head) (ih rest found)

theorem next_log {A : Type} {program : Program A} {world : World} {input : Input}
    (first : ProgramFirstStreamRead.First program world input) :
    (runPrefix (first.position+1) program world).run.2 = (runPrefix first.position program world).run.2 ++
      [Observation.output input first.offset (InputIndexedOracle.bytes world input first.offset first.count)] := by
  rw [ReceiptProgramObservation.history,ReceiptProgramObservation.history]
  exact take_succ _ _ _ first.outputAt

theorem observed_or_bad {A : Type} (program : Program A) (world : World) (input : Input)
    (first : ProgramFirstStreamRead.First program world input)
    (parameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) (digest : Digest)
    (computed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.1 = some digest)
    (full : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.2.Sublist (run program world).run.2)
    (named : digest ∈ ContextDigestTargets.fromInput input) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.2.Sublist
      (runPrefix first.position program world).run.2 ∨ ProgramContextTarget.Bad program world := by
  have present : Observation.output input first.offset (InputIndexedOracle.bytes world input first.offset first.count) ∈
      (runPrefix (first.position+1) program world).run.2 := by
    rw [next_log first]
    exact List.mem_append_right _ List.mem_cons_self
  have target := ContextDigestTargets.named _ _ present digest named
  rcases ProgramContextTarget.context_observed_or_bad program world (first.position+1) parameters digest computed full target with after | bad
  · left
    rw [GoldContextCollision.context_run] at after ⊢
    have member := List.singleton_sublist.mp after
    rw [next_log first,List.mem_append,List.mem_singleton] at member
    rcases member with before | impossible
    · exact List.singleton_sublist.mpr before
    · cases impossible
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.ContextAtFirstRead
