module
public import FormalProof4FHE.HasteBoots.EqualityCandidateResidual
@[expose] public section

/-! Coefficient collection depends on the exact stream input and cursor,
not transcript labels or profiles. Equality events can therefore use one
canonical phase for the original input without changing their sampled values. -/
namespace FormalProof4FHE.HasteBoots.EqualityCollectorInputCongruence
open InputIndexedOracle (Input World)
open NativeTranscript (FieldPhase)
noncomputable section

theorem program_congr (p fuel count : ℕ) (left right : FieldPhase)
    (input : left.pending.input = right.pending.input) (cursor : left.consumed.length = right.consumed.length) :
    NativeFieldVectorProgram.program p fuel count left = NativeFieldVectorProgram.program p fuel count right := by
  induction fuel generalizing count left right with
  | zero => cases count <;> rfl
  | succ fuel ih =>
    cases count with
    | zero => rfl
    | succ count =>
      rw [NativeFieldVectorProgram.program,NativeFieldVectorProgram.program,input,cursor]
      congr 1
      funext raw
      have nextInput : (NativeFieldVectorProgram.nextPhase left raw).pending.input =
          (NativeFieldVectorProgram.nextPhase right raw).pending.input := input
      have nextCursor : (NativeFieldVectorProgram.nextPhase left raw).consumed.length =
          (NativeFieldVectorProgram.nextPhase right raw).consumed.length := by
        simp only [NativeFieldVectorProgram.nextPhase,List.length_append,cursor]
      split
      · rw [ih count _ _ nextInput nextCursor]
      · exact ih (count+1) _ _ nextInput nextCursor

theorem coefficients (p fuel count : ℕ) (left right : FieldPhase) (world : World)
    (input : left.pending.input = right.pending.input) (cursor : left.consumed.length = right.consumed.length) :
    NativeFieldVectorLaw.values p fuel count left world = NativeFieldVectorLaw.values p fuel count right world := by
  rw [NativeFieldVectorLaw.program_values,NativeFieldVectorLaw.program_values,program_congr p fuel count left right input cursor]

theorem values (n fuel : ℕ) (left right : FieldPhase) (world : World)
    (input : left.pending.input = right.pending.input) (cursor : left.consumed.length = right.consumed.length) :
    GoldEqualityPointLaw.values n fuel left world = GoldEqualityPointLaw.values n fuel right world := by
  unfold GoldEqualityPointLaw.values
  rw [coefficients NativeFields.goldilocksModulus fuel (n*3) left right world input cursor]

def phase (input : Input) : FieldPhase := ⟨⟨input,fun _ => 0⟩,NativeLookupEquality.pointLabel,[]⟩

theorem original_values (n fuel : ℕ) (field : NativeFieldVector.State) (world : World) :
    GoldEqualityPointLaw.values n fuel (EqualityCollectorTrace.start field) world =
      GoldEqualityPointLaw.values n fuel (phase field.phase.pending.input) world :=
  values n fuel _ _ world rfl rfl

end
end FormalProof4FHE.HasteBoots.EqualityCollectorInputCongruence
