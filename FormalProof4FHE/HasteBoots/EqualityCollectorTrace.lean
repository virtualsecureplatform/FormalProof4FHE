module
public import FormalProof4FHE.HasteBoots.GoldEqualityPointLaw
@[expose] public section

/-! Active and completed equality vectors retain their original coefficient
collector through every analysis pause and native receipt finalization. -/
namespace FormalProof4FHE.HasteBoots.EqualityCollectorTrace
open InputIndexedOracle (World)
open NativeTranscript (Transcript FieldPhase)
open NativeLookupEquality (Machine Draw pointLabel)
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
noncomputable section

def start (field : NativeFieldVector.State) : FieldPhase := ⟨field.phase.pending,pointLabel,[]⟩

def Source (n : ℕ) (field : NativeFieldVector.State) (world : World) : Prop :=
  ∃ fuel, (NativeFieldVector.execute goldilocksModulus fuel (NativeFieldVector.initial (start field) (n*3)) world).1 = field

def Traced {n : ℕ} (machine : Machine n Goldilocks3) (world : World) : Prop :=
  (∀ field, machine.active = some field → Source n field world) ∧
    ∀ draw ∈ machine.draws, Source n draw.coefficients world ∧ draw.coefficients.remaining = 0

theorem begin_source (n : ℕ) (transcript : Transcript) (world : World) :
    Source n (TypedFieldVector.beginExecute goldilocksModulus 3 7 n transcript pointLabel).1 world := ⟨0,rfl⟩

theorem collect_source (n fuel : ℕ) (field : NativeFieldVector.State) (world : World) (source : Source n field world) :
    Source n (NativeFieldVector.execute goldilocksModulus fuel field world).1 world := by
  obtain ⟨prior,old⟩ := source
  have header := NativeFieldVector.header_preserved goldilocksModulus fuel field world
  have startEq : start (NativeFieldVector.execute goldilocksModulus fuel field world).1 = start field := by
    unfold start
    rw [header.1]
  refine ⟨prior+fuel,?_⟩
  rw [startEq,NativeFieldVector.execute_add]
  dsimp only
  rw [old]

theorem drive_source (n fuel : ℕ) (field : NativeFieldVector.State) (world : World) (source : Source n field world) :
    Source n (NativeFieldVector.stateOf (NativeFieldVector.driveExecute goldilocksModulus fuel field world).1) world := by
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.finish_state]
  exact collect_source n fuel field world source

theorem initial (n : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) :
    Traced (NativeLookupEquality.initial n transcript roots fits) world :=
  ⟨by simp [NativeLookupEquality.initial],by simp [NativeLookupEquality.initial]⟩

theorem tick {n : ℕ} (machine : Machine n Goldilocks3) (world : World) (traced : Traced machine world) :
    Traced (NativeLookupEquality.tickExecute goldilocksBasis 7 machine world).1 world := by
  by_cases done : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,done,ite_true] using traced
  · cases active : machine.active with
    | none =>
      simp only [NativeLookupEquality.tickExecute,done,ite_false,active,Traced]
      refine ⟨?_,traced.2⟩
      intro field same
      cases Option.some.inj same
      exact begin_source n machine.transcript world
    | some field =>
      have collected := drive_source n 1 field world (traced.1 field active)
      have status := NativeFieldVector.finish_status world (NativeFieldVector.execute goldilocksModulus 1 field world).1
      change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 at status
      cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
      | suspended next =>
        rw [result] at collected
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Traced]
        exact ⟨by intro field same; cases Option.some.inj same; exact collected,traced.2⟩
      | finished coefficients transcript =>
        rw [result] at collected status
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Traced]
        refine ⟨by simp,?_⟩
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact traced.2 draw old
        · cases List.mem_singleton.mp added
          exact ⟨collected,status⟩

theorem execute {n : ℕ} (fuel : ℕ) (machine : Machine n Goldilocks3) (world : World) (traced : Traced machine world) :
    Traced (NativeLookupEquality.execute goldilocksBasis 7 fuel machine world).1 world := by
  induction fuel generalizing machine with
  | zero => exact traced
  | succ fuel ih => exact ih _ (tick machine world traced)

theorem initialized (n fuel : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) :
    Traced (NativeLookupEquality.execute goldilocksBasis 7 fuel (NativeLookupEquality.initial n transcript roots fits) world).1 world :=
  execute fuel _ world (initial n transcript roots fits world)

/-- A retained equality draw is an eventual result of the same vector reader;
no completed-draw distribution is postulated. -/
theorem draw_value {n : ℕ} (fuel : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) (draw : Draw n Goldilocks3)
    (member : draw ∈ (NativeLookupEquality.execute goldilocksBasis 7 fuel
      (NativeLookupEquality.initial n transcript roots fits) world).1.draws) :
    ∃ budget, GoldEqualityPointLaw.values n budget (start draw.coefficients) world =
      some (TypedFieldVector.value goldilocksBasis n draw.coefficients.values) := by
  obtain ⟨⟨budget,collected⟩,complete⟩ := (initialized n fuel transcript roots fits world).2 draw member
  exact ⟨budget,GoldEqualityPointLaw.completed_values n budget _ world draw.coefficients collected complete⟩

/-- The initialized equality machine also derives the interpretation of the
stored point, so the result is the original draw rather than a substitute. -/
theorem draw_point {n : ℕ} (fuel : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) (draw : Draw n Goldilocks3)
    (member : draw ∈ (NativeLookupEquality.execute goldilocksBasis 7 fuel
      (NativeLookupEquality.initial n transcript roots fits) world).1.draws) :
    ∃ budget, GoldEqualityPointLaw.values n budget (start draw.coefficients) world = some draw.point := by
  have valid := NativeLookupEquality.execute_valid goldilocksBasis 7 fuel
    (NativeLookupEquality.initial n transcript roots fits) world
    (NativeLookupEquality.initial_valid goldilocksBasis n transcript roots fits)
  obtain ⟨budget,value⟩ := draw_value fuel transcript roots fits world draw member
  exact ⟨budget,by rw [(valid.2 draw member).2.2]; exact value⟩

end
end FormalProof4FHE.HasteBoots.EqualityCollectorTrace
