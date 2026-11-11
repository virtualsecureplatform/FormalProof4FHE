module
public import FormalProof4FHE.HasteBoots.FieldConsumedReplay
public import FormalProof4FHE.HasteBoots.NativeLookupEquality
@[expose] public section

/-! Actual lookup and equality readers retain the complete candidate-byte
trace. Every accepted or rejected offset draw inherits it, across suspension
and arbitrary analysis budgets, without a supplied collector certificate. -/
namespace FormalProof4FHE.HasteBoots.LookupConsumedTrace
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open FieldConsumedReplay (Traced)
noncomputable section
variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

def Lookup (p : ℕ) (machine : NativeLookupChallenge.Machine K) : Prop :=
  (match machine.control with
    | .compression field | .reciprocal _ _ _ field => Traced p field
    | .finished _ _ _ _ _ => True) ∧
    ∀ draw ∈ machine.draws, Traced p draw.coefficients

omit [Field K] [DecidableEq K] in
theorem lookup_initial (p degree w : ℕ) (transcript : Transcript) :
    Lookup p (NativeLookupChallenge.initialExecute (K := K) p degree w transcript).1 :=
  ⟨FieldConsumedReplay.begin_scalar p degree w transcript _,by simp [NativeLookupChallenge.initialExecute]⟩

theorem lookup_tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (valid : Lookup p machine) :
    Lookup p (NativeLookupChallenge.tickExecute basis w width rows machine world).1 := by
  cases control : machine.control with
  | finished y r weights table transcript => simpa only [NativeLookupChallenge.tickExecute,control] using valid
  | compression field =>
    have active : Traced p field := by simpa only [Lookup,control] using valid.1
    have collected := FieldConsumedReplay.drive p 1 field world active
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      rw [result] at collected
      simpa only [NativeLookupChallenge.tickExecute,control,result,Lookup,NativeFieldVector.stateOf] using And.intro collected valid.2
    | finished next transcript =>
      rw [result] at collected
      simp only [NativeLookupChallenge.tickExecute,control,result,Lookup]
      refine ⟨FieldConsumedReplay.begin_scalar p degree w transcript _,?_⟩
      intro draw member
      rcases List.mem_append.mp member with old | added
      · exact valid.2 draw old
      · obtain rfl := List.mem_singleton.mp added
        exact collected
  | reciprocal y weights table field =>
    have active : Traced p field := by simpa only [Lookup,control] using valid.1
    have collected := FieldConsumedReplay.drive p 1 field world active
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      rw [result] at collected
      simpa only [NativeLookupChallenge.tickExecute,control,result,Lookup,NativeFieldVector.stateOf] using And.intro collected valid.2
    | finished next transcript =>
      rw [result] at collected
      have draws : ∀ draw ∈ machine.draws ++ [⟨TypedFieldRequest.scalarValue basis next.values,next⟩], Traced p draw.coefficients := by
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact valid.2 draw old
        · obtain rfl := List.mem_singleton.mp added
          exact collected
      cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue basis next.values) with
      | true => simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,ite_true,Lookup] using And.intro True.intro draws
      | false =>
        simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false,Lookup] using
          And.intro (FieldConsumedReplay.begin_scalar p degree w transcript NativeLookupChallenge.reciprocalLabel) draws

theorem lookup_execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (valid : Lookup p machine) :
    Lookup p (NativeLookupChallenge.execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (lookup_tick basis w width rows machine world valid)

theorem lookup_request (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ) (rows : List (List (ZMod p)))
    (transcript : Transcript) (world : World) :
    Lookup p (OracleProgram.run (NativeLookupChallenge.request basis w width fuel rows transcript) world).run.1 := by
  rw [NativeLookupChallenge.run_request]
  exact lookup_execute basis w width fuel rows _ world (lookup_initial p degree w transcript)

def Equality (p : ℕ) (machine : NativeLookupEquality.Machine count K) : Prop :=
  (∀ field, machine.active = some field → Traced p field) ∧ ∀ draw ∈ machine.draws, Traced p draw.coefficients

omit [Field K] [DecidableEq K] in
theorem equality_initial (p count : ℕ) (transcript : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64) :
    Equality p (NativeLookupEquality.initial (K := K) count transcript roots fits) := by
  constructor
  · intro field impossible; contradiction
  · intro draw impossible; contradiction

omit [DecidableEq K] in
theorem equality_tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (valid : Equality p machine) :
    Equality p (NativeLookupEquality.tickExecute basis w machine world).1 := by
  by_cases done : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,done,ite_true] using valid
  · cases active : machine.active with
    | none =>
      simp only [NativeLookupEquality.tickExecute,done,ite_false,active,Equality]
      refine ⟨?_,valid.2⟩
      intro field same
      exact Option.some.inj same ▸ FieldConsumedReplay.begin_vector p degree w count machine.transcript NativeLookupEquality.pointLabel
    | some field =>
      have collected := FieldConsumedReplay.drive p 1 field world (valid.1 field active)
      cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
      | suspended next =>
        rw [result] at collected
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Equality]
        refine ⟨?_,valid.2⟩
        intro field same
        exact Option.some.inj same ▸ collected
      | finished next transcript =>
        rw [result] at collected
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Equality]
        constructor
        · intro field impossible; contradiction
        · intro draw member
          rcases List.mem_append.mp member with old | added
          · exact valid.2 draw old
          · obtain rfl := List.mem_singleton.mp added
            exact collected

omit [DecidableEq K] in
theorem equality_execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (valid : Equality p machine) :
    Equality p (NativeLookupEquality.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (equality_tick basis w machine world valid)

omit [DecidableEq K] in
theorem equality_request (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ) (transcript : Transcript)
    (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64) (world : World) :
    Equality p (OracleProgram.run (NativeLookupEquality.request basis w count fuel transcript roots fits) world).run.1 := by
  rw [NativeLookupEquality.request,NativeLookupEquality.run_steps]
  exact equality_execute basis w fuel _ world (equality_initial p count transcript roots fits)

end
end FormalProof4FHE.HasteBoots.LookupConsumedTrace
