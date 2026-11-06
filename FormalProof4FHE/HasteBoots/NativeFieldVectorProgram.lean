module
public import FormalProof4FHE.HasteBoots.NativeFieldVectorValues
public import FormalProof4FHE.HasteBoots.BudgetedUniformSequence
@[expose] public section

/-! A tail-building projection of the native collector. It makes the single
shared candidate budget explicit without changing a read, cursor or log. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldVectorProgram
open InputIndexedOracle (Input World bytes)
open NativeTranscript (FieldPhase Observation)
open OracleProgram (Program bind run)
open NativeFieldVectorValues (project valuesExecute)
noncomputable section

def nextPhase (phase : FieldPhase) (raw : Input) : FieldPhase :=
  {phase with consumed := phase.consumed++raw}

def program (p : ℕ) : (fuel count : ℕ) → FieldPhase → Program (Option (Fin count → ZMod p))
  | _,0,_ => .pure (some Fin.elim0)
  | 0,_+1,_ => .pure none
  | fuel+1,count+1,phase => .read phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p) (fun raw =>
      if CanonicalTranscriptSampler.candidate p raw < p then
        bind (program p fuel count (nextPhase phase raw)) (fun result =>
          .pure (Option.map (Fin.cons (CanonicalTranscriptSampler.candidate p raw : ZMod p)) result))
      else program p fuel (count+1) (nextPhase phase raw))

theorem run_program (p fuel count : ℕ) (phase : FieldPhase) (world : World) :
    (run (program p fuel count phase) world).run = valuesExecute p fuel count phase world := by
  induction fuel generalizing count phase with
  | zero => cases count <;> rfl
  | succ fuel ih =>
    cases count with
    | zero => rfl
    | succ count =>
      let raw := bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)
      by_cases accepted : CanonicalTranscriptSampler.candidate p raw < p
      all_goals simp only [program,run,ObservationReplay.read,ObservationReplay.run_bind,
        valuesExecute,CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,
        CanonicalTranscriptSampler.completed,CanonicalTranscriptSampler.prepend,CanonicalTranscriptSampler.paused,
        accepted,raw,ite_true,ite_false,List.append_nil,OracleProgram.run_bind,WriterT.run_mk,WriterT.run_pure,
        ih,nextPhase]
      all_goals simp [Pure.pure]

/-- The projected program uses exactly the actual collector's ordered log. -/
theorem collect_projection (p fuel count : ℕ) (phase : FieldPhase) (world : World) :
    (project p count 0 (run (NativeFieldVector.collect p fuel (NativeFieldVector.initial phase count)) world).run.1,
      (run (NativeFieldVector.collect p fuel (NativeFieldVector.initial phase count)) world).run.2) =
      (run (program p fuel count phase) world).run := by
  rw [run_program]
  exact NativeFieldVectorValues.collect_projection p fuel count phase world
end
end FormalProof4FHE.HasteBoots.NativeFieldVectorProgram
