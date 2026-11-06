module
public import FormalProof4FHE.HasteBoots.NativeFieldVector
@[expose] public section

/-! Exact value/log projection of the native shared-candidate-budget collector.
Rejected candidates retain their byte trace and advance only the reader.
Typed suffix values are returned only on actual completion. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldVectorValues
open NativeFieldVector (State advance execute)
open NativeTranscript (FieldPhase Observation)
open InputIndexedOracle (World)
noncomputable section

def project (p count before : ℕ) (state : State) : Option (Fin count → ZMod p) :=
  if state.remaining = 0 then some (fun index => (state.values[before+index.val]?.getD 0 : ZMod p)) else none

theorem values_prefix (p fuel : ℕ) (state : State) (world : World) : state.values <+: (execute p fuel state world).1.values := by
  induction fuel generalizing state with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simp only [execute,complete,ite_true]
      exact List.prefix_refl _
    · simp only [execute,complete,ite_false]
      apply List.IsPrefix.trans (l₂ := (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1).values)
      · cases found : (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1.accepted <;>
          simp [advance,found]
      · exact ih _

theorem project_cons (p count : ℕ) (before : List ℕ) (head : ℕ) (state : State)
    (kept : before ++ [head] <+: state.values) :
    project p (count+1) before.length state =
      Option.map (Fin.cons (head : ZMod p)) (project p count (before.length+1) state) := by
  unfold project
  split
  · simp only [Option.map_some,Option.some.injEq]
    funext index
    induction index using Fin.cases with
    | zero =>
      obtain ⟨tail,same⟩ := kept
      rw [← same,List.getElem?_append_left (by simp),List.getElem?_append_right (by omega)]
      simp
    | succ index =>
      simp only [Fin.val_succ,Fin.cons_succ]
      congr 3
      omega
  · simp

def valuesExecute (p : ℕ) : (fuel count : ℕ) → FieldPhase → World → Option (Fin count → ZMod p) × List Observation
  | _,0,_,_ => (some Fin.elim0,[])
  | 0,_+1,_,_ => (none,[])
  | fuel+1,count+1,phase,world =>
      let trial := CanonicalTranscriptSampler.executePrefix p 1 phase world
      match trial.1.accepted with
      | none => let rest := valuesExecute p fuel (count+1) trial.1.phase world
                (rest.1,trial.2++rest.2)
      | some raw => let rest := valuesExecute p fuel count trial.1.phase world
                    (Option.map (Fin.cons (n := count) (α := fun _ => ZMod p) (CanonicalTranscriptSampler.candidate p raw : ZMod p)) rest.1,trial.2++rest.2)

/-- An exact projection of execution, with the complete ordered native log.
The coefficient index advances on acceptance; fuel advances on every trial. -/
theorem execute_projection (p fuel count : ℕ) (state : State) (world : World) (remaining : state.remaining = count) :
    (project p count state.values.length (execute p fuel state world).1,(execute p fuel state world).2) =
      valuesExecute p fuel count state.phase world := by
  induction fuel generalizing count state with
  | zero =>
    cases count with
    | zero =>
      simp only [execute,valuesExecute,project,remaining,ite_true]
      congr 2
      funext index
      exact Fin.elim0 index
    | succ count => simp [execute,valuesExecute,project,remaining]
  | succ fuel ih =>
    cases count with
    | zero =>
      rw [NativeFieldVector.execute_complete p (fuel+1) state world remaining]
      simp only [valuesExecute,project,remaining,ite_true]
      congr 2
      funext index
      exact Fin.elim0 index
    | succ count =>
      have pending : state.remaining ≠ 0 := by omega
      let trial := CanonicalTranscriptSampler.executePrefix p 1 state.phase world
      let next := advance p state trial.1
      cases found : trial.1.accepted with
      | none =>
        have size : next.remaining = count+1 := by simp only [next,advance,found]; exact remaining
        have earlier := ih (count+1) next size
        simpa only [execute,pending,ite_false,valuesExecute,trial,found,advance,next] using
          congrArg (fun result => (result.1,trial.2++result.2)) earlier
      | some raw =>
        have size : next.remaining = count := by simp only [next,advance,found,remaining]; omega
        have earlier := ih count next size
        have kept : state.values ++ [CanonicalTranscriptSampler.candidate p raw] <+: (execute p fuel next world).1.values := by
          simpa only [next,advance,found] using values_prefix p fuel next world
        have split := project_cons p count state.values (CanonicalTranscriptSampler.candidate p raw) (execute p fuel next world).1 kept
        have length : next.values.length = state.values.length+1 := by simp [next,advance,found]
        rw [length] at earlier
        have combined := congrArg (fun result => (Option.map (Fin.cons (n := count) (α := fun _ => ZMod p) (CanonicalTranscriptSampler.candidate p raw : ZMod p)) result.1,trial.2++result.2)) earlier
        rw [← split] at combined
        simpa only [execute,pending,ite_false,valuesExecute,trial,found,advance,next] using combined

/-- The actual OracleProgram collector has the same typed values and log. -/
theorem collect_projection (p fuel count : ℕ) (phase : FieldPhase) (world : World) :
    (project p count 0 (OracleProgram.run (NativeFieldVector.collect p fuel (NativeFieldVector.initial phase count)) world).run.1,
      (OracleProgram.run (NativeFieldVector.collect p fuel (NativeFieldVector.initial phase count)) world).run.2) =
      valuesExecute p fuel count phase world := by
  rw [NativeFieldVector.run_collect]
  exact execute_projection p fuel count (NativeFieldVector.initial phase count) world rfl
end
end FormalProof4FHE.HasteBoots.NativeFieldVectorValues
