module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupSampler

@[expose] public section

/-! Computable ordered lookup requests and retries. Projection preserves
original ordinals, repetitions, all retained coefficient records and oracle
observations. No bounded retry policy is introduced. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupBatch

open NativeFields NativeFieldRepresentation NativeExtensionFields
open NativeTranscript (Transcript Observation appendBytes)
open InputIndexedOracle (World)
open NativeUsizeMessage (Usize)
open OracleProgram (Program bind run)

structure Request where
  width : ℕ
  rows : List (List GoldWord)
  repetitions : ℕ

structure Job where
  ordinal : Usize
  repetition : ℕ
  request : Request

inductive Action where
  | request (ordinal : Usize)
  | sample (job : Job)

def schedule {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) : List Action :=
  (List.ofFn (fun index : Fin count =>
    let ordinal : Usize := ⟨index.val,index.isLt.trans_le fits⟩
    Action.request ordinal :: List.ofFn (fun repetition : Fin (requests index).repetitions =>
      Action.sample ⟨ordinal,repetition.val,requests index⟩))).flatten

structure Completed where
  job : Job
  selection : NativeGoldLookupSampler.Machine

inductive Control where
  | ready (todo : List Action) (transcript : Transcript)
  | sampling (job : Job) (todo : List Action) (selection : NativeGoldLookupSampler.Machine)
  | finished (transcript : Transcript)

structure Machine where
  control : Control
  done : List Action
  completed : List Completed

def initial (actions : List Action) (transcript : Transcript) : Machine := ⟨.ready actions transcript,[],[]⟩

def afterSample (machine : Machine) (job : Job) (todo : List Action) (selection : NativeGoldLookupSampler.Machine) : Machine :=
  match selection.control with
  | .finished _ _ _ _ transcript => ⟨.ready todo transcript,machine.done ++ [.sample job],machine.completed ++ [⟨job,selection⟩]⟩
  | _ => {machine with control := .sampling job todo selection}

def tick (w : ℕ) (machine : Machine) : Program Machine :=
  match machine.control with
  | .finished _ => .pure machine
  | .ready [] transcript => .pure {machine with control := .finished transcript}
  | .ready (.request ordinal :: todo) transcript =>
    .pure {machine with
      control := .ready todo (appendBytes transcript NativeLookupBatch.requestLabel (NativeUsizeMessage.encode ordinal))
      done := machine.done ++ [.request ordinal]}
  | .ready (.sample job :: todo) transcript => bind (NativeGoldLookupSampler.initial w transcript)
    (fun selection => .pure {machine with control := .sampling job todo selection})
  | .sampling job todo selection => bind (NativeGoldLookupSampler.tick w job.request.width job.request.rows selection)
    (fun selection => .pure (afterSample machine job todo selection))

def tickExecute (w : ℕ) (machine : Machine) (world : World) : Machine × List Observation :=
  match machine.control with
  | .finished _ => (machine,[])
  | .ready [] transcript => ({machine with control := .finished transcript},[])
  | .ready (.request ordinal :: todo) transcript =>
    ({machine with
      control := .ready todo (appendBytes transcript NativeLookupBatch.requestLabel (NativeUsizeMessage.encode ordinal))
      done := machine.done ++ [.request ordinal]},[])
  | .ready (.sample job :: todo) transcript =>
    let started := NativeGoldLookupSampler.initialExecute w transcript
    ({machine with control := .sampling job todo started.1},started.2)
  | .sampling job todo selection =>
    let trial := NativeGoldLookupSampler.tickExecute w job.request.width job.request.rows selection world
    (afterSample machine job todo trial.1,trial.2)

theorem run_tick (w : ℕ) (machine : Machine) (world : World) : (run (tick w machine) world).run = tickExecute w machine world := by
  cases control : machine.control with
  | finished transcript => simp only [tick,tickExecute,control,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  | ready todo transcript =>
    cases todo with
    | nil => simp only [tick,tickExecute,control,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    | cons action todo =>
      cases action with
      | request ordinal => simp only [tick,tickExecute,control,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
      | sample job => simp only [tick,tickExecute,control,OracleProgram.run_bind,ObservationReplay.run_bind,
          NativeGoldLookupSampler.run_initial,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  | sampling job todo selection => simp only [tick,tickExecute,control,OracleProgram.run_bind,ObservationReplay.run_bind,
      NativeGoldLookupSampler.run_tick,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

def steps (w : ℕ) : ℕ → Machine → Program Machine
  | 0,machine => .pure machine
  | fuel+1,machine => bind (tick w machine) (steps w fuel)

def execute (w : ℕ) : ℕ → Machine → World → Machine × List Observation
  | 0,machine,_ => (machine,[])
  | fuel+1,machine,world =>
    let trial := tickExecute w machine world
    let later := execute w fuel trial.1 world
    (later.1,trial.2 ++ later.2)

theorem run_steps (w fuel : ℕ) (machine : Machine) (world : World) : (run (steps w fuel machine) world).run = execute w fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih => simp only [steps,execute,OracleProgram.run_bind,ObservationReplay.run_bind,run_tick,ih]

theorem execute_add (w first extra : ℕ) (machine : Machine) (world : World) :
    execute w (first+extra) machine world =
      let earlier := execute w first machine world
      let later := execute w extra earlier.1 world
      (later.1,earlier.2 ++ later.2) := by
  induction first generalizing machine with
  | zero => simp only [Nat.zero_add,execute,List.nil_append]
  | succ first ih => simp only [Nat.succ_add,execute,ih,List.append_assoc]

def projectRequest (request : Request) : NativeLookupBatch.Request goldilocksModulus :=
  ⟨request.width,request.rows.map (List.map goldValue),request.repetitions⟩

def projectJob (job : Job) : NativeLookupBatch.Job goldilocksModulus := ⟨job.ordinal,job.repetition,projectRequest job.request⟩

def projectAction : Action → NativeLookupBatch.Action goldilocksModulus
  | .request ordinal => .request ordinal
  | .sample job => .sample (projectJob job)

theorem project_schedule {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) :
    (schedule fits requests).map projectAction = NativeLookupBatch.schedule fits (fun index => projectRequest (requests index)) := by
  simp only [schedule,NativeLookupBatch.schedule,List.map_flatten,List.map_ofFn,Function.comp_def,List.map_cons,
    projectAction,projectJob,projectRequest]

noncomputable section

def projectCompleted (completed : Completed) : NativeLookupBatch.Completed goldilocksModulus Goldilocks3 :=
  ⟨projectJob completed.job,NativeGoldLookupSampler.project completed.selection⟩

def projectControl : Control → NativeLookupBatch.Control goldilocksModulus Goldilocks3
  | .ready todo transcript => .ready (todo.map projectAction) transcript
  | .sampling job todo selection => .sampling (projectJob job) (todo.map projectAction) (NativeGoldLookupSampler.project selection)
  | .finished transcript => .finished transcript

def project (machine : Machine) : NativeLookupBatch.Machine goldilocksModulus Goldilocks3 :=
  ⟨projectControl machine.control,machine.done.map projectAction,machine.completed.map projectCompleted⟩

theorem project_initial (actions : List Action) (transcript : Transcript) :
    project (initial actions transcript) = NativeLookupBatch.initial (actions.map projectAction) transcript := rfl

theorem project_afterSample (machine : Machine) (job : Job) (todo : List Action) (selection : NativeGoldLookupSampler.Machine) :
    project (afterSample machine job todo selection) =
      NativeLookupBatch.afterSample (project machine) (projectJob job) (todo.map projectAction) (NativeGoldLookupSampler.project selection) := by
  cases control : selection.control <;>
    simp only [afterSample,control,project,projectControl,NativeGoldLookupSampler.project,NativeGoldLookupSampler.projectControl,
      NativeLookupBatch.afterSample,List.map_append,List.map_singleton,projectAction,projectCompleted]

theorem project_tick (w : ℕ) (machine : Machine) (world : World) :
    let trial := tickExecute w machine world
    (project trial.1,trial.2) = NativeLookupBatch.tickExecute goldilocksBasis w (project machine) world := by
  cases control : machine.control with
  | finished transcript => simp only [tickExecute,control,project,projectControl,NativeLookupBatch.tickExecute]
  | ready todo transcript =>
    cases todo with
    | nil => simp only [tickExecute,control,project,projectControl,NativeLookupBatch.tickExecute,List.map_nil]
    | cons action todo =>
      cases action with
      | request ordinal => simp only [tickExecute,control,project,projectControl,NativeLookupBatch.tickExecute,List.map_cons,
          projectAction,List.map_append,List.map_nil]
      | sample job =>
        simp only [tickExecute,control,project,projectControl,NativeLookupBatch.tickExecute,List.map_cons,projectAction]
        have started := NativeGoldLookupSampler.project_initial w transcript
        have state := congrArg Prod.fst started
        have observations := congrArg Prod.snd started
        simp only at state observations
        rw [← state,← observations]
  | sampling job todo selection =>
    simp only [tickExecute,control,NativeLookupBatch.tickExecute]
    have trial := NativeGoldLookupSampler.project_tick w job.request.width job.request.rows selection world
    have state := congrArg Prod.fst trial
    have observations := congrArg Prod.snd trial
    simp only at state observations
    change (project (afterSample machine job todo (NativeGoldLookupSampler.tickExecute w job.request.width job.request.rows selection world).1),
      (NativeGoldLookupSampler.tickExecute w job.request.width job.request.rows selection world).2) = _
    rw [project_afterSample]
    simp only [project,projectControl,control,projectJob,projectRequest] at state ⊢
    rw [← state,← observations]

theorem project_execute (w fuel : ℕ) (machine : Machine) (world : World) :
    let result := execute w fuel machine world
    (project result.1,result.2) = NativeLookupBatch.execute goldilocksBasis w fuel (project machine) world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute,NativeLookupBatch.execute]
    have tick := project_tick w machine world
    have state := congrArg Prod.fst tick
    have observations := congrArg Prod.snd tick
    simp only at state observations
    rw [← state,← observations,← ih]

end

end FormalProof4FHE.HasteBoots.NativeGoldLookupBatch
