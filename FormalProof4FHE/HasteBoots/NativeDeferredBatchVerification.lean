module

public import FormalProof4FHE.HasteBoots.NativeDeferredOpeningBatch
public import FormalProof4FHE.HasteBoots.NativeGoldBatchPcsProgram
@[expose] public section

/-! Native deferred registry sealing and ordered batch execution. Calls select
first-original owners and carry all inserted claims. Receipts are derived from
actual causal executions; successful completion accounts for every packet.
This operational layer does not establish application soundness or work. -/
namespace FormalProof4FHE.HasteBoots.NativeDeferredBatchVerification
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeGoldBlockCode (Stored Tables)
open NativeGoldPcsWire (Query)
open NativeGoldBatchOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation)
open NativeGoldBatchPcsProgram (Scheduler)
open NativeDeferredOpeningBatch (State)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)
open OracleSpec OracleComp
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure Call where
  group : ℕ
  slot : ℕ
  oracle : Oracle Stored
  queries : Vector Query
  values : Vector Row
  opening : Opening

/-- The parameter/root object comes from the first ORIGINAL registry representative. -/
def call (registry : Vector (Oracle Stored)) (state : State)
    (group : Fin (NativeSourceRegistry.groupCount state.sources)) (opening : Opening) : Option Call :=
  let owner := NativeSourceRegistry.representative state.sources group
  registry.val[owner.val]?.map (fun oracle =>
    ⟨group.val,owner.val,oracle,NativeDeferredOpeningBatch.groupQueries state group,NativeDeferredOpeningBatch.groupValues state group,opening⟩)

def Call.context (call : Call) (tables : Tables) (fieldFuel : ℕ) (parent : Transcript) : NativeGoldBatchPcsProgram.Context :=
  ⟨tables,call.oracle.parameters,parent,call.oracle.root,call.queries,call.values,call.opening,fieldFuel⟩

theorem call_spec (registry : Vector (Oracle Stored)) (state : State) (group : Fin (NativeSourceRegistry.groupCount state.sources))
    (opening : Opening) (result : Call) (computed : call registry state group opening = some result) :
    result.group = group.val ∧ result.slot = (NativeSourceRegistry.representative state.sources group).val ∧
      registry.val[result.slot]? = some result.oracle ∧ result.queries = NativeDeferredOpeningBatch.groupQueries state group ∧
      result.values = NativeDeferredOpeningBatch.groupValues state group ∧ result.opening = opening := by
  obtain ⟨oracle,found,same⟩ := Option.map_eq_some_iff.mp computed
  subst result
  exact ⟨rfl,rfl,found,rfl,rfl,rfl⟩

structure Receipt (Memory : Type) where
  call : Call
  before : Transcript
  memory : Memory
  work : NativeGoldBatchPcsProgram.Prepared
  completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length
  after : Transcript
structure Progress (Memory : Type) where
  parent : Transcript
  memory : Memory
  receipts : List (Receipt Memory)
inductive Result (Memory : Type) where
  | done (progress : Progress Memory)
  | stopped (progress : Progress Memory) (call : Call) (outcome : NativeGoldBatchPcsProgram.Outcome Memory)
  | indexingUnavailable (progress : Progress Memory) (group slot : ℕ)
  | packetUnavailable (progress : Progress Memory)

def Result.progress {Memory : Type} : Result Memory → Progress Memory
  | .done progress => progress
  | .stopped progress _ _ => progress
  | .indexingUnavailable progress _ _ => progress
  | .packetUnavailable progress => progress

def advance {Memory : Type} (before : Progress Memory) (call : Call) : NativeGoldBatchPcsProgram.Outcome Memory → Option (Progress Memory)
  | .prior _ => none
  | .completed work completion => match completion.status with
    | .accepted parent => some ⟨parent,completion.pool.memory,before.receipts++[⟨call,before.parent,before.memory,work,completion,parent⟩]⟩
    | _ => none

theorem advance_spec {Memory : Type} (before : Progress Memory) (call : Call) (outcome : NativeGoldBatchPcsProgram.Outcome Memory)
    (after : Progress Memory) (advanced : advance before call outcome = some after) :
    ∃ work completion parent, outcome = .completed work completion ∧ completion.status = .accepted parent ∧
      after = ⟨parent,completion.pool.memory,before.receipts++[⟨call,before.parent,before.memory,work,completion,parent⟩]⟩ := by
  cases outcome with
  | prior previous => contradiction
  | completed work completion =>
    cases status : completion.status with
    | accepted parent =>
      simp only [advance,status] at advanced
      exact ⟨work,completion,parent,rfl,status,(Option.some.inj advanced).symm⟩
    | columns => simp only [advance,status] at advanced; contradiction
    | claim reason => simp only [advance,status] at advanced; contradiction
    | suspended => simp only [advance,status] at advanced; contradiction

def loop {Memory : Type} (tables : Tables) (registry : Vector (Oracle Stored)) (state : State) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) :
    List (Fin (NativeSourceRegistry.groupCount state.sources)) → List Opening → Progress Memory → Program (Result Memory)
  | [],[],before => .pure (.done before)
  | group::rest,opening::openings,before => match call registry state group opening with
    | none => .pure (.indexingUnavailable before group.val (NativeSourceRegistry.representative state.sources group).val)
    | some call => bind (NativeGoldBatchPcsProgram.program (call.context tables fieldFuel before.parent) choose workerFuel before.memory)
      (fun outcome => match advance before call outcome with
        | none => .pure (.stopped before call outcome)
        | some after => loop tables registry state fieldFuel choose workerFuel rest openings after)
  | _,_,before => .pure (.packetUnavailable before)

structure Context where
  tables : Tables
  registry : Vector (Oracle Stored)
  state : State
  proof : Vector Opening
  fieldFuel : ℕ
  workerFuel : ℕ
inductive Outcome (Memory : Type) where
  | sealRejected (state : State) (reason : NativeDeferredOpeningBatch.Error)
  | verification (result : Result Memory)

/-- Packet count and seal precede the ordered batch calls, with one packet per used group. -/
def program {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) : Program (Outcome Memory) :=
  let sealed := NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length
  match sealed.2 with
  | .error reason => .pure (.sealRejected sealed.1 reason)
  | .ok () => bind (loop ctx.tables ctx.registry ctx.state ctx.fieldFuel choose ctx.workerFuel
      (NativeDeferredOpeningBatch.usedGroups ctx.state) ctx.proof.val ⟨sealed.1.parent,memory,[]⟩)
      (fun result => .pure (.verification result))

def Checked {Memory : Type} (tables : Tables) (fieldFuel : ℕ) (choose : Scheduler Memory) (workerFuel : ℕ) (world : World)
    (receipt : Receipt Memory) : Prop :=
  (run (NativeGoldBatchPcsProgram.program (receipt.call.context tables fieldFuel receipt.before) choose workerFuel receipt.memory) world).run.1 =
      .completed receipt.work receipt.completion ∧ receipt.completion.status = .accepted receipt.after

inductive Trace {Memory : Type} (tables : Tables) (registry : Vector (Oracle Stored)) (state : State) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) (world : World) :
    List (Fin (NativeSourceRegistry.groupCount state.sources)) → List Opening → Progress Memory → Result Memory → List Observation → Prop
  | done (before : Progress Memory) : Trace tables registry state fieldFuel choose workerFuel world [] [] before (.done before) []
  | packets (groups : List (Fin (NativeSourceRegistry.groupCount state.sources))) (openings : List Opening) (before : Progress Memory)
      (mismatch : groups = [] ∧ openings ≠ [] ∨ groups ≠ [] ∧ openings = []) :
      Trace tables registry state fieldFuel choose workerFuel world groups openings before (.packetUnavailable before) []
  | index (group : Fin (NativeSourceRegistry.groupCount state.sources)) (rest : List (Fin (NativeSourceRegistry.groupCount state.sources)))
      (opening : Opening) (openings : List Opening) (before : Progress Memory) (missing : call registry state group opening = none) :
      Trace tables registry state fieldFuel choose workerFuel world (group::rest) (opening::openings) before
        (.indexingUnavailable before group.val (NativeSourceRegistry.representative state.sources group).val) []
  | stopped (group : Fin (NativeSourceRegistry.groupCount state.sources)) (rest : List (Fin (NativeSourceRegistry.groupCount state.sources)))
      (opening : Opening) (openings : List Opening) (before : Progress Memory) (planned : Call) (outcome : NativeGoldBatchPcsProgram.Outcome Memory)
      (log : List Observation) (computed : call registry state group opening = some planned)
      (executed : (run (NativeGoldBatchPcsProgram.program (planned.context tables fieldFuel before.parent) choose workerFuel before.memory) world).run = (outcome,log))
      (failed : advance before planned outcome = none) :
      Trace tables registry state fieldFuel choose workerFuel world (group::rest) (opening::openings) before (.stopped before planned outcome) log
  | passed (group : Fin (NativeSourceRegistry.groupCount state.sources)) (rest : List (Fin (NativeSourceRegistry.groupCount state.sources)))
      (opening : Opening) (openings : List Opening) (before after : Progress Memory) (planned : Call) (outcome : NativeGoldBatchPcsProgram.Outcome Memory)
      (log : List Observation) (result : Result Memory) (later : List Observation) (computed : call registry state group opening = some planned)
      (executed : (run (NativeGoldBatchPcsProgram.program (planned.context tables fieldFuel before.parent) choose workerFuel before.memory) world).run = (outcome,log))
      (advanced : advance before planned outcome = some after)
      (tail : Trace tables registry state fieldFuel choose workerFuel world rest openings after result later) :
      Trace tables registry state fieldFuel choose workerFuel world (group::rest) (opening::openings) before result (log++later)

theorem loop_trace {Memory : Type} (tables : Tables) (registry : Vector (Oracle Stored)) (state : State) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) (groups : List (Fin (NativeSourceRegistry.groupCount state.sources)))
    (openings : List Opening) (before : Progress Memory) (world : World) :
    Trace tables registry state fieldFuel choose workerFuel world groups openings before
      (run (loop tables registry state fieldFuel choose workerFuel groups openings before) world).run.1
      (run (loop tables registry state fieldFuel choose workerFuel groups openings before) world).run.2 := by
  induction groups generalizing openings before with
  | nil =>
    cases openings with
    | nil => exact .done before
    | cons opening rest => exact .packets [] (opening::rest) before (Or.inl ⟨rfl,by simp⟩)
  | cons group rest ih =>
    cases openings with
    | nil => exact .packets (group::rest) [] before (Or.inr ⟨by simp,rfl⟩)
    | cons opening openings =>
      cases computed : call registry state group opening with
      | none => simpa only [loop,computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using Trace.index group rest opening openings before computed
      | some planned =>
        let current := (run (NativeGoldBatchPcsProgram.program (planned.context tables fieldFuel before.parent) choose workerFuel before.memory) world).run
        have currentEq : (run (NativeGoldBatchPcsProgram.program (planned.context tables fieldFuel before.parent) choose workerFuel before.memory) world).run = (current.1,current.2) := rfl
        cases advanced : advance before planned
            (run (NativeGoldBatchPcsProgram.program (planned.context tables fieldFuel before.parent) choose workerFuel before.memory) world).run.1 with
        | none =>
          simpa only [current,loop,computed,OracleProgram.run_bind,ObservationReplay.run_bind,advanced,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil] using
            Trace.stopped group rest opening openings before planned current.1 current.2 computed currentEq advanced
        | some after =>
          simpa only [current,loop,computed,OracleProgram.run_bind,ObservationReplay.run_bind,advanced] using
            Trace.passed group rest opening openings before after planned current.1 current.2 _ _ computed currentEq advanced (ih openings after)

theorem Trace.receipts {Memory : Type} {tables : Tables} {registry : Vector (Oracle Stored)} {state : State} {fieldFuel : ℕ}
    {choose : Scheduler Memory} {workerFuel : ℕ} {world : World}
    {groups : List (Fin (NativeSourceRegistry.groupCount state.sources))} {openings : List Opening} {before : Progress Memory}
    {result : Result Memory} {log : List Observation} (trace : Trace tables registry state fieldFuel choose workerFuel world groups openings before result log) :
    ∀ receipt ∈ result.progress.receipts, receipt ∈ before.receipts ∨
      Checked tables fieldFuel choose workerFuel world receipt ∧
      (run (NativeGoldBatchPcsProgram.program (receipt.call.context tables fieldFuel receipt.before) choose workerFuel receipt.memory) world).run.2.Sublist log := by
  induction trace with
  | done before => intro receipt member; exact Or.inl member
  | packets groups openings before mismatch => intro receipt member; exact Or.inl member
  | index group rest opening openings before missing => intro receipt member; exact Or.inl member
  | stopped group rest opening openings before planned outcome log computed executed failed => intro receipt member; exact Or.inl member
  | passed group rest opening openings before after planned outcome log result later computed executed advanced tail ih =>
    obtain ⟨work,completion,next,outcomeEq,accepted,same⟩ := advance_spec before planned outcome after advanced
    intro receipt member
    rcases ih receipt member with previous | ⟨checked,observed⟩
    · rw [same] at previous
      rcases List.mem_append.mp previous with old | added
      · exact Or.inl old
      · obtain rfl := List.mem_singleton.mp added
        refine Or.inr ⟨⟨?_,accepted⟩,?_⟩
        · exact (congrArg Prod.fst executed).trans outcomeEq
        · rw [congrArg Prod.snd executed]
          exact List.sublist_append_left _ _
    · exact Or.inr ⟨checked,observed.trans (List.sublist_append_right _ _)⟩

theorem Trace.done_packets {Memory : Type} {tables : Tables} {registry : Vector (Oracle Stored)} {state : State} {fieldFuel : ℕ}
    {choose : Scheduler Memory} {workerFuel : ℕ} {world : World}
    {groups : List (Fin (NativeSourceRegistry.groupCount state.sources))} {openings : List Opening} {before : Progress Memory}
    {result : Result Memory} {log : List Observation} (trace : Trace tables registry state fieldFuel choose workerFuel world groups openings before result log) :
    ∀ after, result = .done after →
      after.receipts.map (fun receipt => (receipt.call.group,receipt.call.opening)) =
        before.receipts.map (fun receipt => (receipt.call.group,receipt.call.opening)) ++ (groups.map Fin.val).zip openings := by
  induction trace with
  | done before => intro after same; cases same; simp
  | packets groups openings before mismatch => intro after same; cases same
  | index group rest opening openings before missing => intro after same; cases same
  | stopped group rest opening openings before planned outcome log computed executed failed => intro after same; cases same
  | passed group rest opening openings before after planned outcome log result later computed executed advanced tail ih =>
    intro final same
    have ordered := ih final same
    obtain ⟨work,completion,next,outcomeEq,accepted,recorded⟩ := advance_spec before planned outcome after advanced
    have spec := call_spec registry state group opening planned computed
    rw [ordered,recorded]
    simp only [List.map_append,List.map, List.zip_cons_cons,List.append_assoc]
    rw [spec.1,spec.2.2.2.2.2]
    rfl

theorem program_trace {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification result) :
    (NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length).2 = .ok () ∧
    Trace ctx.tables ctx.registry ctx.state ctx.fieldFuel choose ctx.workerFuel world
      (NativeDeferredOpeningBatch.usedGroups ctx.state) ctx.proof.val
      ⟨(NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length).1.parent,memory,[]⟩ result
      (run (program ctx choose memory) world).run.2 := by
  simp only [program] at executed ⊢
  cases sealed : (NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length).2 with
  | error reason => simp only [sealed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | ok value =>
    cases value
    simp only [sealed,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed ⊢
    cases executed
    have traced := loop_trace ctx.tables ctx.registry ctx.state ctx.fieldFuel choose ctx.workerFuel
      (NativeDeferredOpeningBatch.usedGroups ctx.state) ctx.proof.val
      ⟨(NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length).1.parent,memory,[]⟩ world
    exact ⟨trivial,by simpa only [List.append_nil] using traced⟩

theorem program_receipts {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification result) :
    ∀ receipt ∈ result.progress.receipts, Checked ctx.tables ctx.fieldFuel choose ctx.workerFuel world receipt ∧
      (run (NativeGoldBatchPcsProgram.program (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) choose ctx.workerFuel receipt.memory) world).run.2.Sublist
        (run (program ctx choose memory) world).run.2 := by
  intro receipt member
  rcases (program_trace ctx choose memory world result executed).2.receipts receipt member with impossible | checked
  · cases impossible
  · exact checked

theorem program_order {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (after : Progress Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification (.done after)) :
    after.receipts.map (fun receipt => (receipt.call.group,receipt.call.opening)) =
      ((NativeDeferredOpeningBatch.usedGroups ctx.state).map Fin.val).zip ctx.proof.val := by
  simpa only [List.map_nil,List.nil_append] using (program_trace ctx choose memory world (.done after) executed).2.done_packets after rfl

theorem program_counts {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (after : Progress Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification (.done after)) :
    after.receipts.length = ctx.proof.val.length ∧ after.receipts.length = (NativeDeferredOpeningBatch.usedGroups ctx.state).length := by
  have count := (NativeDeferredOpeningBatch.seal_spec ctx.state ctx.proof.val.length
    (program_trace ctx choose memory world (.done after) executed).1).1
  have ordered := congrArg List.length (program_order ctx choose memory world after executed)
  simp only [List.length_map,List.length_zip] at ordered
  rw [count,Nat.min_self] at ordered
  exact ⟨ordered.trans count.symm,ordered⟩

/-- All recorded raw workers and response groups replay in any enclosing truthful
history containing this actual execution, including the final whole-program cache. -/
theorem program_workers {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification result)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (program ctx choose memory) world).run.2.Sublist history) :
    ∀ receipt ∈ result.progress.receipts, ∀ job ∈ receipt.work.jobs, ∃ leaf siblings,
      NativeGoldColumnAuthentication.decodePath receipt.work.geometry.height job.column.path.val = some (leaf,siblings) ∧
      job.column.path.val = leaf :: siblings.toList ∧
      simulateQ (JointHashCache.project history).cache.toPartialImpl
        (NativeMerkleVerifier.verifyPayload NativeGoldColumnAuthentication.encoding receipt.work.geometry.height job.index
          job.column.values leaf receipt.work.root siblings) = some true ∧
      NativeGoldBatchColumnWorker.check receipt.work.geometry receipt.work.width receipt.work.random receipt.work.test
        job.column.values.val receipt.work.groups job.index = true ∧
      ∀ response ∈ receipt.work.groups, NativeGoldColumnChecks.check receipt.work.geometry receipt.work.width receipt.work.random
        response.1 receipt.work.test response.2 job.column.values.val job.index = true := by
  intro receipt member
  obtain ⟨checked,contained⟩ := program_receipts ctx choose memory world result executed receipt member
  intro job memberJob
  obtain ⟨leaf,siblings,decoded,path,authenticated,allGroups,eachGroup⟩ := NativeGoldBatchPcsProgram.accepted_workers
    (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) choose ctx.workerFuel receipt.memory world receipt.work receipt.completion
    checked.1 receipt.after checked.2 history truthful (contained.trans observed) job memberJob
  exact ⟨leaf,siblings,decoded,path,authenticated,allGroups,eachGroup⟩
end
end FormalProof4FHE.HasteBoots.NativeDeferredBatchVerification
