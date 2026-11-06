module
public import FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
public import FormalProof4FHE.HasteBoots.NativeSharedLookupHelpers
/-! Ordered native helper verification in the shared causal oracle program.

Completion here covers helper openings; source registry verification and application
acceptance remain separate obligations. Analysis fuel preserves suspended outcomes. -/

@[expose] public section

namespace FormalProof4FHE.HasteBoots.NativeGoldHelperVerification
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation)
open NativeGoldBlockCode (Tables Stored)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsOpening (Opening)
open NativeSharedLookupHelpers (Call Plan)
open NativeGoldPcsProgram (Scheduler)
open OracleProgram (Program bind run)
open OracleSpec OracleComp
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def context (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ) (parent : Transcript) (call : Call Opening) :
    NativeGoldPcsExecution.Context := ⟨tables,parameters,parent,call.root,call.query,call.values,call.opening,fieldFuel⟩

structure Receipt (Memory : Type) where
  call : Call Opening
  before : Transcript
  memory : Memory
  work : NativeGoldPcsWorkers.Prepared
  completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length
  after : Transcript

structure Progress (Memory : Type) where
  lastAccepted : Transcript
  memory : Memory
  receipts : List (Receipt Memory)

inductive Result (Memory : Type) where
  | done (progress : Progress Memory)
  | stopped (before : Progress Memory) (call : Call Opening) (outcome : NativeGoldPcsProgram.Outcome Memory)

def Result.progress {Memory : Type} : Result Memory → Progress Memory
  | .done progress => progress
  | .stopped before _ _ => before

/-- Only the computed PCS accepted status advances to the next helper. -/
def advance {Memory : Type} (before : Progress Memory) (call : Call Opening) : NativeGoldPcsProgram.Outcome Memory → Option (Progress Memory)
  | .prefix _ => none
  | .completed work completion => match completion.status with
    | .accepted next => some ⟨next,completion.pool.memory,before.receipts++[⟨call,before.lastAccepted,before.memory,work,completion,next⟩]⟩
    | _ => none

theorem advance_spec {Memory : Type} (before : Progress Memory) (call : Call Opening)
    (outcome : NativeGoldPcsProgram.Outcome Memory) (after : Progress Memory) (advanced : advance before call outcome = some after) :
    ∃ work completion next, outcome = .completed work completion ∧ completion.status = .accepted next ∧
      after = ⟨next,completion.pool.memory,before.receipts++[⟨call,before.lastAccepted,before.memory,work,completion,next⟩]⟩ := by
  cases outcome with
  | «prefix» previous => contradiction
  | completed work completion =>
    cases status : completion.status with
    | accepted next =>
      simp only [advance,status] at advanced
      exact ⟨work,completion,next,rfl,status,(Option.some.inj advanced).symm⟩
    | columns => simp only [advance,status] at advanced; contradiction
    | claim reason => simp only [advance,status] at advanced; contradiction
    | suspended => simp only [advance,status] at advanced; contradiction

def loop {Memory : Type} (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) : List (Call Opening) → Progress Memory → Program (Result Memory)
  | [],before => .pure (.done before)
  | call::rest,before => bind (NativeGoldPcsProgram.program (context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory)
    (fun outcome => match advance before call outcome with
      | none => .pure (.stopped before call outcome)
      | some after => loop tables parameters fieldFuel choose workerFuel rest after)

/-- Actual segment equations, rather than supplied acceptance/worker certificates. -/
inductive Trace {Memory : Type} (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) (world : World) :
    List (Call Opening) → Progress Memory → Result Memory → List Observation → Prop
  | done (before : Progress Memory) : Trace tables parameters fieldFuel choose workerFuel world [] before (.done before) []
  | stopped (before : Progress Memory) (call : Call Opening) (rest : List (Call Opening)) (outcome : NativeGoldPcsProgram.Outcome Memory)
      (log : List Observation)
      (executed : (run (NativeGoldPcsProgram.program (context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory) world).run = (outcome,log))
      (stopped : advance before call outcome = none) :
      Trace tables parameters fieldFuel choose workerFuel world (call::rest) before (.stopped before call outcome) log
  | passed (before after : Progress Memory) (call : Call Opening) (rest : List (Call Opening)) (outcome : NativeGoldPcsProgram.Outcome Memory)
      (log : List Observation) (result : Result Memory) (later : List Observation)
      (executed : (run (NativeGoldPcsProgram.program (context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory) world).run = (outcome,log))
      (advanced : advance before call outcome = some after)
      (tail : Trace tables parameters fieldFuel choose workerFuel world rest after result later) :
      Trace tables parameters fieldFuel choose workerFuel world (call::rest) before result (log++later)

theorem loop_trace {Memory : Type} (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) (calls : List (Call Opening)) (before : Progress Memory) (world : World) :
    Trace tables parameters fieldFuel choose workerFuel world calls before
      (run (loop tables parameters fieldFuel choose workerFuel calls before) world).run.1
      (run (loop tables parameters fieldFuel choose workerFuel calls before) world).run.2 := by
  induction calls generalizing before with
  | nil => exact .done before
  | cons call rest ih =>
    let current := (run (NativeGoldPcsProgram.program (context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory) world).run
    have currentEq : (run (NativeGoldPcsProgram.program (context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory) world).run = (current.1,current.2) := rfl
    cases advanced : advance before call
        (run (NativeGoldPcsProgram.program (context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory) world).run.1 with
    | none =>
      simpa only [current,loop,OracleProgram.run_bind,ObservationReplay.run_bind,advanced,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil] using
        Trace.stopped before call rest current.1 current.2 currentEq advanced
    | some after =>
      simpa only [current,loop,OracleProgram.run_bind,ObservationReplay.run_bind,advanced] using
        Trace.passed before after call rest current.1 current.2 _ _ currentEq advanced (ih after)

/-- Every passed helper is recorded in its original position; a stop identifies the first unpassed call. -/
theorem Trace.order {Memory : Type} {tables : Tables} {parameters : Parameters Stored} {fieldFuel : ℕ}
    {choose : Scheduler Memory} {workerFuel : ℕ} {world : World} {calls : List (Call Opening)} {before : Progress Memory}
    {result : Result Memory} {log : List Observation} (trace : Trace tables parameters fieldFuel choose workerFuel world calls before result log) :
    match result with
    | .done after => after.receipts.map Receipt.call = before.receipts.map Receipt.call ++ calls
    | .stopped after call _ => ∃ passed rest, calls = passed++call::rest ∧
        after.receipts.map Receipt.call = before.receipts.map Receipt.call ++ passed := by
  induction trace with
  | done before => simp
  | stopped before call rest outcome log executed stopped => exact ⟨[],rest,rfl,by simp⟩
  | passed before after call rest outcome log result later executed advanced tail ih =>
    obtain ⟨work,completion,next,_,_,same⟩ := advance_spec before call outcome after advanced
    have recorded : after.receipts.map Receipt.call = before.receipts.map Receipt.call ++ [call] := by rw [same]; simp
    cases result with
    | done final =>
      dsimp only at ih ⊢
      rw [ih,recorded,List.append_assoc]
      rfl
    | stopped final failed failure =>
      dsimp only at ih ⊢
      obtain ⟨passed,remaining,calls,receipts⟩ := ih
      refine ⟨call::passed,remaining,by simp [calls],?_⟩
      rw [receipts,recorded,List.append_assoc]
      rfl

def Checked {Memory : Type} (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ)
    (choose : Scheduler Memory) (workerFuel : ℕ) (world : World) (receipt : Receipt Memory) : Prop :=
  (run (NativeGoldPcsProgram.program (context tables parameters fieldFuel receipt.before receipt.call) choose workerFuel receipt.memory) world).run.1 =
      .completed receipt.work receipt.completion ∧ receipt.completion.status = .accepted receipt.after

theorem Trace.receipts {Memory : Type} {tables : Tables} {parameters : Parameters Stored} {fieldFuel : ℕ}
    {choose : Scheduler Memory} {workerFuel : ℕ} {world : World} {calls : List (Call Opening)} {before : Progress Memory}
    {result : Result Memory} {log : List Observation} (trace : Trace tables parameters fieldFuel choose workerFuel world calls before result log) :
    ∀ receipt ∈ result.progress.receipts, receipt ∈ before.receipts ∨
      Checked tables parameters fieldFuel choose workerFuel world receipt ∧
      (run (NativeGoldPcsProgram.program (context tables parameters fieldFuel receipt.before receipt.call) choose workerFuel receipt.memory) world).run.2.Sublist log := by
  induction trace with
  | done before => intro receipt member; exact Or.inl member
  | stopped before call rest outcome log executed stopped => intro receipt member; exact Or.inl member
  | passed before after call rest outcome log result later executed advanced tail ih =>
    obtain ⟨work,completion,next,outcomeEq,accepted,same⟩ := advance_spec before call outcome after advanced
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


structure Context (B : Type) where
  tables : Tables
  registry : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle Stored)
  helper : Parameters Stored
  parent : Transcript
  requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request
  proof : NativeSharedLookupProofData.Proof Opening B
  lookupFuel : ℕ
  equalityFuel : ℕ
  scalarFuel : ℕ
  fieldFuel : ℕ
  workerFuel : ℕ

def Context.native {B : Type} (ctx : Context B) := NativeSharedLookupHelpers.protocol NativeGoldBlockCode.description.row
  ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel

inductive Outcome (Memory : Type) where
  | prior (packet : Option NativeSharedLookupBody.Outcome × Option (Plan Opening))
  | helpers (result : NativeSharedLookupBody.Bound) (plan : Plan Opening) (status : Result Memory)

/-- The actual completed lookup/child body computes every helper call before this native ordered loop. -/
def program {B Memory : Type} (ctx : Context B) (choose : Scheduler Memory) (memory : Memory) : Program (Outcome Memory) :=
  bind ctx.native (fun packet => match packet.1,packet.2 with
    | some (.bound result),some plan =>
      bind (loop ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨result.parent,memory,[]⟩)
        (fun status => .pure (.helpers result plan status))
    | _,_ => .pure (.prior packet))

structure Origin {B Memory : Type} (ctx : Context B) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : NativeSharedLookupBody.Bound) (plan : Plan Opening) (status : Result Memory) : Prop where
  native : (run ctx.native world).run.1 = (some (.bound result),some plan)
  helpers : (run (loop ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨result.parent,memory,[]⟩) world).run.1 = status
  log : (run (program ctx choose memory) world).run.2 = (run ctx.native world).run.2 ++
    (run (loop ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨result.parent,memory,[]⟩) world).run.2
  spec : NativeSharedLookupHelpers.Spec ctx.helper.width result.terminal.point ctx.proof plan
  count : plan.calls.length = ctx.proof.roots.val.length

theorem helpers_origin {B Memory : Type} (ctx : Context B) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : NativeSharedLookupBody.Bound) (plan : Plan Opening) (status : Result Memory)
    (executed : (run (program ctx choose memory) world).run.1 = .helpers result plan status) :
    Origin ctx choose memory world result plan status := by
  simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind] at executed
  cases packet : (run ctx.native world).run.1 with
  | mk native candidate =>
    cases native with
    | none => simp only [packet,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | some previous =>
      cases previous with
      | suspended machine => simp only [packet,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
      | rejected reason machine => simp only [packet,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
      | bound original =>
        cases candidate with
        | none => simp only [packet,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
        | some handoff =>
          simp only [packet,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed
          cases executed
          have nativeValue := packet
          simp only [Context.native,NativeSharedLookupHelpers.run_protocol] at nativeValue
          have upstream := congrArg Prod.fst nativeValue
          have planned := congrArg Prod.snd nativeValue
          dsimp only at upstream planned
          have built : NativeSharedLookupHelpers.build ctx.helper.width result.terminal.point ctx.proof = some plan := by
            simpa only [upstream,NativeSharedLookupHelpers.handoff] using planned
          have geometry := NativeSharedLookupHelpers.completed_geometry NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
            ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world result upstream
          refine ⟨packet,rfl,?_,NativeSharedLookupHelpers.build_spec _ _ _ _ built,
            NativeSharedLookupHelpers.no_truncation _ _ _ _ built geometry.2.2.2.1 geometry.2.2.2.2⟩
          simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind,packet,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem helpers_order {B Memory : Type} (ctx : Context B) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : NativeSharedLookupBody.Bound) (plan : Plan Opening) (after : Progress Memory)
    (executed : (run (program ctx choose memory) world).run.1 = .helpers result plan (.done after)) :
    after.receipts.map Receipt.call = plan.calls ∧ after.receipts.length = ctx.proof.roots.val.length := by
  have origin := helpers_origin ctx choose memory world result plan (.done after) executed
  have trace := loop_trace ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨result.parent,memory,[]⟩ world
  rw [origin.helpers] at trace
  have ordered := trace.order
  dsimp only at ordered
  simp only [List.map_nil,List.nil_append] at ordered
  refine ⟨ordered,?_⟩
  have length := congrArg List.length ordered
  simpa only [List.length_map,origin.count] using length

theorem helpers_receipts {B Memory : Type} (ctx : Context B) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : NativeSharedLookupBody.Bound) (plan : Plan Opening) (status : Result Memory)
    (executed : (run (program ctx choose memory) world).run.1 = .helpers result plan status) :
    ∀ receipt ∈ status.progress.receipts, Checked ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel world receipt ∧
      (run (NativeGoldPcsProgram.program (context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) choose ctx.workerFuel receipt.memory) world).run.2.Sublist
        (run (program ctx choose memory) world).run.2 := by
  have origin := helpers_origin ctx choose memory world result plan status executed
  have trace := loop_trace ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨result.parent,memory,[]⟩ world
  rw [origin.helpers] at trace
  intro receipt member
  rcases trace.receipts receipt member with impossible | ⟨checked,observed⟩
  · cases impossible
  · refine ⟨checked,observed.trans ?_⟩
    rw [origin.log]
    exact List.sublist_append_right _ _


/-- Every recorded helper authenticates its raw columns against the final cache of the entire native helper pipeline. -/
theorem helpers_workers {B Memory : Type} (ctx : Context B) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : NativeSharedLookupBody.Bound) (plan : Plan Opening) (status : Result Memory)
    (executed : (run (program ctx choose memory) world).run.1 = .helpers result plan status) :
    ∀ receipt ∈ status.progress.receipts, receipt.work.root = receipt.call.root ∧
      ∀ job ∈ receipt.work.jobs, ∃ leaf siblings,
        NativeGoldColumnAuthentication.decodePath receipt.work.geometry.height job.column.path.val = some (leaf,siblings) ∧
        job.column.path.val = leaf :: siblings.toList ∧
        simulateQ (JointHashCache.project (run (program ctx choose memory) world).run.2).cache.toPartialImpl
          (NativeMerkleVerifier.verifyPayload NativeGoldColumnAuthentication.encoding receipt.work.geometry.height job.index
            job.column.values leaf receipt.call.root siblings) = some true ∧
        NativeGoldColumnChecks.check receipt.work.geometry receipt.work.width receipt.work.random receipt.work.structured
          receipt.work.test receipt.work.evaluation job.column.values.val job.index = true := by
  intro receipt member
  obtain ⟨checked,observed⟩ := helpers_receipts ctx choose memory world result plan status executed receipt member
  have original := NativeGoldPcsProgram.completed_origin (context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call)
    choose ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1
  have root := (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.helper receipt.before receipt.call.root
    receipt.call.query receipt.call.values receipt.call.opening ctx.fieldFuel world receipt.work original.prepared).2.2
  refine ⟨root,?_⟩
  have workers := NativeGoldPcsProgram.accepted_workers (context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call)
    choose ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1 receipt.after checked.2
    (run (program ctx choose memory) world).run.2 ((OracleProgram.run_replay _).truthful world) observed
  simpa only [root] using workers

end
end FormalProof4FHE.HasteBoots.NativeGoldHelperVerification

