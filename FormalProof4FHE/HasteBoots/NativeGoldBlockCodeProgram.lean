module
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeLayout
public import FormalProof4FHE.HasteBoots.ConcreteNTTGoldCapturedAttempt
@[expose] public section

/-! Explicit BlockReedSolomonCode::new phases: preflight, discarded generated
Plan, cache init/recheck/capture/publication/retry, then actual table-root load.
Other concrete cache operations may interleave between phases. Rejected retry
proposals are retained as ghost receipts, not charged work. Rust/ArcSwap/Mutex,
allocation, scheduling and physical refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBlockCodeProgram
open NativeUsizeMessage (Usize)
open NativeGoldBlockCodeLayout (Layout preflight logSize store)
open ConcreteNTTGoldCacheRCU (Machine Snapshot)
open ConcreteNTTGoldTable (Table newTable)
open ConcreteNTTCacheLookup (lookup)

structure Request where
  message : Usize
  block : Usize
  blowup : Usize
  deriving DecidableEq

def rawRoot (root : ConcreteNTTLimbArithmetic.Limb) : NativeFieldRepresentation.GoldWord :=
  ⟨root.val,root.isLt⟩

structure Completed where
  layout : Layout
  loaded : Table
  code : NativeGoldBlockCode.Stored
  deriving DecidableEq

inductive Phase where
  | start
  | generating (layout : Layout)
  | initializing (layout : Layout)
  | capturing (layout : Layout)
  | publishing (layout : Layout) (snapshot : Snapshot)
  | loading (layout : Layout)
  | done (result : Completed)
  | error (error : NativeGoldBlockCode.Error)
  | assertionFailure
  | indexFailure
  deriving DecidableEq

structure Config where
  cache : Machine := {}
  phase : Phase := .start
  rejected : List (List (ℕ × Table)) := []
  deriving DecidableEq

def tick (request : Request) (config : Config) : Config :=
  match config.phase with
  | .start =>
    match preflight request.message request.block request.blowup with
    | .error error => {config with phase := .error error}
    | .ok layout => {config with phase := .generating layout}
  | .generating layout =>
    match newTable (logSize layout) with
    | .created _ => {config with phase := .initializing layout}
    | .tableError => {config with phase := .error .generation}
    | .assertionFailure => {config with phase := .assertionFailure}
    | .indexFailure => {config with phase := .indexFailure}
  | .initializing layout =>
    match lookup config.cache.current.tables (logSize layout) with
    | some _ => {config with phase := .loading layout}
    | none => {config with phase := .capturing layout}
  | .capturing layout =>
    {config with cache := ConcreteNTTGoldCacheRCU.capture config.cache, phase := .publishing layout (Snapshot.mk config.cache.version config.cache.current.tables)}
  | .publishing layout snapshot =>
    match ConcreteNTTGoldCapturedAttempt.run (logSize layout) config.cache snapshot with
    | .committed after => {config with cache := after,phase := .loading layout}
    | .retry proposal => {config with phase := .capturing layout,rejected := config.rejected++[proposal]}
    | .assertionFailure => {config with phase := .assertionFailure}
    | .indexFailure => {config with phase := .indexFailure}
  | .loading layout =>
    match lookup config.cache.current.tables (logSize layout) with
    | none => {config with phase := .initializing layout}
    | some table => {config with phase := .done ⟨layout,table,store layout (rawRoot table.root)⟩}
  | .done _ | .error _ | .assertionFailure | .indexFailure => config

def LayoutReady (request : Request) (layout : Layout) : Prop :=
  preflight request.message request.block request.blowup = .ok layout

def Generated (layout : Layout) : Prop := ∃ table, newTable (logSize layout) = .created table

def PhaseGood (request : Request) (cache : Machine) : Phase → Prop
  | .start | .error _ | .assertionFailure | .indexFailure => True
  | .generating layout => LayoutReady request layout
  | .initializing layout | .capturing layout | .loading layout => LayoutReady request layout ∧ Generated layout
  | .publishing layout snapshot => LayoutReady request layout ∧ Generated layout ∧ snapshot ∈ cache.snapshots.toList
  | .done result => LayoutReady request result.layout ∧ newTable (logSize result.layout) = .created result.loaded ∧
      lookup cache.current.tables (logSize result.layout) = some result.loaded ∧
      result.code = store result.layout (rawRoot result.loaded.root)

def Good (request : Request) (config : Config) : Prop :=
  ConcreteNTTGoldCacheRCU.Reachable config.cache ∧ PhaseGood request config.cache config.phase

theorem initial_good (request : Request) : Good request {} := ⟨.empty,True.intro⟩

theorem tick_good (request : Request) (config : Config) (good : Good request config) : Good request (tick request config) := by
  rcases config with ⟨cache,phase,rejected⟩
  rcases good with ⟨reachable,phaseGood⟩
  cases phase with
  | start =>
    dsimp only [tick]
    cases ready : preflight request.message request.block request.blowup with
    | error error => exact ⟨reachable,True.intro⟩
    | ok layout => exact ⟨reachable,ready⟩
  | generating layout =>
    dsimp only [tick]
    cases built : newTable (logSize layout) with
    | created table => exact ⟨reachable,phaseGood,table,built⟩
    | tableError => exact ⟨reachable,True.intro⟩
    | assertionFailure => exact ⟨reachable,True.intro⟩
    | indexFailure => exact ⟨reachable,True.intro⟩
  | initializing layout =>
    dsimp only [tick]
    cases found : lookup cache.current.tables (logSize layout) <;> exact ⟨reachable,phaseGood⟩
  | capturing layout =>
    exact ⟨.capture reachable,phaseGood.1,phaseGood.2,by simp [tick,ConcreteNTTGoldCacheRCU.capture]⟩
  | publishing layout snapshot =>
    obtain ⟨ticket,same⟩ := ConcreteNTTGoldCapturedAttempt.member_ticket cache snapshot phaseGood.2.2
    have runEq : ConcreteNTTGoldCapturedAttempt.run (logSize layout) cache snapshot =
        ConcreteNTTGoldCacheRCU.attempt (logSize layout) cache ticket := by
      rw [← same]
      exact ConcreteNTTGoldCapturedAttempt.ticket_eq _ _ _
    dsimp only [tick]
    cases executed : ConcreteNTTGoldCapturedAttempt.run (logSize layout) cache snapshot with
    | committed after => exact ⟨.commit (logSize layout) ticket reachable (runEq.symm.trans executed),phaseGood.1,phaseGood.2.1⟩
    | retry proposal => exact ⟨reachable,phaseGood.1,phaseGood.2.1⟩
    | assertionFailure => exact ⟨reachable,True.intro⟩
    | indexFailure => exact ⟨reachable,True.intro⟩
  | loading layout =>
    dsimp only [tick]
    cases found : lookup cache.current.tables (logSize layout) with
    | none => exact ⟨reachable,phaseGood⟩
    | some table => exact ⟨reachable,phaseGood.1,
        ConcreteNTTGoldCacheRCU.retained_table_origin cache reachable _ table found,found,rfl⟩
  | done result => exact ⟨reachable,phaseGood⟩
  | error error => exact ⟨reachable,phaseGood⟩
  | assertionFailure => exact ⟨reachable,phaseGood⟩
  | indexFailure => exact ⟨reachable,phaseGood⟩

theorem background_good (request : Request) (config : Config) (after : Machine) (good : Good request config)
    (move : ConcreteNTTGoldCapturedAttempt.Move config.cache after) : Good request {config with cache := after} := by
  refine ⟨ConcreteNTTGoldCapturedAttempt.move_reachable _ _ good.1 move,?_⟩
  have phaseGood := good.2
  cases phase : config.phase with
  | publishing layout snapshot =>
    rw [phase] at phaseGood
    exact ⟨phaseGood.1,phaseGood.2.1,ConcreteNTTGoldCapturedAttempt.move_snapshot_member _ _ move snapshot phaseGood.2.2⟩
  | done result =>
    rw [phase] at phaseGood
    exact ⟨phaseGood.1,phaseGood.2.1,
      ConcreteNTTGoldCapturedAttempt.move_table_read _ _ good.1 move _ _ phaseGood.2.2.1,phaseGood.2.2.2⟩
  | start => trivial
  | error error => trivial
  | assertionFailure => trivial
  | indexFailure => trivial
  | _ => simpa only [phase,PhaseGood] using phaseGood

inductive Reachable (request : Request) : Config → Prop where
  | initial : Reachable request {}
  | tick {config : Config} (prior : Reachable request config) : Reachable request (tick request config)
  | background {config : Config} (after : Machine) (prior : Reachable request config)
      (move : ConcreteNTTGoldCapturedAttempt.Move config.cache after) : Reachable request {config with cache := after}

theorem reachable_good (request : Request) (config : Config) (reachable : Reachable request config) : Good request config := by
  induction reachable with
  | initial => exact initial_good request
  | tick prior ih => exact tick_good request _ ih
  | background after prior move ih => exact background_good request _ after ih move

theorem completed_origin (request : Request) (config : Config) (reachable : Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    ConcreteNTTGoldCacheRCU.Reachable config.cache ∧ LayoutReady request result.layout ∧
      newTable (logSize result.layout) = .created result.loaded ∧
      lookup config.cache.current.tables (logSize result.layout) = some result.loaded ∧
      result.code = store result.layout (rawRoot result.loaded.root) := by
  have good := reachable_good request config reachable
  exact ⟨good.1,by simpa only [finished,PhaseGood] using good.2⟩

end FormalProof4FHE.HasteBoots.NativeGoldBlockCodeProgram
