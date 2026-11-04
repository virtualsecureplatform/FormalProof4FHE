module

public import FormalProof4FHE.HasteBoots.JointHashKernel
public import FormalProof4FHE.HasteBoots.OraclePrefixTrace
public import FormalProof4FHE.HasteBoots.OracleHistoryDrift

@[expose] public section

/-!
# Collision drift along actual mixed-oracle prefixes

Only a fresh SHA-512 input incurs the birthday charge. SHAKE starts and
reads, repeated hashes, and completed executions incur no new charge.
Conditioning retains the complete mixed history and inherited collisions.
-/

namespace FormalProof4FHE.HasteBoots.JointHashPrefix

open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open InputIndexedOracle (World law Input sha512)
open NativeTranscript (Execution Observation)
open OracleProgram (Program runPrefix)
open JointHashCache (State project record)

noncomputable section

abbrev History (A : Type) := (Program A ⊕ A) × List Observation

def nextState {A : Type} (history : History A) (world : World) : State :=
  project (history.2 ++ (OraclePrefixTrace.advance history.1 world).run.2)

def loss {A : Type} (history : History A) : ENNReal :=
  match history.1 with
  | .inl (.hash input _) =>
      if (project history.2).cache input = none then
        ((project history.2).keys.card : ENNReal) / (2 : ENNReal) ^ 512 else 0
  | _ => 0

def risk {A : Type} (history : History A) : ENNReal := by
  classical
  exact if CacheHasCollision (project history.2).cache then 1 else 0

theorem nextState_done {A : Type} (value : A) (log : List Observation) (world : World) :
    nextState (.inr value, log) world = project log := by
  change project (log ++ []) = _
  rw [List.append_nil]

theorem nextState_pure {A : Type} (value : A) (log : List Observation) (world : World) :
    nextState (.inl (.pure value), log) world = project log := by
  change project (log ++ []) = _
  rw [List.append_nil]

theorem zero_log {A : Type} (program : Program A) (world : World) :
    (runPrefix 0 program world).run.2 = [] := by
  cases program <;> rfl

theorem nextState_start {A : Type} (input : Input) (next : Program A)
    (log : List Observation) (world : World) :
    nextState (.inl (.start input next), log) world = project log := by
  change project (log ++ ([.start input] ++ (runPrefix 0 next world).run.2)) = _
  rw [zero_log, List.append_nil, JointHashCache.project_append]
  rfl

theorem nextState_read {A : Type} (input : Input) (offset count : ℕ) (next : Input → Program A)
    (log : List Observation) (world : World) :
    nextState (.inl (.read input offset count next), log) world = project log := by
  change project (log ++ ([.output input offset (InputIndexedOracle.bytes world input offset count)] ++
    (runPrefix 0 (next (InputIndexedOracle.bytes world input offset count)) world).run.2)) = _
  rw [zero_log, List.append_nil, JointHashCache.project_append]
  rfl

theorem nextState_hash {A : Type} (input : Input) (next : JointHashCache.Digest → Program A)
    (log : List Observation) (world : World) :
    nextState (.inl (.hash input next), log) world =
      record (project log) (.hash input (List.ofFn (sha512 world input))) := by
  change project (log ++ ([.hash input (List.ofFn (sha512 world input))] ++
    (runPrefix 0 (next (sha512 world input)) world).run.2)) = _
  rw [zero_log, List.append_nil, JointHashCache.project_append]

/-- The actual next hash cache agrees with the longer prefix, including
all preceding SHAKE and hash observations. -/
theorem nextState_prefix {A : Type} (depth : ℕ) (program : Program A) (world : World) :
    nextState (runPrefix depth program world).run world =
      project (runPrefix (depth + 1) program world).run.2 := by
  rw [OraclePrefixTrace.runPrefix_succ_run]
  rfl

/-- Conditioned histories containing a collision keep risk one. Good
histories incur only the next fresh hash charge. -/
theorem conditional_step {A : Type} {past : World → Execution (Program A ⊕ A)}
    (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}])
      {other | CacheHasCollision (nextState (past other).run other).cache} ≤
        risk (past world).run + loss (past world).run := by
  classical
  have positive : law {other | (past other).run = (past world).run} ≠ 0 := by
    rw [ObservationReplay.fiber_eq_assignment replay world]
    exact OraclePosterior.assignment_ne_zero _ _
  let := cond_isProbabilityMeasure (μ := law) positive
  have fixed : (law[|{other | (past other).run = (past world).run}])
      {other | CacheHasCollision (nextState (past other).run other).cache} =
      (law[|{other | (past other).run = (past world).run}])
        {other | CacheHasCollision (nextState (past world).run other).cache} := by
    apply measure_congr
    filter_upwards [ae_cond_mem (μ := law) (ObservationReplay.fiber_measurable replay world)] with other same
    change (past other).run = (past world).run at same
    rw [same]
  rw [fixed]
  by_cases bad : CacheHasCollision (project (past world).run.2).cache
  · simp only [risk, bad, ite_true]
    exact (measure_le_one _ _).trans (le_add_right le_rfl)
  · have zero : risk (past world).run = 0 := by simp only [risk, bad, ite_false]
    rw [zero, zero_add]
    cases historyEq : (past world).run with
    | mk result log =>
      rw [historyEq] at bad
      cases result with
      | inr value => simp only [nextState_done, bad, Set.ofPred_false, measure_empty, loss, le_refl]
      | inl program =>
        cases program with
        | pure value => simp only [nextState_pure, bad, Set.ofPred_false, measure_empty, loss, le_refl]
        | start input next => simp only [nextState_start, bad, Set.ofPred_false, measure_empty, loss, le_refl]
        | read input offset count next => simp only [nextState_read, bad, Set.ofPred_false, measure_empty, loss, le_refl]
        | hash input next =>
          simp only [nextState_hash, loss]
          have bound := JointHashKernel.collision_step replay world input (by simpa only [historyEq] using bad)
          simpa only [historyEq] using bound

/-- No safe-history premise remains in the unconditional drift: earlier
collision probability is preserved as the inherited-risk integral. -/
theorem prefix_drift {A : Type} (depth : ℕ) (program : Program A) :
    law {world | CacheHasCollision (project (runPrefix (depth + 1) program world).run.2).cache} ≤
      (∫⁻ world, risk (runPrefix depth program world).run ∂law) +
        ∫⁻ world, loss (runPrefix depth program world).run ∂law := by
  have bound := OracleHistoryDrift.additive_drift (OracleProgram.prefix_replay depth program)
    {world | CacheHasCollision (nextState (runPrefix depth program world).run world).cache}
    ?_ risk loss (conditional_step (OracleProgram.prefix_replay depth program))
  · simpa only [nextState_prefix] using bound
  · simp only [nextState_prefix]
    exact OracleExecutionLaw.event_measurable (OracleProgram.prefix_replay (depth + 1) program)
      (fun history => CacheHasCollision (project history.2).cache)

/-- The inherited risk integral is exactly the earlier collision
probability, including histories with conditional risk one. -/
theorem risk_mean {A : Type} {past : World → Execution (Program A ⊕ A)}
    (replay : ObservationReplay.Replayable past) :
    (∫⁻ world, risk (past world).run ∂law) =
      law {world | CacheHasCollision (project (past world).run.2).cache} := by
  classical
  change (∫⁻ world, {world | CacheHasCollision (project (past world).run.2).cache}.indicator
    (fun _ => (1 : ENNReal)) world ∂law) = _
  rw [lintegral_indicator_const
    (OracleExecutionLaw.event_measurable replay (fun history => CacheHasCollision (project history.2).cache)),
    one_mul]

/-- Birthday hazards telescope over every actual mixed prefix. Earlier
SHAKE reads and repeated hash entries stay in the conditioning history. -/
theorem prefix_bound {A : Type} (depth : ℕ) (program : Program A) :
    law {world | CacheHasCollision (project (runPrefix depth program world).run.2).cache} ≤
      ∑ time ∈ Finset.range depth, ∫⁻ world, loss (runPrefix time program world).run ∂law := by
  induction depth with
  | zero =>
    have empty : {world | CacheHasCollision (project (runPrefix 0 program world).run.2).cache} = ∅ := by
      ext world
      simp only [zero_log, JointHashCache.project, List.foldl_nil,
        CachedHashCollision.no_collision_empty, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [empty, measure_empty, Finset.range_zero, Finset.sum_empty]
  | succ depth ih =>
    have drift := prefix_drift depth program
    rw [risk_mean (OracleProgram.prefix_replay depth program)] at drift
    rw [Finset.sum_range_succ]
    exact drift.trans (add_le_add ih le_rfl)

/-- Sum of pre-answer charges on the same chronological execution. This
is a probability loss ledger, not an identification with machine work. -/
def charge {A : Type} (depth : ℕ) (program : Program A) (world : World) : ENNReal :=
  ∑ time ∈ Finset.range depth, loss (runPrefix time program world).run

theorem charge_mean {A : Type} (depth : ℕ) (program : Program A) :
    (∫⁻ world, charge depth program world ∂law) =
      ∑ time ∈ Finset.range depth, ∫⁻ world, loss (runPrefix time program world).run ∂law := by
  exact lintegral_finsetSum _ (fun time _ =>
    OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay time program) loss)

theorem prefix_bound_charge {A : Type} (depth : ℕ) (program : Program A) :
    law {world | CacheHasCollision (project (runPrefix depth program world).run.2).cache} ≤
      ∫⁻ world, charge depth program world ∂law := by
  rw [charge_mean]
  exact prefix_bound depth program

/-- Truthful updates extend the cache even when prior entries collide. -/
theorem record_cache_mono (world : World) (state : State) (entry : Observation)
    (agrees : JointHashCache.AgreesWorld world state)
    (truthful : ObservationReplay.Matches world entry) :
    state.cache ≤ (record state entry).cache := by
  cases entry with
  | start => exact le_rfl
  | output => exact le_rfl
  | hash input digest =>
    change List.ofFn (sha512 world input) = digest at truthful
    subst digest
    simp only [record, JointHashCache.decode_ofFn, CachedHashHandler.observe]
    cases known : state.cache input with
    | none => exact state.cache.le_cacheQuery known
    | some answer =>
      have same := agrees input answer known
      subst answer
      rw [JointHashCache.cacheQuery_known state input _ known]

theorem nextState_cache_mono {A : Type} (history : History A) (world : World)
    (truthful : ObservationReplay.Agrees world history.2) :
    (project history.2).cache ≤ (nextState history world).cache := by
  rcases history with ⟨result, log⟩
  cases result with
  | inr value => rw [nextState_done]
  | inl program =>
    cases program with
    | pure value => rw [nextState_pure]
    | start input next => rw [nextState_start]
    | read input offset count next => rw [nextState_read]
    | hash input next =>
      rw [nextState_hash]
      exact record_cache_mono world (project log) _
        (JointHashCache.project_valid world log truthful).2 rfl

/-- Once revealed, a collision persists after arbitrary later reads,
repeated hashes, completion and rejection encoded in the continuation. -/
theorem collision_prefix_mono {A : Type} (program : Program A) :
    Monotone (fun depth => {world | CacheHasCollision (project (runPrefix depth program world).run.2).cache}) := by
  apply monotone_nat_of_le_succ
  intro depth world collided
  apply CachedHashCollision.collision_mono _ _ ?_ collided
  rw [← nextState_prefix]
  exact nextState_cache_mono _ world ((OracleProgram.prefix_replay depth program).truthful world)

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ⨆ depth, charge depth program world

theorem charge_measurable {A : Type} (depth : ℕ) (program : Program A) :
    Measurable (charge depth program) := by
  apply Finset.measurable_sum
  intro time _
  exact OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay time program) loss

theorem charge_mono {A : Type} (program : Program A) (world : World) :
    Monotone (fun depth => charge depth program world) := by
  intro first last ordered
  exact Finset.sum_le_sum_of_subset (Finset.range_mono ordered)

/-- The total ledger has exactly the supremum of prefix expectations;
no finite-mean assumption discards long or infinite cost tails. -/
theorem totalCharge_mean {A : Type} (program : Program A) :
    (∫⁻ world, totalCharge program world ∂law) =
      ⨆ depth, ∫⁻ world, charge depth program world ∂law := by
  apply lintegral_iSup (fun depth => charge_measurable depth program)
  intro first last ordered world
  exact charge_mono program world ordered

/-- Unrestricted observation-prefix collision bound. The same pathwise
ledger dominates all prefixes; infinite ledgers and expectations remain
allowed. Coupling an unbounded native sampler to compatible prefixes is
still a separate compiler/refinement obligation. -/
theorem ever_collision_bound {A : Type} (program : Program A) :
    law {world | ∃ depth, CacheHasCollision (project (runPrefix depth program world).run.2).cache} ≤
      ∫⁻ world, totalCharge program world ∂law := by
  have equal : {world | ∃ depth, CacheHasCollision (project (runPrefix depth program world).run.2).cache} =
      ⋃ depth, {world | CacheHasCollision (project (runPrefix depth program world).run.2).cache} := by
    ext world
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [equal, (collision_prefix_mono program).measure_iUnion]
  apply iSup_le
  intro depth
  apply (prefix_bound_charge depth program).trans
  apply lintegral_mono
  intro world
  exact le_iSup (fun n => charge n program world) depth

/-- The same ledger bounds the terminal collision event of the complete
mixed program, without conditioning on its returned success value. -/
theorem terminal_collision_bound {A : Type} (program : Program A) :
    law {world | CacheHasCollision (project (OracleProgram.run program world).run.2).cache} ≤
      ∫⁻ world, totalCharge program world ∂law := by
  apply (measure_mono ?_).trans (ever_collision_bound program)
  intro world collided
  obtain ⟨depth, same⟩ := OraclePrefixTrace.eventual_completion program world
  refine ⟨depth, ?_⟩
  rw [same]
  exact collided

end

end FormalProof4FHE.HasteBoots.JointHashPrefix
