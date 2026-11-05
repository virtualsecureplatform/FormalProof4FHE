module

public import FormalProof4FHE.HasteBoots.NativeShakeCache

@[expose] public section

/-! The one-byte SHAKE kernel under the complete mixed-oracle history.
Its cache is derived from the finite observed coordinate set. Fresh bytes
use the actual private uniform query; cached bytes reuse the old value.
The shared execution proof preserves the entire hash/checkpoint state.
Whole-program probability transport remains a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.NativeShakeKernel
open InputIndexedOracle (Byte Coordinate Input World law)
open NativeShakeCache (Cache Key)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp

noncomputable section

/-- Finite observed SHAKE coordinates, with no reader identity or full-reader conditioning. -/
def observed (log : List Observation) (world : World) : Cache := fun key =>
  if (.inl key : Coordinate) ∈ ObservationReplay.footprint log then some (world (.inl key)) else none

/-- The physical cached-or-uniform byte answer law. -/
def answer (cache : Cache) (key : Key) : ProbComp Byte :=
  match cache key with
  | some value => pure value
  | none => liftM (unifSpec.query 255)

/-- The full mixed past induces precisely the physical cached-or-uniform byte law. -/
theorem reply_law {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (key : Key) :
    (law[|{other | (past other).run = (past world).run}]).map (fun other => other (.inl key)) =
      𝒟[answer (observed (past world).run.2 world) key] := by
  rw [OraclePosterior.execution_posterior replay world,
    Measure.map_map (measurable_pi_apply (.inl key)) (OraclePosterior.override_measurable _ _)]
  by_cases known : (.inl key : Coordinate) ∈ ObservationReplay.footprint (past world).run.2
  · have constant : (fun other => other (.inl key)) ∘
        OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world =
        fun _ : World => world (.inl key) := by
      funext fresh
      exact OraclePosterior.override_seen _ _ _ _ known
    rw [constant]
    simp only [answer,observed,known,ite_true,evalDist_pure,Measure.map_const,measure_univ,one_smul]
  · have unchanged : (fun other => other (.inl key)) ∘
        OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world =
        fun fresh : World => fresh (.inl key) := by
      funext fresh
      exact OraclePosterior.override_unseen _ _ _ _ known
    rw [unchanged]
    simp only [answer,observed,known,ite_false,evalDist_liftM_unifSpec_query]
    exact Measure.infinitePi_map_eval (fun _ : Coordinate => InputIndexedOracle.byteLaw) (.inl key)

/-- Cache ownership stays with the interpreter on both hits and misses. -/
def install (cache : Cache) (key : Key) (value : Byte) : Cache :=
  match cache key with
  | some _ => cache
  | none => Function.update cache key (some value)

/-- The answer paired with its actual updated byte cache. -/
def step (cache : Cache) (key : Key) : ProbComp (Byte × Cache) :=
  (fun value => (value,install cache key value)) <$> answer cache key

/-- One actual compiled byte step preserves every shared SHA-512 and checkpoint field. -/
theorem shared_step {Cfg Payload : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (cache : Cache) (key : Key) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      ((NativeShakeCache.byte (Cfg := Cfg) key).run cache)).run state =
      (fun result => (result,state)) <$> step cache key := by
  cases known : cache key with
  | some value =>
    rw [NativeShakeCache.byte_cached cache key value known]
    simp only [simulateQ_pure,StateT.run_pure,step,answer,install,known,map_pure]
  | none =>
    rw [NativeShakeCache.byte_fresh cache key known,simulateQ_map,simulateQ_spec_query,StateT.run_map]
    change (fun result => ((result.1,Function.update cache key (some result.1)),result.2)) <$>
      ((fun value => (value,state)) <$> (liftM (unifSpec.query 255) : ProbComp Byte)) = _
    simp only [step,answer,install,known,Functor.map_map]


/-- Exact event transport for arbitrary byte predicates. -/
theorem reply_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (key : Key) (event : Byte → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | event (other (.inl key))} =
      Pr{let value ← answer (observed (past world).run.2 world) key}[event value] := by
  rw [prEvent_eq_evalDist_of_discrete,← reply_law replay world key]
  exact (Measure.map_apply (measurable_pi_apply ((.inl key) : Coordinate)) MeasurableSet.of_discrete).symm

/-- Exact event transport includes the owned cache transition. -/
theorem step_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (key : Key)
    (event : Byte × Cache → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (other (.inl key),install (observed (past world).run.2 world) key (other (.inl key)))} =
      Pr{let result ← step (observed (past world).run.2 world) key}[event result] := by
  rw [reply_event replay world key (fun value =>
    event (value,install (observed (past world).run.2 world) key value))]
  simp only [step,prEvent_map]


/-- Appending the next observed byte produces exactly the interpreter cache transition. -/
theorem observed_append_byte (log : List Observation) (world : World) (key : Key) :
    observed (log++[.output key.1 key.2 [world (.inl key)]]) world =
      install (observed log world) key (world (.inl key)) := by
  classical
  have footprint : ObservationReplay.footprint (log++[.output key.1 key.2 [world (.inl key)]]) =
      ObservationReplay.footprint log ∪ {(.inl key : Coordinate)} := by
    simp [ObservationReplay.footprint,ObservationReplay.coordinates,List.toFinset_append]
  funext other
  by_cases known : (.inl key : Coordinate) ∈ ObservationReplay.footprint log
  · simp [observed,install,footprint,known]
  · by_cases same : other = key
    · subst other
      simp [observed,install,footprint,known]
    · simp [observed,install,footprint,known,same]


/-- Installing the masked answer is exactly a write of that answer, on hits
as well as misses. No cached byte is overwritten by a different value. -/
theorem install_masked (cache : Cache) (key : Key) (raw : Byte) :
    install cache key ((cache key).getD raw) =
      Function.update cache key (some ((cache key).getD raw)) := by
  cases known : cache key with
  | none => simp only [install,known]
  | some value =>
    funext other
    by_cases same : other = key
    · subst other
      simp [install,known]
    · simp [install,known,Function.update_of_ne same]

/-- Reading one coordinate does not populate any other coordinate. -/
theorem install_other (cache : Cache) (key other : Key) (value : Byte) (different : other ≠ key) :
    install cache key value other = cache other := by
  cases known : cache key <;> simp [install,known,Function.update_of_ne different]

end
end FormalProof4FHE.HasteBoots.NativeShakeKernel
