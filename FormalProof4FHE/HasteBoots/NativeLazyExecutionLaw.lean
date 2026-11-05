module

public import FormalProof4FHE.HasteBoots.NativeLazyExecution
public import FormalProof4FHE.HasteBoots.OracleKernelComposition

@[expose] public section

/-! Exact conditional probabilities for the actual shared lazy mixed-oracle
interpreter. Events include the complete value and ordered native log. The
initial caches come from a replayable whole history; adaptive continuations
receive only responses. Final cache/state recovery and infinite limits are
separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open InputIndexedOracle (World Input law)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
noncomputable section

theorem execute_law {Cfg Payload A : Type} (program : OracleProgram.Program A)
    {P : Type} {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (event : A × List Observation → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (OracleProgram.run program other).run} =
      Pr{let result ← (NativeLazyExecution.execute enc dummy shape program
        (NativeShakeKernel.observed (past world).run.2 world) state)}[event result] := by
  classical
  induction program generalizing P world state event with
  | pure value =>
    rw [NativeLazyExecution.execute_pure,prEvent_pure,OraclePosterior.execution_posterior replay world]
    simp only [OracleProgram.run,WriterT.run_pure]
    change (law.map (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world)) {other : World | event (value,[])} = _
    by_cases yes : event (value,[])
    · simp [yes]
    · simp [yes]
  | start input next ih =>
    rw [NativeLazyExecution.execute_start,prEvent_map]
    exact ih replay world state hashStart
      (fun result => event (NativeCheckpointProgram.prepend (.start input) result))
  | read input offset count next ih =>
    rw [NativeLazyExecution.execute_read]
    let bad : Set World := {other | event (OracleProgram.run (.read input offset count next) other).run}
    have measurable : MeasurableSet bad := OracleExecutionLaw.event_measurable
      (OracleProgram.run_replay (.read input offset count next)) event
    have transfer := OracleKernelComposition.read_transfer replay world input offset count bad measurable
      (fun first => NativeCheckpointProgram.prepend (.output input offset first.1) <$>
        NativeLazyExecution.execute enc dummy shape (next first.1) first.2 state) event
    simp only [← bind_pure_comp] at transfer ⊢
    apply transfer
    intro current same
    let later := OracleHistorySnapshot.read past input offset count
    have laterReplay := OracleHistorySnapshot.read_replay replay input offset count
    let values := InputIndexedOracle.bytes current input offset count
    have fixed : ∀ other, (later other).run = (later current).run →
        InputIndexedOracle.bytes other input offset count = values := by
      intro other equal
      exact congrArg (fun history => history.1.2) equal
    have cacheEq : NativeShakeKernel.observed (later current).run.2 current =
        NativeShakeHistory.writeBytes (NativeShakeKernel.observed (past world).run.2 world) input offset values := by
      rw [OracleHistorySnapshot.read_run,NativeShakeProjection.observed_append_read,
        NativeShakeProjection.observed_of_fiber replay world current same]
    have hashEq : state.hash = JointHashCache.project (later current).run.2 := by
      rw [OracleHistorySnapshot.read_run,JointHashCache.project_append]
      simpa only [JointHashCache.record,congrArg Prod.snd same] using hashStart
    calc _ = (law[|{other | (later other).run = (later current).run}])
          {other | event (NativeCheckpointProgram.prepend (.output input offset values)
            (OracleProgram.run (next values) other).run)} := by
          apply NativeShakeProjection.conditional_event_congr laterReplay current
          intro other equal
          simp only [OracleProgram.run,ObservationReplay.read,ObservationReplay.run_bind,WriterT.run_mk]
          rw [fixed other equal]
          rfl
         _ = _ := by
          have tail := ih values laterReplay current state hashEq
            (fun result => event (NativeCheckpointProgram.prepend (.output input offset values) result))
          rw [cacheEq] at tail
          simpa only [values,InputIndexedOracle.bytes,InputIndexedOracle.block,NativeShakeReadLaw.outcome,bind_assoc,pure_bind,bind_pure_comp,Functor.map_map] using tail
  | hash input next ih =>
    rw [NativeLazyExecution.execute_hash,hashStart]
    let bad : Set World := {other | event (OracleProgram.run (.hash input next) other).run}
    have measurable : MeasurableSet bad := OracleExecutionLaw.event_measurable
      (OracleProgram.run_replay (.hash input next)) event
    have transfer := OracleKernelComposition.hash_transfer replay world input bad measurable
      (fun digest => NativeCheckpointProgram.prepend (.hash input (List.ofFn digest)) <$>
        NativeLazyExecution.execute enc dummy shape (next digest)
          (NativeShakeKernel.observed (past world).run.2 world)
          (CheckpointExecution.afterHash enc dummy shape state
            (JointHashCache.record (JointHashCache.project (past world).run.2) (.hash input (List.ofFn digest))))) event
    simp only [← bind_pure_comp] at transfer ⊢
    apply transfer
    intro current same
    let later := OracleHistorySnapshot.hash past input
    have laterReplay := OracleHistorySnapshot.hash_replay replay input
    let digest := InputIndexedOracle.sha512 current input
    have fixed : ∀ other, (later other).run = (later current).run →
        InputIndexedOracle.sha512 other input = digest := by
      intro other equal
      exact congrArg (fun history => history.1.2) equal
    have cacheEq : NativeShakeKernel.observed (later current).run.2 current =
        NativeShakeKernel.observed (past world).run.2 world := by
      rw [OracleHistorySnapshot.hash_run,NativeShakeProjection.observed_append_hash,
        NativeShakeProjection.observed_of_fiber replay world current same]
    let newState := CheckpointExecution.afterHash enc dummy shape state
      (JointHashCache.record (JointHashCache.project (past world).run.2) (.hash input (List.ofFn digest)))
    have hashEq : newState.hash = JointHashCache.project (later current).run.2 := by
      change JointHashCache.record (JointHashCache.project (past world).run.2) (.hash input (List.ofFn digest)) = _
      rw [OracleHistorySnapshot.hash_run,JointHashCache.project_append,congrArg Prod.snd same]
    calc _ = (law[|{other | (later other).run = (later current).run}])
          {other | event (NativeCheckpointProgram.prepend (.hash input (List.ofFn digest))
            (OracleProgram.run (next digest) other).run)} := by
          apply NativeShakeProjection.conditional_event_congr laterReplay current
          intro other equal
          simp only [OracleProgram.run,ObservationReplay.hash,ObservationReplay.run_bind,WriterT.run_mk]
          rw [fixed other equal]
          rfl
         _ = _ := by
          have tail := ih digest laterReplay current newState hashEq
            (fun result => event (NativeCheckpointProgram.prepend (.hash input (List.ofFn digest)) result))
          rw [cacheEq] at tail
          simpa only [bind_assoc,pure_bind,bind_pure_comp,Functor.map_map] using tail


/-- Every finite analysis prefix keeps its actual residual program in the
observed result. Fuel imposes no retry cap on the original native program. -/
theorem prefix_law {Cfg Payload A P : Type} (fuel : ℕ) (program : OracleProgram.Program A)
    {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (event : (OracleProgram.Program A ⊕ A) × List Observation → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (OracleProgram.runPrefix fuel program other).run} =
      Pr{let result ← (NativeLazyExecution.execute enc dummy shape (NativeProgramPrefix.take fuel program)
        (NativeShakeKernel.observed (past world).run.2 world) state)}[event result] := by
  simpa only [NativeProgramPrefix.take_run] using
    execute_law (NativeProgramPrefix.take fuel program) replay world enc dummy shape state hashStart event

/-- Empty initial byte/hash caches discharge the history premises. -/
theorem from_empty {Cfg Payload A : Type} (program : OracleProgram.Program A)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (event : A × List Observation → Prop) :
    law {other | event (OracleProgram.run program other).run} =
      Pr{let result ← (NativeLazyExecution.execute enc dummy shape program NativeShakeCache.empty
        (CheckpointExecution.empty shape))}[event result] := by
  have proved := execute_law program (past := fun _ => WriterT.mk ((),[]))
    (ObservationReplay.pure_replay ()) (fun _ => 0)
    enc dummy shape (CheckpointExecution.empty shape) rfl event
  simp only [WriterT.run_mk] at proved
  have emptyCache : NativeShakeKernel.observed [] (fun _ => 0) = NativeShakeCache.empty := by
    funext key
    simp [NativeShakeKernel.observed,ObservationReplay.footprint,NativeShakeCache.empty]
  rw [emptyCache] at proved
  simpa using proved


/-- The same exact conditional law includes the owned final SHAKE cache.
It is the observed cache of the complete old-plus-new native log. -/
theorem cache_law {Cfg Payload A P : Type} (program : OracleProgram.Program A)
    {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (event : (A × List Observation) × NativeShakeCache.Cache → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event ((OracleProgram.run program other).run,
        NativeShakeKernel.observed ((past other).run.2 ++ (OracleProgram.run program other).run.2) other)} =
      Pr{let result ← (NativeLazyExecution.executeWithCache enc dummy shape program
        (NativeShakeKernel.observed (past world).run.2 world) state)}[event result] := by
  rw [NativeLazyExecution.executeWithCache_records,prEvent_map]
  calc _ = (law[|{other | (past other).run = (past world).run}]) {other | event ((OracleProgram.run program other).run,
        (OracleProgram.run program other).run.2.foldl NativeShakeHistory.record
          (NativeShakeKernel.observed (past world).run.2 world))} := by
        apply NativeShakeProjection.conditional_event_congr replay world
        intro other same
        have truthful := (ObservationReplay.agrees_append other (past other).run.2
          (OracleProgram.run program other).run.2).mpr
            ⟨replay.truthful other,(OracleProgram.run_replay program).truthful other⟩
        rw [← NativeShakeProjection.fold_observed _ other truthful,List.foldl_append,
          NativeShakeProjection.fold_observed _ other (replay.truthful other),
          NativeShakeProjection.observed_of_fiber replay world other same]
       _ = _ := execute_law program replay world enc dummy shape state hashStart
          (fun packet => event (packet,packet.2.foldl NativeShakeHistory.record
            (NativeShakeKernel.observed (past world).run.2 world)))

end
end FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw
