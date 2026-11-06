module

public import FormalProof4FHE.HasteBoots.HashWorkerPool
public import FormalProof4FHE.HasteBoots.NativeHashOracleBridge
public import FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler
@[expose] public section

/-! Causal mixed-oracle scheduling of the original hash workers. Scheduler
prequeries and worker hashes share the native history and lazy caches.
Acceptance replays every original worker in the resulting common cache.
Fuel is an extensible analysis prefix. Physical work, fairness, termination
and native scheduler/compiler refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.CausalHashWorkerPool
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open HashWorkerPool (Workers Outcome)
open OracleProgram (Program bind run)
open OracleSpec OracleComp
noncomputable section

def tick (worker : OracleComp (Input →ₒ Digest) Bool) : Program (OracleComp (Input →ₒ Digest) Bool) :=
  OracleComp.casesOn worker (fun value => .pure (pure value))
    (fun input next => .hash input (fun digest => .pure (next digest)))

def program {Memory : Type} {count : ℕ}
    (choose : Workers Input Digest count → Memory → Program (Option (Fin count) × Memory)) :
    ℕ → Workers Input Digest count → Memory → Program (Outcome Input Digest Memory count)
  | 0,workers,memory => .pure ⟨workers,memory⟩
  | fuel+1,workers,memory =>
    if HashWorkerPool.allAccepted workers then .pure ⟨workers,memory⟩ else
      bind (choose workers memory) (fun selected => match selected.1 with
      | none => .pure ⟨workers,selected.2⟩
      | some index => bind (tick (workers index)) (fun remaining =>
          program choose fuel (Function.update workers index remaining) selected.2))

def Known (cache : (Input →ₒ Digest).QueryCache) (log : List Observation) : Prop :=
  ∀ input digest, Observation.hash input (List.ofFn digest) ∈ log → cache input = some digest

theorem known_sublist {cache : (Input →ₒ Digest).QueryCache} {before after : List Observation}
    (known : Known cache after) (sublist : before.Sublist after) : Known cache before :=
  fun input digest member => known input digest (sublist.subset member)

/-- One actual native hash fixes the same residual in any cache containing its observed answer. -/
theorem tick_replay (worker : OracleComp (Input →ₒ Digest) Bool) (world : World)
    (cache : (Input →ₒ Digest).QueryCache) (known : Known cache (run (tick worker) world).run.2) :
    simulateQ cache.toPartialImpl worker = simulateQ cache.toPartialImpl (run (tick worker) world).run.1 := by
  cases worker with
  | pure value => rfl
  | queryBind input next =>
    have cached : cache input = some (InputIndexedOracle.sha512 world input) := known input _ List.mem_cons_self
    change simulateQ cache.toPartialImpl ((liftM ((Input →ₒ Digest).query input) : OracleComp (Input →ₒ Digest) Digest) >>= next) = _
    rw [simulateQ_bind,simulateQ_spec_query,QueryCache.toPartialImpl_apply,cached]
    rfl

/-- Scheduler prequeries and interleaved worker steps remain in one complete causal history. -/
theorem program_replays {Memory : Type} {count : ℕ}
    (choose : Workers Input Digest count → Memory → Program (Option (Fin count) × Memory))
    (fuel : ℕ) (workers : Workers Input Digest count) (memory : Memory) (world : World)
    (cache : (Input →ₒ Digest).QueryCache) (known : Known cache (run (program choose fuel workers memory) world).run.2) :
    ∀ index, simulateQ cache.toPartialImpl (workers index) =
      simulateQ cache.toPartialImpl ((run (program choose fuel workers memory) world).run.1.workers index) := by
  induction fuel generalizing workers memory with
  | zero => intro index; rfl
  | succ fuel ih =>
    by_cases complete : HashWorkerPool.allAccepted workers = true
    · intro index
      simp only [program,complete,ite_true,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    · simp only [program,complete,Bool.false_eq_true,ite_false,OracleProgram.run_bind,ObservationReplay.run_bind] at known ⊢
      cases selected : (run (choose workers memory) world).run.1.1 with
      | none =>
        intro index
        simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure]
      | some index =>
        simp only [selected,OracleProgram.run_bind,ObservationReplay.run_bind] at known ⊢
        have stepKnown : Known cache (run (tick (workers index)) world).run.2 :=
          known_sublist known ((List.sublist_append_left _ _).trans (List.sublist_append_right _ _))
        have laterKnown : Known cache (run (program choose fuel
            (Function.update workers index (run (tick (workers index)) world).run.1)
            (run (choose workers memory) world).run.1.2) world).run.2 :=
          known_sublist known ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _))
        have tail := ih _ _ laterKnown
        intro current
        rw [← tail current]
        by_cases same : current = index
        · subst current
          rw [Function.update_self]
          exact tick_replay _ world cache stepKnown
        · rw [Function.update_of_ne same]

theorem accepted_replays {Memory : Type} {count : ℕ}
    (choose : Workers Input Digest count → Memory → Program (Option (Fin count) × Memory))
    (fuel : ℕ) (workers : Workers Input Digest count) (memory : Memory) (world : World)
    (cache : (Input →ₒ Digest).QueryCache) (known : Known cache (run (program choose fuel workers memory) world).run.2)
    (accepted : HashWorkerPool.allAccepted (run (program choose fuel workers memory) world).run.1.workers = true)
    (index : Fin count) : simulateQ cache.toPartialImpl (workers index) = some true := by
  rw [program_replays choose fuel workers memory world cache known index,HashWorkerPool.allAccepted_sound _ accepted index]
  rfl

/-- The actual mixed log supplies every needed answer, even after later shared work. -/
theorem accepted_actual {Memory : Type} {count : ℕ}
    (choose : Workers Input Digest count → Memory → Program (Option (Fin count) × Memory))
    (fuel : ℕ) (workers : Workers Input Digest count) (memory : Memory) (world : World)
    (earlier later : List Observation) (past : ObservationReplay.Agrees world earlier) (future : ObservationReplay.Agrees world later)
    (accepted : HashWorkerPool.allAccepted (run (program choose fuel workers memory) world).run.1.workers = true)
    (index : Fin count) :
    simulateQ (JointHashCache.project (earlier ++ (run (program choose fuel workers memory) world).run.2 ++ later)).cache.toPartialImpl
      (workers index) = some true := by
  apply accepted_replays choose fuel workers memory world _ _ accepted index
  intro input digest member
  apply NativeHashOracleBridge.cache_known world _ _ input digest
    (List.mem_append_left _ (List.mem_append_right earlier member))
  exact (ObservationReplay.agrees_append world _ later).mpr
    ⟨(ObservationReplay.agrees_append world earlier _).mpr ⟨past,(OracleProgram.run_replay _).truthful world⟩,future⟩


/-- Increasing analysis fuel only extends the native history; cancellation does not restart work. -/
theorem log_prefix {Memory : Type} {count : ℕ}
    (choose : Workers Input Digest count → Memory → Program (Option (Fin count) × Memory))
    (first extra : ℕ) (workers : Workers Input Digest count) (memory : Memory) (world : World) :
    (run (program choose first workers memory) world).run.2.IsPrefix
      (run (program choose (first+extra) workers memory) world).run.2 := by
  induction first generalizing workers memory with
  | zero => exact List.nil_prefix
  | succ first ih =>
    by_cases complete : HashWorkerPool.allAccepted workers = true
    · simp only [Nat.succ_add,program,complete,ite_true,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
      exact List.nil_prefix
    · simp only [Nat.succ_add,program,complete,Bool.false_eq_true,ite_false,OracleProgram.run_bind,ObservationReplay.run_bind]
      cases selected : (run (choose workers memory) world).run.1.1 with
      | none =>
        simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
        exact List.prefix_rfl
      | some index =>
        simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
        obtain ⟨suffix,extension⟩ := ih (Function.update workers index (run (tick (workers index)) world).run.1)
          (run (choose workers memory) world).run.1.2
        refine ⟨suffix,?_⟩
        simpa only [List.append_assoc] using congrArg
          (fun log => (run (choose workers memory) world).run.2 ++ (run (tick (workers index)) world).run.2 ++ log) extension

end
end FormalProof4FHE.HasteBoots.CausalHashWorkerPool
