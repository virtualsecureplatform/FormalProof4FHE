module
public import FormalProof4FHE.HasteBoots.CheckpointRecordScope
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix
public import FormalProof4FHE.HasteBoots.InteractiveSampling
public import FormalProof4FHE.HasteBoots.ShortCircuitSequence
public import FormalProof4FHE.HasteBoots.HashWorkerPool
@[expose] public section

/-! Scope follows actual private draws, early-return loops and worker scheduling.
These lemmas constrain recording tags, without bounding other oracle work. -/
namespace FormalProof4FHE.HasteBoots.CheckpointProgramScope
open OracleSpec OracleComp CheckpointRecordScope
noncomputable section
variable {Cfg Input Digest A B Challenge Response Draw Memory Index Result Emission : Type}
  {ι : Type} {base : OracleSpec ι}

theorem simulate_scoped (scope : Cfg → Prop)
    (impl : QueryImpl base (OracleComp (SharedSequence.Shared Cfg Input Digest)))
    (restricted : ∀ query, Scoped scope (impl query)) (program : OracleComp base A) :
    Scoped scope (simulateQ impl program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact pure_scoped scope value
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query]
    exact bind_scoped scope _ _ (restricted query) ih

theorem private_scoped (scope : Cfg → Prop) (program : ProbComp A) :
    Scoped scope (PrivateSampling.embed Cfg Input Digest program) := by
  apply simulate_scoped scope _ _ program
  intro query
  exact query_scoped scope (.inl query) trivial

theorem continuation_scoped (scope : Cfg → Prop)
    (first : OracleComp (SharedSequence.Shared Cfg Input Digest) A)
    (next : A → OracleComp (SharedSequence.Shared Cfg Input Digest) B)
    (restricted : Scoped scope first) (following : ∀ value, Scoped scope (next value)) :
    Scoped scope (SharedContinuation.program first next) := by
  unfold SharedContinuation.program
  apply bind_scoped scope _ _ restricted
  intro value
  exact bind_scoped scope _ _ (following value) (fun _ => pure_scoped scope _)

theorem interactive_scoped (scope : Cfg → Prop) (coins : ProbComp Challenge)
    (respond : Challenge → OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (draws : ProbComp Draw) (restricted : ∀ challenge, Scoped scope (respond challenge)) :
    Scoped scope (InteractiveSampling.program coins respond draws) := by
  unfold InteractiveSampling.program
  apply bind_scoped scope _ _ (private_scoped scope coins)
  intro challenge
  apply bind_scoped scope _ _ (restricted challenge)
  intro response
  exact bind_scoped scope _ _ (private_scoped scope draws) (fun _ => pure_scoped scope _)

theorem complete_scoped (scope : Cfg → Prop) (coins : ProbComp Challenge)
    (respond : Challenge → OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (draws : ProbComp Draw)
    (next : ((Challenge × Response) × Draw) → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (restricted : ∀ challenge, Scoped scope (respond challenge))
    (following : ∀ sample, Scoped scope (next sample)) :
    Scoped scope (InteractiveSampling.complete coins respond draws next) :=
  continuation_scoped scope _ _ (interactive_scoped scope coins respond draws restricted) following

/-- Trusted recording sites are checked against every actual emitted registry. -/
theorem commitment_scoped (scope : Cfg → Prop) (requests : Emission → List (Cfg × Digest))
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (restricted : Scoped scope commit) (records : ∀ emission request, request ∈ requests emission → scope request.1)
    (following : ∀ emission, Scoped scope (next emission)) :
    Scoped scope (MultiCommitmentPrefix.program requests commit next) := by
  unfold MultiCommitmentPrefix.program
  apply bind_scoped scope _ _ restricted
  intro emission
  apply bind_scoped scope _ _ (recordRoots_scoped scope (requests emission) (records emission))
  intro _
  exact bind_scoped scope _ _ (following emission) (fun _ => pure_scoped scope _)

/-- Rejected branches retain their scope and skip the remaining loop. -/
theorem shortCircuit_scoped (scope : Cfg → Prop)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Result Memory))
    (indices : List Index) (restricted : ∀ index ∈ indices, ∀ memory, Scoped scope (step index memory))
    (memory : Memory) : Scoped scope (ShortCircuitSequence.program step indices memory) := by
  induction indices generalizing memory with
  | nil => exact pure_scoped scope _
  | cons index rest ih =>
    unfold ShortCircuitSequence.program
    apply bind_scoped scope _ _ (restricted index (List.mem_cons_self) memory)
    intro first
    split
    · exact bind_scoped scope _ _
        (ih (fun next member => restricted next (List.mem_cons_of_mem index member)) first.memory)
        (fun _ => pure_scoped scope _)
    · simp only [pure_bind]
      exact pure_scoped scope _

/-- A worker tick can issue only its single shared hash query. -/
theorem tick_scoped (scope : Cfg → Prop) (worker : OracleComp (Input →ₒ Digest) Bool) :
    Scoped scope (HashWorkerPool.tick (Cfg := Cfg) worker) := by
  cases worker with
  | pure value => exact pure_scoped scope _
  | queryBind input next =>
    rw [HashWorkerPool.tick_query]
    exact map_scoped scope _ (query_scoped scope (.inr (.inl input)) trivial) next

/-- Arbitrary scheduler work is covered on all residual-worker/memory branches. -/
theorem pool_scoped {count : ℕ} (scope : Cfg → Prop)
    (choose : HashWorkerPool.Workers Input Digest count → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Option (Fin count) × Memory))
    (restricted : ∀ workers memory, Scoped scope (choose workers memory))
    (fuel : ℕ) (workers : HashWorkerPool.Workers Input Digest count) (memory : Memory) :
    Scoped scope (HashWorkerPool.program choose fuel workers memory) := by
  induction fuel generalizing workers memory with
  | zero => exact pure_scoped scope _
  | succ fuel ih =>
    unfold HashWorkerPool.program
    split
    · exact pure_scoped scope _
    · apply bind_scoped scope _ _ (restricted workers memory)
      intro selected
      cases selected.1 with
      | none => exact pure_scoped scope _
      | some index =>
        exact bind_scoped scope _ _ (tick_scoped scope _) (fun _ => ih _ _)

end
end FormalProof4FHE.HasteBoots.CheckpointProgramScope
