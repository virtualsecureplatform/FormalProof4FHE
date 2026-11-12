module
public import FormalProof4FHE.HasteBoots.CheckpointProgramScope
public import FormalProof4FHE.HasteBoots.NativeMatrixVerifier
public import FormalProof4FHE.HasteBoots.SingletonOpening
@[expose] public section

/-! Native opening programs introduce no recording sites of their own.
Every prover/provider/scheduler callback remains explicit in the scope proof. -/
namespace FormalProof4FHE.HasteBoots.MatrixOpeningRecordScope
open OracleSpec OracleComp CheckpointRecordScope CheckpointProgramScope
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Factor Input Digest Cfg Response Memory : Type}
  {b front suffix claims m queries height leftCount size : ℕ}

/-- Recording scope of all batch callbacks, on every adaptive input. -/
structure BatchCallbacks (scope : Cfg → Prop)
    (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height) : Prop where
  prepare : ∀ memory, Scoped scope (p.prepare memory)
  respond : ∀ memory test, Scoped scope (p.respond memory test)
  receive : ∀ memory sample, Scoped scope (p.receiveColumns memory sample)
  choose : ∀ memory sample columns workers state, Scoped scope (p.choose memory sample columns workers state)

/-- Matrix callbacks contain no extra recording privilege. -/
structure MatrixCallbacks (scope : Cfg → Prop)
    (p : NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height) : Prop where
  respond : ∀ factor memory test, Scoped scope (p.respond factor memory test)
  receive : ∀ factor memory sample, Scoped scope (p.receiveColumns factor memory sample)
  choose : ∀ factor memory sample columns workers state, Scoped scope (p.choose factor memory sample columns workers state)

variable [Field F] [DecidableEq F] [DecidableEq Digest]

theorem batch_next (scope : Cfg → Prop)
    (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (restricted : BatchCallbacks scope p) (memory : Memory)
    (sample : SampleData F Response (2^front) b height queries) :
    Scoped scope (NativeBatchVerifier.next p memory sample) := by
  unfold NativeBatchVerifier.next
  apply bind_scoped scope _ _ (restricted.receive memory sample)
  intro received
  split
  · unfold NativeBatchColumnWorkerPool.program
    exact map_scoped scope _ (pool_scoped scope _ (restricted.choose memory sample received.1) _ _ _) _
  · exact pure_scoped scope _

theorem matrix_next (scope : Cfg → Prop)
    (p : NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (restricted : MatrixCallbacks scope p) (factor : Factor) (memory : Memory)
    (sample : SampleData F Response leftCount b height queries) :
    Scoped scope (NativeMatrixVerifier.next p factor memory sample) := by
  unfold NativeMatrixVerifier.next
  apply bind_scoped scope _ _ (restricted.receive factor memory sample)
  intro received
  unfold NativeColumnWorkerPool.program
  exact map_scoped scope _ (pool_scoped scope _ (restricted.choose factor memory sample received.1) _ _ _) _

section Batch
variable [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

theorem batch_sampled (scope : Cfg → Prop)
    (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (restricted : BatchCallbacks scope p) (memory : Memory) :
    Scoped scope (NativeBatchVerifier.sampledStep p memory) := by
  unfold NativeBatchVerifier.sampledStep StoppingJointMatrixOpening.step
  apply map_scoped scope _ _ _
  apply complete_scoped scope _ _ _ _ (restricted.respond memory)
  intro sample
  exact map_scoped scope _ (batch_next scope p restricted memory sample) _

theorem batch_step (scope : Cfg → Prop)
    (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (restricted : BatchCallbacks scope p) (memory : Memory) :
    Scoped scope (NativeBatchVerifier.step p memory) := by
  unfold NativeBatchVerifier.step
  exact bind_scoped scope _ _ (restricted.prepare memory) (batch_sampled scope p restricted)

/-- Single-opening execution has precisely the callback scope of its
one-claim batch, including its per-root binding before fresh sampling. -/
theorem singleton_step (scope : Cfg → Prop)
    (p : SingletonOpening.Protocol F Input Digest Cfg Response Memory b front suffix m queries height)
    (restricted : BatchCallbacks scope (SingletonOpening.toBatch p)) (memory : Memory) :
    Scoped scope (SingletonOpening.step p memory) := by
  rw [←SingletonOpening.step_eq]
  exact batch_step scope _ restricted memory
end Batch

section Matrix
variable [SampleableType (TestMatrix F leftCount b)] [SampleableType (Fin queries → Fin (2^height))]

theorem matrix_step (scope : Cfg → Prop)
    (p : NativeMatrixVerifier.Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (restricted : MatrixCallbacks scope p) (factor : Factor) (memory : Memory) :
    Scoped scope (NativeMatrixVerifier.step p factor memory) := by
  unfold NativeMatrixVerifier.step StoppingJointMatrixOpening.step
  apply map_scoped scope _ _ _
  apply complete_scoped scope _ _ _ _ (restricted.respond factor memory)
  intro sample
  exact map_scoped scope _ (matrix_next scope p restricted factor memory sample) _
end Matrix

end
end FormalProof4FHE.HasteBoots.MatrixOpeningRecordScope
