module
public import FormalProof4FHE.HasteBoots.MatrixOpeningRecordScope
public import FormalProof4FHE.HasteBoots.AuthenticatedNTT
@[expose] public section

/-! NTT row proposals, bindings, compression and both original-root opening
batches retain their callbacks' recording scope on every adaptive branch. -/
namespace FormalProof4FHE.HasteBoots.NTTRecordingScope
open OracleSpec OracleComp CheckpointRecordScope CheckpointProgramScope MatrixOpeningRecordScope
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Input Digest Cfg Response Memory CommitMemory : Type} [Field F]
  {b c r k front suffix m queries height : ℕ}

structure Callbacks (scope : Cfg → Prop)
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height) : Prop where
  commit : Scoped scope s.commit
  receive : ∀ emission points memory, Scoped scope (s.receive emission points memory)
  bindRows : ∀ emission points proposal, Scoped scope (s.bindRows emission points proposal)
  afterQuery : ∀ emission packet query, Scoped scope (s.afterQuery emission packet query)
  openings : ∀ emission packet side, BatchCallbacks scope (s.build emission packet side)

variable [DecidableEq F] [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]

theorem select (scope : Cfg → Prop)
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Bool → Digest) × CommitMemory) :
    Scoped scope (AuthenticatedNTT.select s emission) := by
  unfold AuthenticatedNTT.select NTTCompression.program GuardedCompression.program
  apply continuation_scoped scope _ _
  · unfold NTTRowOracle.program
    apply continuation_scoped scope _ _ (private_scoped scope _)
    intro points
    unfold NTTRowOracle.next
    apply bind_scoped scope _ _ (restricted.receive emission points _)
    intro proposal
    exact bind_scoped scope _ _ (restricted.bindRows emission points proposal) (fun _ => pure_scoped scope _)
  · intro packet
    unfold GuardedCompression.finish
    split
    · apply map_scoped scope _ _ _
      exact continuation_scoped scope _ _ (private_scoped scope _) (restricted.afterQuery emission packet)
    · exact pure_scoped scope _

variable [DecidableEq Digest]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

theorem continuation (scope : Cfg → Prop)
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Bool → Digest) × CommitMemory) :
    Scoped scope (AuthenticatedNTT.continuation s emission) := by
  unfold AuthenticatedNTT.continuation CommittedBatchOpening.continuation
  apply continuation_scoped scope _ _ (select scope s restricted emission)
  intro packet
  split
  · apply shortCircuit_scoped scope _ _ _ (AuthenticatedNTT.memory packet)
    intro side _ memory
    apply batch_step scope _ _ memory
    have original := restricted.openings emission packet side
    exact ⟨original.prepare,original.respond,original.receive,original.choose⟩
  · exact pure_scoped scope _

/-- The original coefficient/evaluation context tags are the only trusted
recording sites introduced by the authenticated NTT verifier itself. -/
theorem program (scope : Cfg → Prop)
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (restricted : Callbacks scope s) (tags : ∀ side, scope (s.tag side)) :
    Scoped scope (AuthenticatedNTT.program s) := by
  unfold AuthenticatedNTT.program
  apply commitment_scoped scope _ _ _ restricted.commit _ (continuation scope s restricted)
  intro emission request member
  simp only [CommittedJointMatrixOpening.requests,List.mem_map] at member
  obtain ⟨side,_,equal⟩ := member
  have same := congrArg Prod.fst equal
  rw [←same]
  exact tags side

end
end FormalProof4FHE.HasteBoots.NTTRecordingScope
