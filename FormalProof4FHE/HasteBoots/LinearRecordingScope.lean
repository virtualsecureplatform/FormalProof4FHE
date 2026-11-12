module
public import FormalProof4FHE.HasteBoots.MatrixOpeningRecordScope
public import FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
@[expose] public section

/-! Derive recording scope of the real linear reconstruction program from its
callbacks and trusted context tags. All source-root overrides are retained. -/
namespace FormalProof4FHE.HasteBoots.LinearRecordingScope
open OracleSpec OracleComp CheckpointRecordScope CheckpointProgramScope MatrixOpeningRecordScope
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Input Digest Cfg Response Memory CommitMemory : Type} [Field F]
  {count b front suffix m queries height : ℕ}

structure Callbacks (scope : Cfg → Prop)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height) : Prop where
  commit : Scoped scope s.commit
  bindRelations : ∀ emission memory, Scoped scope (s.bindRelations emission memory)
  receive : ∀ emission memory query, Scoped scope (s.receive emission memory query)
  openings : ∀ emission packet factor, BatchCallbacks scope (SingletonOpening.toBatch (s.build emission packet factor))

/-- Native interpolation changes trusted nodes but grants no recording access. -/
theorem native_callbacks (scope : Cfg → Prop) (characteristic : ℕ) [CharP F characteristic]
    (enough : 2*b ≤ characteristic)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (restricted : Callbacks scope s) :
    Callbacks scope (AuthenticatedLinear.nativeScheme characteristic enough s) :=
  ⟨restricted.commit,restricted.bindRelations,restricted.receive,restricted.openings⟩

/-- Caller-fixed input/digit roots and verifier-owned reconstruction relations
preserve callback scope, including the actual commitment's earlier work. -/
theorem owned_callbacks {d : ℕ} (scope : Cfg → Prop) (inputRoot : Digest) (digits : Fin d → Digest) (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory (2*d+2) b front suffix m queries height)
    (restricted : Callbacks scope s) :
    Callbacks scope (OwnedDecompositionSoundness.stage inputRoot digits radix s) := by
  constructor
  · exact bind_scoped scope _ _ restricted.commit (fun _ => pure_scoped scope _)
  · exact restricted.bindRelations
  · exact restricted.receive
  · exact restricted.openings

variable [DecidableEq F] [Fintype F]
  [SampleableType (Fin b → F)]

theorem select (scope : Cfg → Prop)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Fin count → Digest) × CommitMemory) :
    Scoped scope (AuthenticatedLinear.select s emission) := by
  unfold AuthenticatedLinear.select PackedLinearOracle.program
  split
  · apply bind_scoped scope _ _ (restricted.bindRelations emission _)
    intro memory
    apply map_scoped scope _ _ _
    exact continuation_scoped scope _ _ (private_scoped scope _) (restricted.receive emission memory)
  · exact pure_scoped scope _

variable [DecidableEq Digest] [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

theorem continuation (scope : Cfg → Prop)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Fin count → Digest) × CommitMemory) :
    Scoped scope (AuthenticatedLinear.continuation s emission) := by
  rw [AuthenticatedLinear.continuation_single]
  apply continuation_scoped scope _ _ (select scope s restricted emission)
  intro packet
  split
  · apply shortCircuit_scoped scope _ _ _ packet.memory
    intro factor _ memory
    apply singleton_step scope _ _ memory
    have original := restricted.openings emission packet factor
    exact ⟨original.prepare,original.respond,original.receive,original.choose⟩
  · exact pure_scoped scope _

/-- The trusted registry is the complete actual factor array. Source roots
are unconstrained; only their fixed context tags must lie in the recording scope. -/
theorem program (scope : Cfg → Prop)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (restricted : Callbacks scope s) (tags : ∀ factor, scope (s.tag factor)) :
    Scoped scope (AuthenticatedLinear.program s) := by
  unfold AuthenticatedLinear.program
  apply commitment_scoped scope _ _ _ restricted.commit _ (continuation scope s restricted)
  intro emission request member
  simp only [CommittedJointMatrixOpening.requests,List.mem_map] at member
  obtain ⟨factor,_,equal⟩ := member
  have same := congrArg Prod.fst equal
  rw [←same]
  exact tags factor

end
end FormalProof4FHE.HasteBoots.LinearRecordingScope
