module
public import FormalProof4FHE.HasteBoots.MatrixOpeningRecordScope
public import FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck
@[expose] public section

/-! All ZeroCheck callback and trusted recording sites are accounted for on
first-message, round-message, terminal and original-factor opening branches. -/
namespace FormalProof4FHE.HasteBoots.ZeroCheckRecordingScope
open OracleSpec OracleComp CheckpointRecordScope CheckpointProgramScope MatrixOpeningRecordScope
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type} [Field F]
  {b n front suffix m queries height : ℕ}

structure Callbacks (scope : Cfg → Prop)
    (s : AuthenticatedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) : Prop where
  commit : Scoped scope s.commit
  firstRespond : ∀ emission points memory, Scoped scope (s.firstRespond emission points memory)
  afterFirst : ∀ emission points packet coins, Scoped scope (s.afterFirst emission points packet coins)
  send : ∀ emission round memory claimed, Scoped scope (s.send emission round memory claimed)
  afterChallenge : ∀ emission memory challenge, Scoped scope (s.afterChallenge emission memory challenge)
  receiveValues : ∀ emission subclaim memory, Scoped scope (s.receiveValues emission subclaim memory)
  bindValues : ∀ emission subclaim values memory, Scoped scope (s.bindValues emission subclaim values memory)
  openings : ∀ emission packet, MatrixCallbacks scope (s.build emission packet)

/-- Native degree-bounded interpolation changes no callback recording sites. -/
theorem native_callbacks (scope : Cfg → Prop) (characteristic productDegree : ℕ) [CharP F characteristic]
    (firstSmall : (2*b-1)*productDegree+1 ≤ characteristic)
    (roundSmall : (2*b-1)*(productDegree+1)+1 ≤ characteristic)
    (nodesEnough : 2*b ≤ (2*b-1)*productDegree+1)
    (s : AuthenticatedZeroCheck.Scheme F Factor Term
      (Fin b → Fin ((2*b-1)*productDegree+1) → F) (Fin ((2*b-1)*(productDegree+1)+1) → F)
      Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (restricted : Callbacks scope s) :
    Callbacks scope (AuthenticatedZeroCheck.nativeScheme characteristic productDegree firstSmall roundSmall nodesEnough s) :=
  ⟨restricted.commit,restricted.firstRespond,restricted.afterFirst,restricted.send,restricted.afterChallenge,
    restricted.receiveValues,restricted.bindValues,restricted.openings⟩

variable [SampleableType (Fin b → F)]

theorem rounds (scope : Cfg → Prop)
    (s : AuthenticatedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Factor → Digest) × CommitMemory)
    (rounds : ℕ) (claimed : Fin b → F) (memory : Memory) :
    Scoped scope (PackedSumcheckOracle.program s.nodes s.interpret (s.send emission) (s.afterChallenge emission) rounds claimed memory) := by
  classical
  induction rounds generalizing claimed memory with
  | zero => exact pure_scoped scope _
  | succ count ih =>
    unfold PackedSumcheckOracle.program
    apply bind_scoped scope _ _ (restricted.send emission _ memory claimed)
    intro packet
    split
    · apply bind_scoped scope _ _ (private_scoped scope _)
      intro challenge
      apply bind_scoped scope _ _ (restricted.afterChallenge emission packet.2 challenge)
      intro state
      exact bind_scoped scope _ _ (ih _ state) (fun _ => pure_scoped scope _)
    · exact pure_scoped scope _

variable [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]

theorem zero (scope : Cfg → Prop)
    (s : AuthenticatedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Factor → Digest) × CommitMemory) :
    Scoped scope (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret
      (s.firstRespond emission) (s.afterFirst emission) (s.send emission) (s.afterChallenge emission) (s.initial emission)) := by
  unfold PackedZeroOracle.program
  apply bind_scoped scope _ _ (private_scoped scope _)
  intro points
  apply bind_scoped scope _ _ (restricted.firstRespond emission points _)
  intro first
  split
  · apply bind_scoped scope _ _ (private_scoped scope _)
    intro coins
    apply bind_scoped scope _ _ (restricted.afterFirst emission points first coins)
    intro state
    exact bind_scoped scope _ _ (rounds scope s restricted emission n _ state) (fun _ => pure_scoped scope _)
  · exact pure_scoped scope _

variable [DecidableEq F] [Fintype Term]

theorem select (scope : Cfg → Prop)
    (s : AuthenticatedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Factor → Digest) × CommitMemory) :
    Scoped scope (AuthenticatedZeroCheck.select s emission) := by
  unfold AuthenticatedZeroCheck.select PreparedZeroTerminal.select
  apply map_scoped scope _ _ _
  apply continuation_scoped scope _ _ (zero scope s restricted emission)
  intro earlier
  cases earlier with
  | none => exact pure_scoped scope _
  | some entry =>
    unfold PreparedZeroTerminal.prepare
    apply bind_scoped scope _ _ (restricted.receiveValues emission entry.1 entry.2)
    intro proposal
    split
    · exact bind_scoped scope _ _ (restricted.bindValues emission entry.1 proposal.1 proposal.2) (fun _ => pure_scoped scope _)
    · exact pure_scoped scope _

variable [DecidableEq Digest]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

theorem continuation (scope : Cfg → Prop)
    (s : AuthenticatedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (restricted : Callbacks scope s) (emission : (Factor → Digest) × CommitMemory) :
    Scoped scope (AuthenticatedZeroCheck.continuation s emission) := by
  unfold AuthenticatedZeroCheck.continuation NativeCommittedOpening.continuation
  apply continuation_scoped scope _ _ (select scope s restricted emission)
  intro packet
  split
  · apply shortCircuit_scoped scope _ _ _ packet.data.memory
    intro factor _ memory
    apply matrix_step scope _ _ factor memory
    have original := restricted.openings emission packet
    exact ⟨original.respond,original.receive,original.choose⟩
  · exact pure_scoped scope _

/-- Scope is derived from the actual original-factor recording list and
all callbacks; no verifier acceptance or source-truth premise is involved. -/
theorem program (scope : Cfg → Prop)
    (s : AuthenticatedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (restricted : Callbacks scope s) (tags : ∀ factor ∈ s.factors, scope (s.tag factor)) :
    Scoped scope (AuthenticatedZeroCheck.program s) := by
  unfold AuthenticatedZeroCheck.program
  apply commitment_scoped scope _ _ _ restricted.commit _ (continuation scope s restricted)
  intro emission request member
  simp only [CommittedJointMatrixOpening.requests,List.mem_map] at member
  obtain ⟨factor,present,equal⟩ := member
  have same := congrArg Prod.fst equal
  rw [←same]
  exact tags factor present

end
end FormalProof4FHE.HasteBoots.ZeroCheckRecordingScope
