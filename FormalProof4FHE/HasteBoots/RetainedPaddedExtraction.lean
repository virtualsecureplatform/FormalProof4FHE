module
public import FormalProof4FHE.HasteBoots.PaddedPublicZeroCheck
public import FormalProof4FHE.HasteBoots.DependentStageContinuation
@[expose] public section

/-! Append extraction to a retained comparison return. The enclosing caller
reads acceptance and memory from that actual return. The selected index keeps
the predecessor so its original endpoint remains available to the child. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Before Cfg Input Digest Response Memory CommitMemory Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {b n : ℕ}

variable (base : Before → Memory → PaddedPublicZeroCheck.Scheme F Unit Bool Term FirstMessage Message
  Input Digest Cfg Response Memory CommitMemory H b n)
  (get : Before → Option (Bool × Memory))
  (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))

/-- Only a successful actual comparison return enables extraction. -/
def select (before : Before) : Option (Before × Memory) :=
  (get before).bind fun returned => if returned.1 then some (before,returned.2) else none

abbrev Child (selected : Before × Memory) :=
  PaddedPublicZeroCheck.Prefix (Private := Unit) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
    PaddedPublicZeroCheck.RunResult (base selected.1 selected.2)

variable [SampleableType Digest] [SampleableType (Fin b → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((base before memory).code factor).front) b)]
  [∀ before memory factor, SampleableType (Fin ((base before memory).code factor).queries → Fin (2^H ((base before memory).tag factor)))]

def child (dummy : Digest) (selected : Before × Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) :=
  PaddedPublicZeroCheck.witness (base selected.1 selected.2) dummy initial

def finish (dummy : Digest) := DependentStageContinuation.program (select get) state (child base dummy)

def finalState (outcome : Before × Option (Sigma (Child base))) :=
  DependentStageContinuation.finalState state (fun _ result => result.2.2) outcome

/-- The child uses the returned comparison memory and the same predecessor state. -/
theorem reached (dummy : Digest) (before : Before) (result : Sigma (Child base))
    (supported : (before,some result) ∈ support (finish base get state dummy before)) :
    result.1.1 = before ∧ get before = some (true,result.1.2) ∧
      result.2 ∈ support (child base dummy result.1 (state before)) := by
  have actual := DependentStageContinuation.reached (select get) state (child base dummy) before result supported
  refine ⟨?_,?_,actual.2⟩
  all_goals
    unfold select at actual
    cases found : get before with
    | none => simp only [found,Option.bind_none] at actual; cases actual.1
    | some returned =>
      simp only [found,Option.bind_some] at actual
      split at actual
      · rename_i accepted
        have same := Option.some.inj actual.1
        first
        | exact (congrArg Prod.fst same).symm
        | apply congrArg some
          apply Prod.ext
          · exact accepted
          · exact congrArg (fun pair : Before × Memory => pair.2) same
      · cases actual.1

/-- A child reached in the complete bind has the real supported predecessor,
not an independently supplied result or private-memory label. -/
theorem reached_bind (dummy : Digest) (prior : ProbComp Before) (before : Before) (result : Sigma (Child base))
    (supported : (before,some result) ∈ support (prior >>= finish base get state dummy)) :
    before ∈ support prior ∧ result.1.1 = before ∧ get before = some (true,result.1.2) ∧
      result.2 ∈ support (child base dummy result.1 (state before)) := by
  rw [support_bind] at supported
  obtain ⟨earlier,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨priorSupported,laterSupported⟩ := Set.mem_iUnion.mp present
  have same := DependentStageContinuation.predecessor (select get) state (child base dummy)
    earlier (before,some result) laterSupported
  change before = earlier at same
  rw [←same] at priorSupported laterSupported
  exact ⟨priorSupported,reached base get state dummy before result laterSupported⟩

/-- Earlier events retain the same final collision exclusion after extraction. -/
theorem earlier_safe_event_le (dummy : Digest) (prior : ProbComp Before) (event : Before → Prop) :
    Pr{let outcome ← (prior >>= finish base get state dummy)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base state outcome)] ≤
    Pr{let before ← prior}[event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (state before)] := by
  apply DependentStageContinuation.earlier_safe_event_le (select get) state (child base dummy)
    (fun _ result => result.2.2) (CheckpointCollision.Bad (AmbientMatrixSource.Shape H)) _ prior event
  intro selected initial result supported bad
  exact PaddedPublicZeroCheck.bad_persistent (base selected.1 selected.2) dummy initial result supported bad

/-- Actual extraction execution preserves the incoming audit, including rejection. -/
theorem audited (dummy : Digest) (enc : MerkleOracle.Encoding Input Digest (List F))
    (sameEncoding : ∀ before memory, (base before memory).encoding = enc)
    (before : Before) (outcome : Before × Option (Sigma (Child base)))
    (supported : outcome ∈ support (finish base get state dummy before))
    (valid : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (state before)) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (finalState base state outcome) := by
  apply DependentStageContinuation.preserves (select get) state (child base dummy)
    (fun _ result => result.2.2) (CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H)) _ before outcome supported valid
  intro selected initial result present incoming
  have validChild := PaddedPublicZeroCheck.audited_witness (base selected.1 selected.2) dummy initial
  rw [sameEncoding] at validChild
  exact validChild incoming result present

/-- Consume the complete predecessor audit without expanding its execution. -/
theorem audited_bind (dummy : Digest) (enc : MerkleOracle.Encoding Input Digest (List F))
    (sameEncoding : ∀ before memory, (base before memory).encoding = enc)
    (prior : ProbComp Before)
    (incoming : ∀ before ∈ support prior,
      CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (state before))
    (outcome : Before × Option (Sigma (Child base)))
    (supported : outcome ∈ support (prior >>= finish base get state dummy)) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (finalState base state outcome) := by
  rw [support_bind] at supported
  obtain ⟨before,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨earlier,later⟩ := Set.mem_iUnion.mp present
  exact audited base get state dummy enc sameEncoding before outcome later (incoming before earlier)

end
end FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
