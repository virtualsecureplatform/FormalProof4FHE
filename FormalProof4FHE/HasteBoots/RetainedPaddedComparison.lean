module
public import FormalProof4FHE.HasteBoots.PaddedReconstructionComparison
public import FormalProof4FHE.HasteBoots.DependentStageContinuation
@[expose] public section

/-! Append the native comparison to a retained optional reconstruction result.
The selected index contains the actual emitted roots and opening memory. No
source identity, replay law or child-security certificate is part of execution. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedComparison
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {F Before Cfg Input Response Memory CommitMemory : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {d b n : ℕ}
  {Helper Result : Memory → Type}

abbrev Reconstruction (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n) :=
  Sigma (fun memory => PaddedReconstructionComparison.Before (base memory))

variable (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
  (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (Helper memory) (Result memory) d)
  (get : Before → Option (Reconstruction base))
  (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))

/-- The verifier's actual accepted linear return selects the child index. -/
def select (before : Before) : Option (Reconstruction base) :=
  (get before).bind fun reconstructed =>
    if PaddedLinear.accepted (base reconstructed.1) reconstructed.2.2.1 then some reconstructed else none

abbrev Child (reconstructed : Reconstruction base) :=
  PackedPBSComparisonStage.Outcome (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))

/-- Sources and private memory come from the selected actual return. The
incoming full state is supplied by the enclosing execution without reset. -/
def child (dummy : Digest) (reconstructed : Reconstruction base)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) :=
  PackedPBSComparisonStage.witness (base reconstructed.1).encoding dummy
    (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))
    reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory initial

def finish (dummy : Digest) := DependentStageContinuation.program (select base get) state (child base comparison dummy)

def finalState (outcome : Before × Option (Sigma (Child base comparison))) :=
  DependentStageContinuation.finalState state (fun _ result => result.2.2.2) outcome

/-- A reached comparison retains the computed linear gate and the selected
reconstruction, together with support of the literal comparison execution. -/
theorem reached (dummy : Digest) (before : Before) (result : Sigma (Child base comparison))
    (supported : (before,some result) ∈ support (finish base comparison get state dummy before)) :
    get before = some result.1 ∧
    PaddedLinear.accepted (base result.1.1) result.1.2.2.1 = true ∧
    result.2 ∈ support (child base comparison dummy result.1 (state before)) := by
  have actual := DependentStageContinuation.reached (select base get) state (child base comparison dummy) before result supported
  refine ⟨?_,?_,actual.2⟩
  all_goals
    unfold select at actual
    cases found : get before with
    | none => simp only [found,Option.bind_none] at actual; cases actual.1
    | some reconstructed =>
      simp only [found,Option.bind_some] at actual
      split at actual
      · rename_i accepted
        have same := Option.some.inj actual.1
        cases same
        first | rfl | assumption
      · cases actual.1

/-- Earlier events cannot grow through the actual reached-or-skipped child. -/
theorem earlier_event_le (dummy : Digest) (prior : ProbComp Before) (event : Before → Prop) :
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[event outcome.1] ≤
      Pr{let before ← prior}[event before] :=
  DependentStageContinuation.earlier_event_le (select base get) state (child base comparison dummy) prior event

/-- Earlier safe events retain the same final Bad exclusion. The required
badness persistence follows from the actual comparison program. -/
theorem earlier_safe_event_le (dummy : Digest) (prior : ProbComp Before) (event : Before → Prop) :
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base comparison state outcome)] ≤
    Pr{let before ← prior}[event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (state before)] := by
  apply DependentStageContinuation.earlier_safe_event_le (select base get) state (child base comparison dummy)
    (fun _ result => result.2.2.2) (CheckpointCollision.Bad (AmbientMatrixSource.Shape H)) _ prior event
  intro reconstructed initial result supported bad
  exact PackedPBSComparisonStage.bad_persistent (base reconstructed.1).encoding dummy
    (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))
    reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory initial bad result supported

/-- Every reached comparison preserves the incoming audit; skipped paths
preserve it identically. No separately supplied child audit is required. -/
theorem audited (dummy : Digest) (enc : MerkleOracle.Encoding Input Digest (List F))
    (sameEncoding : ∀ memory, (base memory).encoding = enc)
    (before : Before) (outcome : Before × Option (Sigma (Child base comparison)))
    (supported : outcome ∈ support (finish base comparison get state dummy before))
    (valid : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (state before)) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (finalState base comparison state outcome) := by
  apply DependentStageContinuation.preserves (select base get) state (child base comparison dummy)
    (fun _ result => result.2.2.2) (CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H)) _ before outcome supported valid
  intro reconstructed initial result present incoming
  have bound := PackedPBSComparisonStage.audited (base reconstructed.1).encoding dummy
    (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))
    reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory initial
  rw [sameEncoding] at bound
  exact bound incoming result (by simpa only [child,sameEncoding] using present)

/-- The complete predecessor audit is consumed as one invariant function.
The bind is unpacked only at this generic interface, where the predecessor
experiment remains opaque and no earlier execution is expanded. -/
theorem audited_bind (dummy : Digest) (enc : MerkleOracle.Encoding Input Digest (List F))
    (sameEncoding : ∀ memory, (base memory).encoding = enc)
    (prior : ProbComp Before)
    (incoming : ∀ before ∈ support prior,
      CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (state before))
    (outcome : Before × Option (Sigma (Child base comparison)))
    (supported : outcome ∈ support (prior >>= finish base comparison get state dummy)) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (finalState base comparison state outcome) := by
  rw [support_bind] at supported
  obtain ⟨before,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨beforeSupported,laterSupported⟩ := Set.mem_iUnion.mp present
  exact audited base comparison get state dummy enc sameEncoding before outcome laterSupported (incoming before beforeSupported)

end
end FormalProof4FHE.HasteBoots.RetainedPaddedComparison
