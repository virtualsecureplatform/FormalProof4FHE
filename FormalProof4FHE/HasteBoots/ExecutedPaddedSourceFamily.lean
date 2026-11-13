module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
@[expose] public section

/-! Product and reconstruction families constructed from their actual prefix
snapshots and physical decoders. Execution proves recording; private source
values and availability certificates are not inputs to the constructors. -/
namespace FormalProof4FHE.HasteBoots.ExecutedPaddedSourceFamily
open OracleSpec OracleComp BinaryTree
noncomputable section
section Zero
variable {F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] {heights : Cfg → ℕ} {b n : ℕ}
variable (s : PaddedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory heights b n)

/-- Each private factor keeps its actual decoder and the fresh prefix owner. -/
def zeroFamily
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Factor → ℕ)
    (first : PaddedZeroCheck.Prefix (Factor := Factor) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights) :
    RecordedPaddedSourceFamily.Family F Cfg Input Digest Factor heights b where
  parameters := PaddedStageSourceInterpretation.zeroParameters s capacity radius
  roots := first.1.1
  owners := HeterogeneousSingleOpening.snapshots heights s.tag first
  ownerRoots := fun _ => rfl

theorem zero_roots
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Factor → ℕ)
    (first : PaddedZeroCheck.Prefix (Factor := Factor) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights) :
    (zeroFamily s capacity radius first).roots = first.1.1 := rfl

variable [DecidableEq F] [DecidableEq Digest]
/-- The literal original product sources are precisely this constructed family. -/
theorem zero_logical (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Factor → ℕ)
    (first : PaddedZeroCheck.Prefix (Factor := Factor) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights)
    (factor : Factor) :
    PaddedZeroCheck.originalSources s dummy capacity radius
      (HeterogeneousSingleOpening.snapshots heights s.tag first) factor =
      RecordedPaddedSourceFamily.logical (zeroFamily s capacity radius first) s.encoding dummy (n+1) factor :=
  PaddedStageSourceInterpretation.zero_original s dummy capacity radius _ factor

variable [Fintype Term] [DecidableEq Input] [SampleableType Digest]
  [SampleableType (Fin b → F)] [SampleableType (PackedZeroReduction.Points F n b)]
  [SampleableType (Fin b → Fin b → F)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

/-- All constructed anchors are recorded by the actual supported stage. -/
theorem zero_recorded_witness (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Factor → ℕ)
    (complete : ∀ factor, factor ∈ s.factors)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : PaddedZeroCheck.Prefix (Factor := Factor) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights × PaddedZeroCheck.RunResult s)
    (supported : outcome ∈ support (PaddedZeroCheck.witness s dummy initial)) :
    RecordedPaddedSourceFamily.Recorded (zeroFamily s capacity radius outcome.1) outcome.2.2 := by
  intro factor
  exact PaddedZeroCheck.fresh_recorded s dummy initial outcome supported complete factor
end Zero

section Linear
variable {F Input Digest Cfg Response Memory CommitMemory : Type} [Field F]
  {heights : Cfg → ℕ} {b n count : ℕ}
variable (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory heights count b n)

/-- Input, digits and newly emitted borrows keep their actual prefix owners. -/
def linearFamily
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (first : PaddedLinear.Prefix (count := count) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights) :
    RecordedPaddedSourceFamily.Family F Cfg Input Digest (Fin count) heights b where
  parameters := PaddedStageSourceInterpretation.linearParameters s capacity radius
  roots := first.1.1
  owners := HeterogeneousBatchOpening.snapshots heights s.tag first
  ownerRoots := fun _ => rfl

theorem linear_roots
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (first : PaddedLinear.Prefix (count := count) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights) :
    (linearFamily s capacity radius first).roots = first.1.1 := rfl

variable [DecidableEq F] [DecidableEq Digest]
/-- The literal original reconstruction tables are this same constructed family. -/
theorem linear_logical (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (first : PaddedLinear.Prefix (count := count) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights)
    (factor : Fin count) :
    PaddedLinear.originalSources s dummy capacity radius
      (HeterogeneousBatchOpening.snapshots heights s.tag first) factor =
      RecordedPaddedSourceFamily.logical (linearFamily s capacity radius first) s.encoding dummy n factor :=
  PaddedStageSourceInterpretation.linear_original s dummy capacity radius _ factor

variable [Fintype F] [DecidableEq Input] [SampleableType Digest] [SampleableType (Fin b → F)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

/-- The real reconstruction records every input/digit/borrow anchor, including
its newly committed borrows and including later rejected paths. -/
theorem linear_recorded_witness (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : PaddedLinear.Prefix (count := count) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights × PaddedLinear.RunResult s)
    (supported : outcome ∈ support (PaddedLinear.witness s dummy initial)) :
    RecordedPaddedSourceFamily.Recorded (linearFamily s capacity radius outcome.1) outcome.2.2 := by
  intro factor
  exact PaddedLinear.fresh_recorded s dummy initial outcome supported factor
end Linear
end
end FormalProof4FHE.HasteBoots.ExecutedPaddedSourceFamily
