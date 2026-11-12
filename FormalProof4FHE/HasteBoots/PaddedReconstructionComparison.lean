module
public import FormalProof4FHE.HasteBoots.PaddedLinear
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonStage
@[expose] public section

/-! Canonical shared comparison starts only on the actual accepted native
reconstruction return. Sources omit only the input, preserve each original
context, and reuse the actual opening memory and complete incoming history.
This local composition does not yet append comparison to the full PBS prefix. -/
namespace FormalProof4FHE.HasteBoots.PaddedReconstructionComparison
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {F Cfg Input Response Memory CommitMemory Helper Result : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {d b n : ℕ}

abbrev Before (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n) :=
  PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) H ×
    PaddedLinear.RunResult s

/-- Original source contexts come from the actual reconstruction registry;
helper work and the shared comparison continuation are retained. -/
abbrev stage (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d) :=
  {comparison with
    heights := H
    sourceTag := fun source => s.tag (PackedPBSComparisonReferences.linearSlot source)}

variable [SampleableType Digest]

def continuation (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d) (dummy : Digest)
    (before : Before s) : ProbComp (Option (PackedPBSComparisonStage.Outcome (stage s comparison))) :=
  if PaddedLinear.accepted s before.2.1 then
    some <$> PackedPBSComparisonStage.witness s.encoding dummy (stage s comparison)
      before.1.1.1 before.2.1.2.memory before.2.2
  else pure none

/-- A reached comparison is the real child execution at the returned linear
opening state, with the accepted linear guard computed by the verifier. -/
theorem reached (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d) (dummy : Digest)
    (before : Before s) (outcome : PackedPBSComparisonStage.Outcome (stage s comparison))
    (supported : some outcome ∈ support (continuation s comparison dummy before)) :
    PaddedLinear.accepted s before.2.1 = true ∧
      outcome ∈ support (PackedPBSComparisonStage.witness s.encoding dummy (stage s comparison)
        before.1.1.1 before.2.1.2.memory before.2.2) := by
  unfold continuation at supported
  split at supported
  · rename_i accepted
    refine ⟨accepted,?_⟩
    rw [support_map] at supported
    obtain ⟨actual,actualSupported,same⟩ := supported
    exact Option.some.inj same ▸ actualSupported
  · simp only [support_pure,Set.mem_singleton_iff] at supported
    cases supported

/-- Source roots, opening memory and the pre-helper history are literally the
reconstruction's returned data, including repeated root aliases. -/
theorem sources (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d) (dummy : Digest)
    (before : Before s) (outcome : PackedPBSComparisonStage.Outcome (stage s comparison))
    (supported : some outcome ∈ support (continuation s comparison dummy before)) :
    outcome.1.1 = PackedPBSComparisonStage.sources before.1.1.1 before.2.1.2.memory ∧
      outcome.1.2 = before.2.2 :=
  PackedPBSComparisonStage.source_eq s.encoding dummy (stage s comparison)
    before.1.1.1 before.2.1.2.memory before.2.2 outcome (reached s comparison dummy before outcome supported).2

omit [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
/-- Every comparison slot uses the original reconstruction's source context. -/
theorem source_context (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d) (source : Fin (2*d+1)) :
    (stage s comparison).sourceTag source = s.tag (PackedPBSComparisonReferences.linearSlot source) := rfl

/-- The actual linear audit is retained by every reached comparison, without
requiring a separately supplied child audit. -/
theorem audited (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d) (dummy : Digest)
    (before : Before s) (valid : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape H) before.2.2)
    (outcome : PackedPBSComparisonStage.Outcome (stage s comparison))
    (supported : some outcome ∈ support (continuation s comparison dummy before)) :
    CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape H) outcome.2.2.2 :=
  PackedPBSComparisonStage.audited s.encoding dummy (stage s comparison)
    before.1.1.1 before.2.1.2.memory before.2.2 valid outcome (reached s comparison dummy before outcome supported).2

end
end FormalProof4FHE.HasteBoots.PaddedReconstructionComparison
