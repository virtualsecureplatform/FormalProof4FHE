module
public import FormalProof4FHE.HasteBoots.AmbientAccumulator
public import FormalProof4FHE.HasteBoots.PackedNTTBinding
@[expose] public section

/-! Read the final public endpoint of the actual accumulator factory, in its
original coefficient/half order. A pure root borrower preserves the precise
incoming private memory that selected this context. -/
namespace FormalProof4FHE.HasteBoots.AccumulatorEndpoint
open OracleSpec OracleComp
open InteractiveAuthenticatedOpening
noncomputable section
variable {q log b c r : ℕ} [Fact q.Prime]

def value (length : 2^c*b = 2^log) (context : PackedAccumulatorOracle.Context (ZMod q) b c r) :
    NativeBlindRotation.Cipher q (2^log) :=
  fun half => PackedNTT.flatten length (fun position => context.final half position.1 position.2)

omit [Fact q.Prime] in
theorem at_address (length : 2^c*b = 2^log) (context : PackedAccumulatorOracle.Context (ZMod q) b c r)
    (half : Bool) (cell : MatrixFold.Cube c) (lane : Fin b) :
    value length context half (PackedNTT.address length (cell,lane)) = context.final half cell lane := by
  simp only [value,PackedNTT.flatten,Equiv.symm_apply_apply]

variable {Input Digest Cfg Response Memory : Type} [DecidableEq Input] [DecidableEq Digest]
  {front suffix m queries height : ℕ}
  [SampleableType Digest] [SampleableType (Fin b → ZMod q)]
  [SampleableType (TestMatrix (ZMod q) (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

/-- The accumulator's caller-root commitment emits its ACTUAL incoming memory;
this is derived from support, not assumed as a callback or endpoint certificate. -/
theorem emitted_memory
    (s : AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg Response Memory Memory b c r front suffix m queries height)
    (roots : Fin 7 → Digest) (memory : Memory) (heights : Cfg → ℕ) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (child : AmbientAccumulator.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := Memory) ×
      AmbientAccumulator.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response)
        (Memory := Memory) (b := b) (c := c) (r := r) (front := front) (queries := queries) (height := height))
    (supported : child ∈ support (AmbientAccumulator.witness heights {s with commit := pure (roots,memory)} dummy initial)) :
    child.1.1.2 = memory := by
  simp only [AmbientAccumulator.witness,MultiCommitmentPrefix.witness,simulateQ_pure,StateT.run_pure,
    pure_bind,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨last,_,same⟩ := supported
  subst child
  rfl

end
end FormalProof4FHE.HasteBoots.AccumulatorEndpoint
