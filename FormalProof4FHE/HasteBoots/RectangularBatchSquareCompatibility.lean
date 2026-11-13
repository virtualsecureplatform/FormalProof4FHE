module
public import FormalProof4FHE.HasteBoots.RectangularBatchVerifier
public import FormalProof4FHE.HasteBoots.NativeBatchVerifier
@[expose] public section

/-! Exact square specialization preserves the complete oracle program,
including preparation, response work, coverage rejection and worker scheduling. -/
namespace FormalProof4FHE.HasteBoots.RectangularBatchSquareCompatibility
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Input Digest Cfg Response Memory : Type}
  {b front suffix claims m queries height : ℕ}

def ofSquare (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height) :
    RectangularBatchVerifier.Protocol F Input Digest Cfg Response Memory b b front suffix claims m queries height :=
  ⟨p.encoding,p.domain,p.root,p.query,p.values,p.testResponse,p.groupResponse,p.prepare,p.respond,
    p.receiveColumns,p.choose,p.fuel⟩

variable [Field F] [DecidableEq F] [DecidableEq Digest]

theorem next_eq (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (memory : Memory) (sample : SampleData F Response (2^front) b height queries) :
    RectangularBatchVerifier.next (ofSquare p) memory sample = NativeBatchVerifier.next p memory sample := rfl

omit [DecidableEq Digest] in
theorem checks_eq (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height) :
    RectangularBatchVerifier.checks (ofSquare p) = NativeBatchVerifier.checks p := rfl

variable [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

theorem sampledStep_eq (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (memory : Memory) :
    RectangularBatchVerifier.sampledStep (ofSquare p) memory = NativeBatchVerifier.sampledStep p memory := rfl

theorem step_eq (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (memory : Memory) :
    RectangularBatchVerifier.step (ofSquare p) memory = NativeBatchVerifier.step p memory := rfl

end
end FormalProof4FHE.HasteBoots.RectangularBatchSquareCompatibility
