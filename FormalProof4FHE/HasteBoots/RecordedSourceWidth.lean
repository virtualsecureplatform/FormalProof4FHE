module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.DecompositionLinear
@[expose] public section

/-! Transport only a public equality of scalar widths. Physical descriptors,
root owners, logs and lookup configurations are preserved. -/
namespace FormalProof4FHE.HasteBoots.RecordedSourceWidth
noncomputable section
variable {F Cfg Input Digest Index : Type} [Field F] {heights : Cfg → ℕ} {b other n d : ℕ}

def family (width : b = other)
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b) :
    RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights other := width ▸ world

/-- Width transport leaves every caller root unchanged. -/
theorem roots (width : b = other)
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b) :
    (family width world).roots = world.roots := by
  subst other
  rfl

/-- Recording receipts survive the public type transport verbatim. -/
theorem recorded (width : b = other)
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (present : RecordedPaddedSourceFamily.Recorded world state) :
    RecordedPaddedSourceFamily.Recorded (family width world) state := by
  subst other
  exact present

variable [DecidableEq F] [DecidableEq Digest]

/-- The transported lane reads exactly the same decoded scalar. -/
theorem logical (width : b = other)
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (index : Index) (cell : MatrixFold.Cube n) (lane : Fin b) :
    RecordedPaddedSourceFamily.logical (family width world) enc dummy n index cell (Fin.cast width lane) =
      RecordedPaddedSourceFamily.logical world enc dummy n index cell lane := by
  subst other
  rfl

/-- Native reconstruction and endpoint-borrow equations transport without
assuming any new source values or re-running a verifier. -/
theorem relation {q : ℕ} [Fact q.Prime] (width : b = other)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (factors : Fin (2*d+2) → Index) (radix : ZMod q)
    (holds : DecompositionLinear.Relation radix
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy n (factors factor))) :
    DecompositionLinear.Relation radix
      (fun factor => RecordedPaddedSourceFamily.logical (family width world) enc dummy n (factors factor)) := by
  subst other
  exact holds

end
end FormalProof4FHE.HasteBoots.RecordedSourceWidth
