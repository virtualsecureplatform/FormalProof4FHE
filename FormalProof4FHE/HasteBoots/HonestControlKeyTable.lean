module
public import FormalProof4FHE.HasteBoots.HonestPaddedSource
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
public import FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
@[expose] public section

/-! Materialize honest control-key evaluations in the complete original NTT
layout, keeping every stored round and both ciphertext output halves. -/
namespace FormalProof4FHE.HasteBoots.HonestControlKeyTable
noncomputable section
variable {q cells lanes rows levels : ℕ} [Fact q.Prime]

abbrev Controls := Fin (2^rows) → NativeBlindRotation.Control q (2^(cells+lanes)) levels

/-- Native key slots have source half first, then low-to-high gadget limb. -/
def evaluations (psi : ZMod q) (controls : Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (slot : Fin (2*levels)) (position : Fin (2^rows)) : NativeBlindRotation.Cipher q (2^(cells+lanes)) :=
  let component := (PBSHadamardBlindRotation.digitEquiv levels).symm slot
  fun half => BlindRotationNTT.transform (cells+lanes) psi (controls position component.1 component.2 half)

/-- Logical setup source in the same round-low, output-half-high NTT layout. -/
def logical (psi : ZMod q) (controls : Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (slot : Fin (2*levels)) : MatrixFold.Cube ((rows+1)+cells) → Fin (2^lanes) → ZMod q :=
  DecodedAccumulatorRows.nttView (PackedAccumulatorTrace.pack (RingHom.id (ZMod q)) (evaluations psi controls slot))

variable {Cfg : Type} {H : Cfg → ℕ}

/-- Actual physical buffers, including deterministic zero padding beyond the
full logical source; the Merkle payloads are built from these field values. -/
def table (parameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
    (psi : ZMod q) (controls : Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (slot : Fin (2*levels)) : RecordedPaddedSource.PhysicalMatrix (parameters slot) :=
  HonestPaddedSource.physical (front := (parameters slot).front) (suffix := (parameters slot).suffix) (logical psi controls slot)

/-- Honest padding preserves every original logical scalar address. -/
theorem logical_table (parameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
    (psi : ZMod q) (controls : Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (slot : Fin (2*levels)) (fits : (rows+1)+cells ≤ (parameters slot).front+(parameters slot).suffix) :
    PaddedSourceAddress.logical ((rows+1)+cells) (table parameters psi controls slot) = logical psi controls slot :=
  HonestPaddedSource.logical_physical _ fits

/-- Each committed evaluation polynomial is constructed from the actual
coefficient control row, rather than supplied as a transform certificate. -/
theorem polynomial (psi : ZMod q)
    (controls : Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (position : Fin (2^rows)) (half source : Bool) (level : Fin levels) :
    PackedMonomialRotation.polynomial (logical psi controls (PBSHadamardBlindRotation.digitIndex (source,level))) position half =
      BlindRotationNTT.transform (cells+lanes) psi (controls position source level half) := by
  rw [logical,DecodedAccumulatorRows.polynomial_nttView,DecodedAccumulatorRows.decode_pack]
  have component := (PBSHadamardBlindRotation.digitEquiv levels).symm_apply_apply (source,level)
  change (PBSHadamardBlindRotation.digitEquiv levels).symm (PBSHadamardBlindRotation.digitIndex (source,level)) = (source,level) at component
  simp only [evaluations,component]

end
end FormalProof4FHE.HasteBoots.HonestControlKeyTable
