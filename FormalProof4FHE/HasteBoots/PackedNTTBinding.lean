module
public import FormalProof4FHE.HasteBoots.PackedNTT
public import FormalProof4FHE.HasteBoots.BlindRotationNTT
public import FormalProof4FHE.HasteBoots.AccumulatorQuerySplit
@[expose] public section

/-! Original NTT source rows give the coefficient-domain transform bindings
used by PBS multiplication. Coefficients remain low and polynomial rows high;
all lanes and the native bit-reversed output order are retained. -/
namespace FormalProof4FHE.HasteBoots.PackedNTTBinding
noncomputable section
variable {q log c b r : ℕ} [Fact q.Prime]

abbrev Table (q cells width : ℕ) := MatrixFold.Cube cells → Fin width → ZMod q

def row (length : 2^c*b = 2^log) (table : Table q (r+c) b) (index : MatrixFold.Cube r) :
    NativeBlindRotation.Poly q (2^log) :=
  PackedNTT.flatten length (NTTCompression.sourceRows c r table index)

/-- Every polynomial coefficient is read at its original full source address. -/
def address (length : 2^c*b = 2^log) (index : MatrixFold.Cube r) (coefficient : Fin (2^log)) :
    MatrixFold.Cube (r+c) × Fin b :=
  let position := (PackedNTT.address length).symm coefficient
  (NTTSourceQuery.join c r position.1 index,position.2)

omit [Fact q.Prime] in
theorem row_address (length : 2^c*b = 2^log) (table : Table q (r+c) b)
    (index : MatrixFold.Cube r) (coefficient : Fin (2^log)) :
    row length table index coefficient = table (address length index coefficient).1 (address length index coefficient).2 := rfl

/-- The authenticated row relation and the PBS transform use the same odd,
bit-reversed root powers; no additional source-transform equality is assumed. -/
theorem transform_of_relation (length : 2^c*b = 2^log) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (coefficients evaluations : Table q (r+c) b)
    (relation : PackedNTT.Relation length psi (NTTCompression.sourceRows c r coefficients)
      (NTTCompression.sourceRows c r evaluations)) (index : MatrixFold.Cube r) :
    BlindRotationNTT.transform log psi (row length coefficients index) = row length evaluations index := by
  have equal := congrArg (PackedNTT.flatten length) (relation index)
  simpa only [PackedNTT.butterfly,PackedNTT.flatten_unflatten,
    NTTButterfly.negacyclic_evaluation log psi primitive,row,BlindRotationNTT.transform] using equal

theorem relation_iff_transforms (length : 2^c*b = 2^log) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (coefficients evaluations : Table q (r+c) b) :
    PackedNTT.Relation length psi (NTTCompression.sourceRows c r coefficients)
      (NTTCompression.sourceRows c r evaluations) ↔
    ∀ index, BlindRotationNTT.transform log psi (row length coefficients index) = row length evaluations index := by
  constructor
  · exact fun relation index => transform_of_relation length psi primitive coefficients evaluations relation index
  · intro transformed index
    have equal := congrArg (PackedNTT.unflatten length) (transformed index)
    simpa only [row,BlindRotationNTT.transform,←NTTButterfly.negacyclic_evaluation log psi primitive,
      PackedNTT.unflatten_flatten,PackedNTT.butterfly] using equal

/-- Pack independently supplied polynomial rows into the original source
layout. This constructor is useful for checking honest source fixtures. -/
def pack (length : 2^c*b = 2^log) (polynomials : MatrixFold.Cube r → NativeBlindRotation.Poly q (2^log)) : Table q (r+c) b :=
  fun cell lane =>
    let split := AccumulatorQuerySplit.cubeSplit c r cell
    polynomials split.2 (PackedNTT.address length (split.1,lane))

theorem split_join (coefficient : MatrixFold.Cube c) (index : MatrixFold.Cube r) :
    AccumulatorQuerySplit.cubeSplit c r (NTTSourceQuery.join c r coefficient index) = (coefficient,index) := by
  induction c with
  | zero => cases coefficient; rfl
  | succ c ih =>
    rcases coefficient with ⟨bit,tail⟩
    change ((bit,(AccumulatorQuerySplit.cubeSplit c r (NTTSourceQuery.join c r tail index)).1),
      (AccumulatorQuerySplit.cubeSplit c r (NTTSourceQuery.join c r tail index)).2) = _
    rw [ih]
    rfl

omit [Fact q.Prime] in
theorem row_pack (length : 2^c*b = 2^log)
    (polynomials : MatrixFold.Cube r → NativeBlindRotation.Poly q (2^log)) (index : MatrixFold.Cube r) :
    row length (pack length polynomials) index = polynomials index := by
  funext coefficient
  simp only [row,PackedNTT.flatten,NTTCompression.sourceRows,pack,split_join,
    Prod.mk.eta,Equiv.apply_symm_apply]

end
end FormalProof4FHE.HasteBoots.PackedNTTBinding
