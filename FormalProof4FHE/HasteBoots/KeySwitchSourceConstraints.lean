module
public import FormalProof4FHE.HasteBoots.PackedNTTBinding
public import FormalProof4FHE.HasteBoots.PackedKeySwitchStage
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! The final key-switch bindings follow from original coefficient sources,
canonical decomposition and the two-half NTT source relations. The public key
remains tied to its original trusted setup; no new key NTT subproof is invented. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchSourceConstraints
open NativeBlindRotation
noncomputable section
variable {q log c b levels d dc dw : ℕ} [Fact q.Prime]

/-- The two high polynomial rows are the original nonce and body halves. -/
def stage (length : 2^c*b = 2^log)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) (1+c) b) :
    PackedKeySwitchStage.Stage q log levels (1+c) b :=
  ⟨tables,fun half => PackedNTTBinding.address length (half,())⟩

omit [Fact q.Prime] in
theorem project_row (length : 2^c*b = 2^log)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) (1+c) b)
    (half : Bool) (factor : PBSHadamard.Factor levels) :
    CanonicalKeySwitch.project tables ((stage length tables).address half) factor =
      PackedNTTBinding.row length (tables factor) (half,()) := rfl

theorem digit_bindings (length : 2^c*b = 2^log) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registry : DecompositionBlindRotation.Registry q d dc dw)
    (registryAddress : Fin (2^log) → MatrixFold.Cube dc × Fin dw) (mask : Poly q (2^log))
    (input : DecompositionBlindRotation.project registry registryAddress DecompositionLinear.input = -mask)
    (linear : DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) registry)
    (lookup : ∀ index, RadixCanonicity.LookupAt q (2^bits) registry (registryAddress index).1 (registryAddress index).2)
    (coefficients : Fin levels → PackedNTTBinding.Table q (1+c) b)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) (1+c) b)
    (sources : ∀ half level, PackedNTTBinding.row length (coefficients level) (half,()) =
      DecompositionBlindRotation.project registry registryAddress (DecompositionLinear.digit (Fin.castLE covered level)))
    (transforms : ∀ level, PackedNTT.Relation length psi (NTTCompression.sourceRows c 1 (coefficients level))
      (NTTCompression.sourceRows c 1 (tables (.inl (level,false))))) :
    ∀ half level, BlindRotationNTT.transform log psi (digit bits level (-mask)) =
      CanonicalKeySwitch.project tables ((stage length tables).address half) (.inl (level,false)) := by
  intro half level
  have canonical := DecompositionBlindRotation.digit_of_constraints bits radixLarge radixSmall enough covered
    registry registryAddress (-mask) input linear lookup level
  rw [project_row,←canonical,←sources half level]
  exact PackedNTTBinding.transform_of_relation length psi primitive _ _ (transforms level) (half,())

theorem result_bindings (length : 2^c*b = 2^log) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (result : Cipher q (2^log))
    (coefficients : PackedNTTBinding.Table q (1+c) b)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) (1+c) b)
    (source : ∀ half, PackedNTTBinding.row length coefficients (half,()) = result half)
    (transform : PackedNTT.Relation length psi (NTTCompression.sourceRows c 1 coefficients)
      (NTTCompression.sourceRows c 1 (tables (.inr ())))) :
    ∀ half, BlindRotationNTT.transform log psi (result half) =
      CanonicalKeySwitch.project tables ((stage length tables).address half) (.inr ()) := by
  intro half
  rw [project_row,←source half]
  exact PackedNTTBinding.transform_of_relation length psi primitive _ _ transform (half,())

/-- No transform of a canonical digit or signed result is supplied as a
certificate: both follow from their original coefficient/NTT relations. -/
theorem holds_of_constraints (length : 2^c*b = 2^log) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registry : DecompositionBlindRotation.Registry q d dc dw)
    (registryAddress : Fin (2^log) → MatrixFold.Cube dc × Fin dw)
    (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log)) (result : Cipher q (2^log))
    (input : DecompositionBlindRotation.project registry registryAddress DecompositionLinear.input = -mask)
    (linear : DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) registry)
    (lookup : ∀ index, RadixCanonicity.LookupAt q (2^bits) registry (registryAddress index).1 (registryAddress index).2)
    (coefficients : Fin levels → PackedNTTBinding.Table q (1+c) b)
    (resultCoefficients : PackedNTTBinding.Table q (1+c) b)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) (1+c) b)
    (digitSources : ∀ half level, PackedNTTBinding.row length (coefficients level) (half,()) =
      DecompositionBlindRotation.project registry registryAddress (DecompositionLinear.digit (Fin.castLE covered level)))
    (digitTransforms : ∀ level, PackedNTT.Relation length psi (NTTCompression.sourceRows c 1 (coefficients level))
      (NTTCompression.sourceRows c 1 (tables (.inl (level,false)))))
    (resultSource : ∀ half, PackedNTTBinding.row length resultCoefficients (half,()) = result half)
    (resultTransform : PackedNTT.Relation length psi (NTTCompression.sourceRows c 1 resultCoefficients)
      (NTTCompression.sourceRows c 1 (tables (.inr ()))))
    (keys : ∀ half level, BlindRotationNTT.transform log psi (key level half) =
      PackedNTTBinding.row length (tables (.inl (level,true))) (half,()))
    (relation : PBSHadamard.Relation tables) :
    PackedKeySwitchStage.Holds psi bits key mask result (stage length tables) := by
  refine ⟨relation,?_,?_,?_⟩
  · exact digit_bindings length psi primitive bits radixLarge radixSmall enough covered registry registryAddress mask
      input linear lookup coefficients tables digitSources digitTransforms
  · intro half level
    exact keys half level
  · exact result_bindings length psi primitive result resultCoefficients tables resultSource resultTransform

end
end FormalProof4FHE.HasteBoots.KeySwitchSourceConstraints
