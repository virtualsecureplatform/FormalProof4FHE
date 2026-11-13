module
public import FormalProof4FHE.HasteBoots.DecodedCipherRadixConstraints
public import FormalProof4FHE.HasteBoots.CanonicalKeySwitch
@[expose] public section

/-! The checked field, lookup, NTT and pointwise product equations identify
the canonical signed key-switch increment. Common-family specialization uses
only ciphertexts constructed from recorded owners, including the key sources. -/
namespace FormalProof4FHE.HasteBoots.DecodedKeySwitchIncrement
open scoped BigOperators
open NativeBlindRotation (Cipher Poly)
noncomputable section
variable {q d c lanes : ℕ} [Fact q.Prime]

def sources (registry : Fin (2*d+2) → Cipher q (2^(c+lanes)))
    (key : NativeKeySwitch.Key q (2^(c+lanes)) d) (result : Cipher q (2^(c+lanes))) :
    PBSHadamard.Factor d → Cipher q (2^(c+lanes))
  | .inl (level,false) => registry (DecompositionLinear.digit level)
  | .inl (level,true) => key level
  | .inr () => result

/-- All polynomial meanings on the coefficient side are derived from radix
constraints. NTT injectivity converts the checked evaluation product to the
native convolution of digits of the negative mask with the original key. -/
theorem increment_of_constraints
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d)
    (registry : Fin (2*d+2) → Cipher q (2^(c+lanes)))
    (linear : DecompositionLinear.Relation (2^bits : ZMod q) (DecodedCipherRadixConstraints.tables registry))
    (lookup : ∀ cell lane, RadixCanonicity.LookupAt q (2^bits) (DecodedCipherRadixConstraints.tables registry) cell lane)
    (mask : Poly q (2^(c+lanes))) (known : ∀ half, registry DecompositionLinear.input half = -mask)
    (key : NativeKeySwitch.Key q (2^(c+lanes)) d) (result : Cipher q (2^(c+lanes)))
    (evaluations : PBSHadamard.Factor d → Cipher q (2^(c+lanes)))
    (transformed : ∀ factor half, BlindRotationNTT.transform (c+lanes) psi (sources registry key result factor half) = evaluations factor half)
    (product : evaluations (.inr ()) = ∑ level : Fin d, evaluations (.inl (level,false)) * evaluations (.inl (level,true))) :
    result = CanonicalKeySwitch.increment bits key mask := by
  have digits := DecodedCipherRadixConstraints.native_digits_of_constraints bits radixLarge radixSmall enough
    registry linear lookup mask known
  funext half
  apply BlindRotationNTT.transform_injective (c+lanes) psi primitive
  rw [show BlindRotationNTT.transform (c+lanes) psi (result half) = evaluations (.inr ()) half from transformed (.inr ()) half,
    CanonicalKeySwitch.increment_transform psi primitive]
  have projected := congrFun product half
  simp only [Finset.sum_apply,Pi.mul_apply] at projected
  rw [projected]
  apply Finset.sum_congr rfl
  intro level _
  rw [←transformed (.inl (level,false)) half,←transformed (.inl (level,true)) half]
  change BlindRotationNTT.transform (c+lanes) psi (registry (DecompositionLinear.digit level) half) * _ = _
  rw [digits level half]
  rfl

/-- A wrong decoded increment exposes one of the actual semantic constraint
families needed for the stage-risk coverage argument. -/
theorem wrong_increment_coverage
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d)
    (registry : Fin (2*d+2) → Cipher q (2^(c+lanes)))
    (mask : Poly q (2^(c+lanes)))
    (key : NativeKeySwitch.Key q (2^(c+lanes)) d) (result : Cipher q (2^(c+lanes)))
    (evaluations : PBSHadamard.Factor d → Cipher q (2^(c+lanes)))
    (wrong : result ≠ CanonicalKeySwitch.increment bits key mask) :
    ¬DecompositionLinear.Relation (2^bits : ZMod q) (DecodedCipherRadixConstraints.tables registry) ∨
    (∃ cell lane, ¬RadixCanonicity.LookupAt q (2^bits) (DecodedCipherRadixConstraints.tables registry) cell lane) ∨
    (∃ half, registry DecompositionLinear.input half ≠ -mask) ∨
    (∃ factor half, BlindRotationNTT.transform (c+lanes) psi (sources registry key result factor half) ≠ evaluations factor half) ∨
    evaluations (.inr ()) ≠ ∑ level : Fin d, evaluations (.inl (level,false)) * evaluations (.inl (level,true)) := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (increment_of_constraints psi primitive bits radixLarge radixSmall enough registry
    absent.1 absent.2.1 mask absent.2.2.1 key result evaluations absent.2.2.2.1 absent.2.2.2.2)

/-- The extraction constraint completes the local key-switch output equation
once the checked original-source constraints hold. -/
theorem output_of_constraints
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d)
    (registry : Fin (2*d+2) → Cipher q (2^(c+lanes)))
    (linear : DecompositionLinear.Relation (2^bits : ZMod q) (DecodedCipherRadixConstraints.tables registry))
    (lookup : ∀ cell lane, RadixCanonicity.LookupAt q (2^bits) (DecodedCipherRadixConstraints.tables registry) cell lane)
    (mask : Poly q (2^(c+lanes))) (known : ∀ half, registry DecompositionLinear.input half = -mask)
    (key : NativeKeySwitch.Key q (2^(c+lanes)) d) (result : Cipher q (2^(c+lanes)))
    (evaluations : PBSHadamard.Factor d → Cipher q (2^(c+lanes)))
    (transformed : ∀ factor half, BlindRotationNTT.transform (c+lanes) psi (sources registry key result factor half) = evaluations factor half)
    (product : evaluations (.inr ()) = ∑ level : Fin d, evaluations (.inl (level,false)) * evaluations (.inl (level,true)))
    {dimension : ℕ} (shape : dimension ≤ 2^(c+lanes))
    (accumulator : Cipher q (2^(c+lanes))) (maskIsAccumulator : mask = accumulator false)
    (output : NativePublic.Ciphertext q dimension)
    (extracted : CanonicalKeySwitch.Extraction shape accumulator result output) :
    output = NativeKeySwitch.extract shape (CanonicalKeySwitch.switch bits key accumulator) := by
  have increment := increment_of_constraints psi primitive bits radixLarge radixSmall enough registry
    linear lookup mask known key result evaluations transformed product
  have correct := CanonicalKeySwitch.extract_of_constraints shape accumulator result output extracted
  rw [increment,maskIsAccumulator] at correct
  exact correct

variable {Cfg Input Digest Index : Type} {heights : Cfg → ℕ} [DecidableEq Digest]

/-- The family result is the canonical signed increment under the key decoded
from its retained key coefficient roots. Trusted setup association remains a
separate obligation; no independent private-source interpretation is supplied. -/
theorem increment_of_family_constraints
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (factors : Fin (2*d+2) → Index) (keys : Fin d → Index) (result : Index)
    (evaluations : PBSHadamard.Factor d → Index)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d)
    (linear : DecompositionLinear.Relation (2^bits : ZMod q)
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (factors factor)))
    (lookup : ∀ cell lane, RadixCanonicity.LookupAt q (2^bits)
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (factors factor)) cell lane)
    (mask : Poly q (2^(c+lanes)))
    (known : ∀ half, PackedCipherSource.familyCipher (c := c) world enc dummy (factors DecompositionLinear.input) half = -mask)
    (digitTransform : ∀ level half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) world enc dummy (factors (DecompositionLinear.digit level)) half) =
      PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,false))) half)
    (keyTransform : ∀ level half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) world enc dummy (keys level) half) =
      PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,true))) half)
    (resultTransform : ∀ half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) world enc dummy result half) =
      PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inr ())) half)
    (product : PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inr ())) =
      ∑ level : Fin d, PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,false))) *
        PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,true)))) :
    PackedCipherSource.familyCipher (c := c) world enc dummy result = CanonicalKeySwitch.increment bits
      (fun level => PackedCipherSource.familyCipher (c := c) world enc dummy (keys level)) mask := by
  apply increment_of_constraints psi primitive bits radixLarge radixSmall enough
    (fun factor => PackedCipherSource.familyCipher (c := c) world enc dummy (factors factor))
    (by rw [DecodedCipherRadixConstraints.family_tables]; exact linear)
    (by rw [DecodedCipherRadixConstraints.family_tables]; exact lookup)
    mask known _ _ (fun factor => PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations factor))
    ?_ product
  intro factor half
  rcases factor with ⟨level,side⟩ | ⟨⟩
  · cases side
    · exact digitTransform level half
    · exact keyTransform level half
  · exact resultTransform half

end
end FormalProof4FHE.HasteBoots.DecodedKeySwitchIncrement
