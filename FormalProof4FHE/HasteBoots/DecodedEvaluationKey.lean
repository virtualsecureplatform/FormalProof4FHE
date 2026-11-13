module
public import FormalProof4FHE.HasteBoots.DecodedKeySwitchIncrement
@[expose] public section

/-! Native key references contain evaluation roots. Invertibility of the NTT
constructs their coefficient key without an additional coefficient commitment.
Honest setup association follows once its evaluation identity is established. -/
namespace FormalProof4FHE.HasteBoots.DecodedEvaluationKey
open NativeBlindRotation (Poly Cipher)
noncomputable section
variable {q levels : ℕ} [Fact q.Prime]

def transformEquiv (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) :
    Poly q (2^log) ≃ Poly q (2^log) :=
  Equiv.ofBijective (BlindRotationNTT.transform log psi)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨BlindRotationNTT.transform_injective log psi primitive,rfl⟩)

def inverse (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) :
    Poly q (2^log) → Poly q (2^log) := (transformEquiv log psi primitive).symm

theorem transform_inverse (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (values : Poly q (2^log)) :
    BlindRotationNTT.transform log psi (inverse log psi primitive values) = values :=
  (transformEquiv log psi primitive).apply_symm_apply values

theorem inverse_transform (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (values : Poly q (2^log)) :
    inverse log psi primitive (BlindRotationNTT.transform log psi values) = values :=
  (transformEquiv log psi primitive).symm_apply_apply values

def key (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (evaluations : Fin levels → Cipher q (2^log)) : NativeKeySwitch.Key q (2^log) levels :=
  fun level half => inverse log psi primitive (evaluations level half)

theorem key_transform (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (evaluations : Fin levels → Cipher q (2^log)) (level : Fin levels) (half : Bool) :
    BlindRotationNTT.transform log psi (key log psi primitive evaluations level half) = evaluations level half :=
  transform_inverse log psi primitive _

/-- An actual honest-setup transform identity identifies the constructed key;
there is no extra root or private-source equality certificate in its definition. -/
theorem key_eq_of_setup (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (evaluations : Fin levels → Cipher q (2^log)) (original : NativeKeySwitch.Key q (2^log) levels)
    (transformed : ∀ level half, BlindRotationNTT.transform log psi (original level half) = evaluations level half) :
    key log psi primitive evaluations = original := by
  funext level half
  unfold key
  rw [←transformed level half, inverse_transform]

variable {c lanes : ℕ}

theorem increment_of_constraints
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^levels)
    (registry : Fin (2*levels+2) → Cipher q (2^(c+lanes)))
    (linear : DecompositionLinear.Relation (2^bits : ZMod q) (DecodedCipherRadixConstraints.tables registry))
    (lookup : ∀ cell lane, RadixCanonicity.LookupAt q (2^bits) (DecodedCipherRadixConstraints.tables registry) cell lane)
    (mask : Poly q (2^(c+lanes))) (known : ∀ half, registry DecompositionLinear.input half = -mask)
    (result : Cipher q (2^(c+lanes))) (evaluations : PBSHadamard.Factor levels → Cipher q (2^(c+lanes)))
    (digitTransform : ∀ level half, BlindRotationNTT.transform (c+lanes) psi
      (registry (DecompositionLinear.digit level) half) = evaluations (.inl (level,false)) half)
    (resultTransform : ∀ half, BlindRotationNTT.transform (c+lanes) psi (result half) = evaluations (.inr ()) half)
    (product : evaluations (.inr ()) = ∑ level : Fin levels,
      evaluations (.inl (level,false)) * evaluations (.inl (level,true))) :
    result = CanonicalKeySwitch.increment bits
      (key (c+lanes) psi primitive (fun level => evaluations (.inl (level,true)))) mask := by
  apply DecodedKeySwitchIncrement.increment_of_constraints psi primitive bits radixLarge radixSmall enough
    registry linear lookup mask known _ result evaluations ?_ product
  intro factor half
  rcases factor with ⟨level,side⟩ | ⟨⟩
  · cases side
    · exact digitTransform level half
    · exact key_transform (c+lanes) psi primitive (fun level => evaluations (.inl (level,true))) level half
  · exact resultTransform half

variable {Cfg Input Digest Index : Type} {heights : Cfg → ℕ} [DecidableEq Digest]

/-- Coefficient keys are constructed from the actual evaluation-key slots;
no coefficient-key source owner or checked key-NTT stage is required. -/
theorem family_increment_of_constraints
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (factors : Fin (2*levels+2) → Index) (result : Index) (evaluations : PBSHadamard.Factor levels → Index)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^levels)
    (linear : DecompositionLinear.Relation (2^bits : ZMod q)
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (factors factor)))
    (lookup : ∀ cell lane, RadixCanonicity.LookupAt q (2^bits)
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (factors factor)) cell lane)
    (mask : Poly q (2^(c+lanes)))
    (known : ∀ half, PackedCipherSource.familyCipher (c := c) world enc dummy (factors DecompositionLinear.input) half = -mask)
    (digitTransform : ∀ level half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) world enc dummy (factors (DecompositionLinear.digit level)) half) =
      PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,false))) half)
    (resultTransform : ∀ half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) world enc dummy result half) =
      PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inr ())) half)
    (product : PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inr ())) =
      ∑ level : Fin levels, PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,false))) *
        PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,true)))) :
    PackedCipherSource.familyCipher (c := c) world enc dummy result = CanonicalKeySwitch.increment bits
      (key (c+lanes) psi primitive
        (fun level => PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations (.inl (level,true))))) mask := by
  exact increment_of_constraints psi primitive bits radixLarge radixSmall enough
    (fun factor => PackedCipherSource.familyCipher (c := c) world enc dummy (factors factor))
    (by rw [DecodedCipherRadixConstraints.family_tables]; exact linear)
    (by rw [DecodedCipherRadixConstraints.family_tables]; exact lookup) mask known
    (PackedCipherSource.familyCipher (c := c) world enc dummy result)
    (fun factor => PackedCipherSource.familyCipher (c := c) world enc dummy (evaluations factor))
    digitTransform resultTransform product

end
end FormalProof4FHE.HasteBoots.DecodedEvaluationKey
