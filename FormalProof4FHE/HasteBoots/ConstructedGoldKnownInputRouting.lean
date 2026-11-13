module
public import FormalProof4FHE.HasteBoots.ConstructedGoldKeySwitchRouting
public import FormalProof4FHE.HasteBoots.DecodedKnownInput
@[expose] public section

/-! The fixed-height known-input verifier borrows the same final native source
allocation as reconstruction. Only public source geometry is installed here;
negative-mask semantics still follow from the actual accepted check. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldKnownInputRouting
open NativeFields (Goldilocks goldilocksModulus)
open NativeRootMessage (Digest)
open ConstructedGoldSourceDescriptor (Configuration heights)
open ConstructedGoldKeySwitchRouting (descriptor geometry)
noncomputable section
variable {Input Response Memory CommitMemory : Type} {c : ℕ}

abbrev Scheme (bundle : ClassicalGoldRoleBundle.Bundle) (radius : ℕ) :=
  AmbientKnownInput.Scheme Goldilocks Input Digest Configuration Response Memory CommitMemory 4 (1+c)
    (descriptor bundle radius).front (descriptor bundle radius).suffix (descriptor bundle radius).degree
    (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).queries.val
    (heights (descriptor bundle radius).tag)

/-- Install the final source allocation, retaining the raw known-input callback
work and memories. Logical padding is derived from the checked native fit. -/
def scheme (bundle : ClassicalGoldRoleBundle.Bundle)
    (fits : 1+c ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val) (radius : ℕ)
    (raw : Scheme (c := c) (Input := Input) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) bundle radius) :
    Scheme (c := c) (Input := Input) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) bundle radius :=
  {raw with
    tag := (descriptor bundle radius).tag
    domain := (descriptor bundle radius).domain
    padding := (descriptor bundle radius).front+(descriptor bundle radius).suffix-(1+c)
    dimensions := Nat.sub_add_cancel ((geometry bundle Unit (1+c) fits radius).fits ())}

theorem parameters [DecidableEq Input] [DecidableEq Digest]
    (bundle : ClassicalGoldRoleBundle.Bundle)
    (fits : 1+c ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val) (radius : ℕ)
    (raw : Scheme (c := c) (Input := Input) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) bundle radius)
    (small : 8 ≤ goldilocksModulus) (enc : MerkleOracle.Encoding Input Digest (List Goldilocks)) (root : Digest)
    (accumulator : NativeBlindRotation.Cipher goldilocksModulus (2^(c+2))) :
    DecodedKnownInput.parameters
      (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c 2).symm accumulator (scheme bundle fits radius raw))
      heights rfl (descriptor bundle radius).capacity radius = descriptor bundle radius := by
  rfl

end
end FormalProof4FHE.HasteBoots.ConstructedGoldKnownInputRouting
