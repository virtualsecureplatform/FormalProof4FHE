module
public import FormalProof4FHE.HasteBoots.ConstructedGoldRoleSourceDescriptors
public import FormalProof4FHE.HasteBoots.ConstructedKeySwitchSourceParameters
@[expose] public section

/-! Final key-switch verifier geometries borrow one native four-lane source
allocation. Their different logical arities cannot change decoder metadata.
These constructors discharge source-routing equalities without decoded values. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldKeySwitchRouting
open NativeFields (Goldilocks goldilocksModulus)
open NativeRootMessage (Digest)
open ConstructedGoldSourceDescriptor (Configuration heights)
noncomputable section
variable {Input Response Memory CommitMemory : Type} {c d : ℕ}

abbrev descriptor (bundle : ClassicalGoldRoleBundle.Bundle) (radius : ℕ) :=
  ConstructedGoldRoleSourceDescriptors.descriptor bundle .finalCoefficients (Or.inr rfl) radius

def geometry (bundle : ClassicalGoldRoleBundle.Bundle) (Index : Type) (logical : ℕ)
    (fits : logical ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val)
    (radius : ℕ) : PaddedSourceGeometry.Geometry Goldilocks Configuration Index heights 4 logical :=
  ConstructedGoldRoleSourceDescriptors.geometry bundle (fun _ : Index => .finalCoefficients)
    (fun _ => Or.inr rfl) logical (fun _ => fits) radius

theorem geometry_parameters (bundle : ClassicalGoldRoleBundle.Bundle) (Index : Type) (logical : ℕ)
    (fits : logical ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val)
    (radius : ℕ) (index : Index) :
    (geometry bundle Index logical fits radius).parameters index = descriptor bundle radius := rfl

/-- The allocation is the native descriptor for every original final role,
including inputs, keys and borrows, at the same fixed decoder radius. -/
theorem geometry_matches_final_role (bundle : ClassicalGoldRoleBundle.Bundle) (Index : Type) (logical : ℕ)
    (fits : logical ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val)
    (radius : ℕ) (index : Index) (stage : ClassicalGoldRoleBundle.Stage)
    (finalRole : ClassicalGoldRoleBundle.roleIndex stage = 2) :
    (geometry bundle Index logical fits radius).parameters index =
      ConstructedGoldRoleSourceDescriptors.descriptor bundle stage (Or.inr finalRole) radius :=
  ConstructedGoldRoleSourceDescriptors.descriptor_eq_of_role bundle .finalCoefficients stage
    (Or.inr rfl) (Or.inr finalRole) finalRole.symm radius

section NTT
variable (bundle : ClassicalGoldRoleBundle.Bundle)
    (fits : 1+c ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val) (radius : ℕ)
    (raw : PaddedNTT.Scheme Goldilocks Input Digest Configuration Response Memory CommitMemory heights 4 c 1 4)
    (build : ((Bool → Digest) × CommitMemory) → AuthenticatedNTT.Packet Goldilocks Memory c 4 1 4 → (side : Bool) →
      NativeBatchVerifier.Protocol Goldilocks Input Digest Configuration Response Memory 4
        (descriptor bundle radius).front (descriptor bundle radius).suffix 4
        (descriptor bundle radius).degree
        ((geometry bundle Bool (1+c) fits radius).queries side) (heights (descriptor bundle radius).tag))

/-- Native source geometry is installed before the NTT's typed arithmetic and
caller-root constructor; response work and private memory remain in `raw`. -/
def ntt := PaddedSourceGeometry.ntt raw (geometry bundle Bool (1+c) fits radius) build

theorem ntt_parameters (enc : MerkleOracle.Encoding Input Digest (List Goldilocks)) (roots : Bool → Digest)
    (small : 8 ≤ goldilocksModulus) (psi : Goldilocks) (primitive : IsPrimitiveRoot psi (2^(c+3))) (side : Bool) :
    PaddedStageSourceInterpretation.nttParameters
      (PaddedNTT.nativeScheme (ntt bundle fits radius raw build) enc roots goldilocksModulus small
        (Nat.pow_add 2 c 2).symm psi primitive)
      (fun _ => (descriptor bundle radius).capacity) (fun _ => radius) side = descriptor bundle radius := rfl
end NTT

section Reconstruction
variable (bundle : ClassicalGoldRoleBundle.Bundle)
    (fits : 1+c ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val) (radius : ℕ)
    (raw : PaddedLinear.Scheme Goldilocks Input Digest Configuration Response Memory CommitMemory heights (2*d+2) 4 (1+c))
    (build : ((Fin (2*d+2) → Digest) × CommitMemory) → PackedLinearOracle.Packet Goldilocks (Fin (2*d+2)) Memory 4 (1+c) →
      (factor : Fin (2*d+2)) → SingletonOpening.Protocol Goldilocks Input Digest Configuration Response Memory 4
        (descriptor bundle radius).front (descriptor bundle radius).suffix (descriptor bundle radius).degree
        ((geometry bundle (Fin (2*d+2)) (1+c) fits radius).queries factor) (heights (descriptor bundle radius).tag))

def reconstruction := PaddedSourceGeometry.linear raw (geometry bundle (Fin (2*d+2)) (1+c) fits radius) build

theorem reconstruction_parameters [DecidableEq Input] [DecidableEq Digest]
    (enc : MerkleOracle.Encoding Input Digest (List Goldilocks)) (input : NativeGoldParameterStore.Reference)
    (family : PackedPBSOriginalReferences.Family d) (small : 8 ≤ goldilocksModulus) (radix : Goldilocks) (factor : Fin (2*d+2)) :
    PaddedStageSourceInterpretation.linearParameters
      (KeySwitchPaddedReconstruction.stage (reconstruction bundle fits radius raw build) enc input family small radix)
      (fun _ => (descriptor bundle radius).capacity) (fun _ => radius) factor = descriptor bundle radius := rfl
end Reconstruction

section Product
variable (bundle : ClassicalGoldRoleBundle.Bundle)
    (fits : c+1 ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val) (radius : ℕ)
    (raw : KeySwitchPaddedProduct.Scheme (q := goldilocksModulus) (d := d) (b := 4) (n := c)
      (Input := Input) (Cfg := Configuration) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := heights))
    (build : ((PBSHadamard.Factor d → Digest) × CommitMemory) → PreparedZeroTerminal.Packet Goldilocks (PBSHadamard.Factor d) Memory 4 c →
      (factor : PBSHadamard.Factor d) → HeterogeneousSingleOpening.Protocol Goldilocks Input Digest Configuration Response Memory 4 heights
        (fun _ => (descriptor bundle radius).tag) (PaddedSourceGeometry.code (geometry bundle (PBSHadamard.Factor d) (c+1) fits radius)) factor)

def product := PaddedSourceGeometry.zero raw (geometry bundle (PBSHadamard.Factor d) (c+1) fits radius) build

theorem product_parameters [DecidableEq Input] [DecidableEq Digest]
    (enc : MerkleOracle.Encoding Input Digest (List Goldilocks)) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : 15 ≤ goldilocksModulus) (roundSmall : 22 ≤ goldilocksModulus) (nodes : 8 ≤ 15) (factor : PBSHadamard.Factor d) :
    PaddedStageSourceInterpretation.zeroParameters
      (KeySwitchPaddedProduct.stage (product bundle fits radius raw build) enc family firstSmall roundSmall nodes)
      (fun _ => (descriptor bundle radius).capacity) (fun _ => radius) factor = descriptor bundle radius := rfl
end Product

end
end FormalProof4FHE.HasteBoots.ConstructedGoldKeySwitchRouting
