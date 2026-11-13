module
public import FormalProof4FHE.HasteBoots.PaddedSourceGeometry
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedProduct
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedReconstruction
@[expose] public section

/-! Trusted native arithmetic/root constructors preserve the source geometry
installed from public descriptors. These equalities discharge metadata
associations; they assert no equality between different private root values. -/
namespace FormalProof4FHE.HasteBoots.ConstructedKeySwitchSourceParameters
open NativeRootMessage (Digest)
noncomputable section
variable {q b c r k log n d : ℕ} [Fact q.Prime]
  {Cfg Input Response Memory CommitMemory : Type} {H : Cfg → ℕ}

theorem native_ntt
    (raw : PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory H b c r k)
    (g : PaddedSourceGeometry.Geometry (ZMod q) Cfg Bool H b (r+c))
    (build : ((Bool → Digest) × CommitMemory) → AuthenticatedNTT.Packet (ZMod q) Memory c b r k → (side : Bool) →
      NativeBatchVerifier.Protocol (ZMod q) Input Digest Cfg Response Memory b (g.parameters side).front (g.parameters side).suffix k
        (g.parameters side).degree (g.queries side) (H (g.parameters side).tag))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (roots : Bool → Digest)
    (small : 2*b ≤ q) (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (side : Bool) :
    PaddedStageSourceInterpretation.nttParameters
      (PaddedNTT.nativeScheme (PaddedSourceGeometry.ntt raw g build) enc roots q small length psi primitive)
      (fun side => (g.parameters side).capacity) (fun side => (g.parameters side).radius) side = g.parameters side := rfl

theorem native_product
    (raw : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := b) (n := n)
      (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := H))
    (g : PaddedSourceGeometry.Geometry (ZMod q) Cfg (PBSHadamard.Factor d) H b (n+1))
    (build : ((PBSHadamard.Factor d → Digest) × CommitMemory) → PreparedZeroTerminal.Packet (ZMod q) (PBSHadamard.Factor d) Memory b n →
      (factor : PBSHadamard.Factor d) →
      HeterogeneousSingleOpening.Protocol (ZMod q) Input Digest Cfg Response Memory b H
        (fun factor => (g.parameters factor).tag) (PaddedSourceGeometry.code g) factor)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q) (nodes : 2*b ≤ (2*b-1)*2+1)
    (factor : PBSHadamard.Factor d) :
    PaddedStageSourceInterpretation.zeroParameters
      (KeySwitchPaddedProduct.stage (PaddedSourceGeometry.zero raw g build) enc family firstSmall roundSmall nodes)
      (fun factor => (g.parameters factor).capacity) (fun factor => (g.parameters factor).radius) factor = g.parameters factor := rfl

theorem native_reconstruction
    (raw : PaddedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (g : PaddedSourceGeometry.Geometry (ZMod q) Cfg (Fin (2*d+2)) H b n)
    (build : ((Fin (2*d+2) → Digest) × CommitMemory) → PackedLinearOracle.Packet (ZMod q) (Fin (2*d+2)) Memory b n →
      (factor : Fin (2*d+2)) → SingletonOpening.Protocol (ZMod q) Input Digest Cfg Response Memory b
        (g.parameters factor).front (g.parameters factor).suffix (g.parameters factor).degree (g.queries factor) (H (g.parameters factor).tag))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (input : NativeGoldParameterStore.Reference)
    (family : PackedPBSOriginalReferences.Family d) (nodes : 2*b ≤ q) (radix : ZMod q) (factor : Fin (2*d+2)) :
    PaddedStageSourceInterpretation.linearParameters
      (KeySwitchPaddedReconstruction.stage (PaddedSourceGeometry.linear raw g build) enc input family nodes radix)
      (fun factor => (g.parameters factor).capacity) (fun factor => (g.parameters factor).radius) factor = g.parameters factor := rfl

end
end FormalProof4FHE.HasteBoots.ConstructedKeySwitchSourceParameters
