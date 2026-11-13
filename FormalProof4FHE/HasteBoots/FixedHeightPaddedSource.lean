module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
@[expose] public section

/-! Fixed-height stage descriptors in one heterogeneous recorded-source family.
Only the source's actual context height is transported. Logical high-zero
padding and the physical decoder/domain/radius remain unchanged. -/
namespace FormalProof4FHE.HasteBoots.FixedHeightPaddedSource
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] {heights : Cfg → ℕ}
  {front suffix degree b n height : ℕ}

/-- Public geometry identifies the source's retained height with its ambient
context; it does not assert any equality of decoded source values. -/
def parameters (tag : Cfg) (geometry : heights tag = height) (domain : Fin (2^height) ↪ F)
    (capacity : 2^suffix ≤ degree*b) (radius : ℕ) : RecordedPaddedSource.Parameters F Cfg heights b :=
  ⟨front,suffix,degree,tag,((finCongr (congrArg (fun h => 2^h) geometry)).toEmbedding.trans domain),capacity,radius⟩

variable [DecidableEq F] [DecidableEq Digest]

/-- The exact fixed-height padded source is a canonical ambient-address view
under the public height association, with its own decoder kept fixed. -/
theorem padded_eq_logical (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Cfg) (geometry : heights tag = height) (domain : Fin (2^height) ↪ F)
    (capacity : 2^suffix ≤ degree*b) (radius : ℕ)
    (padding : ℕ) (dimensions : padding+n = front+suffix)
    (owner : AmbientMatrixSource.Snapshot Input Digest heights tag) :
    QueryHighZeroPadding.source padding (QueryReindex.source dimensions
      (AmbientMatrixSource.source (front := front) enc dummy heights domain capacity radius tag owner)) =
    RecordedPaddedSource.logical (parameters (front := front) tag geometry domain capacity radius) enc dummy n owner := by
  subst height
  exact RecordedPaddedSource.padded_eq_logical
    (parameters (front := front) tag rfl domain capacity radius) enc dummy padding dimensions owner

end
end FormalProof4FHE.HasteBoots.FixedHeightPaddedSource
