module
public import FormalProof4FHE.HasteBoots.RecordedRectangularSource
@[expose] public section

/-! Only an original source whose code symbols equal its packing width is
viewed through the existing square source family. This imposes no equality on
any helper's widths and does not change the decoded table or logical addresses. -/
namespace FormalProof4FHE.HasteBoots.RectangularSourceSquareView
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {H : Cfg → ℕ} {packing symbols : ℕ}

def parameters (p : RecordedRectangularSource.Parameters F Cfg H packing symbols) (same : symbols = packing) :
    RecordedPaddedSource.Parameters F Cfg H packing :=
  ⟨p.front,p.suffix,p.degree,p.tag,p.domain,by simpa only [same] using p.capacity,p.radius⟩

theorem logical (p : RecordedRectangularSource.Parameters F Cfg H packing symbols) (same : symbols = packing)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (arity : ℕ)
    (owner : RecordedRectangularSource.Owner (Input := Input) (Digest := Digest) p) :
    RecordedRectangularSource.logical p enc dummy arity owner =
      RecordedPaddedSource.logical (parameters p same) enc dummy arity owner := by
  subst symbols
  rfl

end
end FormalProof4FHE.HasteBoots.RectangularSourceSquareView
