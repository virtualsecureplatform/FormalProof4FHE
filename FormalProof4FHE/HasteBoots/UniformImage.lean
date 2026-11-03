module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-!
# Uniform images of surjective additive maps

A finite uniform coefficient vector maps uniformly onto its linear image,
even when the source rows are linearly dependent. The proof uses a literal
bijection with image times kernel, not an assumed independence of image rows.
-/

open ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.UniformImage

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

noncomputable def fibers (f : A →+ B) (surj : Function.Surjective f) : A ≃ B × f.ker := by
  classical
  let preimage : B → A := fun b => Classical.choose (surj b)
  have hs (b : B) : f (preimage b) = b := Classical.choose_spec (surj b)
  exact {
    toFun := fun a => (f a, ⟨a - preimage (f a), by simp [map_sub, hs]⟩)
    invFun := fun pair => preimage pair.1 + pair.2.val
    left_inv := by intro a; simp
    right_inv := by
      rintro ⟨b, k⟩
      have hk : f k.val = 0 := k.property
      apply Prod.ext
      · simp [map_add, hs, hk]
      · apply Subtype.ext
        simp [map_add, hs, hk] }

theorem fibers_fst (f : A →+ B) (surj : Function.Surjective f) (a : A) :
    (fibers f surj a).1 = f a := rfl

/-- Uniform source coefficients induce the uniform image distribution. -/
theorem uniform_event [SampleableType A] [SampleableType B]
    (f : A →+ B) (surj : Function.Surjective f) [SampleableType f.ker]
    (event : B → Prop) :
    Pr{let a ← $ᵗ A}[event (f a)] = Pr{let b ← $ᵗ B}[event b] := by
  have h := SampleableType.prEvent_uniformSample_equiv (fibers f surj)
    (fun pair => event pair.1)
  simp only [fibers_fst] at h
  exact h.trans (SampleableType.prEvent_uniformSample_fst event)

end FormalProof4FHE.HasteBoots.UniformImage
