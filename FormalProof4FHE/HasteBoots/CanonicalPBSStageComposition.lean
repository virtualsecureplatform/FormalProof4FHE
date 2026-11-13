module
public import FormalProof4FHE.HasteBoots.CanonicalPBS
@[expose] public section

/-! Public PBS evaluation with the verifier's canonical decomposition of the
negative mask and addition of the signed key-product increment. -/
namespace FormalProof4FHE.HasteBoots.CanonicalPBSStageComposition
open NativeBlindRotation (Cipher)
noncomputable section
variable {q n dimension brLevels ksLevels : ℕ} [NeZero n]

omit [NeZero n] in
/-- The single body bias leaves the mask used by canonical key switching intact. -/
theorem bias_mask (accumulator : Cipher q n) : NativePBS.bias accumulator false = accumulator false := rfl

/-- Compose blind-rotation output with the exact signed increment and extraction
relation. No extra body bias or conversion to the old positive-mask product occurs. -/
theorem output_of_stages (brBits ksBits : ℕ) (shape : dimension ≤ n)
    (controls : NativeBlindRotation.Controls q n brLevels)
    (key : NativeKeySwitch.Key q n ksLevels) (initial accumulator increment : Cipher q n)
    (output : NativePublic.Ciphertext q dimension)
    (blind : accumulator = NativeBlindRotation.run brBits controls initial)
    (signedIncrement : increment = CanonicalKeySwitch.increment ksBits key (accumulator false))
    (extraction : CanonicalKeySwitch.Extraction shape (NativePBS.bias accumulator) increment output) :
    output = NativeKeySwitch.extract shape
      (CanonicalKeySwitch.switch ksBits key (NativePBS.bias (NativeBlindRotation.run brBits controls initial))) := by
  have extracted := CanonicalKeySwitch.extract_of_constraints shape (NativePBS.bias accumulator) increment output extraction
  rw [signedIncrement] at extracted
  change output = NativeKeySwitch.extract shape (CanonicalKeySwitch.switch ksBits key (NativePBS.bias accumulator)) at extracted
  rw [blind] at extracted
  exact extracted

/-- The same composition targets the complete caller-visible PBS evaluator. -/
theorem output_eq_evaluate (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : NativePBS.PublicKey q n dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension)
    (accumulator increment : Cipher q n) (output : NativePublic.Ciphertext q dimension)
    (blind : accumulator = NativeBlindRotation.run brBits
      (NativePBS.controls key (NativePublic.frontend (n := n) stride input.1 input.2))
      (NativePBS.initial (NativePublic.frontend (n := n) stride input.1 input.2)))
    (signedIncrement : increment = CanonicalKeySwitch.increment ksBits key.switching (accumulator false))
    (extraction : CanonicalKeySwitch.Extraction shape (NativePBS.bias accumulator) increment output) :
    output = CanonicalPBS.evaluate brBits ksBits stride shape key input :=
  output_of_stages brBits ksBits shape _ key.switching _ accumulator increment output blind signedIncrement extraction

end
end FormalProof4FHE.HasteBoots.CanonicalPBSStageComposition
